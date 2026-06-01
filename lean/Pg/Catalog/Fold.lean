/-
Pg.Catalog.Fold — kernel-checked catalog projection.

Folds a `Pg.Query.Top.TopParseResult` (the C decoder's `--typed`
output) into a `Pg.Catalog.Snapshot`. This is the Lean-side mirror
of what `tools/pgpb_to_snapshot.c` does — same shape, same OID
allocation scheme, same namespace seeding — but kernel-checked.

Trust shift:

  C (pgpb_to_snapshot.c)                     | Lean (this module)
  ─────────────────────────────────────────  | ────────────────────────────
  Allocates OIDs at 16384, monotonic         | Same. State carries `nextOid`.
  Seeds pg_catalog (11), public (2200)       | Same. `Snapshot.seeded`.
  ensure_namespace dedupes by name           | `ensureNamespace`.
  Adds rows via realloc-backed arrays        | Adds via `List.cons`-style.
  Per-stmt switch on node_case               | `foldTopStmt` pattern match.

The byte-equivalent output is the goal; in Phase 0 (this commit)
we cover `CreateSchemaStmt` + `CreateEnumStmt` only. Subsequent
phases add `CompositeTypeStmt`, `CreateStmt`, `CreateDomainStmt`,
`CreateFunctionStmt`, `ViewStmt`, `AlterTableStmt` — each requires
the C decoder to pre-decode that stmt's inner fields and emit
the matching `Top*Stmt` variant.

Why ship Phase 0 anyway: it locks the shape (allocation scheme,
namespace seeding, ensureNamespace dedupe semantics) so subsequent
phases can plug handlers in without architectural churn. The
correctness theorem `fold ≡ C_fold` becomes provable once every
stmt kind the C tool handles is covered here.
-/

import Pg.Catalog.Snapshot
import Pg.Query.Top

namespace Pg.Catalog

open Pg.Query.Top

/-! ### Snapshot state for the fold

The fold needs a mutable counter for the next-OID allocator on top
of the bare `Snapshot` struct. We carry it as a sibling field
inside a small `FoldState` record so the kernel-side proof
discipline matches the C tool's `Snapshot.next_oid`. -/

structure FoldState where
  snap    : Snapshot
  nextOid : Nat := 16384

namespace FoldState

/-- Allocate one OID. Returns the new OID and the bumped state. -/
def alloc (s : FoldState) : Nat × FoldState :=
  (s.nextOid, { s with nextOid := s.nextOid + 1 })

/-- Allocate two OIDs (used by composite types: one type_oid + one rel_oid). -/
def alloc2 (s : FoldState) : Nat × Nat × FoldState :=
  let (o1, s')  := s.alloc
  let (o2, s'') := s'.alloc
  (o1, o2, s'')

/-- Snapshot seeded with `pg_catalog` (oid 11) and `public` (oid 2200)
    namespaces — matches what `pgpb_to_snapshot.c`'s `snap_init` does. -/
def empty : FoldState where
  snap := {
    namespaces := [
      { oid := ⟨11⟩,   nspname := "pg_catalog" },
      { oid := ⟨2200⟩, nspname := "public" }
    ]
  }
  nextOid := 16384

end FoldState

/-! ### Namespace handling -/

/-- Look up an existing namespace by name; if absent, allocate one. -/
def ensureNamespace (name : String) (s : FoldState) : Oid .namespace × FoldState :=
  match s.snap.namespaces.find? (fun n => n.nspname == name) with
  | some ns => (ns.oid, s)
  | none =>
    let (oid, s') := s.alloc
    let row : PgNamespace := { oid := ⟨oid⟩, nspname := name }
    (row.oid, { s' with snap := { s'.snap with namespaces := s'.snap.namespaces ++ [row] } })

/-! ### Type resolution

  When the C decoder emits a `TypeRef`, the `oidHint` carries the
  pre-resolved OID for `pg_catalog` builtins (`text=25`, `int8=20`,
  `bigint=20` alias, …) drawn from the same BUILTIN_TYPES table
  pgpb_to_snapshot.c uses. User-defined types arrive with
  `oidHint = 0`; we walk `snap.types` to find them.

  Returns the OID raw value; the catchall is `2249` (record), the
  same "unknown type" sentinel pgpb_to_snapshot.c uses. -/
def resolveType (ref : TypeRef) (s : FoldState) : Nat :=
  if ref.oidHint ≠ 0 then ref.oidHint
  else
    let target := ref.schema.getD "public"
    -- Look up the namespace OID for the target schema.
    match s.snap.namespaces.find? (fun n => n.nspname == target) with
    | some ns =>
      match s.snap.types.find? (fun t =>
              t.typnamespace == ns.oid && t.typname == ref.name) with
      | some t => t.oid.raw
      | none   => 2249
    | none => 2249

/-! ### Per-stmt handlers -/

/-- `CREATE SCHEMA <name>` — registers a namespace row. -/
def foldCreateSchema (st : TopCreateSchemaStmt) (s : FoldState) : FoldState :=
  let (_, s') := ensureNamespace st.schemaname s
  s'

/-- `CREATE TYPE <qualName> AS ENUM (<labels>)` — registers an enum
    type row. Schema defaults to "public" when unqualified. -/
def foldCreateEnum (st : TopCreateEnumStmt) (s : FoldState) : FoldState :=
  let schema := st.qualName.schema.getD "public"
  let (nsOid, s') := ensureNamespace schema s
  let (typOid, s'') := s'.alloc
  let row : PgType := {
    oid          := ⟨typOid⟩
    typname      := st.qualName.name
    typnamespace := nsOid
    typtype      := .enum
  }
  { s'' with snap := { s''.snap with types := s''.snap.types ++ [row] } }

/-- `CREATE DOMAIN <qualName> AS <baseType>` — registers a domain
    type row carrying its base type OID. -/
def foldCreateDomain (st : TopCreateDomainStmt) (s : FoldState) : FoldState :=
  let schema := st.qualName.schema.getD "public"
  let (nsOid, s') := ensureNamespace schema s
  let baseOid := resolveType st.baseType s'
  let (typOid, s'') := s'.alloc
  let row : PgType := {
    oid          := ⟨typOid⟩
    typname      := st.qualName.name
    typnamespace := nsOid
    typtype      := .domain
    typbasetype  := ⟨baseOid⟩
  }
  { s'' with snap := { s''.snap with types := s''.snap.types ++ [row] } }

/-! ### Composite & table — both register a composite type + relation
    + per-column attribute rows. Only the relkind differs. -/

/-- Push a relation row and its per-column attribute rows. Returns
    the updated FoldState. -/
def addRelationWithColumns
    (qualName : QualifiedName) (relkind : RelKind)
    (columns : List ColumnDefSpec) (s : FoldState) : FoldState :=
  let schema := qualName.schema.getD "public"
  let (nsOid, s') := ensureNamespace schema s
  let (typOid, relOid, s'') := s'.alloc2
  let typeRow : PgType := {
    oid          := ⟨typOid⟩
    typname      := qualName.name
    typnamespace := nsOid
    typtype      := .composite
    typrelid     := ⟨relOid⟩
  }
  let relRow : PgClass := {
    oid          := ⟨relOid⟩
    relname      := qualName.name
    relnamespace := nsOid
    relkind      := relkind
    reltype      := ⟨typOid⟩
  }
  -- Add attributes after the relation is staged so resolveType sees
  -- any earlier-allocated types in the same fold.
  let s0 : FoldState := { s'' with snap :=
    { s''.snap with
        types     := s''.snap.types ++ [typeRow]
        relations := s''.snap.relations ++ [relRow] } }
  let (_, finalState) :=
    columns.foldl
      (fun (acc : Nat × FoldState) col =>
        let (attnum, st) := acc
        let attnum := attnum + 1
        let oid := resolveType col.typeRef st
        let attr : PgAttribute := {
          attrelid  := ⟨relOid⟩
          attname   := col.name
          atttypid  := ⟨oid⟩
          attnum    := attnum
          attnotnull := col.notNull
        }
        (attnum,
         { st with snap :=
             { st.snap with attributes := st.snap.attributes ++ [attr] } }))
      (0, s0)
  finalState

/-- `CREATE TYPE <qualName> AS (<columns>)` — composite type with
    a relkind=compositeType companion row. -/
def foldCompositeType (st : TopCompositeTypeStmt) (s : FoldState) : FoldState :=
  addRelationWithColumns st.qualName .compositeType st.columns s

/-- `CREATE TABLE <qualName> (<columns>)` — ordinary-table relkind. -/
def foldCreateTable (st : TopCreateStmt) (s : FoldState) : FoldState :=
  addRelationWithColumns st.qualName .ordinaryTable st.columns s

/-- `CREATE FUNCTION <qualName>(<params>) RETURNS [SETOF] <returnType>` —
    registers a `PgProc` row. Mirrors what
    `pgpb_to_snapshot.c::handle_create_function` does:

      * Resolve each parameter's typeRef → OID.
      * Resolve the return type → OID (falls back to 2278 = void).
      * Collect names / modes / types separately (preserving order).
      * `proargmodes` is emitted only if any mode is non-default,
        matching the C tool's `has_modes` branch and savvi-studio's
        on-disk PgProc representation (empty list means "all IN"). -/
def foldCreateFunction (st : TopCreateFunctionStmt) (s : FoldState) : FoldState :=
  let schema := st.qualName.schema.getD "public"
  let (nsOid, s0) := ensureNamespace schema s

  -- Resolve every parameter's type against the in-progress snapshot.
  let argTypes  : List Nat       := st.parameters.map (fun p => resolveType p.typeRef s0)
  let argNames  : List String    := st.parameters.map (·.name)
  let argModes  : List ArgMode   := st.parameters.map (·.mode)
  let hasModes  : Bool := argModes.any (fun m => decide (m ≠ .in_))

  -- Return type — fall back to void (2278) when unresolved.
  let retOidRaw : Nat := resolveType st.returnType s0
  let retOid    : Oid .type := ⟨if retOidRaw == 0 then 2278 else retOidRaw⟩

  let (procOid, s1) := s0.alloc
  let row : PgProc := {
    oid          := ⟨procOid⟩
    proname      := st.qualName.name
    pronamespace := nsOid
    prokind      := .function
    prosecdef    := false
    provolatile  := .stable
    prorettype   := retOid
    proargtypes  := argTypes.map (fun n => ⟨n⟩)
    proargnames  := argNames
    proretset    := st.returnSetof
    proargmodes  := if hasModes then argModes else []
  }
  { s1 with snap := { s1.snap with procs := s1.snap.procs ++ [row] } }

/-! ### Top-level dispatch -/

/-! ### AlterTable

  Mutates the in-progress snapshot. Looks up the target relation by
  (schema, name) — same as `pgpb_to_snapshot.c::find_relation_by_name` —
  then dispatches each cmd. Drops and not-null flips happen by
  rewriting `snap.attributes`; add-column appends a new attribute
  row with the next attnum.

  Unsupported AlterTableCmd subtypes (ADD CONSTRAINT, RENAME, OWNER,
  …) arrive as `.skip` from the C decoder; the fold treats them as
  no-ops. -/
def findRelByQual (qn : QualifiedName) (snap : Snapshot)
    : Option (Oid .relation) := do
  let target := qn.schema.getD "public"
  let ns ← snap.namespaces.find? (fun n => n.nspname == target)
  let r  ← snap.relations.find? (fun r => r.relnamespace == ns.oid && r.relname == qn.name)
  pure r.oid

def maxAttnumFor (relOid : Oid .relation) (attrs : List PgAttribute) : Int :=
  attrs.foldl
    (fun acc a => if a.attrelid == relOid && a.attnum > acc then a.attnum else acc)
    (0 : Int)

def applyAlterCmd (relOid : Oid .relation) (cmd : AlterTableCmd) (s : FoldState)
    : FoldState :=
  match cmd with
  | .addColumn col =>
    let typid : Nat := resolveType col.typeRef s
    let attr : PgAttribute := {
      attrelid  := relOid
      attname   := col.name
      atttypid  := ⟨typid⟩
      attnum    := maxAttnumFor relOid s.snap.attributes + 1
      attnotnull := col.notNull
    }
    { s with snap := { s.snap with attributes := s.snap.attributes ++ [attr] } }
  | .dropColumn name =>
    let attrs' := s.snap.attributes.filter
      (fun a => !(a.attrelid == relOid && a.attname == name))
    { s with snap := { s.snap with attributes := attrs' } }
  | .setNotNull name =>
    let attrs' := s.snap.attributes.map
      (fun a => if a.attrelid == relOid && a.attname == name
                then { a with attnotnull := true } else a)
    { s with snap := { s.snap with attributes := attrs' } }
  | .dropNotNull name =>
    let attrs' := s.snap.attributes.map
      (fun a => if a.attrelid == relOid && a.attname == name
                then { a with attnotnull := false } else a)
    { s with snap := { s.snap with attributes := attrs' } }
  | .skip => s

def foldAlterTable (st : TopAlterTableStmt) (s : FoldState) : FoldState :=
  match findRelByQual st.qualName s.snap with
  | none => s   -- target table not in snapshot — silently skip (mirrors C tool)
  | some relOid =>
    st.cmds.foldl (fun acc cmd => applyAlterCmd relOid cmd acc) s

/-! ### Top-level dispatch -/

def foldTopStmt : TopStmt → FoldState → FoldState
  | .createSchemaStmt   st, s => foldCreateSchema   st s
  | .createEnumStmt     st, s => foldCreateEnum     st s
  | .createDomainStmt   st, s => foldCreateDomain   st s
  | .compositeTypeStmt  st, s => foldCompositeType  st s
  | .createStmt         st, s => foldCreateTable    st s
  | .createFunctionStmt st, s => foldCreateFunction st s
  | .alterTableStmt     st, s => foldAlterTable     st s
  | .other _,               s => s  -- catchall — fold leaves snapshot unchanged

/-- Fold an entire `TopParseResult` over the seeded empty state.
    The resulting `Snapshot` is the kernel-checked catalog. -/
def Snapshot.ofTopParseResult (pr : TopParseResult) : Snapshot :=
  (pr.stmts.foldl (fun s rs => foldTopStmt rs.stmt s) FoldState.empty).snap

end Pg.Catalog
