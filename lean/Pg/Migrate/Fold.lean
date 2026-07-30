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
  snap       : Snapshot
  nextOid    : Nat := 16384
  /-- Enum labels by type OID — populated by `foldCreateEnum`. The
      C tool emits these as a sibling `def enumLabels` alongside
      `def snapshot` (downstream `catalogFromSnapshotWithEnums`
      consumes both); the Lean fold tracks them here for the same
      drop-in shape. -/
  enumLabels : List (Oid .type × List String) := []

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

  `resolveTypeOpt` returns `none` on miss (C's `type_name_to_oid`
  returning -1). Handlers apply per-context fallbacks:
    * domain base type           → 0  (Oid.invalid)
    * composite/table column     → skip the attribute
    * function argtype           → 2249 (record)
    * function rettype           → 2278 (void)

  `resolveType` is a sugar wrapper that picks `2249` (record) on
  miss — used by paths where the per-stmt fallback is also 2249
  (view-target ColumnRef misses). -/
def resolveTypeOpt (ref : TypeRef) (s : FoldState) : Option Nat :=
  if ref.oidHint ≠ 0 then some ref.oidHint
  else
    let target := ref.schema.getD "public"
    match s.snap.namespaces.find? (fun n => n.nspname == target) with
    | some ns =>
      (s.snap.types.find? (fun t =>
              t.typnamespace == ns.oid && t.typname == ref.name))
        |>.map (·.oid.raw)
    | none => none

def resolveType (ref : TypeRef) (s : FoldState) : Nat :=
  (resolveTypeOpt ref s).getD 2249

/-! ### Per-stmt handlers -/

/-- `CREATE SCHEMA <name>` — registers a namespace row. -/
def foldCreateSchema (st : TopCreateSchemaStmt) (s : FoldState) : FoldState :=
  let (_, s') := ensureNamespace st.schemaname s
  s'

/-- `CREATE TYPE <qualName> AS ENUM (<labels>)` — registers an enum
    type row and tracks its labels for the sibling `enumLabels`
    emit. Schema defaults to "public" when unqualified. -/
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
  { s'' with
    snap       := { s''.snap with types := s''.snap.types ++ [row] }
    enumLabels := s''.enumLabels ++ [(⟨typOid⟩, st.labels)] }

/-- `CREATE DOMAIN <qualName> AS <baseType>` — registers a domain
    type row carrying its base type OID. Unresolved base types
    use OID 0 (Oid.invalid), matching the C tool's `base_oid >= 0
    ? base_oid : 0` fallback. -/
def foldCreateDomain (st : TopCreateDomainStmt) (s : FoldState) : FoldState :=
  let schema := st.qualName.schema.getD "public"
  let (nsOid, s') := ensureNamespace schema s
  let baseOid := (resolveTypeOpt st.baseType s').getD 0
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
    the updated FoldState.

    `forceNotNull` overrides each column's per-column `notNull` flag
    and emits `attnotnull = true`. Composite types use this since
    postgres treats composite columns as struct fields with implicit
    NOT NULL; CREATE TABLE leaves each column's flag intact so
    constraint-driven NOT NULL / PRIMARY KEY logic in the C decoder
    flows through.

    `useSourceIndex` controls how skipped (unresolved-type) columns
    affect attnum:
      * `false` (CREATE TABLE) — attnum is a counter that only
        increments for emitted attributes. Skipped columns leave
        no gap. Matches `handle_create_table`'s `attnum++` AFTER
        the type-resolve check.
      * `true` (CREATE TYPE composite) — attnum is `i + 1` where
        `i` is the source position. Skipped columns leave a gap.
        Matches `handle_composite_type`'s `"attnum": i + 1`. -/
def addRelationWithColumns
    (qualName : QualifiedName) (relkind : RelKind)
    (columns : List ColumnDefSpec) (forceNotNull : Bool)
    (useSourceIndex : Bool)
    (s : FoldState) : FoldState :=
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
  -- Skip columns whose type doesn't resolve, matching the C tool's
  -- `if (typoid < 0) continue`. attnum source depends on
  -- `useSourceIndex` (see fn docstring above).
  let indexed : List (Nat × ColumnDefSpec) :=
    columns.foldl (fun acc col => acc ++ [(acc.length, col)]) []
  let (_, finalState) :=
    indexed.foldl
      (fun (acc : Nat × FoldState) (entry : Nat × ColumnDefSpec) =>
        let (counter, st) := acc
        let (i, col) := entry
        match resolveTypeOpt col.typeRef st with
        | none => (counter, st)
        | some oid =>
          let counter := counter + 1
          let attnum : Int := if useSourceIndex then i + 1 else counter
          let attr : PgAttribute := {
            attrelid  := ⟨relOid⟩
            attname   := col.name
            atttypid  := ⟨oid⟩
            attnum    := attnum
            attnotnull := forceNotNull || col.notNull
          }
          (counter,
           { st with snap :=
               { st.snap with attributes := st.snap.attributes ++ [attr] } }))
      (0, s0)
  finalState

/-- `CREATE TYPE <qualName> AS (<columns>)` — composite type with a
    relkind=compositeType companion row. Composite columns are
    implicitly NOT NULL (`forceNotNull := true`); attnum is source
    index (skipped columns leave gaps), matching what
    pgpb_to_snapshot.c does. -/
def foldCompositeType (st : TopCompositeTypeStmt) (s : FoldState) : FoldState :=
  addRelationWithColumns st.qualName .compositeType st.columns
    (forceNotNull := true) (useSourceIndex := true) s

/-- `CREATE TABLE <qualName> (<columns>)` — ordinary-table relkind.
    Column-level NOT NULL flags flow through unchanged (the C
    decoder set them from `CONSTR_NOTNULL` / `CONSTR_PRIMARY`).
    attnum is sequential — skipped columns don't leave gaps. -/
def foldCreateTable (st : TopCreateStmt) (s : FoldState) : FoldState :=
  addRelationWithColumns st.qualName .ordinaryTable st.columns
    (forceNotNull := false) (useSourceIndex := false) s

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
  -- Args fall back to 2249 (record) on miss; matches the C tool's
  -- `t >= 0 ? t : 2249` in handle_create_function.
  let argTypes  : List Nat       :=
    st.parameters.map (fun p => (resolveTypeOpt p.typeRef s0).getD 2249)
  let argNames  : List String    := st.parameters.map (·.name)
  let argModes  : List ArgMode   := st.parameters.map (·.mode)
  let hasModes  : Bool := argModes.any (fun m => decide (m ≠ .in_))

  -- Return type — fall back to void (2278) when unresolved, matching
  -- the C tool's `rettype >= 0 ? rettype : 2278`.
  let retOid : Oid .type := ⟨(resolveTypeOpt st.returnType s0).getD 2278⟩

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

/-! ### View

  CREATE VIEW lands a view-kind relation plus per-column attribute
  rows. Column types are inferred from each ResTarget — same logic
  pgpb_to_snapshot.c runs in `handle_view_stmt`:

    * Look up each ColumnRef's table alias in the SELECT's
      FROM-clause map, find the underlying relation, find the
      column's atttypid.
    * Bare column refs (no alias) search all FROM relations
      (first match wins).
    * Anything that isn't a ColumnRef → OID 2249 (record).

  Phase 4 ships the same encoding the C tool does; Phase 6's
  byte-equivalence diff covers the agreement. -/

/-- For a known table alias, find the (schema, relname) it resolves
    to in the SELECT's FROM map. -/
def fromMapLookup (fromList : List FromEntry) (alias : String)
    : Option FromEntry :=
  fromList.find? (fun fe => fe.alias == alias)

/-- Resolve a `tbl.col` (qualified) view-target column → its
    underlying attribute's atttypid.

    Returns `none` if the table alias doesn't appear in the FROM
    map, or if the named column doesn't exist on that relation.
    The fold uses `none` → OID 2249 (z.unknown) downstream. -/
def resolveQualifiedColumn (fromList : List FromEntry)
    (snap : Snapshot)
    (table : String) (col : String) : Option Nat := do
  let fe ← fromMapLookup fromList table
  let ns ← snap.namespaces.find? (fun n => n.nspname == fe.schema)
  let r  ← snap.relations.find? (fun r =>
            r.relnamespace == ns.oid && r.relname == fe.name)
  let a  ← snap.attributes.find? (fun a =>
            a.attrelid == r.oid && a.attname == col)
  pure a.atttypid.raw

/-- Resolve a bare `col` view-target column. Walks ALL snapshot
    relations in registration order and returns the first
    attribute that matches by name — same algorithm as
    `pgpb_to_snapshot.c::resolve_column_oid` for the unqualified
    case.

    Note: the FROM map is intentionally NOT consulted here. The
    C tool ignores it for bare refs, so we match. This means a
    column reference like `schema_name` resolves against any
    relation with that attribute (the first one allocated),
    even if the SELECT's FROM clause names something else — a
    quirk of the C tool's resolver that we replicate for
    byte-equivalence. -/
def resolveBareColumn (_fromList : List FromEntry)
    (snap : Snapshot)
    (col : String) : Option Nat :=
  (snap.attributes.find? (fun a => a.attname == col)).map (·.atttypid.raw)

/-- Resolve a single view-target expression → its OID.

    Phase 4 only types ColumnRefs; anything else (function calls,
    CASE, casts, arithmetic) collapses to 2249. That gives the
    downstream codegen `z.unknown()` for that column — same
    behavior as `pgpb_to_snapshot.c` post-0.5.5. -/
def resolveViewTarget (fromList : List FromEntry) (snap : Snapshot)
    : ViewTargetExpr → Nat
  | .columnRef (some t) col =>
      (resolveQualifiedColumn fromList snap t col).getD 2249
  | .columnRef none col =>
      (resolveBareColumn fromList snap col).getD 2249
  | .unknownExpr => 2249

/-- `CREATE VIEW <qualName> AS SELECT ... FROM ...` — emits a
    composite type + view-kind relation + one attribute per
    target column with its inferred OID. -/
def foldViewStmt (st : TopViewStmt) (s : FoldState) : FoldState :=
  let schema := st.qualName.schema.getD "public"
  let (nsOid, s0) := ensureNamespace schema s
  let (typOid, relOid, s1) := s0.alloc2
  let typeRow : PgType := {
    oid          := ⟨typOid⟩
    typname      := st.qualName.name
    typnamespace := nsOid
    typtype      := .composite
    typrelid     := ⟨relOid⟩
  }
  let relRow : PgClass := {
    oid          := ⟨relOid⟩
    relname      := st.qualName.name
    relnamespace := nsOid
    relkind      := .view
    reltype      := ⟨typOid⟩
  }
  let s2 : FoldState := { s1 with snap :=
    { s1.snap with
        types     := s1.snap.types ++ [typeRow]
        relations := s1.snap.relations ++ [relRow] } }
  -- Resolve and append one attribute per target. The FROM map and
  -- snapshot are read-only during the per-target walk.
  let (_, finalState) :=
    st.targets.foldl
      (fun (acc : Int × FoldState) tgt =>
        let (attnum, st') := acc
        let attnum := attnum + 1
        let oid := resolveViewTarget st.fromList st'.snap tgt.expr
        let attr : PgAttribute := {
          attrelid  := ⟨relOid⟩
          attname   := tgt.outputName
          atttypid  := ⟨oid⟩
          attnum    := attnum
          attnotnull := false   -- views project nullable-by-default
        }
        (attnum,
         { st' with snap :=
             { st'.snap with attributes := st'.snap.attributes ++ [attr] } }))
      ((0 : Int), s2)
  finalState

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
    -- Same skip-on-miss as composite/table column emit.
    match resolveTypeOpt col.typeRef s with
    | none => s
    | some typid =>
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
  | .viewStmt           st, s => foldViewStmt       st s
  | .alterTableStmt     st, s => foldAlterTable     st s
  | .other _,               s => s  -- catchall — fold leaves snapshot unchanged

/-- Fold an entire `TopParseResult` over the seeded empty state.
    The resulting `Snapshot` is the kernel-checked catalog without
    referenced-builtin augmentation — i.e. `snap.types` carries only
    the user-allocated rows the fold itself added.

    For byte-equivalence with `pgpb_to_snapshot.c` (which prepends
    referenced `pg_catalog` builtin rows to its emit), compose with
    `Snapshot.augmentBuiltins` (or call `ofTopParseResultAugmented`
    below). -/
def Snapshot.ofTopParseResult (pr : TopParseResult) : Snapshot :=
  (pr.stmts.foldl (fun s rs => foldTopStmt rs.stmt s) FoldState.empty).snap

/-! ### Builtins augmentation

  Phase 7 mirrors `pgpb_to_snapshot.c::emit_referenced_builtins`:
  scan the snapshot for OIDs referenced from user rows, filter to
  the BUILTIN_TYPES table, dedup + sort, prepend `PgType` rows to
  `snap.types`. After this pass, the Lean fold's emitted `Snapshot`
  byte-matches the C tool's for every catalog table. -/

/-- Mirror of `pgpb_to_snapshot.c::BUILTIN_TYPES`. The ORDER inside
    matters: lookup-by-OID returns the FIRST match (so `oid := 20`
    resolves to `"int8"`, not `"bigint"`), exactly mirroring
    `builtin_name_for_oid`. -/
def builtinTable : List (String × Nat × Bool) :=
  -- (typname, OID, isPseudo)
  [ ("bool", 16, false), ("bytea", 17, false), ("char", 18, false), ("name", 19, false),
    ("int8", 20, false), ("bigint", 20, false),
    ("int2", 21, false), ("smallint", 21, false),
    ("int4", 23, false), ("integer", 23, false), ("int", 23, false),
    ("text", 25, false), ("oid", 26, false),
    ("float4", 700, false), ("real", 700, false),
    ("float8", 701, false), ("double", 701, false), ("double_precision", 701, false),
    ("numeric", 1700, false), ("decimal", 1700, false),
    ("varchar", 1043, false), ("bpchar", 1042, false),
    ("uuid", 2950, false),
    ("date", 1082, false),
    ("time", 1083, false), ("timetz", 1266, false),
    ("timestamp", 1114, false), ("timestamptz", 1184, false),
    ("interval", 1186, false),
    ("json", 114, false), ("jsonb", 3802, false),
    ("void", 2278, true),  ("record", 2249, true),
    ("_int8", 1016, false), ("_int4", 1007, false),
    ("_text", 1009, false), ("_bool", 1000, false),
    ("regclass", 2205, false), ("regproc", 24, false),
    ("regprocedure", 2202, false),
    ("regoper", 2203, false), ("regoperator", 2204, false),
    ("regtype", 2206, false),
    ("regrole", 4096, false), ("regnamespace", 4089, false)
  ]

def builtinNameOf (oid : Nat) : Option String :=
  builtinTable.findSome? (fun (n, o, _) => if o == oid then some n else none)

def builtinIsPseudo (oid : Nat) : Bool :=
  builtinTable.any (fun (_, o, p) => o == oid && p)

/-- Insert `x` into a sorted-ascending list, preserving order. -/
def insertSorted (x : Nat) : List Nat → List Nat
  | []         => [x]
  | h :: t     => if x ≤ h then x :: h :: t else h :: insertSorted x t

/-- Sort + dedupe a list of Nat ascending. Used for the
    referenced-builtin OID set; sizes are small (≤64), so the
    O(n²) insertion-sort cost is irrelevant. -/
def sortDedupAsc (l : List Nat) : List Nat :=
  l.foldr (fun x acc => if acc.contains x then acc else insertSorted x acc) []

/-- All OIDs referenced by the snapshot's user rows that exist in
    the `BUILTIN_TYPES` table. Mirrors the C tool's collection
    walk: types' typbasetype + live attributes' atttypid + procs'
    prorettype + procs' proargtypes. -/
def Snapshot.referencedBuiltinOids (s : Snapshot) : List Nat :=
  let typeOids   := s.types.map (·.typbasetype.raw)
  let attrOids   := (s.attributes.filter (fun a => a.attrelid.raw ≠ 0))
                      |>.map (·.atttypid.raw)
  let procRetOids := s.procs.map (·.prorettype.raw)
  let procArgOids := s.procs.foldl
                      (fun acc p => acc ++ p.proargtypes.map (·.raw)) []
  let all := typeOids ++ attrOids ++ procRetOids ++ procArgOids
  let builtins := all.filter (fun o => (builtinNameOf o).isSome)
  sortDedupAsc builtins

/-- Prepend `PgType` rows for every referenced builtin to
    `snap.types`. The new rows carry `typnamespace = ⟨11⟩`
    (pg_catalog) and `typtype = .pseudo` for `void`/`record`, else
    `.base` — matching the C tool's emit semantics exactly. -/
def Snapshot.augmentBuiltins (s : Snapshot) : Snapshot :=
  let oids := s.referencedBuiltinOids
  let rows : List PgType := oids.filterMap (fun oid =>
    (builtinNameOf oid).map (fun name => {
      oid          := ⟨oid⟩
      typname      := name
      typnamespace := ⟨11⟩
      typtype      := if builtinIsPseudo oid then .pseudo else .base
    }))
  { s with types := rows ++ s.types }

/-- Fold + augment in one step. This is the byte-equivalent
    counterpart of `pgpb_to_snapshot.c`'s output. -/
def Snapshot.ofTopParseResultAugmented (pr : TopParseResult) : Snapshot :=
  (Snapshot.ofTopParseResult pr).augmentBuiltins

/-- Fold + augment + return both the Snapshot and the enum-labels
    sibling table. Used by the lean_emit pipeline that replaces
    `pgpb_to_snapshot.c` — downstream consumers
    (`catalogFromSnapshotWithEnums`) need both. -/
def Snapshot.ofTopParseResultAugmentedWithEnums (pr : TopParseResult)
    : Snapshot × List (Oid .type × List String) :=
  let final := pr.stmts.foldl
    (fun s rs => foldTopStmt rs.stmt s) FoldState.empty
  (final.snap.augmentBuiltins, final.enumLabels)

end Pg.Catalog
