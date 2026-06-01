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

/-! ### Top-level dispatch -/

def foldTopStmt : TopStmt → FoldState → FoldState
  | .createSchemaStmt st, s => foldCreateSchema st s
  | .createEnumStmt   st, s => foldCreateEnum   st s
  | .other _,             s => s  -- catchall — fold leaves snapshot unchanged

/-- Fold an entire `TopParseResult` over the seeded empty state.
    The resulting `Snapshot` is the kernel-checked catalog. -/
def Snapshot.ofTopParseResult (pr : TopParseResult) : Snapshot :=
  (pr.stmts.foldl (fun s rs => foldTopStmt rs.stmt s) FoldState.empty).snap

end Pg.Catalog
