/-
Pg.Catalog.FoldPipelineTest — end-to-end test of the proof-tier
ladder leg: .sql → .pgpb → typed .lean → Lean fold → Snapshot.

The pipeline:

  tools/pgpb_to_lean_ast/smoke_fixture.sql
      ↓ //tools:sql_to_protobuf
  smoke_fixture.pgpb
      ↓ //tools/pgpb_to_lean_ast:pgpb_to_lean_ast --typed
  SmokeFixtureTyped.lean   (Pg.Query.SmokeFixtureTyped.parseResult)
      ↓ Pg.Catalog.Snapshot.ofTopParseResult
  snapshot value
      ↓ native_decide assertions below

The smoke fixture has 8 stmts:
  CREATE SCHEMA test_smoke;
  CREATE DOMAIN test_smoke.identifier AS TEXT CHECK ...;
  CREATE TYPE test_smoke.point AS (x INTEGER, y INTEGER);
  CREATE TABLE test_smoke.locations (...);
  CREATE FUNCTION test_smoke.distance(p_a point, p_b point) RETURNS double precision;
  ALTER TABLE test_smoke.locations ADD COLUMN created_at TIMESTAMPTZ NOT NULL;
  ALTER TABLE test_smoke.locations ALTER COLUMN name DROP NOT NULL;
  CREATE VIEW test_smoke.location_summary AS SELECT l.id, name, EXTRACT(...) AS epoch FROM test_smoke.locations l;

Phase 0 fold handles `CreateSchemaStmt` and `CreateEnumStmt` only;
`CreateDomainStmt`, `CompositeTypeStmt`, `CreateStmt` collapse to
`.other` and leave the snapshot unchanged. So the expected fold
output is:

  namespaces : [pg_catalog, public, test_smoke]   (3)
  types      : []
  relations  : []
  ...

As more stmt kinds get pre-decoded in the C tool + handled in
the fold, these assertions tighten.
-/

import Pg.Catalog.Fold
import SmokeFixtureTyped

namespace Pg.Catalog.FoldPipelineTest

open Pg.Catalog SmokeFixtureTyped

def folded : Snapshot := Snapshot.ofTopParseResult parseResult

/-- The decoder saw 8 stmts; Phases 0-5 cover all of them. -/
example : (parseResult.stmts.length) = 8 := by native_decide

/-- pg_catalog + public + test_smoke. -/
example : folded.namespaces.length = 3 := by native_decide

/-- The new namespace from CREATE SCHEMA is materialized. -/
example : (folded.namespaces.find? (fun n => n.nspname == "test_smoke")).isSome := by
  native_decide

/-- Phase 0-5 cover everything in the fixture. The snapshot gains:
      * 4 types     — identifier (domain), point (composite),
                      locations (table's implicit composite),
                      location_summary (view's implicit composite)
      * 3 relations — point (compositeType), locations (table),
                      location_summary (view)
      * 9 attributes — 2 from point + 4 from locations (after
                      ADD COLUMN created_at) + 3 from the view.
      * 1 proc — distance. -/
example : folded.types.length = 4 := by native_decide

/-- 3 relations: point composite + locations table + location_summary view. -/
example : folded.relations.length = 3 := by native_decide

/-- 9 attributes:
      point.x, point.y                                                (2)
      locations.id, .name, .position, .created_at                     (4)
      location_summary.id, .name, .epoch                              (3) -/
example : folded.attributes.length = 9 := by native_decide

/-- `identifier` is a domain over `text` (OID 25, builtin). The
    decoder filled the OID hint; the fold used it directly. -/
example :
    (folded.types.find? (fun t => t.typname == "identifier")).map (·.typbasetype.raw)
      = some 25 := by
  native_decide

/-- `locations.id` is `BIGINT PRIMARY KEY` — typed as int8 (20) +
    NOT NULL inferred from the PRIMARY KEY constraint. -/
example :
    (folded.attributes.find? (fun a => a.attname == "id")).map (·.atttypid.raw)
      = some 20 := by
  native_decide

example :
    (folded.attributes.find? (fun a => a.attname == "id")).map (·.attnotnull)
      = some true := by
  native_decide

/-- `locations.position` references the user-defined `test_smoke.point`
    composite type. The OID hint was 0 (not a builtin); the Lean
    fold's `resolveType` walked `snap.types` and found it. -/
example :
    let pointOid := (folded.types.find? (fun t => t.typname == "point")).map (·.oid.raw)
    let posOid   := (folded.attributes.find? (fun a => a.attname == "position")).map (·.atttypid.raw)
    pointOid = posOid ∧ pointOid.isSome := by
  native_decide

/-- Phase 3: the function row is registered. -/
example : folded.procs.length = 1 := by native_decide

/-- `distance` returns `DOUBLE PRECISION` (OID 701). The builtin hint
    was filled by the C decoder. -/
example :
    (folded.procs.find? (fun p => p.proname == "distance")).map (·.prorettype.raw)
      = some 701 := by
  native_decide

/-- Both parameters are typed as `test_smoke.point` (user type),
    which the Lean fold resolved via `resolveType` against the
    snapshot row added two stmts earlier. -/
example :
    let pointOid := (folded.types.find? (fun t => t.typname == "point")).map (·.oid.raw)
    let argTypes := (folded.procs.find? (fun p => p.proname == "distance")).map
                      (fun p => p.proargtypes.map (·.raw))
    argTypes = pointOid.map (fun o => [o, o]) := by
  native_decide

/-- The two argument names round-trip. -/
example :
    (folded.procs.find? (fun p => p.proname == "distance")).map (·.proargnames)
      = some ["p_a", "p_b"] := by
  native_decide

/-! ### Phase 5 — AlterTable effects -/

/-- ALTER TABLE ... ADD COLUMN created_at TIMESTAMPTZ NOT NULL — adds
    one more attribute row to `locations`. The new column carries
    `timestamptz` (OID 1184, builtin) + NOT NULL. -/
example :
    (folded.attributes.find? (fun a => a.attname == "created_at")).map (·.atttypid.raw)
      = some 1184 := by
  native_decide

example :
    (folded.attributes.find? (fun a => a.attname == "created_at")).map (·.attnotnull)
      = some true := by
  native_decide

/-- ALTER TABLE ... ALTER COLUMN name DROP NOT NULL — flips the
    `name` column's `attnotnull` from true (from CREATE TABLE) to false. -/
example :
    (folded.attributes.find? (fun a => a.attname == "name")).map (·.attnotnull)
      = some false := by
  native_decide

/-! ### Phase 4 — ViewStmt type inference

The view projects three columns of distinct expression kinds:

  * `l.id`              — qualified `tbl.col`; resolved via FROM alias `l`
                          → locations.id → bigint (20).
  * `name`              — bare column; first-match across FROM relations
                          → locations.name → identifier (a user domain).
                          The fold's `resolveBareColumn` walked the snapshot.
  * `EXTRACT(...) AS epoch` — non-ColumnRef expression; the C decoder
                          emitted `.unknownExpr`; the fold uses 2249. -/

/-- The view's relation row is registered with `relkind = .view`. -/
example :
    (folded.relations.find? (fun r => r.relname == "location_summary")).map (·.relkind)
      = some .view := by
  native_decide

/-- `l.id` resolves through the FROM alias `l → test_smoke.locations`. -/
example :
    let viewRel := (folded.relations.find? (fun r => r.relname == "location_summary")).map (·.oid)
    let idAttr  := folded.attributes.find?
                    (fun a => viewRel.any (· == a.attrelid) && a.attname == "id")
    idAttr.map (·.atttypid.raw) = some 20 := by
  native_decide

/-- Bare `name` reference — fold's `resolveBareColumn` finds it in
    the single FROM relation and pulls its identifier-domain type. -/
example :
    let identifierOid :=
      (folded.types.find? (fun t => t.typname == "identifier")).map (·.oid.raw)
    let viewRel := (folded.relations.find? (fun r => r.relname == "location_summary")).map (·.oid)
    let nameAttr := folded.attributes.find?
                    (fun a => viewRel.any (· == a.attrelid) && a.attname == "name")
    nameAttr.map (·.atttypid.raw) = identifierOid ∧ identifierOid.isSome := by
  native_decide

/-- `EXTRACT(...) AS epoch` — non-ColumnRef expression collapses to
    the unknown sentinel 2249 (record). -/
example :
    let viewRel := (folded.relations.find? (fun r => r.relname == "location_summary")).map (·.oid)
    let epochAttr := folded.attributes.find?
                    (fun a => viewRel.any (· == a.attrelid) && a.attname == "epoch")
    epochAttr.map (·.atttypid.raw) = some 2249 := by
  native_decide

end Pg.Catalog.FoldPipelineTest
