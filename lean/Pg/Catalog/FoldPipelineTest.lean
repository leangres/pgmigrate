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

The smoke fixture has 4 stmts:
  CREATE SCHEMA test_smoke;
  CREATE DOMAIN test_smoke.identifier AS TEXT CHECK ...;
  CREATE TYPE test_smoke.point AS (x INTEGER, y INTEGER);
  CREATE TABLE test_smoke.locations (...);

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

/-- The decoder saw 4 stmts; one of them (CREATE SCHEMA) is folded. -/
example : (parseResult.stmts.length) = 4 := by native_decide

/-- pg_catalog + public + test_smoke. -/
example : folded.namespaces.length = 3 := by native_decide

/-- The new namespace from CREATE SCHEMA is materialized. -/
example : (folded.namespaces.find? (fun n => n.nspname == "test_smoke")).isSome := by
  native_decide

/-- Phase 1+2 lifts CreateDomain + CompositeType + CreateStmt into
    typed dispatch. The fixture has one of each, so the snapshot
    gains:
      * 3 types  — `test_smoke.identifier` (domain),
                   `test_smoke.point` (composite),
                   `test_smoke.locations` (table's implicit composite)
      * 2 relations — `point` (compositeType) and `locations` (table)
      * 5 attributes — `point.x`, `point.y`,
                       `locations.id`, `locations.name`, `locations.position`. -/
example : folded.types.length = 3 := by native_decide

example : folded.relations.length = 2 := by native_decide

example : folded.attributes.length = 5 := by native_decide

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

end Pg.Catalog.FoldPipelineTest
