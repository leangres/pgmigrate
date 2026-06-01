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

/-- Phase 0 doesn't handle CompositeTypeStmt/CreateDomainStmt/CreateStmt
    yet — they collapse to `.other` and don't add type rows. As the
    fold's coverage grows, this number rises. -/
example : folded.types.length = 0 := by native_decide

example : folded.relations.length = 0 := by native_decide

end Pg.Catalog.FoldPipelineTest
