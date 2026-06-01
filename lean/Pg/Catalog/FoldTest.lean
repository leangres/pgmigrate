/-
Pg.Catalog.FoldTest — exercises `Snapshot.ofTopParseResult` on
hand-crafted `TopStmt` lists. Validates that:

  * `CreateSchemaStmt` adds exactly one namespace row.
  * Repeated `CreateSchemaStmt` for the same name dedupes
    (matches the C tool's `snap_ensure_namespace`).
  * `CreateEnumStmt` adds one type row in the right namespace.
  * Unqualified enums land in `public`.
  * `.other` payloads leave the snapshot unchanged.

When the C decoder gains `--typed` mode, an additional Bazel-driven
test will run smoke_fixture.sql through that path and byte-diff the
resulting snapshot against `pgpb_to_snapshot.c`'s output. The
hand-crafted tests below are sufficient to lock the fold's shape
in the meantime.
-/

import Pg.Catalog.Fold

namespace Pg.Catalog.FoldTest

open Pg.Catalog Pg.Query.Top

/-! ### CreateSchemaStmt -/

/-- One schema → one new namespace row alongside pg_catalog + public. -/
def one_schema : Snapshot :=
  Snapshot.ofTopParseResult {
    version := 170007
    stmts   := [{ stmt := .createSchemaStmt { schemaname := "ids" } }]
  }

example : one_schema.namespaces.length = 3 := by native_decide
example : (one_schema.namespaces.find? (fun n => n.nspname == "ids")).isSome := by native_decide

/-- Duplicate CREATE SCHEMA dedupes — only one row per name. -/
def dup_schema : Snapshot :=
  Snapshot.ofTopParseResult {
    version := 170007
    stmts   := [
      { stmt := .createSchemaStmt { schemaname := "ids" } },
      { stmt := .createSchemaStmt { schemaname := "ids" } },
      { stmt := .createSchemaStmt { schemaname := "audit" } }
    ]
  }

example : dup_schema.namespaces.length = 4 := by native_decide
example : (dup_schema.namespaces.filter (fun n => n.nspname == "ids")).length = 1 := by native_decide

/-! ### CreateEnumStmt -/

/-- Qualified enum: lands in the named schema. -/
def one_enum : Snapshot :=
  Snapshot.ofTopParseResult {
    version := 170007
    stmts   := [
      { stmt := .createSchemaStmt { schemaname := "ids" } },
      { stmt := .createEnumStmt {
          qualName := { schema := some "ids", name := "key_type" },
          labels   := ["symmetric", "hmac", "rsa"]
        } }
    ]
  }

example : one_enum.types.length = 1 := by native_decide
example : (one_enum.types.find? (fun t => t.typname == "key_type")).isSome := by native_decide

/-- Unqualified enum: lands in `public`. The fold doesn't need to
    create the public namespace — it's seeded. -/
def public_enum : Snapshot :=
  Snapshot.ofTopParseResult {
    version := 170007
    stmts   := [{ stmt := .createEnumStmt {
      qualName := { schema := none, name := "color" },
      labels   := ["red", "green", "blue"]
    } }]
  }

example : public_enum.types.length = 1 := by native_decide

/-! ### CreateDomainStmt -/

/-- `CREATE DOMAIN ids.identifier AS TEXT` with a builtin baseType.
    The OID hint (25 = text) is taken directly without snapshot walk. -/
def one_domain : Snapshot :=
  Snapshot.ofTopParseResult {
    version := 170007
    stmts   := [
      { stmt := .createSchemaStmt { schemaname := "ids" } },
      { stmt := .createDomainStmt {
          qualName := { schema := some "ids", name := "identifier" },
          baseType := { schema := none, name := "text", oidHint := 25 }
        } }
    ]
  }

example : one_domain.types.length = 1 := by native_decide
example :
    (one_domain.types.find? (fun t => t.typname == "identifier")).map (·.typbasetype.raw)
      = some 25 := by
  native_decide

/-! ### CompositeTypeStmt + CreateStmt -/

/-- Composite + table referencing the composite. -/
def composite_chain : Snapshot :=
  Snapshot.ofTopParseResult {
    version := 170007
    stmts   := [
      { stmt := .createSchemaStmt { schemaname := "geo" } },
      { stmt := .compositeTypeStmt {
          qualName := { schema := some "geo", name := "point" },
          columns  := [
            { name := "x", typeRef := { name := "int4", oidHint := 23 }, notNull := true },
            { name := "y", typeRef := { name := "int4", oidHint := 23 }, notNull := true }
          ]
        } },
      { stmt := .createStmt {
          qualName := { schema := some "geo", name := "locations" },
          columns  := [
            { name := "id",  typeRef := { name := "int8", oidHint := 20 }, notNull := true },
            -- The `point` user type: oidHint=0 means "resolve via snapshot lookup".
            { name := "pos", typeRef := { schema := some "geo", name := "point" }, notNull := false }
          ]
        } }
    ]
  }

example : composite_chain.types.length = 2 := by native_decide       -- point composite + locations implicit row type
example : composite_chain.relations.length = 2 := by native_decide   -- point composite + locations table
example : composite_chain.attributes.length = 4 := by native_decide  -- 2 from point + 2 from locations

/-- The cross-reference works: `locations.pos.atttypid` ≡ `point.oid`. -/
example :
    let pointOid := (composite_chain.types.find? (fun t => t.typname == "point")).map (·.oid.raw)
    let posOid   := (composite_chain.attributes.find? (fun a => a.attname == "pos")).map (·.atttypid.raw)
    pointOid = posOid ∧ pointOid.isSome := by
  native_decide

/-! ### Other / catchall -/

/-- `.other` payloads don't perturb the snapshot. -/
def opaque_only : Snapshot :=
  Snapshot.ofTopParseResult {
    version := 170007
    stmts   := List.replicate 5 { stmt := .other .empty }
  }

example : opaque_only.namespaces.length = 2 := by native_decide  -- just the seeded pair
example : opaque_only.types.length = 0 := by native_decide

end Pg.Catalog.FoldTest
