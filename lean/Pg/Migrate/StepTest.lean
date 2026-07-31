/-
Pins for the catalog transition.

The interesting assertions here are the FAILURES. A transition that accepts
everything is `Fold`, and we already have one of those. What makes `step` worth
writing is that it refuses — so most of these check that a statement which
cannot run against a given catalog is rejected, and with the right error.

Assertions project (`errorOf`, `.toOption.map`) rather than comparing whole
states: `CatalogState` has no `DecidableEq`, and comparing entire catalogs would
fail on incidental differences like OID counters while saying nothing about the
property under test.
-/

import Pg.Migrate.Step

namespace Pg.Migrate.StepTest

open Pg.Catalog Pg.Ast Pg.Stmt Pg.Migrate

private def resourceName : Identifier := Identifier.qualified "graph" "resource"

/-- A catalog holding `graph.resource(id, kind)`, built by running the CREATEs
    through `step` rather than hand-written — so the fixture itself exercises the
    transition. -/
private def base : Except CatalogError CatalogState :=
  step CatalogState.empty (.createSchema { name := Identifier.unqualified "graph" })
    >>= fun s => step s (.createTable
      { name := resourceName
      , columns :=
          [ { name := "id",   pgType := .bigint, notNull := true }
          , { name := "kind", pgType := .text } ] })

private def baseState : CatalogState := base.toOption.getD CatalogState.empty

private def colsOf (s : CatalogState) : Option (List String) :=
  (findRel s resourceName).map (fun r => (relColumns s r.oid).map (fun c => c.attname))

example : base.isOk = true := by native_decide

example : colsOf baseState = some ["id", "kind"] := by native_decide

/-! ## Preconditions refuse -/

example :
    errorOf (step baseState
      (.alterTable { name := Identifier.qualified "graph" "nope"
                   , action := .setNotNull "kind" }))
      = some (.relationNotFound "nope") := by
  native_decide

example :
    errorOf (step baseState
      (.alterTable { name := resourceName, action := .setNotNull "missing" }))
      = some (.columnNotFound "resource" "missing") := by
  native_decide

example :
    errorOf (step baseState
      (.alterTable { name := resourceName
                   , action := .addColumn { name := "kind", pgType := .text } }))
      = some (.columnExists "resource" "kind") := by
  native_decide

/-- …but `IF NOT EXISTS` makes the same statement a no-op, which is what a
    re-runnable migration depends on. -/
example :
    (step baseState
      (.alterTable { name := resourceName
                   , action := .addColumn { name := "kind", pgType := .text } true })
    ).toOption.map colsOf = some (some ["id", "kind"]) := by
  native_decide

example :
    errorOf (step baseState
      (.alterTable { name := resourceName, action := .renameColumn "id" "kind" }))
      = some (.columnExists "resource" "kind") := by
  native_decide

example :
    errorOf (step baseState
      (.alterTable { name := resourceName, action := .validateConstraint "nope" }))
      = some (.constraintNotFound "resource" "nope") := by
  native_decide

/-! ## NOT VALID, then VALIDATE

    The sequence that makes an online migration possible, and the reason
    `convalidated` had to be modelled at all. -/

private def afterNotValid : Except CatalogError CatalogState :=
  step baseState
    (.alterTable { name := resourceName
                 , action := .addConstraint
                     (.check (.isNotNull (.var "kind")) (some "kind_nn")) true })

private def validatedFlags (s : CatalogState) : List Bool :=
  s.constraints.map (fun c => c.convalidated)

/-- Added `NOT VALID`: enforced on new rows, but NOT yet checked against
    existing ones. -/
example : afterNotValid.toOption.map validatedFlags = some [false] := by
  native_decide

example :
    (afterNotValid >>= fun s => step s
      (.alterTable { name := resourceName, action := .validateConstraint "kind_nn" })
    ).toOption.map validatedFlags = some [true] := by
  native_decide

example :
    errorOf (afterNotValid >>= fun s => step s
      (.alterTable { name := resourceName
                   , action := .addConstraint
                       (.check (.isNotNull (.var "id")) (some "kind_nn")) }))
      = some (.constraintExists "resource" "kind_nn") := by
  native_decide

/-! ## An unmodelled statement is an ERROR, not a silent success

    A migration "proved" against a transition that quietly ignored half its
    statements would be worse than no proof at all. -/

example :
    errorOf (step baseState
      (.alterTable { name := resourceName
                   , action := .setColumnType "kind" .bigint none }))
      = some (.unsupported "ALTER COLUMN TYPE") := by
  native_decide

/-! ## `run` reports WHICH statement failed -/

example :
    runErrorOf (run baseState
      [ .alterTable { name := resourceName, action := .setNotNull "kind" }
      , .alterTable { name := resourceName, action := .setNotNull "missing" } ])
      = some (1, .columnNotFound "resource" "missing") := by
  native_decide

/-- A run whose statements all hold succeeds, and the effects landed in order. -/
example :
    (run baseState
      [ .alterTable { name := resourceName
                    , action := .addColumn { name := "archived_at", pgType := .timestamptz } }
      , .alterTable { name := resourceName
                    , action := .renameColumn "archived_at" "removed_at" } ]
    ).toOption.map colsOf = some (some ["id", "kind", "removed_at"]) := by
  native_decide


/-! ## DROP … CASCADE takes the dependents with it

    It previously emitted ONLY the target's drop, which left a view behind
    pointing at a table that no longer existed. These pin the closure. -/

private def graphNs : Nat := 16384

/-- `graph.resource` ← `graph.v_resource` ← `graph.v_summary`. -/
private def withViews : CatalogState :=
  { CatalogState.empty with
    snap := { CatalogState.empty.snap with
      namespaces := CatalogState.empty.snap.namespaces ++
        [{ oid := ⟨graphNs⟩, nspname := "graph" }]
      relations := [
        { oid := ⟨16400⟩, relname := "resource",   relnamespace := ⟨graphNs⟩
        , relkind := .ordinaryTable, reltype := ⟨16410⟩ }
      , { oid := ⟨16401⟩, relname := "v_resource", relnamespace := ⟨graphNs⟩
        , relkind := .view, reltype := ⟨16411⟩ }
      , { oid := ⟨16402⟩, relname := "v_summary",  relnamespace := ⟨graphNs⟩
        , relkind := .view, reltype := ⟨16412⟩ }] }
    depends := [
      { classid := .relation, objid := 16401
      , refclassid := .relation, refobjid := 16400, deptype := .normal }
    , { classid := .relation, objid := 16402
      , refclassid := .relation, refobjid := 16401, deptype := .normal } ] }

private def dropResource (b : DropBehavior) : Stmt :=
  .dropObject { target := .table (Identifier.qualified "graph" "resource"), behavior := b }

/-- RESTRICT still refuses — the direct dependent is enough.

    ⚠ Pinned as EMITTED: the error names `resource`, not `graph.resource`, even
    though the statement was qualified. `nameOf` drops the schema. That is a real
    wart — two schemas can each hold a `resource` and the message would not say
    which — but qualifying it changes every existing error pin, so it is its own
    change. This pin is what makes that change visible when someone makes it. -/
example : errorOf (step withViews (dropResource .restrict))
    = some (.dependentsExist "resource" 1) := by
  native_decide

/-- CASCADE emits a drop for EVERY object in the closure, not just the target.
    Three, not one: this is the pin that fails on the old behaviour. -/
example : (elabStmt withViews (dropResource .cascade)).toOption.map (·.length)
    = some 3 := by native_decide

/-- Deepest-first, so a dependent is gone before the thing it depends on. -/
example : (elabStmt withViews (dropResource .cascade)).toOption
    = some [.dropRelation 16402, .dropRelation 16401, .dropRelation 16400] := by
  native_decide

/-- And the resulting state has none of the three. The old behaviour left two
    views describing a table that no longer existed. -/
example : (step withViews (dropResource .cascade)).toOption.map
    (fun s => s.snap.relations.length) = some 0 := by native_decide

/-- Dropping the MIDDLE view takes only what sits on it, leaving the table. -/
private def dropView : Stmt :=
  .dropObject { target := .table (Identifier.qualified "graph" "v_resource")
              , behavior := .cascade }

example : (step withViews dropView).toOption.map
    (fun s => s.snap.relations.map (fun r => r.relname)) = some ["resource"] := by
  native_decide

/-! ## pg_depend does not leak on a drop

    A stale edge whose referent is gone still counts in `dependentsOf`, so a
    later RESTRICT refuses over a dependent the user cannot find. -/

example : (step withViews dropView).toOption.map (fun s => s.depends.length)
    = some 0 := by native_decide

/-- Which means the table is then droppable with RESTRICT — it was not before,
    and would still not be if the edges had leaked. -/
example : ((step withViews dropView).toOption.map
    (fun s => errorOf (step s (dropResource .restrict)))) = some none := by
  native_decide

end Pg.Migrate.StepTest
