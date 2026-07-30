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

end Pg.Migrate.StepTest
