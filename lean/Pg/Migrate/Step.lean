/-
Pg.Migrate.Step — applying a statement to a catalog, with preconditions.

`Fold` projects: it takes whatever the parser produced and folds it in, TOTAL,
never failing. That is right for its job — reconstructing a catalog from a schema
that already exists and already worked.

A migration is the other direction. It has to answer "may this statement run
against THIS catalog", and the interesting answers are no: the column does not
exist, the constraint name is already taken, something still depends on the
thing you are dropping.

## Checking is split from mutation, deliberately

  `elabStmt : CatalogState → Stmt → Except CatalogError (List CatalogEffect)`
  `applyEffect : CatalogState → CatalogEffect → CatalogState`   -- TOTAL
  `step s st := (elabStmt s st).map (applyEffects s)`

Every precondition lives in `elabStmt`; every OID-allocation and determinism
argument lives in `applyEffect`. Neither has to reason about the other. It also
means hazard and lock analysis can later read the EFFECT LIST rather than
re-matching `Stmt` — an effect list containing `dropAttribute` is data-lossy by
construction, with no second opinion about which statements destroy data.

## This does not replace `Fold`, and must not

`Fold` carries a byte-equivalence claim against a retired C tool over a
1,384-statement production schema, and deliberately reproduces that tool's
quirks. `step` rejects several of them. Where the two disagree on a schema both
accept, that disagreement is a FINDING to triage — quite possibly a real defect
in the schema — not a bug in either. Correcting `Fold` would void its claim.
-/

import Pg.Catalog.State
import Pg.Stmt
import Pg.Pretty

namespace Pg.Migrate

open Pg.Catalog Pg.Ast Pg.Stmt

/-! ## Errors

    Named per precondition class rather than as a single `String`, so a caller
    can branch — a migration runner wants to distinguish "already exists" (often
    benign, and what `IF NOT EXISTS` is for) from "still has dependents" (never
    benign, and the whole point of `RESTRICT`). -/

inductive CatalogError where
  | schemaNotFound     (name : String)
  | relationNotFound   (name : String)
  | relationExists     (name : String)
  | columnNotFound     (rel col : String)
  | columnExists       (rel col : String)
  | constraintNotFound (rel name : String)
  | constraintExists   (rel name : String)
  /-- `DROP … RESTRICT` with `normal` dependents. Carries how many, because the
      count is the first thing anyone asks. -/
  | dependentsExist    (name : String) (count : Nat)
  /-- A foreign key whose referenced columns are not covered by a unique index —
      the check Postgres performs and a schema-shape predicate cannot. -/
  | fkTargetNotUnique  (rel : String) (cols : List String)
  /-- Reached a statement this transition does not model yet. Explicit rather
      than silently succeeding: a migration proved against a `step` that quietly
      ignored half its statements would be worse than no proof. -/
  | unsupported        (what : String)
deriving DecidableEq, Repr

/-! ## Effects — the total mutation language -/

inductive CatalogEffect where
  | addNamespace    (oid : Nat) (name : String)
  | addRelation     (oid nsOid : Nat) (name : String)
  | dropRelation    (oid : Nat)
  | addAttribute    (rel : Nat) (name : String) (typ : Nat) (attnum : Int) (notNull : Bool)
  | dropAttribute   (rel : Nat) (name : String)
  | setAttrNotNull  (rel : Nat) (name : String) (v : Bool)
  | renameAttribute (rel : Nat) (old new : String)
  | addConstraintRow    (row : PgConstraint)
  | dropConstraintRow   (oid : Nat)
  | validateConstraintRow (oid : Nat)
  | bumpOid
deriving DecidableEq, Repr

/-- TOTAL. Every constructor is a catalog write that cannot fail — all the
    "may I" questions were answered in `elabStmt`. -/
def applyEffect (s : CatalogState) : CatalogEffect → CatalogState
  | .addNamespace oid name =>
      let ns : PgNamespace := { oid := ⟨oid⟩, nspname := name }
      let snap' := { s.snap with namespaces := s.snap.namespaces ++ [ns] }
      { s with snap := snap', nextOid := max s.nextOid (oid + 1) }
  | .addRelation oid nsOid name =>
      let rel : PgClass :=
        { oid := ⟨oid⟩, relname := name, relnamespace := ⟨nsOid⟩
        , relkind := .ordinaryTable, reltype := ⟨0⟩ }
      let snap' := { s.snap with relations := s.snap.relations ++ [rel] }
      { s with snap := snap', nextOid := max s.nextOid (oid + 1) }
  | .dropRelation oid =>
      let snap' :=
        { s.snap with
          relations  := s.snap.relations.filter (fun r => r.oid.raw != oid),
          attributes := s.snap.attributes.filter (fun a => a.attrelid.raw != oid) }
      -- Dropping a relation takes its constraints and indexes with it. That is
      -- not CASCADE — those rows have no independent existence, and leaving
      -- them would leave the catalog describing constraints on nothing.
      { s with snap := snap'
             , constraints := s.constraints.filter (fun c => c.conrelid.raw != oid)
             , indexes     := s.indexes.filter (fun i => i.indrelid.raw != oid) }
  | .addAttribute rel name typ attnum notNull =>
      let a : PgAttribute :=
        { attrelid := ⟨rel⟩, attname := name, atttypid := ⟨typ⟩
        , attnum := attnum, attnotnull := notNull }
      { s with snap := { s.snap with attributes := s.snap.attributes ++ [a] } }
  | .dropAttribute rel name =>
      let attrs := s.snap.attributes.filter
        (fun a => !(a.attrelid.raw == rel && a.attname == name))
      { s with snap := { s.snap with attributes := attrs } }
  | .setAttrNotNull rel name v =>
      let attrs := s.snap.attributes.map (fun a =>
        if a.attrelid.raw == rel && a.attname == name then
          { a with attnotnull := v } else a)
      { s with snap := { s.snap with attributes := attrs } }
  | .renameAttribute rel old new =>
      let attrs := s.snap.attributes.map (fun a =>
        if a.attrelid.raw == rel && a.attname == old then
          { a with attname := new } else a)
      { s with snap := { s.snap with attributes := attrs } }
  | .addConstraintRow row =>
      { s with constraints := s.constraints ++ [row]
             , nextOid := max s.nextOid (row.oid.raw + 1) }
  | .dropConstraintRow oid =>
      { s with constraints := s.constraints.filter (fun c => c.oid.raw != oid) }
  | .validateConstraintRow oid =>
      let cs := s.constraints.map (fun c =>
        if c.oid.raw == oid then { c with convalidated := true } else c)
      { s with constraints := cs }
  | .bumpOid => { s with nextOid := s.nextOid + 1 }

def applyEffects (s : CatalogState) (es : List CatalogEffect) : CatalogState :=
  es.foldl applyEffect s

/-! ## Resolution -/

/-- The schema a qualified name lives in, defaulting to `public` exactly as an
    unqualified name does under a default `search_path`. -/
def schemaOf (n : Identifier) : String :=
  match n with
  | .qualified s _   => s
  | .unqualified _   => "public"

def nameOf (n : Identifier) : String :=
  match n with
  | .qualified _ n => n
  | .unqualified n => n

def findRel (s : CatalogState) (n : Identifier) : Option PgClass := do
  let ns ← s.snap.findNamespaceByName (schemaOf n)
  s.snap.findRelationInSchema ns.oid (nameOf n)

def relColumns (s : CatalogState) (rel : Oid .relation) : List PgAttribute :=
  s.snap.attributes.filter (fun a => a.attrelid == rel)

/-! ## Small helpers over the AST

    These read a `TableConstraint` / `Stmt` without duplicating knowledge that
    belongs in `pgast`. `constraintName` synthesises when the AST carries none,
    the way Postgres does — a constraint always ends up with a name, and a
    migration that cannot refer to it later has lost something. -/

/-- The declared constraint name, or one synthesised from the relation and kind.

    Postgres's own scheme is `<table>_<column>_<suffix>`; this is deliberately
    simpler and only has to be stable and unique per relation, since that is
    what `findConstraint` keys on. -/
def constraintName : TableConstraint → String
  | .primaryKey _ (some n) => n
  | .primaryKey _ none     => "pkey"
  | .unique _ (some n)     => n
  | .unique _ none         => "key"
  | .foreignKey _ _ _ _ _ (some n) _ => n
  | .foreignKey _ ref _ _ _ none   _ => ref ++ "_fkey"
  | .check _ (some n)      => n
  | .check _ none          => "check"

def conTypeOf : TableConstraint → ConType
  | .primaryKey _ _        => .primaryKey
  | .unique _ _            => .unique
  | .foreignKey _ _ _ _ _ _ _ => .foreignKey
  | .check _ _             => .check

/-- The statement kind, for the `unsupported` error. Non-catchall, so a new
    `Stmt` constructor breaks THIS match too and cannot reach the transition as
    a silently-mislabelled error. -/
def stmtKeyword : Stmt → String
  | .createFunction _               => "CREATE FUNCTION"
  | .createTable _                  => "CREATE TABLE"
  | .createIndex _                  => "CREATE INDEX"
  | .createSqlFunction _            => "CREATE FUNCTION (SQL)"
  | .createSetReturningFunction _   => "CREATE FUNCTION (SETOF)"
  | .createTableReturningFunction _ => "CREATE FUNCTION (TABLE)"
  | .createScalarSelectFunction _   => "CREATE FUNCTION (scalar SELECT)"
  | .createRecursiveCteFunction _   => "CREATE FUNCTION (recursive CTE)"
  | .createTrigger _                => "CREATE TRIGGER"
  | .createSchema _                 => "CREATE SCHEMA"
  | .createDomain _                 => "CREATE DOMAIN"
  | .createType _                   => "CREATE TYPE"
  | .createPolicy _                 => "CREATE POLICY"
  | .alterTable _                   => "ALTER TABLE"
  | .dropObject _                   => "DROP"

/-! ## Elaboration — every precondition lives here

    Each arm answers "may this run against THIS catalog" and returns the writes
    it would make. Nothing below allocates or mutates; that is `applyEffect`'s
    job, and keeping them apart is what lets each be reasoned about alone. -/

/-- `ALTER TABLE`, which is where most of the preconditions are. -/
def elabAlterTable (s : CatalogState) (a : AlterTableStmt)
    : Except CatalogError (List CatalogEffect) := do
  let some rel := findRel s a.name
    | throw (.relationNotFound (nameOf a.name))
  let cols := relColumns s rel.oid
  let hasCol (n : String) : Bool := cols.any (fun c => c.attname == n)
  let relName := nameOf a.name
  match a.action with
  | .addColumn col ifNotExists =>
      if hasCol col.name then
        -- IF NOT EXISTS makes a re-run a no-op rather than an error; that is
        -- the whole point of it, so it must not be treated as success-with-write.
        if ifNotExists then pure [] else throw (.columnExists relName col.name)
      else
        let nextAttnum : Int :=
          (cols.map (fun c => c.attnum)).foldl (fun m n => if n > m then n else m) 0 + 1
        pure [.addAttribute rel.oid.raw col.name 0 nextAttnum col.notNull]
  | .dropColumn name ifExists _ =>
      if hasCol name then pure [.dropAttribute rel.oid.raw name]
      else if ifExists then pure []
      else throw (.columnNotFound relName name)
  | .setNotNull name =>
      if hasCol name then pure [.setAttrNotNull rel.oid.raw name true]
      else throw (.columnNotFound relName name)
  | .dropNotNull name =>
      if hasCol name then pure [.setAttrNotNull rel.oid.raw name false]
      else throw (.columnNotFound relName name)
  | .renameColumn from_ to =>
      if !hasCol from_ then throw (.columnNotFound relName from_)
      else if hasCol to then throw (.columnExists relName to)
      else pure [.renameAttribute rel.oid.raw from_ to]
  | .addConstraint c notValid =>
      let cname := constraintName c
      match s.findConstraint rel.oid cname with
      | some _ => throw (.constraintExists relName cname)
      | none =>
        -- A foreign key must reference uniquely-indexed columns or it does not
        -- identify one row. Postgres enforces this; a shape-only predicate
        -- cannot, because it needs the index catalog.
        match c with
        | .foreignKey _ refTable refCols _ _ _ _ =>
            let some refRel := findRel s (Identifier.unqualified refTable)
              | throw (.relationNotFound refTable)
            let refAttnums := (relColumns s refRel.oid).filterMap (fun a =>
              if refCols.contains a.attname then some a.attnum else none)
            if s.hasUniqueIndexOn refRel.oid refAttnums then
              pure [.addConstraintRow
                { oid := ⟨s.nextOid⟩, conname := cname, connamespace := rel.relnamespace
                , contype := .foreignKey, convalidated := !notValid
                , conrelid := rel.oid, confrelid := some refRel.oid }]
            else throw (.fkTargetNotUnique refTable refCols)
        | _ =>
            pure [.addConstraintRow
              { oid := ⟨s.nextOid⟩, conname := cname, connamespace := rel.relnamespace
              , contype := conTypeOf c, convalidated := !notValid
              , conrelid := rel.oid }]
  | .validateConstraint name =>
      match s.findConstraint rel.oid name with
      | some c => pure [.validateConstraintRow c.oid.raw]
      | none   => throw (.constraintNotFound relName name)
  | .dropConstraint name ifExists _ =>
      match s.findConstraint rel.oid name with
      | some c => pure [.dropConstraintRow c.oid.raw]
      | none   => if ifExists then pure [] else throw (.constraintNotFound relName name)
  | .enableRowLevelSecurity  => pure []
  | .disableRowLevelSecurity => pure []
  | .forceRowLevelSecurity   => pure []
  | .noForceRowLevelSecurity => pure []
  -- Modelled in the AST, not yet in the transition. Explicit, so a migration
  -- using one cannot be "proved" against a step that quietly ignored it.
  | .setDefault _ _      => throw (.unsupported "ALTER COLUMN SET DEFAULT")
  | .dropDefault _       => throw (.unsupported "ALTER COLUMN DROP DEFAULT")
  | .setColumnType _ _ _ => throw (.unsupported "ALTER COLUMN TYPE")
  | .renameTable _       => throw (.unsupported "ALTER TABLE RENAME TO")
  | .setSchema _         => throw (.unsupported "ALTER TABLE SET SCHEMA")

/-- `DROP`. `RESTRICT` is refused when anything still `normal`-depends on the
    target; `CASCADE` is accepted, and the hazard classifier is what should make
    that visible rather than this. -/
def elabDrop (s : CatalogState) (d : DropStmt)
    : Except CatalogError (List CatalogEffect) := do
  match d.target with
  | .table n =>
      match findRel s n with
      | none => if d.ifExists then pure [] else throw (.relationNotFound (nameOf n))
      | some rel =>
          let deps := s.dependentsOf .relation rel.oid.raw
          match d.behavior with
          | .restrict =>
              if deps.isEmpty then pure [.dropRelation rel.oid.raw]
              else throw (.dependentsExist (nameOf n) deps.length)
          | .cascade => pure [.dropRelation rel.oid.raw]
  | t => throw (.unsupported ("DROP " ++ t.keyword))

/-- Apply one statement. -/
def elabStmt (s : CatalogState) : Stmt → Except CatalogError (List CatalogEffect)
  | .createSchema sc =>
      let name := nameOf sc.name
      match s.snap.findNamespaceByName name with
      | some _ => if sc.ifNotExists then pure [] else throw (.relationExists name)
      | none   => pure [.addNamespace s.nextOid name]
  | .createTable t =>
      match findRel s t.name with
      | some _ => if t.ifNotExists then pure [] else throw (.relationExists (nameOf t.name))
      | none =>
        match s.snap.findNamespaceByName (schemaOf t.name) with
        | none    => throw (.schemaNotFound (schemaOf t.name))
        | some ns =>
            let relOid := s.nextOid
            let addCols := t.columns.zipIdx.map (fun (c, i) =>
              CatalogEffect.addAttribute relOid c.name 0 (Int.ofNat i + 1) c.notNull)
            pure (.addRelation relOid ns.oid.raw (nameOf t.name) :: addCols)
  | .alterTable a => elabAlterTable s a
  | .dropObject d => elabDrop s d
  | st => throw (.unsupported (stmtKeyword st))

/-- The transition. -/
def step (s : CatalogState) (st : Stmt) : Except CatalogError CatalogState :=
  (elabStmt s st).map (applyEffects s)

/-- Run a sequence, stopping at the first statement whose preconditions fail.

    The index is carried because "statement 7 failed" is the first thing anyone
    needs, and a bare error loses it. -/
def run (s : CatalogState) (sts : List Stmt)
    : Except (Nat × CatalogError) CatalogState :=
  sts.zipIdx.foldlM
    (fun acc (st, i) =>
      match step acc st with
      | .ok s'  => .ok s'
      | .error e => .error (i, e))
    s

/-! ## Projecting the outcome

    `CatalogState` has no `DecidableEq` — it carries a `Snapshot`, and deriving
    equality across the whole catalog would be expensive and is not wanted. So
    assertions project the part being claimed: the error if there is one, or a
    specific lookup from the resulting state. That is also better as a test —
    comparing whole states would fail on incidental differences like OID
    counters and say nothing about the property under test. -/

/-- The error, if the statement was refused. -/
def errorOf : Except CatalogError α → Option CatalogError
  | .error e => some e
  | .ok _    => none

/-- The failing statement's index and error, if a run was refused. -/
def runErrorOf : Except (Nat × CatalogError) α → Option (Nat × CatalogError)
  | .error e => some e
  | .ok _    => none

end Pg.Migrate
