# Changelog

## 17.6.3 — CASCADE actually cascades, and pg_depend stops leaking

Two real bugs, both in the drop path.

**`DROP … CASCADE` emitted only the target's drop.** It never dropped the
dependents — which is the entire meaning of CASCADE. A `DROP TABLE t CASCADE`
left every view on `t` in the catalog, describing a table that no longer existed.
Now it emits the full transitive closure (pgcatalog 17.6.4's `cascadeClosure`),
deepest-first so a dependent is gone before the thing it depends on.

⚠ And it **refuses a non-converged closure** rather than emitting a short one.
The closure is fuel-bounded because `pg_depend` is a general graph with real
cycles; a partial cascade that half-drops the schema and reports success is worse
than a refusal.

**`dropRelation` never cleaned `pg_depend`.** Edges at both ends survived the
drop, and a stale edge whose referent is gone still counts in `dependentsOf` — so
a later `DROP … RESTRICT` refused over a dependent that was already dropped,
naming an object the user cannot find. Both ends are now filtered.

Pinned: RESTRICT still refuses; CASCADE emits three effects for a 3-deep chain,
not one; drop order is deepest-first; the resulting state holds none of the
three; dropping the middle view leaves the table; the depend edges are gone; and
the table is droppable with RESTRICT afterwards — which it would not be if the
edges had leaked.

⚠ One wart pinned as-emitted rather than fixed: `dependentsExist` names
`resource`, not `graph.resource`. `nameOf` drops the schema, so an error cannot
say which schema's `resource` it meant. Qualifying it changes every existing
error pin, so it is its own change — and this pin makes it visible.

## 17.6.2 — DML is identity on the catalog, and it is proved

Bumps `pgast` to 17.6.2, which adds top-level `INSERT`/`UPDATE`/`DELETE`.

The exhaustivity lock did its job: `stmtKeyword` stopped compiling the moment
`Stmt` grew, which is the entire reason it has no catchall.

`elabStmt` now has explicit DML arms emitting **no** effects, rather than letting
them fall through to `unsupported`. The distinction is the point — `unsupported`
means "we cannot say what this does", while these arms are a positive claim that
they do nothing a catalog can observe.

That claim is now a theorem rather than a comment:

    theorem insert_is_catalog_identity (s : CatalogState) (i : InsertStmt) :
        step s (.insert i) = .ok s := rfl

plus `update`/`delete`, and `run_dml_only` lifting it to whole scripts by
induction. These are the module's **first universally quantified** results —
everything else here is `native_decide` over concrete states, true of what was
tested and silent about the rest. A migration runner can now skip the catalog
transition for a backfill on a proved basis.

Verified by deliberate break: making the DML arms emit one bogus effect turns
all of them red (9 errors). They constrain the implementation, which is not
something to assume of a proof in this codebase.

⚠ Three scope limits, one of which is a real hole rather than a simplification:
the heap is not modelled (obvious, and not what `CatalogState` is);
`pg_class.reltuples`/`relpages` do move on DML via autovacuum, so a differential
gate must mask them; and **a DML statement can fire a trigger whose body runs
DDL**, in which case the catalog does change and these theorems do not describe
what happened. They are claims about the statement, not its trigger closure.
Closing that needs `pg_trigger` in the kernel. Documented, not proved absent.

## 17.6.1 — a transition that can refuse

`Fold` projects: it folds whatever the parser produced into a catalog, TOTAL,
never failing. Right for its job — reconstructing a catalog from a schema that
already exists and already worked.

A migration is the other direction. It has to answer *may this statement run
against THIS catalog*, and the interesting answers are no.

`Pg.Migrate.step : CatalogState → Stmt → Except CatalogError CatalogState`, with
`run` over a list reporting **which** statement failed.

### Checking is split from mutation

`elabStmt` decides and returns effects; `applyEffect` is total and just writes.
Every precondition proof lives in one, every allocation argument in the other,
and neither reasons about the other. It also means hazard and lock analysis can
later read the **effect list** rather than re-matching `Stmt` — an effect list
containing `dropAttribute` is data-lossy by construction.

### It consumes the emitter-side AST

`Fold` takes `Pg.Query.Top.TopStmt` (what Postgres parsed); `step` takes
`Pg.Stmt.Stmt` (what we are about to emit). Both directions are wanted, which is
why this module now depends on `pgast` as well.

### What it refuses

ALTER on a missing relation or column; ADD COLUMN or RENAME onto a name already
taken; VALIDATE or DROP naming a constraint that was never added; re-adding a
constraint name; `DROP … RESTRICT` while `normal` dependents remain; and a
foreign key whose referenced columns are not covered by a unique index — the
check Postgres performs that a schema-shape predicate cannot.

`IF NOT EXISTS` / `IF EXISTS` make the corresponding statement a no-op rather
than an error, which is what a re-runnable migration depends on.

### `NOT VALID` round-trips

`ADD CONSTRAINT … NOT VALID` leaves `convalidated := false`; `VALIDATE
CONSTRAINT` flips it. That is the sequence an online migration is built from, and
it is now expressible end to end: `pgast` emits it, `pgcatalog` models it,
`step` transitions it.

### Unmodelled statements ERROR

`setDefault`, `setColumnType`, `renameTable`, `setSchema` and most `DROP` kinds
return `.unsupported` rather than succeeding quietly. A migration "proved"
against a transition that silently ignored half its statements would be worse
than no proof.

### `Fold` is untouched

It keeps its byte-equivalence claim over a 1,384-statement production schema, and
deliberately keeps the quirks `step` rejects. Where the two disagree on a schema
both accept, that is a **finding to triage** — quite possibly a real defect in
the schema — not a bug in either.

15 pins in `Pg/Migrate/StepTest.lean`; 3/3 targets pass.

## 17.6.0 — the migration layer, opened

`Pg.Catalog.Fold` extracted from `tomato-bazel/rules_postgres` with
`git filter-repo`, history preserved (8 commits), and **moved** to
`Pg/Migrate/Fold.lean`.

**Why it moved, twice over.** It is the only module in the catalog family that
reaches outside `Pg.Catalog` — it imports `Pg.Query.Top` — so it cannot live in
`@pgcatalog` without dragging the parse tree in. And it could not keep its old
*path* here either: `@pgcatalog` publishes oleans rooted at `Pg/Catalog/`, so a
second archive claiming that root would overlap on unpack.

**The namespace did not move.** `namespace Pg.Catalog` inside the file is
unchanged. Module path and namespace are independent in Lean, so
`Snapshot.ofTopParseResult` and friends resolve exactly as before for anyone with
`open Pg.Catalog` — only the import line changes. Renaming the namespace is a
separate, later decision; doing both at once would churn call sites for no gain.
`Fold.lean` itself is byte-identical.

**`Fold` is total, and must stay that way.** It deliberately reproduces the quirks
of a C tool it replaced — `resolveType` falling back to 2249, `resolveBareColumn`
ignoring the FROM map, `foldAlterTable` silently skipping a missing table — and
carries a byte-equivalence claim against that tool over a 1,384-statement
production schema. It is not to be "fixed". The validating transition function
(`step`, with real preconditions and an error type) gets written **beside** it, and
the disagreements between the two are findings to triage rather than bugs in
either.

**Sits at the top of the graph**, depending on both `@pgcatalog` (for `Snapshot`)
and `@pgquery` (for `Query.Top`, and for the generated `SmokeFixtureTyped` that the
pipeline test folds). CI exercises the decoder and the fold together rather than
either alone.

### What comes next here

This module is where the provable-migration work lands: statement closure over
mutating DDL, top-level DML, a catalog transition that can *fail*, the `Migration`
object and its headline theorem, hazard and lock analysis, and backfill
correctness. Today it holds `Fold` and nothing else.

Requires `rules_lean` 0.6.1 — earlier releases' `lean_olean_archive` fails on linux.
