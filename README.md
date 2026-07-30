# pgmigrate

**Postgres schema migrations, in Lean 4 — the layer where "provable migration"
gets built.**

Today this holds one thing: `Fold`, the DDL→catalog projection. The rest of the
module is the work it exists for.

Part of [leangres](https://github.com/leangres). It sits at the top of the
dependency graph.

## Why this module exists

A schema migration is a *state transition*, and almost nothing about one is
checked before it runs. Current tooling can tell you the SQL parses and, with
luck, that it ran once against a staging database. It cannot tell you:

- every statement's **preconditions hold** in the state the previous statement
  left behind;
- the end state is **exactly** the schema you intended, not merely one that did
  not error;
- the migration never holds `ACCESS EXCLUSIVE` **while it scans** a large table;
- a backfill **establishes the invariant** the next statement assumes;
- nothing else — a view, an RLS policy, a PL/pgSQL body — **referred to the column
  you just dropped**. Postgres does not dependency-track PL/pgSQL bodies, so this
  one is silently broken until something calls it at runtime.

Each is decidable given a faithful catalog model and a typed AST. leangres has
both, in [`pgcatalog`](https://github.com/leangres/pgcatalog) and
[`pgast`](https://github.com/leangres/pgast).

## `Fold` — and why it must not be "fixed"

`Pg.Migrate.Fold` folds a parsed DDL stream into a `Pg.Catalog.Snapshot`. It is
**total**, and it deliberately reproduces the quirks of a C tool it replaced:
`resolveType` falling back to `2249`, `resolveBareColumn` ignoring the FROM map,
`foldAlterTable` silently skipping a missing table, columns with unresolvable types
being dropped.

It carries a **byte-equivalence claim against that tool over a 1,384-statement
production schema** — which is why the C was deleted. Correcting the quirks would
void the claim.

So the validating transition function is written **beside** it, not over it:

```lean
step : Snapshot → Stmt → Except CatalogError Snapshot
```

with real preconditions and a typed error taxonomy. Where `step` and `Fold`
disagree on a schema both accept, that disagreement is a **finding to triage** —
several will be real defects in the production schema — not a bug in either. Expect
the agreement theorem to fail on first run; that is the point of writing it.

## Why `Fold` lives here and not in pgcatalog

Two independent reasons:

1. It is the only module in the catalog family that reaches outside `Pg.Catalog` —
   it imports `Pg.Query.Top`. Keeping it in `pgcatalog` would drag the parse tree
   into a module whose whole value is being dep-free.
2. It could not keep its old *path* either. `pgcatalog` publishes oleans rooted at
   `Pg/Catalog/`, so a second archive claiming that root would overlap on unpack.
   Hence `Pg/Migrate/Fold.lean`.

**The namespace is unchanged.** `namespace Pg.Catalog` inside the file stays, because
module path and namespace are independent in Lean: `Snapshot.ofTopParseResult` and
friends resolve exactly as before for anyone with `open Pg.Catalog`, and only the
import line moves. Renaming the namespace too is a separate decision.

## The roadmap this module is for

Roughly in dependency order, each step useful before the next:

1. **Statement closure over mutating DDL** — the full `ALTER TABLE` action set, the
   `DROP` family with `CASCADE`/`RESTRICT`, renames, `ALTER TYPE … ADD VALUE`.
   Lands in `pgast`.
2. **Top-level DML** — `INSERT`/`UPDATE`/`DELETE`/`MERGE`/`SELECT` as statements
   rather than fragments inside PL/pgSQL bodies. Also `pgast`.
3. **A catalog transition that can fail** — `step`, above. Needs the catalog kernel
   extended with `pg_constraint`, `pg_index` and `pg_depend`: without those there is
   no `DROP … RESTRICT`, no `NOT VALID`/`VALIDATE`, and no FK invariant preservation.
4. **`Migration` and its theorem** — a migration carries its intended start and end
   catalogs; the obligation is that running it from the first yields exactly the
   second. Decidable, because schemas are concrete data.
5. **Safety beyond well-formedness** — hazard classification, lock-level analysis
   against Postgres's real lock table, reversibility (where `none` is the useful
   answer), invariant preservation.
6. **Backfill correctness** — the step that needs a semantics for *data*, not just
   the catalog.

### One correction worth recording up front

The canonical safe pattern is usually written as three statements — add nullable
column, backfill, `SET NOT NULL`. **That is wrong twice over:** the third statement
takes `ACCESS EXCLUSIVE` *and* scans the table, and a concurrent `INSERT` between
the second and third leaves a NULL that makes the third fail.

The correct form is six statements, with `ADD CONSTRAINT … CHECK … NOT VALID`
**before** the backfill — Postgres enforces `NOT VALID` constraints on new and
updated rows immediately, which is what closes the race, while validating
separately keeps the scan off the exclusive lock. Both facts are decidable
consequences of the model rather than folklore, and demonstrating that is one of
the clearest arguments for this layer existing.

## Dependencies

`pgcatalog` (for `Snapshot`) and `pgquery` (for `Query.Top`, and for the generated
`SmokeFixtureTyped` that the pipeline test folds) — both as compiled oleans. Lean
core otherwise: no mathlib, no batteries. Proofs here lean on `native_decide` over
concrete data, which needs neither.

## Consuming it

```python
bazel_dep(name = "pgmigrate", version = "17.6.0")
```

## Versioning

`<pg_major>.<pg_minor>.<patch>`. ⚠ A convention, not enforced —
`compatibility_level` would have been the mechanism and Bazel 9 made it a no-op.
See [pgcatalog](https://github.com/leangres/pgcatalog)'s `MODULE.bazel`.

## Provenance

Carved from
[`tomato-bazel/rules_postgres`](https://github.com/tomato-bazel/rules_postgres)
with `git filter-repo`, history preserved.

## License

MIT.
