# Changelog

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
