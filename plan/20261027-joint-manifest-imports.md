# Resolve joint-check imports from the manifest

Joint checks compose imports from the root package and module name, breaking nested layouts and modules in another package. Reuse the existing proof materializer resolver; preserve specifications, proof bodies and grading rules.

Keep four focused import-rendering cases: Flocq, Json, flat-layout fallback, and same-named modules in different packages. Keep the equivalent list.extend cleanup. No benchmark or Alaya changes.

## Validation

- The initial full-corpus probe found 27 real nested-module failures and a multi-package failure on the original code; the initial fixed suite passed 183 tests. These are historical results, not the size of the narrowed suite.
- The narrowed cases give 3 failures and 1 pass on the original renderer (flat fallback remains compatible). With the fix, all 20 joint/proof-materialization tests pass; changed-file Ruff, formatting and git diff --check pass.
- Validation covers generated imports and materialization, not a full Mathlib build or an experiment rerun.
