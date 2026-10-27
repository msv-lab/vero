# Resolve joint-check imports from the manifest

Joint checks compose imports from the root package and module name, breaking nested layouts and modules in another package. Reuse the existing proof materializer resolver; preserve specifications, proof bodies and grading rules.

Keep two focused import-rendering cases: the Flocq regression and flat-layout fallback compatibility. Keep the equivalent list.extend cleanup. No benchmark or Alaya changes.

## Validation

- The initial full-corpus probe found 27 real nested-module failures and a multi-package failure on the original code; the initial fixed suite passed 183 tests. These are historical results, not the size of the narrowed suite.
- The retained cases give 1 failure (Flocq) and 1 pass (flat fallback) on the original renderer. With the fix, all 18 joint/proof-materialization tests pass; changed-file Ruff, formatting and git diff --check pass.
- Validation covers generated imports and materialization, not a full Mathlib build or an experiment rerun.
