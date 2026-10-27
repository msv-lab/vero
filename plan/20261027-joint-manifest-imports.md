# Resolve joint-check imports from the manifest

Joint checks currently compose imports from the root package and module name. This fails for nested layouts such as Flocq/Core/Spec/FLT.lean and for modules in another package.

Reuse the existing proof materializer path resolver. Preserve the selected specifications, proof bodies, grading rules and flat-layout fallback. Add regression coverage over every real benchmark specification module and a two-package fixture. Run focused generation/evaluation tests and formatting checks. No benchmark edits, model calls, publishing or changes to Alaya PR #81 are included.

## Validation

- The new tests fail on the original code: 28 failures and 144 passes, including 27 real nested specification modules and the multi-package fixture.
- After the fix, the joint-check and proof-materialization tests pass: 183 tests.
- Ruff check, Ruff format check and git diff --check pass for the changed files.
- This validates rendered imports and materialization; it does not claim a full Mathlib compilation or an experiment rerun.
