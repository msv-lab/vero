# Impl slot schedule consistency

Target: `codex/slot-schedule-consistency`, based on `0a7325df9e9e6dbc275c0ad483b3d1cbe38d9b09`. Align trusted implementation-slot permissions and preserve definitions that the task provides.

## Problem and scope

The current schedule invents 128 imports/global_aux slots in 67 modules without APIs. Six of those modules do have imports slots, so dropping all no-API modules would remove existing edit permissions. Unicode also marks three provided predicates as editable implementations, and sortedcontainers marks two unregistered compatibility definitions. Codeproof blanks these five bodies but extraction rejects them as extras, so even a reference-answer round trip leaves sorry bodies.

## Plan

1. For modules without APIs, include only header slots actually present in the trusted benchmark source. Keep strict required headers and per-API slots for modules with APIs. Never derive the schedule from agent-edited files.
2. Freeze Unicode's three provided minimal-well-formedness predicates, including the five private predicates they depend on. Keep other implementation helpers in global_aux. Preserve Bundle fields, canonical wiring, Specs, and existential semantics.
3. Remove editable markers around the two unregistered sortedcontainers bisect-key compatibility definitions without changing their bodies.
4. Add regression coverage across all shipped benchmark Impl files, no-API header permissions, agent marker tampering, and real codeproof sandbox/render preservation and blanking. Reuse the existing sandbox/render test interfaces and disable dependency-cache downloads in these tests.
5. Update the relevant schema notes, TODO and WORKLOG, run focused tests and lint in an isolated environment, and record verification limits.

## Boundaries

No manifest API additions, scoring changes, Bundle/Spec edits, dependency downloads, model calls, or paid experiments. Lean compilation depends on already available toolchains/caches; Python regression tests alone are not Lean acceptance.

## Verification

Completed the implementation without changing manifest APIs, Bundle fields, or Specs. All 43 shipped benchmarks match their Impl schedule in both modes. The focused Python suite passes 126 tests. Existing Lean 4.29.1 compiled the four changed Impl modules after codeproof blanking; nine Unicode boundary examples and two sortedcontainers compatibility examples passed, and all five fixed definitions have only standard axioms. Ruff finds no new issue; FURB188 and PERF102 in unchanged extractor code also reproduce at the base commit.
