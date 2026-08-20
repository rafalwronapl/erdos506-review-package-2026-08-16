# Verification Results

Verification date: 2026-08-15 for Lean; 2026-08-16 for the package refresh.
Environment: Windows/PowerShell, Lean 4.30.0, pinned mathlib 4.30.0.

## Lean

```text
lake -Kjobs=1 build Erdos506.V1.Main
Build completed successfully (8885 jobs).

lake -Kjobs=1 build Erdos506
Build completed successfully (8888 jobs).

lake env lean -DwarningAsError=true AxiomsAudit.lean
PASS
```

The ordinary builds print non-fatal linter/deprecation warnings but no errors.
The public axiom audit reports only `propext`, `Classical.choice`, and
`Quot.sound`.

## Manuscript

The current paper checks pass:

```text
PASS_CANONICAL_MANUSCRIPT_STATIC_INTEGRITY files=5 labels=359 refs=279 citations=11 supplements=1 claims=81 proofs=75
PASS_NO_MISSING_INPUT_REFERENCE_OR_CITATION
PASS_NO_RESEARCH_PATH_OR_OBSOLETE_DELETION_ARCHITECTURE
PASS_REVIEW_SIMPLIFICATION_IDENTITIES_NO_SEARCH
PASS_N16_M4_M5_M6_COMMON_ROW_AND_SIGNATURE_BOUNDS_NO_SEARCH
PASS_SYMBOLIC_N13_GAMMA5_ADDED_CENTER_GLOBAL_CLOSURE
```

## Python

The latest complete project regression recorded before the final Lean-only
extension is:

```text
754 passed, 1 skipped
```

The compact corrected n=6 replay is included separately. Python checks are
secondary software/arithmetic controls and are not used as substitutes for
the kernel-checked Lean theorems.

## Scope

The package was synchronized from the current source and deliberately excludes
`.lake`, generated Lean objects, compilation logs, scratch searches, solver
proof debris, and unrelated historical experiments.
