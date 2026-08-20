# Erdos 506 Reviewer Artifact

Refresh date: 2026-08-16. The Lean source and public audit in this package
were verified on 2026-08-15 with Lean 4.30.0 and the pinned mathlib 4.30.0
revision.

This is a compact package for technical and mathematical review. It contains
the current public Lean source, the V1 review manuscript, the V3/V4 proof
records, the corrected n=6 replay, and reproducibility instructions. It does
not contain the exploratory search workspace or generated Lean build caches.

## Current result

- V1 proves the lower bound for every admissible configuration with `n >= 4`.
  The public theorem `Erdos506.V1.circleCount_ge_v1Target` has no geometric
  principle parameter and no finite-case callback.
- V3 is the separate no-three-collinear variant, with the exceptional value
  `f_V3(8)=20` and the generic value `1 + binom(n-1,2)` otherwise.
- V4 is the separate no-four-concyclic variant, with value
  `binom(n-1,2)` and a near-pencil equality classification.
- The corrected V1 value is `f_V1(6)=8`, not `9`.

## Verification

The following commands passed on the source used for this package:

```text
lake -Kjobs=1 build Erdos506.V1.Main       # PASS, 8885 jobs
lake -Kjobs=1 build Erdos506                # PASS, 8888 jobs
lake env lean -DwarningAsError=true AxiomsAudit.lean  # PASS
```

The public theorem audit reports only the standard Lean axioms
`propext`, `Classical.choice`, and `Quot.sound`. The build has non-fatal
linter/deprecation warnings; it has no compilation errors.

This package is ready for review. It is not a publication, priority, or
claim-of-correctness certificate by itself. Independent mathematical review
and a final literature/priority audit remain necessary.

## Start here

- `STATUS.md` -- exact status and trust boundary;
- `REPRODUCE.md` -- Lean, manuscript, and checksum commands;
- `formalization/README.md` -- source layout and public endpoints;
- `audit/RESULTS.md` -- recorded verification results;
- `audit/AXIOMS.md` -- public theorem axiom audit;
- `paper/erdos506_v1_review_manuscript.pdf` -- review manuscript;
- `docs/ERDOS506_FORMALIZATION_AUDIT_2026-08-15.md` -- current Lean audit.
