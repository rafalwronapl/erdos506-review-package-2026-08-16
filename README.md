# Erdos 506 Reviewer Artifact

Refresh date: 2026-08-20. The Lean source and public audit in this package
were verified on 2026-08-20 with Lean 4.30.0 and the pinned mathlib 4.30.0
revision.

This is a compact package for technical and mathematical review. It contains
the current public Lean source, the V1 review manuscript, the V3/V4 proof
records, the corrected n=6 replay, and reproducibility instructions. It does
not contain the exploratory search workspace or generated Lean build caches.

## Current result

- V1 now proves the exact minimum for every `n >= 4`. The endpoint
  `Erdos506.erdos_506` is an `IsLeast` theorem over the same `Finset`,
  `Collinear`, `Cospherical`, and set-based `numCircles` formulation used by
  `FormalConjectures/ErdosProblems/506.lean`.
- The lower-bound theorem `Erdos506.V1.circleCount_ge_v1Target` remains
  available with no geometric-principle parameter or finite-case callback.
- Sharpness is kernel-checked: explicit constructions cover `n=6,7,8`, and a
  paired circle-and-centre family covers every remaining theorem-domain `n`.
- V3 is the separate no-three-collinear variant, with the exceptional value
  `f_V3(8)=20` and the generic value `1 + binom(n-1,2)` otherwise.
- V4 is the separate no-four-concyclic variant, with value
  `binom(n-1,2)` and a near-pencil equality classification.
- The corrected V1 value is `f_V1(6)=8`, not `9`.

## Verification

The following commands passed on the source used for this package:

```text
lake -Kjobs=1 build Erdos506.V1.Main       # PASS, 8885 jobs
lake -Kjobs=1 build Erdos506.V1.Sharpness  # PASS, 8892 jobs
lake -Kjobs=1 build Erdos506.Canonical     # PASS, 8893 jobs
lake -Kjobs=1 build Erdos506               # PASS, 8896 jobs
lake env lean -DwarningAsError=true AxiomsAudit.lean  # PASS
```

The public theorem audit reports only the standard Lean axioms
`propext`, `Classical.choice`, and `Quot.sound`. The build has non-fatal
linter/deprecation warnings; it has no compilation errors.

This package is ready for review. It is not a publication, priority, or
claim-of-correctness certificate by itself. Independent mathematical review
and a final literature/priority audit remain necessary.

## AI assistance and review status

This artifact was developed with substantial AI assistance, including
mathematical exploration, manuscript drafting, preparation of exact-arithmetic
checking scripts, and Lean formalization. AI assistance is not treated as a
certificate of mathematical correctness. The Lean kernel checks the formal
claims within their stated trust boundary, but it does not by itself establish
that the formal statements exactly match the intended interpretation of
Erdos Problem 506 or that every informal argument in the manuscript is
correct. The package is therefore being submitted for independent human
mathematical and formal review.

## Start here

- `STATUS.md` -- exact status and trust boundary;
- `REPRODUCE.md` -- Lean, manuscript, and checksum commands;
- `formalization/README.md` -- source layout and public endpoints;
- `docs/ERDOS506_CANONICAL_ENDPOINT_2026-08-20.md` -- exact `IsLeast` bridge and sharpness audit;
- `audit/RESULTS.md` -- recorded verification results;
- `audit/AXIOMS.md` -- public theorem axiom audit;
- `paper/erdos506_v1_review_manuscript.pdf` -- review manuscript;
- `docs/ERDOS506_FORMALIZATION_AUDIT_2026-08-15.md` -- current Lean audit.
