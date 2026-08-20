# Exact Status and Trust Boundary

## Exact canonical V1 theorem

The current top-level endpoint is:

```lean
Erdos506.erdos_506 (n : Nat) (hn : 4 <= n) :
  IsLeast {k : Nat | exists P : Finset Point2,
    P.card = n /\ not Collinear Real (P : Set Point2) /\
    not Cospherical (P : Set Point2) /\
    numCircles (P : Set Point2) = k}
  (v1Target n)
```

This matches the mathematical predicate in the Formal Conjectures statement.
`Canonical.lean` proves the bridge
`numCircles (pointSet cfg) = circleCount cfg`, so the endpoint does not merely
reuse the internal count without justification.

## V1 lower-bound theorem

The current public endpoint is:

```lean
Erdos506.V1.circleCount_ge_v1Target
    (cfg : Configuration alpha)
    (hadm : Admissible cfg)
    (hcard : 4 <= Fintype.card alpha)
```

The theorem constructs the real-plane incidence inputs used by the assembly
internally. Its public signature contains no Melchior, Langer, Kelly--Moser,
finite-window, selected-circle, or endpoint-callback parameter.

The finite endpoints exposed by the source include:

| `n` | lower-bound target |
| ---: | ---: |
| 4 | 3 |
| 5 | 5 |
| 6 | 8 |
| 7 | 11 |
| 8 | 17 |
| 9 | 25 |
| 10 | 33 |
| 11 | 41 |
| 12 | 51 |
| 13 | 61 |
| 14 | 73 |

For `n >= 9`, the V1 target is

```text
1 + binom(n-1, 2) - floor((n-1)/2).
```

The uniform proof uses the finite window `14 <= n <= 22` and a cap-sensitive
tail for `n >= 23`. The last recorded finite residual is the `(15,6)`
rich-line endpoint in `V1/LangerApplicationFifteenLineSixFinish.lean`.

## Separate variants

V3 forbids every collinear triple and has `f_V3(8)=20`, with
`1 + binom(n-1,2)` for the other theorem-domain values. V4 forbids four points
on one proper circle and has value `binom(n-1,2)`, including a near-pencil
equality classification. These variants are separate statements and do not
reuse V1 values as if their hypotheses were identical.

## Verification status

The following commands passed on the current source:

```text
lake -Kjobs=1 build Erdos506.V1.Main       # PASS, 8885 jobs
lake -Kjobs=1 build Erdos506.V1.Sharpness  # PASS, 8892 jobs
lake -Kjobs=1 build Erdos506.Canonical     # PASS, 8893 jobs
lake -Kjobs=1 build Erdos506               # PASS, 8896 jobs
lake env lean -DwarningAsError=true AxiomsAudit.lean  # PASS
```

The audited public declarations depend only on `propext`, `Classical.choice`,
and `Quot.sound`. The production source contains no `sorry`, `admit`, project-
local `axiom`, or `unsafe` declaration in the audited chain. The build emits
non-fatal linter and deprecation warnings which do not prevent verification.

One retained finite helper, `Finite/UngarSixEvenAllowable.lean`, contains
three `native_decide` checks. It is not imported by the current public root and
none of its declarations appears in `AxiomsAudit.lean`; it is included for
source transparency rather than as a dependency of the public endpoints.

The manuscript-facing checks run on the current paper package are:

```text
PASS_CANONICAL_MANUSCRIPT_STATIC_INTEGRITY
PASS_NO_MISSING_INPUT_REFERENCE_OR_CITATION
PASS_NO_RESEARCH_PATH_OR_OBSOLETE_DELETION_ARCHITECTURE
PASS_REVIEW_SIMPLIFICATION_IDENTITIES_NO_SEARCH
PASS_SYMBOLIC_N13_GAMMA5_ADDED_CENTER_GLOBAL_CLOSURE
```

The last complete Python project regression recorded before the final Lean-only
extension was `754 passed, 1 skipped`. It is a software and document check,
not a replacement for the Lean proof.

## Remaining review boundary

- The result still needs independent mathematical review.
- The literature and priority audit is not a proof of priority; MathSciNet,
  zbMATH, citation chains, and the Erdős Problems maintainers should be
  checked before any priority claim.
- The paper must state the V1 convention explicitly: distinct points, not all
  collinear, not all concyclic, and distinct proper circles through
  non-collinear selected triples counted once.
