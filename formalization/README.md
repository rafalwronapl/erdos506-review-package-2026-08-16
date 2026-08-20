# Erdős #506 Lean formalization

This is the isolated Lean 4 project for the V1, V3, and V4 statements. It is
pinned to Lean/mathlib 4.30.0.

## Exact status

- **The exact Formal Conjectures-style endpoint is build-verified.**
  `Erdos506.erdos_506` proves `IsLeast` for the official `Finset` predicate,
  with answer `Erdos506.v1Target n`. `Erdos506/Canonical.lean` proves the
  equivalence between the official set-based `numCircles` and the internal
  `circleCount`.
- **V1 sharpness is now formalized.** Explicit exact constructions cover
  `n=6,7,8`; the paired circle-and-centre family covers all remaining
  theorem-domain values.
- **The V1 source endpoint is parameter-free and build-verified.**
  `Erdos506.V1.circleCount_ge_v1Target` covers every admissible `n>=4` and
  now accepts only `cfg`, `Admissible cfg`, and `4 <= Fintype.card alpha`.
  The former real-plane principle structures, including Langer, are
  constructed internally. The final Langer-free closing layer and public
  target build pass.
- **The V3 source endpoint is parameter-free and build-verified.** Its lower bound constructs
  `RealPlaneMelchiorPrinciple` from the projective-arrangement cellulation,
  while its sharp constructions remain unconditional.
- **V4 is unconditional and complete** inside its frozen model, including
  lower bound, equality classification, and extremal construction.

The public root imports `Canonical`, `V1.Main`, `V3.Fano`, `V3.Main`, and `V4.Main` (with
selected intermediate/front modules retained for audit visibility).

## Public V1 endpoints

```text
n=9:  circleCount_ge_twenty_five_of_card_nine
n=10: circleCount_ge_thirty_three_of_card_ten
n=11: circleCount_ge_forty_one_of_card_eleven
n=12: circleCount_ge_fifty_one_of_card_twelve
n=13: circleCount_ge_sixty_one_of_card_thirteen
all n>=4: circleCount_ge_v1Target
exact minimum: Erdos506.erdos_506
```

The global theorem has no principle, callback, or circle-count hypothesis.
Its public arguments are the configuration, admissibility, and the lower
cardinality bound only.

The reusable ten-point theorem still exposes
`RealPlaneSixCircleU17Principle`; `V1.Main` derives that value from
`Events.toSixCircleU17` rather than asking for a redundant public-master
parameter.

Several fields are sharp local terminal inputs: they provide an overload or
block collision, coordinate/link data subsequently proved unrealizable, or a
named grid/gallery exclusion. Therefore “callback-free” is a statement about
the aggregate theorem's signature, not a claim that these geometric facts
have already been derived from foundations.

## Main module groups

- `V1/Carrier.lean`, `V1/BlockRows.lean`, `Block/RelativeRows.lean` — block
  semantics and exact finite rows;
- `V1/PivotGeometry.lean`, `V1/RestoredPivot.lean` — inversion dictionaries;
- `V1/LangerRow.lean`, `V1/UniversalRows.lean`, `V1/RichBlockPencil.lean`,
  `V1/HalfCap.lean`, `V1/LargeMaster.lean` — universal and `n>=15` proof;
- `V1/Nine*.lean` — complete nine-point endpoint;
- `V1/Ten*.lean`, `V1/Deletion.lean` — local tables, deletion transfer, and
  complete ten-point endpoint;
- `V1/ElevenGammaSix.lean`, `V1/ElevenFive.lean`, `V1/Eleven.lean` — both
  eleven-point branches and router;
- `V1/TwelveGeometry.lean`, `V1/TwelveFive.lean`, `V1/TwelveSix*.lean`,
  `V1/Twelve.lean` — explicit local interfaces and both twelve-point branches;
- `Incidence/SixConicEventsPrinciple.lean`, `V1/ThirteenSix*.lean`,
  `V1/ThirteenFull.lean` — six-conic calculus and thirteen-point endpoint;
- `V1/Main.lean` — callback-free public V1 assembly;
- `V3/Main.lean`, `V4/Main.lean` — public variant endpoints.

## Trust and computation boundary

The previously published axiom report covered the older conditional
snapshot. The current source constructs the real-plane structures internally;
the refreshed strict `#print axioms` report passes after the clean build.
The final chain contains no `sorry`, `admit`, or project-local `axiom`.

## Build and audit

```text
lake -Kjobs=1 build Erdos506.V1.Main
lake -Kjobs=1 build Erdos506.V1.Sharpness
lake -Kjobs=1 build Erdos506.Canonical
lake -Kjobs=1 build Erdos506
lake env lean -DwarningAsError=true AxiomsAudit.lean
```

The commands pass on the current source tree. This formalization directory is
the synchronized source included in the reviewer artifact and its 2026-08-20
distribution archive.
