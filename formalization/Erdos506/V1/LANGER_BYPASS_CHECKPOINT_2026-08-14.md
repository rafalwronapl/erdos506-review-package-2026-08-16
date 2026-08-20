# Langer bypass checkpoint — 2026-08-14

> **Superseded on 2026-08-15.** All residual branches listed below have now
> been closed and `V1/Main.lean` no longer takes a Langer parameter. The
> current status is recorded in
> `docs/SESSION_CHECKPOINT_2026-08-15_V1_ZERO_PARAMETERS.md`. The closing
> layer has been audited statically but has not yet been compiled.

All statements in this checkpoint were inspected statically only.  No Lean,
`lake`, Python, solver, or build was run.

## Public API status

`V1/Main.lean` currently has one public geometric parameter left:
`Lan : RealPlaneLangerPrinciple`.  Melchior, even-arrangement, guarded
Kelly--Moser, and all former finite geometry callbacks are constructed
locally.

The Langer-free tail `n >= 23` and the finite hard core `n <= 13` are already
available.  In the finite window, every case with `n >= 16` is discharged.

## Newly closed cases

- `V1/LangerApplicationFifteenSevenCircleFinish.lean`
  - `FiniteWindowRichBlockResidual.circle_impossible_of_fifteen_seven`
- `V1/LangerApplicationFifteenSixCircleFinish.lean`
  - `FiniteWindowRichBlockResidual.circle_impossible_of_fifteen_six`
- `V1/LangerApplicationSixteenSevenCircleFinish.lean`
  - `FiniteWindowRichBlockResidual.circle_impossible_of_sixteen_seven`
- `V1/LangerApplicationSeventeenEightCircleFinish.lean`
  - `FiniteWindowRichBlockResidual.circle_impossible_of_seventeen_eight`
- `V1/LangerApplicationEighteenEightCircleFinish.lean`
  - `FiniteWindowRichBlockResidual.circle_impossible_of_eighteen_eight`

Together with the previously completed line/circle endpoints, this leaves
only three branches: `(15,6)` line, `(14,6)` line, and `(14,6)` circle.

## Saved residual checkpoints

### `(15,6)` line

File: `V1/LangerApplicationFifteenLineSixFinish.lean`.

Saved public facts:

- `sixConic_markedLineAt_card_le_three`;
- `sixConic_line_incidence_le_twenty_of_card_eight`;
- `fifteenSixLine_partition_arithmetic`.

The arithmetic endpoint gives `C >= 87 > 84` after a lossless inversion
adapter identifies the selected six-line fan fibres with
`SixConicMarkedLineAt`.  That adapter is the sole remaining seam in this
branch.

### `(14,6)` circle

File: `V1/LangerApplicationFourteenSixCircleFunctional.lean`.

Saved public facts:

- `FourteenSixCircleResidualData.fourteenWeight_ge_seventy_six`;
- `FourteenSixCircleResidualData.functional_extreme_residual`.

The branch is reduced to the exact range `76 <= W <= 79` together with
`J <= 22`.  The remaining task is a coupled six-conic weight/line-footprint
exclusion for these four weights.

### `(14,6)` line

File: `V1/LangerApplicationFourteenSixLineFinish.lean`.

Saved public facts:

- `fourteenSixLine_twoInside_oneOutside_row` (`P2 = 120`);
- `sum_fourteenSixLineBlockFunctional_eq`;
- `sum_fourteenSixLineBlockFunctional_le`;
- `fourteenSixLine_weight_ge_seventy_six`;
- `fourteenSixLine_weight_interval` (`76 <= W <= 84`).

The remaining task is the labelled/off-pencil exclusion of these nine
weight layers, preferably by producing an actual six-circle and routing to
the preceding circle residual.

## Resume order

1. Finish the `(15,6)` inversion/fibre adapter; this should immediately
   close the entire `n = 15` row.
2. Prove the coupled `W/J` exclusion for the `(14,6)` selected circle.
3. Reduce the `(14,6)` selected line to that circle endpoint, or close its
   `W = 76..84` layers directly.
4. Add the finite-window router, switch `Main` to the Langer-free assembly,
   and remove the final public `Lan` parameter.
