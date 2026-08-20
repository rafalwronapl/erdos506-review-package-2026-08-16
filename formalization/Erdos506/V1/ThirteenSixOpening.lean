import Mathlib.Tactic

/-!
# Arithmetic opening of the thirteen-point six-circle branch

This file isolates the solver-free integer arithmetic in the opening lemma
of the paper's `n = 13`, selected-six-circle branch.  It deliberately does
not claim the geometric endpoint.  The variables have the following paper
meanings:

* `C` is the number of proper circles;
* `D` is the global restored-centre defect row;
* `O = 3 C₃` is ordinary-circle incidence;
* `MX` is the pivot moment on the seven points outside the selected circle;
* `W` is the outside-pair weight;
* `R` is the sum of the nonnegative opening residuals;
* `f = c(2,3)` is the zero-residual circle multiplicity.

The four nontrivial hypotheses are named after their exact roles in the
paper.  A future geometric wrapper must derive them coefficientwise from
the block system, Melchior and Lenchner.  In particular, none of them is a
hidden six-conic-events principle and this module does not close the
six-circle branch.
-/

namespace Erdos506.V1

/-- The exact scalar rows used by the opening certificate.

`openingDual` is equation `123 D >= 33810 - 414 W`.  At the sole integral
wall `W = 47`, `retainedBudget` is the retained-slack inequality from the
same coefficientwise calculation.  `residualGap` records that a positive
local residual is at least `96`, hence so is their sum.  Finally,
`zeroLayer` is the summed identity
`M_X + 123 c(2,3) = 240` after all residuals vanish. -/
def ThirteenSixOpeningConditions
    (C D O MX W R f : Nat) : Prop :=
  C <= 60 /\
  D <= 117 /\
  39 <= O /\
  21 <= MX /\
  (33810 : Int) - 414 * (W : Int) <= 123 * (D : Int) /\
  (W = 47 ->
    R + 79 * (O - 39) + 199 * (MX - 21) + 1344 * (60 - C) <= 39) /\
  (R = 0 \/ 96 <= R) /\
  (R = 0 -> MX + 123 * f = 240)

/-- The opening dual and `D <= 117` already force the preliminary integral
bound `W >= 47`. -/
theorem thirteen_six_opening_dual_ge_forty_seven
    {D W : Nat} (hD : D <= 117)
    (hdual : (33810 : Int) - 414 * (W : Int) <= 123 * (D : Int)) :
    47 <= W := by
  omega

/-- At `W = 47`, the retained budget and the residual gap force every
opening residual to vanish and make all three global lower bounds sharp. -/
theorem thirteen_six_opening_wall_sharp
    {C O MX R : Nat}
    (hC : C <= 60) (hO : 39 <= O) (hMX : 21 <= MX)
    (hbudget :
      R + 79 * (O - 39) + 199 * (MX - 21) + 1344 * (60 - C) <= 39)
    (hgap : R = 0 \/ 96 <= R) :
    R = 0 /\ O = 39 /\ MX = 21 /\ C = 60 := by
  rcases hgap with hzero | hlarge
  · constructor
    · exact hzero
    omega
  · omega

/-- The zero-residual layer cannot occur at the integral wall `W = 47`:
sharpness gives `M_X = 21`, while the exact zero-layer identity would give
`21 + 123 c(2,3) = 240`. -/
theorem thirteen_six_opening_zero_layer_impossible
    {MX f : Nat} (hMX : MX = 21)
    (hzeroLayer : MX + 123 * f = 240) : False := by
  omega

/-- Solver-free arithmetic conclusion of the thirteen-point opening
certificate: the outside-pair weight satisfies `W >= 48`.

This theorem consumes only the named scalar rows above.  It is intended as
the checked target for a later configuration-level Melchior--Lenchner
wrapper, not as that wrapper itself. -/
theorem thirteen_six_opening_weight_ge_forty_eight
    {C D O MX W R f : Nat}
    (hs : ThirteenSixOpeningConditions C D O MX W R f) :
    48 <= W := by
  rcases hs with
    ⟨hC, hD, hO, hMX, hdual, hretained, hgap, hzeroLayer⟩
  have hW47 : 47 <= W :=
    thirteen_six_opening_dual_ge_forty_seven hD hdual
  by_contra hnot
  have hWeq : W = 47 := by omega
  have hbudget := hretained hWeq
  obtain ⟨hR, _hOeq, hMXeq, _hCeq⟩ :=
    thirteen_six_opening_wall_sharp hC hO hMX hbudget hgap
  exact thirteen_six_opening_zero_layer_impossible hMXeq (hzeroLayer hR)

end Erdos506.V1
