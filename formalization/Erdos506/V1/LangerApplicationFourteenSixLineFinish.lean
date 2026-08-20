import Erdos506.V1.LangerApplicationFourteenSixResidual

/-!
# The selected six-line checkpoint at fourteen points

For a selected six-line the six-block cap removes the outsider-triple
correction from the fourteen-point functional table.  The resulting honest
certificate forces the two-inside circle weight into the narrow interval
`76 .. 84`.  The final labelled/off-pencil exclusion is deliberately not
asserted here.
-/

namespace Erdos506.V1

open Erdos506.Block
open Erdos506.Block.BlockSystem
open Erdos506.Incidence
open Erdos506.V4
open scoped BigOperators

universe u v

section RelativeCertificate

variable {Point : Type u} {Block : Type v}
  [Fintype Point] [Fintype Block] [DecidableEq Point]

private theorem fourteenSixLine_line_functional_bound (g x : Nat)
    (hg : g ≤ 2) (hmin : 3 ≤ g + x) (hcap : g + x ≤ 6) :
    fourteenBlockFunctional .line g x ≤
      4 * fourteenBlockDefect .line g x := by
  have hx : x ≤ 6 := by omega
  interval_cases g <;> interval_cases x <;>
    simp [fourteenBlockFunctional, fourteenBlockDefect, Nat.choose] at *

private theorem fourteenSixLine_circle_functional_bound (g x : Nat)
    (hg : g ≤ 2) (hmin : 3 ≤ g + x) (hcap : g + x ≤ 6) :
    fourteenBlockFunctional .circle g x ≤
      4 * fourteenBlockDefect .circle g x := by
  have hx : x ≤ 6 := by omega
  interval_cases g <;> interval_cases x <;>
    simp [fourteenBlockFunctional, fourteenBlockDefect, Nat.choose] at *

private theorem fourteenSixLine_selected_functional_bound :
    fourteenBlockFunctional .line 6 0 ≤
      4 * fourteenBlockDefect .line 6 0 := by
  simp [fourteenBlockFunctional, fourteenBlockDefect, Nat.choose]

/-- The `P₂` relative row.  Since a distinct line cannot contain two
selected labels, all 120 units must ultimately be carried by circles; this
is the lossless input for the remaining off-pencil argument. -/
theorem fourteenSixLine_twoInside_oneOutside_row
    (S : BlockSystem Point Block) (D : Finset Point)
    (hpoint : Fintype.card Point = 14) (hD : D.card = 6) :
    (∑ b : Block,
      (Nat.choose (fourteenInside S D b) 2 : Int) *
        (fourteenOutside S D b : Int)) = 120 :=
  (fourteenSix_relative_rows S D hpoint hD).2.2.1

/-- Exact expansion of the selected-line functional at the `6+8` split. -/
theorem sum_fourteenSixLineBlockFunctional_eq
    (S : BlockSystem Point Block) (D : Finset Point)
    (hpoint : Fintype.card Point = 14) (hD : D.card = 6) :
    (∑ b : Block,
      fourteenBlockFunctional (S.kind b)
        (fourteenInside S D b) (fourteenOutside S D b)) =
      3408 + 3 * S.subsetPivotMoment D +
        6 * S.subsetPivotMoment (Finset.univ \ D) -
        36 * (S.totalCircleCount : Int) -
        6 * (fourteenWeight S D : Int) := by
  classical
  obtain ⟨hrow0, hrow1, hrow2, hrow3⟩ :=
    fourteenSix_relative_rows S D hpoint hD
  have hmomentD :
      (∑ b : Block,
        if 3 ≤ fourteenInside S D b + fourteenOutside S D b then
          (fourteenInside S D b : Int) *
            (4 - ((fourteenInside S D b +
              fourteenOutside S D b : Nat) : Int))
        else 0) = S.subsetPivotMoment D := by
    rw [subsetPivotMoment]
    apply Fintype.sum_congr
    intro b
    rw [fourteenInside_add_fourteenOutside]
    rfl
  have hmomentX :
      (∑ b : Block,
        if 3 ≤ fourteenInside S D b + fourteenOutside S D b then
          (fourteenOutside S D b : Int) *
            (4 - ((fourteenInside S D b +
              fourteenOutside S D b : Nat) : Int))
        else 0) = S.subsetPivotMoment (Finset.univ \ D) := by
    rw [subsetPivotMoment]
    apply Fintype.sum_congr
    intro b
    rw [fourteenInside_add_fourteenOutside,
      fourteenOutside_eq_inside_compl]
    rfl
  have hcircle :
      (∑ b : Block,
        if S.kind b = .circle then (36 : Int) else 0) =
          36 * (S.totalCircleCount : Int) := by
    rw [← Finset.sum_filter]
    simp [BlockSystem.totalCircleCount, BlockSystem.blocksOfKind]
    ring
  have hweight :
      (∑ b : Block,
        if S.kind b = .circle ∧ fourteenInside S D b = 2 then
          (Nat.choose (fourteenOutside S D b) 2 : Int)
        else 0) = (fourteenWeight S D : Int) := by
    rw [fourteenWeight, Nat.cast_sum]
    simp [fourteenTwoTraceCircles, Finset.sum_filter]
  have hpointwise (b : Block) :
      fourteenBlockFunctional (S.kind b)
          (fourteenInside S D b) (fourteenOutside S D b) =
        6 * (Nat.choose (fourteenOutside S D b) 3 : Int) +
        9 * ((fourteenInside S D b : Int) *
          (Nat.choose (fourteenOutside S D b) 2 : Int)) +
        12 * ((Nat.choose (fourteenInside S D b) 2 : Int) *
          (fourteenOutside S D b : Int)) +
        6 * (Nat.choose (fourteenInside S D b) 3 : Int) +
        3 * (if 3 ≤ fourteenInside S D b + fourteenOutside S D b then
          (fourteenInside S D b : Int) *
            (4 - ((fourteenInside S D b +
              fourteenOutside S D b : Nat) : Int))
        else 0) +
        6 * (if 3 ≤ fourteenInside S D b + fourteenOutside S D b then
          (fourteenOutside S D b : Int) *
            (4 - ((fourteenInside S D b +
              fourteenOutside S D b : Nat) : Int))
        else 0) -
        (if S.kind b = .circle then 36 else 0) -
        6 * (if S.kind b = .circle ∧ fourteenInside S D b = 2 then
          (Nat.choose (fourteenOutside S D b) 2 : Int)
        else 0) := by
    by_cases hthree :
      3 ≤ fourteenInside S D b + fourteenOutside S D b
    · simp [fourteenBlockFunctional, hthree]
      ring
    · simp [fourteenBlockFunctional, hthree]
      ring
  simp_rw [hpointwise]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ← Finset.mul_sum]
  rw [hrow0, hrow1, hrow2, hrow3, hmomentD, hmomentX, hcircle,
    hweight]
  ring

/-- With a global six-block cap there is no outsider-triple correction:
the selected line and every other local cell are paid directly by defect. -/
theorem sum_fourteenSixLineBlockFunctional_le
    (S : BlockSystem Point Block) (D : Finset Point) (gamma : Block)
    (hD : D.card = 6)
    (hgammaKind : S.kind gamma = .line)
    (hgammaSupport : S.support gamma = D)
    (hcap : BlockSizeCap S 6) :
    (∑ b : Block,
      fourteenBlockFunctional (S.kind b)
        (fourteenInside S D b) (fourteenOutside S D b)) ≤
      4 * S.defectRow := by
  classical
  have hlocal (b : Block) :
      fourteenBlockFunctional (S.kind b)
          (fourteenInside S D b) (fourteenOutside S D b) ≤
        4 * S.blockDefectContribution b := by
    by_cases hbgamma : b = gamma
    · subst b
      have hg : fourteenInside S D gamma = 6 := by
        simp [fourteenInside, hgammaSupport, hD]
      have hx : fourteenOutside S D gamma = 0 := by
        simp [fourteenOutside, hgammaSupport]
      have hdefect :
          fourteenBlockDefect .line 6 0 =
            S.blockDefectContribution gamma := by
        simp [fourteenBlockDefect, BlockSystem.blockDefectContribution,
          hgammaKind, hgammaSupport, hD]
      rw [hgammaKind, hg, hx, ← hdefect]
      exact fourteenSixLine_selected_functional_bound
    · have hg : fourteenInside S D b ≤ 2 := by
        have hinter := S.distinct_block_inter_card_lt_three hbgamma
        rw [hgammaSupport] at hinter
        exact Nat.le_of_lt_succ hinter
      have hsum := fourteenInside_add_fourteenOutside S D b
      cases hkind : S.kind b with
      | circle =>
          have hmin :
              3 ≤ fourteenInside S D b + fourteenOutside S D b := by
            rw [hsum]
            exact S.circle_min b hkind
          have hsizeCap :
              fourteenInside S D b + fourteenOutside S D b ≤ 6 := by
            rw [hsum]
            exact hcap b (by simpa [hsum] using hmin)
          have hres := fourteenSixLine_circle_functional_bound
            (fourteenInside S D b) (fourteenOutside S D b)
            hg hmin hsizeCap
          simpa [fourteenBlockDefect,
            BlockSystem.blockDefectContribution, hkind, ← hsum] using hres
      | line =>
          by_cases hmin :
              3 ≤ fourteenInside S D b + fourteenOutside S D b
          · have hsizeCap :
                fourteenInside S D b + fourteenOutside S D b ≤ 6 := by
              rw [hsum]
              exact hcap b (by rw [← hsum]; exact hmin)
            have hres := fourteenSixLine_line_functional_bound
              (fourteenInside S D b) (fourteenOutside S D b)
              hg hmin hsizeCap
            simpa [fourteenBlockDefect,
              BlockSystem.blockDefectContribution, hkind, ← hsum] using hres
          · have hsmin : 2 ≤ (S.support b).card := S.line_min b hkind
            have htwo :
                fourteenInside S D b + fourteenOutside S D b = 2 := by
              rw [hsum]
              omega
            have hx : fourteenOutside S D b ≤ 2 := by omega
            simp only [BlockSystem.blockDefectContribution]
            rw [hkind, ← hsum]
            interval_cases fourteenInside S D b <;>
              interval_cases fourteenOutside S D b <;>
              norm_num [fourteenBlockFunctional, fourteenBlockDefect,
                Nat.choose] at * <;> omega
  calc
    (∑ b : Block,
        fourteenBlockFunctional (S.kind b)
          (fourteenInside S D b) (fourteenOutside S D b)) ≤
        ∑ b : Block, 4 * S.blockDefectContribution b := by
      exact Finset.sum_le_sum fun b _hb => hlocal b
    _ = 4 * S.defectRow := by
      rw [← Finset.mul_sum, S.defectRow_eq_sum_blockDefectContribution]

/-- The complete aggregate consequence of the selected-line functional. -/
theorem fourteenSixLine_weight_ge_seventy_six
    (S : BlockSystem Point Block) (D : Finset Point) (gamma : Block)
    (hpoint : Fintype.card Point = 14) (hD : D.card = 6)
    (hgammaKind : S.kind gamma = .line)
    (hgammaSupport : S.support gamma = D)
    (hcap : BlockSizeCap S 6)
    (hmomentD : 18 ≤ S.subsetPivotMoment D)
    (hmomentX : 24 ≤ S.subsetPivotMoment (Finset.univ \ D))
    (hdefect : S.defectRow ≤ 140)
    (hcircles : S.totalCircleCount ≤ 72) :
    76 ≤ fourteenWeight S D := by
  have hexpand :=
    sum_fourteenSixLineBlockFunctional_eq S D hpoint hD
  have hupper := sum_fourteenSixLineBlockFunctional_le
    S D gamma hD hgammaKind hgammaSupport hcap
  have hupper' :
      (∑ b : Block,
        fourteenBlockFunctional (S.kind b)
          (fourteenInside S D b) (fourteenOutside S D b)) ≤ 560 := by
    omega
  rw [hexpand] at hupper'
  omega

/-- Lossless aggregate residual: only the eight top weight layers remain. -/
theorem fourteenSixLine_weight_interval
    (S : BlockSystem Point Block) (D : Finset Point) (gamma : Block)
    (hpoint : Fintype.card Point = 14) (hD : D.card = 6)
    (hgammaKind : S.kind gamma = .line)
    (hgammaSupport : S.support gamma = D)
    (hcap : BlockSizeCap S 6)
    (hmomentD : 18 ≤ S.subsetPivotMoment D)
    (hmomentX : 24 ≤ S.subsetPivotMoment (Finset.univ \ D))
    (hdefect : S.defectRow ≤ 140)
    (hcircles : S.totalCircleCount ≤ 72) :
    76 ≤ fourteenWeight S D ∧ fourteenWeight S D ≤ 84 := by
  refine ⟨fourteenSixLine_weight_ge_seventy_six S D gamma hpoint hD
    hgammaKind hgammaSupport hcap hmomentD hmomentX hdefect hcircles, ?_⟩
  have hcapacity := fourteenWeight_le_capacity S D
  rw [hpoint, hD] at hcapacity
  norm_num [Nat.choose] at hcapacity ⊢
  exact hcapacity

end RelativeCertificate

end Erdos506.V1
