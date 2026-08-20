import Erdos506.V1.LangerApplicationFourteenSixLineFinish

/-!
# The fourteen-point selected six-line endpoint

The selected line itself has functional slack `192 - 84 = 108`.  Retaining
that single local correction strengthens the aggregate weight lower bound
from `76` to `94`, contradicting the universal capacity `W <= 84`.
-/

namespace Erdos506.V1

open Erdos506.Block
open Erdos506.Block.BlockSystem
open Erdos506.Incidence
open Erdos506.V4
open scoped BigOperators

universe u v

section RelativeEndpoint

variable {Point : Type u} {Block : Type v}
  [Fintype Point] [Fintype Block] [DecidableEq Point]

private theorem fourteenSixLineEndpoint_line_bound (g x : Nat)
    (hg : g ≤ 2) (hmin : 3 ≤ g + x) (hcap : g + x ≤ 6) :
    fourteenBlockFunctional .line g x ≤
      4 * fourteenBlockDefect .line g x := by
  have hx : x ≤ 6 := by omega
  interval_cases g <;> interval_cases x <;>
    simp [fourteenBlockFunctional, fourteenBlockDefect, Nat.choose] at *

private theorem fourteenSixLineEndpoint_circle_bound (g x : Nat)
    (hg : g ≤ 2) (hmin : 3 ≤ g + x) (hcap : g + x ≤ 6) :
    fourteenBlockFunctional .circle g x ≤
      4 * fourteenBlockDefect .circle g x := by
  have hx : x ≤ 6 := by omega
  interval_cases g <;> interval_cases x <;>
    simp [fourteenBlockFunctional, fourteenBlockDefect, Nat.choose] at *

private theorem fourteenSixLineEndpoint_selected_exact :
    fourteenBlockFunctional .line 6 0 + 108 =
      4 * fourteenBlockDefect .line 6 0 := by
  simp [fourteenBlockFunctional, fourteenBlockDefect, Nat.choose]

/-- The selected line contributes an unavoidable 108 units of local slack. -/
theorem sum_fourteenSixLineBlockFunctional_add_108_le
    (S : BlockSystem Point Block) (D : Finset Point) (gamma : Block)
    (hD : D.card = 6)
    (hgammaKind : S.kind gamma = .line)
    (hgammaSupport : S.support gamma = D)
    (hcap : BlockSizeCap S 6) :
    (∑ b : Block,
      fourteenBlockFunctional (S.kind b)
        (fourteenInside S D b) (fourteenOutside S D b)) + 108 ≤
      4 * S.defectRow := by
  classical
  have hlocal (b : Block) :
      fourteenBlockFunctional (S.kind b)
          (fourteenInside S D b) (fourteenOutside S D b) +
          (if b = gamma then 108 else 0) ≤
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
      rw [hgammaKind, hg, hx, if_pos rfl, ← hdefect]
      exact le_of_eq fourteenSixLineEndpoint_selected_exact
    · simp only [if_neg hbgamma, add_zero]
      have hg : fourteenInside S D b ≤ 2 := by
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
            exact hcap b (by rw [← hsum]; exact hmin)
          have hres := fourteenSixLineEndpoint_circle_bound
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
            have hres := fourteenSixLineEndpoint_line_bound
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
          (fourteenInside S D b) (fourteenOutside S D b)) + 108 =
        ∑ b : Block,
          (fourteenBlockFunctional (S.kind b)
              (fourteenInside S D b) (fourteenOutside S D b) +
            if b = gamma then 108 else 0) := by
      simp [Finset.sum_add_distrib]
    _ ≤ ∑ b : Block, 4 * S.blockDefectContribution b := by
      exact Finset.sum_le_sum fun b _hb => hlocal b
    _ = 4 * S.defectRow := by
      rw [← Finset.mul_sum, S.defectRow_eq_sum_blockDefectContribution]

/-- The selected-line correction forces `W >= 94`, while two--two capacity
allows only `W <= 84`. -/
theorem no_selected_six_line_at_fourteen
    (S : BlockSystem Point Block) (D : Finset Point) (gamma : Block)
    (hpoint : Fintype.card Point = 14) (hD : D.card = 6)
    (hgammaKind : S.kind gamma = .line)
    (hgammaSupport : S.support gamma = D)
    (hcap : BlockSizeCap S 6)
    (hmomentD : 18 ≤ S.subsetPivotMoment D)
    (hmomentX : 24 ≤ S.subsetPivotMoment (Finset.univ \ D))
    (hdefect : S.defectRow ≤ 140)
    (hcircles : S.totalCircleCount ≤ 72) : False := by
  have hexpand :=
    sum_fourteenSixLineBlockFunctional_eq S D hpoint hD
  have hupper := sum_fourteenSixLineBlockFunctional_add_108_le
    S D gamma hD hgammaKind hgammaSupport hcap
  have hupper' :
      (∑ b : Block,
        fourteenBlockFunctional (S.kind b)
          (fourteenInside S D b) (fourteenOutside S D b)) ≤ 452 := by
    omega
  rw [hexpand] at hupper'
  have hlower : 94 ≤ fourteenWeight S D := by omega
  have hcapacity := fourteenWeight_le_capacity S D
  rw [hpoint, hD] at hcapacity
  norm_num [Nat.choose] at hcapacity ⊢
  omega

end RelativeEndpoint

section GeometricEndpoint

variable {alpha : Type u} [Fintype alpha] [DecidableEq alpha]

/-- A fourteen-point finite-window residual cannot be carried by a
six-point determined line. -/
theorem FiniteWindowRichBlockResidual.line_impossible_of_fourteen_six
    (Mel : RealPlaneMelchiorPrinciple.{u})
    {cfg : Configuration alpha} (R : FiniteWindowRichBlockResidual cfg)
    (hadm : Admissible cfg)
    (hline : (blockSystem cfg).kind R.block = .line)
    (h14 : Fintype.card alpha = 14)
    (hsix : (geometricBlockSupport cfg R.block).card = 6)
    (hcount : Erdos506.V4.circleCount cfg <
      Erdos506.v1UniformTarget (Fintype.card alpha)) : False := by
  classical
  let S := blockSystem cfg
  let D := geometricBlockSupport cfg R.block
  let gamma := R.block
  have hcount72 : Erdos506.V4.circleCount cfg ≤ 72 := by
    rw [h14] at hcount
    norm_num [Erdos506.v1UniformTarget, Nat.choose] at hcount
    omega
  have hnoSeven : NoSevenCircle cfg := by
    intro c hc
    exact no_seven_circle_of_fourteen_of_circleCount_le
      Mel cfg hadm h14 hcount72 c hc
  have hcap : BlockSizeCap S 6 := by
    exact blockSizeCap_six_of_fourteen_of_circleCount_le
      cfg hadm h14 hcount72 hnoSeven
  have hthree : 3 ≤ Fintype.card alpha := by omega
  have hpivot : ∀ p : alpha, 0 ≤ S.pivotSigma p := by
    intro p
    change 0 ≤ sigma cfg p
    exact sigma_nonneg_of_realPlaneMelchior Mel cfg hadm hthree p
  have hDcard : D.card = 6 := by
    simpa [D, S] using hsix
  have hXcard : (Finset.univ \ D).card = 8 := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ D),
      Finset.card_univ, h14, hDcard]
  have hmomentD : 18 ≤ S.subsetPivotMoment D := by
    have hmoment := S.three_mul_card_le_subsetPivotMoment D
      (fun p _hp => hpivot p)
    rw [hDcard] at hmoment
    norm_num at hmoment ⊢
    exact hmoment
  have hmomentX : 24 ≤ S.subsetPivotMoment (Finset.univ \ D) := by
    have hmoment := S.three_mul_card_le_subsetPivotMoment
      (Finset.univ \ D) (fun p _hp => hpivot p)
    rw [hXcard] at hmoment
    norm_num at hmoment ⊢
    exact hmoment
  have hdefect : S.defectRow ≤ 140 := by
    have hrow := rowD_le_n_mul_n_sub_four_of_realPlaneMelchior
      Mel cfg hadm hthree
    change S.defectRow ≤
      (Fintype.card alpha : Int) * ((Fintype.card alpha : Int) - 4) at hrow
    rw [h14] at hrow
    norm_num at hrow ⊢
    exact hrow
  have htotal : S.totalCircleCount ≤ 72 := by
    dsimp only [S]
    rw [totalCircleCount_eq_card_determinedCircle,
      ← Erdos506.V3.circleCount_eq_card_determinedCircle]
    exact hcount72
  apply no_selected_six_line_at_fourteen S D gamma h14 hDcard
  · simpa [gamma, S] using hline
  · rfl
  · exact hcap
  · exact hmomentD
  · exact hmomentX
  · exact hdefect
  · exact htotal

end GeometricEndpoint

end Erdos506.V1
