import Erdos506.V1.LangerApplicationSeventeenEightCircleFinish

/-!
# The eighteen-point selected-eight-circle endpoint

The selected-circle functional forces weight at least `310`, while
elementary two--two capacity gives at most `180`.
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

private theorem eighteenEight_relative_rows
    (S : BlockSystem Point Block) (D : Finset Point)
    (hpoint : Fintype.card Point = 18) (hD : D.card = 8) :
    (∑ b : Block, (Nat.choose (fourteenOutside S D b) 3 : Int)) = 120 ∧
    (∑ b : Block,
      (fourteenInside S D b : Int) *
        (Nat.choose (fourteenOutside S D b) 2 : Int)) = 360 ∧
    (∑ b : Block,
      (Nat.choose (fourteenInside S D b) 2 : Int) *
        (fourteenOutside S D b : Int)) = 280 ∧
    (∑ b : Block, (Nat.choose (fourteenInside S D b) 3 : Int)) = 56 := by
  have h0 := S.relative_triple_partition D 0 (by omega)
  have h1 := S.relative_triple_partition D 1 (by omega)
  have h2 := S.relative_triple_partition D 2 (by omega)
  have h3 := S.relative_triple_partition D 3 (by omega)
  rw [hpoint, hD] at h0 h1 h2 h3
  norm_num [fourteenInside, fourteenOutside, Nat.choose] at h0 h1 h2 h3
  exact ⟨by exact_mod_cast h0, by exact_mod_cast h1,
    by exact_mod_cast h2, by exact_mod_cast h3⟩

private theorem eighteenEight_line_residual_bound (g x : Nat)
    (hg : g ≤ 2) (hmin : 3 ≤ g + x) (hcap : g + x ≤ 9) :
    fourteenBlockFunctional .line g x ≤
      4 * fourteenBlockDefect .line g x +
        3 * (Nat.choose x 3 : Int) := by
  have hx : x ≤ 9 := by omega
  interval_cases g <;> interval_cases x <;>
    simp [fourteenBlockFunctional, fourteenBlockDefect, Nat.choose] at *

private theorem eighteenEight_circle_residual_bound (g x : Nat)
    (hg : g ≤ 2) (hmin : 3 ≤ g + x) (hcap : g + x ≤ 9) :
    fourteenBlockFunctional .circle g x ≤
      4 * fourteenBlockDefect .circle g x +
        3 * (Nat.choose x 3 : Int) := by
  have hx : x ≤ 9 := by omega
  interval_cases g <;> interval_cases x <;>
    simp [fourteenBlockFunctional, fourteenBlockDefect, Nat.choose] at *

private theorem eighteenEight_selected_circle_residual :
    fourteenBlockFunctional .circle 8 0 =
      4 * fourteenBlockDefect .circle 8 0 + 76 := by
  norm_num [fourteenBlockFunctional, fourteenBlockDefect, Nat.choose]

private theorem sum_eighteenEightBlockFunctional_eq
    (S : BlockSystem Point Block) (D : Finset Point)
    (hpoint : Fintype.card Point = 18) (hD : D.card = 8) :
    (∑ b : Block,
      fourteenBlockFunctional (S.kind b)
        (fourteenInside S D b) (fourteenOutside S D b)) =
      7656 + 3 * S.subsetPivotMoment D +
        6 * S.subsetPivotMoment (Finset.univ \ D) -
        36 * (S.totalCircleCount : Int) -
        6 * (fourteenWeight S D : Int) := by
  classical
  obtain ⟨hrow0, hrow1, hrow2, hrow3⟩ :=
    eighteenEight_relative_rows S D hpoint hD
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

private theorem sum_eighteenEightBlockFunctional_le
    (S : BlockSystem Point Block) (D : Finset Point) (gamma : Block)
    (hpoint : Fintype.card Point = 18) (hD : D.card = 8)
    (hgammaKind : S.kind gamma = .circle)
    (hgammaSupport : S.support gamma = D)
    (hcircleCap : ∀ b, S.kind b = .circle → (S.support b).card ≤ 9)
    (hlineCap : ∀ b, S.kind b = .line → (S.support b).card ≤ 9) :
    (∑ b : Block,
      fourteenBlockFunctional (S.kind b)
        (fourteenInside S D b) (fourteenOutside S D b)) ≤
      4 * S.defectRow + 436 := by
  classical
  have hrow0 := (eighteenEight_relative_rows S D hpoint hD).1
  have hlocal (b : Block) :
      fourteenBlockFunctional (S.kind b)
          (fourteenInside S D b) (fourteenOutside S D b) ≤
        4 * S.blockDefectContribution b +
          3 * (Nat.choose (fourteenOutside S D b) 3 : Int) +
          (if b = gamma then 76 else 0) := by
    by_cases hbgamma : b = gamma
    · subst b
      have hg : fourteenInside S D gamma = 8 := by
        simp [fourteenInside, hgammaSupport, hD]
      have hx : fourteenOutside S D gamma = 0 := by
        simp [fourteenOutside, hgammaSupport]
      rw [hg, hx, hgammaKind]
      have hdefectGamma :
          fourteenBlockDefect .circle 8 0 =
            S.blockDefectContribution gamma := by
        simp [fourteenBlockDefect, BlockSystem.blockDefectContribution,
          hgammaKind, hgammaSupport, hD]
      rw [eighteenEight_selected_circle_residual, hdefectGamma]
      norm_num [Nat.choose]
    · have hg : fourteenInside S D b ≤ 2 := by
        have hinter := S.distinct_block_inter_card_lt_three hbgamma
        rw [hgammaSupport] at hinter
        exact Nat.le_of_lt_succ hinter
      have hsum := fourteenInside_add_fourteenOutside S D b
      have hdefect :
          fourteenBlockDefect (S.kind b)
              (fourteenInside S D b) (fourteenOutside S D b) =
            S.blockDefectContribution b := by
        cases hkind : S.kind b <;>
          simp [fourteenBlockDefect, BlockSystem.blockDefectContribution,
            hkind, ← hsum]
      cases hkind : S.kind b with
      | circle =>
          have hmin :
              3 ≤ fourteenInside S D b + fourteenOutside S D b := by
            rw [hsum]
            exact S.circle_min b hkind
          have hcap :
              fourteenInside S D b + fourteenOutside S D b ≤ 9 := by
            rw [hsum]
            exact hcircleCap b hkind
          have hres := eighteenEight_circle_residual_bound
            (fourteenInside S D b) (fourteenOutside S D b)
            hg hmin hcap
          have hdefect' :
              fourteenBlockDefect .circle
                  (fourteenInside S D b) (fourteenOutside S D b) =
                S.blockDefectContribution b := by
            simpa [hkind] using hdefect
          rw [hdefect'] at hres
          simpa [hbgamma] using hres
      | line =>
          have hsmin : 2 ≤ (S.support b).card := S.line_min b hkind
          have hcap :
              fourteenInside S D b + fourteenOutside S D b ≤ 9 := by
            rw [hsum]
            exact hlineCap b hkind
          by_cases hmin :
              3 ≤ fourteenInside S D b + fourteenOutside S D b
          · have hres := eighteenEight_line_residual_bound
              (fourteenInside S D b) (fourteenOutside S D b)
              hg hmin hcap
            have hdefect' :
                fourteenBlockDefect .line
                    (fourteenInside S D b) (fourteenOutside S D b) =
                  S.blockDefectContribution b := by
              simpa [hkind] using hdefect
            rw [hdefect'] at hres
            simpa [hbgamma] using hres
          · have htwo :
                fourteenInside S D b + fourteenOutside S D b = 2 := by
              rw [hsum]
              omega
            have hg2 : fourteenInside S D b ≤ 2 := by omega
            have hx2 : fourteenOutside S D b ≤ 2 := by omega
            have hdefect' :
                fourteenBlockDefect .line
                    (fourteenInside S D b) (fourteenOutside S D b) =
                  S.blockDefectContribution b := by
              simpa [hkind] using hdefect
            rw [← hdefect']
            simp only [if_neg hbgamma, add_zero]
            interval_cases fourteenInside S D b <;>
              interval_cases fourteenOutside S D b <;>
              norm_num [fourteenBlockFunctional, fourteenBlockDefect,
                Nat.choose] at * <;>
              omega
  calc
    (∑ b : Block,
        fourteenBlockFunctional (S.kind b)
          (fourteenInside S D b) (fourteenOutside S D b)) ≤
        ∑ b : Block,
          (4 * S.blockDefectContribution b +
            3 * (Nat.choose (fourteenOutside S D b) 3 : Int) +
            (if b = gamma then 76 else 0)) := by
      exact Finset.sum_le_sum fun b _hb => hlocal b
    _ = 4 * S.defectRow + 436 := by
      simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
      rw [S.defectRow_eq_sum_blockDefectContribution, hrow0]
      simp
      ring

private theorem no_selected_eight_block_at_eighteen
    (S : BlockSystem Point Block) (D : Finset Point) (gamma : Block)
    (hpoint : Fintype.card Point = 18) (hD : D.card = 8)
    (hgammaKind : S.kind gamma = .circle)
    (hgammaSupport : S.support gamma = D)
    (hcircleCap : ∀ b, S.kind b = .circle → (S.support b).card ≤ 9)
    (hlineCap : ∀ b, S.kind b = .line → (S.support b).card ≤ 9)
    (hmomentD : 24 ≤ S.subsetPivotMoment D)
    (hmomentX : 30 ≤ S.subsetPivotMoment (Finset.univ \ D))
    (hdefect : S.defectRow ≤ 252)
    (hcircles : S.totalCircleCount ≤ 128) : False := by
  have hexpand := sum_eighteenEightBlockFunctional_eq S D hpoint hD
  have hupper := sum_eighteenEightBlockFunctional_le S D gamma hpoint hD
    hgammaKind hgammaSupport hcircleCap hlineCap
  have hupper' :
      (∑ b : Block,
        fourteenBlockFunctional (S.kind b)
          (fourteenInside S D b) (fourteenOutside S D b)) ≤ 1444 := by
    omega
  have hresidual :
      (3300 : Int) - 6 * (fourteenWeight S D : Int) ≤ 1444 := by
    rw [hexpand] at hupper'
    omega
  have hlower : 310 ≤ fourteenWeight S D := by omega
  have hcapacity := fourteenWeight_le_capacity S D
  rw [hpoint, hD] at hcapacity
  norm_num [Nat.choose] at hcapacity
  omega

end RelativeCertificate

section GeometricEndpoint

variable {alpha : Type u} [Fintype alpha] [DecidableEq alpha]

/-- The `(18,8)` circle-kind finite-window residual is impossible. -/
theorem FiniteWindowRichBlockResidual.circle_impossible_of_eighteen_eight
    (Mel : RealPlaneMelchiorPrinciple.{u})
    {cfg : Configuration alpha} (R : FiniteWindowRichBlockResidual cfg)
    (hadm : Admissible cfg)
    (hcircle : (blockSystem cfg).kind R.block = .circle)
    (h18 : Fintype.card alpha = 18)
    (height : (geometricBlockSupport cfg R.block).card = 8)
    (hcount : Erdos506.V4.circleCount cfg <
      Erdos506.v1UniformTarget (Fintype.card alpha)) : False := by
  classical
  let S := blockSystem cfg
  let D := geometricBlockSupport cfg R.block
  let gamma := R.block
  have hcapNine : BlockSizeCap S 9 := by
    have hcap := halfBlockCap_of_circleCount_lt_v1UniformTarget
      cfg hadm (by omega) hcount
    rw [h18] at hcap
    norm_num at hcap
    exact hcap
  have hcircleCap : ∀ b, S.kind b = .circle → (S.support b).card ≤ 9 := by
    intro b hb
    exact hcapNine b (S.circle_min b hb)
  have hlineCap : ∀ b, S.kind b = .line → (S.support b).card ≤ 9 := by
    intro b hb
    by_cases hthree : 3 ≤ (S.support b).card
    · exact hcapNine b hthree
    · have hmin := S.line_min b hb
      omega
  have hthree : 3 ≤ Fintype.card alpha := by omega
  have hpivot : ∀ p : alpha, 0 ≤ S.pivotSigma p := by
    intro p
    change 0 ≤ sigma cfg p
    exact sigma_nonneg_of_realPlaneMelchior Mel cfg hadm hthree p
  have hDcard : D.card = 8 := by simpa [D, S] using height
  have hXcard : (Finset.univ \ D).card = 10 := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ D),
      Finset.card_univ, h18, hDcard]
  have hmomentD : 24 ≤ S.subsetPivotMoment D := by
    have hmoment := S.three_mul_card_le_subsetPivotMoment D
      (fun p _hp => hpivot p)
    rw [hDcard] at hmoment
    norm_num at hmoment ⊢
    exact hmoment
  have hmomentX : 30 ≤ S.subsetPivotMoment (Finset.univ \ D) := by
    have hmoment := S.three_mul_card_le_subsetPivotMoment
      (Finset.univ \ D) (fun p _hp => hpivot p)
    rw [hXcard] at hmoment
    norm_num at hmoment ⊢
    exact hmoment
  have hdefect : S.defectRow ≤ 252 := by
    have hrow := rowD_le_n_mul_n_sub_four_of_realPlaneMelchior
      Mel cfg hadm hthree
    change S.defectRow ≤
      (Fintype.card alpha : Int) * ((Fintype.card alpha : Int) - 4) at hrow
    rw [h18] at hrow
    norm_num at hrow ⊢
    exact hrow
  have hcount128 : Erdos506.V4.circleCount cfg ≤ 128 := by
    rw [h18] at hcount
    norm_num [Erdos506.v1UniformTarget, Nat.choose] at hcount
    omega
  have htotal : S.totalCircleCount ≤ 128 := by
    dsimp only [S]
    rw [totalCircleCount_eq_card_determinedCircle,
      ← Erdos506.V3.circleCount_eq_card_determinedCircle]
    exact hcount128
  apply no_selected_eight_block_at_eighteen S D gamma h18 hDcard
  · simpa [gamma, S] using hcircle
  · rfl
  · exact hcircleCap
  · exact hlineCap
  · exact hmomentD
  · exact hmomentX
  · exact hdefect
  · exact htotal

end GeometricEndpoint

end Erdos506.V1
