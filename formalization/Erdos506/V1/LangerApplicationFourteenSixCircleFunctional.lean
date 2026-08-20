import Erdos506.V1.LangerApplicationFourteenSixResidual

/-!
# The fourteen-point selected-six functional bound

The defect-corrected selected-circle functional, specialized to the
`6+8` split and the six-block cap, forces the two--two weight to be at
least `76`.  This leaves only the narrow geometric range `76..79`.
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

private theorem fourteenSix_line_functional_bound (g x : Nat)
    (hg : g ≤ 2) (hmin : 3 ≤ g + x) (hcap : g + x ≤ 6) :
    fourteenBlockFunctional .line g x ≤
      4 * fourteenBlockDefect .line g x := by
  have hx : x ≤ 6 := by omega
  interval_cases g <;> interval_cases x <;>
    simp [fourteenBlockFunctional, fourteenBlockDefect, Nat.choose] at *

private theorem fourteenSix_circle_functional_bound (g x : Nat)
    (hg : g ≤ 2) (hmin : 3 ≤ g + x) (hcap : g + x ≤ 6) :
    fourteenBlockFunctional .circle g x ≤
      4 * fourteenBlockDefect .circle g x := by
  have hx : x ≤ 6 := by omega
  interval_cases g <;> interval_cases x <;>
    simp [fourteenBlockFunctional, fourteenBlockDefect, Nat.choose] at *

private theorem fourteenSix_selected_functional :
    fourteenBlockFunctional .circle 6 0 =
      4 * fourteenBlockDefect .circle 6 0 := by
  norm_num [fourteenBlockFunctional, fourteenBlockDefect, Nat.choose]

private theorem sum_fourteenSixBlockFunctional_eq
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

private theorem sum_fourteenSixBlockFunctional_le
    (S : BlockSystem Point Block) (D : Finset Point) (gamma : Block)
    (hD : D.card = 6)
    (hgammaKind : S.kind gamma = .circle)
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
      rw [hg, hx, hgammaKind]
      have hdefectGamma :
          fourteenBlockDefect .circle 6 0 =
            S.blockDefectContribution gamma := by
        simp [fourteenBlockDefect, BlockSystem.blockDefectContribution,
          hgammaKind, hgammaSupport, hD]
      rw [fourteenSix_selected_functional, hdefectGamma]
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
          have hblockCap :
              fourteenInside S D b + fourteenOutside S D b ≤ 6 := by
            rw [hsum]
            exact hcap b (S.circle_min b hkind)
          have hres := fourteenSix_circle_functional_bound
            (fourteenInside S D b) (fourteenOutside S D b)
            hg hmin hblockCap
          have hdefect' :
              fourteenBlockDefect .circle
                  (fourteenInside S D b) (fourteenOutside S D b) =
                S.blockDefectContribution b := by
            simpa [hkind] using hdefect
          rw [hdefect'] at hres
          exact hres
      | line =>
          have hsmin : 2 ≤ (S.support b).card := S.line_min b hkind
          by_cases hmin :
              3 ≤ fourteenInside S D b + fourteenOutside S D b
          · have hblockCap :
                fourteenInside S D b + fourteenOutside S D b ≤ 6 := by
              rw [hsum]
              apply hcap b
              rw [← hsum]
              exact hmin
            have hres := fourteenSix_line_functional_bound
              (fourteenInside S D b) (fourteenOutside S D b)
              hg hmin hblockCap
            have hdefect' :
                fourteenBlockDefect .line
                    (fourteenInside S D b) (fourteenOutside S D b) =
                  S.blockDefectContribution b := by
              simpa [hkind] using hdefect
            rw [hdefect'] at hres
            exact hres
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
            interval_cases fourteenInside S D b <;>
              interval_cases fourteenOutside S D b <;>
              norm_num [fourteenBlockFunctional, fourteenBlockDefect,
                Nat.choose] at * <;>
              omega
  calc
    _ ≤ ∑ b : Block, 4 * S.blockDefectContribution b := by
      exact Finset.sum_le_sum fun b _hb => hlocal b
    _ = 4 * S.defectRow := by
      rw [← Finset.mul_sum, S.defectRow_eq_sum_blockDefectContribution]

private theorem fourteenWeight_ge_seventy_six_of_rows
    (S : BlockSystem Point Block) (D : Finset Point) (gamma : Block)
    (hpoint : Fintype.card Point = 14) (hD : D.card = 6)
    (hgammaKind : S.kind gamma = .circle)
    (hgammaSupport : S.support gamma = D)
    (hcap : BlockSizeCap S 6)
    (hmomentD : 18 ≤ S.subsetPivotMoment D)
    (hmomentX : 24 ≤ S.subsetPivotMoment (Finset.univ \ D))
    (hdefect : S.defectRow ≤ 140)
    (hcircles : S.totalCircleCount ≤ 72) :
    76 ≤ fourteenWeight S D := by
  have hexpand := sum_fourteenSixBlockFunctional_eq S D hpoint hD
  have hupper := sum_fourteenSixBlockFunctional_le S D gamma hD
    hgammaKind hgammaSupport hcap
  have hupper' :
      (∑ b : Block,
        fourteenBlockFunctional (S.kind b)
          (fourteenInside S D b) (fourteenOutside S D b)) ≤ 560 := by
    omega
  have hresidual :
      (1014 : Int) - 6 * (fourteenWeight S D : Int) ≤ 560 := by
    rw [hexpand] at hupper'
    omega
  omega

end RelativeCertificate

section GeometricResidual

variable {alpha : Type u} [Fintype alpha] [DecidableEq alpha]

/-- The selected-six residual functional forces `W ≥ 76`. -/
theorem FourteenSixCircleResidualData.fourteenWeight_ge_seventy_six
    {cfg : Configuration alpha} {c : DeterminedCircle cfg}
    (R : FourteenSixCircleResidualData cfg c) :
    76 ≤ fourteenWeight (blockSystem cfg) (circleTrace cfg c.1) := by
  have htotal : (blockSystem cfg).totalCircleCount ≤ 72 := by
    rw [totalCircleCount_eq_card_determinedCircle,
      ← Erdos506.V3.circleCount_eq_card_determinedCircle]
    exact R.circle_count_le
  have hgammaKind :
      (blockSystem cfg).kind (Sum.inr c : GeometricBlock cfg) = .circle := rfl
  have hgammaSupport :
      (blockSystem cfg).support (Sum.inr c : GeometricBlock cfg) =
        circleTrace cfg c.1 := rfl
  exact fourteenWeight_ge_seventy_six_of_rows
    (Point := alpha) (Block := GeometricBlock cfg)
    (blockSystem cfg) (circleTrace cfg c.1) (Sum.inr c)
    R.point_card R.selected_card hgammaKind hgammaSupport R.block_cap
    R.selected_moment R.outside_moment R.defect_row_le htotal

/-- Lossless checkpoint after the functional and the existing eight-outsider
geometry: only weights `76..79`, with line footprint at most `22`, remain. -/
theorem FourteenSixCircleResidualData.functional_extreme_residual
    {cfg : Configuration alpha} {c : DeterminedCircle cfg}
    (R : FourteenSixCircleResidualData cfg c) :
    76 ≤ fourteenWeight (blockSystem cfg) (circleTrace cfg c.1) ∧
      fourteenWeight (blockSystem cfg) (circleTrace cfg c.1) ≤ 79 ∧
      sixConicLineIncidence cfg c
        (Finset.univ \ circleTrace cfg c.1) ≤ 22 := by
  exact ⟨FourteenSixCircleResidualData.fourteenWeight_ge_seventy_six
      (alpha := alpha) (cfg := cfg) (c := c) R,
    FourteenSixCircleResidualData.fourteenWeight_le_seventy_nine
      (α := alpha) (cfg := cfg) (c := c) R,
    FourteenSixCircleResidualData.line_incidence_le_twenty_two
      (α := alpha) (cfg := cfg) (c := c) R⟩

end GeometricResidual

end Erdos506.V1
