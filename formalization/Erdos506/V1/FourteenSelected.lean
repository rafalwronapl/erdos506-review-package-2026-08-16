import Erdos506.Block.RelativeRows
import Erdos506.V1.FourteenResidual

/-!
# The selected seven-circle branch at fourteen points

This module closes the second half of the fourteen-point dichotomy.  It
keeps the relative block calculation abstract until the final geometric
specialization.
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

/-- Number of labels of a block in the selected seven-set. -/
def fourteenInside (S : BlockSystem Point Block) (D : Finset Point)
    (b : Block) : ℕ :=
  (S.support b ∩ D).card

/-- Number of labels of a block outside the selected seven-set. -/
def fourteenOutside (S : BlockSystem Point Block) (D : Finset Point)
    (b : Block) : ℕ :=
  (S.support b \ D).card

/-- Circle blocks whose trace in the selected seven-set has size two. -/
def fourteenTwoTraceCircles (S : BlockSystem Point Block)
    (D : Finset Point) : Finset Block :=
  Finset.univ.filter fun b =>
    S.kind b = .circle ∧ fourteenInside S D b = 2

/-- The outside-pair weight in the selected seven-circle certificate. -/
def fourteenWeight (S : BlockSystem Point Block) (D : Finset Point) : ℕ :=
  ∑ b ∈ fourteenTwoTraceCircles S D,
    Nat.choose (fourteenOutside S D b) 2

theorem fourteenInside_add_fourteenOutside
    (S : BlockSystem Point Block) (D : Finset Point) (b : Block) :
    fourteenInside S D b + fourteenOutside S D b =
      (S.support b).card := by
  exact Finset.card_inter_add_card_sdiff (S.support b) D

theorem fourteenOutside_eq_inside_compl
    (S : BlockSystem Point Block) (D : Finset Point) (b : Block) :
    fourteenOutside S D b =
      fourteenInside S (Finset.univ \ D) b := by
  apply congrArg Finset.card
  ext p
  simp

theorem fourteenWeight_le_capacity
    (S : BlockSystem Point Block) (D : Finset Point) :
    fourteenWeight S D ≤
      D.card / 2 * Nat.choose (Fintype.card Point - D.card) 2 := by
  apply S.relative_two_two_capacity D (fourteenTwoTraceCircles S D)
  intro b hb
  exact (Finset.mem_filter.mp hb).2.2

/-- The four relative triple rows at a seven--seven split, cast to `Int` in
the form used by the residual functional. -/
theorem fourteen_relative_rows
    (S : BlockSystem Point Block) (D : Finset Point)
    (hpoint : Fintype.card Point = 14) (hD : D.card = 7) :
    (∑ b : Block, (Nat.choose (fourteenOutside S D b) 3 : ℤ)) = 35 ∧
    (∑ b : Block,
      (fourteenInside S D b : ℤ) *
        (Nat.choose (fourteenOutside S D b) 2 : ℤ)) = 147 ∧
    (∑ b : Block,
      (Nat.choose (fourteenInside S D b) 2 : ℤ) *
        (fourteenOutside S D b : ℤ)) = 147 ∧
    (∑ b : Block, (Nat.choose (fourteenInside S D b) 3 : ℤ)) = 35 := by
  have h0 := S.relative_triple_partition D 0 (by omega)
  have h1 := S.relative_triple_partition D 1 (by omega)
  have h2 := S.relative_triple_partition D 2 (by omega)
  have h3 := S.relative_triple_partition D 3 (by omega)
  rw [hpoint, hD] at h0 h1 h2 h3
  norm_num [fourteenInside, fourteenOutside, Nat.choose] at h0 h1 h2 h3
  constructor
  · exact_mod_cast h0
  constructor
  · exact_mod_cast h1
  constructor
  · exact_mod_cast h2
  · exact_mod_cast h3

/-- Exact expansion of the sum of the local residual functionals. -/
theorem sum_fourteenBlockFunctional_eq
    (S : BlockSystem Point Block) (D : Finset Point)
    (hpoint : Fintype.card Point = 14) (hD : D.card = 7) :
    (∑ b : Block,
      fourteenBlockFunctional (S.kind b)
        (fourteenInside S D b) (fourteenOutside S D b)) =
      3507 + 3 * S.subsetPivotMoment D +
        6 * S.subsetPivotMoment (Finset.univ \ D) -
        36 * (S.totalCircleCount : ℤ) -
        6 * (fourteenWeight S D : ℤ) := by
  classical
  obtain ⟨hrow0, hrow1, hrow2, hrow3⟩ :=
    fourteen_relative_rows S D hpoint hD
  have hmomentD :
      (∑ b : Block,
        if 3 ≤ fourteenInside S D b + fourteenOutside S D b then
          (fourteenInside S D b : ℤ) *
            (4 - ((fourteenInside S D b +
              fourteenOutside S D b : ℕ) : ℤ))
        else 0) = S.subsetPivotMoment D := by
    rw [subsetPivotMoment]
    apply Fintype.sum_congr
    intro b
    rw [fourteenInside_add_fourteenOutside]
    rfl
  have hmomentX :
      (∑ b : Block,
        if 3 ≤ fourteenInside S D b + fourteenOutside S D b then
          (fourteenOutside S D b : ℤ) *
            (4 - ((fourteenInside S D b +
              fourteenOutside S D b : ℕ) : ℤ))
        else 0) = S.subsetPivotMoment (Finset.univ \ D) := by
    rw [subsetPivotMoment]
    apply Fintype.sum_congr
    intro b
    rw [fourteenInside_add_fourteenOutside,
      fourteenOutside_eq_inside_compl]
    rfl
  have hcircle :
      (∑ b : Block,
        if S.kind b = .circle then (36 : ℤ) else 0) =
          36 * (S.totalCircleCount : ℤ) := by
    rw [← Finset.sum_filter]
    simp [BlockSystem.totalCircleCount, BlockSystem.blocksOfKind]
    ring
  have hweight :
      (∑ b : Block,
        if S.kind b = .circle ∧ fourteenInside S D b = 2 then
          (Nat.choose (fourteenOutside S D b) 2 : ℤ)
        else 0) = (fourteenWeight S D : ℤ) := by
    rw [fourteenWeight, Nat.cast_sum]
    simp [fourteenTwoTraceCircles, Finset.sum_filter]
  have hpointwise (b : Block) :
      fourteenBlockFunctional (S.kind b)
          (fourteenInside S D b) (fourteenOutside S D b) =
        6 * (Nat.choose (fourteenOutside S D b) 3 : ℤ) +
        9 * ((fourteenInside S D b : ℤ) *
          (Nat.choose (fourteenOutside S D b) 2 : ℤ)) +
        12 * ((Nat.choose (fourteenInside S D b) 2 : ℤ) *
          (fourteenOutside S D b : ℤ)) +
        6 * (Nat.choose (fourteenInside S D b) 3 : ℤ) +
        3 * (if 3 ≤ fourteenInside S D b + fourteenOutside S D b then
          (fourteenInside S D b : ℤ) *
            (4 - ((fourteenInside S D b +
              fourteenOutside S D b : ℕ) : ℤ))
        else 0) +
        6 * (if 3 ≤ fourteenInside S D b + fourteenOutside S D b then
          (fourteenOutside S D b : ℤ) *
            (4 - ((fourteenInside S D b +
              fourteenOutside S D b : ℕ) : ℤ))
        else 0) -
        (if S.kind b = .circle then 36 else 0) -
        6 * (if S.kind b = .circle ∧ fourteenInside S D b = 2 then
          (Nat.choose (fourteenOutside S D b) 2 : ℤ)
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

/-- Summing the pointwise residual table leaves only the outsider-triple
correction and the exceptional contribution of the selected circle. -/
theorem sum_fourteenBlockFunctional_le
    (S : BlockSystem Point Block) (D : Finset Point) (gamma : Block)
    (hpoint : Fintype.card Point = 14) (hD : D.card = 7)
    (hgammaKind : S.kind gamma = .circle)
    (hgammaSupport : S.support gamma = D)
    (hcircleCap : ∀ b, S.kind b = .circle → (S.support b).card ≤ 7)
    (hlineCap : ∀ b, S.kind b = .line → (S.support b).card ≤ 6) :
    (∑ b : Block,
      fourteenBlockFunctional (S.kind b)
        (fourteenInside S D b) (fourteenOutside S D b)) ≤
      4 * S.defectRow + 132 := by
  classical
  have hrow0 := (fourteen_relative_rows S D hpoint hD).1
  have hlocal (b : Block) :
      fourteenBlockFunctional (S.kind b)
          (fourteenInside S D b) (fourteenOutside S D b) ≤
        4 * S.blockDefectContribution b +
          3 * (Nat.choose (fourteenOutside S D b) 3 : ℤ) +
          (if b = gamma then 27 else 0) := by
    by_cases hbgamma : b = gamma
    · subst b
      have hg : fourteenInside S D gamma = 7 := by
        simp [fourteenInside, hgammaSupport, hD]
      have hx : fourteenOutside S D gamma = 0 := by
        simp [fourteenOutside, hgammaSupport]
      rw [hg, hx, hgammaKind]
      have hdefectGamma :
          fourteenBlockDefect .circle 7 0 =
            S.blockDefectContribution gamma := by
        simp [fourteenBlockDefect, BlockSystem.blockDefectContribution,
          hgammaKind, hgammaSupport, hD]
      rw [fourteen_selected_circle_residual, hdefectGamma]
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
              fourteenInside S D b + fourteenOutside S D b ≤ 7 := by
            rw [hsum]
            exact hcircleCap b hkind
          have hres := fourteen_circle_residual_bound
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
              fourteenInside S D b + fourteenOutside S D b ≤ 6 := by
            rw [hsum]
            exact hlineCap b hkind
          by_cases hmin :
              3 ≤ fourteenInside S D b + fourteenOutside S D b
          · have hres := fourteen_line_residual_bound
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
              norm_num [fourteenBlockFunctional,
                fourteenBlockDefect,
                Nat.choose] at * <;>
              omega
  calc
    (∑ b : Block,
        fourteenBlockFunctional (S.kind b)
          (fourteenInside S D b) (fourteenOutside S D b)) ≤
        ∑ b : Block,
          (4 * S.blockDefectContribution b +
            3 * (Nat.choose (fourteenOutside S D b) 3 : ℤ) +
            (if b = gamma then 27 else 0)) := by
      exact Finset.sum_le_sum fun b _hb => hlocal b
    _ = 4 * S.defectRow + 132 := by
      simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
      rw [S.defectRow_eq_sum_blockDefectContribution, hrow0]
      simp
      ring

/-- The residual certificate forces the outside-pair weight to be at least
sixty-nine. -/
theorem fourteenWeight_ge_sixty_nine
    (S : BlockSystem Point Block) (D : Finset Point) (gamma : Block)
    (hpoint : Fintype.card Point = 14) (hD : D.card = 7)
    (hgammaKind : S.kind gamma = .circle)
    (hgammaSupport : S.support gamma = D)
    (hcircleCap : ∀ b, S.kind b = .circle → (S.support b).card ≤ 7)
    (hlineCap : ∀ b, S.kind b = .line → (S.support b).card ≤ 6)
    (hmomentD : 21 ≤ S.subsetPivotMoment D)
    (hmomentX : 21 ≤ S.subsetPivotMoment (Finset.univ \ D))
    (hdefect : S.defectRow ≤ 140)
    (hcircles : S.totalCircleCount ≤ 72) :
    69 ≤ fourteenWeight S D := by
  have hexpand := sum_fourteenBlockFunctional_eq S D hpoint hD
  have hupper := sum_fourteenBlockFunctional_le S D gamma hpoint hD
    hgammaKind hgammaSupport hcircleCap hlineCap
  have hupper' :
      (∑ b : Block,
        fourteenBlockFunctional (S.kind b)
          (fourteenInside S D b) (fourteenOutside S D b)) ≤ 692 := by
    omega
  have hresidual :
      (1104 : ℤ) - 6 * (fourteenWeight S D : ℤ) ≤ 692 := by
    rw [hexpand] at hupper'
    omega
  exact fourteen_weight_ge_sixty_nine_of_residual
    (fourteenWeight S D) hresidual

/-- The residual lower bound and the matching capacity are incompatible. -/
theorem no_selected_seven_block_at_fourteen
    (S : BlockSystem Point Block) (D : Finset Point) (gamma : Block)
    (hpoint : Fintype.card Point = 14) (hD : D.card = 7)
    (hgammaKind : S.kind gamma = .circle)
    (hgammaSupport : S.support gamma = D)
    (hcircleCap : ∀ b, S.kind b = .circle → (S.support b).card ≤ 7)
    (hlineCap : ∀ b, S.kind b = .line → (S.support b).card ≤ 6)
    (hmomentD : 21 ≤ S.subsetPivotMoment D)
    (hmomentX : 21 ≤ S.subsetPivotMoment (Finset.univ \ D))
    (hdefect : S.defectRow ≤ 140)
    (hcircles : S.totalCircleCount ≤ 72) : False := by
  have hlower := fourteenWeight_ge_sixty_nine S D gamma hpoint hD
    hgammaKind hgammaSupport hcircleCap hlineCap hmomentD hmomentX
    hdefect hcircles
  have hupper := fourteenWeight_le_capacity S D
  rw [hpoint, hD] at hupper
  norm_num [Nat.choose] at hupper
  exact fourteen_weight_contradiction (fourteenWeight S D) hlower hupper

end RelativeCertificate

section GeometricEndpoint

/-- Under the contradictory circle bound, a determined seven-circle cannot
exist in an admissible fourteen-point configuration. -/
theorem no_seven_circle_of_fourteen_of_circleCount_le
    {α : Type u} [Fintype α] [DecidableEq α]
    (Mel : RealPlaneMelchiorPrinciple.{u})
    (cfg : Configuration α) (hadm : Admissible cfg)
    (hcard : Fintype.card α = 14)
    (hcount : Erdos506.V4.circleCount cfg ≤ 72)
    (c : DeterminedCircle cfg)
    (hc : (circleTrace cfg c.1).card = 7) : False := by
  classical
  let D : Finset α := circleTrace cfg c.1
  let gamma : GeometricBlock cfg := Sum.inr c
  have hD : D.card = 7 := hc
  have hgammaKind : (blockSystem cfg).kind gamma = .circle := rfl
  have hgammaSupport : (blockSystem cfg).support gamma = D := rfl
  have hcircleCap : ∀ b : GeometricBlock cfg,
      (blockSystem cfg).kind b = .circle →
        ((blockSystem cfg).support b).card ≤ 7 := by
    intro b hb
    cases b with
    | inl L => cases hb
    | inr c' =>
        exact circleTrace_card_le_seven_of_fourteen_of_circleCount_le
          cfg hadm hcard hcount c'
  have hlineCap : ∀ b : GeometricBlock cfg,
      (blockSystem cfg).kind b = .line →
        ((blockSystem cfg).support b).card ≤ 6 := by
    intro b hb
    cases b with
    | inl L =>
        exact lineSupport_card_le_six_of_fourteen_of_circleCount_le
          cfg hadm hcard hcount L
    | inr c' => cases hb
  have hthree : 3 ≤ Fintype.card α := by omega
  have hmomentD : 21 ≤ (blockSystem cfg).subsetPivotMoment D := by
    have hmoment := (blockSystem cfg).three_mul_card_le_subsetPivotMoment D
      (fun p _hp => by
        change 0 ≤ sigma cfg p
        exact sigma_nonneg_of_realPlaneMelchior
          Mel cfg hadm hthree p)
    rw [hD] at hmoment
    norm_num at hmoment ⊢
    exact hmoment
  have hXcard : (Finset.univ \ D).card = 7 := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ D),
      Finset.card_univ, hcard, hD]
  have hmomentX :
      21 ≤ (blockSystem cfg).subsetPivotMoment (Finset.univ \ D) := by
    have hmoment := (blockSystem cfg).three_mul_card_le_subsetPivotMoment
      (Finset.univ \ D) (fun p _hp => by
        change 0 ≤ sigma cfg p
        exact sigma_nonneg_of_realPlaneMelchior
          Mel cfg hadm hthree p)
    rw [hXcard] at hmoment
    norm_num at hmoment ⊢
    exact hmoment
  have hdefect : (blockSystem cfg).defectRow ≤ 140 := by
    have hrow := rowD_le_n_mul_n_sub_four_of_realPlaneMelchior
      Mel cfg hadm hthree
    change (blockSystem cfg).defectRow ≤
      (Fintype.card α : ℤ) * ((Fintype.card α : ℤ) - 4) at hrow
    rw [hcard] at hrow
    norm_num at hrow ⊢
    exact hrow
  have hcircles : (blockSystem cfg).totalCircleCount ≤ 72 := by
    rw [totalCircleCount_eq_card_determinedCircle,
      ← Erdos506.V3.circleCount_eq_card_determinedCircle]
    exact hcount
  exact no_selected_seven_block_at_fourteen
    (blockSystem cfg) D gamma hcard hD hgammaKind hgammaSupport
    hcircleCap hlineCap hmomentD hmomentX hdefect hcircles

/-- Every admissible fourteen-point configuration determines at least
seventy-three proper circles. -/
theorem circleCount_ge_seventy_three_of_card_fourteen
    {α : Type u} [Fintype α] [DecidableEq α]
    (Mel : RealPlaneMelchiorPrinciple.{u})
    (Lan : RealPlaneLangerPrinciple.{u})
    (cfg : Configuration α) (hadm : Admissible cfg)
    (hcard : Fintype.card α = 14) :
    73 ≤ Erdos506.V4.circleCount cfg := by
  by_contra hnot
  have hcount : Erdos506.V4.circleCount cfg ≤ 72 := by omega
  by_cases hno7 : NoSevenCircle cfg
  · exact hnot (circleCount_ge_seventy_three_of_card_fourteen_of_noSevenCircle
      Mel Lan cfg hadm hcard hno7)
  · rw [NoSevenCircle] at hno7
    push Not at hno7
    obtain ⟨c, hc⟩ := hno7
    exact no_seven_circle_of_fourteen_of_circleCount_le
      Mel cfg hadm hcard hcount c hc

end GeometricEndpoint

end Erdos506.V1
