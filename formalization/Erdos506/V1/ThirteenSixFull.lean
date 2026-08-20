import Erdos506.V1.ThirteenSixTerminal

/-!
# Full thirteen-point selected-six-circle endpoint

All opening, conservation, signed-`J`, capacity-gap, and terminal arithmetic
is materialized in imported cacheable modules.  This file contains only the
final configuration-level composition.
-/

namespace Erdos506.V1

open Erdos506.Block
open Erdos506.Block.BlockSystem
open Erdos506.Incidence
open Erdos506.V4
open scoped BigOperators

universe u v

section GeometricEndpoint

/-- Full configuration-level selected-six-circle endpoint at thirteen
points.  Every scalar row is materialized above from the canonical block
system and field-free six-conic incidence bounds. -/
theorem thirteenSix_circleCount_ge_sixty_one_of_configuration
    {alpha : Type u} [Fintype alpha] [DecidableEq alpha]
    (Mel : RealPlaneMelchiorPrinciple.{u})
    (cfg : Configuration alpha) (hadm : Admissible cfg)
    (hpoint : Fintype.card alpha = 13)
    (gamma : DeterminedCircle cfg)
    (hgamma : (circleTrace cfg gamma.1).card = 6) :
    61 ≤ Erdos506.V4.circleCount cfg := by
  classical
  by_contra hnot
  have hcount : Erdos506.V4.circleCount cfg ≤ 60 := by omega
  let S := blockSystem cfg
  let D : Finset alpha := circleTrace cfg gamma.1
  let X : Finset alpha := Finset.univ \ D
  let gammaBlock : GeometricBlock cfg := Sum.inr gamma
  have hD : D.card = 6 := hgamma
  have hXcard : X.card = 7 := by
    simp [X, D, Finset.card_sdiff_of_subset
      (Finset.subset_univ (circleTrace cfg gamma.1)), hpoint, hgamma]
  have hdisjoint : Disjoint D X := by simp [X, Finset.disjoint_left]
  have hcircleCapGeom : ∀ c : DeterminedCircle cfg,
      (circleTrace cfg c.1).card ≤ 6 := by
    intro c
    exact circleTrace_card_le_six_of_thirteen_of_circleCount_le
      cfg hadm hpoint hcount c
  have hlineCapGeom : ∀ L : DeterminedLine cfg,
      (lineSupport cfg L).card ≤ 6 := by
    intro L
    exact lineSupport_card_le_six_of_thirteen_of_circleCount_le
      cfg hadm hpoint hcount L
  have hcircleCap : ∀ b : GeometricBlock cfg,
      S.kind b = .circle → (S.support b).card ≤ 6 := by
    intro b hb
    cases b with
    | inl L => cases hb
    | inr c => exact hcircleCapGeom c
  have hlineCap : ∀ b : GeometricBlock cfg,
      S.kind b = .line → (S.support b).card ≤ 6 := by
    intro b hb
    cases b with
    | inl L => exact hlineCapGeom L
    | inr c => cases hb
  have hcap : BlockSizeCap S 6 := by
    intro b _hthree
    cases b with
    | inl L =>
        simpa [S, blockSystem, geometricBlockSystem,
          geometricBlockSupport] using hlineCapGeom L
    | inr c =>
        simpa [S, blockSystem, geometricBlockSystem,
          geometricBlockSupport] using hcircleCapGeom c
  have hdefect : S.defectRow ≤ 117 := by
    simpa [S] using thirteenSix_defectRow_le_one_hundred_seventeen
      Mel cfg hadm hpoint
  have hCbridge : S.totalCircleCount = Erdos506.V4.circleCount cfg := by
    dsimp only [S]
    rw [totalCircleCount_eq_card_determinedCircle,
      ← Erdos506.V3.circleCount_eq_card_determinedCircle]
  have hC : S.totalCircleCount ≤ 60 := by omega
  have hP := three_n_le_rowP_of_realPlaneMelchior Mel cfg hadm (by omega)
  change 3 * (Fintype.card alpha : Int) <= S.pivotRow at hP
  rw [hpoint] at hP
  have hC3 : 13 <= S.circleCount 3 :=
    thirteen_circleCount_three_ge_thirteen_of_cap_six
      S hpoint hcap hC hP hdefect
  have hO : 39 ≤ thirteenSixOrdinaryIncidence S := by
    rw [thirteenSixOrdinaryIncidence_eq_three_circleCount]
    omega
  have hpivots := thirteenSix_class_pivot_bounds
    Mel cfg hadm hpoint D hD
  let MX : Nat := Int.toNat (S.subsetPivotMoment X)
  let MG : Nat := Int.toNat (S.subsetPivotMoment D)
  have hMXlower : (21 : Int) ≤ S.subsetPivotMoment X := by
    simpa only [S, X] using hpivots.2
  have hMGlower : (18 : Int) ≤ S.subsetPivotMoment D := by
    simpa only [S] using hpivots.1
  have hMXnonneg : 0 ≤ S.subsetPivotMoment X :=
    le_trans (by norm_num) hMXlower
  have hMGnonneg : 0 ≤ S.subsetPivotMoment D :=
    le_trans (by norm_num) hMGlower
  have hMXcast : (MX : Int) = S.subsetPivotMoment X := by
    exact Int.toNat_of_nonneg hMXnonneg
  have hMGcast : (MG : Int) = S.subsetPivotMoment D := by
    exact Int.toNat_of_nonneg hMGnonneg
  have hMXInt : (21 : Int) ≤ (MX : Int) := by
    rw [hMXcast]
    exact hMXlower
  have hMGInt : (18 : Int) ≤ (MG : Int) := by
    rw [hMGcast]
    exact hMGlower
  have hMX : 21 ≤ MX := by exact_mod_cast hMXInt
  have hMG : 18 ≤ MG := by exact_mod_cast hMGInt
  let u : Nat := MX - 21
  let v : Nat := MG - 18
  have hXslack : S.subsetPivotMoment X = (21 + u : Nat) := by
    rw [← hMXcast]
    dsimp [u]
    omega
  have hGslack : S.subsetPivotMoment D = (18 + v : Nat) := by
    rw [← hMGcast]
    dsimp [v]
    omega
  have hretained : ThirteenSixRetainedOpeningRows S.defectRow
      S.totalCircleCount (thirteenSixOrdinaryIncidence S) MX
      (thirteenSixWeight S D) (thirteenSixGuardedOpeningResidual S D)
      (thirteenSixRelativeCount S D .circle 2 3) := by
    exact thirteenSixRetainedOpeningRows_of_blockSystem
      S D gammaBlock hpoint hD rfl rfl hcircleCap hlineCap
        hdefect hC hO MX (by simpa [X] using hMXcast) hMX
  have hW48 : 48 ≤ thirteenSixWeight S D :=
    thirteenSix_weight_ge_forty_eight_of_retained_opening
      hC hdefect hO hMX hretained
  have hsemantic : thirteenSixWeight S D =
      sixConicWeight cfg gamma X := by
    simpa [S, D, X] using thirteenSixWeight_eq_sixConicWeight cfg gamma
  have hW54semantic := thirteenSix_weight_le_fifty_four
    cfg gamma hgamma X hXcard hdisjoint
  have hW54 : thirteenSixWeight S D ≤ 54 := by
    rw [hsemantic]
    exact hW54semantic
  let r : Nat := thirteenSixWeight S D - 48
  have hWslack : thirteenSixWeight S D = 48 + r := by
    dsimp [r]
    omega
  have hr : r ≤ 6 := by omega
  let C3 : Nat :=
    thirteenSixRelativeCount S D .circle 0 3 +
    thirteenSixRelativeCount S D .circle 1 2 +
    thirteenSixRelativeCount S D .circle 2 1
  have hordinaryRelative := thirteenSixOrdinaryIncidence_eq_relative
    S D gammaBlock hD rfl
  have hC3 : 13 ≤ C3 := by
    dsimp [C3]
    omega
  let j : Nat := C3 - 13
  have hC3slack : C3 = 13 + j := by
    dsimp [j]
    omega
  let d : Nat := 60 - S.totalCircleCount
  have hCslack : S.totalCircleCount + d = 60 := by
    dsimp [d]
    omega
  have hfullLower : 6 + r ≤ (sixConicFullEdges cfg gamma X).card :=
    thirteenSix_fullEdges_lower_of_weight cfg gamma hgamma X hXcard
      hdisjoint hsemantic hWslack
  let repetitionEvents := (sixConicRepetitionEvents cfg gamma X).card
  have hrepetitionLower : thirteenSixRho r ≤ repetitionEvents := by
    exact thirteenSix_repetition_lower cfg gamma hgamma X hXcard
      hdisjoint hfullLower hr
  have hopeningBudget := thirteenSix_opening_residual_budget
    S D gammaBlock hpoint hD rfl rfl hcircleCap hlineCap hdefect
    (C := S.totalCircleCount) (O := thirteenSixOrdinaryIncidence S)
    (MX := MX) (W := thirteenSixWeight S D) (base := 48 + r)
    (budget := 453 + 414 * r) rfl rfl (by simpa [X] using hMXcast)
    rfl hC hO hMX hWslack (by omega)
  have hopeningResidual : thirteenSixOpeningResidualTotal S D ≤
      453 + 414 * r := by omega
  have hA6 : thirteenSixRelativeCount S D .circle 0 6 = 0 := by
    simpa [S, D, X] using thirteenSix_c06_eq_zero
      cfg gamma hgamma X rfl hXcard hr hfullLower hopeningResidual
  obtain ⟨hl05, hl06, hl14, hl15, hl24, hbudget⟩ :=
    thirteenSix_second_budget_of_blockSystem
      S D gammaBlock hpoint hD rfl rfl hcircleCap hlineCap hdefect
      hGslack (by simpa [X] using hXslack) hCslack hWslack hr
  have hrepetitionHost : repetitionEvents ≤ thirteenSixEventCapacitySum S D := by
    have hhost := thirteenSix_repetition_host_capacity_of_blockSystem
      cfg gamma hgamma X rfl hcircleCapGeom hlineCapGeom
        (by simpa [S, D] using hl05) (by simpa [S, D] using hl06)
    simpa [repetitionEvents, thirteenSixEventCapacitySum, S, D] using hhost
  have rows : ThirteenSixAffineRows S D S.totalCircleCount C3
      (thirteenSixWeight S D) u v d r j := by
    exact thirteenSixAffineRows_of_blockSystem
      S D gammaBlock hpoint hD rfl rfl hcircleCap hlineCap
      rfl rfl rfl (by simpa [X] using hXslack) hGslack hCslack
      hC3slack hWslack hl05 hl06 hl14 hl15 hl24
  exact thirteenSix_materialized_arithmetic_impossible
    S D rows hr hrepetitionLower hrepetitionHost hA6 hbudget

end GeometricEndpoint

end Erdos506.V1
