import Erdos506.V1.ThirteenSixConservationA

/-!
# Thirteen-point selected-six conservation, part B

This module adds the weight and two pivot-moment rows and assembles all seven
opaque conservation results into `ThirteenSixAffineRows`.
-/

namespace Erdos506.V1

open Erdos506.Block
open Erdos506.Block.BlockSystem
open Erdos506.Incidence
open Erdos506.V4
open scoped BigOperators

universe u v

section RelativeCensus

variable {Point : Type u} {Block : Type v}
  [Fintype Point] [Fintype Block] [DecidableEq Point]

theorem thirteenSix_affine_weight_row
    (S : BlockSystem Point Block) (D : Finset Point) (gamma : Block)
    (hD : D.card = 6) (hgammaKind : S.kind gamma = .circle)
    (hgammaSupport : S.support gamma = D)
    (hcircleCap : ∀ c, S.kind c = .circle → (S.support c).card ≤ 6)
    (hlineCap : ∀ L, S.kind L = .line → (S.support L).card ≤ 6) :
    thirteenSixRelativeCount S D .circle 2 2 +
      3 * thirteenSixRelativeCount S D .circle 2 3 +
      6 * thirteenSixRelativeCount S D .circle 2 4 =
        thirteenSixWeight S D := by
  classical
  obtain ⟨hc00, hc01, hc02, hc10, hc11, hc16, hc20, hc25, hc26,
      hl00, hl01, hl10, hl16, hl25, hl26⟩ :=
    thirteenSixInvalidRelativeCells_of_caps S D hcircleCap hlineCap
  have hrow := thirteenSix_sum_by_relativeCount_selected
    S D gamma hD hgammaKind hgammaSupport hcircleCap hlineCap
      (fun kind g x =>
        if kind = .circle ∧ g = 2 then (Nat.choose x 2 : Int) else 0)
  have hleft :
      (∑ b : Block,
        if S.kind b = .circle ∧ thirteenSixInside S D b = 2 then
          (Nat.choose (thirteenSixOutside S D b) 2 : Int) else 0) =
        (thirteenSixWeight S D : Int) := by
    rw [thirteenSixWeight, fourteenWeight, Nat.cast_sum]
    simp [fourteenTwoTraceCircles, Finset.sum_filter]
  rw [hleft, thirteenSix_sum_blockKind_int] at hrow
  norm_num [Finset.sum_range_succ, Nat.choose] at hrow
  omega

theorem thirteenSix_affine_momentX_row
    (S : BlockSystem Point Block) (D : Finset Point) (gamma : Block)
    (hD : D.card = 6) (hgammaKind : S.kind gamma = .circle)
    (hgammaSupport : S.support gamma = D)
    (hcircleCap : ∀ c, S.kind c = .circle → (S.support c).card ≤ 6)
    (hlineCap : ∀ L, S.kind L = .line → (S.support L).card ≤ 6)
    (hl05 : thirteenSixRelativeCount S D .line 0 5 = 0)
    (hl06 : thirteenSixRelativeCount S D .line 0 6 = 0)
    (hl14 : thirteenSixRelativeCount S D .line 1 4 = 0)
    (hl15 : thirteenSixRelativeCount S D .line 1 5 = 0)
    (hl24 : thirteenSixRelativeCount S D .line 2 4 = 0) :
    3 * (thirteenSixRelativeCount S D .circle 0 3 : Int) -
      5 * (thirteenSixRelativeCount S D .circle 0 5 : Int) -
      12 * (thirteenSixRelativeCount S D .circle 0 6 : Int) +
      2 * (thirteenSixRelativeCount S D .circle 1 2 : Int) -
      4 * (thirteenSixRelativeCount S D .circle 1 4 : Int) -
      10 * (thirteenSixRelativeCount S D .circle 1 5 : Int) +
      (thirteenSixRelativeCount S D .circle 2 1 : Int) -
      3 * (thirteenSixRelativeCount S D .circle 2 3 : Int) -
      8 * (thirteenSixRelativeCount S D .circle 2 4 : Int) +
      3 * (thirteenSixRelativeCount S D .line 0 3 : Int) +
      2 * (thirteenSixRelativeCount S D .line 1 2 : Int) +
      (thirteenSixRelativeCount S D .line 2 1 : Int) -
      3 * (thirteenSixRelativeCount S D .line 2 3 : Int) =
        S.subsetPivotMoment (Finset.univ \ D) := by
  classical
  obtain ⟨hc00, hc01, hc02, hc10, hc11, hc16, hc20, hc25, hc26,
      hl00, hl01, hl10, hl16, hl25, hl26⟩ :=
    thirteenSixInvalidRelativeCells_of_caps S D hcircleCap hlineCap
  have hrow := thirteenSix_sum_by_relativeCount_selected
    S D gamma hD hgammaKind hgammaSupport hcircleCap hlineCap
      (fun _kind g x =>
        if 3 ≤ g + x then (x : Int) * (4 - ((g + x : Nat) : Int)) else 0)
  have hleft :
      (∑ b : Block,
        if 3 ≤ thirteenSixInside S D b + thirteenSixOutside S D b then
          (thirteenSixOutside S D b : Int) *
            (4 - ((thirteenSixInside S D b +
              thirteenSixOutside S D b : Nat) : Int)) else 0) =
        S.subsetPivotMoment (Finset.univ \ D) := by
    rw [subsetPivotMoment]
    apply Fintype.sum_congr
    intro b
    rw [thirteenSixInside_add_thirteenSixOutside,
      thirteenSixOutside_eq_support_inter_compl_card]
  rw [hleft, thirteenSix_sum_blockKind_int] at hrow
  norm_num [Finset.sum_range_succ] at hrow
  omega

theorem thirteenSix_affine_momentGamma_row
    (S : BlockSystem Point Block) (D : Finset Point) (gamma : Block)
    (hD : D.card = 6) (hgammaKind : S.kind gamma = .circle)
    (hgammaSupport : S.support gamma = D)
    (hcircleCap : ∀ c, S.kind c = .circle → (S.support c).card ≤ 6)
    (hlineCap : ∀ L, S.kind L = .line → (S.support L).card ≤ 6)
    (hl14 : thirteenSixRelativeCount S D .line 1 4 = 0)
    (hl15 : thirteenSixRelativeCount S D .line 1 5 = 0)
    (hl24 : thirteenSixRelativeCount S D .line 2 4 = 0) :
    -12 + (thirteenSixRelativeCount S D .circle 1 2 : Int) -
      (thirteenSixRelativeCount S D .circle 1 4 : Int) -
      2 * (thirteenSixRelativeCount S D .circle 1 5 : Int) +
      2 * (thirteenSixRelativeCount S D .circle 2 1 : Int) -
      2 * (thirteenSixRelativeCount S D .circle 2 3 : Int) -
      4 * (thirteenSixRelativeCount S D .circle 2 4 : Int) +
      (thirteenSixRelativeCount S D .line 1 2 : Int) +
      2 * (thirteenSixRelativeCount S D .line 2 1 : Int) -
      2 * (thirteenSixRelativeCount S D .line 2 3 : Int) =
        S.subsetPivotMoment D := by
  classical
  obtain ⟨hc00, hc01, hc02, hc10, hc11, hc16, hc20, hc25, hc26,
      hl00, hl01, hl10, hl16, hl25, hl26⟩ :=
    thirteenSixInvalidRelativeCells_of_caps S D hcircleCap hlineCap
  have hrow := thirteenSix_sum_by_relativeCount_selected
    S D gamma hD hgammaKind hgammaSupport hcircleCap hlineCap
      (fun _kind g x =>
        if 3 ≤ g + x then (g : Int) * (4 - ((g + x : Nat) : Int)) else 0)
  have hleft :
      (∑ b : Block,
        if 3 ≤ thirteenSixInside S D b + thirteenSixOutside S D b then
          (thirteenSixInside S D b : Int) *
            (4 - ((thirteenSixInside S D b +
              thirteenSixOutside S D b : Nat) : Int)) else 0) =
        S.subsetPivotMoment D := by
    rw [subsetPivotMoment]
    apply Fintype.sum_congr
    intro b
    rw [thirteenSixInside_add_thirteenSixOutside,
      thirteenSixInside_eq_support_inter_card]
  rw [hleft, thirteenSix_sum_blockKind_int] at hrow
  norm_num [Finset.sum_range_succ] at hrow
  omega

theorem thirteenSixAffineRows_of_blockSystem
    (S : BlockSystem Point Block) (D : Finset Point) (gamma : Block)
    (hpoint : Fintype.card Point = 13) (hD : D.card = 6)
    (hgammaKind : S.kind gamma = .circle)
    (hgammaSupport : S.support gamma = D)
    (hcircleCap : ∀ c, S.kind c = .circle → (S.support c).card ≤ 6)
    (hlineCap : ∀ L, S.kind L = .line → (S.support L).card ≤ 6)
    {C C3 W u v d r j : Nat}
    (hCeq : C = S.totalCircleCount)
    (hC3eq : C3 = thirteenSixRelativeCount S D .circle 0 3 +
      thirteenSixRelativeCount S D .circle 1 2 +
      thirteenSixRelativeCount S D .circle 2 1)
    (hWeq : W = thirteenSixWeight S D)
    (hX : S.subsetPivotMoment (Finset.univ \ D) = (21 + u : Nat))
    (hGamma : S.subsetPivotMoment D = (18 + v : Nat))
    (hCslack : C + d = 60) (hC3slack : C3 = 13 + j)
    (hWslack : W = 48 + r)
    (hl05 : thirteenSixRelativeCount S D .line 0 5 = 0)
    (hl06 : thirteenSixRelativeCount S D .line 0 6 = 0)
    (hl14 : thirteenSixRelativeCount S D .line 1 4 = 0)
    (hl15 : thirteenSixRelativeCount S D .line 1 5 = 0)
    (hl24 : thirteenSixRelativeCount S D .line 2 4 = 0) :
    ThirteenSixAffineRows S D C C3 W u v d r j := by
  have hcircle := thirteenSix_affine_circle_row
    S D gamma hD hgammaKind hgammaSupport hcircleCap hlineCap
  have h0 := thirteenSix_affine_row0
    S D gamma hpoint hD hgammaKind hgammaSupport hcircleCap hlineCap
      hl05 hl06 hl14 hl15 hl24
  have h1 := thirteenSix_affine_row1
    S D gamma hpoint hD hgammaKind hgammaSupport hcircleCap hlineCap
      hl14 hl15 hl24
  have h2 := thirteenSix_affine_row2
    S D gamma hpoint hD hgammaKind hgammaSupport hcircleCap hlineCap hl24
  have hweight := thirteenSix_affine_weight_row
    S D gamma hD hgammaKind hgammaSupport hcircleCap hlineCap
  have hmomentX := thirteenSix_affine_momentX_row
    S D gamma hD hgammaKind hgammaSupport hcircleCap hlineCap
      hl05 hl06 hl14 hl15 hl24
  have hmomentGamma := thirteenSix_affine_momentGamma_row
    S D gamma hD hgammaKind hgammaSupport hcircleCap hlineCap
      hl14 hl15 hl24
  constructor
  · omega
  · exact hC3eq.symm
  · exact h0
  · exact h1
  · exact h2
  · omega
  · omega
  · omega
  · exact hCslack
  · exact hC3slack
  · exact hWslack

end RelativeCensus

end Erdos506.V1
