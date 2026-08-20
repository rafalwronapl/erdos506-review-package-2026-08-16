import Erdos506.V1.LangerApplicationRichCircleEasyFinish

/-!
# Rich-circle outsider correction in the finite-window tail

For nineteen through twenty-two labels, the rich-circle pencil together
with the already proved ten-, eleven-, and twelve-outsider bounds exceeds
the uniform target.  This closes all circle-kind residuals in that tail.
-/

namespace Erdos506.V1

open Erdos506.Block
open Erdos506.Block.BlockSystem
open Erdos506.Incidence
open Erdos506.V4

universe u

/-- Every circle-kind finite-window residual from nineteen through
twenty-two labels contradicts the assumed sub-target circle count. -/
theorem FiniteWindowRichBlockResidual.circle_impossible_of_ge_nineteen
    {α : Type u} [Fintype α] [DecidableEq α]
    (Mel : RealPlaneMelchiorPrinciple.{u})
    (EvenArr : RealPlaneEvenArrangementPrinciple.{u})
    (Cross : RealPlaneRadicalAxisCrossBlockPrinciple.{u})
    (Kelly : RealPlaneKellyMoserPrinciple.{u})
    (U17 : RealPlaneSixCircleU17Principle.{u})
    (TenGeometry : RealPlaneTenFiveGeometry.{u})
    (TenReduction : RealPlaneTenFiveReductionPrinciple.{u})
    (ElevenGeometry : RealPlaneElevenFiveGeometry.{u})
    (Gram : RealPlaneTwelveGramPrinciple.{u})
    (Grid : RealPlaneTwelveGridPrinciple.{u})
    (Gallery : RealPlaneTwelveGalleryPrinciple.{u})
    (Direction : RealPlaneTwelveDirectionPrinciple.{u})
    {cfg : Configuration α} (R : FiniteWindowRichBlockResidual cfg)
    (hadm : Admissible cfg)
    (hcircle : (blockSystem cfg).kind R.block = .circle)
    (hn19 : 19 ≤ Fintype.card α)
    (hcount : Erdos506.V4.circleCount cfg <
      Erdos506.v1UniformTarget (Fintype.card α)) : False := by
  let S := blockSystem cfg
  let O := blockOutsiders S R.block
  let Q := finsetRestrictionConfiguration cfg O
  have hcap := halfBlockCap_of_circleCount_lt_v1UniformTarget
    cfg hadm (by omega) hcount
  have hcorrect := richCirclePencilNumerator_add_outsiderCircleCount_le
    cfg R.block hcircle
  rw [totalCircleCount_eq_card_determinedCircle,
    ← Erdos506.V3.circleCount_eq_card_determinedCircle] at hcorrect
  have hwindowUpper := R.window_upper
  have hnCases : Fintype.card α = 19 ∨ Fintype.card α = 20 ∨
      Fintype.card α = 21 ∨ Fintype.card α = 22 := by
    omega
  rcases hnCases with h19 | h20 | h21 | h22
  · have hs : (geometricBlockSupport cfg R.block).card = 9 := by
      have hlower := R.aboveThreshold
      have hupper := R.atMostHalf
      rw [h19] at hlower hupper
      norm_num [finiteWindowCapThreshold] at hlower hupper
      omega
    have hsS : (S.support R.block).card = 9 := by
      simpa [S] using hs
    have hcapNine : BlockSizeCap S 9 := by
      rw [h19] at hcap
      norm_num at hcap
      exact hcap
    have hOcard : O.card = 10 := by
      dsimp only [O]
      rw [card_blockOutsiders, h19, hsS]
    have hQcard : Fintype.card (BlockOutsider S R.block) = 10 := by
      rw [Fintype.card_coe, hOcard]
    have hQadm : Admissible Q := by
      exact admissible_finsetRestriction_blockOutsiders_of_cap
        cfg R.block 9 (by omega) hcapNine (by change 9 < O.card; omega)
    have hQcount : 33 ≤ Erdos506.V4.circleCount Q :=
      circleCount_ge_thirty_three_of_card_ten
        Mel EvenArr Cross Kelly U17 TenGeometry Q hQadm hQcard
    change 33 ≤ Erdos506.V4.circleCount
      (finsetRestrictionConfiguration cfg
        (blockOutsiders (blockSystem cfg) R.block)) at hQcount
    rw [h19, hs] at hcorrect
    norm_num [Nat.choose] at hcorrect
    rw [h19] at hcount
    norm_num [Erdos506.v1UniformTarget, Nat.choose] at hcount
    omega
  -- The even twenty-label residual has strict block size nine.
  · have hs : (geometricBlockSupport cfg R.block).card = 9 := by
      have hlower := R.aboveThreshold
      have hstrict := R.strictAtLargeEven (Or.inr (Or.inl h20))
      rw [h20] at hlower hstrict
      norm_num [finiteWindowCapThreshold] at hlower hstrict
      omega
    have hsS : (S.support R.block).card = 9 := by
      simpa [S] using hs
    have hcapTen : BlockSizeCap S 10 := by
      rw [h20] at hcap
      norm_num at hcap
      exact hcap
    have hOcard : O.card = 11 := by
      dsimp only [O]
      rw [card_blockOutsiders, h20, hsS]
    have hQcard : Fintype.card (BlockOutsider S R.block) = 11 := by
      rw [Fintype.card_coe, hOcard]
    have hQadm : Admissible Q := by
      exact admissible_finsetRestriction_blockOutsiders_of_cap
        cfg R.block 10 (by omega) hcapTen (by change 10 < O.card; omega)
    have hQcount : 41 ≤ Erdos506.V4.circleCount Q :=
      circleCount_ge_forty_one_of_card_eleven_without_langer
        Mel EvenArr Cross Kelly U17 TenReduction ElevenGeometry
          Q hQadm hQcard
    change 41 ≤ Erdos506.V4.circleCount
      (finsetRestrictionConfiguration cfg
        (blockOutsiders (blockSystem cfg) R.block)) at hQcount
    rw [h20, hs] at hcorrect
    norm_num [Nat.choose] at hcorrect
    rw [h20] at hcount
    norm_num [Erdos506.v1UniformTarget, Nat.choose] at hcount
    omega
  · have hs : (geometricBlockSupport cfg R.block).card = 10 := by
      have hlower := R.aboveThreshold
      have hupper := R.atMostHalf
      rw [h21] at hlower hupper
      norm_num [finiteWindowCapThreshold] at hlower hupper
      omega
    have hsS : (S.support R.block).card = 10 := by
      simpa [S] using hs
    have hcapTen : BlockSizeCap S 10 := by
      rw [h21] at hcap
      norm_num at hcap
      exact hcap
    have hOcard : O.card = 11 := by
      dsimp only [O]
      rw [card_blockOutsiders, h21, hsS]
    have hQcard : Fintype.card (BlockOutsider S R.block) = 11 := by
      rw [Fintype.card_coe, hOcard]
    have hQadm : Admissible Q := by
      exact admissible_finsetRestriction_blockOutsiders_of_cap
        cfg R.block 10 (by omega) hcapTen (by change 10 < O.card; omega)
    have hQcount : 41 ≤ Erdos506.V4.circleCount Q :=
      circleCount_ge_forty_one_of_card_eleven_without_langer
        Mel EvenArr Cross Kelly U17 TenReduction ElevenGeometry
          Q hQadm hQcard
    change 41 ≤ Erdos506.V4.circleCount
      (finsetRestrictionConfiguration cfg
        (blockOutsiders (blockSystem cfg) R.block)) at hQcount
    rw [h21, hs] at hcorrect
    norm_num [Nat.choose] at hcorrect
    rw [h21] at hcount
    norm_num [Erdos506.v1UniformTarget, Nat.choose] at hcount
    omega
  · have hs : (geometricBlockSupport cfg R.block).card = 10 := by
      have hlower := R.aboveThreshold
      have hstrict := R.strictAtLargeEven (Or.inr (Or.inr h22))
      rw [h22] at hlower hstrict
      norm_num [finiteWindowCapThreshold] at hlower hstrict
      omega
    have hsS : (S.support R.block).card = 10 := by
      simpa [S] using hs
    have hcapEleven : BlockSizeCap S 11 := by
      rw [h22] at hcap
      norm_num at hcap
      exact hcap
    have hOcard : O.card = 12 := by
      dsimp only [O]
      rw [card_blockOutsiders, h22, hsS]
    have hQcard : Fintype.card (BlockOutsider S R.block) = 12 := by
      rw [Fintype.card_coe, hOcard]
    have hQadm : Admissible Q := by
      exact admissible_finsetRestriction_blockOutsiders_of_cap
        cfg R.block 11 (by omega) hcapEleven (by change 11 < O.card; omega)
    have hQcount : 51 ≤ Erdos506.V4.circleCount Q :=
      circleCount_ge_fifty_one_of_card_twelve
        Mel EvenArr Kelly Gram Grid Gallery Direction Q hQadm hQcard
    change 51 ≤ Erdos506.V4.circleCount
      (finsetRestrictionConfiguration cfg
        (blockOutsiders (blockSystem cfg) R.block)) at hQcount
    rw [h22, hs] at hcorrect
    norm_num [Nat.choose] at hcorrect
    rw [h22] at hcount
    norm_num [Erdos506.v1UniformTarget, Nat.choose] at hcount
    omega

end Erdos506.V1
