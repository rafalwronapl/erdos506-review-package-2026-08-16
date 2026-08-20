import Erdos506.V1.LangerApplicationFourteenSixCircleFinish
import Erdos506.V1.LangerApplicationFourteenSixLineEndpoint
import Erdos506.V1.LangerApplicationFifteenSixCircleFinish
import Erdos506.V1.LangerApplicationFifteenLineSixFinish
import Erdos506.V1.LangerApplicationEighteenEightCircleFinish
import Erdos506.V1.LangerApplicationOutsiderCirclePencilFinish
import Erdos506.V1.LangerApplicationRichCircleTailFinish

/-!
# Final finite-window dispatcher without Langer

This leaf dispatches the lossless rich-block residual for every cardinality
from fourteen through twenty-two.  It contains no endpoint callback.
-/

namespace Erdos506.V1

open Erdos506.Block
open Erdos506.Block.BlockSystem
open Erdos506.Incidence
open Erdos506.V4

universe u

section ResidualSizes

variable {alpha : Type u} [Fintype alpha] [DecidableEq alpha]
  {cfg : Configuration alpha}

private theorem FiniteWindowRichBlockResidual.size_six_or_seven_of_fifteen
    (R : FiniteWindowRichBlockResidual cfg)
    (h15 : Fintype.card alpha = 15) :
    (geometricBlockSupport cfg R.block).card = 6 ∨
      (geometricBlockSupport cfg R.block).card = 7 := by
  have hlower := R.aboveThreshold
  have hupper := R.atMostHalf
  rw [h15] at hlower hupper
  norm_num [finiteWindowCapThreshold] at hlower hupper
  omega

private theorem FiniteWindowRichBlockResidual.size_seven_or_eight_of_sixteen
    (R : FiniteWindowRichBlockResidual cfg)
    (h16 : Fintype.card alpha = 16) :
    (geometricBlockSupport cfg R.block).card = 7 ∨
      (geometricBlockSupport cfg R.block).card = 8 := by
  have hlower := R.aboveThreshold
  have hupper := R.atMostHalf
  rw [h16] at hlower hupper
  norm_num [finiteWindowCapThreshold] at hlower hupper
  omega

private theorem FiniteWindowRichBlockResidual.size_eight_of_seventeen
    (R : FiniteWindowRichBlockResidual cfg)
    (h17 : Fintype.card alpha = 17) :
    (geometricBlockSupport cfg R.block).card = 8 := by
  have hlower := R.aboveThreshold
  have hupper := R.atMostHalf
  rw [h17] at hlower hupper
  norm_num [finiteWindowCapThreshold] at hlower hupper
  omega

private theorem FiniteWindowRichBlockResidual.size_eight_of_eighteen
    (R : FiniteWindowRichBlockResidual cfg)
    (h18 : Fintype.card alpha = 18) :
    (geometricBlockSupport cfg R.block).card = 8 := by
  have hlower := R.aboveThreshold
  have hstrict := R.strictAtLargeEven (Or.inl h18)
  rw [h18] at hlower hstrict
  norm_num [finiteWindowCapThreshold] at hlower hstrict
  omega

end ResidualSizes

section Dispatcher

variable {alpha : Type u} [Fintype alpha] [DecidableEq alpha]

private theorem FiniteWindowRichBlockResidual.circle_impossible_finiteWindow
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
    {cfg : Configuration alpha} (R : FiniteWindowRichBlockResidual cfg)
    (hadm : Admissible cfg)
    (hcircle : (blockSystem cfg).kind R.block = .circle)
    (hcount : Erdos506.V4.circleCount cfg <
      Erdos506.v1UniformTarget (Fintype.card alpha)) : False := by
  by_cases hn19 : 19 ≤ Fintype.card alpha
  · exact R.circle_impossible_of_ge_nineteen
      Mel EvenArr Cross Kelly U17 TenGeometry TenReduction ElevenGeometry
        Gram Grid Gallery Direction hadm hcircle hn19 hcount
  · have hmin := R.window_lower
    have hmax := R.window_upper
    have hcases : Fintype.card alpha = 14 ∨
        Fintype.card alpha = 15 ∨ Fintype.card alpha = 16 ∨
        Fintype.card alpha = 17 ∨ Fintype.card alpha = 18 := by
      omega
    rcases hcases with h14 | h15 | h16 | h17 | h18
    · have hs := R.fourteen_size h14
      exact R.circle_impossible_of_fourteen_six
        Mel hadm hcircle h14 hs hcount
    · rcases R.size_six_or_seven_of_fifteen h15 with hs | hs
      · exact R.circle_impossible_of_fifteen_six
          Mel hadm hcircle h15 hs hcount
      · exact R.circle_impossible_of_fifteen_seven
          Mel hadm hcircle h15 hs hcount
    · rcases R.size_seven_or_eight_of_sixteen h16 with hs | hs
      · exact R.circle_impossible_of_sixteen_seven
          Mel EvenArr hadm hcircle h16 hs hcount
      · exact R.circle_impossible_of_sixteen_eight
          Mel EvenArr hadm hcircle h16 hs hcount
    · have hs := R.size_eight_of_seventeen h17
      exact R.circle_impossible_of_seventeen_eight
        Mel hadm hcircle h17 hs hcount
    · have hs := R.size_eight_of_eighteen h18
      exact R.circle_impossible_of_eighteen_eight
        Mel hadm hcircle h18 hs hcount

private theorem FiniteWindowRichBlockResidual.line_impossible_finiteWindow_of_ne_fifteen
    (Mel : RealPlaneMelchiorPrinciple.{u})
    (EvenArr : RealPlaneEvenArrangementPrinciple.{u})
    (Cross : RealPlaneRadicalAxisCrossBlockPrinciple.{u})
    (Kelly : RealPlaneKellyMoserPrinciple.{u})
    (U17 : RealPlaneSixCircleU17Principle.{u})
    (TenGeometry : RealPlaneTenFiveGeometry.{u})
    {cfg : Configuration alpha} (R : FiniteWindowRichBlockResidual cfg)
    (hadm : Admissible cfg)
    (hline : (blockSystem cfg).kind R.block = .line)
    (hne15 : Fintype.card alpha ≠ 15)
    (hcount : Erdos506.V4.circleCount cfg <
      Erdos506.v1UniformTarget (Fintype.card alpha)) : False := by
  by_cases hn19 : 19 ≤ Fintype.card alpha
  · exact R.line_impossible_of_sixteenEight_or_ge_nineteen
      hline (Or.inr hn19) hcount
  · have hmin := R.window_lower
    have hmax := R.window_upper
    have hcases : Fintype.card alpha = 14 ∨
        Fintype.card alpha = 16 ∨ Fintype.card alpha = 17 ∨
        Fintype.card alpha = 18 := by
      omega
    rcases hcases with h14 | h16 | h17 | h18
    · have hs := R.fourteen_size h14
      exact R.line_impossible_of_fourteen_six
        Mel hadm hline h14 hs hcount
    · rcases R.size_seven_or_eight_of_sixteen h16 with hs | hs
      · exact R.line_impossible_of_sixteen_seven_or_seventeen_eight
          Mel EvenArr Cross hadm hline (Or.inl ⟨h16, hs⟩) hcount
      · exact R.line_impossible_of_sixteenEight_or_ge_nineteen
          hline (Or.inl ⟨h16, hs⟩) hcount
    · have hs := R.size_eight_of_seventeen h17
      exact R.line_impossible_of_sixteen_seven_or_seventeen_eight
        Mel EvenArr Cross hadm hline (Or.inr ⟨h17, hs⟩) hcount
    · have hs := R.size_eight_of_eighteen h18
      exact R.line_impossible_of_eighteen_eight
        Mel EvenArr Cross Kelly U17 TenGeometry hadm hline h18 hs hcount

/-- Every counterexample in the complete finite window is eliminated by the
kind- and cardinality-specific endpoints, without invoking Langer. -/
theorem v1UniformTarget_le_circleCount_finiteWindow_without_langer
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
    (cfg : Configuration alpha) (hadm : Admissible cfg)
    (hmin : 14 ≤ Fintype.card alpha)
    (hmax : Fintype.card alpha ≤ 22) :
    Erdos506.v1UniformTarget (Fintype.card alpha) ≤
      Erdos506.V4.circleCount cfg := by
  by_contra hnot
  have hcount : Erdos506.V4.circleCount cfg <
      Erdos506.v1UniformTarget (Fintype.card alpha) := by
    omega
  let R := finiteWindowRichBlockResidual_of_counterexample
    Mel cfg hadm hmin hmax hcount
  cases hkind : (blockSystem cfg).kind R.block with
  | circle =>
      exact R.circle_impossible_finiteWindow
        Mel EvenArr Cross Kelly U17 TenGeometry TenReduction ElevenGeometry
          Gram Grid Gallery Direction hadm hkind hcount
  | line =>
      by_cases h15 : Fintype.card alpha = 15
      · rcases R.size_six_or_seven_of_fifteen h15 with hs | hs
        · exact R.line_impossible_of_fifteen_six
            Mel hadm hkind h15 hs hcount
        · exact R.line_impossible_of_fifteen_seven
            hadm hkind h15 hs hcount
      · exact R.line_impossible_finiteWindow_of_ne_fifteen
          Mel EvenArr Cross Kelly U17 TenGeometry hadm hkind h15 hcount

end Dispatcher

end Erdos506.V1
