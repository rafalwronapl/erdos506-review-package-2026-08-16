import Erdos506.V1.ElevenFive
import Erdos506.V1.TenFiveGeometry

/-!
# The complete eleven-point router

Below the target `41`, `ElevenTwelveOuter` produces an actual determined
circle whose trace has cardinality exactly five or exactly six.  The two
alternatives are exhaustive, and each is sent to its configuration-level
endpoint theorem.  No endpoint callback is assumed here.

The selected-five theorem remains semantically appropriate in its branch:
it internally checks whether some (possibly different) six-circle exists
and, if so, redirects that configuration to the completed selected-six
theorem.  Thus the outer split does not silently assert a global trace-five
cap.
-/

namespace Erdos506.V1

open Erdos506.Incidence
open Erdos506.V4

universe u

/-- Every admissible configuration on eleven labels determines at least
forty-one proper circles without using the global Langer principle. -/
theorem circleCount_ge_forty_one_of_card_eleven_without_langer
    {α : Type u} [Fintype α] [DecidableEq α]
    (Mel : RealPlaneMelchiorPrinciple.{u})
    (EvenArr : RealPlaneEvenArrangementPrinciple.{u})
    (Cross : RealPlaneRadicalAxisCrossBlockPrinciple.{u})
    (Kelly : RealPlaneKellyMoserPrinciple.{u})
    (U17 : RealPlaneSixCircleU17Principle.{u})
    (TenReduction : RealPlaneTenFiveReductionPrinciple.{u})
    (ElevenGeometry : RealPlaneElevenFiveGeometry.{u})
    (cfg : Configuration α) (hadm : Admissible cfg)
    (hcard : Fintype.card α = 11) :
    41 <= Erdos506.V4.circleCount cfg := by
  by_contra htarget
  have hcount : Erdos506.V4.circleCount cfg <= 40 := by
    omega
  obtain ⟨gamma, hgammaFive | hgammaSix⟩ :=
    exists_circle_trace_card_five_or_six_of_card_eleven_of_circleCount_le
      Mel Kelly cfg hadm hcard hcount
  · have hfive :=
      elevenFive_circleCount_ge_forty_one_of_configuration_without_langer
        Mel EvenArr Cross Kelly U17
          TenReduction.toGeometry ElevenGeometry
          cfg hadm hcard gamma hgammaFive
    exact htarget hfive
  · have hsix :=
      elevenGammaSix_circleCount_ge_forty_one_of_configuration
        Mel EvenArr Kelly cfg hadm hcard gamma hgammaSix
    exact htarget hsix

/-- Compatibility wrapper retaining the historical global parameter list. -/
theorem circleCount_ge_forty_one_of_card_eleven
    {α : Type u} [Fintype α] [DecidableEq α]
    (Mel : RealPlaneMelchiorPrinciple.{u})
    (_Langer : RealPlaneLangerPrinciple.{u})
    (EvenArr : RealPlaneEvenArrangementPrinciple.{u})
    (Cross : RealPlaneRadicalAxisCrossBlockPrinciple.{u})
    (Kelly : RealPlaneKellyMoserPrinciple.{u})
    (U17 : RealPlaneSixCircleU17Principle.{u})
    (TenReduction : RealPlaneTenFiveReductionPrinciple.{u})
    (ElevenGeometry : RealPlaneElevenFiveGeometry.{u})
    (cfg : Configuration α) (hadm : Admissible cfg)
    (hcard : Fintype.card α = 11) :
    41 <= Erdos506.V4.circleCount cfg :=
  circleCount_ge_forty_one_of_card_eleven_without_langer
    Mel EvenArr Cross Kelly U17 TenReduction ElevenGeometry cfg hadm hcard

end Erdos506.V1
