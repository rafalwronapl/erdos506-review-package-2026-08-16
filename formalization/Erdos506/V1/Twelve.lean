import Erdos506.V1.ElevenTwelveOuter
import Erdos506.V1.TwelveFive
import Erdos506.V1.TwelveSix

/-!
# The complete twelve-point router

Below the target `51`, the checked outer incidence rows produce a determined
proper circle whose trace has size five or six.  A selected six-circle is
sent directly to the completed selected-six branch.  In the selected-five
case, either every circle has trace at most five and the selected-five branch
applies, or the universal trace-six cap supplies a selected six-circle.

The theorem has only the named real-plane incidence and local geometric
principles used by those checked branches.  It assumes no endpoint callback.
-/

namespace Erdos506.V1

open Erdos506.Incidence
open Erdos506.V4

universe u

/-- Every admissible configuration on twelve labels determines at least
fifty-one proper circles. -/
theorem circleCount_ge_fifty_one_of_card_twelve
    {alpha : Type u} [Fintype alpha] [DecidableEq alpha]
    (Mel : RealPlaneMelchiorPrinciple.{u})
    (EvenArr : RealPlaneEvenArrangementPrinciple.{u})
    (Kelly : RealPlaneKellyMoserPrinciple.{u})
    (Gram : RealPlaneTwelveGramPrinciple.{u})
    (Grid : RealPlaneTwelveGridPrinciple.{u})
    (Gallery : RealPlaneTwelveGalleryPrinciple.{u})
    (Direction : RealPlaneTwelveDirectionPrinciple.{u})
    (cfg : Configuration alpha) (hadm : Admissible cfg)
    (hcard : Fintype.card alpha = 12) :
    51 <= Erdos506.V4.circleCount cfg := by
  by_contra htarget
  have hcount : Erdos506.V4.circleCount cfg <= 50 := by omega
  have hcapSix : forall c : DeterminedCircle cfg,
      (circleTrace cfg c.1).card <= 6 :=
    circleTrace_card_le_six_of_twelve_of_circleCount_le
      cfg hadm hcard hcount
  obtain ⟨gamma, hgammaFive | hgammaSix⟩ :=
    exists_circle_trace_card_five_or_six_of_card_twelve_of_circleCount_le
      Mel Kelly cfg hadm hcard hcount
  · by_cases hcapFive : forall c : DeterminedCircle cfg,
        (circleTrace cfg c.1).card <= 5
    · exact htarget (twelveFive_circleCount_ge_fifty_one
        Mel EvenArr Kelly Gram Grid Gallery cfg hadm hcard
          gamma hgammaFive hcapFive)
    · push Not at hcapFive
      obtain ⟨delta, hdeltaLarge⟩ := hcapFive
      have hdeltaSix : (circleTrace cfg delta.1).card = 6 := by
        have hdeltaCap := hcapSix delta
        omega
      exact htarget (twelveSix_circleCount_ge_fifty_one
        Mel EvenArr Kelly Gram Gallery Direction cfg hadm hcard
          delta hdeltaSix hcapSix)
  · exact htarget (twelveSix_circleCount_ge_fifty_one
      Mel EvenArr Kelly Gram Gallery Direction cfg hadm hcard
        gamma hgammaSix hcapSix)

end Erdos506.V1
