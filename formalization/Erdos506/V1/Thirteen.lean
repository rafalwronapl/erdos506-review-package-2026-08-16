import Erdos506.V1.FiniteCaps
import Erdos506.V1.ThirteenFive

/-!
# The thirteen-point outer router

The checked rich-circle cap and the complete five-circle transfer reduce the
thirteen-point endpoint to one semantic callback: a selected proper circle
whose trace has size exactly six.  No geometry of that remaining branch is
assumed in this file.
-/

namespace Erdos506.V1

open Erdos506.Incidence
open Erdos506.V4

universe u

/-- At thirteen points, after the checked `≤ 5` branch, the only remaining
counterexample branch contains a proper six-circle. -/
theorem circleCount_ge_sixty_one_of_card_thirteen_of_six_circle_hard
    {α : Type u} [Fintype α] [DecidableEq α]
    (Mel : RealPlaneMelchiorPrinciple.{u})
    (cfg : Configuration α) (hadm : Admissible cfg)
    (hcard : Fintype.card α = 13)
    (sixCircle : ∀ c : DeterminedCircle cfg,
      (circleTrace cfg c.1).card = 6 →
        61 ≤ Erdos506.V4.circleCount cfg) :
    61 ≤ Erdos506.V4.circleCount cfg := by
  by_contra hnot
  have hcount : Erdos506.V4.circleCount cfg ≤ 60 := by omega
  have hcap : ∀ c : DeterminedCircle cfg,
      (circleTrace cfg c.1).card ≤ 6 :=
    circleTrace_card_le_six_of_thirteen_of_circleCount_le
      cfg hadm hcard hcount
  by_cases hfive : ∀ c : DeterminedCircle cfg,
      (circleTrace cfg c.1).card ≤ 5
  · exact hnot (circleCount_ge_sixty_one_of_card_thirteen_of_circleTrace_le_five
      Mel cfg hadm hcard hfive)
  · push Not at hfive
    obtain ⟨c, hc⟩ := hfive
    have hsix : (circleTrace cfg c.1).card = 6 := by
      have := hcap c
      omega
    exact hnot (sixCircle c hsix)

end Erdos506.V1
