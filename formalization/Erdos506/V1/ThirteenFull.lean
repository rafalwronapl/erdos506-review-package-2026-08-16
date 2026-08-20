import Erdos506.V1.ThirteenFive
import Erdos506.V1.ThirteenSixFull

/-!
# Complete thirteen-point endpoint

This is the public router between the checked `circleTrace ≤ 5` branch and
the fully materialized selected-six-circle branch.  It contains no semantic
callback.
-/

namespace Erdos506.V1

open Erdos506.Incidence
open Erdos506.V4

universe u

/-- Every admissible thirteen-point real-plane configuration determines at
least sixty-one proper circles. -/
theorem circleCount_ge_sixty_one_of_card_thirteen
    {α : Type u} [Fintype α] [DecidableEq α]
    (Mel : RealPlaneMelchiorPrinciple.{u})
    (cfg : Configuration α) (hadm : Admissible cfg)
    (hcard : Fintype.card α = 13) :
    61 ≤ Erdos506.V4.circleCount cfg := by
  classical
  by_contra hnot
  have hcount : Erdos506.V4.circleCount cfg ≤ 60 := by omega
  have hcap : ∀ c : DeterminedCircle cfg,
      (circleTrace cfg c.1).card ≤ 6 :=
    circleTrace_card_le_six_of_thirteen_of_circleCount_le
      cfg hadm hcard hcount
  by_cases hfive : ∀ c : DeterminedCircle cfg,
      (circleTrace cfg c.1).card ≤ 5
  · exact hnot
      (circleCount_ge_sixty_one_of_card_thirteen_of_circleTrace_le_five
        Mel cfg hadm hcard hfive)
  · push Not at hfive
    obtain ⟨c, hc⟩ := hfive
    have hsix : (circleTrace cfg c.1).card = 6 := by
      have hcle := hcap c
      omega
    exact hnot
      (thirteenSix_circleCount_ge_sixty_one_of_configuration
        Mel cfg hadm hcard c hsix)

end Erdos506.V1
