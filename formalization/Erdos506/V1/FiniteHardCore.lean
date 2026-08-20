import Erdos506.V1.ElevenTwelveOuter
import Erdos506.V1.FiniteRange
import Erdos506.V1.NineComplete
import Erdos506.V1.TenFour
import Erdos506.V1.Thirteen

/-!
# The exact remaining hard core on nine through thirteen labels

Relative to the currently checked outer reductions, the surrounding modules
fully discharge `n = 9` and leave one explicitly selected-circle endpoint at
each of `n = 10, 11, 12, 13`.  This file records that reduction as a single
checked router.  In particular, none of the callbacks below is an unlabelled
``middle range'' assumption.
-/

namespace Erdos506.V1

open Erdos506.Incidence Erdos506.V4

universe u

/-- At nine labels, the cap-four and cap-at-least-six branches are already
closed.  Thus it suffices to close a selected five-point circle. -/
theorem circleCount_ge_twenty_five_of_card_nine_of_five_circle_endpoint
    {α : Type u} [Fintype α] [DecidableEq α]
    (Mel : RealPlaneMelchiorPrinciple.{u})
    (EvenArr : RealPlaneEvenArrangementPrinciple.{u})
    (cfg : Configuration α) (hadm : Admissible cfg)
    (hcard : Fintype.card α = 9)
    (fiveCircle : ∀ c : DeterminedCircle cfg,
      (circleTrace cfg c.1).card = 5 →
        25 ≤ Erdos506.V4.circleCount cfg) :
    25 ≤ Erdos506.V4.circleCount cfg := by
  by_contra hnot
  have hcount : Erdos506.V4.circleCount cfg ≤ 24 := by omega
  have hcap : ∀ c : DeterminedCircle cfg,
      (circleTrace cfg c.1).card ≤ 5 :=
    circleTrace_card_le_five_of_nine_of_circleCount_le
      cfg hadm hcard hcount
  by_cases hfour : ∀ c : DeterminedCircle cfg,
      (circleTrace cfg c.1).card ≤ 4
  · exact hnot
      (circleCount_ge_twenty_five_of_card_nine_of_circle_cap_four
        Mel EvenArr cfg hadm hcard hfour)
  · push Not at hfour
    obtain ⟨c, hc⟩ := hfour
    have hc5 : (circleTrace cfg c.1).card = 5 := by
      have := hcap c
      omega
    exact hnot (fiveCircle c hc5)

/-- At eleven labels, the outer incidence rows force a selected circle of
trace five or six under the contradictory bound `C ≤ 40`. -/
theorem circleCount_ge_forty_one_of_card_eleven_of_five_or_six_endpoint
    {α : Type u} [Fintype α] [DecidableEq α]
    (Mel : RealPlaneMelchiorPrinciple.{u})
    (Kelly : RealPlaneKellyMoserPrinciple.{u})
    (cfg : Configuration α) (hadm : Admissible cfg)
    (hcard : Fintype.card α = 11)
    (fiveOrSix : ∀ c : DeterminedCircle cfg,
      ((circleTrace cfg c.1).card = 5 ∨
        (circleTrace cfg c.1).card = 6) →
          41 ≤ Erdos506.V4.circleCount cfg) :
    41 ≤ Erdos506.V4.circleCount cfg := by
  by_contra hnot
  have hcount : Erdos506.V4.circleCount cfg ≤ 40 := by omega
  obtain ⟨c, hc⟩ :=
    exists_circle_trace_card_five_or_six_of_card_eleven_of_circleCount_le
      Mel Kelly cfg hadm hcard hcount
  exact hnot (fiveOrSix c hc)

/-- At twelve labels, the outer incidence rows force a selected circle of
trace five or six under the contradictory bound `C ≤ 50`. -/
theorem circleCount_ge_fifty_one_of_card_twelve_of_five_or_six_endpoint
    {α : Type u} [Fintype α] [DecidableEq α]
    (Mel : RealPlaneMelchiorPrinciple.{u})
    (Kelly : RealPlaneKellyMoserPrinciple.{u})
    (cfg : Configuration α) (hadm : Admissible cfg)
    (hcard : Fintype.card α = 12)
    (fiveOrSix : ∀ c : DeterminedCircle cfg,
      ((circleTrace cfg c.1).card = 5 ∨
        (circleTrace cfg c.1).card = 6) →
          51 ≤ Erdos506.V4.circleCount cfg) :
    51 ≤ Erdos506.V4.circleCount cfg := by
  by_contra hnot
  have hcount : Erdos506.V4.circleCount cfg ≤ 50 := by omega
  obtain ⟨c, hc⟩ :=
    exists_circle_trace_card_five_or_six_of_card_twelve_of_circleCount_le
      Mel Kelly cfg hadm hcard hcount
  exact hnot (fiveOrSix c hc)

/-- Full-domain V1 assembly with four explicitly labelled finite endpoint
callbacks.  The callbacks are deliberately specialized to the trace sizes
left by the currently checked outer reductions. -/
theorem circleCount_ge_target_of_exact_finite_hard_core
    {α : Type u} [Fintype α] [DecidableEq α]
    (Mel : RealPlaneMelchiorPrinciple.{u})
    (Lan : RealPlaneLangerPrinciple.{u})
    (EvenArr : RealPlaneEvenArrangementPrinciple.{u})
    (Cross : RealPlaneRadicalAxisCrossBlockPrinciple.{u})
    (Kelly : RealPlaneKellyMoserPrinciple.{u})
    (U17 : RealPlaneSixCircleU17Principle.{u})
    (cfg : Configuration α) (hadm : Admissible cfg)
    (hcard : 4 ≤ Fintype.card α)
    (tenFive : Fintype.card α = 10 → SmallHardCase cfg →
      ∀ c : DeterminedCircle cfg,
        (circleTrace cfg c.1).card = 5 →
          33 ≤ Erdos506.V4.circleCount cfg)
    (elevenFiveOrSix : Fintype.card α = 11 → SmallHardCase cfg →
      ∀ c : DeterminedCircle cfg,
        ((circleTrace cfg c.1).card = 5 ∨
          (circleTrace cfg c.1).card = 6) →
            41 ≤ Erdos506.V4.circleCount cfg)
    (twelveFiveOrSix : Fintype.card α = 12 → SmallHardCase cfg →
      ∀ c : DeterminedCircle cfg,
        ((circleTrace cfg c.1).card = 5 ∨
          (circleTrace cfg c.1).card = 6) →
            51 ≤ Erdos506.V4.circleCount cfg)
    (thirteenSix : Fintype.card α = 13 → SmallHardCase cfg →
      ∀ c : DeterminedCircle cfg,
        (circleTrace cfg c.1).card = 6 →
          61 ≤ Erdos506.V4.circleCount cfg) :
    Erdos506.v1Target (Fintype.card α) ≤
      Erdos506.V4.circleCount cfg := by
  apply circleCount_ge_target_of_nine_hard
    Mel Lan EvenArr cfg hadm hcard
  intro hnine hthirteen hhard
  by_cases h9 : Fintype.card α = 9
  · have h :=
      circleCount_ge_twenty_five_of_card_nine
        Mel EvenArr Cross cfg hadm h9
    rw [h9]
    norm_num [Erdos506.v1Target, Erdos506.v1UniformTarget, Nat.choose]
    exact h
  by_cases h10 : Fintype.card α = 10
  · have h :=
      circleCount_ge_thirty_three_of_card_ten_of_five_circle_endpoint
        Mel EvenArr Kelly U17 cfg hadm h10 (tenFive h10 hhard)
    rw [h10]
    norm_num [Erdos506.v1Target, Erdos506.v1UniformTarget, Nat.choose]
    exact h
  by_cases h11 : Fintype.card α = 11
  · have h :=
      circleCount_ge_forty_one_of_card_eleven_of_five_or_six_endpoint
        Mel Kelly cfg hadm h11 (elevenFiveOrSix h11 hhard)
    rw [h11]
    norm_num [Erdos506.v1Target, Erdos506.v1UniformTarget, Nat.choose]
    exact h
  by_cases h12 : Fintype.card α = 12
  · have h :=
      circleCount_ge_fifty_one_of_card_twelve_of_five_or_six_endpoint
        Mel Kelly cfg hadm h12 (twelveFiveOrSix h12 hhard)
    rw [h12]
    norm_num [Erdos506.v1Target, Erdos506.v1UniformTarget, Nat.choose]
    exact h
  have h13 : Fintype.card α = 13 := by omega
  have h := circleCount_ge_sixty_one_of_card_thirteen_of_six_circle_hard
    Mel cfg hadm h13 (thirteenSix h13 hhard)
  rw [h13]
  norm_num [Erdos506.v1Target, Erdos506.v1UniformTarget, Nat.choose]
  exact h

end Erdos506.V1
