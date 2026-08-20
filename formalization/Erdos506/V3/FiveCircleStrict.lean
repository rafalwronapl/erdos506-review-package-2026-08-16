import Erdos506.V3.FiveCircleDesign
import Erdos506.V3.SixFivePattern

/-!
# Strict five-circle bound on ten points

Equality in the combinatorial bound `c₅ ≤ 6` gives a six-by-five design.
The checked finite classification relabels that design to the canonical
pattern, whose real-plane realization was excluded by inversion and directed
power of a point.  Hence the sharp bound needed at the ten-point wall is
`c₅ ≤ 5`.
-/

namespace Erdos506.V3

open Erdos506.Finite
open Erdos506.V4

theorem circleCensus_five_ne_six_of_card_ten
    {α : Type*} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (hthree : NoThreeCollinear cfg)
    (hα : Fintype.card α = 10) :
    circleCensus cfg 5 ≠ 6 := by
  intro hc5
  let D := sixFiveDesignOfConfiguration cfg hthree hα hc5
  obtain ⟨P, B, hcanonical⟩ := D.exists_canonical_labeling
  let p : Fin 10 → Point2 := fun i => cfg (P i)
  have hp : Function.Injective p := cfg.injective.comp P.injective
  let Γ : Fin 6 → ProperCircle := fun j => (B j).1.1
  have hinc : ∀ i j, p i ∈ ((Γ j).1 : Set Point2) ↔
      j ∈ sixFivePointProfile i := by
    intro i j
    have hlabel :
        j ∈ D.relabeledProfiles P B i ↔
          p i ∈ ((Γ j).1 : Set Point2) := by
      rw [D.mem_relabeledProfiles]
      change P i ∈ circleTrace cfg (B j).1.1 ↔
        cfg (P i) ∈ (((B j).1.1).1 : Set Point2)
      exact mem_circleTrace
    calc
      p i ∈ ((Γ j).1 : Set Point2) ↔
          j ∈ D.relabeledProfiles P B i := hlabel.symm
      _ ↔ j ∈ sixFivePointProfile i := by rw [hcanonical i]
  exact canonical_six_five_pattern_not_realizable p hp Γ hinc

theorem c5_le_five_of_card_ten
    {α : Type*} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (hthree : NoThreeCollinear cfg)
    (hα : Fintype.card α = 10) :
    circleCensus cfg 5 ≤ 5 := by
  have hle := c5_le_six_of_card_ten cfg hthree hα
  have hne := circleCensus_five_ne_six_of_card_ten cfg hthree hα
  omega

end Erdos506.V3
