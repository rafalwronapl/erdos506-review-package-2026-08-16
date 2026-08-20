import Erdos506.Finite.IncidenceMoments
import Erdos506.V3.SmallPacking

/-!
# The five-circle packing bound on ten labels

The first part of the ten-point wall is purely combinatorial: at most six
five-point determined circles can occur.  The strict improvement from six
to five is a separate real-geometry statement.
-/

namespace Erdos506.V3

open Erdos506.Finite
open Erdos506.V4

theorem c5_le_six_of_card_ten
    {α : Type*} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (hthree : NoThreeCollinear cfg)
    (hα : Fintype.card α = 10) :
    circleCensus cfg 5 ≤ 6 := by
  letI : DecidableEq (DeterminedCircle cfg) := Classical.decEq _
  let B := circlesOfSize cfg 5
  let support : DeterminedCircle cfg → Finset α :=
    fun c => circleTrace cfg c.1
  have hcard : ∀ c ∈ B, (support c).card = 5 := by
    intro c hc
    exact mem_circlesOfSize.mp hc
  have hinter : ∀ c ∈ B, ∀ d ∈ B, c ≠ d →
      (support c ∩ support d).card ≤ 2 := by
    intro c hc d hd hcd
    have hlt := (circleOwnership cfg hthree).card_inter_lt_of_ne hcd
    change (support c ∩ support d).card < 3 at hlt
    omega
  have hbound := card_le_six_of_five_subsets_card_ten_inter_le_two
    B support hα hcard hinter
  simpa [B, card_circlesOfSize] using hbound

noncomputable def fiveCircleDegree
    {α : Type*} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (x : α) : ℕ := by
  letI : DecidableEq (DeterminedCircle cfg) := Classical.decEq _
  exact incidenceDegree (circlesOfSize cfg 5)
    (fun c : DeterminedCircle cfg => circleTrace cfg c.1) x

/-- Equality in the `c₅ ≤ 6` bound forces the incidence design used by the
power-of-a-point obstruction: every pair of five-circles meets in exactly
two selected points, and every selected point lies on exactly three of the
six circles. -/
theorem c5_eq_six_forces_design
    {α : Type*} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (hthree : NoThreeCollinear cfg)
    (hα : Fintype.card α = 10) (hc5 : circleCensus cfg 5 = 6) :
    (∀ c ∈ circlesOfSize cfg 5, ∀ d ∈ circlesOfSize cfg 5, c ≠ d →
        (circleTrace cfg c.1 ∩ circleTrace cfg d.1).card = 2) ∧
      ∀ x : α, fiveCircleDegree cfg x = 3 := by
  letI : DecidableEq (DeterminedCircle cfg) := Classical.decEq _
  let B := circlesOfSize cfg 5
  let support : DeterminedCircle cfg → Finset α :=
    fun c => circleTrace cfg c.1
  have hB : B.card = 6 := by
    simpa [B, card_circlesOfSize] using hc5
  have hcard : ∀ c ∈ B, (support c).card = 5 := by
    intro c hc
    exact mem_circlesOfSize.mp hc
  have hinter : ∀ c ∈ B, ∀ d ∈ B, c ≠ d →
      (support c ∩ support d).card ≤ 2 := by
    intro c hc d hd hcd
    have hlt := (circleOwnership cfg hthree).card_inter_lt_of_ne hcd
    change (support c ∩ support d).card < 3 at hlt
    omega
  constructor
  · exact inter_eq_two_of_six_five_subsets_card_ten_inter_le_two
      B support hα hB hcard hinter
  · intro x
    have hx := incidenceDegree_eq_three_of_six_five_subsets_card_ten_inter_le_two
      B support hα hB hcard hinter x
    simpa [fiveCircleDegree, B, support] using hx

end Erdos506.V3
