import Erdos506.V3.Functional

/-!
# Summing the pivot rows

This file isolates the finite double count between the pointwise inverted
Melchior rows and `SummedMelchior`.  Consequently the future incidence proof
only has to establish one local row at each pivot; no global coefficient
manipulation remains hidden in that bridge.
-/

namespace Erdos506.V3

open Erdos506.V4
open scoped BigOperators

noncomputable def circlesThrough {α : Type*} [Fintype α]
    (cfg : Configuration α) (p : α) : Finset (DeterminedCircle cfg) := by
  classical
  exact Finset.univ.filter fun c => p ∈ circleTrace cfg c.1

@[simp] theorem mem_circlesThrough {α : Type*} [Fintype α]
    {cfg : Configuration α} {p : α} {c : DeterminedCircle cfg} :
    c ∈ circlesThrough cfg p ↔ p ∈ circleTrace cfg c.1 := by
  classical
  simp [circlesThrough]

/-- The exact pointwise row obtained by inverting at `p` and applying
Melchior to the remaining points. -/
def PivotMelchior {α : Type*} [Fintype α]
    (cfg : Configuration α) (p : α) : Prop :=
  (3 : ℤ) ≤ ∑ c ∈ circlesThrough cfg p,
    (4 - (circleTrace cfg c.1).card : ℤ)

theorem sum_card_indicator {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] (S : β → Finset α) (w : β → ℤ) :
    (∑ p : α, ∑ b : β, if p ∈ S b then w b else 0) =
      ∑ b : β, (S b).card * w b := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b hb
  calc
    (∑ p : α, if p ∈ S b then w b else 0) =
        ∑ p ∈ S b, w b := by
      rw [← Finset.sum_filter]
      simp
    _ = (S b).card * w b := by simp

/-- Pure finite double counting: all pointwise pivot rows imply the summed
row used by the rational functional. -/
theorem summedMelchior_of_pivots {α : Type*} [Fintype α]
    (cfg : Configuration α) (hpivot : ∀ p : α, PivotMelchior cfg p) :
    SummedMelchior cfg := by
  classical
  have hsum :
      ∑ _p : α, (3 : ℤ) ≤
        ∑ p : α, ∑ c ∈ circlesThrough cfg p,
          (4 - (circleTrace cfg c.1).card : ℤ) :=
    Finset.sum_le_sum fun p _ => hpivot p
  have hrewrite :
      (∑ p : α, ∑ c ∈ circlesThrough cfg p,
          (4 - (circleTrace cfg c.1).card : ℤ)) =
        ∑ c : DeterminedCircle cfg,
          (circleTrace cfg c.1).card *
            (4 - (circleTrace cfg c.1).card : ℤ) := by
    have hrow (p : α) : (∑ c ∈ circlesThrough cfg p,
        (4 - (circleTrace cfg c.1).card : ℤ)) =
        ∑ c : DeterminedCircle cfg,
          if p ∈ circleTrace cfg c.1 then
            (4 - (circleTrace cfg c.1).card : ℤ) else 0 := by
      rw [← Finset.sum_filter]
      simp [circlesThrough]
    simp_rw [hrow]
    exact sum_card_indicator
      (fun c : DeterminedCircle cfg => circleTrace cfg c.1)
      (fun c => (4 - (circleTrace cfg c.1).card : ℤ))
  simp only [Finset.sum_const, Finset.card_univ] at hsum
  rw [hrewrite] at hsum
  have hsum' : (3 : ℤ) * Fintype.card α ≤
      ∑ c : DeterminedCircle cfg,
        (circleTrace cfg c.1).card *
          (4 - (circleTrace cfg c.1).card : ℤ) := by
    simpa [nsmul_eq_mul, mul_comm] using hsum
  change 3 * (Fintype.card α : ℚ) ≤
    ∑ c : DeterminedCircle cfg,
      (circleTrace cfg c.1).card *
        (4 - (circleTrace cfg c.1).card : ℚ)
  exact_mod_cast hsum'

end Erdos506.V3
