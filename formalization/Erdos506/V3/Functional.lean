import Erdos506.V3.Arithmetic
import Erdos506.V3.Model

/-!
# The bounded-support V3 functional

This module isolates the exact consequence of the triple partition and the
summed Melchior row.  The latter remains a named geometric proposition until
the project-owned real-arrangement proof supplies it.
-/

namespace Erdos506.V3

open Erdos506.V4
open scoped BigOperators

/-- The summed inverted-Melchior inequality in its coefficient form. -/
def SummedMelchior {α : Type*} [Fintype α] (cfg : Configuration α) : Prop :=
  3 * (Fintype.card α : ℚ) ≤
    ∑ c : DeterminedCircle cfg,
      (circleTrace cfg c.1).card * (4 - (circleTrace cfg c.1).card : ℚ)

def circleFunctionalCoefficient (m s : ℚ) : ℚ :=
  functionalLambda m * chooseThreeQ s - functionalMu m * s * (s - 4)

theorem circleFunctionalCoefficient_at_three (m : ℚ) (hm : 4 ≤ m) :
    circleFunctionalCoefficient m 3 = 1 := by
  have h := functional_normalization m hm
  norm_num [circleFunctionalCoefficient, chooseThreeQ]
  linarith

theorem circleFunctionalCoefficient_le_one (m : ℕ) (hm : 4 ≤ m)
    (s : ℕ) (hs : 3 ≤ s) (hsm : s ≤ m) :
    circleFunctionalCoefficient (m : ℚ) (s : ℚ) ≤ 1 := by
  by_cases hs3 : s = 3
  · subst s
    exact le_of_eq (circleFunctionalCoefficient_at_three (m : ℚ) (by exact_mod_cast hm))
  · have hs4 : 4 ≤ s := by omega
    exact functional_coefficient_le_one (m : ℚ) (s : ℚ)
      (by exact_mod_cast hm) (by exact_mod_cast hs4) (by exact_mod_cast hsm)

theorem triple_partition_rat {α : Type*} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (hthree : NoThreeCollinear cfg)
    (hcard : 3 ≤ Fintype.card α) :
    (∑ c : DeterminedCircle cfg,
        chooseThreeQ ((circleTrace cfg c.1).card : ℚ)) =
      chooseThreeQ (Fintype.card α : ℚ) := by
  simp_rw [chooseThreeQ_natCast _ (circleSupport_card_ge_three cfg _)]
  rw [chooseThreeQ_natCast _ hcard]
  exact_mod_cast triple_partition cfg hthree

/-- Conditional bounded-support lower bound.  The exact summed-Melchior
proposition is an explicit hypothesis; the public assembly obtains it from
the explicit `RealPlaneMelchiorPrinciple` contract. -/
theorem boundedSupportLower_le_circleCount {α : Type*} [Fintype α]
    [DecidableEq α] (cfg : Configuration α) (hthree : NoThreeCollinear cfg)
    (hcard : 4 ≤ Fintype.card α) (hmel : SummedMelchior cfg)
    (m : ℕ) (hm : 4 ≤ m)
    (hcap : ∀ c : DeterminedCircle cfg, (circleTrace cfg c.1).card ≤ m) :
    boundedSupportLowerQ (Fintype.card α : ℚ) (m : ℚ) ≤ circleCount cfg := by
  let T : ℚ := ∑ c : DeterminedCircle cfg,
    chooseThreeQ ((circleTrace cfg c.1).card : ℚ)
  let M : ℚ := ∑ c : DeterminedCircle cfg,
    (circleTrace cfg c.1).card * (4 - (circleTrace cfg c.1).card : ℚ)
  have hT : T = chooseThreeQ (Fintype.card α : ℚ) := by
    exact triple_partition_rat cfg hthree (by omega)
  have hmu : 0 ≤ functionalMu (m : ℚ) :=
    functionalMu_nonneg (m : ℚ) (by exact_mod_cast hm)
  have hM : 3 * (Fintype.card α : ℚ) ≤ M := hmel
  have hweighted :
      functionalLambda (m : ℚ) * T + functionalMu (m : ℚ) * M =
        ∑ c : DeterminedCircle cfg,
          circleFunctionalCoefficient (m : ℚ)
            ((circleTrace cfg c.1).card : ℚ) := by
    dsimp [T, M]
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro c hc
    simp only [circleFunctionalCoefficient]
    ring
  have hcoeff :
      (∑ c : DeterminedCircle cfg,
          circleFunctionalCoefficient (m : ℚ)
            ((circleTrace cfg c.1).card : ℚ)) ≤
        ∑ _c : DeterminedCircle cfg, (1 : ℚ) := by
    apply Finset.sum_le_sum
    intro c hc
    exact circleFunctionalCoefficient_le_one m hm _
      (circleSupport_card_ge_three cfg c) (hcap c)
  have hstart :
      boundedSupportLowerQ (Fintype.card α : ℚ) (m : ℚ) ≤
        functionalLambda (m : ℚ) * T + functionalMu (m : ℚ) * M := by
    rw [boundedSupportLowerQ, hT]
    have hmul := mul_le_mul_of_nonneg_left hM hmu
    nlinarith
  calc
    boundedSupportLowerQ (Fintype.card α : ℚ) (m : ℚ) ≤
        functionalLambda (m : ℚ) * T + functionalMu (m : ℚ) * M := hstart
    _ = ∑ c : DeterminedCircle cfg,
          circleFunctionalCoefficient (m : ℚ)
            ((circleTrace cfg c.1).card : ℚ) := hweighted
    _ ≤ ∑ _c : DeterminedCircle cfg, (1 : ℚ) := hcoeff
    _ = Fintype.card (DeterminedCircle cfg) := by simp
    _ = circleCount cfg := by
      exact_mod_cast (circleCount_eq_card_determinedCircle cfg).symm

end Erdos506.V3
