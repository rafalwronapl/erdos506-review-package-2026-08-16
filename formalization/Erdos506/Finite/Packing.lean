import Erdos506.Finite.KSubset
import Mathlib.Data.Finset.Powerset
import Mathlib.Tactic

/-!
# A finite packing bound

If distinct blocks have intersection smaller than `t`, their `t`-subsets
are pairwise disjoint.  Counting those subsets gives the standard packing
bound used by the small V3 cases.
-/

namespace Erdos506.Finite

open scoped BigOperators

theorem card_mul_choose_le_choose_of_pairwise_inter_lt
    {α : Type*} [DecidableEq α]
    (G : Finset α) (P : Finset (Finset α)) (k t : ℕ)
    (hsub : ∀ p ∈ P, p ⊆ G)
    (hcard : ∀ p ∈ P, p.card = k)
    (hinter : ∀ p ∈ P, ∀ q ∈ P, p ≠ q → (p ∩ q).card < t) :
    P.card * Nat.choose k t ≤ Nat.choose G.card t := by
  classical
  let F : Finset α → Finset (Finset α) := fun p => p.powersetCard t
  have hdisj : (P : Set (Finset α)).PairwiseDisjoint F := by
    intro p hp q hq hpq
    change Disjoint (F p) (F q)
    rw [Finset.disjoint_left]
    intro A hAp hAq
    have hAp' := Finset.mem_powersetCard.mp hAp
    have hAq' := Finset.mem_powersetCard.mp hAq
    have hAinter : A ⊆ p ∩ q := by
      intro x hx
      exact Finset.mem_inter.mpr ⟨hAp'.1 hx, hAq'.1 hx⟩
    have hle := Finset.card_le_card hAinter
    rw [hAp'.2] at hle
    exact (Nat.not_le_of_lt (hinter p hp q hq hpq)) hle
  have hunionSub : P.biUnion F ⊆ G.powersetCard t := by
    intro A hA
    rcases Finset.mem_biUnion.mp hA with ⟨p, hp, hAp⟩
    have hAp' := Finset.mem_powersetCard.mp hAp
    exact Finset.mem_powersetCard.mpr ⟨hAp'.1.trans (hsub p hp), hAp'.2⟩
  have hunionCard : (P.biUnion F).card = P.card * Nat.choose k t := by
    rw [Finset.card_biUnion hdisj]
    calc
      (∑ p ∈ P, (F p).card) = ∑ _p ∈ P, Nat.choose k t := by
        apply Finset.sum_congr rfl
        intro p hp
        simp only [F, Finset.card_powersetCard]
        rw [hcard p hp]
      _ = P.card * Nat.choose k t := by simp
  have hle := Finset.card_le_card hunionSub
  rw [hunionCard, Finset.card_powersetCard] at hle
  exact hle

/-- Equality in the packing bound means that every `t`-subset of the ground
set belongs to exactly one block. -/
theorem existsUnique_block_of_packing_equality
    {α : Type*} [DecidableEq α]
    (G : Finset α) (P : Finset (Finset α)) (k t : ℕ)
    (hsub : ∀ p ∈ P, p ⊆ G)
    (hcard : ∀ p ∈ P, p.card = k)
    (hinter : ∀ p ∈ P, ∀ q ∈ P, p ≠ q → (p ∩ q).card < t)
    (heq : P.card * Nat.choose k t = Nat.choose G.card t)
    {A : Finset α} (hA : A ∈ G.powersetCard t) :
    ∃! p : Finset α, p ∈ P ∧ A ⊆ p := by
  classical
  let F : Finset α → Finset (Finset α) := fun p => p.powersetCard t
  have hdisj : (P : Set (Finset α)).PairwiseDisjoint F := by
    intro p hp q hq hpq
    change Disjoint (F p) (F q)
    rw [Finset.disjoint_left]
    intro B hBp hBq
    have hBp' := Finset.mem_powersetCard.mp hBp
    have hBq' := Finset.mem_powersetCard.mp hBq
    have hBinter : B ⊆ p ∩ q := by
      intro x hx
      exact Finset.mem_inter.mpr ⟨hBp'.1 hx, hBq'.1 hx⟩
    have hle := Finset.card_le_card hBinter
    rw [hBp'.2] at hle
    exact (Nat.not_le_of_lt (hinter p hp q hq hpq)) hle
  have hunionSub : P.biUnion F ⊆ G.powersetCard t := by
    intro B hB
    rcases Finset.mem_biUnion.mp hB with ⟨p, hp, hBp⟩
    have hBp' := Finset.mem_powersetCard.mp hBp
    exact Finset.mem_powersetCard.mpr ⟨hBp'.1.trans (hsub p hp), hBp'.2⟩
  have hunionCard : (P.biUnion F).card = P.card * Nat.choose k t := by
    rw [Finset.card_biUnion hdisj]
    calc
      (∑ p ∈ P, (F p).card) = ∑ _p ∈ P, Nat.choose k t := by
        apply Finset.sum_congr rfl
        intro p hp
        simp only [F, Finset.card_powersetCard]
        rw [hcard p hp]
      _ = P.card * Nat.choose k t := by simp
  have hunionEq : P.biUnion F = G.powersetCard t := by
    apply Finset.eq_of_subset_of_card_le hunionSub
    rw [hunionCard, Finset.card_powersetCard, heq]
  have hAunion : A ∈ P.biUnion F := by
    rw [hunionEq]
    exact hA
  rcases Finset.mem_biUnion.mp hAunion with ⟨p, hp, hAp⟩
  refine ⟨p, ⟨hp, (Finset.mem_powersetCard.mp hAp).1⟩, ?_⟩
  intro q hq
  by_contra hpq
  have hAinter : A ⊆ p ∩ q := by
    intro x hx
    exact Finset.mem_inter.mpr ⟨(Finset.mem_powersetCard.mp hAp).1 hx, hq.2 hx⟩
  have hle := Finset.card_le_card hAinter
  rw [(Finset.mem_powersetCard.mp hAp).2] at hle
  exact (Nat.not_le_of_lt (hinter p hp q hq.1 (Ne.symm hpq))) hle

end Erdos506.Finite
