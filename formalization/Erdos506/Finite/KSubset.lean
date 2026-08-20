import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Powerset

/-!
# Uniform finite subsets

This module packages unordered `k`-subsets of a finite type.  It is the
geometry-free indexing object for pair and triple ownership.
-/

namespace Erdos506.Finite

/-- An unordered `k`-element subset of `α`. -/
abbrev KSubset (α : Type*) [DecidableEq α] (k : ℕ) :=
  {s : Finset α // s.card = k}

/-- Uniform subsets are equivalent to the attached `powersetCard` of the
universal finite set. -/
noncomputable def kSubsetEquivPowersetCard (α : Type*) [Fintype α]
    [DecidableEq α] (k : ℕ) :
    KSubset α k ≃ {s : Finset α // s ∈ Finset.univ.powersetCard k} where
  toFun s := ⟨s.1, Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, s.2⟩⟩
  invFun s := ⟨s.1, (Finset.mem_powersetCard.mp s.2).2⟩
  left_inv s := by ext; rfl
  right_inv s := by ext; rfl

theorem card_kSubset (α : Type*) [Fintype α] [DecidableEq α] (k : ℕ) :
    Fintype.card (KSubset α k) = Nat.choose (Fintype.card α) k := by
  classical
  rw [Fintype.card_congr (kSubsetEquivPowersetCard α k)]
  simp

end Erdos506.Finite
