import Erdos506.Finite.KSubset
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.BigOperators

/-!
# Unique owners of uniform finite subsets

The structure in this module records an explicit owner for every unordered
`k`-subset.  All results are finite double counts and contain no geometry.
-/

namespace Erdos506.Finite

open scoped BigOperators

structure UniformOwner (Point Block : Type*) [Fintype Point] [Fintype Block]
    [DecidableEq Point] (k : ℕ) where
  support : Block → Finset Point
  owner : KSubset Point k → Block
  owner_contains : ∀ A, A.1 ⊆ support (owner A)
  owner_unique : ∀ A b, A.1 ⊆ support b → b = owner A

namespace UniformOwner

variable {Point Block : Type*} [Fintype Point] [Fintype Block]
  [DecidableEq Point] {k : ℕ}

theorem subset_support_iff_eq_owner (O : UniformOwner Point Block k)
    (A : KSubset Point k) (b : Block) :
    A.1 ⊆ O.support b ↔ b = O.owner A := by
  constructor
  · exact O.owner_unique A b
  · rintro rfl
    exact O.owner_contains A

/-- Owner flags consist of a block and a uniform subset contained in its
support. -/
abbrev OwnerFlag (O : UniformOwner Point Block k) :=
  Σ b : Block, {A : KSubset Point k // A.1 ⊆ O.support b}

/-- Forgetting the owner from a flag is an equivalence: uniqueness recovers
it. -/
noncomputable def ownerFlagEquiv (O : UniformOwner Point Block k) :
    KSubset Point k ≃ OwnerFlag O where
  toFun A := ⟨O.owner A, ⟨A, O.owner_contains A⟩⟩
  invFun f := f.2.1
  left_inv A := rfl
  right_inv := by
    rintro ⟨b, ⟨A, hA⟩⟩
    have hb : b = O.owner A := O.owner_unique A b hA
    subst b
    rfl

noncomputable def ownerFiberEquivPowersetCard
    (O : UniformOwner Point Block k) (b : Block) :
    {A : KSubset Point k // A.1 ⊆ O.support b} ≃
      {s : Finset Point // s ∈ (O.support b).powersetCard k} where
  toFun A :=
    ⟨A.1.1, Finset.mem_powersetCard.mpr ⟨A.2, A.1.2⟩⟩
  invFun s :=
    ⟨⟨s.1, (Finset.mem_powersetCard.mp s.2).2⟩,
      (Finset.mem_powersetCard.mp s.2).1⟩
  left_inv A := by ext; rfl
  right_inv s := by ext; rfl

theorem card_ownerFiber (O : UniformOwner Point Block k) (b : Block) :
    Fintype.card {A : KSubset Point k // A.1 ⊆ O.support b} =
      Nat.choose (O.support b).card k := by
  classical
  calc
    Fintype.card {A : KSubset Point k // A.1 ⊆ O.support b} =
        Fintype.card ↥((O.support b).powersetCard k) :=
      Fintype.card_congr (ownerFiberEquivPowersetCard O b)
    _ = ((O.support b).powersetCard k).card := Fintype.card_coe _
    _ = Nat.choose (O.support b).card k := by simp

/-- Global owner partition: every `k`-subset appears in exactly one support. -/
theorem sum_choose_support_card (O : UniformOwner Point Block k) :
    (∑ b : Block, Nat.choose (O.support b).card k) =
      Nat.choose (Fintype.card Point) k := by
  classical
  have hcard := Fintype.card_congr (ownerFlagEquiv O)
  rw [card_kSubset] at hcard
  rw [Fintype.card_sigma] at hcard
  simp_rw [card_ownerFiber] at hcard
  exact hcard.symm

/-- Distinct owners cannot have `k` common points. -/
theorem card_inter_lt_of_ne (O : UniformOwner Point Block k)
    {b c : Block} (hbc : b ≠ c) :
    (O.support b ∩ O.support c).card < k := by
  classical
  by_contra hnot
  have hk : k ≤ (O.support b ∩ O.support c).card := Nat.le_of_not_gt hnot
  obtain ⟨A, hA, hAcard⟩ := Finset.exists_subset_card_eq hk
  let Ak : KSubset Point k := ⟨A, hAcard⟩
  have hAb : A ⊆ O.support b := hA.trans Finset.inter_subset_left
  have hAc : A ⊆ O.support c := hA.trans Finset.inter_subset_right
  have hb : b = O.owner Ak := O.owner_unique Ak b hAb
  have hc : c = O.owner Ak := O.owner_unique Ak c hAc
  exact hbc (hb.trans hc.symm)

end UniformOwner
end Erdos506.Finite
