import Erdos506.Finite.UniformOwner

/-!
# Relative partitions for uniform owners

This module refines the global owner partition by recording how many points
of a uniform subset lie in a fixed finite set `D`.  The proof is an explicit
finite equivalence: split every subset into its part in `D` and its part
outside `D`.
-/

namespace Erdos506.Finite

open scoped BigOperators

/-- `k`-subsets of `U` having exactly `j` points in `D`. -/
abbrev RestrictedKSubset (Point : Type*) [Fintype Point] [DecidableEq Point]
    (U D : Finset Point) (k j : ℕ) :=
  {A : KSubset Point k // A.1 ⊆ U ∧ (A.1 ∩ D).card = j}

/-- Split a restricted `k`-subset into its `j` points in `D` and its
`k-j` points outside `D`. -/
noncomputable def restrictedKSubsetEquiv
    {Point : Type*} [Fintype Point] [DecidableEq Point]
    (U D : Finset Point) (k j : ℕ) (hj : j ≤ k) :
    RestrictedKSubset Point U D k j ≃
      ↥((U ∩ D).powersetCard j) × ↥((U \ D).powersetCard (k - j)) where
  toFun A := by
    refine (⟨A.1.1 ∩ D, ?_⟩, ⟨A.1.1 \ D, ?_⟩)
    · apply Finset.mem_powersetCard.mpr
      exact ⟨by
        intro x hx
        have hx' := Finset.mem_inter.mp hx
        exact Finset.mem_inter.mpr ⟨A.2.1 hx'.1, hx'.2⟩, A.2.2⟩
    · apply Finset.mem_powersetCard.mpr
      refine ⟨?_, ?_⟩
      · intro x hx
        have hx' := Finset.mem_sdiff.mp hx
        exact Finset.mem_sdiff.mpr ⟨A.2.1 hx'.1, hx'.2⟩
      · rw [Finset.card_sdiff, Finset.inter_comm, A.1.2, A.2.2]
  invFun UV := by
    let A : Finset Point := UV.1.1 ∪ UV.2.1
    have hUin : UV.1.1 ⊆ U ∩ D := (Finset.mem_powersetCard.mp UV.1.2).1
    have hUcard : UV.1.1.card = j := (Finset.mem_powersetCard.mp UV.1.2).2
    have hVout : UV.2.1 ⊆ U \ D := (Finset.mem_powersetCard.mp UV.2.2).1
    have hVcard : UV.2.1.card = k - j :=
      (Finset.mem_powersetCard.mp UV.2.2).2
    have hdis : Disjoint UV.1.1 UV.2.1 := by
      apply Finset.disjoint_left.mpr
      intro x hxU hxV
      exact (Finset.mem_sdiff.mp (hVout hxV)).2
        (Finset.mem_inter.mp (hUin hxU)).2
    have hAcard : A.card = k := by
      change (UV.1.1 ∪ UV.2.1).card = k
      rw [Finset.card_union_of_disjoint hdis, hUcard, hVcard]
      omega
    refine ⟨⟨A, hAcard⟩, ?_, ?_⟩
    · intro x hx
      rcases Finset.mem_union.mp hx with hxU | hxV
      · exact (Finset.mem_inter.mp (hUin hxU)).1
      · exact (Finset.mem_sdiff.mp (hVout hxV)).1
    · have hAD : A ∩ D = UV.1.1 := by
        ext x
        constructor
        · intro hx
          have hx' := Finset.mem_inter.mp hx
          rcases Finset.mem_union.mp hx'.1 with hxU | hxV
          · exact hxU
          · exact ((Finset.mem_sdiff.mp (hVout hxV)).2 hx'.2).elim
        · intro hxU
          exact Finset.mem_inter.mpr
            ⟨Finset.mem_union_left _ hxU,
              (Finset.mem_inter.mp (hUin hxU)).2⟩
      rw [hAD, hUcard]
  left_inv A := by
    apply Subtype.ext
    apply Subtype.ext
    ext x
    by_cases hxD : x ∈ D <;> simp [hxD]
  right_inv UV := by
    rcases UV with ⟨Uin, Vout⟩
    apply Prod.ext
    · apply Subtype.ext
      ext x
      have hUin : Uin.1 ⊆ U ∩ D :=
        (Finset.mem_powersetCard.mp Uin.2).1
      have hVout : Vout.1 ⊆ U \ D :=
        (Finset.mem_powersetCard.mp Vout.2).1
      constructor
      · intro hx
        have hx' := Finset.mem_inter.mp hx
        rcases Finset.mem_union.mp hx'.1 with hxU | hxV
        · exact hxU
        · exact ((Finset.mem_sdiff.mp (hVout hxV)).2 hx'.2).elim
      · intro hxU
        exact Finset.mem_inter.mpr
          ⟨Finset.mem_union_left _ hxU,
            (Finset.mem_inter.mp (hUin hxU)).2⟩
    · apply Subtype.ext
      ext x
      have hUin : Uin.1 ⊆ U ∩ D :=
        (Finset.mem_powersetCard.mp Uin.2).1
      have hVout : Vout.1 ⊆ U \ D :=
        (Finset.mem_powersetCard.mp Vout.2).1
      constructor
      · intro hx
        have hx' := Finset.mem_sdiff.mp hx
        rcases Finset.mem_union.mp hx'.1 with hxU | hxV
        · exact (hx'.2 (Finset.mem_inter.mp (hUin hxU)).2).elim
        · exact hxV
      · intro hxV
        exact Finset.mem_sdiff.mpr
          ⟨Finset.mem_union_right _ hxV,
            (Finset.mem_sdiff.mp (hVout hxV)).2⟩

theorem card_restrictedKSubset
    {Point : Type*} [Fintype Point] [DecidableEq Point]
    (U D : Finset Point) (k j : ℕ) (hj : j ≤ k) :
    Fintype.card (RestrictedKSubset Point U D k j) =
      Nat.choose (U ∩ D).card j * Nat.choose (U \ D).card (k - j) := by
  classical
  calc
    Fintype.card (RestrictedKSubset Point U D k j) =
        Fintype.card
          (↥((U ∩ D).powersetCard j) × ↥((U \ D).powersetCard (k - j))) :=
      Fintype.card_congr (restrictedKSubsetEquiv U D k j hj)
    _ = Nat.choose (U ∩ D).card j *
        Nat.choose (U \ D).card (k - j) := by
      rw [Fintype.card_prod, Fintype.card_coe, Fintype.card_coe]
      simp

namespace UniformOwner

variable {Point Block : Type*} [Fintype Point] [Fintype Block]
  [DecidableEq Point] {k : ℕ}

/-- Owner flags restricted by the number of selected points in `D`. -/
abbrev RelativeOwnerFlag (O : UniformOwner Point Block k)
    (D : Finset Point) (j : ℕ) :=
  Σ b : Block, RestrictedKSubset Point (O.support b) D k j

/-- Forgetting the owner remains an equivalence after imposing the
intersection-cardinality condition. -/
noncomputable def relativeOwnerFlagEquiv
    (O : UniformOwner Point Block k) (D : Finset Point) (j : ℕ) :
    RestrictedKSubset Point Finset.univ D k j ≃ RelativeOwnerFlag O D j where
  toFun A := ⟨O.owner A.1, ⟨A.1, O.owner_contains A.1, A.2.2⟩⟩
  invFun f := ⟨f.2.1, Finset.subset_univ _, f.2.2.2⟩
  left_inv A := by ext; rfl
  right_inv := by
    rintro ⟨b, ⟨A, hsub, hrel⟩⟩
    have hb : b = O.owner A := O.owner_unique A b hsub
    subst b
    rfl

/-- Relative owner partition.  It simultaneously contains the global,
pivot, pair-extension, and selected-block triple rows. -/
theorem relative_owner_partition (O : UniformOwner Point Block k)
    (D : Finset Point) (j : ℕ) (hj : j ≤ k) :
    (∑ b : Block,
        Nat.choose (O.support b ∩ D).card j *
          Nat.choose (O.support b \ D).card (k - j)) =
      Nat.choose D.card j *
        Nat.choose (Fintype.card Point - D.card) (k - j) := by
  classical
  have hcard := Fintype.card_congr (O.relativeOwnerFlagEquiv D j)
  rw [Fintype.card_sigma] at hcard
  simp_rw [card_restrictedKSubset _ _ _ _ hj] at hcard
  simpa only [Finset.univ_inter, Finset.card_univ,
    Finset.card_sdiff_of_subset (Finset.subset_univ D)] using hcard.symm

end UniformOwner
end Erdos506.Finite
