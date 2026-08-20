import Erdos506.Finite.KFiveNearOneFactorization

/-!
# The two simultaneous orbits of near-one-factorizations of `K5`

After one labelled near-one-factorization is put in canonical form, its
vertex stabilizer has order twenty.  It fixes that table and is transitive
on the other five labelled tables.  Consequently a second factorization has
only two simultaneous normal forms: the same table or the cyclic (twisted)
table.

The action below is defined on whole chord families.  It therefore does not
depend on the auxiliary numbering of the three row choices used by the
finite certificate.
-/

namespace Erdos506.Finite

/-- Apply a permutation of the five vertices to a labelled chord. -/
def kFivePermuteChordEquiv (σ : Equiv.Perm (Fin 5)) :
    FinFiveChord ≃ FinFiveChord where
  toFun e :=
    ⟨e.1.map σ.toEmbedding, by
      rw [Finset.mem_powersetCard]
      refine ⟨Finset.subset_univ _, ?_⟩
      rw [Finset.card_map]
      exact (Finset.mem_powersetCard.mp e.2).2⟩
  invFun e :=
    ⟨e.1.map σ.symm.toEmbedding, by
      rw [Finset.mem_powersetCard]
      refine ⟨Finset.subset_univ _, ?_⟩
      rw [Finset.card_map]
      exact (Finset.mem_powersetCard.mp e.2).2⟩
  left_inv e := by
    apply Subtype.ext
    ext x
    simp
  right_inv e := by
    apply Subtype.ext
    ext x
    simp

/-- Simultaneously relabel vertices and omitted colours in a chord family. -/
def kFivePermuteFactorFamily (σ : Equiv.Perm (Fin 5))
    (F : Fin 5 → Finset FinFiveChord) :
    Fin 5 → Finset FinFiveChord :=
  fun c =>
    (F (σ.symm c)).map (kFivePermuteChordEquiv σ).toEmbedding

/-- The first, already normalized, factorization. -/
def kFiveCanonicalFactorFamily : Fin 5 → Finset FinFiveChord :=
  kFiveCodedFactor kFiveCanonicalNearOneFactorizationCode.rowChoice

/-- The representative for a second factorization distinct from the first. -/
def kFiveTwistedFactorFamily : Fin 5 → Finset FinFiveChord :=
  kFiveCodedFactor kFiveCyclicNearOneFactorizationCode.rowChoice

/-- A vertex permutation belongs to the stabilizer of the canonical table. -/
def KFivePreservesCanonical (σ : Equiv.Perm (Fin 5)) : Prop :=
  kFivePermuteFactorFamily σ kFiveCanonicalFactorFamily =
    kFiveCanonicalFactorFamily

private instance (σ : Equiv.Perm (Fin 5)) :
    Decidable (KFivePreservesCanonical σ) := by
  unfold KFivePreservesCanonical
  infer_instance

/-- The full vertex stabilizer of the canonical near-one-factorization. -/
def kFiveCanonicalStabilizer : Finset (Equiv.Perm (Fin 5)) :=
  Finset.univ.filter KFivePreservesCanonical

@[simp] theorem mem_kFiveCanonicalStabilizer
    (σ : Equiv.Perm (Fin 5)) :
    σ ∈ kFiveCanonicalStabilizer ↔ KFivePreservesCanonical σ := by
  simp [kFiveCanonicalStabilizer]

/-- The canonical table has the Frobenius stabilizer of order twenty. -/
theorem kFiveCanonicalStabilizer_card :
    kFiveCanonicalStabilizer.card = 20 := by
  decide +kernel

/-! ## Explicit normalizers for the five noncanonical tables -/

/-- The permutation `(1 2 3 4)`, fixing vertex zero. -/
def kFiveStabilizerCycle : Equiv.Perm (Fin 5) where
  toFun := (![0, 2, 3, 4, 1] : Fin 5 → Fin 5)
  invFun := (![0, 4, 1, 2, 3] : Fin 5 → Fin 5)
  left_inv := by decide +kernel
  right_inv := by decide +kernel

/-- The inverse of `kFiveStabilizerCycle`. -/
def kFiveStabilizerCycleInv : Equiv.Perm (Fin 5) :=
  kFiveStabilizerCycle.symm

/-- A reflection in the canonical stabilizer. -/
def kFiveStabilizerSwap : Equiv.Perm (Fin 5) where
  toFun := (![1, 0, 3, 2, 4] : Fin 5 → Fin 5)
  invFun := (![1, 0, 3, 2, 4] : Fin 5 → Fin 5)
  left_inv := by decide +kernel
  right_inv := by decide +kernel

/-- A second involution in the canonical stabilizer. -/
def kFiveStabilizerDoubleSwap : Equiv.Perm (Fin 5) where
  toFun := (![0, 3, 4, 1, 2] : Fin 5 → Fin 5)
  invFun := (![0, 3, 4, 1, 2] : Fin 5 → Fin 5)
  left_inv := by decide +kernel
  right_inv := by decide +kernel

/-- The five table indices different from the canonical index `3`. -/
def kFiveTwistedTableIndex : Fin 5 → Fin 6 :=
  ![0, 1, 2, 4, 5]

/--
For each noncanonical table, a canonical-stabilizer element which sends it
to the cyclic representative.  The order corresponds to
`kFiveTwistedTableIndex`.
-/
def kFiveTwistedNormalizer : Fin 5 → Equiv.Perm (Fin 5) := ![
  kFiveStabilizerCycleInv,
  kFiveStabilizerCycle,
  kFiveStabilizerSwap,
  kFiveStabilizerDoubleSwap,
  Equiv.refl (Fin 5)
]

theorem kFiveTableIndex_canonical_or_twisted :
    ∀ i : Fin 6, i = 3 ∨ ∃ j : Fin 5, i = kFiveTwistedTableIndex j := by
  decide +kernel

theorem kFiveTwistedNormalizer_preserves_canonical :
    ∀ j : Fin 5, KFivePreservesCanonical (kFiveTwistedNormalizer j) := by
  decide +kernel

theorem kFiveTwistedNormalizer_mem_stabilizer :
    ∀ j : Fin 5,
      kFiveTwistedNormalizer j ∈ kFiveCanonicalStabilizer := by
  intro j
  exact (mem_kFiveCanonicalStabilizer _).2
    (kFiveTwistedNormalizer_preserves_canonical j)

theorem kFiveTwistedNormalizer_sends_table_to_twisted :
    ∀ j : Fin 5,
      kFivePermuteFactorFamily (kFiveTwistedNormalizer j)
        (kFiveCodedFactor
          (kFiveNearOneFactorizationTable (kFiveTwistedTableIndex j))) =
        kFiveTwistedFactorFamily := by
  decide +kernel

/--
Once the first factorization is canonical, every checked second code is
either the same table or can be sent to the single twisted representative by
a permutation preserving the first table.
-/
theorem kFiveNearOneFactorizationCode_same_or_twisted
    (C : KFiveNearOneFactorizationCode) :
    C.rowChoice = kFiveCanonicalNearOneFactorizationCode.rowChoice ∨
      ∃ σ : Equiv.Perm (Fin 5),
        σ ∈ kFiveCanonicalStabilizer ∧
        kFivePermuteFactorFamily σ (kFiveCodedFactor C.rowChoice) =
          kFiveTwistedFactorFamily := by
  obtain ⟨i, hi⟩ :=
    (kFiveNearOneFactorizationCode_complete C.rowChoice).mp C.valid
  rcases kFiveTableIndex_canonical_or_twisted i with hi3 | ⟨j, hij⟩
  · left
    simpa [kFiveCanonicalNearOneFactorizationCode, hi3] using hi
  · right
    refine ⟨kFiveTwistedNormalizer j,
      kFiveTwistedNormalizer_mem_stabilizer j, ?_⟩
    rw [hi, hij]
    exact kFiveTwistedNormalizer_sends_table_to_twisted j

end Erdos506.Finite
