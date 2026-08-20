import Erdos506.Finite.SixFiveNormalization

/-!
# Canonical form of the six-by-five design

The finite certificate leaves six cases because the first three block labels
are fixed while the last three may be permuted.  Here those six cases are
reduced to one canonical profile family, and the ten point labels are then
reordered to match that family exactly.
-/

namespace Erdos506.Finite

def sixFiveCanonicalProfile : Fin 10 → Finset (Fin 6) := ![
  {0, 1, 2},
  {0, 1, 3},
  {0, 2, 4},
  {1, 2, 5},
  {0, 3, 5},
  {0, 4, 5},
  {1, 3, 4},
  {1, 4, 5},
  {2, 3, 4},
  {2, 3, 5}
]

theorem sixFiveCanonicalProfile_injective :
    Function.Injective sixFiveCanonicalProfile := by
  intro i j h
  fin_cases i <;> fin_cases j
  all_goals try rfl
  all_goals
    exfalso
    revert h
    decide +kernel

theorem sixFiveProfileInSet0_iff_exists_canonical :
    ∀ S : Finset (Fin 6),
      sixFiveProfileInSet0 S ↔ ∃ i, S = sixFiveCanonicalProfile i := by
  intro S
  constructor
  · intro h
    rcases h with h | h | h | h | h | h | h | h | h | h
    · exact ⟨0, h.trans (by decide_cbv)⟩
    · exact ⟨1, h.trans (by decide_cbv)⟩
    · exact ⟨2, h.trans (by decide_cbv)⟩
    · exact ⟨6, h.trans (by decide_cbv)⟩
    · exact ⟨8, h.trans (by decide_cbv)⟩
    · exact ⟨3, h.trans (by decide_cbv)⟩
    · exact ⟨4, h.trans (by decide_cbv)⟩
    · exact ⟨9, h.trans (by decide_cbv)⟩
    · exact ⟨5, h.trans (by decide_cbv)⟩
    · exact ⟨7, h.trans (by decide_cbv)⟩
  · rintro ⟨i, rfl⟩
    fin_cases i <;> unfold sixFiveProfileInSet0 <;> decide_cbv

def sixFiveBlockPerm0 : Fin 6 ≃ Fin 6 :=
  { toFun := (![0, 1, 2, 3, 4, 5] : Fin 6 → Fin 6)
    invFun := (![0, 1, 2, 3, 4, 5] : Fin 6 → Fin 6)
    left_inv := by decide_cbv
    right_inv := by decide_cbv }

def sixFiveBlockPerm1 : Fin 6 ≃ Fin 6 :=
  { toFun := (![0, 1, 2, 3, 5, 4] : Fin 6 → Fin 6)
    invFun := (![0, 1, 2, 3, 5, 4] : Fin 6 → Fin 6)
    left_inv := by decide_cbv
    right_inv := by decide_cbv }

def sixFiveBlockPerm2 : Fin 6 ≃ Fin 6 :=
  { toFun := (![0, 1, 2, 4, 3, 5] : Fin 6 → Fin 6)
    invFun := (![0, 1, 2, 4, 3, 5] : Fin 6 → Fin 6)
    left_inv := by decide_cbv
    right_inv := by decide_cbv }

def sixFiveBlockPerm3 : Fin 6 ≃ Fin 6 :=
  { toFun := (![0, 1, 2, 5, 3, 4] : Fin 6 → Fin 6)
    invFun := (![0, 1, 2, 4, 5, 3] : Fin 6 → Fin 6)
    left_inv := by decide_cbv
    right_inv := by decide_cbv }

def sixFiveBlockPerm4 : Fin 6 ≃ Fin 6 :=
  { toFun := (![0, 1, 2, 4, 5, 3] : Fin 6 → Fin 6)
    invFun := (![0, 1, 2, 5, 3, 4] : Fin 6 → Fin 6)
    left_inv := by decide_cbv
    right_inv := by decide_cbv }

def sixFiveBlockPerm5 : Fin 6 ≃ Fin 6 :=
  { toFun := (![0, 1, 2, 5, 4, 3] : Fin 6 → Fin 6)
    invFun := (![0, 1, 2, 5, 4, 3] : Fin 6 → Fin 6)
    left_inv := by decide_cbv
    right_inv := by decide_cbv }

def sixFivePermuteProfile (π : Fin 6 ≃ Fin 6)
    (S : Finset (Fin 6)) : Finset (Fin 6) :=
  S.map π.toEmbedding

theorem sixFivePermuteProfile_set0 :
    ∀ S, sixFiveProfileInSet0 S →
      sixFiveProfileInSet0 (sixFivePermuteProfile sixFiveBlockPerm0 S) := by
  intro S h
  rcases h with h | h | h | h | h | h | h | h | h | h <;>
    subst S <;> unfold sixFiveProfileInSet0 <;> decide_cbv

theorem sixFivePermuteProfile_set1 :
    ∀ S, sixFiveProfileInSet1 S →
      sixFiveProfileInSet0 (sixFivePermuteProfile sixFiveBlockPerm1 S) := by
  intro S h
  rcases h with h | h | h | h | h | h | h | h | h | h <;>
    subst S <;> unfold sixFiveProfileInSet0 <;> decide_cbv

theorem sixFivePermuteProfile_set2 :
    ∀ S, sixFiveProfileInSet2 S →
      sixFiveProfileInSet0 (sixFivePermuteProfile sixFiveBlockPerm2 S) := by
  intro S h
  rcases h with h | h | h | h | h | h | h | h | h | h <;>
    subst S <;> unfold sixFiveProfileInSet0 <;> decide_cbv

theorem sixFivePermuteProfile_set3 :
    ∀ S, sixFiveProfileInSet3 S →
      sixFiveProfileInSet0 (sixFivePermuteProfile sixFiveBlockPerm3 S) := by
  intro S h
  rcases h with h | h | h | h | h | h | h | h | h | h <;>
    subst S <;> unfold sixFiveProfileInSet0 <;> decide_cbv

theorem sixFivePermuteProfile_set4 :
    ∀ S, sixFiveProfileInSet4 S →
      sixFiveProfileInSet0 (sixFivePermuteProfile sixFiveBlockPerm4 S) := by
  intro S h
  rcases h with h | h | h | h | h | h | h | h | h | h <;>
    subst S <;> unfold sixFiveProfileInSet0 <;> decide_cbv

theorem sixFivePermuteProfile_set5 :
    ∀ S, sixFiveProfileInSet5 S →
      sixFiveProfileInSet0 (sixFivePermuteProfile sixFiveBlockPerm5 S) := by
  intro S h
  rcases h with h | h | h | h | h | h | h | h | h | h <;>
    subst S <;> unfold sixFiveProfileInSet0 <;> decide_cbv

theorem SixFiveDesign.relabeledProfiles_relabelBlocks
    {Point Block : Type*} [Fintype Point] [DecidableEq Point]
    [Fintype Block] [DecidableEq Block]
    (D : SixFiveDesign Point Block)
    (P : Fin 10 ≃ Point) (B : Fin 6 ≃ Block) (π : Fin 6 ≃ Fin 6)
    (i : Fin 10) :
    D.relabeledProfiles P (π.symm.trans B) i =
      sixFivePermuteProfile π (D.relabeledProfiles P B i) := by
  ext j
  simp [SixFiveDesign.relabeledProfiles, sixFivePermuteProfile]

theorem SixFiveDesign.exists_set0_labeling
    {Point Block : Type*} [Fintype Point] [DecidableEq Point]
    [Fintype Block] [DecidableEq Block]
    (D : SixFiveDesign Point Block) :
    ∃ (P : Fin 10 ≃ Point) (B : Fin 6 ≃ Block),
      ∀ i, sixFiveProfileInSet0 (D.relabeledProfiles P B i) := by
  obtain ⟨P, B, hclass⟩ := D.exists_classified_labeling
  rcases hclass with h0 | h1 | h2 | h3 | h4 | h5
  · refine ⟨P, sixFiveBlockPerm0.symm.trans B, ?_⟩
    intro i
    rw [D.relabeledProfiles_relabelBlocks]
    exact sixFivePermuteProfile_set0 _ (h0 i)
  · refine ⟨P, sixFiveBlockPerm1.symm.trans B, ?_⟩
    intro i
    rw [D.relabeledProfiles_relabelBlocks]
    exact sixFivePermuteProfile_set1 _ (h1 i)
  · refine ⟨P, sixFiveBlockPerm2.symm.trans B, ?_⟩
    intro i
    rw [D.relabeledProfiles_relabelBlocks]
    exact sixFivePermuteProfile_set2 _ (h2 i)
  · refine ⟨P, sixFiveBlockPerm3.symm.trans B, ?_⟩
    intro i
    rw [D.relabeledProfiles_relabelBlocks]
    exact sixFivePermuteProfile_set3 _ (h3 i)
  · refine ⟨P, sixFiveBlockPerm4.symm.trans B, ?_⟩
    intro i
    rw [D.relabeledProfiles_relabelBlocks]
    exact sixFivePermuteProfile_set4 _ (h4 i)
  · refine ⟨P, sixFiveBlockPerm5.symm.trans B, ?_⟩
    intro i
    rw [D.relabeledProfiles_relabelBlocks]
    exact sixFivePermuteProfile_set5 _ (h5 i)

theorem exists_relabeling_to_sixFiveCanonicalProfile
    (R : Fin 10 → Finset (Fin 6)) (hRinj : Function.Injective R)
    (hset0 : ∀ i, sixFiveProfileInSet0 (R i)) :
    ∃ Q : Fin 10 ≃ Fin 10,
      ∀ i, R (Q i) = sixFiveCanonicalProfile i := by
  have hexists : ∀ i, ∃ k, R i = sixFiveCanonicalProfile k := by
    intro i
    exact (sixFiveProfileInSet0_iff_exists_canonical (R i)).mp (hset0 i)
  choose f hf using hexists
  have hfinj : Function.Injective f := by
    intro i k hik
    apply hRinj
    rw [hf i, hf k, hik]
  let E : Fin 10 ≃ Fin 10 :=
    Equiv.ofBijective f ⟨hfinj, Finite.injective_iff_surjective.mp hfinj⟩
  refine ⟨E.symm, ?_⟩
  intro i
  rw [hf]
  congr 1
  change E (E.symm i) = i
  exact E.apply_symm_apply i

theorem SixFiveDesign.exists_canonical_labeling
    {Point Block : Type*} [Fintype Point] [DecidableEq Point]
    [Fintype Block] [DecidableEq Block]
    (D : SixFiveDesign Point Block) :
    ∃ (P : Fin 10 ≃ Point) (B : Fin 6 ≃ Block),
      ∀ i, D.relabeledProfiles P B i = sixFiveCanonicalProfile i := by
  obtain ⟨P, B, hset0⟩ := D.exists_set0_labeling
  obtain ⟨Q, hQ⟩ := exists_relabeling_to_sixFiveCanonicalProfile
    (D.relabeledProfiles P B) (D.relabeledProfiles_valid P B).2.2.2 hset0
  refine ⟨Q.trans P, B, ?_⟩
  intro i
  simpa [SixFiveDesign.relabeledProfiles] using hQ i

end Erdos506.Finite
