import Erdos506.Finite.SixFiveDesign
import Erdos506.Finite.SixFiveEncoding

/-!
# Normalizing a six-by-five design

This module relabels an abstract `SixFiveDesign` by `Fin 10` and `Fin 6`,
then chooses four distinguished points and three distinguished blocks that
meet the symmetry-breaking conditions of the checked finite classifier.
-/

namespace Erdos506.Finite

noncomputable def SixFiveDesign.relabeledProfiles
    {Point Block : Type*} [Fintype Point] [DecidableEq Point]
    [Fintype Block] [DecidableEq Block]
    (D : SixFiveDesign Point Block)
    (P : Fin 10 ≃ Point) (B : Fin 6 ≃ Block) :
    Fin 10 → Finset (Fin 6) :=
  fun i => (D.profile (P i)).preimage B B.injective.injOn

@[simp] theorem SixFiveDesign.mem_relabeledProfiles
    {Point Block : Type*} [Fintype Point] [DecidableEq Point]
    [Fintype Block] [DecidableEq Block]
    (D : SixFiveDesign Point Block)
    (P : Fin 10 ≃ Point) (B : Fin 6 ≃ Block) (i : Fin 10) (j : Fin 6) :
    j ∈ D.relabeledProfiles P B i ↔ P i ∈ D.support (B j) := by
  simp [SixFiveDesign.relabeledProfiles]

theorem card_preimage_equiv
    {α β : Type*} [Fintype α] [Fintype β]
    (e : α ≃ β) (S : Finset β) :
    (S.preimage e e.injective.injOn).card = S.card := by
  classical
  rw [Finset.card_preimage]
  simp

theorem SixFiveDesign.relabeledProfiles_valid
    {Point Block : Type*} [Fintype Point] [DecidableEq Point]
    [Fintype Block] [DecidableEq Block]
    (D : SixFiveDesign Point Block)
    (P : Fin 10 ≃ Point) (B : Fin 6 ≃ Block) :
    SixFiveProfilesValid (D.relabeledProfiles P B) := by
  classical
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i
    rw [SixFiveDesign.relabeledProfiles, card_preimage_equiv]
    exact D.card_profile (P i)
  · intro j
    let S : Finset (Fin 10) :=
      (D.support (B j)).preimage P P.injective.injOn
    have hS :
        ((Finset.univ : Finset (Fin 10)).filter
          (fun i => j ∈ D.relabeledProfiles P B i)) = S := by
      ext i
      simp [S]
    rw [hS, card_preimage_equiv]
    exact D.support_card (B j)
  · intro j k hjk
    let S : Finset (Fin 10) :=
      (D.support (B j) ∩ D.support (B k)).preimage P P.injective.injOn
    have hS :
        ((Finset.univ : Finset (Fin 10)).filter
          (fun i => j ∈ D.relabeledProfiles P B i ∧
            k ∈ D.relabeledProfiles P B i)) = S := by
      ext i
      simp [S]
    rw [hS, card_preimage_equiv]
    exact D.pair_inter_card (B j) (B k) (B.injective.ne hjk)
  · intro i k hprofiles
    apply P.injective
    apply D.profile_injective
    ext b
    obtain ⟨j, rfl⟩ := B.surjective b
    have hmem := Finset.ext_iff.mp hprofiles j
    simpa [SixFiveDesign.relabeledProfiles] using hmem

def finThreeEmbeddingSix : Fin 3 ↪ Fin 6 where
  toFun i := ⟨i.val, by omega⟩
  inj' := by
    intro i k h
    apply Fin.ext
    exact congrArg (fun x : Fin 6 => x.val) h

def finFourEmbeddingTen : Fin 4 ↪ Fin 10 where
  toFun i := ⟨i.val, by omega⟩
  inj' := by
    intro i k h
    apply Fin.ext
    exact congrArg (fun x : Fin 10 => x.val) h

theorem exists_mem_ne_of_card_eq_two
    {α : Type*} [DecidableEq α] (S : Finset α) (p : α)
    (hcard : S.card = 2) (hp : p ∈ S) :
    ∃ q ∈ S, q ≠ p := by
  obtain ⟨x, y, hxy, rfl⟩ := Finset.card_eq_two.mp hcard
  simp only [Finset.mem_insert, Finset.mem_singleton] at hp
  rcases hp with rfl | rfl
  · exact ⟨y, by simp, hxy.symm⟩
  · exact ⟨x, by simp, hxy⟩

theorem SixFiveDesign.exists_normalized_labeling
    {Point Block : Type*} [Fintype Point] [DecidableEq Point]
    [Fintype Block] [DecidableEq Block]
    (D : SixFiveDesign Point Block) :
    ∃ (P : Fin 10 ≃ Point) (B : Fin 6 ≃ Block),
      SixFiveProfilesNormalized (D.relabeledProfiles P B) := by
  classical
  let Pbase : Fin 10 ≃ Point := (Fintype.equivFinOfCardEq D.point_card).symm
  let p₀ : Point := Pbase 0
  let Eprof : D.profile p₀ ≃ Fin 3 :=
    Finset.equivFinOfCardEq (D.card_profile p₀)
  let b : Fin 3 → Block := fun i => (Eprof.symm i).1
  have hbmem (i : Fin 3) : b i ∈ D.profile p₀ := (Eprof.symm i).2
  have hbinj : Function.Injective b := by
    intro i k h
    apply Eprof.symm.injective
    exact Subtype.ext h
  let Bbase : Fin 6 ≃ Block := (Fintype.equivFinOfCardEq D.block_card).symm
  obtain ⟨σB, hσB⟩ := Equiv.Perm.exists_extending_pair
    (fun i : Fin 3 => Bbase (finThreeEmbeddingSix i)) b
    (Bbase.injective.comp finThreeEmbeddingSix.injective) hbinj
  let B : Fin 6 ≃ Block := Bbase.trans σB
  have hBfirst (i : Fin 3) : B (finThreeEmbeddingSix i) = b i := hσB i
  have hB0 : B 0 = b 0 := by simpa [finThreeEmbeddingSix] using hBfirst 0
  have hB1 : B 1 = b 1 := by simpa [finThreeEmbeddingSix] using hBfirst 1
  have hB2 : B 2 = b 2 := by simpa [finThreeEmbeddingSix] using hBfirst 2
  have hpB0 : p₀ ∈ D.support (B 0) := by
    apply (D.mem_profile p₀ (B 0)).mp
    rw [hB0]
    exact hbmem 0
  have hpB1 : p₀ ∈ D.support (B 1) := by
    apply (D.mem_profile p₀ (B 1)).mp
    rw [hB1]
    exact hbmem 1
  have hpB2 : p₀ ∈ D.support (B 2) := by
    apply (D.mem_profile p₀ (B 2)).mp
    rw [hB2]
    exact hbmem 2
  have hprofile₀ : D.profile p₀ = {B 0, B 1, B 2} := by
    symm
    apply Finset.eq_of_subset_of_card_le
    · intro c hc
      simp only [Finset.mem_insert, Finset.mem_singleton] at hc
      rcases hc with rfl | rfl | rfl
      · exact (D.mem_profile p₀ (B 0)).mpr hpB0
      · exact (D.mem_profile p₀ (B 1)).mpr hpB1
      · exact (D.mem_profile p₀ (B 2)).mpr hpB2
    · rw [D.card_profile]
      simp [B.injective.ne]

  have hpair01 := D.pair_inter_card (B 0) (B 1) (B.injective.ne (by decide))
  obtain ⟨p₀₁, hp₀₁, hp₀₁ne⟩ := exists_mem_ne_of_card_eq_two
    (D.support (B 0) ∩ D.support (B 1)) p₀ hpair01
    (Finset.mem_inter.mpr ⟨hpB0, hpB1⟩)
  have hp₀₁0 : p₀₁ ∈ D.support (B 0) := (Finset.mem_inter.mp hp₀₁).1
  have hp₀₁1 : p₀₁ ∈ D.support (B 1) := (Finset.mem_inter.mp hp₀₁).2
  have hpair02 := D.pair_inter_card (B 0) (B 2) (B.injective.ne (by decide))
  obtain ⟨p₀₂, hp₀₂, hp₀₂ne⟩ := exists_mem_ne_of_card_eq_two
    (D.support (B 0) ∩ D.support (B 2)) p₀ hpair02
    (Finset.mem_inter.mpr ⟨hpB0, hpB2⟩)
  have hp₀₂0 : p₀₂ ∈ D.support (B 0) := (Finset.mem_inter.mp hp₀₂).1
  have hp₀₂2 : p₀₂ ∈ D.support (B 2) := (Finset.mem_inter.mp hp₀₂).2
  have hpair12 := D.pair_inter_card (B 1) (B 2) (B.injective.ne (by decide))
  obtain ⟨p₁₂, hp₁₂, hp₁₂ne⟩ := exists_mem_ne_of_card_eq_two
    (D.support (B 1) ∩ D.support (B 2)) p₀ hpair12
    (Finset.mem_inter.mpr ⟨hpB1, hpB2⟩)
  have hp₁₂1 : p₁₂ ∈ D.support (B 1) := (Finset.mem_inter.mp hp₁₂).1
  have hp₁₂2 : p₁₂ ∈ D.support (B 2) := (Finset.mem_inter.mp hp₁₂).2

  have profile_eq_profile₀ (x : Point)
      (hx0 : x ∈ D.support (B 0))
      (hx1 : x ∈ D.support (B 1))
      (hx2 : x ∈ D.support (B 2)) :
      D.profile x = D.profile p₀ := by
    rw [hprofile₀]
    symm
    apply Finset.eq_of_subset_of_card_le
    · intro c hc
      simp only [Finset.mem_insert, Finset.mem_singleton] at hc
      rcases hc with rfl | rfl | rfl
      · exact (D.mem_profile x (B 0)).mpr hx0
      · exact (D.mem_profile x (B 1)).mpr hx1
      · exact (D.mem_profile x (B 2)).mpr hx2
    · rw [D.card_profile]
      simp [B.injective.ne]
  have hp₀₁_ne_p₀₂ : p₀₁ ≠ p₀₂ := by
    intro h
    apply hp₀₁ne
    apply D.profile_injective
    apply profile_eq_profile₀ p₀₁ hp₀₁0 hp₀₁1
    rw [h]
    exact hp₀₂2
  have hp₀₁_ne_p₁₂ : p₀₁ ≠ p₁₂ := by
    intro h
    apply hp₀₁ne
    apply D.profile_injective
    apply profile_eq_profile₀ p₀₁ hp₀₁0 hp₀₁1
    rw [h]
    exact hp₁₂2
  have hp₀₂_ne_p₁₂ : p₀₂ ≠ p₁₂ := by
    intro h
    apply hp₀₂ne
    apply D.profile_injective
    apply profile_eq_profile₀ p₀₂ hp₀₂0
    · rw [h]
      exact hp₁₂1
    · exact hp₀₂2

  let p : Fin 4 → Point := ![p₀, p₀₁, p₀₂, p₁₂]
  have hpinj : Function.Injective p := by
    intro i k hik
    fin_cases i <;> fin_cases k <;>
      simp_all [p]
  obtain ⟨σP, hσP⟩ := Equiv.Perm.exists_extending_pair
    (fun i : Fin 4 => Pbase (finFourEmbeddingTen i)) p
    (Pbase.injective.comp finFourEmbeddingTen.injective) hpinj
  let P : Fin 10 ≃ Point := Pbase.trans σP
  have hPfirst (i : Fin 4) : P (finFourEmbeddingTen i) = p i := hσP i
  have hP0 : P 0 = p₀ := by simpa [finFourEmbeddingTen, p] using hPfirst 0
  have hP1 : P 1 = p₀₁ := by simpa [finFourEmbeddingTen, p] using hPfirst 1
  have hP2 : P 2 = p₀₂ := by simpa [finFourEmbeddingTen, p] using hPfirst 2
  have hP3 : P 3 = p₁₂ := by simpa [finFourEmbeddingTen, p] using hPfirst 3
  refine ⟨P, B, ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · ext j
    simp [SixFiveDesign.relabeledProfiles, hP0, hprofile₀,
      B.injective.eq_iff]
  · exact D.mem_relabeledProfiles P B 1 0 |>.2 (hP1 ▸ hp₀₁0)
  · exact D.mem_relabeledProfiles P B 1 1 |>.2 (hP1 ▸ hp₀₁1)
  · exact D.mem_relabeledProfiles P B 2 0 |>.2 (hP2 ▸ hp₀₂0)
  · exact D.mem_relabeledProfiles P B 2 2 |>.2 (hP2 ▸ hp₀₂2)
  · exact D.mem_relabeledProfiles P B 3 1 |>.2 (hP3 ▸ hp₁₂1)
  · exact D.mem_relabeledProfiles P B 3 2 |>.2 (hP3 ▸ hp₁₂2)

theorem SixFiveDesign.exists_classified_labeling
    {Point Block : Type*} [Fintype Point] [DecidableEq Point]
    [Fintype Block] [DecidableEq Block]
    (D : SixFiveDesign Point Block) :
    ∃ (P : Fin 10 ≃ Point) (B : Fin 6 ≃ Block),
      SixFiveProfilesClassified (D.relabeledProfiles P B) := by
  obtain ⟨P, B, hnorm⟩ := D.exists_normalized_labeling
  exact ⟨P, B, sixFiveProfiles_classification _
    (D.relabeledProfiles_valid P B) hnorm⟩

end Erdos506.Finite
