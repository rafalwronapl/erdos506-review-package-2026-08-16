import Erdos506.Finite.IncidenceMoments

/-!
# The finite six-by-five incidence design

This file isolates the geometry-free design forced by equality in the
ten-point five-block packing bound.  In particular, it proves structurally
that two points cannot have the same three incident blocks; no search is used
for that step.
-/

namespace Erdos506.Finite

structure SixFiveDesign (Point Block : Type*)
    [Fintype Point] [DecidableEq Point]
    [Fintype Block] [DecidableEq Block] where
  support : Block → Finset Point
  point_card : Fintype.card Point = 10
  block_card : Fintype.card Block = 6
  support_card : ∀ b, (support b).card = 5
  profile_card : ∀ x,
    ((Finset.univ : Finset Block).filter fun b => x ∈ support b).card = 3
  pair_inter_card : ∀ b c, b ≠ c →
    (support b ∩ support c).card = 2

def SixFiveDesign.profile
    {Point Block : Type*} [Fintype Point] [DecidableEq Point]
    [Fintype Block] [DecidableEq Block]
    (D : SixFiveDesign Point Block) (x : Point) : Finset Block :=
  Finset.univ.filter fun b => x ∈ D.support b

@[simp] theorem SixFiveDesign.mem_profile
    {Point Block : Type*} [Fintype Point] [DecidableEq Point]
    [Fintype Block] [DecidableEq Block]
    (D : SixFiveDesign Point Block) (x : Point) (b : Block) :
    b ∈ D.profile x ↔ x ∈ D.support b := by
  simp [SixFiveDesign.profile]

theorem SixFiveDesign.card_profile
    {Point Block : Type*} [Fintype Point] [DecidableEq Point]
    [Fintype Block] [DecidableEq Block]
    (D : SixFiveDesign Point Block) (x : Point) :
    (D.profile x).card = 3 :=
  D.profile_card x

theorem card_union_three_eq_eleven_of_common_pair
    {α : Type*} [DecidableEq α]
    (A B C : Finset α) (p q : α) (hpq : p ≠ q)
    (hA : A.card = 5) (hB : B.card = 5) (hC : C.card = 5)
    (hpA : p ∈ A) (hqA : q ∈ A)
    (hpB : p ∈ B) (hqB : q ∈ B)
    (hpC : p ∈ C) (hqC : q ∈ C)
    (hAB : (A ∩ B).card = 2) (hAC : (A ∩ C).card = 2)
    (hBC : (B ∩ C).card = 2) :
    ((A ∪ B) ∪ C).card = 11 := by
  have hpqCard : ({p, q} : Finset α).card = 2 := by simp [hpq]
  have hpair (S T : Finset α) (hpS : p ∈ S) (hqS : q ∈ S)
      (hpT : p ∈ T) (hqT : q ∈ T) (hcard : (S ∩ T).card = 2) :
      S ∩ T = {p, q} := by
    symm
    apply Finset.eq_of_subset_of_card_le
    · intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact Finset.mem_inter.mpr ⟨hpS, hpT⟩
      · exact Finset.mem_inter.mpr ⟨hqS, hqT⟩
    · rw [hcard, hpqCard]
  have hABeq := hpair A B hpA hqA hpB hqB hAB
  have hACeq := hpair A C hpA hqA hpC hqC hAC
  have hBCeq := hpair B C hpB hqB hpC hqC hBC
  have hABunion : (A ∪ B).card = 8 := by
    have h := Finset.card_union_add_card_inter A B
    rw [hA, hB, hAB] at h
    omega
  have hinter : ((A ∪ B) ∩ C).card = 2 := by
    have heq : (A ∪ B) ∩ C = (A ∩ C) ∪ (B ∩ C) := by
      ext x
      simp only [Finset.mem_inter, Finset.mem_union]
      tauto
    rw [heq, hACeq, hBCeq, Finset.union_self, hpqCard]
  have h := Finset.card_union_add_card_inter (A ∪ B) C
  rw [hABunion, hC, hinter] at h
  omega

theorem SixFiveDesign.profile_injective
    {Point Block : Type*} [Fintype Point] [DecidableEq Point]
    [Fintype Block] [DecidableEq Block]
    (D : SixFiveDesign Point Block) : Function.Injective D.profile := by
  intro p q hpqProfile
  by_contra hpq
  obtain ⟨b₀, b₁, b₂, hb01, hb02, hb12, hprof⟩ :=
    Finset.card_eq_three.mp (D.card_profile p)
  have hp (i : Block) (hi : i ∈ ({b₀, b₁, b₂} : Finset Block)) :
      p ∈ D.support i := by
    apply (D.mem_profile p i).mp
    rw [hprof]
    exact hi
  have hq (i : Block) (hi : i ∈ ({b₀, b₁, b₂} : Finset Block)) :
      q ∈ D.support i := by
    apply (D.mem_profile q i).mp
    rw [← hpqProfile, hprof]
    exact hi
  have hunion := card_union_three_eq_eleven_of_common_pair
    (D.support b₀) (D.support b₁) (D.support b₂) p q hpq
    (D.support_card b₀) (D.support_card b₁) (D.support_card b₂)
    (hp b₀ (by simp)) (hq b₀ (by simp))
    (hp b₁ (by simp)) (hq b₁ (by simp))
    (hp b₂ (by simp)) (hq b₂ (by simp))
    (D.pair_inter_card b₀ b₁ hb01)
    (D.pair_inter_card b₀ b₂ hb02)
    (D.pair_inter_card b₁ b₂ hb12)
  have hsub : (D.support b₀ ∪ D.support b₁) ∪ D.support b₂ ⊆
      (Finset.univ : Finset Point) := Finset.subset_univ _
  have hle := Finset.card_le_card hsub
  rw [hunion, Finset.card_univ, D.point_card] at hle
  omega

end Erdos506.Finite
