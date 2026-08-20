import Erdos506.Finite.FourPentagonProfile
import Erdos506.Finite.FourPentagonLedgerCore
import Erdos506.Finite.FourPentagonFinFourPairLedger

/-!
# Core data for the five-block profile normalizer

This predecessor module contains the small generic filter lemmas, canonical
profile fibres, and the opaque labeling stage used in the second-moment
twelve row.  It deliberately contains no four-block relabeling.
-/

namespace Erdos506.Finite

open Erdos506.Block
open Erdos506.Block.BlockSystem
open scoped BigOperators
open FourPentagonProfile

universe u v

namespace FourPentagonFiveProfile

theorem card_filter_pair_of_mem_mem
    {α : Type*} [DecidableEq α] {a b : α} (hab : a ≠ b)
    (U : Finset α) (ha : a ∈ U) (hb : b ∈ U) :
    (({a, b} : Finset α).filter fun x => x ∈ U).card = 2 := by
  have hfilter : ({a, b} : Finset α).filter (fun x => x ∈ U) =
      {a, b} := by
    apply Finset.filter_eq_self.2
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact ha
    · exact hb
  rw [hfilter]
  exact Finset.card_pair hab

theorem card_filter_pair_of_mem_not_mem
    {α : Type*} [DecidableEq α] {a b : α}
    (U : Finset α) (ha : a ∈ U) (hb : b ∉ U) :
    (({a, b} : Finset α).filter fun x => x ∈ U).card = 1 := by
  have hfilter : ({a, b} : Finset α).filter (fun x => x ∈ U) =
      {a} := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_insert,
      Finset.mem_singleton]
    constructor
    · rintro ⟨hpair, hxU⟩
      rcases hpair with hxa | hxb
      · exact hxa
      · rw [hxb] at hxU
        exact (hb hxU).elim
    · intro hxa
      rw [hxa]
      exact ⟨Or.inl rfl, ha⟩
  rw [hfilter]
  exact Finset.card_singleton a

theorem card_filter_pair_of_not_mem_mem
    {α : Type*} [DecidableEq α] {a b : α}
    (U : Finset α) (ha : a ∉ U) (hb : b ∈ U) :
    (({a, b} : Finset α).filter fun x => x ∈ U).card = 1 := by
  have hfilter : ({a, b} : Finset α).filter (fun x => x ∈ U) =
      {b} := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_insert,
      Finset.mem_singleton]
    constructor
    · rintro ⟨hpair, hxU⟩
      rcases hpair with hxa | hxb
      · rw [hxa] at hxU
        exact (ha hxU).elim
      · exact hxb
    · intro hxb
      rw [hxb]
      exact ⟨Or.inr rfl, hb⟩
  rw [hfilter]
  exact Finset.card_singleton b

theorem card_filter_pair_of_not_mem_not_mem
    {α : Type*} [DecidableEq α] {a b : α}
    (U : Finset α) (ha : a ∉ U) (hb : b ∉ U) :
    (({a, b} : Finset α).filter fun x => x ∈ U).card = 0 := by
  have hfilter : ({a, b} : Finset α).filter (fun x => x ∈ U) = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro x hx
    have hx' := Finset.mem_filter.mp hx
    have hpair := hx'.1
    have hxU := hx'.2
    simp only [Finset.mem_insert, Finset.mem_singleton] at hpair
    rcases hpair with hxa | hxb
    · rw [hxa] at hxU
      exact ha hxU
    · rw [hxb] at hxU
      exact hb hxU
  rw [hfilter]
  exact Finset.card_empty

def fourPentagonProfile (i : Fin 10) : Finset (Fin 4) :=
  Finset.univ.filter fun j => i ∈ fourPentagonFiveSupport j

def fourPentagonProfileMultiplicity (Q : Finset (Fin 4)) : Nat :=
  if Q = {2, 3} then 2 else if Q ∈ ({
      {0}, {1}, {0, 1, 2}, {0, 1, 3},
      {0, 2}, {0, 3}, {1, 2}, {1, 3}
    } : Finset (Finset (Fin 4))) then 1 else 0

theorem canonicalProfile_fiber_card (Q : Finset (Fin 4)) :
    Fintype.card {i : Fin 10 // fourPentagonProfile i = Q} =
      fourPentagonProfileMultiplicity Q := by
  revert Q
  decide +kernel

noncomputable def equivOfFiberCardEq
    {α β γ : Type*} [Fintype α] [Fintype β] [DecidableEq γ]
    (f : α → γ) (g : β → γ)
    (h : ∀ c, Fintype.card {a : α // f a = c} =
      Fintype.card {b : β // g b = c}) : α ≃ β :=
  Equiv.ofFiberEquiv fun c => Fintype.equivOfCardEq (h c)

@[simp] theorem equivOfFiberCardEq_map
    {α β γ : Type*} [Fintype α] [Fintype β] [DecidableEq γ]
    (f : α → γ) (g : β → γ)
    (h : ∀ c, Fintype.card {a : α // f a = c} =
      Fintype.card {b : β // g b = c}) (a : α) :
    g (equivOfFiberCardEq f g h a) = f a := by
  exact Equiv.ofFiberEquiv_map
    (fun c => Fintype.equivOfCardEq (h c)) a

structure FourPentagonFiveNormalForm
    {Point Block : Type*} [Fintype Point] [Fintype Block]
    [DecidableEq Point] (S : BlockSystem Point Block) where
  point : Fin 10 ≃ Point
  five : Fin 4 → Block
  five_mem : ∀ j, five j ∈ S.blocksOfSize 5
  mem_five : ∀ i j,
    point i ∈ S.support (five j) ↔ i ∈ fourPentagonFiveSupport j

theorem fiveBlock_support_degree_sum_eq_eleven
    {Point Block : Type*} [Fintype Point] [Fintype Block]
    [DecidableEq Point]
    (S : BlockSystem Point Block)
    (hfive : S.blockCount 5 = 4)
    (hinterFive : ∀ b ∈ S.blocksOfSize 5,
      ∀ c ∈ S.blocksOfSize 5, b ≠ c →
        (S.support b ∩ S.support c).card = 2)
    (b : Block) (hb : b ∈ S.blocksOfSize 5) :
    (∑ p ∈ S.support b, S.blockDegree 5 p) = 11 := by
  classical
  change (∑ p ∈ S.support b,
    S.degreeIn (S.blocksOfSize 5) p) = 11
  rw [sum_degreeIn_over_support S (S.blocksOfSize 5) b]
  have hsplit := Finset.sum_erase_add (S.blocksOfSize 5)
    (fun c => (S.support b ∩ S.support c).card) hb
  have hFcard : (S.blocksOfSize 5).card = 4 := by
    change (S.blocksOfSize 5).card = 4 at hfive
    exact hfive
  have hother :
      (∑ c ∈ (S.blocksOfSize 5).erase b,
        (S.support b ∩ S.support c).card) = 6 := by
    calc
      _ = ∑ _c ∈ (S.blocksOfSize 5).erase b, 2 := by
        apply Finset.sum_congr rfl
        intro c hc
        exact hinterFive b hb c (Finset.mem_of_mem_erase hc)
          (Finset.mem_erase.mp hc).1.symm
      _ = 6 := by
        rw [Finset.sum_const, nsmul_eq_mul,
          Finset.card_erase_of_mem hb, hFcard]
        norm_num
  have hself : (S.support b ∩ S.support b).card = 5 := by
    simp [S.mem_blocksOfSize.mp hb]
  calc
    (∑ c ∈ S.blocksOfSize 5,
        (S.support b ∩ S.support c).card) =
        (∑ c ∈ (S.blocksOfSize 5).erase b,
          (S.support b ∩ S.support c).card) +
          (S.support b ∩ S.support b).card := hsplit.symm
    _ = 6 + 5 := by rw [hother, hself]
    _ = 11 := by norm_num

theorem fiveBlock_covered_by_high_pair
    {Point Block : Type*} [Fintype Point] [Fintype Block]
    [DecidableEq Point]
    (S : BlockSystem Point Block)
    (T T' : Point)
    (hprofile : ∀ p : Point, S.blockDegree 5 p = 1 ∨
      S.blockDegree 5 p = 2 ∨ S.blockDegree 5 p = 3)
    (hhighCases : ∀ {p : Point}, S.blockDegree 5 p = 3 →
      p = T ∨ p = T')
    (b : Block) (hb : b ∈ S.blocksOfSize 5)
    (hsum : (∑ p ∈ S.support b, S.blockDegree 5 p) = 11) :
    T ∈ S.support b ∨ T' ∈ S.support b := by
  by_contra hnot
  have hTnot : T ∉ S.support b := fun h => hnot (Or.inl h)
  have hT'not : T' ∉ S.support b := fun h => hnot (Or.inr h)
  have hterm (p : Point) (hp : p ∈ S.support b) :
      S.blockDegree 5 p ≤ 2 := by
    rcases hprofile p with h1 | h2 | h3
    · omega
    · omega
    · rcases hhighCases h3 with rfl | rfl
      · exact (hTnot hp).elim
      · exact (hT'not hp).elim
  have hle : (∑ p ∈ S.support b, S.blockDegree 5 p) ≤ 10 := by
    calc
      _ ≤ ∑ _p ∈ S.support b, 2 := by
        apply Finset.sum_le_sum
        intro p hp
        exact hterm p hp
      _ = 10 := by simp [S.mem_blocksOfSize.mp hb]
  omega

theorem card_inter_eq_two_of_three_subsets_of_four
    {α : Type*} [DecidableEq α]
    (F A B : Finset α)
    (hFcard : F.card = 4) (hAcard : A.card = 3)
    (hBcard : B.card = 3)
    (hAsub : A ⊆ F) (hBsub : B ⊆ F) (hne : A ≠ B) :
    (A ∩ B).card = 2 := by
  have hunionSub : A ∪ B ⊆ F := Finset.union_subset hAsub hBsub
  have hunionLe := Finset.card_le_card hunionSub
  have hformula := Finset.card_union_add_card_inter A B
  have hinterLe : (A ∩ B).card ≤ 3 := by
    calc
      (A ∩ B).card ≤ A.card :=
        Finset.card_le_card Finset.inter_subset_left
      _ = 3 := hAcard
  have hinterGe : 2 ≤ (A ∩ B).card := by omega
  by_contra hnotTwo
  have hinterThree : (A ∩ B).card = 3 := by omega
  have hinterEqA : A ∩ B = A := by
    apply Finset.eq_of_subset_of_card_le Finset.inter_subset_left
    rw [hinterThree, hAcard]
  have hinterEqB : A ∩ B = B := by
    apply Finset.eq_of_subset_of_card_le Finset.inter_subset_right
    rw [hinterThree, hBcard]
  exact hne (hinterEqA.symm.trans hinterEqB)

theorem card_filter_subtype_eq_card_filter
    {α : Type*} [DecidableEq α]
    (F : Finset α) (p : α → Prop) [DecidablePred p] :
    ((Finset.univ : Finset {x : α // x ∈ F}).filter
      fun x => p x.1).card = (F.filter p).card := by
  rw [Finset.univ_eq_attach, Finset.filter_attach]
  simp only [Finset.card_map, Finset.card_attach]

theorem card_profile_eq_card_filter
    {ι α : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq α]
    (F : Finset α) (B : ι ≃ {x : α // x ∈ F})
    (p : α → Prop) [DecidablePred p] :
    ((Finset.univ : Finset ι).filter fun i => p (B i).1).card =
      (F.filter p).card := by
  let A := ((Finset.univ : Finset {x : α // x ∈ F}).filter
    fun x => p x.1)
  have heq : ((Finset.univ : Finset ι).filter fun i => p (B i).1) =
      A.preimage B B.injective.injOn := by
    ext i
    simp [A]
  rw [heq, card_preimage_equiv]
  exact card_filter_subtype_eq_card_filter F p

/-- The opaque combinatorial labeling stage: it chooses the two degree-three
points and orders the four five-blocks by their incidences with that pair. -/
structure FourPentagonFiveBlockLabeling
    {Point Block : Type*} [Fintype Point] [Fintype Block]
    [DecidableEq Point] (S : BlockSystem Point Block) where
  high₀ : Point
  high₁ : Point
  high_ne : high₀ ≠ high₁
  high₀_degree : S.blockDegree 5 high₀ = 3
  high₁_degree : S.blockDegree 5 high₁ = 3
  high_cases : ∀ {p : Point}, S.blockDegree 5 p = 3 →
    p = high₀ ∨ p = high₁
  high_set : ((Finset.univ : Finset Point).filter
    fun p => S.blockDegree 5 p = 3) = {high₀, high₁}
  five : Fin 4 ≃ {b : Block // b ∈ S.blocksOfSize 5}
  high₀_mem : ∀ j : Fin 4,
    high₀ ∈ S.support (five j).1 ↔ j ∈ ({0, 1, 2} : Finset (Fin 4))
  high₁_mem : ∀ j : Fin 4,
    high₁ ∈ S.support (five j).1 ↔ j ∈ ({0, 1, 3} : Finset (Fin 4))

noncomputable def fiveBlockLabeling_of_secondMoment_twelve
    {Point Block : Type*} [Fintype Point] [Fintype Block]
    [DecidableEq Point]
    (S : BlockSystem Point Block)
    (hfive : S.blockCount 5 = 4)
    (hhigh : ((Finset.univ : Finset Point).filter
      fun p => S.blockDegree 5 p = 3).card = 2)
    (hprofile : ∀ p : Point, S.blockDegree 5 p = 1 ∨
      S.blockDegree 5 p = 2 ∨ S.blockDegree 5 p = 3)
    (hmoment : (∑ p : Point,
      Nat.choose (S.blockDegree 5 p) 2) = 12) :
    FourPentagonFiveBlockLabeling S := by
  classical
  let F := S.blocksOfSize 5
  have hFcard : F.card = 4 := hfive
  have hinterFive := fiveBlock_pair_inter_eq_two_of_secondMoment_twelve
    S hfive hmoment
  let High := (Finset.univ : Finset Point).filter
    fun p => S.blockDegree 5 p = 3
  let highPair : ∃ x y : Point, x ≠ y ∧ High = {x, y} :=
    Finset.card_eq_two.mp hhigh
  let T : Point := Classical.choose highPair
  have highPairAtT : ∃ y : Point, T ≠ y ∧ High = {T, y} := by
    simpa [T] using Classical.choose_spec highPair
  let T' : Point := Classical.choose highPairAtT
  have highPairSpec : T ≠ T' ∧ High = {T, T'} := by
    simpa [T'] using Classical.choose_spec highPairAtT
  have hTT' : T ≠ T' := highPairSpec.1
  have hHighEq : High = {T, T'} := highPairSpec.2
  have hTdegree : S.blockDegree 5 T = 3 := by
    have hmem : T ∈ High := by rw [hHighEq]; simp
    exact (Finset.mem_filter.mp hmem).2
  have hT'degree : S.blockDegree 5 T' = 3 := by
    have hmem : T' ∈ High := by rw [hHighEq]; simp
    exact (Finset.mem_filter.mp hmem).2
  have hhighCases {p : Point} (hp : S.blockDegree 5 p = 3) :
      p = T ∨ p = T' := by
    have hpHigh : p ∈ High :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ p, hp⟩
    rw [hHighEq] at hpHigh
    simpa using hpHigh
  have hsumSupport (b : Block) (hb : b ∈ F) :
      (∑ p ∈ S.support b, S.blockDegree 5 p) = 11 :=
    fiveBlock_support_degree_sum_eq_eleven S hfive hinterFive b hb
  have hcovered (b : Block) (hb : b ∈ F) :
      T ∈ S.support b ∨ T' ∈ S.support b :=
    fiveBlock_covered_by_high_pair S T T' hprofile hhighCases
      b hb (hsumSupport b hb)
  let FT := F.filter fun b => T ∈ S.support b
  let FT' := F.filter fun b => T' ∈ S.support b
  have hFTcard : FT.card = 3 := hTdegree
  have hFT'card : FT'.card = 3 := hT'degree
  have hFTne : FT ≠ FT' := by
    intro heq
    have hFsub : F ⊆ FT := by
      intro b hbF
      rcases hcovered b hbF with hT | hT'
      · exact Finset.mem_filter.mpr ⟨hbF, hT⟩
      · have hbFT' : b ∈ FT' := Finset.mem_filter.mpr ⟨hbF, hT'⟩
        rwa [← heq] at hbFT'
    have hcard := Finset.card_le_card hFsub
    rw [hFcard, hFTcard] at hcard
    omega
  let C := FT ∩ FT'
  have hCcard : C.card = 2 := by
    apply card_inter_eq_two_of_three_subsets_of_four F FT FT'
      hFcard hFTcard hFT'card
    · exact Finset.filter_subset _ _
    · exact Finset.filter_subset _ _
    · exact hFTne
  let commonPair : ∃ x y : Block, x ≠ y ∧ C = {x, y} :=
    Finset.card_eq_two.mp hCcard
  let b₀ : Block := Classical.choose commonPair
  have commonPairAtB₀ : ∃ y : Block, b₀ ≠ y ∧ C = {b₀, y} := by
    simpa [b₀] using Classical.choose_spec commonPair
  let b₁ : Block := Classical.choose commonPairAtB₀
  have commonPairSpec : b₀ ≠ b₁ ∧ C = {b₀, b₁} := by
    simpa [b₁] using Classical.choose_spec commonPairAtB₀
  have hb₀ne₁ : b₀ ≠ b₁ := commonPairSpec.1
  have hCeq : C = {b₀, b₁} := commonPairSpec.2
  let E := FT \ FT'
  let E' := FT' \ FT
  have hEcard : E.card = 1 := by
    have hsplit := Finset.card_sdiff_add_card_inter FT FT'
    change E.card + C.card = FT.card at hsplit
    omega
  have hE'card : E'.card = 1 := by
    have hsplit := Finset.card_sdiff_add_card_inter FT' FT
    rw [Finset.inter_comm FT' FT] at hsplit
    change E'.card + C.card = FT'.card at hsplit
    omega
  let eWitness : ∃ b : Block, E = {b} := Finset.card_eq_one.mp hEcard
  let b₂ : Block := Classical.choose eWitness
  have hEeq : E = {b₂} := by
    simpa [b₂] using Classical.choose_spec eWitness
  let e'Witness : ∃ b : Block, E' = {b} := Finset.card_eq_one.mp hE'card
  let b₃ : Block := Classical.choose e'Witness
  have hE'eq : E' = {b₃} := by
    simpa [b₃] using Classical.choose_spec e'Witness
  have hb₀C : b₀ ∈ C := by rw [hCeq]; simp
  have hb₁C : b₁ ∈ C := by rw [hCeq]; simp
  have hb₂E : b₂ ∈ E := by rw [hEeq]; simp
  have hb₃E : b₃ ∈ E' := by rw [hE'eq]; simp
  have hb₀F : b₀ ∈ F := (Finset.mem_filter.mp
    (Finset.mem_inter.mp hb₀C).1).1
  have hb₁F : b₁ ∈ F := (Finset.mem_filter.mp
    (Finset.mem_inter.mp hb₁C).1).1
  have hb₂F : b₂ ∈ F := (Finset.mem_filter.mp
    (Finset.mem_sdiff.mp hb₂E).1).1
  have hb₃F : b₃ ∈ F := (Finset.mem_filter.mp
    (Finset.mem_sdiff.mp hb₃E).1).1
  have hTb₀ : T ∈ S.support b₀ := (Finset.mem_filter.mp
    (Finset.mem_inter.mp hb₀C).1).2
  have hT'b₀ : T' ∈ S.support b₀ := (Finset.mem_filter.mp
    (Finset.mem_inter.mp hb₀C).2).2
  have hTb₁ : T ∈ S.support b₁ := (Finset.mem_filter.mp
    (Finset.mem_inter.mp hb₁C).1).2
  have hT'b₁ : T' ∈ S.support b₁ := (Finset.mem_filter.mp
    (Finset.mem_inter.mp hb₁C).2).2
  have hTb₂ : T ∈ S.support b₂ := (Finset.mem_filter.mp
    (Finset.mem_sdiff.mp hb₂E).1).2
  have hT'notb₂ : T' ∉ S.support b₂ := by
    exact fun h => (Finset.mem_sdiff.mp hb₂E).2
      (Finset.mem_filter.mpr ⟨hb₂F, h⟩)
  have hT'b₃ : T' ∈ S.support b₃ := (Finset.mem_filter.mp
    (Finset.mem_sdiff.mp hb₃E).1).2
  have hTnotb₃ : T ∉ S.support b₃ := by
    exact fun h => (Finset.mem_sdiff.mp hb₃E).2
      (Finset.mem_filter.mpr ⟨hb₃F, h⟩)
  have hb₂ne₃ : b₂ ≠ b₃ := by
    intro h
    apply hTnotb₃
    simpa only [← h] using hTb₂
  have hb₀ne₂ : b₀ ≠ b₂ := by
    intro h
    apply hT'notb₂
    simpa only [← h] using hT'b₀
  have hb₁ne₂ : b₁ ≠ b₂ := by
    intro h
    apply hT'notb₂
    simpa only [← h] using hT'b₁
  have hb₀ne₃ : b₀ ≠ b₃ := by
    intro h
    apply hTnotb₃
    simpa only [← h] using hTb₀
  have hb₁ne₃ : b₁ ≠ b₃ := by
    intro h
    apply hTnotb₃
    simpa only [← h] using hTb₁
  let b : Fin 4 → Block := ![b₀, b₁, b₂, b₃]
  have hbinj : Function.Injective b := by
    dsimp [b]
    exact FourPentagonFinFourPairLedger.vector_injective
      hb₀ne₁ hb₀ne₂ hb₀ne₃ hb₁ne₂ hb₁ne₃ hb₂ne₃
  let bsub : Fin 4 → {c : Block // c ∈ F} := fun j =>
    ⟨b j, by fin_cases j <;> simp [b, hb₀F, hb₁F, hb₂F, hb₃F]⟩
  have hbsubInj : Function.Injective bsub := by
    intro i j h
    apply hbinj
    exact congrArg Subtype.val h
  have hbsubBij : Function.Bijective bsub := by
    apply (Fintype.bijective_iff_injective_and_card bsub).mpr
    constructor
    · exact hbsubInj
    · simp [hFcard]
  let B : Fin 4 ≃ {c : Block // c ∈ F} := Equiv.ofBijective bsub hbsubBij
  have hBval (j : Fin 4) : (B j).1 = b j := rfl
  refine {
    high₀ := T
    high₁ := T'
    high_ne := hTT'
    high₀_degree := hTdegree
    high₁_degree := hT'degree
    high_cases := hhighCases
    high_set := hHighEq
    five := B
    high₀_mem := ?_
    high₁_mem := ?_ }
  · intro j
    fin_cases j <;>
      simp [hBval, b, hTb₀, hTb₁, hTb₂, hTnotb₃]
  · intro j
    fin_cases j <;>
      simp [hBval, b, hT'b₀, hT'b₁, hT'notb₂, hT'b₃]

end FourPentagonFiveProfile

end Erdos506.Finite
