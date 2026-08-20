import Erdos506.Finite.FourPentagonFiveProfile
import Erdos506.Finite.FourPentagonRowTen
import Erdos506.Finite.FourPentagonRowEleven
import Erdos506.Finite.FourPentagonLedger

/-!
# The finite four-pentagon normalizer

This thin module combines the verified row eliminations, five-block profile,
and four-block ledgers.  The expensive finite classifications are compiled in
predecessor modules; this file only performs relabeling and the final assembly.
-/

namespace Erdos506.Finite

open Erdos506.Block
open Erdos506.Block.BlockSystem
open scoped BigOperators
open FourPentagonProfile
open FourPentagonRowTen
open FourPentagonRowEleven
open FourPentagonFiveProfile

universe u v

def fourPentagonRequiredFourSupport : Fin 7 → Finset (Fin 10) := ![
  {0, 2, 3, 8},
  {0, 2, 7, 9},
  {0, 3, 5, 9},
  {1, 2, 3, 9},
  {1, 2, 6, 8},
  {1, 3, 4, 8},
  {4, 5, 6, 7}
]

/-- Positive output of the finite four-pentagon normalizer. -/
structure FourPentagonFiniteNormalForm
    {Point Block : Type*} [Fintype Point] [Fintype Block]
    [DecidableEq Point] (S : BlockSystem Point Block) where
  point : Fin 10 ≃ Point
  five : Fin 4 → Block
  four : Fin 7 → Block
  five_size : ∀ j, (S.support (five j)).card = 5
  four_size : ∀ j, (S.support (four j)).card = 4
  mem_five : ∀ i j,
    point i ∈ S.support (five j) ↔ i ∈ fourPentagonFiveSupport j
  mem_four : ∀ i j,
    point i ∈ S.support (four j) ↔ i ∈ fourPentagonRequiredFourSupport j

private theorem finTwo_ne_orientations {a b : Fin 2} (hab : a ≠ b) :
    (a = 0 ∧ b = 1) ∨ (a = 1 ∧ b = 0) := by
  fin_cases a <;> fin_cases b
  · exact (hab rfl).elim
  · exact Or.inl ⟨rfl, rfl⟩
  · exact Or.inr ⟨rfl, rfl⟩
  · exact (hab rfl).elim

/-! ## The surviving second-moment twelve row -/

private noncomputable def relabeledSupport
    {Point : Type*} [Fintype Point] [DecidableEq Point]
    (P : Fin 10 ≃ Point) (A : Finset Point) : Finset (Fin 10) :=
  A.preimage P P.injective.injOn

@[simp] private theorem mem_relabeledSupport
    {Point : Type*} [Fintype Point] [DecidableEq Point]
    (P : Fin 10 ≃ Point) (A : Finset Point) (i : Fin 10) :
    i ∈ relabeledSupport P A ↔ P i ∈ A := by
  simp [relabeledSupport]

private theorem relabeledSupport_card
    {Point : Type*} [Fintype Point] [DecidableEq Point]
    (P : Fin 10 ≃ Point) (A : Finset Point) :
    (relabeledSupport P A).card = A.card :=
  card_preimage_equiv P A

private theorem relabeledSupport_inter_card
    {Point : Type*} [Fintype Point] [DecidableEq Point]
    (P : Fin 10 ≃ Point) (A B : Finset Point) :
    (relabeledSupport P A ∩ relabeledSupport P B).card =
      (A ∩ B).card := by
  rw [← relabeledSupport_card P (A ∩ B)]
  congr 1
  ext i
  simp [relabeledSupport]

private noncomputable def pulledFourFamily
    {Point Block : Type*} [Fintype Point] [Fintype Block]
    [DecidableEq Point]
    (S : BlockSystem Point Block) (P : Fin 10 ≃ Point) :
    Finset (Finset (Fin 10)) :=
  (S.blocksOfSize 4).image fun b => relabeledSupport P (S.support b)

private theorem pullSupport_injOn_four
    {Point Block : Type*} [Fintype Point] [Fintype Block]
    [DecidableEq Point]
    (S : BlockSystem Point Block) (P : Fin 10 ≃ Point) :
    Set.InjOn (fun b => relabeledSupport P (S.support b))
      (S.blocksOfSize 4 : Set Block) := by
  intro b hb c hc heq
  apply support_injOn_blocksOfSize S 4 (by omega) hb hc
  ext p
  obtain ⟨i, rfl⟩ := P.surjective p
  have hi := Finset.ext_iff.mp heq i
  simpa using hi

private theorem pulledFourFamily_card
    {Point Block : Type*} [Fintype Point] [Fintype Block]
    [DecidableEq Point]
    (S : BlockSystem Point Block) (P : Fin 10 ≃ Point) :
    (pulledFourFamily S P).card = S.blockCount 4 := by
  rw [pulledFourFamily, Finset.card_image_iff.mpr
    (pullSupport_injOn_four S P)]
  rfl

private theorem pulledFourFamily_compatible
    {Point Block : Type*} [Fintype Point] [Fintype Block]
    [DecidableEq Point]
    (S : BlockSystem Point Block) (P : Fin 10 ≃ Point) :
    fourPentagonCompatible (pulledFourFamily S P) := by
  intro Q hQ R hR hQR
  obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hQ
  obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hR
  have hbc : b ≠ c := by
    intro h
    apply hQR
    simp [h]
  rw [relabeledSupport_inter_card]
  have := S.distinct_block_inter_card_lt_three hbc
  omega

private theorem pulledFourFamily_subset_candidates
    {Point Block : Type*} [Fintype Point] [Fintype Block]
    [DecidableEq Point]
    (S : BlockSystem Point Block) (P : Fin 10 ≃ Point)
    (five : Fin 4 → Block)
    (hfiveMem : ∀ j, five j ∈ S.blocksOfSize 5)
    (hfive : ∀ i j, P i ∈ S.support (five j) ↔
      i ∈ fourPentagonFiveSupport j) :
    pulledFourFamily S P ⊆ fourPentagonCandidates := by
  intro Q hQ
  obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hQ
  apply Finset.mem_filter.mpr
  constructor
  · apply Finset.mem_powersetCard.mpr
    exact ⟨Finset.subset_univ _, by
      rw [relabeledSupport_card, S.mem_blocksOfSize.mp hb]⟩
  · intro j
    have hcolumn : relabeledSupport P (S.support (five j)) =
        fourPentagonFiveSupport j := by
      ext i
      simp [hfive i j]
    rw [← hcolumn, relabeledSupport_inter_card]
    have hbne : b ≠ five j := by
      intro h
      have hbsize := S.mem_blocksOfSize.mp hb
      have h5size := S.mem_blocksOfSize.mp (hfiveMem j)
      rw [h] at hbsize
      omega
    have := S.distinct_block_inter_card_lt_three hbne
    omega

private theorem pulledFourFamily_filter_card
    {Point Block : Type*} [Fintype Point] [Fintype Block]
    [DecidableEq Point]
    (S : BlockSystem Point Block) (P : Fin 10 ≃ Point) (i : Fin 10) :
    ((pulledFourFamily S P).filter fun Q => i ∈ Q).card =
      S.blockDegree 4 (P i) := by
  classical
  let H := (S.blocksOfSize 4).filter fun b => P i ∈ S.support b
  have heq : (pulledFourFamily S P).filter (fun Q => i ∈ Q) =
      H.image fun b => relabeledSupport P (S.support b) := by
    ext Q
    simp only [Finset.mem_filter, pulledFourFamily, Finset.mem_image]
    constructor
    · rintro ⟨⟨b, hb, rfl⟩, hi⟩
      exact ⟨b, Finset.mem_filter.mpr
        ⟨hb, (mem_relabeledSupport P (S.support b) i).mp hi⟩, rfl⟩
    · rintro ⟨b, hb, rfl⟩
      have hb' := Finset.mem_filter.mp hb
      exact ⟨⟨b, hb'.1, rfl⟩,
        (mem_relabeledSupport P (S.support b) i).mpr hb'.2⟩
  rw [heq, Finset.card_image_iff.mpr
    ((pullSupport_injOn_four S P).mono (Finset.filter_subset _ _))]
  rfl

private theorem relabeledSupport_swap
    {Point : Type*} [Fintype Point] [DecidableEq Point]
    (P : Fin 10 ≃ Point) (A : Finset Point) :
    relabeledSupport (fourPentagonSwapEightNine.trans P) A =
      fourPentagonSwapSupport (relabeledSupport P A) := by
  ext i
  rw [mem_relabeledSupport]
  change P (fourPentagonSwapEightNine i) ∈ A ↔
    i ∈ (relabeledSupport P A).image fourPentagonSwapEightNine
  simp only [Finset.mem_image]
  constructor
  · intro hi
    refine ⟨fourPentagonSwapEightNine i, ?_, ?_⟩
    · exact (mem_relabeledSupport P A _).mpr hi
    · simp [fourPentagonSwapEightNine]
  · rintro ⟨a, ha, rfl⟩
    simpa [fourPentagonSwapEightNine] using
      (mem_relabeledSupport P A a).mp ha

private theorem pulledFourFamily_swap
    {Point Block : Type*} [Fintype Point] [Fintype Block]
    [DecidableEq Point]
    (S : BlockSystem Point Block) (P : Fin 10 ≃ Point) :
    pulledFourFamily S (fourPentagonSwapEightNine.trans P) =
      (pulledFourFamily S P).image fourPentagonSwapSupport := by
  ext Q
  simp only [pulledFourFamily, Finset.mem_image]
  constructor
  · rintro ⟨b, hb, rfl⟩
    exact ⟨relabeledSupport P (S.support b),
      ⟨b, hb, rfl⟩, (relabeledSupport_swap P (S.support b)).symm⟩
  · rintro ⟨R, ⟨b, hb, rfl⟩, rfl⟩
    exact ⟨b, hb, relabeledSupport_swap P (S.support b)⟩

private theorem mem_fourPentagonFiveSupport_swap
    (i : Fin 10) (j : Fin 4) :
    fourPentagonSwapEightNine i ∈ fourPentagonFiveSupport j ↔
      i ∈ fourPentagonFiveSupport j := by
  constructor
  · intro hswap
    have hiImage : i ∈
        fourPentagonSwapSupport (fourPentagonFiveSupport j) := by
      change i ∈ (fourPentagonFiveSupport j).image
        fourPentagonSwapEightNine
      exact Finset.mem_image.mpr
        ⟨fourPentagonSwapEightNine i, hswap, by
          simp [fourPentagonSwapEightNine]⟩
    rw [swap_five_support] at hiImage
    exact hiImage
  · intro hi
    have hswapImage : fourPentagonSwapEightNine i ∈
        fourPentagonSwapSupport (fourPentagonFiveSupport j) := by
      change fourPentagonSwapEightNine i ∈
        (fourPentagonFiveSupport j).image fourPentagonSwapEightNine
      exact Finset.mem_image.mpr ⟨i, hi, rfl⟩
    rw [swap_five_support] at hswapImage
    exact hswapImage

private noncomputable def fullNormalForm_of_oriented_family
    {Point Block : Type*} [Fintype Point] [Fintype Block]
    [DecidableEq Point]
    (S : BlockSystem Point Block)
    (P : Fin 10 ≃ Point) (five : Fin 4 → Block)
    (hfiveMem : ∀ j, five j ∈ S.blocksOfSize 5)
    (hfive : ∀ i j, P i ∈ S.support (five j) ↔
      i ∈ fourPentagonFiveSupport j)
    (hB4 : S.blockCount 4 = 13)
    (hzero : (pulledFourFamily S P).filter (fun Q => 0 ∈ Q) =
      fourPentagonZeroOrientation 0)
    (hone : (pulledFourFamily S P).filter (fun Q => 1 ∈ Q) =
      fourPentagonOneOrientation 1) :
    FourPentagonFiniteNormalForm S := by
  classical
  let G := pulledFourFamily S P
  let H₀ := G.filter fun Q => 0 ∈ Q
  let H₁ := G.filter fun Q => 1 ∈ Q
  let G₀ := G.filter fun Q => 0 ∉ Q
  let R := G₀.filter fun Q => 1 ∉ Q
  have hGsub := pulledFourFamily_subset_candidates S P five hfiveMem hfive
  have hcompat := pulledFourFamily_compatible S P
  have hGcard : G.card = 13 := by rw [pulledFourFamily_card, hB4]
  have hH₀ : H₀ = fourPentagonZeroOrientation 0 := hzero
  have hH₁ : H₁ = fourPentagonOneOrientation 1 := hone
  have hH₀card : H₀.card = 3 := by rw [hH₀]; decide
  have hH₁card : H₁.card = 3 := by rw [hH₁]; decide
  have hsplit0 := Finset.card_filter_add_card_filter_not
    (s := G) (fun Q => 0 ∈ Q)
  have hG₀eq : G.filter (fun Q => ¬0 ∈ Q) = G₀ := by rfl
  rw [show G.filter (fun Q => 0 ∈ Q) = H₀ from rfl, hG₀eq,
    hGcard, hH₀card] at hsplit0
  have hfilterOne : G₀.filter (fun Q => 1 ∈ Q) = H₁ := by
    ext Q
    simp only [G₀, H₁, Finset.mem_filter]
    constructor
    · rintro ⟨⟨hQG, hQ0⟩, hQ1⟩
      exact ⟨hQG, hQ1⟩
    · rintro ⟨hQG, hQ1⟩
      have hQcan := hGsub hQG
      have hQ0 : 0 ∉ Q := by
        intro h0
        exact candidate_not_mem_zero_and_one Q hQcan ⟨h0, hQ1⟩
      exact ⟨⟨hQG, hQ0⟩, hQ1⟩
  have hsplit1 := Finset.card_filter_add_card_filter_not
    (s := G₀) (fun Q => 1 ∈ Q)
  have hReq : G₀.filter (fun Q => ¬1 ∈ Q) = R := by rfl
  rw [hfilterOne, hReq, hH₁card] at hsplit1
  have hRcard : R.card = 7 := by omega
  have hforced : fourPentagonForcedSix = H₀ ∪ H₁ := by
    rw [hH₀, hH₁]
    rfl
  have hRsub : R ⊆ fourPentagonResidualCandidates := by
    intro Q hQR
    have hQR' := Finset.mem_filter.mp hQR
    have hQG₀ := Finset.mem_filter.mp hQR'.1
    have hQG := hQG₀.1
    apply Finset.mem_filter.mpr
    refine ⟨hGsub hQG, hQG₀.2, hQR'.2, ?_⟩
    intro A hA
    have hA' : A ∈ H₀ ∪ H₁ := by rw [← hforced]; exact hA
    have hAG : A ∈ G := by
      rcases Finset.mem_union.mp hA' with hA0 | hA1
      · exact (Finset.mem_filter.mp hA0).1
      · exact (Finset.mem_filter.mp hA1).1
    by_cases hQA : Q = A
    · subst A
      have hQ0 := hQG₀.2
      rcases Finset.mem_union.mp hA' with hA0 | hA1
      · exact (hQ0 (Finset.mem_filter.mp hA0).2).elim
      · exact (hQR'.2 (Finset.mem_filter.mp hA1).2).elim
    · exact hcompat Q hQG A hAG hQA
  have hRcompat : fourPentagonCompatible R := by
    intro Q hQ A hA hne
    exact hcompat Q (Finset.mem_filter.mp (Finset.mem_filter.mp hQ).1).1
      A (Finset.mem_filter.mp (Finset.mem_filter.mp hA).1).1 hne
  have hRequality : R = fourPentagonResidualEquality :=
    residual_eq_of_card_eq_seven R hRsub hRcompat hRcard
  have hrequired (j : Fin 7) :
      fourPentagonRequiredFourSupport j ∈ G := by
    fin_cases j
    · have : fourPentagonRequiredFourSupport 0 ∈ H₀ := by
        rw [hH₀]
        decide
      exact (Finset.mem_filter.mp this).1
    · have : fourPentagonRequiredFourSupport 1 ∈ H₀ := by
        rw [hH₀]
        decide
      exact (Finset.mem_filter.mp this).1
    · have : fourPentagonRequiredFourSupport 2 ∈ H₀ := by
        rw [hH₀]
        decide
      exact (Finset.mem_filter.mp this).1
    · have : fourPentagonRequiredFourSupport 3 ∈ H₁ := by
        rw [hH₁]
        decide
      exact (Finset.mem_filter.mp this).1
    · have : fourPentagonRequiredFourSupport 4 ∈ H₁ := by
        rw [hH₁]
        decide
      exact (Finset.mem_filter.mp this).1
    · have : fourPentagonRequiredFourSupport 5 ∈ H₁ := by
        rw [hH₁]
        decide
      exact (Finset.mem_filter.mp this).1
    · have : fourPentagonRequiredFourSupport 6 ∈ R := by
        rw [hRequality]
        decide
      exact (Finset.mem_filter.mp (Finset.mem_filter.mp this).1).1
  have hexists (j : Fin 7) : ∃ b ∈ S.blocksOfSize 4,
      relabeledSupport P (S.support b) =
        fourPentagonRequiredFourSupport j := by
    simpa [G, pulledFourFamily] using hrequired j
  let four : Fin 7 → Block := fun j => Classical.choose (hexists j)
  have hfourMem (j : Fin 7) : four j ∈ S.blocksOfSize 4 :=
    (Classical.choose_spec (hexists j)).1
  have hfourSupport (j : Fin 7) :
      relabeledSupport P (S.support (four j)) =
        fourPentagonRequiredFourSupport j :=
    (Classical.choose_spec (hexists j)).2
  exact {
    point := P
    five := five
    four := four
    five_size := fun j => S.mem_blocksOfSize.mp (hfiveMem j)
    four_size := fun j => S.mem_blocksOfSize.mp (hfourMem j)
    mem_five := hfive
    mem_four := by
      intro i j
      have hi := Finset.ext_iff.mp (hfourSupport j) i
      simpa using hi }

/-! ## The four-five-block moment entrance -/

/-- Four five-blocks on ten points, under the raw five-point cap and the
`6/9` three-block degree profile, have the canonical four-pentagon finite
normal form. -/
noncomputable def fourPentagonFiniteNormalForm
    {Point Block : Type*} [Fintype Point] [Fintype Block]
    [DecidableEq Point]
    (S : BlockSystem Point Block)
    (hPoint : Fintype.card Point = 10)
    (hcap : ∀ b : Block, 3 ≤ (S.support b).card →
      (S.support b).card ≤ 5)
    (hd3 : ∀ p : Point, S.blockDegree 3 p = 6 ∨
      S.blockDegree 3 p = 9)
    (hfive : S.blockCount 5 = 4) :
    FourPentagonFiniteNormalForm S := by
  classical
  have hd5le (p : Point) : S.blockDegree 5 p ≤ 4 := by
    have h := degreeIn_le_card S (S.blocksOfSize 5) p
    change S.blockDegree 5 p ≤ S.blockCount 5 at h
    omega
  have hfirst : (∑ p : Point, S.blockDegree 5 p) = 20 := by
    have h := S.block_incidence 5
    rw [hfive] at h
    norm_num at h
    exact h
  have hsecond :
      (∑ p : Point, Nat.choose (S.blockDegree 5 p) 2) ≤ 12 := by
    have h := S.second_moment_le_two_choose (S.blocksOfSize 5)
    change (∑ p : Point, Nat.choose (S.blockDegree 5 p) 2) ≤
      2 * Nat.choose (S.blockCount 5) 2 at h
    rw [hfive] at h
    norm_num [Nat.choose] at h
    exact h
  have hrows := ten_fourFamily_degree_profile hPoint
    (fun p => S.blockDegree 5 p) hd5le hfirst hsecond
  have helevenOrTwelve := hrows.resolve_left (by
    intro hten
    exact secondMoment_ten_row_impossible S hPoint hcap hd3 hfive hten.2)
  have htwelve := helevenOrTwelve.resolve_left (by
    intro heleven
    exact secondMoment_eleven_row_impossible S hPoint hcap hd3 hfive
      heleven.2.1 heleven.2.2.1 heleven.2.2.2 heleven.1)
  have hresult : FourPentagonFiniteNormalForm S := by
    let N := fiveNormalForm_of_secondMoment_twelve S hPoint hfive
      htwelve.2.1 htwelve.2.2.1 htwelve.2.2.2 htwelve.1
    let P : Fin 10 ≃ Point := N.point
    let five : Fin 4 → Block := N.five
    have hfiveMem (j : Fin 4) : five j ∈ S.blocksOfSize 5 := by
      simpa [five] using N.five_mem j
    have hmemFive (i : Fin 10) (j : Fin 4) :
        P i ∈ S.support (five j) ↔
          i ∈ fourPentagonFiveSupport j := by
      simpa [P, five] using N.mem_five i j
    have hsupportInj : Function.Injective fourPentagonFiveSupport := by
      decide
    have hfiveInj : Function.Injective five := by
      intro j k hjk
      apply hsupportInj
      ext i
      rw [← hmemFive i j, ← hmemFive i k, hjk]
    have hd5zeroLower : 3 ≤ S.blockDegree 5 (P 0) := by
      let A : Finset Block := {five 0, five 1, five 2}
      have hAcard : A.card = 3 := by
        simp [A, hfiveInj.eq_iff]
      have hAsub : A ⊆
          (S.blocksOfSize 5).filter fun b => P 0 ∈ S.support b := by
        intro b hb
        simp only [A, Finset.mem_insert, Finset.mem_singleton] at hb
        rcases hb with rfl | rfl | rfl
        · exact Finset.mem_filter.mpr
            ⟨hfiveMem 0, (hmemFive 0 0).2 (by decide)⟩
        · exact Finset.mem_filter.mpr
            ⟨hfiveMem 1, (hmemFive 0 1).2 (by decide)⟩
        · exact Finset.mem_filter.mpr
            ⟨hfiveMem 2, (hmemFive 0 2).2 (by decide)⟩
      have hle := Finset.card_le_card hAsub
      change 3 ≤ ((S.blocksOfSize 5).filter
        fun b => P 0 ∈ S.support b).card
      rw [← hAcard]
      exact hle
    have hd5oneLower : 3 ≤ S.blockDegree 5 (P 1) := by
      let A : Finset Block := {five 0, five 1, five 3}
      have hAcard : A.card = 3 := by
        simp [A, hfiveInj.eq_iff]
      have hAsub : A ⊆
          (S.blocksOfSize 5).filter fun b => P 1 ∈ S.support b := by
        intro b hb
        simp only [A, Finset.mem_insert, Finset.mem_singleton] at hb
        rcases hb with rfl | rfl | rfl
        · exact Finset.mem_filter.mpr
            ⟨hfiveMem 0, (hmemFive 1 0).2 (by decide)⟩
        · exact Finset.mem_filter.mpr
            ⟨hfiveMem 1, (hmemFive 1 1).2 (by decide)⟩
        · exact Finset.mem_filter.mpr
            ⟨hfiveMem 3, (hmemFive 1 3).2 (by decide)⟩
      have hle := Finset.card_le_card hAsub
      change 3 ≤ ((S.blocksOfSize 5).filter
        fun b => P 1 ∈ S.support b).card
      rw [← hAcard]
      exact hle
    have hd5zero : S.blockDegree 5 (P 0) = 3 := by
      rcases htwelve.2.2.2 (P 0) with h1 | h23
      · change S.blockDegree 5 (P 0) = 1 at h1
        rw [h1] at hd5zeroLower
        omega
      · rcases h23 with h2 | h3
        · change S.blockDegree 5 (P 0) = 2 at h2
          rw [h2] at hd5zeroLower
          omega
        · exact h3
    have hd5one : S.blockDegree 5 (P 1) = 3 := by
      rcases htwelve.2.2.2 (P 1) with h1 | h23
      · change S.blockDegree 5 (P 1) = 1 at h1
        rw [h1] at hd5oneLower
        omega
      · rcases h23 with h2 | h3
        · change S.blockDegree 5 (P 1) = 2 at h2
          rw [h2] at hd5oneLower
          omega
        · exact h3
    let G := pulledFourFamily S P
    have hGsub : G ⊆ fourPentagonCandidates := by
      simpa [G] using pulledFourFamily_subset_candidates
        S P five hfiveMem hmemFive
    have hGcompat : fourPentagonCompatible G := by
      simpa [G] using pulledFourFamily_compatible S P
    have hGcard : G.card = S.blockCount 4 := by
      simpa [G] using pulledFourFamily_card S P
    have hB4upper : S.blockCount 4 ≤ 13 := by
      have h := compatible_candidates_card_le_thirteen G hGsub hGcompat
      rw [hGcard] at h
      exact h
    have hB4lower := blockCount_four_ge_thirteen
      S hPoint hcap hd3 hfive
    have hB4 : S.blockCount 4 = 13 :=
      Nat.le_antisymm hB4upper hB4lower
    let H0 := G.filter fun Q => 0 ∈ Q
    let H1 := G.filter fun Q => 1 ∈ Q
    have hH0sub : H0 ⊆ fourPentagonAtZero := by
      intro Q hQ
      change Q ∈ fourPentagonCandidates.filter (fun R => 0 ∈ R)
      have hQ' := Finset.mem_filter.mp hQ
      exact Finset.mem_filter.mpr ⟨hGsub hQ'.1, hQ'.2⟩
    have hH1sub : H1 ⊆ fourPentagonAtOne := by
      intro Q hQ
      change Q ∈ fourPentagonCandidates.filter (fun R => 1 ∈ R)
      have hQ' := Finset.mem_filter.mp hQ
      exact Finset.mem_filter.mpr ⟨hGsub hQ'.1, hQ'.2⟩
    have hH0compat : fourPentagonCompatible H0 := by
      intro Q hQ R hR hne
      exact hGcompat Q (Finset.mem_filter.mp hQ).1
        R (Finset.mem_filter.mp hR).1 hne
    have hH1compat : fourPentagonCompatible H1 := by
      intro Q hQ R hR hne
      exact hGcompat Q (Finset.mem_filter.mp hQ).1
        R (Finset.mem_filter.mp hR).1 hne
    have hfilter0 : H0.card = S.blockDegree 4 (P 0) := by
      simpa [H0, G] using pulledFourFamily_filter_card S P 0
    have hfilter1 : H1.card = S.blockDegree 4 (P 1) := by
      simpa [H1, G] using pulledFourFamily_filter_card S P 1
    have hledger0 := zero_local_ledger H0 hH0sub hH0compat
    have hledger1 := one_local_ledger H1 hH1sub hH1compat
    have hH0card : H0.card = 3 := by
      have hpairs := ten_pair_row S hPoint hcap (P 0)
      rw [hd5zero] at hpairs
      have hle : S.blockDegree 4 (P 0) ≤ 3 := by
        rw [← hfilter0]
        exact hledger0.1
      rcases hd3 (P 0) with h6 | h9
      · rw [h6] at hpairs
        omega
      · rw [h9] at hpairs
        omega
    have hH1card : H1.card = 3 := by
      have hpairs := ten_pair_row S hPoint hcap (P 1)
      rw [hd5one] at hpairs
      have hle : S.blockDegree 4 (P 1) ≤ 3 := by
        rw [← hfilter1]
        exact hledger1.1
      rcases hd3 (P 1) with h6 | h9
      · rw [h6] at hpairs
        omega
      · rw [h9] at hpairs
        omega
    let o0 : Fin 2 := Classical.choose (hledger0.2 hH0card)
    have ho0 : H0 = fourPentagonZeroOrientation o0 := by
      simpa [o0] using Classical.choose_spec (hledger0.2 hH0card)
    let o1 : Fin 2 := Classical.choose (hledger1.2 hH1card)
    have ho1 : H1 = fourPentagonOneOrientation o1 := by
      simpa [o1] using Classical.choose_spec (hledger1.2 hH1card)
    have hUnionCompat : fourPentagonCompatible (H0 ∪ H1) := by
      intro Q hQ R hR hne
      apply hGcompat Q
      · rcases Finset.mem_union.mp hQ with hQ0 | hQ1
        · exact (Finset.mem_filter.mp hQ0).1
        · exact (Finset.mem_filter.mp hQ1).1
      · rcases Finset.mem_union.mp hR with hR0 | hR1
        · exact (Finset.mem_filter.mp hR0).1
        · exact (Finset.mem_filter.mp hR1).1
      · exact hne
    have horientNe : o0 ≠ o1 := by
      intro heq
      have ho1same : H1 = fourPentagonOneOrientation o0 :=
        ho1.trans (congrArg fourPentagonOneOrientation heq.symm)
      have hsame : fourPentagonCompatible
          (fourPentagonZeroOrientation o0 ∪
            fourPentagonOneOrientation o0) := by
        rw [← ho0, ← ho1same]
        exact hUnionCompat
      exact same_orientations_conflict o0 hsame
    have horient := finTwo_ne_orientations horientNe
    have hnormal : Nonempty (FourPentagonFiniteNormalForm S) := by
      rcases horient with hdirect | hswapped
      · rcases hdirect with ⟨ho0zero, ho1one⟩
        have hzero : H0 = fourPentagonZeroOrientation 0 :=
          ho0.trans (congrArg fourPentagonZeroOrientation ho0zero)
        have hone : H1 = fourPentagonOneOrientation 1 :=
          ho1.trans (congrArg fourPentagonOneOrientation ho1one)
        exact ⟨fullNormalForm_of_oriented_family S P five hfiveMem hmemFive
          hB4 (by simpa [H0, G] using hzero)
            (by simpa [H1, G] using hone)⟩
      · rcases hswapped with ⟨ho0one, ho1zero⟩
        have hzero : H0 = fourPentagonZeroOrientation 1 :=
          ho0.trans (congrArg fourPentagonZeroOrientation ho0one)
        have hone : H1 = fourPentagonOneOrientation 0 :=
          ho1.trans (congrArg fourPentagonOneOrientation ho1zero)
        refine ⟨?_⟩
        let P' : Fin 10 ≃ Point := fourPentagonSwapEightNine.trans P
        have hmemFive' (i : Fin 10) (j : Fin 4) :
            P' i ∈ S.support (five j) ↔
              i ∈ fourPentagonFiveSupport j := by
          change P (fourPentagonSwapEightNine i) ∈ S.support (five j) ↔
            i ∈ fourPentagonFiveSupport j
          rw [hmemFive]
          exact mem_fourPentagonFiveSupport_swap i j
        have hzero' :
            (pulledFourFamily S P').filter (fun Q => 0 ∈ Q) =
              fourPentagonZeroOrientation 0 := by
          rw [show pulledFourFamily S P' =
            (pulledFourFamily S P).image fourPentagonSwapSupport by
              simpa [P'] using pulledFourFamily_swap S P]
          rw [filter_zero_image_swap]
          have h0 : (pulledFourFamily S P).filter (fun Q => 0 ∈ Q) =
              fourPentagonZeroOrientation 1 := by
            simpa [H0, G] using hzero
          rw [h0, swap_zero_orientation]
        have hone' :
            (pulledFourFamily S P').filter (fun Q => 1 ∈ Q) =
              fourPentagonOneOrientation 1 := by
          rw [show pulledFourFamily S P' =
            (pulledFourFamily S P).image fourPentagonSwapSupport by
              simpa [P'] using pulledFourFamily_swap S P]
          rw [filter_one_image_swap]
          have h1 : (pulledFourFamily S P).filter (fun Q => 1 ∈ Q) =
              fourPentagonOneOrientation 0 := by
            simpa [H1, G] using hone
          rw [h1, swap_one_orientation]
        exact fullNormalForm_of_oriented_family S P' five hfiveMem
          hmemFive' hB4 hzero' hone'
    exact Classical.choice hnormal
  exact hresult

end Erdos506.Finite

