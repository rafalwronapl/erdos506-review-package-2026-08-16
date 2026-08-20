import Erdos506.Block.Moments
import Erdos506.Finite.Packing
import Mathlib.Tactic

/-!
# Generic profile lemmas for the ten-point four-pentagon branch

This module isolates the small finite-cardinality, moment-profile, and
common-pair estimates shared by the row eliminations and the final normalizer.
-/

namespace Erdos506.Finite

open Erdos506.Block
open Erdos506.Block.BlockSystem
open scoped BigOperators

namespace FourPentagonProfile

theorem card_preimage_equiv
    {α β : Type*} [Fintype α] [Fintype β]
    (e : α ≃ β) (A : Finset β) :
    (A.preimage e e.injective.injOn).card = A.card := by
  classical
  rw [Finset.card_preimage]
  simp

theorem degreeIn_le_card
    {Point Block : Type*} [Fintype Point] [Fintype Block]
    [DecidableEq Point]
    (S : BlockSystem Point Block) (F : Finset Block) (p : Point) :
    S.degreeIn F p ≤ F.card := by
  classical
  exact Finset.card_filter_le _ _

theorem sum_degreeIn_over_support
    {Point Block : Type*} [Fintype Point] [Fintype Block]
    [DecidableEq Point]
    (S : BlockSystem Point Block) (F : Finset Block) (b : Block) :
    (∑ x ∈ S.support b, S.degreeIn F x) =
      ∑ c ∈ F, (S.support b ∩ S.support c).card := by
  classical
  simp only [BlockSystem.degreeIn, Finset.card_eq_sum_ones,
    Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro c hc
  simp

theorem support_injOn_blocksOfSize
    {Point Block : Type*} [Fintype Point] [Fintype Block]
    [DecidableEq Point]
    (S : BlockSystem Point Block) (s : Nat) (hs : 3 ≤ s) :
    Set.InjOn S.support (S.blocksOfSize s : Set Block) := by
  classical
  intro b hb c hc hsupport
  have hbcard : (S.support b).card = s := S.mem_blocksOfSize.mp hb
  obtain ⟨A, hAsub, hAcard⟩ :=
    Finset.exists_subset_card_eq (show 3 ≤ (S.support b).card by omega)
  let K : KSubset Point 3 := ⟨A, hAcard⟩
  have hbOwner : b = S.tripleOwner K := S.triple_unique K b hAsub
  have hcOwner : c = S.tripleOwner K := by
    apply S.triple_unique K c
    intro x hx
    rw [← hsupport]
    exact hAsub hx
  exact hbOwner.trans hcOwner.symm

theorem blockCount_eq_zero_of_fiveCap
    {Point Block : Type*} [Fintype Point] [Fintype Block]
    [DecidableEq Point]
    (S : BlockSystem Point Block)
    (hcap : ∀ b : Block, 3 ≤ (S.support b).card →
      (S.support b).card ≤ 5)
    {s : Nat} (hs : 5 < s) : S.blockCount s = 0 := by
  classical
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro b hb
  have hsize := S.mem_blocksOfSize.mp hb
  have hle := hcap b (by omega)
  omega

theorem blockDegree_eq_zero_of_blockCount_eq_zero
    {Point Block : Type*} [Fintype Point] [Fintype Block]
    [DecidableEq Point]
    (S : BlockSystem Point Block) (s : Nat) (p : Point)
    (hzero : S.blockCount s = 0) : S.blockDegree s p = 0 := by
  have hinc := S.block_incidence s
  rw [hzero] at hinc
  have hle : S.blockDegree s p ≤ ∑ q : Point, S.blockDegree s q := by
    exact Finset.single_le_sum
      (fun q _hq => Nat.zero_le (S.blockDegree s q)) (Finset.mem_univ p)
  omega

/-- The ten-point local pair row, stated only with the raw finite cap. -/
theorem ten_pair_row
    {Point Block : Type*} [Fintype Point] [Fintype Block]
    [DecidableEq Point]
    (S : BlockSystem Point Block) (hPoint : Fintype.card Point = 10)
    (hcap : ∀ b : Block, 3 ≤ (S.support b).card →
      (S.support b).card ≤ 5) (p : Point) :
    S.blockDegree 3 p + 3 * S.blockDegree 4 p +
      6 * S.blockDegree 5 p = 36 := by
  have hb6 := blockCount_eq_zero_of_fiveCap S hcap (s := 6) (by omega)
  have hb7 := blockCount_eq_zero_of_fiveCap S hcap (s := 7) (by omega)
  have hb8 := blockCount_eq_zero_of_fiveCap S hcap (s := 8) (by omega)
  have hb9 := blockCount_eq_zero_of_fiveCap S hcap (s := 9) (by omega)
  have hb10 := blockCount_eq_zero_of_fiveCap S hcap (s := 10) (by omega)
  have hd6 := blockDegree_eq_zero_of_blockCount_eq_zero S 6 p hb6
  have hd7 := blockDegree_eq_zero_of_blockCount_eq_zero S 7 p hb7
  have hd8 := blockDegree_eq_zero_of_blockCount_eq_zero S 8 p hb8
  have hd9 := blockDegree_eq_zero_of_blockCount_eq_zero S 9 p hb9
  have hd10 := blockDegree_eq_zero_of_blockCount_eq_zero S 10 p hb10
  have hpairs := S.pivot_pair_partition p
  rw [hPoint] at hpairs
  norm_num [Finset.sum_range_succ, Nat.choose,
    hd6, hd7, hd8, hd9, hd10] at hpairs
  exact hpairs

theorem blockCount_three_eq_twenty_add_high
    {Point Block : Type*} [Fintype Point] [Fintype Block]
    [DecidableEq Point]
    (S : BlockSystem Point Block) (hPoint : Fintype.card Point = 10)
    (hd3 : ∀ p : Point, S.blockDegree 3 p = 6 ∨
      S.blockDegree 3 p = 9) :
    S.blockCount 3 = 20 +
      ((Finset.univ : Finset Point).filter
        fun p => S.blockDegree 3 p = 9).card := by
  classical
  have hpoint (p : Point) :
      S.blockDegree 3 p =
        6 + 3 * (if S.blockDegree 3 p = 9 then 1 else 0) := by
    rcases hd3 p with h6 | h9
    · simp [h6]
    · simp [h9]
  have hsum := S.block_incidence 3
  have hindicator :
      (∑ p : Point, if S.blockDegree 3 p = 9 then 1 else 0) =
        ((Finset.univ : Finset Point).filter
          fun p => S.blockDegree 3 p = 9).card := by simp
  have hmul : S.blockCount 3 * 3 =
      (20 + ((Finset.univ : Finset Point).filter
        fun p => S.blockDegree 3 p = 9).card) * 3 := by
    calc
      S.blockCount 3 * 3 = ∑ p : Point, S.blockDegree 3 p := by
        simpa [Nat.mul_comm] using hsum.symm
      _ = ∑ p : Point,
          (6 + 3 * (if S.blockDegree 3 p = 9 then 1 else 0)) := by
        apply Finset.sum_congr rfl
        intro p _hp
        exact hpoint p
      _ = 60 + 3 * ((Finset.univ : Finset Point).filter
          fun p => S.blockDegree 3 p = 9).card := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, hindicator]
        simp [hPoint]
      _ = _ := by ring
  omega

theorem blockCount_four_ge_thirteen
    {Point Block : Type*} [Fintype Point] [Fintype Block]
    [DecidableEq Point]
    (S : BlockSystem Point Block) (hPoint : Fintype.card Point = 10)
    (hcap : ∀ b : Block, 3 ≤ (S.support b).card →
      (S.support b).card ≤ 5)
    (hd3 : ∀ p : Point, S.blockDegree 3 p = 6 ∨
      S.blockDegree 3 p = 9)
    (hfive : S.blockCount 5 = 4) :
    13 ≤ S.blockCount 4 := by
  classical
  have hb6 := blockCount_eq_zero_of_fiveCap S hcap (s := 6) (by omega)
  have hb7 := blockCount_eq_zero_of_fiveCap S hcap (s := 7) (by omega)
  have hb8 := blockCount_eq_zero_of_fiveCap S hcap (s := 8) (by omega)
  have hb9 := blockCount_eq_zero_of_fiveCap S hcap (s := 9) (by omega)
  have hb10 := blockCount_eq_zero_of_fiveCap S hcap (s := 10) (by omega)
  have htriple := S.triple_partition_by_size
  rw [hPoint] at htriple
  norm_num [Finset.sum_range_succ, Nat.choose, hfive,
    hb6, hb7, hb8, hb9, hb10] at htriple
  have hhigh := blockCount_three_eq_twenty_add_high S hPoint hd3
  have hhighLe :
      ((Finset.univ : Finset Point).filter
        fun p => S.blockDegree 3 p = 9).card ≤ 10 := by
    calc
      _ ≤ Fintype.card Point := Finset.card_le_univ _
      _ = 10 := hPoint
  omega

theorem card_three_sum_five_le_two
    {α : Type*} [DecidableEq α] (A : Finset α) (f : α → Nat)
    (hcard : A.card = 3) (hle : ∀ a ∈ A, f a ≤ 2)
    (hsum : ∑ a ∈ A, f a = 5) :
    ∃ a ∈ A, f a = 1 ∧ ∀ c ∈ A, c ≠ a → f c = 2 := by
  classical
  have hone (c : α) (hc : c ∈ A) : 1 ≤ f c := by
    have hrest : (∑ a ∈ A.erase c, f a) ≤ 4 := by
      calc
        (∑ a ∈ A.erase c, f a) ≤ ∑ _a ∈ A.erase c, 2 := by
          apply Finset.sum_le_sum
          intro a ha
          exact hle a (Finset.mem_of_mem_erase ha)
        _ = 4 := by simp [Finset.card_erase_of_mem hc, hcard]
    have hsplit := Finset.sum_erase_add A f hc
    omega
  have hex : ∃ a ∈ A, f a = 1 := by
    by_contra hnot
    push Not at hnot
    have hall : ∀ a ∈ A, f a = 2 := by
      intro a ha
      have := hone a ha
      have := hle a ha
      have := hnot a ha
      omega
    have hsum6 : (∑ a ∈ A, f a) = 6 := by
      calc
        _ = ∑ _a ∈ A, 2 := by
          apply Finset.sum_congr rfl
          intro a ha
          exact hall a ha
        _ = 6 := by simp [hcard]
    omega
  obtain ⟨a, ha, haone⟩ := hex
  refine ⟨a, ha, haone, ?_⟩
  intro c hc hca
  have hcErase : c ∈ A.erase a := Finset.mem_erase.mpr ⟨hca, hc⟩
  have hRcard : ((A.erase a).erase c).card = 1 := by
    rw [Finset.card_erase_of_mem hcErase,
      Finset.card_erase_of_mem ha, hcard]
  have hrest : (∑ z ∈ (A.erase a).erase c, f z) ≤ 2 := by
    calc
      _ ≤ ∑ _z ∈ (A.erase a).erase c, 2 := by
        apply Finset.sum_le_sum
        intro z hz
        exact hle z (Finset.mem_of_mem_erase
          (Finset.mem_of_mem_erase hz))
      _ = 2 := by simp [hRcard]
  have hsplitA := Finset.sum_erase_add A f ha
  have hsplitC := Finset.sum_erase_add (A.erase a) f hcErase
  have hcUpper := hle c hc
  have hcLower := hone c hc
  omega

theorem blockDegree_four_le_four_of_common_pair
    {Point Block : Type*} [Fintype Point] [Fintype Block]
    [DecidableEq Point]
    (S : BlockSystem Point Block) (hPoint : Fintype.card Point = 10)
    (x y : Point) (hxy : x ≠ y)
    (hcommon : ∀ b ∈ S.blocksOfSize 4,
      x ∈ S.support b → y ∈ S.support b) :
    S.blockDegree 4 x ≤ 4 := by
  classical
  let H := (S.blocksOfSize 4).filter fun b => x ∈ S.support b
  let O := (Finset.univ : Finset Point) \ {x, y}
  let away : Block → Finset Point := fun b => S.support b \ {x, y}
  let P := H.image away
  have hOcard : O.card = 8 := by
    rw [Finset.card_sdiff_of_subset (by simp : ({x, y} : Finset Point) ⊆
      (Finset.univ : Finset Point))]
    simp [hPoint, hxy]
  have hawayCard (b : Block) (hb : b ∈ H) : (away b).card = 2 := by
    have hb' := Finset.mem_filter.mp hb
    have hxmem : x ∈ S.support b := hb'.2
    have hymem : y ∈ S.support b := hcommon b hb'.1 hxmem
    have hpair : ({x, y} : Finset Point) ⊆ S.support b := by
      intro z hz
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with rfl | rfl
      · exact hxmem
      · exact hymem
    change (S.support b \ {x, y}).card = 2
    rw [Finset.card_sdiff_of_subset hpair,
      S.mem_blocksOfSize.mp hb'.1]
    simp [hxy]
  have hawayInj : Set.InjOn away (H : Set Block) := by
    intro b hb c hc heq
    have hb' := Finset.mem_filter.mp hb
    have hc' := Finset.mem_filter.mp hc
    have hxb : x ∈ S.support b := hb'.2
    have hxc : x ∈ S.support c := hc'.2
    have hyb : y ∈ S.support b := hcommon b hb'.1 hxb
    have hyc : y ∈ S.support c := hcommon c hc'.1 hxc
    apply support_injOn_blocksOfSize S 4 (by omega) hb'.1 hc'.1
    ext z
    by_cases hzx : z = x
    · subst z; simp [hxb, hxc]
    by_cases hzy : z = y
    · subst z; simp [hyb, hyc]
    have hz := Finset.ext_iff.mp heq z
    simpa [away, hzx, hzy] using hz
  have hPcard : P.card = H.card := by
    exact Finset.card_image_iff.mpr hawayInj
  have hPsub (Q : Finset Point) (hQ : Q ∈ P) : Q ⊆ O := by
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hQ
    intro z hz
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ z,
      (Finset.mem_sdiff.mp hz).2⟩
  have hPsize (Q : Finset Point) (hQ : Q ∈ P) : Q.card = 2 := by
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hQ
    exact hawayCard b hb
  have hPinter (Q : Finset Point) (hQ : Q ∈ P)
      (R : Finset Point) (hR : R ∈ P) (hQR : Q ≠ R) :
      (Q ∩ R).card < 1 := by
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hQ
    obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hR
    have hbc : b ≠ c := by
      intro h
      subst c
      exact hQR rfl
    have hb' := Finset.mem_filter.mp hb
    have hc' := Finset.mem_filter.mp hc
    have hxmem : x ∈ S.support b ∩ S.support c :=
      Finset.mem_inter.mpr ⟨hb'.2, hc'.2⟩
    have hymem : y ∈ S.support b ∩ S.support c :=
      Finset.mem_inter.mpr ⟨hcommon b hb'.1 hb'.2,
        hcommon c hc'.1 hc'.2⟩
    have hinter := S.distinct_block_inter_card_lt_three hbc
    apply Nat.lt_one_iff.mpr
    apply Finset.card_eq_zero.mpr
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro z hz
    have hz' := Finset.mem_inter.mp hz
    have hzb : z ∈ S.support b := (Finset.mem_sdiff.mp hz'.1).1
    have hzc : z ∈ S.support c := (Finset.mem_sdiff.mp hz'.2).1
    have hzx : z ≠ x := by
      intro h; subst z
      exact (Finset.mem_sdiff.mp hz'.1).2 (by simp)
    have hzy : z ≠ y := by
      intro h; subst z
      exact (Finset.mem_sdiff.mp hz'.1).2 (by simp)
    have hthree : ({x, y, z} : Finset Point) ⊆
        S.support b ∩ S.support c := by
      intro w hw
      simp only [Finset.mem_insert, Finset.mem_singleton] at hw
      rcases hw with rfl | rfl | rfl
      · exact hxmem
      · exact hymem
      · exact Finset.mem_inter.mpr ⟨hzb, hzc⟩
    have hcard := Finset.card_le_card hthree
    have hxyz : ({x, y, z} : Finset Point).card = 3 := by
      simp [hxy, Ne.symm hzx, Ne.symm hzy]
    omega
  have hpack := card_mul_choose_le_choose_of_pairwise_inter_lt
    O P 2 1 hPsub hPsize hPinter
  rw [hPcard, hOcard] at hpack
  change H.card ≤ 4
  norm_num [Nat.choose] at hpack
  omega


theorem card_six_sum_eleven_le_two
    {α : Type*} [DecidableEq α] (A : Finset α) (f : α → Nat)
    (hcard : A.card = 6) (hle : ∀ a ∈ A, f a ≤ 2)
    (hsum : ∑ a ∈ A, f a = 11) :
    ∃ a ∈ A, f a = 1 ∧ ∀ c ∈ A, c ≠ a → f c = 2 := by
  classical
  have hone (c : α) (hc : c ∈ A) : 1 ≤ f c := by
    have hrest : (∑ a ∈ A.erase c, f a) ≤ 10 := by
      calc
        _ ≤ ∑ _a ∈ A.erase c, 2 := by
          apply Finset.sum_le_sum
          intro a ha
          exact hle a (Finset.mem_of_mem_erase ha)
        _ = 10 := by simp [Finset.card_erase_of_mem hc, hcard]
    have hsplit := Finset.sum_erase_add A f hc
    omega
  have hex : ∃ a ∈ A, f a = 1 := by
    by_contra hnot
    push Not at hnot
    have hall : ∀ a ∈ A, f a = 2 := by
      intro a ha
      have := hone a ha
      have := hle a ha
      have := hnot a ha
      omega
    have hsum12 : (∑ a ∈ A, f a) = 12 := by
      calc
        _ = ∑ _a ∈ A, 2 := by
          apply Finset.sum_congr rfl
          intro a ha
          exact hall a ha
        _ = 12 := by simp [hcard]
    omega
  obtain ⟨a, ha, haone⟩ := hex
  refine ⟨a, ha, haone, ?_⟩
  intro c hc hca
  have hcErase : c ∈ A.erase a := Finset.mem_erase.mpr ⟨hca, hc⟩
  have hRcard : ((A.erase a).erase c).card = 4 := by
    rw [Finset.card_erase_of_mem hcErase,
      Finset.card_erase_of_mem ha, hcard]
  have hrest : (∑ z ∈ (A.erase a).erase c, f z) ≤ 8 := by
    calc
      _ ≤ ∑ _z ∈ (A.erase a).erase c, 2 := by
        apply Finset.sum_le_sum
        intro z hz
        exact hle z (Finset.mem_of_mem_erase
          (Finset.mem_of_mem_erase hz))
      _ = 8 := by simp [hRcard]
  have hsplitA := Finset.sum_erase_add A f ha
  have hsplitC := Finset.sum_erase_add (A.erase a) f hcErase
  have hcUpper := hle c hc
  have hcLower := hone c hc
  omega


theorem sum_add_filter_one_eq_two_mul_card_add_filter_three
    {α : Type*} [DecidableEq α] (A : Finset α) (d : α → Nat)
    (hprofile : ∀ x, x ∈ A → d x = 1 ∨ d x = 2 ∨ d x = 3) :
    (∑ x ∈ A, d x) + (A.filter fun x => d x = 1).card =
      2 * A.card + (A.filter fun x => d x = 3).card := by
  classical
  calc
    (∑ x ∈ A, d x) + (A.filter fun x => d x = 1).card =
        (∑ x ∈ A, d x) +
          ∑ x ∈ A, if d x = 1 then 1 else 0 := by
            congr 1
            rw [Finset.card_eq_sum_ones, Finset.sum_filter]
    _ = ∑ x ∈ A, (d x + if d x = 1 then 1 else 0) := by
          rw [Finset.sum_add_distrib]
    _ = ∑ x ∈ A, (2 + if d x = 3 then 1 else 0) := by
          apply Finset.sum_congr rfl
          intro x hx
          rcases hprofile x hx with h1 | h2 | h3
          · simp [h1]
          · simp [h2]
          · simp [h3]
    _ = 2 * A.card + (A.filter fun x => d x = 3).card := by
          rw [Finset.sum_add_distrib]
          have hindicator :
              (∑ x ∈ A, if d x = 3 then 1 else 0) =
                (A.filter fun x => d x = 3).card := by simp
          rw [hindicator]
          simp [Nat.mul_comm]

theorem fiveBlock_pair_inter_eq_two_of_secondMoment_twelve
    {Point Block : Type*} [Fintype Point] [Fintype Block]
    [DecidableEq Point]
    (S : BlockSystem Point Block) (hfive : S.blockCount 5 = 4)
    (hmoment : (∑ p : Point,
      Nat.choose (S.blockDegree 5 p) 2) = 12) :
    ∀ b ∈ S.blocksOfSize 5, ∀ c ∈ S.blocksOfSize 5,
      b ≠ c → (S.support b ∩ S.support c).card = 2 := by
  classical
  let F := S.blocksOfSize 5
  have hFcard : F.card = 4 := hfive
  have hpairTotal :
      (∑ A ∈ F.powersetCard 2, (S.commonSupport A).card) = 12 := by
    rw [← S.binomial_degree_moment F 2]
    exact hmoment
  have hconst : (∑ _A ∈ F.powersetCard 2, 2) = 12 := by
    simp [hFcard, Nat.choose]
  have htermLe : ∀ A ∈ F.powersetCard 2,
      (S.commonSupport A).card ≤ 2 := by
    intro A hA
    exact S.commonSupport_card_le_two (Finset.mem_powersetCard.mp hA).2
  have htotal :
      (∑ A ∈ F.powersetCard 2, (S.commonSupport A).card) =
        ∑ _A ∈ F.powersetCard 2, 2 := hpairTotal.trans hconst.symm
  intro b hb c hc hbc
  have hbcMem : ({b, c} : Finset Block) ∈ F.powersetCard 2 := by
    apply Finset.mem_powersetCard.mpr
    constructor
    · intro z hz
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with rfl | rfl
      · exact hb
      · exact hc
    · simp [hbc]
  have hterm := (Finset.sum_eq_sum_iff_of_le htermLe).mp
    htotal {b, c} hbcMem
  rw [S.commonSupport_pair] at hterm
  exact hterm

/-! ## The four-five-block moment entrance -/

theorem ten_fourFamily_degree_profile
    {Point : Type*} [Fintype Point] [DecidableEq Point]
    (hPoint : Fintype.card Point = 10) (d : Point → Nat)
    (hdle : ∀ p, d p ≤ 4)
    (hsum : (∑ p : Point, d p) = 20)
    (hsecond : (∑ p : Point, Nat.choose (d p) 2) ≤ 12) :
    let m := ∑ p : Point, Nat.choose (d p) 2
    (m = 10 ∧ ∀ p, d p = 2) ∨
      (m = 11 ∧
        ((Finset.univ : Finset Point).filter fun p => d p = 1).card = 1 ∧
        ((Finset.univ : Finset Point).filter fun p => d p = 3).card = 1 ∧
        ∀ p, d p = 1 ∨ d p = 2 ∨ d p = 3) ∨
      (m = 12 ∧
        ((Finset.univ : Finset Point).filter fun p => d p = 1).card = 2 ∧
        ((Finset.univ : Finset Point).filter fun p => d p = 3).card = 2 ∧
        ∀ p, d p = 1 ∨ d p = 2 ∨ d p = 3) := by
  classical
  dsimp only
  let n₀ := ((Finset.univ : Finset Point).filter fun p => d p = 0).card
  let n₁ := ((Finset.univ : Finset Point).filter fun p => d p = 1).card
  let n₃ := ((Finset.univ : Finset Point).filter fun p => d p = 3).card
  let n₄ := ((Finset.univ : Finset Point).filter fun p => d p = 4).card
  have hslackPoint (p : Point) :
      Nat.choose (d p) 2 + 3 =
        2 * d p + 3 * (if d p = 0 then 1 else 0) +
          (if d p = 1 then 1 else 0) +
          (if d p = 4 then 1 else 0) := by
    have hp := hdle p
    interval_cases hd : d p <;> norm_num [Nat.choose] at *
  have hbalancePoint (p : Point) :
      d p + 2 * (if d p = 0 then 1 else 0) +
          (if d p = 1 then 1 else 0) =
        2 + (if d p = 3 then 1 else 0) +
          2 * (if d p = 4 then 1 else 0) := by
    have hp := hdle p
    interval_cases hd : d p <;> norm_num at *
  have hslack :
      (∑ p : Point, (Nat.choose (d p) 2 + 3)) =
        ∑ p : Point,
          (2 * d p + 3 * (if d p = 0 then 1 else 0) +
            (if d p = 1 then 1 else 0) +
            (if d p = 4 then 1 else 0)) := by
    apply Finset.sum_congr rfl
    intro p _hp
    exact hslackPoint p
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, ← Finset.mul_sum] at hslack
  have hzero : (∑ p : Point, if d p = 0 then 1 else 0) = n₀ := by
    simp [n₀]
  have hone : (∑ p : Point, if d p = 1 then 1 else 0) = n₁ := by
    simp [n₁]
  have hthree : (∑ p : Point, if d p = 3 then 1 else 0) = n₃ := by
    simp [n₃]
  have hfour : (∑ p : Point, if d p = 4 then 1 else 0) = n₄ := by
    simp [n₄]
  rw [hsum, hPoint, hzero, hone, hfour] at hslack
  have hbalance :
      (∑ p : Point,
          (d p + 2 * (if d p = 0 then 1 else 0) +
            (if d p = 1 then 1 else 0))) =
        ∑ p : Point,
          (2 + (if d p = 3 then 1 else 0) +
            2 * (if d p = 4 then 1 else 0)) := by
    apply Finset.sum_congr rfl
    intro p _hp
    exact hbalancePoint p
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, ← Finset.mul_sum] at hbalance
  rw [hsum, hPoint, hzero, hone, hthree, hfour] at hbalance
  have hmLower : 10 ≤ ∑ p : Point, Nat.choose (d p) 2 := by omega
  have hn₀pos {p : Point} (hp : d p = 0) : 1 ≤ n₀ := by
    change 1 ≤ ((Finset.univ : Finset Point).filter
      fun q => d q = 0).card
    apply Finset.card_pos.mpr
    exact ⟨p, Finset.mem_filter.mpr ⟨Finset.mem_univ p, hp⟩⟩
  have hn₁pos {p : Point} (hp : d p = 1) : 1 ≤ n₁ := by
    change 1 ≤ ((Finset.univ : Finset Point).filter
      fun q => d q = 1).card
    apply Finset.card_pos.mpr
    exact ⟨p, Finset.mem_filter.mpr ⟨Finset.mem_univ p, hp⟩⟩
  have hn₃pos {p : Point} (hp : d p = 3) : 1 ≤ n₃ := by
    change 1 ≤ ((Finset.univ : Finset Point).filter
      fun q => d q = 3).card
    apply Finset.card_pos.mpr
    exact ⟨p, Finset.mem_filter.mpr ⟨Finset.mem_univ p, hp⟩⟩
  have hn₄pos {p : Point} (hp : d p = 4) : 1 ≤ n₄ := by
    change 1 ≤ ((Finset.univ : Finset Point).filter
      fun q => d q = 4).card
    apply Finset.card_pos.mpr
    exact ⟨p, Finset.mem_filter.mpr ⟨Finset.mem_univ p, hp⟩⟩
  interval_cases hm : (∑ p : Point, Nat.choose (d p) 2)
  · left
    constructor
    · rfl
    · intro p
      have hp := hdle p
      interval_cases hdp : d p
      · have hn := hn₀pos hdp; omega
      · have hn := hn₁pos hdp; omega
      · rfl
      · have hn := hn₃pos hdp; omega
      · have hn := hn₄pos hdp; omega
  · right; left
    have hn₀ : n₀ = 0 := by omega
    have hn₁ : n₁ = 1 := by omega
    have hn₃ : n₃ = 1 := by omega
    have hn₄ : n₄ = 0 := by omega
    refine ⟨rfl, ?_, ?_, ?_⟩
    · exact hn₁
    · exact hn₃
    · intro p
      have hp := hdle p
      interval_cases hdp : d p
      · have := hn₀pos hdp; omega
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr rfl)
      · have := hn₄pos hdp; omega
  · right; right
    have hn₀ : n₀ = 0 := by omega
    have hn₁ : n₁ = 2 := by omega
    have hn₃ : n₃ = 2 := by omega
    have hn₄ : n₄ = 0 := by omega
    refine ⟨rfl, ?_, ?_, ?_⟩
    · exact hn₁
    · exact hn₃
    · intro p
      have hp := hdle p
      interval_cases hdp : d p
      · have := hn₀pos hdp; omega
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr rfl)
      · have := hn₄pos hdp; omega


end FourPentagonProfile

end Erdos506.Finite
