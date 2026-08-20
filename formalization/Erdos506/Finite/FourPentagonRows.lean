import Erdos506.Block.Moments
import Erdos506.Finite.Packing
import Mathlib.Tactic

/-!
# Moment rows for the ten-point four-pentagon branch

This module contains only the raw finite moment identities, the eliminations
of the second-moment rows 10 and 11, and the positive profile of the surviving
row 12. Keeping these proofs opaque and separate prevents their large tactic
terms from being re-elaborated with the normalization ledgers.
-/

namespace Erdos506.Finite

open Erdos506.Block
open Erdos506.Block.BlockSystem
open scoped BigOperators

universe u v

namespace FourPentagonRows

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
    push_neg at hnot
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
  have hrest : (∑ z ∈ A.erase {a, c}, f z) ≤ 2 := by
    calc
      _ ≤ ∑ _z ∈ A.erase {a, c}, 2 := by
        apply Finset.sum_le_sum
        intro z hz
        exact hle z (Finset.mem_of_mem_erase hz)
      _ ≤ 2 := by
        have hsub : (A.erase {a, c}).card ≤ 1 := by
          rw [Finset.erase_eq_sdiff]
          have hacard : ({a, c} : Finset α).card = 2 := by simp [hca]
          have hsubset : ({a, c} : Finset α) ⊆ A := by simp [ha, hc]
          rw [Finset.card_sdiff_of_subset hsubset, hacard, hcard]
        simp only [Finset.sum_const, nsmul_eq_mul]
        omega
  have hsplitA := Finset.sum_erase_add A f ha
  have hcErase : c ∈ A.erase a := Finset.mem_erase.mpr ⟨hca, hc⟩
  have hsplitC := Finset.sum_erase_add (A.erase a) f hcErase
  have heraseEq : (A.erase a).erase c = A.erase {a, c} := by
    ext z
    simp [and_left_comm, and_assoc, and_comm]
  rw [heraseEq] at hsplitC
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
    have hpair : ({x, y} : Finset Point) ⊆ S.support b := by simp [hxmem, hymem]
    rw [away, Finset.card_sdiff_of_subset hpair,
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
      apply hQR
      simp [h]
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
        S.support b ∩ S.support c := by simp [hxmem, hymem, hzb, hzc]
    have hcard := Finset.card_le_card hthree
    have hxyz : ({x, y, z} : Finset Point).card = 3 := by
      simp [hxy, hzx, hzy, Ne.symm hzy]
    omega
  have hpack := card_mul_choose_le_choose_of_pairwise_inter_lt
    O P 2 1 hPsub hPsize hPinter
  rw [hPcard, hOcard] at hpack
  change H.card ≤ 4
  norm_num [Nat.choose] at hpack
  exact hpack

theorem secondMoment_ten_row_impossible
    {Point Block : Type*} [Fintype Point] [Fintype Block]
    [DecidableEq Point]
    (S : BlockSystem Point Block) (hPoint : Fintype.card Point = 10)
    (hcap : ∀ b : Block, 3 ≤ (S.support b).card →
      (S.support b).card ≤ 5)
    (hd3 : ∀ p : Point, S.blockDegree 3 p = 6 ∨
      S.blockDegree 3 p = 9)
    (hfive : S.blockCount 5 = 4)
    (hrow : ∀ p : Point, S.blockDegree 5 p = 2) : False := by
  classical
  let F := S.blocksOfSize 5
  have hFcard : F.card = 4 := hfive
  obtain ⟨b₀, hb₀⟩ : F.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro h
    have := congrArg Finset.card h
    simp [hFcard] at this
  have hinterLe (b : Block) (hb : b ∈ F) (c : Block) (hc : c ∈ F)
      (hbc : b ≠ c) : (S.support b ∩ S.support c).card ≤ 2 := by
    have := S.distinct_block_inter_card_lt_three hbc
    omega
  have hpairRow (b : Block) (hb : b ∈ F) :
      (∑ c ∈ F.erase b, (S.support b ∩ S.support c).card) = 5 := by
    have hleft : (∑ x ∈ S.support b, S.blockDegree 5 x) = 10 := by
      calc
        _ = ∑ _x ∈ S.support b, 2 := by
          apply Finset.sum_congr rfl
          intro x hx
          exact hrow x
        _ = 10 := by simp [S.mem_blocksOfSize.mp hb]
    have hfubini := sum_degreeIn_over_support S F b
    change (∑ x ∈ S.support b, S.blockDegree 5 x) = _ at hfubini
    rw [hleft] at hfubini
    have hsplit := Finset.sum_erase_add F
      (fun c => (S.support b ∩ S.support c).card) hb
    have hself : (S.support b ∩ S.support b).card = 5 := by
      simp [S.mem_blocksOfSize.mp hb]
    omega
  have hdeficient (b : Block) (hb : b ∈ F) :
      ∃ c ∈ F.erase b,
        (S.support b ∩ S.support c).card = 1 ∧
        ∀ d ∈ F.erase b, d ≠ c →
          (S.support b ∩ S.support d).card = 2 := by
    have hcard : (F.erase b).card = 3 := by
      rw [Finset.card_erase_of_mem hb, hFcard]
    apply card_three_sum_five_le_two
      (F.erase b) (fun c => (S.support b ∩ S.support c).card)
      hcard
    · intro c hc
      exact hinterLe b hb c (Finset.mem_of_mem_erase hc)
        (Finset.mem_erase.mp hc).1.symm
    · exact hpairRow b hb
  obtain ⟨b₁, hb₁erase, hb₀₁, hb₀other⟩ := hdeficient b₀ hb₀
  have hb₁ : b₁ ∈ F := Finset.mem_of_mem_erase hb₁erase
  have hb₀ne₁ : b₀ ≠ b₁ := (Finset.mem_erase.mp hb₁erase).1.symm
  let R := (F.erase b₀).erase b₁
  have hRcard : R.card = 2 := by
    rw [Finset.card_erase_of_mem hb₁erase,
      Finset.card_erase_of_mem hb₀, hFcard]
  obtain ⟨b₂, b₃, hb₂ne₃, hReq⟩ := Finset.card_eq_two.mp hRcard
  have hb₂R : b₂ ∈ R := by rw [hReq]; simp
  have hb₃R : b₃ ∈ R := by rw [hReq]; simp
  have hb₂ : b₂ ∈ F := Finset.mem_of_mem_erase
    (Finset.mem_of_mem_erase hb₂R)
  have hb₃ : b₃ ∈ F := Finset.mem_of_mem_erase
    (Finset.mem_of_mem_erase hb₃R)
  have hb₂ne₀ : b₂ ≠ b₀ := (Finset.mem_erase.mp
    (Finset.mem_of_mem_erase hb₂R)).1
  have hb₃ne₀ : b₃ ≠ b₀ := (Finset.mem_erase.mp
    (Finset.mem_of_mem_erase hb₃R)).1
  have hb₂ne₁ : b₂ ≠ b₁ := (Finset.mem_erase.mp hb₂R).1
  have hb₃ne₁ : b₃ ≠ b₁ := (Finset.mem_erase.mp hb₃R).1
  have hb₀₂ : (S.support b₀ ∩ S.support b₂).card = 2 :=
    hb₀other b₂ (Finset.mem_of_mem_erase hb₂R) hb₂ne₁
  have hb₀₃ : (S.support b₀ ∩ S.support b₃).card = 2 :=
    hb₀other b₃ (Finset.mem_of_mem_erase hb₃R) hb₃ne₁
  obtain ⟨c₁, hc₁, hb₁c₁, hb₁other⟩ := hdeficient b₁ hb₁
  have hc₁eq : c₁ = b₀ := by
    by_contra hne
    have hb₁₀two := hb₁other b₀
      (Finset.mem_erase.mpr ⟨hb₀ne₁, hb₀⟩) (Ne.symm hne)
    have hb₁₀ : (S.support b₁ ∩ S.support b₀).card = 1 := by
      simpa [Finset.inter_comm] using hb₀₁
    omega
  have hb₁₂ : (S.support b₁ ∩ S.support b₂).card = 2 := by
    apply hb₁other b₂ (Finset.mem_erase.mpr ⟨hb₂ne₁, hb₂⟩)
    simpa [hc₁eq] using hb₂ne₀
  have hb₁₃ : (S.support b₁ ∩ S.support b₃).card = 2 := by
    apply hb₁other b₃ (Finset.mem_erase.mpr ⟨hb₃ne₁, hb₃⟩)
    simpa [hc₁eq] using hb₃ne₀
  have hb₂₃ : (S.support b₂ ∩ S.support b₃).card = 1 := by
    have hsum := hpairRow b₂ hb₂
    have hFerase : F.erase b₂ = {b₀, b₁, b₃} := by
      apply Finset.eq_of_subset_of_card_le
      · intro z hz
        have hzF := Finset.mem_of_mem_erase hz
        have hzne := (Finset.mem_erase.mp hz).1
        have hzRor : z = b₀ ∨ z = b₁ ∨ z ∈ R := by
          by_cases hz0 : z = b₀
          · exact Or.inl hz0
          by_cases hz1 : z = b₁
          · exact Or.inr (Or.inl hz1)
          · exact Or.inr (Or.inr (Finset.mem_erase.mpr ⟨hz1,
              Finset.mem_erase.mpr ⟨hz0, hzF⟩⟩))
        rcases hzRor with rfl | rfl | hzR
        · simp
        · simp
        · rw [hReq] at hzR
          simp only [Finset.mem_insert, Finset.mem_singleton] at hzR
          rcases hzR with rfl | rfl
          · exact (hzne rfl).elim
          · simp
      · rw [Finset.card_erase_of_mem hb₂, hFcard]
        simp [hb₀ne₁, hb₂ne₀, hb₂ne₁, hb₃ne₀, hb₃ne₁, hb₂ne₃]
    rw [hFerase] at hsum
    norm_num [Finset.inter_comm, hb₀₂, hb₁₂] at hsum ⊢
    exact hsum
  obtain ⟨x, hx⟩ := Finset.card_eq_one.mp hb₀₁
  obtain ⟨y, hy⟩ := Finset.card_eq_one.mp hb₂₃
  have hx₀ : x ∈ S.support b₀ := by rw [← Finset.mem_inter, hx]; simp
  have hx₁ : x ∈ S.support b₁ := by rw [← Finset.mem_inter, hx]; simp
  have hy₂ : y ∈ S.support b₂ := by rw [← Finset.mem_inter, hy]; simp
  have hy₃ : y ∈ S.support b₃ := by rw [← Finset.mem_inter, hy]; simp
  have hxnot₂ : x ∉ S.support b₂ := by
    intro hx₂
    have hsub : ({b₀, b₁, b₂} : Finset Block) ⊆
        F.filter fun b => x ∈ S.support b := by simp [hb₀, hb₁, hb₂,
          hx₀, hx₁, hx₂]
    have hle := Finset.card_le_card hsub
    have hdistinct : ({b₀, b₁, b₂} : Finset Block).card = 3 := by
      simp [hb₀ne₁, hb₂ne₀, hb₂ne₁]
    rw [hdistinct, hrow x] at hle
    omega
  have hxnot₃ : x ∉ S.support b₃ := by
    intro hx₃
    have hsub : ({b₀, b₁, b₃} : Finset Block) ⊆
        F.filter fun b => x ∈ S.support b := by simp [hb₀, hb₁, hb₃,
          hx₀, hx₁, hx₃]
    have hle := Finset.card_le_card hsub
    have hdistinct : ({b₀, b₁, b₃} : Finset Block).card = 3 := by
      simp [hb₀ne₁, hb₃ne₀, hb₃ne₁]
    rw [hdistinct, hrow x] at hle
    omega
  have hxy : x ≠ y := by
    intro h
    subst y
    exact hxnot₂ hy₂
  have hcommon : ∀ q ∈ S.blocksOfSize 4,
      x ∈ S.support q → y ∈ S.support q := by
    intro q hq hxq
    have hqne (b : Block) (hb : b ∈ F) : q ≠ b := by
      intro h
      have hqsize := S.mem_blocksOfSize.mp hq
      have hbsize := S.mem_blocksOfSize.mp hb
      rw [h] at hqsize
      omega
    have hinterQ (b : Block) (hb : b ∈ F) :
        (S.support q ∩ S.support b).card ≤ 2 := by
      have := S.distinct_block_inter_card_lt_three (hqne b hb)
      omega
    have hqsum :
        (∑ b ∈ F, (S.support q ∩ S.support b).card) = 8 := by
      rw [← sum_degreeIn_over_support S F q]
      change (∑ z ∈ S.support q, S.blockDegree 5 z) = 8
      calc
        _ = ∑ _z ∈ S.support q, 2 := by
          apply Finset.sum_congr rfl
          intro z hz
          exact hrow z
        _ = 8 := by simp [S.mem_blocksOfSize.mp hq]
    have hinter₂ : (S.support q ∩ S.support b₂).card = 2 := by
      have hrest :
          (∑ b ∈ F.erase b₂, (S.support q ∩ S.support b).card) ≤ 6 := by
        calc
          _ ≤ ∑ _b ∈ F.erase b₂, 2 := by
            apply Finset.sum_le_sum
            intro b hb
            exact hinterQ b (Finset.mem_of_mem_erase hb)
          _ = 6 := by simp [Finset.card_erase_of_mem hb₂, hFcard]
      have hsplit := Finset.sum_erase_add F
        (fun b => (S.support q ∩ S.support b).card) hb₂
      have hle := hinterQ b₂ hb₂
      omega
    have hinter₃ : (S.support q ∩ S.support b₃).card = 2 := by
      have hrest :
          (∑ b ∈ F.erase b₃, (S.support q ∩ S.support b).card) ≤ 6 := by
        calc
          _ ≤ ∑ _b ∈ F.erase b₃, 2 := by
            apply Finset.sum_le_sum
            intro b hb
            exact hinterQ b (Finset.mem_of_mem_erase hb)
          _ = 6 := by simp [Finset.card_erase_of_mem hb₃, hFcard]
      have hsplit := Finset.sum_erase_add F
        (fun b => (S.support q ∩ S.support b).card) hb₃
      have hle := hinterQ b₃ hb₃
      omega
    by_contra hynot
    let A := S.support q ∩ S.support b₂
    let B := S.support q ∩ S.support b₃
    have hABdisj : Disjoint A B := by
      rw [Finset.disjoint_left]
      intro z hzA hzB
      have hz₂ : z ∈ S.support b₂ := (Finset.mem_inter.mp hzA).2
      have hz₃ : z ∈ S.support b₃ := (Finset.mem_inter.mp hzB).2
      have : z = y := by
        have hz : z ∈ S.support b₂ ∩ S.support b₃ :=
          Finset.mem_inter.mpr ⟨hz₂, hz₃⟩
        rw [hy] at hz
        simpa using hz
      subst z
      exact hynot (Finset.mem_inter.mp hzA).1
    have hunionCard : (A ∪ B).card = 4 := by
      rw [Finset.card_union_of_disjoint hABdisj]
      simp [A, B, hinter₂, hinter₃]
    have hunionSub : A ∪ B ⊆ (S.support q).erase x := by
      intro z hz
      apply Finset.mem_erase.mpr
      constructor
      · intro hzx
        subst z
        rcases Finset.mem_union.mp hz with hzA | hzB
        · exact hxnot₂ (Finset.mem_inter.mp hzA).2
        · exact hxnot₃ (Finset.mem_inter.mp hzB).2
      · rcases Finset.mem_union.mp hz with hzA | hzB
        · exact (Finset.mem_inter.mp hzA).1
        · exact (Finset.mem_inter.mp hzB).1
    have hcardLe := Finset.card_le_card hunionSub
    rw [hunionCard, Finset.card_erase_of_mem hxq,
      S.mem_blocksOfSize.mp hq] at hcardLe
    omega
  have hfourCap := blockDegree_four_le_four_of_common_pair
    S hPoint x y hxy hcommon
  have hpairs := ten_pair_row S hPoint hcap x
  rw [hrow x] at hpairs
  rcases hd3 x with hx3 | hx3 <;> rw [hx3] at hpairs <;> omega

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
    push_neg at hnot
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
  have hrest : (∑ z ∈ A.erase {a, c}, f z) ≤ 8 := by
    calc
      _ ≤ ∑ _z ∈ A.erase {a, c}, 2 := by
        apply Finset.sum_le_sum
        intro z hz
        exact hle z (Finset.mem_of_mem_erase hz)
      _ = 8 := by
        rw [Finset.erase_eq_sdiff]
        have hacard : ({a, c} : Finset α).card = 2 := by simp [hca]
        have hsubset : ({a, c} : Finset α) ⊆ A := by simp [ha, hc]
        rw [Finset.card_sdiff_of_subset hsubset, hacard, hcard]
        simp
  have hsplitA := Finset.sum_erase_add A f ha
  have hcErase : c ∈ A.erase a := Finset.mem_erase.mpr ⟨hca, hc⟩
  have hsplitC := Finset.sum_erase_add (A.erase a) f hcErase
  have heraseEq : (A.erase a).erase c = A.erase {a, c} := by
    ext z
    simp [and_left_comm, and_assoc, and_comm]
  rw [heraseEq] at hsplitC
  have hcUpper := hle c hc
  have hcLower := hone c hc
  omega

theorem secondMoment_eleven_row_impossible
    {Point Block : Type*} [Fintype Point] [Fintype Block]
    [DecidableEq Point]
    (S : BlockSystem Point Block) (hPoint : Fintype.card Point = 10)
    (hcap : ∀ b : Block, 3 ≤ (S.support b).card →
      (S.support b).card ≤ 5)
    (hd3 : ∀ p : Point, S.blockDegree 3 p = 6 ∨
      S.blockDegree 3 p = 9)
    (hfive : S.blockCount 5 = 4)
    (hlow : ((Finset.univ : Finset Point).filter
      fun p => S.blockDegree 5 p = 1).card = 1)
    (hhigh : ((Finset.univ : Finset Point).filter
      fun p => S.blockDegree 5 p = 3).card = 1)
    (hprofile : ∀ p : Point, S.blockDegree 5 p = 1 ∨
      S.blockDegree 5 p = 2 ∨ S.blockDegree 5 p = 3)
    (hmoment : (∑ p : Point,
      Nat.choose (S.blockDegree 5 p) 2) = 11) : False := by
  classical
  let F := S.blocksOfSize 5
  have hFcard : F.card = 4 := hfive
  obtain ⟨U, hUeq⟩ := Finset.card_eq_one.mp hlow
  obtain ⟨T, hTeq⟩ := Finset.card_eq_one.mp hhigh
  have hUdegree : S.blockDegree 5 U = 1 := by
    have : U ∈ ((Finset.univ : Finset Point).filter
      fun p => S.blockDegree 5 p = 1) := by rw [hUeq]; simp
    exact (Finset.mem_filter.mp this).2
  have hTdegree : S.blockDegree 5 T = 3 := by
    have : T ∈ ((Finset.univ : Finset Point).filter
      fun p => S.blockDegree 5 p = 3) := by rw [hTeq]; simp
    exact (Finset.mem_filter.mp this).2
  have hTU : T ≠ U := by
    intro h
    rw [h] at hTdegree
    omega
  have hdegreeBaseline (p : Point) (hpU : p ≠ U) (hpT : p ≠ T) :
      S.blockDegree 5 p = 2 := by
    rcases hprofile p with h1 | h2 | h3
    · have hp : p ∈ ((Finset.univ : Finset Point).filter
          fun q => S.blockDegree 5 q = 1) := by simp [h1]
      rw [hUeq] at hp
      exact (hpU (by simpa using hp)).elim
    · exact h2
    · have hp : p ∈ ((Finset.univ : Finset Point).filter
          fun q => S.blockDegree 5 q = 3) := by simp [h3]
      rw [hTeq] at hp
      exact (hpT (by simpa using hp)).elim
  have hpairTotal :
      (∑ A ∈ F.powersetCard 2, (S.commonSupport A).card) = 11 := by
    rw [← S.binomial_degree_moment F 2]
    exact hmoment
  have hpairLe (A : Finset Block) (hA : A ∈ F.powersetCard 2) :
      (S.commonSupport A).card ≤ 2 :=
    S.commonSupport_card_le_two (Finset.mem_powersetCard.mp hA).2
  have hpairFamilyCard : (F.powersetCard 2).card = 6 := by
    simp [hFcard, Nat.choose]
  obtain ⟨D, hD, hDone, hDother⟩ := card_six_sum_eleven_le_two
    (F.powersetCard 2) (fun A => (S.commonSupport A).card)
    hpairFamilyCard hpairLe hpairTotal
  obtain ⟨d₀, d₁, hd₀ne₁, hDeq⟩ :=
    Finset.card_eq_two.mp (Finset.mem_powersetCard.mp hD).2
  have hDsub := (Finset.mem_powersetCard.mp hD).1
  have hd₀ : d₀ ∈ F := hDsub (by rw [hDeq]; simp)
  have hd₁ : d₁ ∈ F := hDsub (by rw [hDeq]; simp)
  let HU := F.filter fun b => U ∈ S.support b
  have hHUcard : HU.card = 1 := hUdegree
  obtain ⟨b₀, hb₀eq⟩ := Finset.card_eq_one.mp hHUcard
  have hb₀HU : b₀ ∈ HU := by rw [hb₀eq]; simp
  have hb₀ : b₀ ∈ F := (Finset.mem_filter.mp hb₀HU).1
  have hUb₀ : U ∈ S.support b₀ := (Finset.mem_filter.mp hb₀HU).2
  have hUnot (b : Block) (hb : b ∈ F) (hbne : b ≠ b₀) :
      U ∉ S.support b := by
    intro hUb
    have : b ∈ HU := Finset.mem_filter.mpr ⟨hb, hUb⟩
    rw [hb₀eq] at this
    exact hbne (by simpa using this)
  have hpairRow (b : Block) (hb : b ∈ F) :
      (∑ c ∈ F.erase b, (S.support b ∩ S.support c).card) =
        if b ∈ D then 5 else 6 := by
    have hcardErase : (F.erase b).card = 3 := by
      rw [Finset.card_erase_of_mem hb, hFcard]
    by_cases hbD : b ∈ D
    · obtain ⟨c₀, hc₀D, hc₀ne⟩ :
          ∃ c₀ ∈ D, c₀ ≠ b := by
        rw [hDeq] at hbD ⊢
        rcases hbD with rfl | rfl
        · exact ⟨d₁, by simp, hd₀ne₁.symm⟩
        · exact ⟨d₀, by simp, hd₀ne₁⟩
      have hc₀F : c₀ ∈ F := hDsub hc₀D
      have hpairD : ({b, c₀} : Finset Block) = D := by
        apply Finset.eq_of_subset_of_card_le
        · intro z hz
          simp only [Finset.mem_insert, Finset.mem_singleton] at hz
          rcases hz with rfl | rfl <;> assumption
        · simp [Finset.card_eq_two.mp
            (Finset.mem_powersetCard.mp hD).2, hc₀ne]
      have hone : (S.support b ∩ S.support c₀).card = 1 := by
        rw [← S.commonSupport_pair, hpairD]
        exact hDone
      calc
        (∑ c ∈ F.erase b, (S.support b ∩ S.support c).card) =
            1 + ∑ c ∈ (F.erase b).erase c₀,
              (S.support b ∩ S.support c).card := by
          have hc₀erase : c₀ ∈ F.erase b :=
            Finset.mem_erase.mpr ⟨hc₀ne, hc₀F⟩
          have hsplit := Finset.sum_erase_add (F.erase b)
            (fun c => (S.support b ∩ S.support c).card) hc₀erase
          omega
        _ = 1 + ∑ _c ∈ (F.erase b).erase c₀, 2 := by
          congr 1
          apply Finset.sum_congr rfl
          intro c hc
          have hcF := Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hc)
          have hcb := (Finset.mem_erase.mp (Finset.mem_of_mem_erase hc)).1
          have hcc₀ := (Finset.mem_erase.mp hc).1
          have hpairMem : ({b, c} : Finset Block) ∈ F.powersetCard 2 := by
            apply Finset.mem_powersetCard.mpr
            exact ⟨by simp [hb, hcF], by simp [hcb]⟩
          have hneD : ({b, c} : Finset Block) ≠ D := by
            intro heq
            have : c = c₀ := by
              have hcD : c ∈ D := by rw [← heq]; simp
              rw [← hpairD] at hcD
              simpa [hcb] using hcD
            exact hcc₀ this
          have := hDother {b, c} hpairMem hneD
          simpa [S.commonSupport_pair] using this
        _ = 5 := by simp [Finset.card_erase_of_mem,
            Finset.card_erase_of_mem, hcardErase,
            (show c₀ ∈ F.erase b from Finset.mem_erase.mpr ⟨hc₀ne, hc₀F⟩)]
        _ = (if b ∈ D then 5 else 6) := by simp [hbD]
    · calc
        (∑ c ∈ F.erase b, (S.support b ∩ S.support c).card) =
            ∑ _c ∈ F.erase b, 2 := by
          apply Finset.sum_congr rfl
          intro c hc
          have hcF := Finset.mem_of_mem_erase hc
          have hcb := (Finset.mem_erase.mp hc).1
          have hpairMem : ({b, c} : Finset Block) ∈ F.powersetCard 2 := by
            exact Finset.mem_powersetCard.mpr
              ⟨by simp [hb, hcF], by simp [hcb]⟩
          have hneD : ({b, c} : Finset Block) ≠ D := by
            intro heq
            apply hbD
            rw [← heq]
            simp
          have := hDother {b, c} hpairMem hneD
          simpa [S.commonSupport_pair] using this
        _ = 6 := by simp [hcardErase]
        _ = (if b ∈ D then 5 else 6) := by simp [hbD]
  have hsumSupport (b : Block) (hb : b ∈ F) :
      (∑ p ∈ S.support b, S.blockDegree 5 p) =
        5 + (if b ∈ D then 5 else 6) := by
    rw [sum_degreeIn_over_support S F b]
    change (∑ c ∈ F, (S.support b ∩ S.support c).card) = _
    have hsplit := Finset.sum_erase_add F
      (fun c => (S.support b ∩ S.support c).card) hb
    have hself : (S.support b ∩ S.support b).card = 5 := by
      simp [S.mem_blocksOfSize.mp hb]
    rw [hpairRow b hb] at hsplit
    omega
  have hTb₀ : T ∈ S.support b₀ := by
    by_contra hTnot
    have hpoint (p : Point) (hp : p ∈ S.support b₀) :
        S.blockDegree 5 p = if p = U then 1 else 2 := by
      by_cases hpU : p = U
      · simp [hpU, hUdegree]
      · simp [hpU, hdegreeBaseline p hpU (fun hpT => hTnot (hpT ▸ hp))]
    have hsum9 : (∑ p ∈ S.support b₀, S.blockDegree 5 p) = 9 := by
      calc
        _ = ∑ p ∈ S.support b₀, if p = U then 1 else 2 := by
          apply Finset.sum_congr rfl
          intro p hp
          exact hpoint p hp
        _ = 9 := by
          rw [Finset.sum_ite_irrel, Finset.filter_eq'] <;>
            simp [hUb₀, S.mem_blocksOfSize.mp hb₀]
    have := hsumSupport b₀ hb₀
    omega
  have hsumB₀ : (∑ p ∈ S.support b₀, S.blockDegree 5 p) = 10 := by
    have hpoint (p : Point) (hp : p ∈ S.support b₀) :
        S.blockDegree 5 p =
          if p = U then 1 else if p = T then 3 else 2 := by
      by_cases hpU : p = U
      · simp [hpU, hUdegree, hTU]
      by_cases hpT : p = T
      · simp [hpU, hpT, hTdegree]
      · simp [hpU, hpT, hdegreeBaseline p hpU hpT]
    calc
      _ = ∑ p ∈ S.support b₀,
          (if p = U then 1 else if p = T then 3 else 2) := by
        apply Finset.sum_congr rfl
        intro p hp
        exact hpoint p hp
      _ = 10 := by
        have hUneT : U ≠ T := hTU.symm
        have hcard := S.mem_blocksOfSize.mp hb₀
        simp only [Finset.sum_ite_irrel]
        simp [hUb₀, hTb₀, hUneT, hcard]
  have hb₀D : b₀ ∈ D := by
    have := hsumSupport b₀ hb₀
    by_cases h : b₀ ∈ D <;> simp [h] at this <;> omega
  obtain ⟨b₃, hb₃D, hb₃ne₀⟩ : ∃ b₃ ∈ D, b₃ ≠ b₀ := by
    rw [hDeq] at hb₀D ⊢
    rcases hb₀D with rfl | rfl
    · exact ⟨d₁, by simp, hd₀ne₁.symm⟩
    · exact ⟨d₀, by simp, hd₀ne₁⟩
  have hb₃ : b₃ ∈ F := hDsub hb₃D
  have hUb₃ : U ∉ S.support b₃ := hUnot b₃ hb₃ hb₃ne₀
  have hTb₃ : T ∉ S.support b₃ := by
    intro hT
    have hpoint (p : Point) (hp : p ∈ S.support b₃) :
        S.blockDegree 5 p = if p = T then 3 else 2 := by
      by_cases hpT : p = T
      · simp [hpT, hTdegree]
      · simp [hpT, hdegreeBaseline p (fun hpU => hUb₃ (hpU ▸ hp)) hpT]
    have hsum11 : (∑ p ∈ S.support b₃, S.blockDegree 5 p) = 11 := by
      calc
        _ = ∑ p ∈ S.support b₃, if p = T then 3 else 2 := by
          apply Finset.sum_congr rfl
          intro p hp
          exact hpoint p hp
        _ = 11 := by
          simp [hT, S.mem_blocksOfSize.mp hb₃]
    have := hsumSupport b₃ hb₃
    simp [hb₃D] at this
    omega
  let R := (F.erase b₀).erase b₃
  have hRcard : R.card = 2 := by
    have hb₃erase : b₃ ∈ F.erase b₀ :=
      Finset.mem_erase.mpr ⟨hb₃ne₀, hb₃⟩
    rw [Finset.card_erase_of_mem hb₃erase,
      Finset.card_erase_of_mem hb₀, hFcard]
  obtain ⟨b₁, b₂, hb₁ne₂, hReq⟩ := Finset.card_eq_two.mp hRcard
  have hb₁R : b₁ ∈ R := by rw [hReq]; simp
  have hb₂R : b₂ ∈ R := by rw [hReq]; simp
  have hb₁ : b₁ ∈ F := Finset.mem_of_mem_erase
    (Finset.mem_of_mem_erase hb₁R)
  have hb₂ : b₂ ∈ F := Finset.mem_of_mem_erase
    (Finset.mem_of_mem_erase hb₂R)
  have hb₁ne₀ : b₁ ≠ b₀ := (Finset.mem_erase.mp
    (Finset.mem_of_mem_erase hb₁R)).1
  have hb₂ne₀ : b₂ ≠ b₀ := (Finset.mem_erase.mp
    (Finset.mem_of_mem_erase hb₂R)).1
  have hb₁ne₃ : b₁ ≠ b₃ := (Finset.mem_erase.mp hb₁R).1
  have hb₂ne₃ : b₂ ≠ b₃ := (Finset.mem_erase.mp hb₂R).1
  have hb₁notD : b₁ ∉ D := by
    intro hbD
    rw [hDeq] at hb₀D hb₃D hbD
    rcases hbD with rfl | rfl <;>
      simp_all
  have hb₂notD : b₂ ∉ D := by
    intro hbD
    rw [hDeq] at hb₀D hb₃D hbD
    rcases hbD with rfl | rfl <;>
      simp_all
  have hTb (b : Block) (hb : b ∈ F) (hbne₀ : b ≠ b₀)
      (hbnotD : b ∉ D) : T ∈ S.support b := by
    have hUb : U ∉ S.support b := hUnot b hb hbne₀
    by_contra hTnot
    have hpoint (p : Point) (hp : p ∈ S.support b) :
        S.blockDegree 5 p = 2 :=
      hdegreeBaseline p (fun hpU => hUb (hpU ▸ hp))
        (fun hpT => hTnot (hpT ▸ hp))
    have hsum10 : (∑ p ∈ S.support b, S.blockDegree 5 p) = 10 := by
      calc
        _ = ∑ _p ∈ S.support b, 2 := by
          apply Finset.sum_congr rfl
          intro p hp
          exact hpoint p hp
        _ = 10 := by simp [S.mem_blocksOfSize.mp hb]
    have := hsumSupport b hb
    simp [hbnotD] at this
    omega
  have hTb₁ : T ∈ S.support b₁ := hTb b₁ hb₁ hb₁ne₀ hb₁notD
  have hTb₂ : T ∈ S.support b₂ := hTb b₂ hb₂ hb₂ne₀ hb₂notD
  have hinter₁₃ : (S.support b₁ ∩ S.support b₃).card = 2 := by
    have hpairMem : ({b₁, b₃} : Finset Block) ∈ F.powersetCard 2 := by
      exact Finset.mem_powersetCard.mpr
        ⟨by simp [hb₁, hb₃], by simp [hb₁ne₃]⟩
    have hneD : ({b₁, b₃} : Finset Block) ≠ D := by
      intro h
      apply hb₁notD
      rw [← h]
      simp
    have := hDother {b₁, b₃} hpairMem hneD
    simpa [S.commonSupport_pair] using this
  have hinter₂₃ : (S.support b₂ ∩ S.support b₃).card = 2 := by
    have hpairMem : ({b₂, b₃} : Finset Block) ∈ F.powersetCard 2 := by
      exact Finset.mem_powersetCard.mpr
        ⟨by simp [hb₂, hb₃], by simp [hb₂ne₃]⟩
    have hneD : ({b₂, b₃} : Finset Block) ≠ D := by
      intro h
      apply hb₂notD
      rw [← h]
      simp
    have := hDother {b₂, b₃} hpairMem hneD
    simpa [S.commonSupport_pair] using this
  let X := S.support b₁ ∩ S.support b₃
  let Y := S.support b₂ ∩ S.support b₃
  have hXcard : X.card = 2 := hinter₁₃
  have hYcard : Y.card = 2 := hinter₂₃
  let H := (S.blocksOfSize 4).filter fun q => T ∈ S.support q
  have hcommon (q : Block) (hq : q ∈ H) : U ∈ S.support q := by
    have hq' := Finset.mem_filter.mp hq
    by_contra hUnotq
    have hsumLower : 9 ≤ ∑ p ∈ S.support q, S.blockDegree 5 p := by
      have hrest : 6 ≤ ∑ p ∈ (S.support q).erase T,
          S.blockDegree 5 p := by
        calc
          6 = ∑ _p ∈ (S.support q).erase T, 2 := by
            simp [Finset.card_erase_of_mem hq'.2,
              S.mem_blocksOfSize.mp hq'.1]
          _ ≤ _ := by
            apply Finset.sum_le_sum
            intro p hp
            have hpneT := (Finset.mem_erase.mp hp).1
            have hpneU : p ≠ U := by
              intro h; subst p
              exact hUnotq (Finset.mem_of_mem_erase hp)
            rcases hprofile p with h1 | h2 | h3
            · have hpLow : p ∈ ((Finset.univ : Finset Point).filter
                  fun z => S.blockDegree 5 z = 1) := by simp [h1]
              rw [hUeq] at hpLow
              exact (hpneU (by simpa using hpLow)).elim
            · omega
            · omega
      have hsplit := Finset.sum_erase_add (S.support q)
        (fun p => S.blockDegree 5 p) hq'.2
      rw [hTdegree] at hsplit
      omega
    have hsumUpper :
        (∑ b ∈ F, (S.support q ∩ S.support b).card) ≤ 8 := by
      calc
        _ ≤ ∑ _b ∈ F, 2 := by
          apply Finset.sum_le_sum
          intro b hb
          have hqb : q ≠ b := by
            intro h
            have hqsize := S.mem_blocksOfSize.mp hq'.1
            have hbsize := S.mem_blocksOfSize.mp hb
            rw [h] at hqsize
            omega
          have hinter := S.distinct_block_inter_card_lt_three hqb
          omega
        _ = 8 := by simp [hFcard]
    have hfubini := sum_degreeIn_over_support S F q
    change (∑ p ∈ S.support q, S.blockDegree 5 p) = _ at hfubini
    omega
  have hawayXY (q : Block) (hq : q ∈ H) :
      ((S.support q \ {T, U}) ∩ X).card = 1 ∧
      ((S.support q \ {T, U}) ∩ Y).card = 1 := by
    have hq' := Finset.mem_filter.mp hq
    have hUq := hcommon q hq
    have hqne (b : Block) (hb : b ∈ F) : q ≠ b := by
      intro h
      have hqsize := S.mem_blocksOfSize.mp hq'.1
      have hbsize := S.mem_blocksOfSize.mp hb
      rw [h] at hqsize
      omega
    have hinterCap (b : Block) (hb : b ∈ F) :
        (S.support q ∩ S.support b).card ≤ 2 := by
      have := S.distinct_block_inter_card_lt_three (hqne b hb)
      omega
    have hawayCard : (S.support q \ {T, U}).card = 2 := by
      have hsub : ({T, U} : Finset Point) ⊆ S.support q := by
        simp [hq'.2, hUq]
      rw [Finset.card_sdiff_of_subset hsub,
        S.mem_blocksOfSize.mp hq'.1]
      simp [hTU]
    have hnotB₀ (p : Point) (hp : p ∈ S.support q \ {T, U}) :
        p ∉ S.support b₀ := by
      intro hpb₀
      have hsub : ({T, U, p} : Finset Point) ⊆
          S.support q ∩ S.support b₀ := by
        have hpq := (Finset.mem_sdiff.mp hp).1
        have hpne := (Finset.mem_sdiff.mp hp).2
        have hpneT : p ≠ T := by intro h; subst p; exact hpne (by simp)
        have hpneU : p ≠ U := by intro h; subst p; exact hpne (by simp)
        simp [hq'.2, hUq, hTb₀, hUb₀, hpq, hpb₀,
          hTU, hpneT, hpneU]
      have hc := Finset.card_le_card hsub
      have hinter := hinterCap b₀ hb₀
      have hthree : ({T, U, p} : Finset Point).card = 3 := by
        have hpne := (Finset.mem_sdiff.mp hp).2
        simp only [Finset.mem_insert, Finset.mem_singleton,
          not_or] at hpne
        simp [hTU, hpne.1, hpne.2]
      omega
    have hlabels (p : Point) (hp : p ∈ S.support q \ {T, U}) :
        p ∈ X ∪ Y := by
      have hpq := (Finset.mem_sdiff.mp hp).1
      have hpne := (Finset.mem_sdiff.mp hp).2
      have hpneT : p ≠ T := by intro h; subst p; exact hpne (by simp)
      have hpneU : p ≠ U := by intro h; subst p; exact hpne (by simp)
      have hpdeg := hdegreeBaseline p hpneU hpneT
      have hpnot₀ := hnotB₀ p hp
      have hpIn : p ∈ S.support b₁ ∨ p ∈ S.support b₂ ∨
          p ∈ S.support b₃ := by
        by_contra hnone
        push_neg at hnone
        have hfilterEmpty :
            (F.filter fun b => p ∈ S.support b) = ∅ := by
          apply Finset.eq_empty_iff_forall_notMem.mpr
          intro b hb
          have hbF := (Finset.mem_filter.mp hb).1
          have hcases : b = b₀ ∨ b = b₁ ∨ b = b₂ ∨ b = b₃ := by
            by_cases h0 : b = b₀
            · exact Or.inl h0
            have hbRor : b = b₃ ∨ b ∈ R := by
              by_cases h3 : b = b₃
              · exact Or.inl h3
              · exact Or.inr (Finset.mem_erase.mpr ⟨h3,
                  Finset.mem_erase.mpr ⟨h0, hbF⟩⟩)
            rcases hbRor with h3 | hbR
            · exact Or.inr (Or.inr (Or.inr h3))
            · rw [hReq] at hbR
              simp only [Finset.mem_insert, Finset.mem_singleton] at hbR
              rcases hbR with rfl | rfl
              · exact Or.inr (Or.inl rfl)
              · exact Or.inr (Or.inr (Or.inl rfl))
          rcases hcases with rfl | rfl | rfl | rfl
          · exact hpnot₀ (Finset.mem_filter.mp hb).2
          · exact hnone.1 (Finset.mem_filter.mp hb).2
          · exact hnone.2.1 (Finset.mem_filter.mp hb).2
          · exact hnone.2.2 (Finset.mem_filter.mp hb).2
        have : S.blockDegree 5 p = 0 := by
          change (F.filter fun b => p ∈ S.support b).card = 0
          rw [hfilterEmpty]
          simp
        omega
      have hp₁cap : ¬(p ∈ S.support b₁ ∧ p ∈ S.support b₂) := by
        rintro ⟨hp₁, hp₂⟩
        have hsub : ({T, p} : Finset Point) ⊆
            S.support q ∩ S.support b₁ := by simp [hq'.2, hTb₁, hpq, hp₁]
        have hsub' : ({T, p} : Finset Point) ⊆
            S.support q ∩ S.support b₂ := by simp [hq'.2, hTb₂, hpq, hp₂]
        have hother := (S.support q \ {T, U}).erase p
        have hotherCard : hother.card = 1 := by
          have hpAway : p ∈ S.support q \ {T, U} := hp
          rw [Finset.card_erase_of_mem hpAway, hawayCard]
        obtain ⟨z, hz⟩ := Finset.card_eq_one.mp hotherCard
        have hzAway : z ∈ S.support q \ {T, U} := by
          have : z ∈ hother := by rw [hz]; simp
          exact Finset.mem_of_mem_erase this
        have hznot₀ := hnotB₀ z hzAway
        have hzlabels := hlabels z hzAway
        rcases Finset.mem_union.mp hzlabels with hzX | hzY
        · have hz₁ : z ∈ S.support b₁ := (Finset.mem_inter.mp hzX).1
          have hpneZ : p ≠ z := by
            intro h; subst z
            have : p ∈ hother := by rw [hz]; simp
            exact (Finset.mem_erase.mp this).1 rfl
          have hthree : ({T, p, z} : Finset Point) ⊆
              S.support q ∩ S.support b₁ := by
            simp [hq'.2, hTb₁, hpq, hp₁,
              (Finset.mem_sdiff.mp hzAway).1, hz₁]
          have hc := Finset.card_le_card hthree
          have hcap₁ := hinterCap b₁ hb₁
          have hpneT := by
            intro h; subst p
            exact (Finset.mem_sdiff.mp hp).2 (by simp)
          have hzNeT := by
            intro h; subst z
            exact (Finset.mem_sdiff.mp hzAway).2 (by simp)
          have : ({T, p, z} : Finset Point).card = 3 := by
            simp [hpneT, hzNeT, hpneZ]
          omega
        · have hz₂ : z ∈ S.support b₂ := (Finset.mem_inter.mp hzY).1
          have hpneZ : p ≠ z := by
            intro h; subst z
            have : p ∈ hother := by rw [hz]; simp
            exact (Finset.mem_erase.mp this).1 rfl
          have hthree : ({T, p, z} : Finset Point) ⊆
              S.support q ∩ S.support b₂ := by
            simp [hq'.2, hTb₂, hpq, hp₂,
              (Finset.mem_sdiff.mp hzAway).1, hz₂]
          have hc := Finset.card_le_card hthree
          have hcap₂ := hinterCap b₂ hb₂
          have hpneT := by
            intro h; subst p
            exact (Finset.mem_sdiff.mp hp).2 (by simp)
          have hzNeT := by
            intro h; subst z
            exact (Finset.mem_sdiff.mp hzAway).2 (by simp)
          have : ({T, p, z} : Finset Point).card = 3 := by
            simp [hpneT, hzNeT, hpneZ]
          omega
      rcases hpIn with hp₁ | hp₂ | hp₃
      · have hpnot₂ : p ∉ S.support b₂ := fun hp₂ => hp₁cap ⟨hp₁, hp₂⟩
        have hp₃ : p ∈ S.support b₃ := by
          have hsub : ({b₁} : Finset Block) ⊆
              F.filter fun b => p ∈ S.support b := by simp [hb₁, hp₁]
          have hneed := hpdeg
          by_contra hpnot₃
          have hfilter : F.filter (fun b => p ∈ S.support b) = {b₁} := by
            ext b
            by_cases h : b = b₀ <;> by_cases h' : b = b₁ <;>
              by_cases h'' : b = b₂ <;> by_cases h''' : b = b₃ <;>
              simp_all [hReq, R]
          change (F.filter fun b => p ∈ S.support b).card = 2 at hpdeg
          rw [hfilter] at hpdeg
          simp at hpdeg
        exact Finset.mem_union.mpr (Or.inl (Finset.mem_inter.mpr ⟨hp₁, hp₃⟩))
      · exact (hp₁cap ⟨hp₂.1, hp₂.2.1⟩).elim
      · have hpnot₁ : p ∉ S.support b₁ := by
          intro hp₁
          have hp₂mem : p ∈ S.support b₂ := by
            rcases hpIn with _ | hp₂ | hp₃only
            · contradiction
            · exact hp₂.1
            · contradiction
          exact hp₁cap ⟨hp₁, hp₂mem⟩
        have hp₂mem : p ∈ S.support b₂ := by
          have hneed := hpdeg
          by_contra hpnot₂
          have hfilter : F.filter (fun b => p ∈ S.support b) = {b₃} := by
            ext b
            by_cases h : b = b₀ <;> by_cases h' : b = b₁ <;>
              by_cases h'' : b = b₂ <;> by_cases h''' : b = b₃ <;>
              simp_all [hReq, R]
          change (F.filter fun b => p ∈ S.support b).card = 2 at hpdeg
          rw [hfilter] at hpdeg
          simp at hpdeg
        exact Finset.mem_union.mpr
          (Or.inr (Finset.mem_inter.mpr ⟨hp₂mem, hp₃⟩))
    have hawaySub : S.support q \ {T, U} ⊆ X ∪ Y := hlabels
    have hunionCard : (X ∪ Y).card ≤ 4 := by
      calc
        _ ≤ X.card + Y.card := Finset.card_union_le
        _ = 4 := by rw [hXcard, hYcard]
    have hparts :
        ((S.support q \ {T, U}) ∩ X).card +
          ((S.support q \ {T, U}) ∩ Y).card ≥ 2 := by
      have hcover : (S.support q \ {T, U}) =
          ((S.support q \ {T, U}) ∩ X) ∪
            ((S.support q \ {T, U}) ∩ Y) := by
        ext p
        simp only [Finset.mem_union, Finset.mem_inter]
        constructor
        · intro hp
          rcases Finset.mem_union.mp (hawaySub hp) with hpX | hpY
          · exact Or.inl ⟨hp, hpX⟩
          · exact Or.inr ⟨hp, hpY⟩
        · rintro (hp | hp) <;> exact hp.1
      rw [hcover, Finset.card_union] at hawayCard
      omega
    have hXle : ((S.support q \ {T, U}) ∩ X).card ≤ 1 := by
      by_contra hnot
      have htwo : 2 ≤ ((S.support q \ {T, U}) ∩ X).card := by omega
      obtain ⟨A, hAsub, hAcard⟩ := Finset.exists_subset_card_eq htwo
      have hthree : insert T A ⊆ S.support q ∩ S.support b₁ := by
        intro p hp
        simp only [Finset.mem_insert] at hp
        rcases hp with rfl | hp
        · exact Finset.mem_inter.mpr ⟨hq'.2, hTb₁⟩
        · have hp' := hAsub hp
          exact Finset.mem_inter.mpr ⟨
            (Finset.mem_sdiff.mp (Finset.mem_inter.mp hp').1).1,
            (Finset.mem_inter.mp (Finset.mem_inter.mp hp').2).1⟩
      have hTnotA : T ∉ A := by
        intro h
        have h' := hAsub h
        exact (Finset.mem_sdiff.mp (Finset.mem_inter.mp h').1).2 (by simp)
      have hcard3 : (insert T A).card = 3 := by simp [hTnotA, hAcard]
      have hc := Finset.card_le_card hthree
      have hcap₁ := hinterCap b₁ hb₁
      omega
    have hYle : ((S.support q \ {T, U}) ∩ Y).card ≤ 1 := by
      by_contra hnot
      have htwo : 2 ≤ ((S.support q \ {T, U}) ∩ Y).card := by omega
      obtain ⟨A, hAsub, hAcard⟩ := Finset.exists_subset_card_eq htwo
      have hthree : insert T A ⊆ S.support q ∩ S.support b₂ := by
        intro p hp
        simp only [Finset.mem_insert] at hp
        rcases hp with rfl | hp
        · exact Finset.mem_inter.mpr ⟨hq'.2, hTb₂⟩
        · have hp' := hAsub hp
          exact Finset.mem_inter.mpr ⟨
            (Finset.mem_sdiff.mp (Finset.mem_inter.mp hp').1).1,
            (Finset.mem_inter.mp (Finset.mem_inter.mp hp').2).1⟩
      have hTnotA : T ∉ A := by
        intro h
        have h' := hAsub h
        exact (Finset.mem_sdiff.mp (Finset.mem_inter.mp h').1).2 (by simp)
      have hcard3 : (insert T A).card = 3 := by simp [hTnotA, hAcard]
      have hc := Finset.card_le_card hthree
      have hcap₂ := hinterCap b₂ hb₂
      omega
    omega
  let Pick : {q : Block // q ∈ H} → {p : Point // p ∈ X} := fun q => by
    have hcard := (hawayXY q.1 q.2).1
    exact ⟨Classical.choose (Finset.card_pos.mp (by omega :
      0 < ((S.support q.1 \ {T, U}) ∩ X).card)),
      (Finset.mem_inter.mp (Classical.choose_spec
        (Finset.card_pos.mp (by omega :
          0 < ((S.support q.1 \ {T, U}) ∩ X).card)))).2⟩
  have hPickMem (q : {q : Block // q ∈ H}) :
      Pick q ∈ (S.support q.1 \ {T, U}) ∩ X := by
    exact Classical.choose_spec (Finset.card_pos.mp
      (by have := (hawayXY q.1 q.2).1; omega :
        0 < ((S.support q.1 \ {T, U}) ∩ X).card))
  have hPickInj : Function.Injective Pick := by
    intro q r hqr
    apply Subtype.ext
    apply support_injOn_blocksOfSize S 4 (by omega)
      (Finset.mem_filter.mp q.2).1 (Finset.mem_filter.mp r.2).1
    by_contra hsupp
    have hqT := (Finset.mem_filter.mp q.2).2
    have hrT := (Finset.mem_filter.mp r.2).2
    have hqU := hcommon q.1 q.2
    have hrU := hcommon r.1 r.2
    have hpq := (Finset.mem_sdiff.mp (Finset.mem_inter.mp
      (hPickMem q)).1).1
    have hpr := (Finset.mem_sdiff.mp (Finset.mem_inter.mp
      (hPickMem r)).1).1
    have hpne := (Finset.mem_sdiff.mp (Finset.mem_inter.mp
      (hPickMem q)).1).2
    have hpneT : (Pick q : Point) ≠ T := by
      intro h; exact hpne (by simp [h])
    have hpneU : (Pick q : Point) ≠ U := by
      intro h; exact hpne (by simp [h])
    have hsub : ({T, U, (Pick q : Point)} : Finset Point) ⊆
        S.support q.1 ∩ S.support r.1 := by
      simp [hqT, hrT, hqU, hrU, hpq, hpr, hqr]
    have hcard3 : ({T, U, (Pick q : Point)} : Finset Point).card = 3 := by
      simp [hTU, hpneT, hpneU]
    have hcardLe := Finset.card_le_card hsub
    have hinter := S.distinct_block_inter_card_lt_three (by
      intro h; apply hsupp; exact congrArg S.support h)
    omega
  have hcardH : H.card ≤ 2 := by
    have hle := Fintype.card_le_of_injective Pick hPickInj
    simpa [H, hXcard] using hle
  have hpairs := ten_pair_row S hPoint hcap T
  change H.card = S.blockDegree 4 T at hcardH
  rw [hTdegree] at hpairs
  rcases hd3 T with hT3 | hT3 <;> rw [hT3] at hpairs <;> omega

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
          rcases hprofile x hx with h1 | h2 | h3 <;> simp [h1, h2, h3]
    _ = 2 * A.card + (A.filter fun x => d x = 3).card := by
          rw [Finset.sum_add_distrib]
          simp [Finset.card_eq_sum_ones, Finset.sum_filter, Nat.mul_comm]

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
    exact Finset.mem_powersetCard.mpr
      ⟨by simp [hb, hc], by simp [hbc]⟩
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
  have hslack := Finset.sum_congr
    (s := (Finset.univ : Finset Point)) rfl
    (fun p _hp => hslackPoint p)
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
  have hbalance := Finset.sum_congr
    (s := (Finset.univ : Finset Point)) rfl
    (fun p _hp => hbalancePoint p)
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, ← Finset.mul_sum] at hbalance
  rw [hsum, hPoint, hzero, hone, hthree, hfour] at hbalance
  have hmLower : 10 ≤ ∑ p : Point, Nat.choose (d p) 2 := by omega
  have hn₀pos {p : Point} (hp : d p = 0) : 1 ≤ n₀ := by
    apply Finset.card_pos.mpr
    exact ⟨p, by simp [n₀, hp]⟩
  have hn₁pos {p : Point} (hp : d p = 1) : 1 ≤ n₁ := by
    apply Finset.card_pos.mpr
    exact ⟨p, by simp [n₁, hp]⟩
  have hn₃pos {p : Point} (hp : d p = 3) : 1 ≤ n₃ := by
    apply Finset.card_pos.mpr
    exact ⟨p, by simp [n₃, hp]⟩
  have hn₄pos {p : Point} (hp : d p = 4) : 1 ≤ n₄ := by
    apply Finset.card_pos.mpr
    exact ⟨p, by simp [n₄, hp]⟩
  interval_cases hm : (∑ p : Point, Nat.choose (d p) 2)
  · left
    constructor
    · exact hm
    · intro p
      have hp := hdle p
      interval_cases hdp : d p
      all_goals try { exact (by omega : False).elim }
      · exact hdp
      all_goals
        first
        | have := hn₀pos hdp; omega
        | have := hn₁pos hdp; omega
        | have := hn₃pos hdp; omega
        | have := hn₄pos hdp; omega
  · right; left
    have hn₀ : n₀ = 0 := by omega
    have hn₁ : n₁ = 1 := by omega
    have hn₃ : n₃ = 1 := by omega
    have hn₄ : n₄ = 0 := by omega
    refine ⟨hm, ?_, ?_, ?_⟩
    · simpa [n₁] using hn₁
    · simpa [n₃] using hn₃
    · intro p
      have hp := hdle p
      interval_cases hdp : d p
      · have := hn₀pos hdp; omega
      · exact Or.inl hdp
      · exact Or.inr (Or.inl hdp)
      · exact Or.inr (Or.inr hdp)
      · have := hn₄pos hdp; omega
  · right; right
    have hn₀ : n₀ = 0 := by omega
    have hn₁ : n₁ = 2 := by omega
    have hn₃ : n₃ = 2 := by omega
    have hn₄ : n₄ = 0 := by omega
    refine ⟨hm, ?_, ?_, ?_⟩
    · simpa [n₁] using hn₁
    · simpa [n₃] using hn₃
    · intro p
      have hp := hdle p
      interval_cases hdp : d p
      · have := hn₀pos hdp; omega
      · exact Or.inl hdp
      · exact Or.inr (Or.inl hdp)
      · exact Or.inr (Or.inr hdp)
      · have := hn₄pos hdp; omega


end FourPentagonRows

end Erdos506.Finite

