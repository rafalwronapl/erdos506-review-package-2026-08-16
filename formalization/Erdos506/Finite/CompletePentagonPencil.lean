import Erdos506.Block.Moments
import Mathlib.Tactic

/-!
# Complete five-block pencils on eleven points

This file proves the finite local fact behind the eleven-point, maximum-block
five argument.  Unique ownership of triples alone implies that at most five
five-blocks pass through a point.  In the equality case their traces away from
the pivot all have degree two, which excludes every four-block through that
pivot.

The final theorem combines this dichotomy with the local pair row.  No
geometric principle is used.
-/

namespace Erdos506.Finite

open Erdos506.Block
open Erdos506.Block.BlockSystem
open scoped BigOperators

private theorem degreeIn_le_card
    {Point Block : Type*} [Fintype Point] [Fintype Block]
    [DecidableEq Point]
    (S : BlockSystem Point Block) (F : Finset Block) (p : Point) :
    S.degreeIn F p ≤ F.card := by
  classical
  exact Finset.card_filter_le _ _

private theorem two_mul_choose_two (n : Nat) :
    2 * Nat.choose n 2 = n * (n - 1) := by
  have h := Nat.choose_succ_right_eq n 1
  simpa [Nat.choose_one_right, Nat.mul_comm] using h

/-- The elementary pointwise inequality used in both moment arguments. -/
private theorem twice_le_choose_add_three (n : Nat) :
    2 * n ≤ Nat.choose n 2 + 3 := by
  by_cases hn : n ≤ 3
  · interval_cases n <;> norm_num [Nat.choose]
  · have hn4 : 4 ≤ n := by omega
    have hsub : n - 1 + 1 = n := by omega
    have hchoose := two_mul_choose_two n
    nlinarith

/-- Incidence Fubini restricted to an arbitrary point set. -/
private theorem sum_degreeIn_over
    {Point Block : Type*} [Fintype Point] [Fintype Block]
    [DecidableEq Point]
    (S : BlockSystem Point Block) (F : Finset Block) (D : Finset Point) :
    (∑ x ∈ D, S.degreeIn F x) =
      ∑ b ∈ F, (D ∩ S.support b).card := by
  classical
  simp only [BlockSystem.degreeIn, Finset.card_eq_sum_ones,
    Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b hb
  simp

/-- If every entry is at least two and the sum is exactly twice the size of
the index set, then every entry is two. -/
private theorem eq_two_of_two_le_of_sum_eq_two_mul_card
    {α : Type*} [DecidableEq α]
    (I : Finset α) (f : α → Nat)
    (htwo : ∀ a ∈ I, 2 ≤ f a)
    (hsum : (∑ a ∈ I, f a) = I.card * 2) :
    ∀ a ∈ I, f a = 2 := by
  intro a ha
  have hrest : 2 * (I.erase a).card ≤ ∑ b ∈ I.erase a, f b := by
    calc
      2 * (I.erase a).card = ∑ _b ∈ I.erase a, 2 := by
        simp [Nat.mul_comm]
      _ ≤ ∑ b ∈ I.erase a, f b := by
        apply Finset.sum_le_sum
        intro b hb
        exact htwo b (Finset.mem_of_mem_erase hb)
  have hsplit := Finset.sum_erase_add I f ha
  have hcard := Finset.card_erase_of_mem ha
  have hlow := htwo a ha
  omega

/-- On an eleven-point triple-owned block system, no point belongs to six
five-blocks. -/
theorem blockDegree_five_le_five_of_card_eleven
    {Point Block : Type*} [Fintype Point] [Fintype Block]
    [DecidableEq Point]
    (S : BlockSystem Point Block) (hPoint : Fintype.card Point = 11)
    (p : Point) :
    S.blockDegree 5 p ≤ 5 := by
  classical
  by_contra hnot
  have hsix : 6 ≤ S.blockDegree 5 p := by omega
  let P := (S.blocksOfSize 5).filter fun b => p ∈ S.support b
  have hPcard : P.card = S.blockDegree 5 p := rfl
  obtain ⟨F, hFP, hFcard⟩ :=
    Finset.exists_subset_card_eq (show 6 ≤ P.card by simpa [hPcard])
  have hp (b : Block) (hb : b ∈ F) : p ∈ S.support b :=
    (Finset.mem_filter.mp (hFP hb)).2
  have hsize (b : Block) (hb : b ∈ F) : (S.support b).card = 5 :=
    S.mem_blocksOfSize.mp (Finset.mem_filter.mp (hFP hb)).1
  have hpDegree : S.degreeIn F p = 6 := by
    unfold BlockSystem.degreeIn
    have hfilter : F.filter (fun b => p ∈ S.support b) = F := by
      apply Finset.filter_eq_self.mpr
      exact hp
    rw [hfilter, hFcard]
  have hfirst : (∑ q : Point, S.degreeIn F q) = 30 := by
    rw [S.first_moment]
    calc
      (∑ b ∈ F, (S.support b).card) = ∑ _b ∈ F, 5 := by
        apply Finset.sum_congr rfl
        intro b hb
        exact hsize b hb
      _ = 30 := by simp [hFcard]
  have hsecond :
      (∑ q : Point, Nat.choose (S.degreeIn F q) 2) ≤ 30 := by
    have h := S.second_moment_le_two_choose F
    rw [hFcard] at h
    norm_num [Nat.choose] at h
    exact h
  have hpointwise (q : Point) :
      2 * S.degreeIn F q + (if q = p then 6 else 0) ≤
        Nat.choose (S.degreeIn F q) 2 + 3 := by
    by_cases hqp : q = p
    · subst q
      simp [hpDegree, Nat.choose]
    · simpa [hqp] using twice_le_choose_add_three (S.degreeIn F q)
  have hsum := Finset.sum_le_sum
    (s := (Finset.univ : Finset Point))
    (fun q _hq => hpointwise q)
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul] at hsum
  have hite : (∑ q : Point, if q = p then 6 else 0) = 6 := by simp
  have htwice :
      (∑ q : Point, 2 * S.degreeIn F q) =
        2 * (∑ q : Point, S.degreeIn F q) := by
    rw [Finset.mul_sum]
  rw [hite, htwice, hfirst, hPoint] at hsum
  omega

/-- If exactly five five-blocks pass through a pivot on eleven points, then
no four-block passes through the same pivot. -/
theorem blockDegree_four_eq_zero_of_card_eleven_of_blockDegree_five_eq_five
    {Point Block : Type*} [Fintype Point] [Fintype Block]
    [DecidableEq Point]
    (S : BlockSystem Point Block) (hPoint : Fintype.card Point = 11)
    (p : Point) (hfive : S.blockDegree 5 p = 5) :
    S.blockDegree 4 p = 0 := by
  classical
  let F := (S.blocksOfSize 5).filter fun b => p ∈ S.support b
  have hFcardRaw : F.card = S.blockDegree 5 p := rfl
  have hFcard : F.card = 5 := hFcardRaw.trans hfive
  have hp (b : Block) (hb : b ∈ F) : p ∈ S.support b :=
    (Finset.mem_filter.mp hb).2
  have hsize (b : Block) (hb : b ∈ F) : (S.support b).card = 5 :=
    S.mem_blocksOfSize.mp (Finset.mem_filter.mp hb).1
  have hpDegree : S.degreeIn F p = 5 := by
    unfold BlockSystem.degreeIn
    have hfilter : F.filter (fun b => p ∈ S.support b) = F := by
      apply Finset.filter_eq_self.mpr
      exact hp
    rw [hfilter, hFcard]
  have hfirst : (∑ q : Point, S.degreeIn F q) = 25 := by
    rw [S.first_moment]
    calc
      (∑ b ∈ F, (S.support b).card) = ∑ _b ∈ F, 5 := by
        apply Finset.sum_congr rfl
        intro b hb
        exact hsize b hb
      _ = 25 := by simp [hFcard]
  have hsecond :
      (∑ q : Point, Nat.choose (S.degreeIn F q) 2) ≤ 20 := by
    have h := S.second_moment_le_two_choose F
    rw [hFcard] at h
    norm_num [Nat.choose] at h
    exact h
  have hpointwise (q : Point) :
      2 * S.degreeIn F q + (if q = p then 3 else 0) ≤
        Nat.choose (S.degreeIn F q) 2 + 3 := by
    by_cases hqp : q = p
    · subst q
      simp [hpDegree, Nat.choose]
    · simpa [hqp] using twice_le_choose_add_three (S.degreeIn F q)
  have hsum := Finset.sum_le_sum
    (s := (Finset.univ : Finset Point))
    (fun q _hq => hpointwise q)
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul] at hsum
  have hite : (∑ q : Point, if q = p then 3 else 0) = 3 := by simp
  have htwice :
      (∑ q : Point, 2 * S.degreeIn F q) =
        2 * (∑ q : Point, S.degreeIn F q) := by
    rw [Finset.mul_sum]
  rw [hite, htwice, hfirst, hPoint] at hsum
  have hsecondEq :
      (∑ q : Point, Nat.choose (S.degreeIn F q) 2) = 20 := by
    omega
  have hsumEq :
      (∑ q : Point,
          (2 * S.degreeIn F q + (if q = p then 3 else 0))) =
        ∑ q : Point, (Nat.choose (S.degreeIn F q) 2 + 3) := by
    simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul]
    rw [hite, htwice, hfirst, hsecondEq, hPoint]
    norm_num
  have hprofile (q : Point) (hqp : q ≠ p) :
      S.degreeIn F q = 2 ∨ S.degreeIn F q = 3 := by
    have heq := (Finset.sum_eq_sum_iff_of_le
      (fun x (_hx : x ∈ (Finset.univ : Finset Point)) => hpointwise x)).mp
        hsumEq q (Finset.mem_univ q)
    simp [hqp] at heq
    have hcap := degreeIn_le_card S F q
    rw [hFcard] at hcap
    interval_cases hd : S.degreeIn F q <;>
      norm_num [Nat.choose] at *
  let O : Finset Point := Finset.univ.erase p
  have hOcard : O.card = 10 := by simp [O, hPoint]
  have hsumO : (∑ q ∈ O, S.degreeIn F q) = 20 := by
    have hsplit := Finset.sum_erase_add Finset.univ
      (fun q => S.degreeIn F q) (Finset.mem_univ p)
    change (∑ q ∈ O, S.degreeIn F q) + S.degreeIn F p =
      ∑ q : Point, S.degreeIn F q at hsplit
    rw [hpDegree, hfirst] at hsplit
    omega
  have hOtwo (q : Point) (hq : q ∈ O) : 2 ≤ S.degreeIn F q := by
    have hqp : q ≠ p := by
      exact (Finset.mem_erase.mp hq).1
    rcases hprofile q hqp with hq2 | hq3 <;> omega
  have hsumOTwo :
      (∑ q ∈ O, S.degreeIn F q) = O.card * 2 := by
    rw [hsumO, hOcard]
  have hdegreeOutside : ∀ q ∈ O, S.degreeIn F q = 2 :=
    eq_two_of_two_le_of_sum_eq_two_mul_card O
      (fun q => S.degreeIn F q) hOtwo hsumOTwo

  change ((S.blocksOfSize 4).filter fun b => p ∈ S.support b).card = 0
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro c hc
  have hc' := Finset.mem_filter.mp hc
  have hcsize : (S.support c).card = 4 := S.mem_blocksOfSize.mp hc'.1
  have hcp : p ∈ S.support c := hc'.2
  let T : Finset Point := S.support c \ {p}
  have hTerase : T = (S.support c).erase p := by
    ext q
    change q ∈ S.support c \ {p} ↔ q ∈ (S.support c).erase p
    constructor
    · intro hq
      have hq' := Finset.mem_sdiff.mp hq
      apply Finset.mem_erase.mpr
      exact ⟨by simpa using hq'.2, hq'.1⟩
    · intro hq
      have hq' := Finset.mem_erase.mp hq
      apply Finset.mem_sdiff.mpr
      exact ⟨hq'.2, by simpa using hq'.1⟩
  have hTcard : T.card = 3 := by
    rw [hTerase, Finset.card_erase_of_mem hcp, hcsize]
  have hTsubsetO : T ⊆ O := by
    intro q hq
    have hq' := Finset.mem_sdiff.mp hq
    apply Finset.mem_erase.mpr
    exact ⟨by simpa using hq'.2, Finset.mem_univ q⟩
  have hleft : (∑ q ∈ T, S.degreeIn F q) = 6 := by
    calc
      (∑ q ∈ T, S.degreeIn F q) = ∑ _q ∈ T, 2 := by
        apply Finset.sum_congr rfl
        intro q hq
        exact hdegreeOutside q (hTsubsetO hq)
      _ = 6 := by simp [hTcard]
  have hinter (b : Block) (hb : b ∈ F) :
      (T ∩ S.support b).card ≤ 1 := by
    have hbsize := hsize b hb
    have hbc : b ≠ c := by
      intro hbc
      subst c
      omega
    have hinterFull := S.distinct_block_inter_card_lt_three hbc
    have hpInter : p ∈ S.support c ∩ S.support b :=
      Finset.mem_inter.mpr ⟨hcp, hp b hb⟩
    have htrace :
        T ∩ S.support b = (S.support c ∩ S.support b).erase p := by
      ext q
      constructor
      · intro hq
        have hq' := Finset.mem_inter.mp hq
        have hqT := Finset.mem_sdiff.mp hq'.1
        apply Finset.mem_erase.mpr
        exact ⟨by simpa using hqT.2,
          Finset.mem_inter.mpr ⟨hqT.1, hq'.2⟩⟩
      · intro hq
        have hq' := Finset.mem_erase.mp hq
        have hqInter := Finset.mem_inter.mp hq'.2
        apply Finset.mem_inter.mpr
        exact ⟨Finset.mem_sdiff.mpr
          ⟨hqInter.1, by simpa using hq'.1⟩, hqInter.2⟩
    rw [htrace, Finset.card_erase_of_mem hpInter]
    rw [Finset.inter_comm] at hinterFull
    omega
  have hright :
      (∑ b ∈ F, (T ∩ S.support b).card) ≤ 5 := by
    calc
      (∑ b ∈ F, (T ∩ S.support b).card) ≤ ∑ _b ∈ F, 1 := by
        apply Finset.sum_le_sum
        intro b hb
        exact hinter b hb
      _ = 5 := by simp [hFcard]
  have hfubini := sum_degreeIn_over S F T
  rw [hleft] at hfubini
  omega

/-- The pair row and the deletion-sized bound `d₃ ≤ 12` improve the universal
five-block pencil cap from five to four. -/
theorem blockDegree_five_le_four_of_card_eleven_of_pairRow
    {Point Block : Type*} [Fintype Point] [Fintype Block]
    [DecidableEq Point]
    (S : BlockSystem Point Block) (hPoint : Fintype.card Point = 11)
    (p : Point)
    (hpair : S.blockDegree 3 p + 3 * S.blockDegree 4 p +
      6 * S.blockDegree 5 p = 45)
    (hthree : S.blockDegree 3 p ≤ 12) :
    S.blockDegree 5 p ≤ 4 := by
  have hcap := blockDegree_five_le_five_of_card_eleven S hPoint p
  by_contra hnot
  have hfive : S.blockDegree 5 p = 5 := by omega
  have hfour :=
    blockDegree_four_eq_zero_of_card_eleven_of_blockDegree_five_eq_five
      S hPoint p hfive
  rw [hfive, hfour] at hpair
  omega

end Erdos506.Finite
