import Erdos506.V1.ElevenFiveC40SmallSixPageCapFinish
import Erdos506.V1.ElevenFiveC40SmallFiveGeometryFinish
import Erdos506.V1.ElevenFiveC40FinalSevenDefectProfile
import Erdos506.V1.ElevenFiveC40FourteenSevenH27PageCap
import Erdos506.V1.ElevenFiveHarmonicFiveCap
import Erdos506.Incidence.SixConicActiveSignatureCap
import Mathlib.Tactic

/-!
# Page-cap reductions in the C40/L14 seven-five-block face

This file is deliberately not connected to the terminal C40 router.  It
records the part of the `L = 14, B₅ = 7` face which follows from the existing
incidence rows and the H28/H29/H30 page caps.

The useful numerical observation is a weighted Fubini bound.  If
`m(b) = ∑ p ∈ support(b), d₃(p)`, then

`∑ b ∈ blocksOfSize 5, m(b) = ∑ p, d₃(p) d₅(p) ≤ 318`.

Consequently the maximum pair-moment face `M = 42` contains an all-double
proper five-circle with `m(b) ≤ 48`.  The same selection works in the
`M = 40` face away from an actual disjoint pair.  A circle with six double
five-block neighbours and three-mass at most `48` contradicts the existing
page caps at host weights 28, 29 and 30.
-/

namespace Erdos506.V1

open Erdos506.Block
open Erdos506.Block.BlockSystem
open Erdos506.Incidence
open Erdos506.V3
open Erdos506.V4
open scoped BigOperators

universe u v

noncomputable local instance c40FourteenSeven_geometricBlockDecidableEq
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    (cfg : Configuration Point) : DecidableEq (GeometricBlock cfg) :=
  Classical.decEq _

/-! ## The common seven-block page-cap endpoint -/

/-- Incidence on a selected size-five block, split into the one- and
two-trace relative fibres of blocks of a fixed, different size. -/
private theorem c40FourteenSevenPageCap_selected_support_degree
    {Point : Type u} {Block : Type v} [Fintype Point] [Fintype Block]
    [DecidableEq Point] [DecidableEq Block]
    (S : BlockSystem Point Block) (b : Block)
    (hb : b ∈ S.blocksOfSize 5)
    (s x1 x2 : ℕ) (hsne : s ≠ 5)
    (hx1 : 1 + x1 = s) (hx2 : 2 + x2 = s) :
    (∑ p ∈ S.support b, S.blockDegree s p) =
      elevenFiveRelativeCount S (S.support b) 1 x1 +
        2 * elevenFiveRelativeCount S (S.support b) 2 x2 := by
  classical
  have hinc := S.sum_degreeIn_over (S.blocksOfSize s) (S.support b)
  change (∑ p ∈ S.support b, S.blockDegree s p) =
    ∑ c ∈ S.blocksOfSize s, (S.support b ∩ S.support c).card at hinc
  rw [hinc]
  calc
    (∑ c ∈ S.blocksOfSize s, (S.support b ∩ S.support c).card) =
        ∑ c : Block, if c ∈ S.blocksOfSize s then
          (S.support b ∩ S.support c).card else 0 := by
      unfold BlockSystem.blocksOfSize
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro c hc
      by_cases hcs : (S.support c).card = s
      · simp [hcs]
      · simp [hcs]
    _ = ∑ c : Block,
        ((if (S.support c ∩ S.support b).card = 1 ∧
              (S.support c \ S.support b).card = x1 then 1 else 0) +
          2 * (if (S.support c ∩ S.support b).card = 2 ∧
              (S.support c \ S.support b).card = x2 then 1 else 0)) := by
      apply Finset.sum_congr rfl
      intro c _hc
      by_cases hcs : c ∈ S.blocksOfSize s
      · have hcSize := S.mem_blocksOfSize.mp hcs
        have hcb : c ≠ b := by
          intro hcb
          subst c
          have hbSize := S.mem_blocksOfSize.mp hb
          exact hsne (by omega)
        have hinter := S.distinct_block_inter_card_lt_three hcb
        have hiLe : (S.support c ∩ S.support b).card ≤ 2 := by omega
        have hsplit :=
          Finset.card_inter_add_card_sdiff (S.support c) (S.support b)
        interval_cases hi : (S.support c ∩ S.support b).card
        · have hi' : (S.support b ∩ S.support c).card = 0 := by
            simpa [Finset.inter_comm] using hi
          rw [Finset.card_eq_zero.mp hi']
          simp [hcs, hi]
        · have ho : (S.support c \ S.support b).card = x1 := by omega
          have hi' : (S.support b ∩ S.support c).card = 1 := by
            simpa [Finset.inter_comm] using hi
          simp [hcs, hi, hi', ho]
        · have ho : (S.support c \ S.support b).card = x2 := by omega
          have hi' : (S.support b ∩ S.support c).card = 2 := by
            simpa [Finset.inter_comm] using hi
          simp [hcs, hi, hi', ho]
      · have hone : ¬ ((S.support c ∩ S.support b).card = 1 ∧
            (S.support c \ S.support b).card = x1) := by
          rintro ⟨hi, ho⟩
          apply hcs
          apply S.mem_blocksOfSize.mpr
          have hsplit :=
            Finset.card_inter_add_card_sdiff (S.support c) (S.support b)
          omega
        have htwo : ¬ ((S.support c ∩ S.support b).card = 2 ∧
            (S.support c \ S.support b).card = x2) := by
          rintro ⟨hi, ho⟩
          apply hcs
          apply S.mem_blocksOfSize.mpr
          have hsplit :=
            Finset.card_inter_add_card_sdiff (S.support c) (S.support b)
          omega
        simp [hcs, hone, htwo]
    _ = elevenFiveRelativeCount S (S.support b) 1 x1 +
        2 * elevenFiveRelativeCount S (S.support b) 2 x2 := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum]
      have hone :
          (∑ c : Block,
            if (S.support c ∩ S.support b).card = 1 ∧
                (S.support c \ S.support b).card = x1 then 1 else 0) =
            elevenFiveRelativeCount S (S.support b) 1 x1 := by
        rw [← Finset.sum_filter, ← Finset.card_eq_sum_ones]
        unfold elevenFiveRelativeCount
        apply congrArg Finset.card
        ext c
        simp
      have htwo :
          (∑ c : Block,
            if (S.support c ∩ S.support b).card = 2 ∧
                (S.support c \ S.support b).card = x2 then 1 else 0) =
            elevenFiveRelativeCount S (S.support b) 2 x2 := by
        rw [← Finset.sum_filter, ← Finset.card_eq_sum_ones]
        unfold elevenFiveRelativeCount
        apply congrArg Finset.card
        ext c
        simp
      rw [hone, htwo]

/-- Six double neighbours give five-degree mass `5 + 6 * 2 = 17`. -/
private theorem c40FourteenSevenPageCap_support_fiveDegree_sum_eq_seventeen
    {Point : Type u} {Block : Type v} [Fintype Point] [Fintype Block]
    [DecidableEq Point] [DecidableEq Block]
    (S : BlockSystem Point Block) (b : Block)
    (hb : b ∈ S.blocksOfSize 5)
    (hfive : S.blockCount 5 = 7)
    (hallDouble : ∀ c ∈ S.blocksOfSize 5, c ≠ b →
      (S.support b ∩ S.support c).card = 2) :
    (∑ p ∈ S.support b, S.blockDegree 5 p) = 17 := by
  classical
  let F := S.blocksOfSize 5
  have hbF : b ∈ F := by simpa [F] using hb
  have hFcard : F.card = 7 := by
    simpa [F, BlockSystem.blockCount] using hfive
  have hother (c : Block) (hc : c ∈ F.erase b) :
      (S.support b ∩ S.support c).card = 2 :=
    hallDouble c (by simpa [F] using Finset.mem_of_mem_erase hc)
      (Finset.mem_erase.mp hc).1
  have hotherSum :
      (∑ c ∈ F.erase b, (S.support b ∩ S.support c).card) = 12 := by
    calc
      (∑ c ∈ F.erase b, (S.support b ∩ S.support c).card) =
          ∑ _c ∈ F.erase b, 2 := by
        apply Finset.sum_congr rfl
        intro c hc
        exact hother c hc
      _ = 12 := by
        simp [Finset.card_erase_of_mem hbF, hFcard]
  have hself : (S.support b ∩ S.support b).card = 5 := by
    simp [S.mem_blocksOfSize.mp hb]
  have hsplit := Finset.sum_erase_add F
    (fun c => (S.support b ∩ S.support c).card) hbF
  have hinc := S.sum_degreeIn_over F (S.support b)
  change (∑ p ∈ S.support b, S.blockDegree 5 p) =
    ∑ c ∈ F, (S.support b ∩ S.support c).card at hinc
  rw [hinc]
  calc
    (∑ c ∈ F, (S.support b ∩ S.support c).card) =
        (∑ c ∈ F.erase b, (S.support b ∩ S.support c).card) +
          (S.support b ∩ S.support b).card := hsplit.symm
    _ = 17 := by rw [hotherSum, hself]

/-- The six other size-five blocks are exactly the selected block's six
relative `(2,3)` blocks. -/
private theorem c40FourteenSevenPageCap_relativeCount_two_three_eq_six
    {Point : Type u} {Block : Type v} [Fintype Point] [Fintype Block]
    [DecidableEq Point] [DecidableEq Block]
    (S : BlockSystem Point Block) (b : Block)
    (hb : b ∈ S.blocksOfSize 5)
    (hfive : S.blockCount 5 = 7)
    (hallDouble : ∀ c ∈ S.blocksOfSize 5, c ≠ b →
      (S.support c ∩ S.support b).card = 2) :
    elevenFiveRelativeCount S (S.support b) 2 3 = 6 := by
  classical
  let A := (Finset.univ : Finset Block).filter fun c =>
    (S.support c ∩ S.support b).card = 2 ∧
      (S.support c \ S.support b).card = 3
  let F := S.blocksOfSize 5
  have hbF : b ∈ F := by simpa [F] using hb
  have hAF : A = F.erase b := by
    ext c
    simp only [A, F, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_erase]
    constructor
    · rintro ⟨hi, ho⟩
      have hsplit :=
        Finset.card_inter_add_card_sdiff (S.support c) (S.support b)
      have hcFive : c ∈ S.blocksOfSize 5 := by
        apply S.mem_blocksOfSize.mpr
        omega
      have hcb : c ≠ b := by
        intro hcb
        subst c
        have hbSize := S.mem_blocksOfSize.mp hb
        simp [hbSize] at hi
      exact ⟨hcb, hcFive⟩
    · rintro ⟨hcb, hcFive⟩
      have hi := hallDouble c hcFive hcb
      have hcSize := S.mem_blocksOfSize.mp hcFive
      have hsplit :=
        Finset.card_inter_add_card_sdiff (S.support c) (S.support b)
      refine ⟨hi, ?_⟩
      omega
  change A.card = 6
  rw [hAF, Finset.card_erase_of_mem hbF]
  have hFcard : F.card = 7 := by
    simpa [F, BlockSystem.blockCount] using hfive
  rw [hFcard]

/-- A proper size-five circle with six double five-block neighbours and
three-degree mass at most `48` is incompatible with the H27/H28/H29/H30
page caps. -/
theorem elevenFive_c40_l14_b5_seven_doubleNeighbourCircle_impossible_of_pageCap
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    (cfg : Configuration Point) (Gamma : DeterminedCircle cfg)
    (hpoint : Fintype.card Point = 11)
    (hcap : BlockSizeCap (blockSystem cfg) 5)
    (hlocal : ∀ p : Point, ElevenFiveLocalRows (blockSystem cfg) p)
    (hD : (circleTrace cfg Gamma.1).card = 5)
    (hfive : (blockSystem cfg).blockCount 5 = 7)
    (hallDoubleAt : ∀ c ∈ (blockSystem cfg).blocksOfSize 5,
      c ≠ (Sum.inr Gamma : GeometricBlock cfg) →
        ((blockSystem cfg).support (Sum.inr Gamma) ∩
          (blockSystem cfg).support c).card = 2)
    (hsumThreeLe :
      (∑ p ∈ circleTrace cfg Gamma.1,
        (blockSystem cfg).blockDegree 3 p) ≤ 48) : False := by
  classical
  let S := blockSystem cfg
  let D := circleTrace cfg Gamma.1
  let b : GeometricBlock cfg := Sum.inr Gamma
  have hb : b ∈ S.blocksOfSize 5 := by
    apply S.mem_blocksOfSize.mpr
    simpa [S, b, D, blockSystem, geometricBlockSystem,
      geometricBlockSupport] using hD
  have hDb : S.support b = D := by
    simp [S, b, D, blockSystem, geometricBlockSystem,
      geometricBlockSupport]
  have hallAt : ∀ c ∈ S.blocksOfSize 5, c ≠ b →
      (S.support b ∩ S.support c).card = 2 := by
    intro c hc hcb
    exact hallDoubleAt c (by simpa [S] using hc) (by simpa [b] using hcb)
  have hzero : elevenFiveRelativeCount S D 1 4 = 0 := by
    apply elevenFive_relativeCount_one_four_eq_zero_of_no_sizeFive_singleton
    rintro ⟨c, hc, hinter⟩
    by_cases hcb : c = b
    · subst c
      rw [← hDb] at hinter
      have hbSize := S.mem_blocksOfSize.mp hb
      simp [hbSize] at hinter
    · have htwo := hallAt c hc hcb
      have htwo' : (S.support c ∩ D).card = 2 := by
        rw [← hDb]
        simpa [Finset.inter_comm] using htwo
      omega
  have hsumFive : (∑ p ∈ D, S.blockDegree 5 p) = 17 := by
    rw [← hDb]
    apply c40FourteenSevenPageCap_support_fiveDegree_sum_eq_seventeen
      S b hb (by simpa [S] using hfive)
    intro c hc hcb
    exact hallAt c hc hcb
  have hA23 : elevenFiveRelativeCount S D 2 3 = 6 := by
    rw [← hDb]
    apply c40FourteenSevenPageCap_relativeCount_two_three_eq_six
      S b hb (by simpa [S] using hfive)
    intro c hc hcb
    simpa [Finset.inter_comm] using hallAt c hc hcb
  have hrowTwo :=
    elevenFive_relativeCount_two_one_add_two_mul_two_two_add_three_mul_two_three_eq_sixty
      S D b hpoint (by simpa [D] using hD) hb hDb
        (by simpa [S] using hcap)
  have hhostRow :=
    elevenFiveHostWeight_eq_relativeCount22_add_three_mul_relativeCount23
      S D (by simpa [S] using hcap)
  have hhostCap := elevenFiveHostWeight_le_thirty S D
    hpoint (by simpa [D] using hD)
  have hthreeRelative :=
    c40FourteenSevenPageCap_selected_support_degree
      S b hb 3 2 1 (by omega) (by omega) (by omega)
  rw [hDb] at hthreeRelative
  have hsumThreeLeS : (∑ p ∈ D, S.blockDegree 3 p) ≤ 48 := by
    simpa [S, D] using hsumThreeLe
  have hA21Upper : elevenFiveRelativeCount S D 2 1 ≤ 24 := by omega
  have hA22Lower : 9 ≤ elevenFiveRelativeCount S D 2 2 := by omega
  have hhostCases : elevenFiveHostWeight S D = 27 ∨
      elevenFiveHostWeight S D = 28 ∨
        elevenFiveHostWeight S D = 29 ∨
          elevenFiveHostWeight S D = 30 := by
    omega
  have hsumPair :
      (∑ p ∈ D, (S.blockDegree 3 p + 3 * S.blockDegree 4 p +
        6 * S.blockDegree 5 p)) = ∑ _p ∈ D, 45 := by
    apply Finset.sum_congr rfl
    intro p _hp
    simpa [S] using (hlocal p).pairRow
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at hsumPair
  have hsumFourLower : 25 ≤ (∑ p ∈ D, S.blockDegree 4 p) := by
    rw [hsumFive] at hsumPair
    have hDcard : D.card = 5 := by simpa [D] using hD
    have hconst : (∑ _p ∈ D, 45) = 225 := by simp [hDcard]
    rw [hconst] at hsumPair
    omega
  have hfourRelative :=
    c40FourteenSevenPageCap_selected_support_degree
      S b hb 4 3 2 (by omega) (by omega) (by omega)
  rw [hDb] at hfourRelative
  rcases hhostCases with hhost | hhost | hhost | hhost
  · have hhostCfg : elevenFiveHostWeight (blockSystem cfg)
        (circleTrace cfg Gamma.1) = 27 := by simpa [S, D] using hhost
    have hpageCap :=
      elevenFive_relativeCount_one_three_le_six_of_hostWeight_eq_twenty_seven
        cfg Gamma hpoint hD hhostCfg
    have hpageCapS : elevenFiveRelativeCount S D 1 3 ≤ 6 := by
      simpa [S, D] using hpageCap
    have hA22 : elevenFiveRelativeCount S D 2 2 = 9 := by omega
    omega
  · have hhostCfg : elevenFiveHostWeight (blockSystem cfg)
        (circleTrace cfg Gamma.1) = 28 := by simpa [S, D] using hhost
    have hzeroCfg : elevenFiveRelativeCount (blockSystem cfg)
        (circleTrace cfg Gamma.1) 1 4 = 0 := by simpa [S, D] using hzero
    have hpageCap := elevenFiveC39H28PageCapInput_of_hostPairFibres cfg
      Gamma hpoint hD hhostCfg hzeroCfg
    have hpageCapS : elevenFiveRelativeCount S D 1 3 ≤ 4 := by
      simpa [S, D] using hpageCap
    have hA22 : elevenFiveRelativeCount S D 2 2 = 10 := by omega
    omega
  · have hK21 := elevenFive_c39_h29_relativeCount_one_three_le_one
      cfg Gamma hpoint hD (by simpa [S, D] using hhost)
    have hK21S : elevenFiveRelativeCount S D 1 3 ≤ 1 := by
      simpa [S, D] using hK21
    have hA22 : elevenFiveRelativeCount S D 2 2 = 11 := by omega
    omega
  · have hK21 := elevenFive_c39_h30_relativeCount_one_three_eq_zero
      cfg Gamma hpoint hD (by simpa [S, D] using hhost)
    have hK21S : elevenFiveRelativeCount S D 1 3 = 0 := by
      simpa [S, D] using hK21
    have hA22 : elevenFiveRelativeCount S D 2 2 = 12 := by omega
    omega

/-! ## Global census and weighted Fubini -/

/-- The C40/L14/B₅=7 rows fix the remaining block counts. -/
theorem elevenFive_c40_l14_b5_seven_block_census
    {Point : Type u} {Block : Type v} [Fintype Point] [Fintype Block]
    [DecidableEq Point]
    (S : BlockSystem Point Block) (hglobal : ElevenFiveGlobalRows S)
    (hC : S.totalCircleCount = 40)
    (hL : elevenFiveLineTotal S = 14)
    (hfive : S.blockCount 5 = 7) :
    S.blockCount 3 = 31 ∧ S.blockCount 4 = 16 := by
  have htriple := hglobal.tripleRow
  have htotal := hglobal.blockTotal
  rw [hC, hL, hfive] at htotal
  rw [hfive] at htriple
  omega

/-- If `u` is the number of degree-twelve three-block pivots, then the
three-degree census is `n₆=u+2`, `n₉+2u=9`. -/
theorem elevenFive_c40_l14_b5_seven_threeDegree_census
    {Point : Type u} {Block : Type v} [Fintype Point] [Fintype Block]
    [DecidableEq Point]
    (S : BlockSystem Point Block) (hcard : Fintype.card Point = 11)
    (hlocal : ∀ p : Point, ElevenFiveLocalRows S p)
    (hglobal : ElevenFiveGlobalRows S)
    (hC : S.totalCircleCount = 40)
    (hL : elevenFiveLineTotal S = 14)
    (hfive : S.blockCount 5 = 7) :
    ((Finset.univ : Finset Point).filter
        fun p => S.blockDegree 3 p = 6).card =
      ((Finset.univ : Finset Point).filter
        fun p => S.blockDegree 3 p = 12).card + 2 ∧
      ((Finset.univ : Finset Point).filter
          fun p => S.blockDegree 3 p = 9).card +
        2 * ((Finset.univ : Finset Point).filter
          fun p => S.blockDegree 3 p = 12).card = 9 ∧
      ∀ p : Point, S.blockDegree 3 p = 6 ∨
        S.blockDegree 3 p = 9 ∨ S.blockDegree 3 p = 12 := by
  classical
  obtain ⟨hthreeCount, _hfourCount⟩ :=
    elevenFive_c40_l14_b5_seven_block_census S hglobal hC hL hfive
  have hthreeSum : (∑ p : Point, S.blockDegree 3 p) = 93 := by
    rw [hglobal.threeIncidence, hthreeCount]
  have hvalues (p : Point) : S.blockDegree 3 p = 6 ∨
      S.blockDegree 3 p = 9 ∨ S.blockDegree 3 p = 12 :=
    elevenFive_c40_threeDegree_values S p (hlocal p) hC
  let N6 := (Finset.univ : Finset Point).filter
    fun p => S.blockDegree 3 p = 6
  let N9 := (Finset.univ : Finset Point).filter
    fun p => S.blockDegree 3 p = 9
  let N12 := (Finset.univ : Finset Point).filter
    fun p => S.blockDegree 3 p = 12
  have hN6sum : (∑ p : Point, if p ∈ N6 then 1 else 0) = N6.card := by
    simp [N6]
  have hN9sum : (∑ p : Point, if p ∈ N9 then 1 else 0) = N9.card := by
    simp [N9]
  have hN12sum : (∑ p : Point, if p ∈ N12 then 1 else 0) = N12.card := by
    simp [N12]
  have hdegreePoint (p : Point) : S.blockDegree 3 p =
      6 + 3 * (if p ∈ N9 then 1 else 0) +
        6 * (if p ∈ N12 then 1 else 0) := by
    rcases hvalues p with h6 | h9 | h12
    · simp [N9, N12, h6]
    · simp [N9, N12, h9]
    · simp [N9, N12, h12]
  have hdegreeSum :
      (∑ p : Point, S.blockDegree 3 p) =
        ∑ p : Point, (6 + 3 * (if p ∈ N9 then 1 else 0) +
          6 * (if p ∈ N12 then 1 else 0)) := by
    apply Finset.sum_congr rfl
    intro p _hp
    exact hdegreePoint p
  have hN9N12 : N9.card + 2 * N12.card = 9 := by
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
      ← Finset.mul_sum, ← Finset.mul_sum, hN9sum, hN12sum,
      Finset.sum_const, Finset.card_univ, hcard, hthreeSum] at hdegreeSum
    norm_num at hdegreeSum
    omega
  have hpartitionPoint (p : Point) :
      (if p ∈ N6 then 1 else 0) +
        (if p ∈ N9 then 1 else 0) +
          (if p ∈ N12 then 1 else 0) = 1 := by
    rcases hvalues p with h6 | h9 | h12
    · simp [N6, N9, N12, h6]
    · simp [N6, N9, N12, h9]
    · simp [N6, N9, N12, h12]
  have hpartitionSum :
      (∑ p : Point, ((if p ∈ N6 then 1 else 0) +
        (if p ∈ N9 then 1 else 0) +
          (if p ∈ N12 then 1 else 0))) = ∑ _p : Point, 1 := by
    apply Finset.sum_congr rfl
    intro p _hp
    exact hpartitionPoint p
  have hpartition : N6.card + N9.card + N12.card = 11 := by
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
      hN6sum, hN9sum, hN12sum, Finset.sum_const,
      Finset.card_univ, hcard] at hpartitionSum
    norm_num at hpartitionSum
    exact hpartitionSum
  change N6.card = N12.card + 2 ∧
    N9.card + 2 * N12.card = 9 ∧ ∀ p : Point,
      S.blockDegree 3 p = 6 ∨ S.blockDegree 3 p = 9 ∨
        S.blockDegree 3 p = 12
  exact ⟨by omega, hN9N12, hvalues⟩

/-- Weighted point/block Fubini for three-degree mass on the five-block
family. -/
theorem elevenFive_fiveBlock_threeMass_sum_eq_weighted
    {Point : Type u} {Block : Type v} [Fintype Point] [Fintype Block]
    [DecidableEq Point]
    (S : BlockSystem Point Block) :
    (∑ b ∈ S.blocksOfSize 5,
        ∑ p ∈ S.support b, S.blockDegree 3 p) =
      ∑ p : Point, S.blockDegree 3 p * S.blockDegree 5 p := by
  classical
  let F := S.blocksOfSize 5
  calc
    (∑ b ∈ S.blocksOfSize 5,
        ∑ p ∈ S.support b, S.blockDegree 3 p) =
        ∑ b ∈ F, ∑ p : Point,
          if p ∈ S.support b then S.blockDegree 3 p else 0 := by
      apply Finset.sum_congr rfl
      intro b hb
      simp [F]
    _ = ∑ p : Point, ∑ b ∈ F,
          if p ∈ S.support b then S.blockDegree 3 p else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ p : Point, S.blockDegree 3 p * S.blockDegree 5 p := by
      apply Finset.sum_congr rfl
      intro p _hp
      change (∑ b ∈ F,
          if p ∈ S.support b then S.blockDegree 3 p else 0) =
        S.blockDegree 3 p *
          ((F.filter fun b => p ∈ S.support b).card)
      rw [Finset.card_eq_sum_ones, Finset.sum_filter, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro b _hb
      by_cases hpb : p ∈ S.support b <;> simp [hpb]

/-- The mixed three/five incidence in the C40/L14/B₅=7 row is at most
`318`.  This uses only the three-degree spectrum, the global incidence rows,
Langer at degree six, and the universal cap `d₅ ≤ 4`. -/
theorem elevenFive_c40_l14_b5_seven_weighted_three_five_le_318
    {Point : Type u} {Block : Type v} [Fintype Point] [Fintype Block]
    [DecidableEq Point]
    (S : BlockSystem Point Block) (hcard : Fintype.card Point = 11)
    (hlocal : ∀ p : Point, ElevenFiveLocalRows S p)
    (hglobal : ElevenFiveGlobalRows S)
    (hC : S.totalCircleCount = 40)
    (hL : elevenFiveLineTotal S = 14)
    (hfive : S.blockCount 5 = 7) :
    (∑ p : Point, S.blockDegree 3 p * S.blockDegree 5 p) ≤ 318 := by
  classical
  obtain ⟨hN6card, hN9N12, hvalues⟩ :=
    elevenFive_c40_l14_b5_seven_threeDegree_census
      S hcard hlocal hglobal hC hL hfive
  let N6 := (Finset.univ : Finset Point).filter
    fun p => S.blockDegree 3 p = 6
  let N9 := (Finset.univ : Finset Point).filter
    fun p => S.blockDegree 3 p = 9
  let N12 := (Finset.univ : Finset Point).filter
    fun p => S.blockDegree 3 p = 12
  let E6 := ∑ p ∈ N6, S.blockDegree 5 p
  let E9 := ∑ p ∈ N9, S.blockDegree 5 p
  let E12 := ∑ p ∈ N12, S.blockDegree 5 p
  have hN6card' : N6.card = N12.card + 2 := by
    simpa [N6, N12] using hN6card
  have hN9N12' : N9.card + 2 * N12.card = 9 := by
    simpa only [N9, N12] using hN9N12
  have hpartition (w : Point → ℕ) :
      (∑ p : Point, w p) =
        (∑ p ∈ N6, w p) + (∑ p ∈ N9, w p) +
          (∑ p ∈ N12, w p) := by
    have hpoint (p : Point) : w p =
        (if p ∈ N6 then w p else 0) +
          (if p ∈ N9 then w p else 0) +
            (if p ∈ N12 then w p else 0) := by
      rcases hvalues p with h6 | h9 | h12
      · simp [N6, N9, N12, h6]
      · simp [N6, N9, N12, h9]
      · simp [N6, N9, N12, h12]
    calc
      (∑ p : Point, w p) = ∑ p : Point,
          ((if p ∈ N6 then w p else 0) +
            (if p ∈ N9 then w p else 0) +
              (if p ∈ N12 then w p else 0)) := by
        apply Finset.sum_congr rfl
        intro p _hp
        exact hpoint p
      _ = (∑ p : Point, if p ∈ N6 then w p else 0) +
          (∑ p : Point, if p ∈ N9 then w p else 0) +
            (∑ p : Point, if p ∈ N12 then w p else 0) := by
        simp only [Finset.sum_add_distrib]
      _ = (∑ p ∈ N6, w p) + (∑ p ∈ N9, w p) +
          (∑ p ∈ N12, w p) := by
        simp
  have htotal : E6 + E9 + E12 = 35 := by
    have hinc : (∑ p : Point, S.blockDegree 5 p) = 35 := by
      rw [hglobal.fiveIncidence, hfive]
    have hparts := hpartition (fun p => S.blockDegree 5 p)
    simpa [E6, E9, E12, hinc] using hparts.symm
  have hE6Cap : E6 ≤ 4 * N6.card := by
    calc
      E6 ≤ ∑ _p ∈ N6, 4 := by
        apply Finset.sum_le_sum
        intro p _hp
        exact (hlocal p).fiveDegreeCap
      _ = 4 * N6.card := by simp [Nat.mul_comm]
  have hE9Cap : E9 ≤ 4 * N9.card := by
    calc
      E9 ≤ ∑ _p ∈ N9, 4 := by
        apply Finset.sum_le_sum
        intro p _hp
        exact (hlocal p).fiveDegreeCap
      _ = 4 * N9.card := by simp [Nat.mul_comm]
  have hE12Cap : E12 ≤ 4 * N12.card := by
    calc
      E12 ≤ ∑ _p ∈ N12, 4 := by
        apply Finset.sum_le_sum
        intro p _hp
        exact (hlocal p).fiveDegreeCap
      _ = 4 * N12.card := by simp [Nat.mul_comm]
  have hE12Le : E12 ≤ E6 + 1 := by omega
  have hT6 : (∑ p ∈ N6,
      S.blockDegree 3 p * S.blockDegree 5 p) = 6 * E6 := by
    calc
      (∑ p ∈ N6, S.blockDegree 3 p * S.blockDegree 5 p) =
          ∑ p ∈ N6, 6 * S.blockDegree 5 p := by
        apply Finset.sum_congr rfl
        intro p hp
        have hp6 : S.blockDegree 3 p = 6 := by simpa [N6] using hp
        rw [hp6]
      _ = 6 * E6 := by rw [Finset.mul_sum]
  have hT9 : (∑ p ∈ N9,
      S.blockDegree 3 p * S.blockDegree 5 p) = 9 * E9 := by
    calc
      (∑ p ∈ N9, S.blockDegree 3 p * S.blockDegree 5 p) =
          ∑ p ∈ N9, 9 * S.blockDegree 5 p := by
        apply Finset.sum_congr rfl
        intro p hp
        have hp9 : S.blockDegree 3 p = 9 := by simpa [N9] using hp
        rw [hp9]
      _ = 9 * E9 := by rw [Finset.mul_sum]
  have hT12 : (∑ p ∈ N12,
      S.blockDegree 3 p * S.blockDegree 5 p) = 12 * E12 := by
    calc
      (∑ p ∈ N12, S.blockDegree 3 p * S.blockDegree 5 p) =
          ∑ p ∈ N12, 12 * S.blockDegree 5 p := by
        apply Finset.sum_congr rfl
        intro p hp
        have hp12 : S.blockDegree 3 p = 12 := by simpa [N12] using hp
        rw [hp12]
      _ = 12 * E12 := by rw [Finset.mul_sum]
  have hweighted := hpartition
    (fun p => S.blockDegree 3 p * S.blockDegree 5 p)
  rw [hT6, hT9, hT12] at hweighted
  rw [hweighted]
  omega

/-! ## Moment 42 -/

/-- Moment 42 is equality in the universal seven-block pair bound. -/
private theorem c40FourteenSeven_allDouble_of_secondMoment_fortyTwo
    {Point : Type u} {Block : Type v} [Fintype Point] [Fintype Block]
    [DecidableEq Point] [DecidableEq Block]
    (S : BlockSystem Point Block) (hfive : S.blockCount 5 = 7)
    (hmoment : elevenFiveSecondMoment S = 42) :
    ∀ b ∈ S.blocksOfSize 5, ∀ c ∈ S.blocksOfSize 5,
      b ≠ c → (S.support b ∩ S.support c).card = 2 := by
  classical
  let F := S.blocksOfSize 5
  have hFcard : F.card = 7 := by
    simpa [F, BlockSystem.blockCount] using hfive
  have hmoment' :
      (∑ p : Point, Nat.choose (S.degreeIn F p) 2) =
        2 * Nat.choose F.card 2 := by
    simpa [F, BlockSystem.blockDegree, elevenFiveSecondMoment,
      hFcard, Nat.choose] using hmoment
  exact blockFamily_inter_card_eq_two_of_pairMoment_maximum S F hmoment'

/-- The K4 cut removes size-five lines throughout the C40/L14/B₅=7 row. -/
private theorem c40FourteenSeven_lineCount_five_eq_zero
    {Point : Type u} {Block : Type v} [Fintype Point] [Fintype Block]
    [DecidableEq Point]
    (S : BlockSystem Point Block) (hglobal : ElevenFiveGlobalRows S)
    (hC : S.totalCircleCount = 40)
    (hL : elevenFiveLineTotal S = 14)
    (hfive : S.blockCount 5 = 7) : S.lineCount 5 = 0 := by
  have hcut := elevenFive_k4_cut S hglobal hC hL
  omega

/-- The maximum moment face `M=42` is already impossible by weighted
averaging and the page-cap endpoint; no K3.2/K3.3 external-trace input is
needed. -/
theorem elevenFive_c40_l14_b5_seven_secondMoment_fortyTwo_impossible
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    (cfg : Configuration Point)
    (hpoint : Fintype.card Point = 11)
    (hcap : BlockSizeCap (blockSystem cfg) 5)
    (hlocal : ∀ p : Point, ElevenFiveLocalRows (blockSystem cfg) p)
    (hglobal : ElevenFiveGlobalRows (blockSystem cfg))
    (hC : (blockSystem cfg).totalCircleCount = 40)
    (hL : elevenFiveLineTotal (blockSystem cfg) = 14)
    (hfive : (blockSystem cfg).blockCount 5 = 7)
    (hmoment : elevenFiveSecondMoment (blockSystem cfg) = 42) : False := by
  classical
  let S := blockSystem cfg
  let F := S.blocksOfSize 5
  let mass : GeometricBlock cfg → ℕ := fun b =>
    ∑ p ∈ S.support b, S.blockDegree 3 p
  have hFcard : F.card = 7 := by
    simpa [F, S, BlockSystem.blockCount] using hfive
  have hweighted :=
    elevenFive_c40_l14_b5_seven_weighted_three_five_le_318
      S hpoint (by simpa [S] using hlocal) (by simpa [S] using hglobal)
        (by simpa [S] using hC) (by simpa [S] using hL)
          (by simpa [S] using hfive)
  have hmassTotal : (∑ b ∈ F, mass b) ≤ 318 := by
    have hfubini := elevenFive_fiveBlock_threeMass_sum_eq_weighted S
    simpa [F, mass] using hfubini.trans_le hweighted
  have hlow : ∃ b ∈ F, mass b ≤ 47 := by
    by_contra hnot
    push_neg at hnot
    have hlower : (∑ _b ∈ F, 48) ≤ ∑ b ∈ F, mass b := by
      apply Finset.sum_le_sum
      intro b hb
      have hbHigh := hnot b hb
      omega
    have hconstant : (∑ _b ∈ F, 48) = 336 := by
      simp [hFcard]
    omega
  obtain ⟨b, hbF, hbLow⟩ := hlow
  have hallDouble := c40FourteenSeven_allDouble_of_secondMoment_fortyTwo
    S (by simpa [S] using hfive) (by simpa [S] using hmoment)
  have hlineFive := c40FourteenSeven_lineCount_five_eq_zero
    S (by simpa [S] using hglobal) (by simpa [S] using hC)
      (by simpa [S] using hL) (by simpa [S] using hfive)
  rcases b with L | Gamma
  · have hbLine : (Sum.inl L : GeometricBlock cfg) ∈ S.lineBlocksOfSize 5 := by
      apply S.mem_blocksOfKindSize.mpr
      refine ⟨?_, S.mem_blocksOfSize.mp (by simpa [F] using hbF)⟩
      simp [S, blockSystem, geometricBlockSystem, geometricBlockKind]
    have hlineCard : (S.lineBlocksOfSize 5).card = 0 := by
      simpa [BlockSystem.lineCount] using hlineFive
    have hpositive := Finset.card_pos.mpr ⟨Sum.inl L, hbLine⟩
    omega
  · have hb : (Sum.inr Gamma : GeometricBlock cfg) ∈ S.blocksOfSize 5 := by
      simpa [F] using hbF
    have hD : (circleTrace cfg Gamma.1).card = 5 := by
      have hsize := S.mem_blocksOfSize.mp hb
      simpa [S, blockSystem, geometricBlockSystem,
        geometricBlockSupport] using hsize
    have hallAt : ∀ c ∈ (blockSystem cfg).blocksOfSize 5,
        c ≠ (Sum.inr Gamma : GeometricBlock cfg) →
          ((blockSystem cfg).support (Sum.inr Gamma) ∩
            (blockSystem cfg).support c).card = 2 := by
      intro c hc hcb
      exact hallDouble (Sum.inr Gamma) hb c (by simpa [S] using hc) hcb.symm
    have hmass :
        (∑ p ∈ circleTrace cfg Gamma.1,
          (blockSystem cfg).blockDegree 3 p) ≤ 47 := by
      simpa [mass, S, blockSystem, geometricBlockSystem,
        geometricBlockSupport] using hbLow
    exact
      elevenFive_c40_l14_b5_seven_doubleNeighbourCircle_impossible_of_pageCap
        cfg Gamma hpoint hcap hlocal hD hfive hallAt (by omega)

/-! ## The disjoint branch of moment 40 -/

/-- If the moment-40 face contains an actual disjoint pair, the five blocks
away from that pair are clean: every one of them meets all six other
five-blocks twice.  Weighted averaging selects one with three-mass at most
`47`, so the common page-cap endpoint closes the branch. -/
theorem elevenFive_c40_l14_b5_seven_secondMoment_forty_disjoint_impossible
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    (cfg : Configuration Point)
    (hpoint : Fintype.card Point = 11)
    (hcap : BlockSizeCap (blockSystem cfg) 5)
    (hlocal : ∀ p : Point, ElevenFiveLocalRows (blockSystem cfg) p)
    (hglobal : ElevenFiveGlobalRows (blockSystem cfg))
    (hC : (blockSystem cfg).totalCircleCount = 40)
    (hL : elevenFiveLineTotal (blockSystem cfg) = 14)
    (hfive : (blockSystem cfg).blockCount 5 = 7)
    (hmoment : elevenFiveSecondMoment (blockSystem cfg) = 40)
    {f g : GeometricBlock cfg}
    (hf : f ∈ (blockSystem cfg).blocksOfSize 5)
    (hg : g ∈ (blockSystem cfg).blocksOfSize 5)
    (hfg : f ≠ g)
    (hdisjoint : ((blockSystem cfg).support f ∩
      (blockSystem cfg).support g).card = 0) : False := by
  classical
  let S := blockSystem cfg
  let F := S.blocksOfSize 5
  let mass : GeometricBlock cfg → ℕ := fun b =>
    ∑ p ∈ S.support b, S.blockDegree 3 p
  have hfF : f ∈ F := by simpa [F, S] using hf
  have hgF : g ∈ F := by simpa [F, S] using hg
  have hFcard : F.card = 7 := by
    simpa [F, S, BlockSystem.blockCount] using hfive
  have hgfMem : g ∈ F.erase f := Finset.mem_erase.mpr ⟨hfg.symm, hgF⟩
  let R := (F.erase f).erase g
  have hRcard : R.card = 5 := by
    dsimp [R]
    rw [Finset.card_erase_of_mem hgfMem,
      Finset.card_erase_of_mem hfF, hFcard]
  have hRspec (b : GeometricBlock cfg) (hb : b ∈ R) :
      b ∈ S.blocksOfSize 5 ∧ b ≠ f ∧ b ≠ g := by
    have hbg := Finset.mem_erase.mp hb
    have hbf := Finset.mem_erase.mp hbg.2
    exact ⟨by simpa [F] using hbf.2, hbf.1, hbg.1⟩
  have hmomentRaw :
      (∑ p : Point, Nat.choose (S.blockDegree 5 p) 2) = 40 := by
    simpa [S, elevenFiveSecondMoment] using hmoment
  have hother :=
    fiveBlock_inter_card_eq_two_of_secondMoment_forty_of_disjoint_pair
      S (by simpa [S] using hfive) hmomentRaw
        (by simpa [S] using hf) (by simpa [S] using hg) hfg
          (by simpa [S] using hdisjoint)
  have hpairNe (b : GeometricBlock cfg) (hb : b ∈ R)
      (c : GeometricBlock cfg) :
      ({b, c} : Finset (GeometricBlock cfg)) ≠ {f, g} := by
    intro hpair
    have hbFG : b ∈ ({f, g} : Finset (GeometricBlock cfg)) := by
      rw [← hpair]
      simp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hbFG
    rcases hbFG with hbf | hbg
    · exact (hRspec b hb).2.1 hbf
    · exact (hRspec b hb).2.2 hbg
  have hweighted :=
    elevenFive_c40_l14_b5_seven_weighted_three_five_le_318
      S hpoint (by simpa [S] using hlocal) (by simpa [S] using hglobal)
        (by simpa [S] using hC) (by simpa [S] using hL)
          (by simpa [S] using hfive)
  have hmassTotal : (∑ b ∈ F, mass b) ≤ 318 := by
    have hfubini := elevenFive_fiveBlock_threeMass_sum_eq_weighted S
    simpa [F, mass] using hfubini.trans_le hweighted

  have hFGdisjoint : Disjoint (S.support f) (S.support g) := by
    rw [Finset.disjoint_left]
    intro p hpf hpg
    have hp : p ∈ S.support f ∩ S.support g :=
      Finset.mem_inter.mpr ⟨hpf, hpg⟩
    have hempty : S.support f ∩ S.support g = ∅ :=
      Finset.card_eq_zero.mp (by simpa [S] using hdisjoint)
    simpa [hempty] using hp
  let V := S.support f ∪ S.support g
  have hVcard : V.card = 10 := by
    dsimp [V]
    rw [Finset.card_union_of_disjoint hFGdisjoint,
      S.mem_blocksOfSize.mp (by simpa [S] using hf),
      S.mem_blocksOfSize.mp (by simpa [S] using hg)]
  have hcomplCard : ((Finset.univ : Finset Point) \ V).card = 1 := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ V),
      Finset.card_univ, hpoint, hVcard]
  have hcomplLe :
      (∑ p ∈ (Finset.univ : Finset Point) \ V, S.blockDegree 3 p) ≤ 12 := by
    calc
      (∑ p ∈ (Finset.univ : Finset Point) \ V, S.blockDegree 3 p) ≤
          ∑ _p ∈ (Finset.univ : Finset Point) \ V, 12 := by
        apply Finset.sum_le_sum
        intro p _hp
        rcases elevenFive_c40_threeDegree_values S p (hlocal p)
          (by simpa [S] using hC) with h6 | h9 | h12
        · omega
        · omega
        · omega
      _ = 12 := by simp [hcomplCard]
  have hthreeSum : (∑ p : Point, S.blockDegree 3 p) = 93 := by
    obtain ⟨hthreeCount, _hfourCount⟩ :=
      elevenFive_c40_l14_b5_seven_block_census
        S (by simpa [S] using hglobal) (by simpa [S] using hC)
          (by simpa [S] using hL) (by simpa [S] using hfive)
    rw [hglobal.threeIncidence, hthreeCount]
  have hpointSplit :
      (∑ p ∈ (Finset.univ : Finset Point) \ V, S.blockDegree 3 p) +
          (∑ p ∈ V, S.blockDegree 3 p) =
        ∑ p : Point, S.blockDegree 3 p :=
    Finset.sum_sdiff (Finset.subset_univ V)
  have hVsum : (∑ p ∈ V, S.blockDegree 3 p) = mass f + mass g := by
    dsimp [V, mass]
    rw [Finset.sum_union hFGdisjoint]
  have hendpointMass : 81 ≤ mass f + mass g := by
    rw [hVsum, hthreeSum] at hpointSplit
    omega
  have hsplitF := Finset.sum_erase_add F mass hfF
  have hsplitG := Finset.sum_erase_add (F.erase f) mass hgfMem
  have hmassDecomp :
      (∑ b ∈ F, mass b) = ((∑ b ∈ R, mass b) + mass g) + mass f := by
    calc
      (∑ b ∈ F, mass b) = (∑ b ∈ F.erase f, mass b) + mass f :=
        hsplitF.symm
      _ = ((∑ b ∈ R, mass b) + mass g) + mass f := by
        dsimp [R]
        rw [hsplitG.symm]
  have hRmassLe : (∑ b ∈ R, mass b) ≤ 237 := by omega
  have hlow : ∃ b ∈ R, mass b ≤ 47 := by
    by_contra hnot
    push_neg at hnot
    have hlower : (∑ _b ∈ R, 48) ≤ ∑ b ∈ R, mass b := by
      apply Finset.sum_le_sum
      intro b hb
      have hbHigh := hnot b hb
      omega
    have hconstant : (∑ _b ∈ R, 48) = 240 := by
      simp [hRcard]
    omega
  obtain ⟨b, hbR, hbLow⟩ := hlow
  have hlineFive := c40FourteenSeven_lineCount_five_eq_zero
    S (by simpa [S] using hglobal) (by simpa [S] using hC)
      (by simpa [S] using hL) (by simpa [S] using hfive)
  rcases b with L | Gamma
  · have hbLine : (Sum.inl L : GeometricBlock cfg) ∈ S.lineBlocksOfSize 5 := by
      apply S.mem_blocksOfKindSize.mpr
      refine ⟨?_, S.mem_blocksOfSize.mp (hRspec (Sum.inl L) hbR).1⟩
      simp [S, blockSystem, geometricBlockSystem, geometricBlockKind]
    have hlineCard : (S.lineBlocksOfSize 5).card = 0 := by
      simpa [BlockSystem.lineCount] using hlineFive
    have hpositive := Finset.card_pos.mpr ⟨Sum.inl L, hbLine⟩
    omega
  · have hb : (Sum.inr Gamma : GeometricBlock cfg) ∈ S.blocksOfSize 5 :=
      (hRspec (Sum.inr Gamma) hbR).1
    have hD : (circleTrace cfg Gamma.1).card = 5 := by
      have hsize := S.mem_blocksOfSize.mp hb
      simpa [S, blockSystem, geometricBlockSystem,
        geometricBlockSupport] using hsize
    have hallAt : ∀ c ∈ (blockSystem cfg).blocksOfSize 5,
        c ≠ (Sum.inr Gamma : GeometricBlock cfg) →
          ((blockSystem cfg).support (Sum.inr Gamma) ∩
            (blockSystem cfg).support c).card = 2 := by
      intro c hc hcb
      exact hother (Sum.inr Gamma) hb c (by simpa [S] using hc) hcb.symm
        (hpairNe (Sum.inr Gamma) hbR c)
    have hmass :
        (∑ p ∈ circleTrace cfg Gamma.1,
          (blockSystem cfg).blockDegree 3 p) ≤ 47 := by
      simpa [mass, S, blockSystem, geometricBlockSystem,
        geometricBlockSupport] using hbLow
    exact
      elevenFive_c40_l14_b5_seven_doubleNeighbourCircle_impossible_of_pageCap
        cfg Gamma hpoint hcap hlocal hD hfive hallAt (by omega)

/-! ## Moment 41: the sharp weighted selector -/

/-- In moment 41 exactly four points have five-degree four.  Only this one
coordinate of the full profile is needed for the sharpened weighted bound. -/
theorem elevenFive_c40_l14_b5_seven_secondMoment_fortyOne_degreeFour_card
    {Point : Type u} {Block : Type v} [Fintype Point] [Fintype Block]
    [DecidableEq Point]
    (S : BlockSystem Point Block) (hcard : Fintype.card Point = 11)
    (hlocal : ∀ p : Point, ElevenFiveLocalRows S p)
    (hglobal : ElevenFiveGlobalRows S)
    (hfive : S.blockCount 5 = 7)
    (hmoment : elevenFiveSecondMoment S = 41) :
    ((Finset.univ : Finset Point).filter fun p =>
      S.blockDegree 5 p = 4).card = 4 := by
  classical
  let count : ℕ → ℕ := fun d =>
    ((Finset.univ : Finset Point).filter fun p =>
      S.blockDegree 5 p = d).card
  have hdegree (p : Point) : S.blockDegree 5 p = 0 ∨
      S.blockDegree 5 p = 1 ∨ S.blockDegree 5 p = 2 ∨
        S.blockDegree 5 p = 3 ∨ S.blockDegree 5 p = 4 := by
    have hcap := (hlocal p).fiveDegreeCap
    omega
  have hcount (d : ℕ) :
      (∑ p : Point, if S.blockDegree 5 p = d then 1 else 0) = count d := by
    simp [count]
  have hpartitionPoint (p : Point) :
      (if S.blockDegree 5 p = 0 then 1 else 0) +
        (if S.blockDegree 5 p = 1 then 1 else 0) +
        (if S.blockDegree 5 p = 2 then 1 else 0) +
        (if S.blockDegree 5 p = 3 then 1 else 0) +
        (if S.blockDegree 5 p = 4 then 1 else 0) = 1 := by
    rcases hdegree p with h0 | h1 | h2 | h3 | h4
    · norm_num [h0]
    · norm_num [h1]
    · norm_num [h2]
    · norm_num [h3]
    · norm_num [h4]
  have hincPoint (p : Point) : S.blockDegree 5 p =
      (if S.blockDegree 5 p = 1 then 1 else 0) +
        2 * (if S.blockDegree 5 p = 2 then 1 else 0) +
        3 * (if S.blockDegree 5 p = 3 then 1 else 0) +
        4 * (if S.blockDegree 5 p = 4 then 1 else 0) := by
    rcases hdegree p with h0 | h1 | h2 | h3 | h4
    · norm_num [h0]
    · norm_num [h1]
    · norm_num [h2]
    · norm_num [h3]
    · norm_num [h4]
  have hmomentPoint (p : Point) :
      Nat.choose (S.blockDegree 5 p) 2 =
        (if S.blockDegree 5 p = 2 then 1 else 0) +
          3 * (if S.blockDegree 5 p = 3 then 1 else 0) +
          6 * (if S.blockDegree 5 p = 4 then 1 else 0) := by
    rcases hdegree p with h0 | h1 | h2 | h3 | h4
    · norm_num [h0, Nat.choose]
    · norm_num [h1, Nat.choose]
    · norm_num [h2, Nat.choose]
    · norm_num [h3, Nat.choose]
    · norm_num [h4, Nat.choose]
  have hpoints :
      count 0 + count 1 + count 2 + count 3 + count 4 = 11 := by
    calc
      count 0 + count 1 + count 2 + count 3 + count 4 =
          (∑ p : Point, if S.blockDegree 5 p = 0 then 1 else 0) +
          (∑ p : Point, if S.blockDegree 5 p = 1 then 1 else 0) +
          (∑ p : Point, if S.blockDegree 5 p = 2 then 1 else 0) +
          (∑ p : Point, if S.blockDegree 5 p = 3 then 1 else 0) +
          (∑ p : Point, if S.blockDegree 5 p = 4 then 1 else 0) := by
        rw [hcount 0, hcount 1, hcount 2, hcount 3, hcount 4]
      _ = ∑ p : Point,
          ((if S.blockDegree 5 p = 0 then 1 else 0) +
            (if S.blockDegree 5 p = 1 then 1 else 0) +
            (if S.blockDegree 5 p = 2 then 1 else 0) +
            (if S.blockDegree 5 p = 3 then 1 else 0) +
            (if S.blockDegree 5 p = 4 then 1 else 0)) := by
        simp only [Finset.sum_add_distrib]
      _ = ∑ _p : Point, 1 := by
        apply Finset.sum_congr rfl
        intro p _hp
        exact hpartitionPoint p
      _ = 11 := by simp [hcard]
  have hincidence :
      count 1 + 2 * count 2 + 3 * count 3 + 4 * count 4 = 35 := by
    calc
      count 1 + 2 * count 2 + 3 * count 3 + 4 * count 4 =
          (∑ p : Point, if S.blockDegree 5 p = 1 then 1 else 0) +
          2 * (∑ p : Point, if S.blockDegree 5 p = 2 then 1 else 0) +
          3 * (∑ p : Point, if S.blockDegree 5 p = 3 then 1 else 0) +
          4 * (∑ p : Point, if S.blockDegree 5 p = 4 then 1 else 0) := by
        rw [hcount 1, hcount 2, hcount 3, hcount 4]
      _ = ∑ p : Point,
          ((if S.blockDegree 5 p = 1 then 1 else 0) +
            2 * (if S.blockDegree 5 p = 2 then 1 else 0) +
            3 * (if S.blockDegree 5 p = 3 then 1 else 0) +
            4 * (if S.blockDegree 5 p = 4 then 1 else 0)) := by
        simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
      _ = ∑ p : Point, S.blockDegree 5 p := by
        apply Finset.sum_congr rfl
        intro p _hp
        exact (hincPoint p).symm
      _ = 35 := by rw [hglobal.fiveIncidence, hfive]
  have hmomentRow : count 2 + 3 * count 3 + 6 * count 4 = 41 := by
    calc
      count 2 + 3 * count 3 + 6 * count 4 =
          (∑ p : Point, if S.blockDegree 5 p = 2 then 1 else 0) +
          3 * (∑ p : Point, if S.blockDegree 5 p = 3 then 1 else 0) +
          6 * (∑ p : Point, if S.blockDegree 5 p = 4 then 1 else 0) := by
        rw [hcount 2, hcount 3, hcount 4]
      _ = ∑ p : Point,
          ((if S.blockDegree 5 p = 2 then 1 else 0) +
            3 * (if S.blockDegree 5 p = 3 then 1 else 0) +
            6 * (if S.blockDegree 5 p = 4 then 1 else 0)) := by
        simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
      _ = ∑ p : Point, Nat.choose (S.blockDegree 5 p) 2 := by
        apply Finset.sum_congr rfl
        intro p _hp
        exact (hmomentPoint p).symm
      _ = 41 := by simpa [elevenFiveSecondMoment] using hmoment
  have hfour : count 4 = 4 := by omega
  simpa [count] using hfour

/-- Moment 41 improves the general mixed bound by three: only four points
can have five-degree four, so one unit of the three-degree excess must be
paid at five-degree at most three. -/
theorem elevenFive_c40_l14_b5_seven_secondMoment_fortyOne_weighted_le_315
    {Point : Type u} {Block : Type v} [Fintype Point] [Fintype Block]
    [DecidableEq Point]
    (S : BlockSystem Point Block) (hcard : Fintype.card Point = 11)
    (hlocal : ∀ p : Point, ElevenFiveLocalRows S p)
    (hglobal : ElevenFiveGlobalRows S)
    (hC : S.totalCircleCount = 40)
    (hL : elevenFiveLineTotal S = 14)
    (hfive : S.blockCount 5 = 7)
    (hmoment : elevenFiveSecondMoment S = 41) :
    (∑ p : Point, S.blockDegree 3 p * S.blockDegree 5 p) ≤ 315 := by
  classical
  obtain ⟨_hN6, hN9N12, hvalues⟩ :=
    elevenFive_c40_l14_b5_seven_threeDegree_census
      S hcard hlocal hglobal hC hL hfive
  have hfour :=
    elevenFive_c40_l14_b5_seven_secondMoment_fortyOne_degreeFour_card
      S hcard hlocal hglobal hfive hmoment
  have hcount9 :
      (∑ p : Point, if S.blockDegree 3 p = 9 then 1 else 0) =
        ((Finset.univ : Finset Point).filter fun p =>
          S.blockDegree 3 p = 9).card := by simp
  have hcount12 :
      (∑ p : Point, if S.blockDegree 3 p = 12 then 1 else 0) =
        ((Finset.univ : Finset Point).filter fun p =>
          S.blockDegree 3 p = 12).card := by simp
  have hcount4 :
      (∑ p : Point, if S.blockDegree 5 p = 4 then 1 else 0) =
        ((Finset.univ : Finset Point).filter fun p =>
          S.blockDegree 5 p = 4).card := by simp
  have hpointBound (p : Point) :
      S.blockDegree 3 p * S.blockDegree 5 p ≤
        6 * S.blockDegree 5 p +
          9 * (if S.blockDegree 3 p = 9 then 1 else 0) +
          18 * (if S.blockDegree 3 p = 12 then 1 else 0) +
          6 * (if S.blockDegree 5 p = 4 then 1 else 0) := by
    have hcap := (hlocal p).fiveDegreeCap
    rcases hvalues p with h6 | h9 | h12
    · simp [h6]
    · by_cases h4 : S.blockDegree 5 p = 4
      · simp [h9, h4]
      · simp [h9, h4]
        omega
    · by_cases h4 : S.blockDegree 5 p = 4
      · simp [h12, h4]
      · simp [h12, h4]
        omega
  have hsum := Finset.sum_le_sum
    (s := (Finset.univ : Finset Point)) fun p _hp => hpointBound p
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at hsum
  rw [hglobal.fiveIncidence, hfive, hcount9, hcount12, hcount4,
    hfour] at hsum
  omega

/-- A singleton pair consumes the unique defect in moment 41; every other
pair in the seven-block family is double. -/
private theorem c40FourteenSeven_inter_card_eq_two_of_secondMoment_fortyOne
    {Point : Type u} {Block : Type v} [Fintype Point] [Fintype Block]
    [DecidableEq Point] [DecidableEq Block]
    (S : BlockSystem Point Block) (hfive : S.blockCount 5 = 7)
    (hmoment : elevenFiveSecondMoment S = 41)
    {f g : Block} (hf : f ∈ S.blocksOfSize 5)
    (hg : g ∈ S.blocksOfSize 5) (hfg : f ≠ g)
    (hsingle : (S.support f ∩ S.support g).card = 1) :
    ∀ b ∈ S.blocksOfSize 5, ∀ c ∈ S.blocksOfSize 5,
      b ≠ c → ({b, c} : Finset Block) ≠ ({f, g} : Finset Block) →
        (S.support b ∩ S.support c).card = 2 := by
  classical
  let F := S.blocksOfSize 5
  let Q := F.powersetCard 2
  let q : Finset Block → ℕ := fun A => (S.commonSupport A).card
  have hFcard : F.card = 7 := by
    simpa [F, BlockSystem.blockCount] using hfive
  have hQcard : Q.card = 21 := by simp [Q, hFcard, Nat.choose]
  have hpairTotal : (∑ A ∈ Q, q A) = 41 := by
    change (∑ A ∈ F.powersetCard 2, (S.commonSupport A).card) = 41
    rw [← S.binomial_degree_moment F 2]
    simpa [F, BlockSystem.blockDegree, elevenFiveSecondMoment] using hmoment
  have hspecial : ({f, g} : Finset Block) ∈ Q := by
    change ({f, g} : Finset Block) ∈ F.powersetCard 2
    refine Finset.mem_powersetCard.mpr ⟨?_, ?_⟩
    · intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact hf
      · exact hg
    · simp [hfg]
  have hone : q ({f, g} : Finset Block) = 1 := by
    dsimp [q]
    rw [S.commonSupport_pair]
    exact hsingle
  have hrestCard : (Q.erase ({f, g} : Finset Block)).card = 20 := by
    rw [Finset.card_erase_of_mem hspecial, hQcard]
  have hsplit := Finset.sum_erase_add Q q hspecial
  have hrestSum :
      (∑ A ∈ Q.erase ({f, g} : Finset Block), q A) = 40 := by
    rw [hone, hpairTotal] at hsplit
    omega
  have htermLe (A : Finset Block)
      (hA : A ∈ Q.erase ({f, g} : Finset Block)) : q A ≤ 2 := by
    dsimp [q]
    apply S.commonSupport_card_le_two
    have hAQ : A ∈ Q := Finset.mem_of_mem_erase hA
    have hAF : A ∈ F.powersetCard 2 := by simpa [Q] using hAQ
    exact (Finset.mem_powersetCard.mp hAF).2
  have hrestConst :
      (∑ _A ∈ Q.erase ({f, g} : Finset Block), 2) = 40 := by
    simp [hrestCard]
  have hall := (Finset.sum_eq_sum_iff_of_le htermLe).mp
    (hrestSum.trans hrestConst.symm)
  intro b hb c hc hbc hpairNe
  have hbcMem : ({b, c} : Finset Block) ∈
      Q.erase ({f, g} : Finset Block) := by
    refine Finset.mem_erase.mpr ⟨hpairNe, ?_⟩
    change ({b, c} : Finset Block) ∈ F.powersetCard 2
    refine Finset.mem_powersetCard.mpr ⟨?_, ?_⟩
    · intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact hb
      · exact hc
    · simp [hbc]
  have hterm := hall {b, c} hbcMem
  simpa [q, S.commonSupport_pair] using hterm

/-- Moment 41 is also impossible.  Away from its unique singleton pair the
five remaining blocks are clean.  Either one has mass at most 47 and enters
the page-cap endpoint, or all five have mass at least 48.  Sharp weighted
mass `≤315` then forces equality at the singleton carrier, in particular
`d₃=6`; the existing unconditional `(6,2)/(6,3)` singleton dispatcher closes
that equality case. -/
theorem elevenFive_c40_l14_b5_seven_secondMoment_fortyOne_impossible
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    (cfg : Configuration Point)
    (hpoint : Fintype.card Point = 11)
    (hcap : BlockSizeCap (blockSystem cfg) 5)
    (hlocal : ∀ p : Point, ElevenFiveLocalRows (blockSystem cfg) p)
    (hglobal : ElevenFiveGlobalRows (blockSystem cfg))
    (hC : (blockSystem cfg).totalCircleCount = 40)
    (hL : elevenFiveLineTotal (blockSystem cfg) = 14)
    (hfive : (blockSystem cfg).blockCount 5 = 7)
    (hmoment : elevenFiveSecondMoment (blockSystem cfg) = 41) : False := by
  classical
  let S := blockSystem cfg
  let F := S.blocksOfSize 5
  let mass : GeometricBlock cfg → ℕ := fun b =>
    ∑ p ∈ S.support b, S.blockDegree 3 p
  have hodd : Odd (∑ p : Point, Nat.choose (S.blockDegree 5 p) 2) := by
    change Odd (elevenFiveSecondMoment S)
    rw [show elevenFiveSecondMoment S = 41 by simpa [S] using hmoment]
    norm_num
  obtain ⟨f, hf, g, hg, hfg, hsingle⟩ :=
    fiveBlock_singleton_of_odd_secondMoment S hodd
  have hfF : f ∈ F := by simpa [F] using hf
  have hgF : g ∈ F := by simpa [F] using hg
  have hFcard : F.card = 7 := by
    simpa [F, S, BlockSystem.blockCount] using hfive
  have hgfMem : g ∈ F.erase f := Finset.mem_erase.mpr ⟨hfg.symm, hgF⟩
  let R := (F.erase f).erase g
  have hRcard : R.card = 5 := by
    dsimp [R]
    rw [Finset.card_erase_of_mem hgfMem,
      Finset.card_erase_of_mem hfF, hFcard]
  have hRspec (b : GeometricBlock cfg) (hb : b ∈ R) :
      b ∈ S.blocksOfSize 5 ∧ b ≠ f ∧ b ≠ g := by
    have hbg := Finset.mem_erase.mp hb
    have hbf := Finset.mem_erase.mp hbg.2
    exact ⟨by simpa [F] using hbf.2, hbf.1, hbg.1⟩
  have hother := c40FourteenSeven_inter_card_eq_two_of_secondMoment_fortyOne
    S (by simpa [S] using hfive) (by simpa [S] using hmoment)
      hf hg hfg hsingle
  have hpairNe (b : GeometricBlock cfg) (hb : b ∈ R)
      (c : GeometricBlock cfg) :
      ({b, c} : Finset (GeometricBlock cfg)) ≠ {f, g} := by
    intro hpair
    have hbFG : b ∈ ({f, g} : Finset (GeometricBlock cfg)) := by
      rw [← hpair]
      simp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hbFG
    rcases hbFG with hbf | hbg
    · exact (hRspec b hb).2.1 hbf
    · exact (hRspec b hb).2.2 hbg
  have hweighted :=
    elevenFive_c40_l14_b5_seven_secondMoment_fortyOne_weighted_le_315
      S hpoint (by simpa [S] using hlocal) (by simpa [S] using hglobal)
        (by simpa [S] using hC) (by simpa [S] using hL)
          (by simpa [S] using hfive) (by simpa [S] using hmoment)
  have hmassTotal : (∑ b ∈ F, mass b) ≤ 315 := by
    have hfubini := elevenFive_fiveBlock_threeMass_sum_eq_weighted S
    simpa [F, mass] using hfubini.trans_le hweighted
  have hlineFive := c40FourteenSeven_lineCount_five_eq_zero
    S (by simpa [S] using hglobal) (by simpa [S] using hC)
      (by simpa [S] using hL) (by simpa [S] using hfive)
  have hpage (b : GeometricBlock cfg) (hbR : b ∈ R)
      (hbLow : mass b ≤ 47) : False := by
    rcases b with L | Gamma
    · have hbLine : (Sum.inl L : GeometricBlock cfg) ∈
          S.lineBlocksOfSize 5 := by
        apply S.mem_blocksOfKindSize.mpr
        refine ⟨?_, S.mem_blocksOfSize.mp (hRspec (Sum.inl L) hbR).1⟩
        simp [S, blockSystem, geometricBlockSystem, geometricBlockKind]
      have hlineCard : (S.lineBlocksOfSize 5).card = 0 := by
        simpa [BlockSystem.lineCount] using hlineFive
      have hpositive := Finset.card_pos.mpr ⟨Sum.inl L, hbLine⟩
      omega
    · have hb : (Sum.inr Gamma : GeometricBlock cfg) ∈ S.blocksOfSize 5 :=
        (hRspec (Sum.inr Gamma) hbR).1
      have hD : (circleTrace cfg Gamma.1).card = 5 := by
        have hsize := S.mem_blocksOfSize.mp hb
        simpa [S, blockSystem, geometricBlockSystem,
          geometricBlockSupport] using hsize
      have hallAt : ∀ c ∈ (blockSystem cfg).blocksOfSize 5,
          c ≠ (Sum.inr Gamma : GeometricBlock cfg) →
            ((blockSystem cfg).support (Sum.inr Gamma) ∩
              (blockSystem cfg).support c).card = 2 := by
        intro c hc hcb
        exact hother (Sum.inr Gamma) hb c (by simpa [S] using hc) hcb.symm
          (hpairNe (Sum.inr Gamma) hbR c)
      have hmass :
          (∑ p ∈ circleTrace cfg Gamma.1,
            (blockSystem cfg).blockDegree 3 p) ≤ 47 := by
        simpa [mass, S, blockSystem, geometricBlockSystem,
          geometricBlockSupport] using hbLow
      exact
        elevenFive_c40_l14_b5_seven_doubleNeighbourCircle_impossible_of_pageCap
          cfg Gamma hpoint hcap hlocal hD hfive hallAt (by omega)
  by_cases hlow : ∃ b ∈ R, mass b ≤ 47
  · obtain ⟨b, hbR, hbLow⟩ := hlow
    exact hpage b hbR hbLow
  · push_neg at hlow
    have hRmassLower : 240 ≤ ∑ b ∈ R, mass b := by
      have hlower : (∑ _b ∈ R, 48) ≤ ∑ b ∈ R, mass b := by
        apply Finset.sum_le_sum
        intro b hb
        have hbHigh := hlow b hb
        omega
      have hconstant : (∑ _b ∈ R, 48) = 240 := by simp [hRcard]
      omega
    have hsplitF := Finset.sum_erase_add F mass hfF
    have hsplitG := Finset.sum_erase_add (F.erase f) mass hgfMem
    have hmassDecomp :
        (∑ b ∈ F, mass b) = ((∑ b ∈ R, mass b) + mass g) + mass f := by
      calc
        (∑ b ∈ F, mass b) = (∑ b ∈ F.erase f, mass b) + mass f :=
          hsplitF.symm
        _ = ((∑ b ∈ R, mass b) + mass g) + mass f := by
          dsimp [R]
          rw [hsplitG.symm]
    have hendpointUpper : mass f + mass g ≤ 75 := by omega

    let I := S.support f ∩ S.support g
    let V := S.support f ∪ S.support g
    have hIcard : I.card = 1 := by simpa [I] using hsingle
    obtain ⟨p, hIeq⟩ := Finset.card_eq_one.mp hIcard
    have hpI : p ∈ I := by rw [hIeq]; simp
    have hpParts : p ∈ S.support f ∧ p ∈ S.support g := by
      simpa [I] using Finset.mem_inter.mp (by simpa [I] using hpI)
    have hVcard : V.card = 9 := by
      have hformula :=
        Finset.card_union_add_card_inter (S.support f) (S.support g)
      have hfSize := S.mem_blocksOfSize.mp hf
      have hgSize := S.mem_blocksOfSize.mp hg
      change V.card + I.card =
        (S.support f).card + (S.support g).card at hformula
      rw [hfSize, hgSize, hIcard] at hformula
      omega
    have hcomplCard : ((Finset.univ : Finset Point) \ V).card = 2 := by
      rw [Finset.card_sdiff_of_subset (Finset.subset_univ V),
        Finset.card_univ, hpoint, hVcard]
    have hcomplLe :
        (∑ q ∈ (Finset.univ : Finset Point) \ V,
          S.blockDegree 3 q) ≤ 24 := by
      calc
        (∑ q ∈ (Finset.univ : Finset Point) \ V,
            S.blockDegree 3 q) ≤
            ∑ _q ∈ (Finset.univ : Finset Point) \ V, 12 := by
          apply Finset.sum_le_sum
          intro q _hq
          rcases elevenFive_c40_threeDegree_values S q (hlocal q)
            (by simpa [S] using hC) with h6 | h9 | h12
          · omega
          · omega
          · omega
        _ = 24 := by simp [hcomplCard]
    have hthreeSum : (∑ q : Point, S.blockDegree 3 q) = 93 := by
      obtain ⟨hthreeCount, _hfourCount⟩ :=
        elevenFive_c40_l14_b5_seven_block_census
          S (by simpa [S] using hglobal) (by simpa [S] using hC)
            (by simpa [S] using hL) (by simpa [S] using hfive)
      rw [hglobal.threeIncidence, hthreeCount]
    have hpointSplit :
        (∑ q ∈ (Finset.univ : Finset Point) \ V,
            S.blockDegree 3 q) +
          (∑ q ∈ V, S.blockDegree 3 q) =
            ∑ q : Point, S.blockDegree 3 q :=
      Finset.sum_sdiff (Finset.subset_univ V)
    have hVlower : 69 ≤ ∑ q ∈ V, S.blockDegree 3 q := by
      rw [hthreeSum] at hpointSplit
      omega
    have hfIndicator : mass f = ∑ q : Point,
        if q ∈ S.support f then S.blockDegree 3 q else 0 := by
      simp [mass]
    have hgIndicator : mass g = ∑ q : Point,
        if q ∈ S.support g then S.blockDegree 3 q else 0 := by
      simp [mass]
    have hmassIdentity :
        mass f + mass g =
          (∑ q ∈ V, S.blockDegree 3 q) +
            (∑ q ∈ I, S.blockDegree 3 q) := by
      calc
        mass f + mass g =
            (∑ q : Point,
              if q ∈ S.support f then S.blockDegree 3 q else 0) +
            (∑ q : Point,
              if q ∈ S.support g then S.blockDegree 3 q else 0) := by
          rw [hfIndicator, hgIndicator]
        _ = ∑ q : Point,
            ((if q ∈ S.support f then S.blockDegree 3 q else 0) +
              (if q ∈ S.support g then S.blockDegree 3 q else 0)) := by
          rw [Finset.sum_add_distrib]
        _ = ∑ q : Point,
            ((if q ∈ V then S.blockDegree 3 q else 0) +
              (if q ∈ I then S.blockDegree 3 q else 0)) := by
          apply Finset.sum_congr rfl
          intro q _hq
          by_cases hqf : q ∈ S.support f <;>
            by_cases hqg : q ∈ S.support g <;>
              simp [V, I, hqf, hqg]
        _ = (∑ q : Point, if q ∈ V then S.blockDegree 3 q else 0) +
            (∑ q : Point, if q ∈ I then S.blockDegree 3 q else 0) := by
          rw [Finset.sum_add_distrib]
        _ = (∑ q ∈ V, S.blockDegree 3 q) +
            (∑ q ∈ I, S.blockDegree 3 q) := by simp
    have hIsum : (∑ q ∈ I, S.blockDegree 3 q) = S.blockDegree 3 p := by
      rw [hIeq]
      simp
    have hpThreeLower : 6 ≤ S.blockDegree 3 p := by
      rcases elevenFive_c40_threeDegree_values S p (hlocal p)
        (by simpa [S] using hC) with h6 | h9 | h12 <;> omega
    have hpThree : S.blockDegree 3 p = 6 := by
      rw [hIsum] at hmassIdentity
      omega
    have hfCfg : f ∈ (blockSystem cfg).blocksOfSize 5 := by simpa [S] using hf
    have hgCfg : g ∈ (blockSystem cfg).blocksOfSize 5 := by simpa [S] using hg
    have hpfGeo : p ∈ geometricBlockSupport cfg f := by
      simpa [S, blockSystem, geometricBlockSystem,
        geometricBlockSupport] using hpParts.1
    have hpgGeo : p ∈ geometricBlockSupport cfg g := by
      simpa [S, blockSystem, geometricBlockSystem,
        geometricBlockSupport] using hpParts.2
    have hsingleGeo :
        (geometricBlockSupport cfg f ∩ geometricBlockSupport cfg g).card = 1 := by
      simpa [S, blockSystem, geometricBlockSystem,
        geometricBlockSupport] using hsingle
    have htwo : 2 ≤ S.blockDegree 5 p :=
      two_le_blockDegree_five_of_two_blocks S p hf hg hpParts.1 hpParts.2 hfg
    have hlanger := (hlocal p).langer
    have hfiveCap := (hlocal p).fiveDegreeCap
    change 2 * S.blockDegree 5 p ≤ S.blockDegree 3 p + 1 at hlanger
    change S.blockDegree 5 p ≤ 4 at hfiveCap
    have hfiveCases : S.blockDegree 5 p = 2 ∨ S.blockDegree 5 p = 3 := by
      omega
    have hprofile :
        ((blockSystem cfg).blockDegree 3 p = 6 ∧
          (blockSystem cfg).blockDegree 5 p = 2) ∨
        ((blockSystem cfg).blockDegree 3 p = 6 ∧
          (blockSystem cfg).blockDegree 5 p = 3) ∨
        (blockSystem cfg).blockDegree 5 p = 4 := by
      rcases hfiveCases with htwo' | hthree'
      · exact Or.inl ⟨by simpa [S] using hpThree, by simpa [S] using htwo'⟩
      · exact Or.inr (Or.inl
          ⟨by simpa [S] using hpThree, by simpa [S] using hthree'⟩)
    exact elevenFive_c40_singleton_impossible_of_common_profiles
      cfg hpoint p (hlocal p) hfCfg hgCfg hpfGeo hpgGeo hfg
        hsingleGeo hprofile

/-! ## Exact residual singleton seam -/

/-- Degree-count notation for the remaining two moment profiles. -/
noncomputable def elevenFiveC40FourteenSevenDegreeCount
    {Point : Type u} {Block : Type v} [Fintype Point] [Fintype Block]
    [DecidableEq Point]
    (S : BlockSystem Point Block) (d : ℕ) : ℕ :=
  ((Finset.univ : Finset Point).filter fun p =>
    S.blockDegree 5 p = d).card

/-- Point count, five-incidence and pair-moment in literal degree
coordinates `n₀,...,n₄` for a seven-five-block family on eleven points. -/
theorem elevenFive_c40_l14_b5_seven_degree_count_rows
    {Point : Type u} {Block : Type v} [Fintype Point] [Fintype Block]
    [DecidableEq Point]
    (S : BlockSystem Point Block) (hcard : Fintype.card Point = 11)
    (hlocal : ∀ p : Point, ElevenFiveLocalRows S p)
    (hglobal : ElevenFiveGlobalRows S)
    (hfive : S.blockCount 5 = 7) :
    elevenFiveC40FourteenSevenDegreeCount S 0 +
        elevenFiveC40FourteenSevenDegreeCount S 1 +
        elevenFiveC40FourteenSevenDegreeCount S 2 +
        elevenFiveC40FourteenSevenDegreeCount S 3 +
        elevenFiveC40FourteenSevenDegreeCount S 4 = 11 ∧
      elevenFiveC40FourteenSevenDegreeCount S 1 +
        2 * elevenFiveC40FourteenSevenDegreeCount S 2 +
        3 * elevenFiveC40FourteenSevenDegreeCount S 3 +
        4 * elevenFiveC40FourteenSevenDegreeCount S 4 = 35 ∧
      elevenFiveSecondMoment S =
        elevenFiveC40FourteenSevenDegreeCount S 2 +
          3 * elevenFiveC40FourteenSevenDegreeCount S 3 +
          6 * elevenFiveC40FourteenSevenDegreeCount S 4 := by
  classical
  let count := elevenFiveC40FourteenSevenDegreeCount S
  have hdegree (p : Point) : S.blockDegree 5 p = 0 ∨
      S.blockDegree 5 p = 1 ∨ S.blockDegree 5 p = 2 ∨
        S.blockDegree 5 p = 3 ∨ S.blockDegree 5 p = 4 := by
    have hcap := (hlocal p).fiveDegreeCap
    omega
  have hcount (d : ℕ) :
      (∑ p : Point, if S.blockDegree 5 p = d then 1 else 0) = count d := by
    simp [count, elevenFiveC40FourteenSevenDegreeCount]
  have hpartitionPoint (p : Point) :
      (if S.blockDegree 5 p = 0 then 1 else 0) +
        (if S.blockDegree 5 p = 1 then 1 else 0) +
        (if S.blockDegree 5 p = 2 then 1 else 0) +
        (if S.blockDegree 5 p = 3 then 1 else 0) +
        (if S.blockDegree 5 p = 4 then 1 else 0) = 1 := by
    rcases hdegree p with h0 | h1 | h2 | h3 | h4
    · norm_num [h0]
    · norm_num [h1]
    · norm_num [h2]
    · norm_num [h3]
    · norm_num [h4]
  have hincPoint (p : Point) : S.blockDegree 5 p =
      (if S.blockDegree 5 p = 1 then 1 else 0) +
        2 * (if S.blockDegree 5 p = 2 then 1 else 0) +
        3 * (if S.blockDegree 5 p = 3 then 1 else 0) +
        4 * (if S.blockDegree 5 p = 4 then 1 else 0) := by
    rcases hdegree p with h0 | h1 | h2 | h3 | h4
    · norm_num [h0]
    · norm_num [h1]
    · norm_num [h2]
    · norm_num [h3]
    · norm_num [h4]
  have hmomentPoint (p : Point) :
      Nat.choose (S.blockDegree 5 p) 2 =
        (if S.blockDegree 5 p = 2 then 1 else 0) +
          3 * (if S.blockDegree 5 p = 3 then 1 else 0) +
          6 * (if S.blockDegree 5 p = 4 then 1 else 0) := by
    rcases hdegree p with h0 | h1 | h2 | h3 | h4
    · norm_num [h0, Nat.choose]
    · norm_num [h1, Nat.choose]
    · norm_num [h2, Nat.choose]
    · norm_num [h3, Nat.choose]
    · norm_num [h4, Nat.choose]
  change count 0 + count 1 + count 2 + count 3 + count 4 = 11 ∧
    count 1 + 2 * count 2 + 3 * count 3 + 4 * count 4 = 35 ∧
      elevenFiveSecondMoment S = count 2 + 3 * count 3 + 6 * count 4
  constructor
  · calc
      count 0 + count 1 + count 2 + count 3 + count 4 =
          (∑ p : Point, if S.blockDegree 5 p = 0 then 1 else 0) +
          (∑ p : Point, if S.blockDegree 5 p = 1 then 1 else 0) +
          (∑ p : Point, if S.blockDegree 5 p = 2 then 1 else 0) +
          (∑ p : Point, if S.blockDegree 5 p = 3 then 1 else 0) +
          (∑ p : Point, if S.blockDegree 5 p = 4 then 1 else 0) := by
        rw [hcount 0, hcount 1, hcount 2, hcount 3, hcount 4]
      _ = ∑ p : Point,
          ((if S.blockDegree 5 p = 0 then 1 else 0) +
            (if S.blockDegree 5 p = 1 then 1 else 0) +
            (if S.blockDegree 5 p = 2 then 1 else 0) +
            (if S.blockDegree 5 p = 3 then 1 else 0) +
            (if S.blockDegree 5 p = 4 then 1 else 0)) := by
        simp only [Finset.sum_add_distrib]
      _ = ∑ _p : Point, 1 := by
        apply Finset.sum_congr rfl
        intro p _hp
        exact hpartitionPoint p
      _ = 11 := by simp [hcard]
  · constructor
    · calc
        count 1 + 2 * count 2 + 3 * count 3 + 4 * count 4 =
            (∑ p : Point, if S.blockDegree 5 p = 1 then 1 else 0) +
            2 * (∑ p : Point, if S.blockDegree 5 p = 2 then 1 else 0) +
            3 * (∑ p : Point, if S.blockDegree 5 p = 3 then 1 else 0) +
            4 * (∑ p : Point, if S.blockDegree 5 p = 4 then 1 else 0) := by
          rw [hcount 1, hcount 2, hcount 3, hcount 4]
        _ = ∑ p : Point,
            ((if S.blockDegree 5 p = 1 then 1 else 0) +
              2 * (if S.blockDegree 5 p = 2 then 1 else 0) +
              3 * (if S.blockDegree 5 p = 3 then 1 else 0) +
              4 * (if S.blockDegree 5 p = 4 then 1 else 0)) := by
          simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
        _ = ∑ p : Point, S.blockDegree 5 p := by
          apply Finset.sum_congr rfl
          intro p _hp
          exact (hincPoint p).symm
        _ = 35 := by rw [hglobal.fiveIncidence, hfive]
    · calc
        elevenFiveSecondMoment S =
            ∑ p : Point, Nat.choose (S.blockDegree 5 p) 2 := rfl
        _ = ∑ p : Point,
            ((if S.blockDegree 5 p = 2 then 1 else 0) +
              3 * (if S.blockDegree 5 p = 3 then 1 else 0) +
              6 * (if S.blockDegree 5 p = 4 then 1 else 0)) := by
          apply Finset.sum_congr rfl
          intro p _hp
          exact hmomentPoint p
        _ = (∑ p : Point, if S.blockDegree 5 p = 2 then 1 else 0) +
            3 * (∑ p : Point, if S.blockDegree 5 p = 3 then 1 else 0) +
            6 * (∑ p : Point, if S.blockDegree 5 p = 4 then 1 else 0) := by
          simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
        _ = count 2 + 3 * count 3 + 6 * count 4 := by
          rw [hcount 2, hcount 3, hcount 4]

/-- Literal five-degree profile in moment 39. -/
theorem elevenFive_c40_l14_b5_seven_secondMoment_thirtyNine_profile
    {Point : Type u} {Block : Type v} [Fintype Point] [Fintype Block]
    [DecidableEq Point]
    (S : BlockSystem Point Block) (hcard : Fintype.card Point = 11)
    (hlocal : ∀ p : Point, ElevenFiveLocalRows S p)
    (hglobal : ElevenFiveGlobalRows S) (hfive : S.blockCount 5 = 7)
    (hmoment : elevenFiveSecondMoment S = 39) :
    elevenFiveC40FourteenSevenDegreeCount S 4 = 2 ∧
      elevenFiveC40FourteenSevenDegreeCount S 3 = 9 ∧
      (∀ p : Point, S.blockDegree 5 p = 3 ∨ S.blockDegree 5 p = 4) := by
  classical
  obtain ⟨hpoints, hinc, hmomentRow⟩ :=
    elevenFive_c40_l14_b5_seven_degree_count_rows
      S hcard hlocal hglobal hfive
  rw [hmoment] at hmomentRow
  have hzero0 : elevenFiveC40FourteenSevenDegreeCount S 0 = 0 := by omega
  have hzero1 : elevenFiveC40FourteenSevenDegreeCount S 1 = 0 := by omega
  have hzero2 : elevenFiveC40FourteenSevenDegreeCount S 2 = 0 := by omega
  have hthree : elevenFiveC40FourteenSevenDegreeCount S 3 = 9 := by omega
  have hfour : elevenFiveC40FourteenSevenDegreeCount S 4 = 2 := by omega
  have hprofile (p : Point) : S.blockDegree 5 p = 3 ∨
      S.blockDegree 5 p = 4 := by
    have hcap := (hlocal p).fiveDegreeCap
    have hnot (d : ℕ)
        (hcount : elevenFiveC40FourteenSevenDegreeCount S d = 0)
        (hp : S.blockDegree 5 p = d) : False := by
      have hmem : p ∈ ((Finset.univ : Finset Point).filter fun q =>
          S.blockDegree 5 q = d) := by simp [hp]
      have hpos := Finset.card_pos.mpr ⟨p, hmem⟩
      change 0 < elevenFiveC40FourteenSevenDegreeCount S d at hpos
      rw [hcount] at hpos
      omega
    by_cases h0 : S.blockDegree 5 p = 0
    · exact False.elim (hnot 0 hzero0 h0)
    by_cases h1 : S.blockDegree 5 p = 1
    · exact False.elim (hnot 1 hzero1 h1)
    by_cases h2 : S.blockDegree 5 p = 2
    · exact False.elim (hnot 2 hzero2 h2)
    have : S.blockDegree 5 p = 3 ∨ S.blockDegree 5 p = 4 := by omega
    exact this
  exact ⟨hfour, hthree, hprofile⟩

/-- Literal five-degree profile in moment 40. -/
theorem elevenFive_c40_l14_b5_seven_secondMoment_forty_profile
    {Point : Type u} {Block : Type v} [Fintype Point] [Fintype Block]
    [DecidableEq Point]
    (S : BlockSystem Point Block) (hcard : Fintype.card Point = 11)
    (hlocal : ∀ p : Point, ElevenFiveLocalRows S p)
    (hglobal : ElevenFiveGlobalRows S) (hfive : S.blockCount 5 = 7)
    (hmoment : elevenFiveSecondMoment S = 40) :
    elevenFiveC40FourteenSevenDegreeCount S 4 = 3 ∧
      elevenFiveC40FourteenSevenDegreeCount S 3 = 7 ∧
      elevenFiveC40FourteenSevenDegreeCount S 2 = 1 ∧
      (∀ p : Point, S.blockDegree 5 p = 2 ∨
        S.blockDegree 5 p = 3 ∨ S.blockDegree 5 p = 4) := by
  classical
  obtain ⟨hpoints, hinc, hmomentRow⟩ :=
    elevenFive_c40_l14_b5_seven_degree_count_rows
      S hcard hlocal hglobal hfive
  rw [hmoment] at hmomentRow
  have hzero0 : elevenFiveC40FourteenSevenDegreeCount S 0 = 0 := by omega
  have hzero1 : elevenFiveC40FourteenSevenDegreeCount S 1 = 0 := by omega
  have htwo : elevenFiveC40FourteenSevenDegreeCount S 2 = 1 := by omega
  have hthree : elevenFiveC40FourteenSevenDegreeCount S 3 = 7 := by omega
  have hfour : elevenFiveC40FourteenSevenDegreeCount S 4 = 3 := by omega
  have hprofile (p : Point) : S.blockDegree 5 p = 2 ∨
      S.blockDegree 5 p = 3 ∨ S.blockDegree 5 p = 4 := by
    have hcap := (hlocal p).fiveDegreeCap
    have hnot (d : ℕ)
        (hcount : elevenFiveC40FourteenSevenDegreeCount S d = 0)
        (hp : S.blockDegree 5 p = d) : False := by
      have hmem : p ∈ ((Finset.univ : Finset Point).filter fun q =>
          S.blockDegree 5 q = d) := by simp [hp]
      have hpos := Finset.card_pos.mpr ⟨p, hmem⟩
      change 0 < elevenFiveC40FourteenSevenDegreeCount S d at hpos
      rw [hcount] at hpos
      omega
    by_cases h0 : S.blockDegree 5 p = 0
    · exact False.elim (hnot 0 hzero0 h0)
    by_cases h1 : S.blockDegree 5 p = 1
    · exact False.elim (hnot 1 hzero1 h1)
    omega
  exact ⟨hfour, hthree, htwo, hprofile⟩

/-! ## The remaining moment-40 defect -/

/-- With seven five-blocks, moment `40`, and no disjoint pair, exactly two
unordered pairs have singleton common support. -/
private theorem c40FourteenSeven_singleton_pair_family_card_two
    {Point : Type u} {Block : Type v} [Fintype Point] [Fintype Block]
    [DecidableEq Point] [DecidableEq Block]
    (S : BlockSystem Point Block)
    (hfive : S.blockCount 5 = 7)
    (hmoment : elevenFiveSecondMoment S = 40)
    (hnodisjoint : ∀ b ∈ S.blocksOfSize 5, ∀ c ∈ S.blocksOfSize 5,
      b ≠ c → (S.support b ∩ S.support c).card ≠ 0) :
    (((S.blocksOfSize 5).powersetCard 2).filter
        (fun A => (S.commonSupport A).card = 1)).card = 2 := by
  classical
  let F := S.blocksOfSize 5
  let Q := F.powersetCard 2
  let q : Finset Block → ℕ := fun A => (S.commonSupport A).card
  let O := Q.filter fun A => q A = 1
  have hFcard : F.card = 7 := by
    simpa [F, BlockSystem.blockCount] using hfive
  have hqsum : (∑ A ∈ Q, q A) = 40 := by
    have hmoment' : (∑ A ∈ Q, q A) = elevenFiveSecondMoment S := by
      change (∑ A ∈ F.powersetCard 2, (S.commonSupport A).card) =
        ∑ p : Point, Nat.choose (S.degreeIn F p) 2
      exact (S.binomial_degree_moment F 2).symm
    exact hmoment'.trans hmoment
  have hterm (A : Finset Block) (hA : A ∈ Q) :
      q A + (if q A = 1 then 1 else 0) = 2 := by
    have hAF : A ∈ F.powersetCard 2 := by simpa [Q] using hA
    have hqLe : q A ≤ 2 := by
      dsimp [q]
      exact S.commonSupport_card_le_two
        (Finset.mem_powersetCard.mp hAF).2
    obtain ⟨b, c, hbc, hAeq⟩ :=
      Finset.card_eq_two.mp (Finset.mem_powersetCard.mp hAF).2
    have hbF : b ∈ F :=
      (Finset.mem_powersetCard.mp hAF).1 (by simp [hAeq])
    have hcF : c ∈ F :=
      (Finset.mem_powersetCard.mp hAF).1 (by simp [hAeq])
    have hqNe : q A ≠ 0 := by
      dsimp [q]
      rw [hAeq, S.commonSupport_pair]
      exact hnodisjoint b (by simpa [F] using hbF)
        c (by simpa [F] using hcF) hbc
    by_cases hqOne : q A = 1
    · simp [hqOne]
    · have hqTwo : q A = 2 := by omega
      simp [hqTwo]
  have hsum :
      (∑ A ∈ Q, (q A + (if q A = 1 then 1 else 0))) =
        ∑ _A ∈ Q, 2 := by
    apply Finset.sum_congr rfl
    intro A hA
    exact hterm A hA
  have hleft :
      (∑ A ∈ Q, (q A + (if q A = 1 then 1 else 0))) =
        (∑ A ∈ Q, q A) + O.card := by
    rw [Finset.sum_add_distrib]
    congr 1
    rw [← Finset.sum_filter]
    simp [O]
  have hright : (∑ _A ∈ Q, 2) = 42 := by
    simp [Q, Finset.card_powersetCard, hFcard, Nat.choose]
  rw [hleft, hright, hqsum] at hsum
  have hOcard : O.card = 2 := by omega
  simpa [O, Q, q, F] using hOcard

/-- The sole local singleton profile not already excluded by the completed
two-base, K3.1 and four-star endpoints. -/
def ElevenFiveC40FourteenSevenTwelveThreeSingleton
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    (cfg : Configuration Point) : Prop :=
  ∃ p : Point, ∃ b c : GeometricBlock cfg,
    b ∈ (blockSystem cfg).blocksOfSize 5 ∧
    c ∈ (blockSystem cfg).blocksOfSize 5 ∧ b ≠ c ∧
    p ∈ geometricBlockSupport cfg b ∧
    p ∈ geometricBlockSupport cfg c ∧
    (geometricBlockSupport cfg b ∩ geometricBlockSupport cfg c).card = 1 ∧
    (blockSystem cfg).blockDegree 3 p = 12 ∧
    (blockSystem cfg).blockDegree 5 p = 3

/-- The lossless actual pivot-inversion data at the last local seam. -/
structure ElevenFiveC40FourteenSevenActualFiveTracePath
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    (cfg : Configuration Point) where
  pivot : Point
  left : GeometricBlock cfg
  right : GeometricBlock cfg
  left_five : left ∈ (blockSystem cfg).blocksOfSize 5
  right_five : right ∈ (blockSystem cfg).blocksOfSize 5
  left_ne_right : left ≠ right
  pivot_left : pivot ∈ geometricBlockSupport cfg left
  pivot_right : pivot ∈ geometricBlockSupport cfg right
  singleton : (geometricBlockSupport cfg left ∩
    geometricBlockSupport cfg right).card = 1
  three_degree : (blockSystem cfg).blockDegree 3 pivot = 12
  five_degree : (blockSystem cfg).blockDegree 5 pivot = 3
  three_line_count :
    (blockSystem (pivotInversion cfg pivot)).lineCount 3 = 5
  four_line_count :
    (blockSystem (pivotInversion cfg pivot)).lineCount 4 = 3
  connector : (blockSystem (pivotInversion cfg pivot)).LineBlock
  connector_four :
    ((blockSystem (pivotInversion cfg pivot)).support connector.1).card = 4
  connector_ne_left : connector.1 ≠ Sum.inl (blockToPivotLine cfg pivot
    (elevenFiveFivePivotBlock cfg pivot left left_five pivot_left))
  connector_ne_right : connector.1 ≠ Sum.inl (blockToPivotLine cfg pivot
    (elevenFiveFivePivotBlock cfg pivot right right_five pivot_right))
  connector_left_one :
    ((blockSystem (pivotInversion cfg pivot)).support connector.1 ∩
      lineSupport (pivotInversion cfg pivot)
        (blockToPivotLine cfg pivot
          (elevenFiveFivePivotBlock cfg pivot left left_five pivot_left))).card = 1
  connector_right_one :
    ((blockSystem (pivotInversion cfg pivot)).support connector.1 ∩
      lineSupport (pivotInversion cfg pivot)
        (blockToPivotLine cfg pivot
          (elevenFiveFivePivotBlock cfg pivot right right_five pivot_right))).card = 1

/-- A singleton carried at five-degree three must have three-degree twelve:
the degree-six and degree-nine K3.1 rows are already unconditional. -/
theorem elevenFive_c40_singleton_carrier_twelve_of_fiveDegree_three
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    (cfg : Configuration Point) (hpoint : Fintype.card Point = 11)
    (p : Point) (hlocal : ElevenFiveLocalRows (blockSystem cfg) p)
    (hC : (blockSystem cfg).totalCircleCount = 40)
    (hfive : (blockSystem cfg).blockDegree 5 p = 3)
    {b c : GeometricBlock cfg}
    (hb : b ∈ (blockSystem cfg).blocksOfSize 5)
    (hc : c ∈ (blockSystem cfg).blocksOfSize 5)
    (hbp : p ∈ geometricBlockSupport cfg b)
    (hcp : p ∈ geometricBlockSupport cfg c)
    (hbc : b ≠ c)
    (hsingle : (geometricBlockSupport cfg b ∩
      geometricBlockSupport cfg c).card = 1) :
    (blockSystem cfg).blockDegree 3 p = 12 := by
  rcases elevenFive_c40_threeDegree_values
    (blockSystem cfg) p hlocal hC with h6 | h9 | h12
  · exact False.elim (elevenFive_threeFive_six_singleton_impossible
      cfg hpoint p hlocal h6 hfive hb hc hbp hcp hbc hsingle)
  · exact False.elim (elevenFive_threeFive_nine_singleton_impossible
      cfg hpoint p hlocal h9 hfive hb hc hbp hcp hbc hsingle)
  · exact h12

/-- Exact pivot-inversion census at the surviving carrier.  It has three
four-point base lines and five three-point external traces; this is just
outside the existing K3.1 endpoints, which handle six or seven traces. -/
theorem elevenFive_c40_twelveThree_inverted_census
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    (cfg : Configuration Point) (p : Point)
    (hlocal : ElevenFiveLocalRows (blockSystem cfg) p)
    (hthree : (blockSystem cfg).blockDegree 3 p = 12)
    (hfive : (blockSystem cfg).blockDegree 5 p = 3) :
    (blockSystem (pivotInversion cfg p)).lineCount 3 = 5 ∧
      (blockSystem (pivotInversion cfg p)).lineCount 4 = 3 := by
  have hpair := hlocal.pairRow
  have hfour : (blockSystem cfg).blockDegree 4 p = 5 := by omega
  constructor
  · rw [← blockDegree_eq_lineCount_pivotInversion cfg p 4 (by omega)]
    exact hfour
  · rw [← blockDegree_eq_lineCount_pivotInversion cfg p 5 (by omega)]
    exact hfive

/-- The singleton seam produces the actual three-four-line path together
with its exact five-trace census. -/
noncomputable def elevenFive_c40_twelveThreeSingleton_actualFiveTracePath
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    (cfg : Configuration Point) (hpoint : Fintype.card Point = 11)
    (hlocal : ∀ p : Point, ElevenFiveLocalRows (blockSystem cfg) p)
    (hseam : ElevenFiveC40FourteenSevenTwelveThreeSingleton cfg) :
    ElevenFiveC40FourteenSevenActualFiveTracePath cfg := by
  classical
  let p := Classical.choose hseam
  have hp := Classical.choose_spec hseam
  let b := Classical.choose hp
  have hbRest := Classical.choose_spec hp
  let d := Classical.choose hbRest
  have hdata := Classical.choose_spec hbRest
  have hb := hdata.1
  have hd := hdata.2.1
  have hbd := hdata.2.2.1
  have hbp := hdata.2.2.2.1
  have hdp := hdata.2.2.2.2.1
  have hinter := hdata.2.2.2.2.2.1
  have hthree := hdata.2.2.2.2.2.2.1
  have hfive := hdata.2.2.2.2.2.2.2
  have hex := elevenFive_threeFive_singleton_inverted_path
    cfg hpoint p hfive hb hd hbp hdp hbd hinter
  let e := Classical.choose hex
  have he := Classical.choose_spec hex
  have hcensus := elevenFive_c40_twelveThree_inverted_census
    cfg p (hlocal p) hthree hfive
  exact
    { pivot := p
      left := b
      right := d
      left_five := hb
      right_five := hd
      left_ne_right := hbd
      pivot_left := hbp
      pivot_right := hdp
      singleton := hinter
      three_degree := hthree
      five_degree := hfive
      three_line_count := hcensus.1
      four_line_count := hcensus.2
      connector := e
      connector_four := he.1
      connector_ne_left := he.2.1
      connector_ne_right := he.2.2.1
      connector_left_one := he.2.2.2.1
      connector_right_one := he.2.2.2.2 }

/-- Classification of one singleton pair in the moment-40 profile.  The
only alternative to the target `(12,3)` seam is the unique degree-two
carrier. -/
private theorem c40FourteenSeven_singleton_pair_classify
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    (cfg : Configuration Point) (hpoint : Fintype.card Point = 11)
    (hlocal : ∀ p : Point, ElevenFiveLocalRows (blockSystem cfg) p)
    (hC : (blockSystem cfg).totalCircleCount = 40)
    (hprofile : ∀ p : Point,
      (blockSystem cfg).blockDegree 5 p = 2 ∨
      (blockSystem cfg).blockDegree 5 p = 3 ∨
      (blockSystem cfg).blockDegree 5 p = 4)
    (A : Finset (GeometricBlock cfg))
    (hA : A ∈ ((blockSystem cfg).blocksOfSize 5).powersetCard 2)
    (hsingle : ((blockSystem cfg).commonSupport A).card = 1) :
    ElevenFiveC40FourteenSevenTwelveThreeSingleton cfg ∨
      ∃ p : Point, p ∈ (blockSystem cfg).commonSupport A ∧
        (blockSystem cfg).blockDegree 5 p = 2 := by
  classical
  let S := blockSystem cfg
  have hAF : A ∈ (S.blocksOfSize 5).powersetCard 2 := by
    simpa [S] using hA
  obtain ⟨b, c, hbc, hAeq⟩ :=
    Finset.card_eq_two.mp (Finset.mem_powersetCard.mp hAF).2
  have hb : b ∈ S.blocksOfSize 5 :=
    (Finset.mem_powersetCard.mp hAF).1 (by simp [hAeq])
  have hc : c ∈ S.blocksOfSize 5 :=
    (Finset.mem_powersetCard.mp hAF).1 (by simp [hAeq])
  have hsingleS : (S.commonSupport A).card = 1 := by
    simpa [S] using hsingle
  obtain ⟨p, hpCommonEq⟩ := Finset.card_eq_one.mp hsingleS
  have hpCommon : p ∈ S.commonSupport A := by
    rw [hpCommonEq]
    simp
  have hpInter : p ∈ S.support b ∩ S.support c := by
    simpa [hAeq, S.commonSupport_pair] using hpCommon
  have hbpS := (Finset.mem_inter.mp hpInter).1
  have hcpS := (Finset.mem_inter.mp hpInter).2
  have hbCfg : b ∈ (blockSystem cfg).blocksOfSize 5 := by simpa [S] using hb
  have hcCfg : c ∈ (blockSystem cfg).blocksOfSize 5 := by simpa [S] using hc
  have hbp : p ∈ geometricBlockSupport cfg b := by
    simpa [S, blockSystem, geometricBlockSystem,
      geometricBlockSupport] using hbpS
  have hcp : p ∈ geometricBlockSupport cfg c := by
    simpa [S, blockSystem, geometricBlockSystem,
      geometricBlockSupport] using hcpS
  have hsinglePair : (S.support b ∩ S.support c).card = 1 := by
    simpa [hAeq, S.commonSupport_pair] using hsingleS
  have hsingleCfg :
      (geometricBlockSupport cfg b ∩ geometricBlockSupport cfg c).card = 1 := by
    simpa [S, blockSystem, geometricBlockSystem,
      geometricBlockSupport] using hsinglePair
  rcases hprofile p with hp2 | hp3 | hp4
  · exact Or.inr ⟨p, by simpa [S] using hpCommon, hp2⟩
  · have hp12 := elevenFive_c40_singleton_carrier_twelve_of_fiveDegree_three
      cfg hpoint p (hlocal p) hC hp3 hbCfg hcCfg hbp hcp hbc hsingleCfg
    exact Or.inl ⟨p, b, c, hbCfg, hcCfg, hbc, hbp, hcp,
      hsingleCfg, hp12, hp3⟩
  · exact False.elim
      (elevenFive_degreeFourPivot_fiveBlock_inter_card_ne_one
        cfg hpoint p hp4 hbCfg hcCfg hbp hcp hbc hsingleCfg)

/-- In the moment-40 degree profile there is only one degree-two point, and
its two incident five-blocks form only one unordered pair. -/
private theorem c40FourteenSeven_degreeTwo_pair_unique
    {Point : Type u} {Block : Type v} [Fintype Point] [Fintype Block]
    [DecidableEq Point] [DecidableEq Block]
    (S : BlockSystem Point Block)
    (htwo : elevenFiveC40FourteenSevenDegreeCount S 2 = 1)
    {A B : Finset Block}
    (hA : A ∈ (S.blocksOfSize 5).powersetCard 2)
    (hB : B ∈ (S.blocksOfSize 5).powersetCard 2)
    {p q : Point} (hpA : p ∈ S.commonSupport A)
    (hqB : q ∈ S.commonSupport B)
    (hpTwo : S.blockDegree 5 p = 2)
    (hqTwo : S.blockDegree 5 q = 2) : A = B := by
  classical
  let U := (Finset.univ : Finset Point).filter fun x =>
    S.blockDegree 5 x = 2
  have hUcard : U.card = 1 := by
    simpa [U, elevenFiveC40FourteenSevenDegreeCount] using htwo
  have hpU : p ∈ U := by simp [U, hpTwo]
  have hqU : q ∈ U := by simp [U, hqTwo]
  have hpq : p = q :=
    Finset.card_le_one.mp (by omega : U.card ≤ 1) p hpU q hqU
  subst q
  let T := (S.blocksOfSize 5).filter fun b => p ∈ S.support b
  have hTcard : T.card = 2 := by
    simpa [T, BlockSystem.blockDegree, BlockSystem.degreeIn] using hpTwo
  have hAsub : A ⊆ T := by
    intro b hb
    exact Finset.mem_filter.mpr
      ⟨(Finset.mem_powersetCard.mp hA).1 hb,
        (S.mem_commonSupport.mp hpA) b hb⟩
  have hBsub : B ⊆ T := by
    intro b hb
    exact Finset.mem_filter.mpr
      ⟨(Finset.mem_powersetCard.mp hB).1 hb,
        (S.mem_commonSupport.mp hqB) b hb⟩
  have hAcard : A.card = 2 := (Finset.mem_powersetCard.mp hA).2
  have hBcard : B.card = 2 := (Finset.mem_powersetCard.mp hB).2
  have hAT : A = T :=
    Finset.eq_of_subset_of_card_le hAsub (by omega)
  have hBT : B = T :=
    Finset.eq_of_subset_of_card_le hBsub (by omega)
  exact hAT.trans hBT.symm

/-- The entire moment-39 profile reduces to the exact `(d₃,d₅)=(12,3)`
singleton seam. -/
theorem elevenFive_c40_l14_b5_seven_secondMoment_thirtyNine_reaches_twelveThree
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    (cfg : Configuration Point)
    (hpoint : Fintype.card Point = 11)
    (hlocal : ∀ p : Point, ElevenFiveLocalRows (blockSystem cfg) p)
    (hglobal : ElevenFiveGlobalRows (blockSystem cfg))
    (hC : (blockSystem cfg).totalCircleCount = 40)
    (hfive : (blockSystem cfg).blockCount 5 = 7)
    (hmoment : elevenFiveSecondMoment (blockSystem cfg) = 39) :
    ElevenFiveC40FourteenSevenTwelveThreeSingleton cfg := by
  classical
  let S := blockSystem cfg
  have hodd : Odd (∑ p : Point, Nat.choose (S.blockDegree 5 p) 2) := by
    change Odd (elevenFiveSecondMoment S)
    rw [show elevenFiveSecondMoment S = 39 by simpa [S] using hmoment]
    norm_num
  obtain ⟨b, hb, c, hc, hbc, hsingle⟩ :=
    fiveBlock_singleton_of_odd_secondMoment S hodd
  obtain ⟨p, hpinter⟩ := Finset.card_eq_one.mp hsingle
  have hpMem : p ∈ S.support b ∩ S.support c := by
    rw [hpinter]
    simp
  have hbpS := (Finset.mem_inter.mp hpMem).1
  have hcpS := (Finset.mem_inter.mp hpMem).2
  have hbp : p ∈ geometricBlockSupport cfg b := by
    simpa [S, blockSystem, geometricBlockSystem,
      geometricBlockSupport] using hbpS
  have hcp : p ∈ geometricBlockSupport cfg c := by
    simpa [S, blockSystem, geometricBlockSystem,
      geometricBlockSupport] using hcpS
  have hbCfg : b ∈ (blockSystem cfg).blocksOfSize 5 := by simpa [S] using hb
  have hcCfg : c ∈ (blockSystem cfg).blocksOfSize 5 := by simpa [S] using hc
  have hsingleCfg :
      (geometricBlockSupport cfg b ∩ geometricBlockSupport cfg c).card = 1 := by
    simpa [S, blockSystem, geometricBlockSystem,
      geometricBlockSupport] using hsingle
  obtain ⟨_hfour, _hthree, hprofile⟩ :=
    elevenFive_c40_l14_b5_seven_secondMoment_thirtyNine_profile
      S hpoint (by simpa [S] using hlocal) (by simpa [S] using hglobal)
        (by simpa [S] using hfive) (by simpa [S] using hmoment)
  rcases hprofile p with hp3 | hp4
  · have hp12 :=
      elevenFive_c40_singleton_carrier_twelve_of_fiveDegree_three
        cfg hpoint p (hlocal p) hC (by simpa [S] using hp3)
          hbCfg hcCfg hbp hcp hbc hsingleCfg
    exact ⟨p, b, c, hbCfg, hcCfg, hbc, hbp, hcp, hsingleCfg,
      hp12, by simpa [S] using hp3⟩
  · exact False.elim
      (elevenFive_degreeFourPivot_fiveBlock_inter_card_ne_one
        cfg hpoint p (by simpa [S] using hp4) hbCfg hcCfg hbp hcp hbc
          hsingleCfg)

/-- In moment `40`, absence of a disjoint five-block pair again reduces the
whole profile to the same `(12,3)` singleton seam. -/
theorem elevenFive_c40_l14_b5_seven_secondMoment_forty_noDisjoint_reaches_twelveThree
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    (cfg : Configuration Point)
    (hpoint : Fintype.card Point = 11)
    (hlocal : ∀ p : Point, ElevenFiveLocalRows (blockSystem cfg) p)
    (hglobal : ElevenFiveGlobalRows (blockSystem cfg))
    (hC : (blockSystem cfg).totalCircleCount = 40)
    (hfive : (blockSystem cfg).blockCount 5 = 7)
    (hmoment : elevenFiveSecondMoment (blockSystem cfg) = 40)
    (hnodisjoint : ∀ b ∈ (blockSystem cfg).blocksOfSize 5,
      ∀ c ∈ (blockSystem cfg).blocksOfSize 5, b ≠ c →
        ((blockSystem cfg).support b ∩
          (blockSystem cfg).support c).card ≠ 0) :
    ElevenFiveC40FourteenSevenTwelveThreeSingleton cfg := by
  classical
  let S := blockSystem cfg
  let O := ((S.blocksOfSize 5).powersetCard 2).filter fun A =>
    (S.commonSupport A).card = 1
  have hOcard : O.card = 2 := by
    simpa [O, S] using
      (c40FourteenSeven_singleton_pair_family_card_two
        S (by simpa [S] using hfive) (by simpa [S] using hmoment)
          (by simpa [S] using hnodisjoint))
  obtain ⟨A, B, hAB, hOeq⟩ := Finset.card_eq_two.mp hOcard
  have hAO : A ∈ O := by rw [hOeq]; simp
  have hBO : B ∈ O := by rw [hOeq]; simp
  have hAdata := Finset.mem_filter.mp hAO
  have hBdata := Finset.mem_filter.mp hBO
  obtain ⟨hfour, hthree, htwo, hprofile⟩ :=
    elevenFive_c40_l14_b5_seven_secondMoment_forty_profile
      S hpoint (by simpa [S] using hlocal) (by simpa [S] using hglobal)
        (by simpa [S] using hfive) (by simpa [S] using hmoment)
  rcases c40FourteenSeven_singleton_pair_classify
      cfg hpoint hlocal hC (by simpa [S] using hprofile) A
        (by simpa [S] using hAdata.1) (by simpa [S] using hAdata.2) with
    htarget | ⟨p, hpA, hpTwo⟩
  · exact htarget
  rcases c40FourteenSeven_singleton_pair_classify
      cfg hpoint hlocal hC (by simpa [S] using hprofile) B
        (by simpa [S] using hBdata.1) (by simpa [S] using hBdata.2) with
    htarget | ⟨q, hqB, hqTwo⟩
  · exact htarget
  have hEq : A = B := c40FourteenSeven_degreeTwo_pair_unique
    S htwo hAdata.1 hBdata.1
      (by simpa [S] using hpA) (by simpa [S] using hqB)
      (by simpa [S] using hpTwo) (by simpa [S] using hqTwo)
  exact False.elim (hAB hEq)

/-- Full moment-40 reduction.  An actual disjoint pair is eliminated by the
page-cap argument; otherwise the two singleton defects force `(12,3)`. -/
theorem elevenFive_c40_l14_b5_seven_secondMoment_forty_reaches_twelveThree
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    (cfg : Configuration Point)
    (hpoint : Fintype.card Point = 11)
    (hcap : BlockSizeCap (blockSystem cfg) 5)
    (hlocal : ∀ p : Point, ElevenFiveLocalRows (blockSystem cfg) p)
    (hglobal : ElevenFiveGlobalRows (blockSystem cfg))
    (hC : (blockSystem cfg).totalCircleCount = 40)
    (hL : elevenFiveLineTotal (blockSystem cfg) = 14)
    (hfive : (blockSystem cfg).blockCount 5 = 7)
    (hmoment : elevenFiveSecondMoment (blockSystem cfg) = 40) :
    ElevenFiveC40FourteenSevenTwelveThreeSingleton cfg := by
  classical
  by_cases hdisjoint : ∃ f, f ∈ (blockSystem cfg).blocksOfSize 5 ∧
      ∃ g, g ∈ (blockSystem cfg).blocksOfSize 5 ∧ f ≠ g ∧
        ((blockSystem cfg).support f ∩
          (blockSystem cfg).support g).card = 0
  · obtain ⟨f, hf, g, hg, hfg, hzero⟩ := hdisjoint
    exact False.elim
      (elevenFive_c40_l14_b5_seven_secondMoment_forty_disjoint_impossible
        cfg hpoint hcap hlocal hglobal hC hL hfive hmoment
          hf hg hfg hzero)
  · apply
      elevenFive_c40_l14_b5_seven_secondMoment_forty_noDisjoint_reaches_twelveThree
        cfg hpoint hlocal hglobal hC hfive hmoment
    intro b hb c hc hbc hzero
    exact hdisjoint ⟨b, hb, c, hc, hbc, hzero⟩

/-! ## Full reduction of the seven-block front -/

private theorem c40FourteenSeven_three_mul_degree_le_choose_add_six
    (d : ℕ) (hd : d ≤ 4) :
    3 * d ≤ Nat.choose d 2 + 6 := by
  interval_cases d <;> norm_num [Nat.choose]

/-- Five-incidence `35` on eleven points forces pair moment at least `39`. -/
theorem elevenFive_c40_l14_b5_seven_secondMoment_ge_thirtyNine
    {Point : Type u} {Block : Type v} [Fintype Point] [Fintype Block]
    [DecidableEq Point]
    (S : BlockSystem Point Block) (hpoint : Fintype.card Point = 11)
    (hlocal : ∀ p : Point, ElevenFiveLocalRows S p)
    (hglobal : ElevenFiveGlobalRows S)
    (hfive : S.blockCount 5 = 7) :
    39 ≤ elevenFiveSecondMoment S := by
  have hsum := Finset.sum_le_sum
    (s := (Finset.univ : Finset Point)) fun p _hp =>
      c40FourteenSeven_three_mul_degree_le_choose_add_six
        (S.blockDegree 5 p) (hlocal p).fiveDegreeCap
  have hleft : (∑ p : Point, 3 * S.blockDegree 5 p) = 105 := by
    rw [← Finset.mul_sum, hglobal.fiveIncidence, hfive]
    norm_num
  have hright :
      (∑ p : Point, (Nat.choose (S.blockDegree 5 p) 2 + 6)) =
        elevenFiveSecondMoment S + 66 := by
    simp [elevenFiveSecondMoment, Finset.sum_add_distrib, hpoint]
  rw [hleft, hright] at hsum
  omega

/-- Pairwise common supports have cardinality at most two, so seven blocks
have pair moment at most `2 * choose 7 2 = 42`. -/
theorem elevenFive_c40_l14_b5_seven_secondMoment_le_fortyTwo
    {Point : Type u} {Block : Type v} [Fintype Point] [Fintype Block]
    [DecidableEq Point] [DecidableEq Block]
    (S : BlockSystem Point Block) (hfive : S.blockCount 5 = 7) :
    elevenFiveSecondMoment S ≤ 42 := by
  classical
  let F := S.blocksOfSize 5
  let Q := F.powersetCard 2
  have hFcard : F.card = 7 := by
    simpa [F, BlockSystem.blockCount] using hfive
  have hterm (A : Finset Block) (hA : A ∈ Q) :
      (S.commonSupport A).card ≤ 2 := by
    apply S.commonSupport_card_le_two
    have hAF : A ∈ F.powersetCard 2 := by simpa [Q] using hA
    exact (Finset.mem_powersetCard.mp hAF).2
  have hsumLe :
      (∑ A ∈ Q, (S.commonSupport A).card) ≤
        ∑ _A ∈ Q, 2 :=
    Finset.sum_le_sum fun A hA => hterm A hA
  have hmomentEq : elevenFiveSecondMoment S =
      ∑ A ∈ Q, (S.commonSupport A).card := by
    change (∑ p : Point, Nat.choose (S.degreeIn F p) 2) =
      ∑ A ∈ F.powersetCard 2, (S.commonSupport A).card
    exact S.binomial_degree_moment F 2
  have hconstant : (∑ _A ∈ Q, 2) = 42 := by
    simp [Q, Finset.card_powersetCard, hFcard, Nat.choose]
  rw [← hmomentEq, hconstant] at hsumLe
  exact hsumLe

/-- Every full `C40/L14/B₅=7` row reaches the single local `(12,3)`
external-trace seam.  Moments `41,42` are impossible; moments `39,40`
both produce the same carrier. -/
theorem elevenFive_c40_l14_b5_seven_reaches_twelveThree
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    (cfg : Configuration Point)
    (hpoint : Fintype.card Point = 11)
    (hcap : BlockSizeCap (blockSystem cfg) 5)
    (hlocal : ∀ p : Point, ElevenFiveLocalRows (blockSystem cfg) p)
    (hglobal : ElevenFiveGlobalRows (blockSystem cfg))
    (hC : (blockSystem cfg).totalCircleCount = 40)
    (hL : elevenFiveLineTotal (blockSystem cfg) = 14)
    (hfive : (blockSystem cfg).blockCount 5 = 7) :
    ElevenFiveC40FourteenSevenTwelveThreeSingleton cfg := by
  have hlower :=
    elevenFive_c40_l14_b5_seven_secondMoment_ge_thirtyNine
      (blockSystem cfg) hpoint hlocal hglobal hfive
  have hupper :=
    elevenFive_c40_l14_b5_seven_secondMoment_le_fortyTwo
      (blockSystem cfg) hfive
  have hcases : elevenFiveSecondMoment (blockSystem cfg) = 39 ∨
      elevenFiveSecondMoment (blockSystem cfg) = 40 ∨
      elevenFiveSecondMoment (blockSystem cfg) = 41 ∨
      elevenFiveSecondMoment (blockSystem cfg) = 42 := by omega
  rcases hcases with h39 | h40 | h41 | h42
  · exact
      elevenFive_c40_l14_b5_seven_secondMoment_thirtyNine_reaches_twelveThree
        cfg hpoint hlocal hglobal hC hfive h39
  · exact
      elevenFive_c40_l14_b5_seven_secondMoment_forty_reaches_twelveThree
        cfg hpoint hcap hlocal hglobal hC hL hfive h40
  · exact False.elim
      (elevenFive_c40_l14_b5_seven_secondMoment_fortyOne_impossible
        cfg hpoint hcap hlocal hglobal hC hL hfive h41)
  · exact False.elim
      (elevenFive_c40_l14_b5_seven_secondMoment_fortyTwo_impossible
        cfg hpoint hcap hlocal hglobal hC hL hfive h42)

/-- Lossless full-front form of the preceding reduction, already expressed
as the actual inverted three-base path with exactly five external traces. -/
noncomputable def elevenFive_c40_l14_b5_seven_reaches_actualFiveTracePath
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    (cfg : Configuration Point)
    (hpoint : Fintype.card Point = 11)
    (hcap : BlockSizeCap (blockSystem cfg) 5)
    (hlocal : ∀ p : Point, ElevenFiveLocalRows (blockSystem cfg) p)
    (hglobal : ElevenFiveGlobalRows (blockSystem cfg))
    (hC : (blockSystem cfg).totalCircleCount = 40)
    (hL : elevenFiveLineTotal (blockSystem cfg) = 14)
    (hfive : (blockSystem cfg).blockCount 5 = 7) :
    ElevenFiveC40FourteenSevenActualFiveTracePath cfg :=
  elevenFive_c40_twelveThreeSingleton_actualFiveTracePath
    cfg hpoint hlocal
      (elevenFive_c40_l14_b5_seven_reaches_twelveThree
        cfg hpoint hcap hlocal hglobal hC hL hfive)

/-! ## The no-disjoint moment-39 defect graph -/

/-- Degree-four carrier points lying on a selected five-block. -/
def elevenFiveC40M39HighOnFiveBlock
    {Point : Type u} {Block : Type v} [Fintype Point] [Fintype Block]
    [DecidableEq Point]
    (S : BlockSystem Point Block) (b : Block) : Finset Point :=
  (S.support b).filter fun p => S.blockDegree 5 p = 4

/-- Other five-blocks meeting `b` in exactly one selected point. -/
def elevenFiveC40M39SingletonNeighbours
    {Point : Type u} {Block : Type v} [Fintype Point] [Fintype Block]
    [DecidableEq Point] [DecidableEq Block]
    (S : BlockSystem Point Block) (b : Block) : Finset Block :=
  ((S.blocksOfSize 5).erase b).filter fun c =>
    (S.support b ∩ S.support c).card = 1

/-- Vertex degree in the singleton-intersection defect graph. -/
def elevenFiveC40M39DefectDegree
    {Point : Type u} {Block : Type v} [Fintype Point] [Fintype Block]
    [DecidableEq Point] [DecidableEq Block]
    (S : BlockSystem Point Block) (b : Block) : ℕ :=
  (elevenFiveC40M39SingletonNeighbours S b).card

/-- Unordered singleton-intersection edges on the seven five-blocks. -/
def elevenFiveC40M39DefectEdges
    {Point : Type u} {Block : Type v} [Fintype Point] [Fintype Block]
    [DecidableEq Point] [DecidableEq Block]
    (S : BlockSystem Point Block) : Finset (Finset Block) :=
  ((S.blocksOfSize 5).powersetCard 2).filter fun A =>
    (S.commonSupport A).card = 1

/-- Unordered pairs of defect edges which share one block vertex. -/
def elevenFiveC40M39AdjacentDefectEdgePairs
    {Point : Type u} {Block : Type v} [Fintype Point] [Fintype Block]
    [DecidableEq Point] [DecidableEq Block]
    (S : BlockSystem Point Block) : Finset (Finset (Finset Block)) :=
  ((elevenFiveC40M39DefectEdges S).powersetCard 2).filter fun P =>
    (P.biUnion fun A => A).card = 3

/-- Invariant presentation of one of the four three-edge, degree-two graph
shapes.  The last parameter counts degree-two vertices; its values
`0,1,2,3` mean respectively `3K2`, `P3+K2`, `P4`, and `C3`.  This is the
same as the number of adjacent edge-pairs once the degree cap excludes
`K1,3`, but is substantially cheaper to consume in the weighted proof. -/
def ElevenFiveC40M39DefectShape
    {Point : Type u} {Block : Type v} [Fintype Point] [Fintype Block]
    [DecidableEq Point] [DecidableEq Block]
  (S : BlockSystem Point Block) (adjacentPairs : ℕ) : Prop :=
  (elevenFiveC40M39DefectEdges S).card = 3 ∧
  (∀ b ∈ S.blocksOfSize 5, elevenFiveC40M39DefectDegree S b ≤ 2) ∧
  ((S.blocksOfSize 5).filter fun b =>
    elevenFiveC40M39DefectDegree S b = 2).card = adjacentPairs

abbrev ElevenFiveC40M39ThreeMatching
    {Point : Type u} {Block : Type v} [Fintype Point] [Fintype Block]
    [DecidableEq Point] [DecidableEq Block]
    (S : BlockSystem Point Block) : Prop := ElevenFiveC40M39DefectShape S 0

abbrev ElevenFiveC40M39PathThreePlusEdge
    {Point : Type u} {Block : Type v} [Fintype Point] [Fintype Block]
    [DecidableEq Point] [DecidableEq Block]
    (S : BlockSystem Point Block) : Prop := ElevenFiveC40M39DefectShape S 1

abbrev ElevenFiveC40M39PathFour
    {Point : Type u} {Block : Type v} [Fintype Point] [Fintype Block]
    [DecidableEq Point] [DecidableEq Block]
    (S : BlockSystem Point Block) : Prop := ElevenFiveC40M39DefectShape S 2

abbrev ElevenFiveC40M39Triangle
    {Point : Type u} {Block : Type v} [Fintype Point] [Fintype Block]
    [DecidableEq Point] [DecidableEq Block]
    (S : BlockSystem Point Block) : Prop := ElevenFiveC40M39DefectShape S 3

private theorem c40Seven_noDisjoint_pair_defect_term
    {Point : Type u} {Block : Type v} [Fintype Point] [Fintype Block]
    [DecidableEq Point] [DecidableEq Block]
    (S : BlockSystem Point Block) (A : Finset Block)
    (hA : A ∈ (S.blocksOfSize 5).powersetCard 2)
    (hnodisjoint : ∀ b ∈ S.blocksOfSize 5, ∀ c ∈ S.blocksOfSize 5,
      b ≠ c → (S.support b ∩ S.support c).card ≠ 0) :
    (S.commonSupport A).card +
      (if (S.commonSupport A).card = 1 then 1 else 0) = 2 := by
  classical
  have hqLe : (S.commonSupport A).card ≤ 2 :=
    S.commonSupport_card_le_two (Finset.mem_powersetCard.mp hA).2
  obtain ⟨b, c, hbc, hAeq⟩ :=
    Finset.card_eq_two.mp (Finset.mem_powersetCard.mp hA).2
  have hb : b ∈ S.blocksOfSize 5 :=
    (Finset.mem_powersetCard.mp hA).1 (by simp [hAeq])
  have hc : c ∈ S.blocksOfSize 5 :=
    (Finset.mem_powersetCard.mp hA).1 (by simp [hAeq])
  have hqNe : (S.commonSupport A).card ≠ 0 := by
    rw [hAeq, S.commonSupport_pair]
    exact hnodisjoint b hb c hc hbc
  by_cases hqOne : (S.commonSupport A).card = 1
  · simp [hqOne]
  · have hqTwo : (S.commonSupport A).card = 2 := by omega
    simp [hqTwo]

/-- In no-disjoint moment `39`, the singleton defect graph has exactly
three edges. -/
theorem elevenFive_c40_l14_b5_seven_m39_defectEdges_card_three
    {Point : Type u} {Block : Type v} [Fintype Point] [Fintype Block]
    [DecidableEq Point] [DecidableEq Block]
    (S : BlockSystem Point Block)
    (hfive : S.blockCount 5 = 7)
    (hmoment : elevenFiveSecondMoment S = 39)
    (hnodisjoint : ∀ b ∈ S.blocksOfSize 5, ∀ c ∈ S.blocksOfSize 5,
      b ≠ c → (S.support b ∩ S.support c).card ≠ 0) :
    (elevenFiveC40M39DefectEdges S).card = 3 := by
  classical
  let F := S.blocksOfSize 5
  let Q := F.powersetCard 2
  let O := Q.filter fun A => (S.commonSupport A).card = 1
  have hFcard : F.card = 7 := by
    simpa [F, BlockSystem.blockCount] using hfive
  have hqsum :
      (∑ A ∈ Q, (S.commonSupport A).card) = 39 := by
    have hmoment' :
        (∑ A ∈ Q, (S.commonSupport A).card) =
          elevenFiveSecondMoment S := by
      change (∑ A ∈ F.powersetCard 2, (S.commonSupport A).card) =
        ∑ p : Point, Nat.choose (S.degreeIn F p) 2
      exact (S.binomial_degree_moment F 2).symm
    exact hmoment'.trans hmoment
  have hsum :
      (∑ A ∈ Q, ((S.commonSupport A).card +
        (if (S.commonSupport A).card = 1 then 1 else 0))) =
        ∑ _A ∈ Q, 2 := by
    apply Finset.sum_congr rfl
    intro A hA
    apply c40Seven_noDisjoint_pair_defect_term S A
    · simpa [Q] using hA
    · exact hnodisjoint
  have hleft :
      (∑ A ∈ Q, ((S.commonSupport A).card +
        (if (S.commonSupport A).card = 1 then 1 else 0))) =
        (∑ A ∈ Q, (S.commonSupport A).card) + O.card := by
    rw [Finset.sum_add_distrib]
    congr 1
    rw [← Finset.sum_filter]
    simp [O]
  have hright : (∑ _A ∈ Q, 2) = 42 := by
    simp [Q, Finset.card_powersetCard, hFcard, Nat.choose]
  rw [hleft, hright, hqsum] at hsum
  have hOcard : O.card = 3 := by omega
  simpa [elevenFiveC40M39DefectEdges, O, Q, F] using hOcard

/-- Fubini around one five-block: after removing the block itself, its
pair-intersection mass is the sum of `d₅-1` over its five points. -/
private theorem c40M39_sum_degree_sub_one_eq_other_intersections
    {Point : Type u} {Block : Type v} [Fintype Point] [Fintype Block]
    [DecidableEq Point] [DecidableEq Block]
    (S : BlockSystem Point Block) (b : Block)
    (hb : b ∈ S.blocksOfSize 5) :
    (∑ p ∈ S.support b, (S.blockDegree 5 p - 1)) =
      ∑ c ∈ (S.blocksOfSize 5).erase b,
        (S.support b ∩ S.support c).card := by
  classical
  let F := S.blocksOfSize 5
  have hbF : b ∈ F := by simpa [F] using hb
  have hbcard : (S.support b).card = 5 := S.mem_blocksOfSize.mp hb
  have hdegree := S.sum_degreeIn_over F (S.support b)
  change (∑ p ∈ S.support b, S.blockDegree 5 p) =
    ∑ c ∈ F, (S.support b ∩ S.support c).card at hdegree
  have hpositive (p : Point) (hp : p ∈ S.support b) :
      0 < S.blockDegree 5 p := by
    have hmem : b ∈ F.filter fun c => p ∈ S.support c :=
      Finset.mem_filter.mpr ⟨hbF, hp⟩
    have hpos := Finset.card_pos.mpr ⟨b, hmem⟩
    simpa [F, BlockSystem.blockDegree, BlockSystem.degreeIn] using hpos
  have hleftSplit :
      (∑ p ∈ S.support b, S.blockDegree 5 p) =
        (∑ p ∈ S.support b, (S.blockDegree 5 p - 1)) + 5 := by
    calc
      (∑ p ∈ S.support b, S.blockDegree 5 p) =
          ∑ p ∈ S.support b, ((S.blockDegree 5 p - 1) + 1) := by
        apply Finset.sum_congr rfl
        intro p hp
        have hpPos := hpositive p hp
        omega
      _ = (∑ p ∈ S.support b, (S.blockDegree 5 p - 1)) + 5 := by
        rw [Finset.sum_add_distrib]
        simp [hbcard]
  have hrightSplit :
      (∑ c ∈ F, (S.support b ∩ S.support c).card) =
        (∑ c ∈ F.erase b, (S.support b ∩ S.support c).card) + 5 := by
    calc
      (∑ c ∈ F, (S.support b ∩ S.support c).card) =
          (∑ c ∈ F.erase b,
            (S.support b ∩ S.support c).card) +
              (S.support b ∩ S.support b).card :=
        (Finset.sum_erase_add F
          (fun c => (S.support b ∩ S.support c).card) hbF).symm
      _ = (∑ c ∈ F.erase b,
            (S.support b ∩ S.support c).card) + 5 := by
        simp [hbcard]
  rw [hleftSplit, hrightSplit] at hdegree
  exact Nat.add_right_cancel hdegree

/-- Two singleton neighbours of one five-block have different carrier
points.  Otherwise the union of the three five-supports has cardinality at
least twelve, impossible on eleven points. -/
theorem fiveBlock_two_singleton_neighbours_carriers_ne
    {Point : Type u} {Block : Type v} [Fintype Point] [Fintype Block]
    [DecidableEq Point]
    (S : BlockSystem Point Block) (hpoint : Fintype.card Point = 11)
    {b c d : Block}
    (hb : b ∈ S.blocksOfSize 5) (hc : c ∈ S.blocksOfSize 5)
    (hd : d ∈ S.blocksOfSize 5)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    {p q : Point}
    (hp : p ∈ S.support b ∩ S.support c)
    (hq : q ∈ S.support b ∩ S.support d)
    (honeBC : (S.support b ∩ S.support c).card = 1)
    (honeBD : (S.support b ∩ S.support d).card = 1) : p ≠ q := by
  intro hpq
  subst q
  have hBDset : S.support b ∩ S.support d = {p} := by
    obtain ⟨r, hr⟩ := Finset.card_eq_one.mp honeBD
    have hpr : p = r := by
      have : p ∈ ({r} : Finset Point) := by simpa [hr] using hq
      simpa using this
    subst r
    exact hr
  have hCDle : (S.support c ∩ S.support d).card ≤ 2 := by
    have hlt := S.distinct_block_inter_card_lt_three hcd
    omega
  have hinterEq :
      ((S.support b ∪ S.support c) ∩ S.support d) =
        S.support c ∩ S.support d := by
    ext x
    constructor
    · intro hx
      have hxd := (Finset.mem_inter.mp hx).2
      rcases Finset.mem_union.mp (Finset.mem_inter.mp hx).1 with hxb | hxc
      · have hxbd : x ∈ S.support b ∩ S.support d :=
          Finset.mem_inter.mpr ⟨hxb, hxd⟩
        rw [hBDset] at hxbd
        have hxp : x = p := by simpa using hxbd
        subst x
        exact Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp hp).2, hxd⟩
      · exact Finset.mem_inter.mpr ⟨hxc, hxd⟩
    · intro hx
      exact Finset.mem_inter.mpr
        ⟨Finset.mem_union_right _ (Finset.mem_inter.mp hx).1,
          (Finset.mem_inter.mp hx).2⟩
  have hBCcard : (S.support b ∪ S.support c).card = 9 := by
    have hrow := Finset.card_union_add_card_inter (S.support b) (S.support c)
    rw [S.mem_blocksOfSize.mp hb, S.mem_blocksOfSize.mp hc, honeBC] at hrow
    omega
  have hUrow := Finset.card_union_add_card_inter
    (S.support b ∪ S.support c) (S.support d)
  have hUlower : 12 ≤
      ((S.support b ∪ S.support c) ∪ S.support d).card := by
    rw [hBCcard, S.mem_blocksOfSize.mp hd, hinterEq] at hUrow
    omega
  have hUupper :
      ((S.support b ∪ S.support c) ∪ S.support d).card ≤ 11 := by
    have hle := Finset.card_le_card
      (Finset.subset_univ ((S.support b ∪ S.support c) ∪ S.support d))
    simpa [Finset.card_univ, hpoint] using hle
  omega

/-- Carrier injectivity for distinct singleton edges whose carrier has
five-degree three.  If two such edges had the same carrier, their union
would have at most three blocks.  Thus they share one block, reducing to
`fiveBlock_two_singleton_neighbours_carriers_ne`. -/
theorem fiveBlock_singleton_edges_degreeThree_carriers_ne
    {Point : Type u} {Block : Type v} [Fintype Point] [Fintype Block]
    [DecidableEq Point] [DecidableEq Block]
    (S : BlockSystem Point Block) (hpoint : Fintype.card Point = 11)
    {A B : Finset Block}
    (hA : A ∈ (S.blocksOfSize 5).powersetCard 2)
    (hB : B ∈ (S.blocksOfSize 5).powersetCard 2)
    (hAone : (S.commonSupport A).card = 1)
    (hBone : (S.commonSupport B).card = 1)
    (hAB : A ≠ B)
    {p q : Point}
    (hp : p ∈ S.commonSupport A) (hq : q ∈ S.commonSupport B)
    (hpFive : S.blockDegree 5 p = 3) : p ≠ q := by
  classical
  intro hpq
  subst q
  have hAcard : A.card = 2 := (Finset.mem_powersetCard.mp hA).2
  have hBcard : B.card = 2 := (Finset.mem_powersetCard.mp hB).2
  let U := A ∪ B
  let I := A ∩ B
  have hUsub : U ⊆ (S.blocksOfSize 5).filter fun b => p ∈ S.support b := by
    intro b hb
    rcases Finset.mem_union.mp (by simpa [U] using hb) with hbA | hbB
    · exact Finset.mem_filter.mpr
        ⟨(Finset.mem_powersetCard.mp hA).1 hbA,
          (S.mem_commonSupport.mp hp) b hbA⟩
    · exact Finset.mem_filter.mpr
        ⟨(Finset.mem_powersetCard.mp hB).1 hbB,
          (S.mem_commonSupport.mp hq) b hbB⟩
  have hincidentCard :
      ((S.blocksOfSize 5).filter fun b => p ∈ S.support b).card = 3 := by
    simpa [BlockSystem.blockDegree, BlockSystem.degreeIn] using hpFive
  have hUle : U.card ≤ 3 := by
    have := Finset.card_le_card hUsub
    rw [hincidentCard] at this
    exact this
  have hformula := Finset.card_union_add_card_inter A B
  change U.card + I.card = A.card + B.card at hformula
  have hIle : I.card ≤ 1 := by
    have hIA : I ⊆ A := by
      intro x hx
      exact (Finset.mem_inter.mp (by simpa [I] using hx)).1
    have hIB : I ⊆ B := by
      intro x hx
      exact (Finset.mem_inter.mp (by simpa [I] using hx)).2
    by_contra hnot
    have hIcard : I.card = 2 := by
      have hle := Finset.card_le_card hIA
      omega
    have hIAeq : I = A :=
      Finset.eq_of_subset_of_card_le hIA (by omega)
    have hIBeq : I = B :=
      Finset.eq_of_subset_of_card_le hIB (by omega)
    exact hAB (hIAeq.symm.trans hIBeq)
  have hIcard : I.card = 1 := by omega
  obtain ⟨b, hIeq⟩ := Finset.card_eq_one.mp hIcard
  have hbI : b ∈ I := by rw [hIeq]; simp
  have hbA : b ∈ A := (Finset.mem_inter.mp (by simpa [I] using hbI)).1
  have hbB : b ∈ B := (Finset.mem_inter.mp (by simpa [I] using hbI)).2
  have hAeraseCard : (A.erase b).card = 1 := by
    rw [Finset.card_erase_of_mem hbA, hAcard]
  have hBeraseCard : (B.erase b).card = 1 := by
    rw [Finset.card_erase_of_mem hbB, hBcard]
  obtain ⟨c, hAc⟩ := Finset.card_eq_one.mp hAeraseCard
  obtain ⟨d, hBd⟩ := Finset.card_eq_one.mp hBeraseCard
  have hcErase : c ∈ A.erase b := by rw [hAc]; simp
  have hdErase : d ∈ B.erase b := by rw [hBd]; simp
  have hcA := (Finset.mem_erase.mp hcErase).2
  have hdB := (Finset.mem_erase.mp hdErase).2
  have hbc : b ≠ c := Ne.symm (Finset.mem_erase.mp hcErase).1
  have hbd : b ≠ d := Ne.symm (Finset.mem_erase.mp hdErase).1
  have hAeq : A = {b, c} := by
    rw [← Finset.insert_erase hbA, hAc]
  have hBeq : B = {b, d} := by
    rw [← Finset.insert_erase hbB, hBd]
  have hcd : c ≠ d := by
    intro h
    subst d
    exact hAB (hAeq.trans hBeq.symm)
  have hbFive : b ∈ S.blocksOfSize 5 :=
    (Finset.mem_powersetCard.mp hA).1 hbA
  have hcFive : c ∈ S.blocksOfSize 5 :=
    (Finset.mem_powersetCard.mp hA).1 hcA
  have hdFive : d ∈ S.blocksOfSize 5 :=
    (Finset.mem_powersetCard.mp hB).1 hdB
  have hpBC : p ∈ S.support b ∩ S.support c := by
    simpa [hAeq, S.commonSupport_pair] using hp
  have hpBD : p ∈ S.support b ∩ S.support d := by
    simpa [hBeq, S.commonSupport_pair] using hq
  have honeBC : (S.support b ∩ S.support c).card = 1 := by
    simpa [hAeq, S.commonSupport_pair] using hAone
  have honeBD : (S.support b ∩ S.support d).card = 1 := by
    simpa [hBeq, S.commonSupport_pair] using hBone
  exact (fiveBlock_two_singleton_neighbours_carriers_ne
    S hpoint hbFive hcFive hdFive hbc hbd hcd hpBC hpBD honeBC honeBD) rfl

/-- In the literal `4² 3⁹` profile, the selected-block side of the
preceding Fubini identity is `10` plus the number of high pivots on it. -/
private theorem c40M39_sum_degree_sub_one_eq_ten_add_high
    {Point : Type u} {Block : Type v} [Fintype Point] [Fintype Block]
    [DecidableEq Point]
    (S : BlockSystem Point Block) (b : Block)
    (hb : b ∈ S.blocksOfSize 5)
    (hprofile : ∀ p : Point,
      S.blockDegree 5 p = 3 ∨ S.blockDegree 5 p = 4) :
    (∑ p ∈ S.support b, (S.blockDegree 5 p - 1)) =
      10 + (elevenFiveC40M39HighOnFiveBlock S b).card := by
  classical
  have hbcard : (S.support b).card = 5 := S.mem_blocksOfSize.mp hb
  have hpoint (p : Point) : S.blockDegree 5 p - 1 =
      2 + (if S.blockDegree 5 p = 4 then 1 else 0) := by
    rcases hprofile p with hthree | hfour
    · simp [hthree]
    · simp [hfour]
  have hindicator :
      (∑ p ∈ S.support b,
        if S.blockDegree 5 p = 4 then 1 else 0) =
          (elevenFiveC40M39HighOnFiveBlock S b).card := by
    simp [elevenFiveC40M39HighOnFiveBlock]
  calc
    (∑ p ∈ S.support b, (S.blockDegree 5 p - 1)) =
        ∑ p ∈ S.support b,
          (2 + (if S.blockDegree 5 p = 4 then 1 else 0)) := by
      apply Finset.sum_congr rfl
      intro p _hp
      exact hpoint p
    _ = (∑ _p ∈ S.support b, 2) +
          ∑ p ∈ S.support b,
            (if S.blockDegree 5 p = 4 then 1 else 0) := by
      rw [Finset.sum_add_distrib]
    _ = 10 + (elevenFiveC40M39HighOnFiveBlock S b).card := by
      rw [hindicator]
      simp [hbcard]

/-- In the no-disjoint face each of the six other blocks contributes two,
except that every singleton neighbour loses one unit. -/
private theorem c40M39_other_intersections_add_defectDegree_eq_twelve
    {Point : Type u} {Block : Type v} [Fintype Point] [Fintype Block]
    [DecidableEq Point] [DecidableEq Block]
    (S : BlockSystem Point Block) (b : Block)
    (hb : b ∈ S.blocksOfSize 5)
    (hfive : S.blockCount 5 = 7)
    (hnodisjoint : ∀ c ∈ S.blocksOfSize 5, b ≠ c →
      (S.support b ∩ S.support c).card ≠ 0) :
    (∑ c ∈ (S.blocksOfSize 5).erase b,
        (S.support b ∩ S.support c).card) +
      elevenFiveC40M39DefectDegree S b = 12 := by
  classical
  let F := S.blocksOfSize 5
  let R := F.erase b
  let N := R.filter fun c => (S.support b ∩ S.support c).card = 1
  have hbF : b ∈ F := by simpa [F] using hb
  have hFcard : F.card = 7 := by
    simpa [F, BlockSystem.blockCount] using hfive
  have hRcard : R.card = 6 := by
    simp [R, Finset.card_erase_of_mem hbF, hFcard]
  have hterm (c : Block) (hc : c ∈ R) :
      (S.support b ∩ S.support c).card +
        (if (S.support b ∩ S.support c).card = 1 then 1 else 0) = 2 := by
    have hcspec := Finset.mem_erase.mp (by simpa [R] using hc)
    have hcF : c ∈ S.blocksOfSize 5 := by simpa [F] using hcspec.2
    have hbc : b ≠ c := Ne.symm hcspec.1
    have hneZero := hnodisjoint c hcF hbc
    have hlt := S.distinct_block_inter_card_lt_three hbc
    have hle : (S.support b ∩ S.support c).card ≤ 2 := by omega
    by_cases hone : (S.support b ∩ S.support c).card = 1
    · simp [hone]
    · have htwo : (S.support b ∩ S.support c).card = 2 := by omega
      simp [htwo]
  have hsum :
      (∑ c ∈ R, ((S.support b ∩ S.support c).card +
        (if (S.support b ∩ S.support c).card = 1 then 1 else 0))) =
        ∑ _c ∈ R, 2 := by
    apply Finset.sum_congr rfl
    intro c hc
    exact hterm c hc
  have hleft :
      (∑ c ∈ R, ((S.support b ∩ S.support c).card +
        (if (S.support b ∩ S.support c).card = 1 then 1 else 0))) =
        (∑ c ∈ R, (S.support b ∩ S.support c).card) + N.card := by
    rw [Finset.sum_add_distrib]
    congr 1
    rw [← Finset.sum_filter]
    simp [N]
  have hright : (∑ _c ∈ R, 2) = 12 := by simp [hRcard]
  rw [hleft, hright] at hsum
  simpa [elevenFiveC40M39DefectDegree,
    elevenFiveC40M39SingletonNeighbours, N, R, F] using hsum

/-- Exact defect-graph identity in moment `39`:
`(# high pivots on b) + deg_G(b) = 2`. -/
theorem elevenFive_c40_l14_b5_seven_m39_highOnBlock_add_defectDegree
    {Point : Type u} {Block : Type v} [Fintype Point] [Fintype Block]
    [DecidableEq Point] [DecidableEq Block]
    (S : BlockSystem Point Block) (hpoint : Fintype.card Point = 11)
    (hlocal : ∀ p : Point, ElevenFiveLocalRows S p)
    (hglobal : ElevenFiveGlobalRows S)
    (hfive : S.blockCount 5 = 7)
    (hmoment : elevenFiveSecondMoment S = 39)
    (b : Block) (hb : b ∈ S.blocksOfSize 5)
    (hnodisjoint : ∀ c ∈ S.blocksOfSize 5, b ≠ c →
      (S.support b ∩ S.support c).card ≠ 0) :
    (elevenFiveC40M39HighOnFiveBlock S b).card +
      elevenFiveC40M39DefectDegree S b = 2 := by
  obtain ⟨_hfour, _hthree, hprofile⟩ :=
    elevenFive_c40_l14_b5_seven_secondMoment_thirtyNine_profile
      S hpoint hlocal hglobal hfive hmoment
  have hhigh := c40M39_sum_degree_sub_one_eq_ten_add_high
    S b hb hprofile
  have hfubini := c40M39_sum_degree_sub_one_eq_other_intersections S b hb
  have hdefect := c40M39_other_intersections_add_defectDegree_eq_twelve
    S b hb hfive hnodisjoint
  omega

/-- The literal M39 profile sharpens the mixed mass bound from `318` to
`303`: baseline five-degree three contributes `3 * 93`, and the two high
pivots contribute at most twelve each. -/
theorem elevenFive_c40_l14_b5_seven_m39_weighted_three_five_le_303
    {Point : Type u} {Block : Type v} [Fintype Point] [Fintype Block]
    [DecidableEq Point]
    (S : BlockSystem Point Block) (hpoint : Fintype.card Point = 11)
    (hlocal : ∀ p : Point, ElevenFiveLocalRows S p)
    (hglobal : ElevenFiveGlobalRows S)
    (hC : S.totalCircleCount = 40)
    (hL : elevenFiveLineTotal S = 14)
    (hfive : S.blockCount 5 = 7)
    (hmoment : elevenFiveSecondMoment S = 39) :
    (∑ p : Point, S.blockDegree 3 p * S.blockDegree 5 p) ≤ 303 := by
  classical
  obtain ⟨hfour, _hthree, hprofile⟩ :=
    elevenFive_c40_l14_b5_seven_secondMoment_thirtyNine_profile
      S hpoint hlocal hglobal hfive hmoment
  let H := (Finset.univ : Finset Point).filter fun p =>
    S.blockDegree 5 p = 4
  have hHcard : H.card = 2 := by simpa [H] using hfour
  have hthreeSum : (∑ p : Point, S.blockDegree 3 p) = 93 := by
    obtain ⟨hthreeCount, _hfourCount⟩ :=
      elevenFive_c40_l14_b5_seven_block_census S hglobal hC hL hfive
    rw [hglobal.threeIncidence, hthreeCount]
  have hpointSplit (p : Point) :
      S.blockDegree 3 p * S.blockDegree 5 p =
        3 * S.blockDegree 3 p +
          (if p ∈ H then S.blockDegree 3 p else 0) := by
    rcases hprofile p with hp3 | hp4
    · simp [H, hp3, Nat.mul_comm]
    · simp [H, hp4, Nat.mul_comm, Nat.succ_mul]
  have hsplit :
      (∑ p : Point, S.blockDegree 3 p * S.blockDegree 5 p) =
        3 * (∑ p : Point, S.blockDegree 3 p) +
          ∑ p ∈ H, S.blockDegree 3 p := by
    calc
      (∑ p : Point, S.blockDegree 3 p * S.blockDegree 5 p) =
          ∑ p : Point, (3 * S.blockDegree 3 p +
            (if p ∈ H then S.blockDegree 3 p else 0)) := by
        apply Finset.sum_congr rfl
        intro p _hp
        exact hpointSplit p
      _ = 3 * (∑ p : Point, S.blockDegree 3 p) +
          ∑ p ∈ H, S.blockDegree 3 p := by
        rw [Finset.sum_add_distrib]
        congr 1
        · rw [Finset.mul_sum]
        · rw [← Finset.sum_filter]
          simp
  have hHsum : (∑ p ∈ H, S.blockDegree 3 p) ≤ 24 := by
    calc
      (∑ p ∈ H, S.blockDegree 3 p) ≤ ∑ _p ∈ H, 12 := by
        apply Finset.sum_le_sum
        intro p _hp
        rcases elevenFive_c40_threeDegree_values S p (hlocal p) hC with
          h6 | h9 | h12 <;> omega
      _ = 24 := by simp [hHcard]
  rw [hsplit, hthreeSum]
  omega

/-- Exact form behind the `303` bound: M39 is the degree-three baseline
`3 * 93 = 279` plus the three-degrees of the two degree-four pivots. -/
theorem elevenFive_c40_l14_b5_seven_m39_weighted_eq_279_add_high
    {Point : Type u} {Block : Type v} [Fintype Point] [Fintype Block]
    [DecidableEq Point]
    (S : BlockSystem Point Block) (hpoint : Fintype.card Point = 11)
    (hlocal : ∀ p : Point, ElevenFiveLocalRows S p)
    (hglobal : ElevenFiveGlobalRows S)
    (hC : S.totalCircleCount = 40)
    (hL : elevenFiveLineTotal S = 14)
    (hfive : S.blockCount 5 = 7)
    (hmoment : elevenFiveSecondMoment S = 39) :
    (∑ p : Point, S.blockDegree 3 p * S.blockDegree 5 p) =
      279 + ∑ p ∈ (Finset.univ : Finset Point).filter
        (fun p => S.blockDegree 5 p = 4), S.blockDegree 3 p := by
  classical
  obtain ⟨_hfour, _hthree, hprofile⟩ :=
    elevenFive_c40_l14_b5_seven_secondMoment_thirtyNine_profile
      S hpoint hlocal hglobal hfive hmoment
  let H := (Finset.univ : Finset Point).filter fun p =>
    S.blockDegree 5 p = 4
  have hthreeSum : (∑ p : Point, S.blockDegree 3 p) = 93 := by
    obtain ⟨hthreeCount, _hfourCount⟩ :=
      elevenFive_c40_l14_b5_seven_block_census S hglobal hC hL hfive
    rw [hglobal.threeIncidence, hthreeCount]
  have hpointSplit (p : Point) :
      S.blockDegree 3 p * S.blockDegree 5 p =
        3 * S.blockDegree 3 p +
          (if p ∈ H then S.blockDegree 3 p else 0) := by
    rcases hprofile p with hp3 | hp4
    · simp [H, hp3, Nat.mul_comm]
    · simp [H, hp4, Nat.mul_comm, Nat.succ_mul]
  calc
    (∑ p : Point, S.blockDegree 3 p * S.blockDegree 5 p) =
        ∑ p : Point, (3 * S.blockDegree 3 p +
          (if p ∈ H then S.blockDegree 3 p else 0)) := by
      apply Finset.sum_congr rfl
      intro p _hp
      exact hpointSplit p
    _ = 3 * (∑ p : Point, S.blockDegree 3 p) +
        ∑ p ∈ H, S.blockDegree 3 p := by
      rw [Finset.sum_add_distrib, Finset.mul_sum]
      congr 1
      rw [← Finset.sum_filter]
      simp
    _ = 279 + ∑ p ∈ H, S.blockDegree 3 p := by rw [hthreeSum]
    _ = 279 + ∑ p ∈ (Finset.univ : Finset Point).filter
        (fun p => S.blockDegree 5 p = 4), S.blockDegree 3 p := by rfl

/-- Hence the three-edge defect graph has maximum vertex degree two. -/
theorem elevenFive_c40_l14_b5_seven_m39_defectDegree_le_two
    {Point : Type u} {Block : Type v} [Fintype Point] [Fintype Block]
    [DecidableEq Point] [DecidableEq Block]
    (S : BlockSystem Point Block) (hpoint : Fintype.card Point = 11)
    (hlocal : ∀ p : Point, ElevenFiveLocalRows S p)
    (hglobal : ElevenFiveGlobalRows S)
    (hfive : S.blockCount 5 = 7)
    (hmoment : elevenFiveSecondMoment S = 39)
    (hnodisjoint : ∀ b ∈ S.blocksOfSize 5, ∀ c ∈ S.blocksOfSize 5,
      b ≠ c → (S.support b ∩ S.support c).card ≠ 0)
    (b : Block) (hb : b ∈ S.blocksOfSize 5) :
    elevenFiveC40M39DefectDegree S b ≤ 2 := by
  have hid :=
    elevenFive_c40_l14_b5_seven_m39_highOnBlock_add_defectDegree
      S hpoint hlocal hglobal hfive hmoment b hb
        (fun c hc hbc => hnodisjoint b hb c hc hbc)
  omega

/-- Literal anchor localization: defect degrees `0,1,2` carry respectively
two, one, or no degree-four pivots. -/
theorem elevenFive_c40_l14_b5_seven_m39_highOnBlock_by_defectDegree
    {Point : Type u} {Block : Type v} [Fintype Point] [Fintype Block]
    [DecidableEq Point] [DecidableEq Block]
    (S : BlockSystem Point Block) (hpoint : Fintype.card Point = 11)
    (hlocal : ∀ p : Point, ElevenFiveLocalRows S p)
    (hglobal : ElevenFiveGlobalRows S)
    (hfive : S.blockCount 5 = 7)
    (hmoment : elevenFiveSecondMoment S = 39)
    (b : Block) (hb : b ∈ S.blocksOfSize 5)
    (hnodisjoint : ∀ c ∈ S.blocksOfSize 5, b ≠ c →
      (S.support b ∩ S.support c).card ≠ 0) :
    (elevenFiveC40M39DefectDegree S b = 0 →
      (elevenFiveC40M39HighOnFiveBlock S b).card = 2) ∧
    (elevenFiveC40M39DefectDegree S b = 1 →
      (elevenFiveC40M39HighOnFiveBlock S b).card = 1) ∧
    (elevenFiveC40M39DefectDegree S b = 2 →
      (elevenFiveC40M39HighOnFiveBlock S b).card = 0) := by
  have hid :=
    elevenFive_c40_l14_b5_seven_m39_highOnBlock_add_defectDegree
      S hpoint hlocal hglobal hfive hmoment b hb hnodisjoint
  omega

/-- The singleton defect graph has degree sum six.  This is obtained
without orienting its edges: sum the exact local identity
`highOnBlock + defectDegree = 2`, and count the two degree-four pivots,
each incident with four five-blocks. -/
theorem elevenFive_c40_l14_b5_seven_m39_sum_defectDegree_eq_six
    {Point : Type u} {Block : Type v} [Fintype Point] [Fintype Block]
    [DecidableEq Point] [DecidableEq Block]
    (S : BlockSystem Point Block) (hpoint : Fintype.card Point = 11)
    (hlocal : ∀ p : Point, ElevenFiveLocalRows S p)
    (hglobal : ElevenFiveGlobalRows S)
    (hfive : S.blockCount 5 = 7)
    (hmoment : elevenFiveSecondMoment S = 39)
    (hnodisjoint : ∀ b ∈ S.blocksOfSize 5, ∀ c ∈ S.blocksOfSize 5,
      b ≠ c → (S.support b ∩ S.support c).card ≠ 0) :
    (∑ b ∈ S.blocksOfSize 5,
      elevenFiveC40M39DefectDegree S b) = 6 := by
  classical
  let F := S.blocksOfSize 5
  let H := (Finset.univ : Finset Point).filter fun p =>
    S.blockDegree 5 p = 4
  obtain ⟨hfour, _hthree, _hprofile⟩ :=
    elevenFive_c40_l14_b5_seven_secondMoment_thirtyNine_profile
      S hpoint hlocal hglobal hfive hmoment
  have hFcard : F.card = 7 := by
    simpa [F, BlockSystem.blockCount] using hfive
  have hHcard : H.card = 2 := by simpa [H] using hfour
  have hhighSum :
      (∑ b ∈ F, (elevenFiveC40M39HighOnFiveBlock S b).card) = 8 := by
    have hfubini := S.sum_degreeIn_over F H
    change (∑ p ∈ H, S.blockDegree 5 p) =
      ∑ b ∈ F, (H ∩ S.support b).card at hfubini
    calc
      (∑ b ∈ F, (elevenFiveC40M39HighOnFiveBlock S b).card) =
          ∑ b ∈ F, (H ∩ S.support b).card := by
        apply Finset.sum_congr rfl
        intro b _hb
        congr 1
        ext p
        simp [H, elevenFiveC40M39HighOnFiveBlock, and_comm]
      _ = ∑ p ∈ H, S.blockDegree 5 p := hfubini.symm
      _ = ∑ _p ∈ H, 4 := by
        apply Finset.sum_congr rfl
        intro p hp
        exact (Finset.mem_filter.mp hp).2
      _ = 8 := by simp [hHcard]
  have hsumIdentity :
      (∑ b ∈ F, ((elevenFiveC40M39HighOnFiveBlock S b).card +
        elevenFiveC40M39DefectDegree S b)) = ∑ _b ∈ F, 2 := by
    apply Finset.sum_congr rfl
    intro b hb
    exact elevenFive_c40_l14_b5_seven_m39_highOnBlock_add_defectDegree
      S hpoint hlocal hglobal hfive hmoment b (by simpa [F] using hb)
        (fun c hc hbc => hnodisjoint b (by simpa [F] using hb) c hc hbc)
  rw [Finset.sum_add_distrib, hhighSum] at hsumIdentity
  simp [hFcard] at hsumIdentity
  have hdefectSum :
      (∑ b ∈ F, elevenFiveC40M39DefectDegree S b) = 6 := by
    omega
  simpa [F] using hdefectSum

/-- Complete four-way classification of the no-disjoint moment-39 defect
graph.  Its three edges have degree sum six; hence at most three vertices
have degree two, and that count gives the four possible shapes. -/
theorem elevenFive_c40_l14_b5_seven_m39_defectShape_classification
    {Point : Type u} {Block : Type v} [Fintype Point] [Fintype Block]
    [DecidableEq Point] [DecidableEq Block]
    (S : BlockSystem Point Block) (hpoint : Fintype.card Point = 11)
    (hlocal : ∀ p : Point, ElevenFiveLocalRows S p)
    (hglobal : ElevenFiveGlobalRows S)
    (hfive : S.blockCount 5 = 7)
    (hmoment : elevenFiveSecondMoment S = 39)
    (hnodisjoint : ∀ b ∈ S.blocksOfSize 5, ∀ c ∈ S.blocksOfSize 5,
      b ≠ c → (S.support b ∩ S.support c).card ≠ 0) :
    ElevenFiveC40M39ThreeMatching S ∨
      ElevenFiveC40M39PathThreePlusEdge S ∨
      ElevenFiveC40M39PathFour S ∨
      ElevenFiveC40M39Triangle S := by
  classical
  let G := elevenFiveC40M39DefectEdges S
  let T := (S.blocksOfSize 5).filter fun b =>
    elevenFiveC40M39DefectDegree S b = 2
  have hGcard : G.card = 3 := by
    simpa [G] using
      (elevenFive_c40_l14_b5_seven_m39_defectEdges_card_three
        S hfive hmoment hnodisjoint)
  have hdegree : ∀ b ∈ S.blocksOfSize 5,
      elevenFiveC40M39DefectDegree S b ≤ 2 := by
    intro b hb
    exact elevenFive_c40_l14_b5_seven_m39_defectDegree_le_two
      S hpoint hlocal hglobal hfive hmoment hnodisjoint b hb
  have hdegreeSum :=
    elevenFive_c40_l14_b5_seven_m39_sum_defectDegree_eq_six
      S hpoint hlocal hglobal hfive hmoment hnodisjoint
  have hselectedLower :
      (∑ b ∈ S.blocksOfSize 5,
        if elevenFiveC40M39DefectDegree S b = 2 then 2 else 0) ≤
          ∑ b ∈ S.blocksOfSize 5,
            elevenFiveC40M39DefectDegree S b := by
    apply Finset.sum_le_sum
    intro b hb
    by_cases htwo : elevenFiveC40M39DefectDegree S b = 2
    · simp [htwo]
    · simp [htwo]
  have hselectedSum :
      (∑ b ∈ S.blocksOfSize 5,
        if elevenFiveC40M39DefectDegree S b = 2 then 2 else 0) =
          2 * T.card := by
    rw [← Finset.sum_filter]
    simp [T, Nat.mul_comm]
  have hTle : T.card ≤ 3 := by
    rw [hselectedSum, hdegreeSum] at hselectedLower
    omega
  have hcases : T.card = 0 ∨ T.card = 1 ∨
      T.card = 2 ∨ T.card = 3 := by omega
  rcases hcases with h0 | h1 | h2 | h3
  · exact Or.inl ⟨by simpa [G] using hGcard, hdegree,
      by simpa [T] using h0⟩
  · exact Or.inr (Or.inl ⟨by simpa [G] using hGcard, hdegree,
      by simpa [T] using h1⟩)
  · exact Or.inr (Or.inr (Or.inl
      ⟨by simpa [G] using hGcard, hdegree, by simpa [T] using h2⟩))
  · exact Or.inr (Or.inr (Or.inr
      ⟨by simpa [G] using hGcard, hdegree, by simpa [T] using h3⟩))

/-- The zero/one/two defect-degree classes partition the seven five-blocks,
and their degree-weighted count is the graph handshake `6`. -/
theorem elevenFive_c40_l14_b5_seven_m39_defectDegree_partition_rows
    {Point : Type u} {Block : Type v} [Fintype Point] [Fintype Block]
    [DecidableEq Point] [DecidableEq Block]
    (S : BlockSystem Point Block) (hpoint : Fintype.card Point = 11)
    (hlocal : ∀ p : Point, ElevenFiveLocalRows S p)
    (hglobal : ElevenFiveGlobalRows S)
    (hfive : S.blockCount 5 = 7)
    (hmoment : elevenFiveSecondMoment S = 39)
    (hnodisjoint : ∀ b ∈ S.blocksOfSize 5, ∀ c ∈ S.blocksOfSize 5,
      b ≠ c → (S.support b ∩ S.support c).card ≠ 0) :
    let Z := (S.blocksOfSize 5).filter fun b =>
      elevenFiveC40M39DefectDegree S b = 0
    let O := (S.blocksOfSize 5).filter fun b =>
      elevenFiveC40M39DefectDegree S b = 1
    let T := (S.blocksOfSize 5).filter fun b =>
      elevenFiveC40M39DefectDegree S b = 2
    Z.card + O.card + T.card = 7 ∧ O.card + 2 * T.card = 6 := by
  classical
  let F := S.blocksOfSize 5
  let Z := F.filter fun b => elevenFiveC40M39DefectDegree S b = 0
  let O := F.filter fun b => elevenFiveC40M39DefectDegree S b = 1
  let T := F.filter fun b => elevenFiveC40M39DefectDegree S b = 2
  have hcap : ∀ b ∈ F, elevenFiveC40M39DefectDegree S b ≤ 2 := by
    intro b hb
    exact elevenFive_c40_l14_b5_seven_m39_defectDegree_le_two
      S hpoint hlocal hglobal hfive hmoment hnodisjoint b
        (by simpa [F] using hb)
  have hcases (b : Block) (hb : b ∈ F) :
      elevenFiveC40M39DefectDegree S b = 0 ∨
      elevenFiveC40M39DefectDegree S b = 1 ∨
      elevenFiveC40M39DefectDegree S b = 2 := by
    have := hcap b hb
    omega
  have hcardRow : Z.card + O.card + T.card = F.card := by
    have hsum :
        (∑ b ∈ F, ((if elevenFiveC40M39DefectDegree S b = 0 then 1 else 0) +
          (if elevenFiveC40M39DefectDegree S b = 1 then 1 else 0) +
          (if elevenFiveC40M39DefectDegree S b = 2 then 1 else 0))) =
            ∑ _b ∈ F, 1 := by
      apply Finset.sum_congr rfl
      intro b hb
      rcases hcases b hb with h0 | h1 | h2
      · simp [h0]
      · simp [h1]
      · simp [h2]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib] at hsum
    simpa [Z, O, T, ← Finset.sum_filter] using hsum
  have hdegreeRow : O.card + 2 * T.card = 6 := by
    have hsum :
        (∑ b ∈ F, elevenFiveC40M39DefectDegree S b) =
          ∑ b ∈ F, ((if elevenFiveC40M39DefectDegree S b = 1 then 1 else 0) +
            (if elevenFiveC40M39DefectDegree S b = 2 then 2 else 0)) := by
      apply Finset.sum_congr rfl
      intro b hb
      rcases hcases b hb with h0 | h1 | h2
      · simp [h0]
      · simp [h1]
      · simp [h2]
    rw [elevenFive_c40_l14_b5_seven_m39_sum_defectDegree_eq_six
      S hpoint hlocal hglobal hfive hmoment hnodisjoint,
      Finset.sum_add_distrib] at hsum
    simpa [O, T, ← Finset.sum_filter, Nat.mul_comm] using hsum.symm
  have hFcard : F.card = 7 := by
    simpa [F, BlockSystem.blockCount] using hfive
  change Z.card + O.card + T.card = 7 ∧ O.card + 2 * T.card = 6
  exact ⟨hcardRow.trans hFcard, hdegreeRow⟩

theorem elevenFive_c40_l14_b5_seven_m39_triangle_degree_counts
    {Point : Type u} {Block : Type v} [Fintype Point] [Fintype Block]
    [DecidableEq Point] [DecidableEq Block]
    (S : BlockSystem Point Block) (hpoint : Fintype.card Point = 11)
    (hlocal : ∀ p : Point, ElevenFiveLocalRows S p)
    (hglobal : ElevenFiveGlobalRows S)
    (hfive : S.blockCount 5 = 7)
    (hmoment : elevenFiveSecondMoment S = 39)
    (hnodisjoint : ∀ b ∈ S.blocksOfSize 5, ∀ c ∈ S.blocksOfSize 5,
      b ≠ c → (S.support b ∩ S.support c).card ≠ 0)
    (htriangle : ElevenFiveC40M39Triangle S) :
    ((S.blocksOfSize 5).filter fun b =>
      elevenFiveC40M39DefectDegree S b = 0).card = 4 ∧
    ((S.blocksOfSize 5).filter fun b =>
      elevenFiveC40M39DefectDegree S b = 1).card = 0 ∧
    ((S.blocksOfSize 5).filter fun b =>
      elevenFiveC40M39DefectDegree S b = 2).card = 3 := by
  obtain ⟨hcard, hdegree⟩ :=
    elevenFive_c40_l14_b5_seven_m39_defectDegree_partition_rows
      S hpoint hlocal hglobal hfive hmoment hnodisjoint
  have htwo := htriangle.2.2
  omega

theorem elevenFive_c40_l14_b5_seven_m39_pathFour_degree_counts
    {Point : Type u} {Block : Type v} [Fintype Point] [Fintype Block]
    [DecidableEq Point] [DecidableEq Block]
    (S : BlockSystem Point Block) (hpoint : Fintype.card Point = 11)
    (hlocal : ∀ p : Point, ElevenFiveLocalRows S p)
    (hglobal : ElevenFiveGlobalRows S)
    (hfive : S.blockCount 5 = 7)
    (hmoment : elevenFiveSecondMoment S = 39)
    (hnodisjoint : ∀ b ∈ S.blocksOfSize 5, ∀ c ∈ S.blocksOfSize 5,
      b ≠ c → (S.support b ∩ S.support c).card ≠ 0)
    (hpath : ElevenFiveC40M39PathFour S) :
    ((S.blocksOfSize 5).filter fun b =>
      elevenFiveC40M39DefectDegree S b = 0).card = 3 ∧
    ((S.blocksOfSize 5).filter fun b =>
      elevenFiveC40M39DefectDegree S b = 1).card = 2 ∧
    ((S.blocksOfSize 5).filter fun b =>
      elevenFiveC40M39DefectDegree S b = 2).card = 2 := by
  obtain ⟨hcard, hdegree⟩ :=
    elevenFive_c40_l14_b5_seven_m39_defectDegree_partition_rows
      S hpoint hlocal hglobal hfive hmoment hnodisjoint
  have htwo := hpath.2.2
  omega

theorem elevenFive_c40_l14_b5_seven_m39_pathThreePlusEdge_degree_counts
    {Point : Type u} {Block : Type v} [Fintype Point] [Fintype Block]
    [DecidableEq Point] [DecidableEq Block]
    (S : BlockSystem Point Block) (hpoint : Fintype.card Point = 11)
    (hlocal : ∀ p : Point, ElevenFiveLocalRows S p)
    (hglobal : ElevenFiveGlobalRows S)
    (hfive : S.blockCount 5 = 7)
    (hmoment : elevenFiveSecondMoment S = 39)
    (hnodisjoint : ∀ b ∈ S.blocksOfSize 5, ∀ c ∈ S.blocksOfSize 5,
      b ≠ c → (S.support b ∩ S.support c).card ≠ 0)
    (hshape : ElevenFiveC40M39PathThreePlusEdge S) :
    ((S.blocksOfSize 5).filter fun b =>
      elevenFiveC40M39DefectDegree S b = 0).card = 2 ∧
    ((S.blocksOfSize 5).filter fun b =>
      elevenFiveC40M39DefectDegree S b = 1).card = 4 ∧
    ((S.blocksOfSize 5).filter fun b =>
      elevenFiveC40M39DefectDegree S b = 2).card = 1 := by
  obtain ⟨hcard, hdegree⟩ :=
    elevenFive_c40_l14_b5_seven_m39_defectDegree_partition_rows
      S hpoint hlocal hglobal hfive hmoment hnodisjoint
  have htwo := hshape.2.2
  omega

theorem elevenFive_c40_l14_b5_seven_m39_threeMatching_degree_counts
    {Point : Type u} {Block : Type v} [Fintype Point] [Fintype Block]
    [DecidableEq Point] [DecidableEq Block]
    (S : BlockSystem Point Block) (hpoint : Fintype.card Point = 11)
    (hlocal : ∀ p : Point, ElevenFiveLocalRows S p)
    (hglobal : ElevenFiveGlobalRows S)
    (hfive : S.blockCount 5 = 7)
    (hmoment : elevenFiveSecondMoment S = 39)
    (hnodisjoint : ∀ b ∈ S.blocksOfSize 5, ∀ c ∈ S.blocksOfSize 5,
      b ≠ c → (S.support b ∩ S.support c).card ≠ 0)
    (hshape : ElevenFiveC40M39ThreeMatching S) :
    ((S.blocksOfSize 5).filter fun b =>
      elevenFiveC40M39DefectDegree S b = 0).card = 1 ∧
    ((S.blocksOfSize 5).filter fun b =>
      elevenFiveC40M39DefectDegree S b = 1).card = 6 ∧
    ((S.blocksOfSize 5).filter fun b =>
      elevenFiveC40M39DefectDegree S b = 2).card = 0 := by
  obtain ⟨hcard, hdegree⟩ :=
    elevenFive_c40_l14_b5_seven_m39_defectDegree_partition_rows
      S hpoint hlocal hglobal hfive hmoment hnodisjoint
  have htwo := hshape.2.2
  omega

/-! ### Sharp block masses at the defect-graph endpoint -/

/-- The two singleton neighbours of a defect-degree-two five-block provide
two different `(d₃,d₅) = (12,3)` carrier points on that block. -/
theorem elevenFive_c40_l14_b5_seven_m39_degreeTwo_carriers
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    (cfg : Configuration Point) (hpoint : Fintype.card Point = 11)
    (hlocal : ∀ p : Point, ElevenFiveLocalRows (blockSystem cfg) p)
    (hglobal : ElevenFiveGlobalRows (blockSystem cfg))
    (hC : (blockSystem cfg).totalCircleCount = 40)
    (hfive : (blockSystem cfg).blockCount 5 = 7)
    (hmoment : elevenFiveSecondMoment (blockSystem cfg) = 39)
    (b : GeometricBlock cfg)
    (hb : b ∈ (blockSystem cfg).blocksOfSize 5)
    (hdegree : elevenFiveC40M39DefectDegree (blockSystem cfg) b = 2) :
    ∃ p q : Point, p ≠ q ∧
      p ∈ geometricBlockSupport cfg b ∧
      q ∈ geometricBlockSupport cfg b ∧
      (blockSystem cfg).blockDegree 3 p = 12 ∧
      (blockSystem cfg).blockDegree 5 p = 3 ∧
      (blockSystem cfg).blockDegree 3 q = 12 ∧
      (blockSystem cfg).blockDegree 5 q = 3 := by
  classical
  let S := blockSystem cfg
  let N := elevenFiveC40M39SingletonNeighbours S b
  have hNcard : N.card = 2 := by
    simpa [N, elevenFiveC40M39DefectDegree] using hdegree
  obtain ⟨c, d, hcd, hNeq⟩ := Finset.card_eq_two.mp hNcard
  have hcN : c ∈ N := by rw [hNeq]; simp
  have hdN : d ∈ N := by rw [hNeq]; simp
  have hcSpec := Finset.mem_filter.mp (by simpa only [N] using hcN)
  have hdSpec := Finset.mem_filter.mp (by simpa only [N] using hdN)
  have hcErase := Finset.mem_erase.mp hcSpec.1
  have hdErase := Finset.mem_erase.mp hdSpec.1
  have hc : c ∈ S.blocksOfSize 5 := hcErase.2
  have hd : d ∈ S.blocksOfSize 5 := hdErase.2
  have hbc : b ≠ c := Ne.symm hcErase.1
  have hbd : b ≠ d := Ne.symm hdErase.1
  obtain ⟨p, hpEq⟩ := Finset.card_eq_one.mp hcSpec.2
  obtain ⟨q, hqEq⟩ := Finset.card_eq_one.mp hdSpec.2
  have hpInter : p ∈ S.support b ∩ S.support c := by rw [hpEq]; simp
  have hqInter : q ∈ S.support b ∩ S.support d := by rw [hqEq]; simp
  have hpq : p ≠ q := fiveBlock_two_singleton_neighbours_carriers_ne
    S hpoint hb hc hd hbc hbd hcd hpInter hqInter hcSpec.2 hdSpec.2
  obtain ⟨_hfour, _hthree, hprofile⟩ :=
    elevenFive_c40_l14_b5_seven_secondMoment_thirtyNine_profile
      S hpoint (by simpa [S] using hlocal) (by simpa [S] using hglobal)
        (by simpa [S] using hfive) (by simpa [S] using hmoment)
  have hbCfg : b ∈ (blockSystem cfg).blocksOfSize 5 := by simpa [S] using hb
  have hcCfg : c ∈ (blockSystem cfg).blocksOfSize 5 := by simpa [S] using hc
  have hdCfg : d ∈ (blockSystem cfg).blocksOfSize 5 := by simpa [S] using hd
  have hpB : p ∈ geometricBlockSupport cfg b := by
    simpa [S, blockSystem, geometricBlockSystem, geometricBlockSupport] using
      (Finset.mem_inter.mp hpInter).1
  have hpC : p ∈ geometricBlockSupport cfg c := by
    simpa [S, blockSystem, geometricBlockSystem, geometricBlockSupport] using
      (Finset.mem_inter.mp hpInter).2
  have hqB : q ∈ geometricBlockSupport cfg b := by
    simpa [S, blockSystem, geometricBlockSystem, geometricBlockSupport] using
      (Finset.mem_inter.mp hqInter).1
  have hqD : q ∈ geometricBlockSupport cfg d := by
    simpa [S, blockSystem, geometricBlockSystem, geometricBlockSupport] using
      (Finset.mem_inter.mp hqInter).2
  have hpFive : S.blockDegree 5 p = 3 := by
    rcases hprofile p with hp3 | hp4
    · exact hp3
    · exact False.elim (elevenFive_degreeFourPivot_fiveBlock_inter_card_ne_one
        cfg hpoint p (by simpa [S] using hp4) hbCfg hcCfg hpB hpC hbc
          (by simpa [S, blockSystem, geometricBlockSystem,
            geometricBlockSupport] using hcSpec.2))
  have hqFive : S.blockDegree 5 q = 3 := by
    rcases hprofile q with hq3 | hq4
    · exact hq3
    · exact False.elim (elevenFive_degreeFourPivot_fiveBlock_inter_card_ne_one
        cfg hpoint q (by simpa [S] using hq4) hbCfg hdCfg hqB hqD hbd
          (by simpa [S, blockSystem, geometricBlockSystem,
            geometricBlockSupport] using hdSpec.2))
  have hpThree := elevenFive_c40_singleton_carrier_twelve_of_fiveDegree_three
    cfg hpoint p (hlocal p) hC (by simpa [S] using hpFive)
      hbCfg hcCfg hpB hpC hbc
        (by simpa [S, blockSystem, geometricBlockSystem,
          geometricBlockSupport] using hcSpec.2)
  have hqThree := elevenFive_c40_singleton_carrier_twelve_of_fiveDegree_three
    cfg hpoint q (hlocal q) hC (by simpa [S] using hqFive)
      hbCfg hdCfg hqB hqD hbd
        (by simpa [S, blockSystem, geometricBlockSystem,
          geometricBlockSupport] using hdSpec.2)
  exact ⟨p, q, hpq, hpB, hqB, hpThree, by simpa [S] using hpFive,
    hqThree, by simpa [S] using hqFive⟩

/-- Every singleton edge in the literal M39 profile has a `(12,3)`
carrier. -/
theorem elevenFive_c40_l14_b5_seven_m39_defectEdge_carrier
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    (cfg : Configuration Point) (hpoint : Fintype.card Point = 11)
    (hlocal : ∀ p : Point, ElevenFiveLocalRows (blockSystem cfg) p)
    (hglobal : ElevenFiveGlobalRows (blockSystem cfg))
    (hC : (blockSystem cfg).totalCircleCount = 40)
    (hfive : (blockSystem cfg).blockCount 5 = 7)
    (hmoment : elevenFiveSecondMoment (blockSystem cfg) = 39)
    (A : Finset (GeometricBlock cfg))
    (hA : A ∈ elevenFiveC40M39DefectEdges (blockSystem cfg)) :
    ∃ p : Point, p ∈ (blockSystem cfg).commonSupport A ∧
      (blockSystem cfg).blockDegree 3 p = 12 ∧
      (blockSystem cfg).blockDegree 5 p = 3 := by
  classical
  let S := blockSystem cfg
  have hAdata := Finset.mem_filter.mp
    (by simpa only [S, elevenFiveC40M39DefectEdges] using hA)
  obtain ⟨b, c, hbc, hAeq⟩ :=
    Finset.card_eq_two.mp (Finset.mem_powersetCard.mp hAdata.1).2
  have hb : b ∈ S.blocksOfSize 5 :=
    (Finset.mem_powersetCard.mp hAdata.1).1 (by simp [hAeq])
  have hc : c ∈ S.blocksOfSize 5 :=
    (Finset.mem_powersetCard.mp hAdata.1).1 (by simp [hAeq])
  obtain ⟨p, hpEq⟩ := Finset.card_eq_one.mp hAdata.2
  have hpCommon : p ∈ S.commonSupport A := by rw [hpEq]; simp
  have hpInter : p ∈ S.support b ∩ S.support c := by
    simpa [hAeq, S.commonSupport_pair] using hpCommon
  change p ∈ geometricBlockSupport cfg b ∩ geometricBlockSupport cfg c at hpInter
  have hbCfg : b ∈ (blockSystem cfg).blocksOfSize 5 := by simpa [S] using hb
  have hcCfg : c ∈ (blockSystem cfg).blocksOfSize 5 := by simpa [S] using hc
  have hpB : p ∈ geometricBlockSupport cfg b := by
    exact (Finset.mem_inter.mp hpInter).1
  have hpC : p ∈ geometricBlockSupport cfg c := by
    exact (Finset.mem_inter.mp hpInter).2
  have honeCfg :
      (geometricBlockSupport cfg b ∩ geometricBlockSupport cfg c).card = 1 := by
    have honeS : (S.support b ∩ S.support c).card = 1 := by
      rw [← S.commonSupport_pair, ← hAeq]
      exact hAdata.2
    change (geometricBlockSupport cfg b ∩
      geometricBlockSupport cfg c).card = 1 at honeS
    exact honeS
  obtain ⟨_hfour, _hthree, hprofile⟩ :=
    elevenFive_c40_l14_b5_seven_secondMoment_thirtyNine_profile
      S hpoint (by simpa [S] using hlocal) (by simpa [S] using hglobal)
        (by simpa [S] using hfive) (by simpa [S] using hmoment)
  have hpFive : S.blockDegree 5 p = 3 := by
    rcases hprofile p with hp3 | hp4
    · exact hp3
    · exact False.elim (elevenFive_degreeFourPivot_fiveBlock_inter_card_ne_one
        cfg hpoint p (by simpa [S] using hp4) hbCfg hcCfg hpB hpC hbc honeCfg)
  have hpThree := elevenFive_c40_singleton_carrier_twelve_of_fiveDegree_three
    cfg hpoint p (hlocal p) hC (by simpa [S] using hpFive)
      hbCfg hcCfg hpB hpC hbc honeCfg
  exact ⟨p, by simpa [S] using hpCommon, hpThree, by simpa [S] using hpFive⟩

private theorem elevenFive_c40_l14_b5_seven_m39_three_edge_carriers
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    (cfg : Configuration Point) (hpoint : Fintype.card Point = 11)
    (hlocal : ∀ p : Point, ElevenFiveLocalRows (blockSystem cfg) p)
    (hglobal : ElevenFiveGlobalRows (blockSystem cfg))
    (hC : (blockSystem cfg).totalCircleCount = 40)
    (hfive : (blockSystem cfg).blockCount 5 = 7)
    (hmoment : elevenFiveSecondMoment (blockSystem cfg) = 39)
    (A B C : Finset (GeometricBlock cfg))
    (hAG : A ∈ elevenFiveC40M39DefectEdges (blockSystem cfg))
    (hBG : B ∈ elevenFiveC40M39DefectEdges (blockSystem cfg))
    (hCG : C ∈ elevenFiveC40M39DefectEdges (blockSystem cfg)) :
    ∃ p q r : Point,
      p ∈ (blockSystem cfg).commonSupport A ∧
      (blockSystem cfg).blockDegree 3 p = 12 ∧
      (blockSystem cfg).blockDegree 5 p = 3 ∧
      q ∈ (blockSystem cfg).commonSupport B ∧
      (blockSystem cfg).blockDegree 3 q = 12 ∧
      (blockSystem cfg).blockDegree 5 q = 3 ∧
      r ∈ (blockSystem cfg).commonSupport C ∧
      (blockSystem cfg).blockDegree 3 r = 12 ∧
      (blockSystem cfg).blockDegree 5 r = 3 := by
  obtain ⟨p, hpA, hp12, hp3⟩ :=
    elevenFive_c40_l14_b5_seven_m39_defectEdge_carrier
      cfg hpoint hlocal hglobal hC hfive hmoment A hAG
  obtain ⟨q, hqB, hq12, hq3⟩ :=
    elevenFive_c40_l14_b5_seven_m39_defectEdge_carrier
      cfg hpoint hlocal hglobal hC hfive hmoment B hBG
  obtain ⟨r, hrC, hr12, hr3⟩ :=
    elevenFive_c40_l14_b5_seven_m39_defectEdge_carrier
      cfg hpoint hlocal hglobal hC hfive hmoment C hCG
  exact ⟨p, q, r, hpA, hp12, hp3, hqB, hq12, hq3, hrC, hr12, hr3⟩

private theorem elevenFive_c40_l14_b5_seven_m39_three_edge_carriers_ne
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    (cfg : Configuration Point) (hpoint : Fintype.card Point = 11)
    (A B C : Finset (GeometricBlock cfg))
    (hAG : A ∈ elevenFiveC40M39DefectEdges (blockSystem cfg))
    (hBG : B ∈ elevenFiveC40M39DefectEdges (blockSystem cfg))
    (hCG : C ∈ elevenFiveC40M39DefectEdges (blockSystem cfg))
    (hAB : A ≠ B) (hAC : A ≠ C) (hBC : B ≠ C)
    (p q r : Point)
    (hpA : p ∈ (blockSystem cfg).commonSupport A)
    (hqB : q ∈ (blockSystem cfg).commonSupport B)
    (hrC : r ∈ (blockSystem cfg).commonSupport C)
    (hp3 : (blockSystem cfg).blockDegree 5 p = 3)
    (hq3 : (blockSystem cfg).blockDegree 5 q = 3) :
    p ≠ q ∧ p ≠ r ∧ q ≠ r := by
  have hAdata := Finset.mem_filter.mp
    (by simpa only [elevenFiveC40M39DefectEdges] using hAG)
  have hBdata := Finset.mem_filter.mp
    (by simpa only [elevenFiveC40M39DefectEdges] using hBG)
  have hCdata := Finset.mem_filter.mp
    (by simpa only [elevenFiveC40M39DefectEdges] using hCG)
  exact ⟨
    fiveBlock_singleton_edges_degreeThree_carriers_ne
      (blockSystem cfg) hpoint hAdata.1 hBdata.1 hAdata.2 hBdata.2 hAB
        hpA hqB hp3,
    fiveBlock_singleton_edges_degreeThree_carriers_ne
      (blockSystem cfg) hpoint hAdata.1 hCdata.1 hAdata.2 hCdata.2 hAC
        hpA hrC hp3,
    fiveBlock_singleton_edges_degreeThree_carriers_ne
      (blockSystem cfg) hpoint hBdata.1 hCdata.1 hBdata.2 hCdata.2 hBC
        hqB hrC hq3⟩

/-- The three M39 singleton edges have three pairwise different `(12,3)`
carriers. -/
theorem elevenFive_c40_l14_b5_seven_m39_three_distinct_carriers
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    (cfg : Configuration Point) (hpoint : Fintype.card Point = 11)
    (hlocal : ∀ p : Point, ElevenFiveLocalRows (blockSystem cfg) p)
    (hglobal : ElevenFiveGlobalRows (blockSystem cfg))
    (hC : (blockSystem cfg).totalCircleCount = 40)
    (hfive : (blockSystem cfg).blockCount 5 = 7)
    (hmoment : elevenFiveSecondMoment (blockSystem cfg) = 39)
    (hnodisjoint : ∀ b ∈ (blockSystem cfg).blocksOfSize 5,
      ∀ c ∈ (blockSystem cfg).blocksOfSize 5, b ≠ c →
        ((blockSystem cfg).support b ∩
          (blockSystem cfg).support c).card ≠ 0) :
    ∃ p q r : Point, p ≠ q ∧ p ≠ r ∧ q ≠ r ∧
      (blockSystem cfg).blockDegree 3 p = 12 ∧
      (blockSystem cfg).blockDegree 5 p = 3 ∧
      (blockSystem cfg).blockDegree 3 q = 12 ∧
      (blockSystem cfg).blockDegree 5 q = 3 ∧
      (blockSystem cfg).blockDegree 3 r = 12 ∧
      (blockSystem cfg).blockDegree 5 r = 3 := by
  classical
  let S := blockSystem cfg
  let G := elevenFiveC40M39DefectEdges S
  have hGcard : G.card = 3 :=
    elevenFive_c40_l14_b5_seven_m39_defectEdges_card_three
      S (by simpa [S] using hfive) (by simpa [S] using hmoment)
        (by simpa [S] using hnodisjoint)
  obtain ⟨A, B, C, hAB, hAC, hBC, hGeq⟩ := Finset.card_eq_three.mp hGcard
  have hAG : A ∈ G := by rw [hGeq]; simp
  have hBG : B ∈ G := by rw [hGeq]; simp
  have hCG : C ∈ G := by rw [hGeq]; simp
  change A ∈ elevenFiveC40M39DefectEdges (blockSystem cfg) at hAG
  change B ∈ elevenFiveC40M39DefectEdges (blockSystem cfg) at hBG
  change C ∈ elevenFiveC40M39DefectEdges (blockSystem cfg) at hCG
  obtain ⟨p, q, r, hpA, hp12, hp3, hqB, hq12, hq3,
      hrC, hr12, hr3⟩ :=
    elevenFive_c40_l14_b5_seven_m39_three_edge_carriers
      cfg hpoint hlocal hglobal hC hfive hmoment A B C hAG hBG hCG
  obtain ⟨hpq, hpr, hqr⟩ :=
    elevenFive_c40_l14_b5_seven_m39_three_edge_carriers_ne
      cfg hpoint A B C hAG hBG hCG hAB hAC hBC
        p q r hpA hqB hrC hp3 hq3
  exact ⟨p, q, r, hpq, hpr, hqr, hp12, hp3, hq12, hq3, hr12, hr3⟩

theorem elevenFive_c40_l14_b5_seven_m39_threeDegreeTwelve_count_ge_three
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    (cfg : Configuration Point) (hpoint : Fintype.card Point = 11)
    (hlocal : ∀ p : Point, ElevenFiveLocalRows (blockSystem cfg) p)
    (hglobal : ElevenFiveGlobalRows (blockSystem cfg))
    (hC : (blockSystem cfg).totalCircleCount = 40)
    (hfive : (blockSystem cfg).blockCount 5 = 7)
    (hmoment : elevenFiveSecondMoment (blockSystem cfg) = 39)
    (hnodisjoint : ∀ b ∈ (blockSystem cfg).blocksOfSize 5,
      ∀ c ∈ (blockSystem cfg).blocksOfSize 5, b ≠ c →
        ((blockSystem cfg).support b ∩
          (blockSystem cfg).support c).card ≠ 0) :
    3 ≤ ((Finset.univ : Finset Point).filter fun p =>
      (blockSystem cfg).blockDegree 3 p = 12).card := by
  classical
  obtain ⟨p, q, r, hpq, hpr, hqr, hp12, _hp3,
    hq12, _hq3, hr12, _hr3⟩ :=
      elevenFive_c40_l14_b5_seven_m39_three_distinct_carriers
        cfg hpoint hlocal hglobal hC hfive hmoment hnodisjoint
  let P : Finset Point := {p, q, r}
  let N12 := (Finset.univ : Finset Point).filter fun x =>
    (blockSystem cfg).blockDegree 3 x = 12
  have hPcard : P.card = 3 := by simp [P, hpq, hpr, hqr]
  have hPsub : P ⊆ N12 := by
    intro x hx
    simp only [P, Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl <;> simp [N12, hp12, hq12, hr12]
  have := Finset.card_le_card hPsub
  simpa [N12, hPcard] using this

/-- The two degree-four pivots have total three-degree at most `21`.
Three distinct low degree-twelve singleton carriers already consume three
of the at most four degree-twelve points, so both highs cannot be twelve. -/
theorem elevenFive_c40_l14_b5_seven_m39_high_threeMass_le_twentyOne
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    (cfg : Configuration Point) (hpoint : Fintype.card Point = 11)
    (hlocal : ∀ p : Point, ElevenFiveLocalRows (blockSystem cfg) p)
    (hglobal : ElevenFiveGlobalRows (blockSystem cfg))
    (hC : (blockSystem cfg).totalCircleCount = 40)
    (hL : elevenFiveLineTotal (blockSystem cfg) = 14)
    (hfive : (blockSystem cfg).blockCount 5 = 7)
    (hmoment : elevenFiveSecondMoment (blockSystem cfg) = 39)
    (hnodisjoint : ∀ b ∈ (blockSystem cfg).blocksOfSize 5,
      ∀ c ∈ (blockSystem cfg).blocksOfSize 5, b ≠ c →
        ((blockSystem cfg).support b ∩
          (blockSystem cfg).support c).card ≠ 0) :
    (∑ p ∈ (Finset.univ : Finset Point).filter
      (fun p => (blockSystem cfg).blockDegree 5 p = 4),
        (blockSystem cfg).blockDegree 3 p) ≤ 21 := by
  classical
  let S := blockSystem cfg
  let H := (Finset.univ : Finset Point).filter fun p => S.blockDegree 5 p = 4
  let N12 := (Finset.univ : Finset Point).filter fun p => S.blockDegree 3 p = 12
  obtain ⟨hHcount, _hthree, _hfiveValues⟩ :=
    elevenFive_c40_l14_b5_seven_secondMoment_thirtyNine_profile
      S hpoint (by simpa [S] using hlocal) (by simpa [S] using hglobal)
        (by simpa [S] using hfive) (by simpa [S] using hmoment)
  have hHcard : H.card = 2 := by simpa [H] using hHcount
  obtain ⟨x, y, hxy, hHeq⟩ := Finset.card_eq_two.mp hHcard
  have hxH : x ∈ H := by rw [hHeq]; simp
  have hyH : y ∈ H := by rw [hHeq]; simp
  obtain ⟨_hN6, hN9N12, hthreeValues⟩ :=
    elevenFive_c40_l14_b5_seven_threeDegree_census
      S hpoint (by simpa [S] using hlocal) (by simpa [S] using hglobal)
        (by simpa [S] using hC) (by simpa [S] using hL)
          (by simpa [S] using hfive)
  have hN12le : N12.card ≤ 4 := by
    have hrow :
        ((Finset.univ : Finset Point).filter fun p => S.blockDegree 3 p = 9).card +
          2 * N12.card = 9 := by simpa only [N12] using hN9N12
    omega
  obtain ⟨p, q, r, hpq, hpr, hqr, hp12, hp3,
    hq12, hq3, hr12, hr3⟩ :=
      elevenFive_c40_l14_b5_seven_m39_three_distinct_carriers
        cfg hpoint hlocal hglobal hC hfive hmoment hnodisjoint
  let P : Finset Point := {p, q, r}
  have hPcard : P.card = 3 := by simp [P, hpq, hpr, hqr]
  have hPsub : P ⊆ N12 := by
    intro z hz
    simp only [P, Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl | rfl <;> simp [N12, S, hp12, hq12, hr12]
  have hPdisH : Disjoint P H := by
    rw [Finset.disjoint_left]
    intro z hzP hzH
    have hz4 := (Finset.mem_filter.mp hzH).2
    simp only [P, Finset.mem_insert, Finset.mem_singleton] at hzP
    have hp3S : S.blockDegree 5 p = 3 := by simpa [S] using hp3
    have hq3S : S.blockDegree 5 q = 3 := by simpa [S] using hq3
    have hr3S : S.blockDegree 5 r = 3 := by simpa [S] using hr3
    rcases hzP with rfl | rfl | rfl <;> omega
  by_contra hnot
  have hsumHigh :
      S.blockDegree 3 x + S.blockDegree 3 y > 21 := by
    have hsum : (∑ p ∈ H, S.blockDegree 3 p) =
        S.blockDegree 3 x + S.blockDegree 3 y := by
      rw [hHeq]
      simp [hxy, Nat.add_comm]
    simpa [S, H, hsum] using hnot
  have hx12 : S.blockDegree 3 x = 12 := by
    rcases hthreeValues x with hx6 | hx9 | hx12 <;>
      rcases hthreeValues y with hy6 | hy9 | hy12 <;> omega
  have hy12 : S.blockDegree 3 y = 12 := by
    rcases hthreeValues x with hx6 | hx9 | hx12 <;>
      rcases hthreeValues y with hy6 | hy9 | hy12 <;> omega
  have hHsub : H ⊆ N12 := by
    intro z hz
    rw [hHeq] at hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl <;> simp [N12, hx12, hy12]
  have hUnionSub : P ∪ H ⊆ N12 := Finset.union_subset hPsub hHsub
  have hUnionCard : (P ∪ H).card = 5 := by
    rw [Finset.card_union_of_disjoint hPdisH, hPcard, hHcard]
  have hle := Finset.card_le_card hUnionSub
  rw [hUnionCard] at hle
  omega

/-- Equality `high mass = 21` identifies one high `(12,4)` pivot and one
high `(9,4)` pivot, and forces the global counts `N₁₂=4`, `N₉=1`. -/
theorem elevenFive_c40_l14_b5_seven_m39_high_pair_of_mass_twentyOne
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    (cfg : Configuration Point) (hpoint : Fintype.card Point = 11)
    (hlocal : ∀ p : Point, ElevenFiveLocalRows (blockSystem cfg) p)
    (hglobal : ElevenFiveGlobalRows (blockSystem cfg))
    (hC : (blockSystem cfg).totalCircleCount = 40)
    (hL : elevenFiveLineTotal (blockSystem cfg) = 14)
    (hfive : (blockSystem cfg).blockCount 5 = 7)
    (hmoment : elevenFiveSecondMoment (blockSystem cfg) = 39)
    (hnodisjoint : ∀ b ∈ (blockSystem cfg).blocksOfSize 5,
      ∀ c ∈ (blockSystem cfg).blocksOfSize 5, b ≠ c →
        ((blockSystem cfg).support b ∩
          (blockSystem cfg).support c).card ≠ 0)
    (hhigh : (∑ p ∈ (Finset.univ : Finset Point).filter
      (fun p => (blockSystem cfg).blockDegree 5 p = 4),
        (blockSystem cfg).blockDegree 3 p) = 21) :
    ∃ a z : Point, a ≠ z ∧
      (blockSystem cfg).blockDegree 5 a = 4 ∧
      (blockSystem cfg).blockDegree 3 a = 12 ∧
      (blockSystem cfg).blockDegree 5 z = 4 ∧
      (blockSystem cfg).blockDegree 3 z = 9 ∧
      ((Finset.univ : Finset Point).filter fun p =>
        (blockSystem cfg).blockDegree 3 p = 12).card = 4 ∧
      ((Finset.univ : Finset Point).filter fun p =>
        (blockSystem cfg).blockDegree 3 p = 9).card = 1 := by
  classical
  let S := blockSystem cfg
  let H := (Finset.univ : Finset Point).filter fun p => S.blockDegree 5 p = 4
  let N12 := (Finset.univ : Finset Point).filter fun p => S.blockDegree 3 p = 12
  let N9 := (Finset.univ : Finset Point).filter fun p => S.blockDegree 3 p = 9
  obtain ⟨hHcount, _hthree, _hfiveValues⟩ :=
    elevenFive_c40_l14_b5_seven_secondMoment_thirtyNine_profile
      S hpoint (by simpa [S] using hlocal) (by simpa [S] using hglobal)
        (by simpa [S] using hfive) (by simpa [S] using hmoment)
  have hHcard : H.card = 2 := by simpa [H] using hHcount
  obtain ⟨x, y, hxy, hHeq⟩ := Finset.card_eq_two.mp hHcard
  have hxH : x ∈ H := by rw [hHeq]; simp
  have hyH : y ∈ H := by rw [hHeq]; simp
  have hx4 : S.blockDegree 5 x = 4 := (Finset.mem_filter.mp hxH).2
  have hy4 : S.blockDegree 5 y = 4 := (Finset.mem_filter.mp hyH).2
  have hsumXY : S.blockDegree 3 x + S.blockDegree 3 y = 21 := by
    have hhigh' : (∑ p ∈ H, S.blockDegree 3 p) = 21 := by
      simpa [S, H] using hhigh
    rw [hHeq] at hhigh'
    simpa [hxy, Nat.add_comm] using hhigh'
  obtain ⟨_hN6, hN9N12, hthreeValues⟩ :=
    elevenFive_c40_l14_b5_seven_threeDegree_census
      S hpoint (by simpa [S] using hlocal) (by simpa [S] using hglobal)
        (by simpa [S] using hC) (by simpa [S] using hL)
          (by simpa [S] using hfive)
  obtain ⟨a, z, haz, haH, hzH, ha12, hz9⟩ :
      ∃ a z : Point, a ≠ z ∧ a ∈ H ∧ z ∈ H ∧
        S.blockDegree 3 a = 12 ∧ S.blockDegree 3 z = 9 := by
    rcases hthreeValues x with hx6 | hx9 | hx12 <;>
      rcases hthreeValues y with hy6 | hy9 | hy12
    all_goals try omega
    · exact ⟨y, x, Ne.symm hxy, hyH, hxH, hy12, hx9⟩
    · exact ⟨x, y, hxy, hxH, hyH, hx12, hy9⟩
  have ha4 : S.blockDegree 5 a = 4 := (Finset.mem_filter.mp haH).2
  have hz4 : S.blockDegree 5 z = 4 := (Finset.mem_filter.mp hzH).2
  obtain ⟨p, q, r, hpq, hpr, hqr, hp12, hp3,
    hq12, hq3, hr12, hr3⟩ :=
      elevenFive_c40_l14_b5_seven_m39_three_distinct_carriers
        cfg hpoint hlocal hglobal hC hfive hmoment hnodisjoint
  let P : Finset Point := {p, q, r}
  have hPcard : P.card = 3 := by simp [P, hpq, hpr, hqr]
  have hPsub : P ⊆ N12 := by
    intro w hw
    simp only [P, Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with rfl | rfl | rfl <;> simp [N12, S, hp12, hq12, hr12]
  have haNotP : a ∉ P := by
    intro haP
    simp only [P, Finset.mem_insert, Finset.mem_singleton] at haP
    have hp3S : S.blockDegree 5 p = 3 := by simpa [S] using hp3
    have hq3S : S.blockDegree 5 q = 3 := by simpa [S] using hq3
    have hr3S : S.blockDegree 5 r = 3 := by simpa [S] using hr3
    rcases haP with rfl | rfl | rfl <;> omega
  have hInsertSub : insert a P ⊆ N12 := by
    intro w hw
    simp only [Finset.mem_insert] at hw
    rcases hw with rfl | hw
    · simp [N12, ha12]
    · exact hPsub hw
  have hInsertCard : (insert a P).card = 4 := by
    rw [Finset.card_insert_of_notMem haNotP, hPcard]
  have hN12ge : 4 ≤ N12.card := by
    have hle := Finset.card_le_card hInsertSub
    rw [hInsertCard] at hle
    exact hle
  have hN9N12' : N9.card + 2 * N12.card = 9 := by
    simpa only [N9, N12] using hN9N12
  have hN12card : N12.card = 4 := by omega
  have hN9card : N9.card = 1 := by omega
  exact ⟨a, z, haz, by simpa [S] using ha4, by simpa [S] using ha12,
    by simpa [S] using hz4, by simpa [S] using hz9,
    by simpa only [S, N12] using hN12card,
    by simpa only [S, N9] using hN9card⟩

/-- A defect-degree-two five-block has three-mass at least `42`: its five
points contribute the universal baseline `5 * 6`, and its two distinct
singleton carriers contribute six additional units each. -/
theorem elevenFive_c40_l14_b5_seven_m39_threeMass_ge_fortyTwo_of_degreeTwo
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    (cfg : Configuration Point) (hpoint : Fintype.card Point = 11)
    (hlocal : ∀ p : Point, ElevenFiveLocalRows (blockSystem cfg) p)
    (hglobal : ElevenFiveGlobalRows (blockSystem cfg))
    (hC : (blockSystem cfg).totalCircleCount = 40)
    (hfive : (blockSystem cfg).blockCount 5 = 7)
    (hmoment : elevenFiveSecondMoment (blockSystem cfg) = 39)
    (b : GeometricBlock cfg)
    (hb : b ∈ (blockSystem cfg).blocksOfSize 5)
    (hdegree : elevenFiveC40M39DefectDegree (blockSystem cfg) b = 2) :
    42 ≤ ∑ p ∈ (blockSystem cfg).support b,
      (blockSystem cfg).blockDegree 3 p := by
  classical
  let S := blockSystem cfg
  obtain ⟨p, q, hpq, hpBcfg, hqBcfg, hp12, _hp3, hq12, _hq3⟩ :=
    elevenFive_c40_l14_b5_seven_m39_degreeTwo_carriers
      cfg hpoint hlocal hglobal hC hfive hmoment b hb hdegree
  have hpB : p ∈ S.support b := by
    simpa [S, blockSystem, geometricBlockSystem, geometricBlockSupport] using
      hpBcfg
  have hqB : q ∈ S.support b := by
    simpa [S, blockSystem, geometricBlockSystem, geometricBlockSupport] using
      hqBcfg
  have hp12S : S.blockDegree 3 p = 12 := by simpa [S] using hp12
  have hq12S : S.blockDegree 3 q = 12 := by simpa [S] using hq12
  have hbcard : (S.support b).card = 5 := by
    exact S.mem_blocksOfSize.mp (by simpa [S] using hb)
  have hpointLower (x : Point) (hx : x ∈ S.support b) :
      6 + (if x = p then 6 else 0) + (if x = q then 6 else 0) ≤
        S.blockDegree 3 x := by
    by_cases hxp : x = p
    · subst x
      simp [hp12S, hpq]
    · by_cases hxq : x = q
      · subst x
        simp [hq12S, hxp]
      · rcases elevenFive_c40_threeDegree_values
          S x (by simpa [S] using hlocal x) (by simpa [S] using hC) with
          h6 | h9 | h12
        all_goals simp [hxp, hxq]
        all_goals omega
  have hsum :
      (∑ x ∈ S.support b,
        (6 + (if x = p then 6 else 0) + (if x = q then 6 else 0))) ≤
          ∑ x ∈ S.support b, S.blockDegree 3 x := by
    exact Finset.sum_le_sum (fun x hx => hpointLower x hx)
  have hleft :
      (∑ x ∈ S.support b,
        (6 + (if x = p then 6 else 0) + (if x = q then 6 else 0))) = 42 := by
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
    simp [hbcard, hpB, hqB]
  change 42 ≤ ∑ x ∈ S.support b, S.blockDegree 3 x
  rw [← hleft]
  exact hsum

/-- A defect-degree-one five-block has three-mass at least `36`: its
unique singleton edge supplies one `(12,3)` carrier. -/
theorem elevenFive_c40_l14_b5_seven_m39_threeMass_ge_thirtySix_of_degreeOne
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    (cfg : Configuration Point) (hpoint : Fintype.card Point = 11)
    (hlocal : ∀ p : Point, ElevenFiveLocalRows (blockSystem cfg) p)
    (hglobal : ElevenFiveGlobalRows (blockSystem cfg))
    (hC : (blockSystem cfg).totalCircleCount = 40)
    (hfive : (blockSystem cfg).blockCount 5 = 7)
    (hmoment : elevenFiveSecondMoment (blockSystem cfg) = 39)
    (b : GeometricBlock cfg)
    (hb : b ∈ (blockSystem cfg).blocksOfSize 5)
    (hdegree : elevenFiveC40M39DefectDegree (blockSystem cfg) b = 1) :
    36 ≤ ∑ p ∈ (blockSystem cfg).support b,
      (blockSystem cfg).blockDegree 3 p := by
  classical
  let S := blockSystem cfg
  let N := elevenFiveC40M39SingletonNeighbours S b
  have hNcard : N.card = 1 := by
    simpa [N, elevenFiveC40M39DefectDegree] using hdegree
  obtain ⟨c, hNeq⟩ := Finset.card_eq_one.mp hNcard
  have hcN : c ∈ N := by rw [hNeq]; simp
  have hcSpec := Finset.mem_filter.mp (by simpa only [N] using hcN)
  have hcErase := Finset.mem_erase.mp hcSpec.1
  have hc : c ∈ S.blocksOfSize 5 := hcErase.2
  have hbc : b ≠ c := Ne.symm hcErase.1
  let A : Finset (GeometricBlock cfg) := {b, c}
  have hA : A ∈ elevenFiveC40M39DefectEdges S := by
    apply Finset.mem_filter.mpr
    constructor
    · apply Finset.mem_powersetCard.mpr
      constructor
      · intro x hx
        simp only [A, Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl
        · simpa [S] using hb
        · exact hc
      · simp [A, hbc]
    · simpa [A, S.commonSupport_pair] using hcSpec.2
  obtain ⟨p, hpA, hp12, _hp3⟩ :=
    elevenFive_c40_l14_b5_seven_m39_defectEdge_carrier
      cfg hpoint hlocal hglobal hC hfive hmoment A (by simpa [S] using hA)
  have hpB : p ∈ S.support b := by
    have hpPair : p ∈ S.support b ∩ S.support c := by
      simpa [A, S.commonSupport_pair, S] using hpA
    exact (Finset.mem_inter.mp hpPair).1
  have hp12S : S.blockDegree 3 p = 12 := by simpa [S] using hp12
  have hbcard : (S.support b).card = 5 :=
    S.mem_blocksOfSize.mp (by simpa [S] using hb)
  have hpointLower (x : Point) (hx : x ∈ S.support b) :
      6 + (if x = p then 6 else 0) ≤ S.blockDegree 3 x := by
    by_cases hxp : x = p
    · subst x
      simp [hp12S]
    · rcases elevenFive_c40_threeDegree_values
        S x (by simpa [S] using hlocal x) (by simpa [S] using hC) with
        h6 | h9 | h12
      all_goals simp [hxp]
      all_goals omega
  have hsum :
      (∑ x ∈ S.support b, (6 + (if x = p then 6 else 0))) ≤
        ∑ x ∈ S.support b, S.blockDegree 3 x :=
    Finset.sum_le_sum (fun x hx => hpointLower x hx)
  have hleft :
      (∑ x ∈ S.support b, (6 + (if x = p then 6 else 0))) = 36 := by
    rw [Finset.sum_add_distrib]
    simp [hbcard, hpB]
  change 36 ≤ ∑ x ∈ S.support b, S.blockDegree 3 x
  rw [← hleft]
  exact hsum

/-- A clean five-block (all six other five-blocks meet it twice) has
three-mass at least `48`; otherwise it is exactly the page-cap endpoint.
The zero five-line census ensures that the selected geometric block is a
circle, so no extra kind hypothesis is needed. -/
theorem elevenFive_c40_l14_b5_seven_clean_threeMass_ge_fortyEight
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    (cfg : Configuration Point) (hpoint : Fintype.card Point = 11)
    (hcap : BlockSizeCap (blockSystem cfg) 5)
    (hlocal : ∀ p : Point, ElevenFiveLocalRows (blockSystem cfg) p)
    (hglobal : ElevenFiveGlobalRows (blockSystem cfg))
    (hC : (blockSystem cfg).totalCircleCount = 40)
    (hL : elevenFiveLineTotal (blockSystem cfg) = 14)
    (hfive : (blockSystem cfg).blockCount 5 = 7)
    (b : GeometricBlock cfg)
    (hb : b ∈ (blockSystem cfg).blocksOfSize 5)
    (hallAt : ∀ c ∈ (blockSystem cfg).blocksOfSize 5, c ≠ b →
      ((blockSystem cfg).support b ∩ (blockSystem cfg).support c).card = 2) :
    48 ≤ ∑ p ∈ (blockSystem cfg).support b,
      (blockSystem cfg).blockDegree 3 p := by
  classical
  let S := blockSystem cfg
  have hlineFive := c40FourteenSeven_lineCount_five_eq_zero
    S (by simpa [S] using hglobal) (by simpa [S] using hC)
      (by simpa [S] using hL) (by simpa [S] using hfive)
  by_contra hnot
  have hmassLow :
      (∑ p ∈ S.support b, S.blockDegree 3 p) ≤ 47 := by
    change ¬ 48 ≤ ∑ p ∈ S.support b, S.blockDegree 3 p at hnot
    omega
  rcases b with L | Gamma
  · have hbLine : (Sum.inl L : GeometricBlock cfg) ∈
        S.lineBlocksOfSize 5 := by
      apply S.mem_blocksOfKindSize.mpr
      refine ⟨?_, S.mem_blocksOfSize.mp (by simpa [S] using hb)⟩
      simp [S, blockSystem, geometricBlockSystem, geometricBlockKind]
    have hlineCard : (S.lineBlocksOfSize 5).card = 0 := by
      simpa [BlockSystem.lineCount] using hlineFive
    exact (by
      have hpositive := Finset.card_pos.mpr ⟨Sum.inl L, hbLine⟩
      omega)
  · have hD : (circleTrace cfg Gamma.1).card = 5 := by
      have hsize := S.mem_blocksOfSize.mp (by simpa [S] using hb)
      simpa [S, blockSystem, geometricBlockSystem,
        geometricBlockSupport] using hsize
    have hmass :
        (∑ p ∈ circleTrace cfg Gamma.1,
          (blockSystem cfg).blockDegree 3 p) ≤ 47 := by
      simpa [S, blockSystem, geometricBlockSystem,
        geometricBlockSupport] using hmassLow
    exact elevenFive_c40_l14_b5_seven_doubleNeighbourCircle_impossible_of_pageCap
      cfg Gamma hpoint hcap hlocal hD hfive
        (by
          intro c hc hcb
          exact hallAt c hc hcb)
        (by omega)

/-- The sharpened page-cap endpoint also excludes the boundary mass `48`.
Thus a clean five-block has mass at least `49`. -/
theorem elevenFive_c40_l14_b5_seven_clean_threeMass_ge_fortyNine
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    (cfg : Configuration Point) (hpoint : Fintype.card Point = 11)
    (hcap : BlockSizeCap (blockSystem cfg) 5)
    (hlocal : ∀ p : Point, ElevenFiveLocalRows (blockSystem cfg) p)
    (hglobal : ElevenFiveGlobalRows (blockSystem cfg))
    (hC : (blockSystem cfg).totalCircleCount = 40)
    (hL : elevenFiveLineTotal (blockSystem cfg) = 14)
    (hfive : (blockSystem cfg).blockCount 5 = 7)
    (b : GeometricBlock cfg)
    (hb : b ∈ (blockSystem cfg).blocksOfSize 5)
    (hallAt : ∀ c ∈ (blockSystem cfg).blocksOfSize 5, c ≠ b →
      ((blockSystem cfg).support b ∩ (blockSystem cfg).support c).card = 2) :
    49 ≤ ∑ p ∈ (blockSystem cfg).support b,
      (blockSystem cfg).blockDegree 3 p := by
  classical
  let S := blockSystem cfg
  by_contra hnot
  have hmassLow :
      (∑ p ∈ S.support b, S.blockDegree 3 p) ≤ 48 := by
    change ¬ 49 ≤ ∑ p ∈ S.support b, S.blockDegree 3 p at hnot
    omega
  have hlineFive := c40FourteenSeven_lineCount_five_eq_zero
    S (by simpa [S] using hglobal) (by simpa [S] using hC)
      (by simpa [S] using hL) (by simpa [S] using hfive)
  rcases b with L | Gamma
  · have hbLine : (Sum.inl L : GeometricBlock cfg) ∈
        S.lineBlocksOfSize 5 := by
      apply S.mem_blocksOfKindSize.mpr
      refine ⟨?_, S.mem_blocksOfSize.mp (by simpa [S] using hb)⟩
      simp [S, blockSystem, geometricBlockSystem, geometricBlockKind]
    have hlineCard : (S.lineBlocksOfSize 5).card = 0 := by
      simpa [BlockSystem.lineCount] using hlineFive
    have hpositive := Finset.card_pos.mpr ⟨Sum.inl L, hbLine⟩
    omega
  · have hD : (circleTrace cfg Gamma.1).card = 5 := by
      have hsize := S.mem_blocksOfSize.mp (by simpa [S] using hb)
      simpa [S, blockSystem, geometricBlockSystem,
        geometricBlockSupport] using hsize
    have hmass :
        (∑ p ∈ circleTrace cfg Gamma.1,
          (blockSystem cfg).blockDegree 3 p) ≤ 48 := by
      simpa [S, blockSystem, geometricBlockSystem,
        geometricBlockSupport] using hmassLow
    exact elevenFive_c40_l14_b5_seven_doubleNeighbourCircle_impossible_of_pageCap
      cfg Gamma hpoint hcap hlocal hD hfive
        (by
          intro c hc hcb
          exact hallAt c hc hcb)
        hmass

/-- Defect degree zero is exactly the clean condition in the no-disjoint
face: every other five-block meets the selected block twice. -/
theorem elevenFive_c40_m39_all_inter_two_of_defectDegree_zero
    {Point : Type u} {Block : Type v} [Fintype Point] [Fintype Block]
    [DecidableEq Point] [DecidableEq Block]
    (S : BlockSystem Point Block) (b : Block)
    (hb : b ∈ S.blocksOfSize 5)
    (hdegree : elevenFiveC40M39DefectDegree S b = 0)
    (hnodisjoint : ∀ c ∈ S.blocksOfSize 5, b ≠ c →
      (S.support b ∩ S.support c).card ≠ 0) :
    ∀ c ∈ S.blocksOfSize 5, c ≠ b →
      (S.support b ∩ S.support c).card = 2 := by
  classical
  intro c hc hcb
  have hbc : b ≠ c := Ne.symm hcb
  have hne := hnodisjoint c hc hbc
  have hlt := S.distinct_block_inter_card_lt_three hbc
  have hle : (S.support b ∩ S.support c).card ≤ 2 := by omega
  by_contra hnotTwo
  have hone : (S.support b ∩ S.support c).card = 1 := by omega
  have hcN : c ∈ elevenFiveC40M39SingletonNeighbours S b := by
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_erase.mpr ⟨hcb, hc⟩, hone⟩
  have hpositive := Finset.card_pos.mpr ⟨c, hcN⟩
  change (elevenFiveC40M39SingletonNeighbours S b).card = 0 at hdegree
  omega

/-- The triangle defect shape is impossible.  Its four clean blocks have
mass at least `48`, and its three degree-two blocks have mass at least
`42`, giving `318 > 303`. -/
theorem elevenFive_c40_l14_b5_seven_m39_triangle_impossible
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    (cfg : Configuration Point) (hpoint : Fintype.card Point = 11)
    (hcap : BlockSizeCap (blockSystem cfg) 5)
    (hlocal : ∀ p : Point, ElevenFiveLocalRows (blockSystem cfg) p)
    (hglobal : ElevenFiveGlobalRows (blockSystem cfg))
    (hC : (blockSystem cfg).totalCircleCount = 40)
    (hL : elevenFiveLineTotal (blockSystem cfg) = 14)
    (hfive : (blockSystem cfg).blockCount 5 = 7)
    (hmoment : elevenFiveSecondMoment (blockSystem cfg) = 39)
    (hnodisjoint : ∀ b ∈ (blockSystem cfg).blocksOfSize 5,
      ∀ c ∈ (blockSystem cfg).blocksOfSize 5, b ≠ c →
        ((blockSystem cfg).support b ∩
          (blockSystem cfg).support c).card ≠ 0)
    (htriangle : ElevenFiveC40M39Triangle (blockSystem cfg)) : False := by
  classical
  let S := blockSystem cfg
  let F := S.blocksOfSize 5
  let Z := F.filter fun b => elevenFiveC40M39DefectDegree S b = 0
  let O := F.filter fun b => elevenFiveC40M39DefectDegree S b = 1
  let T := F.filter fun b => elevenFiveC40M39DefectDegree S b = 2
  let mass : GeometricBlock cfg → ℕ := fun b =>
    ∑ p ∈ S.support b, S.blockDegree 3 p
  obtain ⟨hZcard, hOcard, hTcard⟩ :=
    elevenFive_c40_l14_b5_seven_m39_triangle_degree_counts
      S hpoint (by simpa [S] using hlocal) (by simpa [S] using hglobal)
        (by simpa [S] using hfive) (by simpa [S] using hmoment)
          (by simpa [S] using hnodisjoint) (by simpa [S] using htriangle)
  have hZcard' : Z.card = 4 := by simpa only [Z, F] using hZcard
  have hOcard' : O.card = 0 := by simpa only [O, F] using hOcard
  have hTcard' : T.card = 3 := by simpa only [T, F] using hTcard
  have hFcard : F.card = 7 := by
    simpa [F, S, BlockSystem.blockCount] using hfive
  have hmassPoint (b : GeometricBlock cfg) (hbF : b ∈ F) :
      (if elevenFiveC40M39DefectDegree S b = 0 then 48 else 42) ≤ mass b := by
    have hdegLe := htriangle.2.1 b (by simpa [F, S] using hbF)
    interval_cases hdeg : elevenFiveC40M39DefectDegree S b
    · simp [hdeg, mass]
      apply elevenFive_c40_l14_b5_seven_clean_threeMass_ge_fortyEight
        cfg hpoint hcap hlocal hglobal hC hL hfive b (by simpa [F, S] using hbF)
      exact elevenFive_c40_m39_all_inter_two_of_defectDegree_zero
        S b (by simpa [F] using hbF) hdeg
          (fun c hc hbc => hnodisjoint b (by simpa [F, S] using hbF)
            c (by simpa [S] using hc) hbc)
    · have hbO : b ∈ O := by simp [O, hbF, hdeg]
      have hpositive := Finset.card_pos.mpr ⟨b, hbO⟩
      omega
    · simp [hdeg, mass]
      exact elevenFive_c40_l14_b5_seven_m39_threeMass_ge_fortyTwo_of_degreeTwo
        cfg hpoint hlocal hglobal hC hfive hmoment b
          (by simpa [F, S] using hbF) (by simpa [S] using hdeg)
  have hmassLower :
      (∑ b ∈ F,
        if elevenFiveC40M39DefectDegree S b = 0 then 48 else 42) ≤
          ∑ b ∈ F, mass b :=
    Finset.sum_le_sum (fun b hb => hmassPoint b hb)
  have hweight :
      (∑ b ∈ F,
        if elevenFiveC40M39DefectDegree S b = 0 then 48 else 42) = 318 := by
    calc
      (∑ b ∈ F,
        if elevenFiveC40M39DefectDegree S b = 0 then 48 else 42) =
          ∑ b ∈ F, (42 +
            if elevenFiveC40M39DefectDegree S b = 0 then 6 else 0) := by
        apply Finset.sum_congr rfl
        intro b _hb
        by_cases hzero : elevenFiveC40M39DefectDegree S b = 0 <;>
          simp [hzero]
      _ = 318 := by
        rw [Finset.sum_add_distrib]
        simp [F, Z, ← Finset.sum_filter, hFcard, hZcard']
  have hweighted :=
    elevenFive_c40_l14_b5_seven_m39_weighted_three_five_le_303
      S hpoint (by simpa [S] using hlocal) (by simpa [S] using hglobal)
        (by simpa [S] using hC) (by simpa [S] using hL)
          (by simpa [S] using hfive) (by simpa [S] using hmoment)
  have hmassUpper : (∑ b ∈ F, mass b) ≤ 303 := by
    have hfubini := elevenFive_fiveBlock_threeMass_sum_eq_weighted S
    simpa [F, mass] using hfubini.trans_le hweighted
  rw [hweight] at hmassLower
  omega

/-- The page-cap lower mass in the P4 shape is `300`:
`3 * 48 + 2 * 36 + 2 * 42`. -/
theorem elevenFive_c40_l14_b5_seven_m39_pathFour_weighted_ge_300
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    (cfg : Configuration Point) (hpoint : Fintype.card Point = 11)
    (hcap : BlockSizeCap (blockSystem cfg) 5)
    (hlocal : ∀ p : Point, ElevenFiveLocalRows (blockSystem cfg) p)
    (hglobal : ElevenFiveGlobalRows (blockSystem cfg))
    (hC : (blockSystem cfg).totalCircleCount = 40)
    (hL : elevenFiveLineTotal (blockSystem cfg) = 14)
    (hfive : (blockSystem cfg).blockCount 5 = 7)
    (hmoment : elevenFiveSecondMoment (blockSystem cfg) = 39)
    (hnodisjoint : ∀ b ∈ (blockSystem cfg).blocksOfSize 5,
      ∀ c ∈ (blockSystem cfg).blocksOfSize 5, b ≠ c →
        ((blockSystem cfg).support b ∩
          (blockSystem cfg).support c).card ≠ 0)
    (hpath : ElevenFiveC40M39PathFour (blockSystem cfg)) :
    300 ≤ ∑ p : Point,
      (blockSystem cfg).blockDegree 3 p *
        (blockSystem cfg).blockDegree 5 p := by
  classical
  let S := blockSystem cfg
  let F := S.blocksOfSize 5
  let Z := F.filter fun b => elevenFiveC40M39DefectDegree S b = 0
  let O := F.filter fun b => elevenFiveC40M39DefectDegree S b = 1
  let T := F.filter fun b => elevenFiveC40M39DefectDegree S b = 2
  let mass : GeometricBlock cfg → ℕ := fun b =>
    ∑ p ∈ S.support b, S.blockDegree 3 p
  obtain ⟨hZcard, hOcard, hTcard⟩ :=
    elevenFive_c40_l14_b5_seven_m39_pathFour_degree_counts
      S hpoint (by simpa [S] using hlocal) (by simpa [S] using hglobal)
        (by simpa [S] using hfive) (by simpa [S] using hmoment)
          (by simpa [S] using hnodisjoint) (by simpa [S] using hpath)
  have hZcard' : Z.card = 3 := by simpa only [Z, F] using hZcard
  have hOcard' : O.card = 2 := by simpa only [O, F] using hOcard
  have hTcard' : T.card = 2 := by simpa only [T, F] using hTcard
  have hmassPoint (b : GeometricBlock cfg) (hbF : b ∈ F) :
      (if elevenFiveC40M39DefectDegree S b = 0 then 48
        else if elevenFiveC40M39DefectDegree S b = 1 then 36 else 42) ≤
          mass b := by
    have hdegLe := hpath.2.1 b (by simpa [F, S] using hbF)
    interval_cases hdeg : elevenFiveC40M39DefectDegree S b
    · simp [hdeg, mass]
      apply elevenFive_c40_l14_b5_seven_clean_threeMass_ge_fortyEight
        cfg hpoint hcap hlocal hglobal hC hL hfive b (by simpa [F, S] using hbF)
      exact elevenFive_c40_m39_all_inter_two_of_defectDegree_zero
        S b (by simpa [F] using hbF) hdeg
          (fun c hc hbc => hnodisjoint b (by simpa [F, S] using hbF)
            c (by simpa [S] using hc) hbc)
    · simp [hdeg, mass]
      exact elevenFive_c40_l14_b5_seven_m39_threeMass_ge_thirtySix_of_degreeOne
        cfg hpoint hlocal hglobal hC hfive hmoment b
          (by simpa [F, S] using hbF) (by simpa [S] using hdeg)
    · simp [hdeg, mass]
      exact elevenFive_c40_l14_b5_seven_m39_threeMass_ge_fortyTwo_of_degreeTwo
        cfg hpoint hlocal hglobal hC hfive hmoment b
          (by simpa [F, S] using hbF) (by simpa [S] using hdeg)
  have hmassLower :
      (∑ b ∈ F, if elevenFiveC40M39DefectDegree S b = 0 then 48
        else if elevenFiveC40M39DefectDegree S b = 1 then 36 else 42) ≤
          ∑ b ∈ F, mass b :=
    Finset.sum_le_sum (fun b hb => hmassPoint b hb)
  have hweight :
      (∑ b ∈ F, if elevenFiveC40M39DefectDegree S b = 0 then 48
        else if elevenFiveC40M39DefectDegree S b = 1 then 36 else 42) = 300 := by
    have hcases (b : GeometricBlock cfg) (hb : b ∈ F) :=
      hpath.2.1 b (by simpa [F, S] using hb)
    calc
      (∑ b ∈ F, if elevenFiveC40M39DefectDegree S b = 0 then 48
        else if elevenFiveC40M39DefectDegree S b = 1 then 36 else 42) =
          ∑ b ∈ F,
            ((if elevenFiveC40M39DefectDegree S b = 0 then 48 else 0) +
             (if elevenFiveC40M39DefectDegree S b = 1 then 36 else 0) +
             (if elevenFiveC40M39DefectDegree S b = 2 then 42 else 0)) := by
        apply Finset.sum_congr rfl
        intro b hb
        have hle := hcases b hb
        interval_cases hdeg : elevenFiveC40M39DefectDegree S b <;> simp [hdeg]
      _ = 300 := by
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
        simp [Z, O, T, ← Finset.sum_filter, hZcard', hOcard', hTcard']
  have hfubini := elevenFive_fiveBlock_threeMass_sum_eq_weighted S
  have hmassWeighted : (∑ b ∈ F, mass b) =
      ∑ p : Point, S.blockDegree 3 p * S.blockDegree 5 p := by
    simpa [F, mass] using hfubini
  rw [hweight, hmassWeighted] at hmassLower
  simpa [S] using hmassLower

/-- In the P4 branch the two high pivots have total three-degree `21`, and
the global three-degree profile is exactly `N₁₂=4, N₉=1`.  The alternative
high sum `24` would add two high degree-twelve points to the three distinct
low singleton carriers, contradicting the universal census `N₁₂ ≤ 4`. -/
theorem elevenFive_c40_l14_b5_seven_m39_pathFour_high_profile
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    (cfg : Configuration Point) (hpoint : Fintype.card Point = 11)
    (hcap : BlockSizeCap (blockSystem cfg) 5)
    (hlocal : ∀ p : Point, ElevenFiveLocalRows (blockSystem cfg) p)
    (hglobal : ElevenFiveGlobalRows (blockSystem cfg))
    (hC : (blockSystem cfg).totalCircleCount = 40)
    (hL : elevenFiveLineTotal (blockSystem cfg) = 14)
    (hfive : (blockSystem cfg).blockCount 5 = 7)
    (hmoment : elevenFiveSecondMoment (blockSystem cfg) = 39)
    (hnodisjoint : ∀ b ∈ (blockSystem cfg).blocksOfSize 5,
      ∀ c ∈ (blockSystem cfg).blocksOfSize 5, b ≠ c →
        ((blockSystem cfg).support b ∩
          (blockSystem cfg).support c).card ≠ 0)
    (hpath : ElevenFiveC40M39PathFour (blockSystem cfg)) :
    (∑ p ∈ (Finset.univ : Finset Point).filter
        (fun p => (blockSystem cfg).blockDegree 5 p = 4),
          (blockSystem cfg).blockDegree 3 p) = 21 ∧
    ((Finset.univ : Finset Point).filter fun p =>
      (blockSystem cfg).blockDegree 3 p = 12).card = 4 ∧
    ((Finset.univ : Finset Point).filter fun p =>
      (blockSystem cfg).blockDegree 3 p = 9).card = 1 := by
  classical
  let S := blockSystem cfg
  let H := (Finset.univ : Finset Point).filter fun p => S.blockDegree 5 p = 4
  let N12 := (Finset.univ : Finset Point).filter fun p => S.blockDegree 3 p = 12
  let N9 := (Finset.univ : Finset Point).filter fun p => S.blockDegree 3 p = 9
  obtain ⟨hHcount, _hthree, _hfiveValues⟩ :=
    elevenFive_c40_l14_b5_seven_secondMoment_thirtyNine_profile
      S hpoint (by simpa [S] using hlocal) (by simpa [S] using hglobal)
        (by simpa [S] using hfive) (by simpa [S] using hmoment)
  have hHcard : H.card = 2 := by simpa [H] using hHcount
  obtain ⟨_hN6, hN9N12, hthreeValues⟩ :=
    elevenFive_c40_l14_b5_seven_threeDegree_census
      S hpoint (by simpa [S] using hlocal) (by simpa [S] using hglobal)
        (by simpa [S] using hC) (by simpa [S] using hL)
          (by simpa [S] using hfive)
  have hN9N12' : N9.card + 2 * N12.card = 9 := by
    simpa [N9, N12] using hN9N12
  have hweightedLower :=
    elevenFive_c40_l14_b5_seven_m39_pathFour_weighted_ge_300
      cfg hpoint hcap hlocal hglobal hC hL hfive hmoment hnodisjoint hpath
  have hweightedExact :=
    elevenFive_c40_l14_b5_seven_m39_weighted_eq_279_add_high
      S hpoint (by simpa [S] using hlocal) (by simpa [S] using hglobal)
        (by simpa [S] using hC) (by simpa [S] using hL)
          (by simpa [S] using hfive) (by simpa [S] using hmoment)
  have hHlower : 21 ≤ ∑ p ∈ H, S.blockDegree 3 p := by
    simpa [S, H] using (show 21 ≤
      ∑ p ∈ (Finset.univ : Finset Point).filter
        (fun p => S.blockDegree 5 p = 4), S.blockDegree 3 p by
          rw [hweightedExact] at hweightedLower
          omega)
  obtain ⟨x, y, hxy, hHeq⟩ := Finset.card_eq_two.mp hHcard
  have hxH : x ∈ H := by rw [hHeq]; simp
  have hyH : y ∈ H := by rw [hHeq]; simp
  have hx4 : S.blockDegree 5 x = 4 := (Finset.mem_filter.mp hxH).2
  have hy4 : S.blockDegree 5 y = 4 := (Finset.mem_filter.mp hyH).2
  have hHsum : (∑ p ∈ H, S.blockDegree 3 p) =
      S.blockDegree 3 x + S.blockDegree 3 y := by
    rw [hHeq]
    simp [hxy, Nat.add_comm]
  have hHcases : (∑ p ∈ H, S.blockDegree 3 p) = 21 ∨
      (∑ p ∈ H, S.blockDegree 3 p) = 24 := by
    rw [hHsum]
    rcases hthreeValues x with hx6 | hx9 | hx12 <;>
      rcases hthreeValues y with hy6 | hy9 | hy12 <;> omega
  obtain ⟨p, q, r, hpq, hpr, hqr, hp12, hp3,
    hq12, hq3, hr12, hr3⟩ :=
      elevenFive_c40_l14_b5_seven_m39_three_distinct_carriers
        cfg hpoint hlocal hglobal hC hfive hmoment hnodisjoint
  let P : Finset Point := {p, q, r}
  have hPcard : P.card = 3 := by simp [P, hpq, hpr, hqr]
  have hPsub : P ⊆ N12 := by
    intro z hz
    simp only [P, Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl | rfl <;> simp [N12, S, hp12, hq12, hr12]
  have hPdisH : Disjoint P H := by
    rw [Finset.disjoint_left]
    intro z hzP hzH
    have hz4 := (Finset.mem_filter.mp hzH).2
    simp only [P, Finset.mem_insert, Finset.mem_singleton] at hzP
    have hp3S : S.blockDegree 5 p = 3 := by simpa [S] using hp3
    have hq3S : S.blockDegree 5 q = 3 := by simpa [S] using hq3
    have hr3S : S.blockDegree 5 r = 3 := by simpa [S] using hr3
    rcases hzP with rfl | rfl | rfl <;> omega
  have hN12le : N12.card ≤ 4 := by omega
  have hHsum21 : (∑ p ∈ H, S.blockDegree 3 p) = 21 := by
    rcases hHcases with h21 | h24
    · exact h21
    · have hxySum : S.blockDegree 3 x + S.blockDegree 3 y = 24 := by omega
      have hx12 : S.blockDegree 3 x = 12 := by
        rcases hthreeValues x with hx6 | hx9 | hx12 <;>
          rcases hthreeValues y with hy6 | hy9 | hy12 <;> omega
      have hy12 : S.blockDegree 3 y = 12 := by
        rcases hthreeValues x with hx6 | hx9 | hx12 <;>
          rcases hthreeValues y with hy6 | hy9 | hy12 <;> omega
      have hHsub : H ⊆ N12 := by
        intro z hz
        rw [hHeq] at hz
        simp only [Finset.mem_insert, Finset.mem_singleton] at hz
        rcases hz with rfl | rfl <;> simp [N12, hx12, hy12]
      have hUnionSub : P ∪ H ⊆ N12 := Finset.union_subset hPsub hHsub
      have hUnionCard : (P ∪ H).card = 5 := by
        rw [Finset.card_union_of_disjoint hPdisH, hPcard, hHcard]
      have hle := Finset.card_le_card hUnionSub
      rw [hUnionCard] at hle
      omega
  have hxySum21 : S.blockDegree 3 x + S.blockDegree 3 y = 21 := by omega
  obtain ⟨z, hzH, hz12⟩ : ∃ z ∈ H, S.blockDegree 3 z = 12 := by
    rcases hthreeValues x with hx6 | hx9 | hx12 <;>
      rcases hthreeValues y with hy6 | hy9 | hy12
    all_goals try omega
    · exact ⟨y, hyH, hy12⟩
    · exact ⟨x, hxH, hx12⟩
  have hzNotP : z ∉ P := by
    intro hzP
    have hz4 := (Finset.mem_filter.mp hzH).2
    simp only [P, Finset.mem_insert, Finset.mem_singleton] at hzP
    have hp3S : S.blockDegree 5 p = 3 := by simpa [S] using hp3
    have hq3S : S.blockDegree 5 q = 3 := by simpa [S] using hq3
    have hr3S : S.blockDegree 5 r = 3 := by simpa [S] using hr3
    rcases hzP with rfl | rfl | rfl <;> omega
  have hInsertSub : insert z P ⊆ N12 := by
    intro w hw
    simp only [Finset.mem_insert] at hw
    rcases hw with rfl | hw
    · simp [N12, hz12]
    · exact hPsub hw
  have hInsertCard : (insert z P).card = 4 := by
    rw [Finset.card_insert_of_notMem hzNotP, hPcard]
  have hN12ge : 4 ≤ N12.card := by
    have hle := Finset.card_le_card hInsertSub
    rw [hInsertCard] at hle
    exact hle
  have hN12card : N12.card = 4 := by omega
  have hN9card : N9.card = 1 := by omega
  exact ⟨by simpa only [S, H] using hHsum21,
    by simpa only [S, N12] using hN12card,
    by simpa only [S, N9] using hN9card⟩

theorem elevenFive_c40_l14_b5_seven_m39_pathFour_block_mass_lower
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    (cfg : Configuration Point) (hpoint : Fintype.card Point = 11)
    (hcap : BlockSizeCap (blockSystem cfg) 5)
    (hlocal : ∀ p : Point, ElevenFiveLocalRows (blockSystem cfg) p)
    (hglobal : ElevenFiveGlobalRows (blockSystem cfg))
    (hC : (blockSystem cfg).totalCircleCount = 40)
    (hL : elevenFiveLineTotal (blockSystem cfg) = 14)
    (hfive : (blockSystem cfg).blockCount 5 = 7)
    (hmoment : elevenFiveSecondMoment (blockSystem cfg) = 39)
    (hnodisjoint : ∀ b ∈ (blockSystem cfg).blocksOfSize 5,
      ∀ c ∈ (blockSystem cfg).blocksOfSize 5, b ≠ c →
        ((blockSystem cfg).support b ∩
          (blockSystem cfg).support c).card ≠ 0)
    (hpath : ElevenFiveC40M39PathFour (blockSystem cfg))
    (b : GeometricBlock cfg) (hb : b ∈ (blockSystem cfg).blocksOfSize 5) :
    (if elevenFiveC40M39DefectDegree (blockSystem cfg) b = 0 then 48
      else if elevenFiveC40M39DefectDegree (blockSystem cfg) b = 1 then 36
      else 42) ≤
        ∑ p ∈ (blockSystem cfg).support b,
          (blockSystem cfg).blockDegree 3 p := by
  have hdegLe := hpath.2.1 b hb
  interval_cases hdeg :
      elevenFiveC40M39DefectDegree (blockSystem cfg) b
  · simp [hdeg]
    apply elevenFive_c40_l14_b5_seven_clean_threeMass_ge_fortyEight
      cfg hpoint hcap hlocal hglobal hC hL hfive b hb
    exact elevenFive_c40_m39_all_inter_two_of_defectDegree_zero
      (blockSystem cfg) b hb hdeg
        (fun c hc hbc => hnodisjoint b hb c hc hbc)
  · simp [hdeg]
    exact elevenFive_c40_l14_b5_seven_m39_threeMass_ge_thirtySix_of_degreeOne
      cfg hpoint hlocal hglobal hC hfive hmoment b hb hdeg
  · simp [hdeg]
    exact elevenFive_c40_l14_b5_seven_m39_threeMass_ge_fortyTwo_of_degreeTwo
      cfg hpoint hlocal hglobal hC hfive hmoment b hb hdeg

/-- Equality propagation in the P4 branch: every clean block has mass
exactly `48`. -/
theorem elevenFive_c40_l14_b5_seven_m39_pathFour_clean_mass_eq_fortyEight
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    (cfg : Configuration Point) (hpoint : Fintype.card Point = 11)
    (hcap : BlockSizeCap (blockSystem cfg) 5)
    (hlocal : ∀ p : Point, ElevenFiveLocalRows (blockSystem cfg) p)
    (hglobal : ElevenFiveGlobalRows (blockSystem cfg))
    (hC : (blockSystem cfg).totalCircleCount = 40)
    (hL : elevenFiveLineTotal (blockSystem cfg) = 14)
    (hfive : (blockSystem cfg).blockCount 5 = 7)
    (hmoment : elevenFiveSecondMoment (blockSystem cfg) = 39)
    (hnodisjoint : ∀ b ∈ (blockSystem cfg).blocksOfSize 5,
      ∀ c ∈ (blockSystem cfg).blocksOfSize 5, b ≠ c →
        ((blockSystem cfg).support b ∩
          (blockSystem cfg).support c).card ≠ 0)
    (hpath : ElevenFiveC40M39PathFour (blockSystem cfg))
    (b : GeometricBlock cfg) (hb : b ∈ (blockSystem cfg).blocksOfSize 5)
    (hzero : elevenFiveC40M39DefectDegree (blockSystem cfg) b = 0) :
    (∑ p ∈ (blockSystem cfg).support b,
      (blockSystem cfg).blockDegree 3 p) = 48 := by
  classical
  let S := blockSystem cfg
  let F := S.blocksOfSize 5
  let mass : GeometricBlock cfg → ℕ := fun c =>
    ∑ p ∈ S.support c, S.blockDegree 3 p
  let weight : GeometricBlock cfg → ℕ := fun c =>
    if elevenFiveC40M39DefectDegree S c = 0 then 48
    else if elevenFiveC40M39DefectDegree S c = 1 then 36 else 42
  obtain ⟨hZcard, hOcard, hTcard⟩ :=
    elevenFive_c40_l14_b5_seven_m39_pathFour_degree_counts
      S hpoint (by simpa [S] using hlocal) (by simpa [S] using hglobal)
        (by simpa [S] using hfive) (by simpa [S] using hmoment)
          (by simpa [S] using hnodisjoint) (by simpa [S] using hpath)
  have hweightSum : (∑ c ∈ F, weight c) = 300 := by
    have hcases (c : GeometricBlock cfg) (hc : c ∈ F) :=
      hpath.2.1 c (by simpa [F, S] using hc)
    calc
      (∑ c ∈ F, weight c) =
          ∑ c ∈ F,
            ((if elevenFiveC40M39DefectDegree S c = 0 then 48 else 0) +
             (if elevenFiveC40M39DefectDegree S c = 1 then 36 else 0) +
             (if elevenFiveC40M39DefectDegree S c = 2 then 42 else 0)) := by
        apply Finset.sum_congr rfl
        intro c hc
        have hle := hcases c hc
        interval_cases hd : elevenFiveC40M39DefectDegree S c <;>
          simp [weight, hd]
      _ = 300 := by
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
        simpa [F, ← Finset.sum_filter, hZcard, hOcard, hTcard,
          Nat.mul_comm] using
          (show 48 * 3 + 36 * 2 + 42 * 2 = 300 by norm_num)
  obtain ⟨hHsum, _hN12, _hN9⟩ :=
    elevenFive_c40_l14_b5_seven_m39_pathFour_high_profile
      cfg hpoint hcap hlocal hglobal hC hL hfive hmoment hnodisjoint hpath
  have hweightedExact :=
    elevenFive_c40_l14_b5_seven_m39_weighted_eq_279_add_high
      S hpoint (by simpa [S] using hlocal) (by simpa [S] using hglobal)
        (by simpa [S] using hC) (by simpa [S] using hL)
          (by simpa [S] using hfive) (by simpa [S] using hmoment)
  have hweighted :
      (∑ p : Point, S.blockDegree 3 p * S.blockDegree 5 p) = 300 := by
    rw [hweightedExact]
    have hHsum' :
        (∑ p ∈ (Finset.univ : Finset Point).filter
          (fun p => S.blockDegree 5 p = 4), S.blockDegree 3 p) = 21 := by
      simpa [S] using hHsum
    rw [hHsum']
  have hmassSum : (∑ c ∈ F, mass c) = 300 := by
    have hfubini := elevenFive_fiveBlock_threeMass_sum_eq_weighted S
    simpa [F, mass, hweighted] using hfubini
  have hpointLe : ∀ c ∈ F, weight c ≤ mass c := by
    intro c hc
    simpa [weight, mass, S] using
      (elevenFive_c40_l14_b5_seven_m39_pathFour_block_mass_lower
        cfg hpoint hcap hlocal hglobal hC hL hfive hmoment hnodisjoint
          hpath c (by simpa [F, S] using hc))
  have hsumEq : (∑ c ∈ F, weight c) = ∑ c ∈ F, mass c := by
    rw [hweightSum, hmassSum]
  have hall := (Finset.sum_eq_sum_iff_of_le hpointLe).mp hsumEq
  have hbEq := hall b (by simpa [F, S] using hb)
  simpa [weight, mass, S, hzero] using hbEq.symm

/-- Every clean M39 block contains both degree-four pivots. -/
theorem elevenFive_c40_l14_b5_seven_m39_high_subset_clean_block
    {Point : Type u} {Block : Type v} [Fintype Point] [Fintype Block]
    [DecidableEq Point] [DecidableEq Block]
    (S : BlockSystem Point Block) (hpoint : Fintype.card Point = 11)
    (hlocal : ∀ p : Point, ElevenFiveLocalRows S p)
    (hglobal : ElevenFiveGlobalRows S)
    (hfive : S.blockCount 5 = 7)
    (hmoment : elevenFiveSecondMoment S = 39)
    (b : Block) (hb : b ∈ S.blocksOfSize 5)
    (hzero : elevenFiveC40M39DefectDegree S b = 0)
    (hnodisjoint : ∀ c ∈ S.blocksOfSize 5, b ≠ c →
      (S.support b ∩ S.support c).card ≠ 0) :
    (Finset.univ : Finset Point).filter (fun p => S.blockDegree 5 p = 4) ⊆
      S.support b := by
  classical
  let H := (Finset.univ : Finset Point).filter fun p => S.blockDegree 5 p = 4
  obtain ⟨hfour, _hthree, _hprofile⟩ :=
    elevenFive_c40_l14_b5_seven_secondMoment_thirtyNine_profile
      S hpoint hlocal hglobal hfive hmoment
  have hHcard : H.card = 2 := by simpa [H] using hfour
  have hid :=
    elevenFive_c40_l14_b5_seven_m39_highOnBlock_add_defectDegree
      S hpoint hlocal hglobal hfive hmoment b hb hnodisjoint
  have hBcard : (elevenFiveC40M39HighOnFiveBlock S b).card = 2 := by omega
  have hsub : elevenFiveC40M39HighOnFiveBlock S b ⊆ H := by
    intro p hp
    have hpData := Finset.mem_filter.mp hp
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ p, hpData.2⟩
  have heq : elevenFiveC40M39HighOnFiveBlock S b = H :=
    Finset.eq_of_subset_of_card_le hsub (by omega)
  intro p hp
  have : p ∈ elevenFiveC40M39HighOnFiveBlock S b := by
    rw [heq]
    simpa [H] using hp
  exact (Finset.mem_filter.mp this).1

/-- A clean mass-48 block cannot contain a high `(12,4)` pivot and the
unique `(9,4)` pivot: removing them leaves odd mass `27`, while every
remaining point has even three-degree `6` or `12`. -/
theorem elevenFive_c40_m39_clean_mass48_high_twelve_nine_impossible
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    (cfg : Configuration Point) (hpoint : Fintype.card Point = 11)
    (hlocal : ∀ p : Point, ElevenFiveLocalRows (blockSystem cfg) p)
    (hglobal : ElevenFiveGlobalRows (blockSystem cfg))
    (hC : (blockSystem cfg).totalCircleCount = 40)
    (hfive : (blockSystem cfg).blockCount 5 = 7)
    (hmoment : elevenFiveSecondMoment (blockSystem cfg) = 39)
    (hnodisjoint : ∀ b ∈ (blockSystem cfg).blocksOfSize 5,
      ∀ c ∈ (blockSystem cfg).blocksOfSize 5, b ≠ c →
        ((blockSystem cfg).support b ∩
          (blockSystem cfg).support c).card ≠ 0)
    (b : GeometricBlock cfg) (hb : b ∈ (blockSystem cfg).blocksOfSize 5)
    (hzero : elevenFiveC40M39DefectDegree (blockSystem cfg) b = 0)
    (hmass : (∑ p ∈ (blockSystem cfg).support b,
      (blockSystem cfg).blockDegree 3 p) = 48)
    (a z : Point) (haz : a ≠ z)
    (ha4 : (blockSystem cfg).blockDegree 5 a = 4)
    (ha12 : (blockSystem cfg).blockDegree 3 a = 12)
    (hz4 : (blockSystem cfg).blockDegree 5 z = 4)
    (hz9 : (blockSystem cfg).blockDegree 3 z = 9)
    (hN9card : ((Finset.univ : Finset Point).filter fun p =>
      (blockSystem cfg).blockDegree 3 p = 9).card = 1) : False := by
  classical
  let S := blockSystem cfg
  let H := (Finset.univ : Finset Point).filter fun p => S.blockDegree 5 p = 4
  let N9 := (Finset.univ : Finset Point).filter fun p => S.blockDegree 3 p = 9
  have hN9card' : N9.card = 1 := by simpa [N9, S] using hN9card
  obtain ⟨w, hN9eqRaw⟩ := Finset.card_eq_one.mp hN9card'
  have hN9eq : N9 = {z} := by
    have hzN9 : z ∈ N9 := by simp [N9, S, hz9]
    have hzw : z = w := by
      rw [hN9eqRaw] at hzN9
      simpa using hzN9
    subst w
    exact hN9eqRaw
  have hHighSub :=
    elevenFive_c40_l14_b5_seven_m39_high_subset_clean_block
      S hpoint (by simpa [S] using hlocal) (by simpa [S] using hglobal)
        (by simpa [S] using hfive) (by simpa [S] using hmoment)
          b (by simpa [S] using hb) (by simpa [S] using hzero)
            (fun c hc hbc => hnodisjoint b (by simpa [S] using hb)
              c (by simpa [S] using hc) hbc)
  have haB : a ∈ S.support b := hHighSub (by simp [H, S, ha4])
  have hzB : z ∈ S.support b := hHighSub (by simp [H, S, hz4])
  have hzErase : z ∈ (S.support b).erase a :=
    Finset.mem_erase.mpr ⟨Ne.symm haz, hzB⟩
  let R := ((S.support b).erase a).erase z
  have hsplitA := Finset.sum_erase_add
    (S.support b) (fun p => S.blockDegree 3 p) haB
  have hsplitZ := Finset.sum_erase_add
    ((S.support b).erase a) (fun p => S.blockDegree 3 p) hzErase
  have hdecomp :
      (∑ p ∈ S.support b, S.blockDegree 3 p) =
        ((∑ p ∈ R, S.blockDegree 3 p) + S.blockDegree 3 z) +
          S.blockDegree 3 a := by
    calc
      (∑ p ∈ S.support b, S.blockDegree 3 p) =
          (∑ p ∈ (S.support b).erase a, S.blockDegree 3 p) +
            S.blockDegree 3 a := hsplitA.symm
      _ = ((∑ p ∈ R, S.blockDegree 3 p) + S.blockDegree 3 z) +
            S.blockDegree 3 a := by
          rw [← hsplitZ]
  have hRsum : (∑ p ∈ R, S.blockDegree 3 p) = 27 := by
    have hmass' : (∑ p ∈ S.support b, S.blockDegree 3 p) = 48 := by
      simpa [S] using hmass
    have ha12' : S.blockDegree 3 a = 12 := by simpa [S] using ha12
    have hz9' : S.blockDegree 3 z = 9 := by simpa [S] using hz9
    omega
  have hdoublePoint (p : Point) (hpR : p ∈ R) :
      S.blockDegree 3 p = 2 * (S.blockDegree 3 p / 2) := by
    rcases elevenFive_c40_threeDegree_values
      S p (by simpa [S] using hlocal p) (by simpa [S] using hC) with
      hp6 | hp9 | hp12
    · simp [hp6]
    · have hpN9 : p ∈ N9 := by simp [N9, hp9]
      rw [hN9eq] at hpN9
      have hpz : p = z := by simpa using hpN9
      have hpR' : p ∈ ((S.support b).erase a).erase z := by
        simpa only [R] using hpR
      have hpNe := (Finset.mem_erase.mp hpR').1
      exact False.elim (hpNe hpz)
    · simp [hp12]
  have hRdouble :
      (∑ p ∈ R, S.blockDegree 3 p) =
        2 * ∑ p ∈ R, (S.blockDegree 3 p / 2) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro p hp
    exact hdoublePoint p hp
  rw [hRsum] at hRdouble
  omega

/-- In the `P3+K2` shape the two clean blocks force equality: high mass is
`21` and both clean masses are `48`. -/
theorem elevenFive_c40_l14_b5_seven_m39_pathThreePlusEdge_clean_pair
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    (cfg : Configuration Point) (hpoint : Fintype.card Point = 11)
    (hcap : BlockSizeCap (blockSystem cfg) 5)
    (hlocal : ∀ p : Point, ElevenFiveLocalRows (blockSystem cfg) p)
    (hglobal : ElevenFiveGlobalRows (blockSystem cfg))
    (hC : (blockSystem cfg).totalCircleCount = 40)
    (hL : elevenFiveLineTotal (blockSystem cfg) = 14)
    (hfive : (blockSystem cfg).blockCount 5 = 7)
    (hmoment : elevenFiveSecondMoment (blockSystem cfg) = 39)
    (hnodisjoint : ∀ b ∈ (blockSystem cfg).blocksOfSize 5,
      ∀ c ∈ (blockSystem cfg).blocksOfSize 5, b ≠ c →
        ((blockSystem cfg).support b ∩
          (blockSystem cfg).support c).card ≠ 0)
    (hshape : ElevenFiveC40M39PathThreePlusEdge (blockSystem cfg)) :
    ∃ b c : GeometricBlock cfg, b ≠ c ∧
      b ∈ (blockSystem cfg).blocksOfSize 5 ∧
      c ∈ (blockSystem cfg).blocksOfSize 5 ∧
      elevenFiveC40M39DefectDegree (blockSystem cfg) b = 0 ∧
      elevenFiveC40M39DefectDegree (blockSystem cfg) c = 0 ∧
      (∑ p ∈ (blockSystem cfg).support b,
        (blockSystem cfg).blockDegree 3 p) = 48 ∧
      (∑ p ∈ (blockSystem cfg).support c,
        (blockSystem cfg).blockDegree 3 p) = 48 ∧
      (∑ p ∈ (Finset.univ : Finset Point).filter
        (fun p => (blockSystem cfg).blockDegree 5 p = 4),
          (blockSystem cfg).blockDegree 3 p) = 21 := by
  classical
  let S := blockSystem cfg
  let F := S.blocksOfSize 5
  let Z := F.filter fun b => elevenFiveC40M39DefectDegree S b = 0
  let H := (Finset.univ : Finset Point).filter fun p => S.blockDegree 5 p = 4
  obtain ⟨hZcard, _hOcard, _hTcard⟩ :=
    elevenFive_c40_l14_b5_seven_m39_pathThreePlusEdge_degree_counts
      S hpoint (by simpa [S] using hlocal) (by simpa [S] using hglobal)
        (by simpa [S] using hfive) (by simpa [S] using hmoment)
          (by simpa [S] using hnodisjoint) (by simpa [S] using hshape)
  have hZcard' : Z.card = 2 := by simpa [Z, F] using hZcard
  obtain ⟨b, c, hbc, hZeq⟩ := Finset.card_eq_two.mp hZcard'
  have hbZ : b ∈ Z := by rw [hZeq]; simp
  have hcZ : c ∈ Z := by rw [hZeq]; simp
  have hbData := Finset.mem_filter.mp (by simpa only [Z] using hbZ)
  have hcData := Finset.mem_filter.mp (by simpa only [Z] using hcZ)
  have hb : b ∈ S.blocksOfSize 5 := by simpa [F] using hbData.1
  have hc : c ∈ S.blocksOfSize 5 := by simpa [F] using hcData.1
  have hzeroB : elevenFiveC40M39DefectDegree S b = 0 := hbData.2
  have hzeroC : elevenFiveC40M39DefectDegree S c = 0 := hcData.2
  let mass : GeometricBlock cfg → ℕ := fun d =>
    ∑ p ∈ S.support d, S.blockDegree 3 p
  have hmassB : 48 ≤ mass b := by
    apply elevenFive_c40_l14_b5_seven_clean_threeMass_ge_fortyEight
      cfg hpoint hcap hlocal hglobal hC hL hfive b (by simpa [S] using hb)
    exact elevenFive_c40_m39_all_inter_two_of_defectDegree_zero
      S b hb hzeroB
        (fun d hd hbd => hnodisjoint b (by simpa [S] using hb)
          d (by simpa [S] using hd) hbd)
  have hmassC : 48 ≤ mass c := by
    apply elevenFive_c40_l14_b5_seven_clean_threeMass_ge_fortyEight
      cfg hpoint hcap hlocal hglobal hC hL hfive c (by simpa [S] using hc)
    exact elevenFive_c40_m39_all_inter_two_of_defectDegree_zero
      S c hc hzeroC
        (fun d hd hcd => hnodisjoint c (by simpa [S] using hc)
          d (by simpa [S] using hd) hcd)
  obtain ⟨hHcount, _hthree, _hfiveValues⟩ :=
    elevenFive_c40_l14_b5_seven_secondMoment_thirtyNine_profile
      S hpoint (by simpa [S] using hlocal) (by simpa [S] using hglobal)
        (by simpa [S] using hfive) (by simpa [S] using hmoment)
  have hHcard : H.card = 2 := by simpa [H] using hHcount
  have hhighB := elevenFive_c40_l14_b5_seven_m39_high_subset_clean_block
    S hpoint (by simpa [S] using hlocal) (by simpa [S] using hglobal)
      (by simpa [S] using hfive) (by simpa [S] using hmoment)
        b hb hzeroB (fun d hd hbd => hnodisjoint b (by simpa [S] using hb)
          d (by simpa [S] using hd) hbd)
  have hhighC := elevenFive_c40_l14_b5_seven_m39_high_subset_clean_block
    S hpoint (by simpa [S] using hlocal) (by simpa [S] using hglobal)
      (by simpa [S] using hfive) (by simpa [S] using hmoment)
        c hc hzeroC (fun d hd hcd => hnodisjoint c (by simpa [S] using hc)
          d (by simpa [S] using hd) hcd)
  let I := S.support b ∩ S.support c
  have hIcard : I.card = 2 := by
    have hall := elevenFive_c40_m39_all_inter_two_of_defectDegree_zero
      S b hb hzeroB
        (fun d hd hbd => hnodisjoint b (by simpa [S] using hb)
          d (by simpa [S] using hd) hbd)
    simpa [I] using hall c hc (Ne.symm hbc)
  have hHsubI : H ⊆ I := by
    intro p hp
    exact Finset.mem_inter.mpr ⟨hhighB (by simpa [H] using hp),
      hhighC (by simpa [H] using hp)⟩
  have hHI : H = I := Finset.eq_of_subset_of_card_le hHsubI (by omega)
  let B := S.support b
  let C := S.support c
  let R := C \ B
  let U := B ∪ C
  let M := (Finset.univ : Finset Point) \ U
  have hBRdisj : Disjoint B R := by
    rw [Finset.disjoint_left]
    intro p hpB hpR
    exact (Finset.mem_sdiff.mp hpR).2 hpB
  have hBRunion : B ∪ R = U := by
    ext p
    simp only [B, C, R, U, Finset.mem_union, Finset.mem_sdiff]
    constructor
    · rintro (hpB | ⟨hpC, _hpNotB⟩)
      · exact Or.inl hpB
      · exact Or.inr hpC
    · rintro (hpB | hpC)
      · exact Or.inl hpB
      · by_cases hpB : p ∈ S.support b
        · exact Or.inl hpB
        · exact Or.inr ⟨hpC, hpB⟩
  have hIRdisj : Disjoint I R := by
    rw [Finset.disjoint_left]
    intro p hpI hpR
    exact (Finset.mem_sdiff.mp hpR).2 (Finset.mem_inter.mp hpI).1
  have hIRunion : I ∪ R = C := by
    ext p
    simp only [I, B, C, R, Finset.mem_union, Finset.mem_inter,
      Finset.mem_sdiff]
    constructor
    · rintro (⟨_hpB, hpC⟩ | ⟨hpC, _hpNotB⟩)
      · exact hpC
      · exact hpC
    · intro hpC
      by_cases hpB : p ∈ S.support b
      · exact Or.inl ⟨hpB, hpC⟩
      · exact Or.inr ⟨hpC, hpB⟩
  have hsumU : (∑ p ∈ U, S.blockDegree 3 p) =
      (∑ p ∈ B, S.blockDegree 3 p) +
        ∑ p ∈ R, S.blockDegree 3 p := by
    rw [← Finset.sum_union hBRdisj, hBRunion]
  have hsumC : (∑ p ∈ C, S.blockDegree 3 p) =
      (∑ p ∈ I, S.blockDegree 3 p) +
        ∑ p ∈ R, S.blockDegree 3 p := by
    rw [← Finset.sum_union hIRdisj, hIRunion]
  have hmassPair : mass b + mass c =
      (∑ p ∈ U, S.blockDegree 3 p) +
        ∑ p ∈ H, S.blockDegree 3 p := by
    change (∑ p ∈ B, S.blockDegree 3 p) +
      (∑ p ∈ C, S.blockDegree 3 p) =
        (∑ p ∈ U, S.blockDegree 3 p) +
          ∑ p ∈ H, S.blockDegree 3 p
    rw [hsumU, hsumC, hHI]
    omega
  have hUcard : U.card = 8 := by
    have hrow := Finset.card_union_add_card_inter B C
    have hBcard : B.card = 5 := by simpa [B] using S.mem_blocksOfSize.mp hb
    have hCcard : C.card = 5 := by simpa [C] using S.mem_blocksOfSize.mp hc
    change U.card + I.card = B.card + C.card at hrow
    omega
  have hMcard : M.card = 3 := by
    dsimp [M]
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ U),
      Finset.card_univ, hpoint, hUcard]
  have hMmass : 18 ≤ ∑ p ∈ M, S.blockDegree 3 p := by
    have hlower : (∑ _p ∈ M, 6) ≤ ∑ p ∈ M, S.blockDegree 3 p := by
      apply Finset.sum_le_sum
      intro p _hp
      rcases elevenFive_c40_threeDegree_values
        S p (by simpa [S] using hlocal p) (by simpa [S] using hC) with
        h6 | h9 | h12 <;> omega
    have hconst : (∑ _p ∈ M, 6) = 18 := by simp [hMcard]
    omega
  have hUMdisj : Disjoint U M := by
    rw [Finset.disjoint_left]
    intro p hpU hpM
    exact (Finset.mem_sdiff.mp hpM).2 hpU
  have hUMcover : U ∪ M = (Finset.univ : Finset Point) := by
    ext p
    simp [M]
  have hthreeSum : (∑ p : Point, S.blockDegree 3 p) = 93 := by
    obtain ⟨hthreeCount, _hfourCount⟩ :=
      elevenFive_c40_l14_b5_seven_block_census S
        (by simpa [S] using hglobal) (by simpa [S] using hC)
          (by simpa [S] using hL) (by simpa [S] using hfive)
    rw [hglobal.threeIncidence, hthreeCount]
  have htotalSplit :
      (∑ p ∈ U, S.blockDegree 3 p) +
        (∑ p ∈ M, S.blockDegree 3 p) = 93 := by
    calc
      (∑ p ∈ U, S.blockDegree 3 p) +
          (∑ p ∈ M, S.blockDegree 3 p) =
            ∑ p ∈ U ∪ M, S.blockDegree 3 p :=
              (Finset.sum_union hUMdisj).symm
      _ = ∑ p : Point, S.blockDegree 3 p := by rw [hUMcover]
      _ = 93 := hthreeSum
  have hUupper : (∑ p ∈ U, S.blockDegree 3 p) ≤ 75 := by omega
  have hHighUpper := elevenFive_c40_l14_b5_seven_m39_high_threeMass_le_twentyOne
    cfg hpoint hlocal hglobal hC hL hfive hmoment hnodisjoint
  have hHighEq : (∑ p ∈ H, S.blockDegree 3 p) = 21 := by
    have hpairLower : 96 ≤ mass b + mass c := by omega
    have hupper : (∑ p ∈ H, S.blockDegree 3 p) ≤ 21 := by
      simpa [S, H] using hHighUpper
    omega
  have hmassBEq : mass b = 48 := by omega
  have hmassCEq : mass c = 48 := by omega
  exact ⟨b, c, hbc, by simpa [S] using hb, by simpa [S] using hc,
    by simpa [S] using hzeroB, by simpa [S] using hzeroC,
    by simpa [mass, S] using hmassBEq, by simpa [mass, S] using hmassCEq,
    by simpa [S, H] using hHighEq⟩

theorem elevenFive_c40_l14_b5_seven_m39_pathThreePlusEdge_impossible
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    (cfg : Configuration Point) (hpoint : Fintype.card Point = 11)
    (hcap : BlockSizeCap (blockSystem cfg) 5)
    (hlocal : ∀ p : Point, ElevenFiveLocalRows (blockSystem cfg) p)
    (hglobal : ElevenFiveGlobalRows (blockSystem cfg))
    (hC : (blockSystem cfg).totalCircleCount = 40)
    (hL : elevenFiveLineTotal (blockSystem cfg) = 14)
    (hfive : (blockSystem cfg).blockCount 5 = 7)
    (hmoment : elevenFiveSecondMoment (blockSystem cfg) = 39)
    (hnodisjoint : ∀ b ∈ (blockSystem cfg).blocksOfSize 5,
      ∀ c ∈ (blockSystem cfg).blocksOfSize 5, b ≠ c →
        ((blockSystem cfg).support b ∩
          (blockSystem cfg).support c).card ≠ 0)
    (hshape : ElevenFiveC40M39PathThreePlusEdge (blockSystem cfg)) : False := by
  obtain ⟨b, _c, _hbc, hb, _hc, hzero, _hzeroC,
    hmass, _hmassC, hhigh⟩ :=
      elevenFive_c40_l14_b5_seven_m39_pathThreePlusEdge_clean_pair
        cfg hpoint hcap hlocal hglobal hC hL hfive hmoment hnodisjoint hshape
  obtain ⟨a, z, haz, ha4, ha12, hz4, hz9, _hN12, hN9⟩ :=
    elevenFive_c40_l14_b5_seven_m39_high_pair_of_mass_twentyOne
      cfg hpoint hlocal hglobal hC hL hfive hmoment hnodisjoint hhigh
  exact elevenFive_c40_m39_clean_mass48_high_twelve_nine_impossible
    cfg hpoint hlocal hglobal hC hfive hmoment hnodisjoint b hb hzero hmass
      a z haz ha4 ha12 hz4 hz9 hN9

/-- The P4 defect shape is impossible.  Equality in its `300` lower bound
forces every clean block to have mass `48`.  Such a block contains the
unique high degree-twelve and high degree-nine pivots, leaving residual
mass `27`; but the remaining points have three-degree only `6` or `12`. -/
theorem elevenFive_c40_l14_b5_seven_m39_pathFour_impossible
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    (cfg : Configuration Point) (hpoint : Fintype.card Point = 11)
    (hcap : BlockSizeCap (blockSystem cfg) 5)
    (hlocal : ∀ p : Point, ElevenFiveLocalRows (blockSystem cfg) p)
    (hglobal : ElevenFiveGlobalRows (blockSystem cfg))
    (hC : (blockSystem cfg).totalCircleCount = 40)
    (hL : elevenFiveLineTotal (blockSystem cfg) = 14)
    (hfive : (blockSystem cfg).blockCount 5 = 7)
    (hmoment : elevenFiveSecondMoment (blockSystem cfg) = 39)
    (hnodisjoint : ∀ b ∈ (blockSystem cfg).blocksOfSize 5,
      ∀ c ∈ (blockSystem cfg).blocksOfSize 5, b ≠ c →
        ((blockSystem cfg).support b ∩
          (blockSystem cfg).support c).card ≠ 0)
    (hpath : ElevenFiveC40M39PathFour (blockSystem cfg)) : False := by
  classical
  let S := blockSystem cfg
  let F := S.blocksOfSize 5
  let Z := F.filter fun b => elevenFiveC40M39DefectDegree S b = 0
  let H := (Finset.univ : Finset Point).filter fun p => S.blockDegree 5 p = 4
  let N9 := (Finset.univ : Finset Point).filter fun p => S.blockDegree 3 p = 9
  obtain ⟨hZcard, _hOcard, _hTcard⟩ :=
    elevenFive_c40_l14_b5_seven_m39_pathFour_degree_counts
      S hpoint (by simpa [S] using hlocal) (by simpa [S] using hglobal)
        (by simpa [S] using hfive) (by simpa [S] using hmoment)
          (by simpa [S] using hnodisjoint) (by simpa [S] using hpath)
  have hZpos : 0 < Z.card := by
    have hZcard' : Z.card = 3 := by simpa [Z, F] using hZcard
    omega
  obtain ⟨b, hbZ⟩ := Finset.card_pos.mp hZpos
  have hbData := Finset.mem_filter.mp (by simpa only [Z] using hbZ)
  have hbF : b ∈ F := hbData.1
  have hb : b ∈ S.blocksOfSize 5 := by simpa [F] using hbF
  have hzero : elevenFiveC40M39DefectDegree S b = 0 := hbData.2
  have hmass :=
    elevenFive_c40_l14_b5_seven_m39_pathFour_clean_mass_eq_fortyEight
      cfg hpoint hcap hlocal hglobal hC hL hfive hmoment hnodisjoint hpath
        b (by simpa [S] using hb) (by simpa [S] using hzero)
  obtain ⟨hHsum, _hN12card, hN9card⟩ :=
    elevenFive_c40_l14_b5_seven_m39_pathFour_high_profile
      cfg hpoint hcap hlocal hglobal hC hL hfive hmoment hnodisjoint hpath
  obtain ⟨hHcount, _hthree, _hfiveValues⟩ :=
    elevenFive_c40_l14_b5_seven_secondMoment_thirtyNine_profile
      S hpoint (by simpa [S] using hlocal) (by simpa [S] using hglobal)
        (by simpa [S] using hfive) (by simpa [S] using hmoment)
  have hHcard : H.card = 2 := by simpa [H] using hHcount
  obtain ⟨x, y, hxy, hHeq⟩ := Finset.card_eq_two.mp hHcard
  have hxH : x ∈ H := by rw [hHeq]; simp
  have hyH : y ∈ H := by rw [hHeq]; simp
  have hsumXY : S.blockDegree 3 x + S.blockDegree 3 y = 21 := by
    have hHsum' : (∑ p ∈ H, S.blockDegree 3 p) = 21 := by
      simpa [S, H] using hHsum
    rw [hHeq] at hHsum'
    simpa [hxy, Nat.add_comm] using hHsum'
  obtain ⟨_hN6, _hN9N12, hthreeValues⟩ :=
    elevenFive_c40_l14_b5_seven_threeDegree_census
      S hpoint (by simpa [S] using hlocal) (by simpa [S] using hglobal)
        (by simpa [S] using hC) (by simpa [S] using hL)
          (by simpa [S] using hfive)
  have hN9card' : N9.card = 1 := by simpa [N9, S] using hN9card
  obtain ⟨w, hN9eqRaw⟩ := Finset.card_eq_one.mp hN9card'
  have himpossible (a z : Point) (haz : a ≠ z)
      (haH : a ∈ H) (hzH : z ∈ H)
      (ha12 : S.blockDegree 3 a = 12)
      (hz9 : S.blockDegree 3 z = 9) : False := by
    have hN9eq : N9 = {z} := by
      have hzN9 : z ∈ N9 := by simp [N9, hz9]
      have hzw : z = w := by
        rw [hN9eqRaw] at hzN9
        simpa using hzN9
      subst w
      exact hN9eqRaw
    have hHighSub :=
      elevenFive_c40_l14_b5_seven_m39_high_subset_clean_block
        S hpoint (by simpa [S] using hlocal) (by simpa [S] using hglobal)
          (by simpa [S] using hfive) (by simpa [S] using hmoment)
            b hb hzero
              (fun c hc hbc => hnodisjoint b (by simpa [S] using hb)
                c (by simpa [S] using hc) hbc)
    have haB : a ∈ S.support b := hHighSub (by simpa [H] using haH)
    have hzB : z ∈ S.support b := hHighSub (by simpa [H] using hzH)
    have hzErase : z ∈ (S.support b).erase a :=
      Finset.mem_erase.mpr ⟨Ne.symm haz, hzB⟩
    let R := ((S.support b).erase a).erase z
    have hsplitA := Finset.sum_erase_add
      (S.support b) (fun p => S.blockDegree 3 p) haB
    have hsplitZ := Finset.sum_erase_add
      ((S.support b).erase a) (fun p => S.blockDegree 3 p) hzErase
    have hdecomp :
        (∑ p ∈ S.support b, S.blockDegree 3 p) =
          ((∑ p ∈ R, S.blockDegree 3 p) + S.blockDegree 3 z) +
            S.blockDegree 3 a := by
      calc
        (∑ p ∈ S.support b, S.blockDegree 3 p) =
            (∑ p ∈ (S.support b).erase a, S.blockDegree 3 p) +
              S.blockDegree 3 a := hsplitA.symm
        _ = ((∑ p ∈ R, S.blockDegree 3 p) + S.blockDegree 3 z) +
              S.blockDegree 3 a := by
            rw [← hsplitZ]
    have hRsum : (∑ p ∈ R, S.blockDegree 3 p) = 27 := by
      rw [ha12, hz9] at hdecomp
      have hmass' : (∑ p ∈ S.support b, S.blockDegree 3 p) = 48 := by
        simpa [S] using hmass
      omega
    have hdoublePoint (p : Point) (hpR : p ∈ R) :
        S.blockDegree 3 p = 2 * (S.blockDegree 3 p / 2) := by
      rcases hthreeValues p with hp6 | hp9 | hp12
      · simp [hp6]
      · have hpN9 : p ∈ N9 := by simp [N9, hp9]
        rw [hN9eq] at hpN9
        have hpz : p = z := by simpa using hpN9
        have hpR' : p ∈ ((S.support b).erase a).erase z := by
          simpa only [R] using hpR
        have hpNe := (Finset.mem_erase.mp hpR').1
        exact False.elim (hpNe hpz)
      · simp [hp12]
    have hRdouble :
        (∑ p ∈ R, S.blockDegree 3 p) =
          2 * ∑ p ∈ R, (S.blockDegree 3 p / 2) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p hp
      exact hdoublePoint p hp
    rw [hRsum] at hRdouble
    omega
  rcases hthreeValues x with hx6 | hx9 | hx12 <;>
    rcases hthreeValues y with hy6 | hy9 | hy12
  all_goals try omega
  · exact himpossible y x (Ne.symm hxy) hyH hxH hy12 hx9
  · exact himpossible x y hxy hxH hyH hx12 hy9

/-- After the page-cap and weighted endpoints, the only no-disjoint M39
defect graph is the three-edge matching. -/
theorem elevenFive_c40_l14_b5_seven_m39_noDisjoint_threeMatching
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    (cfg : Configuration Point) (hpoint : Fintype.card Point = 11)
    (hcap : BlockSizeCap (blockSystem cfg) 5)
    (hlocal : ∀ p : Point, ElevenFiveLocalRows (blockSystem cfg) p)
    (hglobal : ElevenFiveGlobalRows (blockSystem cfg))
    (hC : (blockSystem cfg).totalCircleCount = 40)
    (hL : elevenFiveLineTotal (blockSystem cfg) = 14)
    (hfive : (blockSystem cfg).blockCount 5 = 7)
    (hmoment : elevenFiveSecondMoment (blockSystem cfg) = 39)
    (hnodisjoint : ∀ b ∈ (blockSystem cfg).blocksOfSize 5,
      ∀ c ∈ (blockSystem cfg).blocksOfSize 5, b ≠ c →
        ((blockSystem cfg).support b ∩
          (blockSystem cfg).support c).card ≠ 0) :
    ElevenFiveC40M39ThreeMatching (blockSystem cfg) := by
  rcases elevenFive_c40_l14_b5_seven_m39_defectShape_classification
      (blockSystem cfg) hpoint hlocal hglobal hfive hmoment hnodisjoint with
    hmatching | hpathThree | hpathFour | htriangle
  · exact hmatching
  · exact False.elim
      (elevenFive_c40_l14_b5_seven_m39_pathThreePlusEdge_impossible
        cfg hpoint hcap hlocal hglobal hC hL hfive hmoment hnodisjoint
          hpathThree)
  · exact False.elim
      (elevenFive_c40_l14_b5_seven_m39_pathFour_impossible
        cfg hpoint hcap hlocal hglobal hC hL hfive hmoment hnodisjoint
          hpathFour)
  · exact False.elim
      (elevenFive_c40_l14_b5_seven_m39_triangle_impossible
        cfg hpoint hcap hlocal hglobal hC hL hfive hmoment hnodisjoint
          htriangle)

private theorem c40M39_defectEdge_endpoint_neighbour
    {Point : Type u} {Block : Type v} [Fintype Point] [Fintype Block]
    [DecidableEq Point] [DecidableEq Block]
    (S : BlockSystem Point Block) {A : Finset Block}
    (hA : A ∈ elevenFiveC40M39DefectEdges S)
    {b c : Block} (hb : b ∈ A) (hc : c ∈ A) (hbc : b ≠ c) :
    c ∈ elevenFiveC40M39SingletonNeighbours S b := by
  have hAdata := Finset.mem_filter.mp
    (by simpa only [elevenFiveC40M39DefectEdges] using hA)
  have hApow := Finset.mem_powersetCard.mp hAdata.1
  have hbFive := hApow.1 hb
  have hcFive := hApow.1 hc
  have hAeq : A = {b, c} := by
    have hsub : ({b, c} : Finset Block) ⊆ A := by
      intro d hd
      simp only [Finset.mem_insert, Finset.mem_singleton] at hd
      rcases hd with rfl | rfl
      · exact hb
      · exact hc
    have hpairCard : ({b, c} : Finset Block).card = 2 := by simp [hbc]
    have hcardLe : A.card ≤ ({b, c} : Finset Block).card := by
      rw [hApow.2, hpairCard]
    have heq := Finset.eq_of_subset_of_card_le hsub hcardLe
    exact heq.symm
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_erase.mpr ⟨Ne.symm hbc, hcFive⟩, ?_⟩
  simpa [hAeq, S.commonSupport_pair] using hAdata.2

private theorem c40M39_threeMatching_isPerfectMatching
    {Point : Type u} {Block : Type v} [Fintype Point] [Fintype Block]
    [DecidableEq Point] [DecidableEq Block]
    (S : BlockSystem Point Block) (clean : Block)
    (hcleanFive : clean ∈ S.blocksOfSize 5)
    (hcleanZero : elevenFiveC40M39DefectDegree S clean = 0)
    (hother : ∀ b ∈ S.blocksOfSize 5, b ≠ clean →
      elevenFiveC40M39DefectDegree S b = 1) :
    SixConicPerfectMatchingOn ((S.blocksOfSize 5).erase clean)
      (elevenFiveC40M39DefectEdges S) := by
  classical
  let F := S.blocksOfSize 5
  let G := elevenFiveC40M39DefectEdges S
  have hpair : ∀ A ∈ G, A.card = 2 ∧ A ⊆ F.erase clean := by
    intro A hA
    have hAdata := Finset.mem_filter.mp
      (by simpa only [G, elevenFiveC40M39DefectEdges] using hA)
    have hApow := Finset.mem_powersetCard.mp hAdata.1
    refine ⟨hApow.2, ?_⟩
    intro b hbA
    have hbF : b ∈ F := hApow.1 hbA
    apply Finset.mem_erase.mpr
    refine ⟨?_, hbF⟩
    intro hbc
    subst b
    have hEraseCard : (A.erase clean).card = 1 := by
      rw [Finset.card_erase_of_mem hbA, hApow.2]
    obtain ⟨c, hEraseEq⟩ := Finset.card_eq_one.mp hEraseCard
    have hcErase : c ∈ A.erase clean := by rw [hEraseEq]; simp
    have hcA := Finset.mem_of_mem_erase hcErase
    have hcNe := (Finset.mem_erase.mp hcErase).1
    have hcN := c40M39_defectEdge_endpoint_neighbour S
      (by simpa [G] using hA) hbA hcA (Ne.symm hcNe)
    have hpositive := Finset.card_pos.mpr ⟨c, hcN⟩
    have hzero : (elevenFiveC40M39SingletonNeighbours S clean).card = 0 := by
      simpa [elevenFiveC40M39DefectDegree] using hcleanZero
    omega
  refine ⟨hpair, ?_, ?_⟩
  · intro A hA B hB hAB
    change Disjoint A B
    rw [Finset.disjoint_left]
    intro b hbA hbB
    have hbF : b ∈ F :=
      Finset.mem_of_mem_erase ((hpair A hA).2 hbA)
    have hbDegreeLe : elevenFiveC40M39DefectDegree S b ≤ 1 := by
      by_cases hbc : b = clean
      · subst b
        rw [hcleanZero]
        omega
      · rw [hother b hbF hbc]
    have hAeraseCard : (A.erase b).card = 1 := by
      rw [Finset.card_erase_of_mem hbA, (hpair A hA).1]
    have hBeraseCard : (B.erase b).card = 1 := by
      rw [Finset.card_erase_of_mem hbB, (hpair B hB).1]
    obtain ⟨c, hAc⟩ := Finset.card_eq_one.mp hAeraseCard
    obtain ⟨d, hBd⟩ := Finset.card_eq_one.mp hBeraseCard
    have hcErase : c ∈ A.erase b := by rw [hAc]; simp
    have hdErase : d ∈ B.erase b := by rw [hBd]; simp
    have hcA := Finset.mem_of_mem_erase hcErase
    have hdB := Finset.mem_of_mem_erase hdErase
    have hbc := Ne.symm (Finset.mem_erase.mp hcErase).1
    have hbd := Ne.symm (Finset.mem_erase.mp hdErase).1
    have hcd : c ≠ d := by
      intro hcd
      subst d
      apply hAB
      rw [← Finset.insert_erase hbA, ← Finset.insert_erase hbB, hAc, hBd]
    have hcN := c40M39_defectEdge_endpoint_neighbour S
      (by simpa [G] using hA) hbA hcA hbc
    have hdN := c40M39_defectEdge_endpoint_neighbour S
      (by simpa [G] using hB) hbB hdB hbd
    have htwo : 2 ≤ (elevenFiveC40M39SingletonNeighbours S b).card := by
      have hsub : ({c, d} : Finset Block) ⊆
          elevenFiveC40M39SingletonNeighbours S b := by
        intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl
        · exact hcN
        · exact hdN
      have := Finset.card_le_card hsub
      have hpairCard : ({c, d} : Finset Block).card = 2 := by simp [hcd]
      rwa [hpairCard] at this
    change (elevenFiveC40M39SingletonNeighbours S b).card ≤ 1 at hbDegreeLe
    omega
  · ext b
    constructor
    · intro hb
      obtain ⟨A, hAG, hbA⟩ := Finset.mem_biUnion.mp hb
      exact (hpair A hAG).2 hbA
    · intro hb
      have hbErase := Finset.mem_erase.mp hb
      have hbDegree : elevenFiveC40M39DefectDegree S b = 1 :=
        hother b (by simpa [F] using hbErase.2) hbErase.1
      let N := elevenFiveC40M39SingletonNeighbours S b
      have hNcard : N.card = 1 := by
        simpa [N, elevenFiveC40M39DefectDegree] using hbDegree
      obtain ⟨c, hNeq⟩ := Finset.card_eq_one.mp hNcard
      have hcN : c ∈ elevenFiveC40M39SingletonNeighbours S b := by
        have hcN' : c ∈ N := by rw [hNeq]; simp
        simpa only [N] using hcN'
      have hcData := Finset.mem_filter.mp hcN
      have hcErase := Finset.mem_erase.mp hcData.1
      let A : Finset Block := {b, c}
      have hbc : b ≠ c := Ne.symm hcErase.1
      have hAedge : A ∈ G := by
        change A ∈ elevenFiveC40M39DefectEdges S
        rw [elevenFiveC40M39DefectEdges]
        apply Finset.mem_filter.mpr
        constructor
        · apply Finset.mem_powersetCard.mpr
          constructor
          · intro x hx
            simp only [A, Finset.mem_insert, Finset.mem_singleton] at hx
            rcases hx with rfl | rfl
            · exact hbErase.2
            · exact hcErase.2
          · simp [A, hbc]
        · simpa [A, S.commonSupport_pair] using hcData.2
      apply Finset.mem_biUnion.mpr
      exact ⟨A, hAedge, by simp [A]⟩

/-- Lossless page-cap entrance for the sole surviving M39 shape.  The
seven five-blocks consist of one clean block and six degree-one vertices;
the three singleton edges therefore form `3K2`.  The fields retain the
three actual `(12,3)` carriers needed by the geometric five-trace tail. -/
structure ElevenFiveC40M39ThreeMatchingPageResidual
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    (cfg : Configuration Point) where
  clean : GeometricBlock cfg
  clean_five : clean ∈ (blockSystem cfg).blocksOfSize 5
  all_circle : ∀ b ∈ (blockSystem cfg).blocksOfSize 5,
    ∃ Gamma : DeterminedCircle cfg, b = Sum.inr Gamma
  clean_unique : ∀ b ∈ (blockSystem cfg).blocksOfSize 5,
    elevenFiveC40M39DefectDegree (blockSystem cfg) b = 0 ↔ b = clean
  other_degree_one : ∀ b ∈ (blockSystem cfg).blocksOfSize 5,
    b ≠ clean → elevenFiveC40M39DefectDegree (blockSystem cfg) b = 1
  clean_double : ∀ b ∈ (blockSystem cfg).blocksOfSize 5,
    b ≠ clean →
      ((blockSystem cfg).support clean ∩
        (blockSystem cfg).support b).card = 2
  clean_mass_ge : 49 ≤ ∑ p ∈ (blockSystem cfg).support clean,
    (blockSystem cfg).blockDegree 3 p
  clean_mass_cases :
    (∑ p ∈ (blockSystem cfg).support clean,
      (blockSystem cfg).blockDegree 3 p) = 51 ∨
    (∑ p ∈ (blockSystem cfg).support clean,
      (blockSystem cfg).blockDegree 3 p) = 54 ∨
    (∑ p ∈ (blockSystem cfg).support clean,
      (blockSystem cfg).blockDegree 3 p) = 57
  high_card : (elevenFiveC40M39HighOnFiveBlock
    (blockSystem cfg) clean).card = 2
  high_covers : ∀ p : Point, (blockSystem cfg).blockDegree 5 p = 4 →
    p ∈ (blockSystem cfg).support clean
  high_on_other : ∀ b ∈ (blockSystem cfg).blocksOfSize 5,
    b ≠ clean →
      (elevenFiveC40M39HighOnFiveBlock (blockSystem cfg) b).card = 1
  defect_edges_card :
    (elevenFiveC40M39DefectEdges (blockSystem cfg)).card = 3
  defect_matching : SixConicPerfectMatchingOn
    (((blockSystem cfg).blocksOfSize 5).erase clean)
      (elevenFiveC40M39DefectEdges (blockSystem cfg))
  edge_carrier : ∀ A ∈ elevenFiveC40M39DefectEdges (blockSystem cfg),
    ∃ p : Point, p ∈ (blockSystem cfg).commonSupport A ∧
      (blockSystem cfg).blockDegree 3 p = 12 ∧
      (blockSystem cfg).blockDegree 5 p = 3

private theorem elevenFive_c40_l14_b5_seven_m39_clean_vertex_core
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    (cfg : Configuration Point) (hpoint : Fintype.card Point = 11)
    (hcap : BlockSizeCap (blockSystem cfg) 5)
    (hlocal : ∀ p : Point, ElevenFiveLocalRows (blockSystem cfg) p)
    (hglobal : ElevenFiveGlobalRows (blockSystem cfg))
    (hC : (blockSystem cfg).totalCircleCount = 40)
    (hL : elevenFiveLineTotal (blockSystem cfg) = 14)
    (hfive : (blockSystem cfg).blockCount 5 = 7)
    (hmoment : elevenFiveSecondMoment (blockSystem cfg) = 39)
    (hnodisjoint : ∀ b ∈ (blockSystem cfg).blocksOfSize 5,
      ∀ c ∈ (blockSystem cfg).blocksOfSize 5, b ≠ c →
        ((blockSystem cfg).support b ∩
          (blockSystem cfg).support c).card ≠ 0) :
    ∃ clean : GeometricBlock cfg,
      clean ∈ (blockSystem cfg).blocksOfSize 5 ∧
      elevenFiveC40M39DefectDegree (blockSystem cfg) clean = 0 ∧
      (∀ b ∈ (blockSystem cfg).blocksOfSize 5,
        elevenFiveC40M39DefectDegree (blockSystem cfg) b = 0 ↔ b = clean) ∧
      (∀ b ∈ (blockSystem cfg).blocksOfSize 5, b ≠ clean →
        elevenFiveC40M39DefectDegree (blockSystem cfg) b = 1) ∧
      ElevenFiveC40M39ThreeMatching (blockSystem cfg) := by
  classical
  let S := blockSystem cfg
  let F := S.blocksOfSize 5
  let Z := F.filter fun b => elevenFiveC40M39DefectDegree S b = 0
  let T := F.filter fun b => elevenFiveC40M39DefectDegree S b = 2
  have hshape := elevenFive_c40_l14_b5_seven_m39_noDisjoint_threeMatching
    cfg hpoint hcap hlocal hglobal hC hL hfive hmoment hnodisjoint
  obtain ⟨hZcard, _hOcard, hTcard⟩ :=
    elevenFive_c40_l14_b5_seven_m39_threeMatching_degree_counts
      S hpoint (by simpa [S] using hlocal) (by simpa [S] using hglobal)
        (by simpa [S] using hfive) (by simpa [S] using hmoment)
          (by simpa [S] using hnodisjoint) (by simpa [S] using hshape)
  have hZcard' : Z.card = 1 := by simpa [Z, F] using hZcard
  obtain ⟨clean, hZeq⟩ := Finset.card_eq_one.mp hZcard'
  have hcleanZ : clean ∈ Z := by rw [hZeq]; simp
  have hcleanData := Finset.mem_filter.mp (by simpa only [Z] using hcleanZ)
  have hcleanFive : clean ∈ S.blocksOfSize 5 := by
    simpa [F] using hcleanData.1
  have hcleanZero : elevenFiveC40M39DefectDegree S clean = 0 :=
    hcleanData.2
  have hunique : ∀ b ∈ S.blocksOfSize 5,
      elevenFiveC40M39DefectDegree S b = 0 ↔ b = clean := by
    intro b hb
    constructor
    · intro hbZero
      have hbZ : b ∈ Z := by simp [Z, F, hb, hbZero]
      rw [hZeq] at hbZ
      simpa using hbZ
    · rintro rfl
      exact hcleanZero
  have hother : ∀ b ∈ S.blocksOfSize 5, b ≠ clean →
      elevenFiveC40M39DefectDegree S b = 1 := by
    intro b hb hbc
    have hle := hshape.2.1 b (by simpa [S] using hb)
    change elevenFiveC40M39DefectDegree S b ≤ 2 at hle
    have hneZero : elevenFiveC40M39DefectDegree S b ≠ 0 := by
      intro hz
      exact hbc ((hunique b hb).1 hz)
    have hneTwo : elevenFiveC40M39DefectDegree S b ≠ 2 := by
      intro ht
      have hbT : b ∈ T := by simp [T, F, hb, ht]
      have hTcard' : T.card = 0 := by simpa [T, F] using hTcard
      have hTEmpty : T = ∅ := Finset.card_eq_zero.mp hTcard'
      rw [hTEmpty] at hbT
      simpa using hbT
    omega
  exact ⟨clean, by simpa [S] using hcleanFive,
    by simpa [S] using hcleanZero, by simpa [S] using hunique,
    by simpa [S] using hother, hshape⟩

private theorem elevenFive_c40_l14_b5_seven_m39_clean_geometry_core
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    (cfg : Configuration Point)
    (hglobal : ElevenFiveGlobalRows (blockSystem cfg))
    (hC : (blockSystem cfg).totalCircleCount = 40)
    (hL : elevenFiveLineTotal (blockSystem cfg) = 14)
    (hfive : (blockSystem cfg).blockCount 5 = 7)
    (hnodisjoint : ∀ b ∈ (blockSystem cfg).blocksOfSize 5,
      ∀ c ∈ (blockSystem cfg).blocksOfSize 5, b ≠ c →
        ((blockSystem cfg).support b ∩
          (blockSystem cfg).support c).card ≠ 0)
    (clean : GeometricBlock cfg)
    (hcleanFive : clean ∈ (blockSystem cfg).blocksOfSize 5)
    (hcleanZero : elevenFiveC40M39DefectDegree
      (blockSystem cfg) clean = 0) :
    (∀ b ∈ (blockSystem cfg).blocksOfSize 5, b ≠ clean →
      ((blockSystem cfg).support clean ∩
        (blockSystem cfg).support b).card = 2) ∧
    ∀ b ∈ (blockSystem cfg).blocksOfSize 5,
      ∃ Gamma : DeterminedCircle cfg, b = Sum.inr Gamma := by
  classical
  let S := blockSystem cfg
  have hdouble : ∀ b ∈ S.blocksOfSize 5, b ≠ clean →
      (S.support clean ∩ S.support b).card = 2 :=
    elevenFive_c40_m39_all_inter_two_of_defectDegree_zero
      S clean (by simpa [S] using hcleanFive)
        (by simpa [S] using hcleanZero)
        (fun b hb hcb => hnodisjoint clean hcleanFive
          b (by simpa [S] using hb) hcb)
  have hlineFive := c40FourteenSeven_lineCount_five_eq_zero
    S (by simpa [S] using hglobal) (by simpa [S] using hC)
      (by simpa [S] using hL) (by simpa [S] using hfive)
  have hallCircle : ∀ b ∈ S.blocksOfSize 5,
      ∃ Gamma : DeterminedCircle cfg, b = Sum.inr Gamma := by
    intro b hb
    rcases b with L | Gamma
    · have hbLine : (Sum.inl L : GeometricBlock cfg) ∈
          S.lineBlocksOfSize 5 := by
        apply S.mem_blocksOfKindSize.mpr
        exact ⟨by simp [S, blockSystem, geometricBlockSystem,
          geometricBlockKind], S.mem_blocksOfSize.mp hb⟩
      have hlineCard : (S.lineBlocksOfSize 5).card = 0 := by
        simpa [BlockSystem.lineCount] using hlineFive
      exact False.elim (by
        have hpositive := Finset.card_pos.mpr ⟨Sum.inl L, hbLine⟩
        omega)
    · exact ⟨Gamma, rfl⟩
  exact ⟨by simpa [S] using hdouble, by simpa [S] using hallCircle⟩

private theorem elevenFive_c40_l14_b5_seven_m39_clean_finite_core
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    (cfg : Configuration Point) (hpoint : Fintype.card Point = 11)
    (hcap : BlockSizeCap (blockSystem cfg) 5)
    (hlocal : ∀ p : Point, ElevenFiveLocalRows (blockSystem cfg) p)
    (hglobal : ElevenFiveGlobalRows (blockSystem cfg))
    (hC : (blockSystem cfg).totalCircleCount = 40)
    (hL : elevenFiveLineTotal (blockSystem cfg) = 14)
    (hfive : (blockSystem cfg).blockCount 5 = 7)
    (hmoment : elevenFiveSecondMoment (blockSystem cfg) = 39)
    (hnodisjoint : ∀ b ∈ (blockSystem cfg).blocksOfSize 5,
      ∀ c ∈ (blockSystem cfg).blocksOfSize 5, b ≠ c →
        ((blockSystem cfg).support b ∩
          (blockSystem cfg).support c).card ≠ 0) :
    ∃ clean : GeometricBlock cfg,
      clean ∈ (blockSystem cfg).blocksOfSize 5 ∧
      elevenFiveC40M39DefectDegree (blockSystem cfg) clean = 0 ∧
      (∀ b ∈ (blockSystem cfg).blocksOfSize 5,
        elevenFiveC40M39DefectDegree (blockSystem cfg) b = 0 ↔ b = clean) ∧
      (∀ b ∈ (blockSystem cfg).blocksOfSize 5, b ≠ clean →
        elevenFiveC40M39DefectDegree (blockSystem cfg) b = 1) ∧
      (∀ b ∈ (blockSystem cfg).blocksOfSize 5, b ≠ clean →
        ((blockSystem cfg).support clean ∩
          (blockSystem cfg).support b).card = 2) ∧
      (∀ b ∈ (blockSystem cfg).blocksOfSize 5,
        ∃ Gamma : DeterminedCircle cfg, b = Sum.inr Gamma) ∧
      ElevenFiveC40M39ThreeMatching (blockSystem cfg) := by
  obtain ⟨clean, hcleanFive, hcleanZero, hunique, hother, hshape⟩ :=
    elevenFive_c40_l14_b5_seven_m39_clean_vertex_core
      cfg hpoint hcap hlocal hglobal hC hL hfive hmoment hnodisjoint
  obtain ⟨hdouble, hallCircle⟩ :=
    elevenFive_c40_l14_b5_seven_m39_clean_geometry_core
      cfg hglobal hC hL hfive hnodisjoint clean hcleanFive hcleanZero
  exact ⟨clean, hcleanFive, hcleanZero, hunique, hother,
    hdouble, hallCircle, hshape⟩

private theorem elevenFive_c40_l14_b5_seven_m39_clean_high_core
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    (cfg : Configuration Point) (hpoint : Fintype.card Point = 11)
    (hlocal : ∀ p : Point, ElevenFiveLocalRows (blockSystem cfg) p)
    (hglobal : ElevenFiveGlobalRows (blockSystem cfg))
    (hfive : (blockSystem cfg).blockCount 5 = 7)
    (hmoment : elevenFiveSecondMoment (blockSystem cfg) = 39)
    (hnodisjoint : ∀ b ∈ (blockSystem cfg).blocksOfSize 5,
      ∀ c ∈ (blockSystem cfg).blocksOfSize 5, b ≠ c →
        ((blockSystem cfg).support b ∩
          (blockSystem cfg).support c).card ≠ 0)
    (clean : GeometricBlock cfg)
    (hcleanFive : clean ∈ (blockSystem cfg).blocksOfSize 5)
    (hcleanZero : elevenFiveC40M39DefectDegree
      (blockSystem cfg) clean = 0) :
    (elevenFiveC40M39HighOnFiveBlock
        (blockSystem cfg) clean).card = 2 ∧
      ∀ p : Point, (blockSystem cfg).blockDegree 5 p = 4 →
        p ∈ (blockSystem cfg).support clean := by
  have hhighClean :=
    elevenFive_c40_l14_b5_seven_m39_highOnBlock_add_defectDegree
      (blockSystem cfg) hpoint hlocal hglobal hfive hmoment clean hcleanFive
        (fun b hb hcb => hnodisjoint clean hcleanFive b hb hcb)
  have hhighCard : (elevenFiveC40M39HighOnFiveBlock
      (blockSystem cfg) clean).card = 2 := by omega
  refine ⟨hhighCard, ?_⟩
  intro p hp
  apply elevenFive_c40_l14_b5_seven_m39_high_subset_clean_block
    (blockSystem cfg) hpoint hlocal hglobal hfive hmoment clean hcleanFive
      hcleanZero (fun b hb hcb => hnodisjoint clean hcleanFive b hb hcb)
  simpa [hp]

private theorem elevenFive_c40_l14_b5_seven_m39_clean_mass_le_fiftySeven
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    (cfg : Configuration Point) (hpoint : Fintype.card Point = 11)
    (hlocal : ∀ p : Point, ElevenFiveLocalRows (blockSystem cfg) p)
    (hglobal : ElevenFiveGlobalRows (blockSystem cfg))
    (hC : (blockSystem cfg).totalCircleCount = 40)
    (hL : elevenFiveLineTotal (blockSystem cfg) = 14)
    (hfive : (blockSystem cfg).blockCount 5 = 7)
    (hmoment : elevenFiveSecondMoment (blockSystem cfg) = 39)
    (hnodisjoint : ∀ b ∈ (blockSystem cfg).blocksOfSize 5,
      ∀ c ∈ (blockSystem cfg).blocksOfSize 5, b ≠ c →
        ((blockSystem cfg).support b ∩
          (blockSystem cfg).support c).card ≠ 0)
    (clean : GeometricBlock cfg)
    (hcleanFive : clean ∈ (blockSystem cfg).blocksOfSize 5)
    (hhighCard : (elevenFiveC40M39HighOnFiveBlock
      (blockSystem cfg) clean).card = 2)
    (hhighCovers : ∀ p : Point, (blockSystem cfg).blockDegree 5 p = 4 →
      p ∈ (blockSystem cfg).support clean) :
    (∑ p ∈ (blockSystem cfg).support clean,
      (blockSystem cfg).blockDegree 3 p) ≤ 57 := by
  classical
  let S := blockSystem cfg
  let H := elevenFiveC40M39HighOnFiveBlock S clean
  let HG := (Finset.univ : Finset Point).filter fun p =>
    S.blockDegree 5 p = 4
  let R := S.support clean \ H
  have hHcard : H.card = 2 := by simpa [H, S] using hhighCard
  have hHsub : H ⊆ S.support clean := by
    intro p hp
    exact (Finset.mem_filter.mp (by simpa only [H] using hp)).1
  have hRcard : R.card = 3 := by
    rw [show R = S.support clean \ H by rfl,
      Finset.card_sdiff_of_subset hHsub,
      S.mem_blocksOfSize.mp (by simpa [S] using hcleanFive), hHcard]
  have hHHG : H = HG := by
    ext p
    simp only [H, HG, elevenFiveC40M39HighOnFiveBlock,
      Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨fun hp => hp.2, fun hp =>
      ⟨by simpa [S] using hhighCovers p (by simpa [S] using hp), hp⟩⟩
  have hHighMassLe : (∑ p ∈ H, S.blockDegree 3 p) ≤ 21 := by
    have hle :=
      elevenFive_c40_l14_b5_seven_m39_high_threeMass_le_twentyOne
        cfg hpoint hlocal hglobal hC hL hfive hmoment hnodisjoint
    change (∑ p ∈ HG, S.blockDegree 3 p) ≤ 21 at hle
    rwa [← hHHG] at hle
  have hRMassLe : (∑ p ∈ R, S.blockDegree 3 p) ≤ 36 := by
    calc
      (∑ p ∈ R, S.blockDegree 3 p) ≤ ∑ _p ∈ R, 12 := by
        apply Finset.sum_le_sum
        intro p _hp
        rcases elevenFive_c40_threeDegree_values S p
          (by simpa [S] using hlocal p) (by simpa [S] using hC) with
          h6 | h9 | h12 <;> omega
      _ = 36 := by simp [hRcard]
  have hHRdisj : Disjoint H R := by
    simpa only [R] using (Finset.disjoint_sdiff (s := H) (t := S.support clean))
  have hHRcover : H ∪ R = S.support clean :=
    Finset.union_sdiff_of_subset hHsub
  have hsplit : (∑ p ∈ S.support clean, S.blockDegree 3 p) =
      (∑ p ∈ H, S.blockDegree 3 p) + ∑ p ∈ R, S.blockDegree 3 p := by
    rw [← hHRcover]
    exact Finset.sum_union hHRdisj
  change (∑ p ∈ S.support clean, S.blockDegree 3 p) ≤ 57
  omega

private theorem elevenFive_c40_l14_b5_seven_m39_clean_mass_cases
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    (cfg : Configuration Point)
    (hlocal : ∀ p : Point, ElevenFiveLocalRows (blockSystem cfg) p)
    (hfive : (blockSystem cfg).blockCount 5 = 7)
    (clean : GeometricBlock cfg)
    (hcleanFive : clean ∈ (blockSystem cfg).blocksOfSize 5)
    (hdouble : ∀ b ∈ (blockSystem cfg).blocksOfSize 5, b ≠ clean →
      ((blockSystem cfg).support clean ∩
        (blockSystem cfg).support b).card = 2)
    (hmassLower : 49 ≤ ∑ p ∈ (blockSystem cfg).support clean,
      (blockSystem cfg).blockDegree 3 p)
    (hmassUpper : (∑ p ∈ (blockSystem cfg).support clean,
      (blockSystem cfg).blockDegree 3 p) ≤ 57) :
    (∑ p ∈ (blockSystem cfg).support clean,
      (blockSystem cfg).blockDegree 3 p) = 51 ∨
    (∑ p ∈ (blockSystem cfg).support clean,
      (blockSystem cfg).blockDegree 3 p) = 54 ∨
    (∑ p ∈ (blockSystem cfg).support clean,
      (blockSystem cfg).blockDegree 3 p) = 57 := by
  let S := blockSystem cfg
  have hsumFive : (∑ p ∈ S.support clean,
      S.blockDegree 5 p) = 17 := by
    apply c40FourteenSevenPageCap_support_fiveDegree_sum_eq_seventeen
      S clean (by simpa [S] using hcleanFive) (by simpa [S] using hfive)
    intro b hb hbc
    exact hdouble b (by simpa [S] using hb) hbc
  have hsumPair :
      (∑ p ∈ S.support clean,
        (S.blockDegree 3 p + 3 * S.blockDegree 4 p +
          6 * S.blockDegree 5 p)) =
        ∑ _p ∈ S.support clean, 45 := by
    apply Finset.sum_congr rfl
    intro p _hp
    simpa [S] using (hlocal p).pairRow
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at hsumPair
  have hcleanCard : (S.support clean).card = 5 :=
    S.mem_blocksOfSize.mp (by simpa [S] using hcleanFive)
  have hconstant : (∑ _p ∈ S.support clean, 45) = 225 := by
    simp [hcleanCard]
  rw [hsumFive, hconstant] at hsumPair
  change 49 ≤ ∑ p ∈ S.support clean, S.blockDegree 3 p at hmassLower
  change (∑ p ∈ S.support clean, S.blockDegree 3 p) ≤ 57 at hmassUpper
  change (∑ p ∈ S.support clean, S.blockDegree 3 p) = 51 ∨
    (∑ p ∈ S.support clean, S.blockDegree 3 p) = 54 ∨
    (∑ p ∈ S.support clean, S.blockDegree 3 p) = 57
  omega

private theorem elevenFive_c40_l14_b5_seven_m39_high_on_other
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    (cfg : Configuration Point) (hpoint : Fintype.card Point = 11)
    (hlocal : ∀ p : Point, ElevenFiveLocalRows (blockSystem cfg) p)
    (hglobal : ElevenFiveGlobalRows (blockSystem cfg))
    (hfive : (blockSystem cfg).blockCount 5 = 7)
    (hmoment : elevenFiveSecondMoment (blockSystem cfg) = 39)
    (hnodisjoint : ∀ b ∈ (blockSystem cfg).blocksOfSize 5,
      ∀ c ∈ (blockSystem cfg).blocksOfSize 5, b ≠ c →
        ((blockSystem cfg).support b ∩
          (blockSystem cfg).support c).card ≠ 0)
    (clean : GeometricBlock cfg)
    (hother : ∀ b ∈ (blockSystem cfg).blocksOfSize 5, b ≠ clean →
      elevenFiveC40M39DefectDegree (blockSystem cfg) b = 1) :
    ∀ b ∈ (blockSystem cfg).blocksOfSize 5, b ≠ clean →
      (elevenFiveC40M39HighOnFiveBlock
        (blockSystem cfg) b).card = 1 := by
  intro b hb hbc
  have hid :=
    elevenFive_c40_l14_b5_seven_m39_highOnBlock_add_defectDegree
      (blockSystem cfg) hpoint hlocal hglobal hfive hmoment b hb
        (fun c hc hcb => hnodisjoint b hb c hc hcb)
  rw [hother b hb hbc] at hid
  omega

/-- The finite/page-cap argument reaches the preceding residual without
any geometric assumption. -/
noncomputable def elevenFive_c40_l14_b5_seven_m39_threeMatchingPageResidual
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    (cfg : Configuration Point) (hpoint : Fintype.card Point = 11)
    (hcap : BlockSizeCap (blockSystem cfg) 5)
    (hlocal : ∀ p : Point, ElevenFiveLocalRows (blockSystem cfg) p)
    (hglobal : ElevenFiveGlobalRows (blockSystem cfg))
    (hC : (blockSystem cfg).totalCircleCount = 40)
    (hL : elevenFiveLineTotal (blockSystem cfg) = 14)
    (hfive : (blockSystem cfg).blockCount 5 = 7)
    (hmoment : elevenFiveSecondMoment (blockSystem cfg) = 39)
    (hnodisjoint : ∀ b ∈ (blockSystem cfg).blocksOfSize 5,
      ∀ c ∈ (blockSystem cfg).blocksOfSize 5, b ≠ c →
        ((blockSystem cfg).support b ∩
          (blockSystem cfg).support c).card ≠ 0) :
    ElevenFiveC40M39ThreeMatchingPageResidual cfg := by
  classical
  let S := blockSystem cfg
  have hcore :=
    elevenFive_c40_l14_b5_seven_m39_clean_finite_core
      cfg hpoint hcap hlocal hglobal hC hL hfive hmoment hnodisjoint
  let clean := Classical.choose hcore
  have hcleanDef : clean = Classical.choose hcore := rfl
  have hcoreSpec := Classical.choose_spec hcore
  rw [← hcleanDef] at hcoreSpec
  rcases hcoreSpec with ⟨hcleanFive, hcleanZero, hunique, hother,
    hdouble, hallCircle, hshape⟩
  have hmass :=
    elevenFive_c40_l14_b5_seven_clean_threeMass_ge_fortyNine
      cfg hpoint hcap hlocal hglobal hC hL hfive clean
        (by simpa [S] using hcleanFive)
          (fun b hb hbc => hdouble b (by simpa [S] using hb) hbc)
  obtain ⟨hhighCard, hhighCovers⟩ :=
    elevenFive_c40_l14_b5_seven_m39_clean_high_core
      cfg hpoint hlocal hglobal hfive hmoment hnodisjoint clean
        hcleanFive hcleanZero
  have hmassUpper :=
    elevenFive_c40_l14_b5_seven_m39_clean_mass_le_fiftySeven
      cfg hpoint hlocal hglobal hC hL hfive hmoment hnodisjoint clean
        hcleanFive hhighCard hhighCovers
  have hmassCases :=
    elevenFive_c40_l14_b5_seven_m39_clean_mass_cases
      cfg hlocal hfive clean hcleanFive hdouble hmass hmassUpper
  have hhighOther :=
    elevenFive_c40_l14_b5_seven_m39_high_on_other
      cfg hpoint hlocal hglobal hfive hmoment hnodisjoint clean hother
  refine
    { clean := clean
      clean_five := by simpa [S] using hcleanFive
      all_circle := by simpa [S] using hallCircle
      clean_unique := by simpa [S] using hunique
      other_degree_one := by simpa [S] using hother
      clean_double := by simpa [S] using hdouble
      clean_mass_ge := by simpa [S] using hmass
      clean_mass_cases := by simpa [S] using hmassCases
      high_card := by simpa [S] using hhighCard
      high_covers := by simpa [S] using hhighCovers
      high_on_other := by simpa [S] using hhighOther
      defect_edges_card := by simpa [S] using hshape.1
      defect_matching := by
        simpa [S] using c40M39_threeMatching_isPerfectMatching
          S clean hcleanFive hcleanZero hother
      edge_carrier := ?_ }
  intro A hA
  exact elevenFive_c40_l14_b5_seven_m39_defectEdge_carrier
    cfg hpoint hlocal hglobal hC hfive hmoment A hA

/-- Every matching edge joins opposite high fibres.  Equivalently, the
unique high pivot on each of its two endpoint blocks is different. -/
theorem ElevenFiveC40M39ThreeMatchingPageResidual.edge_high_disjoint
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point}
    (R : ElevenFiveC40M39ThreeMatchingPageResidual cfg)
    {A : Finset (GeometricBlock cfg)}
    (hA : A ∈ elevenFiveC40M39DefectEdges (blockSystem cfg))
    {b c : GeometricBlock cfg} (hb : b ∈ A) (hc : c ∈ A)
    (hbc : b ≠ c) :
    Disjoint
      (elevenFiveC40M39HighOnFiveBlock (blockSystem cfg) b)
      (elevenFiveC40M39HighOnFiveBlock (blockSystem cfg) c) := by
  classical
  let S := blockSystem cfg
  have hpair := R.defect_matching.pair A hA
  have hsub : ({b, c} : Finset (GeometricBlock cfg)) ⊆ A := by
    intro d hd
    simp only [Finset.mem_insert, Finset.mem_singleton] at hd
    rcases hd with rfl | rfl
    · exact hb
    · exact hc
  have hAeq : A = {b, c} := by
    have hpairCard : ({b, c} : Finset (GeometricBlock cfg)).card = 2 := by
      simp [hbc]
    have hcardLe : A.card ≤ ({b, c} : Finset (GeometricBlock cfg)).card := by
      rw [hpair.1, hpairCard]
    have heq := Finset.eq_of_subset_of_card_le hsub hcardLe
    exact heq.symm
  rw [Finset.disjoint_left]
  intro x hxb hxc
  have hxbData := Finset.mem_filter.mp hxb
  have hxcData := Finset.mem_filter.mp hxc
  have hxCommon : x ∈ S.commonSupport A := by
    rw [hAeq, S.commonSupport_pair]
    exact Finset.mem_inter.mpr ⟨hxbData.1, hxcData.1⟩
  obtain ⟨p, hpCommon, _hp12, hp3⟩ := R.edge_carrier A hA
  have hAdata := Finset.mem_filter.mp
    (by simpa only [S, elevenFiveC40M39DefectEdges] using hA)
  have hcommonLe : (S.commonSupport A).card ≤ 1 := by
    rw [hAdata.2]
  have hxp : x = p :=
    Finset.card_le_one.mp hcommonLe x hxCommon p (by simpa [S] using hpCommon)
  subst p
  have hx4 : S.blockDegree 5 x = 4 := hxbData.2
  have hx3 : S.blockDegree 5 x = 3 := by simpa [S] using hp3
  omega

noncomputable def ElevenFiveC40M39ThreeMatchingPageResidual.otherBlocks
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point}
    (R : ElevenFiveC40M39ThreeMatchingPageResidual cfg) :
    Finset (GeometricBlock cfg) :=
  ((blockSystem cfg).blocksOfSize 5).erase R.clean

noncomputable def ElevenFiveC40M39ThreeMatchingPageResidual.highFibre
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point}
    (R : ElevenFiveC40M39ThreeMatchingPageResidual cfg) (p : Point) :
    Finset (GeometricBlock cfg) :=
  R.otherBlocks.filter fun b => p ∈ (blockSystem cfg).support b

/-- Canonical `3+3` presentation of `3K2`: the six nonclean blocks split
by their unique high pivot, and every singleton edge crosses the split. -/
structure ElevenFiveC40M39ThreeMatchingBipartiteTrace
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    (cfg : Configuration Point) where
  page : ElevenFiveC40M39ThreeMatchingPageResidual cfg
  leftHigh : Point
  rightHigh : Point
  high_ne : leftHigh ≠ rightHigh
  clean_high_eq : elevenFiveC40M39HighOnFiveBlock
    (blockSystem cfg) page.clean = {leftHigh, rightHigh}
  left_card : (page.highFibre leftHigh).card = 3
  right_card : (page.highFibre rightHigh).card = 3
  fibres_disjoint : Disjoint (page.highFibre leftHigh)
    (page.highFibre rightHigh)
  fibres_cover : page.highFibre leftHigh ∪ page.highFibre rightHigh =
    page.otherBlocks
  edge_split : ∀ A ∈ elevenFiveC40M39DefectEdges (blockSystem cfg),
    ∃ b ∈ page.highFibre leftHigh, ∃ c ∈ page.highFibre rightHigh,
      A = {b, c}

private theorem ElevenFiveC40M39ThreeMatchingPageResidual.high_fibre_card
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point}
    (R : ElevenFiveC40M39ThreeMatchingPageResidual cfg) (p : Point)
    (hp : p ∈ elevenFiveC40M39HighOnFiveBlock
      (blockSystem cfg) R.clean) :
    (R.highFibre p).card = 3 := by
  classical
  let S := blockSystem cfg
  have hp' : p ∈ elevenFiveC40M39HighOnFiveBlock S R.clean := by
    simpa only [S] using hp
  have hpData := Finset.mem_filter.mp hp'
  have hp4 : S.blockDegree 5 p = 4 := hpData.2
  let I := (S.blocksOfSize 5).filter fun b => p ∈ S.support b
  have hICard : I.card = 4 := by
    simpa [I, BlockSystem.blockDegree, BlockSystem.degreeIn] using hp4
  have hcleanI : R.clean ∈ I :=
    Finset.mem_filter.mpr ⟨by simpa [S] using R.clean_five, hpData.1⟩
  have hfibreEq : R.highFibre p = I.erase R.clean := by
    simpa [ElevenFiveC40M39ThreeMatchingPageResidual.highFibre,
      ElevenFiveC40M39ThreeMatchingPageResidual.otherBlocks, I, S] using
        (Finset.filter_erase R.clean (S.blocksOfSize 5)
          (p := fun b => p ∈ S.support b))
  rw [hfibreEq, Finset.card_erase_of_mem hcleanI, hICard]

private theorem ElevenFiveC40M39ThreeMatchingPageResidual.high_fibres_disjoint
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point}
    (R : ElevenFiveC40M39ThreeMatchingPageResidual cfg)
    (a z : Point) (haz : a ≠ z)
    (hHeq : elevenFiveC40M39HighOnFiveBlock
      (blockSystem cfg) R.clean = {a, z}) :
    Disjoint (R.highFibre a) (R.highFibre z) := by
  classical
  let S := blockSystem cfg
  have haClean : a ∈ elevenFiveC40M39HighOnFiveBlock S R.clean := by
    rw [show elevenFiveC40M39HighOnFiveBlock S R.clean = {a, z} by
      simpa [S] using hHeq]
    simp
  have hzClean : z ∈ elevenFiveC40M39HighOnFiveBlock S R.clean := by
    rw [show elevenFiveC40M39HighOnFiveBlock S R.clean = {a, z} by
      simpa [S] using hHeq]
    simp
  have ha4 := (Finset.mem_filter.mp haClean).2
  have hz4 := (Finset.mem_filter.mp hzClean).2
  rw [Finset.disjoint_left]
  intro b hbA hbZ
  have hbAData := Finset.mem_filter.mp hbA
  have hbZData := Finset.mem_filter.mp hbZ
  have haHigh : a ∈ elevenFiveC40M39HighOnFiveBlock S b :=
    Finset.mem_filter.mpr ⟨hbAData.2, ha4⟩
  have hzHigh : z ∈ elevenFiveC40M39HighOnFiveBlock S b :=
    Finset.mem_filter.mpr ⟨hbZData.2, hz4⟩
  have hsub : ({a, z} : Finset Point) ⊆
      elevenFiveC40M39HighOnFiveBlock S b := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact haHigh
    · exact hzHigh
  have htwo := Finset.card_le_card hsub
  have hbOther := Finset.mem_erase.mp hbAData.1
  have hone := R.high_on_other b (by simpa [S] using hbOther.2) hbOther.1
  have hpairCard : ({a, z} : Finset Point).card = 2 := by simp [haz]
  rw [hpairCard, hone] at htwo
  omega

private theorem ElevenFiveC40M39ThreeMatchingPageResidual.high_fibres_cover
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point}
    (R : ElevenFiveC40M39ThreeMatchingPageResidual cfg)
    (a z : Point)
    (hHeq : elevenFiveC40M39HighOnFiveBlock
      (blockSystem cfg) R.clean = {a, z}) :
    R.highFibre a ∪ R.highFibre z = R.otherBlocks := by
  classical
  let S := blockSystem cfg
  apply Finset.Subset.antisymm
  · exact Finset.union_subset (fun _ h => (Finset.mem_filter.mp h).1)
      (fun _ h => (Finset.mem_filter.mp h).1)
  · intro b hbOther
    have hbOther' : b ∈ (S.blocksOfSize 5).erase R.clean := by
      simpa only [S,
        ElevenFiveC40M39ThreeMatchingPageResidual.otherBlocks] using hbOther
    have hbErase := Finset.mem_erase.mp hbOther'
    have hone := R.high_on_other b (by simpa [S] using hbErase.2) hbErase.1
    obtain ⟨x, hxEq⟩ := Finset.card_eq_one.mp hone
    have hxHigh : x ∈ elevenFiveC40M39HighOnFiveBlock S b := by
      rw [hxEq]
      simp
    have hxData := Finset.mem_filter.mp hxHigh
    have hxClean := R.high_covers x (by simpa [S] using hxData.2)
    have hxCleanHigh : x ∈ elevenFiveC40M39HighOnFiveBlock S R.clean :=
      Finset.mem_filter.mpr ⟨hxClean, hxData.2⟩
    have hxPair : x ∈ ({a, z} : Finset Point) := by
      rw [← show elevenFiveC40M39HighOnFiveBlock S R.clean = {a, z} by
        simpa [S] using hHeq]
      exact hxCleanHigh
    rcases Finset.mem_insert.mp hxPair with hxa | hxz
    · exact Finset.mem_union_left _
        (Finset.mem_filter.mpr ⟨hbOther, by simpa [hxa] using hxData.1⟩)
    · have hxz' : x = z := by simpa using hxz
      exact Finset.mem_union_right _
        (Finset.mem_filter.mpr ⟨hbOther, by simpa [hxz'] using hxData.1⟩)

private theorem ElevenFiveC40M39ThreeMatchingPageResidual.high_fibre_partition
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point}
    (R : ElevenFiveC40M39ThreeMatchingPageResidual cfg)
    (a z : Point) (haz : a ≠ z)
    (hHeq : elevenFiveC40M39HighOnFiveBlock
      (blockSystem cfg) R.clean = {a, z}) :
    (R.highFibre a).card = 3 ∧
      (R.highFibre z).card = 3 ∧
      Disjoint (R.highFibre a) (R.highFibre z) ∧
      R.highFibre a ∪ R.highFibre z = R.otherBlocks := by
  have haMem : a ∈ elevenFiveC40M39HighOnFiveBlock
      (blockSystem cfg) R.clean := by rw [hHeq]; simp
  have hzMem : z ∈ elevenFiveC40M39HighOnFiveBlock
      (blockSystem cfg) R.clean := by rw [hHeq]; simp
  exact ⟨R.high_fibre_card a haMem, R.high_fibre_card z hzMem,
    R.high_fibres_disjoint a z haz hHeq,
    R.high_fibres_cover a z hHeq⟩

private theorem ElevenFiveC40M39ThreeMatchingPageResidual.edge_split_between_fibres
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point}
    (R : ElevenFiveC40M39ThreeMatchingPageResidual cfg)
    (a z : Point)
    (ha4 : (blockSystem cfg).blockDegree 5 a = 4)
    (hz4 : (blockSystem cfg).blockDegree 5 z = 4)
    (hfibreCover : R.highFibre a ∪ R.highFibre z = R.otherBlocks) :
    ∀ A ∈ elevenFiveC40M39DefectEdges (blockSystem cfg),
      ∃ b ∈ R.highFibre a, ∃ c ∈ R.highFibre z, A = {b, c} := by
  classical
  let S := blockSystem cfg
  intro A hA
  obtain ⟨b, c, hbc, hAeq⟩ :=
    Finset.card_eq_two.mp (R.defect_matching.pair A hA).1
  have hbA : b ∈ A := by rw [hAeq]; simp
  have hcA : c ∈ A := by rw [hAeq]; simp
  have hbOther := (R.defect_matching.pair A hA).2 hbA
  have hcOther := (R.defect_matching.pair A hA).2 hcA
  have hbCover : b ∈ R.highFibre a ∪ R.highFibre z := by
    rw [hfibreCover]
    exact hbOther
  have hcCover : c ∈ R.highFibre a ∪ R.highFibre z := by
    rw [hfibreCover]
    exact hcOther
  have hcross := R.edge_high_disjoint hA hbA hcA hbc
  rcases Finset.mem_union.mp hbCover with hbLeft | hbRight <;>
    rcases Finset.mem_union.mp hcCover with hcLeft | hcRight
  · have hbData := Finset.mem_filter.mp hbLeft
    have hcData := Finset.mem_filter.mp hcLeft
    have haB : a ∈ elevenFiveC40M39HighOnFiveBlock S b :=
      Finset.mem_filter.mpr ⟨hbData.2, by simpa [S] using ha4⟩
    have haC : a ∈ elevenFiveC40M39HighOnFiveBlock S c :=
      Finset.mem_filter.mpr ⟨hcData.2, by simpa [S] using ha4⟩
    exact False.elim ((Finset.disjoint_left.mp hcross) haB haC)
  · exact ⟨b, hbLeft, c, hcRight, hAeq⟩
  · exact ⟨c, hcLeft, b, hbRight, by
      simpa [Finset.pair_comm] using hAeq⟩
  · have hbData := Finset.mem_filter.mp hbRight
    have hcData := Finset.mem_filter.mp hcRight
    have hzB : z ∈ elevenFiveC40M39HighOnFiveBlock S b :=
      Finset.mem_filter.mpr ⟨hbData.2, by simpa [S] using hz4⟩
    have hzC : z ∈ elevenFiveC40M39HighOnFiveBlock S c :=
      Finset.mem_filter.mpr ⟨hcData.2, by simpa [S] using hz4⟩
    exact False.elim ((Finset.disjoint_left.mp hcross) hzB hzC)

/-- Index-free construction of the canonical `3+3` trace.  Choosing
equivalences of the two three-element fibres with `Fin 3` gives the usual
`3 x 3` presentation. -/
noncomputable def ElevenFiveC40M39ThreeMatchingPageResidual.bipartiteTrace
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point}
    (R : ElevenFiveC40M39ThreeMatchingPageResidual cfg) :
    ElevenFiveC40M39ThreeMatchingBipartiteTrace cfg := by
  classical
  let S := blockSystem cfg
  let H := elevenFiveC40M39HighOnFiveBlock S R.clean
  have hHighPair := Finset.card_eq_two.mp (by
    simpa [H, S] using R.high_card)
  let a := Classical.choose hHighPair
  have haRest := Classical.choose_spec hHighPair
  let z := Classical.choose haRest
  have hzSpec := Classical.choose_spec haRest
  have haz : a ≠ z := hzSpec.1
  have hHeq : H = {a, z} := hzSpec.2
  have haH : a ∈ H := by rw [hHeq]; simp
  have hzH : z ∈ H := by rw [hHeq]; simp
  have haData := Finset.mem_filter.mp (by simpa only [H] using haH)
  have hzData := Finset.mem_filter.mp (by simpa only [H] using hzH)
  have ha4 : S.blockDegree 5 a = 4 := haData.2
  have hz4 : S.blockDegree 5 z = 4 := hzData.2
  obtain ⟨hleftCard, hrightCard, hfibreDisjoint, hfibreCover⟩ :=
    R.high_fibre_partition a z haz (by simpa [S, H] using hHeq)
  have hedgeSplit :=
    R.edge_split_between_fibres a z
      (by simpa [S] using ha4) (by simpa [S] using hz4) hfibreCover
  exact
    { page := R
      leftHigh := a
      rightHigh := z
      high_ne := haz
      clean_high_eq := by simpa [S, H] using hHeq
      left_card := hleftCard
      right_card := hrightCard
      fibres_disjoint := hfibreDisjoint
      fibres_cover := hfibreCover
      edge_split := by simpa [S] using hedgeSplit }

/-- Public one-call entrance to the last M39 geometry seam. -/
noncomputable def elevenFive_c40_l14_b5_seven_m39_bipartiteTrace
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    (cfg : Configuration Point) (hpoint : Fintype.card Point = 11)
    (hcap : BlockSizeCap (blockSystem cfg) 5)
    (hlocal : ∀ p : Point, ElevenFiveLocalRows (blockSystem cfg) p)
    (hglobal : ElevenFiveGlobalRows (blockSystem cfg))
    (hC : (blockSystem cfg).totalCircleCount = 40)
    (hL : elevenFiveLineTotal (blockSystem cfg) = 14)
    (hfive : (blockSystem cfg).blockCount 5 = 7)
    (hmoment : elevenFiveSecondMoment (blockSystem cfg) = 39)
    (hnodisjoint : ∀ b ∈ (blockSystem cfg).blocksOfSize 5,
      ∀ c ∈ (blockSystem cfg).blocksOfSize 5, b ≠ c →
        ((blockSystem cfg).support b ∩
          (blockSystem cfg).support c).card ≠ 0) :
    ElevenFiveC40M39ThreeMatchingBipartiteTrace cfg :=
  (elevenFive_c40_l14_b5_seven_m39_threeMatchingPageResidual
    cfg hpoint hcap hlocal hglobal hC hL hfive hmoment hnodisjoint).bipartiteTrace

/-- The two high fibres of the last `3K2` row contain a genuine neutral
`(9,4,4)` pivot.  The local sigma row excludes three-degree six at
five-degree four, while the already proved high-mass bound excludes two
three-degree-twelve highs. -/
theorem elevenFive_c40_l14_b5_seven_m39_bipartiteTrace_exists_944
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    (cfg : Configuration Point) (hpoint : Fintype.card Point = 11)
    (hcap : BlockSizeCap (blockSystem cfg) 5)
    (hlocal : ∀ p : Point, ElevenFiveLocalRows (blockSystem cfg) p)
    (hglobal : ElevenFiveGlobalRows (blockSystem cfg))
    (hC : (blockSystem cfg).totalCircleCount = 40)
    (hL : elevenFiveLineTotal (blockSystem cfg) = 14)
    (hfive : (blockSystem cfg).blockCount 5 = 7)
    (hmoment : elevenFiveSecondMoment (blockSystem cfg) = 39)
    (hnodisjoint : ∀ b ∈ (blockSystem cfg).blocksOfSize 5,
      ∀ c ∈ (blockSystem cfg).blocksOfSize 5, b ≠ c →
        ((blockSystem cfg).support b ∩
          (blockSystem cfg).support c).card ≠ 0) :
    ∃ T : ElevenFiveC40M39ThreeMatchingBipartiteTrace cfg,
      ∃ p : Point, p ∈ elevenFive944Pivots (blockSystem cfg) ∧
        (p = T.leftHigh ∨ p = T.rightHigh) := by
  classical
  let S := blockSystem cfg
  let T := elevenFive_c40_l14_b5_seven_m39_bipartiteTrace
    cfg hpoint hcap hlocal hglobal hC hL hfive hmoment hnodisjoint
  have haHigh : T.leftHigh ∈ elevenFiveC40M39HighOnFiveBlock S T.page.clean := by
    rw [show elevenFiveC40M39HighOnFiveBlock S T.page.clean =
      {T.leftHigh, T.rightHigh} by simpa [S] using T.clean_high_eq]
    simp
  have hzHigh : T.rightHigh ∈ elevenFiveC40M39HighOnFiveBlock S T.page.clean := by
    rw [show elevenFiveC40M39HighOnFiveBlock S T.page.clean =
      {T.leftHigh, T.rightHigh} by simpa [S] using T.clean_high_eq]
    simp
  have ha4 : S.blockDegree 5 T.leftHigh = 4 :=
    (Finset.mem_filter.mp haHigh).2
  have hz4 : S.blockDegree 5 T.rightHigh = 4 :=
    (Finset.mem_filter.mp hzHigh).2
  have hHighEq : (Finset.univ : Finset Point).filter
      (fun p => S.blockDegree 5 p = 4) = {T.leftHigh, T.rightHigh} := by
    ext p
    constructor
    · intro hp
      have hp4 := (Finset.mem_filter.mp hp).2
      have hpClean : p ∈ S.support T.page.clean := by
        simpa [S] using T.page.high_covers p (by simpa [S] using hp4)
      have hpHigh : p ∈ elevenFiveC40M39HighOnFiveBlock S T.page.clean :=
        Finset.mem_filter.mpr ⟨hpClean, hp4⟩
      rw [show elevenFiveC40M39HighOnFiveBlock S T.page.clean =
        {T.leftHigh, T.rightHigh} by simpa [S] using T.clean_high_eq] at hpHigh
      exact hpHigh
    · intro hp
      simp only [Finset.mem_insert, Finset.mem_singleton] at hp
      rcases hp with rfl | rfl <;> simp [ha4, hz4]
  have hmass :=
    elevenFive_c40_l14_b5_seven_m39_high_threeMass_le_twentyOne
      cfg hpoint hlocal hglobal hC hL hfive hmoment hnodisjoint
  have hsum : S.blockDegree 3 T.leftHigh +
      S.blockDegree 3 T.rightHigh ≤ 21 := by
    change (∑ p ∈ (Finset.univ : Finset Point).filter
      (fun p => S.blockDegree 5 p = 4), S.blockDegree 3 p) ≤ 21 at hmass
    rw [hHighEq] at hmass
    simpa [T.high_ne] using hmass
  have haNotSix : S.blockDegree 3 T.leftHigh ≠ 6 := by
    intro ha6
    have hsigma := (hlocal T.leftHigh).sigmaRow
    change elevenFiveSigmaAt S T.leftHigh + 3 + S.blockDegree 5 T.leftHigh =
      S.blockDegree 3 T.leftHigh at hsigma
    rw [ha4, ha6] at hsigma
    omega
  have hzNotSix : S.blockDegree 3 T.rightHigh ≠ 6 := by
    intro hz6
    have hsigma := (hlocal T.rightHigh).sigmaRow
    change elevenFiveSigmaAt S T.rightHigh + 3 + S.blockDegree 5 T.rightHigh =
      S.blockDegree 3 T.rightHigh at hsigma
    rw [hz4, hz6] at hsigma
    omega
  have haCases : S.blockDegree 3 T.leftHigh = 9 ∨
      S.blockDegree 3 T.leftHigh = 12 :=
    (elevenFive_c40_threeDegree_values S T.leftHigh
      (by simpa [S] using hlocal T.leftHigh) (by simpa [S] using hC)).resolve_left
        haNotSix
  have hzCases : S.blockDegree 3 T.rightHigh = 9 ∨
      S.blockDegree 3 T.rightHigh = 12 :=
    (elevenFive_c40_threeDegree_values S T.rightHigh
      (by simpa [S] using hlocal T.rightHigh) (by simpa [S] using hC)).resolve_left
        hzNotSix
  have hNine : S.blockDegree 3 T.leftHigh = 9 ∨
      S.blockDegree 3 T.rightHigh = 9 := by
    rcases haCases with ha9 | ha12
    · exact Or.inl ha9
    · rcases hzCases with hz9 | hz12
      · exact Or.inr hz9
      · omega
  refine ⟨T, ?_⟩
  rcases hNine with ha9 | hz9
  · have haFour : S.blockDegree 4 T.leftHigh = 4 := by
      have hpair := (hlocal T.leftHigh).pairRow
      change S.blockDegree 3 T.leftHigh + 3 * S.blockDegree 4 T.leftHigh +
        6 * S.blockDegree 5 T.leftHigh = 45 at hpair
      omega
    refine ⟨T.leftHigh, ?_, Or.inl rfl⟩
    exact (mem_elevenFive944Pivots S T.leftHigh).2 ⟨ha9, haFour, ha4⟩
  · have hzFour : S.blockDegree 4 T.rightHigh = 4 := by
      have hpair := (hlocal T.rightHigh).pairRow
      change S.blockDegree 3 T.rightHigh + 3 * S.blockDegree 4 T.rightHigh +
        6 * S.blockDegree 5 T.rightHigh = 45 at hpair
      omega
    refine ⟨T.rightHigh, ?_, Or.inr rfl⟩
    exact (mem_elevenFive944Pivots S T.rightHigh).2 ⟨hz9, hzFour, hz4⟩

noncomputable def ElevenFiveC40M39ThreeMatchingBipartiteTrace.leftIndex
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point}
    (T : ElevenFiveC40M39ThreeMatchingBipartiteTrace cfg) :
    Fin 3 ≃ ↑(T.page.highFibre T.leftHigh) :=
  (Finset.equivFinOfCardEq T.left_card).symm

noncomputable def ElevenFiveC40M39ThreeMatchingBipartiteTrace.rightIndex
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point}
    (T : ElevenFiveC40M39ThreeMatchingBipartiteTrace cfg) :
    Fin 3 ≃ ↑(T.page.highFibre T.rightHigh) :=
  (Finset.equivFinOfCardEq T.right_card).symm

noncomputable def ElevenFiveC40M39ThreeMatchingBipartiteTrace.leftBlock
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point}
    (T : ElevenFiveC40M39ThreeMatchingBipartiteTrace cfg) (i : Fin 3) :
    GeometricBlock cfg := (T.leftIndex i).1

noncomputable def ElevenFiveC40M39ThreeMatchingBipartiteTrace.rightBlock
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point}
    (T : ElevenFiveC40M39ThreeMatchingBipartiteTrace cfg) (i : Fin 3) :
    GeometricBlock cfg := (T.rightIndex i).1

theorem ElevenFiveC40M39ThreeMatchingBipartiteTrace.leftBlock_mem
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point}
    (T : ElevenFiveC40M39ThreeMatchingBipartiteTrace cfg) (i : Fin 3) :
    T.leftBlock i ∈ T.page.highFibre T.leftHigh := (T.leftIndex i).2

theorem ElevenFiveC40M39ThreeMatchingBipartiteTrace.rightBlock_mem
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point}
    (T : ElevenFiveC40M39ThreeMatchingBipartiteTrace cfg) (i : Fin 3) :
    T.rightBlock i ∈ T.page.highFibre T.rightHigh := (T.rightIndex i).2

theorem ElevenFiveC40M39ThreeMatchingBipartiteTrace.leftBlock_five
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point}
    (T : ElevenFiveC40M39ThreeMatchingBipartiteTrace cfg) (i : Fin 3) :
    T.leftBlock i ∈ (blockSystem cfg).blocksOfSize 5 := by
  have hother := (Finset.mem_filter.mp (T.leftBlock_mem i)).1
  exact (Finset.mem_erase.mp (by simpa [
    ElevenFiveC40M39ThreeMatchingPageResidual.otherBlocks] using hother)).2

theorem ElevenFiveC40M39ThreeMatchingBipartiteTrace.rightBlock_five
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point}
    (T : ElevenFiveC40M39ThreeMatchingBipartiteTrace cfg) (i : Fin 3) :
    T.rightBlock i ∈ (blockSystem cfg).blocksOfSize 5 := by
  have hother := (Finset.mem_filter.mp (T.rightBlock_mem i)).1
  exact (Finset.mem_erase.mp (by simpa [
    ElevenFiveC40M39ThreeMatchingPageResidual.otherBlocks] using hother)).2

noncomputable def ElevenFiveC40M39ThreeMatchingBipartiteTrace.leftCircle
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point}
    (T : ElevenFiveC40M39ThreeMatchingBipartiteTrace cfg) (i : Fin 3) :
    DeterminedCircle cfg :=
  Classical.choose (T.page.all_circle (T.leftBlock i) (T.leftBlock_five i))

noncomputable def ElevenFiveC40M39ThreeMatchingBipartiteTrace.rightCircle
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point}
    (T : ElevenFiveC40M39ThreeMatchingBipartiteTrace cfg) (i : Fin 3) :
    DeterminedCircle cfg :=
  Classical.choose (T.page.all_circle (T.rightBlock i) (T.rightBlock_five i))

theorem ElevenFiveC40M39ThreeMatchingBipartiteTrace.leftBlock_eq_circle
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point}
    (T : ElevenFiveC40M39ThreeMatchingBipartiteTrace cfg) (i : Fin 3) :
    T.leftBlock i = Sum.inr (T.leftCircle i) :=
  Classical.choose_spec
    (T.page.all_circle (T.leftBlock i) (T.leftBlock_five i))

theorem ElevenFiveC40M39ThreeMatchingBipartiteTrace.rightBlock_eq_circle
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point}
    (T : ElevenFiveC40M39ThreeMatchingBipartiteTrace cfg) (i : Fin 3) :
    T.rightBlock i = Sum.inr (T.rightCircle i) :=
  Classical.choose_spec
    (T.page.all_circle (T.rightBlock i) (T.rightBlock_five i))

end Erdos506.V1
