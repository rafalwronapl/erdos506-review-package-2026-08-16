import Erdos506.V1.ElevenFiveC39H28GraphTail
import Mathlib.Tactic

/-!
# The finite singleton-graph double count at `C = 39`, `L = 12`

This file contains only the finite tail isolated in
`ElevenFiveC39H28GraphTail`.  In particular, it assumes the singleton
neighbour supplied by that interface; it does not replace the separate
geometric extraction of such a neighbour in the exact `H = 28` layer.
-/

namespace Erdos506.V1

open Erdos506.Block
open Erdos506.Block.BlockSystem
open Erdos506.Incidence
open Erdos506.V3
open Erdos506.V4
open scoped BigOperators

universe u v

private theorem c39H28_threeDegree_six_or_nine
    {Point : Type u} {Block : Type v} [Fintype Point] [Fintype Block]
    [DecidableEq Point]
    (S : BlockSystem Point Block) (p : Point)
    (hlocal : ElevenFiveLocalRows S p)
    (hC : S.totalCircleCount = 39) :
    S.blockDegree 3 p = 6 ∨ S.blockDegree 3 p = 9 := by
  have hpair := hlocal.pairRow
  have harms := hlocal.lineArmRow
  have hsplit := hlocal.threeSplit
  have hkelly := hlocal.kelly
  have hdelete := hlocal.deletion
  rw [hC] at hdelete
  have hline : S.lineDegree 3 p ≤ 5 := by omega
  have hcircle : S.circleDegree 3 p ≤ 6 := by omega
  omega

/-- A singleton pair in the C39 row has the exact carrier profile used by
the global graph count. -/
private theorem c39H28_singleton_carrier_profile
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    (cfg : Configuration Point) (hcard : Fintype.card Point = 11)
    (p : Point)
    (hlocal : ∀ q : Point, ElevenFiveLocalRows (blockSystem cfg) q)
    (hC : (blockSystem cfg).totalCircleCount = 39)
    {b c : GeometricBlock cfg}
    (hb : b ∈ (blockSystem cfg).blocksOfSize 5)
    (hc : c ∈ (blockSystem cfg).blocksOfSize 5)
    (hbp : p ∈ geometricBlockSupport cfg b)
    (hcp : p ∈ geometricBlockSupport cfg c) (hbc : b ≠ c)
    (hinter : (geometricBlockSupport cfg b ∩
      geometricBlockSupport cfg c).card = 1) :
    (blockSystem cfg).blockDegree 3 p = 9 ∧
      (blockSystem cfg).blockDegree 5 p = 2 := by
  let S := blockSystem cfg
  have htwo : 2 ≤ S.blockDegree 5 p :=
    two_le_blockDegree_five_of_two_blocks S p hb hc hbp hcp hbc
  have hfiveCap := (hlocal p).fiveDegreeCap
  change S.blockDegree 5 p ≤ 4 at hfiveCap
  rcases c39H28_threeDegree_six_or_nine S p (hlocal p) hC with hsix | hnine
  · have hfive : S.blockDegree 5 p = 2 ∨ S.blockDegree 5 p = 3 ∨
        S.blockDegree 5 p = 4 := by omega
    exfalso
    rcases hfive with htwo' | hthree | hfour
    · exact elevenFive_c40_singleton_impossible_of_common_profiles
        cfg hcard p (hlocal p) hb hc hbp hcp hbc hinter
          (Or.inl ⟨hsix, htwo'⟩)
    · exact elevenFive_c40_singleton_impossible_of_common_profiles
        cfg hcard p (hlocal p) hb hc hbp hcp hbc hinter
          (Or.inr (Or.inl ⟨hsix, hthree⟩))
    · exact elevenFive_c40_singleton_impossible_of_common_profiles
        cfg hcard p (hlocal p) hb hc hbp hcp hbc hinter
          (Or.inr (Or.inr hfour))
  · by_cases htwo' : S.blockDegree 5 p = 2
    · exact ⟨hnine, htwo'⟩
    have hthree : S.blockDegree 5 p = 3 ∨ S.blockDegree 5 p = 4 := by
      omega
    exfalso
    rcases hthree with hthree | hfour
    · exact elevenFive_threeFive_nine_singleton_impossible
        cfg hcard p (hlocal p) hnine hthree hb hc hbp hcp hbc hinter
    · exact elevenFive_c40_singleton_impossible_of_common_profiles
        cfg hcard p (hlocal p) hb hc hbp hcp hbc hinter
          (Or.inr (Or.inr hfour))

private theorem c39H28_hostTotal_le
    {Point : Type u} {Block : Type v} [Fintype Point] [Fintype Block]
    [DecidableEq Point]
    (S : BlockSystem Point Block) (hcard : Fintype.card Point = 11)
    (hcircle : ∀ b ∈ S.circleBlocksOfSize 5,
      elevenFiveHostWeight S (S.support b) ≤ 28) :
    elevenFiveFiveBlockHostTotal S ≤
      28 * S.blockCount 5 + 2 * S.lineCount 5 := by
  classical
  have hpoint (b : Block) (hb : b ∈ S.blocksOfSize 5) :
      elevenFiveHostWeight S (S.support b) ≤
        28 + 2 * (if S.kind b = .line then 1 else 0) := by
    have hsize := S.mem_blocksOfSize.mp hb
    cases hkind : S.kind b with
    | line =>
        have hthirty := elevenFiveHostWeight_le_thirty S (S.support b)
          hcard hsize
        simp [hkind]
        omega
    | circle =>
        have hmem : b ∈ S.circleBlocksOfSize 5 :=
          S.mem_blocksOfKindSize.mpr ⟨hkind, hsize⟩
        have htwentyEight := hcircle b hmem
        simp [hkind]
        omega
  have hsum := Finset.sum_le_sum fun b hb => hpoint b hb
  have hindicator :
      (∑ b ∈ S.blocksOfSize 5,
        if S.kind b = .line then 1 else 0) = S.lineCount 5 := by
    rw [← Finset.sum_filter]
    have hfilter : (S.blocksOfSize 5).filter
        (fun b => S.kind b = .line) = S.lineBlocksOfSize 5 := by
      ext b
      simp [BlockSystem.blocksOfSize, BlockSystem.blocksOfKindSize,
        BlockSystem.blocksOfKind, and_comm]
    rw [hfilter]
    simp [BlockSystem.lineCount]
  have hright :
      (∑ b ∈ S.blocksOfSize 5,
        (28 + 2 * (if S.kind b = .line then 1 else 0))) =
        28 * S.blockCount 5 + 2 * S.lineCount 5 := by
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, hindicator]
    simp [BlockSystem.blockCount, Nat.mul_comm]
  change (∑ b ∈ S.blocksOfSize 5,
    elevenFiveHostWeight S (S.support b)) ≤ _
  rw [hright] at hsum
  exact hsum

private theorem c39H28_twice_degree_le_choose_add_three (z : Nat)
    (hz : z ≤ 4) : 2 * z ≤ Nat.choose z 2 + 3 := by
  interval_cases z <;> norm_num [Nat.choose]

/-- The binomial incidence moment with the point sum restricted to a
finite subset. -/
private theorem c39H28_binomial_degree_moment_over
    {Point : Type u} {Block : Type v} [Fintype Point] [Fintype Block]
    [DecidableEq Point]
    (S : BlockSystem Point Block) (F : Finset Block)
    (D : Finset Point) (r : Nat) :
    (∑ p ∈ D, Nat.choose (S.degreeIn F p) r) =
      ∑ A ∈ F.powersetCard r, (D ∩ S.commonSupport A).card := by
  classical
  calc
    (∑ p ∈ D, Nat.choose (S.degreeIn F p) r) =
        ∑ p ∈ D,
          ((F.filter fun b => p ∈ S.support b).powersetCard r).card := by
      apply Finset.sum_congr rfl
      intro p hp
      simp [BlockSystem.degreeIn]
    _ = ∑ p ∈ D,
        (((F.powersetCard r).filter fun A =>
          ∀ b ∈ A, p ∈ S.support b).card) := by
      apply Finset.sum_congr rfl
      intro p hp
      apply congrArg Finset.card
      ext A
      simp only [Finset.mem_powersetCard, Finset.mem_filter]
      constructor
      · rintro ⟨hAF, hAcard⟩
        exact ⟨⟨fun b hb => (Finset.mem_filter.mp (hAF hb)).1, hAcard⟩,
          fun b hb => (Finset.mem_filter.mp (hAF hb)).2⟩
      · rintro ⟨⟨hAF, hAcard⟩, hpA⟩
        exact ⟨fun b hb => Finset.mem_filter.mpr ⟨hAF hb, hpA b hb⟩,
          hAcard⟩
    _ = ∑ p ∈ D, ∑ A ∈ F.powersetCard r,
        if (∀ b ∈ A, p ∈ S.support b) then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro p hp
      rw [Finset.card_eq_sum_ones, Finset.sum_filter]
    _ = ∑ A ∈ F.powersetCard r, ∑ p ∈ D,
        if (∀ b ∈ A, p ∈ S.support b) then 1 else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ A ∈ F.powersetCard r, (D ∩ S.commonSupport A).card := by
      apply Finset.sum_congr rfl
      intro A hA
      rw [Finset.card_eq_sum_ones]
      rw [← Finset.filter_mem_eq_inter, Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro p hp
      by_cases hall : ∀ b ∈ A, p ∈ S.support b <;>
        simp [hall, BlockSystem.mem_commonSupport]

/-- Count point pairs first, or count them inside each support. -/
private theorem c39H28_pairDegree_sum
    {Point : Type u} {Block : Type v} [DecidableEq Point]
    [DecidableEq Block]
    (F : Finset Block) (D : Finset Point) (support : Block → Finset Point) :
    (∑ A ∈ D.powersetCard 2,
        (F.filter fun b => A ⊆ support b).card) =
      ∑ b ∈ F, Nat.choose (D ∩ support b).card 2 := by
  classical
  calc
    (∑ A ∈ D.powersetCard 2,
        (F.filter fun b => A ⊆ support b).card) =
        ∑ A ∈ D.powersetCard 2, ∑ b ∈ F,
          if A ⊆ support b then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro A hA
      rw [Finset.card_eq_sum_ones, Finset.sum_filter]
    _ = ∑ b ∈ F, ∑ A ∈ D.powersetCard 2,
          if A ⊆ support b then 1 else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ b ∈ F, ((D ∩ support b).powersetCard 2).card := by
      apply Finset.sum_congr rfl
      intro b hb
      rw [Finset.card_eq_sum_ones]
      have hfilter :
          (D.powersetCard 2).filter (fun A => A ⊆ support b) =
            (D ∩ support b).powersetCard 2 := by
        ext A
        simp only [Finset.mem_filter, Finset.mem_powersetCard]
        constructor
        · rintro ⟨⟨hAD, hcard⟩, hAb⟩
          exact ⟨fun x hx => Finset.mem_inter.mpr ⟨hAD hx, hAb hx⟩, hcard⟩
        · rintro ⟨hAinter, hcard⟩
          exact ⟨⟨fun x hx => (Finset.mem_inter.mp (hAinter hx)).1, hcard⟩,
            fun x hx => (Finset.mem_inter.mp (hAinter hx)).2⟩
      rw [← Finset.sum_filter, hfilter]
    _ = ∑ b ∈ F, Nat.choose (D ∩ support b).card 2 := by
      apply Finset.sum_congr rfl
      intro b hb
      rw [Finset.card_powersetCard]

/-- The symmetric second Fubini count for point pairs and block pairs. -/
private theorem c39H28_pairDegree_second_sum
    {Point : Type u} {Block : Type v} [DecidableEq Point]
    [DecidableEq Block]
    (F : Finset Block) (D : Finset Point) (support : Block → Finset Point) :
    (∑ A ∈ D.powersetCard 2,
        Nat.choose ((F.filter fun b => A ⊆ support b).card) 2) =
      ∑ B ∈ F.powersetCard 2,
        Nat.choose
          ((D.filter fun p => ∀ b ∈ B, p ∈ support b).card) 2 := by
  classical
  calc
    (∑ A ∈ D.powersetCard 2,
        Nat.choose ((F.filter fun b => A ⊆ support b).card) 2) =
        ∑ A ∈ D.powersetCard 2,
          ((F.filter fun b => A ⊆ support b).powersetCard 2).card := by
      apply Finset.sum_congr rfl
      intro A hA
      rw [Finset.card_powersetCard]
    _ = ∑ A ∈ D.powersetCard 2, ∑ B ∈ F.powersetCard 2,
          if (∀ b ∈ B, A ⊆ support b) then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro A hA
      rw [BlockSystem.powersetCard_filter_eq]
      rw [Finset.card_eq_sum_ones, Finset.sum_filter]
    _ = ∑ B ∈ F.powersetCard 2, ∑ A ∈ D.powersetCard 2,
          if (∀ b ∈ B, A ⊆ support b) then 1 else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ B ∈ F.powersetCard 2,
          ((D.filter fun p => ∀ b ∈ B, p ∈ support b).powersetCard 2).card := by
      apply Finset.sum_congr rfl
      intro B hB
      rw [← Finset.sum_filter]
      rw [← Finset.card_eq_sum_ones]
      apply congrArg Finset.card
      ext A
      simp only [Finset.mem_filter, Finset.mem_powersetCard]
      constructor
      · rintro ⟨⟨hAD, hAcard⟩, hall⟩
        exact ⟨fun p hp => Finset.mem_filter.mpr
          ⟨hAD hp, fun b hb => hall b hb hp⟩, hAcard⟩
      · rintro ⟨hAfilter, hAcard⟩
        exact ⟨⟨fun p hp => (Finset.mem_filter.mp (hAfilter hp)).1,
          hAcard⟩, fun b hb p hp =>
            (Finset.mem_filter.mp (hAfilter hp)).2 b hb⟩
    _ = ∑ B ∈ F.powersetCard 2,
        Nat.choose
          ((D.filter fun p => ∀ b ∈ B, p ∈ support b).card) 2 := by
      apply Finset.sum_congr rfl
      intro B hB
      rw [Finset.card_powersetCard]

private theorem c39H28_pairDegree_second_sum_le_twelve
    {Point : Type u} {Block : Type v} [DecidableEq Point]
    [DecidableEq Block]
    (F : Finset Block) (L H : Finset Point) (support : Block → Finset Point)
    (hFcard : F.card = 6)
    (hhigh :
      (∑ B ∈ F.powersetCard 2,
        (H.filter fun p => ∀ b ∈ B, p ∈ support b).card) = 3)
    (hterm : ∀ B ∈ F.powersetCard 2,
      Nat.choose
          ((L.filter fun p => ∀ b ∈ B, p ∈ support b).card) 2 +
        (H.filter fun p => ∀ b ∈ B, p ∈ support b).card ≤ 1) :
    (∑ A ∈ L.powersetCard 2,
      Nat.choose ((F.filter fun b => A ⊆ support b).card) 2) ≤ 12 := by
  have hfubini := c39H28_pairDegree_second_sum F L support
  have hsumLe := Finset.sum_le_sum
    (s := F.powersetCard 2) fun B hB => hterm B hB
  have hpairFamilyCard : (F.powersetCard 2).card = 15 := by
    rw [Finset.card_powersetCard, hFcard]
    norm_num [Nat.choose]
  have hrightConst : (∑ _B ∈ F.powersetCard 2, 1) = 15 := by
    simp [hpairFamilyCard]
  rw [Finset.sum_add_distrib] at hsumLe
  rw [hhigh, hrightConst] at hsumLe
  rw [hfubini]
  omega

private theorem c39H28_zero_indicator_add_le_choose (n : Nat) (hn : n ≤ 3) :
    (if n = 0 then 1 else 0) + n ≤ 1 + Nat.choose n 2 := by
  interval_cases n <;> norm_num [Nat.choose]

private theorem c39H28_zero_pair_card_le_four
    {ι : Type u} [DecidableEq ι] (Q : Finset ι) (degree : ι → Nat)
    (hQcard : Q.card = 28)
    (hdegreeLe : ∀ A ∈ Q, degree A ≤ 3)
    (hdegreeSum : (∑ A ∈ Q, degree A) = 36)
    (hsecondSum : (∑ A ∈ Q, Nat.choose (degree A) 2) ≤ 12) :
    (Q.filter fun A => degree A = 0).card ≤ 4 := by
  have hzeroSum := Finset.sum_le_sum (s := Q) fun A hA =>
    c39H28_zero_indicator_add_le_choose (degree A) (hdegreeLe A hA)
  have hzeroIndicator :
      (∑ A ∈ Q, if degree A = 0 then 1 else 0) =
        (Q.filter fun A => degree A = 0).card := by
    rw [← Finset.sum_filter, ← Finset.card_eq_sum_ones]
  have hzeroLeft :
      (∑ A ∈ Q, ((if degree A = 0 then 1 else 0) + degree A)) =
        (Q.filter fun A => degree A = 0).card + 36 := by
    rw [Finset.sum_add_distrib, hzeroIndicator, hdegreeSum]
  have hzeroRight :
      (∑ A ∈ Q, (1 + Nat.choose (degree A) 2)) ≤ 40 := by
    rw [Finset.sum_add_distrib]
    have hones : (∑ _A ∈ Q, 1) = 28 := by simp [hQcard]
    rw [hones]
    omega
  rw [hzeroLeft] at hzeroSum
  omega

private theorem c39H28_pair_second_term
    {Point : Type u} {Block : Type v} [Fintype Point] [Fintype Block]
    [DecidableEq Point] [DecidableEq Block]
    (S : BlockSystem Point Block) (F : Finset Block) (L H : Finset Point)
    (hHLdisjoint : Disjoint H L)
    (hHLunion : H ∪ L = Finset.univ)
    (hblockHigh : ∀ b ∈ F, (H ∩ S.support b).card = 1)
    (B : Finset Block) (hB : B ∈ F.powersetCard 2) :
    Nat.choose
        ((L.filter fun p => ∀ b ∈ B, p ∈ S.support b).card) 2 +
      (H.filter fun p => ∀ b ∈ B, p ∈ S.support b).card ≤ 1 := by
  have hBcard := (Finset.mem_powersetCard.mp hB).2
  have hcommonLe := S.commonSupport_card_le_two hBcard
  have hLfilter :
      L.filter (fun p => ∀ b ∈ B, p ∈ S.support b) =
        L ∩ S.commonSupport B := by
    ext p
    simp
  have hHfilter :
      H.filter (fun p => ∀ b ∈ B, p ∈ S.support b) =
        H ∩ S.commonSupport B := by
    ext p
    simp
  rw [hLfilter, hHfilter]
  have hparts :
      (L ∩ S.commonSupport B).card + (H ∩ S.commonSupport B).card =
        (S.commonSupport B).card := by
    have hdis : Disjoint (L ∩ S.commonSupport B)
        (H ∩ S.commonSupport B) :=
      hHLdisjoint.symm.mono Finset.inter_subset_left Finset.inter_subset_left
    have hunion : (L ∩ S.commonSupport B) ∪ (H ∩ S.commonSupport B) =
        S.commonSupport B := by
      ext p
      have hpPartition : p ∈ H ∨ p ∈ L := by
        have : p ∈ H ∪ L := by rw [hHLunion]; simp
        simpa using this
      simp only [Finset.mem_union, Finset.mem_inter]
      constructor
      · rintro (⟨_hpL, hpB⟩ | ⟨_hpH, hpB⟩) <;> exact hpB
      · intro hpB
        rcases hpPartition with hpH | hpL
        · exact Or.inr ⟨hpH, hpB⟩
        · exact Or.inl ⟨hpL, hpB⟩
    have hc := Finset.card_union_of_disjoint hdis
    rw [hunion] at hc
    exact hc.symm
  have hHighLe : (H ∩ S.commonSupport B).card ≤ 1 := by
    obtain ⟨b, c, hbc, hBeq⟩ := Finset.card_eq_two.mp hBcard
    have hBsub := (Finset.mem_powersetCard.mp hB).1
    have hbF : b ∈ F := hBsub (by rw [hBeq]; simp)
    have hsub : H ∩ S.commonSupport B ⊆ H ∩ S.support b := by
      intro p hp
      have hp' := Finset.mem_inter.mp hp
      apply Finset.mem_inter.mpr
      refine ⟨hp'.1, ?_⟩
      exact (S.mem_commonSupport.mp hp'.2) b (by rw [hBeq]; simp)
    have hle := Finset.card_le_card hsub
    rw [hblockHigh b hbF] at hle
    exact hle
  have hLowLe : (L ∩ S.commonSupport B).card ≤ 2 := by omega
  have hLowCases : (L ∩ S.commonSupport B).card = 0 ∨
      (L ∩ S.commonSupport B).card = 1 ∨
        (L ∩ S.commonSupport B).card = 2 := by omega
  rcases hLowCases with hlow | hlow | hlow
  · simpa [hlow, Nat.choose] using hHighLe
  · simpa [hlow, Nat.choose] using hHighLe
  · have hHighZero : (H ∩ S.commonSupport B).card = 0 := by omega
    simp [hlow, hHighZero, Nat.choose]

private theorem c39H28_pair_tail_absurd
    {Point : Type u} {Block : Type v} [Fintype Point] [Fintype Block]
    [DecidableEq Point] [DecidableEq Block]
    (S : BlockSystem Point Block) (F : Finset Block) (L H : Finset Point)
    (hFcard : F.card = 6) (hLcard : L.card = 8) (hHcard : H.card = 3)
    (hHLdisjoint : Disjoint H L)
    (hHLunion : H ∪ L = Finset.univ)
    (hlowDegree : ∀ p ∈ L, S.degreeIn F p = 3)
    (hhighDegree : ∀ p ∈ H, S.degreeIn F p = 2)
    (hlowInBlock : ∀ b ∈ F, (L ∩ S.support b).card = 4)
    (hblockHigh : ∀ b ∈ F, (H ∩ S.support b).card = 1)
    (hzeroLower :
      12 ≤ ((L.powersetCard 2).filter
        (fun A => (F.filter fun b => A ⊆ S.support b).card = 0)).card) : False := by
  let degree : Finset Point → Nat := fun A =>
    (F.filter fun b => A ⊆ S.support b).card
  let Q : Finset (Finset Point) := L.powersetCard 2
  have hQcard : Q.card = 28 := by
    simp [Q, Finset.card_powersetCard, hLcard, Nat.choose]
  have hdegreeLe (A : Finset Point) (hA : A ∈ Q) : degree A ≤ 3 := by
    obtain ⟨x, y, hxy, hAeq⟩ :=
      Finset.card_eq_two.mp (Finset.mem_powersetCard.mp hA).2
    have hAsub := (Finset.mem_powersetCard.mp hA).1
    have hxL : x ∈ L := hAsub (by rw [hAeq]; simp)
    have hsub : (F.filter fun b => A ⊆ S.support b) ⊆
        F.filter fun b => x ∈ S.support b := by
      intro b hb
      have hb' := Finset.mem_filter.mp hb
      apply Finset.mem_filter.mpr
      refine ⟨hb'.1, hb'.2 ?_⟩
      rw [hAeq]
      simp
    have hle := Finset.card_le_card hsub
    change degree A ≤ _
    change degree A ≤ S.degreeIn F x at hle
    exact hle.trans_eq (hlowDegree x hxL)
  have hdegreeSum : (∑ A ∈ Q, degree A) = 36 := by
    have hsum := c39H28_pairDegree_sum F L S.support
    have hright :
        (∑ b ∈ F, Nat.choose (L ∩ S.support b).card 2) = 36 := by
      calc
        (∑ b ∈ F, Nat.choose (L ∩ S.support b).card 2) =
            ∑ _b ∈ F, 6 := by
          apply Finset.sum_congr rfl
          intro b hb
          rw [hlowInBlock b hb]
          norm_num [Nat.choose]
        _ = 36 := by simp [hFcard]
    simpa [Q, degree] using hsum.trans hright
  have hhighPairMoment :
      (∑ B ∈ F.powersetCard 2,
        (H.filter fun p => ∀ b ∈ B, p ∈ S.support b).card) = 3 := by
    have hmoment := c39H28_binomial_degree_moment_over S F H 2
    have hleft : (∑ p ∈ H, Nat.choose (S.degreeIn F p) 2) = 3 := by
      calc
        (∑ p ∈ H, Nat.choose (S.degreeIn F p) 2) = ∑ _p ∈ H, 1 := by
          apply Finset.sum_congr rfl
          intro p hp
          rw [hhighDegree p hp]
          norm_num [Nat.choose]
        _ = 3 := by simp [hHcard]
    have hfilterEq (B : Finset Block) :
        H.filter (fun p => ∀ b ∈ B, p ∈ S.support b) =
          H ∩ S.commonSupport B := by
      ext p
      simp
    simp_rw [hfilterEq]
    omega
  have hpairSecondTerm (B : Finset Block) (hB : B ∈ F.powersetCard 2) :
      Nat.choose
          ((L.filter fun p => ∀ b ∈ B, p ∈ S.support b).card) 2 +
        (H.filter fun p => ∀ b ∈ B, p ∈ S.support b).card ≤ 1 :=
    c39H28_pair_second_term S F L H hHLdisjoint hHLunion hblockHigh B hB
  have hsecondSum : (∑ A ∈ Q, Nat.choose (degree A) 2) ≤ 12 := by
    change
      (∑ A ∈ L.powersetCard 2,
        Nat.choose ((F.filter fun b => A ⊆ S.support b).card) 2) ≤ 12
    have hfubini :
        (∑ A ∈ L.powersetCard 2,
            Nat.choose ((F.filter fun b => A ⊆ S.support b).card) 2) =
          ∑ B ∈ F.powersetCard 2,
            Nat.choose
              ((L.filter fun p => ∀ b ∈ B, p ∈ S.support b).card) 2 := by
      calc
        (∑ A ∈ L.powersetCard 2,
            Nat.choose ((F.filter fun b => A ⊆ S.support b).card) 2) =
            ∑ A ∈ L.powersetCard 2,
              ((F.filter fun b => A ⊆ S.support b).powersetCard 2).card := by
          apply Finset.sum_congr rfl
          intro A hA
          rw [Finset.card_powersetCard]
        _ = ∑ A ∈ L.powersetCard 2, ∑ B ∈ F.powersetCard 2,
              if (∀ b ∈ B, A ⊆ S.support b) then 1 else 0 := by
          apply Finset.sum_congr rfl
          intro A hA
          rw [BlockSystem.powersetCard_filter_eq]
          rw [Finset.card_eq_sum_ones, Finset.sum_filter]
          apply Finset.sum_congr rfl
          intro B hB
          by_cases hall : ∀ b ∈ B, A ⊆ S.support b
          · simp [hall]
          · simp [hall]
        _ = ∑ B ∈ F.powersetCard 2, ∑ A ∈ L.powersetCard 2,
              if (∀ b ∈ B, A ⊆ S.support b) then 1 else 0 := by
          rw [Finset.sum_comm]
        _ = ∑ B ∈ F.powersetCard 2,
              ((L.filter fun p => ∀ b ∈ B,
                p ∈ S.support b).powersetCard 2).card := by
          apply Finset.sum_congr rfl
          intro B hB
          rw [← Finset.sum_filter]
          rw [← Finset.card_eq_sum_ones]
          apply congrArg Finset.card
          ext A
          simp only [Finset.mem_filter, Finset.mem_powersetCard]
          constructor
          · rintro ⟨⟨hAL, hAcard⟩, hall⟩
            exact ⟨fun p hp => Finset.mem_filter.mpr
              ⟨hAL hp, fun b hb => hall b hb hp⟩, hAcard⟩
          · rintro ⟨hAfilter, hAcard⟩
            exact ⟨⟨fun p hp => (Finset.mem_filter.mp (hAfilter hp)).1,
              hAcard⟩, fun b hb p hp =>
                (Finset.mem_filter.mp (hAfilter hp)).2 b hb⟩
        _ = ∑ B ∈ F.powersetCard 2,
            Nat.choose
              ((L.filter fun p => ∀ b ∈ B, p ∈ S.support b).card) 2 := by
          apply Finset.sum_congr rfl
          intro B hB
          rw [Finset.card_powersetCard]
    have hsumLe := Finset.sum_le_sum
      (s := F.powersetCard 2) fun B hB => hpairSecondTerm B hB
    have hpairFamilyCard : (F.powersetCard 2).card = 15 := by
      rw [Finset.card_powersetCard, hFcard]
      norm_num [Nat.choose]
    have hrightConst : (∑ _B ∈ F.powersetCard 2, 1) = 15 := by
      simp [hpairFamilyCard]
    rw [Finset.sum_add_distrib] at hsumLe
    rw [hhighPairMoment, hrightConst] at hsumLe
    have hrightLe :
        (∑ B ∈ F.powersetCard 2,
          Nat.choose
            ((L.filter fun p => ∀ b ∈ B, p ∈ S.support b).card) 2) ≤ 12 := by
      omega
    exact hfubini.le.trans hrightLe
  have hzeroUpper : (Q.filter fun A => degree A = 0).card ≤ 4 :=
    c39H28_zero_pair_card_le_four Q degree hQcard hdegreeLe hdegreeSum hsecondSum
  change 12 ≤ (Q.filter fun A => degree A = 0).card at hzeroLower
  omega

/-- The unconditional finite value of the singleton-graph field.  The two
function hypotheses are exactly the hypotheses exposed by the definition in
`ElevenFiveC39H28GraphTail`. -/
theorem elevenFive_c39_h28_singletonGraphDoubleCount
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    (cfg : Configuration Point) :
    ElevenFiveC39H28SingletonGraphDoubleCount cfg := by
  classical
  intro hpoint hcap hlocal hglobal hC hL hcircle hsingleton
  let S := blockSystem cfg
  let F := S.blocksOfSize 5
  change BlockSizeCap S 5 at hcap
  change (∀ p : Point, ElevenFiveLocalRows S p) at hlocal
  change ElevenFiveGlobalRows S at hglobal
  change S.totalCircleCount = 39 at hC
  change elevenFiveLineTotal S = 12 at hL
  change (∀ b ∈ S.circleBlocksOfSize 5,
    elevenFiveHostWeight S (S.support b) ≤ 28) at hcircle
  change (∀ b ∈ S.circleBlocksOfSize 5,
    ∃ c ∈ S.blocksOfSize 5, (S.support c ∩ S.support b).card = 1) at hsingleton

  have hhigh := elevenFive_c39_l12_high_count_row
    S hpoint hlocal hglobal hC hL
  have hlineCut := elevenFive_c39_l12_line_cut S hglobal hC hL
  have hlineMelchior := hglobal.lineMelchior
  rw [hL] at hlineMelchior
  have hlineFiveLe : S.lineCount 5 ≤ 1 := by omega
  have hhostUpper := c39H28_hostTotal_le S hpoint hcircle
  have hhostMoment := elevenFive_c39_l12_host_moment
    S hpoint hcap hlocal hglobal hC hL
  have hfiveLower : 5 ≤ S.blockCount 5 := by omega
  have hfiveUpper : S.blockCount 5 ≤ 6 := by omega
  have hlineFive : S.lineCount 5 = 0 := by omega
  have hfiveCases : S.blockCount 5 = 5 ∨ S.blockCount 5 = 6 := by omega

  have hFcard : F.card = S.blockCount 5 := rfl
  have hFcircle (b : GeometricBlock cfg) (hb : b ∈ F) :
      b ∈ S.circleBlocksOfSize 5 := by
    have hsize : (S.support b).card = 5 := S.mem_blocksOfSize.mp hb
    cases hkind : S.kind b with
    | circle => exact S.mem_blocksOfKindSize.mpr ⟨hkind, hsize⟩
    | line =>
        exfalso
        have hbline : b ∈ S.lineBlocksOfSize 5 :=
          S.mem_blocksOfKindSize.mpr ⟨hkind, hsize⟩
        have hpos : 0 < S.lineCount 5 := by
          change 0 < (S.lineBlocksOfSize 5).card
          exact Finset.card_pos.mpr ⟨b, hbline⟩
        omega

  let H : Finset Point :=
    (Finset.univ : Finset Point).filter fun p => S.blockDegree 3 p = 9
  have hHcard : H.card = elevenFiveC39HighCount S := by
    unfold elevenFiveC39HighCount elevenFiveC39HighIndicator
    rw [← Finset.sum_filter]
    change H.card = ∑ _p ∈ H, 1
    rw [Finset.card_eq_sum_ones]

  let C : Finset Point := H.filter fun p =>
    S.blockDegree 5 p = 2 ∧
      ∃ b ∈ F, ∃ c ∈ F, b ≠ c ∧
        p ∈ S.support b ∧ p ∈ S.support c ∧
          (S.support b ∩ S.support c).card = 1
  have hCsubH : C ⊆ H := Finset.filter_subset _ _

  have hcarrier (b : GeometricBlock cfg) (hb : b ∈ F) :
      ∃ p ∈ C, p ∈ S.support b := by
    obtain ⟨c, hc, hinterRev⟩ := hsingleton b (hFcircle b hb)
    have hbsize : (S.support b).card = 5 := S.mem_blocksOfSize.mp hb
    have hbc : b ≠ c := by
      intro hbc
      subst c
      rw [Finset.inter_self, hbsize] at hinterRev
      omega
    have hinter : (S.support b ∩ S.support c).card = 1 := by
      simpa [Finset.inter_comm] using hinterRev
    obtain ⟨p, hpEq⟩ := Finset.card_eq_one.mp hinter
    have hpinter : p ∈ S.support b ∩ S.support c := by
      rw [hpEq]
      simp
    have hprofile := c39H28_singleton_carrier_profile
      cfg hpoint p hlocal hC hb hc
        (Finset.mem_inter.mp hpinter).1 (Finset.mem_inter.mp hpinter).2
        hbc hinter
    change S.blockDegree 3 p = 9 ∧ S.blockDegree 5 p = 2 at hprofile
    have hpH : p ∈ H := by simp [H, hprofile.1]
    have hpC : p ∈ C := by
      apply Finset.mem_filter.mpr
      refine ⟨hpH, hprofile.2, b, hb, c, hc, hbc, ?_⟩
      exact ⟨(Finset.mem_inter.mp hpinter).1,
        (Finset.mem_inter.mp hpinter).2, hinter⟩
    exact ⟨p, hpC, (Finset.mem_inter.mp hpinter).1⟩

  rcases hfiveCases with hfive | hfive
  · have hHone : H.card = 1 := by omega
    have hFnonempty : F.Nonempty := by
      rw [← Finset.card_pos, hFcard, hfive]
      omega
    obtain ⟨b, hb⟩ := hFnonempty
    obtain ⟨p, hpC, hpb⟩ := hcarrier b hb
    have hpH : p ∈ H := hCsubH hpC
    have hsub : F ⊆ F.filter fun d => p ∈ S.support d := by
      intro d hd
      obtain ⟨q, hqC, hqd⟩ := hcarrier d hd
      have hqH : q ∈ H := hCsubH hqC
      have hqp := Finset.card_le_one.mp (by omega : H.card ≤ 1)
        p hpH q hqH
      subst q
      exact Finset.mem_filter.mpr ⟨hd, hqd⟩
    have hdegree : F.card ≤ S.blockDegree 5 p := by
      have hle := Finset.card_le_card hsub
      simpa [F, BlockSystem.blockDegree, BlockSystem.degreeIn] using hle
    have hpFive : S.blockDegree 5 p = 2 :=
      (Finset.mem_filter.mp hpC).2.1
    omega
  · have hFcardSix : F.card = 6 := by simpa [hFcard, hfive]
    have hHthree : H.card = 3 := by omega

    have hpositive (b : GeometricBlock cfg) (hb : b ∈ F) :
        1 ≤ (C ∩ S.support b).card := by
      obtain ⟨p, hpC, hpb⟩ := hcarrier b hb
      exact Finset.one_le_card.mpr ⟨p, Finset.mem_inter.mpr ⟨hpC, hpb⟩⟩
    have hCdegree (p : Point) (hp : p ∈ C) :
        S.degreeIn F p = 2 := by
      change S.blockDegree 5 p = 2
      exact (Finset.mem_filter.mp hp).2.1
    have hCcardLe : C.card ≤ 3 := by
      have := Finset.card_le_card hCsubH
      omega
    have hCincidence := S.sum_degreeIn_over F C
    have hCleft : (∑ p ∈ C, S.degreeIn F p) = 2 * C.card := by
      calc
        (∑ p ∈ C, S.degreeIn F p) = ∑ _p ∈ C, 2 := by
          apply Finset.sum_congr rfl
          intro p hp
          exact hCdegree p hp
        _ = 2 * C.card := by simp [Nat.mul_comm]
    have hCrightLower : F.card ≤ ∑ b ∈ F, (C ∩ S.support b).card := by
      calc
        F.card = ∑ _b ∈ F, 1 := by simp
        _ ≤ ∑ b ∈ F, (C ∩ S.support b).card := by
          apply Finset.sum_le_sum
          intro b hb
          exact hpositive b hb
    have hCcard : C.card = 3 := by
      rw [hCleft] at hCincidence
      omega
    have hCeqH : C = H :=
      Finset.eq_of_subset_of_card_le hCsubH (by omega)

    have hblockHigh (b : GeometricBlock cfg) (hb : b ∈ F) :
        (H ∩ S.support b).card = 1 := by
      have htermLe : ∀ d ∈ F, 1 ≤ (H ∩ S.support d).card := by
        intro d hd
        rw [← hCeqH]
        exact hpositive d hd
      have hsumHigh :
          (∑ d ∈ F, 1) = ∑ d ∈ F, (H ∩ S.support d).card := by
        have hfubini := S.sum_degreeIn_over F H
        have hleft : (∑ p ∈ H, S.degreeIn F p) = 6 := by
          rw [← hCeqH]
          rw [hCleft, hCcard]
        rw [hleft] at hfubini
        simpa [hFcardSix] using hfubini
      exact ((Finset.sum_eq_sum_iff_of_le htermLe).mp
        hsumHigh b hb).symm

    have hhighFive (p : Point) (hp : p ∈ H) :
        S.blockDegree 5 p = 2 := by
      rw [← hCeqH] at hp
      exact (Finset.mem_filter.mp hp).2.1

    have hhighPair (p : Point) (hp : p ∈ H)
        {b c : GeometricBlock cfg} (hb : b ∈ F) (hc : c ∈ F)
        (hpb : p ∈ S.support b) (hpc : p ∈ S.support c)
        (hbc : b ≠ c) : (S.support b ∩ S.support c).card = 1 := by
      have hpC : p ∈ C := by rw [hCeqH]; exact hp
      obtain ⟨b₀, hb₀, c₀, hc₀, hbc₀, hpb₀, hpc₀, hinter₀⟩ :=
        (Finset.mem_filter.mp hpC).2.2
      let I := F.filter fun d => p ∈ S.support d
      have hIcard : I.card = 2 := by
        change S.blockDegree 5 p = 2
        exact hhighFive p hp
      have hpair₀ : ({b₀, c₀} : Finset (GeometricBlock cfg)) = I := by
        apply Finset.eq_of_subset_of_card_le
        · intro d hd
          simp only [Finset.mem_insert, Finset.mem_singleton] at hd
          rcases hd with rfl | rfl
          · exact Finset.mem_filter.mpr ⟨hb₀, hpb₀⟩
          · exact Finset.mem_filter.mpr ⟨hc₀, hpc₀⟩
        · rw [hIcard]
          simp [hbc₀]
      have hbI : b ∈ I := Finset.mem_filter.mpr ⟨hb, hpb⟩
      have hcI : c ∈ I := Finset.mem_filter.mpr ⟨hc, hpc⟩
      rw [← hpair₀] at hbI hcI
      simp only [Finset.mem_insert, Finset.mem_singleton] at hbI hcI
      rcases hbI with rfl | rfl <;> rcases hcI with rfl | rfl
      · exact False.elim (hbc rfl)
      · exact hinter₀
      · simpa [Finset.inter_comm] using hinter₀
      · exact False.elim (hbc rfl)

    have hhighIncidence : elevenFiveC39HighFiveIncidence S = 6 := by
      calc
        elevenFiveC39HighFiveIncidence S =
            ∑ p : Point, if S.blockDegree 3 p = 9 then 2 else 0 := by
          unfold elevenFiveC39HighFiveIncidence elevenFiveC39HighIndicator
          apply Fintype.sum_congr
          intro p
          by_cases hp : S.blockDegree 3 p = 9
          · have hpH : p ∈ H := by simp [H, hp]
            simp [hp, hhighFive p hpH]
          · simp [hp]
        _ = ∑ _p ∈ H, 2 := by
          rw [← Finset.sum_filter]
        _ = 2 * H.card := by simp [Nat.mul_comm]
        _ = 6 := by rw [hHthree]

    have hdegreePoint (p : Point) :
        2 * S.blockDegree 5 p ≤
          Nat.choose (S.blockDegree 5 p) 2 + 3 :=
      c39H28_twice_degree_le_choose_add_three _ (hlocal p).fiveDegreeCap
    have hdegreeSum := Finset.sum_le_sum
      (s := (Finset.univ : Finset Point)) fun p _hp => hdegreePoint p
    have hfiveIncidence : (∑ p : Point, S.blockDegree 5 p) = 30 := by
      rw [hglobal.fiveIncidence, hfive]
    have hdegreeLeft :
        (∑ p : Point, 2 * S.blockDegree 5 p) = 60 := by
      rw [← Finset.mul_sum, hfiveIncidence]
      norm_num
    have hdegreeRight :
        (∑ p : Point, (Nat.choose (S.blockDegree 5 p) 2 + 3)) =
          elevenFiveSecondMoment S + 33 := by
      simp [elevenFiveSecondMoment, Finset.sum_add_distrib, hpoint]
    rw [hdegreeLeft, hdegreeRight] at hdegreeSum
    have hsecondLower : 27 ≤ elevenFiveSecondMoment S := by omega

    have hhostIdentity := elevenFive_c39_l12_host_moment_identity
      S hpoint hcap hlocal hglobal hC hL
    have hhostUpper' : elevenFiveFiveBlockHostTotal S ≤ 168 := by
      rw [hlineFive, hfive] at hhostUpper
      omega
    have hsecond : elevenFiveSecondMoment S = 27 := by omega
    have houtsideTotal : elevenFiveFiveBlockOutsideRichTotal S = 0 := by
      omega
    have hhostTotal : elevenFiveFiveBlockHostTotal S = 168 := by omega

    have hdegreeSumEq :
        (∑ p : Point, 2 * S.blockDegree 5 p) =
          ∑ p : Point, (Nat.choose (S.blockDegree 5 p) 2 + 3) := by
      rw [hdegreeLeft, hdegreeRight, hsecond]
    have hfiveProfile (p : Point) :
        S.blockDegree 5 p = 2 ∨ S.blockDegree 5 p = 3 := by
      have heq := (Finset.sum_eq_sum_iff_of_le
        (fun q (_hq : q ∈ (Finset.univ : Finset Point)) =>
          hdegreePoint q)).mp hdegreeSumEq p (Finset.mem_univ p)
      have hcap := (hlocal p).fiveDegreeCap
      interval_cases hz : S.blockDegree 5 p <;>
        norm_num [Nat.choose] at heq <;> omega

    let L : Finset Point := (Finset.univ : Finset Point) \ H
    have hHLdisjoint : Disjoint H L := by
      rw [Finset.disjoint_left]
      intro p hpH hpL
      exact (Finset.mem_sdiff.mp hpL).2 hpH
    have hHLunion : H ∪ L = (Finset.univ : Finset Point) := by
      ext p
      simp [L]
    have hLcard : L.card = 8 := by
      have hcardUnion := Finset.card_union_of_disjoint hHLdisjoint
      rw [hHLunion, Finset.card_univ, hpoint, hHthree] at hcardUnion
      omega
    have hlowNotHigh (p : Point) (hp : p ∈ L) :
        S.blockDegree 3 p ≠ 9 := by
      have hpnot : p ∉ H := (Finset.mem_sdiff.mp hp).2
      simpa [H] using hpnot
    have hlowThreeDegree (p : Point) (hp : p ∈ L) :
        S.blockDegree 3 p = 6 := by
      rcases c39H28_threeDegree_six_or_nine S p (hlocal p) hC with h | h
      · exact h
      · exact False.elim (hlowNotHigh p hp h)
    have hsumHighDegree : (∑ p ∈ H, S.blockDegree 5 p) = 6 := by
      calc
        (∑ p ∈ H, S.blockDegree 5 p) = ∑ _p ∈ H, 2 := by
          apply Finset.sum_congr rfl
          intro p hp
          exact hhighFive p hp
        _ = 6 := by simp [hHthree]
    have hdegreePartition := Finset.sum_union hHLdisjoint
      (f := fun p => S.blockDegree 5 p)
    rw [hHLunion] at hdegreePartition
    have hsumLowDegree : (∑ p ∈ L, S.blockDegree 5 p) = 24 := by
      have huniv : (∑ p ∈ (Finset.univ : Finset Point),
          S.blockDegree 5 p) = 30 := by simpa using hfiveIncidence
      have hpart :
          30 = 6 + ∑ p ∈ L, S.blockDegree 5 p := by
        calc
          30 = ∑ p ∈ (Finset.univ : Finset Point),
              S.blockDegree 5 p := huniv.symm
          _ = (∑ p ∈ H, S.blockDegree 5 p) +
                ∑ p ∈ L, S.blockDegree 5 p := hdegreePartition
          _ = 6 + ∑ p ∈ L, S.blockDegree 5 p := by
            rw [hsumHighDegree]
      omega
    have hlowFive (p : Point) (hp : p ∈ L) :
        S.blockDegree 5 p = 3 := by
      have hle : ∀ q ∈ L, S.blockDegree 5 q ≤ 3 := by
        intro q hq
        rcases hfiveProfile q with hq2 | hq3 <;> omega
      have hsumConst :
          (∑ q ∈ L, S.blockDegree 5 q) = ∑ _q ∈ L, 3 := by
        rw [hsumLowDegree]
        simp [hLcard]
      exact (Finset.sum_eq_sum_iff_of_le hle).mp hsumConst p hp

    have hhighFour (p : Point) (hp : p ∈ H) :
        S.blockDegree 4 p = 8 := by
      have hpair := (hlocal p).pairRow
      have hthree : S.blockDegree 3 p = 9 := (Finset.mem_filter.mp hp).2
      have hfivep := hhighFive p hp
      omega
    have hlowFour (p : Point) (hp : p ∈ L) :
        S.blockDegree 4 p = 7 := by
      have hpair := (hlocal p).pairRow
      have hthree := hlowThreeDegree p hp
      have hfivep := hlowFive p hp
      omega

    have houtsidePoint (b : GeometricBlock cfg) (hb : b ∈ F) :
        elevenFiveOutsideRichWeight S (S.support b) = 0 := by
      unfold elevenFiveFiveBlockOutsideRichTotal at houtsideTotal
      have hall := (Finset.sum_eq_zero_iff_of_nonneg
        (fun _ _ => Nat.zero_le _)).mp houtsideTotal
      exact hall b hb
    have hmeets (d : GeometricBlock cfg) (hd : d ∈ S.blocksOfSize 4)
        (b : GeometricBlock cfg) (hb : b ∈ F) :
        1 ≤ (S.support d ∩ S.support b).card := by
      by_contra hnot
      have hinter : (S.support d ∩ S.support b).card = 0 := by omega
      have hdmem : d ∈ (S.blocksOfSize 4).filter fun c =>
          (S.support c ∩ S.support b).card = 0 :=
        Finset.mem_filter.mpr ⟨hd, hinter⟩
      have hpos : 0 < ((S.blocksOfSize 4).filter fun c =>
          (S.support c ∩ S.support b).card = 0).card :=
        Finset.card_pos.mpr ⟨d, hdmem⟩
      have hzero := houtsidePoint b hb
      unfold elevenFiveOutsideRichWeight at hzero
      omega

    have hcodegreeOne (p : Point) (hp : p ∈ H)
        (x : Point) (hx : x ∈ L) :
        S.degreeIn (F.filter fun b => x ∈ S.support b) p = 1 := by
      let Fx := F.filter fun b => x ∈ S.support b
      have hpx : p ≠ x := by
        intro h
        subst x
        exact (Finset.mem_sdiff.mp hx).2 hp
      have htermLe : ∀ q ∈ H, S.degreeIn Fx q ≤ 1 := by
        intro q hq
        unfold BlockSystem.degreeIn
        apply Finset.card_le_one_iff.mpr
        intro b c hb hc
        have hb' := Finset.mem_filter.mp hb
        have hc' := Finset.mem_filter.mp hc
        have hbFx := Finset.mem_filter.mp hb'.1
        have hcFx := Finset.mem_filter.mp hc'.1
        by_contra hbc
        have hinter := hhighPair q hq hbFx.1 hcFx.1 hb'.2 hc'.2 hbc
        have hqx : q ≠ x := by
          intro h
          subst x
          exact (Finset.mem_sdiff.mp hx).2 hq
        have hpairCard : ({q, x} : Finset Point).card = 2 := by simp [hqx]
        have hsub : ({q, x} : Finset Point) ⊆
            S.support b ∩ S.support c := by
          intro y hy
          simp only [Finset.mem_insert, Finset.mem_singleton] at hy
          rcases hy with rfl | rfl
          · exact Finset.mem_inter.mpr ⟨hb'.2, hc'.2⟩
          · exact Finset.mem_inter.mpr ⟨hbFx.2, hcFx.2⟩
        have hle := Finset.card_le_card hsub
        rw [hpairCard, hinter] at hle
        omega
      have hfubini := S.sum_degreeIn_over Fx H
      have hright :
          (∑ b ∈ Fx, (H ∩ S.support b).card) = Fx.card := by
        calc
          (∑ b ∈ Fx, (H ∩ S.support b).card) = ∑ _b ∈ Fx, 1 := by
            apply Finset.sum_congr rfl
            intro b hb
            exact hblockHigh b (Finset.mem_filter.mp hb).1
          _ = Fx.card := by simp
      have hFxcard : Fx.card = 3 := by
        change S.blockDegree 5 x = 3
        exact hlowFive x hx
      have hsum :
          (∑ q ∈ H, S.degreeIn Fx q) = ∑ _q ∈ H, 1 := by
        rw [hfubini, hright, hFxcard]
        simp [hHthree]
      exact (Finset.sum_eq_sum_iff_of_le htermLe).mp hsum p hp

    let G := S.blocksOfSize 4
    have hhighFourIncidence :
        (∑ d ∈ G, (H ∩ S.support d).card) = 24 := by
      have hfubini := S.sum_degreeIn_over G H
      have hleft : (∑ p ∈ H, S.degreeIn G p) = 24 := by
        calc
          (∑ p ∈ H, S.degreeIn G p) = ∑ _p ∈ H, 8 := by
            apply Finset.sum_congr rfl
            intro p hp
            change S.blockDegree 4 p = 8
            exact hhighFour p hp
          _ = 24 := by simp [hHthree]
      omega

    have hhighCardLe (d : GeometricBlock cfg) (hd : d ∈ G) :
        (H ∩ S.support d).card ≤ 3 := by
      have hsub : H ∩ S.support d ⊆ H := Finset.inter_subset_left
      have := Finset.card_le_card hsub
      omega

    have hhighCardNeOne (d : GeometricBlock cfg) (hd : d ∈ G) :
        (H ∩ S.support d).card ≠ 1 := by
      intro hone
      obtain ⟨p, hpEq⟩ := Finset.card_eq_one.mp hone
      have hpHD : p ∈ H ∩ S.support d := by rw [hpEq]; simp
      have hpH := (Finset.mem_inter.mp hpHD).1
      have hpD := (Finset.mem_inter.mp hpHD).2
      let X := S.support d \ {p}
      have hDcard : (S.support d).card = 4 := S.mem_blocksOfSize.mp hd
      have hXcard : X.card = 3 := by
        have hpSub : ({p} : Finset Point) ⊆ S.support d := by
          simpa using hpD
        change (S.support d \ {p}).card = 3
        rw [Finset.card_sdiff_of_subset hpSub, hDcard]
        simp
      have hXlow (x : Point) (hx : x ∈ X) : x ∈ L := by
        have hxD : x ∈ S.support d := (Finset.mem_sdiff.mp hx).1
        have hxp : x ≠ p := by simpa using (Finset.mem_sdiff.mp hx).2
        have hxnotH : x ∉ H := by
          intro hxH
          have hxInter : x ∈ H ∩ S.support d :=
            Finset.mem_inter.mpr ⟨hxH, hxD⟩
          rw [hpEq] at hxInter
          simpa [hxp] using hxInter
        exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ x, hxnotH⟩
      let I := F.filter fun b => p ∈ S.support b
      have hIcard : I.card = 2 := by
        change S.blockDegree 5 p = 2
        exact hhighFive p hpH
      have hleft : (∑ x ∈ X, S.degreeIn I x) = 3 := by
        calc
          (∑ x ∈ X, S.degreeIn I x) = ∑ _x ∈ X, 1 := by
            apply Finset.sum_congr rfl
            intro x hx
            simpa [I, BlockSystem.degreeIn, Finset.filter_filter,
              and_comm, and_left_comm, and_assoc] using
              hcodegreeOne p hpH x (hXlow x hx)
          _ = 3 := by simp [hXcard]
      have hfubini := S.sum_degreeIn_over I X
      have hrightLe : (∑ b ∈ I, (X ∩ S.support b).card) ≤ 2 := by
        calc
          (∑ b ∈ I, (X ∩ S.support b).card) ≤ ∑ _b ∈ I, 1 := by
            apply Finset.sum_le_sum
            intro b hb
            have hbF := (Finset.mem_filter.mp hb).1
            have hpb := (Finset.mem_filter.mp hb).2
            have hbd : b ≠ d := by
              intro hbd
              subst b
              have hbcard : (S.support d).card = 5 := S.mem_blocksOfSize.mp hbF
              omega
            have hinterLt := S.distinct_block_inter_card_lt_three hbd.symm
            have hsub : insert p (X ∩ S.support b) ⊆
                S.support d ∩ S.support b := by
              intro y hy
              simp only [Finset.mem_insert] at hy
              rcases hy with rfl | hy
              · exact Finset.mem_inter.mpr ⟨hpD, hpb⟩
              · have hy' := Finset.mem_inter.mp hy
                exact Finset.mem_inter.mpr
                  ⟨(Finset.mem_sdiff.mp hy'.1).1, hy'.2⟩
            have hpnot : p ∉ X ∩ S.support b := by
              intro hp
              exact (Finset.mem_sdiff.mp (Finset.mem_inter.mp hp).1).2 (by simp)
            have hcardInsert : (insert p (X ∩ S.support b)).card =
                (X ∩ S.support b).card + 1 := by simp [hpnot]
            have hle := Finset.card_le_card hsub
            rw [hcardInsert] at hle
            omega
          _ = 2 := by simp [hIcard]
      omega

    let G2 := G.filter fun d => (H ∩ S.support d).card = 2
    let G3 := G.filter fun d => (H ∩ S.support d).card = 3
    have hG3card : G3.card ≤ 1 := by
      apply Finset.card_le_one_iff.mpr
      intro d e hd he
      have hd' := Finset.mem_filter.mp hd
      have he' := Finset.mem_filter.mp he
      by_contra hde
      have hHsubD : H ⊆ S.support d := by
        have heq : H ∩ S.support d = H :=
          Finset.eq_of_subset_of_card_le Finset.inter_subset_left (by
            rw [hd'.2, hHthree])
        intro p hp
        have : p ∈ H ∩ S.support d := by rw [heq]; exact hp
        exact (Finset.mem_inter.mp this).2
      have hHsubE : H ⊆ S.support e := by
        have heq : H ∩ S.support e = H :=
          Finset.eq_of_subset_of_card_le Finset.inter_subset_left (by
            rw [he'.2, hHthree])
        intro p hp
        have : p ∈ H ∩ S.support e := by rw [heq]; exact hp
        exact (Finset.mem_inter.mp this).2
      have hsub : H ⊆ S.support d ∩ S.support e := fun p hp =>
        Finset.mem_inter.mpr ⟨hHsubD hp, hHsubE hp⟩
      have hle := Finset.card_le_card hsub
      have hlt := S.distinct_block_inter_card_lt_three hde
      omega
    have hhighCardCases (d : GeometricBlock cfg) (hd : d ∈ G) :
        (H ∩ S.support d).card = 0 ∨
          (H ∩ S.support d).card = 2 ∨
            (H ∩ S.support d).card = 3 := by
      have hle := hhighCardLe d hd
      have hne := hhighCardNeOne d hd
      omega
    have hrewrite (d : GeometricBlock cfg) (hd : d ∈ G) :
        (H ∩ S.support d).card =
          2 * (if (H ∩ S.support d).card = 2 then 1 else 0) +
            3 * (if (H ∩ S.support d).card = 3 then 1 else 0) := by
      rcases hhighCardCases d hd with hzero | htwo | hthree
      · simp [hzero]
      · simp [htwo]
      · simp [hthree]
    have hG23 : 2 * G2.card + 3 * G3.card = 24 := by
      have hsum := hhighFourIncidence
      have hG2indicator :
          (∑ d ∈ G, if (H ∩ S.support d).card = 2 then 1 else 0) =
            G2.card := by
        rw [← Finset.sum_filter]
        simp [G2]
      have hG3indicator :
          (∑ d ∈ G, if (H ∩ S.support d).card = 3 then 1 else 0) =
            G3.card := by
        rw [← Finset.sum_filter]
        simp [G3]
      calc
        2 * G2.card + 3 * G3.card =
            (∑ d ∈ G,
              (2 * (if (H ∩ S.support d).card = 2 then 1 else 0) +
                3 * (if (H ∩ S.support d).card = 3 then 1 else 0))) := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum,
            ← Finset.mul_sum, hG2indicator, hG3indicator]
        _ = ∑ d ∈ G, (H ∩ S.support d).card := by
          apply Finset.sum_congr rfl
          intro d hd
          exact (hrewrite d hd).symm
        _ = 24 := hsum
    have hG3zero : G3.card = 0 := by omega
    have hG2card : G2.card = 12 := by omega

    have hsupportPartitionCard (d : GeometricBlock cfg) :
        (H ∩ S.support d).card + (L ∩ S.support d).card =
          (S.support d).card := by
      have hdis : Disjoint (H ∩ S.support d) (L ∩ S.support d) :=
        hHLdisjoint.mono Finset.inter_subset_left Finset.inter_subset_left
      have hunion : (H ∩ S.support d) ∪ (L ∩ S.support d) =
          S.support d := by
        ext p
        have hpPartition : p ∈ H ∨ p ∈ L := by
          have : p ∈ H ∪ L := by rw [hHLunion]; simp
          simpa using this
        simp only [Finset.mem_union, Finset.mem_inter]
        constructor
        · rintro (⟨_hpH, hpD⟩ | ⟨_hpL, hpD⟩) <;> exact hpD
        · intro hpD
          rcases hpPartition with hpH | hpL
          · exact Or.inl ⟨hpH, hpD⟩
          · exact Or.inr ⟨hpL, hpD⟩
      have hcardUnion := Finset.card_union_of_disjoint hdis
      rw [hunion] at hcardUnion
      exact hcardUnion.symm

    let pairDegree : Finset Point → Nat := fun A =>
      (F.filter fun b => A ⊆ S.support b).card
    let Q : Finset (Finset Point) := L.powersetCard 2
    let Z : Finset (Finset Point) := Q.filter fun A => pairDegree A = 0

    have hlowPairCard (d : GeometricBlock cfg) (hd : d ∈ G2) :
        (L ∩ S.support d).card = 2 := by
      have hd' := Finset.mem_filter.mp hd
      have hDcard : (S.support d).card = 4 := S.mem_blocksOfSize.mp hd'.1
      have hpartition := hsupportPartitionCard d
      omega

    have hlowPairZero (d : GeometricBlock cfg) (hd : d ∈ G2) :
        pairDegree (L ∩ S.support d) = 0 := by
      have hd' := Finset.mem_filter.mp hd
      have hAcard := hlowPairCard d hd
      by_contra hne
      have hpos : 0 < pairDegree (L ∩ S.support d) := by omega
      obtain ⟨b, hbfilter⟩ := Finset.card_pos.mp hpos
      have hbdata := Finset.mem_filter.mp hbfilter
      have hbF : b ∈ F := hbdata.1
      have hAb : L ∩ S.support d ⊆ S.support b := hbdata.2
      obtain ⟨r, hrEq⟩ := Finset.card_eq_one.mp (hblockHigh b hbF)
      have hrHb : r ∈ H ∩ S.support b := by rw [hrEq]; simp
      have hrH := (Finset.mem_inter.mp hrHb).1
      have hrb := (Finset.mem_inter.mp hrHb).2
      by_cases hrd : r ∈ S.support d
      · have hrnotA : r ∉ L ∩ S.support d := by
          intro hrA
          exact (Finset.mem_sdiff.mp (Finset.mem_inter.mp hrA).1).2 hrH
        have hsub : insert r (L ∩ S.support d) ⊆
            S.support d ∩ S.support b := by
          intro x hx
          simp only [Finset.mem_insert] at hx
          rcases hx with rfl | hx
          · exact Finset.mem_inter.mpr ⟨hrd, hrb⟩
          · exact Finset.mem_inter.mpr
              ⟨(Finset.mem_inter.mp hx).2, hAb hx⟩
        have hcardInsert : (insert r (L ∩ S.support d)).card = 3 := by
          simp [hrnotA, hAcard]
        have hle := Finset.card_le_card hsub
        have hbd : b ≠ d := by
          intro hbd
          subst b
          have hbcard : (S.support d).card = 5 := S.mem_blocksOfSize.mp hbF
          have hdcard : (S.support d).card = 4 := S.mem_blocksOfSize.mp hd'.1
          omega
        have hlt : (S.support d ∩ S.support b).card < 3 := by
          simpa [Finset.inter_comm] using
            S.distinct_block_inter_card_lt_three hbd
        omega
      · let I := F.filter fun c => r ∈ S.support c
        have hIcard : I.card = 2 := by
          change S.blockDegree 5 r = 2
          exact hhighFive r hrH
        have hbI : b ∈ I := Finset.mem_filter.mpr ⟨hbF, hrb⟩
        have hex : ∃ c ∈ I, c ≠ b := by
          by_contra hnot
          push_neg at hnot
          have hsub : I ⊆ {b} := by
            intro c hc
            have hcb : c = b := hnot c hc
            simpa [hcb]
          have hle := Finset.card_le_card hsub
          rw [hIcard] at hle
          simp at hle
        obtain ⟨c, hcI, hcb⟩ := hex
        have hcdata := Finset.mem_filter.mp hcI
        have hcF := hcdata.1
        have hrc := hcdata.2
        have hinterBC := hhighPair r hrH hbF hcF hrb hrc hcb.symm
        have hhighC : H ∩ S.support c = {r} := by
          have hcard := hblockHigh c hcF
          symm
          apply Finset.eq_of_subset_of_card_le
          · intro x hx
            simp only [Finset.mem_singleton] at hx
            subst x
            exact Finset.mem_inter.mpr ⟨hrH, hrc⟩
          · simp [hcard]
        have hdisjoint : (S.support d ∩ S.support c).card = 0 := by
          apply Finset.card_eq_zero.mpr
          apply Finset.eq_empty_iff_forall_notMem.mpr
          intro x hx
          have hxd := (Finset.mem_inter.mp hx).1
          have hxc := (Finset.mem_inter.mp hx).2
          by_cases hxH : x ∈ H
          · have : x ∈ H ∩ S.support c := Finset.mem_inter.mpr ⟨hxH, hxc⟩
            rw [hhighC] at this
            have hxr : x = r := by simpa using this
            exact hrd (hxr ▸ hxd)
          · have hxL : x ∈ L :=
              Finset.mem_sdiff.mpr ⟨Finset.mem_univ x, hxH⟩
            have hxA : x ∈ L ∩ S.support d :=
              Finset.mem_inter.mpr ⟨hxL, hxd⟩
            have hxb := hAb hxA
            have hrx : r ≠ x := by
              intro h
              subst x
              exact hxH hrH
            have hpairCard : ({r, x} : Finset Point).card = 2 := by
              simp [hrx]
            have hsub : ({r, x} : Finset Point) ⊆
                S.support b ∩ S.support c := by
              intro y hy
              simp only [Finset.mem_insert, Finset.mem_singleton] at hy
              rcases hy with rfl | rfl
              · exact Finset.mem_inter.mpr ⟨hrb, hrc⟩
              · exact Finset.mem_inter.mpr ⟨hxb, hxc⟩
            have hle := Finset.card_le_card hsub
            rw [hpairCard, hinterBC] at hle
            omega
        have hmeet := hmeets d hd'.1 c hcF
        omega

    let lowPairMap : ↥G2 → ↥Z := fun d => by
      refine ⟨L ∩ S.support d.1, ?_⟩
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_powersetCard.mpr ⟨Finset.inter_subset_left,
        hlowPairCard d.1 d.2⟩, ?_⟩
      exact hlowPairZero d.1 d.2
    have hlowPairMapInj : Function.Injective lowPairMap := by
      intro d e heq
      apply Subtype.ext
      by_contra hde
      have hAeq : L ∩ S.support d.1 = L ∩ S.support e.1 :=
        congrArg Subtype.val heq
      have hdData := Finset.mem_filter.mp d.2
      have heData := Finset.mem_filter.mp e.2
      let HD := H ∩ S.support d.1
      let HE := H ∩ S.support e.1
      have hHDcard : HD.card = 2 := hdData.2
      have hHEcard : HE.card = 2 := heData.2
      have hunionSub : HD ∪ HE ⊆ H := by
        intro p hp
        rcases Finset.mem_union.mp hp with hp | hp
        · exact (Finset.mem_inter.mp hp).1
        · exact (Finset.mem_inter.mp hp).1
      have hunionLe : (HD ∪ HE).card ≤ 3 := by
        have := Finset.card_le_card hunionSub
        omega
      have hcardFormula := Finset.card_union_add_card_inter HD HE
      have hinterPos : 0 < (HD ∩ HE).card := by omega
      obtain ⟨p, hpInter⟩ := Finset.card_pos.mp hinterPos
      have hpHD := (Finset.mem_inter.mp hpInter).1
      have hpHE := (Finset.mem_inter.mp hpInter).2
      have hpH := (Finset.mem_inter.mp hpHD).1
      have hpd := (Finset.mem_inter.mp hpHD).2
      have hpe := (Finset.mem_inter.mp hpHE).2
      let A := L ∩ S.support d.1
      have hAcard : A.card = 2 := hlowPairCard d.1 d.2
      have hpnotA : p ∉ A := by
        intro hpA
        exact (Finset.mem_sdiff.mp (Finset.mem_inter.mp hpA).1).2 hpH
      have hsub : insert p A ⊆ S.support d.1 ∩ S.support e.1 := by
        intro x hx
        simp only [Finset.mem_insert] at hx
        rcases hx with rfl | hx
        · exact Finset.mem_inter.mpr ⟨hpd, hpe⟩
        · have hxd := (Finset.mem_inter.mp hx).2
          have hxe : x ∈ S.support e.1 := by
            have : x ∈ L ∩ S.support e.1 := by rw [← hAeq]; exact hx
            exact (Finset.mem_inter.mp this).2
          exact Finset.mem_inter.mpr ⟨hxd, hxe⟩
      have hinsertCard : (insert p A).card = 3 := by simp [hpnotA, hAcard]
      have hle := Finset.card_le_card hsub
      have hlt := S.distinct_block_inter_card_lt_three hde
      omega
    have hG2leZ : G2.card ≤ Z.card := by
      have hle := Fintype.card_le_of_injective lowPairMap hlowPairMapInj
      simpa only [Fintype.card_coe] using hle

    have hlowInBlock (b : GeometricBlock cfg) (hb : b ∈ F) :
        (L ∩ S.support b).card = 4 := by
      have hpartition := hsupportPartitionCard b
      have hhigh := hblockHigh b hb
      have hsize : (S.support b).card = 5 := S.mem_blocksOfSize.mp hb
      omega
    have hlowDegree (p : Point) (hp : p ∈ L) : S.degreeIn F p = 3 := by
      change S.blockDegree 5 p = 3
      exact hlowFive p hp
    have hhighDegree (p : Point) (hp : p ∈ H) : S.degreeIn F p = 2 := by
      change S.blockDegree 5 p = 2
      exact hhighFive p hp
    have hzeroLower : 12 ≤ Z.card := by omega
    change
      12 ≤ ((L.powersetCard 2).filter
        (fun A => (F.filter fun b => A ⊆ S.support b).card = 0)).card at hzeroLower
    exact c39H28_pair_tail_absurd S F L H hFcardSix hLcard hHthree
      hHLdisjoint hHLunion hlowDegree hhighDegree hlowInBlock hblockHigh
      hzeroLower

end Erdos506.V1
