import Erdos506.V1.ElevenFiveC39MaximumHostRouter

/-!
# The singleton front of the C39 maximum-host residual

This module isolates the finite entrance to the last `C = 39`, `L = 12`
face.  The existing maximum-host router already proves that the `H <= 27`
face has five size-five blocks, no five-line, and one high point.  What is
not yet present in the abstract `BlockSystem` API is the rebased C39 front:
under absence of a singleton neighbour it supplies the two signed equations
for `A12` and `eX` below.  Once those equations are available, their
arithmetic contradiction and the conversion from a positive relative census
to an actual singleton block are completely finite.
-/

namespace Erdos506.V1

open Erdos506.Block
open Erdos506.Block.BlockSystem
open scoped BigOperators

universe u v

/-- The arithmetic core of the no-singleton branch of the C39 front.  This
is the paper's contradiction from
`A12 = 3q - R`, `eX = 3 - R - q + 2y`, `R >= 3`, and the rich-block cap.
The two displayed front rows are deliberately stated in `Int`, since their
right sides are signed quantities. -/
theorem elevenFive_c39_noSingleton_front_arithmetic_absurd
    (R q y A12 eX : Nat)
    (hR : 3 <= R) (hq : q <= 3) (hy : y <= 1)
    (hyRich : y = 1 -> q = 3)
    (hA12 : (A12 : Int) = 3 * (q : Int) - (R : Int))
    (heX : (eX : Int) = 3 - (R : Int) - (q : Int) + 2 * (y : Int)) :
    False := by
  interval_cases hy' : y <;> simp [hy'] at hyRich heX <;> omega

/-- A positive `A14` relative census is exactly an actual size-five block
having singleton intersection with the selected set. -/
theorem elevenFive_relativeCount_one_four_pos_iff_exists_sizeFive_singleton
    {Point : Type u} {Block : Type v} [Fintype Point] [Fintype Block]
    [DecidableEq Point]
    (S : BlockSystem Point Block) (D : Finset Point) :
    0 < elevenFiveRelativeCount S D 1 4 ↔
      ∃ c, c ∈ S.blocksOfSize 5 /\
        (S.support c ∩ D).card = 1 := by
  classical
  constructor
  · intro hpos
    rw [elevenFiveRelativeCount] at hpos
    obtain ⟨c, hc⟩ := Finset.card_pos.mp hpos
    have hspec := Finset.mem_filter.mp hc
    rcases hspec with ⟨_, hinter, houtside⟩
    refine ⟨c, S.mem_blocksOfSize.mpr ?_, hinter⟩
    have hsplit := Finset.card_inter_add_card_sdiff (S.support c) D
    omega
  · rintro ⟨c, hc, hinter⟩
    rw [elevenFiveRelativeCount]
    apply Finset.card_pos.mpr
    refine ⟨c, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hinter, ?_⟩⟩
    have hsize := S.mem_blocksOfSize.mp hc
    have hsplit := Finset.card_inter_add_card_sdiff (S.support c) D
    omega

/-- If the selected `D` is a size-five block, absence of singleton
neighbours is the vanishing of the `A14` relative census. -/
theorem elevenFive_relativeCount_one_four_eq_zero_of_no_sizeFive_singleton
    {Point : Type u} {Block : Type v} [Fintype Point] [Fintype Block]
    [DecidableEq Point]
    (S : BlockSystem Point Block) (D : Finset Point)
    (hno : ¬ (∃ c, c ∈ S.blocksOfSize 5 /\
      (S.support c ∩ D).card = 1)) :
    elevenFiveRelativeCount S D 1 4 = 0 := by
  classical
  by_contra hne
  have hpos : 0 < elevenFiveRelativeCount S D 1 4 := by omega
  exact hno ((elevenFive_relativeCount_one_four_pos_iff_exists_sizeFive_singleton
    S D).mp hpos)

/-! ## Relative triple rows at a selected five-block -/

/-- Summing a constant over an untagged relative fibre evaluates to its
materialized relative count. -/
theorem elevenFive_sum_relative_indicator
    {Point : Type u} {Block : Type v} [Fintype Point] [Fintype Block]
    [DecidableEq Point]
    (S : BlockSystem Point Block) (D : Finset Point) (g x a : Nat) :
    (∑ b : Block,
      if (S.support b ∩ D).card = g /\ (S.support b \ D).card = x
      then a else 0) = a * elevenFiveRelativeCount S D g x := by
  classical
  rw [elevenFiveRelativeCount, ← Finset.sum_filter]
  simp [Nat.mul_comm]

/-- The raw `j=2` relative triple partition at an eleven--five split. -/
theorem elevenFive_relative_triple_row_two
    {Point : Type u} {Block : Type v} [Fintype Point] [Fintype Block]
    [DecidableEq Point]
    (S : BlockSystem Point Block) (D : Finset Point)
    (hpoint : Fintype.card Point = 11) (hD : D.card = 5) :
    (∑ b : Block, Nat.choose (S.support b ∩ D).card 2 *
      (S.support b \ D).card) = 60 := by
  have hrow := S.relative_triple_partition D 2 (by omega)
  rw [hpoint, hD] at hrow
  norm_num [Nat.choose] at hrow
  simpa using hrow

/-- The raw `j=1` relative triple partition at an eleven--five split. -/
theorem elevenFive_relative_triple_row_one
    {Point : Type u} {Block : Type v} [Fintype Point] [Fintype Block]
    [DecidableEq Point]
    (S : BlockSystem Point Block) (D : Finset Point)
    (hpoint : Fintype.card Point = 11) (hD : D.card = 5) :
    (∑ b : Block, (S.support b ∩ D).card *
      Nat.choose (S.support b \ D).card 2) = 75 := by
  have hrow := S.relative_triple_partition D 1 (by omega)
  rw [hpoint, hD] at hrow
  norm_num [Nat.choose] at hrow
  simpa using hrow

/-- The raw outsider triple partition at an eleven--five split. -/
theorem elevenFive_relative_triple_row_zero
    {Point : Type u} {Block : Type v} [Fintype Point] [Fintype Block]
    [DecidableEq Point]
    (S : BlockSystem Point Block) (D : Finset Point)
    (hpoint : Fintype.card Point = 11) (hD : D.card = 5) :
    (∑ b : Block, Nat.choose (S.support b \ D).card 3) = 20 := by
  have hrow := S.relative_triple_partition D 0 (by omega)
  rw [hpoint, hD] at hrow
  norm_num [Nat.choose] at hrow
  simpa using hrow

/-- The first expanded C39 front row.  Relative triple ownership with two
selected labels gives `A21 + 2 A22 + 3 A23 = 60`; the selected five-block
itself contributes zero, and every other block has selected trace at most
two. -/
theorem elevenFive_relativeCount_two_one_add_two_mul_two_two_add_three_mul_two_three_eq_sixty
    {Point : Type u} {Block : Type v} [Fintype Point] [Fintype Block]
    [DecidableEq Point]
    (S : BlockSystem Point Block) (D : Finset Point) (b : Block)
    (hpoint : Fintype.card Point = 11) (hD : D.card = 5)
    (hb : b ∈ S.blocksOfSize 5) (hDb : S.support b = D)
    (hcap : BlockSizeCap S 5) :
    elevenFiveRelativeCount S D 2 1 +
      2 * elevenFiveRelativeCount S D 2 2 +
        3 * elevenFiveRelativeCount S D 2 3 = 60 := by
  classical
  have hraw := elevenFive_relative_triple_row_two S D hpoint hD
  have hpointwise (c : Block) :
      Nat.choose (S.support c ∩ D).card 2 * (S.support c \ D).card =
        (if (S.support c ∩ D).card = 2 /\ (S.support c \ D).card = 1
          then 1 else 0) +
        (if (S.support c ∩ D).card = 2 /\ (S.support c \ D).card = 2
          then 2 else 0) +
        (if (S.support c ∩ D).card = 2 /\ (S.support c \ D).card = 3
          then 3 else 0) := by
    by_cases hcb : c = b
    · subst c
      simp [hDb]
    · have hinter := S.distinct_block_inter_card_lt_three (Ne.symm hcb)
      rw [hDb] at hinter
      have hi : (S.support c ∩ D).card <= 2 := by
        have hinter' : (S.support c ∩ D).card < 3 := by
          simpa [Finset.inter_comm] using hinter
        omega
      have hsplit := Finset.card_inter_add_card_sdiff (S.support c) D
      have hsize : (S.support c).card <= 5 := by
        by_cases hthree : 3 <= (S.support c).card
        · exact hcap c hthree
        · omega
      have ho : (S.support c \ D).card <= 5 := by omega
      interval_cases hinside : (S.support c ∩ D).card <;>
        interval_cases houtside : (S.support c \ D).card <;>
        norm_num [Nat.choose, hinside, houtside] at * <;> omega
  have hsum :
      (∑ c : Block, Nat.choose (S.support c ∩ D).card 2 *
        (S.support c \ D).card) =
      elevenFiveRelativeCount S D 2 1 +
        2 * elevenFiveRelativeCount S D 2 2 +
          3 * elevenFiveRelativeCount S D 2 3 := by
    simp_rw [hpointwise]
    simp only [Finset.sum_add_distrib]
    rw [elevenFive_sum_relative_indicator S D 2 1 1,
      elevenFive_sum_relative_indicator S D 2 2 2,
      elevenFive_sum_relative_indicator S D 2 3 3]
    simp
  omega

/-- The `A21` identity of the C39 front, obtained by eliminating `A22`
from the expanded two-selected triple row and the already materialized host
identity `H = A22 + 3 A23`. -/
theorem elevenFive_relativeCount_two_one_eq_sixty_sub_two_mul_host_add_three_mul_two_three
    {Point : Type u} {Block : Type v} [Fintype Point] [Fintype Block]
    [DecidableEq Point]
    (S : BlockSystem Point Block) (D : Finset Point) (b : Block)
    (hpoint : Fintype.card Point = 11) (hD : D.card = 5)
    (hb : b ∈ S.blocksOfSize 5) (hDb : S.support b = D)
    (hcap : BlockSizeCap S 5) :
    elevenFiveRelativeCount S D 2 1 =
      60 - 2 * elevenFiveHostWeight S D +
        3 * elevenFiveRelativeCount S D 2 3 := by
  have hrow :=
    elevenFive_relativeCount_two_one_add_two_mul_two_two_add_three_mul_two_three_eq_sixty
      S D b hpoint hD hb hDb hcap
  have hhost :=
    elevenFiveHostWeight_eq_relativeCount22_add_three_mul_relativeCount23 S D hcap
  have hhost_le : elevenFiveHostWeight S D <= 30 :=
    elevenFiveHostWeight_le_thirty S D hpoint hD
  omega

/-! ## The unconditional rich-block cap -/

/-- The `A04` relative count is the literal number of four-blocks disjoint
from the selected set. -/
theorem elevenFive_relativeCount_zero_four_eq_disjointFourCount
    {Point : Type u} {Block : Type v} [Fintype Point] [Fintype Block]
    [DecidableEq Point]
    (S : BlockSystem Point Block) (D : Finset Point) :
    elevenFiveRelativeCount S D 0 4 =
      ((S.blocksOfSize 4).filter fun c =>
        (S.support c ∩ D).card = 0).card := by
  classical
  unfold elevenFiveRelativeCount
  apply congrArg Finset.card
  ext c
  simp only [Finset.mem_filter, Finset.mem_univ, true_and,
    S.mem_blocksOfSize]
  constructor
  · rintro ⟨hinter, houtside⟩
    have hsplit := Finset.card_inter_add_card_sdiff (S.support c) D
    exact ⟨by omega, hinter⟩
  · rintro ⟨hsize, hinter⟩
    have hsplit := Finset.card_inter_add_card_sdiff (S.support c) D
    exact ⟨hinter, by omega⟩

/-- The `A05` relative count is the literal number of five-blocks disjoint
from the selected set. -/
theorem elevenFive_relativeCount_zero_five_eq_disjointFiveCount
    {Point : Type u} {Block : Type v} [Fintype Point] [Fintype Block]
    [DecidableEq Point]
    (S : BlockSystem Point Block) (D : Finset Point) :
    elevenFiveRelativeCount S D 0 5 =
      ((S.blocksOfSize 5).filter fun c =>
        (S.support c ∩ D).card = 0).card := by
  classical
  unfold elevenFiveRelativeCount
  apply congrArg Finset.card
  ext c
  simp only [Finset.mem_filter, Finset.mem_univ, true_and,
    S.mem_blocksOfSize]
  constructor
  · rintro ⟨hinter, houtside⟩
    have hsplit := Finset.card_inter_add_card_sdiff (S.support c) D
    exact ⟨by omega, hinter⟩
  · rintro ⟨hsize, hinter⟩
    have hsplit := Finset.card_inter_add_card_sdiff (S.support c) D
    exact ⟨hinter, by omega⟩

/-- The paper's local rich weight is exactly `A04 + 3 A05`. -/
theorem elevenFiveOutsideRichWeight_eq_relativeCount_zero_four_add_three_mul_zero_five
    {Point : Type u} {Block : Type v} [Fintype Point] [Fintype Block]
    [DecidableEq Point]
    (S : BlockSystem Point Block) (D : Finset Point) :
    elevenFiveOutsideRichWeight S D =
      elevenFiveRelativeCount S D 0 4 +
        3 * elevenFiveRelativeCount S D 0 5 := by
  unfold elevenFiveOutsideRichWeight
  rw [← elevenFive_relativeCount_zero_four_eq_disjointFourCount S D,
    ← elevenFive_relativeCount_zero_five_eq_disjointFiveCount S D]

/-- At an eleven--five split there is at most one disjoint five-block.
This is the `y ∈ {0,1}` half of the C39 rich-block cap and uses only triple
ownership: two five-subsets of the six outsiders would share a triple. -/
theorem elevenFive_relativeCount_zero_five_le_one
    {Point : Type u} {Block : Type v} [Fintype Point] [Fintype Block]
    [DecidableEq Point]
    (S : BlockSystem Point Block) (D : Finset Point)
    (hpoint : Fintype.card Point = 11) (hD : D.card = 5) :
    elevenFiveRelativeCount S D 0 5 <= 1 := by
  classical
  rw [elevenFive_relativeCount_zero_five_eq_disjointFiveCount S D,
    Finset.card_le_one]
  intro b hb c hc
  simp only [Finset.mem_filter] at hb hc
  by_contra hbc
  let X : Finset Point := Finset.univ \ D
  have hXcard : X.card = 6 := by
    simp [X, Finset.card_sdiff_of_subset (Finset.subset_univ D), hpoint, hD]
  have hbX : S.support b ⊆ X := by
    intro p hp
    refine Finset.mem_sdiff.mpr ⟨Finset.mem_univ p, ?_⟩
    intro hpD
    have hpinter : p ∈ S.support b ∩ D := Finset.mem_inter.mpr ⟨hp, hpD⟩
    have hempty : S.support b ∩ D = ∅ := Finset.card_eq_zero.mp hb.2
    simpa [hempty] using hpinter
  have hcX : S.support c ⊆ X := by
    intro p hp
    refine Finset.mem_sdiff.mpr ⟨Finset.mem_univ p, ?_⟩
    intro hpD
    have hpinter : p ∈ S.support c ∩ D := Finset.mem_inter.mpr ⟨hp, hpD⟩
    have hempty : S.support c ∩ D = ∅ := Finset.card_eq_zero.mp hc.2
    simpa [hempty] using hpinter
  have hUnion : (S.support b ∪ S.support c).card <= 6 := by
    have hsub : S.support b ∪ S.support c ⊆ X := Finset.union_subset hbX hcX
    exact (Finset.card_le_card hsub).trans_eq hXcard
  have hsizeB := S.mem_blocksOfSize.mp hb.1
  have hsizeC := S.mem_blocksOfSize.mp hc.1
  have hcount := Finset.card_union_add_card_inter (S.support b) (S.support c)
  have hinter := S.distinct_block_inter_card_lt_three hbc
  omega

/-- The disjoint four-blocks have pairwise disjoint complementary pairs in
the six-point outsider set.  Thus there are at most three of them. -/
theorem elevenFive_relativeCount_zero_four_le_three
    {Point : Type u} {Block : Type v} [Fintype Point] [Fintype Block]
    [DecidableEq Point]
    (S : BlockSystem Point Block) (D : Finset Point)
    (hpoint : Fintype.card Point = 11) (hD : D.card = 5) :
    elevenFiveRelativeCount S D 0 4 <= 3 := by
  classical
  let X : Finset Point := Finset.univ \ D
  let F4 := (S.blocksOfSize 4).filter fun c => (S.support c ∩ D).card = 0
  have hXcard : X.card = 6 := by
    simp [X, Finset.card_sdiff_of_subset (Finset.subset_univ D), hpoint, hD]
  have hsub (c : Block) (hc : c ∈ F4) : S.support c ⊆ X := by
    intro p hp
    refine Finset.mem_sdiff.mpr ⟨Finset.mem_univ p, ?_⟩
    intro hpD
    have hc' : c ∈ S.blocksOfSize 4 /\ (S.support c ∩ D).card = 0 := by
      simpa [F4] using hc
    have hspec : (S.support c ∩ D).card = 0 := hc'.2
    have hempty : S.support c ∩ D = ∅ := Finset.card_eq_zero.mp hspec
    have hpinter : p ∈ S.support c ∩ D := Finset.mem_inter.mpr ⟨hp, hpD⟩
    simpa [hempty] using hpinter
  let comp : Block → Finset Point := fun c => X \ S.support c
  have hcompCard (c : Block) (hc : c ∈ F4) : (comp c).card = 2 := by
    have hc' : c ∈ S.blocksOfSize 4 /\ (S.support c ∩ D).card = 0 := by
      simpa [F4] using hc
    have hsize : (S.support c).card = 4 := S.mem_blocksOfSize.mp hc'.1
    rw [show comp c = X \ S.support c by rfl,
      Finset.card_sdiff_of_subset (hsub c hc), hXcard, hsize]
  have hdisj : (F4 : Set Block).PairwiseDisjoint comp := by
    intro b hb c hc hbc
    change Disjoint (comp b) (comp c)
    rw [Finset.disjoint_left]
    intro p hpB hpC
    have hpB' : p ∈ X ∧ p ∉ S.support b := by
      simpa [comp] using (Finset.mem_sdiff.mp hpB)
    have hpC' : p ∈ X ∧ p ∉ S.support c := by
      simpa [comp] using (Finset.mem_sdiff.mp hpC)
    have hUnionSub : S.support b ∪ S.support c ⊆ X.erase p := by
      intro z hz
      refine Finset.mem_erase.mpr ⟨?_, ?_⟩
      · intro hzp
        subst z
        rcases Finset.mem_union.mp hz with hzb | hzc
        · exact hpB'.2 hzb
        · exact hpC'.2 hzc
      · rcases Finset.mem_union.mp hz with hzb | hzc
        · exact hsub b hb hzb
        · exact hsub c hc hzc
    have hUnionCard : (S.support b ∪ S.support c).card <= 5 := by
      calc
        (S.support b ∪ S.support c).card <= (X.erase p).card :=
          Finset.card_le_card hUnionSub
        _ = 5 := by rw [Finset.card_erase_of_mem hpB'.1, hXcard]
    have hb' : b ∈ S.blocksOfSize 4 /\ (S.support b ∩ D).card = 0 := by
      simpa [F4] using hb
    have hc' : c ∈ S.blocksOfSize 4 /\ (S.support c ∩ D).card = 0 := by
      simpa [F4] using hc
    have hsizeB : (S.support b).card = 4 := S.mem_blocksOfSize.mp hb'.1
    have hsizeC : (S.support c).card = 4 := S.mem_blocksOfSize.mp hc'.1
    have hcount := Finset.card_union_add_card_inter (S.support b) (S.support c)
    have hinter := S.distinct_block_inter_card_lt_three hbc
    omega
  have hUnionSub : F4.biUnion comp ⊆ X := by
    intro p hp
    obtain ⟨c, hc, hpc⟩ := Finset.mem_biUnion.mp hp
    exact (Finset.mem_sdiff.mp (by simpa [comp] using hpc)).1
  have hUnionCard : (F4.biUnion comp).card = 2 * F4.card := by
    rw [Finset.card_biUnion hdisj]
    calc
      (∑ c ∈ F4, (comp c).card) = ∑ _c ∈ F4, 2 := by
        apply Finset.sum_congr rfl
        intro c hc
        exact hcompCard c hc
      _ = 2 * F4.card := by simp [Nat.mul_comm]
  have hle := Finset.card_le_card hUnionSub
  rw [hUnionCard, hXcard] at hle
  have hF4 : elevenFiveRelativeCount S D 0 4 = F4.card := by
    simpa [F4] using
      elevenFive_relativeCount_zero_four_eq_disjointFourCount S D
  rw [hF4]
  omega

/-- If the unique disjoint five-block exists, no disjoint four-block can
exist: their supports would share at least three of the six outsider labels.
Consequently the rich weight is exactly three. -/
theorem elevenFiveOutsideRichWeight_eq_three_of_relativeCount_zero_five_eq_one
    {Point : Type u} {Block : Type v} [Fintype Point] [Fintype Block]
    [DecidableEq Point]
    (S : BlockSystem Point Block) (D : Finset Point)
    (hpoint : Fintype.card Point = 11) (hD : D.card = 5)
    (hy : elevenFiveRelativeCount S D 0 5 = 1) :
    elevenFiveOutsideRichWeight S D = 3 := by
  classical
  let F4 := (S.blocksOfSize 4).filter fun c => (S.support c ∩ D).card = 0
  let F5 := (S.blocksOfSize 5).filter fun c => (S.support c ∩ D).card = 0
  have hF5 : F5.card = 1 := by
    simpa [F5] using
      (elevenFive_relativeCount_zero_five_eq_disjointFiveCount S D).symm.trans hy
  have hF4 : F4.card = 0 := by
    apply Finset.card_eq_zero.mpr
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro c hc
    obtain ⟨b, hb⟩ := Finset.card_pos.mp (by omega : 0 < F5.card)
    have hc' : c ∈ S.blocksOfSize 4 /\ (S.support c ∩ D).card = 0 := by
      simpa [F4] using hc
    have hb' : b ∈ S.blocksOfSize 5 /\ (S.support b ∩ D).card = 0 := by
      simpa [F5] using hb
    have hbc : b ≠ c := by
      intro hbc
      subst c
      have hfour := S.mem_blocksOfSize.mp hc'.1
      have hfive := S.mem_blocksOfSize.mp hb'.1
      omega
    let X : Finset Point := Finset.univ \ D
    have hXcard : X.card = 6 := by
      simp [X, Finset.card_sdiff_of_subset (Finset.subset_univ D), hpoint, hD]
    have hbX : S.support b ⊆ X := by
      intro p hp
      refine Finset.mem_sdiff.mpr ⟨Finset.mem_univ p, ?_⟩
      intro hpD
      have hpinter : p ∈ S.support b ∩ D := Finset.mem_inter.mpr ⟨hp, hpD⟩
      have hempty : S.support b ∩ D = ∅ := Finset.card_eq_zero.mp hb'.2
      simpa [hempty] using hpinter
    have hcX : S.support c ⊆ X := by
      intro p hp
      refine Finset.mem_sdiff.mpr ⟨Finset.mem_univ p, ?_⟩
      intro hpD
      have hpinter : p ∈ S.support c ∩ D := Finset.mem_inter.mpr ⟨hp, hpD⟩
      have hempty : S.support c ∩ D = ∅ := Finset.card_eq_zero.mp hc'.2
      simpa [hempty] using hpinter
    have hUnion : (S.support b ∪ S.support c).card <= 6 := by
      have hsub : S.support b ∪ S.support c ⊆ X := Finset.union_subset hbX hcX
      exact (Finset.card_le_card hsub).trans_eq hXcard
    have hsizeB := S.mem_blocksOfSize.mp hb'.1
    have hsizeC := S.mem_blocksOfSize.mp hc'.1
    have hcount := Finset.card_union_add_card_inter (S.support b) (S.support c)
    have hinter := S.distinct_block_inter_card_lt_three hbc
    omega
  rw [elevenFiveOutsideRichWeight_eq_relativeCount_zero_four_add_three_mul_zero_five,
    elevenFive_relativeCount_zero_four_eq_disjointFourCount,
    elevenFive_relativeCount_zero_five_eq_disjointFiveCount]
  have hF4set : ((S.blocksOfSize 4).filter fun c => S.support c ∩ D = ∅) = F4 := by
    ext c
    simp [F4, Finset.card_eq_zero]
  have hF4' : ((S.blocksOfSize 4).filter fun c => S.support c ∩ D = ∅).card = 0 := by
    rw [hF4set]
    exact hF4
  have hF5set : ((S.blocksOfSize 5).filter fun c => S.support c ∩ D = ∅) = F5 := by
    ext c
    simp [F5, Finset.card_eq_zero]
  have hF5' : ((S.blocksOfSize 5).filter fun c => S.support c ∩ D = ∅).card = 1 := by
    rw [hF5set]
    exact hF5
  simp [hF4', hF5']

/-- The C39 rich-block cap is a finite packing fact: either there is one
disjoint five-block, when the rich weight is exactly three, or the
disjoint four-blocks have the three complementary-pair bound above. -/
theorem elevenFiveOutsideRichWeight_le_three
    {Point : Type u} {Block : Type v} [Fintype Point] [Fintype Block]
    [DecidableEq Point]
    (S : BlockSystem Point Block) (D : Finset Point)
    (hpoint : Fintype.card Point = 11) (hD : D.card = 5) :
    elevenFiveOutsideRichWeight S D <= 3 := by
  have hy := elevenFive_relativeCount_zero_five_le_one S D hpoint hD
  rcases Nat.eq_zero_or_pos (elevenFiveRelativeCount S D 0 5) with hy | hy
  · rw [elevenFiveOutsideRichWeight_eq_relativeCount_zero_four_add_three_mul_zero_five,
      hy, Nat.mul_zero, Nat.add_zero]
    exact elevenFive_relativeCount_zero_four_le_three S D hpoint hD
  · have hyone : elevenFiveRelativeCount S D 0 5 = 1 := by omega
    rw [elevenFiveOutsideRichWeight_eq_three_of_relativeCount_zero_five_eq_one
      S D hpoint hD hyone]

/-- The actual number of C39 high points on the outsider side of a selected
set.  This is the paper's `e_X`; it is defined from the existing high
indicator rather than introduced as an auxiliary certificate. -/
noncomputable def elevenFiveC39HighOutsideCount
    {Point : Type u} {Block : Type v} [Fintype Point] [Fintype Block]
    [DecidableEq Point]
    (S : BlockSystem Point Block) (D : Finset Point) : Nat :=
  ∑ p ∈ Finset.univ \ D, elevenFiveC39HighIndicator S p

/-- The formal no-singleton entrance.  The implication `hfront` is exactly
the currently missing rebased C39 front: it is only requested after the
actual `A14` census has vanished.  All remaining work, including turning the
conclusion into an actual size-five block, is discharged here. -/
theorem elevenFive_c39_singleton_exists_of_noSingleton_front
    {Point : Type u} {Block : Type v} [Fintype Point] [Fintype Block]
    [DecidableEq Point]
    (S : BlockSystem Point Block) (D : Finset Point)
    (hhost : elevenFiveHostWeight S D <= 27)
    (q y A12 eX : Nat) (hq : q <= 3) (hy : y <= 1)
    (hyRich : y = 1 -> q = 3)
    (hfront : elevenFiveRelativeCount S D 1 4 = 0 ->
      (A12 : Int) = 3 * (q : Int) -
          (30 - elevenFiveHostWeight S D : Nat) /\
        (eX : Int) = 3 - (30 - elevenFiveHostWeight S D : Nat) -
          (q : Int) + 2 * (y : Int)) :
    ∃ c, c ∈ S.blocksOfSize 5 /\
      (S.support c ∩ D).card = 1 := by
  classical
  by_contra hno
  have hzero :=
    elevenFive_relativeCount_one_four_eq_zero_of_no_sizeFive_singleton S D hno
  obtain ⟨hA12, heX⟩ := hfront hzero
  have hR : 3 <= 30 - elevenFiveHostWeight S D := by omega
  exact elevenFive_c39_noSingleton_front_arithmetic_absurd
    (30 - elevenFiveHostWeight S D) q y A12 eX hR hq hy hyRich hA12 heX

/-- Public C39 singleton entrance with all relative quantities materialized.
The rich-block cap and its equality case are finite theorems of the abstract
block system.  The only remaining input is the rebased signed front. -/
theorem elevenFive_c39_singleton_exists_of_rebased_signed_front
    {Point : Type u} {Block : Type v} [Fintype Point] [Fintype Block]
    [DecidableEq Point]
    (S : BlockSystem Point Block) (D : Finset Point)
    (hpoint : Fintype.card Point = 11) (hD : D.card = 5)
    (hhost : elevenFiveHostWeight S D <= 27)
    (hfront : elevenFiveRelativeCount S D 1 4 = 0 ->
      (elevenFiveRelativeCount S D 1 2 : Int) =
          3 * (elevenFiveOutsideRichWeight S D : Int) -
            (30 - elevenFiveHostWeight S D : Nat) /\
        (elevenFiveC39HighOutsideCount S D : Int) =
          3 - (30 - elevenFiveHostWeight S D : Nat) -
            (elevenFiveOutsideRichWeight S D : Int) +
              2 * (elevenFiveRelativeCount S D 0 5 : Int)) :
    ∃ c, c ∈ S.blocksOfSize 5 /\ (S.support c ∩ D).card = 1 := by
  exact elevenFive_c39_singleton_exists_of_noSingleton_front
    S D hhost (elevenFiveOutsideRichWeight S D)
      (elevenFiveRelativeCount S D 0 5)
      (elevenFiveRelativeCount S D 1 2)
      (elevenFiveC39HighOutsideCount S D)
      (elevenFiveOutsideRichWeight_le_three S D hpoint hD)
      (elevenFive_relativeCount_zero_five_le_one S D hpoint hD)
      (fun hy =>
        elevenFiveOutsideRichWeight_eq_three_of_relativeCount_zero_five_eq_one
          S D hpoint hD hy)
      hfront

/-- The C39,L12 residual combined with the no-singleton front.  In the
`H <= 27` maximum-host face the singleton neighbour is automatically a
proper five-circle, because the existing router has already eliminated
five-lines. -/
theorem elevenFive_c39_l12_singleton_front_of_rows
    {Point : Type u} {Block : Type v} [Fintype Point] [Fintype Block]
    [DecidableEq Point]
    (S : BlockSystem Point Block) (hcard : Fintype.card Point = 11)
    (hcap : BlockSizeCap S 5)
    (hlocal : ∀ p : Point, ElevenFiveLocalRows S p)
    (hglobal : ElevenFiveGlobalRows S)
    (hC : S.totalCircleCount = 39)
    (hL : elevenFiveLineTotal S = 12)
    (hcircle : ∀ b ∈ S.circleBlocksOfSize 5,
      elevenFiveHostWeight S (S.support b) <= 27)
    (b : Block) (hb : b ∈ S.circleBlocksOfSize 5)
    (q y A12 eX : Nat) (hq : q <= 3) (hy : y <= 1)
    (hyRich : y = 1 -> q = 3)
    (hfront : elevenFiveRelativeCount S (S.support b) 1 4 = 0 ->
      (A12 : Int) = 3 * (q : Int) -
          (30 - elevenFiveHostWeight S (S.support b) : Nat) /\
        (eX : Int) = 3 - (30 - elevenFiveHostWeight S (S.support b) : Nat) -
          (q : Int) + 2 * (y : Int)) :
    S.blockCount 5 = 5 /\ S.lineCount 5 = 0 /\
      elevenFiveC39HighCount S = 1 /\
      ∃ c, c ∈ S.circleBlocksOfSize 5 /\
        (S.support c ∩ S.support b).card = 1 := by
  obtain ⟨hm, hline, hhigh⟩ :=
    elevenFive_c39_l12_circleHost_le_twenty_seven_residual
      S hcard hcap hlocal hglobal hC hL hcircle
  have hhost := hcircle b hb
  obtain ⟨c, hc, hinter⟩ :=
    elevenFive_c39_singleton_exists_of_noSingleton_front
      S (S.support b) hhost q y A12 eX hq hy hyRich hfront
  have hsize := S.mem_blocksOfSize.mp hc
  have hcircleC : c ∈ S.circleBlocksOfSize 5 := by
    cases hkind : S.kind c with
    | line =>
        have hmem : c ∈ S.lineBlocksOfSize 5 :=
          S.mem_blocksOfKindSize.mpr ⟨hkind, hsize⟩
        have hpos : 0 < S.lineCount 5 := by
          unfold BlockSystem.lineCount
          exact Finset.card_pos.mpr ⟨c, hmem⟩
        omega
    | circle =>
        exact S.mem_blocksOfKindSize.mpr ⟨hkind, hsize⟩
  exact ⟨hm, hline, hhigh, c, hcircleC, hinter⟩

/-- The L12 residual router with the finite rich-block cap discharged.  This
is the parameter-free-in-`q` form of the singleton entrance; the remaining
front hypothesis is stated entirely using the actual relative censuses. -/
theorem elevenFive_c39_l12_singleton_front_of_rebased_signed_front_of_rows
    {Point : Type u} {Block : Type v} [Fintype Point] [Fintype Block]
    [DecidableEq Point]
    (S : BlockSystem Point Block) (hcard : Fintype.card Point = 11)
    (hcap : BlockSizeCap S 5)
    (hlocal : ∀ p : Point, ElevenFiveLocalRows S p)
    (hglobal : ElevenFiveGlobalRows S)
    (hC : S.totalCircleCount = 39)
    (hL : elevenFiveLineTotal S = 12)
    (hcircle : ∀ b ∈ S.circleBlocksOfSize 5,
      elevenFiveHostWeight S (S.support b) <= 27)
    (b : Block) (hb : b ∈ S.circleBlocksOfSize 5)
    (hfront : elevenFiveRelativeCount S (S.support b) 1 4 = 0 ->
      (elevenFiveRelativeCount S (S.support b) 1 2 : Int) =
          3 * (elevenFiveOutsideRichWeight S (S.support b) : Int) -
            (30 - elevenFiveHostWeight S (S.support b) : Nat) /\
        (elevenFiveC39HighOutsideCount S (S.support b) : Int) =
          3 - (30 - elevenFiveHostWeight S (S.support b) : Nat) -
            (elevenFiveOutsideRichWeight S (S.support b) : Int) +
              2 * (elevenFiveRelativeCount S (S.support b) 0 5 : Int)) :
    S.blockCount 5 = 5 /\ S.lineCount 5 = 0 /\
      elevenFiveC39HighCount S = 1 /\
      ∃ c, c ∈ S.circleBlocksOfSize 5 /\
        (S.support c ∩ S.support b).card = 1 := by
  obtain ⟨hm, hline, hhigh⟩ :=
    elevenFive_c39_l12_circleHost_le_twenty_seven_residual
      S hcard hcap hlocal hglobal hC hL hcircle
  have hsizeB : (S.support b).card = 5 :=
    (S.mem_blocksOfKindSize.mp hb).2
  have hhost := hcircle b hb
  obtain ⟨c, hc, hinter⟩ :=
    elevenFive_c39_singleton_exists_of_rebased_signed_front
      S (S.support b) hcard hsizeB hhost hfront
  have hsize := S.mem_blocksOfSize.mp hc
  have hcircleC : c ∈ S.circleBlocksOfSize 5 := by
    cases hkind : S.kind c with
    | line =>
        have hmem : c ∈ S.lineBlocksOfSize 5 :=
          S.mem_blocksOfKindSize.mpr ⟨hkind, hsize⟩
        have hpos : 0 < S.lineCount 5 := by
          unfold BlockSystem.lineCount
          exact Finset.card_pos.mpr ⟨c, hmem⟩
        omega
    | circle =>
        exact S.mem_blocksOfKindSize.mpr ⟨hkind, hsize⟩
  exact ⟨hm, hline, hhigh, c, hcircleC, hinter⟩

end Erdos506.V1
