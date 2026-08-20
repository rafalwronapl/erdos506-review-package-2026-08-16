import Erdos506.V1.ElevenFiveC39SingletonFront
import Mathlib.Tactic

/-!
# The completed signed C39 front

This file derives the two formerly residual signed rows at a selected
five-block directly from the tagged block census.  The only branch assumption
is the literal vanishing of `A14`, i.e. absence of a singleton five-block
neighbour.  In particular, neither signed row is an additional geometric
principle.
-/

namespace Erdos506.V1

open Erdos506.Block
open Erdos506.Block.BlockSystem
open scoped BigOperators

universe u v

/-- Sum a constant over one actual support-size layer. -/
private theorem elevenFive_c39_sum_size_indicator
    {Point : Type u} {Block : Type v} [Fintype Point] [Fintype Block]
    [DecidableEq Point]
    (S : BlockSystem Point Block) (s a : Nat) :
    (∑ b : Block, if (S.support b).card = s then a else 0) =
      a * S.blockCount s := by
  classical
  unfold BlockSystem.blockCount BlockSystem.blocksOfSize
  rw [← Finset.sum_filter]
  simp [Nat.mul_comm]

/-- Every block different from the chosen five-block has selected trace at
most two, and the five-cap bounds its full support. -/
private theorem elevenFive_c39_other_block_trace_bounds
    {Point : Type u} {Block : Type v} [Fintype Point] [Fintype Block]
    [DecidableEq Point]
    (S : BlockSystem Point Block) (b c : Block)
    (hb : b ∈ S.blocksOfSize 5) (hcb : c ≠ b)
    (hcap : BlockSizeCap S 5) :
    (S.support c ∩ S.support b).card ≤ 2 /\
      (S.support c).card ≤ 5 /\
      (S.support c \ S.support b).card ≤ 5 := by
  have hinter := S.distinct_block_inter_card_lt_three (Ne.symm hcb)
  have hinside : (S.support c ∩ S.support b).card ≤ 2 := by
    have hlt : (S.support c ∩ S.support b).card < 3 := by
      simpa [Finset.inter_comm] using hinter
    omega
  have hsize : (S.support c).card ≤ 5 := by
    by_cases hsmall : (S.support c).card < 3
    · omega
    · exact hcap c (by omega)
  have hsplit := Finset.card_inter_add_card_sdiff (S.support c) (S.support b)
  have houtside : (S.support c \ S.support b).card ≤ 5 := by omega
  exact ⟨hinside, hsize, houtside⟩

/-- The full size-four/five C39 row rebased at a selected five-block, exposed
for the high-host `H = 28,29,30` routers. -/
theorem elevenFive_c39_relative_size_weight_row
    {Point : Type u} {Block : Type v} [Fintype Point] [Fintype Block]
    [DecidableEq Point]
    (S : BlockSystem Point Block) (b : Block)
    (hb : b ∈ S.blocksOfSize 5) (hcap : BlockSizeCap S 5) :
    S.blockCount 4 + 3 * S.blockCount 5 =
      elevenFiveRelativeCount S (S.support b) 0 4 +
        elevenFiveRelativeCount S (S.support b) 1 3 +
          elevenFiveRelativeCount S (S.support b) 2 2 +
            3 * elevenFiveRelativeCount S (S.support b) 0 5 +
              3 * elevenFiveRelativeCount S (S.support b) 1 4 +
                3 * elevenFiveRelativeCount S (S.support b) 2 3 + 3 := by
  classical
  have hpoint (c : Block) :
      (if (S.support c).card = 4 then 1 else 0) +
          (if (S.support c).card = 5 then 3 else 0) =
        (if (S.support c ∩ S.support b).card = 0 /\
            (S.support c \ S.support b).card = 4 then 1 else 0) +
          (if (S.support c ∩ S.support b).card = 1 /\
              (S.support c \ S.support b).card = 3 then 1 else 0) +
            (if (S.support c ∩ S.support b).card = 2 /\
                (S.support c \ S.support b).card = 2 then 1 else 0) +
              (if (S.support c ∩ S.support b).card = 0 /\
                  (S.support c \ S.support b).card = 5 then 3 else 0) +
                (if (S.support c ∩ S.support b).card = 1 /\
                    (S.support c \ S.support b).card = 4 then 3 else 0) +
                  (if (S.support c ∩ S.support b).card = 2 /\
                      (S.support c \ S.support b).card = 3 then 3 else 0) +
                    (if c = b then 3 else 0) := by
    by_cases hcb : c = b
    · subst c
      have hsize : (S.support b).card = 5 := S.mem_blocksOfSize.mp hb
      simp [hsize]
    · obtain ⟨hinside, hsize, houtside⟩ :=
        elevenFive_c39_other_block_trace_bounds S b c hb hcb hcap
      have hsplit := Finset.card_inter_add_card_sdiff (S.support c) (S.support b)
      have hcardSize : (S.support c).card =
          (S.support c ∩ S.support b).card +
            (S.support c \ S.support b).card := hsplit.symm
      by_cases hfour : (S.support c).card = 4
      · have hsum :
            (S.support c ∩ S.support b).card +
                (S.support c \ S.support b).card = 4 := by
            omega
        interval_cases hi : (S.support c ∩ S.support b).card
        · have ho : (S.support c \ S.support b).card = 4 := by omega
          simp [hfour, hi, ho, hcb]
        · have ho : (S.support c \ S.support b).card = 3 := by omega
          simp [hfour, hi, ho, hcb]
        · have ho : (S.support c \ S.support b).card = 2 := by omega
          simp [hfour, hi, ho, hcb]
      · by_cases hfive : (S.support c).card = 5
        · have hsum :
              (S.support c ∩ S.support b).card +
                  (S.support c \ S.support b).card = 5 := by
              omega
          interval_cases hi : (S.support c ∩ S.support b).card
          · have ho : (S.support c \ S.support b).card = 5 := by omega
            simp [hfour, hfive, hi, ho, hcb]
          · have ho : (S.support c \ S.support b).card = 4 := by omega
            simp [hfour, hfive, hi, ho, hcb]
          · have ho : (S.support c \ S.support b).card = 3 := by omega
            simp [hfour, hfive, hi, ho, hcb]
        · have h04 : ¬ ((S.support c ∩ S.support b).card = 0 /\
              (S.support c \ S.support b).card = 4) := by
            rintro ⟨hi, ho⟩
            apply hfour
            omega
          have h13 : ¬ ((S.support c ∩ S.support b).card = 1 /\
              (S.support c \ S.support b).card = 3) := by
            rintro ⟨hi, ho⟩
            apply hfour
            omega
          have h22 : ¬ ((S.support c ∩ S.support b).card = 2 /\
              (S.support c \ S.support b).card = 2) := by
            rintro ⟨hi, ho⟩
            apply hfour
            omega
          have h05 : ¬ ((S.support c ∩ S.support b).card = 0 /\
              (S.support c \ S.support b).card = 5) := by
            rintro ⟨hi, ho⟩
            apply hfive
            omega
          have h14 : ¬ ((S.support c ∩ S.support b).card = 1 /\
              (S.support c \ S.support b).card = 4) := by
            rintro ⟨hi, ho⟩
            apply hfive
            omega
          have h23 : ¬ ((S.support c ∩ S.support b).card = 2 /\
              (S.support c \ S.support b).card = 3) := by
            rintro ⟨hi, ho⟩
            apply hfive
            omega
          simp only [Finset.card_eq_zero] at h04 h05
          simp [hfour, hfive, h04, h13, h22, h05, h14, h23, hcb]
  have hsum :
      (∑ c : Block, (
        (if (S.support c).card = 4 then 1 else 0) +
          (if (S.support c).card = 5 then 3 else 0))) =
        elevenFiveRelativeCount S (S.support b) 0 4 +
          elevenFiveRelativeCount S (S.support b) 1 3 +
            elevenFiveRelativeCount S (S.support b) 2 2 +
              3 * elevenFiveRelativeCount S (S.support b) 0 5 +
                3 * elevenFiveRelativeCount S (S.support b) 1 4 +
                  3 * elevenFiveRelativeCount S (S.support b) 2 3 + 3 := by
    calc
      (∑ c : Block, (
        (if (S.support c).card = 4 then 1 else 0) +
          (if (S.support c).card = 5 then 3 else 0))) =
          ∑ c : Block, (
            (if (S.support c ∩ S.support b).card = 0 /\
                (S.support c \ S.support b).card = 4 then 1 else 0) +
              (if (S.support c ∩ S.support b).card = 1 /\
                  (S.support c \ S.support b).card = 3 then 1 else 0) +
                (if (S.support c ∩ S.support b).card = 2 /\
                    (S.support c \ S.support b).card = 2 then 1 else 0) +
                  (if (S.support c ∩ S.support b).card = 0 /\
                      (S.support c \ S.support b).card = 5 then 3 else 0) +
                    (if (S.support c ∩ S.support b).card = 1 /\
                        (S.support c \ S.support b).card = 4 then 3 else 0) +
                      (if (S.support c ∩ S.support b).card = 2 /\
                          (S.support c \ S.support b).card = 3 then 3 else 0) +
                        (if c = b then 3 else 0)) := by
          apply Finset.sum_congr rfl
          intro c _hc
          exact hpoint c
      _ = _ := by
        simp only [Finset.sum_add_distrib]
        rw [elevenFive_sum_relative_indicator S (S.support b) 0 4 1,
          elevenFive_sum_relative_indicator S (S.support b) 1 3 1,
          elevenFive_sum_relative_indicator S (S.support b) 2 2 1,
          elevenFive_sum_relative_indicator S (S.support b) 0 5 3,
          elevenFive_sum_relative_indicator S (S.support b) 1 4 3,
          elevenFive_sum_relative_indicator S (S.support b) 2 3 3]
        simp
  rw [Finset.sum_add_distrib,
    elevenFive_c39_sum_size_indicator S 4 1,
    elevenFive_c39_sum_size_indicator S 5 3] at hsum
  simpa using hsum

/-- The raw `j=1` triple row, expanded into the only nonzero relative
fibres at a selected five-block. -/
private theorem elevenFive_c39_relative_triple_one_row
    {Point : Type u} {Block : Type v} [Fintype Point] [Fintype Block]
    [DecidableEq Point]
    (S : BlockSystem Point Block) (b : Block)
    (hcard : Fintype.card Point = 11)
    (hb : b ∈ S.blocksOfSize 5) (hcap : BlockSizeCap S 5) :
    elevenFiveRelativeCount S (S.support b) 1 2 +
        3 * elevenFiveRelativeCount S (S.support b) 1 3 +
          6 * elevenFiveRelativeCount S (S.support b) 1 4 +
            2 * elevenFiveRelativeCount S (S.support b) 2 2 +
              6 * elevenFiveRelativeCount S (S.support b) 2 3 = 75 := by
  classical
  have hD : (S.support b).card = 5 := S.mem_blocksOfSize.mp hb
  have hraw := elevenFive_relative_triple_row_one S (S.support b) hcard hD
  have hpoint (c : Block) :
      (S.support c ∩ S.support b).card *
          Nat.choose (S.support c \ S.support b).card 2 =
        (if (S.support c ∩ S.support b).card = 1 /\
            (S.support c \ S.support b).card = 2 then 1 else 0) +
          (if (S.support c ∩ S.support b).card = 1 /\
              (S.support c \ S.support b).card = 3 then 3 else 0) +
            (if (S.support c ∩ S.support b).card = 1 /\
                (S.support c \ S.support b).card = 4 then 6 else 0) +
              (if (S.support c ∩ S.support b).card = 2 /\
                  (S.support c \ S.support b).card = 2 then 2 else 0) +
                (if (S.support c ∩ S.support b).card = 2 /\
                    (S.support c \ S.support b).card = 3 then 6 else 0) := by
    by_cases hcb : c = b
    · subst c
      simp [hD]
    · obtain ⟨hinside, hsize, houtside⟩ :=
        elevenFive_c39_other_block_trace_bounds S b c hb hcb hcap
      have hsplit := Finset.card_inter_add_card_sdiff (S.support c) (S.support b)
      interval_cases hi : (S.support c ∩ S.support b).card <;>
        interval_cases ho : (S.support c \ S.support b).card <;>
        norm_num [Nat.choose, hi, ho] at * <;> omega
  have hsum :
      (∑ c : Block, (S.support c ∩ S.support b).card *
        Nat.choose (S.support c \ S.support b).card 2) =
        elevenFiveRelativeCount S (S.support b) 1 2 +
          3 * elevenFiveRelativeCount S (S.support b) 1 3 +
            6 * elevenFiveRelativeCount S (S.support b) 1 4 +
              2 * elevenFiveRelativeCount S (S.support b) 2 2 +
                6 * elevenFiveRelativeCount S (S.support b) 2 3 := by
    calc
      (∑ c : Block, (S.support c ∩ S.support b).card *
        Nat.choose (S.support c \ S.support b).card 2) =
          ∑ c : Block, (
            (if (S.support c ∩ S.support b).card = 1 /\
                (S.support c \ S.support b).card = 2 then 1 else 0) +
              (if (S.support c ∩ S.support b).card = 1 /\
                  (S.support c \ S.support b).card = 3 then 3 else 0) +
                (if (S.support c ∩ S.support b).card = 1 /\
                    (S.support c \ S.support b).card = 4 then 6 else 0) +
                  (if (S.support c ∩ S.support b).card = 2 /\
                      (S.support c \ S.support b).card = 2 then 2 else 0) +
                    (if (S.support c ∩ S.support b).card = 2 /\
                        (S.support c \ S.support b).card = 3 then 6 else 0)) := by
          apply Finset.sum_congr rfl
          intro c _hc
          exact hpoint c
      _ = _ := by
        simp only [Finset.sum_add_distrib]
        rw [elevenFive_sum_relative_indicator S (S.support b) 1 2 1,
          elevenFive_sum_relative_indicator S (S.support b) 1 3 3,
          elevenFive_sum_relative_indicator S (S.support b) 1 4 6,
          elevenFive_sum_relative_indicator S (S.support b) 2 2 2,
          elevenFive_sum_relative_indicator S (S.support b) 2 3 6]
        simp
  exact hsum.symm.trans hraw

/-- The raw outsider triple row at a selected five-block. -/
private theorem elevenFive_c39_relative_triple_zero_row
    {Point : Type u} {Block : Type v} [Fintype Point] [Fintype Block]
    [DecidableEq Point]
    (S : BlockSystem Point Block) (b : Block)
    (hcard : Fintype.card Point = 11)
    (hb : b ∈ S.blocksOfSize 5) (hcap : BlockSizeCap S 5) :
    elevenFiveRelativeCount S (S.support b) 0 3 +
        4 * elevenFiveRelativeCount S (S.support b) 0 4 +
          10 * elevenFiveRelativeCount S (S.support b) 0 5 +
            elevenFiveRelativeCount S (S.support b) 1 3 +
              4 * elevenFiveRelativeCount S (S.support b) 1 4 +
                elevenFiveRelativeCount S (S.support b) 2 3 = 20 := by
  classical
  have hD : (S.support b).card = 5 := S.mem_blocksOfSize.mp hb
  have hraw := elevenFive_relative_triple_row_zero S (S.support b) hcard hD
  have hpoint (c : Block) :
      Nat.choose (S.support c \ S.support b).card 3 =
        (if (S.support c ∩ S.support b).card = 0 /\
            (S.support c \ S.support b).card = 3 then 1 else 0) +
          (if (S.support c ∩ S.support b).card = 0 /\
              (S.support c \ S.support b).card = 4 then 4 else 0) +
            (if (S.support c ∩ S.support b).card = 0 /\
                (S.support c \ S.support b).card = 5 then 10 else 0) +
              (if (S.support c ∩ S.support b).card = 1 /\
                  (S.support c \ S.support b).card = 3 then 1 else 0) +
                (if (S.support c ∩ S.support b).card = 1 /\
                    (S.support c \ S.support b).card = 4 then 4 else 0) +
                  (if (S.support c ∩ S.support b).card = 2 /\
                      (S.support c \ S.support b).card = 3 then 1 else 0) := by
    by_cases hcb : c = b
    · subst c
      simp [hD]
    · obtain ⟨hinside, hsize, houtside⟩ :=
        elevenFive_c39_other_block_trace_bounds S b c hb hcb hcap
      have hsplit := Finset.card_inter_add_card_sdiff (S.support c) (S.support b)
      interval_cases hi : (S.support c ∩ S.support b).card <;>
        interval_cases ho : (S.support c \ S.support b).card <;>
        norm_num [Nat.choose, hi, ho] at * <;> omega
  have hsum :
      (∑ c : Block,
        Nat.choose (S.support c \ S.support b).card 3) =
        elevenFiveRelativeCount S (S.support b) 0 3 +
          4 * elevenFiveRelativeCount S (S.support b) 0 4 +
            10 * elevenFiveRelativeCount S (S.support b) 0 5 +
              elevenFiveRelativeCount S (S.support b) 1 3 +
                4 * elevenFiveRelativeCount S (S.support b) 1 4 +
                  elevenFiveRelativeCount S (S.support b) 2 3 := by
    calc
      (∑ c : Block,
        Nat.choose (S.support c \ S.support b).card 3) =
          ∑ c : Block, (
            (if (S.support c ∩ S.support b).card = 0 /\
                (S.support c \ S.support b).card = 3 then 1 else 0) +
              (if (S.support c ∩ S.support b).card = 0 /\
                  (S.support c \ S.support b).card = 4 then 4 else 0) +
                (if (S.support c ∩ S.support b).card = 0 /\
                    (S.support c \ S.support b).card = 5 then 10 else 0) +
                  (if (S.support c ∩ S.support b).card = 1 /\
                      (S.support c \ S.support b).card = 3 then 1 else 0) +
                    (if (S.support c ∩ S.support b).card = 1 /\
                        (S.support c \ S.support b).card = 4 then 4 else 0) +
                      (if (S.support c ∩ S.support b).card = 2 /\
                          (S.support c \ S.support b).card = 3 then 1 else 0)) := by
          apply Finset.sum_congr rfl
          intro c _hc
          exact hpoint c
      _ = _ := by
        simp only [Finset.sum_add_distrib]
        rw [elevenFive_sum_relative_indicator S (S.support b) 0 3 1,
          elevenFive_sum_relative_indicator S (S.support b) 0 4 4,
          elevenFive_sum_relative_indicator S (S.support b) 0 5 10,
          elevenFive_sum_relative_indicator S (S.support b) 1 3 1,
          elevenFive_sum_relative_indicator S (S.support b) 1 4 4,
          elevenFive_sum_relative_indicator S (S.support b) 2 3 1]
        simp
  exact hsum.symm.trans hraw

/-- In the C39 face every local three-degree is six or nine. -/
private theorem elevenFive_c39_three_degree_six_or_nine
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

/-- The C39 indicator records the previous two-valued degree row exactly. -/
private theorem elevenFive_c39_three_degree_indicator
    {Point : Type u} {Block : Type v} [Fintype Point] [Fintype Block]
    [DecidableEq Point]
    (S : BlockSystem Point Block) (p : Point)
    (hlocal : ElevenFiveLocalRows S p)
    (hC : S.totalCircleCount = 39) :
    S.blockDegree 3 p =
      6 + 3 * elevenFiveC39HighIndicator S p := by
  rcases elevenFive_c39_three_degree_six_or_nine S p hlocal hC with h | h
  · simp [elevenFiveC39HighIndicator, h]
  · simp [elevenFiveC39HighIndicator, h]

/-- The outsider-side degree sum, written as the literal `eX` count and the
three possible size-three relative fibres. -/
private theorem elevenFive_c39_high_outside_degree_row
    {Point : Type u} {Block : Type v} [Fintype Point] [Fintype Block]
    [DecidableEq Point]
    (S : BlockSystem Point Block) (b : Block)
    (hcard : Fintype.card Point = 11)
    (hb : b ∈ S.blocksOfSize 5) (hcap : BlockSizeCap S 5)
    (hlocal : ∀ p : Point, ElevenFiveLocalRows S p)
    (hC : S.totalCircleCount = 39) :
    36 + 3 * elevenFiveC39HighOutsideCount S (S.support b) =
      3 * elevenFiveRelativeCount S (S.support b) 0 3 +
        2 * elevenFiveRelativeCount S (S.support b) 1 2 +
          elevenFiveRelativeCount S (S.support b) 2 1 := by
  classical
  have hD : (S.support b).card = 5 := S.mem_blocksOfSize.mp hb
  have houtside : (Finset.univ \ S.support b).card = 6 := by
    simp [Finset.card_sdiff_of_subset (Finset.subset_univ (S.support b)),
      hcard, hD]
  have hlocalSum :
      (∑ p ∈ Finset.univ \ S.support b, S.blockDegree 3 p) =
        36 + 3 * elevenFiveC39HighOutsideCount S (S.support b) := by
    calc
      (∑ p ∈ Finset.univ \ S.support b, S.blockDegree 3 p) =
          ∑ p ∈ Finset.univ \ S.support b,
            (6 + 3 * elevenFiveC39HighIndicator S p) := by
        apply Finset.sum_congr rfl
        intro p _hp
        exact elevenFive_c39_three_degree_indicator S p (hlocal p) hC
      _ = 36 + 3 * elevenFiveC39HighOutsideCount S (S.support b) := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum]
        simp [houtside, elevenFiveC39HighOutsideCount]
  have hpoint (c : Block) :
      (if (S.support c).card = 3 then
          (S.support c \ S.support b).card else 0) =
        (if (S.support c ∩ S.support b).card = 0 /\
            (S.support c \ S.support b).card = 3 then 3 else 0) +
          (if (S.support c ∩ S.support b).card = 1 /\
              (S.support c \ S.support b).card = 2 then 2 else 0) +
            (if (S.support c ∩ S.support b).card = 2 /\
                (S.support c \ S.support b).card = 1 then 1 else 0) := by
    by_cases hcb : c = b
    · subst c
      simp [hD]
    · obtain ⟨hinside, hsize, houtside⟩ :=
        elevenFive_c39_other_block_trace_bounds S b c hb hcb hcap
      have hsplit := Finset.card_inter_add_card_sdiff (S.support c) (S.support b)
      have hcardSize : (S.support c).card =
          (S.support c ∩ S.support b).card +
            (S.support c \ S.support b).card := hsplit.symm
      by_cases hthree : (S.support c).card = 3
      · have hsum :
            (S.support c ∩ S.support b).card +
                (S.support c \ S.support b).card = 3 := by
            omega
        interval_cases hi : (S.support c ∩ S.support b).card
        · have ho : (S.support c \ S.support b).card = 3 := by omega
          simp [hthree, hi, ho]
        · have ho : (S.support c \ S.support b).card = 2 := by omega
          simp [hthree, hi, ho]
        · have ho : (S.support c \ S.support b).card = 1 := by omega
          simp [hthree, hi, ho]
      · have h03 : ¬ ((S.support c ∩ S.support b) = ∅ /\
            (S.support c \ S.support b).card = 3) := by
          rintro ⟨he, ho⟩
          apply hthree
          have hi : (S.support c ∩ S.support b).card = 0 :=
            Finset.card_eq_zero.mpr he
          omega
        have h12 : ¬ ((S.support c ∩ S.support b).card = 1 /\
            (S.support c \ S.support b).card = 2) := by
          rintro ⟨hi, ho⟩
          apply hthree
          omega
        have h21 : ¬ ((S.support c ∩ S.support b).card = 2 /\
            (S.support c \ S.support b).card = 1) := by
          rintro ⟨hi, ho⟩
          apply hthree
          omega
        simp [hthree, h03, h12, h21]
  have hblockDegree :
      (∑ p ∈ Finset.univ \ S.support b, S.blockDegree 3 p) =
        ∑ c : Block,
          if (S.support c).card = 3 then
            (S.support c \ S.support b).card else 0 := by
    have hraw := S.sum_degreeIn_over (S.blocksOfSize 3)
      (Finset.univ \ S.support b)
    change (∑ p ∈ Finset.univ \ S.support b, S.blockDegree 3 p) =
      ∑ c ∈ S.blocksOfSize 3,
        ((Finset.univ \ S.support b) ∩ S.support c).card at hraw
    have hintersection (c : Block) :
        (Finset.univ \ S.support b) ∩ S.support c =
          S.support c \ S.support b := by
      ext p
      simp [and_comm]
    simp_rw [hintersection] at hraw
    calc
      (∑ p ∈ Finset.univ \ S.support b, S.blockDegree 3 p) =
          ∑ c ∈ S.blocksOfSize 3,
            (S.support c \ S.support b).card := hraw
      _ = ∑ c : Block,
          if (S.support c).card = 3 then
            (S.support c \ S.support b).card else 0 := by
        simp only [BlockSystem.blocksOfSize, Finset.sum_filter]
  have hsumPoint :
      (∑ c : Block, (
        if (S.support c).card = 3 then
          (S.support c \ S.support b).card else 0)) =
        ∑ c : Block, (
          (if (S.support c ∩ S.support b).card = 0 /\
              (S.support c \ S.support b).card = 3 then 3 else 0) +
            (if (S.support c ∩ S.support b).card = 1 /\
                (S.support c \ S.support b).card = 2 then 2 else 0) +
              (if (S.support c ∩ S.support b).card = 2 /\
                  (S.support c \ S.support b).card = 1 then 1 else 0)) := by
    apply Finset.sum_congr rfl
    intro c _hc
    exact hpoint c
  have hsum :
      (∑ c : Block, (
        if (S.support c).card = 3 then
          (S.support c \ S.support b).card else 0)) =
        3 * elevenFiveRelativeCount S (S.support b) 0 3 +
          2 * elevenFiveRelativeCount S (S.support b) 1 2 +
            elevenFiveRelativeCount S (S.support b) 2 1 := by
    calc
      (∑ c : Block, (
        if (S.support c).card = 3 then
          (S.support c \ S.support b).card else 0)) =
          ∑ c : Block, (
            (if (S.support c ∩ S.support b).card = 0 /\
                (S.support c \ S.support b).card = 3 then 3 else 0) +
              (if (S.support c ∩ S.support b).card = 1 /\
                  (S.support c \ S.support b).card = 2 then 2 else 0) +
                (if (S.support c ∩ S.support b).card = 2 /\
                    (S.support c \ S.support b).card = 1 then 1 else 0)) := hsumPoint
      _ = (∑ c : Block,
          if (S.support c ∩ S.support b).card = 0 /\
              (S.support c \ S.support b).card = 3 then 3 else 0) +
          (∑ c : Block,
            if (S.support c ∩ S.support b).card = 1 /\
                (S.support c \ S.support b).card = 2 then 2 else 0) +
            (∑ c : Block,
              if (S.support c ∩ S.support b).card = 2 /\
                  (S.support c \ S.support b).card = 1 then 1 else 0) := by
        simp only [Finset.sum_add_distrib]
      _ = _ := by
        rw [elevenFive_sum_relative_indicator S (S.support b) 0 3 3,
          elevenFive_sum_relative_indicator S (S.support b) 1 2 2,
          elevenFive_sum_relative_indicator S (S.support b) 2 1 1]
        simp
  exact hlocalSum.symm.trans (hblockDegree.trans hsum)

/-- The formerly assumed rebased signed C39 front is a consequence of the
actual relative rows.  The premise is exactly the no-singleton condition
`A14 = 0`; no normalization or geometric callback is used. -/
theorem elevenFive_c39_rebased_signed_front_of_rows
    {Point : Type u} {Block : Type v} [Fintype Point] [Fintype Block]
    [DecidableEq Point]
    (S : BlockSystem Point Block) (hcard : Fintype.card Point = 11)
    (hcap : BlockSizeCap S 5)
    (hlocal : ∀ p : Point, ElevenFiveLocalRows S p)
    (hglobal : ElevenFiveGlobalRows S)
    (hC : S.totalCircleCount = 39)
    (hL : elevenFiveLineTotal S = 12)
    (b : Block) (hb : b ∈ S.circleBlocksOfSize 5) :
    elevenFiveRelativeCount S (S.support b) 1 4 = 0 →
      (elevenFiveRelativeCount S (S.support b) 1 2 : Int) =
          3 * (elevenFiveOutsideRichWeight S (S.support b) : Int) -
            (30 - elevenFiveHostWeight S (S.support b) : Nat) /\
        (elevenFiveC39HighOutsideCount S (S.support b) : Int) =
          3 - (30 - elevenFiveHostWeight S (S.support b) : Nat) -
            (elevenFiveOutsideRichWeight S (S.support b) : Int) +
              2 * (elevenFiveRelativeCount S (S.support b) 0 5 : Int) := by
  classical
  intro hzero
  have hsize : (S.support b).card = 5 :=
    (S.mem_blocksOfKindSize.mp hb).2
  have hblock : b ∈ S.blocksOfSize 5 := S.mem_blocksOfSize.mpr hsize
  have hweight := elevenFive_c39_relative_size_weight_row S b hblock hcap
  have hone := elevenFive_c39_relative_triple_one_row
    S b hcard hblock hcap
  have hzeroRow := elevenFive_c39_relative_triple_zero_row
    S b hcard hblock hcap
  have htwo :=
    elevenFive_relativeCount_two_one_add_two_mul_two_two_add_three_mul_two_three_eq_sixty
      S (S.support b) b hcard hsize hblock rfl hcap
  have hhigh := elevenFive_c39_high_outside_degree_row
    S b hcard hblock hcap hlocal hC
  have hhost :=
    elevenFiveHostWeight_eq_relativeCount22_add_three_mul_relativeCount23
      S (S.support b) hcap
  have hhostCap := elevenFiveHostWeight_le_thirty
    S (S.support b) hcard hsize
  have hglobalWeight : S.blockCount 4 + 3 * S.blockCount 5 = 38 := by
    have htriple := hglobal.tripleRow
    have htotal := hglobal.blockTotal
    rw [hC, hL] at htotal
    omega
  have hq :=
    elevenFiveOutsideRichWeight_eq_relativeCount_zero_four_add_three_mul_zero_five
      S (S.support b)
  constructor <;> omega

/-- In the C39,L12 maximum-host-at-most-27 face, the singleton conclusion is
now unconditional: its signed-front input has been discharged above. -/
theorem elevenFive_c39_l12_singleton_front_unconditional_of_rows
    {Point : Type u} {Block : Type v} [Fintype Point] [Fintype Block]
    [DecidableEq Point]
    (S : BlockSystem Point Block) (hcard : Fintype.card Point = 11)
    (hcap : BlockSizeCap S 5)
    (hlocal : ∀ p : Point, ElevenFiveLocalRows S p)
    (hglobal : ElevenFiveGlobalRows S)
    (hC : S.totalCircleCount = 39)
    (hL : elevenFiveLineTotal S = 12)
    (hcircle : ∀ b ∈ S.circleBlocksOfSize 5,
      elevenFiveHostWeight S (S.support b) ≤ 27)
    (b : Block) (hb : b ∈ S.circleBlocksOfSize 5) :
    S.blockCount 5 = 5 /\ S.lineCount 5 = 0 /\
      elevenFiveC39HighCount S = 1 /\
        ∃ c, c ∈ S.circleBlocksOfSize 5 /\
          (S.support c ∩ S.support b).card = 1 := by
  apply elevenFive_c39_l12_singleton_front_of_rebased_signed_front_of_rows
    S hcard hcap hlocal hglobal hC hL hcircle b hb
  exact elevenFive_c39_rebased_signed_front_of_rows
    S hcard hcap hlocal hglobal hC hL b hb

end Erdos506.V1
