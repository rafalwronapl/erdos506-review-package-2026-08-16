import Erdos506.V1.TenFiveScalar
import Erdos506.V1.TenLocalParity

/-!
# Materializing the ten-point selected-five scalar rows

This file connects the abstract scalar router to a concrete `BlockSystem`.
The only inputs not proved here are the already isolated local dichotomy
`d3(p) = 6 or 9` and the geometric five-block cap `1 <= B5 <= 3`.
-/

namespace Erdos506.V1

open Erdos506.Block
open Erdos506.Block.BlockSystem
open Erdos506.Incidence
open Erdos506.V4
open scoped BigOperators

universe u

/-- Points having the high local three-block degree nine. -/
noncomputable def tenHighPoints
    {Point Block : Type*} [Fintype Point] [Fintype Block]
    [DecidableEq Point]
    (S : BlockSystem Point Block) : Finset Point := by
  classical
  exact Finset.univ.filter fun p => S.blockDegree 3 p = 9

@[simp] theorem mem_tenHighPoints
    {Point Block : Type*} [Fintype Point] [Fintype Block]
    [DecidableEq Point]
    {S : BlockSystem Point Block} {p : Point} :
    p ∈ tenHighPoints S ↔ S.blockDegree 3 p = 9 := by
  classical
  simp [tenHighPoints]

/-- Summing the pointwise dichotomy gives the manuscript's
`B3 = 20 + alpha` identity. -/
theorem blockCount_three_eq_twenty_add_tenHighPoints
    {Point Block : Type*} [Fintype Point] [Fintype Block]
    [DecidableEq Point]
    (S : BlockSystem Point Block) (hcard : Fintype.card Point = 10)
    (hd3 : ∀ p : Point, S.blockDegree 3 p = 6 ∨
      S.blockDegree 3 p = 9) :
    S.blockCount 3 = 20 + (tenHighPoints S).card := by
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
        (tenHighPoints S).card := by
    simp [tenHighPoints]
  have hmul : S.blockCount 3 * 3 =
      (20 + (tenHighPoints S).card) * 3 := by
    calc
      S.blockCount 3 * 3 = ∑ p : Point, S.blockDegree 3 p := by
        simpa [Nat.mul_comm] using hsum.symm
      _ = ∑ p : Point,
          (6 + 3 * (if S.blockDegree 3 p = 9 then 1 else 0)) := by
        apply Finset.sum_congr rfl
        intro p _hp
        exact hpoint p
      _ = 60 + 3 * (tenHighPoints S).card := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, hindicator]
        simp [hcard]
      _ = (20 + (tenHighPoints S).card) * 3 := by ring
  omega

private theorem tenFive_blockCount_eq_zero_of_cap
    {Point Block : Type*} [Fintype Point] [Fintype Block]
    [DecidableEq Point]
    (S : BlockSystem Point Block) {s : Nat}
    (hcap : BlockSizeCap S 5) (hs : 5 < s) : S.blockCount s = 0 := by
  classical
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro b hb
  have hsize := S.mem_blocksOfSize.mp hb
  have hle := hcap b (by omega)
  omega

/-- Under a five-cap, the defect row has only the five displayed terms. -/
theorem ten_defectRow_eq_under_block_cap_five
    {Point Block : Type*} [Fintype Point] [Fintype Block]
    [DecidableEq Point]
    (S : BlockSystem Point Block) (hcard : Fintype.card Point = 10)
    (hcap : BlockSizeCap S 5) :
    S.defectRow = -3 * (S.circleCount 3 : Int) +
      5 * (S.circleCount 5 : Int) +
      6 * (S.lineCount 3 : Int) + 16 * (S.lineCount 4 : Int) +
      30 * (S.lineCount 5 : Int) := by
  have hb6 := tenFive_blockCount_eq_zero_of_cap S hcap (s := 6) (by omega)
  have hb7 := tenFive_blockCount_eq_zero_of_cap S hcap (s := 7) (by omega)
  have hb8 := tenFive_blockCount_eq_zero_of_cap S hcap (s := 8) (by omega)
  have hb9 := tenFive_blockCount_eq_zero_of_cap S hcap (s := 9) (by omega)
  have hb10 := tenFive_blockCount_eq_zero_of_cap S hcap (s := 10) (by omega)
  have hs6 := S.blockCount_eq_lineCount_add_circleCount 6
  have hs7 := S.blockCount_eq_lineCount_add_circleCount 7
  have hs8 := S.blockCount_eq_lineCount_add_circleCount 8
  have hs9 := S.blockCount_eq_lineCount_add_circleCount 9
  have hs10 := S.blockCount_eq_lineCount_add_circleCount 10
  have hl6 : S.lineCount 6 = 0 := by omega
  have hl7 : S.lineCount 7 = 0 := by omega
  have hl8 : S.lineCount 8 = 0 := by omega
  have hl9 : S.lineCount 9 = 0 := by omega
  have hl10 : S.lineCount 10 = 0 := by omega
  have hc6 : S.circleCount 6 = 0 := by omega
  have hc7 : S.circleCount 7 = 0 := by omega
  have hc8 : S.circleCount 8 = 0 := by omega
  have hc9 : S.circleCount 9 = 0 := by omega
  have hc10 : S.circleCount 10 = 0 := by omega
  unfold BlockSystem.defectRow BlockSystem.nontrivialSizes
  rw [hcard]
  have hIcc : Finset.Icc 3 10 = {3, 4, 5, 6, 7, 8, 9, 10} := by decide
  rw [hIcc]
  norm_num [hc6, hc7, hc8, hc9, hc10,
    hl6, hl7, hl8, hl9, hl10]
  ring

/-- The concrete block rows produce exactly `TenFiveScalarConditions`.

The Melchior input is used only for `defectRow <= 60`; all other fields are
exact ownership/counting identities. -/
theorem tenFiveScalarConditions_of_blockSystem
    {α : Type u} [Fintype α] [DecidableEq α]
    (Mel : RealPlaneMelchiorPrinciple.{u})
    (cfg : Configuration α) (hadm : Admissible cfg)
    (hcard : Fintype.card α = 10)
    (hcap : BlockSizeCap (blockSystem cfg) 5)
    (hB5Lower : 1 <= (blockSystem cfg).blockCount 5)
    (hB5Upper : (blockSystem cfg).blockCount 5 <= 3)
    (hd3 : ∀ p : α, (blockSystem cfg).blockDegree 3 p = 6 ∨
      (blockSystem cfg).blockDegree 3 p = 9) :
    let S := blockSystem cfg
    TenFiveScalarConditions S.totalCircleCount (S.blockCount 5)
      (S.blockCount 3) (S.blockCount 4) (tenHighPoints S).card
      (S.lineCount 3 + S.lineCount 4 + S.lineCount 5)
      (S.lineCount 4) (S.lineCount 5) := by
  classical
  dsimp only
  let S := blockSystem cfg
  have hb6 := tenFive_blockCount_eq_zero_of_cap S hcap (s := 6) (by omega)
  have hb7 := tenFive_blockCount_eq_zero_of_cap S hcap (s := 7) (by omega)
  have hb8 := tenFive_blockCount_eq_zero_of_cap S hcap (s := 8) (by omega)
  have hb9 := tenFive_blockCount_eq_zero_of_cap S hcap (s := 9) (by omega)
  have hb10 := tenFive_blockCount_eq_zero_of_cap S hcap (s := 10) (by omega)
  have hs6 := S.blockCount_eq_lineCount_add_circleCount 6
  have hs7 := S.blockCount_eq_lineCount_add_circleCount 7
  have hs8 := S.blockCount_eq_lineCount_add_circleCount 8
  have hs9 := S.blockCount_eq_lineCount_add_circleCount 9
  have hs10 := S.blockCount_eq_lineCount_add_circleCount 10
  have hl6 : S.lineCount 6 = 0 := by omega
  have hl7 : S.lineCount 7 = 0 := by omega
  have hl8 : S.lineCount 8 = 0 := by omega
  have hl9 : S.lineCount 9 = 0 := by omega
  have hl10 : S.lineCount 10 = 0 := by omega
  have hc6 : S.circleCount 6 = 0 := by omega
  have hc7 : S.circleCount 7 = 0 := by omega
  have hc8 : S.circleCount 8 = 0 := by omega
  have hc9 : S.circleCount 9 = 0 := by omega
  have hc10 : S.circleCount 10 = 0 := by omega
  have hc0 : S.circleCount 0 = 0 := S.circleCount_eq_zero_of_lt_three (by omega)
  have hc1 : S.circleCount 1 = 0 := S.circleCount_eq_zero_of_lt_three (by omega)
  have hc2 : S.circleCount 2 = 0 := S.circleCount_eq_zero_of_lt_three (by omega)
  have htriple := S.triple_partition_by_size
  rw [hcard] at htriple
  norm_num [Finset.sum_range_succ, Nat.choose,
    hb6, hb7, hb8, hb9, hb10] at htriple
  have hsplit3 := S.blockCount_eq_lineCount_add_circleCount 3
  have hsplit4 := S.blockCount_eq_lineCount_add_circleCount 4
  have hsplit5 := S.blockCount_eq_lineCount_add_circleCount 5
  have htotal := S.totalCircleCount_eq_sum_circleCount
  rw [hcard] at htotal
  norm_num [Finset.sum_range_succ, hc0, hc1, hc2,
    hc6, hc7, hc8, hc9, hc10] at htotal
  have hhigh := blockCount_three_eq_twenty_add_tenHighPoints
    S hcard hd3
  have htripleInt :
      (S.blockCount 3 : Int) + 4 * S.blockCount 4 +
        10 * S.blockCount 5 = 120 := by exact_mod_cast htriple
  have hsplit3Int :
      (S.blockCount 3 : Int) =
        S.lineCount 3 + S.circleCount 3 := by exact_mod_cast hsplit3
  have hsplit4Int :
      (S.blockCount 4 : Int) =
        S.lineCount 4 + S.circleCount 4 := by exact_mod_cast hsplit4
  have hsplit5Int :
      (S.blockCount 5 : Int) =
        S.lineCount 5 + S.circleCount 5 := by exact_mod_cast hsplit5
  have htotalInt :
      (S.totalCircleCount : Int) =
        S.circleCount 3 + S.circleCount 4 + S.circleCount 5 := by
    exact_mod_cast htotal
  have hhighInt :
      (S.blockCount 3 : Int) =
        20 + (tenHighPoints S).card := by exact_mod_cast hhigh
  have hlineEquation :
      (4 : Int) * (S.lineCount 3 + S.lineCount 4 + S.lineCount 5) =
        180 - 4 * S.totalCircleCount +
          3 * (tenHighPoints S).card - 6 * S.blockCount 5 := by
    omega
  have hdefect := ten_defectRow_eq_under_block_cap_five S hcard hcap
  have hD := rowD_le_n_mul_n_sub_four_of_realPlaneMelchior
    Mel cfg hadm (by omega)
  change S.defectRow <= (Fintype.card α : Int) *
    ((Fintype.card α : Int) - 4) at hD
  rw [hdefect, hcard] at hD
  have hAC :
      15 * ((tenHighPoints S).card : Int) -
          34 * (S.blockCount 5 : Int) +
          28 * (S.lineCount 4 : Int) +
          64 * (S.lineCount 5 : Int) <=
        36 * (S.totalCircleCount : Int) - 1140 := by
    omega
  refine ⟨hB5Lower, hB5Upper, hhigh, htriple, ?_, hAC, ?_, ?_⟩
  · exact hlineEquation
  · have hle := Finset.card_le_card
      (Finset.subset_univ (tenHighPoints S))
    simpa [hcard] using hle
  · omega

end Erdos506.V1
