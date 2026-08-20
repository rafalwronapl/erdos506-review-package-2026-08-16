import Erdos506.V1.Eight
import Erdos506.Incidence.OrdinaryPrinciples
import Erdos506.V1.FiniteCaps
import Erdos506.V1.TenLocalTable
import Erdos506.V1.UniversalRows

/-!
# Configuration wrapper for the ten-point local table

This module derives the pair row and the restored-centre formula from a
five-block cap, and transfers Melchior plus the explicit even-arrangement
principle to the arithmetic table in `TenLocalTable`.

One hypothesis remains deliberately visible: `blockDegree 3 p <= 11`.  In
the manuscript it is the deletion bound `circleDegree 3 p <= C - f(9)` plus
the four-ray bound.  Keeping it explicit identifies the exact missing
deletion adapter instead of hiding it in the local arithmetic.
-/

namespace Erdos506.V1

open Erdos506.Block
open Erdos506.Block.BlockSystem
open Erdos506.Incidence
open Erdos506.V3
open Erdos506.V4

universe u

private theorem tenParity_blockCount_eq_zero_of_cap
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

private theorem tenParity_lineCount_eq_zero_of_cap
    {Point Block : Type*} [Fintype Point] [Fintype Block]
    [DecidableEq Point]
    (S : BlockSystem Point Block) {s : Nat}
    (hcap : BlockSizeCap S 5) (hs : 5 < s) : S.lineCount s = 0 := by
  classical
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro b hb
  have hsize := S.mem_blocksOfKindSize.mp hb
  have hle := hcap b (by omega)
  omega

private theorem tenParity_blockDegree_eq_zero
    {Point Block : Type*} [Fintype Point] [Fintype Block]
    [DecidableEq Point]
    (S : BlockSystem Point Block) (s : Nat) (p : Point)
    (hzero : S.blockCount s = 0) : S.blockDegree s p = 0 := by
  have hinc := S.block_incidence s
  rw [hzero] at hinc
  have hle : S.blockDegree s p <= ∑ q : Point, S.blockDegree s q := by
    exact Finset.single_le_sum
      (fun q _hq => Nat.zero_le (S.blockDegree s q)) (Finset.mem_univ p)
  omega

private theorem tenParity_lineDegree_eq_zero
    {Point Block : Type*} [Fintype Point] [Fintype Block]
    [DecidableEq Point]
    (S : BlockSystem Point Block) (s : Nat) (p : Point)
    (hzero : S.lineCount s = 0) : S.lineDegree s p = 0 := by
  have hinc := S.line_incidence s
  rw [hzero] at hinc
  have hle : S.lineDegree s p <= ∑ q : Point, S.lineDegree s q := by
    exact Finset.single_le_sum
      (fun q _hq => Nat.zero_le (S.lineDegree s q)) (Finset.mem_univ p)
  omega

/-- Under a five-block cap, the ten-point pair row and restored-centre
expression reduce exactly to the five local degrees used by the table. -/
theorem ten_local_pair_and_kappa
    {Point Block : Type*} [Fintype Point] [Fintype Block]
    [DecidableEq Point]
    (S : BlockSystem Point Block) (hcard : Fintype.card Point = 10)
    (hcap : BlockSizeCap S 5) (p : Point) :
    S.blockDegree 3 p + 3 * S.blockDegree 4 p +
        6 * S.blockDegree 5 p = 36 ∧
      S.restoredKappa p =
        tenLocalKappa (S.blockDegree 3 p) (S.blockDegree 5 p)
          (S.lineDegree 3 p) (S.lineDegree 4 p) (S.lineDegree 5 p) := by
  have hb6 := tenParity_blockCount_eq_zero_of_cap S hcap (s := 6) (by omega)
  have hb7 := tenParity_blockCount_eq_zero_of_cap S hcap (s := 7) (by omega)
  have hb8 := tenParity_blockCount_eq_zero_of_cap S hcap (s := 8) (by omega)
  have hb9 := tenParity_blockCount_eq_zero_of_cap S hcap (s := 9) (by omega)
  have hb10 := tenParity_blockCount_eq_zero_of_cap S hcap (s := 10) (by omega)
  have hl6 := tenParity_lineCount_eq_zero_of_cap S hcap (s := 6) (by omega)
  have hl7 := tenParity_lineCount_eq_zero_of_cap S hcap (s := 7) (by omega)
  have hl8 := tenParity_lineCount_eq_zero_of_cap S hcap (s := 8) (by omega)
  have hl9 := tenParity_lineCount_eq_zero_of_cap S hcap (s := 9) (by omega)
  have hl10 := tenParity_lineCount_eq_zero_of_cap S hcap (s := 10) (by omega)
  have hd6 := tenParity_blockDegree_eq_zero S 6 p hb6
  have hd7 := tenParity_blockDegree_eq_zero S 7 p hb7
  have hd8 := tenParity_blockDegree_eq_zero S 8 p hb8
  have hd9 := tenParity_blockDegree_eq_zero S 9 p hb9
  have hd10 := tenParity_blockDegree_eq_zero S 10 p hb10
  have hld6 := tenParity_lineDegree_eq_zero S 6 p hl6
  have hld7 := tenParity_lineDegree_eq_zero S 7 p hl7
  have hld8 := tenParity_lineDegree_eq_zero S 8 p hl8
  have hld9 := tenParity_lineDegree_eq_zero S 9 p hl9
  have hld10 := tenParity_lineDegree_eq_zero S 10 p hl10
  have hpairs := S.pivot_pair_partition p
  rw [hcard] at hpairs
  norm_num [Finset.sum_range_succ, Nat.choose,
    hd6, hd7, hd8, hd9, hd10] at hpairs
  have hsigma :
      S.pivotSigma p =
        (S.blockDegree 3 p : Int) - (S.blockDegree 5 p : Int) - 3 := by
    unfold BlockSystem.pivotSigma BlockSystem.nontrivialSizes
    rw [hcard]
    have hIcc : Finset.Icc 3 10 = {3, 4, 5, 6, 7, 8, 9, 10} := by decide
    rw [hIcc]
    norm_num [hd6, hd7, hd8, hd9, hd10]
    ring
  have hkappa :
      S.restoredKappa p =
        9 + S.pivotSigma p - 3 * (S.lineDegree 3 p : Int) -
          4 * (S.lineDegree 4 p : Int) -
          5 * (S.lineDegree 5 p : Int) := by
    unfold BlockSystem.restoredKappa BlockSystem.nontrivialSizes
    rw [hcard]
    have hIcc : Finset.Icc 3 10 = {3, 4, 5, 6, 7, 8, 9, 10} := by decide
    rw [hIcc]
    norm_num [hld6, hld7, hld8, hld9, hld10]
    ring
  constructor
  · exact hpairs
  · rw [hkappa, hsigma]
    unfold tenLocalKappa
    ring

/-- A local degree is bounded by the corresponding global block count. -/
theorem blockDegree_le_blockCount
    {Point Block : Type*} [Fintype Point] [Fintype Block]
    [DecidableEq Point]
    (S : BlockSystem Point Block) (s : Nat) (p : Point) :
    S.blockDegree s p <= S.blockCount s := by
  unfold BlockSystem.blockDegree BlockSystem.blockCount BlockSystem.degreeIn
  exact Finset.card_filter_le _ _

/-- The four-ray bound at a ten-point pivot follows directly from the line
arm partition. -/
theorem ten_lineDegree_three_le_four
    {Point Block : Type*} [Fintype Point] [Fintype Block]
    [DecidableEq Point]
    (S : BlockSystem Point Block) (hcard : Fintype.card Point = 10)
    (p : Point) : S.lineDegree 3 p <= 4 := by
  have harms := S.line_arms p
  have hterm :
      (3 - 1) * S.lineDegree 3 p <=
        ∑ s ∈ Finset.range (Fintype.card Point + 1),
          (s - 1) * S.lineDegree s p := by
    exact Finset.single_le_sum
      (fun s _hs => Nat.zero_le ((s - 1) * S.lineDegree s p))
      (by simp [hcard])
  rw [harms, hcard] at hterm
  norm_num at hterm
  omega

/-- Under the ten-point contradiction bound, a circle cap of five and the
rich-line pencil give a five-cap on every nontrivial geometric block. -/
theorem blockSizeCap_five_of_card_ten_of_circleCount_le_of_circle_cap_five
    {α : Type u} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (hadm : Admissible cfg)
    (hcard : Fintype.card α = 10)
    (hcount : Erdos506.V4.circleCount cfg <= 32)
    (hcircle : ∀ c : DeterminedCircle cfg,
      (circleTrace cfg c.1).card <= 5) :
    BlockSizeCap (blockSystem cfg) 5 := by
  intro b _hthree
  cases b with
  | inl L =>
      simpa [blockSystem, geometricBlockSupport] using
        lineSupport_card_le_five_of_ten_of_circleCount_le
          cfg hadm hcard hcount L
  | inr c =>
      exact hcircle c

/-- Configuration-level transfer to the exact local table.

The explicit `hdegree3Upper` is the sole deletion bridge still missing from
this module.  The global `hB5` hypothesis supplies `r <= 3`. -/
theorem ten_local_line3_table_of_geometry
    {α : Type u} [Fintype α] [DecidableEq α]
    (Mel : RealPlaneMelchiorPrinciple.{u})
    (EvenArr : RealPlaneEvenArrangementPrinciple.{u})
    (Kelly : RealPlaneKellyMoserPrinciple.{u})
    (cfg : Configuration α) (hadm : Admissible cfg)
    (hcard : Fintype.card α = 10)
    (hcap : BlockSizeCap (blockSystem cfg) 5)
    (hB5 : (blockSystem cfg).blockCount 5 <= 3)
    (p : α) (hdegree3Upper : (blockSystem cfg).blockDegree 3 p <= 11)
    (hline5 : (blockSystem cfg).lineDegree 5 p = 0) :
    let S := blockSystem cfg
    (S.blockDegree 3 p = 6 ∨ S.blockDegree 3 p = 9) ∧
      tenLocalStateAllowed (S.blockDegree 3 p) (S.lineDegree 4 p)
        (S.blockDegree 5 p) ∧
      S.lineDegree 3 p <=
        tenLocalLine3Cap (S.blockDegree 3 p) (S.lineDegree 4 p)
          (S.blockDegree 5 p) := by
  classical
  dsimp only
  let S := blockSystem cfg
  obtain ⟨hpairs, hkappaFormula⟩ :=
    ten_local_pair_and_kappa S hcard hcap p
  have hKM := Kelly.pivot_three_block_bound cfg hadm
    (by omega) (by omega) p
  rw [hcard] at hKM
  norm_num at hKM
  change 27 <= 7 * S.blockDegree 3 p at hKM
  have hd3 : S.blockDegree 3 p = 6 ∨ S.blockDegree 3 p = 9 :=
    ten_local_pair_d3_eq_six_or_nine hpairs hKM hdegree3Upper
  have hr : S.blockDegree 5 p <= 3 :=
    (blockDegree_le_blockCount S 5 p).trans hB5
  have hkappaNonneg : 0 <= S.restoredKappa p := by
    simpa [S] using kappa_nonneg_of_realPlaneMelchior
      Mel cfg hadm (by omega) p
  have hrestCard : Fintype.card (Option (AwayFrom p)) = 10 := by
    simp [hcard]
  have heven : Even (Fintype.card (Option (AwayFrom p))) := by
    rw [hrestCard]
    norm_num
  have hrestNoncol : Noncollinear (restoredPivotConfiguration cfg p) :=
    restoredPivotConfiguration_noncollinear cfg hadm (by omega) p
  have hkappaNe : S.restoredKappa p ≠ 1 := by
    have hne := EvenArr.slack_ne_one
      (restoredPivotConfiguration cfg p) hrestNoncol heven
    rw [← restoredKappa_eq_lineMelchiorSlack cfg p] at hne
    simpa [S] using hne
  have hq : S.lineDegree 4 p <= 3 := by
    rw [hkappaFormula] at hkappaNonneg
    rcases hd3 with hd3 | hd3 <;>
      simp [tenLocalKappa, hd3] at hkappaNonneg <;> omega
  have hl3 := ten_lineDegree_three_le_four S hcard p
  have hkappaLocal :
      0 <= tenLocalKappa (S.blockDegree 3 p) (S.blockDegree 5 p)
        (S.lineDegree 3 p) (S.lineDegree 4 p) 0 := by
    rw [← hline5, ← hkappaFormula]
    exact hkappaNonneg
  have hkappaLocalNe :
      tenLocalKappa (S.blockDegree 3 p) (S.blockDegree 5 p)
        (S.lineDegree 3 p) (S.lineDegree 4 p) 0 ≠ 1 := by
    rw [← hline5, ← hkappaFormula]
    exact hkappaNe
  obtain ⟨hallowed, hlineCap⟩ := ten_local_line3_table
    hd3 hr hq hl3 hkappaLocal hkappaLocalNe
  exact ⟨hd3, hallowed, hlineCap⟩

end Erdos506.V1
