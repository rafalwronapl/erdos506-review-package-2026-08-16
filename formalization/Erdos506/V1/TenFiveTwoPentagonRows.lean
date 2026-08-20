import Erdos506.V1.TenLocalParity

/-!
# Exact rows at the ten-point two-pentagon endpoint

The endpoint counts

* `B₃ = 20`,
* `B₄ = 20`, and
* `B₅ = 2`

already exhaust the global triple partition on ten points.  Consequently
there is no generalized block of size greater than five.  The local pair
row then gives `d₄ + 2 d₅ = 10` at every point.  Melchior nonnegativity and
the even-arrangement exclusion of restored slack one give
`l₃ + d₅ ≤ 4`; the global rows `L₃ = 10` and `B₅ = 2` force equality
pointwise.

This module is independent of the geometric meeting/disjoint split.
-/

namespace Erdos506.V1

open Erdos506.Block
open Erdos506.Block.BlockSystem
open Erdos506.Incidence
open Erdos506.V3
open Erdos506.V4
open scoped BigOperators

universe u v

/-- The three displayed block counts exhaust `choose(10,3)`, so every
nontrivial generalized block has size at most five. -/
theorem blockSizeCap_five_of_tenTwoPentagon_rows
    {Point : Type u} {Block : Type v} [Fintype Point] [Fintype Block]
    [DecidableEq Point]
    (S : BlockSystem Point Block) (hcard : Fintype.card Point = 10)
    (hB3 : S.blockCount 3 = 20)
    (hB4 : S.blockCount 4 = 20)
    (hB5 : S.blockCount 5 = 2) :
    BlockSizeCap S 5 := by
  classical
  have htriple := S.triple_partition_by_size
  rw [hcard] at htriple
  norm_num [Finset.sum_range_succ, Nat.choose, hB3, hB4, hB5] at htriple
  have hB6 : S.blockCount 6 = 0 := by omega
  have hB7 : S.blockCount 7 = 0 := by omega
  have hB8 : S.blockCount 8 = 0 := by omega
  have hB9 : S.blockCount 9 = 0 := by omega
  have hB10 : S.blockCount 10 = 0 := by omega
  intro b _hthree
  have hupper := S.support_card_le_point_card b
  rw [hcard] at hupper
  by_contra hnot
  have hlower : 6 ≤ (S.support b).card := by omega
  interval_cases hsize : (S.support b).card
  all_goals
    have hbmem : b ∈ S.blocksOfSize (S.support b).card :=
      S.mem_blocksOfSize.mpr rfl
    have hpositive : 0 < S.blockCount (S.support b).card := by
      exact Finset.card_pos.mpr ⟨b, hbmem⟩
    simp only [hsize] at hpositive
    omega

private theorem lineDegree_eq_zero_of_lineCount_eq_zero
    {Point : Type u} {Block : Type v} [Fintype Point] [Fintype Block]
    [DecidableEq Point]
    (S : BlockSystem Point Block) (s : Nat) (p : Point)
    (hzero : S.lineCount s = 0) :
    S.lineDegree s p = 0 := by
  change (S.lineBlocksOfSize s).card = 0 at hzero
  change ((S.lineBlocksOfSize s).filter
    (fun b => p ∈ S.support b)).card = 0
  have hcard := Finset.card_filter_le
    (S.lineBlocksOfSize s) (fun b => p ∈ S.support b)
  omega

/-- The two local inequalities needed in both branches of the
two-pentagon endpoint. -/
theorem tenTwoPentagon_point_cap
    {α : Type u} [Fintype α] [DecidableEq α]
    (Mel : RealPlaneMelchiorPrinciple.{u})
    (EvenArr : RealPlaneEvenArrangementPrinciple.{u})
    (cfg : Configuration α) (hadm : Admissible cfg)
    (hcard : Fintype.card α = 10)
    (hB3 : (blockSystem cfg).blockCount 3 = 20)
    (hB4 : (blockSystem cfg).blockCount 4 = 20)
    (hB5 : (blockSystem cfg).blockCount 5 = 2)
    (hL4 : (blockSystem cfg).lineCount 4 = 0)
    (hL5 : (blockSystem cfg).lineCount 5 = 0)
    (hd3 : ∀ p : α, (blockSystem cfg).blockDegree 3 p = 6)
    (p : α) :
    (blockSystem cfg).blockDegree 4 p +
          2 * (blockSystem cfg).blockDegree 5 p = 10 ∧
      (blockSystem cfg).lineDegree 3 p +
          (blockSystem cfg).blockDegree 5 p ≤ 4 := by
  classical
  let S := blockSystem cfg
  have hcap : BlockSizeCap S 5 :=
    blockSizeCap_five_of_tenTwoPentagon_rows S hcard hB3 hB4 hB5
  obtain ⟨hpairs, hkappaFormula⟩ :=
    ten_local_pair_and_kappa S hcard hcap p
  have hd3p : S.blockDegree 3 p = 6 := hd3 p
  have hpair : S.blockDegree 4 p + 2 * S.blockDegree 5 p = 10 := by
    omega
  have hd5le : S.blockDegree 5 p ≤ 2 := by
    exact (blockDegree_le_blockCount S 5 p).trans_eq hB5
  have hl4 : S.lineDegree 4 p = 0 :=
    lineDegree_eq_zero_of_lineCount_eq_zero S 4 p hL4
  have hl5 : S.lineDegree 5 p = 0 :=
    lineDegree_eq_zero_of_lineCount_eq_zero S 5 p hL5
  have hkappaNonneg : 0 ≤ S.restoredKappa p := by
    simpa [S] using
      kappa_nonneg_of_realPlaneMelchior Mel cfg hadm (by omega) p
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
  rw [hkappaFormula] at hkappaNonneg hkappaNe
  simp [tenLocalKappa, hd3p, hl4, hl5] at hkappaNonneg hkappaNe
  refine ⟨hpair, ?_⟩
  change S.lineDegree 3 p + S.blockDegree 5 p ≤ 4
  interval_cases hd5p : S.blockDegree 5 p <;> omega

/-- At the exact endpoint, the two local inequalities are equalities at
every point.  Saturation uses only `L₃ = 10`, `B₅ = 2`, and ten points. -/
theorem tenTwoPentagon_point_rows
    {α : Type u} [Fintype α] [DecidableEq α]
    (Mel : RealPlaneMelchiorPrinciple.{u})
    (EvenArr : RealPlaneEvenArrangementPrinciple.{u})
    (cfg : Configuration α) (hadm : Admissible cfg)
    (hcard : Fintype.card α = 10)
    (hB3 : (blockSystem cfg).blockCount 3 = 20)
    (hB4 : (blockSystem cfg).blockCount 4 = 20)
    (hB5 : (blockSystem cfg).blockCount 5 = 2)
    (hL3 : (blockSystem cfg).lineCount 3 = 10)
    (hL4 : (blockSystem cfg).lineCount 4 = 0)
    (hL5 : (blockSystem cfg).lineCount 5 = 0)
    (hd3 : ∀ p : α, (blockSystem cfg).blockDegree 3 p = 6)
    (p : α) :
    (blockSystem cfg).blockDegree 4 p +
          2 * (blockSystem cfg).blockDegree 5 p = 10 ∧
      (blockSystem cfg).lineDegree 3 p +
          (blockSystem cfg).blockDegree 5 p = 4 := by
  classical
  let S := blockSystem cfg
  have hpoint (q : α) :
      S.blockDegree 4 q + 2 * S.blockDegree 5 q = 10 ∧
        S.lineDegree 3 q + S.blockDegree 5 q ≤ 4 :=
    tenTwoPentagon_point_cap Mel EvenArr cfg hadm hcard
      hB3 hB4 hB5 hL4 hL5 hd3 q
  have hlineIncidence := S.line_incidence 3
  have hblockIncidence := S.block_incidence 5
  rw [hL3] at hlineIncidence
  rw [hB5] at hblockIncidence
  norm_num at hlineIncidence hblockIncidence
  have hsum :
      (∑ q : α, (S.lineDegree 3 q + S.blockDegree 5 q)) = 40 := by
    rw [Finset.sum_add_distrib, hlineIncidence, hblockIncidence]
  have hsumFour : (∑ _q : α, 4) = 40 := by simp [hcard]
  have hexact (q : α) : S.lineDegree 3 q + S.blockDegree 5 q = 4 :=
    (Finset.sum_eq_sum_iff_of_le
      (fun r (_hr : r ∈ (Finset.univ : Finset α)) => (hpoint r).2)).mp
        (hsum.trans hsumFour.symm) q (Finset.mem_univ q)
  exact ⟨(hpoint p).1, hexact p⟩

end Erdos506.V1
