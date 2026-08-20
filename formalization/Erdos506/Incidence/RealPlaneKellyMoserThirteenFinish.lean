import Erdos506.Incidence.RealProjectiveArrangementWeakKellyFinish

/-!
# The thirteen-point Kelly--Moser endpoint

The weak attachment count gives five ordinary lines at thirteen points.
Melchior and the pair row leave a unique equality profile below six:
`(L_2,L_3,L_5)=(5,21,1)`.  Every label then has even ordinary degree, so
at least eight arrangement lines have ordinary degree zero.  Their three
attachments each exceed the global four-per-ordinary-vertex capacity.
-/

namespace Erdos506.Incidence

open Erdos506.Block
open Erdos506.Block.BlockSystem
open Erdos506.V1
open Erdos506.V3
open Erdos506.V4
open scoped BigOperators

universe u

private theorem thirteen_globalLineRow_eq_weighted_lineCount
    {Point Block : Type*} [Fintype Point] [Fintype Block]
    [DecidableEq Point] (S : BlockSystem Point Block) :
    S.globalLineRow =
      ∑ s ∈ Finset.range (Fintype.card Point + 1),
        ((if 3 ≤ s then Nat.choose s 2 + s - 3 else 0 : ℕ) : ℤ) *
          (S.lineCount s : ℤ) := by
  classical
  let w : ℕ → ℕ := fun s =>
    if 3 ≤ s then Nat.choose s 2 + s - 3 else 0
  have hgroup := S.sum_kindCount_weight .line w
  have hsubtype :
      (∑ b : LineBlock S, w (S.support b.1).card) =
        ∑ b ∈ S.blocksOfKind .line, w (S.support b).card := by
    symm
    simpa [blocksOfKind] using
      (Finset.sum_subtype (S.blocksOfKind .line)
        (fun b => by simp [blocksOfKind])
        (fun b => w (S.support b).card))
  have hpoint (b : LineBlock S) :
      (if 3 ≤ (S.support b.1).card then
          (Nat.choose (S.support b.1).card 2 : ℤ) +
            ((S.support b.1).card : ℤ) - 3
        else 0) = (w (S.support b.1).card : ℤ) := by
    dsimp only [w]
    split_ifs with hthree
    · omega
    · rfl
  have hglobal :
      S.globalLineRow =
        ((∑ b ∈ S.blocksOfKind .line,
          w (S.support b).card : ℕ) : ℤ) := by
    unfold BlockSystem.globalLineRow
    calc
      (∑ b : LineBlock S,
          if 3 ≤ (S.support b.1).card then
            (Nat.choose (S.support b.1).card 2 : ℤ) +
              ((S.support b.1).card : ℤ) - 3
          else 0) =
          ∑ b : LineBlock S, (w (S.support b.1).card : ℤ) := by
            apply Fintype.sum_congr
            exact hpoint
      _ = ((∑ b : LineBlock S, w (S.support b.1).card : ℕ) : ℤ) := by
            norm_num
      _ = ((∑ b ∈ S.blocksOfKind .line,
          w (S.support b).card : ℕ) : ℤ) := by rw [hsubtype]
  rw [hglobal, ← hgroup]
  norm_num [w, BlockSystem.lineCount]

private theorem thirteen_lineDegree_le_lineCount
    {Point Block : Type*} [Fintype Point] [Fintype Block]
    [DecidableEq Point] (S : BlockSystem Point Block)
    (s : ℕ) (p : Point) : S.lineDegree s p ≤ S.lineCount s := by
  unfold BlockSystem.lineDegree BlockSystem.degreeIn BlockSystem.lineCount
  exact Finset.card_filter_le _ _

private theorem thirteen_lineDegree_eq_zero_of_lineCount_eq_zero
    {Point Block : Type*} [Fintype Point] [Fintype Block]
    [DecidableEq Point] (S : BlockSystem Point Block)
    (s : ℕ) (p : Point) (hzero : S.lineCount s = 0) :
    S.lineDegree s p = 0 := by
  have hle := thirteen_lineDegree_le_lineCount S s p
  omega

/-- Thirteen noncollinear real points determine at least six ordinary
lines.  This closes the one integral gap left by the universal weak count. -/
theorem six_le_lineCount_two_of_card_thirteen
    {alpha : Type u} [Fintype alpha] [DecidableEq alpha]
    (Mel : RealPlaneMelchiorPrinciple.{u})
    (cfg : Configuration alpha) (hnon : Noncollinear cfg)
    (hcard : Fintype.card alpha = 13) :
    6 ≤ (blockSystem cfg).lineCount 2 := by
  classical
  let S := blockSystem cfg
  let A := labelDualArrangement cfg
  have hA : A.NonPencil := by
    simpa [A] using labelDualArrangement_nonPencil_of_noncollinear cfg hnon
  by_cases hlow : ∃ l : alpha, (A.lineVertexSet l).card ≤ 2
  · obtain ⟨l, hl⟩ := hlow
    have hstrong :=
      A.three_mul_card_le_seven_mul_card_ordinaryVertex_of_lineVertexSet_card_le_two
        hA (by rw [hcard]; omega) l hl
    change 3 * Fintype.card alpha ≤
      7 * Fintype.card (labelDualArrangement cfg).OrdinaryVertex at hstrong
    rw [hcard, ← lineCount_two_eq_card_labelDualOrdinaryVertex cfg] at hstrong
    omega
  have hhigh (l : alpha) : 3 ≤ (A.lineVertexSet l).card := by
    by_contra hthree
    exact hlow ⟨l, by omega⟩
  have hweak :=
    A.three_mul_card_le_eight_mul_card_ordinaryVertex_of_highLines hA hhigh
  change 3 * Fintype.card alpha ≤
    8 * Fintype.card (labelDualArrangement cfg).OrdinaryVertex at hweak
  rw [hcard, ← lineCount_two_eq_card_labelDualOrdinaryVertex cfg] at hweak
  by_contra hsix
  have htwo : S.lineCount 2 = 5 := by omega
  have hpair := S.line_pair_partition_by_size
  rw [hcard] at hpair
  norm_num [Finset.sum_range_succ, Nat.choose] at hpair
  have hGform : S.globalLineRow =
      3 * (S.lineCount 3 : ℤ) + 7 * (S.lineCount 4 : ℤ) +
      12 * (S.lineCount 5 : ℤ) + 18 * (S.lineCount 6 : ℤ) +
      25 * (S.lineCount 7 : ℤ) + 33 * (S.lineCount 8 : ℤ) +
      42 * (S.lineCount 9 : ℤ) + 52 * (S.lineCount 10 : ℤ) +
      63 * (S.lineCount 11 : ℤ) + 75 * (S.lineCount 12 : ℤ) +
      88 * (S.lineCount 13 : ℤ) := by
    rw [thirteen_globalLineRow_eq_weighted_lineCount, hcard]
    norm_num [Finset.sum_range_succ, Nat.choose]
  have hmel : LineMelchior cfg := Mel.lineMelchior cfg hnon
  have hslack : 0 ≤ S.globalLineSlack := by
    simpa [S] using globalLineSlack_nonneg_of_lineMelchior cfg hmel
  rw [← S.choose_two_sub_three_sub_globalLineRow_eq_globalLineSlack,
    hcard, hGform] at hslack
  norm_num [Nat.choose] at hslack
  have hl4 : S.lineCount 4 = 0 := by omega
  have hl5 : S.lineCount 5 = 1 := by omega
  have hl6 : S.lineCount 6 = 0 := by omega
  have hl7 : S.lineCount 7 = 0 := by omega
  have hl8 : S.lineCount 8 = 0 := by omega
  have hl9 : S.lineCount 9 = 0 := by omega
  have hl10 : S.lineCount 10 = 0 := by omega
  have hl11 : S.lineCount 11 = 0 := by omega
  have hl12 : S.lineCount 12 = 0 := by omega
  have hl13 : S.lineCount 13 = 0 := by omega
  have hpositiveTwo (p : alpha) (hp : S.lineDegree 2 p ≠ 0) :
      2 ≤ S.lineDegree 2 p := by
    have harms := S.line_arms p
    rw [hcard] at harms
    have hd4 := thirteen_lineDegree_eq_zero_of_lineCount_eq_zero S 4 p hl4
    have hd6 := thirteen_lineDegree_eq_zero_of_lineCount_eq_zero S 6 p hl6
    have hd7 := thirteen_lineDegree_eq_zero_of_lineCount_eq_zero S 7 p hl7
    have hd8 := thirteen_lineDegree_eq_zero_of_lineCount_eq_zero S 8 p hl8
    have hd9 := thirteen_lineDegree_eq_zero_of_lineCount_eq_zero S 9 p hl9
    have hd10 := thirteen_lineDegree_eq_zero_of_lineCount_eq_zero S 10 p hl10
    have hd11 := thirteen_lineDegree_eq_zero_of_lineCount_eq_zero S 11 p hl11
    have hd12 := thirteen_lineDegree_eq_zero_of_lineCount_eq_zero S 12 p hl12
    have hd13 := thirteen_lineDegree_eq_zero_of_lineCount_eq_zero S 13 p hl13
    norm_num [Finset.sum_range_succ, hd4, hd6, hd7, hd8, hd9, hd10,
      hd11, hd12, hd13] at harms
    omega
  let positiveLabels : Finset alpha :=
    Finset.univ.filter fun p => S.lineDegree 2 p ≠ 0
  let zeroLabels : Finset alpha :=
    Finset.univ.filter fun p => S.lineDegree 2 p = 0
  have hpositiveSum :
      2 * positiveLabels.card ≤
        ∑ p ∈ positiveLabels, S.lineDegree 2 p := by
    calc
      2 * positiveLabels.card = ∑ _p ∈ positiveLabels, 2 := by
        simp [mul_comm]
      _ ≤ ∑ p ∈ positiveLabels, S.lineDegree 2 p := by
        exact Finset.sum_le_sum fun p hp =>
          hpositiveTwo p (Finset.mem_filter.mp hp).2
  have hpositiveSumUpper :
      (∑ p ∈ positiveLabels, S.lineDegree 2 p) ≤ 10 := by
    calc
      (∑ p ∈ positiveLabels, S.lineDegree 2 p) ≤
          ∑ p : alpha, S.lineDegree 2 p := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · exact Finset.filter_subset _ _
        · intro p _hp _hnot
          exact Nat.zero_le _
      _ = 2 * S.lineCount 2 := S.line_incidence 2
      _ = 10 := by rw [htwo]
  have hpositiveCard : positiveLabels.card ≤ 5 := by omega
  have hpartition : zeroLabels.card + positiveLabels.card = 13 := by
    simpa [zeroLabels, positiveLabels, hcard] using
      (Finset.card_filter_add_card_filter_not
        (s := (Finset.univ : Finset alpha))
        (p := fun p => S.lineDegree 2 p = 0))
  have hzeroCard : 8 ≤ zeroLabels.card := by omega
  have hzeroAttachment (p : alpha) (hp : p ∈ zeroLabels) :
      3 ≤ A.lineOrdinaryAttachmentDegree p := by
    have hpzero : S.lineDegree 2 p = 0 :=
      (Finset.mem_filter.mp hp).2
    have hdualZero : A.lineOrdinaryVertexDegree p = 0 := by
      change (labelDualArrangement cfg).lineOrdinaryVertexDegree p = 0
      rw [labelDual_lineOrdinaryVertexDegree_eq_lineDegree_two]
      exact hpzero
    exact A.three_le_lineOrdinaryAttachmentDegree_of_degree_zero
      hA p (hhigh p) hdualZero
  have hzeroAttachmentSum :
      3 * zeroLabels.card ≤
        ∑ p ∈ zeroLabels, A.lineOrdinaryAttachmentDegree p := by
    calc
      3 * zeroLabels.card = ∑ _p ∈ zeroLabels, 3 := by simp [mul_comm]
      _ ≤ ∑ p ∈ zeroLabels, A.lineOrdinaryAttachmentDegree p := by
        exact Finset.sum_le_sum fun p hp => hzeroAttachment p hp
  have hzeroAttachmentSumFull :
      (∑ p ∈ zeroLabels, A.lineOrdinaryAttachmentDegree p) ≤
        ∑ p : alpha, A.lineOrdinaryAttachmentDegree p := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · exact Finset.filter_subset _ _
    · intro p _hp _hnot
      exact Nat.zero_le _
  have hattachmentUpper :
      (∑ p : alpha, A.lineOrdinaryAttachmentDegree p) ≤
        4 * Fintype.card A.OrdinaryVertex := by
    rw [show (∑ p : alpha, A.lineOrdinaryAttachmentDegree p) =
        ∑ q : A.OrdinaryVertex, A.ordinaryVertexAttachmentDegree q by
      simpa only [FiniteProjectiveLineArrangement.lineOrdinaryAttachmentDegree,
        FiniteProjectiveLineArrangement.ordinaryVertexAttachmentDegree] using
        (sum_finiteRelationRightDegree_eq_sum_finiteRelationLeftDegree
          A.OrdinaryVertexAttachedToLine)]
    calc
      (∑ q : A.OrdinaryVertex, A.ordinaryVertexAttachmentDegree q) ≤
          ∑ _q : A.OrdinaryVertex, 4 := by
        exact Finset.sum_le_sum fun q _hq =>
          A.ordinaryVertexAttachmentDegree_le_four hA q
      _ = 4 * Fintype.card A.OrdinaryVertex := by simp [mul_comm]
  have hordinaryCard : Fintype.card A.OrdinaryVertex = 5 := by
    change Fintype.card (labelDualArrangement cfg).OrdinaryVertex = 5
    rw [← lineCount_two_eq_card_labelDualOrdinaryVertex cfg, htwo]
  rw [hordinaryCard] at hattachmentUpper
  omega

/-- Every pivot of an admissible fourteen-label configuration lies on at
least six three-blocks. -/
theorem six_le_blockDegree_three_of_card_fourteen
    {alpha : Type u} [Fintype alpha] [DecidableEq alpha]
    (Mel : RealPlaneMelchiorPrinciple.{u})
    (cfg : Configuration alpha) (hadm : Admissible cfg)
    (hcard : Fintype.card alpha = 14) (p : alpha) :
    6 ≤ (blockSystem cfg).blockDegree 3 p := by
  have hnon : Noncollinear (pivotInversion cfg p) :=
    pivotInversion_noncollinear cfg hadm (by omega) p
  have hthirteen : Fintype.card (AwayFrom p) = 13 := by
    rw [card_awayFrom, hcard]
  have hordinary := six_le_lineCount_two_of_card_thirteen
    Mel (pivotInversion cfg p) hnon hthirteen
  rw [← blockDegree_three_eq_lineCount_two_pivotInversion] at hordinary
  exact hordinary

end Erdos506.Incidence
