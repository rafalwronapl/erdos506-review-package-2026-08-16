import Erdos506.Incidence.EvenArrangementPrinciple
import Erdos506.V1.FiniteCaps

/-!
# The nine-point V1 endpoint below the five-circle wall

This file closes the branch in which every determined proper circle has at
most four selected points.  The eight-point Orchard input after pivot
inversion is replaced by the explicit even-arrangement statement: under the
size-four block cap, eight four-blocks through a pivot would give Melchior
slack exactly one.
-/

namespace Erdos506.V1

open Erdos506.Block
open Erdos506.Block.BlockSystem
open Erdos506.Incidence
open Erdos506.V3
open Erdos506.V4
open scoped BigOperators

universe u

/-- The V1 pivot expression is exactly the Melchior slack of the inverted
configuration. -/
theorem pivotSigma_eq_lineMelchiorSlack
    {α : Type*} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (p : α) :
    (geometricBlockSystem cfg).pivotSigma p =
      lineMelchiorSlack (pivotInversion cfg p) := by
  classical
  have hsum :
      (∑ b : PivotBlock cfg p,
          (4 - ((geometricBlockSupport cfg b.1).card : ℤ))) =
        ∑ L : DeterminedLine (pivotInversion cfg p),
          (3 - ((lineSupport (pivotInversion cfg p) L).card : ℤ)) := by
    apply Fintype.sum_equiv (blockPivotLineEquiv cfg p)
    intro b
    exact (pivotWeight_blockToPivotLine cfg p b).symm
  rw [(geometricBlockSystem cfg).pivotSigma_eq_sum_nontrivialBlockAt_sub_three]
  unfold lineMelchiorSlack
  exact congrArg (fun z : ℤ => z - 3) hsum

private theorem blockCount_eq_zero_of_cap
    {Point Block : Type*} [Fintype Point] [Fintype Block]
    [DecidableEq Point]
    (S : BlockSystem Point Block) {M s : ℕ}
    (hcap : BlockSizeCap S M) (hthree : 3 ≤ s) (hlarge : M < s) :
    S.blockCount s = 0 := by
  classical
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro b hb
  have hsize := S.mem_blocksOfSize.mp hb
  have hle := hcap b (by omega)
  omega

private theorem lineCount_eq_zero_of_cap
    {Point Block : Type*} [Fintype Point] [Fintype Block]
    [DecidableEq Point]
    (S : BlockSystem Point Block) {M s : ℕ}
    (hcap : BlockSizeCap S M) (hthree : 3 ≤ s) (hlarge : M < s) :
    S.lineCount s = 0 := by
  classical
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro b hb
  have hspec := S.mem_blocksOfKindSize.mp hb
  have hle := hcap b (by rw [hspec.2]; exact hthree)
  omega

private theorem circleCount_eq_zero_of_cap
    {Point Block : Type*} [Fintype Point] [Fintype Block]
    [DecidableEq Point]
    (S : BlockSystem Point Block) {M s : ℕ}
    (hcap : BlockSizeCap S M) (hlarge : M < s) :
    S.circleCount s = 0 := by
  classical
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro b hb
  have hspec := S.mem_blocksOfKindSize.mp hb
  have hle := hcap b (S.circle_min b hspec.1)
  omega

private theorem blockDegree_eq_zero_of_blockCount_eq_zero
    {Point Block : Type*} [Fintype Point] [Fintype Block]
    [DecidableEq Point]
    (S : BlockSystem Point Block) (s : ℕ) (p : Point)
    (hzero : S.blockCount s = 0) :
    S.blockDegree s p = 0 := by
  have hinc := S.block_incidence s
  rw [hzero] at hinc
  have hle : S.blockDegree s p ≤ ∑ q : Point, S.blockDegree s q := by
    exact Finset.single_le_sum
      (fun q _hq => Nat.zero_le (S.blockDegree s q)) (Finset.mem_univ p)
  omega

/-- Under the contradictory circle bound, a cap of four on determined
circles and the sharp rich-line pencil give a cap of four on every V1 block. -/
theorem blockSizeCap_four_of_card_nine_of_circleCount_le_twenty_four
    {α : Type u} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (hadm : Admissible cfg)
    (hcard : Fintype.card α = 9)
    (hcount : Erdos506.V4.circleCount cfg ≤ 24)
    (hcircle : ∀ c : DeterminedCircle cfg,
      (circleTrace cfg c.1).card ≤ 4) :
    BlockSizeCap (blockSystem cfg) 4 := by
  intro b _hthree
  cases b with
  | inl L =>
      simpa [blockSystem, geometricBlockSupport] using
        lineSupport_card_le_four_of_nine_of_circleCount_le
          cfg hadm hcard hcount L
  | inr c =>
      simpa [blockSystem, geometricBlockSupport] using hcircle c

private theorem nine_local_pair_sigma
    {Point Block : Type*} [Fintype Point] [Fintype Block]
    [DecidableEq Point]
    (S : BlockSystem Point Block) (hcard : Fintype.card Point = 9)
    (hcap : BlockSizeCap S 4) (p : Point) :
    S.blockDegree 3 p + 3 * S.blockDegree 4 p = 28 ∧
      S.pivotSigma p = 25 - 3 * (S.blockDegree 4 p : ℤ) := by
  have hb5 : S.blockCount 5 = 0 :=
    blockCount_eq_zero_of_cap S hcap (by omega) (by omega)
  have hb6 : S.blockCount 6 = 0 :=
    blockCount_eq_zero_of_cap S hcap (by omega) (by omega)
  have hb7 : S.blockCount 7 = 0 :=
    blockCount_eq_zero_of_cap S hcap (by omega) (by omega)
  have hb8 : S.blockCount 8 = 0 :=
    blockCount_eq_zero_of_cap S hcap (by omega) (by omega)
  have hb9 : S.blockCount 9 = 0 :=
    blockCount_eq_zero_of_cap S hcap (by omega) (by omega)
  have hd5 := blockDegree_eq_zero_of_blockCount_eq_zero S 5 p hb5
  have hd6 := blockDegree_eq_zero_of_blockCount_eq_zero S 6 p hb6
  have hd7 := blockDegree_eq_zero_of_blockCount_eq_zero S 7 p hb7
  have hd8 := blockDegree_eq_zero_of_blockCount_eq_zero S 8 p hb8
  have hd9 := blockDegree_eq_zero_of_blockCount_eq_zero S 9 p hb9
  have hpairs := S.pivot_pair_partition p
  rw [hcard] at hpairs
  norm_num [Finset.sum_range_succ, Nat.choose, hd5, hd6, hd7, hd8, hd9]
    at hpairs
  have hsigma :
      S.pivotSigma p = 25 - 3 * (S.blockDegree 4 p : ℤ) := by
    unfold BlockSystem.pivotSigma BlockSystem.nontrivialSizes
    rw [hcard]
    have hIcc : Finset.Icc 3 9 = {3, 4, 5, 6, 7, 8, 9} := by decide
    rw [hIcc]
    norm_num [hd5, hd6, hd7, hd8, hd9]
    omega
  exact ⟨hpairs, hsigma⟩

/-- The even-arrangement slack obstruction is the eight-point Orchard bound
needed after inversion: at most seven four-blocks pass through any pivot. -/
theorem blockDegree_four_le_seven_of_card_nine
    {α : Type u} [Fintype α] [DecidableEq α]
    (Mel : RealPlaneMelchiorPrinciple.{u})
    (EvenArr : RealPlaneEvenArrangementPrinciple.{u})
    (cfg : Configuration α) (hadm : Admissible cfg)
    (hcard : Fintype.card α = 9)
    (hcap : BlockSizeCap (blockSystem cfg) 4)
    (p : α) :
    (blockSystem cfg).blockDegree 4 p ≤ 7 := by
  let S := blockSystem cfg
  change S.blockDegree 4 p ≤ 7
  have hlocal := nine_local_pair_sigma S hcard hcap p
  have hnoncol : Noncollinear (pivotInversion cfg p) :=
    pivotInversion_noncollinear cfg hadm (by omega) p
  have hmel : LineMelchior (pivotInversion cfg p) :=
    Mel.lineMelchior (pivotInversion cfg p) hnoncol
  have hnonneg : 0 ≤ S.pivotSigma p := by
    simpa [S] using pivotSigma_nonneg_of_lineMelchior cfg p hmel
  have hpivotCard : Fintype.card (AwayFrom p) = 8 := by
    rw [card_awayFrom, hcard]
  have heven : Even (Fintype.card (AwayFrom p)) := by
    rw [hpivotCard]
    norm_num
  have hslackNe : lineMelchiorSlack (pivotInversion cfg p) ≠ 1 :=
    EvenArr.slack_ne_one (pivotInversion cfg p) hnoncol heven
  have hsigmaNe : S.pivotSigma p ≠ 1 := by
    rw [← pivotSigma_eq_lineMelchiorSlack cfg p] at hslackNe
    simpa [S] using hslackNe
  omega

private theorem globalLineRow_eq_three_lineCount_three_add_seven_lineCount_four
    {Point Block : Type*} [Fintype Point] [Fintype Block]
    [DecidableEq Point]
    (S : BlockSystem Point Block) (hcard : Fintype.card Point = 9)
    (hcap : BlockSizeCap S 4) :
    S.globalLineRow =
      3 * (S.lineCount 3 : ℤ) + 7 * (S.lineCount 4 : ℤ) := by
  classical
  let w : ℕ → ℕ := fun s =>
    if 3 ≤ s then Nat.choose s 2 + s - 3 else 0
  have hl5 : S.lineCount 5 = 0 :=
    lineCount_eq_zero_of_cap S hcap (by omega) (by omega)
  have hl6 : S.lineCount 6 = 0 :=
    lineCount_eq_zero_of_cap S hcap (by omega) (by omega)
  have hl7 : S.lineCount 7 = 0 :=
    lineCount_eq_zero_of_cap S hcap (by omega) (by omega)
  have hl8 : S.lineCount 8 = 0 :=
    lineCount_eq_zero_of_cap S hcap (by omega) (by omega)
  have hl9 : S.lineCount 9 = 0 :=
    lineCount_eq_zero_of_cap S hcap (by omega) (by omega)
  have hgroup := S.sum_kindCount_weight .line w
  change
    (∑ s ∈ Finset.range (Fintype.card Point + 1),
      w s * S.lineCount s) =
      ∑ b ∈ S.blocksOfKind .line, w (S.support b).card at hgroup
  rw [hcard] at hgroup
  norm_num [Finset.sum_range_succ, w,
    hl5, hl6, hl7, hl8, hl9, Nat.choose] at hgroup
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
  rw [hglobal]
  have hnat :
      (∑ b ∈ S.blocksOfKind .line, w (S.support b).card) =
        3 * S.lineCount 3 + 7 * S.lineCount 4 := by
    exact hgroup.symm
  exact_mod_cast hnat

/-- Exact circle objective and the direct global line row after the
size-four cap reduces the nine-point census to sizes three and four. -/
theorem nine_global_rows
    {α : Type u} [Fintype α] [DecidableEq α]
    (Mel : RealPlaneMelchiorPrinciple.{u})
    (cfg : Configuration α) (hadm : Admissible cfg)
    (hcard : Fintype.card α = 9)
    (hcap : BlockSizeCap (blockSystem cfg) 4) :
    let S := blockSystem cfg
    ((S.totalCircleCount : ℤ) =
      84 - 3 * (S.blockCount 4 : ℤ) -
        (S.lineCount 3 : ℤ) - (S.lineCount 4 : ℤ)) ∧
    (3 * (S.lineCount 3 : ℤ) + 7 * (S.lineCount 4 : ℤ) ≤ 33) := by
  classical
  dsimp only
  let S := blockSystem cfg
  have hb5 : S.blockCount 5 = 0 :=
    blockCount_eq_zero_of_cap S hcap (by omega) (by omega)
  have hb6 : S.blockCount 6 = 0 :=
    blockCount_eq_zero_of_cap S hcap (by omega) (by omega)
  have hb7 : S.blockCount 7 = 0 :=
    blockCount_eq_zero_of_cap S hcap (by omega) (by omega)
  have hb8 : S.blockCount 8 = 0 :=
    blockCount_eq_zero_of_cap S hcap (by omega) (by omega)
  have hb9 : S.blockCount 9 = 0 :=
    blockCount_eq_zero_of_cap S hcap (by omega) (by omega)
  have hc0 : S.circleCount 0 = 0 :=
    S.circleCount_eq_zero_of_lt_three (by omega)
  have hc1 : S.circleCount 1 = 0 :=
    S.circleCount_eq_zero_of_lt_three (by omega)
  have hc2 : S.circleCount 2 = 0 :=
    S.circleCount_eq_zero_of_lt_three (by omega)
  have hc5 : S.circleCount 5 = 0 :=
    circleCount_eq_zero_of_cap S hcap (by omega)
  have hc6 : S.circleCount 6 = 0 :=
    circleCount_eq_zero_of_cap S hcap (by omega)
  have hc7 : S.circleCount 7 = 0 :=
    circleCount_eq_zero_of_cap S hcap (by omega)
  have hc8 : S.circleCount 8 = 0 :=
    circleCount_eq_zero_of_cap S hcap (by omega)
  have hc9 : S.circleCount 9 = 0 :=
    circleCount_eq_zero_of_cap S hcap (by omega)
  have htriple := S.triple_partition_by_size
  rw [hcard] at htriple
  norm_num [Finset.sum_range_succ, Nat.choose, hb5, hb6, hb7, hb8, hb9]
    at htriple
  have htripleZ :
      (S.blockCount 3 : ℤ) + 4 * (S.blockCount 4 : ℤ) = 84 := by
    exact_mod_cast htriple
  have hsplit3 := S.blockCount_eq_lineCount_add_circleCount 3
  have hsplit4 := S.blockCount_eq_lineCount_add_circleCount 4
  have htotal := S.totalCircleCount_eq_sum_circleCount
  rw [hcard] at htotal
  norm_num [Finset.sum_range_succ, hc0, hc1, hc2, hc5, hc6, hc7, hc8, hc9]
    at htotal
  have htotalZ :
      (S.totalCircleCount : ℤ) =
        84 - 3 * (S.blockCount 4 : ℤ) -
          (S.lineCount 3 : ℤ) - (S.lineCount 4 : ℤ) := by
    omega
  have hline :=
    globalLineRow_le_choose_two_sub_three_of_realPlaneMelchior Mel cfg hadm
  change S.globalLineRow ≤
    (Nat.choose (Fintype.card α) 2 : ℤ) - 3 at hline
  rw [globalLineRow_eq_three_lineCount_three_add_seven_lineCount_four
    S hcard hcap, hcard] at hline
  norm_num [Nat.choose] at hline
  exact ⟨htotalZ, hline⟩

/-- If every determined proper circle has size at most four, every admissible
nine-point V1 configuration determines at least twenty-five proper circles. -/
theorem circleCount_ge_twenty_five_of_card_nine_of_circle_cap_four
    {α : Type u} [Fintype α] [DecidableEq α]
    (Mel : RealPlaneMelchiorPrinciple.{u})
    (EvenArr : RealPlaneEvenArrangementPrinciple.{u})
    (cfg : Configuration α) (hadm : Admissible cfg)
    (hcard : Fintype.card α = 9)
    (hcircle : ∀ c : DeterminedCircle cfg,
      (circleTrace cfg c.1).card ≤ 4) :
    25 ≤ Erdos506.V4.circleCount cfg := by
  by_contra hnot
  have hcount : Erdos506.V4.circleCount cfg ≤ 24 := by omega
  let S := blockSystem cfg
  have hcap : BlockSizeCap S 4 := by
    simpa [S] using
      blockSizeCap_four_of_card_nine_of_circleCount_le_twenty_four
        cfg hadm hcard hcount hcircle
  have hrows := nine_global_rows Mel cfg hadm hcard hcap
  change
    ((S.totalCircleCount : ℤ) =
      84 - 3 * (S.blockCount 4 : ℤ) -
        (S.lineCount 3 : ℤ) - (S.lineCount 4 : ℤ)) ∧
    (3 * (S.lineCount 3 : ℤ) + 7 * (S.lineCount 4 : ℤ) ≤ 33) at hrows
  have htotalEq := hrows.1
  have hline := hrows.2
  have hlineCount :
      (S.lineCount 3 : ℤ) + (S.lineCount 4 : ℤ) ≤ 11 := by
    omega
  have htotalBridge :
      S.totalCircleCount = Erdos506.V4.circleCount cfg := by
    rw [totalCircleCount_eq_card_determinedCircle,
      ← Erdos506.V3.circleCount_eq_card_determinedCircle]
  rw [htotalBridge] at htotalEq
  have hcountZ : (Erdos506.V4.circleCount cfg : ℤ) ≤ 24 := by
    exact_mod_cast hcount
  have hmany : 17 ≤ S.blockCount 4 := by
    omega
  have hdegree : ∀ p : α, S.blockDegree 4 p ≤ 7 := by
    intro p
    simpa [S] using blockDegree_four_le_seven_of_card_nine
      Mel EvenArr cfg hadm hcard hcap p
  have hsumLe : (∑ p : α, S.blockDegree 4 p) ≤ 9 * 7 := by
    calc
      (∑ p : α, S.blockDegree 4 p) ≤ ∑ _p : α, 7 :=
        Finset.sum_le_sum fun p _hp => hdegree p
      _ = 9 * 7 := by simp [hcard]
  have hinc := S.block_incidence 4
  rw [hinc] at hsumLe
  omega

/-- A determined proper circle containing at least six selected points already
forces the nine-point target by the rich-circle cap calculation. -/
theorem circleCount_ge_twenty_five_of_card_nine_of_circleTrace_ge_six
    {α : Type u} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (hadm : Admissible cfg)
    (hcard : Fintype.card α = 9)
    (c : DeterminedCircle cfg)
    (hc : 6 ≤ (circleTrace cfg c.1).card) :
    25 ≤ Erdos506.V4.circleCount cfg := by
  by_contra hnot
  have hcount : Erdos506.V4.circleCount cfg ≤ 24 := by omega
  have hcap := circleTrace_card_le_five_of_nine_of_circleCount_le
    cfg hadm hcard hcount c
  omega

end Erdos506.V1
