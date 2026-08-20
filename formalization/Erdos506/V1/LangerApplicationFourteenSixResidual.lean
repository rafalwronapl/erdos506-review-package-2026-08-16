import Erdos506.V1.LangerApplicationRichBlockResidual
import Erdos506.V1.DirectKelly
import Erdos506.Incidence.SixConicEightOutsiderLineIncidence

/-!
# The actual fourteen-point selected-six residual

This module records the full incidence input left by the Langer-free
finite-window reduction at `n = 14`.  It does not postulate an endpoint:
the rows below are consequences of the block-system axioms and Melchior.
-/

namespace Erdos506.V1

open Erdos506.Block
open Erdos506.Block.BlockSystem
open Erdos506.Incidence
open Erdos506.V4
open scoped BigOperators

universe u v

section RelativeRows

variable {Point : Type u} {Block : Type v}
  [Fintype Point] [Fintype Block] [DecidableEq Point]

/-- The four relative triple partitions for a six--eight split of fourteen
points.  This is the exact row input for the selected-six residual. -/
theorem fourteenSix_relative_rows
    (S : BlockSystem Point Block) (D : Finset Point)
    (hpoint : Fintype.card Point = 14) (hD : D.card = 6) :
    (∑ b : Block, (Nat.choose (fourteenOutside S D b) 3 : ℤ)) = 56 ∧
    (∑ b : Block,
      (fourteenInside S D b : ℤ) *
        (Nat.choose (fourteenOutside S D b) 2 : ℤ)) = 168 ∧
    (∑ b : Block,
      (Nat.choose (fourteenInside S D b) 2 : ℤ) *
        (fourteenOutside S D b : ℤ)) = 120 ∧
    (∑ b : Block, (Nat.choose (fourteenInside S D b) 3 : ℤ)) = 20 := by
  have h0 := S.relative_triple_partition D 0 (by omega)
  have h1 := S.relative_triple_partition D 1 (by omega)
  have h2 := S.relative_triple_partition D 2 (by omega)
  have h3 := S.relative_triple_partition D 3 (by omega)
  rw [hpoint, hD] at h0 h1 h2 h3
  norm_num [fourteenInside, fourteenOutside, Nat.choose] at h0 h1 h2 h3
  constructor
  · exact_mod_cast h0
  constructor
  · exact_mod_cast h1
  constructor
  · exact_mod_cast h2
  · exact_mod_cast h3

end RelativeRows

section GeometricResidual

private theorem fourteenSix_blockCount_eq_zero_of_cap
    {Point Block : Type*} [Fintype Point] [Fintype Block]
    [DecidableEq Point]
    (S : BlockSystem Point Block) {s : ℕ}
    (hcap : BlockSizeCap S 6) (hlarge : 6 < s) :
    S.blockCount s = 0 := by
  classical
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro b hb
  have hsize := S.mem_blocksOfSize.mp hb
  have hle := hcap b (by omega)
  omega

private theorem fourteenSix_blockDegree_eq_zero_of_cap
    {Point Block : Type*} [Fintype Point] [Fintype Block]
    [DecidableEq Point]
    (S : BlockSystem Point Block) (hcap : BlockSizeCap S 6)
    (p : Point) {s : ℕ} (hlarge : 6 < s) :
    S.blockDegree s p = 0 := by
  have hzero := fourteenSix_blockCount_eq_zero_of_cap S hcap hlarge
  have hinc := S.block_incidence s
  rw [hzero] at hinc
  have hle : S.blockDegree s p ≤ ∑ q : Point, S.blockDegree s q :=
    Finset.single_le_sum
      (fun q _hq => Nat.zero_le (S.blockDegree s q)) (Finset.mem_univ p)
  omega

private theorem fourteenSix_lineDegree_eq_zero_of_cap
    {Point Block : Type*} [Fintype Point] [Fintype Block]
    [DecidableEq Point]
    (S : BlockSystem Point Block) (hcap : BlockSizeCap S 6)
    (p : Point) {s : ℕ} (hlarge : 6 < s) :
    S.lineDegree s p = 0 := by
  have hzero := fourteenSix_blockCount_eq_zero_of_cap S hcap hlarge
  have hsplit := S.blockCount_eq_lineCount_add_circleCount s
  have hlineZero : S.lineCount s = 0 := by omega
  have hinc := S.line_incidence s
  rw [hlineZero] at hinc
  have hle : S.lineDegree s p ≤ ∑ q : Point, S.lineDegree s q :=
    Finset.single_le_sum
      (fun q _hq => Nat.zero_le (S.lineDegree s q)) (Finset.mem_univ p)
  omega

/-- The exact pointwise rows retained from a capped fourteen-point block
system.  These are the small-slack rows used by labelled Gamma-six lifts. -/
structure FourteenSixPointRows
    {Point Block : Type*} [Fintype Point] [Fintype Block]
    [DecidableEq Point]
    (S : BlockSystem Point Block) (p : Point) where
  pair_row :
    S.blockDegree 3 p + 3 * S.blockDegree 4 p +
      6 * S.blockDegree 5 p + 10 * S.blockDegree 6 p = 78
  sigma_row :
    S.pivotSigma p = (S.blockDegree 3 p : ℤ) -
      (S.blockDegree 5 p : ℤ) - 2 * (S.blockDegree 6 p : ℤ) - 3
  sigma_nonnegative : 0 ≤ S.pivotSigma p
  line_arm_row :
    S.lineDegree 2 p + 2 * S.lineDegree 3 p +
      3 * S.lineDegree 4 p + 4 * S.lineDegree 5 p +
      5 * S.lineDegree 6 p = 13
  kappa_row :
    S.restoredKappa p + 3 * (S.lineDegree 3 p : ℤ) +
      4 * (S.lineDegree 4 p : ℤ) +
      5 * (S.lineDegree 5 p : ℤ) +
      6 * (S.lineDegree 6 p : ℤ) = 13 + S.pivotSigma p
  kappa_nonnegative : 0 ≤ S.restoredKappa p

/-- Eliminating the three-block degree leaves the small local residue used
in the Gamma-six catalogues. -/
theorem FourteenSixPointRows.rich_residue_row
    {Point Block : Type*} [Fintype Point] [Fintype Block]
    [DecidableEq Point]
    {S : BlockSystem Point Block} {p : Point}
    (R : FourteenSixPointRows S p) :
    3 * (S.blockDegree 4 p : ℤ) + 7 * (S.blockDegree 5 p : ℤ) +
      12 * (S.blockDegree 6 p : ℤ) + S.pivotSigma p = 75 := by
  have hpairs :
      (S.blockDegree 3 p : ℤ) + 3 * (S.blockDegree 4 p : ℤ) +
        6 * (S.blockDegree 5 p : ℤ) +
        10 * (S.blockDegree 6 p : ℤ) = 78 := by
    exact_mod_cast R.pair_row
  rw [R.sigma_row]
  omega

/-- The corresponding pointwise congruence, retained without converting
the signed Melchior slack to a truncated natural number. -/
theorem FourteenSixPointRows.sigma_add_fiveDegree_mod_three
    {Point Block : Type*} [Fintype Point] [Fintype Block]
    [DecidableEq Point]
    {S : BlockSystem Point Block} {p : Point}
    (R : FourteenSixPointRows S p) :
    (S.pivotSigma p + (S.blockDegree 5 p : ℤ)) % 3 = 0 := by
  have hrow := R.rich_residue_row
  omega

/-- Actual configuration-level data available in the selected-six-circle
branch at fourteen points.  In particular, this records the pointwise
Melchior input needed by grouped local arguments, rather than only its
summed consequence. -/
structure FourteenSixCircleResidualData
    {α : Type u} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (c : DeterminedCircle cfg) where
  point_card : Fintype.card α = 14
  selected_card : (circleTrace cfg c.1).card = 6
  circle_count_le : Erdos506.V4.circleCount cfg ≤ 72
  block_cap : BlockSizeCap (blockSystem cfg) 6
  pivot_nonnegative : ∀ p : α, 0 ≤ (blockSystem cfg).pivotSigma p
  restored_nonnegative :
    ∀ p : α, 0 ≤ (blockSystem cfg).restoredKappa p
  selected_moment :
    18 ≤ (blockSystem cfg).subsetPivotMoment (circleTrace cfg c.1)
  outside_card : (Finset.univ \ circleTrace cfg c.1).card = 8
  outside_moment :
    24 ≤ (blockSystem cfg).subsetPivotMoment
      (Finset.univ \ circleTrace cfg c.1)
  defect_row_le : (blockSystem cfg).defectRow ≤ 140
  other_meets_selected_le_two : ∀ b : GeometricBlock cfg,
    b ≠ Sum.inr c →
      (geometricBlockSupport cfg b ∩ circleTrace cfg c.1).card ≤ 2

/-- The abstract relative rows specialized to the selected circle carried
by the residual record. -/
theorem FourteenSixCircleResidualData.relative_rows
    {α : Type u} [Fintype α] [DecidableEq α]
    {cfg : Configuration α} {c : DeterminedCircle cfg}
    (R : FourteenSixCircleResidualData cfg c) :
    (∑ b : GeometricBlock cfg,
      (Nat.choose (fourteenOutside (blockSystem cfg)
        (circleTrace cfg c.1) b) 3 : ℤ)) = 56 ∧
    (∑ b : GeometricBlock cfg,
      (fourteenInside (blockSystem cfg) (circleTrace cfg c.1) b : ℤ) *
        (Nat.choose (fourteenOutside (blockSystem cfg)
          (circleTrace cfg c.1) b) 2 : ℤ)) = 168 ∧
    (∑ b : GeometricBlock cfg,
      (Nat.choose (fourteenInside (blockSystem cfg)
        (circleTrace cfg c.1) b) 2 : ℤ) *
        (fourteenOutside (blockSystem cfg) (circleTrace cfg c.1) b : ℤ)) = 120 ∧
    (∑ b : GeometricBlock cfg,
      (Nat.choose (fourteenInside (blockSystem cfg)
        (circleTrace cfg c.1) b) 3 : ℤ)) = 20 :=
  fourteenSix_relative_rows (blockSystem cfg) (circleTrace cfg c.1)
    R.point_card R.selected_card

/-- Specialize triple ownership and the signed pivot definition at every
point of an actual fourteen-point selected-six residual. -/
theorem FourteenSixCircleResidualData.point_rows
    {α : Type u} [Fintype α] [DecidableEq α]
    {cfg : Configuration α} {c : DeterminedCircle cfg}
    (R : FourteenSixCircleResidualData cfg c) (p : α) :
    FourteenSixPointRows (blockSystem cfg) p := by
  let S := blockSystem cfg
  have hd7 : S.blockDegree 7 p = 0 :=
    fourteenSix_blockDegree_eq_zero_of_cap S R.block_cap p (by omega)
  have hd8 : S.blockDegree 8 p = 0 :=
    fourteenSix_blockDegree_eq_zero_of_cap S R.block_cap p (by omega)
  have hd9 : S.blockDegree 9 p = 0 :=
    fourteenSix_blockDegree_eq_zero_of_cap S R.block_cap p (by omega)
  have hd10 : S.blockDegree 10 p = 0 :=
    fourteenSix_blockDegree_eq_zero_of_cap S R.block_cap p (by omega)
  have hd11 : S.blockDegree 11 p = 0 :=
    fourteenSix_blockDegree_eq_zero_of_cap S R.block_cap p (by omega)
  have hd12 : S.blockDegree 12 p = 0 :=
    fourteenSix_blockDegree_eq_zero_of_cap S R.block_cap p (by omega)
  have hd13 : S.blockDegree 13 p = 0 :=
    fourteenSix_blockDegree_eq_zero_of_cap S R.block_cap p (by omega)
  have hd14 : S.blockDegree 14 p = 0 :=
    fourteenSix_blockDegree_eq_zero_of_cap S R.block_cap p (by omega)
  have hld7 : S.lineDegree 7 p = 0 :=
    fourteenSix_lineDegree_eq_zero_of_cap S R.block_cap p (by omega)
  have hld8 : S.lineDegree 8 p = 0 :=
    fourteenSix_lineDegree_eq_zero_of_cap S R.block_cap p (by omega)
  have hld9 : S.lineDegree 9 p = 0 :=
    fourteenSix_lineDegree_eq_zero_of_cap S R.block_cap p (by omega)
  have hld10 : S.lineDegree 10 p = 0 :=
    fourteenSix_lineDegree_eq_zero_of_cap S R.block_cap p (by omega)
  have hld11 : S.lineDegree 11 p = 0 :=
    fourteenSix_lineDegree_eq_zero_of_cap S R.block_cap p (by omega)
  have hld12 : S.lineDegree 12 p = 0 :=
    fourteenSix_lineDegree_eq_zero_of_cap S R.block_cap p (by omega)
  have hld13 : S.lineDegree 13 p = 0 :=
    fourteenSix_lineDegree_eq_zero_of_cap S R.block_cap p (by omega)
  have hld14 : S.lineDegree 14 p = 0 :=
    fourteenSix_lineDegree_eq_zero_of_cap S R.block_cap p (by omega)
  have hpairs := S.pivot_pair_partition p
  rw [R.point_card] at hpairs
  norm_num [Finset.sum_range_succ, Nat.choose, hd7, hd8, hd9, hd10,
    hd11, hd12, hd13, hd14] at hpairs
  have hsigma :
      S.pivotSigma p = (S.blockDegree 3 p : ℤ) -
        (S.blockDegree 5 p : ℤ) - 2 * (S.blockDegree 6 p : ℤ) - 3 := by
    have hIcc : Finset.Icc 3 14 =
        {3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14} := by decide
    unfold BlockSystem.pivotSigma BlockSystem.nontrivialSizes
    rw [R.point_card, hIcc]
    norm_num [hd7, hd8, hd9, hd10, hd11, hd12, hd13, hd14]
    ring
  have harms := S.line_arms p
  rw [R.point_card] at harms
  norm_num [Finset.sum_range_succ, hld7, hld8, hld9, hld10, hld11,
    hld12, hld13, hld14] at harms
  have hkappa :
      S.restoredKappa p + 3 * (S.lineDegree 3 p : ℤ) +
        4 * (S.lineDegree 4 p : ℤ) +
        5 * (S.lineDegree 5 p : ℤ) +
        6 * (S.lineDegree 6 p : ℤ) = 13 + S.pivotSigma p := by
    have hIcc : Finset.Icc 3 14 =
        {3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14} := by decide
    unfold BlockSystem.restoredKappa BlockSystem.nontrivialSizes
    rw [R.point_card, hIcc]
    norm_num [hld7, hld8, hld9, hld10, hld11, hld12, hld13, hld14]
    omega
  exact ⟨hpairs, hsigma, R.pivot_nonnegative p, harms, hkappa,
    R.restored_nonnegative p⟩

/-- The selected circle itself contributes one six-block through every one
of its six labels. -/
theorem FourteenSixCircleResidualData.one_le_sixDegree_on_selected
    {α : Type u} [Fintype α] [DecidableEq α]
    {cfg : Configuration α} {c : DeterminedCircle cfg}
    (R : FourteenSixCircleResidualData cfg c) {p : α}
    (hp : p ∈ circleTrace cfg c.1) :
    1 ≤ (blockSystem cfg).blockDegree 6 p := by
  let S := blockSystem cfg
  change 1 ≤ ((S.blocksOfSize 6).filter fun b => p ∈ S.support b).card
  apply Finset.one_le_card.mpr
  refine ⟨Sum.inr c, Finset.mem_filter.mpr ⟨?_, ?_⟩⟩
  · exact S.mem_blocksOfSize.mpr R.selected_card
  · exact hp

/-- Summing the pointwise residue over the selected six labels. -/
theorem FourteenSixCircleResidualData.selected_rich_residue_sum
    {α : Type u} [Fintype α] [DecidableEq α]
    {cfg : Configuration α} {c : DeterminedCircle cfg}
    (R : FourteenSixCircleResidualData cfg c) :
    3 * (∑ p ∈ circleTrace cfg c.1,
        ((blockSystem cfg).blockDegree 4 p : ℤ)) +
      7 * (∑ p ∈ circleTrace cfg c.1,
        ((blockSystem cfg).blockDegree 5 p : ℤ)) +
      12 * (∑ p ∈ circleTrace cfg c.1,
        ((blockSystem cfg).blockDegree 6 p : ℤ)) +
      (∑ p ∈ circleTrace cfg c.1,
        (blockSystem cfg).pivotSigma p) = 450 := by
  have hsum :
      (∑ p ∈ circleTrace cfg c.1,
        (3 * ((blockSystem cfg).blockDegree 4 p : ℤ) +
          7 * ((blockSystem cfg).blockDegree 5 p : ℤ) +
          12 * ((blockSystem cfg).blockDegree 6 p : ℤ) +
          (blockSystem cfg).pivotSigma p)) =
        ∑ _p ∈ circleTrace cfg c.1, (75 : ℤ) := by
    apply Finset.sum_congr rfl
    intro p _hp
    exact (R.point_rows p).rich_residue_row
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum,
    Finset.sum_const] at hsum
  rw [R.selected_card] at hsum
  norm_num at hsum ⊢
  exact hsum

/-- Summing the same residue over the eight outsider labels. -/
theorem FourteenSixCircleResidualData.outside_rich_residue_sum
    {α : Type u} [Fintype α] [DecidableEq α]
    {cfg : Configuration α} {c : DeterminedCircle cfg}
    (R : FourteenSixCircleResidualData cfg c) :
    3 * (∑ p ∈ Finset.univ \ circleTrace cfg c.1,
        ((blockSystem cfg).blockDegree 4 p : ℤ)) +
      7 * (∑ p ∈ Finset.univ \ circleTrace cfg c.1,
        ((blockSystem cfg).blockDegree 5 p : ℤ)) +
      12 * (∑ p ∈ Finset.univ \ circleTrace cfg c.1,
        ((blockSystem cfg).blockDegree 6 p : ℤ)) +
      (∑ p ∈ Finset.univ \ circleTrace cfg c.1,
        (blockSystem cfg).pivotSigma p) = 600 := by
  have hsum :
      (∑ p ∈ Finset.univ \ circleTrace cfg c.1,
        (3 * ((blockSystem cfg).blockDegree 4 p : ℤ) +
          7 * ((blockSystem cfg).blockDegree 5 p : ℤ) +
          12 * ((blockSystem cfg).blockDegree 6 p : ℤ) +
          (blockSystem cfg).pivotSigma p)) =
        ∑ _p ∈ Finset.univ \ circleTrace cfg c.1, (75 : ℤ) := by
    apply Finset.sum_congr rfl
    intro p _hp
    exact (R.point_rows p).rich_residue_row
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum,
    Finset.sum_const] at hsum
  rw [R.outside_card] at hsum
  norm_num at hsum ⊢
  exact hsum

/-- The unused fourteen-point branch is deliberately independent of the
restricted Kelly window.  A future consumer may provide precisely these two
pointwise rows, without widening `RealPlaneKellyMoserPrinciple` to `n = 14`. -/
theorem FourteenSixCircleResidualData.explicit_ordinary_rows
    {α : Type u} [Fintype α] [DecidableEq α]
    {cfg : Configuration α} {c : DeterminedCircle cfg}
    (_R : FourteenSixCircleResidualData cfg c) (p : α)
    (hthree : 39 ≤ 7 * (blockSystem cfg).blockDegree 3 p)
    (hrestored : 42 ≤ 7 * ((blockSystem cfg).lineDegree 2 p +
      (blockSystem cfg).circleDegree 3 p)) :
    39 ≤ 7 * (blockSystem cfg).blockDegree 3 p ∧
      42 ≤ 7 * ((blockSystem cfg).lineDegree 2 p +
        (blockSystem cfg).circleDegree 3 p) := by
  exact ⟨hthree, hrestored⟩

/-- The application-specific added-centre row.  Its left side is exactly
the global defect plus three units for every circle block; at `C ≤ 72`
this is at most `140 + 3 * 72 = 356`. -/
theorem FourteenSixCircleResidualData.added_center_weight_le
    {α : Type u} [Fintype α] [DecidableEq α]
    {cfg : Configuration α} {c : DeterminedCircle cfg}
    (R : FourteenSixCircleResidualData cfg c) :
    Finset.univ.sum (fun b : GeometricBlock cfg =>
      (blockSystem cfg).blockDefectContribution b +
        (if (blockSystem cfg).kind b = .circle
          then (3 : ℤ) else 0)) ≤
      356 := by
  let S := blockSystem cfg
  have hcircle :
      Finset.univ.sum (fun b : GeometricBlock cfg =>
        (if S.kind b = .circle
          then (3 : ℤ) else 0)) =
        3 * (S.totalCircleCount : ℤ) := by
    rw [← Finset.sum_filter]
    simp [BlockSystem.totalCircleCount, BlockSystem.blocksOfKind]
    ring
  have htotal : S.totalCircleCount ≤ 72 := by
    rw [totalCircleCount_eq_card_determinedCircle,
      ← Erdos506.V3.circleCount_eq_card_determinedCircle]
    exact R.circle_count_le
  have htotalZ : (S.totalCircleCount : ℤ) ≤ 72 := by
    exact_mod_cast htotal
  rw [Finset.sum_add_distrib, ← S.defectRow_eq_sum_blockDefectContribution,
    hcircle]
  have hdefect : S.defectRow ≤ 140 := by
    simpa [S] using R.defect_row_le
  omega

/-- The exact two--two matching capacity gives the familiar Gamma-six
outside-pair range `0 ≤ W ≤ 84`. -/
theorem FourteenSixCircleResidualData.fourteenWeight_le_eighty_four
    {α : Type u} [Fintype α] [DecidableEq α]
    {cfg : Configuration α} {c : DeterminedCircle cfg}
    (R : FourteenSixCircleResidualData cfg c) :
    fourteenWeight (blockSystem cfg) (circleTrace cfg c.1) ≤ 84 := by
  have hcapacity := fourteenWeight_le_capacity
    (blockSystem cfg) (circleTrace cfg c.1)
  rw [R.point_card, R.selected_card] at hcapacity
  norm_num [Nat.choose] at hcapacity ⊢
  exact hcapacity

/-- The relative block-system weight is the semantic six-conic pair weight
on the full outsider set. -/
theorem FourteenSixCircleResidualData.fourteenWeight_eq_sixConicWeight
    {α : Type u} [Fintype α] [DecidableEq α]
    {cfg : Configuration α} {c : DeterminedCircle cfg}
    (_R : FourteenSixCircleResidualData cfg c) :
    fourteenWeight (blockSystem cfg) (circleTrace cfg c.1) =
      sixConicWeight cfg c
        (Finset.univ \ circleTrace cfg c.1) := by
  classical
  have houtside (d : DeterminedCircle cfg) :
      circleTrace cfg d.1 \ circleTrace cfg c.1 =
        circleTrace cfg d.1 ∩
          (Finset.univ \ circleTrace cfg c.1) := by
    ext p
    simp
  simp [fourteenWeight, fourteenTwoTraceCircles, fourteenInside,
    fourteenOutside, sixConicWeight, blockSystem,
    geometricBlockSystem, geometricBlockKind, geometricBlockSupport,
    Finset.sum_filter, houtside]

/-- Averaged U17 improves the purely finite matching cap from `84` to
`79` for the actual eight-outsider geometry. -/
theorem FourteenSixCircleResidualData.fourteenWeight_le_seventy_nine
    {α : Type u} [Fintype α] [DecidableEq α]
    {cfg : Configuration α} {c : DeterminedCircle cfg}
    (R : FourteenSixCircleResidualData cfg c) :
    fourteenWeight (blockSystem cfg) (circleTrace cfg c.1) ≤ 79 := by
  rw [R.fourteenWeight_eq_sixConicWeight]
  apply sixConic_weight_le_seventy_nine_of_card_eight
    cfg c R.selected_card
      (Finset.univ \ circleTrace cfg c.1) R.outside_card
  simp [Finset.disjoint_left]

/-- The real six-conic geometry sharpens the outsider line footprint from
the generic finite rows to `J ≤ 22`. -/
theorem FourteenSixCircleResidualData.line_incidence_le_twenty_two
    {α : Type u} [Fintype α] [DecidableEq α]
    {cfg : Configuration α} {c : DeterminedCircle cfg}
    (R : FourteenSixCircleResidualData cfg c) :
    sixConicLineIncidence cfg c
      (Finset.univ \ circleTrace cfg c.1) ≤ 22 := by
  apply sixConic_line_incidence_le_twenty_two_of_card_eight
    cfg c R.selected_card
      (Finset.univ \ circleTrace cfg c.1) R.outside_card
  simp [Finset.disjoint_left]

/-- Materialize the selected-six residual from an actual admissible
configuration and the contradictory circle-count bound. -/
theorem fourteenSixCircleResidualData_of_configuration
    {α : Type u} [Fintype α] [DecidableEq α]
    (Mel : RealPlaneMelchiorPrinciple.{u})
    (cfg : Configuration α) (hadm : Admissible cfg)
    (hcard : Fintype.card α = 14)
    (hcount : Erdos506.V4.circleCount cfg ≤ 72)
    (c : DeterminedCircle cfg)
    (hc : (circleTrace cfg c.1).card = 6) :
    FourteenSixCircleResidualData cfg c := by
  have hthree : 3 ≤ Fintype.card α := by omega
  have hpivot : ∀ p : α, 0 ≤ (blockSystem cfg).pivotSigma p := by
    intro p
    change 0 ≤ sigma cfg p
    exact sigma_nonneg_of_realPlaneMelchior Mel cfg hadm hthree p
  have hkappa : ∀ p : α, 0 ≤ (blockSystem cfg).restoredKappa p := by
    intro p
    change 0 ≤ kappa cfg p
    exact kappa_nonneg_of_realPlaneMelchior Mel cfg hadm hthree p
  have hno7 : NoSevenCircle cfg := by
    intro c' hc'
    exact no_seven_circle_of_fourteen_of_circleCount_le
      Mel cfg hadm hcard hcount c' hc'
  have hcap : BlockSizeCap (blockSystem cfg) 6 :=
    blockSizeCap_six_of_fourteen_of_circleCount_le
      cfg hadm hcard hcount hno7
  have hmomentD :
      18 ≤ (blockSystem cfg).subsetPivotMoment (circleTrace cfg c.1) := by
    have hmoment := (blockSystem cfg).three_mul_card_le_subsetPivotMoment
      (circleTrace cfg c.1) (fun p _hp => hpivot p)
    rw [hc] at hmoment
    norm_num at hmoment ⊢
    exact hmoment
  have hXcard : (Finset.univ \ circleTrace cfg c.1).card = 8 := by
    rw [Finset.card_sdiff_of_subset
      (Finset.subset_univ (circleTrace cfg c.1)), Finset.card_univ,
      hcard, hc]
  have hmomentX :
      24 ≤ (blockSystem cfg).subsetPivotMoment
        (Finset.univ \ circleTrace cfg c.1) := by
    have hmoment := (blockSystem cfg).three_mul_card_le_subsetPivotMoment
      (Finset.univ \ circleTrace cfg c.1) (fun p _hp => hpivot p)
    rw [hXcard] at hmoment
    norm_num at hmoment ⊢
    exact hmoment
  have hdefect : (blockSystem cfg).defectRow ≤ 140 := by
    have hrow := rowD_le_n_mul_n_sub_four_of_realPlaneMelchior
      Mel cfg hadm hthree
    change (blockSystem cfg).defectRow ≤
      (Fintype.card α : ℤ) * ((Fintype.card α : ℤ) - 4) at hrow
    rw [hcard] at hrow
    norm_num at hrow ⊢
    exact hrow
  have hinter : ∀ b : GeometricBlock cfg, b ≠ Sum.inr c →
      (geometricBlockSupport cfg b ∩ circleTrace cfg c.1).card ≤ 2 := by
    intro b hb
    have hlt := (blockSystem cfg).distinct_block_inter_card_lt_three hb
    change
      (geometricBlockSupport cfg b ∩ circleTrace cfg c.1).card < 3 at hlt
    omega
  exact ⟨hcard, hc, hcount, hcap, hpivot, hkappa, hmomentD, hXcard,
    hmomentX, hdefect, hinter⟩

/-- At fourteen labels the lossless finite-window block is literally either
a six-line or a selected six-circle. -/
theorem FiniteWindowRichBlockResidual.fourteen_block_cases
    {α : Type u} [Fintype α] [DecidableEq α]
    {cfg : Configuration α} (R : FiniteWindowRichBlockResidual cfg)
    (hcard : Fintype.card α = 14) :
    (∃ L : DeterminedLine cfg,
      R.block = Sum.inl L ∧ (lineSupport cfg L).card = 6) ∨
    (∃ c : DeterminedCircle cfg,
      R.block = Sum.inr c ∧ (circleTrace cfg c.1).card = 6) := by
  have hsix := R.fourteen_size hcard
  cases hblock : R.block with
  | inl L =>
      left
      refine ⟨L, rfl, ?_⟩
      rw [hblock] at hsix
      exact hsix
  | inr c =>
      right
      refine ⟨c, rfl, ?_⟩
      rw [hblock] at hsix
      exact hsix

/-- Configuration-level reduction of the `n=14` counterexample: the line
side remains an actual six-line, while the circle side is upgraded to all
of the unconditional selected-six rows above. -/
theorem fourteenSix_line_or_circleResidualData_of_counterexample
    {α : Type u} [Fintype α] [DecidableEq α]
    (Mel : RealPlaneMelchiorPrinciple.{u})
    (cfg : Configuration α) (hadm : Admissible cfg)
    (hcard : Fintype.card α = 14)
    (hcount : Erdos506.V4.circleCount cfg <
      Erdos506.v1UniformTarget (Fintype.card α)) :
    (∃ L : DeterminedLine cfg, (lineSupport cfg L).card = 6) ∨
      ∃ c : DeterminedCircle cfg, FourteenSixCircleResidualData cfg c := by
  have hmin : 14 ≤ Fintype.card α := by omega
  have hmax : Fintype.card α ≤ 22 := by omega
  let R := finiteWindowRichBlockResidual_of_counterexample
    Mel cfg hadm hmin hmax hcount
  have hcount72 : Erdos506.V4.circleCount cfg ≤ 72 := by
    rw [hcard] at hcount
    norm_num [Erdos506.v1UniformTarget, Nat.choose] at hcount
    omega
  rcases R.fourteen_block_cases hcard with
    ⟨L, _hblock, hL⟩ | ⟨c, _hblock, hc⟩
  · exact Or.inl ⟨L, hL⟩
  · exact Or.inr ⟨c,
      fourteenSixCircleResidualData_of_configuration
        Mel cfg hadm hcard hcount72 c hc⟩

end GeometricResidual

end Erdos506.V1
