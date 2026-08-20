import Erdos506.Incidence.EvenArrangementPrinciple
import Erdos506.V1.SmallReduction

/-!
# The eight-point V1 endpoint

The metric input in this endpoint is only the ordinary real-plane Melchior
principle.  The one extra topological input is kept explicit as
`RealPlaneEvenArrangementPrinciple`: an even non-pencil projective line
arrangement cannot have Melchior slack one.
-/

namespace Erdos506.V1

open Erdos506.Block
open Erdos506.Block.BlockSystem
open Erdos506.Finite
open Erdos506.Incidence
open Erdos506.V4
open scoped BigOperators

universe u

/-- The algebraic restored-centre quantity is exactly, not merely bounded by,
the Melchior slack of the restored inverted configuration. -/
theorem restoredKappa_eq_lineMelchiorSlack
    {α : Type*} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (p : α) :
    (geometricBlockSystem cfg).restoredKappa p =
      lineMelchiorSlack (restoredPivotConfiguration cfg p) := by
  classical
  have hsum :
      (∑ b : BlockThrough cfg p,
          (geometricBlockSystem cfg).restoredBlockWeight b.1) =
        ∑ L : DeterminedLine (restoredPivotConfiguration cfg p),
          (3 - ((lineSupport (restoredPivotConfiguration cfg p) L).card : ℤ)) := by
    apply Fintype.sum_equiv (blockRestoredLineEquiv cfg p)
    intro b
    exact (restoredWeight_blockToRestoredLine cfg p b).symm
  rw [(geometricBlockSystem cfg).restoredKappa_eq_sum_blockAt_weight_sub_three]
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

/-- Sixteen circles rule out every geometric block larger than four on eight
labels.  This is the common rich-block pencil calculation. -/
theorem blockSizeCap_four_of_card_eight_of_circleCount_le_sixteen
    {α : Type u} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (hadm : Admissible cfg)
    (hcard : Fintype.card α = 8)
    (hcount : Erdos506.V4.circleCount cfg ≤ 16) :
    BlockSizeCap (blockSystem cfg) 4 := by
  intro b hthree
  have hproper : ((blockSystem cfg).support b).card < Fintype.card α :=
    geometricBlockSupport_card_lt_of_admissible cfg hadm b
  by_contra hnot
  have hfive : 5 ≤ ((blockSystem cfg).support b).card := by omega
  have hpencil := richBlockPencilBound_le_totalCircleCount
    (blockSystem cfg) b hproper hthree
  rw [totalCircleCount_eq_card_determinedCircle,
    ← Erdos506.V3.circleCount_eq_card_determinedCircle] at hpencil
  rw [hcard] at hproper hpencil
  let s := ((blockSystem cfg).support b).card
  change richBlockPencilBound 8 s ≤ Erdos506.V4.circleCount cfg at hpencil
  change s < 8 at hproper
  change 5 ≤ s at hfive
  interval_cases s <;>
    norm_num [richBlockPencilBound, Nat.choose] at hpencil <;> omega

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

private theorem lineDegree_eq_zero_of_lineCount_eq_zero
    {Point Block : Type*} [Fintype Point] [Fintype Block]
    [DecidableEq Point]
    (S : BlockSystem Point Block) (s : ℕ) (p : Point)
    (hzero : S.lineCount s = 0) :
    S.lineDegree s p = 0 := by
  have hinc := S.line_incidence s
  rw [hzero] at hinc
  have hle : S.lineDegree s p ≤ ∑ q : Point, S.lineDegree s q := by
    exact Finset.single_le_sum
      (fun q _hq => Nat.zero_le (S.lineDegree s q)) (Finset.mem_univ p)
  omega

/-- The four exact scalar rows needed after the rich-pencil cap has reduced
the census to support sizes three and four. -/
private theorem eight_global_rows
    {α : Type u} [Fintype α] [DecidableEq α]
    (Mel : RealPlaneMelchiorPrinciple.{u})
    (cfg : Configuration α) (hadm : Admissible cfg)
    (hcard : Fintype.card α = 8)
    (hcount : Erdos506.V4.circleCount cfg ≤ 16) :
    let S := blockSystem cfg
    ((S.blockCount 3 : ℤ) + 4 * (S.blockCount 4 : ℤ) = 56) ∧
    ((∑ p : α, S.pivotSigma p) =
      144 - 12 * (S.blockCount 4 : ℤ)) ∧
    ((∑ p : α, S.restoredKappa p) =
      200 - 12 * (S.blockCount 4 : ℤ) -
        9 * (S.lineCount 3 : ℤ) - 16 * (S.lineCount 4 : ℤ)) ∧
    (9 * (S.lineCount 3 : ℤ) + 16 * (S.lineCount 4 : ℤ) ≤
      200 - 12 * (S.blockCount 4 : ℤ)) ∧
    ((S.totalCircleCount : ℤ) =
      56 - 3 * (S.blockCount 4 : ℤ) -
        (S.lineCount 3 : ℤ) - (S.lineCount 4 : ℤ)) := by
  classical
  dsimp only
  let S := blockSystem cfg
  have hcap : BlockSizeCap S 4 := by
    simpa [S] using
      blockSizeCap_four_of_card_eight_of_circleCount_le_sixteen
        cfg hadm hcard hcount
  have hb5 : S.blockCount 5 = 0 :=
    blockCount_eq_zero_of_cap S hcap (by omega) (by omega)
  have hb6 : S.blockCount 6 = 0 :=
    blockCount_eq_zero_of_cap S hcap (by omega) (by omega)
  have hb7 : S.blockCount 7 = 0 :=
    blockCount_eq_zero_of_cap S hcap (by omega) (by omega)
  have hb8 : S.blockCount 8 = 0 :=
    blockCount_eq_zero_of_cap S hcap (by omega) (by omega)
  have hl5 : S.lineCount 5 = 0 :=
    lineCount_eq_zero_of_cap S hcap (by omega) (by omega)
  have hl6 : S.lineCount 6 = 0 :=
    lineCount_eq_zero_of_cap S hcap (by omega) (by omega)
  have hl7 : S.lineCount 7 = 0 :=
    lineCount_eq_zero_of_cap S hcap (by omega) (by omega)
  have hl8 : S.lineCount 8 = 0 :=
    lineCount_eq_zero_of_cap S hcap (by omega) (by omega)
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
  have hT := S.triple_partition_by_size
  rw [hcard] at hT
  norm_num [Finset.sum_range_succ, Nat.choose, hb5, hb6, hb7, hb8] at hT
  have hTz :
      (S.blockCount 3 : ℤ) + 4 * (S.blockCount 4 : ℤ) = 56 := by
    exact_mod_cast hT
  have hsumSigma := S.sum_pivotSigma_eq_pivotRow_sub_three_n
  simp only [BlockSystem.pivotRow, BlockSystem.nontrivialSizes] at hsumSigma
  rw [hcard] at hsumSigma
  have hIcc : Finset.Icc 3 8 = {3, 4, 5, 6, 7, 8} := by decide
  rw [hIcc] at hsumSigma
  norm_num [hb5, hb6, hb7, hb8] at hsumSigma
  have hSigma :
      (∑ p : α, S.pivotSigma p) =
        144 - 12 * (S.blockCount 4 : ℤ) := by
    omega
  have hD := rowD_le_n_mul_n_sub_four_of_realPlaneMelchior
    (α := α) Mel cfg hadm (by omega)
  change S.defectRow ≤
    (Fintype.card α : ℤ) * ((Fintype.card α : ℤ) - 4) at hD
  simp only [BlockSystem.defectRow, BlockSystem.nontrivialSizes] at hD
  rw [hcard, hIcc] at hD
  norm_num [hl5, hl6, hl7, hl8, hc5, hc6, hc7, hc8] at hD
  have hsplit3 := S.blockCount_eq_lineCount_add_circleCount 3
  have hsplit4 := S.blockCount_eq_lineCount_add_circleCount 4
  have hsumKappa := S.sum_restoredKappa_eq_n_mul_n_sub_four_sub_defectRow
  simp only [BlockSystem.defectRow, BlockSystem.nontrivialSizes] at hsumKappa
  rw [hcard, hIcc] at hsumKappa
  norm_num [hl5, hl6, hl7, hl8, hc5, hc6, hc7, hc8] at hsumKappa
  have hKappa :
      (∑ p : α, S.restoredKappa p) =
        200 - 12 * (S.blockCount 4 : ℤ) -
          9 * (S.lineCount 3 : ℤ) - 16 * (S.lineCount 4 : ℤ) := by
    omega
  have hAdded :
      9 * (S.lineCount 3 : ℤ) + 16 * (S.lineCount 4 : ℤ) ≤
        200 - 12 * (S.blockCount 4 : ℤ) := by
    omega
  have htotalEq := S.totalCircleCount_eq_sum_circleCount
  rw [hcard] at htotalEq
  norm_num [Finset.sum_range_succ, hc0, hc1, hc2, hc5, hc6, hc7, hc8]
    at htotalEq
  have htotalZ :
      (S.totalCircleCount : ℤ) =
        56 - 3 * (S.blockCount 4 : ℤ) -
          (S.lineCount 3 : ℤ) - (S.lineCount 4 : ℤ) := by
    omega
  exact ⟨hTz, hSigma, hKappa, hAdded, htotalZ⟩

/-- Pointwise forms of triple ownership, pivot slack, and restored slack under
the size-four cap. -/
private theorem eight_local_rows
    {Point Block : Type*} [Fintype Point] [Fintype Block]
    [DecidableEq Point]
    (S : BlockSystem Point Block) (hcard : Fintype.card Point = 8)
    (hcap : BlockSizeCap S 4) (p : Point) :
    S.blockDegree 3 p + 3 * S.blockDegree 4 p = 21 ∧
    S.pivotSigma p = 18 - 3 * (S.blockDegree 4 p : ℤ) ∧
    S.restoredKappa p =
      7 + S.pivotSigma p - 3 * (S.lineDegree 3 p : ℤ) -
        4 * (S.lineDegree 4 p : ℤ) := by
  have hb5 : S.blockCount 5 = 0 :=
    blockCount_eq_zero_of_cap S hcap (by omega) (by omega)
  have hb6 : S.blockCount 6 = 0 :=
    blockCount_eq_zero_of_cap S hcap (by omega) (by omega)
  have hb7 : S.blockCount 7 = 0 :=
    blockCount_eq_zero_of_cap S hcap (by omega) (by omega)
  have hb8 : S.blockCount 8 = 0 :=
    blockCount_eq_zero_of_cap S hcap (by omega) (by omega)
  have hl5 : S.lineCount 5 = 0 :=
    lineCount_eq_zero_of_cap S hcap (by omega) (by omega)
  have hl6 : S.lineCount 6 = 0 :=
    lineCount_eq_zero_of_cap S hcap (by omega) (by omega)
  have hl7 : S.lineCount 7 = 0 :=
    lineCount_eq_zero_of_cap S hcap (by omega) (by omega)
  have hl8 : S.lineCount 8 = 0 :=
    lineCount_eq_zero_of_cap S hcap (by omega) (by omega)
  have hd5 := blockDegree_eq_zero_of_blockCount_eq_zero S 5 p hb5
  have hd6 := blockDegree_eq_zero_of_blockCount_eq_zero S 6 p hb6
  have hd7 := blockDegree_eq_zero_of_blockCount_eq_zero S 7 p hb7
  have hd8 := blockDegree_eq_zero_of_blockCount_eq_zero S 8 p hb8
  have hld5 := lineDegree_eq_zero_of_lineCount_eq_zero S 5 p hl5
  have hld6 := lineDegree_eq_zero_of_lineCount_eq_zero S 6 p hl6
  have hld7 := lineDegree_eq_zero_of_lineCount_eq_zero S 7 p hl7
  have hld8 := lineDegree_eq_zero_of_lineCount_eq_zero S 8 p hl8
  have hpairs := S.pivot_pair_partition p
  rw [hcard] at hpairs
  norm_num [Finset.sum_range_succ, Nat.choose, hd5, hd6, hd7, hd8] at hpairs
  have hsigma :
      S.pivotSigma p = 18 - 3 * (S.blockDegree 4 p : ℤ) := by
    unfold BlockSystem.pivotSigma BlockSystem.nontrivialSizes
    rw [hcard]
    have hIcc : Finset.Icc 3 8 = {3, 4, 5, 6, 7, 8} := by decide
    rw [hIcc]
    norm_num [hd5, hd6, hd7, hd8]
    omega
  have hkappa :
      S.restoredKappa p =
        7 + S.pivotSigma p - 3 * (S.lineDegree 3 p : ℤ) -
          4 * (S.lineDegree 4 p : ℤ) := by
    unfold BlockSystem.restoredKappa BlockSystem.nontrivialSizes
    rw [hcard]
    have hIcc : Finset.Icc 3 8 = {3, 4, 5, 6, 7, 8} := by decide
    rw [hIcc]
    norm_num [hld5, hld6, hld7, hld8]
    ring
  exact ⟨hpairs, hsigma, hkappa⟩

private theorem eq_one_of_le_one_of_sum_eq_card
    {α : Type*} [Fintype α] [DecidableEq α]
    (f : α → ℕ) (hle : ∀ p, f p ≤ 1)
    (hsum : (∑ p : α, f p) = Fintype.card α) :
    ∀ p, f p = 1 := by
  classical
  have hpoint (q : α) : f q + (1 - f q) = 1 := by
    have := hle q
    omega
  have hsumComplement : (∑ q : α, (1 - f q)) = 0 := by
    have hadd :
        Fintype.card α + (∑ q : α, (1 - f q)) = Fintype.card α := by
      calc
        Fintype.card α + (∑ q : α, (1 - f q)) =
            (∑ q : α, f q) + ∑ q : α, (1 - f q) := by rw [hsum]
        _ = ∑ q : α, (f q + (1 - f q)) :=
          Finset.sum_add_distrib.symm
        _ = ∑ _q : α, 1 := by
          apply Fintype.sum_congr
          exact hpoint
        _ = Fintype.card α := by simp
    have hc :
        Fintype.card α + (∑ q : α, (1 - f q)) = Fintype.card α + 0 := by
      simpa using hadd
    exact Nat.add_left_cancel hc
  intro p
  have hterm : 1 - f p ≤ ∑ q : α, (1 - f q) := by
    exact Finset.single_le_sum
      (fun q _hq => Nat.zero_le (1 - f q)) (Finset.mem_univ p)
  rw [hsumComplement] at hterm
  have hpLe := hle p
  omega

/-- The terminal line pattern forced in the `b = 12` branch is impossible:
two four-lines cover all points, so a three-line meets one of them twice. -/
private theorem no_two_three_lines_two_four_lines_of_four_degree_pos
    {Point Block : Type*} [Fintype Point] [Fintype Block]
    [DecidableEq Point]
    (S : BlockSystem Point Block)
    (hl3 : S.lineCount 3 = 2) (hl4 : S.lineCount 4 = 2)
    (hdegree : ∀ p : Point, 1 ≤ S.lineDegree 4 p) : False := by
  classical
  let F3 := S.lineBlocksOfSize 3
  let F4 := S.lineBlocksOfSize 4
  have hF3card : F3.card = 2 := by simpa [F3, BlockSystem.lineCount] using hl3
  have hF4card : F4.card = 2 := by simpa [F4, BlockSystem.lineCount] using hl4
  obtain ⟨a, b, hab, hF4⟩ := Finset.card_eq_two.mp hF4card
  have haMem : a ∈ F4 := by rw [hF4]; simp
  have hbMem : b ∈ F4 := by rw [hF4]; simp
  have haSpec := S.mem_blocksOfKindSize.mp haMem
  have hbSpec := S.mem_blocksOfKindSize.mp hbMem
  have hcover (p : Point) : p ∈ S.support a ∪ S.support b := by
    have hpos : 0 < S.lineDegree 4 p := hdegree p
    change 0 < (S.degreeIn F4 p) at hpos
    unfold BlockSystem.degreeIn at hpos
    obtain ⟨l, hl⟩ := Finset.card_pos.mp hpos
    have hlspec := Finset.mem_filter.mp hl
    rw [hF4] at hlspec
    have hlab : l = a ∨ l = b := by simpa using hlspec.1
    rcases hlab with rfl | rfl
    · exact Finset.mem_union_left _ hlspec.2
    · exact Finset.mem_union_right _ hlspec.2
  have hF3pos : 0 < F3.card := by omega
  obtain ⟨t, htMem⟩ := Finset.card_pos.mp hF3pos
  have htSpec := S.mem_blocksOfKindSize.mp htMem
  have htSub : S.support t ⊆ S.support a ∪ S.support b := by
    intro p hp
    exact hcover p
  have hdecomp :
      S.support t =
        (S.support t ∩ S.support a) ∪ (S.support t ∩ S.support b) := by
    ext p
    constructor
    · intro hp
      have hpab := htSub hp
      rcases Finset.mem_union.mp hpab with hpa | hpb
      · exact Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨hp, hpa⟩)
      · exact Finset.mem_union_right _ (Finset.mem_inter.mpr ⟨hp, hpb⟩)
    · intro hp
      rcases Finset.mem_union.mp hp with hpa | hpb
      · exact (Finset.mem_inter.mp hpa).1
      · exact (Finset.mem_inter.mp hpb).1
  have hinter :
      2 ≤ (S.support t ∩ S.support a).card ∨
        2 ≤ (S.support t ∩ S.support b).card := by
    by_contra hnot
    simp only [not_or, not_le] at hnot
    have hunion := Finset.card_union_le
      (S.support t ∩ S.support a) (S.support t ∩ S.support b)
    rw [← hdecomp] at hunion
    omega
  rcases hinter with hinter | hinter
  · have hta : t ≠ a := by
      intro h
      rw [h] at htSpec
      omega
    let lt : LineBlock S := ⟨t, htSpec.1⟩
    let la : LineBlock S := ⟨a, haSpec.1⟩
    have hne : lt ≠ la := by
      intro h
      exact hta (congrArg Subtype.val h)
    have hlt := S.distinct_line_inter_card_lt_two hne
    have hlt' : (S.support t ∩ S.support a).card < 2 := by
      simpa [lt, la] using hlt
    omega
  · have htb : t ≠ b := by
      intro h
      rw [h] at htSpec
      omega
    let lt : LineBlock S := ⟨t, htSpec.1⟩
    let lb : LineBlock S := ⟨b, hbSpec.1⟩
    have hne : lt ≠ lb := by
      intro h
      exact htb (congrArg Subtype.val h)
    have hlt := S.distinct_line_inter_card_lt_two hne
    have hlt' : (S.support t ∩ S.support b).card < 2 := by
      simpa [lt, lb] using hlt
    omega

/-- Every admissible eight-point V1 configuration determines at least
seventeen proper circles, conditional only on the two explicit real-plane
arrangement principles. -/
theorem circleCount_ge_target_of_card_eight
    {α : Type u} [Fintype α] [DecidableEq α]
    (Mel : RealPlaneMelchiorPrinciple.{u})
    (EvenArr : RealPlaneEvenArrangementPrinciple.{u})
    (cfg : Configuration α) (hadm : Admissible cfg)
    (hcard : Fintype.card α = 8) :
    17 ≤ Erdos506.V4.circleCount cfg := by
  classical
  by_cases hfour : Erdos506.V4.NoFourConcyclic cfg
  · have hv4 := Erdos506.V4.circleCount_ge_target cfg (by omega)
      ⟨hadm.1, hfour⟩
    rw [hcard] at hv4
    norm_num [Erdos506.v4Target, Nat.choose] at hv4
    omega
  · by_contra hnot
    have hcount : Erdos506.V4.circleCount cfg ≤ 16 := by omega
    let S := blockSystem cfg
    have hcap : BlockSizeCap S 4 := by
      simpa [S] using
        blockSizeCap_four_of_card_eight_of_circleCount_le_sixteen
          cfg hadm hcard hcount
    have hrows :
        ((S.blockCount 3 : ℤ) + 4 * (S.blockCount 4 : ℤ) = 56) ∧
        ((∑ p : α, S.pivotSigma p) =
          144 - 12 * (S.blockCount 4 : ℤ)) ∧
        ((∑ p : α, S.restoredKappa p) =
          200 - 12 * (S.blockCount 4 : ℤ) -
            9 * (S.lineCount 3 : ℤ) - 16 * (S.lineCount 4 : ℤ)) ∧
        (9 * (S.lineCount 3 : ℤ) + 16 * (S.lineCount 4 : ℤ) ≤
          200 - 12 * (S.blockCount 4 : ℤ)) ∧
        ((S.totalCircleCount : ℤ) =
          56 - 3 * (S.blockCount 4 : ℤ) -
            (S.lineCount 3 : ℤ) - (S.lineCount 4 : ℤ)) := by
      simpa [S] using eight_global_rows Mel cfg hadm hcard hcount
    rcases hrows with
      ⟨hT, hSigma, hKappa, hAdded, hTotal⟩
    have htotalLe : S.totalCircleCount ≤ 16 := by
      rw [totalCircleCount_eq_card_determinedCircle,
        ← Erdos506.V3.circleCount_eq_card_determinedCircle]
      exact hcount
    have hsigmaNonneg (p : α) : 0 ≤ S.pivotSigma p := by
      have h := sigma_nonneg_of_realPlaneMelchior
        (α := α) Mel cfg hadm (by omega) p
      simpa [S, sigma] using h
    have hkappaNonneg (p : α) : 0 ≤ S.restoredKappa p := by
      have h := kappa_nonneg_of_realPlaneMelchior
        (α := α) Mel cfg hadm (by omega) p
      simpa [S, kappa] using h
    have hsumSigmaNonneg : 0 ≤ ∑ p : α, S.pivotSigma p :=
      Finset.sum_nonneg fun p _hp => hsigmaNonneg p
    have hb : S.blockCount 4 = 11 ∨ S.blockCount 4 = 12 := by
      omega
    rcases hb with hb | hb
    · have hlines : S.lineCount 3 = 7 ∧ S.lineCount 4 = 0 := by
        omega
      rcases hlines with ⟨hl3, hl4⟩
      have hsumKappa : (∑ p : α, S.restoredKappa p) = 5 := by
        omega
      have hkappaPos (p : α) : 1 ≤ S.restoredKappa p := by
        rcases eight_local_rows S hcard hcap p with
          ⟨_hpairs, hsigma, hkappa⟩
        have hld4 := lineDegree_eq_zero_of_lineCount_eq_zero S 4 p hl4
        have hnonneg := hkappaNonneg p
        omega
      have hsumLower :
          (8 : ℤ) ≤ ∑ p : α, S.restoredKappa p := by
        calc
          (8 : ℤ) = ∑ _p : α, (1 : ℤ) := by simp [hcard]
          _ ≤ ∑ p : α, S.restoredKappa p :=
            Finset.sum_le_sum fun p _hp => hkappaPos p
      omega
    · have hsumSigma : (∑ p : α, S.pivotSigma p) = 0 := by
        omega
      have hsigmaZero (p : α) : S.pivotSigma p = 0 := by
        have hle : S.pivotSigma p ≤ ∑ q : α, S.pivotSigma q := by
          exact Finset.single_le_sum
            (fun q _hq => hsigmaNonneg q) (Finset.mem_univ p)
        rw [hsumSigma] at hle
        have hnonneg := hsigmaNonneg p
        omega
      have hkappaNeOne (p : α) : S.restoredKappa p ≠ 1 := by
        have hnoncol : Noncollinear (restoredPivotConfiguration cfg p) :=
          restoredPivotConfiguration_noncollinear cfg hadm (by omega) p
        have hrestCard :
            Fintype.card (Option (Erdos506.V3.AwayFrom p)) = 8 := by
          simp [hcard]
        have heven : Even (Fintype.card (Option (Erdos506.V3.AwayFrom p))) := by
          rw [hrestCard]
          norm_num
        have hne := EvenArr.slack_ne_one
          (restoredPivotConfiguration cfg p) hnoncol heven
        rw [← restoredKappa_eq_lineMelchiorSlack cfg p] at hne
        simpa [S] using hne
      have hlineDegree3Le (p : α) : S.lineDegree 3 p ≤ 1 := by
        rcases eight_local_rows S hcard hcap p with
          ⟨_hpairs, _hsigma, hkappa⟩
        have hnonneg := hkappaNonneg p
        have hzero := hsigmaZero p
        have hne := hkappaNeOne p
        omega
      have hlineDegree4Le (p : α) : S.lineDegree 4 p ≤ 1 := by
        rcases eight_local_rows S hcard hcap p with
          ⟨_hpairs, _hsigma, hkappa⟩
        have hnonneg := hkappaNonneg p
        have hzero := hsigmaZero p
        omega
      have hsumDegree3 : (∑ p : α, S.lineDegree 3 p) ≤ 8 := by
        calc
          (∑ p : α, S.lineDegree 3 p) ≤ ∑ _p : α, 1 :=
            Finset.sum_le_sum fun p _hp => hlineDegree3Le p
          _ = 8 := by simp [hcard]
      have hinc3 := S.line_incidence 3
      have hl3le : S.lineCount 3 ≤ 2 := by omega
      have hlines : S.lineCount 3 = 2 ∧ S.lineCount 4 = 2 := by
        omega
      rcases hlines with ⟨hl3, hl4⟩
      have hinc4 := S.line_incidence 4
      have hsumDegree4 :
          (∑ p : α, S.lineDegree 4 p) = Fintype.card α := by
        rw [hinc4, hl4, hcard]
      have hdegree4One : ∀ p : α, S.lineDegree 4 p = 1 :=
        eq_one_of_le_one_of_sum_eq_card
          (fun p : α => S.lineDegree 4 p) hlineDegree4Le hsumDegree4
      exact no_two_three_lines_two_four_lines_of_four_degree_pos
        S hl3 hl4 (fun p => by rw [hdegree4One p])

end Erdos506.V1
