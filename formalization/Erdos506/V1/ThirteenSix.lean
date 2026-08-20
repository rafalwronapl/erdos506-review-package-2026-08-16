import Erdos506.Incidence.OrdinaryPrinciples
import Erdos506.Incidence.SixConicEventsPrinciple
import Erdos506.V1.FiniteCaps
import Erdos506.V1.FourteenSelected
import Erdos506.V1.ThirteenSixOpening

/-!
# The thirteen-point selected-six-circle certificate

This module checks the integer end of the manuscript's `n = 13`, selected
six-circle argument.  It also derives the relative triple rows, the two
class pivot bounds, the global defect bound, and the ordinary-circle row
directly from the existing block-system and real-plane principles.

The geometric six-conic event theorem is deliberately not smuggled into
the arithmetic statement.  The remaining transport has two named parts:

* the S1/S2 signature-and-host conclusions must supply the repetition
  bounds in `ThirteenSixCapacityGapConditions`;
* the retained second-dual and conservation identities must supply its
  remaining fields and `ThirteenSixTerminalConditions`.

None of the structures below contains a circle-count endpoint or a field of
type `False`.
-/

namespace Erdos506.V1

open Erdos506.Block
open Erdos506.Block.BlockSystem
open Erdos506.Incidence
open Erdos506.V4
open scoped BigOperators

universe u v

section CheckedConfigurationRows

variable {Point : Type u} {Block : Type v}
  [Fintype Point] [Fintype Block] [DecidableEq Point]

private theorem thirteenSix_blockCount_eq_zero_of_cap
    (S : BlockSystem Point Block) {M s : Nat}
    (hcap : BlockSizeCap S M) (hthree : 3 <= s) (hlarge : M < s) :
    S.blockCount s = 0 := by
  classical
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro b hb
  have hsize := S.mem_blocksOfSize.mp hb
  have hle := hcap b (by omega)
  omega

/-- Number of labels of a block on the selected six-circle. -/
abbrev thirteenSixInside (S : BlockSystem Point Block)
    (D : Finset Point) (b : Block) : Nat :=
  fourteenInside S D b

/-- Number of labels of a block outside the selected six-circle. -/
abbrev thirteenSixOutside (S : BlockSystem Point Block)
    (D : Finset Point) (b : Block) : Nat :=
  fourteenOutside S D b

/-- The paper's outside-pair weight
`W = sum_j choose(j,2) c(2,j)`. -/
abbrev thirteenSixWeight (S : BlockSystem Point Block)
    (D : Finset Point) : Nat :=
  fourteenWeight S D

/-- The relative block-system definition of `W` agrees with the semantic
sum over determined circles used by the six-conic-events interface. -/
theorem thirteenSixWeight_eq_sixConicWeight
    {α : Type u} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (gamma : DeterminedCircle cfg) :
    thirteenSixWeight (blockSystem cfg) (circleTrace cfg gamma.1) =
      sixConicWeight cfg gamma
        (Finset.univ \ circleTrace cfg gamma.1) := by
  classical
  have houtside (c : DeterminedCircle cfg) :
      circleTrace cfg c.1 \ circleTrace cfg gamma.1 =
        circleTrace cfg c.1 ∩
          (Finset.univ \ circleTrace cfg gamma.1) := by
    ext p
    simp
  simp [thirteenSixWeight, fourteenWeight, fourteenTwoTraceCircles,
    fourteenInside, fourteenOutside, sixConicWeight,
    blockSystem, geometricBlockSystem, geometricBlockKind,
    geometricBlockSupport, Finset.sum_filter, houtside]

/-- The four relative triple totals at the six--seven split are exactly
`(35,126,105,20)`, in increasing order of the number of selected-circle
labels. -/
theorem thirteenSix_relative_rows
    (S : BlockSystem Point Block) (D : Finset Point)
    (hpoint : Fintype.card Point = 13) (hD : D.card = 6) :
    (∑ b : Block, (Nat.choose (thirteenSixOutside S D b) 3 : Int)) = 35 /\
    (∑ b : Block,
      (thirteenSixInside S D b : Int) *
        (Nat.choose (thirteenSixOutside S D b) 2 : Int)) = 126 /\
    (∑ b : Block,
      (Nat.choose (thirteenSixInside S D b) 2 : Int) *
        (thirteenSixOutside S D b : Int)) = 105 /\
    (∑ b : Block, (Nat.choose (thirteenSixInside S D b) 3 : Int)) = 20 := by
  have h0 := S.relative_triple_partition D 0 (by omega)
  have h1 := S.relative_triple_partition D 1 (by omega)
  have h2 := S.relative_triple_partition D 2 (by omega)
  have h3 := S.relative_triple_partition D 3 (by omega)
  rw [hpoint, hD] at h0 h1 h2 h3
  norm_num [thirteenSixInside, thirteenSixOutside, fourteenInside,
    fourteenOutside, Nat.choose] at h0 h1 h2 h3
  constructor
  · exact_mod_cast h0
  constructor
  · exact_mod_cast h1
  constructor
  · exact_mod_cast h2
  · exact_mod_cast h3

/-- At thirteen points, the cap-six triple census together with the global
Melchior pivot and defect rows forces at least thirteen three-circles. -/
theorem thirteen_circleCount_three_ge_thirteen_of_cap_six
    (S : BlockSystem Point Block)
    (hcard : Fintype.card Point = 13)
    (hcap : BlockSizeCap S 6)
    (hC : S.totalCircleCount <= 60)
    (hP : (39 : Int) <= S.pivotRow)
    (hD : S.defectRow <= 117) :
    13 <= S.circleCount 3 := by
  classical
  have hb7 := thirteenSix_blockCount_eq_zero_of_cap S hcap
    (s := 7) (by omega) (by omega)
  have hb8 := thirteenSix_blockCount_eq_zero_of_cap S hcap
    (s := 8) (by omega) (by omega)
  have hb9 := thirteenSix_blockCount_eq_zero_of_cap S hcap
    (s := 9) (by omega) (by omega)
  have hb10 := thirteenSix_blockCount_eq_zero_of_cap S hcap
    (s := 10) (by omega) (by omega)
  have hb11 := thirteenSix_blockCount_eq_zero_of_cap S hcap
    (s := 11) (by omega) (by omega)
  have hb12 := thirteenSix_blockCount_eq_zero_of_cap S hcap
    (s := 12) (by omega) (by omega)
  have hb13 := thirteenSix_blockCount_eq_zero_of_cap S hcap
    (s := 13) (by omega) (by omega)
  have hsplit7 := S.blockCount_eq_lineCount_add_circleCount 7
  have hsplit8 := S.blockCount_eq_lineCount_add_circleCount 8
  have hsplit9 := S.blockCount_eq_lineCount_add_circleCount 9
  have hsplit10 := S.blockCount_eq_lineCount_add_circleCount 10
  have hsplit11 := S.blockCount_eq_lineCount_add_circleCount 11
  have hsplit12 := S.blockCount_eq_lineCount_add_circleCount 12
  have hsplit13 := S.blockCount_eq_lineCount_add_circleCount 13
  have hl7 : S.lineCount 7 = 0 := by omega
  have hl8 : S.lineCount 8 = 0 := by omega
  have hl9 : S.lineCount 9 = 0 := by omega
  have hl10 : S.lineCount 10 = 0 := by omega
  have hl11 : S.lineCount 11 = 0 := by omega
  have hl12 : S.lineCount 12 = 0 := by omega
  have hl13 : S.lineCount 13 = 0 := by omega
  have hc7 : S.circleCount 7 = 0 := by omega
  have hc8 : S.circleCount 8 = 0 := by omega
  have hc9 : S.circleCount 9 = 0 := by omega
  have hc10 : S.circleCount 10 = 0 := by omega
  have hc11 : S.circleCount 11 = 0 := by omega
  have hc12 : S.circleCount 12 = 0 := by omega
  have hc13 : S.circleCount 13 = 0 := by omega
  have hc0 : S.circleCount 0 = 0 :=
    S.circleCount_eq_zero_of_lt_three (by omega)
  have hc1 : S.circleCount 1 = 0 :=
    S.circleCount_eq_zero_of_lt_three (by omega)
  have hc2 : S.circleCount 2 = 0 :=
    S.circleCount_eq_zero_of_lt_three (by omega)
  have hT := S.triple_partition_by_size
  rw [hcard] at hT
  norm_num [Finset.sum_range_succ, Nat.choose,
    hb7, hb8, hb9, hb10, hb11, hb12, hb13] at hT
  have htotal := S.totalCircleCount_eq_sum_circleCount
  rw [hcard] at htotal
  norm_num [Finset.sum_range_succ,
    hc0, hc1, hc2, hc7, hc8, hc9, hc10, hc11, hc12, hc13] at htotal
  have hIcc : Finset.Icc 3 13 =
      {3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13} := by
    decide
  unfold BlockSystem.pivotRow BlockSystem.nontrivialSizes at hP
  rw [hcard, hIcc] at hP
  norm_num [hb7, hb8, hb9, hb10, hb11, hb12, hb13] at hP
  unfold BlockSystem.defectRow BlockSystem.nontrivialSizes at hD
  rw [hcard, hIcc] at hD
  norm_num [hl7, hl8, hl9, hl10, hl11, hl12, hl13,
    hc7, hc8, hc9, hc10, hc11, hc12, hc13] at hD
  have hsplit3 := S.blockCount_eq_lineCount_add_circleCount 3
  have hsplit4 := S.blockCount_eq_lineCount_add_circleCount 4
  have hsplit5 := S.blockCount_eq_lineCount_add_circleCount 5
  have hsplit6 := S.blockCount_eq_lineCount_add_circleCount 6
  by_contra hnot
  have hc3 : S.circleCount 3 = 12 := by omega
  have hl4 : S.lineCount 4 = 0 := by omega
  have hl5 : S.lineCount 5 = 0 := by omega
  have hl6 : S.lineCount 6 = 0 := by omega
  have hc5 : S.circleCount 5 <= 1 := by omega
  by_cases hfive : S.circleCount 5 = 0
  · omega
  · have hfiveOne : S.circleCount 5 = 1 := by omega
    omega

/-- Melchior on the six selected labels and seven outside labels gives the
paper's class-pivot bounds `M_Gamma >= 18` and `M_X >= 21`. -/
theorem thirteenSix_class_pivot_bounds
    {α : Type u} [Fintype α] [DecidableEq α]
    (Mel : RealPlaneMelchiorPrinciple.{u})
    (cfg : Configuration α) (hadm : Admissible cfg)
    (hcard : Fintype.card α = 13) (D : Finset α)
    (hD : D.card = 6) :
    18 <= (blockSystem cfg).subsetPivotMoment D /\
      21 <= (blockSystem cfg).subsetPivotMoment (Finset.univ \ D) := by
  have hthree : 3 <= Fintype.card α := by omega
  have hGamma := (blockSystem cfg).three_mul_card_le_subsetPivotMoment D
    (fun p _hp => sigma_nonneg_of_realPlaneMelchior
      Mel cfg hadm hthree p)
  have hXcard : (Finset.univ \ D).card = 7 := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ D),
      Finset.card_univ, hcard, hD]
  have hX := (blockSystem cfg).three_mul_card_le_subsetPivotMoment
    (Finset.univ \ D) (fun p _hp =>
      sigma_nonneg_of_realPlaneMelchior Mel cfg hadm hthree p)
  rw [hD] at hGamma
  rw [hXcard] at hX
  norm_num at hGamma hX ⊢
  exact ⟨hGamma, hX⟩

/-- At thirteen points the global restored-centre defect row satisfies
`D <= 117`. -/
theorem thirteenSix_defectRow_le_one_hundred_seventeen
    {α : Type u} [Fintype α] [DecidableEq α]
    (Mel : RealPlaneMelchiorPrinciple.{u})
    (cfg : Configuration α) (hadm : Admissible cfg)
    (hcard : Fintype.card α = 13) :
    (blockSystem cfg).defectRow <= 117 := by
  have hrow := rowD_le_n_mul_n_sub_four_of_realPlaneMelchior
    Mel cfg hadm (by omega)
  change (blockSystem cfg).defectRow <=
    (Fintype.card α : Int) * ((Fintype.card α : Int) - 4) at hrow
  rw [hcard] at hrow
  norm_num at hrow ⊢
  exact hrow

end CheckedConfigurationRows

section RetainedOpeningBridge

/-- The four retained rows not yet reconstructed coefficientwise at the
configuration level.  `defect` is the actual signed block defect row; all
other variables have the meanings fixed in `ThirteenSixOpeningConditions`.

This interface is narrower than the opening conclusion: it contains the
dual comparison, the equality-wall budget, the local residual gap, and the
zero-layer identity, but no lower bound for `W`.
-/
structure ThirteenSixRetainedOpeningRows
    (defect : Int) (C O MX W R f : Nat) : Prop where
  openingDual :
    (33810 : Int) - 414 * (W : Int) <= 123 * defect
  retainedBudget : W = 47 ->
    R + 79 * (O - 39) + 199 * (MX - 21) + 1344 * (60 - C) <= 39
  residualGap : R = 0 \/ 96 <= R
  zeroLayer : R = 0 -> MX + 123 * f = 240

/-- The checked scalar opening theorem composed with an actual defect-row
upper bound.  Notice that the retained interface supplies only comparison
with `defect`; replacing it by `117` is proved here. -/
theorem thirteenSix_weight_ge_forty_eight_of_retained_opening
    {defect : Int} {C O MX W R f : Nat}
    (hC : C <= 60) (hdefect : defect <= 117)
    (hO : 39 <= O) (hMX : 21 <= MX)
    (h : ThirteenSixRetainedOpeningRows defect C O MX W R f) :
    48 <= W := by
  have hdual :
      (33810 : Int) - 414 * (W : Int) <= 123 * (117 : Int) := by
    exact h.openingDual.trans
      (mul_le_mul_of_nonneg_left hdefect (by norm_num))
  apply thirteen_six_opening_weight_ge_forty_eight
  exact ⟨hC, le_rfl, hO, hMX, hdual, h.retainedBudget,
    h.residualGap, h.zeroLayer⟩

/-- Configuration-level composition of every presently checked opening
row.  Only the four coefficientwise retained rows above and the harmless
natural-number name `MX` for the signed subset moment remain hypotheses.
-/
theorem thirteenSix_weight_ge_forty_eight_of_configuration_rows
    {α : Type u} [Fintype α] [DecidableEq α]
    (Mel : RealPlaneMelchiorPrinciple.{u})
    (cfg : Configuration α) (hadm : Admissible cfg)
    (hcard : Fintype.card α = 13)
    (hcount : Erdos506.V4.circleCount cfg <= 60)
    (gamma : DeterminedCircle cfg)
    (hgamma : (circleTrace cfg gamma.1).card = 6)
    (MX R f : Nat)
    (hMXeq : (MX : Int) =
      (blockSystem cfg).subsetPivotMoment
        (Finset.univ \ circleTrace cfg gamma.1))
    (hretained : ThirteenSixRetainedOpeningRows
      (blockSystem cfg).defectRow
      (Erdos506.V4.circleCount cfg)
      (3 * circleBlockCount cfg 3) MX
      (thirteenSixWeight (blockSystem cfg) (circleTrace cfg gamma.1))
      R f) :
    48 <= thirteenSixWeight
      (blockSystem cfg) (circleTrace cfg gamma.1) := by
  have hpivots := thirteenSix_class_pivot_bounds
    Mel cfg hadm hcard (circleTrace cfg gamma.1) hgamma
  have hMXInt : (21 : Int) <= (MX : Int) := by
    rw [hMXeq]
    exact hpivots.2
  have hMX : 21 <= MX := by exact_mod_cast hMXInt
  have hdefect := thirteenSix_defectRow_le_one_hundred_seventeen
    Mel cfg hadm hcard
  have hlineCap : ∀ L : DeterminedLine cfg,
      (lineSupport cfg L).card <= 6 :=
    lineSupport_card_le_six_of_thirteen_of_circleCount_le
      cfg hadm hcard hcount
  have hcircleCap : ∀ c : DeterminedCircle cfg,
      (circleTrace cfg c.1).card <= 6 := fun c =>
    circleTrace_card_le_six_of_thirteen_of_circleCount_le
      cfg hadm hcard hcount c
  have hcap : BlockSizeCap (blockSystem cfg) 6 := by
    intro b _hthree
    cases b with
    | inl L =>
        simpa [blockSystem, geometricBlockSystem, geometricBlockSupport] using
          hlineCap L
    | inr c =>
        simpa [blockSystem, geometricBlockSystem, geometricBlockSupport] using
          hcircleCap c
  have hCbridge : (blockSystem cfg).totalCircleCount =
      Erdos506.V4.circleCount cfg := by
    rw [totalCircleCount_eq_card_determinedCircle,
      ← Erdos506.V3.circleCount_eq_card_determinedCircle]
  have hC : (blockSystem cfg).totalCircleCount <= 60 := by omega
  have hP := three_n_le_rowP_of_realPlaneMelchior Mel cfg hadm (by omega)
  change 3 * (Fintype.card α : Int) <=
    (blockSystem cfg).pivotRow at hP
  rw [hcard] at hP
  have hC3 := thirteen_circleCount_three_ge_thirteen_of_cap_six
    (blockSystem cfg) hcard hcap hC hP hdefect
  have hO : 39 <= 3 * circleBlockCount cfg 3 := by
    change 39 <= 3 * (blockSystem cfg).circleCount 3
    omega
  exact thirteenSix_weight_ge_forty_eight_of_retained_opening
    hcount hdefect hO hMX hretained

end RetainedOpeningBridge

section CapacityGapArithmetic

/-- The balanced lower bound for repetition events, equation `rho(r)` in
the manuscript.  Values outside the already-proved range `0 <= r <= 6`
are irrelevant and are assigned zero. -/
def thirteenSixRho : Nat -> Nat
  | 0 => 2
  | 1 => 3
  | 2 => 4
  | 3 => 6
  | 4 => 8
  | 5 => 10
  | 6 => 12
  | _ => 0

/-- Nonnegative variables in the retained second-added-centre budget and
the event-host capacity.  Names and coefficients follow equations
`(n13-second-budget)` and `(n13-capacity-gap)` exactly. -/
structure ThirteenSixCapacityGapData where
  r : Nat
  repetitionEvents : Nat
  E : Nat
  A6 : Nat
  h : Nat
  k : Nat
  ell : Nat
  g : Nat
  y : Nat
  z : Nat
  f : Nat
  w : Nat
  t : Nat
  p : Nat
  u : Nat
  v : Nat
  d : Nat

/-- Exact named rows used before the two terminal residues.

The first two event inequalities are the conclusions to be transported
from S1/S2.  `capacityGap` and `A6_eq_zero` are the retained capacity-gap
rows.  `E_definition` is the exhaustive host-capacity sum, and
`secondBudget` is the full retained slack budget from the paper. -/
structure ThirteenSixCapacityGapConditions
    (x : ThirteenSixCapacityGapData) : Prop where
  r_le_six : x.r <= 6
  repetition_lower : thirteenSixRho x.r <= x.repetitionEvents
  repetition_host_capacity : x.repetitionEvents <= x.E
  capacityGap : 4 * x.E <= 6 * x.r + 7 + 8 * x.A6
  A6_eq_zero : x.A6 = 0
  E_definition :
    x.E = 2 * x.h + 3 * x.k + 9 * x.A6 + 2 * x.ell + 2 * x.g
  secondBudget :
    12 * x.h + 26 * x.k + 36 * x.A6 + 3 * x.y + 5 * x.z +
        2 * x.f + 40 * x.ell + 31 * x.w + 22 * x.t + 48 * x.p +
        6 * x.u + 3 * x.v + 36 * x.d <=
      12 + 6 * x.r

/-- The capacity gap eliminates residues `0,1,4,5,6`.  Hence only the two
terminal equality layers `r=2,3` can survive. -/
theorem thirteenSix_capacity_gap_leaves_two_or_three
    (x : ThirteenSixCapacityGapData)
    (h : ThirteenSixCapacityGapConditions x) :
    x.r = 2 \/ x.r = 3 := by
  have hrle := h.r_le_six
  have hrange :
      x.r = 0 \/ x.r = 1 \/ x.r = 2 \/ x.r = 3 \/
        x.r = 4 \/ x.r = 5 \/ x.r = 6 := by
    omega
  have hlower := h.repetition_lower
  have hhost := h.repetition_host_capacity
  have hcap := h.capacityGap
  have hA6 := h.A6_eq_zero
  have hE := h.E_definition
  have hbudget := h.secondBudget
  rcases hrange with hr | hr | hr | hr | hr | hr | hr <;>
    simp [hr, thirteenSixRho] at hlower <;>
    omega

/-- Variables in equations `(n13-res-delta)`--`(n13-res-J)` after the
capacity gap has reduced the proof to `r=2,3`.  The paper first proves that
the signed quantity `delta` is nonnegative, so it is represented by `Nat`
here. -/
structure ThirteenSixTerminalData where
  delta : Nat
  j : Nat
  mu : Nat
  a : Nat
  y : Nat
  u : Nat
  v : Nat
  h : Nat
  t : Nat
  f : Nat

/-- Exact terminal rows, written without subtraction so every equality is
over natural numbers.

They are respectively `delta = 7 mu - 4 j`, the rows for `v` and `f`, the
terminal budget, and the exact identity for `J`.  `delta_le_two` and
`y_le_a` are the two inequalities retained immediately before those rows.
-/
structure ThirteenSixTerminalConditions
    (r J : Nat) (x : ThirteenSixTerminalData) : Prop where
  delta_le_two : x.delta <= 2
  y_le_a : x.y <= x.a
  delta_row : x.delta + 4 * x.j = 7 * x.mu
  v_row :
    x.v + x.a + 2 * x.u + 4 * x.h + 4 * x.t =
      2 * x.delta + 2 * r
  f_row :
    x.f + x.v + 5 * x.t + 2 * r =
      2 * x.j + x.mu + x.y + 4 * x.h
  budget :
    x.a + x.u + 4 * x.h + 2 * x.t + 4 * x.mu <=
      3 + 2 * r + x.j
  J_row :
    J + 123 * x.mu + 24 * r + 9 * x.t =
      7 * x.a + 48 * x.h + 90 * x.j + 19 * x.u + 8 * x.y

/-- The exact terminal system is empty for the `r=2`, `J=9` equality
layer. -/
theorem thirteenSix_terminal_two_impossible
    (x : ThirteenSixTerminalData)
    (h : ThirteenSixTerminalConditions 2 9 x) : False := by
  rcases x with ⟨delta, j, mu, a, y, u, v, hh, t, f⟩
  rcases h with ⟨hdelta, hya, hdeltaRow, hv, hf, hbudget, hJ⟩
  change delta <= 2 at hdelta
  change y <= a at hya
  change delta + 4 * j = 7 * mu at hdeltaRow
  change v + a + 2 * u + 4 * hh + 4 * t =
    2 * delta + 4 at hv
  change f + v + 5 * t + 4 = 2 * j + mu + y + 4 * hh at hf
  change a + u + 4 * hh + 2 * t + 4 * mu <= 7 + j at hbudget
  change 9 + 123 * mu + 48 + 9 * t =
    7 * a + 48 * hh + 90 * j + 19 * u + 8 * y at hJ
  have hjle : j <= 5 := by omega
  have htrip :
      (delta = 0 /\ j = 0 /\ mu = 0) \/
      (delta = 1 /\ j = 5 /\ mu = 3) \/
      (delta = 2 /\ j = 3 /\ mu = 2) := by
    interval_cases delta <;> interval_cases j <;> omega
  rcases htrip with hzero | hone | htwo
  · rcases hzero with ⟨hdelta0, hj, hmu⟩
    subst delta
    subst j
    subst mu
    have hu : u = 0 := by omega
    have ht : t = 0 := by omega
    have hyaeq : y = a := by omega
    have ha : a + 4 * hh = 4 := by omega
    omega
  · rcases hone with ⟨hdelta1, hj, hmu⟩
    subst delta
    subst j
    subst mu
    have ha : a = 0 := by omega
    have hu : u = 0 := by omega
    have hh0 : hh = 0 := by omega
    have ht : t = 0 := by omega
    have hy : y = 0 := by omega
    omega
  · rcases htwo with ⟨hdelta2, hj, hmu⟩
    subst delta
    subst j
    subst mu
    have hh0 : hh = 0 := by omega
    have ht : t <= 1 := by omega
    have htCases : t = 0 \/ t = 1 := by omega
    rcases htCases with ht0 | ht1
    · subst t
      have hau : a + u = 2 := by omega
      omega
    · subst t
      have ha0 : a = 0 := by omega
      have hu0 : u = 0 := by omega
      have hy0 : y = 0 := by omega
      omega

/-- The exact terminal system is empty for the `r=3`, `J=3` equality
layer. -/
theorem thirteenSix_terminal_three_impossible
    (x : ThirteenSixTerminalData)
    (h : ThirteenSixTerminalConditions 3 3 x) : False := by
  rcases x with ⟨delta, j, mu, a, y, u, v, hh, t, f⟩
  rcases h with ⟨hdelta, hya, hdeltaRow, hv, hf, hbudget, hJ⟩
  change delta <= 2 at hdelta
  change y <= a at hya
  change delta + 4 * j = 7 * mu at hdeltaRow
  change v + a + 2 * u + 4 * hh + 4 * t =
    2 * delta + 6 at hv
  change f + v + 5 * t + 6 = 2 * j + mu + y + 4 * hh at hf
  change a + u + 4 * hh + 2 * t + 4 * mu <= 9 + j at hbudget
  change 3 + 123 * mu + 72 + 9 * t =
    7 * a + 48 * hh + 90 * j + 19 * u + 8 * y at hJ
  have hjle : j <= 7 := by omega
  have htrip :
      (delta = 0 /\ j = 0 /\ mu = 0) \/
      (delta = 0 /\ j = 7 /\ mu = 4) \/
      (delta = 1 /\ j = 5 /\ mu = 3) \/
      (delta = 2 /\ j = 3 /\ mu = 2) := by
    interval_cases delta <;> interval_cases j <;> omega
  rcases htrip with hzero | hextra | hone | htwo
  · rcases hzero with ⟨hdelta0, hj, hmu⟩
    subst delta
    subst j
    subst mu
    have hu : u = 0 := by omega
    have ht : t = 0 := by omega
    have hyaeq : y = a := by omega
    have ha : a + 4 * hh = 6 := by omega
    omega
  · rcases hextra with ⟨hdelta0, hj, hmu⟩
    subst delta
    subst j
    subst mu
    have ha : a = 0 := by omega
    have hu : u = 0 := by omega
    have hh0 : hh = 0 := by omega
    have ht : t = 0 := by omega
    have hy : y = 0 := by omega
    omega
  · rcases hone with ⟨hdelta1, hj, hmu⟩
    subst delta
    subst j
    subst mu
    have hh0 : hh = 0 := by omega
    have ht : t <= 1 := by omega
    have htCases : t = 0 \/ t = 1 := by omega
    rcases htCases with ht0 | ht1
    · subst t
      omega
    · subst t
      omega
  · rcases htwo with ⟨hdelta2, hj, hmu⟩
    subst delta
    subst j
    subst mu
    have hhle : hh <= 1 := by omega
    have ht : t <= 2 := by omega
    have hhCases : hh = 0 \/ hh = 1 := by omega
    rcases hhCases with hh0 | hh1
    · subst hh
      have htCases : t = 0 \/ t = 1 \/ t = 2 := by omega
      rcases htCases with ht0 | ht1 | ht2
      · subst t
        have hau : a + u = 4 := by omega
        omega
      · subst t
        have hau : a + u <= 2 := by omega
        omega
      · subst t
        have ha0 : a = 0 := by omega
        have hu0 : u = 0 := by omega
        have hy0 : y = 0 := by omega
        omega
    · subst hh
      have ha0 : a = 0 := by omega
      have hu0 : u = 0 := by omega
      have ht0 : t = 0 := by omega
      have hy0 : y = 0 := by omega
      omega

/-- Data for the final arithmetic composition.  The identity defining `J`
is equation `(n13-J)` after `A6=0`; the terminal rows are supplied only on
the equality layers to which they apply. -/
structure ThirteenSixFullArithmeticCertificate where
  gap : ThirteenSixCapacityGapData
  gapRows : ThirteenSixCapacityGapConditions gap
  J : Nat
  J_definition : J + 12 * gap.E = 21 + 18 * gap.r
  terminal : ThirteenSixTerminalData
  terminalRows :
    gap.r = 2 \/ gap.r = 3 ->
      ThirteenSixTerminalConditions gap.r J terminal

/-- Complete solver-free integer end of the capacity-gap argument: no
collection of counts can satisfy all retained rows. -/
theorem thirteenSix_full_arithmetic_impossible
    (c : ThirteenSixFullArithmeticCertificate) : False := by
  have hr := thirteenSix_capacity_gap_leaves_two_or_three c.gap c.gapRows
  have hterminal := c.terminalRows hr
  rcases hr with hr2 | hr3
  · have hE : c.gap.E = 4 := by
      have hlower := c.gapRows.repetition_lower
      have hhost := c.gapRows.repetition_host_capacity
      have hcap := c.gapRows.capacityGap
      have hA6 := c.gapRows.A6_eq_zero
      simp [hr2, thirteenSixRho] at hlower
      omega
    have hJdef := c.J_definition
    have hJ : c.J = 9 := by omega
    apply thirteenSix_terminal_two_impossible c.terminal
    simpa [hr2, hJ] using hterminal
  · have hE : c.gap.E = 6 := by
      have hlower := c.gapRows.repetition_lower
      have hhost := c.gapRows.repetition_host_capacity
      have hcap := c.gapRows.capacityGap
      have hA6 := c.gapRows.A6_eq_zero
      simp [hr3, thirteenSixRho] at hlower
      omega
    have hJdef := c.J_definition
    have hJ : c.J = 3 := by omega
    apply thirteenSix_terminal_three_impossible c.terminal
    simpa [hr3, hJ] using hterminal

end CapacityGapArithmetic

end Erdos506.V1
