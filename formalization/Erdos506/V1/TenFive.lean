import Erdos506.Finite.IncidenceMoments
import Erdos506.V1.Deletion
import Erdos506.V1.TenFiveRows
import Erdos506.V1.TenFour
import Erdos506.V1.TenLocalParity

/-!
# The ten-point selected-five-circle branch

This file joins the checked deletion theorem, the exact local parity table,
and the scalar faces for `C = 28, ..., 32`.  All numerical routing is carried
out inside Lean and uses no solver certificate.

Three genuinely geometric inputs from the manuscript remain explicit in
`RealPlaneTenFiveGeometry`: the reduction from at most five generalized
five-blocks to at most three, the three-pentagon rich-line endpoint, and the
disjoint golden-link endpoint.  None of these fields assumes the desired
circle-count conclusion.
-/

namespace Erdos506.V1

open Erdos506.Block
open Erdos506.Block.BlockSystem
open Erdos506.Incidence
open Erdos506.V3
open Erdos506.V4
open scoped BigOperators

universe u

/-- The complete pointwise information supplied by the ten-point local
parity calculation.  The last clause is the loss caused by a five-line. -/
def TenFiveLocalProfile
    {Point Block : Type*} [Fintype Point] [Fintype Block]
    [DecidableEq Point]
    (S : BlockSystem Point Block) (p : Point) : Prop :=
  (S.blockDegree 3 p = 6 ∨ S.blockDegree 3 p = 9) ∧
  S.lineDegree 4 p ≤ 3 ∧
  (S.lineDegree 5 p = 0 →
    tenLocalStateAllowed (S.blockDegree 3 p) (S.lineDegree 4 p)
        (S.blockDegree 5 p) ∧
      S.lineDegree 3 p ≤
        tenLocalLine3Cap (S.blockDegree 3 p) (S.lineDegree 4 p)
          (S.blockDegree 5 p)) ∧
  (1 ≤ S.lineDegree 5 p →
    S.lineDegree 3 p + 1 ≤
      tenLocalLine3Cap (S.blockDegree 3 p) 0
        (S.blockDegree 5 p))

/-- The three precise real-geometric kernels not contained in the generic
block calculus.

The first three fields are the manuscript's `P1`, punctured-pentagon, and
four-pentagon steps.  They prove only the structural bound `B₅ ≤ 3`.  The
last two fields are restricted to the exact scalar equality rows that
survive every local-capacity comparison. -/
structure RealPlaneTenFiveGeometry where
  fiveBlockPacking :
    ∀ {α : Type u} [Fintype α] [DecidableEq α]
      (cfg : Configuration α),
      Admissible cfg →
      Fintype.card α = 10 →
      BlockSizeCap (blockSystem cfg) 5 →
      (blockSystem cfg).blockCount 5 ≤ 5
  puncturedPentagon :
    ∀ {α : Type u} [Fintype α] [DecidableEq α]
      (cfg : Configuration α),
      Admissible cfg →
      Fintype.card α = 10 →
      BlockSizeCap (blockSystem cfg) 5 →
      (∀ p : α, (blockSystem cfg).blockDegree 3 p = 6 ∨
        (blockSystem cfg).blockDegree 3 p = 9) →
      (blockSystem cfg).blockCount 5 ≠ 5
  fourPentagon :
    ∀ {α : Type u} [Fintype α] [DecidableEq α]
      (cfg : Configuration α),
      Admissible cfg →
      Fintype.card α = 10 →
      BlockSizeCap (blockSystem cfg) 5 →
      (∀ p : α, (blockSystem cfg).blockDegree 3 p = 6 ∨
        (blockSystem cfg).blockDegree 3 p = 9) →
      (blockSystem cfg).blockCount 5 ≠ 4
  threePentagonRichLine :
    ∀ {α : Type u} [Fintype α] [DecidableEq α]
      (cfg : Configuration α),
      Admissible cfg →
      Fintype.card α = 10 →
      BlockSizeCap (blockSystem cfg) 5 →
      (blockSystem cfg).totalCircleCount = 32 →
      (blockSystem cfg).blockCount 5 = 3 →
      (tenHighPoints (blockSystem cfg)).card = 2 →
      (blockSystem cfg).lineCount 5 = 0 →
      1 ≤ (blockSystem cfg).lineCount 4 →
      (blockSystem cfg).lineCount 4 ≤ 3 →
      (blockSystem cfg).lineCount 3 +
          (blockSystem cfg).lineCount 4 = 10 →
      (∀ p : α, TenFiveLocalProfile (blockSystem cfg) p) →
      False
  disjointGoldenLink :
    ∀ {α : Type u} [Fintype α] [DecidableEq α]
      (cfg : Configuration α),
      Admissible cfg →
      Fintype.card α = 10 →
      (blockSystem cfg).totalCircleCount = 32 →
      (blockSystem cfg).blockCount 3 = 20 →
      (blockSystem cfg).blockCount 4 = 20 →
      (blockSystem cfg).blockCount 5 = 2 →
      (blockSystem cfg).lineCount 3 = 10 →
      (blockSystem cfg).lineCount 4 = 0 →
      (blockSystem cfg).lineCount 5 = 0 →
      (∀ p : α, (blockSystem cfg).blockDegree 3 p = 6) →
      False

/-- A degree in a subfamily is at most the size of that subfamily. -/
theorem degreeIn_le_card
    {Point Block : Type*} [Fintype Point] [Fintype Block]
    [DecidableEq Point]
    (S : BlockSystem Point Block) (F : Finset Block) (p : Point) :
    S.degreeIn F p ≤ F.card := by
  unfold BlockSystem.degreeIn
  exact Finset.card_filter_le _ _

/-- The local degree in four-lines is at most their global number. -/
theorem lineDegree_le_lineCount
    {Point Block : Type*} [Fintype Point] [Fintype Block]
    [DecidableEq Point]
    (S : BlockSystem Point Block) (s : Nat) (p : Point) :
    S.lineDegree s p ≤ S.lineCount s :=
  degreeIn_le_card S (S.lineBlocksOfSize s) p

/-- A selected five-circle supplies at least one generalized five-block. -/
theorem one_le_blockCount_five_of_selected_five_circle
    {α : Type u} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (gamma : DeterminedCircle cfg)
    (hgamma : (circleTrace cfg gamma.1).card = 5) :
    1 ≤ (blockSystem cfg).blockCount 5 := by
  classical
  let S := blockSystem cfg
  let b : GeometricBlock cfg := Sum.inr gamma
  have hb : b ∈ S.blocksOfSize 5 := by
    apply S.mem_blocksOfSize.mpr
    simpa [S, b, blockSystem, geometricBlockSupport] using hgamma
  change 1 ≤ (S.blocksOfSize 5).card
  exact Finset.card_pos.mpr ⟨b, hb⟩

/-- The deletion bound, Kelly--Moser, and the pair row give the two possible
three-block degrees without using the later `B₅ ≤ 3` reduction. -/
theorem ten_blockDegree_three_eq_six_or_nine_of_geometry
    {α : Type u} [Fintype α] [DecidableEq α]
    (Mel : RealPlaneMelchiorPrinciple.{u})
    (EvenArr : RealPlaneEvenArrangementPrinciple.{u})
    (Cross : RealPlaneRadicalAxisCrossBlockPrinciple.{u})
    (Kelly : RealPlaneKellyMoserPrinciple.{u})
    (cfg : Configuration α) (hadm : Admissible cfg)
    (hcard : Fintype.card α = 10)
    (hcount : Erdos506.V4.circleCount cfg ≤ 32)
    (hcap : BlockSizeCap (blockSystem cfg) 5)
    (p : α) :
    (blockSystem cfg).blockDegree 3 p = 6 ∨
      (blockSystem cfg).blockDegree 3 p = 9 := by
  let S := blockSystem cfg
  have hpairs := (ten_local_pair_and_kappa S hcard hcap p).1
  have hKM := Kelly.pivot_three_block_bound cfg hadm
    (by omega) (by omega) p
  rw [hcard] at hKM
  norm_num at hKM
  change 27 ≤ 7 * S.blockDegree 3 p at hKM
  have hupper := ten_blockDegree_three_le_eleven_of_deletion
    Mel EvenArr Cross cfg hadm hcard hcount p
  exact ten_local_pair_d3_eq_six_or_nine hpairs hKM hupper

/-- Configuration-level materialization of the complete local profile once
the geometric five-block reduction `B₅ ≤ 3` is available. -/
theorem tenFiveLocalProfile_of_geometry
    {α : Type u} [Fintype α] [DecidableEq α]
    (Mel : RealPlaneMelchiorPrinciple.{u})
    (EvenArr : RealPlaneEvenArrangementPrinciple.{u})
    (Cross : RealPlaneRadicalAxisCrossBlockPrinciple.{u})
    (Kelly : RealPlaneKellyMoserPrinciple.{u})
    (cfg : Configuration α) (hadm : Admissible cfg)
    (hcard : Fintype.card α = 10)
    (hcount : Erdos506.V4.circleCount cfg ≤ 32)
    (hcap : BlockSizeCap (blockSystem cfg) 5)
    (hB5 : (blockSystem cfg).blockCount 5 ≤ 3)
    (p : α) : TenFiveLocalProfile (blockSystem cfg) p := by
  classical
  let S := blockSystem cfg
  obtain ⟨hpairs, hkappaFormula⟩ :=
    ten_local_pair_and_kappa S hcard hcap p
  have hKM := Kelly.pivot_three_block_bound cfg hadm
    (by omega) (by omega) p
  rw [hcard] at hKM
  norm_num at hKM
  change 27 ≤ 7 * S.blockDegree 3 p at hKM
  have hupper := ten_blockDegree_three_le_eleven_of_deletion
    Mel EvenArr Cross cfg hadm hcard hcount p
  have hd3 : S.blockDegree 3 p = 6 ∨ S.blockDegree 3 p = 9 :=
    ten_local_pair_d3_eq_six_or_nine hpairs hKM hupper
  have hr : S.blockDegree 5 p ≤ 3 :=
    (blockDegree_le_blockCount S 5 p).trans hB5
  have hkappaNonneg : 0 ≤ S.restoredKappa p := by
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
  have hq : S.lineDegree 4 p ≤ 3 := by
    rw [hkappaFormula] at hkappaNonneg
    rcases hd3 with hd3 | hd3 <;>
      simp [tenLocalKappa, hd3] at hkappaNonneg <;> omega
  refine ⟨hd3, hq, ?_, ?_⟩
  · intro hline5
    have htable := ten_local_line3_table_of_geometry
      Mel EvenArr Kelly cfg hadm hcard hcap hB5 p hupper hline5
    simpa [S] using htable.2
  · intro hline5
    have hkappaLocal :
        0 ≤ tenLocalKappa (S.blockDegree 3 p) (S.blockDegree 5 p)
          (S.lineDegree 3 p) (S.lineDegree 4 p)
          (S.lineDegree 5 p) := by
      rw [← hkappaFormula]
      exact hkappaNonneg
    have hkappaLocalNe :
        tenLocalKappa (S.blockDegree 3 p) (S.blockDegree 5 p)
          (S.lineDegree 3 p) (S.lineDegree 4 p)
          (S.lineDegree 5 p) ≠ 1 := by
      rw [← hkappaFormula]
      exact hkappaNe
    exact ten_local_five_line_loses_one hd3 hr hline5
      hkappaLocal hkappaLocalNe

/-! ## Finite local-capacity arithmetic -/

/-- Moving from a `q`-row to the `q = 0` row never decreases the printed
capacity on an allowed ten-point cell. -/
theorem tenLocalLine3Cap_le_qzero
    {d3 q r : Nat}
    (hd3 : d3 = 6 ∨ d3 = 9) (hr : r ≤ 3) (hq : q ≤ 3) :
    tenLocalLine3Cap d3 q r ≤ tenLocalLine3Cap d3 0 r := by
  rcases hd3 with rfl | rfl <;>
    interval_cases q <;> interval_cases r <;>
    simp [tenLocalLine3Cap]

/-- For five-degree at most two, the zero-four-line capacity has the simple
linear majorant used in the `k = 1,2` faces. -/
theorem tenLocalLine3Cap_add_degree_le
    {d3 r : Nat} (hd3 : d3 = 6 ∨ d3 = 9) (hr : r ≤ 2) :
    tenLocalLine3Cap d3 0 r + r ≤
      4 + (if d3 = 9 then 1 else 0) := by
  rcases hd3 with rfl | rfl <;> interval_cases r <;>
    simp [tenLocalLine3Cap]

/-- At five-degree three there is a two-unit correction to the preceding
linear majorant. -/
theorem tenLocalLine3Cap_add_degree_le_three
    {d3 r : Nat} (hd3 : d3 = 6 ∨ d3 = 9) (hr : r ≤ 3) :
    tenLocalLine3Cap d3 0 r + r ≤
      4 + (if d3 = 9 then 1 else 0) +
        2 * (if r = 3 then 1 else 0) := by
  rcases hd3 with rfl | rfl <;> interval_cases r <;>
    simp [tenLocalLine3Cap]

/-- The indicator of degree three is controlled by the binomial moment. -/
theorem ten_degree_three_indicator_bound {r : Nat} (hr : r ≤ 3) :
    (if r = 3 then 1 else 0) + r ≤ Nat.choose r 2 + 1 := by
  interval_cases r <;> norm_num [Nat.choose]

/-- In a low row with at most two five-blocks, every incident four-line
charges the weak loss `2-r`. -/
theorem ten_low_four_line_loss
    {q r : Nat} (hq : q ≤ 2) (hr : r ≤ 2) :
    tenLocalLine3Cap 6 q r + q * (2 - r) ≤
      tenLocalLine3Cap 6 0 r := by
  interval_cases q <;> interval_cases r <;>
    simp [tenLocalLine3Cap]

noncomputable def tenFiveDegreeThreePoints
    {Point Block : Type*} [Fintype Point] [Fintype Block]
    [DecidableEq Point]
    (S : BlockSystem Point Block) : Finset Point := by
  classical
  exact Finset.univ.filter fun p => S.blockDegree 5 p = 3

@[simp] theorem mem_tenFiveDegreeThreePoints
    {Point Block : Type*} [Fintype Point] [Fintype Block]
    [DecidableEq Point]
    {S : BlockSystem Point Block} {p : Point} :
    p ∈ tenFiveDegreeThreePoints S ↔ S.blockDegree 5 p = 3 := by
  classical
  simp [tenFiveDegreeThreePoints]

/-- Sum of the zero-four-line capacities in the `B₅ ≤ 2` range. -/
theorem ten_qzero_capacity_sum_add_fiveB5_le
    {Point Block : Type*} [Fintype Point] [Fintype Block]
    [DecidableEq Point]
    (S : BlockSystem Point Block) (hcard : Fintype.card Point = 10)
    (hB5 : S.blockCount 5 ≤ 2)
    (hd3 : ∀ p : Point, S.blockDegree 3 p = 6 ∨
      S.blockDegree 3 p = 9) :
    (∑ p : Point,
        tenLocalLine3Cap (S.blockDegree 3 p) 0
          (S.blockDegree 5 p)) + 5 * S.blockCount 5 ≤
      40 + (tenHighPoints S).card := by
  classical
  have hr (p : Point) : S.blockDegree 5 p ≤ 2 :=
    (blockDegree_le_blockCount S 5 p).trans hB5
  have hpoint (p : Point) :
      tenLocalLine3Cap (S.blockDegree 3 p) 0
          (S.blockDegree 5 p) + S.blockDegree 5 p ≤
        4 + (if S.blockDegree 3 p = 9 then 1 else 0) :=
    tenLocalLine3Cap_add_degree_le (hd3 p) (hr p)
  have hinc := S.block_incidence 5
  have hhigh :
      (∑ p : Point, if S.blockDegree 3 p = 9 then 1 else 0) =
        (tenHighPoints S).card := by
    simp [tenHighPoints]
  calc
    (∑ p : Point,
        tenLocalLine3Cap (S.blockDegree 3 p) 0
          (S.blockDegree 5 p)) + 5 * S.blockCount 5 =
        (∑ p : Point,
          tenLocalLine3Cap (S.blockDegree 3 p) 0
            (S.blockDegree 5 p)) +
          ∑ p : Point, S.blockDegree 5 p := by rw [hinc]
    _ = ∑ p : Point,
        (tenLocalLine3Cap (S.blockDegree 3 p) 0
          (S.blockDegree 5 p) + S.blockDegree 5 p) := by
      rw [Finset.sum_add_distrib]
    _ ≤ ∑ p : Point,
        (4 + (if S.blockDegree 3 p = 9 then 1 else 0)) := by
      exact Finset.sum_le_sum fun p _hp => hpoint p
    _ = 40 + (tenHighPoints S).card := by
      rw [Finset.sum_add_distrib, hhigh]
      simp [hcard]

/-- With three five-blocks, at most one point can have five-degree three. -/
theorem tenFiveDegreeThreePoints_card_le_one
    {Point Block : Type*} [Fintype Point] [Fintype Block]
    [DecidableEq Point]
    (S : BlockSystem Point Block) (hcard : Fintype.card Point = 10)
    (hB5 : S.blockCount 5 = 3) :
    (tenFiveDegreeThreePoints S).card ≤ 1 := by
  classical
  have hr (p : Point) : S.blockDegree 5 p ≤ 3 := by
    exact (blockDegree_le_blockCount S 5 p).trans (by omega)
  have hpoint (p : Point) :
      (if S.blockDegree 5 p = 3 then 1 else 0) +
          S.blockDegree 5 p ≤
        Nat.choose (S.blockDegree 5 p) 2 + 1 :=
    ten_degree_three_indicator_bound (hr p)
  have hinc := S.block_incidence 5
  rw [hB5] at hinc
  norm_num at hinc
  have hmoment := S.second_moment_le_two_choose (S.blocksOfSize 5)
  change (∑ p : Point, Nat.choose (S.blockDegree 5 p) 2) ≤
    2 * Nat.choose (S.blockCount 5) 2 at hmoment
  rw [hB5] at hmoment
  norm_num [Nat.choose] at hmoment
  have hindicator :
      (∑ p : Point, if S.blockDegree 5 p = 3 then 1 else 0) =
        (tenFiveDegreeThreePoints S).card := by
    simp [tenFiveDegreeThreePoints]
  have hsum :
      (tenFiveDegreeThreePoints S).card + 15 ≤
        (∑ p : Point, Nat.choose (S.blockDegree 5 p) 2) + 10 := by
    calc
      (tenFiveDegreeThreePoints S).card + 15 =
          (∑ p : Point, if S.blockDegree 5 p = 3 then 1 else 0) +
            ∑ p : Point, S.blockDegree 5 p := by
        rw [hindicator, hinc]
      _ = ∑ p : Point,
          ((if S.blockDegree 5 p = 3 then 1 else 0) +
            S.blockDegree 5 p) := by rw [Finset.sum_add_distrib]
      _ ≤ ∑ p : Point,
          (Nat.choose (S.blockDegree 5 p) 2 + 1) := by
        exact Finset.sum_le_sum fun p _hp => hpoint p
      _ = (∑ p : Point, Nat.choose (S.blockDegree 5 p) 2) + 10 := by
        rw [Finset.sum_add_distrib]
        simp [hcard]
  omega

/-- Sum of the zero-four-line capacities when `B₅ = 3`. -/
theorem ten_qzero_capacity_sum_le_of_blockCount_five_eq_three
    {Point Block : Type*} [Fintype Point] [Fintype Block]
    [DecidableEq Point]
    (S : BlockSystem Point Block) (hcard : Fintype.card Point = 10)
    (hB5 : S.blockCount 5 = 3)
    (hd3 : ∀ p : Point, S.blockDegree 3 p = 6 ∨
      S.blockDegree 3 p = 9) :
    (∑ p : Point,
      tenLocalLine3Cap (S.blockDegree 3 p) 0
        (S.blockDegree 5 p)) ≤ 27 + (tenHighPoints S).card := by
  classical
  have hr (p : Point) : S.blockDegree 5 p ≤ 3 :=
    (blockDegree_le_blockCount S 5 p).trans (by omega)
  have hpoint (p : Point) :
      tenLocalLine3Cap (S.blockDegree 3 p) 0
          (S.blockDegree 5 p) + S.blockDegree 5 p ≤
        4 + (if S.blockDegree 3 p = 9 then 1 else 0) +
          2 * (if S.blockDegree 5 p = 3 then 1 else 0) :=
    tenLocalLine3Cap_add_degree_le_three (hd3 p) (hr p)
  have hinc := S.block_incidence 5
  rw [hB5] at hinc
  norm_num at hinc
  have hhigh :
      (∑ p : Point, if S.blockDegree 3 p = 9 then 1 else 0) =
        (tenHighPoints S).card := by
    simp [tenHighPoints]
  have hthree :
      (∑ p : Point, if S.blockDegree 5 p = 3 then 1 else 0) =
        (tenFiveDegreeThreePoints S).card := by
    simp [tenFiveDegreeThreePoints]
  have hN := tenFiveDegreeThreePoints_card_le_one S hcard hB5
  have hsum :
      (∑ p : Point,
        tenLocalLine3Cap (S.blockDegree 3 p) 0
          (S.blockDegree 5 p)) + 15 ≤
        40 + (tenHighPoints S).card +
          2 * (tenFiveDegreeThreePoints S).card := by
    calc
      (∑ p : Point,
        tenLocalLine3Cap (S.blockDegree 3 p) 0
          (S.blockDegree 5 p)) + 15 =
          (∑ p : Point,
            tenLocalLine3Cap (S.blockDegree 3 p) 0
              (S.blockDegree 5 p)) +
            ∑ p : Point, S.blockDegree 5 p := by rw [hinc]
      _ = ∑ p : Point,
          (tenLocalLine3Cap (S.blockDegree 3 p) 0
            (S.blockDegree 5 p) + S.blockDegree 5 p) := by
        rw [Finset.sum_add_distrib]
      _ ≤ ∑ p : Point,
          (4 + (if S.blockDegree 3 p = 9 then 1 else 0) +
            2 * (if S.blockDegree 5 p = 3 then 1 else 0)) := by
        exact Finset.sum_le_sum fun p _hp => hpoint p
      _ = 40 + (tenHighPoints S).card +
          2 * (tenFiveDegreeThreePoints S).card := by
        simp only [Finset.sum_add_distrib, ← Finset.mul_sum, hhigh, hthree]
        simp [hcard]
  omega

/-- With no five-line, the three-line incidence is bounded by the sum of
the `q = 0` local capacities. -/
theorem ten_line_three_sum_le_qzero_capacity
    {Point Block : Type*} [Fintype Point] [Fintype Block]
    [DecidableEq Point]
    (S : BlockSystem Point Block)
    (hlocal : ∀ p : Point, TenFiveLocalProfile S p)
    (hB5 : S.blockCount 5 ≤ 3)
    (hL5 : S.lineCount 5 = 0) :
    3 * S.lineCount 3 ≤
      ∑ p : Point,
        tenLocalLine3Cap (S.blockDegree 3 p) 0
          (S.blockDegree 5 p) := by
  have hpoint (p : Point) :
      S.lineDegree 3 p ≤
        tenLocalLine3Cap (S.blockDegree 3 p) 0
          (S.blockDegree 5 p) := by
    have hl5 : S.lineDegree 5 p = 0 := by
      have := lineDegree_le_lineCount S 5 p
      omega
    have hcell := (hlocal p).2.2.1 hl5
    exact hcell.2.trans
      (tenLocalLine3Cap_le_qzero (hlocal p).1
        ((blockDegree_le_blockCount S 5 p).trans hB5)
        (hlocal p).2.1)
  have hinc := S.line_incidence 3
  rw [← hinc]
  exact Finset.sum_le_sum fun p _hp => hpoint p

/-- A unique five-line removes one unit of capacity at each of its five
points. -/
theorem ten_line_three_sum_add_five_le_qzero_capacity
    {Point Block : Type*} [Fintype Point] [Fintype Block]
    [DecidableEq Point]
    (S : BlockSystem Point Block)
    (hlocal : ∀ p : Point, TenFiveLocalProfile S p)
    (hB5 : S.blockCount 5 ≤ 3)
    (hL5 : S.lineCount 5 = 1) :
    3 * S.lineCount 3 + 5 ≤
      ∑ p : Point,
        tenLocalLine3Cap (S.blockDegree 3 p) 0
          (S.blockDegree 5 p) := by
  have hl5le (p : Point) : S.lineDegree 5 p ≤ 1 := by
    have := lineDegree_le_lineCount S 5 p
    omega
  have hpoint (p : Point) :
      S.lineDegree 3 p + S.lineDegree 5 p ≤
        tenLocalLine3Cap (S.blockDegree 3 p) 0
          (S.blockDegree 5 p) := by
    by_cases hz : S.lineDegree 5 p = 0
    · rw [hz, Nat.add_zero]
      have hcell := (hlocal p).2.2.1 hz
      exact hcell.2.trans
        (tenLocalLine3Cap_le_qzero (hlocal p).1
          ((blockDegree_le_blockCount S 5 p).trans hB5)
          (hlocal p).2.1)
    · have hpLe := hl5le p
      have hone : S.lineDegree 5 p = 1 := by omega
      rw [hone]
      exact (hlocal p).2.2.2 (by omega)
  have hinc3 := S.line_incidence 3
  have hinc5 := S.line_incidence 5
  rw [hL5] at hinc5
  norm_num at hinc5
  calc
    3 * S.lineCount 3 + 5 =
        (∑ p : Point, S.lineDegree 3 p) +
          ∑ p : Point, S.lineDegree 5 p := by rw [hinc3, hinc5]
    _ = ∑ p : Point,
        (S.lineDegree 3 p + S.lineDegree 5 p) := by
      rw [Finset.sum_add_distrib]
    _ ≤ _ := Finset.sum_le_sum fun p _hp => hpoint p

/-- Cross-family degree Fubini: the pointwise product of two family degrees
counts support intersections of ordered cross-pairs. -/
theorem sum_degreeIn_mul_degreeIn
    {Point Block : Type*} [Fintype Point] [Fintype Block]
    [DecidableEq Point] [DecidableEq Block]
    (S : BlockSystem Point Block) (F G : Finset Block) :
    (∑ p : Point, S.degreeIn F p * S.degreeIn G p) =
      ∑ b ∈ F, ∑ c ∈ G, (S.support b ∩ S.support c).card := by
  classical
  let indicator : Point → Block → Nat := fun p b =>
    if p ∈ S.support b then 1 else 0
  have hdegree (H : Finset Block) (p : Point) :
      S.degreeIn H p = ∑ b ∈ H, indicator p b := by
    simp [BlockSystem.degreeIn, indicator]
  simp_rw [hdegree]
  calc
    (∑ p : Point,
        (∑ b ∈ F, indicator p b) * (∑ c ∈ G, indicator p c)) =
        ∑ p : Point, ∑ b ∈ F, ∑ c ∈ G,
          indicator p b * indicator p c := by
      apply Fintype.sum_congr
      intro p
      rw [Finset.sum_mul_sum]
    _ = ∑ b ∈ F, ∑ c ∈ G, ∑ p : Point,
          indicator p b * indicator p c := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro b hb
      rw [Finset.sum_comm]
    _ = ∑ b ∈ F, ∑ c ∈ G,
          (S.support b ∩ S.support c).card := by
      apply Finset.sum_congr rfl
      intro b hb
      apply Finset.sum_congr rfl
      intro c hc
      simpa [indicator, Erdos506.Finite.incidenceIndicator] using
        (Erdos506.Finite.sum_indicator_mul_eq_card_inter S.support b c)

/-- If every cross-pair consists of distinct blocks, the cross degree
moment is at most twice the number of cross-pairs. -/
theorem sum_degreeIn_mul_degreeIn_le_two_mul
    {Point Block : Type*} [Fintype Point] [Fintype Block]
    [DecidableEq Point] [DecidableEq Block]
    (S : BlockSystem Point Block) (F G : Finset Block)
    (hne : ∀ b ∈ F, ∀ c ∈ G, b ≠ c) :
    (∑ p : Point, S.degreeIn F p * S.degreeIn G p) ≤
      2 * F.card * G.card := by
  rw [sum_degreeIn_mul_degreeIn S F G]
  calc
    (∑ b ∈ F, ∑ c ∈ G, (S.support b ∩ S.support c).card) ≤
        ∑ b ∈ F, ∑ _c ∈ G, 2 := by
      apply Finset.sum_le_sum
      intro b hb
      apply Finset.sum_le_sum
      intro c hc
      have hlt := S.distinct_block_inter_card_lt_three (hne b hb c hc)
      omega
    _ = 2 * F.card * G.card := by
      simp [Nat.mul_comm, Nat.mul_left_comm]

/-- For `B₅ = 2`, one or two four-lines remove at least four units of
zero-row capacity per line. -/
theorem ten_two_pentagon_four_line_capacity
    {Point Block : Type*} [Fintype Point] [Fintype Block]
    [DecidableEq Point] [DecidableEq Block]
    (S : BlockSystem Point Block)
    (hB5 : S.blockCount 5 = 2)
    (hhigh : (tenHighPoints S).card = 0)
    (hL5 : S.lineCount 5 = 0) (hL4 : S.lineCount 4 ≤ 2)
    (hlocal : ∀ p : Point, TenFiveLocalProfile S p) :
    3 * S.lineCount 3 + 4 * S.lineCount 4 ≤
      ∑ p : Point,
        tenLocalLine3Cap (S.blockDegree 3 p) 0
          (S.blockDegree 5 p) := by
  classical
  have hhighEmpty : tenHighPoints S = ∅ := Finset.card_eq_zero.mp hhigh
  have hd3six (p : Point) : S.blockDegree 3 p = 6 := by
    rcases (hlocal p).1 with h6 | h9
    · exact h6
    · have hp : p ∈ tenHighPoints S := mem_tenHighPoints.mpr h9
      rw [hhighEmpty] at hp
      simp at hp
  have hr (p : Point) : S.blockDegree 5 p ≤ 2 :=
    (blockDegree_le_blockCount S 5 p).trans (by omega)
  have hq (p : Point) : S.lineDegree 4 p ≤ 2 :=
    (lineDegree_le_lineCount S 4 p).trans hL4
  have hl5 (p : Point) : S.lineDegree 5 p = 0 := by
    have := lineDegree_le_lineCount S 5 p
    omega
  have hpoint (p : Point) :
      S.lineDegree 3 p + S.lineDegree 4 p *
          (2 - S.blockDegree 5 p) ≤
        tenLocalLine3Cap (S.blockDegree 3 p) 0
          (S.blockDegree 5 p) := by
    have hcell := (hlocal p).2.2.1 (hl5 p)
    have hcap := ten_low_four_line_loss (hq p) (hr p)
    rw [hd3six p] at hcell ⊢
    exact (Nat.add_le_add_right hcell.2 _).trans hcap
  let F := S.lineBlocksOfSize 4
  let G := S.blocksOfSize 5
  have hne : ∀ b ∈ F, ∀ c ∈ G, b ≠ c := by
    intro b hb c hc hbc
    subst c
    have hb4 := (S.mem_blocksOfKindSize.mp hb).2
    have hb5 := S.mem_blocksOfSize.mp hc
    omega
  have hcross := sum_degreeIn_mul_degreeIn_le_two_mul S F G hne
  change (∑ p : Point,
      S.lineDegree 4 p * S.blockDegree 5 p) ≤
        2 * S.lineCount 4 * S.blockCount 5 at hcross
  rw [hB5] at hcross
  have hinc4 := S.line_incidence 4
  have hdecomp (p : Point) :
      S.lineDegree 4 p * (2 - S.blockDegree 5 p) +
          S.lineDegree 4 p * S.blockDegree 5 p =
        2 * S.lineDegree 4 p := by
    have := hr p
    interval_cases h : S.blockDegree 5 p <;> simp <;> omega
  have hlossIdentity :
      (∑ p : Point,
        S.lineDegree 4 p * (2 - S.blockDegree 5 p)) +
        (∑ p : Point,
          S.lineDegree 4 p * S.blockDegree 5 p) =
        8 * S.lineCount 4 := by
    calc
      (∑ p : Point,
        S.lineDegree 4 p * (2 - S.blockDegree 5 p)) +
          (∑ p : Point,
            S.lineDegree 4 p * S.blockDegree 5 p) =
          ∑ p : Point,
            (S.lineDegree 4 p * (2 - S.blockDegree 5 p) +
              S.lineDegree 4 p * S.blockDegree 5 p) := by
        rw [Finset.sum_add_distrib]
      _ = ∑ p : Point, 2 * S.lineDegree 4 p := by
        apply Finset.sum_congr rfl
        intro p hp
        exact hdecomp p
      _ = 2 * (∑ p : Point, S.lineDegree 4 p) := by
        rw [Finset.mul_sum]
      _ = 8 * S.lineCount 4 := by rw [hinc4]; ring
  have hloss : 4 * S.lineCount 4 ≤
      ∑ p : Point,
        S.lineDegree 4 p * (2 - S.blockDegree 5 p) := by
    omega
  have hinc3 := S.line_incidence 3
  have hsumPoint :
      (∑ p : Point, S.lineDegree 3 p) +
          (∑ p : Point,
            S.lineDegree 4 p * (2 - S.blockDegree 5 p)) ≤
        ∑ p : Point,
          tenLocalLine3Cap (S.blockDegree 3 p) 0
            (S.blockDegree 5 p) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun p _hp => hpoint p
  rw [hinc3] at hsumPoint
  omega

/-! ## Configuration router -/

/-- The sharp form of the deletion row used to remove `C ≤ 27`. -/
theorem ten_circleDegree_three_add_twenty_five_le_circleCount
    {α : Type u} [Fintype α] [DecidableEq α]
    (Mel : RealPlaneMelchiorPrinciple.{u})
    (EvenArr : RealPlaneEvenArrangementPrinciple.{u})
    (Cross : RealPlaneRadicalAxisCrossBlockPrinciple.{u})
    (cfg : Configuration α) (hadm : Admissible cfg)
    (hcard : Fintype.card α = 10)
    (hcount : Erdos506.V4.circleCount cfg ≤ 32)
    (p : α) :
    (blockSystem cfg).circleDegree 3 p + 25 ≤
      Erdos506.V4.circleCount cfg := by
  have hdelCard : Fintype.card (AwayFrom p) = 9 := by
    rw [card_awayFrom, hcard]
  have hdelAdm := deletePointConfiguration_admissible_of_ten
    cfg hadm hcard hcount p
  have hnine := circleCount_ge_twenty_five_of_card_nine
    Mel EvenArr Cross (deletePointConfiguration cfg p) hdelAdm hdelCard
  have hdelete := circleDegree_three_add_circleCount_delete_le_circleCount
    cfg p
  omega

/-- Complete selected-five-circle branch under the three named geometric
kernels in `RealPlaneTenFiveGeometry`.  Every scalar face and every local
capacity comparison is proved internally. -/
theorem circleCount_ge_thirty_three_of_ten_of_selected_five_circle_of_cap
    {α : Type u} [Fintype α] [DecidableEq α]
    (Mel : RealPlaneMelchiorPrinciple.{u})
    (EvenArr : RealPlaneEvenArrangementPrinciple.{u})
    (Cross : RealPlaneRadicalAxisCrossBlockPrinciple.{u})
    (Kelly : RealPlaneKellyMoserPrinciple.{u})
    (Geometry : RealPlaneTenFiveGeometry.{u})
    (cfg : Configuration α) (hadm : Admissible cfg)
    (hcard : Fintype.card α = 10)
    (gamma : DeterminedCircle cfg)
    (hgamma : (circleTrace cfg gamma.1).card = 5)
    (hcircleCap : ∀ c : DeterminedCircle cfg,
      (circleTrace cfg c.1).card ≤ 5) :
    33 ≤ Erdos506.V4.circleCount cfg := by
  classical
  by_contra htarget
  have hcount : Erdos506.V4.circleCount cfg ≤ 32 := by omega
  let S := blockSystem cfg
  have hcap : BlockSizeCap S 5 := by
    simpa [S] using
      blockSizeCap_five_of_card_ten_of_circleCount_le_of_circle_cap_five
        cfg hadm hcard hcount hcircleCap
  have hB5Lower : 1 ≤ S.blockCount 5 := by
    simpa [S] using
      one_le_blockCount_five_of_selected_five_circle cfg gamma hgamma
  have hd3 (p : α) : S.blockDegree 3 p = 6 ∨
      S.blockDegree 3 p = 9 := by
    simpa [S] using ten_blockDegree_three_eq_six_or_nine_of_geometry
      Mel EvenArr Cross Kelly cfg hadm hcard hcount hcap p
  have hB5le5 : S.blockCount 5 ≤ 5 := by
    simpa [S] using Geometry.fiveBlockPacking cfg hadm hcard hcap
  have hB5ne5 : S.blockCount 5 ≠ 5 := by
    simpa [S] using Geometry.puncturedPentagon cfg hadm hcard hcap hd3
  have hB5ne4 : S.blockCount 5 ≠ 4 := by
    simpa [S] using Geometry.fourPentagon cfg hadm hcard hcap hd3
  have hB5Upper : S.blockCount 5 ≤ 3 := by omega
  have hlocal (p : α) : TenFiveLocalProfile S p := by
    simpa [S] using tenFiveLocalProfile_of_geometry
      Mel EvenArr Cross Kelly cfg hadm hcard hcount hcap hB5Upper p
  have htotalBridge :
      S.totalCircleCount = Erdos506.V4.circleCount cfg := by
    rw [totalCircleCount_eq_card_determinedCircle,
      ← Erdos506.V3.circleCount_eq_card_determinedCircle]
  have hcountS : S.totalCircleCount ≤ 32 := by
    rw [htotalBridge]
    exact hcount
  have hCgeTwentySeven : 27 ≤ S.totalCircleCount := by
    have hnonempty : Nonempty α := Fintype.card_pos_iff.mp (by omega)
    obtain ⟨p⟩ := hnonempty
    have hd3Lower : 6 ≤ S.blockDegree 3 p := by
      rcases hd3 p with h6 | h9 <;> omega
    have hline := ten_lineDegree_three_le_four S hcard p
    have hcircle := ten_circleDegree_three_add_twenty_five_le_circleCount
      Mel EvenArr Cross cfg hadm hcard hcount p
    rw [← htotalBridge] at hcircle
    change S.circleDegree 3 p + 25 ≤ S.totalCircleCount at hcircle
    have hsplit := blockDegree_eq_lineDegree_add_circleDegree S 3 p
    omega
  have hCgeTwentyEight : 28 ≤ S.totalCircleCount := by
    by_contra hnot
    have hCeq : S.totalCircleCount = 27 := by omega
    have hlineFour (p : α) : S.lineDegree 3 p = 4 := by
      have hd3Lower : 6 ≤ S.blockDegree 3 p := by
        rcases hd3 p with h6 | h9 <;> omega
      have hline := ten_lineDegree_three_le_four S hcard p
      have hcircle :=
        ten_circleDegree_three_add_twenty_five_le_circleCount
          Mel EvenArr Cross cfg hadm hcard hcount p
      rw [← htotalBridge, hCeq] at hcircle
      change S.circleDegree 3 p + 25 ≤ 27 at hcircle
      have hsplit := blockDegree_eq_lineDegree_add_circleDegree S 3 p
      omega
    have hinc := S.line_incidence 3
    have hsum : (∑ p : α, S.lineDegree 3 p) = 40 := by
      calc
        (∑ p : α, S.lineDegree 3 p) = ∑ _p : α, 4 := by
          apply Finset.sum_congr rfl
          intro p hp
          exact hlineFour p
        _ = 40 := by simp [hcard]
    rw [hsum] at hinc
    omega
  have hscalar := tenFiveScalarConditions_of_blockSystem
    Mel cfg hadm hcard hcap hB5Lower hB5Upper hd3
  change TenFiveScalarConditions S.totalCircleCount (S.blockCount 5)
      (S.blockCount 3) (S.blockCount 4) (tenHighPoints S).card
      (S.lineCount 3 + S.lineCount 4 + S.lineCount 5)
      (S.lineCount 4) (S.lineCount 5) at hscalar
  have hfaces := ten_five_scalar_faces hCgeTwentyEight hcountS hscalar
  let Cap : Nat := ∑ p : α,
    tenLocalLine3Cap (S.blockDegree 3 p) 0 (S.blockDegree 5 p)
  have hnoFiveLine (hL5 : S.lineCount 5 = 0) :
      3 * S.lineCount 3 ≤ Cap := by
    simpa [Cap] using ten_line_three_sum_le_qzero_capacity
      S hlocal hB5Upper hL5
  have honeFiveLine (hL5 : S.lineCount 5 = 1) :
      3 * S.lineCount 3 + 5 ≤ Cap := by
    simpa [Cap] using ten_line_three_sum_add_five_le_qzero_capacity
      S hlocal hB5Upper hL5
  have hcapSmall (hB5 : S.blockCount 5 ≤ 2) :
      Cap + 5 * S.blockCount 5 ≤ 40 + (tenHighPoints S).card := by
    simpa [Cap] using ten_qzero_capacity_sum_add_fiveB5_le
      S hcard hB5 hd3
  have hcapThree (hB5 : S.blockCount 5 = 3) :
      Cap ≤ 27 + (tenHighPoints S).card := by
    simpa [Cap] using
      ten_qzero_capacity_sum_le_of_blockCount_five_eq_three
        S hcard hB5 hd3
  have hthreeGeometry
      (hC : S.totalCircleCount = 32)
      (hB5 : S.blockCount 5 = 3)
      (hhigh : (tenHighPoints S).card = 2)
      (hL5 : S.lineCount 5 = 0)
      (hL4pos : 1 ≤ S.lineCount 4)
      (hL4le : S.lineCount 4 ≤ 3)
      (hsum : S.lineCount 3 + S.lineCount 4 = 10) : False := by
    apply Geometry.threePentagonRichLine cfg hadm hcard
    · simpa [S] using hcap
    · simpa [S] using hC
    · simpa [S] using hB5
    · simpa [S] using hhigh
    · simpa [S] using hL5
    · simpa [S] using hL4pos
    · simpa [S] using hL4le
    · simpa [S] using hsum
    · intro p
      simpa [S] using hlocal p
  rcases hfaces with h30 | h31 | h32
  · rcases h30 with ⟨hC, hk, hL4, hL5⟩
    have hline := hnoFiveLine hL5
    rcases hk with hk2 | hk3
    · rcases hk2 with ⟨hB5, hhigh, hL⟩
      have hcapSum := hcapSmall (by omega)
      omega
    · rcases hk3 with ⟨hB5, hhigh, hL⟩
      have hcapSum := hcapThree hB5
      omega
  · rcases h31 with ⟨hC, hk, hlineState⟩
    rcases hk with hk2 | hk3
    · rcases hk2 with ⟨hB5, hhigh, hL⟩
      have hcapSum := hcapSmall (by omega)
      rcases hlineState with hzero | hone
      · rcases hzero with ⟨hL4, hL5⟩
        have hline := hnoFiveLine hL5
        omega
      · rcases hone with ⟨hL4, hL5⟩
        have hlineLoss := ten_two_pentagon_four_line_capacity
          S hB5 hhigh hL5 (by omega) hlocal
        have hlineLoss' : 3 * S.lineCount 3 +
            4 * S.lineCount 4 ≤ Cap := by simpa [Cap] using hlineLoss
        omega
    · rcases hk3 with ⟨hB5, hhigh, hL⟩
      have hcapSum := hcapThree hB5
      rcases hlineState with hzero | hone
      · rcases hzero with ⟨hL4, hL5⟩
        have hline := hnoFiveLine hL5
        omega
      · rcases hone with ⟨hL4, hL5⟩
        have hline := hnoFiveLine hL5
        omega
  · rcases h32 with ⟨hC, hrow⟩
    rcases hrow with hL13 | hk2 | hk3
    · rcases hL13 with ⟨hk, hL4, hL5⟩
      have hline := hnoFiveLine hL5
      rcases hk with hk1 | hk2 | hk3
      · rcases hk1 with ⟨hB5, hhigh, hL⟩
        have hcapSum := hcapSmall (by omega)
        omega
      · rcases hk2 with ⟨hB5, hhigh, hL⟩
        have hcapSum := hcapSmall (by omega)
        omega
      · rcases hk3 with ⟨hB5, hhigh, hL⟩
        have hcapSum := hcapThree hB5
        omega
    · rcases hk2 with ⟨hB5, hhigh, hL, hlineState⟩
      have hcapSum := hcapSmall (by omega)
      rcases hlineState with h00 | h10 | h20 | h01
      · rcases h00 with ⟨hL4, hL5⟩
        have hs := hscalar
        rcases hs with
          ⟨_hB5Lower, _hB5Upper, hB3row, htriple,
            _hline, _hAC, _hhighBound, _hrichBound⟩
        have hB3 : S.blockCount 3 = 20 := by omega
        have hB4 : S.blockCount 4 = 20 := by omega
        have hL3 : S.lineCount 3 = 10 := by omega
        have hd3six (p : α) : S.blockDegree 3 p = 6 := by
          have hhighEmpty : tenHighPoints S = ∅ :=
            Finset.card_eq_zero.mp hhigh
          rcases hd3 p with h6 | h9
          · exact h6
          · have hp : p ∈ tenHighPoints S := mem_tenHighPoints.mpr h9
            rw [hhighEmpty] at hp
            simp at hp
        exact (Geometry.disjointGoldenLink cfg hadm hcard
          hC hB3 hB4 hB5 hL3 hL4 hL5 hd3six).elim
      · rcases h10 with ⟨hL4, hL5⟩
        have hlineLoss := ten_two_pentagon_four_line_capacity
          S hB5 hhigh hL5 (by omega) hlocal
        have hlineLoss' : 3 * S.lineCount 3 +
            4 * S.lineCount 4 ≤ Cap := by simpa [Cap] using hlineLoss
        omega
      · rcases h20 with ⟨hL4, hL5⟩
        have hlineLoss := ten_two_pentagon_four_line_capacity
          S hB5 hhigh hL5 (by omega) hlocal
        have hlineLoss' : 3 * S.lineCount 3 +
            4 * S.lineCount 4 ≤ Cap := by simpa [Cap] using hlineLoss
        omega
      · rcases h01 with ⟨hL4, hL5⟩
        have hline := honeFiveLine hL5
        omega
    · rcases hk3 with ⟨hB5, hhigh, hL, hlineState⟩
      have hcapSum := hcapThree hB5
      rcases hlineState with h00 | h10 | h20 | h30 | h01
      · rcases h00 with ⟨hL4, hL5⟩
        have hline := hnoFiveLine hL5
        omega
      · rcases h10 with ⟨hL4, hL5⟩
        exact (hthreeGeometry hC hB5 hhigh hL5
          (by omega) (by omega) (by omega)).elim
      · rcases h20 with ⟨hL4, hL5⟩
        exact (hthreeGeometry hC hB5 hhigh hL5
          (by omega) (by omega) (by omega)).elim
      · rcases h30 with ⟨hL4, hL5⟩
        exact (hthreeGeometry hC hB5 hhigh hL5
          (by omega) (by omega) (by omega)).elim
      · rcases h01 with ⟨hL4, hL5⟩
        have hline := honeFiveLine hL5
        omega

/-- Public selected-five-circle theorem.  If a six-circle exists, the
already checked U17 branch closes it; otherwise the preceding cap-five
kernel applies. -/
theorem circleCount_ge_thirty_three_of_ten_of_selected_five_circle
    {α : Type u} [Fintype α] [DecidableEq α]
    (Mel : RealPlaneMelchiorPrinciple.{u})
    (EvenArr : RealPlaneEvenArrangementPrinciple.{u})
    (Cross : RealPlaneRadicalAxisCrossBlockPrinciple.{u})
    (Kelly : RealPlaneKellyMoserPrinciple.{u})
    (U17 : RealPlaneSixCircleU17Principle.{u})
    (Geometry : RealPlaneTenFiveGeometry.{u})
    (cfg : Configuration α) (hadm : Admissible cfg)
    (hcard : Fintype.card α = 10)
    (gamma : DeterminedCircle cfg)
    (hgamma : (circleTrace cfg gamma.1).card = 5) :
    33 ≤ Erdos506.V4.circleCount cfg := by
  by_contra htarget
  have hcount : Erdos506.V4.circleCount cfg ≤ 32 := by omega
  have hcapSix : ∀ c : DeterminedCircle cfg,
      (circleTrace cfg c.1).card ≤ 6 :=
    circleTrace_card_le_six_of_ten_of_circleCount_le
      cfg hadm hcard hcount
  by_cases hcapFive : ∀ c : DeterminedCircle cfg,
      (circleTrace cfg c.1).card ≤ 5
  · exact htarget
      (circleCount_ge_thirty_three_of_ten_of_selected_five_circle_of_cap
        Mel EvenArr Cross Kelly Geometry cfg hadm hcard gamma hgamma hcapFive)
  · push Not at hcapFive
    obtain ⟨delta, hdeltaLarge⟩ := hcapFive
    have hdelta : (circleTrace cfg delta.1).card = 6 := by
      have := hcapSix delta
      omega
    have hsix := circleCount_ge_thirty_three_of_ten_of_selected_six_circle
      Mel U17 cfg hadm hcard delta hdelta hcapSix
    exact htarget hsix

/-- Full ten-point lower bound.  The cap-four and cap-six branches use the
existing checked routers; the selected-five branch is discharged above. -/
theorem circleCount_ge_thirty_three_of_card_ten
    {α : Type u} [Fintype α] [DecidableEq α]
    (Mel : RealPlaneMelchiorPrinciple.{u})
    (EvenArr : RealPlaneEvenArrangementPrinciple.{u})
    (Cross : RealPlaneRadicalAxisCrossBlockPrinciple.{u})
    (Kelly : RealPlaneKellyMoserPrinciple.{u})
    (U17 : RealPlaneSixCircleU17Principle.{u})
    (Geometry : RealPlaneTenFiveGeometry.{u})
    (cfg : Configuration α) (hadm : Admissible cfg)
    (hcard : Fintype.card α = 10) :
    33 ≤ Erdos506.V4.circleCount cfg := by
  apply circleCount_ge_thirty_three_of_card_ten_of_five_circle_endpoint
    Mel EvenArr Kelly U17 cfg hadm hcard
  intro gamma hgamma
  exact circleCount_ge_thirty_three_of_ten_of_selected_five_circle
    Mel EvenArr Cross Kelly U17 Geometry cfg hadm hcard gamma hgamma

end Erdos506.V1
