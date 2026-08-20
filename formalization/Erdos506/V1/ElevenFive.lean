import Erdos506.Block.RelativeRows
import Erdos506.Incidence.EvenArrangementPrinciple
import Erdos506.Incidence.OrdinaryPrinciples
import Erdos506.V1.Deletion
import Erdos506.V1.DirectKelly
import Erdos506.V1.ElevenGammaSixConfiguration
import Erdos506.Finite.CompletePentagonPencil
import Erdos506.V1.ElevenTwelveOuter
import Erdos506.V1.LargeMaster
import Erdos506.V1.TenFive
import Erdos506.V1.UniversalRows

/-!
# The eleven-point selected-five-circle branch

This file materializes the `n = 11`, selected-five-circle calculation from
the canonical tagged block system.  The exact triple, line, pivot,
restored-centre, deletion, and relative host rows are proved below.  The
remaining real inputs are exposed by `RealPlaneElevenFiveGeometry` as local
positive certificates: the K3 harmonic-incidence cap, one K2 maximum-host
overload, and explicit triple-collision witnesses for the residual K2/K3
face catalogues.  No field
states `False`, negates a
complete circle-count layer, or returns the target `41 <= circleCount cfg`.

The public theorem first dispatches an actual six-circle to
`ElevenGammaSix`.  In the maximum-circle-five branch it invokes the checked
ten-point theorem only on literal one-point deletions.
-/

namespace Erdos506.V1

open Erdos506.Block
open Erdos506.Block.BlockSystem
open Erdos506.Incidence
open Erdos506.V4
open scoped BigOperators

universe u

private theorem elevenFive_blockCount_eq_zero_of_cap
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

private theorem elevenFive_lineCount_eq_zero_of_blockCount_eq_zero
    {Point Block : Type*} [Fintype Point] [Fintype Block]
    [DecidableEq Point]
    (S : BlockSystem Point Block) (s : Nat)
    (hzero : S.blockCount s = 0) : S.lineCount s = 0 := by
  have hsplit := S.blockCount_eq_lineCount_add_circleCount s
  omega

private theorem elevenFive_circleCount_eq_zero_of_blockCount_eq_zero
    {Point Block : Type*} [Fintype Point] [Fintype Block]
    [DecidableEq Point]
    (S : BlockSystem Point Block) (s : Nat)
    (hzero : S.blockCount s = 0) : S.circleCount s = 0 := by
  have hsplit := S.blockCount_eq_lineCount_add_circleCount s
  omega

private theorem elevenFive_blockDegree_eq_zero_of_blockCount_eq_zero
    {Point Block : Type*} [Fintype Point] [Fintype Block]
    [DecidableEq Point]
    (S : BlockSystem Point Block) (s : Nat) (p : Point)
    (hzero : S.blockCount s = 0) : S.blockDegree s p = 0 := by
  have hinc := S.block_incidence s
  rw [hzero] at hinc
  have hle : S.blockDegree s p <=
      ∑ q : Point, S.blockDegree s q :=
    Finset.single_le_sum
      (fun q _hq => Nat.zero_le (S.blockDegree s q)) (Finset.mem_univ p)
  omega

private theorem elevenFive_lineDegree_eq_zero_of_lineCount_eq_zero
    {Point Block : Type*} [Fintype Point] [Fintype Block]
    [DecidableEq Point]
    (S : BlockSystem Point Block) (s : Nat) (p : Point)
    (hzero : S.lineCount s = 0) : S.lineDegree s p = 0 := by
  have hinc := S.line_incidence s
  rw [hzero] at hinc
  have hle : S.lineDegree s p <=
      ∑ q : Point, S.lineDegree s q :=
    Finset.single_le_sum
      (fun q _hq => Nat.zero_le (S.lineDegree s q)) (Finset.mem_univ p)
  omega

/-- Total number of maximal lines when every nontrivial block has size at
most five. -/
noncomputable def elevenFiveLineTotal
    {Point Block : Type*} [Fintype Point] [Fintype Block]
    [DecidableEq Point] (S : BlockSystem Point Block) : Nat :=
  S.lineCount 3 + S.lineCount 4 + S.lineCount 5

/-- The pair moment of the generalized five-block family. -/
noncomputable def elevenFiveSecondMoment
    {Point Block : Type*} [Fintype Point] [Fintype Block]
    [DecidableEq Point] (S : BlockSystem Point Block) : Nat :=
  ∑ p : Point, Nat.choose (S.blockDegree 5 p) 2

/-- Pivots of the harmonic K3 type `(d3,d4,d5) = (9,4,4)`. -/
noncomputable def elevenFiveHarmonicPivots
    {Point Block : Type*} [Fintype Point] [Fintype Block]
    [DecidableEq Point] (S : BlockSystem Point Block) : Finset Point :=
  Finset.univ.filter fun p =>
    S.blockDegree 3 p = 9 /\ S.blockDegree 4 p = 4 /\
      S.blockDegree 5 p = 4

/-- Blocks with a two-point trace on a selected five-set. -/
noncomputable def elevenFiveHostFamily
    {Point Block : Type*} [Fintype Point] [Fintype Block]
    [DecidableEq Point] (S : BlockSystem Point Block) (D : Finset Point) :
    Finset Block :=
  Finset.univ.filter fun b => (S.support b ∩ D).card = 2

/-- Host load on outsider pairs.  A four-block contributes one and a
five-block contributes three; smaller blocks contribute zero automatically. -/
noncomputable def elevenFiveHostWeight
    {Point Block : Type*} [Fintype Point] [Fintype Block]
    [DecidableEq Point] (S : BlockSystem Point Block) (D : Finset Point) :
    Nat :=
  ∑ b ∈ elevenFiveHostFamily S D,
    Nat.choose (S.support b \ D).card 2

/-- A positive, concrete violation of unique triple ownership. -/
def ElevenFiveTripleCollision
    {Point Block : Type*} [Fintype Point] [Fintype Block]
    [DecidableEq Point] (S : BlockSystem Point Block) : Prop :=
  ∃ b c : Block, b ≠ c /\ 3 <= (S.support b ∩ S.support c).card

theorem elevenFive_no_tripleCollision
    {Point Block : Type*} [Fintype Point] [Fintype Block]
    [DecidableEq Point] (S : BlockSystem Point Block) :
    ¬ ElevenFiveTripleCollision S := by
  rintro ⟨b, c, hbc, hinter⟩
  have hlt := S.distinct_block_inter_card_lt_three hbc
  omega

/-- The still-geometric local K2/K3 certificates in the eleven-five proof.

The collision fields expose actual pairs of blocks sharing a triple.  The
`C=39` field exposes an actual selected five-circle whose outsider host load
is at least thirty-one.  These are positive local witnesses, and the generic
block calculus proves below that their capacities are respectively zero and
thirty. -/
structure RealPlaneElevenFiveGeometry where
  harmonicIncidenceCap :
    ∀ {α : Type u} [Fintype α] [DecidableEq α]
      (cfg : Configuration α),
      Admissible cfg → Fintype.card α = 11 →
      BlockSizeCap (blockSystem cfg) 5 →
        4 * (elevenFiveHarmonicPivots (blockSystem cfg)).card <=
          2 * (blockSystem cfg).blockCount 5
  c39MaximumHostOverload :
    ∀ {α : Type u} [Fintype α] [DecidableEq α]
      (cfg : Configuration α),
      Admissible cfg → Fintype.card α = 11 →
      BlockSizeCap (blockSystem cfg) 5 →
      Erdos506.V4.circleCount cfg = 39 →
      elevenFiveLineTotal (blockSystem cfg) = 12 →
      ∃ delta : DeterminedCircle cfg,
        (circleTrace cfg delta.1).card = 5 /\
          31 <= elevenFiveHostWeight (blockSystem cfg)
            (circleTrace cfg delta.1)
  c40ElevenSmallFaceCollision :
    ∀ {α : Type u} [Fintype α] [DecidableEq α]
      (cfg : Configuration α),
      Admissible cfg → Fintype.card α = 11 →
      BlockSizeCap (blockSystem cfg) 5 →
      Erdos506.V4.circleCount cfg = 40 →
      elevenFiveLineTotal (blockSystem cfg) = 11 →
      ((blockSystem cfg).blockCount 5 = 5 ∨
        (blockSystem cfg).blockCount 5 = 6) →
        ElevenFiveTripleCollision (blockSystem cfg)
  c40ElevenSevenDefectCollision :
    ∀ {α : Type u} [Fintype α] [DecidableEq α]
      (cfg : Configuration α),
      Admissible cfg → Fintype.card α = 11 →
      BlockSizeCap (blockSystem cfg) 5 →
      Erdos506.V4.circleCount cfg = 40 →
      elevenFiveLineTotal (blockSystem cfg) = 11 →
      (blockSystem cfg).blockCount 5 = 7 →
        ElevenFiveTripleCollision (blockSystem cfg)
  c40FourteenSevenExternalTraceCollision :
    ∀ {α : Type u} [Fintype α] [DecidableEq α]
      (cfg : Configuration α),
      Admissible cfg → Fintype.card α = 11 →
      BlockSizeCap (blockSystem cfg) 5 →
      Erdos506.V4.circleCount cfg = 40 →
      elevenFiveLineTotal (blockSystem cfg) = 14 →
      (blockSystem cfg).blockCount 5 = 7 →
        ElevenFiveTripleCollision (blockSystem cfg)
  c40FourteenEightDefectCollision :
    ∀ {α : Type u} [Fintype α] [DecidableEq α]
      (cfg : Configuration α),
      Admissible cfg → Fintype.card α = 11 →
      BlockSizeCap (blockSystem cfg) 5 →
      Erdos506.V4.circleCount cfg = 40 →
      elevenFiveLineTotal (blockSystem cfg) = 14 →
      (blockSystem cfg).blockCount 5 = 8 →
        ElevenFiveTripleCollision (blockSystem cfg)

/-- The two matching slots available for every outsider pair give the
universal K1 host cap `H <= 30`. -/
theorem elevenFiveHostWeight_le_thirty
    {Point Block : Type*} [Fintype Point] [Fintype Block]
    [DecidableEq Point]
    (S : BlockSystem Point Block) (D : Finset Point)
    (hpoint : Fintype.card Point = 11) (hD : D.card = 5) :
    elevenFiveHostWeight S D <= 30 := by
  classical
  have hcap := relative_two_two_capacity S D
    (elevenFiveHostFamily S D) (by
      intro b hb
      exact (Finset.mem_filter.mp hb).2)
  simpa [elevenFiveHostWeight, hpoint, hD, Nat.choose] using hcap

/-- Nonnegative natural representatives of the two local Melchior slacks. -/
noncomputable def elevenFiveSigmaAt
    {Point Block : Type*} [Fintype Point] [Fintype Block]
    [DecidableEq Point] (S : BlockSystem Point Block) (p : Point) : Nat :=
  Int.toNat (S.pivotSigma p)

noncomputable def elevenFiveKappaAt
    {Point Block : Type*} [Fintype Point] [Fintype Block]
    [DecidableEq Point] (S : BlockSystem Point Block) (p : Point) : Nat :=
  Int.toNat (S.restoredKappa p)

noncomputable def elevenFiveSigmaTotal
    {Point Block : Type*} [Fintype Point] [Fintype Block]
    [DecidableEq Point] (S : BlockSystem Point Block) : Nat :=
  ∑ p : Point, elevenFiveSigmaAt S p

noncomputable def elevenFiveKappaTotal
    {Point Block : Type*} [Fintype Point] [Fintype Block]
    [DecidableEq Point] (S : BlockSystem Point Block) : Nat :=
  ∑ p : Point, elevenFiveKappaAt S p

/-- Exact pointwise rows in the maximum-block-five branch. -/
structure ElevenFiveLocalRows
    {Point Block : Type*} [Fintype Point] [Fintype Block]
    [DecidableEq Point] (S : BlockSystem Point Block) (p : Point) : Prop where
  pairRow :
    S.blockDegree 3 p + 3 * S.blockDegree 4 p +
      6 * S.blockDegree 5 p = 45
  sigmaRow :
    elevenFiveSigmaAt S p + 3 + S.blockDegree 5 p =
      S.blockDegree 3 p
  lineArmRow :
    S.lineDegree 2 p + 2 * S.lineDegree 3 p +
      3 * S.lineDegree 4 p + 4 * S.lineDegree 5 p = 10
  kappaRow :
    elevenFiveKappaAt S p + 3 * S.lineDegree 3 p +
        4 * S.lineDegree 4 p + 5 * S.lineDegree 5 p =
      10 + elevenFiveSigmaAt S p
  threeSplit :
    S.blockDegree 3 p = S.lineDegree 3 p + S.circleDegree 3 p
  kelly : 5 <= S.blockDegree 3 p
  deletion :
    S.circleDegree 3 p + 33 <= S.totalCircleCount
  langer : 2 * S.blockDegree 5 p <= S.blockDegree 3 p + 1
  fiveDegreeCap : S.blockDegree 5 p <= 4

/-- Exact aggregate rows used by every boundary dispatch. -/
structure ElevenFiveGlobalRows
    {Point Block : Type*} [Fintype Point] [Fintype Block]
    [DecidableEq Point] (S : BlockSystem Point Block) : Prop where
  tripleRow :
    S.blockCount 3 + 4 * S.blockCount 4 +
      10 * S.blockCount 5 = 165
  blockTotal :
    S.blockCount 3 + S.blockCount 4 + S.blockCount 5 =
      S.totalCircleCount + elevenFiveLineTotal S
  circleTotal :
    S.totalCircleCount =
      S.circleCount 3 + S.circleCount 4 + S.circleCount 5
  sigmaRow :
    elevenFiveSigmaTotal S + 33 + 5 * S.blockCount 5 =
      3 * S.blockCount 3
  kappaRow :
    elevenFiveKappaTotal S + 9 * S.lineCount 3 +
        16 * S.lineCount 4 + 25 * S.lineCount 5 =
      110 + elevenFiveSigmaTotal S
  lineMelchior :
    3 * elevenFiveLineTotal S + 4 * S.lineCount 4 +
      9 * S.lineCount 5 <= 52
  threeIncidence :
    (∑ p : Point, S.blockDegree 3 p) = 3 * S.blockCount 3
  circleThreeIncidence :
    (∑ p : Point, S.circleDegree 3 p) = 3 * S.circleCount 3
  fiveIncidence :
    (∑ p : Point, S.blockDegree 5 p) = 5 * S.blockCount 5
  secondMomentCap :
    elevenFiveSecondMoment S <= 2 * Nat.choose (S.blockCount 5) 2

private theorem elevenFive_totalCircleCount_eq_circleCount
    {α : Type u} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) :
    (blockSystem cfg).totalCircleCount = Erdos506.V4.circleCount cfg := by
  rw [totalCircleCount_eq_card_determinedCircle,
    ← Erdos506.V3.circleCount_eq_card_determinedCircle]

private theorem elevenFive_globalLineRow_eq_weighted
    {Point Block : Type*} [Fintype Point] [Fintype Block]
    [DecidableEq Point] (S : BlockSystem Point Block) :
    S.globalLineRow =
      ∑ s ∈ Finset.range (Fintype.card Point + 1),
        ((if 3 <= s then Nat.choose s 2 + s - 3 else 0 : Nat) : Int) *
          (S.lineCount s : Int) := by
  classical
  let w : Nat → Nat := fun s =>
    if 3 <= s then Nat.choose s 2 + s - 3 else 0
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
      (if 3 <= (S.support b.1).card then
          (Nat.choose (S.support b.1).card 2 : Int) +
            ((S.support b.1).card : Int) - 3
        else 0) = (w (S.support b.1).card : Int) := by
    dsimp only [w]
    split_ifs with hthree
    · omega
    · rfl
  have hglobal :
      S.globalLineRow =
        ((∑ b ∈ S.blocksOfKind .line,
          w (S.support b).card : Nat) : Int) := by
    unfold BlockSystem.globalLineRow
    calc
      (∑ b : LineBlock S,
          if 3 <= (S.support b.1).card then
            (Nat.choose (S.support b.1).card 2 : Int) +
              ((S.support b.1).card : Int) - 3
          else 0) =
          ∑ b : LineBlock S, (w (S.support b.1).card : Int) := by
            apply Fintype.sum_congr
            exact hpoint
      _ = ((∑ b : LineBlock S, w (S.support b.1).card : Nat) : Int) := by
            norm_num
      _ = ((∑ b ∈ S.blocksOfKind .line,
          w (S.support b).card : Nat) : Int) := by rw [hsubtype]
  rw [hglobal]
  rw [← hgroup]
  norm_num [w, BlockSystem.lineCount]

private theorem elevenFive_globalLineRow_eq
    {Point Block : Type*} [Fintype Point] [Fintype Block]
    [DecidableEq Point]
    (S : BlockSystem Point Block) (hcard : Fintype.card Point = 11)
    (hcap : BlockSizeCap S 5) :
    S.globalLineRow =
      3 * (S.lineCount 3 : Int) + 7 * (S.lineCount 4 : Int) +
        12 * (S.lineCount 5 : Int) := by
  have hl6 : S.lineCount 6 = 0 :=
    elevenFive_lineCount_eq_zero_of_blockCount_eq_zero S 6
      (elevenFive_blockCount_eq_zero_of_cap S hcap (by omega))
  have hl7 : S.lineCount 7 = 0 :=
    elevenFive_lineCount_eq_zero_of_blockCount_eq_zero S 7
      (elevenFive_blockCount_eq_zero_of_cap S hcap (by omega))
  have hl8 : S.lineCount 8 = 0 :=
    elevenFive_lineCount_eq_zero_of_blockCount_eq_zero S 8
      (elevenFive_blockCount_eq_zero_of_cap S hcap (by omega))
  have hl9 : S.lineCount 9 = 0 :=
    elevenFive_lineCount_eq_zero_of_blockCount_eq_zero S 9
      (elevenFive_blockCount_eq_zero_of_cap S hcap (by omega))
  have hl10 : S.lineCount 10 = 0 :=
    elevenFive_lineCount_eq_zero_of_blockCount_eq_zero S 10
      (elevenFive_blockCount_eq_zero_of_cap S hcap (by omega))
  have hl11 : S.lineCount 11 = 0 :=
    elevenFive_lineCount_eq_zero_of_blockCount_eq_zero S 11
      (elevenFive_blockCount_eq_zero_of_cap S hcap (by omega))
  rw [elevenFive_globalLineRow_eq_weighted, hcard]
  norm_num [Finset.sum_range_succ, Nat.choose,
    hl6, hl7, hl8, hl9, hl10, hl11]

/-- Every local row is obtained from Melchior, the remaining finite incidence
principles, and the literal ten-point deletion.  Langer is not needed at
eleven points: its former local slope follows from `sigma ≥ 0` and `d₅ ≤ 4`. -/
theorem elevenFiveLocalRows_of_configuration_without_langer
    {α : Type u} [Fintype α] [DecidableEq α]
    (Mel : RealPlaneMelchiorPrinciple.{u})
    (EvenArr : RealPlaneEvenArrangementPrinciple.{u})
    (Cross : RealPlaneRadicalAxisCrossBlockPrinciple.{u})
    (Kelly : RealPlaneKellyMoserPrinciple.{u})
    (U17 : RealPlaneSixCircleU17Principle.{u})
    (TenGeometry : RealPlaneTenFiveGeometry.{u})
    (cfg : Configuration α) (hadm : Admissible cfg)
    (hcard : Fintype.card α = 11)
    (hcap : BlockSizeCap (blockSystem cfg) 5)
    (hCupper : (blockSystem cfg).totalCircleCount <= 40)
    (p : α) : ElevenFiveLocalRows (blockSystem cfg) p := by
  classical
  let S := blockSystem cfg
  have hb6 := elevenFive_blockCount_eq_zero_of_cap S hcap
    (s := 6) (by omega)
  have hb7 := elevenFive_blockCount_eq_zero_of_cap S hcap
    (s := 7) (by omega)
  have hb8 := elevenFive_blockCount_eq_zero_of_cap S hcap
    (s := 8) (by omega)
  have hb9 := elevenFive_blockCount_eq_zero_of_cap S hcap
    (s := 9) (by omega)
  have hb10 := elevenFive_blockCount_eq_zero_of_cap S hcap
    (s := 10) (by omega)
  have hb11 := elevenFive_blockCount_eq_zero_of_cap S hcap
    (s := 11) (by omega)
  have hd6 := elevenFive_blockDegree_eq_zero_of_blockCount_eq_zero S 6 p hb6
  have hd7 := elevenFive_blockDegree_eq_zero_of_blockCount_eq_zero S 7 p hb7
  have hd8 := elevenFive_blockDegree_eq_zero_of_blockCount_eq_zero S 8 p hb8
  have hd9 := elevenFive_blockDegree_eq_zero_of_blockCount_eq_zero S 9 p hb9
  have hd10 := elevenFive_blockDegree_eq_zero_of_blockCount_eq_zero S 10 p hb10
  have hd11 := elevenFive_blockDegree_eq_zero_of_blockCount_eq_zero S 11 p hb11
  have hl6 := elevenFive_lineCount_eq_zero_of_blockCount_eq_zero S 6 hb6
  have hl7 := elevenFive_lineCount_eq_zero_of_blockCount_eq_zero S 7 hb7
  have hl8 := elevenFive_lineCount_eq_zero_of_blockCount_eq_zero S 8 hb8
  have hl9 := elevenFive_lineCount_eq_zero_of_blockCount_eq_zero S 9 hb9
  have hl10 := elevenFive_lineCount_eq_zero_of_blockCount_eq_zero S 10 hb10
  have hl11 := elevenFive_lineCount_eq_zero_of_blockCount_eq_zero S 11 hb11
  have hld6 := elevenFive_lineDegree_eq_zero_of_lineCount_eq_zero S 6 p hl6
  have hld7 := elevenFive_lineDegree_eq_zero_of_lineCount_eq_zero S 7 p hl7
  have hld8 := elevenFive_lineDegree_eq_zero_of_lineCount_eq_zero S 8 p hl8
  have hld9 := elevenFive_lineDegree_eq_zero_of_lineCount_eq_zero S 9 p hl9
  have hld10 := elevenFive_lineDegree_eq_zero_of_lineCount_eq_zero S 10 p hl10
  have hld11 := elevenFive_lineDegree_eq_zero_of_lineCount_eq_zero S 11 p hl11
  have hIcc : Finset.Icc 3 11 = {3, 4, 5, 6, 7, 8, 9, 10, 11} := by
    decide
  have hpairs := S.pivot_pair_partition p
  rw [hcard] at hpairs
  norm_num [Finset.sum_range_succ, Nat.choose,
    hd6, hd7, hd8, hd9, hd10, hd11] at hpairs
  have harms := S.line_arms p
  rw [hcard] at harms
  norm_num [Finset.sum_range_succ,
    hld6, hld7, hld8, hld9, hld10, hld11] at harms
  have hsigmaNonneg : 0 <= S.pivotSigma p := by
    simpa [S] using sigma_nonneg_of_realPlaneMelchior
      Mel cfg hadm (by omega) p
  have hkappaNonneg : 0 <= S.restoredKappa p := by
    simpa [S] using kappa_nonneg_of_realPlaneMelchior
      Mel cfg hadm (by omega) p
  have hsigmaZ :
      S.pivotSigma p + 3 + (S.blockDegree 5 p : Int) =
        S.blockDegree 3 p := by
    unfold BlockSystem.pivotSigma BlockSystem.nontrivialSizes
    rw [hcard, hIcc]
    norm_num [hd6, hd7, hd8, hd9, hd10, hd11]
  have hkappaZ :
      S.restoredKappa p + 3 * (S.lineDegree 3 p : Int) +
          4 * (S.lineDegree 4 p : Int) +
          5 * (S.lineDegree 5 p : Int) =
        10 + S.pivotSigma p := by
    unfold BlockSystem.restoredKappa BlockSystem.nontrivialSizes
    rw [hcard, hIcc]
    norm_num [hld6, hld7, hld8, hld9, hld10, hld11]
    omega
  have hsigmaCast : (elevenFiveSigmaAt S p : Int) = S.pivotSigma p := by
    exact Int.toNat_of_nonneg hsigmaNonneg
  have hkappaCast : (elevenFiveKappaAt S p : Int) = S.restoredKappa p := by
    exact Int.toNat_of_nonneg hkappaNonneg
  have hsigma :
      elevenFiveSigmaAt S p + 3 + S.blockDegree 5 p =
        S.blockDegree 3 p := by
    exact_mod_cast (show
      (elevenFiveSigmaAt S p : Int) + 3 + (S.blockDegree 5 p : Int) =
        (S.blockDegree 3 p : Int) by omega)
  have hkappa :
      elevenFiveKappaAt S p + 3 * S.lineDegree 3 p +
          4 * S.lineDegree 4 p + 5 * S.lineDegree 5 p =
        10 + elevenFiveSigmaAt S p := by
    exact_mod_cast (show
      (elevenFiveKappaAt S p : Int) + 3 * (S.lineDegree 3 p : Int) +
          4 * (S.lineDegree 4 p : Int) + 5 * (S.lineDegree 5 p : Int) =
        10 + (elevenFiveSigmaAt S p : Int) by omega)
  have hsplit := blockDegree_eq_lineDegree_add_circleDegree S 3 p
  have hkellyRaw := Kelly.pivot_three_block_bound cfg hadm
    (by omega) (by omega) p
  rw [hcard] at hkellyRaw
  change 3 * (11 - 1) <=
    7 * (blockSystem cfg).blockDegree 3 p at hkellyRaw
  norm_num at hkellyRaw
  have hkelly : 5 <= S.blockDegree 3 p := by
    have hkellyCfg : 5 <= (blockSystem cfg).blockDegree 3 p := by
      omega
    simpa [S] using hkellyCfg
  have hlineGeom : ∀ L : DeterminedLine cfg,
      (lineSupport cfg L).card <= 5 := by
    intro L
    by_cases hthree : 3 <= (lineSupport cfg L).card
    · simpa [blockSystem, geometricBlockSystem, geometricBlockSupport] using
        hcap (Sum.inl L) (by
          simpa [blockSystem, geometricBlockSystem, geometricBlockSupport]
            using hthree)
    · omega
  have hcircleGeom : ∀ c : DeterminedCircle cfg,
      (circleTrace cfg c.1).card <= 5 := by
    intro c
    simpa [blockSystem, geometricBlockSystem, geometricBlockSupport] using
      hcap (Sum.inr c) (by
        simpa [blockSystem, geometricBlockSystem, geometricBlockSupport] using
          Erdos506.V3.circleSupport_card_ge_three cfg c)
  have hAway : Fintype.card (Erdos506.V3.AwayFrom p) = 10 := by
    rw [Erdos506.V3.card_awayFrom, hcard]
  have hdeleteAdm : Admissible (deletePointConfiguration cfg p) := by
    constructor
    · exact deletePointConfiguration_noncollinear_of_line_cap
        cfg p (by omega) hlineGeom
    · exact deletePointConfiguration_notConcyclic_of_circle_cap
        cfg p (by omega) (fun c => (hcircleGeom c).trans (by omega))
  have hten := circleCount_ge_thirty_three_of_card_ten
    Mel EvenArr Cross Kelly U17 TenGeometry
    (deletePointConfiguration cfg p) hdeleteAdm hAway
  have hdeleteRaw :=
    circleDegree_three_add_circleCount_delete_le_circleCount cfg p
  have hcircleBridge := elevenFive_totalCircleCount_eq_circleCount cfg
  have hdelete :
      S.circleDegree 3 p + 33 <= S.totalCircleCount := by
    have hdeleteCfg :
        (blockSystem cfg).circleDegree 3 p + 33 <=
          (blockSystem cfg).totalCircleCount := by
      rw [hcircleBridge]
      omega
    simpa [S] using hdeleteCfg
  have hCupperS : S.totalCircleCount <= 40 := by
    simpa [S] using hCupper
  have hd3cap : S.blockDegree 3 p <= 12 := by
    have hc3 : S.circleDegree 3 p <= 7 := by omega
    have hl3 : S.lineDegree 3 p <= 5 := by omega
    omega
  have hd5cap : S.blockDegree 5 p <= 4 :=
    Erdos506.Finite.blockDegree_five_le_four_of_card_eleven_of_pairRow
      S hcard p hpairs hd3cap
  have hlanger : 2 * S.blockDegree 5 p <= S.blockDegree 3 p + 1 := by
    omega
  exact ⟨hpairs, hsigma, harms, hkappa, hsplit, hkelly,
    hdelete, hlanger, hd5cap⟩

/-- Compatibility wrapper for downstream files that still thread the global
Langer principle.  The proof at eleven points is independent of that input. -/
theorem elevenFiveLocalRows_of_configuration
    {α : Type u} [Fintype α] [DecidableEq α]
    (Mel : RealPlaneMelchiorPrinciple.{u})
    (_Langer : RealPlaneLangerPrinciple.{u})
    (EvenArr : RealPlaneEvenArrangementPrinciple.{u})
    (Cross : RealPlaneRadicalAxisCrossBlockPrinciple.{u})
    (Kelly : RealPlaneKellyMoserPrinciple.{u})
    (U17 : RealPlaneSixCircleU17Principle.{u})
    (TenGeometry : RealPlaneTenFiveGeometry.{u})
    (cfg : Configuration α) (hadm : Admissible cfg)
    (hcard : Fintype.card α = 11)
    (hcap : BlockSizeCap (blockSystem cfg) 5)
    (hCupper : (blockSystem cfg).totalCircleCount <= 40)
    (p : α) : ElevenFiveLocalRows (blockSystem cfg) p :=
  elevenFiveLocalRows_of_configuration_without_langer
    Mel EvenArr Cross Kelly U17 TenGeometry
      cfg hadm hcard hcap hCupper p

/-- The exact global census, obtained by summing the preceding local rows
and expanding only the three surviving size layers. -/
theorem elevenFiveGlobalRows_of_configuration
    {α : Type u} [Fintype α] [DecidableEq α]
    (Mel : RealPlaneMelchiorPrinciple.{u})
    (cfg : Configuration α) (hadm : Admissible cfg)
    (hcard : Fintype.card α = 11)
    (hcap : BlockSizeCap (blockSystem cfg) 5)
    (hlocal : ∀ p : α, ElevenFiveLocalRows (blockSystem cfg) p) :
    ElevenFiveGlobalRows (blockSystem cfg) := by
  classical
  let S := blockSystem cfg
  have hb6 := elevenFive_blockCount_eq_zero_of_cap S hcap
    (s := 6) (by omega)
  have hb7 := elevenFive_blockCount_eq_zero_of_cap S hcap
    (s := 7) (by omega)
  have hb8 := elevenFive_blockCount_eq_zero_of_cap S hcap
    (s := 8) (by omega)
  have hb9 := elevenFive_blockCount_eq_zero_of_cap S hcap
    (s := 9) (by omega)
  have hb10 := elevenFive_blockCount_eq_zero_of_cap S hcap
    (s := 10) (by omega)
  have hb11 := elevenFive_blockCount_eq_zero_of_cap S hcap
    (s := 11) (by omega)
  have hc0 : S.circleCount 0 = 0 :=
    S.circleCount_eq_zero_of_lt_three (by omega)
  have hc1 : S.circleCount 1 = 0 :=
    S.circleCount_eq_zero_of_lt_three (by omega)
  have hc2 : S.circleCount 2 = 0 :=
    S.circleCount_eq_zero_of_lt_three (by omega)
  have hc6 := elevenFive_circleCount_eq_zero_of_blockCount_eq_zero S 6 hb6
  have hc7 := elevenFive_circleCount_eq_zero_of_blockCount_eq_zero S 7 hb7
  have hc8 := elevenFive_circleCount_eq_zero_of_blockCount_eq_zero S 8 hb8
  have hc9 := elevenFive_circleCount_eq_zero_of_blockCount_eq_zero S 9 hb9
  have hc10 := elevenFive_circleCount_eq_zero_of_blockCount_eq_zero S 10 hb10
  have hc11 := elevenFive_circleCount_eq_zero_of_blockCount_eq_zero S 11 hb11
  have htripleRaw := S.triple_partition_by_size
  rw [hcard] at htripleRaw
  norm_num [Finset.sum_range_succ, Nat.choose,
    hb6, hb7, hb8, hb9, hb10, hb11] at htripleRaw
  have htriple :
      S.blockCount 3 + 4 * S.blockCount 4 +
        10 * S.blockCount 5 = 165 := by
    omega
  have hcircleRaw := S.totalCircleCount_eq_sum_circleCount
  rw [hcard] at hcircleRaw
  norm_num [Finset.sum_range_succ,
    hc0, hc1, hc2, hc6, hc7, hc8, hc9, hc10, hc11] at hcircleRaw
  have hcircle :
      S.totalCircleCount =
        S.circleCount 3 + S.circleCount 4 + S.circleCount 5 := by
    omega
  have hsplit3 := S.blockCount_eq_lineCount_add_circleCount 3
  have hsplit4 := S.blockCount_eq_lineCount_add_circleCount 4
  have hsplit5 := S.blockCount_eq_lineCount_add_circleCount 5
  have hblockTotal :
      S.blockCount 3 + S.blockCount 4 + S.blockCount 5 =
        S.totalCircleCount + elevenFiveLineTotal S := by
    unfold elevenFiveLineTotal
    omega
  have hinc3 := S.block_incidence 3
  have hcinc3 := S.circle_incidence 3
  have hinc5 := S.block_incidence 5
  have hsigmaPoint :
      (∑ p : α,
        (elevenFiveSigmaAt S p + 3 + S.blockDegree 5 p)) =
          ∑ p : α, S.blockDegree 3 p := by
    apply Finset.sum_congr rfl
    intro p _hp
    exact (hlocal p).sigmaRow
  have hsigma :
      elevenFiveSigmaTotal S + 33 + 5 * S.blockCount 5 =
        3 * S.blockCount 3 := by
    simp only [Finset.sum_add_distrib] at hsigmaPoint
    rw [hinc5, hinc3] at hsigmaPoint
    simp [hcard] at hsigmaPoint
    simpa only [elevenFiveSigmaTotal] using hsigmaPoint
  have hkappaPoint :
      (∑ p : α,
        (elevenFiveKappaAt S p + 3 * S.lineDegree 3 p +
          4 * S.lineDegree 4 p + 5 * S.lineDegree 5 p)) =
        ∑ p : α, (10 + elevenFiveSigmaAt S p) := by
    apply Finset.sum_congr rfl
    intro p _hp
    exact (hlocal p).kappaRow
  have hlinc3 := S.line_incidence 3
  have hlinc4 := S.line_incidence 4
  have hlinc5 := S.line_incidence 5
  have hthreeLineSum :
      (∑ p : α, 3 * S.lineDegree 3 p) = 9 * S.lineCount 3 := by
    rw [← Finset.mul_sum, hlinc3]
    omega
  have hfourLineSum :
      (∑ p : α, 4 * S.lineDegree 4 p) = 16 * S.lineCount 4 := by
    rw [← Finset.mul_sum, hlinc4]
    omega
  have hfiveLineSum :
      (∑ p : α, 5 * S.lineDegree 5 p) = 25 * S.lineCount 5 := by
    rw [← Finset.mul_sum, hlinc5]
    omega
  have hkappa :
      elevenFiveKappaTotal S + 9 * S.lineCount 3 +
          16 * S.lineCount 4 + 25 * S.lineCount 5 =
        110 + elevenFiveSigmaTotal S := by
    simp only [Finset.sum_add_distrib] at hkappaPoint
    rw [hthreeLineSum, hfourLineSum, hfiveLineSum] at hkappaPoint
    simp [hcard] at hkappaPoint
    simpa only [elevenFiveKappaTotal, elevenFiveSigmaTotal] using hkappaPoint
  have hglobal :=
    globalLineRow_le_choose_two_sub_three_of_realPlaneMelchior Mel cfg hadm
  change S.globalLineRow <=
    (Nat.choose (Fintype.card α) 2 : Int) - 3 at hglobal
  rw [elevenFive_globalLineRow_eq S hcard hcap, hcard] at hglobal
  norm_num [Nat.choose] at hglobal
  have hglobalNat :
      3 * S.lineCount 3 + 7 * S.lineCount 4 +
        12 * S.lineCount 5 <= 52 := by
    exact_mod_cast hglobal
  have hmel :
      3 * elevenFiveLineTotal S + 4 * S.lineCount 4 +
        9 * S.lineCount 5 <= 52 := by
    unfold elevenFiveLineTotal
    omega
  have hmomentRaw := S.second_moment_le_two_choose (S.blocksOfSize 5)
  have hmoment :
      elevenFiveSecondMoment S <= 2 * Nat.choose (S.blockCount 5) 2 := by
    simpa [elevenFiveSecondMoment, BlockSystem.blockDegree,
      BlockSystem.blockCount] using hmomentRaw
  exact ⟨htriple, hblockTotal, hcircle, hsigma, hkappa, hmel,
    hinc3, hcinc3, hinc5, hmoment⟩

/-- Scalar consequences which are common to all five boundary layers. -/
structure ElevenFiveScalarBounds
    {Point Block : Type*} [Fintype Point] [Fintype Block]
    [DecidableEq Point] (S : BlockSystem Point Block) : Prop where
  fiveBlockCap : S.blockCount 5 <= 8
  threeIncidenceLower : 66 <= 3 * S.blockCount 3
  threeFiveSlope : 15 * S.blockCount 5 <= 3 * S.blockCount 3 + 33
  restoredOrdinaryLower :
    6 * S.lineCount 3 + 12 * S.lineCount 4 +
      20 * S.lineCount 5 <= 55 + 3 * S.circleCount 3
  deletionSum :
    3 * S.circleCount 3 + 363 <= 11 * S.totalCircleCount

private theorem elevenFive_threeDegree_values
    {Point Block : Type*} [Fintype Point] [Fintype Block]
    [DecidableEq Point]
    (S : BlockSystem Point Block) (p : Point)
    (hlocal : ElevenFiveLocalRows S p)
    (hC : S.totalCircleCount <= 40) :
    S.blockDegree 3 p = 6 ∨ S.blockDegree 3 p = 9 ∨
      S.blockDegree 3 p = 12 := by
  have hpair := hlocal.pairRow
  have harms := hlocal.lineArmRow
  have hsplit := hlocal.threeSplit
  have hkelly := hlocal.kelly
  have hdelete := hlocal.deletion
  have hl3 : S.lineDegree 3 p <= 5 := by
    omega
  have hc3 : S.circleDegree 3 p <= 7 := by
    omega
  omega

private theorem elevenFive_six_le_threeDegree
    {Point Block : Type*} [Fintype Point] [Fintype Block]
    [DecidableEq Point]
    (S : BlockSystem Point Block) (p : Point)
    (hlocal : ElevenFiveLocalRows S p)
    (hC : S.totalCircleCount <= 40) :
    6 <= S.blockDegree 3 p := by
  rcases elevenFive_threeDegree_values S p hlocal hC with h | h | h <;>
    omega

private theorem elevenFive_three_five_slope
    {Point Block : Type*} [Fintype Point] [Fintype Block]
    [DecidableEq Point]
    (S : BlockSystem Point Block) (p : Point)
    (hlocal : ElevenFiveLocalRows S p)
    (hC : S.totalCircleCount <= 40) :
    3 * S.blockDegree 5 p <= S.blockDegree 3 p + 3 := by
  have hfive := hlocal.fiveDegreeCap
  have hlanger := hlocal.langer
  rcases elevenFive_threeDegree_values S p hlocal hC with h | h | h <;>
    omega

theorem elevenFiveScalarBounds_of_rows
    {Point Block : Type*} [Fintype Point] [Fintype Block]
    [DecidableEq Point]
    (S : BlockSystem Point Block) (hcard : Fintype.card Point = 11)
    (hC : S.totalCircleCount <= 40)
    (hlocal : ∀ p : Point, ElevenFiveLocalRows S p)
    (hglobal : ElevenFiveGlobalRows S)
    (hrestored : 55 <= 2 * S.lineCount 2 + 3 * S.circleCount 3) :
    ElevenFiveScalarBounds S := by
  classical
  have hd5sum :
      (∑ p : Point, S.blockDegree 5 p) <= ∑ _p : Point, 4 :=
    Finset.sum_le_sum fun p _hp => (hlocal p).fiveDegreeCap
  rw [hglobal.fiveIncidence] at hd5sum
  simp [hcard] at hd5sum
  have hthreeSum :
      (∑ _p : Point, 6) <= ∑ p : Point, S.blockDegree 3 p :=
    Finset.sum_le_sum fun p _hp =>
      elevenFive_six_le_threeDegree S p (hlocal p) hC
  rw [hglobal.threeIncidence] at hthreeSum
  simp [hcard] at hthreeSum
  have hslopeSum :
      (∑ p : Point, 3 * S.blockDegree 5 p) <=
        ∑ p : Point, (S.blockDegree 3 p + 3) :=
    Finset.sum_le_sum fun p _hp =>
      elevenFive_three_five_slope S p (hlocal p) hC
  have hleft :
      (∑ p : Point, 3 * S.blockDegree 5 p) =
        15 * S.blockCount 5 := by
    rw [← Finset.mul_sum, hglobal.fiveIncidence]
    omega
  have hright :
      (∑ p : Point, (S.blockDegree 3 p + 3)) =
        3 * S.blockCount 3 + 33 := by
    rw [Finset.sum_add_distrib, hglobal.threeIncidence]
    simp [hcard]
  rw [hleft, hright] at hslopeSum
  have harmsPoint :
      (∑ p : Point,
        (S.lineDegree 2 p + 2 * S.lineDegree 3 p +
          3 * S.lineDegree 4 p + 4 * S.lineDegree 5 p)) =
        ∑ _p : Point, 10 := by
    apply Finset.sum_congr rfl
    intro p _hp
    exact (hlocal p).lineArmRow
  simp only [Finset.sum_add_distrib] at harmsPoint
  have hsum3 : (∑ p : Point, 2 * S.lineDegree 3 p) =
      2 * ∑ p : Point, S.lineDegree 3 p := by
    rw [Finset.mul_sum]
  have hsum4 : (∑ p : Point, 3 * S.lineDegree 4 p) =
      3 * ∑ p : Point, S.lineDegree 4 p := by
    rw [Finset.mul_sum]
  have hsum5 : (∑ p : Point, 4 * S.lineDegree 5 p) =
      4 * ∑ p : Point, S.lineDegree 5 p := by
    rw [Finset.mul_sum]
  rw [S.line_incidence 2, hsum3, hsum4, hsum5,
    S.line_incidence 3, S.line_incidence 4,
    S.line_incidence 5] at harmsPoint
  simp [hcard] at harmsPoint
  have hrestoredLine :
      6 * S.lineCount 3 + 12 * S.lineCount 4 +
        20 * S.lineCount 5 <= 55 + 3 * S.circleCount 3 := by
    omega
  have hdelSum :
      (∑ p : Point, (S.circleDegree 3 p + 33)) <=
        ∑ _p : Point, S.totalCircleCount :=
    Finset.sum_le_sum fun p _hp => (hlocal p).deletion
  rw [Finset.sum_add_distrib, hglobal.circleThreeIncidence] at hdelSum
  simp [hcard] at hdelSum
  exact ⟨by omega, by omega, hslopeSum, hrestoredLine, by omega⟩

private theorem elevenFive_lineDegree_eq_zero_of_lineCount_zero
    {Point Block : Type*} [Fintype Point] [Fintype Block]
    [DecidableEq Point]
    (S : BlockSystem Point Block) (s : Nat) (p : Point)
    (hzero : S.lineCount s = 0) : S.lineDegree s p = 0 :=
  elevenFive_lineDegree_eq_zero_of_lineCount_eq_zero S s p hzero

/-- Pointwise convex cost used in the `C=38`, `B5=5,6` moment faces. -/
private theorem elevenFive_moment_cost
    {Point Block : Type*} [Fintype Point] [Fintype Block]
    [DecidableEq Point]
    (S : BlockSystem Point Block) (p : Point)
    (hlocal : ElevenFiveLocalRows S p)
    (hl4 : S.lineDegree 4 p = 0)
    (hl5 : S.lineDegree 5 p = 0) :
    2 * S.blockDegree 5 p <=
      Nat.choose (S.blockDegree 5 p) 2 + elevenFiveKappaAt S p + 2 := by
  have hpair := hlocal.pairRow
  have hsigma := hlocal.sigmaRow
  have harms := hlocal.lineArmRow
  have hkappa := hlocal.kappaRow
  have hz := hlocal.fiveDegreeCap
  interval_cases S.blockDegree 5 p <;>
    norm_num [Nat.choose] at * <;> omega

/-- The same pointwise moment estimate with the exact correction contributed
by a possible four-line through the pivot. -/
private theorem elevenFive_moment_cost_with_four
    {Point Block : Type*} [Fintype Point] [Fintype Block]
    [DecidableEq Point]
    (S : BlockSystem Point Block) (p : Point)
    (hlocal : ElevenFiveLocalRows S p)
    (hl5 : S.lineDegree 5 p = 0) :
    2 * S.blockDegree 5 p <=
      Nat.choose (S.blockDegree 5 p) 2 + elevenFiveKappaAt S p + 2 +
        S.lineDegree 4 p := by
  have hpair := hlocal.pairRow
  have hsigma := hlocal.sigmaRow
  have harms := hlocal.lineArmRow
  have hkappa := hlocal.kappaRow
  have hz := hlocal.fiveDegreeCap
  interval_cases S.blockDegree 5 p <;>
    norm_num [Nat.choose] at * <;> omega

/-- Pointwise harmonic-cost inequality.  The correction `2*l4` is exactly
what is needed for the possible unique four-line in the `C=38,B5=8` row. -/
private theorem elevenFive_harmonic_cost
    {Point Block : Type*} [Fintype Point] [Fintype Block]
    [DecidableEq Point]
    (S : BlockSystem Point Block) (p : Point)
    (hlocal : ElevenFiveLocalRows S p)
    (hthree : S.blockDegree 3 p = 6 ∨ S.blockDegree 3 p = 9)
    (hl5 : S.lineDegree 5 p = 0) :
    S.blockDegree 5 p <=
      3 * (if p ∈ elevenFiveHarmonicPivots S then 1 else 0) + 1 +
    2 * elevenFiveKappaAt S p + 2 * S.lineDegree 4 p := by
  classical
  have hpair := hlocal.pairRow
  have hsigma := hlocal.sigmaRow
  have harms := hlocal.lineArmRow
  have hkappa := hlocal.kappaRow
  have hz := hlocal.fiveDegreeCap
  by_cases hp : p ∈ elevenFiveHarmonicPivots S
  · simp only [hp, if_true]
    omega
  · simp only [hp, if_false]
    simp only [elevenFiveHarmonicPivots, Finset.mem_filter,
      Finset.mem_univ, true_and] at hp
    rcases hthree with hthree | hthree <;>
      interval_cases S.blockDegree 5 p <;>
      norm_num [Nat.choose] at * <;> omega

private theorem elevenFive_moment_sum_bound
    {Point Block : Type*} [Fintype Point] [Fintype Block]
    [DecidableEq Point]
    (S : BlockSystem Point Block) (hcard : Fintype.card Point = 11)
    (hlocal : ∀ p : Point, ElevenFiveLocalRows S p)
    (hglobal : ElevenFiveGlobalRows S)
    (hl4 : S.lineCount 4 = 0) (hl5 : S.lineCount 5 = 0) :
    10 * S.blockCount 5 <=
      elevenFiveSecondMoment S + elevenFiveKappaTotal S + 22 := by
  classical
  have hpoint (p : Point) := elevenFive_moment_cost S p (hlocal p)
    (elevenFive_lineDegree_eq_zero_of_lineCount_zero S 4 p hl4)
    (elevenFive_lineDegree_eq_zero_of_lineCount_zero S 5 p hl5)
  have hsum :
      (∑ p : Point, 2 * S.blockDegree 5 p) <=
        ∑ p : Point,
          (Nat.choose (S.blockDegree 5 p) 2 + elevenFiveKappaAt S p + 2) :=
    Finset.sum_le_sum fun p _hp => hpoint p
  have hleft :
      (∑ p : Point, 2 * S.blockDegree 5 p) =
        10 * S.blockCount 5 := by
    rw [← Finset.mul_sum, hglobal.fiveIncidence]
    omega
  have hright :
      (∑ p : Point,
          (Nat.choose (S.blockDegree 5 p) 2 + elevenFiveKappaAt S p + 2)) =
        elevenFiveSecondMoment S + elevenFiveKappaTotal S + 22 := by
    simp only [Finset.sum_add_distrib]
    simp [elevenFiveSecondMoment, elevenFiveKappaTotal, hcard]
  rwa [hleft, hright] at hsum

/-- Summed moment estimate retaining the exact contribution of all
four-lines. -/
private theorem elevenFive_moment_sum_bound_with_four
    {Point Block : Type*} [Fintype Point] [Fintype Block]
    [DecidableEq Point]
    (S : BlockSystem Point Block) (hcard : Fintype.card Point = 11)
    (hlocal : ∀ p : Point, ElevenFiveLocalRows S p)
    (hglobal : ElevenFiveGlobalRows S)
    (hl5 : S.lineCount 5 = 0) :
    10 * S.blockCount 5 <=
      elevenFiveSecondMoment S + elevenFiveKappaTotal S + 22 +
        4 * S.lineCount 4 := by
  classical
  have hpoint (p : Point) := elevenFive_moment_cost_with_four
    S p (hlocal p)
    (elevenFive_lineDegree_eq_zero_of_lineCount_zero S 5 p hl5)
  have hsum :
      (∑ p : Point, 2 * S.blockDegree 5 p) <=
        ∑ p : Point,
          (Nat.choose (S.blockDegree 5 p) 2 + elevenFiveKappaAt S p + 2 +
            S.lineDegree 4 p) :=
    Finset.sum_le_sum fun p _hp => hpoint p
  have hleft :
      (∑ p : Point, 2 * S.blockDegree 5 p) =
        10 * S.blockCount 5 := by
    rw [← Finset.mul_sum, hglobal.fiveIncidence]
    omega
  have hright :
      (∑ p : Point,
          (Nat.choose (S.blockDegree 5 p) 2 + elevenFiveKappaAt S p + 2 +
            S.lineDegree 4 p)) =
        elevenFiveSecondMoment S + elevenFiveKappaTotal S + 22 +
          4 * S.lineCount 4 := by
    simp only [Finset.sum_add_distrib]
    rw [S.line_incidence]
    simp [elevenFiveSecondMoment, elevenFiveKappaTotal, hcard]
  rwa [hleft, hright] at hsum

private theorem elevenFive_harmonic_sum_bound
    {Point Block : Type*} [Fintype Point] [Fintype Block]
    [DecidableEq Point]
    (S : BlockSystem Point Block) (hcard : Fintype.card Point = 11)
    (hlocal : ∀ p : Point, ElevenFiveLocalRows S p)
    (hglobal : ElevenFiveGlobalRows S)
    (hthree : ∀ p : Point,
      S.blockDegree 3 p = 6 ∨ S.blockDegree 3 p = 9)
    (hl5 : S.lineCount 5 = 0) :
    5 * S.blockCount 5 <=
      3 * (elevenFiveHarmonicPivots S).card + 11 +
        2 * elevenFiveKappaTotal S + 8 * S.lineCount 4 := by
  classical
  have hpoint (p : Point) := elevenFive_harmonic_cost S p (hlocal p)
    (hthree p)
    (elevenFive_lineDegree_eq_zero_of_lineCount_zero S 5 p hl5)
  have hsum :
      (∑ p : Point, S.blockDegree 5 p) <=
        ∑ p : Point,
          (3 * (if p ∈ elevenFiveHarmonicPivots S then 1 else 0) + 1 +
            2 * elevenFiveKappaAt S p + 2 * S.lineDegree 4 p) :=
    Finset.sum_le_sum fun p _hp => hpoint p
  have hindicator :
      (∑ p : Point,
        (if p ∈ elevenFiveHarmonicPivots S then 1 else 0)) =
          (elevenFiveHarmonicPivots S).card := by
    simp
  have hlinc4 := S.line_incidence 4
  have hright :
      (∑ p : Point,
          (3 * (if p ∈ elevenFiveHarmonicPivots S then 1 else 0) + 1 +
            2 * elevenFiveKappaAt S p + 2 * S.lineDegree 4 p)) =
        3 * (elevenFiveHarmonicPivots S).card + 11 +
          2 * elevenFiveKappaTotal S + 8 * S.lineCount 4 := by
    simp only [Finset.sum_add_distrib]
    have hind3 :
        (∑ p : Point,
          3 * (if p ∈ elevenFiveHarmonicPivots S then 1 else 0)) =
            3 * (elevenFiveHarmonicPivots S).card := by
      rw [← Finset.mul_sum, hindicator]
    have hkappa2 :
        (∑ p : Point, 2 * elevenFiveKappaAt S p) =
          2 * elevenFiveKappaTotal S := by
      rw [← Finset.mul_sum]
      rfl
    have hline2 :
        (∑ p : Point, 2 * S.lineDegree 4 p) =
          8 * S.lineCount 4 := by
      rw [← Finset.mul_sum, hlinc4]
      omega
    rw [hind3, hkappa2, hline2]
    simp [hcard]
  rw [hglobal.fiveIncidence, hright] at hsum
  exact hsum

private theorem elevenFive_c36_impossible
    {Point Block : Type*} [Fintype Point] [Fintype Block]
    [DecidableEq Point]
    (S : BlockSystem Point Block)
    (hglobal : ElevenFiveGlobalRows S)
    (hscalar : ElevenFiveScalarBounds S)
    (hC : S.totalCircleCount = 36) : False := by
  have ht := hglobal.tripleRow
  have hb := hglobal.blockTotal
  have hcircle := hglobal.circleTotal
  have hs := hglobal.sigmaRow
  have hk := hglobal.kappaRow
  have hm := hglobal.lineMelchior
  have hsplit3 := S.blockCount_eq_lineCount_add_circleCount 3
  have hsplit4 := S.blockCount_eq_lineCount_add_circleCount 4
  have hsplit5 := S.blockCount_eq_lineCount_add_circleCount 5
  have hB5 := hscalar.fiveBlockCap
  have hB3 := hscalar.threeIncidenceLower
  have hslope := hscalar.threeFiveSlope
  have hrest := hscalar.restoredOrdinaryLower
  have hdel := hscalar.deletionSum
  unfold elevenFiveLineTotal at hb hm
  omega

private theorem elevenFive_c37_impossible
    {Point Block : Type*} [Fintype Point] [Fintype Block]
    [DecidableEq Point]
    (S : BlockSystem Point Block)
    (hglobal : ElevenFiveGlobalRows S)
    (hscalar : ElevenFiveScalarBounds S)
    (hC : S.totalCircleCount = 37) : False := by
  have ht := hglobal.tripleRow
  have hb := hglobal.blockTotal
  have hcircle := hglobal.circleTotal
  have hs := hglobal.sigmaRow
  have hk := hglobal.kappaRow
  have hm := hglobal.lineMelchior
  have hsplit3 := S.blockCount_eq_lineCount_add_circleCount 3
  have hsplit4 := S.blockCount_eq_lineCount_add_circleCount 4
  have hsplit5 := S.blockCount_eq_lineCount_add_circleCount 5
  have hB5 := hscalar.fiveBlockCap
  have hB3 := hscalar.threeIncidenceLower
  have hslope := hscalar.threeFiveSlope
  have hrest := hscalar.restoredOrdinaryLower
  have hdel := hscalar.deletionSum
  unfold elevenFiveLineTotal at hb hm
  have hB5Cases :
      S.blockCount 5 = 7 ∨ S.blockCount 5 = 8 := by
    interval_cases S.blockCount 5 <;> omega
  rcases hB5Cases with hB5 | hB5 <;> omega

private theorem elevenFive_c38_front
    {Point Block : Type*} [Fintype Point] [Fintype Block]
    [DecidableEq Point]
    (S : BlockSystem Point Block)
    (hglobal : ElevenFiveGlobalRows S)
    (hscalar : ElevenFiveScalarBounds S)
    (hpositive : 1 <= S.blockCount 5)
    (hC : S.totalCircleCount = 38) :
    elevenFiveLineTotal S = 13 /\
      5 <= S.blockCount 5 /\ S.blockCount 5 <= 8 /\
      S.lineCount 5 = 0 /\ S.lineCount 4 <= 1 /\
      elevenFiveSigmaTotal S = S.blockCount 5 + 6 /\
      elevenFiveKappaTotal S + 7 * S.lineCount 4 + 1 =
        S.blockCount 5 := by
  have ht := hglobal.tripleRow
  have hb := hglobal.blockTotal
  have hcircle := hglobal.circleTotal
  have hs := hglobal.sigmaRow
  have hk := hglobal.kappaRow
  have hm := hglobal.lineMelchior
  have hsplit3 := S.blockCount_eq_lineCount_add_circleCount 3
  have hsplit4 := S.blockCount_eq_lineCount_add_circleCount 4
  have hsplit5 := S.blockCount_eq_lineCount_add_circleCount 5
  have hB5 := hscalar.fiveBlockCap
  have hB3 := hscalar.threeIncidenceLower
  have hslope := hscalar.threeFiveSlope
  have hrest := hscalar.restoredOrdinaryLower
  have hdel := hscalar.deletionSum
  unfold elevenFiveLineTotal at hb hm ⊢
  have hLExact :
      S.lineCount 3 + S.lineCount 4 + S.lineCount 5 = 13 := by
    omega
  have hB3Exact :
      S.blockCount 3 = 2 * S.blockCount 5 + 13 := by
    omega
  have hsigmaExact :
      elevenFiveSigmaTotal S = S.blockCount 5 + 6 := by
    omega
  have hkappaExact :
      elevenFiveKappaTotal S + 7 * S.lineCount 4 +
          16 * S.lineCount 5 + 1 = S.blockCount 5 := by
    omega
  have hB5Cases :
      S.blockCount 5 = 5 ∨ S.blockCount 5 = 6 ∨
        S.blockCount 5 = 7 ∨ S.blockCount 5 = 8 := by
    interval_cases S.blockCount 5 <;> omega
  rcases hB5Cases with hB5 | hB5 | hB5 | hB5 <;> omega

private theorem elevenFive_c39_front
    {Point Block : Type*} [Fintype Point] [Fintype Block]
    [DecidableEq Point]
    (S : BlockSystem Point Block)
    (hglobal : ElevenFiveGlobalRows S)
    (hscalar : ElevenFiveScalarBounds S)
    (hpositive : 1 <= S.blockCount 5)
    (hC : S.totalCircleCount = 39) :
    (elevenFiveLineTotal S = 12) ∨
      (elevenFiveLineTotal S = 15 /\
        (S.blockCount 5 = 7 ∨ S.blockCount 5 = 8) /\
        S.lineCount 4 = 0 /\ S.lineCount 5 = 0 /\
        elevenFiveKappaTotal S + 7 = S.blockCount 5) := by
  have ht := hglobal.tripleRow
  have hb := hglobal.blockTotal
  have hcircle := hglobal.circleTotal
  have hs := hglobal.sigmaRow
  have hk := hglobal.kappaRow
  have hm := hglobal.lineMelchior
  have hsplit3 := S.blockCount_eq_lineCount_add_circleCount 3
  have hsplit4 := S.blockCount_eq_lineCount_add_circleCount 4
  have hsplit5 := S.blockCount_eq_lineCount_add_circleCount 5
  have hB5 := hscalar.fiveBlockCap
  have hB3 := hscalar.threeIncidenceLower
  have hslope := hscalar.threeFiveSlope
  have hrest := hscalar.restoredOrdinaryLower
  have hdel := hscalar.deletionSum
  unfold elevenFiveLineTotal at hb hm ⊢
  have hLLower :
      12 <= S.lineCount 3 + S.lineCount 4 + S.lineCount 5 := by
    omega
  have hLUpper :
      S.lineCount 3 + S.lineCount 4 + S.lineCount 5 <= 17 := by
    omega
  have hLCases :
      S.lineCount 3 + S.lineCount 4 + S.lineCount 5 = 12 ∨
        S.lineCount 3 + S.lineCount 4 + S.lineCount 5 = 15 := by
    interval_cases
      (S.lineCount 3 + S.lineCount 4 + S.lineCount 5) <;> omega
  rcases hLCases with hL12 | hL15
  · exact Or.inl hL12
  · have hB3Exact :
        S.blockCount 3 = 2 * S.blockCount 5 + 17 := by
      omega
    have hsigmaExact :
        elevenFiveSigmaTotal S = S.blockCount 5 + 18 := by
      omega
    have hkappaExact :
        elevenFiveKappaTotal S + 7 * S.lineCount 4 +
            16 * S.lineCount 5 + 7 = S.blockCount 5 := by
      omega
    have hL4zero : S.lineCount 4 = 0 := by
      omega
    have hL5zero : S.lineCount 5 = 0 := by
      omega
    have hB5Cases :
        S.blockCount 5 = 7 ∨ S.blockCount 5 = 8 := by
      omega
    have hkappaFinal :
        elevenFiveKappaTotal S + 7 = S.blockCount 5 := by
      omega
    exact Or.inr
      ⟨hL15, hB5Cases, hL4zero, hL5zero, hkappaFinal⟩

private theorem elevenFive_c40_front
    {Point Block : Type*} [Fintype Point] [Fintype Block]
    [DecidableEq Point]
    (S : BlockSystem Point Block)
    (hglobal : ElevenFiveGlobalRows S)
    (hscalar : ElevenFiveScalarBounds S)
    (hpositive : 1 <= S.blockCount 5)
    (hC : S.totalCircleCount = 40) :
    (elevenFiveLineTotal S = 11 /\
        5 <= S.blockCount 5 /\ S.blockCount 5 <= 8) ∨
      (elevenFiveLineTotal S = 14 /\
        3 <= S.blockCount 5 /\ S.blockCount 5 <= 8) := by
  have ht := hglobal.tripleRow
  have hb := hglobal.blockTotal
  have hcircle := hglobal.circleTotal
  have hs := hglobal.sigmaRow
  have hk := hglobal.kappaRow
  have hm := hglobal.lineMelchior
  have hsplit3 := S.blockCount_eq_lineCount_add_circleCount 3
  have hsplit4 := S.blockCount_eq_lineCount_add_circleCount 4
  have hsplit5 := S.blockCount_eq_lineCount_add_circleCount 5
  have hB5 := hscalar.fiveBlockCap
  have hB3 := hscalar.threeIncidenceLower
  have hslope := hscalar.threeFiveSlope
  have hrest := hscalar.restoredOrdinaryLower
  have hdel := hscalar.deletionSum
  unfold elevenFiveLineTotal at hb hm ⊢
  omega

/-- The K4 added-centre cut is a direct consequence of the exact summed
restored row; it is not an additional geometry parameter. -/
theorem elevenFive_k4_cut
    {Point Block : Type*} [Fintype Point] [Fintype Block]
    [DecidableEq Point]
    (S : BlockSystem Point Block)
    (hglobal : ElevenFiveGlobalRows S)
    (hC : S.totalCircleCount = 40)
    (hL : elevenFiveLineTotal S = 14) :
    7 * S.lineCount 4 + 16 * S.lineCount 5 <= S.blockCount 5 + 2 := by
  have ht := hglobal.tripleRow
  have hb := hglobal.blockTotal
  have hcircle := hglobal.circleTotal
  have hs := hglobal.sigmaRow
  have hk := hglobal.kappaRow
  have hsplit3 := S.blockCount_eq_lineCount_add_circleCount 3
  have hsplit4 := S.blockCount_eq_lineCount_add_circleCount 4
  have hsplit5 := S.blockCount_eq_lineCount_add_circleCount 5
  unfold elevenFiveLineTotal at hb hL
  omega

private theorem elevenFive_c38_impossible
    {Point Block : Type*} [Fintype Point] [Fintype Block]
    [DecidableEq Point]
    (S : BlockSystem Point Block) (hcard : Fintype.card Point = 11)
    (hlocal : ∀ p : Point, ElevenFiveLocalRows S p)
    (hglobal : ElevenFiveGlobalRows S)
    (hscalar : ElevenFiveScalarBounds S)
    (hpositive : 1 <= S.blockCount 5)
    (hharmonic :
      4 * (elevenFiveHarmonicPivots S).card <= 2 * S.blockCount 5)
    (hC : S.totalCircleCount = 38) : False := by
  obtain ⟨hL, hkLower, hkUpper, hL5, hL4, hsigma, hkappa⟩ :=
    elevenFive_c38_front S hglobal hscalar hpositive hC
  have hthree (p : Point) :
      S.blockDegree 3 p = 6 ∨ S.blockDegree 3 p = 9 := by
    have hvals := elevenFive_threeDegree_values S p (hlocal p) (by omega)
    have harms := (hlocal p).lineArmRow
    have hdelete := (hlocal p).deletion
    have hsplit := (hlocal p).threeSplit
    have hl3 : S.lineDegree 3 p <= 5 := by
      omega
    have hc3 : S.circleDegree 3 p <= 5 := by
      omega
    rcases hvals with h | h | h <;> omega
  have hkCases :
      S.blockCount 5 = 5 ∨ S.blockCount 5 = 6 ∨
        S.blockCount 5 = 7 ∨ S.blockCount 5 = 8 := by
    omega
  rcases hkCases with hk | hk | hk | hk
  · have hl4zero : S.lineCount 4 = 0 := by omega
    have hmoment := elevenFive_moment_sum_bound
      S hcard hlocal hglobal hl4zero hL5
    have hcap := hglobal.secondMomentCap
    norm_num [hk, Nat.choose] at hmoment hcap
    omega
  · have hl4zero : S.lineCount 4 = 0 := by omega
    have hmoment := elevenFive_moment_sum_bound
      S hcard hlocal hglobal hl4zero hL5
    have hcap := hglobal.secondMomentCap
    norm_num [hk, Nat.choose] at hmoment hcap
    omega
  · have hhost := elevenFive_harmonic_sum_bound
      S hcard hlocal hglobal hthree hL5
    norm_num [hk] at hhost hharmonic
    omega
  · have hhost := elevenFive_harmonic_sum_bound
      S hcard hlocal hglobal hthree hL5
    norm_num [hk] at hhost hharmonic
    omega

private theorem elevenFive_c40_eleven_eight_harmonic_bound
    {Point Block : Type*} [Fintype Point] [Fintype Block]
    [DecidableEq Point]
    (S : BlockSystem Point Block) (hcard : Fintype.card Point = 11)
    (hlocal : ∀ p : Point, ElevenFiveLocalRows S p)
    (hglobal : ElevenFiveGlobalRows S)
    (hC : S.totalCircleCount = 40)
    (hpivot : ∀ p : Point,
      S.blockDegree 3 p + S.blockDegree 4 p + S.blockDegree 5 p <= 18) :
    5 * S.blockCount 5 <=
      33 + (elevenFiveHarmonicPivots S).card := by
  classical
  have hpoint (p : Point) :
      S.blockDegree 5 p <=
        3 + (if p ∈ elevenFiveHarmonicPivots S then 1 else 0) := by
    have hvals := elevenFive_threeDegree_values S p (hlocal p) (by omega)
    have hpair := (hlocal p).pairRow
    have hlanger := (hlocal p).langer
    have hfive := (hlocal p).fiveDegreeCap
    by_cases hm : p ∈ elevenFiveHarmonicPivots S
    · simp [hm]
      exact hfive
    · simp only [hm, if_false]
      have hnotProfile :
          ¬ (S.blockDegree 3 p = 9 /\ S.blockDegree 4 p = 4 /\
            S.blockDegree 5 p = 4) := by
        simpa only [elevenFiveHarmonicPivots, Finset.mem_filter,
          Finset.mem_univ, true_and] using hm
      rcases hvals with h6 | h9 | h12
      · omega
      · omega
      · have hp := hpivot p
        omega
  have hsum :
      (∑ p : Point, S.blockDegree 5 p) <=
        ∑ p : Point,
          (3 + (if p ∈ elevenFiveHarmonicPivots S then 1 else 0)) :=
    Finset.sum_le_sum fun p _hp => hpoint p
  have hindicator :
      (∑ p : Point,
        (if p ∈ elevenFiveHarmonicPivots S then 1 else 0)) =
          (elevenFiveHarmonicPivots S).card := by
    simp
  rw [hglobal.fiveIncidence, Finset.sum_add_distrib, hindicator] at hsum
  simp [hcard] at hsum
  exact hsum

/-- The small `L = 14` face is arithmetic once Kelly--Moser is available
in direct ordinary-line form on every restored pivot configuration.  The
unique possible four-line is handled by the corrected moment row; when no
four-line is present, the direct ordinary bound and the pair congruence
force `3*l3 <= d3+3` pointwise, contradicting the global census. -/
private theorem elevenFive_c40_fourteen_small_impossible
    {Point Block : Type*} [Fintype Point] [Fintype Block]
    [DecidableEq Point]
    (S : BlockSystem Point Block) (hcard : Fintype.card Point = 11)
    (hlocal : ∀ p : Point, ElevenFiveLocalRows S p)
    (hglobal : ElevenFiveGlobalRows S)
    (hC : S.totalCircleCount = 40)
    (hL : elevenFiveLineTotal S = 14)
    (hcut : 7 * S.lineCount 4 + 16 * S.lineCount 5 <=
      S.blockCount 5 + 2)
    (hsmall : S.blockCount 5 <= 6)
    (hordinary : ∀ p : Point,
      3 * S.lineDegree 3 p + 3 * S.lineDegree 4 p +
          4 * S.lineDegree 5 p + 5 <= S.blockDegree 3 p + 10) :
    False := by
  classical
  have hL5 : S.lineCount 5 = 0 := by omega
  have hL4le : S.lineCount 4 <= 1 := by omega
  by_cases hL4 : S.lineCount 4 = 0
  · have hL3 : S.lineCount 3 = 14 := by
      unfold elevenFiveLineTotal at hL
      omega
    have hpoint (p : Point) :
        3 * S.lineDegree 3 p <= S.blockDegree 3 p + 3 := by
      have hord := hordinary p
      have hpairs := (hlocal p).pairRow
      have hl4 :=
        elevenFive_lineDegree_eq_zero_of_lineCount_zero S 4 p hL4
      have hl5 :=
        elevenFive_lineDegree_eq_zero_of_lineCount_zero S 5 p hL5
      rw [hl4, hl5] at hord
      omega
    have hsum :
        (∑ p : Point, 3 * S.lineDegree 3 p) <=
          ∑ p : Point, (S.blockDegree 3 p + 3) :=
      Finset.sum_le_sum fun p _hp => hpoint p
    simp only [← Finset.mul_sum, Finset.sum_add_distrib] at hsum
    simp [hcard] at hsum
    rw [S.line_incidence, hglobal.threeIncidence, hL3] at hsum
    have ht := hglobal.tripleRow
    have hb := hglobal.blockTotal
    unfold elevenFiveLineTotal at hb hL
    omega
  · have hL4one : S.lineCount 4 = 1 := by omega
    have hL3 : S.lineCount 3 = 13 := by
      unfold elevenFiveLineTotal at hL
      omega
    have hkCases : S.blockCount 5 = 5 ∨ S.blockCount 5 = 6 := by
      omega
    have hmoment := elevenFive_moment_sum_bound_with_four
      S hcard hlocal hglobal hL5
    have hcap := hglobal.secondMomentCap
    have ht := hglobal.tripleRow
    have hb := hglobal.blockTotal
    have hs := hglobal.sigmaRow
    have hkappa := hglobal.kappaRow
    unfold elevenFiveLineTotal at hb hL
    rcases hkCases with hk | hk
    · norm_num [hk, hL3, hL4one, hL5, Nat.choose] at hmoment hcap ht hb hs hkappa
      omega
    · norm_num [hk, hL3, hL4one, hL5, Nat.choose] at hmoment hcap ht hb hs hkappa
      omega

/-- Complete maximum-circle-five kernel, independent of Langer. -/
theorem elevenFive_circleCount_ge_forty_one_of_cap_without_langer
    {α : Type u} [Fintype α] [DecidableEq α]
    (Mel : RealPlaneMelchiorPrinciple.{u})
    (EvenArr : RealPlaneEvenArrangementPrinciple.{u})
    (Cross : RealPlaneRadicalAxisCrossBlockPrinciple.{u})
    (Kelly : RealPlaneKellyMoserPrinciple.{u})
    (U17 : RealPlaneSixCircleU17Principle.{u})
    (TenGeometry : RealPlaneTenFiveGeometry.{u})
    (Geometry : RealPlaneElevenFiveGeometry.{u})
    (cfg : Configuration α) (hadm : Admissible cfg)
    (hcard : Fintype.card α = 11)
    (gamma : DeterminedCircle cfg)
    (hgamma : (circleTrace cfg gamma.1).card = 5)
    (hcap : BlockSizeCap (blockSystem cfg) 5) :
    41 <= Erdos506.V4.circleCount cfg := by
  classical
  by_contra htarget
  let S := blockSystem cfg
  have hbridge : S.totalCircleCount = Erdos506.V4.circleCount cfg := by
    simpa [S] using elevenFive_totalCircleCount_eq_circleCount cfg
  have hCupper : S.totalCircleCount <= 40 := by
    rw [hbridge]
    omega
  have hlocal : ∀ p : α, ElevenFiveLocalRows S p := by
    intro p
    simpa [S] using elevenFiveLocalRows_of_configuration_without_langer
      Mel EvenArr Cross Kelly U17 TenGeometry
        cfg hadm hcard hcap hCupper p
  have hglobal : ElevenFiveGlobalRows S := by
    simpa [S] using elevenFiveGlobalRows_of_configuration
      Mel cfg hadm hcard hcap hlocal
  have hrestored :
      55 <= 2 * S.lineCount 2 + 3 * S.circleCount 3 := by
    simpa [S] using
      Kelly.fifty_five_le_restored_three_incidence_of_card_eleven
        cfg hadm hcard
  have hscalar := elevenFiveScalarBounds_of_rows
    S hcard hCupper hlocal hglobal hrestored
  have hpositive : 1 <= S.blockCount 5 := by
    simpa [S] using
      one_le_blockCount_five_of_selected_five_circle cfg gamma hgamma
  have hharmonic :
      4 * (elevenFiveHarmonicPivots S).card <= 2 * S.blockCount 5 := by
    simpa [S] using Geometry.harmonicIncidenceCap cfg hadm hcard hcap
  have hClower : 36 <= S.totalCircleCount := by
    have hB3 := hscalar.threeIncidenceLower
    have hrest := hscalar.restoredOrdinaryLower
    have hdel := hscalar.deletionSum
    have hdecomp := S.blockCount_eq_lineCount_add_circleCount 3
    omega
  have hCases :
      S.totalCircleCount = 36 ∨ S.totalCircleCount = 37 ∨
        S.totalCircleCount = 38 ∨ S.totalCircleCount = 39 ∨
        S.totalCircleCount = 40 := by
    omega
  rcases hCases with hC | hC | hC | hC | hC
  · exact elevenFive_c36_impossible S hglobal hscalar hC
  · exact elevenFive_c37_impossible S hglobal hscalar hC
  · exact elevenFive_c38_impossible
      S hcard hlocal hglobal hscalar hpositive hharmonic hC
  · have hcount39 : Erdos506.V4.circleCount cfg = 39 := by
      rw [← hbridge]
      exact hC
    rcases elevenFive_c39_front S hglobal hscalar hpositive hC with
      hL12 | ⟨hL15, hk, hL4, hL5, hkappa⟩
    · obtain ⟨delta, hdelta, hover⟩ :=
        Geometry.c39MaximumHostOverload
          cfg hadm hcard hcap hcount39 hL12
      have hhostCap := elevenFiveHostWeight_le_thirty
        S (circleTrace cfg delta.1) hcard hdelta
      have hoverS :
          31 <= elevenFiveHostWeight S (circleTrace cfg delta.1) := by
        simpa [S] using hover
      omega
    · have hthree (p : α) :
          S.blockDegree 3 p = 6 ∨ S.blockDegree 3 p = 9 := by
        have hvals := elevenFive_threeDegree_values S p (hlocal p) (by omega)
        have harms := (hlocal p).lineArmRow
        have hdelete := (hlocal p).deletion
        have hsplit := (hlocal p).threeSplit
        have hl3 : S.lineDegree 3 p <= 5 := by
          omega
        have hc3 : S.circleDegree 3 p <= 6 := by
          omega
        rcases hvals with h | h | h <;> omega
      have hhost := elevenFive_harmonic_sum_bound
        S hcard hlocal hglobal hthree hL5
      rcases hk with hk | hk
      · norm_num [hk] at hhost hharmonic
        omega
      · norm_num [hk] at hhost hharmonic
        omega
  · have hcount40 : Erdos506.V4.circleCount cfg = 40 := by
      rw [← hbridge]
      exact hC
    rcases elevenFive_c40_front S hglobal hscalar hpositive hC with
      ⟨hL11, hkLower, hkUpper⟩ | ⟨hL14, hkLower, hkUpper⟩
    · have hkCases :
          S.blockCount 5 = 5 ∨ S.blockCount 5 = 6 ∨
            S.blockCount 5 = 7 ∨ S.blockCount 5 = 8 := by
        omega
      rcases hkCases with hk | hk | hk | hk
      · have hcollision := Geometry.c40ElevenSmallFaceCollision
          cfg hadm hcard hcap hcount40 hL11 (Or.inl hk)
        exact elevenFive_no_tripleCollision S hcollision
      · have hcollision := Geometry.c40ElevenSmallFaceCollision
          cfg hadm hcard hcap hcount40 hL11 (Or.inr hk)
        exact elevenFive_no_tripleCollision S hcollision
      · have hcollision := Geometry.c40ElevenSevenDefectCollision
          cfg hadm hcard hcap hcount40 hL11 hk
        exact elevenFive_no_tripleCollision S hcollision
      · have hpivot : ∀ p : α,
            S.blockDegree 3 p + S.blockDegree 4 p +
              S.blockDegree 5 p <= 18 := by
          have hB3 : S.blockCount 3 = 29 := by
            have ht := hglobal.tripleRow
            have hb := hglobal.blockTotal
            rw [hk] at ht
            rw [hk, hC, hL11] at hb
            omega
          have hslopeLe (q : α) :
              3 * S.blockDegree 5 q <= S.blockDegree 3 q + 3 :=
            elevenFive_three_five_slope S q (hlocal q) (by omega)
          have hleft :
              (∑ q : α, 3 * S.blockDegree 5 q) =
                15 * S.blockCount 5 := by
            rw [← Finset.mul_sum, hglobal.fiveIncidence]
            omega
          have hright :
              (∑ q : α, (S.blockDegree 3 q + 3)) =
                3 * S.blockCount 3 + 33 := by
            rw [Finset.sum_add_distrib, hglobal.threeIncidence]
            simp [hcard]
          have hsumEq :
              (∑ q : α, 3 * S.blockDegree 5 q) =
                ∑ q : α, (S.blockDegree 3 q + 3) := by
            calc
              _ = 15 * S.blockCount 5 := hleft
              _ = 120 := by omega
              _ = 3 * S.blockCount 3 + 33 := by omega
              _ = _ := hright.symm
          have hslopeEq (q : α) :
              3 * S.blockDegree 5 q = S.blockDegree 3 q + 3 :=
            (Finset.sum_eq_sum_iff_of_le
              (fun x (_hx : x ∈ (Finset.univ : Finset α)) =>
                hslopeLe x)).mp hsumEq q (Finset.mem_univ q)
          intro p
          have hpair := (hlocal p).pairRow
          have hfive := (hlocal p).fiveDegreeCap
          have hslope := hslopeEq p
          rcases elevenFive_threeDegree_values S p (hlocal p) (by omega) with
            h6 | h9 | h12 <;> omega
        have hhost := elevenFive_c40_eleven_eight_harmonic_bound
          S hcard hlocal hglobal hC hpivot
        norm_num [hk] at hhost hharmonic
        omega
    · have hcut := elevenFive_k4_cut S hglobal hC hL14
      by_cases hsmall : S.blockCount 5 <= 6
      · have hord : ∀ p : α,
            3 * S.lineDegree 3 p + 3 * S.lineDegree 4 p +
                4 * S.lineDegree 5 p + 5 <= S.blockDegree 3 p + 10 := by
          intro p
          have hordinary :
              5 <= S.lineDegree 2 p + S.circleDegree 3 p := by
            simpa [S] using
              Kelly.five_le_restored_ordinary_line_count_of_card_eleven
                cfg hadm hcard p
          have harms := (hlocal p).lineArmRow
          have hsplit := (hlocal p).threeSplit
          omega
        exact elevenFive_c40_fourteen_small_impossible
          S hcard hlocal hglobal hC hL14 hcut hsmall hord
      · have hk : S.blockCount 5 = 7 ∨ S.blockCount 5 = 8 := by
          omega
        rcases hk with hk | hk
        · have hcollision :=
            Geometry.c40FourteenSevenExternalTraceCollision
              cfg hadm hcard hcap hcount40 hL14 hk
          exact elevenFive_no_tripleCollision S hcollision
        · have hcollision := Geometry.c40FourteenEightDefectCollision
            cfg hadm hcard hcap hcount40 hL14 hk
          exact elevenFive_no_tripleCollision S hcollision

/-- Compatibility wrapper retaining the historical global parameter list. -/
theorem elevenFive_circleCount_ge_forty_one_of_cap
    {α : Type u} [Fintype α] [DecidableEq α]
    (Mel : RealPlaneMelchiorPrinciple.{u})
    (_Langer : RealPlaneLangerPrinciple.{u})
    (EvenArr : RealPlaneEvenArrangementPrinciple.{u})
    (Cross : RealPlaneRadicalAxisCrossBlockPrinciple.{u})
    (Kelly : RealPlaneKellyMoserPrinciple.{u})
    (U17 : RealPlaneSixCircleU17Principle.{u})
    (TenGeometry : RealPlaneTenFiveGeometry.{u})
    (Geometry : RealPlaneElevenFiveGeometry.{u})
    (cfg : Configuration α) (hadm : Admissible cfg)
    (hcard : Fintype.card α = 11)
    (gamma : DeterminedCircle cfg)
    (hgamma : (circleTrace cfg gamma.1).card = 5)
    (hcap : BlockSizeCap (blockSystem cfg) 5) :
    41 <= Erdos506.V4.circleCount cfg :=
  elevenFive_circleCount_ge_forty_one_of_cap_without_langer
    Mel EvenArr Cross Kelly U17 TenGeometry Geometry
      cfg hadm hcard gamma hgamma hcap

/-- Selected-five-circle theorem independent of Langer.  A genuine six-circle
is sent to the completed `ElevenGammaSix` branch. -/
theorem elevenFive_circleCount_ge_forty_one_of_configuration_without_langer
    {α : Type u} [Fintype α] [DecidableEq α]
    (Mel : RealPlaneMelchiorPrinciple.{u})
    (EvenArr : RealPlaneEvenArrangementPrinciple.{u})
    (Cross : RealPlaneRadicalAxisCrossBlockPrinciple.{u})
    (Kelly : RealPlaneKellyMoserPrinciple.{u})
    (U17 : RealPlaneSixCircleU17Principle.{u})
    (TenGeometry : RealPlaneTenFiveGeometry.{u})
    (Geometry : RealPlaneElevenFiveGeometry.{u})
    (cfg : Configuration α) (hadm : Admissible cfg)
    (hcard : Fintype.card α = 11)
    (gamma : DeterminedCircle cfg)
    (hgamma : (circleTrace cfg gamma.1).card = 5) :
    41 <= Erdos506.V4.circleCount cfg := by
  by_contra htarget
  have hcount : Erdos506.V4.circleCount cfg <= 40 := by omega
  have hcapSix : ∀ c : DeterminedCircle cfg,
      (circleTrace cfg c.1).card <= 6 := by
    intro c
    exact circleTrace_card_le_six_of_eleven_of_circleCount_le
      cfg hadm hcard hcount c
  by_cases hcapFive : ∀ c : DeterminedCircle cfg,
      (circleTrace cfg c.1).card <= 5
  · have hlineFive : ∀ L : DeterminedLine cfg,
        (lineSupport cfg L).card <= 5 :=
      lineSupport_card_le_five_of_eleven_of_circleCount_le
        cfg hadm hcard hcount
    have hblockCap : BlockSizeCap (blockSystem cfg) 5 :=
      blockSizeCap_of_line_circle_caps cfg 5 hlineFive hcapFive
    have hresult := elevenFive_circleCount_ge_forty_one_of_cap_without_langer
      Mel EvenArr Cross Kelly U17 TenGeometry
        Geometry cfg hadm hcard gamma hgamma hblockCap
    exact htarget hresult
  · push Not at hcapFive
    obtain ⟨delta, hdeltaLarge⟩ := hcapFive
    have hdelta : (circleTrace cfg delta.1).card = 6 := by
      have hle := hcapSix delta
      omega
    have hsix :=
      elevenGammaSix_circleCount_ge_forty_one_of_configuration
        Mel EvenArr Kelly cfg hadm hcard delta hdelta
    exact htarget hsix

/-- Compatibility wrapper retaining the historical global parameter list. -/
theorem elevenFive_circleCount_ge_forty_one_of_configuration
    {α : Type u} [Fintype α] [DecidableEq α]
    (Mel : RealPlaneMelchiorPrinciple.{u})
    (_Langer : RealPlaneLangerPrinciple.{u})
    (EvenArr : RealPlaneEvenArrangementPrinciple.{u})
    (Cross : RealPlaneRadicalAxisCrossBlockPrinciple.{u})
    (Kelly : RealPlaneKellyMoserPrinciple.{u})
    (U17 : RealPlaneSixCircleU17Principle.{u})
    (TenGeometry : RealPlaneTenFiveGeometry.{u})
    (Geometry : RealPlaneElevenFiveGeometry.{u})
    (cfg : Configuration α) (hadm : Admissible cfg)
    (hcard : Fintype.card α = 11)
    (gamma : DeterminedCircle cfg)
    (hgamma : (circleTrace cfg gamma.1).card = 5) :
    41 <= Erdos506.V4.circleCount cfg :=
  elevenFive_circleCount_ge_forty_one_of_configuration_without_langer
    Mel EvenArr Cross Kelly U17 TenGeometry Geometry
      cfg hadm hcard gamma hgamma

end Erdos506.V1
