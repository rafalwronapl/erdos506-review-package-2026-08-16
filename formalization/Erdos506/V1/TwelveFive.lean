import Erdos506.Incidence.EvenArrangementPrinciple
import Erdos506.Incidence.OrdinaryPrinciples
import Erdos506.V1.Eight
import Erdos506.V1.TwelveGammaFiveFront
import Erdos506.V1.TwelveGeometry
import Erdos506.V1.UniversalRows

/-!
# The twelve-point selected-five-circle branch

This module materializes the scalar spine and its local `j,u,q` calculus
from a concrete V1 configuration.  The only parameters beyond the existing
Melchior, Kelly--Moser, and even-arrangement interfaces are the explicit
twelve-point Gram, grid, and gallery principles in `TwelveGeometry`.

No hypothesis below states `51 <= C`, negates the complete selected-five
branch, or packages one of the four boundary circle counts as impossible.
-/

namespace Erdos506.V1

open Erdos506.Block
open Erdos506.Block.BlockSystem
open Erdos506.Incidence
open Erdos506.V4
open scoped BigOperators

universe u

private theorem twelveFive_blockCount_eq_zero_of_cap
    {Point Block : Type*} [Fintype Point] [Fintype Block]
    [DecidableEq Point]
    (S : BlockSystem Point Block) {s : Nat}
    (hcap : BlockSizeCap S 6) (hs : 6 < s) : S.blockCount s = 0 := by
  classical
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro b hb
  have hsize := S.mem_blocksOfSize.mp hb
  have hle := hcap b (by omega)
  omega

private theorem twelveFive_circleCount_eq_zero_of_cap
    {Point Block : Type*} [Fintype Point] [Fintype Block]
    [DecidableEq Point]
    (S : BlockSystem Point Block) {s : Nat}
    (hcircle : forall b : Block,
      S.kind b = .circle -> (S.support b).card <= 5)
    (hs : 5 < s) : S.circleCount s = 0 := by
  classical
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro b hb
  have hspec := S.mem_blocksOfKindSize.mp hb
  have hle := hcircle b hspec.1
  omega

private theorem twelveFive_lineCount_eq_zero_of_blockCount_eq_zero
    {Point Block : Type*} [Fintype Point] [Fintype Block]
    [DecidableEq Point]
    (S : BlockSystem Point Block) (s : Nat)
    (hzero : S.blockCount s = 0) : S.lineCount s = 0 := by
  have hsplit := S.blockCount_eq_lineCount_add_circleCount s
  omega

private theorem twelveFive_circleCount_eq_zero_of_blockCount_eq_zero
    {Point Block : Type*} [Fintype Point] [Fintype Block]
    [DecidableEq Point]
    (S : BlockSystem Point Block) (s : Nat)
    (hzero : S.blockCount s = 0) : S.circleCount s = 0 := by
  have hsplit := S.blockCount_eq_lineCount_add_circleCount s
  omega

private theorem twelveFive_blockDegree_eq_zero_of_blockCount_eq_zero
    {Point Block : Type*} [Fintype Point] [Fintype Block]
    [DecidableEq Point]
    (S : BlockSystem Point Block) (s : Nat) (p : Point)
    (hzero : S.blockCount s = 0) : S.blockDegree s p = 0 := by
  have hinc := S.block_incidence s
  rw [hzero] at hinc
  have hle : S.blockDegree s p <= ∑ q : Point, S.blockDegree s q :=
    Finset.single_le_sum
      (fun q _hq => Nat.zero_le (S.blockDegree s q)) (Finset.mem_univ p)
  omega

private theorem twelveFive_lineDegree_eq_zero_of_lineCount_eq_zero
    {Point Block : Type*} [Fintype Point] [Fintype Block]
    [DecidableEq Point]
    (S : BlockSystem Point Block) (s : Nat) (p : Point)
    (hzero : S.lineCount s = 0) : S.lineDegree s p = 0 := by
  have hinc := S.line_incidence s
  rw [hzero] at hinc
  have hle : S.lineDegree s p <= ∑ q : Point, S.lineDegree s q :=
    Finset.single_le_sum
      (fun q _hq => Nat.zero_le (S.lineDegree s q)) (Finset.mem_univ p)
  omega

/-- The rich line/circle pencil caps every nontrivial block by six in the
contradictory twelve-point range. -/
theorem blockSizeCap_six_of_twelve_five_branch
    {alpha : Type u} [Fintype alpha] [DecidableEq alpha]
    (cfg : Configuration alpha) (hadm : Admissible cfg)
    (hcard : Fintype.card alpha = 12)
    (hcount : Erdos506.V4.circleCount cfg <= 50)
    (hcircle : forall c : DeterminedCircle cfg,
      (circleTrace cfg c.1).card <= 5) :
    BlockSizeCap (blockSystem cfg) 6 := by
  intro b _hthree
  cases b with
  | inl L =>
      simpa [blockSystem, geometricBlockSupport] using
        lineSupport_card_le_six_of_twelve_of_circleCount_le
          cfg hadm hcard hcount L
  | inr c =>
      have hc := hcircle c
      change (circleTrace cfg c.1).card <= 6
      omega

/-- The nonnegative natural total of the pointwise pivot slacks. -/
noncomputable def twelveFiveSigmaTotal
    {Point Block : Type*} [Fintype Point] [Fintype Block]
    [DecidableEq Point] (S : BlockSystem Point Block) : Nat :=
  ∑ p : Point, Int.toNat (S.pivotSigma p)

noncomputable def twelveFiveKappaTotal
    {Point Block : Type*} [Fintype Point] [Fintype Block]
    [DecidableEq Point] (S : BlockSystem Point Block) : Nat :=
  ∑ p : Point, Int.toNat (S.restoredKappa p)

theorem twelveFiveSigmaTotal_cast
    {Point Block : Type*} [Fintype Point] [Fintype Block]
    [DecidableEq Point] (S : BlockSystem Point Block)
    (hsigma : forall p : Point, 0 <= S.pivotSigma p) :
    (twelveFiveSigmaTotal S : Int) = ∑ p : Point, S.pivotSigma p := by
  classical
  simp only [twelveFiveSigmaTotal, Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro p _hp
  exact Int.toNat_of_nonneg (hsigma p)

theorem twelveFiveKappaTotal_cast
    {Point Block : Type*} [Fintype Point] [Fintype Block]
    [DecidableEq Point] (S : BlockSystem Point Block)
    (hkappa : forall p : Point, 0 <= S.restoredKappa p) :
    (twelveFiveKappaTotal S : Int) =
      ∑ p : Point, S.restoredKappa p := by
  classical
  simp only [twelveFiveKappaTotal, Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro p _hp
  exact Int.toNat_of_nonneg (hkappa p)

/-- Canonical data for the already checked arithmetic front. -/
noncomputable def twelveGammaFiveFrontDataOfBlockSystem
    {Point Block : Type*} [Fintype Point] [Fintype Block]
    [DecidableEq Point] (S : BlockSystem Point Block) :
    TwelveGammaFiveFrontData where
  C := S.totalCircleCount
  B3 := S.blockCount 3
  B4 := S.blockCount 4
  B5 := S.blockCount 5
  B6 := S.blockCount 6
  K := twelveFiveSigmaTotal S
  L := S.lineCount 3 + S.lineCount 4 + S.lineCount 5 + S.lineCount 6

/-- Exact global rows before conversion to the natural-number front. -/
private theorem twelveFive_global_rows
    {alpha : Type u} [Fintype alpha] [DecidableEq alpha]
    (Mel : RealPlaneMelchiorPrinciple.{u})
    (cfg : Configuration alpha) (hadm : Admissible cfg)
    (hcard : Fintype.card alpha = 12)
    (hcap : BlockSizeCap (blockSystem cfg) 6)
    (hcircle : forall c : DeterminedCircle cfg,
      (circleTrace cfg c.1).card <= 5) :
    let S := blockSystem cfg
    (S.blockCount 3 + 4 * S.blockCount 4 + 10 * S.blockCount 5 +
        20 * S.blockCount 6 = 220) /\
    (3 * (S.blockCount 3 : Int) - 5 * (S.blockCount 5 : Int) -
        12 * (S.blockCount 6 : Int) =
      36 + ∑ p : alpha, S.pivotSigma p) /\
    (12 * (S.blockCount 4 : Int) + 35 * (S.blockCount 5 : Int) +
        72 * (S.blockCount 6 : Int) =
      624 - ∑ p : alpha, S.pivotSigma p) /\
    (S.totalCircleCount =
      S.circleCount 3 + S.circleCount 4 + S.circleCount 5) /\
    (S.blockCount 3 = S.lineCount 3 + S.circleCount 3) /\
    (S.blockCount 4 = S.lineCount 4 + S.circleCount 4) /\
    (S.blockCount 5 = S.lineCount 5 + S.circleCount 5) /\
    (S.blockCount 6 = S.lineCount 6) /\
    (5 * (S.lineCount 3 : Int) + 12 * (S.lineCount 4 : Int) +
        20 * (S.lineCount 5 : Int) + 28 * (S.lineCount 6 : Int) <=
      4 * (S.totalCircleCount : Int) - 124 +
        (S.circleCount 5 : Int)) := by
  classical
  dsimp only
  let S := blockSystem cfg
  have hcircleBlock : forall b,
      S.kind b = .circle -> (S.support b).card <= 5 := by
    intro b hb
    cases b with
    | inl L => cases hb
    | inr c =>
        simpa [S, blockSystem, geometricBlockSystem,
          geometricBlockKind, geometricBlockSupport] using hcircle c
  have hb7 := twelveFive_blockCount_eq_zero_of_cap S hcap
    (s := 7) (by omega)
  have hb8 := twelveFive_blockCount_eq_zero_of_cap S hcap
    (s := 8) (by omega)
  have hb9 := twelveFive_blockCount_eq_zero_of_cap S hcap
    (s := 9) (by omega)
  have hb10 := twelveFive_blockCount_eq_zero_of_cap S hcap
    (s := 10) (by omega)
  have hb11 := twelveFive_blockCount_eq_zero_of_cap S hcap
    (s := 11) (by omega)
  have hb12 := twelveFive_blockCount_eq_zero_of_cap S hcap
    (s := 12) (by omega)
  have hl7 := twelveFive_lineCount_eq_zero_of_blockCount_eq_zero S 7 hb7
  have hl8 := twelveFive_lineCount_eq_zero_of_blockCount_eq_zero S 8 hb8
  have hl9 := twelveFive_lineCount_eq_zero_of_blockCount_eq_zero S 9 hb9
  have hl10 := twelveFive_lineCount_eq_zero_of_blockCount_eq_zero S 10 hb10
  have hl11 := twelveFive_lineCount_eq_zero_of_blockCount_eq_zero S 11 hb11
  have hl12 := twelveFive_lineCount_eq_zero_of_blockCount_eq_zero S 12 hb12
  have hc0 := S.circleCount_eq_zero_of_lt_three (s := 0) (by omega)
  have hc1 := S.circleCount_eq_zero_of_lt_three (s := 1) (by omega)
  have hc2 := S.circleCount_eq_zero_of_lt_three (s := 2) (by omega)
  have hc6 := twelveFive_circleCount_eq_zero_of_cap S hcircleBlock
    (s := 6) (by omega)
  have hc7 := twelveFive_circleCount_eq_zero_of_cap S hcircleBlock
    (s := 7) (by omega)
  have hc8 := twelveFive_circleCount_eq_zero_of_cap S hcircleBlock
    (s := 8) (by omega)
  have hc9 := twelveFive_circleCount_eq_zero_of_cap S hcircleBlock
    (s := 9) (by omega)
  have hc10 := twelveFive_circleCount_eq_zero_of_cap S hcircleBlock
    (s := 10) (by omega)
  have hc11 := twelveFive_circleCount_eq_zero_of_cap S hcircleBlock
    (s := 11) (by omega)
  have hc12 := twelveFive_circleCount_eq_zero_of_cap S hcircleBlock
    (s := 12) (by omega)
  have hT := S.triple_partition_by_size
  rw [hcard] at hT
  norm_num [Finset.sum_range_succ, Nat.choose,
    hb7, hb8, hb9, hb10, hb11, hb12] at hT
  have hsumSigma := S.sum_pivotSigma_eq_pivotRow_sub_three_n
  simp only [BlockSystem.pivotRow, BlockSystem.nontrivialSizes] at hsumSigma
  rw [hcard] at hsumSigma
  have hIcc : Finset.Icc 3 12 = {3, 4, 5, 6, 7, 8, 9, 10, 11, 12} := by
    decide
  rw [hIcc] at hsumSigma
  norm_num [hb7, hb8, hb9, hb10, hb11, hb12] at hsumSigma
  have hSigma :
      3 * (S.blockCount 3 : Int) - 5 * (S.blockCount 5 : Int) -
          12 * (S.blockCount 6 : Int) =
        36 + ∑ p : alpha, S.pivotSigma p := by
    omega
  have hBlock :
      12 * (S.blockCount 4 : Int) + 35 * (S.blockCount 5 : Int) +
          72 * (S.blockCount 6 : Int) =
        624 - ∑ p : alpha, S.pivotSigma p := by
    have hTz :
        (S.blockCount 3 : Int) + 4 * S.blockCount 4 +
          10 * S.blockCount 5 + 20 * S.blockCount 6 = 220 := by
      exact_mod_cast hT
    omega
  have htotal := S.totalCircleCount_eq_sum_circleCount
  rw [hcard] at htotal
  norm_num [Finset.sum_range_succ, hc0, hc1, hc2,
    hc6, hc7, hc8, hc9, hc10, hc11, hc12] at htotal
  have hsplit3 := S.blockCount_eq_lineCount_add_circleCount 3
  have hsplit4 := S.blockCount_eq_lineCount_add_circleCount 4
  have hsplit5 := S.blockCount_eq_lineCount_add_circleCount 5
  have hsplit6 := S.blockCount_eq_lineCount_add_circleCount 6
  rw [hc6, add_zero] at hsplit6
  have hD := rowD_le_n_mul_n_sub_four_of_realPlaneMelchior
    (α := alpha) Mel cfg hadm (by omega)
  change S.defectRow <=
    (Fintype.card alpha : Int) * ((Fintype.card alpha : Int) - 4) at hD
  simp only [BlockSystem.defectRow, BlockSystem.nontrivialSizes] at hD
  rw [hcard, hIcc] at hD
  norm_num [hl7, hl8, hl9, hl10, hl11, hl12,
    hc6, hc7, hc8, hc9, hc10, hc11, hc12] at hD
  have hAupper :
      5 * (S.lineCount 3 : Int) + 12 * (S.lineCount 4 : Int) +
          20 * (S.lineCount 5 : Int) + 28 * (S.lineCount 6 : Int) <=
        4 * (S.totalCircleCount : Int) - 124 +
          (S.circleCount 5 : Int) := by
    have htotalZ :
        (S.totalCircleCount : Int) = S.circleCount 3 +
          S.circleCount 4 + S.circleCount 5 := by exact_mod_cast htotal
    have hTz :
        (S.blockCount 3 : Int) + 4 * S.blockCount 4 +
          10 * S.blockCount 5 + 20 * S.blockCount 6 = 220 := by
      exact_mod_cast hT
    have hs3 : (S.blockCount 3 : Int) =
        S.lineCount 3 + S.circleCount 3 := by exact_mod_cast hsplit3
    have hs4 : (S.blockCount 4 : Int) =
        S.lineCount 4 + S.circleCount 4 := by exact_mod_cast hsplit4
    have hs5 : (S.blockCount 5 : Int) =
        S.lineCount 5 + S.circleCount 5 := by exact_mod_cast hsplit5
    have hs6 : (S.blockCount 6 : Int) = S.lineCount 6 := by
      exact_mod_cast hsplit6
    omega
  refine ⟨hT, hSigma, hBlock, htotal, hsplit3, hsplit4, hsplit5, hsplit6, ?_⟩
  exact hAupper

/-- The concrete configuration produces all four rows of the existing
`TwelveGammaFiveFrontConditions` structure. -/
theorem twelveGammaFiveFrontConditions_of_configuration
    {alpha : Type u} [Fintype alpha] [DecidableEq alpha]
    (Mel : RealPlaneMelchiorPrinciple.{u})
    (Gram : RealPlaneTwelveGramPrinciple.{u})
    (cfg : Configuration alpha) (hadm : Admissible cfg)
    (hcard : Fintype.card alpha = 12)
    (hcount : Erdos506.V4.circleCount cfg <= 50)
    (hcircle : forall c : DeterminedCircle cfg,
      (circleTrace cfg c.1).card <= 5) :
    TwelveGammaFiveFrontConditions
      (twelveGammaFiveFrontDataOfBlockSystem (blockSystem cfg)) := by
  classical
  let S := blockSystem cfg
  have hcap : BlockSizeCap S 6 := by
    simpa [S] using blockSizeCap_six_of_twelve_five_branch
      cfg hadm hcard hcount hcircle
  have hsigma : forall p : alpha, 0 <= S.pivotSigma p := by
    intro p
    simpa [S] using sigma_nonneg_of_realPlaneMelchior
      Mel cfg hadm (by omega) p
  have hK := twelveFiveSigmaTotal_cast S hsigma
  rcases twelveFive_global_rows Mel cfg hadm hcard hcap hcircle with
    ⟨hT, hSigma, _hBlock, htotal, hs3, hs4, hs5, hs6, hAupper⟩
  have hB5cap : S.blockCount 5 <= 12 :=
    Gram.fiveBlockCap cfg hadm hcard hcap
  have hline :
      4 * (S.lineCount 3 + S.lineCount 4 + S.lineCount 5 +
          S.lineCount 6) + 4 * S.totalCircleCount + S.blockCount 5 +
          4 * S.blockCount 6 = 256 + twelveFiveSigmaTotal S := by
    have hTz :
        (S.blockCount 3 : Int) + 4 * S.blockCount 4 +
          10 * S.blockCount 5 + 20 * S.blockCount 6 = 220 := by
      exact_mod_cast hT
    have htotalZ : (S.totalCircleCount : Int) =
        S.circleCount 3 + S.circleCount 4 + S.circleCount 5 := by
      exact_mod_cast htotal
    have hs3z : (S.blockCount 3 : Int) =
        S.lineCount 3 + S.circleCount 3 := by exact_mod_cast hs3
    have hs4z : (S.blockCount 4 : Int) =
        S.lineCount 4 + S.circleCount 4 := by exact_mod_cast hs4
    have hs5z : (S.blockCount 5 : Int) =
        S.lineCount 5 + S.circleCount 5 := by exact_mod_cast hs5
    have hs6z : (S.blockCount 6 : Int) = S.lineCount 6 := by
      exact_mod_cast hs6
    simp only [S] at *
    omega
  have hadded :
      1776 + 5 * twelveFiveSigmaTotal S + 72 * S.blockCount 6 <=
        36 * S.totalCircleCount + 9 * S.blockCount 5 := by
    have hC5 : S.circleCount 5 <= S.blockCount 5 := by
      have := S.blockCount_eq_lineCount_add_circleCount 5
      omega
    have hlineZ :
        4 * ((S.lineCount 3 : Int) + S.lineCount 4 + S.lineCount 5 +
            S.lineCount 6) + 4 * S.totalCircleCount + S.blockCount 5 +
            4 * S.blockCount 6 =
          256 + twelveFiveSigmaTotal S := by
      exact_mod_cast hline
    have hB6z : (S.blockCount 6 : Int) = S.lineCount 6 := by
      exact_mod_cast hs6
    have hC5z : (S.circleCount 5 : Int) <= S.blockCount 5 := by
      exact_mod_cast hC5
    have haddedZ :
        1776 + 5 * (twelveFiveSigmaTotal S : Int) +
            72 * S.blockCount 6 <=
          36 * S.totalCircleCount + 9 * S.blockCount 5 := by
      simp only [S] at *
      omega
    exact_mod_cast haddedZ
  constructor
  · exact hB5cap
  · simpa only [twelveGammaFiveFrontDataOfBlockSystem] using hT
  · simp only [twelveGammaFiveFrontDataOfBlockSystem]
    simp only [S] at *
    omega
  · simpa only [twelveGammaFiveFrontDataOfBlockSystem] using hline
  · simpa only [twelveGammaFiveFrontDataOfBlockSystem] using hadded

/-- The exact pointwise rows used throughout the five-circle endpoint. -/
structure TwelveFiveLocalRows
    {Point Block : Type*} [Fintype Point] [Fintype Block]
    [DecidableEq Point] (S : BlockSystem Point Block) (p : Point) : Prop where
  pairRow :
    S.blockDegree 3 p + 3 * S.blockDegree 4 p +
      6 * S.blockDegree 5 p + 10 * S.blockDegree 6 p = 55
  sigmaRow :
    S.pivotSigma p + 3 + S.blockDegree 5 p +
        2 * S.blockDegree 6 p = S.blockDegree 3 p
  lineArmRow :
    S.lineDegree 2 p + 2 * S.lineDegree 3 p +
      3 * S.lineDegree 4 p + 4 * S.lineDegree 5 p +
      5 * S.lineDegree 6 p = 11
  kappaRow :
    S.restoredKappa p + 3 * S.lineDegree 3 p +
        4 * S.lineDegree 4 p + 5 * S.lineDegree 5 p +
        6 * S.lineDegree 6 p = 11 + S.pivotSigma p
  sigmaNonneg : 0 <= S.pivotSigma p
  kappaNonneg : 0 <= S.restoredKappa p
  kappaNeOne : S.restoredKappa p ≠ 1
  kellyRow : 33 <= 7 * S.blockDegree 3 p
  fiveDegreeCap : S.blockDegree 5 p <= 6

/-- Existing real-plane principles and the explicit local Gram cap
materialize every field of `TwelveFiveLocalRows`. -/
theorem twelveFiveLocalRows_of_configuration
    {alpha : Type u} [Fintype alpha] [DecidableEq alpha]
    (Mel : RealPlaneMelchiorPrinciple.{u})
    (EvenArr : RealPlaneEvenArrangementPrinciple.{u})
    (Kelly : RealPlaneKellyMoserPrinciple.{u})
    (Gram : RealPlaneTwelveGramPrinciple.{u})
    (cfg : Configuration alpha) (hadm : Admissible cfg)
    (hcard : Fintype.card alpha = 12)
    (hcap : BlockSizeCap (blockSystem cfg) 6)
    (p : alpha) :
    TwelveFiveLocalRows (blockSystem cfg) p := by
  classical
  let S := blockSystem cfg
  have hb7 := twelveFive_blockCount_eq_zero_of_cap S hcap
    (s := 7) (by omega)
  have hb8 := twelveFive_blockCount_eq_zero_of_cap S hcap
    (s := 8) (by omega)
  have hb9 := twelveFive_blockCount_eq_zero_of_cap S hcap
    (s := 9) (by omega)
  have hb10 := twelveFive_blockCount_eq_zero_of_cap S hcap
    (s := 10) (by omega)
  have hb11 := twelveFive_blockCount_eq_zero_of_cap S hcap
    (s := 11) (by omega)
  have hb12 := twelveFive_blockCount_eq_zero_of_cap S hcap
    (s := 12) (by omega)
  have hd7 := twelveFive_blockDegree_eq_zero_of_blockCount_eq_zero S 7 p hb7
  have hd8 := twelveFive_blockDegree_eq_zero_of_blockCount_eq_zero S 8 p hb8
  have hd9 := twelveFive_blockDegree_eq_zero_of_blockCount_eq_zero S 9 p hb9
  have hd10 := twelveFive_blockDegree_eq_zero_of_blockCount_eq_zero S 10 p hb10
  have hd11 := twelveFive_blockDegree_eq_zero_of_blockCount_eq_zero S 11 p hb11
  have hd12 := twelveFive_blockDegree_eq_zero_of_blockCount_eq_zero S 12 p hb12
  have hl7 := twelveFive_lineCount_eq_zero_of_blockCount_eq_zero S 7 hb7
  have hl8 := twelveFive_lineCount_eq_zero_of_blockCount_eq_zero S 8 hb8
  have hl9 := twelveFive_lineCount_eq_zero_of_blockCount_eq_zero S 9 hb9
  have hl10 := twelveFive_lineCount_eq_zero_of_blockCount_eq_zero S 10 hb10
  have hl11 := twelveFive_lineCount_eq_zero_of_blockCount_eq_zero S 11 hb11
  have hl12 := twelveFive_lineCount_eq_zero_of_blockCount_eq_zero S 12 hb12
  have hld7 := twelveFive_lineDegree_eq_zero_of_lineCount_eq_zero S 7 p hl7
  have hld8 := twelveFive_lineDegree_eq_zero_of_lineCount_eq_zero S 8 p hl8
  have hld9 := twelveFive_lineDegree_eq_zero_of_lineCount_eq_zero S 9 p hl9
  have hld10 := twelveFive_lineDegree_eq_zero_of_lineCount_eq_zero S 10 p hl10
  have hld11 := twelveFive_lineDegree_eq_zero_of_lineCount_eq_zero S 11 p hl11
  have hld12 := twelveFive_lineDegree_eq_zero_of_lineCount_eq_zero S 12 p hl12
  have hpairs := S.pivot_pair_partition p
  rw [hcard] at hpairs
  norm_num [Finset.sum_range_succ, Nat.choose,
    hd7, hd8, hd9, hd10, hd11, hd12] at hpairs
  have harms := S.line_arms p
  rw [hcard] at harms
  norm_num [Finset.sum_range_succ,
    hld7, hld8, hld9, hld10, hld11, hld12] at harms
  have hIcc : Finset.Icc 3 12 = {3, 4, 5, 6, 7, 8, 9, 10, 11, 12} := by
    decide
  have hsigmaRow :
      S.pivotSigma p + 3 + S.blockDegree 5 p +
          2 * S.blockDegree 6 p = S.blockDegree 3 p := by
    unfold BlockSystem.pivotSigma BlockSystem.nontrivialSizes
    rw [hcard, hIcc]
    norm_num [hd7, hd8, hd9, hd10, hd11, hd12]
    omega
  have hkappaRow :
      S.restoredKappa p + 3 * S.lineDegree 3 p +
          4 * S.lineDegree 4 p + 5 * S.lineDegree 5 p +
          6 * S.lineDegree 6 p = 11 + S.pivotSigma p := by
    unfold BlockSystem.restoredKappa BlockSystem.nontrivialSizes
    rw [hcard, hIcc]
    norm_num [hld7, hld8, hld9, hld10, hld11, hld12]
    omega
  have hsigmaNonneg : 0 <= S.pivotSigma p := by
    simpa [S] using sigma_nonneg_of_realPlaneMelchior
      Mel cfg hadm (by omega) p
  have hkappaNonneg : 0 <= S.restoredKappa p := by
    simpa [S] using kappa_nonneg_of_realPlaneMelchior
      Mel cfg hadm (by omega) p
  have hrestCard : Fintype.card (Option (Erdos506.V3.AwayFrom p)) = 12 := by
    simp [hcard]
  have heven : Even (Fintype.card (Option (Erdos506.V3.AwayFrom p))) := by
    rw [hrestCard]
    norm_num
  have hrestNoncol : Noncollinear (restoredPivotConfiguration cfg p) :=
    restoredPivotConfiguration_noncollinear cfg hadm (by omega) p
  have hkappaNe : S.restoredKappa p ≠ 1 := by
    have hne := EvenArr.slack_ne_one
      (restoredPivotConfiguration cfg p) hrestNoncol heven
    rw [← restoredKappa_eq_lineMelchiorSlack cfg p] at hne
    simpa [S] using hne
  have hKelly := Kelly.pivot_three_block_bound cfg hadm
    (by omega) (by omega) p
  rw [hcard] at hKelly
  norm_num at hKelly
  change 33 <= 7 * S.blockDegree 3 p at hKelly
  have hd5cap := Gram.fiveDegreeCap cfg hadm hcard hcap p
  exact ⟨hpairs, hsigmaRow, harms, hkappaRow, hsigmaNonneg,
    hkappaNonneg, hkappaNe, hKelly, hd5cap⟩

/-- The quotient parameter in `d3 = 7 + 3j`. -/
noncomputable def twelveFiveJ
    {Point Block : Type*} [Fintype Point] [Fintype Block]
    [DecidableEq Point] (S : BlockSystem Point Block) (p : Point) : Nat :=
  (S.blockDegree 3 p - 7) / 3

/-- The unused rich-line-arm parameter in the no-five-line branch. -/
noncomputable def twelveFiveU
    {Point Block : Type*} [Fintype Point] [Fintype Block]
    [DecidableEq Point] (S : BlockSystem Point Block) (p : Point) : Nat :=
  5 - S.lineDegree 3 p - S.lineDegree 4 p

/-- The nonnegative local `q` parameter. -/
noncomputable def twelveFiveQ
    {Point Block : Type*} [Fintype Point] [Fintype Block]
    [DecidableEq Point] (S : BlockSystem Point Block) (p : Point) : Nat :=
  twelveFiveU S p + 2 * twelveFiveJ S p + 2 - S.blockDegree 5 p

/-- Materialization of the pointwise `j,u,q` front when six-blocks and
five-lines are absent. -/
theorem twelveFive_local_juq_rows
    {alpha : Type u} [Fintype alpha] [DecidableEq alpha]
    (Grid : RealPlaneTwelveGridPrinciple.{u})
    (cfg : Configuration alpha) (hadm : Admissible cfg)
    (hcard : Fintype.card alpha = 12)
    (hcap5 : BlockSizeCap (blockSystem cfg) 5)
    (p : alpha)
    (hlocal : TwelveFiveLocalRows (blockSystem cfg) p)
    (hB6 : (blockSystem cfg).blockCount 6 = 0)
    (hL5 : (blockSystem cfg).lineCount 5 = 0) :
    let S := blockSystem cfg
    S.blockDegree 3 p = 7 + 3 * twelveFiveJ S p /\
    twelveFiveU S p + S.lineDegree 3 p + S.lineDegree 4 p = 5 /\
    twelveFiveQ S p + S.blockDegree 5 p =
      twelveFiveU S p + 2 * twelveFiveJ S p + 2 /\
    (twelveFiveJ S p = 0 -> S.blockDegree 5 p <= 4) /\
    (twelveFiveJ S p = 1 -> S.blockDegree 5 p <= 5) /\
    (2 <= twelveFiveJ S p -> S.blockDegree 5 p <= 6) /\
    S.restoredKappa p + S.lineDegree 4 p + S.blockDegree 5 p =
      3 * (twelveFiveU S p + twelveFiveJ S p) /\
    0 <= twelveFiveQ S p := by
  dsimp only
  let S := blockSystem cfg
  have hlocalS : TwelveFiveLocalRows S p := by
    simpa [S] using hlocal
  have hd6 := twelveFive_blockDegree_eq_zero_of_blockCount_eq_zero S 6 p hB6
  have hl6 := twelveFive_lineCount_eq_zero_of_blockCount_eq_zero S 6 hB6
  have hld6 := twelveFive_lineDegree_eq_zero_of_lineCount_eq_zero S 6 p hl6
  have hld5 := twelveFive_lineDegree_eq_zero_of_lineCount_eq_zero S 5 p hL5
  have hd3mod : S.blockDegree 3 p % 3 = 1 := by
    have hpairs := hlocalS.pairRow
    omega
  have hd3lower : 7 <= S.blockDegree 3 p := by
    have hpairs := hlocalS.pairRow
    have hkelly := hlocalS.kellyRow
    omega
  have hd3 : S.blockDegree 3 p = 7 + 3 * twelveFiveJ S p := by
    have hsubmod : (S.blockDegree 3 p - 7) % 3 = 0 := by omega
    have hdiv := Nat.mod_add_div (S.blockDegree 3 p - 7) 3
    unfold twelveFiveJ
    omega
  have huLe : S.lineDegree 3 p + S.lineDegree 4 p <= 5 := by
    have := hlocalS.lineArmRow
    omega
  have hu : twelveFiveU S p + S.lineDegree 3 p +
      S.lineDegree 4 p = 5 := by
    unfold twelveFiveU
    omega
  have hcap0 : twelveFiveJ S p = 0 -> S.blockDegree 5 p <= 4 := by
    intro hj
    have := hlocalS.sigmaRow
    have := hlocalS.sigmaNonneg
    omega
  have hcap1 : twelveFiveJ S p = 1 -> S.blockDegree 5 p <= 5 := by
    intro hj
    apply Grid.jOneFiveDegreeCap cfg hadm hcard hcap5 p
    have hd3ten : S.blockDegree 3 p = 10 := by omega
    simpa [S] using hd3ten
  have hcap2 : 2 <= twelveFiveJ S p -> S.blockDegree 5 p <= 6 := by
    intro _hj
    exact hlocalS.fiveDegreeCap
  have hkappa :
      S.restoredKappa p + S.lineDegree 4 p + S.blockDegree 5 p =
        3 * (twelveFiveU S p + twelveFiveJ S p) := by
    have hsigma := hlocalS.sigmaRow
    have hk := hlocalS.kappaRow
    omega
  have hqLe : S.blockDegree 5 p <=
      twelveFiveU S p + 2 * twelveFiveJ S p + 2 := by
    by_cases hj0 : twelveFiveJ S p = 0
    · have hc := hcap0 hj0
      by_cases hu0 : twelveFiveU S p = 0
      · have := hlocalS.kappaNonneg
        omega
      · by_cases hu1 : twelveFiveU S p = 1
        · have := hlocalS.kappaNonneg
          omega
        · omega
    · by_cases hj1 : twelveFiveJ S p = 1
      · have hc := hcap1 hj1
        by_cases hu0 : twelveFiveU S p = 0
        · have := hlocalS.kappaNonneg
          omega
        · omega
      · have hj2 : 2 <= twelveFiveJ S p := by omega
        have hc := hcap2 hj2
        omega
  have hq : twelveFiveQ S p + S.blockDegree 5 p =
      twelveFiveU S p + 2 * twelveFiveJ S p + 2 := by
    unfold twelveFiveQ
    omega
  exact ⟨hd3, hu, hq, hcap0, hcap1, hcap2, hkappa, Nat.zero_le _⟩

/-- Canonical global sums for the `q` front. -/
noncomputable def twelveGammaFiveQSumDataOfBlockSystem
    {Point Block : Type*} [Fintype Point] [Fintype Block]
    [DecidableEq Point] (S : BlockSystem Point Block) :
    TwelveGammaFiveQSumData where
  C := S.totalCircleCount
  k := S.blockCount 5
  h := S.lineCount 4
  sumJ := ∑ p : Point, twelveFiveJ S p
  sumU := ∑ p : Point, twelveFiveU S p
  sumQ := ∑ p : Point, twelveFiveQ S p

/-- Summing the materialized local rows gives exactly `eq:n12-q-sums`. -/
theorem twelveGammaFiveQSumConditions_of_blockSystem
    {Point Block : Type*} [Fintype Point] [Fintype Block]
    [DecidableEq Point]
    (S : BlockSystem Point Block) (hcard : Fintype.card Point = 12)
    (hfront : TwelveGammaFiveFrontConditions
      (twelveGammaFiveFrontDataOfBlockSystem S))
    (hB6 : S.blockCount 6 = 0)
    (hK : twelveFiveSigmaTotal S = S.blockCount 5)
    (hL5 : S.lineCount 5 = 0)
    (hjuq : forall p : Point,
      S.blockDegree 3 p = 7 + 3 * twelveFiveJ S p /\
      twelveFiveU S p + S.lineDegree 3 p + S.lineDegree 4 p = 5 /\
      twelveFiveQ S p + S.blockDegree 5 p =
        twelveFiveU S p + 2 * twelveFiveJ S p + 2) :
    TwelveGammaFiveQSumConditions
      (twelveGammaFiveQSumDataOfBlockSystem S) := by
  classical
  have hfrontTriple := hfront.tripleRow
  have hfrontBlock := hfront.blockRow
  have hfrontLine := hfront.lineRow
  simp only [twelveGammaFiveFrontDataOfBlockSystem] at hfrontTriple hfrontBlock hfrontLine
  have hB3 : S.blockCount 3 = 12 + 2 * S.blockCount 5 := by omega
  have hB4 : S.blockCount 4 + 3 * S.blockCount 5 = 52 := by omega
  have hL6 := twelveFive_lineCount_eq_zero_of_blockCount_eq_zero S 6 hB6
  have hL : S.lineCount 3 + S.lineCount 4 + S.lineCount 5 +
      S.lineCount 6 + S.totalCircleCount = 64 := by omega
  have hinc3 := S.block_incidence 3
  have hsumJPoint :
      (∑ p : Point, S.blockDegree 3 p) =
        84 + 3 * ∑ p : Point, twelveFiveJ S p := by
    calc
      (∑ p : Point, S.blockDegree 3 p) =
          ∑ p : Point, (7 + 3 * twelveFiveJ S p) := by
        apply Finset.sum_congr rfl
        intro p _hp
        exact (hjuq p).1
      _ = 84 + 3 * ∑ p : Point, twelveFiveJ S p := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum]
        simp [hcard]
  have hsumJ :
      (∑ p : Point, twelveFiveJ S p) + 16 =
        2 * S.blockCount 5 := by
    omega
  have hline3 := S.line_incidence 3
  have hline4 := S.line_incidence 4
  have hsumUPoint :
      (∑ p : Point, twelveFiveU S p) +
          (∑ p : Point, S.lineDegree 3 p) +
          (∑ p : Point, S.lineDegree 4 p) = 60 := by
    calc
      (∑ p : Point, twelveFiveU S p) +
          (∑ p : Point, S.lineDegree 3 p) +
          (∑ p : Point, S.lineDegree 4 p) =
          ∑ p : Point,
            (twelveFiveU S p + S.lineDegree 3 p + S.lineDegree 4 p) := by
        simp only [Finset.sum_add_distrib]
      _ = 60 := by
        calc
          (∑ p : Point,
              (twelveFiveU S p + S.lineDegree 3 p + S.lineDegree 4 p)) =
              ∑ _p : Point, 5 := by
            apply Finset.sum_congr rfl
            intro p _hp
            exact (hjuq p).2.1
          _ = 60 := by simp [hcard]
  have hsumU :
      (∑ p : Point, twelveFiveU S p) + 132 + S.lineCount 4 =
        3 * S.totalCircleCount := by
    omega
  have hinc5 := S.block_incidence 5
  have hsumQPoint :
      (∑ p : Point, twelveFiveQ S p) +
          (∑ p : Point, S.blockDegree 5 p) =
        (∑ p : Point, twelveFiveU S p) +
          2 * (∑ p : Point, twelveFiveJ S p) + 24 := by
    calc
      (∑ p : Point, twelveFiveQ S p) +
          (∑ p : Point, S.blockDegree 5 p) =
          ∑ p : Point, (twelveFiveQ S p + S.blockDegree 5 p) := by
        simp only [Finset.sum_add_distrib]
      _ = ∑ p : Point,
          (twelveFiveU S p + 2 * twelveFiveJ S p + 2) := by
        apply Finset.sum_congr rfl
        intro p _hp
        exact (hjuq p).2.2
      _ = (∑ p : Point, twelveFiveU S p) +
          2 * (∑ p : Point, twelveFiveJ S p) + 24 := by
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
          ← Finset.mul_sum]
        simp [hcard]
  have hsumQ :
      (∑ p : Point, twelveFiveQ S p) + 140 + S.blockCount 5 +
          S.lineCount 4 = 3 * S.totalCircleCount := by
    omega
  exact ⟨hsumJ, hsumU, hsumQ⟩

private theorem twelveFive_blockSizeCap_five_of_six_layer_zero
    {Point Block : Type*} [Fintype Point] [Fintype Block]
    [DecidableEq Point]
    (S : BlockSystem Point Block) (hcap : BlockSizeCap S 6)
    (hB6 : S.blockCount 6 = 0) : BlockSizeCap S 5 := by
  intro b hthree
  have hle := hcap b hthree
  by_contra hnot
  have hcard : (S.support b).card = 6 := by omega
  have hbmem : b ∈ S.blocksOfSize 6 := S.mem_blocksOfSize.mpr hcard
  have hpositive : 0 < S.blockCount 6 := by
    unfold BlockSystem.blockCount
    exact Finset.card_pos.mpr ⟨b, hbmem⟩
  omega

private theorem twelveFive_sigma_eq_zero_of_total_eq_zero
    {Point Block : Type*} [Fintype Point] [Fintype Block]
    [DecidableEq Point]
    (S : BlockSystem Point Block)
    (hsigma : forall p : Point, 0 <= S.pivotSigma p)
    (hK : twelveFiveSigmaTotal S = 0) (p : Point) :
    S.pivotSigma p = 0 := by
  have hle : Int.toNat (S.pivotSigma p) <= twelveFiveSigmaTotal S := by
    unfold twelveFiveSigmaTotal
    exact Finset.single_le_sum
      (fun q _hq => Nat.zero_le (Int.toNat (S.pivotSigma q)))
      (Finset.mem_univ p)
  have hto : Int.toNat (S.pivotSigma p) = 0 := by omega
  have hcast := Int.toNat_of_nonneg (hsigma p)
  omega

private theorem twelveFive_kappa_eq_zero_of_sum_eq_zero
    {Point Block : Type*} [Fintype Point] [Fintype Block]
    [DecidableEq Point]
    (S : BlockSystem Point Block)
    (hkappa : forall p : Point, 0 <= S.restoredKappa p)
    (hsum : (∑ p : Point, S.restoredKappa p) = 0) (p : Point) :
    S.restoredKappa p = 0 := by
  have hle : S.restoredKappa p <= ∑ q : Point, S.restoredKappa q :=
    Finset.single_le_sum (fun q _hq => hkappa q) (Finset.mem_univ p)
  have hpnonneg := hkappa p
  omega

/-- Summed form of the pointwise restored-centre row. -/
theorem twelveFive_sum_kappa_row
    {Point Block : Type*} [Fintype Point] [Fintype Block]
    [DecidableEq Point]
    (S : BlockSystem Point Block) (hcard : Fintype.card Point = 12)
    (hlocal : forall p : Point, TwelveFiveLocalRows S p)
    (hKcast : (twelveFiveSigmaTotal S : Int) =
      ∑ p : Point, S.pivotSigma p) :
    (∑ p : Point, S.restoredKappa p) +
        9 * S.lineCount 3 + 16 * S.lineCount 4 +
        25 * S.lineCount 5 + 36 * S.lineCount 6 =
      132 + twelveFiveSigmaTotal S := by
  have hsumLocal :
      (∑ p : Point, S.restoredKappa p) +
          3 * (∑ p : Point, S.lineDegree 3 p) +
          4 * (∑ p : Point, S.lineDegree 4 p) +
          5 * (∑ p : Point, S.lineDegree 5 p) +
          6 * (∑ p : Point, S.lineDegree 6 p) =
        132 + ∑ p : Point, S.pivotSigma p := by
    calc
      (∑ p : Point, S.restoredKappa p) +
          3 * (∑ p : Point, S.lineDegree 3 p) +
          4 * (∑ p : Point, S.lineDegree 4 p) +
          5 * (∑ p : Point, S.lineDegree 5 p) +
          6 * (∑ p : Point, S.lineDegree 6 p) =
          ∑ p : Point,
            (S.restoredKappa p + 3 * S.lineDegree 3 p +
              4 * S.lineDegree 4 p + 5 * S.lineDegree 5 p +
              6 * S.lineDegree 6 p) := by
        simp only [Finset.sum_add_distrib, Nat.cast_sum, ← Finset.mul_sum]
      _ = ∑ p : Point, (11 + S.pivotSigma p) := by
        apply Finset.sum_congr rfl
        intro p _hp
        exact (hlocal p).kappaRow
      _ = 132 + ∑ p : Point, S.pivotSigma p := by
        rw [Finset.sum_add_distrib]
        simp [hcard]
  have hl3 : ((∑ p : Point, S.lineDegree 3 p : Nat) : Int) =
      3 * (S.lineCount 3 : Int) := by
    exact_mod_cast S.line_incidence 3
  have hl4 : ((∑ p : Point, S.lineDegree 4 p : Nat) : Int) =
      4 * (S.lineCount 4 : Int) := by
    exact_mod_cast S.line_incidence 4
  have hl5 : ((∑ p : Point, S.lineDegree 5 p : Nat) : Int) =
      5 * (S.lineCount 5 : Int) := by
    exact_mod_cast S.line_incidence 5
  have hl6 : ((∑ p : Point, S.lineDegree 6 p : Nat) : Int) =
      6 * (S.lineCount 6 : Int) := by
    exact_mod_cast S.line_incidence 6
  rw [hl3, hl4, hl5, hl6, ← hKcast] at hsumLocal
  ring_nf at hsumLocal ⊢
  exact hsumLocal

private theorem twelveFive_Kzero_B5twelve_impossible
    {Point Block : Type*} [Fintype Point] [Fintype Block]
    [DecidableEq Point]
    (S : BlockSystem Point Block) (hcard : Fintype.card Point = 12)
    (hlocal : forall p : Point, TwelveFiveLocalRows S p)
    (hK : twelveFiveSigmaTotal S = 0)
    (hB5 : S.blockCount 5 = 12) : False := by
  have hsigma (p : Point) : S.pivotSigma p = 0 :=
    twelveFive_sigma_eq_zero_of_total_eq_zero S
      (fun q => (hlocal q).sigmaNonneg) hK p
  have hd5 (p : Point) : S.blockDegree 5 p <= 4 := by
    have hpairs := (hlocal p).pairRow
    have hsrow := (hlocal p).sigmaRow
    have hsone := hsigma p
    have hcap := (hlocal p).fiveDegreeCap
    have hmod : S.blockDegree 5 p % 3 = 1 := by omega
    omega
  have hsumLe : (∑ p : Point, S.blockDegree 5 p) <= 48 := by
    calc
      (∑ p : Point, S.blockDegree 5 p) <= ∑ _p : Point, 4 :=
        Finset.sum_le_sum fun p _hp => hd5 p
      _ = 48 := by simp [hcard]
  have hinc := S.block_incidence 5
  omega

/-- The block row gives the only congruence used by the endpoint routers. -/
private theorem twelveGammaFive_K_mod_twelve
    (B4 B5 B6 K : Nat)
    (hrow : 12 * B4 + 35 * B5 + 72 * B6 + K = 624) :
    K % 12 = B5 % 12 := by
  omega

/-- In the `C = 50`, `B6 = 0` row, the block-row congruence and the
added-centre bound leave just these three values of the total slack. -/
private theorem twelveGammaFive_C50_B6_zero_K_profiles
    (B5 K : Nat)
    (hB5pos : 1 <= B5) (hB5cap : B5 <= 12)
    (hadded : 5 * K <= 24 + 9 * B5)
    (hmod : K % 12 = B5 % 12) :
    K = B5 \/ (K = 0 /\ B5 = 12) \/
      (K = B5 + 12 /\ 9 <= B5) := by
  omega

/-- In the `C = 50`, `B6 = 1` row, the same congruence has only its two
zero-residue representatives left. -/
private theorem twelveGammaFive_C50_B6_one_K_profiles
    (B5 K : Nat)
    (hB5pos : 1 <= B5) (hB5cap : B5 <= 12)
    (hadded : 5 * K + 48 <= 9 * B5)
    (hmod : K % 12 = B5 % 12) :
    (K = 0 /\ B5 = 12) \/ (K = 12 /\ B5 = 12) := by
  omega

private theorem twelveGammaFive_C48_profiles
    (d : TwelveGammaFiveFrontData)
    (h : TwelveGammaFiveFrontConditions d)
    (hC : d.C = 48) (hB5pos : 1 <= d.B5) :
    (d.K = 0 /\ d.B5 = 12 /\ d.B6 = 0 /\ d.L = 13) \/
    (d.K = 12 /\ d.B5 = 12 /\ d.B6 = 0 /\ d.L = 16) := by
  rcases h with ⟨hcap, hT, hB, hL, hA⟩
  have hmod := twelveGammaFive_K_mod_twelve d.B4 d.B5 d.B6 d.K hB
  have hm : d.B6 <= 1 := by omega
  omega

private theorem twelveGammaFive_C49_profiles
    (d : TwelveGammaFiveFrontData)
    (h : TwelveGammaFiveFrontConditions d)
    (hC : d.C = 49) (hB5pos : 1 <= d.B5) :
    (d.K = 0 /\ d.B5 = 12 /\ d.B6 = 1) \/
    (d.K = 0 /\ d.B5 = 12 /\ d.B6 = 0) \/
    (d.B6 = 0 /\ d.K = d.B5 /\ 3 <= d.B5 /\ d.B5 <= 12 /\
      d.L = 15) := by
  rcases h with ⟨hcap, hT, hB, hL, hA⟩
  have hmod := twelveGammaFive_K_mod_twelve d.B4 d.B5 d.B6 d.K hB
  have hm : d.B6 <= 1 := by omega
  omega

private theorem twelveGammaFive_C50_profiles
    (d : TwelveGammaFiveFrontData)
    (h : TwelveGammaFiveFrontConditions d)
    (hC : d.C = 50) (hB5pos : 1 <= d.B5) :
    (d.B6 = 0 /\ d.K = d.B5 /\ 1 <= d.B5 /\ d.B5 <= 12 /\
      d.L = 14) \/
    (d.B6 = 0 /\ d.K = 0 /\ d.B5 = 12 /\ d.L = 11) \/
    (d.B6 = 0 /\ d.K = d.B5 + 12 /\ 9 <= d.B5 /\ d.B5 <= 12 /\
      d.L = 17) \/
    (d.B6 = 1 /\ d.K = 0 /\ d.B5 = 12 /\ d.L = 10) \/
    (d.B6 = 1 /\ d.K = 12 /\ d.B5 = 12 /\ d.L = 13) := by
  rcases h with ⟨hcap, hT, hB, hL, hA⟩
  have hmod := twelveGammaFive_K_mod_twelve d.B4 d.B5 d.B6 d.K hB
  have hm : d.B6 <= 1 := by omega
  by_cases hB6zero : d.B6 = 0
  · have hadded : 5 * d.K <= 24 + 9 * d.B5 := by omega
    rcases twelveGammaFive_C50_B6_zero_K_profiles
        d.B5 d.K hB5pos hcap hadded hmod with
      hmain | hzero | hshift
    · apply Or.inl
      refine ⟨hB6zero, hmain, hB5pos, hcap, ?_⟩
      omega
    · rcases hzero with ⟨hKzero, hB5twelve⟩
      apply Or.inr
      apply Or.inl
      refine ⟨hB6zero, hKzero, hB5twelve, ?_⟩
      omega
    · rcases hshift with ⟨hKshift, hB5nine⟩
      apply Or.inr
      apply Or.inr
      apply Or.inl
      refine ⟨hB6zero, hKshift, hB5nine, hcap, ?_⟩
      omega
  · have hB6one : d.B6 = 1 := by omega
    have hadded : 5 * d.K + 48 <= 9 * d.B5 := by omega
    rcases twelveGammaFive_C50_B6_one_K_profiles
        d.B5 d.K hB5pos hcap hadded hmod with hzero | htwelve
    · rcases hzero with ⟨hKzero, hB5twelve⟩
      apply Or.inr
      apply Or.inr
      apply Or.inr
      apply Or.inl
      refine ⟨hB6one, hKzero, hB5twelve, ?_⟩
      omega
    · rcases htwelve with ⟨hKtwelve, hB5twelve⟩
      apply Or.inr
      apply Or.inr
      apply Or.inr
      apply Or.inr
      refine ⟨hB6one, hKtwelve, hB5twelve, ?_⟩
      omega

private theorem twelveGammaFive_shifted_q_sums
    {Point Block : Type*} [Fintype Point] [Fintype Block]
    [DecidableEq Point]
    (S : BlockSystem Point Block) (hcard : Fintype.card Point = 12)
    (hfront : TwelveGammaFiveFrontConditions
      (twelveGammaFiveFrontDataOfBlockSystem S))
    (hB6 : S.blockCount 6 = 0)
    (hK : twelveFiveSigmaTotal S = S.blockCount 5 + 12)
    (hL : S.lineCount 3 + S.lineCount 4 + S.lineCount 5 +
      S.lineCount 6 = 17)
    (hL4 : S.lineCount 4 = 0) (hL5 : S.lineCount 5 = 0)
    (hjuq : forall p : Point,
      S.blockDegree 3 p = 7 + 3 * twelveFiveJ S p /\
      twelveFiveU S p + S.lineDegree 3 p + S.lineDegree 4 p = 5 /\
      twelveFiveQ S p + S.blockDegree 5 p =
        twelveFiveU S p + 2 * twelveFiveJ S p + 2) :
    (∑ p : Point, twelveFiveJ S p) + 12 = 2 * S.blockCount 5 /\
    (∑ p : Point, twelveFiveU S p) = 9 /\
    (∑ p : Point, twelveFiveQ S p) + S.blockCount 5 = 9 := by
  classical
  have hT := hfront.tripleRow
  have hB := hfront.blockRow
  simp only [twelveGammaFiveFrontDataOfBlockSystem] at hT hB
  have hB3 : S.blockCount 3 = 16 + 2 * S.blockCount 5 := by omega
  have hinc3 := S.block_incidence 3
  have hsumJPoint :
      (∑ p : Point, S.blockDegree 3 p) =
        84 + 3 * ∑ p : Point, twelveFiveJ S p := by
    calc
      (∑ p : Point, S.blockDegree 3 p) =
          ∑ p : Point, (7 + 3 * twelveFiveJ S p) := by
        apply Finset.sum_congr rfl
        intro p _hp
        exact (hjuq p).1
      _ = 84 + 3 * ∑ p : Point, twelveFiveJ S p := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum]
        simp [hcard]
  have hsumJ : (∑ p : Point, twelveFiveJ S p) + 12 =
      2 * S.blockCount 5 := by omega
  have hL6 := twelveFive_lineCount_eq_zero_of_blockCount_eq_zero S 6 hB6
  have hl3 := S.line_incidence 3
  have hl4 := S.line_incidence 4
  have hsumUPoint :
      (∑ p : Point, twelveFiveU S p) +
          (∑ p : Point, S.lineDegree 3 p) +
          (∑ p : Point, S.lineDegree 4 p) = 60 := by
    calc
      (∑ p : Point, twelveFiveU S p) +
          (∑ p : Point, S.lineDegree 3 p) +
          (∑ p : Point, S.lineDegree 4 p) =
          ∑ p : Point,
            (twelveFiveU S p + S.lineDegree 3 p + S.lineDegree 4 p) := by
        simp only [Finset.sum_add_distrib]
      _ = ∑ _p : Point, 5 := by
        apply Finset.sum_congr rfl
        intro p _hp
        exact (hjuq p).2.1
      _ = 60 := by simp [hcard]
  have hsumU : (∑ p : Point, twelveFiveU S p) = 9 := by omega
  have hinc5 := S.block_incidence 5
  have hsumQPoint :
      (∑ p : Point, twelveFiveQ S p) +
          (∑ p : Point, S.blockDegree 5 p) =
        (∑ p : Point, twelveFiveU S p) +
          2 * (∑ p : Point, twelveFiveJ S p) + 24 := by
    calc
      (∑ p : Point, twelveFiveQ S p) +
          (∑ p : Point, S.blockDegree 5 p) =
          ∑ p : Point, (twelveFiveQ S p + S.blockDegree 5 p) := by
        simp only [Finset.sum_add_distrib]
      _ = ∑ p : Point,
          (twelveFiveU S p + 2 * twelveFiveJ S p + 2) := by
        apply Finset.sum_congr rfl
        intro p _hp
        exact (hjuq p).2.2
      _ = (∑ p : Point, twelveFiveU S p) +
          2 * (∑ p : Point, twelveFiveJ S p) + 24 := by
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
          ← Finset.mul_sum]
        simp [hcard]
  have hsumQ : (∑ p : Point, twelveFiveQ S p) +
      S.blockCount 5 = 9 := by omega
  exact ⟨hsumJ, hsumU, hsumQ⟩

/-- The four rows of the manuscript's low-defect local table. -/
private theorem twelveFive_low_defect_table
    {alpha : Type u} [Fintype alpha] [DecidableEq alpha]
    (Grid : RealPlaneTwelveGridPrinciple.{u})
    (cfg : Configuration alpha) (hadm : Admissible cfg)
    (hcard : Fintype.card alpha = 12)
    (hcap5 : BlockSizeCap (blockSystem cfg) 5)
    (hL5 : (blockSystem cfg).lineCount 5 = 0)
    (p : alpha)
    (hlocal : TwelveFiveLocalRows (blockSystem cfg) p)
    (hjuq :
      (blockSystem cfg).blockDegree 3 p =
          7 + 3 * twelveFiveJ (blockSystem cfg) p /\
      twelveFiveU (blockSystem cfg) p +
          (blockSystem cfg).lineDegree 3 p +
          (blockSystem cfg).lineDegree 4 p = 5 /\
      twelveFiveQ (blockSystem cfg) p +
          (blockSystem cfg).blockDegree 5 p =
        twelveFiveU (blockSystem cfg) p +
          2 * twelveFiveJ (blockSystem cfg) p + 2 /\
      (twelveFiveJ (blockSystem cfg) p = 0 ->
        (blockSystem cfg).blockDegree 5 p <= 4) /\
      (twelveFiveJ (blockSystem cfg) p = 1 ->
        (blockSystem cfg).blockDegree 5 p <= 5) /\
      (2 <= twelveFiveJ (blockSystem cfg) p ->
        (blockSystem cfg).blockDegree 5 p <= 6) /\
      (blockSystem cfg).restoredKappa p +
          (blockSystem cfg).lineDegree 4 p +
          (blockSystem cfg).blockDegree 5 p =
        3 * (twelveFiveU (blockSystem cfg) p +
          twelveFiveJ (blockSystem cfg) p)) :
    let S := blockSystem cfg
    (S.lineDegree 4 p = 0 -> twelveFiveQ S p = 0 ->
      twelveFiveJ S p = 0) /\
    (S.lineDegree 4 p = 0 -> twelveFiveQ S p = 1 ->
      twelveFiveJ S p <= 1) /\
    (twelveFiveQ S p = 0 -> S.lineDegree 4 p = 1 ->
      twelveFiveJ S p = 1 /\ twelveFiveU S p = 1 /\
        S.blockDegree 5 p = 5 /\ S.restoredKappa p = 0) /\
    (twelveFiveQ S p = 0 -> S.lineDegree 4 p = 2 ->
      twelveFiveJ S p = 0 /\ twelveFiveU S p = 2 /\
        S.blockDegree 5 p = 4 /\ S.restoredKappa p = 0) := by
  dsimp only
  let S := blockSystem cfg
  change
    (S.lineDegree 4 p = 0 -> twelveFiveQ S p = 0 ->
      twelveFiveJ S p = 0) /\
    (S.lineDegree 4 p = 0 -> twelveFiveQ S p = 1 ->
      twelveFiveJ S p <= 1) /\
    (twelveFiveQ S p = 0 -> S.lineDegree 4 p = 1 ->
      twelveFiveJ S p = 1 /\ twelveFiveU S p = 1 /\
        S.blockDegree 5 p = 5 /\ S.restoredKappa p = 0) /\
    (twelveFiveQ S p = 0 -> S.lineDegree 4 p = 2 ->
      twelveFiveJ S p = 0 /\ twelveFiveU S p = 2 /\
        S.blockDegree 5 p = 4 /\ S.restoredKappa p = 0)
  have hlocalS : TwelveFiveLocalRows S p := by
    simpa [S] using hlocal
  have hjuqS :
      S.blockDegree 3 p = 7 + 3 * twelveFiveJ S p /\
      twelveFiveU S p + S.lineDegree 3 p + S.lineDegree 4 p = 5 /\
      twelveFiveQ S p + S.blockDegree 5 p =
        twelveFiveU S p + 2 * twelveFiveJ S p + 2 /\
      (twelveFiveJ S p = 0 -> S.blockDegree 5 p <= 4) /\
      (twelveFiveJ S p = 1 -> S.blockDegree 5 p <= 5) /\
      (2 <= twelveFiveJ S p -> S.blockDegree 5 p <= 6) /\
      S.restoredKappa p + S.lineDegree 4 p + S.blockDegree 5 p =
        3 * (twelveFiveU S p + twelveFiveJ S p) := by
    simpa [S] using hjuq
  rcases hjuqS with ⟨hd3, hu, hq, hcap0, hcap1, hcap2, hkappa⟩
  have row0 : S.lineDegree 4 p = 0 -> twelveFiveQ S p = 0 ->
      twelveFiveJ S p = 0 := by
    intro he hq0
    by_contra hj0
    have hvalues : twelveFiveJ S p = 2 /\ twelveFiveU S p = 0 /\
        S.blockDegree 5 p = 6 /\ S.restoredKappa p = 0 := by
      by_cases hj1 : twelveFiveJ S p = 1
      · have hc := hcap1 hj1
        have hne := hlocalS.kappaNeOne
        have hnonneg := hlocalS.kappaNonneg
        omega
      · have hj2 : 2 <= twelveFiveJ S p := by omega
        have hc := hcap2 hj2
        have hne := hlocalS.kappaNeOne
        have hnonneg := hlocalS.kappaNonneg
        omega
    have hforbid : Not (exists q : alpha,
        S.blockDegree 3 q = 13 /\ S.blockDegree 5 q = 6 /\
        S.lineDegree 3 q = 5 /\ S.lineDegree 4 q = 0) := by
      simpa [S] using
        Grid.forbiddenGridTypeZero cfg hadm hcard hcap5 hL5
    apply hforbid
    refine ⟨p, ?_, hvalues.2.2.1, ?_, he⟩
    · omega
    · omega
  have row1 : S.lineDegree 4 p = 0 -> twelveFiveQ S p = 1 ->
      twelveFiveJ S p <= 1 := by
    intro he hq1
    by_contra hj
    have hvalues : twelveFiveJ S p = 2 /\ twelveFiveU S p = 1 /\
        S.blockDegree 5 p = 6 := by
      have hc := hcap2 (by omega)
      have hne := hlocalS.kappaNeOne
      have hnonneg := hlocalS.kappaNonneg
      omega
    have hforbid : Not (exists q : alpha,
        S.blockDegree 3 q = 13 /\ S.blockDegree 5 q = 6 /\
        S.lineDegree 3 q = 4 /\ S.lineDegree 4 q = 0) := by
      simpa [S] using
        Grid.forbiddenGridTypeOne cfg hadm hcard hcap5 hL5
    apply hforbid
    refine ⟨p, ?_, hvalues.2.2, ?_, he⟩
    · omega
    · omega
  have row2 : twelveFiveQ S p = 0 -> S.lineDegree 4 p = 1 ->
      twelveFiveJ S p = 1 /\ twelveFiveU S p = 1 /\
        S.blockDegree 5 p = 5 /\ S.restoredKappa p = 0 := by
    intro hq0 he
    by_cases hj0 : twelveFiveJ S p = 0
    · have hc := hcap0 hj0
      have hne := hlocalS.kappaNeOne
      have hnonneg := hlocalS.kappaNonneg
      omega
    · by_cases hj1 : twelveFiveJ S p = 1
      · have hc := hcap1 hj1
        have hnonneg := hlocalS.kappaNonneg
        omega
      · have hc := hcap2 (by omega)
        have hnonneg := hlocalS.kappaNonneg
        omega
  have row3 : twelveFiveQ S p = 0 -> S.lineDegree 4 p = 2 ->
      twelveFiveJ S p = 0 /\ twelveFiveU S p = 2 /\
        S.blockDegree 5 p = 4 /\ S.restoredKappa p = 0 := by
    intro hq0 he
    by_cases hj0 : twelveFiveJ S p = 0
    · have hc := hcap0 hj0
      have hnonneg := hlocalS.kappaNonneg
      omega
    · by_cases hj1 : twelveFiveJ S p = 1
      · have hc := hcap1 hj1
        have hnonneg := hlocalS.kappaNonneg
        omega
      · have hc := hcap2 (by omega)
        have hnonneg := hlocalS.kappaNonneg
        omega
  exact ⟨row0, row1, row2, row3⟩

private theorem twelveFive_lineDegree_le_lineCount
    {Point Block : Type*} [Fintype Point] [Fintype Block]
    [DecidableEq Point]
    (S : BlockSystem Point Block) (s : Nat) (p : Point) :
    S.lineDegree s p <= S.lineCount s := by
  unfold BlockSystem.lineDegree BlockSystem.degreeIn BlockSystem.lineCount
  exact Finset.card_filter_le _ _

private theorem twelveFive_blockDegree_le_blockCount
    {Point Block : Type*} [Fintype Point] [Fintype Block]
    [DecidableEq Point]
    (S : BlockSystem Point Block) (s : Nat) (p : Point) :
    S.blockDegree s p <= S.blockCount s := by
  unfold BlockSystem.blockDegree BlockSystem.degreeIn BlockSystem.blockCount
  exact Finset.card_filter_le _ _

/-- Modified unused-arm variable in the possible five-line subbranch. -/
noncomputable def twelveFiveUHat
    {Point Block : Type*} [Fintype Point] [Fintype Block]
    [DecidableEq Point] (S : BlockSystem Point Block) (p : Point) : Nat :=
  5 - S.lineDegree 3 p - 2 * S.lineDegree 5 p

/-- Modified nonnegative `q` variable in the possible five-line subbranch. -/
noncomputable def twelveFiveQHat
    {Point Block : Type*} [Fintype Point] [Fintype Block]
    [DecidableEq Point] (S : BlockSystem Point Block) (p : Point) : Nat :=
  twelveFiveUHat S p + 2 * twelveFiveJ S p + 2 +
    S.lineDegree 5 p - S.blockDegree 5 p

/-- The exact nonnegative-sum argument excluding a five-line from the main
`C=50`, `K=B5`, `L=14` front. -/
private theorem twelveFive_main_front_has_no_five_line
    {alpha : Type u} [Fintype alpha] [DecidableEq alpha]
    (Grid : RealPlaneTwelveGridPrinciple.{u})
    (cfg : Configuration alpha) (hadm : Admissible cfg)
    (hcard : Fintype.card alpha = 12)
    (hcap5 : BlockSizeCap (blockSystem cfg) 5)
    (hfront : TwelveGammaFiveFrontConditions
      (twelveGammaFiveFrontDataOfBlockSystem (blockSystem cfg)))
    (hlocal : forall p : alpha,
      TwelveFiveLocalRows (blockSystem cfg) p)
    (hKcast : (twelveFiveSigmaTotal (blockSystem cfg) : Int) =
      ∑ p : alpha, (blockSystem cfg).pivotSigma p)
    (hB6 : (blockSystem cfg).blockCount 6 = 0)
    (hK : twelveFiveSigmaTotal (blockSystem cfg) =
      (blockSystem cfg).blockCount 5)
    (hL : (blockSystem cfg).lineCount 3 +
      (blockSystem cfg).lineCount 4 + (blockSystem cfg).lineCount 5 +
      (blockSystem cfg).lineCount 6 = 14) :
    (blockSystem cfg).lineCount 5 = 0 := by
  classical
  let S := blockSystem cfg
  have hfrontS : TwelveGammaFiveFrontConditions
      (twelveGammaFiveFrontDataOfBlockSystem S) := by
    simpa [S] using hfront
  have hlocalS : forall p : alpha, TwelveFiveLocalRows S p := by
    simpa [S] using hlocal
  have hKcastS : (twelveFiveSigmaTotal S : Int) =
      ∑ p : alpha, S.pivotSigma p := by
    simpa [S] using hKcast
  have hB6S : S.blockCount 6 = 0 := by simpa [S] using hB6
  have hKS : twelveFiveSigmaTotal S = S.blockCount 5 := by
    simpa [S] using hK
  have hLS : S.lineCount 3 + S.lineCount 4 + S.lineCount 5 +
      S.lineCount 6 = 14 := by
    simpa [S] using hL
  change S.lineCount 5 = 0
  by_contra hL5zero
  have hsumKappa := twelveFive_sum_kappa_row S hcard hlocalS hKcastS
  have hsumKappaNonneg : 0 <= ∑ p : alpha, S.restoredKappa p :=
    Finset.sum_nonneg fun p _hp => (hlocalS p).kappaNonneg
  have hL6 := twelveFive_lineCount_eq_zero_of_blockCount_eq_zero S 6 hB6S
  have hB5cap := hfrontS.fiveBlockCap
  simp only [twelveGammaFiveFrontDataOfBlockSystem] at hB5cap
  have hscalar : S.lineCount 5 = 1 /\ S.lineCount 4 = 0 /\
      10 <= S.blockCount 5 := by
    omega
  rcases hscalar with ⟨hL5, hL4, hkLower⟩
  have hB3 : S.blockCount 3 = 12 + 2 * S.blockCount 5 := by
    have hT := hfrontS.tripleRow
    have hB := hfrontS.blockRow
    simp only [twelveGammaFiveFrontDataOfBlockSystem] at hT hB
    omega
  have hd6 (p : alpha) : S.blockDegree 6 p = 0 :=
    twelveFive_blockDegree_eq_zero_of_blockCount_eq_zero S 6 p hB6S
  have hld6 (p : alpha) : S.lineDegree 6 p = 0 :=
    twelveFive_lineDegree_eq_zero_of_lineCount_eq_zero S 6 p hL6
  have hld4 (p : alpha) : S.lineDegree 4 p = 0 := by
    exact twelveFive_lineDegree_eq_zero_of_lineCount_eq_zero S 4 p hL4
  have hjRow (p : alpha) : S.blockDegree 3 p =
      7 + 3 * twelveFiveJ S p := by
    have hmod : S.blockDegree 3 p % 3 = 1 := by
      have := (hlocalS p).pairRow
      have hd6p := hd6 p
      omega
    have hlower : 7 <= S.blockDegree 3 p := by
      have hpairs := (hlocalS p).pairRow
      have hkelly := (hlocalS p).kellyRow
      omega
    have hsubmod : (S.blockDegree 3 p - 7) % 3 = 0 := by omega
    have hdiv := Nat.mod_add_div (S.blockDegree 3 p - 7) 3
    unfold twelveFiveJ
    omega
  have hzCap (p : alpha) : S.lineDegree 5 p <= 1 := by
    exact (twelveFive_lineDegree_le_lineCount S 5 p).trans_eq hL5
  have huHatRow (p : alpha) :
      twelveFiveUHat S p + S.lineDegree 3 p +
        2 * S.lineDegree 5 p = 5 := by
    have harms := (hlocalS p).lineArmRow
    have hz := hzCap p
    unfold twelveFiveUHat
    omega
  have hcapJ (p : alpha) :
      (twelveFiveJ S p = 0 -> S.blockDegree 5 p <= 4) /\
      (twelveFiveJ S p = 1 -> S.blockDegree 5 p <= 5) /\
      (2 <= twelveFiveJ S p -> S.blockDegree 5 p <= 6) := by
    constructor
    · intro hj
      have hs := (hlocalS p).sigmaRow
      have hn := (hlocalS p).sigmaNonneg
      have hd3 := hjRow p
      omega
    constructor
    · intro hj
      apply Grid.jOneFiveDegreeCap cfg hadm hcard hcap5 p
      have hd3ten : S.blockDegree 3 p = 10 := by
        have := hjRow p
        omega
      simpa [S] using hd3ten
    · intro _hj
      exact (hlocalS p).fiveDegreeCap
  have hkappaHat (p : alpha) :
      S.restoredKappa p + S.blockDegree 5 p =
        3 * (twelveFiveUHat S p + twelveFiveJ S p) +
          S.lineDegree 5 p := by
    have hs := (hlocalS p).sigmaRow
    have hk := (hlocalS p).kappaRow
    have hj := hjRow p
    have hu := huHatRow p
    have hl4 := hld4 p
    have hl6 := hld6 p
    have hd6p := hd6 p
    omega
  have hqHatRow (p : alpha) :
      twelveFiveQHat S p + S.blockDegree 5 p =
        twelveFiveUHat S p + 2 * twelveFiveJ S p + 2 +
          S.lineDegree 5 p := by
    rcases hcapJ p with ⟨hc0, hc1, hc2⟩
    have hk := hkappaHat p
    have hkn := (hlocalS p).kappaNonneg
    have hle : S.blockDegree 5 p <=
        twelveFiveUHat S p + 2 * twelveFiveJ S p + 2 +
          S.lineDegree 5 p := by
      by_cases hj0 : twelveFiveJ S p = 0
      · have hc := hc0 hj0
        by_cases hu0 : twelveFiveUHat S p = 0
        · omega
        · by_cases hu1 : twelveFiveUHat S p = 1
          · omega
          · omega
      · by_cases hj1 : twelveFiveJ S p = 1
        · have hc := hc1 hj1
          by_cases hu0 : twelveFiveUHat S p = 0
          · omega
          · omega
        · have hc := hc2 (by omega)
          omega
    unfold twelveFiveQHat
    omega
  have hinc3 := S.block_incidence 3
  have hsumJPoint :
      (∑ p : alpha, S.blockDegree 3 p) =
        84 + 3 * ∑ p : alpha, twelveFiveJ S p := by
    calc
      (∑ p : alpha, S.blockDegree 3 p) =
          ∑ p : alpha, (7 + 3 * twelveFiveJ S p) := by
        apply Finset.sum_congr rfl
        intro p _hp
        exact hjRow p
      _ = 84 + 3 * ∑ p : alpha, twelveFiveJ S p := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum]
        simp [hcard]
  have hsumJ : (∑ p : alpha, twelveFiveJ S p) + 16 =
      2 * S.blockCount 5 := by omega
  have hzInc := S.line_incidence 5
  have hline3 := S.line_incidence 3
  have hsumUPoint :
      (∑ p : alpha, twelveFiveUHat S p) +
          (∑ p : alpha, S.lineDegree 3 p) +
          2 * (∑ p : alpha, S.lineDegree 5 p) = 60 := by
    calc
      (∑ p : alpha, twelveFiveUHat S p) +
          (∑ p : alpha, S.lineDegree 3 p) +
          2 * (∑ p : alpha, S.lineDegree 5 p) =
          ∑ p : alpha,
            (twelveFiveUHat S p + S.lineDegree 3 p +
              2 * S.lineDegree 5 p) := by
        simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
      _ = ∑ _p : alpha, 5 := by
        apply Finset.sum_congr rfl
        intro p _hp
        exact huHatRow p
      _ = 60 := by simp [hcard]
  have hsumU : (∑ p : alpha, twelveFiveUHat S p) = 11 := by
    omega
  have hinc5 := S.block_incidence 5
  have hsumQPoint :
      (∑ p : alpha, twelveFiveQHat S p) +
          (∑ p : alpha, S.blockDegree 5 p) =
        (∑ p : alpha, twelveFiveUHat S p) +
          2 * (∑ p : alpha, twelveFiveJ S p) + 24 +
          (∑ p : alpha, S.lineDegree 5 p) := by
    calc
      (∑ p : alpha, twelveFiveQHat S p) +
          (∑ p : alpha, S.blockDegree 5 p) =
          ∑ p : alpha, (twelveFiveQHat S p + S.blockDegree 5 p) := by
        simp only [Finset.sum_add_distrib]
      _ = ∑ p : alpha,
          (twelveFiveUHat S p + 2 * twelveFiveJ S p + 2 +
            S.lineDegree 5 p) := by
        apply Finset.sum_congr rfl
        intro p _hp
        exact hqHatRow p
      _ = (∑ p : alpha, twelveFiveUHat S p) +
          2 * (∑ p : alpha, twelveFiveJ S p) + 24 +
          (∑ p : alpha, S.lineDegree 5 p) := by
        simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
        simp [hcard]
  have hsumQ : (∑ p : alpha, twelveFiveQHat S p) +
      S.blockCount 5 = 8 := by omega
  have hnonneg : 0 <= ∑ p : alpha, twelveFiveQHat S p := Nat.zero_le _
  omega

private theorem twelveFive_two_four_lines_same_support_impossible
    {Point Block : Type*} [Fintype Point] [Fintype Block]
    [DecidableEq Point]
    (S : BlockSystem Point Block) (hL4 : S.lineCount 4 = 2)
    (hnoOne : forall p : Point, S.lineDegree 4 p ≠ 1) : False := by
  classical
  let F := S.lineBlocksOfSize 4
  have hFcard : F.card = 2 := by
    simpa [F, BlockSystem.lineCount] using hL4
  obtain ⟨a, b, hab, hF⟩ := Finset.card_eq_two.mp hFcard
  have haMem : a ∈ F := by rw [hF]; simp
  have hbMem : b ∈ F := by rw [hF]; simp
  have haSpec := S.mem_blocksOfKindSize.mp haMem
  have hbSpec := S.mem_blocksOfKindSize.mp hbMem
  have habSupport : S.support a = S.support b := by
    apply Finset.Subset.antisymm
    · intro p hpa
      by_contra hpb
      have hdeg : S.lineDegree 4 p = 1 := by
        unfold BlockSystem.lineDegree BlockSystem.degreeIn
        rw [show S.lineBlocksOfSize 4 = {a, b} by exact hF]
        simp only [Finset.filter_insert, Finset.filter_singleton,
          hpa, hpb, if_true, if_false]
        exact Finset.card_singleton a
      exact hnoOne p hdeg
    · intro p hpb
      by_contra hpa
      have hdeg : S.lineDegree 4 p = 1 := by
        unfold BlockSystem.lineDegree BlockSystem.degreeIn
        rw [show S.lineBlocksOfSize 4 = {a, b} by exact hF]
        simp only [Finset.filter_insert, Finset.filter_singleton,
          hpa, hpb, if_true, if_false]
        exact Finset.card_singleton b
      exact hnoOne p hdeg
  let la : LineBlock S := ⟨a, haSpec.1⟩
  let lb : LineBlock S := ⟨b, hbSpec.1⟩
  have hne : la ≠ lb := by
    intro h
    have : a = b := congrArg Subtype.val h
    exact hab this
  have hinter := S.distinct_line_inter_card_lt_two hne
  have hcardInter : (S.support la.1 ∩ S.support lb.1).card = 4 := by
    change (S.support a ∩ S.support b).card = 4
    rw [← habSupport, Finset.inter_self, haSpec.2]
  omega

private theorem twelveGammaFive_main_scalar_profiles
    (k h sumJ sumQ sumKappa : Nat)
    (hk : k <= 12)
    (hj : sumJ + 16 = 2 * k)
    (hq : sumQ + k + h = 10)
    (hkap : sumKappa + 7 * h = 6 + k) :
    (h = 0 /\ k = 8) \/ (h = 0 /\ k = 9) \/
    (h = 0 /\ k = 10) \/ (h = 1 /\ k = 8) \/
    (h = 1 /\ k = 9) \/ (h = 2 /\ k = 8) := by
  omega

private theorem twelveFive_all_one_of_sum_twelve
    {Point : Type*} [Fintype Point] [DecidableEq Point]
    (f : Point -> Nat) (hcard : Fintype.card Point = 12)
    (hsum : (∑ p : Point, f p) = 12)
    (hone : forall p : Point, 1 <= f p) (p : Point) : f p = 1 := by
  classical
  let E : Finset Point := Finset.univ.erase p
  have hEcard : E.card = 11 := by
    simp [E, hcard]
  have hElower : E.card <= ∑ q ∈ E, f q := by
    calc
      E.card = ∑ _q ∈ E, 1 := by simp
      _ <= ∑ q ∈ E, f q :=
        Finset.sum_le_sum fun q _hq => hone q
  have hdecomp : (∑ q ∈ E, f q) + f p = 12 := by
    calc
      (∑ q ∈ E, f q) + f p = ∑ q : Point, f q := by
        exact Finset.sum_erase_add Finset.univ f (Finset.mem_univ p)
      _ = 12 := hsum
  have hpone := hone p
  omega

private theorem twelveFive_final_typeA_pivot
    {alpha : Type u} [Fintype alpha] [DecidableEq alpha]
    (cfg : Configuration alpha) (hcard : Fintype.card alpha = 12)
    (hB6 : (blockSystem cfg).blockCount 6 = 0)
    (hL4 : (blockSystem cfg).lineCount 4 = 0)
    (hL5 : (blockSystem cfg).lineCount 5 = 0)
    (hlocal : forall p : alpha,
      TwelveFiveLocalRows (blockSystem cfg) p)
    (hjuq : forall p : alpha,
      (blockSystem cfg).blockDegree 3 p =
          7 + 3 * twelveFiveJ (blockSystem cfg) p /\
      twelveFiveU (blockSystem cfg) p +
          (blockSystem cfg).lineDegree 3 p +
          (blockSystem cfg).lineDegree 4 p = 5 /\
      twelveFiveQ (blockSystem cfg) p +
          (blockSystem cfg).blockDegree 5 p =
        twelveFiveU (blockSystem cfg) p +
          2 * twelveFiveJ (blockSystem cfg) p + 2 /\
      (twelveFiveJ (blockSystem cfg) p = 0 ->
        (blockSystem cfg).blockDegree 5 p <= 4) /\
      (twelveFiveJ (blockSystem cfg) p = 1 ->
        (blockSystem cfg).blockDegree 5 p <= 5) /\
      (2 <= twelveFiveJ (blockSystem cfg) p ->
        (blockSystem cfg).blockDegree 5 p <= 6) /\
      (blockSystem cfg).restoredKappa p +
          (blockSystem cfg).lineDegree 4 p +
          (blockSystem cfg).blockDegree 5 p =
        3 * (twelveFiveU (blockSystem cfg) p +
          twelveFiveJ (blockSystem cfg) p))
    (hsumJ : (∑ p : alpha, twelveFiveJ (blockSystem cfg) p) = 0)
    (hsumU : (∑ p : alpha, twelveFiveU (blockSystem cfg) p) = 18)
    (hsumQ : (∑ p : alpha, twelveFiveQ (blockSystem cfg) p) = 2) :
    exists p : alpha,
      (blockSystem cfg).blockDegree 3 p = 7 /\
      (blockSystem cfg).blockDegree 4 p = 10 /\
      (blockSystem cfg).blockDegree 5 p = 3 /\
      (blockSystem cfg).blockDegree 6 p = 0 /\
      (blockSystem cfg).lineDegree 3 p = 4 /\
      (blockSystem cfg).lineDegree 4 p = 0 /\
      (blockSystem cfg).lineDegree 5 p = 0 /\
      (blockSystem cfg).lineDegree 6 p = 0 := by
  classical
  let S := blockSystem cfg
  change exists p : alpha,
    S.blockDegree 3 p = 7 /\
    S.blockDegree 4 p = 10 /\
    S.blockDegree 5 p = 3 /\
    S.blockDegree 6 p = 0 /\
    S.lineDegree 3 p = 4 /\
    S.lineDegree 4 p = 0 /\
    S.lineDegree 5 p = 0 /\
    S.lineDegree 6 p = 0
  let Z : Finset alpha := Finset.univ.filter fun p => twelveFiveQ S p = 0
  let N : Finset alpha := Finset.univ \ Z
  have hB6S : S.blockCount 6 = 0 := by simpa [S] using hB6
  have hL4S : S.lineCount 4 = 0 := by simpa [S] using hL4
  have hL5S : S.lineCount 5 = 0 := by simpa [S] using hL5
  have hlocalS : forall p : alpha, TwelveFiveLocalRows S p := by
    simpa [S] using hlocal
  have hjuqS (p : alpha) :
      S.blockDegree 3 p = 7 + 3 * twelveFiveJ S p /\
      twelveFiveU S p + S.lineDegree 3 p + S.lineDegree 4 p = 5 /\
      twelveFiveQ S p + S.blockDegree 5 p =
        twelveFiveU S p + 2 * twelveFiveJ S p + 2 /\
      (twelveFiveJ S p = 0 -> S.blockDegree 5 p <= 4) /\
      (twelveFiveJ S p = 1 -> S.blockDegree 5 p <= 5) /\
      (2 <= twelveFiveJ S p -> S.blockDegree 5 p <= 6) /\
      S.restoredKappa p + S.lineDegree 4 p + S.blockDegree 5 p =
        3 * (twelveFiveU S p + twelveFiveJ S p) := by
    simpa [S] using hjuq p
  have hsumJS : (∑ p : alpha, twelveFiveJ S p) = 0 := by
    simpa [S] using hsumJ
  have hsumUS : (∑ p : alpha, twelveFiveU S p) = 18 := by
    simpa [S] using hsumU
  have hsumQS : (∑ p : alpha, twelveFiveQ S p) = 2 := by
    simpa [S] using hsumQ
  have hNsubset : N ⊆ (Finset.univ : Finset alpha) := Finset.sdiff_subset
  have hNcardLeSum : N.card <= ∑ p ∈ N, twelveFiveQ S p := by
    calc
      N.card = ∑ _p ∈ N, 1 := by simp
      _ <= ∑ p ∈ N, twelveFiveQ S p := by
        apply Finset.sum_le_sum
        intro p hp
        have hpN := Finset.mem_sdiff.mp hp
        have hpNotZ : twelveFiveQ S p ≠ 0 := by
          simpa [Z] using hpN.2
        omega
  have hNSumLe : (∑ p ∈ N, twelveFiveQ S p) <=
      ∑ p : alpha, twelveFiveQ S p := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · exact hNsubset
    · intro p _hp _hnot
      exact Nat.zero_le _
  have hNcard : N.card <= 2 := by omega
  have hpartition : Z.card + N.card = 12 := by
    have hZsub : Z ⊆ (Finset.univ : Finset alpha) := Finset.filter_subset _ _
    have hcardDiff := Finset.card_sdiff_add_card_eq_card hZsub
    simpa [N, hcard, Nat.add_comm] using hcardDiff
  have hZcard : 10 <= Z.card := by omega
  by_contra hnone
  push Not at hnone
  have hjzero (p : alpha) : twelveFiveJ S p = 0 := by
    have hle : twelveFiveJ S p <= ∑ q : alpha, twelveFiveJ S q :=
      Finset.single_le_sum (fun q _hq => Nat.zero_le (twelveFiveJ S q))
        (Finset.mem_univ p)
    have hsumJ' : (∑ q : alpha, twelveFiveJ S q) = 0 := hsumJS
    omega
  have huTwo (p : alpha) (hpZ : p ∈ Z) : twelveFiveU S p = 2 := by
    have hq0 : twelveFiveQ S p = 0 := by simpa [Z] using hpZ
    rcases hjuqS p with ⟨_hd3, _hu, hq, hcap0, _hcap1, _hcap2, hkappa⟩
    have hc := hcap0 (hjzero p)
    have hkn := (hlocalS p).kappaNonneg
    have hne : twelveFiveU S p ≠ 1 := by
      intro hu1
      have hL6 := twelveFive_lineCount_eq_zero_of_blockCount_eq_zero S 6 hB6S
      have hd6 := twelveFive_blockDegree_eq_zero_of_blockCount_eq_zero S 6 p hB6S
      have hld4 := twelveFive_lineDegree_eq_zero_of_lineCount_eq_zero S 4 p hL4S
      have hld5 := twelveFive_lineDegree_eq_zero_of_lineCount_eq_zero S 5 p hL5S
      have hld6 := twelveFive_lineDegree_eq_zero_of_lineCount_eq_zero S 6 p hL6
      have hpairs := (hlocalS p).pairRow
      have hd3eq : S.blockDegree 3 p = 7 := by omega
      have hd4eq : S.blockDegree 4 p = 10 := by omega
      have hd5eq : S.blockDegree 5 p = 3 := by omega
      have hl3eq : S.lineDegree 3 p = 4 := by omega
      exact (hnone p hd3eq hd4eq hd5eq hd6 hl3eq hld4 hld5) hld6
    omega
  have hZUlower : 2 * Z.card <= ∑ p ∈ Z, twelveFiveU S p := by
    calc
      2 * Z.card = ∑ _p ∈ Z, 2 := by simp [Nat.mul_comm]
      _ <= ∑ p ∈ Z, twelveFiveU S p := by
        apply Finset.sum_le_sum
        intro p hp
        rw [huTwo p hp]
  have hZUsumLe : (∑ p ∈ Z, twelveFiveU S p) <=
      ∑ p : alpha, twelveFiveU S p := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · exact Finset.filter_subset _ _
    · intro p _hp _hnot
      exact Nat.zero_le _
  omega

private theorem twelveFive_C50_six_line_endpoint_impossible
    {alpha : Type u} [Fintype alpha] [DecidableEq alpha]
    (Gram : RealPlaneTwelveGramPrinciple.{u})
    (cfg : Configuration alpha) (hadm : Admissible cfg)
    (hcard : Fintype.card alpha = 12)
    (hcap : BlockSizeCap (blockSystem cfg) 6)
    (hlocal : forall p : alpha,
      TwelveFiveLocalRows (blockSystem cfg) p)
    (hKcast : (twelveFiveSigmaTotal (blockSystem cfg) : Int) =
      ∑ p : alpha, (blockSystem cfg).pivotSigma p)
    (hsplit6 : (blockSystem cfg).blockCount 6 =
      (blockSystem cfg).lineCount 6)
    (hB6 : (blockSystem cfg).blockCount 6 = 1)
    (hK : twelveFiveSigmaTotal (blockSystem cfg) = 12)
    (hB5 : (blockSystem cfg).blockCount 5 = 12)
    (hL : (blockSystem cfg).lineCount 3 +
      (blockSystem cfg).lineCount 4 + (blockSystem cfg).lineCount 5 +
      (blockSystem cfg).lineCount 6 = 13) : False := by
  classical
  let S := blockSystem cfg
  have hlocalS : forall p : alpha, TwelveFiveLocalRows S p := by
    simpa [S] using hlocal
  have hKcastS : (twelveFiveSigmaTotal S : Int) =
      ∑ p : alpha, S.pivotSigma p := by
    simpa [S] using hKcast
  have hsplit6S : S.blockCount 6 = S.lineCount 6 := by
    simpa [S] using hsplit6
  have hB6S : S.blockCount 6 = 1 := by simpa [S] using hB6
  have hKS : twelveFiveSigmaTotal S = 12 := by simpa [S] using hK
  have hB5S : S.blockCount 5 = 12 := by simpa [S] using hB5
  have hLS : S.lineCount 3 + S.lineCount 4 + S.lineCount 5 +
      S.lineCount 6 = 13 := by
    simpa [S] using hL
  have hsumKappa := twelveFive_sum_kappa_row S hcard hlocalS hKcastS
  have hsumKappaNonneg : 0 <= ∑ p : alpha, S.restoredKappa p :=
    Finset.sum_nonneg fun p _hp => (hlocalS p).kappaNonneg
  have hlines : S.lineCount 6 = 1 /\ S.lineCount 4 = 0 /\
      S.lineCount 5 = 0 /\ S.lineCount 3 = 12 /\
      (∑ p : alpha, S.restoredKappa p) = 0 := by
    omega
  rcases hlines with ⟨hL6, hL4, hL5, hL3, hkapSum⟩
  have hld4 (p : alpha) : S.lineDegree 4 p = 0 :=
    twelveFive_lineDegree_eq_zero_of_lineCount_eq_zero S 4 p hL4
  have hld5 (p : alpha) : S.lineDegree 5 p = 0 :=
    twelveFive_lineDegree_eq_zero_of_lineCount_eq_zero S 5 p hL5
  have hkappa (p : alpha) : S.restoredKappa p = 0 :=
    twelveFive_kappa_eq_zero_of_sum_eq_zero S
      (fun q => (hlocalS q).kappaNonneg) hkapSum p
  have hsigmaPos (p : alpha) : 1 <= S.pivotSigma p := by
    have hk := (hlocalS p).kappaRow
    have hn := (hlocalS p).sigmaNonneg
    have hkzero := hkappa p
    have hl4 := hld4 p
    have hl5 := hld5 p
    omega
  have htoOne (p : alpha) : Int.toNat (S.pivotSigma p) = 1 := by
    apply twelveFive_all_one_of_sum_twelve
      (fun q : alpha => Int.toNat (S.pivotSigma q)) hcard
    · simpa [twelveFiveSigmaTotal] using hKS
    · intro q
      have hq := hsigmaPos q
      have hqnonneg : 0 <= S.pivotSigma q := by omega
      have hcast := Int.toNat_of_nonneg hqnonneg
      omega
  have hsigmaOne (p : alpha) : S.pivotSigma p = 1 := by
    have hpnonneg : 0 <= S.pivotSigma p := by have := hsigmaPos p; omega
    have hcast := Int.toNat_of_nonneg hpnonneg
    have ht := htoOne p
    omega
  have hd6cap (p : alpha) : S.blockDegree 6 p <= 1 := by
    exact (twelveFive_blockDegree_le_blockCount S 6 p).trans_eq hB6S
  have hd5weighted (p : alpha) :
      S.blockDegree 5 p + 3 * S.blockDegree 6 p <= 6 := by
    have hpairs := (hlocalS p).pairRow
    have hsrow := (hlocalS p).sigmaRow
    have hd5cap := (hlocalS p).fiveDegreeCap
    by_cases hd6 : S.blockDegree 6 p = 0
    · omega
    · have hdcap := hd6cap p
      have hd6one : S.blockDegree 6 p = 1 := by omega
      have hrichRaw := Gram.fiveDegreeCapOnSixBlock cfg hadm hcard hcap p
        (by simpa [S] using (show 0 < S.blockDegree 6 p by omega))
      have hrich : S.blockDegree 5 p <= 5 := by
        simpa [S] using hrichRaw
      have hsone := hsigmaOne p
      have hmod : S.blockDegree 5 p % 3 = 0 := by omega
      omega
  have hsumWeighted :
      (∑ p : alpha, S.blockDegree 5 p) +
          3 * (∑ p : alpha, S.blockDegree 6 p) <= 72 := by
    calc
      (∑ p : alpha, S.blockDegree 5 p) +
          3 * (∑ p : alpha, S.blockDegree 6 p) =
          ∑ p : alpha,
            (S.blockDegree 5 p + 3 * S.blockDegree 6 p) := by
        simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
      _ <= ∑ _p : alpha, 6 :=
        Finset.sum_le_sum fun p _hp => hd5weighted p
      _ = 72 := by simp [hcard]
  have hinc5 := S.block_incidence 5
  have hinc6 := S.block_incidence 6
  omega

/-- Full selected-five-circle endpoint, conditional only on the explicit
real-plane principles whose local statements are listed in
`TwelveGeometry`. -/
theorem twelveFive_circleCount_ge_fifty_one
    {alpha : Type u} [Fintype alpha] [DecidableEq alpha]
    (Mel : RealPlaneMelchiorPrinciple.{u})
    (EvenArr : RealPlaneEvenArrangementPrinciple.{u})
    (Kelly : RealPlaneKellyMoserPrinciple.{u})
    (Gram : RealPlaneTwelveGramPrinciple.{u})
    (Grid : RealPlaneTwelveGridPrinciple.{u})
    (Gallery : RealPlaneTwelveGalleryPrinciple.{u})
    (cfg : Configuration alpha) (hadm : Admissible cfg)
    (hcard : Fintype.card alpha = 12)
    (gamma : DeterminedCircle cfg)
    (hgamma : (circleTrace cfg gamma.1).card = 5)
    (hcircle : forall c : DeterminedCircle cfg,
      (circleTrace cfg c.1).card <= 5) :
    51 <= Erdos506.V4.circleCount cfg := by
  classical
  by_contra htarget
  have hcount : Erdos506.V4.circleCount cfg <= 50 := by omega
  let S := blockSystem cfg
  have htotal : S.totalCircleCount = Erdos506.V4.circleCount cfg := by
    rw [show S = blockSystem cfg by rfl,
      totalCircleCount_eq_card_determinedCircle,
      ← Erdos506.V3.circleCount_eq_card_determinedCircle]
  have hcountS : S.totalCircleCount <= 50 := by omega
  have hcap : BlockSizeCap S 6 := by
    simpa [S] using blockSizeCap_six_of_twelve_five_branch
      cfg hadm hcard hcount hcircle
  have hfront : TwelveGammaFiveFrontConditions
      (twelveGammaFiveFrontDataOfBlockSystem S) := by
    simpa [S] using twelveGammaFiveFrontConditions_of_configuration
      Mel Gram cfg hadm hcard hcount hcircle
  have hB5pos : 1 <= S.blockCount 5 := by
    let b : GeometricBlock cfg := Sum.inr gamma
    have hbmem : b ∈ S.blocksOfSize 5 := by
      apply S.mem_blocksOfSize.mpr
      simpa [b, S, blockSystem, geometricBlockSystem,
        geometricBlockSupport] using hgamma
    have hpos : 0 < (S.blocksOfSize 5).card := Finset.card_pos.mpr ⟨b, hbmem⟩
    simpa [BlockSystem.blockCount] using hpos
  have hlocal : forall p : alpha, TwelveFiveLocalRows S p := by
    intro p
    simpa [S] using twelveFiveLocalRows_of_configuration
      Mel EvenArr Kelly Gram cfg hadm hcard hcap p
  have hsigmaNonneg : forall p : alpha, 0 <= S.pivotSigma p :=
    fun p => (hlocal p).sigmaNonneg
  have hkappaNonneg : forall p : alpha, 0 <= S.restoredKappa p :=
    fun p => (hlocal p).kappaNonneg
  have hKcast : (twelveFiveSigmaTotal S : Int) =
      ∑ p : alpha, S.pivotSigma p :=
    twelveFiveSigmaTotal_cast S hsigmaNonneg
  have hKapCast : (twelveFiveKappaTotal S : Int) =
      ∑ p : alpha, S.restoredKappa p :=
    twelveFiveKappaTotal_cast S hkappaNonneg
  have hsumKappa := twelveFive_sum_kappa_row S hcard hlocal hKcast
  have hsumKappaNat : twelveFiveKappaTotal S +
      9 * S.lineCount 3 + 16 * S.lineCount 4 +
      25 * S.lineCount 5 + 36 * S.lineCount 6 =
      132 + twelveFiveSigmaTotal S := by
    have hrow := hsumKappa
    rw [← hKapCast] at hrow
    exact_mod_cast hrow
  obtain ⟨_, _, _, _, _, _, _, hs6, _⟩ :=
    twelveFive_global_rows Mel cfg hadm hcard hcap hcircle
  have hs6S : S.blockCount 6 = S.lineCount 6 := by
    simpa [S] using hs6
  have hCge : 47 <= S.totalCircleCount := by
    exact twelveGammaFive_front_circleCount_ge_forty_seven
      (twelveGammaFiveFrontDataOfBlockSystem S) hfront
  have hCrange : S.totalCircleCount = 47 \/ S.totalCircleCount = 48 \/
      S.totalCircleCount = 49 \/ S.totalCircleCount = 50 := by omega
  rcases hCrange with hC47 | hC48 | hC49 | hC50
  · have hvals : twelveFiveSigmaTotal S = 0 /\ S.blockCount 5 = 12 := by
      rcases hfront with ⟨hB5cap, hT, hB, hL, hA⟩
      simp only [twelveGammaFiveFrontDataOfBlockSystem] at hB5cap hT hB hL hA
      have hmod := twelveGammaFive_K_mod_twelve
        (S.blockCount 4) (S.blockCount 5) (S.blockCount 6)
          (twelveFiveSigmaTotal S) hB
      omega
    exact twelveFive_Kzero_B5twelve_impossible
      S hcard hlocal hvals.1 hvals.2
  · have hC48profiles := twelveGammaFive_C48_profiles
      (twelveGammaFiveFrontDataOfBlockSystem S) hfront hC48 hB5pos
    simp only [twelveGammaFiveFrontDataOfBlockSystem] at hC48profiles
    rcases hC48profiles with hzero | hqfront
    · exact twelveFive_Kzero_B5twelve_impossible
        S hcard hlocal hzero.1 hzero.2.1
    · rcases hqfront with ⟨hK, hB5, hB6, hL⟩
      have hL6 := twelveFive_lineCount_eq_zero_of_blockCount_eq_zero S 6 hB6
      have hrichZero : S.lineCount 4 = 0 /\ S.lineCount 5 = 0 := by
        omega
      have hcap5 := twelveFive_blockSizeCap_five_of_six_layer_zero S hcap hB6
      have hjuqFull (p : alpha) := twelveFive_local_juq_rows
        Grid cfg hadm hcard hcap5 p (hlocal p) hB6 hrichZero.2
      have hjuq (p : alpha) :
          S.blockDegree 3 p = 7 + 3 * twelveFiveJ S p /\
          twelveFiveU S p + S.lineDegree 3 p + S.lineDegree 4 p = 5 /\
          twelveFiveQ S p + S.blockDegree 5 p =
            twelveFiveU S p + 2 * twelveFiveJ S p + 2 := by
        exact ⟨(hjuqFull p).1, (hjuqFull p).2.1, (hjuqFull p).2.2.1⟩
      have hqrows := twelveGammaFiveQSumConditions_of_blockSystem
        S hcard hfront hB6 (by omega) hrichZero.2 hjuq
      have hqbound := twelveGammaFive_qSum_circleCount_ge_fifty
        (twelveGammaFiveQSumDataOfBlockSystem S) hqrows
      simp only [twelveGammaFiveQSumDataOfBlockSystem] at hqbound
      omega
  · have hC49profiles := twelveGammaFive_C49_profiles
      (twelveGammaFiveFrontDataOfBlockSystem S) hfront hC49 hB5pos
    simp only [twelveGammaFiveFrontDataOfBlockSystem] at hC49profiles
    rcases hC49profiles with hzero | hzero | hqfront
    · exact twelveFive_Kzero_B5twelve_impossible
        S hcard hlocal hzero.1 hzero.2.1
    · exact twelveFive_Kzero_B5twelve_impossible
        S hcard hlocal hzero.1 hzero.2.1
    · rcases hqfront with ⟨hB6, hK, _hk3, _hk12, hL⟩
      have hL6 := twelveFive_lineCount_eq_zero_of_blockCount_eq_zero S 6 hB6
      have hL5 : S.lineCount 5 = 0 := by omega
      have hcap5 := twelveFive_blockSizeCap_five_of_six_layer_zero S hcap hB6
      have hjuqFull (p : alpha) := twelveFive_local_juq_rows
        Grid cfg hadm hcard hcap5 p (hlocal p) hB6 hL5
      have hjuq (p : alpha) :
          S.blockDegree 3 p = 7 + 3 * twelveFiveJ S p /\
          twelveFiveU S p + S.lineDegree 3 p + S.lineDegree 4 p = 5 /\
          twelveFiveQ S p + S.blockDegree 5 p =
            twelveFiveU S p + 2 * twelveFiveJ S p + 2 := by
        exact ⟨(hjuqFull p).1, (hjuqFull p).2.1, (hjuqFull p).2.2.1⟩
      have hqrows := twelveGammaFiveQSumConditions_of_blockSystem
        S hcard hfront hB6 (by omega) hL5 hjuq
      have hqbound := twelveGammaFive_qSum_circleCount_ge_fifty
        (twelveGammaFiveQSumDataOfBlockSystem S) hqrows
      simp only [twelveGammaFiveQSumDataOfBlockSystem] at hqbound
      omega
  · have hC50profiles := twelveGammaFive_C50_profiles
      (twelveGammaFiveFrontDataOfBlockSystem S) hfront hC50 hB5pos
    simp only [twelveGammaFiveFrontDataOfBlockSystem] at hC50profiles
    rcases hC50profiles with hmain | hzero | hshift | hzero | hsix
    · rcases hmain with ⟨hB6, hK, _hkpos, hkcap, hL⟩
      have hcap5 := twelveFive_blockSizeCap_five_of_six_layer_zero S hcap hB6
      have hL5 : S.lineCount 5 = 0 := by
        exact twelveFive_main_front_has_no_five_line
          Grid cfg hadm hcard hcap5 hfront hlocal hKcast hB6 hK hL
      have hL6 := twelveFive_lineCount_eq_zero_of_blockCount_eq_zero S 6 hB6
      have hjuqFull (p : alpha) := twelveFive_local_juq_rows
        Grid cfg hadm hcard hcap5 p (hlocal p) hB6 hL5
      have hjuq (p : alpha) :
          S.blockDegree 3 p = 7 + 3 * twelveFiveJ S p /\
          twelveFiveU S p + S.lineDegree 3 p + S.lineDegree 4 p = 5 /\
          twelveFiveQ S p + S.blockDegree 5 p =
            twelveFiveU S p + 2 * twelveFiveJ S p + 2 := by
        exact ⟨(hjuqFull p).1, (hjuqFull p).2.1, (hjuqFull p).2.2.1⟩
      have hqrows := twelveGammaFiveQSumConditions_of_blockSystem
        S hcard hfront hB6 hK hL5 hjuq
      have hjSum := hqrows.jSumRow
      have hqSum := hqrows.qSumRow
      simp only [twelveGammaFiveQSumDataOfBlockSystem] at hjSum hqSum
      have hkapNat : twelveFiveKappaTotal S + 7 * S.lineCount 4 =
          6 + S.blockCount 5 := by
        omega
      have hprofiles := twelveGammaFive_main_scalar_profiles
        (S.blockCount 5) (S.lineCount 4)
        (∑ p : alpha, twelveFiveJ S p)
        (∑ p : alpha, twelveFiveQ S p)
        (twelveFiveKappaTotal S) hkcap hjSum (by omega) hkapNat
      have htable (p : alpha) :
          (S.lineDegree 4 p = 0 -> twelveFiveQ S p = 0 ->
            twelveFiveJ S p = 0) /\
          (S.lineDegree 4 p = 0 -> twelveFiveQ S p = 1 ->
            twelveFiveJ S p <= 1) /\
          (twelveFiveQ S p = 0 -> S.lineDegree 4 p = 1 ->
            twelveFiveJ S p = 1 /\ twelveFiveU S p = 1 /\
              S.blockDegree 5 p = 5 /\ S.restoredKappa p = 0) /\
          (twelveFiveQ S p = 0 -> S.lineDegree 4 p = 2 ->
            twelveFiveJ S p = 0 /\ twelveFiveU S p = 2 /\
              S.blockDegree 5 p = 4 /\ S.restoredKappa p = 0) := by
        simpa [S] using twelveFive_low_defect_table
          Grid cfg hadm hcard hcap5 hL5 p (hlocal p)
            ⟨(hjuqFull p).1, (hjuqFull p).2.1, (hjuqFull p).2.2.1,
              (hjuqFull p).2.2.2.1, (hjuqFull p).2.2.2.2.1,
              (hjuqFull p).2.2.2.2.2.1,
              (hjuqFull p).2.2.2.2.2.2.1⟩
      rcases hprofiles with hk | hk | hk | hk | hk | hk
      · rcases hk with ⟨hL4, hk⟩
        have hsumJ : (∑ p : alpha, twelveFiveJ S p) = 0 := by omega
        have hsumURow := hqrows.uSumRow
        have hsumQ : (∑ p : alpha, twelveFiveQ S p) = 2 := by omega
        simp only [twelveGammaFiveQSumDataOfBlockSystem] at hsumURow
        have hsumU : (∑ p : alpha, twelveFiveU S p) = 18 := by
          omega
        have hpivot := twelveFive_final_typeA_pivot cfg hcard hB6 hL4 hL5
          hlocal
          (fun p => ⟨(hjuqFull p).1, (hjuqFull p).2.1,
            (hjuqFull p).2.2.1, (hjuqFull p).2.2.2.1,
            (hjuqFull p).2.2.2.2.1, (hjuqFull p).2.2.2.2.2.1,
            (hjuqFull p).2.2.2.2.2.2.1⟩)
          hsumJ hsumU hsumQ
        exact (Gallery.typeAForbidden cfg hadm hcard hcap) hpivot
      · rcases hk with ⟨hL4, hk⟩
        have hsumJ : (∑ p : alpha, twelveFiveJ S p) = 2 := by omega
        have hsumQ : (∑ p : alpha, twelveFiveQ S p) = 1 := by omega
        have hld4 (p : alpha) :=
          twelveFive_lineDegree_eq_zero_of_lineCount_eq_zero S 4 p hL4
        have hpoint (p : alpha) : twelveFiveJ S p <= twelveFiveQ S p := by
          by_cases hq0 : twelveFiveQ S p = 0
          · have := (htable p).1 (hld4 p) hq0
            omega
          · have hq1 : twelveFiveQ S p = 1 := by
              have hle : twelveFiveQ S p <= ∑ q : alpha, twelveFiveQ S q :=
                Finset.single_le_sum
                  (fun q _hq => Nat.zero_le (twelveFiveQ S q))
                  (Finset.mem_univ p)
              omega
            have hjle := (htable p).2.1 (hld4 p) hq1
            omega
        have hsumLe : (∑ p : alpha, twelveFiveJ S p) <=
            ∑ p : alpha, twelveFiveQ S p :=
          Finset.sum_le_sum fun p _hp => hpoint p
        omega
      · rcases hk with ⟨hL4, hk⟩
        have hsumJ : (∑ p : alpha, twelveFiveJ S p) = 4 := by omega
        have hsumQ : (∑ p : alpha, twelveFiveQ S p) = 0 := by omega
        have hld4 (p : alpha) :=
          twelveFive_lineDegree_eq_zero_of_lineCount_eq_zero S 4 p hL4
        have hj0 (p : alpha) : twelveFiveJ S p = 0 := by
          have hq0 : twelveFiveQ S p = 0 := by
            have hle : twelveFiveQ S p <= ∑ q : alpha, twelveFiveQ S q :=
              Finset.single_le_sum
                (fun q _hq => Nat.zero_le (twelveFiveQ S q))
                (Finset.mem_univ p)
            omega
          exact (htable p).1 (hld4 p) hq0
        have : (∑ p : alpha, twelveFiveJ S p) = 0 := by simp [hj0]
        omega
      · rcases hk with ⟨hL4, hk⟩
        have hsumJ : (∑ p : alpha, twelveFiveJ S p) = 0 := by omega
        have hsumQ : (∑ p : alpha, twelveFiveQ S p) = 1 := by omega
        have hj0 (p : alpha) : twelveFiveJ S p = 0 := by
          have hle : twelveFiveJ S p <= ∑ q : alpha, twelveFiveJ S q :=
            Finset.single_le_sum
              (fun q _hq => Nat.zero_le (twelveFiveJ S q))
              (Finset.mem_univ p)
          omega
        have hepsCap (p : alpha) : S.lineDegree 4 p <= 1 :=
          (twelveFive_lineDegree_le_lineCount S 4 p).trans_eq hL4
        have hepsLeQ (p : alpha) : S.lineDegree 4 p <= twelveFiveQ S p := by
          by_cases he : S.lineDegree 4 p = 0
          · omega
          · have hcapP := hepsCap p
            have he1 : S.lineDegree 4 p = 1 := by omega
            by_contra hq
            have hq0 : twelveFiveQ S p = 0 := by omega
            have hj1 := ((htable p).2.2.1 hq0 he1).1
            have hjzero := hj0 p
            omega
        have hsumEps := S.line_incidence 4
        have hsumLe : (∑ p : alpha, S.lineDegree 4 p) <=
            ∑ p : alpha, twelveFiveQ S p :=
          Finset.sum_le_sum fun p _hp => hepsLeQ p
        omega
      · rcases hk with ⟨hL4, hk⟩
        have hsumJ : (∑ p : alpha, twelveFiveJ S p) = 2 := by omega
        have hsumQ : (∑ p : alpha, twelveFiveQ S p) = 0 := by omega
        have hepsCap (p : alpha) : S.lineDegree 4 p <= 1 :=
          (twelveFive_lineDegree_le_lineCount S 4 p).trans_eq hL4
        have hpoint (p : alpha) : twelveFiveJ S p = S.lineDegree 4 p := by
          have hq0 : twelveFiveQ S p = 0 := by
            have hle : twelveFiveQ S p <= ∑ q : alpha, twelveFiveQ S q :=
              Finset.single_le_sum
                (fun q _hq => Nat.zero_le (twelveFiveQ S q))
                (Finset.mem_univ p)
            omega
          by_cases he : S.lineDegree 4 p = 0
          · have hj0 := (htable p).1 he hq0
            omega
          · have hcapP := hepsCap p
            have he1 : S.lineDegree 4 p = 1 := by omega
            have hj1 := ((htable p).2.2.1 hq0 he1).1
            omega
        have hsumEps := S.line_incidence 4
        have hsumEq : (∑ p : alpha, twelveFiveJ S p) =
            ∑ p : alpha, S.lineDegree 4 p := by
          apply Finset.sum_congr rfl
          intro p _hp
          exact hpoint p
        omega
      · rcases hk with ⟨hL4, hk⟩
        have hsumJ : (∑ p : alpha, twelveFiveJ S p) = 0 := by omega
        have hsumQ : (∑ p : alpha, twelveFiveQ S p) = 0 := by omega
        have hj0 (p : alpha) : twelveFiveJ S p = 0 := by
          have hle : twelveFiveJ S p <= ∑ q : alpha, twelveFiveJ S q :=
            Finset.single_le_sum
              (fun q _hq => Nat.zero_le (twelveFiveJ S q))
              (Finset.mem_univ p)
          omega
        have hq0 (p : alpha) : twelveFiveQ S p = 0 := by
          have hle : twelveFiveQ S p <= ∑ q : alpha, twelveFiveQ S q :=
            Finset.single_le_sum
              (fun q _hq => Nat.zero_le (twelveFiveQ S q))
              (Finset.mem_univ p)
          omega
        have hnoOne (p : alpha) : S.lineDegree 4 p ≠ 1 := by
          intro he
          have hj1 := ((htable p).2.2.1 (hq0 p) he).1
          have hjzero := hj0 p
          exact (by omega)
        exact twelveFive_two_four_lines_same_support_impossible S hL4 hnoOne
    · exact twelveFive_Kzero_B5twelve_impossible
        S hcard hlocal hzero.2.1 hzero.2.2.1
    · rcases hshift with ⟨hB6, hK, hkLower, hkUpper, hL⟩
      have hL6 := twelveFive_lineCount_eq_zero_of_blockCount_eq_zero S 6 hB6
      have hrichZero : S.lineCount 4 = 0 /\ S.lineCount 5 = 0 := by omega
      have hcap5 := twelveFive_blockSizeCap_five_of_six_layer_zero S hcap hB6
      have hjuqFull (p : alpha) := twelveFive_local_juq_rows
        Grid cfg hadm hcard hcap5 p (hlocal p) hB6 hrichZero.2
      have hjuq (p : alpha) :
          S.blockDegree 3 p = 7 + 3 * twelveFiveJ S p /\
          twelveFiveU S p + S.lineDegree 3 p + S.lineDegree 4 p = 5 /\
          twelveFiveQ S p + S.blockDegree 5 p =
            twelveFiveU S p + 2 * twelveFiveJ S p + 2 := by
        exact ⟨(hjuqFull p).1, (hjuqFull p).2.1, (hjuqFull p).2.2.1⟩
      have hsums := twelveGammaFive_shifted_q_sums S hcard hfront
        hB6 hK hL hrichZero.1 hrichZero.2 hjuq
      have hsumJ := hsums.1
      have hsumQ := hsums.2.2
      have hvals : S.blockCount 5 = 9 /\
          (∑ p : alpha, twelveFiveQ S p) = 0 /\
          (∑ p : alpha, S.restoredKappa p) = 0 := by
        omega
      rcases hvals with ⟨hk, hqzero, hkapzero⟩
      have hex : exists p : alpha, 0 < twelveFiveJ S p := by
        by_contra hnone
        push Not at hnone
        have hall (p : alpha) : twelveFiveJ S p = 0 :=
          Nat.eq_zero_of_le_zero (hnone p)
        have hz : (∑ p : alpha, twelveFiveJ S p) = 0 := by simp [hall]
        omega
      rcases hex with ⟨p, hjpos⟩
      have hq0 : twelveFiveQ S p = 0 := by
        have hle : twelveFiveQ S p <= ∑ q : alpha, twelveFiveQ S q :=
          Finset.single_le_sum
            (fun q _hq => Nat.zero_le (twelveFiveQ S q))
            (Finset.mem_univ p)
        omega
      have hkap0 := twelveFive_kappa_eq_zero_of_sum_eq_zero
        S hkappaNonneg hkapzero p
      have hvalsP : twelveFiveJ S p = 2 /\ twelveFiveU S p = 0 /\
          S.blockDegree 5 p = 6 := by
        have hkrow : S.restoredKappa p + S.lineDegree 4 p +
            S.blockDegree 5 p =
              3 * (twelveFiveU S p + twelveFiveJ S p) := by
          simpa [S] using (hjuqFull p).2.2.2.2.2.2.1
        have hqrow := (hjuq p).2.2
        have hcapj : 2 <= twelveFiveJ S p -> S.blockDegree 5 p <= 6 := by
          simpa [S] using (hjuqFull p).2.2.2.2.2.1
        have heps := twelveFive_lineDegree_eq_zero_of_lineCount_eq_zero
          S 4 p hrichZero.1
        omega
      have hforbid : Not (exists q : alpha,
          S.blockDegree 3 q = 13 /\ S.blockDegree 5 q = 6 /\
          S.lineDegree 3 q = 5 /\ S.lineDegree 4 q = 0) := by
        simpa [S] using Grid.forbiddenGridTypeZero
          cfg hadm hcard hcap5 hrichZero.2
      apply hforbid
      refine ⟨p, ?_, hvalsP.2.2, ?_, ?_⟩
      · have hd3 := (hjuq p).1
        omega
      · have hu := (hjuq p).2.1
        have heps := twelveFive_lineDegree_eq_zero_of_lineCount_eq_zero
          S 4 p hrichZero.1
        omega
      · exact twelveFive_lineDegree_eq_zero_of_lineCount_eq_zero
          S 4 p hrichZero.1
    · exact twelveFive_Kzero_B5twelve_impossible
        S hcard hlocal hzero.2.1 hzero.2.2.1
    · rcases hsix with ⟨hB6, hK, hB5, hL⟩
      exact twelveFive_C50_six_line_endpoint_impossible
        Gram cfg hadm hcard hcap hlocal hKcast hs6S hB6 hK hB5 hL

end Erdos506.V1
