import Erdos506.Block.Moments
import Erdos506.V1.TwelveFive

/-!
# Exact rows for the twelve-point selected-six-circle branch

This module derives the natural local rows and exact global counting rows
from a concrete twelve-point configuration.  It contains no normalized
branch router and no endpoint assumption.
-/

namespace Erdos506.V1

open Erdos506.Block
open Erdos506.Block.BlockSystem
open Erdos506.Incidence
open Erdos506.V4
open scoped BigOperators

universe u

private theorem twelveSix_blockCount_eq_zero_of_cap
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

private theorem twelveSix_circleCount_eq_zero_of_cap
    {Point Block : Type*} [Fintype Point] [Fintype Block]
    [DecidableEq Point]
    (S : BlockSystem Point Block)
    (hcircle : forall b : Block,
      S.kind b = .circle -> (S.support b).card <= 6)
    {s : Nat} (hs : 6 < s) : S.circleCount s = 0 := by
  classical
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro b hb
  have hspec := S.mem_blocksOfKindSize.mp hb
  have hle := hcircle b hspec.1
  omega

/-- Under the contradictory circle-count range and a six-circle cap, every
geometric block has support at most six. -/
theorem blockSizeCap_six_of_twelve_six_branch
    {alpha : Type u} [Fintype alpha] [DecidableEq alpha]
    (cfg : Configuration alpha) (hadm : Admissible cfg)
    (hcard : Fintype.card alpha = 12)
    (hcount : Erdos506.V4.circleCount cfg <= 50)
    (hcircle : forall c : DeterminedCircle cfg,
      (circleTrace cfg c.1).card <= 6) :
    BlockSizeCap (blockSystem cfg) 6 := by
  intro b _hthree
  cases b with
  | inl L =>
      simpa [blockSystem, geometricBlockSupport] using
        lineSupport_card_le_six_of_twelve_of_circleCount_le
          cfg hadm hcard hcount L
  | inr c =>
      simpa [blockSystem, geometricBlockSupport] using hcircle c

/-- A selected proper six-circle supplies a six-block. -/
theorem one_le_blockCount_six_of_selected_six_circle
    {alpha : Type u} [Fintype alpha] [DecidableEq alpha]
    (cfg : Configuration alpha) (gamma : DeterminedCircle cfg)
    (hgamma : (circleTrace cfg gamma.1).card = 6) :
    1 <= (blockSystem cfg).blockCount 6 := by
  classical
  let S := blockSystem cfg
  let b : GeometricBlock cfg := Sum.inr gamma
  have hb : b ∈ S.blocksOfSize 6 := by
    apply S.mem_blocksOfSize.mpr
    simpa [S, b, blockSystem, geometricBlockSystem,
      geometricBlockSupport] using hgamma
  change 1 <= (S.blocksOfSize 6).card
  exact Finset.card_pos.mpr ⟨b, hb⟩

/-- Natural versions of the two pointwise restored-pivot slacks. -/
noncomputable def twelveSixSigmaAt
    {Point Block : Type*} [Fintype Point] [Fintype Block]
    [DecidableEq Point] (S : BlockSystem Point Block) (p : Point) : Nat :=
  Int.toNat (S.pivotSigma p)

noncomputable def twelveSixKappaAt
    {Point Block : Type*} [Fintype Point] [Fintype Block]
    [DecidableEq Point] (S : BlockSystem Point Block) (p : Point) : Nat :=
  Int.toNat (S.restoredKappa p)

/-- The exact natural local rows and residues in the universal six-circle
spine. -/
structure TwelveSixLocalRows
    {Point Block : Type*} [Fintype Point] [Fintype Block]
    [DecidableEq Point] (S : BlockSystem Point Block) (p : Point) : Prop where
  pairRow :
    S.blockDegree 3 p + 3 * S.blockDegree 4 p +
      6 * S.blockDegree 5 p + 10 * S.blockDegree 6 p = 55
  sigmaRow :
    twelveSixSigmaAt S p + 3 + S.blockDegree 5 p +
      2 * S.blockDegree 6 p = S.blockDegree 3 p
  lineArmRow :
    S.lineDegree 2 p + 2 * S.lineDegree 3 p +
      3 * S.lineDegree 4 p + 4 * S.lineDegree 5 p +
      5 * S.lineDegree 6 p = 11
  kappaRow :
    twelveSixKappaAt S p + 3 * S.lineDegree 3 p +
      4 * S.lineDegree 4 p + 5 * S.lineDegree 5 p +
      6 * S.lineDegree 6 p = 11 + twelveSixSigmaAt S p
  richResidueRow :
    3 * S.blockDegree 4 p + 7 * S.blockDegree 5 p +
      12 * S.blockDegree 6 p + twelveSixSigmaAt S p = 52
  sigmaResidue :
    (twelveSixSigmaAt S p + S.blockDegree 5 p) % 3 = 1
  kappaResidue :
    (twelveSixKappaAt S p + S.blockDegree 5 p +
      S.lineDegree 4 p) % 3 = S.lineDegree 5 p % 3
  kappaNeOne : twelveSixKappaAt S p ≠ 1
  kellyRow : 33 <= 7 * S.blockDegree 3 p

/-- The already materialized Melchior/even-arrangement/Kelly rows convert
to the natural local spine without any new geometric input. -/
theorem twelveSixLocalRows_of_configuration
    {alpha : Type u} [Fintype alpha] [DecidableEq alpha]
    (Mel : RealPlaneMelchiorPrinciple.{u})
    (EvenArr : RealPlaneEvenArrangementPrinciple.{u})
    (Kelly : RealPlaneKellyMoserPrinciple.{u})
    (Gram : RealPlaneTwelveGramPrinciple.{u})
    (cfg : Configuration alpha) (hadm : Admissible cfg)
    (hcard : Fintype.card alpha = 12)
    (hcap : BlockSizeCap (blockSystem cfg) 6)
    (p : alpha) : TwelveSixLocalRows (blockSystem cfg) p := by
  let S := blockSystem cfg
  have hraw : TwelveFiveLocalRows S p := by
    simpa [S] using twelveFiveLocalRows_of_configuration
      Mel EvenArr Kelly Gram cfg hadm hcard hcap p
  have hsCast : (twelveSixSigmaAt S p : Int) = S.pivotSigma p := by
    simpa [twelveSixSigmaAt] using Int.toNat_of_nonneg hraw.sigmaNonneg
  have hkCast : (twelveSixKappaAt S p : Int) = S.restoredKappa p := by
    simpa [twelveSixKappaAt] using Int.toNat_of_nonneg hraw.kappaNonneg
  have hsigmaZ := hraw.sigmaRow
  rw [← hsCast] at hsigmaZ
  have hsigma : twelveSixSigmaAt S p + 3 + S.blockDegree 5 p +
      2 * S.blockDegree 6 p = S.blockDegree 3 p := by
    exact_mod_cast hsigmaZ
  have hkappaZ := hraw.kappaRow
  rw [← hkCast, ← hsCast] at hkappaZ
  have hkappa : twelveSixKappaAt S p + 3 * S.lineDegree 3 p +
      4 * S.lineDegree 4 p + 5 * S.lineDegree 5 p +
      6 * S.lineDegree 6 p = 11 + twelveSixSigmaAt S p := by
    exact_mod_cast hkappaZ
  have hrich : 3 * S.blockDegree 4 p + 7 * S.blockDegree 5 p +
      12 * S.blockDegree 6 p + twelveSixSigmaAt S p = 52 := by
    have hpairs := hraw.pairRow
    omega
  have hsResidue :
      (twelveSixSigmaAt S p + S.blockDegree 5 p) % 3 = 1 := by
    omega
  have hkResidue :
      (twelveSixKappaAt S p + S.blockDegree 5 p +
        S.lineDegree 4 p) % 3 = S.lineDegree 5 p % 3 := by
    omega
  have hkNe : twelveSixKappaAt S p ≠ 1 := by
    intro hk
    rw [hk] at hkCast
    norm_num at hkCast
    exact hraw.kappaNeOne hkCast.symm
  exact ⟨hraw.pairRow, hsigma, hraw.lineArmRow, hkappa, hrich,
    hsResidue, hkResidue, hkNe, hraw.kellyRow⟩

/-- Exact global rows before quotient normalization. -/
structure TwelveSixGlobalRows
    {Point Block : Type*} [Fintype Point] [Fintype Block]
    [DecidableEq Point] (S : BlockSystem Point Block) : Prop where
  tripleRow :
    S.blockCount 3 + 4 * S.blockCount 4 + 10 * S.blockCount 5 +
      20 * S.blockCount 6 = 220
  sigmaRow :
    3 * S.blockCount 3 = 36 + 5 * S.blockCount 5 +
      12 * S.blockCount 6 + twelveFiveSigmaTotal S
  blockRow :
    12 * S.blockCount 4 + 35 * S.blockCount 5 +
      72 * S.blockCount 6 + twelveFiveSigmaTotal S = 624
  totalCircleRow :
    S.totalCircleCount = S.circleCount 3 + S.circleCount 4 +
      S.circleCount 5 + S.circleCount 6
  split3 : S.blockCount 3 = S.lineCount 3 + S.circleCount 3
  split4 : S.blockCount 4 = S.lineCount 4 + S.circleCount 4
  split5 : S.blockCount 5 = S.lineCount 5 + S.circleCount 5
  split6 : S.blockCount 6 = S.lineCount 6 + S.circleCount 6

/-- Triple ownership and the exact summed pivot row give all global rows
used by the six-circle normalization. -/
theorem twelveSixGlobalRows_of_configuration
    {alpha : Type u} [Fintype alpha] [DecidableEq alpha]
    (cfg : Configuration alpha)
    (hcard : Fintype.card alpha = 12)
    (hcap : BlockSizeCap (blockSystem cfg) 6)
    (hcircle : forall c : DeterminedCircle cfg,
      (circleTrace cfg c.1).card <= 6)
    (hsigmaNonneg : forall p : alpha,
      0 <= (blockSystem cfg).pivotSigma p) :
    TwelveSixGlobalRows (blockSystem cfg) := by
  classical
  let S := blockSystem cfg
  have hcircleBlock : forall b,
      S.kind b = .circle -> (S.support b).card <= 6 := by
    intro b hb
    cases b with
    | inl L => cases hb
    | inr c =>
        simpa [S, blockSystem, geometricBlockSystem,
          geometricBlockKind, geometricBlockSupport] using hcircle c
  have hb7 := twelveSix_blockCount_eq_zero_of_cap S hcap
    (s := 7) (by omega)
  have hb8 := twelveSix_blockCount_eq_zero_of_cap S hcap
    (s := 8) (by omega)
  have hb9 := twelveSix_blockCount_eq_zero_of_cap S hcap
    (s := 9) (by omega)
  have hb10 := twelveSix_blockCount_eq_zero_of_cap S hcap
    (s := 10) (by omega)
  have hb11 := twelveSix_blockCount_eq_zero_of_cap S hcap
    (s := 11) (by omega)
  have hb12 := twelveSix_blockCount_eq_zero_of_cap S hcap
    (s := 12) (by omega)
  have hc0 := S.circleCount_eq_zero_of_lt_three (s := 0) (by omega)
  have hc1 := S.circleCount_eq_zero_of_lt_three (s := 1) (by omega)
  have hc2 := S.circleCount_eq_zero_of_lt_three (s := 2) (by omega)
  have hc7 := twelveSix_circleCount_eq_zero_of_cap S hcircleBlock
    (s := 7) (by omega)
  have hc8 := twelveSix_circleCount_eq_zero_of_cap S hcircleBlock
    (s := 8) (by omega)
  have hc9 := twelveSix_circleCount_eq_zero_of_cap S hcircleBlock
    (s := 9) (by omega)
  have hc10 := twelveSix_circleCount_eq_zero_of_cap S hcircleBlock
    (s := 10) (by omega)
  have hc11 := twelveSix_circleCount_eq_zero_of_cap S hcircleBlock
    (s := 11) (by omega)
  have hc12 := twelveSix_circleCount_eq_zero_of_cap S hcircleBlock
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
  have hKcast : (twelveFiveSigmaTotal S : Int) =
      ∑ p : alpha, S.pivotSigma p := by
    exact twelveFiveSigmaTotal_cast S hsigmaNonneg
  have hSigmaZ :
      3 * (S.blockCount 3 : Int) - 5 * (S.blockCount 5 : Int) -
          12 * (S.blockCount 6 : Int) =
        36 + twelveFiveSigmaTotal S := by
    rw [hKcast]
    omega
  have hSigma : 3 * S.blockCount 3 = 36 + 5 * S.blockCount 5 +
      12 * S.blockCount 6 + twelveFiveSigmaTotal S := by
    have hSigmaCleared :
        3 * (S.blockCount 3 : Int) = 36 + 5 * S.blockCount 5 +
          12 * S.blockCount 6 + twelveFiveSigmaTotal S := by
      omega
    exact_mod_cast hSigmaCleared
  have hBlock : 12 * S.blockCount 4 + 35 * S.blockCount 5 +
      72 * S.blockCount 6 + twelveFiveSigmaTotal S = 624 := by
    omega
  have htotal := S.totalCircleCount_eq_sum_circleCount
  rw [hcard] at htotal
  norm_num [Finset.sum_range_succ, hc0, hc1, hc2,
    hc7, hc8, hc9, hc10, hc11, hc12] at htotal
  have hs3 := S.blockCount_eq_lineCount_add_circleCount 3
  have hs4 := S.blockCount_eq_lineCount_add_circleCount 4
  have hs5 := S.blockCount_eq_lineCount_add_circleCount 5
  have hs6 := S.blockCount_eq_lineCount_add_circleCount 6
  exact ⟨hT, hSigma, hBlock, htotal, hs3, hs4, hs5, hs6⟩

end Erdos506.V1
