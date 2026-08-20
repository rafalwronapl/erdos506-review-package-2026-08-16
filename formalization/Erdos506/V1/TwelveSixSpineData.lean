import Erdos506.V1.TwelveSixRows

/-!
# Materialized spine for the twelve-point selected-six-circle branch

This module packages the quotient and circle-count deficits, the exact
block and line identities, and the Gram caps from a concrete configuration.
-/

namespace Erdos506.V1

open Erdos506.Block
open Erdos506.Block.BlockSystem
open Erdos506.Incidence
open Erdos506.V4
open scoped BigOperators

universe u

/-- The selected object is a circle block, not merely an untagged six-block. -/
private theorem one_le_circleCount_six_of_selected_six_circle
    {alpha : Type u} [Fintype alpha] [DecidableEq alpha]
    (cfg : Configuration alpha) (gamma : DeterminedCircle cfg)
    (hgamma : (circleTrace cfg gamma.1).card = 6) :
    1 <= (blockSystem cfg).circleCount 6 := by
  classical
  let S := blockSystem cfg
  let b : GeometricBlock cfg := Sum.inr gamma
  have hb : b ∈ S.circleBlocksOfSize 6 := by
    apply S.mem_blocksOfKindSize.mpr
    constructor
    · rfl
    · simpa [S, b, blockSystem, geometricBlockSystem,
        geometricBlockSupport] using hgamma
  change 1 <= (S.circleBlocksOfSize 6).card
  exact Finset.card_pos.mpr ⟨b, hb⟩

/-! The normalization below is deliberately factored through small
Presburger lemmas.  This keeps `omega` away from the much larger geometric
context of `twelveSixSpine_of_configuration`. -/

private theorem twelveSix_five_count_lt_twelve
    (m k : Nat) (hrich : m + k ≤ 12) (hmpos : 1 ≤ m) : k < 12 := by
  omega

private theorem twelveSix_sigma_mod_twelve
    (b4 k m K : Nat)
    (hB : 12 * b4 + 35 * k + 72 * m + K = 624) :
    K % 12 = k % 12 := by
  omega

private theorem twelveSix_sigma_quotient
    (K k : Nat) (hk : k < 12) (hmod : K % 12 = k % 12) :
    K = k + 12 * (K / 12) := by
  have hdiv := Nat.mod_add_div K 12
  omega

private theorem twelveSix_deficit_eq
    (C : Nat) (hC : C ≤ 50) : 50 - C + C = 50 := by
  omega

private theorem twelveSix_block_three_arithmetic
    (b3 m k K s : Nat)
    (hSigma : 3 * b3 = 36 + 5 * k + 12 * m + K)
    (hK : K = k + 12 * s) :
    b3 = 12 + 4 * m + 2 * k + 4 * s := by
  omega

private theorem twelveSix_block_four_arithmetic
    (b4 m k K s : Nat)
    (hB : 12 * b4 + 35 * k + 72 * m + K = 624)
    (hK : K = k + 12 * s) :
    b4 + 6 * m + 3 * k + s = 52 := by
  omega

private theorem twelveSix_block_total_arithmetic
    (b3 b4 m k s : Nat)
    (hB3 : b3 = 12 + 4 * m + 2 * k + 4 * s)
    (hB4 : b4 + 6 * m + 3 * k + s = 52) :
    b3 + b4 + k + m + m = 64 + 3 * s := by
  omega

private theorem twelveSix_line_total_arithmetic
    (b3 b4 b5 b6 l3 l4 l5 l6 c3 c4 c5 c6 C s e : Nat)
    (hB : b3 + b4 + b5 + b6 + b6 = 64 + 3 * s)
    (hs3 : b3 = l3 + c3) (hs4 : b4 = l4 + c4)
    (hs5 : b5 = l5 + c5) (hs6 : b6 = l6 + c6)
    (hC : C = c3 + c4 + c5 + c6) (he : e + C = 50) :
    l3 + l4 + l5 + l6 + b6 = 14 + 3 * s + e := by
  omega

private theorem twelveSix_kappa_total_arithmetic
    (Q K k m s e l3 l4 l5 l6 : Nat)
    (hsum : Q + 9 * l3 + 16 * l4 + 25 * l5 + 36 * l6 = 132 + K)
    (hK : K = k + 12 * s)
    (hL : l3 + l4 + l5 + l6 + m = 14 + 3 * s + e) :
    Q + 15 * s + 9 * e + 7 * l4 + 16 * l5 + 27 * l6 =
      6 + 9 * m + k := by
  omega

private theorem twelveSix_six_line_strict_arithmetic
    (m r c : Nat) (hsplit : m = r + c) (hc : 1 ≤ c) : r < m := by
  omega

/-- Quotient-normalized universal spine.  Every subtraction in the paper is
cleared to an equality of natural numbers. -/
structure TwelveSixSpine
    {Point Block : Type*} [Fintype Point] [Fintype Block]
    [DecidableEq Point] (S : BlockSystem Point Block) where
  s : Nat
  e : Nat
  globalRows : TwelveSixGlobalRows S
  sigmaQuotient : twelveFiveSigmaTotal S = S.blockCount 5 + 12 * s
  circleDeficit : e + S.totalCircleCount = 50
  blockThree :
    S.blockCount 3 = 12 + 4 * S.blockCount 6 +
      2 * S.blockCount 5 + 4 * s
  blockFour :
    S.blockCount 4 + 6 * S.blockCount 6 +
      3 * S.blockCount 5 + s = 52
  blockTotal :
    S.blockCount 3 + S.blockCount 4 + S.blockCount 5 +
      S.blockCount 6 + S.blockCount 6 = 64 + 3 * s
  lineTotal :
    S.lineCount 3 + S.lineCount 4 + S.lineCount 5 +
      S.lineCount 6 + S.blockCount 6 = 14 + 3 * s + e
  kappaTotal :
    twelveFiveKappaTotal S + 15 * s + 9 * e +
      7 * S.lineCount 4 + 16 * S.lineCount 5 +
      27 * S.lineCount 6 = 6 + 9 * S.blockCount 6 + S.blockCount 5
  richBlockCap : S.blockCount 6 + S.blockCount 5 <= 12
  sixBlockCaps :
    S.blockCount 6 <= 4 /\
      (S.blockCount 6 = 4 -> S.blockCount 5 = 0) /\
      (S.blockCount 6 = 3 -> S.blockCount 5 <= 3) /\
      (S.blockCount 6 = 2 -> S.blockCount 5 <= 8) /\
      (S.blockCount 6 = 1 -> S.blockCount 5 <= 11)
  sixBlockPositive : 1 <= S.blockCount 6
  sixLineStrict : S.lineCount 6 < S.blockCount 6

/-- Materialization of the manuscript's universal six-circle spine from a
concrete selected circle. -/
noncomputable def twelveSixSpine_of_configuration
    {alpha : Type u} [Fintype alpha] [DecidableEq alpha]
    (Mel : RealPlaneMelchiorPrinciple.{u})
    (EvenArr : RealPlaneEvenArrangementPrinciple.{u})
    (Kelly : RealPlaneKellyMoserPrinciple.{u})
    (Gram : RealPlaneTwelveGramPrinciple.{u})
    (cfg : Configuration alpha) (hadm : Admissible cfg)
    (hcard : Fintype.card alpha = 12)
    (hcount : Erdos506.V4.circleCount cfg <= 50)
    (gamma : DeterminedCircle cfg)
    (hgamma : (circleTrace cfg gamma.1).card = 6)
    (hcircle : forall c : DeterminedCircle cfg,
      (circleTrace cfg c.1).card <= 6) :
    TwelveSixSpine (blockSystem cfg) := by
  classical
  let S := blockSystem cfg
  have hcap : BlockSizeCap S 6 := by
    simpa [S] using blockSizeCap_six_of_twelve_six_branch
      cfg hadm hcard hcount hcircle
  have hlocal : forall p : alpha, TwelveFiveLocalRows S p := by
    intro p
    simpa [S] using twelveFiveLocalRows_of_configuration
      Mel EvenArr Kelly Gram cfg hadm hcard hcap p
  have hsigmaNonneg : forall p : alpha, 0 <= S.pivotSigma p :=
    fun p => (hlocal p).sigmaNonneg
  have hkappaNonneg : forall p : alpha, 0 <= S.restoredKappa p :=
    fun p => (hlocal p).kappaNonneg
  have hglobal : TwelveSixGlobalRows S := by
    simpa [S] using twelveSixGlobalRows_of_configuration
      cfg hcard hcap hcircle hsigmaNonneg
  have hmpos : 1 <= S.blockCount 6 := by
    simpa [S] using one_le_blockCount_six_of_selected_six_circle
      cfg gamma hgamma
  have hc6pos : 1 <= S.circleCount 6 := by
    simpa [S] using one_le_circleCount_six_of_selected_six_circle
      cfg gamma hgamma
  have hrich : S.blockCount 6 + S.blockCount 5 <= 12 := by
    simpa [S] using Gram.richBlockCap cfg hadm hcard hcap
  have hcaps : S.blockCount 6 <= 4 /\
      (S.blockCount 6 = 4 -> S.blockCount 5 = 0) /\
      (S.blockCount 6 = 3 -> S.blockCount 5 <= 3) /\
      (S.blockCount 6 = 2 -> S.blockCount 5 <= 8) /\
      (S.blockCount 6 = 1 -> S.blockCount 5 <= 11) := by
    simpa [S] using Gram.sixBlockCaps cfg hadm hcard hcap
  have hklt : S.blockCount 5 < 12 :=
    twelveSix_five_count_lt_twelve
      (S.blockCount 6) (S.blockCount 5) hrich hmpos
  have hmod : twelveFiveSigmaTotal S % 12 = S.blockCount 5 % 12 := by
    exact twelveSix_sigma_mod_twelve
      (S.blockCount 4) (S.blockCount 5) (S.blockCount 6)
        (twelveFiveSigmaTotal S) hglobal.blockRow
  let s := twelveFiveSigmaTotal S / 12
  have hK : twelveFiveSigmaTotal S = S.blockCount 5 + 12 * s := by
    dsimp only [s]
    exact twelveSix_sigma_quotient
      (twelveFiveSigmaTotal S) (S.blockCount 5) hklt hmod
  have htotal : S.totalCircleCount = Erdos506.V4.circleCount cfg := by
    rw [show S = blockSystem cfg by rfl,
      totalCircleCount_eq_card_determinedCircle,
      ← Erdos506.V3.circleCount_eq_card_determinedCircle]
  have hcountS : S.totalCircleCount <= 50 :=
    htotal.le.trans hcount
  let e := 50 - S.totalCircleCount
  have he : e + S.totalCircleCount = 50 := by
    dsimp only [e]
    exact twelveSix_deficit_eq S.totalCircleCount hcountS
  have hB3 : S.blockCount 3 = 12 + 4 * S.blockCount 6 +
      2 * S.blockCount 5 + 4 * s := by
    exact twelveSix_block_three_arithmetic
      (S.blockCount 3) (S.blockCount 6) (S.blockCount 5)
        (twelveFiveSigmaTotal S) s hglobal.sigmaRow hK
  have hB4 : S.blockCount 4 + 6 * S.blockCount 6 +
      3 * S.blockCount 5 + s = 52 := by
    exact twelveSix_block_four_arithmetic
      (S.blockCount 4) (S.blockCount 6) (S.blockCount 5)
        (twelveFiveSigmaTotal S) s hglobal.blockRow hK
  have hBtotal : S.blockCount 3 + S.blockCount 4 + S.blockCount 5 +
      S.blockCount 6 + S.blockCount 6 = 64 + 3 * s := by
    exact twelveSix_block_total_arithmetic
      (S.blockCount 3) (S.blockCount 4) (S.blockCount 6)
        (S.blockCount 5) s hB3 hB4
  have hsplit3 := hglobal.split3
  have hsplit4 := hglobal.split4
  have hsplit5 := hglobal.split5
  have hsplit6 := hglobal.split6
  have hC := hglobal.totalCircleRow
  have hLtotal : S.lineCount 3 + S.lineCount 4 + S.lineCount 5 +
      S.lineCount 6 + S.blockCount 6 = 14 + 3 * s + e := by
    exact twelveSix_line_total_arithmetic
      (S.blockCount 3) (S.blockCount 4) (S.blockCount 5) (S.blockCount 6)
      (S.lineCount 3) (S.lineCount 4) (S.lineCount 5) (S.lineCount 6)
      (S.circleCount 3) (S.circleCount 4) (S.circleCount 5) (S.circleCount 6)
      S.totalCircleCount s e hBtotal hsplit3 hsplit4 hsplit5 hsplit6 hC he
  have hKcast : (twelveFiveSigmaTotal S : Int) =
      ∑ p : alpha, S.pivotSigma p :=
    twelveFiveSigmaTotal_cast S hsigmaNonneg
  have hQcast : (twelveFiveKappaTotal S : Int) =
      ∑ p : alpha, S.restoredKappa p :=
    twelveFiveKappaTotal_cast S hkappaNonneg
  have hsumKappa := twelveFive_sum_kappa_row S hcard hlocal hKcast
  have hsumKappaNat : twelveFiveKappaTotal S +
      9 * S.lineCount 3 + 16 * S.lineCount 4 +
      25 * S.lineCount 5 + 36 * S.lineCount 6 =
        132 + twelveFiveSigmaTotal S := by
    rw [← hQcast] at hsumKappa
    exact_mod_cast hsumKappa
  have hQ : twelveFiveKappaTotal S + 15 * s + 9 * e +
      7 * S.lineCount 4 + 16 * S.lineCount 5 +
      27 * S.lineCount 6 = 6 + 9 * S.blockCount 6 + S.blockCount 5 := by
    exact twelveSix_kappa_total_arithmetic
      (twelveFiveKappaTotal S) (twelveFiveSigmaTotal S)
      (S.blockCount 5) (S.blockCount 6) s e
      (S.lineCount 3) (S.lineCount 4) (S.lineCount 5) (S.lineCount 6)
      hsumKappaNat hK hLtotal
  have hrlt : S.lineCount 6 < S.blockCount 6 := by
    exact twelveSix_six_line_strict_arithmetic
      (S.blockCount 6) (S.lineCount 6) (S.circleCount 6)
        hglobal.split6 hc6pos
  exact ⟨s, e, hglobal, hK, he, hB3, hB4, hBtotal, hLtotal,
    hQ, hrich, hcaps, hmpos, hrlt⟩

end Erdos506.V1
