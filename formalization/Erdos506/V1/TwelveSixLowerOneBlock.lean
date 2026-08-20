import Erdos506.V1.TwelveSixLowerTwoBlocks

/-!
# One-six-block lower branch at twelve points

This module contains the one-six-block elimination. It imports the shared
lower-branch pointwise certificates and the completed two-block branch.
-/

namespace Erdos506.V1

open Erdos506.Block
open Erdos506.Block.BlockSystem
open Erdos506.Incidence
open Erdos506.V4
open scoped BigOperators

universe u

/-- First clean-core certificate for `s=1`.  The single arithmetic
exception is the literal Type-A gallery pivot. -/
private theorem twelveSix_m1_clean_point_one
    {Point Block : Type*} [Fintype Point] [Fintype Block]
    [DecidableEq Point]
    (S : BlockSystem Point Block) (ctx : TwelveSixBranchContext S)
    (hL6 : S.lineCount 6 = 0) (p : Point)
    (hd5 : S.blockDegree 5 p ≤ 7)
    (hd6 : S.blockDegree 6 p ≤ 1)
    (hl4 : S.lineDegree 4 p ≤ 1)
    (hl5 : S.lineDegree 5 p = 0) :
    7 * S.blockDegree 5 p + 6 * S.lineDegree 3 p ≤
      3 * Nat.choose (S.blockDegree 5 p) 2 +
        7 * twelveSixSigmaAt S p + 7 * twelveSixKappaAt S p +
        S.lineDegree 4 p + 14 := by
  rcases ctx.localRows p with
    ⟨hpair, hsrow, hline, hkrow, hrich, hsres, hkres, hkne, hkelly⟩
  have hld6 : S.lineDegree 6 p = 0 := by
    have hp := lineDegree_le_lineCount S 6 p
    omega
  have hdir : S.blockDegree 6 p = 0 ∨
      2 * S.blockDegree 5 p + 6 * S.blockDegree 6 p ≤
        twelveSixSigmaAt S p + 8 := by
    by_cases hz : S.blockDegree 6 p = 0
    · exact Or.inl hz
    · exact Or.inr (ctx.direction hL6 p (by omega))
  have hord := ctx.ordinaryVertex hL6 p
  by_contra hnot
  have hvals : S.blockDegree 3 p = 7 /\
      S.blockDegree 4 p = 10 /\ S.blockDegree 5 p = 3 /\
      S.blockDegree 6 p = 0 /\ S.lineDegree 3 p = 4 /\
      S.lineDegree 4 p = 0 := by
    interval_cases S.blockDegree 5 p <;>
      interval_cases S.blockDegree 6 p <;>
      interval_cases S.lineDegree 4 p <;>
      norm_num [Nat.choose] at hnot ⊢ <;> omega
  rcases hvals with ⟨hd3, hd4, hd5eq, hd6eq, hl3, hl4eq⟩
  exact ctx.noTypeA ⟨p, hd3, hd4, hd5eq, hd6eq, hl3,
    hl4eq, hl5, hld6⟩

/-- Second clean-core certificate for `s=1`. -/
private theorem twelveSix_m1_clean_point_two
    {Point Block : Type*} [Fintype Point] [Fintype Block]
    [DecidableEq Point]
    (S : BlockSystem Point Block) (ctx : TwelveSixBranchContext S)
    (hL6 : S.lineCount 6 = 0) (p : Point)
    (hd5 : S.blockDegree 5 p ≤ 7)
    (hd6 : S.blockDegree 6 p ≤ 1)
    (hl4 : S.lineDegree 4 p ≤ 1)
    (hl5 : S.lineDegree 5 p = 0) :
    9 * S.blockDegree 5 p + 9 * S.blockDegree 6 p +
        twelveSixKappaAt S p + 9 * S.lineDegree 4 p +
        6 * S.lineDegree 3 p ≤
      2 * Nat.choose (S.blockDegree 5 p) 2 +
        4 * twelveSixSigmaAt S p + 44 := by
  rcases ctx.localRows p with
    ⟨hpair, hsrow, hline, hkrow, hrich, hsres, hkres, hkne, hkelly⟩
  have hdir : S.blockDegree 6 p = 0 ∨
      2 * S.blockDegree 5 p + 6 * S.blockDegree 6 p ≤
        twelveSixSigmaAt S p + 8 := by
    by_cases hz : S.blockDegree 6 p = 0
    · exact Or.inl hz
    · exact Or.inr (ctx.direction hL6 p (by omega))
  have hord := ctx.ordinaryVertex hL6 p
  interval_cases S.blockDegree 5 p <;>
    interval_cases S.blockDegree 6 p <;>
    interval_cases S.lineDegree 4 p <;>
    norm_num [Nat.choose] <;> omega

/-- One six-block contradicts the universal spine.  The proof uses only
summed local certificates and the ordinary-direction row; no footprint
classification or finite realization search is needed. -/
theorem twelveSix_one_block_impossible
    {Point Block : Type*} [Fintype Point] [Fintype Block]
    [DecidableEq Point]
    (S : BlockSystem Point Block) (ctx : TwelveSixBranchContext S)
    (hm : S.blockCount 6 = 1) : False := by
  classical
  let k := S.blockCount 5
  let h := S.lineCount 4
  let g := S.lineCount 5
  let r := S.lineCount 6
  let K := twelveFiveSigmaTotal S
  let Q := twelveFiveKappaTotal S
  let M5 := ∑ p : Point, Nat.choose (S.blockDegree 5 p) 2
  have hkcap : k ≤ 11 := by
    dsimp only [k]
    exact ctx.spine.sixBlockCaps.2.2.2.2 hm
  have hsle : ctx.spine.s ≤ 1 := by
    have hQ := ctx.spine.kappaTotal
    change Q + 15 * ctx.spine.s + 9 * ctx.spine.e +
      7 * h + 16 * g + 27 * r =
        6 + 9 * S.blockCount 6 + k at hQ
    omega
  have hr0 : r = 0 := by
    have hh := ctx.spine.sixLineStrict
    dsimp only [r]
    omega
  have hL6 : S.lineCount 6 = 0 := by simpa [r] using hr0
  have hd5cap (p : Point) : S.blockDegree 5 p ≤ k :=
    blockDegree_le_blockCount S 5 p
  have hd5seven (p : Point) : S.blockDegree 5 p ≤ 7 := by
    have hr := (ctx.localRows p).richResidueRow
    omega
  have hd6cap (p : Point) : S.blockDegree 6 p ≤ 1 := by
    have hp := blockDegree_le_blockCount S 6 p
    omega
  have hinc5 : (∑ p : Point, S.blockDegree 5 p) = 5 * k := by
    dsimp only [k]
    exact S.block_incidence 5
  have hinc6 : (∑ p : Point, S.blockDegree 6 p) = 6 := by
    have hi := S.block_incidence 6
    rw [hm] at hi
    norm_num at hi
    exact hi
  have hl3inc := S.line_incidence 3
  have hl4inc := S.line_incidence 4
  have hl5inc := S.line_incidence 5
  have hsumSigma : (∑ p : Point, twelveSixSigmaAt S p) = K :=
    twelveSix_sigma_sum S
  have hsumKappa : (∑ p : Point, twelveSixKappaAt S p) = Q :=
    twelveSix_kappa_sum S
  have hK : K = k + 12 * ctx.spine.s := ctx.spine.sigmaQuotient
  have hM5cap : M5 ≤ 2 * Nat.choose k 2 := by
    simpa [M5, k] using ctx.fiveMoment
  have hOrdPoint := ctx.ordinaryVertex hL6
  have hOrd : 36 ≤ 5 * k + 12 + Q + 4 * h + 5 * g := by
    have hh := Finset.sum_le_sum
      (fun p (_hp : p ∈ (Finset.univ : Finset Point)) => hOrdPoint p)
    simp only [Finset.sum_add_distrib, twelveSix_sum_const_mul] at hh
    rw [hinc5, hinc6, hsumKappa, hl4inc, hl5inc] at hh
    simp [ctx.pointCard] at hh
    omega
  have hDefPoint (p : Point) := twelveSix_rzero_defect_point
    S ctx hL6 p (by have hp := hd5cap p; omega)
  have hDef : 10 * k ≤ M5 + K + Q + 4 * h + 10 * g := by
    have hh := Finset.sum_le_sum
      (fun p (_hp : p ∈ (Finset.univ : Finset Point)) => hDefPoint p)
    simp only [Finset.sum_add_distrib, twelveSix_sum_const_mul] at hh
    rw [hinc5, hsumSigma, hsumKappa, hl4inc, hl5inc] at hh
    change 2 * (5 * k) ≤ M5 + K + Q + 4 * h + 2 * (5 * g) at hh
    omega
  have hEnergyPoint (p : Point) :
      5 * S.blockDegree 6 p + 4 * S.blockDegree 5 p ≤
        twelveSixSigmaAt S p + Nat.choose (S.blockDegree 5 p) 2 + 10 := by
    have hh := twelveSix_direction_energy_point
      (S.blockDegree 5 p) (S.blockDegree 6 p) (twelveSixSigmaAt S p)
      (by have hp := hd5seven p; omega) (by have hp := hd6cap p; omega)
      (ctx.localRows p).sigmaResidue (fun hp => ctx.direction hL6 p hp)
    have hz : Nat.choose (S.blockDegree 6 p) 2 = 0 := by
      have hp := hd6cap p
      interval_cases hd : S.blockDegree 6 p <;> norm_num [Nat.choose]
    omega
  have hEnergy : 30 + 20 * k ≤ K + M5 + 120 := by
    have hh := Finset.sum_le_sum
      (fun p (_hp : p ∈ (Finset.univ : Finset Point)) => hEnergyPoint p)
    simp only [Finset.sum_add_distrib, twelveSix_sum_const_mul] at hh
    rw [hinc6, hinc5, hsumSigma] at hh
    simp [ctx.pointCard] at hh
    change 5 * 6 + 4 * (5 * k) ≤ K + M5 + 10 * 12 at hh
    omega
  by_cases hg0 : g = 0
  · have hld5 (p : Point) : S.lineDegree 5 p = 0 := by
      have hp := lineDegree_le_lineCount S 5 p
      dsimp only [g] at hg0
      omega
    have hAPoint (p : Point) :
        3 ≤ S.blockDegree 5 p + twelveSixKappaAt S p +
          S.lineDegree 4 p := by
      have hord := hOrdPoint p
      have hres := (ctx.localRows p).kappaResidue
      rw [hld5 p] at hord hres
      have hd := hd6cap p
      omega
    have hA : 36 ≤ 5 * k + Q + 4 * h := by
      have hh := Finset.sum_le_sum
        (fun p (_hp : p ∈ (Finset.univ : Finset Point)) => hAPoint p)
      simp only [Finset.sum_add_distrib] at hh
      rw [hinc5, hsumKappa, hl4inc] at hh
      simpa [ctx.pointCard] using hh
    have hscases : ctx.spine.s = 0 ∨ ctx.spine.s = 1 := by omega
    rcases hscases with hs0 | hs1
    · have hQrow := ctx.spine.kappaTotal
      change Q + 15 * ctx.spine.s + 9 * ctx.spine.e +
        7 * h + 16 * g + 27 * r =
          6 + 9 * S.blockCount 6 + k at hQrow
      interval_cases k <;> norm_num [Nat.choose] at hM5cap <;> omega
    · have hhcap : h ≤ 1 := by
        have hQrow := ctx.spine.kappaTotal
        change Q + 15 * ctx.spine.s + 9 * ctx.spine.e +
          7 * h + 16 * g + 27 * r =
            6 + 9 * S.blockCount 6 + k at hQrow
        omega
      have hCpoint (p : Point) := twelveSix_m1_clean_point_one
        S ctx hL6 p (hd5seven p) (hd6cap p)
        ((lineDegree_le_lineCount S 4 p).trans hhcap) (hld5 p)
      have hC := Finset.sum_le_sum
        (fun p (_hp : p ∈ (Finset.univ : Finset Point)) => hCpoint p)
      simp only [Finset.sum_add_distrib, twelveSix_sum_const_mul] at hC
      rw [hinc5, hl3inc, hsumSigma, hsumKappa, hl4inc] at hC
      simp [ctx.pointCard] at hC
      change 7 * (5 * k) + 6 * (3 * S.lineCount 3) ≤
        3 * M5 + 7 * K + 7 * Q + 4 * h + 14 * 12 at hC
      have hDpoint (p : Point) := twelveSix_m1_clean_point_two
        S ctx hL6 p (hd5seven p) (hd6cap p)
        ((lineDegree_le_lineCount S 4 p).trans hhcap) (hld5 p)
      have hD := Finset.sum_le_sum
        (fun p (_hp : p ∈ (Finset.univ : Finset Point)) => hDpoint p)
      simp only [Finset.sum_add_distrib, twelveSix_sum_const_mul] at hD
      rw [hinc5, hinc6, hsumKappa, hl4inc, hl3inc, hsumSigma] at hD
      simp [ctx.pointCard] at hD
      change 9 * (5 * k) + 9 * 6 + Q + 9 * (4 * h) +
        6 * (3 * S.lineCount 3) ≤ 2 * M5 + 4 * K + 44 * 12 at hD
      have hL := ctx.spine.lineTotal
      have hQrow := ctx.spine.kappaTotal
      change S.lineCount 3 + h + g + r + S.blockCount 6 =
        14 + 3 * ctx.spine.s + ctx.spine.e at hL
      change Q + 15 * ctx.spine.s + 9 * ctx.spine.e +
        7 * h + 16 * g + 27 * r =
          6 + 9 * S.blockCount 6 + k at hQrow
      interval_cases k <;> norm_num [Nat.choose] at hM5cap <;> omega
  · have hQrow := ctx.spine.kappaTotal
    change Q + 15 * ctx.spine.s + 9 * ctx.spine.e +
      7 * h + 16 * g + 27 * r =
        6 + 9 * S.blockCount 6 + k at hQrow
    interval_cases k <;> interval_cases ctx.spine.s <;>
      norm_num [Nat.choose] at hM5cap <;> omega

end Erdos506.V1

