import Erdos506.V1.TwelveSixUpper

/-!
# Two-six-block lower branch at twelve points

This module contains the two-six-block elimination and shared pointwise certificates.
It imports the cached upper-branch arithmetic but introduces no endpoint
assumption or finite-search callback.
-/

namespace Erdos506.V1

open Erdos506.Block
open Erdos506.Block.BlockSystem
open Erdos506.Incidence
open Erdos506.V4
open scoped BigOperators

universe u

/-- Direction plus the sigma residue, in a form whose sum is the convex
energy bound used in the one- and two-six-block branches. -/
theorem twelveSix_direction_energy_point
    (d5 d6 sigma : Nat) (hd5 : d5 ≤ 8) (hd6 : d6 ≤ 2)
    (hres : (sigma + d5) % 3 = 1)
    (hdir : 0 < d6 -> 2 * d5 + 6 * d6 ≤ sigma + 8) :
    5 * d6 + Nat.choose d6 2 + 4 * d5 ≤
      sigma + Nat.choose d5 2 + 10 := by
  interval_cases d5 <;> interval_cases d6 <;>
    norm_num [Nat.choose] at hres ⊢ <;> omega

/-- The local scalar-defect inequality.  Its sole arithmetic exception is
exactly the Type-A gallery pivot, so the literal gallery principle removes
it without any endpoint premise. -/
theorem twelveSix_rzero_defect_point
    {Point Block : Type*} [Fintype Point] [Fintype Block]
    [DecidableEq Point]
    (S : BlockSystem Point Block) (ctx : TwelveSixBranchContext S)
    (hL6 : S.lineCount 6 = 0) (p : Point)
    (hd5cap : S.blockDegree 5 p ≤ 11) :
    2 * S.blockDegree 5 p ≤
      Nat.choose (S.blockDegree 5 p) 2 + twelveSixSigmaAt S p +
        twelveSixKappaAt S p + S.lineDegree 4 p +
        2 * S.lineDegree 5 p := by
  have hrow := ctx.localRows p
  have hld6 : S.lineDegree 6 p = 0 := by
    have hp := lineDegree_le_lineCount S 6 p
    omega
  by_contra hnot
  have hvals : S.blockDegree 5 p = 3 /\
      twelveSixSigmaAt S p = 1 /\ twelveSixKappaAt S p = 0 /\
      S.lineDegree 4 p = 0 /\ S.lineDegree 5 p = 0 := by
    have hs := hrow.sigmaResidue
    have hk := hrow.kappaResidue
    have hne := hrow.kappaNeOne
    interval_cases hd : S.blockDegree 5 p
    all_goals norm_num [Nat.choose] at hnot
    all_goals omega
  rcases hvals with ⟨hd5, hsigma, hkappa, hl4, hl5⟩
  have hd6 : S.blockDegree 6 p = 0 := by
    by_contra hp
    have hd := ctx.direction hL6 p (by omega)
    rw [hd5, hsigma] at hd
    omega
  have hd3 : S.blockDegree 3 p = 7 := by
    have hs := hrow.sigmaRow
    omega
  have hd4 : S.blockDegree 4 p = 10 := by
    have hr := hrow.richResidueRow
    omega
  have hl3 : S.lineDegree 3 p = 4 := by
    have hk := hrow.kappaRow
    omega
  exact ctx.noTypeA ⟨p, hd3, hd4, hd5, hd6, hl3,
    hl4, hl5, hld6⟩

/-- Certificate for the last `s=0, k=3` rows in the two-six-block branch. -/
private theorem twelveSix_m2_s0_k3_point
    {Point Block : Type*} [Fintype Point] [Fintype Block]
    [DecidableEq Point]
    (S : BlockSystem Point Block) (ctx : TwelveSixBranchContext S)
    (hL6 : S.lineCount 6 = 0) (p : Point)
    (hd5 : S.blockDegree 5 p ≤ 3)
    (hd6 : S.blockDegree 6 p ≤ 2)
    (hl4 : S.lineDegree 4 p ≤ 2)
    (hl5 : S.lineDegree 5 p ≤ 1) :
    10 * S.blockDegree 5 p + 15 * S.blockDegree 6 p +
        3 * twelveSixKappaAt S p + 12 * S.lineDegree 4 p +
        15 * S.lineDegree 5 p + 15 * S.lineDegree 6 p +
        9 * S.lineDegree 3 p ≤
      8 * twelveSixSigmaAt S p + 58 := by
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
  interval_cases S.blockDegree 5 p <;>
    interval_cases S.blockDegree 6 p <;>
    interval_cases S.lineDegree 4 p <;>
    interval_cases S.lineDegree 5 p <;> omega

/-- Certificate for every remaining `s=1` scalar row with two six-blocks. -/
private theorem twelveSix_m2_s1_point
    {Point Block : Type*} [Fintype Point] [Fintype Block]
    [DecidableEq Point]
    (S : BlockSystem Point Block) (ctx : TwelveSixBranchContext S)
    (hL6 : S.lineCount 6 = 0) (p : Point)
    (hd5 : S.blockDegree 5 p ≤ 4)
    (hd6 : S.blockDegree 6 p ≤ 2)
    (hl4 : S.lineDegree 4 p ≤ 1)
    (hl5 : S.lineDegree 5 p = 0) :
    9 * S.blockDegree 5 p + 9 * S.blockDegree 6 p +
        9 * S.lineDegree 5 p + 9 * S.lineDegree 6 p +
        9 * S.lineDegree 3 p ≤
      Nat.choose (S.blockDegree 5 p) 2 +
        3 * Nat.choose (S.blockDegree 5 p + S.blockDegree 6 p) 2 +
        9 * twelveSixSigmaAt S p + 9 * twelveSixKappaAt S p +
        2 * S.lineDegree 4 p + 24 := by
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

/-- Certificate for the possible six-line rows when there are two
six-blocks. -/
private theorem twelveSix_m2_rone_point
    {Point Block : Type*} [Fintype Point] [Fintype Block]
    [DecidableEq Point]
    (S : BlockSystem Point Block) (ctx : TwelveSixBranchContext S)
    (p : Point)
    (hd5 : S.blockDegree 5 p ≤ 8)
    (hd6 : S.blockDegree 6 p ≤ 2)
    (hl4 : S.lineDegree 4 p = 0)
    (hl5 : S.lineDegree 5 p = 0)
    (hl6 : S.lineDegree 6 p ≤ 1) :
    12 ≤ 4 * twelveSixSigmaAt S p +
      3 * twelveSixKappaAt S p + 4 * S.lineDegree 6 p +
      2 * S.lineDegree 3 p := by
  rcases ctx.localRows p with
    ⟨hpair, hsrow, hline, hkrow, hrich, hsres, hkres, hkne, hkelly⟩
  interval_cases S.blockDegree 5 p <;>
    interval_cases S.blockDegree 6 p <;>
    interval_cases S.lineDegree 6 p <;> omega

/-- On the `Q=0` terminal row, the kappa residue restricts `d5` to a
multiple of three; after the pair moment removes degree six, direction has
the following sharp cost. -/
private theorem twelveSix_m2_s2_cost
    (d5 d6 sigma : Nat) (hd5 : d5 ≤ 3) (hd6 : d6 ≤ 2)
    (hmod : d5 % 3 = 0) (hres : (sigma + d5) % 3 = 1)
    (hdir : 0 < d6 -> 2 * d5 + 6 * d6 ≤ sigma + 8) :
    d5 + 3 * d6 ≤ sigma + 2 := by
  interval_cases d5 <;> interval_cases d6 <;> omega

/-- The two residue-compatible values in the range used by the terminal
`k=6` profile already dominate their degree through the pair moment. -/
private theorem twelveSix_m2_mod_three_choose_le
    (d : Nat) (hd : d ≤ 6) (hmod : d % 3 = 0) :
    d ≤ Nat.choose d 2 := by
  interval_cases d <;> norm_num [Nat.choose] at hmod
  all_goals norm_num [Nat.choose]

/-- Equality in the preceding pair-moment bound removes the value six. -/
private theorem twelveSix_m2_mod_three_choose_eq_le_three
    (d : Nat) (hd : d ≤ 6) (hmod : d % 3 = 0)
    (heq : d = Nat.choose d 2) : d ≤ 3 := by
  interval_cases d <;> norm_num [Nat.choose] at hmod
  all_goals norm_num [Nat.choose] at heq
  all_goals norm_num

/-- Two six-blocks contradict the universal spine. -/
theorem twelveSix_two_blocks_impossible
    {Point Block : Type*} [Fintype Point] [Fintype Block]
    [DecidableEq Point]
    (S : BlockSystem Point Block) (ctx : TwelveSixBranchContext S)
    (hm : S.blockCount 6 = 2) : False := by
  classical
  let k := S.blockCount 5
  let h := S.lineCount 4
  let g := S.lineCount 5
  let r := S.lineCount 6
  let K := twelveFiveSigmaTotal S
  let Q := twelveFiveKappaTotal S
  let M5 := ∑ p : Point, Nat.choose (S.blockDegree 5 p) 2
  let M6 := ∑ p : Point, Nat.choose (S.blockDegree 6 p) 2
  let MR := ∑ p : Point,
    Nat.choose (S.blockDegree 5 p + S.blockDegree 6 p) 2
  let X := ∑ p : Point, S.blockDegree 5 p * S.blockDegree 6 p
  have hkcap : k ≤ 8 := by
    dsimp only [k]
    exact ctx.spine.sixBlockCaps.2.2.2.1 hm
  have hsle : ctx.spine.s ≤ 2 := by
    have hQ := ctx.spine.kappaTotal
    change Q + 15 * ctx.spine.s + 9 * ctx.spine.e +
      7 * h + 16 * g + 27 * r =
        6 + 9 * S.blockCount 6 + k at hQ
    omega
  have hrlt : r < 2 := by
    dsimp only [r]
    have hh := ctx.spine.sixLineStrict
    omega
  have hd5cap (p : Point) : S.blockDegree 5 p ≤ k :=
    blockDegree_le_blockCount S 5 p
  have hd6cap (p : Point) : S.blockDegree 6 p ≤ 2 := by
    have hp := blockDegree_le_blockCount S 6 p
    omega
  have hinc5 : (∑ p : Point, S.blockDegree 5 p) = 5 * k := by
    dsimp only [k]
    exact S.block_incidence 5
  have hinc6 : (∑ p : Point, S.blockDegree 6 p) = 12 := by
    have hi := S.block_incidence 6
    rw [hm] at hi
    norm_num at hi
    exact hi
  have hl3inc := S.line_incidence 3
  have hl4inc := S.line_incidence 4
  have hl5inc := S.line_incidence 5
  have hl6inc := S.line_incidence 6
  have hsumSigma : (∑ p : Point, twelveSixSigmaAt S p) = K :=
    twelveSix_sigma_sum S
  have hsumKappa : (∑ p : Point, twelveSixKappaAt S p) = Q :=
    twelveSix_kappa_sum S
  have hK : K = k + 12 * ctx.spine.s := ctx.spine.sigmaQuotient
  have hM5cap : M5 ≤ 2 * Nat.choose k 2 := by
    simpa [M5, k] using ctx.fiveMoment
  have hM6cap : M6 ≤ 2 := by
    have hh := ctx.sixMoment
    rw [hm] at hh
    change M6 ≤ 2 * Nat.choose 2 2 at hh
    norm_num [Nat.choose] at hh
    exact hh
  have hMRcap : MR ≤ 2 * Nat.choose (k + 2) 2 := by
    have hh := ctx.richMoment
    rw [hm] at hh
    simpa [MR, k, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hh
  have hXcap : X ≤ 4 * k := by
    have hh := ctx.crossMoment
    rw [hm] at hh
    change X ≤ 2 * k * 2 at hh
    omega
  have hrcases : r = 0 ∨ r = 1 := by omega
  rcases hrcases with hr0 | hr1
  · have hL6 : S.lineCount 6 = 0 := by simpa [r] using hr0
    have hOrdPoint := ctx.ordinaryVertex hL6
    have hOrd : 36 ≤ 5 * k + 24 + Q + 4 * h + 5 * g := by
      have hh := Finset.sum_le_sum
        (fun p (_hp : p ∈ (Finset.univ : Finset Point)) => hOrdPoint p)
      simp only [Finset.sum_add_distrib, twelveSix_sum_const_mul] at hh
      rw [hinc5, hinc6, hsumKappa, hl4inc, hl5inc] at hh
      simp [ctx.pointCard] at hh
      omega
    have hDefPoint (p : Point) := twelveSix_rzero_defect_point
      S ctx hL6 p (by have hp := (hd5cap p).trans hkcap; omega)
    have hDef : 10 * k ≤ M5 + K + Q + 4 * h + 10 * g := by
      have hh := Finset.sum_le_sum
        (fun p (_hp : p ∈ (Finset.univ : Finset Point)) => hDefPoint p)
      simp only [Finset.sum_add_distrib, twelveSix_sum_const_mul] at hh
      rw [hinc5, hsumSigma, hsumKappa, hl4inc, hl5inc] at hh
      change 2 * (5 * k) ≤ M5 + K + Q + 4 * h + 2 * (5 * g) at hh
      omega
    have hEnergyPoint (p : Point) :
        5 * S.blockDegree 6 p + Nat.choose (S.blockDegree 6 p) 2 +
            4 * S.blockDegree 5 p ≤
          twelveSixSigmaAt S p + Nat.choose (S.blockDegree 5 p) 2 + 10 :=
      twelveSix_direction_energy_point _ _ _
        ((hd5cap p).trans hkcap) (hd6cap p)
        (ctx.localRows p).sigmaResidue
        (fun hp => ctx.direction hL6 p hp)
    have hEnergy : 60 + M6 + 20 * k ≤ K + M5 + 120 := by
      have hh := Finset.sum_le_sum
        (fun p (_hp : p ∈ (Finset.univ : Finset Point)) => hEnergyPoint p)
      simp only [Finset.sum_add_distrib, twelveSix_sum_const_mul] at hh
      rw [hinc6, hinc5, hsumSigma] at hh
      simp [ctx.pointCard] at hh
      change 5 * 12 + M6 + 4 * (5 * k) ≤ K + M5 + 10 * 12 at hh
      omega
    have hscases : ctx.spine.s = 0 ∨ ctx.spine.s = 1 ∨
        ctx.spine.s = 2 := by omega
    rcases hscases with hs0 | hs1 | hs2
    · have hkcases : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by
        interval_cases k <;> norm_num [Nat.choose] at hM5cap <;> omega
      rcases hkcases with hk0 | hk1 | hk2 | hk3
      · have hpoint (p : Point) : 1 ≤
            twelveSixSigmaAt S p + S.blockDegree 5 p := by
          have hr := (ctx.localRows p).sigmaResidue
          omega
        have hsum := Finset.sum_le_sum
          (fun p (_hp : p ∈ (Finset.univ : Finset Point)) => hpoint p)
        rw [Finset.sum_add_distrib, hsumSigma, hinc5] at hsum
        simp [ctx.pointCard] at hsum
        omega
      · have hpoint (p : Point) : 1 ≤
            twelveSixSigmaAt S p + S.blockDegree 5 p := by
          have hr := (ctx.localRows p).sigmaResidue
          omega
        have hsum := Finset.sum_le_sum
          (fun p (_hp : p ∈ (Finset.univ : Finset Point)) => hpoint p)
        rw [Finset.sum_add_distrib, hsumSigma, hinc5] at hsum
        simp [ctx.pointCard] at hsum
        omega
      · have hd5two (p : Point) : S.blockDegree 5 p ≤ 2 := by
          have hp := hd5cap p
          omega
        have hcost (p : Point) :
            1 + 3 * Nat.choose (S.blockDegree 5 p) 2 ≤
              twelveSixSigmaAt S p + S.blockDegree 5 p :=
          twelveSix_sigma_residue_cost_two _ _ (hd5two p)
            (ctx.localRows p).sigmaResidue
        have hsumCost := Finset.sum_le_sum
          (fun p (_hp : p ∈ (Finset.univ : Finset Point)) => hcost p)
        rw [Finset.sum_add_distrib, ← Finset.mul_sum,
          Finset.sum_add_distrib, hsumSigma, hinc5] at hsumCost
        simp [ctx.pointCard] at hsumCost
        have hM5zero : M5 = 0 := by omega
        have hd5one (p : Point) : S.blockDegree 5 p ≤ 1 := by
          have hle : Nat.choose (S.blockDegree 5 p) 2 ≤ M5 := by
            dsimp only [M5]
            exact Finset.single_le_sum
              (fun q _hq => Nat.zero_le (Nat.choose (S.blockDegree 5 q) 2))
              (Finset.mem_univ p)
          have hp := hd5two p
          interval_cases hd : S.blockDegree 5 p
          all_goals norm_num [Nat.choose] at hle
          all_goals omega
        have hsigmaLe (p : Point) : twelveSixSigmaAt S p ≤ 2 := by
          have hle : twelveSixSigmaAt S p ≤ K := by
            rw [← hsumSigma]
            exact Finset.single_le_sum
              (fun q _hq => Nat.zero_le (twelveSixSigmaAt S q))
              (Finset.mem_univ p)
          omega
        have hd6one (p : Point) : S.blockDegree 6 p ≤ 1 := by
          by_contra hp
          have hd := ctx.direction hL6 p (by omega)
          have hs := hsigmaLe p
          omega
        have hd6eq (p : Point) : S.blockDegree 6 p = 1 := by
          have hconst : (∑ p : Point, S.blockDegree 6 p) =
              ∑ _p : Point, 1 := by
            simp [ctx.pointCard, hinc6]
          exact (Finset.sum_eq_sum_iff_of_le
            (fun q _hq => hd6one q)).mp hconst p (Finset.mem_univ p)
        have hXeq : X = 10 := by
          calc
            X = ∑ p : Point, S.blockDegree 5 p := by
              apply Finset.sum_congr rfl
              intro p _hp
              simp [hd6eq p]
            _ = 10 := by simpa [hk2] using hinc5
        omega
      · have hscalar : ctx.spine.e = 0 /\ h ≤ 2 /\ g ≤ 1 := by
          have hQ := ctx.spine.kappaTotal
          change Q + 15 * ctx.spine.s + 9 * ctx.spine.e +
            7 * h + 16 * g + 27 * r =
              6 + 9 * S.blockCount 6 + k at hQ
          have hhcap : h ≤ 3 := by omega
          have hgcap : g ≤ 1 := by omega
          have hM5six : M5 ≤ 6 := by
            have hcap := hM5cap
            rw [hk3] at hcap
            norm_num [Nat.choose] at hcap
            exact hcap
          interval_cases h <;> interval_cases g <;> omega
        rcases hscalar with ⟨he, hh, hg⟩
        have hpoint (p : Point) := twelveSix_m2_s0_k3_point
          S ctx hL6 p ((hd5cap p).trans_eq hk3) (hd6cap p)
          ((lineDegree_le_lineCount S 4 p).trans hh)
          ((lineDegree_le_lineCount S 5 p).trans hg)
        have hsum := Finset.sum_le_sum
          (fun p (_hp : p ∈ (Finset.univ : Finset Point)) => hpoint p)
        simp only [Finset.sum_add_distrib, twelveSix_sum_const_mul] at hsum
        rw [hinc5, hinc6, hsumKappa, hl4inc, hl5inc, hl6inc,
          hl3inc, hsumSigma] at hsum
        simp [ctx.pointCard] at hsum
        change 10 * (5 * k) + 15 * 12 + 3 * Q + 12 * (4 * h) +
          15 * (5 * g) + 15 * (6 * r) + 9 * (3 * S.lineCount 3) ≤
            8 * K + 58 * 12 at hsum
        have hL := ctx.spine.lineTotal
        have hQrow := ctx.spine.kappaTotal
        change S.lineCount 3 + h + g + r + S.blockCount 6 =
          14 + 3 * ctx.spine.s + ctx.spine.e at hL
        change Q + 15 * ctx.spine.s + 9 * ctx.spine.e +
          7 * h + 16 * g + 27 * r =
            6 + 9 * S.blockCount 6 + k at hQrow
        omega
    · have hscalar : 1 ≤ k /\ k ≤ 4 /\ ctx.spine.e = 0 /\
          h ≤ 1 /\ g = 0 := by
        have hQrow := ctx.spine.kappaTotal
        change Q + 15 * ctx.spine.s + 9 * ctx.spine.e +
          7 * h + 16 * g + 27 * r =
            6 + 9 * S.blockCount 6 + k at hQrow
        interval_cases k <;> norm_num [Nat.choose] at hM5cap hMRcap <;> omega
      rcases hscalar with ⟨hkpos, hkle, he, hh, hg⟩
      have hld5 (p : Point) : S.lineDegree 5 p = 0 := by
        have hp := lineDegree_le_lineCount S 5 p
        dsimp only [g] at hg
        omega
      have hpoint (p : Point) := twelveSix_m2_s1_point
        S ctx hL6 p ((hd5cap p).trans hkle) (hd6cap p)
        ((lineDegree_le_lineCount S 4 p).trans hh) (hld5 p)
      have hsum := Finset.sum_le_sum
        (fun p (_hp : p ∈ (Finset.univ : Finset Point)) => hpoint p)
      simp only [Finset.sum_add_distrib, twelveSix_sum_const_mul] at hsum
      rw [hinc5, hinc6, hl5inc, hl6inc, hl3inc, hsumSigma,
        hsumKappa, hl4inc] at hsum
      simp [ctx.pointCard] at hsum
      change 9 * (5 * k) + 9 * 12 + 9 * (5 * g) + 9 * (6 * r) +
        9 * (3 * S.lineCount 3) ≤
          M5 + 3 * MR + 9 * K + 9 * Q + 2 * (4 * h) + 24 * 12 at hsum
      have hL := ctx.spine.lineTotal
      have hQrow := ctx.spine.kappaTotal
      change S.lineCount 3 + h + g + r + S.blockCount 6 =
        14 + 3 * ctx.spine.s + ctx.spine.e at hL
      change Q + 15 * ctx.spine.s + 9 * ctx.spine.e +
        7 * h + 16 * g + 27 * r =
          6 + 9 * S.blockCount 6 + k at hQrow
      interval_cases k <;> norm_num [Nat.choose] at hM5cap hMRcap <;> omega
    · have hscalar : k = 6 /\ ctx.spine.e = 0 /\ h = 0 /\
          g = 0 /\ Q = 0 := by
        have hQrow := ctx.spine.kappaTotal
        change Q + 15 * ctx.spine.s + 9 * ctx.spine.e +
          7 * h + 16 * g + 27 * r =
            6 + 9 * S.blockCount 6 + k at hQrow
        interval_cases k <;> norm_num [Nat.choose] at hM5cap <;> omega
      rcases hscalar with ⟨hk6, he, hh, hg, hQ0⟩
      have hkappa0 (p : Point) : twelveSixKappaAt S p = 0 := by
        have hp : twelveSixKappaAt S p ≤ Q := by
          rw [← hsumKappa]
          exact Finset.single_le_sum
            (fun q _hq => Nat.zero_le (twelveSixKappaAt S q))
            (Finset.mem_univ p)
        omega
      have hld4 (p : Point) : S.lineDegree 4 p = 0 := by
        have hp := lineDegree_le_lineCount S 4 p
        dsimp only [h] at hh
        omega
      have hld5 (p : Point) : S.lineDegree 5 p = 0 := by
        have hp := lineDegree_le_lineCount S 5 p
        dsimp only [g] at hg
        omega
      have hd5mod (p : Point) : S.blockDegree 5 p % 3 = 0 := by
        have hr := (ctx.localRows p).kappaResidue
        rw [hkappa0 p, hld4 p, hld5 p] at hr
        simpa using hr
      have hchoose (p : Point) :
          S.blockDegree 5 p ≤ Nat.choose (S.blockDegree 5 p) 2 := by
        have hp : S.blockDegree 5 p ≤ 6 := (hd5cap p).trans_eq hk6
        have hm := hd5mod p
        exact twelveSix_m2_mod_three_choose_le _ hp hm
      have hM5lower : 30 ≤ M5 := by
        have hs := Finset.sum_le_sum
          (fun p (_hp : p ∈ (Finset.univ : Finset Point)) => hchoose p)
        rw [hinc5, hk6] at hs
        change 30 ≤ M5 at hs
        exact hs
      have hM5 : M5 = 30 := by
        norm_num [hk6, Nat.choose] at hM5cap
        omega
      have hchooseEq (p : Point) :
          S.blockDegree 5 p = Nat.choose (S.blockDegree 5 p) 2 := by
        have heq : (∑ p : Point, S.blockDegree 5 p) =
            ∑ p : Point, Nat.choose (S.blockDegree 5 p) 2 := by
          rw [hinc5, hk6]
          change 30 = M5
          exact hM5.symm
        exact (Finset.sum_eq_sum_iff_of_le
          (fun q _hq => hchoose q)).mp heq p (Finset.mem_univ p)
      have hd5three (p : Point) : S.blockDegree 5 p ≤ 3 := by
        have hp : S.blockDegree 5 p ≤ 6 := (hd5cap p).trans_eq hk6
        have heq := hchooseEq p
        have hmod := hd5mod p
        exact twelveSix_m2_mod_three_choose_eq_le_three _ hp hmod heq
      have hcost (p : Point) :
          S.blockDegree 5 p + 3 * S.blockDegree 6 p ≤
            twelveSixSigmaAt S p + 2 :=
        twelveSix_m2_s2_cost _ _ _ (hd5three p) (hd6cap p)
          (hd5mod p) (ctx.localRows p).sigmaResidue
          (fun hp => ctx.direction hL6 p hp)
      have hsum := Finset.sum_le_sum
        (fun p (_hp : p ∈ (Finset.univ : Finset Point)) => hcost p)
      rw [Finset.sum_add_distrib, ← Finset.mul_sum,
        hinc5, hinc6, Finset.sum_add_distrib, hsumSigma] at hsum
      simp [ctx.pointCard] at hsum
      omega
  · have hscalar : ctx.spine.s = 0 /\ ctx.spine.e = 0 /\
        h = 0 /\ g = 0 := by
      have hQrow := ctx.spine.kappaTotal
      change Q + 15 * ctx.spine.s + 9 * ctx.spine.e +
        7 * h + 16 * g + 27 * r =
          6 + 9 * S.blockCount 6 + k at hQrow
      omega
    rcases hscalar with ⟨hs0, he, hh, hg⟩
    have hld4 (p : Point) : S.lineDegree 4 p = 0 := by
      have hp := lineDegree_le_lineCount S 4 p
      dsimp only [h] at hh
      omega
    have hld5 (p : Point) : S.lineDegree 5 p = 0 := by
      have hp := lineDegree_le_lineCount S 5 p
      dsimp only [g] at hg
      omega
    have hpoint (p : Point) := twelveSix_m2_rone_point
      S ctx p ((hd5cap p).trans hkcap) (hd6cap p)
      (hld4 p) (hld5 p)
      ((lineDegree_le_lineCount S 6 p).trans_eq (by simpa [r] using hr1))
    have hsum := Finset.sum_le_sum
      (fun p (_hp : p ∈ (Finset.univ : Finset Point)) => hpoint p)
    simp only [Finset.sum_add_distrib, twelveSix_sum_const_mul] at hsum
    rw [hsumSigma, hsumKappa, hl6inc, hl3inc] at hsum
    simp [ctx.pointCard] at hsum
    change 12 * 12 ≤ 4 * K + 3 * Q + 4 * (6 * r) +
      2 * (3 * S.lineCount 3) at hsum
    have hL := ctx.spine.lineTotal
    have hQrow := ctx.spine.kappaTotal
    change S.lineCount 3 + h + g + r + S.blockCount 6 =
      14 + 3 * ctx.spine.s + ctx.spine.e at hL
    change Q + 15 * ctx.spine.s + 9 * ctx.spine.e +
      7 * h + 16 * g + 27 * r =
        6 + 9 * S.blockCount 6 + k at hQrow
    omega

end Erdos506.V1

