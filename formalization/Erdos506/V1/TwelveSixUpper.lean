import Erdos506.V1.TwelveSixCore

/-!
# Upper six-block branches at twelve points

This module contains the complete eliminations for three and four
six-blocks, together with the small arithmetic helpers shared downstream.
-/

namespace Erdos506.V1

open Erdos506.Block
open Erdos506.Block.BlockSystem
open Erdos506.Incidence
open Erdos506.V4
open scoped BigOperators

universe u

/-- The two natural local slacks sum to the totals already used by the
universal spine. -/
theorem twelveSix_sigma_sum
    {Point Block : Type*} [Fintype Point] [Fintype Block]
    [DecidableEq Point]
    (S : BlockSystem Point Block) :
    (∑ p : Point, twelveSixSigmaAt S p) = twelveFiveSigmaTotal S := by
  rfl

theorem twelveSix_kappa_sum
    {Point Block : Type*} [Fintype Point] [Fintype Block]
    [DecidableEq Point]
    (S : BlockSystem Point Block) :
    (∑ p : Point, twelveSixKappaAt S p) = twelveFiveKappaTotal S := by
  rfl

/-- A bounded version of the elementary identity
`choose (a+b) 2 = choose a 2 + choose b 2 + a*b`.  The only consumers have
`a ≤ 8`, `b ≤ 4`; spelling out that tiny range keeps all later arithmetic
in Presburger form. -/
private theorem twelveSix_choose_add_two
    (a b : Nat) (ha : a ≤ 8) (hb : b ≤ 4) :
    Nat.choose (a + b) 2 =
      Nat.choose a 2 + Nat.choose b 2 + a * b := by
  interval_cases a <;> interval_cases b <;> norm_num [Nat.choose]

/-- Normalize a pointwise constant multiple after summation. -/
theorem twelveSix_sum_const_mul
    {Point : Type*} [Fintype Point] (c : Nat) (f : Point → Nat) :
    (∑ p : Point, c * f p) = c * ∑ p : Point, f p := by
  rw [Finset.mul_sum]

/-- The balanced six-degree row for four six-blocks. -/
private theorem twelveSix_four_blocks_degree_eq_two
    {Point Block : Type*} [Fintype Point] [Fintype Block]
    [DecidableEq Point]
    (S : BlockSystem Point Block) (hcard : Fintype.card Point = 12)
    (hm : S.blockCount 6 = 4)
    (hmoment : (∑ p : Point, Nat.choose (S.blockDegree 6 p) 2) ≤
      2 * Nat.choose (S.blockCount 6) 2) :
    ∀ p : Point, S.blockDegree 6 p = 2 := by
  have hinc := S.block_incidence 6
  rw [hm] at hinc hmoment
  norm_num [Nat.choose] at hinc hmoment
  have hcap (p : Point) : S.blockDegree 6 p ≤ 4 :=
    (blockDegree_le_blockCount S 6 p).trans_eq hm
  have hpoint (p : Point) :
      2 * S.blockDegree 6 p ≤ 3 + Nat.choose (S.blockDegree 6 p) 2 := by
    have hp := hcap p
    interval_cases S.blockDegree 6 p <;> norm_num [Nat.choose]
  have hsumLe :
      (∑ p : Point, 2 * S.blockDegree 6 p) ≤
        ∑ p : Point, (3 + Nat.choose (S.blockDegree 6 p) 2) :=
    Finset.sum_le_sum fun p _hp => hpoint p
  have hleft : (∑ p : Point, 2 * S.blockDegree 6 p) = 48 := by
    rw [← Finset.mul_sum, hinc]
    norm_num
  have hright : (∑ p : Point,
      (3 + Nat.choose (S.blockDegree 6 p) 2)) ≤ 48 := by
    rw [Finset.sum_add_distrib]
    have hthree : (∑ _p : Point, 3) = 36 := by simp [hcard]
    rw [hthree]
    omega
  have heq : (∑ p : Point, 2 * S.blockDegree 6 p) =
      ∑ p : Point, (3 + Nat.choose (S.blockDegree 6 p) 2) := by
    omega
  have hterm (p : Point) :
      2 * S.blockDegree 6 p =
        3 + Nat.choose (S.blockDegree 6 p) 2 :=
    (Finset.sum_eq_sum_iff_of_le
      (fun q _hq => hpoint q)).mp heq p (Finset.mem_univ p)
  have hge (p : Point) : 2 ≤ S.blockDegree 6 p := by
    have hp := hcap p
    have ht := hterm p
    interval_cases hd : S.blockDegree 6 p
    all_goals norm_num [Nat.choose] at ht
    all_goals omega
  have hconst : (∑ _p : Point, 2) = 24 := by simp [hcard]
  have hallEq : (∑ _p : Point, 2) =
      ∑ p : Point, S.blockDegree 6 p := by omega
  intro p
  exact ((Finset.sum_eq_sum_iff_of_le
    (fun q _hq => hge q)).mp hallEq p (Finset.mem_univ p)).symm

/-- The corresponding balanced row for three six-blocks: every point has
six-degree one or two. -/
private theorem twelveSix_three_blocks_degree_one_or_two
    {Point Block : Type*} [Fintype Point] [Fintype Block]
    [DecidableEq Point]
    (S : BlockSystem Point Block) (hcard : Fintype.card Point = 12)
    (hm : S.blockCount 6 = 3)
    (hmoment : (∑ p : Point, Nat.choose (S.blockDegree 6 p) 2) ≤
      2 * Nat.choose (S.blockCount 6) 2) :
    ∀ p : Point, S.blockDegree 6 p = 1 ∨ S.blockDegree 6 p = 2 := by
  have hinc := S.block_incidence 6
  rw [hm] at hinc hmoment
  norm_num at hinc hmoment
  have hcap (p : Point) : S.blockDegree 6 p ≤ 3 :=
    (blockDegree_le_blockCount S 6 p).trans_eq hm
  have hpoint (p : Point) : S.blockDegree 6 p ≤
      1 + Nat.choose (S.blockDegree 6 p) 2 := by
    have hp := hcap p
    interval_cases S.blockDegree 6 p <;> norm_num [Nat.choose]
  have hsumLe : (∑ p : Point, S.blockDegree 6 p) ≤
      ∑ p : Point, (1 + Nat.choose (S.blockDegree 6 p) 2) :=
    Finset.sum_le_sum fun p _hp => hpoint p
  have hright : (∑ p : Point,
      (1 + Nat.choose (S.blockDegree 6 p) 2)) ≤ 18 := by
    rw [Finset.sum_add_distrib]
    have hone : (∑ _p : Point, 1) = 12 := by simp [hcard]
    rw [hone]
    omega
  have heq : (∑ p : Point, S.blockDegree 6 p) =
      ∑ p : Point, (1 + Nat.choose (S.blockDegree 6 p) 2) := by
    omega
  intro p
  have ht := (Finset.sum_eq_sum_iff_of_le
    (fun q _hq => hpoint q)).mp heq p (Finset.mem_univ p)
  have hp := hcap p
  interval_cases hd : S.blockDegree 6 p
  all_goals norm_num [Nat.choose] at ht
  all_goals omega

/-- Four six-blocks contradict the universal spine. -/
theorem twelveSix_four_blocks_impossible
    {Point Block : Type*} [Fintype Point] [Fintype Block]
    [DecidableEq Point]
    (S : BlockSystem Point Block) (ctx : TwelveSixBranchContext S)
    (hm : S.blockCount 6 = 4) : False := by
  classical
  let k := S.blockCount 5
  let h := S.lineCount 4
  let g := S.lineCount 5
  let r := S.lineCount 6
  let K := twelveFiveSigmaTotal S
  let Q := twelveFiveKappaTotal S
  have hk : k = 0 := by
    dsimp only [k]
    exact ctx.spine.sixBlockCaps.2.1 hm
  have hd6 (p : Point) : S.blockDegree 6 p = 2 :=
    twelveSix_four_blocks_degree_eq_two S ctx.pointCard hm ctx.sixMoment p
  have hd5 (p : Point) : S.blockDegree 5 p = 0 := by
    have hle := blockDegree_le_blockCount S 5 p
    dsimp only [k] at hk
    omega
  have hsigmaOne (p : Point) : 1 ≤ twelveSixSigmaAt S p := by
    have hr := (ctx.localRows p).sigmaResidue
    rw [hd5 p] at hr
    omega
  have hsumSigma : (∑ p : Point, twelveSixSigmaAt S p) = K := by
    exact twelveSix_sigma_sum S
  have hK : K = k + 12 * ctx.spine.s := ctx.spine.sigmaQuotient
  have hsge : 1 ≤ ctx.spine.s := by
    have hsumLower : (∑ _p : Point, 1) ≤
        ∑ p : Point, twelveSixSigmaAt S p :=
      Finset.sum_le_sum fun p _hp => hsigmaOne p
    simp [ctx.pointCard] at hsumLower
    omega
  have hsle : ctx.spine.s ≤ 2 := by
    have hQ := ctx.spine.kappaTotal
    change Q + 15 * ctx.spine.s + 9 * ctx.spine.e +
      7 * h + 16 * g + 27 * r =
        6 + 9 * S.blockCount 6 + k at hQ
    omega
  have hrange : r = 0 ∨ r = 1 := by
    have hrlt := ctx.spine.sixLineStrict
    have hQrow := ctx.spine.kappaTotal
    change Q + 15 * ctx.spine.s + 9 * ctx.spine.e +
      7 * h + 16 * g + 27 * r =
        6 + 9 * S.blockCount 6 + k at hQrow
    dsimp only [r]
    omega
  rcases hrange with hr0 | hr1
  · have hsigFour (p : Point) : 4 ≤ twelveSixSigmaAt S p := by
      have hd := ctx.direction (by simpa [r] using hr0) p (by rw [hd6 p]; omega)
      rw [hd5 p, hd6 p] at hd
      omega
    have hsumLower : (∑ _p : Point, 4) ≤
        ∑ p : Point, twelveSixSigmaAt S p :=
      Finset.sum_le_sum fun p _hp => hsigFour p
    simp [ctx.pointCard] at hsumLower
    omega
  · have hscalar : ctx.spine.s = 1 /\ ctx.spine.e = 0 /\
        h = 0 /\ g = 0 /\ Q = 0 := by
      have hQ := ctx.spine.kappaTotal
      change Q + 15 * ctx.spine.s + 9 * ctx.spine.e +
        7 * h + 16 * g + 27 * r =
          6 + 9 * S.blockCount 6 + k at hQ
      omega
    rcases hscalar with ⟨hs, he, hh, hg, hQzero⟩
    have hsigmaEq (p : Point) : twelveSixSigmaAt S p = 1 := by
      have hsumOne : (∑ _p : Point, 1) =
          ∑ p : Point, twelveSixSigmaAt S p := by
        simp [ctx.pointCard, hsumSigma, hK, hk, hs]
      exact ((Finset.sum_eq_sum_iff_of_le
        (fun q _hq => hsigmaOne q)).mp hsumOne p
          (Finset.mem_univ p)).symm
    have hkappaEq (p : Point) : twelveSixKappaAt S p = 0 := by
      have hle : twelveSixKappaAt S p ≤ Q := by
        dsimp only [Q]
        rw [← twelveSix_kappa_sum S]
        exact Finset.single_le_sum
          (fun q _hq => Nat.zero_le (twelveSixKappaAt S q))
          (Finset.mem_univ p)
      omega
    have hld4 (p : Point) : S.lineDegree 4 p = 0 := by
      have hle := lineDegree_le_lineCount S 4 p
      dsimp only [h] at hh
      omega
    have hld5 (p : Point) : S.lineDegree 5 p = 0 := by
      have hle := lineDegree_le_lineCount S 5 p
      dsimp only [g] at hg
      omega
    have hoff : exists p : Point, S.lineDegree 6 p = 0 := by
      by_contra hn
      push Not at hn
      have hlower : (∑ _p : Point, 1) ≤
          ∑ p : Point, S.lineDegree 6 p :=
        Finset.sum_le_sum fun p _hp => by
          have hne := hn p
          omega
      have hinc := S.line_incidence 6
      dsimp only [r] at hr1
      rw [hr1] at hinc
      norm_num at hinc
      simp [ctx.pointCard] at hlower
      omega
    obtain ⟨p, hld6⟩ := hoff
    have hrow := ctx.localRows p
    have hd3 : S.blockDegree 3 p = 8 := by
      have hs := hrow.sigmaRow
      rw [hsigmaEq p, hd5 p, hd6 p] at hs
      omega
    have hd4 : S.blockDegree 4 p = 9 := by
      have hr := hrow.richResidueRow
      rw [hsigmaEq p, hd5 p, hd6 p] at hr
      omega
    have hl3 : S.lineDegree 3 p = 4 := by
      have hkrow := hrow.kappaRow
      rw [hkappaEq p, hsigmaEq p, hld4 p, hld5 p, hld6] at hkrow
      omega
    exact ctx.noTypeB ⟨p, hd3, hd4, hd5 p, hd6 p,
      hl3, hld4 p, hld5 p, hld6⟩

/-- The least nonnegative sigma in the residue class `1-d5` for
`d5 ≤ 2`, written without a case-defined cost function. -/
theorem twelveSix_sigma_residue_cost_two
    (d5 sigma : Nat) (hd5 : d5 ≤ 2)
    (hres : (sigma + d5) % 3 = 1) :
    1 + 3 * Nat.choose d5 2 ≤ sigma + d5 := by
  interval_cases d5 <;> norm_num [Nat.choose] at hres ⊢ <;> omega

/-- Supporting line for the balanced rich-degree moment in the only range
used below. -/
private theorem twelveSix_rich_degree_support
    (d5 d6 : Nat) (hd5 : d5 ≤ 3) (hd6 : d6 ≤ 3) :
    2 * (d5 + d6) ≤ Nat.choose (d5 + d6) 2 + 3 := by
  interval_cases d5 <;> interval_cases d6 <;> norm_num [Nat.choose]

/-- In the three-block distribution, the direction row and the sigma
residue have costs `1,4` on six-degrees `1,2`. -/
private theorem twelveSix_three_direction_cost_zero
    (d6 sigma : Nat) (hd6 : d6 = 1 ∨ d6 = 2)
    (hres : sigma % 3 = 1)
    (hdir : 6 * d6 ≤ sigma + 8) :
    3 * d6 ≤ sigma + 2 := by
  rcases hd6 with rfl | rfl <;> omega

private theorem twelveSix_three_direction_cost_one
    (d5 d6 sigma : Nat) (hd5 : d5 ≤ 1)
    (hd6 : d6 = 1 ∨ d6 = 2)
    (hres : (sigma + d5) % 3 = 1)
    (hdir : 2 * d5 + 6 * d6 ≤ sigma + 8) :
    3 * d6 ≤ sigma + 2 + d5 := by
  interval_cases d5 <;> rcases hd6 with rfl | rfl <;> omega

/-- With no four- or five-line through a pivot, a point on the unique
five-block contributes at least two units of kappa. -/
private theorem twelveSix_kappa_cost_one
    (d5 kappa : Nat) (hd5 : d5 ≤ 1)
    (hres : (kappa + d5 + 0) % 3 = 0) : 2 * d5 ≤ kappa := by
  interval_cases d5 <;> omega

/-- Three six-blocks contradict the universal spine. -/
theorem twelveSix_three_blocks_impossible
    {Point Block : Type*} [Fintype Point] [Fintype Block]
    [DecidableEq Point]
    (S : BlockSystem Point Block) (ctx : TwelveSixBranchContext S)
    (hm : S.blockCount 6 = 3) : False := by
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
  have hkcap : k ≤ 3 := by
    dsimp only [k]
    exact ctx.spine.sixBlockCaps.2.2.1 hm
  have hsle : ctx.spine.s ≤ 2 := by
    have hQ := ctx.spine.kappaTotal
    change Q + 15 * ctx.spine.s + 9 * ctx.spine.e +
      7 * h + 16 * g + 27 * r =
        6 + 9 * S.blockCount 6 + k at hQ
    omega
  have hd6 (p : Point) :
      S.blockDegree 6 p = 1 ∨ S.blockDegree 6 p = 2 :=
    twelveSix_three_blocks_degree_one_or_two
      S ctx.pointCard hm ctx.sixMoment p
  have hd6cap (p : Point) : S.blockDegree 6 p ≤ 2 := by
    rcases hd6 p with hp | hp <;> omega
  have hd5cap (p : Point) : S.blockDegree 5 p ≤ k := by
    exact (blockDegree_le_blockCount S 5 p)
  have hinc5 : (∑ p : Point, S.blockDegree 5 p) = 5 * k := by
    dsimp only [k]
    exact S.block_incidence 5
  have hinc6 : (∑ p : Point, S.blockDegree 6 p) = 18 := by
    have hi := S.block_incidence 6
    rw [hm] at hi
    norm_num at hi
    exact hi
  have hsumSigma : (∑ p : Point, twelveSixSigmaAt S p) = K :=
    twelveSix_sigma_sum S
  have hsumKappa : (∑ p : Point, twelveSixKappaAt S p) = Q :=
    twelveSix_kappa_sum S
  have hK : K = k + 12 * ctx.spine.s := ctx.spine.sigmaQuotient
  have hM5cap : M5 ≤ 2 * Nat.choose k 2 := by
    simpa [M5, k] using ctx.fiveMoment
  have hM6cap : M6 ≤ 6 := by
    have hh := ctx.sixMoment
    rw [hm] at hh
    change M6 ≤ 2 * Nat.choose 3 2 at hh
    norm_num [Nat.choose] at hh
    exact hh
  have hMRcap : MR ≤ 2 * Nat.choose (k + 3) 2 := by
    have hh := ctx.richMoment
    rw [hm] at hh
    simpa [MR, k, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hh
  have hXcap : X ≤ 6 * k := by
    have hh := ctx.crossMoment
    rw [hm] at hh
    change X ≤ 2 * k * 3 at hh
    omega
  have hM6 : M6 = 6 := by
    have hpoint (p : Point) :
        Nat.choose (S.blockDegree 6 p) 2 + 1 = S.blockDegree 6 p := by
      rcases hd6 p with hp | hp <;> rw [hp] <;> norm_num [Nat.choose]
    have hsum : M6 + 12 = 18 := by
      calc
        M6 + 12 = ∑ p : Point,
            (Nat.choose (S.blockDegree 6 p) 2 + 1) := by
          rw [Finset.sum_add_distrib]
          simp [M6, ctx.pointCard]
        _ = ∑ p : Point, S.blockDegree 6 p := by
          apply Finset.sum_congr rfl
          intro p _hp
          exact hpoint p
        _ = 18 := hinc6
    omega
  have hcase : ctx.spine.s = 0 ∨ ctx.spine.s = 1 ∨ ctx.spine.s = 2 := by
    omega
  rcases hcase with hs0 | hs1 | hs2
  · have hkcases : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by omega
    rcases hkcases with hk0 | hk1 | hk2 | hk3
    · have hpoint (p : Point) : 1 ≤
          twelveSixSigmaAt S p + S.blockDegree 5 p := by
        have hr := (ctx.localRows p).sigmaResidue
        omega
      have hsum : 12 ≤ K + 5 * k := by
        have hh : (∑ _p : Point, 1) ≤
            ∑ p : Point,
              (twelveSixSigmaAt S p + S.blockDegree 5 p) :=
          Finset.sum_le_sum fun p _hp => hpoint p
        rw [Finset.sum_add_distrib, hsumSigma, hinc5] at hh
        simpa [ctx.pointCard] using hh
      omega
    · have hpoint (p : Point) : 1 ≤
          twelveSixSigmaAt S p + S.blockDegree 5 p := by
        have hr := (ctx.localRows p).sigmaResidue
        omega
      have hsum : 12 ≤ K + 5 * k := by
        have hh : (∑ _p : Point, 1) ≤
            ∑ p : Point,
              (twelveSixSigmaAt S p + S.blockDegree 5 p) :=
          Finset.sum_le_sum fun p _hp => hpoint p
        rw [Finset.sum_add_distrib, hsumSigma, hinc5] at hh
        simpa [ctx.pointCard] using hh
      omega
    · have hrichPoint (p : Point) :
          2 * (S.blockDegree 5 p + S.blockDegree 6 p) ≤
            Nat.choose (S.blockDegree 5 p + S.blockDegree 6 p) 2 + 3 :=
        twelveSix_rich_degree_support _ _
          ((hd5cap p).trans hkcap) (by rcases hd6 p with hp | hp <;> omega)
      have hMRlower : 20 ≤ MR := by
        have hh := Finset.sum_le_sum fun p (_hp : p ∈ (Finset.univ : Finset Point)) =>
          hrichPoint p
        simp only [Finset.sum_add_distrib, twelveSix_sum_const_mul] at hh
        rw [hinc5, hinc6] at hh
        simp [ctx.pointCard] at hh
        change 2 * (5 * k + 18) ≤ MR + 36 at hh
        omega
      have hMR : MR = 20 := by
        norm_num [hk2, Nat.choose] at hMRcap
        omega
      have hdecomp : MR = M5 + M6 + X := by
        calc
          MR = ∑ p : Point,
              (Nat.choose (S.blockDegree 5 p) 2 +
                Nat.choose (S.blockDegree 6 p) 2 +
                S.blockDegree 5 p * S.blockDegree 6 p) := by
            apply Finset.sum_congr rfl
            intro p _hp
            exact twelveSix_choose_add_two _ _
              ((hd5cap p).trans (by omega)) (by rcases hd6 p with hp | hp <;> omega)
          _ = M5 + M6 + X := by
            simp only [Finset.sum_add_distrib, M5, M6, X]
      have hM5 : M5 = 2 := by
        have hM5upper := hM5cap
        rw [hk2] at hM5upper
        norm_num [Nat.choose] at hM5upper
        have hXupper : X ≤ 12 := by omega
        omega
      have hcost (p : Point) :
          1 + 3 * Nat.choose (S.blockDegree 5 p) 2 ≤
            twelveSixSigmaAt S p + S.blockDegree 5 p :=
        twelveSix_sigma_residue_cost_two _ _
          ((hd5cap p).trans_eq hk2) (ctx.localRows p).sigmaResidue
      have hsumCost := Finset.sum_le_sum
        (fun p (_hp : p ∈ (Finset.univ : Finset Point)) => hcost p)
      rw [Finset.sum_add_distrib, ← Finset.mul_sum,
        Finset.sum_add_distrib, hsumSigma, hinc5] at hsumCost
      simp [ctx.pointCard, M5, hM5] at hsumCost
      omega
    · have hrichPoint (p : Point) :
          2 * (S.blockDegree 5 p + S.blockDegree 6 p) ≤
            Nat.choose (S.blockDegree 5 p + S.blockDegree 6 p) 2 + 3 :=
        twelveSix_rich_degree_support _ _
          ((hd5cap p).trans_eq hk3) (by rcases hd6 p with hp | hp <;> omega)
      have hMRlower : 30 ≤ MR := by
        have hh := Finset.sum_le_sum fun p (_hp : p ∈ (Finset.univ : Finset Point)) =>
          hrichPoint p
        simp only [Finset.sum_add_distrib, twelveSix_sum_const_mul] at hh
        rw [hinc5, hinc6] at hh
        simp [ctx.pointCard] at hh
        change 2 * (5 * k + 18) ≤ MR + 36 at hh
        omega
      have hMR : MR = 30 := by
        norm_num [hk3, Nat.choose] at hMRcap
        omega
      have hdecomp : MR = M5 + M6 + X := by
        calc
          MR = ∑ p : Point,
              (Nat.choose (S.blockDegree 5 p) 2 +
                Nat.choose (S.blockDegree 6 p) 2 +
                S.blockDegree 5 p * S.blockDegree 6 p) := by
            apply Finset.sum_congr rfl
            intro p _hp
            exact twelveSix_choose_add_two _ _
              ((hd5cap p).trans (by omega)) (by rcases hd6 p with hp | hp <;> omega)
          _ = M5 + M6 + X := by
            simp only [Finset.sum_add_distrib, M5, M6, X]
      have hM5 : M5 = 6 := by
        have hM5upper := hM5cap
        rw [hk3] at hM5upper
        norm_num [Nat.choose] at hM5upper
        have hXupper : X ≤ 18 := by omega
        omega
      have hrichEq (p : Point) :
          2 * (S.blockDegree 5 p + S.blockDegree 6 p) =
            Nat.choose (S.blockDegree 5 p + S.blockDegree 6 p) 2 + 3 := by
        have hsumEq :
            (∑ p : Point, 2 * (S.blockDegree 5 p + S.blockDegree 6 p)) =
              ∑ p : Point,
                (Nat.choose (S.blockDegree 5 p + S.blockDegree 6 p) 2 + 3) := by
          rw [← Finset.mul_sum, Finset.sum_add_distrib,
            hinc5, hinc6, Finset.sum_add_distrib]
          simp [MR, hMR, ctx.pointCard, hk3]
        exact (Finset.sum_eq_sum_iff_of_le
          (fun q _hq => hrichPoint q)).mp hsumEq p (Finset.mem_univ p)
      have hd5two (p : Point) : S.blockDegree 5 p ≤ 2 := by
        have hb : S.blockDegree 5 p ≤ 3 := (hd5cap p).trans_eq hk3
        have hr := hrichEq p
        rcases hd6 p with hp | hp
        · rw [hp] at hr
          interval_cases hd : S.blockDegree 5 p
          all_goals norm_num [Nat.choose] at hr
          all_goals omega
        · rw [hp] at hr
          interval_cases hd : S.blockDegree 5 p
          all_goals norm_num [Nat.choose] at hr
          all_goals omega
      have hcost (p : Point) :
          1 + 3 * Nat.choose (S.blockDegree 5 p) 2 ≤
            twelveSixSigmaAt S p + S.blockDegree 5 p :=
        twelveSix_sigma_residue_cost_two _ _ (hd5two p)
          (ctx.localRows p).sigmaResidue
      have hsumCost := Finset.sum_le_sum
        (fun p (_hp : p ∈ (Finset.univ : Finset Point)) => hcost p)
      rw [Finset.sum_add_distrib, ← Finset.mul_sum,
        Finset.sum_add_distrib, hsumSigma, hinc5] at hsumCost
      simp [ctx.pointCard, M5, hM5] at hsumCost
      omega
  · have hr0 : r = 0 := by
      have hQ := ctx.spine.kappaTotal
      change Q + 15 * ctx.spine.s + 9 * ctx.spine.e +
        7 * h + 16 * g + 27 * r =
          6 + 9 * S.blockCount 6 + k at hQ
      omega
    have hdir (p : Point) := ctx.direction (by simpa [r] using hr0) p
      (by rcases hd6 p with hp | hp <;> omega)
    have hsumDir : 10 * k + 108 ≤ K + 96 := by
      have hh := Finset.sum_le_sum
        (fun p (_hp : p ∈ (Finset.univ : Finset Point)) => hdir p)
      rw [Finset.sum_add_distrib, ← Finset.mul_sum,
        ← Finset.mul_sum, Finset.sum_add_distrib, hinc5, hinc6,
        hsumSigma] at hh
      simp [ctx.pointCard] at hh
      omega
    have hk0 : k = 0 := by omega
    have hcost (p : Point) :
        3 * S.blockDegree 6 p ≤ twelveSixSigmaAt S p + 2 := by
      have hd5zero : S.blockDegree 5 p = 0 := by
        have hp := hd5cap p
        omega
      have hr := (ctx.localRows p).sigmaResidue
      rw [hd5zero] at hr
      have hd := hdir p
      rw [hd5zero] at hd
      exact twelveSix_three_direction_cost_zero _ _ (hd6 p) hr
        (by simpa using hd)
    have hsumCost := Finset.sum_le_sum
      (fun p (_hp : p ∈ (Finset.univ : Finset Point)) => hcost p)
    rw [← Finset.mul_sum, hinc6, Finset.sum_add_distrib, hsumSigma] at hsumCost
    simp [ctx.pointCard] at hsumCost
    omega
  · have hr0 : r = 0 := by
      have hQ := ctx.spine.kappaTotal
      change Q + 15 * ctx.spine.s + 9 * ctx.spine.e +
        7 * h + 16 * g + 27 * r =
          6 + 9 * S.blockCount 6 + k at hQ
      omega
    have hdir (p : Point) := ctx.direction (by simpa [r] using hr0) p
      (by rcases hd6 p with hp | hp <;> omega)
    have hsumDir : 10 * k + 108 ≤ K + 96 := by
      have hh := Finset.sum_le_sum
        (fun p (_hp : p ∈ (Finset.univ : Finset Point)) => hdir p)
      rw [Finset.sum_add_distrib, ← Finset.mul_sum,
        ← Finset.mul_sum, Finset.sum_add_distrib, hinc5, hinc6,
        hsumSigma] at hh
      simp [ctx.pointCard] at hh
      omega
    have hkc : k = 0 ∨ k = 1 := by omega
    rcases hkc with hk0 | hk1
    · have hcost (p : Point) :
          3 * S.blockDegree 6 p ≤ twelveSixSigmaAt S p + 2 := by
        have hd5zero : S.blockDegree 5 p = 0 := by
          have hp := hd5cap p
          omega
        have hr := (ctx.localRows p).sigmaResidue
        rw [hd5zero] at hr
        have hd := hdir p
        rw [hd5zero] at hd
        exact twelveSix_three_direction_cost_zero _ _ (hd6 p) hr
          (by simpa using hd)
      have hsumCost := Finset.sum_le_sum
        (fun p (_hp : p ∈ (Finset.univ : Finset Point)) => hcost p)
      rw [← Finset.mul_sum, hinc6, Finset.sum_add_distrib, hsumSigma] at hsumCost
      simp [ctx.pointCard] at hsumCost
      omega
    · have hscalar : ctx.spine.e = 0 /\ h = 0 /\ g = 0 /\ Q = 4 := by
        have hQ := ctx.spine.kappaTotal
        change Q + 15 * ctx.spine.s + 9 * ctx.spine.e +
          7 * h + 16 * g + 27 * r =
            6 + 9 * S.blockCount 6 + k at hQ
        have hM5capOne := hM5cap
        have hMRcapOne := hMRcap
        have hXcapOne := hXcap
        norm_num [hk1, Nat.choose] at hM5capOne hMRcapOne hXcapOne
        clear hM5cap hMRcap hXcap
        have hezero : ctx.spine.e = 0 := by omega
        have hhzero : h = 0 := by omega
        have hgzero : g = 0 := by omega
        refine ⟨hezero, hhzero, hgzero, ?_⟩
        omega
      rcases hscalar with ⟨he, hh, hg, hQfour⟩
      have hld4 (p : Point) : S.lineDegree 4 p = 0 := by
        have hp := lineDegree_le_lineCount S 4 p
        dsimp only [h] at hh
        omega
      have hld5 (p : Point) : S.lineDegree 5 p = 0 := by
        have hp := lineDegree_le_lineCount S 5 p
        dsimp only [g] at hg
        omega
      have hkcost (p : Point) :
          2 * S.blockDegree 5 p ≤ twelveSixKappaAt S p := by
        have hb := hd5cap p
        have hr := (ctx.localRows p).kappaResidue
        rw [hld4 p, hld5 p] at hr
        exact twelveSix_kappa_cost_one _ _ (by omega) hr
      have hsumCost := Finset.sum_le_sum
        (fun p (_hp : p ∈ (Finset.univ : Finset Point)) => hkcost p)
      rw [← Finset.mul_sum, hinc5, hsumKappa] at hsumCost
      omega

end Erdos506.V1
