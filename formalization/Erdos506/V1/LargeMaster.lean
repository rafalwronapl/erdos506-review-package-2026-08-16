import Erdos506.V1.UniversalRows

/-!
# The analytic large-range master for V1

This module formalizes the manuscript's single `S_M` functional.  After
clearing denominators, its circle coefficients are at most `36 M`, its line
coefficients are nonpositive, and the universal `T/P/D/L` rows give the
stated lower numerator.  The final parity calculation is symbolic for every
`n ≥ 15`; it does not enumerate configurations or invoke native reflection.
-/

namespace Erdos506.V1

open Erdos506.Block
open Erdos506.Block.BlockSystem
open Erdos506.V4
open scoped BigOperators

universe u

private theorem six_mul_choose_three (s : ℕ) :
    6 * Nat.choose s 3 = s * (s - 1) * (s - 2) := by
  have h3 := Nat.choose_succ_right_eq s 2
  have h2 := Nat.choose_succ_right_eq s 1
  simp only [Nat.reduceAdd, Nat.choose_one_right] at h3 h2
  calc
    6 * Nat.choose s 3 = 2 * (Nat.choose s 3 * 3) := by ring
    _ = 2 * (Nat.choose s 2 * (s - 2)) := by rw [h3]
    _ = (Nat.choose s 2 * 2) * (s - 2) := by ring
    _ = s * (s - 1) * (s - 2) := by rw [h2]

private theorem eighteen_choose_three_int (s : ℕ) (hs : 3 ≤ s) :
    18 * (Nat.choose s 3 : ℤ) =
      3 * (s : ℤ) * ((s : ℤ) - 1) * ((s : ℤ) - 2) := by
  have h := congrArg (fun z : ℕ => (z : ℤ)) (six_mul_choose_three s)
  push_cast [Nat.cast_sub (by omega : 1 ≤ s),
    Nat.cast_sub (by omega : 2 ≤ s)] at h
  nlinarith

def largeMasterCircleCoeff (M s : ℕ) : ℤ :=
  18 * (Nat.choose s 3 : ℤ) +
    2 * ((M : ℤ) + 3) * (s : ℤ) * (4 - (s : ℤ)) +
    3 * ((M : ℤ) - 2) * (s : ℤ) * ((s : ℤ) - 1) -
    4 * (M : ℤ) * (s : ℤ) * ((s : ℤ) - 4)

def largeMasterLineCoeff (M s : ℕ) : ℤ :=
  18 * (Nat.choose s 3 : ℤ) +
    2 * ((M : ℤ) + 3) * (s : ℤ) * (4 - (s : ℤ)) +
    3 * ((M : ℤ) - 2) * (s : ℤ) * ((s : ℤ) - 1) -
    8 * (M : ℤ) * (s : ℤ) * ((s : ℤ) - 2)

theorem largeMasterCircleCoeff_slack (M s : ℕ) (hs : 3 ≤ s) :
    36 * (M : ℤ) - largeMasterCircleCoeff M s =
      3 * ((M : ℤ) - (s : ℤ)) * ((s : ℤ) - 4) * ((s : ℤ) - 3) := by
  rw [largeMasterCircleCoeff, eighteen_choose_three_int s hs]
  ring

theorem largeMasterLineCoeff_factor (M s : ℕ) (hs : 3 ≤ s) :
    largeMasterLineCoeff M s =
      (s : ℤ) * ((s : ℤ) - 3) *
        (-7 * (M : ℤ) + 3 * (s : ℤ) - 12) := by
  rw [largeMasterLineCoeff, eighteen_choose_three_int s hs]
  ring

theorem largeMasterCircleCoeff_le (M s : ℕ) (hs : 3 ≤ s) (hsM : s ≤ M) :
    largeMasterCircleCoeff M s ≤ 36 * (M : ℤ) := by
  have hsMz : (s : ℤ) ≤ (M : ℤ) := by exact_mod_cast hsM
  have hMs : 0 ≤ (M : ℤ) - (s : ℤ) := by omega
  by_cases hs4 : s ≤ 4
  · have hsCases : s = 3 ∨ s = 4 := by omega
    have hgap :
        0 ≤ 3 * ((M : ℤ) - (s : ℤ)) * ((s : ℤ) - 4) *
          ((s : ℤ) - 3) := by
      rcases hsCases with rfl | rfl <;> norm_num
    rw [← largeMasterCircleCoeff_slack M s hs] at hgap
    omega
  · have hs4z : 0 ≤ (s : ℤ) - 4 := by omega
    have hs3z : 0 ≤ (s : ℤ) - 3 := by omega
    have hgap :
        0 ≤ 3 * ((M : ℤ) - (s : ℤ)) * ((s : ℤ) - 4) *
          ((s : ℤ) - 3) := by positivity
    rw [← largeMasterCircleCoeff_slack M s hs] at hgap
    omega

theorem largeMasterLineCoeff_nonpos (M s : ℕ)
    (hs : 3 ≤ s) (hsM : s ≤ M) :
    largeMasterLineCoeff M s ≤ 0 := by
  rw [largeMasterLineCoeff_factor M s hs]
  have hs0 : 0 ≤ (s : ℤ) := by positivity
  have hs3z : 0 ≤ (s : ℤ) - 3 := by omega
  have hlast : -7 * (M : ℤ) + 3 * (s : ℤ) - 12 ≤ 0 := by
    have hsMz : (s : ℤ) ≤ (M : ℤ) := by exact_mod_cast hsM
    omega
  exact mul_nonpos_of_nonneg_of_nonpos (mul_nonneg hs0 hs3z) hlast

private theorem circleCount_eq_zero_of_lt_three
    {Point Block : Type*} [Fintype Point] [Fintype Block]
    [DecidableEq Point] (S : BlockSystem Point Block)
    (s : ℕ) (hs : s < 3) :
    S.circleCount s = 0 := by
  rw [BlockSystem.circleCount]
  apply Finset.card_eq_zero.mpr
  apply Finset.not_nonempty_iff_eq_empty.mp
  intro hne
  obtain ⟨b, hb⟩ := hne
  have hb' := S.mem_blocksOfKindSize.mp hb
  have hmin := S.circle_min b hb'.1
  omega

private theorem triple_partition_nontrivial_int
    {Point Block : Type*} [Fintype Point] [Fintype Block]
    [DecidableEq Point] (S : BlockSystem Point Block) :
    (∑ s ∈ S.nontrivialSizes,
        (Nat.choose s 3 : ℤ) * (S.blockCount s : ℤ)) =
      (Nat.choose (Fintype.card Point) 3 : ℤ) := by
  have hnat :
      (∑ s ∈ S.nontrivialSizes,
          Nat.choose s 3 * S.blockCount s) =
        Nat.choose (Fintype.card Point) 3 := by
    rw [← S.triple_partition_by_size]
    apply Finset.sum_subset
    · intro s hs
      simp only [nontrivialSizes, Finset.mem_Icc] at hs
      simp only [Finset.mem_range]
      omega
    · intro s hsRange hsNot
      simp only [Finset.mem_range] at hsRange
      simp only [nontrivialSizes, Finset.mem_Icc, not_and_or] at hsNot
      have hslt : s < 3 := by omega
      rw [Nat.choose_eq_zero_of_lt hslt]
      simp
  exact_mod_cast hnat

private theorem totalCircleCount_eq_sum_nontrivial
    {Point Block : Type*} [Fintype Point] [Fintype Block]
    [DecidableEq Point] (S : BlockSystem Point Block) :
    S.totalCircleCount = ∑ s ∈ S.nontrivialSizes, S.circleCount s := by
  rw [S.totalCircleCount_eq_sum_circleCount]
  symm
  apply Finset.sum_subset
  · intro s hs
    simp only [nontrivialSizes, Finset.mem_Icc] at hs
    simp only [Finset.mem_range]
    omega
  · intro s hsRange hsNot
    simp only [Finset.mem_range] at hsRange
    simp only [nontrivialSizes, Finset.mem_Icc, not_and_or] at hsNot
    have hslt : s < 3 := by omega
    exact circleCount_eq_zero_of_lt_three S s hslt

def largeMasterFunctional
    {Point Block : Type*} [Fintype Point] [Fintype Block]
    [DecidableEq Point] (S : BlockSystem Point Block) (M : ℕ) : ℤ :=
  ∑ s ∈ S.nontrivialSizes,
    (largeMasterCircleCoeff M s * (S.circleCount s : ℤ) +
      largeMasterLineCoeff M s * (S.lineCount s : ℤ))

theorem largeMasterFunctional_eq_rows
    {Point Block : Type*} [Fintype Point] [Fintype Block]
    [DecidableEq Point] (S : BlockSystem Point Block) (M : ℕ) :
    largeMasterFunctional S M =
      18 * (Nat.choose (Fintype.card Point) 3 : ℤ) +
        2 * ((M : ℤ) + 3) * S.pivotRow +
        3 * ((M : ℤ) - 2) * S.langerRow -
        4 * (M : ℤ) * S.defectRow := by
  rw [← triple_partition_nontrivial_int S]
  unfold largeMasterFunctional largeMasterCircleCoeff largeMasterLineCoeff
    pivotRow langerRow defectRow
  calc
    (∑ s ∈ S.nontrivialSizes,
        ((18 * (Nat.choose s 3 : ℤ) +
              2 * ((M : ℤ) + 3) * (s : ℤ) * (4 - (s : ℤ)) +
              3 * ((M : ℤ) - 2) * (s : ℤ) * ((s : ℤ) - 1) -
              4 * (M : ℤ) * (s : ℤ) * ((s : ℤ) - 4)) *
            (S.circleCount s : ℤ) +
          (18 * (Nat.choose s 3 : ℤ) +
              2 * ((M : ℤ) + 3) * (s : ℤ) * (4 - (s : ℤ)) +
              3 * ((M : ℤ) - 2) * (s : ℤ) * ((s : ℤ) - 1) -
              8 * (M : ℤ) * (s : ℤ) * ((s : ℤ) - 2)) *
            (S.lineCount s : ℤ))) =
        ∑ s ∈ S.nontrivialSizes,
          (18 * ((Nat.choose s 3 : ℤ) * (S.blockCount s : ℤ)) +
            2 * ((M : ℤ) + 3) *
              ((s : ℤ) * (4 - (s : ℤ)) * (S.blockCount s : ℤ)) +
            3 * ((M : ℤ) - 2) *
              ((s : ℤ) * ((s : ℤ) - 1) * (S.blockCount s : ℤ)) -
            (4 * (M : ℤ) *
                ((s : ℤ) * ((s : ℤ) - 4) * (S.circleCount s : ℤ)) +
              4 * (M : ℤ) *
                (2 * (s : ℤ) * ((s : ℤ) - 2) * (S.lineCount s : ℤ)))) := by
      apply Finset.sum_congr rfl
      intro s hs
      have hsplit : (S.blockCount s : ℤ) =
          (S.lineCount s : ℤ) + (S.circleCount s : ℤ) := by
        exact_mod_cast S.blockCount_eq_lineCount_add_circleCount s
      rw [hsplit]
      ring
    _ =
      18 * (∑ s ∈ S.nontrivialSizes,
          (Nat.choose s 3 : ℤ) * (S.blockCount s : ℤ)) +
        2 * ((M : ℤ) + 3) *
          (∑ s ∈ S.nontrivialSizes,
            (s : ℤ) * (4 - (s : ℤ)) * (S.blockCount s : ℤ)) +
        3 * ((M : ℤ) - 2) *
          (∑ s ∈ S.nontrivialSizes,
            (s : ℤ) * ((s : ℤ) - 1) * (S.blockCount s : ℤ)) -
        4 * (M : ℤ) *
          ((∑ s ∈ S.nontrivialSizes,
              (s : ℤ) * ((s : ℤ) - 4) * (S.circleCount s : ℤ)) +
            ∑ s ∈ S.nontrivialSizes,
              2 * (s : ℤ) * ((s : ℤ) - 2) * (S.lineCount s : ℤ)) := by
      simp_rw [Finset.sum_sub_distrib, Finset.sum_add_distrib,
        ← Finset.mul_sum]
      ring_nf

def BlockSizeCap
    {Point Block : Type*} [Fintype Point] [Fintype Block]
    [DecidableEq Point] (S : BlockSystem Point Block) (M : ℕ) : Prop :=
  ∀ b : Block, 3 ≤ (S.support b).card → (S.support b).card ≤ M

/-- A cap on V1 blocks gives the Langer occupancy hypothesis after every
inversion, provided the corresponding elementary numerical inequality holds. -/
theorem pivotOccupancy_of_blockSizeCap
    {α : Type*} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (M : ℕ)
    (hcap : BlockSizeCap (blockSystem cfg) M)
    (hnum : 3 * (M - 1) ≤ 2 * (Fintype.card α - 1)) :
    ∀ p : α,
      Erdos506.Incidence.LineOccupancyTwoThirds
        (Erdos506.V3.pivotInversion cfg p) := by
  intro p L
  obtain ⟨b, rfl⟩ := blockToPivotLine_surjective cfg p L
  have hbcap : (geometricBlockSupport cfg b.1).card ≤ M := by
    exact hcap b.1 b.2.2
  rw [card_lineSupport_blockToPivotLine, Erdos506.V3.card_awayFrom]
  omega

theorem largeMasterFunctional_le_circleCount
    {Point Block : Type*} [Fintype Point] [Fintype Block]
    [DecidableEq Point] (S : BlockSystem Point Block) (M : ℕ)
    (hcap : BlockSizeCap S M) :
    largeMasterFunctional S M ≤ 36 * (M : ℤ) * S.totalCircleCount := by
  unfold largeMasterFunctional
  rw [totalCircleCount_eq_sum_nontrivial S]
  push_cast
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro s hs
  have hsBounds := Finset.mem_Icc.mp hs
  have hlineCap : S.lineCount s ≠ 0 → s ≤ M := by
    intro hne
    rw [BlockSystem.lineCount, Finset.card_ne_zero] at hne
    obtain ⟨b, hb⟩ := hne
    have hb' := S.mem_blocksOfKindSize.mp hb
    have hthree : 3 ≤ (S.support b).card := by
      rw [hb'.2]
      exact hsBounds.1
    have hle := hcap b hthree
    rwa [hb'.2] at hle
  have hcircleCap : S.circleCount s ≠ 0 → s ≤ M := by
    intro hne
    rw [BlockSystem.circleCount, Finset.card_ne_zero] at hne
    obtain ⟨b, hb⟩ := hne
    have hb' := S.mem_blocksOfKindSize.mp hb
    have hthree : 3 ≤ (S.support b).card := by
      rw [hb'.2]
      exact hsBounds.1
    have hle := hcap b hthree
    rwa [hb'.2] at hle
  by_cases hc : S.circleCount s = 0
  · simp only [hc, Nat.cast_zero, mul_zero, zero_add]
    by_cases hl : S.lineCount s = 0
    · simp [hl]
    · have hcoeff := largeMasterLineCoeff_nonpos M s hsBounds.1 (hlineCap hl)
      exact mul_nonpos_of_nonpos_of_nonneg hcoeff (by positivity)
  · have hcCoeff := largeMasterCircleCoeff_le M s hsBounds.1 (hcircleCap hc)
    have hcMul :
        largeMasterCircleCoeff M s * (S.circleCount s : ℤ) ≤
          36 * (M : ℤ) * (S.circleCount s : ℤ) :=
      mul_le_mul_of_nonneg_right hcCoeff (by positivity)
    by_cases hl : S.lineCount s = 0
    · simpa [hl] using hcMul
    · have hlCoeff := largeMasterLineCoeff_nonpos M s hsBounds.1 (hlineCap hl)
      have hlMul :
          largeMasterLineCoeff M s * (S.lineCount s : ℤ) ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg hlCoeff (by positivity)
      omega

def largeMasterNumerator (n M : ℕ) : ℤ :=
  18 * (Nat.choose n 3 : ℤ) +
    6 * (n : ℤ) * ((M : ℤ) + 3) +
    ((M : ℤ) - 2) * (n : ℤ) * ((n : ℤ) - 1) * ((n : ℤ) + 2) -
    4 * (M : ℤ) * (n : ℤ) * ((n : ℤ) - 4)

private theorem choose_two_even_predecessor (r : ℕ) (hr : 1 ≤ r) :
    Nat.choose (2 * r - 1) 2 = (2 * r - 1) * (r - 1) := by
  have h := Nat.choose_succ_right_eq (2 * r - 1) 1
  simp only [Nat.reduceAdd, Nat.choose_one_right] at h
  have hsub : 2 * r - 1 - 1 = 2 * (r - 1) := by omega
  rw [hsub] at h
  have hprod : (2 * r - 1) * (2 * (r - 1)) =
      ((2 * r - 1) * (r - 1)) * 2 := by ring
  rw [hprod] at h
  omega

private theorem choose_two_odd_predecessor (r : ℕ) :
    Nat.choose (2 * r) 2 = r * (2 * r - 1) := by
  have h := Nat.choose_succ_right_eq (2 * r) 1
  simp only [Nat.reduceAdd, Nat.choose_one_right] at h
  have hprod : 2 * r * (2 * r - 1) =
      (r * (2 * r - 1)) * 2 := by ring
  rw [hprod] at h
  omega

private theorem v1UniformTarget_even (r : ℕ) (hr : 1 ≤ r) :
    Erdos506.v1UniformTarget (2 * r) =
      1 + 2 * (r - 1) * (r - 1) := by
  have hpred : 2 * r - 1 = 2 * (r - 1) + 1 := by omega
  have hdiv : (2 * r - 1) / 2 = r - 1 := by omega
  have hprod : (2 * r - 1) * (r - 1) =
      2 * (r - 1) * (r - 1) + (r - 1) := by
    rw [hpred]
    ring
  unfold Erdos506.v1UniformTarget
  rw [choose_two_even_predecessor r hr, hdiv, hprod]
  omega

private theorem v1UniformTarget_odd (r : ℕ) (hr : 1 ≤ r) :
    Erdos506.v1UniformTarget (2 * r + 1) =
      1 + 2 * r * (r - 1) := by
  have hpred : 2 * r - 1 = 2 * (r - 1) + 1 := by omega
  have hdiv : (2 * r) / 2 = r := by omega
  have hprod : r * (2 * r - 1) = 2 * r * (r - 1) + r := by
    rw [hpred]
    ring
  unfold Erdos506.v1UniformTarget
  rw [show 2 * r + 1 - 1 = 2 * r by omega,
    choose_two_odd_predecessor r, hdiv, hprod]
  omega

/-- The exact parity calculation behind the strict `S_M` contradiction for
the half cap in every size `n ≥ 15`. -/
theorem scaledUniformTarget_lt_largeMasterNumerator
    (n : ℕ) (hn : 15 ≤ n) :
    36 * ((n / 2 : ℕ) : ℤ) * (Erdos506.v1UniformTarget n : ℤ) <
      largeMasterNumerator n (n / 2) := by
  rcases n.even_or_odd' with ⟨r, hnEven | hnOdd⟩
  · subst n
    have hr : 8 ≤ r := by omega
    have hdiv : 2 * r / 2 = r := by omega
    rw [hdiv, v1UniformTarget_even r (by omega)]
    unfold largeMasterNumerator
    rw [eighteen_choose_three_int (2 * r) (by omega)]
    push_cast [Nat.cast_sub (by omega : 1 ≤ r)]
    have ht : 0 ≤ (r : ℤ) - 8 := by omega
    have hquad : 0 < (r : ℤ)^2 - 9 * (r : ℤ) + 13 := by
      calc
        (r : ℤ)^2 - 9 * (r : ℤ) + 13 =
            ((r : ℤ) - 8)^2 + 7 * ((r : ℤ) - 8) + 5 := by ring
        _ > 0 := by positivity
    have hgap :
        0 < 4 * (r : ℤ) * (2 * (r : ℤ) - 1) *
          ((r : ℤ)^2 - 9 * (r : ℤ) + 13) := by
      have hrpos : 0 < (r : ℤ) := by omega
      have htwor : 0 < 2 * (r : ℤ) - 1 := by omega
      exact mul_pos (mul_pos (mul_pos (by norm_num) hrpos) htwor) hquad
    nlinarith
  · subst n
    have hr : 7 ≤ r := by omega
    have hdiv : (2 * r + 1) / 2 = r := by omega
    rw [hdiv, v1UniformTarget_odd r (by omega)]
    unfold largeMasterNumerator
    rw [eighteen_choose_three_int (2 * r + 1) (by omega)]
    push_cast [Nat.cast_sub (by omega : 1 ≤ r)]
    have ht : 0 ≤ (r : ℤ) - 7 := by omega
    have hpoly :
        0 < 4 * (r : ℤ)^4 - 32 * (r : ℤ)^3 +
          37 * (r : ℤ)^2 + 9 := by
      calc
        4 * (r : ℤ)^4 - 32 * (r : ℤ)^3 + 37 * (r : ℤ)^2 + 9 =
            4 * ((r : ℤ) - 7)^4 + 80 * ((r : ℤ) - 7)^3 +
              541 * ((r : ℤ) - 7)^2 + 1302 * ((r : ℤ) - 7) + 450 := by
          ring
        _ > 0 := by positivity
    nlinarith

/-- Integer-scaled form of the manuscript's `S_M` master. -/
theorem largeMasterNumerator_le_circleCount
    {Point Block : Type*} [Fintype Point] [Fintype Block]
    [DecidableEq Point] (S : BlockSystem Point Block) (M : ℕ)
    (hM : 3 ≤ M)
    (hcap : BlockSizeCap S M)
    (hP : 3 * (Fintype.card Point : ℤ) ≤ S.pivotRow)
    (hD : S.defectRow ≤
      (Fintype.card Point : ℤ) * ((Fintype.card Point : ℤ) - 4))
    (hL : (Fintype.card Point : ℤ) *
        ((Fintype.card Point : ℤ) - 1) *
        ((Fintype.card Point : ℤ) + 2) ≤ 3 * S.langerRow) :
    largeMasterNumerator (Fintype.card Point) M ≤
      36 * (M : ℤ) * S.totalCircleCount := by
  have hM2 : 0 ≤ (M : ℤ) - 2 := by omega
  have hM3 : 0 ≤ 2 * ((M : ℤ) + 3) := by positivity
  have hM4 : 0 ≤ 4 * (M : ℤ) := by positivity
  have hP' := mul_le_mul_of_nonneg_left hP hM3
  have hL' := mul_le_mul_of_nonneg_left hL hM2
  have hD' := mul_le_mul_of_nonneg_left hD hM4
  have hfun := largeMasterFunctional_le_circleCount S M hcap
  rw [largeMasterFunctional_eq_rows] at hfun
  unfold largeMasterNumerator
  nlinarith

/-- Geometric specialization of the scaled master.  The only hypotheses not
proved by the universal V1 infrastructure are the block cap and the explicit
Langer occupancy condition. -/
theorem largeMasterNumerator_le_geometricCircleCount
    {α : Type u} [Fintype α] [DecidableEq α]
    (Mel : Erdos506.Incidence.RealPlaneMelchiorPrinciple.{u})
    (Lan : Erdos506.Incidence.RealPlaneLangerPrinciple.{u})
    (cfg : Configuration α) (hadm : Admissible cfg)
    (hcard : 3 ≤ Fintype.card α) (M : ℕ) (hM : 3 ≤ M)
    (hcap : BlockSizeCap (blockSystem cfg) M)
    (hocc : ∀ p : α,
      Erdos506.Incidence.LineOccupancyTwoThirds
        (Erdos506.V3.pivotInversion cfg p)) :
    largeMasterNumerator (Fintype.card α) M ≤
      36 * (M : ℤ) * Erdos506.V4.circleCount cfg := by
  have hP : 3 * (Fintype.card α : ℤ) ≤ rowP cfg :=
    three_n_le_rowP_of_realPlaneMelchior (α := α) Mel cfg hadm hcard
  have hD : rowD cfg ≤
      (Fintype.card α : ℤ) * ((Fintype.card α : ℤ) - 4) :=
    rowD_le_n_mul_n_sub_four_of_realPlaneMelchior
      (α := α) Mel cfg hadm hcard
  have hL : (Fintype.card α : ℤ) * ((Fintype.card α : ℤ) - 1) *
      ((Fintype.card α : ℤ) + 2) ≤ 3 * rowL cfg :=
    n_mul_n_sub_one_mul_n_add_two_le_three_rowL_of_realPlaneLanger
      (α := α) Lan cfg hadm hcard hocc
  unfold rowP at hP
  unfold rowD at hD
  unfold rowL at hL
  have hmaster := largeMasterNumerator_le_circleCount
    (blockSystem cfg) M hM hcap hP hD hL
  rw [totalCircleCount_eq_card_determinedCircle,
    ← Erdos506.V3.circleCount_eq_card_determinedCircle] at hmaster
  exact hmaster

/-- Under the manuscript's half-size block cap, the scaled master is strictly
above the uniform target for every `n ≥ 15`. -/
theorem v1UniformTarget_lt_circleCount_of_halfBlockCap
    {α : Type u} [Fintype α] [DecidableEq α]
    (Mel : Erdos506.Incidence.RealPlaneMelchiorPrinciple.{u})
    (Lan : Erdos506.Incidence.RealPlaneLangerPrinciple.{u})
    (cfg : Configuration α) (hadm : Admissible cfg)
    (hcard : 15 ≤ Fintype.card α)
    (hcap : BlockSizeCap (blockSystem cfg) (Fintype.card α / 2)) :
    Erdos506.v1UniformTarget (Fintype.card α) <
      Erdos506.V4.circleCount cfg := by
  let n := Fintype.card α
  let M := n / 2
  have hM : 3 ≤ M := by
    dsimp only [M, n]
    omega
  have hocc : ∀ p : α,
      Erdos506.Incidence.LineOccupancyTwoThirds
        (Erdos506.V3.pivotInversion cfg p) := by
    apply pivotOccupancy_of_blockSizeCap cfg M hcap
    dsimp only [M, n]
    omega
  have hmaster := largeMasterNumerator_le_geometricCircleCount
    Mel Lan cfg hadm (by omega) M hM hcap hocc
  have hgap := scaledUniformTarget_lt_largeMasterNumerator n (by
    dsimp only [n]
    exact hcard)
  have hscaled := hgap.trans_le hmaster
  have hMpos : 0 < 36 * (M : ℤ) := by positivity
  have hcast :
      (Erdos506.v1UniformTarget n : ℤ) <
        (Erdos506.V4.circleCount cfg : ℤ) := by
    nlinarith
  exact_mod_cast hcast

end Erdos506.V1
