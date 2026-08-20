import Erdos506.V1.ThirteenSix
import Erdos506.V1.FiniteCaps
import Erdos506.Finite.Packing
import Erdos506.Incidence.SixConicEventCapacity
import Erdos506.Incidence.SixConicSignaturesOnHostCap
import Erdos506.Incidence.SixConicU17

/-!
# Full thirteen-point selected-six-circle transport

This module reconstructs the coefficientwise rows which feed the checked
arithmetic certificate in `ThirteenSix.lean`.  The definitions are all
attached to the canonical block system; no circle-count conclusion is used
as an input.
-/

namespace Erdos506.V1

open Erdos506.Block
open Erdos506.Block.BlockSystem
open Erdos506.Incidence
open Erdos506.V4
open scoped BigOperators

universe u v

section OpeningFunctional

variable {Point : Type u} {Block : Type v}
  [Fintype Point] [Fintype Block] [DecidableEq Point]

/-- The ordinary-circle incidence `O=3 C_3`, in a form which can be
expanded block by block. -/
noncomputable def thirteenSixOrdinaryIncidence
    (S : BlockSystem Point Block) : Nat :=
  ∑ b : Block,
    if S.kind b = .circle ∧ (S.support b).card = 3 then 3 else 0

/- The thirteen-point names are abbreviations, but keeping these bridges
explicit prevents the relative-row and residual proofs from depending on
reducibility during rewriting. -/
theorem thirteenSixInside_eq_fourteenInside
    (S : BlockSystem Point Block) (D : Finset Point) (b : Block) :
    thirteenSixInside S D b = fourteenInside S D b := rfl

theorem thirteenSixOutside_eq_fourteenOutside
    (S : BlockSystem Point Block) (D : Finset Point) (b : Block) :
    thirteenSixOutside S D b = fourteenOutside S D b := rfl

theorem thirteenSixInside_add_thirteenSixOutside
    (S : BlockSystem Point Block) (D : Finset Point) (b : Block) :
    thirteenSixInside S D b + thirteenSixOutside S D b =
      (S.support b).card := by
  exact fourteenInside_add_fourteenOutside S D b

theorem thirteenSixOutside_eq_support_inter_compl_card
    (S : BlockSystem Point Block) (D : Finset Point) (b : Block) :
    thirteenSixOutside S D b =
      (S.support b ∩ (Finset.univ \ D)).card := by
  change (S.support b \ D).card =
    (S.support b ∩ (Finset.univ \ D)).card
  congr 1
  ext p
  simp

theorem thirteenSixInside_eq_support_inter_card
    (S : BlockSystem Point Block) (D : Finset Point) (b : Block) :
    thirteenSixInside S D b = (S.support b ∩ D).card := rfl

theorem thirteenSixInside_eq_card_of_support_eq
    (S : BlockSystem Point Block) (D : Finset Point) (b : Block)
    (hsupport : S.support b = D) :
    thirteenSixInside S D b = D.card := by
  change (S.support b ∩ D).card = D.card
  rw [hsupport, Finset.inter_self]

theorem thirteenSixOutside_eq_zero_of_support_eq
    (S : BlockSystem Point Block) (D : Finset Point) (b : Block)
    (hsupport : S.support b = D) :
    thirteenSixOutside S D b = 0 := by
  change (S.support b \ D).card = 0
  rw [hsupport, Finset.sdiff_self, Finset.card_empty]

@[simp] theorem thirteenSix_circle_ne_line :
    (BlockKind.circle : BlockKind) ≠ .line := by decide

@[simp] theorem thirteenSix_line_ne_circle :
    (BlockKind.line : BlockKind) ≠ .circle := by decide

theorem thirteenSix_blockDefectContribution_circle
    (S : BlockSystem Point Block) (D : Finset Point) (b : Block)
    (hkind : S.kind b = .circle) :
    S.blockDefectContribution b =
      ((thirteenSixInside S D b + thirteenSixOutside S D b : Nat) : Int) *
        (((thirteenSixInside S D b +
          thirteenSixOutside S D b : Nat) : Int) - 4) := by
  rw [BlockSystem.blockDefectContribution, hkind,
    ← thirteenSixInside_add_thirteenSixOutside S D b]

theorem thirteenSix_blockDefectContribution_line
    (S : BlockSystem Point Block) (D : Finset Point) (b : Block)
    (hkind : S.kind b = .line) :
    S.blockDefectContribution b =
      2 * ((thirteenSixInside S D b +
        thirteenSixOutside S D b : Nat) : Int) *
        (((thirteenSixInside S D b +
          thirteenSixOutside S D b : Nat) : Int) - 2) := by
  rw [BlockSystem.blockDefectContribution, hkind,
    ← thirteenSixInside_add_thirteenSixOutside S D b]

/-- The cleared opening functional from the manuscript.  The pivot term is
gated because two-point lines are present in `BlockSystem`. -/
def thirteenSixOpeningFunctional
    (kind : BlockKind) (g x : Nat) : Int :=
  141 * (Nat.choose x 3 : Int) +
    340 * (g : Int) * (Nat.choose x 2 : Int) +
    539 * (Nat.choose g 2 : Int) * (x : Int) +
    141 * (Nat.choose g 3 : Int) +
    (if 3 ≤ g + x then
      199 * (x : Int) * (4 - ((g + x : Nat) : Int))
    else 0) +
    (if kind = .circle ∧ g + x = 3 then 237 else 0) -
    (if kind = .circle then 1344 else 0) -
    (if kind = .circle ∧ g = 2 then
      414 * (Nat.choose x 2 : Int)
    else 0)

def thirteenSixOpeningCircleResidual (g x : Nat) : Nat :=
  Int.toNat (123 * (((g + x : Nat) : Int) *
      (((g + x : Nat) : Int) - 4)) -
    thirteenSixOpeningFunctional .circle g x)

def thirteenSixOpeningLineResidual (g x : Nat) : Nat :=
  Int.toNat (123 * (2 * ((g + x : Nat) : Int) *
      (((g + x : Nat) : Int) - 2)) -
    thirteenSixOpeningFunctional .line g x)

def thirteenSixOpeningCircleZeroProfile (g x : Nat) : Prop :=
  (g = 0 ∧ x = 3) ∨ (g = 1 ∧ x = 2) ∨
  (g = 1 ∧ x = 5) ∨ (g = 2 ∧ x = 1) ∨
  (g = 2 ∧ x = 2) ∨ (g = 2 ∧ x = 3)

/-- Two-point lines are genuine zero cells.  They carry none of the
triple, ordinary, weight, or gated pivot rows, but must be present in the
exhaustive local classification. -/
def thirteenSixOpeningLineZeroProfile (g x : Nat) : Prop :=
  (g = 0 ∧ x = 2) ∨ (g = 0 ∧ x = 3) ∨
  (g = 1 ∧ x = 1) ∨ (g = 1 ∧ x = 2) ∨
  (g = 2 ∧ x = 0) ∨ (g = 2 ∧ x = 1)

/-- The complete numerical opening table for a nonselected circle. -/
theorem thirteenSix_opening_circle_table
    (g x : Nat) (hg : g ≤ 2) (hx : x ≤ 6)
    (hmin : 3 ≤ g + x) (hcap : g + x ≤ 6) :
    thirteenSixOpeningFunctional .circle g x ≤
        123 * (((g + x : Nat) : Int) * (((g + x : Nat) : Int) - 4)) ∧
      (thirteenSixOpeningCircleResidual g x = 0 ∨
        96 ≤ thirteenSixOpeningCircleResidual g x) ∧
      (thirteenSixOpeningCircleResidual g x = 0 →
        thirteenSixOpeningCircleZeroProfile g x) := by
  interval_cases g <;> interval_cases x <;>
    norm_num [thirteenSixOpeningCircleResidual,
      thirteenSixOpeningCircleZeroProfile,
      thirteenSixOpeningFunctional, Nat.choose] at *

/-- The complete numerical opening table for a line, including the three
two-point zero cells. -/
theorem thirteenSix_opening_line_table
    (g x : Nat) (hg : g ≤ 2) (hx : x ≤ 6)
    (hmin : 2 ≤ g + x) (hcap : g + x ≤ 6) :
    thirteenSixOpeningFunctional .line g x ≤
        123 * (2 * ((g + x : Nat) : Int) *
          (((g + x : Nat) : Int) - 2)) ∧
      (thirteenSixOpeningLineResidual g x = 0 ∨
        96 ≤ thirteenSixOpeningLineResidual g x) ∧
      (thirteenSixOpeningLineResidual g x = 0 →
        thirteenSixOpeningLineZeroProfile g x) := by
  interval_cases g <;> interval_cases x <;>
    norm_num [thirteenSixOpeningLineResidual,
      thirteenSixOpeningLineZeroProfile,
      thirteenSixOpeningFunctional, Nat.choose] at *

/-- Exact expansion of the opening functional through the four relative
triple rows, the outsider pivot row, `O`, `C`, and `W`. -/
theorem sum_thirteenSixOpeningFunctional_eq
    (S : BlockSystem Point Block) (D : Finset Point)
    (hpoint : Fintype.card Point = 13) (hD : D.card = 6) :
    (∑ b : Block,
      thirteenSixOpeningFunctional (S.kind b)
        (thirteenSixInside S D b) (thirteenSixOutside S D b)) =
      107190 + 199 * S.subsetPivotMoment (Finset.univ \ D) +
        79 * (thirteenSixOrdinaryIncidence S : Int) -
        1344 * (S.totalCircleCount : Int) -
        414 * (thirteenSixWeight S D : Int) := by
  classical
  obtain ⟨hrow0, hrow1, hrow2, hrow3⟩ :=
    thirteenSix_relative_rows S D hpoint hD
  have hmomentX :
      (∑ b : Block,
        if 3 ≤ thirteenSixInside S D b + thirteenSixOutside S D b then
          (thirteenSixOutside S D b : Int) *
            (4 - ((thirteenSixInside S D b +
              thirteenSixOutside S D b : Nat) : Int))
        else 0) = S.subsetPivotMoment (Finset.univ \ D) := by
    rw [subsetPivotMoment]
    apply Fintype.sum_congr
    intro b
    rw [thirteenSixInside_add_thirteenSixOutside,
      thirteenSixOutside_eq_support_inter_compl_card]
  have hordinary :
      (∑ b : Block,
        if S.kind b = .circle ∧
            thirteenSixInside S D b + thirteenSixOutside S D b = 3
        then (237 : Int) else 0) =
      79 * (thirteenSixOrdinaryIncidence S : Int) := by
    unfold thirteenSixOrdinaryIncidence
    rw [Nat.cast_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro b _hb
    rw [thirteenSixInside_add_thirteenSixOutside]
    by_cases h : S.kind b = .circle ∧ (S.support b).card = 3
    · simp [h]
    · simp [h]
  have hcircle :
      (∑ b : Block, if S.kind b = .circle then (1344 : Int) else 0) =
        1344 * (S.totalCircleCount : Int) := by
    rw [← Finset.sum_filter]
    simp [BlockSystem.totalCircleCount, BlockSystem.blocksOfKind]
    ring
  have hweight :
      (∑ b : Block,
        if S.kind b = .circle ∧ thirteenSixInside S D b = 2 then
          (Nat.choose (thirteenSixOutside S D b) 2 : Int)
        else 0) = (thirteenSixWeight S D : Int) := by
    rw [thirteenSixWeight, fourteenWeight, Nat.cast_sum]
    simp [fourteenTwoTraceCircles, Finset.sum_filter]
  have hpointwise (b : Block) :
      thirteenSixOpeningFunctional (S.kind b)
          (thirteenSixInside S D b) (thirteenSixOutside S D b) =
        141 * (Nat.choose (thirteenSixOutside S D b) 3 : Int) +
        340 * ((thirteenSixInside S D b : Int) *
          (Nat.choose (thirteenSixOutside S D b) 2 : Int)) +
        539 * ((Nat.choose (thirteenSixInside S D b) 2 : Int) *
          (thirteenSixOutside S D b : Int)) +
        141 * (Nat.choose (thirteenSixInside S D b) 3 : Int) +
        199 * (if 3 ≤ thirteenSixInside S D b +
            thirteenSixOutside S D b then
          (thirteenSixOutside S D b : Int) *
            (4 - ((thirteenSixInside S D b +
              thirteenSixOutside S D b : Nat) : Int))
        else 0) +
        (if S.kind b = .circle ∧
            thirteenSixInside S D b + thirteenSixOutside S D b = 3
          then 237 else 0) -
        (if S.kind b = .circle then 1344 else 0) -
        414 * (if S.kind b = .circle ∧ thirteenSixInside S D b = 2
          then (Nat.choose (thirteenSixOutside S D b) 2 : Int)
          else 0) := by
    by_cases hthree :
      3 ≤ thirteenSixInside S D b + thirteenSixOutside S D b
    <;> simp [thirteenSixOpeningFunctional, hthree]
    <;> ring
  simp_rw [hpointwise]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ← Finset.mul_sum]
  rw [hrow0, hrow1, hrow2, hrow3, hmomentX, hordinary,
    hcircle, hweight]
  ring

/-- Every admissible local cell has nonnegative opening residual. -/
theorem thirteenSixOpeningFunctional_le_blockDefect
    (S : BlockSystem Point Block) (D : Finset Point) (gamma : Block)
    (hD : D.card = 6)
    (hgammaKind : S.kind gamma = .circle)
    (hgammaSupport : S.support gamma = D)
    (hcircleCap : ∀ b, S.kind b = .circle → (S.support b).card ≤ 6)
    (hlineCap : ∀ b, S.kind b = .line → (S.support b).card ≤ 6)
    (b : Block) :
    thirteenSixOpeningFunctional (S.kind b)
        (thirteenSixInside S D b) (thirteenSixOutside S D b) ≤
      123 * S.blockDefectContribution b := by
  by_cases hbgamma : b = gamma
  · subst b
    have hg : thirteenSixInside S D gamma = 6 := by
      exact (thirteenSixInside_eq_card_of_support_eq
        S D gamma hgammaSupport).trans hD
    have hx : thirteenSixOutside S D gamma = 0 :=
      thirteenSixOutside_eq_zero_of_support_eq S D gamma hgammaSupport
    have hdefect : S.blockDefectContribution gamma = 12 := by
      rw [thirteenSix_blockDefectContribution_circle S D gamma hgammaKind,
        hg, hx]
      norm_num
    rw [hdefect]
    norm_num [hg, hx, hgammaKind, thirteenSixOpeningFunctional, Nat.choose]
  · have hg : thirteenSixInside S D b ≤ 2 := by
      have hinter := S.distinct_block_inter_card_lt_three hbgamma
      rw [hgammaSupport] at hinter
      exact Nat.le_of_lt_succ hinter
    have hsum :
        thirteenSixInside S D b + thirteenSixOutside S D b =
          (S.support b).card :=
      thirteenSixInside_add_thirteenSixOutside S D b
    cases hkind : S.kind b with
    | circle =>
        have hdefect :=
          thirteenSix_blockDefectContribution_circle S D b hkind
        rw [hdefect]
        have hmin := S.circle_min b hkind
        have hcap := hcircleCap b hkind
        rw [← hsum] at hmin hcap
        have hx : thirteenSixOutside S D b ≤ 6 := by omega
        exact (thirteenSix_opening_circle_table
          (thirteenSixInside S D b) (thirteenSixOutside S D b)
          hg hx hmin hcap).1
    | line =>
        have hdefect :=
          thirteenSix_blockDefectContribution_line S D b hkind
        rw [hdefect]
        have hmin := S.line_min b hkind
        have hcap := hlineCap b hkind
        rw [← hsum] at hmin hcap
        have hx : thirteenSixOutside S D b ≤ 6 := by omega
        exact (thirteenSix_opening_line_table
          (thirteenSixInside S D b) (thirteenSixOutside S D b)
          hg hx hmin hcap).1

/-- The nonnegative local opening residual. -/
def thirteenSixOpeningResidual
    (S : BlockSystem Point Block) (D : Finset Point) (b : Block) : Nat :=
  Int.toNat (123 * S.blockDefectContribution b -
    thirteenSixOpeningFunctional (S.kind b)
      (thirteenSixInside S D b) (thirteenSixOutside S D b))

noncomputable def thirteenSixOpeningResidualTotal
    (S : BlockSystem Point Block) (D : Finset Point) : Nat :=
  ∑ b : Block, thirteenSixOpeningResidual S D b

/-- Casting the residual sum recovers the exact signed difference. -/
theorem thirteenSixOpeningResidualTotal_cast
    (S : BlockSystem Point Block) (D : Finset Point) (gamma : Block)
    (hD : D.card = 6)
    (hgammaKind : S.kind gamma = .circle)
    (hgammaSupport : S.support gamma = D)
    (hcircleCap : ∀ b, S.kind b = .circle → (S.support b).card ≤ 6)
    (hlineCap : ∀ b, S.kind b = .line → (S.support b).card ≤ 6) :
    (thirteenSixOpeningResidualTotal S D : Int) =
      123 * S.defectRow -
        ∑ b : Block,
          thirteenSixOpeningFunctional (S.kind b)
            (thirteenSixInside S D b) (thirteenSixOutside S D b) := by
  classical
  unfold thirteenSixOpeningResidualTotal thirteenSixOpeningResidual
  rw [Nat.cast_sum, S.defectRow_eq_sum_blockDefectContribution,
    Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro b _hb
  rw [Int.toNat_of_nonneg]
  exact sub_nonneg.mpr
    (thirteenSixOpeningFunctional_le_blockDefect
      S D gamma hD hgammaKind hgammaSupport hcircleCap hlineCap b)

/-- Every positive cell in the opening residual table costs at least 96. -/
theorem thirteenSixOpeningResidual_eq_zero_or_ge_ninety_six
    (S : BlockSystem Point Block) (D : Finset Point) (gamma : Block)
    (hD : D.card = 6)
    (hgammaKind : S.kind gamma = .circle)
    (hgammaSupport : S.support gamma = D)
    (hcircleCap : ∀ b, S.kind b = .circle → (S.support b).card ≤ 6)
    (hlineCap : ∀ b, S.kind b = .line → (S.support b).card ≤ 6)
    (b : Block) :
    thirteenSixOpeningResidual S D b = 0 ∨
      96 ≤ thirteenSixOpeningResidual S D b := by
  by_cases hbgamma : b = gamma
  · subst b
    left
    have hg : thirteenSixInside S D gamma = 6 := by
      exact (thirteenSixInside_eq_card_of_support_eq
        S D gamma hgammaSupport).trans hD
    have hx : thirteenSixOutside S D gamma = 0 :=
      thirteenSixOutside_eq_zero_of_support_eq S D gamma hgammaSupport
    have hdefect : S.blockDefectContribution gamma = 12 := by
      rw [thirteenSix_blockDefectContribution_circle S D gamma hgammaKind,
        hg, hx]
      norm_num
    unfold thirteenSixOpeningResidual
    rw [hdefect]
    norm_num [hg, hx, hgammaKind, thirteenSixOpeningFunctional, Nat.choose]
  · have hg : thirteenSixInside S D b ≤ 2 := by
      have hinter := S.distinct_block_inter_card_lt_three hbgamma
      rw [hgammaSupport] at hinter
      exact Nat.le_of_lt_succ hinter
    have hsum :
        thirteenSixInside S D b + thirteenSixOutside S D b =
          (S.support b).card :=
      thirteenSixInside_add_thirteenSixOutside S D b
    cases hkind : S.kind b with
    | circle =>
        have hdefect :=
          thirteenSix_blockDefectContribution_circle S D b hkind
        unfold thirteenSixOpeningResidual
        rw [hdefect]
        have hmin := S.circle_min b hkind
        have hcap := hcircleCap b hkind
        rw [← hsum] at hmin hcap
        have hx : thirteenSixOutside S D b ≤ 6 := by omega
        rw [hkind]
        change thirteenSixOpeningCircleResidual
          (thirteenSixInside S D b) (thirteenSixOutside S D b) = 0 ∨
            96 ≤ thirteenSixOpeningCircleResidual
              (thirteenSixInside S D b) (thirteenSixOutside S D b)
        exact (thirteenSix_opening_circle_table
          (thirteenSixInside S D b) (thirteenSixOutside S D b)
          hg hx hmin hcap).2.1
    | line =>
        have hdefect :=
          thirteenSix_blockDefectContribution_line S D b hkind
        unfold thirteenSixOpeningResidual
        rw [hdefect]
        have hmin := S.line_min b hkind
        have hcap := hlineCap b hkind
        rw [← hsum] at hmin hcap
        have hx : thirteenSixOutside S D b ≤ 6 := by omega
        rw [hkind]
        change thirteenSixOpeningLineResidual
          (thirteenSixInside S D b) (thirteenSixOutside S D b) = 0 ∨
            96 ≤ thirteenSixOpeningLineResidual
              (thirteenSixInside S D b) (thirteenSixOutside S D b)
        exact (thirteenSix_opening_line_table
          (thirteenSixInside S D b) (thirteenSixOutside S D b)
          hg hx hmin hcap).2.1

theorem thirteenSixOpeningResidualTotal_eq_zero_or_ge_ninety_six
    (S : BlockSystem Point Block) (D : Finset Point) (gamma : Block)
    (hD : D.card = 6)
    (hgammaKind : S.kind gamma = .circle)
    (hgammaSupport : S.support gamma = D)
    (hcircleCap : ∀ b, S.kind b = .circle → (S.support b).card ≤ 6)
    (hlineCap : ∀ b, S.kind b = .line → (S.support b).card ≤ 6) :
    thirteenSixOpeningResidualTotal S D = 0 ∨
      96 ≤ thirteenSixOpeningResidualTotal S D := by
  by_cases hzero : thirteenSixOpeningResidualTotal S D = 0
  · exact Or.inl hzero
  · right
    have hpos : 0 < thirteenSixOpeningResidualTotal S D :=
      Nat.pos_of_ne_zero hzero
    unfold thirteenSixOpeningResidualTotal at hpos ⊢
    rw [Finset.sum_pos_iff] at hpos
    obtain ⟨b, _hb, hbpos⟩ := hpos
    have hlocal :=
      thirteenSixOpeningResidual_eq_zero_or_ge_ninety_six
        S D gamma hD hgammaKind hgammaSupport hcircleCap hlineCap b
    have hb96 : 96 ≤ thirteenSixOpeningResidual S D b := by
      rcases hlocal with hlocal | hlocal
      · omega
      · exact hlocal
    calc
      96 ≤ thirteenSixOpeningResidual S D b := hb96
      _ ≤ ∑ c : Block, thirteenSixOpeningResidual S D c := by
        exact Finset.single_le_sum
          (fun _ _ => Nat.zero_le _) (Finset.mem_univ b)

/-- The opening residual budget, with the wall `W=47` and the general
`W=48+r` layer as immediate specializations. -/
theorem thirteenSix_opening_residual_budget
    (S : BlockSystem Point Block) (D : Finset Point) (gamma : Block)
    (hpoint : Fintype.card Point = 13) (hD : D.card = 6)
    (hgammaKind : S.kind gamma = .circle)
    (hgammaSupport : S.support gamma = D)
    (hcircleCap : ∀ b, S.kind b = .circle → (S.support b).card ≤ 6)
    (hlineCap : ∀ b, S.kind b = .line → (S.support b).card ≤ 6)
    (hdefect : S.defectRow ≤ 117)
    {C O MX W base budget : Nat}
    (hCeq : C = S.totalCircleCount)
    (hOeq : O = thirteenSixOrdinaryIncidence S)
    (hMXeq : (MX : Int) = S.subsetPivotMoment (Finset.univ \ D))
    (hWeq : W = thirteenSixWeight S D)
    (hC : C ≤ 60) (hO : 39 ≤ O) (hMX : 21 ≤ MX)
    (hWbase : W = base)
    (hbalance : 33810 + budget = 123 * 117 + 414 * base) :
    thirteenSixOpeningResidualTotal S D +
        79 * (O - 39) + 199 * (MX - 21) + 1344 * (60 - C) ≤
      budget := by
  have hcast := thirteenSixOpeningResidualTotal_cast
    S D gamma hD hgammaKind hgammaSupport hcircleCap hlineCap
  have hexpand := sum_thirteenSixOpeningFunctional_eq
    S D hpoint hD
  rw [hexpand, ← hCeq, ← hOeq, ← hMXeq, ← hWeq] at hcast
  omega

/-- The ordinary-incidence sum agrees with `3 C_3` on a geometric block
system. -/
theorem thirteenSixOrdinaryIncidence_eq_three_circleCount
    (S : BlockSystem Point Block) :
    thirteenSixOrdinaryIncidence S = 3 * S.circleCount 3 := by
  classical
  unfold thirteenSixOrdinaryIncidence
  rw [← Finset.sum_filter]
  have hfilter :
      Finset.univ.filter (fun b : Block =>
        S.kind b = .circle ∧ (S.support b).card = 3) =
        S.circleBlocksOfSize 3 := by
    ext b
    simp [BlockSystem.circleBlocksOfSize,
      BlockSystem.blocksOfKindSize, BlockSystem.blocksOfKind]
  rw [hfilter]
  simp [BlockSystem.circleCount, Nat.mul_comm]

theorem thirteenSixOrdinaryIncidence_eq_three_circleBlockCount
    {alpha : Type u} [Fintype alpha] [DecidableEq alpha]
    (cfg : Configuration alpha) :
    thirteenSixOrdinaryIncidence (blockSystem cfg) =
      3 * circleBlockCount cfg 3 := by
  simpa [circleBlockCount] using
    thirteenSixOrdinaryIncidence_eq_three_circleCount (blockSystem cfg)

/-- Blocks of one relative type. -/
def thirteenSixRelativeBlocks
    (S : BlockSystem Point Block) (D : Finset Point)
    (kind : BlockKind) (g x : Nat) : Finset Block :=
  Finset.univ.filter fun b =>
    S.kind b = kind ∧ thirteenSixInside S D b = g ∧
      thirteenSixOutside S D b = x

def thirteenSixRelativeCount
    (S : BlockSystem Point Block) (D : Finset Point)
    (kind : BlockKind) (g x : Nat) : Nat :=
  (thirteenSixRelativeBlocks S D kind g x).card

theorem thirteenSix_sum_relative_indicator
    (S : BlockSystem Point Block) (D : Finset Point)
    (kind : BlockKind) (g x a : Nat) :
    (∑ b : Block,
      if S.kind b = kind ∧ thirteenSixInside S D b = g ∧
          thirteenSixOutside S D b = x then a else 0) =
      a * thirteenSixRelativeCount S D kind g x := by
  classical
  rw [thirteenSixRelativeCount, thirteenSixRelativeBlocks,
    ← Finset.sum_filter]
  simp [Nat.mul_comm]

theorem thirteenSix_sum_relative_indicator_int
    (S : BlockSystem Point Block) (D : Finset Point)
    (kind : BlockKind) (g x : Nat) (a : Int) :
    (∑ b : Block,
      if S.kind b = kind ∧ thirteenSixInside S D b = g ∧
          thirteenSixOutside S D b = x then a else 0) =
      a * (thirteenSixRelativeCount S D kind g x : Int) := by
  classical
  rw [thirteenSixRelativeCount, thirteenSixRelativeBlocks,
    ← Finset.sum_filter]
  simp
  ring

/-- Complete classification of the zero cells of the opening table. -/
theorem thirteenSix_opening_zero_cell
    (S : BlockSystem Point Block) (D : Finset Point) (gamma b : Block)
    (hgammaSupport : S.support gamma = D)
    (hcircleCap : ∀ c, S.kind c = .circle → (S.support c).card ≤ 6)
    (hlineCap : ∀ L, S.kind L = .line → (S.support L).card ≤ 6)
    (hzero : thirteenSixOpeningResidual S D b = 0) :
    b = gamma ∨
    (S.kind b = .circle ∧ thirteenSixOpeningCircleZeroProfile
      (thirteenSixInside S D b) (thirteenSixOutside S D b)) ∨
    (S.kind b = .line ∧ thirteenSixOpeningLineZeroProfile
      (thirteenSixInside S D b) (thirteenSixOutside S D b)) := by
  by_cases hbgamma : b = gamma
  · exact Or.inl hbgamma
  · right
    have hg : thirteenSixInside S D b ≤ 2 := by
      have hinter := S.distinct_block_inter_card_lt_three hbgamma
      rw [hgammaSupport] at hinter
      exact Nat.le_of_lt_succ hinter
    have hsum := thirteenSixInside_add_thirteenSixOutside S D b
    cases hkind : S.kind b with
    | circle =>
        left
        refine ⟨rfl, ?_⟩
        have hdefect :=
          thirteenSix_blockDefectContribution_circle S D b hkind
        unfold thirteenSixOpeningResidual at hzero
        rw [hdefect] at hzero
        have hmin := S.circle_min b hkind
        have hcap := hcircleCap b hkind
        rw [← hsum] at hmin hcap
        have hx : thirteenSixOutside S D b ≤ 6 := by omega
        rw [hkind] at hzero
        change thirteenSixOpeningCircleResidual
          (thirteenSixInside S D b) (thirteenSixOutside S D b) = 0 at hzero
        exact (thirteenSix_opening_circle_table
          (thirteenSixInside S D b) (thirteenSixOutside S D b)
          hg hx hmin hcap).2.2 hzero
    | line =>
        right
        refine ⟨rfl, ?_⟩
        have hdefect :=
          thirteenSix_blockDefectContribution_line S D b hkind
        unfold thirteenSixOpeningResidual at hzero
        rw [hdefect] at hzero
        have hmin := S.line_min b hkind
        have hcap := hlineCap b hkind
        rw [← hsum] at hmin hcap
        have hx : thirteenSixOutside S D b ≤ 6 := by omega
        rw [hkind] at hzero
        change thirteenSixOpeningLineResidual
          (thirteenSixInside S D b) (thirteenSixOutside S D b) = 0 at hzero
        exact (thirteenSix_opening_line_table
          (thirteenSixInside S D b) (thirteenSixOutside S D b)
          hg hx hmin hcap).2.2 hzero

/-- The seven elementary rows on the zero-residual layer. -/
structure ThirteenSixOpeningZeroRows
    (S : BlockSystem Point Block) (D : Finset Point) : Prop where
  circleCountRow :
    S.totalCircleCount =
      1 + thirteenSixRelativeCount S D .circle 0 3 +
      thirteenSixRelativeCount S D .circle 1 2 +
      thirteenSixRelativeCount S D .circle 1 5 +
      thirteenSixRelativeCount S D .circle 2 1 +
      thirteenSixRelativeCount S D .circle 2 2 +
      thirteenSixRelativeCount S D .circle 2 3
  ordinaryRow :
    thirteenSixOrdinaryIncidence S = 3 *
      (thirteenSixRelativeCount S D .circle 0 3 +
       thirteenSixRelativeCount S D .circle 1 2 +
       thirteenSixRelativeCount S D .circle 2 1)
  weightRow :
    thirteenSixWeight S D =
      thirteenSixRelativeCount S D .circle 2 2 +
        3 * thirteenSixRelativeCount S D .circle 2 3
  row0 :
    35 = thirteenSixRelativeCount S D .circle 0 3 +
      10 * thirteenSixRelativeCount S D .circle 1 5 +
      thirteenSixRelativeCount S D .circle 2 3 +
      thirteenSixRelativeCount S D .line 0 3
  row1 :
    126 = thirteenSixRelativeCount S D .circle 1 2 +
      10 * thirteenSixRelativeCount S D .circle 1 5 +
      2 * thirteenSixRelativeCount S D .circle 2 2 +
      6 * thirteenSixRelativeCount S D .circle 2 3 +
      thirteenSixRelativeCount S D .line 1 2
  row2 :
    105 = thirteenSixRelativeCount S D .circle 2 1 +
      2 * thirteenSixRelativeCount S D .circle 2 2 +
      3 * thirteenSixRelativeCount S D .circle 2 3 +
      thirteenSixRelativeCount S D .line 2 1
  momentXRow :
    S.subsetPivotMoment (Finset.univ \ D) =
      3 * (thirteenSixRelativeCount S D .circle 0 3 : Int) +
      2 * (thirteenSixRelativeCount S D .circle 1 2 : Int) -
      10 * (thirteenSixRelativeCount S D .circle 1 5 : Int) +
      (thirteenSixRelativeCount S D .circle 2 1 : Int) -
      3 * (thirteenSixRelativeCount S D .circle 2 3 : Int) +
      3 * (thirteenSixRelativeCount S D .line 0 3 : Int) +
      2 * (thirteenSixRelativeCount S D .line 1 2 : Int) +
      (thirteenSixRelativeCount S D .line 2 1 : Int)

theorem thirteenSixOpeningZeroRows_of_residual_zero
    (S : BlockSystem Point Block) (D : Finset Point) (gamma : Block)
    (hpoint : Fintype.card Point = 13) (hD : D.card = 6)
    (hgammaKind : S.kind gamma = .circle)
    (hgammaSupport : S.support gamma = D)
    (hcircleCap : ∀ c, S.kind c = .circle → (S.support c).card ≤ 6)
    (hlineCap : ∀ L, S.kind L = .line → (S.support L).card ≤ 6)
    (htotal : thirteenSixOpeningResidualTotal S D = 0) :
    ThirteenSixOpeningZeroRows S D := by
  classical
  have hlocalZero (b : Block) :
      thirteenSixOpeningResidual S D b = 0 := by
    have hle : thirteenSixOpeningResidual S D b ≤
        thirteenSixOpeningResidualTotal S D := by
      unfold thirteenSixOpeningResidualTotal
      exact Finset.single_le_sum
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ b)
    omega
  have hcell (b : Block) := thirteenSix_opening_zero_cell
    S D gamma b hgammaSupport hcircleCap hlineCap
      (hlocalZero b)
  simp only [thirteenSixOpeningCircleZeroProfile,
    thirteenSixOpeningLineZeroProfile] at hcell
  have hgammaInside : thirteenSixInside S D gamma = 6 := by
    exact (thirteenSixInside_eq_card_of_support_eq
      S D gamma hgammaSupport).trans hD
  have hgammaOutside : thirteenSixOutside S D gamma = 0 :=
    thirteenSixOutside_eq_zero_of_support_eq S D gamma hgammaSupport
  have hcirclePoint (b : Block) :
      (if S.kind b = .circle then 1 else 0) =
        (if b = gamma then 1 else 0) +
        (if S.kind b = .circle ∧ thirteenSixInside S D b = 0 ∧
            thirteenSixOutside S D b = 3 then 1 else 0) +
        (if S.kind b = .circle ∧ thirteenSixInside S D b = 1 ∧
            thirteenSixOutside S D b = 2 then 1 else 0) +
        (if S.kind b = .circle ∧ thirteenSixInside S D b = 1 ∧
            thirteenSixOutside S D b = 5 then 1 else 0) +
        (if S.kind b = .circle ∧ thirteenSixInside S D b = 2 ∧
            thirteenSixOutside S D b = 1 then 1 else 0) +
        (if S.kind b = .circle ∧ thirteenSixInside S D b = 2 ∧
            thirteenSixOutside S D b = 2 then 1 else 0) +
        (if S.kind b = .circle ∧ thirteenSixInside S D b = 2 ∧
            thirteenSixOutside S D b = 3 then 1 else 0) := by
    by_cases hbg : b = gamma
    · subst b
      simp [hgammaKind, hgammaInside, hgammaOutside]
    · rcases hcell b with hcontra | hc | hl
      · exact (hbg hcontra).elim
      · rcases hc with ⟨hk, hc⟩
        rcases hc with hc | hc | hc | hc | hc | hc <;>
          rcases hc with ⟨hg, hx⟩ <;>
            simp [hk, hg, hx, hbg]
      · rcases hl with ⟨hk, hl⟩
        rcases hl with hl | hl | hl | hl | hl | hl <;>
          rcases hl with ⟨hg, hx⟩ <;>
            simp [hk, hg, hx, hbg]
  have hordinaryPoint (b : Block) :
      (if S.kind b = .circle ∧ (S.support b).card = 3 then 3 else 0) =
        (if S.kind b = .circle ∧ thirteenSixInside S D b = 0 ∧
            thirteenSixOutside S D b = 3 then 3 else 0) +
        (if S.kind b = .circle ∧ thirteenSixInside S D b = 1 ∧
            thirteenSixOutside S D b = 2 then 3 else 0) +
        (if S.kind b = .circle ∧ thirteenSixInside S D b = 2 ∧
            thirteenSixOutside S D b = 1 then 3 else 0) := by
    have hsum := thirteenSixInside_add_thirteenSixOutside S D b
    rcases hcell b with hbg | hc | hl
    · subst b
      simp [hgammaKind, hgammaSupport, hD, hgammaInside, hgammaOutside]
    · rcases hc with ⟨hk, hc⟩
      rcases hc with hc | hc | hc | hc | hc | hc <;>
        rcases hc with ⟨hg, hx⟩ <;>
        simp [hk, hg, hx, ← hsum]
    · rcases hl with ⟨hk, hl⟩
      rcases hl with hl | hl | hl | hl | hl | hl <;>
        rcases hl with ⟨hg, hx⟩ <;>
        simp [hk, hg, hx, ← hsum]
  have hweightPoint (b : Block) :
      (if S.kind b = .circle ∧ thirteenSixInside S D b = 2 then
          Nat.choose (thirteenSixOutside S D b) 2 else 0) =
        (if S.kind b = .circle ∧ thirteenSixInside S D b = 2 ∧
            thirteenSixOutside S D b = 2 then 1 else 0) +
        (if S.kind b = .circle ∧ thirteenSixInside S D b = 2 ∧
            thirteenSixOutside S D b = 3 then 3 else 0) := by
    rcases hcell b with hbg | hc | hl
    · subst b
      simp [hgammaKind, hgammaInside, hgammaOutside]
    · rcases hc with ⟨hk, hc⟩
      rcases hc with hc | hc | hc | hc | hc | hc <;>
        rcases hc with ⟨hg, hx⟩ <;>
        simp [hk, hg, hx]
    · rcases hl with ⟨hk, hl⟩
      rcases hl with hl | hl | hl | hl | hl | hl <;>
        rcases hl with ⟨hg, hx⟩ <;>
        simp [hk, hg, hx]
  have hrow0Point (b : Block) :
      Nat.choose (thirteenSixOutside S D b) 3 =
        (if S.kind b = .circle ∧ thirteenSixInside S D b = 0 ∧
            thirteenSixOutside S D b = 3 then 1 else 0) +
        (if S.kind b = .circle ∧ thirteenSixInside S D b = 1 ∧
            thirteenSixOutside S D b = 5 then 10 else 0) +
        (if S.kind b = .circle ∧ thirteenSixInside S D b = 2 ∧
            thirteenSixOutside S D b = 3 then 1 else 0) +
        (if S.kind b = .line ∧ thirteenSixInside S D b = 0 ∧
            thirteenSixOutside S D b = 3 then 1 else 0) := by
    rcases hcell b with hbg | hc | hl
    · subst b
      simp [hgammaKind, hgammaInside, hgammaOutside]
    · rcases hc with ⟨hk, hc⟩
      rcases hc with hc | hc | hc | hc | hc | hc <;>
        rcases hc with ⟨hg, hx⟩ <;>
        simp [hk, hg, hx, Nat.choose]
    · rcases hl with ⟨hk, hl⟩
      rcases hl with hl | hl | hl | hl | hl | hl <;>
        rcases hl with ⟨hg, hx⟩ <;>
        simp [hk, hg, hx, Nat.choose]
  have hrow1Point (b : Block) :
      thirteenSixInside S D b * Nat.choose (thirteenSixOutside S D b) 2 =
        (if S.kind b = .circle ∧ thirteenSixInside S D b = 1 ∧
            thirteenSixOutside S D b = 2 then 1 else 0) +
        (if S.kind b = .circle ∧ thirteenSixInside S D b = 1 ∧
            thirteenSixOutside S D b = 5 then 10 else 0) +
        (if S.kind b = .circle ∧ thirteenSixInside S D b = 2 ∧
            thirteenSixOutside S D b = 2 then 2 else 0) +
        (if S.kind b = .circle ∧ thirteenSixInside S D b = 2 ∧
            thirteenSixOutside S D b = 3 then 6 else 0) +
        (if S.kind b = .line ∧ thirteenSixInside S D b = 1 ∧
            thirteenSixOutside S D b = 2 then 1 else 0) := by
    rcases hcell b with hbg | hc | hl
    · subst b
      simp [hgammaKind, hgammaInside, hgammaOutside]
    · rcases hc with ⟨hk, hc⟩
      rcases hc with hc | hc | hc | hc | hc | hc <;>
        rcases hc with ⟨hg, hx⟩ <;>
        simp [hk, hg, hx, Nat.choose]
    · rcases hl with ⟨hk, hl⟩
      rcases hl with hl | hl | hl | hl | hl | hl <;>
        rcases hl with ⟨hg, hx⟩ <;>
        simp [hk, hg, hx]
  have hrow2Point (b : Block) :
      Nat.choose (thirteenSixInside S D b) 2 * thirteenSixOutside S D b =
        (if S.kind b = .circle ∧ thirteenSixInside S D b = 2 ∧
            thirteenSixOutside S D b = 1 then 1 else 0) +
        (if S.kind b = .circle ∧ thirteenSixInside S D b = 2 ∧
            thirteenSixOutside S D b = 2 then 2 else 0) +
        (if S.kind b = .circle ∧ thirteenSixInside S D b = 2 ∧
            thirteenSixOutside S D b = 3 then 3 else 0) +
        (if S.kind b = .line ∧ thirteenSixInside S D b = 2 ∧
            thirteenSixOutside S D b = 1 then 1 else 0) := by
    rcases hcell b with hbg | hc | hl
    · subst b
      simp [hgammaKind, hgammaInside, hgammaOutside, Nat.choose]
    · rcases hc with ⟨hk, hc⟩
      rcases hc with hc | hc | hc | hc | hc | hc <;>
        rcases hc with ⟨hg, hx⟩ <;>
        simp [hk, hg, hx]
    · rcases hl with ⟨hk, hl⟩
      rcases hl with hl | hl | hl | hl | hl | hl <;>
        rcases hl with ⟨hg, hx⟩ <;>
        simp [hk, hg, hx]
  have hmomentPoint (b : Block) :
      (if 3 ≤ (S.support b).card then
          (thirteenSixOutside S D b : Int) *
            (4 - ((S.support b).card : Int)) else 0) =
        (if S.kind b = .circle ∧ thirteenSixInside S D b = 0 ∧
            thirteenSixOutside S D b = 3 then 3 else 0) +
        (if S.kind b = .circle ∧ thirteenSixInside S D b = 1 ∧
            thirteenSixOutside S D b = 2 then 2 else 0) -
        (if S.kind b = .circle ∧ thirteenSixInside S D b = 1 ∧
            thirteenSixOutside S D b = 5 then 10 else 0) +
        (if S.kind b = .circle ∧ thirteenSixInside S D b = 2 ∧
            thirteenSixOutside S D b = 1 then 1 else 0) -
        (if S.kind b = .circle ∧ thirteenSixInside S D b = 2 ∧
            thirteenSixOutside S D b = 3 then 3 else 0) +
        (if S.kind b = .line ∧ thirteenSixInside S D b = 0 ∧
            thirteenSixOutside S D b = 3 then 3 else 0) +
        (if S.kind b = .line ∧ thirteenSixInside S D b = 1 ∧
            thirteenSixOutside S D b = 2 then 2 else 0) +
        (if S.kind b = .line ∧ thirteenSixInside S D b = 2 ∧
            thirteenSixOutside S D b = 1 then 1 else 0) := by
    have hsum := thirteenSixInside_add_thirteenSixOutside S D b
    rcases hcell b with hbg | hc | hl
    · subst b
      simp [hgammaKind, hgammaSupport, hD, hgammaInside, hgammaOutside]
    · rcases hc with ⟨hk, hc⟩
      rcases hc with hc | hc | hc | hc | hc | hc <;>
        rcases hc with ⟨hg, hx⟩ <;>
        norm_num [hk, hg, hx, ← hsum]
    · rcases hl with ⟨hk, hl⟩
      rcases hl with hl | hl | hl | hl | hl | hl <;>
        rcases hl with ⟨hg, hx⟩ <;>
        norm_num [hk, hg, hx, ← hsum]
  constructor
  · calc
      S.totalCircleCount =
          ∑ b : Block, if S.kind b = .circle then 1 else 0 := by
        simp [BlockSystem.totalCircleCount, BlockSystem.blocksOfKind]
      _ = ∑ b : Block,
          ((if b = gamma then 1 else 0) +
          (if S.kind b = .circle ∧ thirteenSixInside S D b = 0 ∧
              thirteenSixOutside S D b = 3 then 1 else 0) +
          (if S.kind b = .circle ∧ thirteenSixInside S D b = 1 ∧
              thirteenSixOutside S D b = 2 then 1 else 0) +
          (if S.kind b = .circle ∧ thirteenSixInside S D b = 1 ∧
              thirteenSixOutside S D b = 5 then 1 else 0) +
          (if S.kind b = .circle ∧ thirteenSixInside S D b = 2 ∧
              thirteenSixOutside S D b = 1 then 1 else 0) +
          (if S.kind b = .circle ∧ thirteenSixInside S D b = 2 ∧
              thirteenSixOutside S D b = 2 then 1 else 0) +
          (if S.kind b = .circle ∧ thirteenSixInside S D b = 2 ∧
              thirteenSixOutside S D b = 3 then 1 else 0)) := by
        apply Fintype.sum_congr
        exact hcirclePoint
      _ = _ := by
        simp only [Finset.sum_add_distrib]
        rw [thirteenSix_sum_relative_indicator,
          thirteenSix_sum_relative_indicator,
          thirteenSix_sum_relative_indicator,
          thirteenSix_sum_relative_indicator,
          thirteenSix_sum_relative_indicator,
          thirteenSix_sum_relative_indicator]
        simp
  · unfold thirteenSixOrdinaryIncidence
    simp_rw [hordinaryPoint]
    simp only [Finset.sum_add_distrib]
    rw [thirteenSix_sum_relative_indicator,
      thirteenSix_sum_relative_indicator,
      thirteenSix_sum_relative_indicator]
    omega
  · rw [thirteenSixWeight, fourteenWeight]
    simp [fourteenTwoTraceCircles, Finset.sum_filter]
    simp_rw [hweightPoint]
    simp only [Finset.sum_add_distrib]
    rw [thirteenSix_sum_relative_indicator,
      thirteenSix_sum_relative_indicator]
    omega
  · have hrInt := (thirteenSix_relative_rows S D hpoint hD).1
    have hr :
        (∑ b : Block, Nat.choose (thirteenSixOutside S D b) 3) = 35 := by
      exact_mod_cast hrInt
    simp_rw [hrow0Point] at hr
    simp only [Finset.sum_add_distrib] at hr
    rw [thirteenSix_sum_relative_indicator,
      thirteenSix_sum_relative_indicator,
      thirteenSix_sum_relative_indicator,
      thirteenSix_sum_relative_indicator] at hr
    omega
  · have hrInt := (thirteenSix_relative_rows S D hpoint hD).2.1
    have hr :
        (∑ b : Block, thirteenSixInside S D b *
          Nat.choose (thirteenSixOutside S D b) 2) = 126 := by
      exact_mod_cast hrInt
    simp_rw [hrow1Point] at hr
    simp only [Finset.sum_add_distrib] at hr
    rw [thirteenSix_sum_relative_indicator,
      thirteenSix_sum_relative_indicator,
      thirteenSix_sum_relative_indicator,
      thirteenSix_sum_relative_indicator,
      thirteenSix_sum_relative_indicator] at hr
    omega
  · have hrInt := (thirteenSix_relative_rows S D hpoint hD).2.2.1
    have hr :
        (∑ b : Block, Nat.choose (thirteenSixInside S D b) 2 *
          thirteenSixOutside S D b) = 105 := by
      exact_mod_cast hrInt
    simp_rw [hrow2Point] at hr
    simp only [Finset.sum_add_distrib] at hr
    rw [thirteenSix_sum_relative_indicator,
      thirteenSix_sum_relative_indicator,
      thirteenSix_sum_relative_indicator,
      thirteenSix_sum_relative_indicator] at hr
    omega
  · rw [subsetPivotMoment]
    have houtside (b : Block) :
        (S.support b ∩ (Finset.univ \ D)).card =
          thirteenSixOutside S D b := by
      exact (thirteenSixOutside_eq_support_inter_compl_card S D b).symm
    simp_rw [houtside, hmomentPoint]
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
    rw [thirteenSix_sum_relative_indicator_int,
      thirteenSix_sum_relative_indicator_int,
      thirteenSix_sum_relative_indicator_int,
      thirteenSix_sum_relative_indicator_int,
      thirteenSix_sum_relative_indicator_int,
      thirteenSix_sum_relative_indicator_int,
      thirteenSix_sum_relative_indicator_int,
      thirteenSix_sum_relative_indicator_int]
    ring

/-- A harmless guard makes the zero layer name the only wall at which it
is consumed.  At `W=47` this is exactly the sum of local residuals. -/
noncomputable def thirteenSixGuardedOpeningResidual
    (S : BlockSystem Point Block) (D : Finset Point) : Nat :=
  if thirteenSixWeight S D = 47 then
    thirteenSixOpeningResidualTotal S D
  else 96 + thirteenSixOpeningResidualTotal S D

/-- All four retained opening rows are consequences of the block system.
The variable `f` is the actual `c(2,3)` multiplicity. -/
theorem thirteenSixRetainedOpeningRows_of_blockSystem
    (S : BlockSystem Point Block) (D : Finset Point) (gamma : Block)
    (hpoint : Fintype.card Point = 13) (hD : D.card = 6)
    (hgammaKind : S.kind gamma = .circle)
    (hgammaSupport : S.support gamma = D)
    (hcircleCap : ∀ c, S.kind c = .circle → (S.support c).card ≤ 6)
    (hlineCap : ∀ L, S.kind L = .line → (S.support L).card ≤ 6)
    (hdefect : S.defectRow ≤ 117)
    (hC : S.totalCircleCount ≤ 60)
    (hO : 39 ≤ thirteenSixOrdinaryIncidence S)
    (MX : Nat)
    (hMXeq : (MX : Int) = S.subsetPivotMoment (Finset.univ \ D))
    (hMX : 21 ≤ MX) :
    ThirteenSixRetainedOpeningRows S.defectRow
      S.totalCircleCount (thirteenSixOrdinaryIncidence S) MX
      (thirteenSixWeight S D)
      (thirteenSixGuardedOpeningResidual S D)
      (thirteenSixRelativeCount S D .circle 2 3) := by
  have hcast := thirteenSixOpeningResidualTotal_cast
    S D gamma hD hgammaKind hgammaSupport hcircleCap hlineCap
  have hexpand := sum_thirteenSixOpeningFunctional_eq S D hpoint hD
  rw [hexpand, ← hMXeq] at hcast
  constructor
  · omega
  · intro hW
    have hbudget := thirteenSix_opening_residual_budget
      S D gamma hpoint hD hgammaKind hgammaSupport hcircleCap hlineCap
      hdefect (C := S.totalCircleCount)
      (O := thirteenSixOrdinaryIncidence S) (MX := MX)
      (W := thirteenSixWeight S D) (base := 47) (budget := 39)
      rfl rfl hMXeq rfl hC hO hMX hW (by norm_num)
    simpa [thirteenSixGuardedOpeningResidual, hW] using hbudget
  · unfold thirteenSixGuardedOpeningResidual
    by_cases hW : thirteenSixWeight S D = 47
    · simpa [hW] using
        thirteenSixOpeningResidualTotal_eq_zero_or_ge_ninety_six
          S D gamma hD hgammaKind hgammaSupport hcircleCap hlineCap
    · right
      simp [hW]
  · intro hguardZero
    have hW : thirteenSixWeight S D = 47 := by
      by_contra hne
      simp [thirteenSixGuardedOpeningResidual, hne] at hguardZero
    have htotalZero : thirteenSixOpeningResidualTotal S D = 0 := by
      simpa [thirteenSixGuardedOpeningResidual, hW] using hguardZero
    have hbudget := thirteenSix_opening_residual_budget
      S D gamma hpoint hD hgammaKind hgammaSupport hcircleCap hlineCap
      hdefect (C := S.totalCircleCount)
      (O := thirteenSixOrdinaryIncidence S) (MX := MX)
      (W := thirteenSixWeight S D) (base := 47) (budget := 39)
      rfl rfl hMXeq rfl hC hO hMX hW (by norm_num)
    have hCeq : S.totalCircleCount = 60 := by omega
    have hOeq : thirteenSixOrdinaryIncidence S = 39 := by omega
    have hMXwall : MX = 21 := by omega
    have hz := thirteenSixOpeningZeroRows_of_residual_zero
      S D gamma hpoint hD hgammaKind hgammaSupport hcircleCap hlineCap
        htotalZero
    have hMXrow := hz.momentXRow
    rw [← hMXeq] at hMXrow
    have hc := hz.circleCountRow
    have ho := hz.ordinaryRow
    have hw := hz.weightRow
    have h0 := hz.row0
    have h1 := hz.row1
    have h2 := hz.row2
    omega

/-- The `c(0,6)` cell alone costs 2388 units in the opening residual. -/
theorem thirteenSix_c06_openingResidual_le
    (S : BlockSystem Point Block) (D : Finset Point) :
    2388 * thirteenSixRelativeCount S D .circle 0 6 ≤
      thirteenSixOpeningResidualTotal S D := by
  classical
  have hpointwise (b : Block) :
      (if S.kind b = .circle ∧ thirteenSixInside S D b = 0 ∧
          thirteenSixOutside S D b = 6 then 2388 else 0) ≤
        thirteenSixOpeningResidual S D b := by
    by_cases hcell : S.kind b = .circle ∧
        thirteenSixInside S D b = 0 ∧ thirteenSixOutside S D b = 6
    · rcases hcell with ⟨hk, hg, hx⟩
      have hdefect :=
        thirteenSix_blockDefectContribution_circle S D b hk
      unfold thirteenSixOpeningResidual
      rw [hdefect]
      norm_num [thirteenSixOpeningFunctional, hk, hg, hx, Nat.choose]
    · simp [hcell]
  have hsum := Finset.sum_le_sum
    (s := (Finset.univ : Finset Block)) fun b _hb => hpointwise b
  rw [thirteenSix_sum_relative_indicator] at hsum
  simpa [thirteenSixOpeningResidualTotal, Nat.mul_comm] using hsum

end OpeningFunctional

section SecondDual

variable {Point : Type u} {Block : Type v}
  [Fintype Point] [Fintype Block] [DecidableEq Point]

/-- The full second-added-centre residual at one block. -/
def thirteenSixSecondResidual
    (S : BlockSystem Point Block) (D : Finset Point) (b : Block) : Nat :=
  Int.toNat (4 * S.blockDefectContribution b -
    fourteenBlockFunctional (S.kind b)
      (thirteenSixInside S D b) (thirteenSixOutside S D b))

noncomputable def thirteenSixSecondResidualTotal
    (S : BlockSystem Point Block) (D : Finset Point) : Nat :=
  ∑ b : Block, thirteenSixSecondResidual S D b

/-- The numerical second-dual residual of a relative cell.  Pulling this
quantity out of the block-system context keeps the finite verification
small and reusable. -/
def thirteenSixSecondCellResidual
    (kind : BlockKind) (g x : Nat) : Nat :=
  Int.toNat (4 * fourteenBlockDefect kind g x -
    fourteenBlockFunctional kind g x)

@[simp] theorem thirteenSix_intToNat_natCast (n : Nat) :
    Int.toNat (n : Int) = n := by
  have hcast : (Int.toNat (n : Int) : Int) = (n : Int) :=
    Int.toNat_of_nonneg (by omega)
  exact_mod_cast hcast

/-- The coefficient retained from each cell in the second-dual budget. -/
def thirteenSixSecondRetainedWeight
    (kind : BlockKind) (g x : Nat) : Nat :=
  (if kind = .circle ∧ g = 0 ∧ x = 4 then 12 else 0) +
  (if kind = .circle ∧ g = 0 ∧ x = 5 then 26 else 0) +
  (if kind = .circle ∧ g = 0 ∧ x = 6 then 36 else 0) +
  (if kind = .circle ∧ g = 1 ∧ x = 3 then 3 else 0) +
  (if kind = .circle ∧ g = 1 ∧ x = 4 then 5 else 0) +
  (if kind = .circle ∧ g = 2 ∧ x = 3 then 2 else 0) +
  (if kind = .line ∧ g = 0 ∧ x = 4 then 40 else 0) +
  (if kind = .line ∧ g = 0 ∧ x = 5 then 90 else 0) +
  (if kind = .line ∧ g = 0 ∧ x = 6 then 144 else 0) +
  (if kind = .line ∧ g = 1 ∧ x = 3 then 31 else 0) +
  (if kind = .line ∧ g = 1 ∧ x = 4 then 69 else 0) +
  (if kind = .line ∧ g = 1 ∧ x = 5 then 108 else 0) +
  (if kind = .line ∧ g = 2 ∧ x = 2 then 22 else 0) +
  (if kind = .line ∧ g = 2 ∧ x = 3 then 48 else 0) +
  (if kind = .line ∧ g = 2 ∧ x = 4 then 72 else 0)

/-- Complete second-dual table for a nonselected circle. -/
theorem thirteenSix_second_circle_table
    (g x : Nat) (hg : g ≤ 2) (hx : x ≤ 6)
    (hmin : 3 ≤ g + x) (hcap : g + x ≤ 6) :
    fourteenBlockFunctional .circle g x ≤
        4 * fourteenBlockDefect .circle g x ∧
      thirteenSixSecondCellResidual .circle g x =
        thirteenSixSecondRetainedWeight .circle g x := by
  interval_cases g <;> interval_cases x <;>
    norm_num [thirteenSixSecondCellResidual,
      thirteenSixSecondRetainedWeight, fourteenBlockDefect,
      fourteenBlockFunctional, Nat.choose,
      thirteenSix_intToNat_natCast, Int.toNat] at *

/-- Complete second-dual table for a nonselected line, including the
two-point cells whose residual and retained weight are both zero. -/
theorem thirteenSix_second_line_table
    (g x : Nat) (hg : g ≤ 2) (hx : x ≤ 6)
    (hmin : 2 ≤ g + x) (hcap : g + x ≤ 6) :
    fourteenBlockFunctional .line g x ≤
        4 * fourteenBlockDefect .line g x ∧
      thirteenSixSecondCellResidual .line g x =
        thirteenSixSecondRetainedWeight .line g x := by
  interval_cases g <;> interval_cases x <;>
    norm_num [thirteenSixSecondCellResidual,
      thirteenSixSecondRetainedWeight, fourteenBlockDefect,
      fourteenBlockFunctional, Nat.choose,
      thirteenSix_intToNat_natCast, Int.toNat] at *

theorem thirteenSixSecondResidual_eq_circle
    (S : BlockSystem Point Block) (D : Finset Point) (b : Block)
    (hkind : S.kind b = .circle) :
    thirteenSixSecondResidual S D b =
      thirteenSixSecondCellResidual .circle
        (thirteenSixInside S D b) (thirteenSixOutside S D b) := by
  unfold thirteenSixSecondResidual thirteenSixSecondCellResidual
  rw [hkind, thirteenSix_blockDefectContribution_circle S D b hkind]
  rfl

theorem thirteenSixSecondResidual_eq_line
    (S : BlockSystem Point Block) (D : Finset Point) (b : Block)
    (hkind : S.kind b = .line) :
    thirteenSixSecondResidual S D b =
      thirteenSixSecondCellResidual .line
        (thirteenSixInside S D b) (thirteenSixOutside S D b) := by
  unfold thirteenSixSecondResidual thirteenSixSecondCellResidual
  rw [hkind, thirteenSix_blockDefectContribution_line S D b hkind]
  rfl

theorem thirteenSixSecondFunctional_le_blockDefect
    (S : BlockSystem Point Block) (D : Finset Point) (gamma b : Block)
    (hD : D.card = 6)
    (hgammaKind : S.kind gamma = .circle)
    (hgammaSupport : S.support gamma = D)
    (hcircleCap : ∀ c, S.kind c = .circle → (S.support c).card ≤ 6)
    (hlineCap : ∀ L, S.kind L = .line → (S.support L).card ≤ 6) :
    fourteenBlockFunctional (S.kind b)
        (thirteenSixInside S D b) (thirteenSixOutside S D b) ≤
      4 * S.blockDefectContribution b := by
  by_cases hbgamma : b = gamma
  · subst b
    have hg : thirteenSixInside S D gamma = 6 := by
      exact (thirteenSixInside_eq_card_of_support_eq
        S D gamma hgammaSupport).trans hD
    have hx : thirteenSixOutside S D gamma = 0 :=
      thirteenSixOutside_eq_zero_of_support_eq S D gamma hgammaSupport
    have hdefect : S.blockDefectContribution gamma = 12 := by
      rw [thirteenSix_blockDefectContribution_circle S D gamma hgammaKind,
        hg, hx]
      norm_num
    rw [hdefect]
    norm_num [hg, hx, hgammaKind, fourteenBlockFunctional, Nat.choose]
  · have hg : thirteenSixInside S D b ≤ 2 := by
      have hinter := S.distinct_block_inter_card_lt_three hbgamma
      rw [hgammaSupport] at hinter
      exact Nat.le_of_lt_succ hinter
    have hsum := thirteenSixInside_add_thirteenSixOutside S D b
    cases hkind : S.kind b with
    | circle =>
        have hmin := S.circle_min b hkind
        have hcap := hcircleCap b hkind
        rw [← hsum] at hmin hcap
        have hx : thirteenSixOutside S D b ≤ 6 := by omega
        have htable := thirteenSix_second_circle_table
          (thirteenSixInside S D b) (thirteenSixOutside S D b)
          hg hx hmin hcap
        rw [thirteenSix_blockDefectContribution_circle S D b hkind]
        exact htable.1
    | line =>
        have hmin := S.line_min b hkind
        have hcap := hlineCap b hkind
        rw [← hsum] at hmin hcap
        have hx : thirteenSixOutside S D b ≤ 6 := by omega
        have htable := thirteenSix_second_line_table
          (thirteenSixInside S D b) (thirteenSixOutside S D b)
          hg hx hmin hcap
        rw [thirteenSix_blockDefectContribution_line S D b hkind]
        exact htable.1

theorem sum_fourteenBlockFunctional_eq_thirteen
    (S : BlockSystem Point Block) (D : Finset Point)
    (hpoint : Fintype.card Point = 13) (hD : D.card = 6) :
    (∑ b : Block,
      fourteenBlockFunctional (S.kind b)
        (thirteenSixInside S D b) (thirteenSixOutside S D b)) =
      2724 + 3 * S.subsetPivotMoment D +
        6 * S.subsetPivotMoment (Finset.univ \ D) -
        36 * (S.totalCircleCount : Int) -
        6 * (thirteenSixWeight S D : Int) := by
  classical
  obtain ⟨hrow0, hrow1, hrow2, hrow3⟩ :=
    thirteenSix_relative_rows S D hpoint hD
  have hmomentD :
      (∑ b : Block,
        if 3 ≤ thirteenSixInside S D b + thirteenSixOutside S D b then
          (thirteenSixInside S D b : Int) *
            (4 - ((thirteenSixInside S D b +
              thirteenSixOutside S D b : Nat) : Int))
        else 0) = S.subsetPivotMoment D := by
    rw [subsetPivotMoment]
    apply Fintype.sum_congr
    intro b
    rw [thirteenSixInside_add_thirteenSixOutside,
      thirteenSixInside_eq_support_inter_card]
  have hmomentX :
      (∑ b : Block,
        if 3 ≤ thirteenSixInside S D b + thirteenSixOutside S D b then
          (thirteenSixOutside S D b : Int) *
            (4 - ((thirteenSixInside S D b +
              thirteenSixOutside S D b : Nat) : Int))
        else 0) = S.subsetPivotMoment (Finset.univ \ D) := by
    rw [subsetPivotMoment]
    apply Fintype.sum_congr
    intro b
    rw [thirteenSixInside_add_thirteenSixOutside,
      thirteenSixOutside_eq_support_inter_compl_card]
  have hcircle :
      (∑ b : Block, if S.kind b = .circle then (36 : Int) else 0) =
        36 * (S.totalCircleCount : Int) := by
    rw [← Finset.sum_filter]
    simp [BlockSystem.totalCircleCount, BlockSystem.blocksOfKind]
    ring
  have hweight :
      (∑ b : Block,
        if S.kind b = .circle ∧ thirteenSixInside S D b = 2 then
          (Nat.choose (thirteenSixOutside S D b) 2 : Int)
        else 0) = (thirteenSixWeight S D : Int) := by
    rw [thirteenSixWeight, fourteenWeight, Nat.cast_sum]
    simp [fourteenTwoTraceCircles, Finset.sum_filter]
  have hpointwise (b : Block) :
      fourteenBlockFunctional (S.kind b)
          (thirteenSixInside S D b) (thirteenSixOutside S D b) =
        6 * (Nat.choose (thirteenSixOutside S D b) 3 : Int) +
        9 * ((thirteenSixInside S D b : Int) *
          (Nat.choose (thirteenSixOutside S D b) 2 : Int)) +
        12 * ((Nat.choose (thirteenSixInside S D b) 2 : Int) *
          (thirteenSixOutside S D b : Int)) +
        6 * (Nat.choose (thirteenSixInside S D b) 3 : Int) +
        3 * (if 3 ≤ thirteenSixInside S D b + thirteenSixOutside S D b
          then (thirteenSixInside S D b : Int) *
            (4 - ((thirteenSixInside S D b +
              thirteenSixOutside S D b : Nat) : Int)) else 0) +
        6 * (if 3 ≤ thirteenSixInside S D b + thirteenSixOutside S D b
          then (thirteenSixOutside S D b : Int) *
            (4 - ((thirteenSixInside S D b +
              thirteenSixOutside S D b : Nat) : Int)) else 0) -
        (if S.kind b = .circle then 36 else 0) -
        6 * (if S.kind b = .circle ∧ thirteenSixInside S D b = 2
          then (Nat.choose (thirteenSixOutside S D b) 2 : Int)
          else 0) := by
    by_cases hthree :
      3 ≤ thirteenSixInside S D b + thirteenSixOutside S D b
    <;> simp [fourteenBlockFunctional, hthree]
    <;> ring
  simp_rw [hpointwise]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ← Finset.mul_sum]
  rw [hrow0, hrow1, hrow2, hrow3, hmomentD, hmomentX,
    hcircle, hweight]
  ring

theorem thirteenSixSecondResidualTotal_cast
    (S : BlockSystem Point Block) (D : Finset Point) (gamma : Block)
    (hD : D.card = 6)
    (hgammaKind : S.kind gamma = .circle)
    (hgammaSupport : S.support gamma = D)
    (hcircleCap : ∀ c, S.kind c = .circle → (S.support c).card ≤ 6)
    (hlineCap : ∀ L, S.kind L = .line → (S.support L).card ≤ 6) :
    (thirteenSixSecondResidualTotal S D : Int) =
      4 * S.defectRow -
        ∑ b : Block,
          fourteenBlockFunctional (S.kind b)
            (thirteenSixInside S D b) (thirteenSixOutside S D b) := by
  classical
  unfold thirteenSixSecondResidualTotal thirteenSixSecondResidual
  rw [Nat.cast_sum, S.defectRow_eq_sum_blockDefectContribution,
    Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro b _hb
  rw [Int.toNat_of_nonneg]
  exact sub_nonneg.mpr
    (thirteenSixSecondFunctional_le_blockDefect
      S D gamma b hD hgammaKind hgammaSupport hcircleCap hlineCap)

/-- The named nonzero cells retained in the second-dual budget. -/
def thirteenSixSecondRetainedTotal
    (S : BlockSystem Point Block) (D : Finset Point) : Nat :=
  12 * thirteenSixRelativeCount S D .circle 0 4 +
  26 * thirteenSixRelativeCount S D .circle 0 5 +
  36 * thirteenSixRelativeCount S D .circle 0 6 +
  3 * thirteenSixRelativeCount S D .circle 1 3 +
  5 * thirteenSixRelativeCount S D .circle 1 4 +
  2 * thirteenSixRelativeCount S D .circle 2 3 +
  40 * thirteenSixRelativeCount S D .line 0 4 +
  90 * thirteenSixRelativeCount S D .line 0 5 +
  144 * thirteenSixRelativeCount S D .line 0 6 +
  31 * thirteenSixRelativeCount S D .line 1 3 +
  69 * thirteenSixRelativeCount S D .line 1 4 +
  108 * thirteenSixRelativeCount S D .line 1 5 +
  22 * thirteenSixRelativeCount S D .line 2 2 +
  48 * thirteenSixRelativeCount S D .line 2 3 +
  72 * thirteenSixRelativeCount S D .line 2 4

theorem thirteenSixSecondRetainedTotal_le_residual
    (S : BlockSystem Point Block) (D : Finset Point) (gamma : Block)
    (hD : D.card = 6)
    (hgammaKind : S.kind gamma = .circle)
    (hgammaSupport : S.support gamma = D)
    (hcircleCap : ∀ c, S.kind c = .circle → (S.support c).card ≤ 6)
    (hlineCap : ∀ L, S.kind L = .line → (S.support L).card ≤ 6) :
    thirteenSixSecondRetainedTotal S D ≤
      thirteenSixSecondResidualTotal S D := by
  classical
  have hpointwise (b : Block) :
      thirteenSixSecondRetainedWeight (S.kind b)
          (thirteenSixInside S D b) (thirteenSixOutside S D b) ≤
        thirteenSixSecondResidual S D b := by
    by_cases hbgamma : b = gamma
    · subst b
      have hg : thirteenSixInside S D gamma = 6 := by
        exact (thirteenSixInside_eq_card_of_support_eq
          S D gamma hgammaSupport).trans hD
      have hx : thirteenSixOutside S D gamma = 0 :=
        thirteenSixOutside_eq_zero_of_support_eq S D gamma hgammaSupport
      have hdefect : S.blockDefectContribution gamma = 12 := by
        rw [thirteenSix_blockDefectContribution_circle S D gamma hgammaKind,
          hg, hx]
        norm_num
      unfold thirteenSixSecondResidual
      rw [hdefect]
      norm_num [thirteenSixSecondRetainedWeight, hg, hx, hgammaKind,
        fourteenBlockFunctional, Nat.choose]
    · have hg : thirteenSixInside S D b ≤ 2 := by
        have hinter := S.distinct_block_inter_card_lt_three hbgamma
        rw [hgammaSupport] at hinter
        exact Nat.le_of_lt_succ hinter
      have hsum := thirteenSixInside_add_thirteenSixOutside S D b
      cases hkind : S.kind b with
      | circle =>
          have hmin := S.circle_min b hkind
          have hcap := hcircleCap b hkind
          rw [← hsum] at hmin hcap
          have hx : thirteenSixOutside S D b ≤ 6 := by omega
          have htable := thirteenSix_second_circle_table
            (thirteenSixInside S D b) (thirteenSixOutside S D b)
            hg hx hmin hcap
          rw [thirteenSixSecondResidual_eq_circle S D b hkind]
          exact Nat.le_of_eq htable.2.symm
      | line =>
          have hmin := S.line_min b hkind
          have hcap := hlineCap b hkind
          rw [← hsum] at hmin hcap
          have hx : thirteenSixOutside S D b ≤ 6 := by omega
          have htable := thirteenSix_second_line_table
            (thirteenSixInside S D b) (thirteenSixOutside S D b)
            hg hx hmin hcap
          rw [thirteenSixSecondResidual_eq_line S D b hkind]
          exact Nat.le_of_eq htable.2.symm
  have hsumLe := Finset.sum_le_sum
    (s := (Finset.univ : Finset Block)) fun b _hb => hpointwise b
  simp only [thirteenSixSecondRetainedWeight,
    Finset.sum_add_distrib] at hsumLe
  rw [thirteenSix_sum_relative_indicator,
    thirteenSix_sum_relative_indicator,
    thirteenSix_sum_relative_indicator,
    thirteenSix_sum_relative_indicator,
    thirteenSix_sum_relative_indicator,
    thirteenSix_sum_relative_indicator,
    thirteenSix_sum_relative_indicator,
    thirteenSix_sum_relative_indicator,
    thirteenSix_sum_relative_indicator,
    thirteenSix_sum_relative_indicator,
    thirteenSix_sum_relative_indicator,
    thirteenSix_sum_relative_indicator,
    thirteenSix_sum_relative_indicator,
    thirteenSix_sum_relative_indicator,
    thirteenSix_sum_relative_indicator] at hsumLe
  simpa [thirteenSixSecondRetainedTotal, thirteenSixSecondResidualTotal,
    Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hsumLe

/-- The full retained second-dual budget, including the forced vanishing of
the outsider five- and six-lines. -/
theorem thirteenSix_second_budget_of_blockSystem
    (S : BlockSystem Point Block) (D : Finset Point) (gamma : Block)
    (hpoint : Fintype.card Point = 13) (hD : D.card = 6)
    (hgammaKind : S.kind gamma = .circle)
    (hgammaSupport : S.support gamma = D)
    (hcircleCap : ∀ c, S.kind c = .circle → (S.support c).card ≤ 6)
    (hlineCap : ∀ L, S.kind L = .line → (S.support L).card ≤ 6)
    (hdefect : S.defectRow ≤ 117)
    {u v d r : Nat}
    (hGamma : S.subsetPivotMoment D = (18 + v : Nat))
    (hX : S.subsetPivotMoment (Finset.univ \ D) = (21 + u : Nat))
    (hC : S.totalCircleCount + d = 60)
    (hW : thirteenSixWeight S D = 48 + r)
    (hr : r ≤ 6) :
    thirteenSixRelativeCount S D .line 0 5 = 0 ∧
    thirteenSixRelativeCount S D .line 0 6 = 0 ∧
    thirteenSixRelativeCount S D .line 1 4 = 0 ∧
    thirteenSixRelativeCount S D .line 1 5 = 0 ∧
    thirteenSixRelativeCount S D .line 2 4 = 0 ∧
    12 * thirteenSixRelativeCount S D .circle 0 4 +
      26 * thirteenSixRelativeCount S D .circle 0 5 +
      36 * thirteenSixRelativeCount S D .circle 0 6 +
      3 * thirteenSixRelativeCount S D .circle 1 3 +
      5 * thirteenSixRelativeCount S D .circle 1 4 +
      2 * thirteenSixRelativeCount S D .circle 2 3 +
      40 * thirteenSixRelativeCount S D .line 0 4 +
      31 * thirteenSixRelativeCount S D .line 1 3 +
      22 * thirteenSixRelativeCount S D .line 2 2 +
      48 * thirteenSixRelativeCount S D .line 2 3 +
      6 * u + 3 * v + 36 * d ≤ 12 + 6 * r := by
  have hcast := thirteenSixSecondResidualTotal_cast
    S D gamma hD hgammaKind hgammaSupport hcircleCap hlineCap
  have hexpand := sum_fourteenBlockFunctional_eq_thirteen
    S D hpoint hD
  rw [hexpand, hGamma, hX] at hcast
  have hret := thirteenSixSecondRetainedTotal_le_residual
    S D gamma hD hgammaKind hgammaSupport hcircleCap hlineCap
  have hfull :
      thirteenSixSecondRetainedTotal S D + 6 * u + 3 * v + 36 * d ≤
        12 + 6 * r := by
    omega
  unfold thirteenSixSecondRetainedTotal at hfull
  constructor
  · omega
  constructor
  · omega
  constructor
  · omega
  constructor
  · omega
  constructor <;> omega

end SecondDual

section SignatureEvents

variable {alpha : Type u} [Fintype alpha] [DecidableEq alpha]

noncomputable def thirteenSixSignatureFiber
    (cfg : Configuration alpha) (gamma : DeterminedCircle cfg)
    (X : Finset alpha) (s : Finset (Finset alpha)) :
    Finset (Finset alpha) :=
  (sixConicFullEdges cfg gamma X).filter fun e =>
    sixConicSignature cfg gamma e = s

theorem thirteenSix_signatureFiber_card_le_three
    (cfg : Configuration alpha) (gamma : DeterminedCircle cfg)
    (hgamma : (circleTrace cfg gamma.1).card = 6)
    (X : Finset alpha) (hX : X.card = 7)
    (hdisjoint : Disjoint (circleTrace cfg gamma.1) X)
    (s : Finset (Finset alpha)) :
    (thirteenSixSignatureFiber cfg gamma X s).card ≤ 3 := by
  classical
  have hpack := Erdos506.Finite.card_mul_choose_le_choose_of_pairwise_inter_lt
    X (thirteenSixSignatureFiber cfg gamma X s) 2 1
  have hsub : ∀ e ∈ thirteenSixSignatureFiber cfg gamma X s, e ⊆ X := by
    intro e he
    exact (Finset.mem_powersetCard.mp
      (mem_sixConicFullEdges.mp (Finset.mem_filter.mp he).1).1).1
  have hcard : ∀ e ∈ thirteenSixSignatureFiber cfg gamma X s,
      e.card = 2 := by
    intro e he
    exact (Finset.mem_powersetCard.mp
      (mem_sixConicFullEdges.mp (Finset.mem_filter.mp he).1).1).2
  have hinter : ∀ e ∈ thirteenSixSignatureFiber cfg gamma X s,
      ∀ f ∈ thirteenSixSignatureFiber cfg gamma X s, e ≠ f →
        (e ∩ f).card < 1 := by
    intro e he f hf hef
    have he' := Finset.mem_filter.mp he
    have hf' := Finset.mem_filter.mp hf
    have hdisj := sixConic_equal_full_signatures_disjoint
      cfg gamma hgamma X hdisjoint he'.1 hf'.1 hef (he'.2.trans hf'.2.symm)
    rw [Finset.disjoint_iff_inter_eq_empty] at hdisj
    simp [hdisj]
  have h := hpack hsub hcard hinter
  norm_num [hX, Nat.choose] at h
  omega

theorem thirteenSix_fullEdges_card_le_twelve
    (cfg : Configuration alpha) (gamma : DeterminedCircle cfg)
    (hgamma : (circleTrace cfg gamma.1).card = 6)
    (X : Finset alpha) (hX : X.card = 7)
    (hdisjoint : Disjoint (circleTrace cfg gamma.1) X) :
    (sixConicFullEdges cfg gamma X).card ≤ 12 := by
  classical
  let A := sixConicActiveSignatures cfg gamma X
  let F := sixConicFullEdges cfg gamma X
  let fiber := thirteenSixSignatureFiber cfg gamma X
  have hcover : F = A.biUnion fiber := by
    ext e
    constructor
    · intro he
      have hs : sixConicSignature cfg gamma e ∈ A := by
        exact Finset.mem_image.mpr ⟨e, he, rfl⟩
      exact Finset.mem_biUnion.mpr
        ⟨sixConicSignature cfg gamma e, hs,
          Finset.mem_filter.mpr ⟨he, rfl⟩⟩
    · intro he
      rcases Finset.mem_biUnion.mp he with ⟨s, _hs, hes⟩
      exact (Finset.mem_filter.mp hes).1
  have hcardUnion : F.card ≤ ∑ s ∈ A, (fiber s).card := by
    rw [hcover]
    exact Finset.card_biUnion_le
  have hfiber : ∀ s ∈ A, (fiber s).card ≤ 3 := by
    intro s _hs
    exact thirteenSix_signatureFiber_card_le_three
      cfg gamma hgamma X hX hdisjoint s
  have hsum : (∑ s ∈ A, (fiber s).card) ≤ 3 * A.card := by
    calc
      (∑ s ∈ A, (fiber s).card) ≤ ∑ _s ∈ A, 3 := by
        exact Finset.sum_le_sum fun s hs => hfiber s hs
      _ = 3 * A.card := by simp [Nat.mul_comm]
  have hA : A.card ≤ 4 :=
    sixConic_activeSignatures_card_le_four
      cfg gamma hgamma X hdisjoint
  change F.card ≤ 12
  omega

/-- A full edge is exactly a pair whose local weight reaches three; this
is the pointwise estimate used by both global weight bounds. -/
theorem thirteenSix_pairWeight_le_two_add_fullIndicator
    (cfg : Configuration alpha) (gamma : DeterminedCircle cfg)
    (hgamma : (circleTrace cfg gamma.1).card = 6)
    (X : Finset alpha)
    (hdisjoint : Disjoint (circleTrace cfg gamma.1) X)
    (e : Finset alpha) (he : e ∈ X.powersetCard 2) :
    sixConicPairWeight cfg gamma e ≤
      2 + if e ∈ sixConicFullEdges cfg gamma X then 1 else 0 := by
  have heSpec := Finset.mem_powersetCard.mp he
  have heDisjoint : Disjoint e (circleTrace cfg gamma.1) :=
    hdisjoint.symm.mono_left heSpec.1
  have hq := sixConicPairWeight_le_three hgamma heSpec.2 heDisjoint
  by_cases hfull : e ∈ sixConicFullEdges cfg gamma X
  · simp only [hfull, if_true]
    omega
  · have hne : sixConicPairWeight cfg gamma e ≠ 3 := by
      intro hthree
      exact hfull (mem_sixConicFullEdges.mpr ⟨he, hthree⟩)
    simp only [hfull, if_false]
    omega

theorem thirteenSix_sum_fullEdge_indicator
    (cfg : Configuration alpha) (gamma : DeterminedCircle cfg)
    (X : Finset alpha) :
    (∑ e ∈ X.powersetCard 2,
      if e ∈ sixConicFullEdges cfg gamma X then 1 else 0) =
      (sixConicFullEdges cfg gamma X).card := by
  classical
  have hfilter :
      (X.powersetCard 2).filter
          (fun e => e ∈ sixConicFullEdges cfg gamma X) =
        sixConicFullEdges cfg gamma X := by
    ext e
    simp only [Finset.mem_filter]
    constructor
    · exact fun h => h.2
    · intro he
      exact ⟨(mem_sixConicFullEdges.mp he).1, he⟩
  rw [← Finset.sum_filter, hfilter]
  simp

/-- Summing the local pair estimate over the 21 outsider pairs. -/
theorem thirteenSix_weight_le_forty_two_add_fullEdges
    (cfg : Configuration alpha) (gamma : DeterminedCircle cfg)
    (hgamma : (circleTrace cfg gamma.1).card = 6)
    (X : Finset alpha) (hX : X.card = 7)
    (hdisjoint : Disjoint (circleTrace cfg gamma.1) X) :
    sixConicWeight cfg gamma X ≤
      42 + (sixConicFullEdges cfg gamma X).card := by
  classical
  have hsum := Finset.sum_le_sum fun e he =>
    thirteenSix_pairWeight_le_two_add_fullIndicator
      cfg gamma hgamma X hdisjoint e he
  change sixConicTotalWeight cfg gamma X ≤ _ at hsum
  rw [sixConicTotalWeight_eq_sixConicWeight] at hsum
  have hpairCard : (X.powersetCard 2).card = 21 := by
    rw [Finset.card_powersetCard, hX]
    norm_num [Nat.choose]
  have hindicator := thirteenSix_sum_fullEdge_indicator cfg gamma X
  simp only [Finset.sum_add_distrib, Finset.sum_const,
    nsmul_eq_mul] at hsum
  rw [hpairCard, hindicator] at hsum
  omega

theorem thirteenSix_weight_le_fifty_four
    (cfg : Configuration alpha) (gamma : DeterminedCircle cfg)
    (hgamma : (circleTrace cfg gamma.1).card = 6)
    (X : Finset alpha) (hX : X.card = 7)
    (hdisjoint : Disjoint (circleTrace cfg gamma.1) X) :
    sixConicWeight cfg gamma X ≤ 54 := by
  have hsum := thirteenSix_weight_le_forty_two_add_fullEdges
    cfg gamma hgamma X hX hdisjoint
  have hF := thirteenSix_fullEdges_card_le_twelve
    cfg gamma hgamma X hX hdisjoint
  omega

theorem thirteenSix_fullEdges_lower_of_weight
    (cfg : Configuration alpha) (gamma : DeterminedCircle cfg)
    (hgamma : (circleTrace cfg gamma.1).card = 6)
    (X : Finset alpha) (hX : X.card = 7)
    (hdisjoint : Disjoint (circleTrace cfg gamma.1) X)
    {W r : Nat} (hWsemantic : W = sixConicWeight cfg gamma X)
    (hWr : W = 48 + r) :
    6 + r ≤ (sixConicFullEdges cfg gamma X).card := by
  have hsum := thirteenSix_weight_le_forty_two_add_fullEdges
    cfg gamma hgamma X hX hdisjoint
  rw [← hWsemantic, hWr] at hsum
  omega

/-- Repetition events are exactly the disjoint union of the two-subsets of
the active signature fibers. -/
theorem thirteenSix_repetitionEvents_card_eq_sum_choose_fibers
    (cfg : Configuration alpha) (gamma : DeterminedCircle cfg)
    (X : Finset alpha) :
    (sixConicRepetitionEvents cfg gamma X).card =
      ∑ s ∈ sixConicActiveSignatures cfg gamma X,
        Nat.choose (thirteenSixSignatureFiber cfg gamma X s).card 2 := by
  classical
  let A := sixConicActiveSignatures cfg gamma X
  let fiber := thirteenSixSignatureFiber cfg gamma X
  have hcover : sixConicRepetitionEvents cfg gamma X =
      A.biUnion fun s => (fiber s).powersetCard 2 := by
    ext E
    constructor
    · intro hE
      have hspec := mem_sixConicRepetitionEvents.mp hE
      obtain ⟨e, f, hef, hEeq⟩ :=
        Finset.card_eq_two.mp (Finset.mem_powersetCard.mp hspec.1).2
      have heE : e ∈ E := by simp [hEeq]
      have hfE : f ∈ E := by simp [hEeq]
      let s := sixConicSignature cfg gamma e
      have hs : s ∈ A := by
        exact Finset.mem_image.mpr
          ⟨e, (Finset.mem_powersetCard.mp hspec.1).1 heE, rfl⟩
      have hEfiber : E ⊆ fiber s := by
        intro q hq
        exact Finset.mem_filter.mpr
          ⟨(Finset.mem_powersetCard.mp hspec.1).1 hq,
            hspec.2 q hq e heE⟩
      exact Finset.mem_biUnion.mpr ⟨s, hs,
        Finset.mem_powersetCard.mpr
          ⟨hEfiber, (Finset.mem_powersetCard.mp hspec.1).2⟩⟩
    · intro hE
      rcases Finset.mem_biUnion.mp hE with ⟨s, _hs, hEfiber⟩
      have hpow := Finset.mem_powersetCard.mp hEfiber
      apply mem_sixConicRepetitionEvents.mpr
      constructor
      · exact Finset.mem_powersetCard.mpr
          ⟨fun e he => (Finset.mem_filter.mp (hpow.1 he)).1, hpow.2⟩
      · intro e he f hf
        exact (Finset.mem_filter.mp (hpow.1 he)).2.trans
          (Finset.mem_filter.mp (hpow.1 hf)).2.symm
  have hdisjoint : (A : Set (Finset (Finset alpha))).PairwiseDisjoint
      (fun s => (fiber s).powersetCard 2) := by
    intro s _hs t _ht hst
    change Disjoint ((fiber s).powersetCard 2) ((fiber t).powersetCard 2)
    rw [Finset.disjoint_left]
    intro E hEs hEt
    have hsPow := Finset.mem_powersetCard.mp hEs
    obtain ⟨e, he⟩ : E.Nonempty := Finset.card_pos.mp (by omega)
    have hes := Finset.mem_filter.mp (hsPow.1 he)
    have het := Finset.mem_filter.mp
      ((Finset.mem_powersetCard.mp hEt).1 he)
    exact hst (hes.2.symm.trans het.2)
  rw [hcover, Finset.card_biUnion hdisjoint]
  apply Finset.sum_congr rfl
  intro s _hs
  rw [Finset.card_powersetCard]

theorem thirteenSix_repetition_lower
    (cfg : Configuration alpha) (gamma : DeterminedCircle cfg)
    (hgamma : (circleTrace cfg gamma.1).card = 6)
    (X : Finset alpha) (hX : X.card = 7)
    (hdisjoint : Disjoint (circleTrace cfg gamma.1) X)
    {r : Nat}
    (hfull : 6 + r ≤ (sixConicFullEdges cfg gamma X).card)
    (hr : r ≤ 6) :
    thirteenSixRho r ≤ (sixConicRepetitionEvents cfg gamma X).card := by
  classical
  let A := sixConicActiveSignatures cfg gamma X
  let fiber := thirteenSixSignatureFiber cfg gamma X
  have hA : A.card ≤ 4 :=
    sixConic_activeSignatures_card_le_four
      cfg gamma hgamma X hdisjoint
  have hfiberCard (s : Finset (Finset alpha)) (hs : s ∈ A) :
      1 ≤ (fiber s).card ∧ (fiber s).card ≤ 3 := by
    have hsImage := Finset.mem_image.mp hs
    obtain ⟨e, he, hes⟩ := hsImage
    have heFiber : e ∈ fiber s := by
      exact Finset.mem_filter.mpr ⟨he, hes⟩
    exact ⟨Finset.card_pos.mpr ⟨e, heFiber⟩,
      thirteenSix_signatureFiber_card_le_three
        cfg gamma hgamma X hX hdisjoint s⟩
  have hsumFiber :
      (∑ s ∈ A, (fiber s).card) =
        (sixConicFullEdges cfg gamma X).card := by
    let F := sixConicFullEdges cfg gamma X
    have hcover : F = A.biUnion fiber := by
      ext e
      constructor
      · intro he
        exact Finset.mem_biUnion.mpr
          ⟨sixConicSignature cfg gamma e,
            Finset.mem_image.mpr ⟨e, he, rfl⟩,
            Finset.mem_filter.mpr ⟨he, rfl⟩⟩
      · intro he
        rcases Finset.mem_biUnion.mp he with ⟨s, _hs, hes⟩
        exact (Finset.mem_filter.mp hes).1
    have hdisjoint : (A : Set (Finset (Finset alpha))).PairwiseDisjoint
        fiber := by
      intro s _hs t _ht hst
      change Disjoint (fiber s) (fiber t)
      rw [Finset.disjoint_left]
      intro e hes het
      exact hst ((Finset.mem_filter.mp hes).2.symm.trans
        (Finset.mem_filter.mp het).2)
    change (∑ s ∈ A, (fiber s).card) = F.card
    rw [hcover, Finset.card_biUnion hdisjoint]
  have hevents :=
    thirteenSix_repetitionEvents_card_eq_sum_choose_fibers cfg gamma X
  change (sixConicRepetitionEvents cfg gamma X).card =
    ∑ s ∈ A, Nat.choose (fiber s).card 2 at hevents
  have hfirst :
      (∑ s ∈ A, (fiber s).card) ≤
        (∑ s ∈ A, Nat.choose (fiber s).card 2) + A.card := by
    have hpoint (s : Finset (Finset alpha)) (hs : s ∈ A) :
        (fiber s).card ≤ Nat.choose (fiber s).card 2 + 1 := by
      rcases hfiberCard s hs with ⟨hlower, hupper⟩
      interval_cases (fiber s).card <;> norm_num [Nat.choose] at *
    have h := Finset.sum_le_sum hpoint
    simpa [Finset.sum_add_distrib] using h
  have hsecond :
      2 * (∑ s ∈ A, (fiber s).card) ≤
        (∑ s ∈ A, Nat.choose (fiber s).card 2) + 3 * A.card := by
    have hpoint (s : Finset (Finset alpha)) (hs : s ∈ A) :
        2 * (fiber s).card ≤ Nat.choose (fiber s).card 2 + 3 := by
      rcases hfiberCard s hs with ⟨hlower, hupper⟩
      interval_cases (fiber s).card <;> norm_num [Nat.choose] at *
    have h := Finset.sum_le_sum hpoint
    simp only [← Finset.mul_sum, Finset.sum_add_distrib] at h
    simpa [Nat.mul_comm] using h
  rw [hsumFiber, ← hevents] at hfirst hsecond
  interval_cases r <;> norm_num [thirteenSixRho] at * <;> omega

/-- A full signature partitions all six marked points into three pairs. -/
theorem thirteenSix_fullSignature_union_eq_gamma
    (cfg : Configuration alpha) (gamma : DeterminedCircle cfg)
    (hgamma : (circleTrace cfg gamma.1).card = 6)
    (X : Finset alpha)
    (hdisjoint : Disjoint (circleTrace cfg gamma.1) X)
    {e : Finset alpha} (he : e ∈ sixConicFullEdges cfg gamma X) :
    (sixConicSignature cfg gamma e).biUnion id =
      circleTrace cfg gamma.1 := by
  classical
  have heSpec := mem_sixConicFullEdges.mp he
  have hePow := Finset.mem_powersetCard.mp heSpec.1
  have heDisjoint : Disjoint e (circleTrace cfg gamma.1) :=
    hdisjoint.symm.mono_left hePow.1
  have hsigCard := card_sixConicSignature hePow.2 heDisjoint
  rw [heSpec.2] at hsigCard
  have hpair (p : Finset alpha) (hp : p ∈ sixConicSignature cfg gamma e) :
      p.card = 2 := (sixConicSignature_pair hp).1
  have hsub : (sixConicSignature cfg gamma e).biUnion id ⊆
      circleTrace cfg gamma.1 := by
    intro z hz
    rcases Finset.mem_biUnion.mp hz with ⟨p, hp, hzp⟩
    exact (sixConicSignature_pair hp).2 hzp
  have hpairwise :=
    sixConicSignature_pairwiseDisjoint hePow.2 heDisjoint
  have hunionCard :
      ((sixConicSignature cfg gamma e).biUnion id).card = 6 := by
    rw [Finset.card_biUnion hpairwise]
    calc
      (∑ p ∈ sixConicSignature cfg gamma e, (id p).card) =
          ∑ _p ∈ sixConicSignature cfg gamma e, 2 := by
        apply Finset.sum_congr rfl
        intro p hp
        simpa using hpair p hp
      _ = 6 := by simp [hsigCard]
  exact Finset.eq_of_subset_of_card_le hsub (by omega)

/-- If an event host meets the selected circle, it is necessarily a circle
and meets it in exactly the signature pair.  This is the host-admissibility
step used in S2. -/
theorem thirteenSix_eventHost_meeting_gamma
    (cfg : Configuration alpha) (gamma : DeterminedCircle cfg)
    (hgamma : (circleTrace cfg gamma.1).card = 6)
    (X : Finset alpha) (hdisjoint : Disjoint (circleTrace cfg gamma.1) X)
    {E : Finset (Finset alpha)}
    (hE : E ∈ sixConicRepetitionEvents cfg gamma X)
    (H : GeometricBlock cfg) (hhost : SixConicEventHostedBy cfg E H)
    (hmeet : (geometricBlockSupport cfg H ∩
      circleTrace cfg gamma.1).Nonempty) :
    geometricBlockKind H = .circle ∧
      (geometricBlockSupport cfg H ∩ circleTrace cfg gamma.1).card = 2 := by
  classical
  obtain ⟨z, hz⟩ := hmeet
  have hzH := (Finset.mem_inter.mp hz).1
  have hzGamma := (Finset.mem_inter.mp hz).2
  have hEspec := mem_sixConicRepetitionEvents.mp hE
  obtain ⟨e, heE⟩ : E.Nonempty :=
    Finset.card_pos.mp (by
      rw [(Finset.mem_powersetCard.mp hEspec.1).2]
      norm_num)
  have heFull := (Finset.mem_powersetCard.mp hEspec.1).1 heE
  have hunion := thirteenSix_fullSignature_union_eq_gamma
    cfg gamma hgamma X hdisjoint heFull
  have hzUnion : z ∈ (sixConicSignature cfg gamma e).biUnion id := by
    rw [hunion]
    exact hzGamma
  rcases Finset.mem_biUnion.mp hzUnion with ⟨p, hpSig, hzp⟩
  rw [sixConicSignature] at hpSig
  obtain ⟨c, hcPair, hp⟩ := Finset.mem_image.mp hpSig
  have heSubCircle := (mem_sixConicPairCircles.mp hcPair).1
  have heSpec := Finset.mem_powersetCard.mp
    (mem_sixConicFullEdges.mp heFull).1
  have hzNotE : z ∉ e := by
    intro hze
    exact Finset.disjoint_left.mp hdisjoint hzGamma (heSpec.1 hze)
  have hthree : (insert z e).card = 3 := by simp [hzNotE, heSpec.2]
  have hsubInter : insert z e ⊆
      geometricBlockSupport cfg H ∩ circleTrace cfg c.1 := by
    intro q hq
    rw [Finset.mem_inter]
    rcases Finset.mem_insert.mp hq with rfl | hqe
    · exact ⟨hzH, (Finset.mem_inter.mp (hp.symm ▸ hzp)).1⟩
    · constructor
      · apply hhost
        exact Finset.mem_biUnion.mpr ⟨e, heE, hqe⟩
      · exact heSubCircle hqe
  have hHeq : H = (Sum.inr c : GeometricBlock cfg) := by
    by_contra hne
    have hinter := (geometricBlockSystem cfg).distinct_block_inter_card_lt_three
      hne
    change (geometricBlockSupport cfg H ∩ circleTrace cfg c.1).card < 3
      at hinter
    have hle := Finset.card_le_card hsubInter
    omega
  subst H
  constructor
  · rfl
  · change (circleTrace cfg c.1 ∩ circleTrace cfg gamma.1).card = 2
    exact sixConicPairCircle_gammaPair_card hcPair

/-- In the two high layers, a six-outsider circle would carry every active
signature, contradicting the three-signature-on-one-host clause. -/
theorem thirteenSix_no_six_outsider_circle_of_many_fullEdges
    (cfg : Configuration alpha) (gamma : DeterminedCircle cfg)
    (hgamma : (circleTrace cfg gamma.1).card = 6)
    (X : Finset alpha) (hX : X.card = 7)
    (hdisjoint : Disjoint (circleTrace cfg gamma.1) X)
    (hfull : 11 ≤ (sixConicFullEdges cfg gamma X).card)
    (H : GeometricBlock cfg)
    (hHoutside : (geometricBlockSupport cfg H ∩ X).card = 6) : False := by
  classical
  let A := sixConicActiveSignatures cfg gamma X
  let F := sixConicFullEdges cfg gamma X
  let fiber := thirteenSixSignatureFiber cfg gamma X
  change 11 ≤ F.card at hfull
  have hA : A.card ≤ 4 :=
    sixConic_activeSignatures_card_le_four
      cfg gamma hgamma X hdisjoint
  have hfiberUpper (s : Finset (Finset alpha)) : (fiber s).card ≤ 3 :=
    thirteenSix_signatureFiber_card_le_three
      cfg gamma hgamma X hX hdisjoint s
  have hsumFiber : (∑ s ∈ A, (fiber s).card) = F.card := by
    have hcover : F = A.biUnion fiber := by
      ext e
      constructor
      · intro he
        exact Finset.mem_biUnion.mpr
          ⟨sixConicSignature cfg gamma e,
            Finset.mem_image.mpr ⟨e, he, rfl⟩,
            Finset.mem_filter.mpr ⟨he, rfl⟩⟩
      · intro he
        rcases Finset.mem_biUnion.mp he with ⟨s, _hs, hes⟩
        exact (Finset.mem_filter.mp hes).1
    have hdisjFibers : (A : Set (Finset (Finset alpha))).PairwiseDisjoint
        fiber := by
      intro s _hs t _ht hst
      change Disjoint (fiber s) (fiber t)
      rw [Finset.disjoint_left]
      intro e hes het
      exact hst ((Finset.mem_filter.mp hes).2.symm.trans
        (Finset.mem_filter.mp het).2)
    rw [hcover, Finset.card_biUnion hdisjFibers]
  have hfiberLower (s : Finset (Finset alpha)) (hs : s ∈ A) :
      2 ≤ (fiber s).card := by
    by_contra hnot
    have hsUpper : (fiber s).card ≤ 1 := by omega
    have hrest : (∑ t ∈ A.erase s, (fiber t).card) ≤
        3 * (A.erase s).card := by
      calc
        (∑ t ∈ A.erase s, (fiber t).card) ≤
            ∑ _t ∈ A.erase s, 3 := by
          exact Finset.sum_le_sum fun t _ht => hfiberUpper t
        _ = 3 * (A.erase s).card := by simp [Nat.mul_comm]
    have heraseCard : (A.erase s).card + 1 = A.card := by
      simpa [Finset.card_erase_of_mem hs] using
        (Nat.sub_add_cancel (Finset.card_pos.mpr ⟨s, hs⟩))
    have hdecomp :
        (∑ t ∈ A.erase s, (fiber t).card) + (fiber s).card =
          ∑ t ∈ A, (fiber t).card := by
      exact Finset.sum_erase_add A (fun t => (fiber t).card) hs
    omega
  have hactiveOnHost : A ⊆ sixConicSignaturesOnHost cfg gamma X H := by
    intro s hs
    have hpowersetNonempty : ((fiber s).powersetCard 2).Nonempty := by
      rw [← Finset.card_pos, Finset.card_powersetCard]
      have hs2 := hfiberLower s hs
      exact Nat.choose_pos hs2
    obtain ⟨E, hEpowerset⟩ := hpowersetNonempty
    have hEpow := Finset.mem_powersetCard.mp hEpowerset
    have hErep : E ∈ sixConicRepetitionEvents cfg gamma X := by
      apply mem_sixConicRepetitionEvents.mpr
      constructor
      · exact Finset.mem_powersetCard.mpr
          ⟨fun e he => (Finset.mem_filter.mp (hEpow.1 he)).1, hEpow.2⟩
      · intro e he f hf
        exact (Finset.mem_filter.mp (hEpow.1 he)).2.trans
          (Finset.mem_filter.mp (hEpow.1 hf)).2.symm
    have hEpairwise : (E : Set (Finset alpha)).PairwiseDisjoint id := by
      intro e he f hf hef
      exact sixConic_repetition_event_edges_disjoint
        cfg gamma hgamma X hdisjoint hErep he hf hef
    have hEedgeCard (e : Finset alpha) (he : e ∈ E) : e.card = 2 := by
      exact (Finset.mem_powersetCard.mp
        (mem_sixConicFullEdges.mp
          (Finset.mem_filter.mp (hEpow.1 he)).1).1).2
    have hUnionCard : (E.biUnion id).card = 4 := by
      rw [Finset.card_biUnion hEpairwise]
      calc
        (∑ e ∈ E, (id e).card) = ∑ _e ∈ E, 2 := by
          apply Finset.sum_congr rfl
          intro e he
          simpa using hEedgeCard e he
        _ = 4 := by simp [hEpow.2]
    have hUnionSubX : E.biUnion id ⊆ X := by
      intro z hz
      rcases Finset.mem_biUnion.mp hz with ⟨e, he, hze⟩
      exact (Finset.mem_powersetCard.mp
        (mem_sixConicFullEdges.mp
          (Finset.mem_filter.mp (hEpow.1 he)).1).1).1 hze
    obtain ⟨K, hKhost⟩ := sixConic_repetition_host_exists
      cfg gamma hgamma X hdisjoint E hErep
    have hinterThree : 3 ≤
        ((E.biUnion id) ∩ (geometricBlockSupport cfg H ∩ X)).card := by
      have hunionSub : (E.biUnion id) ∪
          (geometricBlockSupport cfg H ∩ X) ⊆ X :=
        Finset.union_subset hUnionSubX Finset.inter_subset_right
      have hunionCard := Finset.card_le_card hunionSub
      have hcount := Finset.card_union_add_card_inter
        (E.biUnion id) (geometricBlockSupport cfg H ∩ X)
      omega
    have hsubBlocks :
        (E.biUnion id) ∩ (geometricBlockSupport cfg H ∩ X) ⊆
          geometricBlockSupport cfg K ∩ geometricBlockSupport cfg H := by
      intro z hz
      have hz' := Finset.mem_inter.mp hz
      exact Finset.mem_inter.mpr ⟨hKhost hz'.1,
        (Finset.mem_inter.mp hz'.2).1⟩
    have hKH : K = H := by
      by_contra hne
      have hinter := (geometricBlockSystem cfg).distinct_block_inter_card_lt_three
        hne
      change (geometricBlockSupport cfg K ∩
        geometricBlockSupport cfg H).card < 3 at hinter
      have hle := Finset.card_le_card hsubBlocks
      omega
    subst K
    obtain ⟨e, heE⟩ : E.Nonempty := Finset.card_pos.mp (by omega)
    have heFiber := Finset.mem_filter.mp (hEpow.1 heE)
    apply Finset.mem_image.mpr
    refine ⟨e, Finset.mem_filter.mpr ⟨heFiber.1, ?_⟩, heFiber.2⟩
    intro z hze
    exact hKhost (Finset.mem_biUnion.mpr ⟨e, heE, hze⟩)
  have hhostCap := sixConicSignaturesOnHost_card_le_three
    cfg gamma hgamma X hdisjoint H
  have hAhost := Finset.card_le_card hactiveOnHost
  have hFle : F.card ≤ 3 * A.card := by
    rw [← hsumFiber]
    calc
      (∑ s ∈ A, (fiber s).card) ≤ ∑ _s ∈ A, 3 := by
        exact Finset.sum_le_sum fun s _hs => hfiberUpper s
      _ = 3 * A.card := by simp [Nat.mul_comm]
  omega

theorem thirteenSix_c06_eq_zero
    (cfg : Configuration alpha) (gamma : DeterminedCircle cfg)
    (hgamma : (circleTrace cfg gamma.1).card = 6)
    (X : Finset alpha) (hXdef : X = Finset.univ \ circleTrace cfg gamma.1)
    (hXcard : X.card = 7)
    {r : Nat} (hr : r ≤ 6)
    (hfull : 6 + r ≤ (sixConicFullEdges cfg gamma X).card)
    (hopening : thirteenSixOpeningResidualTotal (blockSystem cfg)
        (circleTrace cfg gamma.1) ≤ 453 + 414 * r) :
    thirteenSixRelativeCount (blockSystem cfg)
      (circleTrace cfg gamma.1) .circle 0 6 = 0 := by
  classical
  let S := blockSystem cfg
  let D : Finset alpha := circleTrace cfg gamma.1
  change thirteenSixOpeningResidualTotal S D ≤ 453 + 414 * r at hopening
  have hdisjoint : Disjoint D X := by simp [D, hXdef, Finset.disjoint_left]
  by_contra hne
  change thirteenSixRelativeCount S D .circle 0 6 ≠ 0 at hne
  have hpos : 0 < thirteenSixRelativeCount S D .circle 0 6 :=
    Nat.pos_of_ne_zero hne
  have hres := thirteenSix_c06_openingResidual_le S D
  by_cases hsmall : r ≤ 4
  · omega
  · have hfull11 : 11 ≤ (sixConicFullEdges cfg gamma X).card := by
      omega
    obtain ⟨H, hH⟩ : (thirteenSixRelativeBlocks S D .circle 0 6).Nonempty :=
      Finset.card_pos.mp hpos
    have hHspec := Finset.mem_filter.mp hH
    have hHoutside : (geometricBlockSupport cfg H ∩ X).card = 6 := by
      have hx := hHspec.2.2.2
      have hx' : thirteenSixOutside S D H = 6 := by
        rw [thirteenSixOutside_eq_fourteenOutside]
        exact hx
      rw [hXdef]
      change (S.support H ∩ (Finset.univ \ D)).card = 6
      rw [← thirteenSixOutside_eq_support_inter_compl_card S D H]
      exact hx'
    exact thirteenSix_no_six_outsider_circle_of_many_fullEdges
      cfg gamma hgamma X hXcard hdisjoint hfull11 H hHoutside

end SignatureEvents

section HostCapacity

variable {alpha : Type u} [Fintype alpha] [DecidableEq alpha]

/-- S2 summed over the exhaustive admissible host list. -/
theorem thirteenSix_repetition_host_capacity_of_blockSystem
    (cfg : Configuration alpha) (gamma : DeterminedCircle cfg)
    (hgamma : (circleTrace cfg gamma.1).card = 6)
    (X : Finset alpha) (hX : X = Finset.univ \ circleTrace cfg gamma.1)
    (hcircleCap : ∀ c : DeterminedCircle cfg,
      (circleTrace cfg c.1).card ≤ 6)
    (hlineCap : ∀ L : DeterminedLine cfg,
      (lineSupport cfg L).card ≤ 6)
    (hline05 : thirteenSixRelativeCount (blockSystem cfg)
      (circleTrace cfg gamma.1) .line 0 5 = 0)
    (hline06 : thirteenSixRelativeCount (blockSystem cfg)
      (circleTrace cfg gamma.1) .line 0 6 = 0) :
    (sixConicRepetitionEvents cfg gamma X).card ≤
      2 * thirteenSixRelativeCount (blockSystem cfg)
          (circleTrace cfg gamma.1) .circle 0 4 +
      3 * thirteenSixRelativeCount (blockSystem cfg)
          (circleTrace cfg gamma.1) .circle 0 5 +
      9 * thirteenSixRelativeCount (blockSystem cfg)
          (circleTrace cfg gamma.1) .circle 0 6 +
      2 * thirteenSixRelativeCount (blockSystem cfg)
          (circleTrace cfg gamma.1) .line 0 4 +
      2 * thirteenSixRelativeCount (blockSystem cfg)
          (circleTrace cfg gamma.1) .circle 2 4 := by
  classical
  let D : Finset alpha := circleTrace cfg gamma.1
  let S := blockSystem cfg
  have hdisjoint : Disjoint D X := by simp [D, hX, Finset.disjoint_left]
  have hpointwise (H : GeometricBlock cfg) :
      (sixConicEventsHostedBy cfg gamma X H).card ≤
        (if S.kind H = .circle ∧ thirteenSixInside S D H = 0 ∧
            thirteenSixOutside S D H = 4 then 2 else 0) +
        (if S.kind H = .circle ∧ thirteenSixInside S D H = 0 ∧
            thirteenSixOutside S D H = 5 then 3 else 0) +
        (if S.kind H = .circle ∧ thirteenSixInside S D H = 0 ∧
            thirteenSixOutside S D H = 6 then 9 else 0) +
        (if S.kind H = .line ∧ thirteenSixInside S D H = 0 ∧
            thirteenSixOutside S D H = 4 then 2 else 0) +
        (if S.kind H = .circle ∧ thirteenSixInside S D H = 2 ∧
            thirteenSixOutside S D H = 4 then 2 else 0) := by
    by_cases hnonempty : (sixConicEventsHostedBy cfg gamma X H).Nonempty
    · obtain ⟨E, hEhosted⟩ := hnonempty
      have hEdata := Finset.mem_filter.mp hEhosted
      have hE := hEdata.1
      have hhost := hEdata.2
      have hEspec := mem_sixConicRepetitionEvents.mp hE
      obtain ⟨e, f, hef, hEeq⟩ :=
        Finset.card_eq_two.mp (Finset.mem_powersetCard.mp hEspec.1).2
      have heE : e ∈ E := by simp [hEeq]
      have hfE : f ∈ E := by simp [hEeq]
      have heFull := (Finset.mem_powersetCard.mp hEspec.1).1 heE
      have hfFull := (Finset.mem_powersetCard.mp hEspec.1).1 hfE
      have heCard := (Finset.mem_powersetCard.mp
        (mem_sixConicFullEdges.mp heFull).1).2
      have hfCard := (Finset.mem_powersetCard.mp
        (mem_sixConicFullEdges.mp hfFull).1).2
      have hefDisjoint := sixConic_repetition_event_edges_disjoint
        cfg gamma hgamma X hdisjoint hE heE hfE hef
      have hUnionCard : (e ∪ f).card = 4 := by
        rw [Finset.card_union_of_disjoint hefDisjoint, heCard, hfCard]
      have hUnionSub : e ∪ f ⊆ geometricBlockSupport cfg H ∩ X := by
        intro z hz
        rw [Finset.mem_inter]
        constructor
        · apply hhost
          rcases Finset.mem_union.mp hz with hze | hzf
          · exact Finset.mem_biUnion.mpr ⟨e, heE, hze⟩
          · exact Finset.mem_biUnion.mpr ⟨f, hfE, hzf⟩
        · rcases Finset.mem_union.mp hz with hze | hzf
          · exact (Finset.mem_powersetCard.mp
              (mem_sixConicFullEdges.mp heFull).1).1 hze
          · exact (Finset.mem_powersetCard.mp
              (mem_sixConicFullEdges.mp hfFull).1).1 hzf
      have hfour : 4 ≤ sixConicHostOutsiderCount cfg X H := by
        unfold sixConicHostOutsiderCount
        exact hUnionCard ▸ Finset.card_le_card hUnionSub
      have houtsideEq : sixConicHostOutsiderCount cfg X H =
          thirteenSixOutside S D H := by
        unfold sixConicHostOutsiderCount
        rw [hX]
        change (S.support H ∩ (Finset.univ \ D)).card =
          thirteenSixOutside S D H
        exact (thirteenSixOutside_eq_support_inter_compl_card S D H).symm
      rw [houtsideEq] at hfour
      have hcapEvents :=
        sixConicEventsHostedBy_card_le_hostEventCapacity
          cfg gamma hgamma X hdisjoint H
      have hsum := thirteenSixInside_add_thirteenSixOutside S D H
      by_cases hmeet : (geometricBlockSupport cfg H ∩ D).Nonempty
      · have hadm := thirteenSix_eventHost_meeting_gamma
          cfg gamma hgamma X hdisjoint hE H hhost (by simpa [D] using hmeet)
        have hkind : S.kind H = .circle := hadm.1
        have hinside : thirteenSixInside S D H = 2 := by
          simpa [S, D, thirteenSixInside] using hadm.2
        have hcap : (S.support H).card ≤ 6 := by
          cases H with
          | inl L => cases hkind
          | inr c => exact hcircleCap c
        rw [← hsum, hinside] at hcap
        have hout : thirteenSixOutside S D H = 4 := by omega
        simp [hkind, hinside, hout]
        rw [houtsideEq, hout] at hcapEvents
        norm_num [sixConicHostEventCapacity, Nat.choose] at hcapEvents ⊢
        exact hcapEvents
      · have hinside : thirteenSixInside S D H = 0 := by
          rw [thirteenSixInside]
          exact Finset.card_eq_zero.mpr (by
            rw [← Finset.not_nonempty_iff_eq_empty]
            simpa [S, D, geometricBlockSupport] using hmeet)
        cases hkind : S.kind H with
        | circle =>
            have hcap : (S.support H).card ≤ 6 := by
              cases H with
              | inl L => cases hkind
              | inr c => exact hcircleCap c
            rw [← hsum, hinside] at hcap
            have houtCases : thirteenSixOutside S D H = 4 ∨
                thirteenSixOutside S D H = 5 ∨
                thirteenSixOutside S D H = 6 := by omega
            rcases houtCases with hout | hout | hout <;>
              simp [hinside, hout] <;>
              rw [houtsideEq, hout] at hcapEvents <;>
              norm_num [sixConicHostEventCapacity, Nat.choose] at hcapEvents ⊢ <;>
              exact hcapEvents
        | line =>
            have hcap : (S.support H).card ≤ 6 := by
              cases H with
              | inl L => exact hlineCap L
              | inr c => cases hkind
            rw [← hsum, hinside] at hcap
            have houtCases : thirteenSixOutside S D H = 4 ∨
                thirteenSixOutside S D H = 5 ∨
                thirteenSixOutside S D H = 6 := by omega
            rcases houtCases with hout | hout | hout
            · simp [hinside, hout]
              rw [houtsideEq, hout] at hcapEvents
              norm_num [sixConicHostEventCapacity, Nat.choose] at hcapEvents ⊢
              exact hcapEvents
            · have hmem : H ∈ thirteenSixRelativeBlocks S D .line 0 5 := by
                simp [thirteenSixRelativeBlocks, hkind, hinside, hout]
              have hpos : 0 < thirteenSixRelativeCount S D .line 0 5 := by
                exact Finset.card_pos.mpr ⟨H, hmem⟩
              simp [S, D, hline05] at hpos
            · have hmem : H ∈ thirteenSixRelativeBlocks S D .line 0 6 := by
                simp [thirteenSixRelativeBlocks, hkind, hinside, hout]
              have hpos : 0 < thirteenSixRelativeCount S D .line 0 6 := by
                exact Finset.card_pos.mpr ⟨H, hmem⟩
              simp [S, D, hline06] at hpos
    · have hempty : sixConicEventsHostedBy cfg gamma X H = ∅ :=
        Finset.not_nonempty_iff_eq_empty.mp hnonempty
      simp [hempty]
  have hcover : sixConicRepetitionEvents cfg gamma X ⊆
      (Finset.univ : Finset (GeometricBlock cfg)).biUnion
        (sixConicEventsHostedBy cfg gamma X) := by
    intro E hE
    obtain ⟨H, hH⟩ := sixConic_repetition_host_exists
      cfg gamma hgamma X hdisjoint E hE
    exact Finset.mem_biUnion.mpr
      ⟨H, Finset.mem_univ H, Finset.mem_filter.mpr ⟨hE, hH⟩⟩
  have hcoverCard := Finset.card_le_card hcover
  have hunionCard :
      ((Finset.univ : Finset (GeometricBlock cfg)).biUnion
        (sixConicEventsHostedBy cfg gamma X)).card ≤
      ∑ H : GeometricBlock cfg,
        (sixConicEventsHostedBy cfg gamma X H).card :=
    Finset.card_biUnion_le
  have hsum := Finset.sum_le_sum
    (s := (Finset.univ : Finset (GeometricBlock cfg)))
      fun H _hH => hpointwise H
  simp only [Finset.sum_add_distrib] at hsum
  rw [thirteenSix_sum_relative_indicator,
    thirteenSix_sum_relative_indicator,
    thirteenSix_sum_relative_indicator,
    thirteenSix_sum_relative_indicator,
    thirteenSix_sum_relative_indicator] at hsum
  change _ ≤ 2 * thirteenSixRelativeCount S D .circle 0 4 +
      3 * thirteenSixRelativeCount S D .circle 0 5 +
      9 * thirteenSixRelativeCount S D .circle 0 6 +
      2 * thirteenSixRelativeCount S D .line 0 4 +
      2 * thirteenSixRelativeCount S D .circle 2 4 at hsum
  simpa [S, D] using hcoverCard.trans (hunionCard.trans hsum)

end HostCapacity

end Erdos506.V1
