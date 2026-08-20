import Erdos506.V1.RichBlockPencil
import Erdos506.V1.LargeMaster

/-!
# The uniform half-cap for V1

The rich-block pencil forces every line or proper-circle block to have size
at most `⌊n / 2⌋` as soon as the circle count is below the uniform target.
The numerical core is the four-parity calculation from the manuscript, with
`q = n - s` and `s > ⌊n / 2⌋`.
-/

namespace Erdos506.V1

open Erdos506.Block
open Erdos506.Block.BlockSystem
open Erdos506.Incidence
open Erdos506.V4

universe u

/-- Admissibility makes every geometric line/circle block proper: neither a
line nor a proper circle contains all selected points. -/
theorem geometricBlockSupport_card_lt_of_admissible
    {α : Type*} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (hadm : Admissible cfg)
    (b : GeometricBlock cfg) :
    (geometricBlockSupport cfg b).card < Fintype.card α := by
  cases b with
  | inr c =>
      exact Erdos506.V3.circleSupport_card_lt cfg hadm.2 c
  | inl L =>
      change (lineSupport cfg L).card < Fintype.card α
      by_contra hnot
      have hle : (lineSupport cfg L).card ≤ Fintype.card α := by
        simpa using Finset.card_le_univ (lineSupport cfg L)
      have heq : (lineSupport cfg L).card = Fintype.card α := by omega
      have hall : lineSupport cfg L = Finset.univ :=
        Finset.eq_univ_of_card _ heq
      apply hadm.1
      have hcolLine : Collinear ℝ (L.1 : Set Point2) := by
        rw [collinear_iff_finrank_le_one,
          ← AffineSubspace.direction_eq_vectorSpan]
        rw [L.direction_finrank]
      apply hcolLine.subset
      rintro y ⟨x, rfl⟩
      apply mem_lineSupport.mp
      rw [hall]
      simp

private theorem choose_two_even (r : ℕ) :
    Nat.choose (2 * r) 2 = r * (2 * r - 1) := by
  have h := Nat.choose_succ_right_eq (2 * r) 1
  simp only [Nat.reduceAdd, Nat.choose_one_right] at h
  have hprod : 2 * r * (2 * r - 1) =
      (r * (2 * r - 1)) * 2 := by ring
  rw [hprod] at h
  omega

private theorem choose_two_odd (r : ℕ) :
    Nat.choose (2 * r + 1) 2 = r * (2 * r + 1) := by
  have h := Nat.choose_succ_right_eq (2 * r + 1) 1
  simp only [Nat.reduceAdd, Nat.choose_one_right] at h
  have hprod : (2 * r + 1) * (2 * r + 1 - 1) =
      (r * (2 * r + 1)) * 2 := by
    have : 2 * r + 1 - 1 = 2 * r := by omega
    rw [this]
    ring
  rw [hprod] at h
  omega

private theorem choose_two_even_sub_half (r : ℕ) (hr : 1 ≤ r) :
    Nat.choose (2 * r) 2 - r = 2 * r * (r - 1) := by
  rw [choose_two_even]
  have hpred : 2 * r - 1 = 2 * (r - 1) + 1 := by omega
  have hprod : r * (2 * r - 1) = 2 * r * (r - 1) + r := by
    rw [hpred]
    ring
  rw [hprod]
  omega

private theorem choose_two_odd_sub_half (r : ℕ) :
    Nat.choose (2 * r + 1) 2 - r = 2 * r * r := by
  rw [choose_two_odd]
  have hprod : r * (2 * r + 1) = 2 * r * r + r := by ring
  rw [hprod]
  omega

private theorem half_even (r : ℕ) : 2 * r / 2 = r := by omega

private theorem half_odd (r : ℕ) : (2 * r + 1) / 2 = r := by omega

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
  have hprod : r * (2 * r - 1) = 2 * r * (r - 1) + r := by
    rw [hpred]
    ring
  unfold Erdos506.v1UniformTarget
  rw [show 2 * r + 1 - 1 = 2 * r by omega,
    choose_two_even r, half_even r, hprod]
  omega

private theorem parityRowOne_nonneg (b c : ℕ) (hb : 1 ≤ b)
    (hlarge : 7 ≤ 2 * b + c) :
    (0 : ℤ) ≤
      (4 * (b : ℤ) - 2) * (c : ℤ) ^ 2 +
        (6 * (b : ℤ) ^ 2 - 3 * (b : ℤ)) * (c : ℤ) +
        2 * (b : ℤ) ^ 3 - 5 * (b : ℤ) ^ 2 + (b : ℤ) := by
  by_cases hb3 : 3 ≤ b
  · have hbz : (0 : ℤ) ≤ (b : ℤ) := by positivity
    have hcz : (0 : ℤ) ≤ (c : ℤ) := by positivity
    have hcoefOne : (0 : ℤ) ≤ 4 * (b : ℤ) - 2 := by omega
    have hcoefTwo : (0 : ℤ) ≤
        6 * (b : ℤ) ^ 2 - 3 * (b : ℤ) := by
      have hprod : (0 : ℤ) ≤
          3 * (b : ℤ) * (2 * (b : ℤ) - 1) := by
        exact mul_nonneg (mul_nonneg (by norm_num) hbz) (by omega)
      nlinarith
    have hcore : (0 : ℤ) ≤
        2 * (b : ℤ) ^ 2 - 5 * (b : ℤ) + 1 := by
      have hprod : (0 : ℤ) ≤
          ((b : ℤ) - 3) * (2 * (b : ℤ) + 1) := by
        exact mul_nonneg (by omega) (by omega)
      nlinarith
    have htermOne := mul_nonneg hcoefOne (sq_nonneg (c : ℤ))
    have htermTwo := mul_nonneg hcoefTwo hcz
    have hconstant := mul_nonneg hbz hcore
    nlinarith
  · have hbCases : b = 1 ∨ b = 2 := by omega
    rcases hbCases with rfl | rfl
    · have hc : 5 ≤ c := by omega
      have hcz : (5 : ℤ) ≤ (c : ℤ) := by exact_mod_cast hc
      norm_num at ⊢
      nlinarith [sq_nonneg (c : ℤ)]
    · have hc : 3 ≤ c := by omega
      have hcz : (3 : ℤ) ≤ (c : ℤ) := by exact_mod_cast hc
      norm_num at ⊢
      nlinarith [sq_nonneg (c : ℤ)]

private theorem parityRowTwo_nonneg (b c : ℕ)
    (hlarge : 6 ≤ 2 * b + c) :
    (0 : ℤ) ≤ (b : ℤ) *
      (4 * (c : ℤ) ^ 2 +
        (6 * (b : ℤ) - 1) * (c : ℤ) +
        2 * (b : ℤ) ^ 2 - 5 * (b : ℤ) - 3) := by
  rcases eq_zero_or_pos b with rfl | hb
  · norm_num
  · have hbz : (0 : ℤ) ≤ (b : ℤ) := by positivity
    have hinside : (0 : ℤ) ≤
        4 * (c : ℤ) ^ 2 +
          (6 * (b : ℤ) - 1) * (c : ℤ) +
          2 * (b : ℤ) ^ 2 - 5 * (b : ℤ) - 3 := by
      by_cases hb3 : 3 ≤ b
      · have hcz : (0 : ℤ) ≤ (c : ℤ) := by positivity
        have hcoef : (0 : ℤ) ≤ 6 * (b : ℤ) - 1 := by omega
        have hcore : (0 : ℤ) ≤
            2 * (b : ℤ) ^ 2 - 5 * (b : ℤ) - 3 := by
          have hprod : (0 : ℤ) ≤
              ((b : ℤ) - 3) * (2 * (b : ℤ) + 1) := by
            exact mul_nonneg (by omega) (by omega)
          nlinarith
        have hterm := mul_nonneg hcoef hcz
        nlinarith [sq_nonneg (c : ℤ)]
      · have hbCases : b = 1 ∨ b = 2 := by omega
        rcases hbCases with rfl | rfl
        · have hc : 4 ≤ c := by omega
          have hcz : (4 : ℤ) ≤ (c : ℤ) := by exact_mod_cast hc
          nlinarith [sq_nonneg (c : ℤ)]
        · have hc : 2 ≤ c := by omega
          have hcz : (2 : ℤ) ≤ (c : ℤ) := by exact_mod_cast hc
          nlinarith [sq_nonneg (c : ℤ)]
    exact mul_nonneg hbz hinside

private theorem parityRowThree_nonneg (b c : ℕ) (hb : 1 ≤ b)
    (hlarge : 7 ≤ 2 * b + c) :
    (0 : ℤ) ≤
      (4 * (b : ℤ) - 2) * (c : ℤ) ^ 2 +
        (6 * (b : ℤ) ^ 2 - 7 * (b : ℤ) + 2) * (c : ℤ) +
        2 * (b : ℤ) ^ 3 - 7 * (b : ℤ) ^ 2 + 4 * (b : ℤ) := by
  by_cases hb3 : 3 ≤ b
  · have hbz : (0 : ℤ) ≤ (b : ℤ) := by positivity
    have hcz : (0 : ℤ) ≤ (c : ℤ) := by positivity
    have hcoefOne : (0 : ℤ) ≤ 4 * (b : ℤ) - 2 := by omega
    have hcoefTwo : (0 : ℤ) ≤
        6 * (b : ℤ) ^ 2 - 7 * (b : ℤ) + 2 := by
      have hprod : (0 : ℤ) ≤
          ((b : ℤ) - 3) * (6 * (b : ℤ) + 11) := by
        exact mul_nonneg (by omega) (by omega)
      nlinarith
    have hcore : (0 : ℤ) ≤
        2 * (b : ℤ) ^ 2 - 7 * (b : ℤ) + 4 := by
      have hprod : (0 : ℤ) ≤
          ((b : ℤ) - 3) * (2 * (b : ℤ) - 1) := by
        exact mul_nonneg (by omega) (by omega)
      nlinarith
    have htermOne := mul_nonneg hcoefOne (sq_nonneg (c : ℤ))
    have htermTwo := mul_nonneg hcoefTwo hcz
    have hconstant := mul_nonneg hbz hcore
    nlinarith
  · have hbCases : b = 1 ∨ b = 2 := by omega
    rcases hbCases with rfl | rfl
    · have hc : 5 ≤ c := by omega
      have hcz : (5 : ℤ) ≤ (c : ℤ) := by exact_mod_cast hc
      norm_num at ⊢
      nlinarith [sq_nonneg (c : ℤ)]
    · have hc : 3 ≤ c := by omega
      have hcz : (3 : ℤ) ≤ (c : ℤ) := by exact_mod_cast hc
      norm_num at ⊢
      nlinarith [sq_nonneg (c : ℤ)]

private theorem parityRowFour_nonneg (b c : ℕ) :
    (0 : ℤ) ≤ (b : ℤ) *
      (4 * (c : ℤ) ^ 2 +
        (6 * (b : ℤ) + 3) * (c : ℤ) +
        2 * (b : ℤ) ^ 2 - (b : ℤ) - 1) := by
  rcases eq_zero_or_pos b with rfl | hb
  · norm_num
  · have hbz : (0 : ℤ) ≤ (b : ℤ) := by positivity
    have hcz : (0 : ℤ) ≤ (c : ℤ) := by positivity
    have hcoef : (0 : ℤ) ≤ 6 * (b : ℤ) + 3 := by positivity
    have hcore : (0 : ℤ) ≤
        2 * (b : ℤ) ^ 2 - (b : ℤ) - 1 := by
      have hprod : (0 : ℤ) ≤
          ((b : ℤ) - 1) * (2 * (b : ℤ) + 1) := by
        exact mul_nonneg (by omega) (by omega)
      nlinarith
    have hterm := mul_nonneg hcoef hcz
    have hinside : (0 : ℤ) ≤
        4 * (c : ℤ) ^ 2 +
          (6 * (b : ℤ) + 3) * (c : ℤ) +
          2 * (b : ℤ) ^ 2 - (b : ℤ) - 1 := by
      nlinarith [sq_nonneg (c : ℤ)]
    exact mul_nonneg hbz hinside

private theorem parityRowOne
    (b c : ℕ) (hb : 1 ≤ b) (hlarge : 7 ≤ 2 * b + c) :
    Erdos506.v1UniformTarget (2 * (2 * b + 1 + c)) +
        Nat.choose (2 * b) 2 * (b + 1 + c) ≤
      1 + (2 * b) *
        (Nat.choose (2 * (b + 1 + c)) 2 - (b + 1 + c)) := by
  rw [v1UniformTarget_even (2 * b + 1 + c) (by omega),
    choose_two_even b,
    choose_two_even_sub_half (b + 1 + c) (by omega)]
  have hgap := parityRowOne_nonneg b c hb hlarge
  have hbsub : 1 ≤ 2 * b := by omega
  have harsub : 1 ≤ 2 * b + 1 + c := by omega
  have hasub : 1 ≤ b + 1 + c := by omega
  have hcast :
      ((1 + 2 * (2 * b + 1 + c - 1) * (2 * b + 1 + c - 1) +
          b * (2 * b - 1) * (b + 1 + c) : ℕ) : ℤ) ≤
        ((1 + 2 * b * (2 * (b + 1 + c) * (b + 1 + c - 1)) : ℕ) : ℤ) := by
    push_cast [Nat.cast_sub hbsub, Nat.cast_sub harsub, Nat.cast_sub hasub]
    nlinarith
  exact_mod_cast hcast

private theorem parityRowTwo
    (b c : ℕ) (hlarge : 6 ≤ 2 * b + c) :
    Erdos506.v1UniformTarget (2 * (2 * b + 1 + c) + 1) +
        Nat.choose (2 * b + 1) 2 * (b + 1 + c) ≤
      1 + (2 * b + 1) *
        (Nat.choose (2 * (b + 1 + c)) 2 - (b + 1 + c)) := by
  rw [v1UniformTarget_odd (2 * b + 1 + c) (by omega),
    choose_two_odd b,
    choose_two_even_sub_half (b + 1 + c) (by omega)]
  have hgap := parityRowTwo_nonneg b c hlarge
  have hrsub : 1 ≤ 2 * b + 1 + c := by omega
  have hasub : 1 ≤ b + 1 + c := by omega
  have hcast :
      ((1 + 2 * (2 * b + 1 + c) * (2 * b + 1 + c - 1) +
          b * (2 * b + 1) * (b + 1 + c) : ℕ) : ℤ) ≤
        ((1 + (2 * b + 1) *
          (2 * (b + 1 + c) * (b + 1 + c - 1)) : ℕ) : ℤ) := by
    push_cast [Nat.cast_sub hrsub, Nat.cast_sub hasub]
    nlinarith
  exact_mod_cast hcast

private theorem parityRowThree
    (b c : ℕ) (hb : 1 ≤ b) (hlarge : 7 ≤ 2 * b + c) :
    Erdos506.v1UniformTarget (2 * (2 * b + c) + 1) +
        Nat.choose (2 * b) 2 * (b + c) ≤
      1 + (2 * b) *
        (Nat.choose (2 * (b + c) + 1) 2 - (b + c)) := by
  rw [v1UniformTarget_odd (2 * b + c) (by omega),
    choose_two_even b, choose_two_odd_sub_half (b + c)]
  have hgap := parityRowThree_nonneg b c hb hlarge
  have hbsub : 1 ≤ 2 * b := by omega
  have hrsub : 1 ≤ 2 * b + c := by omega
  have hcast :
      ((1 + 2 * (2 * b + c) * (2 * b + c - 1) +
          b * (2 * b - 1) * (b + c) : ℕ) : ℤ) ≤
        ((1 + 2 * b * (2 * (b + c) * (b + c)) : ℕ) : ℤ) := by
    push_cast [Nat.cast_sub hbsub, Nat.cast_sub hrsub]
    nlinarith
  exact_mod_cast hcast

private theorem parityRowFour
    (b c : ℕ) (hlarge : 6 ≤ 2 * b + c) :
    Erdos506.v1UniformTarget (2 * (2 * b + 2 + c)) +
        Nat.choose (2 * b + 1) 2 * (b + 1 + c) ≤
      1 + (2 * b + 1) *
        (Nat.choose (2 * (b + 1 + c) + 1) 2 - (b + 1 + c)) := by
  rw [v1UniformTarget_even (2 * b + 2 + c) (by omega),
    choose_two_odd b, choose_two_odd_sub_half (b + 1 + c)]
  have hgap := parityRowFour_nonneg b c
  have hrsub : 1 ≤ 2 * b + 2 + c := by omega
  have hcast :
      ((1 + 2 * (2 * b + 2 + c - 1) * (2 * b + 2 + c - 1) +
          b * (2 * b + 1) * (b + 1 + c) : ℕ) : ℤ) ≤
        ((1 + (2 * b + 1) *
          (2 * (b + 1 + c) * (b + 1 + c)) : ℕ) : ℤ) := by
    push_cast [Nat.cast_sub hrsub]
    nlinarith
  exact_mod_cast hcast

/-- The four-parity arithmetic behind the half-cap.  It is stated in the
subtraction-safe form `target + overlap ≤ numerator`; the rich pencil bound
then follows by `Nat.le_sub_of_add_le`. -/
theorem v1UniformTarget_add_overlap_le_richBlockPencilNumerator
    (n s : ℕ) (hn : 15 ≤ n) (hhalf : n / 2 < s) (hproper : s < n) :
    Erdos506.v1UniformTarget n +
        Nat.choose (n - s) 2 * (s / 2) ≤
      1 + (n - s) * (Nat.choose s 2 - s / 2) := by
  let q := n - s
  have hqpos : 0 < q := by dsimp only [q]; omega
  have hnSplit : n = s + q := by dsimp only [q]; omega
  rcases s.even_or_odd' with ⟨a, hsEven | hsOdd⟩
  · rcases q.even_or_odd' with ⟨b, hqEven | hqOdd⟩
    · have hb : 1 ≤ b := by omega
      have hab : b + 1 ≤ a := by
        rw [hnSplit, hsEven, hqEven] at hhalf
        omega
      let c := a - (b + 1)
      have ha : a = b + 1 + c := by dsimp only [c]; omega
      have hlarge : 7 ≤ 2 * b + c := by
        rw [hnSplit, hsEven, hqEven, ha] at hn
        omega
      have hrow := parityRowOne b c hb hlarge
      have hsForm : s = 2 * (b + 1 + c) := by omega
      have hqForm : n - s = 2 * b := by omega
      have hnForm : n = 2 * (2 * b + 1 + c) := by omega
      rw [hqForm, hnForm, hsForm, half_even]
      exact hrow
    · have hab : b + 1 ≤ a := by
        rw [hnSplit, hsEven, hqOdd] at hhalf
        omega
      let c := a - (b + 1)
      have ha : a = b + 1 + c := by dsimp only [c]; omega
      have hlarge : 6 ≤ 2 * b + c := by
        rw [hnSplit, hsEven, hqOdd, ha] at hn
        omega
      have hrow := parityRowTwo b c hlarge
      have hsForm : s = 2 * (b + 1 + c) := by omega
      have hqForm : n - s = 2 * b + 1 := by omega
      have hnForm : n = 2 * (2 * b + 1 + c) + 1 := by omega
      rw [hqForm, hnForm, hsForm, half_even]
      exact hrow
  · rcases q.even_or_odd' with ⟨b, hqEven | hqOdd⟩
    · have hb : 1 ≤ b := by omega
      have hab : b ≤ a := by
        rw [hnSplit, hsOdd, hqEven] at hhalf
        omega
      let c := a - b
      have ha : a = b + c := by dsimp only [c]; omega
      have hlarge : 7 ≤ 2 * b + c := by
        rw [hnSplit, hsOdd, hqEven, ha] at hn
        omega
      have hrow := parityRowThree b c hb hlarge
      have hsForm : s = 2 * (b + c) + 1 := by omega
      have hqForm : n - s = 2 * b := by omega
      have hnForm : n = 2 * (2 * b + c) + 1 := by omega
      rw [hqForm, hnForm, hsForm, half_odd]
      exact hrow
    · have hab : b + 1 ≤ a := by
        rw [hnSplit, hsOdd, hqOdd] at hhalf
        omega
      let c := a - (b + 1)
      have ha : a = b + 1 + c := by dsimp only [c]; omega
      have hlarge : 6 ≤ 2 * b + c := by
        rw [hnSplit, hsOdd, hqOdd, ha] at hn
        omega
      have hrow := parityRowFour b c hlarge
      have hsForm : s = 2 * (b + 1 + c) + 1 := by omega
      have hqForm : n - s = 2 * b + 1 := by omega
      have hnForm : n = 2 * (2 * b + 2 + c) := by omega
      rw [hqForm, hnForm, hsForm, half_odd]
      exact hrow

theorem v1UniformTarget_le_richBlockPencilBound
    (n s : ℕ) (hn : 15 ≤ n) (hhalf : n / 2 < s) (hproper : s < n) :
    Erdos506.v1UniformTarget n ≤ richBlockPencilBound n s := by
  unfold richBlockPencilBound
  exact Nat.le_sub_of_add_le
    (v1UniformTarget_add_overlap_le_richBlockPencilNumerator
      n s hn hhalf hproper)

/-- A circle count below the uniform target forces the manuscript's
half-size cap on every nontrivial geometric block. -/
theorem halfBlockCap_of_circleCount_lt_v1UniformTarget
    {α : Type u} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (hadm : Admissible cfg)
    (hcard : 15 ≤ Fintype.card α)
    (hcount : Erdos506.V4.circleCount cfg <
      Erdos506.v1UniformTarget (Fintype.card α)) :
    BlockSizeCap (blockSystem cfg) (Fintype.card α / 2) := by
  intro b hbsize
  change 3 ≤ (geometricBlockSupport cfg b).card at hbsize
  let s := (geometricBlockSupport cfg b).card
  have hproper : s < Fintype.card α := by
    dsimp only [s]
    exact geometricBlockSupport_card_lt_of_admissible cfg hadm b
  by_contra hnot
  change ¬(geometricBlockSupport cfg b).card ≤ Fintype.card α / 2 at hnot
  have hhalf : Fintype.card α / 2 < s := by omega
  have hpencil := richBlockPencilBound_le_totalCircleCount
    (blockSystem cfg) b hproper hbsize
  have htarget := v1UniformTarget_le_richBlockPencilBound
    (Fintype.card α) s hcard hhalf hproper
  rw [totalCircleCount_eq_card_determinedCircle,
    ← Erdos506.V3.circleCount_eq_card_determinedCircle] at hpencil
  have hpencil' : richBlockPencilBound (Fintype.card α) s ≤
      Erdos506.V4.circleCount cfg := by
    simpa [s] using hpencil
  omega

/-- The large-range V1 lower bound, obtained by feeding the forced half-cap
into the already formalized `S_M` master. -/
theorem v1UniformTarget_le_circleCount_large
    {α : Type u} [Fintype α] [DecidableEq α]
    (Mel : Erdos506.Incidence.RealPlaneMelchiorPrinciple.{u})
    (Lan : Erdos506.Incidence.RealPlaneLangerPrinciple.{u})
    (cfg : Configuration α) (hadm : Admissible cfg)
    (hcard : 15 ≤ Fintype.card α) :
    Erdos506.v1UniformTarget (Fintype.card α) ≤
      Erdos506.V4.circleCount cfg := by
  by_contra hnot
  have hcount : Erdos506.V4.circleCount cfg <
      Erdos506.v1UniformTarget (Fintype.card α) := by omega
  have hcap := halfBlockCap_of_circleCount_lt_v1UniformTarget
    cfg hadm hcard hcount
  have hstrict := v1UniformTarget_lt_circleCount_of_halfBlockCap
    Mel Lan cfg hadm hcard hcap
  omega

end Erdos506.V1
