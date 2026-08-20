import Erdos506.Targets
import Mathlib.Tactic

/-!
# Symbolic arithmetic for V3

This file proves the rational factorizations and fixed scalar consequences
used by the V3 routing.  It contains no configuration enumeration.
-/

namespace Erdos506.V3

def chooseTwoQ (x : ℚ) : ℚ := x * (x - 1) / 2
def chooseThreeQ (x : ℚ) : ℚ := x * (x - 1) * (x - 2) / 6

theorem chooseTwoQ_natCast (s : ℕ) :
    chooseTwoQ (s : ℚ) = (Nat.choose s 2 : ℚ) := by
  simpa [chooseTwoQ] using (Nat.cast_choose_two ℚ s).symm

theorem chooseThreeQ_natCast (s : ℕ) (hs : 3 ≤ s) :
    chooseThreeQ (s : ℚ) = (Nat.choose s 3 : ℚ) := by
  have h := Nat.descFactorial_eq_factorial_mul_choose s 3
  norm_num [Nat.descFactorial_succ] at h
  rw [chooseThreeQ]
  rw [div_eq_iff (by norm_num : (6 : ℚ) ≠ 0)]
  have hq := congrArg (fun z : ℕ => (z : ℚ)) h
  norm_num only [Nat.cast_mul, Nat.cast_ofNat] at hq
  rw [Nat.cast_sub (by omega : 2 ≤ s),
    Nat.cast_sub (by omega : 1 ≤ s)] at hq
  ring_nf at hq ⊢
  exact hq

def genericTargetQ (n : ℚ) : ℚ := 1 + chooseTwoQ (n - 1)

def functionalA (m : ℚ) : ℚ := chooseThreeQ m
def functionalB (m : ℚ) : ℚ := m * (m - 4)
def functionalD (m : ℚ) : ℚ := 3 * functionalA m + functionalB m
def functionalLambda (m : ℚ) : ℚ := (functionalB m + 3) / functionalD m
def functionalMu (m : ℚ) : ℚ := (functionalA m - 1) / functionalD m

def boundedSupportLowerQ (n m : ℚ) : ℚ :=
  functionalLambda m * chooseThreeQ n + 3 * n * functionalMu m

theorem functionalD_factorization (m : ℚ) :
    functionalD m = m * (m - 3) * (m + 2) / 2 := by
  simp [functionalD, functionalA, functionalB, chooseThreeQ]
  ring

theorem functionalD_pos (m : ℚ) (hm : 4 ≤ m) : 0 < functionalD m := by
  rw [functionalD_factorization]
  have hm0 : 0 < m := by linarith
  have hm3 : 0 < m - 3 := by linarith
  have hm2 : 0 < m + 2 := by linarith
  positivity

theorem functionalLambda_nonneg (m : ℚ) (hm : 4 ≤ m) :
    0 ≤ functionalLambda m := by
  rw [functionalLambda]
  have hB : 0 ≤ functionalB m := by
    have hm0 : 0 ≤ m := by linarith
    have hm4 : 0 ≤ m - 4 := by linarith
    simp only [functionalB]
    positivity
  exact div_nonneg (by linarith) (le_of_lt (functionalD_pos m hm))

theorem functionalMu_nonneg (m : ℚ) (hm : 4 ≤ m) :
    0 ≤ functionalMu m := by
  rw [functionalMu]
  have hnum : functionalA m - 1 = (m - 3) * (m^2 + 2) / 6 := by
    simp [functionalA, chooseThreeQ]
    ring
  rw [hnum]
  apply div_nonneg
  · exact div_nonneg (mul_nonneg (by linarith) (by positivity)) (by norm_num)
  · exact le_of_lt (functionalD_pos m hm)

theorem functional_normalization (m : ℚ) (hm : 4 ≤ m) :
    functionalLambda m + 3 * functionalMu m = 1 := by
  have hm0 : m ≠ 0 := by linarith
  have hm3 : m ≠ 3 := by linarith
  have hm2 : m + 2 ≠ 0 := by linarith
  rw [functionalLambda, functionalMu, functionalD_factorization]
  simp [functionalA, functionalB, chooseThreeQ]
  field_simp
  ring

theorem functional_endpoint (m : ℚ) (hm : 4 ≤ m) :
    functionalLambda m * chooseThreeQ m - functionalMu m * m * (m - 4) = 1 := by
  have hm0 : m ≠ 0 := by linarith
  have hm3 : m ≠ 3 := by linarith
  have hm2 : m + 2 ≠ 0 := by linarith
  rw [functionalLambda, functionalMu, functionalD_factorization]
  simp [functionalA, functionalB, chooseThreeQ]
  field_simp
  ring

theorem functional_slack_factorization (m s : ℚ) (hm : 4 ≤ m) :
    1 - (functionalLambda m * chooseThreeQ s - functionalMu m * s * (s - 4)) =
      (m - s) * (s - 3) * (m * s - m - s - 2) / (3 * m * (m + 2)) := by
  have hm0 : m ≠ 0 := by linarith
  have hm3 : m ≠ 3 := by linarith
  have hm2 : m + 2 ≠ 0 := by linarith
  rw [functionalLambda, functionalMu, functionalD_factorization]
  simp [functionalA, functionalB, chooseThreeQ]
  field_simp
  ring

theorem functional_coefficient_le_one (m s : ℚ)
    (hm : 4 ≤ m) (hs : 4 ≤ s) (hsm : s ≤ m) :
    functionalLambda m * chooseThreeQ s - functionalMu m * s * (s - 4) ≤ 1 := by
  rw [← sub_nonneg, functional_slack_factorization m s hm]
  have hms : 0 ≤ m - s := by linarith
  have hs3 : 0 ≤ s - 3 := by linarith
  have hlast : 0 ≤ m * s - m - s - 2 := by nlinarith
  have hden : 0 < 3 * m * (m + 2) := by positivity
  positivity

theorem boundedSupportLower_closed (n m : ℚ) (hm : 4 ≤ m) :
    boundedSupportLowerQ n m =
      n * (3 * m^2 + m * n^2 - 3 * m * n + 2 * m - n^2 + 3 * n + 4) /
        (3 * m * (m + 2)) := by
  have hm0 : m ≠ 0 := by linarith
  have hm3 : m ≠ 3 := by linarith
  have hm2 : m + 2 ≠ 0 := by linarith
  simp [boundedSupportLowerQ, functionalLambda, functionalMu,
    functionalD_factorization, functionalA, functionalB, chooseThreeQ]
  field_simp
  ring

theorem boundedSupportLower_step (n m : ℚ) (hm : 4 ≤ m) :
    boundedSupportLowerQ n m - boundedSupportLowerQ n (m + 1) =
      n * (n - 4) * (n + 1) * (m^2 - m - 3) /
        (3 * m * (m + 1) * (m + 2) * (m + 3)) := by
  rw [boundedSupportLower_closed n m hm,
    boundedSupportLower_closed n (m + 1) (by linarith)]
  have hm0 : m ≠ 0 := by linarith
  have hm1 : m + 1 ≠ 0 := by linarith
  have hm2 : m + 2 ≠ 0 := by linarith
  have hm3 : m + 3 ≠ 0 := by linarith
  field_simp
  ring

theorem boundedSupportLower_antitone (n m : ℚ)
    (hn : 5 ≤ n) (hm : 4 ≤ m) :
    boundedSupportLowerQ n (m + 1) < boundedSupportLowerQ n m := by
  rw [← sub_pos, boundedSupportLower_step n m hm]
  have h1 : 0 < n := by linarith
  have h2 : 0 < n - 4 := by linarith
  have h3 : 0 < n + 1 := by linarith
  have h4 : 0 < m^2 - m - 3 := by nlinarith
  have hden : 0 < 3 * m * (m + 1) * (m + 2) * (m + 3) := by positivity
  positivity

theorem boundedSupport_even_gap (r : ℚ) (hr : 4 ≤ r) :
    boundedSupportLowerQ (2 * r) r - genericTargetQ (2 * r) =
      (r - 2) * (2 * r^2 - 13 * r + 2) / (3 * (r + 2)) := by
  rw [boundedSupportLower_closed (2 * r) r hr]
  have hr2 : r + 2 ≠ 0 := by linarith
  simp [genericTargetQ, chooseTwoQ]
  field_simp
  ring

theorem boundedSupport_odd_gap (r : ℚ) (hr : 4 ≤ r) :
    boundedSupportLowerQ (2 * r + 1) r - genericTargetQ (2 * r + 1) =
      (2 * r - 3) * (r^3 - 4 * r^2 - 4 * r - 2) /
        (3 * r * (r + 2)) := by
  rw [boundedSupportLower_closed (2 * r + 1) r hr]
  have hr0 : r ≠ 0 := by linarith
  have hr2 : r + 2 ≠ 0 := by linarith
  simp [genericTargetQ, chooseTwoQ]
  field_simp
  ring

def pencilEvenQ (k r : ℚ) : ℚ :=
  1 + k * chooseTwoQ (2 * r) - chooseTwoQ k * r

def pencilOddQ (k r : ℚ) : ℚ :=
  1 + k * chooseTwoQ (2 * r + 1) - chooseTwoQ k * r

theorem pencil_even_gap (k r : ℚ) :
    2 * (pencilEvenQ k r - genericTargetQ (2 * r + k)) =
      (k - 1) * (4 * r^2 - 6 * r + 2 - k * (r + 1)) := by
  simp [pencilEvenQ, genericTargetQ, chooseTwoQ]
  ring

theorem pencil_odd_gap (k r : ℚ) :
    2 * (pencilOddQ k r - genericTargetQ (2 * r + 1 + k)) =
      (k - 1) * (4 * r^2 - 2 * r - k * (r + 1)) := by
  simp [pencilOddQ, genericTargetQ, chooseTwoQ]
  ring

/-- Natural-number form of the rich-circle pencil expression. -/
def pencilBound (n m : ℕ) : ℕ :=
  1 + (n - m) * Nat.choose m 2 - Nat.choose (n - m) 2 * (m / 2)

theorem pencilBound_small_values :
    [pencilBound 6 5,
      pencilBound 7 5, pencilBound 7 6,
      pencilBound 8 5, pencilBound 8 6, pencilBound 8 7,
      pencilBound 9 5, pencilBound 9 6, pencilBound 9 7, pencilBound 9 8,
      pencilBound 10 6, pencilBound 10 7, pencilBound 10 8,
        pencilBound 10 9] =
    [11, 19, 16, 25, 28, 22, 29, 37, 40, 29, 43, 55, 53, 37] := by
  norm_num [pencilBound, Nat.choose]

theorem m4_n5 {c3 c4 : ℕ}
    (hT : Nat.choose 5 3 = c3 + 4 * c4) (hM : 5 ≤ c3) :
    7 ≤ c3 + c4 := by
  norm_num [Nat.choose] at hT
  omega

theorem m4_n6 {c3 c4 : ℕ}
    (hT : Nat.choose 6 3 = c3 + 4 * c4) (hM : 6 ≤ c3) :
    11 ≤ c3 + c4 := by
  norm_num [Nat.choose] at hT
  omega

theorem m4_n7_base {c3 c4 : ℕ}
    (hT : Nat.choose 7 3 = c3 + 4 * c4) (hM : 7 ≤ c3) :
    14 ≤ c3 + c4 := by
  norm_num [Nat.choose] at hT
  omega

theorem m4_n7_jump {c3 c4 : ℕ}
    (hT : Nat.choose 7 3 = c3 + 4 * c4) (hM : 7 ≤ c3)
    (hne : c3 ≠ 7) :
    17 ≤ c3 + c4 := by
  norm_num [Nat.choose] at hT
  omega

theorem m4_n8 {c3 c4 : ℕ}
    (hT : Nat.choose 8 3 = c3 + 4 * c4) (hM : 8 ≤ c3) :
    20 ≤ c3 + c4 := by
  norm_num [Nat.choose] at hT
  omega

theorem m4_n9 {c3 c4 : ℕ}
    (hT : Nat.choose 9 3 = c3 + 4 * c4) (hM : 9 ≤ c3) :
    30 ≤ c3 + c4 := by
  norm_num [Nat.choose] at hT
  omega

theorem m4_n10 {c3 c4 : ℕ}
    (hT : Nat.choose 10 3 = c3 + 4 * c4) (hM : 10 ≤ c3) :
    39 ≤ c3 + c4 := by
  norm_num [Nat.choose] at hT
  omega

theorem n10_m5_arithmetic {c3 c4 q : ℕ}
    (hq : q ≤ 5)
    (hT : 120 = c3 + 4 * c4 + 10 * q)
    (hM : 30 + 5 * q ≤ 3 * c3) :
    39 ≤ c3 + c4 + q := by
  omega

end Erdos506.V3
