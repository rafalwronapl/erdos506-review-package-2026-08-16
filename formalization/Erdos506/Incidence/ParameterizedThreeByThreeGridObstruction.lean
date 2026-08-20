import Erdos506.Incidence.ThreeByThreeProjectiveNormalization
import Mathlib.Tactic

/-!
# Algebraic obstruction for a parameterized real `3 x 3` grid

After the line joining the two pencil centres is sent to infinity, a real
three-by-three grid has coordinate sets

`{-1, 0, a} x {-1, 0, b}`.

This module begins the genuinely algebraic part of the real-grid lemma.  It
does not choose a rigid normalization as an assumption.  Instead it records
the six possible transversal permutations, computes their determinants, and
proves that two distinct transversals force each parameter into the three
affinely normalized values `{-2, -1/2, 1}`.  These are precisely the three
ways of relabelling an affine copy of `{-1,0,1}`.

The result is the cross-ratio bridge needed before the finite ordinary-secant
calculation can be transported to the actual twelve-grid entrance.
-/

namespace Erdos506.Incidence

/-- The six row-to-column permutations of a three-by-three transversal,
in lexicographic order. -/
def parameterizedThreeByThreeTransversalPermutation : Fin 6 → Fin 3 → Fin 3
  | 0 => ![0, 1, 2]
  | 1 => ![0, 2, 1]
  | 2 => ![1, 0, 2]
  | 3 => ![1, 2, 0]
  | 4 => ![2, 0, 1]
  | 5 => ![2, 1, 0]

/-- Twice the oriented affine area of three real coordinate points. -/
def parameterizedThreeByThreeAffineArea
    (U V W : ℝ × ℝ) : ℝ :=
  (V.1 - U.1) * (W.2 - U.2) - (V.2 - U.2) * (W.1 - U.1)

/-- Twice the oriented affine area of the triangle formed by three labelled
points of the parameterized grid.  Its vanishing is the elementary affine
collinearity test used throughout this file. -/
def parameterizedThreeByThreeGridArea
    (a b : ℝ) (u v w : Fin 3 × Fin 3) : ℝ :=
  parameterizedThreeByThreeAffineArea
    (threeByThreeParameterizedGridPoint a b u)
    (threeByThreeParameterizedGridPoint a b v)
    (threeByThreeParameterizedGridPoint a b w)

/-- The determinant of the three points selected by one of the six possible
transversal permutations. -/
def parameterizedThreeByThreeTransversalDeterminant
    (a b : ℝ) (t : Fin 6) : ℝ :=
  let σ := parameterizedThreeByThreeTransversalPermutation t
  parameterizedThreeByThreeGridArea a b
    (0, σ 0) (1, σ 1) (2, σ 2)

/-- Explicit polynomial table for the six transversal determinants. -/
def parameterizedThreeByThreeTransversalPolynomial
    (a b : ℝ) : Fin 6 → ℝ
  | 0 => b - a
  | 1 => -a * b - a - b
  | 2 => a + b + 1
  | 3 => -a * b - b - 1
  | 4 => a * b + a + 1
  | 5 => a * b - 1

/-- A coded transversal is present exactly when its displayed determinant
vanishes. -/
def ParameterizedThreeByThreeGridTransversal
    (a b : ℝ) (t : Fin 6) : Prop :=
  parameterizedThreeByThreeTransversalDeterminant a b t = 0

/-- Direct determinant calculation for the six transversal permutations. -/
theorem parameterizedThreeByThreeTransversal_determinant_eq_polynomial
    (a b : ℝ) (t : Fin 6) :
    parameterizedThreeByThreeTransversalDeterminant a b t =
      parameterizedThreeByThreeTransversalPolynomial a b t := by
  fin_cases t <;>
    norm_num [parameterizedThreeByThreeTransversalDeterminant,
      parameterizedThreeByThreeTransversalPermutation,
      parameterizedThreeByThreeGridArea,
      parameterizedThreeByThreeAffineArea,
      threeByThreeParameterizedGridPoint,
      threeByThreePencilCoordinate,
      parameterizedThreeByThreeTransversalPolynomial,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two] <;>
    ring

/-- The three possible third coordinates of one pencil after two distinct
transversals have fixed its affine cross-ratio. -/
def ParameterizedThreeByThreeSpecialParameter (x : ℝ) : Prop :=
  x = -2 ∨ x = (-1 / 2 : ℝ) ∨ x = 1

/-- The pair of parameter alternatives which is forced by two distinct
transversals. -/
def ParameterizedThreeByThreeParameterCases (a b : ℝ) : Prop :=
  ParameterizedThreeByThreeSpecialParameter a ∧
    ParameterizedThreeByThreeSpecialParameter b

private theorem parameterizedThreeByThreeTransversal_zero_one
    {a b : ℝ}
    (ha_minus : a ≠ -1) (ha_zero : a ≠ 0)
    (_hb_minus : b ≠ -1) (_hb_zero : b ≠ 0)
    (hzero : ParameterizedThreeByThreeGridTransversal a b 0)
    (hone : ParameterizedThreeByThreeGridTransversal a b 1) :
    ParameterizedThreeByThreeParameterCases a b := by
  have hzero' : b - a = 0 := by
    rw [ParameterizedThreeByThreeGridTransversal,
      parameterizedThreeByThreeTransversal_determinant_eq_polynomial] at hzero
    simpa [parameterizedThreeByThreeTransversalPolynomial] using hzero
  have hone' : -a * b - a - b = 0 := by
    rw [ParameterizedThreeByThreeGridTransversal,
      parameterizedThreeByThreeTransversal_determinant_eq_polynomial] at hone
    simpa [parameterizedThreeByThreeTransversalPolynomial] using hone
  have hba : b = a := by linarith
  subst b
  have hfactor : a * (a + 2) = 0 := by nlinarith
  rcases mul_eq_zero.mp hfactor with hzeroa | htwo
  · exact False.elim (ha_zero hzeroa)
  · constructor <;> left <;> linarith

private theorem parameterizedThreeByThreeTransversal_zero_two
    {a b : ℝ}
    (_ha_minus : a ≠ -1) (_ha_zero : a ≠ 0)
    (_hb_minus : b ≠ -1) (_hb_zero : b ≠ 0)
    (hzero : ParameterizedThreeByThreeGridTransversal a b 0)
    (htwo : ParameterizedThreeByThreeGridTransversal a b 2) :
    ParameterizedThreeByThreeParameterCases a b := by
  have hzero' : b - a = 0 := by
    rw [ParameterizedThreeByThreeGridTransversal,
      parameterizedThreeByThreeTransversal_determinant_eq_polynomial] at hzero
    simpa [parameterizedThreeByThreeTransversalPolynomial] using hzero
  have htwo' : a + b + 1 = 0 := by
    rw [ParameterizedThreeByThreeGridTransversal,
      parameterizedThreeByThreeTransversal_determinant_eq_polynomial] at htwo
    simpa [parameterizedThreeByThreeTransversalPolynomial] using htwo
  constructor <;> right <;> left <;> linarith

private theorem parameterizedThreeByThreeTransversal_zero_three
    {a b : ℝ}
    (_ha_minus : a ≠ -1) (_ha_zero : a ≠ 0)
    (_hb_minus : b ≠ -1) (_hb_zero : b ≠ 0)
    (hzero : ParameterizedThreeByThreeGridTransversal a b 0)
    (hthree : ParameterizedThreeByThreeGridTransversal a b 3) : False := by
  have hzero' : b - a = 0 := by
    rw [ParameterizedThreeByThreeGridTransversal,
      parameterizedThreeByThreeTransversal_determinant_eq_polynomial] at hzero
    simpa [parameterizedThreeByThreeTransversalPolynomial] using hzero
  have hthree' : -a * b - b - 1 = 0 := by
    rw [ParameterizedThreeByThreeGridTransversal,
      parameterizedThreeByThreeTransversal_determinant_eq_polynomial] at hthree
    simpa [parameterizedThreeByThreeTransversalPolynomial] using hthree
  have hba : b = a := by linarith
  subst b
  have hsq := sq_nonneg (a + (1 / 2 : ℝ))
  nlinarith

private theorem parameterizedThreeByThreeTransversal_zero_four
    {a b : ℝ}
    (_ha_minus : a ≠ -1) (_ha_zero : a ≠ 0)
    (_hb_minus : b ≠ -1) (_hb_zero : b ≠ 0)
    (hzero : ParameterizedThreeByThreeGridTransversal a b 0)
    (hfour : ParameterizedThreeByThreeGridTransversal a b 4) : False := by
  have hzero' : b - a = 0 := by
    rw [ParameterizedThreeByThreeGridTransversal,
      parameterizedThreeByThreeTransversal_determinant_eq_polynomial] at hzero
    simpa [parameterizedThreeByThreeTransversalPolynomial] using hzero
  have hfour' : a * b + a + 1 = 0 := by
    rw [ParameterizedThreeByThreeGridTransversal,
      parameterizedThreeByThreeTransversal_determinant_eq_polynomial] at hfour
    simpa [parameterizedThreeByThreeTransversalPolynomial] using hfour
  have hba : b = a := by linarith
  subst b
  have hsq := sq_nonneg (a + (1 / 2 : ℝ))
  nlinarith

private theorem parameterizedThreeByThreeTransversal_zero_five
    {a b : ℝ}
    (ha_minus : a ≠ -1) (_ha_zero : a ≠ 0)
    (_hb_minus : b ≠ -1) (_hb_zero : b ≠ 0)
    (hzero : ParameterizedThreeByThreeGridTransversal a b 0)
    (hfive : ParameterizedThreeByThreeGridTransversal a b 5) :
    ParameterizedThreeByThreeParameterCases a b := by
  have hzero' : b - a = 0 := by
    rw [ParameterizedThreeByThreeGridTransversal,
      parameterizedThreeByThreeTransversal_determinant_eq_polynomial] at hzero
    simpa [parameterizedThreeByThreeTransversalPolynomial] using hzero
  have hfive' : a * b - 1 = 0 := by
    rw [ParameterizedThreeByThreeGridTransversal,
      parameterizedThreeByThreeTransversal_determinant_eq_polynomial] at hfive
    simpa [parameterizedThreeByThreeTransversalPolynomial] using hfive
  have hba : b = a := by linarith
  subst b
  have hfactor : (a - 1) * (a + 1) = 0 := by nlinarith
  rcases mul_eq_zero.mp hfactor with hone | hminus
  · constructor <;> right <;> right <;> linarith
  · exact False.elim (ha_minus (by linarith))

private theorem parameterizedThreeByThreeTransversal_one_two
    {a b : ℝ}
    (_ha_minus : a ≠ -1) (_ha_zero : a ≠ 0)
    (_hb_minus : b ≠ -1) (_hb_zero : b ≠ 0)
    (hone : ParameterizedThreeByThreeGridTransversal a b 1)
    (htwo : ParameterizedThreeByThreeGridTransversal a b 2) : False := by
  have hone' : -a * b - a - b = 0 := by
    rw [ParameterizedThreeByThreeGridTransversal,
      parameterizedThreeByThreeTransversal_determinant_eq_polynomial] at hone
    simpa [parameterizedThreeByThreeTransversalPolynomial] using hone
  have htwo' : a + b + 1 = 0 := by
    rw [ParameterizedThreeByThreeGridTransversal,
      parameterizedThreeByThreeTransversal_determinant_eq_polynomial] at htwo
    simpa [parameterizedThreeByThreeTransversalPolynomial] using htwo
  have hba : b = -a - 1 := by linarith
  subst b
  have hsq := sq_nonneg (a + (1 / 2 : ℝ))
  nlinarith

private theorem parameterizedThreeByThreeTransversal_one_three
    {a b : ℝ}
    (_ha_minus : a ≠ -1) (_ha_zero : a ≠ 0)
    (_hb_minus : b ≠ -1) (_hb_zero : b ≠ 0)
    (hone : ParameterizedThreeByThreeGridTransversal a b 1)
    (hthree : ParameterizedThreeByThreeGridTransversal a b 3) :
    ParameterizedThreeByThreeParameterCases a b := by
  have hone' : -a * b - a - b = 0 := by
    rw [ParameterizedThreeByThreeGridTransversal,
      parameterizedThreeByThreeTransversal_determinant_eq_polynomial] at hone
    simpa [parameterizedThreeByThreeTransversalPolynomial] using hone
  have hthree' : -a * b - b - 1 = 0 := by
    rw [ParameterizedThreeByThreeGridTransversal,
      parameterizedThreeByThreeTransversal_determinant_eq_polynomial] at hthree
    simpa [parameterizedThreeByThreeTransversalPolynomial] using hthree
  have ha : a = 1 := by nlinarith
  have hb : b = (-1 / 2 : ℝ) := by nlinarith
  constructor
  · right; right; exact ha
  · right; left; exact hb

private theorem parameterizedThreeByThreeTransversal_one_four
    {a b : ℝ}
    (_ha_minus : a ≠ -1) (_ha_zero : a ≠ 0)
    (_hb_minus : b ≠ -1) (_hb_zero : b ≠ 0)
    (hone : ParameterizedThreeByThreeGridTransversal a b 1)
    (hfour : ParameterizedThreeByThreeGridTransversal a b 4) :
    ParameterizedThreeByThreeParameterCases a b := by
  have hone' : -a * b - a - b = 0 := by
    rw [ParameterizedThreeByThreeGridTransversal,
      parameterizedThreeByThreeTransversal_determinant_eq_polynomial] at hone
    simpa [parameterizedThreeByThreeTransversalPolynomial] using hone
  have hfour' : a * b + a + 1 = 0 := by
    rw [ParameterizedThreeByThreeGridTransversal,
      parameterizedThreeByThreeTransversal_determinant_eq_polynomial] at hfour
    simpa [parameterizedThreeByThreeTransversalPolynomial] using hfour
  have ha : a = (-1 / 2 : ℝ) := by nlinarith
  have hb : b = 1 := by nlinarith
  constructor
  · right; left; exact ha
  · right; right; exact hb

private theorem parameterizedThreeByThreeTransversal_one_five
    {a b : ℝ}
    (_ha_minus : a ≠ -1) (_ha_zero : a ≠ 0)
    (_hb_minus : b ≠ -1) (_hb_zero : b ≠ 0)
    (hone : ParameterizedThreeByThreeGridTransversal a b 1)
    (hfive : ParameterizedThreeByThreeGridTransversal a b 5) : False := by
  have hone' : -a * b - a - b = 0 := by
    rw [ParameterizedThreeByThreeGridTransversal,
      parameterizedThreeByThreeTransversal_determinant_eq_polynomial] at hone
    simpa [parameterizedThreeByThreeTransversalPolynomial] using hone
  have hfive' : a * b - 1 = 0 := by
    rw [ParameterizedThreeByThreeGridTransversal,
      parameterizedThreeByThreeTransversal_determinant_eq_polynomial] at hfive
    simpa [parameterizedThreeByThreeTransversalPolynomial] using hfive
  have hba : b = -a - 1 := by nlinarith
  subst b
  have hsq := sq_nonneg (a + (1 / 2 : ℝ))
  nlinarith

private theorem parameterizedThreeByThreeTransversal_two_three
    {a b : ℝ}
    (_ha_minus : a ≠ -1) (_ha_zero : a ≠ 0)
    (hb_minus : b ≠ -1) (_hb_zero : b ≠ 0)
    (htwo : ParameterizedThreeByThreeGridTransversal a b 2)
    (hthree : ParameterizedThreeByThreeGridTransversal a b 3) :
    ParameterizedThreeByThreeParameterCases a b := by
  have htwo' : a + b + 1 = 0 := by
    rw [ParameterizedThreeByThreeGridTransversal,
      parameterizedThreeByThreeTransversal_determinant_eq_polynomial] at htwo
    simpa [parameterizedThreeByThreeTransversalPolynomial] using htwo
  have hthree' : -a * b - b - 1 = 0 := by
    rw [ParameterizedThreeByThreeGridTransversal,
      parameterizedThreeByThreeTransversal_determinant_eq_polynomial] at hthree
    simpa [parameterizedThreeByThreeTransversalPolynomial] using hthree
  have hab : a = -b - 1 := by linarith
  subst a
  have hfactor : (b - 1) * (b + 1) = 0 := by nlinarith
  rcases mul_eq_zero.mp hfactor with hone | hminus
  · constructor
    · left; linarith
    · right; right; linarith
  · exact False.elim (hb_minus (by linarith))

private theorem parameterizedThreeByThreeTransversal_two_four
    {a b : ℝ}
    (ha_minus : a ≠ -1) (_ha_zero : a ≠ 0)
    (_hb_minus : b ≠ -1) (_hb_zero : b ≠ 0)
    (htwo : ParameterizedThreeByThreeGridTransversal a b 2)
    (hfour : ParameterizedThreeByThreeGridTransversal a b 4) :
    ParameterizedThreeByThreeParameterCases a b := by
  have htwo' : a + b + 1 = 0 := by
    rw [ParameterizedThreeByThreeGridTransversal,
      parameterizedThreeByThreeTransversal_determinant_eq_polynomial] at htwo
    simpa [parameterizedThreeByThreeTransversalPolynomial] using htwo
  have hfour' : a * b + a + 1 = 0 := by
    rw [ParameterizedThreeByThreeGridTransversal,
      parameterizedThreeByThreeTransversal_determinant_eq_polynomial] at hfour
    simpa [parameterizedThreeByThreeTransversalPolynomial] using hfour
  have hba : b = -a - 1 := by linarith
  subst b
  have hfactor : (a - 1) * (a + 1) = 0 := by nlinarith
  rcases mul_eq_zero.mp hfactor with hone | hminus
  · constructor
    · right; right; linarith
    · left; linarith
  · exact False.elim (ha_minus (by linarith))

private theorem parameterizedThreeByThreeTransversal_two_five
    {a b : ℝ}
    (_ha_minus : a ≠ -1) (_ha_zero : a ≠ 0)
    (_hb_minus : b ≠ -1) (_hb_zero : b ≠ 0)
    (htwo : ParameterizedThreeByThreeGridTransversal a b 2)
    (hfive : ParameterizedThreeByThreeGridTransversal a b 5) : False := by
  have htwo' : a + b + 1 = 0 := by
    rw [ParameterizedThreeByThreeGridTransversal,
      parameterizedThreeByThreeTransversal_determinant_eq_polynomial] at htwo
    simpa [parameterizedThreeByThreeTransversalPolynomial] using htwo
  have hfive' : a * b - 1 = 0 := by
    rw [ParameterizedThreeByThreeGridTransversal,
      parameterizedThreeByThreeTransversal_determinant_eq_polynomial] at hfive
    simpa [parameterizedThreeByThreeTransversalPolynomial] using hfive
  have hba : b = -a - 1 := by linarith
  subst b
  have hsq := sq_nonneg (a + (1 / 2 : ℝ))
  nlinarith

private theorem parameterizedThreeByThreeTransversal_three_four
    {a b : ℝ}
    (_ha_minus : a ≠ -1) (_ha_zero : a ≠ 0)
    (_hb_minus : b ≠ -1) (_hb_zero : b ≠ 0)
    (hthree : ParameterizedThreeByThreeGridTransversal a b 3)
    (hfour : ParameterizedThreeByThreeGridTransversal a b 4) : False := by
  have hthree' : -a * b - b - 1 = 0 := by
    rw [ParameterizedThreeByThreeGridTransversal,
      parameterizedThreeByThreeTransversal_determinant_eq_polynomial] at hthree
    simpa [parameterizedThreeByThreeTransversalPolynomial] using hthree
  have hfour' : a * b + a + 1 = 0 := by
    rw [ParameterizedThreeByThreeGridTransversal,
      parameterizedThreeByThreeTransversal_determinant_eq_polynomial] at hfour
    simpa [parameterizedThreeByThreeTransversalPolynomial] using hfour
  have hba : b = a := by nlinarith
  subst b
  have hsq := sq_nonneg (a + (1 / 2 : ℝ))
  nlinarith

private theorem parameterizedThreeByThreeTransversal_three_five
    {a b : ℝ}
    (_ha_minus : a ≠ -1) (_ha_zero : a ≠ 0)
    (_hb_minus : b ≠ -1) (_hb_zero : b ≠ 0)
    (hthree : ParameterizedThreeByThreeGridTransversal a b 3)
    (hfive : ParameterizedThreeByThreeGridTransversal a b 5) :
    ParameterizedThreeByThreeParameterCases a b := by
  have hthree' : -a * b - b - 1 = 0 := by
    rw [ParameterizedThreeByThreeGridTransversal,
      parameterizedThreeByThreeTransversal_determinant_eq_polynomial] at hthree
    simpa [parameterizedThreeByThreeTransversalPolynomial] using hthree
  have hfive' : a * b - 1 = 0 := by
    rw [ParameterizedThreeByThreeGridTransversal,
      parameterizedThreeByThreeTransversal_determinant_eq_polynomial] at hfive
    simpa [parameterizedThreeByThreeTransversalPolynomial] using hfive
  have ha : a = (-1 / 2 : ℝ) := by nlinarith
  have hb : b = -2 := by nlinarith
  constructor
  · right; left; exact ha
  · left; exact hb

private theorem parameterizedThreeByThreeTransversal_four_five
    {a b : ℝ}
    (_ha_minus : a ≠ -1) (_ha_zero : a ≠ 0)
    (_hb_minus : b ≠ -1) (_hb_zero : b ≠ 0)
    (hfour : ParameterizedThreeByThreeGridTransversal a b 4)
    (hfive : ParameterizedThreeByThreeGridTransversal a b 5) :
    ParameterizedThreeByThreeParameterCases a b := by
  have hfour' : a * b + a + 1 = 0 := by
    rw [ParameterizedThreeByThreeGridTransversal,
      parameterizedThreeByThreeTransversal_determinant_eq_polynomial] at hfour
    simpa [parameterizedThreeByThreeTransversalPolynomial] using hfour
  have hfive' : a * b - 1 = 0 := by
    rw [ParameterizedThreeByThreeGridTransversal,
      parameterizedThreeByThreeTransversal_determinant_eq_polynomial] at hfive
    simpa [parameterizedThreeByThreeTransversalPolynomial] using hfive
  have ha : a = -2 := by nlinarith
  have hb : b = (-1 / 2 : ℝ) := by nlinarith
  constructor
  · left; exact ha
  · right; left; exact hb

private theorem parameterizedThreeByThreeTransversal_parameter_cases_ordered
    {a b : ℝ} {s t : Fin 6}
    (ha_minus : a ≠ -1) (ha_zero : a ≠ 0)
    (hb_minus : b ≠ -1) (hb_zero : b ≠ 0)
    (horder : s.val < t.val)
    (hs : ParameterizedThreeByThreeGridTransversal a b s)
    (ht : ParameterizedThreeByThreeGridTransversal a b t) :
    ParameterizedThreeByThreeParameterCases a b := by
  fin_cases s <;> fin_cases t <;> norm_num at horder
  all_goals
    first
    | exact parameterizedThreeByThreeTransversal_zero_one
        ha_minus ha_zero hb_minus hb_zero hs ht
    | exact parameterizedThreeByThreeTransversal_zero_two
        ha_minus ha_zero hb_minus hb_zero hs ht
    | exact False.elim (parameterizedThreeByThreeTransversal_zero_three
        ha_minus ha_zero hb_minus hb_zero hs ht)
    | exact False.elim (parameterizedThreeByThreeTransversal_zero_four
        ha_minus ha_zero hb_minus hb_zero hs ht)
    | exact parameterizedThreeByThreeTransversal_zero_five
        ha_minus ha_zero hb_minus hb_zero hs ht
    | exact False.elim (parameterizedThreeByThreeTransversal_one_two
        ha_minus ha_zero hb_minus hb_zero hs ht)
    | exact parameterizedThreeByThreeTransversal_one_three
        ha_minus ha_zero hb_minus hb_zero hs ht
    | exact parameterizedThreeByThreeTransversal_one_four
        ha_minus ha_zero hb_minus hb_zero hs ht
    | exact False.elim (parameterizedThreeByThreeTransversal_one_five
        ha_minus ha_zero hb_minus hb_zero hs ht)
    | exact parameterizedThreeByThreeTransversal_two_three
        ha_minus ha_zero hb_minus hb_zero hs ht
    | exact parameterizedThreeByThreeTransversal_two_four
        ha_minus ha_zero hb_minus hb_zero hs ht
    | exact False.elim (parameterizedThreeByThreeTransversal_two_five
        ha_minus ha_zero hb_minus hb_zero hs ht)
    | exact False.elim (parameterizedThreeByThreeTransversal_three_four
        ha_minus ha_zero hb_minus hb_zero hs ht)
    | exact parameterizedThreeByThreeTransversal_three_five
        ha_minus ha_zero hb_minus hb_zero hs ht
    | exact parameterizedThreeByThreeTransversal_four_five
        ha_minus ha_zero hb_minus hb_zero hs ht

/-- Two distinct parameterized transversals force the two affine
cross-ratio parameters into the three relabelled normal-grid values.  No
normalization is assumed: the conclusion is obtained by the displayed finite
determinant table. -/
theorem parameterizedThreeByThreeGrid_two_transversals_parameter_cases
    {a b : ℝ} {s t : Fin 6}
    (ha_minus : a ≠ -1) (ha_zero : a ≠ 0)
    (hb_minus : b ≠ -1) (hb_zero : b ≠ 0)
    (hst : s ≠ t)
    (hs : ParameterizedThreeByThreeGridTransversal a b s)
    (ht : ParameterizedThreeByThreeGridTransversal a b t) :
    ParameterizedThreeByThreeParameterCases a b := by
  have hval : s.val ≠ t.val := by
    intro h
    apply hst
    exact Fin.ext h
  rcases lt_or_gt_of_ne hval with horder | horder
  · exact parameterizedThreeByThreeTransversal_parameter_cases_ordered
      ha_minus ha_zero hb_minus hb_zero horder hs ht
  · exact parameterizedThreeByThreeTransversal_parameter_cases_ordered
      ha_minus ha_zero hb_minus hb_zero horder ht hs

/-! ## The affine relabelling forced by the two-transversal table -/

/-- The three possible affine relabellings of one coordinate set.  The
parameter values are not new hypotheses: the preceding theorem produces
exactly this finite type. -/
inductive ParameterizedThreeByThreeGridRelabelling where
  | one
  | minusTwo
  | minusHalf
  deriving DecidableEq

/-- The remaining third coordinate in each relabelling. -/
noncomputable def ParameterizedThreeByThreeGridRelabelling.parameter :
    ParameterizedThreeByThreeGridRelabelling → ℝ
  | .one => 1
  | .minusTwo => -2
  | .minusHalf => (-1 / 2 : ℝ)

/-- The nonzero linear factor of the corresponding affine coordinate
change. -/
def ParameterizedThreeByThreeGridRelabelling.scale :
    ParameterizedThreeByThreeGridRelabelling → ℝ
  | .one => 1
  | .minusTwo => 1
  | .minusHalf => 2

/-- An affine map sending the displayed three-level set to
`{-1,0,1}`. -/
def ParameterizedThreeByThreeGridRelabelling.normalizer :
    ParameterizedThreeByThreeGridRelabelling → ℝ → ℝ
  | .one => fun x => x
  | .minusTwo => fun x => x + 1
  | .minusHalf => fun x => 2 * x + 1

/-- The induced relabelling of the three coordinate indices. -/
def ParameterizedThreeByThreeGridRelabelling.index :
    ParameterizedThreeByThreeGridRelabelling → Fin 3 → Fin 3
  | .one => ![0, 1, 2]
  | .minusTwo => ![1, 2, 0]
  | .minusHalf => ![0, 2, 1]

/-- The one-dimensional coordinate calculation for each relabelling. -/
theorem ParameterizedThreeByThreeGridRelabelling.normalizer_coordinate
    (r : ParameterizedThreeByThreeGridRelabelling) (i : Fin 3) :
    r.normalizer
      (threeByThreePencilCoordinate r.parameter i) =
      (r.index i : ℝ) - 1 := by
  cases r <;> fin_cases i <;>
    norm_num [ParameterizedThreeByThreeGridRelabelling.normalizer,
      ParameterizedThreeByThreeGridRelabelling.parameter,
      ParameterizedThreeByThreeGridRelabelling.index,
      threeByThreePencilCoordinate]

/-- The standard affine coordinate table, retained locally so this incidence
module stays independent of the V1 transfer wrapper. -/
def parameterizedThreeByThreeStandardPoint (ij : Fin 3 × Fin 3) : ℝ × ℝ :=
  ((ij.1 : ℝ) - 1, (ij.2 : ℝ) - 1)

/-- Coordinatewise affine normalization of a parameterized grid. -/
def parameterizedThreeByThreeNormalizePoint
    (ra rb : ParameterizedThreeByThreeGridRelabelling) (z : ℝ × ℝ) : ℝ × ℝ :=
  (ra.normalizer z.1, rb.normalizer z.2)

/-- The relabelled grid index after the coordinatewise normalization. -/
def parameterizedThreeByThreeNormalizedIndex
    (ra rb : ParameterizedThreeByThreeGridRelabelling)
    (ij : Fin 3 × Fin 3) : Fin 3 × Fin 3 :=
  (ra.index ij.1, rb.index ij.2)

/-- The parameterized grid is sent pointwise to the standard grid by the
affine maps determined by the two transversal cross-ratios. -/
theorem parameterizedThreeByThreeNormalize_gridPoint
    (ra rb : ParameterizedThreeByThreeGridRelabelling)
    (ij : Fin 3 × Fin 3) :
    parameterizedThreeByThreeNormalizePoint ra rb
      (threeByThreeParameterizedGridPoint ra.parameter rb.parameter ij) =
      parameterizedThreeByThreeStandardPoint
        (parameterizedThreeByThreeNormalizedIndex ra rb ij) := by
  rcases ij with ⟨i, j⟩
  apply Prod.ext
  · simpa [parameterizedThreeByThreeNormalizePoint,
      parameterizedThreeByThreeNormalizedIndex,
      parameterizedThreeByThreeStandardPoint,
      threeByThreeParameterizedGridPoint] using
      ParameterizedThreeByThreeGridRelabelling.normalizer_coordinate ra i
  · simpa [parameterizedThreeByThreeNormalizePoint,
      parameterizedThreeByThreeNormalizedIndex,
      parameterizedThreeByThreeStandardPoint,
      threeByThreeParameterizedGridPoint] using
      ParameterizedThreeByThreeGridRelabelling.normalizer_coordinate rb j

/-- The coordinatewise affine map rescales oriented area by its nonzero
linear determinant. -/
theorem parameterizedThreeByThreeAffineArea_normalize
    (ra rb : ParameterizedThreeByThreeGridRelabelling)
    (U V W : ℝ × ℝ) :
    parameterizedThreeByThreeAffineArea
      (parameterizedThreeByThreeNormalizePoint ra rb U)
      (parameterizedThreeByThreeNormalizePoint ra rb V)
      (parameterizedThreeByThreeNormalizePoint ra rb W) =
      (ra.scale * rb.scale) * parameterizedThreeByThreeAffineArea U V W := by
  cases ra <;> cases rb <;>
    simp [parameterizedThreeByThreeAffineArea,
      parameterizedThreeByThreeNormalizePoint,
      ParameterizedThreeByThreeGridRelabelling.normalizer,
      ParameterizedThreeByThreeGridRelabelling.scale] <;>
    ring

/-- Affine normalization preserves and reflects collinearity. -/
theorem parameterizedThreeByThreeAffineArea_normalize_eq_zero_iff
    (ra rb : ParameterizedThreeByThreeGridRelabelling)
    (U V W : ℝ × ℝ) :
    parameterizedThreeByThreeAffineArea
      (parameterizedThreeByThreeNormalizePoint ra rb U)
      (parameterizedThreeByThreeNormalizePoint ra rb V)
      (parameterizedThreeByThreeNormalizePoint ra rb W) = 0 ↔
      parameterizedThreeByThreeAffineArea U V W = 0 := by
  rw [parameterizedThreeByThreeAffineArea_normalize]
  have hra : ra.scale ≠ 0 := by
    cases ra <;> norm_num [ParameterizedThreeByThreeGridRelabelling.scale]
  have hrb : rb.scale ≠ 0 := by
    cases rb <;> norm_num [ParameterizedThreeByThreeGridRelabelling.scale]
  constructor
  · intro h
    exact (mul_eq_zero.mp h).resolve_left (mul_ne_zero hra hrb)
  · intro h
    rw [h, mul_zero]

/-- Every pair of parameter cases determines concrete affine relabellings.
This is the data-valued form of the determinant classification above. -/
theorem parameterizedThreeByThreeParameterCases_exists_relabelling
    {a b : ℝ} (h : ParameterizedThreeByThreeParameterCases a b) :
    ∃ ra rb : ParameterizedThreeByThreeGridRelabelling,
      a = ra.parameter ∧ b = rb.parameter := by
  rcases h with ⟨ha, hb⟩
  rcases ha with ha | ha | ha <;>
    rcases hb with hb | hb | hb
  · exact ⟨.minusTwo, .minusTwo,
      by simpa [ParameterizedThreeByThreeGridRelabelling.parameter] using ha,
      by simpa [ParameterizedThreeByThreeGridRelabelling.parameter] using hb⟩
  · exact ⟨.minusTwo, .minusHalf,
      by simpa [ParameterizedThreeByThreeGridRelabelling.parameter] using ha,
      by simpa [ParameterizedThreeByThreeGridRelabelling.parameter] using hb⟩
  · exact ⟨.minusTwo, .one,
      by simpa [ParameterizedThreeByThreeGridRelabelling.parameter] using ha,
      by simpa [ParameterizedThreeByThreeGridRelabelling.parameter] using hb⟩
  · exact ⟨.minusHalf, .minusTwo,
      by simpa [ParameterizedThreeByThreeGridRelabelling.parameter] using ha,
      by simpa [ParameterizedThreeByThreeGridRelabelling.parameter] using hb⟩
  · exact ⟨.minusHalf, .minusHalf,
      by simpa [ParameterizedThreeByThreeGridRelabelling.parameter] using ha,
      by simpa [ParameterizedThreeByThreeGridRelabelling.parameter] using hb⟩
  · exact ⟨.minusHalf, .one,
      by simpa [ParameterizedThreeByThreeGridRelabelling.parameter] using ha,
      by simpa [ParameterizedThreeByThreeGridRelabelling.parameter] using hb⟩
  · exact ⟨.one, .minusTwo,
      by simpa [ParameterizedThreeByThreeGridRelabelling.parameter] using ha,
      by simpa [ParameterizedThreeByThreeGridRelabelling.parameter] using hb⟩
  · exact ⟨.one, .minusHalf,
      by simpa [ParameterizedThreeByThreeGridRelabelling.parameter] using ha,
      by simpa [ParameterizedThreeByThreeGridRelabelling.parameter] using hb⟩
  · exact ⟨.one, .one,
      by simpa [ParameterizedThreeByThreeGridRelabelling.parameter] using ha,
      by simpa [ParameterizedThreeByThreeGridRelabelling.parameter] using hb⟩

end Erdos506.Incidence
