import Mathlib.Data.Matrix.Action
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.FinTwo
import Mathlib.LinearAlgebra.Projectivization.Action
import Mathlib.Tactic

/-!
# Cyclic orientation on the real projective line

This file isolates the analytic ingredient used by the six-marked-conic
argument.  A point of `RP¹` is represented by a nonzero vector in `ℝ²`.
For three representatives `p,q,r`, the sign of

`[p,q] [q,r] [r,p]`

is independent of all three choices of scale: rescaling by `a,b,c`
multiplies it by `(a*b*c)²`.  Its positive sign therefore gives an
intrinsic cyclic orientation on `RP¹`.

An invertible real two-by-two matrix multiplies each bracket by its
determinant.  It consequently preserves this orientation when its
determinant is positive and reverses it when its determinant is negative.
This is the precise order statement needed after a chord-pencil map has
been identified with a projective linear involution.
-/

namespace Erdos506.Incidence

open Matrix
open scoped LinearAlgebra.Projectivization

/-- Homogeneous coordinate vectors for the real projective line. -/
abbrev RealProjectiveLineVector := Fin 2 → ℝ

/-- The real projective line. -/
abbrev RealProjectiveOnePoint := ℙ ℝ RealProjectiveLineVector

/-- The alternating bracket of two homogeneous `RP¹` representatives. -/
def realProjectiveBracket
    (p q : RealProjectiveLineVector) : ℝ :=
  p 0 * q 1 - p 1 * q 0

@[simp] theorem realProjectiveBracket_self
    (p : RealProjectiveLineVector) :
    realProjectiveBracket p p = 0 := by
  simp [realProjectiveBracket]
  ring

theorem realProjectiveBracket_swap
    (p q : RealProjectiveLineVector) :
    realProjectiveBracket q p = -realProjectiveBracket p q := by
  simp [realProjectiveBracket]
  ring

theorem realProjectiveBracket_smul
    (a b : ℝ) (p q : RealProjectiveLineVector) :
    realProjectiveBracket (a • p) (b • q) =
      (a * b) * realProjectiveBracket p q := by
  simp [realProjectiveBracket]
  ring

/-- Two nonzero vectors determine the same point of `RP¹` exactly when
their alternating bracket vanishes. -/
theorem realProjective_mk_eq_mk_iff_bracket_eq_zero
    {p q : RealProjectiveLineVector} (hp : p ≠ 0) (hq : q ≠ 0) :
    Projectivization.mk ℝ p hp = Projectivization.mk ℝ q hq ↔
      realProjectiveBracket p q = 0 := by
  constructor
  · intro heq
    obtain ⟨a, ha⟩ :=
      (Projectivization.mk_eq_mk_iff' ℝ p q hp hq).mp heq
    calc
      realProjectiveBracket p q =
          realProjectiveBracket (a • q) q := by rw [ha]
      _ = 0 := by
        simp [realProjectiveBracket]
        ring
  · intro hbracket
    apply (Projectivization.mk_eq_mk_iff' ℝ p q hp hq).mpr
    by_cases hq0 : q 0 = 0
    · have hq1 : q 1 ≠ 0 := by
        intro hq1
        apply hq
        funext i
        fin_cases i <;> simp_all
      have hp0 : p 0 = 0 := by
        simp only [realProjectiveBracket, hq0, mul_zero, sub_zero]
          at hbracket
        exact (mul_eq_zero.mp hbracket).resolve_right hq1
      refine ⟨p 1 / q 1, ?_⟩
      funext i
      fin_cases i
      · change (p 1 / q 1) * q 0 = p 0
        rw [hq0, hp0]
        norm_num
      · change (p 1 / q 1) * q 1 = p 1
        exact div_mul_cancel₀ (p 1) hq1
    · refine ⟨p 0 / q 0, ?_⟩
      funext i
      fin_cases i
      · change (p 0 / q 0) * q 0 = p 0
        exact div_mul_cancel₀ (p 0) hq0
      · change (p 0 / q 0) * q 1 = p 1
        simp only [realProjectiveBracket] at hbracket
        field_simp [hq0]
        linarith

/-- The scale-invariant orientation numerator of three homogeneous
representatives. -/
def realProjectiveTripleBracket
    (p q r : RealProjectiveLineVector) : ℝ :=
  realProjectiveBracket p q * realProjectiveBracket q r *
    realProjectiveBracket r p

/-- Independent rescaling of three representatives changes the triple
bracket only by a square. -/
theorem realProjectiveTripleBracket_smul
    (a b c : ℝ) (p q r : RealProjectiveLineVector) :
    realProjectiveTripleBracket (a • p) (b • q) (c • r) =
      (a * b * c) ^ 2 * realProjectiveTripleBracket p q r := by
  simp only [realProjectiveTripleBracket, realProjectiveBracket_smul]
  ring

/-- Positive cyclic orientation of three points of the real projective
line.  The existential representatives are harmless because
`realProjectiveTripleBracket_smul` shows that every nonzero change of
representatives has a positive square factor. -/
def RealProjectiveCyclic
    (P Q R : RealProjectiveOnePoint) : Prop :=
  ∃ (p q r : RealProjectiveLineVector)
      (hp : p ≠ 0) (hq : q ≠ 0) (hr : r ≠ 0),
    P = Projectivization.mk ℝ p hp ∧
    Q = Projectivization.mk ℝ q hq ∧
    R = Projectivization.mk ℝ r hr ∧
    0 < realProjectiveTripleBracket p q r

/-- Concrete positive representatives certify the intrinsic cyclic
orientation. -/
theorem realProjectiveCyclic_mk
    {p q r : RealProjectiveLineVector}
    (hp : p ≠ 0) (hq : q ≠ 0) (hr : r ≠ 0)
    (hcyclic : 0 < realProjectiveTripleBracket p q r) :
    RealProjectiveCyclic
      (Projectivization.mk ℝ p hp)
      (Projectivization.mk ℝ q hq)
      (Projectivization.mk ℝ r hr) := by
  exact ⟨p, q, r, hp, hq, hr, rfl, rfl, rfl, hcyclic⟩

/-- A two-by-two matrix scales the alternating bracket by its determinant. -/
theorem realProjectiveBracket_mulVec
    (A : Matrix (Fin 2) (Fin 2) ℝ)
    (p q : RealProjectiveLineVector) :
    realProjectiveBracket (A *ᵥ p) (A *ᵥ q) =
      A.det * realProjectiveBracket p q := by
  simp only [realProjectiveBracket, Matrix.mulVec, dotProduct,
    Fin.sum_univ_two, Matrix.det_fin_two]
  ring

/-- The preceding determinant identity for the standard `GL₂(ℝ)` action. -/
theorem realProjectiveBracket_gl_smul
    (g : GL (Fin 2) ℝ) (p q : RealProjectiveLineVector) :
    realProjectiveBracket (g • p) (g • q) =
      (g : Matrix (Fin 2) (Fin 2) ℝ).det *
        realProjectiveBracket p q := by
  change realProjectiveBracket
      ((g : Matrix (Fin 2) (Fin 2) ℝ) *ᵥ p)
      ((g : Matrix (Fin 2) (Fin 2) ℝ) *ᵥ q) = _
  exact realProjectiveBracket_mulVec (g : Matrix (Fin 2) (Fin 2) ℝ) p q

/-- Positive-determinant projectivities preserve positive cyclic
orientation. -/
theorem realProjectiveCyclic_smul_of_det_pos
    (g : GL (Fin 2) ℝ)
    (hdet : 0 < (g : Matrix (Fin 2) (Fin 2) ℝ).det)
    {P Q R : RealProjectiveOnePoint}
    (hcyclic : RealProjectiveCyclic P Q R) :
    RealProjectiveCyclic (g • P) (g • Q) (g • R) := by
  rcases hcyclic with
    ⟨p, q, r, hp, hq, hr, hP, hQ, hR, hori⟩
  let hp' : g • p ≠ 0 := (smul_ne_zero_iff_ne g).mpr hp
  let hq' : g • q ≠ 0 := (smul_ne_zero_iff_ne g).mpr hq
  let hr' : g • r ≠ 0 := (smul_ne_zero_iff_ne g).mpr hr
  refine ⟨g • p, g • q, g • r, hp', hq', hr', ?_, ?_, ?_, ?_⟩
  · calc
      g • P = g • Projectivization.mk ℝ p hp :=
        congrArg (fun T : RealProjectiveOnePoint => g • T) hP
      _ = Projectivization.mk ℝ (g • p) hp' := by
        simp
  · calc
      g • Q = g • Projectivization.mk ℝ q hq :=
        congrArg (fun T : RealProjectiveOnePoint => g • T) hQ
      _ = Projectivization.mk ℝ (g • q) hq' := by
        simp
  · calc
      g • R = g • Projectivization.mk ℝ r hr :=
        congrArg (fun T : RealProjectiveOnePoint => g • T) hR
      _ = Projectivization.mk ℝ (g • r) hr' := by
        simp
  · simp only [realProjectiveTripleBracket,
      realProjectiveBracket_gl_smul]
    simp only [realProjectiveTripleBracket] at hori
    have hfactor :
        0 < ((g : Matrix (Fin 2) (Fin 2) ℝ).det *
          (g : Matrix (Fin 2) (Fin 2) ℝ).det *
          (g : Matrix (Fin 2) (Fin 2) ℝ).det) :=
      mul_pos (mul_pos hdet hdet) hdet
    have hprod := mul_pos hfactor hori
    convert hprod using 1
    ring

/-- Negative-determinant projectivities reverse positive cyclic
orientation.  Reversal is recorded by swapping the last two images. -/
theorem realProjectiveCyclic_smul_of_det_neg
    (g : GL (Fin 2) ℝ)
    (hdet : (g : Matrix (Fin 2) (Fin 2) ℝ).det < 0)
    {P Q R : RealProjectiveOnePoint}
    (hcyclic : RealProjectiveCyclic P Q R) :
    RealProjectiveCyclic (g • P) (g • R) (g • Q) := by
  rcases hcyclic with
    ⟨p, q, r, hp, hq, hr, hP, hQ, hR, hori⟩
  let hp' : g • p ≠ 0 := (smul_ne_zero_iff_ne g).mpr hp
  let hq' : g • q ≠ 0 := (smul_ne_zero_iff_ne g).mpr hq
  let hr' : g • r ≠ 0 := (smul_ne_zero_iff_ne g).mpr hr
  refine ⟨g • p, g • r, g • q, hp', hr', hq', ?_, ?_, ?_, ?_⟩
  · calc
      g • P = g • Projectivization.mk ℝ p hp :=
        congrArg (fun T : RealProjectiveOnePoint => g • T) hP
      _ = Projectivization.mk ℝ (g • p) hp' := by
        simp
  · calc
      g • R = g • Projectivization.mk ℝ r hr :=
        congrArg (fun T : RealProjectiveOnePoint => g • T) hR
      _ = Projectivization.mk ℝ (g • r) hr' := by
        simp
  · calc
      g • Q = g • Projectivization.mk ℝ q hq :=
        congrArg (fun T : RealProjectiveOnePoint => g • T) hQ
      _ = Projectivization.mk ℝ (g • q) hq' := by
        simp
  · simp only [realProjectiveTripleBracket,
      realProjectiveBracket_gl_smul]
    simp only [realProjectiveTripleBracket] at hori
    have hsq :
        0 < (g : Matrix (Fin 2) (Fin 2) ℝ).det *
          (g : Matrix (Fin 2) (Fin 2) ℝ).det :=
      mul_pos_of_neg_of_neg hdet hdet
    have hcube :
        (g : Matrix (Fin 2) (Fin 2) ℝ).det *
            (g : Matrix (Fin 2) (Fin 2) ℝ).det *
            (g : Matrix (Fin 2) (Fin 2) ℝ).det < 0 :=
      mul_neg_of_pos_of_neg hsq hdet
    have hfactor :
        0 < -((g : Matrix (Fin 2) (Fin 2) ℝ).det *
          (g : Matrix (Fin 2) (Fin 2) ℝ).det *
          (g : Matrix (Fin 2) (Fin 2) ℝ).det) :=
      neg_pos.mpr hcube
    have hprod := mul_pos hfactor hori
    have hpr : realProjectiveBracket p r =
        -realProjectiveBracket r p :=
      realProjectiveBracket_swap r p
    have hrq : realProjectiveBracket r q =
        -realProjectiveBracket q r :=
      realProjectiveBracket_swap q r
    have hqp : realProjectiveBracket q p =
        -realProjectiveBracket p q :=
      realProjectiveBracket_swap p q
    rw [hpr, hrq, hqp]
    convert hprod using 1
    ring

/-- The order action of a real projectivity: it either preserves the cyclic
orientation of every triple or reverses the cyclic orientation of every
triple. -/
theorem realProjectiveLine_gl_preserves_or_reverses_cyclicOrder
    (g : GL (Fin 2) ℝ) :
    (∀ P Q R : RealProjectiveOnePoint,
      RealProjectiveCyclic P Q R →
        RealProjectiveCyclic (g • P) (g • Q) (g • R)) ∨
    (∀ P Q R : RealProjectiveOnePoint,
      RealProjectiveCyclic P Q R →
        RealProjectiveCyclic (g • P) (g • R) (g • Q)) := by
  rcases lt_or_gt_of_ne
      (Matrix.GeneralLinearGroup.det_ne_zero g) with hneg | hpos
  · exact Or.inr fun _P _Q _R =>
      realProjectiveCyclic_smul_of_det_neg g hneg
  · exact Or.inl fun _P _Q _R =>
      realProjectiveCyclic_smul_of_det_pos g hpos

end Erdos506.Incidence
