import Erdos506.Incidence.RealProjectiveLineCyclicOrder

/-!
# Algebra of a chord-pencil involution

For a symmetric binary form

`A u₀v₀ + B(u₀v₁+u₁v₀) + C u₁v₁`,

the residual solution to orthogonality with `u` is represented by

`T u`, where `T = !![-B,-C; A,B]`.

The identities `det T = A*C-B²` and
`T² = (B²-A*C) I` show that a nondegenerate form produces a genuine
projective involution of `RP¹`.  This file is deliberately independent of
circles: the circle module only has to identify its concurrent-chord
condition with this binary form.
-/

namespace Erdos506.Incidence

open Matrix
open scoped LinearAlgebra.Projectivization

/-- The symmetric binary form encoding two endpoints in one conic chord
pencil. -/
def realConicPencilForm (A B C : ℝ)
    (u v : RealProjectiveLineVector) : ℝ :=
  A * u 0 * v 0 + B * (u 0 * v 1 + u 1 * v 0) +
    C * u 1 * v 1

theorem realConicPencilForm_comm (A B C : ℝ)
    (u v : RealProjectiveLineVector) :
    realConicPencilForm A B C u v =
      realConicPencilForm A B C v u := by
  simp [realConicPencilForm]
  ring

/-- The trace-zero linear map taking one endpoint to the residual endpoint
in the pencil. -/
def realConicPencilMatrix (A B C : ℝ) :
    Matrix (Fin 2) (Fin 2) ℝ :=
  !![-B, -C; A, B]

@[simp] theorem realConicPencilMatrix_apply_zero
    (A B C : ℝ) (u : RealProjectiveLineVector) :
    (realConicPencilMatrix A B C *ᵥ u) 0 =
      -B * u 0 - C * u 1 := by
  simp [realConicPencilMatrix, Matrix.mulVec, dotProduct,
    Fin.sum_univ_two]
  ring

@[simp] theorem realConicPencilMatrix_apply_one
    (A B C : ℝ) (u : RealProjectiveLineVector) :
    (realConicPencilMatrix A B C *ᵥ u) 1 =
      A * u 0 + B * u 1 := by
  simp [realConicPencilMatrix, Matrix.mulVec, dotProduct,
    Fin.sum_univ_two]

/-- The pencil form is the bracket of the proposed residual endpoint with
the given endpoint. -/
theorem realProjectiveBracket_pencilMatrix
    (A B C : ℝ) (u v : RealProjectiveLineVector) :
    realProjectiveBracket v (realConicPencilMatrix A B C *ᵥ u) =
      realConicPencilForm A B C u v := by
  simp [realProjectiveBracket, realConicPencilForm]
  ring

@[simp] theorem realConicPencilMatrix_det (A B C : ℝ) :
    (realConicPencilMatrix A B C).det = A * C - B ^ 2 := by
  simp [realConicPencilMatrix, Matrix.det_fin_two]
  ring

/-- Cayley--Hamilton in the special trace-zero form used here. -/
theorem realConicPencilMatrix_sq_mulVec
    (A B C : ℝ) (u : RealProjectiveLineVector) :
    realConicPencilMatrix A B C *ᵥ
        (realConicPencilMatrix A B C *ᵥ u) =
      (B ^ 2 - A * C) • u := by
  funext i
  fin_cases i <;>
    simp [realConicPencilMatrix, Matrix.mulVec, dotProduct,
      Fin.sum_univ_two] <;>
    ring

/-- The invertible linear representative of a nondegenerate pencil
involution. -/
noncomputable def realConicPencilGL
    (A B C : ℝ) (hnondegenerate : A * C - B ^ 2 ≠ 0) :
    GL (Fin 2) ℝ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero
    (realConicPencilMatrix A B C)
    (by simpa using hnondegenerate)

theorem realConicPencilGL_smul_vector
    (A B C : ℝ) (hnondegenerate : A * C - B ^ 2 ≠ 0)
    (u : RealProjectiveLineVector) :
    realConicPencilGL A B C hnondegenerate • u =
      realConicPencilMatrix A B C *ᵥ u := by
  rfl

theorem realConicPencilGL_smul_smul_vector
    (A B C : ℝ) (hnondegenerate : A * C - B ^ 2 ≠ 0)
    (u : RealProjectiveLineVector) :
    realConicPencilGL A B C hnondegenerate •
        (realConicPencilGL A B C hnondegenerate • u) =
      (B ^ 2 - A * C) • u := by
  rw [realConicPencilGL_smul_vector,
    realConicPencilGL_smul_vector]
  exact realConicPencilMatrix_sq_mulVec A B C u

/-- The projective action induced by a nondegenerate pencil is an
involution. -/
theorem realConicPencilGL_projective_involution
    (A B C : ℝ) (hnondegenerate : A * C - B ^ 2 ≠ 0)
    (P : RealProjectiveOnePoint) :
    realConicPencilGL A B C hnondegenerate •
        (realConicPencilGL A B C hnondegenerate • P) = P := by
  induction P using Projectivization.ind with
  | h u hu =>
      rw [Projectivization.smul_mk, Projectivization.smul_mk]
      apply (Projectivization.mk_eq_mk_iff' ℝ _ _
        ((smul_ne_zero_iff_ne
          (realConicPencilGL A B C hnondegenerate)).mpr
          ((smul_ne_zero_iff_ne
            (realConicPencilGL A B C hnondegenerate)).mpr hu)) hu).mpr
      refine ⟨B ^ 2 - A * C, ?_⟩
      exact (realConicPencilGL_smul_smul_vector
        A B C hnondegenerate u).symm

/-- A vector is paired with the endpoint produced by the pencil map. -/
@[simp] theorem realConicPencilForm_matrix_self
    (A B C : ℝ) (u : RealProjectiveLineVector) :
    realConicPencilForm A B C u
      (realConicPencilMatrix A B C *ᵥ u) = 0 := by
  rw [← realProjectiveBracket_pencilMatrix]
  simp [realProjectiveBracket]
  ring

/-- Exact residual-endpoint characterization: among projective points, the
solutions of the pencil equation with a fixed nonzero endpoint `u` form
the single point represented by `T u`. -/
theorem realConicPencil_residual_iff
    (A B C : ℝ) (hnondegenerate : A * C - B ^ 2 ≠ 0)
    {u v : RealProjectiveLineVector} (hu : u ≠ 0) (hv : v ≠ 0) :
    realConicPencilForm A B C u v = 0 ↔
      Projectivization.mk ℝ v hv =
        Projectivization.mk ℝ
          (realConicPencilMatrix A B C *ᵥ u)
          (by
            rw [← realConicPencilGL_smul_vector
              A B C hnondegenerate]
            exact (smul_ne_zero_iff_ne
              (realConicPencilGL A B C hnondegenerate)).mpr hu) := by
  rw [realProjective_mk_eq_mk_iff_bracket_eq_zero,
    realProjectiveBracket_pencilMatrix]

/-- The residual endpoint operation inherits the cyclic-order dichotomy
from its `GL₂(ℝ)` representative. -/
theorem realConicPencil_preserves_or_reverses_cyclicOrder
    (A B C : ℝ) (hnondegenerate : A * C - B ^ 2 ≠ 0) :
    (∀ P Q R : RealProjectiveOnePoint,
      RealProjectiveCyclic P Q R →
        RealProjectiveCyclic
          (realConicPencilGL A B C hnondegenerate • P)
          (realConicPencilGL A B C hnondegenerate • Q)
          (realConicPencilGL A B C hnondegenerate • R)) ∨
    (∀ P Q R : RealProjectiveOnePoint,
      RealProjectiveCyclic P Q R →
        RealProjectiveCyclic
          (realConicPencilGL A B C hnondegenerate • P)
          (realConicPencilGL A B C hnondegenerate • R)
          (realConicPencilGL A B C hnondegenerate • Q)) :=
  realProjectiveLine_gl_preserves_or_reverses_cyclicOrder
    (realConicPencilGL A B C hnondegenerate)

end Erdos506.Incidence
