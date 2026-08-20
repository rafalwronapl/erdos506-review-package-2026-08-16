import Erdos506.Incidence.ProjectiveCoordinates
import Mathlib.LinearAlgebra.Matrix.Nondegenerate

/-!
# Diagonal points of a complete quadrangle

For four homogeneous points `a,b,c,d`, the three diagonal points are the
intersections of the opposite side pairs

* `AB` and `CD`,
* `AC` and `BD`,
* `AD` and `BC`.

Lines and intersections are both represented by cross products.  Expanding
the resulting determinant gives `-2` times the product of the four vertex
minors.  Over `ℝ` this proves that the diagonal points are noncollinear
whenever every three of the four vertices are noncollinear.
-/

namespace Erdos506.Incidence

open Matrix
open scoped LinearAlgebra.Projectivization

/-- Intersection vector of the opposite sides `AB` and `CD`. -/
def diagonalAB_CD (a b c d : Homogeneous3) : Homogeneous3 :=
  crossProduct (crossProduct a b) (crossProduct c d)

/-- Intersection vector of the opposite sides `AC` and `BD`. -/
def diagonalAC_BD (a b c d : Homogeneous3) : Homogeneous3 :=
  crossProduct (crossProduct a c) (crossProduct b d)

/-- Intersection vector of the opposite sides `AD` and `BC`. -/
def diagonalAD_BC (a b c d : Homogeneous3) : Homogeneous3 :=
  crossProduct (crossProduct a d) (crossProduct b c)

/-- General position for four homogeneous projective points: each of the four
three-by-three vertex minors is nonzero. -/
structure CompleteQuadrangleGeneralPosition
    (a b c d : Homogeneous3) : Prop where
  det_abc_ne : Matrix.det ![a, b, c] ≠ 0
  det_abd_ne : Matrix.det ![a, b, d] ≠ 0
  det_acd_ne : Matrix.det ![a, c, d] ≠ 0
  det_bcd_ne : Matrix.det ![b, c, d] ≠ 0

/-- Exact complete-quadrangle determinant identity.  The sign corresponds to
the ordered diagonal vectors `AB|CD`, `AC|BD`, `AD|BC`. -/
theorem completeQuadrangle_diagonal_det_identity
    (a b c d : Homogeneous3) :
    Matrix.det ![diagonalAB_CD a b c d,
        diagonalAC_BD a b c d, diagonalAD_BC a b c d] =
      (-2 : ℝ) * Matrix.det ![a, b, c] * Matrix.det ![a, b, d] *
        Matrix.det ![a, c, d] * Matrix.det ![b, c, d] := by
  simp [diagonalAB_CD, diagonalAC_BD, diagonalAD_BC,
    cross_apply, det_fin_three]
  ring

/-- In general position, the determinant of the three diagonal vectors is
nonzero. -/
theorem completeQuadrangle_diagonal_det_ne_zero
    {a b c d : Homogeneous3}
    (h : CompleteQuadrangleGeneralPosition a b c d) :
    Matrix.det ![diagonalAB_CD a b c d,
        diagonalAC_BD a b c d, diagonalAD_BC a b c d] ≠ 0 := by
  rw [completeQuadrangle_diagonal_det_identity]
  exact mul_ne_zero
    (mul_ne_zero
      (mul_ne_zero
        (mul_ne_zero (by norm_num) h.det_abc_ne)
        h.det_abd_ne)
      h.det_acd_ne)
    h.det_bcd_ne

/-- The three raw diagonal vectors are linearly independent. -/
theorem completeQuadrangle_diagonal_linearIndependent
    {a b c d : Homogeneous3}
    (h : CompleteQuadrangleGeneralPosition a b c d) :
    LinearIndependent ℝ ![diagonalAB_CD a b c d,
      diagonalAC_BD a b c d, diagonalAD_BC a b c d] :=
  Matrix.linearIndependent_rows_of_det_ne_zero
    (completeQuadrangle_diagonal_det_ne_zero h)

theorem diagonalAB_CD_ne_zero
    {a b c d : Homogeneous3}
    (h : CompleteQuadrangleGeneralPosition a b c d) :
    diagonalAB_CD a b c d ≠ 0 := by
  simpa using
    (completeQuadrangle_diagonal_linearIndependent h).ne_zero (0 : Fin 3)

theorem diagonalAC_BD_ne_zero
    {a b c d : Homogeneous3}
    (h : CompleteQuadrangleGeneralPosition a b c d) :
    diagonalAC_BD a b c d ≠ 0 := by
  simpa using
    (completeQuadrangle_diagonal_linearIndependent h).ne_zero (1 : Fin 3)

theorem diagonalAD_BC_ne_zero
    {a b c d : Homogeneous3}
    (h : CompleteQuadrangleGeneralPosition a b c d) :
    diagonalAD_BC a b c d ≠ 0 := by
  simpa using
    (completeQuadrangle_diagonal_linearIndependent h).ne_zero (2 : Fin 3)

/-- No nonzero covector is orthogonal to all three diagonal vectors. -/
theorem completeQuadrangle_no_common_nonzero_covector
    {a b c d ell : Homogeneous3}
    (h : CompleteQuadrangleGeneralPosition a b c d)
    (hell : ell ≠ 0)
    (hAB : diagonalAB_CD a b c d ⬝ᵥ ell = 0)
    (hAC : diagonalAC_BD a b c d ⬝ᵥ ell = 0)
    (hAD : diagonalAD_BC a b c d ⬝ᵥ ell = 0) : False := by
  apply hell
  apply Matrix.eq_zero_of_mulVec_eq_zero
    (completeQuadrangle_diagonal_det_ne_zero h)
  ext i
  fin_cases i
  · simpa [Matrix.mulVec] using hAB
  · simpa [Matrix.mulVec] using hAC
  · simpa [Matrix.mulVec] using hAD

/-- Intrinsic projective noncollinearity: no projective line covector is
incident with all three points. -/
def ProjectivelyNoncollinear
    (P Q R : RealProjectivePlane) : Prop :=
  ¬∃ ell : RealProjectivePlane,
    Projectivization.orthogonal P ell ∧
      Projectivization.orthogonal Q ell ∧
      Projectivization.orthogonal R ell

/-- First projective diagonal point of a complete quadrangle. -/
noncomputable def projectiveDiagonalAB_CD
    (a b c d : Homogeneous3)
    (h : CompleteQuadrangleGeneralPosition a b c d) :
    RealProjectivePlane :=
  Projectivization.mk ℝ (diagonalAB_CD a b c d)
    (diagonalAB_CD_ne_zero h)

/-- Second projective diagonal point of a complete quadrangle. -/
noncomputable def projectiveDiagonalAC_BD
    (a b c d : Homogeneous3)
    (h : CompleteQuadrangleGeneralPosition a b c d) :
    RealProjectivePlane :=
  Projectivization.mk ℝ (diagonalAC_BD a b c d)
    (diagonalAC_BD_ne_zero h)

/-- Third projective diagonal point of a complete quadrangle. -/
noncomputable def projectiveDiagonalAD_BC
    (a b c d : Homogeneous3)
    (h : CompleteQuadrangleGeneralPosition a b c d) :
    RealProjectivePlane :=
  Projectivization.mk ℝ (diagonalAD_BC a b c d)
    (diagonalAD_BC_ne_zero h)

/-- The three diagonal points of a complete quadrangle over `ℝ` are
projectively noncollinear. -/
theorem completeQuadrangle_projectiveDiagonals_noncollinear
    {a b c d : Homogeneous3}
    (h : CompleteQuadrangleGeneralPosition a b c d) :
    ProjectivelyNoncollinear
      (projectiveDiagonalAB_CD a b c d h)
      (projectiveDiagonalAC_BD a b c d h)
      (projectiveDiagonalAD_BC a b c d h) := by
  rintro ⟨ell, hAB, hAC, hAD⟩
  induction ell using Projectivization.ind with
  | h ell hell =>
      have hAB' : diagonalAB_CD a b c d ⬝ᵥ ell = 0 := by
        simpa only [projectiveDiagonalAB_CD,
          Projectivization.orthogonal_mk] using hAB
      have hAC' : diagonalAC_BD a b c d ⬝ᵥ ell = 0 := by
        simpa only [projectiveDiagonalAC_BD,
          Projectivization.orthogonal_mk] using hAC
      have hAD' : diagonalAD_BC a b c d ⬝ᵥ ell = 0 := by
        simpa only [projectiveDiagonalAD_BC,
          Projectivization.orthogonal_mk] using hAD
      exact completeQuadrangle_no_common_nonzero_covector
        h hell hAB' hAC' hAD'

end Erdos506.Incidence
