import Erdos506.Incidence.FiveConicOneSingleTraceRigidity
import Erdos506.Incidence.RealProjectiveHarmonicFiveCap

/-!
# Quadratic projective transport for a real five-conic

The cyclic separator for a five-point conic is computed in the normal
Veronese coordinates `[t²:t:1]`.  This file records the literal change of
coordinates from an arbitrary proper circle and from an arbitrary `GL₂`
change of its projective parameter.  It is deliberately only a transport
layer: no cyclic chamber, page, or host assumption is introduced here.

The two matrices below are useful independently of the C39 router:

* `fiveConicSymmetricSquare` is the degree-two representation of a `2×2`
  parameter matrix;
* `properCircleVeroneseMatrix` identifies the standard binary Veronese
  coordinates with the homogeneous lift of a concrete proper circle.
-/

namespace Erdos506.Incidence

open Erdos506.V4
open Matrix

/-! ## Binary and affine Veronese coordinates -/

/-- The homogeneous binary Veronese vector in the basis
`u₀², u₀u₁, u₁²`. -/
def fiveConicBinaryVeronese
    (u : RealProjectiveLineVector) : Homogeneous3 :=
  ![u 0 ^ 2, u 0 * u 1, u 1 ^ 2]

/-- The affine parameter vector representing `[t:1]`. -/
def fiveConicAffineParameterVector (t : ℝ) : RealProjectiveLineVector :=
  ![t, 1]

theorem fiveConicAffineParameterVector_ne_zero (t : ℝ) :
    fiveConicAffineParameterVector t ≠ 0 := by
  intro hzero
  have hlast := congrFun hzero (1 : Fin 2)
  simp [fiveConicAffineParameterVector] at hlast

/-- The binary and affine presentations of the normal five-conic agree. -/
theorem fiveConicBinaryVeronese_affine (t : ℝ) :
    fiveConicBinaryVeronese (fiveConicAffineParameterVector t) =
      fiveConicNormalPoint t := by
  ext i
  fin_cases i <;>
    simp [fiveConicBinaryVeronese, fiveConicAffineParameterVector,
      fiveConicNormalPoint]

/-! ## The symmetric-square action -/

/-- The degree-two matrix induced by a binary parameter matrix. -/
def fiveConicSymmetricSquare
    (g : Matrix (Fin 2) (Fin 2) ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  ![
    ![g 0 0 ^ 2, 2 * g 0 0 * g 0 1, g 0 1 ^ 2],
    ![g 0 0 * g 1 0, g 0 0 * g 1 1 + g 0 1 * g 1 0,
      g 0 1 * g 1 1],
    ![g 1 0 ^ 2, 2 * g 1 0 * g 1 1, g 1 1 ^ 2]
  ]

/-- Applying the symmetric square is literally the same as first changing
the binary parameter and then applying the Veronese map. -/
theorem fiveConicSymmetricSquare_mulVec
    (g : Matrix (Fin 2) (Fin 2) ℝ) (u : RealProjectiveLineVector) :
    fiveConicSymmetricSquare g *ᵥ fiveConicBinaryVeronese u =
      fiveConicBinaryVeronese (g *ᵥ u) := by
  ext i
  fin_cases i <;>
    simp [fiveConicSymmetricSquare, fiveConicBinaryVeronese,
      Matrix.mulVec, dotProduct, Fin.sum_univ_two, Fin.sum_univ_three,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two] <;>
    ring

/-- The symmetric-square determinant is the cube of the binary determinant. -/
theorem fiveConicSymmetricSquare_det
    (g : Matrix (Fin 2) (Fin 2) ℝ) :
    Matrix.det (fiveConicSymmetricSquare g) = (Matrix.det g) ^ 3 := by
  simp [fiveConicSymmetricSquare, Matrix.det_fin_two,
    Matrix.det_fin_three, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two]
  ring

theorem fiveConicSymmetricSquare_det_ne_zero
    (g : GL (Fin 2) ℝ) :
    Matrix.det (fiveConicSymmetricSquare (g : Matrix (Fin 2) (Fin 2) ℝ)) ≠ 0 := by
  rw [fiveConicSymmetricSquare_det]
  exact pow_ne_zero 3 (Matrix.GeneralLinearGroup.det_ne_zero g)

/-! ## Transport from the concrete proper circle -/

/-- The invertible linear map from binary Veronese coordinates to the
homogeneous lift of the displayed proper circle. -/
def properCircleVeroneseMatrix
    (c : ProperCircle) : Matrix (Fin 3) (Fin 3) ℝ :=
  ![
    ![c.1.center 0 + c.1.radius, 0, c.1.center 0 - c.1.radius],
    ![c.1.center 1, 2 * c.1.radius, c.1.center 1],
    ![1, 0, 1]
  ]

/-- The concrete circle Veronese vector is the binary Veronese vector after
the displayed invertible linear coordinate change. -/
theorem properCircleVeroneseVector_eq_matrix_mulVec
    (c : ProperCircle) (u : RealProjectiveLineVector) :
    properCircleVeroneseVector c u =
      properCircleVeroneseMatrix c *ᵥ fiveConicBinaryVeronese u := by
  ext i
  fin_cases i <;>
    simp [properCircleVeroneseVector, properCircleVeroneseMatrix,
      fiveConicBinaryVeronese, realProjectiveLineNormSq,
      Matrix.mulVec, dotProduct,
      Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two] <;>
    ring

/-- The circle coordinate change is nonsingular; its determinant is
`4 r²`. -/
theorem properCircleVeroneseMatrix_det (c : ProperCircle) :
    Matrix.det (properCircleVeroneseMatrix c) = 4 * c.1.radius ^ 2 := by
  simp [properCircleVeroneseMatrix, Matrix.det_fin_three,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two]
  ring

theorem properCircleVeroneseMatrix_det_ne_zero (c : ProperCircle) :
    Matrix.det (properCircleVeroneseMatrix c) ≠ 0 := by
  rw [properCircleVeroneseMatrix_det]
  exact mul_ne_zero (by norm_num) (pow_ne_zero 2 c.2.ne')

/-- Combining the two literal matrices transports a parameter projectivity
through the homogeneous proper-circle parametrization. -/
theorem properCircleVeroneseVector_parameter_transform
    (c : ProperCircle) (g : Matrix (Fin 2) (Fin 2) ℝ)
    (u : RealProjectiveLineVector) :
    properCircleVeroneseVector c (g *ᵥ u) =
      properCircleVeroneseMatrix c *ᵥ
        (fiveConicSymmetricSquare g *ᵥ fiveConicBinaryVeronese u) := by
  rw [properCircleVeroneseVector_eq_matrix_mulVec,
    fiveConicSymmetricSquare_mulVec]

/-! ## The induced projective-plane equivalence -/

/-- The actual `GL₃` transport obtained by first changing the parameter and
then identifying the binary conic with the displayed proper circle. -/
noncomputable def fiveConicProjectiveTransport
    (c : ProperCircle) (g : GL (Fin 2) ℝ) : GL (Fin 3) ℝ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero
    (properCircleVeroneseMatrix c *
      fiveConicSymmetricSquare (g : Matrix (Fin 2) (Fin 2) ℝ))
    (by
      rw [Matrix.det_mul]
      exact mul_ne_zero (properCircleVeroneseMatrix_det_ne_zero c)
        (fiveConicSymmetricSquare_det_ne_zero g))

/-- On binary Veronese vectors the induced plane projectivity is exactly
the concrete proper-circle parametrization after the parameter change. -/
theorem fiveConicProjectiveTransport_mulVec
    (c : ProperCircle) (g : GL (Fin 2) ℝ)
    (u : RealProjectiveLineVector) :
    fiveConicProjectiveTransport c g • fiveConicBinaryVeronese u =
      properCircleVeroneseVector c (g • u) := by
  change (properCircleVeroneseMatrix c *
      fiveConicSymmetricSquare (g : Matrix (Fin 2) (Fin 2) ℝ)) *ᵥ
        fiveConicBinaryVeronese u =
      properCircleVeroneseVector c
        ((g : Matrix (Fin 2) (Fin 2) ℝ) *ᵥ u)
  rw [← Matrix.mulVec_mulVec]
  exact (properCircleVeroneseVector_parameter_transform c
    (g : Matrix (Fin 2) (Fin 2) ℝ) u).symm

/-- Collinearity of any three binary conic representatives is preserved
exactly by the explicit proper-circle/projective-parameter transport. -/
theorem fiveConicProjectiveTransport_det_eq_zero_iff
    (c : ProperCircle) (g : GL (Fin 2) ℝ)
    (u v w : RealProjectiveLineVector) :
    Matrix.det ![properCircleVeroneseVector c (g • u),
      properCircleVeroneseVector c (g • v),
      properCircleVeroneseVector c (g • w)] = 0 ↔
      Matrix.det ![fiveConicBinaryVeronese u,
        fiveConicBinaryVeronese v, fiveConicBinaryVeronese w] = 0 := by
  have htransport := det_eq_zero_iff_generalLinear_smul_three
    (fiveConicProjectiveTransport c g)
    (fiveConicBinaryVeronese u) (fiveConicBinaryVeronese v)
    (fiveConicBinaryVeronese w)
  rw [fiveConicProjectiveTransport_mulVec,
    fiveConicProjectiveTransport_mulVec,
    fiveConicProjectiveTransport_mulVec] at htransport
  exact htransport

end Erdos506.Incidence
