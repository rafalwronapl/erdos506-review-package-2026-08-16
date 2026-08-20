import Erdos506.Incidence.FiveConicNormalQuadrangle
import Erdos506.Incidence.FiveConicNormalSeparator
import Erdos506.Incidence.FiveConicProjectiveTransport

/-!
# Transporting the normal five-conic separator

The algebraic separator is stated in the standard binary Veronese chart.
This file records its exact transport through the concrete `GL₃` associated
to a proper circle and a projective parameter change.  It is deliberately a
raw determinant statement: the separate projective-representative bridge
turns page incidences into this input.
-/

namespace Erdos506.Incidence

open Erdos506.V4
open Matrix

/-- The binary Veronese vector at the standard infinite parameter. -/
theorem fiveConicBinaryVeronese_infinity :
    fiveConicBinaryVeronese realProjectiveLineInfinityVector =
      fiveConicNormalInfinity := by
  ext i
  fin_cases i <;>
    norm_num [fiveConicBinaryVeronese, realProjectiveLineInfinityVector,
      fiveConicNormalInfinity]

/-- The induced `GL₃` sends a normal finite conic representative to the
literal homogeneous representative of the corresponding point on the
concrete proper circle. -/
theorem fiveConicProjectiveTransport_normalPoint
    (c : ProperCircle) (g : GL (Fin 2) ℝ) (t : ℝ) :
    fiveConicProjectiveTransport c g • fiveConicNormalPoint t =
      properCircleVeroneseVector c
        (g • fiveConicAffineParameterVector t) := by
  rw [← fiveConicBinaryVeronese_affine]
  exact fiveConicProjectiveTransport_mulVec c g
    (fiveConicAffineParameterVector t)

/-- The analogous literal transport statement at the parameter infinity. -/
theorem fiveConicProjectiveTransport_normalInfinity
    (c : ProperCircle) (g : GL (Fin 2) ℝ) :
    fiveConicProjectiveTransport c g • fiveConicNormalInfinity =
      properCircleVeroneseVector c
        (g • realProjectiveLineInfinityVector) := by
  rw [← fiveConicBinaryVeronese_infinity]
  exact fiveConicProjectiveTransport_mulVec c g
    realProjectiveLineInfinityVector

/-- The only possible pair of distinct normal diagonal centres lying with
the fifth normal conic point on one line remains the pair `0,1` after every
concrete proper-circle/projective-parameter transport. -/
theorem fiveConicProjectiveTransport_collinear_diagonal_pair_eq_zero_one
    (c : ProperCircle) (g : GL (Fin 2) ℝ) {lam t : ℝ}
    (hlam : 1 < lam) (ht : lam < t)
    (i j : Fin 3) (hij : i ≠ j)
    (hcol : Matrix.det ![
      fiveConicProjectiveTransport c g • fiveConicNormalPoint t,
      fiveConicProjectiveTransport c g • fiveConicNormalDiagonal lam i,
      fiveConicProjectiveTransport c g • fiveConicNormalDiagonal lam j] = 0) :
    (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0) := by
  apply fiveConicNormal_collinear_diagonal_pair_eq_zero_one
    hlam ht i j hij
  exact (det_eq_zero_iff_generalLinear_smul_three
    (fiveConicProjectiveTransport c g)
    (fiveConicNormalPoint t)
    (fiveConicNormalDiagonal lam i)
    (fiveConicNormalDiagonal lam j)).mp hcol

end Erdos506.Incidence
