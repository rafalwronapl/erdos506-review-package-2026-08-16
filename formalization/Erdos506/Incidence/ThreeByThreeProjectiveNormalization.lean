import Erdos506.Incidence.ProjectiveCompletion
import Erdos506.Incidence.ProjectiveCoordinates
import Erdos506.Incidence.RealThreeByThreeGrid

/-!
# The parameter wall for a projective three-by-three grid

Two triples of distinct concurrent projective lines with nine distinct
crossings do have an affine grid chart, but they do **not** in general have
the rigid chart `{-1,0,1}^2`.  After choosing the two pencil centres as
points at infinity, the two remaining projective parameters are represented
by `a` and `b` below.  The special normal grid is precisely `a = b = 1`.

Thus a proof that an arbitrary two-pencil grid has the rigid normal form
must additionally establish the two cross-ratio identities forcing those
parameters to be one.  This file makes the unconditional parameterized
affine/projective endpoint explicit, rather than treating that missing
cross-ratio input as a normalization assumption.
-/

namespace Erdos506.Incidence

open Erdos506.V4

/-- Three affine levels in one pencil after sending its centre to infinity.
The first two levels fix the affine scale; the third is the remaining
projective parameter. -/
def threeByThreePencilCoordinate (a : ℝ) : Fin 3 → ℝ
  | 0 => -1
  | 1 => 0
  | 2 => a

/-- The parameterized affine grid obtained from two pencil parameters. -/
def threeByThreeParameterizedGridPoint (a b : ℝ) (ij : Fin 3 × Fin 3) :
    ℝ × ℝ :=
  (threeByThreePencilCoordinate a ij.1,
    threeByThreePencilCoordinate b ij.2)

/-- The same grid point in the concrete affine plane used by the projective
completion. -/
noncomputable def threeByThreeParameterizedPoint2
    (a b : ℝ) (ij : Fin 3 × Fin 3) : Point2 :=
  EuclideanSpace.single (0 : Fin 2) (threeByThreePencilCoordinate a ij.1) +
    EuclideanSpace.single (1 : Fin 2) (threeByThreePencilCoordinate b ij.2)

@[simp] theorem threeByThreeParameterizedPoint2_apply_zero
    (a b : ℝ) (ij : Fin 3 × Fin 3) :
    threeByThreeParameterizedPoint2 a b ij (0 : Fin 2) =
      threeByThreePencilCoordinate a ij.1 := by
  simp [threeByThreeParameterizedPoint2]

@[simp] theorem threeByThreeParameterizedPoint2_apply_one
    (a b : ℝ) (ij : Fin 3 × Fin 3) :
    threeByThreeParameterizedPoint2 a b ij (1 : Fin 2) =
      threeByThreePencilCoordinate b ij.2 := by
  simp [threeByThreeParameterizedPoint2]

/-- Canonical projective representatives of the parameterized grid. -/
noncomputable def threeByThreeParameterizedProjectivePoint
    (a b : ℝ) (ij : Fin 3 × Fin 3) : RealProjectivePoint :=
  affinePointToProjective (threeByThreeParameterizedPoint2 a b ij)

/-- The standard rigid grid is the special parameter pair `(1,1)`. -/
theorem threeByThreePencilCoordinate_one (i : Fin 3) :
    threeByThreePencilCoordinate 1 i = (i : ℝ) - 1 := by
  fin_cases i <;> norm_num [threeByThreePencilCoordinate]

/-- The parameterized point formula specializes definitionally to the
standard three-by-three coordinate table at `(1,1)`. -/
theorem threeByThreeParameterizedGridPoint_one_one (ij : Fin 3 × Fin 3) :
    threeByThreeParameterizedGridPoint 1 1 ij =
      ((ij.1 : ℝ) - 1, (ij.2 : ℝ) - 1) := by
  simp [threeByThreeParameterizedGridPoint, threeByThreePencilCoordinate_one]

/-- A nondegenerate pencil parameter gives three distinct affine levels. -/
theorem threeByThreePencilCoordinate_injective
    {a : ℝ} (ha_minus : a ≠ -1) (ha_zero : a ≠ 0) :
    Function.Injective (threeByThreePencilCoordinate a) := by
  intro i j hij
  fin_cases i <;> fin_cases j <;>
    simp [threeByThreePencilCoordinate] at hij ⊢ <;>
    first | rfl | exact False.elim (ha_minus (by linarith)) |
      exact False.elim (ha_zero (by linarith))

/-- Under the two nondegeneracy conditions, the nine parameterized affine
coordinates really are nine distinct points. -/
theorem threeByThreeParameterizedGridPoint_injective
    {a b : ℝ}
    (ha_minus : a ≠ -1) (ha_zero : a ≠ 0)
    (hb_minus : b ≠ -1) (hb_zero : b ≠ 0) :
    Function.Injective (threeByThreeParameterizedGridPoint a b) := by
  intro ij kl h
  apply Prod.ext
  · exact threeByThreePencilCoordinate_injective ha_minus ha_zero
      (congrArg Prod.fst h)
  · exact threeByThreePencilCoordinate_injective hb_minus hb_zero
      (congrArg Prod.snd h)

/-- Projective completion does not collapse any of the nine parameterized
affine grid points. -/
theorem threeByThreeParameterizedProjectivePoint_injective
    {a b : ℝ}
    (ha_minus : a ≠ -1) (ha_zero : a ≠ 0)
    (hb_minus : b ≠ -1) (hb_zero : b ≠ 0) :
    Function.Injective (threeByThreeParameterizedProjectivePoint a b) := by
  intro ij kl h
  have hpoint : threeByThreeParameterizedPoint2 a b ij =
      threeByThreeParameterizedPoint2 a b kl :=
    affinePointToProjective_injective h
  apply threeByThreeParameterizedGridPoint_injective
    ha_minus ha_zero hb_minus hb_zero
  apply Prod.ext
  · simpa [threeByThreeParameterizedPoint2] using
      congrArg (fun z : Point2 => z (0 : Fin 2)) hpoint
  · simpa [threeByThreeParameterizedPoint2] using
      congrArg (fun z : Point2 => z (1 : Fin 2)) hpoint

/-- The affine line covectors of the first (row) pencil in the parameter
grid.  Their common projective point is the horizontal ideal point. -/
def threeByThreeParameterizedRowCovector (b : ℝ) (s : Fin 3) : Homogeneous3 :=
  ![0, 1, -threeByThreePencilCoordinate b s]

/-- The affine line covectors of the second (column) pencil in the parameter
grid.  Their common projective point is the vertical ideal point. -/
def threeByThreeParameterizedColumnCovector (a : ℝ) (r : Fin 3) : Homogeneous3 :=
  ![1, 0, -threeByThreePencilCoordinate a r]

/-- The row covector vanishes on precisely its displayed grid crossings. -/
theorem threeByThreeParameterizedRowCovector_incident
    (a b : ℝ) (r s : Fin 3) :
    homogeneousIncident (threeByThreeParameterizedPoint2 a b (r, s))
      (threeByThreeParameterizedRowCovector b s) := by
  simp [homogeneousIncident, homogeneousLift,
    threeByThreeParameterizedPoint2,
    threeByThreeParameterizedRowCovector, dotProduct,
    Fin.sum_univ_three]

/-- The column covector vanishes on precisely its displayed grid crossings. -/
theorem threeByThreeParameterizedColumnCovector_incident
    (a b : ℝ) (r s : Fin 3) :
    homogeneousIncident (threeByThreeParameterizedPoint2 a b (r, s))
      (threeByThreeParameterizedColumnCovector a r) := by
  simp [homogeneousIncident, homogeneousLift,
    threeByThreeParameterizedPoint2,
    threeByThreeParameterizedColumnCovector, dotProduct,
    Fin.sum_univ_three]

end Erdos506.Incidence
