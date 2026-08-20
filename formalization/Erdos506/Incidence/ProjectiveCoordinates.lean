import Erdos506.V4.Model
import Mathlib.LinearAlgebra.Projectivization.Constructions
import Mathlib.Tactic

/-!
# Homogeneous coordinates for the real affine plane

This file supplies a small coordinate interface between the concrete plane
`Point2` and the real projective plane.  Affine points are lifted as
`(x, y, 1)`.  The line covector through two distinct affine points is their
cross product, so incidence is a dot-product equation and hence a vanishing
three-by-three determinant.

No geometric extremal principle enters here; everything is elementary linear
algebra over `ℝ` and the quotient construction of projective space.
-/

namespace Erdos506.Incidence

open Erdos506.V4
open Matrix
open scoped LinearAlgebra.Projectivization

/-- Three real homogeneous coordinates. -/
abbrev Homogeneous3 := Fin 3 → ℝ

/-- The real projective plane, used both for points and (dually) line
covectors. -/
abbrev RealProjectivePlane := ℙ ℝ Homogeneous3

/-- The affine-chart lift `(x, y) ↦ (x, y, 1)`. -/
def homogeneousLift (p : Point2) : Homogeneous3 :=
  ![p 0, p 1, 1]

@[simp] theorem homogeneousLift_zero (p : Point2) :
    homogeneousLift p 0 = p 0 := rfl

@[simp] theorem homogeneousLift_one (p : Point2) :
    homogeneousLift p 1 = p 1 := rfl

@[simp] theorem homogeneousLift_two (p : Point2) :
    homogeneousLift p 2 = 1 := rfl

/-- An affine-chart lift is nonzero because its last coordinate is one. -/
theorem homogeneousLift_ne_zero (p : Point2) : homogeneousLift p ≠ 0 := by
  intro hzero
  have hlast := congrFun hzero (2 : Fin 3)
  norm_num at hlast

/-- The homogeneous lift retains both affine coordinates. -/
theorem homogeneousLift_injective : Function.Injective homogeneousLift := by
  intro p q hpq
  ext i
  fin_cases i
  · simpa using congrFun hpq (0 : Fin 3)
  · simpa using congrFun hpq (1 : Fin 3)

/-- The canonical embedding of the real affine plane in its projective
completion. -/
noncomputable def projectivePoint (p : Point2) : RealProjectivePlane :=
  Projectivization.mk ℝ (homogeneousLift p) (homogeneousLift_ne_zero p)

/-- The affine chart embeds injectively in projective space: equality up to a
nonzero scalar is forced to use scalar one by the last coordinate. -/
theorem projectivePoint_injective : Function.Injective projectivePoint := by
  intro p q hpq
  have hscaled : ∃ a : ℝ, a • homogeneousLift q = homogeneousLift p :=
    (Projectivization.mk_eq_mk_iff' ℝ
      (homogeneousLift p) (homogeneousLift q)
      (homogeneousLift_ne_zero p) (homogeneousLift_ne_zero q)).1
      (by simpa [projectivePoint] using hpq)
  obtain ⟨a, ha⟩ := hscaled
  have haone : a = 1 := by
    have hlast := congrFun ha (2 : Fin 3)
    simpa using hlast
  apply homogeneousLift_injective
  simpa [haone] using ha.symm

@[simp] theorem projectivePoint_inj {p q : Point2} :
    projectivePoint p = projectivePoint q ↔ p = q := by
  constructor
  · intro hpq
    exact projectivePoint_injective hpq
  · intro hpq
    exact congrArg projectivePoint hpq

/-- The homogeneous covector of the line through `p` and `q`.  Nonzeroness is
proved below under the natural hypothesis `p ≠ q`. -/
def lineCovector (p q : Point2) : Homogeneous3 :=
  crossProduct (homogeneousLift p) (homogeneousLift q)

/-- Explicit affine-coordinate form of the line covector. -/
theorem lineCovector_eq_vec (p q : Point2) :
    lineCovector p q =
      ![p 1 - q 1, q 0 - p 0, p 0 * q 1 - p 1 * q 0] := by
  simp [lineCovector, homogeneousLift, cross_apply]

/-- Distinct affine points have a nonzero cross-product covector. -/
theorem lineCovector_ne_zero {p q : Point2} (hpq : p ≠ q) :
    lineCovector p q ≠ 0 := by
  intro hzero
  apply hpq
  apply projectivePoint_injective
  have hmk :
      Projectivization.mk ℝ (homogeneousLift p) (homogeneousLift_ne_zero p) =
        Projectivization.mk ℝ (homogeneousLift q) (homogeneousLift_ne_zero q) :=
    (Projectivization.mk_eq_mk_iff_crossProduct_eq_zero
      (homogeneousLift_ne_zero p) (homogeneousLift_ne_zero q)).2
      (by simpa [lineCovector] using hzero)
  simpa [projectivePoint] using hmk

@[simp] theorem lineCovector_eq_zero_iff (p q : Point2) :
    lineCovector p q = 0 ↔ p = q := by
  constructor
  · intro hzero
    by_contra hpq
    exact lineCovector_ne_zero hpq hzero
  · rintro rfl
    simp [lineCovector]

/-- The projective line covector determined by two distinct affine points. -/
noncomputable def projectiveLine (p q : Point2) (hpq : p ≠ q) : RealProjectivePlane :=
  Projectivization.mk ℝ (lineCovector p q) (lineCovector_ne_zero hpq)

/-- The preceding raw construction agrees with Mathlib's projective cross
product. -/
theorem projectivePoint_cross_eq_projectiveLine
    {p q : Point2} (hpq : p ≠ q) :
    Projectivization.cross (projectivePoint p) (projectivePoint q) =
      projectiveLine p q hpq := by
  classical
  have hproj : projectivePoint p ≠ projectivePoint q :=
    projectivePoint_injective.ne hpq
  have hproj' :
      Projectivization.mk ℝ (homogeneousLift p) (homogeneousLift_ne_zero p) ≠
        Projectivization.mk ℝ (homogeneousLift q) (homogeneousLift_ne_zero q) := by
    simpa [projectivePoint] using hproj
  change Projectivization.cross
      (Projectivization.mk ℝ (homogeneousLift p) (homogeneousLift_ne_zero p))
      (Projectivization.mk ℝ (homogeneousLift q) (homogeneousLift_ne_zero q)) = _
  rw [Projectivization.cross_mk_of_ne
    (homogeneousLift_ne_zero p) (homogeneousLift_ne_zero q) hproj']
  rfl

/-- Raw homogeneous incidence: the lifted point annihilates the line
covector. -/
def homogeneousIncident (p : Point2) (ell : Homogeneous3) : Prop :=
  homogeneousLift p ⬝ᵥ ell = 0

@[simp] theorem homogeneousIncident_lineCovector_left (p q : Point2) :
    homogeneousIncident p (lineCovector p q) := by
  simp [homogeneousIncident, lineCovector]

@[simp] theorem homogeneousIncident_lineCovector_right (p q : Point2) :
    homogeneousIncident q (lineCovector p q) := by
  simp [homogeneousIncident, lineCovector]

/-- The projective line covector is orthogonal to its first endpoint. -/
theorem projectiveLine_orthogonal_left
    {p q : Point2} (hpq : p ≠ q) :
    Projectivization.orthogonal (projectiveLine p q hpq)
      (projectivePoint p) := by
  rw [← projectivePoint_cross_eq_projectiveLine hpq]
  exact Projectivization.cross_orthogonal_left
    (projectivePoint_injective.ne hpq)

/-- The projective line covector is orthogonal to its second endpoint. -/
theorem projectiveLine_orthogonal_right
    {p q : Point2} (hpq : p ≠ q) :
    Projectivization.orthogonal (projectiveLine p q hpq)
      (projectivePoint q) := by
  rw [← projectivePoint_cross_eq_projectiveLine hpq]
  exact Projectivization.cross_orthogonal_right
    (projectivePoint_injective.ne hpq)

/-- Cyclically arranging the scalar triple product puts the three affine
points in the standard row order `(p,q,r)`. -/
theorem homogeneousLift_dot_lineCovector_eq_det (p q r : Point2) :
    homogeneousLift r ⬝ᵥ lineCovector p q =
      Matrix.det ![homogeneousLift p, homogeneousLift q, homogeneousLift r] := by
  calc
    homogeneousLift r ⬝ᵥ lineCovector p q =
        homogeneousLift r ⬝ᵥ
          crossProduct (homogeneousLift p) (homogeneousLift q) := rfl
    _ = homogeneousLift p ⬝ᵥ
          crossProduct (homogeneousLift q) (homogeneousLift r) :=
      triple_product_permutation _ _ _
    _ = Matrix.det ![homogeneousLift p, homogeneousLift q,
          homogeneousLift r] :=
      triple_product_eq_det _ _ _

/-- A third affine point is incident with the line covector through `p,q`
exactly when the determinant of the three homogeneous rows vanishes. -/
theorem homogeneousIncident_lineCovector_iff_det_eq_zero
    (p q r : Point2) :
    homogeneousIncident r (lineCovector p q) ↔
      Matrix.det ![homogeneousLift p, homogeneousLift q,
        homogeneousLift r] = 0 := by
  rw [homogeneousIncident, homogeneousLift_dot_lineCovector_eq_det]

/-- Projective formulation of the same third-point determinant criterion. -/
theorem projectivePoint_orthogonal_projectiveLine_iff_det_eq_zero
    {p q : Point2} (hpq : p ≠ q) (r : Point2) :
    Projectivization.orthogonal (projectivePoint r)
        (projectiveLine p q hpq) ↔
      Matrix.det ![homogeneousLift p, homogeneousLift q,
        homogeneousLift r] = 0 := by
  simpa only [projectivePoint, projectiveLine,
      Projectivization.orthogonal_mk, homogeneousIncident] using
    homogeneousIncident_lineCovector_iff_det_eq_zero p q r

/-- Homogeneous lift `(dx,dy,0)` of an affine direction. -/
def directionLift (v : Point2) : Homogeneous3 :=
  ![v 0, v 1, 0]

@[simp] theorem directionLift_zero (v : Point2) :
    directionLift v 0 = v 0 := rfl

@[simp] theorem directionLift_one (v : Point2) :
    directionLift v 1 = v 1 := rfl

@[simp] theorem directionLift_two (v : Point2) :
    directionLift v 2 = 0 := rfl

/-- A nonzero affine direction remains nonzero after adding last coordinate
zero. -/
theorem directionLift_ne_zero {v : Point2} (hv : v ≠ 0) :
    directionLift v ≠ 0 := by
  intro hzero
  apply hv
  ext i
  fin_cases i
  · simpa using congrFun hzero (0 : Fin 3)
  · simpa using congrFun hzero (1 : Fin 3)

/-- The point at infinity represented by a nonzero affine direction. -/
noncomputable def pointAtInfinity (v : Point2) (hv : v ≠ 0) : RealProjectivePlane :=
  Projectivization.mk ℝ (directionLift v) (directionLift_ne_zero hv)

/-- A direction point (last coordinate zero) never lies in the affine chart
(last coordinate nonzero). -/
theorem pointAtInfinity_ne_projectivePoint
    {v : Point2} (hv : v ≠ 0) (p : Point2) :
    pointAtInfinity v hv ≠ projectivePoint p := by
  intro heq
  have hscaled : ∃ a : ℝ, a • homogeneousLift p = directionLift v :=
    (Projectivization.mk_eq_mk_iff' ℝ
      (directionLift v) (homogeneousLift p)
      (directionLift_ne_zero hv) (homogeneousLift_ne_zero p)).1
      (by simpa [pointAtInfinity, projectivePoint] using heq)
  obtain ⟨a, ha⟩ := hscaled
  have hazero : a = 0 := by
    have hlast := congrFun ha (2 : Fin 3)
    simpa using hlast
  apply directionLift_ne_zero hv
  simpa [hazero] using ha.symm

end Erdos506.Incidence
