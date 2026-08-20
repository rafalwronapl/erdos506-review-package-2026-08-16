import Erdos506.Incidence.ProjectiveCovectorFrame
import Erdos506.Incidence.CompleteQuadrangle

/-!
# Real-projective endpoint for the four-star link

The finite link layer supplies four nonconcurrent base lines and their four
private marked points.  This file records the minimal homogeneous interface
for that data and the scalar endpoint of the triangle-pendant calculation.
It intentionally does not claim that an arbitrary finite four-star link has
already been realized by this projective data.
-/

namespace Erdos506.Incidence

open Matrix

/-- Four nonconcurrent projective base lines together with a private marked
point on each.  Base lines are homogeneous covectors and private points are
homogeneous vectors. -/
structure FourStarProjectiveSkeleton where
  baseLine : Fin 4 → Homogeneous3
  privatePoint : Fin 4 → Homogeneous3
  base_general_position : CompleteQuadrangleGeneralPosition
    (baseLine 0) (baseLine 1) (baseLine 2) (baseLine 3)
  private_ne_zero : ∀ i, privatePoint i ≠ 0
  private_on_base : ∀ i, privatePoint i ⬝ᵥ baseLine i = 0
  private_off_base : ∀ i j, i ≠ j → privatePoint i ⬝ᵥ baseLine j ≠ 0

/-- The opposite base vertex used by an `S`-line. -/
def fourStarOppositeVertex
    (baseLine : Fin 4 → Homogeneous3) (k l : Fin 4) : Homogeneous3 :=
  crossProduct (baseLine k) (baseLine l)

/-- The collinearity determinant for an `Sᵢⱼ` line through private points
`uᵢ,uⱼ` and the opposite base vertex `vₖₗ`. -/
def fourStarSDet (F : FourStarProjectiveSkeleton)
    (i j k l : Fin 4) : ℝ :=
  Matrix.det ![F.privatePoint i, F.privatePoint j,
    fourStarOppositeVertex F.baseLine k l]

/-- The collinearity determinant for a `T`-line through three private
points. -/
def fourStarTDet (F : FourStarProjectiveSkeleton)
    (i j k : Fin 4) : ℝ :=
  Matrix.det ![F.privatePoint i, F.privatePoint j, F.privatePoint k]

/-- The four `S`-determinants of the triangle-pendant pattern
`S₀₁,S₀₂,S₁₂,S₀₃`.  This is a determinant-level endpoint, independent of
any choice of affine chart. -/
def IsFourStarTrianglePendantDeterminantal
    (F : FourStarProjectiveSkeleton) : Prop :=
  fourStarSDet F 0 1 2 3 = 0 ∧
  fourStarSDet F 0 2 1 3 = 0 ∧
  fourStarSDet F 1 2 0 3 = 0 ∧
  fourStarSDet F 0 3 1 2 = 0

/-- Scalar normal coordinates of a triangle-pendant four-star.  The four
equations are precisely the determinant formulas after the standard
complete-quadrangle normalization. -/
structure FourStarTrianglePendantCoordinates where
  a : ℝ
  b : ℝ
  c : ℝ
  d : ℝ
  a_ne_neg_one : a ≠ -1
  s12 : b - a = 0
  s13 : 1 - a * c = 0
  s23 : b - c = 0
  s14 : 1 + d * (1 + a) = 0

/-- The real scalar endpoint of the triangle-pendant case.  This is the
part of four-star rigidity that follows directly from the four displayed
determinant equations; the projective normalization bridge is deliberately
left as a separate geometric theorem. -/
theorem fourStar_trianglePendant_coordinates_unique
    (h : FourStarTrianglePendantCoordinates) :
    h.a = 1 ∧ h.b = 1 ∧ h.c = 1 ∧ h.d = -1 / 2 := by
  have hab : h.b = h.a := sub_eq_zero.mp h.s12
  have hbc : h.b = h.c := sub_eq_zero.mp h.s23
  have hca : h.c = h.a := hbc.symm.trans hab
  have hac : h.a * h.a = 1 := by
    have hs13 := h.s13
    rw [hca] at hs13
    linarith
  have haSq : h.a ^ 2 = 1 := by
    simpa [pow_two] using hac
  have ha : h.a = 1 :=
    (sq_eq_one_iff.mp haSq).resolve_right h.a_ne_neg_one
  have hb : h.b = 1 := hab.trans ha
  have hc : h.c = 1 := hbc.symm.trans hb
  have hd : h.d = -1 / 2 := by
    have hs14 := h.s14
    rw [ha] at hs14
    linarith
  exact ⟨ha, hb, hc, hd⟩

/-! ## Normal-coordinate scalar exclusions -/

/-- The seven determinant polynomials of a normalized real four-star. -/
structure FourStarNormalDeterminants where
  a : ℝ
  b : ℝ
  c : ℝ
  d : ℝ
  a_ne_zero : a ≠ 0
  b_ne_zero : b ≠ 0
  c_ne_zero : c ≠ 0
  d_ne_zero : d ≠ 0
  a_ne_neg_one : a ≠ -1
  b_ne_neg_one : b ≠ -1
  c_ne_neg_one : c ≠ -1
  d_ne_neg_one : d ≠ -1

/-- The normalized private point on the `i`-th base line. -/
def fourStarNormalPrivatePoint
    (N : FourStarNormalDeterminants) : Fin 4 → Homogeneous3 :=
  ![![0, 1, N.a], ![1, 0, N.b], ![1, N.c, 0],
    ![1, N.d, -1 - N.d]]

@[simp] theorem fourStarNormal_t123
    (N : FourStarNormalDeterminants) :
    Matrix.det ![fourStarNormalPrivatePoint N 0,
      fourStarNormalPrivatePoint N 1,
      fourStarNormalPrivatePoint N 2] = N.b + N.a * N.c := by
  simp [fourStarNormalPrivatePoint, Matrix.det_fin_three]

@[simp] theorem fourStarNormal_s12
    (N : FourStarNormalDeterminants) :
    Matrix.det ![fourStarNormalPrivatePoint N 0,
      fourStarNormalPrivatePoint N 1,
      crossProduct (projectiveCovectorNormalLine 2)
        (projectiveCovectorNormalLine 3)] = N.a - N.b := by
  simp [fourStarNormalPrivatePoint, projectiveCovectorNormalLine,
    Matrix.det_fin_three, cross_apply]
  ring

@[simp] theorem fourStarNormal_s13
    (N : FourStarNormalDeterminants) :
    Matrix.det ![fourStarNormalPrivatePoint N 0,
      fourStarNormalPrivatePoint N 2,
      crossProduct (projectiveCovectorNormalLine 1)
        (projectiveCovectorNormalLine 3)] = 1 - N.a * N.c := by
  simp [fourStarNormalPrivatePoint, projectiveCovectorNormalLine,
    Matrix.det_fin_three, cross_apply]

@[simp] theorem fourStarNormal_s14
    (N : FourStarNormalDeterminants) :
    Matrix.det ![fourStarNormalPrivatePoint N 0,
      fourStarNormalPrivatePoint N 3,
      crossProduct (projectiveCovectorNormalLine 1)
        (projectiveCovectorNormalLine 2)] =
          -(1 + N.d * (1 + N.a)) := by
  simp [fourStarNormalPrivatePoint, projectiveCovectorNormalLine,
    Matrix.det_fin_three, cross_apply]
  ring

@[simp] theorem fourStarNormal_s23
    (N : FourStarNormalDeterminants) :
    Matrix.det ![fourStarNormalPrivatePoint N 1,
      fourStarNormalPrivatePoint N 2,
      crossProduct (projectiveCovectorNormalLine 0)
        (projectiveCovectorNormalLine 3)] = N.c - N.b := by
  simp [fourStarNormalPrivatePoint, projectiveCovectorNormalLine,
    Matrix.det_fin_three, cross_apply]
  ring

@[simp] theorem fourStarNormal_s24
    (N : FourStarNormalDeterminants) :
    Matrix.det ![fourStarNormalPrivatePoint N 1,
      fourStarNormalPrivatePoint N 3,
      crossProduct (projectiveCovectorNormalLine 0)
        (projectiveCovectorNormalLine 2)] = -(1 + N.d + N.b) := by
  simp [fourStarNormalPrivatePoint, projectiveCovectorNormalLine,
    Matrix.det_fin_three, cross_apply]
  ring

@[simp] theorem fourStarNormal_s34
    (N : FourStarNormalDeterminants) :
    Matrix.det ![fourStarNormalPrivatePoint N 2,
      fourStarNormalPrivatePoint N 3,
      crossProduct (projectiveCovectorNormalLine 0)
        (projectiveCovectorNormalLine 1)] = N.d - N.c := by
  simp [fourStarNormalPrivatePoint, projectiveCovectorNormalLine,
    Matrix.det_fin_three, cross_apply]

/-- The normalized `T₁₂₃,S₁₄,S₂₄,S₃₄` star is impossible over the reals. -/
theorem fourStarNormal_tStar_impossible
    (N : FourStarNormalDeterminants)
    (hT123 : N.b + N.a * N.c = 0)
    (hS14 : 1 + N.d * (1 + N.a) = 0)
    (hS24 : 1 + N.d + N.b = 0)
    (hS34 : N.d - N.c = 0) : False := by
  have hdc : N.d = N.c := sub_eq_zero.mp hS34
  rw [hdc] at hS14 hS24
  have hb : N.b = -1 - N.c := by linarith
  have hac : N.a * N.c = N.b := by
    rw [hb]
    nlinarith [hS14]
  have hbzero : N.b = 0 := by nlinarith [hT123]
  exact N.b_ne_zero hbzero

/-- The normalized four-cycle `S₁₂,S₂₃,S₃₄,S₁₄` has no real point. -/
theorem fourStarNormal_fourCycle_impossible
    (N : FourStarNormalDeterminants)
    (hS12 : N.b - N.a = 0)
    (hS23 : N.b - N.c = 0)
    (hS34 : N.d - N.c = 0)
    (hS14 : 1 + N.d * (1 + N.a) = 0) : False := by
  have hab : N.b = N.a := sub_eq_zero.mp hS12
  have hbc : N.b = N.c := sub_eq_zero.mp hS23
  have hdc : N.d = N.c := sub_eq_zero.mp hS34
  have heq : N.a ^ 2 + N.a + 1 = 0 := by
    rw [← hab, hbc, ← hdc]
    nlinarith [hS14]
  nlinarith [sq_nonneg (N.a + 1 / 2)]

/-- The normalized triangle-pendant equations have the unique real
solution `(1,1,1,-1/2)`. -/
theorem fourStarNormal_trianglePendant_unique
    (N : FourStarNormalDeterminants)
    (hS12 : N.b - N.a = 0)
    (hS13 : 1 - N.a * N.c = 0)
    (hS23 : N.b - N.c = 0)
    (hS14 : 1 + N.d * (1 + N.a) = 0) :
    N.a = 1 ∧ N.b = 1 ∧ N.c = 1 ∧ N.d = -1 / 2 := by
  exact fourStar_trianglePendant_coordinates_unique
    { a := N.a
      b := N.b
      c := N.c
      d := N.d
      a_ne_neg_one := N.a_ne_neg_one
      s12 := hS12
      s13 := hS13
      s23 := hS23
      s14 := hS14 }

end Erdos506.Incidence
