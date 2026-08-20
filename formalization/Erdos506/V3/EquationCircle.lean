import Erdos506.V3.Model

/-!
# Coordinate equations for proper circles in the real plane

This module bridges the elementary equation
`x² + y² + A x + B y + C = 0` to the semantic Euclidean-sphere model used
by the formalization.  It also supplies the usual orientation certificate
for noncollinearity.
-/

namespace Erdos506.V3

open Erdos506.V4

noncomputable def pointOfCoords (x y : ℝ) : Point2 :=
  EuclideanSpace.single (0 : Fin 2) x +
    EuclideanSpace.single (1 : Fin 2) y

@[simp] theorem pointOfCoords_apply_zero (x y : ℝ) :
    pointOfCoords x y (0 : Fin 2) = x := by
  simp [pointOfCoords]

@[simp] theorem pointOfCoords_apply_one (x y : ℝ) :
    pointOfCoords x y (1 : Fin 2) = y := by
  simp [pointOfCoords]

def circleEquation (A B C : ℝ) (p : Point2) : ℝ :=
  p 0 ^ 2 + p 1 ^ 2 + A * p 0 + B * p 1 + C

noncomputable def equationCircleCenter (A B : ℝ) : Point2 :=
  pointOfCoords (-A / 2) (-B / 2)

noncomputable def equationCircleRadiusSq (A B C : ℝ) : ℝ :=
  (A ^ 2 + B ^ 2) / 4 - C

noncomputable def properCircleOfEquation (A B C : ℝ)
    (hpos : 0 < equationCircleRadiusSq A B C) : ProperCircle :=
  ⟨⟨equationCircleCenter A B, Real.sqrt (equationCircleRadiusSq A B C)⟩,
    Real.sqrt_pos.2 hpos⟩

theorem dist_equationCircleCenter_sq (A B : ℝ) (p : Point2) :
    dist (equationCircleCenter A B) p ^ 2 =
      p 0 ^ 2 + p 1 ^ 2 + A * p 0 + B * p 1 +
        (A ^ 2 + B ^ 2) / 4 := by
  rw [dist_eq_norm, EuclideanSpace.real_norm_sq_eq]
  simp [equationCircleCenter, pointOfCoords, Fin.sum_univ_two]
  ring

@[simp] theorem mem_properCircleOfEquation_iff (A B C : ℝ)
    (hpos : 0 < equationCircleRadiusSq A B C) (p : Point2) :
    p ∈ ((properCircleOfEquation A B C hpos).1 : Set Point2) ↔
      circleEquation A B C p = 0 := by
  have hsqrt : Real.sqrt (equationCircleRadiusSq A B C) ^ 2 =
      equationCircleRadiusSq A B C :=
    Real.sq_sqrt hpos.le
  constructor
  · intro hp
    have hd := EuclideanGeometry.mem_sphere'.mp hp
    change dist (equationCircleCenter A B) p =
      Real.sqrt (equationCircleRadiusSq A B C) at hd
    have hd2 := congrArg (fun z : ℝ => z ^ 2) hd
    dsimp at hd2
    rw [dist_equationCircleCenter_sq, hsqrt] at hd2
    unfold circleEquation equationCircleRadiusSq at *
    linarith
  · intro hp
    apply EuclideanGeometry.mem_sphere'.mpr
    change dist (equationCircleCenter A B) p =
      Real.sqrt (equationCircleRadiusSq A B C)
    apply (sq_eq_sq₀ dist_nonneg (Real.sqrt_nonneg _)).mp
    rw [dist_equationCircleCenter_sq, hsqrt]
    unfold circleEquation equationCircleRadiusSq at *
    linarith

def orientation (p q r : Point2) : ℝ :=
  (q 0 - p 0) * (r 1 - p 1) -
    (q 1 - p 1) * (r 0 - p 0)

theorem not_collinear_of_orientation_ne_zero (p q r : Point2)
    (hori : orientation p q r ≠ 0) :
    ¬Collinear ℝ ({p, q, r} : Set Point2) := by
  intro hcol
  rw [collinear_iff_of_mem
    (show p ∈ ({p, q, r} : Set Point2) by simp)] at hcol
  obtain ⟨v, hv⟩ := hcol
  obtain ⟨a, ha⟩ := hv q (by simp)
  obtain ⟨b, hb⟩ := hv r (by simp)
  apply hori
  rw [ha, hb]
  simp [orientation]
  ring

end Erdos506.V3
