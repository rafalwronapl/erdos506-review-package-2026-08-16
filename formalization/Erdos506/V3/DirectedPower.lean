import Erdos506.V3.EquationCircle

/-!
# Directed power of a point

For two parametrised lines through the same point, the products of the two
directed root parameters differ by the squared lengths of the direction
vectors.  This is the sign-sensitive form of the intersecting-secants
theorem needed by the six-five-circle obstruction.
-/

namespace Erdos506.V3

open Erdos506.V4

noncomputable def properCircleEquationA (c : ProperCircle) : ℝ :=
  -2 * c.1.center 0

noncomputable def properCircleEquationB (c : ProperCircle) : ℝ :=
  -2 * c.1.center 1

noncomputable def properCircleEquationC (c : ProperCircle) : ℝ :=
  c.1.center 0 ^ 2 + c.1.center 1 ^ 2 - c.1.radius ^ 2

theorem properCircleEquation_eq_dist_sq_sub (c : ProperCircle) (p : Point2) :
    circleEquation (properCircleEquationA c) (properCircleEquationB c)
        (properCircleEquationC c) p =
      dist c.1.center p ^ 2 - c.1.radius ^ 2 := by
  rw [dist_eq_norm, EuclideanSpace.real_norm_sq_eq]
  simp [circleEquation, properCircleEquationA, properCircleEquationB,
    properCircleEquationC, Fin.sum_univ_two]
  ring

theorem mem_properCircle_iff_equation (c : ProperCircle) (p : Point2) :
    p ∈ (c.1 : Set Point2) ↔
      circleEquation (properCircleEquationA c) (properCircleEquationB c)
        (properCircleEquationC c) p = 0 := by
  constructor
  · intro hp
    have hd := EuclideanGeometry.mem_sphere'.mp hp
    change dist c.1.center p = c.1.radius at hd
    rw [properCircleEquation_eq_dist_sq_sub, hd]
    ring
  · intro hp
    apply EuclideanGeometry.mem_sphere'.mpr
    change dist c.1.center p = c.1.radius
    apply (sq_eq_sq₀ dist_nonneg c.2.le).mp
    rw [← sub_eq_zero]
    rw [← properCircleEquation_eq_dist_sq_sub]
    exact hp

noncomputable def affineParamPoint (o u : Point2) (t : ℝ) : Point2 :=
  o + t • u

@[simp] theorem affineParamPoint_apply (o u : Point2) (t : ℝ) (i : Fin 2) :
    affineParamPoint o u t i = o i + t * u i := by
  simp [affineParamPoint]

@[simp] theorem affineParamPoint_zero (o u : Point2) :
    affineParamPoint o u 0 = o := by
  simp [affineParamPoint]

@[simp] theorem affineParamPoint_endpoint (p q : Point2) :
    affineParamPoint p (q - p) 1 = q := by
  simp [affineParamPoint]

theorem affineParamPoint_reverse (p q : Point2) (t : ℝ) :
    affineParamPoint q (p - q) (1 - t) =
      affineParamPoint p (q - p) t := by
  ext i
  simp [affineParamPoint]
  ring

def directionSq (u : Point2) : ℝ := u 0 ^ 2 + u 1 ^ 2

@[simp] theorem directionSq_neg (u : Point2) :
    directionSq (-u) = directionSq u := by
  simp [directionSq]

theorem directionSq_sub_comm (p q : Point2) :
    directionSq (p - q) = directionSq (q - p) := by
  rw [show p - q = -(q - p) by abel, directionSq_neg]

theorem directionSq_eq_zero_iff (u : Point2) :
    directionSq u = 0 ↔ u = 0 := by
  constructor
  · intro h
    have h0 : u 0 = 0 := by
      unfold directionSq at h
      nlinarith [sq_nonneg (u 0), sq_nonneg (u 1)]
    have h1 : u 1 = 0 := by
      unfold directionSq at h
      nlinarith [sq_nonneg (u 0), sq_nonneg (u 1)]
    ext i
    fin_cases i
    · simpa using h0
    · simpa using h1
  · rintro rfl
    simp [directionSq]

theorem directionSq_sub_ne_zero {p q : Point2} (hpq : p ≠ q) :
    directionSq (p - q) ≠ 0 := by
  intro h
  apply hpq
  exact sub_eq_zero.mp ((directionSq_eq_zero_iff (p - q)).mp h)

/-- Two named points strictly distinct from both endpoints of a parametrised
side, and from one another. -/
def DistinctSideParameters (r s : ℝ) : Prop :=
  r ≠ 0 ∧ r ≠ 1 ∧ s ≠ 0 ∧ s ≠ 1 ∧ r ≠ s

def lineCircleLinearCoefficient (A B : ℝ) (o u : Point2) : ℝ :=
  2 * o 0 * u 0 + 2 * o 1 * u 1 + A * u 0 + B * u 1

theorem circleEquation_affineParamPoint (A B C : ℝ)
    (o u : Point2) (t : ℝ) :
    circleEquation A B C (affineParamPoint o u t) =
      directionSq u * t ^ 2 +
        lineCircleLinearCoefficient A B o u * t + circleEquation A B C o := by
  simp [circleEquation, affineParamPoint, directionSq,
    lineCircleLinearCoefficient]
  ring

theorem quadratic_constant_eq_leading_mul_roots
    {K L D t₁ t₂ : ℝ} (hne : t₁ ≠ t₂)
    (h₁ : K * t₁ ^ 2 + L * t₁ + D = 0)
    (h₂ : K * t₂ ^ 2 + L * t₂ + D = 0) :
    D = K * t₁ * t₂ := by
  have hprod : (t₂ - t₁) * (D - K * t₁ * t₂) = 0 := by
    linear_combination t₂ * h₁ - t₁ * h₂
  have hsub : t₂ - t₁ ≠ 0 := sub_ne_zero.mpr hne.symm
  have hzero : D - K * t₁ * t₂ = 0 :=
    (mul_eq_zero.mp hprod).resolve_left hsub
  linarith

theorem directed_power_of_four_cocircular_points
    (c : ProperCircle) (o u v : Point2)
    {t₁ t₂ s₁ s₂ : ℝ} (ht : t₁ ≠ t₂) (hs : s₁ ≠ s₂)
    (ht₁ : affineParamPoint o u t₁ ∈ (c.1 : Set Point2))
    (ht₂ : affineParamPoint o u t₂ ∈ (c.1 : Set Point2))
    (hs₁ : affineParamPoint o v s₁ ∈ (c.1 : Set Point2))
    (hs₂ : affineParamPoint o v s₂ ∈ (c.1 : Set Point2)) :
    directionSq u * t₁ * t₂ = directionSq v * s₁ * s₂ := by
  let A := properCircleEquationA c
  let B := properCircleEquationB c
  let C := properCircleEquationC c
  let Lu := lineCircleLinearCoefficient A B o u
  let Lv := lineCircleLinearCoefficient A B o v
  let D := circleEquation A B C o
  have hut₁ : directionSq u * t₁ ^ 2 + Lu * t₁ + D = 0 := by
    rw [← circleEquation_affineParamPoint]
    exact (mem_properCircle_iff_equation c _).mp ht₁
  have hut₂ : directionSq u * t₂ ^ 2 + Lu * t₂ + D = 0 := by
    rw [← circleEquation_affineParamPoint]
    exact (mem_properCircle_iff_equation c _).mp ht₂
  have hvs₁ : directionSq v * s₁ ^ 2 + Lv * s₁ + D = 0 := by
    rw [← circleEquation_affineParamPoint]
    exact (mem_properCircle_iff_equation c _).mp hs₁
  have hvs₂ : directionSq v * s₂ ^ 2 + Lv * s₂ + D = 0 := by
    rw [← circleEquation_affineParamPoint]
    exact (mem_properCircle_iff_equation c _).mp hs₂
  have hu := quadratic_constant_eq_leading_mul_roots ht hut₁ hut₂
  have hv := quadratic_constant_eq_leading_mul_roots hs hvs₁ hvs₂
  exact hu.symm.trans hv

end Erdos506.V3
