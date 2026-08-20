import Erdos506.V3.DirectedPower
import Mathlib.Geometry.Euclidean.Inversion.ImageHyperplane

/-!
# Inversion of a proper circle away from the inversion centre

Mathlib already supplies the line/circle dictionary for circles through the
centre of inversion.  Here we prove the complementary fact needed by V3: a
proper circle not through the centre is sent to another proper circle.  The
proof is an exact two-coordinate calculation over `ℝ`.
-/

namespace Erdos506.V3

open Erdos506.V4

theorem directionSq_sub_eq_dist_sq (p q : Point2) :
    directionSq (p - q) = dist p q ^ 2 := by
  rw [dist_eq_norm, EuclideanSpace.real_norm_sq_eq]
  simp [directionSq, Fin.sum_univ_two]

noncomputable def circleInversionDelta (o : Point2) (c : ProperCircle) : ℝ :=
  directionSq (c.1.center - o) - c.1.radius ^ 2

theorem circleInversionDelta_ne_zero (o : Point2) (c : ProperCircle)
    (ho : o ∉ (c.1 : Set Point2)) : circleInversionDelta o c ≠ 0 := by
  intro hδ
  apply ho
  apply EuclideanGeometry.mem_sphere'.mpr
  change dist c.1.center o = c.1.radius
  apply (sq_eq_sq₀ dist_nonneg c.2.le).mp
  rw [← directionSq_sub_eq_dist_sq]
  exact sub_eq_zero.mp hδ

noncomputable def circleInversionCenter (o : Point2) (c : ProperCircle) : Point2 :=
  o + (circleInversionDelta o c)⁻¹ • (c.1.center - o)

noncomputable def circleInversionRadius (o : Point2) (c : ProperCircle) : ℝ :=
  |c.1.radius / circleInversionDelta o c|

noncomputable def invertedProperCircle (o : Point2) (c : ProperCircle)
    (ho : o ∉ (c.1 : Set Point2)) : ProperCircle :=
  ⟨⟨circleInversionCenter o c, circleInversionRadius o c⟩,
    abs_pos.mpr (div_ne_zero c.2.ne' (circleInversionDelta_ne_zero o c ho))⟩

theorem inversion_circle_coordinate_identity
    {q₀ q₁ o₀ o₁ x₀ x₁ r δ s : ℝ}
    (hs0 : s ≠ 0) (hδ0 : δ ≠ 0)
    (hs : s = (x₀ - o₀) ^ 2 + (x₁ - o₁) ^ 2)
    (hδ : δ = (q₀ - o₀) ^ 2 + (q₁ - o₁) ^ 2 - r ^ 2)
    (hc : (q₀ - x₀) ^ 2 + (q₁ - x₁) ^ 2 = r ^ 2) :
    ((q₀ - o₀) / δ - (x₀ - o₀) / s) ^ 2 +
        ((q₁ - o₁) / δ - (x₁ - o₁) / s) ^ 2 = (r / δ) ^ 2 := by
  subst s
  subst δ
  field_simp
  rw [← hc]
  ring

set_option maxRecDepth 10000 in
theorem inversion_mem_invertedProperCircle (o x : Point2) (c : ProperCircle)
    (ho : o ∉ (c.1 : Set Point2)) (hx : x ∈ (c.1 : Set Point2)) :
    EuclideanGeometry.inversion o 1 x ∈
      ((invertedProperCircle o c ho).1 : Set Point2) := by
  have hxo : x ≠ o := by
    intro h
    apply ho
    simpa [h] using hx
  have hdist : dist x o ≠ 0 := dist_ne_zero.mpr hxo
  have hδ := circleInversionDelta_ne_zero o c ho
  have hsphere := EuclideanGeometry.mem_sphere'.mp hx
  change dist c.1.center x = c.1.radius at hsphere
  have hsphereSq := congrArg (fun t : ℝ => t ^ 2) hsphere
  dsimp at hsphereSq
  rw [dist_eq_norm, EuclideanSpace.real_norm_sq_eq] at hsphereSq
  simp [Fin.sum_univ_two] at hsphereSq
  have hdistSqCoords : dist x o ^ 2 =
      (x 0 - o 0) ^ 2 + (x 1 - o 1) ^ 2 := by
    rw [← directionSq_sub_eq_dist_sq]
    simp [directionSq]
  have hdistSq0 : dist x o ^ 2 ≠ 0 := pow_ne_zero 2 hdist
  have hdeltaCoords : circleInversionDelta o c =
      (c.1.center 0 - o 0) ^ 2 + (c.1.center 1 - o 1) ^ 2 -
        c.1.radius ^ 2 := by
    simp [circleInversionDelta, directionSq]
  have hcenterCoord (i : Fin 2) : circleInversionCenter o c i =
      o i + (c.1.center i - o i) / circleInversionDelta o c := by
    simp [circleInversionCenter]
    rw [div_eq_mul_inv, mul_comm]
  have hinversionCoord (i : Fin 2) :
      EuclideanGeometry.inversion o 1 x i =
        o i + (x i - o i) / (dist x o ^ 2) := by
    simp [EuclideanGeometry.inversion]
    ring
  have halgebra := inversion_circle_coordinate_identity
    hdistSq0 hδ hdistSqCoords hdeltaCoords hsphereSq
  apply EuclideanGeometry.mem_sphere'.mpr
  change dist (circleInversionCenter o c)
      (EuclideanGeometry.inversion o 1 x) = circleInversionRadius o c
  apply (sq_eq_sq₀ dist_nonneg (abs_nonneg _)).mp
  rw [dist_eq_norm, EuclideanSpace.real_norm_sq_eq]
  simp only [Fin.sum_univ_two]
  change
    (circleInversionCenter o c 0 -
          EuclideanGeometry.inversion o 1 x 0) ^ 2 +
        (circleInversionCenter o c 1 -
          EuclideanGeometry.inversion o 1 x 1) ^ 2 =
      |c.1.radius / circleInversionDelta o c| ^ 2
  rw [hcenterCoord 0, hcenterCoord 1, hinversionCoord 0,
    hinversionCoord 1]
  simpa [circleInversionRadius, abs_sq] using halgebra

end Erdos506.V3
