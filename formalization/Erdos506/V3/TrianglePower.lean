import Erdos506.V3.DirectedPower
import Erdos506.V3.SixFivePower

/-!
# The geometric six-five-circle obstruction in a triangle

After inversion at the point labelled `123`, the six-block design forced by
equality in the five-circle packing bound has three sides and three remaining
proper circles.  This file turns that geometric picture into the six directed
power equations and proves it impossible over `ℝ`.
-/

namespace Erdos506.V3

open Erdos506.V4

/-- The exact post-inversion triangle pattern forced by six five-point
circles cannot occur over the real plane. -/
theorem no_six_five_triangle_pattern
    (A B C : Point2) (hAB : A ≠ B) (hAC : A ≠ C) (hBC : B ≠ C)
    {x y u v w z : ℝ}
    (hxy : DistinctSideParameters x y)
    (huv : DistinctSideParameters u v)
    (hwz : DistinctSideParameters w z)
    (Γ₄ Γ₅ Γ₆ : ProperCircle)
    (h4A : A ∈ (Γ₄.1 : Set Point2))
    (h4X : affineParamPoint A (B - A) x ∈ (Γ₄.1 : Set Point2))
    (h4U : affineParamPoint A (C - A) u ∈ (Γ₄.1 : Set Point2))
    (h4W : affineParamPoint B (C - B) w ∈ (Γ₄.1 : Set Point2))
    (h4Z : affineParamPoint B (C - B) z ∈ (Γ₄.1 : Set Point2))
    (h5B : B ∈ (Γ₅.1 : Set Point2))
    (h5Y : affineParamPoint A (B - A) y ∈ (Γ₅.1 : Set Point2))
    (h5U : affineParamPoint A (C - A) u ∈ (Γ₅.1 : Set Point2))
    (h5V : affineParamPoint A (C - A) v ∈ (Γ₅.1 : Set Point2))
    (h5W : affineParamPoint B (C - B) w ∈ (Γ₅.1 : Set Point2))
    (h6C : C ∈ (Γ₆.1 : Set Point2))
    (h6X : affineParamPoint A (B - A) x ∈ (Γ₆.1 : Set Point2))
    (h6Y : affineParamPoint A (B - A) y ∈ (Γ₆.1 : Set Point2))
    (h6V : affineParamPoint A (C - A) v ∈ (Γ₆.1 : Set Point2))
    (h6Z : affineParamPoint B (C - B) z ∈ (Γ₆.1 : Set Point2)) : False := by
  rcases hxy with ⟨hx0, hx1, hy0, hy1, hxy⟩
  rcases huv with ⟨hu0, hu1, hv0, hv1, huv⟩
  rcases hwz with ⟨hw0, hw1, hz0, hz1, hwz⟩
  let a2 := directionSq (C - B)
  let b2 := directionSq (C - A)
  let c2 := directionSq (B - A)
  have ha2 : a2 ≠ 0 := directionSq_sub_ne_zero hBC.symm
  have hb2 : b2 ≠ 0 := directionSq_sub_ne_zero hAC.symm
  have hc2 : c2 ≠ 0 := directionSq_sub_ne_zero hAB.symm
  have h1 : c2 * (1 - x) = a2 * w * z := by
    have hp := directed_power_of_four_cocircular_points Γ₄ B (A - B) (C - B)
      (show (1 : ℝ) ≠ 1 - x by
        intro h
        apply hx0
        linarith)
      hwz
      (by simpa using h4A)
      (by simpa [affineParamPoint_reverse] using h4X)
      h4W h4Z
    simpa [a2, c2, directionSq_sub_comm] using hp
  have h2 : b2 * (1 - u) = a2 * (1 - w) * (1 - z) := by
    have hp := directed_power_of_four_cocircular_points Γ₄ C (A - C) (B - C)
      (show (1 : ℝ) ≠ 1 - u by
        intro h
        apply hu0
        linarith)
      (show (1 - w : ℝ) ≠ 1 - z by
        intro h
        apply hwz
        linarith)
      (by simpa using h4A)
      (by simpa [affineParamPoint_reverse] using h4U)
      (by simpa [affineParamPoint_reverse] using h4W)
      (by simpa [affineParamPoint_reverse] using h4Z)
    simpa [a2, b2, directionSq_sub_comm] using hp
  have h3 : c2 * y = b2 * u * v := by
    have hp := directed_power_of_four_cocircular_points Γ₅ A (B - A) (C - A)
      (show (1 : ℝ) ≠ y by exact hy1.symm)
      huv
      (by simpa using h5B)
      h5Y h5U h5V
    simpa [b2, c2] using hp
  have h4 : a2 * (1 - w) = b2 * (1 - u) * (1 - v) := by
    have hp := directed_power_of_four_cocircular_points Γ₅ C (B - C) (A - C)
      (show (1 : ℝ) ≠ 1 - w by
        intro h
        apply hw0
        linarith)
      (show (1 - u : ℝ) ≠ 1 - v by
        intro h
        apply huv
        linarith)
      (by simpa using h5B)
      (by simpa [affineParamPoint_reverse] using h5W)
      (by simpa [affineParamPoint_reverse] using h5U)
      (by simpa [affineParamPoint_reverse] using h5V)
    simpa [a2, b2, directionSq_sub_comm] using hp
  have h5 : c2 * x * y = b2 * v := by
    have hp := directed_power_of_four_cocircular_points Γ₆ A (B - A) (C - A)
      hxy
      (show (1 : ℝ) ≠ v by exact hv1.symm)
      h6X h6Y
      (by simpa using h6C)
      h6V
    simpa [b2, c2] using hp
  have h6 : c2 * (1 - x) * (1 - y) = a2 * z := by
    have hp := directed_power_of_four_cocircular_points Γ₆ B (A - B) (C - B)
      (show (1 - x : ℝ) ≠ 1 - y by
        intro h
        apply hxy
        linarith)
      (show (1 : ℝ) ≠ z by exact hz1.symm)
      (by simpa [affineParamPoint_reverse] using h6X)
      (by simpa [affineParamPoint_reverse] using h6Y)
      (by simpa using h6C)
      h6Z
    simpa [a2, c2, directionSq_sub_comm] using hp
  exact six_five_power_equations_contradiction ha2 hb2 hc2 hv0 hz0
    hu1 hv1 hw1 h1 h2 h3 h4 h5 h6

end Erdos506.V3
