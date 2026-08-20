import Erdos506.V3.DirectedPower

/-!
# Menelaus versus three directed-power equations

These elementary lemmas isolate the algebraic contradiction used for the
seven-point Fano wall after inversion.  Three side points of a triangle are
collinear, so their directed parameters satisfy Menelaus with a minus sign.
Three cyclic quadrilaterals force the same product with a plus sign.
-/

namespace Erdos506.V3

open Erdos506.V4

def det2 (v w : Point2) : ℝ := v 0 * w 1 - v 1 * w 0

theorem exists_affineParamPoint_of_det2_eq_zero
    {A B C : Point2} (hAB : A ≠ B)
    (hdet : det2 (B - A) (C - A) = 0) :
    ∃ t : ℝ, affineParamPoint A (B - A) t = C := by
  let v : Point2 := B - A
  let z : Point2 := C - A
  by_cases hv0 : v 0 = 0
  · have hv1 : v 1 ≠ 0 := by
      intro hv1
      apply hAB
      ext i
      fin_cases i
      · exact (sub_eq_zero.mp (by simpa [v] using hv0)).symm
      · exact (sub_eq_zero.mp (by simpa [v] using hv1)).symm
    have hz0 : z 0 = 0 := by
      change v 0 * z 1 - v 1 * z 0 = 0 at hdet
      rw [hv0, zero_mul, zero_sub] at hdet
      have hprod : v 1 * z 0 = 0 := neg_eq_zero.mp hdet
      exact (mul_eq_zero.mp hprod).resolve_left hv1
    refine ⟨z 1 / v 1, ?_⟩
    ext i
    fin_cases i
    · change A 0 + (z 1 / v 1) * v 0 = C 0
      rw [hv0, mul_zero, add_zero]
      change C 0 - A 0 = 0 at hz0
      linarith
    · change A 1 + (z 1 / v 1) * v 1 = C 1
      have hcancel : z 1 / v 1 * v 1 = z 1 := div_mul_cancel₀ _ hv1
      rw [hcancel]
      dsimp [z]
      ring
  · have hvrel : z 0 * v 1 = z 1 * v 0 := by
      change v 0 * z 1 - v 1 * z 0 = 0 at hdet
      nlinarith
    have hz1 : (z 0 / v 0) * v 1 = z 1 := by
      calc
        (z 0 / v 0) * v 1 = (z 0 * v 1) / v 0 := by ring
        _ = (z 1 * v 0) / v 0 := by rw [hvrel]
        _ = z 1 := by field_simp
    refine ⟨z 0 / v 0, ?_⟩
    ext i
    fin_cases i
    · change A 0 + (z 0 / v 0) * v 0 = C 0
      have hcancel : z 0 / v 0 * v 0 = z 0 := div_mul_cancel₀ _ hv0
      rw [hcancel]
      dsimp [z]
      ring
    · change A 1 + (z 0 / v 0) * v 1 = C 1
      rw [hz1]
      dsimp [z]
      ring

theorem menelaus_parameter_equation
    {A B C X U W : Point2} {x u w t : ℝ}
    (hdet : det2 (B - A) (C - A) ≠ 0)
    (hx : affineParamPoint A (B - A) x = X)
    (hu : affineParamPoint A (C - A) u = U)
    (hw : affineParamPoint B (C - B) w = W)
    (hcol : affineParamPoint X (U - X) t = W) :
    u * (1 - x) * (1 - w) + x * w * (1 - u) = 0 := by
  rw [← hx, ← hu, ← hw] at hcol
  let a : ℝ := (1 - w) - x * (1 - t)
  let b : ℝ := w - t * u
  have hcoord (i : Fin 2) :
      a * (B - A) i + b * (C - A) i = 0 := by
    have hi := congrArg (fun q : Point2 => q i) hcol
    simp [affineParamPoint] at hi
    dsimp [a, b]
    nlinarith
  have haDet : a * det2 (B - A) (C - A) = 0 := by
    calc
      a * det2 (B - A) (C - A) =
          (C - A) 1 * (a * (B - A) 0 + b * (C - A) 0) -
            (C - A) 0 * (a * (B - A) 1 + b * (C - A) 1) := by
              simp [det2]
              ring
      _ = 0 := by rw [hcoord 0, hcoord 1]; ring
  have hbDet : b * det2 (B - A) (C - A) = 0 := by
    calc
      b * det2 (B - A) (C - A) =
          (B - A) 0 * (a * (B - A) 1 + b * (C - A) 1) -
            (B - A) 1 * (a * (B - A) 0 + b * (C - A) 0) := by
              simp [det2]
              ring
      _ = 0 := by rw [hcoord 0, hcoord 1]; ring
  have ha : a = 0 := (mul_eq_zero.mp haDet).resolve_right hdet
  have hb : b = 0 := (mul_eq_zero.mp hbDet).resolve_right hdet
  have hsum : x * (1 - t) + t * u = 1 := by
    dsimp [a, b] at ha hb
    linarith
  have hw₁ : 1 - w = x * (1 - t) := by
    dsimp [a] at ha
    linarith
  have hw₂ : w = t * u := by
    dsimp [b] at hb
    linarith
  rw [hw₁, hw₂]
  calc
    u * (1 - x) * (x * (1 - t)) + x * (t * u) * (1 - u) =
        x * u * (1 - (x * (1 - t) + t * u)) := by ring
    _ = 0 := by rw [hsum]; ring

theorem no_menelaus_three_power_pattern
    {a2 b2 c2 x u w : ℝ}
    (ha2 : a2 ≠ 0) (hc2 : c2 ≠ 0)
    (hu0 : u ≠ 0) (hx1 : x ≠ 1) (hw1 : w ≠ 1)
    (hmen : u * (1 - x) * (1 - w) + x * w * (1 - u) = 0)
    (h₁ : c2 * x = b2 * u)
    (h₂ : c2 * (1 - x) = a2 * w)
    (h₃ : b2 * (1 - u) = a2 * (1 - w)) : False := by
  let L : ℝ := u * (1 - x) * (1 - w)
  let R : ℝ := x * w * (1 - u)
  have hscaled : (c2 * a2) * L = (c2 * a2) * R := by
    calc
      (c2 * a2) * L =
          u * (c2 * (1 - x)) * (a2 * (1 - w)) := by
            simp [L]
            ring
      _ = u * (a2 * w) * (b2 * (1 - u)) := by rw [h₂, h₃]
      _ = (b2 * u) * (a2 * w) * (1 - u) := by ring
      _ = (c2 * x) * (a2 * w) * (1 - u) := by rw [h₁]
      _ = (c2 * a2) * R := by simp [R]; ring
  have hLR : L = R := mul_left_cancel₀ (mul_ne_zero hc2 ha2) hscaled
  have hLzero : L = 0 := by
    dsimp [L, R] at hLR
    dsimp [L]
    nlinarith
  have hLne : L ≠ 0 := by
    dsimp [L]
    exact mul_ne_zero (mul_ne_zero hu0 (sub_ne_zero.mpr hx1.symm))
      (sub_ne_zero.mpr hw1.symm)
  exact hLne hLzero

end Erdos506.V3
