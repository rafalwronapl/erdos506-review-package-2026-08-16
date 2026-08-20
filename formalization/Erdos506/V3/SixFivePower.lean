import Erdos506.V3.FiveCircle

/-!
# Algebraic core of the six-five-circle obstruction

These are exactly the six power-of-a-point equations in the paper.  The
proof is division-free: three cancellation steps produce the reciprocal
relations, after which the fourth power equation equates a nonzero quantity
with its negative.
-/

namespace Erdos506.V3

theorem six_five_power_equations_contradiction
    {a2 b2 c2 x y u v w z : ℝ}
    (ha2 : a2 ≠ 0) (hb2 : b2 ≠ 0) (hc2 : c2 ≠ 0)
    (hv : v ≠ 0) (hz : z ≠ 0)
    (hu1 : u ≠ 1) (hv1 : v ≠ 1) (hw1 : w ≠ 1)
    (h1 : c2 * (1 - x) = a2 * w * z)
    (h2 : b2 * (1 - u) = a2 * (1 - w) * (1 - z))
    (h3 : c2 * y = b2 * u * v)
    (h4 : a2 * (1 - w) = b2 * (1 - u) * (1 - v))
    (h5 : c2 * x * y = b2 * v)
    (h6 : c2 * (1 - x) * (1 - y) = a2 * z) : False := by
  have hxuScaled : b2 * v = (b2 * v) * (x * u) := by
    calc
      b2 * v = c2 * x * y := h5.symm
      _ = x * (c2 * y) := by ring
      _ = x * (b2 * u * v) := by rw [h3]
      _ = (b2 * v) * (x * u) := by ring
  have hxu : x * u = 1 := by
    apply mul_left_cancel₀ (mul_ne_zero hb2 hv)
    simpa using hxuScaled.symm
  have hywScaled : a2 * z = (a2 * z) * (w * (1 - y)) := by
    calc
      a2 * z = c2 * (1 - x) * (1 - y) := h6.symm
      _ = (c2 * (1 - x)) * (1 - y) := by ring
      _ = (a2 * w * z) * (1 - y) := by rw [h1]
      _ = (a2 * z) * (w * (1 - y)) := by ring
  have hyw : w * (1 - y) = 1 := by
    apply mul_left_cancel₀ (mul_ne_zero ha2 hz)
    simpa using hywScaled.symm
  have hzvScaled : b2 * (1 - u) =
      (b2 * (1 - u)) * ((1 - v) * (1 - z)) := by
    calc
      b2 * (1 - u) = a2 * (1 - w) * (1 - z) := h2
      _ = (a2 * (1 - w)) * (1 - z) := by ring
      _ = (b2 * (1 - u) * (1 - v)) * (1 - z) := by rw [h4]
      _ = (b2 * (1 - u)) * ((1 - v) * (1 - z)) := by ring
  have hzv : (1 - v) * (1 - z) = 1 := by
    apply mul_left_cancel₀ (mul_ne_zero hb2 (sub_ne_zero.mpr hu1.symm))
    simpa using hzvScaled.symm
  have hwy : w * y = w - 1 := by
    nlinarith [hyw]
  have huz : u * (1 - x) = u - 1 := by
    nlinarith [hxu]
  have hzrel : z * (1 - v) = -v := by
    nlinarith [hzv]
  have hR : c2 * (w - 1) = b2 * u * v * w := by
    calc
      c2 * (w - 1) = c2 * (w * y) := by rw [hwy]
      _ = w * (c2 * y) := by ring
      _ = w * (b2 * u * v) := by rw [h3]
      _ = b2 * u * v * w := by ring
  have hSneg : c2 * (u - 1) * (1 - v) = -a2 * u * w * v := by
    calc
      c2 * (u - 1) * (1 - v) =
          c2 * (u * (1 - x)) * (1 - v) := by rw [huz]
      _ = u * (1 - v) * (c2 * (1 - x)) := by ring
      _ = u * (1 - v) * (a2 * w * z) := by rw [h1]
      _ = a2 * u * w * (z * (1 - v)) := by ring
      _ = -a2 * u * w * v := by rw [hzrel]; ring
  have hS : c2 * (u - 1) * (v - 1) = a2 * u * w * v := by
    calc
      c2 * (u - 1) * (v - 1) =
          -(c2 * (u - 1) * (1 - v)) := by ring
      _ = -(-a2 * u * w * v) := by rw [hSneg]
      _ = a2 * u * w * v := by ring
  have hfinal :
      c2 * (u - 1) * (v - 1) * (1 - w) =
        c2 * (w - 1) * (1 - u) * (1 - v) := by
    calc
      c2 * (u - 1) * (v - 1) * (1 - w) =
          (a2 * u * w * v) * (1 - w) := by rw [hS]
      _ = (a2 * (1 - w)) * (u * w * v) := by ring
      _ = (b2 * (1 - u) * (1 - v)) * (u * w * v) := by rw [h4]
      _ = (b2 * u * v * w) * (1 - u) * (1 - v) := by ring
      _ = c2 * (w - 1) * (1 - u) * (1 - v) := by rw [hR]
  have hzero : c2 * (u - 1) * (v - 1) * (w - 1) = 0 := by
    nlinarith [hfinal]
  exact (mul_ne_zero
    (mul_ne_zero (mul_ne_zero hc2 (sub_ne_zero.mpr hu1))
      (sub_ne_zero.mpr hv1)) (sub_ne_zero.mpr hw1)) hzero

end Erdos506.V3
