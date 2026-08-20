import Erdos506.V3.SmallPacking

/-!
# The characteristic-zero Fano obstruction

This is the algebraic core of the seven-point wall.  After choosing the
non-line `1,2,4` as a basis, the Fano incidences give the four displayed
relations.  The first three force `bcf = ade`, whereas the last one forces
`bcf = -ade`; this is impossible over the reals when the relevant
coordinates are nonzero.
-/

namespace Erdos506.V3

/-- Coordinate contradiction for the standard Fano lines
`167, 257, 347, 356` after normalising `1,2,4` to the coordinate basis.

The remaining lines `123, 145, 246` are what put points `3,5,6` into the
coordinate planes and give the coefficients occurring here. -/
theorem fano_coordinate_contradiction
    {a b c d e f X Y Z : ℝ}
    (ha : a ≠ 0) (hd : d ≠ 0) (he : e ≠ 0) (hZ : Z ≠ 0)
    (h167 : e * Z = f * Y)
    (h257 : d * X = c * Z)
    (h347 : b * X = a * Y)
    (h356 : -a * e * d - b * c * f = 0) : False := by
  have hscaled : (b * c * f) * Z = (a * d * e) * Z := by
    calc
      (b * c * f) * Z = b * f * (c * Z) := by ring
      _ = b * f * (d * X) := by rw [h257]
      _ = d * f * (b * X) := by ring
      _ = d * f * (a * Y) := by rw [h347]
      _ = a * d * (f * Y) := by ring
      _ = a * d * (e * Z) := by rw [h167]
      _ = (a * d * e) * Z := by ring
  have hcoeff : b * c * f = a * d * e :=
    mul_right_cancel₀ hZ hscaled
  have hlast := h356
  rw [hcoeff] at hlast
  have hzero : a * d * e = 0 := by
    nlinarith
  exact (mul_ne_zero (mul_ne_zero ha hd) he) hzero

end Erdos506.V3
