import Mathlib.Tactic

/-!
# Arithmetic spine of the V4 richest-line argument

The geometric proof writes `m` for the number of points on a richest line
and `k` for the number off that line.  The two visibly disjoint triple
families have lower count

`k * choose(m, 2) + choose(k, 2) * (m - 1)`.

This file formalizes the factorization behind the comparison with
`choose(m + k - 1, 2)`.  It is only the arithmetic spine; the finite-set
injections producing those two families are formalized separately.
-/

namespace Erdos506.V4

/-- The exact polynomial gap in the richest-line lower bound. -/
theorem richestLineFactorization (m k : ℚ) :
    k * (m * (m - 1) / 2) + (k * (k - 1) / 2) * (m - 1) -
        ((m + k - 1) * (m + k - 2) / 2) =
      (m + k - 1) * (k - 1) * (m - 2) / 2 := by
  ring

/-- For `m ≥ 2` and `k ≥ 1`, the two richest-line triple families meet the
V4 target. -/
theorem richestLineArithmetic (m k : ℚ) (hm : 2 ≤ m) (hk : 1 ≤ k) :
    (m + k - 1) * (m + k - 2) / 2 ≤
      k * (m * (m - 1) / 2) + (k * (k - 1) / 2) * (m - 1) := by
  rw [← sub_nonneg, richestLineFactorization]
  have hmk : 0 ≤ m + k - 1 := by linarith
  have hk1 : 0 ≤ k - 1 := by linarith
  have hm2 : 0 ≤ m - 2 := by linarith
  positivity

end Erdos506.V4
