import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic

/-!
# Frozen numerical targets for Erdős #506

This file records only the numerical right-hand sides of the three frozen
variants.  It is deliberately not presented as a formalization of their
geometric lower bounds.  Those theorems enter only after their hypotheses and
incidence interfaces have been formalized.
-/

namespace Erdos506

/-- The Elliott-convention value in the uniform range `n ≥ 9`. -/
def v1UniformTarget (n : ℕ) : ℕ :=
  1 + Nat.choose (n - 1) 2 - (n - 1) / 2

/-- The non-exceptional V3 value. -/
def v3GenericTarget (n : ℕ) : ℕ :=
  1 + Nat.choose (n - 1) 2

/-- The V4 value. -/
def v4Target (n : ℕ) : ℕ :=
  Nat.choose (n - 1) 2

/-- The total frozen V3 target.  Values below the theorem domain are
irrelevant; the exceptional value is at `n = 8`. -/
def v3Target (n : ℕ) : ℕ :=
  if n = 8 then 20 else v3GenericTarget n

/-- The total frozen V1 target.  The corrected small value at `n = 6` and the
stated values at `n = 7, 8` are exceptional; from `n = 9` onward the uniform
formula applies. -/
def v1Target (n : ℕ) : ℕ :=
  if n = 6 then 8
  else if n = 7 then 11
  else if n = 8 then 17
  else v1UniformTarget n

@[simp] theorem v3Target_at_eight : v3Target 8 = 20 := by
  norm_num [v3Target]

theorem v3Target_eq_generic {n : ℕ} (hn : n ≠ 8) :
    v3Target n = v3GenericTarget n := by
  simp [v3Target, hn]

theorem v3Target_small_values :
    [v3Target 4, v3Target 5, v3Target 6, v3Target 7,
      v3Target 8, v3Target 9, v3Target 10] =
      [4, 7, 11, 16, 20, 29, 37] := by
  norm_num [v3Target, v3GenericTarget, Nat.choose]

theorem v1Target_small_values :
    [v1Target 4, v1Target 5, v1Target 6, v1Target 7, v1Target 8] =
      [3, 5, 8, 11, 17] := by
  norm_num [v1Target, v1UniformTarget, Nat.choose]

theorem v1Target_eq_uniform {n : ℕ} (hn : 9 ≤ n) :
    v1Target n = v1UniformTarget n := by
  have h6 : n ≠ 6 := by omega
  have h7 : n ≠ 7 := by omega
  have h8 : n ≠ 8 := by omega
  simp [v1Target, h6, h7, h8]

/-- The V1 target never exceeds the V3 target. -/
theorem v1Target_le_v3Target (n : ℕ) :
    v1Target n ≤ v3Target n := by
  by_cases h6 : n = 6
  · subst n
    norm_num [v1Target, v3Target, v3GenericTarget, Nat.choose]
  by_cases h7 : n = 7
  · subst n
    norm_num [v1Target, v3Target, v3GenericTarget, Nat.choose]
  by_cases h8 : n = 8
  · subst n
    norm_num [v1Target, v3Target]
  rw [v1Target, if_neg h6, if_neg h7, if_neg h8, v3Target, if_neg h8]
  exact Nat.sub_le _ _

/-- On the theorem domain, the V1 target never exceeds the V4 target. -/
theorem v1Target_le_v4Target {n : ℕ} (hn : 4 ≤ n) :
    v1Target n ≤ v4Target n := by
  by_cases h6 : n = 6
  · subst n
    norm_num [v1Target, v4Target, Nat.choose]
  by_cases h7 : n = 7
  · subst n
    norm_num [v1Target, v4Target, Nat.choose]
  by_cases h8 : n = 8
  · subst n
    norm_num [v1Target, v4Target, Nat.choose]
  rw [v1Target, if_neg h6, if_neg h7, if_neg h8, v1UniformTarget, v4Target]
  have hhalf : 1 ≤ (n - 1) / 2 := by omega
  omega

end Erdos506
