import Mathlib.Tactic

/-!
# The ten-point local parity table

This file isolates the integer calculation in the manuscript's ten-point
local-parity lemma.  It does not assert that an arbitrary configuration
supplies the hypotheses: the geometric wrapper must still prove the local
pair row, the two possible values `d3 = 6, 9`, Melchior nonnegativity and the
even-arrangement exclusion `kappa != 1`.

The table is nevertheless complete.  `r` is the five-block degree, `q` the
four-line degree, `l3` the three-line degree and `l5` the five-line degree.
-/

namespace Erdos506.V1

/-- The cleared restored-centre slack used by the local table. -/
def tenLocalKappa (d3 r l3 q l5 : Nat) : Int :=
  (d3 : Int) + 6 - (r : Int) - 3 * (l3 : Int) -
    4 * (q : Int) - 5 * (l5 : Int)

/-- Whether a cell of the `l5 = 0` local table is possible. -/
def tenLocalStateAllowed : Nat → Nat → Nat → Prop
  | 6, 0, 0 => True
  | 6, 0, 1 => True
  | 6, 0, 2 => True
  | 6, 0, 3 => True
  | 6, 1, 0 => True
  | 6, 1, 1 => True
  | 6, 1, 2 => True
  | 6, 1, 3 => True
  | 6, 2, 0 => True
  | 6, 2, 1 => True
  | 6, 2, 2 => True
  | 6, 2, 3 => False
  | 6, 3, 0 => True
  | 6, 3, 1 => False
  | 6, 3, 2 => False
  | 6, 3, 3 => False
  | 9, 0, 0 => True
  | 9, 0, 1 => True
  | 9, 0, 2 => True
  | 9, 0, 3 => True
  | 9, 1, 0 => True
  | 9, 1, 1 => True
  | 9, 1, 2 => True
  | 9, 1, 3 => True
  | 9, 2, 0 => True
  | 9, 2, 1 => True
  | 9, 2, 2 => True
  | 9, 2, 3 => True
  | 9, 3, 0 => True
  | 9, 3, 1 => True
  | 9, 3, 2 => False
  | 9, 3, 3 => True
  | _, _, _ => False

/-- The maximum three-line degree in each possible `l5 = 0` cell.

Arguments are ordered as `(d3, q, r)`, matching the rows and columns of the
printed table.  Values in impossible cells are irrelevant and set to zero. -/
def tenLocalLine3Cap : Nat → Nat → Nat → Nat
  | 6, 0, 0 => 4
  | 6, 0, 1 => 3
  | 6, 0, 2 => 2
  | 6, 0, 3 => 3
  | 6, 1, 0 => 2
  | 6, 1, 1 => 1
  | 6, 1, 2 => 2
  | 6, 1, 3 => 1
  | 6, 2, 0 => 0
  | 6, 2, 1 => 1
  | 6, 2, 2 => 0
  | 6, 2, 3 => 0
  | 6, 3, 0 => 0
  | 6, 3, 1 => 0
  | 6, 3, 2 => 0
  | 6, 3, 3 => 0
  | 9, 0, 0 => 4
  | 9, 0, 1 => 4
  | 9, 0, 2 => 3
  | 9, 0, 3 => 4
  | 9, 1, 0 => 3
  | 9, 1, 1 => 2
  | 9, 1, 2 => 3
  | 9, 1, 3 => 2
  | 9, 2, 0 => 1
  | 9, 2, 1 => 2
  | 9, 2, 2 => 1
  | 9, 2, 3 => 0
  | 9, 3, 0 => 1
  | 9, 3, 1 => 0
  | 9, 3, 2 => 0
  | 9, 3, 3 => 0
  | _, _, _ => 0

/-- The pair row, Kelly lower bound and the deletion upper bound leave only
the two local three-block degrees `6` and `9`. -/
theorem ten_local_pair_d3_eq_six_or_nine
    {d3 d4 d5 : Nat}
    (hpairs : d3 + 3 * d4 + 6 * d5 = 36)
    (hKelly : 27 <= 7 * d3) (hupper : d3 <= 11) :
    d3 = 6 ∨ d3 = 9 := by
  omega

/-- Exact `l5 = 0` table, including all dash/impossible cells. -/
theorem ten_local_line3_table
    {d3 r q l3 : Nat}
    (hd3 : d3 = 6 ∨ d3 = 9) (hr : r <= 3) (hq : q <= 3)
    (hl3 : l3 <= 4)
    (hkappa : 0 <= tenLocalKappa d3 r l3 q 0)
    (hkappaNe : tenLocalKappa d3 r l3 q 0 ≠ 1) :
    tenLocalStateAllowed d3 q r ∧ l3 <= tenLocalLine3Cap d3 q r := by
  rcases hd3 with rfl | rfl
  · interval_cases q <;> interval_cases r <;>
      simp [tenLocalStateAllowed, tenLocalLine3Cap, tenLocalKappa] at * <;>
      omega
  · interval_cases q <;> interval_cases r <;>
      simp [tenLocalStateAllowed, tenLocalLine3Cap, tenLocalKappa] at * <;>
      omega

/-- A five-line lowers the `q = 0` table capacity by at least one.  Any
additional four-lines only strengthen the inequality. -/
theorem ten_local_five_line_loses_one
    {d3 r q l3 l5 : Nat}
    (hd3 : d3 = 6 ∨ d3 = 9) (hr : r <= 3) (hl5 : 1 <= l5)
    (hkappa : 0 <= tenLocalKappa d3 r l3 q l5)
    (hkappaNe : tenLocalKappa d3 r l3 q l5 ≠ 1) :
    l3 + 1 <= tenLocalLine3Cap d3 0 r := by
  rcases hd3 with rfl | rfl
  · interval_cases r <;>
      simp [tenLocalLine3Cap, tenLocalKappa] at * <;> omega
  · interval_cases r <;>
      simp [tenLocalLine3Cap, tenLocalKappa] at * <;> omega

end Erdos506.V1
