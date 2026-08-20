import Erdos506.V1.Fourteen

/-!
# The pointwise residual certificate for the fourteen-point endpoint

This module checks the finite arithmetic at the heart of the selected
seven-circle branch.  The global double-counting identities are deliberately
kept separate.  In particular the pivot term is gated by `3 ≤ g + x`, since
the tagged `BlockSystem` also contains two-point line blocks.
-/

namespace Erdos506.V1

open Erdos506.Block

/-- The contribution of a block with `g` selected-circle labels and `x`
outside labels to the global restored-centre defect row. -/
def fourteenBlockDefect (kind : BlockKind) (g x : ℕ) : ℤ :=
  let s : ℤ := (g + x : ℕ)
  match kind with
  | .circle => s * (s - 4)
  | .line => 2 * s * (s - 2)

/-- The cleared local functional from the selected seven-circle proof.
The last summand is the `W` correction. -/
def fourteenBlockFunctional (kind : BlockKind) (g x : ℕ) : ℤ :=
  6 * (Nat.choose x 3 : ℤ) +
    9 * (g : ℤ) * (Nat.choose x 2 : ℤ) +
    12 * (Nat.choose g 2 : ℤ) * (x : ℤ) +
    6 * (Nat.choose g 3 : ℤ) +
    (if 3 ≤ g + x then
      (3 * (g : ℤ) + 6 * (x : ℤ)) *
        ((4 : ℤ) - ((g + x : ℕ) : ℤ))
    else 0) -
    (if kind = .circle then 36 else 0) -
    (if kind = .circle ∧ g = 2 then
      6 * (Nat.choose x 2 : ℤ)
    else 0)

/-- Every nonselected line block satisfying the fourteen-point cap has
nonnegative residual, even after allowing the uniform outsider-triple
correction used for circles. -/
theorem fourteen_line_residual_bound (g x : ℕ)
    (hg : g ≤ 2) (hmin : 3 ≤ g + x) (hcap : g + x ≤ 6) :
    fourteenBlockFunctional .line g x ≤
      4 * fourteenBlockDefect .line g x +
        3 * (Nat.choose x 3 : ℤ) := by
  have hx : x ≤ 6 := by omega
  interval_cases g <;> interval_cases x <;>
    simp [fourteenBlockFunctional, fourteenBlockDefect, Nat.choose] at *

/-- Every nonselected circle block satisfying the fourteen-point cap has
residual bounded below by minus three times its outsider triples.  This
single correction covers the two negative cells `(g,x)=(1,6),(2,5)`. -/
theorem fourteen_circle_residual_bound (g x : ℕ)
    (hg : g ≤ 2) (hmin : 3 ≤ g + x) (hcap : g + x ≤ 7) :
    fourteenBlockFunctional .circle g x ≤
      4 * fourteenBlockDefect .circle g x +
        3 * (Nat.choose x 3 : ℤ) := by
  have hx : x ≤ 7 := by omega
  interval_cases g <;> interval_cases x <;>
    simp [fourteenBlockFunctional, fourteenBlockDefect, Nat.choose] at *

/-- The distinguished seven-circle is the unique exceptional local cell:
its functional exceeds four times its defect contribution by exactly 27. -/
theorem fourteen_selected_circle_residual :
    fourteenBlockFunctional .circle 7 0 =
      4 * fourteenBlockDefect .circle 7 0 + 27 := by
  norm_num [fourteenBlockFunctional, fourteenBlockDefect, Nat.choose]

/-- The final lower half of the numerical contradiction. -/
theorem fourteen_weight_ge_sixty_nine_of_residual
    (W : ℕ) (hresidual : (1104 : ℤ) - 6 * (W : ℤ) ≤ 692) :
    69 ≤ W := by
  omega

/-- The two numerical sides of the selected-circle certificate are
incompatible. -/
theorem fourteen_weight_contradiction
    (W : ℕ) (hlower : 69 ≤ W) (hupper : W ≤ 63) : False := by
  omega

end Erdos506.V1
