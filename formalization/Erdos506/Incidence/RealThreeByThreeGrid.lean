import Erdos506.Incidence.ProjectiveCoordinates

/-!
# The direction kernel of the normalized real `3 x 3` grid

The equality case of the twelve-point grid argument is projectively sent to
the affine grid `{-1,0,1}^2`.  Its twelve ordinary secants have the six
slopes listed below, with the two signs of the constant term for each slope:

`x ± y = ±1`, `x ± 2y = ±1`, and `2x ± y = ±1`.

This module formalizes the finite direction part of that calculation.  In
particular, no direction at infinity can carry three of the twelve ordinary
secants.  It is intentionally independent of the as-yet-unformalized
projective normalization and grid entrance.
-/

namespace Erdos506.Incidence

/-- The six affine slopes of the ordinary secants in the normalized grid.
The first four are the slopes of `x ± y` and `x ± 2y`; the last two are
those of `2x ± y`. -/
noncomputable def realThreeByThreeGridSecantSlope : Fin 6 → ℝ :=
  ![-1, 1, -(1 / 2 : ℝ), 1 / 2, -2, 2]

/-- The six slope codes are genuinely distinct. -/
theorem realThreeByThreeGridSecantSlope_injective :
    Function.Injective realThreeByThreeGridSecantSlope := by
  intro i j hij
  fin_cases i <;> fin_cases j
  all_goals first | rfl | norm_num [realThreeByThreeGridSecantSlope] at hij

/-- A normalized ordinary grid secant is determined by one of the six
directions and one of the two possible constant signs. -/
abbrev RealThreeByThreeGridSecant := Fin 6 × Bool

/-- Forget the sign and retain the projective direction of a grid secant. -/
noncomputable def RealThreeByThreeGridSecant.direction
    (s : RealThreeByThreeGridSecant) : ℝ :=
  realThreeByThreeGridSecantSlope s.1

/-- Two normalized ordinary grid secants have the same direction exactly
when they come from the same one of the six direction families. -/
theorem RealThreeByThreeGridSecant.direction_eq_iff
    (s t : RealThreeByThreeGridSecant) :
    s.direction = t.direction ↔ s.1 = t.1 := by
  constructor
  · intro h
    exact realThreeByThreeGridSecantSlope_injective h
  · intro h
    simp [RealThreeByThreeGridSecant.direction, h]

/-- Each direction in the normalized `3 x 3` grid occurs on at most two
ordinary secants.  This is the ideal-point half of the grid lemma: a third
ordinary secant of the same direction would have to repeat one of the two
sign choices. -/
theorem RealThreeByThreeGridSecant.no_three_distinct_same_direction
    (a b c : RealThreeByThreeGridSecant)
    (hab : a.direction = b.direction)
    (hac : a.direction = c.direction) :
    a = b ∨ a = c ∨ b = c := by
  rcases a with ⟨i, a⟩
  rcases b with ⟨j, b⟩
  rcases c with ⟨k, c⟩
  have hij : i = j :=
    realThreeByThreeGridSecantSlope_injective hab
  have hik : i = k :=
    realThreeByThreeGridSecantSlope_injective hac
  subst j
  subst k
  cases a <;> cases b <;> cases c <;> simp

/-- The affine equation of one of the twelve ordinary secants.  The first
component chooses one of the six directions and the Boolean chooses the sign
of the constant term. -/
def RealThreeByThreeGridSecant.incident
    (s : RealThreeByThreeGridSecant) (x y : ℝ) : Prop :=
  match s.1 with
  | 0 => x + y = if s.2 then 1 else -1
  | 1 => x - y = if s.2 then 1 else -1
  | 2 => x + 2 * y = if s.2 then 1 else -1
  | 3 => x - 2 * y = if s.2 then 1 else -1
  | 4 => 2 * x + y = if s.2 then 1 else -1
  | 5 => 2 * x - y = if s.2 then 1 else -1

/-- An affine point outside the normalized `3 x 3` grid. -/
def RealThreeByThreeGridExternal (x y : ℝ) : Prop :=
  (x ≠ -1 ∧ x ≠ 0 ∧ x ≠ 1) ∨
    (y ≠ -1 ∧ y ≠ 0 ∧ y ≠ 1)

/-- The direct affine calculation for three ordered directions.  The finite
case split is only over the twenty choices of three directions and their
eight constant-sign choices; every surviving system is solved by linear
arithmetic. -/
private theorem realThreeByThreeGrid_external_not_three_ordered
    (a b c : RealThreeByThreeGridSecant) (x y : ℝ)
    (horder : a.1.val < b.1.val ∧ b.1.val < c.1.val)
    (ha : a.incident x y) (hb : b.incident x y)
    (hc : c.incident x y) :
    ¬ RealThreeByThreeGridExternal x y := by
  set_option maxRecDepth 100000 in
    rintro (⟨hxm, hxz, hxp⟩ | ⟨hym, hyz, hyp⟩)
    · rcases a with ⟨a, sa⟩
      rcases b with ⟨b, sb⟩
      rcases c with ⟨c, sc⟩
      fin_cases a <;> fin_cases b <;> fin_cases c
      all_goals norm_num at horder
      all_goals cases sa <;> cases sb <;> cases sc
      all_goals
        norm_num [RealThreeByThreeGridSecant.incident] at ha hb hc <;>
          first
          | linarith
          | exact hxm (by linarith)
          | exact hxz (by linarith)
          | exact hxp (by linarith)
    · rcases a with ⟨a, sa⟩
      rcases b with ⟨b, sb⟩
      rcases c with ⟨c, sc⟩
      fin_cases a <;> fin_cases b <;> fin_cases c
      all_goals norm_num at horder
      all_goals cases sa <;> cases sb <;> cases sc
      all_goals
        norm_num [RealThreeByThreeGridSecant.incident] at ha hb hc <;>
          first
          | linarith
          | exact hym (by linarith)
          | exact hyz (by linarith)
          | exact hyp (by linarith)

/-- Affine half of the real `3 x 3` grid lemma: an external finite point is
not incident with three ordinary grid secants of three different directions.
Together with `no_three_distinct_same_direction`, this proves that no point
of the affine or ideal plane outside the grid has three ordinary secants. -/
theorem RealThreeByThreeGridSecant.external_not_three_distinct_directions
    (a b c : RealThreeByThreeGridSecant) (x y : ℝ)
    (hab : a.1 ≠ b.1) (hac : a.1 ≠ c.1) (hbc : b.1 ≠ c.1)
    (ha : a.incident x y) (hb : b.incident x y)
    (hc : c.incident x y) :
    ¬ RealThreeByThreeGridExternal x y := by
  have habval : a.1.val ≠ b.1.val := by
    intro h
    apply hab
    exact Fin.ext h
  have hacval : a.1.val ≠ c.1.val := by
    intro h
    apply hac
    exact Fin.ext h
  have hbcval : b.1.val ≠ c.1.val := by
    intro h
    apply hbc
    exact Fin.ext h
  have horder :
      (a.1.val < b.1.val ∧ b.1.val < c.1.val) ∨
      (a.1.val < c.1.val ∧ c.1.val < b.1.val) ∨
      (b.1.val < a.1.val ∧ a.1.val < c.1.val) ∨
      (b.1.val < c.1.val ∧ c.1.val < a.1.val) ∨
      (c.1.val < a.1.val ∧ a.1.val < b.1.val) ∨
      (c.1.val < b.1.val ∧ b.1.val < a.1.val) := by
    omega
  rcases horder with h | h | h | h | h | h
  · exact realThreeByThreeGrid_external_not_three_ordered
      a b c x y h ha hb hc
  · exact realThreeByThreeGrid_external_not_three_ordered
      a c b x y h ha hc hb
  · exact realThreeByThreeGrid_external_not_three_ordered
      b a c x y h hb ha hc
  · exact realThreeByThreeGrid_external_not_three_ordered
      b c a x y h hb hc ha
  · exact realThreeByThreeGrid_external_not_three_ordered
      c a b x y h hc ha hb
  · exact realThreeByThreeGrid_external_not_three_ordered
      c b a x y h hc hb ha

/-- Two incident ordinary grid secants in one direction family are the same
secant.  The two different sign choices are parallel distinct lines, hence
cannot meet at an affine point. -/
theorem RealThreeByThreeGridSecant.eq_of_same_direction_of_incident
    (s t : RealThreeByThreeGridSecant) (x y : ℝ)
    (hdir : s.direction = t.direction)
    (hs : s.incident x y) (ht : t.incident x y) : s = t := by
  rcases s with ⟨i, si⟩
  rcases t with ⟨j, sj⟩
  have hij : i = j := realThreeByThreeGridSecantSlope_injective hdir
  subst j
  fin_cases i <;> cases si <;> cases sj <;>
    simp [RealThreeByThreeGridSecant.incident] at hs ht ⊢ <;>
    linarith

/-- Complete affine form of the normalized-grid calculation: three distinct
ordinary secants cannot concur outside `{-1,0,1}²`.  This is the form needed
after the projective `3 x 3` normalization when a candidate external pivot
is supplied by either forbidden-grid local type. -/
theorem RealThreeByThreeGridSecant.external_not_three_distinct
    (a b c : RealThreeByThreeGridSecant) (x y : ℝ)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (ha : a.incident x y) (hb : b.incident x y)
    (hc : c.incident x y) :
    ¬ RealThreeByThreeGridExternal x y := by
  by_cases habdir : a.direction = b.direction
  · exact (hab (a.eq_of_same_direction_of_incident b x y habdir ha hb)).elim
  by_cases hacdir : a.direction = c.direction
  · exact (hac (a.eq_of_same_direction_of_incident c x y hacdir ha hc)).elim
  by_cases hbcdir : b.direction = c.direction
  · exact (hbc (b.eq_of_same_direction_of_incident c x y hbcdir hb hc)).elim
  apply a.external_not_three_distinct_directions b c x y
  · intro h
    apply habdir
    exact (RealThreeByThreeGridSecant.direction_eq_iff a b).mpr h
  · intro h
    apply hacdir
    exact (RealThreeByThreeGridSecant.direction_eq_iff a c).mpr h
  · intro h
    apply hbcdir
    exact (RealThreeByThreeGridSecant.direction_eq_iff b c).mpr h
  · exact ha
  · exact hb
  · exact hc

end Erdos506.Incidence
