import Mathlib.Tactic

/-!
# Scalar router for the ten-point selected-five-circle branch

This file formalizes only the integer arithmetic in the scalar table
`eq:n10-scalar-faces` of the paper.  There is no geometric input and no
external solver certificate.

The variables have the paper's meanings:

* `C` is the circle count;
* `x`, `b`, and `k` are the numbers of generalized blocks of sizes three,
  four, and five;
* `alpha` is the number of points of high three-block degree;
* `L` is the total number of rich lines, while `h` and `g` count its
  four- and five-point members.

All counts are natural numbers.  The hypotheses `alpha <= 10` and
`h + g <= L` record their immediate counting bounds; the arithmetic router
is strong enough that these two bounds are redundant, but retaining them
makes the theorem interface match its intended application.
-/

namespace Erdos506.V1

/-- The scalar hypotheses common to the five rows `C = 28, ..., 32`.

The two rows containing subtraction are stated over `Int`, avoiding
truncated subtraction on natural-number counts. -/
def TenFiveScalarConditions
    (C k x b alpha L h g : Nat) : Prop :=
  1 <= k /\ k <= 3 /\
  x = 20 + alpha /\
  x + 4 * b + 10 * k = 120 /\
  (4 : Int) * (L : Int) =
    180 - 4 * (C : Int) + 3 * (alpha : Int) - 6 * (k : Int) /\
  15 * (alpha : Int) - 34 * (k : Int) +
      28 * (h : Int) + 64 * (g : Int) <= 36 * (C : Int) - 1140 /\
  alpha <= 10 /\ h + g <= L

/-- There is no scalar face at `C = 28`. -/
theorem ten_five_scalar_faces_c28
    {k x b alpha L h g : Nat}
    (hs : TenFiveScalarConditions 28 k x b alpha L h g) : False := by
  rcases hs with
    ⟨hkLower, hkUpper, hx, htriple, hline, hac, halpha, hrich⟩
  norm_num at hline hac
  interval_cases k <;> omega

/-- There is no scalar face at `C = 29`. -/
theorem ten_five_scalar_faces_c29
    {k x b alpha L h g : Nat}
    (hs : TenFiveScalarConditions 29 k x b alpha L h g) : False := by
  rcases hs with
    ⟨hkLower, hkUpper, hx, htriple, hline, hac, halpha, hrich⟩
  norm_num at hline hac
  interval_cases k <;> omega

/-- The two scalar faces at `C = 30`. -/
theorem ten_five_scalar_faces_c30
    {k x b alpha L h g : Nat}
    (hs : TenFiveScalarConditions 30 k x b alpha L h g) :
    ((k = 2 /\ alpha = 0 /\ L = 12) \/
      (k = 3 /\ alpha = 2 /\ L = 12)) /\
      h = 0 /\ g = 0 := by
  rcases hs with
    ⟨hkLower, hkUpper, hx, htriple, hline, hac, halpha, hrich⟩
  norm_num at hline hac
  interval_cases k <;> omega

/-- The two scalar faces, with their line states, at `C = 31`. -/
theorem ten_five_scalar_faces_c31
    {k x b alpha L h g : Nat}
    (hs : TenFiveScalarConditions 31 k x b alpha L h g) :
    ((k = 2 /\ alpha = 0 /\ L = 11) \/
      (k = 3 /\ alpha = 2 /\ L = 11)) /\
      ((h = 0 /\ g = 0) \/ (h = 1 /\ g = 0)) := by
  rcases hs with
    ⟨hkLower, hkUpper, hx, htriple, hline, hac, halpha, hrich⟩
  norm_num at hline hac
  interval_cases k <;> omega

/-- The complete scalar-face table at `C = 32`. -/
theorem ten_five_scalar_faces_c32
    {k x b alpha L h g : Nat}
    (hs : TenFiveScalarConditions 32 k x b alpha L h g) :
    ((((k = 1 /\ alpha = 2 /\ L = 13) \/
        (k = 2 /\ alpha = 4 /\ L = 13) \/
        (k = 3 /\ alpha = 6 /\ L = 13)) /\
        h = 0 /\ g = 0) \/
      (k = 2 /\ alpha = 0 /\ L = 10 /\
        ((h = 0 /\ g = 0) \/ (h = 1 /\ g = 0) \/
          (h = 2 /\ g = 0) \/ (h = 0 /\ g = 1))) \/
      (k = 3 /\ alpha = 2 /\ L = 10 /\
        ((h = 0 /\ g = 0) \/ (h = 1 /\ g = 0) \/
          (h = 2 /\ g = 0) \/ (h = 3 /\ g = 0) \/
          (h = 0 /\ g = 1)))) := by
  rcases hs with
    ⟨hkLower, hkUpper, hx, htriple, hline, hac, halpha, hrich⟩
  norm_num at hline hac
  interval_cases k <;> omega

/-- Unified form of the exact scalar table for `28 <= C <= 32`.

In particular, the first two values of `C` are absent, and every remaining
tuple is one of the faces printed in the paper. -/
theorem ten_five_scalar_faces
    {C k x b alpha L h g : Nat}
    (hCLower : 28 <= C) (hCUpper : C <= 32)
    (hs : TenFiveScalarConditions C k x b alpha L h g) :
    (C = 30 /\
        (((k = 2 /\ alpha = 0 /\ L = 12) \/
          (k = 3 /\ alpha = 2 /\ L = 12)) /\
          h = 0 /\ g = 0)) \/
    (C = 31 /\
        (((k = 2 /\ alpha = 0 /\ L = 11) \/
          (k = 3 /\ alpha = 2 /\ L = 11)) /\
          ((h = 0 /\ g = 0) \/ (h = 1 /\ g = 0)))) \/
    (C = 32 /\
        (((((k = 1 /\ alpha = 2 /\ L = 13) \/
            (k = 2 /\ alpha = 4 /\ L = 13) \/
            (k = 3 /\ alpha = 6 /\ L = 13)) /\
            h = 0 /\ g = 0) \/
          (k = 2 /\ alpha = 0 /\ L = 10 /\
            ((h = 0 /\ g = 0) \/ (h = 1 /\ g = 0) \/
              (h = 2 /\ g = 0) \/ (h = 0 /\ g = 1))) \/
          (k = 3 /\ alpha = 2 /\ L = 10 /\
            ((h = 0 /\ g = 0) \/ (h = 1 /\ g = 0) \/
              (h = 2 /\ g = 0) \/ (h = 3 /\ g = 0) \/
              (h = 0 /\ g = 1)))))) := by
  interval_cases C
  · exact (ten_five_scalar_faces_c28 hs).elim
  · exact (ten_five_scalar_faces_c29 hs).elim
  · exact Or.inl ⟨rfl, ten_five_scalar_faces_c30 hs⟩
  · exact Or.inr (Or.inl ⟨rfl, ten_five_scalar_faces_c31 hs⟩)
  · exact Or.inr (Or.inr ⟨rfl, ten_five_scalar_faces_c32 hs⟩)

end Erdos506.V1
