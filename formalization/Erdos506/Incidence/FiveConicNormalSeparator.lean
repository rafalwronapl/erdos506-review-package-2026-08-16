import Erdos506.Incidence.FiveConicOneSingleTraceRigidity

/-!
# The normal one-single five-conic separator

This is the finite, algebraic endpoint of the one-single/two-double page
calculation.  In the normal cyclic chart with parameters
`∞, 0, 1, λ, t` and `1 < λ < t`, a line through the fifth point and two
diagonal centres can use only the first two centres.  The two other diagonal
sides are excluded by the literal determinant computations already proved in
`FiveConicOneSingleTraceRigidity`.

The statement deliberately speaks only about homogeneous representatives;
the actual five-trace transport is supplied separately by the projective
parameter bridge.
-/

namespace Erdos506.Incidence

open Matrix

/-- The three complete-quadrangle diagonal representatives in their canonical
finite indexing. -/
def fiveConicNormalDiagonal (lam : ℝ) : Fin 3 → Homogeneous3 :=
  ![fiveConicNormalDiagonalZero lam,
    fiveConicNormalDiagonalOne lam,
    fiveConicNormalDiagonalTwo lam]

/-- Reversing the last two determinant rows preserves the zero locus. -/
private theorem fiveConic_det_zero_of_swap_last_zero
    (u v w : Homogeneous3)
    (h : Matrix.det ![u, w, v] = 0) :
    Matrix.det ![u, v, w] = 0 := by
  calc
    Matrix.det ![u, v, w] = -Matrix.det ![u, w, v] := by
      simp [Matrix.det_fin_three]
      ring
    _ = 0 := by rw [h]; ring

/-- In the normal cyclic chart, a collinear pair of *distinct* diagonal
centres with the complementary fifth conic point is exactly the pair of the
first two diagonal centres (in either order). -/
theorem fiveConicNormal_collinear_diagonal_pair_eq_zero_one
    {lam t : ℝ} (hlam : 1 < lam) (ht : lam < t)
    (i j : Fin 3) (hij : i ≠ j)
    (hcol : Matrix.det ![fiveConicNormalPoint t,
      fiveConicNormalDiagonal lam i, fiveConicNormalDiagonal lam j] = 0) :
    (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0) := by
  fin_cases i
  · fin_cases j
    · exact (hij rfl).elim
    · exact Or.inl ⟨rfl, rfl⟩
    · exfalso
      apply fiveConicNormal_not_collinear_zero_two_of_one_lt hlam ht
      simpa [fiveConicNormalDiagonal] using hcol
  · fin_cases j
    · exact Or.inr ⟨rfl, rfl⟩
    · exact (hij rfl).elim
    · exfalso
      apply fiveConicNormal_not_collinear_one_two_of_one_lt hlam ht
      simpa [fiveConicNormalDiagonal] using hcol
  · fin_cases j
    · exfalso
      apply fiveConicNormal_not_collinear_zero_two_of_one_lt hlam ht
      apply fiveConic_det_zero_of_swap_last_zero _ _ _
      simpa [fiveConicNormalDiagonal] using hcol
    · exfalso
      apply fiveConicNormal_not_collinear_one_two_of_one_lt hlam ht
      apply fiveConic_det_zero_of_swap_last_zero _ _ _
      simpa [fiveConicNormalDiagonal] using hcol
    · exact (hij rfl).elim

end Erdos506.Incidence
