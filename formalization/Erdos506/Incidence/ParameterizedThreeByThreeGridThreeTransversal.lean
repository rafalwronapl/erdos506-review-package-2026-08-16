import Erdos506.Incidence.ParameterizedThreeByThreeGridObstruction

/-!
# Three-transversal obstruction for a parameterized real `3 x 3` grid

The two-transversal determinant table already forces both pencil parameters
into a finite three-value set.  This file records the final finite fact:
for every one of the nine resulting parameter pairs, exactly two of the six
permutation transversals are collinear.  Consequently a real parameterized
three-by-three grid admits no three pairwise distinct transversals.

This is deliberately a statement about the parameterized grid alone.  It
contains neither an incidence-census hypothesis nor a chosen normalization.
-/

namespace Erdos506.Incidence

private theorem parameterizedThreeByThreeGrid_no_three_of_two
    {α : Type*} {x y s t u : α}
    (hs : s = x ∨ s = y) (ht : t = x ∨ t = y) (hu : u = x ∨ u = y)
    (hst : s ≠ t) (hsu : s ≠ u) (htu : t ≠ u) : False := by
  rcases hs with rfl | rfl <;>
    rcases ht with rfl | rfl <;>
    rcases hu with rfl | rfl
  all_goals first | exact hst rfl | exact hsu rfl | exact htu rfl

private theorem parameterizedThreeByThreeGrid_transversal_codes_minusTwo_minusTwo
    {t : Fin 6}
    (ht : ParameterizedThreeByThreeGridTransversal (-2 : ℝ) (-2 : ℝ) t) :
    t = 0 ∨ t = 1 := by
  fin_cases t
  · exact Or.inl rfl
  · exact Or.inr rfl
  · norm_num [ParameterizedThreeByThreeGridTransversal,
      parameterizedThreeByThreeTransversal_determinant_eq_polynomial,
      parameterizedThreeByThreeTransversalPolynomial] at ht
  · norm_num [ParameterizedThreeByThreeGridTransversal,
      parameterizedThreeByThreeTransversal_determinant_eq_polynomial,
      parameterizedThreeByThreeTransversalPolynomial] at ht
  · norm_num [ParameterizedThreeByThreeGridTransversal,
      parameterizedThreeByThreeTransversal_determinant_eq_polynomial,
      parameterizedThreeByThreeTransversalPolynomial] at ht
  · norm_num [ParameterizedThreeByThreeGridTransversal,
      parameterizedThreeByThreeTransversal_determinant_eq_polynomial,
      parameterizedThreeByThreeTransversalPolynomial] at ht

private theorem parameterizedThreeByThreeGrid_transversal_codes_minusTwo_minusHalf
    {t : Fin 6}
    (ht : ParameterizedThreeByThreeGridTransversal (-2 : ℝ) (-1 / 2 : ℝ) t) :
    t = 4 ∨ t = 5 := by
  fin_cases t
  · norm_num [ParameterizedThreeByThreeGridTransversal,
      parameterizedThreeByThreeTransversal_determinant_eq_polynomial,
      parameterizedThreeByThreeTransversalPolynomial] at ht
  · norm_num [ParameterizedThreeByThreeGridTransversal,
      parameterizedThreeByThreeTransversal_determinant_eq_polynomial,
      parameterizedThreeByThreeTransversalPolynomial] at ht
  · norm_num [ParameterizedThreeByThreeGridTransversal,
      parameterizedThreeByThreeTransversal_determinant_eq_polynomial,
      parameterizedThreeByThreeTransversalPolynomial] at ht
  · norm_num [ParameterizedThreeByThreeGridTransversal,
      parameterizedThreeByThreeTransversal_determinant_eq_polynomial,
      parameterizedThreeByThreeTransversalPolynomial] at ht
  · exact Or.inl rfl
  · exact Or.inr rfl

private theorem parameterizedThreeByThreeGrid_transversal_codes_minusTwo_one
    {t : Fin 6}
    (ht : ParameterizedThreeByThreeGridTransversal (-2 : ℝ) (1 : ℝ) t) :
    t = 2 ∨ t = 3 := by
  fin_cases t
  · norm_num [ParameterizedThreeByThreeGridTransversal,
      parameterizedThreeByThreeTransversal_determinant_eq_polynomial,
      parameterizedThreeByThreeTransversalPolynomial] at ht
  · norm_num [ParameterizedThreeByThreeGridTransversal,
      parameterizedThreeByThreeTransversal_determinant_eq_polynomial,
      parameterizedThreeByThreeTransversalPolynomial] at ht
  · exact Or.inl rfl
  · exact Or.inr rfl
  · norm_num [ParameterizedThreeByThreeGridTransversal,
      parameterizedThreeByThreeTransversal_determinant_eq_polynomial,
      parameterizedThreeByThreeTransversalPolynomial] at ht
  · norm_num [ParameterizedThreeByThreeGridTransversal,
      parameterizedThreeByThreeTransversal_determinant_eq_polynomial,
      parameterizedThreeByThreeTransversalPolynomial] at ht

private theorem parameterizedThreeByThreeGrid_transversal_codes_minusHalf_minusTwo
    {t : Fin 6}
    (ht : ParameterizedThreeByThreeGridTransversal (-1 / 2 : ℝ) (-2 : ℝ) t) :
    t = 3 ∨ t = 5 := by
  fin_cases t
  · norm_num [ParameterizedThreeByThreeGridTransversal,
      parameterizedThreeByThreeTransversal_determinant_eq_polynomial,
      parameterizedThreeByThreeTransversalPolynomial] at ht
  · norm_num [ParameterizedThreeByThreeGridTransversal,
      parameterizedThreeByThreeTransversal_determinant_eq_polynomial,
      parameterizedThreeByThreeTransversalPolynomial] at ht
  · norm_num [ParameterizedThreeByThreeGridTransversal,
      parameterizedThreeByThreeTransversal_determinant_eq_polynomial,
      parameterizedThreeByThreeTransversalPolynomial] at ht
  · exact Or.inl rfl
  · norm_num [ParameterizedThreeByThreeGridTransversal,
      parameterizedThreeByThreeTransversal_determinant_eq_polynomial,
      parameterizedThreeByThreeTransversalPolynomial] at ht
  · exact Or.inr rfl

private theorem parameterizedThreeByThreeGrid_transversal_codes_minusHalf_minusHalf
    {t : Fin 6}
    (ht : ParameterizedThreeByThreeGridTransversal
      (-1 / 2 : ℝ) (-1 / 2 : ℝ) t) :
    t = 0 ∨ t = 2 := by
  fin_cases t
  · exact Or.inl rfl
  · norm_num [ParameterizedThreeByThreeGridTransversal,
      parameterizedThreeByThreeTransversal_determinant_eq_polynomial,
      parameterizedThreeByThreeTransversalPolynomial] at ht
  · exact Or.inr rfl
  · norm_num [ParameterizedThreeByThreeGridTransversal,
      parameterizedThreeByThreeTransversal_determinant_eq_polynomial,
      parameterizedThreeByThreeTransversalPolynomial] at ht
  · norm_num [ParameterizedThreeByThreeGridTransversal,
      parameterizedThreeByThreeTransversal_determinant_eq_polynomial,
      parameterizedThreeByThreeTransversalPolynomial] at ht
  · norm_num [ParameterizedThreeByThreeGridTransversal,
      parameterizedThreeByThreeTransversal_determinant_eq_polynomial,
      parameterizedThreeByThreeTransversalPolynomial] at ht

private theorem parameterizedThreeByThreeGrid_transversal_codes_minusHalf_one
    {t : Fin 6}
    (ht : ParameterizedThreeByThreeGridTransversal (-1 / 2 : ℝ) (1 : ℝ) t) :
    t = 1 ∨ t = 4 := by
  fin_cases t
  · norm_num [ParameterizedThreeByThreeGridTransversal,
      parameterizedThreeByThreeTransversal_determinant_eq_polynomial,
      parameterizedThreeByThreeTransversalPolynomial] at ht
  · exact Or.inl rfl
  · norm_num [ParameterizedThreeByThreeGridTransversal,
      parameterizedThreeByThreeTransversal_determinant_eq_polynomial,
      parameterizedThreeByThreeTransversalPolynomial] at ht
  · norm_num [ParameterizedThreeByThreeGridTransversal,
      parameterizedThreeByThreeTransversal_determinant_eq_polynomial,
      parameterizedThreeByThreeTransversalPolynomial] at ht
  · exact Or.inr rfl
  · norm_num [ParameterizedThreeByThreeGridTransversal,
      parameterizedThreeByThreeTransversal_determinant_eq_polynomial,
      parameterizedThreeByThreeTransversalPolynomial] at ht

private theorem parameterizedThreeByThreeGrid_transversal_codes_one_minusTwo
    {t : Fin 6}
    (ht : ParameterizedThreeByThreeGridTransversal (1 : ℝ) (-2 : ℝ) t) :
    t = 2 ∨ t = 4 := by
  fin_cases t
  · norm_num [ParameterizedThreeByThreeGridTransversal,
      parameterizedThreeByThreeTransversal_determinant_eq_polynomial,
      parameterizedThreeByThreeTransversalPolynomial] at ht
  · norm_num [ParameterizedThreeByThreeGridTransversal,
      parameterizedThreeByThreeTransversal_determinant_eq_polynomial,
      parameterizedThreeByThreeTransversalPolynomial] at ht
  · exact Or.inl rfl
  · norm_num [ParameterizedThreeByThreeGridTransversal,
      parameterizedThreeByThreeTransversal_determinant_eq_polynomial,
      parameterizedThreeByThreeTransversalPolynomial] at ht
  · exact Or.inr rfl
  · norm_num [ParameterizedThreeByThreeGridTransversal,
      parameterizedThreeByThreeTransversal_determinant_eq_polynomial,
      parameterizedThreeByThreeTransversalPolynomial] at ht

private theorem parameterizedThreeByThreeGrid_transversal_codes_one_minusHalf
    {t : Fin 6}
    (ht : ParameterizedThreeByThreeGridTransversal (1 : ℝ) (-1 / 2 : ℝ) t) :
    t = 1 ∨ t = 3 := by
  fin_cases t
  · norm_num [ParameterizedThreeByThreeGridTransversal,
      parameterizedThreeByThreeTransversal_determinant_eq_polynomial,
      parameterizedThreeByThreeTransversalPolynomial] at ht
  · exact Or.inl rfl
  · norm_num [ParameterizedThreeByThreeGridTransversal,
      parameterizedThreeByThreeTransversal_determinant_eq_polynomial,
      parameterizedThreeByThreeTransversalPolynomial] at ht
  · exact Or.inr rfl
  · norm_num [ParameterizedThreeByThreeGridTransversal,
      parameterizedThreeByThreeTransversal_determinant_eq_polynomial,
      parameterizedThreeByThreeTransversalPolynomial] at ht
  · norm_num [ParameterizedThreeByThreeGridTransversal,
      parameterizedThreeByThreeTransversal_determinant_eq_polynomial,
      parameterizedThreeByThreeTransversalPolynomial] at ht

private theorem parameterizedThreeByThreeGrid_transversal_codes_one_one
    {t : Fin 6}
    (ht : ParameterizedThreeByThreeGridTransversal (1 : ℝ) (1 : ℝ) t) :
    t = 0 ∨ t = 5 := by
  fin_cases t
  · exact Or.inl rfl
  · norm_num [ParameterizedThreeByThreeGridTransversal,
      parameterizedThreeByThreeTransversal_determinant_eq_polynomial,
      parameterizedThreeByThreeTransversalPolynomial] at ht
  · norm_num [ParameterizedThreeByThreeGridTransversal,
      parameterizedThreeByThreeTransversal_determinant_eq_polynomial,
      parameterizedThreeByThreeTransversalPolynomial] at ht
  · norm_num [ParameterizedThreeByThreeGridTransversal,
      parameterizedThreeByThreeTransversal_determinant_eq_polynomial,
      parameterizedThreeByThreeTransversalPolynomial] at ht
  · norm_num [ParameterizedThreeByThreeGridTransversal,
      parameterizedThreeByThreeTransversal_determinant_eq_polynomial,
      parameterizedThreeByThreeTransversalPolynomial] at ht
  · exact Or.inr rfl

/-- A parameterized real `3 x 3` grid with three distinct coordinate values
in each pencil has no three pairwise distinct transversal lines. -/
theorem parameterizedThreeByThreeGrid_no_three_distinct_transversals
    {a b : ℝ} {s t u : Fin 6}
    (ha_minus : a ≠ -1) (ha_zero : a ≠ 0)
    (hb_minus : b ≠ -1) (hb_zero : b ≠ 0)
    (hst : s ≠ t) (hsu : s ≠ u) (htu : t ≠ u)
    (hs : ParameterizedThreeByThreeGridTransversal a b s)
    (ht : ParameterizedThreeByThreeGridTransversal a b t)
    (hu : ParameterizedThreeByThreeGridTransversal a b u) : False := by
  have hcases := parameterizedThreeByThreeGrid_two_transversals_parameter_cases
    ha_minus ha_zero hb_minus hb_zero hst hs ht
  rcases hcases with ⟨ha, hb⟩
  rcases ha with ha | ha | ha <;> rcases hb with hb | hb | hb
  · subst a
    subst b
    exact parameterizedThreeByThreeGrid_no_three_of_two
      (parameterizedThreeByThreeGrid_transversal_codes_minusTwo_minusTwo hs)
      (parameterizedThreeByThreeGrid_transversal_codes_minusTwo_minusTwo ht)
      (parameterizedThreeByThreeGrid_transversal_codes_minusTwo_minusTwo hu)
      hst hsu htu
  · subst a
    subst b
    exact parameterizedThreeByThreeGrid_no_three_of_two
      (parameterizedThreeByThreeGrid_transversal_codes_minusTwo_minusHalf hs)
      (parameterizedThreeByThreeGrid_transversal_codes_minusTwo_minusHalf ht)
      (parameterizedThreeByThreeGrid_transversal_codes_minusTwo_minusHalf hu)
      hst hsu htu
  · subst a
    subst b
    exact parameterizedThreeByThreeGrid_no_three_of_two
      (parameterizedThreeByThreeGrid_transversal_codes_minusTwo_one hs)
      (parameterizedThreeByThreeGrid_transversal_codes_minusTwo_one ht)
      (parameterizedThreeByThreeGrid_transversal_codes_minusTwo_one hu)
      hst hsu htu
  · subst a
    subst b
    exact parameterizedThreeByThreeGrid_no_three_of_two
      (parameterizedThreeByThreeGrid_transversal_codes_minusHalf_minusTwo hs)
      (parameterizedThreeByThreeGrid_transversal_codes_minusHalf_minusTwo ht)
      (parameterizedThreeByThreeGrid_transversal_codes_minusHalf_minusTwo hu)
      hst hsu htu
  · subst a
    subst b
    exact parameterizedThreeByThreeGrid_no_three_of_two
      (parameterizedThreeByThreeGrid_transversal_codes_minusHalf_minusHalf hs)
      (parameterizedThreeByThreeGrid_transversal_codes_minusHalf_minusHalf ht)
      (parameterizedThreeByThreeGrid_transversal_codes_minusHalf_minusHalf hu)
      hst hsu htu
  · subst a
    subst b
    exact parameterizedThreeByThreeGrid_no_three_of_two
      (parameterizedThreeByThreeGrid_transversal_codes_minusHalf_one hs)
      (parameterizedThreeByThreeGrid_transversal_codes_minusHalf_one ht)
      (parameterizedThreeByThreeGrid_transversal_codes_minusHalf_one hu)
      hst hsu htu
  · subst a
    subst b
    exact parameterizedThreeByThreeGrid_no_three_of_two
      (parameterizedThreeByThreeGrid_transversal_codes_one_minusTwo hs)
      (parameterizedThreeByThreeGrid_transversal_codes_one_minusTwo ht)
      (parameterizedThreeByThreeGrid_transversal_codes_one_minusTwo hu)
      hst hsu htu
  · subst a
    subst b
    exact parameterizedThreeByThreeGrid_no_three_of_two
      (parameterizedThreeByThreeGrid_transversal_codes_one_minusHalf hs)
      (parameterizedThreeByThreeGrid_transversal_codes_one_minusHalf ht)
      (parameterizedThreeByThreeGrid_transversal_codes_one_minusHalf hu)
      hst hsu htu
  · subst a
    subst b
    exact parameterizedThreeByThreeGrid_no_three_of_two
      (parameterizedThreeByThreeGrid_transversal_codes_one_one hs)
      (parameterizedThreeByThreeGrid_transversal_codes_one_one ht)
      (parameterizedThreeByThreeGrid_transversal_codes_one_one hu)
      hst hsu htu

end Erdos506.Incidence
