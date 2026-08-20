import Mathlib.Tactic

/-!
# Arithmetic certificates for the five-circle branch at nine points

The difficult `n = 9` branch selects a proper circle through five labels and
classifies the four labels outside it.  The geometric and finite-incidence
adapters live elsewhere; this file isolates the four small linear
certificates used after those adapters have produced their census rows.

Keeping the certificates separate makes the proof boundary explicit: no
geometric conclusion is assumed here, and every theorem is Presburger
arithmetic over the displayed manuscript rows.
-/

namespace Erdos506.V1

/-- Two distinct equal-sized subsets leave a two-set that is contained in
neither of them.  For two outsider triples this is the missing pair in the
union of their pair-shadows. -/
theorem exists_pair_not_subset_either_of_ne_of_card_eq
    {α : Type*} [DecidableEq α]
    {X A B : Finset α}
    (hAX : A ⊆ X) (hBX : B ⊆ X)
    (hcard : A.card = B.card) (hne : A ≠ B) :
    ∃ E : Finset α, E ⊆ X ∧ E.card = 2 ∧ ¬E ⊆ A ∧ ¬E ⊆ B := by
  have hab : ∃ a ∈ A, a ∉ B := by
    by_contra h
    push Not at h
    have hsub : A ⊆ B := fun a ha => h a ha
    exact hne (Finset.eq_of_subset_of_card_le hsub (by omega))
  have hba : ∃ b ∈ B, b ∉ A := by
    by_contra h
    push Not at h
    have hsub : B ⊆ A := fun b hb => h b hb
    exact hne (Finset.eq_of_subset_of_card_le hsub (by omega)).symm
  obtain ⟨a, haA, haB⟩ := hab
  obtain ⟨b, hbB, hbA⟩ := hba
  have habne : a ≠ b := by
    intro heq
    exact haB (heq ▸ hbB)
  refine ⟨{a, b}, ?_, Finset.card_pair habne, ?_, ?_⟩
  · intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact hAX haA
    · exact hBX hbB
  · intro hEA
    exact hbA (hEA (by simp))
  · intro hEB
    exact haB (hEB (by simp))

/-- Four outsiders in general position contribute four distinct triple
circles.  Together with the four-outsider master row this exceeds the chord
incidence capacity `R ≤ 8`. -/
theorem nine_five_general_position_arithmetic
    {R h : ℕ} (hR : R ≤ 8) (hh : 4 ≤ h) (hmaster : 5 + h ≤ R) :
    False := by
  omega

/-- Arithmetic end of the all-four-collinear outsider case.  Here `a` and
`b` count circles of types `(1,2)` and `(2,2)`, while `R` is the total chord
incidence and `C` the full circle count. -/
theorem nine_five_four_collinear_arithmetic
    {R a b C : ℕ}
    (hR : R ≤ 8)
    (hab : a + 2 * b = 30)
    (hb : b ≤ 12)
    (hsub : R + b ≤ 40)
    (hC : C = 1 + (40 - R - b) + a)
    (hCle : C ≤ 24) :
    False := by
  omega

/-- The equalities forced in the exactly-three-collinear case before the
last pair-shadow obstruction.  This theorem deliberately stops at the
combinatorial boundary: the missing contradiction is that two distinct
three-subsets of a four-set cover only five of its six pairs. -/
theorem nine_five_three_collinear_forced_rows
    {R h c I C : ℕ}
    (hR : R ≤ 8)
    (hhc : 3 ≤ h + c)
    (hmaster : 5 + h + c ≤ R)
    (hI : I ≤ 12)
    (hCeq : C + I = 36)
    (hCle : C ≤ 24) :
    R = 8 ∧ h + c = 3 ∧ I = 12 ∧ C = 24 := by
  omega

/-- Arithmetic contradiction when the four outsiders lie on a second
circle disjoint from the selected five-circle.  The cross-block capacity is
encoded by `b + v ≤ 12`; all other hypotheses are the exact master,
triple, and global-line rows. -/
theorem nine_five_concyclic_disjoint_arithmetic
    {R a b e v ell : ℕ}
    (hbe : b + e = 12)
    (hcross : b + v ≤ 12)
    (hmaster : 6 + e + a ≤ R)
    (htriple : ell + 2 * v + a = 6 + 2 * e)
    (hline : 3 * R + 3 * ell + v ≤ 33) :
    False := by
  omega

/-- Arithmetic contradiction when the selected five-circle and the
four-outsider circle share one selected point.  After deleting that point,
the sharp `4 + 4` cross-block capacity is `b + v ≤ 10`. -/
theorem nine_five_concyclic_one_common_arithmetic
    {R a b e v ell : ℕ}
    (hbe : b + e = 12)
    (hcross : b + v ≤ 10)
    (hmaster : 6 + e + a ≤ R)
    (hea : e + a ≤ 2)
    (htriple : ell + 2 * v + a + 6 = 6 + 2 * e)
    (hline : 3 * R + 3 * ell + v ≤ 33) :
    False := by
  omega

end Erdos506.V1
