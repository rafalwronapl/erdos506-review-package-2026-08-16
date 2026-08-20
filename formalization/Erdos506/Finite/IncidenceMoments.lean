import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Tactic

/-!
# First and second moments of finite incidences

This file supplies a reusable degree-moment count.  Its main specialised
consequence says that a family of five-subsets of a ten-element ground set,
with pairwise intersections of size at most two, has at most six members.
-/

namespace Erdos506.Finite

open scoped BigOperators

def incidenceIndicator {Point Block : Type*} [DecidableEq Point]
    (support : Block → Finset Point) (x : Point) (b : Block) : ℕ :=
  if x ∈ support b then 1 else 0

def incidenceDegree {Point Block : Type*}
    [DecidableEq Point] [DecidableEq Block]
    (B : Finset Block) (support : Block → Finset Point) (x : Point) : ℕ :=
  ∑ b ∈ B, incidenceIndicator support x b

theorem sum_indicator_eq_card {Point Block : Type*}
    [Fintype Point] [DecidableEq Point]
    (support : Block → Finset Point) (b : Block) :
    (∑ x : Point, incidenceIndicator support x b) = (support b).card := by
  simp [incidenceIndicator]

theorem sum_indicator_mul_eq_card_inter {Point Block : Type*}
    [Fintype Point] [DecidableEq Point]
    (support : Block → Finset Point) (b c : Block) :
    (∑ x : Point,
      incidenceIndicator support x b * incidenceIndicator support x c) =
        (support b ∩ support c).card := by
  simp [incidenceIndicator, Finset.inter_comm]

theorem sum_incidenceDegree {Point Block : Type*}
    [Fintype Point] [DecidableEq Point] [DecidableEq Block]
    (B : Finset Block) (support : Block → Finset Point) :
    (∑ x : Point, incidenceDegree B support x) =
      ∑ b ∈ B, (support b).card := by
  classical
  change (∑ x ∈ (Finset.univ : Finset Point),
      ∑ b ∈ B, incidenceIndicator support x b) = _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b hb
  exact sum_indicator_eq_card support b

theorem sum_sq_incidenceDegree {Point Block : Type*}
    [Fintype Point] [DecidableEq Point] [DecidableEq Block]
    (B : Finset Block) (support : Block → Finset Point) :
    (∑ x : Point, (incidenceDegree B support x) ^ 2) =
      ∑ b ∈ B, ∑ c ∈ B, (support b ∩ support c).card := by
  classical
  change (∑ x ∈ (Finset.univ : Finset Point),
      (∑ b ∈ B, incidenceIndicator support x b) ^ 2) = _
  calc
    (∑ x ∈ (Finset.univ : Finset Point),
        (∑ b ∈ B, incidenceIndicator support x b) ^ 2) =
        ∑ x ∈ (Finset.univ : Finset Point),
          ∑ b ∈ B, ∑ c ∈ B,
            incidenceIndicator support x b * incidenceIndicator support x c := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [pow_two, Finset.sum_mul_sum]
    _ = ∑ b ∈ B, ∑ x ∈ (Finset.univ : Finset Point),
          ∑ c ∈ B,
            incidenceIndicator support x b * incidenceIndicator support x c := by
      rw [Finset.sum_comm]
    _ = ∑ b ∈ B, ∑ c ∈ B, ∑ x : Point,
          incidenceIndicator support x b * incidenceIndicator support x c := by
      apply Finset.sum_congr rfl
      intro b hb
      rw [Finset.sum_comm]
    _ = ∑ b ∈ B, ∑ c ∈ B, (support b ∩ support c).card := by
      apply Finset.sum_congr rfl
      intro b hb
      apply Finset.sum_congr rfl
      intro c hc
      exact sum_indicator_mul_eq_card_inter support b c

theorem sum_sq_incidenceDegree_le
    {Point Block : Type*}
    [Fintype Point] [DecidableEq Point] [DecidableEq Block]
    (B : Finset Block) (support : Block → Finset Point)
    (hcard : ∀ b ∈ B, (support b).card = 5)
    (hinter : ∀ b ∈ B, ∀ c ∈ B, b ≠ c →
      (support b ∩ support c).card ≤ 2) :
    (∑ x : Point, (incidenceDegree B support x) ^ 2) ≤
      2 * B.card ^ 2 + 3 * B.card := by
  rw [sum_sq_incidenceDegree]
  calc
    (∑ b ∈ B, ∑ c ∈ B, (support b ∩ support c).card) ≤
        ∑ b ∈ B, ∑ c ∈ B, (2 + if b = c then 3 else 0) := by
      apply Finset.sum_le_sum
      intro b hb
      apply Finset.sum_le_sum
      intro c hc
      by_cases hbc : b = c
      · subst c
        simp [hcard b hb]
      · simp [hbc, hinter b hb c hc hbc]
    _ = 2 * B.card ^ 2 + 3 * B.card := by
      simp [Finset.sum_add_distrib]
      ring

/-- The combinatorial `q ≤ 6` half of the six-five-circle wall. -/
theorem card_le_six_of_five_subsets_card_ten_inter_le_two
    {Point Block : Type*}
    [Fintype Point] [DecidableEq Point] [DecidableEq Block]
    (B : Finset Block) (support : Block → Finset Point)
    (hPoint : Fintype.card Point = 10)
    (hcard : ∀ b ∈ B, (support b).card = 5)
    (hinter : ∀ b ∈ B, ∀ c ∈ B, b ≠ c →
      (support b ∩ support c).card ≤ 2) :
    B.card ≤ 6 := by
  have hfirst := sum_incidenceDegree B support
  have hfirst' : (∑ x : Point, incidenceDegree B support x) = 5 * B.card := by
    rw [hfirst]
    calc
      (∑ b ∈ B, (support b).card) = ∑ _b ∈ B, 5 := by
        apply Finset.sum_congr rfl
        intro b hb
        exact hcard b hb
      _ = 5 * B.card := by simp [Nat.mul_comm]
  have hcauchy := sq_sum_le_card_mul_sum_sq
    (s := (Finset.univ : Finset Point))
    (f := fun x => incidenceDegree B support x)
  have hsquares := sum_sq_incidenceDegree_le B support hcard hinter
  simp only [Finset.card_univ] at hcauchy
  rw [hfirst', hPoint] at hcauchy
  have hbound : (5 * B.card) ^ 2 ≤
      10 * (2 * B.card ^ 2 + 3 * B.card) :=
    hcauchy.trans (Nat.mul_le_mul_left 10 hsquares)
  nlinarith

theorem incidence_moments_of_six_five_subsets_card_ten_inter_le_two
    {Point Block : Type*}
    [Fintype Point] [DecidableEq Point] [DecidableEq Block]
    (B : Finset Block) (support : Block → Finset Point)
    (hPoint : Fintype.card Point = 10) (hB : B.card = 6)
    (hcard : ∀ b ∈ B, (support b).card = 5)
    (hinter : ∀ b ∈ B, ∀ c ∈ B, b ≠ c →
      (support b ∩ support c).card ≤ 2) :
    (∑ x : Point, incidenceDegree B support x) = 30 ∧
      (∑ x : Point, (incidenceDegree B support x) ^ 2) = 90 := by
  have hfirst := sum_incidenceDegree B support
  have hfirst' : (∑ x : Point, incidenceDegree B support x) = 30 := by
    rw [hfirst]
    calc
      (∑ b ∈ B, (support b).card) = ∑ _b ∈ B, 5 := by
        apply Finset.sum_congr rfl
        intro b hb
        exact hcard b hb
      _ = 30 := by simp [hB]
  have hcauchy := sq_sum_le_card_mul_sum_sq
    (s := (Finset.univ : Finset Point))
    (f := fun x => incidenceDegree B support x)
  simp only [Finset.card_univ] at hcauchy
  rw [hfirst', hPoint] at hcauchy
  have hupper := sum_sq_incidenceDegree_le B support hcard hinter
  rw [hB] at hupper
  norm_num at hupper
  constructor
  · exact hfirst'
  · omega

theorem incidenceDegree_eq_three_of_six_five_subsets_card_ten_inter_le_two
    {Point Block : Type*}
    [Fintype Point] [DecidableEq Point] [DecidableEq Block]
    (B : Finset Block) (support : Block → Finset Point)
    (hPoint : Fintype.card Point = 10) (hB : B.card = 6)
    (hcard : ∀ b ∈ B, (support b).card = 5)
    (hinter : ∀ b ∈ B, ∀ c ∈ B, b ≠ c →
      (support b ∩ support c).card ≤ 2) :
    ∀ x : Point, incidenceDegree B support x = 3 := by
  obtain ⟨hfirst, hsecond⟩ :=
    incidence_moments_of_six_five_subsets_card_ten_inter_le_two
      B support hPoint hB hcard hinter
  have hfirstZ : (∑ x : Point, (incidenceDegree B support x : ℤ)) = 30 := by
    exact_mod_cast hfirst
  have hsecondZ :
      (∑ x : Point, (incidenceDegree B support x : ℤ) ^ 2) = 90 := by
    exact_mod_cast hsecond
  have hvariance :
      (∑ x : Point, ((incidenceDegree B support x : ℤ) - 3) ^ 2) = 0 := by
    calc
      (∑ x : Point, ((incidenceDegree B support x : ℤ) - 3) ^ 2) =
          (∑ x : Point, (incidenceDegree B support x : ℤ) ^ 2) -
            6 * (∑ x : Point, (incidenceDegree B support x : ℤ)) +
              9 * Fintype.card Point := by
        simp_rw [show ∀ z : ℤ, (z - 3) ^ 2 = z ^ 2 - 6 * z + 9 by
          intro z
          ring]
        simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib,
          Finset.mul_sum, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        ring
      _ = 0 := by rw [hfirstZ, hsecondZ, hPoint]; norm_num
  intro x
  have hterm : ((incidenceDegree B support x : ℤ) - 3) ^ 2 = 0 := by
    have hall := (Finset.sum_eq_zero_iff_of_nonneg
      (fun i (_hi : i ∈ (Finset.univ : Finset Point)) =>
        sq_nonneg ((incidenceDegree B support i : ℤ) - 3))).mp hvariance
    exact hall x (Finset.mem_univ x)
  have hdegreeZ : (incidenceDegree B support x : ℤ) = 3 := by
    nlinarith
  exact_mod_cast hdegreeZ

theorem inter_eq_two_of_six_five_subsets_card_ten_inter_le_two
    {Point Block : Type*}
    [Fintype Point] [DecidableEq Point] [DecidableEq Block]
    (B : Finset Block) (support : Block → Finset Point)
    (hPoint : Fintype.card Point = 10) (hB : B.card = 6)
    (hcard : ∀ b ∈ B, (support b).card = 5)
    (hinter : ∀ b ∈ B, ∀ c ∈ B, b ≠ c →
      (support b ∩ support c).card ≤ 2) :
    ∀ b ∈ B, ∀ c ∈ B, b ≠ c → (support b ∩ support c).card = 2 := by
  obtain ⟨_hfirst, hsecond⟩ :=
    incidence_moments_of_six_five_subsets_card_ten_inter_le_two
      B support hPoint hB hcard hinter
  have hleft :
      (∑ b ∈ B, ∑ c ∈ B, (support b ∩ support c).card) = 90 := by
    rw [← sum_sq_incidenceDegree]
    exact hsecond
  have hright :
      (∑ b ∈ B, ∑ c ∈ B, (2 + if b = c then 3 else 0)) = 90 := by
    simp [Finset.sum_add_distrib, hB]
  have htotal :
      (∑ b ∈ B, ∑ c ∈ B, (support b ∩ support c).card) =
        ∑ b ∈ B, ∑ c ∈ B, (2 + if b = c then 3 else 0) :=
    hleft.trans hright.symm
  have houterLe : ∀ b ∈ B,
      (∑ c ∈ B, (support b ∩ support c).card) ≤
        ∑ c ∈ B, (2 + if b = c then 3 else 0) := by
    intro b hb
    apply Finset.sum_le_sum
    intro c hc
    by_cases hbc : b = c
    · subst c
      simp [hcard b hb]
    · simp [hbc, hinter b hb c hc hbc]
  intro b hb c hc hbc
  have hbEq := (Finset.sum_eq_sum_iff_of_le houterLe).mp htotal b hb
  have hinnerLe : ∀ d ∈ B,
      (support b ∩ support d).card ≤ (2 + if b = d then 3 else 0) := by
    intro d hd
    by_cases hbd : b = d
    · subst d
      simp [hcard b hb]
    · simp [hbd, hinter b hb d hd hbd]
  have hterm := (Finset.sum_eq_sum_iff_of_le hinnerLe).mp hbEq c hc
  simpa [hbc] using hterm

end Erdos506.Finite
