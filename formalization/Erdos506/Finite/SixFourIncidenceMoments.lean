import Erdos506.Finite.IncidenceMoments
import Mathlib.Tactic

/-!
# The `6` four-subset incidence wall on eleven points

Six four-subsets of an eleven-point set which meet pairwise in at most one
point are automatically tight: every pair meets once, and the point degrees
are `3,3,2,2,2,2,2,2,2,2,2`.  No coverage hypothesis is required; the
degree conclusion itself proves coverage.
-/

namespace Erdos506.Finite

open scoped BigOperators

/-- Incidence degree in a six-indexed family of supports. -/
noncomputable def sixFourDegree {Point : Type*} [DecidableEq Point]
    (B : Fin 6 -> Finset Point) (x : Point) : Nat :=
  ((Finset.univ : Finset (Fin 6)).filter fun i => x ∈ B i).card

/-- The two degree-three points in the saturated six-four profile. -/
noncomputable def sixFourDegreeThree {Point : Type*} [Fintype Point]
    [DecidableEq Point] (B : Fin 6 -> Finset Point) : Finset Point :=
  (Finset.univ : Finset Point).filter fun x => sixFourDegree B x = 3

/-- The remaining nine degree-two points in the saturated six-four profile. -/
noncomputable def sixFourDegreeTwo {Point : Type*} [Fintype Point]
    [DecidableEq Point] (B : Fin 6 -> Finset Point) : Finset Point :=
  (Finset.univ : Finset Point).filter fun x => sixFourDegree B x = 2

/-- Precisely the assumptions needed for the six-four moment argument. -/
structure IsSaturatedSixFour {Point : Type*} [Fintype Point] [DecidableEq Point]
    (B : Fin 6 -> Finset Point) : Prop where
  point_card : Fintype.card Point = 11
  base_card : ∀ i, (B i).card = 4
  pair_inter_le_one : ∀ i j, i ≠ j -> (B i ∩ B j).card ≤ 1

/-- The abstract incidence degree is the concrete six-indexed degree. -/
theorem incidenceDegree_univ_eq_sixFourDegree
    {Point : Type*} [Fintype Point] [DecidableEq Point]
    (B : Fin 6 -> Finset Point) (x : Point) :
    incidenceDegree (Finset.univ : Finset (Fin 6)) B x = sixFourDegree B x := by
  classical
  simp [incidenceDegree, incidenceIndicator, sixFourDegree]

private theorem two_mul_choose_two (n : Nat) :
    2 * Nat.choose n 2 = n * (n - 1) := by
  have h := Nat.choose_succ_right_eq n 1
  simpa [Nat.choose_one_right, Nat.mul_comm] using h

/-- The pointwise inequality whose sum gives the lower second-moment bound. -/
private theorem twice_le_choose_add_three (n : Nat) :
    2 * n ≤ Nat.choose n 2 + 3 := by
  by_cases hn : n ≤ 3
  · interval_cases n <;> norm_num [Nat.choose]
  · have hn4 : 4 ≤ n := by omega
    have hsub : n - 1 + 1 = n := by omega
    have hchoose := two_mul_choose_two n
    nlinarith

/-- The explicit diagonal/off-diagonal total for six indices. -/
private theorem sixFour_diagonal_offDiagonal_sum :
    (∑ i : Fin 6, ∑ j : Fin 6, (1 + if i = j then 3 else 0)) = 54 := by
  classical
  calc
    (∑ i : Fin 6, ∑ j : Fin 6, (1 + if i = j then 3 else 0)) =
        ∑ i : Fin 6, 9 := by
      apply Finset.sum_congr rfl
      intro i _hi
      fin_cases i <;> decide
    _ = 54 := by norm_num

/-- First incidence moment: six four-subsets have twenty-four incidences. -/
theorem sixFour_degree_sum_eq_twenty_four
    {Point : Type*} [Fintype Point] [DecidableEq Point]
    {B : Fin 6 -> Finset Point} (H : IsSaturatedSixFour B) :
    (∑ x : Point, sixFourDegree B x) = 24 := by
  calc
    (∑ x : Point, sixFourDegree B x) =
        ∑ x : Point, incidenceDegree (Finset.univ : Finset (Fin 6)) B x := by
          apply Finset.sum_congr rfl
          intro x _hx
          exact (incidenceDegree_univ_eq_sixFourDegree B x).symm
    _ = ∑ i ∈ (Finset.univ : Finset (Fin 6)), (B i).card :=
      sum_incidenceDegree (Finset.univ : Finset (Fin 6)) B
    _ = ∑ _i ∈ (Finset.univ : Finset (Fin 6)), 4 := by
      apply Finset.sum_congr rfl
      intro i _hi
      exact H.base_card i
    _ = 24 := by norm_num

/-- The off-diagonal intersection budget is at most the fifteen pairs of
the six supports. -/
private theorem sixFour_square_degree_sum_le_fifty_four
    {Point : Type*} [Fintype Point] [DecidableEq Point]
    {B : Fin 6 -> Finset Point} (H : IsSaturatedSixFour B) :
    (∑ x : Point, (sixFourDegree B x) ^ 2) ≤ 54 := by
  calc
    (∑ x : Point, (sixFourDegree B x) ^ 2) =
        ∑ x : Point,
          (incidenceDegree (Finset.univ : Finset (Fin 6)) B x) ^ 2 := by
          apply Finset.sum_congr rfl
          intro x _hx
          rw [incidenceDegree_univ_eq_sixFourDegree]
    _ = ∑ i ∈ (Finset.univ : Finset (Fin 6)),
          ∑ j ∈ (Finset.univ : Finset (Fin 6)), (B i ∩ B j).card :=
      sum_sq_incidenceDegree (Finset.univ : Finset (Fin 6)) B
    _ ≤ ∑ i ∈ (Finset.univ : Finset (Fin 6)),
          ∑ j ∈ (Finset.univ : Finset (Fin 6)), (1 + if i = j then 3 else 0) := by
      apply Finset.sum_le_sum
      intro i _hi
      apply Finset.sum_le_sum
      intro j _hj
      by_cases hij : i = j
      · subst j
        simp [H.base_card]
      · simp [hij, H.pair_inter_le_one i j hij]
    _ = 54 := by
      simpa only using sixFour_diagonal_offDiagonal_sum

/-- The first moment on eleven points forces the complementary lower second
moment.  The proof uses the elementary convex inequality for `choose n 2`;
it does not assume that the six supports cover the point type. -/
private theorem sixFour_square_degree_sum_ge_fifty_four
    {Point : Type*} [Fintype Point] [DecidableEq Point]
    {B : Fin 6 -> Finset Point} (H : IsSaturatedSixFour B) :
    54 ≤ (∑ x : Point, (sixFourDegree B x) ^ 2) := by
  have hfirst := sixFour_degree_sum_eq_twenty_four H
  have hpointwise (x : Point) :
      5 * sixFourDegree B x ≤ (sixFourDegree B x) ^ 2 + 6 := by
    by_cases hx : sixFourDegree B x ≤ 3
    · interval_cases hdegree : sixFourDegree B x <;> norm_num [hdegree]
    · have hfour : 4 ≤ sixFourDegree B x := by omega
      nlinarith
  have hsum : (∑ x : Point, 5 * sixFourDegree B x) ≤
      ∑ x : Point, ((sixFourDegree B x) ^ 2 + 6) :=
    Finset.sum_le_sum (s := Finset.univ) (fun x _hx => hpointwise x)
  have hleft : (∑ x : Point, 5 * sixFourDegree B x) = 120 := by
    rw [← Finset.mul_sum, hfirst]
    norm_num
  have hright : (∑ x : Point, ((sixFourDegree B x) ^ 2 + 6)) =
      (∑ x : Point, (sixFourDegree B x) ^ 2) + 66 := by
    rw [Finset.sum_add_distrib]
    simp [H.point_card]
  rw [hleft, hright] at hsum
  omega

/-- Exact second moment of the saturated six-four family. -/
theorem sixFour_square_degree_sum_eq_fifty_four
    {Point : Type*} [Fintype Point] [DecidableEq Point]
    {B : Fin 6 -> Finset Point} (H : IsSaturatedSixFour B) :
    (∑ x : Point, (sixFourDegree B x) ^ 2) = 54 := by
  have hupper := sixFour_square_degree_sum_le_fifty_four H
  have hlower := sixFour_square_degree_sum_ge_fifty_four H
  omega

/-- The pair-intersection moment is fifteen. -/
theorem sixFour_choose_degree_sum_eq_fifteen
    {Point : Type*} [Fintype Point] [DecidableEq Point]
    {B : Fin 6 -> Finset Point} (H : IsSaturatedSixFour B) :
    (∑ x : Point, Nat.choose (sixFourDegree B x) 2) = 15 := by
  have hfirst := sixFour_degree_sum_eq_twenty_four H
  have hsecond := sixFour_square_degree_sum_eq_fifty_four H
  have hchooseSquare (x : Point) :
      (sixFourDegree B x) ^ 2 =
        sixFourDegree B x + 2 * Nat.choose (sixFourDegree B x) 2 := by
    by_cases hzero : sixFourDegree B x = 0
    · simp [hzero]
    · have hsub : sixFourDegree B x - 1 + 1 = sixFourDegree B x := by
        omega
      have hchoose := two_mul_choose_two (sixFourDegree B x)
      calc
        (sixFourDegree B x) ^ 2 = sixFourDegree B x * sixFourDegree B x := by
          ring
        _ = sixFourDegree B x * (sixFourDegree B x - 1 + 1) := by rw [hsub]
        _ = sixFourDegree B x * (sixFourDegree B x - 1) + sixFourDegree B x := by
          ring
        _ = sixFourDegree B x + 2 * Nat.choose (sixFourDegree B x) 2 := by
          omega
  have hidentity :
      (∑ x : Point, (sixFourDegree B x) ^ 2) =
        (∑ x : Point, sixFourDegree B x) +
          2 * (∑ x : Point, Nat.choose (sixFourDegree B x) 2) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro x _hx
    exact hchooseSquare x
  omega

/-- Tightness makes every one of the fifteen pairs of four-subsets meet. -/
theorem sixFour_pair_inter_eq_one
    {Point : Type*} [Fintype Point] [DecidableEq Point]
    {B : Fin 6 -> Finset Point} (H : IsSaturatedSixFour B) :
    ∀ i j, i ≠ j -> (B i ∩ B j).card = 1 := by
  have hsecond := sixFour_square_degree_sum_eq_fifty_four H
  have hleft :
      (∑ i ∈ (Finset.univ : Finset (Fin 6)),
        ∑ j ∈ (Finset.univ : Finset (Fin 6)), (B i ∩ B j).card) = 54 := by
    calc
      _ = ∑ x : Point,
          (incidenceDegree (Finset.univ : Finset (Fin 6)) B x) ^ 2 := by
            symm
            exact sum_sq_incidenceDegree (Finset.univ : Finset (Fin 6)) B
      _ = ∑ x : Point, (sixFourDegree B x) ^ 2 := by
            apply Finset.sum_congr rfl
            intro x _hx
            rw [incidenceDegree_univ_eq_sixFourDegree]
      _ = 54 := hsecond
  have hright :
      (∑ i ∈ (Finset.univ : Finset (Fin 6)),
        ∑ j ∈ (Finset.univ : Finset (Fin 6)), (1 + if i = j then 3 else 0)) = 54 := by
    simpa only using sixFour_diagonal_offDiagonal_sum
  have htotal :
      (∑ i ∈ (Finset.univ : Finset (Fin 6)),
        ∑ j ∈ (Finset.univ : Finset (Fin 6)), (B i ∩ B j).card) =
      ∑ i ∈ (Finset.univ : Finset (Fin 6)),
        ∑ j ∈ (Finset.univ : Finset (Fin 6)), (1 + if i = j then 3 else 0) :=
    hleft.trans hright.symm
  have houterLe : ∀ i ∈ (Finset.univ : Finset (Fin 6)),
      (∑ j ∈ (Finset.univ : Finset (Fin 6)), (B i ∩ B j).card) ≤
        ∑ j ∈ (Finset.univ : Finset (Fin 6)), (1 + if i = j then 3 else 0) := by
    intro i hi
    apply Finset.sum_le_sum
    intro j hj
    by_cases hij : i = j
    · subst j
      simp [H.base_card]
    · simp [hij, H.pair_inter_le_one i j hij]
  intro i j hij
  have hiEq := (Finset.sum_eq_sum_iff_of_le houterLe).mp htotal i (Finset.mem_univ i)
  have hinnerLe : ∀ k ∈ (Finset.univ : Finset (Fin 6)),
      (B i ∩ B k).card ≤ (1 + if i = k then 3 else 0) := by
    intro k hk
    by_cases hik : i = k
    · subst k
      simp [H.base_card]
    · simp [hik, H.pair_inter_le_one i k hik]
  have hterm := (Finset.sum_eq_sum_iff_of_le hinnerLe).mp hiEq j (Finset.mem_univ j)
  simpa [hij] using hterm

/-- Pointwise degree restriction forced by the two exact moments. -/
theorem sixFour_degree_eq_two_or_three
    {Point : Type*} [Fintype Point] [DecidableEq Point]
    {B : Fin 6 -> Finset Point} (H : IsSaturatedSixFour B) (x : Point) :
    sixFourDegree B x = 2 ∨ sixFourDegree B x = 3 := by
  have hfirst := sixFour_degree_sum_eq_twenty_four H
  have hsecond := sixFour_square_degree_sum_eq_fifty_four H
  have hvariance :
      (∑ y : Point, ((sixFourDegree B y : Int) - 2) *
        ((sixFourDegree B y : Int) - 3)) = 0 := by
    calc
      (∑ y : Point, ((sixFourDegree B y : Int) - 2) *
          ((sixFourDegree B y : Int) - 3)) =
          (∑ y : Point, (sixFourDegree B y : Int) ^ 2) -
            5 * (∑ y : Point, (sixFourDegree B y : Int)) +
              6 * Fintype.card Point := by
        simp_rw [show ∀ z : Int, (z - 2) * (z - 3) = z ^ 2 - 5 * z + 6 by
          intro z
          ring]
        simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib,
          Finset.mul_sum, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        ring
      _ = 0 := by
        norm_num [show (∑ y : Point, (sixFourDegree B y : Int)) = 24 by
          exact_mod_cast hfirst,
          show (∑ y : Point, (sixFourDegree B y : Int) ^ 2) = 54 by
            exact_mod_cast hsecond,
          H.point_card]
  have hnonneg (y : Point) : 0 ≤ ((sixFourDegree B y : Int) - 2) *
      ((sixFourDegree B y : Int) - 3) := by
    by_cases hy : sixFourDegree B y ≤ 2
    · interval_cases hdegree : sixFourDegree B y <;> norm_num [hdegree]
    · have hythree : 3 ≤ sixFourDegree B y := by omega
      have hythreeZ : (3 : Int) ≤ sixFourDegree B y := by exact_mod_cast hythree
      nlinarith
  have hterm : ((sixFourDegree B x : Int) - 2) *
      ((sixFourDegree B x : Int) - 3) = 0 := by
    have hall := (Finset.sum_eq_zero_iff_of_nonneg
      (fun y (_hy : y ∈ (Finset.univ : Finset Point)) => hnonneg y)).mp hvariance
    exact hall x (Finset.mem_univ x)
  have hxnonneg : (0 : Int) ≤ sixFourDegree B x := by exact_mod_cast Nat.zero_le _
  have hx : (sixFourDegree B x : Int) = 2 ∨ (sixFourDegree B x : Int) = 3 := by
    rcases mul_eq_zero.mp hterm with htwo | hthree <;> omega
  exact_mod_cast hx

/-- The full `3,3,2^9` profile, recorded as degree classes. -/
theorem sixFour_degree_profile
    {Point : Type*} [Fintype Point] [DecidableEq Point]
    {B : Fin 6 -> Finset Point} (H : IsSaturatedSixFour B) :
    (sixFourDegreeThree B).card = 2 ∧ (sixFourDegreeTwo B).card = 9 ∧
      ∀ x : Point, sixFourDegree B x = 2 ∨ sixFourDegree B x = 3 := by
  have hfirst := sixFour_degree_sum_eq_twenty_four H
  have hpoint (x : Point) := sixFour_degree_eq_two_or_three H x
  let T := sixFourDegreeThree B
  have hrewrite (x : Point) : sixFourDegree B x =
      2 + if sixFourDegree B x = 3 then 1 else 0 := by
    rcases hpoint x with hx | hx <;> simp [hx]
  have hT : T.card = 2 := by
    have hsum : (∑ x : Point, sixFourDegree B x) =
        ∑ x : Point, (2 + if sixFourDegree B x = 3 then 1 else 0) := by
      apply Finset.sum_congr rfl
      intro x _hx
      exact hrewrite x
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul] at hsum
    have hfilter : (∑ x : Point, if sixFourDegree B x = 3 then 1 else 0) = T.card := by
      change (∑ x ∈ (Finset.univ : Finset Point),
        if sixFourDegree B x = 3 then 1 else 0) =
          ((Finset.univ : Finset Point).filter fun x => sixFourDegree B x = 3).card
      rw [Finset.card_eq_sum_ones, Finset.sum_filter]
    rw [hfilter, hfirst, H.point_card] at hsum
    norm_num at hsum
    omega
  have htwo : (sixFourDegreeTwo B).card = 9 := by
    have hcomp : sixFourDegreeTwo B = (Finset.univ : Finset Point) \ T := by
      ext x
      simp only [sixFourDegreeTwo, T, sixFourDegreeThree,
        Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_sdiff]
      rcases hpoint x with hx | hx <;> simp [hx]
    calc
      (sixFourDegreeTwo B).card = ((Finset.univ : Finset Point) \ T).card :=
        congrArg Finset.card hcomp
      _ = (Finset.univ : Finset Point).card - T.card :=
        Finset.card_sdiff_of_subset (Finset.subset_univ T)
      _ = 9 := by rw [Finset.card_univ, H.point_card, hT]
  exact ⟨by simpa [T] using hT, htwo, hpoint⟩

end Erdos506.Finite
