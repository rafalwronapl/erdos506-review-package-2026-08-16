import Erdos506.Finite.IncidenceMoments
import Mathlib.Data.Finset.Powerset
import Mathlib.Tactic

/-!
# Degree profile of a saturated four-star

This file is deliberately geometry-free.  Its intended input is four
four-subsets of a ten-point universe, with every pair meeting once.  The
relevant numerical identity is

`sum_x (d_x - 1) * (d_x - 2) = 0`.

Together with coverage, this forces every degree to be one or two; the two
incidence moments then give the `2^6 1^4` profile.  The final per-base
private-point statement needs, in addition, the elementary fact that the
three pair intersections on one base are distinct.
-/

namespace Erdos506.Finite

open scoped BigOperators

/-- Incidence degree of a point in a four-indexed family. -/
noncomputable def fourStarDegree {Point : Type*} [DecidableEq Point]
    (B : Fin 4 → Finset Point) (x : Point) : ℕ :=
  ((Finset.univ : Finset (Fin 4)).filter fun i => x ∈ B i).card

/-- The union of the four supports. -/
noncomputable def fourStarCarrier {Point : Type*} [DecidableEq Point]
    (B : Fin 4 → Finset Point) : Finset Point :=
  (Finset.univ : Finset (Fin 4)).biUnion B

/-- The explicit four-term presentation of the carrier. -/
def fourStarCarrierUnion {Point : Type*} [DecidableEq Point]
    (B : Fin 4 → Finset Point) : Finset Point :=
  B 0 ∪ B 1 ∪ B 2 ∪ B 3

theorem fourStarCarrier_eq_union {Point : Type*} [DecidableEq Point]
    (B : Fin 4 → Finset Point) : fourStarCarrier B = fourStarCarrierUnion B := by
  classical
  ext x
  simp only [fourStarCarrier, fourStarCarrierUnion, Finset.mem_biUnion,
    Finset.mem_univ, Finset.mem_union]
  constructor
  · rintro ⟨i, _hi, hxi⟩
    fin_cases i <;> simp_all
  · intro hx
    rcases hx with hx | hx
    · rcases hx with hx | hx
      · rcases hx with hx | hx
        · exact ⟨0, trivial, hx⟩
        · exact ⟨1, trivial, hx⟩
      · exact ⟨2, trivial, hx⟩
    · exact ⟨3, trivial, hx⟩

/-- Degree-one points in the carrier. -/
noncomputable def fourStarDegreeOne {Point : Type*} [DecidableEq Point]
    (B : Fin 4 → Finset Point) : Finset Point :=
  (fourStarCarrier B).filter fun x => fourStarDegree B x = 1

/-- Degree-two points in the carrier. -/
noncomputable def fourStarDegreeTwo {Point : Type*} [DecidableEq Point]
    (B : Fin 4 → Finset Point) : Finset Point :=
  (fourStarCarrier B).filter fun x => fourStarDegree B x = 2

/-- The degree-one points on a specified base support. -/
noncomputable def fourStarDegreeOneOnBase {Point : Type*} [DecidableEq Point]
    (B : Fin 4 → Finset Point) (i : Fin 4) : Finset Point :=
  B i ∩ fourStarDegreeOne B

/-- The neutral `2^6 1^4` conclusion. -/
structure IsFourStarDegreeProfile {Point : Type*} [DecidableEq Point]
    (B : Fin 4 → Finset Point) : Prop where
  carrier_card : (fourStarCarrier B).card = 10
  degree_one_or_two : ∀ x, x ∈ fourStarCarrier B →
    fourStarDegree B x = 1 ∨ fourStarDegree B x = 2
  degree_one_card : (fourStarDegreeOne B).card = 4
  degree_two_card : (fourStarDegreeTwo B).card = 6
  one_on_each_base : ∀ i, (fourStarDegreeOneOnBase B i).card = 1

/-- The moment hypotheses in a form independent of projective geometry. -/
structure IsSaturatedFourStar {Point : Type*} [Fintype Point] [DecidableEq Point]
    (B : Fin 4 → Finset Point) : Prop where
  point_card : Fintype.card Point = 10
  base_card : ∀ i, (B i).card = 4
  pair_inter_one : ∀ i j, i ≠ j → (B i ∩ B j).card = 1
  carrier_card : (fourStarCarrier B).card = 10

/-- The common `IncidenceMoments` degree specializes to the direct four-star
degree definition. -/
theorem incidenceDegree_univ_eq_fourStarDegree
    {Point : Type*} [Fintype Point] [DecidableEq Point]
    (B : Fin 4 → Finset Point) (x : Point) :
    incidenceDegree (Finset.univ : Finset (Fin 4)) B x = fourStarDegree B x := by
  classical
  simp [incidenceDegree, incidenceIndicator, fourStarDegree]

/-- First incidence moment of a saturated four-star. -/
theorem fourStar_degree_sum_eq_sixteen
    {Point : Type*} [Fintype Point] [DecidableEq Point]
    {B : Fin 4 → Finset Point} (H : IsSaturatedFourStar B) :
    (∑ x : Point, fourStarDegree B x) = 16 := by
  calc
    (∑ x : Point, fourStarDegree B x) =
        ∑ x : Point, incidenceDegree (Finset.univ : Finset (Fin 4)) B x := by
          apply Finset.sum_congr rfl
          intro x _hx
          exact (incidenceDegree_univ_eq_fourStarDegree B x).symm
    _ = ∑ i ∈ (Finset.univ : Finset (Fin 4)), (B i).card :=
      sum_incidenceDegree (Finset.univ : Finset (Fin 4)) B
    _ = ∑ _i ∈ (Finset.univ : Finset (Fin 4)), 4 := by
      apply Finset.sum_congr rfl
      intro i _hi
      exact H.base_card i
    _ = 16 := by norm_num

/-- For one fixed base, the diagonal contributes four and the three
off-diagonal intersections contribute one each. -/
theorem fourStar_inter_sum_eq_seven
    {Point : Type*} [Fintype Point] [DecidableEq Point]
    {B : Fin 4 → Finset Point} (H : IsSaturatedFourStar B) (i : Fin 4) :
    (∑ j : Fin 4, (B i ∩ B j).card) = 7 := by
  have hsplit := Finset.sum_erase_add (Finset.univ : Finset (Fin 4))
    (fun j => (B i ∩ B j).card) (Finset.mem_univ i)
  have herase :
      (∑ j ∈ (Finset.univ.erase i : Finset (Fin 4)), (B i ∩ B j).card) = 3 := by
    calc
      (∑ j ∈ (Finset.univ.erase i : Finset (Fin 4)), (B i ∩ B j).card) =
          ∑ _j ∈ (Finset.univ.erase i : Finset (Fin 4)), 1 := by
            apply Finset.sum_congr rfl
            intro j hj
            exact H.pair_inter_one i j (Finset.mem_erase.mp hj).1.symm
      _ = 3 := by simp
  have hdiag : (B i ∩ B i).card = 4 := by simpa using H.base_card i
  change (∑ j ∈ (Finset.univ : Finset (Fin 4)), (B i ∩ B j).card) = 7
  rw [← hsplit, herase]
  change 3 + (B i ∩ B i).card = 7
  rw [hdiag]

/-- Second incidence moment of a saturated four-star. -/
theorem fourStar_degree_sq_sum_eq_twenty_eight
    {Point : Type*} [Fintype Point] [DecidableEq Point]
    {B : Fin 4 → Finset Point} (H : IsSaturatedFourStar B) :
    (∑ x : Point, fourStarDegree B x ^ 2) = 28 := by
  calc
    (∑ x : Point, fourStarDegree B x ^ 2) =
        ∑ x : Point, (incidenceDegree (Finset.univ : Finset (Fin 4)) B x) ^ 2 := by
          apply Finset.sum_congr rfl
          intro x _hx
          rw [incidenceDegree_univ_eq_fourStarDegree]
    _ = ∑ i ∈ (Finset.univ : Finset (Fin 4)),
          ∑ j ∈ (Finset.univ : Finset (Fin 4)), (B i ∩ B j).card :=
      sum_sq_incidenceDegree (Finset.univ : Finset (Fin 4)) B
    _ = ∑ i : Fin 4, 7 := by
      apply Finset.sum_congr rfl
      intro i _hi
      exact fourStar_inter_sum_eq_seven H i
    _ = 28 := by norm_num

/-- Saturation means the four-star carrier is the whole ten-point universe. -/
theorem fourStarCarrier_eq_univ
    {Point : Type*} [Fintype Point] [DecidableEq Point]
    {B : Fin 4 → Finset Point} (H : IsSaturatedFourStar B) :
    fourStarCarrier B = Finset.univ := by
  apply Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
  simpa [H.point_card] using H.carrier_card.ge

/-- Every point in a saturated four-star has positive degree. -/
theorem fourStarDegree_pos
    {Point : Type*} [Fintype Point] [DecidableEq Point]
    {B : Fin 4 → Finset Point} (H : IsSaturatedFourStar B) (x : Point) :
    0 < fourStarDegree B x := by
  have hxcarrier : x ∈ fourStarCarrier B := by
    rw [fourStarCarrier_eq_univ H]
    simp
  rcases Finset.mem_biUnion.mp hxcarrier with ⟨i, _hi, hxi⟩
  apply Finset.card_pos.mpr
  refine ⟨i, ?_⟩
  simp [hxi]

/-- The two saturated moments force every point degree to be one or two.
The proof is the nonnegative integer identity
`(d - 1) * (d - 2)`, summed over the ten-point carrier. -/
theorem fourStarDegree_eq_one_or_two
    {Point : Type*} [Fintype Point] [DecidableEq Point]
    {B : Fin 4 → Finset Point} (H : IsSaturatedFourStar B) (x : Point) :
    fourStarDegree B x = 1 ∨ fourStarDegree B x = 2 := by
  have hsum := fourStar_degree_sum_eq_sixteen H
  have hsq := fourStar_degree_sq_sum_eq_twenty_eight H
  have hsumZ : (∑ y : Point, (fourStarDegree B y : ℤ)) = 16 := by
    exact_mod_cast hsum
  have hsqZ : (∑ y : Point, (fourStarDegree B y : ℤ) ^ 2) = 28 := by
    exact_mod_cast hsq
  have hterm_nonneg (y : Point) :
      0 ≤ ((fourStarDegree B y : ℤ) - 1) * ((fourStarDegree B y : ℤ) - 2) := by
    have hypos : 0 < fourStarDegree B y := fourStarDegree_pos H y
    by_cases hyone : fourStarDegree B y = 1
    · simp [hyone]
    · have hytwo : 2 ≤ fourStarDegree B y := by omega
      have hytwoZ : (2 : ℤ) ≤ (fourStarDegree B y : ℤ) := by
        exact_mod_cast hytwo
      apply mul_nonneg <;> omega
  have hvariance :
      (∑ y : Point,
        ((fourStarDegree B y : ℤ) - 1) * ((fourStarDegree B y : ℤ) - 2)) = 0 := by
    calc
      (∑ y : Point,
          ((fourStarDegree B y : ℤ) - 1) * ((fourStarDegree B y : ℤ) - 2)) =
          (∑ y : Point, (fourStarDegree B y : ℤ) ^ 2) -
            3 * (∑ y : Point, (fourStarDegree B y : ℤ)) +
              2 * Fintype.card Point := by
            simp_rw [show ∀ z : ℤ, (z - 1) * (z - 2) = z ^ 2 - 3 * z + 2 by
              intro z
              ring]
            simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib,
              Finset.mul_sum, Finset.sum_const, Finset.card_univ,
              nsmul_eq_mul]
            ring
      _ = 0 := by rw [hsqZ, hsumZ, H.point_card]; norm_num
  have hterm :
      ((fourStarDegree B x : ℤ) - 1) * ((fourStarDegree B x : ℤ) - 2) = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg
      (fun y (_hy : y ∈ (Finset.univ : Finset Point)) => hterm_nonneg y)).mp
        hvariance x (Finset.mem_univ x)
  have hdegreeZ : (fourStarDegree B x : ℤ) = 1 ∨
      (fourStarDegree B x : ℤ) = 2 := by
    rw [mul_eq_zero] at hterm
    omega
  exact_mod_cast hdegreeZ

/-- The degree-one layer contains exactly four points. -/
theorem fourStar_degreeOne_card_eq_four
    {Point : Type*} [Fintype Point] [DecidableEq Point]
    {B : Fin 4 → Finset Point} (H : IsSaturatedFourStar B) :
    (fourStarDegreeOne B).card = 4 := by
  classical
  let D : Finset Point := (Finset.univ : Finset Point).filter fun x =>
    fourStarDegree B x = 1
  have hcarrier : fourStarCarrier B = Finset.univ := fourStarCarrier_eq_univ H
  have hD : fourStarDegreeOne B = D := by
    ext x
    simp [fourStarDegreeOne, D, hcarrier]
  have hsum := fourStar_degree_sum_eq_sixteen H
  have hsumZ : (∑ x : Point, (fourStarDegree B x : ℤ)) = 16 := by
    exact_mod_cast hsum
  have hpointwise (x : Point) : (fourStarDegree B x : ℤ) =
      2 - if fourStarDegree B x = 1 then 1 else 0 := by
    rcases fourStarDegree_eq_one_or_two H x with hx | hx <;> simp [hx]
  have hDcardZ : (D.card : ℤ) = 4 := by
    calc
      (D.card : ℤ) = ∑ x : Point,
          (if fourStarDegree B x = 1 then (1 : ℤ) else 0) := by
            simp [D, Finset.sum_boole]
      _ = ∑ x : Point, (2 - (fourStarDegree B x : ℤ)) := by
            apply Finset.sum_congr rfl
            intro x _hx
            rw [hpointwise x]
            split <;> ring
      _ = 4 := by
            rw [Finset.sum_sub_distrib, hsumZ]
            simp [H.point_card]
  rw [hD]
  exact_mod_cast hDcardZ

/-- The degree-two layer contains exactly six points. -/
theorem fourStar_degreeTwo_card_eq_six
    {Point : Type*} [Fintype Point] [DecidableEq Point]
    {B : Fin 4 → Finset Point} (H : IsSaturatedFourStar B) :
    (fourStarDegreeTwo B).card = 6 := by
  classical
  let D1 : Finset Point := (Finset.univ : Finset Point).filter fun x =>
    fourStarDegree B x = 1
  let D2 : Finset Point := (Finset.univ : Finset Point).filter fun x =>
    fourStarDegree B x = 2
  have hcarrier : fourStarCarrier B = Finset.univ := fourStarCarrier_eq_univ H
  have hD1 : fourStarDegreeOne B = D1 := by
    ext x
    simp [fourStarDegreeOne, D1, hcarrier]
  have hD2 : fourStarDegreeTwo B = D2 := by
    ext x
    simp [fourStarDegreeTwo, D2, hcarrier]
  have hpartition : D1 ∪ D2 = Finset.univ := by
    apply Finset.eq_univ_of_forall
    intro x
    rcases fourStarDegree_eq_one_or_two H x with hx | hx
    · exact Finset.mem_union_left _ (by simp [D1, hx])
    · exact Finset.mem_union_right _ (by simp [D2, hx])
  have hdisj : Disjoint D1 D2 := by
    apply Finset.disjoint_left.mpr
    intro x hx1 hx2
    have h1 : fourStarDegree B x = 1 := by simpa [D1] using hx1
    have h2 : fourStarDegree B x = 2 := by simpa [D2] using hx2
    omega
  have hD1card : D1.card = 4 := by
    rw [← hD1]
    exact fourStar_degreeOne_card_eq_four H
  have hunion := Finset.card_union_of_disjoint hdisj
  rw [hpartition, hD1card] at hunion
  change Fintype.card Point = 4 + D2.card at hunion
  rw [H.point_card] at hunion
  rw [hD2]
  omega

/-- In particular no point is incident with three base supports. -/
theorem fourStarDegree_le_two
    {Point : Type*} [Fintype Point] [DecidableEq Point]
    {B : Fin 4 → Finset Point} (H : IsSaturatedFourStar B) (x : Point) :
    fourStarDegree B x ≤ 2 := by
  rcases fourStarDegree_eq_one_or_two H x with hx | hx <;> omega

/-- Double-count base incidences restricted to an arbitrary selected set.
This is the reusable form needed when a size-three line is tested against
the four base supports. -/
theorem sum_fourStarDegree_over
    {Point : Type*} [DecidableEq Point]
    (B : Fin 4 → Finset Point) (C : Finset Point) :
    (∑ x ∈ C, fourStarDegree B x) =
      ∑ i : Fin 4, (C ∩ B i).card := by
  classical
  calc
    (∑ x ∈ C, fourStarDegree B x) =
        ∑ x ∈ C, ∑ i : Fin 4, if x ∈ B i then 1 else 0 := by
          apply Finset.sum_congr rfl
          intro x hx
          rw [fourStarDegree, Finset.card_eq_sum_ones,
            Finset.sum_filter]
    _ = ∑ i : Fin 4, ∑ x ∈ C, if x ∈ B i then 1 else 0 := by
          rw [Finset.sum_comm]
    _ = ∑ i : Fin 4, (C ∩ B i).card := by
          apply Finset.sum_congr rfl
          intro i hi
          have hfilter : C.filter (fun x => x ∈ B i) = C ∩ B i := by
            ext x
            simp
          rw [← Finset.sum_filter, ← Finset.card_eq_sum_ones, hfilter]

/-- On a set where every base degree is one or two, the deficit from degree
two is exactly the number of degree-one points. -/
theorem sum_fourStarDegree_add_card_degreeOne_eq_two_mul_card
    {Point : Type*} [DecidableEq Point]
    (B : Fin 4 → Finset Point) (C : Finset Point)
    (hprofile : ∀ x ∈ C,
      fourStarDegree B x = 1 ∨ fourStarDegree B x = 2) :
    (∑ x ∈ C, fourStarDegree B x) +
        (C.filter fun x => fourStarDegree B x = 1).card = 2 * C.card := by
  classical
  calc
    (∑ x ∈ C, fourStarDegree B x) +
        (C.filter fun x => fourStarDegree B x = 1).card =
        (∑ x ∈ C, fourStarDegree B x) +
          ∑ x ∈ C, if fourStarDegree B x = 1 then 1 else 0 := by
            congr 1
            rw [Finset.card_eq_sum_ones, Finset.sum_filter]
    _ = ∑ x ∈ C,
        (fourStarDegree B x + if fourStarDegree B x = 1 then 1 else 0) := by
          rw [Finset.sum_add_distrib]
    _ = ∑ _x ∈ C, 2 := by
          apply Finset.sum_congr rfl
          intro x hx
          rcases hprofile x hx with hdegree | hdegree <;> simp [hdegree]
    _ = 2 * C.card := by simp [Nat.mul_comm]

/-- A three-set that meets each saturated four-star base support at most
once contains at least two degree-one (private) points.  Indeed its total
base incidence is at most four, while three points of degree one or two have
one excess incidence for each degree-two point. -/
theorem fourStar_degreeOne_inter_card_ge_two_of_card_three
    {Point : Type*} [Fintype Point] [DecidableEq Point]
    {B : Fin 4 → Finset Point} (H : IsSaturatedFourStar B)
    (C : Finset Point) (hCcard : C.card = 3)
    (hinter : ∀ i : Fin 4, (C ∩ B i).card ≤ 1) :
    2 ≤ (C ∩ fourStarDegreeOne B).card := by
  classical
  have hsum := sum_fourStarDegree_over B C
  have hsumle : (∑ x ∈ C, fourStarDegree B x) ≤ 4 := by
    rw [hsum]
    calc
      (∑ i : Fin 4, (C ∩ B i).card) ≤ ∑ _i : Fin 4, 1 := by
        apply Finset.sum_le_sum
        intro i hi
        exact hinter i
      _ = 4 := by norm_num
  have hprofile : ∀ x ∈ C,
      fourStarDegree B x = 1 ∨ fourStarDegree B x = 2 := by
    intro x hx
    exact fourStarDegree_eq_one_or_two H x
  have hidentity :=
    sum_fourStarDegree_add_card_degreeOne_eq_two_mul_card B C hprofile
  have hcarrier : fourStarCarrier B = Finset.univ := fourStarCarrier_eq_univ H
  have hdegreeOne :
      C ∩ fourStarDegreeOne B = C.filter fun x => fourStarDegree B x = 1 := by
    ext x
    simp [fourStarDegreeOne, hcarrier]
  rw [hdegreeOne]
  omega

/-- The three pair-intersection points on a fixed base, before proving their
pairwise disjointness from the degree bound. -/
noncomputable def fourStarOtherCrosses {Point : Type*} [DecidableEq Point]
    (B : Fin 4 → Finset Point) (i : Fin 4) : Finset Point :=
  (Finset.univ.erase i).biUnion fun j => B i ∩ B j

theorem fourStarOtherCrosses_subset_base {Point : Type*} [DecidableEq Point]
    (B : Fin 4 → Finset Point) (i : Fin 4) :
    fourStarOtherCrosses B i ⊆ B i := by
  intro x hx
  rcases Finset.mem_biUnion.mp hx with ⟨j, _hj, hxij⟩
  exact (Finset.mem_inter.mp hxij).1

/-- Membership in the cross union exactly says that the point is on `i` and
at least one distinct second base. -/
theorem mem_fourStarOtherCrosses_iff {Point : Type*} [DecidableEq Point]
    (B : Fin 4 → Finset Point) (i : Fin 4) (x : Point) :
    x ∈ fourStarOtherCrosses B i ↔
      x ∈ B i ∧ ∃ j : Fin 4, j ≠ i ∧ x ∈ B j := by
  constructor
  · intro hx
    rcases Finset.mem_biUnion.mp hx with ⟨j, hj, hxj⟩
    refine ⟨(Finset.mem_inter.mp hxj).1, j, ?_, (Finset.mem_inter.mp hxj).2⟩
    exact (Finset.mem_erase.mp hj).1
  · rintro ⟨hxi, j, hji, hxj⟩
    apply Finset.mem_biUnion.mpr
    refine ⟨j, Finset.mem_erase.mpr ⟨hji, Finset.mem_univ _⟩, ?_⟩
    exact Finset.mem_inter.mpr ⟨hxi, hxj⟩

theorem fourStarOtherCrosses_card_eq_three
    {Point : Type*} [Fintype Point] [DecidableEq Point]
    {B : Fin 4 → Finset Point} (H : IsSaturatedFourStar B) (i : Fin 4) :
    (fourStarOtherCrosses B i).card = 3 := by
  classical
  have hdisj :
      ((↑(Finset.univ.erase i : Finset (Fin 4)) : Set (Fin 4))).PairwiseDisjoint
        (fun j => B i ∩ B j) := by
    intro j hj k hk hjk
    apply Finset.disjoint_left.mpr
    intro x hxj hxk
    have hji : j ≠ i := (Finset.mem_erase.mp hj).1
    have hki : k ≠ i := (Finset.mem_erase.mp hk).1
    have hxj' : x ∈ B j := (Finset.mem_inter.mp hxj).2
    have hxk' : x ∈ B k := (Finset.mem_inter.mp hxk).2
    have hxi : x ∈ B i := (Finset.mem_inter.mp hxj).1
    have hsub : ({i, j, k} : Finset (Fin 4)) ⊆
        (Finset.univ.filter fun a => x ∈ B a) := by
      intro a ha
      simp only [Finset.mem_insert, Finset.mem_singleton] at ha
      rcases ha with rfl | rfl | ha
      · simp [hxi]
      · simp [hxj']
      · have hak : a = k := ha
        subst a
        simp [hxk']
    have hthree : ({i, j, k} : Finset (Fin 4)).card = 3 := by
      apply Finset.card_eq_three.mpr
      exact ⟨i, j, k, hji.symm, hki.symm, hjk, rfl⟩
    have hle := Finset.card_le_card hsub
    have hdegree : fourStarDegree B x =
        (Finset.univ.filter fun a => x ∈ B a).card := rfl
    rw [hthree, ← hdegree] at hle
    have hupper := fourStarDegree_le_two H x
    omega
  unfold fourStarOtherCrosses
  rw [Finset.card_biUnion hdisj]
  calc
    (∑ j ∈ (Finset.univ.erase i : Finset (Fin 4)), (B i ∩ B j).card) =
        ∑ _j ∈ (Finset.univ.erase i : Finset (Fin 4)), 1 := by
          apply Finset.sum_congr rfl
          intro j hj
          exact H.pair_inter_one i j (Finset.mem_erase.mp hj).1.symm
    _ = 3 := by simp

/-- On each base, the degree-one layer is exactly the complement of its
three cross points. -/
theorem fourStarDegreeOneOnBase_eq_sdiff_otherCrosses
    {Point : Type*} [Fintype Point] [DecidableEq Point]
    {B : Fin 4 → Finset Point} (H : IsSaturatedFourStar B) (i : Fin 4) :
    fourStarDegreeOneOnBase B i = B i \ fourStarOtherCrosses B i := by
  classical
  ext x
  constructor
  · intro hx
    rcases Finset.mem_inter.mp hx with ⟨hxi, hxone⟩
    refine Finset.mem_sdiff.mpr ⟨hxi, ?_⟩
    intro hcross
    rcases (mem_fourStarOtherCrosses_iff B i x).mp hcross with
      ⟨_hxi, j, hji, hxj⟩
    have hsub : ({i, j} : Finset (Fin 4)) ⊆
        (Finset.univ.filter fun a => x ∈ B a) := by
      intro a ha
      rcases Finset.mem_insert.mp ha with rfl | ha
      · simp [hxi]
      · have haj : a = j := Finset.mem_singleton.mp ha
        subst a
        simp [hxj]
    have hcard : ({i, j} : Finset (Fin 4)).card = 2 := by simp [hji.symm]
    have hle := Finset.card_le_card hsub
    have hxdegree : fourStarDegree B x = 1 := by
      simpa [fourStarDegreeOne, fourStarCarrier_eq_univ H] using hxone
    rw [hcard] at hle
    change 2 ≤ fourStarDegree B x at hle
    omega
  · intro hx
    rcases Finset.mem_sdiff.mp hx with ⟨hxi, hnotcross⟩
    refine Finset.mem_inter.mpr ⟨hxi, ?_⟩
    have hxcarrier : x ∈ fourStarCarrier B := by
      rw [fourStarCarrier_eq_univ H]
      simp
    have hcase := fourStarDegree_eq_one_or_two H x
    have hxdegree : fourStarDegree B x = 1 := by
      rcases hcase with hone | htwo
      · exact hone
      · exfalso
        have hfilter : ∃ j : Fin 4, j ≠ i ∧ x ∈ B j := by
          have hcount :
              (Finset.univ.filter fun a => x ∈ B a).card = 2 := htwo
          have hi : i ∈ Finset.univ.filter fun a => x ∈ B a := by simp [hxi]
          obtain ⟨j, hj, hji⟩ := Finset.exists_mem_ne
            (by rw [hcount]; omega) i
          exact ⟨j, hji, (Finset.mem_filter.mp hj).2⟩
        exact hnotcross ((mem_fourStarOtherCrosses_iff B i x).mpr
          ⟨hxi, hfilter.choose, hfilter.choose_spec.1, hfilter.choose_spec.2⟩)
    simp [fourStarDegreeOne, fourStarCarrier_eq_univ H, hxdegree]

/-- The local degree-one complement has cardinality one on every base. -/
theorem fourStar_degreeOneOnBase_card_eq_one
    {Point : Type*} [Fintype Point] [DecidableEq Point]
    {B : Fin 4 → Finset Point} (H : IsSaturatedFourStar B) (i : Fin 4) :
    (fourStarDegreeOneOnBase B i).card = 1 := by
  rw [fourStarDegreeOneOnBase_eq_sdiff_otherCrosses H i,
    Finset.card_sdiff_of_subset (fourStarOtherCrosses_subset_base B i),
    H.base_card i, fourStarOtherCrosses_card_eq_three H i]

/-- Public saturated four-star profile theorem: four four-subsets of a
ten-point universe with all six intersections of size one have incidence
profile `2^6 1^4`, and exactly one degree-one point on every base support. -/
theorem saturated_fourStar_degree_profile
    {Point : Type*} [Fintype Point] [DecidableEq Point]
    {B : Fin 4 → Finset Point} (H : IsSaturatedFourStar B) :
    IsFourStarDegreeProfile B where
  carrier_card := H.carrier_card
  degree_one_or_two := by
    intro x _hx
    exact fourStarDegree_eq_one_or_two H x
  degree_one_card := fourStar_degreeOne_card_eq_four H
  degree_two_card := fourStar_degreeTwo_card_eq_six H
  one_on_each_base := fourStar_degreeOneOnBase_card_eq_one H

/-!
`saturated_fourStar_degree_profile` is intended to be the neutral finite
input for the V1 four-star/harmonic bridge.  It uses only finite-set moments;
no projective or Euclidean datum occurs in its statement.
-/

end Erdos506.Finite
