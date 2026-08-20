import Erdos506.V1.ElevenFiveC40SmallFiveFinish
import Mathlib.Tactic

/-!
# Exact arithmetic profiles in the two small C40/L11 faces

The completed C40 singleton dispatcher makes the five-block second moment
even.  Together with the local beta domains and the global incidence rows,
this leaves four arithmetic profiles when `B₅ = 5` and five profiles when
`B₅ = 6`.  In each case the moment is either two below the all-double
maximum or is equal to that maximum.

Thus the rows alone do not honestly force moments `18` and `28`: the sole
remaining input is exclusion of the corresponding all-double face.  The
last two theorems expose exactly that seam for the geometric endpoint.
-/

namespace Erdos506.V1

open Erdos506.Block
open Erdos506.Block.BlockSystem
open Erdos506.Incidence
open Erdos506.V3
open Erdos506.V4
open scoped BigOperators

universe u v

/-- Number of points of a prescribed five-block degree. -/
noncomputable def elevenFiveC40SmallDegreeCount
    {Point : Type u} {Block : Type v} [Fintype Point] [Fintype Block]
    [DecidableEq Point]
    (S : BlockSystem Point Block) (d : ℕ) : ℕ :=
  ((Finset.univ : Finset Point).filter fun p =>
    S.blockDegree 5 p = d).card

/-- The beta cap leaves only five-degrees one through four. -/
theorem elevenFive_c40_l11_small_fiveDegree_values
    {Point : Type u} {Block : Type v} [Fintype Point] [Fintype Block]
    [DecidableEq Point]
    (S : BlockSystem Point Block)
    (hlocal : ∀ p : Point, ElevenFiveLocalRows S p)
    (hC : S.totalCircleCount = 40)
    (hbeta : ∀ p : Point,
      S.blockDegree 3 p + S.blockDegree 4 p + S.blockDegree 5 p ≤ 18)
    (p : Point) :
    S.blockDegree 5 p = 1 ∨ S.blockDegree 5 p = 2 ∨
      S.blockDegree 5 p = 3 ∨ S.blockDegree 5 p = 4 := by
  rcases elevenFive_c40_l11_pivot_domains_of_beta_cap
    S p (hlocal p) hC (hbeta p) with ⟨_h6, hlow⟩ | ⟨_h9, hhigh⟩
  · rcases hlow with h1 | h2 | h3
    · exact Or.inl h1
    · exact Or.inr (Or.inl h2)
    · exact Or.inr (Or.inr (Or.inl h3))
  · rcases hhigh with h3 | h4
    · exact Or.inr (Or.inr (Or.inl h3))
    · exact Or.inr (Or.inr (Or.inr h4))

/-- The point-count, five-incidence, and pair-moment rows in literal degree
coordinates `n₁,n₂,n₃,n₄`. -/
theorem elevenFive_c40_l11_small_degree_count_rows
    {Point : Type u} {Block : Type v} [Fintype Point] [Fintype Block]
    [DecidableEq Point]
    (S : BlockSystem Point Block) (hcard : Fintype.card Point = 11)
    (hlocal : ∀ p : Point, ElevenFiveLocalRows S p)
    (hglobal : ElevenFiveGlobalRows S)
    (hC : S.totalCircleCount = 40)
    (hbeta : ∀ p : Point,
      S.blockDegree 3 p + S.blockDegree 4 p + S.blockDegree 5 p ≤ 18) :
    elevenFiveC40SmallDegreeCount S 1 +
        elevenFiveC40SmallDegreeCount S 2 +
        elevenFiveC40SmallDegreeCount S 3 +
        elevenFiveC40SmallDegreeCount S 4 = 11 ∧
      5 * S.blockCount 5 +
          2 * elevenFiveC40SmallDegreeCount S 1 +
            elevenFiveC40SmallDegreeCount S 2 =
        33 + elevenFiveC40SmallDegreeCount S 4 ∧
      elevenFiveSecondMoment S +
          3 * elevenFiveC40SmallDegreeCount S 1 +
            2 * elevenFiveC40SmallDegreeCount S 2 =
        33 + 3 * elevenFiveC40SmallDegreeCount S 4 := by
  classical
  have hdegree (p : Point) :
      S.blockDegree 5 p = 1 ∨ S.blockDegree 5 p = 2 ∨
        S.blockDegree 5 p = 3 ∨ S.blockDegree 5 p = 4 :=
    elevenFive_c40_l11_small_fiveDegree_values S hlocal hC hbeta p
  have hcount (d : ℕ) :
      (∑ p : Point, if S.blockDegree 5 p = d then 1 else 0) =
        elevenFiveC40SmallDegreeCount S d := by
    simp [elevenFiveC40SmallDegreeCount]
  have hpartitionPoint (p : Point) :
      (if S.blockDegree 5 p = 1 then 1 else 0) +
          (if S.blockDegree 5 p = 2 then 1 else 0) +
          (if S.blockDegree 5 p = 3 then 1 else 0) +
          (if S.blockDegree 5 p = 4 then 1 else 0) = 1 := by
    rcases hdegree p with h1 | h2 | h3 | h4
    · norm_num [h1]
    · norm_num [h2]
    · norm_num [h3]
    · norm_num [h4]
  have hincPoint (p : Point) :
      S.blockDegree 5 p +
          2 * (if S.blockDegree 5 p = 1 then 1 else 0) +
            (if S.blockDegree 5 p = 2 then 1 else 0) =
        3 + (if S.blockDegree 5 p = 4 then 1 else 0) := by
    rcases hdegree p with h1 | h2 | h3 | h4
    · norm_num [h1]
    · norm_num [h2]
    · norm_num [h3]
    · norm_num [h4]
  have hmomentPoint (p : Point) :
      Nat.choose (S.blockDegree 5 p) 2 +
          3 * (if S.blockDegree 5 p = 1 then 1 else 0) +
            2 * (if S.blockDegree 5 p = 2 then 1 else 0) =
        3 + 3 * (if S.blockDegree 5 p = 4 then 1 else 0) := by
    rcases hdegree p with h1 | h2 | h3 | h4
    · norm_num [h1, Nat.choose]
    · norm_num [h2, Nat.choose]
    · norm_num [h3, Nat.choose]
    · norm_num [h4, Nat.choose]
  refine ⟨?_, ?_, ?_⟩
  · calc
      elevenFiveC40SmallDegreeCount S 1 +
            elevenFiveC40SmallDegreeCount S 2 +
            elevenFiveC40SmallDegreeCount S 3 +
            elevenFiveC40SmallDegreeCount S 4 =
          (∑ p : Point, if S.blockDegree 5 p = 1 then 1 else 0) +
            (∑ p : Point, if S.blockDegree 5 p = 2 then 1 else 0) +
            (∑ p : Point, if S.blockDegree 5 p = 3 then 1 else 0) +
            (∑ p : Point, if S.blockDegree 5 p = 4 then 1 else 0) := by
        rw [hcount 1, hcount 2, hcount 3, hcount 4]
      _ = ∑ p : Point,
          ((if S.blockDegree 5 p = 1 then 1 else 0) +
            (if S.blockDegree 5 p = 2 then 1 else 0) +
            (if S.blockDegree 5 p = 3 then 1 else 0) +
            (if S.blockDegree 5 p = 4 then 1 else 0)) := by
        simp only [Finset.sum_add_distrib]
      _ = ∑ _p : Point, 1 := by
        apply Finset.sum_congr rfl
        intro p _hp
        exact hpartitionPoint p
      _ = 11 := by simp [hcard]
  · calc
      5 * S.blockCount 5 +
            2 * elevenFiveC40SmallDegreeCount S 1 +
              elevenFiveC40SmallDegreeCount S 2 =
          (∑ p : Point, S.blockDegree 5 p) +
            2 * (∑ p : Point,
              if S.blockDegree 5 p = 1 then 1 else 0) +
            (∑ p : Point,
              if S.blockDegree 5 p = 2 then 1 else 0) := by
        rw [hglobal.fiveIncidence, hcount 1, hcount 2]
      _ = ∑ p : Point,
          (S.blockDegree 5 p +
            2 * (if S.blockDegree 5 p = 1 then 1 else 0) +
              (if S.blockDegree 5 p = 2 then 1 else 0)) := by
        simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
      _ = ∑ p : Point,
          (3 + (if S.blockDegree 5 p = 4 then 1 else 0)) := by
        apply Finset.sum_congr rfl
        intro p _hp
        exact hincPoint p
      _ = 33 + elevenFiveC40SmallDegreeCount S 4 := by
        rw [Finset.sum_add_distrib, hcount 4]
        simp [hcard]
  · calc
      elevenFiveSecondMoment S +
            3 * elevenFiveC40SmallDegreeCount S 1 +
              2 * elevenFiveC40SmallDegreeCount S 2 =
          (∑ p : Point, Nat.choose (S.blockDegree 5 p) 2) +
            3 * (∑ p : Point,
              if S.blockDegree 5 p = 1 then 1 else 0) +
            2 * (∑ p : Point,
              if S.blockDegree 5 p = 2 then 1 else 0) := by
        rw [elevenFiveSecondMoment, hcount 1, hcount 2]
      _ = ∑ p : Point,
          (Nat.choose (S.blockDegree 5 p) 2 +
            3 * (if S.blockDegree 5 p = 1 then 1 else 0) +
              2 * (if S.blockDegree 5 p = 2 then 1 else 0)) := by
        simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
      _ = ∑ p : Point,
          (3 + 3 * (if S.blockDegree 5 p = 4 then 1 else 0)) := by
        apply Finset.sum_congr rfl
        intro p _hp
        exact hmomentPoint p
      _ = 33 + 3 * elevenFiveC40SmallDegreeCount S 4 := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, hcount 4]
        simp [hcard]

/-- A degree-four five-block pivot is necessarily a degree-nine
three-block pivot in the beta domain. -/
theorem elevenFive_c40_l11_small_degreeFour_subset_degreeNine
    {Point : Type u} {Block : Type v} [Fintype Point] [Fintype Block]
    [DecidableEq Point]
    (S : BlockSystem Point Block)
    (hlocal : ∀ p : Point, ElevenFiveLocalRows S p)
    (hC : S.totalCircleCount = 40)
    (hbeta : ∀ p : Point,
      S.blockDegree 3 p + S.blockDegree 4 p + S.blockDegree 5 p ≤ 18) :
    ((Finset.univ : Finset Point).filter fun p =>
        S.blockDegree 5 p = 4) ⊆
      ((Finset.univ : Finset Point).filter fun p =>
        S.blockDegree 3 p = 9) := by
  intro p hp
  have hp4 : S.blockDegree 5 p = 4 := (Finset.mem_filter.mp hp).2
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rcases elevenFive_c40_l11_pivot_domains_of_beta_cap
    S p (hlocal p) hC (hbeta p) with ⟨_h6, hlow⟩ | ⟨h9, _hhigh⟩
  · rcases hlow with h1 | h2 | h3 <;> omega
  · exact h9

/-- In the `B₅ = 5` face there is one degree-nine three-block pivot. -/
theorem elevenFive_c40_l11_b5_five_threeDegree_profile
    {Point : Type u} {Block : Type v} [Fintype Point] [Fintype Block]
    [DecidableEq Point]
    (S : BlockSystem Point Block) (hcard : Fintype.card Point = 11)
    (hlocal : ∀ p : Point, ElevenFiveLocalRows S p)
    (hglobal : ElevenFiveGlobalRows S)
    (hC : S.totalCircleCount = 40)
    (hL : elevenFiveLineTotal S = 11)
    (hfive : S.blockCount 5 = 5)
    (hbeta : ∀ p : Point,
      S.blockDegree 3 p + S.blockDegree 4 p + S.blockDegree 5 p ≤ 18) :
    ((Finset.univ : Finset Point).filter fun p =>
      S.blockDegree 3 p = 9).card = 1 ∧
      ∀ p : Point, S.blockDegree 3 p = 6 ∨ S.blockDegree 3 p = 9 := by
  classical
  have htriple := hglobal.tripleRow
  have htotal := hglobal.blockTotal
  have hthreeCount : S.blockCount 3 = 23 := by
    rw [hfive] at htriple
    rw [hC, hL] at htotal
    omega
  have hthreeSum : (∑ p : Point, S.blockDegree 3 p) = 69 := by
    rw [hglobal.threeIncidence, hthreeCount]
  have hvalues (p : Point) :
      S.blockDegree 3 p = 6 ∨ S.blockDegree 3 p = 9 := by
    rcases elevenFive_c40_threeDegree_values S p (hlocal p) hC with
      h6 | h9 | h12
    · exact Or.inl h6
    · exact Or.inr h9
    · have hpivot := hbeta p
      have hfiveCap := (hlocal p).fiveDegreeCap
      have hpair := (hlocal p).pairRow
      omega
  let H := (Finset.univ : Finset Point).filter fun p =>
    S.blockDegree 3 p = 9
  have hpoint (p : Point) : S.blockDegree 3 p =
      6 + 3 * (if p ∈ H then 1 else 0) := by
    rcases hvalues p with h6 | h9
    · simp [H, h6]
    · simp [H, h9]
  have hindicator : (∑ p : Point, if p ∈ H then 1 else 0) = H.card := by
    simp [H]
  have hsum :
      (∑ p : Point, S.blockDegree 3 p) =
        ∑ p : Point, (6 + 3 * (if p ∈ H then 1 else 0)) := by
    apply Finset.sum_congr rfl
    intro p _hp
    exact hpoint p
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, hindicator,
    Finset.sum_const, Finset.card_univ, hcard, hthreeSum] at hsum
  norm_num at hsum
  constructor
  · simpa [H] using (show H.card = 1 by omega)
  · exact hvalues

/-- In the `B₅ = 6` face there are three degree-nine three-block pivots. -/
theorem elevenFive_c40_l11_b5_six_threeDegree_profile
    {Point : Type u} {Block : Type v} [Fintype Point] [Fintype Block]
    [DecidableEq Point]
    (S : BlockSystem Point Block) (hcard : Fintype.card Point = 11)
    (hlocal : ∀ p : Point, ElevenFiveLocalRows S p)
    (hglobal : ElevenFiveGlobalRows S)
    (hC : S.totalCircleCount = 40)
    (hL : elevenFiveLineTotal S = 11)
    (hfive : S.blockCount 5 = 6)
    (hbeta : ∀ p : Point,
      S.blockDegree 3 p + S.blockDegree 4 p + S.blockDegree 5 p ≤ 18) :
    ((Finset.univ : Finset Point).filter fun p =>
      S.blockDegree 3 p = 9).card = 3 ∧
      ∀ p : Point, S.blockDegree 3 p = 6 ∨ S.blockDegree 3 p = 9 := by
  classical
  have htriple := hglobal.tripleRow
  have htotal := hglobal.blockTotal
  have hthreeCount : S.blockCount 3 = 25 := by
    rw [hfive] at htriple
    rw [hC, hL] at htotal
    omega
  have hthreeSum : (∑ p : Point, S.blockDegree 3 p) = 75 := by
    rw [hglobal.threeIncidence, hthreeCount]
  have hvalues (p : Point) :
      S.blockDegree 3 p = 6 ∨ S.blockDegree 3 p = 9 := by
    rcases elevenFive_c40_threeDegree_values S p (hlocal p) hC with
      h6 | h9 | h12
    · exact Or.inl h6
    · exact Or.inr h9
    · have hpivot := hbeta p
      have hfiveCap := (hlocal p).fiveDegreeCap
      have hpair := (hlocal p).pairRow
      omega
  let H := (Finset.univ : Finset Point).filter fun p =>
    S.blockDegree 3 p = 9
  have hpoint (p : Point) : S.blockDegree 3 p =
      6 + 3 * (if p ∈ H then 1 else 0) := by
    rcases hvalues p with h6 | h9
    · simp [H, h6]
    · simp [H, h9]
  have hindicator : (∑ p : Point, if p ∈ H then 1 else 0) = H.card := by
    simp [H]
  have hsum :
      (∑ p : Point, S.blockDegree 3 p) =
        ∑ p : Point, (6 + 3 * (if p ∈ H then 1 else 0)) := by
    apply Finset.sum_congr rfl
    intro p _hp
    exact hpoint p
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, hindicator,
    Finset.sum_const, Finset.card_univ, hcard, hthreeSum] at hsum
  norm_num at hsum
  constructor
  · simpa [H] using (show H.card = 3 by omega)
  · exact hvalues

/-- Complete arithmetic profile list for `B₅ = 5`. -/
theorem elevenFive_c40_l11_b5_five_arithmetic_profiles
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    (cfg : Configuration Point) (hcard : Fintype.card Point = 11)
    (hlocal : ∀ p : Point, ElevenFiveLocalRows (blockSystem cfg) p)
    (hglobal : ElevenFiveGlobalRows (blockSystem cfg))
    (hC : (blockSystem cfg).totalCircleCount = 40)
    (hL : elevenFiveLineTotal (blockSystem cfg) = 11)
    (hfive : (blockSystem cfg).blockCount 5 = 5)
    (hbeta : ∀ p : Point,
      (blockSystem cfg).blockDegree 3 p +
        (blockSystem cfg).blockDegree 4 p +
          (blockSystem cfg).blockDegree 5 p ≤ 18) :
    (elevenFiveSecondMoment (blockSystem cfg) = 18 ∧
      elevenFiveC40SmallDegreeCount (blockSystem cfg) 4 = 0 ∧
      elevenFiveC40SmallDegreeCount (blockSystem cfg) 1 = 1 ∧
      elevenFiveC40SmallDegreeCount (blockSystem cfg) 2 = 6 ∧
      elevenFiveC40SmallDegreeCount (blockSystem cfg) 3 = 4) ∨
    (elevenFiveSecondMoment (blockSystem cfg) = 18 ∧
      elevenFiveC40SmallDegreeCount (blockSystem cfg) 4 = 1 ∧
      elevenFiveC40SmallDegreeCount (blockSystem cfg) 1 = 0 ∧
      elevenFiveC40SmallDegreeCount (blockSystem cfg) 2 = 9 ∧
      elevenFiveC40SmallDegreeCount (blockSystem cfg) 3 = 1) ∨
    (elevenFiveSecondMoment (blockSystem cfg) = 20 ∧
      elevenFiveC40SmallDegreeCount (blockSystem cfg) 4 = 0 ∧
      elevenFiveC40SmallDegreeCount (blockSystem cfg) 1 = 3 ∧
      elevenFiveC40SmallDegreeCount (blockSystem cfg) 2 = 2 ∧
      elevenFiveC40SmallDegreeCount (blockSystem cfg) 3 = 6) ∨
    (elevenFiveSecondMoment (blockSystem cfg) = 20 ∧
      elevenFiveC40SmallDegreeCount (blockSystem cfg) 4 = 1 ∧
      elevenFiveC40SmallDegreeCount (blockSystem cfg) 1 = 2 ∧
      elevenFiveC40SmallDegreeCount (blockSystem cfg) 2 = 5 ∧
      elevenFiveC40SmallDegreeCount (blockSystem cfg) 3 = 3) := by
  classical
  obtain ⟨hpoints, _hinc, _hmomentRow⟩ :=
    elevenFive_c40_l11_small_degree_count_rows
      (blockSystem cfg) hcard hlocal hglobal hC hbeta
  have hfaces :
      (elevenFiveSecondMoment (blockSystem cfg) = 18 ∧
        elevenFiveC40SmallDegreeCount (blockSystem cfg) 4 = 0 ∧
        elevenFiveC40SmallDegreeCount (blockSystem cfg) 1 = 1 ∧
        elevenFiveC40SmallDegreeCount (blockSystem cfg) 2 = 6) ∨
      (elevenFiveSecondMoment (blockSystem cfg) = 18 ∧
        elevenFiveC40SmallDegreeCount (blockSystem cfg) 4 = 1 ∧
        elevenFiveC40SmallDegreeCount (blockSystem cfg) 1 = 0 ∧
        elevenFiveC40SmallDegreeCount (blockSystem cfg) 2 = 9) ∨
      (elevenFiveSecondMoment (blockSystem cfg) = 20 ∧
        elevenFiveC40SmallDegreeCount (blockSystem cfg) 4 = 0 ∧
        elevenFiveC40SmallDegreeCount (blockSystem cfg) 1 = 3 ∧
        elevenFiveC40SmallDegreeCount (blockSystem cfg) 2 = 2) ∨
      (elevenFiveSecondMoment (blockSystem cfg) = 20 ∧
        elevenFiveC40SmallDegreeCount (blockSystem cfg) 4 = 1 ∧
        elevenFiveC40SmallDegreeCount (blockSystem cfg) 1 = 2 ∧
        elevenFiveC40SmallDegreeCount (blockSystem cfg) 2 = 5) := by
    simpa only [elevenFiveC40SmallFiveDegreeCount,
      elevenFiveC40SmallDegreeCount] using
        (elevenFive_c40_l11_b5_five_arithmetic_faces
          cfg hcard hlocal hglobal hC hL hfive hbeta)
  rcases hfaces with h | h | h | h
  · exact Or.inl
      ⟨h.1, h.2.1, h.2.2.1, h.2.2.2, by omega⟩
  · exact Or.inr (Or.inl
      ⟨h.1, h.2.1, h.2.2.1, h.2.2.2, by omega⟩)
  · exact Or.inr (Or.inr (Or.inl
      ⟨h.1, h.2.1, h.2.2.1, h.2.2.2, by omega⟩))
  · exact Or.inr (Or.inr (Or.inr
      ⟨h.1, h.2.1, h.2.2.1, h.2.2.2, by omega⟩))

private theorem elevenFive_c40_l11_b5_six_profile_n4_zero
    (m n1 n2 n3 n4 k : ℕ)
    (hpoints : n1 + n2 + n3 + n4 = 11)
    (hinc : 30 + 2 * n1 + n2 = 33 + n4)
    (hmoment : m + 3 * n1 + 2 * n2 = 33 + 3 * n4)
    (hcap : m ≤ 30) (heven : m = 2 * k) (hfour : n4 = 0) :
    m = 28 ∧ n4 = 0 ∧ n1 = 1 ∧ n2 = 1 ∧ n3 = 9 := by
  omega

private theorem elevenFive_c40_l11_b5_six_profile_n4_one
    (m n1 n2 n3 n4 k : ℕ)
    (hpoints : n1 + n2 + n3 + n4 = 11)
    (hinc : 30 + 2 * n1 + n2 = 33 + n4)
    (hmoment : m + 3 * n1 + 2 * n2 = 33 + 3 * n4)
    (hcap : m ≤ 30) (heven : m = 2 * k) (hfour : n4 = 1) :
    (m = 28 ∧ n4 = 1 ∧ n1 = 0 ∧ n2 = 4 ∧ n3 = 6) ∨
      (m = 30 ∧ n4 = 1 ∧ n1 = 2 ∧ n2 = 0 ∧ n3 = 8) := by
  have hone : n1 = 0 ∨ n1 = 2 := by omega
  rcases hone with hone | hone
  · exact Or.inl (by omega)
  · exact Or.inr (by omega)

private theorem elevenFive_c40_l11_b5_six_profile_n4_two
    (m n1 n2 n3 n4 k : ℕ)
    (hpoints : n1 + n2 + n3 + n4 = 11)
    (hinc : 30 + 2 * n1 + n2 = 33 + n4)
    (hmoment : m + 3 * n1 + 2 * n2 = 33 + 3 * n4)
    (hcap : m ≤ 30) (heven : m = 2 * k) (hfour : n4 = 2) :
    m = 30 ∧ n4 = 2 ∧ n1 = 1 ∧ n2 = 3 ∧ n3 = 5 := by
  omega

private theorem elevenFive_c40_l11_b5_six_profile_n4_three
    (m n1 n2 n3 n4 k : ℕ)
    (hpoints : n1 + n2 + n3 + n4 = 11)
    (hinc : 30 + 2 * n1 + n2 = 33 + n4)
    (hmoment : m + 3 * n1 + 2 * n2 = 33 + 3 * n4)
    (hcap : m ≤ 30) (heven : m = 2 * k) (hfour : n4 = 3) :
    m = 30 ∧ n4 = 3 ∧ n1 = 0 ∧ n2 = 6 ∧ n3 = 2 := by
  omega

/-- Complete arithmetic profile list for `B₅ = 6`. -/
theorem elevenFive_c40_l11_b5_six_arithmetic_profiles
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    (cfg : Configuration Point) (hcard : Fintype.card Point = 11)
    (hlocal : ∀ p : Point, ElevenFiveLocalRows (blockSystem cfg) p)
    (hglobal : ElevenFiveGlobalRows (blockSystem cfg))
    (hC : (blockSystem cfg).totalCircleCount = 40)
    (hL : elevenFiveLineTotal (blockSystem cfg) = 11)
    (hfive : (blockSystem cfg).blockCount 5 = 6)
    (hbeta : ∀ p : Point,
      (blockSystem cfg).blockDegree 3 p +
        (blockSystem cfg).blockDegree 4 p +
          (blockSystem cfg).blockDegree 5 p ≤ 18) :
    (elevenFiveSecondMoment (blockSystem cfg) = 28 ∧
      elevenFiveC40SmallDegreeCount (blockSystem cfg) 4 = 0 ∧
      elevenFiveC40SmallDegreeCount (blockSystem cfg) 1 = 1 ∧
      elevenFiveC40SmallDegreeCount (blockSystem cfg) 2 = 1 ∧
      elevenFiveC40SmallDegreeCount (blockSystem cfg) 3 = 9) ∨
    (elevenFiveSecondMoment (blockSystem cfg) = 28 ∧
      elevenFiveC40SmallDegreeCount (blockSystem cfg) 4 = 1 ∧
      elevenFiveC40SmallDegreeCount (blockSystem cfg) 1 = 0 ∧
      elevenFiveC40SmallDegreeCount (blockSystem cfg) 2 = 4 ∧
      elevenFiveC40SmallDegreeCount (blockSystem cfg) 3 = 6) ∨
    (elevenFiveSecondMoment (blockSystem cfg) = 30 ∧
      elevenFiveC40SmallDegreeCount (blockSystem cfg) 4 = 1 ∧
      elevenFiveC40SmallDegreeCount (blockSystem cfg) 1 = 2 ∧
      elevenFiveC40SmallDegreeCount (blockSystem cfg) 2 = 0 ∧
      elevenFiveC40SmallDegreeCount (blockSystem cfg) 3 = 8) ∨
    (elevenFiveSecondMoment (blockSystem cfg) = 30 ∧
      elevenFiveC40SmallDegreeCount (blockSystem cfg) 4 = 2 ∧
      elevenFiveC40SmallDegreeCount (blockSystem cfg) 1 = 1 ∧
      elevenFiveC40SmallDegreeCount (blockSystem cfg) 2 = 3 ∧
      elevenFiveC40SmallDegreeCount (blockSystem cfg) 3 = 5) ∨
    (elevenFiveSecondMoment (blockSystem cfg) = 30 ∧
      elevenFiveC40SmallDegreeCount (blockSystem cfg) 4 = 3 ∧
      elevenFiveC40SmallDegreeCount (blockSystem cfg) 1 = 0 ∧
      elevenFiveC40SmallDegreeCount (blockSystem cfg) 2 = 6 ∧
      elevenFiveC40SmallDegreeCount (blockSystem cfg) 3 = 2) := by
  classical
  let S := blockSystem cfg
  obtain ⟨hpoints, hinc, hmomentRow⟩ :=
    elevenFive_c40_l11_small_degree_count_rows
      S hcard (by simpa [S] using hlocal) (by simpa [S] using hglobal)
        (by simpa [S] using hC) (by simpa [S] using hbeta)
  obtain ⟨hhigh, _hvalues⟩ :=
    elevenFive_c40_l11_b5_six_threeDegree_profile
      S hcard (by simpa [S] using hlocal) (by simpa [S] using hglobal)
        (by simpa [S] using hC) (by simpa [S] using hL)
          (by simpa [S] using hfive) (by simpa [S] using hbeta)
  have hfourSub := elevenFive_c40_l11_small_degreeFour_subset_degreeNine
    S (by simpa [S] using hlocal) (by simpa [S] using hC)
      (by simpa [S] using hbeta)
  have hfourLe := Finset.card_le_card hfourSub
  rw [hhigh] at hfourLe
  have hfourLeThree : elevenFiveC40SmallDegreeCount S 4 ≤ 3 := by
    simpa [elevenFiveC40SmallDegreeCount] using hfourLe
  have hcap := hglobal.secondMomentCap
  rw [hfive] at hinc hcap
  norm_num [Nat.choose] at hinc hcap
  change elevenFiveSecondMoment S ≤ 30 at hcap
  have heven := elevenFive_c40_l11_secondMoment_even
    cfg hcard hlocal hC hbeta
  change Even (elevenFiveSecondMoment S) at heven
  obtain ⟨k, hk⟩ := heven
  have hk' : elevenFiveSecondMoment S = 2 * k := by omega
  change
    (elevenFiveSecondMoment S = 28 ∧
      elevenFiveC40SmallDegreeCount S 4 = 0 ∧
      elevenFiveC40SmallDegreeCount S 1 = 1 ∧
      elevenFiveC40SmallDegreeCount S 2 = 1 ∧
      elevenFiveC40SmallDegreeCount S 3 = 9) ∨
    (elevenFiveSecondMoment S = 28 ∧
      elevenFiveC40SmallDegreeCount S 4 = 1 ∧
      elevenFiveC40SmallDegreeCount S 1 = 0 ∧
      elevenFiveC40SmallDegreeCount S 2 = 4 ∧
      elevenFiveC40SmallDegreeCount S 3 = 6) ∨
    (elevenFiveSecondMoment S = 30 ∧
      elevenFiveC40SmallDegreeCount S 4 = 1 ∧
      elevenFiveC40SmallDegreeCount S 1 = 2 ∧
      elevenFiveC40SmallDegreeCount S 2 = 0 ∧
      elevenFiveC40SmallDegreeCount S 3 = 8) ∨
    (elevenFiveSecondMoment S = 30 ∧
      elevenFiveC40SmallDegreeCount S 4 = 2 ∧
      elevenFiveC40SmallDegreeCount S 1 = 1 ∧
      elevenFiveC40SmallDegreeCount S 2 = 3 ∧
      elevenFiveC40SmallDegreeCount S 3 = 5) ∨
    (elevenFiveSecondMoment S = 30 ∧
      elevenFiveC40SmallDegreeCount S 4 = 3 ∧
      elevenFiveC40SmallDegreeCount S 1 = 0 ∧
      elevenFiveC40SmallDegreeCount S 2 = 6 ∧
      elevenFiveC40SmallDegreeCount S 3 = 2)
  have hfourCases :
      elevenFiveC40SmallDegreeCount S 4 = 0 ∨
        elevenFiveC40SmallDegreeCount S 4 = 1 ∨
        elevenFiveC40SmallDegreeCount S 4 = 2 ∨
        elevenFiveC40SmallDegreeCount S 4 = 3 := by
    omega
  rcases hfourCases with hfour | hfour | hfour | hfour
  · exact Or.inl
      (elevenFive_c40_l11_b5_six_profile_n4_zero
        (elevenFiveSecondMoment S)
        (elevenFiveC40SmallDegreeCount S 1)
        (elevenFiveC40SmallDegreeCount S 2)
        (elevenFiveC40SmallDegreeCount S 3)
        (elevenFiveC40SmallDegreeCount S 4) k
        hpoints hinc hmomentRow hcap hk' hfour)
  · rcases elevenFive_c40_l11_b5_six_profile_n4_one
      (elevenFiveSecondMoment S)
      (elevenFiveC40SmallDegreeCount S 1)
      (elevenFiveC40SmallDegreeCount S 2)
      (elevenFiveC40SmallDegreeCount S 3)
      (elevenFiveC40SmallDegreeCount S 4) k
      hpoints hinc hmomentRow hcap hk' hfour with h | h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr (Or.inl
      (elevenFive_c40_l11_b5_six_profile_n4_two
        (elevenFiveSecondMoment S)
        (elevenFiveC40SmallDegreeCount S 1)
        (elevenFiveC40SmallDegreeCount S 2)
        (elevenFiveC40SmallDegreeCount S 3)
        (elevenFiveC40SmallDegreeCount S 4) k
        hpoints hinc hmomentRow hcap hk' hfour))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr
      (elevenFive_c40_l11_b5_six_profile_n4_three
        (elevenFiveSecondMoment S)
        (elevenFiveC40SmallDegreeCount S 1)
        (elevenFiveC40SmallDegreeCount S 2)
        (elevenFiveC40SmallDegreeCount S 3)
        (elevenFiveC40SmallDegreeCount S 4) k
        hpoints hinc hmomentRow hcap hk' hfour))))

/-- The five-block face has moment `18` or the all-double maximum `20`. -/
theorem elevenFive_c40_l11_b5_five_secondMoment_eq_eighteen_or_twenty
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    (cfg : Configuration Point) (hcard : Fintype.card Point = 11)
    (hlocal : ∀ p : Point, ElevenFiveLocalRows (blockSystem cfg) p)
    (hglobal : ElevenFiveGlobalRows (blockSystem cfg))
    (hC : (blockSystem cfg).totalCircleCount = 40)
    (hL : elevenFiveLineTotal (blockSystem cfg) = 11)
    (hfive : (blockSystem cfg).blockCount 5 = 5)
    (hbeta : ∀ p : Point,
      (blockSystem cfg).blockDegree 3 p +
        (blockSystem cfg).blockDegree 4 p +
          (blockSystem cfg).blockDegree 5 p ≤ 18) :
    elevenFiveSecondMoment (blockSystem cfg) = 18 ∨
      elevenFiveSecondMoment (blockSystem cfg) = 20 := by
  rcases elevenFive_c40_l11_b5_five_arithmetic_profiles
    cfg hcard hlocal hglobal hC hL hfive hbeta with h | h | h | h
  · exact Or.inl h.1
  · exact Or.inl h.1
  · exact Or.inr h.1
  · exact Or.inr h.1

/-- The six-block face has moment `28` or the all-double maximum `30`. -/
theorem elevenFive_c40_l11_b5_six_secondMoment_eq_twentyEight_or_thirty
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    (cfg : Configuration Point) (hcard : Fintype.card Point = 11)
    (hlocal : ∀ p : Point, ElevenFiveLocalRows (blockSystem cfg) p)
    (hglobal : ElevenFiveGlobalRows (blockSystem cfg))
    (hC : (blockSystem cfg).totalCircleCount = 40)
    (hL : elevenFiveLineTotal (blockSystem cfg) = 11)
    (hfive : (blockSystem cfg).blockCount 5 = 6)
    (hbeta : ∀ p : Point,
      (blockSystem cfg).blockDegree 3 p +
        (blockSystem cfg).blockDegree 4 p +
          (blockSystem cfg).blockDegree 5 p ≤ 18) :
    elevenFiveSecondMoment (blockSystem cfg) = 28 ∨
      elevenFiveSecondMoment (blockSystem cfg) = 30 := by
  rcases elevenFive_c40_l11_b5_six_arithmetic_profiles
    cfg hcard hlocal hglobal hC hL hfive hbeta with h | h | h | h | h
  · exact Or.inl h.1
  · exact Or.inl h.1
  · exact Or.inr h.1
  · exact Or.inr h.1
  · exact Or.inr h.1

/-- Excluding the all-double five-block face supplies the moment consumed by
`fiveBlock_unique_disjoint_pair_outsider_degree_three_of_five`. -/
theorem elevenFive_c40_l11_b5_five_secondMoment_eq_eighteen_of_ne_twenty
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    (cfg : Configuration Point) (hcard : Fintype.card Point = 11)
    (hlocal : ∀ p : Point, ElevenFiveLocalRows (blockSystem cfg) p)
    (hglobal : ElevenFiveGlobalRows (blockSystem cfg))
    (hC : (blockSystem cfg).totalCircleCount = 40)
    (hL : elevenFiveLineTotal (blockSystem cfg) = 11)
    (hfive : (blockSystem cfg).blockCount 5 = 5)
    (hbeta : ∀ p : Point,
      (blockSystem cfg).blockDegree 3 p +
        (blockSystem cfg).blockDegree 4 p +
          (blockSystem cfg).blockDegree 5 p ≤ 18)
    (hnot : elevenFiveSecondMoment (blockSystem cfg) ≠ 20) :
    elevenFiveSecondMoment (blockSystem cfg) = 18 := by
  rcases elevenFive_c40_l11_b5_five_secondMoment_eq_eighteen_or_twenty
    cfg hcard hlocal hglobal hC hL hfive hbeta with h | h
  · exact h
  · exact False.elim (hnot h)

/-- Excluding the all-double six-block face supplies the moment consumed by
`fiveBlock_unique_disjoint_pair_outsider_degree_four_of_six`. -/
theorem elevenFive_c40_l11_b5_six_secondMoment_eq_twentyEight_of_ne_thirty
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    (cfg : Configuration Point) (hcard : Fintype.card Point = 11)
    (hlocal : ∀ p : Point, ElevenFiveLocalRows (blockSystem cfg) p)
    (hglobal : ElevenFiveGlobalRows (blockSystem cfg))
    (hC : (blockSystem cfg).totalCircleCount = 40)
    (hL : elevenFiveLineTotal (blockSystem cfg) = 11)
    (hfive : (blockSystem cfg).blockCount 5 = 6)
    (hbeta : ∀ p : Point,
      (blockSystem cfg).blockDegree 3 p +
        (blockSystem cfg).blockDegree 4 p +
          (blockSystem cfg).blockDegree 5 p ≤ 18)
    (hnot : elevenFiveSecondMoment (blockSystem cfg) ≠ 30) :
    elevenFiveSecondMoment (blockSystem cfg) = 28 := by
  rcases elevenFive_c40_l11_b5_six_secondMoment_eq_twentyEight_or_thirty
    cfg hcard hlocal hglobal hC hL hfive hbeta with h | h
  · exact h
  · exact False.elim (hnot h)

end Erdos506.V1
