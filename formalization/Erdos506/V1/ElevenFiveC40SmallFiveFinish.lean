import Erdos506.V1.ElevenFiveC40SmallFinish
import Erdos506.V1.ElevenFiveC40FinalBetaCapCount

/-!
# The C40/L11 five-block small-face front

The local domains, global moments, and completed singleton dispatcher reduce
the `B₅ = 5` row to four numerical faces.  The common two-defect outsider
theorem eliminates one of them without further geometry.  The other three
faces are exposed as one exact residual: its first branch is the actual K2.4
page and its last two branches are the K2.1 triangle-capacity cases.
-/

namespace Erdos506.V1

open Erdos506.Block
open Erdos506.Block.BlockSystem
open Erdos506.Incidence
open Erdos506.V3
open Erdos506.V4
open scoped BigOperators

universe u v

/-- Number of points having a prescribed five-block degree. -/
noncomputable def elevenFiveC40SmallFiveDegreeCount
    {Point : Type u} {Block : Type v} [Fintype Point] [Fintype Block]
    [DecidableEq Point]
    (S : BlockSystem Point Block) (d : ℕ) : ℕ :=
  ((Finset.univ : Finset Point).filter fun p =>
    S.blockDegree 5 p = d).card

/-- The three genuinely geometric faces left after the purely finite
`B₅ = 5` dispatch. -/
def ElevenFiveC40B5FiveGeometricResidual
    {Point : Type u} {Block : Type v} [Fintype Point] [Fintype Block]
    [DecidableEq Point]
    (S : BlockSystem Point Block) : Prop :=
  (elevenFiveSecondMoment S = 18 ∧
      elevenFiveC40SmallFiveDegreeCount S 4 = 0 ∧
      elevenFiveC40SmallFiveDegreeCount S 1 = 1 ∧
      elevenFiveC40SmallFiveDegreeCount S 2 = 6) ∨
    (elevenFiveSecondMoment S = 20 ∧
      elevenFiveC40SmallFiveDegreeCount S 4 = 0 ∧
      elevenFiveC40SmallFiveDegreeCount S 1 = 3 ∧
      elevenFiveC40SmallFiveDegreeCount S 2 = 2) ∨
    (elevenFiveSecondMoment S = 20 ∧
      elevenFiveC40SmallFiveDegreeCount S 4 = 1 ∧
      elevenFiveC40SmallFiveDegreeCount S 1 = 2 ∧
      elevenFiveC40SmallFiveDegreeCount S 2 = 5)

/-- In the C40/L11 `B₅ = 5` row there is exactly one degree-nine
three-block pivot; every other pivot has three-degree six. -/
theorem elevenFive_c40_l11_b5_five_threeDegree_census
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

/-- The five-incidence and pair-moment rows expressed through the literal
degree-one, degree-two, and degree-four census. -/
private theorem elevenFive_c40_smallFive_degree_count_rows
    {Point : Type u} {Block : Type v} [Fintype Point] [Fintype Block]
    [DecidableEq Point]
    (S : BlockSystem Point Block) (hcard : Fintype.card Point = 11)
    (hlocal : ∀ p : Point, ElevenFiveLocalRows S p)
    (hglobal : ElevenFiveGlobalRows S)
    (hC : S.totalCircleCount = 40)
    (hbeta : ∀ p : Point,
      S.blockDegree 3 p + S.blockDegree 4 p + S.blockDegree 5 p ≤ 18) :
    5 * S.blockCount 5 +
        2 * elevenFiveC40SmallFiveDegreeCount S 1 +
          elevenFiveC40SmallFiveDegreeCount S 2 =
      33 + elevenFiveC40SmallFiveDegreeCount S 4 ∧
    elevenFiveSecondMoment S +
        3 * elevenFiveC40SmallFiveDegreeCount S 1 +
          2 * elevenFiveC40SmallFiveDegreeCount S 2 =
      33 + 3 * elevenFiveC40SmallFiveDegreeCount S 4 := by
  classical
  have hdegree (p : Point) :
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
  have hcount (d : ℕ) :
      (∑ p : Point, if S.blockDegree 5 p = d then 1 else 0) =
        elevenFiveC40SmallFiveDegreeCount S d := by
    simp [elevenFiveC40SmallFiveDegreeCount]
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
  constructor
  · calc
      5 * S.blockCount 5 +
            2 * elevenFiveC40SmallFiveDegreeCount S 1 +
              elevenFiveC40SmallFiveDegreeCount S 2 =
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
      _ = 33 + elevenFiveC40SmallFiveDegreeCount S 4 := by
        rw [Finset.sum_add_distrib, hcount 4]
        simp [hcard]
  · calc
      elevenFiveSecondMoment S +
            3 * elevenFiveC40SmallFiveDegreeCount S 1 +
              2 * elevenFiveC40SmallFiveDegreeCount S 2 =
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
      _ = 33 + 3 * elevenFiveC40SmallFiveDegreeCount S 4 := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, hcount 4]
        simp [hcard]

/-- Complete arithmetic face list in the C40/L11 `B₅ = 5` row. -/
theorem elevenFive_c40_l11_b5_five_arithmetic_faces
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
      elevenFiveC40SmallFiveDegreeCount (blockSystem cfg) 4 = 0 ∧
      elevenFiveC40SmallFiveDegreeCount (blockSystem cfg) 1 = 1 ∧
      elevenFiveC40SmallFiveDegreeCount (blockSystem cfg) 2 = 6) ∨
    (elevenFiveSecondMoment (blockSystem cfg) = 18 ∧
      elevenFiveC40SmallFiveDegreeCount (blockSystem cfg) 4 = 1 ∧
      elevenFiveC40SmallFiveDegreeCount (blockSystem cfg) 1 = 0 ∧
      elevenFiveC40SmallFiveDegreeCount (blockSystem cfg) 2 = 9) ∨
    (elevenFiveSecondMoment (blockSystem cfg) = 20 ∧
      elevenFiveC40SmallFiveDegreeCount (blockSystem cfg) 4 = 0 ∧
      elevenFiveC40SmallFiveDegreeCount (blockSystem cfg) 1 = 3 ∧
      elevenFiveC40SmallFiveDegreeCount (blockSystem cfg) 2 = 2) ∨
    (elevenFiveSecondMoment (blockSystem cfg) = 20 ∧
      elevenFiveC40SmallFiveDegreeCount (blockSystem cfg) 4 = 1 ∧
      elevenFiveC40SmallFiveDegreeCount (blockSystem cfg) 1 = 2 ∧
      elevenFiveC40SmallFiveDegreeCount (blockSystem cfg) 2 = 5) := by
  classical
  let S := blockSystem cfg
  obtain ⟨hinc, hmomentRow⟩ :=
    elevenFive_c40_smallFive_degree_count_rows
      S hcard (by simpa [S] using hlocal) (by simpa [S] using hglobal)
        (by simpa [S] using hC) (by simpa [S] using hbeta)
  obtain ⟨hhigh, _hvalues⟩ :=
    elevenFive_c40_l11_b5_five_threeDegree_census
      S hcard (by simpa [S] using hlocal) (by simpa [S] using hglobal)
        (by simpa [S] using hC) (by simpa [S] using hL)
          (by simpa [S] using hfive) (by simpa [S] using hbeta)
  have hfourSub :
      ((Finset.univ : Finset Point).filter fun p =>
          S.blockDegree 5 p = 4) ⊆
        ((Finset.univ : Finset Point).filter fun p =>
          S.blockDegree 3 p = 9) := by
    intro p hp
    have hp4 : S.blockDegree 5 p = 4 := (Finset.mem_filter.mp hp).2
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rcases elevenFive_c40_l11_pivot_domains_of_beta_cap
      S p (hlocal p) hC (hbeta p) with ⟨h6, hlow⟩ | ⟨h9, _hhigh⟩
    · rcases hlow with h1 | h2 | h3 <;> omega
    · exact h9
  have hfourLe := Finset.card_le_card hfourSub
  rw [hhigh] at hfourLe
  have hfourLeOne : elevenFiveC40SmallFiveDegreeCount S 4 ≤ 1 := by
    simpa [elevenFiveC40SmallFiveDegreeCount] using hfourLe
  have hcap := hglobal.secondMomentCap
  rw [hfive] at hinc hcap
  norm_num [Nat.choose] at hinc hcap
  change elevenFiveSecondMoment S ≤ 20 at hcap
  have heven := elevenFive_c40_l11_secondMoment_even
    cfg hcard hlocal hC hbeta
  change Even (elevenFiveSecondMoment S) at heven
  obtain ⟨k, hk⟩ := heven
  have hk' : elevenFiveSecondMoment S = 2 * k := by
    omega
  have hmomentFormula :
      elevenFiveSecondMoment S =
        17 + elevenFiveC40SmallFiveDegreeCount S 1 +
          elevenFiveC40SmallFiveDegreeCount S 4 := by
    omega
  have hfourCases :
      elevenFiveC40SmallFiveDegreeCount S 4 = 0 ∨
        elevenFiveC40SmallFiveDegreeCount S 4 = 1 := by
    omega
  rcases hfourCases with hfourZero | hfourOne
  · rw [hfourZero] at hinc hmomentRow hmomentFormula
    have honeCases :
        elevenFiveC40SmallFiveDegreeCount S 1 = 1 ∨
          elevenFiveC40SmallFiveDegreeCount S 1 = 3 := by
      omega
    rcases honeCases with hone | hone
    · apply Or.inl
      change elevenFiveSecondMoment S = 18 ∧
        elevenFiveC40SmallFiveDegreeCount S 4 = 0 ∧
        elevenFiveC40SmallFiveDegreeCount S 1 = 1 ∧
        elevenFiveC40SmallFiveDegreeCount S 2 = 6
      omega
    · apply Or.inr
      apply Or.inr
      apply Or.inl
      change elevenFiveSecondMoment S = 20 ∧
        elevenFiveC40SmallFiveDegreeCount S 4 = 0 ∧
        elevenFiveC40SmallFiveDegreeCount S 1 = 3 ∧
        elevenFiveC40SmallFiveDegreeCount S 2 = 2
      omega
  · rw [hfourOne] at hinc hmomentRow hmomentFormula
    have honeCases :
        elevenFiveC40SmallFiveDegreeCount S 1 = 0 ∨
          elevenFiveC40SmallFiveDegreeCount S 1 = 2 := by
      have honeLe : elevenFiveC40SmallFiveDegreeCount S 1 ≤ 2 := by
        omega
      interval_cases hone : elevenFiveC40SmallFiveDegreeCount S 1 <;> omega
    rcases honeCases with hone | hone
    · apply Or.inr
      apply Or.inl
      change elevenFiveSecondMoment S = 18 ∧
        elevenFiveC40SmallFiveDegreeCount S 4 = 1 ∧
        elevenFiveC40SmallFiveDegreeCount S 1 = 0 ∧
        elevenFiveC40SmallFiveDegreeCount S 2 = 9
      omega
    · apply Or.inr
      apply Or.inr
      apply Or.inr
      change elevenFiveSecondMoment S = 20 ∧
        elevenFiveC40SmallFiveDegreeCount S 4 = 1 ∧
        elevenFiveC40SmallFiveDegreeCount S 1 = 2 ∧
        elevenFiveC40SmallFiveDegreeCount S 2 = 5
      omega

/-- The apparent face `(a,n₁,n₂)=(1,0,9)` is already finite-impossible.
The two-defect theorem puts the unique degree-three point outside the
disjoint pair, so the degree-four point lies on one endpoint.  Its other
four points all have degree at least two, contradicting the endpoint row
sum `11`. -/
theorem elevenFive_c40_l11_b5_five_four_two_face_impossible
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    (cfg : Configuration Point) (hcard : Fintype.card Point = 11)
    (hlocal : ∀ p : Point, ElevenFiveLocalRows (blockSystem cfg) p)
    (hC : (blockSystem cfg).totalCircleCount = 40)
    (hfive : (blockSystem cfg).blockCount 5 = 5)
    (hbeta : ∀ p : Point,
      (blockSystem cfg).blockDegree 3 p +
        (blockSystem cfg).blockDegree 4 p +
          (blockSystem cfg).blockDegree 5 p ≤ 18)
    (hmoment : elevenFiveSecondMoment (blockSystem cfg) = 18)
    (hfour : elevenFiveC40SmallFiveDegreeCount (blockSystem cfg) 4 = 1)
    (hone : elevenFiveC40SmallFiveDegreeCount (blockSystem cfg) 1 = 0) :
    False := by
  classical
  let S := blockSystem cfg
  have hnoSingleton : ∀ b ∈ S.blocksOfSize 5, ∀ c ∈ S.blocksOfSize 5,
      b ≠ c → (S.support b ∩ S.support c).card ≠ 1 := by
    intro b hb c hc hbc hsingle
    obtain ⟨p, hpEq⟩ := Finset.card_eq_one.mp hsingle
    have hp : p ∈ S.support b ∩ S.support c := by
      rw [hpEq]
      simp
    exact elevenFive_c40_l11_fiveBlock_singleton_impossible
      cfg hcard p (hlocal p) hC (hbeta p) hb hc
        (Finset.mem_inter.mp hp).1 (Finset.mem_inter.mp hp).2
          hbc hsingle
  obtain ⟨f, hf, g, hg, hfg, hdisjoint, _hallDouble, _hunique,
      q, hq, _hqUnique⟩ :=
    fiveBlock_unique_disjoint_pair_outsider_degree_three_of_five
      S hcard (by simpa [S] using hfive)
        (by simpa [S] using hmoment) hnoSingleton
  have hmomentDefect :
      elevenFiveSecondMoment S = 2 * Nat.choose 5 2 - 2 := by
    norm_num [Nat.choose]
    simpa [S] using hmoment
  have hrowF :=
    fiveBlock_support_degree_sum_eq_two_mul_add_one_of_pairMoment_defect_two
      S 5 (by norm_num) (by simpa [S] using hfive)
        hmomentDefect hf hg hfg hdisjoint
  have hdisjointG : (S.support g ∩ S.support f).card = 0 := by
    simpa [Finset.inter_comm] using hdisjoint
  have hrowG :=
    fiveBlock_support_degree_sum_eq_two_mul_add_one_of_pairMoment_defect_two
      S 5 (by norm_num) (by simpa [S] using hfive)
        hmomentDefect hg hf hfg.symm hdisjointG
  have hdegreeLower (x : Point) : 2 ≤ S.blockDegree 5 x := by
    have hnone : S.blockDegree 5 x ≠ 1 := by
      intro hx
      have hmem : x ∈ ((Finset.univ : Finset Point).filter fun p =>
          S.blockDegree 5 p = 1) := by simp [hx]
      have hempty : ((Finset.univ : Finset Point).filter fun p =>
          S.blockDegree 5 p = 1) = ∅ := by
        apply Finset.card_eq_zero.mp
        simpa [S, elevenFiveC40SmallFiveDegreeCount] using hone
      rw [hempty] at hmem
      simp at hmem
    rcases elevenFive_c40_l11_pivot_domains_of_beta_cap
      S x (hlocal x) hC (hbeta x) with ⟨_h6, hlow⟩ | ⟨_h9, hhigh⟩
    · rcases hlow with h1 | h2 | h3 <;> omega
    · rcases hhigh with h3 | h4 <;> omega
  have hfourCard : ((Finset.univ : Finset Point).filter fun p =>
      S.blockDegree 5 p = 4).card = 1 := by
    simpa [S, elevenFiveC40SmallFiveDegreeCount] using hfour
  have hfourPos : 0 < ((Finset.univ : Finset Point).filter fun p =>
      S.blockDegree 5 p = 4).card := by rw [hfourCard]; norm_num
  obtain ⟨p, hpMem⟩ := Finset.card_pos.mp hfourPos
  have hp4 : S.blockDegree 5 p = 4 := (Finset.mem_filter.mp hpMem).2
  have hFGdisjoint : Disjoint (S.support f) (S.support g) := by
    rw [Finset.disjoint_left]
    intro x hxf hxg
    have hx : x ∈ S.support f ∩ S.support g :=
      Finset.mem_inter.mpr ⟨hxf, hxg⟩
    have hempty : S.support f ∩ S.support g = ∅ :=
      Finset.card_eq_zero.mp hdisjoint
    simpa [hempty] using hx
  let V := S.support f ∪ S.support g
  have hVcard : V.card = 10 := by
    dsimp [V]
    rw [Finset.card_union_of_disjoint hFGdisjoint,
      S.mem_blocksOfSize.mp hf, S.mem_blocksOfSize.mp hg]
  have hcomplCard : ((Finset.univ : Finset Point) \ V).card = 1 := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ V),
      Finset.card_univ, hcard, hVcard]
  have hqCompl : q ∈ (Finset.univ : Finset Point) \ V :=
    Finset.mem_sdiff.mpr ⟨Finset.mem_univ q, by simpa [V] using hq.1⟩
  obtain ⟨r, hrEq⟩ := Finset.card_eq_one.mp hcomplCard
  have hqr : q = r := by
    have : q ∈ ({r} : Finset Point) := by
      rw [← hrEq]
      exact hqCompl
    simpa using this
  have hcomplEq : (Finset.univ : Finset Point) \ V = {q} := by
    simpa [hqr] using hrEq
  have hq3 : S.blockDegree 5 q = 3 := hq.2
  have hpq : p ≠ q := by
    intro hpq
    subst p
    have h43 : (4 : ℕ) = 3 := hp4.symm.trans hq3
    norm_num at h43
  have hpV : p ∈ V := by
    by_contra hpNot
    have hpCompl : p ∈ (Finset.univ : Finset Point) \ V :=
      Finset.mem_sdiff.mpr ⟨Finset.mem_univ p, hpNot⟩
    rw [hcomplEq] at hpCompl
    exact hpq (by simpa using hpCompl)
  have endpoint_absurd (b : GeometricBlock cfg)
      (hb : b ∈ S.blocksOfSize 5) (hpb : p ∈ S.support b)
      (hrow : (∑ x ∈ S.support b, S.blockDegree 5 x) = 11) : False := by
    let R := (S.support b).erase p
    have hRcard : R.card = 4 := by
      dsimp [R]
      rw [Finset.card_erase_of_mem hpb, S.mem_blocksOfSize.mp hb]
    have hRlower : 2 * R.card ≤ ∑ x ∈ R, S.blockDegree 5 x := by
      calc
        2 * R.card = ∑ _x ∈ R, 2 := by simp [Nat.mul_comm]
        _ ≤ ∑ x ∈ R, S.blockDegree 5 x :=
          Finset.sum_le_sum fun x _hx => hdegreeLower x
    rw [hRcard] at hRlower
    have hsplit := Finset.sum_erase_add (S.support b)
      (fun x => S.blockDegree 5 x) hpb
    rw [hrow] at hsplit
    change (∑ x ∈ R, S.blockDegree 5 x) + S.blockDegree 5 p = 11 at hsplit
    rw [hp4] at hsplit
    omega
  rcases Finset.mem_union.mp hpV with hpf | hpg
  · exact endpoint_absurd f hf hpf (by norm_num at hrowF ⊢; exact hrowF)
  · exact endpoint_absurd g hg hpg (by norm_num at hrowG ⊢; exact hrowG)

/-- Maximal unconditional `B₅ = 5` front: the finite dispatcher removes
the fourth-degree/two-degree two-defect face and leaves exactly the three
geometric branches recorded in `ElevenFiveC40B5FiveGeometricResidual`. -/
theorem elevenFive_c40_l11_b5_five_reduces_to_geometricResidual
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
    ElevenFiveC40B5FiveGeometricResidual (blockSystem cfg) := by
  rcases elevenFive_c40_l11_b5_five_arithmetic_faces
    cfg hcard hlocal hglobal hC hL hfive hbeta with
      hfirst | hbad | hthird | hfourth
  · exact Or.inl hfirst
  · exact False.elim
      (elevenFive_c40_l11_b5_five_four_two_face_impossible
        cfg hcard hlocal hC hfive hbeta hbad.1 hbad.2.1 hbad.2.2.1)
  · exact Or.inr (Or.inl hthird)
  · exact Or.inr (Or.inr hfourth)

/-- Configuration-level form of the same unconditional reduction. -/
theorem elevenFive_c40_l11_b5_five_geometricResidual_of_configuration
    (Mel : RealPlaneMelchiorPrinciple.{u})
    (Langer : RealPlaneLangerPrinciple.{u})
    (EvenArr : RealPlaneEvenArrangementPrinciple.{u})
    (Cross : RealPlaneRadicalAxisCrossBlockPrinciple.{u})
    (Kelly : RealPlaneKellyMoserPrinciple.{u})
    (U17 : RealPlaneSixCircleU17Principle.{u})
    (TenGeometry : RealPlaneTenFiveGeometry.{u})
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    (cfg : Configuration Point) (hadm : Admissible cfg)
    (hcard : Fintype.card Point = 11)
    (hcap : BlockSizeCap (blockSystem cfg) 5)
    (hC : Erdos506.V4.circleCount cfg = 40)
    (hL : elevenFiveLineTotal (blockSystem cfg) = 11)
    (hfive : (blockSystem cfg).blockCount 5 = 5) :
    ElevenFiveC40B5FiveGeometricResidual (blockSystem cfg) := by
  have hCtotal : (blockSystem cfg).totalCircleCount = 40 := by
    rw [totalCircleCount_eq_card_determinedCircle,
      ← Erdos506.V3.circleCount_eq_card_determinedCircle]
    exact hC
  have hCupper : (blockSystem cfg).totalCircleCount ≤ 40 := by omega
  have hlocal : ∀ p : Point,
      ElevenFiveLocalRows (blockSystem cfg) p := fun p =>
    elevenFiveLocalRows_of_configuration
      Mel Langer EvenArr Cross Kelly U17 TenGeometry
        cfg hadm hcard hcap hCupper p
  have hglobal : ElevenFiveGlobalRows (blockSystem cfg) :=
    elevenFiveGlobalRows_of_configuration Mel cfg hadm hcard hcap hlocal
  have hbeta := elevenFive_c40_l11_beta_cap
    Mel EvenArr Cross Kelly U17 TenGeometry
      cfg hadm hcard hcap hglobal hCtotal hL
  exact elevenFive_c40_l11_b5_five_reduces_to_geometricResidual
    cfg hcard hlocal hglobal hCtotal hL hfive hbeta

end Erdos506.V1
