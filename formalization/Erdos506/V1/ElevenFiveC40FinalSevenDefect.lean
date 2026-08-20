import Erdos506.V1.ElevenFiveC40FinalPairDefect
import Erdos506.V1.ElevenFiveLineTraceComparison

/-!
# First global seven-defect census for C40, L = 11

This module exposes the numerical part of the `B5 = 7` row which was
previously only used inside the terminal C40 router.  It is the common
entrance to the two five-degree faces `4^2 3^9` and `4^3 3^7 2`.
-/

namespace Erdos506.V1

open Erdos506.Block
open Erdos506.Block.BlockSystem
open Erdos506.Incidence
open Erdos506.V4
open scoped BigOperators

universe u v

/-- In the C40 `L = 11, B5 = 7` row there are exactly five degree-nine
three-block pivots; all remaining pivots have three-degree six. -/
theorem elevenFive_c40_l11_sevenDefect_threeDegree_census
    {Point Block : Type*} [Fintype Point] [Fintype Block]
    [DecidableEq Point]
    (S : BlockSystem Point Block) (hcard : Fintype.card Point = 11)
    (hlocal : ∀ p : Point, ElevenFiveLocalRows S p)
    (hglobal : ElevenFiveGlobalRows S)
    (hC : S.totalCircleCount = 40)
    (hL : elevenFiveLineTotal S = 11)
    (hfive : S.blockCount 5 = 7)
    (hbeta : ∀ p : Point,
      S.blockDegree 3 p + S.blockDegree 4 p + S.blockDegree 5 p ≤ 18) :
    ((Finset.univ : Finset Point).filter
      fun p => S.blockDegree 3 p = 9).card = 5 ∧
      ∀ p : Point, S.blockDegree 3 p = 6 ∨ S.blockDegree 3 p = 9 := by
  classical
  have htriple := hglobal.tripleRow
  have htotal := hglobal.blockTotal
  have hthreeCount : S.blockCount 3 = 27 := by
    rw [hfive] at htriple
    rw [hC, hL] at htotal
    omega
  have hthreeSum : (∑ p : Point, S.blockDegree 3 p) = 81 := by
    rw [hglobal.threeIncidence, hthreeCount]
  have hvalues (p : Point) :
      S.blockDegree 3 p = 6 ∨ S.blockDegree 3 p = 9 := by
    have hpair := (hlocal p).pairRow
    have hfiveCap := (hlocal p).fiveDegreeCap
    rcases elevenFive_c40_threeDegree_values S p (hlocal p) hC with
      h6 | h9 | h12
    · exact Or.inl h6
    · exact Or.inr h9
    · have hpivot := hbeta p
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
  · simpa [H] using (show H.card = 5 by omega)
  · exact hvalues

/-! ## Harmonic excess and the odd seven-defect face -/

/-- Under the C40 beta cap, a five-degree can exceed three only at a
harmonic `(9,4,4)` pivot.  This is the pointwise form needed to turn the
five-incidence row into a small finite profile census. -/
theorem elevenFive_c40_l11_fiveDegree_le_three_add_harmonic
    {Point Block : Type*} [Fintype Point] [Fintype Block]
    [DecidableEq Point]
    (S : BlockSystem Point Block) (p : Point)
    (hlocal : ElevenFiveLocalRows S p)
    (hC : S.totalCircleCount = 40)
    (hbeta : S.blockDegree 3 p + S.blockDegree 4 p +
      S.blockDegree 5 p <= 18) :
    S.blockDegree 5 p <=
      3 + (if p ∈ elevenFiveHarmonicPivots S then 1 else 0) := by
  classical
  have hvalues := elevenFive_c40_threeDegree_values S p hlocal hC
  have hpair := hlocal.pairRow
  have hlanger := hlocal.langer
  have hfive := hlocal.fiveDegreeCap
  by_cases hm : p ∈ elevenFiveHarmonicPivots S
  · simp [hm]
    exact hfive
  · simp only [hm, if_false]
    have hnotProfile :
        ¬ (S.blockDegree 3 p = 9 /\ S.blockDegree 4 p = 4 /\
          S.blockDegree 5 p = 4) := by
      simpa only [elevenFiveHarmonicPivots, Finset.mem_filter,
        Finset.mem_univ, true_and] using hm
    rcases hvalues with h6 | h9 | h12 <;> omega

/-- The C40 seven-five row has at least two harmonic pivots.  This is just
the five-incidence total `35` compared with the pointwise harmonic excess
bound. -/
theorem elevenFive_c40_l11_sevenDefect_harmonic_card_ge_two
    {Point Block : Type*} [Fintype Point] [Fintype Block]
    [DecidableEq Point]
    (S : BlockSystem Point Block) (hcard : Fintype.card Point = 11)
    (hglobal : ElevenFiveGlobalRows S) (hfive : S.blockCount 5 = 7)
    (hbound : ∀ p : Point, S.blockDegree 5 p <=
      3 + (if p ∈ elevenFiveHarmonicPivots S then 1 else 0)) :
    2 <= (elevenFiveHarmonicPivots S).card := by
  classical
  have hsum :
      (∑ p : Point, S.blockDegree 5 p) <=
        ∑ p : Point,
          (3 + (if p ∈ elevenFiveHarmonicPivots S then 1 else 0)) :=
    Finset.sum_le_sum fun p _hp => hbound p
  have hindicator :
      (∑ p : Point,
        (if p ∈ elevenFiveHarmonicPivots S then 1 else 0)) =
          (elevenFiveHarmonicPivots S).card := by
    simp
  rw [hglobal.fiveIncidence, Finset.sum_add_distrib, hindicator] at hsum
  simp [hcard, hfive] at hsum
  omega

/-- Combining the actual harmonic incidence cap with the preceding excess
count leaves precisely the two cardinalities `2` and `3`. -/
theorem elevenFive_c40_l11_sevenDefect_harmonic_card_two_or_three
    {Point Block : Type*} [Fintype Point] [Fintype Block]
    [DecidableEq Point]
    (S : BlockSystem Point Block) (hcard : Fintype.card Point = 11)
    (hglobal : ElevenFiveGlobalRows S) (hfive : S.blockCount 5 = 7)
    (hbound : ∀ p : Point, S.blockDegree 5 p <=
      3 + (if p ∈ elevenFiveHarmonicPivots S then 1 else 0))
    (hharmonic : 4 * (elevenFiveHarmonicPivots S).card <=
      2 * S.blockCount 5) :
    (elevenFiveHarmonicPivots S).card = 2 ∨
      (elevenFiveHarmonicPivots S).card = 3 := by
  have hlower := elevenFive_c40_l11_sevenDefect_harmonic_card_ge_two
    S hcard hglobal hfive hbound
  have hupper : (elevenFiveHarmonicPivots S).card <= 3 := by
    rw [hfive] at hharmonic
    omega
  omega

/-- If exactly two harmonic pivots occur, equality in the five-incidence
bound forces the literal degree profile `4² 3⁹`. -/
theorem elevenFive_c40_l11_harmonic_two_fiveDegree_profile
    {Point Block : Type*} [Fintype Point] [Fintype Block]
    [DecidableEq Point]
    (S : BlockSystem Point Block) (hcard : Fintype.card Point = 11)
    (hglobal : ElevenFiveGlobalRows S) (hfive : S.blockCount 5 = 7)
    (hbound : ∀ p : Point, S.blockDegree 5 p <=
      3 + (if p ∈ elevenFiveHarmonicPivots S then 1 else 0))
    (hharmonic : (elevenFiveHarmonicPivots S).card = 2) :
    ((Finset.univ : Finset Point).filter
      fun p => S.blockDegree 5 p = 4).card = 2 ∧
      ∀ p : Point, S.blockDegree 5 p = 3 ∨ S.blockDegree 5 p = 4 := by
  classical
  have hleft : (∑ p : Point, S.blockDegree 5 p) = 35 := by
    rw [hglobal.fiveIncidence, hfive]
  have hindicator :
      (∑ p : Point,
        (if p ∈ elevenFiveHarmonicPivots S then 1 else 0)) =
          (elevenFiveHarmonicPivots S).card := by
    simp
  have hright :
      (∑ p : Point,
        (3 + (if p ∈ elevenFiveHarmonicPivots S then 1 else 0))) = 35 := by
    rw [Finset.sum_add_distrib, hindicator]
    simp [hcard, hharmonic]
  have hsum :
      (∑ p : Point, S.blockDegree 5 p) =
        ∑ p : Point,
          (3 + (if p ∈ elevenFiveHarmonicPivots S then 1 else 0)) :=
    hleft.trans hright.symm
  have heq (p : Point) : S.blockDegree 5 p =
      3 + (if p ∈ elevenFiveHarmonicPivots S then 1 else 0) :=
    (Finset.sum_eq_sum_iff_of_le
      (fun x (_hx : x ∈ (Finset.univ : Finset Point)) => hbound x)).mp
        hsum p (Finset.mem_univ p)
  have hprofile (p : Point) :
      S.blockDegree 5 p = 3 ∨ S.blockDegree 5 p = 4 := by
    rw [heq p]
    by_cases hp : p ∈ elevenFiveHarmonicPivots S <;> simp [hp]
  have hset :
      ((Finset.univ : Finset Point).filter
        fun p => S.blockDegree 5 p = 4) = elevenFiveHarmonicPivots S := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [heq p]
    by_cases hp : p ∈ elevenFiveHarmonicPivots S <;> simp [hp]
  constructor
  · rw [hset, hharmonic]
  · exact hprofile

/-- The harmonic-card-two subface of the actual C40 `L = 11, B₅ = 7` row is
impossible: its forced `4²3⁹` profile has odd second moment and hence a
singleton five-block intersection. -/
theorem elevenFive_c40_l11_sevenDefect_harmonic_two_impossible
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    (cfg : Configuration Point) (hcard : Fintype.card Point = 11)
    (hlocal : ∀ p : Point, ElevenFiveLocalRows (blockSystem cfg) p)
    (hglobal : ElevenFiveGlobalRows (blockSystem cfg))
    (hC : (blockSystem cfg).totalCircleCount = 40)
    (hfive : (blockSystem cfg).blockCount 5 = 7)
    (hbeta : ∀ p : Point,
      (blockSystem cfg).blockDegree 3 p +
          (blockSystem cfg).blockDegree 4 p +
            (blockSystem cfg).blockDegree 5 p <= 18)
    (hH : (elevenFiveHarmonicPivots (blockSystem cfg)).card = 2) : False := by
  have hbound : ∀ p : Point, (blockSystem cfg).blockDegree 5 p <=
      3 + (if p ∈ elevenFiveHarmonicPivots (blockSystem cfg) then 1 else 0) := by
    intro p
    exact elevenFive_c40_l11_fiveDegree_le_three_add_harmonic
      (blockSystem cfg) p (hlocal p) hC (hbeta p)
  obtain ⟨hfour, hprofile⟩ :=
    elevenFive_c40_l11_harmonic_two_fiveDegree_profile
      (blockSystem cfg) hcard hglobal hfive hbound hH
  exact elevenFive_c40_l11_four_three_fiveDegree_profile_impossible
    cfg hcard hlocal hC hbeta hfour hprofile

/-- The harmonic cap is already fully geometric, so the actual seven-defect
row has only the surviving cardinal-three face after the preceding theorem. -/
theorem elevenFive_c40_l11_sevenDefect_harmonic_card_two_or_three_of_configuration
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    (cfg : Configuration Point) (hcard : Fintype.card Point = 11)
    (hlocal : ∀ p : Point, ElevenFiveLocalRows (blockSystem cfg) p)
    (hglobal : ElevenFiveGlobalRows (blockSystem cfg))
    (hC : (blockSystem cfg).totalCircleCount = 40)
    (hfive : (blockSystem cfg).blockCount 5 = 7)
    (hbeta : ∀ p : Point,
      (blockSystem cfg).blockDegree 3 p +
          (blockSystem cfg).blockDegree 4 p +
            (blockSystem cfg).blockDegree 5 p <= 18) :
    (elevenFiveHarmonicPivots (blockSystem cfg)).card = 2 ∨
      (elevenFiveHarmonicPivots (blockSystem cfg)).card = 3 := by
  have hbound : ∀ p : Point, (blockSystem cfg).blockDegree 5 p <=
      3 + (if p ∈ elevenFiveHarmonicPivots (blockSystem cfg) then 1 else 0) := by
    intro p
    exact elevenFive_c40_l11_fiveDegree_le_three_add_harmonic
      (blockSystem cfg) p (hlocal p) hC (hbeta p)
  have hharmonic :
      4 * (elevenFiveHarmonicPivots (blockSystem cfg)).card <=
        2 * (blockSystem cfg).blockCount 5 := by
    apply elevenFive_harmonicIncidenceCap_of_normalCircleTraceTransport_and_fiveLineCap
      cfg hcard
    · intro p hp
      exact elevenFive944_normalCircleTraceTransport cfg hcard p hp
    · exact elevenFive944Pivots_fiveLine_cap cfg hcard
  exact elevenFive_c40_l11_sevenDefect_harmonic_card_two_or_three
    (blockSystem cfg) hcard hglobal hfive hbound hharmonic

/-- The cardinal-two alternative is eliminated by its odd pair moment;
therefore the actual C40 seven-defect row has exactly three harmonic
four-star pivots. -/
theorem elevenFive_c40_l11_sevenDefect_harmonic_card_eq_three_of_configuration
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    (cfg : Configuration Point) (hcard : Fintype.card Point = 11)
    (hlocal : ∀ p : Point, ElevenFiveLocalRows (blockSystem cfg) p)
    (hglobal : ElevenFiveGlobalRows (blockSystem cfg))
    (hC : (blockSystem cfg).totalCircleCount = 40)
    (hfive : (blockSystem cfg).blockCount 5 = 7)
    (hbeta : ∀ p : Point,
      (blockSystem cfg).blockDegree 3 p +
          (blockSystem cfg).blockDegree 4 p +
            (blockSystem cfg).blockDegree 5 p <= 18) :
    (elevenFiveHarmonicPivots (blockSystem cfg)).card = 3 := by
  rcases elevenFive_c40_l11_sevenDefect_harmonic_card_two_or_three_of_configuration
    cfg hcard hlocal hglobal hC hfive hbeta with htwo | hthree
  · exact False.elim
      (elevenFive_c40_l11_sevenDefect_harmonic_two_impossible
        cfg hcard hlocal hglobal hC hfive hbeta htwo)
  · exact hthree

end Erdos506.V1
