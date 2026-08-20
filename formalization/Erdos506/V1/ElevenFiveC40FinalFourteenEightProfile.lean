import Erdos506.V1.ElevenFiveC40FinalBetaCapCount

/-!
# The first finite census of the C40 `L = 14, B₅ = 8` face

The new pivot-inversion count gives the sharp local beta cap in this row.
Before using that cap to force the five-degree profile, the global rows
already determine the exact three- and four-block census and the distribution
of the three-block degrees.  This file records those reusable finite facts.
-/

namespace Erdos506.V1

open Erdos506.Block
open Erdos506.Block.BlockSystem
open Erdos506.Incidence
open Erdos506.V4
open scoped BigOperators

universe u v

/-- The `C = 40, L = 14, B₅ = 8` global rows fix the remaining block
counts. -/
theorem elevenFive_c40_l14_eightDefect_block_census
    {Point : Type u} {Block : Type v} [Fintype Point] [Fintype Block]
    [DecidableEq Point]
    (S : BlockSystem Point Block) (hglobal : ElevenFiveGlobalRows S)
    (hC : S.totalCircleCount = 40)
    (hL : elevenFiveLineTotal S = 14)
    (hfive : S.blockCount 5 = 8) :
    S.blockCount 3 = 33 ∧ S.blockCount 4 = 13 := by
  have htriple := hglobal.tripleRow
  have htotal := hglobal.blockTotal
  rw [hC, hL, hfive] at htotal
  rw [hfive] at htriple
  omega

/-- In the same row, write `u` for the number of degree-twelve
three-block pivots.  The three-block incidence sum gives
`n₆ = n₁₂ = u` and `n₉ = 11 - 2u`. -/
theorem elevenFive_c40_l14_eightDefect_threeDegree_census
    {Point : Type u} {Block : Type v} [Fintype Point] [Fintype Block]
    [DecidableEq Point]
    (S : BlockSystem Point Block) (hcard : Fintype.card Point = 11)
    (hlocal : ∀ p : Point, ElevenFiveLocalRows S p)
    (hglobal : ElevenFiveGlobalRows S)
    (hC : S.totalCircleCount = 40)
    (hL : elevenFiveLineTotal S = 14)
    (hfive : S.blockCount 5 = 8) :
    ((Finset.univ : Finset Point).filter
        fun p => S.blockDegree 3 p = 6).card =
      ((Finset.univ : Finset Point).filter
        fun p => S.blockDegree 3 p = 12).card ∧
      ((Finset.univ : Finset Point).filter
        fun p => S.blockDegree 3 p = 9).card =
        11 - 2 * ((Finset.univ : Finset Point).filter
          fun p => S.blockDegree 3 p = 12).card ∧
      ∀ p : Point, S.blockDegree 3 p = 6 ∨
        S.blockDegree 3 p = 9 ∨ S.blockDegree 3 p = 12 := by
  classical
  obtain ⟨hthreeCount, _hfourCount⟩ :=
    elevenFive_c40_l14_eightDefect_block_census
      S hglobal hC hL hfive
  have hthreeSum : (∑ p : Point, S.blockDegree 3 p) = 99 := by
    rw [hglobal.threeIncidence, hthreeCount]
  have hvalues (p : Point) : S.blockDegree 3 p = 6 ∨
      S.blockDegree 3 p = 9 ∨ S.blockDegree 3 p = 12 :=
    elevenFive_c40_threeDegree_values S p (hlocal p) hC
  let N6 := (Finset.univ : Finset Point).filter
    fun p => S.blockDegree 3 p = 6
  let N9 := (Finset.univ : Finset Point).filter
    fun p => S.blockDegree 3 p = 9
  let N12 := (Finset.univ : Finset Point).filter
    fun p => S.blockDegree 3 p = 12
  have hN6sum : (∑ p : Point, if p ∈ N6 then 1 else 0) = N6.card := by
    simp [N6]
  have hN9sum : (∑ p : Point, if p ∈ N9 then 1 else 0) = N9.card := by
    simp [N9]
  have hN12sum : (∑ p : Point, if p ∈ N12 then 1 else 0) = N12.card := by
    simp [N12]
  have hdegreePoint (p : Point) : S.blockDegree 3 p =
      6 + 3 * (if p ∈ N9 then 1 else 0) +
        6 * (if p ∈ N12 then 1 else 0) := by
    rcases hvalues p with h6 | h9 | h12
    · simp [N9, N12, h6]
    · simp [N9, N12, h9]
    · simp [N9, N12, h12]
  have hdegreeSum :
      (∑ p : Point, S.blockDegree 3 p) =
        ∑ p : Point, (6 + 3 * (if p ∈ N9 then 1 else 0) +
          6 * (if p ∈ N12 then 1 else 0)) := by
    apply Finset.sum_congr rfl
    intro p _hp
    exact hdegreePoint p
  have hN9N12 : 3 * N9.card + 6 * N12.card = 33 := by
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
      ← Finset.mul_sum, ← Finset.mul_sum, hN9sum, hN12sum,
      Finset.sum_const, Finset.card_univ, hcard, hthreeSum] at hdegreeSum
    norm_num at hdegreeSum
    omega
  have hpartitionPoint (p : Point) :
      (if p ∈ N6 then 1 else 0) +
        (if p ∈ N9 then 1 else 0) +
          (if p ∈ N12 then 1 else 0) = 1 := by
    rcases hvalues p with h6 | h9 | h12
    · simp [N6, N9, N12, h6]
    · simp [N6, N9, N12, h9]
    · simp [N6, N9, N12, h12]
  have hpartitionSum :
      (∑ p : Point, ((if p ∈ N6 then 1 else 0) +
        (if p ∈ N9 then 1 else 0) +
          (if p ∈ N12 then 1 else 0))) = ∑ _p : Point, 1 := by
    apply Finset.sum_congr rfl
    intro p _hp
    exact hpartitionPoint p
  have hpartition : N6.card + N9.card + N12.card = 11 := by
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
      hN6sum, hN9sum, hN12sum, Finset.sum_const,
      Finset.card_univ, hcard] at hpartitionSum
    norm_num at hpartitionSum
    exact hpartitionSum
  change N6.card = N12.card ∧
    N9.card = 11 - 2 * N12.card ∧ ∀ p : Point,
      S.blockDegree 3 p = 6 ∨ S.blockDegree 3 p = 9 ∨
        S.blockDegree 3 p = 12
  refine ⟨by omega, by omega, hvalues⟩

/-- The pivot-inversion cap and the harmonic incidence cap leave only three
or four degree-twelve three-block pivots in the `L = 14, B₅ = 8` row. -/
theorem elevenFive_c40_l14_eightDefect_degreeTwelve_card_three_or_four
    {Point : Type u} {Block : Type v} [Fintype Point] [Fintype Block]
    [DecidableEq Point]
    (S : BlockSystem Point Block) (hcard : Fintype.card Point = 11)
    (hlocal : ∀ p : Point, ElevenFiveLocalRows S p)
    (hglobal : ElevenFiveGlobalRows S)
    (hC : S.totalCircleCount = 40)
    (hL : elevenFiveLineTotal S = 14)
    (hfive : S.blockCount 5 = 8)
    (hbeta : ∀ p : Point, S.blockDegree 3 p + S.blockDegree 4 p +
      S.blockDegree 5 p ≤ 21)
    (hharmonic : 4 * (elevenFiveHarmonicPivots S).card ≤
      2 * S.blockCount 5) :
    ((Finset.univ : Finset Point).filter
      fun p => S.blockDegree 3 p = 12).card = 3 ∨
      ((Finset.univ : Finset Point).filter
        fun p => S.blockDegree 3 p = 12).card = 4 := by
  classical
  obtain ⟨hN6U, _hN9, hvalues⟩ :=
    elevenFive_c40_l14_eightDefect_threeDegree_census
      S hcard hlocal hglobal hC hL hfive
  let U := (Finset.univ : Finset Point).filter
    fun p => S.blockDegree 3 p = 12
  let N6 := (Finset.univ : Finset Point).filter
    fun p => S.blockDegree 3 p = 6
  let H := elevenFiveHarmonicPivots S
  have hN6U' : N6.card = U.card := by
    simpa [N6, U] using hN6U
  have hUindicator :
      (∑ p : Point, if p ∈ U then 1 else 0) = U.card := by
    simp [U]
  have hN6indicator :
      (∑ p : Point, if p ∈ N6 then 1 else 0) = N6.card := by
    simp [N6]
  have hHindicator :
      (∑ p : Point, if p ∈ H then 1 else 0) = H.card := by
    simp [H]
  have hfiveSum : (∑ p : Point, S.blockDegree 5 p) = 40 := by
    rw [hglobal.fiveIncidence, hfive]
  have hdegreeTwelveLower (p : Point)
      (h12 : S.blockDegree 3 p = 12) : 2 ≤ S.blockDegree 5 p := by
    have hpair := (hlocal p).pairRow
    have hpivot := hbeta p
    omega
  have hfiveUpper (p : Point) : S.blockDegree 5 p ≤
      3 + (if p ∈ U then 1 else 0) +
        (if p ∈ H then 1 else 0) := by
    rcases hvalues p with h6 | h9 | h12
    · have hlanger := (hlocal p).langer
      have hle : S.blockDegree 5 p ≤ 3 := by omega
      simpa [U, H, elevenFiveHarmonicPivots, h6] using hle
    · by_cases hpH : p ∈ H
      · have hcap := (hlocal p).fiveDegreeCap
        have hpU : p ∉ U := by simp [U, h9]
        simpa [hpH, hpU] using hcap
      · have hle : S.blockDegree 5 p ≤ 3 := by
          by_contra hnot
          have hcap := (hlocal p).fiveDegreeCap
          have hfour : S.blockDegree 5 p = 4 := by omega
          have hpair := (hlocal p).pairRow
          have hpH' : p ∈ H := by
            simp only [H, elevenFiveHarmonicPivots,
              Finset.mem_filter, Finset.mem_univ, true_and]
            exact ⟨h9, by omega, hfour⟩
          exact hpH hpH'
        have hpU : p ∉ U := by simp [U, h9]
        simpa [hpH, hpU] using hle
    · have hcap := (hlocal p).fiveDegreeCap
      have hlower := hdegreeTwelveLower p h12
      have hle : S.blockDegree 5 p ≤ 4 := by omega
      have hpU : p ∈ U := by simp [U, h12]
      have hpH : p ∉ H := by
        intro hpH
        have hHdata : S.blockDegree 3 p = 9 ∧
            S.blockDegree 4 p = 4 ∧ S.blockDegree 5 p = 4 := by
          simpa [H, elevenFiveHarmonicPivots] using hpH
        omega
      simpa [hpU, hpH] using hle
  have hfiveUpperSum :
      (∑ p : Point, S.blockDegree 5 p) ≤
        ∑ p : Point, (3 + (if p ∈ U then 1 else 0) +
          (if p ∈ H then 1 else 0)) :=
    Finset.sum_le_sum fun p _hp => hfiveUpper p
  have hfiveUpperRight :
      (∑ p : Point, (3 + (if p ∈ U then 1 else 0) +
        (if p ∈ H then 1 else 0))) = 33 + U.card + H.card := by
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
      hUindicator, hHindicator]
    simp [hcard]
  rw [hfiveSum, hfiveUpperRight] at hfiveUpperSum
  have hHcap : 4 * H.card ≤ 16 := by
    simpa [H, hfive] using hharmonic
  have hUlower : 3 ≤ U.card := by omega
  have hfiveMax (p : Point) : S.blockDegree 5 p +
      (if p ∈ N6 then 1 else 0) ≤ 4 := by
    rcases hvalues p with h6 | h9 | h12
    · have hlanger := (hlocal p).langer
      have hle : S.blockDegree 5 p ≤ 3 := by omega
      have hpN6 : p ∈ N6 := by simp [N6, h6]
      simp [hpN6]
      omega
    · have hcap := (hlocal p).fiveDegreeCap
      have hpN6 : p ∉ N6 := by simp [N6, h9]
      simpa [hpN6] using hcap
    · have hcap := (hlocal p).fiveDegreeCap
      have hpN6 : p ∉ N6 := by simp [N6, h12]
      simpa [hpN6] using hcap
  have hfiveMaxSum :
      (∑ p : Point, (S.blockDegree 5 p +
        (if p ∈ N6 then 1 else 0))) ≤ ∑ _p : Point, 4 :=
    Finset.sum_le_sum fun p _hp => hfiveMax p
  have hfiveMaxLeft :
      (∑ p : Point, (S.blockDegree 5 p +
        (if p ∈ N6 then 1 else 0))) = 40 + N6.card := by
    rw [Finset.sum_add_distrib, hfiveSum, hN6indicator]
  have hfiveMaxRight : (∑ _p : Point, 4) = 44 := by
    simp [hcard]
  rw [hfiveMaxLeft, hfiveMaxRight] at hfiveMaxSum
  have hUupper : U.card ≤ 4 := by omega
  change U.card = 3 ∨ U.card = 4
  omega

/-- The two surviving degree-twelve census cases have the same literal
five-block degree profile.  In the `u = 3` case the equality is the
harmonic-cap equality; in the `u = 4` case it is the equality in the
Langer five-degree cap. -/
theorem elevenFive_c40_l14_eightDefect_fiveDegree_profile
    {Point : Type u} {Block : Type v} [Fintype Point] [Fintype Block]
    [DecidableEq Point]
    (S : BlockSystem Point Block) (hcard : Fintype.card Point = 11)
    (hlocal : ∀ p : Point, ElevenFiveLocalRows S p)
    (hglobal : ElevenFiveGlobalRows S)
    (hC : S.totalCircleCount = 40)
    (hL : elevenFiveLineTotal S = 14)
    (hfive : S.blockCount 5 = 8)
    (hbeta : ∀ p : Point, S.blockDegree 3 p + S.blockDegree 4 p +
      S.blockDegree 5 p ≤ 21)
    (hharmonic : 4 * (elevenFiveHarmonicPivots S).card ≤
      2 * S.blockCount 5) :
    ((Finset.univ : Finset Point).filter
      fun p => S.blockDegree 5 p = 4).card = 7 ∧
      ((Finset.univ : Finset Point).filter
        fun p => S.blockDegree 5 p = 3).card = 4 ∧
      (∀ p : Point, S.blockDegree 5 p = 3 ∨ S.blockDegree 5 p = 4) ∧
      ∀ p : Point, S.blockDegree 5 p = 3 →
        S.blockDegree 3 p = 6 ∨ S.blockDegree 3 p = 9 := by
  classical
  obtain ⟨hN6U, _hN9, hvalues⟩ :=
    elevenFive_c40_l14_eightDefect_threeDegree_census
      S hcard hlocal hglobal hC hL hfive
  let U := (Finset.univ : Finset Point).filter
    fun p => S.blockDegree 3 p = 12
  let N6 := (Finset.univ : Finset Point).filter
    fun p => S.blockDegree 3 p = 6
  let H := elevenFiveHarmonicPivots S
  have hN6U' : N6.card = U.card := by
    simpa [N6, U] using hN6U
  have hUindicator :
      (∑ p : Point, if p ∈ U then 1 else 0) = U.card := by
    simp [U]
  have hN6indicator :
      (∑ p : Point, if p ∈ N6 then 1 else 0) = N6.card := by
    simp [N6]
  have hHindicator :
      (∑ p : Point, if p ∈ H then 1 else 0) = H.card := by
    simp [H]
  have hfiveSum : (∑ p : Point, S.blockDegree 5 p) = 40 := by
    rw [hglobal.fiveIncidence, hfive]
  have hdegreeTwelveLower (p : Point)
      (h12 : S.blockDegree 3 p = 12) : 2 ≤ S.blockDegree 5 p := by
    have hpair := (hlocal p).pairRow
    have hpivot := hbeta p
    omega
  have hfiveUpper (p : Point) : S.blockDegree 5 p ≤
      3 + (if p ∈ U then 1 else 0) +
        (if p ∈ H then 1 else 0) := by
    rcases hvalues p with h6 | h9 | h12
    · have hlanger := (hlocal p).langer
      have hle : S.blockDegree 5 p ≤ 3 := by omega
      simpa [U, H, elevenFiveHarmonicPivots, h6] using hle
    · by_cases hpH : p ∈ H
      · have hcap := (hlocal p).fiveDegreeCap
        have hpU : p ∉ U := by simp [U, h9]
        simpa [hpH, hpU] using hcap
      · have hle : S.blockDegree 5 p ≤ 3 := by
          by_contra hnot
          have hcap := (hlocal p).fiveDegreeCap
          have hfour : S.blockDegree 5 p = 4 := by omega
          have hpair := (hlocal p).pairRow
          have hpH' : p ∈ H := by
            simp only [H, elevenFiveHarmonicPivots,
              Finset.mem_filter, Finset.mem_univ, true_and]
            exact ⟨h9, by omega, hfour⟩
          exact hpH hpH'
        have hpU : p ∉ U := by simp [U, h9]
        simpa [hpH, hpU] using hle
    · have hcap := (hlocal p).fiveDegreeCap
      have hlower := hdegreeTwelveLower p h12
      have hle : S.blockDegree 5 p ≤ 4 := by omega
      have hpU : p ∈ U := by simp [U, h12]
      have hpH : p ∉ H := by
        intro hpH
        have hHdata : S.blockDegree 3 p = 9 ∧
            S.blockDegree 4 p = 4 ∧ S.blockDegree 5 p = 4 := by
          simpa [H, elevenFiveHarmonicPivots] using hpH
        omega
      simpa [hpU, hpH] using hle
  have hfiveUpperSum :
      (∑ p : Point, S.blockDegree 5 p) ≤
        ∑ p : Point, (3 + (if p ∈ U then 1 else 0) +
          (if p ∈ H then 1 else 0)) :=
    Finset.sum_le_sum fun p _hp => hfiveUpper p
  have hfiveUpperRight :
      (∑ p : Point, (3 + (if p ∈ U then 1 else 0) +
        (if p ∈ H then 1 else 0))) = 33 + U.card + H.card := by
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
      hUindicator, hHindicator]
    simp [hcard]
  have hfiveMax (p : Point) : S.blockDegree 5 p +
      (if p ∈ N6 then 1 else 0) ≤ 4 := by
    rcases hvalues p with h6 | h9 | h12
    · have hlanger := (hlocal p).langer
      have hle : S.blockDegree 5 p ≤ 3 := by omega
      have hpN6 : p ∈ N6 := by simp [N6, h6]
      simp [hpN6]
      omega
    · have hcap := (hlocal p).fiveDegreeCap
      have hpN6 : p ∉ N6 := by simp [N6, h9]
      simpa [hpN6] using hcap
    · have hcap := (hlocal p).fiveDegreeCap
      have hpN6 : p ∉ N6 := by simp [N6, h12]
      simpa [hpN6] using hcap
  have hfiveMaxSum :
      (∑ p : Point, (S.blockDegree 5 p +
        (if p ∈ N6 then 1 else 0))) ≤ ∑ _p : Point, 4 :=
    Finset.sum_le_sum fun p _hp => hfiveMax p
  have hfiveMaxLeft :
      (∑ p : Point, (S.blockDegree 5 p +
        (if p ∈ N6 then 1 else 0))) = 40 + N6.card := by
    rw [Finset.sum_add_distrib, hfiveSum, hN6indicator]
  have hfiveMaxRight : (∑ _p : Point, 4) = 44 := by
    simp [hcard]
  obtain hUthree | hUfour :=
    elevenFive_c40_l14_eightDefect_degreeTwelve_card_three_or_four
      S hcard hlocal hglobal hC hL hfive hbeta hharmonic
  · have hUthree' : U.card = 3 := by simpa [U] using hUthree
    have hHcap : 4 * H.card ≤ 16 := by
      simpa [H, hfive] using hharmonic
    have hHlower : 4 ≤ H.card := by
      rw [hfiveSum, hfiveUpperRight, hUthree'] at hfiveUpperSum
      omega
    have hHfour : H.card = 4 := by omega
    have hsumEq : (∑ p : Point, S.blockDegree 5 p) =
        ∑ p : Point, (3 + (if p ∈ U then 1 else 0) +
          (if p ∈ H then 1 else 0)) := by
      rw [hfiveSum, hfiveUpperRight, hUthree', hHfour]
    have hall := (Finset.sum_eq_sum_iff_of_le
      fun p _hp => hfiveUpper p).mp hsumEq
    have heq (p : Point) : S.blockDegree 5 p =
        3 + (if p ∈ U then 1 else 0) +
          (if p ∈ H then 1 else 0) :=
      hall p (Finset.mem_univ p)
    have hUH (p : Point) (hpU : p ∈ U) : p ∉ H := by
      intro hpH
      have hUdata : S.blockDegree 3 p = 12 := by
        simpa [U] using hpU
      have hHdata : S.blockDegree 3 p = 9 ∧
          S.blockDegree 4 p = 4 ∧ S.blockDegree 5 p = 4 := by
        simpa [H, elevenFiveHarmonicPivots] using hpH
      omega
    have hHU (p : Point) (hpH : p ∈ H) : p ∉ U := by
      intro hpU
      exact hUH p hpU hpH
    have hfourIff (p : Point) : S.blockDegree 5 p = 4 ↔
        p ∈ U ∨ p ∈ H := by
      constructor
      · intro hfour
        by_cases hpU : p ∈ U
        · exact Or.inl hpU
        · by_cases hpH : p ∈ H
          · exact Or.inr hpH
          · have hp := heq p
            simp [hpU, hpH, hfour] at hp
      · intro hp
        rcases hp with hpU | hpH
        · have hpH' := hUH p hpU
          rw [heq p]
          simp [hpU, hpH']
        · have hpU' := hHU p hpH
          rw [heq p]
          simp [hpU', hpH]
    have hthreeIff (p : Point) : S.blockDegree 5 p = 3 ↔
        p ∉ U ∧ p ∉ H := by
      constructor
      · intro hthree
        constructor
        · intro hpU
          have hpH := hUH p hpU
          have hp := heq p
          simp [hpU, hpH, hthree] at hp
        · intro hpH
          have hpU := hHU p hpH
          have hp := heq p
          simp [hpU, hpH, hthree] at hp
      · rintro ⟨hpU, hpH⟩
        rw [heq p]
        simp [hpU, hpH]
    have hfourSet : ((Finset.univ : Finset Point).filter
        fun p => S.blockDegree 5 p = 4) = U ∪ H := by
      ext p
      simp only [Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_union]
      exact hfourIff p
    have hUHdisjoint : Disjoint U H := by
      rw [Finset.disjoint_left]
      intro p hpU hpH
      exact hUH p hpU hpH
    have hfour : ((Finset.univ : Finset Point).filter
        fun p => S.blockDegree 5 p = 4).card = 7 := by
      rw [hfourSet, Finset.card_union_of_disjoint hUHdisjoint,
        hUthree', hHfour]
    have hprofile (p : Point) : S.blockDegree 5 p = 3 ∨
        S.blockDegree 5 p = 4 := by
      by_cases hpU : p ∈ U
      · exact Or.inr ((hfourIff p).mpr (Or.inl hpU))
      · by_cases hpH : p ∈ H
        · exact Or.inr ((hfourIff p).mpr (Or.inr hpH))
        · exact Or.inl ((hthreeIff p).mpr ⟨hpU, hpH⟩)
    have hnotFourIff (p : Point) : ¬ S.blockDegree 5 p = 4 ↔
        S.blockDegree 5 p = 3 := by
      constructor
      · intro hnot
        rcases hprofile p with hthree | hfour'
        · exact hthree
        · exact False.elim (hnot hfour')
      · intro hthree hfour'
        omega
    have hthreeSet : ((Finset.univ : Finset Point).filter
        fun p => S.blockDegree 5 p = 3) =
        (Finset.univ : Finset Point).filter
          fun p => ¬ S.blockDegree 5 p = 4 := by
      ext p
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact (hnotFourIff p).symm
    have hpartition := Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset Point))
      (p := fun p => S.blockDegree 5 p = 4)
    have hthree : ((Finset.univ : Finset Point).filter
        fun p => S.blockDegree 5 p = 3).card = 4 := by
      rw [← hthreeSet, hfour, Finset.card_univ, hcard] at hpartition
      omega
    have hcarrier (p : Point) (hthree' : S.blockDegree 5 p = 3) :
        S.blockDegree 3 p = 6 ∨ S.blockDegree 3 p = 9 := by
      have hp := (hthreeIff p).mp hthree'
      rcases hvalues p with h6 | h9 | h12
      · exact Or.inl h6
      · exact Or.inr h9
      · have hpU : p ∈ U := by simp [U, h12]
        exact False.elim (hp.1 hpU)
    exact ⟨hfour, hthree, hprofile, hcarrier⟩
  · have hUfour' : U.card = 4 := by simpa [U] using hUfour
    have hN6four : N6.card = 4 := by
      rw [hN6U', hUfour']
    have hsumEq :
        (∑ p : Point, (S.blockDegree 5 p +
          (if p ∈ N6 then 1 else 0))) = ∑ _p : Point, 4 := by
      rw [hfiveMaxLeft, hN6four, hfiveMaxRight]
    have hall := (Finset.sum_eq_sum_iff_of_le
      fun p _hp => hfiveMax p).mp hsumEq
    have heq (p : Point) : S.blockDegree 5 p +
        (if p ∈ N6 then 1 else 0) = 4 :=
      hall p (Finset.mem_univ p)
    have hthreeIff (p : Point) : S.blockDegree 5 p = 3 ↔ p ∈ N6 := by
      constructor
      · intro hthree
        by_contra hpN6
        have hp := heq p
        simp [hpN6, hthree] at hp
      · intro hpN6
        have hp := heq p
        simp [hpN6] at hp
        omega
    have hfourIff (p : Point) : S.blockDegree 5 p = 4 ↔ p ∉ N6 := by
      constructor
      · intro hfour
        intro hpN6
        have hp := heq p
        simp [hpN6, hfour] at hp
      · intro hpN6
        have hp := heq p
        simp [hpN6] at hp
        omega
    have hthreeSet : ((Finset.univ : Finset Point).filter
        fun p => S.blockDegree 5 p = 3) = N6 := by
      ext p
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact hthreeIff p
    have hthree : ((Finset.univ : Finset Point).filter
        fun p => S.blockDegree 5 p = 3).card = 4 := by
      rw [hthreeSet, hN6four]
    have hprofile (p : Point) : S.blockDegree 5 p = 3 ∨
        S.blockDegree 5 p = 4 := by
      by_cases hpN6 : p ∈ N6
      · exact Or.inl ((hthreeIff p).mpr hpN6)
      · exact Or.inr ((hfourIff p).mpr hpN6)
    have hnotFourSet :
        (Finset.univ : Finset Point).filter
          (fun p => ¬ S.blockDegree 5 p = 4) =
        (Finset.univ : Finset Point).filter
          (fun p => S.blockDegree 5 p = 3) := by
      ext p
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · intro hnot
        rcases hprofile p with hthree' | hfour'
        · exact hthree'
        · exact False.elim (hnot hfour')
      · intro hthree' hfour'
        omega
    have hpartition := Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset Point))
      (p := fun p => S.blockDegree 5 p = 4)
    have hfour : ((Finset.univ : Finset Point).filter
        fun p => S.blockDegree 5 p = 4).card = 7 := by
      rw [hnotFourSet, hthree, Finset.card_univ, hcard] at hpartition
      omega
    have hcarrier (p : Point) (hthree' : S.blockDegree 5 p = 3) :
        S.blockDegree 3 p = 6 ∨ S.blockDegree 3 p = 9 := by
      have hpN6 := (hthreeIff p).mp hthree'
      exact Or.inl (by simpa [N6] using hpN6)
    exact ⟨hfour, hthree, hprofile, hcarrier⟩

end Erdos506.V1
