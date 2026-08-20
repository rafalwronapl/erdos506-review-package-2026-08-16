import Erdos506.V1.ElevenFiveHarmonicFiveCap
import Erdos506.V1.ElevenFive

/-!
# Actual four-star anchors in the residual `C = 40` rows

The two `L = 14` C40 rows with seven or eight five-blocks start their
geometric K3 analysis at a point incident with four five-blocks.  This file
makes that entrance wholly internal to the already proved incidence rows:
it is a consequence of the five-incidence identity and the local cap
`d₅ ≤ 4`.  In particular it does not introduce a collision certificate.

The later external-trace argument must still refine such an anchor to its
full `(d₃,d₄,d₅)` profile and compare the external five-blocks with the
canonical inverted four-star.
-/

namespace Erdos506.V1

open Erdos506.Block
open Erdos506.Block.BlockSystem
open scoped BigOperators

universe u v

/-- The actual pivots at which exactly four selected five-blocks meet. -/
noncomputable def elevenFiveDegreeFourPivots
    {Point : Type u} {Block : Type v} [Fintype Point] [Fintype Block]
    [DecidableEq Point] (S : BlockSystem Point Block) : Finset Point :=
  Finset.univ.filter fun p => S.blockDegree 5 p = 4

@[simp] theorem mem_elevenFiveDegreeFourPivots
    {Point : Type u} {Block : Type v} [Fintype Point] [Fintype Block]
    [DecidableEq Point] (S : BlockSystem Point Block) (p : Point) :
    p ∈ elevenFiveDegreeFourPivots S ↔ S.blockDegree 5 p = 4 := by
  classical
  simp [elevenFiveDegreeFourPivots]

/-- Under the local four-pencil cap, the global five-incidence row bounds
the number of missing degree-four pivots.  This is the numerical entrance
used by both residual `L = 14` C40 geometric rows. -/
theorem five_mul_blockCount_le_thirty_three_add_degreeFourPivots
    {Point : Type u} {Block : Type v} [Fintype Point] [Fintype Block]
    [DecidableEq Point] (S : BlockSystem Point Block)
    (hcard : Fintype.card Point = 11)
    (hglobal : ElevenFiveGlobalRows S)
    (hcap : ∀ p : Point, S.blockDegree 5 p ≤ 4) :
    5 * S.blockCount 5 ≤ 33 + (elevenFiveDegreeFourPivots S).card := by
  classical
  have hpoint (p : Point) :
      S.blockDegree 5 p ≤
        3 + (if p ∈ elevenFiveDegreeFourPivots S then 1 else 0) := by
    by_cases hp : p ∈ elevenFiveDegreeFourPivots S
    · simp [hp]
      exact hcap p
    · simp only [hp, if_false]
      have hne : S.blockDegree 5 p ≠ 4 := by
        simpa only [mem_elevenFiveDegreeFourPivots] using hp
      have hle := hcap p
      omega
  have hsum :
      (∑ p : Point, S.blockDegree 5 p) ≤
        ∑ p : Point,
          (3 + (if p ∈ elevenFiveDegreeFourPivots S then 1 else 0)) :=
    Finset.sum_le_sum fun p _hp => hpoint p
  have hindicator :
      (∑ p : Point,
        (if p ∈ elevenFiveDegreeFourPivots S then 1 else 0)) =
          (elevenFiveDegreeFourPivots S).card := by
    simpa using
      (Finset.card_eq_sum_ite
        (s := elevenFiveDegreeFourPivots S)
        (t := (Finset.univ : Finset Point))
        (Finset.subset_univ _)).symm
  rw [hglobal.fiveIncidence, Finset.sum_add_distrib, hindicator] at hsum
  simp [hcard] at hsum
  exact hsum

/-- The `B₅ = 7` residual row has at least two actual four-star anchors.
This isolates the first nontrivial input to the external-trace obstruction. -/
theorem c40FourteenSeven_two_degreeFourPivots
    {Point : Type u} {Block : Type v} [Fintype Point] [Fintype Block]
    [DecidableEq Point] (S : BlockSystem Point Block)
    (hcard : Fintype.card Point = 11)
    (hglobal : ElevenFiveGlobalRows S)
    (hcap : ∀ p : Point, S.blockDegree 5 p ≤ 4)
    (hfive : S.blockCount 5 = 7) :
    2 ≤ (elevenFiveDegreeFourPivots S).card := by
  have hbound := five_mul_blockCount_le_thirty_three_add_degreeFourPivots
    S hcard hglobal hcap
  omega

/-- The `B₅ = 8` residual row has at least seven actual four-star anchors.
The later K3 four-base argument may choose any one of them. -/
theorem c40FourteenEight_seven_degreeFourPivots
    {Point : Type u} {Block : Type v} [Fintype Point] [Fintype Block]
    [DecidableEq Point] (S : BlockSystem Point Block)
    (hcard : Fintype.card Point = 11)
    (hglobal : ElevenFiveGlobalRows S)
    (hcap : ∀ p : Point, S.blockDegree 5 p ≤ 4)
    (hfive : S.blockCount 5 = 8) :
    7 ≤ (elevenFiveDegreeFourPivots S).card := by
  have hbound := five_mul_blockCount_le_thirty_three_add_degreeFourPivots
    S hcard hglobal hcap
  omega

/-- In particular, the seven-five row supplies a concrete degree-four
anchor.  This is the exact point at which the subsequent proof must derive
the stronger `(9,4,4)` or `(12,_,4)` K3 profile from the C40 local census. -/
theorem c40FourteenSeven_exists_degreeFourPivot
    {Point : Type u} {Block : Type v} [Fintype Point] [Fintype Block]
    [DecidableEq Point] (S : BlockSystem Point Block)
    (hcard : Fintype.card Point = 11)
    (hglobal : ElevenFiveGlobalRows S)
    (hcap : ∀ p : Point, S.blockDegree 5 p ≤ 4)
    (hfive : S.blockCount 5 = 7) :
    ∃ p : Point, S.blockDegree 5 p = 4 := by
  have hmany := c40FourteenSeven_two_degreeFourPivots
    S hcard hglobal hcap hfive
  have hnonempty : (elevenFiveDegreeFourPivots S).Nonempty := by
    apply Finset.card_pos.mp
    omega
  obtain ⟨p, hp⟩ := hnonempty
  exact ⟨p, (mem_elevenFiveDegreeFourPivots S p).mp hp⟩

/-- The seven-five row in fact supplies two different anchors.  This is the
form needed when the external-trace proof separates a base pivot from a
second degree-four point. -/
theorem c40FourteenSeven_exists_two_degreeFourPivots
    {Point : Type u} {Block : Type v} [Fintype Point] [Fintype Block]
    [DecidableEq Point] (S : BlockSystem Point Block)
    (hcard : Fintype.card Point = 11)
    (hglobal : ElevenFiveGlobalRows S)
    (hcap : ∀ p : Point, S.blockDegree 5 p ≤ 4)
    (hfive : S.blockCount 5 = 7) :
    ∃ p q : Point, p ≠ q ∧
      S.blockDegree 5 p = 4 ∧ S.blockDegree 5 q = 4 := by
  let P := elevenFiveDegreeFourPivots S
  have hmany : 2 ≤ P.card := by
    simpa [P] using c40FourteenSeven_two_degreeFourPivots
      S hcard hglobal hcap hfive
  have htwo : 1 < P.card := by omega
  let hexistsPair := Finset.one_lt_card_iff.mp htwo
  let p := Classical.choose hexistsPair
  let hexistsSecond := Classical.choose_spec hexistsPair
  let q := Classical.choose hexistsSecond
  have hpq := Classical.choose_spec hexistsSecond
  refine ⟨p, q, hpq.2.2, ?_, ?_⟩
  · exact (mem_elevenFiveDegreeFourPivots S p).mp hpq.1
  · exact (mem_elevenFiveDegreeFourPivots S q).mp hpq.2.1

end Erdos506.V1
