import Erdos506.Finite.FourStarCompleteQuadrangle
import Erdos506.V1.ElevenFiveC40SingletonExclusion

/-!
# The degree-four four-star bridge for the C40 residual rows

The complete-quadrangle part of K3.2 does not need the special local row
`(d₃,d₄,d₅) = (9,4,4)`.  At any eleven-point pivot with `d₅ = 4`, inversion
produces exactly four four-point lines on ten labels; the finite four-star
count already forces every pair of them to meet.  Transporting this fact
back says that any two of the four five-blocks through the pivot meet in
exactly two selected points.

This is the common singleton-exclusion bridge used by both `L = 11` and
`L = 14` C40 dispatches.  It contains no projective or harmonic input.
-/

namespace Erdos506.V1

open Erdos506.Block
open Erdos506.Block.BlockSystem
open Erdos506.Incidence
open Erdos506.V3
open Erdos506.V4

universe u

/-- At an eleven-point pivot incident with exactly four size-five blocks,
any two distinct incident size-five blocks meet in exactly two points.

After deleting the pivot their inverted traces are two of exactly four
four-point lines on ten labels.  The finite four-star saturation theorem
gives one remaining common label, and reinserting the pivot gives two. -/
theorem elevenFive_degreeFourPivot_fiveBlock_inter_card_two
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    (cfg : Configuration Point) (hcard : Fintype.card Point = 11)
    (p : Point) (hfive : (blockSystem cfg).blockDegree 5 p = 4)
    {b c : GeometricBlock cfg}
    (hb : b ∈ (blockSystem cfg).blocksOfSize 5)
    (hc : c ∈ (blockSystem cfg).blocksOfSize 5)
    (hbp : p ∈ geometricBlockSupport cfg b)
    (hcp : p ∈ geometricBlockSupport cfg c) (hne : b ≠ c) :
    (geometricBlockSupport cfg b ∩ geometricBlockSupport cfg c).card = 2 := by
  let Q := pivotInversion cfg p
  let B := elevenFiveFivePivotBlock cfg p b hb hbp
  let C := elevenFiveFivePivotBlock cfg p c hc hcp
  let A := elevenFiveFivePivotLineOfSize cfg p b hb hbp
  let D := elevenFiveFivePivotLineOfSize cfg p c hc hcp
  let a : (blockSystem Q).LineBlock := ⟨.inl A.1, rfl⟩
  let d : (blockSystem Q).LineBlock := ⟨.inl D.1, rfl⟩
  have ha : a.1 ∈ (blockSystem Q).lineBlocksOfSize 4 := by
    change Sum.inl A.1 ∈ (blockSystem Q).lineBlocksOfSize 4
    exact (blockSystem Q).mem_blocksOfKindSize.mpr ⟨rfl, A.2⟩
  have hd : d.1 ∈ (blockSystem Q).lineBlocksOfSize 4 := by
    change Sum.inl D.1 ∈ (blockSystem Q).lineBlocksOfSize 4
    exact (blockSystem Q).mem_blocksOfKindSize.mpr ⟨rfl, D.2⟩
  have had : a.1 ≠ d.1 := by
    intro heq
    apply hne
    have hline : blockToPivotLine cfg p B = blockToPivotLine cfg p C := by
      simpa [a, d, A, D, B, C] using heq
    have hblock := blockToPivotLine_injective cfg p hline
    exact congrArg Subtype.val hblock
  have hinvcard : Fintype.card (AwayFrom p) = 10 := by
    rw [card_awayFrom, hcard]
  have hfour : (blockSystem Q).lineCount 4 = 4 := by
    change (blockSystem (pivotInversion cfg p)).lineCount 4 = 4
    rw [← blockDegree_eq_lineCount_pivotInversion cfg p 5 (by omega)]
    exact hfive
  have hfinite := Erdos506.Finite.line_four_inter_card_one_of_card_ten_count_four
    (blockSystem Q) hinvcard hfour ha hd had
  have hA : lineSupport Q A.1 = awaySupport p (geometricBlockSupport cfg b) := by
    change lineSupport (pivotInversion cfg p) (blockToPivotLine cfg p B) = _
    exact lineSupport_blockToPivotLine cfg p B
  have hD : lineSupport Q D.1 = awaySupport p (geometricBlockSupport cfg c) := by
    change lineSupport (pivotInversion cfg p) (blockToPivotLine cfg p C) = _
    exact lineSupport_blockToPivotLine cfg p C
  have haway :
      (awaySupport p (geometricBlockSupport cfg b) ∩
        awaySupport p (geometricBlockSupport cfg c)).card = 1 := by
    change (lineSupport Q A.1 ∩ lineSupport Q D.1).card = 1 at hfinite
    rw [hA, hD] at hfinite
    exact hfinite
  have hpinter : p ∈ geometricBlockSupport cfg b ∩ geometricBlockSupport cfg c :=
    Finset.mem_inter.mpr ⟨hbp, hcp⟩
  rw [awaySupport_inter, card_awaySupport p _ hpinter] at haway
  omega

/-- The degree-four-pivot bridge in the singleton-exclusion form used by
the C40 routers. -/
theorem elevenFive_degreeFourPivot_fiveBlock_inter_card_ne_one
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    (cfg : Configuration Point) (hcard : Fintype.card Point = 11)
    (p : Point) (hfive : (blockSystem cfg).blockDegree 5 p = 4)
    {b c : GeometricBlock cfg}
    (hb : b ∈ (blockSystem cfg).blocksOfSize 5)
    (hc : c ∈ (blockSystem cfg).blocksOfSize 5)
    (hbp : p ∈ geometricBlockSupport cfg b)
    (hcp : p ∈ geometricBlockSupport cfg c) (hne : b ≠ c) :
    (geometricBlockSupport cfg b ∩ geometricBlockSupport cfg c).card ≠ 1 := by
  rw [elevenFive_degreeFourPivot_fiveBlock_inter_card_two
    cfg hcard p hfive hb hc hbp hcp hne]
  omega

end Erdos506.V1
