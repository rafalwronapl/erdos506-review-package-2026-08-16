import Erdos506.V1.TwelveGridEntrance
import Erdos506.V1.LargeMaster

/-!
# Incidence census at the twelve-point grid entrance

The exceptional twelve-point rows determine more than the raw `6` and `13`
counts recorded in `TwelveGridEntrance`.  A five-block cap becomes a
four-point cap after pivot inversion.  Pair ownership on the eleven inverted
labels then forces exactly two three-point lines in addition to the thirteen
ordinary and six four-point lines.

This is deliberately an incidence census, rather than a claimed grid.  Pair
ownership says that two different extracted lines share at most one selected
label, but it does not say which of the fifteen pairs of four-lines meet.
The latter incidence graph is the remaining geometric input needed to split
the six lines into two three-line classes and obtain a `3 x 3` grid.
-/

namespace Erdos506.V1

open Erdos506.Block
open Erdos506.Block.BlockSystem
open Erdos506.Incidence
open Erdos506.V3
open Erdos506.V4

universe u

/-- A five-block cap before inversion gives a four-label cap on every
determined line after inversion about the chosen pivot. -/
theorem twelveGridPivotInversion_lineSupport_card_le_four
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    (cfg : Configuration Point) (p : Point)
    (hcap : Erdos506.V1.BlockSizeCap (blockSystem cfg) 5)
    (L : DeterminedLine (pivotInversion cfg p)) :
    (lineSupport (pivotInversion cfg p) L).card <= 4 := by
  obtain ⟨b, rfl⟩ := blockToPivotLine_surjective cfg p L
  have hbcap : (geometricBlockSupport cfg b.1).card <= 5 :=
    hcap b.1 b.2.2
  rw [card_lineSupport_blockToPivotLine]
  omega

/-- Under the preceding inverted line cap, no inverted line has size above
four.  This is the line-level form needed by the pair partition. -/
theorem twelveGridPivotInversion_lineCount_eq_zero_of_gt_four
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    (cfg : Configuration Point) (p : Point)
    (hcap : Erdos506.V1.BlockSizeCap (blockSystem cfg) 5)
    (s : Nat) (hs : 4 < s) :
    (blockSystem (pivotInversion cfg p)).lineCount s = 0 := by
  classical
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro b hb
  have hspec := (blockSystem (pivotInversion cfg p)).mem_blocksOfKindSize.mp hb
  cases b with
  | inl L =>
      have hupper := twelveGridPivotInversion_lineSupport_card_le_four
        cfg p hcap L
      have hsize := hspec.2
      change (lineSupport (pivotInversion cfg p) L).card = s at hsize
      omega
  | inr c => cases hspec.1

/-- The pair partition fills the remaining six pairs by exactly two
three-point inverted lines. -/
theorem twelveGridPivotInversion_lineCount_three
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    (cfg : Configuration Point) (p : Point)
    (hcard : Fintype.card Point = 12)
    (hcap : Erdos506.V1.BlockSizeCap (blockSystem cfg) 5)
    (hthree : (blockSystem cfg).blockDegree 3 p = 13)
    (hfive : (blockSystem cfg).blockDegree 5 p = 6) :
    (blockSystem (pivotInversion cfg p)).lineCount 3 = 2 := by
  classical
  have htwo : (blockSystem (pivotInversion cfg p)).lineCount 2 = 13 := by
    rw [← blockDegree_three_eq_lineCount_two_pivotInversion]
    exact hthree
  have hfour : (blockSystem (pivotInversion cfg p)).lineCount 4 = 6 := by
    rw [← blockDegree_eq_lineCount_pivotInversion cfg p 5 (by omega)]
    exact hfive
  have hl5 := twelveGridPivotInversion_lineCount_eq_zero_of_gt_four
    cfg p hcap 5 (by omega)
  have hl6 := twelveGridPivotInversion_lineCount_eq_zero_of_gt_four
    cfg p hcap 6 (by omega)
  have hl7 := twelveGridPivotInversion_lineCount_eq_zero_of_gt_four
    cfg p hcap 7 (by omega)
  have hl8 := twelveGridPivotInversion_lineCount_eq_zero_of_gt_four
    cfg p hcap 8 (by omega)
  have hl9 := twelveGridPivotInversion_lineCount_eq_zero_of_gt_four
    cfg p hcap 9 (by omega)
  have hl10 := twelveGridPivotInversion_lineCount_eq_zero_of_gt_four
    cfg p hcap 10 (by omega)
  have hl11 := twelveGridPivotInversion_lineCount_eq_zero_of_gt_four
    cfg p hcap 11 (by omega)
  have hcardAway : Fintype.card (AwayFrom p) = 11 := by
    rw [Erdos506.V3.card_awayFrom, hcard]
  have hpairs := (blockSystem (pivotInversion cfg p)).line_pair_partition_by_size
  rw [hcardAway] at hpairs
  norm_num [Finset.sum_range_succ, Nat.choose,
    htwo, hfour, hl5, hl6, hl7, hl8, hl9, hl10, hl11] at hpairs
  omega

/-- The size-two, size-three and size-four lines account for exactly fifty-six
point-line incidences on the eleven inverted labels. -/
theorem twelveGridPivotInversion_small_lineDegree_sum_eq_fifty_six
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    (cfg : Configuration Point) (p : Point)
    (hcard : Fintype.card Point = 12)
    (hcap : Erdos506.V1.BlockSizeCap (blockSystem cfg) 5)
    (hthree : (blockSystem cfg).blockDegree 3 p = 13)
    (hfive : (blockSystem cfg).blockDegree 5 p = 6) :
    (∑ q : AwayFrom p,
      ((blockSystem (pivotInversion cfg p)).lineDegree 2 q +
        (blockSystem (pivotInversion cfg p)).lineDegree 3 q +
        (blockSystem (pivotInversion cfg p)).lineDegree 4 q)) = 56 := by
  let S := blockSystem (pivotInversion cfg p)
  have htwo : S.lineCount 2 = 13 := by
    rw [← blockDegree_three_eq_lineCount_two_pivotInversion]
    exact hthree
  have hthreeCount : S.lineCount 3 = 2 := by
    simpa [S] using
      twelveGridPivotInversion_lineCount_three cfg p hcard hcap hthree hfive
  have hfour : S.lineCount 4 = 6 := by
    rw [← blockDegree_eq_lineCount_pivotInversion cfg p 5 (by omega)]
    exact hfive
  have htwoInc := S.line_incidence 2
  have hthreeInc := S.line_incidence 3
  have hfourInc := S.line_incidence 4
  change (∑ q : AwayFrom p,
    (S.lineDegree 2 q + S.lineDegree 3 q + S.lineDegree 4 q)) = 56
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
    htwoInc, hthreeInc, hfourInc, htwo, hthreeCount, hfour]

/-- The two forced inverted three-lines, obtained from the exact pair
census rather than postulated as part of a grid. -/
noncomputable def twelveGridPivotThreeLineEquiv
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    (cfg : Configuration Point) (p : Point)
    (hcard : Fintype.card Point = 12)
    (hcap : Erdos506.V1.BlockSizeCap (blockSystem cfg) 5)
    (hthree : (blockSystem cfg).blockDegree 3 p = 13)
    (hfive : (blockSystem cfg).blockDegree 5 p = 6) :
    Fin 2 ≃ DeterminedLineOfSize (pivotInversion cfg p) 3 := by
  apply (Fintype.equivFinOfCardEq ?_).symm
  rw [← lineCount_eq_card_determinedLineOfSize]
  exact twelveGridPivotInversion_lineCount_three cfg p hcard hcap hthree hfive

/-- Lossless full line census supplied by either exceptional local grid row.
All three maps enumerate their respective *entire* size classes. -/
structure TwelveGridInvertedLineCensus
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    (cfg : Configuration Point) (p : Point) : Type u where
  ordinaryLine : Fin 13 ≃ DeterminedLineOfSize (pivotInversion cfg p) 2
  threeLine : Fin 2 ≃ DeterminedLineOfSize (pivotInversion cfg p) 3
  fourLine : Fin 6 ≃ DeterminedLineOfSize (pivotInversion cfg p) 4
  lineSupport_card_le_four : forall L : DeterminedLine (pivotInversion cfg p),
    (lineSupport (pivotInversion cfg p) L).card <= 4

/-- Build the exact inverted line profile from the shared numerical portion
of the two forbidden grid rows. -/
noncomputable def twelveGridInvertedLineCensus_of_degree_rows
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    (cfg : Configuration Point) (p : Point)
    (hcard : Fintype.card Point = 12)
    (hcap : Erdos506.V1.BlockSizeCap (blockSystem cfg) 5)
    (hthree : (blockSystem cfg).blockDegree 3 p = 13)
    (hfive : (blockSystem cfg).blockDegree 5 p = 6) :
    TwelveGridInvertedLineCensus cfg p where
  ordinaryLine := twelveGridPivotOrdinaryLineEquiv cfg p hthree
  threeLine := twelveGridPivotThreeLineEquiv cfg p hcard hcap hthree hfive
  fourLine := twelveGridPivotFourLineEquiv cfg p hfive
  lineSupport_card_le_four :=
    twelveGridPivotInversion_lineSupport_card_le_four cfg p hcap

/-- The type-zero local row has the full inverted `(13,2,6)` line census.
Its line-degree data is retained as an argument because it colors some of
the lines by their pre-inversion provenance, but is not needed for this
uncoloured incidence extraction. -/
noncomputable def twelveGridInvertedLineCensus_of_typeZero_row
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    (cfg : Configuration Point) (p : Point)
    (hcard : Fintype.card Point = 12)
    (hcap : Erdos506.V1.BlockSizeCap (blockSystem cfg) 5)
    (hthree : (blockSystem cfg).blockDegree 3 p = 13)
    (hfive : (blockSystem cfg).blockDegree 5 p = 6)
    (_hlineThree : (blockSystem cfg).lineDegree 3 p = 5)
    (_hlineFour : (blockSystem cfg).lineDegree 4 p = 0) :
    TwelveGridInvertedLineCensus cfg p :=
  twelveGridInvertedLineCensus_of_degree_rows cfg p hcard hcap hthree hfive

/-- The type-one local row has the same uncoloured line census; it differs
only in the number of ordinary inverted lines originating from lines rather
than circles before inversion. -/
noncomputable def twelveGridInvertedLineCensus_of_typeOne_row
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    (cfg : Configuration Point) (p : Point)
    (hcard : Fintype.card Point = 12)
    (hcap : Erdos506.V1.BlockSizeCap (blockSystem cfg) 5)
    (hthree : (blockSystem cfg).blockDegree 3 p = 13)
    (hfive : (blockSystem cfg).blockDegree 5 p = 6)
    (_hlineThree : (blockSystem cfg).lineDegree 3 p = 4)
    (_hlineFour : (blockSystem cfg).lineDegree 4 p = 0) :
    TwelveGridInvertedLineCensus cfg p :=
  twelveGridInvertedLineCensus_of_degree_rows cfg p hcard hcap hthree hfive

/-- The selected four-line supports have the exact prescribed cardinality. -/
theorem TwelveGridInvertedLineCensus.fourLine_support_card
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (H : TwelveGridInvertedLineCensus cfg p) (i : Fin 6) :
    (lineSupport (pivotInversion cfg p) (H.fourLine i).1).card = 4 :=
  (H.fourLine i).2

/-- Actual pair ownership: different selected four-lines cannot share two
inverted labels.  This is the complete incidence restriction obtained from
unique determined-line ownership without selecting a grid arrangement. -/
theorem TwelveGridInvertedLineCensus.fourLine_support_inter_lt_two
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (H : TwelveGridInvertedLineCensus cfg p) {i j : Fin 6} (hij : i ≠ j) :
    (lineSupport (pivotInversion cfg p) (H.fourLine i).1 ∩
      lineSupport (pivotInversion cfg p) (H.fourLine j).1).card < 2 := by
  let Q := pivotInversion cfg p
  let bi : GeometricBlock Q := Sum.inl (H.fourLine i).1
  let bj : GeometricBlock Q := Sum.inl (H.fourLine j).1
  let Li : (blockSystem Q).LineBlock := ⟨bi, rfl⟩
  let Lj : (blockSystem Q).LineBlock := ⟨bj, rfl⟩
  have hLiNe : Li ≠ Lj := by
    intro h
    apply hij
    apply H.fourLine.injective
    apply Subtype.ext
    simpa [Li, Lj, bi, bj] using h
  have hinter := (blockSystem Q).distinct_line_inter_card_lt_two hLiNe
  simpa [Q, Li, Lj, bi, bj, geometricBlockSupport] using hinter

end Erdos506.V1
