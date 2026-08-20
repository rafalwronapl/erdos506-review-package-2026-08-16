import Erdos506.V1.InversionAugmentation
import Erdos506.V1.TwelveGridNormalTransfer

/-!
# The finite entrance to the twelve-point grid branch

The two forbidden grid rows have a marked pivot with six five-blocks and
thirteen three-blocks.  The pivot-inversion dictionary turns these numbers
into, respectively, six four-lines and thirteen ordinary lines.  This file
records that extraction without silently choosing a projective chart or a
`3 x 3` incidence pattern.

The missing step from this finite entrance to `TwelveGridNormalTransfer` is
genuinely geometric: one has to prove that the six extracted four-lines
carry a nine-point grid and identify three of the remaining ordinary lines
as concurrent external secants.  Neither the degree rows nor the abstract
tagged block system retain those incidences.
-/

namespace Erdos506.V1

open Erdos506.Block
open Erdos506.Block.BlockSystem
open Erdos506.Incidence
open Erdos506.V3
open Erdos506.V4

universe u

/-- The six four-point lines of the inverted configuration forced by the
`d₅(p)=6` component of either exceptional grid row. -/
noncomputable def twelveGridPivotFourLineEquiv
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    (cfg : Configuration Point) (p : Point)
    (hfive : (blockSystem cfg).blockDegree 5 p = 6) :
    Fin 6 ≃ DeterminedLineOfSize (pivotInversion cfg p) 4 := by
  apply (Fintype.equivFinOfCardEq ?_).symm
  rw [← lineCount_eq_card_determinedLineOfSize,
    ← blockDegree_eq_lineCount_pivotInversion cfg p 5 (by omega)]
  exact hfive

/-- The selected inverted four-line at one of the six forced indices. -/
noncomputable def twelveGridPivotFourLine
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    (cfg : Configuration Point) (p : Point)
    (hfive : (blockSystem cfg).blockDegree 5 p = 6)
    (i : Fin 6) : DeterminedLine (pivotInversion cfg p) :=
  (twelveGridPivotFourLineEquiv cfg p hfive i).1

/-- Every extracted line has precisely four inverted labels. -/
theorem twelveGridPivotFourLine_support_card
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    (cfg : Configuration Point) (p : Point)
    (hfive : (blockSystem cfg).blockDegree 5 p = 6)
    (i : Fin 6) :
    (lineSupport (pivotInversion cfg p)
      (twelveGridPivotFourLine cfg p hfive i)).card = 4 :=
  (twelveGridPivotFourLineEquiv cfg p hfive i).2

/-- The thirteen ordinary inverted secants forced by `d₃(p)=13`.  This is
the full finite ordinary-line census available before a grid arrangement is
identified. -/
noncomputable def twelveGridPivotOrdinaryLineEquiv
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    (cfg : Configuration Point) (p : Point)
    (hthree : (blockSystem cfg).blockDegree 3 p = 13) :
    Fin 13 ≃ DeterminedLineOfSize (pivotInversion cfg p) 2 := by
  apply (Fintype.equivFinOfCardEq ?_).symm
  rw [← lineCount_eq_card_determinedLineOfSize,
    ← blockDegree_three_eq_lineCount_two_pivotInversion]
  exact hthree

/-- The concrete lossless finite entrance shared by both exceptional rows.
It contains exactly what their degree data determines after inversion, but
does not claim the additional projective grid normalization. -/
structure TwelveGridFiniteEntrance
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    (cfg : Configuration Point) (p : Point) : Type u where
  fourLine : Fin 6 → DeterminedLineOfSize (pivotInversion cfg p) 4
  fourLine_injective : Function.Injective fourLine
  ordinaryLine : Fin 13 → DeterminedLineOfSize (pivotInversion cfg p) 2
  ordinaryLine_injective : Function.Injective ordinaryLine

/-- Both local grid degree types supply the same finite inversion entrance.
The line-degree distinction `5` versus `4` is not used here; it belongs to
the missing incidence arrangement which should produce the grid itself. -/
noncomputable def twelveGridFiniteEntrance_of_degree_rows
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    (cfg : Configuration Point) (p : Point)
    (hthree : (blockSystem cfg).blockDegree 3 p = 13)
    (hfive : (blockSystem cfg).blockDegree 5 p = 6) :
    TwelveGridFiniteEntrance cfg p where
  fourLine := twelveGridPivotFourLineEquiv cfg p hfive
  fourLine_injective := (twelveGridPivotFourLineEquiv cfg p hfive).injective
  ordinaryLine := twelveGridPivotOrdinaryLineEquiv cfg p hthree
  ordinaryLine_injective :=
    (twelveGridPivotOrdinaryLineEquiv cfg p hthree).injective

/-- The finite extraction at the type-zero grid row.  The additional
`lineDegree` equalities are retained in the assumptions to make this an
exact entrance for the first forbidden-grid predicate; the pivot dictionary
uses its two block-degree components. -/
noncomputable def twelveGridFiniteEntrance_of_forbiddenGridTypeZero_row
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    (cfg : Configuration Point) (p : Point)
    (hthree : (blockSystem cfg).blockDegree 3 p = 13)
    (hfive : (blockSystem cfg).blockDegree 5 p = 6)
    (_hlineThree : (blockSystem cfg).lineDegree 3 p = 5)
    (_hlineFour : (blockSystem cfg).lineDegree 4 p = 0) :
    TwelveGridFiniteEntrance cfg p :=
  twelveGridFiniteEntrance_of_degree_rows cfg p hthree hfive

/-- The analogous finite extraction at the type-one grid row. -/
noncomputable def twelveGridFiniteEntrance_of_forbiddenGridTypeOne_row
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    (cfg : Configuration Point) (p : Point)
    (hthree : (blockSystem cfg).blockDegree 3 p = 13)
    (hfive : (blockSystem cfg).blockDegree 5 p = 6)
    (_hlineThree : (blockSystem cfg).lineDegree 3 p = 4)
    (_hlineFour : (blockSystem cfg).lineDegree 4 p = 0) :
    TwelveGridFiniteEntrance cfg p :=
  twelveGridFiniteEntrance_of_degree_rows cfg p hthree hfive

end Erdos506.V1
