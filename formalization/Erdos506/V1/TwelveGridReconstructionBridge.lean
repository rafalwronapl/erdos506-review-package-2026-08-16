import Erdos506.V1.TwelveGridIncidenceExtractionMoments
import Erdos506.Finite.SixFourGridReconstruction

/-!
# Actual reconstruction bridge for the inverted twelve-grid census

The preceding census enumerates the *actual* determined lines after pivot
inversion.  This file only transports that enumeration through the saturated
six-four reconstruction.  In particular, the `Fin 3 x Fin 3` labels below
are labels of actual `AwayFrom p` points and their incidences with actual
members of `H.fourLine`; no projective chart or normalization is chosen.
-/

namespace Erdos506.V1

open Erdos506.Block
open Erdos506.Block.BlockSystem
open Erdos506.Finite
open Erdos506.Incidence
open Erdos506.V3
open Erdos506.V4

universe u

/-- The six actual four-line supports selected by the inverted census. -/
noncomputable def twelveGridActualFourSupport
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (H : TwelveGridInvertedLineCensus cfg p) : Fin 6 -> Finset (AwayFrom p) :=
  fun i => lineSupport (pivotInversion cfg p) (H.fourLine i).1

/-- The actual six supports satisfy the saturated six-four hypotheses. -/
theorem twelveGridActualFourSupport_isSaturatedSixFour
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (hcard : Fintype.card Point = 12)
    (H : TwelveGridInvertedLineCensus cfg p) :
    IsSaturatedSixFour (twelveGridActualFourSupport H) :=
  H.isSaturatedSixFour hcard

/-- The two actual degree-three labels in the selected four-line family. -/
noncomputable def twelveGridActualExternalPoint
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (hcard : Fintype.card Point = 12)
    (H : TwelveGridInvertedLineCensus cfg p) : Fin 2 -> AwayFrom p :=
  sixFourExternalPoint (twelveGridActualFourSupport_isSaturatedSixFour hcard H)

/-- The three actual four-line indices through one of the two external
labels.  The `Fin 2` coordinate selects one pencil. -/
noncomputable def twelveGridActualPencilIndex
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (hcard : Fintype.card Point = 12)
    (H : TwelveGridInvertedLineCensus cfg p)
    (a : Fin 2) : Fin 3 -> Fin 6 :=
  sixFourExternalBase (twelveGridActualFourSupport_isSaturatedSixFour hcard H) a

/-- The actual inverted four-line in a numbered pencil. -/
noncomputable def twelveGridActualPencilLine
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (hcard : Fintype.card Point = 12)
    (H : TwelveGridInvertedLineCensus cfg p)
    (a : Fin 2) (r : Fin 3) : DeterminedLineOfSize (pivotInversion cfg p) 4 :=
  H.fourLine (twelveGridActualPencilIndex hcard H a r)

/-- The nine actual inverted labels, indexed by the two reconstructed
pencils. -/
noncomputable def twelveGridActualGridPoint
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (hcard : Fintype.card Point = 12)
    (H : TwelveGridInvertedLineCensus cfg p)
    (r s : Fin 3) : AwayFrom p :=
  sixFourGridPoint (twelveGridActualFourSupport_isSaturatedSixFour hcard H) r s

/-- The two reconstructed external labels are different actual inverted
points. -/
theorem twelveGridActualExternalPoint_injective
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (hcard : Fintype.card Point = 12)
    (H : TwelveGridInvertedLineCensus cfg p) :
    Function.Injective (twelveGridActualExternalPoint hcard H) :=
  sixFourExternalPoint_injective
    (twelveGridActualFourSupport_isSaturatedSixFour hcard H)

/-- Each external label has four-line degree three. -/
theorem twelveGridActualExternalPoint_degree_eq_three
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (hcard : Fintype.card Point = 12)
    (H : TwelveGridInvertedLineCensus cfg p) (a : Fin 2) :
    sixFourDegree (twelveGridActualFourSupport H)
      (twelveGridActualExternalPoint hcard H a) = 3 :=
  sixFourExternalPoint_degree_eq_three
    (twelveGridActualFourSupport_isSaturatedSixFour hcard H) a

/-- Each reconstructed pencil is an injectively numbered triple of actual
four-lines. -/
theorem twelveGridActualPencilIndex_injective
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (hcard : Fintype.card Point = 12)
    (H : TwelveGridInvertedLineCensus cfg p) (a : Fin 2) :
    Function.Injective (twelveGridActualPencilIndex hcard H a) :=
  sixFourExternalBase_injective
    (twelveGridActualFourSupport_isSaturatedSixFour hcard H) a

/-- The two numbered triples of four-line indices are disjoint. -/
theorem twelveGridActualPencilIndex_zero_ne_one
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (hcard : Fintype.card Point = 12)
    (H : TwelveGridInvertedLineCensus cfg p) (r s : Fin 3) :
    twelveGridActualPencilIndex hcard H 0 r ≠
      twelveGridActualPencilIndex hcard H 1 s :=
  sixFourExternalBase_zero_ne_one
    (twelveGridActualFourSupport_isSaturatedSixFour hcard H) r s

/-- The external label of a pencil is incident with every actual line in
that pencil. -/
theorem twelveGridActualExternalPoint_mem_pencilLine
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (hcard : Fintype.card Point = 12)
    (H : TwelveGridInvertedLineCensus cfg p)
    (a : Fin 2) (r : Fin 3) :
    twelveGridActualExternalPoint hcard H a ∈
      lineSupport (pivotInversion cfg p)
        (twelveGridActualPencilLine hcard H a r).1 :=
  sixFourExternalPoint_mem_externalBase
    (twelveGridActualFourSupport_isSaturatedSixFour hcard H) a r

/-- Incidence of the actual `(r,s)` label with the actual `r`-th line of
the first pencil. -/
theorem twelveGridActualGridPoint_mem_row
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (hcard : Fintype.card Point = 12)
    (H : TwelveGridInvertedLineCensus cfg p) (r s : Fin 3) :
    twelveGridActualGridPoint hcard H r s ∈
      lineSupport (pivotInversion cfg p)
        (twelveGridActualPencilLine hcard H 0 r).1 :=
  sixFourGridPoint_mem_row
    (twelveGridActualFourSupport_isSaturatedSixFour hcard H) r s

/-- Incidence of the actual `(r,s)` label with the actual `s`-th line of
the second pencil. -/
theorem twelveGridActualGridPoint_mem_column
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (hcard : Fintype.card Point = 12)
    (H : TwelveGridInvertedLineCensus cfg p) (r s : Fin 3) :
    twelveGridActualGridPoint hcard H r s ∈
      lineSupport (pivotInversion cfg p)
        (twelveGridActualPencilLine hcard H 1 s).1 :=
  sixFourGridPoint_mem_column
    (twelveGridActualFourSupport_isSaturatedSixFour hcard H) r s

/-- The `Fin 3 x Fin 3` coordinates are lossless: different coordinate
pairs denote different actual inverted labels. -/
theorem twelveGridActualGridPoint_injective
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (hcard : Fintype.card Point = 12)
    (H : TwelveGridInvertedLineCensus cfg p) :
    Function.Injective (fun rs : Fin 3 × Fin 3 =>
      twelveGridActualGridPoint hcard H rs.1 rs.2) :=
  sixFourGridPoint_injective
    (twelveGridActualFourSupport_isSaturatedSixFour hcard H)

/-- Every labelled crossing has four-line degree two. -/
theorem twelveGridActualGridPoint_degree_eq_two
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (hcard : Fintype.card Point = 12)
    (H : TwelveGridInvertedLineCensus cfg p) (r s : Fin 3) :
    sixFourDegree (twelveGridActualFourSupport H)
      (twelveGridActualGridPoint hcard H r s) = 2 :=
  sixFourGridPoint_degree_eq_two
    (twelveGridActualFourSupport_isSaturatedSixFour hcard H) r s

/-- The nine labelled actual points are exactly all degree-two labels of the
six actual inverted four-line supports. -/
theorem twelveGridActualGridImage_eq_degreeTwo
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (hcard : Fintype.card Point = 12)
    (H : TwelveGridInvertedLineCensus cfg p) :
    (Finset.univ : Finset (Fin 3 × Fin 3)).image
        (fun rs => twelveGridActualGridPoint hcard H rs.1 rs.2) =
      sixFourDegreeTwo (twelveGridActualFourSupport H) :=
  sixFourGridImage_eq_degreeTwo
    (twelveGridActualFourSupport_isSaturatedSixFour hcard H)

/-- A single lossless package for the actual reconstruction.  It retains the
full census, so the thirteen ordinary and two three-lines are not discarded. -/
structure TwelveGridActualReconstruction
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (hcard : Fintype.card Point = 12)
    (H : TwelveGridInvertedLineCensus cfg p) : Type u where
  census : TwelveGridInvertedLineCensus cfg p
  census_eq : census = H
  saturated : IsSaturatedSixFour (twelveGridActualFourSupport H)
  external : Fin 2 -> AwayFrom p
  external_eq : external = twelveGridActualExternalPoint hcard H
  external_injective : Function.Injective external
  external_degree : ∀ a, sixFourDegree (twelveGridActualFourSupport H) (external a) = 3
  pencilIndex : Fin 2 -> Fin 3 -> Fin 6
  pencilIndex_eq : pencilIndex = twelveGridActualPencilIndex hcard H
  pencilIndex_injective : ∀ a, Function.Injective (pencilIndex a)
  external_incidence : ∀ a r, external a ∈ lineSupport (pivotInversion cfg p)
    (H.fourLine (pencilIndex a r)).1
  gridPoint : Fin 3 -> Fin 3 -> AwayFrom p
  gridPoint_eq : gridPoint = twelveGridActualGridPoint hcard H
  gridPoint_injective : Function.Injective (fun rs : Fin 3 × Fin 3 => gridPoint rs.1 rs.2)
  row_incidence : ∀ r s, gridPoint r s ∈ lineSupport (pivotInversion cfg p)
    (twelveGridActualPencilLine hcard H 0 r).1
  column_incidence : ∀ r s, gridPoint r s ∈ lineSupport (pivotInversion cfg p)
    (twelveGridActualPencilLine hcard H 1 s).1

/-- Construct the reconstruction directly from an arbitrary actual census. -/
noncomputable def twelveGridActualReconstruction_of_census
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (hcard : Fintype.card Point = 12)
    (H : TwelveGridInvertedLineCensus cfg p) :
    TwelveGridActualReconstruction hcard H where
  census := H
  census_eq := rfl
  saturated := twelveGridActualFourSupport_isSaturatedSixFour hcard H
  external := twelveGridActualExternalPoint hcard H
  external_eq := rfl
  external_injective := twelveGridActualExternalPoint_injective hcard H
  external_degree := twelveGridActualExternalPoint_degree_eq_three hcard H
  pencilIndex := twelveGridActualPencilIndex hcard H
  pencilIndex_eq := rfl
  pencilIndex_injective := twelveGridActualPencilIndex_injective hcard H
  external_incidence := twelveGridActualExternalPoint_mem_pencilLine hcard H
  gridPoint := twelveGridActualGridPoint hcard H
  gridPoint_eq := rfl
  gridPoint_injective := twelveGridActualGridPoint_injective hcard H
  row_incidence := twelveGridActualGridPoint_mem_row hcard H
  column_incidence := twelveGridActualGridPoint_mem_column hcard H

/-- Type-zero rows reach the actual reconstruction without any additional
normalization hypothesis. -/
noncomputable def twelveGridActualReconstruction_of_typeZero_row
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    (cfg : Configuration Point) (p : Point)
    (hcard : Fintype.card Point = 12)
    (hcap : Erdos506.V1.BlockSizeCap (blockSystem cfg) 5)
    (hthree : (blockSystem cfg).blockDegree 3 p = 13)
    (hfive : (blockSystem cfg).blockDegree 5 p = 6)
    (hlineThree : (blockSystem cfg).lineDegree 3 p = 5)
    (hlineFour : (blockSystem cfg).lineDegree 4 p = 0) :
    TwelveGridActualReconstruction hcard
      (twelveGridInvertedLineCensus_of_typeZero_row cfg p hcard hcap hthree hfive
        hlineThree hlineFour) :=
  twelveGridActualReconstruction_of_census hcard
    (twelveGridInvertedLineCensus_of_typeZero_row cfg p hcard hcap hthree hfive
      hlineThree hlineFour)

/-- Type-one rows reach the same actual reconstruction, again with no
projective normalization assumption. -/
noncomputable def twelveGridActualReconstruction_of_typeOne_row
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    (cfg : Configuration Point) (p : Point)
    (hcard : Fintype.card Point = 12)
    (hcap : Erdos506.V1.BlockSizeCap (blockSystem cfg) 5)
    (hthree : (blockSystem cfg).blockDegree 3 p = 13)
    (hfive : (blockSystem cfg).blockDegree 5 p = 6)
    (hlineThree : (blockSystem cfg).lineDegree 3 p = 4)
    (hlineFour : (blockSystem cfg).lineDegree 4 p = 0) :
    TwelveGridActualReconstruction hcard
      (twelveGridInvertedLineCensus_of_typeOne_row cfg p hcard hcap hthree hfive
        hlineThree hlineFour) :=
  twelveGridActualReconstruction_of_census hcard
    (twelveGridInvertedLineCensus_of_typeOne_row cfg p hcard hcap hthree hfive
      hlineThree hlineFour)

/-- The type-zero row supplies the saturated actual six-four family without
an extra arrangement or normalization hypothesis. -/
theorem twelveGridActualFourSupport_isSaturatedSixFour_of_typeZero_row
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    (cfg : Configuration Point) (p : Point)
    (hcard : Fintype.card Point = 12)
    (hcap : Erdos506.V1.BlockSizeCap (blockSystem cfg) 5)
    (hthree : (blockSystem cfg).blockDegree 3 p = 13)
    (hfive : (blockSystem cfg).blockDegree 5 p = 6)
    (hlineThree : (blockSystem cfg).lineDegree 3 p = 5)
    (hlineFour : (blockSystem cfg).lineDegree 4 p = 0) :
    IsSaturatedSixFour (twelveGridActualFourSupport
      (twelveGridInvertedLineCensus_of_typeZero_row cfg p hcard hcap hthree hfive
        hlineThree hlineFour)) :=
  twelveGridActualFourSupport_isSaturatedSixFour hcard
    (twelveGridInvertedLineCensus_of_typeZero_row cfg p hcard hcap hthree hfive
      hlineThree hlineFour)

/-- The type-one row supplies the same saturated actual six-four family. -/
theorem twelveGridActualFourSupport_isSaturatedSixFour_of_typeOne_row
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    (cfg : Configuration Point) (p : Point)
    (hcard : Fintype.card Point = 12)
    (hcap : Erdos506.V1.BlockSizeCap (blockSystem cfg) 5)
    (hthree : (blockSystem cfg).blockDegree 3 p = 13)
    (hfive : (blockSystem cfg).blockDegree 5 p = 6)
    (hlineThree : (blockSystem cfg).lineDegree 3 p = 4)
    (hlineFour : (blockSystem cfg).lineDegree 4 p = 0) :
    IsSaturatedSixFour (twelveGridActualFourSupport
      (twelveGridInvertedLineCensus_of_typeOne_row cfg p hcard hcap hthree hfive
        hlineThree hlineFour)) :=
  twelveGridActualFourSupport_isSaturatedSixFour hcard
    (twelveGridInvertedLineCensus_of_typeOne_row cfg p hcard hcap hthree hfive
      hlineThree hlineFour)

/-- The type-zero row has nine pairwise differently labelled actual inverted
points, indexed by `Fin 3 x Fin 3`. -/
theorem twelveGridActualGridPoint_injective_of_typeZero_row
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    (cfg : Configuration Point) (p : Point)
    (hcard : Fintype.card Point = 12)
    (hcap : Erdos506.V1.BlockSizeCap (blockSystem cfg) 5)
    (hthree : (blockSystem cfg).blockDegree 3 p = 13)
    (hfive : (blockSystem cfg).blockDegree 5 p = 6)
    (hlineThree : (blockSystem cfg).lineDegree 3 p = 5)
    (hlineFour : (blockSystem cfg).lineDegree 4 p = 0) :
    Function.Injective (fun rs : Fin 3 × Fin 3 =>
      twelveGridActualGridPoint hcard
        (twelveGridInvertedLineCensus_of_typeZero_row cfg p hcard hcap hthree hfive
          hlineThree hlineFour) rs.1 rs.2) :=
  twelveGridActualGridPoint_injective hcard
    (twelveGridInvertedLineCensus_of_typeZero_row cfg p hcard hcap hthree hfive
      hlineThree hlineFour)

/-- The type-one row has the same lossless `Fin 3 x Fin 3` indexing of
actual inverted points. -/
theorem twelveGridActualGridPoint_injective_of_typeOne_row
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    (cfg : Configuration Point) (p : Point)
    (hcard : Fintype.card Point = 12)
    (hcap : Erdos506.V1.BlockSizeCap (blockSystem cfg) 5)
    (hthree : (blockSystem cfg).blockDegree 3 p = 13)
    (hfive : (blockSystem cfg).blockDegree 5 p = 6)
    (hlineThree : (blockSystem cfg).lineDegree 3 p = 4)
    (hlineFour : (blockSystem cfg).lineDegree 4 p = 0) :
    Function.Injective (fun rs : Fin 3 × Fin 3 =>
      twelveGridActualGridPoint hcard
        (twelveGridInvertedLineCensus_of_typeOne_row cfg p hcard hcap hthree hfive
          hlineThree hlineFour) rs.1 rs.2) :=
  twelveGridActualGridPoint_injective hcard
    (twelveGridInvertedLineCensus_of_typeOne_row cfg p hcard hcap hthree hfive
      hlineThree hlineFour)

end Erdos506.V1
