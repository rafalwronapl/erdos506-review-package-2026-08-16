import Erdos506.V1.TwelveGridReconstructionBridge
import Erdos506.V1.TwelveGridNormalTransfer
import Erdos506.Incidence.DeterminedLineProjectiveRealization

/-!
# Projective entrance for the reconstructed twelve-grid

This is the geometric, but still lossless, continuation of
`TwelveGridReconstructionBridge`.  The six reconstructed four-lines are
real affine lines of the inverted configuration, so they have canonical
homogeneous covectors.  The nine `Fin 3 x Fin 3` labels are shown to be the
actual projective cross-intersections of the two reconstructed pencils.

What is deliberately *not* asserted here is an affine coordinate map sending
those points to `{-1,0,1}^2`: that requires a separate projective-frame
normalization theorem, together with the identification of the three relevant
ordinary lines required by `TwelveGridNormalTransfer`.
-/

namespace Erdos506.V1

open Erdos506.Block
open Erdos506.Block.BlockSystem
open Erdos506.Finite
open Erdos506.Incidence
open Erdos506.V3
open Erdos506.V4

universe u

/-- The canonical projective point of an actual inverted label. -/
noncomputable def twelveGridActualProjectivePoint
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    (cfg : Configuration Point) (p : Point) (q : AwayFrom p) :
    RealProjectivePoint :=
  affinePointToProjective (pivotInversion cfg p q)

/-- The canonical homogeneous line of one reconstructed pencil member. -/
noncomputable def twelveGridActualProjectivePencilLine
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (hcard : Fintype.card Point = 12)
    (H : TwelveGridInvertedLineCensus cfg p)
    (a : Fin 2) (r : Fin 3) : RealProjectiveLine :=
  determinedProjectiveLine (pivotInversion cfg p)
    (twelveGridActualPencilLine hcard H a r).1

/-- Projective completion remains injective on the actual inverted labels. -/
theorem twelveGridActualProjectivePoint_injective
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    (cfg : Configuration Point) (p : Point) :
    Function.Injective (twelveGridActualProjectivePoint cfg p) := by
  intro q r hqr
  apply (pivotInversion cfg p).injective
  apply affinePointToProjective_injective
  simpa [twelveGridActualProjectivePoint] using hqr

/-- Homogeneous incidence of an actual inverted label is exactly membership
in the corresponding actual four-line support. -/
theorem twelveGridActualProjectivePoint_mem_pencilLine_iff
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (hcard : Fintype.card Point = 12)
    (H : TwelveGridInvertedLineCensus cfg p)
    (a : Fin 2) (r : Fin 3) (q : AwayFrom p) :
    twelveGridActualProjectivePoint cfg p q ∈
      twelveGridActualProjectivePencilLine hcard H a r ↔
    q ∈ lineSupport (pivotInversion cfg p)
      (twelveGridActualPencilLine hcard H a r).1 := by
  rw [mem_lineSupport]
  exact affinePoint_mem_determinedProjectiveLine_iff
    (pivotInversion cfg p) q (twelveGridActualPencilLine hcard H a r).1

/-- Every actual external label is incident with all three homogeneous lines
of its reconstructed pencil. -/
theorem twelveGridActualProjectiveExternal_incident
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (hcard : Fintype.card Point = 12)
    (H : TwelveGridInvertedLineCensus cfg p)
    (a : Fin 2) (r : Fin 3) :
    twelveGridActualProjectivePoint cfg p
      (twelveGridActualExternalPoint hcard H a) ∈
      twelveGridActualProjectivePencilLine hcard H a r :=
  (twelveGridActualProjectivePoint_mem_pencilLine_iff hcard H a r
    (twelveGridActualExternalPoint hcard H a)).2
    (twelveGridActualExternalPoint_mem_pencilLine hcard H a r)

/-- One labelled grid point is incident with its actual row line. -/
theorem twelveGridActualProjectiveGridPoint_incident_row
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (hcard : Fintype.card Point = 12)
    (H : TwelveGridInvertedLineCensus cfg p) (r s : Fin 3) :
    twelveGridActualProjectivePoint cfg p
      (twelveGridActualGridPoint hcard H r s) ∈
      twelveGridActualProjectivePencilLine hcard H 0 r :=
  (twelveGridActualProjectivePoint_mem_pencilLine_iff hcard H 0 r
    (twelveGridActualGridPoint hcard H r s)).2
    (twelveGridActualGridPoint_mem_row hcard H r s)

/-- One labelled grid point is incident with its actual column line. -/
theorem twelveGridActualProjectiveGridPoint_incident_column
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (hcard : Fintype.card Point = 12)
    (H : TwelveGridInvertedLineCensus cfg p) (r s : Fin 3) :
    twelveGridActualProjectivePoint cfg p
      (twelveGridActualGridPoint hcard H r s) ∈
      twelveGridActualProjectivePencilLine hcard H 1 s :=
  (twelveGridActualProjectivePoint_mem_pencilLine_iff hcard H 1 s
    (twelveGridActualGridPoint hcard H r s)).2
    (twelveGridActualGridPoint_mem_column hcard H r s)

/-- A line of the first pencil and a line of the second pencil are distinct
homogeneous projective lines. -/
theorem twelveGridActualProjectivePencilLine_zero_ne_one
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (hcard : Fintype.card Point = 12)
    (H : TwelveGridInvertedLineCensus cfg p) (r s : Fin 3) :
    twelveGridActualProjectivePencilLine hcard H 0 r ≠
      twelveGridActualProjectivePencilLine hcard H 1 s := by
  intro hline
  apply twelveGridActualPencilIndex_zero_ne_one hcard H r s
  apply H.fourLine.injective
  apply Subtype.ext
  apply determinedProjectiveLine_injective (pivotInversion cfg p)
  simpa [twelveGridActualProjectivePencilLine] using hline

/-- The labelled actual grid point is the genuine projective cross-product
intersection of its row and column lines. -/
theorem twelveGridActualProjectiveGridPoint_eq_cross
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (hcard : Fintype.card Point = 12)
    (H : TwelveGridInvertedLineCensus cfg p) (r s : Fin 3) :
    twelveGridActualProjectivePoint cfg p
      (twelveGridActualGridPoint hcard H r s) =
      projectiveLineIntersection
        (twelveGridActualProjectivePencilLine hcard H 0 r)
        (twelveGridActualProjectivePencilLine hcard H 1 s)
        (twelveGridActualProjectivePencilLine_zero_ne_one hcard H r s) := by
  let R := twelveGridActualProjectivePencilLine hcard H 0 r
  let C := twelveGridActualProjectivePencilLine hcard H 1 s
  let x := twelveGridActualProjectivePoint cfg p
    (twelveGridActualGridPoint hcard H r s)
  let hRC : R ≠ C := twelveGridActualProjectivePencilLine_zero_ne_one hcard H r s
  obtain ⟨z, hz, hunique⟩ := existsUnique_projectiveLineIntersection R C hRC
  have hx : x ∈ R ∧ x ∈ C := by
    exact ⟨twelveGridActualProjectiveGridPoint_incident_row hcard H r s,
      twelveGridActualProjectiveGridPoint_incident_column hcard H r s⟩
  have hcross : projectiveLineIntersection R C hRC ∈ R ∧
      projectiveLineIntersection R C hRC ∈ C :=
    ⟨projectiveLineIntersection_mem_left hRC,
      projectiveLineIntersection_mem_right hRC⟩
  exact (hunique x hx).trans (hunique (projectiveLineIntersection R C hRC) hcross).symm

/-- The concrete projective endpoint of the reconstruction.  It contains
only projective points, canonical homogeneous lines, and their verified
incidences; it makes no affine-coordinate assertion. -/
structure TwelveGridProjectiveGridEntrance
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (hcard : Fintype.card Point = 12)
    (H : TwelveGridInvertedLineCensus cfg p) : Type u where
  reconstruction : TwelveGridActualReconstruction hcard H
  point : AwayFrom p -> RealProjectivePoint
  point_eq : point = twelveGridActualProjectivePoint cfg p
  point_injective : Function.Injective point
  pencilLine : Fin 2 -> Fin 3 -> RealProjectiveLine
  pencilLine_eq : pencilLine = twelveGridActualProjectivePencilLine hcard H
  pencilLine_cross_ne : ∀ r s, pencilLine 0 r ≠ pencilLine 1 s
  external_incident : ∀ a r,
    point (reconstruction.external a) ∈ pencilLine a r
  grid_cross : ∀ r s,
    point (reconstruction.gridPoint r s) =
      projectiveLineIntersection (pencilLine 0 r) (pencilLine 1 s)
        (pencilLine_cross_ne r s)

/-- Construct the entire projective entrance directly from the actual census. -/
noncomputable def twelveGridProjectiveGridEntrance_of_census
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (hcard : Fintype.card Point = 12)
    (H : TwelveGridInvertedLineCensus cfg p) :
    TwelveGridProjectiveGridEntrance hcard H where
  reconstruction := twelveGridActualReconstruction_of_census hcard H
  point := twelveGridActualProjectivePoint cfg p
  point_eq := rfl
  point_injective := twelveGridActualProjectivePoint_injective cfg p
  pencilLine := twelveGridActualProjectivePencilLine hcard H
  pencilLine_eq := rfl
  pencilLine_cross_ne := twelveGridActualProjectivePencilLine_zero_ne_one hcard H
  external_incident := twelveGridActualProjectiveExternal_incident hcard H
  grid_cross := twelveGridActualProjectiveGridPoint_eq_cross hcard H

/-- Type-zero rows have the canonical projective entrance without a separate
coordinate-normalization hypothesis. -/
noncomputable def twelveGridProjectiveGridEntrance_of_typeZero_row
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    (cfg : Configuration Point) (p : Point)
    (hcard : Fintype.card Point = 12)
    (hcap : Erdos506.V1.BlockSizeCap (blockSystem cfg) 5)
    (hthree : (blockSystem cfg).blockDegree 3 p = 13)
    (hfive : (blockSystem cfg).blockDegree 5 p = 6)
    (hlineThree : (blockSystem cfg).lineDegree 3 p = 5)
    (hlineFour : (blockSystem cfg).lineDegree 4 p = 0) :
    TwelveGridProjectiveGridEntrance hcard
      (twelveGridInvertedLineCensus_of_typeZero_row cfg p hcard hcap hthree hfive
        hlineThree hlineFour) :=
  twelveGridProjectiveGridEntrance_of_census hcard
    (twelveGridInvertedLineCensus_of_typeZero_row cfg p hcard hcap hthree hfive
      hlineThree hlineFour)

/-- Type-one rows have the same canonical projective entrance. -/
noncomputable def twelveGridProjectiveGridEntrance_of_typeOne_row
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    (cfg : Configuration Point) (p : Point)
    (hcard : Fintype.card Point = 12)
    (hcap : Erdos506.V1.BlockSizeCap (blockSystem cfg) 5)
    (hthree : (blockSystem cfg).blockDegree 3 p = 13)
    (hfive : (blockSystem cfg).blockDegree 5 p = 6)
    (hlineThree : (blockSystem cfg).lineDegree 3 p = 4)
    (hlineFour : (blockSystem cfg).lineDegree 4 p = 0) :
    TwelveGridProjectiveGridEntrance hcard
      (twelveGridInvertedLineCensus_of_typeOne_row cfg p hcard hcap hthree hfive
        hlineThree hlineFour) :=
  twelveGridProjectiveGridEntrance_of_census hcard
    (twelveGridInvertedLineCensus_of_typeOne_row cfg p hcard hcap hthree hfive
      hlineThree hlineFour)

end Erdos506.V1
