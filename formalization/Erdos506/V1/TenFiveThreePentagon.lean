import Erdos506.Incidence.NineLinkPrinciple
import Erdos506.V1.TenFiveGeometry

/-!
# The positive boundary of the three-pentagon endpoint

The manuscript's three-pentagon argument has two logically separate parts.
The finite loss table selects one exceptional pivot with local row
`(d3,d4,d5,l3) = (6,10,0,4)`.  The real nine-point link lemma then turns the
four three-lines through that pivot into four disjoint edges inside two
triangles.

The existing `RealPlaneNineLinkPrinciple.twoTriangleLinks` is deliberately a
global ten-point statement: it requires the `6/10/0` block-degree row at
every pivot.  It therefore cannot be applied to the single exceptional pivot
selected in the three-pentagon branch.  This file records the two minimal
positive interfaces at that gap and their lossless adapter to
`LocalNineLinkMatchingData`.  It assumes neither a terminal contradiction nor
the circle-count endpoint.
-/

namespace Erdos506.V1

open Erdos506.Block
open Erdos506.Block.BlockSystem
open Erdos506.Finite
open Erdos506.Incidence
open Erdos506.V4

universe u

/-- The finite output of the three-pentagon loss classification, before any
real nine-point link theorem is used. -/
structure ThreePentagonExceptionalPivotData
    {Point Block : Type*} [Fintype Point] [Fintype Block]
    [DecidableEq Point] (S : BlockSystem Point Block) where
  pivot : Point
  three_degree : S.blockDegree 3 pivot = 6
  four_degree : S.blockDegree 4 pivot = 10
  five_degree : S.blockDegree 5 pivot = 0
  three_line_degree : S.lineDegree 3 pivot = 4

/-- Exact finite statement still missing from the current block API.

Its hypotheses are only those used by the loss table.  In particular the
ambient equality `totalCircleCount = 32` and all real-plane assumptions have
already done their routing work before this finite statement is invoked. -/
structure ThreePentagonFinitePivotPrinciple where
  exceptionalPivot :
    ∀ {Point Block : Type u} [Fintype Point] [Fintype Block]
      [DecidableEq Point]
      (S : BlockSystem Point Block),
      Fintype.card Point = 10 →
      S.blockCount 5 = 3 →
      (tenHighPoints S).card = 2 →
      S.lineCount 5 = 0 →
      1 ≤ S.lineCount 4 →
      S.lineCount 4 ≤ 3 →
      S.lineCount 3 + S.lineCount 4 = 10 →
      (∀ p : Point, TenFiveLocalProfile S p) →
      ThreePentagonExceptionalPivotData S

/-- Local real-nine-link bridge missing from the current global
`RealPlaneNineLinkPrinciple` API.

The four scalar fields in `pivotData` are precisely what the manuscript uses:
the first three give the nine-point line profile after inversion, and the
last supplies the four original three-lines which become the forbidden
matching edges.  The conclusion is positive incidence data rather than an
endpoint or a proposition asserting impossibility. -/
structure RealPlaneLocalNineLinkPrinciple where
  fourMatchingAtExceptionalPivot :
    ∀ {α : Type u} [Fintype α] [DecidableEq α]
      (cfg : Configuration α),
      Admissible cfg →
      Fintype.card α = 10 →
      ThreePentagonExceptionalPivotData (blockSystem cfg) →
      FourMatchingInTwoTriangles α

/-- Attach the local real-nine-link matching to the finite exceptional-pivot
certificate. -/
noncomputable def ThreePentagonExceptionalPivotData.toLocalNineLinkMatchingData
    {α : Type u} [Fintype α] [DecidableEq α]
    (NineLink : RealPlaneLocalNineLinkPrinciple.{u})
    (cfg : Configuration α) (hadm : Admissible cfg)
    (hcard : Fintype.card α = 10)
    (d : ThreePentagonExceptionalPivotData (blockSystem cfg)) :
    LocalNineLinkMatchingData (blockSystem cfg) where
  pivot := d.pivot
  three_degree := d.three_degree
  four_degree := d.four_degree
  five_degree := d.five_degree
  three_line_degree := d.three_line_degree
  matching := NineLink.fourMatchingAtExceptionalPivot cfg hadm hcard d

end Erdos506.V1
