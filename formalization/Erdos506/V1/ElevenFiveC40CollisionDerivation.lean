import Erdos506.V1.ElevenFiveCollisionWitness

/-!
# C40 collision fields as concrete geometric witnesses

The four C40 fields in `RealPlaneElevenFiveGeometry` already return a
collision in `blockSystem cfg`.  For this particular block system the block
type is definitionally `GeometricBlock cfg`, so such a collision contains the
two concrete affine-line/circle blocks required by
`ElevenFiveGeometricTripleOverlapWitness`.  This module makes that lossless
unpacking explicit.  In particular, it adds no C40 certificate and no new
geometric hypothesis.
-/

namespace Erdos506.V1

open Erdos506.Block
open Erdos506.Incidence
open Erdos506.V4

universe u

/-- A collision in the canonical geometric block system already names two
actual geometric blocks. -/
def ElevenFiveTripleCollision.toGeometricWitness
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point}
    (h : ElevenFiveTripleCollision (blockSystem cfg)) :
    ElevenFiveGeometricTripleOverlapWitness cfg := by
  rcases h with ⟨first, second, hne, hover⟩
  refine ⟨first, second, hne, ?_⟩
  simpa [blockSystem, geometricBlockSystem, geometricBlockSupport] using hover

/-- The `C=40,L=11,B5∈{5,6}` C40 field, exposed as its actual pair of
geometric blocks. -/
theorem c40ElevenSmallFace_geometricTripleOverlapWitness
    (Geometry : RealPlaneElevenFiveGeometry.{u})
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    (cfg : Configuration Point) (hadm : Admissible cfg)
    (hcard : Fintype.card Point = 11)
    (hcap : BlockSizeCap (blockSystem cfg) 5)
    (hC : circleCount cfg = 40)
    (hL : elevenFiveLineTotal (blockSystem cfg) = 11)
    (hfive : (blockSystem cfg).blockCount 5 = 5 ∨
      (blockSystem cfg).blockCount 5 = 6) :
    ElevenFiveGeometricTripleOverlapWitness cfg :=
  (Geometry.c40ElevenSmallFaceCollision cfg hadm hcard hcap hC hL hfive).toGeometricWitness

/-- The `C=40,L=11,B5=7` C40 field, exposed as its actual pair of geometric
blocks. -/
theorem c40ElevenSevenDefect_geometricTripleOverlapWitness
    (Geometry : RealPlaneElevenFiveGeometry.{u})
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    (cfg : Configuration Point) (hadm : Admissible cfg)
    (hcard : Fintype.card Point = 11)
    (hcap : BlockSizeCap (blockSystem cfg) 5)
    (hC : circleCount cfg = 40)
    (hL : elevenFiveLineTotal (blockSystem cfg) = 11)
    (hfive : (blockSystem cfg).blockCount 5 = 7) :
    ElevenFiveGeometricTripleOverlapWitness cfg :=
  (Geometry.c40ElevenSevenDefectCollision cfg hadm hcard hcap hC hL hfive).toGeometricWitness

/-- The `C=40,L=14,B5=7` C40 field, exposed as its actual pair of geometric
blocks. -/
theorem c40FourteenSevenExternalTrace_geometricTripleOverlapWitness
    (Geometry : RealPlaneElevenFiveGeometry.{u})
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    (cfg : Configuration Point) (hadm : Admissible cfg)
    (hcard : Fintype.card Point = 11)
    (hcap : BlockSizeCap (blockSystem cfg) 5)
    (hC : circleCount cfg = 40)
    (hL : elevenFiveLineTotal (blockSystem cfg) = 14)
    (hfive : (blockSystem cfg).blockCount 5 = 7) :
    ElevenFiveGeometricTripleOverlapWitness cfg :=
  (Geometry.c40FourteenSevenExternalTraceCollision
    cfg hadm hcard hcap hC hL hfive).toGeometricWitness

/-- The `C=40,L=14,B5=8` C40 field, exposed as its actual pair of geometric
blocks. -/
theorem c40FourteenEightDefect_geometricTripleOverlapWitness
    (Geometry : RealPlaneElevenFiveGeometry.{u})
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    (cfg : Configuration Point) (hadm : Admissible cfg)
    (hcard : Fintype.card Point = 11)
    (hcap : BlockSizeCap (blockSystem cfg) 5)
    (hC : circleCount cfg = 40)
    (hL : elevenFiveLineTotal (blockSystem cfg) = 14)
    (hfive : (blockSystem cfg).blockCount 5 = 8) :
    ElevenFiveGeometricTripleOverlapWitness cfg :=
  (Geometry.c40FourteenEightDefectCollision
    cfg hadm hcard hcap hC hL hfive).toGeometricWitness

/-- The exact small-face C40 hypotheses are contradictory once the C40
field is unpacked and sent through the existing collision adapter. -/
theorem c40ElevenSmallFace_impossible
    (Geometry : RealPlaneElevenFiveGeometry.{u})
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    (cfg : Configuration Point) (hadm : Admissible cfg)
    (hcard : Fintype.card Point = 11)
    (hcap : BlockSizeCap (blockSystem cfg) 5)
    (hC : circleCount cfg = 40)
    (hL : elevenFiveLineTotal (blockSystem cfg) = 11)
    (hfive : (blockSystem cfg).blockCount 5 = 5 ∨
      (blockSystem cfg).blockCount 5 = 6) : False :=
  elevenFive_no_tripleCollision (blockSystem cfg)
    (c40ElevenSmallFace_geometricTripleOverlapWitness
      Geometry cfg hadm hcard hcap hC hL hfive).toTripleCollision

/-- The exact `L=11,B5=7` C40 hypotheses are contradictory. -/
theorem c40ElevenSevenDefect_impossible
    (Geometry : RealPlaneElevenFiveGeometry.{u})
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    (cfg : Configuration Point) (hadm : Admissible cfg)
    (hcard : Fintype.card Point = 11)
    (hcap : BlockSizeCap (blockSystem cfg) 5)
    (hC : circleCount cfg = 40)
    (hL : elevenFiveLineTotal (blockSystem cfg) = 11)
    (hfive : (blockSystem cfg).blockCount 5 = 7) : False :=
  elevenFive_no_tripleCollision (blockSystem cfg)
    (c40ElevenSevenDefect_geometricTripleOverlapWitness
      Geometry cfg hadm hcard hcap hC hL hfive).toTripleCollision

/-- The exact `L=14,B5=7` C40 hypotheses are contradictory. -/
theorem c40FourteenSevenExternalTrace_impossible
    (Geometry : RealPlaneElevenFiveGeometry.{u})
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    (cfg : Configuration Point) (hadm : Admissible cfg)
    (hcard : Fintype.card Point = 11)
    (hcap : BlockSizeCap (blockSystem cfg) 5)
    (hC : circleCount cfg = 40)
    (hL : elevenFiveLineTotal (blockSystem cfg) = 14)
    (hfive : (blockSystem cfg).blockCount 5 = 7) : False :=
  elevenFive_no_tripleCollision (blockSystem cfg)
    (c40FourteenSevenExternalTrace_geometricTripleOverlapWitness
      Geometry cfg hadm hcard hcap hC hL hfive).toTripleCollision

/-- The exact `L=14,B5=8` C40 hypotheses are contradictory. -/
theorem c40FourteenEightDefect_impossible
    (Geometry : RealPlaneElevenFiveGeometry.{u})
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    (cfg : Configuration Point) (hadm : Admissible cfg)
    (hcard : Fintype.card Point = 11)
    (hcap : BlockSizeCap (blockSystem cfg) 5)
    (hC : circleCount cfg = 40)
    (hL : elevenFiveLineTotal (blockSystem cfg) = 14)
    (hfive : (blockSystem cfg).blockCount 5 = 8) : False :=
  elevenFive_no_tripleCollision (blockSystem cfg)
    (c40FourteenEightDefect_geometricTripleOverlapWitness
      Geometry cfg hadm hcard hcap hC hL hfive).toTripleCollision

end Erdos506.V1
