import Erdos506.V1.ElevenFive

/-!
# Raw geometric witnesses for the C40 collision boundary

The remaining C40 fields of `RealPlaneElevenFiveGeometry` conclude an
`ElevenFiveTripleCollision` in the abstract block system.  The geometric
arguments expected to discharge them instead produce a five-circle and a
distinct geometric block containing three common selected labels.  This file
is the lossless adapter from that concrete witness to the block-system
conclusion.  It introduces no C40 case assumption or replacement certificate.
-/

namespace Erdos506.V1

open Erdos506.Block
open Erdos506.Incidence
open Erdos506.V3
open Erdos506.V4

universe u

/-- A concrete geometric witness of a forbidden triple overlap.  Its blocks
are actual determined affine lines or proper circles, rather than opaque
members of the canonical block system. -/
structure ElevenFiveGeometricTripleOverlapWitness
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    (cfg : Configuration Point) where
  first : GeometricBlock cfg
  second : GeometricBlock cfg
  distinct : first ≠ second
  overlap : 3 <=
    (geometricBlockSupport cfg first ∩ geometricBlockSupport cfg second).card

/-- Any concrete geometric triple-overlap witness is a triple collision in
the canonical block system. -/
theorem ElevenFiveGeometricTripleOverlapWitness.toTripleCollision
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point}
    (W : ElevenFiveGeometricTripleOverlapWitness cfg) :
    ElevenFiveTripleCollision (blockSystem cfg) := by
  refine ⟨W.first, W.second, W.distinct, ?_⟩
  simpa [blockSystem, geometricBlockSystem, geometricBlockSupport] using W.overlap

/-- A concrete circle--circle witness of a forbidden triple overlap. -/
structure ElevenFiveCircleTripleOverlapWitness
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    (cfg : Configuration Point) where
  first : DeterminedCircle cfg
  second : DeterminedCircle cfg
  distinct : first ≠ second
  overlap : 3 <= (circleTrace cfg first.1 ∩ circleTrace cfg second.1).card

/-- A circle--circle witness is a special case of the geometric witness. -/
def ElevenFiveCircleTripleOverlapWitness.toGeometricWitness
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point}
    (W : ElevenFiveCircleTripleOverlapWitness cfg) :
    ElevenFiveGeometricTripleOverlapWitness cfg where
  first := Sum.inr W.first
  second := Sum.inr W.second
  distinct := by
    intro h
    apply W.distinct
    exact Sum.inr.inj h
  overlap := by
    simpa [geometricBlockSupport] using W.overlap

/-- Any circle--circle triple-overlap witness is a forbidden collision of two
concrete circle blocks. -/
theorem ElevenFiveCircleTripleOverlapWitness.toTripleCollision
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point}
    (W : ElevenFiveCircleTripleOverlapWitness cfg) :
    ElevenFiveTripleCollision (blockSystem cfg) :=
  W.toGeometricWitness.toTripleCollision

/-- A direct form of the circle adapter. -/
theorem elevenFiveTripleCollision_of_circleTrace_overlap
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point}
    (c d : DeterminedCircle cfg) (hcd : c ≠ d)
    (hover : 3 <= (circleTrace cfg c.1 ∩ circleTrace cfg d.1).card) :
    ElevenFiveTripleCollision (blockSystem cfg) :=
  (ElevenFiveCircleTripleOverlapWitness.mk c d hcd hover).toTripleCollision

/-- In particular, two distinct determined circles cannot share three selected
labels in the canonical geometric block system. -/
theorem elevenFive_no_circleTrace_triple_overlap
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    (cfg : Configuration Point) (c d : DeterminedCircle cfg) (hcd : c ≠ d)
    (hover : 3 <= (circleTrace cfg c.1 ∩ circleTrace cfg d.1).card) : False :=
  elevenFive_no_tripleCollision (blockSystem cfg)
    (elevenFiveTripleCollision_of_circleTrace_overlap c d hcd hover)

end Erdos506.V1
