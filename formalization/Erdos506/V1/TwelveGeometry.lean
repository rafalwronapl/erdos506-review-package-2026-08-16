import Erdos506.V1.FiniteCaps

/-!
# Explicit geometric interfaces used only at twelve points

The analytic twelve-point proof has three small real-geometric inputs which
are not consequences of the abstract tagged-block calculus currently present
in the formalization:

* the centred-incidence-vector (Gram) bounds for five- and six-blocks;
* the real `3 x 3` grid obstruction arising from six four-lines after a
  pivot inversion;
* the two distinguished-line gallery obstructions and the ordinary-direction
  inequality used in the selected-six-circle branch.

They are recorded here as explicit parameters.  None of the fields contains
the target `51 <= circleCount cfg`, the negation of a complete branch, or a
finite-case endpoint callback.  Each field is the literal local or Gram
statement used in the manuscript.  Future developments can construct these
structures from linear algebra, the grid lemma, the gallery argument, and
Ungar's direction theorem without changing the arithmetic consumers.
-/

namespace Erdos506.V1

open Erdos506.Block
open Erdos506.Block.BlockSystem
open Erdos506.Incidence
open Erdos506.V4
open scoped BigOperators

universe u

/-- The centred-vector consequences for rich blocks on twelve labels.

`fiveBlockCap` is the obtuse-family bound in the eleven-dimensional space
`1^perp`.  `fiveDegreeCap` is its local pair-moment companion.  The final
field contains the two-class Gram bounds used by the selected-six-circle
spine.
-/
structure RealPlaneTwelveGramPrinciple where
  fiveBlockCap :
    forall {alpha : Type u} [Fintype alpha] [DecidableEq alpha]
      (cfg : Configuration alpha),
      Admissible cfg -> Fintype.card alpha = 12 ->
      BlockSizeCap (blockSystem cfg) 6 ->
        (blockSystem cfg).blockCount 5 <= 12
  fiveDegreeCap :
    forall {alpha : Type u} [Fintype alpha] [DecidableEq alpha]
      (cfg : Configuration alpha),
      Admissible cfg -> Fintype.card alpha = 12 ->
      BlockSizeCap (blockSystem cfg) 6 -> forall p : alpha,
        (blockSystem cfg).blockDegree 5 p <= 6
  fiveDegreeCapOnSixBlock :
    forall {alpha : Type u} [Fintype alpha] [DecidableEq alpha]
      (cfg : Configuration alpha),
      Admissible cfg -> Fintype.card alpha = 12 ->
      BlockSizeCap (blockSystem cfg) 6 -> forall p : alpha,
        0 < (blockSystem cfg).blockDegree 6 p ->
          (blockSystem cfg).blockDegree 5 p <= 5
  richBlockCap :
    forall {alpha : Type u} [Fintype alpha] [DecidableEq alpha]
      (cfg : Configuration alpha),
      Admissible cfg -> Fintype.card alpha = 12 ->
      BlockSizeCap (blockSystem cfg) 6 ->
        (blockSystem cfg).blockCount 6 +
          (blockSystem cfg).blockCount 5 <= 12
  sixBlockCaps :
    forall {alpha : Type u} [Fintype alpha] [DecidableEq alpha]
      (cfg : Configuration alpha),
      Admissible cfg -> Fintype.card alpha = 12 ->
      BlockSizeCap (blockSystem cfg) 6 ->
      let S := blockSystem cfg
      S.blockCount 6 <= 4 /\
        (S.blockCount 6 = 4 -> S.blockCount 5 = 0) /\
        (S.blockCount 6 = 3 -> S.blockCount 5 <= 3) /\
        (S.blockCount 6 = 2 -> S.blockCount 5 <= 8) /\
        (S.blockCount 6 = 1 -> S.blockCount 5 <= 11)
/-- The exact local consequences of the real `3 x 3` grid lemma.

The first field is the middle local cap `j = 1 -> d5 <= 5`.  The other two
fields exclude precisely the manuscript's local types
`(j,u,epsilon,q,d5) = (2,0,0,0,6)` and `(2,1,0,1,6)`; after expanding the
definitions these are the displayed degree statements below.
-/
structure RealPlaneTwelveGridPrinciple where
  jOneFiveDegreeCap :
    forall {alpha : Type u} [Fintype alpha] [DecidableEq alpha]
      (cfg : Configuration alpha),
      Admissible cfg -> Fintype.card alpha = 12 ->
      BlockSizeCap (blockSystem cfg) 5 -> forall p : alpha,
        (blockSystem cfg).blockDegree 3 p = 10 ->
          (blockSystem cfg).blockDegree 5 p <= 5
  forbiddenGridTypeZero :
    forall {alpha : Type u} [Fintype alpha] [DecidableEq alpha]
      (cfg : Configuration alpha),
      Admissible cfg -> Fintype.card alpha = 12 ->
      BlockSizeCap (blockSystem cfg) 5 ->
      (blockSystem cfg).lineCount 5 = 0 ->
      Not (exists p : alpha,
        (blockSystem cfg).blockDegree 3 p = 13 /\
        (blockSystem cfg).blockDegree 5 p = 6 /\
        (blockSystem cfg).lineDegree 3 p = 5 /\
        (blockSystem cfg).lineDegree 4 p = 0)
  forbiddenGridTypeOne :
    forall {alpha : Type u} [Fintype alpha] [DecidableEq alpha]
      (cfg : Configuration alpha),
      Admissible cfg -> Fintype.card alpha = 12 ->
      BlockSizeCap (blockSystem cfg) 5 ->
      (blockSystem cfg).lineCount 5 = 0 ->
      Not (exists p : alpha,
        (blockSystem cfg).blockDegree 3 p = 13 /\
        (blockSystem cfg).blockDegree 5 p = 6 /\
        (blockSystem cfg).lineDegree 3 p = 4 /\
        (blockSystem cfg).lineDegree 4 p = 0)

/-- The two local distinguished-line gallery exclusions.

The fields are the exact inversion dictionaries for the arrangements
`(t2,t3,t4) = (6,14,3)` and `(t2,t3,t5) = (7,13,2)`, both with
distinguished word `3D+4T`.  They do not mention a circle-count bound.
-/
structure RealPlaneTwelveGalleryPrinciple where
  typeAForbidden :
    forall {alpha : Type u} [Fintype alpha] [DecidableEq alpha]
      (cfg : Configuration alpha),
      Admissible cfg -> Fintype.card alpha = 12 ->
      BlockSizeCap (blockSystem cfg) 6 ->
      Not (exists p : alpha,
        (blockSystem cfg).blockDegree 3 p = 7 /\
        (blockSystem cfg).blockDegree 4 p = 10 /\
        (blockSystem cfg).blockDegree 5 p = 3 /\
        (blockSystem cfg).blockDegree 6 p = 0 /\
        (blockSystem cfg).lineDegree 3 p = 4 /\
        (blockSystem cfg).lineDegree 4 p = 0 /\
        (blockSystem cfg).lineDegree 5 p = 0 /\
        (blockSystem cfg).lineDegree 6 p = 0)
  typeBForbidden :
    forall {alpha : Type u} [Fintype alpha] [DecidableEq alpha]
      (cfg : Configuration alpha),
      Admissible cfg -> Fintype.card alpha = 12 ->
      BlockSizeCap (blockSystem cfg) 6 ->
      Not (exists p : alpha,
        (blockSystem cfg).blockDegree 3 p = 8 /\
        (blockSystem cfg).blockDegree 4 p = 9 /\
        (blockSystem cfg).blockDegree 5 p = 0 /\
        (blockSystem cfg).blockDegree 6 p = 2 /\
        (blockSystem cfg).lineDegree 3 p = 4 /\
        (blockSystem cfg).lineDegree 4 p = 0 /\
        (blockSystem cfg).lineDegree 5 p = 0 /\
        (blockSystem cfg).lineDegree 6 p = 0)

/-- The ordinary-direction consequence used in the six-circle branch.

The selected six-circle is passed explicitly to certify that the branch
really contains such a proper circle.  The conclusion is local and does not
mention a circle-count endpoint.
-/
structure RealPlaneTwelveDirectionPrinciple where
  directionBound :
    forall {alpha : Type u} [Fintype alpha] [DecidableEq alpha]
      (cfg : Configuration alpha),
      Admissible cfg -> Fintype.card alpha = 12 ->
      BlockSizeCap (blockSystem cfg) 6 ->
      (gamma : GeometricBlock cfg) ->
      geometricBlockKind gamma = .circle ->
      (geometricBlockSupport cfg gamma).card = 6 ->
      (blockSystem cfg).lineCount 6 = 0 -> forall p : alpha,
      0 < (blockSystem cfg).blockDegree 6 p ->
        2 * ((blockSystem cfg).blockDegree 5 p : Int) +
            6 * ((blockSystem cfg).blockDegree 6 p : Int) <=
          (blockSystem cfg).pivotSigma p + 8

/-- The strict direction-defect form of the selected-six input.

After inversion at `p`, the geometric proof identifies the displayed
quantity divided by three with the excess of the off-star defect over its
elementary lower bound.  Ungar's six-direction contradiction makes that
excess positive.  Recording the integral numerator avoids a division and is
therefore the direct target for a future projective/affine formalization.

This is deliberately equivalent to `RealPlaneTwelveDirectionPrinciple`: it
does not add a geometric assumption to the public twelve-point theorem. -/
structure RealPlaneTwelveDirectionDefectPrinciple where
  strictDirectionDefect :
    forall {alpha : Type u} [Fintype alpha] [DecidableEq alpha]
      (cfg : Configuration alpha),
      Admissible cfg -> Fintype.card alpha = 12 ->
      BlockSizeCap (blockSystem cfg) 6 ->
      (gamma : GeometricBlock cfg) ->
      geometricBlockKind gamma = .circle ->
      (geometricBlockSupport cfg gamma).card = 6 ->
      (blockSystem cfg).lineCount 6 = 0 -> forall p : alpha,
      0 < (blockSystem cfg).blockDegree 6 p ->
        3 <= 11 + (blockSystem cfg).pivotSigma p -
          2 * ((blockSystem cfg).blockDegree 5 p : Int) -
          6 * ((blockSystem cfg).blockDegree 6 p : Int)

/-- Convert the integral strict-defect certificate supplied by the Ungar
argument into the local direction inequality consumed by the six-circle
arithmetic. -/
noncomputable def RealPlaneTwelveDirectionDefectPrinciple.toDirectionPrinciple
    (Defect : RealPlaneTwelveDirectionDefectPrinciple.{u}) :
    RealPlaneTwelveDirectionPrinciple.{u} where
  directionBound := by
    intro alpha _ _ cfg hadm hcard hcap gamma hkind hgamma hL6 p hp
    have hdefect := Defect.strictDirectionDefect cfg hadm hcard hcap
      gamma hkind hgamma hL6 p hp
    omega

/-- Conversely, the public direction inequality entails the strict integral
defect form.  Thus the adapter above is lossless. -/
noncomputable def RealPlaneTwelveDirectionPrinciple.toDefectPrinciple
    (Direction : RealPlaneTwelveDirectionPrinciple.{u}) :
    RealPlaneTwelveDirectionDefectPrinciple.{u} where
  strictDirectionDefect := by
    intro alpha _ _ cfg hadm hcard hcap gamma hkind hgamma hL6 p hp
    have hdirection := Direction.directionBound cfg hadm hcard hcap
      gamma hkind hgamma hL6 p hp
    omega

end Erdos506.V1
