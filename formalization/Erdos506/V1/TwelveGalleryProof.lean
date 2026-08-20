import Erdos506.V1.TwelveSixRows

/-!
# A lossless Type-B gallery collision

The Type-B field of `RealPlaneTwelveGalleryPrinciple` is needed only in the
part of the selected-six branch where six-point *lines* can still occur.
This file discharges the complementary `lineCount 6 = 0` case directly from
the already materialized pivot row and the existing direction principle.

It deliberately does not claim the full Type-B gallery exclusion: a Type-B
pivot has no six-line through that pivot, but this alone does not rule out a
six-line elsewhere in the arrangement.  The missing global six-line case is
exactly the remaining boundary of `typeBForbidden`.
-/

namespace Erdos506.V1

open Erdos506.Block
open Erdos506.Block.BlockSystem
open Erdos506.Incidence
open Erdos506.V4

universe u

/-- In the selected-six-circle branch, a Type-B pivot is incompatible with
the direction inequality as soon as there are no six-point lines anywhere.

This is a direct collision: the Type-B pivot row gives `pivotSigma = 1`,
whereas the direction row for `(d5,d6) = (0,2)` requires `12 <= 9`.
No gallery exclusion is an input to this theorem. -/
theorem twelveGallery_typeBForbidden_of_noSixLines
    {alpha : Type u} [Fintype alpha] [DecidableEq alpha]
    (Mel : RealPlaneMelchiorPrinciple.{u})
    (EvenArr : RealPlaneEvenArrangementPrinciple.{u})
    (Kelly : RealPlaneKellyMoserPrinciple.{u})
    (Gram : RealPlaneTwelveGramPrinciple.{u})
    (Direction : RealPlaneTwelveDirectionPrinciple.{u})
    (cfg : Configuration alpha) (hadm : Admissible cfg)
    (hcard : Fintype.card alpha = 12)
    (hcap : BlockSizeCap (blockSystem cfg) 6)
    (gamma : DeterminedCircle cfg)
    (hgamma : (circleTrace cfg gamma.1).card = 6)
    (hL6 : (blockSystem cfg).lineCount 6 = 0) :
    Not (exists p : alpha,
      (blockSystem cfg).blockDegree 3 p = 8 /\
      (blockSystem cfg).blockDegree 4 p = 9 /\
      (blockSystem cfg).blockDegree 5 p = 0 /\
      (blockSystem cfg).blockDegree 6 p = 2 /\
      (blockSystem cfg).lineDegree 3 p = 4 /\
      (blockSystem cfg).lineDegree 4 p = 0 /\
      (blockSystem cfg).lineDegree 5 p = 0 /\
      (blockSystem cfg).lineDegree 6 p = 0) := by
  rintro ⟨p, hd3, hd4, hd5, hd6, hl3, hl4, hl5, hl6⟩
  have hrows : TwelveFiveLocalRows (blockSystem cfg) p :=
    twelveFiveLocalRows_of_configuration
      Mel EvenArr Kelly Gram cfg hadm hcard hcap p
  have hsigma : (blockSystem cfg).pivotSigma p = 1 := by
    have hrow := hrows.sigmaRow
    rw [hd3, hd5, hd6] at hrow
    omega
  have hdir :
      2 * ((blockSystem cfg).blockDegree 5 p : Int) +
          6 * ((blockSystem cfg).blockDegree 6 p : Int) <=
        (blockSystem cfg).pivotSigma p + 8 := by
    exact Direction.directionBound cfg hadm hcard hcap
      (Sum.inr gamma) rfl (by
        simpa [geometricBlockSupport] using hgamma)
      hL6 p (by omega)
  rw [hd5, hd6, hsigma] at hdir
  norm_num at hdir

end Erdos506.V1
