import Erdos506.V1.DeletionLineCensus
import Erdos506.V1.TwelveGalleryProof

/-!
# Concrete residual boundary of the twelve-line gallery

`TwelveGalleryProof` already eliminates a Type-B pivot when the original
configuration has no six-point line.  This file records the stronger
configuration-level consequence: any surviving Type-B pivot has an actual
six-point determined line *away from the pivot*.  Thus the unformalized
Type-B gallery field is not a generic line-arrangement assertion any more;
its sole remaining input is the simplicial-gallery contradiction in the
presence of that external six-line.

For Type A the available local rows determine the Melchior defect exactly.
The remaining missing bridge for both types is correspondingly precise:
construct the pivot-inverted dual projective arrangement with its cyclic
successors and triangular-face incidence, then certify the `TTDTDTD`
gallery skeleton and its two finite completions.  The current projective
arrangement modules provide the vertices and incidence census, but not that
successor/face bridge; no replacement principle is introduced here.
-/

namespace Erdos506.V1

open Erdos506.Block
open Erdos506.Block.BlockSystem
open Erdos506.Incidence
open Erdos506.V4

universe u

/-- The Type-A local data have no free Melchior defects: their restored
rows force `pivotSigma = 1` and `restoredKappa = 0`.  This is the exact
arithmetic entrance to the first gallery completion. -/
theorem twelveGallery_typeA_forces_local_defect
    {alpha : Type u} [Fintype alpha] [DecidableEq alpha]
    (Mel : RealPlaneMelchiorPrinciple.{u})
    (EvenArr : RealPlaneEvenArrangementPrinciple.{u})
    (Kelly : RealPlaneKellyMoserPrinciple.{u})
    (Gram : RealPlaneTwelveGramPrinciple.{u})
    (cfg : Configuration alpha) (hadm : Admissible cfg)
    (hcard : Fintype.card alpha = 12)
    (hcap : BlockSizeCap (blockSystem cfg) 6)
    (p : alpha)
    (hd3 : (blockSystem cfg).blockDegree 3 p = 7)
    (hd4 : (blockSystem cfg).blockDegree 4 p = 10)
    (hd5 : (blockSystem cfg).blockDegree 5 p = 3)
    (hd6 : (blockSystem cfg).blockDegree 6 p = 0)
    (hl3 : (blockSystem cfg).lineDegree 3 p = 4)
    (hl4 : (blockSystem cfg).lineDegree 4 p = 0)
    (hl5 : (blockSystem cfg).lineDegree 5 p = 0)
    (hl6 : (blockSystem cfg).lineDegree 6 p = 0) :
    (blockSystem cfg).pivotSigma p = 1 /\
      (blockSystem cfg).restoredKappa p = 0 := by
  have hrows : TwelveFiveLocalRows (blockSystem cfg) p :=
    twelveFiveLocalRows_of_configuration
      Mel EvenArr Kelly Gram cfg hadm hcard hcap p
  constructor
  · have hrow := hrows.sigmaRow
    rw [hd3, hd5, hd6] at hrow
    omega
  · have hrow := hrows.kappaRow
    rw [hl3, hl4, hl5, hl6] at hrow
    have hsigma := hrows.sigmaRow
    rw [hd3, hd5, hd6] at hsigma
    omega

/-- A Type-B pivot cannot occur in the no-six-line subcase.  Consequently
any Type-B witness forces a positive global six-line count. -/
theorem twelveGallery_typeB_forces_positive_sixLineCount
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
    (p : alpha)
    (hd3 : (blockSystem cfg).blockDegree 3 p = 8)
    (hd4 : (blockSystem cfg).blockDegree 4 p = 9)
    (hd5 : (blockSystem cfg).blockDegree 5 p = 0)
    (hd6 : (blockSystem cfg).blockDegree 6 p = 2)
    (hl3 : (blockSystem cfg).lineDegree 3 p = 4)
    (hl4 : (blockSystem cfg).lineDegree 4 p = 0)
    (hl5 : (blockSystem cfg).lineDegree 5 p = 0)
    (hl6 : (blockSystem cfg).lineDegree 6 p = 0) :
    0 < (blockSystem cfg).lineCount 6 := by
  by_contra hnot
  have hL6 : (blockSystem cfg).lineCount 6 = 0 := by omega
  exact (twelveGallery_typeBForbidden_of_noSixLines
    Mel EvenArr Kelly Gram Direction cfg hadm hcard hcap gamma hgamma hL6)
    ⟨p, hd3, hd4, hd5, hd6, hl3, hl4, hl5, hl6⟩

/-- The positive six-line count in the residual Type-B case is realized by
an actual six-point determined line avoiding the Type-B pivot.  This removes
the last ambiguity in the existing `lineCount 6 ≠ 0` boundary. -/
theorem twelveGallery_typeB_forces_external_sixLine
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
    (p : alpha)
    (hd3 : (blockSystem cfg).blockDegree 3 p = 8)
    (hd4 : (blockSystem cfg).blockDegree 4 p = 9)
    (hd5 : (blockSystem cfg).blockDegree 5 p = 0)
    (hd6 : (blockSystem cfg).blockDegree 6 p = 2)
    (hl3 : (blockSystem cfg).lineDegree 3 p = 4)
    (hl4 : (blockSystem cfg).lineDegree 4 p = 0)
    (hl5 : (blockSystem cfg).lineDegree 5 p = 0)
    (hl6 : (blockSystem cfg).lineDegree 6 p = 0) :
    exists L : DeterminedLine cfg,
      (lineSupport cfg L).card = 6 /\ p ∉ lineSupport cfg L := by
  classical
  have hpositive : 0 < (blockSystem cfg).lineCount 6 :=
    twelveGallery_typeB_forces_positive_sixLineCount
      Mel EvenArr Kelly Gram Direction cfg hadm hcard hcap gamma hgamma p
      hd3 hd4 hd5 hd6 hl3 hl4 hl5 hl6
  have hsplit := lineCount_eq_lineDegree_add_card_away cfg p 6
  have hawayPositive :
      0 < Fintype.card (DeterminedLineOfSizeAway cfg p 6) := by
    omega
  let L : DeterminedLineOfSizeAway cfg p 6 :=
    Classical.choice (Fintype.card_pos_iff.mp hawayPositive)
  exact ⟨L.1.1, L.1.2, L.2⟩

end Erdos506.V1
