import Erdos506.V1.TwelveDirectionProjectiveChartBridge

/-!
# The local Type-B gallery contradiction

The Type-B word has no six-line through its distinguished pivot, but it has
two six-blocks through that pivot.  The local form of the direction argument
therefore applies without any assumption on six-lines elsewhere in the
configuration.  Its strict defect numerator is incompatible with
`(d5,d6,sigma) = (0,2,1)`.
-/

namespace Erdos506.V1

open Erdos506.Block
open Erdos506.Block.BlockSystem
open Erdos506.Incidence
open Erdos506.V4

universe u

/-- The Type-B gallery field follows from the actual projective-chart
direction argument.  No global `lineCount 6 = 0` hypothesis is used. -/
theorem twelveGallery_typeBForbidden
    {alpha : Type u} [Fintype alpha] [DecidableEq alpha]
    (Mel : RealPlaneMelchiorPrinciple.{u})
    (EvenArr : RealPlaneEvenArrangementPrinciple.{u})
    (Kelly : RealPlaneKellyMoserPrinciple.{u})
    (Gram : RealPlaneTwelveGramPrinciple.{u})
    (cfg : Configuration alpha) (hadm : Admissible cfg)
    (hcard : Fintype.card alpha = 12)
    (hcap : BlockSizeCap (blockSystem cfg) 6) :
    Not (exists p : alpha,
      (blockSystem cfg).blockDegree 3 p = 8 /\
      (blockSystem cfg).blockDegree 4 p = 9 /\
      (blockSystem cfg).blockDegree 5 p = 0 /\
      (blockSystem cfg).blockDegree 6 p = 2 /\
      (blockSystem cfg).lineDegree 3 p = 4 /\
      (blockSystem cfg).lineDegree 4 p = 0 /\
      (blockSystem cfg).lineDegree 5 p = 0 /\
      (blockSystem cfg).lineDegree 6 p = 0) := by
  rintro ⟨p, hd3, _hd4, hd5, hd6, _hl3, _hl4, _hl5, hl6⟩
  obtain ⟨c, hp, hcircle⟩ :=
    exists_six_circle_through_of_blockDegree_six_pos_of_lineDegree_six_eq_zero
      cfg p (by omega) hl6
  have hgap : 0 < twelveDirectionEqualityGap (blockSystem cfg) p :=
    twelveDirectionEqualityGap_pos_of_projectiveChartBridge
      cfg p c hp hcard hcircle hcap hl6
        (projectiveChartBridge_of_six_dual_lines_covered_by_five_pencil_lines
          cfg p c hp)
  have hrows : TwelveSixLocalRows (blockSystem cfg) p :=
    twelveSixLocalRows_of_configuration
      Mel EvenArr Kelly Gram cfg hadm hcard hcap p
  have hsigmaEq : twelveSixSigmaAt (blockSystem cfg) p = 1 := by
    have hrow := hrows.sigmaRow
    rw [hd3, hd5, hd6] at hrow
    omega
  have hnum :=
    three_le_twelveDirectionDefectNumerator_of_gap_pos
      (blockSystem cfg) p hrows hgap
  rw [hd5, hd6, hsigmaEq] at hnum
  norm_num at hnum

/-- The sole gallery input that remains after the Type-B field is discharged. -/
structure RealPlaneTwelveGalleryTypeAPrinciple where
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

/-- Reconstruct the legacy two-field gallery package from its only remaining
geometric field. -/
noncomputable def RealPlaneTwelveGalleryTypeAPrinciple.toGallery
    (GalleryA : RealPlaneTwelveGalleryTypeAPrinciple.{u})
    (Mel : RealPlaneMelchiorPrinciple.{u})
    (EvenArr : RealPlaneEvenArrangementPrinciple.{u})
    (Kelly : RealPlaneKellyMoserPrinciple.{u})
    (Gram : RealPlaneTwelveGramPrinciple.{u}) :
    RealPlaneTwelveGalleryPrinciple.{u} where
  typeAForbidden := GalleryA.typeAForbidden
  typeBForbidden := twelveGallery_typeBForbidden Mel EvenArr Kelly Gram

end Erdos506.V1
