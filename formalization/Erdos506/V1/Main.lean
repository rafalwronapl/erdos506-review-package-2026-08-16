import Erdos506.V1.Eleven
import Erdos506.V1.ElevenFiveC40FourteenSevenFinal
import Erdos506.V1.LangerApplicationAssembly
import Erdos506.V1.LangerApplicationFiniteWindowFinal
import Erdos506.V1.TenFivePunctured
import Erdos506.V1.ThirteenFull
import Erdos506.V1.Twelve
import Erdos506.V1.TwelveGridGeometryFinal
import Erdos506.V1.TwelveGram
import Erdos506.V1.TwelveGalleryTypeACutSaturationFinish
import Erdos506.V1.TwelveGalleryTypeBFinish
import Erdos506.Incidence.RadicalAxisFourFour
import Erdos506.Incidence.SixConicU17
import Erdos506.Incidence.RealPlaneArrangementPrinciples
import Erdos506.Incidence.RealPlaneKellyMoserFiniteRangeFinish

/-!
# Callback-free V1 assembly

This module closes the four finite callbacks in `FiniteHardCore` with the
configuration-level theorems for ten, eleven, twelve, and thirteen labels.
Melchior, the even-arrangement principle, and the guarded Kelly--Moser
instances actually used at sizes `9..12` are now constructed locally.  The
finite Langer window `14..22` and the large tail are discharged internally,
so the public theorem has no geometric principle parameter.  No argument
states a circle-count conclusion.
-/

namespace Erdos506.V1

open Erdos506.Incidence Erdos506.V4

universe u

/-- The public V1 lower bound with the exact finite hard core discharged.

The `SmallHardCase` witnesses produced by the outer router are deliberately
unused: each callback is closed by a theorem for every admissible
configuration of the corresponding cardinality.  The Melchior and
even-arrangement inputs are assembled locally and are not public parameters.
The eleven-point branch and the outer finite window are both independent of
Langer. -/
theorem circleCount_ge_v1Target
    {alpha : Type u} [Fintype alpha] [DecidableEq alpha]
    (cfg : Configuration alpha) (hadm : Admissible cfg)
    (hcard : 4 <= Fintype.card alpha) :
    Erdos506.v1Target (Fintype.card alpha) <=
      Erdos506.V4.circleCount cfg := by
  let Mel : RealPlaneMelchiorPrinciple.{u} :=
    realPlaneMelchiorPrinciple
  let EvenArr : RealPlaneEvenArrangementPrinciple.{u} :=
    realPlaneEvenArrangementPrinciple
  let Kelly : RealPlaneKellyMoserPrinciple.{u} :=
    realPlaneKellyMoserPrincipleOfFiniteSizes Mel EvenArr
  let Cross : RealPlaneRadicalAxisCrossBlockPrinciple.{u} :=
    realPlaneFourFourCrossBlockPrinciple.toCross
  let TenReduction : RealPlaneTenFiveReductionPrinciple.{u} :=
    realPlaneTenFiveReductionPrinciple Mel EvenArr
  let ElevenGeometry : RealPlaneElevenFiveResidualGeometry.{u} :=
    realPlaneElevenFiveResidualGeometry
      Mel EvenArr Cross Kelly realPlaneSixCircleU17Principle TenReduction
  let Direction : RealPlaneTwelveDirectionPrinciple.{u} :=
    realPlaneTwelveDirectionPrinciple
      Mel EvenArr Kelly realPlaneTwelveGramPrinciple
  let GalleryA : RealPlaneTwelveGalleryTypeAPrinciple.{u} :=
    realPlaneTwelveGalleryTypeAPrinciple
      FiniteProjectiveLineArrangement.realProjectiveArrangementGlobalInput
        Kelly realPlaneTwelveGramPrinciple
  let Gallery : RealPlaneTwelveGalleryPrinciple.{u} :=
    GalleryA.toGallery Mel EvenArr Kelly realPlaneTwelveGramPrinciple
  apply circleCount_ge_target_of_exact_finite_hard_core_without_langer
    Mel EvenArr Cross Kelly realPlaneSixCircleU17Principle
      cfg hadm hcard
  · intro hmin hmax
    rw [Erdos506.v1Target_eq_uniform (by omega)]
    exact v1UniformTarget_le_circleCount_finiteWindow_without_langer
      Mel EvenArr Cross Kelly realPlaneSixCircleU17Principle
        TenReduction.toGeometry TenReduction
          (ElevenGeometry.toGeometry_without_langer Mel EvenArr Cross Kelly
            realPlaneSixCircleU17Principle TenReduction)
          realPlaneTwelveGramPrinciple realPlaneTwelveGridPrinciple
            Gallery Direction cfg hadm hmin hmax
  · intro hten _hsmall _gamma _hgamma
    exact circleCount_ge_thirty_three_of_card_ten
      Mel EvenArr Cross Kelly realPlaneSixCircleU17Principle
        TenReduction.toGeometry
        cfg hadm hten
  · intro heleven _hsmall _gamma _hgamma
    exact circleCount_ge_forty_one_of_card_eleven_without_langer
      Mel EvenArr Cross Kelly realPlaneSixCircleU17Principle
        TenReduction
          (ElevenGeometry.toGeometry_without_langer Mel EvenArr Cross Kelly
            realPlaneSixCircleU17Principle TenReduction)
          cfg hadm heleven
  · intro htwelve _hsmall _gamma _hgamma
    exact circleCount_ge_fifty_one_of_card_twelve
      Mel EvenArr Kelly realPlaneTwelveGramPrinciple
        realPlaneTwelveGridPrinciple Gallery Direction
        cfg hadm htwelve
  · intro hthirteen _hsmall _gamma _hgamma
    exact circleCount_ge_sixty_one_of_card_thirteen
      Mel cfg hadm hthirteen

end Erdos506.V1
