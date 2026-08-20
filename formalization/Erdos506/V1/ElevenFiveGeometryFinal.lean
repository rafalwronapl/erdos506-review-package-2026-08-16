import Erdos506.V1.ElevenFiveLineTraceComparison
import Erdos506.V1.ElevenFiveC40FinalSevenDefectEndpoint
import Erdos506.V1.ElevenFiveC40FinalFourteenEightEndpoint
import Erdos506.V1.ElevenFiveC39H28SingletonOrDisjointFinish
import Erdos506.V1.ElevenFiveC40SmallFiveGeometryFinish
import Erdos506.V1.ElevenFiveC40SmallSixPageCapFinish

/-!
# The unconditional harmonic part of the eleven-five geometry interface

The circle and line trace comparisons now supply both halves of the
harmonic-incidence estimate, while the host-pair-fibre count closes C39 and
the pair-fibre page cap closes the C40/L11 small faces.  Consequently the
public residual interface contains only the C40/L14 seven-block certificate.
-/

namespace Erdos506.V1

open Erdos506.Block
open Erdos506.Block.BlockSystem
open Erdos506.Incidence
open Erdos506.V4

universe u

/-- The former harmonic field of `RealPlaneElevenFiveGeometry`, proved from
the canonical circle and line projective transports. -/
theorem elevenFive_harmonicIncidenceCap_unconditional
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    (cfg : Configuration Point) (_hadm : Admissible cfg)
    (hcard : Fintype.card Point = 11)
    (_hcap : BlockSizeCap (blockSystem cfg) 5) :
    4 * (elevenFiveHarmonicPivots (blockSystem cfg)).card ≤
      2 * (blockSystem cfg).blockCount 5 := by
  apply elevenFive_harmonicIncidenceCap_of_normalCircleTraceTransport_and_fiveLineCap
    cfg hcard
  · intro p hp
    exact elevenFive944_normalCircleTraceTransport cfg hcard p hp
  · exact elevenFive944Pivots_fiveLine_cap cfg hcard

/-- The genuinely residual eleven-point geometry input.  Compared with
`RealPlaneElevenFiveGeometry`, its harmonic-incidence, C39, and C40/L11
small-face fields have disappeared. -/
structure RealPlaneElevenFiveResidualGeometry where
  c40FourteenSevenExternalTraceCollision :
    ∀ {α : Type u} [Fintype α] [DecidableEq α]
      (cfg : Configuration α),
      Admissible cfg → Fintype.card α = 11 →
      BlockSizeCap (blockSystem cfg) 5 →
      Erdos506.V4.circleCount cfg = 40 →
      elevenFiveLineTotal (blockSystem cfg) = 14 →
      (blockSystem cfg).blockCount 5 = 7 →
        ElevenFiveTripleCollision (blockSystem cfg)

/-- Reinsert the now-proved harmonic theorem for the internal legacy
eleven-five endpoint. -/
noncomputable def RealPlaneElevenFiveResidualGeometry.toGeometry_without_langer
    (R : RealPlaneElevenFiveResidualGeometry.{u})
    (Mel : RealPlaneMelchiorPrinciple.{u})
    (EvenArr : RealPlaneEvenArrangementPrinciple.{u})
    (Cross : RealPlaneRadicalAxisCrossBlockPrinciple.{u})
    (Kelly : RealPlaneKellyMoserPrinciple.{u})
    (U17 : RealPlaneSixCircleU17Principle.{u})
    (TenReduction : RealPlaneTenFiveReductionPrinciple.{u}) :
    RealPlaneElevenFiveGeometry.{u} where
  harmonicIncidenceCap := elevenFive_harmonicIncidenceCap_unconditional
  c39MaximumHostOverload := by
    intro α _ _ cfg hadm hcard hcap hC hL
    exact (elevenFive_c39_l12_absurd_of_hostPairFibres_without_langer
      Mel EvenArr Cross Kelly U17 TenReduction.toGeometry
        cfg hadm hcard hcap hC hL).elim
  c40ElevenSmallFaceCollision := by
    intro α _ _ cfg hadm hcard hcap hC hL hfive
    rcases hfive with hfive | hfive
    · exact (elevenFive_c40_l11_b5_five_impossible_of_configuration_without_langer
        Mel EvenArr Cross Kelly U17 TenReduction.toGeometry
          cfg hadm hcard hcap hC hL hfive).elim
    · exact (elevenFive_c40_l11_b5_six_impossible_of_configuration_without_langer
        Mel EvenArr Cross Kelly U17 TenReduction.toGeometry
          cfg hadm hcard hcap hC hL hfive).elim
  c40ElevenSevenDefectCollision :=
    elevenFive_c40_l11_sevenDefectCollision_unconditional_without_langer
      Mel EvenArr Cross Kelly U17 TenReduction.toGeometry
  c40FourteenSevenExternalTraceCollision := R.c40FourteenSevenExternalTraceCollision
  c40FourteenEightDefectCollision :=
    elevenFive_c40_l14_eightDefectCollision_unconditional_without_langer
      Mel EvenArr Cross Kelly U17 TenReduction.toGeometry

/-- Compatibility constructor retaining the historical global parameter list. -/
noncomputable def RealPlaneElevenFiveResidualGeometry.toGeometry
    (R : RealPlaneElevenFiveResidualGeometry.{u})
    (Mel : RealPlaneMelchiorPrinciple.{u})
    (_Langer : RealPlaneLangerPrinciple.{u})
    (EvenArr : RealPlaneEvenArrangementPrinciple.{u})
    (Cross : RealPlaneRadicalAxisCrossBlockPrinciple.{u})
    (Kelly : RealPlaneKellyMoserPrinciple.{u})
    (U17 : RealPlaneSixCircleU17Principle.{u})
    (TenReduction : RealPlaneTenFiveReductionPrinciple.{u}) :
    RealPlaneElevenFiveGeometry.{u} :=
  R.toGeometry_without_langer
    Mel EvenArr Cross Kelly U17 TenReduction

end Erdos506.V1
