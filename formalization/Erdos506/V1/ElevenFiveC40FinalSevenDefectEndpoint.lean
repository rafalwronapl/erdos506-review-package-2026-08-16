import Erdos506.V1.ElevenFiveC40FinalBetaCapCount

/-!
# The unconditional C40/L11 seven-defect endpoint

The only former geometric input for the `B₅ = 7` C40/L11 face is now a
consequence of the ordinary eleven-point local/global rows and the
pivot-inversion beta cap.
-/

namespace Erdos506.V1

open Erdos506.Block
open Erdos506.Block.BlockSystem
open Erdos506.Incidence
open Erdos506.V3
open Erdos506.V4
open scoped BigOperators

universe u

/-- The exact former `C = 40, L = 11, B₅ = 7` collision field is
unconditional: its hypotheses are already contradictory. -/
theorem elevenFive_c40_l11_sevenDefectCollision_unconditional_without_langer
    (Mel : RealPlaneMelchiorPrinciple.{u})
    (EvenArr : RealPlaneEvenArrangementPrinciple.{u})
    (Cross : RealPlaneRadicalAxisCrossBlockPrinciple.{u})
    (Kelly : RealPlaneKellyMoserPrinciple.{u})
    (U17 : RealPlaneSixCircleU17Principle.{u})
    (TenGeometry : RealPlaneTenFiveGeometry.{u})
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    (cfg : Configuration Point) (hadm : Admissible cfg)
    (hcard : Fintype.card Point = 11)
    (hcap : BlockSizeCap (blockSystem cfg) 5)
    (hC : Erdos506.V4.circleCount cfg = 40)
    (hL : elevenFiveLineTotal (blockSystem cfg) = 11)
    (hfive : (blockSystem cfg).blockCount 5 = 7) :
    ElevenFiveTripleCollision (blockSystem cfg) := by
  have hCtotal : (blockSystem cfg).totalCircleCount = 40 := by
    rw [totalCircleCount_eq_card_determinedCircle,
      ← Erdos506.V3.circleCount_eq_card_determinedCircle]
    exact hC
  have hCupper : (blockSystem cfg).totalCircleCount ≤ 40 := by
    omega
  have hlocal : ∀ p : Point,
      ElevenFiveLocalRows (blockSystem cfg) p := fun p =>
    elevenFiveLocalRows_of_configuration_without_langer
      Mel EvenArr Cross Kelly U17 TenGeometry
        cfg hadm hcard hcap hCupper p
  have hglobal : ElevenFiveGlobalRows (blockSystem cfg) :=
    elevenFiveGlobalRows_of_configuration
      Mel cfg hadm hcard hcap hlocal
  have hbeta := elevenFive_c40_l11_beta_cap
    Mel EvenArr Cross Kelly U17 TenGeometry
      cfg hadm hcard hcap hglobal hCtotal hL
  exact False.elim
    (elevenFive_c40_l11_sevenDefect_impossible_of_beta_cap
      cfg hcard hlocal hglobal hCtotal hfive hbeta)

/-- Compatibility wrapper retaining the historical global parameter list. -/
theorem elevenFive_c40_l11_sevenDefectCollision_unconditional
    (Mel : RealPlaneMelchiorPrinciple.{u})
    (_Langer : RealPlaneLangerPrinciple.{u})
    (EvenArr : RealPlaneEvenArrangementPrinciple.{u})
    (Cross : RealPlaneRadicalAxisCrossBlockPrinciple.{u})
    (Kelly : RealPlaneKellyMoserPrinciple.{u})
    (U17 : RealPlaneSixCircleU17Principle.{u})
    (TenGeometry : RealPlaneTenFiveGeometry.{u})
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    (cfg : Configuration Point) (hadm : Admissible cfg)
    (hcard : Fintype.card Point = 11)
    (hcap : BlockSizeCap (blockSystem cfg) 5)
    (hC : Erdos506.V4.circleCount cfg = 40)
    (hL : elevenFiveLineTotal (blockSystem cfg) = 11)
    (hfive : (blockSystem cfg).blockCount 5 = 7) :
    ElevenFiveTripleCollision (blockSystem cfg) :=
  elevenFive_c40_l11_sevenDefectCollision_unconditional_without_langer
    Mel EvenArr Cross Kelly U17 TenGeometry
      cfg hadm hcard hcap hC hL hfive

end Erdos506.V1
