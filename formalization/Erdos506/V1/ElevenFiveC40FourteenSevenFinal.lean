import Erdos506.V1.ElevenFiveC40FourteenSevenM39DisjointFinish
import Erdos506.V1.ElevenFiveC40FourteenSevenM40NoDisjointFinish
import Erdos506.V1.ElevenFiveGeometryFinal

/-!
# Final C40/L14/B5=7 assembly

The four possible five-block pair moments are now all contradictory.  This
module packages that row theorem, lifts it to configurations using the
unconditional local/global rows, and discharges the last field of the
eleven-point residual geometry interface.
-/

namespace Erdos506.V1

open Erdos506.Block
open Erdos506.Block.BlockSystem
open Erdos506.Incidence
open Erdos506.V3
open Erdos506.V4

universe u

/-- All four possible moments `39,40,41,42` in the C40/L14/B5=7 row are
impossible. -/
theorem elevenFive_c40_l14_b5_seven_impossible
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    (cfg : Configuration Point) (hpoint : Fintype.card Point = 11)
    (hcap : BlockSizeCap (blockSystem cfg) 5)
    (hlocal : ∀ p : Point, ElevenFiveLocalRows (blockSystem cfg) p)
    (hglobal : ElevenFiveGlobalRows (blockSystem cfg))
    (hC : (blockSystem cfg).totalCircleCount = 40)
    (hL : elevenFiveLineTotal (blockSystem cfg) = 14)
    (hfive : (blockSystem cfg).blockCount 5 = 7) : False := by
  classical
  let S := blockSystem cfg
  have hlower := elevenFive_c40_l14_b5_seven_secondMoment_ge_thirtyNine
    S hpoint (by simpa [S] using hlocal) (by simpa [S] using hglobal)
      (by simpa [S] using hfive)
  have hupper := elevenFive_c40_l14_b5_seven_secondMoment_le_fortyTwo
    S (by simpa [S] using hfive)
  have hcases : elevenFiveSecondMoment S = 39 ∨
      elevenFiveSecondMoment S = 40 ∨
      elevenFiveSecondMoment S = 41 ∨
      elevenFiveSecondMoment S = 42 := by omega
  rcases hcases with h39 | h40 | h41 | h42
  · by_cases hex : ∃ f, f ∈ S.blocksOfSize 5 ∧
        ∃ g, g ∈ S.blocksOfSize 5 ∧ f ≠ g ∧
          (S.support f ∩ S.support g).card = 0
    · obtain ⟨f, hf, g, hg, hfg, hzero⟩ := hex
      exact elevenFive_c40_l14_b5_seven_secondMoment_thirtyNine_disjoint_impossible
        cfg hpoint hcap hlocal hglobal hC hL hfive
          (by simpa [S] using h39) (by simpa [S] using hf)
            (by simpa [S] using hg) hfg (by simpa [S] using hzero)
    · apply elevenFive_c40_l14_b5_seven_m39_threeMatching_impossible
        cfg hpoint hcap hlocal hglobal hC hL hfive (by simpa [S] using h39)
      intro b hb c hc hbc hzero
      exact hex ⟨b, by simpa [S] using hb, c, by simpa [S] using hc,
        hbc, by simpa [S] using hzero⟩
  · by_cases hex : ∃ f, f ∈ S.blocksOfSize 5 ∧
        ∃ g, g ∈ S.blocksOfSize 5 ∧ f ≠ g ∧
          (S.support f ∩ S.support g).card = 0
    · obtain ⟨f, hf, g, hg, hfg, hzero⟩ := hex
      exact elevenFive_c40_l14_b5_seven_secondMoment_forty_disjoint_impossible
        cfg hpoint hcap hlocal hglobal hC hL hfive
          (by simpa [S] using h40) (by simpa [S] using hf)
            (by simpa [S] using hg) hfg (by simpa [S] using hzero)
    · apply elevenFive_c40_l14_b5_seven_m40_noDisjoint_impossible
        cfg hpoint hcap hlocal hglobal hC hL hfive (by simpa [S] using h40)
      intro b hb c hc hbc hzero
      exact hex ⟨b, by simpa [S] using hb, c, by simpa [S] using hc,
        hbc, by simpa [S] using hzero⟩
  · exact elevenFive_c40_l14_b5_seven_secondMoment_fortyOne_impossible
      cfg hpoint hcap hlocal hglobal hC hL hfive (by simpa [S] using h41)
  · exact elevenFive_c40_l14_b5_seven_secondMoment_fortyTwo_impossible
      cfg hpoint hcap hlocal hglobal hC hL hfive (by simpa [S] using h42)

/-- Configuration-level form of the final C40/L14/B5=7 contradiction. -/
theorem elevenFive_c40_l14_b5_seven_collision_unconditional_without_langer
    (Mel : RealPlaneMelchiorPrinciple.{u})
    (EvenArr : RealPlaneEvenArrangementPrinciple.{u})
    (Cross : RealPlaneRadicalAxisCrossBlockPrinciple.{u})
    (Kelly : RealPlaneKellyMoserPrinciple.{u})
    (U17 : RealPlaneSixCircleU17Principle.{u})
    (TenGeometry : RealPlaneTenFiveGeometry.{u})
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    (cfg : Configuration Point) (hadm : Admissible cfg)
    (hpoint : Fintype.card Point = 11)
    (hcap : BlockSizeCap (blockSystem cfg) 5)
    (hC : Erdos506.V4.circleCount cfg = 40)
    (hL : elevenFiveLineTotal (blockSystem cfg) = 14)
    (hfive : (blockSystem cfg).blockCount 5 = 7) :
    ElevenFiveTripleCollision (blockSystem cfg) := by
  have hCtotal : (blockSystem cfg).totalCircleCount = 40 := by
    rw [totalCircleCount_eq_card_determinedCircle,
      ← Erdos506.V3.circleCount_eq_card_determinedCircle]
    exact hC
  have hCupper : (blockSystem cfg).totalCircleCount ≤ 40 := by omega
  have hlocal : ∀ p : Point, ElevenFiveLocalRows (blockSystem cfg) p :=
    fun p => elevenFiveLocalRows_of_configuration_without_langer
      Mel EvenArr Cross Kelly U17 TenGeometry
        cfg hadm hpoint hcap hCupper p
  have hglobal : ElevenFiveGlobalRows (blockSystem cfg) :=
    elevenFiveGlobalRows_of_configuration Mel cfg hadm hpoint hcap hlocal
  exact False.elim (elevenFive_c40_l14_b5_seven_impossible
    cfg hpoint hcap hlocal hglobal hCtotal hL hfive)

/-- Compatibility wrapper retaining the historical Langer parameter. -/
theorem elevenFive_c40_l14_b5_seven_collision_unconditional
    (Mel : RealPlaneMelchiorPrinciple.{u})
    (_Langer : RealPlaneLangerPrinciple.{u})
    (EvenArr : RealPlaneEvenArrangementPrinciple.{u})
    (Cross : RealPlaneRadicalAxisCrossBlockPrinciple.{u})
    (Kelly : RealPlaneKellyMoserPrinciple.{u})
    (U17 : RealPlaneSixCircleU17Principle.{u})
    (TenGeometry : RealPlaneTenFiveGeometry.{u})
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    (cfg : Configuration Point) (hadm : Admissible cfg)
    (hpoint : Fintype.card Point = 11)
    (hcap : BlockSizeCap (blockSystem cfg) 5)
    (hC : Erdos506.V4.circleCount cfg = 40)
    (hL : elevenFiveLineTotal (blockSystem cfg) = 14)
    (hfive : (blockSystem cfg).blockCount 5 = 7) :
    ElevenFiveTripleCollision (blockSystem cfg) :=
  elevenFive_c40_l14_b5_seven_collision_unconditional_without_langer
    Mel EvenArr Cross Kelly U17 TenGeometry
      cfg hadm hpoint hcap hC hL hfive

/-- The last residual eleven-point geometry field is now unconditional. -/
noncomputable def realPlaneElevenFiveResidualGeometry
    (Mel : RealPlaneMelchiorPrinciple.{u})
    (EvenArr : RealPlaneEvenArrangementPrinciple.{u})
    (Cross : RealPlaneRadicalAxisCrossBlockPrinciple.{u})
    (Kelly : RealPlaneKellyMoserPrinciple.{u})
    (U17 : RealPlaneSixCircleU17Principle.{u})
    (TenReduction : RealPlaneTenFiveReductionPrinciple.{u}) :
    RealPlaneElevenFiveResidualGeometry.{u} where
  c40FourteenSevenExternalTraceCollision := by
    intro Point _ _ cfg hadm hpoint hcap hC hL hfive
    exact elevenFive_c40_l14_b5_seven_collision_unconditional_without_langer
      Mel EvenArr Cross Kelly U17 TenReduction.toGeometry
        cfg hadm hpoint hcap hC hL hfive

end Erdos506.V1
