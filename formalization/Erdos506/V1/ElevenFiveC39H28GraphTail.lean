import Erdos506.V1.ElevenFiveC39H28Finish
import Erdos506.V1.ElevenFiveC39H29Finish
import Erdos506.V1.ElevenFiveC40FinalK31ActualGridTail
import Mathlib.Tactic

/-!
# The global singleton-graph tail of the C39 host router

The local `H = 28` adapter in `ElevenFiveC39H28Finish` supplies a
singleton five-block neighbour.  The signed front supplies the same
conclusion below host weight twenty-eight, while the completed `H = 29`
and `H = 30` routers put every proper five-circle at weight at most
twenty-eight.

The remaining input below is deliberately isolated as one finite
double-count statement.  It is the singleton graph argument on the five or
six size-five blocks: the completed singleton dispatcher makes every edge
carrier a high point of five-degree two; the six-vertex case is then closed
by the K1 pair moment and the final two-defect page count.  This is a
definition of a proposition passed explicitly to the conditional theorem,
not an axiom or a new real-plane principle.
-/

namespace Erdos506.V1

open Erdos506.Block
open Erdos506.Block.BlockSystem
open Erdos506.Incidence
open Erdos506.V3
open Erdos506.V4
open scoped BigOperators

universe u

/-- The one still-unmaterialized, purely finite double count in the H28
tail.  Its hypotheses expose exactly what the singleton graph uses: all
proper five-circles have host weight at most twenty-eight, and every one of
them has an actual singleton size-five neighbour. -/
def ElevenFiveC39H28SingletonGraphDoubleCount
    {alpha : Type u} [Fintype alpha] [DecidableEq alpha]
    (cfg : Configuration alpha) : Prop :=
  ∀
    (_hpoint : Fintype.card alpha = 11)
    (_hcap : BlockSizeCap (blockSystem cfg) 5)
    (_hlocal : ∀ p : alpha, ElevenFiveLocalRows (blockSystem cfg) p)
    (_hglobal : ElevenFiveGlobalRows (blockSystem cfg))
    (_hC : (blockSystem cfg).totalCircleCount = 39)
    (_hL : elevenFiveLineTotal (blockSystem cfg) = 12),
    (∀ b ∈ (blockSystem cfg).circleBlocksOfSize 5,
      elevenFiveHostWeight (blockSystem cfg)
        ((blockSystem cfg).support b) ≤ 28) →
    (∀ b ∈ (blockSystem cfg).circleBlocksOfSize 5,
      ∃ c, c ∈ (blockSystem cfg).blocksOfSize 5 ∧
        ((blockSystem cfg).support c ∩
          (blockSystem cfg).support b).card = 1) →
    False

/-- Under the existing K2.4 actual-configuration adapter and the isolated
finite singleton-graph double count, host weight twenty-eight is
impossible.  The `H = 29,30` exclusions are already unconditional. -/
theorem elevenFive_c39_hostWeight_ne_twenty_eight
    {alpha : Type u} [Fintype alpha] [DecidableEq alpha]
    (cfg : Configuration alpha)
    (hgolden : ElevenFiveC39H28GoldenAxisActualAdapter cfg)
    (hgraph : ElevenFiveC39H28SingletonGraphDoubleCount cfg)
    (hpoint : Fintype.card alpha = 11)
    (hcap : BlockSizeCap (blockSystem cfg) 5)
    (hlocal : ∀ p : alpha, ElevenFiveLocalRows (blockSystem cfg) p)
    (hglobal : ElevenFiveGlobalRows (blockSystem cfg))
    (hC : (blockSystem cfg).totalCircleCount = 39)
    (hL : elevenFiveLineTotal (blockSystem cfg) = 12)
    (Gamma : DeterminedCircle cfg)
    (hD : (circleTrace cfg Gamma.1).card = 5) :
    elevenFiveHostWeight (blockSystem cfg)
      (circleTrace cfg Gamma.1) ≠ 28 := by
  intro _hhost
  have hcircle (b : GeometricBlock cfg)
      (hb : b ∈ (blockSystem cfg).circleBlocksOfSize 5) :
      elevenFiveHostWeight (blockSystem cfg)
        ((blockSystem cfg).support b) ≤ 28 := by
    rcases b with L | delta
    · have hkind := ((blockSystem cfg).mem_blocksOfKindSize.mp hb).1
      change (.line : BlockKind) = .circle at hkind
      cases hkind
    · have hdelta := ((blockSystem cfg).mem_blocksOfKindSize.mp hb).2
      change (circleTrace cfg delta.1).card = 5 at hdelta
      change elevenFiveHostWeight (blockSystem cfg)
        (circleTrace cfg delta.1) ≤ 28
      have hthirty := elevenFiveHostWeight_le_thirty
        (blockSystem cfg) (circleTrace cfg delta.1) hpoint hdelta
      have hne29 := elevenFive_c39_hostWeight_ne_twenty_nine
        cfg hpoint hcap hglobal hC hL delta hdelta
      have hne30 := elevenFive_c39_hostWeight_ne_thirty
        cfg hpoint hcap hglobal hC hL delta hdelta
      omega
  have hsingleton (b : GeometricBlock cfg)
      (hb : b ∈ (blockSystem cfg).circleBlocksOfSize 5) :
      ∃ c, c ∈ (blockSystem cfg).blocksOfSize 5 ∧
        ((blockSystem cfg).support c ∩
          (blockSystem cfg).support b).card = 1 := by
    rcases b with L | delta
    · have hkind := ((blockSystem cfg).mem_blocksOfKindSize.mp hb).1
      change (.line : BlockKind) = .circle at hkind
      cases hkind
    · have hdelta := ((blockSystem cfg).mem_blocksOfKindSize.mp hb).2
      change (circleTrace cfg delta.1).card = 5 at hdelta
      change ∃ c, c ∈ (blockSystem cfg).blocksOfSize 5 ∧
        ((blockSystem cfg).support c ∩ circleTrace cfg delta.1).card = 1
      have hweight := hcircle (Sum.inr delta) hb
      change elevenFiveHostWeight (blockSystem cfg)
        (circleTrace cfg delta.1) ≤ 28 at hweight
      by_cases heq : elevenFiveHostWeight (blockSystem cfg)
          (circleTrace cfg delta.1) = 28
      · have hpos :=
          elevenFive_c39_h28_relativeCount_one_four_pos_of_goldenAxisActualAdapter
            cfg hgolden delta hpoint hdelta heq
        have hex :=
          (elevenFive_relativeCount_one_four_pos_iff_exists_sizeFive_singleton
            (blockSystem cfg) (circleTrace cfg delta.1)).mp hpos
        exact hex
      · have hle : elevenFiveHostWeight (blockSystem cfg)
            (circleTrace cfg delta.1) ≤ 27 := by omega
        have hex :=
          elevenFive_c39_singleton_exists_of_rebased_signed_front
            (blockSystem cfg) (circleTrace cfg delta.1)
              hpoint hdelta hle
              (elevenFive_c39_rebased_signed_front_of_rows
                (blockSystem cfg) hpoint hcap hlocal hglobal hC hL
                  (Sum.inr delta) hb)
        exact hex
  exact hgraph hpoint hcap hlocal hglobal hC hL hcircle hsingleton

/-- Conditional final C39 contradiction.  The selected proper five-circle
has host weight in `[28,30]`; the three endpoint routers exclude 28, 29,
and 30 respectively. -/
theorem elevenFive_c39_l12_absurd_of_h28_adapters
    {alpha : Type u} [Fintype alpha] [DecidableEq alpha]
    (Mel : RealPlaneMelchiorPrinciple.{u})
    (Langer : RealPlaneLangerPrinciple.{u})
    (EvenArr : RealPlaneEvenArrangementPrinciple.{u})
    (Cross : RealPlaneRadicalAxisCrossBlockPrinciple.{u})
    (Kelly : RealPlaneKellyMoserPrinciple.{u})
    (U17 : RealPlaneSixCircleU17Principle.{u})
    (TenGeometry : RealPlaneTenFiveGeometry.{u})
    (cfg : Configuration alpha) (hadm : Admissible cfg)
    (hgolden : ElevenFiveC39H28GoldenAxisActualAdapter cfg)
    (hgraph : ElevenFiveC39H28SingletonGraphDoubleCount cfg)
    (hcard : Fintype.card alpha = 11)
    (hcap : BlockSizeCap (blockSystem cfg) 5)
    (hCcount : Erdos506.V4.circleCount cfg = 39)
    (hL : elevenFiveLineTotal (blockSystem cfg) = 12) : False := by
  have hbridge : (blockSystem cfg).totalCircleCount =
      Erdos506.V4.circleCount cfg := by
    rw [totalCircleCount_eq_card_determinedCircle,
      ← Erdos506.V3.circleCount_eq_card_determinedCircle]
  have hC : (blockSystem cfg).totalCircleCount = 39 := by omega
  have hCupper : (blockSystem cfg).totalCircleCount ≤ 40 := by omega
  have hlocal : ∀ p : alpha,
      ElevenFiveLocalRows (blockSystem cfg) p := by
    intro p
    exact elevenFiveLocalRows_of_configuration
      Mel Langer EvenArr Cross Kelly U17 TenGeometry
        cfg hadm hcard hcap hCupper p
  have hglobal : ElevenFiveGlobalRows (blockSystem cfg) :=
    elevenFiveGlobalRows_of_configuration Mel cfg hadm hcard hcap hlocal
  obtain ⟨delta, hdelta, hlower, hupper⟩ :=
    elevenFive_c39_l12_exists_properFiveCircle_host_between_twenty_eight_thirty
      Mel Langer EvenArr Cross Kelly U17 TenGeometry
        cfg hadm hcard hcap hCcount hL
  have hne28 := elevenFive_c39_hostWeight_ne_twenty_eight
    cfg hgolden hgraph hcard hcap hlocal hglobal hC hL delta hdelta
  have hne29 := elevenFive_c39_hostWeight_ne_twenty_nine
    cfg hcard hcap hglobal hC hL delta hdelta
  have hne30 := elevenFive_c39_hostWeight_ne_thirty
    cfg hcard hcap hglobal hC hL delta hdelta
  omega

end Erdos506.V1
