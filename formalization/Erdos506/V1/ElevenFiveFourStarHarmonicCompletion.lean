import Erdos506.V1.ElevenFive
import Erdos506.V1.ElevenFiveHarmonicFiveCap

/-!
# Completion interface for the eleven-five four-star harmonic transport

The determinant calculation already produces the unique normal four-star.
What remains geometric is not another finite alternative: for a concrete
five-circle through the pivot, its canonical `RP¹` trace has to be identified
with the inverse parameter image of the corresponding normal base trace.

`HasNormalCircleTraceTransport` records exactly that equality.  In
particular, it does not postulate harmonicity of the circle trace.  The
theorems below consume the equality using the proved `GL₂` invariance of the
cross-ratio.  The same comparison is needed for a five-line if the global
five-block cap is to include that tagged layer as well.
-/

namespace Erdos506.V1

open Erdos506.Block
open Erdos506.Block.BlockSystem
open Erdos506.Incidence
open Erdos506.V3
open Erdos506.V4

universe u

noncomputable local instance harmonicCompletionDecidableEqRP1 :
    DecidableEq RealProjectiveOnePoint := Classical.decEq _

/-- The exact normal-coordinate certificate required for one concrete
five-circle through a four-star pivot.  The right side is the inverse image
of a normal four-star trace under the parameter change induced by the
projective normalisation. -/
def ElevenFivePivotInvertedFourStar.HasNormalCircleTraceTransport
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (H : ElevenFivePivotInvertedFourStar cfg p) : Prop :=
  ∀ c : DeterminedCircle cfg,
    (circleTrace cfg c.1).card = 5 →
    (hp : p ∈ circleTrace cfg c.1) →
    ∃ (i : Fin 4) (g : GL (Fin 2) ℝ),
      properCircleTraceParameterSetErase cfg c.1 ⟨p, hp⟩ =
        (fourStarNormalTraceParameterSet i).image (fun P => g⁻¹ • P)

/-- The lossless transport step from a normal four-star trace to the
canonical projective parameters of the original proper circle. -/
theorem ElevenFivePivotInvertedFourStar.hasProperCircleHarmonicDeletion_of_normalCircleTraceTransport
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (H : ElevenFivePivotInvertedFourStar cfg p)
    (htransport : H.HasNormalCircleTraceTransport) :
    H.HasProperCircleHarmonicDeletion := by
  dsimp only [ElevenFivePivotInvertedFourStar.HasProperCircleHarmonicDeletion]
  intro c hfive hp
  unfold ElevenFivePivotInvertedFourStar.HasNormalCircleTraceTransport at htransport
  obtain ⟨i, g, htrace⟩ := htransport c hfive hp
  exact isRealProjectiveHarmonicFour_of_eq_image_inv_fourStarNormalTrace
    g _ i htrace

/-- The proper-circle deletion endpoint for a neutral pivot follows as soon
as its concrete circle traces have been identified with the normal traces.
The finite triangle-pendant survivor is already available inside the pivot
four-star construction; this theorem is the separate, geometric return leg
to the original circle parameters. -/
theorem elevenFive944_properCircleHarmonicDeletion_of_normalCircleTraceTransport
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    (cfg : Configuration Point) (hcard : Fintype.card Point = 11)
    (p : Point) (hp : p ∈ elevenFive944Pivots (blockSystem cfg))
    (htransport :
      (elevenFive944PivotFourStar cfg hcard p hp).HasNormalCircleTraceTransport) :
    ElevenFivePivotInvertedFourStar.HasProperCircleHarmonicDeletion
      (elevenFive944PivotFourStar cfg hcard p hp) := by
  exact ElevenFivePivotInvertedFourStar.hasProperCircleHarmonicDeletion_of_normalCircleTraceTransport
      (elevenFive944PivotFourStar cfg hcard p hp) htransport

/-- Applying the preceding transport at every neutral pivot gives the
proved weighted five-block incidence estimate. -/
theorem elevenFive_weighted_harmonicIncidenceCap_of_normalCircleTraceTransport
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    (cfg : Configuration Point) (hcard : Fintype.card Point = 11)
    (htransport : ∀ p : Point,
      (hp : p ∈ elevenFive944Pivots (blockSystem cfg)) →
      (elevenFive944PivotFourStar cfg hcard p hp).HasNormalCircleTraceTransport) :
    4 * (elevenFive944Pivots (blockSystem cfg)).card ≤
      5 * (blockSystem cfg).lineCount 5 +
        2 * (blockSystem cfg).circleCount 5 := by
  apply elevenFive_weighted_harmonicIncidenceCap_of_properCircleHarmonicDeletion
    cfg hcard
  intro p hp
  exact elevenFive944_properCircleHarmonicDeletion_of_normalCircleTraceTransport
    cfg hcard p hp (htransport p hp)

/-- The untagged version of the five-block double count.  It is the exact
form needed here: a cap on *every* size-five geometric block, including
five-lines, gives coefficient two on the full block count. -/
theorem four_mul_card_le_two_mul_blockCount_of_fiveBlock_cap
    {Point Block : Type*} [Fintype Point] [Fintype Block]
    [DecidableEq Point]
    (S : BlockSystem Point Block) (H : Finset Point)
    (hdegree : ∀ p ∈ H, S.blockDegree 5 p = 4)
    (hblock : ∀ b ∈ S.blocksOfSize 5,
      (H ∩ S.support b).card ≤ 2) :
    4 * H.card ≤ 2 * S.blockCount 5 := by
  classical
  have hfubini := S.sum_degreeIn_over (S.blocksOfSize 5) H
  have htotal :
      4 * H.card = ∑ p ∈ H, S.blockDegree 5 p := by
    calc
      4 * H.card = ∑ _p ∈ H, 4 := by simp [Nat.mul_comm]
      _ = ∑ p ∈ H, S.blockDegree 5 p := by
        apply Finset.sum_congr rfl
        intro p hp
        exact (hdegree p hp).symm
  rw [htotal]
  change (∑ p ∈ H, S.degreeIn (S.blocksOfSize 5) p) ≤ _
  rw [hfubini]
  calc
    (∑ b ∈ S.blocksOfSize 5, (H ∩ S.support b).card) ≤
        ∑ _b ∈ S.blocksOfSize 5, 2 := by
      exact Finset.sum_le_sum fun b hb => hblock b hb
    _ = 2 * S.blockCount 5 := by
      simp [BlockSystem.blockCount, Nat.mul_comm]

/-- Once the same `≤ 2` cap is available on five-lines as well as proper
five-circles, the desired eleven-five harmonic incidence inequality follows
without discarding the five-line layer.  The circle part is supplied by the
proper-circle harmonic transport; the remaining hypothesis is precisely the
line-layer finite cap. -/
theorem elevenFive_harmonicIncidenceCap_of_normalCircleTraceTransport_and_fiveLineCap
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    (cfg : Configuration Point) (hcard : Fintype.card Point = 11)
    (htransport : ∀ p : Point,
      (hp : p ∈ elevenFive944Pivots (blockSystem cfg)) →
      (elevenFive944PivotFourStar cfg hcard p hp).HasNormalCircleTraceTransport)
    (hline : ∀ b ∈ (blockSystem cfg).lineBlocksOfSize 5,
      (elevenFive944Pivots (blockSystem cfg) ∩
        (blockSystem cfg).support b).card ≤ 2) :
    4 * (elevenFiveHarmonicPivots (blockSystem cfg)).card ≤
      2 * (blockSystem cfg).blockCount 5 := by
  change 4 * (elevenFive944Pivots (blockSystem cfg)).card ≤
    2 * (blockSystem cfg).blockCount 5
  apply four_mul_card_le_two_mul_blockCount_of_fiveBlock_cap
    (blockSystem cfg) (elevenFive944Pivots (blockSystem cfg))
  · intro p hp
    exact blockDegree_five_eq_four_of_mem_elevenFive944Pivots hp
  · intro b hb
    rcases (blockSystem cfg).mem_blocksOfSize.mp hb with hsize
    cases hkind : (blockSystem cfg).kind b with
    | line =>
        apply hline b
        exact (blockSystem cfg).mem_blocksOfKindSize.mpr ⟨hkind, hsize⟩
    | circle =>
        exact elevenFive_harmonicPivots_on_circle_card_le_two_of_properCircleHarmonicDeletion
          cfg hcard
          (fun p hp =>
            elevenFive944_properCircleHarmonicDeletion_of_normalCircleTraceTransport
              cfg hcard p hp (htransport p hp)) b
          ((blockSystem cfg).mem_blocksOfKindSize.mpr ⟨hkind, hsize⟩)

/-- A direct constructor for the harmonic-incidence-cap slot, with the
five-line cap stated locally rather than replaced by the stronger and
unnecessary assertion that five-lines do not occur. -/
theorem realPlaneElevenFiveGeometry_harmonicIncidenceCap_of_normalCircleTraceTransport_and_fiveLineCap
    (htransport : ∀ {Point : Type u} [Fintype Point] [DecidableEq Point]
      (cfg : Configuration Point) (hcard : Fintype.card Point = 11)
      (p : Point) (hp : p ∈ elevenFive944Pivots (blockSystem cfg)),
      (elevenFive944PivotFourStar cfg hcard p hp).HasNormalCircleTraceTransport)
    (hline : ∀ {Point : Type u} [Fintype Point] [DecidableEq Point]
      (cfg : Configuration Point),
      Admissible cfg → Fintype.card Point = 11 →
      BlockSizeCap (blockSystem cfg) 5 →
      ∀ b ∈ (blockSystem cfg).lineBlocksOfSize 5,
        (elevenFive944Pivots (blockSystem cfg) ∩
          (blockSystem cfg).support b).card ≤ 2) :
    ∀ {Point : Type u} [Fintype Point] [DecidableEq Point]
      (cfg : Configuration Point),
      Admissible cfg → Fintype.card Point = 11 →
      BlockSizeCap (blockSystem cfg) 5 →
        4 * (elevenFiveHarmonicPivots (blockSystem cfg)).card ≤
          2 * (blockSystem cfg).blockCount 5 := by
  intro Point _ _ cfg hadm hcard hcap
  apply elevenFive_harmonicIncidenceCap_of_normalCircleTraceTransport_and_fiveLineCap
    cfg hcard
  · intro p hp
    exact htransport cfg hcard p hp
  · exact hline cfg hadm hcard hcap

end Erdos506.V1
