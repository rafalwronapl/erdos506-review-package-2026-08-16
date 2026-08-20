import Erdos506.Incidence.ProjectiveLineParamTransport
import Erdos506.Incidence.RealProjectiveHarmonicFiveCap
import Erdos506.V1.ElevenFiveHarmonicFiveCap

/-!
# The five-line harmonic cap: the exact projective compatibility interface

The circle adapter already has a canonical projective parameter.  A five-line
needs one *shared* projective trace for all five possible pivot deletions.
This file isolates that requirement.  It is deliberately stronger than a
cardinality bound, and is invariant under the normal-coordinate `GL₂` change
used by the four-star calculation.

In particular, `HasHarmonicBaseSupports` is not used here: its parameter is
unconstrained, whereas the trace below is one fixed embedding of the actual
five-line support.
-/

namespace Erdos506.V1

open Erdos506.Block
open Erdos506.Block.BlockSystem
open Erdos506.Incidence
open Erdos506.V3
open Erdos506.V4

universe u

noncomputable local instance lineHarmonicDecidableEqRP1 :
    DecidableEq RealProjectiveOnePoint := Classical.decEq _

/-- The projective trace of one concrete line block, with no choice of an
ordering of the five points. -/
noncomputable def lineBlockProjectiveTrace
    {Point Block : Type*} [Fintype Point] [Fintype Block]
    [DecidableEq Point] (S : BlockSystem Point Block) (b : Block)
    (parameter : {p : Point // p ∈ S.support b} ↪ RealProjectiveOnePoint) :
    Finset RealProjectiveOnePoint := by
  classical
  exact (Finset.univ : Finset {p : Point // p ∈ S.support b}).map parameter

theorem lineBlockProjectiveTrace_card
    {Point Block : Type*} [Fintype Point] [Fintype Block]
    [DecidableEq Point] (S : BlockSystem Point Block) (b : Block)
    (parameter : {p : Point // p ∈ S.support b} ↪ RealProjectiveOnePoint) :
    (lineBlockProjectiveTrace S b parameter).card = (S.support b).card := by
  classical
  rw [lineBlockProjectiveTrace, Finset.card_map]
  exact Fintype.card_coe _

/-! ## A canonical projective carrier for an actual affine line -/

/-- Every concrete determined affine line has one projective parameter for
all of its labelled support.  The construction chooses a determining pair
`a,b`; a point on the line is sent to the homogeneous affine coordinate
`[t : 1]`, where `cfg p = cfg a + t (cfg b - cfg a)`.

This is deliberately a parameter of the *original* line, rather than a
separate choice after each pivot inversion. -/
private theorem exists_determinedLineProjectiveParameter
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    (cfg : Configuration Point) (L : DeterminedLine cfg) :
    ∃ parameter : {p : Point // p ∈ lineSupport cfg L} ↪ RealProjectiveOnePoint,
      True := by
  classical
  obtain ⟨A, hA⟩ := L.exists_pair
  obtain ⟨a, b, hab, hAcard⟩ := Finset.card_eq_two.mp A.2
  have hAeq : A = ⟨{a, b}, by simp [hab]⟩ := by
    apply Subtype.ext
    exact hAcard
  subst A
  have hL : L.1 = affineSpan ℝ ({cfg a, cfg b} : Set Point2) := by
    calc
      L.1 = lineOfPair cfg ⟨{a, b}, by simp [hab]⟩ := hA.symm
      _ = affineSpan ℝ ({cfg a, cfg b} : Set Point2) := by
        simpa using (lineOfPair_pair cfg hab)
  let coordinate : {p : Point // p ∈ lineSupport cfg L} → ℝ := fun p =>
    Classical.choose <| (mem_affineSpan_pair_iff_exists_lineMap_eq).mp (by
      rw [← hL]
      exact mem_lineSupport.mp p.2)
  have coordinate_spec (p : {p : Point // p ∈ lineSupport cfg L}) :
      affineParamPoint (cfg a) (cfg b - cfg a) (coordinate p) = cfg p.1 := by
    exact (affineParamPoint_eq_lineMap (cfg a) (cfg b) (coordinate p)).trans
      (Classical.choose_spec <|
        (mem_affineSpan_pair_iff_exists_lineMap_eq).mp (by
          rw [← hL]
          exact mem_lineSupport.mp p.2))
  let parameter : {p : Point // p ∈ lineSupport cfg L} → RealProjectiveOnePoint :=
    fun p => realProjectiveAffinePoint (coordinate p)
  have hparameter : Function.Injective parameter := by
    intro p q hpq
    have hbracket :
      realProjectiveBracket
          (realProjectiveAffineVector (coordinate p))
          (realProjectiveAffineVector (coordinate q)) = 0 := by
      exact (realProjective_mk_eq_mk_iff_bracket_eq_zero
        (realProjectiveAffineVector_ne_zero (coordinate p))
        (realProjectiveAffineVector_ne_zero (coordinate q))).mp hpq
    have hcoordinate : coordinate p = coordinate q := by
      exact sub_eq_zero.mp (by
        simpa [realProjectiveBracket, realProjectiveAffineVector] using hbracket)
    apply Subtype.ext
    apply cfg.injective
    calc
      cfg p.1 = affineParamPoint (cfg a) (cfg b - cfg a) (coordinate p) :=
        (coordinate_spec p).symm
      _ = affineParamPoint (cfg a) (cfg b - cfg a) (coordinate q) := by
        rw [hcoordinate]
      _ = cfg q.1 := coordinate_spec q
  exact ⟨⟨parameter, hparameter⟩, trivial⟩

/-- The shared projective parameter selected from the preceding existence
theorem.  Keeping the choice at this boundary prevents elimination from a
proposition into the embedding data itself. -/
noncomputable def determinedLineProjectiveParameter
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    (cfg : Configuration Point) (L : DeterminedLine cfg) :
    {p : Point // p ∈ lineSupport cfg L} ↪ RealProjectiveOnePoint :=
  Classical.choose (exists_determinedLineProjectiveParameter cfg L)

/-! ## The pivot dictionary for a five-line -/

/-- A size-five line through the pivot, viewed in the same pivot dictionary
as a five-circle. -/
def lineFivePivotBlock
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    (cfg : Configuration Point) (p : Point) (b : GeometricBlock cfg)
    (hb : b ∈ (blockSystem cfg).lineBlocksOfSize 5)
    (hp : p ∈ geometricBlockSupport cfg b) : PivotBlock cfg p :=
  ⟨b, hp, by
    have hsize := ((blockSystem cfg).mem_blocksOfKindSize.mp hb).2
    change (geometricBlockSupport cfg b).card = 5 at hsize
    omega⟩

/-- Deleting the pivot from a five-line produces one of the four saturated
base lines of the inverted four-star. -/
noncomputable def lineFivePivotLineOfSize
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    (cfg : Configuration Point) (p : Point) (b : GeometricBlock cfg)
    (hb : b ∈ (blockSystem cfg).lineBlocksOfSize 5)
    (hp : p ∈ geometricBlockSupport cfg b) :
    DeterminedLineOfSize (pivotInversion cfg p) 4 :=
  ⟨blockToPivotLine cfg p (lineFivePivotBlock cfg p b hb hp), by
    rw [card_lineSupport_blockToPivotLine]
    have hsize := ((blockSystem cfg).mem_blocksOfKindSize.mp hb).2
    change (geometricBlockSupport cfg b).card = 5 at hsize
    change (geometricBlockSupport cfg b).card - 1 = 4
    omega⟩

/-- The canonical base index occupied by a concrete five-line through a
neutral pivot. -/
noncomputable def elevenFive944LineBaseIndex
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    (cfg : Configuration Point) (hcard : Fintype.card Point = 11)
    (p : Point) (hpivot : p ∈ elevenFive944Pivots (blockSystem cfg))
    (b : GeometricBlock cfg)
    (hb : b ∈ (blockSystem cfg).lineBlocksOfSize 5)
    (hp : p ∈ geometricBlockSupport cfg b) : Fin 4 :=
  ((elevenFive944PivotFourStar cfg hcard p hpivot).sizeFourLineEquiv).symm
    (lineFivePivotLineOfSize cfg p b hb hp)

theorem elevenFive944LineBaseIndex_line
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    (cfg : Configuration Point) (hcard : Fintype.card Point = 11)
    (p : Point) (hpivot : p ∈ elevenFive944Pivots (blockSystem cfg))
    (b : GeometricBlock cfg)
    (hb : b ∈ (blockSystem cfg).lineBlocksOfSize 5)
    (hp : p ∈ geometricBlockSupport cfg b) :
    (elevenFive944PivotFourStar cfg hcard p hpivot).sizeFourLine
        (elevenFive944LineBaseIndex cfg hcard p hpivot b hb hp) =
      blockToPivotLine cfg p (lineFivePivotBlock cfg p b hb hp) := by
  unfold elevenFive944LineBaseIndex
    ElevenFivePivotInvertedFourStar.sizeFourLine
  exact congrArg Subtype.val (Equiv.apply_symm_apply _ _)

theorem elevenFive944LineBaseIndex_support
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    (cfg : Configuration Point) (hcard : Fintype.card Point = 11)
    (p : Point) (hpivot : p ∈ elevenFive944Pivots (blockSystem cfg))
    (b : GeometricBlock cfg)
    (hb : b ∈ (blockSystem cfg).lineBlocksOfSize 5)
    (hp : p ∈ geometricBlockSupport cfg b) :
    (elevenFive944PivotFourStar cfg hcard p hpivot).baseSupport
        (elevenFive944LineBaseIndex cfg hcard p hpivot b hb hp) =
      awaySupport p (geometricBlockSupport cfg b) := by
  unfold ElevenFivePivotInvertedFourStar.baseSupport
  rw [elevenFive944LineBaseIndex_line]
  exact lineSupport_blockToPivotLine cfg p
    (lineFivePivotBlock cfg p b hb hp)

/-- A genuine five-line compatibility certificate.  One parameter embeds the
whole line trace into `RP¹`; after deletion of any selected pivot, the four
parameters are identified with a normal four-star trace by a projectivity.
This is geometric data, not a restatement of the incidence cap. -/
def HasFiveLineNormalTraceTransport
    {Point Block : Type*} [Fintype Point] [Fintype Block]
    [DecidableEq Point] (S : BlockSystem Point Block) (H : Finset Point)
    (b : Block) : Prop :=
  ∃ parameter : {p : Point // p ∈ S.support b} ↪ RealProjectiveOnePoint,
    ∀ p : Point, p ∈ H →
      (hp : p ∈ S.support b) →
      ∃ (i : Fin 4) (g : GL (Fin 2) ℝ),
        (lineBlockProjectiveTrace S b parameter).erase (parameter ⟨p, hp⟩) =
          (fourStarNormalTraceParameterSet i).image (fun P => g⁻¹ • P)

/-- The compatibility theorem in the exact form supplied by the pivot
dictionary.  The normal trace index is not arbitrary: it is the base line
obtained from this specific five-line after inversion about this pivot. -/
def ElevenFive944FiveLineNormalTraceTransport
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    (cfg : Configuration Point) (hcard : Fintype.card Point = 11)
    (b : GeometricBlock cfg)
    (hb : b ∈ (blockSystem cfg).lineBlocksOfSize 5) : Prop :=
  ∃ parameter : {p : Point // p ∈ geometricBlockSupport cfg b} ↪
      RealProjectiveOnePoint,
    ∀ p : Point, (hpivot : p ∈ elevenFive944Pivots (blockSystem cfg)) →
      (hp : p ∈ geometricBlockSupport cfg b) →
      ∃ g : GL (Fin 2) ℝ,
        (lineBlockProjectiveTrace (blockSystem cfg) b parameter).erase
            (parameter ⟨p, hp⟩) =
          (fourStarNormalTraceParameterSet
            (elevenFive944LineBaseIndex cfg hcard p hpivot b hb hp)).image
              (fun P => g⁻¹ • P)

/-- Forgetting the prescribed base index recovers the generic finite bridge. -/
theorem elevenFive944FiveLineNormalTraceTransport.toHasFiveLineNormalTraceTransport
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    (cfg : Configuration Point) (hcard : Fintype.card Point = 11)
    (b : GeometricBlock cfg)
    (hb : b ∈ (blockSystem cfg).lineBlocksOfSize 5)
    (htransport : ElevenFive944FiveLineNormalTraceTransport cfg hcard b hb) :
    HasFiveLineNormalTraceTransport (blockSystem cfg)
      (elevenFive944Pivots (blockSystem cfg)) b := by
  obtain ⟨parameter, hparameter⟩ := htransport
  refine ⟨parameter, ?_⟩
  intro p hpivot hp
  obtain ⟨g, htrace⟩ := hparameter p hpivot hp
  exact ⟨elevenFive944LineBaseIndex cfg hcard p hpivot b hb hp, g, htrace⟩

/-- The normal-trace certificate supplies the order-free harmonic deletion
needed by the five-point projective cap. -/
theorem isRealProjectiveHarmonicFour_lineBlockTrace_erase_of_normalTransport
    {Point Block : Type*} [Fintype Point] [Fintype Block]
    [DecidableEq Point] {S : BlockSystem Point Block} {H : Finset Point}
    {b : Block}
    (htransport : HasFiveLineNormalTraceTransport S H b)
    (p : Point) (hpH : p ∈ H) (hp : p ∈ S.support b) :
    IsRealProjectiveHarmonicFour
      ((lineBlockProjectiveTrace S b htransport.choose).erase
        (htransport.choose ⟨p, hp⟩)) := by
  obtain ⟨i, g, htrace⟩ := htransport.choose_spec p hpH hp
  exact isRealProjectiveHarmonicFour_of_eq_image_inv_fourStarNormalTrace
    g _ i htrace

/-- A five-point projective trace with harmonic deletions at the selected
pivots has at most two selected pivots.  This is the finite bridge used for
the line layer. -/
theorem inter_card_le_two_of_fiveLineNormalTraceTransport
    {Point Block : Type*} [Fintype Point] [Fintype Block]
    [DecidableEq Point] (S : BlockSystem Point Block) (H : Finset Point)
    (b : Block) (hfive : (S.support b).card = 5)
    (htransport : HasFiveLineNormalTraceTransport S H b) :
    (H ∩ S.support b).card ≤ 2 := by
  classical
  let parameter := htransport.choose
  let P := lineBlockProjectiveTrace S b parameter
  let X := {p : Point // p ∈ H ∩ S.support b}
  let Y := {q : RealProjectiveOnePoint //
    q ∈ realProjectiveHarmonicComplementPoints P}
  let f : X → Y := fun p => by
    let pp : {q : Point // q ∈ S.support b} :=
      ⟨p.1, (Finset.mem_inter.mp p.2).2⟩
    refine ⟨parameter pp, ?_⟩
    simp only [realProjectiveHarmonicComplementPoints, Finset.mem_filter]
    refine ⟨?_, ?_⟩
    · exact Finset.mem_map_of_mem parameter (Finset.mem_univ pp)
    · simpa [parameter, pp] using
        isRealProjectiveHarmonicFour_lineBlockTrace_erase_of_normalTransport
          htransport p.1 (Finset.mem_inter.mp p.2).1 pp.2
  have hf : Function.Injective f := by
    intro p q hpq
    have hparameter := congrArg Subtype.val hpq
    change parameter ⟨p.1, (Finset.mem_inter.mp p.2).2⟩ =
      parameter ⟨q.1, (Finset.mem_inter.mp q.2).2⟩ at hparameter
    have hsubtype := parameter.injective hparameter
    exact Subtype.ext (congrArg
      (fun z : {q : Point // q ∈ S.support b} => z.1) hsubtype)
  have hinjectiveCard := Fintype.card_le_of_injective f hf
  have hPcard : P.card = 5 := by
    simpa only [P, lineBlockProjectiveTrace_card] using hfive
  have hcap := realProjectiveHarmonicComplementPoints_card_le_two P hPcard
  calc
    (H ∩ S.support b).card = Fintype.card X :=
      (Fintype.card_coe _).symm
    _ ≤ Fintype.card Y := hinjectiveCard
    _ = (realProjectiveHarmonicComplementPoints P).card :=
      Fintype.card_coe _
    _ ≤ 2 := hcap

/-- The desired five-line cap follows from the precise normal-trace
compatibility, with no assumption phrased as a cardinality bound. -/
theorem elevenFive944Pivots_on_fiveLine_card_le_two_of_normalTraceTransport
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    (cfg : Configuration Point) (b : GeometricBlock cfg)
    (hb : b ∈ (blockSystem cfg).lineBlocksOfSize 5)
    (htransport : HasFiveLineNormalTraceTransport (blockSystem cfg)
      (elevenFive944Pivots (blockSystem cfg)) b) :
    (elevenFive944Pivots (blockSystem cfg) ∩
      geometricBlockSupport cfg b).card ≤ 2 := by
  apply inter_card_le_two_of_fiveLineNormalTraceTransport
    (blockSystem cfg) (elevenFive944Pivots (blockSystem cfg)) b
  · exact ((blockSystem cfg).mem_blocksOfKindSize.mp hb).2
  · exact htransport

/-- The same cap in the pivot-dictionary form: each normal four-star trace is
attached to the actual base index determined by the original five-line. -/
theorem elevenFive944Pivots_on_fiveLine_card_le_two_of_exactNormalTraceTransport
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    (cfg : Configuration Point) (hcard : Fintype.card Point = 11)
    (b : GeometricBlock cfg)
    (hb : b ∈ (blockSystem cfg).lineBlocksOfSize 5)
    (htransport : ElevenFive944FiveLineNormalTraceTransport cfg hcard b hb) :
    (elevenFive944Pivots (blockSystem cfg) ∩
      geometricBlockSupport cfg b).card ≤ 2 := by
  exact elevenFive944Pivots_on_fiveLine_card_le_two_of_normalTraceTransport
    cfg b hb (by
      rcases htransport with ⟨parameter, hparameter⟩
      refine ⟨parameter, ?_⟩
      intro p hpivot hp
      obtain ⟨g, htrace⟩ := hparameter p hpivot hp
      exact ⟨elevenFive944LineBaseIndex cfg hcard p hpivot b hb hp, g, htrace⟩)

/-- Uniform normal-trace compatibility over the five-line layer yields the
whole line-layer cap required by the untagged five-block double count. -/
theorem elevenFive944Pivots_fiveLine_cap_of_normalTraceTransport
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    (cfg : Configuration Point)
    (htransport : ∀ b ∈ (blockSystem cfg).lineBlocksOfSize 5,
      HasFiveLineNormalTraceTransport (blockSystem cfg)
        (elevenFive944Pivots (blockSystem cfg)) b) :
    ∀ b ∈ (blockSystem cfg).lineBlocksOfSize 5,
      (elevenFive944Pivots (blockSystem cfg) ∩
        (blockSystem cfg).support b).card ≤ 2 := by
  intro b hb
  exact elevenFive944Pivots_on_fiveLine_card_le_two_of_normalTraceTransport
    cfg b hb (htransport b hb)

/-- Uniform exact compatibility closes the entire five-line layer. -/
theorem elevenFive944Pivots_fiveLine_cap_of_exactNormalTraceTransport
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    (cfg : Configuration Point) (hcard : Fintype.card Point = 11)
    (htransport : ∀ (b : GeometricBlock cfg),
      ∀ hb : b ∈ (blockSystem cfg).lineBlocksOfSize 5,
        ElevenFive944FiveLineNormalTraceTransport cfg hcard b hb) :
    ∀ b ∈ (blockSystem cfg).lineBlocksOfSize 5,
      (elevenFive944Pivots (blockSystem cfg) ∩
        (blockSystem cfg).support b).card ≤ 2 := by
  intro b hb
  exact elevenFive944Pivots_on_fiveLine_card_le_two_of_exactNormalTraceTransport
    cfg hcard b hb (htransport b hb)

end Erdos506.V1
