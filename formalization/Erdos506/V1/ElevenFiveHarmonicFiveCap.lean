import Erdos506.Block.FiveBlockWeightedIncidence
import Erdos506.Incidence.InversionHarmonicTransport
import Erdos506.Incidence.RealProjectiveHarmonicFiveCap
import Erdos506.V1.ElevenFiveFourStarHarmonic

/-!
# The eleven-point harmonic five-circle incidence cap

This module contains the acyclic part of the weighted five-block argument.
It defines the `(d₃,d₄,d₅) = (9,4,4)` pivot set independently of
`ElevenFive`, embeds every finite proper-circle trace into `RP¹`, transports
the five-point harmonic-deletion cap back to a circle trace, and invokes the
neutral weighted incidence theorem.

The remaining geometric seam is deliberately not encoded as an assumption:
one must prove that the canonical four-star line attached to a `(9,4,4)`
pivot on a five-circle is harmonic for the *specific* proper-circle
parameter below.  The current `IsParametricallyHarmonicFour` endpoint permits
an arbitrary parameter function, so it cannot supply that statement without
an additional compatibility theorem.
-/

namespace Erdos506.V1

open Erdos506.Block
open Erdos506.Block.BlockSystem
open Erdos506.Incidence
open Erdos506.V3
open Erdos506.V4

universe u

/-! ## The neutral `(9,4,4)` pivot family -/

/-- Pivots with block degrees `(d₃,d₄,d₅) = (9,4,4)`.  This is kept
independent of `ElevenFive.lean` so that the completed geometric adapter may
be imported there without an import cycle. -/
noncomputable def elevenFive944Pivots
    {Point Block : Type*} [Fintype Point] [Fintype Block]
    [DecidableEq Point] (S : BlockSystem Point Block) : Finset Point :=
  Finset.univ.filter fun p =>
    S.blockDegree 3 p = 9 ∧ S.blockDegree 4 p = 4 ∧
      S.blockDegree 5 p = 4

@[simp] theorem mem_elevenFive944Pivots
    {Point Block : Type*} [Fintype Point] [Fintype Block]
    [DecidableEq Point] (S : BlockSystem Point Block) (p : Point) :
    p ∈ elevenFive944Pivots S ↔
      S.blockDegree 3 p = 9 ∧ S.blockDegree 4 p = 4 ∧
        S.blockDegree 5 p = 4 := by
  classical
  simp [elevenFive944Pivots]

theorem blockDegree_five_eq_four_of_mem_elevenFive944Pivots
    {Point Block : Type*} [Fintype Point] [Fintype Block]
    [DecidableEq Point] {S : BlockSystem Point Block} {p : Point}
    (hp : p ∈ elevenFive944Pivots S) :
    S.blockDegree 5 p = 4 :=
  (mem_elevenFive944Pivots S p).mp hp |>.2.2

private theorem blockDegree_eq_lineDegree_add_circleDegree
    {Point Block : Type*} [Fintype Point] [Fintype Block]
    [DecidableEq Point] (S : BlockSystem Point Block) (s : Nat) (p : Point) :
    S.blockDegree s p = S.lineDegree s p + S.circleDegree s p := by
  classical
  let F := (S.blocksOfSize s).filter fun b => p ∈ S.support b
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := F) (fun b => S.kind b = .line)
  have hline :
      F.filter (fun b => S.kind b = .line) =
        (S.lineBlocksOfSize s).filter fun b => p ∈ S.support b := by
    ext b
    simp [F, BlockSystem.blocksOfSize, BlockSystem.blocksOfKindSize,
      BlockSystem.blocksOfKind, and_comm, and_assoc]
  have hcircle :
      F.filter (fun b => ¬ S.kind b = .line) =
        (S.circleBlocksOfSize s).filter fun b => p ∈ S.support b := by
    ext b
    cases hkind : S.kind b <;>
      simp [F, BlockSystem.blocksOfSize, BlockSystem.blocksOfKindSize,
        BlockSystem.blocksOfKind, hkind, and_comm]
  rw [hline, hcircle] at hsplit
  exact hsplit.symm

/-! ## The canonical inverted four-star at one neutral pivot -/

/-- Membership in the neutral pivot family supplies the complete input of
the finite inverted four-star construction. -/
noncomputable def elevenFive944PivotFourStar
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    (cfg : Configuration Point) (hcard : Fintype.card Point = 11)
    (p : Point) (hp : p ∈ elevenFive944Pivots (blockSystem cfg)) :
    ElevenFivePivotInvertedFourStar cfg p where
  pivot_count_three := (mem_elevenFive944Pivots _ _).mp hp |>.1
  pivot_count_four := (mem_elevenFive944Pivots _ _).mp hp |>.2.1
  pivot_count_five := (mem_elevenFive944Pivots _ _).mp hp |>.2.2
  inverted_card := by
    rw [card_awayFrom, hcard]

/-- A size-five circle block through `p`, viewed as a pivot block. -/
def circleFivePivotBlock
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    (cfg : Configuration Point) (p : Point) (b : GeometricBlock cfg)
    (hb : b ∈ (blockSystem cfg).circleBlocksOfSize 5)
    (hp : p ∈ geometricBlockSupport cfg b) : PivotBlock cfg p :=
  ⟨b, hp, by
    have hsize := ((blockSystem cfg).mem_blocksOfKindSize.mp hb).2
    change (geometricBlockSupport cfg b).card = 5 at hsize
    omega⟩

/-- The four-point inverted line carried by a size-five block through the
pivot. -/
noncomputable def circleFivePivotLineOfSize
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    (cfg : Configuration Point) (p : Point) (b : GeometricBlock cfg)
    (hb : b ∈ (blockSystem cfg).circleBlocksOfSize 5)
    (hp : p ∈ geometricBlockSupport cfg b) :
    DeterminedLineOfSize (pivotInversion cfg p) 4 :=
  ⟨blockToPivotLine cfg p (circleFivePivotBlock cfg p b hb hp), by
    rw [card_lineSupport_blockToPivotLine]
    have hsize := ((blockSystem cfg).mem_blocksOfKindSize.mp hb).2
    change (geometricBlockSupport cfg b).card = 5 at hsize
    change (geometricBlockSupport cfg b).card - 1 = 4
    omega⟩

/-- The canonical base-line index occupied by a given five-circle through
a `(9,4,4)` pivot. -/
noncomputable def elevenFive944CircleBaseIndex
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    (cfg : Configuration Point) (hcard : Fintype.card Point = 11)
    (p : Point) (hpivot : p ∈ elevenFive944Pivots (blockSystem cfg))
    (b : GeometricBlock cfg)
    (hb : b ∈ (blockSystem cfg).circleBlocksOfSize 5)
    (hp : p ∈ geometricBlockSupport cfg b) : Fin 4 :=
  ((elevenFive944PivotFourStar cfg hcard p hpivot).sizeFourLineEquiv).symm
    (circleFivePivotLineOfSize cfg p b hb hp)

/-- At the chosen index, the canonical base line is the pivot-dictionary
line of the original five-circle block. -/
theorem elevenFive944CircleBaseIndex_line
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    (cfg : Configuration Point) (hcard : Fintype.card Point = 11)
    (p : Point) (hpivot : p ∈ elevenFive944Pivots (blockSystem cfg))
    (b : GeometricBlock cfg)
    (hb : b ∈ (blockSystem cfg).circleBlocksOfSize 5)
    (hp : p ∈ geometricBlockSupport cfg b) :
    (elevenFive944PivotFourStar cfg hcard p hpivot).sizeFourLine
        (elevenFive944CircleBaseIndex cfg hcard p hpivot b hb hp) =
      blockToPivotLine cfg p (circleFivePivotBlock cfg p b hb hp) := by
  unfold elevenFive944CircleBaseIndex
    ElevenFivePivotInvertedFourStar.sizeFourLine
  exact congrArg Subtype.val (Equiv.apply_symm_apply _ _)

/-- The selected base support at the preceding index is literally the
five-circle support with the pivot deleted. -/
theorem elevenFive944CircleBaseIndex_support
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    (cfg : Configuration Point) (hcard : Fintype.card Point = 11)
    (p : Point) (hpivot : p ∈ elevenFive944Pivots (blockSystem cfg))
    (b : GeometricBlock cfg)
    (hb : b ∈ (blockSystem cfg).circleBlocksOfSize 5)
    (hp : p ∈ geometricBlockSupport cfg b) :
    (elevenFive944PivotFourStar cfg hcard p hpivot).baseSupport
        (elevenFive944CircleBaseIndex cfg hcard p hpivot b hb hp) =
      awaySupport p (geometricBlockSupport cfg b) := by
  unfold ElevenFivePivotInvertedFourStar.baseSupport
  rw [elevenFive944CircleBaseIndex_line]
  exact lineSupport_blockToPivotLine cfg p
    (circleFivePivotBlock cfg p b hb hp)

/-! ## A finite proper-circle trace inside `RP¹` -/

/-- A selected point on `c` regarded as an actual point of the proper
circle. -/
def properCircleTracePoint
    {Point : Type*} [Fintype Point] [DecidableEq Point]
    (cfg : Configuration Point) (c : ProperCircle)
    (p : {p : Point // p ∈ circleTrace cfg c}) : ProperCirclePoint c :=
  ⟨cfg p.1, mem_circleTrace.mp p.2⟩

theorem properCircleTracePoint_injective
    {Point : Type*} [Fintype Point] [DecidableEq Point]
    (cfg : Configuration Point) (c : ProperCircle) :
    Function.Injective (properCircleTracePoint cfg c) := by
  intro p q hpq
  apply Subtype.ext
  apply cfg.injective
  exact congrArg Subtype.val hpq

/-- The canonical projective parameter of a selected point of `c`. -/
noncomputable def properCircleTraceParameter
    {Point : Type*} [Fintype Point] [DecidableEq Point]
    (cfg : Configuration Point) (c : ProperCircle)
    (p : {p : Point // p ∈ circleTrace cfg c}) : RealProjectiveOnePoint :=
  properCirclePointParameter c (properCircleTracePoint cfg c p)

theorem properCircleTraceParameter_injective
    {Point : Type*} [Fintype Point] [DecidableEq Point]
    (cfg : Configuration Point) (c : ProperCircle) :
    Function.Injective (properCircleTraceParameter cfg c) := by
  intro p q hpq
  apply properCircleTracePoint_injective cfg c
  unfold properCircleTraceParameter at hpq
  rw [properCirclePointParameter_eq_equiv_symm,
    properCirclePointParameter_eq_equiv_symm] at hpq
  exact (properCircleProjectiveEquiv c).symm.injective hpq

/-- The embedding of the selected trace into the projective parameter
line. -/
noncomputable def properCircleTraceParameterEmbedding
    {Point : Type*} [Fintype Point] [DecidableEq Point]
    (cfg : Configuration Point) (c : ProperCircle) :
    {p : Point // p ∈ circleTrace cfg c} ↪ RealProjectiveOnePoint :=
  ⟨properCircleTraceParameter cfg c,
    properCircleTraceParameter_injective cfg c⟩

/-- The five-point projective set associated with a finite circle trace. -/
noncomputable def properCircleTraceParameterSet
    {Point : Type*} [Fintype Point] [DecidableEq Point]
    (cfg : Configuration Point) (c : ProperCircle) :
    Finset RealProjectiveOnePoint := by
  classical
  exact (Finset.univ : Finset {p : Point // p ∈ circleTrace cfg c}).map
    (properCircleTraceParameterEmbedding cfg c)

theorem properCircleTraceParameterSet_card
    {Point : Type*} [Fintype Point] [DecidableEq Point]
    (cfg : Configuration Point) (c : ProperCircle) :
    (properCircleTraceParameterSet cfg c).card =
      (circleTrace cfg c).card := by
  classical
  rw [properCircleTraceParameterSet, Finset.card_map]
  exact Fintype.card_coe _

@[simp] theorem properCircleTraceParameter_mem_parameterSet
    {Point : Type*} [Fintype Point] [DecidableEq Point]
    (cfg : Configuration Point) (c : ProperCircle)
    (p : {p : Point // p ∈ circleTrace cfg c}) :
    properCircleTraceParameter cfg c p ∈
      properCircleTraceParameterSet cfg c := by
  classical
  exact Finset.mem_map_of_mem (properCircleTraceParameterEmbedding cfg c)
    (Finset.mem_univ p)

/-- Delete one selected circle point from its canonical projective trace.
The definition packages the classical equality decision on `RP¹`, so users
do not need to expose it in geometric theorem signatures. -/
noncomputable def properCircleTraceParameterSetErase
    {Point : Type*} [Fintype Point] [DecidableEq Point]
    (cfg : Configuration Point) (c : ProperCircle)
    (p : {p : Point // p ∈ circleTrace cfg c}) :
    Finset RealProjectiveOnePoint := by
  classical
  exact (properCircleTraceParameterSet cfg c).erase
    (properCircleTraceParameter cfg c p)

/-- The concrete geometric endpoint required of the four-star at a
`(9,4,4)` pivot.  Unlike `HasHarmonicBaseSupports`, this predicate fixes the
parameter to the canonical projective parametrisation of each actual
proper circle and fixes the deleted point to the original pivot. -/
def ElevenFivePivotInvertedFourStar.HasProperCircleHarmonicDeletion
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (H : ElevenFivePivotInvertedFourStar cfg p) : Prop :=
  let _pivotCountThree := H.pivot_count_three
  ∀ c : DeterminedCircle cfg,
    (circleTrace cfg c.1).card = 5 →
    (hp : p ∈ circleTrace cfg c.1) →
    IsRealProjectiveHarmonicFour
      (properCircleTraceParameterSetErase cfg c.1 ⟨p, hp⟩)

/-! ## Pulling the five-point cap back to a circle trace -/

/-- If every point of `H` lying on a five-point proper circle is a harmonic
deletion in the canonical projective parameter set, at most two points of
`H` lie on that circle. -/
theorem properCircleTrace_inter_card_le_two_of_harmonic_deletions
    {Point : Type*} [Fintype Point] [DecidableEq Point]
    (cfg : Configuration Point) (c : ProperCircle) (H : Finset Point)
    (hfive : (circleTrace cfg c).card = 5)
    (hharmonic : ∀ p : Point, p ∈ H →
      (hp : p ∈ circleTrace cfg c) →
      IsRealProjectiveHarmonicFour
        (properCircleTraceParameterSetErase cfg c ⟨p, hp⟩)) :
    (H ∩ circleTrace cfg c).card ≤ 2 := by
  classical
  let P := properCircleTraceParameterSet cfg c
  let X := {p : Point // p ∈ H ∩ circleTrace cfg c}
  let Y := {q : RealProjectiveOnePoint //
    q ∈ realProjectiveHarmonicComplementPoints P}
  let f : X → Y := fun p => by
    let pc : {x : Point // x ∈ circleTrace cfg c} :=
      ⟨p.1, (Finset.mem_inter.mp p.2).2⟩
    refine ⟨properCircleTraceParameter cfg c pc, ?_⟩
    simp only [realProjectiveHarmonicComplementPoints, Finset.mem_filter]
    refine ⟨?_, ?_⟩
    · exact properCircleTraceParameter_mem_parameterSet cfg c pc
    · exact hharmonic p.1 (Finset.mem_inter.mp p.2).1 pc.2
  have hf : Function.Injective f := by
    intro p q hpq
    apply Subtype.ext
    have hparam := congrArg Subtype.val hpq
    change properCircleTraceParameter cfg c
        ⟨p.1, (Finset.mem_inter.mp p.2).2⟩ =
      properCircleTraceParameter cfg c
        ⟨q.1, (Finset.mem_inter.mp q.2).2⟩ at hparam
    have hpoint := properCircleTraceParameter_injective cfg c hparam
    exact congrArg
      (fun r : {x : Point // x ∈ circleTrace cfg c} => r.1) hpoint
  have hcard := Fintype.card_le_of_injective f hf
  have hPcard : P.card = 5 := by
    simpa only [P, properCircleTraceParameterSet_card] using hfive
  have hcap := realProjectiveHarmonicComplementPoints_card_le_two P hPcard
  calc
    (H ∩ circleTrace cfg c).card = Fintype.card X :=
      (Fintype.card_coe _).symm
    _ ≤ Fintype.card Y := hcard
    _ = (realProjectiveHarmonicComplementPoints P).card :=
      Fintype.card_coe _
    _ ≤ 2 := hcap

/-! ## Circle-tagged geometric blocks -/

/-- The determined proper circle represented by a circle-tagged geometric
block. -/
noncomputable def properCircleOfCircleBlock
    {Point : Type*} [Fintype Point] [DecidableEq Point]
    (cfg : Configuration Point) (b : GeometricBlock cfg)
    (hb : geometricBlockKind b = .circle) : ProperCircle :=
  ((circleBlockEquiv cfg) ⟨b, hb⟩).1

theorem circleTrace_properCircleOfCircleBlock
    {Point : Type*} [Fintype Point] [DecidableEq Point]
    (cfg : Configuration Point) (b : GeometricBlock cfg)
    (hb : geometricBlockKind b = .circle) :
    circleTrace cfg (properCircleOfCircleBlock cfg b hb) =
      geometricBlockSupport cfg b := by
  rcases b with L | c
  · cases hb
  · rfl

private theorem blockToPivotLine_eq_circlePivotLine_of_block_eq
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    (cfg : Configuration Point) (p : Point) (c : DeterminedCircle cfg)
    (b : PivotBlock cfg p) (hb : b.1 = Sum.inr c) :
    (blockToPivotLine cfg p b).1 = circlePivotLine cfg p c.1 := by
  rcases b with ⟨b, hp, hcard⟩
  cases b with
  | inl L => cases hb
  | inr d =>
      have hdc : d = c := Sum.inr.inj hb
      subst d
      rfl

/-- Since the tagged block is a circle, its pivot-dictionary line is the
explicit perpendicular-bisector line used by inversion geometry. -/
theorem circleFivePivotLine_eq_circlePivotLine
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    (cfg : Configuration Point) (p : Point) (b : GeometricBlock cfg)
    (hb : b ∈ (blockSystem cfg).circleBlocksOfSize 5)
    (hp : p ∈ geometricBlockSupport cfg b) :
    (circleFivePivotLineOfSize cfg p b hb hp).1.1 =
      circlePivotLine cfg p
        (properCircleOfCircleBlock cfg b
          ((blockSystem cfg).mem_blocksOfKindSize.mp hb).1) := by
  rcases b with L | c
  · exact False.elim (by
      have hkind := ((blockSystem cfg).mem_blocksOfKindSize.mp hb).1
      cases hkind)
  · change
      (blockToPivotLine cfg p
        (circleFivePivotBlock cfg p (Sum.inr c) hb hp)).1 =
          circlePivotLine cfg p c.1
    exact blockToPivotLine_eq_circlePivotLine_of_block_eq cfg p c
      (circleFivePivotBlock cfg p (Sum.inr c) hb hp) rfl

/-- The fully proved trace-to-`RP¹` adapter for a circle block.  Its sole
semantic premise is exactly the still-missing geometric four-star theorem. -/
private theorem elevenFive944Pivots_on_circle_card_le_two_of_harmonic_deletions
    {Point : Type*} [Fintype Point] [DecidableEq Point]
    (cfg : Configuration Point) (b : GeometricBlock cfg)
    (hb : b ∈ (blockSystem cfg).circleBlocksOfSize 5)
    (hharmonic : ∀ p : Point, p ∈ elevenFive944Pivots (blockSystem cfg) →
      (hp : p ∈ geometricBlockSupport cfg b) →
      IsRealProjectiveHarmonicFour
        (properCircleTraceParameterSetErase cfg
            (properCircleOfCircleBlock cfg b
              ((blockSystem cfg).mem_blocksOfKindSize.mp hb).1)
            ⟨p, by
              rw [circleTrace_properCircleOfCircleBlock]
              exact hp⟩)) :
    (elevenFive944Pivots (blockSystem cfg) ∩
      geometricBlockSupport cfg b).card ≤ 2 := by
  let hkind := ((blockSystem cfg).mem_blocksOfKindSize.mp hb).1
  let c := properCircleOfCircleBlock cfg b hkind
  have htrace : circleTrace cfg c = geometricBlockSupport cfg b :=
    circleTrace_properCircleOfCircleBlock cfg b hkind
  have hfive : (circleTrace cfg c).card = 5 := by
    rw [htrace]
    exact ((blockSystem cfg).mem_blocksOfKindSize.mp hb).2
  rw [← htrace]
  apply properCircleTrace_inter_card_le_two_of_harmonic_deletions
    cfg c (elevenFive944Pivots (blockSystem cfg)) hfive
  intro p hpH hpTrace
  apply hharmonic p hpH
  rw [← htrace]
  exact hpTrace

/-- A concrete proper-circle harmonic-deletion theorem at every neutral
pivot implies the per-five-circle incidence cap.  The premise is a theorem
target, not a new global geometric principle. -/
theorem elevenFive_harmonicPivots_on_circle_card_le_two_of_properCircleHarmonicDeletion
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    (cfg : Configuration Point) (hcard : Fintype.card Point = 11)
    (hproper : ∀ p : Point,
      (hp : p ∈ elevenFive944Pivots (blockSystem cfg)) →
      ElevenFivePivotInvertedFourStar.HasProperCircleHarmonicDeletion
        (elevenFive944PivotFourStar cfg hcard p hp))
    (b : GeometricBlock cfg)
    (hb : b ∈ (blockSystem cfg).circleBlocksOfSize 5) :
    (elevenFive944Pivots (blockSystem cfg) ∩
      geometricBlockSupport cfg b).card ≤ 2 := by
  let hkind := ((blockSystem cfg).mem_blocksOfKindSize.mp hb).1
  let c : DeterminedCircle cfg := (circleBlockEquiv cfg) ⟨b, hkind⟩
  apply elevenFive944Pivots_on_circle_card_le_two_of_harmonic_deletions
    cfg b hb
  intro p hpivot hpSupport
  have htrace : circleTrace cfg c.1 = geometricBlockSupport cfg b := by
    simpa [c, properCircleOfCircleBlock] using
      circleTrace_properCircleOfCircleBlock cfg b hkind
  apply hproper p hpivot c
  rw [htrace]
  exact ((blockSystem cfg).mem_blocksOfKindSize.mp hb).2

/-! ## Weighted incidence -/

/-- Once the per-circle geometric seam is available, the correct weighted
global inequality follows from the neutral double count. -/
private theorem elevenFive_weighted_harmonicIncidenceCap_of_circle_cap
    {Point : Type*} [Fintype Point] [DecidableEq Point]
    (cfg : Configuration Point)
    (hcircle : ∀ b ∈ (blockSystem cfg).circleBlocksOfSize 5,
      (elevenFive944Pivots (blockSystem cfg) ∩
        geometricBlockSupport cfg b).card ≤ 2) :
    4 * (elevenFive944Pivots (blockSystem cfg)).card ≤
      5 * (blockSystem cfg).lineCount 5 +
        2 * (blockSystem cfg).circleCount 5 := by
  apply four_mul_card_le_five_mul_lineCount_add_two_mul_circleCount
    (blockSystem cfg) (elevenFive944Pivots (blockSystem cfg))
  · intro p hp
    have hd5 := blockDegree_five_eq_four_of_mem_elevenFive944Pivots hp
    have hsplit := blockDegree_eq_lineDegree_add_circleDegree
      (blockSystem cfg) 5 p
    omega
  · exact hcircle

/-- The weighted harmonic incidence cap, reduced exactly to the concrete
proper-circle harmonic-deletion endpoint at every neutral pivot. -/
theorem elevenFive_weighted_harmonicIncidenceCap_of_properCircleHarmonicDeletion
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    (cfg : Configuration Point) (hcard : Fintype.card Point = 11)
    (hproper : ∀ p : Point,
      (hp : p ∈ elevenFive944Pivots (blockSystem cfg)) →
      ElevenFivePivotInvertedFourStar.HasProperCircleHarmonicDeletion
        (elevenFive944PivotFourStar cfg hcard p hp)) :
    4 * (elevenFive944Pivots (blockSystem cfg)).card ≤
      5 * (blockSystem cfg).lineCount 5 +
        2 * (blockSystem cfg).circleCount 5 := by
  apply elevenFive_weighted_harmonicIncidenceCap_of_circle_cap cfg
  intro b hb
  exact elevenFive_harmonicPivots_on_circle_card_le_two_of_properCircleHarmonicDeletion
    cfg hcard hproper b hb

/-!
## Exact remaining theorem

To remove `RealPlaneElevenFiveGeometry.harmonicIncidenceCap`, it remains to
prove, without adding a new principle, the following concrete theorem:

```
theorem elevenFive944_properCircleHarmonicDeletion
    (cfg : Configuration Point) (hcard : Fintype.card Point = 11)
    (p : Point) (hp : p ∈ elevenFive944Pivots (blockSystem cfg)) :
    (elevenFive944PivotFourStar cfg hcard p hp).
      HasProperCircleHarmonicDeletion
```

The pivot dictionary and finite four-star trichotomy are already available.
The missing input is the incidence-compatible projective realization and the
triangle-pendant determinant-to-circle-parameter identification.  The
current `HasHarmonicBaseSupports` cannot be used for this purpose because
its `FourPointLineHarmonicParameter.parameter` is unconstrained by the
actual inverted affine line or by `properCircleTraceParameter`.
-/

end Erdos506.V1
