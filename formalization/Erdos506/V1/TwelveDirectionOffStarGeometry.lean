import Erdos506.Incidence.DeterminedLineArrangementCensus
import Erdos506.Incidence.RealProjectiveLineCellulation
import Erdos506.V1.DeletionLineCensus
import Erdos506.V1.TwelveDirectionDefectDerivation

/-!
# Actual dual star for the twelve-point direction defect

This file is the geometric entrance for the remaining direction argument.
It does not introduce a certificate or an abstract incidence interface.
Starting with an *actual* six-circle through a pivot, it constructs the
corresponding line of the restored inversion and then its genuine vertex in
the labelled dual projective arrangement.  The vertex has multiplicity five
and is off the dual line indexed by the restored pivot label `none`.

Thus the still-missing strictness is now isolated to the finite projective
count around this concrete off-line five-star; no translation between the
original circle language and the arrangement language remains implicit.
-/

namespace Erdos506.V1

open Erdos506.Block
open Erdos506.Block.BlockSystem
open Erdos506.Finite
open Erdos506.Incidence
open Erdos506.V3
open Erdos506.V4

universe u

/-- The restored line obtained from an actual circle through the inversion
pivot. -/
noncomputable def twelveDirectionRestoredCircleLine
    {alpha : Type u} [Fintype alpha] [DecidableEq alpha]
    (cfg : Configuration alpha) (p : alpha) (c : DeterminedCircle cfg)
    (hp : p ∈ circleTrace cfg c.1) :
    DeterminedLine (restoredPivotConfiguration cfg p) :=
  blockToRestoredLine cfg p ⟨Sum.inr c, hp⟩

/-- Its actual vertex in the labelled dual arrangement of the restored
configuration. -/
noncomputable def twelveDirectionOffStarVertex
    {alpha : Type u} [Fintype alpha] [DecidableEq alpha]
    (cfg : Configuration alpha) (p : alpha) (c : DeterminedCircle cfg)
    (hp : p ∈ circleTrace cfg c.1) : RealProjectivePoint :=
  determinedLineDualVertex (restoredPivotConfiguration cfg p)
    (twelveDirectionRestoredCircleLine cfg p c hp)

/-- A six-circle through the pivot becomes a five-point line after the
inversion centre is restored. -/
theorem card_lineSupport_twelveDirectionRestoredCircleLine
    {alpha : Type u} [Fintype alpha] [DecidableEq alpha]
    (cfg : Configuration alpha) (p : alpha) (c : DeterminedCircle cfg)
    (hp : p ∈ circleTrace cfg c.1)
    (hcard : (circleTrace cfg c.1).card = 6) :
    (lineSupport (restoredPivotConfiguration cfg p)
      (twelveDirectionRestoredCircleLine cfg p c hp)).card = 5 := by
  rw [show twelveDirectionRestoredCircleLine cfg p c hp =
      blockToRestoredLine cfg p ⟨Sum.inr c, hp⟩ by rfl,
    card_lineSupport_blockToRestoredLine]
  simpa [geometricBlockSupport, hcard]

/-- The dual point associated with the restored image of a selected
six-circle is an actual projective vertex, not a formal pair-index. -/
theorem twelveDirectionOffStarVertex_mem_labelDualVertexSet
    {alpha : Type u} [Fintype alpha] [DecidableEq alpha]
    (cfg : Configuration alpha) (p : alpha) (c : DeterminedCircle cfg)
    (hp : p ∈ circleTrace cfg c.1) :
    twelveDirectionOffStarVertex cfg p c hp ∈
      labelDualVertexSet (restoredPivotConfiguration cfg p) := by
  exact determinedLineDualVertex_mem_labelDualVertexSet
    (restoredPivotConfiguration cfg p)
    (twelveDirectionRestoredCircleLine cfg p c hp)

/-- The off-star vertex is fivefold in the concrete labelled dual
arrangement. -/
theorem labelDualMultiplicity_twelveDirectionOffStarVertex
    {alpha : Type u} [Fintype alpha] [DecidableEq alpha]
    (cfg : Configuration alpha) (p : alpha) (c : DeterminedCircle cfg)
    (hp : p ∈ circleTrace cfg c.1)
    (hcard : (circleTrace cfg c.1).card = 6) :
    (labelDualArrangement (restoredPivotConfiguration cfg p)).multiplicity
      (twelveDirectionOffStarVertex cfg p c hp) = 5 := by
  rw [show twelveDirectionOffStarVertex cfg p c hp =
      determinedLineDualVertex (restoredPivotConfiguration cfg p)
        (twelveDirectionRestoredCircleLine cfg p c hp) by rfl,
    labelDual_multiplicity_determinedLine]
  exact card_lineSupport_twelveDirectionRestoredCircleLine cfg p c hp hcard

/-- The fivefold vertex from a pivot circle does not lie on the dual line
indexed by `none`, i.e. by the restored inversion centre. -/
theorem twelveDirectionOffStarVertex_not_incident_none
    {alpha : Type u} [Fintype alpha] [DecidableEq alpha]
    (cfg : Configuration alpha) (p : alpha) (c : DeterminedCircle cfg)
    (hp : p ∈ circleTrace cfg c.1) :
    ¬ (labelDualArrangement (restoredPivotConfiguration cfg p)).Incident
      (twelveDirectionOffStarVertex cfg p c hp) none := by
  intro hnone
  have hmem : none ∈ lineSupport (restoredPivotConfiguration cfg p)
      (twelveDirectionRestoredCircleLine cfg p c hp) := by
    exact mem_lineSupport.mpr ((labelDual_incident_determinedLine_iff
      (restoredPivotConfiguration cfg p) none
      (twelveDirectionRestoredCircleLine cfg p c hp)).mp hnone)
  rw [show twelveDirectionRestoredCircleLine cfg p c hp =
      blockToRestoredLine cfg p ⟨Sum.inr c, hp⟩ by rfl,
    lineSupport_blockToRestoredLine] at hmem
  simpa [restoredCarrierSupport] using hmem

/-- In the no-six-line branch, every positive six-block degree supplies an
actual six-circle through the chosen pivot.  This lets the public direction
statement choose its off-star directly from its local hypothesis. -/
theorem exists_six_circle_through_of_blockDegree_six_pos_of_lineCount_six_eq_zero
    {alpha : Type u} [Fintype alpha] [DecidableEq alpha]
    (cfg : Configuration alpha) (p : alpha)
    (hdegree : 0 < (blockSystem cfg).blockDegree 6 p)
    (hline : (blockSystem cfg).lineCount 6 = 0) :
    ∃ c : DeterminedCircle cfg,
      p ∈ circleTrace cfg c.1 ∧ (circleTrace cfg c.1).card = 6 := by
  classical
  let S := blockSystem cfg
  have hfilter : 0 <
      ((S.blocksOfSize 6).filter fun b => p ∈ S.support b).card := by
    simpa [S, BlockSystem.blockDegree, BlockSystem.degreeIn] using hdegree
  obtain ⟨b, hb⟩ := Finset.card_pos.mp hfilter
  have hb' := Finset.mem_filter.mp hb
  have hbsize : (S.support b).card = 6 := S.mem_blocksOfSize.mp hb'.1
  have hbp : p ∈ S.support b := hb'.2
  cases b with
  | inl L =>
      have hL : Sum.inl L ∈ S.lineBlocksOfSize 6 := by
        apply S.mem_blocksOfKindSize.mpr
        exact ⟨rfl, hbsize⟩
      have hpositive : 0 < S.lineCount 6 := by
        exact Finset.card_pos.mpr ⟨Sum.inl L, hL⟩
      rw [hline] at hpositive
      omega
  | inr c =>
      refine ⟨c, ?_, ?_⟩
      · simpa [S, blockSystem, geometricBlockSystem,
          geometricBlockSupport] using hbp
      · simpa [S, blockSystem, geometricBlockSystem,
          geometricBlockSupport] using hbsize

/-! ## Finite star and pivot-line carriers -/

/-- The five labelled dual lines through the concrete off-star vertex. -/
noncomputable def twelveDirectionStarLabels
    {alpha : Type u} [Fintype alpha] [DecidableEq alpha]
    (cfg : Configuration alpha) (p : alpha) (c : DeterminedCircle cfg)
    (hp : p ∈ circleTrace cfg c.1) : Finset (Option (AwayFrom p)) := by
  classical
  exact Finset.univ.filter fun a =>
    (labelDualArrangement (restoredPivotConfiguration cfg p)).Incident
      (twelveDirectionOffStarVertex cfg p c hp) a

/-- The genuine labelled-dual vertices on the distinguished line indexed by
the restored pivot `none`. -/
noncomputable def twelveDirectionPivotLineVertices
    {alpha : Type u} [Fintype alpha] [DecidableEq alpha]
    (cfg : Configuration alpha) (p : alpha) : Finset RealProjectivePoint := by
  classical
  exact (labelDualVertexSet (restoredPivotConfiguration cfg p)).filter fun q =>
    (labelDualArrangement (restoredPivotConfiguration cfg p)).Incident q none

theorem mem_twelveDirectionStarLabels_iff
    {alpha : Type u} [Fintype alpha] [DecidableEq alpha]
    (cfg : Configuration alpha) (p : alpha) (c : DeterminedCircle cfg)
    (hp : p ∈ circleTrace cfg c.1) (a : Option (AwayFrom p)) :
    a ∈ twelveDirectionStarLabels cfg p c hp ↔
      (labelDualArrangement (restoredPivotConfiguration cfg p)).Incident
        (twelveDirectionOffStarVertex cfg p c hp) a := by
  classical
  simp [twelveDirectionStarLabels]

theorem mem_twelveDirectionPivotLineVertices_iff
    {alpha : Type u} [Fintype alpha] [DecidableEq alpha]
    (cfg : Configuration alpha) (p : alpha) (q : RealProjectivePoint) :
    q ∈ twelveDirectionPivotLineVertices cfg p ↔
      q ∈ labelDualVertexSet (restoredPivotConfiguration cfg p) ∧
      (labelDualArrangement (restoredPivotConfiguration cfg p)).Incident q none := by
  classical
  simp [twelveDirectionPivotLineVertices]

/-- The star carrier has exactly its five expected labelled lines. -/
theorem card_twelveDirectionStarLabels
    {alpha : Type u} [Fintype alpha] [DecidableEq alpha]
    (cfg : Configuration alpha) (p : alpha) (c : DeterminedCircle cfg)
    (hp : p ∈ circleTrace cfg c.1)
    (hcard : (circleTrace cfg c.1).card = 6) :
    (twelveDirectionStarLabels cfg p c hp).card = 5 := by
  classical
  unfold twelveDirectionStarLabels
  change (labelDualArrangement (restoredPivotConfiguration cfg p)).multiplicity
    (twelveDirectionOffStarVertex cfg p c hp) = 5
  exact labelDualMultiplicity_twelveDirectionOffStarVertex cfg p c hp hcard

/-- The actual projective intersection of a star arm with the distinguished
pivot line. -/
noncomputable def twelveDirectionStarPivotIntersection
    {alpha : Type u} [Fintype alpha] [DecidableEq alpha]
    (cfg : Configuration alpha) (p : alpha) (a : Option (AwayFrom p)) :
    RealProjectivePoint :=
  (labelDualArrangement (restoredPivotConfiguration cfg p)).intersection none a

/-- No star label is the pivot label: this is precisely the fact that the
fivefold vertex is off the distinguished line. -/
theorem twelveDirectionStarLabel_ne_none
    {alpha : Type u} [Fintype alpha] [DecidableEq alpha]
    (cfg : Configuration alpha) (p : alpha) (c : DeterminedCircle cfg)
    (hp : p ∈ circleTrace cfg c.1) {a : Option (AwayFrom p)}
    (ha : a ∈ twelveDirectionStarLabels cfg p c hp) : a ≠ none := by
  intro h
  subst a
  have hincident :
      (labelDualArrangement (restoredPivotConfiguration cfg p)).Incident
        (twelveDirectionOffStarVertex cfg p c hp) none :=
    (mem_twelveDirectionStarLabels_iff cfg p c hp none).mp ha
  exact twelveDirectionOffStarVertex_not_incident_none cfg p c hp hincident

/-- Every arm meets the pivot line in an actual arrangement vertex. -/
theorem twelveDirectionStarPivotIntersection_mem_pivotLineVertices
    {alpha : Type u} [Fintype alpha] [DecidableEq alpha]
    (cfg : Configuration alpha) (p : alpha) (c : DeterminedCircle cfg)
    (hp : p ∈ circleTrace cfg c.1) {a : Option (AwayFrom p)}
    (ha : a ∈ twelveDirectionStarLabels cfg p c hp) :
    twelveDirectionStarPivotIntersection cfg p a ∈
      twelveDirectionPivotLineVertices cfg p := by
  have hne : none ≠ a := by
    intro h
    exact twelveDirectionStarLabel_ne_none cfg p c hp ha h.symm
  rw [mem_twelveDirectionPivotLineVertices_iff]
  constructor
  · exact labelDualIntersection_mem_vertexSet
      (restoredPivotConfiguration cfg p) hne
  · exact labelDualIntersection_incident_left
      (restoredPivotConfiguration cfg p) hne

/-- Different arms of the off-star have different intersections with the
pivot line.  Otherwise their common projective intersection would be the
off-star itself and would put it on that pivot line. -/
theorem twelveDirectionStarPivotIntersection_injective_on_star
    {alpha : Type u} [Fintype alpha] [DecidableEq alpha]
    (cfg : Configuration alpha) (p : alpha) (c : DeterminedCircle cfg)
    (hp : p ∈ circleTrace cfg c.1) :
    Set.InjOn (twelveDirectionStarPivotIntersection cfg p)
      (↑(twelveDirectionStarLabels cfg p c hp) : Set (Option (AwayFrom p))) := by
  classical
  intro a ha b hb hab
  by_contra habne
  have hstarA :
      (labelDualArrangement (restoredPivotConfiguration cfg p)).Incident
        (twelveDirectionOffStarVertex cfg p c hp) a :=
    (mem_twelveDirectionStarLabels_iff cfg p c hp a).mp ha
  have hstarB :
      (labelDualArrangement (restoredPivotConfiguration cfg p)).Incident
        (twelveDirectionOffStarVertex cfg p c hp) b :=
    (mem_twelveDirectionStarLabels_iff cfg p c hp b).mp hb
  have hv : twelveDirectionOffStarVertex cfg p c hp =
      (labelDualArrangement (restoredPivotConfiguration cfg p)).intersection a b :=
    labelDual_eq_intersection_of_incident
      (restoredPivotConfiguration cfg p) habne hstarA hstarB
  have hnoneA : none ≠ a := by
    intro h
    exact twelveDirectionStarLabel_ne_none cfg p c hp ha h.symm
  have hnoneB : none ≠ b := by
    intro h
    exact twelveDirectionStarLabel_ne_none cfg p c hp hb h.symm
  have hAtB :
      (labelDualArrangement (restoredPivotConfiguration cfg p)).Incident
        ((labelDualArrangement (restoredPivotConfiguration cfg p)).intersection none a) b := by
    have hbAt :
        (labelDualArrangement (restoredPivotConfiguration cfg p)).Incident
          (twelveDirectionStarPivotIntersection cfg p b) b := by
      change (labelDualArrangement (restoredPivotConfiguration cfg p)).Incident
        ((labelDualArrangement (restoredPivotConfiguration cfg p)).intersection none b) b
      exact labelDualIntersection_incident_right
        (restoredPivotConfiguration cfg p) hnoneB
    change (labelDualArrangement (restoredPivotConfiguration cfg p)).Incident
      (twelveDirectionStarPivotIntersection cfg p a) b
    exact hab ▸ hbAt
  have hsame :
      (labelDualArrangement (restoredPivotConfiguration cfg p)).intersection none a =
        (labelDualArrangement (restoredPivotConfiguration cfg p)).intersection a b :=
    labelDual_eq_intersection_of_incident
      (restoredPivotConfiguration cfg p) habne
      (labelDualIntersection_incident_right (restoredPivotConfiguration cfg p) hnoneA)
      hAtB
  have hvertexOnPivot :
      (labelDualArrangement (restoredPivotConfiguration cfg p)).Incident
        (twelveDirectionOffStarVertex cfg p c hp) none := by
    rw [hv, ← hsame]
    exact labelDualIntersection_incident_left
      (restoredPivotConfiguration cfg p) hnoneA
  exact twelveDirectionOffStarVertex_not_incident_none cfg p c hp hvertexOnPivot

/-- The distinguished line contains the five distinct intersections with
the fivefold off-star. -/
theorem five_le_card_twelveDirectionPivotLineVertices
    {alpha : Type u} [Fintype alpha] [DecidableEq alpha]
    (cfg : Configuration alpha) (p : alpha) (c : DeterminedCircle cfg)
    (hp : p ∈ circleTrace cfg c.1)
    (hcard : (circleTrace cfg c.1).card = 6) :
    5 ≤ (twelveDirectionPivotLineVertices cfg p).card := by
  classical
  let f : {a // a ∈ twelveDirectionStarLabels cfg p c hp} →
      {q // q ∈ twelveDirectionPivotLineVertices cfg p} := fun a =>
    ⟨twelveDirectionStarPivotIntersection cfg p a.1,
      twelveDirectionStarPivotIntersection_mem_pivotLineVertices
        cfg p c hp a.2⟩
  have hf : Function.Injective f := by
    intro a b hab
    apply Subtype.ext
    apply twelveDirectionStarPivotIntersection_injective_on_star cfg p c hp
    · exact a.2
    · exact b.2
    · exact congrArg Subtype.val hab
  have hle := Fintype.card_le_of_injective f hf
  have hstar : Fintype.card {a // a ∈ twelveDirectionStarLabels cfg p c hp} = 5 := by
    simpa using card_twelveDirectionStarLabels cfg p c hp hcard
  rw [hstar] at hle
  simpa using hle

/-! ## Actual off-star vertices -/

/-- The actual dual vertices which lie on none of the five labelled lines
through the off-star. -/
noncomputable def twelveDirectionOffStarVertices
    {alpha : Type u} [Fintype alpha] [DecidableEq alpha]
    (cfg : Configuration alpha) (p : alpha) (c : DeterminedCircle cfg)
    (hp : p ∈ circleTrace cfg c.1) : Finset RealProjectivePoint := by
  classical
  exact (labelDualVertexSet (restoredPivotConfiguration cfg p)).filter fun q =>
    ∀ a ∈ twelveDirectionStarLabels cfg p c hp,
      ¬ (labelDualArrangement (restoredPivotConfiguration cfg p)).Incident q a

theorem mem_twelveDirectionOffStarVertices_iff
    {alpha : Type u} [Fintype alpha] [DecidableEq alpha]
    (cfg : Configuration alpha) (p : alpha) (c : DeterminedCircle cfg)
    (hp : p ∈ circleTrace cfg c.1) (q : RealProjectivePoint) :
    q ∈ twelveDirectionOffStarVertices cfg p c hp ↔
      q ∈ labelDualVertexSet (restoredPivotConfiguration cfg p) ∧
      ∀ a ∈ twelveDirectionStarLabels cfg p c hp,
        ¬ (labelDualArrangement (restoredPivotConfiguration cfg p)).Incident q a := by
  classical
  simp [twelveDirectionOffStarVertices]

/-- Every actual labelled-dual vertex has at least two incident labelled
lines, hence contributes at least one unit to a multiplicity-minus-one
defect count. -/
theorem one_le_labelDualMultiplicity_sub_one_of_mem_vertexSet
    {alpha : Type u} [Fintype alpha] [DecidableEq alpha]
    (cfg : Configuration alpha) {q : RealProjectivePoint}
    (hq : q ∈ labelDualVertexSet cfg) :
    1 ≤ (labelDualArrangement cfg).multiplicity q - 1 := by
  obtain ⟨a, b, hab, hint⟩ := exists_label_pair_of_mem_labelDualVertexSet cfg hq
  have htwo : 2 ≤ (labelDualArrangement cfg).multiplicity q := by
    rw [← hint]
    exact two_le_labelDualMultiplicity_intersection cfg hab
  omega

/-- On one line of a finite projective arrangement, the sum of
`multiplicity - 1` over its actual vertices counts every other indexed line
exactly once.  Concurrent intersections are automatically grouped by the
finite vertex set, so this is the weighted form of the elementary
"one intersection with every other line" count. -/
theorem sum_multiplicity_sub_one_lineVertexSet
    {Line : Type*} [Fintype Line] [DecidableEq Line]
    (A : FiniteProjectiveLineArrangement Line) (a : Line) :
    (∑ q ∈ A.lineVertexSet a, (A.multiplicity q - 1)) =
      Fintype.card Line - 1 := by
  classical
  let B : Finset Line := Finset.univ.erase a
  let f : Line → RealProjectivePoint := fun b => A.intersection a b
  have hmaps : ∀ b ∈ B, f b ∈ A.lineVertexSet a := by
    intro b hb
    have hba : b ≠ a := by
      exact (Finset.mem_erase.mp hb).1
    exact (A.mem_lineVertexSet a).mpr ⟨
      A.intersection_mem_vertexSet hba.symm,
      A.intersection_incident_left hba.symm⟩
  have hfiber : ∀ q ∈ A.lineVertexSet a,
      (B.filter fun b => f b = q).card = A.multiplicity q - 1 := by
    intro q hq
    have hqa : A.Incident q a := (A.mem_lineVertexSet a).mp hq |>.2
    have hset : B.filter (fun b => f b = q) =
        (Finset.univ.filter fun b => A.Incident q b).erase a := by
      ext b
      constructor
      · intro hb
        have hbB : b ∈ B := (Finset.mem_filter.mp hb).1
        have habq : f b = q := (Finset.mem_filter.mp hb).2
        have hba : b ≠ a := (Finset.mem_erase.mp hbB).1
        apply Finset.mem_erase.mpr
        refine ⟨hba, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
        rw [← habq]
        exact A.intersection_incident_right hba.symm
      · intro hb
        have hba : b ≠ a := (Finset.mem_erase.mp hb).1
        have hqb : A.Incident q b :=
          (Finset.mem_filter.mp (Finset.mem_erase.mp hb).2).2
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_erase.mpr ⟨hba, Finset.mem_univ _⟩, ?_⟩
        exact (A.eq_intersection_of_incident hba.symm hqa hqb).symm
    rw [hset, Finset.card_erase_of_mem]
    · rfl
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hqa⟩
  have hsum := Finset.sum_card_fiberwise_eq_card_filter
    B (A.lineVertexSet a) f
  have hfilter : B.filter (fun b => f b ∈ A.lineVertexSet a) = B := by
    exact Finset.filter_eq_self.mpr hmaps
  calc
    (∑ q ∈ A.lineVertexSet a, (A.multiplicity q - 1)) =
        ∑ q ∈ A.lineVertexSet a, (B.filter fun b => f b = q).card := by
      apply Finset.sum_congr rfl
      intro q hq
      exact (hfiber q hq).symm
    _ = (B.filter fun b => f b ∈ A.lineVertexSet a).card := hsum
    _ = B.card := by rw [hfilter]
    _ = Fintype.card Line - 1 := by simp [B]

/-- A vertex of the distinguished pivot line which is not one of the five
star intersections is genuinely off the five-star. -/
theorem mem_twelveDirectionOffStarVertices_of_mem_pivotLine_of_not_starIntersection
    {alpha : Type u} [Fintype alpha] [DecidableEq alpha]
    (cfg : Configuration alpha) (p : alpha) (c : DeterminedCircle cfg)
    (hp : p ∈ circleTrace cfg c.1) {q : RealProjectivePoint}
    (hq : q ∈ twelveDirectionPivotLineVertices cfg p)
    (hnot : ∀ a ∈ twelveDirectionStarLabels cfg p c hp,
      twelveDirectionStarPivotIntersection cfg p a ≠ q) :
    q ∈ twelveDirectionOffStarVertices cfg p c hp := by
  rw [mem_twelveDirectionOffStarVertices_iff]
  refine ⟨(mem_twelveDirectionPivotLineVertices_iff cfg p q).mp hq |>.1, ?_⟩
  intro a ha hqa
  have hne : none ≠ a := by
    intro h
    exact twelveDirectionStarLabel_ne_none cfg p c hp ha h.symm
  have hqnone :
      (labelDualArrangement (restoredPivotConfiguration cfg p)).Incident q none :=
    (mem_twelveDirectionPivotLineVertices_iff cfg p q).mp hq |>.2
  have hqeq : q =
      (labelDualArrangement (restoredPivotConfiguration cfg p)).intersection none a :=
    labelDual_eq_intersection_of_incident
      (restoredPivotConfiguration cfg p) hne hqnone hqa
  apply hnot a ha
  change twelveDirectionStarPivotIntersection cfg p a = q
  exact hqeq.symm

/-! ## The elementary defect count -/

/-- The five intersections of the star arms with the distinguished line. -/
noncomputable def twelveDirectionStarPivotIntersections
    {alpha : Type u} [Fintype alpha] [DecidableEq alpha]
    (cfg : Configuration alpha) (p : alpha) (c : DeterminedCircle cfg)
    (hp : p ∈ circleTrace cfg c.1) : Finset RealProjectivePoint := by
  classical
  exact (twelveDirectionStarLabels cfg p c hp).image
    (twelveDirectionStarPivotIntersection cfg p)

/-- The remaining vertices of the distinguished line after its five star
intersections have been removed. -/
noncomputable def twelveDirectionExtraPivotVertices
    {alpha : Type u} [Fintype alpha] [DecidableEq alpha]
    (cfg : Configuration alpha) (p : alpha) (c : DeterminedCircle cfg)
    (hp : p ∈ circleTrace cfg c.1) : Finset RealProjectivePoint := by
  classical
  exact twelveDirectionPivotLineVertices cfg p \
    twelveDirectionStarPivotIntersections cfg p c hp

theorem twelveDirectionStarPivotIntersections_subset_pivotLineVertices
    {alpha : Type u} [Fintype alpha] [DecidableEq alpha]
    (cfg : Configuration alpha) (p : alpha) (c : DeterminedCircle cfg)
    (hp : p ∈ circleTrace cfg c.1) :
    twelveDirectionStarPivotIntersections cfg p c hp ⊆
      twelveDirectionPivotLineVertices cfg p := by
  classical
  intro q hq
  obtain ⟨a, ha, heq⟩ := Finset.mem_image.mp hq
  rw [← heq]
  exact twelveDirectionStarPivotIntersection_mem_pivotLineVertices
    cfg p c hp ha

theorem card_twelveDirectionStarPivotIntersections
    {alpha : Type u} [Fintype alpha] [DecidableEq alpha]
    (cfg : Configuration alpha) (p : alpha) (c : DeterminedCircle cfg)
    (hp : p ∈ circleTrace cfg c.1)
    (hcard : (circleTrace cfg c.1).card = 6) :
    (twelveDirectionStarPivotIntersections cfg p c hp).card = 5 := by
  classical
  unfold twelveDirectionStarPivotIntersections
  rw [Finset.card_image_iff.mpr
    (twelveDirectionStarPivotIntersection_injective_on_star cfg p c hp),
    card_twelveDirectionStarLabels cfg p c hp hcard]

theorem twelveDirectionExtraPivotVertices_subset_offStarVertices
    {alpha : Type u} [Fintype alpha] [DecidableEq alpha]
    (cfg : Configuration alpha) (p : alpha) (c : DeterminedCircle cfg)
    (hp : p ∈ circleTrace cfg c.1) :
    twelveDirectionExtraPivotVertices cfg p c hp ⊆
      twelveDirectionOffStarVertices cfg p c hp := by
  classical
  intro q hq
  have hsplit : q ∈ twelveDirectionPivotLineVertices cfg p ∧
      q ∉ twelveDirectionStarPivotIntersections cfg p c hp := by
    simpa [twelveDirectionExtraPivotVertices] using hq
  apply mem_twelveDirectionOffStarVertices_of_mem_pivotLine_of_not_starIntersection
    cfg p c hp hsplit.1
  intro a ha heq
  apply hsplit.2
  unfold twelveDirectionStarPivotIntersections
  exact Finset.mem_image.mpr ⟨a, ha, heq⟩

/-- The concrete nonnegative off-star defect. -/
noncomputable def twelveDirectionActualOffStarDefect
    {alpha : Type u} [Fintype alpha] [DecidableEq alpha]
    (cfg : Configuration alpha) (p : alpha) (c : DeterminedCircle cfg)
    (hp : p ∈ circleTrace cfg c.1) : Nat :=
  ∑ q ∈ twelveDirectionOffStarVertices cfg p c hp,
    ((labelDualArrangement (restoredPivotConfiguration cfg p)).multiplicity q - 1)

/-- The complementary carrier: all actual vertices met by at least one arm
of the concrete five-star.  This is a finite subset of the genuine dual
vertex set, rather than an abstract star interface. -/
noncomputable def twelveDirectionStarVertices
    {alpha : Type u} [Fintype alpha] [DecidableEq alpha]
    (cfg : Configuration alpha) (p : alpha) (c : DeterminedCircle cfg)
    (hp : p ∈ circleTrace cfg c.1) : Finset RealProjectivePoint := by
  classical
  exact (labelDualVertexSet (restoredPivotConfiguration cfg p)).filter fun q =>
    ∃ a ∈ twelveDirectionStarLabels cfg p c hp,
      (labelDualArrangement (restoredPivotConfiguration cfg p)).Incident q a

theorem mem_twelveDirectionStarVertices_iff
    {alpha : Type u} [Fintype alpha] [DecidableEq alpha]
    (cfg : Configuration alpha) (p : alpha) (c : DeterminedCircle cfg)
    (hp : p ∈ circleTrace cfg c.1) (q : RealProjectivePoint) :
    q ∈ twelveDirectionStarVertices cfg p c hp ↔
      q ∈ labelDualVertexSet (restoredPivotConfiguration cfg p) ∧
      ∃ a ∈ twelveDirectionStarLabels cfg p c hp,
        (labelDualArrangement (restoredPivotConfiguration cfg p)).Incident q a := by
  classical
  simp [twelveDirectionStarVertices]

/-- Number of the five selected star arms through an actual dual point. -/
noncomputable def twelveDirectionStarMultiplicity
    {alpha : Type u} [Fintype alpha] [DecidableEq alpha]
    (cfg : Configuration alpha) (p : alpha) (c : DeterminedCircle cfg)
    (hp : p ∈ circleTrace cfg c.1) (q : RealProjectivePoint) : Nat := by
  classical
  exact ((twelveDirectionStarLabels cfg p c hp).filter fun a =>
    (labelDualArrangement (restoredPivotConfiguration cfg p)).Incident q a).card

theorem twelveDirectionOffStarVertex_mem_starVertices
    {alpha : Type u} [Fintype alpha] [DecidableEq alpha]
    (cfg : Configuration alpha) (p : alpha) (c : DeterminedCircle cfg)
    (hp : p ∈ circleTrace cfg c.1)
    (hcard : (circleTrace cfg c.1).card = 6) :
    twelveDirectionOffStarVertex cfg p c hp ∈
      twelveDirectionStarVertices cfg p c hp := by
  rw [mem_twelveDirectionStarVertices_iff]
  refine ⟨twelveDirectionOffStarVertex_mem_labelDualVertexSet cfg p c hp, ?_⟩
  have hpos : 0 < (twelveDirectionStarLabels cfg p c hp).card := by
    rw [card_twelveDirectionStarLabels cfg p c hp hcard]
    norm_num
  obtain ⟨a, ha⟩ := Finset.card_pos.mp hpos
  exact ⟨a, ha, (mem_twelveDirectionStarLabels_iff cfg p c hp a).mp ha⟩

theorem twelveDirectionStarMultiplicity_offStarVertex
    {alpha : Type u} [Fintype alpha] [DecidableEq alpha]
    (cfg : Configuration alpha) (p : alpha) (c : DeterminedCircle cfg)
    (hp : p ∈ circleTrace cfg c.1)
    (hcard : (circleTrace cfg c.1).card = 6) :
    twelveDirectionStarMultiplicity cfg p c hp
      (twelveDirectionOffStarVertex cfg p c hp) = 5 := by
  classical
  unfold twelveDirectionStarMultiplicity
  rw [Finset.filter_eq_self.mpr]
  · exact card_twelveDirectionStarLabels cfg p c hp hcard
  · intro a ha
    exact (mem_twelveDirectionStarLabels_iff cfg p c hp a).mp ha

/-- Away from the common fivefold centre, a star vertex lies on exactly one
of the five selected arms. -/
theorem twelveDirectionStarMultiplicity_eq_one_of_ne_offStarVertex
    {alpha : Type u} [Fintype alpha] [DecidableEq alpha]
    (cfg : Configuration alpha) (p : alpha) (c : DeterminedCircle cfg)
    (hp : p ∈ circleTrace cfg c.1) {q : RealProjectivePoint}
    (hq : q ∈ twelveDirectionStarVertices cfg p c hp)
    (hqne : q ≠ twelveDirectionOffStarVertex cfg p c hp) :
    twelveDirectionStarMultiplicity cfg p c hp q = 1 := by
  classical
  let A := labelDualArrangement (restoredPivotConfiguration cfg p)
  let S := twelveDirectionStarLabels cfg p c hp
  obtain ⟨_hqVertex, a, haS, hqa⟩ :=
    (mem_twelveDirectionStarVertices_iff cfg p c hp q).mp hq
  have hfilter : S.filter (fun b => A.Incident q b) = {a} := by
    ext b
    simp only [Finset.mem_filter, Finset.mem_singleton]
    constructor
    · rintro ⟨hbS, hqb⟩
      by_contra hba
      have hqint : q = A.intersection b a :=
        A.eq_intersection_of_incident hba hqb hqa
      have hvb : A.Incident (twelveDirectionOffStarVertex cfg p c hp) b := by
        exact (mem_twelveDirectionStarLabels_iff cfg p c hp b).mp hbS
      have hva : A.Incident (twelveDirectionOffStarVertex cfg p c hp) a := by
        exact (mem_twelveDirectionStarLabels_iff cfg p c hp a).mp haS
      have hvint : twelveDirectionOffStarVertex cfg p c hp =
          A.intersection b a :=
        A.eq_intersection_of_incident hba hvb hva
      exact hqne (hqint.trans hvint.symm)
    · intro hba
      subst b
      exact ⟨haS, hqa⟩
  unfold twelveDirectionStarMultiplicity
  change (S.filter fun b => A.Incident q b).card = 1
  rw [hfilter]
  simp

/-- Swap the two finite incidence sums for a selected family of arrangement
lines.  The right side records how many selected lines pass through each
actual vertex. -/
noncomputable def selectedLineMultiplicity
    {Line : Type*} [Fintype Line] [DecidableEq Line]
    (A : FiniteProjectiveLineArrangement Line) (S : Finset Line)
    (q : RealProjectivePoint) : Nat := by
  classical
  exact (S.filter fun a => A.Incident q a).card

theorem sum_lineVertexSet_eq_sum_selectedMultiplicity
    {Line : Type*} [Fintype Line] [DecidableEq Line]
    (A : FiniteProjectiveLineArrangement Line) (S : Finset Line)
    (d : RealProjectivePoint → Nat) :
    (∑ a ∈ S, ∑ q ∈ A.lineVertexSet a, d q) =
      ∑ q ∈ A.vertexSet,
        selectedLineMultiplicity A S q * d q := by
  classical
  calc
    (∑ a ∈ S, ∑ q ∈ A.lineVertexSet a, d q) =
        ∑ a ∈ S, ∑ q ∈ A.vertexSet,
          if A.Incident q a then d q else 0 := by
      apply Finset.sum_congr rfl
      intro a ha
      unfold FiniteProjectiveLineArrangement.lineVertexSet
      exact Finset.sum_filter _ _
    _ = ∑ q ∈ A.vertexSet, ∑ a ∈ S,
          if A.Incident q a then d q else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ q ∈ A.vertexSet,
        selectedLineMultiplicity A S q * d q := by
      apply Finset.sum_congr rfl
      intro q hq
      unfold selectedLineMultiplicity
      rw [← Finset.sum_filter]
      simp

/-- The five-arm incidence sum is supported exactly on the concrete star
vertices. -/
theorem sum_starLineVertexSet_eq_sum_starMultiplicity
    {alpha : Type u} [Fintype alpha] [DecidableEq alpha]
    (cfg : Configuration alpha) (p : alpha) (c : DeterminedCircle cfg)
    (hp : p ∈ circleTrace cfg c.1) :
    (∑ a ∈ twelveDirectionStarLabels cfg p c hp,
      ∑ q ∈ (labelDualArrangement (restoredPivotConfiguration cfg p)).lineVertexSet a,
        ((labelDualArrangement (restoredPivotConfiguration cfg p)).multiplicity q - 1)) =
      ∑ q ∈ twelveDirectionStarVertices cfg p c hp,
        twelveDirectionStarMultiplicity cfg p c hp q *
          ((labelDualArrangement (restoredPivotConfiguration cfg p)).multiplicity q - 1) := by
  classical
  let A := labelDualArrangement (restoredPivotConfiguration cfg p)
  let S := twelveDirectionStarLabels cfg p c hp
  let d : RealProjectivePoint → Nat := fun q => A.multiplicity q - 1
  have hdouble := sum_lineVertexSet_eq_sum_selectedMultiplicity A S d
  have hsupp : (∑ q ∈ A.vertexSet,
      selectedLineMultiplicity A S q * d q) =
      ∑ q ∈ A.vertexSet.filter (fun q => ∃ a ∈ S, A.Incident q a),
        selectedLineMultiplicity A S q * d q := by
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro q hqV hqNot
    have hno : ¬ ∃ a ∈ S, A.Incident q a := by
      intro hex
      exact hqNot (Finset.mem_filter.mpr ⟨hqV, hex⟩)
    have hzero : selectedLineMultiplicity A S q = 0 := by
      unfold selectedLineMultiplicity
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro a haS hqa
      exact hno ⟨a, haS, hqa⟩
    simp [hzero]
  calc
    (∑ a ∈ twelveDirectionStarLabels cfg p c hp,
      ∑ q ∈ (labelDualArrangement (restoredPivotConfiguration cfg p)).lineVertexSet a,
        ((labelDualArrangement (restoredPivotConfiguration cfg p)).multiplicity q - 1)) =
        ∑ q ∈ A.vertexSet,
          selectedLineMultiplicity A S q * d q := by
      simpa only [A, S, d] using hdouble
    _ = ∑ q ∈ A.vertexSet.filter (fun q => ∃ a ∈ S, A.Incident q a),
          selectedLineMultiplicity A S q * d q := hsupp
    _ = ∑ q ∈ twelveDirectionStarVertices cfg p c hp,
        twelveDirectionStarMultiplicity cfg p c hp q *
          ((labelDualArrangement (restoredPivotConfiguration cfg p)).multiplicity q - 1) := by
      simp only [A, S, d, twelveDirectionStarVertices,
        selectedLineMultiplicity, twelveDirectionStarMultiplicity,
        labelDualVertexSet]

theorem twelveDirectionStarVertices_subset_labelDualVertexSet
    {alpha : Type u} [Fintype alpha] [DecidableEq alpha]
    (cfg : Configuration alpha) (p : alpha) (c : DeterminedCircle cfg)
    (hp : p ∈ circleTrace cfg c.1) :
    twelveDirectionStarVertices cfg p c hp ⊆
      labelDualVertexSet (restoredPivotConfiguration cfg p) := by
  classical
  exact Finset.filter_subset _ _

/-- Off-star vertices are exactly the complement of the vertices met by
the five concrete arms. -/
noncomputable def twelveDirectionOffStarComplement
    {alpha : Type u} [Fintype alpha] [DecidableEq alpha]
    (cfg : Configuration alpha) (p : alpha) (c : DeterminedCircle cfg)
    (hp : p ∈ circleTrace cfg c.1) : Finset RealProjectivePoint := by
  classical
  exact labelDualVertexSet (restoredPivotConfiguration cfg p) \
    twelveDirectionStarVertices cfg p c hp

theorem twelveDirectionOffStarVertices_eq_sdiff_starVertices
    {alpha : Type u} [Fintype alpha] [DecidableEq alpha]
    (cfg : Configuration alpha) (p : alpha) (c : DeterminedCircle cfg)
    (hp : p ∈ circleTrace cfg c.1) :
    twelveDirectionOffStarVertices cfg p c hp =
      twelveDirectionOffStarComplement cfg p c hp := by
  classical
  ext q
  constructor
  · intro hq
    obtain ⟨hqVertex, hqAvoids⟩ :=
      (mem_twelveDirectionOffStarVertices_iff cfg p c hp q).mp hq
    apply Finset.mem_sdiff.mpr
    refine ⟨hqVertex, ?_⟩
    intro hqStar
    obtain ⟨_hqVertex', a, ha, hqa⟩ := by
      simpa only [twelveDirectionStarVertices, Finset.mem_filter] using hqStar
    exact hqAvoids a ha hqa
  · intro hq
    obtain ⟨hqVertex, hqNotStar⟩ := Finset.mem_sdiff.mp hq
    apply (mem_twelveDirectionOffStarVertices_iff cfg p c hp q).mpr
    refine ⟨hqVertex, ?_⟩
    intro a ha hqa
    apply hqNotStar
    simp only [twelveDirectionStarVertices, Finset.mem_filter]
    exact ⟨hqVertex, a, ha, hqa⟩

/-- The total concrete multiplicity-minus-one census of the restored dual
arrangement. -/
noncomputable def twelveDirectionTotalDualDefect
    {alpha : Type u} [Fintype alpha] [DecidableEq alpha]
    (cfg : Configuration alpha) (p : alpha) : Nat :=
  ∑ q ∈ labelDualVertexSet (restoredPivotConfiguration cfg p),
    ((labelDualArrangement (restoredPivotConfiguration cfg p)).multiplicity q - 1)

/-- The part of the total defect lying on the actual five-star. -/
noncomputable def twelveDirectionStarDefect
    {alpha : Type u} [Fintype alpha] [DecidableEq alpha]
    (cfg : Configuration alpha) (p : alpha) (c : DeterminedCircle cfg)
    (hp : p ∈ circleTrace cfg c.1) : Nat :=
  ∑ q ∈ twelveDirectionStarVertices cfg p c hp,
    ((labelDualArrangement (restoredPivotConfiguration cfg p)).multiplicity q - 1)

/-- Exact local star count for twelve labels: each of the five arms meets
the other eleven lines, and the common fivefold centre is overcounted by
`5 * 4 - 4 = 16`.  Hence the actual star defect is `5 * 11 - 16 = 39`. -/
theorem twelveDirectionStarDefect_eq_thirty_nine
    {alpha : Type u} [Fintype alpha] [DecidableEq alpha]
    (cfg : Configuration alpha) (p : alpha) (c : DeterminedCircle cfg)
    (hp : p ∈ circleTrace cfg c.1)
    (hpoints : Fintype.card alpha = 12)
    (hcircle : (circleTrace cfg c.1).card = 6) :
    twelveDirectionStarDefect cfg p c hp = 39 := by
  classical
  let A := labelDualArrangement (restoredPivotConfiguration cfg p)
  let S := twelveDirectionStarLabels cfg p c hp
  let T := twelveDirectionStarVertices cfg p c hp
  let v := twelveDirectionOffStarVertex cfg p c hp
  let d : RealProjectivePoint → Nat := fun q => A.multiplicity q - 1
  have hlineCard : Fintype.card (Option (AwayFrom p)) = 12 := by
    rw [Fintype.card_option, card_awayFrom, hpoints]
  have hS : S.card = 5 := by
    simpa only [S] using card_twelveDirectionStarLabels cfg p c hp hcircle
  have hvT : v ∈ T := by
    simpa only [v, T] using
      twelveDirectionOffStarVertex_mem_starVertices cfg p c hp hcircle
  have hdv : d v = 4 := by
    change A.multiplicity v - 1 = 4
    have hvMult := labelDualMultiplicity_twelveDirectionOffStarVertex
      cfg p c hp hcircle
    simpa only [A, v] using congrArg (fun n : Nat => n - 1) hvMult
  have hstarv : twelveDirectionStarMultiplicity cfg p c hp v = 5 := by
    simpa only [v] using
      twelveDirectionStarMultiplicity_offStarVertex cfg p c hp hcircle
  have harms : (∑ a ∈ S, ∑ q ∈ A.lineVertexSet a, d q) = 55 := by
    calc
      (∑ a ∈ S, ∑ q ∈ A.lineVertexSet a, d q) =
          ∑ _a ∈ S, 11 := by
        apply Finset.sum_congr rfl
        intro a ha
        rw [sum_multiplicity_sub_one_lineVertexSet]
        simpa only [A, d, hlineCard]
      _ = 55 := by simp [hS]
  have hweighted : (∑ q ∈ T,
      twelveDirectionStarMultiplicity cfg p c hp q * d q) =
      (∑ q ∈ T.erase v, d q) + 20 := by
    rw [← T.sum_erase_add (fun q =>
      twelveDirectionStarMultiplicity cfg p c hp q * d q) hvT]
    congr 1
    · apply Finset.sum_congr rfl
      intro q hq
      have hqT : q ∈ T := (Finset.mem_erase.mp hq).2
      have hqne : q ≠ v := (Finset.mem_erase.mp hq).1
      have hone := twelveDirectionStarMultiplicity_eq_one_of_ne_offStarVertex
        cfg p c hp (by simpa only [T] using hqT) (by simpa only [v] using hqne)
      rw [hone]
      simp
    · rw [hstarv, hdv]
  have hstar : twelveDirectionStarDefect cfg p c hp =
      (∑ q ∈ T.erase v, d q) + 4 := by
    unfold twelveDirectionStarDefect
    change (∑ q ∈ T, d q) = _
    rw [← T.sum_erase_add d hvT, hdv]
  have hdouble := sum_starLineVertexSet_eq_sum_starMultiplicity cfg p c hp
  have h55weighted : (∑ q ∈ T,
      twelveDirectionStarMultiplicity cfg p c hp q * d q) = 55 := by
    rw [← harms]
    simpa only [A, S, T, d] using hdouble.symm
  omega

/-- Exact finite partition of the dual defect into the off-star and star
carriers.  The forthcoming local fibre count will identify the second term
with `39`. -/
theorem twelveDirectionTotalDualDefect_eq_actualOffStarDefect_add_starDefect
    {alpha : Type u} [Fintype alpha] [DecidableEq alpha]
    (cfg : Configuration alpha) (p : alpha) (c : DeterminedCircle cfg)
    (hp : p ∈ circleTrace cfg c.1) :
    twelveDirectionTotalDualDefect cfg p =
      twelveDirectionActualOffStarDefect cfg p c hp +
        twelveDirectionStarDefect cfg p c hp := by
  classical
  unfold twelveDirectionTotalDualDefect twelveDirectionActualOffStarDefect
    twelveDirectionStarDefect
  rw [twelveDirectionOffStarVertices_eq_sdiff_starVertices cfg p c hp]
  unfold twelveDirectionOffStarComplement
  exact (Finset.sum_sdiff
    (twelveDirectionStarVertices_subset_labelDualVertexSet cfg p c hp)).symm

theorem card_twelveDirectionOffStarVertices_le_actualDefect
    {alpha : Type u} [Fintype alpha] [DecidableEq alpha]
    (cfg : Configuration alpha) (p : alpha) (c : DeterminedCircle cfg)
    (hp : p ∈ circleTrace cfg c.1) :
    (twelveDirectionOffStarVertices cfg p c hp).card ≤
      twelveDirectionActualOffStarDefect cfg p c hp := by
  classical
  unfold twelveDirectionActualOffStarDefect
  calc
    (twelveDirectionOffStarVertices cfg p c hp).card =
        ∑ q ∈ twelveDirectionOffStarVertices cfg p c hp, 1 := by
      rw [Finset.card_eq_sum_ones]
    _ ≤ ∑ q ∈ twelveDirectionOffStarVertices cfg p c hp,
        ((labelDualArrangement (restoredPivotConfiguration cfg p)).multiplicity q - 1) := by
      exact Finset.sum_le_sum (s := twelveDirectionOffStarVertices cfg p c hp)
        (fun q hq => one_le_labelDualMultiplicity_sub_one_of_mem_vertexSet
          (restoredPivotConfiguration cfg p)
          ((mem_twelveDirectionOffStarVertices_iff cfg p c hp q).mp hq).1)

/-- The elementary projective count: after five forced star intersections,
every remaining distinguished-line vertex contributes one unit to the
actual off-star defect. -/
theorem pivotLineVertices_card_sub_five_le_actualOffStarDefect
    {alpha : Type u} [Fintype alpha] [DecidableEq alpha]
    (cfg : Configuration alpha) (p : alpha) (c : DeterminedCircle cfg)
    (hp : p ∈ circleTrace cfg c.1)
    (hcard : (circleTrace cfg c.1).card = 6) :
    (twelveDirectionPivotLineVertices cfg p).card - 5 ≤
      twelveDirectionActualOffStarDefect cfg p c hp := by
  classical
  have hextra : (twelveDirectionExtraPivotVertices cfg p c hp).card =
      (twelveDirectionPivotLineVertices cfg p).card - 5 := by
    unfold twelveDirectionExtraPivotVertices
    rw [Finset.card_sdiff_of_subset
      (twelveDirectionStarPivotIntersections_subset_pivotLineVertices cfg p c hp),
      card_twelveDirectionStarPivotIntersections cfg p c hp hcard]
  calc
    (twelveDirectionPivotLineVertices cfg p).card - 5 =
        (twelveDirectionExtraPivotVertices cfg p c hp).card := hextra.symm
    _ ≤ (twelveDirectionOffStarVertices cfg p c hp).card :=
      Finset.card_le_card
        (twelveDirectionExtraPivotVertices_subset_offStarVertices cfg p c hp)
    _ ≤ twelveDirectionActualOffStarDefect cfg p c hp :=
      card_twelveDirectionOffStarVertices_le_actualDefect cfg p c hp

/-! ## First exact census normalization -/

/-- The distinguished carrier used above is literally the canonical finite
vertex set of the `none` line in the labelled dual arrangement.  This
eliminates a possible ambiguity between the local defect count and the
projective arrangement's per-line vertex census. -/
theorem twelveDirectionPivotLineVertices_eq_lineVertexSet_none
    {alpha : Type u} [Fintype alpha] [DecidableEq alpha]
    (cfg : Configuration alpha) (p : alpha) :
    twelveDirectionPivotLineVertices cfg p =
      (labelDualArrangement (restoredPivotConfiguration cfg p)).lineVertexSet none := by
  classical
  unfold twelveDirectionPivotLineVertices
  unfold FiniteProjectiveLineArrangement.lineVertexSet
  rfl

/-- The five star labels are exactly the five inverted labels of the chosen
circle away from the pivot.  In particular the star in the projective count
has no hidden lines. -/
theorem twelveDirectionStarLabels_eq_someAwaySupport
    {alpha : Type u} [Fintype alpha] [DecidableEq alpha]
    (cfg : Configuration alpha) (p : alpha) (c : DeterminedCircle cfg)
    (hp : p ∈ circleTrace cfg c.1) :
    twelveDirectionStarLabels cfg p c hp =
      someAwaySupport p (circleTrace cfg c.1) := by
  classical
  ext a
  rw [mem_twelveDirectionStarLabels_iff]
  change (labelDualArrangement (restoredPivotConfiguration cfg p)).Incident
      (determinedLineDualVertex (restoredPivotConfiguration cfg p)
        (twelveDirectionRestoredCircleLine cfg p c hp)) a ↔ _
  rw [labelDual_incident_determinedLine_iff]
  rw [← mem_lineSupport]
  rw [show twelveDirectionRestoredCircleLine cfg p c hp =
      blockToRestoredLine cfg p ⟨Sum.inr c, hp⟩ by rfl,
    lineSupport_blockToRestoredLine]
  rfl

/-- The concrete dual-vertex map on determined affine lines is injective.
This is the first lossless leg in turning the distinguished dual-line
vertex census into the original line-through-pivot census. -/
theorem determinedLineDualVertex_injective
    {alpha : Type u} [Fintype alpha] [DecidableEq alpha]
    (cfg : Configuration alpha) :
    Function.Injective (determinedLineDualVertex cfg) := by
  intro L M hLM
  exact (determinedLineProjectiveRealization cfg).projectiveLine_injective hLM

/-- Enumerating the dual vertices by actual determined affine lines is
lossless.  This is the finite converse to
`determinedLineDualVertex_mem_labelDualVertexSet`: every labelled-dual
intersection is the dual point of the line through its two defining labels.
-/
noncomputable def allDeterminedLineDualVertices
    {alpha : Type u} [Fintype alpha] [DecidableEq alpha]
    (cfg : Configuration alpha) : Finset RealProjectivePoint := by
  classical
  exact Finset.univ.image (determinedLineDualVertex cfg)

theorem labelDualVertexSet_eq_allDeterminedLineDualVertices
    {alpha : Type u} [Fintype alpha] [DecidableEq alpha]
    (cfg : Configuration alpha) :
    labelDualVertexSet cfg = allDeterminedLineDualVertices cfg := by
  classical
  ext q
  constructor
  · intro hq
    obtain ⟨a, b, hab, habq⟩ :=
      exists_label_pair_of_mem_labelDualVertexSet cfg hq
    let A : KSubset alpha 2 := ⟨{a, b}, by simp [hab]⟩
    let L : DeterminedLine cfg :=
      ⟨lineOfPair cfg A, lineOfPair_mem_determinedLines cfg A⟩
    have haL : cfg a ∈ L.1 := by
      rw [← mem_lineSupport]
      apply pair_subset_lineSupport cfg A
      simp [A]
    have hbL : cfg b ∈ L.1 := by
      rw [← mem_lineSupport]
      apply pair_subset_lineSupport cfg A
      simp [A]
    have hdualA : (labelDualArrangement cfg).Incident
        (determinedLineDualVertex cfg L) a :=
      (labelDual_incident_determinedLine_iff cfg a L).mpr haL
    have hdualB : (labelDualArrangement cfg).Incident
        (determinedLineDualVertex cfg L) b :=
      (labelDual_incident_determinedLine_iff cfg b L).mpr hbL
    have heq : determinedLineDualVertex cfg L =
        (labelDualArrangement cfg).intersection a b :=
      labelDual_eq_intersection_of_incident cfg hab hdualA hdualB
    unfold allDeterminedLineDualVertices
    exact Finset.mem_image.mpr ⟨L, Finset.mem_univ _, heq.trans habq⟩
  · intro hq
    unfold allDeterminedLineDualVertices at hq
    obtain ⟨L, _hL, hLq⟩ := Finset.mem_image.mp hq
    rw [← hLq]
    exact determinedLineDualVertex_mem_labelDualVertexSet cfg L

/-- Restricting the dual-vertex enumeration to one labelled dual line is
still lossless: its vertices are exactly the determined affine lines
containing the corresponding primal label. -/
noncomputable def determinedLineDualVerticesThroughLabel
    {alpha : Type u} [Fintype alpha] [DecidableEq alpha]
    (cfg : Configuration alpha) (z : alpha) : Finset RealProjectivePoint := by
  classical
  exact (Finset.univ.filter fun L : DeterminedLine cfg => cfg z ∈ L.1).image
    (determinedLineDualVertex cfg)

theorem lineVertexSet_eq_determinedLineDualVerticesThroughLabel
    {alpha : Type u} [Fintype alpha] [DecidableEq alpha]
    (cfg : Configuration alpha) (z : alpha) :
    (labelDualArrangement cfg).lineVertexSet z =
      determinedLineDualVerticesThroughLabel cfg z := by
  classical
  ext q
  constructor
  · intro hq
    obtain ⟨hqVertex, hqInc⟩ :=
      (FiniteProjectiveLineArrangement.mem_lineVertexSet
        (labelDualArrangement cfg) z).mp hq
    change q ∈ labelDualVertexSet cfg at hqVertex
    rw [labelDualVertexSet_eq_allDeterminedLineDualVertices] at hqVertex
    unfold allDeterminedLineDualVertices at hqVertex
    obtain ⟨L, _hL, hLq⟩ := Finset.mem_image.mp hqVertex
    unfold determinedLineDualVerticesThroughLabel
    apply Finset.mem_image.mpr
    refine ⟨L, ?_, hLq⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [← hLq] at hqInc
    exact (labelDual_incident_determinedLine_iff cfg z L).mp hqInc
  · intro hq
    unfold determinedLineDualVerticesThroughLabel at hq
    obtain ⟨L, hL, hLq⟩ := Finset.mem_image.mp hq
    rw [← hLq]
    apply (FiniteProjectiveLineArrangement.mem_lineVertexSet
      (labelDualArrangement cfg) z).mpr
    refine ⟨determinedLineDualVertex_mem_labelDualVertexSet cfg L, ?_⟩
    apply (labelDual_incident_determinedLine_iff cfg z L).mpr
    exact (Finset.mem_filter.mp hL).2

/-- In the restored pivot configuration, a determined line arising from a
block through the pivot contains the restored label `none` exactly when the
original block was a line (rather than a circle). -/
theorem none_mem_lineSupport_blockToRestoredLine_iff_line
    {alpha : Type u} [Fintype alpha] [DecidableEq alpha]
    (cfg : Configuration alpha) (p : alpha) (b : BlockThrough cfg p) :
    none ∈ lineSupport (restoredPivotConfiguration cfg p)
      (blockToRestoredLine cfg p b) ↔
      geometricBlockKind b.1 = .line := by
  rcases b with ⟨b, hbp⟩
  cases b with
  | inl L =>
      rw [lineSupport_blockToRestoredLine]
      simp [restoredCarrierSupport, geometricBlockKind]
  | inr c =>
      rw [lineSupport_blockToRestoredLine]
      simp [restoredCarrierSupport, geometricBlockKind]

/-- Original determined lines through the pivot. -/
abbrev TwelveDirectionLinesThroughPivot
    {alpha : Type u} [Fintype alpha] [DecidableEq alpha]
    (cfg : Configuration alpha) (p : alpha) :=
  {L : DeterminedLine cfg // cfg p ∈ L.1}

/-- Restored determined lines containing the restored pivot label. -/
abbrev TwelveDirectionRestoredLinesThroughNone
    {alpha : Type u} [Fintype alpha] [DecidableEq alpha]
    (cfg : Configuration alpha) (p : alpha) :=
  {D : DeterminedLine (restoredPivotConfiguration cfg p) //
    restoredPivotConfiguration cfg p none ∈ D.1}

/-- The block-restoration equivalence restricts to an equivalence between
original lines through the pivot and restored lines through `none`. -/
noncomputable def twelveDirectionLinesThroughPivotEquivRestoredNone
    {alpha : Type u} [Fintype alpha] [DecidableEq alpha]
    (cfg : Configuration alpha) (p : alpha) :
    TwelveDirectionLinesThroughPivot cfg p ≃
      TwelveDirectionRestoredLinesThroughNone cfg p := by
  classical
  let f : TwelveDirectionLinesThroughPivot cfg p →
      TwelveDirectionRestoredLinesThroughNone cfg p := fun L => by
    let b : BlockThrough cfg p :=
      ⟨Sum.inl L.1, mem_lineSupport.mpr L.2⟩
    refine ⟨blockToRestoredLine cfg p b, ?_⟩
    apply mem_lineSupport.mp
    exact (none_mem_lineSupport_blockToRestoredLine_iff_line cfg p b).mpr rfl
  apply Equiv.ofBijective f
  constructor
  · intro L M hLM
    apply Subtype.ext
    let bL : BlockThrough cfg p :=
      ⟨Sum.inl L.1, mem_lineSupport.mpr L.2⟩
    let bM : BlockThrough cfg p :=
      ⟨Sum.inl M.1, mem_lineSupport.mpr M.2⟩
    have hline0 : (f L).1 = (f M).1 := congrArg Subtype.val hLM
    have hline : blockToRestoredLine cfg p bL = blockToRestoredLine cfg p bM := by
      simpa [f, bL, bM] using hline0
    have hblock : bL = bM := blockToRestoredLine_injective cfg p hline
    have hsum : (Sum.inl L.1 : GeometricBlock cfg) = Sum.inl M.1 :=
      congrArg Subtype.val hblock
    exact Sum.inl_injective hsum
  · intro D
    let b : BlockThrough cfg p := (blockRestoredLineEquiv cfg p).symm D.1
    have hbmap : blockToRestoredLine cfg p b = D.1 :=
      (blockRestoredLineEquiv cfg p).apply_symm_apply D.1
    have hbnone : none ∈ lineSupport (restoredPivotConfiguration cfg p)
        (blockToRestoredLine cfg p b) := by
      rw [hbmap]
      exact mem_lineSupport.mpr D.2
    have hbkind : geometricBlockKind b.1 = .line :=
      (none_mem_lineSupport_blockToRestoredLine_iff_line cfg p b).mp hbnone
    rcases b with ⟨b, hbp⟩
    cases b with
    | inl L =>
        let X : TwelveDirectionLinesThroughPivot cfg p :=
          ⟨L, mem_lineSupport.mp hbp⟩
        refine ⟨X, ?_⟩
        apply Subtype.ext
        change (f X).1 = D.1
        simpa [f, X] using hbmap
    | inr c =>
        simp [geometricBlockKind] at hbkind

/-- Exact cardinal bridge from the distinguished dual-line vertex census to
the original determined lines through the pivot.  The remaining R identity
is now purely the finite partition of these original lines by support size.
-/
theorem card_twelveDirectionPivotLineVertices_eq_card_linesThroughPivot
    {alpha : Type u} [Fintype alpha] [DecidableEq alpha]
    (cfg : Configuration alpha) (p : alpha) :
    (twelveDirectionPivotLineVertices cfg p).card =
      Nat.card (TwelveDirectionLinesThroughPivot cfg p) := by
  classical
  rw [twelveDirectionPivotLineVertices_eq_lineVertexSet_none,
    lineVertexSet_eq_determinedLineDualVerticesThroughLabel]
  unfold determinedLineDualVerticesThroughLabel
  rw [Finset.card_image_iff.mpr (determinedLineDualVertex_injective
    (restoredPivotConfiguration cfg p)).injOn]
  have hsub :
      (Finset.univ.filter fun D : DeterminedLine (restoredPivotConfiguration cfg p) =>
        restoredPivotConfiguration cfg p none ∈ D.1).card =
        Fintype.card (TwelveDirectionRestoredLinesThroughNone cfg p) :=
    (Fintype.card_subtype _).symm
  calc
    (Finset.univ.filter fun D : DeterminedLine (restoredPivotConfiguration cfg p) =>
        restoredPivotConfiguration cfg p none ∈ D.1).card =
      Nat.card (TwelveDirectionRestoredLinesThroughNone cfg p) :=
      hsub.trans Fintype.card_eq_nat_card
    _ = Nat.card (TwelveDirectionLinesThroughPivot cfg p) :=
      Nat.card_congr (twelveDirectionLinesThroughPivotEquivRestoredNone cfg p).symm

/-- The six-block cap bounds every actual determined line by six, including
the elementary two-lines which lie below the cap's threshold. -/
theorem lineSupport_card_le_six_of_blockSizeCap_six
    {alpha : Type u} [Fintype alpha] [DecidableEq alpha]
    (cfg : Configuration alpha)
    (hcap : BlockSizeCap (blockSystem cfg) 6)
    (L : DeterminedLine cfg) : (lineSupport cfg L).card ≤ 6 := by
  by_cases htwo : (lineSupport cfg L).card = 2
  · omega
  have hmin := two_le_lineSupport_card cfg L
  have hthree : 3 ≤ (lineSupport cfg L).card := by omega
  have hle := hcap (Sum.inl L : GeometricBlock cfg) (by
    simpa [blockSystem, geometricBlockSystem, geometricBlockSupport] using hthree)
  simpa [blockSystem, geometricBlockSystem, geometricBlockSupport] using hle

/-- If there are no six-lines globally, no particular determined line has
six labelled support points. -/
theorem lineSupport_card_ne_six_of_lineCount_six_eq_zero
    {alpha : Type u} [Fintype alpha] [DecidableEq alpha]
    (cfg : Configuration alpha)
    (hline : (blockSystem cfg).lineCount 6 = 0)
    (L : DeterminedLine cfg) : (lineSupport cfg L).card ≠ 6 := by
  intro hL
  have hmem : (Sum.inl L : GeometricBlock cfg) ∈
      (blockSystem cfg).lineBlocksOfSize 6 := by
    apply (blockSystem cfg).mem_blocksOfKindSize.mpr
    simpa [blockSystem, geometricBlockSystem, geometricBlockKind,
      geometricBlockSupport] using hL
  have hpos : 0 < (blockSystem cfg).lineCount 6 :=
    Finset.card_pos.mpr ⟨Sum.inl L, hmem⟩
  rw [hline] at hpos
  omega

/-- The support size of every determined line is one of the four sizes
`2,3,4,5` in the selected-six no-six-line branch. -/
theorem lineSupport_card_eq_two_or_three_or_four_or_five_of_twelveDirection
    {alpha : Type u} [Fintype alpha] [DecidableEq alpha]
    (cfg : Configuration alpha)
    (hcap : BlockSizeCap (blockSystem cfg) 6)
    (hline : (blockSystem cfg).lineCount 6 = 0)
    (L : DeterminedLine cfg) :
    (lineSupport cfg L).card = 2 ∨ (lineSupport cfg L).card = 3 ∨
      (lineSupport cfg L).card = 4 ∨ (lineSupport cfg L).card = 5 := by
  have hmin := two_le_lineSupport_card cfg L
  have hmax := lineSupport_card_le_six_of_blockSizeCap_six cfg hcap L
  have hne := lineSupport_card_ne_six_of_lineCount_six_eq_zero cfg hline L
  omega

/-- The four finite support-size layers of original lines through the
pivot.  This is deliberately a type sum, so its cardinality is exactly the
sum of the four line degrees once it is shown to enumerate every line. -/
abbrev TwelveDirectionLineSizeSource
    {alpha : Type u} [Fintype alpha] [DecidableEq alpha]
    (cfg : Configuration alpha) (p : alpha) :=
  DeterminedLineOfSizeThrough cfg p 2 ⊕
    DeterminedLineOfSizeThrough cfg p 3 ⊕
      DeterminedLineOfSizeThrough cfg p 4 ⊕
        DeterminedLineOfSizeThrough cfg p 5

/-- Forget the size tag of one of the four source layers. -/
def twelveDirectionLineSizeSourceToLinesThroughPivot
    {alpha : Type u} [Fintype alpha] [DecidableEq alpha]
    (cfg : Configuration alpha) (p : alpha) :
    TwelveDirectionLineSizeSource cfg p → TwelveDirectionLinesThroughPivot cfg p
  | .inl L => ⟨L.1.1, mem_lineSupport.mp L.2⟩
  | .inr (.inl L) => ⟨L.1.1, mem_lineSupport.mp L.2⟩
  | .inr (.inr (.inl L)) => ⟨L.1.1, mem_lineSupport.mp L.2⟩
  | .inr (.inr (.inr L)) => ⟨L.1.1, mem_lineSupport.mp L.2⟩

/-- The four size layers cover every actual determined line through the
pivot in the capped no-six-line branch.  The next step only has to prove
that their forgetful map is injective. -/
theorem twelveDirectionLineSizeSourceToLinesThroughPivot_surjective
    {alpha : Type u} [Fintype alpha] [DecidableEq alpha]
    (cfg : Configuration alpha) (p : alpha)
    (hcap : BlockSizeCap (blockSystem cfg) 6)
    (hline : (blockSystem cfg).lineCount 6 = 0) :
    Function.Surjective
      (twelveDirectionLineSizeSourceToLinesThroughPivot cfg p) := by
  intro L
  rcases lineSupport_card_eq_two_or_three_or_four_or_five_of_twelveDirection
    cfg hcap hline L.1 with h2 | h3 | h4 | h5
  · let X : DeterminedLineOfSizeThrough cfg p 2 := ⟨⟨L.1, h2⟩, mem_lineSupport.mpr L.2⟩
    exact ⟨.inl X, by rfl⟩
  · let X : DeterminedLineOfSizeThrough cfg p 3 := ⟨⟨L.1, h3⟩, mem_lineSupport.mpr L.2⟩
    exact ⟨.inr (.inl X), by rfl⟩
  · let X : DeterminedLineOfSizeThrough cfg p 4 := ⟨⟨L.1, h4⟩, mem_lineSupport.mpr L.2⟩
    exact ⟨.inr (.inr (.inl X)), by rfl⟩
  · let X : DeterminedLineOfSizeThrough cfg p 5 := ⟨⟨L.1, h5⟩, mem_lineSupport.mpr L.2⟩
    exact ⟨.inr (.inr (.inr X)), by rfl⟩

/-- Numerical tag of a line-size source summand. -/
def twelveDirectionLineSizeSourceSize
    {alpha : Type u} [Fintype alpha] [DecidableEq alpha]
    {cfg : Configuration alpha} {p : alpha} :
    TwelveDirectionLineSizeSource cfg p → Nat
  | .inl _ => 2
  | .inr (.inl _) => 3
  | .inr (.inr (.inl _)) => 4
  | .inr (.inr (.inr _)) => 5

theorem lineSupport_card_twelveDirectionLineSizeSourceToLinesThroughPivot
    {alpha : Type u} [Fintype alpha] [DecidableEq alpha]
    (cfg : Configuration alpha) (p : alpha)
    (X : TwelveDirectionLineSizeSource cfg p) :
    (lineSupport cfg
      (twelveDirectionLineSizeSourceToLinesThroughPivot cfg p X).1).card =
      twelveDirectionLineSizeSourceSize X := by
  cases X with
  | inl X => exact X.1.2
  | inr X =>
      cases X with
      | inl X => exact X.1.2
      | inr X =>
          cases X with
          | inl X => exact X.1.2
          | inr X => exact X.1.2

/-- Forgetting the four size tags is injective: equality of the underlying
line forces equality of its support cardinality, hence equality of the
summand, and then equality of the tagged line itself. -/
theorem twelveDirectionLineSizeSourceToLinesThroughPivot_injective
    {alpha : Type u} [Fintype alpha] [DecidableEq alpha]
    (cfg : Configuration alpha) (p : alpha) :
    Function.Injective (twelveDirectionLineSizeSourceToLinesThroughPivot cfg p) := by
  intro X Y hXY
  have hline :
      (twelveDirectionLineSizeSourceToLinesThroughPivot cfg p X).1 =
        (twelveDirectionLineSizeSourceToLinesThroughPivot cfg p Y).1 :=
    congrArg Subtype.val hXY
  have hsize : twelveDirectionLineSizeSourceSize X =
      twelveDirectionLineSizeSourceSize Y := by
    have hX := lineSupport_card_twelveDirectionLineSizeSourceToLinesThroughPivot
      cfg p X
    have hY := lineSupport_card_twelveDirectionLineSizeSourceToLinesThroughPivot
      cfg p Y
    rw [hline] at hX
    exact hX.symm.trans hY
  cases X with
  | inl X =>
      cases Y with
      | inl Y =>
          have hXY' : X = Y := by
            apply Subtype.ext
            apply Subtype.ext
            exact hline
          simpa [hXY']
      | inr Y =>
          cases Y with
          | inl Y => simp [twelveDirectionLineSizeSourceSize] at hsize
          | inr Y =>
              cases Y <;> simp [twelveDirectionLineSizeSourceSize] at hsize
  | inr X =>
      cases X with
      | inl X =>
          cases Y with
          | inl Y => simp [twelveDirectionLineSizeSourceSize] at hsize
          | inr Y =>
              cases Y with
              | inl Y =>
                  have hXY' : X = Y := by
                    apply Subtype.ext
                    apply Subtype.ext
                    exact hline
                  simpa [hXY']
              | inr Y =>
                  cases Y <;> simp [twelveDirectionLineSizeSourceSize] at hsize
      | inr X =>
          cases X with
          | inl X =>
              cases Y with
              | inl Y => simp [twelveDirectionLineSizeSourceSize] at hsize
              | inr Y =>
                  cases Y with
                  | inl Y => simp [twelveDirectionLineSizeSourceSize] at hsize
                  | inr Y =>
                      cases Y with
                      | inl Y =>
                          have hXY' : X = Y := by
                            apply Subtype.ext
                            apply Subtype.ext
                            exact hline
                          simpa [hXY']
                      | inr Y => simp [twelveDirectionLineSizeSourceSize] at hsize
          | inr X =>
              cases Y with
              | inl Y => simp [twelveDirectionLineSizeSourceSize] at hsize
              | inr Y =>
                  cases Y with
                  | inl Y => simp [twelveDirectionLineSizeSourceSize] at hsize
                  | inr Y =>
                      cases Y with
                      | inl Y => simp [twelveDirectionLineSizeSourceSize] at hsize
                      | inr Y =>
                          have hXY' : X = Y := by
                            apply Subtype.ext
                            apply Subtype.ext
                            exact hline
                          simpa [hXY']

/-- Exact enumeration of the lines through the pivot by their four possible
support sizes. -/
noncomputable def twelveDirectionLineSizeSourceEquivLinesThroughPivot
    {alpha : Type u} [Fintype alpha] [DecidableEq alpha]
    (cfg : Configuration alpha) (p : alpha)
    (hcap : BlockSizeCap (blockSystem cfg) 6)
    (hline : (blockSystem cfg).lineCount 6 = 0) :
    TwelveDirectionLineSizeSource cfg p ≃
      TwelveDirectionLinesThroughPivot cfg p :=
  Equiv.ofBijective (twelveDirectionLineSizeSourceToLinesThroughPivot cfg p)
    ⟨twelveDirectionLineSizeSourceToLinesThroughPivot_injective cfg p,
      twelveDirectionLineSizeSourceToLinesThroughPivot_surjective cfg p hcap hline⟩

/-- Exact interpretation of the distinguished-line vertex count as the
local original line census `ℓ₂+ℓ₃+ℓ₄+ℓ₅`. -/
theorem card_twelveDirectionPivotLineVertices_eq_distinguishedLineVertices
    {alpha : Type u} [Fintype alpha] [DecidableEq alpha]
    (cfg : Configuration alpha) (p : alpha)
    (hcap : BlockSizeCap (blockSystem cfg) 6)
    (hline : (blockSystem cfg).lineCount 6 = 0) :
    (twelveDirectionPivotLineVertices cfg p).card =
      (blockSystem cfg).lineDegree 2 p + (blockSystem cfg).lineDegree 3 p +
        (blockSystem cfg).lineDegree 4 p + (blockSystem cfg).lineDegree 5 p := by
  rw [card_twelveDirectionPivotLineVertices_eq_card_linesThroughPivot]
  calc
    Nat.card (TwelveDirectionLinesThroughPivot cfg p) =
        Nat.card (TwelveDirectionLineSizeSource cfg p) :=
      Nat.card_congr
        (twelveDirectionLineSizeSourceEquivLinesThroughPivot cfg p hcap hline).symm
    _ = Fintype.card (TwelveDirectionLineSizeSource cfg p) :=
      Nat.card_eq_fintype_card
    _ = Fintype.card (DeterminedLineOfSizeThrough cfg p 2) +
        Fintype.card (DeterminedLineOfSizeThrough cfg p 3) +
          Fintype.card (DeterminedLineOfSizeThrough cfg p 4) +
             Fintype.card (DeterminedLineOfSizeThrough cfg p 5) := by
      simp [TwelveDirectionLineSizeSource, Fintype.card_sum, Nat.add_assoc]
    _ = (blockSystem cfg).lineDegree 2 p + (blockSystem cfg).lineDegree 3 p +
          (blockSystem cfg).lineDegree 4 p + (blockSystem cfg).lineDegree 5 p := by
      rw [← lineDegree_eq_card_determinedLineOfSizeThrough,
        ← lineDegree_eq_card_determinedLineOfSizeThrough,
        ← lineDegree_eq_card_determinedLineOfSizeThrough,
        ← lineDegree_eq_card_determinedLineOfSizeThrough]

/-! ## The genuine nonnegative projective gap -/

/-- The projective off-star gap formed from the actual dual arrangement.
Unlike the local arithmetic abbreviation in `TwelveDirectionDefectDerivation`,
this definition is directly a finite sum of genuine arrangement vertices. -/
noncomputable def twelveDirectionActualEqualityGap
    {alpha : Type u} [Fintype alpha] [DecidableEq alpha]
    (cfg : Configuration alpha) (p : alpha) (c : DeterminedCircle cfg)
    (hp : p ∈ circleTrace cfg c.1) : Int :=
  (twelveDirectionActualOffStarDefect cfg p c hp : Int) -
    ((twelveDirectionPivotLineVertices cfg p).card : Int) + 5

/-- The star-intersection injection already proves the actual off-star gap
is nonnegative, without any arithmetic-row assumption. -/
theorem twelveDirectionActualEqualityGap_nonneg
    {alpha : Type u} [Fintype alpha] [DecidableEq alpha]
    (cfg : Configuration alpha) (p : alpha) (c : DeterminedCircle cfg)
    (hp : p ∈ circleTrace cfg c.1)
    (hcard : (circleTrace cfg c.1).card = 6) :
    0 ≤ twelveDirectionActualEqualityGap cfg p c hp := by
  have h := pivotLineVertices_card_sub_five_le_actualOffStarDefect
    cfg p c hp hcard
  simp only [twelveDirectionActualEqualityGap]
  omega

/-- After the exact R census, the elementary topological gap is expressed
with the same distinguished-line term as the local direction-defect row.
Only the exact identification of the defect sum with the `t₂,…,t₅` row
remains before this becomes `twelveDirectionEqualityGap`. -/
theorem twelveDirectionActualEqualityGap_eq_actualDefect_sub_distinguished
    {alpha : Type u} [Fintype alpha] [DecidableEq alpha]
    (cfg : Configuration alpha) (p : alpha) (c : DeterminedCircle cfg)
    (hp : p ∈ circleTrace cfg c.1)
    (hcap : BlockSizeCap (blockSystem cfg) 6)
    (hline : (blockSystem cfg).lineCount 6 = 0) :
    twelveDirectionActualEqualityGap cfg p c hp =
      (twelveDirectionActualOffStarDefect cfg p c hp : Int) -
        (twelveDirectionDistinguishedLineVertices (blockSystem cfg) p - 5) := by
  simp only [twelveDirectionActualEqualityGap]
  rw [card_twelveDirectionPivotLineVertices_eq_distinguishedLineVertices
    cfg p hcap hline]
  simp only [twelveDirectionDistinguishedLineVertices]
  omega

/-! ## Exact dual multiplicity profile -/

/-- Actual labelled-dual vertices of one multiplicity.  The forthcoming
defect-profile identification is expressed solely through this concrete
finite set. -/
noncomputable def twelveDirectionDualMultiplicityVertices
    {alpha : Type u} [Fintype alpha] [DecidableEq alpha]
    (cfg : Configuration alpha) (s : Nat) : Finset RealProjectivePoint := by
  classical
  exact (labelDualVertexSet cfg).filter fun q =>
    (labelDualArrangement cfg).multiplicity q = s

theorem mem_twelveDirectionDualMultiplicityVertices_iff
    {alpha : Type u} [Fintype alpha] [DecidableEq alpha]
    (cfg : Configuration alpha) (s : Nat) (q : RealProjectivePoint) :
    q ∈ twelveDirectionDualMultiplicityVertices cfg s ↔
      q ∈ labelDualVertexSet cfg ∧
        (labelDualArrangement cfg).multiplicity q = s := by
  classical
  simp [twelveDirectionDualMultiplicityVertices]

/-- A determined line of size `s` gives a vertex of actual dual
multiplicity `s`. -/
noncomputable def determinedLineDualVertexOfSize
    {alpha : Type u} [Fintype alpha] [DecidableEq alpha]
    (cfg : Configuration alpha) (s : Nat) :
    DeterminedLineOfSize cfg s →
      {q : RealProjectivePoint // q ∈ twelveDirectionDualMultiplicityVertices cfg s} :=
  fun L => ⟨determinedLineDualVertex cfg L.1,
    (mem_twelveDirectionDualMultiplicityVertices_iff cfg s
      (determinedLineDualVertex cfg L.1)).mpr ⟨
        determinedLineDualVertex_mem_labelDualVertexSet cfg L.1, by
          rw [labelDual_multiplicity_determinedLine]
          exact L.2⟩⟩

theorem determinedLineDualVertexOfSize_injective
    {alpha : Type u} [Fintype alpha] [DecidableEq alpha]
    (cfg : Configuration alpha) (s : Nat) :
    Function.Injective (determinedLineDualVertexOfSize cfg s) := by
  intro L M hLM
  apply Subtype.ext
  apply determinedLineDualVertex_injective cfg
  exact congrArg Subtype.val hLM

/-- Every actual dual vertex of multiplicity `s` is the dual point of one
and only one actual determined line of support size `s`. -/
theorem determinedLineDualVertexOfSize_surjective
    {alpha : Type u} [Fintype alpha] [DecidableEq alpha]
    (cfg : Configuration alpha) (s : Nat) :
    Function.Surjective (determinedLineDualVertexOfSize cfg s) := by
  classical
  intro q
  obtain ⟨hqVertex, hqMult⟩ :=
    (mem_twelveDirectionDualMultiplicityVertices_iff cfg s q.1).mp q.2
  rw [labelDualVertexSet_eq_allDeterminedLineDualVertices] at hqVertex
  unfold allDeterminedLineDualVertices at hqVertex
  obtain ⟨L, _hL, hLq⟩ := Finset.mem_image.mp hqVertex
  let M : DeterminedLineOfSize cfg s := ⟨L, by
    rw [← hLq] at hqMult
    rw [labelDual_multiplicity_determinedLine] at hqMult
    exact hqMult⟩
  refine ⟨M, ?_⟩
  apply Subtype.ext
  exact hLq

noncomputable def determinedLineOfSizeEquivDualMultiplicityVertices
    {alpha : Type u} [Fintype alpha] [DecidableEq alpha]
    (cfg : Configuration alpha) (s : Nat) :
    DeterminedLineOfSize cfg s ≃
      {q : RealProjectivePoint // q ∈ twelveDirectionDualMultiplicityVertices cfg s} :=
  Equiv.ofBijective (determinedLineDualVertexOfSize cfg s)
    ⟨determinedLineDualVertexOfSize_injective cfg s,
      determinedLineDualVertexOfSize_surjective cfg s⟩

/-- Exact cardinal form of the actual dual multiplicity census. -/
theorem card_twelveDirectionDualMultiplicityVertices_eq_lineCount
    {alpha : Type u} [Fintype alpha] [DecidableEq alpha]
    (cfg : Configuration alpha) (s : Nat) :
    (twelveDirectionDualMultiplicityVertices cfg s).card =
      (blockSystem cfg).lineCount s := by
  rw [lineCount_eq_card_determinedLineOfSize]
  calc
    (twelveDirectionDualMultiplicityVertices cfg s).card =
        Fintype.card {q : RealProjectivePoint //
          q ∈ twelveDirectionDualMultiplicityVertices cfg s} :=
      (Fintype.card_coe _).symm
    _ = Fintype.card (DeterminedLineOfSize cfg s) :=
      Fintype.card_congr
        (determinedLineOfSizeEquivDualMultiplicityVertices cfg s).symm

/-- Regroup the total concrete dual defect by vertex multiplicity whenever
the restored arrangement has no multiplicity above five.  This is a plain
finite fibre count over the actual labelled-dual vertex set. -/
theorem twelveDirectionTotalDualDefect_eq_profile_sum
    {alpha : Type u} [Fintype alpha] [DecidableEq alpha]
    (cfg : Configuration alpha) (p : alpha)
    (hmult : ∀ q ∈ labelDualVertexSet (restoredPivotConfiguration cfg p),
      (labelDualArrangement (restoredPivotConfiguration cfg p)).multiplicity q ≤ 5) :
    twelveDirectionTotalDualDefect cfg p =
      ∑ s ∈ Finset.Icc 2 5,
        (s - 1) * (twelveDirectionDualMultiplicityVertices
          (restoredPivotConfiguration cfg p) s).card := by
  classical
  let A := labelDualArrangement (restoredPivotConfiguration cfg p)
  let V := labelDualVertexSet (restoredPivotConfiguration cfg p)
  have hmaps : ∀ q ∈ V, A.multiplicity q ∈ Finset.Icc 2 5 := by
    intro q hq
    have hq' : q ∈ labelDualVertexSet (restoredPivotConfiguration cfg p) := by
      simpa only [V] using hq
    have hlow : 2 ≤ A.multiplicity q := by
      have h := one_le_labelDualMultiplicity_sub_one_of_mem_vertexSet
        (restoredPivotConfiguration cfg p) hq'
      change 1 ≤ A.multiplicity q - 1 at h
      omega
    have hupp : A.multiplicity q ≤ 5 := by
      simpa only [A] using hmult q hq'
    exact Finset.mem_Icc.mpr ⟨hlow, hupp⟩
  have hgroup := Finset.sum_fiberwise_of_maps_to hmaps
    (fun q : RealProjectivePoint => A.multiplicity q - 1)
  have htotal : (∑ q ∈ V, (A.multiplicity q - 1)) =
      ∑ s ∈ Finset.Icc 2 5,
        (s - 1) * (twelveDirectionDualMultiplicityVertices
          (restoredPivotConfiguration cfg p) s).card := by
    calc
      (∑ q ∈ V, (A.multiplicity q - 1)) =
          ∑ s ∈ Finset.Icc 2 5,
            ∑ q ∈ V.filter fun q => A.multiplicity q = s,
              (A.multiplicity q - 1) := hgroup.symm
      _ = ∑ s ∈ Finset.Icc 2 5,
          (s - 1) * (twelveDirectionDualMultiplicityVertices
            (restoredPivotConfiguration cfg p) s).card := by
        apply Finset.sum_congr rfl
        intro s hs
        calc
          (∑ q ∈ V.filter fun q => A.multiplicity q = s,
              (A.multiplicity q - 1)) =
              (V.filter fun q => A.multiplicity q = s).card * (s - 1) := by
            apply Finset.sum_const_nat
            intro q hq
            exact congrArg (fun n : Nat => n - 1)
              (Finset.mem_filter.mp hq).2
          _ = (s - 1) * (V.filter fun q => A.multiplicity q = s).card := by
            rw [Nat.mul_comm]
          _ = (s - 1) * (twelveDirectionDualMultiplicityVertices
            (restoredPivotConfiguration cfg p) s).card := by
            congr 1
  simpa only [twelveDirectionTotalDualDefect, A, V] using htotal

/-- A size-six cap, together with the no-six-line branch, bounds every
actual multiplicity in the restored labelled-dual arrangement by five.
This is the exact hypothesis needed by the finite profile regrouping above. -/
theorem labelDualMultiplicity_restored_le_five_of_blockSizeCap_of_lineCount_six_eq_zero
    {alpha : Type u} [Fintype alpha] [DecidableEq alpha]
    (cfg : Configuration alpha) (p : alpha)
    (hcap : BlockSizeCap (blockSystem cfg) 6)
    (hline : (blockSystem cfg).lineCount 6 = 0)
    {q : RealProjectivePoint}
    (hq : q ∈ labelDualVertexSet (restoredPivotConfiguration cfg p)) :
    (labelDualArrangement (restoredPivotConfiguration cfg p)).multiplicity q ≤ 5 := by
  classical
  rw [labelDualVertexSet_eq_allDeterminedLineDualVertices] at hq
  unfold allDeterminedLineDualVertices at hq
  obtain ⟨L, _hL, hLq⟩ := Finset.mem_image.mp hq
  rw [← hLq, labelDual_multiplicity_determinedLine]
  obtain ⟨b, hb⟩ := (blockRestoredLineEquiv cfg p).surjective L
  rw [← hb]
  change (lineSupport (restoredPivotConfiguration cfg p)
    (blockToRestoredLine cfg p b)).card ≤ 5
  rcases b with ⟨b, hbp⟩
  cases b with
  | inl L =>
      have hcard := card_lineSupport_blockToRestoredLine cfg p
        (⟨.inl L, hbp⟩ : BlockThrough cfg p)
      change (lineSupport (restoredPivotConfiguration cfg p)
        (blockToRestoredLine cfg p ⟨.inl L, hbp⟩)).card =
          (lineSupport cfg L).card at hcard
      by_cases hthree : 3 ≤ (lineSupport cfg L).card
      · have hle : (lineSupport cfg L).card ≤ 6 := by
          apply hcap (.inl L)
          simpa [geometricBlockSupport] using hthree
        have hne : (lineSupport cfg L).card ≠ 6 := by
          intro hsize
          have hmem : Sum.inl L ∈ (blockSystem cfg).lineBlocksOfSize 6 := by
            apply (blockSystem cfg).mem_blocksOfKindSize.mpr
            exact ⟨rfl, by simpa [geometricBlockSupport] using hsize⟩
          have hpos : 0 < (blockSystem cfg).lineCount 6 :=
            Finset.card_pos.mpr ⟨Sum.inl L, hmem⟩
          omega
        have hsmall : (lineSupport cfg L).card ≤ 5 := by omega
        exact hcard.trans_le hsmall
      · have hsmall : (lineSupport cfg L).card ≤ 5 := by omega
        exact hcard.trans_le hsmall
  | inr c =>
      have hcard := card_lineSupport_blockToRestoredLine cfg p
        (⟨.inr c, hbp⟩ : BlockThrough cfg p)
      have hmin := Erdos506.V3.circleSupport_card_ge_three cfg c
      have hle : (circleTrace cfg c.1).card ≤ 6 := by
        apply hcap (.inr c)
        simpa [geometricBlockSupport] using hmin
      change (lineSupport (restoredPivotConfiguration cfg p)
        (blockToRestoredLine cfg p ⟨.inr c, hbp⟩)).card =
          (circleTrace cfg c.1).card - 1 at hcard
      have hsmall : (circleTrace cfg c.1).card - 1 ≤ 5 := by omega
      exact hcard.trans_le hsmall

/-! ## Restored inversion dictionary by multiplicity -/

/-- The two original sources of restored lines of a given size. -/
abbrev TwelveDirectionRestoredLineSourceAtSize
    {alpha : Type u} [Fintype alpha] [DecidableEq alpha]
    (cfg : Configuration alpha) (p : alpha) (s : Nat) :=
  TaggedLineAtSize cfg p s ⊕ TaggedCircleAtSize cfg p (s + 1)

/-- First restrict the original block/restored-line bijection by the
restored line support size. -/
def twelveDirectionRestoredLineSourceBlockEquivAtSize
    {alpha : Type u} [Fintype alpha] [DecidableEq alpha]
    (cfg : Configuration alpha) (p : alpha) (s : Nat) :
    TwelveDirectionRestoredLineSourceAtSize cfg p s ≃
      {b : BlockThrough cfg p //
        (lineSupport (restoredPivotConfiguration cfg p)
          (blockToRestoredLine cfg p b)).card = s} where
  toFun x := by
    cases x with
    | inl x =>
        rcases x with ⟨b, hbkind, hbsize, hbp⟩
        cases b with
        | inl L =>
            let bt : BlockThrough cfg p := ⟨.inl L, hbp⟩
            refine ⟨bt, ?_⟩
            have hcard := card_lineSupport_blockToRestoredLine cfg p bt
            simpa [bt, geometricBlockSupport] using hcard.trans hbsize
        | inr c => cases hbkind
    | inr x =>
        rcases x with ⟨b, hbkind, hbsize, hbp⟩
        cases b with
        | inl L => cases hbkind
        | inr c =>
            let bt : BlockThrough cfg p := ⟨.inr c, hbp⟩
            refine ⟨bt, ?_⟩
            have hcard := card_lineSupport_blockToRestoredLine cfg p bt
            have hmin := Erdos506.V3.circleSupport_card_ge_three cfg c
            change (circleTrace cfg c.1).card = s + 1 at hbsize
            change (lineSupport (restoredPivotConfiguration cfg p)
              (blockToRestoredLine cfg p bt)).card =
                (circleTrace cfg c.1).card - 1 at hcard
            have htrace : (circleTrace cfg c.1).card - 1 = s := by
              omega
            exact hcard.trans htrace
  invFun x := by
    rcases x with ⟨b, hbsize⟩
    rcases b with ⟨b, hbp⟩
    cases b with
    | inl L =>
        let bt : BlockThrough cfg p := ⟨.inl L, hbp⟩
        have hcard := card_lineSupport_blockToRestoredLine cfg p bt
        rw [hcard] at hbsize
        exact .inl ⟨.inl L, rfl, hbsize, hbp⟩
    | inr c =>
        let bt : BlockThrough cfg p := ⟨.inr c, hbp⟩
        have hcard := card_lineSupport_blockToRestoredLine cfg p bt
        have hmin := Erdos506.V3.circleSupport_card_ge_three cfg c
        change (lineSupport (restoredPivotConfiguration cfg p)
          (blockToRestoredLine cfg p bt)).card =
            (circleTrace cfg c.1).card - 1 at hcard
        rw [hcard] at hbsize
        have htrace : (circleTrace cfg c.1).card = s + 1 := by omega
        exact .inr ⟨.inr c, rfl, htrace, hbp⟩
  left_inv x := by
    cases x with
    | inl x =>
        rcases x with ⟨b, hbkind, hbsize, hbp⟩
        cases b with
        | inl L => rfl
        | inr c => cases hbkind
    | inr x =>
        rcases x with ⟨b, hbkind, hbsize, hbp⟩
        cases b with
        | inl L => cases hbkind
        | inr c => rfl
  right_inv x := by
    rcases x with ⟨b, hbsize⟩
    rcases b with ⟨b, hbp⟩
    cases b <;> rfl

/-- Exact source equivalence for every restored line size. -/
noncomputable def twelveDirectionRestoredLineSourceEquivAtSize
    {alpha : Type u} [Fintype alpha] [DecidableEq alpha]
    (cfg : Configuration alpha) (p : alpha) (s : Nat) :
    TwelveDirectionRestoredLineSourceAtSize cfg p s ≃
      DeterminedLineOfSize (restoredPivotConfiguration cfg p) s :=
  (twelveDirectionRestoredLineSourceBlockEquivAtSize cfg p s).trans
    ((blockRestoredLineEquiv cfg p).subtypeEquiv fun _b => Iff.rfl)

/-- The complete restored multiplicity dictionary: an `s`-fold dual vertex
comes from a line `s` through the pivot or a circle `s+1` through it. -/
theorem lineCount_restoredPivotConfiguration_eq_lineDegree_add_circleDegree_succ
    {alpha : Type u} [Fintype alpha] [DecidableEq alpha]
    (cfg : Configuration alpha) (p : alpha) (s : Nat) :
    (blockSystem (restoredPivotConfiguration cfg p)).lineCount s =
      (blockSystem cfg).lineDegree s p +
        (blockSystem cfg).circleDegree (s + 1) p := by
  rw [lineCount_eq_card_determinedLineOfSize]
  calc
    Fintype.card (DeterminedLineOfSize (restoredPivotConfiguration cfg p) s) =
        Fintype.card (TwelveDirectionRestoredLineSourceAtSize cfg p s) :=
      (Fintype.card_congr
        (twelveDirectionRestoredLineSourceEquivAtSize cfg p s)).symm
    _ = Fintype.card (TaggedLineAtSize cfg p s) +
        Fintype.card (TaggedCircleAtSize cfg p (s + 1)) := by
      simp [TwelveDirectionRestoredLineSourceAtSize]
    _ = (blockSystem cfg).lineDegree s p +
        (blockSystem cfg).circleDegree (s + 1) p := by
      rw [← lineDegree_eq_card_taggedLineAtSize,
        ← circleDegree_eq_card_taggedCircleAtSize]

/-- The concrete dual multiplicity profile agrees with the four local
inversion-dictionary expressions `t₂,…,t₅`. -/
theorem card_twelveDirectionDualMultiplicityVertices_restored_eq_twelveDirectionT2
    {alpha : Type u} [Fintype alpha] [DecidableEq alpha]
    (cfg : Configuration alpha) (p : alpha) :
    (twelveDirectionDualMultiplicityVertices (restoredPivotConfiguration cfg p) 2).card =
      twelveDirectionT2 (blockSystem cfg) p := by
  rw [card_twelveDirectionDualMultiplicityVertices_eq_lineCount,
    lineCount_restoredPivotConfiguration_eq_lineDegree_add_circleDegree_succ]
  simp only [twelveDirectionT2]
  rw [blockDegree_eq_lineDegree_add_circleDegree]
  norm_num
  omega

theorem card_twelveDirectionDualMultiplicityVertices_restored_eq_twelveDirectionT3
    {alpha : Type u} [Fintype alpha] [DecidableEq alpha]
    (cfg : Configuration alpha) (p : alpha) :
    (twelveDirectionDualMultiplicityVertices (restoredPivotConfiguration cfg p) 3).card =
      twelveDirectionT3 (blockSystem cfg) p := by
  rw [card_twelveDirectionDualMultiplicityVertices_eq_lineCount,
    lineCount_restoredPivotConfiguration_eq_lineDegree_add_circleDegree_succ]
  simp only [twelveDirectionT3]
  rw [blockDegree_eq_lineDegree_add_circleDegree]
  norm_num
  omega

theorem card_twelveDirectionDualMultiplicityVertices_restored_eq_twelveDirectionT4
    {alpha : Type u} [Fintype alpha] [DecidableEq alpha]
    (cfg : Configuration alpha) (p : alpha) :
    (twelveDirectionDualMultiplicityVertices (restoredPivotConfiguration cfg p) 4).card =
      twelveDirectionT4 (blockSystem cfg) p := by
  rw [card_twelveDirectionDualMultiplicityVertices_eq_lineCount,
    lineCount_restoredPivotConfiguration_eq_lineDegree_add_circleDegree_succ]
  simp only [twelveDirectionT4]
  rw [blockDegree_eq_lineDegree_add_circleDegree]
  norm_num
  omega

theorem card_twelveDirectionDualMultiplicityVertices_restored_eq_twelveDirectionT5
    {alpha : Type u} [Fintype alpha] [DecidableEq alpha]
    (cfg : Configuration alpha) (p : alpha)
    (hline6 : (blockSystem cfg).lineDegree 6 p = 0) :
    (twelveDirectionDualMultiplicityVertices (restoredPivotConfiguration cfg p) 5).card =
      twelveDirectionT5 (blockSystem cfg) p := by
  rw [card_twelveDirectionDualMultiplicityVertices_eq_lineCount,
    lineCount_restoredPivotConfiguration_eq_lineDegree_add_circleDegree_succ]
  simp only [twelveDirectionT5]
  rw [blockDegree_eq_lineDegree_add_circleDegree]
  norm_num
  rw [hline6]
  omega

/-- The global no-six-line branch also removes every local six-line
incidence at the chosen pivot.  Keeping this elementary filter argument
local avoids importing an unrelated numerical case split merely to use the
size-five profile dictionary. -/
theorem twelveDirection_lineDegree_six_eq_zero_of_lineCount_six_eq_zero
    {alpha : Type u} [Fintype alpha] [DecidableEq alpha]
    (cfg : Configuration alpha) (p : alpha)
    (hline : (blockSystem cfg).lineCount 6 = 0) :
    (blockSystem cfg).lineDegree 6 p = 0 := by
  change ((blockSystem cfg).lineBlocksOfSize 6).card = 0 at hline
  change (((blockSystem cfg).lineBlocksOfSize 6).filter
    fun b => p ∈ (blockSystem cfg).support b).card = 0
  have hle := Finset.card_filter_le
    ((blockSystem cfg).lineBlocksOfSize 6)
    (fun b => p ∈ (blockSystem cfg).support b)
  omega

/-- In the global no-six-line branch the final restored profile entry is
also exactly the local `t₅` expression. -/
theorem card_twelveDirectionDualMultiplicityVertices_restored_eq_twelveDirectionT5_of_lineCount_six_eq_zero
    {alpha : Type u} [Fintype alpha] [DecidableEq alpha]
    (cfg : Configuration alpha) (p : alpha)
    (hline : (blockSystem cfg).lineCount 6 = 0) :
    (twelveDirectionDualMultiplicityVertices (restoredPivotConfiguration cfg p) 5).card =
      twelveDirectionT5 (blockSystem cfg) p := by
  apply card_twelveDirectionDualMultiplicityVertices_restored_eq_twelveDirectionT5
  exact twelveDirection_lineDegree_six_eq_zero_of_lineCount_six_eq_zero
    cfg p hline

/-! ## Closing the actual/arithmetic defect dictionary -/

/-- The concrete off-star sum is exactly the arithmetic defect appearing in
the twelve-point direction row.  All terms are derived from the actual dual
arrangement; the constant `39` is the five-arm count proved above. -/
theorem twelveDirectionActualOffStarDefect_eq_twelveDirectionOffStarDefect
    {alpha : Type u} [Fintype alpha] [DecidableEq alpha]
    (cfg : Configuration alpha) (p : alpha) (c : DeterminedCircle cfg)
    (hp : p ∈ circleTrace cfg c.1)
    (hpoints : Fintype.card alpha = 12)
    (hcircle : (circleTrace cfg c.1).card = 6)
    (hcap : BlockSizeCap (blockSystem cfg) 6)
    (hline : (blockSystem cfg).lineCount 6 = 0) :
    (twelveDirectionActualOffStarDefect cfg p c hp : Int) =
      twelveDirectionOffStarDefect (blockSystem cfg) p := by
  classical
  have hmult : ∀ q ∈ labelDualVertexSet (restoredPivotConfiguration cfg p),
      (labelDualArrangement (restoredPivotConfiguration cfg p)).multiplicity q ≤ 5 := by
    intro q hq
    exact labelDualMultiplicity_restored_le_five_of_blockSizeCap_of_lineCount_six_eq_zero
      cfg p hcap hline hq
  have htotal := twelveDirectionTotalDualDefect_eq_profile_sum cfg p hmult
  have hIcc : Finset.Icc 2 5 = {2, 3, 4, 5} := by
    ext s
    simp only [Finset.mem_Icc, Finset.mem_insert, Finset.mem_singleton]
    omega
  rw [hIcc] at htotal
  norm_num [Finset.sum_insert, Finset.sum_singleton] at htotal
  have htotalInt : (twelveDirectionTotalDualDefect cfg p : Int) =
      (twelveDirectionDualMultiplicityVertices
          (restoredPivotConfiguration cfg p) 2).card +
        (2 * (twelveDirectionDualMultiplicityVertices
          (restoredPivotConfiguration cfg p) 3).card +
        (3 * (twelveDirectionDualMultiplicityVertices
          (restoredPivotConfiguration cfg p) 4).card +
        4 * (twelveDirectionDualMultiplicityVertices
          (restoredPivotConfiguration cfg p) 5).card)) := by
    exact_mod_cast htotal
  rw [card_twelveDirectionDualMultiplicityVertices_restored_eq_twelveDirectionT2,
    card_twelveDirectionDualMultiplicityVertices_restored_eq_twelveDirectionT3,
    card_twelveDirectionDualMultiplicityVertices_restored_eq_twelveDirectionT4,
    card_twelveDirectionDualMultiplicityVertices_restored_eq_twelveDirectionT5_of_lineCount_six_eq_zero
      cfg p hline] at htotalInt
  have hpartition :=
    twelveDirectionTotalDualDefect_eq_actualOffStarDefect_add_starDefect cfg p c hp
  have hstar := twelveDirectionStarDefect_eq_thirty_nine
    cfg p c hp hpoints hcircle
  have hpartitionInt : (twelveDirectionTotalDualDefect cfg p : Int) =
      (twelveDirectionActualOffStarDefect cfg p c hp : Int) +
        (twelveDirectionStarDefect cfg p c hp : Int) := by
    exact_mod_cast hpartition
  rw [hstar] at hpartitionInt
  simp only [twelveDirectionOffStarDefect]
  omega

/-- Consequently the genuine projective gap and the arithmetic row gap are
literally equal. -/
theorem twelveDirectionActualEqualityGap_eq_twelveDirectionEqualityGap
    {alpha : Type u} [Fintype alpha] [DecidableEq alpha]
    (cfg : Configuration alpha) (p : alpha) (c : DeterminedCircle cfg)
    (hp : p ∈ circleTrace cfg c.1)
    (hpoints : Fintype.card alpha = 12)
    (hcircle : (circleTrace cfg c.1).card = 6)
    (hcap : BlockSizeCap (blockSystem cfg) 6)
    (hline : (blockSystem cfg).lineCount 6 = 0) :
    twelveDirectionActualEqualityGap cfg p c hp =
      twelveDirectionEqualityGap (blockSystem cfg) p := by
  rw [twelveDirectionActualEqualityGap_eq_actualDefect_sub_distinguished
    cfg p c hp hcap hline,
    twelveDirectionActualOffStarDefect_eq_twelveDirectionOffStarDefect
      cfg p c hp hpoints hcircle hcap hline]
  rfl

/-- The arithmetic equality gap is now nonnegative with no direction
principle assumed. -/
theorem twelveDirectionEqualityGap_nonneg_of_actual_geometry
    {alpha : Type u} [Fintype alpha] [DecidableEq alpha]
    (cfg : Configuration alpha) (p : alpha) (c : DeterminedCircle cfg)
    (hp : p ∈ circleTrace cfg c.1)
    (hpoints : Fintype.card alpha = 12)
    (hcircle : (circleTrace cfg c.1).card = 6)
    (hcap : BlockSizeCap (blockSystem cfg) 6)
    (hline : (blockSystem cfg).lineCount 6 = 0) :
    0 ≤ twelveDirectionEqualityGap (blockSystem cfg) p := by
  rw [← twelveDirectionActualEqualityGap_eq_twelveDirectionEqualityGap
    cfg p c hp hpoints hcircle hcap hline]
  exact twelveDirectionActualEqualityGap_nonneg cfg p c hp hcircle

end Erdos506.V1
