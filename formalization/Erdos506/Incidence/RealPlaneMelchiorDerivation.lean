import Erdos506.Incidence.DeterminedLineArrangementCensus
import Erdos506.Incidence.RealProjectiveArrangementTopology

/-!
# Deriving the real-plane Melchior principle from arrangement topology

The existing real-projective arrangement development already constructs the
actual vertices, cyclic geometric edges, and complement components.  It also
proves the exact edge census and the fact that every geometric edge is on the
boundary of exactly two genuine faces.

This file supplies the remaining algebraic adapters for the dual arrangement
of a finite affine configuration:

* determined affine lines are equivalent to the actual dual vertex set;
* a noncollinear affine configuration gives a non-pencil dual arrangement;
* the existing edge and boundary counts assemble into the finite Melchior
  cellulation interface.

The only global topological input left explicit is Euler's relation together
with the assertion that every genuine face has at least three boundary edges.
No replacement axiom for either statement is introduced.
-/

namespace Erdos506.Incidence

open Erdos506.Finite
open Erdos506.V4
open scoped BigOperators

noncomputable local instance arrangementFaceFintypeForMelchiorDerivation
    {Line : Type*} [Fintype Line] [DecidableEq Line]
    (A : FiniteProjectiveLineArrangement Line) : Fintype A.ArrangementFace :=
  A.arrangementFaceFintype

noncomputable local instance geometricEdgeDecidableEqForMelchiorDerivation
    {Line : Type*} [Fintype Line] [DecidableEq Line]
    (A : FiniteProjectiveLineArrangement Line) : DecidableEq A.GeometricEdge :=
  Classical.decEq _

variable {alpha : Type*} [Fintype alpha] [DecidableEq alpha]

/-- A determined line, regarded as the corresponding actual vertex of the
dual arrangement. -/
noncomputable def determinedLineToLabelDualVertexSet
    (cfg : Configuration alpha) :
    DeterminedLine cfg -> {p // p ∈ labelDualVertexSet cfg} :=
  fun L => ⟨determinedLineDualVertex cfg L,
    determinedLineDualVertex_mem_labelDualVertexSet cfg L⟩

/-- Distinct determined affine lines give distinct actual dual vertices. -/
theorem determinedLineToLabelDualVertexSet_injective
    (cfg : Configuration alpha) :
    Function.Injective (determinedLineToLabelDualVertexSet cfg) := by
  intro L M hLM
  apply determinedProjectiveLine_injective cfg
  exact congrArg Subtype.val hLM

/-- Every actual vertex of the labelled dual arrangement is the vertex of a
determined affine line.  Thus the pair construction of `vertexSet` introduces
neither extra vertices nor duplicate determined lines. -/
theorem determinedLineToLabelDualVertexSet_surjective
    (cfg : Configuration alpha) :
    Function.Surjective (determinedLineToLabelDualVertexSet cfg) := by
  classical
  rintro ⟨p, hp⟩
  obtain ⟨a, b, hab, hpab⟩ :=
    exists_label_pair_of_mem_labelDualVertexSet cfg hp
  let e : KSubset alpha 2 := ⟨{a, b}, by simp [hab]⟩
  let L : DeterminedLine cfg :=
    ⟨lineOfPair cfg e, lineOfPair_mem_determinedLines cfg e⟩
  have ha : cfg a ∈ L.1 := by
    rw [← mem_lineSupport]
    exact pair_subset_lineSupport cfg e (by simp [e])
  have hb : cfg b ∈ L.1 := by
    rw [← mem_lineSupport]
    exact pair_subset_lineSupport cfg e (by simp [e])
  have hdual : determinedLineDualVertex cfg L =
      (labelDualArrangement cfg).intersection a b :=
    labelDual_eq_intersection_of_incident cfg hab
      ((labelDual_incident_determinedLine_iff cfg a L).2 ha)
      ((labelDual_incident_determinedLine_iff cfg b L).2 hb)
  refine ⟨L, Subtype.ext ?_⟩
  exact hdual.trans hpab

/-- The finite type of determined affine lines is exactly the subtype of
actual projective vertices of the labelled dual arrangement. -/
noncomputable def determinedLineEquivLabelDualVertexSet
    (cfg : Configuration alpha) :
    DeterminedLine cfg ≃ {p // p ∈ labelDualVertexSet cfg} :=
  Equiv.ofBijective (determinedLineToLabelDualVertexSet cfg)
    ⟨determinedLineToLabelDualVertexSet_injective cfg,
      determinedLineToLabelDualVertexSet_surjective cfg⟩

@[simp] theorem determinedLineEquivLabelDualVertexSet_apply_val
    (cfg : Configuration alpha) (L : DeterminedLine cfg) :
    (determinedLineEquivLabelDualVertexSet cfg L).1 =
      determinedLineDualVertex cfg L :=
  rfl

/-- Cardinality form of the determined-line/actual-vertex equivalence. -/
theorem card_determinedLine_eq_card_labelDualVertexSet
    (cfg : Configuration alpha) :
    Fintype.card (DeterminedLine cfg) =
      Fintype.card {p // p ∈ labelDualVertexSet cfg} :=
  Fintype.card_congr (determinedLineEquivLabelDualVertexSet cfg)

/-- Transport the concrete arrangement edge census from actual vertices to
determined lines. -/
theorem sum_labelDualVertexSet_multiplicity_eq_determinedLine
    (cfg : Configuration alpha) :
    (∑ p ∈ labelDualVertexSet cfg,
        (labelDualArrangement cfg).multiplicity p) =
      ∑ L : DeterminedLine cfg,
        (labelDualArrangement cfg).multiplicity
          (determinedLineDualVertex cfg L) := by
  classical
  conv_lhs => rw [← Finset.sum_attach]
  rw [Finset.attach_eq_univ]
  symm
  apply Fintype.sum_equiv (determinedLineEquivLabelDualVertexSet cfg)
  intro L
  rfl

/-- Noncollinearity of the affine configuration is precisely enough to rule
out a common point of all labelled dual lines. -/
theorem labelDualArrangement_nonPencil_of_noncollinear
    (cfg : Configuration alpha) (hnon : Noncollinear cfg) :
    (labelDualArrangement cfg).NonPencil := by
  classical
  have hnontrivial : Nontrivial alpha := by
    by_contra htrivial
    haveI : Subsingleton alpha :=
      not_nontrivial_iff_subsingleton.mp htrivial
    apply hnon
    rcases isEmpty_or_nonempty alpha with hEmpty | hNonempty
    · letI : IsEmpty alpha := hEmpty
      have hpointSet : pointSet cfg = ∅ := by
        ext p
        simp [pointSet]
      rw [hpointSet]
      exact collinear_empty ℝ Point2
    · letI : Nonempty alpha := hNonempty
      let a : alpha := Classical.choice hNonempty
      have hsubset : pointSet cfg ⊆ ({cfg a} : Set Point2) := by
        rintro p ⟨b, rfl⟩
        simp [Subsingleton.elim b a]
      exact (collinear_singleton (k := ℝ) (cfg a)).subset hsubset
  letI : Nontrivial alpha := hnontrivial
  obtain ⟨a, b, hab⟩ := exists_pair_ne alpha
  intro hpencil
  obtain ⟨p, hp⟩ := hpencil
  let e : KSubset alpha 2 := ⟨{a, b}, by simp [hab]⟩
  let L : DeterminedLine cfg :=
    ⟨lineOfPair cfg e, lineOfPair_mem_determinedLines cfg e⟩
  have ha : cfg a ∈ L.1 := by
    rw [← mem_lineSupport]
    exact pair_subset_lineSupport cfg e (by simp [e])
  have hb : cfg b ∈ L.1 := by
    rw [← mem_lineSupport]
    exact pair_subset_lineSupport cfg e (by simp [e])
  have hpab : p = (labelDualArrangement cfg).intersection a b :=
    labelDual_eq_intersection_of_incident cfg hab (hp a) (hp b)
  have hLab : determinedLineDualVertex cfg L =
      (labelDualArrangement cfg).intersection a b :=
    labelDual_eq_intersection_of_incident cfg hab
      ((labelDual_incident_determinedLine_iff cfg a L).2 ha)
      ((labelDual_incident_determinedLine_iff cfg b L).2 hb)
  have hsubset : pointSet cfg ⊆ (L.1 : Set Point2) := by
    rintro q ⟨x, rfl⟩
    apply (labelDual_incident_determinedLine_iff cfg x L).1
    rw [hLab, ← hpab]
    exact hp x
  apply hnon
  apply Collinear.subset hsubset
  rw [collinear_iff_finrank_le_one, ← L.1.direction_eq_vectorSpan]
  exact le_of_eq L.direction_finrank

universe u

/-- The two global facts about genuine real-projective arrangement faces
which are not yet proved by `RealProjectiveArrangementTopology`.

All other fields of the finite Melchior cellulation are constructed below
from the existing vertex, cyclic-edge, and closure-incidence theory. -/
structure RealProjectiveArrangementGlobalInput where
  euler :
    ∀ {Line : Type u} [Fintype Line] [DecidableEq Line]
      (A : FiniteProjectiveLineArrangement Line),
      A.NonPencil ->
        Fintype.card {p // p ∈ A.vertexSet} +
            Fintype.card A.ArrangementFace =
          Fintype.card A.GeometricEdge + 1
  faceHasThreeEdges :
    ∀ {Line : Type u} [Fintype Line] [DecidableEq Line]
      (A : FiniteProjectiveLineArrangement Line),
      A.NonPencil -> ∀ F : A.ArrangementFace,
        3 ≤ (A.arrangementFaceBoundary F).card

/-- Under the two explicit global topological facts, the actual dual
arrangement is a `ProjectiveArrangementCellulation`.  Its edges and faces
are the genuine geometric edges and complement components already present in
the topology development. -/
noncomputable def labelDualProjectiveArrangementCellulation
    (H : RealProjectiveArrangementGlobalInput.{u})
    {alpha : Type u} [Fintype alpha] [DecidableEq alpha]
    (cfg : Configuration alpha) (hnon : Noncollinear cfg) :
    ProjectiveArrangementCellulation
      (DeterminedLine cfg)
      (labelDualArrangement cfg).GeometricEdge
      (labelDualArrangement cfg).ArrangementFace := by
  classical
  let A := labelDualArrangement cfg
  have hA : A.NonPencil := by
    simpa [A] using labelDualArrangement_nonPencil_of_noncollinear cfg hnon
  exact
    { multiplicity := fun L =>
        A.multiplicity (determinedLineDualVertex cfg L)
      faceBoundary := A.arrangementFaceBoundary
      euler := by
        rw [card_determinedLine_eq_card_labelDualVertexSet cfg]
        simpa [A, labelDualVertexSet] using H.euler A hA
      edgeCount := by
        calc
          Fintype.card A.GeometricEdge =
              ∑ p ∈ A.vertexSet, A.multiplicity p :=
            A.card_geometricEdge_eq_sum_multiplicity
          _ = ∑ L : DeterminedLine cfg,
              A.multiplicity (determinedLineDualVertex cfg L) := by
            simpa [A, labelDualVertexSet] using
              sum_labelDualVertexSet_multiplicity_eq_determinedLine cfg
      faceHasThreeEdges := H.faceHasThreeEdges A hA
      edgeHasTwoFaces :=
        A.edgeHasTwoFaces_arrangementFaceBoundary hA }

/-- The explicit global arrangement input proves Melchior for every finite
noncollinear real affine configuration. -/
theorem lineMelchior_of_realProjectiveArrangementGlobalInput
    (H : RealProjectiveArrangementGlobalInput.{u})
    {alpha : Type u} [Fintype alpha] [DecidableEq alpha]
    (cfg : Configuration alpha) (hnon : Noncollinear cfg) :
    LineMelchior cfg := by
  apply lineMelchior_of_dualCellulation cfg
    (labelDualProjectiveArrangementCellulation H cfg hnon)
  intro L
  rfl

/-- Assembly of the requested real-plane principle.  The theorem is
unconditional apart from the two missing global topology fields kept in the
explicit input structure above. -/
noncomputable def realPlaneMelchiorPrincipleOfGlobalInput
    (H : RealProjectiveArrangementGlobalInput.{u}) :
    RealPlaneMelchiorPrinciple.{u} where
  lineMelchior := fun cfg hnon =>
    lineMelchior_of_realProjectiveArrangementGlobalInput H cfg hnon

end Erdos506.Incidence
