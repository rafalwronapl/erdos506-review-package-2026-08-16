import Erdos506.Incidence.RealProjectiveArrangementTopology

/-!
# The honest cone-to-boundary front for real projective faces

The existing arrangement topology supplies two complementary pieces of the
three-side argument.  A genuine face is a realized strict homogeneous sign
cone, and `arrangementFaceBoundary` is made from actual geometric open arcs
meeting the ambient closure of that face.  This file closes the elementary
cone topology between them:

* strict sign cones are open;
* closed sign cones are closed and convex;
* whenever the strict cone is realized, its closure is exactly the closed
  sign cone;
* for a non-pencil arrangement the resulting closed cone is pointed.

It also records the lossless finite endpoint: three distinct geometric arcs
in the closure of a face give three distinct members of its literal boundary.

The remaining geometric lemma is now precise.  For every genuine face of a
non-pencil arrangement one must construct an injective family
`edge : Fin 3 -> A.GeometricEdge` and points `q i` such that

`q i in A.geometricEdgeOpenArc (edge i)`

and

`q i in closure (A.arrangementFaceCarrier F)`.

Equivalently, one may prove the standard polyhedral statement that the
full-dimensional pointed closed sign cone has three distinct facets, together
with a facet-realization theorem identifying each such facet with one of the
cyclic geometric arcs.  Neither the cyclic coverage theorem nor this
facet-to-arc identification is present in the current API, so no unconditional
face-cardinality theorem is asserted here.
-/

namespace Erdos506.Incidence

open scoped Convex LinearAlgebra.Projectivization

universe u

namespace FiniteProjectiveLineArrangement

variable {Line : Type u} [Fintype Line] [DecidableEq Line]

noncomputable local instance realProjectivePointTopologicalSpaceForFaceThree :
    TopologicalSpace RealProjectivePoint :=
  realProjectivePointQuotientTopology

/-- A strict homogeneous sign cone is open. -/
theorem isOpen_arrangementSignCone
    (A : FiniteProjectiveLineArrangement Line) (sigma : Line -> Bool) :
    IsOpen (A.arrangementSignCone sigma) := by
  classical
  unfold arrangementSignCone
  apply isOpen_iInter_of_finite
  intro l
  by_cases hs : sigma l
  · simp only [hs, if_true]
    exact isOpen_lt continuous_const
      (projectiveLineEvaluation
        (A.projectiveLine l)).continuous_of_finiteDimensional
  · simp only [hs, if_false]
    exact isOpen_lt
      (projectiveLineEvaluation
        (A.projectiveLine l)).continuous_of_finiteDimensional
      continuous_const

/-- A closed homogeneous sign cone is closed. -/
theorem isClosed_arrangementClosedSignCone
    (A : FiniteProjectiveLineArrangement Line) (sigma : Line -> Bool) :
    IsClosed (A.arrangementClosedSignCone sigma) := by
  unfold arrangementClosedSignCone
  apply isClosed_iInter
  intro l
  by_cases hs : sigma l
  · simp only [hs, if_true]
    exact isClosed_le continuous_const
      (projectiveLineEvaluation
        (A.projectiveLine l)).continuous_of_finiteDimensional
  · simp only [hs, if_false]
    exact isClosed_le
      (projectiveLineEvaluation
        (A.projectiveLine l)).continuous_of_finiteDimensional
      continuous_const

/-- A closed homogeneous sign cone is convex. -/
theorem convex_arrangementClosedSignCone
    (A : FiniteProjectiveLineArrangement Line) (sigma : Line -> Bool) :
    Convex ℝ (A.arrangementClosedSignCone sigma) := by
  unfold arrangementClosedSignCone
  apply convex_iInter
  intro l
  by_cases hs : sigma l
  · simp only [hs, if_true]
    exact convex_halfSpace_ge
      (IsLinearMap.mk
        (projectiveLineEvaluation (A.projectiveLine l)).map_add
        (projectiveLineEvaluation (A.projectiveLine l)).map_smul) 0
  · simp only [hs, if_false]
    exact convex_halfSpace_le
      (IsLinearMap.mk
        (projectiveLineEvaluation (A.projectiveLine l)).map_add
        (projectiveLineEvaluation (A.projectiveLine l)).map_smul) 0

/-- Moving from a strict-cone point towards a closed-cone point stays strict
until the closed endpoint itself. -/
theorem openSegment_subset_arrangementSignCone_of_mem_closed
    (A : FiniteProjectiveLineArrangement Line) (sigma : Line -> Bool)
    {u v : Fin 3 -> ℝ}
    (hu : u ∈ A.arrangementSignCone sigma)
    (hv : v ∈ A.arrangementClosedSignCone sigma) :
    openSegment ℝ u v ⊆ A.arrangementSignCone sigma := by
  simp only [arrangementSignCone, Set.mem_iInter] at hu
  simp only [arrangementClosedSignCone, Set.mem_iInter] at hv
  rintro z ⟨a, b, ha, hb, _hab, rfl⟩
  simp only [arrangementSignCone, Set.mem_iInter]
  intro l
  by_cases hs : sigma l
  · have hu' : 0 < projectiveLineEvaluation (A.projectiveLine l) u := by
      simpa [hs] using hu l
    have hv' : 0 ≤ projectiveLineEvaluation (A.projectiveLine l) v := by
      simpa [hs] using hv l
    have hau : 0 <
        a * projectiveLineEvaluation (A.projectiveLine l) u :=
      mul_pos ha hu'
    have hbv : 0 ≤
        b * projectiveLineEvaluation (A.projectiveLine l) v :=
      mul_nonneg hb.le hv'
    have hsum : 0 <
        a * projectiveLineEvaluation (A.projectiveLine l) u +
          b * projectiveLineEvaluation (A.projectiveLine l) v := by
      linarith
    simpa [hs, LinearMap.map_add, LinearMap.map_smul,
      smul_eq_mul] using hsum
  · have hu' : projectiveLineEvaluation (A.projectiveLine l) u < 0 := by
      simpa [hs] using hu l
    have hv' : projectiveLineEvaluation (A.projectiveLine l) v ≤ 0 := by
      simpa [hs] using hv l
    have hau :
        a * projectiveLineEvaluation (A.projectiveLine l) u < 0 :=
      mul_neg_of_pos_of_neg ha hu'
    have hbv :
        b * projectiveLineEvaluation (A.projectiveLine l) v ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hb.le hv'
    have hsum :
        a * projectiveLineEvaluation (A.projectiveLine l) u +
          b * projectiveLineEvaluation (A.projectiveLine l) v < 0 := by
      linarith
    simpa [hs, LinearMap.map_add, LinearMap.map_smul,
      smul_eq_mul] using hsum

/-- For every realized sign word, replacing its strict inequalities by weak
ones gives exactly its topological closure in homogeneous coordinates. -/
theorem closure_arrangementSignCone_eq_arrangementClosedSignCone
    (A : FiniteProjectiveLineArrangement Line) (sigma : Line -> Bool)
    (hne : (A.arrangementSignCone sigma).Nonempty) :
    closure (A.arrangementSignCone sigma) =
      A.arrangementClosedSignCone sigma := by
  apply Set.Subset.antisymm
  · exact closure_minimal
      (A.arrangementSignCone_subset_arrangementClosedSignCone sigma)
      (A.isClosed_arrangementClosedSignCone sigma)
  · intro v hv
    obtain ⟨u, hu⟩ := hne
    have hvSegment : v ∈ [u -[ℝ] v] := right_mem_segment ℝ u v
    have hvClosure : v ∈ closure (openSegment ℝ u v) :=
      segment_subset_closure_openSegment hvSegment
    exact closure_mono
      (A.openSegment_subset_arrangementSignCone_of_mem_closed sigma hu hv)
      hvClosure

/-- The strict cone attached to an actual face is realized by its normalized
representative. -/
theorem arrangementFaceSignCone_nonempty
    (A : FiniteProjectiveLineArrangement Line) (base : Line)
    (F : A.ArrangementFace) :
    (A.arrangementSignCone (A.arrangementFaceSignPattern base F)).Nonempty := by
  refine ⟨A.arrangementNormalizedRepresentative base
    (A.arrangementFaceRepresentative F), ?_⟩
  exact A.arrangementNormalizedRepresentative_mem_arrangementSignCone
    base (A.arrangementFaceRepresentative F)

/-- Homogeneous closure of the strict cone of a genuine face. -/
theorem closure_arrangementFaceSignCone_eq_closed
    (A : FiniteProjectiveLineArrangement Line) (base : Line)
    (F : A.ArrangementFace) :
    closure (A.arrangementSignCone (A.arrangementFaceSignPattern base F)) =
      A.arrangementClosedSignCone (A.arrangementFaceSignPattern base F) :=
  A.closure_arrangementSignCone_eq_arrangementClosedSignCone _
    (A.arrangementFaceSignCone_nonempty base F)

/-- In a non-pencil arrangement the closed homogeneous cone of every actual
face contains no nontrivial line. -/
theorem eq_zero_of_mem_arrangementFaceClosedSignCone_of_neg_mem
    (A : FiniteProjectiveLineArrangement Line) (hA : A.NonPencil)
    (base : Line) (F : A.ArrangementFace) {v : Fin 3 -> ℝ}
    (hv : v ∈ A.arrangementClosedSignCone
      (A.arrangementFaceSignPattern base F))
    (hneg : -v ∈ A.arrangementClosedSignCone
      (A.arrangementFaceSignPattern base F)) :
    v = 0 :=
  A.eq_zero_of_mem_arrangementClosedSignCone_of_neg_mem_of_nonPencil
    hA _ hv hneg

/-- Finite endpoint: an injective choice of three literal boundary edges
forces the required face degree. -/
theorem three_le_arrangementFaceBoundary_card_of_injective
    (A : FiniteProjectiveLineArrangement Line) (F : A.ArrangementFace)
    (edge : Fin 3 -> A.GeometricEdge)
    (hmem : ∀ i, edge i ∈ A.arrangementFaceBoundary F)
    (hinj : Function.Injective edge) :
    3 ≤ (A.arrangementFaceBoundary F).card := by
  classical
  let edge' : Fin 3 -> {e // e ∈ A.arrangementFaceBoundary F} :=
    fun i => ⟨edge i, hmem i⟩
  have hinj' : Function.Injective edge' := by
    intro i j hij
    apply hinj
    exact congrArg Subtype.val hij
  have hcard := Fintype.card_le_of_injective edge' hinj'
  simpa only [Fintype.card_fin, Fintype.card_coe] using hcard

/-- Concrete cone/facet hand-off: three distinct geometric open arcs meeting
the ambient closure of a face are three distinct members of its boundary. -/
theorem three_le_arrangementFaceBoundary_card_of_three_closure_arcs
    (A : FiniteProjectiveLineArrangement Line) (F : A.ArrangementFace)
    (edge : Fin 3 -> A.GeometricEdge)
    (q : Fin 3 -> RealProjectivePoint)
    (harc : ∀ i, q i ∈ A.geometricEdgeOpenArc (edge i))
    (hclosure : ∀ i, q i ∈ closure (A.arrangementFaceCarrier F))
    (hinj : Function.Injective edge) :
    3 ≤ (A.arrangementFaceBoundary F).card := by
  apply A.three_le_arrangementFaceBoundary_card_of_injective F edge
  · intro i
    rw [A.mem_arrangementFaceBoundary_iff]
    exact ⟨q i, harc i, hclosure i⟩
  · exact hinj

end FiniteProjectiveLineArrangement

end Erdos506.Incidence
