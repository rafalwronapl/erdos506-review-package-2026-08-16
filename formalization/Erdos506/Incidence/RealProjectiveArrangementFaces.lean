import Erdos506.Incidence.RealProjectiveLineSuccessor

/-!
# The finite edge boundary of a real projective arrangement

This module records the part of the face construction which follows from the
projective incidence geometry alone.  An arrangement edge has one open gap on
each side of every marked point on each supporting projective line.  The
successor module now supplies its genuine terminal endpoint through the
transported cyclic orientation of that real projective line.

The results below deliberately stop at this boundary census.  In particular,
they do not manufacture faces, an Euler relation, or a face--edge handshake.
Those assertions require the still-missing theorem that the complement of the
real projective arrangement is a finite cellulation.  The local `RP¹`
parametrisation, cyclic successors, and exact edge census are no longer part
of that gap.
-/

namespace Erdos506.Incidence

open Matrix
open scoped BigOperators LinearAlgebra.Projectivization

namespace FiniteProjectiveLineArrangement

variable {Line : Type*} [Fintype Line] [DecidableEq Line]

/-- All indexed lines of the arrangement pass through one projective point. -/
def IsPencil (A : FiniteProjectiveLineArrangement Line) : Prop :=
  ∃ p : RealProjectivePoint, ∀ l : Line, A.Incident p l

/-- The exact nondegeneracy hypothesis under which the projective arrangement
has no one- or two-sided face degeneracies.  It is kept separate from the
incidence data because it is a geometric conclusion to be supplied by the
dual realization of a noncollinear configuration. -/
def NonPencil (A : FiniteProjectiveLineArrangement Line) : Prop :=
  ¬ A.IsPencil

/-- A non-pencil arrangement has another indexed line besides every chosen
one.  This elementary consequence supplies a base chart transverse to the
supporting line of every future geometric edge. -/
theorem exists_ne_line_of_nonPencil
    (A : FiniteProjectiveLineArrangement Line) (hA : A.NonPencil) (l : Line) :
    ∃ m : Line, m ≠ l := by
  classical
  by_contra h
  apply hA
  have hall : ∀ m : Line, m = l := by
    intro m
    apply Classical.byContradiction
    intro hml
    exact h ⟨m, hml⟩
  let u : RealProjectiveLineVector := ![1, 0]
  have hu : u ≠ 0 := by
    intro hzero
    have hcoord := congrFun hzero (0 : Fin 2)
    norm_num [u] at hcoord
  refine ⟨projectiveLineParameter (A.projectiveLine l)
    (Projectivization.mk ℝ u hu), ?_⟩
  intro m
  rw [hall m]
  exact projectiveLineParameter_incident (A.projectiveLine l)
    (Projectivization.mk ℝ u hu)

/-- At any specified point, a non-pencil arrangement has a line which does
not pass through that point.  Applied to a marked vertex on one support,
this supplies a second marked vertex on the support. -/
theorem exists_not_incident_line_of_nonPencil
    (A : FiniteProjectiveLineArrangement Line) (hA : A.NonPencil)
    (p : RealProjectivePoint) :
    ∃ m : Line, ¬ A.Incident p m := by
  classical
  by_contra h
  apply hA
  refine ⟨p, ?_⟩
  intro m
  by_contra hpm
  exact h ⟨m, hpm⟩

/-- The intersection of two distinct indexed lines is a marked vertex on the
first supporting line. -/
theorem intersection_mem_lineVertexSet_left
    (A : FiniteProjectiveLineArrangement Line) {l m : Line} (hlm : l ≠ m) :
    A.intersection l m ∈ A.lineVertexSet l := by
  rw [mem_lineVertexSet]
  exact ⟨A.intersection_mem_vertexSet hlm, A.intersection_incident_left hlm⟩

/-- The intersection of two distinct indexed lines is a marked vertex on the
second supporting line. -/
theorem intersection_mem_lineVertexSet_right
    (A : FiniteProjectiveLineArrangement Line) {l m : Line} (hlm : l ≠ m) :
    A.intersection l m ∈ A.lineVertexSet m := by
  rw [mem_lineVertexSet]
  exact ⟨A.intersection_mem_vertexSet hlm, A.intersection_incident_right hlm⟩

/-- Every indexed line meeting another indexed line carries a marked vertex.
This is the nonemptiness needed before one can take a circular successor on
that line. -/
theorem nonempty_lineVertexSet_of_exists_ne
    (A : FiniteProjectiveLineArrangement Line) (l : Line)
    (h : ∃ m : Line, m ≠ l) :
    Nonempty (A.CircularGapSlot l) := by
  rcases h with ⟨m, hml⟩
  refine ⟨⟨A.intersection m l, ?_⟩⟩
  exact A.intersection_mem_lineVertexSet_right hml

/-- The representative of the initial endpoint of every edge slot lies in
the homogeneous two-dimensional carrier of its supporting projective line.
Thus every future local `RP¹` parametrisation may be constructed entirely
inside this canonical kernel. -/
theorem edgeSlotVertex_rep_mem_projectiveLineKernel
    (A : FiniteProjectiveLineArrangement Line) (e : A.EdgeSlot) :
    (A.edgeSlotVertex e).rep ∈
      projectiveLineKernel (A.projectiveLine (A.edgeSlotLine e)) := by
  exact (orthogonal_iff_rep_mem_projectiveLineKernel
    (A.edgeSlotVertex e) (A.projectiveLine (A.edgeSlotLine e))).mp
    (A.edgeSlot_incident e)

/-- Counting the marked points on all indexed projective lines counts the
canonical edge slots exactly once.  This is the geometric form of the edge
handshake before a successor endpoint is attached to a slot. -/
theorem card_edgeSlot_eq_sum_card_lineVertexSet
    (A : FiniteProjectiveLineArrangement Line) :
    Fintype.card A.EdgeSlot = ∑ l : Line, (A.lineVertexSet l).card := by
  calc
    Fintype.card A.EdgeSlot =
        Fintype.card (Σ l : Line, A.CircularGapSlot l) :=
      Fintype.card_congr A.edgeSlotEquivCircularGap
    _ = ∑ l : Line, Fintype.card (A.CircularGapSlot l) :=
      Fintype.card_sigma
    _ = ∑ l : Line, (A.lineVertexSet l).card := by
      apply Finset.sum_congr rfl
      intro l _
      exact Fintype.card_coe (A.lineVertexSet l)

/-- Combining the two exact counts shows that the total number of marked
points encountered while traversing all arrangement lines equals the sum of
vertex multiplicities.  No face/topology assertion enters this identity. -/
theorem sum_card_lineVertexSet_eq_sum_multiplicity
    (A : FiniteProjectiveLineArrangement Line) :
    (∑ l : Line, (A.lineVertexSet l).card) =
      ∑ p ∈ A.vertexSet, A.multiplicity p := by
  rw [← A.card_edgeSlot_eq_sum_card_lineVertexSet]
  exact A.card_edgeSlot_eq_sum_multiplicity

/-- Every canonical edge slot now has an actual terminal marked vertex on
the same projective line.  This is the endpoint data which the future
complement-cellulation theorem must turn into faces. -/
theorem geometricEdge_endpoint_incident
    (A : FiniteProjectiveLineArrangement Line) (e : A.GeometricEdge) :
    A.Incident (A.geometricEdgeTerminal e) (A.edgeSlotLine e) :=
  A.edgeSlotEndpoint_incident e

/-- Both endpoints of a geometric edge are actual vertices of the
arrangement. -/
theorem geometricEdge_initial_mem_vertexSet
    (A : FiniteProjectiveLineArrangement Line) (e : A.GeometricEdge) :
    A.geometricEdgeInitial e ∈ A.vertexSet :=
  A.edgeSlotVertex_mem_vertexSet e

theorem geometricEdge_terminal_mem_vertexSet
    (A : FiniteProjectiveLineArrangement Line) (e : A.GeometricEdge) :
    A.geometricEdgeTerminal e ∈ A.vertexSet :=
  A.edgeSlotEndpoint_mem_vertexSet e

/-- The supporting projective line is incident with the initial endpoint as
well as the terminal endpoint. -/
theorem geometricEdge_initial_incident
    (A : FiniteProjectiveLineArrangement Line) (e : A.GeometricEdge) :
    A.Incident (A.geometricEdgeInitial e) (A.edgeSlotLine e) :=
  A.edgeSlot_incident e

/-- In a non-pencil arrangement, the endpoint selected by the geometric
cyclic successor is different from its initial vertex.  The other endpoint
is forced by a line missing the initial vertex, so this excludes precisely
the one-marked-point loop and no stronger artificial condition. -/
theorem geometricEdge_initial_ne_terminal_of_nonPencil
    (A : FiniteProjectiveLineArrangement Line) (hA : A.NonPencil)
    (e : A.GeometricEdge) :
    A.geometricEdgeInitial e ≠ A.geometricEdgeTerminal e := by
  classical
  obtain ⟨m, hm⟩ :=
    A.exists_not_incident_line_of_nonPencil hA (A.geometricEdgeInitial e)
  have hml : m ≠ A.edgeSlotLine e := by
    intro hml
    apply hm
    rw [hml]
    exact A.geometricEdge_initial_incident e
  let r : A.CircularGapSlot (A.edgeSlotLine e) :=
    ⟨A.intersection (A.edgeSlotLine e) m,
      A.intersection_mem_lineVertexSet_left hml.symm⟩
  have hrne : r ≠ A.edgeSlotAsCircularGapSlot e := by
    intro hr
    apply hm
    have hpoint : A.intersection (A.edgeSlotLine e) m =
        A.geometricEdgeInitial e := by
      simpa only [r, edgeSlotAsCircularGapSlot, geometricEdgeInitial] using
        congrArg Subtype.val hr
    rw [← hpoint]
    exact A.intersection_incident_right hml.symm
  have hsuccessor := A.circularGapSuccessor_ne_self_of_exists_ne
    (A.edgeSlotLine e) (A.edgeSlotAsCircularGapSlot e) ⟨r, hrne⟩
  intro hterminal
  apply hsuccessor
  apply Subtype.ext
  change A.edgeSlotEndpoint e = A.edgeSlotVertex e
  exact hterminal.symm

/-- The cyclic endpoint has no marked vertex in the positive open arc from
its initial vertex.  Thus `GeometricEdge` is an actual arrangement edge,
rather than an arbitrary pairing of vertices on a line. -/
theorem geometricEdge_no_lineVertex_between
    (A : FiniteProjectiveLineArrangement Line) (e : A.GeometricEdge)
    (q : A.CircularGapSlot (A.edgeSlotLine e)) :
    ¬ ProjectiveLineCyclic (A.projectiveLine (A.edgeSlotLine e))
      (A.geometricEdgeInitial e) q.1 (A.geometricEdgeTerminal e) :=
  A.edgeSlot_no_lineVertex_between_endpoint e q

/-- The open oriented arc represented by a non-loop geometric edge.  Its
definition uses the transported cyclic order, so it is the actual open gap
from the initial marked vertex to its geometric successor, not a set chosen
by an arbitrary ordering.  For a one-vertex loop the cyclic predicate is
empty; that degenerate case is handled separately by any non-pencil
cellulation theorem. -/
def geometricEdgeOpenArc
    (A : FiniteProjectiveLineArrangement Line) (e : A.GeometricEdge) :
    Set RealProjectivePoint :=
  {q | ProjectiveLineCyclic (A.projectiveLine (A.edgeSlotLine e))
    (A.geometricEdgeInitial e) q (A.geometricEdgeTerminal e)}

/-- No actual arrangement vertex lies in the open arc of a geometric edge.
This turns the one-dimensional successor certificate into a statement about
the global vertex set. -/
theorem geometricEdgeOpenArc_disjoint_vertexSet
    (A : FiniteProjectiveLineArrangement Line) (e : A.GeometricEdge) :
    Disjoint (A.geometricEdgeOpenArc e) (↑A.vertexSet : Set RealProjectivePoint) := by
  rw [Set.disjoint_left]
  intro q hqArc hqVertex
  apply A.geometricEdge_no_lineVertex_between e
    ⟨q, (A.mem_lineVertexSet (A.edgeSlotLine e)).mpr
      ⟨hqVertex, projectiveLineCyclic_incident_middle hqArc⟩⟩
  exact hqArc

/-- Every point in the interior of a geometric edge belongs to its supporting
arrangement line and to no other indexed line.  This is the precise regular
point condition needed for the future two-sided local perturbation theorem. -/
theorem geometricEdgeOpenArc_incident_iff
    (A : FiniteProjectiveLineArrangement Line) (e : A.GeometricEdge)
    {q : RealProjectivePoint} (hq : q ∈ A.geometricEdgeOpenArc e) (m : Line) :
    A.Incident q m ↔ m = A.edgeSlotLine e := by
  constructor
  · intro hqm
    by_contra hne
    have hne' : A.edgeSlotLine e ≠ m := fun h => hne h.symm
    have hsupport : A.Incident q (A.edgeSlotLine e) :=
      projectiveLineCyclic_incident_middle hq
    have hqeq : q = A.intersection (A.edgeSlotLine e) m :=
      A.eq_intersection_of_incident hne' hsupport hqm
    have hqVertex : q ∈ A.vertexSet := by
      rw [hqeq]
      exact A.intersection_mem_vertexSet hne'
    exact (Set.disjoint_left.mp (A.geometricEdgeOpenArc_disjoint_vertexSet e))
      hq hqVertex
  · intro hm
    rw [hm]
    exact projectiveLineCyclic_incident_middle hq

/-- The genuine geometric edge type has the same exact incidence handshake
as the original slot census. -/
theorem card_geometricEdge_eq_sum_card_lineVertexSet
    (A : FiniteProjectiveLineArrangement Line) :
    Fintype.card A.GeometricEdge = ∑ l : Line, (A.lineVertexSet l).card :=
  A.card_edgeSlot_eq_sum_card_lineVertexSet

end FiniteProjectiveLineArrangement

end Erdos506.Incidence
