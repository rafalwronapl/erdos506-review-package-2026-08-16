import Erdos506.Incidence.DeterminedLineArrangementCensus
import Erdos506.Incidence.RealProjectiveArrangementFaceThreeMinimalFinish
import Erdos506.Incidence.RealProjectiveOrdinaryEdgeTriangle
import Erdos506.Incidence.RealProjectiveTriangleExit
import Mathlib.Tactic

/-!
# The Kelly--Rottenberg counting layer

This file isolates the finite double count behind the Kelly--Moser ordinary
line bound.  The geometric input is deliberately phrased in terms of actual
vertices, triangular arrangement faces, and their boundary edges.
-/

namespace Erdos506.Incidence

open scoped BigOperators

universe u v

/-- Degree on the right side of a finite relation. -/
noncomputable def finiteRelationRightDegree
    {X : Type u} {Y : Type v} [Fintype X] [Fintype Y]
    (R : X -> Y -> Prop) (y : Y) : Nat := by
  classical
  exact (Finset.univ.filter fun x => R x y).card

/-- Degree on the left side of a finite relation. -/
noncomputable def finiteRelationLeftDegree
    {X : Type u} {Y : Type v} [Fintype X] [Fintype Y]
    (R : X -> Y -> Prop) (x : X) : Nat := by
  classical
  exact (Finset.univ.filter fun y => R x y).card

/-- The two degree sums of a finite bipartite relation agree. -/
theorem sum_finiteRelationRightDegree_eq_sum_finiteRelationLeftDegree
    {X : Type u} {Y : Type v} [Fintype X] [Fintype Y]
    (R : X -> Y -> Prop) :
    (∑ y : Y, finiteRelationRightDegree R y) =
      ∑ x : X, finiteRelationLeftDegree R x := by
  classical
  calc
    (∑ y : Y, finiteRelationRightDegree R y) =
        ∑ y : Y, ∑ x : X, if R x y then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro y _
      simp [finiteRelationRightDegree]
    _ = ∑ x : X, ∑ y : Y, if R x y then 1 else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ x : X, finiteRelationLeftDegree R x := by
      apply Finset.sum_congr rfl
      intro x _
      simp [finiteRelationLeftDegree]

/-- Pure finite Kelly--Rottenberg count.  `ordinary x y` records that the
ordinary vertex `x` lies on the arrangement line `y`; `attached x y` records
that it is the opposite vertex of a triangular face based on `y`.

The local clause says that a line either contains exactly two ordinary
vertices or has at least three ordinary-or-attached associations. -/
theorem kellyMoser_count_of_local_associations
    {Vertex : Type u} {Line : Type v} [Fintype Vertex] [Fintype Line]
    (ordinary attached : Vertex -> Line -> Prop)
    (hordinary : ∀ x : Vertex,
      finiteRelationLeftDegree ordinary x = 2)
    (hattached : ∀ x : Vertex,
      finiteRelationLeftDegree attached x ≤ 4)
    (hlocal : ∀ l : Line,
      finiteRelationRightDegree ordinary l = 2 ∨
        3 ≤ finiteRelationRightDegree ordinary l +
          finiteRelationRightDegree attached l) :
    3 * Fintype.card Line ≤ 7 * Fintype.card Vertex := by
  classical
  let exceptional : Finset Line := Finset.univ.filter fun l =>
    finiteRelationRightDegree ordinary l = 2
  have hordinarySum :
      (∑ l : Line, finiteRelationRightDegree ordinary l) =
        2 * Fintype.card Vertex := by
    rw [sum_finiteRelationRightDegree_eq_sum_finiteRelationLeftDegree]
    calc
      (∑ x : Vertex, finiteRelationLeftDegree ordinary x) =
          ∑ _x : Vertex, 2 := by
        apply Finset.sum_congr rfl
        intro x _
        exact hordinary x
      _ = 2 * Fintype.card Vertex := by simp [mul_comm]
  have hattachedSum :
      (∑ l : Line, finiteRelationRightDegree attached l) ≤
        4 * Fintype.card Vertex := by
    rw [sum_finiteRelationRightDegree_eq_sum_finiteRelationLeftDegree]
    calc
      (∑ x : Vertex, finiteRelationLeftDegree attached x) ≤
          ∑ _x : Vertex, 4 := by
        exact Finset.sum_le_sum fun x _ => hattached x
      _ = 4 * Fintype.card Vertex := by simp [mul_comm]
  have hexceptionalSum :
      (∑ l ∈ exceptional, finiteRelationRightDegree ordinary l) =
        2 * exceptional.card := by
    calc
      (∑ l ∈ exceptional, finiteRelationRightDegree ordinary l) =
          ∑ _l ∈ exceptional, 2 := by
        apply Finset.sum_congr rfl
        intro l hl
        exact (Finset.mem_filter.mp hl).2
      _ = 2 * exceptional.card := by simp [mul_comm]
  have hexceptionalSum_le :
      (∑ l ∈ exceptional, finiteRelationRightDegree ordinary l) ≤
        ∑ l : Line, finiteRelationRightDegree ordinary l := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · exact Finset.filter_subset _ _
    · intro l _ _
      exact Nat.zero_le _
  have hexceptionalCard : exceptional.card ≤ Fintype.card Vertex := by
    omega
  have hline (l : Line) :
      3 ≤ finiteRelationRightDegree ordinary l +
          finiteRelationRightDegree attached l +
          (if finiteRelationRightDegree ordinary l = 2 then 1 else 0) := by
    by_cases hl : finiteRelationRightDegree ordinary l = 2
    · simp [hl]
    · rcases hlocal l with hl' | hl'
      · exact (hl hl').elim
      · simpa [hl] using hl'
  have htotal :
      3 * Fintype.card Line ≤
        (∑ l : Line, finiteRelationRightDegree ordinary l) +
          (∑ l : Line, finiteRelationRightDegree attached l) +
            exceptional.card := by
    calc
      3 * Fintype.card Line = ∑ _l : Line, 3 := by simp [mul_comm]
      _ ≤ ∑ l : Line,
          (finiteRelationRightDegree ordinary l +
            finiteRelationRightDegree attached l +
              (if finiteRelationRightDegree ordinary l = 2 then 1 else 0)) := by
        exact Finset.sum_le_sum fun l _ => hline l
      _ = (∑ l : Line, finiteRelationRightDegree ordinary l) +
          (∑ l : Line, finiteRelationRightDegree attached l) +
            exceptional.card := by
        simp only [Finset.sum_add_distrib]
        simp [exceptional]
  omega

namespace FiniteProjectiveLineArrangement

variable {Line : Type*} [Fintype Line] [DecidableEq Line]

noncomputable local instance realProjectivePointTopologicalSpaceForKellyMoserFinish :
    TopologicalSpace RealProjectivePoint :=
  realProjectivePointQuotientTopology

noncomputable local instance realProjectivePointDecidableEqForKellyMoserFinish :
    DecidableEq RealProjectivePoint :=
  Classical.decEq _

noncomputable local instance geometricEdgeDecidableEqForKellyMoserFinish
    (A : FiniteProjectiveLineArrangement Line) : DecidableEq A.GeometricEdge :=
  Classical.decEq _

noncomputable local instance incidentDecidableForKellyMoserFinish
    (A : FiniteProjectiveLineArrangement Line)
    (p : RealProjectivePoint) (l : Line) :
    Decidable (A.Incident p l) :=
  Classical.propDecidable _

/-- The actual multiplicity-two vertices of an arrangement. -/
noncomputable def ordinaryVertexSet
    (A : FiniteProjectiveLineArrangement Line) : Finset RealProjectivePoint := by
  classical
  exact A.vertexSet.filter fun q => A.multiplicity q = 2

/-- A bundled actual multiplicity-two vertex. -/
abbrev OrdinaryVertex (A : FiniteProjectiveLineArrangement Line) :=
  {q : RealProjectivePoint // q ∈ A.ordinaryVertexSet}

/-- Bundle a marked vertex on an indexed line once its multiplicity is known
to be two. -/
noncomputable def circularGapOrdinaryVertex
    (A : FiniteProjectiveLineArrangement Line) (l : Line)
    (p : A.CircularGapSlot l) (hp2 : A.multiplicity p.1 = 2) :
    A.OrdinaryVertex := by
  classical
  exact ⟨p.1, Finset.mem_filter.mpr
    ⟨((A.mem_lineVertexSet l).mp p.2).1, hp2⟩⟩

@[simp]
theorem circularGapOrdinaryVertex_val
    (A : FiniteProjectiveLineArrangement Line) (l : Line)
    (p : A.CircularGapSlot l) (hp2 : A.multiplicity p.1 = 2) :
    (A.circularGapOrdinaryVertex l p hp2).1 = p.1 :=
  rfl

/-- A projective arrangement edge has `q` as one of its two selected cyclic
endpoints. -/
def geometricEdgeHasEndpoint
    (A : FiniteProjectiveLineArrangement Line) (e : A.GeometricEdge)
    (q : RealProjectivePoint) : Prop :=
  A.geometricEdgeInitial e = q ∨ A.geometricEdgeTerminal e = q

/-- Literal triangular-face witness that an ordinary vertex is opposite an
edge supported by `l`.  Using closure incidence rather than naming the two
edges through the vertex is the form directly produced by the generic
ordinary-endpoint API. -/
structure OrdinaryAttachmentWitness
    (A : FiniteProjectiveLineArrangement Line) (q : A.OrdinaryVertex)
    (l : Line) where
  face : A.ArrangementFace
  base : A.GeometricEdge
  away : ¬ A.Incident q.1 l
  triangular : (A.arrangementFaceBoundary face).card = 3
  base_mem : base ∈ A.arrangementFaceBoundary face
  base_line : A.edgeSlotLine base = l
  opposite : q.1 ∈ closure (A.arrangementFaceCarrier face)

/-- An ordinary vertex is attached to a line when the corresponding literal
triangular-face witness exists. -/
def OrdinaryVertexAttachedToLine
    (A : FiniteProjectiveLineArrangement Line) (q : A.OrdinaryVertex)
    (l : Line) : Prop :=
  Nonempty (OrdinaryAttachmentWitness A q l)

theorem incident_edgeSlotLine_of_geometricEdgeHasEndpoint
    (A : FiniteProjectiveLineArrangement Line) (e : A.GeometricEdge)
    (q : RealProjectivePoint) (h : A.geometricEdgeHasEndpoint e q) :
    A.Incident q (A.edgeSlotLine e) := by
  rcases h with h | h
  · rw [← h]
    exact A.geometricEdge_initial_incident e
  · rw [← h]
    exact A.geometricEdge_endpoint_incident e

/-- The face in an attachment witness really is locally incident with its
opposite ordinary vertex. -/
theorem OrdinaryAttachmentWitness.face_mem_arrangementPointIncidentFaces
    (A : FiniteProjectiveLineArrangement Line) (hA : A.NonPencil)
    {q : A.OrdinaryVertex} {l : Line}
    (w : OrdinaryAttachmentWitness A q l) :
    w.face ∈ A.arrangementPointIncidentFaces q.1 := by
  exact (A.mem_arrangementPointIncidentFaces_iff q.1 w.face).mpr w.opposite

/-- Number of ordinary vertices lying on one indexed arrangement line. -/
noncomputable def lineOrdinaryVertexDegree
    (A : FiniteProjectiveLineArrangement Line) (l : Line) : Nat :=
  finiteRelationRightDegree (fun q : A.OrdinaryVertex => A.Incident q.1) l

/-- Number of ordinary vertices attached to one indexed arrangement line. -/
noncomputable def lineOrdinaryAttachmentDegree
    (A : FiniteProjectiveLineArrangement Line) (l : Line) : Nat :=
  finiteRelationRightDegree A.OrdinaryVertexAttachedToLine l

/-- Number of indexed lines through a bundled ordinary vertex. -/
noncomputable def ordinaryVertexLineDegree
    (A : FiniteProjectiveLineArrangement Line) (q : A.OrdinaryVertex) : Nat :=
  finiteRelationLeftDegree (fun q : A.OrdinaryVertex => A.Incident q.1) q

/-- Number of indexed lines to which an ordinary vertex is attached. -/
noncomputable def ordinaryVertexAttachmentDegree
    (A : FiniteProjectiveLineArrangement Line) (q : A.OrdinaryVertex) : Nat :=
  finiteRelationLeftDegree A.OrdinaryVertexAttachedToLine q

/-- Two different literal attachment witnesses already give attachment
degree at least two.  This is the finite endpoint needed by the `(1,2+)`
part of the Three-Clause argument. -/
theorem two_le_lineOrdinaryAttachmentDegree_of_distinct
    (A : FiniteProjectiveLineArrangement Line) (l : Line)
    (q r : A.OrdinaryVertex) (hqr : q ≠ r)
    (hq : A.OrdinaryVertexAttachedToLine q l)
    (hr : A.OrdinaryVertexAttachedToLine r l) :
    2 ≤ A.lineOrdinaryAttachmentDegree l := by
  classical
  unfold lineOrdinaryAttachmentDegree finiteRelationRightDegree
  have hsub : ({q, r} : Finset A.OrdinaryVertex) ⊆
      Finset.univ.filter fun x => A.OrdinaryVertexAttachedToLine x l := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hq⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hr⟩
  calc
    2 = ({q, r} : Finset A.OrdinaryVertex).card := by simp [hqr]
    _ ≤ (Finset.univ.filter fun x =>
        A.OrdinaryVertexAttachedToLine x l).card :=
      Finset.card_le_card hsub

/-- Three pairwise different literal attachment witnesses already give
attachment degree at least three.  Thus the geometric `(0,3+)` proof only
has to construct the three actual triangles. -/
theorem three_le_lineOrdinaryAttachmentDegree_of_pairwise
    (A : FiniteProjectiveLineArrangement Line) (l : Line)
    (q r s : A.OrdinaryVertex)
    (hqr : q ≠ r) (hqs : q ≠ s) (hrs : r ≠ s)
    (hq : A.OrdinaryVertexAttachedToLine q l)
    (hr : A.OrdinaryVertexAttachedToLine r l)
    (hs : A.OrdinaryVertexAttachedToLine s l) :
    3 ≤ A.lineOrdinaryAttachmentDegree l := by
  classical
  unfold lineOrdinaryAttachmentDegree finiteRelationRightDegree
  have hsub : ({q, r, s} : Finset A.OrdinaryVertex) ⊆
      Finset.univ.filter fun x => A.OrdinaryVertexAttachedToLine x l := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hq⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hr⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hs⟩
  calc
    3 = ({q, r, s} : Finset A.OrdinaryVertex).card := by
      simp [hqr, hqs, hrs]
    _ ≤ (Finset.univ.filter fun x =>
        A.OrdinaryVertexAttachedToLine x l).card :=
      Finset.card_le_card hsub

/-- A marked point of multiplicity two is counted by the ordinary-vertex
degree of every line on which it lies. -/
theorem one_le_lineOrdinaryVertexDegree_of_circularGap_multiplicity_eq_two
    (A : FiniteProjectiveLineArrangement Line) (l : Line)
    (p : A.CircularGapSlot l) (hp2 : A.multiplicity p.1 = 2) :
    1 ≤ A.lineOrdinaryVertexDegree l := by
  classical
  unfold lineOrdinaryVertexDegree finiteRelationRightDegree
  apply Finset.one_le_card.mpr
  refine ⟨A.circularGapOrdinaryVertex l p hp2, ?_⟩
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
    ((A.mem_lineVertexSet l).mp p.2).2⟩

/-- Consequently a line of ordinary degree zero has no multiplicity-two
marked point.  This is the clean-base condition used by the sector
minimizer in the `(0,3+)` branch. -/
theorem circularGap_multiplicity_ne_two_of_lineOrdinaryVertexDegree_eq_zero
    (A : FiniteProjectiveLineArrangement Line) (l : Line)
    (hzero : A.lineOrdinaryVertexDegree l = 0)
    (p : A.CircularGapSlot l) :
    A.multiplicity p.1 ≠ 2 := by
  intro hp2
  have hpos :=
    A.one_le_lineOrdinaryVertexDegree_of_circularGap_multiplicity_eq_two
      l p hp2
  omega

/-- In the zero-degree branch every marked point of the base line is
therefore a genuine multiple vertex (multiplicity at least three). -/
theorem three_le_circularGap_multiplicity_of_lineOrdinaryVertexDegree_eq_zero
    (A : FiniteProjectiveLineArrangement Line) (l : Line)
    (hzero : A.lineOrdinaryVertexDegree l = 0)
    (p : A.CircularGapSlot l) :
    3 ≤ A.multiplicity p.1 := by
  have hpVertex : p.1 ∈ A.vertexSet :=
    ((A.mem_lineVertexSet l).mp p.2).1
  obtain ⟨a, b, hab, hp⟩ := A.exists_lines_of_mem_vertexSet hpVertex
  have htwo : 2 ≤ A.multiplicity p.1 := by
    rw [← hp]
    exact A.two_le_multiplicity_intersection hab
  have hne :=
    A.circularGap_multiplicity_ne_two_of_lineOrdinaryVertexDegree_eq_zero
      l hzero p
  omega

/-- If a line has ordinary degree one, all of its multiplicity-two marked
points are the same actual projective vertex. -/
theorem circularGap_val_eq_of_lineOrdinaryVertexDegree_eq_one
    (A : FiniteProjectiveLineArrangement Line) (l : Line)
    (hone : A.lineOrdinaryVertexDegree l = 1)
    (p r : A.CircularGapSlot l)
    (hp2 : A.multiplicity p.1 = 2)
    (hr2 : A.multiplicity r.1 = 2) :
    p.1 = r.1 := by
  classical
  let q : A.OrdinaryVertex := A.circularGapOrdinaryVertex l p hp2
  let s : A.OrdinaryVertex := A.circularGapOrdinaryVertex l r hr2
  by_contra hval
  have hqs : q ≠ s := by
    intro h
    apply hval
    simpa only [q, s, circularGapOrdinaryVertex_val] using
      congrArg Subtype.val h
  have hsub : ({q, s} : Finset A.OrdinaryVertex) ⊆
      Finset.univ.filter fun x => A.Incident x.1 l := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        ((A.mem_lineVertexSet l).mp p.2).2⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        ((A.mem_lineVertexSet l).mp r.2).2⟩
  have htwo : 2 ≤ A.lineOrdinaryVertexDegree l := by
    unfold lineOrdinaryVertexDegree finiteRelationRightDegree
    calc
      2 = ({q, s} : Finset A.OrdinaryVertex).card := by simp [hqs]
      _ ≤ (Finset.univ.filter fun x => A.Incident x.1 l).card :=
        Finset.card_le_card hsub
  omega

/-- Degree one can be unpacked as one actual bundled ordinary vertex on the
line, with literal uniqueness. -/
theorem existsUnique_ordinaryVertex_incident_of_lineDegree_eq_one
    (A : FiniteProjectiveLineArrangement Line) (l : Line)
    (hone : A.lineOrdinaryVertexDegree l = 1) :
    ∃! q : A.OrdinaryVertex, A.Incident q.1 l := by
  classical
  let S : Finset A.OrdinaryVertex :=
    Finset.univ.filter fun q => A.Incident q.1 l
  have hcard : S.card = 1 := by
    simpa only [S, lineOrdinaryVertexDegree,
      finiteRelationRightDegree] using hone
  obtain ⟨q, hS⟩ := Finset.card_eq_one.mp hcard
  refine ⟨q, ?_, ?_⟩
  · have hq : q ∈ S := by rw [hS]; simp
    exact (Finset.mem_filter.mp hq).2
  · intro r hrl
    have hr : r ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hrl⟩
    rw [hS] at hr
    exact Finset.mem_singleton.mp hr

/-- Turn a bundled ordinary vertex lying on `l` into the corresponding
marked cyclic slot of `l`. -/
noncomputable def OrdinaryVertex.toCircularGapSlot
    {A : FiniteProjectiveLineArrangement Line} (q : A.OrdinaryVertex)
    (l : Line) (hql : A.Incident q.1 l) : A.CircularGapSlot l := by
  classical
  exact ⟨q.1, (A.mem_lineVertexSet l).2
    ⟨(Finset.mem_filter.mp q.2).1, hql⟩⟩

@[simp]
theorem OrdinaryVertex.toCircularGapSlot_val
    {A : FiniteProjectiveLineArrangement Line} (q : A.OrdinaryVertex)
    (l : Line) (hql : A.Incident q.1 l) :
    (q.toCircularGapSlot l hql).1 = q.1 :=
  rfl

/-- The incidence skeleton used at the start of Felsner's degree-one
argument: the unique ordinary point `p` on the base, its other support `m`,
the next marked point `r` on `m`, and a second support `n` through `r`
returning to a different marked point `q` of the base. -/
structure FelsnerOneLineFrame
    (A : FiniteProjectiveLineArrangement Line) (l : Line) where
  p : A.OrdinaryVertex
  p_on_base : A.Incident p.1 l
  m : Line
  m_ne_base : m ≠ l
  p_on_m : A.Incident p.1 m
  r : RealProjectivePoint
  r_mem_vertexSet : r ∈ A.vertexSet
  r_on_m : A.Incident r m
  r_ne_p : r ≠ p.1
  n : Line
  n_ne_m : n ≠ m
  n_ne_base : n ≠ l
  r_on_n : A.Incident r n
  q : A.CircularGapSlot l
  q_eq_intersection : q.1 = A.intersection l n
  q_ne_p : q.1 ≠ p.1

/-- The degree-one incidence skeleton is available in every non-pencil
arrangement.  No metric or face argument enters this construction. -/
theorem exists_felsnerOneLineFrame_of_lineDegree_eq_one
    (A : FiniteProjectiveLineArrangement Line) (hA : A.NonPencil)
    (l : Line) (hone : A.lineOrdinaryVertexDegree l = 1) :
    Nonempty (FelsnerOneLineFrame A l) := by
  classical
  obtain ⟨p, hpBase, _hpUnique⟩ :=
    A.existsUnique_ordinaryVertex_incident_of_lineDegree_eq_one l hone
  have hp2 : A.multiplicity p.1 = 2 :=
    (Finset.mem_filter.mp p.2).2
  obtain ⟨m, hm, _hmUnique⟩ :=
    A.existsUnique_other_incident_line_of_multiplicity_eq_two
      p.1 l hpBase hp2
  let pm : A.CircularGapSlot m :=
    ⟨p.1, (A.mem_lineVertexSet m).2
      ⟨(Finset.mem_filter.mp p.2).1, hm.2⟩⟩
  let rSlot := A.circularGapSuccessor m pm
  let r : RealProjectivePoint := rSlot.1
  have hrVertex : r ∈ A.vertexSet :=
    ((A.mem_lineVertexSet m).mp rSlot.2).1
  have hrM : A.Incident r m :=
    ((A.mem_lineVertexSet m).mp rSlot.2).2
  have hrp : r ≠ p.1 := by
    simpa only [r, rSlot, pm, A.circularGapEdge_initial,
      A.circularGapEdge_terminal] using
      (A.geometricEdge_initial_ne_terminal_of_nonPencil hA
        (A.circularGapEdge m pm)).symm
  obtain ⟨u, v, huv, huv_r⟩ := A.exists_lines_of_mem_vertexSet hrVertex
  have hru : A.Incident r u := by
    rw [← huv_r]
    exact A.intersection_incident_left huv
  have hrv : A.Incident r v := by
    rw [← huv_r]
    exact A.intersection_incident_right huv
  obtain ⟨n, hnm, hrn⟩ : ∃ n : Line, n ≠ m ∧ A.Incident r n := by
    by_cases hum : u = m
    · exact ⟨v, fun hvm => huv (hum.trans hvm.symm), hrv⟩
    · exact ⟨u, hum, hru⟩
  have hnl : n ≠ l := by
    intro hnl
    apply hrp
    have hrInt : r = A.intersection m l :=
      A.eq_intersection_of_incident hm.1 hrM (hnl ▸ hrn)
    have hpInt : p.1 = A.intersection m l :=
      A.eq_intersection_of_incident hm.1 hm.2 hpBase
    exact hrInt.trans hpInt.symm
  let q : A.CircularGapSlot l :=
    ⟨A.intersection l n,
      A.intersection_mem_lineVertexSet_left hnl.symm⟩
  have hqne : q.1 ≠ p.1 := by
    intro hqp
    have hpn : A.Incident p.1 n := by
      rw [← hqp]
      exact A.intersection_incident_right hnl.symm
    have hexact := A.incident_iff_eq_or_eq_of_multiplicity_eq_two
      p.1 l m hpBase hm.2 hm.1 hp2 n
    rcases hexact.mp hpn with h | h
    · exact hnl h
    · exact hnm h
  exact ⟨{
    p := p
    p_on_base := hpBase
    m := m
    m_ne_base := hm.1
    p_on_m := hm.2
    r := r
    r_mem_vertexSet := hrVertex
    r_on_m := hrM
    r_ne_p := hrp
    n := n
    n_ne_m := hnm
    n_ne_base := hnl
    r_on_n := hrn
    q := q
    q_eq_intersection := rfl
    q_ne_p := hqne
  }⟩

/-- Three marked points on a projective arrangement line provide a third
actual point distinct from any prescribed distinct pair. -/
theorem exists_circularGapSlot_val_ne_pair_of_three_le
    (A : FiniteProjectiveLineArrangement Line) (l : Line)
    (hcard : 3 ≤ Fintype.card (A.CircularGapSlot l))
    (p q : A.CircularGapSlot l) (hpq : p.1 ≠ q.1) :
    ∃ v : A.CircularGapSlot l, v.1 ≠ p.1 ∧ v.1 ≠ q.1 := by
  classical
  by_contra hnone
  have hpqSlot : p ≠ q := by
    intro h
    exact hpq (congrArg Subtype.val h)
  have hsub : (Finset.univ : Finset (A.CircularGapSlot l)) ⊆ {p, q} := by
    intro v _
    by_contra hv
    have hvp : v.1 ≠ p.1 := by
      intro h
      apply hv
      simp only [Finset.mem_insert, Finset.mem_singleton]
      exact Or.inl (Subtype.ext h)
    have hvq : v.1 ≠ q.1 := by
      intro h
      apply hv
      simp only [Finset.mem_insert, Finset.mem_singleton]
      exact Or.inr (Subtype.ext h)
    exact hnone ⟨v, hvp, hvq⟩
  have hle : Fintype.card (A.CircularGapSlot l) ≤ 2 := by
    calc
      Fintype.card (A.CircularGapSlot l) =
          (Finset.univ : Finset (A.CircularGapSlot l)).card := by simp
      _ ≤ ({p, q} : Finset (A.CircularGapSlot l)).card :=
        Finset.card_le_card hsub
      _ = 2 := by simp [hpqSlot]
  omega

/-- Multiplicity at least three supplies three named pairwise distinct
indexed supports through the vertex. -/
theorem exists_three_incident_lines_of_three_le_multiplicity
    (A : FiniteProjectiveLineArrangement Line)
    (q : RealProjectivePoint) (hq : 3 ≤ A.multiplicity q) :
    ∃ a b c : Line,
      a ≠ b ∧ a ≠ c ∧ b ≠ c ∧
      A.Incident q a ∧ A.Incident q b ∧ A.Incident q c := by
  classical
  let I : Finset Line := Finset.univ.filter fun m => A.Incident q m
  have hI : 2 < I.card := by
    change 2 < A.multiplicity q
    omega
  obtain ⟨a, ha, b, hb, c, hc, hab, hac, hbc⟩ :=
    Finset.two_lt_card.mp hI
  exact ⟨a, b, c, hab, hac, hbc,
    (Finset.mem_filter.mp ha).2,
    (Finset.mem_filter.mp hb).2,
    (Finset.mem_filter.mp hc).2⟩

/-- Distinct supports through a point off `l` return to distinct points of
the base line. -/
theorem intersection_base_ne_of_distinct_supports
    (A : FiniteProjectiveLineArrangement Line)
    (q : RealProjectivePoint) (l a b : Line)
    (hql : ¬ A.Incident q l)
    (hqa : A.Incident q a) (hqb : A.Incident q b)
    (hab : a ≠ b) :
    A.intersection l a ≠ A.intersection l b := by
  have hal : l ≠ a := by
    intro h
    apply hql
    rw [h]
    exact hqa
  have hbl : l ≠ b := by
    intro h
    apply hql
    rw [h]
    exact hqb
  intro hsame
  have hq : q = A.intersection a b :=
    A.eq_intersection_of_incident hab hqa hqb
  have hpA : A.Incident (A.intersection l a) a :=
    A.intersection_incident_right hal
  have hpB : A.Incident (A.intersection l a) b := by
    rw [hsame]
    exact A.intersection_incident_right hbl
  have hp : A.intersection l a = A.intersection a b :=
    A.eq_intersection_of_incident hab hpA hpB
  apply hql
  rw [hq, ← hp]
  exact A.intersection_incident_left hal

/-- A multiplicity-at-least-three point incident with two distinct named
lines has a third indexed support. -/
theorem exists_third_incident_line_of_three_le_multiplicity
    (A : FiniteProjectiveLineArrangement Line)
    (q : RealProjectivePoint) (l c : Line)
    (hlc : l ≠ c) (hql : A.Incident q l) (hqc : A.Incident q c)
    (hq3 : 3 ≤ A.multiplicity q) :
    ∃ m : Line, m ≠ l ∧ m ≠ c ∧ A.Incident q m := by
  classical
  let I : Finset Line := Finset.univ.filter fun m => A.Incident q m
  by_contra hnone
  have hsub : I ⊆ {l, c} := by
    intro m hm
    by_contra hmem
    have hml : m ≠ l := by
      intro h
      apply hmem
      simp [h]
    have hmc : m ≠ c := by
      intro h
      apply hmem
      simp [h]
    exact hnone ⟨m, hml, hmc, (Finset.mem_filter.mp hm).2⟩
  have hcard : A.multiplicity q ≤ 2 := by
    change I.card ≤ 2
    calc
      I.card ≤ ({l, c} : Finset Line).card := Finset.card_le_card hsub
      _ = 2 := by simp [hlc]
  omega

/-- On a zero-ordinary base, every transverse return point has an indexed
support besides the base and the returning line. -/
theorem exists_extra_line_at_base_return_of_lineDegree_eq_zero
    (A : FiniteProjectiveLineArrangement Line)
    (l c : Line) (hzero : A.lineOrdinaryVertexDegree l = 0)
    (hlc : l ≠ c) :
    ∃ m : Line, m ≠ l ∧ m ≠ c ∧
      A.Incident (A.intersection l c) m := by
  let p : A.CircularGapSlot l :=
    ⟨A.intersection l c, A.intersection_mem_lineVertexSet_left hlc⟩
  have hp3 : 3 ≤ A.multiplicity p.1 :=
    A.three_le_circularGap_multiplicity_of_lineOrdinaryVertexDegree_eq_zero
      l hzero p
  exact A.exists_third_incident_line_of_three_le_multiplicity
    p.1 l c hlc
      (A.intersection_incident_left hlc)
      (A.intersection_incident_right hlc) hp3

/-! ## The affine gauge for the Felsner sector minimizer -/

/-- A single affine-chart covector can be chosen nonzero on every actual
arrangement vertex.  This is the finite-hyperplane avoidance needed to make
Felsner's first "closest vertex to `l`" selection honest in projective
coordinates. -/
theorem exists_vertexChartCovector
    (A : FiniteProjectiveLineArrangement Line) :
    ∃ f : (Fin 3 -> ℝ) →ₗ[ℝ] ℝ,
      ∀ q : RealProjectivePoint, q ∈ A.vertexSet -> f q.rep ≠ 0 := by
  classical
  obtain ⟨f, hf⟩ := Module.exists_dual_forall_apply_ne_zero
    (K := ℝ) (M := Fin 3 → ℝ)
    (fun q : {q // q ∈ A.vertexSet} => q.1.rep)
    (fun q => q.1.rep_nonzero)
  exact ⟨f, fun q hq => hf ⟨q, hq⟩⟩

/-- In a non-pencil arrangement every indexed line misses some actual
vertex. -/
theorem exists_vertex_not_incident_line
    (A : FiniteProjectiveLineArrangement Line) (hA : A.NonPencil)
    (l : Line) :
    ∃ q : RealProjectivePoint, q ∈ A.vertexSet ∧ ¬ A.Incident q l := by
  obtain ⟨m, hml⟩ := A.exists_ne_line_of_nonPencil hA l
  let p := A.intersection l m
  have hpm : A.Incident p m :=
    A.intersection_incident_right hml.symm
  obtain ⟨n, hpn⟩ := A.exists_not_incident_line_of_nonPencil hA p
  have hmn : m ≠ n := by
    intro hmn
    apply hpn
    simpa only [hmn] using hpm
  let q := A.intersection m n
  have hqm : A.Incident q m := A.intersection_incident_left hmn
  have hqn : A.Incident q n := A.intersection_incident_right hmn
  refine ⟨q, A.intersection_mem_vertexSet hmn, ?_⟩
  intro hql
  have hqp : q = p :=
    A.eq_intersection_of_incident hml.symm hql hqm
  apply hpn
  rw [← hqp]
  exact hqn

/-- The finite set of vertices off a specified line is nonempty in the
non-pencil case. -/
theorem offLineVertexSet_nonempty
    (A : FiniteProjectiveLineArrangement Line) (hA : A.NonPencil)
    (l : Line) :
    (A.vertexSet.filter fun q => ¬ A.Incident q l).Nonempty := by
  classical
  obtain ⟨q, hqVertex, hql⟩ := A.exists_vertex_not_incident_line hA l
  exact ⟨q, Finset.mem_filter.mpr ⟨hqVertex, hql⟩⟩

/-- Normalize a vertex in a chart whose covector is nonzero there. -/
noncomputable def vertexChartNormalizedVector
    (f : (Fin 3 -> ℝ) →ₗ[ℝ] ℝ) (q : RealProjectivePoint) : Fin 3 -> ℝ :=
  (f q.rep)⁻¹ • q.rep

theorem vertexChartNormalizedVector_ne_zero
    (f : (Fin 3 -> ℝ) →ₗ[ℝ] ℝ) (q : RealProjectivePoint)
    (hf : f q.rep ≠ 0) :
    vertexChartNormalizedVector f q ≠ 0 := by
  intro hzero
  unfold vertexChartNormalizedVector at hzero
  rcases smul_eq_zero.mp hzero with hscalar | hvector
  · exact (inv_ne_zero hf) hscalar
  · exact q.rep_nonzero hvector

theorem projectivization_mk_vertexChartNormalizedVector
    (f : (Fin 3 -> ℝ) →ₗ[ℝ] ℝ) (q : RealProjectivePoint)
    (hf : f q.rep ≠ 0) :
    Projectivization.mk ℝ (vertexChartNormalizedVector f q)
      (vertexChartNormalizedVector_ne_zero f q hf) = q := by
  calc
    Projectivization.mk ℝ (vertexChartNormalizedVector f q)
        (vertexChartNormalizedVector_ne_zero f q hf) =
        Projectivization.mk ℝ q.rep q.rep_nonzero := by
      apply (Projectivization.mk_eq_mk_iff' ℝ _ _ _ _).mpr
      exact ⟨(f q.rep)⁻¹, rfl⟩
    _ = q := q.mk_rep

/-- Absolute affine height above an indexed base line in a fixed vertex
chart.  Multiplying by the constant norm of the base covector would give
the usual Euclidean distance, so this has exactly the same minimizers. -/
noncomputable def vertexChartLineHeight
    (A : FiniteProjectiveLineArrangement Line)
    (f : (Fin 3 -> ℝ) →ₗ[ℝ] ℝ) (l : Line)
    (q : RealProjectivePoint) : ℝ :=
  |projectiveLineEvaluation (A.projectiveLine l)
    (vertexChartNormalizedVector f q)|

/-- The finite-selection part of Felsner's first closest-vertex argument. -/
theorem exists_minimal_vertexChartLineHeight
    (A : FiniteProjectiveLineArrangement Line)
    (f : (Fin 3 -> ℝ) →ₗ[ℝ] ℝ) (l : Line)
    (S : Finset RealProjectivePoint) (hS : S.Nonempty) :
    ∃ q ∈ S, ∀ r ∈ S,
      A.vertexChartLineHeight f l q ≤ A.vertexChartLineHeight f l r := by
  exact S.exists_min_image (A.vertexChartLineHeight f l) hS

/-- A vertex missed by the base has strictly positive height in a chart
which contains every arrangement vertex. -/
theorem vertexChartLineHeight_pos
    (A : FiniteProjectiveLineArrangement Line)
    (f : (Fin 3 -> ℝ) →ₗ[ℝ] ℝ) (l : Line)
    (q : RealProjectivePoint) (hf : f q.rep ≠ 0)
    (hql : ¬ A.Incident q l) :
    0 < A.vertexChartLineHeight f l q := by
  unfold vertexChartLineHeight vertexChartNormalizedVector
  rw [LinearMap.map_smul]
  apply abs_pos.mpr
  simpa only [smul_eq_mul] using mul_ne_zero (inv_ne_zero hf)
    ((A.projectiveLineEvaluation_rep_eq_zero_iff_incident q l).not.mpr hql)

/-- Felsner's first closest point exists without a metric choice: choose one
affine chart containing all actual vertices and minimize absolute base
evaluation on the finite set of vertices off the base. -/
theorem exists_closest_offLineVertex
    (A : FiniteProjectiveLineArrangement Line) (hA : A.NonPencil)
    (l : Line) :
    ∃ f : (Fin 3 -> ℝ) →ₗ[ℝ] ℝ,
      (∀ r : RealProjectivePoint, r ∈ A.vertexSet -> f r.rep ≠ 0) ∧
      ∃ q : RealProjectivePoint,
        q ∈ A.vertexSet ∧ ¬ A.Incident q l ∧
        0 < A.vertexChartLineHeight f l q ∧
        ∀ r : RealProjectivePoint, r ∈ A.vertexSet ->
          ¬ A.Incident r l ->
          A.vertexChartLineHeight f l q ≤
            A.vertexChartLineHeight f l r := by
  classical
  obtain ⟨f, hf⟩ := A.exists_vertexChartCovector
  let S := A.vertexSet.filter fun q => ¬ A.Incident q l
  have hS : S.Nonempty := A.offLineVertexSet_nonempty hA l
  obtain ⟨q, hqS, hmin⟩ :=
    A.exists_minimal_vertexChartLineHeight f l S hS
  have hq := Finset.mem_filter.mp hqS
  refine ⟨f, hf, q, hq.1, hq.2,
    A.vertexChartLineHeight_pos f l q (hf q hq.1) hq.2, ?_⟩
  intro r hrVertex hrl
  exact hmin r (Finset.mem_filter.mpr ⟨hrVertex, hrl⟩)

/-- The sum of the three inward-oriented side evaluations of a projective
triangle.  On a pointed closed three-half-space sector this is positive away
from the origin, so it provides the affine normalization needed by the
Kelly--Felsner closest-vertex argument without choosing a Euclidean metric. -/
noncomputable def triangleSectorGauge
    (A : FiniteProjectiveLineArrangement Line) (sigma : Line -> Bool)
    (l a b : Line) (v : Fin 3 -> ℝ) : ℝ :=
  A.arrangementOrientedEvaluation sigma l v +
    A.arrangementOrientedEvaluation sigma a v +
      A.arrangementOrientedEvaluation sigma b v

/-- If the three supporting lines have no common projective point, their
oriented evaluations have trivial common kernel. -/
theorem eq_zero_of_three_orientedEvaluations_eq_zero
    (A : FiniteProjectiveLineArrangement Line) (sigma : Line -> Bool)
    (l a b : Line)
    (htriangle : ¬ ∃ q : RealProjectivePoint,
      A.Incident q l ∧ A.Incident q a ∧ A.Incident q b)
    (v : Fin 3 -> ℝ)
    (hl : A.arrangementOrientedEvaluation sigma l v = 0)
    (ha : A.arrangementOrientedEvaluation sigma a v = 0)
    (hb : A.arrangementOrientedEvaluation sigma b v = 0) :
    v = 0 := by
  by_contra hv
  apply htriangle
  refine ⟨Projectivization.mk ℝ v hv, ?_, ?_, ?_⟩
  · exact (A.incident_projectivization_mk_iff_orientedEvaluation_eq_zero
      sigma l v hv).2 hl
  · exact (A.incident_projectivization_mk_iff_orientedEvaluation_eq_zero
      sigma a v hv).2 ha
  · exact (A.incident_projectivization_mk_iff_orientedEvaluation_eq_zero
      sigma b v hv).2 hb

/-- The triangle gauge is strictly positive on every nonzero vector in the
closed sector cut out by its three sides. -/
theorem triangleSectorGauge_pos
    (A : FiniteProjectiveLineArrangement Line) (sigma : Line -> Bool)
    (l a b : Line)
    (htriangle : ¬ ∃ q : RealProjectivePoint,
      A.Incident q l ∧ A.Incident q a ∧ A.Incident q b)
    {v : Fin 3 -> ℝ} (hv : v ≠ 0)
    (hsector : v ∈ A.arrangementClosedSignConeOn sigma {l, a, b}) :
    0 < A.triangleSectorGauge sigma l a b v := by
  have hl : 0 ≤ A.arrangementOrientedEvaluation sigma l v :=
    hsector l (by simp)
  have ha : 0 ≤ A.arrangementOrientedEvaluation sigma a v :=
    hsector a (by simp)
  have hb : 0 ≤ A.arrangementOrientedEvaluation sigma b v :=
    hsector b (by simp)
  by_contra hnot
  have hsum : A.triangleSectorGauge sigma l a b v ≤ 0 :=
    le_of_not_gt hnot
  have hl0 : A.arrangementOrientedEvaluation sigma l v = 0 := by
    unfold triangleSectorGauge at hsum
    linarith
  have ha0 : A.arrangementOrientedEvaluation sigma a v = 0 := by
    unfold triangleSectorGauge at hsum
    linarith
  have hb0 : A.arrangementOrientedEvaluation sigma b v = 0 := by
    unfold triangleSectorGauge at hsum
    linarith
  exact hv (A.eq_zero_of_three_orientedEvaluations_eq_zero
    sigma l a b htriangle v hl0 ha0 hb0)

/-- The three oriented side covectors, viewed as affine barycentric
coordinates before gauge normalization. -/
def triangleSectorSide (l a b : Line) : Fin 3 -> Line :=
  ![l, a, b]

noncomputable def triangleSectorCoordinateMap
    (A : FiniteProjectiveLineArrangement Line) (sigma : Line -> Bool)
    (l a b : Line) : (Fin 3 -> ℝ) →ₗ[ℝ] (Fin 3 -> ℝ) :=
  LinearMap.pi fun i =>
    A.arrangementOrientedEvaluation sigma (triangleSectorSide l a b i)

@[simp]
theorem triangleSectorCoordinateMap_apply
    (A : FiniteProjectiveLineArrangement Line) (sigma : Line -> Bool)
    (l a b : Line) (v : Fin 3 -> ℝ) (i : Fin 3) :
    A.triangleSectorCoordinateMap sigma l a b v i =
      A.arrangementOrientedEvaluation sigma
        (triangleSectorSide l a b i) v :=
  rfl

/-- Nonconcurrency makes the three side evaluations a genuine coordinate
system on homogeneous vectors. -/
theorem triangleSectorCoordinateMap_injective
    (A : FiniteProjectiveLineArrangement Line) (sigma : Line -> Bool)
    (l a b : Line)
    (htriangle : ¬ ∃ q : RealProjectivePoint,
      A.Incident q l ∧ A.Incident q a ∧ A.Incident q b) :
    Function.Injective (A.triangleSectorCoordinateMap sigma l a b) := by
  intro v w hvw
  have hl : A.arrangementOrientedEvaluation sigma l v =
      A.arrangementOrientedEvaluation sigma l w := by
    have h := congrFun hvw (0 : Fin 3)
    simpa [triangleSectorCoordinateMap, triangleSectorSide] using h
  have ha : A.arrangementOrientedEvaluation sigma a v =
      A.arrangementOrientedEvaluation sigma a w := by
    have h := congrFun hvw (1 : Fin 3)
    simpa [triangleSectorCoordinateMap, triangleSectorSide] using h
  have hb : A.arrangementOrientedEvaluation sigma b v =
      A.arrangementOrientedEvaluation sigma b w := by
    have h := congrFun hvw (2 : Fin 3)
    simpa [triangleSectorCoordinateMap, triangleSectorSide] using h
  apply sub_eq_zero.mp
  apply A.eq_zero_of_three_orientedEvaluations_eq_zero
    sigma l a b htriangle (v - w)
  · rw [LinearMap.map_sub, hl, sub_self]
  · rw [LinearMap.map_sub, ha, sub_self]
  · rw [LinearMap.map_sub, hb, sub_self]

/-- The homogeneous coordinate equivalence attached to a nonconcurrent
triple of projective side lines. -/
noncomputable def triangleSectorCoordinateEquiv
    (A : FiniteProjectiveLineArrangement Line) (sigma : Line -> Bool)
    (l a b : Line)
    (htriangle : ¬ ∃ q : RealProjectivePoint,
      A.Incident q l ∧ A.Incident q a ∧ A.Incident q b) :
    (Fin 3 -> ℝ) ≃ₗ[ℝ] (Fin 3 -> ℝ) :=
  LinearEquiv.ofInjectiveEndo
    (A.triangleSectorCoordinateMap sigma l a b)
    (A.triangleSectorCoordinateMap_injective
      sigma l a b htriangle)

/-- Gauge-one representative used to compare the heights of projective
vertices in one fixed triangle sector. -/
noncomputable def triangleSectorNormalizedVector
    (A : FiniteProjectiveLineArrangement Line) (sigma : Line -> Bool)
    (l a b : Line) (v : Fin 3 -> ℝ) : Fin 3 -> ℝ :=
  (A.triangleSectorGauge sigma l a b v)⁻¹ • v

theorem triangleSectorGauge_smul
    (A : FiniteProjectiveLineArrangement Line) (sigma : Line -> Bool)
    (l a b : Line) (c : ℝ) (v : Fin 3 -> ℝ) :
    A.triangleSectorGauge sigma l a b (c • v) =
      c * A.triangleSectorGauge sigma l a b v := by
  simp only [triangleSectorGauge, LinearMap.map_smul, smul_eq_mul]
  ring

theorem triangleSectorNormalizedVector_ne_zero
    (A : FiniteProjectiveLineArrangement Line) (sigma : Line -> Bool)
    (l a b : Line) {v : Fin 3 -> ℝ} (hv : v ≠ 0)
    (hg : A.triangleSectorGauge sigma l a b v ≠ 0) :
    A.triangleSectorNormalizedVector sigma l a b v ≠ 0 := by
  intro hzero
  unfold triangleSectorNormalizedVector at hzero
  rcases smul_eq_zero.mp hzero with hscalar | hvector
  · exact (inv_ne_zero hg) hscalar
  · exact hv hvector

/-- Gauge normalization really lands in the affine slice of gauge one. -/
theorem triangleSectorGauge_normalizedVector
    (A : FiniteProjectiveLineArrangement Line) (sigma : Line -> Bool)
    (l a b : Line) {v : Fin 3 -> ℝ}
    (hg : A.triangleSectorGauge sigma l a b v ≠ 0) :
    A.triangleSectorGauge sigma l a b
      (A.triangleSectorNormalizedVector sigma l a b v) = 1 := by
  rw [triangleSectorNormalizedVector, A.triangleSectorGauge_smul]
  exact inv_mul_cancel₀ hg

/-- Gauge normalization changes only the homogeneous representative, not
the underlying projective point. -/
theorem projectivization_mk_triangleSectorNormalizedVector
    (A : FiniteProjectiveLineArrangement Line) (sigma : Line -> Bool)
    (l a b : Line) (q : RealProjectivePoint)
    (hg : A.triangleSectorGauge sigma l a b q.rep ≠ 0) :
    Projectivization.mk ℝ
      (A.triangleSectorNormalizedVector sigma l a b q.rep)
      (A.triangleSectorNormalizedVector_ne_zero
        sigma l a b q.rep_nonzero hg) = q := by
  calc
    Projectivization.mk ℝ
        (A.triangleSectorNormalizedVector sigma l a b q.rep)
        (A.triangleSectorNormalizedVector_ne_zero
          sigma l a b q.rep_nonzero hg) =
        Projectivization.mk ℝ q.rep q.rep_nonzero := by
      apply (Projectivization.mk_eq_mk_iff' ℝ _ _ _ _).mpr
      exact ⟨(A.triangleSectorGauge sigma l a b q.rep)⁻¹, rfl⟩
    _ = q := q.mk_rep

/-- Positive gauge rescaling preserves all three weak side inequalities. -/
theorem triangleSectorNormalizedVector_mem
    (A : FiniteProjectiveLineArrangement Line) (sigma : Line -> Bool)
    (l a b : Line) {v : Fin 3 -> ℝ}
    (hg : 0 < A.triangleSectorGauge sigma l a b v)
    (hsector : v ∈ A.arrangementClosedSignConeOn sigma {l, a, b}) :
    A.triangleSectorNormalizedVector sigma l a b v ∈
      A.arrangementClosedSignConeOn sigma {l, a, b} := by
  intro m hm
  rw [triangleSectorNormalizedVector, LinearMap.map_smul]
  simpa only [smul_eq_mul] using
    mul_nonneg (inv_nonneg.mpr hg.le) (hsector m hm)

/-- Projectively invariant membership in one of the two homogeneous lifts of
the closed triangle sector. -/
def projectivePointMemTriangleSector
    (A : FiniteProjectiveLineArrangement Line) (sigma : Line -> Bool)
    (l a b : Line) (q : RealProjectivePoint) : Prop :=
  q.rep ∈ A.arrangementClosedSignConeOn sigma {l, a, b} ∨
    -q.rep ∈ A.arrangementClosedSignConeOn sigma {l, a, b}

/-- Gauge normalization is unchanged when the homogeneous representative is
negated. -/
theorem triangleSectorNormalizedVector_neg
    (A : FiniteProjectiveLineArrangement Line) (sigma : Line -> Bool)
    (l a b : Line) (v : Fin 3 -> ℝ) :
    A.triangleSectorNormalizedVector sigma l a b (-v) =
      A.triangleSectorNormalizedVector sigma l a b v := by
  unfold triangleSectorNormalizedVector
  rw [show -v = (-1 : ℝ) • v by simp,
    A.triangleSectorGauge_smul]
  simp [smul_smul]

/-- Either homogeneous lift of a projective sector point normalizes into the
chosen positive closed cone. -/
theorem triangleSectorNormalizedVector_mem_of_projective
    (A : FiniteProjectiveLineArrangement Line) (sigma : Line -> Bool)
    (l a b : Line)
    (htriangle : ¬ ∃ q : RealProjectivePoint,
      A.Incident q l ∧ A.Incident q a ∧ A.Incident q b)
    (q : RealProjectivePoint)
    (hq : A.projectivePointMemTriangleSector sigma l a b q) :
    A.triangleSectorNormalizedVector sigma l a b q.rep ∈
      A.arrangementClosedSignConeOn sigma {l, a, b} := by
  rcases hq with hq | hq
  · exact A.triangleSectorNormalizedVector_mem sigma l a b
      (A.triangleSectorGauge_pos sigma l a b htriangle
        q.rep_nonzero hq) hq
  · have hneg := A.triangleSectorNormalizedVector_mem sigma l a b
      (A.triangleSectorGauge_pos sigma l a b htriangle
        (neg_ne_zero.mpr q.rep_nonzero) hq) hq
    rwa [A.triangleSectorNormalizedVector_neg] at hneg

theorem triangleSectorGauge_ne_zero_of_projective
    (A : FiniteProjectiveLineArrangement Line) (sigma : Line -> Bool)
    (l a b : Line)
    (htriangle : ¬ ∃ q : RealProjectivePoint,
      A.Incident q l ∧ A.Incident q a ∧ A.Incident q b)
    (q : RealProjectivePoint)
    (hq : A.projectivePointMemTriangleSector sigma l a b q) :
    A.triangleSectorGauge sigma l a b q.rep ≠ 0 := by
  rcases hq with hq | hq
  · exact ne_of_gt (A.triangleSectorGauge_pos sigma l a b htriangle
      q.rep_nonzero hq)
  · have hpos := A.triangleSectorGauge_pos sigma l a b htriangle
      (neg_ne_zero.mpr q.rep_nonzero) hq
    have hneg : A.triangleSectorGauge sigma l a b (-q.rep) =
        -A.triangleSectorGauge sigma l a b q.rep := by
      rw [show -q.rep = (-1 : ℝ) • q.rep by simp,
        A.triangleSectorGauge_smul]
      simp
    intro hzero
    rw [hneg, hzero, neg_zero] at hpos
    exact (lt_irrefl 0 hpos)

/-- The inward evaluation of the base side is the projectively meaningful
height after gauge normalization. -/
noncomputable def triangleSectorHeight
    (A : FiniteProjectiveLineArrangement Line) (sigma : Line -> Bool)
    (l a b : Line) (q : RealProjectivePoint) : ℝ :=
  A.arrangementOrientedEvaluation sigma l
    (A.triangleSectorNormalizedVector sigma l a b q.rep)

/-- Positivity of normalized height in the projectively invariant sector. -/
theorem triangleSectorHeight_pos_of_projective
    (A : FiniteProjectiveLineArrangement Line) (sigma : Line -> Bool)
    (l a b : Line)
    (htriangle : ¬ ∃ q : RealProjectivePoint,
      A.Incident q l ∧ A.Incident q a ∧ A.Incident q b)
    (q : RealProjectivePoint)
    (hq : A.projectivePointMemTriangleSector sigma l a b q)
    (hql : ¬ A.Incident q l) :
    0 < A.triangleSectorHeight sigma l a b q := by
  have hqNorm := A.triangleSectorNormalizedVector_mem_of_projective
    sigma l a b htriangle q hq
  have hg := A.triangleSectorGauge_ne_zero_of_projective
    sigma l a b htriangle q hq
  have hl : 0 ≤ A.arrangementOrientedEvaluation sigma l
      (A.triangleSectorNormalizedVector sigma l a b q.rep) :=
    hqNorm l (by simp)
  have hlne : A.arrangementOrientedEvaluation sigma l
      (A.triangleSectorNormalizedVector sigma l a b q.rep) ≠ 0 := by
    intro hzero
    apply hql
    have hinc : A.Incident
        (Projectivization.mk ℝ
          (A.triangleSectorNormalizedVector sigma l a b q.rep)
          (A.triangleSectorNormalizedVector_ne_zero
            sigma l a b q.rep_nonzero hg)) l :=
      (A.incident_projectivization_mk_iff_orientedEvaluation_eq_zero
        sigma l _ _).2 hzero
    rwa [A.projectivization_mk_triangleSectorNormalizedVector
      sigma l a b q hg] at hinc
  exact lt_of_le_of_ne hl hlne.symm

/-- A projective sector point away from the base has strictly positive
normalized base height. -/
theorem triangleSectorHeight_pos
    (A : FiniteProjectiveLineArrangement Line) (sigma : Line -> Bool)
    (l a b : Line)
    (htriangle : ¬ ∃ q : RealProjectivePoint,
      A.Incident q l ∧ A.Incident q a ∧ A.Incident q b)
    (q : RealProjectivePoint)
    (hsector : q.rep ∈ A.arrangementClosedSignConeOn sigma {l, a, b})
    (hql : ¬ A.Incident q l) :
    0 < A.triangleSectorHeight sigma l a b q := by
  have hg := A.triangleSectorGauge_pos sigma l a b htriangle
    q.rep_nonzero hsector
  have hl : 0 ≤ A.arrangementOrientedEvaluation sigma l q.rep :=
    hsector l (by simp)
  have hlne : A.arrangementOrientedEvaluation sigma l q.rep ≠ 0 := by
    intro hzero
    apply hql
    simpa only [q.mk_rep] using
      (A.incident_projectivization_mk_iff_orientedEvaluation_eq_zero
        sigma l q.rep q.rep_nonzero).2 hzero
  have hlpos : 0 < A.arrangementOrientedEvaluation sigma l q.rep :=
    lt_of_le_of_ne hl hlne.symm
  unfold triangleSectorHeight triangleSectorNormalizedVector
  rw [LinearMap.map_smul]
  simpa only [smul_eq_mul] using mul_pos (inv_pos.mpr hg) hlpos

/-- Every nonempty finite candidate set has a vertex of minimum normalized
base height.  This is the finite-selection half of Felsner's sector lemma;
the remaining geometric step is the strict-height decrease at a nonordinary
selected vertex. -/
theorem exists_minimal_triangleSectorHeight
    (A : FiniteProjectiveLineArrangement Line) (sigma : Line -> Bool)
    (l a b : Line) (S : Finset RealProjectivePoint) (hS : S.Nonempty) :
    ∃ q ∈ S, ∀ r ∈ S,
      A.triangleSectorHeight sigma l a b q ≤
        A.triangleSectorHeight sigma l a b r := by
  exact S.exists_min_image
    (A.triangleSectorHeight sigma l a b) hS

/-- Actual arrangement vertices in the closed projective triangle sector but
away from its base. -/
noncomputable def triangleSectorOffBaseVertexSet
    (A : FiniteProjectiveLineArrangement Line) (sigma : Line -> Bool)
    (l a b : Line) : Finset RealProjectivePoint := by
  classical
  exact A.vertexSet.filter fun q =>
    A.projectivePointMemTriangleSector sigma l a b q ∧
      ¬ A.Incident q l

/-- Fully unpacked finite minimizer in a projective triangle sector. -/
theorem exists_minimal_projectiveTriangleSectorHeight
    (A : FiniteProjectiveLineArrangement Line) (sigma : Line -> Bool)
    (l a b : Line)
    (htriangle : ¬ ∃ q : RealProjectivePoint,
      A.Incident q l ∧ A.Incident q a ∧ A.Incident q b)
    (hS : (A.triangleSectorOffBaseVertexSet sigma l a b).Nonempty) :
    ∃ q : RealProjectivePoint,
      q ∈ A.vertexSet ∧
      A.projectivePointMemTriangleSector sigma l a b q ∧
      ¬ A.Incident q l ∧
      0 < A.triangleSectorHeight sigma l a b q ∧
      ∀ r : RealProjectivePoint, r ∈ A.vertexSet ->
        A.projectivePointMemTriangleSector sigma l a b r ->
        ¬ A.Incident r l ->
        A.triangleSectorHeight sigma l a b q ≤
          A.triangleSectorHeight sigma l a b r := by
  classical
  obtain ⟨q, hqS, hmin⟩ := A.exists_minimal_triangleSectorHeight
    sigma l a b (A.triangleSectorOffBaseVertexSet sigma l a b) hS
  have hq := Finset.mem_filter.mp hqS
  refine ⟨q, hq.1, hq.2.1, hq.2.2,
    A.triangleSectorHeight_pos_of_projective
      sigma l a b htriangle q hq.2.1 hq.2.2, ?_⟩
  intro r hrVertex hrSector hrl
  exact hmin r (Finset.mem_filter.mpr
    ⟨hrVertex, hrSector, hrl⟩)

/-- Bundling a multiplicity-two vertex does not change its incident-line
degree. -/
theorem ordinaryVertexLineDegree_eq_two
    (A : FiniteProjectiveLineArrangement Line) (q : A.OrdinaryVertex) :
    A.ordinaryVertexLineDegree q = 2 := by
  classical
  have hq : A.multiplicity q.1 = 2 :=
    (Finset.mem_filter.mp q.2).2
  simpa [ordinaryVertexLineDegree, finiteRelationLeftDegree,
    FiniteProjectiveLineArrangement.multiplicity] using hq

/-- The two indexed lines through an ordinary vertex, with an exact
incidence characterization. -/
theorem exists_two_lines_incident_iff_of_ordinaryVertex
    (A : FiniteProjectiveLineArrangement Line) (q : A.OrdinaryVertex) :
    ∃ a b : Line, a ≠ b ∧ ∀ l : Line,
      A.Incident q.1 l ↔ l = a ∨ l = b := by
  classical
  have hqVertex : q.1 ∈ A.vertexSet :=
    (Finset.mem_filter.mp q.2).1
  have hqTwo : A.multiplicity q.1 = 2 :=
    (Finset.mem_filter.mp q.2).2
  obtain ⟨a, b, hab, habq⟩ := A.exists_lines_of_mem_vertexSet hqVertex
  have hqa : A.Incident q.1 a := by
    rw [← habq]
    exact A.intersection_incident_left hab
  have hqb : A.Incident q.1 b := by
    rw [← habq]
    exact A.intersection_incident_right hab
  obtain ⟨c, hc, hunique⟩ :=
    A.existsUnique_other_incident_line_of_multiplicity_eq_two
      q.1 a hqa hqTwo
  have hbc : b = c := hunique b ⟨hab.symm, hqb⟩
  refine ⟨a, b, hab, fun l => ?_⟩
  constructor
  · intro hql
    by_cases hla : l = a
    · exact Or.inl hla
    · exact Or.inr ((hunique l ⟨hla, hql⟩).trans hbc.symm)
  · rintro (rfl | rfl)
    · exact hqa
    · exact hqb

/-- Read the two side supports and the two base endpoints from a literal
attachment triangle.  This is the incidence-only frame used in Felsner's
outer `(0,3+)` construction. -/
theorem OrdinaryAttachmentWitness.exists_sideSupports
    (A : FiniteProjectiveLineArrangement Line) (hA : A.NonPencil)
    {q : A.OrdinaryVertex} {l : Line}
    (w : OrdinaryAttachmentWitness A q l) :
    ∃ a b : Line, a ≠ b ∧ a ≠ l ∧ b ≠ l ∧
      A.Incident q.1 a ∧ A.Incident q.1 b ∧
      ({A.geometricEdgeInitial w.base,
          A.geometricEdgeTerminal w.base} : Finset RealProjectivePoint) =
        {A.intersection l a, A.intersection l b} := by
  classical
  obtain ⟨a, b, hab, hincident⟩ :=
    A.exists_two_lines_incident_iff_of_ordinaryVertex q
  have hqa : A.Incident q.1 a := (hincident a).2 (Or.inl rfl)
  have hqb : A.Incident q.1 b := (hincident b).2 (Or.inr rfl)
  have hal : a ≠ l := by
    intro h
    apply w.away
    simpa only [h] using hqa
  have hbl : b ≠ l := by
    intro h
    apply w.away
    simpa only [h] using hqb
  have hincidentBA : ∀ c : Line,
      A.Incident q.1 c ↔ c = b ∨ c = a := by
    intro c
    rw [hincident c, or_comm]
  obtain ⟨edgeB, hedgeBLine, hedgeBMem⟩ :=
    A.exists_transverse_boundaryEdge_of_mem_closure_of_ordinary_intersection
      hA w.face q.1 a b hab.symm hqa hqb hincident w.opposite
  obtain ⟨edgeA, hedgeALine, hedgeAMem⟩ :=
    A.exists_transverse_boundaryEdge_of_mem_closure_of_ordinary_intersection
      hA w.face q.1 b a hab hqb hqa hincidentBA w.opposite
  have hedgeAB : edgeA ≠ edgeB := by
    intro h
    apply hab
    calc
      a = A.edgeSlotLine edgeA := hedgeALine.symm
      _ = A.edgeSlotLine edgeB := congrArg A.edgeSlotLine h
      _ = b := hedgeBLine
  have hbaseA : w.base ≠ edgeA := by
    intro h
    apply hal
    calc
      a = A.edgeSlotLine edgeA := hedgeALine.symm
      _ = A.edgeSlotLine w.base := congrArg A.edgeSlotLine h.symm
      _ = l := w.base_line
  have hbaseB : w.base ≠ edgeB := by
    intro h
    apply hbl
    calc
      b = A.edgeSlotLine edgeB := hedgeBLine.symm
      _ = A.edgeSlotLine w.base := congrArg A.edgeSlotLine h.symm
      _ = l := w.base_line
  have hsub : ({w.base, edgeA, edgeB} : Finset A.GeometricEdge) ⊆
      A.arrangementFaceBoundary w.face := by
    intro e he
    simp only [Finset.mem_insert, Finset.mem_singleton] at he
    rcases he with rfl | rfl | rfl
    · exact w.base_mem
    · exact hedgeAMem
    · exact hedgeBMem
  have htriple : ({w.base, edgeA, edgeB} :
      Finset A.GeometricEdge).card = 3 := by
    simp [hedgeAB, hbaseA, hbaseB]
  have hboundary : A.arrangementFaceBoundary w.face =
      {w.base, edgeA, edgeB} := by
    symm
    apply Finset.eq_of_subset_of_card_le hsub
    rw [w.triangular, htriple]
  have hpairs := A.geometricEdge_endpoint_pair_eq_of_exact_triangle_boundary
    hA w.face w.base edgeA edgeB l a b hboundary
      w.base_line hedgeALine hedgeBLine hal hbl hab
  exact ⟨a, b, hab, hal, hbl, hqa, hqb, hpairs⟩

/-- Ordered version of the support reader: `p` and `r` are the initial and
terminal marked points of the literal base edge, and the side supports are
renamed so that they are `l∩a` and `l∩b`, respectively. -/
structure OrdinaryAttachmentSideFrame
    (A : FiniteProjectiveLineArrangement Line)
    (q : A.OrdinaryVertex) (l : Line) where
  a : Line
  b : Line
  a_ne_b : a ≠ b
  a_ne_base : a ≠ l
  b_ne_base : b ≠ l
  q_on_a : A.Incident q.1 a
  q_on_b : A.Incident q.1 b
  p : A.CircularGapSlot l
  r : A.CircularGapSlot l
  p_ne_r : p.1 ≠ r.1
  p_eq_intersection : p.1 = A.intersection l a
  r_eq_intersection : r.1 = A.intersection l b

theorem OrdinaryAttachmentWitness.exists_sideFrame
    (A : FiniteProjectiveLineArrangement Line) (hA : A.NonPencil)
    {q : A.OrdinaryVertex} {l : Line}
    (w : OrdinaryAttachmentWitness A q l) :
    Nonempty (OrdinaryAttachmentSideFrame A q l) := by
  classical
  obtain ⟨a, b, hab, hal, hbl, hqa, hqb, hpairs⟩ :=
    OrdinaryAttachmentWitness.exists_sideSupports A hA w
  let p : A.CircularGapSlot l :=
    ⟨A.geometricEdgeInitial w.base,
      (A.mem_lineVertexSet l).2 ⟨
        A.geometricEdge_initial_mem_vertexSet w.base,
        by simpa only [w.base_line] using
          A.geometricEdge_initial_incident w.base⟩⟩
  let r : A.CircularGapSlot l :=
    ⟨A.geometricEdgeTerminal w.base,
      (A.mem_lineVertexSet l).2 ⟨
        A.geometricEdge_terminal_mem_vertexSet w.base,
        by simpa only [w.base_line] using
          A.geometricEdge_endpoint_incident w.base⟩⟩
  have hpr : p.1 ≠ r.1 := by
    simpa only [p, r] using
      A.geometricEdge_initial_ne_terminal_of_nonPencil hA w.base
  have hpMem : p.1 ∈
      ({A.intersection l a, A.intersection l b} :
        Finset RealProjectivePoint) := by
    rw [← hpairs]
    simp [p]
  have hrMem : r.1 ∈
      ({A.intersection l a, A.intersection l b} :
        Finset RealProjectivePoint) := by
    rw [← hpairs]
    simp [r]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hpMem hrMem
  rcases hpMem with hpA | hpB
  · have hrB : r.1 = A.intersection l b := by
      rcases hrMem with hrA | hrB
      · exact (hpr (hpA.trans hrA.symm)).elim
      · exact hrB
    exact ⟨{
      a := a
      b := b
      a_ne_b := hab
      a_ne_base := hal
      b_ne_base := hbl
      q_on_a := hqa
      q_on_b := hqb
      p := p
      r := r
      p_ne_r := hpr
      p_eq_intersection := hpA
      r_eq_intersection := hrB
    }⟩
  · have hrA : r.1 = A.intersection l a := by
      rcases hrMem with hrA | hrB
      · exact hrA
      · exact (hpr (hpB.trans hrB.symm)).elim
    exact ⟨{
      a := b
      b := a
      a_ne_b := hab.symm
      a_ne_base := hbl
      b_ne_base := hal
      q_on_a := hqb
      q_on_b := hqa
      p := p
      r := r
      p_ne_r := hpr
      p_eq_intersection := hpB
      r_eq_intersection := hrA
    }⟩

/-- An ordinary arrangement vertex belongs to the closures of at most four
actual faces.  The two incident covectors provide the two Boolean signs; all
other relative signs are forced by closure continuity. -/
theorem card_arrangementPointIncidentFaces_le_four_of_ordinaryVertex
    (A : FiniteProjectiveLineArrangement Line) (hA : A.NonPencil)
    (q : A.OrdinaryVertex) :
    (A.arrangementPointIncidentFaces q.1).card ≤ 4 := by
  classical
  obtain ⟨a, b, hab, hincident⟩ :=
    A.exists_two_lines_incident_iff_of_ordinaryVertex q
  obtain ⟨base, hbase⟩ := A.exists_not_incident_line_of_nonPencil hA q.1
  let f : A.ArrangementFace → Bool × Bool := fun F =>
    (decide (A.arrangementRelativeSign base a
      (A.arrangementFaceRepresentative F).1 = 1),
     decide (A.arrangementRelativeSign base b
      (A.arrangementFaceRepresentative F).1 = 1))
  calc
    (A.arrangementPointIncidentFaces q.1).card ≤
        (Finset.univ : Finset (Bool × Bool)).card :=
      Finset.card_le_card_of_injOn f
        (by intro F _; simp)
        (by
          intro F hF G hG hfg
          apply A.arrangementFaceSignPattern_injective base
          change A.arrangementPointSignPattern base
              (A.arrangementFaceRepresentative F) =
            A.arrangementPointSignPattern base
              (A.arrangementFaceRepresentative G)
          rw [A.arrangementPointSignPattern_eq_relativeSign base,
            A.arrangementPointSignPattern_eq_relativeSign base]
          funext l
          by_cases hla : l = a
          · subst l
            simpa only [f] using congrArg Prod.fst hfg
          · by_cases hlb : l = b
            · subst l
              simpa only [f] using congrArg Prod.snd hfg
            · have hql : ¬ A.Incident q.1 l := by
                intro hql
                rcases (hincident l).mp hql with h | h
                · exact hla h
                · exact hlb h
              have hFclosure :
                  q.1 ∈ closure (A.arrangementFaceCarrier F) :=
                (A.mem_arrangementPointIncidentFaces_iff q.1 F).mp hF
              have hGclosure :
                  q.1 ∈ closure (A.arrangementFaceCarrier G) :=
                (A.mem_arrangementPointIncidentFaces_iff q.1 G).mp hG
              rw [A.arrangementRelativeSign_arrangementFaceRepresentative_eq_of_mem_closure
                    q.1 base l F hbase hql hFclosure,
                A.arrangementRelativeSign_arrangementFaceRepresentative_eq_of_mem_closure
                    q.1 base l G hbase hql hGclosure])
    _ = 4 := by decide

/-- Four-Attachment lemma: an ordinary vertex can be opposite at most four
indexed base lines.  Attachments inject into the at-most-four actual faces
around the vertex. -/
theorem ordinaryVertexAttachmentDegree_le_four
    (A : FiniteProjectiveLineArrangement Line) (hA : A.NonPencil)
    (q : A.OrdinaryVertex) :
    A.ordinaryVertexAttachmentDegree q ≤ 4 := by
  classical
  let S : Finset Line := Finset.univ.filter fun l =>
    A.OrdinaryVertexAttachedToLine q l
  let witness : (l : {l // l ∈ S}) →
      OrdinaryAttachmentWitness A q l.1 := fun l =>
    Classical.choice ((Finset.mem_filter.mp l.2).2)
  let face : {l // l ∈ S} →
      {F // F ∈ A.arrangementPointIncidentFaces q.1} := fun l =>
    ⟨(witness l).face,
      OrdinaryAttachmentWitness.face_mem_arrangementPointIncidentFaces
        A hA (witness l)⟩
  obtain ⟨a, b, hab, hincident⟩ :=
    A.exists_two_lines_incident_iff_of_ordinaryVertex q
  have hqa : A.Incident q.1 a := (hincident a).mpr (Or.inl rfl)
  have hqb : A.Incident q.1 b := (hincident b).mpr (Or.inr rfl)
  have hincidentBA : ∀ c : Line,
      A.Incident q.1 c ↔ c = b ∨ c = a := by
    intro c
    rw [hincident c, or_comm]
  have hface : Function.Injective face := by
    intro l m hlm
    have hfaces : (witness l).face = (witness m).face :=
      congrArg Subtype.val hlm
    obtain ⟨edgeB, hedgeBLine, hedgeBMem⟩ :=
      A.exists_transverse_boundaryEdge_of_mem_closure_of_ordinary_intersection
        hA (witness l).face q.1 a b hab.symm hqa hqb hincident
          (witness l).opposite
    obtain ⟨edgeA, hedgeALine, hedgeAMem⟩ :=
      A.exists_transverse_boundaryEdge_of_mem_closure_of_ordinary_intersection
        hA (witness l).face q.1 b a hab hqb hqa hincidentBA
          (witness l).opposite
    have hedgeAB : edgeA ≠ edgeB := by
      intro h
      apply hab
      calc
        a = A.edgeSlotLine edgeA := hedgeALine.symm
        _ = A.edgeSlotLine edgeB := congrArg A.edgeSlotLine h
        _ = b := hedgeBLine
    have hbaseLA : (witness l).base ≠ edgeA := by
      intro h
      apply (witness l).away
      rw [← (witness l).base_line, h, hedgeALine]
      exact hqa
    have hbaseLB : (witness l).base ≠ edgeB := by
      intro h
      apply (witness l).away
      rw [← (witness l).base_line, h, hedgeBLine]
      exact hqb
    have hsub : ({edgeA, edgeB, (witness l).base} :
        Finset A.GeometricEdge) ⊆
          A.arrangementFaceBoundary (witness l).face := by
      intro e he
      simp only [Finset.mem_insert, Finset.mem_singleton] at he
      rcases he with rfl | rfl | rfl
      · exact hedgeAMem
      · exact hedgeBMem
      · exact (witness l).base_mem
    have htriple : ({edgeA, edgeB, (witness l).base} :
        Finset A.GeometricEdge).card = 3 := by
      simp [hedgeAB, hbaseLA, hbaseLB, hbaseLA.symm, hbaseLB.symm]
    have hboundary : A.arrangementFaceBoundary (witness l).face =
        {edgeA, edgeB, (witness l).base} := by
      symm
      apply Finset.eq_of_subset_of_card_le hsub
      rw [(witness l).triangular, htriple]
    have hbaseMem : (witness m).base ∈
        A.arrangementFaceBoundary (witness l).face := by
      rw [hfaces]
      exact (witness m).base_mem
    rw [hboundary] at hbaseMem
    simp only [Finset.mem_insert, Finset.mem_singleton] at hbaseMem
    apply Subtype.ext
    rcases hbaseMem with hbase | hbase | hbase
    · exfalso
      apply (witness m).away
      rw [← (witness m).base_line, hbase, hedgeALine]
      exact hqa
    · exfalso
      apply (witness m).away
      rw [← (witness m).base_line, hbase, hedgeBLine]
      exact hqb
    · exact (witness l).base_line.symm.trans
        ((congrArg A.edgeSlotLine hbase.symm).trans (witness m).base_line)
  have hcard : S.card ≤ (A.arrangementPointIncidentFaces q.1).card := by
    have h := Fintype.card_le_of_injective face hface
    simpa only [Fintype.card_coe] using h
  change S.card ≤ 4
  exact hcard.trans
    (A.card_arrangementPointIncidentFaces_le_four_of_ordinaryVertex hA q)

/-- The generic `DD` triangular-face extractor supplies the two literal
cross-attachments at the endpoints: the initial endpoint is attached to the
support opposite it, and symmetrically for the terminal endpoint. -/
theorem exists_cross_attachments_of_adjacent_circularGap_dd_triangle
    (A : FiniteProjectiveLineArrangement Line) (hA : A.NonPencil)
    (l : Line) (p : A.CircularGapSlot l) (F : A.ArrangementFace)
    (hp2 : A.multiplicity p.1 = 2)
    (hq2 : A.multiplicity (A.circularGapSuccessor l p).1 = 2)
    (hF : A.geometricEdgeAdjacentFace (A.circularGapEdge l p) F)
    (htri : (A.arrangementFaceBoundary F).card = 3) :
    ∃ a b : Line,
      a ≠ l ∧ b ≠ l ∧ a ≠ b ∧
      A.OrdinaryVertexAttachedToLine
          (A.circularGapOrdinaryVertex l p hp2) b ∧
      A.OrdinaryVertexAttachedToLine
          (A.circularGapOrdinaryVertex l
            (A.circularGapSuccessor l p) hq2) a := by
  classical
  obtain ⟨a, b, eP, eQ, hal, hbl, hab, hp, hq,
      hePline, heQline, _hePne, _heQne, _hePQ, hboundary⟩ :=
    A.exists_exact_triangle_boundary_of_adjacent_circularGap_dd
      hA l p F hp2 hq2 hF htri
  have hpl : A.Incident p.1 l :=
    ((A.mem_lineVertexSet l).mp p.2).2
  have hpa : A.Incident p.1 a := by
    rw [hp]
    exact A.intersection_incident_right hal.symm
  have hpordinary : ∀ m : Line,
      A.Incident p.1 m ↔ m = l ∨ m = a :=
    A.incident_iff_eq_or_eq_of_multiplicity_eq_two
      p.1 l a hpl hpa hal hp2
  have hpAway : ¬ A.Incident p.1 b := by
    intro hpb
    rcases (hpordinary b).mp hpb with h | h
    · exact hbl h
    · exact hab h.symm
  have hqLine : A.Incident (A.circularGapSuccessor l p).1 l :=
    ((A.mem_lineVertexSet l).mp (A.circularGapSuccessor l p).2).2
  have hqb : A.Incident (A.circularGapSuccessor l p).1 b := by
    rw [hq]
    exact A.intersection_incident_right hbl.symm
  have hqordinary : ∀ m : Line,
      A.Incident (A.circularGapSuccessor l p).1 m ↔
        m = l ∨ m = b :=
    A.incident_iff_eq_or_eq_of_multiplicity_eq_two
      (A.circularGapSuccessor l p).1 l b hqLine hqb hbl hq2
  have hqAway : ¬ A.Incident (A.circularGapSuccessor l p).1 a := by
    intro hqa
    rcases (hqordinary a).mp hqa with h | h
    · exact hal h
    · exact hab h
  have hpClosure : p.1 ∈ closure (A.arrangementFaceCarrier F) := by
    simpa using
      A.geometricEdgeInitial_mem_closure_arrangementFaceCarrier_of_adjacent
        hA (A.circularGapEdge l p) F hF
  have hqClosure : (A.circularGapSuccessor l p).1 ∈
      closure (A.arrangementFaceCarrier F) := by
    simpa using
      A.geometricEdgeTerminal_mem_closure_arrangementFaceCarrier_of_adjacent
        hA (A.circularGapEdge l p) F hF
  refine ⟨a, b, hal, hbl, hab, ?_, ?_⟩
  · refine ⟨⟨F, eQ, ?_, htri, ?_, heQline, ?_⟩⟩
    · simpa using hpAway
    · rw [hboundary]
      simp
    · simpa using hpClosure
  · refine ⟨⟨F, eP, ?_, htri, ?_, hePline, ?_⟩⟩
    · simpa using hqAway
    · rw [hboundary]
      simp
    · simpa using hqClosure

/-- The two classical local clauses `(0,3+)` and `(1,2+)` imply the exact
linewise disjunction consumed by the finite count. -/
theorem local_association_clause_of_zero_one
    (A : FiniteProjectiveLineArrangement Line)
    (hzero : ∀ l : Line, A.lineOrdinaryVertexDegree l = 0 →
      3 ≤ A.lineOrdinaryAttachmentDegree l)
    (hone : ∀ l : Line, A.lineOrdinaryVertexDegree l = 1 →
      2 ≤ A.lineOrdinaryAttachmentDegree l)
    (l : Line) :
    A.lineOrdinaryVertexDegree l = 2 ∨
      3 ≤ A.lineOrdinaryVertexDegree l +
        A.lineOrdinaryAttachmentDegree l := by
  by_cases htwo : A.lineOrdinaryVertexDegree l = 2
  · exact Or.inl htwo
  · right
    by_cases hzero' : A.lineOrdinaryVertexDegree l = 0
    · have := hzero l hzero'
      omega
    · by_cases hone' : A.lineOrdinaryVertexDegree l = 1
      · have := hone l hone'
        omega
      · omega

/-- Arrangement-level adapter to the pure Kelly--Rottenberg count.  Its two
remaining hypotheses are exactly the geometric Four-Attachment and local
`(0,3+)`/`(1,2+)` clauses. -/
theorem three_mul_card_le_seven_mul_card_ordinaryVertex
    (A : FiniteProjectiveLineArrangement Line)
    (hfour : ∀ q : A.OrdinaryVertex,
      A.ordinaryVertexAttachmentDegree q ≤ 4)
    (hlocal : ∀ l : Line,
      A.lineOrdinaryVertexDegree l = 2 ∨
        3 ≤ A.lineOrdinaryVertexDegree l +
          A.lineOrdinaryAttachmentDegree l) :
    3 * Fintype.card Line ≤ 7 * Fintype.card A.OrdinaryVertex := by
  apply kellyMoser_count_of_local_associations
    (fun q : A.OrdinaryVertex => A.Incident q.1)
    A.OrdinaryVertexAttachedToLine
  · exact A.ordinaryVertexLineDegree_eq_two
  · exact hfour
  · exact hlocal

/-- Arrangement Kelly--Moser bound once only the two genuine Three-Clause
outputs remain: a line with zero (respectively one) ordinary vertices has at
least three (respectively two) attached ordinary vertices. -/
theorem three_mul_card_le_seven_mul_card_ordinaryVertex_of_zero_one
    (A : FiniteProjectiveLineArrangement Line) (hA : A.NonPencil)
    (hzero : ∀ l : Line, A.lineOrdinaryVertexDegree l = 0 →
      3 ≤ A.lineOrdinaryAttachmentDegree l)
    (hone : ∀ l : Line, A.lineOrdinaryVertexDegree l = 1 →
      2 ≤ A.lineOrdinaryAttachmentDegree l) :
    3 * Fintype.card Line ≤ 7 * Fintype.card A.OrdinaryVertex := by
  apply A.three_mul_card_le_seven_mul_card_ordinaryVertex
  · exact A.ordinaryVertexAttachmentDegree_le_four hA
  · exact A.local_association_clause_of_zero_one hzero hone

end FiniteProjectiveLineArrangement

end Erdos506.Incidence
