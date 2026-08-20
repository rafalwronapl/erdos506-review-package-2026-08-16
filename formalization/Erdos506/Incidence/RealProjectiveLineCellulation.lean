import Erdos506.Incidence.DeterminedLineArrangementCensus

/-!
# Edge slots of a real projective line arrangement

For a finite projective line arrangement, an actual arrangement edge is the
open circular gap following a vertex on one of its supporting projective
lines.  Before choosing these successors topologically, the finite data are
already canonical: one *edge slot* for every incident pair `(vertex, line)`.
This file constructs those slots and proves their exact handshake identity.

The existing `RealProjectiveLineCyclicOrder` module develops an intrinsic
orientation of `RP¹`, but currently uses the unqualified name
`RealProjectiveLine` for a different projective space than the dual `RP²`
line type used by `ProjectiveCompletion`.  The two APIs therefore cannot yet
be imported together.  After that namespace/interface conflict is resolved,
the remaining bridge is to turn its ternary orientation on each projective
line into a successor operation on this finite vertex subset, and to identify
a slot with the resulting closed consecutive vertex pair.
-/

namespace Erdos506.Incidence

open scoped BigOperators LinearAlgebra.Projectivization

namespace FiniteProjectiveLineArrangement

variable {Line : Type*} [Fintype Line] [DecidableEq Line]

/-- The homogeneous two-dimensional carrier of a projective line.  It is
defined from the canonical representative of its dual projective point, so
it involves no choice of affine chart or of an orientation. -/
noncomputable def projectiveLineKernel (l : RealProjectiveLine) :
    Submodule ℝ (Fin 3 → ℝ) where
  carrier := {v | v ⬝ᵥ l.rep = 0}
  zero_mem' := by simp
  add_mem' {v w} hv hw := by
    change v ⬝ᵥ l.rep = 0 at hv
    change w ⬝ᵥ l.rep = 0 at hw
    change (v + w) ⬝ᵥ l.rep = 0
    simp [add_dotProduct, hv, hw]
  smul_mem' a v hv := by
    change v ⬝ᵥ l.rep = 0 at hv
    change (a • v) ⬝ᵥ l.rep = 0
    simp [smul_dotProduct, hv]

/-- A projective point is incident with a projective line exactly when its
canonical homogeneous representative lies in that line's kernel.  Thus the
kernel construction is a lossless linear certificate for the point set of a
projective line; the remaining task is only to choose and order a basis of
this two-dimensional carrier. -/
theorem orthogonal_iff_rep_mem_projectiveLineKernel
    (p : RealProjectivePoint) (l : RealProjectiveLine) :
    p.orthogonal l ↔ p.rep ∈ projectiveLineKernel l := by
  change p.orthogonal l ↔ p.rep ⬝ᵥ l.rep = 0
  constructor
  · intro h
    rw [← p.mk_rep, ← l.mk_rep, Projectivization.orthogonal_mk] at h
    exact h
  · intro h
    rw [← p.mk_rep, ← l.mk_rep, Projectivization.orthogonal_mk]
    exact h

/-- The finite set of actual arrangement vertices lying on one indexed
projective line. -/
noncomputable def lineVertexSet
    (A : FiniteProjectiveLineArrangement Line) (l : Line) :
    Finset RealProjectivePoint := by
  classical
  exact A.vertexSet.filter fun p => A.Incident p l

/-- Membership in the vertex set carried by an indexed line is precisely
vertex membership together with projective incidence. -/
theorem mem_lineVertexSet
    (A : FiniteProjectiveLineArrangement Line) (l : Line)
    {p : RealProjectivePoint} :
    p ∈ A.lineVertexSet l ↔ p ∈ A.vertexSet ∧ A.Incident p l := by
  classical
  simp [lineVertexSet]

/-- A circular-gap slot on a fixed projective line is its initial vertex.
For a finite subset of a circle, every vertex has one following open gap;
the endpoint of that gap awaits the successor construction from the cyclic
orientation. -/
abbrev CircularGapSlot (A : FiniteProjectiveLineArrangement Line) (l : Line) :
    Type :=
  {p : RealProjectivePoint // p ∈ A.lineVertexSet l}

/-- A prospective edge is indexed by a vertex together with one arrangement
line through it.  Once a cyclic successor is constructed on each
`lineVertexSet`, this slot is the unique circular gap immediately following
its vertex on that line. -/
abbrev EdgeSlot (A : FiniteProjectiveLineArrangement Line) : Type _ :=
  Σ p : {p : RealProjectivePoint // p ∈ A.vertexSet},
    {l : Line // A.Incident p.1 l}

/-- Finiteness of the lines incident with a fixed vertex, obtained from the
ambient finite line type. -/
noncomputable instance incidenceSubtypeFintype
    (A : FiniteProjectiveLineArrangement Line) (p : RealProjectivePoint) :
    Fintype {l : Line // A.Incident p l} :=
  Fintype.ofFinite _

/-- Reordering the two pieces of an edge slot exhibits it as a circular-gap
slot on one indexed line.  This is a genuine finite equivalence; only the
geometric successor endpoint has not yet been attached to the gap. -/
noncomputable def edgeSlotEquivCircularGap
    (A : FiniteProjectiveLineArrangement Line) :
    A.EdgeSlot ≃ Σ l : Line, A.CircularGapSlot l where
  toFun e := ⟨e.2.1, ⟨e.1.1,
    (A.mem_lineVertexSet e.2.1).mpr ⟨e.1.2, e.2.2⟩⟩⟩
  invFun g := ⟨⟨g.2.1, ((A.mem_lineVertexSet g.1).mp g.2.2).1⟩,
    ⟨g.1, ((A.mem_lineVertexSet g.1).mp g.2.2).2⟩⟩
  left_inv e := by
    rcases e with ⟨p, l⟩
    rfl
  right_inv g := by
    rcases g with ⟨l, p⟩
    rfl

/-- The vertex at which an edge slot starts. -/
def edgeSlotVertex (A : FiniteProjectiveLineArrangement Line)
    (e : A.EdgeSlot) : RealProjectivePoint :=
  e.1.1

/-- The arrangement line supporting an edge slot. -/
def edgeSlotLine (A : FiniteProjectiveLineArrangement Line)
    (e : A.EdgeSlot) : Line :=
  e.2.1

/-- Every edge slot starts at an actual arrangement vertex. -/
theorem edgeSlotVertex_mem_vertexSet
    (A : FiniteProjectiveLineArrangement Line) (e : A.EdgeSlot) :
    A.edgeSlotVertex e ∈ A.vertexSet := by
  exact e.1.2

/-- Every edge slot is incident with its supporting arrangement line. -/
theorem edgeSlot_incident
    (A : FiniteProjectiveLineArrangement Line) (e : A.EdgeSlot) :
    A.Incident (A.edgeSlotVertex e) (A.edgeSlotLine e) := by
  exact e.2.2

/-- The number of slots based at one vertex is exactly the arrangement
multiplicity at that vertex. -/
theorem card_edgeSlotsAt
    (A : FiniteProjectiveLineArrangement Line) (p : ↥A.vertexSet) :
    Fintype.card {l : Line // A.Incident p.1 l} = A.multiplicity p.1 := by
  classical
  rw [Fintype.card_subtype]
  rfl

/-- Exact edge handshake for the canonical edge slots.  This is the desired
identity `E = Σᵥ multiplicity(v)` before the slots are converted into actual
consecutive circular vertex pairs. -/
theorem card_edgeSlot_eq_sum_multiplicity
    (A : FiniteProjectiveLineArrangement Line) :
    Fintype.card A.EdgeSlot =
      ∑ p ∈ A.vertexSet, A.multiplicity p := by
  classical
  rw [Fintype.card_sigma]
  simp_rw [card_edgeSlotsAt]
  conv_rhs => rw [← Finset.sum_attach]
  rw [Finset.attach_eq_univ]

/-- The exact finite data supplied by the projective arrangement before
faces are introduced.  It is intentionally weaker than
`ProjectiveArrangementCellulation`: no Euler or face assertion is present. -/
structure EdgeCensus (A : FiniteProjectiveLineArrangement Line) where
  Edge : Type*
  edgeFintype : Fintype Edge
  edgeCount : @Fintype.card Edge edgeFintype =
    ∑ p ∈ A.vertexSet, A.multiplicity p

/-- The canonical edge-slot census satisfies the edge-count field exactly. -/
noncomputable def edgeSlotCensus
    (A : FiniteProjectiveLineArrangement Line) : A.EdgeCensus where
  Edge := A.EdgeSlot
  edgeFintype := inferInstance
  edgeCount := A.card_edgeSlot_eq_sum_multiplicity

end FiniteProjectiveLineArrangement

end Erdos506.Incidence
