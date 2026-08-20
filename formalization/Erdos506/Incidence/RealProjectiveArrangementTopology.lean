import Erdos506.Incidence.RealProjectiveArrangementFaces
import Mathlib.Data.Sign.Basic
import Mathlib.Algebra.Module.Submodule.Union
import Mathlib.Topology.Constructions
import Mathlib.Topology.Maps.Basic
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Algebra.Module.LocallyConvex
import Mathlib.Topology.Connected.TotallyDisconnected
import Mathlib.Topology.Connected.LocallyConnected
import Mathlib.Topology.Connected.LocPathConnected
import Mathlib.Topology.Instances.Sign
import Mathlib.Analysis.Convex.PathConnected
import Mathlib.Analysis.Normed.Module.Connected

/-!
# Topological faces of a real projective line arrangement

This is the first global topological layer over the geometric edge module.
Mathlib's `Projectivization` is a quotient, and its quotient topology turns
the complement of the finitely many projective lines into a genuine
topological space.  An arrangement face is defined here, without any
cellulation hypothesis, as a connected component of that complement.

The present file deliberately proves only topology that follows directly from
the quotient construction: the complement is nonempty and open, and each
face component is open and path-connected.  It does *not* claim a finite
cell decomposition, a two-sided edge theorem, or Euler's formula; those are
the remaining global results needed by Melchior.
-/

namespace Erdos506.Incidence

open Matrix
open scoped BigOperators LinearAlgebra.Projectivization

namespace FiniteProjectiveLineArrangement

variable {Line : Type*} [Fintype Line] [DecidableEq Line]

/-- The canonical quotient topology on the algebraic projectivization.  It is
exported as a definition so later boundary constructions can explicitly
install the *same* topology when forming closures or frontiers. -/
@[reducible] noncomputable def realProjectivePointQuotientTopology :
    TopologicalSpace RealProjectivePoint :=
  @instTopologicalSpaceQuotient
    {v : Fin 3 → ℝ // v ≠ 0}
    (projectivizationSetoid ℝ (Fin 3 → ℝ))
    (by infer_instance)

/-- `Projectivization` is a definition rather than an abbreviation, so
typeclass search does not unfold it to the quotient on its own.  The present
module works throughout with the canonical quotient topology above. -/
noncomputable local instance realProjectivePointTopologicalSpace :
    TopologicalSpace RealProjectivePoint :=
  realProjectivePointQuotientTopology

/-- The complement of all indexed projective lines in the quotient-topological
real projective plane. -/
def arrangementComplement (A : FiniteProjectiveLineArrangement Line) :
    Set RealProjectivePoint :=
  {p | ∀ l : Line, ¬ A.Incident p l}

/-- The underlying open space whose connected components are the faces. -/
abbrev ArrangementComplement (A : FiniteProjectiveLineArrangement Line) : Type _ :=
  {p : RealProjectivePoint // p ∈ A.arrangementComplement}

/-- A genuine arrangement face: a connected component of the actual
complement, not an abstract finite placeholder. -/
noncomputable abbrev ArrangementFace (A : FiniteProjectiveLineArrangement Line) : Type _ :=
  ConnectedComponents A.ArrangementComplement

theorem mem_arrangementComplement_iff
    (A : FiniteProjectiveLineArrangement Line) (p : RealProjectivePoint) :
    p ∈ A.arrangementComplement ↔ ∀ l : Line, ¬ A.Incident p l :=
  Iff.rfl

/-- The quotient map from nonzero homogeneous representatives equips the
existing projectivization with its canonical quotient topology. -/
theorem isQuotientMap_projectivePoint_mk :
    Topology.IsQuotientMap
      (Projectivization.mk' ℝ :
        {v : Fin 3 → ℝ // v ≠ 0} → RealProjectivePoint) :=
  isQuotientMap_quotient_mk'

/-- There is a homogeneous representative outside every line of a finite
arrangement.  This is the finite-union-of-proper-hyperplanes argument over
the infinite field `ℝ`. -/
theorem arrangementComplement_nonempty
    (A : FiniteProjectiveLineArrangement Line) :
    A.arrangementComplement.Nonempty := by
  classical
  rcases isEmpty_or_nonempty Line with hLine | hLine
  · letI : IsEmpty Line := hLine
    let v : Fin 3 → ℝ := ![1, 0, 0]
    have hv : v ≠ 0 := by
      intro hzero
      have hcoord := congrFun hzero (0 : Fin 3)
      norm_num [v] at hcoord
    refine ⟨Projectivization.mk ℝ v hv, ?_⟩
    intro l
    exact isEmptyElim l
  · have hforms :
        ∀ l : Line, ∃ v : Fin 3 → ℝ,
          projectiveLineEvaluation (A.projectiveLine l) v ≠ 0 := by
      intro l
      by_contra h
      push_neg at h
      apply projectiveLineEvaluation_ne_zero (A.projectiveLine l)
      exact LinearMap.ext fun v => h v
    obtain ⟨v, hv⟩ := Module.Dual.exists_forall_ne_zero_of_forall_exists
      (fun l : Line => projectiveLineEvaluation (A.projectiveLine l)) hforms
    have hv0 : v ≠ 0 := by
      obtain ⟨l⟩ := hLine
      intro hzero
      exact hv l (by simp [hzero, projectiveLineEvaluation])
    refine ⟨Projectivization.mk ℝ v hv0, ?_⟩
    intro l
    change ¬ (Projectivization.mk ℝ v hv0).orthogonal (A.projectiveLine l)
    rw [← (A.projectiveLine l).mk_rep, Projectivization.orthogonal_mk]
    simpa [projectiveLineEvaluation] using hv l

theorem nonempty_arrangementComplement
    (A : FiniteProjectiveLineArrangement Line) :
    Nonempty A.ArrangementComplement := by
  rcases A.arrangementComplement_nonempty with ⟨p, hp⟩
  exact ⟨⟨p, hp⟩⟩

/-- Pulling the complement back through homogeneous representatives is the
finite intersection of the nonvanishing loci of the defining covectors. -/
theorem preimage_arrangementComplement_projectivePoint_mk
    (A : FiniteProjectiveLineArrangement Line) :
    (Projectivization.mk' ℝ :
      {v : Fin 3 → ℝ // v ≠ 0} → RealProjectivePoint) ⁻¹'
        A.arrangementComplement =
      ⋂ l : Line, {v : {v : Fin 3 → ℝ // v ≠ 0} |
        projectiveLineEvaluation (A.projectiveLine l) v.1 ≠ 0} := by
  ext v
  simp only [Set.mem_preimage, Set.mem_iInter, Set.mem_setOf_eq]
  constructor
  · intro hv l hzero
    apply hv l
    change (Projectivization.mk' ℝ v).orthogonal (A.projectiveLine l)
    rw [Projectivization.mk'_eq_mk, ← (A.projectiveLine l).mk_rep,
      Projectivization.orthogonal_mk]
    simpa [projectiveLineEvaluation] using hzero
  · intro hv l hincident
    have hzero : projectiveLineEvaluation (A.projectiveLine l) v.1 = 0 := by
      change (Projectivization.mk' ℝ v).orthogonal (A.projectiveLine l) at hincident
      rw [Projectivization.mk'_eq_mk, ← (A.projectiveLine l).mk_rep,
        Projectivization.orthogonal_mk] at hincident
      simpa [projectiveLineEvaluation] using hincident
    exact hv l hzero

/-- The actual complement of a finite real projective line arrangement is
open in the quotient topology. -/
theorem isOpen_arrangementComplement
    (A : FiniteProjectiveLineArrangement Line) :
    IsOpen A.arrangementComplement := by
  classical
  rw [← isQuotientMap_projectivePoint_mk.isOpen_preimage,
    A.preimage_arrangementComplement_projectivePoint_mk]
  apply isOpen_iInter_of_finite
  intro l
  have hne : IsOpen {z : ℝ | z ≠ 0} := by
    simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using
      (isClosed_singleton : IsClosed ({0} : Set ℝ)).isOpen_compl
  exact ((projectiveLineEvaluation (A.projectiveLine l)).continuous_of_finiteDimensional.comp
    continuous_subtype_val).isOpen_preimage _ hne

/-- The quotient-topological real projective plane is locally path-connected.
The proof uses that it is a quotient of the open set of nonzero homogeneous
vectors. -/
theorem realProjectivePoint_locPathConnected :
    LocPathConnectedSpace RealProjectivePoint := by
  have hne : IsOpen {v : Fin 3 → ℝ | v ≠ 0} := by
    simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using
      (isClosed_singleton : IsClosed ({0} : Set (Fin 3 → ℝ))).isOpen_compl
  letI : LocPathConnectedSpace {v : Fin 3 → ℝ // v ≠ 0} :=
    hne.locPathConnectedSpace
  exact Topology.IsQuotientMap.locPathConnectedSpace
    isQuotientMap_projectivePoint_mk

/-- The complement inherits local path-connectedness from the projective
plane because it is open. -/
theorem arrangementComplement_locPathConnected
    (A : FiniteProjectiveLineArrangement Line) :
    LocPathConnectedSpace A.ArrangementComplement := by
  letI : LocPathConnectedSpace RealProjectivePoint :=
    realProjectivePoint_locPathConnected
  exact A.isOpen_arrangementComplement.locPathConnectedSpace

/-- Components of the actual complement are open, so the face quotient is
not merely set-theoretic: its points represent open regions. -/
theorem isOpen_arrangementFaceComponent
    (A : FiniteProjectiveLineArrangement Line) (p : A.ArrangementComplement) :
    IsOpen (connectedComponent p) := by
  letI : LocPathConnectedSpace A.ArrangementComplement :=
    A.arrangementComplement_locPathConnected
  exact isOpen_connectedComponent

/-- Every arrangement face component is path-connected. -/
theorem isPathConnected_arrangementFaceComponent
    (A : FiniteProjectiveLineArrangement Line) (p : A.ArrangementComplement) :
    IsPathConnected (connectedComponent p) := by
  letI : LocPathConnectedSpace A.ArrangementComplement :=
    A.arrangementComplement_locPathConnected
  exact (A.isOpen_arrangementFaceComponent p).isConnected_iff_isPathConnected.mp
    isConnected_connectedComponent

/-- The canonical quotient map sends a complement point to its actual face. -/
noncomputable def arrangementFaceOf
    (A : FiniteProjectiveLineArrangement Line) :
    A.ArrangementComplement → A.ArrangementFace :=
  ConnectedComponents.mk

theorem arrangementFaceOf_surjective
    (A : FiniteProjectiveLineArrangement Line) :
    Function.Surjective A.arrangementFaceOf :=
  ConnectedComponents.surjective_coe

theorem arrangementFaceOf_eq_iff
    (A : FiniteProjectiveLineArrangement Line)
    (p q : A.ArrangementComplement) :
    A.arrangementFaceOf p = A.arrangementFaceOf q ↔
      connectedComponent p = connectedComponent q :=
  ConnectedComponents.coe_eq_coe

/-- In the locally path-connected complement, two points determine the same
face exactly when they can be joined by a path staying in the complement. -/
theorem arrangementFaceOf_eq_iff_joined
    (A : FiniteProjectiveLineArrangement Line)
    (p q : A.ArrangementComplement) :
    A.arrangementFaceOf p = A.arrangementFaceOf q ↔ Joined p q := by
  letI : LocPathConnectedSpace A.ArrangementComplement :=
    A.arrangementComplement_locPathConnected
  rw [A.arrangementFaceOf_eq_iff]
  exact connectedComponent_eq_iff_joined p q

/-- The ambient carrier of a face.  This is the image in `RP²` of one
connected component of the genuine complement. -/
def arrangementFaceCarrier
    (A : FiniteProjectiveLineArrangement Line) (F : A.ArrangementFace) :
    Set RealProjectivePoint :=
  Subtype.val '' (A.arrangementFaceOf ⁻¹' {F})

/-- A face carrier may be computed from any point representing the relevant
component. -/
theorem arrangementFaceCarrier_eq_image_connectedComponent
    (A : FiniteProjectiveLineArrangement Line) (p : A.ArrangementComplement) :
    A.arrangementFaceCarrier (A.arrangementFaceOf p) =
      Subtype.val '' connectedComponent p := by
  ext q
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨x, ?_, rfl⟩
    change (x : A.ArrangementFace) = (p : A.ArrangementFace) at hx
    exact ConnectedComponents.coe_eq_coe'.mp hx
  · rintro ⟨x, hx, rfl⟩
    refine ⟨x, ?_, rfl⟩
    change (x : A.ArrangementFace) = (p : A.ArrangementFace)
    exact ConnectedComponents.coe_eq_coe'.mpr hx

/-- Every ambient face carrier is contained in the arrangement complement. -/
theorem arrangementFaceCarrier_subset_arrangementComplement
    (A : FiniteProjectiveLineArrangement Line) (F : A.ArrangementFace) :
    A.arrangementFaceCarrier F ⊆ A.arrangementComplement := by
  rintro q ⟨p, hp, rfl⟩
  exact p.2

/-- No point in an ambient face carrier lies on an arrangement line. -/
theorem not_incident_of_mem_arrangementFaceCarrier
    (A : FiniteProjectiveLineArrangement Line) (F : A.ArrangementFace)
    {p : RealProjectivePoint} (hp : p ∈ A.arrangementFaceCarrier F) (l : Line) :
    ¬ A.Incident p l :=
  A.arrangementFaceCarrier_subset_arrangementComplement F hp l

/-- The ambient carrier of every face is nonempty. -/
theorem arrangementFaceCarrier_nonempty
    (A : FiniteProjectiveLineArrangement Line) (F : A.ArrangementFace) :
    (A.arrangementFaceCarrier F).Nonempty := by
  obtain ⟨p, hp⟩ := A.arrangementFaceOf_surjective F
  rw [← hp, A.arrangementFaceCarrier_eq_image_connectedComponent]
  exact (connectedComponent_nonempty (x := p)).image Subtype.val

/-- A face carrier is open in the ambient real projective plane, rather than
merely open in the complement subtype. -/
theorem isOpen_arrangementFaceCarrier
    (A : FiniteProjectiveLineArrangement Line) (F : A.ArrangementFace) :
    IsOpen (A.arrangementFaceCarrier F) := by
  obtain ⟨p, hp⟩ := A.arrangementFaceOf_surjective F
  rw [← hp, A.arrangementFaceCarrier_eq_image_connectedComponent]
  exact A.isOpen_arrangementComplement.isOpenMap_subtype_val _
    (A.isOpen_arrangementFaceComponent p)

/-- The ambient carrier of every face is path-connected. -/
theorem isPathConnected_arrangementFaceCarrier
    (A : FiniteProjectiveLineArrangement Line) (F : A.ArrangementFace) :
    IsPathConnected (A.arrangementFaceCarrier F) := by
  obtain ⟨p, hp⟩ := A.arrangementFaceOf_surjective F
  rw [← hp, A.arrangementFaceCarrier_eq_image_connectedComponent]
  exact (A.isPathConnected_arrangementFaceComponent p).image continuous_subtype_val

/-- The point of the complement representing a component lies in the ambient
carrier of that component. -/
theorem mem_arrangementFaceCarrier_faceOf
    (A : FiniteProjectiveLineArrangement Line) (p : A.ArrangementComplement) :
    p.1 ∈ A.arrangementFaceCarrier (A.arrangementFaceOf p) := by
  refine ⟨p, ?_, rfl⟩
  change A.arrangementFaceOf p = A.arrangementFaceOf p
  rfl

/-- The genuine ambient face carriers cover exactly the complement of the
arrangement. -/
theorem iUnion_arrangementFaceCarrier_eq_arrangementComplement
    (A : FiniteProjectiveLineArrangement Line) :
    ⋃ F : A.ArrangementFace, A.arrangementFaceCarrier F =
      A.arrangementComplement := by
  ext p
  constructor
  · simp only [Set.mem_iUnion]
    rintro ⟨F, hp⟩
    exact A.arrangementFaceCarrier_subset_arrangementComplement F hp
  · intro hp
    refine Set.mem_iUnion.2 ⟨A.arrangementFaceOf ⟨p, hp⟩, ?_⟩
    exact A.mem_arrangementFaceCarrier_faceOf ⟨p, hp⟩

/-- Distinct connected components give disjoint ambient face carriers. -/
theorem arrangementFaceCarrier_disjoint
    (A : FiniteProjectiveLineArrangement Line) {F G : A.ArrangementFace}
    (hFG : F ≠ G) :
    Disjoint (A.arrangementFaceCarrier F) (A.arrangementFaceCarrier G) := by
  rw [Set.disjoint_left]
  intro q hqF hqG
  rcases hqF with ⟨p, hp, hpq⟩
  rcases hqG with ⟨r, hr, hrq⟩
  have hpr : p = r := Subtype.ext (hpq.trans hrq.symm)
  change A.arrangementFaceOf p = F at hp
  change A.arrangementFaceOf r = G at hr
  apply hFG
  calc
    F = A.arrangementFaceOf p := hp.symm
    _ = A.arrangementFaceOf r := congrArg A.arrangementFaceOf hpr
    _ = G := hr

theorem nonempty_arrangementFace
    (A : FiniteProjectiveLineArrangement Line) :
    Nonempty A.ArrangementFace :=
  ConnectedComponents.nonempty_iff_nonempty.mpr A.nonempty_arrangementComplement

/-- Since the complement is locally connected, its connected-component
quotient has the discrete topology.  Finiteness of this discrete set is a
separate semialgebraic/topological theorem, not assumed here. -/
theorem arrangementFace_discreteTopology
    (A : FiniteProjectiveLineArrangement Line) :
    DiscreteTopology A.ArrangementFace := by
  letI : LocPathConnectedSpace A.ArrangementComplement :=
    A.arrangementComplement_locPathConnected
  infer_instance

/-! ## Finite sign charts for genuine faces

Fixing one arrangement line gives an affine normalization of every point of
the complement: the chosen covector is made equal to one.  The remaining
strict signs are then invariant projective data.  Each sign fibre is the
image of a convex open cone in homogeneous coordinates, so two points with
the same signs are genuinely path-connected in the complement.  This gives a
finite coding of the *actual* connected components, rather than postulating a
finite face type.
-/

/-- A homogeneous strict-sign cone.  Its projective image is one chart cell
of the complement. -/
def arrangementSignCone
    (A : FiniteProjectiveLineArrangement Line) (sigma : Line -> Bool) :
    Set (Fin 3 -> ℝ) :=
  ⋂ l : Line,
    if sigma l then
      {v | 0 < projectiveLineEvaluation (A.projectiveLine l) v}
    else
      {v | projectiveLineEvaluation (A.projectiveLine l) v < 0}

/-- The closed homogeneous cone underlying a strict sign region.  Unlike the
strict cone, this contains its genuine projective boundary and is the
polyhedral object on which the remaining face-degree argument has to work. -/
def arrangementClosedSignCone
    (A : FiniteProjectiveLineArrangement Line) (sigma : Line -> Bool) :
    Set (Fin 3 -> ℝ) :=
  ⋂ l : Line,
    if sigma l then
      {v | 0 ≤ projectiveLineEvaluation (A.projectiveLine l) v}
    else
      {v | projectiveLineEvaluation (A.projectiveLine l) v ≤ 0}

/-- A strict sign cone lies in its closed homogeneous cone. -/
theorem arrangementSignCone_subset_arrangementClosedSignCone
    (A : FiniteProjectiveLineArrangement Line) (sigma : Line -> Bool) :
    A.arrangementSignCone sigma ⊆ A.arrangementClosedSignCone sigma := by
  intro v hv
  simp only [arrangementSignCone, arrangementClosedSignCone,
    Set.mem_iInter] at hv ⊢
  intro l
  by_cases hs : sigma l
  · have hpos : 0 < projectiveLineEvaluation (A.projectiveLine l) v := by
      simpa [hs] using hv l
    simpa [hs] using hpos.le
  · have hneg : projectiveLineEvaluation (A.projectiveLine l) v < 0 := by
      simpa [hs] using hv l
    simpa [hs] using hneg.le

/-- Non-pencilness says that the defining homogeneous covectors have no
nonzero common kernel vector.  This is the exact algebraic form of the fact
that the closed chamber cones below are pointed. -/
theorem eq_zero_of_projectiveLineEvaluation_eq_zero_of_nonPencil
    (A : FiniteProjectiveLineArrangement Line) (hA : A.NonPencil)
    {v : Fin 3 -> ℝ}
    (hv : ∀ l : Line, projectiveLineEvaluation (A.projectiveLine l) v = 0) :
    v = 0 := by
  classical
  by_contra hv0
  apply hA
  refine ⟨Projectivization.mk ℝ v hv0, ?_⟩
  intro l
  change (Projectivization.mk ℝ v hv0).orthogonal (A.projectiveLine l)
  rw [← (A.projectiveLine l).mk_rep, Projectivization.orthogonal_mk]
  simpa [projectiveLineEvaluation] using hv l

/-- The closed cone of a realized sign word contains no nontrivial line in a
non-pencil arrangement.  This is proved directly from the inequalities, not
by postulating a polyhedral-cellulation theorem. -/
theorem eq_zero_of_mem_arrangementClosedSignCone_of_neg_mem_of_nonPencil
    (A : FiniteProjectiveLineArrangement Line) (hA : A.NonPencil)
    (sigma : Line -> Bool) {v : Fin 3 -> ℝ}
    (hv : v ∈ A.arrangementClosedSignCone sigma)
    (hneg : -v ∈ A.arrangementClosedSignCone sigma) :
    v = 0 := by
  apply A.eq_zero_of_projectiveLineEvaluation_eq_zero_of_nonPencil hA
  intro l
  have hv' := Set.mem_iInter.mp hv l
  have hneg' := Set.mem_iInter.mp hneg l
  by_cases hs : sigma l
  · have hle : 0 ≤ projectiveLineEvaluation (A.projectiveLine l) v := by
      simpa [arrangementClosedSignCone, hs] using hv'
    have hge : projectiveLineEvaluation (A.projectiveLine l) v ≤ 0 := by
      have h : 0 ≤ projectiveLineEvaluation (A.projectiveLine l) (-v) := by
        simpa [arrangementClosedSignCone, hs] using hneg'
      rw [LinearMap.map_neg] at h
      linarith
    exact le_antisymm hge hle
  · have hle : projectiveLineEvaluation (A.projectiveLine l) v ≤ 0 := by
      simpa [arrangementClosedSignCone, hs] using hv'
    have hge : 0 ≤ projectiveLineEvaluation (A.projectiveLine l) v := by
      have h : projectiveLineEvaluation (A.projectiveLine l) (-v) ≤ 0 := by
        simpa [arrangementClosedSignCone, hs] using hneg'
      rw [LinearMap.map_neg] at h
      linarith
    exact le_antisymm hle hge

/-- The defining covector of every arrangement line is nonzero on a point of
the complement, even when that point is represented by Mathlib's chosen
homogeneous representative. -/
theorem projectiveLineEvaluation_rep_ne_zero
    (A : FiniteProjectiveLineArrangement Line) (p : A.ArrangementComplement)
    (l : Line) :
    projectiveLineEvaluation (A.projectiveLine l) p.1.rep ≠ 0 := by
  intro hzero
  apply p.2 l
  change p.1.orthogonal (A.projectiveLine l)
  rw [← p.1.mk_rep, ← (A.projectiveLine l).mk_rep,
    Projectivization.orthogonal_mk]
  simpa [projectiveLineEvaluation] using hzero

/-- Normalize a complement point in the affine chart where `base` has value
one.  This is only a representative construction; the induced signs below
are proved to determine the genuine connected component. -/
noncomputable def arrangementNormalizedRepresentative
    (A : FiniteProjectiveLineArrangement Line) (base : Line)
    (p : A.ArrangementComplement) : Fin 3 -> ℝ :=
  (projectiveLineEvaluation (A.projectiveLine base) p.1.rep)⁻¹ • p.1.rep

theorem projectiveLineEvaluation_arrangementNormalizedRepresentative_base
    (A : FiniteProjectiveLineArrangement Line) (base : Line)
    (p : A.ArrangementComplement) :
    projectiveLineEvaluation (A.projectiveLine base)
      (A.arrangementNormalizedRepresentative base p) = 1 := by
  have hne := A.projectiveLineEvaluation_rep_ne_zero p base
  simp [arrangementNormalizedRepresentative, hne]

theorem arrangementNormalizedRepresentative_ne_zero
    (A : FiniteProjectiveLineArrangement Line) (base : Line)
    (p : A.ArrangementComplement) :
    A.arrangementNormalizedRepresentative base p ≠ 0 := by
  intro hzero
  have hbase :=
    A.projectiveLineEvaluation_arrangementNormalizedRepresentative_base base p
  rw [hzero, LinearMap.map_zero] at hbase
  norm_num at hbase

/-- The normalized representative is a representative of the original
projective point. -/
theorem projectivization_mk_arrangementNormalizedRepresentative
    (A : FiniteProjectiveLineArrangement Line) (base : Line)
    (p : A.ArrangementComplement) :
    Projectivization.mk ℝ (A.arrangementNormalizedRepresentative base p)
      (A.arrangementNormalizedRepresentative_ne_zero base p) = p.1 := by
  rw [← p.1.mk_rep]
  apply (Projectivization.mk_eq_mk_iff' ℝ _ _ _ _).mpr
  refine ⟨(projectiveLineEvaluation (A.projectiveLine base) p.1.rep)⁻¹, ?_⟩
  rfl

/-- The strict signs of the normalized homogeneous representative. -/
noncomputable def arrangementPointSignPattern
    (A : FiniteProjectiveLineArrangement Line) (base : Line) :
    A.ArrangementComplement -> Line -> Bool :=
  fun p l => decide (0 < projectiveLineEvaluation (A.projectiveLine l)
    (A.arrangementNormalizedRepresentative base p))

theorem arrangementNormalizedRepresentative_mem_arrangementSignCone
    (A : FiniteProjectiveLineArrangement Line) (base : Line)
    (p : A.ArrangementComplement) :
    A.arrangementNormalizedRepresentative base p ∈
      A.arrangementSignCone (A.arrangementPointSignPattern base p) := by
  simp only [arrangementSignCone, Set.mem_iInter]
  intro l
  by_cases hpos :
      0 < projectiveLineEvaluation (A.projectiveLine l)
        (A.arrangementNormalizedRepresentative base p)
  · simp [arrangementPointSignPattern, hpos]
  · have hne :
        projectiveLineEvaluation (A.projectiveLine l)
          (A.arrangementNormalizedRepresentative base p) ≠ 0 := by
      intro hzero
      rw [arrangementNormalizedRepresentative, LinearMap.map_smul] at hzero
      rcases smul_eq_zero.mp hzero with hscalar | hvalue
      · exact (inv_ne_zero (A.projectiveLineEvaluation_rep_ne_zero p base) hscalar).elim
      · exact (A.projectiveLineEvaluation_rep_ne_zero p l) hvalue
    have hneg :
        projectiveLineEvaluation (A.projectiveLine l)
          (A.arrangementNormalizedRepresentative base p) < 0 :=
      lt_of_le_of_ne (le_of_not_gt hpos) hne
    simp [arrangementPointSignPattern, hpos, hneg]

theorem convex_arrangementSignCone
    (A : FiniteProjectiveLineArrangement Line) (sigma : Line -> Bool) :
    Convex ℝ (A.arrangementSignCone sigma) := by
  unfold arrangementSignCone
  apply convex_iInter
  intro l
  by_cases h : sigma l
  · simp only [h, ite_true]
    exact convex_halfSpace_gt
      (IsLinearMap.mk (projectiveLineEvaluation (A.projectiveLine l)).map_add
        (projectiveLineEvaluation (A.projectiveLine l)).map_smul) 0
  · simp only [h, ite_false]
    exact convex_halfSpace_lt
      (IsLinearMap.mk (projectiveLineEvaluation (A.projectiveLine l)).map_add
        (projectiveLineEvaluation (A.projectiveLine l)).map_smul) 0

theorem arrangementSignCone_ne_zero
    (A : FiniteProjectiveLineArrangement Line) (base : Line)
    (sigma : Line -> Bool) {v : Fin 3 -> ℝ}
    (hv : v ∈ A.arrangementSignCone sigma) : v ≠ 0 := by
  intro hzero
  have hbase := Set.mem_iInter.mp hv base
  by_cases hsign : sigma base
  · have hpos :
        0 < projectiveLineEvaluation (A.projectiveLine base) v := by
      simpa [hsign] using hbase
    rw [hzero, LinearMap.map_zero] at hpos
    exact (lt_irrefl 0 hpos)
  · have hneg :
        projectiveLineEvaluation (A.projectiveLine base) v < 0 := by
      simpa [hsign] using hbase
    rw [hzero, LinearMap.map_zero] at hneg
    exact (lt_irrefl 0 hneg)

/-- The projective image of every point in a strict-sign cone belongs to the
actual arrangement complement. -/
theorem projectivization_mk_mem_arrangementComplement_of_mem_arrangementSignCone
    (A : FiniteProjectiveLineArrangement Line) (base : Line)
    (sigma : Line -> Bool) {v : Fin 3 -> ℝ}
    (hv : v ∈ A.arrangementSignCone sigma) :
    Projectivization.mk ℝ v (A.arrangementSignCone_ne_zero base sigma hv) ∈
      A.arrangementComplement := by
  change ∀ l : Line, ¬ A.Incident
    (Projectivization.mk ℝ v (A.arrangementSignCone_ne_zero base sigma hv)) l
  intro l hincident
  have hsign := Set.mem_iInter.mp hv l
  have hzero : projectiveLineEvaluation (A.projectiveLine l) v = 0 := by
    change (Projectivization.mk ℝ v
      (A.arrangementSignCone_ne_zero base sigma hv)).orthogonal
        (A.projectiveLine l) at hincident
    rw [← (A.projectiveLine l).mk_rep,
      Projectivization.orthogonal_mk] at hincident
    simpa [projectiveLineEvaluation] using hincident
  by_cases h : sigma l <;> simp [h, hzero] at hsign

/-- A strict-sign cone maps continuously into the actual complement. -/
noncomputable def arrangementSignConeToComplement
    (A : FiniteProjectiveLineArrangement Line) (base : Line)
    (sigma : Line -> Bool) :
    {v : Fin 3 -> ℝ // v ∈ A.arrangementSignCone sigma} ->
      A.ArrangementComplement :=
  fun v =>
    ⟨Projectivization.mk' ℝ
        ⟨v.1, A.arrangementSignCone_ne_zero base sigma v.2⟩,
      by
        simpa only [Projectivization.mk'_eq_mk] using
          A.projectivization_mk_mem_arrangementComplement_of_mem_arrangementSignCone
            base sigma v.2⟩

theorem continuous_arrangementSignConeToComplement
    (A : FiniteProjectiveLineArrangement Line) (base : Line)
    (sigma : Line -> Bool) :
    Continuous (A.arrangementSignConeToComplement base sigma) := by
  unfold arrangementSignConeToComplement
  refine (continuous_quotient_mk'.comp
    (continuous_subtype_val.subtype_mk fun v =>
      A.arrangementSignCone_ne_zero base sigma v.2)).subtype_mk ?_

theorem arrangementSignConeToComplement_normalizedRepresentative
    (A : FiniteProjectiveLineArrangement Line) (base : Line)
    (p : A.ArrangementComplement) :
    A.arrangementSignConeToComplement base (A.arrangementPointSignPattern base p)
      ⟨A.arrangementNormalizedRepresentative base p,
        A.arrangementNormalizedRepresentative_mem_arrangementSignCone base p⟩ = p := by
  apply Subtype.ext
  simpa only [arrangementSignConeToComplement, Projectivization.mk'_eq_mk] using
    A.projectivization_mk_arrangementNormalizedRepresentative base p

/-- The preceding normalization lemma with the sign word made explicit.  This
form avoids dependent rewriting of a subtype witness after two sign words
have been identified. -/
theorem arrangementSignConeToComplement_normalizedRepresentative_of_eq
    (A : FiniteProjectiveLineArrangement Line) (base : Line)
    (sigma : Line -> Bool) (p : A.ArrangementComplement)
    (hsigma : sigma = A.arrangementPointSignPattern base p)
    (hp : A.arrangementNormalizedRepresentative base p ∈
      A.arrangementSignCone sigma) :
    A.arrangementSignConeToComplement base sigma
      ⟨A.arrangementNormalizedRepresentative base p, hp⟩ = p := by
  subst sigma
  exact A.arrangementSignConeToComplement_normalizedRepresentative base p

/-- Equal normalized sign patterns give a path in the genuine arrangement
complement.  The path is obtained by projecting a path in their common convex
homogeneous cone. -/
theorem same_arrangementPointSignPattern_joined
    (A : FiniteProjectiveLineArrangement Line) (base : Line)
    (p q : A.ArrangementComplement)
    (hsign : A.arrangementPointSignPattern base p =
      A.arrangementPointSignPattern base q) :
    Joined p q := by
  have hp : A.arrangementNormalizedRepresentative base p ∈
      A.arrangementSignCone (A.arrangementPointSignPattern base p) :=
    A.arrangementNormalizedRepresentative_mem_arrangementSignCone base p
  have hq : A.arrangementNormalizedRepresentative base q ∈
      A.arrangementSignCone (A.arrangementPointSignPattern base p) := by
    rw [hsign]
    exact A.arrangementNormalizedRepresentative_mem_arrangementSignCone base q
  have hpathConnected : IsPathConnected
      (A.arrangementSignCone (A.arrangementPointSignPattern base p)) :=
    (A.convex_arrangementSignCone _).isPathConnected
      ⟨A.arrangementNormalizedRepresentative base p, hp⟩
  have hjoinedCone : Joined
      (⟨A.arrangementNormalizedRepresentative base p, hp⟩ :
        {v : Fin 3 -> ℝ // v ∈
          A.arrangementSignCone (A.arrangementPointSignPattern base p)})
      ⟨A.arrangementNormalizedRepresentative base q, hq⟩ :=
    (hpathConnected.joinedIn
      (A.arrangementNormalizedRepresentative base p) hp
      (A.arrangementNormalizedRepresentative base q) hq).joined_subtype
  have htarget :
      A.arrangementSignConeToComplement base (A.arrangementPointSignPattern base p)
        ⟨A.arrangementNormalizedRepresentative base q, hq⟩ = q := by
    exact A.arrangementSignConeToComplement_normalizedRepresentative_of_eq
      base (A.arrangementPointSignPattern base p) q hsign hq
  exact ⟨(hjoinedCone.somePath.map
    (A.continuous_arrangementSignConeToComplement base
      (A.arrangementPointSignPattern base p))).cast
    (A.arrangementSignConeToComplement_normalizedRepresentative base p).symm
    htarget.symm⟩

/-- A selected point in each actual connected component.  This choice is used
only to code a component by its already intrinsic sign region. -/
noncomputable def arrangementFaceRepresentative
    (A : FiniteProjectiveLineArrangement Line) (F : A.ArrangementFace) :
    A.ArrangementComplement :=
  Classical.choose (A.arrangementFaceOf_surjective F)

theorem arrangementFaceRepresentative_faceOf
    (A : FiniteProjectiveLineArrangement Line) (F : A.ArrangementFace) :
    A.arrangementFaceOf (A.arrangementFaceRepresentative F) = F :=
  Classical.choose_spec (A.arrangementFaceOf_surjective F)

/-- A finite sign word associated to each actual face. -/
noncomputable def arrangementFaceSignPattern
    (A : FiniteProjectiveLineArrangement Line) (base : Line) :
    A.ArrangementFace -> Line -> Bool :=
  fun F => A.arrangementPointSignPattern base (A.arrangementFaceRepresentative F)

theorem arrangementFaceSignPattern_injective
    (A : FiniteProjectiveLineArrangement Line) (base : Line) :
    Function.Injective (A.arrangementFaceSignPattern base) := by
  intro F G hFG
  change A.arrangementPointSignPattern base (A.arrangementFaceRepresentative F) =
    A.arrangementPointSignPattern base (A.arrangementFaceRepresentative G) at hFG
  have hjoined := A.same_arrangementPointSignPattern_joined base
    (A.arrangementFaceRepresentative F) (A.arrangementFaceRepresentative G) hFG
  have hface : A.arrangementFaceOf (A.arrangementFaceRepresentative F) =
      A.arrangementFaceOf (A.arrangementFaceRepresentative G) :=
    (A.arrangementFaceOf_eq_iff_joined _ _).mpr hjoined
  calc
    F = A.arrangementFaceOf (A.arrangementFaceRepresentative F) :=
      (A.arrangementFaceRepresentative_faceOf F).symm
    _ = A.arrangementFaceOf (A.arrangementFaceRepresentative G) := hface
    _ = G := A.arrangementFaceRepresentative_faceOf G

/-- The quotient-topological real projective plane is path-connected.  This
is used only for the degenerate empty arrangement, where there is no line with
which to choose an affine sign chart. -/
theorem realProjectivePoint_pathConnected : PathConnectedSpace RealProjectivePoint := by
  have hfinrank : 1 < Module.finrank ℝ (Fin 3 -> ℝ) := by
    rw [Module.finrank_pi]
    norm_num
  have hrank : 1 < Module.rank ℝ (Fin 3 -> ℝ) :=
    Module.one_lt_rank_of_one_lt_finrank hfinrank
  letI : PathConnectedSpace {v : Fin 3 -> ℝ // v ≠ 0} :=
    isPathConnected_iff_pathConnectedSpace.mp (by
      simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using
        (isPathConnected_compl_singleton_of_one_lt_rank
          (E := Fin 3 -> ℝ) hrank (0 : Fin 3 -> ℝ)))
  exact @Quotient.instPathConnectedSpace
    {v : Fin 3 -> ℝ // v ≠ 0}
    (by infer_instance)
    (projectivizationSetoid ℝ (Fin 3 -> ℝ)) _

/-- In the empty arrangement the complement subtype is just the whole
projective plane. -/
def ambientPointToArrangementComplement_of_isEmpty
    (A : FiniteProjectiveLineArrangement Line) [IsEmpty Line] :
    RealProjectivePoint -> A.ArrangementComplement :=
  fun p => ⟨p, by
    change ∀ l : Line, ¬ A.Incident p l
    intro l
    exact isEmptyElim l⟩

theorem continuous_ambientPointToArrangementComplement_of_isEmpty
    (A : FiniteProjectiveLineArrangement Line) [IsEmpty Line] :
    Continuous (A.ambientPointToArrangementComplement_of_isEmpty) := by
  unfold ambientPointToArrangementComplement_of_isEmpty
  refine continuous_id.subtype_mk ?_

theorem joined_arrangementComplement_of_isEmpty
    (A : FiniteProjectiveLineArrangement Line) [IsEmpty Line]
    (p q : A.ArrangementComplement) : Joined p q := by
  letI : PathConnectedSpace RealProjectivePoint :=
    realProjectivePoint_pathConnected
  have hpathConnected : IsPathConnected (Set.univ : Set RealProjectivePoint) :=
    isPathConnected_univ
  have hjoined : Joined p.1 q.1 :=
    (hpathConnected.joinedIn p.1 (Set.mem_univ p.1)
      q.1 (Set.mem_univ q.1)).joined
  exact ⟨(hjoined.somePath.map
    (A.continuous_ambientPointToArrangementComplement_of_isEmpty)).cast
    (by apply Subtype.ext; rfl) (by apply Subtype.ext; rfl)⟩

theorem arrangementFace_subsingleton_of_isEmpty
    (A : FiniteProjectiveLineArrangement Line) [IsEmpty Line] :
    Subsingleton A.ArrangementFace := by
  constructor
  intro F G
  obtain ⟨p, hp⟩ := A.arrangementFaceOf_surjective F
  obtain ⟨q, hq⟩ := A.arrangementFaceOf_surjective G
  rw [← hp, ← hq]
  exact (A.arrangementFaceOf_eq_iff_joined p q).mpr
    (A.joined_arrangementComplement_of_isEmpty p q)

/-- The type of genuine arrangement faces is finite.  For a nonempty line
family we inject faces into finite normalized sign words; for the empty
family the projective plane itself is connected. -/
theorem finite_arrangementFace
    (A : FiniteProjectiveLineArrangement Line) : Finite A.ArrangementFace := by
  classical
  rcases isEmpty_or_nonempty Line with hLine | hLine
  · letI : IsEmpty Line := hLine
    letI : Subsingleton A.ArrangementFace :=
      A.arrangementFace_subsingleton_of_isEmpty
    exact Finite.of_subsingleton
  · let base : Line := Classical.choice hLine
    exact Finite.of_injective (A.arrangementFaceSignPattern base)
      (A.arrangementFaceSignPattern_injective base)

/-- A usable finite enumeration of the actual connected components. -/
@[reducible]
noncomputable def arrangementFaceFintype
    (A : FiniteProjectiveLineArrangement Line) : Fintype A.ArrangementFace := by
  letI : Finite A.ArrangementFace := A.finite_arrangementFace
  exact Fintype.ofFinite _

/-! ## Intrinsic signs on the quotient

The normalization used above chooses a representative in an affine chart.
That is ideal for convexity, but it is not itself a globally continuous
choice of representative.  The product of the base covector with any other
covector has invariant sign under projective rescaling: rescaling multiplies
it by a positive square.  This supplies a genuinely continuous sign map on
the quotient complement and upgrades the earlier finite injection to an
exact component classification.
-/

/-- The sign of the product of two homogeneous line evaluations.  Unlike a
single evaluation, this is unchanged by rescaling a representative and hence
is a well-defined function on `RP²`. -/
noncomputable def arrangementRelativeSign
    (A : FiniteProjectiveLineArrangement Line) (base l : Line) :
    RealProjectivePoint -> SignType :=
  Projectivization.lift
    (fun v => SignType.sign
      (projectiveLineEvaluation (A.projectiveLine base) v.1 *
        projectiveLineEvaluation (A.projectiveLine l) v.1))
    (by
      intro a b t hscale
      have ht : t ≠ 0 := by
        intro hzero
        apply a.2
        rw [hscale, hzero, zero_smul]
      have hvalue :
          projectiveLineEvaluation (A.projectiveLine base) a.1 *
              projectiveLineEvaluation (A.projectiveLine l) a.1 =
            (t * t) *
              (projectiveLineEvaluation (A.projectiveLine base) b.1 *
                projectiveLineEvaluation (A.projectiveLine l) b.1) := by
        rw [hscale]
        simp only [LinearMap.map_smul, smul_eq_mul]
        ring
      change SignType.sign
          (projectiveLineEvaluation (A.projectiveLine base) a.1 *
            projectiveLineEvaluation (A.projectiveLine l) a.1) =
        SignType.sign
          (projectiveLineEvaluation (A.projectiveLine base) b.1 *
            projectiveLineEvaluation (A.projectiveLine l) b.1)
      rw [hvalue, sign_mul, sign_pos (mul_self_pos.mpr ht), one_mul])

theorem arrangementRelativeSign_mk
    (A : FiniteProjectiveLineArrangement Line) (base l : Line)
    (v : Fin 3 -> ℝ) (hv : v ≠ 0) :
    A.arrangementRelativeSign base l (Projectivization.mk ℝ v hv) =
      SignType.sign
        (projectiveLineEvaluation (A.projectiveLine base) v *
          projectiveLineEvaluation (A.projectiveLine l) v) := by
  simp [arrangementRelativeSign]

theorem arrangementRelativeSign_apply_rep
    (A : FiniteProjectiveLineArrangement Line) (base l : Line)
    (p : RealProjectivePoint) :
    A.arrangementRelativeSign base l p =
      SignType.sign
        (projectiveLineEvaluation (A.projectiveLine base) p.rep *
          projectiveLineEvaluation (A.projectiveLine l) p.rep) := by
  calc
    A.arrangementRelativeSign base l p =
        A.arrangementRelativeSign base l
          (Projectivization.mk ℝ p.rep p.rep_nonzero) := by
      rw [p.mk_rep]
    _ = SignType.sign
        (projectiveLineEvaluation (A.projectiveLine base) p.rep *
          projectiveLineEvaluation (A.projectiveLine l) p.rep) :=
      A.arrangementRelativeSign_mk base l p.rep p.rep_nonzero

private theorem inv_mul_pos_iff_mul_pos (a b : ℝ) :
    0 < a⁻¹ * b ↔ 0 < a * b := by
  rw [show a⁻¹ * b = b / a by rw [div_eq_mul_inv, mul_comm],
    div_pos_iff, mul_pos_iff]
  constructor
  · rintro (h | h)
    · exact Or.inl ⟨h.2, h.1⟩
    · exact Or.inr ⟨h.2, h.1⟩
  · rintro (h | h)
    · exact Or.inl ⟨h.2, h.1⟩
    · exact Or.inr ⟨h.2, h.1⟩

/-- The chart-normalized Boolean code is exactly the positive part of the
intrinsic quotient sign. -/
theorem arrangementPointSignPattern_eq_relativeSign
    (A : FiniteProjectiveLineArrangement Line) (base : Line)
    (p : A.ArrangementComplement) :
    A.arrangementPointSignPattern base p = fun l =>
      decide (A.arrangementRelativeSign base l p.1 = 1) := by
  funext l
  unfold arrangementPointSignPattern
  apply Bool.decide_congr
  rw [A.arrangementRelativeSign_apply_rep, sign_eq_one_iff]
  unfold arrangementNormalizedRepresentative
  rw [LinearMap.map_smul]
  simpa only [smul_eq_mul] using
    (inv_mul_pos_iff_mul_pos
      (projectiveLineEvaluation (A.projectiveLine base) p.1.rep)
      (projectiveLineEvaluation (A.projectiveLine l) p.1.rep))

/-- Each intrinsic relative sign is continuous on the genuine complement.
The proof descends a continuous homogeneous expression through the quotient
map; no continuity of `Projectivization.rep` is used. -/
theorem continuousOn_arrangementRelativeSign
    (A : FiniteProjectiveLineArrangement Line) (base l : Line) :
    ContinuousOn (A.arrangementRelativeSign base l) A.arrangementComplement := by
  rw [isQuotientMap_projectivePoint_mk.continuousOn_isOpen_iff
    A.isOpen_arrangementComplement]
  refine continuousOn_of_forall_continuousAt ?_
  intro x hx
  rw [A.preimage_arrangementComplement_projectivePoint_mk] at hx
  have hbase :
      projectiveLineEvaluation (A.projectiveLine base) x.1 ≠ 0 :=
    Set.mem_iInter.mp hx base
  have hline :
      projectiveLineEvaluation (A.projectiveLine l) x.1 ≠ 0 :=
    Set.mem_iInter.mp hx l
  have hbaseContinuous :
      Continuous (fun z : {v : Fin 3 -> ℝ // v ≠ 0} =>
        projectiveLineEvaluation (A.projectiveLine base) z.1) :=
    (projectiveLineEvaluation (A.projectiveLine base)).continuous_of_finiteDimensional.comp
      continuous_subtype_val
  have hlineContinuous :
      Continuous (fun z : {v : Fin 3 -> ℝ // v ≠ 0} =>
        projectiveLineEvaluation (A.projectiveLine l) z.1) :=
    (projectiveLineEvaluation (A.projectiveLine l)).continuous_of_finiteDimensional.comp
      continuous_subtype_val
  have hproductContinuous :
      Continuous (fun z : {v : Fin 3 -> ℝ // v ≠ 0} =>
        projectiveLineEvaluation (A.projectiveLine base) z.1 *
          projectiveLineEvaluation (A.projectiveLine l) z.1) :=
    hbaseContinuous.mul hlineContinuous
  have hproductContinuousAt :
      ContinuousAt (fun z : {v : Fin 3 -> ℝ // v ≠ 0} =>
        projectiveLineEvaluation (A.projectiveLine base) z.1 *
          projectiveLineEvaluation (A.projectiveLine l) z.1) x :=
    hproductContinuous.continuousAt
  have hsignContinuousAt :
      ContinuousAt SignType.sign
        (projectiveLineEvaluation (A.projectiveLine base) x.1 *
          projectiveLineEvaluation (A.projectiveLine l) x.1) :=
    continuousAt_sign_of_ne_zero (mul_ne_zero hbase hline)
  have hcontinuousAt :
      ContinuousAt (fun z : {v : Fin 3 -> ℝ // v ≠ 0} =>
        SignType.sign
          (projectiveLineEvaluation (A.projectiveLine base) z.1 *
            projectiveLineEvaluation (A.projectiveLine l) z.1)) x :=
    ContinuousAt.comp'
      (f := fun z : {v : Fin 3 -> ℝ // v ≠ 0} =>
        projectiveLineEvaluation (A.projectiveLine base) z.1 *
          projectiveLineEvaluation (A.projectiveLine l) z.1)
      (x := x) hsignContinuousAt hproductContinuousAt
  simpa only [Function.comp_apply, arrangementRelativeSign,
    Projectivization.mk'_eq_mk, Projectivization.lift_mk] using hcontinuousAt

/-- The full intrinsic sign word on the complement. -/
noncomputable def arrangementRelativeSignPattern
    (A : FiniteProjectiveLineArrangement Line) (base : Line) :
    A.ArrangementComplement -> Line -> SignType :=
  fun p l => A.arrangementRelativeSign base l p.1

theorem continuous_arrangementRelativeSignPattern
    (A : FiniteProjectiveLineArrangement Line) (base : Line) :
    Continuous (A.arrangementRelativeSignPattern base) := by
  rw [continuous_pi_iff]
  intro l
  simpa only [arrangementRelativeSignPattern] using
    (A.continuousOn_arrangementRelativeSign base l).restrict

/-- A connected component of the actual complement has one intrinsic sign
word.  This uses only continuity into the finite discrete sign product. -/
theorem arrangementRelativeSignPattern_eq_of_arrangementFaceOf_eq
    (A : FiniteProjectiveLineArrangement Line) (base : Line)
    (p q : A.ArrangementComplement)
    (hface : A.arrangementFaceOf p = A.arrangementFaceOf q) :
    A.arrangementRelativeSignPattern base p =
      A.arrangementRelativeSignPattern base q := by
  have hcont := continuous_arrangementRelativeSignPattern A base
  exact hcont.image_eq_of_connectedComponent_eq p q
      ((A.arrangementFaceOf_eq_iff p q).mp hface)

/-- The normalized Boolean word is constant on every actual face. -/
theorem arrangementPointSignPattern_eq_of_arrangementFaceOf_eq
    (A : FiniteProjectiveLineArrangement Line) (base : Line)
    (p q : A.ArrangementComplement)
    (hface : A.arrangementFaceOf p = A.arrangementFaceOf q) :
    A.arrangementPointSignPattern base p =
      A.arrangementPointSignPattern base q := by
  rw [A.arrangementPointSignPattern_eq_relativeSign base p,
    A.arrangementPointSignPattern_eq_relativeSign base q]
  funext l
  exact congrArg (fun s : SignType => decide (s = 1))
    (congrFun
      (A.arrangementRelativeSignPattern_eq_of_arrangementFaceOf_eq
        base p q hface) l)

/-- Two complement points are in the same genuine face exactly when their
finite normalized sign words agree.  The reverse implication is the convex
cone path constructed above; the forward implication is now topological and
does not rely on a selected representative. -/
theorem arrangementFaceOf_eq_iff_arrangementPointSignPattern_eq
    (A : FiniteProjectiveLineArrangement Line) (base : Line)
    (p q : A.ArrangementComplement) :
    A.arrangementFaceOf p = A.arrangementFaceOf q ↔
      A.arrangementPointSignPattern base p =
        A.arrangementPointSignPattern base q := by
  constructor
  · exact A.arrangementPointSignPattern_eq_of_arrangementFaceOf_eq base p q
  · intro hsign
    exact (A.arrangementFaceOf_eq_iff_joined p q).mpr
      (A.same_arrangementPointSignPattern_joined base p q hsign)

/-- The path relation in the complement is exactly equality of its finite
strict-sign words. -/
theorem joined_iff_arrangementPointSignPattern_eq
    (A : FiniteProjectiveLineArrangement Line) (base : Line)
    (p q : A.ArrangementComplement) :
    Joined p q ↔ A.arrangementPointSignPattern base p =
      A.arrangementPointSignPattern base q := by
  rw [← A.arrangementFaceOf_eq_iff_joined,
    A.arrangementFaceOf_eq_iff_arrangementPointSignPattern_eq]

/-- The strict sign words that are actually realized by complement points.
This subtype deliberately excludes merely formal Boolean assignments whose
strict homogeneous cone is empty. -/
noncomputable def RealizedArrangementSignPattern
    (A : FiniteProjectiveLineArrangement Line) (base : Line) : Type _ :=
  {sigma : Line -> Bool // sigma ∈ Set.range (A.arrangementPointSignPattern base)}

/-- Genuine connected components of the complement are precisely the
realized strict-sign words.  Thus the finite face type contains no duplicate
copies of one sign region, and no unrealizable formal sign word is counted as
a face. -/
noncomputable def arrangementFaceSignPatternEquivRealized
    (A : FiniteProjectiveLineArrangement Line) (base : Line) :
    A.ArrangementFace ≃ A.RealizedArrangementSignPattern base :=
  Equiv.ofBijective
    (fun F =>
      ⟨A.arrangementFaceSignPattern base F,
        ⟨A.arrangementFaceRepresentative F, rfl⟩⟩)
    (by
      constructor
      · intro F G hFG
        apply A.arrangementFaceSignPattern_injective base
        exact congrArg (fun s : A.RealizedArrangementSignPattern base => s.1) hFG
      · rintro ⟨sigma, p, hp⟩
        refine ⟨A.arrangementFaceOf p, ?_⟩
        apply Subtype.ext
        change A.arrangementFaceSignPattern base (A.arrangementFaceOf p) = sigma
        calc
          A.arrangementFaceSignPattern base (A.arrangementFaceOf p) =
              A.arrangementPointSignPattern base
                (A.arrangementFaceRepresentative (A.arrangementFaceOf p)) := rfl
          _ = A.arrangementPointSignPattern base p :=
            A.arrangementPointSignPattern_eq_of_arrangementFaceOf_eq base _ p
              (A.arrangementFaceRepresentative_faceOf (A.arrangementFaceOf p))
          _ = sigma := hp)

/-! ## Actual face--edge incidence

The following boundary relation is intentionally defined through ambient
closures of the genuine complement components.  It is therefore a statement
about the projective arrangement itself, rather than an auxiliary
combinatorial incidence relation.  The remaining local theorem must show
that every nondegenerate open edge arc has exactly two such incident faces.
-/

/-- A genuine face is adjacent to a geometric edge when the closure of its
open carrier meets the open cyclic arc of that edge. -/
def geometricEdgeAdjacentFace
    (A : FiniteProjectiveLineArrangement Line) (e : A.GeometricEdge)
    (F : A.ArrangementFace) : Prop :=
  (A.geometricEdgeOpenArc e ∩ closure (A.arrangementFaceCarrier F)).Nonempty

/-- The finite set of geometric edges adjacent to a genuine face, defined
from actual ambient closure incidence. -/
noncomputable def arrangementFaceBoundary
    (A : FiniteProjectiveLineArrangement Line) (F : A.ArrangementFace) :
    Finset A.GeometricEdge := by
  classical
  exact Finset.univ.filter fun e => A.geometricEdgeAdjacentFace e F

theorem mem_arrangementFaceBoundary_iff
    (A : FiniteProjectiveLineArrangement Line) (F : A.ArrangementFace)
    (e : A.GeometricEdge) :
    e ∈ A.arrangementFaceBoundary F ↔ A.geometricEdgeAdjacentFace e F := by
  classical
  simp [arrangementFaceBoundary]

/-- The finite set of actual faces adjacent to one geometric edge. -/
noncomputable def geometricEdgeIncidentFaces
    (A : FiniteProjectiveLineArrangement Line) (e : A.GeometricEdge) :
    Finset A.ArrangementFace := by
  classical
  letI : Fintype A.ArrangementFace := A.arrangementFaceFintype
  exact Finset.univ.filter fun F => A.geometricEdgeAdjacentFace e F

theorem mem_geometricEdgeIncidentFaces_iff
    (A : FiniteProjectiveLineArrangement Line) (e : A.GeometricEdge)
    (F : A.ArrangementFace) :
    F ∈ A.geometricEdgeIncidentFaces e ↔ A.geometricEdgeAdjacentFace e F := by
  classical
  simp [geometricEdgeIncidentFaces]

/-! ## Local transverse perturbations

At an interior point of a geometric edge exactly one covector vanishes.  The
following elementary real-linear lemma records the uniform stability of all
the other signs under a small perturbation in the normal direction represented
by that covector.  It is the analytic input for proving that the closure
boundary relation above has exactly two sides.
-/

/-- Evaluation on Mathlib's fixed projective representative detects ordinary
incidence. -/
theorem projectiveLineEvaluation_rep_eq_zero_iff_incident
    (A : FiniteProjectiveLineArrangement Line) (p : RealProjectivePoint)
    (l : Line) :
    projectiveLineEvaluation (A.projectiveLine l) p.rep = 0 ↔ A.Incident p l := by
  constructor
  · intro hzero
    change p.orthogonal (A.projectiveLine l)
    rw [← p.mk_rep, ← (A.projectiveLine l).mk_rep,
      Projectivization.orthogonal_mk]
    simpa [projectiveLineEvaluation] using hzero
  · intro hincident
    change p.orthogonal (A.projectiveLine l) at hincident
    rw [← p.mk_rep, ← (A.projectiveLine l).mk_rep,
      Projectivization.orthogonal_mk] at hincident
    simpa [projectiveLineEvaluation] using hincident

/-- At a point incident with precisely `l`, every other homogeneous line
sign is stable for all sufficiently small normal perturbations
`q.rep + t • l.rep`. -/
theorem eventually_sign_perturbation_eq_of_regular
    (A : FiniteProjectiveLineArrangement Line) (q : RealProjectivePoint)
    (l : Line) (hregular : ∀ m : Line, A.Incident q m ↔ m = l) :
    ∀ᶠ t in nhds (0 : ℝ), ∀ m : Line, m ≠ l →
      SignType.sign
        (projectiveLineEvaluation (A.projectiveLine m)
          (q.rep + t • (A.projectiveLine l).rep)) =
        SignType.sign (projectiveLineEvaluation (A.projectiveLine m) q.rep) := by
  apply Filter.eventually_all.2
  intro m
  by_cases hml : m = l
  · exact Filter.Eventually.of_forall fun _ hne => (hne hml).elim
  · have hq : projectiveLineEvaluation (A.projectiveLine m) q.rep ≠ 0 := by
      intro hzero
      have hincident : A.Incident q m :=
        (A.projectiveLineEvaluation_rep_eq_zero_iff_incident q m).mp hzero
      exact hml ((hregular m).mp hincident)
    let g : ℝ → ℝ := fun t =>
      projectiveLineEvaluation (A.projectiveLine m)
        (q.rep + t • (A.projectiveLine l).rep)
    have hg : Continuous g := by
      dsimp [g]
      exact (projectiveLineEvaluation (A.projectiveLine m)).continuous_of_finiteDimensional.comp
        (continuous_const.add (continuous_id.smul continuous_const))
    have hgzero : g 0 = projectiveLineEvaluation (A.projectiveLine m) q.rep := by
      simp [g]
    have hsignAtG : ContinuousAt SignType.sign (g 0) := by
      rw [hgzero]
      exact continuousAt_sign_of_ne_zero hq
    have hsign : ContinuousAt (fun t => SignType.sign (g t)) 0 :=
      ContinuousAt.comp' (f := g) (x := 0) hsignAtG hg.continuousAt
    have heventually : ∀ᶠ t in nhds (0 : ℝ),
        SignType.sign (g t) = SignType.sign (g 0) := by
      have hsingleton : {SignType.sign (g 0)} ∈ nhds (SignType.sign (g 0)) :=
        (isOpen_discrete _).mem_nhds (by simp)
      simpa only [Set.mem_preimage, Set.mem_singleton_iff] using hsign hsingleton
    exact heventually.mono fun t ht _ => by simpa [g] using ht

/-- A metric-radius form of the preceding finite sign-stability statement. -/
theorem exists_pos_sign_perturbation_radius_of_regular
    (A : FiniteProjectiveLineArrangement Line) (q : RealProjectivePoint)
    (l : Line) (hregular : ∀ m : Line, A.Incident q m ↔ m = l) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ {t : ℝ}, |t| < ε → ∀ m : Line, m ≠ l →
      SignType.sign
        (projectiveLineEvaluation (A.projectiveLine m)
          (q.rep + t • (A.projectiveLine l).rep)) =
        SignType.sign (projectiveLineEvaluation (A.projectiveLine m) q.rep) := by
  obtain ⟨ε, hε, hstable⟩ := Metric.eventually_nhds_iff.mp
    (A.eventually_sign_perturbation_eq_of_regular q l hregular)
  refine ⟨ε, hε, ?_⟩
  intro t ht m hml
  exact hstable (y := t)
    (by
      show dist t (0 : ℝ) < ε
      simpa only [Real.dist_0_eq_abs] using ht)
    m hml

/-- Evaluation of a homogeneous covector along the normal perturbation is
the expected affine-linear function of the parameter. -/
theorem projectiveLineEvaluation_normalPerturbationVector
    (A : FiniteProjectiveLineArrangement Line) (q : RealProjectivePoint)
    (l m : Line) (t : ℝ) :
    projectiveLineEvaluation (A.projectiveLine m)
      (q.rep + t • (A.projectiveLine l).rep) =
      projectiveLineEvaluation (A.projectiveLine m) q.rep +
        t * projectiveLineEvaluation (A.projectiveLine m)
          (A.projectiveLine l).rep := by
  rw [LinearMap.map_add, LinearMap.map_smul]
  simp only [smul_eq_mul]

/-- The covector of a real projective line evaluates positively on its own
fixed representative. -/
theorem projectiveLineEvaluation_self_rep_pos (L : RealProjectiveLine) :
    0 < projectiveLineEvaluation L L.rep := by
  change 0 < L.rep ⬝ᵥ L.rep
  simpa using (dotProduct_self_star_pos_iff (v := L.rep)).mpr L.rep_nonzero

/-- Along a perturbation based at a point of `l`, the `l`-evaluation has the
same sign as the scalar parameter. -/
theorem projectiveLineEvaluation_normalPerturbationVector_self
    (A : FiniteProjectiveLineArrangement Line) (q : RealProjectivePoint)
    (l : Line) (hql : A.Incident q l) (t : ℝ) :
    projectiveLineEvaluation (A.projectiveLine l)
      (q.rep + t • (A.projectiveLine l).rep) =
      t * ((A.projectiveLine l).rep ⬝ᵥ (A.projectiveLine l).rep) := by
  have hqzero : projectiveLineEvaluation (A.projectiveLine l) q.rep = 0 :=
    (A.projectiveLineEvaluation_rep_eq_zero_iff_incident q l).mpr hql
  rw [A.projectiveLineEvaluation_normalPerturbationVector q l l t, hqzero]
  simp [projectiveLineEvaluation]

/-- The normal perturbation vector never vanishes: the initial vector lies
in the kernel of the supporting covector whereas the normal representative
does not. -/
theorem normalPerturbationVector_ne_zero
    (A : FiniteProjectiveLineArrangement Line) (q : RealProjectivePoint)
    (l : Line) (hql : A.Incident q l) (t : ℝ) :
    q.rep + t • (A.projectiveLine l).rep ≠ 0 := by
  intro hzero
  have hvalue := congrArg (projectiveLineEvaluation (A.projectiveLine l)) hzero
  rw [A.projectiveLineEvaluation_normalPerturbationVector_self q l hql t,
    LinearMap.map_zero] at hvalue
  rcases mul_eq_zero.mp hvalue with ht | hdot
  · subst t
    apply q.rep_nonzero
    simpa using hzero
  · have hdotne : (A.projectiveLine l).rep ⬝ᵥ (A.projectiveLine l).rep ≠ 0 :=
      ne_of_gt (by
        simpa [projectiveLineEvaluation] using
          (projectiveLineEvaluation_self_rep_pos (A.projectiveLine l)))
    exact hdotne hdot

/-- The genuine projective curve obtained by moving a regular point in the
normal direction of an arrangement line. -/
noncomputable def projectiveNormalPerturbation
    (A : FiniteProjectiveLineArrangement Line) (q : RealProjectivePoint)
    (l : Line) (hql : A.Incident q l) (t : ℝ) : RealProjectivePoint :=
  Projectivization.mk ℝ (q.rep + t • (A.projectiveLine l).rep)
    (A.normalPerturbationVector_ne_zero q l hql t)

theorem projectiveNormalPerturbation_zero
    (A : FiniteProjectiveLineArrangement Line) (q : RealProjectivePoint)
    (l : Line) (hql : A.Incident q l) :
    A.projectiveNormalPerturbation q l hql 0 = q := by
  simpa only [projectiveNormalPerturbation, zero_smul, add_zero] using q.mk_rep

theorem continuous_projectiveNormalPerturbation
    (A : FiniteProjectiveLineArrangement Line) (q : RealProjectivePoint)
    (l : Line) (hql : A.Incident q l) :
    Continuous (A.projectiveNormalPerturbation q l hql) := by
  have hvector : Continuous (fun t : ℝ =>
      q.rep + t • (A.projectiveLine l).rep) :=
    continuous_const.add (continuous_id.smul continuous_const)
  simpa only [projectiveNormalPerturbation, Projectivization.mk'_eq_mk] using
    continuous_quotient_mk'.comp
      (hvector.subtype_mk fun t => A.normalPerturbationVector_ne_zero q l hql t)

/-- Incidence of a normal perturbation can be read directly from its
homogeneous perturbation vector. -/
theorem projectiveNormalPerturbation_incident_iff
    (A : FiniteProjectiveLineArrangement Line) (q : RealProjectivePoint)
    (l : Line) (hql : A.Incident q l) (t : ℝ) (m : Line) :
    A.Incident (A.projectiveNormalPerturbation q l hql t) m ↔
      projectiveLineEvaluation (A.projectiveLine m)
        (q.rep + t • (A.projectiveLine l).rep) = 0 := by
  change Projectivization.orthogonal
      (Projectivization.mk ℝ
        (q.rep + t • (A.projectiveLine l).rep)
        (A.normalPerturbationVector_ne_zero q l hql t))
      (A.projectiveLine m) ↔ _
  rw [← (A.projectiveLine m).mk_rep]
  simpa [projectiveLineEvaluation] using
    (Projectivization.orthogonal_mk
      (A.normalPerturbationVector_ne_zero q l hql t)
      (A.projectiveLine m).rep_nonzero)

/-- A sufficiently small nonzero normal perturbation of a regular point is
in the genuine arrangement complement. -/
theorem projectiveNormalPerturbation_mem_arrangementComplement_of_regular
    (A : FiniteProjectiveLineArrangement Line) (q : RealProjectivePoint)
    (l : Line) (hregular : ∀ m : Line, A.Incident q m ↔ m = l)
    {ε t : ℝ} (hε : ∀ {s : ℝ}, |s| < ε → ∀ m : Line, m ≠ l →
      SignType.sign
        (projectiveLineEvaluation (A.projectiveLine m)
          (q.rep + s • (A.projectiveLine l).rep)) =
        SignType.sign (projectiveLineEvaluation (A.projectiveLine m) q.rep))
    (ht : t ≠ 0) (htsmall : |t| < ε) :
    A.projectiveNormalPerturbation q l ((hregular l).mpr rfl) t ∈
      A.arrangementComplement := by
  intro m hincident
  by_cases hml : m = l
  · subst m
    have hzero := (A.projectiveNormalPerturbation_incident_iff q l
      ((hregular l).mpr rfl) t l).mp hincident
    rw [A.projectiveLineEvaluation_normalPerturbationVector_self q l
      ((hregular l).mpr rfl) t] at hzero
    exact ht (mul_eq_zero.mp hzero |>.resolve_right
      (ne_of_gt (by simpa [projectiveLineEvaluation] using
        (projectiveLineEvaluation_self_rep_pos (A.projectiveLine l)))))
  · have hqne : projectiveLineEvaluation (A.projectiveLine m) q.rep ≠ 0 := by
      intro hzero
      apply hml
      exact (hregular m).mp
        ((A.projectiveLineEvaluation_rep_eq_zero_iff_incident q m).mp hzero)
    have hsign : SignType.sign
        (projectiveLineEvaluation (A.projectiveLine m)
          (q.rep + t • (A.projectiveLine l).rep)) ≠ 0 := by
      rw [hε htsmall m hml]
      exact sign_ne_zero.mpr hqne
    apply hsign
    exact sign_eq_zero_iff.mpr
      ((A.projectiveNormalPerturbation_incident_iff q l
        ((hregular l).mpr rfl) t m).mp hincident)

/-- Package a small nonzero normal perturbation as an actual complement
point. -/
noncomputable def normalPerturbationComplementOfRegular
    (A : FiniteProjectiveLineArrangement Line) (q : RealProjectivePoint)
    (l : Line) (hregular : ∀ m : Line, A.Incident q m ↔ m = l)
    {ε t : ℝ} (hε : ∀ {s : ℝ}, |s| < ε → ∀ m : Line, m ≠ l →
      SignType.sign
        (projectiveLineEvaluation (A.projectiveLine m)
          (q.rep + s • (A.projectiveLine l).rep)) =
        SignType.sign (projectiveLineEvaluation (A.projectiveLine m) q.rep))
    (ht : t ≠ 0) (htsmall : |t| < ε) : A.ArrangementComplement :=
  ⟨A.projectiveNormalPerturbation q l ((hregular l).mpr rfl) t,
    A.projectiveNormalPerturbation_mem_arrangementComplement_of_regular q l
      hregular hε ht htsmall⟩

@[simp] theorem normalPerturbationComplementOfRegular_val
    (A : FiniteProjectiveLineArrangement Line) (q : RealProjectivePoint)
    (l : Line) (hregular : ∀ m : Line, A.Incident q m ↔ m = l)
    {ε t : ℝ} (hε : ∀ {s : ℝ}, |s| < ε → ∀ m : Line, m ≠ l →
      SignType.sign
        (projectiveLineEvaluation (A.projectiveLine m)
          (q.rep + s • (A.projectiveLine l).rep)) =
        SignType.sign (projectiveLineEvaluation (A.projectiveLine m) q.rep))
    (ht : t ≠ 0) (htsmall : |t| < ε) :
    (A.normalPerturbationComplementOfRegular q l hregular hε ht htsmall).1 =
      A.projectiveNormalPerturbation q l ((hregular l).mpr rfl) t :=
  rfl

/-- Intrinsic relative signs may be evaluated on the explicit homogeneous
normal perturbation vector. -/
theorem arrangementRelativeSign_projectiveNormalPerturbation
    (A : FiniteProjectiveLineArrangement Line) (q : RealProjectivePoint)
    (l b m : Line) (hql : A.Incident q l) (t : ℝ) :
    A.arrangementRelativeSign b m
      (A.projectiveNormalPerturbation q l hql t) =
      SignType.sign
        (projectiveLineEvaluation (A.projectiveLine b)
          (q.rep + t • (A.projectiveLine l).rep) *
        projectiveLineEvaluation (A.projectiveLine m)
          (q.rep + t • (A.projectiveLine l).rep)) := by
  simpa only [projectiveNormalPerturbation] using
    A.arrangementRelativeSign_mk b m
      (q.rep + t • (A.projectiveLine l).rep)
      (A.normalPerturbationVector_ne_zero q l hql t)

/-- The intrinsic sign of the supporting covector is positive on the
positive normal side. -/
theorem sign_projectiveLineEvaluation_normalPerturbation_self_of_pos
    (A : FiniteProjectiveLineArrangement Line) (q : RealProjectivePoint)
    (l : Line) (hql : A.Incident q l) {t : ℝ} (ht : 0 < t) :
    SignType.sign
      (projectiveLineEvaluation (A.projectiveLine l)
        (q.rep + t • (A.projectiveLine l).rep)) = 1 := by
  rw [A.projectiveLineEvaluation_normalPerturbationVector_self q l hql t]
  exact sign_pos (mul_pos ht
    (by simpa [projectiveLineEvaluation] using
      (projectiveLineEvaluation_self_rep_pos (A.projectiveLine l))))

/-- The intrinsic sign of the supporting covector is negative on the
negative normal side. -/
theorem sign_projectiveLineEvaluation_normalPerturbation_self_of_neg
    (A : FiniteProjectiveLineArrangement Line) (q : RealProjectivePoint)
    (l : Line) (hql : A.Incident q l) {t : ℝ} (ht : t < 0) :
    SignType.sign
      (projectiveLineEvaluation (A.projectiveLine l)
        (q.rep + t • (A.projectiveLine l).rep)) = -1 := by
  rw [A.projectiveLineEvaluation_normalPerturbationVector_self q l hql t]
  exact sign_neg (mul_neg_of_neg_of_pos ht
    (by simpa [projectiveLineEvaluation] using
      (projectiveLineEvaluation_self_rep_pos (A.projectiveLine l))))

private theorem decide_sign_eq_one_ne_decide_neg_sign_eq_one
    (s : SignType) (hs : s ≠ 0) :
    decide (s = 1) ≠ decide (-s = 1) := by
  cases h : s <;> simp_all

/-- With a transverse base line, the positive and negative sufficiently
small normal perturbations of a regular point have different actual face
codes.  The `l` coordinate of the intrinsic relative sign changes by a
minus sign, while the transverse base sign is stable. -/
theorem arrangementPointSignPattern_normalPerturbation_pos_ne_neg
    (A : FiniteProjectiveLineArrangement Line) (q : RealProjectivePoint)
    (l b : Line) (hregular : ∀ m : Line, A.Incident q m ↔ m = l)
    (hbl : b ≠ l) {ε t : ℝ}
    (hε : ∀ {s : ℝ}, |s| < ε → ∀ m : Line, m ≠ l →
      SignType.sign
        (projectiveLineEvaluation (A.projectiveLine m)
          (q.rep + s • (A.projectiveLine l).rep)) =
        SignType.sign (projectiveLineEvaluation (A.projectiveLine m) q.rep))
    (ht : 0 < t) (htsmall : |t| < ε) :
    A.arrangementPointSignPattern b
      (A.normalPerturbationComplementOfRegular q l hregular hε
        (ne_of_gt ht) htsmall) ≠
    A.arrangementPointSignPattern b
      (A.normalPerturbationComplementOfRegular q l hregular hε
        (neg_ne_zero.mpr (ne_of_gt ht)) (by simpa using htsmall)) := by
  let ppos : A.ArrangementComplement :=
    A.normalPerturbationComplementOfRegular q l hregular hε
      (ne_of_gt ht) htsmall
  let pneg : A.ArrangementComplement :=
    A.normalPerturbationComplementOfRegular q l hregular hε
      (neg_ne_zero.mpr (ne_of_gt ht)) (by simpa using htsmall)
  have hbase0 :
      projectiveLineEvaluation (A.projectiveLine b) q.rep ≠ 0 := by
    intro hzero
    apply hbl
    exact (hregular b).mp
      ((A.projectiveLineEvaluation_rep_eq_zero_iff_incident q b).mp hzero)
  have hsmallneg : |-t| < ε := by simpa using htsmall
  have hbasePos :
      SignType.sign
        (projectiveLineEvaluation (A.projectiveLine b)
          (q.rep + t • (A.projectiveLine l).rep)) =
        SignType.sign (projectiveLineEvaluation (A.projectiveLine b) q.rep) :=
    hε htsmall b hbl
  have hbaseNeg :
      SignType.sign
        (projectiveLineEvaluation (A.projectiveLine b)
          (q.rep + (-t) • (A.projectiveLine l).rep)) =
        SignType.sign (projectiveLineEvaluation (A.projectiveLine b) q.rep) :=
    hε hsmallneg b hbl
  have hlPos :
      SignType.sign
        (projectiveLineEvaluation (A.projectiveLine l)
          (q.rep + t • (A.projectiveLine l).rep)) = 1 :=
    A.sign_projectiveLineEvaluation_normalPerturbation_self_of_pos q l
      ((hregular l).mpr rfl) ht
  have hlNeg :
      SignType.sign
        (projectiveLineEvaluation (A.projectiveLine l)
          (q.rep + (-t) • (A.projectiveLine l).rep)) = -1 :=
    A.sign_projectiveLineEvaluation_normalPerturbation_self_of_neg q l
      ((hregular l).mpr rfl) (neg_lt_zero.mpr ht)
  have hrPos : A.arrangementRelativeSign b l ppos.1 =
      SignType.sign (projectiveLineEvaluation (A.projectiveLine b) q.rep) := by
    change A.arrangementRelativeSign b l
        (A.projectiveNormalPerturbation q l ((hregular l).mpr rfl) t) = _
    rw [A.arrangementRelativeSign_projectiveNormalPerturbation q l b l
      ((hregular l).mpr rfl) t, sign_mul, hbasePos, hlPos, mul_one]
  have hrNeg : A.arrangementRelativeSign b l pneg.1 =
      -SignType.sign (projectiveLineEvaluation (A.projectiveLine b) q.rep) := by
    change A.arrangementRelativeSign b l
        (A.projectiveNormalPerturbation q l ((hregular l).mpr rfl) (-t)) = _
    rw [A.arrangementRelativeSign_projectiveNormalPerturbation q l b l
      ((hregular l).mpr rfl) (-t), sign_mul, hbaseNeg, hlNeg]
    simp
  intro hpattern
  have hcoordinate := congrFun hpattern l
  rw [A.arrangementPointSignPattern_eq_relativeSign b ppos,
    A.arrangementPointSignPattern_eq_relativeSign b pneg] at hcoordinate
  change decide (A.arrangementRelativeSign b l ppos.1 = 1) =
    decide (A.arrangementRelativeSign b l pneg.1 = 1) at hcoordinate
  rw [hrPos, hrNeg] at hcoordinate
  exact decide_sign_eq_one_ne_decide_neg_sign_eq_one _
    (sign_ne_zero.mpr hbase0) hcoordinate

/-- All sufficiently small perturbations on the positive side of a regular
line point have the same strict-sign word (with respect to every transverse
base).  Hence they lie in one actual complement component. -/
theorem arrangementPointSignPattern_normalPerturbation_eq_of_pos
    (A : FiniteProjectiveLineArrangement Line) (q : RealProjectivePoint)
    (l b : Line) (hregular : ∀ m : Line, A.Incident q m ↔ m = l)
    (hbl : b ≠ l) {ε s t : ℝ}
    (hε : ∀ {u : ℝ}, |u| < ε → ∀ m : Line, m ≠ l →
      SignType.sign
        (projectiveLineEvaluation (A.projectiveLine m)
          (q.rep + u • (A.projectiveLine l).rep)) =
        SignType.sign (projectiveLineEvaluation (A.projectiveLine m) q.rep))
    (hs : 0 < s) (ht : 0 < t) (hssmall : |s| < ε) (htsmall : |t| < ε) :
    A.arrangementPointSignPattern b
      (A.normalPerturbationComplementOfRegular q l hregular hε
        (ne_of_gt hs) hssmall) =
    A.arrangementPointSignPattern b
      (A.normalPerturbationComplementOfRegular q l hregular hε
        (ne_of_gt ht) htsmall) := by
  let ps : A.ArrangementComplement :=
    A.normalPerturbationComplementOfRegular q l hregular hε
      (ne_of_gt hs) hssmall
  let pt : A.ArrangementComplement :=
    A.normalPerturbationComplementOfRegular q l hregular hε
      (ne_of_gt ht) htsmall
  rw [A.arrangementPointSignPattern_eq_relativeSign b ps,
    A.arrangementPointSignPattern_eq_relativeSign b pt]
  funext m
  apply Bool.decide_congr
  have hbaseS :
      SignType.sign
        (projectiveLineEvaluation (A.projectiveLine b)
          (q.rep + s • (A.projectiveLine l).rep)) =
        SignType.sign (projectiveLineEvaluation (A.projectiveLine b) q.rep) :=
    hε hssmall b hbl
  have hbaseT :
      SignType.sign
        (projectiveLineEvaluation (A.projectiveLine b)
          (q.rep + t • (A.projectiveLine l).rep)) =
        SignType.sign (projectiveLineEvaluation (A.projectiveLine b) q.rep) :=
    hε htsmall b hbl
  change A.arrangementRelativeSign b m ps.1 = 1 ↔
    A.arrangementRelativeSign b m pt.1 = 1
  have hrelative : A.arrangementRelativeSign b m ps.1 =
      A.arrangementRelativeSign b m pt.1 := by
    change A.arrangementRelativeSign b m
        (A.projectiveNormalPerturbation q l ((hregular l).mpr rfl) s) =
      A.arrangementRelativeSign b m
        (A.projectiveNormalPerturbation q l ((hregular l).mpr rfl) t)
    rw [A.arrangementRelativeSign_projectiveNormalPerturbation q l b m
      ((hregular l).mpr rfl) s,
      A.arrangementRelativeSign_projectiveNormalPerturbation q l b m
        ((hregular l).mpr rfl) t,
      sign_mul, sign_mul, hbaseS, hbaseT]
    by_cases hml : m = l
    · subst m
      rw [A.sign_projectiveLineEvaluation_normalPerturbation_self_of_pos q l
          ((hregular l).mpr rfl) hs,
        A.sign_projectiveLineEvaluation_normalPerturbation_self_of_pos q l
          ((hregular l).mpr rfl) ht,
        mul_one]
    · rw [hε hssmall m hml, hε htsmall m hml]
  rw [hrelative]

/-- All sufficiently small perturbations on the negative side of a regular
line point have the same strict-sign word.  This is the companion to the
positive-side statement above; keeping the two statements separate makes the
two actual adjacent components available without choosing an orientation of
the projective line. -/
theorem arrangementPointSignPattern_normalPerturbation_eq_of_neg
    (A : FiniteProjectiveLineArrangement Line) (q : RealProjectivePoint)
    (l b : Line) (hregular : ∀ m : Line, A.Incident q m ↔ m = l)
    (hbl : b ≠ l) {ε s t : ℝ}
    (hε : ∀ {u : ℝ}, |u| < ε → ∀ m : Line, m ≠ l →
      SignType.sign
        (projectiveLineEvaluation (A.projectiveLine m)
          (q.rep + u • (A.projectiveLine l).rep)) =
        SignType.sign (projectiveLineEvaluation (A.projectiveLine m) q.rep))
    (hs : s < 0) (ht : t < 0) (hssmall : |s| < ε) (htsmall : |t| < ε) :
    A.arrangementPointSignPattern b
      (A.normalPerturbationComplementOfRegular q l hregular hε
        (ne_of_lt hs) hssmall) =
    A.arrangementPointSignPattern b
      (A.normalPerturbationComplementOfRegular q l hregular hε
        (ne_of_lt ht) htsmall) := by
  let ps : A.ArrangementComplement :=
    A.normalPerturbationComplementOfRegular q l hregular hε
      (ne_of_lt hs) hssmall
  let pt : A.ArrangementComplement :=
    A.normalPerturbationComplementOfRegular q l hregular hε
      (ne_of_lt ht) htsmall
  rw [A.arrangementPointSignPattern_eq_relativeSign b ps,
    A.arrangementPointSignPattern_eq_relativeSign b pt]
  funext m
  apply Bool.decide_congr
  have hbaseS :
      SignType.sign
        (projectiveLineEvaluation (A.projectiveLine b)
          (q.rep + s • (A.projectiveLine l).rep)) =
        SignType.sign (projectiveLineEvaluation (A.projectiveLine b) q.rep) :=
    hε hssmall b hbl
  have hbaseT :
      SignType.sign
        (projectiveLineEvaluation (A.projectiveLine b)
          (q.rep + t • (A.projectiveLine l).rep)) =
        SignType.sign (projectiveLineEvaluation (A.projectiveLine b) q.rep) :=
    hε htsmall b hbl
  change A.arrangementRelativeSign b m ps.1 = 1 ↔
    A.arrangementRelativeSign b m pt.1 = 1
  have hrelative : A.arrangementRelativeSign b m ps.1 =
      A.arrangementRelativeSign b m pt.1 := by
    change A.arrangementRelativeSign b m
        (A.projectiveNormalPerturbation q l ((hregular l).mpr rfl) s) =
      A.arrangementRelativeSign b m
        (A.projectiveNormalPerturbation q l ((hregular l).mpr rfl) t)
    rw [A.arrangementRelativeSign_projectiveNormalPerturbation q l b m
      ((hregular l).mpr rfl) s,
      A.arrangementRelativeSign_projectiveNormalPerturbation q l b m
        ((hregular l).mpr rfl) t,
      sign_mul, sign_mul, hbaseS, hbaseT]
    by_cases hml : m = l
    · subst m
      rw [A.sign_projectiveLineEvaluation_normalPerturbation_self_of_neg q l
          ((hregular l).mpr rfl) hs,
        A.sign_projectiveLineEvaluation_normalPerturbation_self_of_neg q l
          ((hregular l).mpr rfl) ht]
    · rw [hε hssmall m hml, hε htsmall m hml]
  rw [hrelative]

/-- The genuine face represented by any sufficiently small positive normal
perturbation has the regular point in its ambient closure. -/
theorem mem_closure_arrangementFaceCarrier_normalPerturbation_of_pos
    (A : FiniteProjectiveLineArrangement Line) (q : RealProjectivePoint)
    (l b : Line) (hregular : ∀ m : Line, A.Incident q m ↔ m = l)
    (hbl : b ≠ l) {ε t : ℝ}
    (hε : ∀ {u : ℝ}, |u| < ε → ∀ m : Line, m ≠ l →
      SignType.sign
        (projectiveLineEvaluation (A.projectiveLine m)
          (q.rep + u • (A.projectiveLine l).rep)) =
        SignType.sign (projectiveLineEvaluation (A.projectiveLine m) q.rep))
    (ht : 0 < t) (htsmall : |t| < ε) :
    q ∈ closure (A.arrangementFaceCarrier
      (A.arrangementFaceOf
        (A.normalPerturbationComplementOfRegular q l hregular hε
          (ne_of_gt ht) htsmall))) := by
  let pt : A.ArrangementComplement :=
    A.normalPerturbationComplementOfRegular q l hregular hε
      (ne_of_gt ht) htsmall
  have hεpos : 0 < ε :=
    lt_of_le_of_lt (abs_nonneg t) htsmall
  have hmaps : Set.MapsTo
      (A.projectiveNormalPerturbation q l ((hregular l).mpr rfl))
      (Set.Ioo (0 : ℝ) ε)
      (A.arrangementFaceCarrier (A.arrangementFaceOf pt)) := by
    intro s hs
    have hsabs : |s| < ε := by
      rw [abs_of_pos hs.1]
      exact hs.2
    let ps : A.ArrangementComplement :=
      A.normalPerturbationComplementOfRegular q l hregular hε
        (ne_of_gt hs.1) hsabs
    change ps.1 ∈ A.arrangementFaceCarrier (A.arrangementFaceOf pt)
    have hpattern : A.arrangementPointSignPattern b ps =
        A.arrangementPointSignPattern b pt := by
      simpa only [ps, pt] using
        (A.arrangementPointSignPattern_normalPerturbation_eq_of_pos q l b
          hregular hbl hε hs.1 ht hsabs htsmall)
    have hface : A.arrangementFaceOf ps = A.arrangementFaceOf pt :=
      (A.arrangementFaceOf_eq_iff_arrangementPointSignPattern_eq b ps pt).mpr
        hpattern
    rw [← hface]
    exact A.mem_arrangementFaceCarrier_faceOf ps
  have hzero : (0 : ℝ) ∈ closure (Set.Ioo (0 : ℝ) ε) := by
    rw [closure_Ioo hεpos.ne]
    exact ⟨le_rfl, hεpos.le⟩
  have hclosure :
      A.projectiveNormalPerturbation q l ((hregular l).mpr rfl) 0 ∈
        closure (A.arrangementFaceCarrier (A.arrangementFaceOf pt)) :=
    ContinuousWithinAt.mem_closure
      ((A.continuous_projectiveNormalPerturbation q l ((hregular l).mpr rfl)).continuousAt.continuousWithinAt)
      hzero hmaps
  simpa only [A.projectiveNormalPerturbation_zero q l ((hregular l).mpr rfl)] using
    hclosure

/-- The genuine face represented by any sufficiently small negative normal
perturbation has the regular point in its ambient closure. -/
theorem mem_closure_arrangementFaceCarrier_normalPerturbation_of_neg
    (A : FiniteProjectiveLineArrangement Line) (q : RealProjectivePoint)
    (l b : Line) (hregular : ∀ m : Line, A.Incident q m ↔ m = l)
    (hbl : b ≠ l) {ε t : ℝ}
    (hε : ∀ {u : ℝ}, |u| < ε → ∀ m : Line, m ≠ l →
      SignType.sign
        (projectiveLineEvaluation (A.projectiveLine m)
          (q.rep + u • (A.projectiveLine l).rep)) =
        SignType.sign (projectiveLineEvaluation (A.projectiveLine m) q.rep))
    (ht : t < 0) (htsmall : |t| < ε) :
    q ∈ closure (A.arrangementFaceCarrier
      (A.arrangementFaceOf
        (A.normalPerturbationComplementOfRegular q l hregular hε
          (ne_of_lt ht) htsmall))) := by
  let pt : A.ArrangementComplement :=
    A.normalPerturbationComplementOfRegular q l hregular hε
      (ne_of_lt ht) htsmall
  have hεpos : 0 < ε :=
    lt_of_le_of_lt (abs_nonneg t) htsmall
  have hmaps : Set.MapsTo
      (A.projectiveNormalPerturbation q l ((hregular l).mpr rfl))
      (Set.Ioo (-ε) (0 : ℝ))
      (A.arrangementFaceCarrier (A.arrangementFaceOf pt)) := by
    intro s hs
    have hsabs : |s| < ε := by
      rw [abs_of_neg hs.2]
      simpa using (neg_lt_neg hs.1)
    let ps : A.ArrangementComplement :=
      A.normalPerturbationComplementOfRegular q l hregular hε
        (ne_of_lt hs.2) hsabs
    change ps.1 ∈ A.arrangementFaceCarrier (A.arrangementFaceOf pt)
    have hpattern : A.arrangementPointSignPattern b ps =
        A.arrangementPointSignPattern b pt := by
      simpa only [ps, pt] using
        (A.arrangementPointSignPattern_normalPerturbation_eq_of_neg q l b
          hregular hbl hε hs.2 ht hsabs htsmall)
    have hface : A.arrangementFaceOf ps = A.arrangementFaceOf pt :=
      (A.arrangementFaceOf_eq_iff_arrangementPointSignPattern_eq b ps pt).mpr
        hpattern
    rw [← hface]
    exact A.mem_arrangementFaceCarrier_faceOf ps
  have hzero : (0 : ℝ) ∈ closure (Set.Ioo (-ε) (0 : ℝ)) := by
    rw [closure_Ioo (neg_ne_zero.mpr hεpos.ne')]
    exact ⟨neg_nonpos.mpr hεpos.le, le_rfl⟩
  have hclosure :
      A.projectiveNormalPerturbation q l ((hregular l).mpr rfl) 0 ∈
        closure (A.arrangementFaceCarrier (A.arrangementFaceOf pt)) :=
    ContinuousWithinAt.mem_closure
      ((A.continuous_projectiveNormalPerturbation q l ((hregular l).mpr rfl)).continuousAt.continuousWithinAt)
      hzero hmaps
  simpa only [A.projectiveNormalPerturbation_zero q l ((hregular l).mpr rfl)] using
    hclosure

/-- A regular point of a non-pencil arrangement has two distinct genuine
complement faces in its ambient boundary.  The faces are obtained from the
positive and negative normal perturbations, rather than postulated as local
germs. -/
theorem exists_two_distinct_arrangementFaces_mem_closure_of_regular
    (A : FiniteProjectiveLineArrangement Line) (hA : A.NonPencil)
    (q : RealProjectivePoint) (l : Line)
    (hregular : ∀ m : Line, A.Incident q m ↔ m = l) :
    ∃ Fpos Fneg : A.ArrangementFace,
      Fpos ≠ Fneg ∧
        q ∈ closure (A.arrangementFaceCarrier Fpos) ∧
        q ∈ closure (A.arrangementFaceCarrier Fneg) := by
  rcases A.exists_ne_line_of_nonPencil hA l with ⟨b, hbl⟩
  rcases A.exists_pos_sign_perturbation_radius_of_regular q l hregular with
    ⟨ε, hεpos, hε⟩
  let t : ℝ := ε / 2
  have ht : 0 < t := by
    dsimp [t]
    exact half_pos hεpos
  have htsmall : |t| < ε := by
    rw [abs_of_pos ht]
    exact half_lt_self hεpos
  have hneg : -t < 0 := neg_lt_zero.mpr ht
  have hnegsmall : |-t| < ε := by simpa using htsmall
  let ppos : A.ArrangementComplement :=
    A.normalPerturbationComplementOfRegular q l hregular hε
      (ne_of_gt ht) htsmall
  let pneg : A.ArrangementComplement :=
    A.normalPerturbationComplementOfRegular q l hregular hε
      (ne_of_lt hneg) hnegsmall
  refine ⟨A.arrangementFaceOf ppos, A.arrangementFaceOf pneg, ?_, ?_, ?_⟩
  · intro hface
    have hpattern : A.arrangementPointSignPattern b ppos =
        A.arrangementPointSignPattern b pneg :=
      (A.arrangementFaceOf_eq_iff_arrangementPointSignPattern_eq b ppos pneg).mp
        hface
    exact A.arrangementPointSignPattern_normalPerturbation_pos_ne_neg q l b
      hregular hbl hε ht htsmall (by simpa only [ppos, pneg] using hpattern)
  · simpa only [ppos] using
      (A.mem_closure_arrangementFaceCarrier_normalPerturbation_of_pos q l b
        hregular hbl hε ht htsmall)
  · simpa only [pneg] using
      (A.mem_closure_arrangementFaceCarrier_normalPerturbation_of_neg q l b
        hregular hbl hε hneg hnegsmall)

/-- Every chosen interior point of a geometric edge in a non-pencil
arrangement witnesses two distinct actual adjacent faces.  This is a lower
two-sidedness statement for the already geometric cyclic edge, with no
combinatorial cellulation record assumed. -/
theorem exists_two_distinct_geometricEdgeAdjacentFaces_at
    (A : FiniteProjectiveLineArrangement Line) (hA : A.NonPencil)
    (e : A.GeometricEdge) {q : RealProjectivePoint}
    (hq : q ∈ A.geometricEdgeOpenArc e) :
    ∃ Fpos Fneg : A.ArrangementFace,
      Fpos ≠ Fneg ∧ A.geometricEdgeAdjacentFace e Fpos ∧
        A.geometricEdgeAdjacentFace e Fneg := by
  obtain ⟨Fpos, Fneg, hne, hpos, hneg⟩ :=
    A.exists_two_distinct_arrangementFaces_mem_closure_of_regular hA q
      (A.edgeSlotLine e) (fun m => A.geometricEdgeOpenArc_incident_iff e hq m)
  exact ⟨Fpos, Fneg, hne, ⟨q, hq, hpos⟩, ⟨q, hq, hneg⟩⟩

/-! ## The upper local two-side bound

For the converse bound we work at one regular point.  A relative sign is
continuous in a neighbourhood in which its two defining covectors do not
vanish, including a point on a third line of the arrangement.  This lets a
closure face inherit every transverse sign from that regular point. -/

/-- The open locus on which the two covectors defining a relative sign are
both nonzero. -/
def relativeSignDomain (A : FiniteProjectiveLineArrangement Line)
    (base l : Line) : Set RealProjectivePoint :=
  {p | ¬ A.Incident p base ∧ ¬ A.Incident p l}

theorem preimage_relativeSignDomain_projectivePoint_mk
    (A : FiniteProjectiveLineArrangement Line) (base l : Line) :
    (Projectivization.mk' ℝ :
      {v : Fin 3 → ℝ // v ≠ 0} → RealProjectivePoint) ⁻¹'
        A.relativeSignDomain base l =
      {v : {v : Fin 3 → ℝ // v ≠ 0} |
        projectiveLineEvaluation (A.projectiveLine base) v.1 ≠ 0} ∩
      {v : {v : Fin 3 → ℝ // v ≠ 0} |
        projectiveLineEvaluation (A.projectiveLine l) v.1 ≠ 0} := by
  ext v
  simp only [Set.mem_preimage, relativeSignDomain, Set.mem_setOf_eq,
    Set.mem_inter_iff]
  constructor
  · rintro ⟨hbase, hline⟩
    constructor
    · intro hzero
      apply hbase
      change (Projectivization.mk' ℝ v).orthogonal (A.projectiveLine base)
      rw [Projectivization.mk'_eq_mk, ← (A.projectiveLine base).mk_rep,
        Projectivization.orthogonal_mk]
      simpa [projectiveLineEvaluation] using hzero
    · intro hzero
      apply hline
      change (Projectivization.mk' ℝ v).orthogonal (A.projectiveLine l)
      rw [Projectivization.mk'_eq_mk, ← (A.projectiveLine l).mk_rep,
        Projectivization.orthogonal_mk]
      simpa [projectiveLineEvaluation] using hzero
  · rintro ⟨hbase, hline⟩
    constructor
    · intro hincident
      have hzero : projectiveLineEvaluation (A.projectiveLine base) v.1 = 0 := by
        change (Projectivization.mk' ℝ v).orthogonal (A.projectiveLine base) at hincident
        rw [Projectivization.mk'_eq_mk, ← (A.projectiveLine base).mk_rep,
          Projectivization.orthogonal_mk] at hincident
        simpa [projectiveLineEvaluation] using hincident
      exact hbase hzero
    · intro hincident
      have hzero : projectiveLineEvaluation (A.projectiveLine l) v.1 = 0 := by
        change (Projectivization.mk' ℝ v).orthogonal (A.projectiveLine l) at hincident
        rw [Projectivization.mk'_eq_mk, ← (A.projectiveLine l).mk_rep,
          Projectivization.orthogonal_mk] at hincident
        simpa [projectiveLineEvaluation] using hincident
      exact hline hzero

theorem isOpen_relativeSignDomain
    (A : FiniteProjectiveLineArrangement Line) (base l : Line) :
    IsOpen (A.relativeSignDomain base l) := by
  rw [← isQuotientMap_projectivePoint_mk.isOpen_preimage,
    A.preimage_relativeSignDomain_projectivePoint_mk]
  have hne : IsOpen {z : ℝ | z ≠ 0} := by
    simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using
      (isClosed_singleton : IsClosed ({0} : Set ℝ)).isOpen_compl
  exact
    (((projectiveLineEvaluation (A.projectiveLine base)).continuous_of_finiteDimensional.comp
      continuous_subtype_val).isOpen_preimage _ hne).inter
    (((projectiveLineEvaluation (A.projectiveLine l)).continuous_of_finiteDimensional.comp
      continuous_subtype_val).isOpen_preimage _ hne)

/-- Relative sign is continuous on its natural nonvanishing domain. -/
theorem continuousOn_arrangementRelativeSign_relativeSignDomain
    (A : FiniteProjectiveLineArrangement Line) (base l : Line) :
    ContinuousOn (A.arrangementRelativeSign base l) (A.relativeSignDomain base l) := by
  rw [isQuotientMap_projectivePoint_mk.continuousOn_isOpen_iff
    (A.isOpen_relativeSignDomain base l),
    A.preimage_relativeSignDomain_projectivePoint_mk]
  refine continuousOn_of_forall_continuousAt ?_
  intro x hx
  have hbase :
      projectiveLineEvaluation (A.projectiveLine base) x.1 ≠ 0 := hx.1
  have hline :
      projectiveLineEvaluation (A.projectiveLine l) x.1 ≠ 0 := hx.2
  have hbaseContinuous :
      Continuous (fun z : {v : Fin 3 → ℝ // v ≠ 0} =>
        projectiveLineEvaluation (A.projectiveLine base) z.1) :=
    (projectiveLineEvaluation (A.projectiveLine base)).continuous_of_finiteDimensional.comp
      continuous_subtype_val
  have hlineContinuous :
      Continuous (fun z : {v : Fin 3 → ℝ // v ≠ 0} =>
        projectiveLineEvaluation (A.projectiveLine l) z.1) :=
    (projectiveLineEvaluation (A.projectiveLine l)).continuous_of_finiteDimensional.comp
      continuous_subtype_val
  have hproductContinuous :
      Continuous (fun z : {v : Fin 3 → ℝ // v ≠ 0} =>
        projectiveLineEvaluation (A.projectiveLine base) z.1 *
          projectiveLineEvaluation (A.projectiveLine l) z.1) :=
    hbaseContinuous.mul hlineContinuous
  have hproductContinuousAt :
      ContinuousAt (fun z : {v : Fin 3 → ℝ // v ≠ 0} =>
        projectiveLineEvaluation (A.projectiveLine base) z.1 *
          projectiveLineEvaluation (A.projectiveLine l) z.1) x :=
    hproductContinuous.continuousAt
  have hsignContinuousAt :
      ContinuousAt SignType.sign
        (projectiveLineEvaluation (A.projectiveLine base) x.1 *
          projectiveLineEvaluation (A.projectiveLine l) x.1) :=
    continuousAt_sign_of_ne_zero (mul_ne_zero hbase hline)
  have hcontinuousAt :
      ContinuousAt (fun z : {v : Fin 3 → ℝ // v ≠ 0} =>
        SignType.sign
          (projectiveLineEvaluation (A.projectiveLine base) z.1 *
            projectiveLineEvaluation (A.projectiveLine l) z.1)) x :=
    ContinuousAt.comp'
      (f := fun z : {v : Fin 3 → ℝ // v ≠ 0} =>
        projectiveLineEvaluation (A.projectiveLine base) z.1 *
          projectiveLineEvaluation (A.projectiveLine l) z.1)
      (x := x) hsignContinuousAt hproductContinuousAt
  simpa only [Function.comp_apply, arrangementRelativeSign,
    Projectivization.mk'_eq_mk, Projectivization.lift_mk] using hcontinuousAt

/-- The quotient-invariant relative sign is continuous at every point where
its base and target covectors are both nonzero. -/
theorem continuousAt_arrangementRelativeSign_of_not_incident
    (A : FiniteProjectiveLineArrangement Line) (q : RealProjectivePoint)
    (base l : Line) (hbase : ¬ A.Incident q base) (hline : ¬ A.Incident q l) :
    ContinuousAt (A.arrangementRelativeSign base l) q :=
  (A.continuousOn_arrangementRelativeSign_relativeSignDomain base l).continuousAt
    ((A.isOpen_relativeSignDomain base l).mem_nhds ⟨hbase, hline⟩)

/-- A face whose carrier accumulates at a point inherits each relative sign
which is continuous at that point. -/
theorem arrangementRelativeSign_arrangementFaceRepresentative_eq_of_mem_closure
    (A : FiniteProjectiveLineArrangement Line) (q : RealProjectivePoint)
    (base l : Line) (F : A.ArrangementFace)
    (hbase : ¬ A.Incident q base) (hline : ¬ A.Incident q l)
    (hF : q ∈ closure (A.arrangementFaceCarrier F)) :
    A.arrangementRelativeSign base l (A.arrangementFaceRepresentative F).1 =
      A.arrangementRelativeSign base l q := by
  have hcontinuous : ContinuousAt (A.arrangementRelativeSign base l) q :=
    A.continuousAt_arrangementRelativeSign_of_not_incident q base l hbase hline
  have hsingleton : {A.arrangementRelativeSign base l q} ∈
      nhds (A.arrangementRelativeSign base l q) :=
    (isOpen_discrete _).mem_nhds (by simp)
  have hfiber : (A.arrangementRelativeSign base l) ⁻¹'
      {A.arrangementRelativeSign base l q} ∈ nhds q :=
    hcontinuous hsingleton
  obtain ⟨r, hrvalue, hrcarrier⟩ :=
    mem_closure_iff_nhds.mp hF _ hfiber
  rcases hrcarrier with ⟨r', hrface, hrval⟩
  have hrfaceEq : A.arrangementFaceOf r' = F := by
    change A.arrangementFaceOf r' ∈ ({F} : Set A.ArrangementFace) at hrface
    simpa using hrface
  have hfaces : A.arrangementFaceOf r' =
      A.arrangementFaceOf (A.arrangementFaceRepresentative F) := by
    rw [hrfaceEq, A.arrangementFaceRepresentative_faceOf]
  have hsigns : A.arrangementRelativeSign base l r'.1 =
      A.arrangementRelativeSign base l (A.arrangementFaceRepresentative F).1 :=
    congrFun
      (A.arrangementRelativeSignPattern_eq_of_arrangementFaceOf_eq base r'
        (A.arrangementFaceRepresentative F) hfaces) l
  have hrvalue' : A.arrangementRelativeSign base l r =
      A.arrangementRelativeSign base l q := by
    simpa only [Set.mem_preimage, Set.mem_singleton_iff] using hrvalue
  calc
    A.arrangementRelativeSign base l (A.arrangementFaceRepresentative F).1 =
        A.arrangementRelativeSign base l r'.1 := hsigns.symm
    _ = A.arrangementRelativeSign base l r := by rw [hrval]
    _ = A.arrangementRelativeSign base l q := hrvalue'

private theorem arrangementRelativeSign_ne_zero_of_arrangementComplement
    (A : FiniteProjectiveLineArrangement Line) (p : A.ArrangementComplement)
    (base l : Line) : A.arrangementRelativeSign base l p.1 ≠ 0 := by
  rw [A.arrangementRelativeSign_apply_rep]
  apply sign_ne_zero.mpr
  apply mul_ne_zero
  · intro hzero
    exact p.2 base
      ((A.projectiveLineEvaluation_rep_eq_zero_iff_incident p.1 base).mp hzero)
  · intro hzero
    exact p.2 l
      ((A.projectiveLineEvaluation_rep_eq_zero_iff_incident p.1 l).mp hzero)

private theorem relativeSign_eq_of_ne_zero_of_decide_eq
    (s t : SignType) (hs : s ≠ 0) (ht : t ≠ 0)
    (h : decide (s = 1) = decide (t = 1)) : s = t := by
  cases hs' : s <;> cases ht' : t <;> simp_all

/-- At a regular point, the relative `l`-sign completely determines any
incident face: all transverse signs are forced by closure continuity. -/
theorem arrangementFace_eq_of_mem_closure_of_regular_relativeSign_eq
    (A : FiniteProjectiveLineArrangement Line)
    (q : RealProjectivePoint) (l b : Line)
    (hregular : ∀ m : Line, A.Incident q m ↔ m = l)
    (hbl : b ≠ l)
    (F G : A.ArrangementFace)
    (hF : q ∈ closure (A.arrangementFaceCarrier F))
    (hG : q ∈ closure (A.arrangementFaceCarrier G))
    (hl : A.arrangementRelativeSign b l (A.arrangementFaceRepresentative F).1 =
      A.arrangementRelativeSign b l (A.arrangementFaceRepresentative G).1) : F = G := by
  apply A.arrangementFaceSignPattern_injective b
  change A.arrangementPointSignPattern b (A.arrangementFaceRepresentative F) =
    A.arrangementPointSignPattern b (A.arrangementFaceRepresentative G)
  rw [A.arrangementPointSignPattern_eq_relativeSign b
    (A.arrangementFaceRepresentative F),
    A.arrangementPointSignPattern_eq_relativeSign b
      (A.arrangementFaceRepresentative G)]
  funext m
  apply Bool.decide_congr
  by_cases hml : m = l
  · subst m
    rw [hl]
  · have hqb : ¬ A.Incident q b := by
      intro hqb
      exact hbl ((hregular b).mp hqb)
    have hqm : ¬ A.Incident q m := by
      intro hqm
      exact hml ((hregular m).mp hqm)
    have hFsign :=
      A.arrangementRelativeSign_arrangementFaceRepresentative_eq_of_mem_closure
        q b m F hqb hqm hF
    have hGsign :=
      A.arrangementRelativeSign_arrangementFaceRepresentative_eq_of_mem_closure
        q b m G hqb hqm hG
    rw [hFsign, hGsign]

/-- The finite set of actual face carriers whose closure contains an ambient
point.  At an edge-interior point this is the local face incidence set. -/
noncomputable def arrangementPointIncidentFaces
    (A : FiniteProjectiveLineArrangement Line) (q : RealProjectivePoint) :
    Finset A.ArrangementFace := by
  classical
  letI : Fintype A.ArrangementFace := A.arrangementFaceFintype
  exact Finset.univ.filter fun F => q ∈ closure (A.arrangementFaceCarrier F)

theorem mem_arrangementPointIncidentFaces_iff
    (A : FiniteProjectiveLineArrangement Line) (q : RealProjectivePoint)
    (F : A.ArrangementFace) :
    F ∈ A.arrangementPointIncidentFaces q ↔
      q ∈ closure (A.arrangementFaceCarrier F) := by
  classical
  simp [arrangementPointIncidentFaces]

/-- The local face-incidence set at every regular point of a non-pencil
arrangement has at most two elements.  It is an injection into the two
possible nonzero signs of the one vanishing covector. -/
theorem card_arrangementPointIncidentFaces_le_two_of_regular
    (A : FiniteProjectiveLineArrangement Line) (hA : A.NonPencil)
    (q : RealProjectivePoint) (l : Line)
    (hregular : ∀ m : Line, A.Incident q m ↔ m = l) :
    (A.arrangementPointIncidentFaces q).card ≤ 2 := by
  classical
  let b : Line := (A.exists_ne_line_of_nonPencil hA l).choose
  have hbl : b ≠ l := (A.exists_ne_line_of_nonPencil hA l).choose_spec
  let f : A.ArrangementFace → Bool := fun F =>
    decide (A.arrangementRelativeSign b l (A.arrangementFaceRepresentative F).1 = 1)
  calc
    (A.arrangementPointIncidentFaces q).card ≤
        (Finset.univ : Finset Bool).card :=
      Finset.card_le_card_of_injOn f
        (by
          intro F hF
          cases h : f F <;> simp [h])
        (by
          intro F hF G hG hfg
          apply A.arrangementFace_eq_of_mem_closure_of_regular_relativeSign_eq
            q l b hregular hbl F G
            ((A.mem_arrangementPointIncidentFaces_iff q F).mp hF)
            ((A.mem_arrangementPointIncidentFaces_iff q G).mp hG)
          apply relativeSign_eq_of_ne_zero_of_decide_eq
          · exact A.arrangementRelativeSign_ne_zero_of_arrangementComplement
              (A.arrangementFaceRepresentative F) b l
          · exact A.arrangementRelativeSign_ne_zero_of_arrangementComplement
              (A.arrangementFaceRepresentative G) b l
          · simpa only [f] using hfg)
    _ = 2 := by decide

/-- The local face-incidence set at a regular point of a non-pencil
arrangement has exactly two elements.  The lower bound is supplied by the
two explicit normal sides, and the upper bound by the transverse-sign
injection proved above. -/
theorem card_arrangementPointIncidentFaces_eq_two_of_regular
    (A : FiniteProjectiveLineArrangement Line) (hA : A.NonPencil)
    (q : RealProjectivePoint) (l : Line)
    (hregular : ∀ m : Line, A.Incident q m ↔ m = l) :
    (A.arrangementPointIncidentFaces q).card = 2 := by
  classical
  letI : Fintype A.ArrangementFace := A.arrangementFaceFintype
  letI : DecidableEq A.ArrangementFace := Classical.decEq _
  apply Nat.le_antisymm
  · exact A.card_arrangementPointIncidentFaces_le_two_of_regular hA q l hregular
  · obtain ⟨Fpos, Fneg, hne, hpos, hneg⟩ :=
      A.exists_two_distinct_arrangementFaces_mem_closure_of_regular hA q l hregular
    have hposMem : Fpos ∈ A.arrangementPointIncidentFaces q :=
      (A.mem_arrangementPointIncidentFaces_iff q Fpos).mpr hpos
    have hnegMem : Fneg ∈ A.arrangementPointIncidentFaces q :=
      (A.mem_arrangementPointIncidentFaces_iff q Fneg).mpr hneg
    calc
      2 = ({Fpos, Fneg} : Finset A.ArrangementFace).card :=
        (Finset.card_pair hne).symm
      _ ≤ (A.arrangementPointIncidentFaces q).card :=
        Finset.card_le_card
          (Finset.insert_subset hposMem (Finset.singleton_subset_iff.mpr hnegMem))

/-! ## Connectedness of a genuine projective cyclic arc

The projective successor has already selected the endpoints of an edge.  To
compare local boundary faces at different interior points, we now prove that
the open cyclic arc between two distinct points of an actual projective line
is path connected.  We do this in the two-dimensional kernel coordinates:
after orienting the terminal representative, the arc is exactly the image of
the convex ray `t > 0` under `P + t • R`.
-/

private theorem realProjectiveBracket_add_smul_right
    (p q r : RealProjectiveLineVector) (t : ℝ) :
    realProjectiveBracket p (q + t • r) =
      realProjectiveBracket p q + t * realProjectiveBracket p r := by
  simp [realProjectiveBracket]
  ring

private theorem realProjectiveBracket_add_smul_left
    (p q r : RealProjectiveLineVector) (t : ℝ) :
    realProjectiveBracket (p + t • q) r =
      realProjectiveBracket p r + t * realProjectiveBracket q r := by
  simp [realProjectiveBracket]
  ring

private theorem realProjectiveTripleBracket_neg_right
    (p q r : RealProjectiveLineVector) :
    realProjectiveTripleBracket p q (-r) =
      realProjectiveTripleBracket p q r := by
  simp [realProjectiveTripleBracket, realProjectiveBracket]
  ring

/-- Cramer's two-dimensional bracket identity.  It is the algebraic inverse
to the positive-ray parametrization of a cyclic arc. -/
private theorem realProjectiveBracket_cramer
    (p q r : RealProjectiveLineVector) :
    realProjectiveBracket q r • p + realProjectiveBracket p q • r =
      realProjectiveBracket p r • q := by
  funext i
  fin_cases i <;> simp [realProjectiveBracket] <;> ring

/-- The open cyclic arc between two distinct incident points of a projective
line is path connected in the quotient topology on `RP²`. -/
theorem isPathConnected_projectiveLineCyclicArc
    (L : RealProjectiveLine) (p r : RealProjectivePoint)
    (hp : p.orthogonal L) (hr : r.orthogonal L) (hpr : p ≠ r) :
    IsPathConnected {q : RealProjectivePoint | ProjectiveLineCyclic L p q r} := by
  classical
  let P : RealProjectiveOnePoint := projectiveLineParameterPreimage L p hp
  let R : RealProjectiveOnePoint := projectiveLineParameterPreimage L r hr
  have hP : projectiveLineParameter L P = p := by
    dsimp [P]
    exact projectiveLineParameter_preimage_spec L p hp
  have hR : projectiveLineParameter L R = r := by
    dsimp [R]
    exact projectiveLineParameter_preimage_spec L r hr
  have hPR : P ≠ R := by
    intro h
    apply hpr
    calc
      p = projectiveLineParameter L P := hP.symm
      _ = projectiveLineParameter L R := by rw [h]
      _ = r := hR
  let d₀ : ℝ := realProjectiveBracket P.rep R.rep
  have hd₀ : d₀ ≠ 0 := by
    intro hzero
    apply hPR
    calc
      P = Projectivization.mk ℝ P.rep P.rep_nonzero :=
        (Projectivization.mk_rep P).symm
      _ = Projectivization.mk ℝ R.rep R.rep_nonzero :=
        (realProjective_mk_eq_mk_iff_bracket_eq_zero
          P.rep_nonzero R.rep_nonzero).mpr hzero
      _ = R := Projectivization.mk_rep R
  let D : RealProjectiveLineVector :=
    if 0 < d₀ then -R.rep else R.rep
  have hDne : D ≠ 0 := by
    dsimp [D]
    split_ifs
    · exact neg_ne_zero.mpr R.rep_nonzero
    · exact R.rep_nonzero
  have hd : realProjectiveBracket P.rep D < 0 := by
    dsimp [D]
    split_ifs with hdpos
    · rw [show realProjectiveBracket P.rep (-R.rep) = -d₀ by
        simp [d₀, realProjectiveBracket]
        ring]
      exact neg_neg_of_pos hdpos
    · exact lt_of_le_of_ne (le_of_not_gt hdpos) hd₀
  have hD : Projectivization.mk ℝ D hDne = R := by
    rw [← Projectivization.mk_rep R]
    apply (Projectivization.mk_eq_mk_iff' ℝ D R.rep hDne R.rep_nonzero).mpr
    dsimp [D]
    split_ifs
    · exact ⟨-1, by simp⟩
    · exact ⟨1, by simp⟩
  let v : ℝ → RealProjectiveLineVector := fun t => P.rep + t • D
  have hvne (t : ℝ) : v t ≠ 0 := by
    by_cases ht : t = 0
    · subst t
      simpa [v] using P.rep_nonzero
    · intro hzero
      have hbracket : realProjectiveBracket P.rep (v t) = 0 := by
        rw [hzero]
        simp [realProjectiveBracket]
      change realProjectiveBracket P.rep (P.rep + t • D) = 0 at hbracket
      rw [realProjectiveBracket_add_smul_right,
        realProjectiveBracket_self, zero_add] at hbracket
      exact (mul_ne_zero ht (ne_of_lt hd)) hbracket
  let γ : ℝ → RealProjectivePoint := fun t =>
    projectiveLineParameter L (Projectivization.mk ℝ (v t) (hvne t))
  have hvContinuous : Continuous v := by
    dsimp [v]
    exact continuous_const.add (continuous_id.smul continuous_const)
  have hMContinuous : Continuous (fun t : ℝ =>
      projectiveLineParameterLinearMap L (v t)) :=
    (projectiveLineParameterLinearMap L).continuous_of_finiteDimensional.comp
      hvContinuous
  have hMne (t : ℝ) : projectiveLineParameterLinearMap L (v t) ≠ 0 := by
    simpa only [map_zero] using
      Function.Injective.ne (projectiveLineParameterLinearMap_injective L) (hvne t)
  have hγContinuous : Continuous γ := by
    have hquotient : Continuous (fun t : ℝ =>
        Projectivization.mk ℝ (projectiveLineParameterLinearMap L (v t)) (hMne t)) := by
      simpa only [Projectivization.mk'_eq_mk] using
        continuous_quotient_mk'.comp (hMContinuous.subtype_mk fun t => hMne t)
    simpa only [γ, projectiveLineParameter, Projectivization.map_mk] using hquotient
  have hγ_mem (t : ℝ) (ht : 0 < t) :
      γ t ∈ {q : RealProjectivePoint | ProjectiveLineCyclic L p q r} := by
    change ProjectiveLineCyclic L p
      (projectiveLineParameter L (Projectivization.mk ℝ (v t) (hvne t))) r
    refine ⟨P, Projectivization.mk ℝ (v t) (hvne t),
      Projectivization.mk ℝ D hDne, hP, rfl, ?_, ?_⟩
    · calc
        projectiveLineParameter L (Projectivization.mk ℝ D hDne) =
            projectiveLineParameter L R := congrArg (projectiveLineParameter L) hD
        _ = r := hR
    · have hpositive : 0 <
          realProjectiveTripleBracket P.rep (v t) D := by
        unfold realProjectiveTripleBracket
        have hfirst : realProjectiveBracket P.rep (v t) =
            t * realProjectiveBracket P.rep D := by
          change realProjectiveBracket P.rep (P.rep + t • D) =
            t * realProjectiveBracket P.rep D
          rw [realProjectiveBracket_add_smul_right,
            realProjectiveBracket_self, zero_add]
        have hsecond : realProjectiveBracket (v t) D =
            realProjectiveBracket P.rep D := by
          change realProjectiveBracket (P.rep + t • D) D =
            realProjectiveBracket P.rep D
          rw [realProjectiveBracket_add_smul_left,
            realProjectiveBracket_self, mul_zero, add_zero]
        rw [hfirst, hsecond, realProjectiveBracket_swap P.rep D]
        exact mul_pos
          (mul_pos_of_neg_of_neg (mul_neg_of_pos_of_neg ht hd) hd)
          (neg_pos.mpr hd)
      simpa only [Projectivization.mk_rep] using
        (realProjectiveCyclic_mk P.rep_nonzero (hvne t) hDne hpositive)
  have himage : γ '' Set.Ioi (0 : ℝ) =
      {q : RealProjectivePoint | ProjectiveLineCyclic L p q r} := by
    ext q
    constructor
    · rintro ⟨t, ht, rfl⟩
      exact hγ_mem t ht
    · intro hq
      rcases hq with ⟨P', Q, R', hP', hQ, hR', hcyclic⟩
      have hP' : P' = P :=
        projectiveLineParameter_injective L (hP'.trans hP.symm)
      have hR' : R' = R :=
        projectiveLineParameter_injective L (hR'.trans hR.symm)
      subst P'
      subst R'
      have htripleR : 0 < realProjectiveTripleBracket P.rep Q.rep R.rep :=
        (realProjectiveCyclic_iff_rep_tripleBracket P Q R).mp hcyclic
      have htripleD : 0 < realProjectiveTripleBracket P.rep Q.rep D := by
        dsimp [D]
        split_ifs
        · rw [realProjectiveTripleBracket_neg_right]
          exact htripleR
        · exact htripleR
      let a : ℝ := realProjectiveBracket P.rep Q.rep
      let b : ℝ := realProjectiveBracket Q.rep D
      let d : ℝ := realProjectiveBracket P.rep D
      have hd' : d < 0 := by simpa only [d] using hd
      have htriple : 0 < a * b * (-d) := by
        change 0 < realProjectiveBracket P.rep Q.rep *
          realProjectiveBracket Q.rep D *
          realProjectiveBracket D P.rep at htripleD
        rw [realProjectiveBracket_swap P.rep D] at htripleD
        simpa only [a, b, d] using htripleD
      have hab : 0 < a * b :=
        (mul_pos_iff_of_pos_right (neg_pos.mpr hd')).mp htriple
      have hb : b ≠ 0 := by
        rcases mul_pos_iff.mp hab with h | h
        · exact ne_of_gt h.2
        · exact ne_of_lt h.2
      have htab : 0 < a / b := by
        rcases mul_pos_iff.mp hab with h | h
        · exact (div_pos_iff).mpr (Or.inl h)
        · exact (div_pos_iff).mpr (Or.inr h)
      have hcramer : b • P.rep + a • D = d • Q.rep := by
        simpa only [a, b, d] using realProjectiveBracket_cramer P.rep Q.rep D
      have hvector : v (a / b) = (d / b) • Q.rep := by
        apply smul_right_injective RealProjectiveLineVector hb
        change b • (P.rep + (a / b) • D) = b • ((d / b) • Q.rep)
        rw [smul_add, smul_smul, smul_smul]
        calc
          b • P.rep + (b * (a / b)) • D = b • P.rep + a • D := by
            rw [show b * (a / b) = a by field_simp [hb]]
          _ = d • Q.rep := hcramer
          _ = (b * (d / b)) • Q.rep := by
            rw [show b * (d / b) = d by field_simp [hb]]
      have hmk : Projectivization.mk ℝ (v (a / b)) (hvne (a / b)) = Q := by
        rw [← Projectivization.mk_rep Q]
        apply (Projectivization.mk_eq_mk_iff' ℝ (v (a / b)) Q.rep
          (hvne (a / b)) Q.rep_nonzero).mpr
        exact ⟨d / b, hvector.symm⟩
      refine ⟨a / b, htab, ?_⟩
      change γ (a / b) = q
      calc
        γ (a / b) = projectiveLineParameter L
            (Projectivization.mk ℝ (v (a / b)) (hvne (a / b))) := rfl
        _ = projectiveLineParameter L Q :=
          congrArg (projectiveLineParameter L) hmk
        _ = q := hQ
  rw [← himage]
  exact ((convex_Ioi (0 : ℝ)).isPathConnected
    ⟨1, by simpa only [Set.mem_Ioi] using zero_lt_one⟩).image hγContinuous

/-- Every geometric open edge of a non-pencil arrangement is a nonempty,
path-connected genuine cyclic arc.  Non-pencilness is used only to rule out
the one-marked-vertex successor loop. -/
theorem isPathConnected_geometricEdgeOpenArc
    (A : FiniteProjectiveLineArrangement Line) (hA : A.NonPencil)
    (e : A.GeometricEdge) :
    IsPathConnected (A.geometricEdgeOpenArc e) := by
  exact isPathConnected_projectiveLineCyclicArc
    (A.projectiveLine (A.edgeSlotLine e))
    (A.geometricEdgeInitial e) (A.geometricEdgeTerminal e)
    (A.geometricEdge_initial_incident e)
    (A.geometricEdge_endpoint_incident e)
    (A.geometricEdge_initial_ne_terminal_of_nonPencil hA e)

/-- Every transverse intrinsic relative sign is constant along a genuine
open geometric edge.  This is the bridge from the cyclic successor to
global complement-face information. -/
theorem arrangementRelativeSign_eq_of_mem_geometricEdgeOpenArc
    (A : FiniteProjectiveLineArrangement Line) (hA : A.NonPencil)
    (e : A.GeometricEdge) (base m : Line)
    (hbase : base ≠ A.edgeSlotLine e) (hm : m ≠ A.edgeSlotLine e)
    {q q' : RealProjectivePoint}
    (hq : q ∈ A.geometricEdgeOpenArc e)
    (hq' : q' ∈ A.geometricEdgeOpenArc e) :
    A.arrangementRelativeSign base m q =
      A.arrangementRelativeSign base m q' := by
  have hcontinuous : ContinuousOn (A.arrangementRelativeSign base m)
      (A.geometricEdgeOpenArc e) :=
    (A.continuousOn_arrangementRelativeSign_relativeSignDomain base m).mono
      (by
        intro x hx
        constructor
        · intro hincident
          exact hbase
            ((A.geometricEdgeOpenArc_incident_iff e hx base).mp hincident)
        · intro hincident
          exact hm
            ((A.geometricEdgeOpenArc_incident_iff e hx m).mp hincident))
  exact ((A.isPathConnected_geometricEdgeOpenArc hA e).isConnected.isPreconnected).constant
    hcontinuous hq hq'

/-- Of the two nonzero signs, a third nonzero sign agrees with one of two
distinct ones.  This finite observation lets a boundary face be transported
across an entire cyclic edge without choosing an orientation of its sides. -/
private theorem sign_eq_left_or_right_of_ne_zero_of_ne
    (s a c : SignType) (hs : s ≠ 0) (ha : a ≠ 0) (hc : c ≠ 0)
    (hac : a ≠ c) : s = a ∨ s = c := by
  cases hs' : s <;> cases ha' : a <;> cases hc' : c <;> simp_all

/-- If the closure of a genuine face meets one interior point of a geometric
edge, it meets every interior point of that same edge.  The proof compares
the finite face sign words: transverse coordinates are constant on the arc,
and the remaining coordinate has exactly its two possible nonzero values. -/
theorem mem_closure_arrangementFaceCarrier_of_mem_closure_of_geometricEdgeOpenArc
    (A : FiniteProjectiveLineArrangement Line) (hA : A.NonPencil)
    (e : A.GeometricEdge) {q q' : RealProjectivePoint}
    (hq : q ∈ A.geometricEdgeOpenArc e)
    (hq' : q' ∈ A.geometricEdgeOpenArc e) (F : A.ArrangementFace)
    (hF : q ∈ closure (A.arrangementFaceCarrier F)) :
    q' ∈ closure (A.arrangementFaceCarrier F) := by
  classical
  let l : Line := A.edgeSlotLine e
  let b : Line := (A.exists_ne_line_of_nonPencil hA l).choose
  have hbl : b ≠ l := (A.exists_ne_line_of_nonPencil hA l).choose_spec
  have hregular : ∀ m : Line, A.Incident q m ↔ m = l := by
    intro m
    simpa only [l] using A.geometricEdgeOpenArc_incident_iff e hq m
  have hregular' : ∀ m : Line, A.Incident q' m ↔ m = l := by
    intro m
    simpa only [l] using A.geometricEdgeOpenArc_incident_iff e hq' m
  obtain ⟨Fpos, Fneg, hne, hpos, hneg⟩ :=
    A.exists_two_distinct_arrangementFaces_mem_closure_of_regular hA q' l hregular'
  have hs : A.arrangementRelativeSign b l
      (A.arrangementFaceRepresentative F).1 ≠ 0 :=
    A.arrangementRelativeSign_ne_zero_of_arrangementComplement
      (A.arrangementFaceRepresentative F) b l
  have hposSign : A.arrangementRelativeSign b l
      (A.arrangementFaceRepresentative Fpos).1 ≠ 0 :=
    A.arrangementRelativeSign_ne_zero_of_arrangementComplement
      (A.arrangementFaceRepresentative Fpos) b l
  have hnegSign : A.arrangementRelativeSign b l
      (A.arrangementFaceRepresentative Fneg).1 ≠ 0 :=
    A.arrangementRelativeSign_ne_zero_of_arrangementComplement
      (A.arrangementFaceRepresentative Fneg) b l
  have hposNegSign : A.arrangementRelativeSign b l
      (A.arrangementFaceRepresentative Fpos).1 ≠
      A.arrangementRelativeSign b l
        (A.arrangementFaceRepresentative Fneg).1 := by
    intro hsign
    apply hne
    exact A.arrangementFace_eq_of_mem_closure_of_regular_relativeSign_eq
      q' l b hregular' hbl Fpos Fneg hpos hneg hsign
  have face_eq_of_sign : ∀ (G : A.ArrangementFace),
      q' ∈ closure (A.arrangementFaceCarrier G) →
      A.arrangementRelativeSign b l (A.arrangementFaceRepresentative F).1 =
        A.arrangementRelativeSign b l (A.arrangementFaceRepresentative G).1 →
      F = G := by
    intro G hG hsign
    apply A.arrangementFaceSignPattern_injective b
    change A.arrangementPointSignPattern b (A.arrangementFaceRepresentative F) =
      A.arrangementPointSignPattern b (A.arrangementFaceRepresentative G)
    rw [A.arrangementPointSignPattern_eq_relativeSign b
      (A.arrangementFaceRepresentative F),
      A.arrangementPointSignPattern_eq_relativeSign b
        (A.arrangementFaceRepresentative G)]
    funext m
    apply Bool.decide_congr
    by_cases hml : m = l
    · subst m
      rw [hsign]
    · have hqb : ¬ A.Incident q b := by
        intro hincident
        exact hbl ((hregular b).mp hincident)
      have hqm : ¬ A.Incident q m := by
        intro hincident
        exact hml ((hregular m).mp hincident)
      have hqb' : ¬ A.Incident q' b := by
        intro hincident
        exact hbl ((hregular' b).mp hincident)
      have hqm' : ¬ A.Incident q' m := by
        intro hincident
        exact hml ((hregular' m).mp hincident)
      have hFsign :=
        A.arrangementRelativeSign_arrangementFaceRepresentative_eq_of_mem_closure
          q b m F hqb hqm hF
      have hGsign :=
        A.arrangementRelativeSign_arrangementFaceRepresentative_eq_of_mem_closure
          q' b m G hqb' hqm' hG
      have harc := A.arrangementRelativeSign_eq_of_mem_geometricEdgeOpenArc
        hA e b m (by simpa only [l] using hbl) (by simpa only [l] using hml) hq hq'
      rw [hFsign, hGsign, harc]
  rcases sign_eq_left_or_right_of_ne_zero_of_ne
      (A.arrangementRelativeSign b l (A.arrangementFaceRepresentative F).1)
      (A.arrangementRelativeSign b l (A.arrangementFaceRepresentative Fpos).1)
      (A.arrangementRelativeSign b l (A.arrangementFaceRepresentative Fneg).1)
      hs hposSign hnegSign hposNegSign with hchoice | hchoice
  · rw [face_eq_of_sign Fpos hpos hchoice]
    exact hpos
  · rw [face_eq_of_sign Fneg hneg hchoice]
    exact hneg

/-- Ambient closure incidence of a face is independent of the chosen
interior point of a geometric edge. -/
theorem geometricEdgeIncidentFaces_eq_arrangementPointIncidentFaces
    (A : FiniteProjectiveLineArrangement Line) (hA : A.NonPencil)
    (e : A.GeometricEdge) {q : RealProjectivePoint}
    (hq : q ∈ A.geometricEdgeOpenArc e) :
    A.geometricEdgeIncidentFaces e = A.arrangementPointIncidentFaces q := by
  classical
  ext F
  rw [A.mem_geometricEdgeIncidentFaces_iff,
    A.mem_arrangementPointIncidentFaces_iff]
  constructor
  · rintro ⟨q', hq', hF⟩
    exact A.mem_closure_arrangementFaceCarrier_of_mem_closure_of_geometricEdgeOpenArc
      hA e hq' hq F hF
  · intro hF
    exact ⟨q, hq, hF⟩

/-- Every genuine non-pencil geometric edge has exactly two actual complement
faces in its ambient boundary. -/
theorem card_geometricEdgeIncidentFaces_eq_two
    (A : FiniteProjectiveLineArrangement Line) (hA : A.NonPencil)
    (e : A.GeometricEdge) {q : RealProjectivePoint}
    (hq : q ∈ A.geometricEdgeOpenArc e) :
    (A.geometricEdgeIncidentFaces e).card = 2 := by
  rw [A.geometricEdgeIncidentFaces_eq_arrangementPointIncidentFaces hA e hq]
  exact A.card_arrangementPointIncidentFaces_eq_two_of_regular hA q
    (A.edgeSlotLine e) (fun m => A.geometricEdgeOpenArc_incident_iff e hq m)

/-- The finite enumeration of actual complement components used by the
global boundary double count below. -/
noncomputable local instance arrangementFaceFintypeForHandshake
    (A : FiniteProjectiveLineArrangement Line) : Fintype A.ArrangementFace :=
  A.arrangementFaceFintype

noncomputable local instance arrangementFaceDecidableEqForHandshake
    (A : FiniteProjectiveLineArrangement Line) : DecidableEq A.ArrangementFace :=
  Classical.decEq _

noncomputable local instance geometricEdgeDecidableEqForHandshake
    (A : FiniteProjectiveLineArrangement Line) : DecidableEq A.GeometricEdge :=
  Classical.decEq _

/-- The actual boundary predicate has exactly two faces at every genuine
geometric edge.  This is the `edgeHasTwoFaces` field of the finite
cellulation interface, now proved from ambient closures rather than assumed. -/
theorem edgeHasTwoFaces_arrangementFaceBoundary
    (A : FiniteProjectiveLineArrangement Line) (hA : A.NonPencil)
    (e : A.GeometricEdge) :
    (Finset.univ.filter fun F : A.ArrangementFace =>
      e ∈ A.arrangementFaceBoundary F).card = 2 := by
  classical
  obtain ⟨q, hq⟩ := (A.isPathConnected_geometricEdgeOpenArc hA e).nonempty
  have hsets : (Finset.univ.filter fun F : A.ArrangementFace =>
      e ∈ A.arrangementFaceBoundary F) = A.geometricEdgeIncidentFaces e := by
    ext F
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      A.mem_arrangementFaceBoundary_iff,
      A.mem_geometricEdgeIncidentFaces_iff]
  rw [hsets]
  exact A.card_geometricEdgeIncidentFaces_eq_two hA e hq

/-- Double-counting the actual closure incidences gives the exact global
face--edge handshake.  No cellulation certificate is used here: both sides
are the concrete finite boundary sets defined above. -/
theorem sum_arrangementFaceBoundary_card_eq_two_mul_card_geometricEdge
    (A : FiniteProjectiveLineArrangement Line) (hA : A.NonPencil) :
    (∑ F : A.ArrangementFace, (A.arrangementFaceBoundary F).card) =
      2 * Fintype.card A.GeometricEdge := by
  classical
  calc
    (∑ F : A.ArrangementFace, (A.arrangementFaceBoundary F).card) =
        ∑ F : A.ArrangementFace, ∑ e : A.GeometricEdge,
          if e ∈ A.arrangementFaceBoundary F then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro F hF
      simp
    _ = ∑ e : A.GeometricEdge, ∑ F : A.ArrangementFace,
        if e ∈ A.arrangementFaceBoundary F then 1 else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ _e : A.GeometricEdge, 2 := by
      apply Finset.sum_congr rfl
      intro e he
      simpa using A.edgeHasTwoFaces_arrangementFaceBoundary hA e
    _ = 2 * Fintype.card A.GeometricEdge := by simp [mul_comm]

end FiniteProjectiveLineArrangement

end Erdos506.Incidence
