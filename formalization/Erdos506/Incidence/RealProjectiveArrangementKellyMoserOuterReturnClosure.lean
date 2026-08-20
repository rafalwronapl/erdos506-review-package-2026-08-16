import Erdos506.Incidence.RealProjectiveArrangementKellyMoserOuterSector

/-!
# Return closure for the two Kelly--Moser outer sectors

This leaf keeps the literal three boundary edges of an ordinary attachment.
Flipping one side sign gives the adjacent outer sector.  A line through an
off-base vertex of that sector cannot return through the old base sector:
otherwise it creates an extra vertex in the clean side of the original
triangular face.
-/

namespace Erdos506.Incidence

open scoped LinearAlgebra.Projectivization

namespace FiniteProjectiveLineArrangement

variable {Line : Type*} [Fintype Line] [DecidableEq Line]

noncomputable local instance realProjectivePointTopologicalSpaceForKellyMoserOuterReturnClosure :
    TopologicalSpace RealProjectivePoint :=
  realProjectivePointQuotientTopology

noncomputable local instance realProjectivePointDecidableEqForKellyMoserOuterReturnClosure :
    DecidableEq RealProjectivePoint :=
  Classical.decEq _

noncomputable local instance geometricEdgeDecidableEqForKellyMoserOuterReturnClosure
    (A : FiniteProjectiveLineArrangement Line) : DecidableEq A.GeometricEdge :=
  A.geometricEdgeDecidableEqForOrdinaryEdgeTriangle

noncomputable local instance incidentDecidableForKellyMoserOuterReturnClosure
    (A : FiniteProjectiveLineArrangement Line)
    (p : RealProjectivePoint) (l : Line) : Decidable (A.Incident p l) :=
  Classical.propDecidable _

/-- Flip exactly one oriented half-space. -/
def flipSignAt (sigma : Line → Bool) (side : Line) : Line → Bool :=
  fun k => if k = side then !(sigma k) else sigma k

@[simp]
theorem arrangementOrientedEvaluation_flipSignAt_self
    (A : FiniteProjectiveLineArrangement Line) (sigma : Line → Bool)
    (side : Line) :
    A.arrangementOrientedEvaluation (flipSignAt sigma side) side =
      -A.arrangementOrientedEvaluation sigma side := by
  by_cases hs : sigma side <;>
    simp [flipSignAt, arrangementOrientedEvaluation, hs]

theorem arrangementOrientedEvaluation_flipSignAt_of_ne
    (A : FiniteProjectiveLineArrangement Line) (sigma : Line → Bool)
    {side k : Line} (hks : k ≠ side) :
    A.arrangementOrientedEvaluation (flipSignAt sigma side) k =
      A.arrangementOrientedEvaluation sigma k := by
  unfold arrangementOrientedEvaluation flipSignAt
  simp only [hks, if_false]

@[simp]
theorem arrangementOrientedEvaluation_flipSignAt_self_apply
    (A : FiniteProjectiveLineArrangement Line) (sigma : Line → Bool)
    (side : Line) (v : Homogeneous3) :
    A.arrangementOrientedEvaluation (flipSignAt sigma side) side v =
      -A.arrangementOrientedEvaluation sigma side v := by
  rw [A.arrangementOrientedEvaluation_flipSignAt_self]
  rfl

theorem arrangementOrientedEvaluation_flipSignAt_of_ne_apply
    (A : FiniteProjectiveLineArrangement Line) (sigma : Line → Bool)
    {side k : Line} (hks : k ≠ side) (v : Homogeneous3) :
    A.arrangementOrientedEvaluation (flipSignAt sigma side) k v =
      A.arrangementOrientedEvaluation sigma k v := by
  rw [A.arrangementOrientedEvaluation_flipSignAt_of_ne sigma hks]

/-- Every vertex of the base and the left side belongs to every closed
sector cut out by the same three projective lines. -/
theorem projectivePointMemTriangleSector_of_incident_base_left
    (A : FiniteProjectiveLineArrangement Line) (sigma : Line → Bool)
    (l a b : Line) (q : RealProjectivePoint)
    (hql : A.Incident q l) (hqa : A.Incident q a) :
    A.projectivePointMemTriangleSector sigma l a b q := by
  have hl0 : A.arrangementOrientedEvaluation sigma l q.rep = 0 := by
    apply (A.incident_projectivization_mk_iff_orientedEvaluation_eq_zero
      sigma l q.rep q.rep_nonzero).1
    simpa only [Projectivization.mk_rep] using hql
  have ha0 : A.arrangementOrientedEvaluation sigma a q.rep = 0 := by
    apply (A.incident_projectivization_mk_iff_orientedEvaluation_eq_zero
      sigma a q.rep q.rep_nonzero).1
    simpa only [Projectivization.mk_rep] using hqa
  by_cases hb : 0 ≤ A.arrangementOrientedEvaluation sigma b q.rep
  · left
    intro k hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hk
    rcases hk with rfl | rfl | rfl
    · exact hl0.symm.le
    · exact ha0.symm.le
    · exact hb
  · right
    intro k hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hk
    rcases hk with rfl | rfl | rfl
    · rw [LinearMap.map_neg, hl0, neg_zero]
    · rw [LinearMap.map_neg, ha0, neg_zero]
    · rw [LinearMap.map_neg]
      exact neg_nonneg.mpr (le_of_not_ge hb)

/-- Symmetric base/right vertex form. -/
theorem projectivePointMemTriangleSector_of_incident_base_right
    (A : FiniteProjectiveLineArrangement Line) (sigma : Line → Bool)
    (l a b : Line) (q : RealProjectivePoint)
    (hql : A.Incident q l) (hqb : A.Incident q b) :
    A.projectivePointMemTriangleSector sigma l a b q := by
  have h := A.projectivePointMemTriangleSector_of_incident_base_left
    sigma l b a q hql hqb
  unfold projectivePointMemTriangleSector at h ⊢
  have hset : ({l, b, a} : Finset Line) = {l, a, b} := by
    ext k
    simp [or_comm, or_left_comm, or_assoc]
  simpa only [hset] using h

/-- On the base of a nonconcurrent triangle, the complement of the sector
obtained by flipping `b` is the original sector. -/
theorem projectivePointMemTriangleSector_of_incident_base_of_not_flip_right
    (A : FiniteProjectiveLineArrangement Line) (sigma : Line → Bool)
    (l a b : Line) (hbl : b ≠ l) (hab : a ≠ b)
    (q : RealProjectivePoint) (hql : A.Incident q l)
    (hout : ¬ A.projectivePointMemTriangleSector
      (flipSignAt sigma b) l a b q) :
    A.projectivePointMemTriangleSector sigma l a b q := by
  have hl0 : A.arrangementOrientedEvaluation sigma l q.rep = 0 := by
    apply (A.incident_projectivization_mk_iff_orientedEvaluation_eq_zero
      sigma l q.rep q.rep_nonzero).1
    simpa only [Projectivization.mk_rep] using hql
  by_cases ha : 0 ≤ A.arrangementOrientedEvaluation sigma a q.rep
  · have hb : 0 ≤ A.arrangementOrientedEvaluation sigma b q.rep := by
      by_contra hb
      apply hout
      left
      intro k hk
      simp only [Finset.mem_insert, Finset.mem_singleton] at hk
      rcases hk with rfl | rfl | rfl
      · rw [A.arrangementOrientedEvaluation_flipSignAt_of_ne_apply
          sigma hbl.symm]
        exact hl0.symm.le
      · rw [A.arrangementOrientedEvaluation_flipSignAt_of_ne_apply
          sigma hab]
        exact ha
      · rw [A.arrangementOrientedEvaluation_flipSignAt_self_apply]
        exact neg_nonneg.mpr (le_of_not_ge hb)
    exact Or.inl (by
      intro k hk
      simp only [Finset.mem_insert, Finset.mem_singleton] at hk
      rcases hk with rfl | rfl | rfl
      · exact hl0.symm.le
      · exact ha
      · exact hb)
  · have hb : A.arrangementOrientedEvaluation sigma b q.rep ≤ 0 := by
      by_contra hb
      have hbpos : 0 < A.arrangementOrientedEvaluation sigma b q.rep :=
        lt_of_not_ge hb
      apply hout
      right
      intro k hk
      simp only [Finset.mem_insert, Finset.mem_singleton] at hk
      rcases hk with rfl | rfl | rfl
      · rw [LinearMap.map_neg,
          A.arrangementOrientedEvaluation_flipSignAt_of_ne_apply
            sigma hbl.symm, hl0, neg_zero]
      · rw [LinearMap.map_neg,
          A.arrangementOrientedEvaluation_flipSignAt_of_ne_apply
            sigma hab]
        exact neg_nonneg.mpr (le_of_not_ge ha)
      · rw [LinearMap.map_neg,
          A.arrangementOrientedEvaluation_flipSignAt_self_apply]
        simpa only [neg_neg] using hbpos.le
    exact Or.inr (by
      intro k hk
      simp only [Finset.mem_insert, Finset.mem_singleton] at hk
      rcases hk with rfl | rfl | rfl
      · rw [LinearMap.map_neg, hl0, neg_zero]
      · rw [LinearMap.map_neg]
        exact neg_nonneg.mpr (le_of_not_ge ha)
      · rw [LinearMap.map_neg]
        exact neg_nonneg.mpr hb)

/-- The lossless literal boundary data hidden behind an attachment witness. -/
structure OrdinaryAttachmentExactTriangleFrame
    (A : FiniteProjectiveLineArrangement Line)
    (q : A.OrdinaryVertex) (l : Line)
    (w : OrdinaryAttachmentWitness A q l) where
  a : Line
  b : Line
  edgeA : A.GeometricEdge
  edgeB : A.GeometricEdge
  a_ne_b : a ≠ b
  a_ne_base : a ≠ l
  b_ne_base : b ≠ l
  q_on_a : A.Incident q.1 a
  q_on_b : A.Incident q.1 b
  edgeA_line : A.edgeSlotLine edgeA = a
  edgeB_line : A.edgeSlotLine edgeB = b
  boundary : A.arrangementFaceBoundary w.face = {w.base, edgeA, edgeB}

/-- Every literal attachment exposes its two actual clean side edges. -/
theorem OrdinaryAttachmentWitness.exists_exactTriangleFrame
    (A : FiniteProjectiveLineArrangement Line) (hA : A.NonPencil)
    {q : A.OrdinaryVertex} {l : Line}
    (w : OrdinaryAttachmentWitness A q l) :
    Nonempty (OrdinaryAttachmentExactTriangleFrame A q l w) := by
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
  exact ⟨{
    a := a
    b := b
    edgeA := edgeA
    edgeB := edgeB
    a_ne_b := hab
    a_ne_base := hal
    b_ne_base := hbl
    q_on_a := hqa
    q_on_b := hqb
    edgeA_line := hedgeALine
    edgeB_line := hedgeBLine
    boundary := hboundary
  }⟩

/-- Exchange the two literal side edges. -/
def OrdinaryAttachmentExactTriangleFrame.swap
    {A : FiniteProjectiveLineArrangement Line}
    {q : A.OrdinaryVertex} {l : Line}
    {w : OrdinaryAttachmentWitness A q l}
    (T : OrdinaryAttachmentExactTriangleFrame A q l w) :
    OrdinaryAttachmentExactTriangleFrame A q l w where
  a := T.b
  b := T.a
  edgeA := T.edgeB
  edgeB := T.edgeA
  a_ne_b := T.a_ne_b.symm
  a_ne_base := T.b_ne_base
  b_ne_base := T.a_ne_base
  q_on_a := T.q_on_b
  q_on_b := T.q_on_a
  edgeA_line := T.edgeB_line
  edgeB_line := T.edgeA_line
  boundary := by
    rw [T.boundary]
    ext e
    simp [or_comm, or_left_comm, or_assoc]

/-- One-side return closure.  The side `b` is the literal clean side and
the outer chamber is obtained by flipping only its face sign. -/
theorem OrdinaryAttachmentExactTriangleFrame.return_mem_flip_right
    (A : FiniteProjectiveLineArrangement Line) (hA : A.NonPencil)
    {q : A.OrdinaryVertex} {l : Line}
    {w : OrdinaryAttachmentWitness A q l}
    (T : OrdinaryAttachmentExactTriangleFrame A q l w)
    (x : RealProjectivePoint) (hxVertex : x ∈ A.vertexSet)
    (hxOuter : A.projectivePointMemTriangleSector
      (flipSignAt (A.arrangementFaceSignPattern l w.face) T.b)
        l T.a T.b x)
    (hxl : ¬ A.Incident x l)
    (c : Line) (hxc : A.Incident x c) (hlc : l ≠ c) :
    A.projectivePointMemTriangleSector
      (flipSignAt (A.arrangementFaceSignPattern l w.face) T.b)
        l T.a T.b (A.intersection l c) := by
  classical
  let sigma := A.arrangementFaceSignPattern l w.face
  let outerSigma := flipSignAt sigma T.b
  change A.projectivePointMemTriangleSector outerSigma l T.a T.b
    (A.intersection l c)
  change A.projectivePointMemTriangleSector outerSigma l T.a T.b x at hxOuter
  by_contra hout
  let r := A.intersection l c
  have hrl : A.Incident r l := by
    exact A.intersection_incident_left hlc
  have hrc : A.Incident r c := by
    exact A.intersection_incident_right hlc
  have hrFace : A.projectivePointMemTriangleSector sigma l T.a T.b r :=
    A.projectivePointMemTriangleSector_of_incident_base_of_not_flip_right
      sigma l T.a T.b T.b_ne_base T.a_ne_b r hrl hout
  have hra : ¬ A.Incident r T.a := by
    intro hra
    apply hout
    exact A.projectivePointMemTriangleSector_of_incident_base_left
      outerSigma l T.a T.b r hrl hra
  have hrb : ¬ A.Incident r T.b := by
    intro hrb
    apply hout
    exact A.projectivePointMemTriangleSector_of_incident_base_right
      outerSigma l T.a T.b r hrl hrb
  have htriangle : ¬ ∃ z : RealProjectivePoint,
      A.Incident z l ∧ A.Incident z T.a ∧ A.Incident z T.b :=
    A.not_three_concurrent_of_offBase_apex q.1 l T.a T.b T.a_ne_b
      T.q_on_a T.q_on_b w.away
  let X := A.sectorExitNormalizedPoint outerSigma l T.a T.b x
  let R := A.sectorExitNormalizedPoint sigma l T.a T.b r
  obtain ⟨hX0, _hXgauge, hmkX, hXcone⟩ :=
    A.sectorExitNormalizedPoint_facts
      outerSigma l T.a T.b htriangle x hxOuter
  obtain ⟨hR0, _hRgauge, hmkR, hRcone⟩ :=
    A.sectorExitNormalizedPoint_facts
      sigma l T.a T.b htriangle r hrFace
  have hcone : A.arrangementClosedSignConeOn sigma {l, T.a, T.b} =
      A.arrangementClosedSignCone sigma := by
    simpa only [sigma] using
      A.arrangementClosedSignConeOn_eq_of_exact_triangle_boundary
        hA l w.face w.base T.edgeA T.edgeB l T.a T.b T.boundary
          w.base_line T.edgeA_line T.edgeB_line
          T.a_ne_base T.b_ne_base T.a_ne_b
  have hRl : A.arrangementOrientedEvaluation sigma l R = 0 := by
    exact A.arrangementOrientedEvaluation_sectorExitNormalizedPoint_eq_zero
      sigma l T.a T.b l htriangle r hrFace hrl
  have hRaNonneg : 0 ≤ A.arrangementOrientedEvaluation sigma T.a R :=
    hRcone T.a (by simp)
  have hRbNonneg : 0 ≤ A.arrangementOrientedEvaluation sigma T.b R :=
    hRcone T.b (by simp)
  have hRaNe : A.arrangementOrientedEvaluation sigma T.a R ≠ 0 := by
    intro hzero
    apply hra
    rw [← hmkR]
    exact (A.incident_projectivization_mk_iff_orientedEvaluation_eq_zero
      sigma T.a R hR0).2 hzero
  have hRbNe : A.arrangementOrientedEvaluation sigma T.b R ≠ 0 := by
    intro hzero
    apply hrb
    rw [← hmkR]
    exact (A.incident_projectivization_mk_iff_orientedEvaluation_eq_zero
      sigma T.b R hR0).2 hzero
  have hRaPos : 0 < A.arrangementOrientedEvaluation sigma T.a R :=
    lt_of_le_of_ne hRaNonneg hRaNe.symm
  have hRbPos : 0 < A.arrangementOrientedEvaluation sigma T.b R :=
    lt_of_le_of_ne hRbNonneg hRbNe.symm
  have hXlNonneg :
      0 ≤ A.arrangementOrientedEvaluation outerSigma l X :=
    hXcone l (by simp)
  have hXlNe : A.arrangementOrientedEvaluation outerSigma l X ≠ 0 := by
    intro hzero
    apply hxl
    rw [← hmkX]
    exact (A.incident_projectivization_mk_iff_orientedEvaluation_eq_zero
      outerSigma l X hX0).2 hzero
  have hXlPos : 0 < A.arrangementOrientedEvaluation sigma l X := by
    have hpos : 0 < A.arrangementOrientedEvaluation outerSigma l X :=
      lt_of_le_of_ne hXlNonneg hXlNe.symm
    simpa only [outerSigma,
      A.arrangementOrientedEvaluation_flipSignAt_of_ne_apply
        sigma T.b_ne_base.symm] using hpos
  have hXaNonneg : 0 ≤ A.arrangementOrientedEvaluation sigma T.a X := by
    have h := hXcone T.a (by simp)
    simpa only [outerSigma,
      A.arrangementOrientedEvaluation_flipSignAt_of_ne_apply
        sigma T.a_ne_b] using h
  have hcb : c ≠ T.b := by
    intro h
    apply hout
    subst c
    exact A.projectivePointMemTriangleSector_of_incident_base_right
      outerSigma l T.a T.b r hrl hrc
  have hXbNe :
      A.arrangementOrientedEvaluation outerSigma T.b X ≠ 0 := by
    intro hzero
    have hxb : A.Incident x T.b := by
      rw [← hmkX]
      exact (A.incident_projectivization_mk_iff_orientedEvaluation_eq_zero
        outerSigma T.b X hX0).2 hzero
    have hXbFace : A.arrangementOrientedEvaluation sigma T.b X = 0 := by
      simpa only [outerSigma,
        A.arrangementOrientedEvaluation_flipSignAt_self_apply,
        neg_eq_zero] using hzero
    have hXFaceCone : X ∈
        A.arrangementClosedSignConeOn sigma {l, T.a, T.b} := by
      intro k hk
      simp only [Finset.mem_insert, Finset.mem_singleton] at hk
      rcases hk with rfl | rfl | rfl
      · exact hXlPos.le
      · exact hXaNonneg
      · exact hXbFace.symm.le
    have hXFull : X ∈ A.arrangementClosedSignCone sigma := by
      rw [← hcone]
      exact hXFaceCone
    have hxClosure : x ∈ closure (A.arrangementFaceCarrier w.face) := by
      have h :=
        A.projectivization_mem_closure_arrangementFaceCarrier_of_mem_closedSignCone
          l w.face hX0 hXFull
      simpa only [hmkX] using h
    have hboundary' : A.arrangementFaceBoundary w.face =
        {T.edgeB, w.base, T.edgeA} := by
      rw [T.boundary]
      ext e
      simp [or_comm, or_left_comm, or_assoc]
    have hxa : A.Incident x T.a :=
      A.incident_third_support_of_vertex_mem_closure_exact_triangle
        hA w.face T.edgeB w.base T.edgeA T.b l T.a x hboundary'
          T.edgeB_line w.base_line T.edgeA_line
          T.b_ne_base.symm T.a_ne_b T.a_ne_base.symm
          hxVertex hxClosure hxb hxl
    have hxq : x = q.1 := by
      calc
        x = A.intersection T.a T.b :=
          A.eq_intersection_of_incident T.a_ne_b hxa hxb
        _ = q.1 :=
          (A.eq_intersection_of_incident T.a_ne_b
            T.q_on_a T.q_on_b).symm
    have hqc : A.Incident q.1 c := by
      rw [← hxq]
      exact hxc
    have hqTwo : A.multiplicity q.1 = 2 :=
      (Finset.mem_filter.mp q.2).2
    have hexact := A.incident_iff_eq_or_eq_of_multiplicity_eq_two
      q.1 T.a T.b T.q_on_a T.q_on_b T.a_ne_b.symm hqTwo c
    rcases hexact.mp hqc with hc | hc
    · apply hout
      subst c
      exact A.projectivePointMemTriangleSector_of_incident_base_left
        outerSigma l T.a T.b r hrl hrc
    · exact hcb hc
  have hXbPos :
      0 < A.arrangementOrientedEvaluation outerSigma T.b X :=
    lt_of_le_of_ne (hXcone T.b (by simp)) hXbNe.symm
  have hXbNeg : A.arrangementOrientedEvaluation sigma T.b X < 0 := by
    have h := hXbPos
    simpa only [outerSigma,
      A.arrangementOrientedEvaluation_flipSignAt_self_apply,
      neg_pos] using h
  have hXd : A.arrangementOrientedEvaluation sigma c X = 0 := by
    have h :=
      A.arrangementOrientedEvaluation_sectorExitNormalizedPoint_eq_zero
        outerSigma l T.a T.b c htriangle x hxOuter hxc
    simpa only [outerSigma,
      A.arrangementOrientedEvaluation_flipSignAt_of_ne_apply sigma hcb]
      using h
  have hRd : A.arrangementOrientedEvaluation sigma c R = 0 :=
    A.arrangementOrientedEvaluation_sectorExitNormalizedPoint_eq_zero
      sigma l T.a T.b c htriangle r hrFace hrc
  obtain ⟨h, hh0, hh1, hbzero⟩ :=
    exists_strict_barycentric_zero_of_mul_neg
      (mul_neg_of_neg_of_pos hXbNeg hRbPos)
  let Y : Homogeneous3 := (1 - h) • X + h • R
  have hYb : A.arrangementOrientedEvaluation sigma T.b Y = 0 := by
    simpa only [Y, LinearMap.map_add, LinearMap.map_smul, smul_eq_mul]
      using hbzero
  have hYd : A.arrangementOrientedEvaluation sigma c Y = 0 := by
    simp only [Y, LinearMap.map_add, LinearMap.map_smul, smul_eq_mul,
      hXd, hRd, mul_zero, add_zero]
  have hYl : 0 < A.arrangementOrientedEvaluation sigma l Y := by
    simp only [Y, LinearMap.map_add, LinearMap.map_smul, smul_eq_mul,
      hRl, mul_zero, add_zero]
    exact mul_pos (sub_pos.mpr hh1) hXlPos
  have hYa : 0 < A.arrangementOrientedEvaluation sigma T.a Y := by
    simp only [Y, LinearMap.map_add, LinearMap.map_smul, smul_eq_mul]
    exact add_pos_of_nonneg_of_pos
      (mul_nonneg (sub_nonneg.mpr hh1.le) hXaNonneg)
      (mul_pos hh0 hRaPos)
  have hY0 : Y ≠ 0 := by
    intro hzero
    rw [hzero, LinearMap.map_zero] at hYl
    exact (lt_irrefl 0 hYl)
  have hYFaceCone : Y ∈
      A.arrangementClosedSignConeOn sigma {l, T.a, T.b} := by
    intro k hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hk
    rcases hk with rfl | rfl | rfl
    · exact hYl.le
    · exact hYa.le
    · exact hYb.symm.le
  have hYFull : Y ∈ A.arrangementClosedSignCone sigma := by
    rw [← hcone]
    exact hYFaceCone
  let y : RealProjectivePoint := Projectivization.mk ℝ Y hY0
  have hyClosure : y ∈ closure (A.arrangementFaceCarrier w.face) := by
    exact A.projectivization_mem_closure_arrangementFaceCarrier_of_mem_closedSignCone
      l w.face hY0 hYFull
  have hyb : A.Incident y T.b := by
    exact (A.incident_projectivization_mk_iff_orientedEvaluation_eq_zero
      sigma T.b Y hY0).2 hYb
  have hyd : A.Incident y c := by
    exact (A.incident_projectivization_mk_iff_orientedEvaluation_eq_zero
      sigma c Y hY0).2 hYd
  have hyVertex : y ∈ A.vertexSet := by
    have hyEq : y = A.intersection T.b c :=
      A.eq_intersection_of_incident hcb.symm hyb hyd
    rw [hyEq]
    exact A.intersection_mem_vertexSet hcb.symm
  have hyl : ¬ A.Incident y l := by
    intro hinc
    have hzero :=
      (A.incident_projectivization_mk_iff_orientedEvaluation_eq_zero
        sigma l Y hY0).1 hinc
    exact (ne_of_gt hYl) hzero
  have hya : ¬ A.Incident y T.a := by
    intro hinc
    have hzero :=
      (A.incident_projectivization_mk_iff_orientedEvaluation_eq_zero
        sigma T.a Y hY0).1 hinc
    exact (ne_of_gt hYa) hzero
  have hboundary' : A.arrangementFaceBoundary w.face =
      {T.edgeB, w.base, T.edgeA} := by
    rw [T.boundary]
    ext e
    simp [or_comm, or_left_comm, or_assoc]
  have := A.incident_third_support_of_vertex_mem_closure_exact_triangle
    hA w.face T.edgeB w.base T.edgeA T.b l T.a y hboundary'
      T.edgeB_line w.base_line T.edgeA_line
      T.b_ne_base.symm T.a_ne_b T.a_ne_base.symm
      hyVertex hyClosure hyb hyl
  exact hya this

/-- The symmetric closure statement across the literal side `a`. -/
theorem OrdinaryAttachmentExactTriangleFrame.return_mem_flip_left
    (A : FiniteProjectiveLineArrangement Line) (hA : A.NonPencil)
    {q : A.OrdinaryVertex} {l : Line}
    {w : OrdinaryAttachmentWitness A q l}
    (T : OrdinaryAttachmentExactTriangleFrame A q l w)
    (x : RealProjectivePoint) (hxVertex : x ∈ A.vertexSet)
    (hxOuter : A.projectivePointMemTriangleSector
      (flipSignAt (A.arrangementFaceSignPattern l w.face) T.a)
        l T.a T.b x)
    (hxl : ¬ A.Incident x l)
    (c : Line) (hxc : A.Incident x c) (hlc : l ≠ c) :
    A.projectivePointMemTriangleSector
      (flipSignAt (A.arrangementFaceSignPattern l w.face) T.a)
        l T.a T.b (A.intersection l c) := by
  have hx' : A.projectivePointMemTriangleSector
      (flipSignAt (A.arrangementFaceSignPattern l w.face) T.a)
        l T.b T.a x := by
    unfold projectivePointMemTriangleSector at hxOuter ⊢
    have hset : ({l, T.b, T.a} : Finset Line) = {l, T.a, T.b} := by
      ext k
      simp [or_comm, or_left_comm, or_assoc]
    simpa only [hset] using hxOuter
  have h :=
    OrdinaryAttachmentExactTriangleFrame.return_mem_flip_right
      A hA T.swap x hxVertex hx' hxl c hxc hlc
  unfold projectivePointMemTriangleSector at h ⊢
  have hset : ({l, T.b, T.a} : Finset Line) = {l, T.a, T.b} := by
    ext k
    simp [or_comm, or_left_comm, or_assoc]
  simpa only [OrdinaryAttachmentExactTriangleFrame.swap, hset] using h

namespace OrdinaryAttachmentOuterSectorFront

variable {A : FiniteProjectiveLineArrangement Line}
  {q : A.OrdinaryVertex} {l : Line}

/-- Forget only the endpoint labels from the richer outer-sector edge
package, retaining exactly the data used by return closure. -/
def exactTriangleFrame
    (F : OrdinaryAttachmentOuterSectorFront A q l)
    (S : OrdinaryAttachmentOuterSectorSideEdges F) :
    OrdinaryAttachmentExactTriangleFrame A q l F.attachment where
  a := F.frame.a
  b := F.frame.b
  edgeA := S.leftEdge
  edgeB := S.rightEdge
  a_ne_b := F.frame.a_ne_b
  a_ne_base := F.frame.a_ne_base
  b_ne_base := F.frame.b_ne_base
  q_on_a := F.frame.q_on_a
  q_on_b := F.frame.q_on_b
  edgeA_line := S.leftEdge_line
  edgeB_line := S.rightEdge_line
  boundary := S.boundary_eq

/-- Uniform callback required by the local Three-Clause consumer in the
outer chamber across the side supported by `a`. -/
theorem leftOuter_return_mem
    (F : OrdinaryAttachmentOuterSectorFront A q l) (hA : A.NonPencil)
    (x : RealProjectivePoint) (hxVertex : x ∈ A.vertexSet)
    (hxOuter : A.projectivePointMemTriangleSector
      F.leftOuterSigma l F.frame.a F.frame.b x)
    (hxl : ¬ A.Incident x l)
    (c : Line) (hxc : A.Incident x c) (hlc : l ≠ c) :
    A.projectivePointMemTriangleSector
      F.leftOuterSigma l F.frame.a F.frame.b (A.intersection l c) := by
  obtain ⟨S⟩ := F.exists_sideEdges hA
  have h := OrdinaryAttachmentExactTriangleFrame.return_mem_flip_left
    A hA (F.exactTriangleFrame S) x hxVertex (by
      simpa only [leftOuterSigma, attachmentFaceSigma, flipSignAt] using
        hxOuter) hxl c hxc hlc
  simpa only [leftOuterSigma, attachmentFaceSigma, flipSignAt] using h

/-- Uniform callback required by the local Three-Clause consumer in the
outer chamber across the side supported by `b`. -/
theorem rightOuter_return_mem
    (F : OrdinaryAttachmentOuterSectorFront A q l) (hA : A.NonPencil)
    (x : RealProjectivePoint) (hxVertex : x ∈ A.vertexSet)
    (hxOuter : A.projectivePointMemTriangleSector
      F.rightOuterSigma l F.frame.a F.frame.b x)
    (hxl : ¬ A.Incident x l)
    (c : Line) (hxc : A.Incident x c) (hlc : l ≠ c) :
    A.projectivePointMemTriangleSector
      F.rightOuterSigma l F.frame.a F.frame.b (A.intersection l c) := by
  obtain ⟨S⟩ := F.exists_sideEdges hA
  have h := OrdinaryAttachmentExactTriangleFrame.return_mem_flip_right
    A hA (F.exactTriangleFrame S) x hxVertex (by
      simpa only [rightOuterSigma, attachmentFaceSigma, flipSignAt] using
        hxOuter) hxl c hxc hlc
  simpa only [rightOuterSigma, attachmentFaceSigma, flipSignAt] using h

end OrdinaryAttachmentOuterSectorFront

end FiniteProjectiveLineArrangement

end Erdos506.Incidence
