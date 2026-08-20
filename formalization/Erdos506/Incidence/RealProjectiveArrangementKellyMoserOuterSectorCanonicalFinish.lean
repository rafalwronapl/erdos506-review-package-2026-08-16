import Erdos506.Incidence.RealProjectiveArrangementKellyMoserOuterReturnClosure

/-!
# Canonical Kelly--Moser outer sectors

This leaf identifies the two concrete transverse witnesses with the two
canonical sign sectors obtained by flipping one side of the initial attached
triangle.  It sits above `OuterReturnClosure` so the common facet router can
be reused without introducing an import cycle in the incidence front.
-/

namespace Erdos506.Incidence

open scoped LinearAlgebra.Projectivization

namespace FiniteProjectiveLineArrangement

variable {Line : Type*} [Fintype Line] [DecidableEq Line]

noncomputable local instance realProjectivePointTopologicalSpaceForKellyMoserOuterSectorCanonicalFinish :
    TopologicalSpace RealProjectivePoint :=
  realProjectivePointQuotientTopology

noncomputable local instance realProjectivePointDecidableEqForKellyMoserOuterSectorCanonicalFinish :
    DecidableEq RealProjectivePoint :=
  Classical.decEq _

noncomputable local instance geometricEdgeDecidableEqForKellyMoserOuterSectorCanonicalFinish
    (A : FiniteProjectiveLineArrangement Line) : DecidableEq A.GeometricEdge :=
  A.geometricEdgeDecidableEqForOrdinaryEdgeTriangle

noncomputable local instance incidentDecidableForKellyMoserOuterSectorCanonicalFinish
    (A : FiniteProjectiveLineArrangement Line)
    (p : RealProjectivePoint) (l : Line) : Decidable (A.Incident p l) :=
  Classical.propDecidable _

namespace OrdinaryAttachmentOuterSectorFront

variable {A : FiniteProjectiveLineArrangement Line}
  {q : A.OrdinaryVertex} {l : Line}

/-- Membership in the original three-line face sector projects into the
closure of the attached face, for either choice of homogeneous sign. -/
private theorem mem_attachmentFaceClosure_of_mem_faceSector
    (F : OrdinaryAttachmentOuterSectorFront A q l) (hA : A.NonPencil)
    (x : RealProjectivePoint)
    (hx : A.projectivePointMemTriangleSector F.attachmentFaceSigma
      l F.frame.a F.frame.b x) :
    x ∈ closure (A.arrangementFaceCarrier F.attachment.face) := by
  obtain ⟨S⟩ := F.exists_sideEdges hA
  have hcone : A.arrangementClosedSignConeOn F.attachmentFaceSigma
      {l, F.frame.a, F.frame.b} =
        A.arrangementClosedSignCone F.attachmentFaceSigma := by
    simpa only [attachmentFaceSigma] using
      A.arrangementClosedSignConeOn_eq_of_exact_triangle_boundary
        hA l F.attachment.face F.attachment.base S.leftEdge S.rightEdge
          l F.frame.a F.frame.b S.boundary_eq F.attachment.base_line
          S.leftEdge_line S.rightEdge_line F.frame.a_ne_base
          F.frame.b_ne_base F.frame.a_ne_b
  rcases hx with hx | hx
  · have hxFull : x.rep ∈
        A.arrangementClosedSignCone F.attachmentFaceSigma := by
      rw [← hcone]
      exact hx
    have hclosure :=
      A.projectivization_mem_closure_arrangementFaceCarrier_of_mem_closedSignCone
        l F.attachment.face x.rep_nonzero hxFull
    simpa only [x.mk_rep] using hclosure
  · have hxFull : -x.rep ∈
        A.arrangementClosedSignCone F.attachmentFaceSigma := by
      rw [← hcone]
      exact hx
    have hclosure :=
      A.projectivization_mem_closure_arrangementFaceCarrier_of_mem_closedSignCone
        l F.attachment.face (neg_ne_zero.mpr x.rep_nonzero) hxFull
    have hmk : Projectivization.mk ℝ (-x.rep)
        (neg_ne_zero.mpr x.rep_nonzero) = x := by
      rw [← x.mk_rep]
      apply (Projectivization.mk_eq_mk_iff' ℝ _ _ _ _).mpr
      exact ⟨-1, by simp⟩
    simpa only [hmk] using hclosure

/-- The witness on `b ∩ cross` lies in the canonical chamber across the
opposite side `a`.  This is the cross-matching in Figure 5.7. -/
theorem rightWitness_mem_leftOuterSector
    (F : OrdinaryAttachmentOuterSectorFront A q l) (hA : A.NonPencil) :
    A.projectivePointMemTriangleSector F.leftOuterSigma
      l F.frame.a F.frame.b F.rightWitness := by
  by_contra hout
  have hout' : ¬ A.projectivePointMemTriangleSector
      (flipSignAt F.attachmentFaceSigma F.frame.a)
        F.frame.b l F.frame.a F.rightWitness := by
    intro h
    apply hout
    change A.projectivePointMemTriangleSector F.leftOuterSigma
      F.frame.b l F.frame.a F.rightWitness at h
    unfold projectivePointMemTriangleSector at h ⊢
    have hset : ({F.frame.b, l, F.frame.a} : Finset Line) =
        {l, F.frame.a, F.frame.b} := by
      ext k
      simp [or_comm, or_left_comm, or_assoc]
    simpa only [hset] using h
  have hface' :=
    A.projectivePointMemTriangleSector_of_incident_base_of_not_flip_right
      F.attachmentFaceSigma F.frame.b l F.frame.a
        F.frame.a_ne_b F.frame.a_ne_base.symm F.rightWitness
        F.rightWitness_incident_right hout'
  have hface : A.projectivePointMemTriangleSector F.attachmentFaceSigma
      l F.frame.a F.frame.b F.rightWitness := by
    unfold projectivePointMemTriangleSector at hface' ⊢
    have hset : ({F.frame.b, l, F.frame.a} : Finset Line) =
        {l, F.frame.a, F.frame.b} := by
      ext k
      simp [or_comm, or_left_comm, or_assoc]
    simpa only [hset] using hface'
  have hclosure : F.rightWitness ∈
      closure (A.arrangementFaceCarrier F.attachment.face) :=
    mem_attachmentFaceClosure_of_mem_faceSector F hA F.rightWitness hface
  obtain ⟨S⟩ := F.exists_sideEdges hA
  have hboundary : A.arrangementFaceBoundary F.attachment.face =
      {S.rightEdge, F.attachment.base, S.leftEdge} := by
    rw [S.boundary_eq]
    ext e
    simp [or_comm, or_left_comm, or_assoc]
  have hleft : A.Incident F.rightWitness F.frame.a :=
    A.incident_third_support_of_vertex_mem_closure_exact_triangle
      hA F.attachment.face S.rightEdge F.attachment.base S.leftEdge
        F.frame.b l F.frame.a F.rightWitness hboundary
        S.rightEdge_line F.attachment.base_line S.leftEdge_line
        F.frame.b_ne_base.symm F.frame.a_ne_b
        F.frame.a_ne_base.symm F.rightWitness_mem_vertexSet hclosure
        F.rightWitness_incident_right F.rightWitness_away
  have hwq : F.rightWitness = q.1 := by
    calc
      F.rightWitness = A.intersection F.frame.a F.frame.b :=
        A.eq_intersection_of_incident F.frame.a_ne_b hleft
          F.rightWitness_incident_right
      _ = q.1 :=
        (A.eq_intersection_of_incident F.frame.a_ne_b
          F.frame.q_on_a F.frame.q_on_b).symm
  exact F.rightWitness_ne_attachment hwq

/-- Symmetrically, the witness on `a ∩ cross` lies in the canonical chamber
across the opposite side `b`. -/
theorem leftWitness_mem_rightOuterSector
    (F : OrdinaryAttachmentOuterSectorFront A q l) (hA : A.NonPencil) :
    A.projectivePointMemTriangleSector F.rightOuterSigma
      l F.frame.a F.frame.b F.leftWitness := by
  by_contra hout
  have hout' : ¬ A.projectivePointMemTriangleSector
      (flipSignAt F.attachmentFaceSigma F.frame.b)
        F.frame.a l F.frame.b F.leftWitness := by
    intro h
    apply hout
    change A.projectivePointMemTriangleSector F.rightOuterSigma
      F.frame.a l F.frame.b F.leftWitness at h
    unfold projectivePointMemTriangleSector at h ⊢
    have hset : ({F.frame.a, l, F.frame.b} : Finset Line) =
        {l, F.frame.a, F.frame.b} := by
      ext k
      simp [or_comm, or_left_comm, or_assoc]
    simpa only [hset] using h
  have hface' :=
    A.projectivePointMemTriangleSector_of_incident_base_of_not_flip_right
      F.attachmentFaceSigma F.frame.a l F.frame.b
        F.frame.a_ne_b.symm F.frame.b_ne_base.symm F.leftWitness
        F.leftWitness_incident_left hout'
  have hface : A.projectivePointMemTriangleSector F.attachmentFaceSigma
      l F.frame.a F.frame.b F.leftWitness := by
    unfold projectivePointMemTriangleSector at hface' ⊢
    have hset : ({F.frame.a, l, F.frame.b} : Finset Line) =
        {l, F.frame.a, F.frame.b} := by
      ext k
      simp [or_comm, or_left_comm, or_assoc]
    simpa only [hset] using hface'
  have hclosure : F.leftWitness ∈
      closure (A.arrangementFaceCarrier F.attachment.face) :=
    mem_attachmentFaceClosure_of_mem_faceSector F hA F.leftWitness hface
  obtain ⟨S⟩ := F.exists_sideEdges hA
  have hboundary : A.arrangementFaceBoundary F.attachment.face =
      {S.leftEdge, F.attachment.base, S.rightEdge} := by
    rw [S.boundary_eq]
    ext e
    simp [or_comm, or_left_comm, or_assoc]
  have hright : A.Incident F.leftWitness F.frame.b :=
    A.incident_third_support_of_vertex_mem_closure_exact_triangle
      hA F.attachment.face S.leftEdge F.attachment.base S.rightEdge
        F.frame.a l F.frame.b F.leftWitness hboundary
        S.leftEdge_line F.attachment.base_line S.rightEdge_line
        F.frame.a_ne_base.symm F.frame.a_ne_b.symm
        F.frame.b_ne_base.symm F.leftWitness_mem_vertexSet hclosure
        F.leftWitness_incident_left F.leftWitness_away
  have hwq : F.leftWitness = q.1 := by
    calc
      F.leftWitness = A.intersection F.frame.a F.frame.b :=
        A.eq_intersection_of_incident F.frame.a_ne_b
          F.leftWitness_incident_left hright
      _ = q.1 :=
        (A.eq_intersection_of_incident F.frame.a_ne_b
          F.frame.q_on_a F.frame.q_on_b).symm
  exact F.leftWitness_ne_attachment hwq

/-- The canonical chamber across `a` has the concrete witness `cross ∩ b`. -/
theorem leftOuterSector_nonempty
    (F : OrdinaryAttachmentOuterSectorFront A q l) (hA : A.NonPencil) :
    (A.triangleSectorOffBaseVertexSet
      F.leftOuterSigma l F.frame.a F.frame.b).Nonempty := by
  classical
  refine ⟨F.rightWitness, Finset.mem_filter.mpr ?_⟩
  exact ⟨F.rightWitness_mem_vertexSet,
    F.rightWitness_mem_leftOuterSector hA, F.rightWitness_away⟩

/-- The canonical chamber across `b` has the concrete witness `a ∩ cross`. -/
theorem rightOuterSector_nonempty
    (F : OrdinaryAttachmentOuterSectorFront A q l) (hA : A.NonPencil) :
    (A.triangleSectorOffBaseVertexSet
      F.rightOuterSigma l F.frame.a F.frame.b).Nonempty := by
  classical
  refine ⟨F.leftWitness, Finset.mem_filter.mpr ?_⟩
  exact ⟨F.leftWitness_mem_vertexSet,
    F.leftWitness_mem_rightOuterSector hA, F.leftWitness_away⟩

end OrdinaryAttachmentOuterSectorFront

end FiniteProjectiveLineArrangement

end Erdos506.Incidence
