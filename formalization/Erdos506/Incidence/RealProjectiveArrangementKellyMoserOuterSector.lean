import Erdos506.Incidence.RealProjectiveArrangementKellyMoserOuterFinish
import Erdos506.Incidence.RealProjectiveArrangementKellyMoserDegreeOneExtra
import Erdos506.Incidence.RealProjectiveTriangleCrossingSign

/-!
# The two outer sectors of a Kelly--Moser attachment

This leaf records the incidence part of Felsner's outer-sector construction.
Starting with a literal ordinary attachment to a base line, a third marked
point of the base supplies a transverse support.  Its intersections with the
two side supports are actual off-base arrangement vertices witnessing two of
the four sign sectors of the *same* three lines `(l, a, b)`.

The cyclic statement that every support through a vertex in either sector
returns to the corresponding base arc is deliberately not built into the
structure below: it needs the literal side edges of the attached triangular
face, rather than just the three-line sign cone.
-/

namespace Erdos506.Incidence

open scoped LinearAlgebra.Projectivization

namespace FiniteProjectiveLineArrangement

variable {Line : Type*} [Fintype Line] [DecidableEq Line]

noncomputable local instance realProjectivePointTopologicalSpaceForKellyMoserOuterSector :
    TopologicalSpace RealProjectivePoint :=
  realProjectivePointQuotientTopology

noncomputable local instance realProjectivePointDecidableEqForKellyMoserOuterSector :
    DecidableEq RealProjectivePoint :=
  Classical.decEq _

noncomputable local instance geometricEdgeDecidableEqForKellyMoserOuterSector
    (A : FiniteProjectiveLineArrangement Line) : DecidableEq A.GeometricEdge :=
  A.geometricEdgeDecidableEqForOrdinaryEdgeTriangle

noncomputable local instance incidentDecidableForKellyMoserOuterSector
    (A : FiniteProjectiveLineArrangement Line)
    (p : RealProjectivePoint) (l : Line) : Decidable (A.Incident p l) :=
  Classical.propDecidable _

/-- Choosing the orientation of a scalar by its strict sign always makes it
nonnegative, including at zero. -/
theorem signedByPositivity_nonneg (r : ℝ) :
    0 ≤ if decide (0 < r) then r else -r := by
  by_cases hr : 0 < r
  · simp [hr, hr.le]
  · have hr' : r ≤ 0 := le_of_not_gt hr
    simp [hr, neg_nonneg.mpr hr']

/-- Orient every arrangement covector toward a specified projective point.
This is only used on a three-line subarrangement, so zeros at its two apex
supports are allowed. -/
noncomputable def closedSectorSignPatternAt
    (A : FiniteProjectiveLineArrangement Line)
    (x : RealProjectivePoint) : Line → Bool := fun k =>
  decide (0 < projectiveLineEvaluation (A.projectiveLine k) x.rep)

/-- The representative of the defining point lies in every finite closed
cone cut out using its pointwise sign pattern. -/
theorem rep_mem_arrangementClosedSignConeOn_closedSectorSignPatternAt
    (A : FiniteProjectiveLineArrangement Line)
    (x : RealProjectivePoint) (K : Finset Line) :
    x.rep ∈ A.arrangementClosedSignConeOn
      (A.closedSectorSignPatternAt x) K := by
  rw [A.mem_arrangementClosedSignConeOn]
  intro k _hk
  unfold closedSectorSignPatternAt arrangementOrientedEvaluation
  by_cases hpos :
      0 < projectiveLineEvaluation (A.projectiveLine k) x.rep
  · simp only [hpos, decide_true, if_true]
    exact hpos.le
  · simp only [hpos, decide_false, if_false, LinearMap.neg_apply]
    exact neg_nonneg.mpr (le_of_not_gt hpos)

/-- Away from the corresponding line, the point-oriented evaluation is
strictly positive. -/
theorem arrangementOrientedEvaluation_closedSectorSignPatternAt_pos
    (A : FiniteProjectiveLineArrangement Line)
    (x : RealProjectivePoint) (k : Line) (hxk : ¬ A.Incident x k) :
    0 < A.arrangementOrientedEvaluation
      (A.closedSectorSignPatternAt x) k x.rep := by
  have heval : projectiveLineEvaluation (A.projectiveLine k) x.rep ≠ 0 :=
    (A.projectiveLineEvaluation_rep_eq_zero_iff_incident x k).not.mpr hxk
  rcases lt_or_gt_of_ne heval with hneg | hpos
  · simp [closedSectorSignPatternAt, arrangementOrientedEvaluation,
      not_lt_of_ge hneg.le, neg_pos.mpr hneg]
  · simp [closedSectorSignPatternAt, arrangementOrientedEvaluation, hpos]

/-- In particular the defining point belongs to the associated projective
three-line sector. -/
theorem projectivePointMemTriangleSector_closedSectorSignPatternAt
    (A : FiniteProjectiveLineArrangement Line)
    (x : RealProjectivePoint) (l a b : Line) :
    A.projectivePointMemTriangleSector
      (A.closedSectorSignPatternAt x) l a b x := by
  exact Or.inl
    (A.rep_mem_arrangementClosedSignConeOn_closedSectorSignPatternAt
      x {l, a, b})

/-- At a point on one side of a triangle, strict agreement of the two
remaining oriented evaluations is exactly the local datum needed for
membership in the corresponding closed projective sector. -/
theorem projectivePointMemTriangleSector_of_incident_middle_of_pair_pos
    (A : FiniteProjectiveLineArrangement Line) (sigma : Line → Bool)
    (l m n : Line) (x : RealProjectivePoint)
    (hxm : A.Incident x m)
    (hpair : 0 < A.arrangementOrientedEvaluation sigma l x.rep *
      A.arrangementOrientedEvaluation sigma n x.rep) :
    A.projectivePointMemTriangleSector sigma l m n x := by
  have hm0 : A.arrangementOrientedEvaluation sigma m x.rep = 0 := by
    apply (A.incident_projectivization_mk_iff_orientedEvaluation_eq_zero
      sigma m x.rep x.rep_nonzero).1
    simpa only [x.mk_rep] using hxm
  rcases mul_pos_iff.mp hpair with h | h
  · left
    rw [A.mem_arrangementClosedSignConeOn]
    intro k hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hk
    rcases hk with rfl | rfl | rfl
    · exact h.1.le
    · exact hm0.symm.le
    · exact h.2.le
  · right
    rw [A.mem_arrangementClosedSignConeOn]
    intro k hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hk
    rcases hk with rfl | rfl | rfl
    · rw [LinearMap.map_neg]
      exact neg_nonneg.mpr h.1.le
    · rw [LinearMap.map_neg, hm0, neg_zero]
    · rw [LinearMap.map_neg]
      exact neg_nonneg.mpr h.2.le

/-- Converse weak-sign reader at a point on the middle side. -/
theorem orientedPair_nonneg_of_memTriangleSector_of_incident_middle
    (A : FiniteProjectiveLineArrangement Line) (sigma : Line → Bool)
    (l m n : Line) (x : RealProjectivePoint)
    (hxm : A.Incident x m)
    (hx : A.projectivePointMemTriangleSector sigma l m n x) :
    0 ≤ A.arrangementOrientedEvaluation sigma l x.rep *
      A.arrangementOrientedEvaluation sigma n x.rep := by
  rcases hx with hx | hx
  · exact mul_nonneg
      (hx l (by simp)) (hx n (by simp))
  · have hl : A.arrangementOrientedEvaluation sigma l x.rep ≤ 0 := by
      have h := hx l (by simp)
      rw [LinearMap.map_neg] at h
      exact neg_nonneg.mp h
    have hn : A.arrangementOrientedEvaluation sigma n x.rep ≤ 0 := by
      have h := hx n (by simp)
      rw [LinearMap.map_neg] at h
      exact neg_nonneg.mp h
    exact mul_nonneg_of_nonpos_of_nonpos hl hn

/-- A marked point on an arrangement line has some other indexed support. -/
theorem CircularGapSlot.exists_incident_line_ne_base
    (A : FiniteProjectiveLineArrangement Line) (l : Line)
    (v : A.CircularGapSlot l) :
    ∃ c : Line, c ≠ l ∧ A.Incident v.1 c := by
  have hvVertex : v.1 ∈ A.vertexSet :=
    ((A.mem_lineVertexSet l).mp v.2).1
  obtain ⟨c, d, hcd, hcdv⟩ := A.exists_lines_of_mem_vertexSet hvVertex
  have hvc : A.Incident v.1 c := by
    rw [← hcdv]
    exact A.intersection_incident_left hcd
  have hvd : A.Incident v.1 d := by
    rw [← hcdv]
    exact A.intersection_incident_right hcd
  by_cases hcl : c = l
  · refine ⟨d, ?_, hvd⟩
    intro hdl
    exact hcd (hcl.trans hdl.symm)
  · exact ⟨c, hcl, hvc⟩

/-- Lossless incidence data for the two regions opposite an attached
triangle.  The transverse line is witness data only; both regions are sign
sectors of the original triple `(l, frame.a, frame.b)`. -/
structure OrdinaryAttachmentOuterSectorFront
    (A : FiniteProjectiveLineArrangement Line)
    (q : A.OrdinaryVertex) (l : Line) where
  attachment : OrdinaryAttachmentWitness A q l
  frame : OrdinaryAttachmentSideFrame A q l
  third : A.CircularGapSlot l
  third_ne_leftReturn : third.1 ≠ frame.p.1
  third_ne_rightReturn : third.1 ≠ frame.r.1
  cross : Line
  cross_ne_base : cross ≠ l
  cross_ne_left : cross ≠ frame.a
  cross_ne_right : cross ≠ frame.b
  third_on_cross : A.Incident third.1 cross

/-- The two literal clean side edges of the attached triangular face. -/
structure OrdinaryAttachmentOuterSectorSideEdges
    {A : FiniteProjectiveLineArrangement Line}
    {q : A.OrdinaryVertex} {l : Line}
    (F : OrdinaryAttachmentOuterSectorFront A q l) where
  leftEdge : A.GeometricEdge
  rightEdge : A.GeometricEdge
  leftEdge_line : A.edgeSlotLine leftEdge = F.frame.a
  rightEdge_line : A.edgeSlotLine rightEdge = F.frame.b
  leftEdge_mem : leftEdge ∈
    A.arrangementFaceBoundary F.attachment.face
  rightEdge_mem : rightEdge ∈
    A.arrangementFaceBoundary F.attachment.face
  boundary_eq : A.arrangementFaceBoundary F.attachment.face =
    {F.attachment.base, leftEdge, rightEdge}
  leftEndpointPair :
    ({A.geometricEdgeInitial leftEdge,
        A.geometricEdgeTerminal leftEdge} : Finset RealProjectivePoint) =
      {F.frame.p.1, q.1}
  rightEndpointPair :
    ({A.geometricEdgeInitial rightEdge,
        A.geometricEdgeTerminal rightEdge} : Finset RealProjectivePoint) =
      {F.frame.r.1, q.1}

/-- A concrete arrangement vertex on the first outer side. -/
noncomputable def OrdinaryAttachmentOuterSectorFront.leftWitness
    {A : FiniteProjectiveLineArrangement Line}
    {q : A.OrdinaryVertex} {l : Line}
    (F : OrdinaryAttachmentOuterSectorFront A q l) :
    RealProjectivePoint :=
  A.intersection F.frame.a F.cross

/-- A concrete arrangement vertex on the second outer side. -/
noncomputable def OrdinaryAttachmentOuterSectorFront.rightWitness
    {A : FiniteProjectiveLineArrangement Line}
    {q : A.OrdinaryVertex} {l : Line}
    (F : OrdinaryAttachmentOuterSectorFront A q l) :
    RealProjectivePoint :=
  A.intersection F.cross F.frame.b

/-- An attachment on a base with at least three marked cyclic slots has the
incidence front of both opposite sectors. -/
theorem OrdinaryAttachmentWitness.exists_outerSectorFront
    (A : FiniteProjectiveLineArrangement Line) (hA : A.NonPencil)
    {q : A.OrdinaryVertex} {l : Line}
    (w : OrdinaryAttachmentWitness A q l)
    (hthree : 3 ≤ Fintype.card (A.CircularGapSlot l)) :
    Nonempty (OrdinaryAttachmentOuterSectorFront A q l) := by
  classical
  obtain ⟨frame⟩ := OrdinaryAttachmentWitness.exists_sideFrame A hA w
  obtain ⟨third, hvp, hvr⟩ :=
    A.exists_circularGapSlot_val_ne_pair_of_three_le
      l hthree frame.p frame.r frame.p_ne_r
  obtain ⟨cross, hcrossBase, hvCross⟩ :=
    CircularGapSlot.exists_incident_line_ne_base A l third
  have hvBase : A.Incident third.1 l :=
    ((A.mem_lineVertexSet l).mp third.2).2
  have hvNotLeft : ¬ A.Incident third.1 frame.a := by
    intro hvLeft
    apply hvp
    calc
      third.1 = A.intersection l frame.a :=
        A.eq_intersection_of_incident
          frame.a_ne_base.symm hvBase hvLeft
      _ = frame.p.1 := frame.p_eq_intersection.symm
  have hvNotRight : ¬ A.Incident third.1 frame.b := by
    intro hvRight
    apply hvr
    calc
      third.1 = A.intersection l frame.b :=
        A.eq_intersection_of_incident
          frame.b_ne_base.symm hvBase hvRight
      _ = frame.r.1 := frame.r_eq_intersection.symm
  have hcrossLeft : cross ≠ frame.a := by
    intro h
    apply hvNotLeft
    simpa only [h] using hvCross
  have hcrossRight : cross ≠ frame.b := by
    intro h
    apply hvNotRight
    simpa only [h] using hvCross
  exact ⟨{
    attachment := w
    frame := frame
    third := third
    third_ne_leftReturn := hvp
    third_ne_rightReturn := hvr
    cross := cross
    cross_ne_base := hcrossBase
    cross_ne_left := hcrossLeft
    cross_ne_right := hcrossRight
    third_on_cross := hvCross
  }⟩

namespace OrdinaryAttachmentOuterSectorFront

variable {A : FiniteProjectiveLineArrangement Line}
  {q : A.OrdinaryVertex} {l : Line}

theorem leftWitness_mem_vertexSet
    (F : OrdinaryAttachmentOuterSectorFront A q l) :
    F.leftWitness ∈ A.vertexSet := by
  exact A.intersection_mem_vertexSet F.cross_ne_left.symm

theorem rightWitness_mem_vertexSet
    (F : OrdinaryAttachmentOuterSectorFront A q l) :
    F.rightWitness ∈ A.vertexSet := by
  exact A.intersection_mem_vertexSet F.cross_ne_right

theorem leftWitness_incident_left
    (F : OrdinaryAttachmentOuterSectorFront A q l) :
    A.Incident F.leftWitness F.frame.a := by
  exact A.intersection_incident_left F.cross_ne_left.symm

theorem leftWitness_incident_cross
    (F : OrdinaryAttachmentOuterSectorFront A q l) :
    A.Incident F.leftWitness F.cross := by
  exact A.intersection_incident_right F.cross_ne_left.symm

theorem rightWitness_incident_cross
    (F : OrdinaryAttachmentOuterSectorFront A q l) :
    A.Incident F.rightWitness F.cross := by
  exact A.intersection_incident_left F.cross_ne_right

theorem rightWitness_incident_right
    (F : OrdinaryAttachmentOuterSectorFront A q l) :
    A.Incident F.rightWitness F.frame.b := by
  exact A.intersection_incident_right F.cross_ne_right

theorem leftWitness_away
    (F : OrdinaryAttachmentOuterSectorFront A q l) :
    ¬ A.Incident F.leftWitness l := by
  intro huBase
  have huP : F.leftWitness = F.frame.p.1 := by
    calc
      F.leftWitness = A.intersection l F.frame.a :=
        A.eq_intersection_of_incident F.frame.a_ne_base.symm
          huBase F.leftWitness_incident_left
      _ = F.frame.p.1 := F.frame.p_eq_intersection.symm
  have hvBase : A.Incident F.third.1 l :=
    ((A.mem_lineVertexSet l).mp F.third.2).2
  have huV : F.leftWitness = F.third.1 := by
    calc
      F.leftWitness = A.intersection l F.cross :=
        A.eq_intersection_of_incident F.cross_ne_base.symm
          huBase F.leftWitness_incident_cross
      _ = F.third.1 :=
        (A.eq_intersection_of_incident F.cross_ne_base.symm
          hvBase F.third_on_cross).symm
  exact F.third_ne_leftReturn (huV.symm.trans huP)

theorem rightWitness_away
    (F : OrdinaryAttachmentOuterSectorFront A q l) :
    ¬ A.Incident F.rightWitness l := by
  intro huBase
  have huR : F.rightWitness = F.frame.r.1 := by
    calc
      F.rightWitness = A.intersection l F.frame.b :=
        A.eq_intersection_of_incident F.frame.b_ne_base.symm
          huBase F.rightWitness_incident_right
      _ = F.frame.r.1 := F.frame.r_eq_intersection.symm
  have hvBase : A.Incident F.third.1 l :=
    ((A.mem_lineVertexSet l).mp F.third.2).2
  have huV : F.rightWitness = F.third.1 := by
    calc
      F.rightWitness = A.intersection l F.cross :=
        A.eq_intersection_of_incident F.cross_ne_base.symm
          huBase F.rightWitness_incident_cross
      _ = F.third.1 :=
        (A.eq_intersection_of_incident F.cross_ne_base.symm
          hvBase F.third_on_cross).symm
  exact F.third_ne_rightReturn (huV.symm.trans huR)

/-- The common three-line boundary of both outer sectors is nonconcurrent. -/
theorem boundary_nonconcurrent
    (F : OrdinaryAttachmentOuterSectorFront A q l) :
    ¬ ∃ x : RealProjectivePoint,
      A.Incident x l ∧ A.Incident x F.frame.a ∧
        A.Incident x F.frame.b := by
  exact A.not_three_concurrent_of_offBase_apex
    q.1 l F.frame.a F.frame.b F.frame.a_ne_b
      F.frame.q_on_a F.frame.q_on_b F.attachment.away

/-- Recover the two actual clean side edges, without forgetting their
supports or endpoint pairs. -/
theorem exists_sideEdges
    (F : OrdinaryAttachmentOuterSectorFront A q l) (hA : A.NonPencil) :
    Nonempty (OrdinaryAttachmentOuterSectorSideEdges F) := by
  classical
  have hqTwo : A.multiplicity q.1 = 2 :=
    (Finset.mem_filter.mp q.2).2
  have hordinaryAB : ∀ m : Line,
      A.Incident q.1 m ↔ m = F.frame.a ∨ m = F.frame.b :=
    A.incident_iff_eq_or_eq_of_multiplicity_eq_two
      q.1 F.frame.a F.frame.b F.frame.q_on_a F.frame.q_on_b
        F.frame.a_ne_b.symm hqTwo
  have hordinaryBA : ∀ m : Line,
      A.Incident q.1 m ↔ m = F.frame.b ∨ m = F.frame.a := by
    intro m
    rw [hordinaryAB m, or_comm]
  obtain ⟨leftEdge, hleftLine, hleftMem⟩ :=
    A.exists_transverse_boundaryEdge_of_mem_closure_of_ordinary_intersection
      hA F.attachment.face q.1 F.frame.b F.frame.a
        F.frame.a_ne_b F.frame.q_on_b F.frame.q_on_a
        hordinaryBA F.attachment.opposite
  obtain ⟨rightEdge, hrightLine, hrightMem⟩ :=
    A.exists_transverse_boundaryEdge_of_mem_closure_of_ordinary_intersection
      hA F.attachment.face q.1 F.frame.a F.frame.b
        F.frame.a_ne_b.symm F.frame.q_on_a F.frame.q_on_b
        hordinaryAB F.attachment.opposite
  have hedgeNe : leftEdge ≠ rightEdge := by
    intro h
    apply F.frame.a_ne_b
    calc
      F.frame.a = A.edgeSlotLine leftEdge := hleftLine.symm
      _ = A.edgeSlotLine rightEdge := congrArg A.edgeSlotLine h
      _ = F.frame.b := hrightLine
  have hbaseLeft : F.attachment.base ≠ leftEdge := by
    intro h
    apply F.attachment.away
    rw [← F.attachment.base_line, h, hleftLine]
    exact F.frame.q_on_a
  have hbaseRight : F.attachment.base ≠ rightEdge := by
    intro h
    apply F.attachment.away
    rw [← F.attachment.base_line, h, hrightLine]
    exact F.frame.q_on_b
  have hsub : ({F.attachment.base, leftEdge, rightEdge} :
      Finset A.GeometricEdge) ⊆
      A.arrangementFaceBoundary F.attachment.face := by
    intro e he
    simp only [Finset.mem_insert, Finset.mem_singleton] at he
    rcases he with rfl | rfl | rfl
    · exact F.attachment.base_mem
    · exact hleftMem
    · exact hrightMem
  have htriple : ({F.attachment.base, leftEdge, rightEdge} :
      Finset A.GeometricEdge).card = 3 := by
    simp [hedgeNe, hbaseLeft, hbaseRight]
  have hboundary : A.arrangementFaceBoundary F.attachment.face =
      {F.attachment.base, leftEdge, rightEdge} := by
    symm
    apply Finset.eq_of_subset_of_card_le hsub
    rw [F.attachment.triangular, htriple]
  have hboundaryLeft : A.arrangementFaceBoundary F.attachment.face =
      {leftEdge, F.attachment.base, rightEdge} := by
    simpa [Finset.insert_comm] using hboundary
  have hpairsLeft :=
    A.geometricEdge_endpoint_pair_eq_of_exact_triangle_boundary
      hA F.attachment.face leftEdge F.attachment.base rightEdge
        F.frame.a l F.frame.b hboundaryLeft hleftLine
        F.attachment.base_line hrightLine
        F.frame.a_ne_base.symm F.frame.a_ne_b.symm
        F.frame.b_ne_base.symm
  have hAL : A.intersection F.frame.a l = F.frame.p.1 := by
    calc
      A.intersection F.frame.a l = A.intersection l F.frame.a :=
        A.eq_intersection_of_incident F.frame.a_ne_base.symm
          (A.intersection_incident_right F.frame.a_ne_base)
          (A.intersection_incident_left F.frame.a_ne_base)
      _ = F.frame.p.1 := F.frame.p_eq_intersection.symm
  have hAQ : A.intersection F.frame.a F.frame.b = q.1 :=
    (A.eq_intersection_of_incident F.frame.a_ne_b
      F.frame.q_on_a F.frame.q_on_b).symm
  have hpairsLeft' :
      ({A.geometricEdgeInitial leftEdge,
          A.geometricEdgeTerminal leftEdge} : Finset RealProjectivePoint) =
        {F.frame.p.1, q.1} := by
    simpa only [hAL, hAQ] using hpairsLeft
  have hboundaryRight : A.arrangementFaceBoundary F.attachment.face =
      {rightEdge, F.attachment.base, leftEdge} := by
    rw [hboundary]
    ext e
    simp only [Finset.mem_insert, Finset.mem_singleton]
    tauto
  have hpairsRight :=
    A.geometricEdge_endpoint_pair_eq_of_exact_triangle_boundary
      hA F.attachment.face rightEdge F.attachment.base leftEdge
        F.frame.b l F.frame.a hboundaryRight hrightLine
        F.attachment.base_line hleftLine
        F.frame.b_ne_base.symm F.frame.a_ne_b
        F.frame.a_ne_base.symm
  have hBL : A.intersection F.frame.b l = F.frame.r.1 := by
    calc
      A.intersection F.frame.b l = A.intersection l F.frame.b :=
        A.eq_intersection_of_incident F.frame.b_ne_base.symm
          (A.intersection_incident_right F.frame.b_ne_base)
          (A.intersection_incident_left F.frame.b_ne_base)
      _ = F.frame.r.1 := F.frame.r_eq_intersection.symm
  have hBQ : A.intersection F.frame.b F.frame.a = q.1 :=
    (A.eq_intersection_of_incident F.frame.a_ne_b.symm
      F.frame.q_on_b F.frame.q_on_a).symm
  have hpairsRight' :
      ({A.geometricEdgeInitial rightEdge,
          A.geometricEdgeTerminal rightEdge} : Finset RealProjectivePoint) =
        {F.frame.r.1, q.1} := by
    simpa only [hBL, hBQ] using hpairsRight
  exact ⟨{
    leftEdge := leftEdge
    rightEdge := rightEdge
    leftEdge_line := hleftLine
    rightEdge_line := hrightLine
    leftEdge_mem := hleftMem
    rightEdge_mem := hrightMem
    boundary_eq := hboundary
    leftEndpointPair := hpairsLeft'
    rightEndpointPair := hpairsRight'
  }⟩

/-- One-call lossless extractor for the incidence front and both clean side
edges. -/
theorem OrdinaryAttachmentWitness.exists_outerSectorFrontWithSideEdges
    (A : FiniteProjectiveLineArrangement Line) (hA : A.NonPencil)
    {q : A.OrdinaryVertex} {l : Line}
    (w : OrdinaryAttachmentWitness A q l)
    (hthree : 3 ≤ Fintype.card (A.CircularGapSlot l)) :
    ∃ F : OrdinaryAttachmentOuterSectorFront A q l,
      Nonempty (OrdinaryAttachmentOuterSectorSideEdges F) := by
  obtain ⟨F⟩ :=
    OrdinaryAttachmentWitness.exists_outerSectorFront A hA w hthree
  exact ⟨F, F.exists_sideEdges hA⟩

/-! ## The clean frame for Felsner's degree-one construction -/

/-- `FelsnerOneLineFrame` with the successor fact it was constructed from
retained as an actual clean geometric edge. -/
structure FelsnerOneLineCleanFrame
    (A : FiniteProjectiveLineArrangement Line) (l : Line)
    extends FelsnerOneLineFrame A l where
  cleanEdge : A.GeometricEdge
  pm : A.CircularGapSlot m
  pm_val : pm.1 = p.1
  r_eq_successor : r = (A.circularGapSuccessor m pm).1
  cleanEdge_eq : cleanEdge = A.circularGapEdge m pm
  cleanEdge_line : A.edgeSlotLine cleanEdge = m
  cleanEdge_initial : A.geometricEdgeInitial cleanEdge = p.1
  cleanEdge_terminal : A.geometricEdgeTerminal cleanEdge = r

/-- Degree one produces the lossless clean frame needed by Figure 5.8. -/
theorem exists_felsnerOneLineCleanFrame_of_lineDegree_eq_one
    (A : FiniteProjectiveLineArrangement Line) (hA : A.NonPencil)
    (l : Line) (hone : A.lineOrdinaryVertexDegree l = 1) :
    Nonempty (FelsnerOneLineCleanFrame A l) := by
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
  let cleanEdge : A.GeometricEdge := A.circularGapEdge m pm
  have hrVertex : r ∈ A.vertexSet :=
    ((A.mem_lineVertexSet m).mp rSlot.2).1
  have hrM : A.Incident r m :=
    ((A.mem_lineVertexSet m).mp rSlot.2).2
  have hrp : r ≠ p.1 := by
    simpa only [r, rSlot, pm, cleanEdge, A.circularGapEdge_initial,
      A.circularGapEdge_terminal] using
      (A.geometricEdge_initial_ne_terminal_of_nonPencil hA cleanEdge).symm
  obtain ⟨u, v, huv, huv_r⟩ := A.exists_lines_of_mem_vertexSet hrVertex
  have hru : A.Incident r u := by
    rw [← huv_r]
    exact A.intersection_incident_left huv
  have hrv : A.Incident r v := by
    rw [← huv_r]
    exact A.intersection_incident_right huv
  obtain ⟨n, hnm, hrn⟩ :
      ∃ n : Line, n ≠ m ∧ A.Incident r n := by
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
  let qSlot : A.CircularGapSlot l :=
    ⟨A.intersection l n,
      A.intersection_mem_lineVertexSet_left hnl.symm⟩
  have hqne : qSlot.1 ≠ p.1 := by
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
    toFelsnerOneLineFrame := {
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
      q := qSlot
      q_eq_intersection := rfl
      q_ne_p := hqne
    }
    cleanEdge := cleanEdge
    pm := pm
    pm_val := rfl
    r_eq_successor := rfl
    cleanEdge_eq := rfl
    cleanEdge_line := A.circularGapEdge_line m pm
    cleanEdge_initial := by
      simp only [cleanEdge, A.circularGapEdge_initial, pm]
    cleanEdge_terminal := by
      simp only [cleanEdge, A.circularGapEdge_terminal, r, rSlot]
  }⟩

end OrdinaryAttachmentOuterSectorFront

/-- Three pairwise distinct points of the real projective line have one of
the two opposite strict cyclic orientations. -/
theorem realProjectiveCyclic_or_reverse
    (P Q R : RealProjectiveOnePoint)
    (hPQ : P ≠ Q) (hQR : Q ≠ R) (hRP : R ≠ P) :
    RealProjectiveCyclic P Q R ∨ RealProjectiveCyclic R Q P := by
  have hPQb : realProjectiveBracket P.rep Q.rep ≠ 0 := by
    intro hzero
    apply hPQ
    rw [← P.mk_rep, ← Q.mk_rep]
    exact (realProjective_mk_eq_mk_iff_bracket_eq_zero
      P.rep_nonzero Q.rep_nonzero).2 hzero
  have hQRb : realProjectiveBracket Q.rep R.rep ≠ 0 := by
    intro hzero
    apply hQR
    rw [← Q.mk_rep, ← R.mk_rep]
    exact (realProjective_mk_eq_mk_iff_bracket_eq_zero
      Q.rep_nonzero R.rep_nonzero).2 hzero
  have hRPb : realProjectiveBracket R.rep P.rep ≠ 0 := by
    intro hzero
    apply hRP
    rw [← R.mk_rep, ← P.mk_rep]
    exact (realProjective_mk_eq_mk_iff_bracket_eq_zero
      R.rep_nonzero P.rep_nonzero).2 hzero
  have htriple : realProjectiveTripleBracket P.rep Q.rep R.rep ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero hPQb hQRb) hRPb
  rcases lt_or_gt_of_ne htriple with hneg | hpos
  · right
    rw [realProjectiveCyclic_iff_rep_tripleBracket]
    have hreverse : realProjectiveTripleBracket R.rep Q.rep P.rep =
        -realProjectiveTripleBracket P.rep Q.rep R.rep := by
      unfold realProjectiveTripleBracket
      rw [realProjectiveBracket_swap R.rep Q.rep,
        realProjectiveBracket_swap Q.rep P.rep,
        realProjectiveBracket_swap P.rep R.rep]
      ring
    rw [hreverse]
    exact neg_pos.mpr hneg
  · left
    rw [realProjectiveCyclic_iff_rep_tripleBracket]
    exact hpos

/-- The total arrangement intersection agrees with Mathlib's projective
cross on distinct indexed lines. -/
theorem intersection_eq_projectiveCross_of_ne
    (A : FiniteProjectiveLineArrangement Line) {a b : Line}
    (hab : a ≠ b) :
    A.intersection a b =
      Projectivization.cross (A.projectiveLine a) (A.projectiveLine b) := by
  classical
  unfold intersection projectiveLineIntersection
  rw [dif_neg hab]

/-- A raw determinant evaluation at the intersection of two arrangement
lines is nonzero exactly when the third line misses that intersection. -/
theorem projectiveLineRep_dot_rawIntersection_ne_zero_iff
    (A : FiniteProjectiveLineArrangement Line) {a b c : Line}
    (hab : a ≠ b) :
    (A.projectiveLine c).rep ⬝ᵥ
          crossProduct (A.projectiveLine a).rep (A.projectiveLine b).rep ≠ 0 ↔
      ¬ A.Incident (A.intersection a b) c := by
  have hproj : A.projectiveLine a ≠ A.projectiveLine b :=
    A.projectiveLine_injective.ne hab
  calc
    (A.projectiveLine c).rep ⬝ᵥ
          crossProduct (A.projectiveLine a).rep (A.projectiveLine b).rep ≠ 0 ↔
        crossProduct (A.projectiveLine a).rep
            (A.projectiveLine b).rep ⬝ᵥ (A.projectiveLine c).rep ≠ 0 := by
          rw [dotProduct_comm]
    _ ↔ (Projectivization.cross
          (A.projectiveLine a) (A.projectiveLine b)).rep ⬝ᵥ
            (A.projectiveLine c).rep ≠ 0 :=
      (projectiveCross_evaluation_ne_zero_iff
        (A.projectiveLine a) (A.projectiveLine b)
          (A.projectiveLine c) hproj).symm
    _ ↔ ¬ A.Incident (A.intersection a b) c := by
      rw [intersection_eq_projectiveCross_of_ne A hab]
      simpa only [projectiveLineEvaluation] using
        (A.projectiveLineEvaluation_rep_eq_zero_iff_incident
          (Projectivization.cross (A.projectiveLine a)
            (A.projectiveLine b)) c).not

/-- The intrinsic two-side sign at an actual arrangement intersection. -/
noncomputable def intersectionPairEvaluation
    (A : FiniteProjectiveLineArrangement Line)
    (side cross other₀ other₁ : Line) : ℝ :=
  projectiveLineEvaluation (A.projectiveLine other₀)
      (A.intersection side cross).rep *
    projectiveLineEvaluation (A.projectiveLine other₁)
      (A.intersection side cross).rep

/-- Oriented version of the intrinsic two-side test. -/
noncomputable def orientedIntersectionPairEvaluation
    (A : FiniteProjectiveLineArrangement Line) (sigma : Line → Bool)
    (side cross other₀ other₁ : Line) : ℝ :=
  A.arrangementOrientedEvaluation sigma other₀
      (A.intersection side cross).rep *
    A.arrangementOrientedEvaluation sigma other₁
      (A.intersection side cross).rep

/-- Exact positive-square comparison between the actual and raw
intersection pair evaluations. -/
theorem intersectionPairEvaluation_eq_posSq_mul_raw
    (A : FiniteProjectiveLineArrangement Line)
    {side cross other₀ other₁ : Line} (hsc : side ≠ cross) :
    ∃ a : ℝ, 0 < a ^ 2 ∧
      A.intersectionPairEvaluation side cross other₀ other₁ =
        a ^ 2 * triangleCrossingSideProduct
          (A.projectiveLine side).rep (A.projectiveLine other₀).rep
            (A.projectiveLine other₁).rep (A.projectiveLine cross).rep := by
  have hproj : A.projectiveLine side ≠ A.projectiveLine cross :=
    A.projectiveLine_injective.ne hsc
  rw [intersectionPairEvaluation,
    intersection_eq_projectiveCross_of_ne A hsc]
  simpa only [projectiveLineEvaluation] using
    (projectiveCross_pairEvaluation_eq_posSq_mul
      (A.projectiveLine side) (A.projectiveLine cross)
        (A.projectiveLine other₀) (A.projectiveLine other₁) hproj)

/-- The positive sign of an actual two-side test agrees with its raw
homogeneous cross-product expression. -/
theorem intersectionPairEvaluation_pos_iff_raw
    (A : FiniteProjectiveLineArrangement Line)
    {side cross other₀ other₁ : Line} (hsc : side ≠ cross) :
    0 < A.intersectionPairEvaluation side cross other₀ other₁ ↔
      0 < triangleCrossingSideProduct
        (A.projectiveLine side).rep (A.projectiveLine other₀).rep
          (A.projectiveLine other₁).rep (A.projectiveLine cross).rep := by
  have hproj : A.projectiveLine side ≠ A.projectiveLine cross :=
    A.projectiveLine_injective.ne hsc
  rw [intersectionPairEvaluation,
    intersection_eq_projectiveCross_of_ne A hsc]
  simpa only [projectiveLineEvaluation] using
    (projectiveCross_pairEvaluation_pos_iff
      (A.projectiveLine side) (A.projectiveLine cross)
        (A.projectiveLine other₀) (A.projectiveLine other₁) hproj)

/-- Negative-sign companion to `intersectionPairEvaluation_pos_iff_raw`. -/
theorem intersectionPairEvaluation_neg_iff_raw
    (A : FiniteProjectiveLineArrangement Line)
    {side cross other₀ other₁ : Line} (hsc : side ≠ cross) :
    A.intersectionPairEvaluation side cross other₀ other₁ < 0 ↔
      triangleCrossingSideProduct
        (A.projectiveLine side).rep (A.projectiveLine other₀).rep
          (A.projectiveLine other₁).rep (A.projectiveLine cross).rep < 0 := by
  have hproj : A.projectiveLine side ≠ A.projectiveLine cross :=
    A.projectiveLine_injective.ne hsc
  rw [intersectionPairEvaluation,
    intersection_eq_projectiveCross_of_ne A hsc]
  simpa only [projectiveLineEvaluation] using
    (projectiveCross_pairEvaluation_neg_iff
      (A.projectiveLine side) (A.projectiveLine cross)
        (A.projectiveLine other₀) (A.projectiveLine other₁) hproj)

/-- Evaluation on the raw parameter vector detects incidence of the
corresponding projective point. -/
theorem projectiveLineEvaluation_parameterVector_eq_zero_iff_incident
    (A : FiniteProjectiveLineArrangement Line)
    (carrier : RealProjectiveLine) (k : Line)
    (X : RealProjectiveOnePoint) :
    projectiveLineEvaluation (A.projectiveLine k)
        (projectiveLineParameterLinearMap carrier X.rep) = 0 ↔
      A.Incident (projectiveLineParameter carrier X) k := by
  have hmap : projectiveLineParameterLinearMap carrier X.rep ≠ 0 :=
    by
      simpa only [map_zero] using
        Function.Injective.ne
          (projectiveLineParameterLinearMap_injective carrier) X.rep_nonzero
  have hparam : projectiveLineParameter carrier X =
      Projectivization.mk ℝ
        (projectiveLineParameterLinearMap carrier X.rep) hmap := by
    calc
      projectiveLineParameter carrier X =
          projectiveLineParameter carrier
            (Projectivization.mk ℝ X.rep X.rep_nonzero) :=
        congrArg (projectiveLineParameter carrier) X.mk_rep.symm
      _ = Projectivization.mk ℝ
          (projectiveLineParameterLinearMap carrier X.rep) hmap := by
        rw [projectiveLineParameter, Projectivization.map_mk]
  have h := A.incident_projectivization_mk_iff_orientedEvaluation_eq_zero
    (fun _ => true) k (projectiveLineParameterLinearMap carrier X.rep) hmap
  rw [hparam]
  simpa only [arrangementOrientedEvaluation, if_true] using h.symm

/-- The intrinsic relative sign may be computed on the raw vector used by
the projective-line parametrization. -/
theorem arrangementRelativeSign_projectiveLineParameter
    (A : FiniteProjectiveLineArrangement Line)
    (carrier : RealProjectiveLine) (a b : Line)
    (X : RealProjectiveOnePoint) :
    A.arrangementRelativeSign a b (projectiveLineParameter carrier X) =
      SignType.sign
        (projectiveLineEvaluation (A.projectiveLine a)
            (projectiveLineParameterLinearMap carrier X.rep) *
          projectiveLineEvaluation (A.projectiveLine b)
            (projectiveLineParameterLinearMap carrier X.rep)) := by
  have hmap : projectiveLineParameterLinearMap carrier X.rep ≠ 0 :=
    by
      simpa only [map_zero] using
        Function.Injective.ne
          (projectiveLineParameterLinearMap_injective carrier) X.rep_nonzero
  have hparam : projectiveLineParameter carrier X =
      Projectivization.mk ℝ
        (projectiveLineParameterLinearMap carrier X.rep) hmap := by
    calc
      projectiveLineParameter carrier X =
          projectiveLineParameter carrier
            (Projectivization.mk ℝ X.rep X.rep_nonzero) :=
        congrArg (projectiveLineParameter carrier) X.mk_rep.symm
      _ = Projectivization.mk ℝ
          (projectiveLineParameterLinearMap carrier X.rep) hmap := by
        rw [projectiveLineParameter, Projectivization.map_mk]
  rw [hparam]
  exact A.arrangementRelativeSign_mk a b
    (projectiveLineParameterLinearMap carrier X.rep) hmap

/-- On a projective line cut by two endpoint supports, equality of the
intrinsic two-support signs is exactly equality of the two cyclic
components.  This is the quotient-safe clean-arc sign classifier. -/
theorem arrangementRelativeSign_eq_iff_projectiveLineCyclic_iff
    (A : FiniteProjectiveLineArrangement Line)
    (carrier : RealProjectiveLine) (a b : Line)
    (P R U V : RealProjectiveOnePoint)
    (hPa : A.Incident (projectiveLineParameter carrier P) a)
    (hPb : ¬ A.Incident (projectiveLineParameter carrier P) b)
    (hRa : ¬ A.Incident (projectiveLineParameter carrier R) a)
    (hRb : A.Incident (projectiveLineParameter carrier R) b)
    (hUa : ¬ A.Incident (projectiveLineParameter carrier U) a)
    (hUb : ¬ A.Incident (projectiveLineParameter carrier U) b)
    (hVa : ¬ A.Incident (projectiveLineParameter carrier V) a)
    (hVb : ¬ A.Incident (projectiveLineParameter carrier V) b) :
    A.arrangementRelativeSign a b (projectiveLineParameter carrier U) =
        A.arrangementRelativeSign a b (projectiveLineParameter carrier V) ↔
      (ProjectiveLineCyclic carrier
          (projectiveLineParameter carrier P)
          (projectiveLineParameter carrier U)
          (projectiveLineParameter carrier R) ↔
        ProjectiveLineCyclic carrier
          (projectiveLineParameter carrier P)
          (projectiveLineParameter carrier V)
          (projectiveLineParameter carrier R)) := by
  let f := (projectiveLineEvaluation (A.projectiveLine a)).comp
    (projectiveLineParameterLinearMap carrier)
  let g := (projectiveLineEvaluation (A.projectiveLine b)).comp
    (projectiveLineParameterLinearMap carrier)
  have heval (X : RealProjectiveOnePoint) (k : Line) :
      projectiveLineEvaluation (A.projectiveLine k)
          (projectiveLineParameterLinearMap carrier X.rep) = 0 ↔
        A.Incident (projectiveLineParameter carrier X) k :=
    A.projectiveLineEvaluation_parameterVector_eq_zero_iff_incident
      carrier k X
  have hfp : f P.rep = 0 := by
    change projectiveLineEvaluation (A.projectiveLine a)
      (projectiveLineParameterLinearMap carrier P.rep) = 0
    exact (heval P a).2 hPa
  have hgr : g R.rep = 0 := by
    change projectiveLineEvaluation (A.projectiveLine b)
      (projectiveLineParameterLinearMap carrier R.rep) = 0
    exact (heval R b).2 hRb
  have hfr : f R.rep ≠ 0 := by
    change projectiveLineEvaluation (A.projectiveLine a)
      (projectiveLineParameterLinearMap carrier R.rep) ≠ 0
    exact (heval R a).not.mpr hRa
  have hgp : g P.rep ≠ 0 := by
    change projectiveLineEvaluation (A.projectiveLine b)
      (projectiveLineParameterLinearMap carrier P.rep) ≠ 0
    exact (heval P b).not.mpr hPb
  have hPR : P ≠ R := by
    intro h
    apply hRa
    simpa only [h] using hPa
  have hPU : P ≠ U := by
    intro h
    apply hUa
    simpa only [← h] using hPa
  have hUR : U ≠ R := by
    intro h
    apply hUb
    simpa only [h] using hRb
  have hPV : P ≠ V := by
    intro h
    apply hVa
    simpa only [← h] using hPa
  have hVR : V ≠ R := by
    intro h
    apply hVb
    simpa only [h] using hRb
  have bracket_ne {X Y : RealProjectiveOnePoint} (hXY : X ≠ Y) :
      realProjectiveBracket X.rep Y.rep ≠ 0 := by
    intro hzero
    apply hXY
    rw [← X.mk_rep, ← Y.mk_rep]
    exact (realProjective_mk_eq_mk_iff_bracket_eq_zero
      X.rep_nonzero Y.rep_nonzero).2 hzero
  have hpr : realProjectiveBracket P.rep R.rep ≠ 0 := bracket_ne hPR
  have hU : realProjectiveTripleBracket P.rep U.rep R.rep ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero (bracket_ne hPU) (bracket_ne hUR))
      (bracket_ne hPR.symm)
  have hV : realProjectiveTripleBracket P.rep V.rep R.rep ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero (bracket_ne hPV) (bracket_ne hVR))
      (bracket_ne hPR.symm)
  have hfu : f U.rep ≠ 0 := by
    change projectiveLineEvaluation (A.projectiveLine a)
      (projectiveLineParameterLinearMap carrier U.rep) ≠ 0
    exact (heval U a).not.mpr hUa
  have hgu : g U.rep ≠ 0 := by
    change projectiveLineEvaluation (A.projectiveLine b)
      (projectiveLineParameterLinearMap carrier U.rep) ≠ 0
    exact (heval U b).not.mpr hUb
  have hfv : f V.rep ≠ 0 := by
    change projectiveLineEvaluation (A.projectiveLine a)
      (projectiveLineParameterLinearMap carrier V.rep) ≠ 0
    exact (heval V a).not.mpr hVa
  have hgv : g V.rep ≠ 0 := by
    change projectiveLineEvaluation (A.projectiveLine b)
      (projectiveLineParameterLinearMap carrier V.rep) ≠ 0
    exact (heval V b).not.mpr hVb
  have hrel (X : RealProjectiveOnePoint) :
      A.arrangementRelativeSign a b (projectiveLineParameter carrier X) =
        SignType.sign (realProjectiveFunctionalPairProduct f g X.rep) := by
    rw [A.arrangementRelativeSign_projectiveLineParameter]
    rfl
  calc
    A.arrangementRelativeSign a b (projectiveLineParameter carrier U) =
        A.arrangementRelativeSign a b (projectiveLineParameter carrier V) ↔
      SignType.sign (realProjectiveFunctionalPairProduct f g U.rep) =
        SignType.sign (realProjectiveFunctionalPairProduct f g V.rep) := by
          rw [hrel U, hrel V]
    _ ↔ 0 < realProjectiveFunctionalPairProduct f g U.rep *
          realProjectiveFunctionalPairProduct f g V.rep :=
      sign_eq_sign_iff_mul_pos (mul_ne_zero hfu hgu) (mul_ne_zero hfv hgv)
    _ ↔ (RealProjectiveCyclic P U R ↔
          RealProjectiveCyclic P V R) :=
      functionalPairProduct_mul_pos_iff_cyclic_iff
        f g P R U V hfp hgr hpr hfr hgp hU hV
    _ ↔ (ProjectiveLineCyclic carrier
          (projectiveLineParameter carrier P)
          (projectiveLineParameter carrier U)
          (projectiveLineParameter carrier R) ↔
        ProjectiveLineCyclic carrier
          (projectiveLineParameter carrier P)
          (projectiveLineParameter carrier V)
          (projectiveLineParameter carrier R)) := by
      rw [projectiveLineCyclic_parameter_iff,
        projectiveLineCyclic_parameter_iff]

namespace OrdinaryAttachmentOuterSectorFront

namespace FelsnerOneLineCleanFrame

variable {A : FiniteProjectiveLineArrangement Line} {l : Line}

private theorem cyclic_middle_ne_left
    {P Q R : RealProjectiveOnePoint} (h : RealProjectiveCyclic P Q R) :
    Q ≠ P := by
  intro hQP
  subst Q
  rw [realProjectiveCyclic_iff_rep_tripleBracket] at h
  simp [realProjectiveTripleBracket] at h

private theorem cyclic_middle_ne_right
    {P Q R : RealProjectiveOnePoint} (h : RealProjectiveCyclic P Q R) :
    Q ≠ R := by
  intro hQR
  subst Q
  rw [realProjectiveCyclic_iff_rep_tripleBracket] at h
  simp [realProjectiveTripleBracket] at h

/-- The unique ordinary point of the degree-one frame, regarded as a marked
cyclic slot of the base line. -/
noncomputable def pSlot (F : FelsnerOneLineCleanFrame A l) :
    A.CircularGapSlot l :=
  F.p.toCircularGapSlot l F.p_on_base

@[simp]
theorem pSlot_val (F : FelsnerOneLineCleanFrame A l) :
    F.pSlot.1 = F.p.1 :=
  rfl

theorem r_away (F : FelsnerOneLineCleanFrame A l) :
    ¬ A.Incident F.r l := by
  intro hrl
  apply F.r_ne_p
  have hr : F.r = A.intersection F.m l :=
    A.eq_intersection_of_incident F.m_ne_base F.r_on_m hrl
  have hp : F.p.1 = A.intersection F.m l :=
    A.eq_intersection_of_incident F.m_ne_base F.p_on_m F.p_on_base
  exact hr.trans hp.symm

theorem q_on_base (F : FelsnerOneLineCleanFrame A l) :
    A.Incident F.q.1 l :=
  ((A.mem_lineVertexSet l).mp F.q.2).2

theorem q_on_n (F : FelsnerOneLineCleanFrame A l) :
    A.Incident F.q.1 F.n := by
  rw [F.q_eq_intersection]
  exact A.intersection_incident_right F.n_ne_base.symm

theorem p_eq_intersection (F : FelsnerOneLineCleanFrame A l) :
    F.p.1 = A.intersection l F.m :=
  A.eq_intersection_of_incident F.m_ne_base.symm
    F.p_on_base F.p_on_m

theorem pSlot_ne_q (F : FelsnerOneLineCleanFrame A l) :
    F.pSlot ≠ F.q := by
  intro h
  exact F.q_ne_p (congrArg Subtype.val h).symm

theorem r_eq_intersection (F : FelsnerOneLineCleanFrame A l) :
    F.r = A.intersection F.m F.n :=
  A.eq_intersection_of_incident F.n_ne_m.symm F.r_on_m F.r_on_n

theorem p_away_n (F : FelsnerOneLineCleanFrame A l) :
    ¬ A.Incident F.p.1 F.n := by
  intro hpN
  have hp : F.p.1 = A.intersection F.m F.n :=
    A.eq_intersection_of_incident F.n_ne_m.symm F.p_on_m hpN
  apply F.r_ne_p
  exact F.r_eq_intersection.trans hp.symm

/-- The three frame supports really form a projective triangle. -/
theorem boundary_nonconcurrent (F : FelsnerOneLineCleanFrame A l) :
    ¬ ∃ x : RealProjectivePoint,
      A.Incident x l ∧ A.Incident x F.m ∧ A.Incident x F.n := by
  rintro ⟨x, hxl, hxm, hxn⟩
  have hx : x = A.intersection F.m F.n :=
    A.eq_intersection_of_incident F.n_ne_m.symm hxm hxn
  apply F.r_away
  rw [F.r_eq_intersection, ← hx]
  exact hxl

theorem cleanEdge_endpointPair (F : FelsnerOneLineCleanFrame A l) :
    ({A.geometricEdgeInitial F.cleanEdge,
        A.geometricEdgeTerminal F.cleanEdge} :
      Finset RealProjectivePoint) = {F.p.1, F.r} := by
  rw [F.cleanEdge_initial, F.cleanEdge_terminal]

/-- A transverse base return, bundled as a marked cyclic slot. -/
noncomputable def baseReturnSlot (F : FelsnerOneLineCleanFrame A l)
    (c : Line) (hlc : l ≠ c) : A.CircularGapSlot l :=
  ⟨A.intersection l c, A.intersection_mem_lineVertexSet_left hlc⟩

@[simp]
theorem baseReturnSlot_val (F : FelsnerOneLineCleanFrame A l)
    (c : Line) (hlc : l ≠ c) :
    (F.baseReturnSlot c hlc).1 = A.intersection l c :=
  rfl

/-- No support transverse to `m` can pass through the open clean edge from
`p` to `r`.  This is the terminal contradiction used by both 5.8 sectors. -/
theorem not_mem_cleanEdgeOpenArc_of_incident_transverse
    (F : FelsnerOneLineCleanFrame A l)
    (x : RealProjectivePoint) (c : Line)
    (hxc : A.Incident x c) (hcm : c ≠ F.m) :
    x ∉ A.geometricEdgeOpenArc F.cleanEdge := by
  intro hxArc
  apply hcm
  have hc :=
    (A.geometricEdgeOpenArc_incident_iff F.cleanEdge hxArc c).mp hxc
  simpa only [F.cleanEdge_line] using hc

/-- An arrangement vertex off the base cannot be the ordinary endpoint or
lie in the open clean edge.  Thus any description of it as belonging to the
closed clean edge collapses to the far endpoint `r`. -/
theorem eq_r_of_mem_vertexSet_of_away_of_mem_cleanEdgeClosure
    (F : FelsnerOneLineCleanFrame A l) (x : RealProjectivePoint)
    (hxVertex : x ∈ A.vertexSet) (hxAway : ¬ A.Incident x l)
    (hxClosure : x = F.p.1 ∨ x = F.r ∨
      x ∈ A.geometricEdgeOpenArc F.cleanEdge) :
    x = F.r := by
  rcases hxClosure with hxp | hxr | hxArc
  · exfalso
    apply hxAway
    rw [hxp]
    exact F.p_on_base
  · exact hxr
  · exact (Set.disjoint_left.mp
      (A.geometricEdgeOpenArc_disjoint_vertexSet F.cleanEdge)
      hxArc hxVertex).elim

/-- A non-pencil clean edge has an honest interior reference point. -/
theorem exists_cleanEdgeReference
    (F : FelsnerOneLineCleanFrame A l) (hA : A.NonPencil) :
    ∃ z : RealProjectivePoint, z ∈ A.geometricEdgeOpenArc F.cleanEdge :=
  (A.isPathConnected_geometricEdgeOpenArc hA F.cleanEdge).nonempty

/-- Every other marked vertex of `m` has the opposite intrinsic `(l,n)`
sign from every point of the clean open edge `p–r`. -/
theorem arrangementRelativeSign_ne_cleanEdgeReference
    (F : FelsnerOneLineCleanFrame A l)
    (z u : RealProjectivePoint)
    (hz : z ∈ A.geometricEdgeOpenArc F.cleanEdge)
    (huVertex : u ∈ A.vertexSet) (huM : A.Incident u F.m)
    (huNeP : u ≠ F.p.1) (huNeR : u ≠ F.r) :
    A.arrangementRelativeSign l F.n u ≠
      A.arrangementRelativeSign l F.n z := by
  let carrier := A.projectiveLine F.m
  let P := circularGapSlotParameter A F.m F.pm
  let R := circularGapSlotParameter A F.m (A.circularGapSuccessor F.m F.pm)
  let U := projectiveLineParameterPreimage carrier u (show u.orthogonal carrier from huM)
  have hzM : A.Incident z F.m := by
    have h := (A.geometricEdgeOpenArc_incident_iff F.cleanEdge hz F.m).2
      F.cleanEdge_line.symm
    exact h
  let Z := projectiveLineParameterPreimage carrier z (show z.orthogonal carrier from hzM)
  have hP : projectiveLineParameter carrier P = F.p.1 := by
    simpa only [carrier, P, F.pm_val] using
      A.projectiveLineParameter_circularGapSlotParameter F.m F.pm
  have hR : projectiveLineParameter carrier R = F.r := by
    simpa only [carrier, R, ← F.r_eq_successor] using
      A.projectiveLineParameter_circularGapSlotParameter F.m
        (A.circularGapSuccessor F.m F.pm)
  have hU : projectiveLineParameter carrier U = u := by
    exact projectiveLineParameter_preimage_spec carrier u huM
  have hZ : projectiveLineParameter carrier Z = z := by
    exact projectiveLineParameter_preimage_spec carrier z hzM
  have huL : ¬ A.Incident u l := by
    intro huL
    have huP : u = F.p.1 := by
      calc
        u = A.intersection l F.m :=
          A.eq_intersection_of_incident F.m_ne_base.symm huL huM
        _ = F.p.1 := F.p_eq_intersection.symm
    exact huNeP huP
  have huN : ¬ A.Incident u F.n := by
    intro huN
    have huR : u = F.r := by
      calc
        u = A.intersection F.m F.n :=
          A.eq_intersection_of_incident F.n_ne_m.symm huM huN
        _ = F.r := F.r_eq_intersection.symm
    exact huNeR huR
  have hzL : ¬ A.Incident z l := by
    intro hzl
    have heq :=
      (A.geometricEdgeOpenArc_incident_iff F.cleanEdge hz l).mp hzl
    exact F.m_ne_base (F.cleanEdge_line.symm.trans heq.symm)
  have hzN : ¬ A.Incident z F.n := by
    intro hzn
    have heq :=
      (A.geometricEdgeOpenArc_incident_iff F.cleanEdge hz F.n).mp hzn
    exact F.n_ne_m (heq.trans F.cleanEdge_line)
  let uSlot : A.CircularGapSlot F.m :=
    ⟨u, (A.mem_lineVertexSet F.m).mpr ⟨huVertex, huM⟩⟩
  have hnotU : ¬ ProjectiveLineCyclic carrier F.p.1 u F.r := by
    have hno := A.circularGapSuccessor_no_line_between F.m F.pm uSlot
    simpa only [carrier, F.pm_val, uSlot, ← F.r_eq_successor] using hno
  have hcyZ : ProjectiveLineCyclic carrier F.p.1 z F.r := by
    change ProjectiveLineCyclic
      (A.projectiveLine (A.edgeSlotLine F.cleanEdge))
        (A.geometricEdgeInitial F.cleanEdge) z
          (A.geometricEdgeTerminal F.cleanEdge) at hz
    simpa only [carrier, F.cleanEdge_line, F.cleanEdge_initial,
      F.cleanEdge_terminal] using hz
  have hrouter :=
    A.arrangementRelativeSign_eq_iff_projectiveLineCyclic_iff
      carrier l F.n P R U Z
      (by simpa only [hP] using F.p_on_base)
      (by simpa only [hP] using F.p_away_n)
      (by simpa only [hR] using F.r_away)
      (by simpa only [hR] using F.r_on_n)
      (by simpa only [hU] using huL)
      (by simpa only [hU] using huN)
      (by simpa only [hZ] using hzL)
      (by simpa only [hZ] using hzN)
  intro hsign
  have hcyIff := hrouter.mp (by simpa only [hU, hZ] using hsign)
  apply hnotU
  simpa only [hP, hU, hR] using
    hcyIff.mpr (by simpa only [hP, hZ, hR] using hcyZ)

/-- A marked base vertex lies strictly in the oriented interval from the
ordinary endpoint `p` to the return endpoint `q`. -/
def InPToQ (F : FelsnerOneLineCleanFrame A l)
    (v : A.CircularGapSlot l) : Prop :=
  RealProjectiveCyclic
    (circularGapSlotParameter A l F.pSlot)
    (circularGapSlotParameter A l v)
    (circularGapSlotParameter A l F.q)

/-- The complementary strict cyclic interval from `q` back to `p`. -/
def InQToP (F : FelsnerOneLineCleanFrame A l)
    (v : A.CircularGapSlot l) : Prop :=
  RealProjectiveCyclic
    (circularGapSlotParameter A l F.q)
    (circularGapSlotParameter A l v)
    (circularGapSlotParameter A l F.pSlot)

theorem InPToQ.ne_pSlot {F : FelsnerOneLineCleanFrame A l}
    {v : A.CircularGapSlot l} (hv : F.InPToQ v) :
    v ≠ F.pSlot := by
  intro h
  apply cyclic_middle_ne_left hv
  rw [h]

theorem InPToQ.ne_q {F : FelsnerOneLineCleanFrame A l}
    {v : A.CircularGapSlot l} (hv : F.InPToQ v) :
    v ≠ F.q := by
  intro h
  apply cyclic_middle_ne_right hv
  rw [h]

theorem InQToP.ne_q {F : FelsnerOneLineCleanFrame A l}
    {v : A.CircularGapSlot l} (hv : F.InQToP v) :
    v ≠ F.q := by
  intro h
  apply cyclic_middle_ne_left hv
  rw [h]

theorem InQToP.ne_pSlot {F : FelsnerOneLineCleanFrame A l}
    {v : A.CircularGapSlot l} (hv : F.InQToP v) :
    v ≠ F.pSlot := by
  intro h
  apply cyclic_middle_ne_right hv
  rw [h]

theorem inPToQ_or_inQToP
    (F : FelsnerOneLineCleanFrame A l) (v : A.CircularGapSlot l)
    (hvp : v ≠ F.pSlot) (hvq : v ≠ F.q) :
    F.InPToQ v ∨ F.InQToP v := by
  exact realProjectiveCyclic_or_reverse
    (circularGapSlotParameter A l F.pSlot)
    (circularGapSlotParameter A l v)
    (circularGapSlotParameter A l F.q)
    ((circularGapSlotParameter_injective A l).ne hvp.symm)
    ((circularGapSlotParameter_injective A l).ne hvq)
    ((circularGapSlotParameter_injective A l).ne F.pSlot_ne_q.symm)

/-- Gauge-invariant scalar which splits the base away from `p = l ∩ m`
and `q = l ∩ n` into its two open sign classes. -/
noncomputable def baseSideProduct (F : FelsnerOneLineCleanFrame A l)
    (v : A.CircularGapSlot l) : ℝ :=
  projectiveLineEvaluation (A.projectiveLine F.m) v.1.rep *
    projectiveLineEvaluation (A.projectiveLine F.n) v.1.rep

/-- Away from the two endpoints the base sign product cannot vanish. -/
theorem baseSideProduct_ne_zero
    (F : FelsnerOneLineCleanFrame A l) (v : A.CircularGapSlot l)
    (hvp : v ≠ F.pSlot) (hvq : v ≠ F.q) :
    F.baseSideProduct v ≠ 0 := by
  have hvBase : A.Incident v.1 l :=
    ((A.mem_lineVertexSet l).mp v.2).2
  have hvNotM : ¬ A.Incident v.1 F.m := by
    intro hvM
    apply hvp
    apply Subtype.ext
    change v.1 = F.p.1
    calc
      v.1 = A.intersection l F.m :=
        A.eq_intersection_of_incident F.m_ne_base.symm hvBase hvM
      _ = F.p.1 := F.p_eq_intersection.symm
  have hvNotN : ¬ A.Incident v.1 F.n := by
    intro hvN
    apply hvq
    apply Subtype.ext
    change v.1 = F.q.1
    calc
      v.1 = A.intersection l F.n :=
        A.eq_intersection_of_incident F.n_ne_base.symm hvBase hvN
      _ = F.q.1 := F.q_eq_intersection.symm
  exact mul_ne_zero
    ((A.projectiveLineEvaluation_rep_eq_zero_iff_incident v.1 F.m).not.mpr
      hvNotM)
    ((A.projectiveLineEvaluation_rep_eq_zero_iff_incident v.1 F.n).not.mpr
      hvNotN)

/-- Every further base vertex belongs to exactly one of the two strict sign
classes; this is the sign-only replacement for the cyclic interval split. -/
theorem baseSideProduct_pos_or_neg
    (F : FelsnerOneLineCleanFrame A l) (v : A.CircularGapSlot l)
    (hvp : v ≠ F.pSlot) (hvq : v ≠ F.q) :
    0 < F.baseSideProduct v ∨ F.baseSideProduct v < 0 := by
  rcases lt_or_gt_of_ne (F.baseSideProduct_ne_zero v hvp hvq) with h | h
  · exact Or.inr h
  · exact Or.inl h

/-- A further marked base vertex together with one of its transverse
supports.  The endpoint inequalities ensure that the support is different
from all three sides of the frame triangle. -/
structure TransverseFront (F : FelsnerOneLineCleanFrame A l)
    (v : A.CircularGapSlot l) where
  v_ne_pSlot : v ≠ F.pSlot
  v_ne_q : v ≠ F.q
  cross : Line
  cross_ne_base : cross ≠ l
  cross_ne_m : cross ≠ F.m
  cross_ne_n : cross ≠ F.n
  v_on_cross : A.Incident v.1 cross

theorem exists_transverseFront
    (F : FelsnerOneLineCleanFrame A l) (v : A.CircularGapSlot l)
    (hvp : v ≠ F.pSlot) (hvq : v ≠ F.q) :
    Nonempty (F.TransverseFront v) := by
  obtain ⟨cross, hcrossBase, hvCross⟩ :=
    CircularGapSlot.exists_incident_line_ne_base A l v
  have hvBase : A.Incident v.1 l :=
    ((A.mem_lineVertexSet l).mp v.2).2
  have hvNotM : ¬ A.Incident v.1 F.m := by
    intro hvM
    apply hvp
    apply Subtype.ext
    change v.1 = F.p.1
    calc
      v.1 = A.intersection l F.m :=
        A.eq_intersection_of_incident F.m_ne_base.symm hvBase hvM
      _ = F.p.1 :=
        (A.eq_intersection_of_incident F.m_ne_base.symm
          F.p_on_base F.p_on_m).symm
  have hvNotN : ¬ A.Incident v.1 F.n := by
    intro hvN
    apply hvq
    apply Subtype.ext
    change v.1 = F.q.1
    calc
      v.1 = A.intersection l F.n :=
        A.eq_intersection_of_incident F.n_ne_base.symm hvBase hvN
      _ = F.q.1 := F.q_eq_intersection.symm
  have hcrossM : cross ≠ F.m := by
    intro h
    apply hvNotM
    simpa only [h] using hvCross
  have hcrossN : cross ≠ F.n := by
    intro h
    apply hvNotN
    simpa only [h] using hvCross
  exact ⟨{
    v_ne_pSlot := hvp
    v_ne_q := hvq
    cross := cross
    cross_ne_base := hcrossBase
    cross_ne_m := hcrossM
    cross_ne_n := hcrossN
    v_on_cross := hvCross
  }⟩

/-- A transverse support chosen away from the third vertex `r` of the
frame triangle.  This removes the zero factor in the Menelaus sign router. -/
structure NondegenerateTransverseFront
    (F : FelsnerOneLineCleanFrame A l) (v : A.CircularGapSlot l)
    extends F.TransverseFront v where
  r_not_on_cross : ¬ A.Incident F.r cross

/-- On a degree-one base, a further marked point has a transverse support
which misses `r`.  If an arbitrary transverse support passes through `r`,
the return has multiplicity at least three, and its third support cannot
also pass through `r`. -/
theorem exists_nondegenerateTransverseFront
    (F : FelsnerOneLineCleanFrame A l)
    (hone : A.lineOrdinaryVertexDegree l = 1)
    (v : A.CircularGapSlot l)
    (hvp : v ≠ F.pSlot) (hvq : v ≠ F.q) :
    Nonempty (F.NondegenerateTransverseFront v) := by
  obtain ⟨cross, hcrossBase, hvCross⟩ :=
    CircularGapSlot.exists_incident_line_ne_base A l v
  have hvBase : A.Incident v.1 l :=
    ((A.mem_lineVertexSet l).mp v.2).2
  have hvNeP : v.1 ≠ F.p.1 := by
    intro h
    apply hvp
    apply Subtype.ext
    exact h
  have hvNotM : ¬ A.Incident v.1 F.m := by
    intro hvM
    apply hvNeP
    calc
      v.1 = A.intersection l F.m :=
        A.eq_intersection_of_incident F.m_ne_base.symm hvBase hvM
      _ = F.p.1 := F.p_eq_intersection.symm
  have hvNotN : ¬ A.Incident v.1 F.n := by
    intro hvN
    apply hvq
    apply Subtype.ext
    change v.1 = F.q.1
    calc
      v.1 = A.intersection l F.n :=
        A.eq_intersection_of_incident F.n_ne_base.symm hvBase hvN
      _ = F.q.1 := F.q_eq_intersection.symm
  have build : ∀ (c : Line), c ≠ l → ¬ A.Incident F.r c →
      A.Incident v.1 c → Nonempty (F.NondegenerateTransverseFront v) := by
    intro c hcBase hrNotC hvC
    have hcM : c ≠ F.m := by
      intro h
      apply hvNotM
      simpa only [h] using hvC
    have hcN : c ≠ F.n := by
      intro h
      apply hvNotN
      simpa only [h] using hvC
    exact ⟨{
      toTransverseFront := {
        v_ne_pSlot := hvp
        v_ne_q := hvq
        cross := c
        cross_ne_base := hcBase
        cross_ne_m := hcM
        cross_ne_n := hcN
        v_on_cross := hvC
      }
      r_not_on_cross := hrNotC
    }⟩
  by_cases hrCross : A.Incident F.r cross
  · have hvEq : v.1 = A.intersection l cross :=
      A.eq_intersection_of_incident hcrossBase.symm hvBase hvCross
    have hreturnNe : A.intersection l cross ≠ F.p.1 := by
      simpa only [← hvEq] using hvNeP
    have hthreeInt : 3 ≤ A.multiplicity (A.intersection l cross) :=
      A.three_le_multiplicity_base_return_of_lineDegree_eq_one_of_ne
        l cross hone hcrossBase.symm F.p F.p_on_base hreturnNe
    have hthree : 3 ≤ A.multiplicity v.1 := by
      simpa only [hvEq] using hthreeInt
    obtain ⟨d, hdBase, hdCross, hvD⟩ :=
      A.exists_third_incident_line_of_three_le_multiplicity
        v.1 l cross hcrossBase.symm hvBase hvCross hthree
    have hrNotD : ¬ A.Incident F.r d := by
      intro hrD
      have hvInt : v.1 = A.intersection cross d :=
        A.eq_intersection_of_incident hdCross.symm hvCross hvD
      have hrInt : F.r = A.intersection cross d :=
        A.eq_intersection_of_incident hdCross.symm hrCross hrD
      have hvr : v.1 = F.r := hvInt.trans hrInt.symm
      apply F.r_away
      rw [← hvr]
      exact hvBase
    exact build d hdBase hrNotD hvD
  · exact build cross hcrossBase hrCross hvCross

namespace TransverseFront

variable {F : FelsnerOneLineCleanFrame A l}
  {v : A.CircularGapSlot l}

noncomputable def leftWitness (T : F.TransverseFront v) :
    RealProjectivePoint :=
  A.intersection F.m T.cross

noncomputable def rightWitness (T : F.TransverseFront v) :
    RealProjectivePoint :=
  A.intersection T.cross F.n

theorem leftWitness_mem_vertexSet (T : F.TransverseFront v) :
    T.leftWitness ∈ A.vertexSet :=
  A.intersection_mem_vertexSet T.cross_ne_m.symm

theorem rightWitness_mem_vertexSet (T : F.TransverseFront v) :
    T.rightWitness ∈ A.vertexSet :=
  A.intersection_mem_vertexSet T.cross_ne_n

theorem leftWitness_incident_m (T : F.TransverseFront v) :
    A.Incident T.leftWitness F.m :=
  A.intersection_incident_left T.cross_ne_m.symm

theorem leftWitness_incident_cross (T : F.TransverseFront v) :
    A.Incident T.leftWitness T.cross :=
  A.intersection_incident_right T.cross_ne_m.symm

theorem rightWitness_incident_cross (T : F.TransverseFront v) :
    A.Incident T.rightWitness T.cross :=
  A.intersection_incident_left T.cross_ne_n

theorem rightWitness_incident_n (T : F.TransverseFront v) :
    A.Incident T.rightWitness F.n :=
  A.intersection_incident_right T.cross_ne_n

theorem rightWitness_eq_intersection_n_cross (T : F.TransverseFront v) :
    T.rightWitness = A.intersection F.n T.cross :=
  A.eq_intersection_of_incident T.cross_ne_n.symm
    T.rightWitness_incident_n T.rightWitness_incident_cross

/-- The transverse support through `v` misses the ordinary endpoint `p`. -/
theorem p_not_on_cross (T : F.TransverseFront v) :
    ¬ A.Incident F.p.1 T.cross := by
  intro hpCross
  apply T.v_ne_pSlot
  apply Subtype.ext
  change v.1 = F.p.1
  have hvBase : A.Incident v.1 l :=
    ((A.mem_lineVertexSet l).mp v.2).2
  calc
    v.1 = A.intersection l T.cross :=
      A.eq_intersection_of_incident T.cross_ne_base.symm
        hvBase T.v_on_cross
    _ = F.p.1 :=
      (A.eq_intersection_of_incident T.cross_ne_base.symm
        F.p_on_base hpCross).symm

theorem leftWitness_ne_p (T : F.TransverseFront v) :
    T.leftWitness ≠ F.p.1 := by
  intro h
  apply T.p_not_on_cross
  rw [← h]
  exact T.leftWitness_incident_cross

/-- The same support misses the other base endpoint `q`. -/
theorem q_not_on_cross (T : F.TransverseFront v) :
    ¬ A.Incident F.q.1 T.cross := by
  intro hqCross
  apply T.v_ne_q
  apply Subtype.ext
  change v.1 = F.q.1
  have hvBase : A.Incident v.1 l :=
    ((A.mem_lineVertexSet l).mp v.2).2
  calc
    v.1 = A.intersection l T.cross :=
      A.eq_intersection_of_incident T.cross_ne_base.symm
        hvBase T.v_on_cross
    _ = F.q.1 :=
      (A.eq_intersection_of_incident T.cross_ne_base.symm
        F.q_on_base hqCross).symm

/-- The base side-product computed from the selected transversal is
literally the intrinsic sign-class value of its marked return `v`. -/
theorem intersectionPairEvaluation_base_eq
    (T : F.TransverseFront v) :
    A.intersectionPairEvaluation l T.cross F.m F.n =
      F.baseSideProduct v := by
  have hvBase : A.Incident v.1 l :=
    ((A.mem_lineVertexSet l).mp v.2).2
  have hvEq : v.1 = A.intersection l T.cross :=
    A.eq_intersection_of_incident T.cross_ne_base.symm
      hvBase T.v_on_cross
  unfold intersectionPairEvaluation baseSideProduct
  rw [← hvEq]

theorem leftWitness_away (T : F.TransverseFront v) :
    ¬ A.Incident T.leftWitness l := by
  intro hbase
  have huP : T.leftWitness = F.p.1 := by
    calc
      T.leftWitness = A.intersection l F.m :=
        A.eq_intersection_of_incident F.m_ne_base.symm
          hbase T.leftWitness_incident_m
      _ = F.p.1 :=
        (A.eq_intersection_of_incident F.m_ne_base.symm
          F.p_on_base F.p_on_m).symm
  have hvBase : A.Incident v.1 l :=
    ((A.mem_lineVertexSet l).mp v.2).2
  have huV : T.leftWitness = v.1 := by
    calc
      T.leftWitness = A.intersection l T.cross :=
        A.eq_intersection_of_incident T.cross_ne_base.symm
          hbase T.leftWitness_incident_cross
      _ = v.1 :=
        (A.eq_intersection_of_incident T.cross_ne_base.symm
          hvBase T.v_on_cross).symm
  apply T.v_ne_pSlot
  apply Subtype.ext
  exact huV.symm.trans huP

theorem rightWitness_away (T : F.TransverseFront v) :
    ¬ A.Incident T.rightWitness l := by
  intro hbase
  have huQ : T.rightWitness = F.q.1 := by
    calc
      T.rightWitness = A.intersection l F.n :=
        A.eq_intersection_of_incident F.n_ne_base.symm
          hbase T.rightWitness_incident_n
      _ = F.q.1 := F.q_eq_intersection.symm
  have hvBase : A.Incident v.1 l :=
    ((A.mem_lineVertexSet l).mp v.2).2
  have huV : T.rightWitness = v.1 := by
    calc
      T.rightWitness = A.intersection l T.cross :=
        A.eq_intersection_of_incident T.cross_ne_base.symm
          hbase T.rightWitness_incident_cross
      _ = v.1 :=
        (A.eq_intersection_of_incident T.cross_ne_base.symm
          hvBase T.v_on_cross).symm
  apply T.v_ne_q
  apply Subtype.ext
  exact huV.symm.trans huQ

noncomputable def leftSigma (T : F.TransverseFront v) : Line → Bool :=
  A.closedSectorSignPatternAt T.leftWitness

noncomputable def rightSigma (T : F.TransverseFront v) : Line → Bool :=
  A.closedSectorSignPatternAt T.rightWitness

theorem leftSector_nonempty (T : F.TransverseFront v) :
    (A.triangleSectorOffBaseVertexSet T.leftSigma l F.m F.n).Nonempty := by
  classical
  refine ⟨T.leftWitness, Finset.mem_filter.mpr ?_⟩
  exact ⟨T.leftWitness_mem_vertexSet,
    A.projectivePointMemTriangleSector_closedSectorSignPatternAt
      T.leftWitness l F.m F.n, T.leftWitness_away⟩

theorem rightSector_nonempty (T : F.TransverseFront v) :
    (A.triangleSectorOffBaseVertexSet T.rightSigma l F.m F.n).Nonempty := by
  classical
  refine ⟨T.rightWitness, Finset.mem_filter.mpr ?_⟩
  exact ⟨T.rightWitness_mem_vertexSet,
    A.projectivePointMemTriangleSector_closedSectorSignPatternAt
      T.rightWitness l F.m F.n, T.rightWitness_away⟩

end TransverseFront

namespace NondegenerateTransverseFront

variable {F : FelsnerOneLineCleanFrame A l}
  {v : A.CircularGapSlot l}

theorem leftWitness_ne_r (T : F.NondegenerateTransverseFront v) :
    T.toTransverseFront.leftWitness ≠ F.r := by
  intro h
  apply T.r_not_on_cross
  rw [← h]
  exact T.toTransverseFront.leftWitness_incident_cross

/-- The transversal misses the vertex `m ∩ n`, in raw homogeneous form. -/
theorem raw_cross_away_mn (T : F.NondegenerateTransverseFront v) :
    (A.projectiveLine T.cross).rep ⬝ᵥ
        crossProduct (A.projectiveLine F.m).rep
          (A.projectiveLine F.n).rep ≠ 0 := by
  apply (A.projectiveLineRep_dot_rawIntersection_ne_zero_iff
    F.n_ne_m.symm).2
  simpa only [← F.r_eq_intersection] using T.r_not_on_cross

/-- The endpoint inequality `v ≠ q` supplies the second nonzero Menelaus
factor. -/
theorem raw_cross_away_nl (T : F.NondegenerateTransverseFront v) :
    (A.projectiveLine T.cross).rep ⬝ᵥ
        crossProduct (A.projectiveLine F.n).rep
          (A.projectiveLine l).rep ≠ 0 := by
  apply (A.projectiveLineRep_dot_rawIntersection_ne_zero_iff
    F.n_ne_base).2
  have hq : F.q.1 = A.intersection F.n l :=
    A.eq_intersection_of_incident F.n_ne_base F.q_on_n F.q_on_base
  simpa only [← hq] using T.toTransverseFront.q_not_on_cross

/-- The endpoint inequality `v ≠ p` supplies the last nonzero Menelaus
factor. -/
theorem raw_cross_away_lm (T : F.NondegenerateTransverseFront v) :
    (A.projectiveLine T.cross).rep ⬝ᵥ
        crossProduct (A.projectiveLine l).rep
          (A.projectiveLine F.m).rep ≠ 0 := by
  apply (A.projectiveLineRep_dot_rawIntersection_ne_zero_iff
    F.m_ne_base.symm).2
  simpa only [← F.p_eq_intersection] using
    T.toTransverseFront.p_not_on_cross

/-- Arrangement-level strict Menelaus parity for the nondegenerate
transversal through `v`. -/
theorem raw_sideProducts_mul_neg
    (T : F.NondegenerateTransverseFront v) :
    (((crossProduct (A.projectiveLine l).rep
          (A.projectiveLine T.cross).rep ⬝ᵥ
            (A.projectiveLine F.m).rep) *
        (crossProduct (A.projectiveLine l).rep
          (A.projectiveLine T.cross).rep ⬝ᵥ
            (A.projectiveLine F.n).rep)) *
      ((crossProduct (A.projectiveLine F.m).rep
          (A.projectiveLine T.cross).rep ⬝ᵥ
            (A.projectiveLine l).rep) *
        (crossProduct (A.projectiveLine F.m).rep
          (A.projectiveLine T.cross).rep ⬝ᵥ
            (A.projectiveLine F.n).rep))) *
      ((crossProduct (A.projectiveLine F.n).rep
          (A.projectiveLine T.cross).rep ⬝ᵥ
            (A.projectiveLine l).rep) *
        (crossProduct (A.projectiveLine F.n).rep
          (A.projectiveLine T.cross).rep ⬝ᵥ
            (A.projectiveLine F.m).rep)) < 0 :=
  triangleCrossing_sideProducts_mul_neg
    (A.projectiveLine l).rep (A.projectiveLine F.m).rep
      (A.projectiveLine F.n).rep (A.projectiveLine T.cross).rep
        T.raw_cross_away_mn T.raw_cross_away_nl T.raw_cross_away_lm

/-- The same strict Menelaus parity, now on the canonical representatives
of the three actual arrangement intersections. -/
theorem intersectionSideProducts_mul_neg
    (T : F.NondegenerateTransverseFront v) :
    ((A.intersectionPairEvaluation l T.cross F.m F.n *
        A.intersectionPairEvaluation F.m T.cross l F.n) *
      A.intersectionPairEvaluation F.n T.cross l F.m) < 0 := by
  obtain ⟨a, ha, hbase⟩ :=
    A.intersectionPairEvaluation_eq_posSq_mul_raw T.cross_ne_base.symm
      (other₀ := F.m) (other₁ := F.n)
  obtain ⟨b, hb, hm⟩ :=
    A.intersectionPairEvaluation_eq_posSq_mul_raw T.cross_ne_m.symm
      (other₀ := l) (other₁ := F.n)
  obtain ⟨c, hc, hn⟩ :=
    A.intersectionPairEvaluation_eq_posSq_mul_raw T.cross_ne_n.symm
      (other₀ := l) (other₁ := F.m)
  rw [hbase, hm, hn]
  have hfactor : 0 < a ^ 2 * b ^ 2 * c ^ 2 :=
    mul_pos (mul_pos ha hb) hc
  have hraw := T.raw_sideProducts_mul_neg
  change
    0 > (((a ^ 2 * triangleCrossingSideProduct
          (A.projectiveLine l).rep (A.projectiveLine F.m).rep
            (A.projectiveLine F.n).rep (A.projectiveLine T.cross).rep) *
        (b ^ 2 * triangleCrossingSideProduct
          (A.projectiveLine F.m).rep (A.projectiveLine l).rep
            (A.projectiveLine F.n).rep (A.projectiveLine T.cross).rep)) *
      (c ^ 2 * triangleCrossingSideProduct
        (A.projectiveLine F.n).rep (A.projectiveLine l).rep
          (A.projectiveLine F.m).rep (A.projectiveLine T.cross).rep))
  rw [show
    (((a ^ 2 * triangleCrossingSideProduct
          (A.projectiveLine l).rep (A.projectiveLine F.m).rep
            (A.projectiveLine F.n).rep (A.projectiveLine T.cross).rep) *
        (b ^ 2 * triangleCrossingSideProduct
          (A.projectiveLine F.m).rep (A.projectiveLine l).rep
            (A.projectiveLine F.n).rep (A.projectiveLine T.cross).rep)) *
      (c ^ 2 * triangleCrossingSideProduct
        (A.projectiveLine F.n).rep (A.projectiveLine l).rep
          (A.projectiveLine F.m).rep (A.projectiveLine T.cross).rep)) =
      (a ^ 2 * b ^ 2 * c ^ 2) *
        ((triangleCrossingSideProduct
            (A.projectiveLine l).rep (A.projectiveLine F.m).rep
              (A.projectiveLine F.n).rep (A.projectiveLine T.cross).rep *
          triangleCrossingSideProduct
            (A.projectiveLine F.m).rep (A.projectiveLine l).rep
              (A.projectiveLine F.n).rep (A.projectiveLine T.cross).rep) *
          triangleCrossingSideProduct
            (A.projectiveLine F.n).rep (A.projectiveLine l).rep
              (A.projectiveLine F.m).rep (A.projectiveLine T.cross).rep) by ring]
  exact mul_neg_of_pos_of_neg hfactor hraw

/-- Simultaneously orienting the three triangle covectors does not change
Menelaus parity: every orientation sign occurs exactly twice. -/
theorem orientedIntersectionSideProducts_mul_neg
    (T : F.NondegenerateTransverseFront v) (sigma : Line → Bool) :
    ((A.orientedIntersectionPairEvaluation sigma l T.cross F.m F.n *
        A.orientedIntersectionPairEvaluation sigma F.m T.cross l F.n) *
      A.orientedIntersectionPairEvaluation sigma F.n T.cross l F.m) < 0 := by
  have hraw := T.intersectionSideProducts_mul_neg
  have heq :
      ((A.orientedIntersectionPairEvaluation sigma l T.cross F.m F.n *
          A.orientedIntersectionPairEvaluation sigma F.m T.cross l F.n) *
        A.orientedIntersectionPairEvaluation sigma F.n T.cross l F.m) =
      ((A.intersectionPairEvaluation l T.cross F.m F.n *
          A.intersectionPairEvaluation F.m T.cross l F.n) *
        A.intersectionPairEvaluation F.n T.cross l F.m) := by
    by_cases hl : sigma l <;> by_cases hm : sigma F.m <;>
      by_cases hn : sigma F.n <;>
      simp [orientedIntersectionPairEvaluation, intersectionPairEvaluation,
        arrangementOrientedEvaluation, hl, hm, hn] <;> ring
  rw [heq]
  exact hraw

/-- Fully oriented canonical sign router. -/
theorem orientedNSide_neg_iff_orientedBase_mul_mSide_pos
    (T : F.NondegenerateTransverseFront v) (sigma : Line → Bool) :
    A.orientedIntersectionPairEvaluation sigma F.n T.cross l F.m < 0 ↔
      0 < A.orientedIntersectionPairEvaluation sigma l T.cross F.m F.n *
        A.orientedIntersectionPairEvaluation sigma F.m T.cross l F.n := by
  have hneg := T.orientedIntersectionSideProducts_mul_neg sigma
  rcases mul_neg_iff.mp hneg with h | h
  · exact iff_of_true h.2 h.1
  · exact iff_of_false (not_lt_of_ge h.2.le) (not_lt_of_ge h.1.le)

/-- Canonical arrangement-level sign router: the return on side `n` has
negative two-side sign exactly when the base return and the return on `m`
have equal signs. -/
theorem nSide_neg_iff_base_mul_mSide_pos
    (T : F.NondegenerateTransverseFront v) :
    A.intersectionPairEvaluation F.n T.cross l F.m < 0 ↔
      0 < A.intersectionPairEvaluation l T.cross F.m F.n *
        A.intersectionPairEvaluation F.m T.cross l F.n := by
  let rawBase := triangleCrossingSideProduct
    (A.projectiveLine l).rep (A.projectiveLine F.m).rep
      (A.projectiveLine F.n).rep (A.projectiveLine T.cross).rep
  let rawM := triangleCrossingSideProduct
    (A.projectiveLine F.m).rep (A.projectiveLine l).rep
      (A.projectiveLine F.n).rep (A.projectiveLine T.cross).rep
  let rawN := triangleCrossingSideProduct
    (A.projectiveLine F.n).rep (A.projectiveLine l).rep
      (A.projectiveLine F.m).rep (A.projectiveLine T.cross).rep
  have hnNeg :
      A.intersectionPairEvaluation F.n T.cross l F.m < 0 ↔ rawN < 0 := by
    simpa only [rawN] using
      (A.intersectionPairEvaluation_neg_iff_raw T.cross_ne_n.symm)
  have hbasePos :
      0 < A.intersectionPairEvaluation l T.cross F.m F.n ↔ 0 < rawBase := by
    simpa only [rawBase] using
      (A.intersectionPairEvaluation_pos_iff_raw T.cross_ne_base.symm)
  have hbaseNeg :
      A.intersectionPairEvaluation l T.cross F.m F.n < 0 ↔ rawBase < 0 := by
    simpa only [rawBase] using
      (A.intersectionPairEvaluation_neg_iff_raw T.cross_ne_base.symm)
  have hmPos :
      0 < A.intersectionPairEvaluation F.m T.cross l F.n ↔ 0 < rawM := by
    simpa only [rawM] using
      (A.intersectionPairEvaluation_pos_iff_raw T.cross_ne_m.symm)
  have hmNeg :
      A.intersectionPairEvaluation F.m T.cross l F.n < 0 ↔ rawM < 0 := by
    simpa only [rawM] using
      (A.intersectionPairEvaluation_neg_iff_raw T.cross_ne_m.symm)
  have hmenelaus : rawN < 0 ↔ 0 < rawBase * rawM := by
    simpa only [rawBase, rawM, rawN] using
      (triangleCrossing_thirdSideProduct_neg_iff
        (A.projectiveLine l).rep (A.projectiveLine F.m).rep
          (A.projectiveLine F.n).rep (A.projectiveLine T.cross).rep
            T.raw_cross_away_mn T.raw_cross_away_nl T.raw_cross_away_lm)
  calc
    A.intersectionPairEvaluation F.n T.cross l F.m < 0 ↔
        rawN < 0 := hnNeg
    _ ↔ 0 < rawBase * rawM := hmenelaus
    _ ↔ 0 < A.intersectionPairEvaluation l T.cross F.m F.n *
          A.intersectionPairEvaluation F.m T.cross l F.n := by
      constructor
      · intro h
        rcases mul_pos_iff.mp h with h | h
        · exact mul_pos (hbasePos.mpr h.1) (hmPos.mpr h.2)
        · exact mul_pos_of_neg_of_neg
            (hbaseNeg.mpr h.1) (hmNeg.mpr h.2)
      · intro h
        rcases mul_pos_iff.mp h with h | h
        · exact mul_pos (hbasePos.mp h.1) (hmPos.mp h.2)
        · exact mul_pos_of_neg_of_neg
            (hbaseNeg.mp h.1) (hmNeg.mp h.2)

/-- In the positive base sign class, the `n`-side test is negative exactly
when the `m`-side test is positive. -/
theorem nSide_neg_iff_mSide_pos_of_base_pos
    (T : F.NondegenerateTransverseFront v)
    (hbase : 0 < F.baseSideProduct v) :
    A.intersectionPairEvaluation F.n T.cross l F.m < 0 ↔
      0 < A.intersectionPairEvaluation F.m T.cross l F.n := by
  calc
    A.intersectionPairEvaluation F.n T.cross l F.m < 0 ↔
        0 < A.intersectionPairEvaluation l T.cross F.m F.n *
          A.intersectionPairEvaluation F.m T.cross l F.n :=
      T.nSide_neg_iff_base_mul_mSide_pos
    _ ↔ 0 < F.baseSideProduct v *
          A.intersectionPairEvaluation F.m T.cross l F.n := by
      rw [T.toTransverseFront.intersectionPairEvaluation_base_eq]
    _ ↔ 0 < A.intersectionPairEvaluation F.m T.cross l F.n :=
      mul_pos_iff_of_pos_left hbase

/-- In the negative base sign class, both other side tests have the same
negative sign. -/
theorem nSide_neg_iff_mSide_neg_of_base_neg
    (T : F.NondegenerateTransverseFront v)
    (hbase : F.baseSideProduct v < 0) :
    A.intersectionPairEvaluation F.n T.cross l F.m < 0 ↔
      A.intersectionPairEvaluation F.m T.cross l F.n < 0 := by
  rw [T.nSide_neg_iff_base_mul_mSide_pos,
    T.toTransverseFront.intersectionPairEvaluation_base_eq]
  constructor
  · intro h
    rcases mul_pos_iff.mp h with h | h
    · exact (not_lt_of_ge hbase.le h.1).elim
    · exact h.2
  · intro h
    exact mul_pos_of_neg_of_neg hbase h

end NondegenerateTransverseFront

/-- The exact two-way case split used in Figure 5.8: either both open base
intervals contain a further marked vertex, or at least one complementary
interval contains none.  No cyclic information is discarded. -/
inductive IntervalDichotomy (F : FelsnerOneLineCleanFrame A l) : Type
  | twoSided
      (pToQ : ∃ v : A.CircularGapSlot l, F.InPToQ v)
      (qToP : ∃ v : A.CircularGapSlot l, F.InQToP v)
  | oneSided
      (empty : (∀ v : A.CircularGapSlot l, ¬ F.InPToQ v) ∨
        (∀ v : A.CircularGapSlot l, ¬ F.InQToP v))

/-- Every clean degree-one frame has the lossless Figure 5.8 interval
dichotomy. -/
noncomputable def intervalDichotomy (F : FelsnerOneLineCleanFrame A l) :
    F.IntervalDichotomy := by
  classical
  by_cases hpq : ∃ v : A.CircularGapSlot l, F.InPToQ v
  · by_cases hqp : ∃ v : A.CircularGapSlot l, F.InQToP v
    · exact IntervalDichotomy.twoSided hpq hqp
    · exact IntervalDichotomy.oneSided
        (Or.inr (not_exists.mp hqp))
  · exact IntervalDichotomy.oneSided
      (Or.inl (not_exists.mp hpq))

/-- The two concrete sector fronts selected by the two cases of Figure 5.8.
In the two-sided case both witnesses lie on `m`; in the one-sided case the
two sides of one transverse triangle are retained together with the empty
complementary interval. -/
inductive SectorPairFront (F : FelsnerOneLineCleanFrame A l)
  | twoSided {u v : A.CircularGapSlot l}
      (hu : F.InPToQ u) (hv : F.InQToP v)
      (Tu : F.TransverseFront u) (Tv : F.TransverseFront v)
  | pToQOnly {u : A.CircularGapSlot l}
      (hu : F.InPToQ u) (T : F.TransverseFront u)
      (emptyReverse : ∀ v : A.CircularGapSlot l, ¬ F.InQToP v)
  | qToPOnly {v : A.CircularGapSlot l}
      (hv : F.InQToP v) (T : F.TransverseFront v)
      (emptyForward : ∀ u : A.CircularGapSlot l, ¬ F.InPToQ u)

/-- A clean frame on a base with at least three marked vertices produces
the full lossless Figure 5.8 sector-pair front. -/
theorem exists_sectorPairFront
    (F : FelsnerOneLineCleanFrame A l)
    (hthree : 3 ≤ Fintype.card (A.CircularGapSlot l)) :
    Nonempty F.SectorPairFront := by
  classical
  rcases F.intervalDichotomy with ⟨hpq, hqp⟩ | ⟨hempty⟩
  · obtain ⟨u, hu⟩ := hpq
    obtain ⟨v, hv⟩ := hqp
    obtain ⟨Tu⟩ := F.exists_transverseFront u hu.ne_pSlot hu.ne_q
    obtain ⟨Tv⟩ := F.exists_transverseFront v hv.ne_pSlot hv.ne_q
    exact ⟨SectorPairFront.twoSided hu hv Tu Tv⟩
  · obtain ⟨w, hwp, hwq⟩ :=
      A.exists_circularGapSlot_val_ne_pair_of_three_le
        l hthree F.pSlot F.q F.q_ne_p.symm
    have hwpSlot : w ≠ F.pSlot := by
      intro h
      exact hwp (congrArg Subtype.val h)
    have hwqSlot : w ≠ F.q := by
      intro h
      exact hwq (congrArg Subtype.val h)
    obtain ⟨T⟩ := F.exists_transverseFront w hwpSlot hwqSlot
    rcases hempty with hforwardEmpty | hreverseEmpty
    · rcases F.inPToQ_or_inQToP w hwpSlot hwqSlot with hw | hw
      · exact (hforwardEmpty w hw).elim
      · exact ⟨SectorPairFront.qToPOnly hw T hforwardEmpty⟩
    · rcases F.inPToQ_or_inQToP w hwpSlot hwqSlot with hw | hw
      · exact ⟨SectorPairFront.pToQOnly hw T hreverseEmpty⟩
      · exact (hreverseEmpty w hw).elim

/-- The pair of concrete nonempty triangle sectors underlying a Figure 5.8
front.  Both use the ordered sides `(m,n)`, so the unique ordinary point
`p = l ∩ m` is always their left base endpoint. -/
structure SectorPair (F : FelsnerOneLineCleanFrame A l) where
  firstSigma : Line → Bool
  secondSigma : Line → Bool
  first_nonempty :
    (A.triangleSectorOffBaseVertexSet firstSigma l F.m F.n).Nonempty
  second_nonempty :
    (A.triangleSectorOffBaseVertexSet secondSigma l F.m F.n).Nonempty

noncomputable def SectorPairFront.toSectorPair
    {F : FelsnerOneLineCleanFrame A l} (G : F.SectorPairFront) :
    F.SectorPair := by
  cases G with
  | twoSided hu hv Tu Tv =>
      exact {
        firstSigma := Tu.leftSigma
        secondSigma := Tv.leftSigma
        first_nonempty := Tu.leftSector_nonempty
        second_nonempty := Tv.leftSector_nonempty
      }
  | pToQOnly hu T hempty =>
      exact {
        firstSigma := T.leftSigma
        secondSigma := T.rightSigma
        first_nonempty := T.leftSector_nonempty
        second_nonempty := T.rightSector_nonempty
      }
  | qToPOnly hv T hempty =>
      exact {
        firstSigma := T.leftSigma
        secondSigma := T.rightSigma
        first_nonempty := T.leftSector_nonempty
        second_nonempty := T.rightSector_nonempty
      }

theorem exists_sectorPair
    (F : FelsnerOneLineCleanFrame A l)
    (hthree : 3 ≤ Fintype.card (A.CircularGapSlot l)) :
    Nonempty F.SectorPair := by
  obtain ⟨G⟩ := F.exists_sectorPairFront hthree
  exact ⟨G.toSectorPair⟩

end FelsnerOneLineCleanFrame

variable {A : FiniteProjectiveLineArrangement Line}
  {q : A.OrdinaryVertex} {l : Line}

/-- One-call lossless degree-one Figure 5.8 extractor. -/
theorem exists_felsnerOneLineSectorPairFront_of_lineDegree_eq_one
    (A : FiniteProjectiveLineArrangement Line) (hA : A.NonPencil)
    (l : Line) (hone : A.lineOrdinaryVertexDegree l = 1)
    (hthree : 3 ≤ Fintype.card (A.CircularGapSlot l)) :
    ∃ F : FelsnerOneLineCleanFrame A l, Nonempty F.SectorPairFront := by
  obtain ⟨F⟩ :=
    exists_felsnerOneLineCleanFrame_of_lineDegree_eq_one A hA l hone
  exact ⟨F, F.exists_sectorPairFront hthree⟩

/-- One-call nonempty-sector projection of the lossless extractor. -/
theorem exists_felsnerOneLineSectorPair_of_lineDegree_eq_one
    (A : FiniteProjectiveLineArrangement Line) (hA : A.NonPencil)
    (l : Line) (hone : A.lineOrdinaryVertexDegree l = 1)
    (hthree : 3 ≤ Fintype.card (A.CircularGapSlot l)) :
    ∃ F : FelsnerOneLineCleanFrame A l, Nonempty F.SectorPair := by
  obtain ⟨F, hF⟩ :=
    exists_felsnerOneLineSectorPairFront_of_lineDegree_eq_one
      A hA l hone hthree
  obtain ⟨G⟩ := hF
  exact ⟨F, ⟨G.toSectorPair⟩⟩

/-- A closed sign sector containing the first transverse witness.  This raw
word is used only for nonemptiness; comparisons between the two raw words
would require a common projective gauge. -/
noncomputable def leftWitnessSigma
    (F : OrdinaryAttachmentOuterSectorFront A q l) : Line → Bool :=
  A.closedSectorSignPatternAt F.leftWitness

/-- A closed sign sector containing the second transverse witness. -/
noncomputable def rightWitnessSigma
    (F : OrdinaryAttachmentOuterSectorFront A q l) : Line → Bool :=
  A.closedSectorSignPatternAt F.rightWitness

theorem leftWitness_mem_sector
    (F : OrdinaryAttachmentOuterSectorFront A q l) :
    A.projectivePointMemTriangleSector F.leftWitnessSigma
      l F.frame.a F.frame.b F.leftWitness := by
  exact A.projectivePointMemTriangleSector_closedSectorSignPatternAt
    F.leftWitness l F.frame.a F.frame.b

theorem rightWitness_mem_sector
    (F : OrdinaryAttachmentOuterSectorFront A q l) :
    A.projectivePointMemTriangleSector F.rightWitnessSigma
      l F.frame.a F.frame.b F.rightWitness := by
  exact A.projectivePointMemTriangleSector_closedSectorSignPatternAt
    F.rightWitness l F.frame.a F.frame.b

/-- The first raw witness sector of the original triple is nonempty. -/
theorem leftSector_nonempty
    (F : OrdinaryAttachmentOuterSectorFront A q l) :
    (A.triangleSectorOffBaseVertexSet
      F.leftWitnessSigma l F.frame.a F.frame.b).Nonempty := by
  classical
  refine ⟨F.leftWitness, Finset.mem_filter.mpr ?_⟩
  exact ⟨F.leftWitness_mem_vertexSet,
    F.leftWitness_mem_sector, F.leftWitness_away⟩

/-- The second raw witness sector of the original triple is nonempty. -/
theorem rightSector_nonempty
    (F : OrdinaryAttachmentOuterSectorFront A q l) :
    (A.triangleSectorOffBaseVertexSet
      F.rightWitnessSigma l F.frame.a F.frame.b).Nonempty := by
  classical
  refine ⟨F.rightWitness, Finset.mem_filter.mpr ?_⟩
  exact ⟨F.rightWitness_mem_vertexSet,
    F.rightWitness_mem_sector, F.rightWitness_away⟩

/-- A common-gauge sign word for the initial attached face. -/
noncomputable def attachmentFaceSigma
    (F : OrdinaryAttachmentOuterSectorFront A q l) : Line → Bool :=
  A.arrangementFaceSignPattern l F.attachment.face

/-- The actual outer chamber across the literal side supported by `a` is
obtained by flipping exactly that coordinate of the initial face word. -/
noncomputable def leftOuterSigma
    (F : OrdinaryAttachmentOuterSectorFront A q l) : Line → Bool := fun k =>
  if k = F.frame.a then Bool.not (F.attachmentFaceSigma k)
  else F.attachmentFaceSigma k

/-- The actual outer chamber across the literal side supported by `b`. -/
noncomputable def rightOuterSigma
    (F : OrdinaryAttachmentOuterSectorFront A q l) : Line → Bool := fun k =>
  if k = F.frame.b then Bool.not (F.attachmentFaceSigma k)
  else F.attachmentFaceSigma k

@[simp]
theorem leftOuterSigma_left
    (F : OrdinaryAttachmentOuterSectorFront A q l) :
    F.leftOuterSigma F.frame.a =
      Bool.not (F.attachmentFaceSigma F.frame.a) := by
  simp [leftOuterSigma]

@[simp]
theorem rightOuterSigma_right
    (F : OrdinaryAttachmentOuterSectorFront A q l) :
    F.rightOuterSigma F.frame.b =
      Bool.not (F.attachmentFaceSigma F.frame.b) := by
  simp [rightOuterSigma]

theorem leftOuterSigma_eq_face_of_ne
    (F : OrdinaryAttachmentOuterSectorFront A q l)
    {k : Line} (hk : k ≠ F.frame.a) :
    F.leftOuterSigma k = F.attachmentFaceSigma k := by
  simp [leftOuterSigma, hk]

theorem rightOuterSigma_eq_face_of_ne
    (F : OrdinaryAttachmentOuterSectorFront A q l)
    {k : Line} (hk : k ≠ F.frame.b) :
    F.rightOuterSigma k = F.attachmentFaceSigma k := by
  simp [rightOuterSigma, hk]

theorem leftOuterSigma_right
    (F : OrdinaryAttachmentOuterSectorFront A q l) :
    F.leftOuterSigma F.frame.b =
      F.attachmentFaceSigma F.frame.b := by
  exact F.leftOuterSigma_eq_face_of_ne F.frame.a_ne_b.symm

theorem rightOuterSigma_left
    (F : OrdinaryAttachmentOuterSectorFront A q l) :
    F.rightOuterSigma F.frame.a =
      F.attachmentFaceSigma F.frame.a := by
  exact F.rightOuterSigma_eq_face_of_ne F.frame.a_ne_b

theorem outerSigma_eq_on_base
    (F : OrdinaryAttachmentOuterSectorFront A q l) :
    F.leftOuterSigma l = F.rightOuterSigma l := by
  rw [F.leftOuterSigma_eq_face_of_ne F.frame.a_ne_base.symm,
    F.rightOuterSigma_eq_face_of_ne F.frame.b_ne_base.symm]

theorem orientedEvaluation_outerSigma_eq_on_base
    (F : OrdinaryAttachmentOuterSectorFront A q l)
    (v : Fin 3 → ℝ) :
    A.arrangementOrientedEvaluation F.leftOuterSigma l v =
      A.arrangementOrientedEvaluation F.rightOuterSigma l v := by
  unfold arrangementOrientedEvaluation
  rw [F.outerSigma_eq_on_base]

theorem orientedEvaluation_leftOuter_eq_neg_right_at_left
    (F : OrdinaryAttachmentOuterSectorFront A q l)
    (v : Fin 3 → ℝ) :
    A.arrangementOrientedEvaluation F.leftOuterSigma F.frame.a v =
      -A.arrangementOrientedEvaluation F.rightOuterSigma F.frame.a v := by
  cases h : F.attachmentFaceSigma F.frame.a <;>
    simp [arrangementOrientedEvaluation, leftOuterSigma, rightOuterSigma,
      F.frame.a_ne_b, h]

theorem orientedEvaluation_leftOuter_eq_neg_right_at_right
    (F : OrdinaryAttachmentOuterSectorFront A q l)
    (v : Fin 3 → ℝ) :
    A.arrangementOrientedEvaluation F.leftOuterSigma F.frame.b v =
      -A.arrangementOrientedEvaluation F.rightOuterSigma F.frame.b v := by
  cases h : F.attachmentFaceSigma F.frame.b <;>
    simp [arrangementOrientedEvaluation, leftOuterSigma, rightOuterSigma,
      F.frame.a_ne_b.symm, h]

/-- The two canonical outer closed sectors meet away from the base only at
the original attachment apex. -/
theorem eq_attachment_of_mem_both_outerSectors
    (F : OrdinaryAttachmentOuterSectorFront A q l)
    (x : RealProjectivePoint)
    (hxLeft : A.projectivePointMemTriangleSector F.leftOuterSigma
      l F.frame.a F.frame.b x)
    (hxRight : A.projectivePointMemTriangleSector F.rightOuterSigma
      l F.frame.a F.frame.b x)
    (hxBase : ¬ A.Incident x l) :
    x = q.1 := by
  have hincOfZero (k : Line)
      (hk : A.arrangementOrientedEvaluation F.leftOuterSigma k x.rep = 0) :
      A.Incident x k := by
    have h :=
      (A.incident_projectivization_mk_iff_orientedEvaluation_eq_zero
        F.leftOuterSigma k x.rep x.rep_nonzero).2 hk
    simpa only [x.mk_rep] using h
  have hfinish (hxa : A.Incident x F.frame.a)
      (hxb : A.Incident x F.frame.b) : x = q.1 := by
    have hx : x = A.intersection F.frame.a F.frame.b :=
      A.eq_intersection_of_incident F.frame.a_ne_b hxa hxb
    have hq : q.1 = A.intersection F.frame.a F.frame.b :=
      A.eq_intersection_of_incident F.frame.a_ne_b
        F.frame.q_on_a F.frame.q_on_b
    exact hx.trans hq.symm
  rcases hxLeft with hL | hL
  · rcases hxRight with hR | hR
    · have hLa := hL F.frame.a (by simp)
      have hRa := hR F.frame.a (by simp)
      have hLb := hL F.frame.b (by simp)
      have hRb := hR F.frame.b (by simp)
      have haRel :=
        F.orientedEvaluation_leftOuter_eq_neg_right_at_left x.rep
      have hbRel :=
        F.orientedEvaluation_leftOuter_eq_neg_right_at_right x.rep
      have ha0 : A.arrangementOrientedEvaluation
          F.leftOuterSigma F.frame.a x.rep = 0 := by
        linarith
      have hb0 : A.arrangementOrientedEvaluation
          F.leftOuterSigma F.frame.b x.rep = 0 := by
        linarith
      exact hfinish (hincOfZero F.frame.a ha0)
        (hincOfZero F.frame.b hb0)
    · have hLl := hL l (by simp)
      have hRl := hR l (by simp)
      rw [LinearMap.map_neg,
        ← F.orientedEvaluation_outerSigma_eq_on_base x.rep] at hRl
      have hl0 : A.arrangementOrientedEvaluation
          F.leftOuterSigma l x.rep = 0 := by
        linarith
      exact (hxBase (hincOfZero l hl0)).elim
  · rcases hxRight with hR | hR
    · have hLl := hL l (by simp)
      have hRl := hR l (by simp)
      rw [LinearMap.map_neg] at hLl
      rw [← F.orientedEvaluation_outerSigma_eq_on_base x.rep] at hRl
      have hl0 : A.arrangementOrientedEvaluation
          F.leftOuterSigma l x.rep = 0 := by
        linarith
      exact (hxBase (hincOfZero l hl0)).elim
    · have hLa := hL F.frame.a (by simp)
      have hRa := hR F.frame.a (by simp)
      have hLb := hL F.frame.b (by simp)
      have hRb := hR F.frame.b (by simp)
      have haRel :=
        F.orientedEvaluation_leftOuter_eq_neg_right_at_left (-x.rep)
      have hbRel :=
        F.orientedEvaluation_leftOuter_eq_neg_right_at_right (-x.rep)
      have haNeg0 : A.arrangementOrientedEvaluation
          F.leftOuterSigma F.frame.a (-x.rep) = 0 := by
        linarith
      have hbNeg0 : A.arrangementOrientedEvaluation
          F.leftOuterSigma F.frame.b (-x.rep) = 0 := by
        linarith
      have ha0 : A.arrangementOrientedEvaluation
          F.leftOuterSigma F.frame.a x.rep = 0 := by
        rw [LinearMap.map_neg] at haNeg0
        linarith
      have hb0 : A.arrangementOrientedEvaluation
          F.leftOuterSigma F.frame.b x.rep = 0 := by
        rw [LinearMap.map_neg] at hbNeg0
        linarith
      exact hfinish (hincOfZero F.frame.a ha0)
        (hincOfZero F.frame.b hb0)

theorem leftWitness_ne_attachment
    (F : OrdinaryAttachmentOuterSectorFront A q l) :
    F.leftWitness ≠ q.1 := by
  intro huq
  have hqCross : A.Incident q.1 F.cross := by
    rw [← huq]
    exact F.leftWitness_incident_cross
  have hqTwo : A.multiplicity q.1 = 2 :=
    (Finset.mem_filter.mp q.2).2
  have hexact := A.incident_iff_eq_or_eq_of_multiplicity_eq_two
    q.1 F.frame.a F.frame.b F.frame.q_on_a F.frame.q_on_b
      F.frame.a_ne_b.symm hqTwo F.cross
  rcases hexact.mp hqCross with h | h
  · exact F.cross_ne_left h
  · exact F.cross_ne_right h

theorem rightWitness_ne_attachment
    (F : OrdinaryAttachmentOuterSectorFront A q l) :
    F.rightWitness ≠ q.1 := by
  intro huq
  have hqCross : A.Incident q.1 F.cross := by
    rw [← huq]
    exact F.rightWitness_incident_cross
  have hqTwo : A.multiplicity q.1 = 2 :=
    (Finset.mem_filter.mp q.2).2
  have hexact := A.incident_iff_eq_or_eq_of_multiplicity_eq_two
    q.1 F.frame.a F.frame.b F.frame.q_on_a F.frame.q_on_b
      F.frame.a_ne_b.symm hqTwo F.cross
  rcases hexact.mp hqCross with h | h
  · exact F.cross_ne_left h
  · exact F.cross_ne_right h

theorem leftWitness_ne_rightWitness
    (F : OrdinaryAttachmentOuterSectorFront A q l) :
    F.leftWitness ≠ F.rightWitness := by
  intro hur
  apply F.leftWitness_ne_attachment
  have huRight : A.Incident F.leftWitness F.frame.b := by
    rw [hur]
    exact F.rightWitness_incident_right
  have hu : F.leftWitness = A.intersection F.frame.a F.frame.b :=
    A.eq_intersection_of_incident F.frame.a_ne_b
      F.leftWitness_incident_left huRight
  have hq : q.1 = A.intersection F.frame.a F.frame.b :=
    A.eq_intersection_of_incident F.frame.a_ne_b
      F.frame.q_on_a F.frame.q_on_b
  exact hu.trans hq.symm

end OrdinaryAttachmentOuterSectorFront

end FiniteProjectiveLineArrangement

end Erdos506.Incidence
