import Erdos506.Incidence.RealProjectiveArrangementKellyMoserOuterFinal
import Erdos506.Incidence.RealProjectiveArrangementKellyMoserDegreeOneOuterSectorFinish

/-!
# The one-attachment degree-one Kelly endpoint

This downstream leaf consumes one canonical clean-edge sector.  The local
minimizer is separated from the far apex before return closure is invoked,
so the producer's logically necessary apex exception is harmless.
-/

namespace Erdos506.Incidence

open scoped LinearAlgebra.Projectivization

namespace FiniteProjectiveLineArrangement

variable {Line : Type*} [Fintype Line] [DecidableEq Line]

/-- An ordinary local minimizer whose support returns remain in the outer
sector cuts out a literal attachment triangle. -/
theorem ordinaryVertexAttachedToLine_of_sector_minimal_and_returns
    (A : FiniteProjectiveLineArrangement Line) (hA : A.NonPencil)
    (outerSigma : Line → Bool) (l outerLeft outerRight : Line)
    (houterTriangle : ¬ ∃ r : RealProjectivePoint,
      A.Incident r l ∧ A.Incident r outerLeft ∧
        A.Incident r outerRight)
    (q : A.OrdinaryVertex)
    (hqOuter : A.projectivePointMemTriangleSector
      outerSigma l outerLeft outerRight q.1)
    (hql : ¬ A.Incident q.1 l)
    (hreturn : ∀ c : Line, A.Incident q.1 c → l ≠ c →
      A.projectivePointMemTriangleSector outerSigma l outerLeft outerRight
        (A.intersection l c))
    (hmin : ∀ y : RealProjectivePoint, y ∈ A.vertexSet →
      A.projectivePointMemTriangleSector
        outerSigma l outerLeft outerRight y →
      ¬ A.Incident y l →
      A.vertexChartLineHeight
          (A.triangleSectorFixedGauge
            outerSigma l outerLeft outerRight) l q.1 ≤
        A.vertexChartLineHeight
          (A.triangleSectorFixedGauge
            outerSigma l outerLeft outerRight) l y) :
    A.OrdinaryVertexAttachedToLine q l := by
  classical
  obtain ⟨a, b, hab, hordinary⟩ :=
    A.exists_two_lines_incident_iff_of_ordinaryVertex q
  have hqa : A.Incident q.1 a := (hordinary a).2 (Or.inl rfl)
  have hqb : A.Incident q.1 b := (hordinary b).2 (Or.inr rfl)
  have hal : a ≠ l := fun h => hql (h ▸ hqa)
  have hbl : b ≠ l := fun h => hql (h ▸ hqb)
  have hsubTriangle := A.not_three_concurrent_of_offBase_apex
    q.1 l a b hab hqa hqb hql
  let fixedGauge :=
    A.triangleSectorFixedGauge outerSigma l outerLeft outerRight
  have hfq : fixedGauge q.1.rep ≠ 0 := by
    simpa only [fixedGauge, A.triangleSectorFixedGauge_apply] using
      A.triangleSectorGauge_ne_zero_of_projective outerSigma l outerLeft
        outerRight houterTriangle q.1 hqOuter
  have hV1Outer := hreturn a hqa hal.symm
  have hV3Outer := hreturn b hqb hbl.symm
  have hfV1 : fixedGauge (A.intersection l a).rep ≠ 0 := by
    simpa only [fixedGauge, A.triangleSectorFixedGauge_apply] using
      A.triangleSectorGauge_ne_zero_of_projective outerSigma l outerLeft
        outerRight houterTriangle (A.intersection l a) hV1Outer
  have hfV3 : fixedGauge (A.intersection l b).rep ≠ 0 := by
    simpa only [fixedGauge, A.triangleSectorFixedGauge_apply] using
      A.triangleSectorGauge_ne_zero_of_projective outerSigma l outerLeft
        outerRight houterTriangle (A.intersection l b) hV3Outer
  let X := vertexChartNormalizedVector fixedGauge q.1
  let V1 := vertexChartNormalizedVector fixedGauge (A.intersection l a)
  let V3 := vertexChartNormalizedVector fixedGauge (A.intersection l b)
  have hV1notB : ¬ A.Incident (A.intersection l a) b :=
    A.not_incident_intersection_base_support_of_offBase_apex
      q.1 l a b hal.symm hab hqa hqb hql
  have hV3notA : ¬ A.Incident (A.intersection l b) a :=
    A.not_incident_intersection_base_support_of_offBase_apex
      q.1 l b a hbl.symm hab.symm hqb hqa hql
  have hV1raw : projectiveLineEvaluation (A.projectiveLine b) V1 ≠ 0 := by
    simpa only [V1, arrangementOrientedEvaluation, if_true] using
      A.arrangementOrientedEvaluation_vertexChartNormalizedVector_ne_zero
        (fun _ => true) fixedGauge hfV1 hV1notB
  have hV3raw : projectiveLineEvaluation (A.projectiveLine a) V3 ≠ 0 := by
    simpa only [V3, arrangementOrientedEvaluation, if_true] using
      A.arrangementOrientedEvaluation_vertexChartNormalizedVector_ne_zero
        (fun _ => true) fixedGauge hfV3 hV3notA
  let sigma : Line → Bool := fun k =>
    if k = a then
      decide (0 < projectiveLineEvaluation (A.projectiveLine a) V3)
    else if k = b then
      decide (0 < projectiveLineEvaluation (A.projectiveLine b) V1)
    else outerSigma k
  have hxNorm : X ∈ A.arrangementClosedSignConeOn outerSigma
      {l, outerLeft, outerRight} := by
    simpa only [X, fixedGauge,
      A.vertexChartNormalizedVector_triangleSectorFixedGauge] using
      A.triangleSectorNormalizedVector_mem_of_projective
        outerSigma l outerLeft outerRight houterTriangle q.1 hqOuter
  have hXbaseOuter : 0 < A.arrangementOrientedEvaluation outerSigma l X := by
    have hge := hxNorm l (by simp)
    have hne : A.arrangementOrientedEvaluation outerSigma l X ≠ 0 := by
      simpa only [X] using
        A.arrangementOrientedEvaluation_vertexChartNormalizedVector_ne_zero
          outerSigma fixedGauge hfq hql
    exact lt_of_le_of_ne hge hne.symm
  have hXbase : 0 < A.arrangementOrientedEvaluation sigma l X := by
    simpa [sigma, hal.symm, hbl.symm, arrangementOrientedEvaluation] using
      hXbaseOuter
  have hV1right : 0 < A.arrangementOrientedEvaluation sigma b V1 := by
    by_cases hpos : 0 < projectiveLineEvaluation (A.projectiveLine b) V1
    · simp [sigma, hab.symm, arrangementOrientedEvaluation, hpos]
    · have hneg : projectiveLineEvaluation (A.projectiveLine b) V1 < 0 :=
        lt_of_le_of_ne (le_of_not_gt hpos) hV1raw
      simp [sigma, hab.symm, arrangementOrientedEvaluation, hpos, hneg]
  have hV3left : 0 < A.arrangementOrientedEvaluation sigma a V3 := by
    by_cases hpos : 0 < projectiveLineEvaluation (A.projectiveLine a) V3
    · simp [sigma, arrangementOrientedEvaluation, hpos]
    · have hneg : projectiveLineEvaluation (A.projectiveLine a) V3 < 0 :=
        lt_of_le_of_ne (le_of_not_gt hpos) hV3raw
      simp [sigma, arrangementOrientedEvaluation, hpos, hneg]
  have hV1OuterNorm : V1 ∈ A.arrangementClosedSignConeOn outerSigma
      {l, outerLeft, outerRight} := by
    simpa only [V1, fixedGauge,
      A.vertexChartNormalizedVector_triangleSectorFixedGauge] using
      A.triangleSectorNormalizedVector_mem_of_projective
        outerSigma l outerLeft outerRight houterTriangle
          (A.intersection l a) hV1Outer
  have hV3OuterNorm : V3 ∈ A.arrangementClosedSignConeOn outerSigma
      {l, outerLeft, outerRight} := by
    simpa only [V3, fixedGauge,
      A.vertexChartNormalizedVector_triangleSectorFixedGauge] using
      A.triangleSectorNormalizedVector_mem_of_projective
        outerSigma l outerLeft outerRight houterTriangle
          (A.intersection l b) hV3Outer
  have hnozero :=
    A.noAdditionalZero_of_minimal_fixedChartLineHeight_in_triangleSector
      sigma outerSigma fixedGauge q l a b l outerLeft outerRight
      hsubTriangle hal.symm hbl.symm hab hql hqa hqb hordinary
      hfq hfV1 hfV3 hXbase hV1right hV3left
      hxNorm hV1OuterNorm hV3OuterNorm hmin
  exact A.ordinaryVertexAttachedToLine_of_noZero_oriented_subtriangle
    hA fixedGauge q l a b sigma hal hbl hab hql hqa hqb hordinary
    hfq hfV1 hfV3 hXbase hV1right hV3left hnozero

namespace OrdinaryAttachmentOuterSectorFront

namespace FelsnerOneLineCleanFrame
namespace CleanEdgeSectorReference

variable {A : FiniteProjectiveLineArrangement Line} {l : Line}
  {F : FelsnerOneLineCleanFrame A l}
  {G : F.CleanEdgeSectorReference}

/-- The exceptional-apex return router suffices for the local minimizer:
the retained right-side witness has strictly smaller height than the apex. -/
theorem OneCanonicalSectorFront.exists_ordinaryAttachment
    (S : G.OneCanonicalSectorFront) (hA : A.NonPencil)
    (hone : A.lineOrdinaryVertexDegree l = 1) :
    ∃ q : A.OrdinaryVertex, A.OrdinaryVertexAttachedToLine q l := by
  classical
  obtain ⟨x, hxVertex, hxSector, hxl, _hxpos, hmin⟩ :=
    A.exists_minimal_originalTriangleGaugeLineHeight
      S.sectorSigma l F.m F.n F.boundary_nonconcurrent S.sector_nonempty
  have hwlt := A.vertexChartLineHeight_lt_apex_of_mem_right_side
    S.sectorSigma l F.m F.n F.boundary_nonconcurrent
      S.transverse.toTransverseFront.rightWitness F.r S.witness_mem
      S.witness_not_incident_m
      S.transverse.toTransverseFront.rightWitness_incident_n
      F.r_on_m F.r_on_n
  have hxNeR : x ≠ F.r :=
    A.ne_of_triangleSector_minimal_of_lower_witness
      S.sectorSigma l F.m F.n x F.r
        S.transverse.toTransverseFront.rightWitness hmin
        S.transverse.toTransverseFront.rightWitness_mem_vertexSet
        S.witness_mem S.transverse.toTransverseFront.rightWitness_away hwlt
  have hxreturn : ∀ c : Line, A.Incident x c → l ≠ c →
      A.projectivePointMemTriangleSector S.sectorSigma l F.m F.n
        (A.intersection l c) :=
    S.return_mem_of_ne_r x hxVertex hxSector hxl hxNeR
  have hx2 := A.multiplicity_eq_two_of_local_triangle_minimal
    S.sectorSigma l F.m F.n F.boundary_nonconcurrent
      x hxVertex hxSector hxl hxreturn (by
        intro left middle right hxleft hxmiddle hxright
          hlleft hlmiddle hlright h12 _h23
        have hleftSector := hxreturn left hxleft hlleft
        exact A.exists_extra_line_at_sector_middle_of_lineDegree_eq_one
          S.sectorSigma l F.m F.n left middle hone
            F.m_ne_base.symm hlmiddle F.p F.p_on_base
            F.p_eq_intersection F.boundary_nonconcurrent hleftSector h12)
      hmin
  let q : A.OrdinaryVertex :=
    ⟨x, Finset.mem_filter.mpr ⟨hxVertex, hx2⟩⟩
  have hattach := A.ordinaryVertexAttachedToLine_of_sector_minimal_and_returns
    hA S.sectorSigma l F.m F.n F.boundary_nonconcurrent q
      hxSector hxl hxreturn hmin
  exact ⟨q, hattach⟩

end CleanEdgeSectorReference
end FelsnerOneLineCleanFrame

end OrdinaryAttachmentOuterSectorFront

/-- Felsner's degree-one branch in the strength needed by the finite
eleven-line fallback: every high degree-one base has one actual ordinary
attachment. -/
theorem one_le_lineOrdinaryAttachmentDegree_of_degree_one_highLine
    (A : FiniteProjectiveLineArrangement Line) (hA : A.NonPencil)
    (l : Line) (hthree : 3 ≤ (A.lineVertexSet l).card)
    (hone : A.lineOrdinaryVertexDegree l = 1) :
    1 ≤ A.lineOrdinaryAttachmentDegree l := by
  classical
  have hslotCard : Fintype.card (A.CircularGapSlot l) =
      (A.lineVertexSet l).card :=
    Fintype.card_coe (A.lineVertexSet l)
  have hslot : 3 ≤ Fintype.card (A.CircularGapSlot l) := by
    rw [hslotCard]
    exact hthree
  obtain ⟨F⟩ :=
    OrdinaryAttachmentOuterSectorFront.exists_felsnerOneLineCleanFrame_of_lineDegree_eq_one
      A hA l hone
  obtain ⟨G⟩ := F.exists_cleanEdgeSectorReference hA
  obtain ⟨S⟩ := G.exists_oneCanonicalSectorFront hone hslot
  obtain ⟨q, hq⟩ := S.exists_ordinaryAttachment hA hone
  unfold lineOrdinaryAttachmentDegree finiteRelationRightDegree
  have hsub : ({q} : Finset A.OrdinaryVertex) ⊆
      Finset.univ.filter fun x => A.OrdinaryVertexAttachedToLine x l := by
    intro x hx
    simp only [Finset.mem_singleton] at hx
    subst x
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hq⟩
  calc
    1 = ({q} : Finset A.OrdinaryVertex).card := by simp
    _ ≤ (Finset.univ.filter fun x =>
        A.OrdinaryVertexAttachedToLine x l).card :=
      Finset.card_le_card hsub

end FiniteProjectiveLineArrangement

end Erdos506.Incidence
