import Erdos506.Incidence.RealProjectiveArrangementKellyMoserThreeClauseFinish
import Erdos506.Incidence.RealProjectiveArrangementKellyMoserLocalFixedChartExit
import Erdos506.Incidence.RealProjectiveArrangementKellyMoserOuterSector
import Erdos506.Incidence.RealProjectiveArrangementKellyMoserOuterSectorCanonicalFinish
import Erdos506.Incidence.RealProjectiveArrangementKellyMoserDegreeOneMedian
import Erdos506.Incidence.RealProjectiveArrangementKellyMoserLowLine
import Erdos506.Incidence.RealPlaneKellyMoserDualCensus

/-!
# Unconditional Kelly--Moser outer routing

This leaf turns the sign-cone Three-Clause into the literal linewise
attachments used by the Kelly--Rottenberg count, then transports the
arrangement inequality back to labelled real-plane configurations.
-/

namespace Erdos506.Incidence

open scoped LinearAlgebra.Projectivization

namespace FiniteProjectiveLineArrangement

variable {Line : Type*} [Fintype Line] [DecidableEq Line]

/-- A globally closest ordinary vertex, in a chart whose base evaluation is
positive at that vertex, cuts out its own literal empty attachment triangle. -/
theorem ordinaryVertexAttachedToLine_of_global_minimal_base_pos
    (A : FiniteProjectiveLineArrangement Line) (hA : A.NonPencil)
    (fixedGauge : (Fin 3 → ℝ) →ₗ[ℝ] ℝ)
    (q : A.OrdinaryVertex) (l : Line)
    (hgauge : ∀ r : RealProjectivePoint, r ∈ A.vertexSet →
      fixedGauge r.rep ≠ 0)
    (hqaway : ¬ A.Incident q.1 l)
    (hbasePos : 0 < projectiveLineEvaluation (A.projectiveLine l)
      (vertexChartNormalizedVector fixedGauge q.1))
    (hmin : ∀ y : RealProjectivePoint, y ∈ A.vertexSet →
      ¬ A.Incident y l →
      A.vertexChartLineHeight fixedGauge l q.1 ≤
        A.vertexChartLineHeight fixedGauge l y) :
    A.OrdinaryVertexAttachedToLine q l := by
  classical
  obtain ⟨a, b, hab, hordinary⟩ :=
    A.exists_two_lines_incident_iff_of_ordinaryVertex q
  have hqa : A.Incident q.1 a := (hordinary a).2 (Or.inl rfl)
  have hqb : A.Incident q.1 b := (hordinary b).2 (Or.inr rfl)
  have hal : a ≠ l := fun h => hqaway (h ▸ hqa)
  have hbl : b ≠ l := fun h => hqaway (h ▸ hqb)
  have htriangle := A.not_three_concurrent_of_offBase_apex
    q.1 l a b hab hqa hqb hqaway
  have hfq := hgauge q.1 (Finset.mem_filter.mp q.2).1
  have hfV1 := hgauge (A.intersection l a)
    (A.intersection_mem_vertexSet hal.symm)
  have hfV3 := hgauge (A.intersection l b)
    (A.intersection_mem_vertexSet hbl.symm)
  let X := vertexChartNormalizedVector fixedGauge q.1
  let V1 := vertexChartNormalizedVector fixedGauge (A.intersection l a)
  let V3 := vertexChartNormalizedVector fixedGauge (A.intersection l b)
  have hV1notB : ¬ A.Incident (A.intersection l a) b :=
    A.not_incident_intersection_base_support_of_offBase_apex
      q.1 l a b hal.symm hab hqa hqb hqaway
  have hV3notA : ¬ A.Incident (A.intersection l b) a :=
    A.not_incident_intersection_base_support_of_offBase_apex
      q.1 l b a hbl.symm hab.symm hqb hqa hqaway
  have hV1raw : projectiveLineEvaluation (A.projectiveLine b) V1 ≠ 0 := by
    simpa only [V1, arrangementOrientedEvaluation, if_true] using
      A.arrangementOrientedEvaluation_vertexChartNormalizedVector_ne_zero
        (fun _ => true) fixedGauge hfV1 hV1notB
  have hV3raw : projectiveLineEvaluation (A.projectiveLine a) V3 ≠ 0 := by
    simpa only [V3, arrangementOrientedEvaluation, if_true] using
      A.arrangementOrientedEvaluation_vertexChartNormalizedVector_ne_zero
        (fun _ => true) fixedGauge hfV3 hV3notA
  let sigma := A.emptyTriangleSignPattern a b V1 V3
  have hXbase : 0 < A.arrangementOrientedEvaluation sigma l X := by
    simpa [sigma, emptyTriangleSignPattern, hal.symm, hbl.symm,
      arrangementOrientedEvaluation, X] using hbasePos
  have hV1right : 0 < A.arrangementOrientedEvaluation sigma b V1 := by
    by_cases hpos : 0 < projectiveLineEvaluation (A.projectiveLine b) V1
    · simp [sigma, emptyTriangleSignPattern, hab.symm,
        arrangementOrientedEvaluation, hpos]
    · have hneg : projectiveLineEvaluation (A.projectiveLine b) V1 < 0 :=
        lt_of_le_of_ne (le_of_not_gt hpos) hV1raw
      simp [sigma, emptyTriangleSignPattern, hab.symm,
        arrangementOrientedEvaluation, hpos, hneg]
  have hV3left : 0 < A.arrangementOrientedEvaluation sigma a V3 := by
    by_cases hpos : 0 < projectiveLineEvaluation (A.projectiveLine a) V3
    · simp [sigma, emptyTriangleSignPattern,
        arrangementOrientedEvaluation, hpos]
    · have hneg : projectiveLineEvaluation (A.projectiveLine a) V3 < 0 :=
        lt_of_le_of_ne (le_of_not_gt hpos) hV3raw
      simp [sigma, emptyTriangleSignPattern,
        arrangementOrientedEvaluation, hpos, hneg]
  have hXleft : A.arrangementOrientedEvaluation sigma a X = 0 := by
    simpa only [X] using
      A.arrangementOrientedEvaluation_vertexChartNormalizedVector_eq_zero
        sigma fixedGauge hfq hqa
  have hXright : A.arrangementOrientedEvaluation sigma b X = 0 := by
    simpa only [X] using
      A.arrangementOrientedEvaluation_vertexChartNormalizedVector_eq_zero
        sigma fixedGauge hfq hqb
  have hV1base : A.arrangementOrientedEvaluation sigma l V1 = 0 := by
    simpa only [V1] using
      A.arrangementOrientedEvaluation_vertexChartNormalizedVector_eq_zero
        sigma fixedGauge hfV1 (A.intersection_incident_left hal.symm)
  have hV1left : A.arrangementOrientedEvaluation sigma a V1 = 0 := by
    simpa only [V1] using
      A.arrangementOrientedEvaluation_vertexChartNormalizedVector_eq_zero
        sigma fixedGauge hfV1 (A.intersection_incident_right hal.symm)
  have hV3base : A.arrangementOrientedEvaluation sigma l V3 = 0 := by
    simpa only [V3] using
      A.arrangementOrientedEvaluation_vertexChartNormalizedVector_eq_zero
        sigma fixedGauge hfV3 (A.intersection_incident_left hbl.symm)
  have hV3right : A.arrangementOrientedEvaluation sigma b V3 = 0 := by
    simpa only [V3] using
      A.arrangementOrientedEvaluation_vertexChartNormalizedVector_eq_zero
        sigma fixedGauge hfV3 (A.intersection_incident_right hbl.symm)
  have hnozero := A.noAdditionalZero_of_minimal_fixedChartLineHeight
    sigma fixedGauge q l a b htriangle hal.symm hbl.symm hab
    hqaway hqa hqb hordinary hfq hfV1 hfV3
    hXbase hV1right hV3left hmin
  let K : Finset Line := {l, a, b}
  let U := X + V1 + V3
  have hU : U ∈ A.arrangementSignConeOn sigma K := by
    intro k hk
    simp only [K, Finset.mem_insert, Finset.mem_singleton] at hk
    rcases hk with rfl | rfl | rfl
    · simpa only [U, LinearMap.map_add, hV1base, hV3base,
        add_zero] using hXbase
    · simpa only [U, LinearMap.map_add, hXleft, hV1left,
        zero_add] using hV3left
    · simpa only [U, LinearMap.map_add, hXright, hV3right,
        zero_add, add_zero] using hV1right
  have hU0 : U ≠ 0 := by
    intro hzero
    have := hU l (by simp [K])
    rw [hzero, LinearMap.map_zero] at this
    exact (lt_irrefl 0 this)
  obtain ⟨p, hp⟩ := A.exists_arrangementComplement_of_no_additional_zero
    sigma K U hU0 hU (fun m hm => hnozero m (by simpa only [K] using hm) U hU)
  have hUbase : 0 < projectiveLineEvaluation (A.projectiveLine l) U := by
    have := hU l (by simp [K])
    simpa [sigma, emptyTriangleSignPattern, hal.symm, hbl.symm,
      arrangementOrientedEvaluation] using this
  have hnorm := A.arrangementNormalizedRepresentative_eq_of_projectivization_mk
    l p hU0 hUbase.ne' hp.symm
  have heqOn := A.arrangementPointSignPattern_eq_on_of_normalized_eq_pos_smul
    l p sigma K U
      (projectiveLineEvaluation (A.projectiveLine l) U)⁻¹
      (inv_pos.mpr hUbase) hnorm hU
  let tau := A.arrangementPointSignPattern l p
  have heval (k : Line) (hk : k ∈ K) :
      A.arrangementOrientedEvaluation tau k =
        A.arrangementOrientedEvaluation sigma k := by
    unfold arrangementOrientedEvaluation
    rw [show tau k = sigma k by exact heqOn k hk]
  have hXbase' : 0 < A.arrangementOrientedEvaluation tau l X := by
    rw [heval l (by simp [K])]
    exact hXbase
  have hV1right' : 0 < A.arrangementOrientedEvaluation tau b V1 := by
    rw [heval b (by simp [K])]
    exact hV1right
  have hV3left' : 0 < A.arrangementOrientedEvaluation tau a V3 := by
    rw [heval a (by simp [K])]
    exact hV3left
  have hqCone : A.arrangementPointNormalizedRepresentativeAt l q.1 ∈
      A.arrangementClosedSignConeOn tau K := by
    intro k hk
    simp only [K, Finset.mem_insert, Finset.mem_singleton] at hk
    rcases hk with hk | hk | hk
    · subst k
      have htau : tau l = true := by
        exact (heqOn l (by simp [K])).trans
          (A.emptyTriangleSignPattern_base l a b V1 V3
            hal.symm hbl.symm)
      unfold arrangementOrientedEvaluation
      rw [htau]
      change 0 ≤ projectiveLineEvaluation (A.projectiveLine l)
        (A.arrangementPointNormalizedRepresentativeAt l q.1)
      rw [A.projectiveLineEvaluation_arrangementPointNormalizedRepresentativeAt_base
        l q.1 hqaway]
      norm_num
    · subst k
      have hq0 := A.arrangementPointNormalizedRepresentativeAt_ne_zero
        l q.1 hqaway
      have hz := (A.incident_projectivization_mk_iff_orientedEvaluation_eq_zero
        tau a _ hq0).1
        (by
          have hmk :=
            A.projectivization_mk_arrangementPointNormalizedRepresentativeAt
              l q.1 hqaway
          rw [hmk]
          exact hqa)
      exact hz.symm.le
    · subst k
      have hq0 := A.arrangementPointNormalizedRepresentativeAt_ne_zero
        l q.1 hqaway
      have hz := (A.incident_projectivization_mk_iff_orientedEvaluation_eq_zero
        tau b _ hq0).1
        (by
          have hmk :=
            A.projectivization_mk_arrangementPointNormalizedRepresentativeAt
              l q.1 hqaway
          rw [hmk]
          exact hqb)
      exact hz.symm.le
  exact A.ordinaryVertexAttachedToLine_of_minimal_threeClauseTriangle
    hA q p fixedGauge l a b hab hqaway hqa hqb
    hordinary hgauge (by simpa only [tau, X] using hXbase')
    (by simpa only [tau, V1] using hV1right')
    (by simpa only [tau, V3] using hV3left')
    (by simpa only [tau, K] using hqCone) hmin

/-- Packaging lemma for a locally minimal empty subtriangle.  Once the
strict three-cone has no transverse zero, its barycentric center itself
chooses the complement face and hence a literal attachment witness. -/
theorem ordinaryVertexAttachedToLine_of_noZero_oriented_subtriangle
    (A : FiniteProjectiveLineArrangement Line) (hA : A.NonPencil)
    (fixedGauge : (Fin 3 → ℝ) →ₗ[ℝ] ℝ)
    (q : A.OrdinaryVertex) (l a b : Line) (sigma : Line → Bool)
    (hal : a ≠ l) (hbl : b ≠ l) (hab : a ≠ b)
    (hqaway : ¬ A.Incident q.1 l)
    (hqa : A.Incident q.1 a) (hqb : A.Incident q.1 b)
    (hordinary : ∀ k : Line, A.Incident q.1 k ↔ k = a ∨ k = b)
    (hfq : fixedGauge q.1.rep ≠ 0)
    (hfV1 : fixedGauge (A.intersection l a).rep ≠ 0)
    (hfV3 : fixedGauge (A.intersection l b).rep ≠ 0)
    (hXbase : 0 < A.arrangementOrientedEvaluation sigma l
      (vertexChartNormalizedVector fixedGauge q.1))
    (hV1right : 0 < A.arrangementOrientedEvaluation sigma b
      (vertexChartNormalizedVector fixedGauge (A.intersection l a)))
    (hV3left : 0 < A.arrangementOrientedEvaluation sigma a
      (vertexChartNormalizedVector fixedGauge (A.intersection l b)))
    (hnozero : ∀ m : Line, m ∉ ({l, a, b} : Finset Line) →
      ∀ Z ∈ A.arrangementSignConeOn sigma {l, a, b},
        A.arrangementOrientedEvaluation sigma m Z ≠ 0) :
    A.OrdinaryVertexAttachedToLine q l := by
  classical
  let X := vertexChartNormalizedVector fixedGauge q.1
  let V1 := vertexChartNormalizedVector fixedGauge (A.intersection l a)
  let V3 := vertexChartNormalizedVector fixedGauge (A.intersection l b)
  have hXleft : A.arrangementOrientedEvaluation sigma a X = 0 := by
    simpa only [X] using
      A.arrangementOrientedEvaluation_vertexChartNormalizedVector_eq_zero
        sigma fixedGauge hfq hqa
  have hXright : A.arrangementOrientedEvaluation sigma b X = 0 := by
    simpa only [X] using
      A.arrangementOrientedEvaluation_vertexChartNormalizedVector_eq_zero
        sigma fixedGauge hfq hqb
  have hV1base : A.arrangementOrientedEvaluation sigma l V1 = 0 := by
    simpa only [V1] using
      A.arrangementOrientedEvaluation_vertexChartNormalizedVector_eq_zero
        sigma fixedGauge hfV1 (A.intersection_incident_left hal.symm)
  have hV1left : A.arrangementOrientedEvaluation sigma a V1 = 0 := by
    simpa only [V1] using
      A.arrangementOrientedEvaluation_vertexChartNormalizedVector_eq_zero
        sigma fixedGauge hfV1 (A.intersection_incident_right hal.symm)
  have hV3base : A.arrangementOrientedEvaluation sigma l V3 = 0 := by
    simpa only [V3] using
      A.arrangementOrientedEvaluation_vertexChartNormalizedVector_eq_zero
        sigma fixedGauge hfV3 (A.intersection_incident_left hbl.symm)
  have hV3right : A.arrangementOrientedEvaluation sigma b V3 = 0 := by
    simpa only [V3] using
      A.arrangementOrientedEvaluation_vertexChartNormalizedVector_eq_zero
        sigma fixedGauge hfV3 (A.intersection_incident_right hbl.symm)
  let K : Finset Line := {l, a, b}
  let U := X + V1 + V3
  have hU : U ∈ A.arrangementSignConeOn sigma K := by
    intro k hk
    simp only [K, Finset.mem_insert, Finset.mem_singleton] at hk
    rcases hk with rfl | rfl | rfl
    · simpa only [U, X, V1, V3, LinearMap.map_add, hV1base,
        hV3base, add_zero] using hXbase
    · simpa only [U, X, V1, V3, LinearMap.map_add, hXleft,
        hV1left, zero_add] using hV3left
    · simpa only [U, X, V1, V3, LinearMap.map_add, hXright,
        hV3right, zero_add, add_zero] using hV1right
  have hU0 : U ≠ 0 := by
    intro hzero
    have hu := hU l (by simp [K])
    rw [hzero, LinearMap.map_zero] at hu
    exact (lt_irrefl 0 hu)
  obtain ⟨p, hp⟩ := A.exists_arrangementComplement_of_no_additional_zero
    sigma K U hU0 hU
      (fun m hm => hnozero m (by simpa only [K] using hm) U hU)
  have hpointBase : A.arrangementPointSignPattern l p l = true := by
    simp [arrangementPointSignPattern,
      A.projectiveLineEvaluation_arrangementNormalizedRepresentative_base]
  have hq0 := A.arrangementPointNormalizedRepresentativeAt_ne_zero
    l q.1 hqaway
  have hqzero (k : Line) (hqk : A.Incident q.1 k) :
      A.arrangementOrientedEvaluation (A.arrangementPointSignPattern l p) k
        (A.arrangementPointNormalizedRepresentativeAt l q.1) = 0 := by
    apply (A.incident_projectivization_mk_iff_orientedEvaluation_eq_zero
      (A.arrangementPointSignPattern l p) k _ hq0).1
    simpa only [A.projectivization_mk_arrangementPointNormalizedRepresentativeAt
      l q.1 hqaway] using hqk
  have hbaseRaw : projectiveLineEvaluation (A.projectiveLine l) U ≠ 0 := by
    exact (A.arrangementOrientedEvaluation_eq_zero_iff sigma l U).not.mp
      (ne_of_gt (hU l (by simp [K])))
  have hnorm := A.arrangementNormalizedRepresentative_eq_of_projectivization_mk
    l p hU0 hbaseRaw hp.symm
  let c := (projectiveLineEvaluation (A.projectiveLine l) U)⁻¹
  have hc0 : c ≠ 0 := inv_ne_zero hbaseRaw
  rcases lt_or_gt_of_ne hc0 with hcneg | hcpos
  · let sigma' : Line → Bool := fun k => !(sigma k)
    have hnegU : -U ∈ A.arrangementSignConeOn sigma' K := by
      intro k hk
      rw [A.arrangementOrientedEvaluation_boolNot_apply, LinearMap.map_neg]
      simpa using hU k hk
    have hnorm' : A.arrangementNormalizedRepresentative l p = (-c) • (-U) := by
      rw [hnorm]
      simp [c, smul_smul]
    have heq' := A.arrangementPointSignPattern_eq_on_of_normalized_eq_pos_smul
      l p sigma' K (-U) (-c) (neg_pos.mpr hcneg) hnorm' hnegU
    have hzero' : ∀ m : Line, m ∉ K →
        ∀ Z ∈ A.arrangementSignConeOn sigma' K,
          A.arrangementOrientedEvaluation sigma' m Z ≠ 0 := by
      intro m hm Z hZ hZm
      have hnegZ : -Z ∈ A.arrangementSignConeOn sigma K := by
        intro k hk
        have hz := hZ k hk
        rw [A.arrangementOrientedEvaluation_boolNot_apply] at hz
        simpa using hz
      apply hnozero m (by simpa only [K] using hm) (-Z) hnegZ
      apply (A.arrangementOrientedEvaluation_eq_zero_iff sigma m (-Z)).2
      rw [LinearMap.map_neg, neg_eq_zero]
      exact (A.arrangementOrientedEvaluation_eq_zero_iff sigma' m Z).1 hZm
    have hzeroPoint := A.noAdditionalZero_mono_signPattern_eqOn
      sigma' (A.arrangementPointSignPattern l p) K heq' hzero'
    have hzeroAll := A.noAdditionalZero_allBases_of_one p l K hzeroPoint
    have hqCone : A.arrangementPointNormalizedRepresentativeAt l q.1 ∈
        A.arrangementClosedSignConeOn
          (A.arrangementPointSignPattern l p) K := by
      intro k hk
      simp only [K, Finset.mem_insert, Finset.mem_singleton] at hk
      rcases hk with hk | hk | hk
      · subst k
        unfold arrangementOrientedEvaluation
        rw [hpointBase,
          if_pos rfl,
          A.projectiveLineEvaluation_arrangementPointNormalizedRepresentativeAt_base
            l q.1 hqaway]
        norm_num
      · subst k
        exact (hqzero a hqa).symm.le
      · subst k
        exact (hqzero b hqb).symm.le
    exact A.ordinaryVertexAttachedToLine_of_no_additional_zero
      hA q p l a b hal hbl hab hqaway hzeroAll
        (by simpa only [K] using hqCone)
  · have heq := A.arrangementPointSignPattern_eq_on_of_normalized_eq_pos_smul
      l p sigma K U c hcpos (by simpa only [c] using hnorm) hU
    have hzeroPoint := A.noAdditionalZero_mono_signPattern_eqOn
      sigma (A.arrangementPointSignPattern l p) K heq
        (by simpa only [K] using hnozero)
    have hzeroAll := A.noAdditionalZero_allBases_of_one p l K hzeroPoint
    have hqCone : A.arrangementPointNormalizedRepresentativeAt l q.1 ∈
        A.arrangementClosedSignConeOn
          (A.arrangementPointSignPattern l p) K := by
      intro k hk
      simp only [K, Finset.mem_insert, Finset.mem_singleton] at hk
      rcases hk with hk | hk | hk
      · subst k
        unfold arrangementOrientedEvaluation
        rw [hpointBase,
          if_pos rfl,
          A.projectiveLineEvaluation_arrangementPointNormalizedRepresentativeAt_base
            l q.1 hqaway]
        norm_num
      · subst k
        exact (hqzero a hqa).symm.le
      · subst k
        exact (hqzero b hqb).symm.le
    exact A.ordinaryVertexAttachedToLine_of_no_additional_zero
      hA q p l a b hal hbl hab hqaway hzeroAll
        (by simpa only [K] using hqCone)

/-- The affine base parameter supplied by a nondegenerate triangle chart is
injective on the base arc of that projective sector. -/
theorem sectorExitBaseParameter_eq_imp_eq
    (A : FiniteProjectiveLineArrangement Line) (sigma : Line → Bool)
    (l a b : Line)
    (htriangle : ¬ ∃ x : RealProjectivePoint,
      A.Incident x l ∧ A.Incident x a ∧ A.Incident x b)
    {q r : RealProjectivePoint}
    (hqSector : A.projectivePointMemTriangleSector sigma l a b q)
    (hrSector : A.projectivePointMemTriangleSector sigma l a b r)
    (hql : A.Incident q l) (hrl : A.Incident r l)
    (heq : A.sectorExitBaseParameter sigma l a b q =
      A.sectorExitBaseParameter sigma l a b r) : q = r := by
  let Q := A.sectorExitNormalizedPoint sigma l a b q
  let R := A.sectorExitNormalizedPoint sigma l a b r
  obtain ⟨hQ0, hQgauge, hmkQ, _hQsector⟩ :=
    A.sectorExitNormalizedPoint_facts sigma l a b htriangle q hqSector
  obtain ⟨hR0, hRgauge, hmkR, _hRsector⟩ :=
    A.sectorExitNormalizedPoint_facts sigma l a b htriangle r hrSector
  have hQl : A.arrangementOrientedEvaluation sigma l Q = 0 :=
    A.arrangementOrientedEvaluation_sectorExitNormalizedPoint_eq_zero
      sigma l a b l htriangle q hqSector hql
  have hRl : A.arrangementOrientedEvaluation sigma l R = 0 :=
    A.arrangementOrientedEvaluation_sectorExitNormalizedPoint_eq_zero
      sigma l a b l htriangle r hrSector hrl
  have hQa : A.arrangementOrientedEvaluation sigma a Q =
      A.arrangementOrientedEvaluation sigma a R := by
    simpa only [sectorExitBaseParameter, Q, R] using heq
  have hQb : A.arrangementOrientedEvaluation sigma b Q =
      A.arrangementOrientedEvaluation sigma b R := by
    simp only [triangleSectorGauge, Q, R] at hQgauge hRgauge
    linarith
  have hQR : Q = R := by
    apply A.triangleSectorCoordinateMap_injective sigma l a b htriangle
    funext i
    fin_cases i
    · simpa [triangleSectorCoordinateMap, triangleSectorSide] using hQl.trans hRl.symm
    · simpa [triangleSectorCoordinateMap, triangleSectorSide] using hQa
    · simpa [triangleSectorCoordinateMap, triangleSectorSide] using hQb
  calc
    q = Projectivization.mk ℝ Q hQ0 := hmkQ.symm
    _ = Projectivization.mk ℝ R hR0 := by simpa only [hQR]
    _ = r := hmkR

@[simp]
theorem fixedChartBaseParameter_triangleSectorFixedGauge
    (A : FiniteProjectiveLineArrangement Line) (sigma : Line → Bool)
    (l a b : Line) (q : RealProjectivePoint) :
    A.fixedChartBaseParameter sigma
        (A.triangleSectorFixedGauge sigma l a b) a q =
      A.sectorExitBaseParameter sigma l a b q := by
  simp [fixedChartBaseParameter, sectorExitBaseParameter,
    sectorExitNormalizedPoint,
    A.vertexChartNormalizedVector_triangleSectorFixedGauge]

/-- Local-gauge version of base-coordinate injectivity. -/
theorem fixedChartBaseParameter_intersection_injective_of_localGauge
    (A : FiniteProjectiveLineArrangement Line) (sigma : Line → Bool)
    (fixedGauge : (Fin 3 → ℝ) →ₗ[ℝ] ℝ)
    {l axis c d : Line} (hlaxis : l ≠ axis)
    (hlc : l ≠ c) (hld : l ≠ d)
    (hfc : fixedGauge (A.intersection l c).rep ≠ 0)
    (hfd : fixedGauge (A.intersection l d).rep ≠ 0)
    (hfaxis : fixedGauge (A.intersection l axis).rep ≠ 0)
    (heq : A.fixedChartBaseParameter sigma fixedGauge axis
        (A.intersection l c) =
      A.fixedChartBaseParameter sigma fixedGauge axis
        (A.intersection l d)) :
    A.intersection l c = A.intersection l d := by
  let q := A.intersection l c
  let r := A.intersection l d
  have hfq : fixedGauge q.rep ≠ 0 := by simpa only [q] using hfc
  have hfr : fixedGauge r.rep ≠ 0 := by simpa only [r] using hfd
  let Q := vertexChartNormalizedVector fixedGauge q
  let R := vertexChartNormalizedVector fixedGauge r
  have hQR : Q = R := by
    apply sub_eq_zero.mp
    apply A.eq_zero_of_two_orientedEvaluations_and_fixedGauge
      sigma fixedGauge hlaxis hfaxis
    · rw [LinearMap.map_sub]
      have hQl :=
        A.arrangementOrientedEvaluation_vertexChartNormalizedVector_eq_zero
          sigma fixedGauge hfq (by
            simpa only [q] using A.intersection_incident_left hlc)
      have hRl :=
        A.arrangementOrientedEvaluation_vertexChartNormalizedVector_eq_zero
          sigma fixedGauge hfr (by
            simpa only [r] using A.intersection_incident_left hld)
      rw [hQl, hRl, sub_self]
    · rw [LinearMap.map_sub]
      exact sub_eq_zero.mpr (by
        simpa only [fixedChartBaseParameter, Q, R, q, r] using heq)
    · rw [LinearMap.map_sub]
      simp only [Q, R,
        vertexChartNormalizedVector_fixedGauge_eq_one fixedGauge q hfq,
        vertexChartNormalizedVector_fixedGauge_eq_one fixedGauge r hfr,
        sub_self]
  calc
    A.intersection l c = Projectivization.mk ℝ Q
        (vertexChartNormalizedVector_ne_zero fixedGauge q hfq) := by
      simpa only [q, Q] using
        (projectivization_mk_vertexChartNormalizedVector
          fixedGauge q hfq).symm
    _ = Projectivization.mk ℝ R
        (vertexChartNormalizedVector_ne_zero fixedGauge r hfr) := by
      simpa only [hQR]
    _ = A.intersection l d := by
      simpa only [r, R] using
        projectivization_mk_vertexChartNormalizedVector fixedGauge r hfr

/-- Local-gauge sorting of three distinct support returns. -/
theorem exists_fixedChart_ordered_three_incident_supports_of_localGauge
    (A : FiniteProjectiveLineArrangement Line) (sigma : Line → Bool)
    (fixedGauge : (Fin 3 → ℝ) →ₗ[ℝ] ℝ)
    (x : RealProjectivePoint) (l axis a b c : Line)
    (hxl : ¬ A.Incident x l) (hlaxis : l ≠ axis)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hxa : A.Incident x a) (hxb : A.Incident x b)
    (hxc : A.Incident x c)
    (hfa : fixedGauge (A.intersection l a).rep ≠ 0)
    (hfb : fixedGauge (A.intersection l b).rep ≠ 0)
    (hfc : fixedGauge (A.intersection l c).rep ≠ 0)
    (hfaxis : fixedGauge (A.intersection l axis).rep ≠ 0) :
    ∃ left middle right : Line,
      l ≠ left ∧ l ≠ middle ∧ l ≠ right ∧
      A.Incident x left ∧ A.Incident x middle ∧ A.Incident x right ∧
      fixedGauge (A.intersection l left).rep ≠ 0 ∧
      fixedGauge (A.intersection l middle).rep ≠ 0 ∧
      fixedGauge (A.intersection l right).rep ≠ 0 ∧
      A.fixedChartBaseParameter sigma fixedGauge axis
          (A.intersection l left) <
        A.fixedChartBaseParameter sigma fixedGauge axis
          (A.intersection l middle) ∧
      A.fixedChartBaseParameter sigma fixedGauge axis
          (A.intersection l middle) <
        A.fixedChartBaseParameter sigma fixedGauge axis
          (A.intersection l right) := by
  have hla : l ≠ a := fun h => hxl (h ▸ hxa)
  have hlb : l ≠ b := fun h => hxl (h ▸ hxb)
  have hlc : l ≠ c := fun h => hxl (h ▸ hxc)
  have hpab := A.intersection_base_ne_of_distinct_supports
    x l a b hxl hxa hxb hab
  have hpac := A.intersection_base_ne_of_distinct_supports
    x l a c hxl hxa hxc hac
  have hpbc := A.intersection_base_ne_of_distinct_supports
    x l b c hxl hxb hxc hbc
  have htab : A.fixedChartBaseParameter sigma fixedGauge axis
      (A.intersection l a) ≠
      A.fixedChartBaseParameter sigma fixedGauge axis
        (A.intersection l b) := by
    intro heq
    exact hpab (A.fixedChartBaseParameter_intersection_injective_of_localGauge
      sigma fixedGauge hlaxis hla hlb hfa hfb hfaxis heq)
  have htac : A.fixedChartBaseParameter sigma fixedGauge axis
      (A.intersection l a) ≠
      A.fixedChartBaseParameter sigma fixedGauge axis
        (A.intersection l c) := by
    intro heq
    exact hpac (A.fixedChartBaseParameter_intersection_injective_of_localGauge
      sigma fixedGauge hlaxis hla hlc hfa hfc hfaxis heq)
  have htbc : A.fixedChartBaseParameter sigma fixedGauge axis
      (A.intersection l b) ≠
      A.fixedChartBaseParameter sigma fixedGauge axis
        (A.intersection l c) := by
    intro heq
    exact hpbc (A.fixedChartBaseParameter_intersection_injective_of_localGauge
      sigma fixedGauge hlaxis hlb hlc hfb hfc hfaxis heq)
  rcases lt_or_gt_of_ne htab with hab' | hba'
  · rcases lt_or_gt_of_ne htbc with hbc' | hcb'
    · exact ⟨a, b, c, hla, hlb, hlc, hxa, hxb, hxc,
        hfa, hfb, hfc, hab', hbc'⟩
    · rcases lt_or_gt_of_ne htac with hac' | hca'
      · exact ⟨a, c, b, hla, hlc, hlb, hxa, hxc, hxb,
          hfa, hfc, hfb, hac', hcb'⟩
      · exact ⟨c, a, b, hlc, hla, hlb, hxc, hxa, hxb,
          hfc, hfa, hfb, hca', hab'⟩
  · rcases lt_or_gt_of_ne htac with hac' | hca'
    · exact ⟨b, a, c, hlb, hla, hlc, hxb, hxa, hxc,
        hfb, hfa, hfc, hba', hac'⟩
    · rcases lt_or_gt_of_ne htbc with hbc' | hcb'
      · exact ⟨b, c, a, hlb, hlc, hla, hxb, hxc, hxa,
          hfb, hfc, hfa, hbc', hca'⟩
      · exact ⟨c, b, a, hlc, hlb, hla, hxc, hxb, hxa,
          hfc, hfb, hfa, hcb', hba'⟩

/-- Local Felsner minimizer step: if every support through the chosen vertex
returns to the base arc and every such return is nonordinary, the minimizing
vertex is ordinary. -/
theorem multiplicity_eq_two_of_local_triangle_minimal
    (A : FiniteProjectiveLineArrangement Line) (outerSigma : Line → Bool)
    (l outerLeft outerRight : Line)
    (houterTriangle : ¬ ∃ r : RealProjectivePoint,
      A.Incident r l ∧ A.Incident r outerLeft ∧
        A.Incident r outerRight)
    (x : RealProjectivePoint) (hxVertex : x ∈ A.vertexSet)
    (hxOuter : A.projectivePointMemTriangleSector
      outerSigma l outerLeft outerRight x)
    (hxl : ¬ A.Incident x l)
    (hreturn : ∀ c : Line, A.Incident x c → l ≠ c →
      A.projectivePointMemTriangleSector outerSigma l outerLeft outerRight
        (A.intersection l c))
    (hextraMiddle : ∀ left middle right : Line,
      A.Incident x left → A.Incident x middle → A.Incident x right →
      l ≠ left → l ≠ middle → l ≠ right →
      A.sectorExitBaseParameter outerSigma l outerLeft outerRight
          (A.intersection l left) <
        A.sectorExitBaseParameter outerSigma l outerLeft outerRight
          (A.intersection l middle) →
      A.sectorExitBaseParameter outerSigma l outerLeft outerRight
          (A.intersection l middle) <
        A.sectorExitBaseParameter outerSigma l outerLeft outerRight
          (A.intersection l right) →
      ∃ m : Line, m ≠ l ∧ m ≠ middle ∧
        A.Incident (A.intersection l middle) m)
    (hmin : ∀ y : RealProjectivePoint, y ∈ A.vertexSet →
      A.projectivePointMemTriangleSector
        outerSigma l outerLeft outerRight y →
      ¬ A.Incident y l →
      A.vertexChartLineHeight
          (A.triangleSectorFixedGauge outerSigma l outerLeft outerRight)
          l x ≤
        A.vertexChartLineHeight
          (A.triangleSectorFixedGauge outerSigma l outerLeft outerRight)
          l y) :
    A.multiplicity x = 2 := by
  have htwo : 2 ≤ A.multiplicity x := by
    obtain ⟨u, v, huv, huvx⟩ := A.exists_lines_of_mem_vertexSet hxVertex
    rw [← huvx]
    exact A.two_le_multiplicity_intersection huv
  by_contra hne
  have hthree : 3 ≤ A.multiplicity x := by omega
  obtain ⟨a, b, c, hab, hac, hbc, hxa, hxb, hxc⟩ :=
    A.exists_three_incident_lines_of_three_le_multiplicity x hthree
  have hla : l ≠ a := fun h => hxl (h ▸ hxa)
  have hlb : l ≠ b := fun h => hxl (h ▸ hxb)
  have hlc : l ≠ c := fun h => hxl (h ▸ hxc)
  have hVa := hreturn a hxa hla
  have hVb := hreturn b hxb hlb
  have hVc := hreturn c hxc hlc
  let fixedGauge :=
    A.triangleSectorFixedGauge outerSigma l outerLeft outerRight
  have hfx : fixedGauge x.rep ≠ 0 := by
    simpa only [fixedGauge, A.triangleSectorFixedGauge_apply] using
      A.triangleSectorGauge_ne_zero_of_projective outerSigma l outerLeft
        outerRight houterTriangle x hxOuter
  have hfa : fixedGauge (A.intersection l a).rep ≠ 0 := by
    simpa only [fixedGauge, A.triangleSectorFixedGauge_apply] using
      A.triangleSectorGauge_ne_zero_of_projective outerSigma l outerLeft
        outerRight houterTriangle (A.intersection l a) hVa
  have hfb : fixedGauge (A.intersection l b).rep ≠ 0 := by
    simpa only [fixedGauge, A.triangleSectorFixedGauge_apply] using
      A.triangleSectorGauge_ne_zero_of_projective outerSigma l outerLeft
        outerRight houterTriangle (A.intersection l b) hVb
  have hfc : fixedGauge (A.intersection l c).rep ≠ 0 := by
    simpa only [fixedGauge, A.triangleSectorFixedGauge_apply] using
      A.triangleSectorGauge_ne_zero_of_projective outerSigma l outerLeft
        outerRight houterTriangle (A.intersection l c) hVc
  have hlOuterLeft : l ≠ outerLeft := by
    intro hEq
    by_cases hEqR : l = outerRight
    · apply houterTriangle
      refine ⟨A.intersection l a, A.intersection_incident_left hla, ?_, ?_⟩
      · rw [← hEq]
        exact A.intersection_incident_left hla
      · rw [← hEqR]
        exact A.intersection_incident_left hla
    · apply houterTriangle
      refine ⟨A.intersection l outerRight,
        A.intersection_incident_left hEqR, ?_,
        A.intersection_incident_right hEqR⟩
      rw [← hEq]
      exact A.intersection_incident_left hEqR
  have hVOuterLeft : A.projectivePointMemTriangleSector
      outerSigma l outerLeft outerRight (A.intersection l outerLeft) :=
    A.projectivePointMemTriangleSector_of_incident_base_left
      outerSigma l outerLeft outerRight (A.intersection l outerLeft)
        (A.intersection_incident_left hlOuterLeft)
        (A.intersection_incident_right hlOuterLeft)
  have hfOuterLeft : fixedGauge (A.intersection l outerLeft).rep ≠ 0 := by
    simpa only [fixedGauge, A.triangleSectorFixedGauge_apply] using
      A.triangleSectorGauge_ne_zero_of_projective outerSigma l outerLeft
        outerRight houterTriangle (A.intersection l outerLeft) hVOuterLeft
  obtain ⟨left, middle, right, hlleft, hlmiddle, hlright,
      hxleft, hxmiddle, hxright, hfleft, hfmiddle, hfright, h12, h23⟩ :=
    A.exists_fixedChart_ordered_three_incident_supports_of_localGauge
      outerSigma fixedGauge x l outerLeft a b c hxl hlOuterLeft hab hac hbc
      hxa hxb hxc hfa hfb hfc hfOuterLeft
  have h12' : A.sectorExitBaseParameter outerSigma l outerLeft outerRight
        (A.intersection l left) <
      A.sectorExitBaseParameter outerSigma l outerLeft outerRight
        (A.intersection l middle) := by
    simpa only [fixedGauge,
      A.fixedChartBaseParameter_triangleSectorFixedGauge] using h12
  have h23' : A.sectorExitBaseParameter outerSigma l outerLeft outerRight
        (A.intersection l middle) <
      A.sectorExitBaseParameter outerSigma l outerLeft outerRight
        (A.intersection l right) := by
    simpa only [fixedGauge,
      A.fixedChartBaseParameter_triangleSectorFixedGauge] using h23
  obtain ⟨m, hml, hmc, hV2m⟩ := hextraMiddle left middle right
    hxleft hxmiddle hxright hlleft hlmiddle hlright h12' h23'
  obtain ⟨y, h, hh0, hh1, hyVertex, _hym, hyl, _hyHeight,
      hylt, hbranch⟩ :=
    A.fixedChartExit_axis_ordered_of_localGauge outerSigma fixedGauge
      l outerLeft left right middle m x hfx hfleft hfmiddle hfright
      hfOuterLeft hxVertex hlOuterLeft hlleft hlright hlmiddle hml hmc hxl
      hxleft hxright hxmiddle hV2m h12 h23
  have hxNorm : vertexChartNormalizedVector fixedGauge x ∈
      A.arrangementClosedSignConeOn outerSigma
        {l, outerLeft, outerRight} := by
    simpa only [fixedGauge,
      A.vertexChartNormalizedVector_triangleSectorFixedGauge] using
      A.triangleSectorNormalizedVector_mem_of_projective
        outerSigma l outerLeft outerRight houterTriangle x hxOuter
  have hVleftOuter := hreturn left hxleft hlleft
  have hVrightOuter := hreturn right hxright hlright
  have hVleftNorm : vertexChartNormalizedVector fixedGauge
        (A.intersection l left) ∈
      A.arrangementClosedSignConeOn outerSigma
        {l, outerLeft, outerRight} := by
    simpa only [fixedGauge,
      A.vertexChartNormalizedVector_triangleSectorFixedGauge] using
      A.triangleSectorNormalizedVector_mem_of_projective
        outerSigma l outerLeft outerRight houterTriangle
          (A.intersection l left) hVleftOuter
  have hVrightNorm : vertexChartNormalizedVector fixedGauge
        (A.intersection l right) ∈
      A.arrangementClosedSignConeOn outerSigma
        {l, outerLeft, outerRight} := by
    simpa only [fixedGauge,
      A.vertexChartNormalizedVector_triangleSectorFixedGauge] using
      A.triangleSectorNormalizedVector_mem_of_projective
        outerSigma l outerLeft outerRight houterTriangle
          (A.intersection l right) hVrightOuter
  have hyData : fixedGauge y.rep ≠ 0 ∧
      vertexChartNormalizedVector fixedGauge y ∈
        A.arrangementClosedSignConeOn outerSigma
          {l, outerLeft, outerRight} := by
    rcases hbranch with hleft | hright
    · have hfy : fixedGauge y.rep ≠ 0 := by
        intro hzero
        have hnormZero : vertexChartNormalizedVector fixedGauge y = 0 := by
          simp [vertexChartNormalizedVector, hzero]
        have hfg := congrArg fixedGauge hleft.2
        simp only [hnormZero, LinearMap.map_zero, LinearMap.map_add,
          LinearMap.map_smul, smul_eq_mul,
          vertexChartNormalizedVector_fixedGauge_eq_one
            fixedGauge (A.intersection l left) hfleft,
          vertexChartNormalizedVector_fixedGauge_eq_one fixedGauge x hfx]
            at hfg
        linarith
      refine ⟨hfy, ?_⟩
      rw [hleft.2]
      exact A.barycentric_mem_arrangementClosedSignConeOn
        outerSigma l outerLeft outerRight hh0.le hh1.le hVleftNorm hxNorm
    · have hfy : fixedGauge y.rep ≠ 0 := by
        intro hzero
        have hnormZero : vertexChartNormalizedVector fixedGauge y = 0 := by
          simp [vertexChartNormalizedVector, hzero]
        have hfg := congrArg fixedGauge hright.2
        simp only [hnormZero, LinearMap.map_zero, LinearMap.map_add,
          LinearMap.map_smul, smul_eq_mul,
          vertexChartNormalizedVector_fixedGauge_eq_one
            fixedGauge (A.intersection l right) hfright,
          vertexChartNormalizedVector_fixedGauge_eq_one fixedGauge x hfx]
            at hfg
        linarith
      refine ⟨hfy, ?_⟩
      rw [hright.2]
      exact A.barycentric_mem_arrangementClosedSignConeOn
        outerSigma l outerLeft outerRight hh0.le hh1.le hVrightNorm hxNorm
  have hyOuter :=
    A.projectivePointMemTriangleSector_of_vertexChartNormalizedVector_mem
      outerSigma fixedGauge l outerLeft outerRight y hyData.1 hyData.2
  exact (not_lt_of_ge (hmin y hyVertex hyOuter hyl)) hylt

/-- Full local Three-Clause consumer for one outer sector, requiring an
extra support only at the median return selected in the contradiction. -/
theorem exists_ordinaryAttachment_in_triangleSector_of_middle
    (A : FiniteProjectiveLineArrangement Line) (hA : A.NonPencil)
    (outerSigma : Line → Bool) (l outerLeft outerRight : Line)
    (houterTriangle : ¬ ∃ r : RealProjectivePoint,
      A.Incident r l ∧ A.Incident r outerLeft ∧
        A.Incident r outerRight)
    (hS : (A.triangleSectorOffBaseVertexSet
      outerSigma l outerLeft outerRight).Nonempty)
    (hreturn : ∀ x : RealProjectivePoint, x ∈ A.vertexSet →
      A.projectivePointMemTriangleSector outerSigma l outerLeft outerRight x →
      ¬ A.Incident x l →
      ∀ c : Line, A.Incident x c → l ≠ c →
        A.projectivePointMemTriangleSector outerSigma l outerLeft outerRight
          (A.intersection l c))
    (hextraMiddle : ∀ x : RealProjectivePoint, x ∈ A.vertexSet →
      A.projectivePointMemTriangleSector outerSigma l outerLeft outerRight x →
      ¬ A.Incident x l →
      ∀ left middle right : Line,
        A.Incident x left → A.Incident x middle → A.Incident x right →
        l ≠ left → l ≠ middle → l ≠ right →
        A.sectorExitBaseParameter outerSigma l outerLeft outerRight
            (A.intersection l left) <
          A.sectorExitBaseParameter outerSigma l outerLeft outerRight
            (A.intersection l middle) →
        A.sectorExitBaseParameter outerSigma l outerLeft outerRight
            (A.intersection l middle) <
          A.sectorExitBaseParameter outerSigma l outerLeft outerRight
            (A.intersection l right) →
        ∃ m : Line, m ≠ l ∧ m ≠ middle ∧
          A.Incident (A.intersection l middle) m) :
    ∃ q : A.OrdinaryVertex,
      A.projectivePointMemTriangleSector outerSigma l outerLeft outerRight q.1 ∧
      ¬ A.Incident q.1 l ∧
      (∀ y : RealProjectivePoint, y ∈ A.vertexSet →
        A.projectivePointMemTriangleSector
          outerSigma l outerLeft outerRight y →
        ¬ A.Incident y l →
        A.vertexChartLineHeight
            (A.triangleSectorFixedGauge
              outerSigma l outerLeft outerRight) l q.1 ≤
          A.vertexChartLineHeight
            (A.triangleSectorFixedGauge
              outerSigma l outerLeft outerRight) l y) ∧
      A.OrdinaryVertexAttachedToLine q l := by
  classical
  obtain ⟨x, hxVertex, hxOuter, hxl, _hxpos, hmin⟩ :=
    A.exists_minimal_originalTriangleGaugeLineHeight
      outerSigma l outerLeft outerRight houterTriangle hS
  have hx2 := A.multiplicity_eq_two_of_local_triangle_minimal
    outerSigma l outerLeft outerRight houterTriangle x hxVertex hxOuter hxl
    (hreturn x hxVertex hxOuter hxl)
    (hextraMiddle x hxVertex hxOuter hxl)
    hmin
  let q : A.OrdinaryVertex :=
    ⟨x, Finset.mem_filter.mpr ⟨hxVertex, hx2⟩⟩
  obtain ⟨a, b, hab, hordinary⟩ :=
    A.exists_two_lines_incident_iff_of_ordinaryVertex q
  have hqa : A.Incident q.1 a := (hordinary a).2 (Or.inl rfl)
  have hqb : A.Incident q.1 b := (hordinary b).2 (Or.inr rfl)
  have hal : a ≠ l := fun h => hxl (h ▸ hqa)
  have hbl : b ≠ l := fun h => hxl (h ▸ hqb)
  have hsubTriangle := A.not_three_concurrent_of_offBase_apex
    q.1 l a b hab hqa hqb hxl
  let fixedGauge :=
    A.triangleSectorFixedGauge outerSigma l outerLeft outerRight
  have hfq : fixedGauge q.1.rep ≠ 0 := by
    simpa only [fixedGauge, A.triangleSectorFixedGauge_apply] using
      A.triangleSectorGauge_ne_zero_of_projective outerSigma l outerLeft
        outerRight houterTriangle q.1 hxOuter
  have hV1Outer := hreturn q.1 hxVertex hxOuter hxl a hqa hal.symm
  have hV3Outer := hreturn q.1 hxVertex hxOuter hxl b hqb hbl.symm
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
      q.1 l a b hal.symm hab hqa hqb hxl
  have hV3notA : ¬ A.Incident (A.intersection l b) a :=
    A.not_incident_intersection_base_support_of_offBase_apex
      q.1 l b a hbl.symm hab.symm hqb hqa hxl
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
        outerSigma l outerLeft outerRight houterTriangle q.1 hxOuter
  have hXbaseOuter : 0 < A.arrangementOrientedEvaluation outerSigma l X := by
    have hge := hxNorm l (by simp)
    have hne : A.arrangementOrientedEvaluation outerSigma l X ≠ 0 := by
      simpa only [X] using
        A.arrangementOrientedEvaluation_vertexChartNormalizedVector_ne_zero
          outerSigma fixedGauge hfq hxl
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
  have hqOuterNorm : X ∈ A.arrangementClosedSignConeOn outerSigma
      {l, outerLeft, outerRight} := hxNorm
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
      hsubTriangle hal.symm hbl.symm hab hxl hqa hqb hordinary
      hfq hfV1 hfV3 hXbase hV1right hV3left
      hqOuterNorm hV1OuterNorm hV3OuterNorm hmin
  have hattach := A.ordinaryVertexAttachedToLine_of_noZero_oriented_subtriangle
    hA fixedGauge q l a b sigma hal hbl hab hxl hqa hqb hordinary
    hfq hfV1 hfV3 hXbase hV1right hV3left hnozero
  exact ⟨q, hxOuter, hxl, hmin, hattach⟩

/-- Convenience wrapper for the degree-zero case, where every base return
has an extra support. -/
theorem exists_ordinaryAttachment_in_triangleSector
    (A : FiniteProjectiveLineArrangement Line) (hA : A.NonPencil)
    (outerSigma : Line → Bool) (l outerLeft outerRight : Line)
    (houterTriangle : ¬ ∃ r : RealProjectivePoint,
      A.Incident r l ∧ A.Incident r outerLeft ∧
        A.Incident r outerRight)
    (hS : (A.triangleSectorOffBaseVertexSet
      outerSigma l outerLeft outerRight).Nonempty)
    (hreturn : ∀ x : RealProjectivePoint, x ∈ A.vertexSet →
      A.projectivePointMemTriangleSector outerSigma l outerLeft outerRight x →
      ¬ A.Incident x l →
      ∀ c : Line, A.Incident x c → l ≠ c →
        A.projectivePointMemTriangleSector outerSigma l outerLeft outerRight
          (A.intersection l c))
    (hextra : ∀ x : RealProjectivePoint, x ∈ A.vertexSet →
      A.projectivePointMemTriangleSector outerSigma l outerLeft outerRight x →
      ¬ A.Incident x l →
      ∀ c : Line, A.Incident x c → l ≠ c →
        ∃ m : Line, m ≠ l ∧ m ≠ c ∧
          A.Incident (A.intersection l c) m) :
    ∃ q : A.OrdinaryVertex,
      A.projectivePointMemTriangleSector outerSigma l outerLeft outerRight q.1 ∧
      ¬ A.Incident q.1 l ∧
      (∀ y : RealProjectivePoint, y ∈ A.vertexSet →
        A.projectivePointMemTriangleSector
          outerSigma l outerLeft outerRight y →
        ¬ A.Incident y l →
        A.vertexChartLineHeight
            (A.triangleSectorFixedGauge
              outerSigma l outerLeft outerRight) l q.1 ≤
          A.vertexChartLineHeight
            (A.triangleSectorFixedGauge
              outerSigma l outerLeft outerRight) l y) ∧
      A.OrdinaryVertexAttachedToLine q l := by
  apply A.exists_ordinaryAttachment_in_triangleSector_of_middle hA
    outerSigma l outerLeft outerRight houterTriangle hS hreturn
  intro x hxVertex hxOuter hxl _left middle _right
    _hxleft hxmiddle _hxright _hlleft hlmiddle _hlright _h12 _h23
  exact hextra x hxVertex hxOuter hxl middle hxmiddle hlmiddle

/-- Degree-one specialization: the unique ordinary base point is the left
endpoint, so the strictly median return is nonordinary. -/
theorem exists_ordinaryAttachment_in_triangleSector_of_degree_one_leftEndpoint
    (A : FiniteProjectiveLineArrangement Line) (hA : A.NonPencil)
    (outerSigma : Line → Bool) (l outerLeft outerRight : Line)
    (houterTriangle : ¬ ∃ r : RealProjectivePoint,
      A.Incident r l ∧ A.Incident r outerLeft ∧
        A.Incident r outerRight)
    (hone : A.lineOrdinaryVertexDegree l = 1)
    (p : A.OrdinaryVertex) (hpl : A.Incident p.1 l)
    (hpEndpoint : p.1 = A.intersection l outerLeft)
    (hS : (A.triangleSectorOffBaseVertexSet
      outerSigma l outerLeft outerRight).Nonempty)
    (hreturn : ∀ x : RealProjectivePoint, x ∈ A.vertexSet →
      A.projectivePointMemTriangleSector outerSigma l outerLeft outerRight x →
      ¬ A.Incident x l →
      ∀ c : Line, A.Incident x c → l ≠ c →
        A.projectivePointMemTriangleSector outerSigma l outerLeft outerRight
          (A.intersection l c)) :
    ∃ q : A.OrdinaryVertex,
      A.projectivePointMemTriangleSector outerSigma l outerLeft outerRight q.1 ∧
      ¬ A.Incident q.1 l ∧
      (∀ y : RealProjectivePoint, y ∈ A.vertexSet →
        A.projectivePointMemTriangleSector
          outerSigma l outerLeft outerRight y →
        ¬ A.Incident y l →
        A.vertexChartLineHeight
            (A.triangleSectorFixedGauge
              outerSigma l outerLeft outerRight) l q.1 ≤
          A.vertexChartLineHeight
            (A.triangleSectorFixedGauge
              outerSigma l outerLeft outerRight) l y) ∧
      A.OrdinaryVertexAttachedToLine q l := by
  apply A.exists_ordinaryAttachment_in_triangleSector_of_middle hA
    outerSigma l outerLeft outerRight houterTriangle hS hreturn
  intro x hxVertex hxOuter hxl left middle right
    hxleft hxmiddle hxright hlleft hlmiddle hlright h12 h23
  have hleftSector := hreturn x hxVertex hxOuter hxl left hxleft hlleft
  have hlOuterLeft : l ≠ outerLeft := by
    intro hEq
    by_cases hEqR : l = outerRight
    · apply houterTriangle
      refine ⟨A.intersection l middle,
        A.intersection_incident_left hlmiddle, ?_, ?_⟩
      · rw [← hEq]
        exact A.intersection_incident_left hlmiddle
      · rw [← hEqR]
        exact A.intersection_incident_left hlmiddle
    · apply houterTriangle
      refine ⟨A.intersection l outerRight,
        A.intersection_incident_left hEqR, ?_,
        A.intersection_incident_right hEqR⟩
      rw [← hEq]
      exact A.intersection_incident_left hEqR
  exact A.exists_extra_line_at_sector_middle_of_lineDegree_eq_one
    outerSigma l outerLeft outerRight left middle hone
      hlOuterLeft hlmiddle p hpl hpEndpoint houterTriangle hleftSector h12

/-- A retained local-minimum certificate separates its chosen point from
any point admitting a strictly lower sector witness. -/
theorem ne_of_triangleSector_minimal_of_lower_witness
    (A : FiniteProjectiveLineArrangement Line) (sigma : Line → Bool)
    (l a b : Line) (x z w : RealProjectivePoint)
    (hmin : ∀ y : RealProjectivePoint, y ∈ A.vertexSet →
      A.projectivePointMemTriangleSector sigma l a b y →
      ¬ A.Incident y l →
      A.vertexChartLineHeight
          (A.triangleSectorFixedGauge sigma l a b) l x ≤
        A.vertexChartLineHeight
          (A.triangleSectorFixedGauge sigma l a b) l y)
    (hwVertex : w ∈ A.vertexSet)
    (hwSector : A.projectivePointMemTriangleSector sigma l a b w)
    (hwl : ¬ A.Incident w l)
    (hwz : A.vertexChartLineHeight
        (A.triangleSectorFixedGauge sigma l a b) l w <
      A.vertexChartLineHeight
        (A.triangleSectorFixedGauge sigma l a b) l z) :
    x ≠ z := by
  intro hxz
  have hle := hmin w hwVertex hwSector hwl
  rw [hxz] at hle
  exact (not_lt_of_ge hle) hwz

/-- If two closed sectors have only one common off-base projective point,
then points chosen away from that common apex in the two sectors differ. -/
theorem ne_of_mem_outerSectors_of_common_eq
    (A : FiniteProjectiveLineArrangement Line)
    (leftSigma rightSigma : Line → Bool) (l a b : Line)
    (x y z : RealProjectivePoint)
    (hxLeft : A.projectivePointMemTriangleSector leftSigma l a b x)
    (hyRight : A.projectivePointMemTriangleSector rightSigma l a b y)
    (hcommon : ∀ u : RealProjectivePoint,
      A.projectivePointMemTriangleSector leftSigma l a b u →
      A.projectivePointMemTriangleSector rightSigma l a b u →
      ¬ A.Incident u l → u = z)
    (hxl : ¬ A.Incident x l) (hxz : x ≠ z) : x ≠ y := by
  intro hxy
  apply hxz
  apply hcommon x hxLeft
  · simpa only [hxy] using hyRight
  · exact hxl

/-- On the nonnegative side selected by `sigma`, absolute fixed-chart
height is exactly the corresponding oriented base evaluation. -/
theorem vertexChartLineHeight_eq_orientedEvaluation_of_nonneg
    (A : FiniteProjectiveLineArrangement Line) (sigma : Line → Bool)
    (f : (Fin 3 → ℝ) →ₗ[ℝ] ℝ) (l : Line)
    (x : RealProjectivePoint)
    (hbase : 0 ≤ A.arrangementOrientedEvaluation sigma l
      (vertexChartNormalizedVector f x)) :
    A.vertexChartLineHeight f l x =
      A.arrangementOrientedEvaluation sigma l
        (vertexChartNormalizedVector f x) := by
  unfold vertexChartLineHeight
  by_cases hs : sigma l
  · have hraw : 0 ≤ projectiveLineEvaluation (A.projectiveLine l)
        (vertexChartNormalizedVector f x) := by
      simpa [arrangementOrientedEvaluation, hs] using hbase
    rw [abs_of_nonneg hraw]
    simp [arrangementOrientedEvaluation, hs]
  · have hraw : projectiveLineEvaluation (A.projectiveLine l)
        (vertexChartNormalizedVector f x) ≤ 0 := by
      have hneg : 0 ≤ -projectiveLineEvaluation (A.projectiveLine l)
          (vertexChartNormalizedVector f x) := by
        simpa [arrangementOrientedEvaluation, hs] using hbase
      linarith
    rw [abs_of_nonpos hraw]
    simp [arrangementOrientedEvaluation, hs]

/-- A point incident with both non-base sides belongs to every projective
closed sector of the three defining lines. -/
theorem projectivePointMemTriangleSector_of_incident_both_sides
    (A : FiniteProjectiveLineArrangement Line) (sigma : Line → Bool)
    (l a b : Line) (x : RealProjectivePoint)
    (hxa : A.Incident x a) (hxb : A.Incident x b) :
    A.projectivePointMemTriangleSector sigma l a b x := by
  have ha0 : A.arrangementOrientedEvaluation sigma a x.rep = 0 := by
    apply (A.incident_projectivization_mk_iff_orientedEvaluation_eq_zero
      sigma a x.rep x.rep_nonzero).1
    simpa only [x.mk_rep] using hxa
  have hb0 : A.arrangementOrientedEvaluation sigma b x.rep = 0 := by
    apply (A.incident_projectivization_mk_iff_orientedEvaluation_eq_zero
      sigma b x.rep x.rep_nonzero).1
    simpa only [x.mk_rep] using hxb
  by_cases hl : 0 ≤ A.arrangementOrientedEvaluation sigma l x.rep
  · left
    intro m hm
    simp only [Finset.mem_insert, Finset.mem_singleton] at hm
    rcases hm with rfl | rfl | rfl
    · exact hl
    · exact ha0.symm.le
    · exact hb0.symm.le
  · right
    intro m hm
    simp only [Finset.mem_insert, Finset.mem_singleton] at hm
    rcases hm with rfl | rfl | rfl
    · rw [LinearMap.map_neg]
      exact neg_nonneg.mpr (le_of_not_ge hl)
    · rw [LinearMap.map_neg, ha0, neg_zero]
    · rw [LinearMap.map_neg, hb0, neg_zero]

/-- In a normalized closed triangle, a non-apex point of either side has
strictly smaller base height than the opposite apex. -/
theorem vertexChartLineHeight_lt_apex_of_mem_left_side
    (A : FiniteProjectiveLineArrangement Line) (sigma : Line → Bool)
    (l a b : Line)
    (htriangle : ¬ ∃ r : RealProjectivePoint,
      A.Incident r l ∧ A.Incident r a ∧ A.Incident r b)
    (x q : RealProjectivePoint)
    (hxSector : A.projectivePointMemTriangleSector sigma l a b x)
    (hxa : A.Incident x a) (hxb : ¬ A.Incident x b)
    (hqa : A.Incident q a) (hqb : A.Incident q b) :
    A.vertexChartLineHeight
        (A.triangleSectorFixedGauge sigma l a b) l x <
      A.vertexChartLineHeight
        (A.triangleSectorFixedGauge sigma l a b) l q := by
  let f := A.triangleSectorFixedGauge sigma l a b
  have hqSector :=
    A.projectivePointMemTriangleSector_of_incident_both_sides
      sigma l a b q hqa hqb
  have hfx : f x.rep ≠ 0 := by
    simpa only [f, A.triangleSectorFixedGauge_apply] using
      A.triangleSectorGauge_ne_zero_of_projective
        sigma l a b htriangle x hxSector
  have hfq : f q.rep ≠ 0 := by
    simpa only [f, A.triangleSectorFixedGauge_apply] using
      A.triangleSectorGauge_ne_zero_of_projective
        sigma l a b htriangle q hqSector
  have hXcone : vertexChartNormalizedVector f x ∈
      A.arrangementClosedSignConeOn sigma {l, a, b} := by
    simpa only [f,
      A.vertexChartNormalizedVector_triangleSectorFixedGauge] using
      A.triangleSectorNormalizedVector_mem_of_projective
        sigma l a b htriangle x hxSector
  have hQcone : vertexChartNormalizedVector f q ∈
      A.arrangementClosedSignConeOn sigma {l, a, b} := by
    simpa only [f,
      A.vertexChartNormalizedVector_triangleSectorFixedGauge] using
      A.triangleSectorNormalizedVector_mem_of_projective
        sigma l a b htriangle q hqSector
  have hXl : 0 ≤ A.arrangementOrientedEvaluation sigma l
      (vertexChartNormalizedVector f x) := hXcone l (by simp)
  have hXb : 0 < A.arrangementOrientedEvaluation sigma b
      (vertexChartNormalizedVector f x) := by
    have hge := hXcone b (by simp)
    have hne :=
      A.arrangementOrientedEvaluation_vertexChartNormalizedVector_ne_zero
        sigma f hfx hxb
    exact lt_of_le_of_ne hge hne.symm
  have hXa : A.arrangementOrientedEvaluation sigma a
      (vertexChartNormalizedVector f x) = 0 :=
    A.arrangementOrientedEvaluation_vertexChartNormalizedVector_eq_zero
      sigma f hfx hxa
  have hQl : 0 ≤ A.arrangementOrientedEvaluation sigma l
      (vertexChartNormalizedVector f q) := hQcone l (by simp)
  have hQa : A.arrangementOrientedEvaluation sigma a
      (vertexChartNormalizedVector f q) = 0 :=
    A.arrangementOrientedEvaluation_vertexChartNormalizedVector_eq_zero
      sigma f hfq hqa
  have hQb : A.arrangementOrientedEvaluation sigma b
      (vertexChartNormalizedVector f q) = 0 :=
    A.arrangementOrientedEvaluation_vertexChartNormalizedVector_eq_zero
      sigma f hfq hqb
  have hXgauge :=
    vertexChartNormalizedVector_fixedGauge_eq_one f x hfx
  have hQgauge :=
    vertexChartNormalizedVector_fixedGauge_eq_one f q hfq
  have hXsum :
      A.arrangementOrientedEvaluation sigma l
          (vertexChartNormalizedVector f x) +
        A.arrangementOrientedEvaluation sigma a
          (vertexChartNormalizedVector f x) +
        A.arrangementOrientedEvaluation sigma b
          (vertexChartNormalizedVector f x) = 1 := by
    simpa only [f, A.triangleSectorFixedGauge_apply,
      triangleSectorGauge] using hXgauge
  have hQsum :
      A.arrangementOrientedEvaluation sigma l
          (vertexChartNormalizedVector f q) +
        A.arrangementOrientedEvaluation sigma a
          (vertexChartNormalizedVector f q) +
        A.arrangementOrientedEvaluation sigma b
          (vertexChartNormalizedVector f q) = 1 := by
    simpa only [f, A.triangleSectorFixedGauge_apply,
      triangleSectorGauge] using hQgauge
  rw [A.vertexChartLineHeight_eq_orientedEvaluation_of_nonneg
      sigma f l x hXl,
    A.vertexChartLineHeight_eq_orientedEvaluation_of_nonneg
      sigma f l q hQl]
  linarith

theorem vertexChartLineHeight_lt_apex_of_mem_right_side
    (A : FiniteProjectiveLineArrangement Line) (sigma : Line → Bool)
    (l a b : Line)
    (htriangle : ¬ ∃ r : RealProjectivePoint,
      A.Incident r l ∧ A.Incident r a ∧ A.Incident r b)
    (x q : RealProjectivePoint)
    (hxSector : A.projectivePointMemTriangleSector sigma l a b x)
    (hxa : ¬ A.Incident x a) (hxb : A.Incident x b)
    (hqa : A.Incident q a) (hqb : A.Incident q b) :
    A.vertexChartLineHeight
        (A.triangleSectorFixedGauge sigma l a b) l x <
      A.vertexChartLineHeight
        (A.triangleSectorFixedGauge sigma l a b) l q := by
  have htriangle' : ¬ ∃ r : RealProjectivePoint,
      A.Incident r l ∧ A.Incident r b ∧ A.Incident r a := by
    rintro ⟨r, hrl, hrb, hra⟩
    exact htriangle ⟨r, hrl, hra, hrb⟩
  have hxSector' :
      A.projectivePointMemTriangleSector sigma l b a x := by
    unfold projectivePointMemTriangleSector at hxSector ⊢
    have hset : ({l, b, a} : Finset Line) = {l, a, b} := by
      ext k
      simp [or_comm, or_left_comm, or_assoc]
    simpa only [hset] using hxSector
  have hswap : A.triangleSectorFixedGauge sigma l b a =
      A.triangleSectorFixedGauge sigma l a b := by
    apply LinearMap.ext
    intro v
    simp only [A.triangleSectorFixedGauge_apply, triangleSectorGauge]
    ring
  have hlt := A.vertexChartLineHeight_lt_apex_of_mem_left_side
    sigma l b a htriangle' x q hxSector' hxb hxa hqb hqa
  simpa only [hswap] using hlt

/-- A local ordinary minimizer in the left sector of a degree-one
transverse front is not the far triangle apex. -/
theorem OrdinaryAttachmentOuterSectorFront.FelsnerOneLineCleanFrame.TransverseFront.ordinary_minimizer_ne_r_left
    {A : FiniteProjectiveLineArrangement Line} {l : Line}
    {F : OrdinaryAttachmentOuterSectorFront.FelsnerOneLineCleanFrame A l}
    {v : A.CircularGapSlot l}
    (T : F.TransverseFront v) (sigma : Line → Bool)
    (q : A.OrdinaryVertex)
    (hwSector : A.projectivePointMemTriangleSector
      sigma l F.m F.n T.leftWitness)
    (hmin : ∀ y : RealProjectivePoint, y ∈ A.vertexSet →
      A.projectivePointMemTriangleSector sigma l F.m F.n y →
      ¬ A.Incident y l →
      A.vertexChartLineHeight
          (A.triangleSectorFixedGauge sigma l F.m F.n) l q.1 ≤
        A.vertexChartLineHeight
          (A.triangleSectorFixedGauge sigma l F.m F.n) l y) :
    q.1 ≠ F.r := by
  by_cases hw : T.leftWitness = F.r
  · intro hqr
    have hq2 : A.multiplicity q.1 = 2 :=
      (Finset.mem_filter.mp q.2).2
    have hqm : A.Incident q.1 F.m := by
      rw [hqr]
      exact F.r_on_m
    have hqn : A.Incident q.1 F.n := by
      rw [hqr]
      exact F.r_on_n
    have hrCross : A.Incident F.r T.cross := by
      rw [← hw]
      exact T.leftWitness_incident_cross
    have hqCross : A.Incident q.1 T.cross := by
      rw [hqr]
      exact hrCross
    have hexact := A.incident_iff_eq_or_eq_of_multiplicity_eq_two
      q.1 F.m F.n hqm hqn F.n_ne_m hq2 T.cross
    rcases hexact.mp hqCross with h | h
    · exact T.cross_ne_m h
    · exact T.cross_ne_n h
  · have hwNotN : ¬ A.Incident T.leftWitness F.n := by
      intro hwn
      apply hw
      have hEq : T.leftWitness = A.intersection F.m F.n :=
        A.eq_intersection_of_incident F.n_ne_m.symm
          T.leftWitness_incident_m hwn
      exact hEq.trans F.r_eq_intersection.symm
    have hlt := A.vertexChartLineHeight_lt_apex_of_mem_left_side
      sigma l F.m F.n F.boundary_nonconcurrent T.leftWitness F.r hwSector
        T.leftWitness_incident_m hwNotN F.r_on_m F.r_on_n
    exact A.ne_of_triangleSector_minimal_of_lower_witness
      sigma l F.m F.n q.1 F.r T.leftWitness hmin
        T.leftWitness_mem_vertexSet hwSector
        T.leftWitness_away hlt

/-- Symmetric far-apex separation for the right sector. -/
theorem OrdinaryAttachmentOuterSectorFront.FelsnerOneLineCleanFrame.TransverseFront.ordinary_minimizer_ne_r_right
    {A : FiniteProjectiveLineArrangement Line} {l : Line}
    {F : OrdinaryAttachmentOuterSectorFront.FelsnerOneLineCleanFrame A l}
    {v : A.CircularGapSlot l}
    (T : F.TransverseFront v) (sigma : Line → Bool)
    (q : A.OrdinaryVertex)
    (hwSector : A.projectivePointMemTriangleSector
      sigma l F.m F.n T.rightWitness)
    (hmin : ∀ y : RealProjectivePoint, y ∈ A.vertexSet →
      A.projectivePointMemTriangleSector sigma l F.m F.n y →
      ¬ A.Incident y l →
      A.vertexChartLineHeight
          (A.triangleSectorFixedGauge sigma l F.m F.n) l q.1 ≤
        A.vertexChartLineHeight
          (A.triangleSectorFixedGauge sigma l F.m F.n) l y) :
    q.1 ≠ F.r := by
  by_cases hw : T.rightWitness = F.r
  · intro hqr
    have hq2 : A.multiplicity q.1 = 2 :=
      (Finset.mem_filter.mp q.2).2
    have hqm : A.Incident q.1 F.m := by
      rw [hqr]
      exact F.r_on_m
    have hqn : A.Incident q.1 F.n := by
      rw [hqr]
      exact F.r_on_n
    have hrCross : A.Incident F.r T.cross := by
      rw [← hw]
      exact T.rightWitness_incident_cross
    have hqCross : A.Incident q.1 T.cross := by
      rw [hqr]
      exact hrCross
    have hexact := A.incident_iff_eq_or_eq_of_multiplicity_eq_two
      q.1 F.m F.n hqm hqn F.n_ne_m hq2 T.cross
    rcases hexact.mp hqCross with h | h
    · exact T.cross_ne_m h
    · exact T.cross_ne_n h
  · have hwNotM : ¬ A.Incident T.rightWitness F.m := by
      intro hwm
      apply hw
      have hEq : T.rightWitness = A.intersection F.m F.n :=
        A.eq_intersection_of_incident F.n_ne_m.symm
          hwm T.rightWitness_incident_n
      exact hEq.trans F.r_eq_intersection.symm
    have hlt := A.vertexChartLineHeight_lt_apex_of_mem_right_side
      sigma l F.m F.n F.boundary_nonconcurrent T.rightWitness F.r hwSector
        hwNotM T.rightWitness_incident_n F.r_on_m F.r_on_n
    exact A.ne_of_triangleSector_minimal_of_lower_witness
      sigma l F.m F.n q.1 F.r T.rightWitness hmin
        T.rightWitness_mem_vertexSet hwSector
        T.rightWitness_away hlt

theorem OrdinaryAttachmentOuterSectorFront.leftWitness_not_incident_right
    {A : FiniteProjectiveLineArrangement Line}
    {q : A.OrdinaryVertex} {l : Line}
    (F : OrdinaryAttachmentOuterSectorFront A q l) :
    ¬ A.Incident F.leftWitness F.frame.b := by
  intro hright
  apply F.leftWitness_ne_attachment
  have hu : F.leftWitness = A.intersection F.frame.a F.frame.b :=
    A.eq_intersection_of_incident F.frame.a_ne_b
      F.leftWitness_incident_left hright
  have hq : q.1 = A.intersection F.frame.a F.frame.b :=
    A.eq_intersection_of_incident F.frame.a_ne_b
      F.frame.q_on_a F.frame.q_on_b
  exact hu.trans hq.symm

theorem OrdinaryAttachmentOuterSectorFront.rightWitness_not_incident_left
    {A : FiniteProjectiveLineArrangement Line}
    {q : A.OrdinaryVertex} {l : Line}
    (F : OrdinaryAttachmentOuterSectorFront A q l) :
    ¬ A.Incident F.rightWitness F.frame.a := by
  intro hleft
  apply F.rightWitness_ne_attachment
  have hu : F.rightWitness = A.intersection F.frame.a F.frame.b :=
    A.eq_intersection_of_incident F.frame.a_ne_b
      hleft F.rightWitness_incident_right
  have hq : q.1 = A.intersection F.frame.a F.frame.b :=
    A.eq_intersection_of_incident F.frame.a_ne_b
      F.frame.q_on_a F.frame.q_on_b
  exact hu.trans hq.symm

theorem OrdinaryAttachmentOuterSectorFront.leftWitness_height_lt_attachment
    {A : FiniteProjectiveLineArrangement Line}
    {q : A.OrdinaryVertex} {l : Line}
    (F : OrdinaryAttachmentOuterSectorFront A q l)
    (hmem : A.projectivePointMemTriangleSector F.leftOuterSigma
      l F.frame.a F.frame.b F.leftWitness) :
    A.vertexChartLineHeight
        (A.triangleSectorFixedGauge
          F.leftOuterSigma l F.frame.a F.frame.b) l F.leftWitness <
      A.vertexChartLineHeight
        (A.triangleSectorFixedGauge
          F.leftOuterSigma l F.frame.a F.frame.b) l q.1 := by
  exact A.vertexChartLineHeight_lt_apex_of_mem_left_side
    F.leftOuterSigma l F.frame.a F.frame.b F.boundary_nonconcurrent
      F.leftWitness q.1 hmem F.leftWitness_incident_left
      F.leftWitness_not_incident_right F.frame.q_on_a F.frame.q_on_b

theorem OrdinaryAttachmentOuterSectorFront.rightWitness_height_lt_attachment
    {A : FiniteProjectiveLineArrangement Line}
    {q : A.OrdinaryVertex} {l : Line}
    (F : OrdinaryAttachmentOuterSectorFront A q l)
    (hmem : A.projectivePointMemTriangleSector F.rightOuterSigma
      l F.frame.a F.frame.b F.rightWitness) :
    A.vertexChartLineHeight
        (A.triangleSectorFixedGauge
          F.rightOuterSigma l F.frame.a F.frame.b) l F.rightWitness <
      A.vertexChartLineHeight
        (A.triangleSectorFixedGauge
          F.rightOuterSigma l F.frame.a F.frame.b) l q.1 := by
  exact A.vertexChartLineHeight_lt_apex_of_mem_right_side
    F.rightOuterSigma l F.frame.a F.frame.b F.boundary_nonconcurrent
      F.rightWitness q.1 hmem F.rightWitness_not_incident_left
      F.rightWitness_incident_right F.frame.q_on_a F.frame.q_on_b

/-- The canonical sector across `a` contains the transverse witness on
the opposite side `b`; this wrapper turns that membership into the strict
height comparison used to exclude the old apex. -/
theorem OrdinaryAttachmentOuterSectorFront.rightWitness_height_lt_attachment_leftOuter
    {A : FiniteProjectiveLineArrangement Line}
    {q : A.OrdinaryVertex} {l : Line}
    (F : OrdinaryAttachmentOuterSectorFront A q l)
    (hmem : A.projectivePointMemTriangleSector F.leftOuterSigma
      l F.frame.a F.frame.b F.rightWitness) :
    A.vertexChartLineHeight
        (A.triangleSectorFixedGauge
          F.leftOuterSigma l F.frame.a F.frame.b) l F.rightWitness <
      A.vertexChartLineHeight
        (A.triangleSectorFixedGauge
          F.leftOuterSigma l F.frame.a F.frame.b) l q.1 := by
  exact A.vertexChartLineHeight_lt_apex_of_mem_right_side
    F.leftOuterSigma l F.frame.a F.frame.b F.boundary_nonconcurrent
      F.rightWitness q.1 hmem F.rightWitness_not_incident_left
      F.rightWitness_incident_right F.frame.q_on_a F.frame.q_on_b

/-- Symmetric strict-height wrapper for the canonical sector across `b`. -/
theorem OrdinaryAttachmentOuterSectorFront.leftWitness_height_lt_attachment_rightOuter
    {A : FiniteProjectiveLineArrangement Line}
    {q : A.OrdinaryVertex} {l : Line}
    (F : OrdinaryAttachmentOuterSectorFront A q l)
    (hmem : A.projectivePointMemTriangleSector F.rightOuterSigma
      l F.frame.a F.frame.b F.leftWitness) :
    A.vertexChartLineHeight
        (A.triangleSectorFixedGauge
          F.rightOuterSigma l F.frame.a F.frame.b) l F.leftWitness <
      A.vertexChartLineHeight
        (A.triangleSectorFixedGauge
          F.rightOuterSigma l F.frame.a F.frame.b) l q.1 := by
  exact A.vertexChartLineHeight_lt_apex_of_mem_left_side
    F.rightOuterSigma l F.frame.a F.frame.b F.boundary_nonconcurrent
      F.leftWitness q.1 hmem F.leftWitness_incident_left
      F.leftWitness_not_incident_right F.frame.q_on_a F.frame.q_on_b

theorem OrdinaryAttachmentOuterSectorFront.outerEvaluations_base_eq
    {A : FiniteProjectiveLineArrangement Line}
    {q : A.OrdinaryVertex} {l : Line}
    (F : OrdinaryAttachmentOuterSectorFront A q l)
    (v : Fin 3 → ℝ) :
    A.arrangementOrientedEvaluation F.leftOuterSigma l v =
      A.arrangementOrientedEvaluation F.rightOuterSigma l v := by
  simp only [arrangementOrientedEvaluation]
  rw [F.leftOuterSigma_eq_face_of_ne F.frame.a_ne_base.symm,
    F.rightOuterSigma_eq_face_of_ne F.frame.b_ne_base.symm]

theorem OrdinaryAttachmentOuterSectorFront.outerEvaluations_left_neg
    {A : FiniteProjectiveLineArrangement Line}
    {q : A.OrdinaryVertex} {l : Line}
    (F : OrdinaryAttachmentOuterSectorFront A q l)
    (v : Fin 3 → ℝ) :
    A.arrangementOrientedEvaluation F.leftOuterSigma F.frame.a v =
      -A.arrangementOrientedEvaluation F.rightOuterSigma F.frame.a v := by
  by_cases hs : F.attachmentFaceSigma F.frame.a
  · simp [arrangementOrientedEvaluation, leftOuterSigma,
      rightOuterSigma, F.frame.a_ne_b, hs]
  · simp [arrangementOrientedEvaluation, leftOuterSigma,
      rightOuterSigma, F.frame.a_ne_b, hs]

theorem OrdinaryAttachmentOuterSectorFront.outerEvaluations_right_neg
    {A : FiniteProjectiveLineArrangement Line}
    {q : A.OrdinaryVertex} {l : Line}
    (F : OrdinaryAttachmentOuterSectorFront A q l)
    (v : Fin 3 → ℝ) :
    A.arrangementOrientedEvaluation F.leftOuterSigma F.frame.b v =
      -A.arrangementOrientedEvaluation F.rightOuterSigma F.frame.b v := by
  by_cases hs : F.attachmentFaceSigma F.frame.b
  · simp [arrangementOrientedEvaluation, leftOuterSigma,
      rightOuterSigma, F.frame.a_ne_b.symm, hs]
  · simp [arrangementOrientedEvaluation, leftOuterSigma,
      rightOuterSigma, F.frame.a_ne_b.symm, hs]

/-- The two canonical outer closed sectors intersect away from the base only
at the original attachment apex. -/
theorem OrdinaryAttachmentOuterSectorFront.eq_attachment_of_mem_both_outer
    {A : FiniteProjectiveLineArrangement Line}
    {q : A.OrdinaryVertex} {l : Line}
    (F : OrdinaryAttachmentOuterSectorFront A q l)
    (u : RealProjectivePoint)
    (huLeft : A.projectivePointMemTriangleSector F.leftOuterSigma
      l F.frame.a F.frame.b u)
    (huRight : A.projectivePointMemTriangleSector F.rightOuterSigma
      l F.frame.a F.frame.b u)
    (huAway : ¬ A.Incident u l) : u = q.1 := by
  have hzeros : ∀ v : Fin 3 → ℝ,
      v ∈ A.arrangementClosedSignConeOn F.leftOuterSigma
          {l, F.frame.a, F.frame.b} →
      v ∈ A.arrangementClosedSignConeOn F.rightOuterSigma
          {l, F.frame.a, F.frame.b} →
      A.arrangementOrientedEvaluation F.leftOuterSigma F.frame.a v = 0 ∧
        A.arrangementOrientedEvaluation F.leftOuterSigma F.frame.b v = 0 := by
    intro v hleft hright
    have hla := hleft F.frame.a (by simp)
    have hra := hright F.frame.a (by simp)
    have hlb := hleft F.frame.b (by simp)
    have hrb := hright F.frame.b (by simp)
    have haOpp := F.outerEvaluations_left_neg v
    have hbOpp := F.outerEvaluations_right_neg v
    constructor <;> linarith
  have hpoint :
      A.arrangementOrientedEvaluation F.leftOuterSigma F.frame.a u.rep = 0 →
      A.arrangementOrientedEvaluation F.leftOuterSigma F.frame.b u.rep = 0 →
      u = q.1 := by
    intro ha0 hb0
    have hua : A.Incident u F.frame.a := by
      have hmk :=
        (A.incident_projectivization_mk_iff_orientedEvaluation_eq_zero
          F.leftOuterSigma F.frame.a u.rep u.rep_nonzero).2 ha0
      simpa only [u.mk_rep] using hmk
    have hub : A.Incident u F.frame.b := by
      have hmk :=
        (A.incident_projectivization_mk_iff_orientedEvaluation_eq_zero
          F.leftOuterSigma F.frame.b u.rep u.rep_nonzero).2 hb0
      simpa only [u.mk_rep] using hmk
    have hu : u = A.intersection F.frame.a F.frame.b :=
      A.eq_intersection_of_incident F.frame.a_ne_b hua hub
    have hq : q.1 = A.intersection F.frame.a F.frame.b :=
      A.eq_intersection_of_incident F.frame.a_ne_b
        F.frame.q_on_a F.frame.q_on_b
    exact hu.trans hq.symm
  rcases huLeft with hleft | hleft <;>
    rcases huRight with hright | hright
  · exact hpoint (hzeros u.rep hleft hright).1
      (hzeros u.rep hleft hright).2
  · exfalso
    apply huAway
    have hl := hleft l (by simp)
    have hr := hright l (by simp)
    have heq := F.outerEvaluations_base_eq u.rep
    have hr' : 0 ≤ -A.arrangementOrientedEvaluation
        F.rightOuterSigma l u.rep := by
      simpa only [LinearMap.map_neg] using hr
    have hz : A.arrangementOrientedEvaluation
        F.leftOuterSigma l u.rep = 0 := by
      linarith
    have hmk :=
      (A.incident_projectivization_mk_iff_orientedEvaluation_eq_zero
        F.leftOuterSigma l u.rep u.rep_nonzero).2 hz
    simpa only [u.mk_rep] using hmk
  · exfalso
    apply huAway
    have hl := hleft l (by simp)
    have hr := hright l (by simp)
    have heq := F.outerEvaluations_base_eq u.rep
    have hl' : 0 ≤ -A.arrangementOrientedEvaluation
        F.leftOuterSigma l u.rep := by
      simpa only [LinearMap.map_neg] using hl
    have hz : A.arrangementOrientedEvaluation
        F.leftOuterSigma l u.rep = 0 := by
      linarith
    have hmk :=
      (A.incident_projectivization_mk_iff_orientedEvaluation_eq_zero
        F.leftOuterSigma l u.rep u.rep_nonzero).2 hz
    simpa only [u.mk_rep] using hmk
  · have hz := hzeros (-u.rep) hleft hright
    apply hpoint
    · simpa only [LinearMap.map_neg, neg_eq_zero] using hz.1
    · simpa only [LinearMap.map_neg, neg_eq_zero] using hz.2

/-- Complete degree-zero counting assembly once the two transverse witnesses
are placed in the canonical, cross-matched outer sectors. -/
theorem three_le_lineOrdinaryAttachmentDegree_of_outerSectorFront_degree_zero
    (A : FiniteProjectiveLineArrangement Line) (hA : A.NonPencil)
    {q : A.OrdinaryVertex} {l : Line}
    (hzero : A.lineOrdinaryVertexDegree l = 0)
    (F : OrdinaryAttachmentOuterSectorFront A q l)
    (hleftWitness : A.projectivePointMemTriangleSector F.leftOuterSigma
      l F.frame.a F.frame.b F.rightWitness)
    (hrightWitness : A.projectivePointMemTriangleSector F.rightOuterSigma
      l F.frame.a F.frame.b F.leftWitness) :
    3 ≤ A.lineOrdinaryAttachmentDegree l := by
  classical
  have hleftS : (A.triangleSectorOffBaseVertexSet F.leftOuterSigma
      l F.frame.a F.frame.b).Nonempty := by
    refine ⟨F.rightWitness, Finset.mem_filter.mpr ?_⟩
    exact ⟨F.rightWitness_mem_vertexSet, hleftWitness,
      F.rightWitness_away⟩
  have hrightS : (A.triangleSectorOffBaseVertexSet F.rightOuterSigma
      l F.frame.a F.frame.b).Nonempty := by
    refine ⟨F.leftWitness, Finset.mem_filter.mpr ?_⟩
    exact ⟨F.leftWitness_mem_vertexSet, hrightWitness,
      F.leftWitness_away⟩
  obtain ⟨qLeft, hqLeftSector, hqLeftAway, hqLeftMin, hqLeftAttach⟩ :=
    A.exists_ordinaryAttachment_in_triangleSector hA F.leftOuterSigma
      l F.frame.a F.frame.b F.boundary_nonconcurrent hleftS
      (fun x hxVertex hxOuter hxl c hxc hlc =>
        F.leftOuter_return_mem hA x hxVertex hxOuter hxl c hxc hlc)
      (by
        intro x hxVertex hxOuter hxl c hxc hlc
        exact A.exists_extra_line_at_base_return_of_lineDegree_eq_zero
          l c hzero hlc)
  obtain ⟨qRight, hqRightSector, hqRightAway, hqRightMin,
      hqRightAttach⟩ :=
    A.exists_ordinaryAttachment_in_triangleSector hA F.rightOuterSigma
      l F.frame.a F.frame.b F.boundary_nonconcurrent hrightS
      (fun x hxVertex hxOuter hxl c hxc hlc =>
        F.rightOuter_return_mem hA x hxVertex hxOuter hxl c hxc hlc)
      (by
        intro x hxVertex hxOuter hxl c hxc hlc
        exact A.exists_extra_line_at_base_return_of_lineDegree_eq_zero
          l c hzero hlc)
  have hqLeftNeVal : qLeft.1 ≠ q.1 :=
    A.ne_of_triangleSector_minimal_of_lower_witness
      F.leftOuterSigma l F.frame.a F.frame.b qLeft.1 q.1
        F.rightWitness hqLeftMin F.rightWitness_mem_vertexSet
        hleftWitness F.rightWitness_away
        (F.rightWitness_height_lt_attachment_leftOuter hleftWitness)
  have hqRightNeVal : qRight.1 ≠ q.1 :=
    A.ne_of_triangleSector_minimal_of_lower_witness
      F.rightOuterSigma l F.frame.a F.frame.b qRight.1 q.1
        F.leftWitness hqRightMin F.leftWitness_mem_vertexSet
        hrightWitness F.leftWitness_away
        (F.leftWitness_height_lt_attachment_rightOuter hrightWitness)
  have hqLeftRightVal : qLeft.1 ≠ qRight.1 := by
    intro heq
    apply hqLeftNeVal
    exact F.eq_attachment_of_mem_both_outerSectors qLeft.1
      hqLeftSector (by simpa only [heq] using hqRightSector) hqLeftAway
  have hqLeft : q ≠ qLeft := by
    intro heq
    exact hqLeftNeVal (congrArg Subtype.val heq).symm
  have hqRight : q ≠ qRight := by
    intro heq
    exact hqRightNeVal (congrArg Subtype.val heq).symm
  have hqLeftRight : qLeft ≠ qRight := by
    intro heq
    exact hqLeftRightVal (congrArg Subtype.val heq)
  exact A.three_le_lineOrdinaryAttachmentDegree_of_pairwise l
    q qLeft qRight hqLeft hqRight hqLeftRight
      ⟨F.attachment⟩ hqLeftAttach hqRightAttach

/-- Felsner's degree-zero clause, now with no geometric callback: a closest
ordinary attachment and the two canonical outer sectors give three pairwise
different ordinary vertices attached to the base. -/
theorem three_le_lineOrdinaryAttachmentDegree_of_degree_zero
    (A : FiniteProjectiveLineArrangement Line) (hA : A.NonPencil)
    (l : Line) (hthree : 3 ≤ (A.lineVertexSet l).card)
    (hzero : A.lineOrdinaryVertexDegree l = 0) :
    3 ≤ A.lineOrdinaryAttachmentDegree l := by
  classical
  obtain ⟨fixedGauge, hgauge, q, hqaway, hbasePos, hmin⟩ :=
    A.exists_closest_offLineOrdinaryVertex_base_pos_of_degree_zero
      hA l hzero
  have hqAttach := A.ordinaryVertexAttachedToLine_of_global_minimal_base_pos
    hA fixedGauge q l hgauge hqaway hbasePos hmin
  obtain ⟨w⟩ := hqAttach
  have hslotCard : Fintype.card (A.CircularGapSlot l) =
      (A.lineVertexSet l).card :=
    Fintype.card_coe (A.lineVertexSet l)
  have hslot : 3 ≤ Fintype.card (A.CircularGapSlot l) := by
    rw [hslotCard]
    exact hthree
  obtain ⟨F⟩ :=
    OrdinaryAttachmentWitness.exists_outerSectorFront A hA w hslot
  exact A.three_le_lineOrdinaryAttachmentDegree_of_outerSectorFront_degree_zero
    hA hzero F (F.rightWitness_mem_leftOuterSector hA)
      (F.leftWitness_mem_rightOuterSector hA)

private theorem multiplicity_intersection_eq_two_of_three_lines
    (A : FiniteProjectiveLineArrangement Line) {l m k : Line}
    (hlm : l ≠ m)
    (hcover : ∀ c : Line, c = l ∨ c = m ∨ c = k)
    (hk : ¬ A.Incident (A.intersection l m) k) :
    A.multiplicity (A.intersection l m) = 2 := by
  classical
  unfold multiplicity
  have hfilter :
      (Finset.univ.filter fun c => A.Incident (A.intersection l m) c) =
        {l, m} := by
    ext c
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_insert, Finset.mem_singleton]
    constructor
    · intro hc
      rcases hcover c with rfl | rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr rfl
      · exact (hk hc).elim
    · rintro (rfl | rfl)
      · exact A.intersection_incident_left hlm
      · exact A.intersection_incident_right hlm
  rw [hfilter]
  simp [hlm]

/-- The only non-pencil arrangement below the low-line threshold has exactly
three nonconcurrent lines, hence three ordinary pair intersections. -/
theorem three_mul_card_le_seven_mul_card_ordinaryVertex_of_card_eq_three
    (A : FiniteProjectiveLineArrangement Line) (hA : A.NonPencil)
    (hcard : Fintype.card Line = 3) :
    3 * Fintype.card Line ≤ 7 * Fintype.card A.OrdinaryVertex := by
  classical
  obtain ⟨l, m, k, hlm, hk⟩ := A.exists_nonconcurrent_triple hA
  have hlk : l ≠ k := by
    intro h
    subst k
    exact hk (A.intersection_incident_left hlm)
  have hmk : m ≠ k := by
    intro h
    subst k
    exact hk (A.intersection_incident_right hlm)
  have huniv : (Finset.univ : Finset Line) = {l, m, k} := by
    symm
    apply Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
    rw [Finset.card_univ, hcard]
    simp [hlm, hlk, hmk, hlk.symm, hmk.symm]
  have hcover (c : Line) : c = l ∨ c = m ∨ c = k := by
    have hc : c ∈ ({l, m, k} : Finset Line) := by
      rw [← huniv]
      exact Finset.mem_univ c
    simpa only [Finset.mem_insert, Finset.mem_singleton] using hc
  have hnotM : ¬ A.Incident (A.intersection l k) m := by
    intro h
    have heq : A.intersection l k = A.intersection l m :=
      A.eq_intersection_of_incident hlm
        (A.intersection_incident_left hlk) h
    apply hk
    rw [← heq]
    exact A.intersection_incident_right hlk
  have hnotL : ¬ A.Incident (A.intersection m k) l := by
    intro h
    have heq : A.intersection m k = A.intersection l m :=
      A.eq_intersection_of_incident hlm h
        (A.intersection_incident_left hmk)
    apply hk
    rw [← heq]
    exact A.intersection_incident_right hmk
  have hLM2 : A.multiplicity (A.intersection l m) = 2 :=
    A.multiplicity_intersection_eq_two_of_three_lines hlm hcover hk
  have hLK2 : A.multiplicity (A.intersection l k) = 2 := by
    apply A.multiplicity_intersection_eq_two_of_three_lines hlk
    · intro c
      rcases hcover c with h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inr h)
      · exact Or.inr (Or.inl h)
    · exact hnotM
  have hMK2 : A.multiplicity (A.intersection m k) = 2 := by
    apply A.multiplicity_intersection_eq_two_of_three_lines hmk
    · intro c
      rcases hcover c with h | h | h
      · exact Or.inr (Or.inr h)
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
    · exact hnotL
  let qLM : A.OrdinaryVertex :=
    ⟨A.intersection l m, Finset.mem_filter.mpr
      ⟨A.intersection_mem_vertexSet hlm, hLM2⟩⟩
  let qLK : A.OrdinaryVertex :=
    ⟨A.intersection l k, Finset.mem_filter.mpr
      ⟨A.intersection_mem_vertexSet hlk, hLK2⟩⟩
  let qMK : A.OrdinaryVertex :=
    ⟨A.intersection m k, Finset.mem_filter.mpr
      ⟨A.intersection_mem_vertexSet hmk, hMK2⟩⟩
  have hLM_LK : qLM ≠ qLK := by
    intro h
    apply hk
    have hv := congrArg Subtype.val h
    change A.intersection l m = A.intersection l k at hv
    rw [hv]
    exact A.intersection_incident_right hlk
  have hLM_MK : qLM ≠ qMK := by
    intro h
    apply hk
    have hv := congrArg Subtype.val h
    change A.intersection l m = A.intersection m k at hv
    rw [hv]
    exact A.intersection_incident_right hmk
  have hLK_MK : qLK ≠ qMK := by
    intro h
    apply hnotL
    have hv := congrArg Subtype.val h
    change A.intersection l k = A.intersection m k at hv
    rw [← hv]
    exact A.intersection_incident_left hlk
  have hord : 3 ≤ Fintype.card A.OrdinaryVertex := by
    calc
      3 = ({qLM, qLK, qMK} : Finset A.OrdinaryVertex).card := by
        simp [hLM_LK, hLM_MK, hLK_MK]
      _ ≤ (Finset.univ : Finset A.OrdinaryVertex).card :=
        Finset.card_le_card (Finset.subset_univ _)
      _ = Fintype.card A.OrdinaryVertex := by simp
  omega

/-- In the high-line branch, the only remaining local input is Felsner's
degree-one `(1,2+)` clause. -/
theorem three_mul_card_le_seven_mul_card_ordinaryVertex_of_highLines_and_one
    (A : FiniteProjectiveLineArrangement Line) (hA : A.NonPencil)
    (hhigh : ∀ l : Line, 3 ≤ (A.lineVertexSet l).card)
    (hone : ∀ l : Line, A.lineOrdinaryVertexDegree l = 1 →
      2 ≤ A.lineOrdinaryAttachmentDegree l) :
    3 * Fintype.card Line ≤ 7 * Fintype.card A.OrdinaryVertex := by
  apply A.three_mul_card_le_seven_mul_card_ordinaryVertex_of_zero_one hA
  · intro l hzero
    exact A.three_le_lineOrdinaryAttachmentDegree_of_degree_zero
      hA l (hhigh l) hzero
  · exact hone

/-- Final finite router once the degree-one local clause is available.  The
three-line case is separated because the low-line product bound starts at
four indexed lines. -/
theorem three_mul_card_le_seven_mul_card_ordinaryVertex_of_one
    (A : FiniteProjectiveLineArrangement Line) (hA : A.NonPencil)
    (hone : ∀ l : Line, A.lineOrdinaryVertexDegree l = 1 →
      2 ≤ A.lineOrdinaryAttachmentDegree l) :
    3 * Fintype.card Line ≤ 7 * Fintype.card A.OrdinaryVertex := by
  have hthreeCard := A.three_le_card_of_nonPencil hA
  by_cases hfour : 4 ≤ Fintype.card Line
  · by_cases hhigh : ∀ l : Line, 3 ≤ (A.lineVertexSet l).card
    · exact A.three_mul_card_le_seven_mul_card_ordinaryVertex_of_highLines_and_one
        hA hhigh hone
    · push_neg at hhigh
      obtain ⟨l, hlow⟩ := hhigh
      exact A.three_mul_card_le_seven_mul_card_ordinaryVertex_of_lineVertexSet_card_le_two
        hA hfour l (by omega)
  · have hcard : Fintype.card Line = 3 := by omega
    exact A.three_mul_card_le_seven_mul_card_ordinaryVertex_of_card_eq_three
      hA hcard

/-- Three distinct supports through an off-base sector point can be sorted by
the intrinsic affine parameter on that sector's base arc. -/
theorem exists_sectorExit_ordered_three_incident_supports
    (A : FiniteProjectiveLineArrangement Line) (sigma : Line → Bool)
    (l outerLeft outerRight : Line)
    (htriangle : ¬ ∃ r : RealProjectivePoint,
      A.Incident r l ∧ A.Incident r outerLeft ∧
        A.Incident r outerRight)
    (x : RealProjectivePoint) (a b c : Line)
    (hxl : ¬ A.Incident x l)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hxa : A.Incident x a) (hxb : A.Incident x b)
    (hxc : A.Incident x c)
    (hVa : A.projectivePointMemTriangleSector sigma l outerLeft outerRight
      (A.intersection l a))
    (hVb : A.projectivePointMemTriangleSector sigma l outerLeft outerRight
      (A.intersection l b))
    (hVc : A.projectivePointMemTriangleSector sigma l outerLeft outerRight
      (A.intersection l c)) :
    ∃ left middle right : Line,
      l ≠ left ∧ l ≠ middle ∧ l ≠ right ∧
      A.Incident x left ∧ A.Incident x middle ∧ A.Incident x right ∧
      A.projectivePointMemTriangleSector sigma l outerLeft outerRight
        (A.intersection l left) ∧
      A.projectivePointMemTriangleSector sigma l outerLeft outerRight
        (A.intersection l middle) ∧
      A.projectivePointMemTriangleSector sigma l outerLeft outerRight
        (A.intersection l right) ∧
      A.sectorExitBaseParameter sigma l outerLeft outerRight
          (A.intersection l left) <
        A.sectorExitBaseParameter sigma l outerLeft outerRight
          (A.intersection l middle) ∧
      A.sectorExitBaseParameter sigma l outerLeft outerRight
          (A.intersection l middle) <
        A.sectorExitBaseParameter sigma l outerLeft outerRight
          (A.intersection l right) := by
  have hla : l ≠ a := fun h => hxl (h ▸ hxa)
  have hlb : l ≠ b := fun h => hxl (h ▸ hxb)
  have hlc : l ≠ c := fun h => hxl (h ▸ hxc)
  have hpab := A.intersection_base_ne_of_distinct_supports
    x l a b hxl hxa hxb hab
  have hpac := A.intersection_base_ne_of_distinct_supports
    x l a c hxl hxa hxc hac
  have hpbc := A.intersection_base_ne_of_distinct_supports
    x l b c hxl hxb hxc hbc
  have htab : A.sectorExitBaseParameter sigma l outerLeft outerRight
      (A.intersection l a) ≠
      A.sectorExitBaseParameter sigma l outerLeft outerRight
        (A.intersection l b) := by
    intro heq
    exact hpab (A.sectorExitBaseParameter_eq_imp_eq sigma l outerLeft
      outerRight htriangle hVa hVb
      (A.intersection_incident_left hla)
      (A.intersection_incident_left hlb) heq)
  have htac : A.sectorExitBaseParameter sigma l outerLeft outerRight
      (A.intersection l a) ≠
      A.sectorExitBaseParameter sigma l outerLeft outerRight
        (A.intersection l c) := by
    intro heq
    exact hpac (A.sectorExitBaseParameter_eq_imp_eq sigma l outerLeft
      outerRight htriangle hVa hVc
      (A.intersection_incident_left hla)
      (A.intersection_incident_left hlc) heq)
  have htbc : A.sectorExitBaseParameter sigma l outerLeft outerRight
      (A.intersection l b) ≠
      A.sectorExitBaseParameter sigma l outerLeft outerRight
        (A.intersection l c) := by
    intro heq
    exact hpbc (A.sectorExitBaseParameter_eq_imp_eq sigma l outerLeft
      outerRight htriangle hVb hVc
      (A.intersection_incident_left hlb)
      (A.intersection_incident_left hlc) heq)
  rcases lt_or_gt_of_ne htab with hab' | hba'
  · rcases lt_or_gt_of_ne htbc with hbc' | hcb'
    · exact ⟨a, b, c, hla, hlb, hlc, hxa, hxb, hxc,
        hVa, hVb, hVc, hab', hbc'⟩
    · rcases lt_or_gt_of_ne htac with hac' | hca'
      · exact ⟨a, c, b, hla, hlc, hlb, hxa, hxc, hxb,
          hVa, hVc, hVb, hac', hcb'⟩
      · exact ⟨c, a, b, hlc, hla, hlb, hxc, hxa, hxb,
          hVc, hVa, hVb, hca', hab'⟩
  · rcases lt_or_gt_of_ne htac with hac' | hca'
    · exact ⟨b, a, c, hlb, hla, hlc, hxb, hxa, hxc,
        hVb, hVa, hVc, hba', hac'⟩
    · rcases lt_or_gt_of_ne htbc with hbc' | hcb'
      · exact ⟨b, c, a, hlb, hlc, hla, hxb, hxc, hxa,
          hVb, hVc, hVa, hbc', hca'⟩
      · exact ⟨c, b, a, hlc, hlb, hla, hxc, hxb, hxa,
          hVc, hVb, hVa, hcb', hba'⟩

/-- Actual ordered exit under the five-point local gauge contract. -/
private theorem fixedChartExit_axis_ordered_of_localGauge_localProof
    (A : FiniteProjectiveLineArrangement Line) (sigma : Line → Bool)
    (fixedGauge : (Fin 3 → ℝ) →ₗ[ℝ] ℝ)
    (l axis left right middle m : Line) (x : RealProjectivePoint)
    (hfx : fixedGauge x.rep ≠ 0)
    (hfv1 : fixedGauge (A.intersection l left).rep ≠ 0)
    (hfv2 : fixedGauge (A.intersection l middle).rep ≠ 0)
    (hfv3 : fixedGauge (A.intersection l right).rep ≠ 0)
    (hfaxis : fixedGauge (A.intersection l axis).rep ≠ 0)
    (hlaxis : l ≠ axis) (hlleft : l ≠ left)
    (hlright : l ≠ right) (hlmiddle : l ≠ middle)
    (hml : m ≠ l) (hmc : m ≠ middle)
    (hxNotBase : ¬ A.Incident x l)
    (hxleft : A.Incident x left) (hxright : A.Incident x right)
    (hxmiddle : A.Incident x middle)
    (hV2m : A.Incident (A.intersection l middle) m)
    (h12 : A.fixedChartBaseParameter sigma fixedGauge axis
        (A.intersection l left) <
      A.fixedChartBaseParameter sigma fixedGauge axis
        (A.intersection l middle))
    (h23 : A.fixedChartBaseParameter sigma fixedGauge axis
        (A.intersection l middle) <
      A.fixedChartBaseParameter sigma fixedGauge axis
        (A.intersection l right)) :
    ∃ y : RealProjectivePoint, ∃ h : ℝ,
      0 < h ∧ h < 1 ∧ y ∈ A.vertexSet ∧
      A.Incident y m ∧ ¬ A.Incident y l ∧
      A.vertexChartLineHeight fixedGauge l y =
        h * A.vertexChartLineHeight fixedGauge l x ∧
      A.vertexChartLineHeight fixedGauge l y <
        A.vertexChartLineHeight fixedGauge l x ∧
      ((A.Incident y left ∧
        vertexChartNormalizedVector fixedGauge y =
          (1 - h) • vertexChartNormalizedVector fixedGauge
              (A.intersection l left) +
            h • vertexChartNormalizedVector fixedGauge x) ∨
       (A.Incident y right ∧
        vertexChartNormalizedVector fixedGauge y =
          (1 - h) • vertexChartNormalizedVector fixedGauge
              (A.intersection l right) +
            h • vertexChartNormalizedVector fixedGauge x)) := by
  have houter : m ≠ left ∧ m ≠ right := by
    constructor
    · intro hm
      subst m
      have heq : A.intersection l middle = A.intersection l left :=
        A.eq_intersection_of_incident hlleft
          (A.intersection_incident_left hlmiddle) hV2m
      rw [heq] at h12
      exact lt_irrefl _ h12
    · intro hm
      subst m
      have heq : A.intersection l middle = A.intersection l right :=
        A.eq_intersection_of_incident hlright
          (A.intersection_incident_left hlmiddle) hV2m
      rw [heq] at h23
      exact lt_irrefl _ h23
  rcases A.fixedChartExit_barycentric_axis_ordered_of_localGauge
      sigma fixedGauge l axis left right middle m x
      hfx hfv1 hfv2 hfv3 hfaxis hlaxis hlleft hlright hlmiddle
      hml hmc hxNotBase hxleft hxright hxmiddle hV2m h12 h23 with
    hleft | hright
  · rcases hleft with ⟨h, Y, hh0, hh1, hY, hY0, hYm, hYleft⟩
    have hVbase :=
      A.arrangementOrientedEvaluation_vertexChartNormalizedVector_eq_zero
        sigma fixedGauge hfv1 (A.intersection_incident_left hlleft)
    have hVgauge := vertexChartNormalizedVector_fixedGauge_eq_one
      fixedGauge (A.intersection l left) hfv1
    have hXgauge := vertexChartNormalizedVector_fixedGauge_eq_one
      fixedGauge x hfx
    have hXbase :=
      A.arrangementOrientedEvaluation_vertexChartNormalizedVector_ne_zero
        sigma fixedGauge hfx hxNotBase
    obtain ⟨y, hyVertex, hym, hyleft, hyNotBase, hyNorm,
        hyHeight, hyLt⟩ :=
      A.fixedChartExit_finish_branch sigma fixedGauge l m left x
        hh0 hh1 hY hY0 houter.1 hYm hYleft hVbase hVgauge
        hXgauge hXbase rfl
    exact ⟨y, h, hh0, hh1, hyVertex, hym, hyNotBase,
      hyHeight, hyLt, Or.inl ⟨hyleft, by simpa only [hY] using hyNorm⟩⟩
  · rcases hright with ⟨h, Y, hh0, hh1, hY, hY0, hYm, hYright⟩
    have hVbase :=
      A.arrangementOrientedEvaluation_vertexChartNormalizedVector_eq_zero
        sigma fixedGauge hfv3 (A.intersection_incident_left hlright)
    have hVgauge := vertexChartNormalizedVector_fixedGauge_eq_one
      fixedGauge (A.intersection l right) hfv3
    have hXgauge := vertexChartNormalizedVector_fixedGauge_eq_one
      fixedGauge x hfx
    have hXbase :=
      A.arrangementOrientedEvaluation_vertexChartNormalizedVector_ne_zero
        sigma fixedGauge hfx hxNotBase
    obtain ⟨y, hyVertex, hym, hyright, hyNotBase, hyNorm,
        hyHeight, hyLt⟩ :=
      A.fixedChartExit_finish_branch sigma fixedGauge l m right x
        hh0 hh1 hY hY0 houter.2 hYm hYright hVbase hVgauge
        hXgauge hXbase rfl
    exact ⟨y, h, hh0, hh1, hyVertex, hym, hyNotBase,
      hyHeight, hyLt, Or.inr ⟨hyright, by simpa only [hY] using hyNorm⟩⟩

end FiniteProjectiveLineArrangement

end Erdos506.Incidence
