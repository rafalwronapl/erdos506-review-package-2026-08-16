import Erdos506.Incidence.RealProjectiveArrangementKellyMoserOuterFinish
import Erdos506.Incidence.RealProjectiveEvenArrangementColorFinish

/-!
# The minimizer-to-attachment form of Felsner's three-clause

Changing the affine normalization line of a complement point either keeps
all oriented half-spaces or reverses all of them.  Hence it is enough to
exclude transverse zeros in one normalization.  The fixed-chart triangle
exit excludes such a zero below a globally closest ordinary apex, and the
existing face materialization then produces a literal attachment witness.
-/

namespace Erdos506.Incidence

namespace FiniteProjectiveLineArrangement

variable {Line : Type*} [Fintype Line] [DecidableEq Line]

/-- Reversing every Boolean sign is the same as negating every oriented
evaluation covector. -/
theorem arrangementOrientedEvaluation_boolNot
    (A : FiniteProjectiveLineArrangement Line) (sigma : Line -> Bool)
    (l : Line) :
    A.arrangementOrientedEvaluation (fun k => !(sigma k)) l =
      -A.arrangementOrientedEvaluation sigma l := by
  by_cases hl : sigma l <;>
    simp [arrangementOrientedEvaluation, hl]

/-- Pointwise form convenient for transporting strict sign cones through a
global reversal of their sign word. -/
theorem arrangementOrientedEvaluation_boolNot_apply
    (A : FiniteProjectiveLineArrangement Line) (sigma : Line -> Bool)
    (l : Line) (v : Fin 3 -> Real) :
    A.arrangementOrientedEvaluation (fun k => !(sigma k)) l v =
      A.arrangementOrientedEvaluation sigma l (-v) := by
  rw [A.arrangementOrientedEvaluation_boolNot]
  simp

/-- A transverse-zero exclusion proved with one normalization line holds
with every normalization line.  The only nontrivial case sends `v` to
`-v`, because changing the base reverses the whole sign word at once. -/
theorem noAdditionalZero_allBases_of_one
    (A : FiniteProjectiveLineArrangement Line)
    (p : A.ArrangementComplement) (base : Line) (K : Finset Line)
    (hzero : ∀ m : Line, m ∉ K →
      ∀ v ∈ A.arrangementSignConeOn
          (A.arrangementPointSignPattern base p) K,
        A.arrangementOrientedEvaluation
          (A.arrangementPointSignPattern base p) m v ≠ 0) :
    ∀ other m : Line, m ∉ K →
      ∀ v ∈ A.arrangementSignConeOn
          (A.arrangementPointSignPattern other p) K,
        A.arrangementOrientedEvaluation
          (A.arrangementPointSignPattern other p) m v ≠ 0 := by
  intro other m hm v hv
  by_cases hsame :
      A.arrangementPointSignPattern base p other = true
  · have hpattern : A.arrangementPointSignPattern other p =
        A.arrangementPointSignPattern base p := by
      funext k
      rw [A.arrangementPointSignPattern_base_change_apply base other p k]
      simp [hsame]
    rw [hpattern] at hv ⊢
    exact hzero m hm v hv
  · have hfalse :
        A.arrangementPointSignPattern base p other = false :=
      Bool.eq_false_of_not_eq_true hsame
    have hpattern : A.arrangementPointSignPattern other p =
        fun k => !(A.arrangementPointSignPattern base p k) := by
      funext k
      rw [A.arrangementPointSignPattern_base_change_apply base other p k]
      simp [hfalse]
    have hnegv : -v ∈ A.arrangementSignConeOn
        (A.arrangementPointSignPattern base p) K := by
      intro k hk
      have hvk := hv k hk
      rw [hpattern,
        A.arrangementOrientedEvaluation_boolNot_apply] at hvk
      exact hvk
    have h := hzero m hm (-v) hnegv
    rw [hpattern, A.arrangementOrientedEvaluation_boolNot_apply]
    exact h

/-- The side-exit contradicts global minimality, so the strict triangle
below a closest ordinary apex contains no transverse arrangement zero. -/
theorem noAdditionalZero_of_minimal_fixedChartLineHeight
    (A : FiniteProjectiveLineArrangement Line) (sigma : Line -> Bool)
    (fixedGauge : (Fin 3 → Real) →ₗ[Real] Real)
    (q : A.OrdinaryVertex) (l a b : Line)
    (htriangle : ¬ ∃ r : RealProjectivePoint,
      A.Incident r l ∧ A.Incident r a ∧ A.Incident r b)
    (hla : l ≠ a) (hlb : l ≠ b) (hab : a ≠ b)
    (hqaway : ¬ A.Incident q.1 l)
    (hqa : A.Incident q.1 a) (hqb : A.Incident q.1 b)
    (hordinary : forall k : Line,
      A.Incident q.1 k ↔ k = a ∨ k = b)
    (hfq : fixedGauge q.1.rep ≠ 0)
    (hfV1 : fixedGauge (A.intersection l a).rep ≠ 0)
    (hfV3 : fixedGauge (A.intersection l b).rep ≠ 0)
    (hXbase : 0 < A.arrangementOrientedEvaluation sigma l
      (vertexChartNormalizedVector fixedGauge q.1))
    (hV1right : 0 < A.arrangementOrientedEvaluation sigma b
      (vertexChartNormalizedVector fixedGauge (A.intersection l a)))
    (hV3left : 0 < A.arrangementOrientedEvaluation sigma a
      (vertexChartNormalizedVector fixedGauge (A.intersection l b)))
    (hmin : forall y : RealProjectivePoint, y ∈ A.vertexSet ->
      ¬ A.Incident y l ->
      A.vertexChartLineHeight fixedGauge l q.1 ≤
        A.vertexChartLineHeight fixedGauge l y) :
    ∀ m : Line, m ∉ ({l, a, b} : Finset Line) →
      ∀ Z ∈ A.arrangementSignConeOn sigma {l, a, b},
        A.arrangementOrientedEvaluation sigma m Z ≠ 0 := by
  intro m hm Z hZ hZm
  obtain ⟨y, _h, _hh0, _hh1, hyVertex, hyl, hylt, _hbranch⟩ :=
    A.exists_smaller_vertex_of_additional_zero
      sigma fixedGauge q l a b m Z htriangle hla hlb hab hm
      hqaway hqa hqb hordinary hfq hfV1 hfV3
      hXbase hV1right hV3left hZ hZm
  exact (not_lt_of_ge (hmin y hyVertex hyl)) hylt

/-- Local-sector version of the minimizer argument.  It is enough that the
fixed-gauge representatives of the apex and the two lower endpoints lie in
one outer closed triangle cone.  Each barycentric exit then remains in that
cone and is therefore eligible for the local minimum. -/
theorem noAdditionalZero_of_minimal_fixedChartLineHeight_in_triangleSector
    (A : FiniteProjectiveLineArrangement Line)
    (sigma outerSigma : Line -> Bool)
    (fixedGauge : (Fin 3 → Real) →ₗ[Real] Real)
    (q : A.OrdinaryVertex) (l a b outerBase outerLeft outerRight : Line)
    (htriangle : ¬ ∃ r : RealProjectivePoint,
      A.Incident r l ∧ A.Incident r a ∧ A.Incident r b)
    (hla : l ≠ a) (hlb : l ≠ b) (hab : a ≠ b)
    (hqaway : ¬ A.Incident q.1 l)
    (hqa : A.Incident q.1 a) (hqb : A.Incident q.1 b)
    (hordinary : forall k : Line,
      A.Incident q.1 k ↔ k = a ∨ k = b)
    (hfq : fixedGauge q.1.rep ≠ 0)
    (hfV1 : fixedGauge (A.intersection l a).rep ≠ 0)
    (hfV3 : fixedGauge (A.intersection l b).rep ≠ 0)
    (hXbase : 0 < A.arrangementOrientedEvaluation sigma l
      (vertexChartNormalizedVector fixedGauge q.1))
    (hV1right : 0 < A.arrangementOrientedEvaluation sigma b
      (vertexChartNormalizedVector fixedGauge (A.intersection l a)))
    (hV3left : 0 < A.arrangementOrientedEvaluation sigma a
      (vertexChartNormalizedVector fixedGauge (A.intersection l b)))
    (hqOuter : vertexChartNormalizedVector fixedGauge q.1 ∈
      A.arrangementClosedSignConeOn outerSigma
        {outerBase, outerLeft, outerRight})
    (hV1Outer : vertexChartNormalizedVector fixedGauge
        (A.intersection l a) ∈
      A.arrangementClosedSignConeOn outerSigma
        {outerBase, outerLeft, outerRight})
    (hV3Outer : vertexChartNormalizedVector fixedGauge
        (A.intersection l b) ∈
      A.arrangementClosedSignConeOn outerSigma
        {outerBase, outerLeft, outerRight})
    (hmin : forall y : RealProjectivePoint, y ∈ A.vertexSet ->
      A.projectivePointMemTriangleSector
        outerSigma outerBase outerLeft outerRight y ->
      ¬ A.Incident y l ->
      A.vertexChartLineHeight fixedGauge l q.1 ≤
        A.vertexChartLineHeight fixedGauge l y) :
    ∀ m : Line, m ∉ ({l, a, b} : Finset Line) →
      ∀ Z ∈ A.arrangementSignConeOn sigma {l, a, b},
        A.arrangementOrientedEvaluation sigma m Z ≠ 0 := by
  intro m hm Z hZ hZm
  obtain ⟨y, h, hh0, hh1, hyVertex, hyl, hylt, hbranch⟩ :=
    A.exists_smaller_vertex_of_additional_zero
      sigma fixedGauge q l a b m Z htriangle hla hlb hab hm
      hqaway hqa hqb hordinary hfq hfV1 hfV3
      hXbase hV1right hV3left hZ hZm
  have hyData : fixedGauge y.rep ≠ 0 ∧
      vertexChartNormalizedVector fixedGauge y ∈
        A.arrangementClosedSignConeOn outerSigma
          {outerBase, outerLeft, outerRight} := by
    rcases hbranch with hleft | hright
    · have hfy : fixedGauge y.rep ≠ 0 := by
        intro hzero
        have hnormZero : vertexChartNormalizedVector fixedGauge y = 0 := by
          simp [vertexChartNormalizedVector, hzero]
        have hfg := congrArg fixedGauge hleft.2
        simp only [hnormZero, LinearMap.map_zero, LinearMap.map_add,
          LinearMap.map_smul, smul_eq_mul,
          vertexChartNormalizedVector_fixedGauge_eq_one
            fixedGauge (A.intersection l a) hfV1,
          vertexChartNormalizedVector_fixedGauge_eq_one
            fixedGauge q.1 hfq] at hfg
        linarith
      refine ⟨hfy, ?_⟩
      rw [hleft.2]
      intro k hk
      rw [LinearMap.map_add, LinearMap.map_smul, LinearMap.map_smul,
        smul_eq_mul, smul_eq_mul]
      exact add_nonneg
        (mul_nonneg (sub_nonneg.mpr hh1.le) (hV1Outer k hk))
        (mul_nonneg hh0.le (hqOuter k hk))
    · have hfy : fixedGauge y.rep ≠ 0 := by
        intro hzero
        have hnormZero : vertexChartNormalizedVector fixedGauge y = 0 := by
          simp [vertexChartNormalizedVector, hzero]
        have hfg := congrArg fixedGauge hright.2
        simp only [hnormZero, LinearMap.map_zero, LinearMap.map_add,
          LinearMap.map_smul, smul_eq_mul,
          vertexChartNormalizedVector_fixedGauge_eq_one
            fixedGauge (A.intersection l b) hfV3,
          vertexChartNormalizedVector_fixedGauge_eq_one
            fixedGauge q.1 hfq] at hfg
        linarith
      refine ⟨hfy, ?_⟩
      rw [hright.2]
      intro k hk
      rw [LinearMap.map_add, LinearMap.map_smul, LinearMap.map_smul,
        smul_eq_mul, smul_eq_mul]
      exact add_nonneg
        (mul_nonneg (sub_nonneg.mpr hh1.le) (hV3Outer k hk))
        (mul_nonneg hh0.le (hqOuter k hk))
  have hyOuter :=
    A.projectivePointMemTriangleSector_of_vertexChartNormalizedVector_mem
      outerSigma fixedGauge outerBase outerLeft outerRight y
      hyData.1 hyData.2
  exact (not_lt_of_ge (hmin y hyVertex hyOuter hyl)) hylt


/-- Usable three-clause endpoint.  An ordinary apex which is globally
closest to the base cannot admit an additional zero in its strict
three-sided sector; the resulting empty sector is therefore a literal
triangular face attaching that apex to the base line. -/
theorem ordinaryVertexAttachedToLine_of_minimal_threeClauseTriangle
    (A : FiniteProjectiveLineArrangement Line) (hA : A.NonPencil)
    (q : A.OrdinaryVertex) (p : A.ArrangementComplement)
    (fixedGauge : (Fin 3 → Real) →ₗ[Real] Real)
    (l a b : Line) (hab : a ≠ b)
    (hqaway : ¬ A.Incident q.1 l)
    (hqa : A.Incident q.1 a) (hqb : A.Incident q.1 b)
    (hordinary : forall k : Line,
      A.Incident q.1 k ↔ k = a ∨ k = b)
    (hgauge : forall r : RealProjectivePoint, r ∈ A.vertexSet ->
      fixedGauge r.rep ≠ 0)
    (hXbase : 0 < A.arrangementOrientedEvaluation
      (A.arrangementPointSignPattern l p) l
      (vertexChartNormalizedVector fixedGauge q.1))
    (hV1right : 0 < A.arrangementOrientedEvaluation
      (A.arrangementPointSignPattern l p) b
      (vertexChartNormalizedVector fixedGauge (A.intersection l a)))
    (hV3left : 0 < A.arrangementOrientedEvaluation
      (A.arrangementPointSignPattern l p) a
      (vertexChartNormalizedVector fixedGauge (A.intersection l b)))
    (hqCone : A.arrangementPointNormalizedRepresentativeAt l q.1 ∈
      A.arrangementClosedSignConeOn
        (A.arrangementPointSignPattern l p) {l, a, b})
    (hmin : forall y : RealProjectivePoint, y ∈ A.vertexSet ->
      ¬ A.Incident y l ->
      A.vertexChartLineHeight fixedGauge l q.1 ≤
        A.vertexChartLineHeight fixedGauge l y) :
    A.OrdinaryVertexAttachedToLine q l := by
  have hla : l ≠ a := by
    intro h
    apply hqaway
    rw [h]
    exact hqa
  have hlb : l ≠ b := by
    intro h
    apply hqaway
    rw [h]
    exact hqb
  have hfq : fixedGauge q.1.rep ≠ 0 :=
    hgauge q.1 (Finset.mem_filter.mp q.2).1
  have hfV1 : fixedGauge (A.intersection l a).rep ≠ 0 :=
    hgauge (A.intersection l a) (A.intersection_mem_vertexSet hla)
  have hfV3 : fixedGauge (A.intersection l b).rep ≠ 0 :=
    hgauge (A.intersection l b) (A.intersection_mem_vertexSet hlb)
  have htriangle :=
    A.not_three_concurrent_of_offBase_apex
      q.1 l a b hab hqa hqb hqaway
  have hzeroAtBase :=
    A.noAdditionalZero_of_minimal_fixedChartLineHeight
      (A.arrangementPointSignPattern l p) fixedGauge q l a b
      htriangle hla hlb hab hqaway hqa hqb hordinary
      hfq hfV1 hfV3 hXbase hV1right hV3left hmin
  have hzeroAll :=
    A.noAdditionalZero_allBases_of_one p l ({l, a, b} : Finset Line)
      hzeroAtBase
  exact A.ordinaryVertexAttachedToLine_of_no_additional_zero
    hA q p l a b hla.symm hlb.symm hab hqaway hzeroAll hqCone

/-- Local form used for the secondary three-clause sectors.  The minimum is
only taken among vertices of one fixed outer projective triangle sector;
the three normalized endpoint hypotheses make that restriction stable
under the barycentric side exit. -/
theorem ordinaryVertexAttachedToLine_of_local_minimal_threeClauseTriangle
    (A : FiniteProjectiveLineArrangement Line) (hA : A.NonPencil)
    (q : A.OrdinaryVertex) (p : A.ArrangementComplement)
    (sigma outerSigma : Line -> Bool)
    (fixedGauge : (Fin 3 → Real) →ₗ[Real] Real)
    (l a b outerBase outerLeft outerRight : Line) (hab : a ≠ b)
    (hqaway : ¬ A.Incident q.1 l)
    (hqa : A.Incident q.1 a) (hqb : A.Incident q.1 b)
    (hordinary : forall k : Line,
      A.Incident q.1 k ↔ k = a ∨ k = b)
    (hfq : fixedGauge q.1.rep ≠ 0)
    (hfV1 : fixedGauge (A.intersection l a).rep ≠ 0)
    (hfV3 : fixedGauge (A.intersection l b).rep ≠ 0)
    (hXbase : 0 < A.arrangementOrientedEvaluation sigma l
      (vertexChartNormalizedVector fixedGauge q.1))
    (hV1right : 0 < A.arrangementOrientedEvaluation sigma b
      (vertexChartNormalizedVector fixedGauge (A.intersection l a)))
    (hV3left : 0 < A.arrangementOrientedEvaluation sigma a
      (vertexChartNormalizedVector fixedGauge (A.intersection l b)))
    (hqOuter : vertexChartNormalizedVector fixedGauge q.1 ∈
      A.arrangementClosedSignConeOn outerSigma
        {outerBase, outerLeft, outerRight})
    (hV1Outer : vertexChartNormalizedVector fixedGauge
        (A.intersection l a) ∈
      A.arrangementClosedSignConeOn outerSigma
        {outerBase, outerLeft, outerRight})
    (hV3Outer : vertexChartNormalizedVector fixedGauge
        (A.intersection l b) ∈
      A.arrangementClosedSignConeOn outerSigma
        {outerBase, outerLeft, outerRight})
    (hqCone : A.arrangementPointNormalizedRepresentativeAt l q.1 ∈
      A.arrangementClosedSignConeOn
        (A.arrangementPointSignPattern l p) {l, a, b})
    (hsigma : ∀ k ∈ ({l, a, b} : Finset Line),
      A.arrangementPointSignPattern l p k = sigma k)
    (hmin : forall y : RealProjectivePoint, y ∈ A.vertexSet ->
      A.projectivePointMemTriangleSector
        outerSigma outerBase outerLeft outerRight y ->
      ¬ A.Incident y l ->
      A.vertexChartLineHeight fixedGauge l q.1 ≤
        A.vertexChartLineHeight fixedGauge l y) :
    A.OrdinaryVertexAttachedToLine q l := by
  have hla : l ≠ a := by
    intro h
    apply hqaway
    rw [h]
    exact hqa
  have hlb : l ≠ b := by
    intro h
    apply hqaway
    rw [h]
    exact hqb
  have htriangle :=
    A.not_three_concurrent_of_offBase_apex
      q.1 l a b hab hqa hqb hqaway
  have hzeroSigma :=
    A.noAdditionalZero_of_minimal_fixedChartLineHeight_in_triangleSector
      sigma outerSigma fixedGauge q l a b outerBase outerLeft outerRight
      htriangle hla hlb hab hqaway hqa hqb hordinary
      hfq hfV1 hfV3 hXbase hV1right hV3left
      hqOuter hV1Outer hV3Outer hmin
  have hzeroAtBase := A.noAdditionalZero_mono_signPattern_eqOn
    sigma (A.arrangementPointSignPattern l p) {l, a, b} hsigma hzeroSigma
  have hzeroAll :=
    A.noAdditionalZero_allBases_of_one p l ({l, a, b} : Finset Line)
      hzeroAtBase
  exact A.ordinaryVertexAttachedToLine_of_no_additional_zero
    hA q p l a b hla.symm hlb.symm hab hqaway hzeroAll hqCone

/-- Projectively invariant specialization of the local endpoint to the
fixed gauge of the original outer triangle.  This is the form consumed
directly after `exists_minimal_originalTriangleGaugeLineHeight`. -/
theorem ordinaryVertexAttachedToLine_of_local_minimal_originalTriangleGauge
    (A : FiniteProjectiveLineArrangement Line) (hA : A.NonPencil)
    (q : A.OrdinaryVertex) (p : A.ArrangementComplement)
    (sigma outerSigma : Line -> Bool)
    (l a b outerBase outerLeft outerRight : Line) (hab : a ≠ b)
    (houterTriangle : ¬ ∃ r : RealProjectivePoint,
      A.Incident r outerBase ∧ A.Incident r outerLeft ∧
        A.Incident r outerRight)
    (hqaway : ¬ A.Incident q.1 l)
    (hqa : A.Incident q.1 a) (hqb : A.Incident q.1 b)
    (hordinary : forall k : Line,
      A.Incident q.1 k ↔ k = a ∨ k = b)
    (hXbase : 0 < A.arrangementOrientedEvaluation sigma l
      (vertexChartNormalizedVector
        (A.triangleSectorFixedGauge
          outerSigma outerBase outerLeft outerRight) q.1))
    (hV1right : 0 < A.arrangementOrientedEvaluation sigma b
      (vertexChartNormalizedVector
        (A.triangleSectorFixedGauge
          outerSigma outerBase outerLeft outerRight)
        (A.intersection l a)))
    (hV3left : 0 < A.arrangementOrientedEvaluation sigma a
      (vertexChartNormalizedVector
        (A.triangleSectorFixedGauge
          outerSigma outerBase outerLeft outerRight)
        (A.intersection l b)))
    (hqOuter : A.projectivePointMemTriangleSector
      outerSigma outerBase outerLeft outerRight q.1)
    (hV1Outer : A.projectivePointMemTriangleSector
      outerSigma outerBase outerLeft outerRight (A.intersection l a))
    (hV3Outer : A.projectivePointMemTriangleSector
      outerSigma outerBase outerLeft outerRight (A.intersection l b))
    (hqCone : A.arrangementPointNormalizedRepresentativeAt l q.1 ∈
      A.arrangementClosedSignConeOn
        (A.arrangementPointSignPattern l p) {l, a, b})
    (hsigma : ∀ k ∈ ({l, a, b} : Finset Line),
      A.arrangementPointSignPattern l p k = sigma k)
    (hmin : forall y : RealProjectivePoint, y ∈ A.vertexSet ->
      A.projectivePointMemTriangleSector
        outerSigma outerBase outerLeft outerRight y ->
      ¬ A.Incident y l ->
      A.vertexChartLineHeight
          (A.triangleSectorFixedGauge
            outerSigma outerBase outerLeft outerRight) l q.1 ≤
        A.vertexChartLineHeight
          (A.triangleSectorFixedGauge
            outerSigma outerBase outerLeft outerRight) l y) :
    A.OrdinaryVertexAttachedToLine q l := by
  let fixedGauge :=
    A.triangleSectorFixedGauge outerSigma outerBase outerLeft outerRight
  have hla : l ≠ a := by
    intro h
    apply hqaway
    rw [h]
    exact hqa
  have hlb : l ≠ b := by
    intro h
    apply hqaway
    rw [h]
    exact hqb
  have hfq : fixedGauge q.1.rep ≠ 0 := by
    simpa only [fixedGauge, A.triangleSectorFixedGauge_apply] using
      A.triangleSectorGauge_ne_zero_of_projective
        outerSigma outerBase outerLeft outerRight houterTriangle q.1 hqOuter
  have hfV1 : fixedGauge (A.intersection l a).rep ≠ 0 := by
    simpa only [fixedGauge, A.triangleSectorFixedGauge_apply] using
      A.triangleSectorGauge_ne_zero_of_projective
        outerSigma outerBase outerLeft outerRight houterTriangle
          (A.intersection l a) hV1Outer
  have hfV3 : fixedGauge (A.intersection l b).rep ≠ 0 := by
    simpa only [fixedGauge, A.triangleSectorFixedGauge_apply] using
      A.triangleSectorGauge_ne_zero_of_projective
        outerSigma outerBase outerLeft outerRight houterTriangle
          (A.intersection l b) hV3Outer
  have hqOuterNorm : vertexChartNormalizedVector fixedGauge q.1 ∈
      A.arrangementClosedSignConeOn outerSigma
        {outerBase, outerLeft, outerRight} := by
    simpa only [fixedGauge,
      A.vertexChartNormalizedVector_triangleSectorFixedGauge] using
      A.triangleSectorNormalizedVector_mem_of_projective
        outerSigma outerBase outerLeft outerRight houterTriangle q.1 hqOuter
  have hV1OuterNorm : vertexChartNormalizedVector fixedGauge
        (A.intersection l a) ∈
      A.arrangementClosedSignConeOn outerSigma
        {outerBase, outerLeft, outerRight} := by
    simpa only [fixedGauge,
      A.vertexChartNormalizedVector_triangleSectorFixedGauge] using
      A.triangleSectorNormalizedVector_mem_of_projective
        outerSigma outerBase outerLeft outerRight houterTriangle
          (A.intersection l a) hV1Outer
  have hV3OuterNorm : vertexChartNormalizedVector fixedGauge
        (A.intersection l b) ∈
      A.arrangementClosedSignConeOn outerSigma
        {outerBase, outerLeft, outerRight} := by
    simpa only [fixedGauge,
      A.vertexChartNormalizedVector_triangleSectorFixedGauge] using
      A.triangleSectorNormalizedVector_mem_of_projective
        outerSigma outerBase outerLeft outerRight houterTriangle
          (A.intersection l b) hV3Outer
  apply A.ordinaryVertexAttachedToLine_of_local_minimal_threeClauseTriangle
    hA q p sigma outerSigma fixedGauge
    l a b outerBase outerLeft outerRight hab hqaway hqa hqb hordinary
    hfq hfV1 hfV3
  · simpa only [fixedGauge] using hXbase
  · simpa only [fixedGauge] using hV1right
  · simpa only [fixedGauge] using hV3left
  · exact hqOuterNorm
  · exact hV1OuterNorm
  · exact hV3OuterNorm
  · exact hqCone
  · exact hsigma
  · simpa only [fixedGauge] using hmin

end FiniteProjectiveLineArrangement

end Erdos506.Incidence
