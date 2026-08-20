import Erdos506.Incidence.RealProjectiveArrangementKellyMoserAttachmentExit
import Erdos506.Incidence.RealProjectiveArrangementEulerFinish

/-!
# Felsner outer router for the Kelly--Moser three-clause

This downstream module consumes the actual barycentric sector exit and keeps
the finite Kelly--Rottenberg core acyclic.
-/

namespace Erdos506.Incidence

open scoped LinearAlgebra.Projectivization Topology

namespace FiniteProjectiveLineArrangement

variable {Line : Type*} [Fintype Line] [DecidableEq Line]

noncomputable local instance realProjectiveOnePointTopologicalSpaceForKellyOuter :
    TopologicalSpace RealProjectiveOnePoint :=
  realProjectiveOnePointQuotientTopology

noncomputable local instance realProjectivePointTopologicalSpaceForKellyOuter :
    TopologicalSpace RealProjectivePoint :=
  realProjectivePointQuotientTopology

noncomputable local instance lineRegularLocusTopologicalSpaceForKellyOuter
    (A : FiniteProjectiveLineArrangement Line) (l : Line) :
    TopologicalSpace (A.lineRegularLocus l) :=
  TopologicalSpace.induced
    (fun q : A.lineRegularLocus l => q.1)
    realProjectivePointQuotientTopology

/-- Orienting a nonzero real number by its strict sign makes it positive. -/
theorem signedByPositivity_pos {r : ℝ} (hr : r ≠ 0) :
    0 < if decide (0 < r) then r else -r := by
  by_cases hpos : 0 < r
  · simp [hpos]
  · have hneg : r < 0 := lt_of_le_of_ne (le_of_not_gt hpos) hr
    simp [hpos, hneg]

/-- Vanishing does not depend on the Boolean orientation of a line. -/
theorem arrangementOrientedEvaluation_eq_zero_iff
    (A : FiniteProjectiveLineArrangement Line) (sigma : Line → Bool)
    (l : Line) (v : Fin 3 → ℝ) :
    A.arrangementOrientedEvaluation sigma l v = 0 ↔
      projectiveLineEvaluation (A.projectiveLine l) v = 0 := by
  by_cases h : sigma l <;>
    simp [arrangementOrientedEvaluation, h]

/-- A strict finite cone crossed by no remaining arrangement line gives an
actual point of the arrangement complement. -/
theorem exists_arrangementComplement_of_no_additional_zero
    (A : FiniteProjectiveLineArrangement Line) (sigma : Line → Bool)
    (K : Finset Line) (u : Fin 3 → ℝ) (hu0 : u ≠ 0)
    (hu : u ∈ A.arrangementSignConeOn sigma K)
    (hnozero : ∀ m : Line, m ∉ K →
      A.arrangementOrientedEvaluation sigma m u ≠ 0) :
    ∃ p : A.ArrangementComplement,
      p.1 = Projectivization.mk ℝ u hu0 := by
  let p0 : RealProjectivePoint := Projectivization.mk ℝ u hu0
  have hpAway : ∀ m : Line, ¬ A.Incident p0 m := by
    intro m
    apply (A.incident_projectivization_mk_iff_orientedEvaluation_eq_zero
      sigma m u hu0).not.mpr
    by_cases hmK : m ∈ K
    · exact ne_of_gt (hu m hmK)
    · exact hnozero m hmK
  exact ⟨⟨p0, hpAway⟩, rfl⟩

/-- The base-normalized representative of a complement point can be read
from any homogeneous representative whose base evaluation is nonzero. -/
theorem arrangementNormalizedRepresentative_eq_of_projectivization_mk
    (A : FiniteProjectiveLineArrangement Line) (base : Line)
    (p : A.ArrangementComplement) {u : Fin 3 → ℝ} (hu0 : u ≠ 0)
    (hbase : projectiveLineEvaluation (A.projectiveLine base) u ≠ 0)
    (hp : Projectivization.mk ℝ u hu0 = p.1) :
    A.arrangementNormalizedRepresentative base p =
      (projectiveLineEvaluation (A.projectiveLine base) u)⁻¹ • u := by
  let Y := (projectiveLineEvaluation (A.projectiveLine base) u)⁻¹ • u
  have hY0 : Y ≠ 0 := by
    intro hzero
    rcases smul_eq_zero.mp hzero with hscalar | hvector
    · exact (inv_ne_zero hbase) hscalar
    · exact hu0 hvector
  have hYbase : projectiveLineEvaluation (A.projectiveLine base) Y = 1 := by
    simp only [Y, LinearMap.map_smul, smul_eq_mul]
    exact inv_mul_cancel₀ hbase
  have hmkY : Projectivization.mk ℝ Y hY0 = p.1 := by
    calc
      Projectivization.mk ℝ Y hY0 = Projectivization.mk ℝ u hu0 := by
        apply (Projectivization.mk_eq_mk_iff' ℝ _ _ _ _).mpr
        exact ⟨_, rfl⟩
      _ = p.1 := hp
  simpa only [arrangementNormalizedRepresentative, Y] using
    (vertexChartNormalizedVector_eq_of_projectivization_mk
      (projectiveLineEvaluation (A.projectiveLine base)) p.1
      hY0 hYbase hmkY)

/-- A positive rescaling of a strict cone point has the same Boolean signs
on every indexed side of that cone. -/
theorem arrangementPointSignPattern_eq_on_of_normalized_eq_pos_smul
    (A : FiniteProjectiveLineArrangement Line) (base : Line)
    (p : A.ArrangementComplement) (sigma : Line → Bool)
    (K : Finset Line) (u : Fin 3 → ℝ) (c : ℝ)
    (hc : 0 < c)
    (hnorm : A.arrangementNormalizedRepresentative base p = c • u)
    (hu : u ∈ A.arrangementSignConeOn sigma K) :
    ∀ k ∈ K, A.arrangementPointSignPattern base p k = sigma k := by
  intro k hk
  have huk := hu k hk
  by_cases hs : sigma k
  · have hraw : 0 < projectiveLineEvaluation (A.projectiveLine k) u := by
      simpa [arrangementOrientedEvaluation, hs] using huk
    have hnormRaw : 0 < projectiveLineEvaluation (A.projectiveLine k)
        (A.arrangementNormalizedRepresentative base p) := by
      rw [hnorm, LinearMap.map_smul]
      simpa only [smul_eq_mul] using mul_pos hc hraw
    simp [arrangementPointSignPattern, hs, hnormRaw]
  · have hraw : projectiveLineEvaluation (A.projectiveLine k) u < 0 := by
      have : 0 < -projectiveLineEvaluation (A.projectiveLine k) u := by
        simpa [arrangementOrientedEvaluation, hs] using huk
      linarith
    have hnormRaw : projectiveLineEvaluation (A.projectiveLine k)
        (A.arrangementNormalizedRepresentative base p) < 0 := by
      rw [hnorm, LinearMap.map_smul]
      simpa only [smul_eq_mul] using mul_neg_of_pos_of_neg hc hraw
    simp [arrangementPointSignPattern, hs, not_lt_of_ge hnormRaw.le]

/-- The absence of transverse zeros only depends on the orientations of the
three retained sides; outside the side set, only vanishing is tested. -/
theorem noAdditionalZero_mono_signPattern_eqOn
    (A : FiniteProjectiveLineArrangement Line)
    (sigma tau : Line → Bool) (K : Finset Line)
    (heq : ∀ k ∈ K, tau k = sigma k)
    (hnozero : ∀ m : Line, m ∉ K →
      ∀ v ∈ A.arrangementSignConeOn sigma K,
        A.arrangementOrientedEvaluation sigma m v ≠ 0) :
    ∀ m : Line, m ∉ K →
      ∀ v ∈ A.arrangementSignConeOn tau K,
        A.arrangementOrientedEvaluation tau m v ≠ 0 := by
  intro m hm v hv hvm
  have hvSigma : v ∈ A.arrangementSignConeOn sigma K := by
    intro k hk
    have heval : A.arrangementOrientedEvaluation tau k =
        A.arrangementOrientedEvaluation sigma k := by
      unfold arrangementOrientedEvaluation
      rw [heq k hk]
    rw [← heval]
    exact hv k hk
  apply hnozero m hm v hvSigma
  apply (A.arrangementOrientedEvaluation_eq_zero_iff sigma m v).2
  exact (A.arrangementOrientedEvaluation_eq_zero_iff tau m v).1 hvm

/-- The return of one apex support on an off-apex base cannot lie on the
other apex support. -/
theorem not_incident_intersection_base_support_of_offBase_apex
    (A : FiniteProjectiveLineArrangement Line)
    (q : RealProjectivePoint) (l a b : Line)
    (hla : l ≠ a) (hab : a ≠ b)
    (hqa : A.Incident q a) (hqb : A.Incident q b)
    (hql : ¬ A.Incident q l) :
    ¬ A.Incident (A.intersection l a) b := by
  intro hpB
  have hp : A.intersection l a = A.intersection a b :=
    A.eq_intersection_of_incident hab
      (A.intersection_incident_right hla) hpB
  have hq : q = A.intersection a b :=
    A.eq_intersection_of_incident hab hqa hqb
  apply hql
  rw [hq, ← hp]
  exact A.intersection_incident_left hla

/-- The base and the two supports of a point away from that base are not
concurrent. -/
theorem not_three_concurrent_of_offBase_apex
    (A : FiniteProjectiveLineArrangement Line)
    (q : RealProjectivePoint) (l a b : Line) (hab : a ≠ b)
    (hqa : A.Incident q a) (hqb : A.Incident q b)
    (hql : ¬ A.Incident q l) :
    ¬ ∃ r : RealProjectivePoint,
      A.Incident r l ∧ A.Incident r a ∧ A.Incident r b := by
  rintro ⟨r, hrl, hra, hrb⟩
  have hr : r = A.intersection a b :=
    A.eq_intersection_of_incident hab hra hrb
  have hq : q = A.intersection a b :=
    A.eq_intersection_of_incident hab hqa hqb
  apply hql
  rw [hq, ← hr]
  exact hrl

/-- Orient the two side supports toward their opposite base returns, while
keeping the base covector in its given positive orientation. -/
noncomputable def emptyTriangleSignPattern
    (A : FiniteProjectiveLineArrangement Line) (a b : Line)
    (Vleft Vright : Fin 3 → ℝ) : Line → Bool := fun k =>
  if k = a then
    decide (0 < projectiveLineEvaluation (A.projectiveLine a) Vright)
  else if k = b then
    decide (0 < projectiveLineEvaluation (A.projectiveLine b) Vleft)
  else true

@[simp]
theorem emptyTriangleSignPattern_base
    (A : FiniteProjectiveLineArrangement Line) (l a b : Line)
    (Vleft Vright : Fin 3 → ℝ) (hla : l ≠ a) (hlb : l ≠ b) :
    A.emptyTriangleSignPattern a b Vleft Vright l = true := by
  simp [emptyTriangleSignPattern, hla, hlb]

/-- Membership of a fixed-gauge normalized representative in a closed
three-cone descends to projective triangle-sector membership. -/
theorem projectivePointMemTriangleSector_of_vertexChartNormalizedVector_mem
    (A : FiniteProjectiveLineArrangement Line) (sigma : Line → Bool)
    (fixedGauge : (Fin 3 → ℝ) →ₗ[ℝ] ℝ) (l a b : Line)
    (q : RealProjectivePoint) (hfq : fixedGauge q.rep ≠ 0)
    (hq : vertexChartNormalizedVector fixedGauge q ∈
      A.arrangementClosedSignConeOn sigma {l, a, b}) :
    A.projectivePointMemTriangleSector sigma l a b q := by
  have hrep : q.rep = fixedGauge q.rep •
      vertexChartNormalizedVector fixedGauge q := by
    simp [vertexChartNormalizedVector, smul_smul, hfq]
  rcases lt_or_gt_of_ne hfq with hfneg | hfpos
  · right
    rw [hrep]
    intro k hk
    rw [LinearMap.map_neg, LinearMap.map_smul]
    simp only [smul_eq_mul]
    simpa only [neg_mul] using
      mul_nonneg (neg_nonneg.mpr hfneg.le) (hq k hk)
  · left
    rw [hrep]
    intro k hk
    rw [LinearMap.map_smul]
    simp only [smul_eq_mul]
    exact mul_nonneg hfpos.le (hq k hk)

@[simp]
theorem vertexChartNormalizedVector_neg_fixedGauge
    (fixedGauge : (Fin 3 → ℝ) →ₗ[ℝ] ℝ) (q : RealProjectivePoint) :
    vertexChartNormalizedVector (-fixedGauge) q =
      -vertexChartNormalizedVector fixedGauge q := by
  simp [vertexChartNormalizedVector, inv_neg]

@[simp]
theorem vertexChartLineHeight_neg_fixedGauge
    (A : FiniteProjectiveLineArrangement Line)
    (fixedGauge : (Fin 3 → ℝ) →ₗ[ℝ] ℝ) (l : Line)
    (q : RealProjectivePoint) :
    A.vertexChartLineHeight (-fixedGauge) l q =
      A.vertexChartLineHeight fixedGauge l q := by
  simp [vertexChartLineHeight]

/-- Two nonzero real values of opposite sign have a unique zero at a strict
barycentric parameter between their endpoints. -/
theorem exists_strict_barycentric_zero_of_mul_neg
    {u v : ℝ} (huv : u * v < 0) :
    ∃ h : ℝ, 0 < h ∧ h < 1 ∧ (1 - h) * u + h * v = 0 := by
  rcases mul_neg_iff.mp huv with ⟨hu, hv⟩ | ⟨hu, hv⟩
  · let h := u / (u - v)
    have hden : 0 < u - v := by linarith
    have hh0 : 0 < h := div_pos hu hden
    have hh1 : h < 1 := by
      apply (div_lt_one hden).2
      linarith
    refine ⟨h, hh0, hh1, ?_⟩
    dsimp only [h]
    field_simp [ne_of_gt hden]
    ring
  · let h := (-u) / (v - u)
    have hden : 0 < v - u := by linarith
    have hh0 : 0 < h := by
      exact div_pos (neg_pos.mpr hu) hden
    have hh1 : h < 1 := by
      apply (div_lt_one hden).2
      linarith
    refine ⟨h, hh0, hh1, ?_⟩
    dsimp only [h]
    field_simp [ne_of_gt hden]
    ring

/-- A transverse covector vanishing strictly inside a three-sided cone must
vanish on one of the two side segments from the apex, at a strict
barycentric parameter. -/
theorem exists_side_barycentric_zero_of_strict_triangle_zero
    (base left right transverse : (Fin 3 → ℝ) →ₗ[ℝ] ℝ)
    {X V1 V3 Z : Fin 3 → ℝ}
    (hkernel : ∀ W, base W = 0 → left W = 0 → right W = 0 → W = 0)
    (hXbase : 0 < base X) (hXleft : left X = 0)
    (hXright : right X = 0)
    (hV1base : base V1 = 0) (hV1left : left V1 = 0)
    (hV1right : 0 < right V1)
    (hV3base : base V3 = 0) (hV3left : 0 < left V3)
    (hV3right : right V3 = 0)
    (hZbase : 0 < base Z) (hZleft : 0 < left Z)
    (hZright : 0 < right Z)
    (hZm : transverse Z = 0) (hXm : transverse X ≠ 0) :
    (∃ h : ℝ, 0 < h ∧ h < 1 ∧
      transverse ((1 - h) • V1 + h • X) = 0) ∨
    (∃ h : ℝ, 0 < h ∧ h < 1 ∧
      transverse ((1 - h) • V3 + h • X) = 0) := by
  let s := base X * left V3 * right V1
  let c1 := base X * left V3 * right Z
  let c3 := base X * right V1 * left Z
  let cx := left V3 * right V1 * base Z
  have hc1 : 0 < c1 := by
    dsimp only [c1]
    exact mul_pos (mul_pos hXbase hV3left) hZright
  have hc3 : 0 < c3 := by
    dsimp only [c3]
    exact mul_pos (mul_pos hXbase hV1right) hZleft
  have hcx : 0 < cx := by
    dsimp only [cx]
    exact mul_pos (mul_pos hV3left hV1right) hZbase
  have hdecomp : s • Z = c1 • V1 + c3 • V3 + cx • X := by
    apply sub_eq_zero.mp
    apply hkernel
    · simp only [LinearMap.map_sub, LinearMap.map_add, LinearMap.map_smul,
        smul_eq_mul, hV1base, hV3base, hXbase.ne', mul_zero,
        zero_add, add_zero]
      dsimp only [s, cx]
      ring
    · simp only [LinearMap.map_sub, LinearMap.map_add, LinearMap.map_smul,
        smul_eq_mul, hV1left, hXleft, mul_zero, zero_add, add_zero]
      dsimp only [s, c3]
      ring
    · simp only [LinearMap.map_sub, LinearMap.map_add, LinearMap.map_smul,
        smul_eq_mul, hV3right, hXright, mul_zero, add_zero]
      dsimp only [s, c1]
      ring
  have hmEq := congrArg transverse hdecomp
  have hsum : c1 * transverse V1 + c3 * transverse V3 +
      cx * transverse X = 0 := by
    simpa only [LinearMap.map_smul, LinearMap.map_add, smul_eq_mul,
      hZm, mul_zero] using hmEq.symm
  rcases lt_or_gt_of_ne hXm with hXneg | hXpos
  · have hside : 0 < transverse V1 ∨ 0 < transverse V3 := by
      by_cases h1 : 0 < transverse V1
      · exact Or.inl h1
      by_cases h3 : 0 < transverse V3
      · exact Or.inr h3
      exfalso
      have ht1 : c1 * transverse V1 ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos hc1.le (le_of_not_gt h1)
      have ht3 : c3 * transverse V3 ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos hc3.le (le_of_not_gt h3)
      have htx : cx * transverse X < 0 := mul_neg_of_pos_of_neg hcx hXneg
      linarith
    rcases hside with h1 | h3
    · left
      obtain ⟨h, hh0, hh1, hz⟩ :=
        exists_strict_barycentric_zero_of_mul_neg
          (mul_neg_of_pos_of_neg h1 hXneg)
      refine ⟨h, hh0, hh1, ?_⟩
      rw [LinearMap.map_add, LinearMap.map_smul, LinearMap.map_smul]
      simpa only [smul_eq_mul] using hz
    · right
      obtain ⟨h, hh0, hh1, hz⟩ :=
        exists_strict_barycentric_zero_of_mul_neg
          (mul_neg_of_pos_of_neg h3 hXneg)
      refine ⟨h, hh0, hh1, ?_⟩
      rw [LinearMap.map_add, LinearMap.map_smul, LinearMap.map_smul]
      simpa only [smul_eq_mul] using hz
  · have hside : transverse V1 < 0 ∨ transverse V3 < 0 := by
      by_cases h1 : transverse V1 < 0
      · exact Or.inl h1
      by_cases h3 : transverse V3 < 0
      · exact Or.inr h3
      exfalso
      have ht1 : 0 ≤ c1 * transverse V1 :=
        mul_nonneg hc1.le (le_of_not_gt h1)
      have ht3 : 0 ≤ c3 * transverse V3 :=
        mul_nonneg hc3.le (le_of_not_gt h3)
      have htx : 0 < cx * transverse X := mul_pos hcx hXpos
      linarith
    rcases hside with h1 | h3
    · left
      obtain ⟨h, hh0, hh1, hz⟩ :=
        exists_strict_barycentric_zero_of_mul_neg
          (mul_neg_of_neg_of_pos h1 hXpos)
      refine ⟨h, hh0, hh1, ?_⟩
      rw [LinearMap.map_add, LinearMap.map_smul, LinearMap.map_smul]
      simpa only [smul_eq_mul] using hz
    · right
      obtain ⟨h, hh0, hh1, hz⟩ :=
        exists_strict_barycentric_zero_of_mul_neg
          (mul_neg_of_neg_of_pos h3 hXpos)
      refine ⟨h, hh0, hh1, ?_⟩
      rw [LinearMap.map_add, LinearMap.map_smul, LinearMap.map_smul]
      simpa only [smul_eq_mul] using hz
/-- The cyclic parameter of a point in the regular part of a fixed indexed
line.  This is the generic-line counterpart of the insertion parameter used
in the Euler proof. -/
noncomputable def lineRegularParameter
    (A : FiniteProjectiveLineArrangement Line) (l : Line) :
    A.lineRegularLocus l → RealProjectiveOnePoint :=
  fun q => (projectiveLineParameterHomeomorph_eulerFinish
    (A.projectiveLine l)).symm ⟨q.1, (q.2 l).mpr rfl⟩

theorem continuous_lineRegularParameter
    (A : FiniteProjectiveLineArrangement Line) (l : Line) :
    Continuous (A.lineRegularParameter l) := by
  apply (projectiveLineParameterHomeomorph_eulerFinish
    (A.projectiveLine l)).symm.continuous.comp
  exact continuous_subtype_val.subtype_mk _

theorem projectiveLineParameter_lineRegularParameter
    (A : FiniteProjectiveLineArrangement Line) (l : Line)
    (q : A.lineRegularLocus l) :
    projectiveLineParameter (A.projectiveLine l)
      (A.lineRegularParameter l q) = q.1 := by
  have h := (projectiveLineParameterHomeomorph_eulerFinish
    (A.projectiveLine l)).apply_symm_apply
      ⟨q.1, (q.2 l).mpr rfl⟩
  simpa only [lineRegularParameter] using congrArg Subtype.val h

/-- A cyclic gap is relatively open in the regular part of its supporting
line. -/
theorem isOpen_circularGapRegularFiber
    (A : FiniteProjectiveLineArrangement Line) (l : Line)
    (g : A.CircularGapSlot l) :
    IsOpen (A.circularGapRegularFiber l g) := by
  let P := circularGapSlotParameter A l g
  let R := circularGapSlotParameter A l (A.circularGapSuccessor l g)
  have hopen : IsOpen
      (A.lineRegularParameter l ⁻¹'
        {Q : RealProjectiveOnePoint | RealProjectiveCyclic P Q R}) :=
    (isOpen_realProjectiveCyclic_middle P R).preimage
      (A.continuous_lineRegularParameter l)
  have hset : A.circularGapRegularFiber l g =
      A.lineRegularParameter l ⁻¹'
        {Q : RealProjectiveOnePoint | RealProjectiveCyclic P Q R} := by
    ext q
    change q.1 ∈ A.geometricEdgeOpenArc (A.circularGapEdge l g) ↔
      RealProjectiveCyclic P (A.lineRegularParameter l q) R
    rw [← projectiveLineCyclic_parameter_iff,
      A.projectiveLineParameter_circularGapSlotParameter l g,
      A.projectiveLineParameter_lineRegularParameter l q,
      A.projectiveLineParameter_circularGapSlotParameter l
        (A.circularGapSuccessor l g)]
    rfl
  rw [hset]
  exact hopen

/-- Strict face inequalities away from one support, sliced by the kernel of
that support. -/
def arrangementFaceLineSliceCone
    (A : FiniteProjectiveLineArrangement Line) (sigma : Line → Bool)
    (l : Line) : Set (Fin 3 → ℝ) :=
  A.arrangementSignConeOn sigma (Finset.univ.erase l) ∩
    (A.arrangementOrientedEvaluation sigma l).ker

theorem convex_arrangementSignConeOn
    (A : FiniteProjectiveLineArrangement Line) (sigma : Line → Bool)
    (K : Finset Line) :
    Convex ℝ (A.arrangementSignConeOn sigma K) := by
  have heq : A.arrangementSignConeOn sigma K =
      ⋂ k ∈ K, {v | 0 < A.arrangementOrientedEvaluation sigma k v} := by
    ext v
    simp [arrangementSignConeOn]
  rw [heq]
  apply convex_iInter
  intro k
  apply convex_iInter
  intro _hk
  exact convex_halfSpace_gt
    (IsLinearMap.mk
      (A.arrangementOrientedEvaluation sigma k).map_add
      (A.arrangementOrientedEvaluation sigma k).map_smul) 0

theorem convex_arrangementFaceLineSliceCone
    (A : FiniteProjectiveLineArrangement Line) (sigma : Line → Bool)
    (l : Line) :
    Convex ℝ (A.arrangementFaceLineSliceCone sigma l) := by
  unfold arrangementFaceLineSliceCone
  apply (A.convex_arrangementSignConeOn sigma (Finset.univ.erase l)).inter
  simpa only [LinearMap.mem_ker] using
    (convex_hyperplane
      (IsLinearMap.mk
        (A.arrangementOrientedEvaluation sigma l).map_add
        (A.arrangementOrientedEvaluation sigma l).map_smul) 0)

theorem arrangementFaceLineSliceCone_ne_zero
    (A : FiniteProjectiveLineArrangement Line) (sigma : Line → Bool)
    (l base : Line) (hbase : base ≠ l) {v : Fin 3 → ℝ}
    (hv : v ∈ A.arrangementFaceLineSliceCone sigma l) :
    v ≠ 0 := by
  intro hzero
  have hpos := hv.1 base (Finset.mem_erase.mpr
    ⟨hbase, Finset.mem_univ base⟩)
  rw [hzero, LinearMap.map_zero] at hpos
  exact (lt_irrefl 0 hpos)

/-- Projectivize a strict face slice into the regular locus of its support. -/
noncomputable def arrangementFaceLineSliceToRegular
    (A : FiniteProjectiveLineArrangement Line) (sigma : Line → Bool)
    (l base : Line) (hbase : base ≠ l) :
    {v : Fin 3 → ℝ // v ∈ A.arrangementFaceLineSliceCone sigma l} →
      A.lineRegularLocus l :=
  fun v =>
    ⟨Projectivization.mk' ℝ
        ⟨v.1, A.arrangementFaceLineSliceCone_ne_zero
          sigma l base hbase v.2⟩,
      by
        intro m
        rw [Projectivization.mk'_eq_mk,
          A.incident_projectivization_mk_iff_orientedEvaluation_eq_zero]
        constructor
        · intro hm
          by_cases hml : m = l
          · exact hml
          · have hmpos := v.2.1 m (Finset.mem_erase.mpr
                ⟨hml, Finset.mem_univ m⟩)
            exact (ne_of_gt hmpos hm).elim
        · rintro rfl
          exact v.2.2⟩

theorem continuous_arrangementFaceLineSliceToRegular
    (A : FiniteProjectiveLineArrangement Line) (sigma : Line → Bool)
    (l base : Line) (hbase : base ≠ l) :
    Continuous (A.arrangementFaceLineSliceToRegular sigma l base hbase) := by
  unfold arrangementFaceLineSliceToRegular
  refine (continuous_quotient_mk'.comp
    (continuous_subtype_val.subtype_mk fun v =>
      A.arrangementFaceLineSliceCone_ne_zero
        sigma l base hbase v.2)).subtype_mk ?_

theorem normalized_mem_arrangementFaceLineSliceCone_of_regular_closure
    (A : FiniteProjectiveLineArrangement Line)
    (q : RealProjectivePoint) (l base : Line) (F : A.ArrangementFace)
    (hbase : base ≠ l)
    (hregular : ∀ m : Line, A.Incident q m ↔ m = l)
    (hF : q ∈ closure (A.arrangementFaceCarrier F)) :
    A.arrangementPointNormalizedRepresentativeAt base q ∈
      A.arrangementFaceLineSliceCone
        (A.arrangementFaceSignPattern base F) l := by
  have hqbase : ¬ A.Incident q base := by
    intro h
    exact hbase ((hregular base).mp h)
  constructor
  · rw [A.mem_arrangementSignConeOn]
    intro m hm
    have hml : m ≠ l := (Finset.mem_erase.mp hm).1
    apply A.arrangementOrientedEvaluation_normalized_pos_of_mem_closure_of_not_incident
      q base F hqbase hF m
    intro hqm
    exact hml ((hregular m).mp hqm)
  · have hq0 :=
      A.arrangementPointNormalizedRepresentativeAt_ne_zero base q hqbase
    apply (A.incident_projectivization_mk_iff_orientedEvaluation_eq_zero
      (A.arrangementFaceSignPattern base F) l
      (A.arrangementPointNormalizedRepresentativeAt base q) hq0).1
    rw [A.projectivization_mk_arrangementPointNormalizedRepresentativeAt
      base q hqbase]
    exact (hregular l).mpr rfl

theorem arrangementFaceLineSliceToRegular_normalized
    (A : FiniteProjectiveLineArrangement Line)
    (q : RealProjectivePoint) (l base : Line) (F : A.ArrangementFace)
    (hbase : base ≠ l)
    (hregular : ∀ m : Line, A.Incident q m ↔ m = l)
    (hF : q ∈ closure (A.arrangementFaceCarrier F)) :
    A.arrangementFaceLineSliceToRegular
        (A.arrangementFaceSignPattern base F) l base hbase
        ⟨A.arrangementPointNormalizedRepresentativeAt base q,
          A.normalized_mem_arrangementFaceLineSliceCone_of_regular_closure
            q l base F hbase hregular hF⟩ =
      (⟨q, hregular⟩ : A.lineRegularLocus l) := by
  apply Subtype.ext
  simp only [arrangementFaceLineSliceToRegular,
    Projectivization.mk'_eq_mk]
  exact A.projectivization_mk_arrangementPointNormalizedRepresentativeAt
    base q (by
      intro h
      exact hbase ((hregular base).mp h))

/-- Two regular points of the same support which lie in the closure of one
actual face are joined without crossing another arrangement line. -/
theorem joined_lineRegularLocus_of_same_face_closure
    (A : FiniteProjectiveLineArrangement Line) (hA : A.NonPencil)
    (l : Line) (F : A.ArrangementFace)
    (q r : A.lineRegularLocus l)
    (hqF : q.1 ∈ closure (A.arrangementFaceCarrier F))
    (hrF : r.1 ∈ closure (A.arrangementFaceCarrier F)) :
    Joined q r := by
  obtain ⟨base, hbase⟩ := A.exists_ne_line_of_nonPencil hA l
  let sigma := A.arrangementFaceSignPattern base F
  let u := A.arrangementPointNormalizedRepresentativeAt base q.1
  let v := A.arrangementPointNormalizedRepresentativeAt base r.1
  have hu : u ∈ A.arrangementFaceLineSliceCone sigma l := by
    simpa only [u, sigma] using
      A.normalized_mem_arrangementFaceLineSliceCone_of_regular_closure
        q.1 l base F hbase q.2 hqF
  have hv : v ∈ A.arrangementFaceLineSliceCone sigma l := by
    simpa only [v, sigma] using
      A.normalized_mem_arrangementFaceLineSliceCone_of_regular_closure
        r.1 l base F hbase r.2 hrF
  have hjoinedSlice : Joined
      (⟨u, hu⟩ : {w : Fin 3 → ℝ //
        w ∈ A.arrangementFaceLineSliceCone sigma l})
      ⟨v, hv⟩ := by
    exact (((A.convex_arrangementFaceLineSliceCone sigma l).isPathConnected
      ⟨u, hu⟩).joinedIn u hu v hv).joined_subtype
  have huMap : A.arrangementFaceLineSliceToRegular sigma l base hbase
      ⟨u, hu⟩ = q := by
    simpa only [u, sigma] using
      A.arrangementFaceLineSliceToRegular_normalized
        q.1 l base F hbase q.2 hqF
  have hvMap : A.arrangementFaceLineSliceToRegular sigma l base hbase
      ⟨v, hv⟩ = r := by
    simpa only [v, sigma] using
      A.arrangementFaceLineSliceToRegular_normalized
        r.1 l base F hbase r.2 hrF
  exact ⟨(hjoinedSlice.somePath.map
    (A.continuous_arrangementFaceLineSliceToRegular
      sigma l base hbase)).cast huMap.symm hvMap.symm⟩

/-- One convex arrangement face has at most one boundary edge on any fixed
indexed support. -/
theorem edgeSlotLine_injective_on_arrangementFaceBoundary
    (A : FiniteProjectiveLineArrangement Line) (hA : A.NonPencil)
    (F : A.ArrangementFace) {e e' : A.GeometricEdge}
    (he : e ∈ A.arrangementFaceBoundary F)
    (he' : e' ∈ A.arrangementFaceBoundary F)
    (hline : A.edgeSlotLine e = A.edgeSlotLine e') :
    e = e' := by
  let l := A.edgeSlotLine e
  have heAdjacent := (A.mem_arrangementFaceBoundary_iff F e).mp he
  have he'Adjacent := (A.mem_arrangementFaceBoundary_iff F e').mp he'
  obtain ⟨q, hqArc, hqF⟩ := heAdjacent
  obtain ⟨r, hrArc, hrF⟩ := he'Adjacent
  have hqRegular : ∀ m : Line, A.Incident q m ↔ m = l := by
    intro m
    simpa only [l] using A.geometricEdgeOpenArc_incident_iff e hqArc m
  have hrRegular : ∀ m : Line, A.Incident r m ↔ m = l := by
    intro m
    have h := A.geometricEdgeOpenArc_incident_iff e' hrArc m
    simpa only [l, hline] using h
  let q' : A.lineRegularLocus l := ⟨q, hqRegular⟩
  let r' : A.lineRegularLocus l := ⟨r, hrRegular⟩
  obtain ⟨g, hg⟩ :=
    A.exists_circularGapEdge_eq_of_edgeSlotLine_eq e l rfl
  obtain ⟨k, hk⟩ :=
    A.exists_circularGapEdge_eq_of_edgeSlotLine_eq e' l hline.symm
  have hqFiber : q' ∈ A.circularGapRegularFiber l g := by
    change q ∈ A.geometricEdgeOpenArc (A.circularGapEdge l g)
    rw [hg]
    exact hqArc
  have hrFiber : r' ∈ A.circularGapRegularFiber l k := by
    change r ∈ A.geometricEdgeOpenArc (A.circularGapEdge l k)
    rw [hk]
    exact hrArc
  have hjoined : Joined q' r' :=
    A.joined_lineRegularLocus_of_same_face_closure
      hA l F q' r' hqF hrF
  have hgk : g = k :=
    A.circularGap_eq_of_joined_regular_of_isOpen hA l
      (fun s => A.isOpen_circularGapRegularFiber l s)
      q' r' g k hqFiber hrFiber hjoined
  calc
    e = A.circularGapEdge l g := hg.symm
    _ = A.circularGapEdge l k := congrArg (A.circularGapEdge l) hgk
    _ = e' := hk

/-- If a finite family of inequalities already defines a face cone, every
literal boundary support belongs to that family. -/
theorem edgeSlotLine_mem_of_mem_boundary_of_coneOn_eq
    (A : FiniteProjectiveLineArrangement Line) (hA : A.NonPencil)
    (base : Line) (F : A.ArrangementFace) (K : Finset Line)
    (e : A.GeometricEdge)
    (hbase : base ≠ A.edgeSlotLine e)
    (hcone : A.arrangementClosedSignConeOn
        (A.arrangementFaceSignPattern base F) K =
      A.arrangementClosedSignCone (A.arrangementFaceSignPattern base F))
    (he : e ∈ A.arrangementFaceBoundary F) :
    A.edgeSlotLine e ∈ K := by
  classical
  let sigma := A.arrangementFaceSignPattern base F
  let l := A.edgeSlotLine e
  by_contra hlK
  obtain ⟨q, hqArc, hqF⟩ :=
    (A.mem_arrangementFaceBoundary_iff F e).mp he
  have hregular : ∀ m : Line, A.Incident q m ↔ m = l := by
    intro m
    simpa only [l] using A.geometricEdgeOpenArc_incident_iff e hqArc m
  have hqbase : ¬ A.Incident q base := by
    intro h
    exact hbase ((hregular base).mp h)
  let v := A.arrangementPointNormalizedRepresentativeAt base q
  have hv0 : v ≠ 0 := by
    simpa only [v] using
      A.arrangementPointNormalizedRepresentativeAt_ne_zero base q hqbase
  have hvFull : v ∈ A.arrangementClosedSignCone sigma := by
    simpa only [v, sigma] using
      A.arrangementPointNormalizedRepresentativeAt_mem_closedSignCone_of_mem_closure
        q base F hqbase hqF
  have hvl : A.arrangementOrientedEvaluation sigma l v = 0 := by
    apply (A.incident_projectivization_mk_iff_orientedEvaluation_eq_zero
      sigma l v hv0).1
    rw [show Projectivization.mk ℝ v hv0 = q by
      simpa only [v] using
        A.projectivization_mk_arrangementPointNormalizedRepresentativeAt
          base q hqbase]
    exact (hregular l).mpr rfl
  have hvOpen : v ∈ A.arrangementSignConeOn sigma K := by
    rw [A.mem_arrangementSignConeOn]
    intro m hm
    apply A.arrangementOrientedEvaluation_normalized_pos_of_mem_closure_of_not_incident
      q base F hqbase hqF m
    intro hqm
    have hml : m = l := (hregular m).mp hqm
    subst m
    exact hlK hm
  obtain ⟨n, hnl⟩ := A.exists_ne_line_of_nonPencil hA l
  obtain ⟨w, _hnw, hlw⟩ :=
    A.exists_orientedEvaluation_neg_on_kernel_of_ne sigma hnl
  let curve : ℝ → (Fin 3 → ℝ) := fun t => v + t • w
  have hcurve : Continuous curve :=
    continuous_const.add (continuous_id.smul continuous_const)
  have hevent : ∀ᶠ t in 𝓝 (0 : ℝ),
      curve t ∈ A.arrangementSignConeOn sigma K :=
    hcurve.continuousAt.eventually
      ((A.isOpen_arrangementSignConeOn sigma K).mem_nhds (by
        simpa only [curve, zero_smul, add_zero] using hvOpen))
  obtain ⟨epsilon, hepsilon, hstable⟩ :=
    Metric.eventually_nhds_iff.mp hevent
  let delta : ℝ := epsilon / 2
  have hdelta : 0 < delta := by
    dsimp only [delta]
    linarith
  have hdist : dist delta (0 : ℝ) < epsilon := by
    rw [Real.dist_eq, sub_zero, abs_of_pos hdelta]
    dsimp only [delta]
    linarith
  have hpertOpen := hstable hdist
  have hpertK : curve delta ∈ A.arrangementClosedSignConeOn sigma K := by
    rw [A.mem_arrangementClosedSignConeOn]
    intro m hm
    exact ((A.mem_arrangementSignConeOn sigma K (curve delta)).mp
      hpertOpen m hm).le
  have hpertFull : curve delta ∈ A.arrangementClosedSignCone sigma := by
    rw [← hcone]
    exact hpertK
  have hpertNeg : A.arrangementOrientedEvaluation sigma l
      (curve delta) < 0 := by
    dsimp only [curve]
    rw [LinearMap.map_add, LinearMap.map_smul, hvl,
      smul_eq_mul, zero_add]
    exact mul_neg_of_pos_of_neg hdelta hlw
  have hpertNonneg : 0 ≤ A.arrangementOrientedEvaluation sigma l
      (curve delta) :=
    (A.mem_arrangementClosedSignCone_iff_orientedEvaluation_nonneg
      sigma (curve delta)).mp hpertFull l
  exact (not_lt_of_ge hpertNonneg hpertNeg)

/-- If the same finite support family defines a face cone in every affine
sign chart, it bounds every literal boundary edge of that face. -/
theorem arrangementFaceBoundary_card_le_of_coneOn_eq
    (A : FiniteProjectiveLineArrangement Line) (hA : A.NonPencil)
    (F : A.ArrangementFace) (K : Finset Line)
    (hcone : ∀ base : Line,
      A.arrangementClosedSignConeOn
          (A.arrangementFaceSignPattern base F) K =
        A.arrangementClosedSignCone
          (A.arrangementFaceSignPattern base F)) :
    (A.arrangementFaceBoundary F).card ≤ K.card := by
  classical
  let support : {e // e ∈ A.arrangementFaceBoundary F} → {l // l ∈ K} :=
    fun e =>
      let base := (A.exists_ne_line_of_nonPencil hA
        (A.edgeSlotLine e.1)).choose
      ⟨A.edgeSlotLine e.1,
        A.edgeSlotLine_mem_of_mem_boundary_of_coneOn_eq
          hA base F K e.1
          (A.exists_ne_line_of_nonPencil hA
            (A.edgeSlotLine e.1)).choose_spec
          (hcone base) e.2⟩
  have hinjective : Function.Injective support := by
    intro e e' heq
    apply Subtype.ext
    apply A.edgeSlotLine_injective_on_arrangementFaceBoundary hA F e.2 e'.2
    exact congrArg Subtype.val heq
  have hcard := Fintype.card_le_of_injective support hinjective
  simpa only [Fintype.card_coe] using hcard

/-- Converse triangle materialization: a face whose closed cone is cut out
by three distinct supports has exactly three literal boundary edges. -/
theorem arrangementFaceBoundary_card_eq_three_of_three_cone
    (A : FiniteProjectiveLineArrangement Line) (hA : A.NonPencil)
    (F : A.ArrangementFace) (l a b : Line)
    (hal : a ≠ l) (hbl : b ≠ l) (hab : a ≠ b)
    (hcone : ∀ base : Line,
      A.arrangementClosedSignConeOn
          (A.arrangementFaceSignPattern base F) {l, a, b} =
        A.arrangementClosedSignCone
          (A.arrangementFaceSignPattern base F)) :
    (A.arrangementFaceBoundary F).card = 3 := by
  apply Nat.le_antisymm
  · calc
      (A.arrangementFaceBoundary F).card ≤ ({l, a, b} : Finset Line).card :=
        A.arrangementFaceBoundary_card_le_of_coneOn_eq hA F {l, a, b} hcone
      _ = 3 := by
        simp [hal, hbl, hab, Ne.symm hal, Ne.symm hbl, Ne.symm hab]
  · exact A.three_le_arrangementFaceBoundary_card hA l F

/-- A strict point plus the absence of any further zero on a strict
subfamily cone shows that the corresponding weak inequalities already cut
out the full closed cone.  The zero-producing vector is an explicit positive
linear combination, so no compactness or IVT is needed. -/
theorem arrangementClosedSignConeOn_eq_of_no_additional_zero
    (A : FiniteProjectiveLineArrangement Line) (sigma : Line → Bool)
    (K : Finset Line) (u : Fin 3 → ℝ)
    (hu : u ∈ A.arrangementSignCone sigma)
    (hnozero : ∀ m : Line, m ∉ K →
      ∀ v ∈ A.arrangementSignConeOn sigma K,
        A.arrangementOrientedEvaluation sigma m v ≠ 0) :
    A.arrangementClosedSignConeOn sigma K =
      A.arrangementClosedSignCone sigma := by
  apply Set.Subset.antisymm
  · intro v hvK
    rw [A.mem_arrangementClosedSignCone_iff_orientedEvaluation_nonneg]
    intro m
    by_cases hmK : m ∈ K
    · exact (A.mem_arrangementClosedSignConeOn sigma K v).mp hvK m hmK
    · let fu := A.arrangementOrientedEvaluation sigma m u
      let fv := A.arrangementOrientedEvaluation sigma m v
      have hfu : 0 < fu := by
        simpa only [fu] using
          (A.mem_arrangementSignCone_iff_orientedEvaluation_pos sigma u).mp hu m
      by_contra hfvNonneg
      have hfv : fv < 0 := lt_of_not_ge hfvNonneg
      let z : Fin 3 → ℝ := (-fv) • u + fu • v
      have hzK : z ∈ A.arrangementSignConeOn sigma K := by
        rw [A.mem_arrangementSignConeOn]
        intro k hk
        have huk :=
          (A.mem_arrangementSignCone_iff_orientedEvaluation_pos sigma u).mp
            hu k
        have hvk :=
          (A.mem_arrangementClosedSignConeOn sigma K v).mp hvK k hk
        dsimp only [z]
        rw [LinearMap.map_add, LinearMap.map_smul,
          LinearMap.map_smul, smul_eq_mul, smul_eq_mul]
        exact add_pos_of_pos_of_nonneg
          (mul_pos (neg_pos.mpr hfv) huk) (mul_nonneg hfu.le hvk)
      apply hnozero m hmK z hzK
      dsimp only [z]
      rw [LinearMap.map_add, LinearMap.map_smul,
        LinearMap.map_smul, smul_eq_mul, smul_eq_mul]
      change -fv * fu + fu * fv = 0
      ring
  · intro v hv
    rw [A.mem_arrangementClosedSignConeOn]
    intro k _hk
    exact (A.mem_arrangementClosedSignCone_iff_orientedEvaluation_nonneg
      sigma v).mp hv k

/-- A strict three-sided chamber with no additional line zero materializes
as a literal triangular arrangement face, including a boundary edge on each
of its three named supports. -/
theorem exists_triangle_face_of_no_additional_zero
    (A : FiniteProjectiveLineArrangement Line) (hA : A.NonPencil)
    (p : A.ArrangementComplement) (l a b : Line)
    (hal : a ≠ l) (hbl : b ≠ l) (hab : a ≠ b)
    (hnozero : ∀ base m : Line, m ∉ ({l, a, b} : Finset Line) →
      ∀ v ∈ A.arrangementSignConeOn
          (A.arrangementPointSignPattern base p) {l, a, b},
        A.arrangementOrientedEvaluation
          (A.arrangementPointSignPattern base p) m v ≠ 0) :
    ∃ F : A.ArrangementFace, ∃ e : A.GeometricEdge,
      F = A.arrangementFaceOf p ∧
      (A.arrangementFaceBoundary F).card = 3 ∧
      e ∈ A.arrangementFaceBoundary F ∧ A.edgeSlotLine e = l := by
  classical
  let F := A.arrangementFaceOf p
  have hpattern : ∀ base : Line,
      A.arrangementFaceSignPattern base F =
        A.arrangementPointSignPattern base p := by
    intro base
    change A.arrangementPointSignPattern base
        (A.arrangementFaceRepresentative F) =
      A.arrangementPointSignPattern base p
    apply A.arrangementPointSignPattern_eq_of_arrangementFaceOf_eq
    simpa only [F] using A.arrangementFaceRepresentative_faceOf F
  have hcone : ∀ base : Line,
      A.arrangementClosedSignConeOn
          (A.arrangementFaceSignPattern base F) {l, a, b} =
        A.arrangementClosedSignCone
          (A.arrangementFaceSignPattern base F) := by
    intro base
    have hu := A.arrangementNormalizedRepresentative_mem_arrangementSignCone
      base p
    have h := A.arrangementClosedSignConeOn_eq_of_no_additional_zero
      (A.arrangementPointSignPattern base p) {l, a, b}
      (A.arrangementNormalizedRepresentative base p) hu
      (hnozero base)
    simpa only [hpattern base] using h
  have htri : (A.arrangementFaceBoundary F).card = 3 :=
    A.arrangementFaceBoundary_card_eq_three_of_three_cone
      hA F l a b hal hbl hab hcone
  let sigma := A.arrangementFaceSignPattern l F
  have hK := hcone l
  have hminimal : ∀ L : Finset Line,
      A.arrangementClosedSignConeOn sigma L =
        A.arrangementClosedSignCone sigma →
      ({l, a, b} : Finset Line).card ≤ L.card := by
    intro L hL
    have hthree :=
      A.three_le_card_of_arrangementClosedSignConeOn_eq hA sigma L hL
    simpa only [show ({l, a, b} : Finset Line).card = 3 by
      simp [hal, hbl, hab, Ne.symm hal, Ne.symm hbl, Ne.symm hab]]
      using hthree
  obtain ⟨e, heLine, heMem⟩ :=
    A.exists_boundaryEdge_supported_by_cardMinimal_index
      hA l F {l, a, b} hK hminimal (l := l) (by simp)
  exact ⟨F, e, rfl, htri, heMem, heLine⟩

/-- Direct Felsner attachment constructor once the minimizing subtriangle
has been shown to contain no additional arrangement-line zero. -/
theorem ordinaryVertexAttachedToLine_of_no_additional_zero
    (A : FiniteProjectiveLineArrangement Line) (hA : A.NonPencil)
    (q : A.OrdinaryVertex) (p : A.ArrangementComplement)
    (l a b : Line) (hal : a ≠ l) (hbl : b ≠ l) (hab : a ≠ b)
    (hql : ¬ A.Incident q.1 l)
    (hnozero : ∀ base m : Line, m ∉ ({l, a, b} : Finset Line) →
      ∀ v ∈ A.arrangementSignConeOn
          (A.arrangementPointSignPattern base p) {l, a, b},
        A.arrangementOrientedEvaluation
          (A.arrangementPointSignPattern base p) m v ≠ 0)
    (hqCone : A.arrangementPointNormalizedRepresentativeAt l q.1 ∈
      A.arrangementClosedSignConeOn
        (A.arrangementPointSignPattern l p) {l, a, b}) :
    A.OrdinaryVertexAttachedToLine q l := by
  classical
  obtain ⟨F, e, hF, htri, heMem, heLine⟩ :=
    A.exists_triangle_face_of_no_additional_zero
      hA p l a b hal hbl hab hnozero
  subst F
  have hpattern : A.arrangementFaceSignPattern l (A.arrangementFaceOf p) =
      A.arrangementPointSignPattern l p := by
    change A.arrangementPointSignPattern l
        (A.arrangementFaceRepresentative (A.arrangementFaceOf p)) =
      A.arrangementPointSignPattern l p
    apply A.arrangementPointSignPattern_eq_of_arrangementFaceOf_eq
    exact A.arrangementFaceRepresentative_faceOf (A.arrangementFaceOf p)
  have hu := A.arrangementNormalizedRepresentative_mem_arrangementSignCone
    l p
  have hconePoint := A.arrangementClosedSignConeOn_eq_of_no_additional_zero
    (A.arrangementPointSignPattern l p) {l, a, b}
    (A.arrangementNormalizedRepresentative l p) hu (hnozero l)
  have hqFullPoint : A.arrangementPointNormalizedRepresentativeAt l q.1 ∈
      A.arrangementClosedSignCone (A.arrangementPointSignPattern l p) := by
    rw [← hconePoint]
    exact hqCone
  have hqFullFace : A.arrangementPointNormalizedRepresentativeAt l q.1 ∈
      A.arrangementClosedSignCone
        (A.arrangementFaceSignPattern l (A.arrangementFaceOf p)) := by
    simpa only [hpattern] using hqFullPoint
  have hq0 :=
    A.arrangementPointNormalizedRepresentativeAt_ne_zero l q.1 hql
  have hqClosure' : Projectivization.mk ℝ
      (A.arrangementPointNormalizedRepresentativeAt l q.1) hq0 ∈
        closure (A.arrangementFaceCarrier (A.arrangementFaceOf p)) :=
    A.projectivization_mem_closure_arrangementFaceCarrier_of_mem_closedSignCone
      l (A.arrangementFaceOf p) hq0 hqFullFace
  have hqClosure : q.1 ∈
      closure (A.arrangementFaceCarrier (A.arrangementFaceOf p)) := by
    simpa only [A.projectivization_mk_arrangementPointNormalizedRepresentativeAt
      l q.1 hql] using hqClosure'
  exact ⟨⟨A.arrangementFaceOf p, e, hql, htri, heMem, heLine, hqClosure⟩⟩

/-- Any additional line zero in the strict subtriangle below an ordinary
apex produces an actual off-base vertex of strictly smaller fixed-chart
height on one of the two side segments. -/
theorem exists_smaller_vertex_of_additional_zero
    (A : FiniteProjectiveLineArrangement Line) (sigma : Line → Bool)
    (fixedGauge : (Fin 3 → ℝ) →ₗ[ℝ] ℝ)
    (q : A.OrdinaryVertex) (l a b m : Line) (Z : Fin 3 → ℝ)
    (htriangle : ¬ ∃ r : RealProjectivePoint,
      A.Incident r l ∧ A.Incident r a ∧ A.Incident r b)
    (hla : l ≠ a) (hlb : l ≠ b) (hab : a ≠ b)
    (hmK : m ∉ ({l, a, b} : Finset Line))
    (hqaway : ¬ A.Incident q.1 l)
    (hqa : A.Incident q.1 a) (hqb : A.Incident q.1 b)
    (hordinary : ∀ k : Line,
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
    (hZ : Z ∈ A.arrangementSignConeOn sigma {l, a, b})
    (hZm : A.arrangementOrientedEvaluation sigma m Z = 0) :
    ∃ y : RealProjectivePoint, ∃ h : ℝ,
      0 < h ∧ h < 1 ∧ y ∈ A.vertexSet ∧
      ¬ A.Incident y l ∧
      A.vertexChartLineHeight fixedGauge l y <
        A.vertexChartLineHeight fixedGauge l q.1 ∧
      ((A.Incident y a ∧
        vertexChartNormalizedVector fixedGauge y =
          (1 - h) • vertexChartNormalizedVector fixedGauge
              (A.intersection l a) +
            h • vertexChartNormalizedVector fixedGauge q.1) ∨
       (A.Incident y b ∧
        vertexChartNormalizedVector fixedGauge y =
          (1 - h) • vertexChartNormalizedVector fixedGauge
              (A.intersection l b) +
            h • vertexChartNormalizedVector fixedGauge q.1)) := by
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
        sigma fixedGauge hfV1 (A.intersection_incident_left hla)
  have hV1left : A.arrangementOrientedEvaluation sigma a V1 = 0 := by
    simpa only [V1] using
      A.arrangementOrientedEvaluation_vertexChartNormalizedVector_eq_zero
        sigma fixedGauge hfV1 (A.intersection_incident_right hla)
  have hV3base : A.arrangementOrientedEvaluation sigma l V3 = 0 := by
    simpa only [V3] using
      A.arrangementOrientedEvaluation_vertexChartNormalizedVector_eq_zero
        sigma fixedGauge hfV3 (A.intersection_incident_left hlb)
  have hV3right : A.arrangementOrientedEvaluation sigma b V3 = 0 := by
    simpa only [V3] using
      A.arrangementOrientedEvaluation_vertexChartNormalizedVector_eq_zero
        sigma fixedGauge hfV3 (A.intersection_incident_right hlb)
  have hXm : A.arrangementOrientedEvaluation sigma m X ≠ 0 := by
    apply A.arrangementOrientedEvaluation_vertexChartNormalizedVector_ne_zero
      sigma fixedGauge hfq
    intro hqm
    rcases (hordinary m).mp hqm with hma | hmb
    · subst m
      exact hmK (by simp)
    · subst m
      exact hmK (by simp)
  have hZbase : 0 < A.arrangementOrientedEvaluation sigma l Z :=
    hZ l (by simp)
  have hZleft : 0 < A.arrangementOrientedEvaluation sigma a Z :=
    hZ a (by simp)
  have hZright : 0 < A.arrangementOrientedEvaluation sigma b Z :=
    hZ b (by simp)
  have hkernel : ∀ W,
      A.arrangementOrientedEvaluation sigma l W = 0 →
      A.arrangementOrientedEvaluation sigma a W = 0 →
      A.arrangementOrientedEvaluation sigma b W = 0 → W = 0 :=
    fun W hl ha hb =>
      A.eq_zero_of_three_orientedEvaluations_eq_zero
        sigma l a b htriangle W hl ha hb
  rcases exists_side_barycentric_zero_of_strict_triangle_zero
      (A.arrangementOrientedEvaluation sigma l)
      (A.arrangementOrientedEvaluation sigma a)
      (A.arrangementOrientedEvaluation sigma b)
      (A.arrangementOrientedEvaluation sigma m)
      hkernel hXbase hXleft hXright
      hV1base hV1left (by simpa only [V1] using hV1right)
      hV3base (by simpa only [V3] using hV3left) hV3right
      hZbase hZleft hZright hZm hXm with hleft | hright
  · rcases hleft with ⟨h, hh0, hh1, hYm⟩
    have hYa : A.arrangementOrientedEvaluation sigma a
        ((1 - h) • V1 + h • X) = 0 := by
      rw [LinearMap.map_add, LinearMap.map_smul, LinearMap.map_smul,
        hV1left, hXleft]
      simp
    have hma : m ≠ a := by
      intro h
      subst m
      exact hmK (by simp)
    obtain ⟨y, hyVertex, _hym, hya, hyl, hyNorm, _hyHeight, hylt⟩ :=
      A.fixedChartExit_finish_branch sigma fixedGauge l m a q.1
        hh0 hh1 rfl
        (by
          intro hzero
          have hfg := congrArg fixedGauge hzero
          have hV1gauge : fixedGauge V1 = 1 := by
            simpa only [V1] using
              (vertexChartNormalizedVector_fixedGauge_eq_one fixedGauge
                (A.intersection l a) hfV1)
          have hQgauge :
              fixedGauge (vertexChartNormalizedVector fixedGauge q.1) = 1 :=
            vertexChartNormalizedVector_fixedGauge_eq_one fixedGauge q.1 hfq
          rw [LinearMap.map_zero, LinearMap.map_add,
            LinearMap.map_smul, LinearMap.map_smul,
            hV1gauge, hQgauge] at hfg
          simp only [smul_eq_mul, mul_one] at hfg
          linarith)
        hma hYm hYa hV1base
        (by
          simpa only [V1] using
            (vertexChartNormalizedVector_fixedGauge_eq_one fixedGauge
              (A.intersection l a) hfV1))
        (by
          simpa only [X] using
            (vertexChartNormalizedVector_fixedGauge_eq_one
              fixedGauge q.1 hfq))
        hXbase.ne' rfl
    exact ⟨y, h, hh0, hh1, hyVertex, hyl, hylt,
      Or.inl ⟨hya, by simpa only [V1, X] using hyNorm⟩⟩
  · rcases hright with ⟨h, hh0, hh1, hYm⟩
    have hYb : A.arrangementOrientedEvaluation sigma b
        ((1 - h) • V3 + h • X) = 0 := by
      rw [LinearMap.map_add, LinearMap.map_smul, LinearMap.map_smul,
        hV3right, hXright]
      simp
    have hmb : m ≠ b := by
      intro h
      subst m
      exact hmK (by simp)
    obtain ⟨y, hyVertex, _hym, hyb, hyl, hyNorm, _hyHeight, hylt⟩ :=
      A.fixedChartExit_finish_branch sigma fixedGauge l m b q.1
        hh0 hh1 rfl
        (by
          intro hzero
          have hfg := congrArg fixedGauge hzero
          have hV3gauge : fixedGauge V3 = 1 := by
            simpa only [V3] using
              (vertexChartNormalizedVector_fixedGauge_eq_one fixedGauge
                (A.intersection l b) hfV3)
          have hQgauge :
              fixedGauge (vertexChartNormalizedVector fixedGauge q.1) = 1 :=
            vertexChartNormalizedVector_fixedGauge_eq_one fixedGauge q.1 hfq
          rw [LinearMap.map_zero, LinearMap.map_add,
            LinearMap.map_smul, LinearMap.map_smul,
            hV3gauge, hQgauge] at hfg
          simp only [smul_eq_mul, mul_one] at hfg
          linarith)
        hmb hYm hYb hV3base
        (by
          simpa only [V3] using
            (vertexChartNormalizedVector_fixedGauge_eq_one fixedGauge
              (A.intersection l b) hfV3))
        (by
          simpa only [X] using
            (vertexChartNormalizedVector_fixedGauge_eq_one
              fixedGauge q.1 hfq))
        hXbase.ne' rfl
    exact ⟨y, h, hh0, hh1, hyVertex, hyl, hylt,
      Or.inr ⟨hyb, by simpa only [V3, X] using hyNorm⟩⟩

/-- The triangle gauge packaged as a linear map, so it can be kept fixed
while smaller triangles are cut out inside the original sector. -/
noncomputable def triangleSectorFixedGauge
    (A : FiniteProjectiveLineArrangement Line) (sigma : Line → Bool)
    (l a b : Line) : (Fin 3 → ℝ) →ₗ[ℝ] ℝ :=
  A.arrangementOrientedEvaluation sigma l +
    A.arrangementOrientedEvaluation sigma a +
      A.arrangementOrientedEvaluation sigma b

@[simp]
theorem triangleSectorFixedGauge_apply
    (A : FiniteProjectiveLineArrangement Line) (sigma : Line → Bool)
    (l a b : Line) (v : Fin 3 → ℝ) :
    A.triangleSectorFixedGauge sigma l a b v =
      A.triangleSectorGauge sigma l a b v := by
  simp [triangleSectorFixedGauge, triangleSectorGauge]

@[simp]
theorem vertexChartNormalizedVector_triangleSectorFixedGauge
    (A : FiniteProjectiveLineArrangement Line) (sigma : Line → Bool)
    (l a b : Line) (q : RealProjectivePoint) :
    vertexChartNormalizedVector
        (A.triangleSectorFixedGauge sigma l a b) q =
      A.triangleSectorNormalizedVector sigma l a b q.rep := by
  simp [vertexChartNormalizedVector, triangleSectorNormalizedVector]

/-- Finite closest-vertex selection inside one projective triangle sector,
using the single affine chart fixed for the whole Kelly--Moser argument. -/
theorem exists_minimal_fixedChartLineHeight_in_triangleSector
    (A : FiniteProjectiveLineArrangement Line) (sigma : Line → Bool)
    (f : (Fin 3 → ℝ) →ₗ[ℝ] ℝ) (l a b : Line)
    (hf : ∀ q : RealProjectivePoint, q ∈ A.vertexSet → f q.rep ≠ 0)
    (hS : (A.triangleSectorOffBaseVertexSet sigma l a b).Nonempty) :
    ∃ x : RealProjectivePoint,
      x ∈ A.vertexSet ∧
      A.projectivePointMemTriangleSector sigma l a b x ∧
      ¬ A.Incident x l ∧
      0 < A.vertexChartLineHeight f l x ∧
      ∀ y : RealProjectivePoint, y ∈ A.vertexSet →
        A.projectivePointMemTriangleSector sigma l a b y →
        ¬ A.Incident y l →
        A.vertexChartLineHeight f l x ≤
          A.vertexChartLineHeight f l y := by
  classical
  obtain ⟨x, hxS, hmin⟩ :=
    A.exists_minimal_vertexChartLineHeight f l
      (A.triangleSectorOffBaseVertexSet sigma l a b) hS
  have hx := Finset.mem_filter.mp hxS
  refine ⟨x, hx.1, hx.2.1, hx.2.2,
    A.vertexChartLineHeight_pos f l x (hf x hx.1) hx.2.2, ?_⟩
  intro y hyVertex hySector hyl
  exact hmin y (Finset.mem_filter.mpr
    ⟨hyVertex, hySector, hyl⟩)

/-- Closest vertex in a triangle, measured in the affine gauge of that
original triangle.  This gauge stays fixed when the exit argument chooses
three different supports through the minimizing vertex. -/
theorem exists_minimal_originalTriangleGaugeLineHeight
    (A : FiniteProjectiveLineArrangement Line) (sigma : Line → Bool)
    (l a b : Line)
    (htriangle : ¬ ∃ q : RealProjectivePoint,
      A.Incident q l ∧ A.Incident q a ∧ A.Incident q b)
    (hS : (A.triangleSectorOffBaseVertexSet sigma l a b).Nonempty) :
    ∃ x : RealProjectivePoint,
      x ∈ A.vertexSet ∧
      A.projectivePointMemTriangleSector sigma l a b x ∧
      ¬ A.Incident x l ∧
      0 < A.vertexChartLineHeight
        (A.triangleSectorFixedGauge sigma l a b) l x ∧
      ∀ y : RealProjectivePoint, y ∈ A.vertexSet →
        A.projectivePointMemTriangleSector sigma l a b y →
        ¬ A.Incident y l →
        A.vertexChartLineHeight
            (A.triangleSectorFixedGauge sigma l a b) l x ≤
          A.vertexChartLineHeight
            (A.triangleSectorFixedGauge sigma l a b) l y := by
  classical
  obtain ⟨x, hxS, hmin⟩ :=
    A.exists_minimal_vertexChartLineHeight
      (A.triangleSectorFixedGauge sigma l a b) l
      (A.triangleSectorOffBaseVertexSet sigma l a b) hS
  have hx := Finset.mem_filter.mp hxS
  have hfx : A.triangleSectorFixedGauge sigma l a b x.rep ≠ 0 := by
    simpa only [A.triangleSectorFixedGauge_apply] using
      A.triangleSectorGauge_ne_zero_of_projective
        sigma l a b htriangle x hx.2.1
  refine ⟨x, hx.1, hx.2.1, hx.2.2,
    A.vertexChartLineHeight_pos
      (A.triangleSectorFixedGauge sigma l a b) l x hfx hx.2.2, ?_⟩
  intro y hyVertex hySector hyl
  exact hmin y (Finset.mem_filter.mpr
    ⟨hyVertex, hySector, hyl⟩)

/-- The fixed-chart exit with its affine coordinate axis separated from the
two outer supports.  This separation makes sorting three arbitrary returns
a literal six-case linear-order argument. -/
theorem fixedChart_transportedBarycentric_with_axis
    (base axis left right fixedGauge middle :
      (Fin 3 → ℝ) →ₗ[ℝ] ℝ)
    {X V1 V3 : Fin 3 → ℝ}
    (hkernel : ∀ Z, base Z = 0 → axis Z = 0 →
      fixedGauge Z = 0 → Z = 0)
    (hbaseX : base X ≠ 0)
    (hgaugeX : fixedGauge X = 1)
    (hbaseV1 : base V1 = 0) (hgaugeV1 : fixedGauge V1 = 1)
    (hbaseV3 : base V3 = 0) (hgaugeV3 : fixedGauge V3 = 1)
    (t2 delta : ℝ) (h12 : axis V1 < t2) (h23 : t2 < axis V3)
    (hdelta : delta ≠ 0)
    (hform : ∀ Z, middle Z =
      fixedChartExitCoordinateEquiv base axis fixedGauge X
          hkernel hbaseX Z ⬝ᵥ
        triangleExitMiddleCovector t2 delta)
    (hleftV : left V1 = 0) (hleftX : left X = 0)
    (hrightV : right V3 = 0) (hrightX : right X = 0) :
    (∃ h : ℝ, 0 < h ∧ h < 1 ∧
      let Y := (1 - h) • V1 + h • X
      Y ≠ 0 ∧ middle Y = 0 ∧ left Y = 0) ∨
    (∃ h : ℝ, 0 < h ∧ h < 1 ∧
      let Y := (1 - h) • V3 + h • X
      Y ≠ 0 ∧ middle Y = 0 ∧ right Y = 0) := by
  let coord := fixedChartExitCoordinateEquiv
    base axis fixedGauge X hkernel hbaseX
  have hcoordX : coord X = homogeneousLift (triangleExitTopPoint 0) := by
    simpa only [coord, fixedChartExitCoordinateEquiv_apply] using
      fixedChartExitCoordinateMap_apex base axis fixedGauge
        hbaseX hgaugeX
  have hcoordV1 : coord V1 =
      homogeneousLift (triangleExitBasePoint (axis V1)) := by
    simpa only [coord, fixedChartExitCoordinateEquiv_apply] using
      fixedChartExitCoordinateMap_base base axis fixedGauge X
        hbaseV1 hgaugeV1
  have hcoordV3 : coord V3 =
      homogeneousLift (triangleExitBasePoint (axis V3)) := by
    simpa only [coord, fixedChartExitCoordinateEquiv_apply] using
      fixedChartExitCoordinateMap_base base axis fixedGauge X
        hbaseV3 hgaugeV3
  have hform' : ∀ Z, middle Z =
      coord Z ⬝ᵥ triangleExitMiddleCovector t2 delta := by
    simpa only [coord] using hform
  rcases triangleExit_transportedBarycentric coord middle left right
      (axis V1) t2 (axis V3) delta h12 h23 hdelta
      hcoordX hcoordV1 hcoordV3 hform'
      hleftV hleftX hrightV hrightX with hleft | hright
  · left
    rcases hleft with ⟨h, hh0, hh1, hY0, hYm, hYa, _⟩
    exact ⟨h, hh0, hh1, hY0, hYm, hYa⟩
  · right
    rcases hright with ⟨h, hh0, hh1, hY0, hYm, hYb, _⟩
    exact ⟨h, hh0, hh1, hY0, hYm, hYb⟩

/-- Ordered arrangement exit with a separately chosen affine axis. -/
theorem fixedChartExit_barycentric_axis_ordered
    (A : FiniteProjectiveLineArrangement Line) (sigma : Line → Bool)
    (fixedGauge : (Fin 3 → ℝ) →ₗ[ℝ] ℝ)
    (l axis left right middle m : Line) (x : RealProjectivePoint)
    (hgauge : ∀ q : RealProjectivePoint, q ∈ A.vertexSet →
      fixedGauge q.rep ≠ 0)
    (hxVertex : x ∈ A.vertexSet)
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
    (∃ h : ℝ, ∃ Y : Fin 3 → ℝ,
      0 < h ∧ h < 1 ∧
      Y = (1 - h) • vertexChartNormalizedVector fixedGauge
          (A.intersection l left) +
        h • vertexChartNormalizedVector fixedGauge x ∧
      Y ≠ 0 ∧
      A.arrangementOrientedEvaluation sigma m Y = 0 ∧
      A.arrangementOrientedEvaluation sigma left Y = 0) ∨
    (∃ h : ℝ, ∃ Y : Fin 3 → ℝ,
      0 < h ∧ h < 1 ∧
      Y = (1 - h) • vertexChartNormalizedVector fixedGauge
          (A.intersection l right) +
        h • vertexChartNormalizedVector fixedGauge x ∧
      Y ≠ 0 ∧
      A.arrangementOrientedEvaluation sigma m Y = 0 ∧
      A.arrangementOrientedEvaluation sigma right Y = 0) := by
  let v1 := A.intersection l left
  let v2 := A.intersection l middle
  let v3 := A.intersection l right
  have hv1Vertex : v1 ∈ A.vertexSet := by
    simpa only [v1] using A.intersection_mem_vertexSet hlleft
  have hv2Vertex : v2 ∈ A.vertexSet := by
    simpa only [v2] using A.intersection_mem_vertexSet hlmiddle
  have hv3Vertex : v3 ∈ A.vertexSet := by
    simpa only [v3] using A.intersection_mem_vertexSet hlright
  have hfx := hgauge x hxVertex
  have hfv1 := hgauge v1 hv1Vertex
  have hfv2 := hgauge v2 hv2Vertex
  have hfv3 := hgauge v3 hv3Vertex
  have hfaxis := hgauge (A.intersection l axis)
    (A.intersection_mem_vertexSet hlaxis)
  let X := vertexChartNormalizedVector fixedGauge x
  let V1 := vertexChartNormalizedVector fixedGauge v1
  let V2 := vertexChartNormalizedVector fixedGauge v2
  let V3 := vertexChartNormalizedVector fixedGauge v3
  have hX0 : X ≠ 0 := vertexChartNormalizedVector_ne_zero _ _ hfx
  have hmkX : Projectivization.mk ℝ X hX0 = x := by
    simpa only [X] using
      projectivization_mk_vertexChartNormalizedVector fixedGauge x hfx
  have hXgauge : fixedGauge X = 1 := by
    simpa only [X] using
      vertexChartNormalizedVector_fixedGauge_eq_one fixedGauge x hfx
  have hXbase : A.arrangementOrientedEvaluation sigma l X ≠ 0 := by
    simpa only [X] using
      A.arrangementOrientedEvaluation_vertexChartNormalizedVector_ne_zero
        sigma fixedGauge hfx hxNotBase
  have hV1base : A.arrangementOrientedEvaluation sigma l V1 = 0 := by
    apply A.arrangementOrientedEvaluation_vertexChartNormalizedVector_eq_zero
      sigma fixedGauge hfv1
    simpa only [v1] using A.intersection_incident_left hlleft
  have hV2base : A.arrangementOrientedEvaluation sigma l V2 = 0 := by
    apply A.arrangementOrientedEvaluation_vertexChartNormalizedVector_eq_zero
      sigma fixedGauge hfv2
    simpa only [v2] using A.intersection_incident_left hlmiddle
  have hV3base : A.arrangementOrientedEvaluation sigma l V3 = 0 := by
    apply A.arrangementOrientedEvaluation_vertexChartNormalizedVector_eq_zero
      sigma fixedGauge hfv3
    simpa only [v3] using A.intersection_incident_left hlright
  have hV1gauge : fixedGauge V1 = 1 := by
    simpa only [V1] using
      vertexChartNormalizedVector_fixedGauge_eq_one fixedGauge v1 hfv1
  have hV2gauge : fixedGauge V2 = 1 := by
    simpa only [V2] using
      vertexChartNormalizedVector_fixedGauge_eq_one fixedGauge v2 hfv2
  have hV3gauge : fixedGauge V3 = 1 := by
    simpa only [V3] using
      vertexChartNormalizedVector_fixedGauge_eq_one fixedGauge v3 hfv3
  have hV2evalM : A.arrangementOrientedEvaluation sigma m V2 = 0 :=
    A.arrangementOrientedEvaluation_vertexChartNormalizedVector_eq_zero
      sigma fixedGauge hfv2 (by simpa only [v2] using hV2m)
  obtain ⟨scale, delta, hscale, hdelta, hform⟩ :=
    A.exists_fixedChart_middle_normalForm_delta_ne_zero
      sigma fixedGauge hlaxis hlmiddle hml hmc hfaxis
      hX0 hmkX hxNotBase hxmiddle
      (by simpa only [v2] using A.intersection_incident_left hlmiddle)
      (by simpa only [v2] using A.intersection_incident_right hlmiddle)
      (by simpa only [v2] using hV2m)
      hXbase hXgauge hV2base hV2gauge hV2evalM
  let coord := A.fixedChartArrangementCoordinateEquiv sigma fixedGauge
    l axis X hlaxis hfaxis hXbase
  let middleEval := scale⁻¹ • A.arrangementOrientedEvaluation sigma m
  have hmiddle : ∀ Z, middleEval Z =
      coord Z ⬝ᵥ triangleExitMiddleCovector
        (A.arrangementOrientedEvaluation sigma axis V2) delta := by
    intro Z
    simp only [middleEval, LinearMap.smul_apply, smul_eq_mul,
      hform Z, coord]
    rw [← mul_assoc, inv_mul_cancel₀ hscale, one_mul]
  let hkernel : ∀ Z,
      A.arrangementOrientedEvaluation sigma l Z = 0 →
      A.arrangementOrientedEvaluation sigma axis Z = 0 →
      fixedGauge Z = 0 → Z = 0 :=
    fun Z hl ha hf =>
      A.eq_zero_of_two_orientedEvaluations_and_fixedGauge
        sigma fixedGauge hlaxis hfaxis Z hl ha hf
  have hmiddle' : ∀ Z, middleEval Z =
      fixedChartExitCoordinateEquiv
          (A.arrangementOrientedEvaluation sigma l)
          (A.arrangementOrientedEvaluation sigma axis)
          fixedGauge X hkernel hXbase Z ⬝ᵥ
        triangleExitMiddleCovector
          (A.arrangementOrientedEvaluation sigma axis V2) delta := by
    simpa only [coord, hkernel, fixedChartArrangementCoordinateEquiv]
      using hmiddle
  have hleftV : A.arrangementOrientedEvaluation sigma left V1 = 0 := by
    apply A.arrangementOrientedEvaluation_vertexChartNormalizedVector_eq_zero
      sigma fixedGauge hfv1
    simpa only [v1] using A.intersection_incident_right hlleft
  have hleftX : A.arrangementOrientedEvaluation sigma left X = 0 := by
    simpa only [X] using
      A.arrangementOrientedEvaluation_vertexChartNormalizedVector_eq_zero
        sigma fixedGauge hfx hxleft
  have hrightV : A.arrangementOrientedEvaluation sigma right V3 = 0 := by
    apply A.arrangementOrientedEvaluation_vertexChartNormalizedVector_eq_zero
      sigma fixedGauge hfv3
    simpa only [v3] using A.intersection_incident_right hlright
  have hrightX : A.arrangementOrientedEvaluation sigma right X = 0 := by
    simpa only [X] using
      A.arrangementOrientedEvaluation_vertexChartNormalizedVector_eq_zero
        sigma fixedGauge hfx hxright
  have ht12 : A.arrangementOrientedEvaluation sigma axis V1 <
      A.arrangementOrientedEvaluation sigma axis V2 := by
    simpa only [fixedChartBaseParameter, V1, V2, v1, v2] using h12
  have ht23 : A.arrangementOrientedEvaluation sigma axis V2 <
      A.arrangementOrientedEvaluation sigma axis V3 := by
    simpa only [fixedChartBaseParameter, V2, V3, v2, v3] using h23
  rcases fixedChart_transportedBarycentric_with_axis
      (A.arrangementOrientedEvaluation sigma l)
      (A.arrangementOrientedEvaluation sigma axis)
      (A.arrangementOrientedEvaluation sigma left)
      (A.arrangementOrientedEvaluation sigma right)
      fixedGauge middleEval hkernel hXbase hXgauge
      hV1base hV1gauge hV3base hV3gauge
      (A.arrangementOrientedEvaluation sigma axis V2) delta
      ht12 ht23 hdelta hmiddle'
      hleftV hleftX hrightV hrightX with hleftBranch | hrightBranch
  · left
    rcases hleftBranch with ⟨h, hh0, hh1, hrest⟩
    dsimp only at hrest
    rcases hrest with ⟨hY0, hYm', hYleft⟩
    have hYm : A.arrangementOrientedEvaluation sigma m
        ((1 - h) • V1 + h • X) = 0 := by
      simp only [middleEval, LinearMap.smul_apply, smul_eq_mul] at hYm'
      exact (mul_eq_zero.mp hYm').resolve_left (inv_ne_zero hscale)
    refine ⟨h, (1 - h) • V1 + h • X,
      hh0, hh1, ?_, hY0, hYm, hYleft⟩
    simp only [V1, X, v1]
  · right
    rcases hrightBranch with ⟨h, hh0, hh1, hrest⟩
    dsimp only at hrest
    rcases hrest with ⟨hY0, hYm', hYright⟩
    have hYm : A.arrangementOrientedEvaluation sigma m
        ((1 - h) • V3 + h • X) = 0 := by
      simp only [middleEval, LinearMap.smul_apply, smul_eq_mul] at hYm'
      exact (mul_eq_zero.mp hYm').resolve_left (inv_ne_zero hscale)
    refine ⟨h, (1 - h) • V3 + h • X,
      hh0, hh1, ?_, hY0, hYm, hYright⟩
    simp only [V3, X, v3]

/-- Actual smaller vertex produced by the axis-separated ordered exit. -/
theorem fixedChartExit_axis_ordered
    (A : FiniteProjectiveLineArrangement Line) (sigma : Line → Bool)
    (fixedGauge : (Fin 3 → ℝ) →ₗ[ℝ] ℝ)
    (l axis left right middle m : Line) (x : RealProjectivePoint)
    (hgauge : ∀ q : RealProjectivePoint, q ∈ A.vertexSet →
      fixedGauge q.rep ≠ 0)
    (hxVertex : x ∈ A.vertexSet)
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
      exact (lt_irrefl _ h12)
    · intro hm
      subst m
      have heq : A.intersection l middle = A.intersection l right :=
        A.eq_intersection_of_incident hlright
          (A.intersection_incident_left hlmiddle) hV2m
      rw [heq] at h23
      exact (lt_irrefl _ h23)
  rcases A.fixedChartExit_barycentric_axis_ordered sigma fixedGauge
      l axis left right middle m x hgauge hxVertex
      hlaxis hlleft hlright hlmiddle hml hmc hxNotBase
      hxleft hxright hxmiddle hV2m h12 h23 with hleft | hright
  · rcases hleft with ⟨h, Y, hh0, hh1, hY, hY0, hYm, hYleft⟩
    have hfV := hgauge (A.intersection l left)
      (A.intersection_mem_vertexSet hlleft)
    have hVbase :=
      A.arrangementOrientedEvaluation_vertexChartNormalizedVector_eq_zero
        sigma fixedGauge hfV (A.intersection_incident_left hlleft)
    have hVgauge := vertexChartNormalizedVector_fixedGauge_eq_one
      fixedGauge (A.intersection l left) hfV
    have hfx := hgauge x hxVertex
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
    have hfV := hgauge (A.intersection l right)
      (A.intersection_mem_vertexSet hlright)
    have hVbase :=
      A.arrangementOrientedEvaluation_vertexChartNormalizedVector_eq_zero
        sigma fixedGauge hfV (A.intersection_incident_left hlright)
    have hVgauge := vertexChartNormalizedVector_fixedGauge_eq_one
      fixedGauge (A.intersection l right) hfV
    have hfx := hgauge x hxVertex
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

/-- A fixed-chart base parameter is injective on actual intersections with
the base. -/
theorem fixedChartBaseParameter_intersection_injective
    (A : FiniteProjectiveLineArrangement Line) (sigma : Line → Bool)
    (fixedGauge : (Fin 3 → ℝ) →ₗ[ℝ] ℝ)
    (hgauge : ∀ q : RealProjectivePoint, q ∈ A.vertexSet →
      fixedGauge q.rep ≠ 0)
    {l axis c d : Line} (hlaxis : l ≠ axis)
    (hlc : l ≠ c) (hld : l ≠ d)
    (heq : A.fixedChartBaseParameter sigma fixedGauge axis
        (A.intersection l c) =
      A.fixedChartBaseParameter sigma fixedGauge axis
        (A.intersection l d)) :
    A.intersection l c = A.intersection l d := by
  let q := A.intersection l c
  let r := A.intersection l d
  have hqVertex : q ∈ A.vertexSet := by
    simpa only [q] using A.intersection_mem_vertexSet hlc
  have hrVertex : r ∈ A.vertexSet := by
    simpa only [r] using A.intersection_mem_vertexSet hld
  have hfq := hgauge q hqVertex
  have hfr := hgauge r hrVertex
  have hfaxis := hgauge (A.intersection l axis)
    (A.intersection_mem_vertexSet hlaxis)
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
    A.intersection l c =
        Projectivization.mk ℝ Q
          (vertexChartNormalizedVector_ne_zero fixedGauge q hfq) := by
      simpa only [q, Q] using
        (projectivization_mk_vertexChartNormalizedVector
          fixedGauge q hfq).symm
    _ = Projectivization.mk ℝ R
          (vertexChartNormalizedVector_ne_zero fixedGauge r hfr) := by
      apply (Projectivization.mk_eq_mk_iff' ℝ _ _ _ _).2
      exact ⟨1, by simpa only [one_smul] using hQR.symm⟩
    _ = A.intersection l d := by
      simpa only [r, R] using
        projectivization_mk_vertexChartNormalizedVector fixedGauge r hfr

/-- Three distinct supports through a point off the base can be relabelled
so that their returns are strictly ordered in any fixed affine coordinate
on the base.  The coordinate axis itself is kept fixed during relabelling. -/
theorem exists_fixedChart_ordered_three_incident_supports
    (A : FiniteProjectiveLineArrangement Line) (sigma : Line → Bool)
    (fixedGauge : (Fin 3 → ℝ) →ₗ[ℝ] ℝ)
    (hgauge : ∀ q : RealProjectivePoint, q ∈ A.vertexSet →
      fixedGauge q.rep ≠ 0)
    (x : RealProjectivePoint) (l a b c : Line)
    (hxl : ¬ A.Incident x l)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hxa : A.Incident x a) (hxb : A.Incident x b)
    (hxc : A.Incident x c) :
    ∃ left middle right : Line,
      l ≠ left ∧ l ≠ middle ∧ l ≠ right ∧
      A.Incident x left ∧ A.Incident x middle ∧ A.Incident x right ∧
      A.fixedChartBaseParameter sigma fixedGauge a
          (A.intersection l left) <
        A.fixedChartBaseParameter sigma fixedGauge a
          (A.intersection l middle) ∧
      A.fixedChartBaseParameter sigma fixedGauge a
          (A.intersection l middle) <
        A.fixedChartBaseParameter sigma fixedGauge a
          (A.intersection l right) := by
  have hla : l ≠ a := by
    intro h
    apply hxl
    rw [h]
    exact hxa
  have hlb : l ≠ b := by
    intro h
    apply hxl
    rw [h]
    exact hxb
  have hlc : l ≠ c := by
    intro h
    apply hxl
    rw [h]
    exact hxc
  have hpab := A.intersection_base_ne_of_distinct_supports
    x l a b hxl hxa hxb hab
  have hpac := A.intersection_base_ne_of_distinct_supports
    x l a c hxl hxa hxc hac
  have hpbc := A.intersection_base_ne_of_distinct_supports
    x l b c hxl hxb hxc hbc
  have htab :
      A.fixedChartBaseParameter sigma fixedGauge a (A.intersection l a) ≠
        A.fixedChartBaseParameter sigma fixedGauge a (A.intersection l b) := by
    intro heq
    exact hpab (A.fixedChartBaseParameter_intersection_injective
      sigma fixedGauge hgauge hla hla hlb heq)
  have htac :
      A.fixedChartBaseParameter sigma fixedGauge a (A.intersection l a) ≠
        A.fixedChartBaseParameter sigma fixedGauge a (A.intersection l c) := by
    intro heq
    exact hpac (A.fixedChartBaseParameter_intersection_injective
      sigma fixedGauge hgauge hla hla hlc heq)
  have htbc :
      A.fixedChartBaseParameter sigma fixedGauge a (A.intersection l b) ≠
        A.fixedChartBaseParameter sigma fixedGauge a (A.intersection l c) := by
    intro heq
    exact hpbc (A.fixedChartBaseParameter_intersection_injective
      sigma fixedGauge hgauge hla hlb hlc heq)
  rcases lt_or_gt_of_ne htab with hab' | hba'
  · rcases lt_or_gt_of_ne htbc with hbc' | hcb'
    · exact ⟨a, b, c, hla, hlb, hlc, hxa, hxb, hxc, hab', hbc'⟩
    · rcases lt_or_gt_of_ne htac with hac' | hca'
      · exact ⟨a, c, b, hla, hlc, hlb, hxa, hxc, hxb, hac', hcb'⟩
      · exact ⟨c, a, b, hlc, hla, hlb, hxc, hxa, hxb, hca', hab'⟩
  · rcases lt_or_gt_of_ne htac with hac' | hca'
    · exact ⟨b, a, c, hlb, hla, hlc, hxb, hxa, hxc, hba', hac'⟩
    · rcases lt_or_gt_of_ne htbc with hbc' | hcb'
      · exact ⟨b, c, a, hlb, hlc, hla, hxb, hxc, hxa, hbc', hca'⟩
      · exact ⟨c, b, a, hlc, hlb, hla, hxc, hxb, hxa, hcb', hba'⟩

/-- On a zero-ordinary base, a globally closest off-base vertex in a fixed
vertex chart is ordinary.  This is the minimizer step of Felsner's argument;
the three-support case is contradicted by the ordered planar exit. -/
theorem multiplicity_eq_two_of_minimal_fixedChartLineHeight_of_degree_zero
    (A : FiniteProjectiveLineArrangement Line) (sigma : Line → Bool)
    (fixedGauge : (Fin 3 → ℝ) →ₗ[ℝ] ℝ)
    (l : Line) (x : RealProjectivePoint)
    (hgauge : ∀ q : RealProjectivePoint, q ∈ A.vertexSet →
      fixedGauge q.rep ≠ 0)
    (hzero : A.lineOrdinaryVertexDegree l = 0)
    (hxVertex : x ∈ A.vertexSet) (hxl : ¬ A.Incident x l)
    (hmin : ∀ y : RealProjectivePoint, y ∈ A.vertexSet →
      ¬ A.Incident y l →
      A.vertexChartLineHeight fixedGauge l x ≤
        A.vertexChartLineHeight fixedGauge l y) :
    A.multiplicity x = 2 := by
  obtain ⟨u, v, huv, huvx⟩ := A.exists_lines_of_mem_vertexSet hxVertex
  have htwo : 2 ≤ A.multiplicity x := by
    rw [← huvx]
    exact A.two_le_multiplicity_intersection huv
  by_contra hne
  have hthree : 3 ≤ A.multiplicity x := by omega
  obtain ⟨a, b, c, hab, hac, hbc, hxa, hxb, hxc⟩ :=
    A.exists_three_incident_lines_of_three_le_multiplicity x hthree
  have hla : l ≠ a := by
    intro h
    apply hxl
    rw [h]
    exact hxa
  obtain ⟨left, middle, right, hlleft, hlmiddle, hlright,
      hxleft, hxmiddle, hxright, h12, h23⟩ :=
    A.exists_fixedChart_ordered_three_incident_supports
      sigma fixedGauge hgauge x l a b c hxl hab hac hbc hxa hxb hxc
  obtain ⟨m, hml, hmc, hV2m⟩ :=
    A.exists_extra_line_at_base_return_of_lineDegree_eq_zero
      l middle hzero hlmiddle
  obtain ⟨y, h, hh0, hh1, hyVertex, hym, hyl, hyHeight, hylt, hbranch⟩ :=
    A.fixedChartExit_axis_ordered sigma fixedGauge
      l a left right middle m x hgauge hxVertex
      hla hlleft hlright hlmiddle hml hmc hxl
      hxleft hxright hxmiddle hV2m h12 h23
  exact (not_lt_of_ge (hmin y hyVertex hyl)) hylt

/-- The global closest-point construction on a zero-ordinary base therefore
returns a bundled ordinary vertex. -/
theorem exists_closest_offLineOrdinaryVertex_of_degree_zero
    (A : FiniteProjectiveLineArrangement Line) (hA : A.NonPencil)
    (sigma : Line → Bool) (l : Line)
    (hzero : A.lineOrdinaryVertexDegree l = 0) :
    ∃ fixedGauge : (Fin 3 → ℝ) →ₗ[ℝ] ℝ,
      (∀ r : RealProjectivePoint, r ∈ A.vertexSet →
        fixedGauge r.rep ≠ 0) ∧
      ∃ q : A.OrdinaryVertex,
        ¬ A.Incident q.1 l ∧
        0 < A.vertexChartLineHeight fixedGauge l q.1 ∧
        ∀ r : RealProjectivePoint, r ∈ A.vertexSet →
          ¬ A.Incident r l →
          A.vertexChartLineHeight fixedGauge l q.1 ≤
            A.vertexChartLineHeight fixedGauge l r := by
  classical
  obtain ⟨fixedGauge, hgauge, x, hxVertex, hxl, hxpos, hmin⟩ :=
    A.exists_closest_offLineVertex hA l
  have hx2 :=
    A.multiplicity_eq_two_of_minimal_fixedChartLineHeight_of_degree_zero
      sigma fixedGauge l x hgauge hzero hxVertex hxl hmin
  let q : A.OrdinaryVertex :=
    ⟨x, Finset.mem_filter.mpr ⟨hxVertex, hx2⟩⟩
  exact ⟨fixedGauge, hgauge, q, hxl, hxpos, hmin⟩

/-- The global closest ordinary vertex can be placed in the orientation of
the fixed chart where its normalized base evaluation is positive. -/
theorem exists_closest_offLineOrdinaryVertex_base_pos_of_degree_zero
    (A : FiniteProjectiveLineArrangement Line) (hA : A.NonPencil)
    (l : Line) (hzero : A.lineOrdinaryVertexDegree l = 0) :
    ∃ fixedGauge : (Fin 3 → ℝ) →ₗ[ℝ] ℝ,
      (∀ r : RealProjectivePoint, r ∈ A.vertexSet →
        fixedGauge r.rep ≠ 0) ∧
      ∃ q : A.OrdinaryVertex,
        ¬ A.Incident q.1 l ∧
        0 < projectiveLineEvaluation (A.projectiveLine l)
          (vertexChartNormalizedVector fixedGauge q.1) ∧
        ∀ r : RealProjectivePoint, r ∈ A.vertexSet →
          ¬ A.Incident r l →
          A.vertexChartLineHeight fixedGauge l q.1 ≤
            A.vertexChartLineHeight fixedGauge l r := by
  classical
  obtain ⟨f, hf, q, hql, _hqpos, hmin⟩ :=
    A.exists_closest_offLineOrdinaryVertex_of_degree_zero
      hA (fun _ => true) l hzero
  let x := projectiveLineEvaluation (A.projectiveLine l)
    (vertexChartNormalizedVector f q.1)
  have hfq : f q.1.rep ≠ 0 :=
    hf q.1 (Finset.mem_filter.mp q.2).1
  have hx0 : x ≠ 0 := by
    simpa only [x, arrangementOrientedEvaluation, if_true] using
      A.arrangementOrientedEvaluation_vertexChartNormalizedVector_ne_zero
        (fun _ => true) f hfq hql
  by_cases hxpos : 0 < x
  · exact ⟨f, hf, q, hql, hxpos, hmin⟩
  · have hxneg : x < 0 :=
      lt_of_le_of_ne (le_of_not_gt hxpos) hx0
    refine ⟨-f, ?_, q, hql, ?_, ?_⟩
    · intro r hr hzero
      apply hf r hr
      simpa using congrArg Neg.neg hzero
    · simpa only [vertexChartNormalizedVector_neg_fixedGauge,
        LinearMap.map_neg, x] using neg_pos.mpr hxneg
    · intro r hrVertex hrl
      simpa only [vertexChartLineHeight_neg_fixedGauge] using
        hmin r hrVertex hrl

end FiniteProjectiveLineArrangement

end Erdos506.Incidence
