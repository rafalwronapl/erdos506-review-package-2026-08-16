import Erdos506.Incidence.RealProjectiveArrangementKellyMoserSectorExit

/-!
# Fixed-chart barycentric exit for Kelly--Moser

This leaf repeats only the coordinate normalization of the sector exit with
the single affine covector used by the global closest-vertex minimizer.
-/

namespace Erdos506.Incidence

open Erdos506.V4
open Matrix
open scoped LinearAlgebra.Projectivization

namespace FiniteProjectiveLineArrangement

variable {Line : Type*} [Fintype Line] [DecidableEq Line]

/-- A strict barycentric move away from the base lowers the base/gauge
ratio whenever both endpoint gauges have the same positive sign. -/
theorem barycentric_fixedGauge_baseRatio_lt
    (base fixedGauge : Homogeneous3 →ₗ[ℝ] ℝ)
    {V X Y : Homogeneous3} {h : ℝ}
    (hh0 : 0 < h) (hh1 : h < 1)
    (hY : Y = (1 - h) • V + h • X)
    (hbaseV : base V = 0)
    (hgaugeV : 0 < fixedGauge V) (hgaugeX : 0 < fixedGauge X)
    (hbaseX : 0 < base X) :
    base Y / fixedGauge Y < base X / fixedGauge X := by
  have hgaugeY : 0 < fixedGauge Y := by
    rw [hY, LinearMap.map_add, LinearMap.map_smul, LinearMap.map_smul]
    simp only [smul_eq_mul]
    exact add_pos
      (mul_pos (sub_pos.mpr hh1) hgaugeV)
      (mul_pos hh0 hgaugeX)
  rw [div_lt_div_iff₀ hgaugeY hgaugeX]
  rw [hY, LinearMap.map_add, LinearMap.map_smul, LinearMap.map_smul,
    hbaseV]
  simp only [smul_eq_mul, mul_zero, add_zero]
  have hstrict : 0 < base X * (1 - h) * fixedGauge V :=
    mul_pos (mul_pos hbaseX (sub_pos.mpr hh1)) hgaugeV
  rw [LinearMap.map_add, LinearMap.map_smul, LinearMap.map_smul]
  simp only [smul_eq_mul]
  nlinarith

/-- Fixed-chart normalization really lies in the affine hyperplane
`f = 1`. -/
@[simp]
theorem vertexChartNormalizedVector_fixedGauge_eq_one
    (f : Homogeneous3 →ₗ[ℝ] ℝ) (q : RealProjectivePoint)
    (hf : f q.rep ≠ 0) :
    f (vertexChartNormalizedVector f q) = 1 := by
  simp only [vertexChartNormalizedVector, LinearMap.map_smul, smul_eq_mul]
  exact inv_mul_cancel₀ hf

/-- A gauge-one representative of `q` is exactly the fixed-chart
normalized representative, independently of the canonical sign of
`q.rep`. -/
theorem vertexChartNormalizedVector_eq_of_projectivization_mk
    (fixedGauge : Homogeneous3 →ₗ[ℝ] ℝ)
    (q : RealProjectivePoint) {Y : Homogeneous3} (hY0 : Y ≠ 0)
    (hgaugeY : fixedGauge Y = 1)
    (hmkY : Projectivization.mk ℝ Y hY0 = q) :
    vertexChartNormalizedVector fixedGauge q = Y := by
  have hproj : Projectivization.mk ℝ Y hY0 =
      Projectivization.mk ℝ q.rep q.rep_nonzero :=
    hmkY.trans q.mk_rep.symm
  obtain ⟨c, hc⟩ := (Projectivization.mk_eq_mk_iff' ℝ
    Y q.rep hY0 q.rep_nonzero).1 hproj
  have hcgauge : c * fixedGauge q.rep = 1 := by
    have hmap := congrArg (fun W : Homogeneous3 => fixedGauge W) hc
    simpa only [LinearMap.map_smul, smul_eq_mul, hgaugeY] using hmap
  have hfrep : fixedGauge q.rep ≠ 0 := by
    intro hf0
    rw [hf0, mul_zero] at hcgauge
    exact zero_ne_one hcgauge
  have hcEq : c = (fixedGauge q.rep)⁻¹ := by
    calc
      c = c * (fixedGauge q.rep * (fixedGauge q.rep)⁻¹) := by
        rw [mul_inv_cancel₀ hfrep, mul_one]
      _ = (c * fixedGauge q.rep) * (fixedGauge q.rep)⁻¹ := by ring
      _ = (fixedGauge q.rep)⁻¹ := by rw [hcgauge, one_mul]
  unfold vertexChartNormalizedVector
  rw [← hcEq, hc]

/-- Every line through a projective point vanishes on its fixed-chart
normalized representative. -/
theorem arrangementOrientedEvaluation_vertexChartNormalizedVector_eq_zero
    (A : FiniteProjectiveLineArrangement Line) (sigma : Line → Bool)
    (f : Homogeneous3 →ₗ[ℝ] ℝ)
    {q : RealProjectivePoint} {l : Line}
    (hf : f q.rep ≠ 0) (hql : A.Incident q l) :
    A.arrangementOrientedEvaluation sigma l
        (vertexChartNormalizedVector f q) = 0 := by
  let V := vertexChartNormalizedVector f q
  have hV0 : V ≠ 0 := vertexChartNormalizedVector_ne_zero f q hf
  apply (A.incident_projectivization_mk_iff_orientedEvaluation_eq_zero
    sigma l V hV0).1
  simpa only [V, projectivization_mk_vertexChartNormalizedVector f q hf]
    using hql

/-- A nonincident line stays nonzero on a fixed-chart normalized
representative. -/
theorem arrangementOrientedEvaluation_vertexChartNormalizedVector_ne_zero
    (A : FiniteProjectiveLineArrangement Line) (sigma : Line → Bool)
    (f : Homogeneous3 →ₗ[ℝ] ℝ)
    {q : RealProjectivePoint} {l : Line}
    (hf : f q.rep ≠ 0) (hql : ¬ A.Incident q l) :
    A.arrangementOrientedEvaluation sigma l
        (vertexChartNormalizedVector f q) ≠ 0 := by
  let V := vertexChartNormalizedVector f q
  have hV0 : V ≠ 0 := vertexChartNormalizedVector_ne_zero f q hf
  intro hzero
  apply hql
  have hinc :=
    (A.incident_projectivization_mk_iff_orientedEvaluation_eq_zero
      sigma l V hV0).2 (by simpa only [V] using hzero)
  simpa only [V, projectivization_mk_vertexChartNormalizedVector f q hf]
    using hinc

/-- Coordinates adapted to a base line, one outer support, and the fixed
affine chart.  Unlike `sectorExitCoordinateMap`, the third coordinate is
the globally chosen chart covector. -/
noncomputable def fixedChartExitCoordinateMap
    (base side fixedGauge : Homogeneous3 →ₗ[ℝ] ℝ)
    (X : Homogeneous3) : Homogeneous3 →ₗ[ℝ] Homogeneous3 :=
  LinearMap.pi ![
    side - ((side X) / (base X)) • base,
    ((base X)⁻¹) • base,
    fixedGauge]

@[simp]
theorem fixedChartExitCoordinateMap_apply_zero
    (base side fixedGauge : Homogeneous3 →ₗ[ℝ] ℝ)
    (X Z : Homogeneous3) :
    fixedChartExitCoordinateMap base side fixedGauge X Z 0 =
      side Z - (side X / base X) * base Z := by
  simp [fixedChartExitCoordinateMap, smul_eq_mul]

@[simp]
theorem fixedChartExitCoordinateMap_apply_one
    (base side fixedGauge : Homogeneous3 →ₗ[ℝ] ℝ)
    (X Z : Homogeneous3) :
    fixedChartExitCoordinateMap base side fixedGauge X Z 1 =
      (base X)⁻¹ * base Z := by
  simp [fixedChartExitCoordinateMap, smul_eq_mul]

@[simp]
theorem fixedChartExitCoordinateMap_apply_two
    (base side fixedGauge : Homogeneous3 →ₗ[ℝ] ℝ)
    (X Z : Homogeneous3) :
    fixedChartExitCoordinateMap base side fixedGauge X Z 2 = fixedGauge Z := by
  simp [fixedChartExitCoordinateMap]

/-- A fixed-gauge normalized apex has coordinates `(0,1,1)`. -/
theorem fixedChartExitCoordinateMap_apex
    (base side fixedGauge : Homogeneous3 →ₗ[ℝ] ℝ)
    {X : Homogeneous3} (hbase : base X ≠ 0)
    (hgauge : fixedGauge X = 1) :
    fixedChartExitCoordinateMap base side fixedGauge X X =
      homogeneousLift (triangleExitTopPoint 0) := by
  ext i
  fin_cases i
  · simp [triangleExitTopPoint, homogeneousLift, hbase]
  · simp [triangleExitTopPoint, homogeneousLift, hbase]
  · simp [triangleExitTopPoint, homogeneousLift, hgauge]

/-- A fixed-gauge normalized point on the base has coordinates `(t,0,1)`. -/
theorem fixedChartExitCoordinateMap_base
    (base side fixedGauge : Homogeneous3 →ₗ[ℝ] ℝ)
    (X : Homogeneous3) {V : Homogeneous3}
    (hbase : base V = 0) (hgauge : fixedGauge V = 1) :
    fixedChartExitCoordinateMap base side fixedGauge X V =
      homogeneousLift (triangleExitBasePoint (side V)) := by
  ext i
  fin_cases i
  · simp [triangleExitBasePoint, homogeneousLift, hbase]
  · simp [triangleExitBasePoint, homogeneousLift, hbase]
  · simp [triangleExitBasePoint, homogeneousLift, hgauge]

/-- The adapted fixed-chart coordinates are injective as soon as the three
coordinate covectors have trivial common kernel. -/
theorem fixedChartExitCoordinateMap_injective
    (base side fixedGauge : Homogeneous3 →ₗ[ℝ] ℝ)
    (X : Homogeneous3)
    (hkernel : ∀ Z, base Z = 0 → side Z = 0 →
      fixedGauge Z = 0 → Z = 0)
    (hbaseX : base X ≠ 0) :
    Function.Injective (fixedChartExitCoordinateMap base side fixedGauge X) := by
  intro v w hvw
  apply sub_eq_zero.mp
  apply hkernel (v - w)
  · have hcoord := congrFun hvw (1 : Fin 3)
    simp only [fixedChartExitCoordinateMap_apply_one] at hcoord
    rw [LinearMap.map_sub]
    exact sub_eq_zero.mpr
      (mul_left_cancel₀ (inv_ne_zero hbaseX) hcoord)
  · have hcoord0 := congrFun hvw (0 : Fin 3)
    have hcoord1 := congrFun hvw (1 : Fin 3)
    simp only [fixedChartExitCoordinateMap_apply_zero] at hcoord0
    simp only [fixedChartExitCoordinateMap_apply_one] at hcoord1
    have hbase : base v = base w :=
      mul_left_cancel₀ (inv_ne_zero hbaseX) hcoord1
    rw [hbase] at hcoord0
    rw [LinearMap.map_sub]
    exact sub_eq_zero.mpr (by linarith)
  · have hcoord := congrFun hvw (2 : Fin 3)
    simp only [fixedChartExitCoordinateMap_apply_two] at hcoord
    rw [LinearMap.map_sub]
    exact sub_eq_zero.mpr hcoord

/-- The linear equivalence used for a fixed-chart exit. -/
noncomputable def fixedChartExitCoordinateEquiv
    (base side fixedGauge : Homogeneous3 →ₗ[ℝ] ℝ)
    (X : Homogeneous3)
    (hkernel : ∀ Z, base Z = 0 → side Z = 0 →
      fixedGauge Z = 0 → Z = 0)
    (hbaseX : base X ≠ 0) : Homogeneous3 ≃ₗ[ℝ] Homogeneous3 :=
  LinearEquiv.ofInjectiveEndo
    (fixedChartExitCoordinateMap base side fixedGauge X)
    (fixedChartExitCoordinateMap_injective
      base side fixedGauge X hkernel hbaseX)

@[simp]
theorem fixedChartExitCoordinateEquiv_apply
    (base side fixedGauge : Homogeneous3 →ₗ[ℝ] ℝ)
    (X Z : Homogeneous3)
    (hkernel : ∀ W, base W = 0 → side W = 0 →
      fixedGauge W = 0 → W = 0)
    (hbaseX : base X ≠ 0) :
    fixedChartExitCoordinateEquiv base side fixedGauge X
        hkernel hbaseX Z =
      fixedChartExitCoordinateMap base side fixedGauge X Z :=
  rfl

/-- Two distinct arrangement supports together with a chart covector that
does not vanish at their intersection form a projective coordinate frame. -/
theorem eq_zero_of_two_orientedEvaluations_and_fixedGauge
    (A : FiniteProjectiveLineArrangement Line) (sigma : Line → Bool)
    (fixedGauge : Homogeneous3 →ₗ[ℝ] ℝ)
    {l a : Line} (hla : l ≠ a)
    (hgauge : fixedGauge (A.intersection l a).rep ≠ 0)
    (Z : Homogeneous3)
    (hl : A.arrangementOrientedEvaluation sigma l Z = 0)
    (ha : A.arrangementOrientedEvaluation sigma a Z = 0)
    (hf : fixedGauge Z = 0) : Z = 0 := by
  by_contra hZ
  let q := Projectivization.mk ℝ Z hZ
  have hql : A.Incident q l :=
    (A.incident_projectivization_mk_iff_orientedEvaluation_eq_zero
      sigma l Z hZ).2 hl
  have hqa : A.Incident q a :=
    (A.incident_projectivization_mk_iff_orientedEvaluation_eq_zero
      sigma a Z hZ).2 ha
  have hq : q = A.intersection l a :=
    A.eq_intersection_of_incident hla hql hqa
  have hproj : Projectivization.mk ℝ Z hZ =
      Projectivization.mk ℝ (A.intersection l a).rep
        (A.intersection l a).rep_nonzero := by
    exact hq.trans (A.intersection l a).mk_rep.symm
  obtain ⟨c, hc⟩ := (Projectivization.mk_eq_mk_iff' ℝ
    Z (A.intersection l a).rep hZ
      (A.intersection l a).rep_nonzero).1 hproj
  have hc0 : c = 0 := by
    have hmap := congrArg (fun W : Homogeneous3 => fixedGauge W) hc
    simp only [LinearMap.map_smul, smul_eq_mul, hf] at hmap
    exact (mul_eq_zero.mp hmap).resolve_right hgauge
  apply hZ
  rw [← hc, hc0, zero_smul]

/-- Affine coordinate of a point along a chosen base, measured by an outer
support covector after fixed-chart normalization. -/
noncomputable def fixedChartBaseParameter
    (A : FiniteProjectiveLineArrangement Line) (sigma : Line → Bool)
    (fixedGauge : Homogeneous3 →ₗ[ℝ] ℝ)
    (a : Line) (q : RealProjectivePoint) : ℝ :=
  A.arrangementOrientedEvaluation sigma a
    (vertexChartNormalizedVector fixedGauge q)

/-- Arrangement specialization of the fixed-chart coordinate frame. -/
noncomputable def fixedChartArrangementCoordinateEquiv
    (A : FiniteProjectiveLineArrangement Line) (sigma : Line → Bool)
    (fixedGauge : Homogeneous3 →ₗ[ℝ] ℝ)
    (l a : Line) (X : Homogeneous3)
    (hla : l ≠ a)
    (hgauge : fixedGauge (A.intersection l a).rep ≠ 0)
    (hbaseX : A.arrangementOrientedEvaluation sigma l X ≠ 0) :
    Homogeneous3 ≃ₗ[ℝ] Homogeneous3 :=
  fixedChartExitCoordinateEquiv
    (A.arrangementOrientedEvaluation sigma l)
    (A.arrangementOrientedEvaluation sigma a)
    fixedGauge X
    (fun Z hl ha hf =>
      A.eq_zero_of_two_orientedEvaluations_and_fixedGauge
        sigma fixedGauge hla hgauge Z hl ha hf)
    hbaseX

@[simp]
theorem fixedChartArrangementCoordinateEquiv_apply
    (A : FiniteProjectiveLineArrangement Line) (sigma : Line → Bool)
    (fixedGauge : Homogeneous3 →ₗ[ℝ] ℝ)
    (l a : Line) (X Z : Homogeneous3)
    (hla : l ≠ a)
    (hgauge : fixedGauge (A.intersection l a).rep ≠ 0)
    (hbaseX : A.arrangementOrientedEvaluation sigma l X ≠ 0) :
    A.fixedChartArrangementCoordinateEquiv sigma fixedGauge l a X
        hla hgauge hbaseX Z =
      fixedChartExitCoordinateMap
        (A.arrangementOrientedEvaluation sigma l)
        (A.arrangementOrientedEvaluation sigma a)
        fixedGauge X Z :=
  rfl

/-- Strict order of the three fixed-chart base parameters makes the
transverse support different from either outer support. -/
theorem fixedChartExit_transverse_ne_outer
    (A : FiniteProjectiveLineArrangement Line) (sigma : Line → Bool)
    (fixedGauge : Homogeneous3 →ₗ[ℝ] ℝ)
    {l a b c m : Line}
    (hla : l ≠ a) (hlb : l ≠ b) (hlc : l ≠ c)
    (hV2m : A.Incident (A.intersection l c) m)
    (h12 : A.fixedChartBaseParameter sigma fixedGauge a
        (A.intersection l a) <
      A.fixedChartBaseParameter sigma fixedGauge a
        (A.intersection l c))
    (h23 : A.fixedChartBaseParameter sigma fixedGauge a
        (A.intersection l c) <
      A.fixedChartBaseParameter sigma fixedGauge a
        (A.intersection l b)) :
    m ≠ a ∧ m ≠ b := by
  constructor
  · intro hma
    subst m
    have heq : A.intersection l c = A.intersection l a :=
      A.eq_intersection_of_incident hla
        (A.intersection_incident_left hlc) hV2m
    rw [heq] at h12
    exact (lt_irrefl _ h12)
  · intro hmb
    subst m
    have heq : A.intersection l c = A.intersection l b :=
      A.eq_intersection_of_incident hlb
        (A.intersection_incident_left hlc) hV2m
    rw [heq] at h23
    exact (lt_irrefl _ h23)

/-- The canonical triangle-exit computation transported through a fixed
affine gauge. -/
theorem fixedChart_transportedBarycentric
    (base left right fixedGauge middle : Homogeneous3 →ₗ[ℝ] ℝ)
    {X V1 V3 : Homogeneous3}
    (hkernel : ∀ Z, base Z = 0 → left Z = 0 →
      fixedGauge Z = 0 → Z = 0)
    (hbaseX : base X ≠ 0)
    (hgaugeX : fixedGauge X = 1)
    (hbaseV1 : base V1 = 0) (hgaugeV1 : fixedGauge V1 = 1)
    (hbaseV3 : base V3 = 0) (hgaugeV3 : fixedGauge V3 = 1)
    (t2 delta : ℝ) (h12 : left V1 < t2) (h23 : t2 < left V3)
    (hdelta : delta ≠ 0)
    (hform : ∀ Z, middle Z =
      fixedChartExitCoordinateEquiv base left fixedGauge X
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
    base left fixedGauge X hkernel hbaseX
  have hcoordX : coord X = homogeneousLift (triangleExitTopPoint 0) := by
    simpa only [coord, fixedChartExitCoordinateEquiv_apply] using
      fixedChartExitCoordinateMap_apex base left fixedGauge
        hbaseX hgaugeX
  have hcoordV1 : coord V1 =
      homogeneousLift (triangleExitBasePoint (left V1)) := by
    simpa only [coord, fixedChartExitCoordinateEquiv_apply] using
      fixedChartExitCoordinateMap_base base left fixedGauge X
        hbaseV1 hgaugeV1
  have hcoordV3 : coord V3 =
      homogeneousLift (triangleExitBasePoint (left V3)) := by
    simpa only [coord, fixedChartExitCoordinateEquiv_apply] using
      fixedChartExitCoordinateMap_base base left fixedGauge X
        hbaseV3 hgaugeV3
  have hform' : ∀ Z, middle Z =
      coord Z ⬝ᵥ triangleExitMiddleCovector t2 delta := by
    simpa only [coord] using hform
  rcases triangleExit_transportedBarycentric coord middle left right
      (left V1) t2 (left V3) delta h12 h23 hdelta
      hcoordX hcoordV1 hcoordV3 hform'
      hleftV hleftX hrightV hrightX with hleft | hright
  · left
    rcases hleft with ⟨h, hh0, hh1, hY0, hYm, hYa, _⟩
    exact ⟨h, hh0, hh1, hY0, hYm, hYa⟩
  · right
    rcases hright with ⟨h, hh0, hh1, hY0, hYm, hYb, _⟩
    exact ⟨h, hh0, hh1, hY0, hYm, hYb⟩

/-- The transverse support through the middle base point has the canonical
middle-line equation in fixed-chart coordinates. -/
theorem exists_fixedChart_middle_normalForm
    (A : FiniteProjectiveLineArrangement Line) (sigma : Line → Bool)
    (fixedGauge : Homogeneous3 →ₗ[ℝ] ℝ)
    {l a m : Line} (hla : l ≠ a) (hml : m ≠ l)
    (hgaugeLA : fixedGauge (A.intersection l a).rep ≠ 0)
    {X V : Homogeneous3}
    (hbaseX : A.arrangementOrientedEvaluation sigma l X ≠ 0)
    (hbaseV : A.arrangementOrientedEvaluation sigma l V = 0)
    (hgaugeV : fixedGauge V = 1)
    (hVm : A.arrangementOrientedEvaluation sigma m V = 0) :
    ∃ scale delta : ℝ, scale ≠ 0 ∧
      ∀ Z, A.arrangementOrientedEvaluation sigma m Z =
        scale *
          (A.fixedChartArrangementCoordinateEquiv sigma fixedGauge
              l a X hla hgaugeLA hbaseX Z ⬝ᵥ
            triangleExitMiddleCovector
              (A.arrangementOrientedEvaluation sigma a V) delta) := by
  let coord := A.fixedChartArrangementCoordinateEquiv sigma fixedGauge
    l a X hla hgaugeLA hbaseX
  apply exists_pulled_middle_normalForm A sigma hml coord
    (A.arrangementOrientedEvaluation sigma l X) hbaseX
  · intro Z
    simp [coord]
  · simpa only [coord, fixedChartBaseParameter] using
      fixedChartExitCoordinateMap_base
        (A.arrangementOrientedEvaluation sigma l)
        (A.arrangementOrientedEvaluation sigma a)
        fixedGauge X hbaseV hgaugeV
  · exact hVm

/-- The canonical displacement of an actual transverse support is nonzero. -/
theorem exists_fixedChart_middle_normalForm_delta_ne_zero
    (A : FiniteProjectiveLineArrangement Line) (sigma : Line → Bool)
    (fixedGauge : Homogeneous3 →ₗ[ℝ] ℝ)
    {l a c m : Line} (hla : l ≠ a) (hlc : l ≠ c)
    (hml : m ≠ l) (hmc : m ≠ c)
    (hgaugeLA : fixedGauge (A.intersection l a).rep ≠ 0)
    {x v : RealProjectivePoint} {X V : Homogeneous3}
    (hX0 : X ≠ 0) (hmkX : Projectivization.mk ℝ X hX0 = x)
    (hxNotBase : ¬ A.Incident x l) (hxc : A.Incident x c)
    (hvl : A.Incident v l) (hvc : A.Incident v c)
    (hvm : A.Incident v m)
    (hbaseX : A.arrangementOrientedEvaluation sigma l X ≠ 0)
    (hgaugeX : fixedGauge X = 1)
    (hbaseV : A.arrangementOrientedEvaluation sigma l V = 0)
    (hgaugeV : fixedGauge V = 1)
    (hVm : A.arrangementOrientedEvaluation sigma m V = 0) :
    ∃ scale delta : ℝ, scale ≠ 0 ∧ delta ≠ 0 ∧
      ∀ Z, A.arrangementOrientedEvaluation sigma m Z =
        scale *
          (A.fixedChartArrangementCoordinateEquiv sigma fixedGauge
              l a X hla hgaugeLA hbaseX Z ⬝ᵥ
            triangleExitMiddleCovector
              (A.arrangementOrientedEvaluation sigma a V) delta) := by
  obtain ⟨scale, delta, hscale, hform⟩ :=
    A.exists_fixedChart_middle_normalForm sigma fixedGauge hla hml
      hgaugeLA hbaseX hbaseV hgaugeV hVm
  let coord := A.fixedChartArrangementCoordinateEquiv sigma fixedGauge
    l a X hla hgaugeLA hbaseX
  have hcoordX : coord X = homogeneousLift (triangleExitTopPoint 0) := by
    simpa only [coord, fixedChartArrangementCoordinateEquiv_apply] using
      fixedChartExitCoordinateMap_apex
        (A.arrangementOrientedEvaluation sigma l)
        (A.arrangementOrientedEvaluation sigma a)
        fixedGauge hbaseX hgaugeX
  have hdelta : delta ≠ 0 := by
    apply A.sectorExit_delta_ne_zero sigma hmc hX0 hmkX hxNotBase hxc
      hvl hvc hvm coord hcoordX
      (A.arrangementOrientedEvaluation sigma a V) scale delta
    simpa only [coord] using hform
  exact ⟨scale, delta, hscale, hdelta, hform⟩

/-- Ordered arrangement data gives one of the two fixed-chart homogeneous
exit branches. -/
theorem fixedChartExit_barycentric_ordered
    (A : FiniteProjectiveLineArrangement Line) (sigma : Line → Bool)
    (fixedGauge : Homogeneous3 →ₗ[ℝ] ℝ)
    (l a b c m : Line) (x : RealProjectivePoint)
    (hgauge : ∀ q : RealProjectivePoint, q ∈ A.vertexSet →
      fixedGauge q.rep ≠ 0)
    (hxVertex : x ∈ A.vertexSet)
    (hla : l ≠ a) (hlb : l ≠ b) (hlc : l ≠ c)
    (hml : m ≠ l) (hmc : m ≠ c)
    (hxNotBase : ¬ A.Incident x l)
    (hxa : A.Incident x a) (hxb : A.Incident x b)
    (hxc : A.Incident x c)
    (hV2m : A.Incident (A.intersection l c) m)
    (h12 : A.fixedChartBaseParameter sigma fixedGauge a
        (A.intersection l a) <
      A.fixedChartBaseParameter sigma fixedGauge a
        (A.intersection l c))
    (h23 : A.fixedChartBaseParameter sigma fixedGauge a
        (A.intersection l c) <
      A.fixedChartBaseParameter sigma fixedGauge a
        (A.intersection l b)) :
    (∃ h : ℝ, ∃ Y : Homogeneous3,
      0 < h ∧ h < 1 ∧
      Y = (1 - h) • vertexChartNormalizedVector fixedGauge
          (A.intersection l a) +
        h • vertexChartNormalizedVector fixedGauge x ∧
      Y ≠ 0 ∧
      A.arrangementOrientedEvaluation sigma m Y = 0 ∧
      A.arrangementOrientedEvaluation sigma a Y = 0) ∨
    (∃ h : ℝ, ∃ Y : Homogeneous3,
      0 < h ∧ h < 1 ∧
      Y = (1 - h) • vertexChartNormalizedVector fixedGauge
          (A.intersection l b) +
        h • vertexChartNormalizedVector fixedGauge x ∧
      Y ≠ 0 ∧
      A.arrangementOrientedEvaluation sigma m Y = 0 ∧
      A.arrangementOrientedEvaluation sigma b Y = 0) := by
  let v1 := A.intersection l a
  let v2 := A.intersection l c
  let v3 := A.intersection l b
  have hv1Vertex : v1 ∈ A.vertexSet := by
    simpa only [v1] using A.intersection_mem_vertexSet hla
  have hv2Vertex : v2 ∈ A.vertexSet := by
    simpa only [v2] using A.intersection_mem_vertexSet hlc
  have hv3Vertex : v3 ∈ A.vertexSet := by
    simpa only [v3] using A.intersection_mem_vertexSet hlb
  have hfx := hgauge x hxVertex
  have hfv1 := hgauge v1 hv1Vertex
  have hfv2 := hgauge v2 hv2Vertex
  have hfv3 := hgauge v3 hv3Vertex
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
    simpa only [v1] using A.intersection_incident_left hla
  have hV2base : A.arrangementOrientedEvaluation sigma l V2 = 0 := by
    apply A.arrangementOrientedEvaluation_vertexChartNormalizedVector_eq_zero
      sigma fixedGauge hfv2
    simpa only [v2] using A.intersection_incident_left hlc
  have hV3base : A.arrangementOrientedEvaluation sigma l V3 = 0 := by
    apply A.arrangementOrientedEvaluation_vertexChartNormalizedVector_eq_zero
      sigma fixedGauge hfv3
    simpa only [v3] using A.intersection_incident_left hlb
  have hV2evalM : A.arrangementOrientedEvaluation sigma m V2 = 0 :=
    A.arrangementOrientedEvaluation_vertexChartNormalizedVector_eq_zero
      sigma fixedGauge hfv2 (by simpa only [v2] using hV2m)
  obtain ⟨scale, delta, hscale, hdelta, hform⟩ :=
    A.exists_fixedChart_middle_normalForm_delta_ne_zero sigma fixedGauge
      hla hlc hml hmc hfv1 hX0 hmkX hxNotBase hxc
      (by simpa only [v2] using A.intersection_incident_left hlc)
      (by simpa only [v2] using A.intersection_incident_right hlc)
      (by simpa only [v2] using hV2m)
      hXbase hXgauge hV2base
      (by simpa only [V2] using
        vertexChartNormalizedVector_fixedGauge_eq_one fixedGauge v2 hfv2)
      hV2evalM
  let coord := A.fixedChartArrangementCoordinateEquiv sigma fixedGauge
    l a X hla hfv1 hXbase
  let middle := scale⁻¹ • A.arrangementOrientedEvaluation sigma m
  have hmiddle : ∀ Z, middle Z =
      coord Z ⬝ᵥ triangleExitMiddleCovector
        (A.arrangementOrientedEvaluation sigma a V2) delta := by
    intro Z
    simp only [middle, LinearMap.smul_apply, smul_eq_mul, hform Z, coord]
    rw [← mul_assoc, inv_mul_cancel₀ hscale, one_mul]
  let hkernel : ∀ Z,
      A.arrangementOrientedEvaluation sigma l Z = 0 →
      A.arrangementOrientedEvaluation sigma a Z = 0 →
      fixedGauge Z = 0 → Z = 0 :=
    fun Z hl ha hf =>
      A.eq_zero_of_two_orientedEvaluations_and_fixedGauge
        sigma fixedGauge hla hfv1 Z hl ha hf
  have hmiddle' : ∀ Z, middle Z =
      fixedChartExitCoordinateEquiv
          (A.arrangementOrientedEvaluation sigma l)
          (A.arrangementOrientedEvaluation sigma a)
          fixedGauge X hkernel hXbase Z ⬝ᵥ
        triangleExitMiddleCovector
          (A.arrangementOrientedEvaluation sigma a V2) delta := by
    simpa only [coord, hkernel, fixedChartArrangementCoordinateEquiv]
      using hmiddle
  have hV1gauge : fixedGauge V1 = 1 := by
    simpa only [V1] using
      vertexChartNormalizedVector_fixedGauge_eq_one fixedGauge v1 hfv1
  have hV3gauge : fixedGauge V3 = 1 := by
    simpa only [V3] using
      vertexChartNormalizedVector_fixedGauge_eq_one fixedGauge v3 hfv3
  have hleftV : A.arrangementOrientedEvaluation sigma a V1 = 0 := by
    apply A.arrangementOrientedEvaluation_vertexChartNormalizedVector_eq_zero
      sigma fixedGauge hfv1
    simpa only [v1] using A.intersection_incident_right hla
  have hleftX : A.arrangementOrientedEvaluation sigma a X = 0 := by
    simpa only [X] using
      A.arrangementOrientedEvaluation_vertexChartNormalizedVector_eq_zero
        sigma fixedGauge hfx hxa
  have hrightV : A.arrangementOrientedEvaluation sigma b V3 = 0 := by
    apply A.arrangementOrientedEvaluation_vertexChartNormalizedVector_eq_zero
      sigma fixedGauge hfv3
    simpa only [v3] using A.intersection_incident_right hlb
  have hrightX : A.arrangementOrientedEvaluation sigma b X = 0 := by
    simpa only [X] using
      A.arrangementOrientedEvaluation_vertexChartNormalizedVector_eq_zero
        sigma fixedGauge hfx hxb
  have ht12 : A.arrangementOrientedEvaluation sigma a V1 <
      A.arrangementOrientedEvaluation sigma a V2 := by
    simpa only [fixedChartBaseParameter, V1, V2, v1, v2] using h12
  have ht23 : A.arrangementOrientedEvaluation sigma a V2 <
      A.arrangementOrientedEvaluation sigma a V3 := by
    simpa only [fixedChartBaseParameter, V2, V3, v2, v3] using h23
  rcases fixedChart_transportedBarycentric
      (A.arrangementOrientedEvaluation sigma l)
      (A.arrangementOrientedEvaluation sigma a)
      (A.arrangementOrientedEvaluation sigma b)
      fixedGauge middle hkernel hXbase hXgauge
      hV1base hV1gauge hV3base hV3gauge
      (A.arrangementOrientedEvaluation sigma a V2) delta
      ht12 ht23 hdelta hmiddle' hleftV hleftX hrightV hrightX with
    hleft | hright
  · rcases hleft with ⟨h, hh0, hh1, hrest⟩
    dsimp only at hrest
    rcases hrest with ⟨hY0, hYm', hYa⟩
    have hYm : A.arrangementOrientedEvaluation sigma m
        ((1 - h) • V1 + h • X) = 0 := by
      simp only [middle, LinearMap.smul_apply, smul_eq_mul] at hYm'
      exact (mul_eq_zero.mp hYm').resolve_left (inv_ne_zero hscale)
    left
    refine ⟨h, (1 - h) • V1 + h • X, hh0, hh1, ?_, hY0, hYm, hYa⟩
    simp only [V1, X, v1]
  · rcases hright with ⟨h, hh0, hh1, hrest⟩
    dsimp only at hrest
    rcases hrest with ⟨hY0, hYm', hYb⟩
    have hYm : A.arrangementOrientedEvaluation sigma m
        ((1 - h) • V3 + h • X) = 0 := by
      simp only [middle, LinearMap.smul_apply, smul_eq_mul] at hYm'
      exact (mul_eq_zero.mp hYm').resolve_left (inv_ne_zero hscale)
    right
    refine ⟨h, (1 - h) • V3 + h • X, hh0, hh1, ?_, hY0, hYm, hYb⟩
    simp only [V3, X, v3]

/-- Finish a homogeneous fixed-chart branch as an actual arrangement
vertex, retaining the barycentric factor and the exact height scaling. -/
theorem fixedChartExit_finish_branch
    (A : FiniteProjectiveLineArrangement Line) (sigma : Line → Bool)
    (fixedGauge : Homogeneous3 →ₗ[ℝ] ℝ)
    (l m n : Line) (x : RealProjectivePoint)
    {X V Y : Homogeneous3} {h : ℝ}
    (hh0 : 0 < h) (hh1 : h < 1)
    (hY : Y = (1 - h) • V + h • X)
    (hY0 : Y ≠ 0) (hmn : m ≠ n)
    (hYm : A.arrangementOrientedEvaluation sigma m Y = 0)
    (hYn : A.arrangementOrientedEvaluation sigma n Y = 0)
    (hVbase : A.arrangementOrientedEvaluation sigma l V = 0)
    (hVgauge : fixedGauge V = 1) (hXgauge : fixedGauge X = 1)
    (hXbase : A.arrangementOrientedEvaluation sigma l X ≠ 0)
    (hXnormalized : vertexChartNormalizedVector fixedGauge x = X) :
    ∃ y : RealProjectivePoint,
      y ∈ A.vertexSet ∧ A.Incident y m ∧ A.Incident y n ∧
      ¬ A.Incident y l ∧
      vertexChartNormalizedVector fixedGauge y = Y ∧
      A.vertexChartLineHeight fixedGauge l y =
        h * A.vertexChartLineHeight fixedGauge l x ∧
      A.vertexChartLineHeight fixedGauge l y <
        A.vertexChartLineHeight fixedGauge l x := by
  let y : RealProjectivePoint := Projectivization.mk ℝ Y hY0
  have hym : A.Incident y m :=
    (A.incident_projectivization_mk_iff_orientedEvaluation_eq_zero
      sigma m Y hY0).2 hYm
  have hyn : A.Incident y n :=
    (A.incident_projectivization_mk_iff_orientedEvaluation_eq_zero
      sigma n Y hY0).2 hYn
  have hyVertex : y ∈ A.vertexSet := by
    rw [A.eq_intersection_of_incident hmn hym hyn]
    exact A.intersection_mem_vertexSet hmn
  have hYgauge : fixedGauge Y = 1 := by
    rw [hY, LinearMap.map_add, LinearMap.map_smul,
      LinearMap.map_smul, hVgauge, hXgauge]
    simp only [smul_eq_mul]
    ring
  have hyNormalized : vertexChartNormalizedVector fixedGauge y = Y := by
    apply vertexChartNormalizedVector_eq_of_projectivization_mk
      fixedGauge y hY0 hYgauge
    rfl
  have hyEval : A.arrangementOrientedEvaluation sigma l Y =
      h * A.arrangementOrientedEvaluation sigma l X := by
    rw [hY, LinearMap.map_add, LinearMap.map_smul,
      LinearMap.map_smul, hVbase]
    simp only [smul_eq_mul, mul_zero, zero_add]
  have hyNotBase : ¬ A.Incident y l := by
    intro hyl
    have hzero :=
      (A.incident_projectivization_mk_iff_orientedEvaluation_eq_zero
        sigma l Y hY0).1 hyl
    rw [hyEval] at hzero
    exact (mul_ne_zero hh0.ne' hXbase) hzero
  have habs (Z : Homogeneous3) :
      |projectiveLineEvaluation (A.projectiveLine l) Z| =
        |A.arrangementOrientedEvaluation sigma l Z| := by
    by_cases hs : sigma l <;>
      simp [arrangementOrientedEvaluation, hs]
  have hyHeight : A.vertexChartLineHeight fixedGauge l y =
      h * A.vertexChartLineHeight fixedGauge l x := by
    unfold vertexChartLineHeight
    rw [hyNormalized, hXnormalized, habs Y, habs X, hyEval,
      abs_mul, abs_of_pos hh0]
  have hxHeightPos : 0 < A.vertexChartLineHeight fixedGauge l x := by
    unfold vertexChartLineHeight
    rw [hXnormalized, habs X]
    exact abs_pos.mpr hXbase
  refine ⟨y, hyVertex, hym, hyn, hyNotBase, hyNormalized, hyHeight, ?_⟩
  rw [hyHeight]
  nlinarith

/-- Public ordered fixed-chart exit.  Besides the actual smaller vertex it
retains the barycentric factor, so any other height using the same affine
chart can reuse the exact scaling identity. -/
theorem fixedChartExit_ordered
    (A : FiniteProjectiveLineArrangement Line) (sigma : Line → Bool)
    (fixedGauge : Homogeneous3 →ₗ[ℝ] ℝ)
    (l a b c m : Line) (x : RealProjectivePoint)
    (hgauge : ∀ q : RealProjectivePoint, q ∈ A.vertexSet →
      fixedGauge q.rep ≠ 0)
    (hxVertex : x ∈ A.vertexSet)
    (hla : l ≠ a) (hlb : l ≠ b) (hlc : l ≠ c)
    (hml : m ≠ l) (hmc : m ≠ c)
    (hxNotBase : ¬ A.Incident x l)
    (hxa : A.Incident x a) (hxb : A.Incident x b)
    (hxc : A.Incident x c)
    (hV2m : A.Incident (A.intersection l c) m)
    (h12 : A.fixedChartBaseParameter sigma fixedGauge a
        (A.intersection l a) <
      A.fixedChartBaseParameter sigma fixedGauge a
        (A.intersection l c))
    (h23 : A.fixedChartBaseParameter sigma fixedGauge a
        (A.intersection l c) <
      A.fixedChartBaseParameter sigma fixedGauge a
        (A.intersection l b)) :
    ∃ y : RealProjectivePoint, ∃ h : ℝ,
      0 < h ∧ h < 1 ∧ y ∈ A.vertexSet ∧
      A.Incident y m ∧ ¬ A.Incident y l ∧
      A.vertexChartLineHeight fixedGauge l y =
        h * A.vertexChartLineHeight fixedGauge l x ∧
      A.vertexChartLineHeight fixedGauge l y <
        A.vertexChartLineHeight fixedGauge l x ∧
      ((A.Incident y a ∧
        vertexChartNormalizedVector fixedGauge y =
          (1 - h) • vertexChartNormalizedVector fixedGauge
              (A.intersection l a) +
            h • vertexChartNormalizedVector fixedGauge x) ∨
       (A.Incident y b ∧
        vertexChartNormalizedVector fixedGauge y =
          (1 - h) • vertexChartNormalizedVector fixedGauge
              (A.intersection l b) +
            h • vertexChartNormalizedVector fixedGauge x)) := by
  have houter := A.fixedChartExit_transverse_ne_outer sigma fixedGauge
    hla hlb hlc hV2m h12 h23
  rcases A.fixedChartExit_barycentric_ordered sigma fixedGauge
      l a b c m x hgauge hxVertex hla hlb hlc hml hmc
      hxNotBase hxa hxb hxc hV2m h12 h23 with hleft | hright
  · rcases hleft with ⟨h, Y, hh0, hh1, hY, hY0, hYm, hYa⟩
    have hfV := hgauge (A.intersection l a)
      (A.intersection_mem_vertexSet hla)
    have hVbase :=
      A.arrangementOrientedEvaluation_vertexChartNormalizedVector_eq_zero
        sigma fixedGauge hfV (A.intersection_incident_left hla)
    have hVgauge := vertexChartNormalizedVector_fixedGauge_eq_one
      fixedGauge (A.intersection l a) hfV
    have hfx := hgauge x hxVertex
    have hXgauge := vertexChartNormalizedVector_fixedGauge_eq_one
      fixedGauge x hfx
    have hXbase :=
      A.arrangementOrientedEvaluation_vertexChartNormalizedVector_ne_zero
        sigma fixedGauge hfx hxNotBase
    obtain ⟨y, hyVertex, hym, hya, hyNotBase, hyNorm,
        hyHeight, hyLt⟩ :=
      A.fixedChartExit_finish_branch sigma fixedGauge l m a x
        hh0 hh1 hY hY0 houter.1 hYm hYa hVbase hVgauge
        hXgauge hXbase rfl
    exact ⟨y, h, hh0, hh1, hyVertex, hym, hyNotBase,
      hyHeight, hyLt, Or.inl ⟨hya, by simpa only [hY] using hyNorm⟩⟩
  · rcases hright with ⟨h, Y, hh0, hh1, hY, hY0, hYm, hYb⟩
    have hfV := hgauge (A.intersection l b)
      (A.intersection_mem_vertexSet hlb)
    have hVbase :=
      A.arrangementOrientedEvaluation_vertexChartNormalizedVector_eq_zero
        sigma fixedGauge hfV (A.intersection_incident_left hlb)
    have hVgauge := vertexChartNormalizedVector_fixedGauge_eq_one
      fixedGauge (A.intersection l b) hfV
    have hfx := hgauge x hxVertex
    have hXgauge := vertexChartNormalizedVector_fixedGauge_eq_one
      fixedGauge x hfx
    have hXbase :=
      A.arrangementOrientedEvaluation_vertexChartNormalizedVector_ne_zero
        sigma fixedGauge hfx hxNotBase
    obtain ⟨y, hyVertex, hym, hyb, hyNotBase, hyNorm,
        hyHeight, hyLt⟩ :=
      A.fixedChartExit_finish_branch sigma fixedGauge l m b x
        hh0 hh1 hY hY0 houter.2 hYm hYb hVbase hVgauge
        hXgauge hXbase rfl
    exact ⟨y, h, hh0, hh1, hyVertex, hym, hyNotBase,
      hyHeight, hyLt, Or.inr ⟨hyb, by simpa only [hY] using hyNorm⟩⟩

end FiniteProjectiveLineArrangement

end Erdos506.Incidence
