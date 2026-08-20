import Erdos506.Incidence.RealProjectiveArrangementKellyMoserFinish
import Erdos506.Incidence.RealProjectiveTriangleExit

/-!
# The actual sector-exit adapter for the Kelly--Moser argument

This downstream leaf combines the arrangement barycentric coordinates with
the low-level planar exit.  Keeping it downstream avoids an import cycle with
the finite Kelly--Rottenberg layer.
-/

namespace Erdos506.Incidence

open Erdos506.V4
open Matrix
open scoped LinearAlgebra.Projectivization

namespace FiniteProjectiveLineArrangement

variable {Line : Type*} [Fintype Line] [DecidableEq Line]

/-- Gauge-one representative of a point in the chosen triangle chart. -/
noncomputable def sectorExitNormalizedPoint
    (A : FiniteProjectiveLineArrangement Line) (sigma : Line → Bool)
    (l a b : Line) (q : RealProjectivePoint) : Homogeneous3 :=
  A.triangleSectorNormalizedVector sigma l a b q.rep

/-- Ordered affine coordinate of a gauge-one point on the base. -/
noncomputable def sectorExitBaseParameter
    (A : FiniteProjectiveLineArrangement Line) (sigma : Line → Bool)
    (l a b : Line) (q : RealProjectivePoint) : ℝ :=
  A.arrangementOrientedEvaluation sigma a
    (A.sectorExitNormalizedPoint sigma l a b q)

/-- The covector of a linear functional after transporting it through a
homogeneous coordinate equivalence. -/
noncomputable def pulledLineCovector
    (coord : Homogeneous3 ≃ₗ[ℝ] Homogeneous3)
    (f : Homogeneous3 →ₗ[ℝ] ℝ) : Homogeneous3 :=
  ![
    f (coord.symm ![1, 0, 0]),
    f (coord.symm ![0, 1, 0]),
    f (coord.symm ![0, 0, 1])]

/-- Every transported functional is dot product with its pulled covector. -/
theorem linearMap_eq_dot_pulledLineCovector
    (coord : Homogeneous3 ≃ₗ[ℝ] Homogeneous3)
    (f : Homogeneous3 →ₗ[ℝ] ℝ) (v : Homogeneous3) :
    f v = coord v ⬝ᵥ pulledLineCovector coord f := by
  let z := coord v
  have hv : v = coord.symm z := by
    simpa only [z] using (coord.symm_apply_apply v).symm
  have hz : z =
      z 0 • ![1, 0, 0] + z 1 • ![0, 1, 0] + z 2 • ![0, 0, 1] := by
    ext i
    fin_cases i <;> simp
  rw [hv, hz]
  simp only [map_add, map_smul]
  simp [pulledLineCovector, dotProduct, Fin.sum_univ_three]

/-- A line through the base point `(t,0,1)`, distinct from the base itself,
has the canonical equation up to a nonzero scalar. -/
theorem exists_pulled_middle_normalForm
    (A : FiniteProjectiveLineArrangement Line) (sigma : Line → Bool)
    {l m : Line} (hlm : m ≠ l)
    (coord : Homogeneous3 ≃ₗ[ℝ] Homogeneous3)
    (heightScale : ℝ) (hheightScale : heightScale ≠ 0)
    (hheight : ∀ Z, coord Z 1 = heightScale⁻¹ *
      A.arrangementOrientedEvaluation sigma l Z)
    {V : Homogeneous3} (t : ℝ)
    (hVcoord : coord V = homogeneousLift (triangleExitBasePoint t))
    (hVm : A.arrangementOrientedEvaluation sigma m V = 0) :
    ∃ scale delta : ℝ, scale ≠ 0 ∧
      ∀ Z, A.arrangementOrientedEvaluation sigma m Z =
        scale * (coord Z ⬝ᵥ triangleExitMiddleCovector t delta) := by
  let f := A.arrangementOrientedEvaluation sigma m
  let w := pulledLineCovector coord f
  have hVdot : homogeneousLift (triangleExitBasePoint t) ⬝ᵥ w = 0 := by
    rw [← hVcoord, ← linearMap_eq_dot_pulledLineCovector coord f V]
    exact hVm
  have hscale : w 0 ≠ 0 := by
    intro hzero
    have hthird : w 2 = 0 := by
      simpa [triangleExitBasePoint, homogeneousLift, dotProduct,
        Fin.sum_univ_three, hzero] using hVdot
    apply hlm
    apply A.eq_of_orientedEvaluation_eq_smul sigma
      (w 1 * heightScale⁻¹)
    apply LinearMap.ext
    intro Z
    rw [linearMap_eq_dot_pulledLineCovector coord f Z]
    change coord Z ⬝ᵥ w =
      (w 1 * heightScale⁻¹) * A.arrangementOrientedEvaluation sigma l Z
    simp only [dotProduct, Fin.sum_univ_three, hzero, hthird,
      mul_zero, add_zero, zero_add]
    rw [hheight Z]
    ring
  have hthird : w 2 = -(w 0 * t) := by
    simp [triangleExitBasePoint, homogeneousLift, dotProduct,
      Fin.sum_univ_three] at hVdot
    linarith
  refine ⟨w 0, t - w 1 / w 0, hscale, fun Z => ?_⟩
  rw [linearMap_eq_dot_pulledLineCovector coord f Z]
  change coord Z ⬝ᵥ w = _
  simp [triangleExitMiddleCovector, dotProduct, Fin.sum_univ_three,
    hthird]
  field_simp [hscale]

/-- Affine coordinates adapted to a triangle sector and a normalized apex.
The coordinates are position along the base, relative base height, and the
triangle gauge. -/
noncomputable def sectorExitCoordinateMap
    (A : FiniteProjectiveLineArrangement Line) (sigma : Line → Bool)
    (l a b : Line) (X : Homogeneous3) :
    Homogeneous3 →ₗ[ℝ] Homogeneous3 :=
  LinearMap.pi ![
    A.arrangementOrientedEvaluation sigma a -
      ((A.arrangementOrientedEvaluation sigma a X) /
        (A.arrangementOrientedEvaluation sigma l X)) •
          A.arrangementOrientedEvaluation sigma l,
    ((A.arrangementOrientedEvaluation sigma l X)⁻¹) •
      A.arrangementOrientedEvaluation sigma l,
    A.arrangementOrientedEvaluation sigma l +
      A.arrangementOrientedEvaluation sigma a +
        A.arrangementOrientedEvaluation sigma b]

@[simp]
theorem sectorExitCoordinateMap_apply_zero
    (A : FiniteProjectiveLineArrangement Line) (sigma : Line → Bool)
    (l a b : Line) (X v : Homogeneous3) :
    A.sectorExitCoordinateMap sigma l a b X v 0 =
      A.arrangementOrientedEvaluation sigma a v -
        ((A.arrangementOrientedEvaluation sigma a X) /
          (A.arrangementOrientedEvaluation sigma l X)) *
            A.arrangementOrientedEvaluation sigma l v := by
  simp [sectorExitCoordinateMap, smul_eq_mul]

@[simp]
theorem sectorExitCoordinateMap_apply_one
    (A : FiniteProjectiveLineArrangement Line) (sigma : Line → Bool)
    (l a b : Line) (X v : Homogeneous3) :
    A.sectorExitCoordinateMap sigma l a b X v 1 =
      (A.arrangementOrientedEvaluation sigma l X)⁻¹ *
        A.arrangementOrientedEvaluation sigma l v := by
  simp [sectorExitCoordinateMap, smul_eq_mul]

@[simp]
theorem sectorExitCoordinateMap_apply_two
    (A : FiniteProjectiveLineArrangement Line) (sigma : Line → Bool)
    (l a b : Line) (X v : Homogeneous3) :
    A.sectorExitCoordinateMap sigma l a b X v 2 =
      A.triangleSectorGauge sigma l a b v := by
  simp [sectorExitCoordinateMap, triangleSectorGauge]

/-- A gauge-one apex is the canonical point `(0,1,1)` in the adapted
coordinates. -/
theorem sectorExitCoordinateMap_apex
    (A : FiniteProjectiveLineArrangement Line) (sigma : Line → Bool)
    (l a b : Line) {X : Homogeneous3}
    (hheight : A.arrangementOrientedEvaluation sigma l X ≠ 0)
    (hgauge : A.triangleSectorGauge sigma l a b X = 1) :
    A.sectorExitCoordinateMap sigma l a b X X =
      homogeneousLift (triangleExitTopPoint 0) := by
  ext i
  fin_cases i
  · simp [triangleExitTopPoint, homogeneousLift, hheight]
  · simp [triangleExitTopPoint, homogeneousLift, hheight]
  · simp [triangleExitTopPoint, homogeneousLift, hgauge]

/-- A gauge-one point of the base gets canonical coordinates `(t,0,1)`,
where `t` is its inward `a`-evaluation. -/
theorem sectorExitCoordinateMap_base
    (A : FiniteProjectiveLineArrangement Line) (sigma : Line → Bool)
    (l a b : Line) {X V : Homogeneous3}
    (hbase : A.arrangementOrientedEvaluation sigma l V = 0)
    (hgauge : A.triangleSectorGauge sigma l a b V = 1) :
    A.sectorExitCoordinateMap sigma l a b X V =
      homogeneousLift
        (triangleExitBasePoint
          (A.arrangementOrientedEvaluation sigma a V)) := by
  ext i
  fin_cases i
  · simp [triangleExitBasePoint, homogeneousLift, hbase]
  · simp [triangleExitBasePoint, homogeneousLift, hbase]
  · simp [triangleExitBasePoint, homogeneousLift, hgauge]

/-- Nonconcurrency of the three triangle sides and nonzero apex height make
the adapted coordinate map invertible. -/
theorem sectorExitCoordinateMap_injective
    (A : FiniteProjectiveLineArrangement Line) (sigma : Line → Bool)
    (l a b : Line) (X : Homogeneous3)
    (htriangle : ¬ ∃ q : RealProjectivePoint,
      A.Incident q l ∧ A.Incident q a ∧ A.Incident q b)
    (hheight : A.arrangementOrientedEvaluation sigma l X ≠ 0) :
    Function.Injective (A.sectorExitCoordinateMap sigma l a b X) := by
  intro v w hvw
  apply sub_eq_zero.mp
  apply A.eq_zero_of_three_orientedEvaluations_eq_zero
    sigma l a b htriangle (v - w)
  · have hcoord := congrFun hvw (1 : Fin 3)
    simp only [sectorExitCoordinateMap_apply_one] at hcoord
    rw [LinearMap.map_sub]
    exact sub_eq_zero.mpr
      (mul_left_cancel₀ (inv_ne_zero hheight) hcoord)
  · have hcoord0 := congrFun hvw (0 : Fin 3)
    have hcoord1 := congrFun hvw (1 : Fin 3)
    simp only [sectorExitCoordinateMap_apply_zero] at hcoord0
    simp only [sectorExitCoordinateMap_apply_one] at hcoord1
    have hl : A.arrangementOrientedEvaluation sigma l v =
        A.arrangementOrientedEvaluation sigma l w :=
      mul_left_cancel₀ (inv_ne_zero hheight) hcoord1
    rw [hl] at hcoord0
    rw [LinearMap.map_sub]
    exact sub_eq_zero.mpr (by linarith)
  · have hcoord2 := congrFun hvw (2 : Fin 3)
    have hcoord0 := congrFun hvw (0 : Fin 3)
    have hcoord1 := congrFun hvw (1 : Fin 3)
    simp only [sectorExitCoordinateMap_apply_two] at hcoord2
    simp only [sectorExitCoordinateMap_apply_zero] at hcoord0
    simp only [sectorExitCoordinateMap_apply_one] at hcoord1
    have hl : A.arrangementOrientedEvaluation sigma l v =
        A.arrangementOrientedEvaluation sigma l w :=
      mul_left_cancel₀ (inv_ne_zero hheight) hcoord1
    rw [hl] at hcoord0
    have ha : A.arrangementOrientedEvaluation sigma a v =
        A.arrangementOrientedEvaluation sigma a w := by
      linarith
    rw [LinearMap.map_sub]
    unfold triangleSectorGauge at hcoord2
    exact sub_eq_zero.mpr (by linarith)

/-- The actual linear equivalence used to pull arrangement lines into the
canonical barycentric exit chart. -/
noncomputable def sectorExitCoordinateEquiv
    (A : FiniteProjectiveLineArrangement Line) (sigma : Line → Bool)
    (l a b : Line) (X : Homogeneous3)
    (htriangle : ¬ ∃ q : RealProjectivePoint,
      A.Incident q l ∧ A.Incident q a ∧ A.Incident q b)
    (hheight : A.arrangementOrientedEvaluation sigma l X ≠ 0) :
    Homogeneous3 ≃ₗ[ℝ] Homogeneous3 :=
  LinearEquiv.ofInjectiveEndo
    (A.sectorExitCoordinateMap sigma l a b X)
    (A.sectorExitCoordinateMap_injective
      sigma l a b X htriangle hheight)

@[simp]
theorem sectorExitCoordinateEquiv_apply
    (A : FiniteProjectiveLineArrangement Line) (sigma : Line → Bool)
    (l a b : Line) (X v : Homogeneous3)
    (htriangle : ¬ ∃ q : RealProjectivePoint,
      A.Incident q l ∧ A.Incident q a ∧ A.Incident q b)
    (hheight : A.arrangementOrientedEvaluation sigma l X ≠ 0) :
    A.sectorExitCoordinateEquiv sigma l a b X htriangle hheight v =
      A.sectorExitCoordinateMap sigma l a b X v :=
  rfl

/-- Arrangement-level specialization of the pulled middle-line normal form. -/
theorem exists_sectorExit_middle_normalForm
    (A : FiniteProjectiveLineArrangement Line) (sigma : Line → Bool)
    (l a b m : Line)
    (htriangle : ¬ ∃ q : RealProjectivePoint,
      A.Incident q l ∧ A.Incident q a ∧ A.Incident q b)
    {X V : Homogeneous3}
    (hXheight : A.arrangementOrientedEvaluation sigma l X ≠ 0)
    (hXgauge : A.triangleSectorGauge sigma l a b X = 1)
    (hVbase : A.arrangementOrientedEvaluation sigma l V = 0)
    (hVgauge : A.triangleSectorGauge sigma l a b V = 1)
    (hVm : A.arrangementOrientedEvaluation sigma m V = 0)
    (hml : m ≠ l) :
    ∃ scale delta : ℝ, scale ≠ 0 ∧
      ∀ Z, A.arrangementOrientedEvaluation sigma m Z =
        scale *
          (A.sectorExitCoordinateEquiv sigma l a b X
              htriangle hXheight Z ⬝ᵥ
            triangleExitMiddleCovector
              (A.arrangementOrientedEvaluation sigma a V) delta) := by
  let coord := A.sectorExitCoordinateEquiv sigma l a b X
    htriangle hXheight
  apply exists_pulled_middle_normalForm A sigma hml coord
    (A.arrangementOrientedEvaluation sigma l X) hXheight
  · intro Z
    simp [coord]
  · simpa [coord] using
      A.sectorExitCoordinateMap_base sigma l a b
        (X := X) hVbase hVgauge
  · exact hVm

/-- If the transverse line is different from the middle support, its
height-one displacement in the canonical chart is nonzero. -/
theorem sectorExit_delta_ne_zero
    (A : FiniteProjectiveLineArrangement Line) (sigma : Line → Bool)
    {l c m : Line} (hmc : m ≠ c)
    {x v : RealProjectivePoint} {X : Homogeneous3} (hX0 : X ≠ 0)
    (hmkX : Projectivization.mk ℝ X hX0 = x)
    (hxNotBase : ¬ A.Incident x l)
    (hxc : A.Incident x c)
    (hvl : A.Incident v l) (hvc : A.Incident v c)
    (hvm : A.Incident v m)
    (coord : Homogeneous3 ≃ₗ[ℝ] Homogeneous3)
    (hcoordX : coord X = homogeneousLift (triangleExitTopPoint 0))
    (t scale delta : ℝ)
    (hform : ∀ Z, A.arrangementOrientedEvaluation sigma m Z =
      scale * (coord Z ⬝ᵥ triangleExitMiddleCovector t delta)) :
    delta ≠ 0 := by
  intro hdelta
  have hXm : A.arrangementOrientedEvaluation sigma m X = 0 := by
    rw [hform, hcoordX, hdelta]
    simp [triangleExitTopPoint, homogeneousLift,
      triangleExitMiddleCovector, dotProduct, Fin.sum_univ_three]
  have hxM : A.Incident x m := by
    rw [← hmkX]
    exact (A.incident_projectivization_mk_iff_orientedEvaluation_eq_zero
      sigma m X hX0).2 hXm
  have hxIntersection : x = A.intersection m c :=
    A.eq_intersection_of_incident hmc hxM hxc
  have hvIntersection : v = A.intersection m c :=
    A.eq_intersection_of_incident hmc hvm hvc
  apply hxNotBase
  rw [hxIntersection, ← hvIntersection]
  exact hvl

/-- The closed triangle cone is preserved by a convex barycentric
combination. -/
theorem barycentric_mem_arrangementClosedSignConeOn
    (A : FiniteProjectiveLineArrangement Line) (sigma : Line → Bool)
    (l a b : Line) {V X : Homogeneous3} {h : ℝ}
    (hh0 : 0 ≤ h) (hh1 : h ≤ 1)
    (hV : V ∈ A.arrangementClosedSignConeOn sigma {l, a, b})
    (hX : X ∈ A.arrangementClosedSignConeOn sigma {l, a, b}) :
    (1 - h) • V + h • X ∈
      A.arrangementClosedSignConeOn sigma {l, a, b} := by
  intro k hk
  rw [LinearMap.map_add, LinearMap.map_smul, LinearMap.map_smul]
  simp only [smul_eq_mul]
  exact add_nonneg
    (mul_nonneg (sub_nonneg.mpr hh1) (hV k hk))
    (mul_nonneg hh0 (hX k hk))

/-- A barycentric combination of two gauge-one representatives again has
gauge one. -/
theorem triangleSectorGauge_barycentric_eq_one
    (A : FiniteProjectiveLineArrangement Line) (sigma : Line → Bool)
    (l a b : Line) {V X : Homogeneous3} (h : ℝ)
    (hV : A.triangleSectorGauge sigma l a b V = 1)
    (hX : A.triangleSectorGauge sigma l a b X = 1) :
    A.triangleSectorGauge sigma l a b
      ((1 - h) • V + h • X) = 1 := by
  simp only [triangleSectorGauge, LinearMap.map_add, LinearMap.map_smul,
    smul_eq_mul] at hV hX ⊢
  linear_combination (1 - h) * hV + h * hX

/-- Gauge-one representatives are unique inside a projective class. -/
theorem triangleSectorNormalizedVector_eq_of_projectivization_mk
    (A : FiniteProjectiveLineArrangement Line) (sigma : Line → Bool)
    (l a b : Line) (q : RealProjectivePoint)
    {v : Homogeneous3} (hv : v ≠ 0)
    (hg : A.triangleSectorGauge sigma l a b v = 1)
    (hq : Projectivization.mk ℝ v hv = q) :
    A.triangleSectorNormalizedVector sigma l a b q.rep = v := by
  have hmk : Projectivization.mk ℝ v hv =
      Projectivization.mk ℝ q.rep q.rep_nonzero :=
    hq.trans q.mk_rep.symm
  obtain ⟨c, hc⟩ :=
    (Projectivization.mk_eq_mk_iff' ℝ v q.rep hv q.rep_nonzero).mp hmk
  have hscale := congrArg
    (A.triangleSectorGauge sigma l a b) hc
  rw [A.triangleSectorGauge_smul, hg] at hscale
  have hgrepnz : A.triangleSectorGauge sigma l a b q.rep ≠ 0 := by
    intro hzero
    rw [hzero, mul_zero] at hscale
    norm_num at hscale
  have hcInv : c =
      (A.triangleSectorGauge sigma l a b q.rep)⁻¹ := by
    calc
      c = c * (A.triangleSectorGauge sigma l a b q.rep *
          (A.triangleSectorGauge sigma l a b q.rep)⁻¹) := by
        rw [mul_inv_cancel₀ hgrepnz, mul_one]
      _ = (c * A.triangleSectorGauge sigma l a b q.rep) *
          (A.triangleSectorGauge sigma l a b q.rep)⁻¹ := by ring
      _ = (A.triangleSectorGauge sigma l a b q.rep)⁻¹ := by
        rw [hscale, one_mul]
  unfold triangleSectorNormalizedVector
  rw [← hcInv, hc]

/-- All routine facts about the gauge-one representative of a sector
point, bundled for the final adapter. -/
theorem sectorExitNormalizedPoint_facts
    (A : FiniteProjectiveLineArrangement Line) (sigma : Line → Bool)
    (l a b : Line)
    (htriangle : ¬ ∃ r : RealProjectivePoint,
      A.Incident r l ∧ A.Incident r a ∧ A.Incident r b)
    (q : RealProjectivePoint)
    (hsector : A.projectivePointMemTriangleSector sigma l a b q) :
    let Q := A.sectorExitNormalizedPoint sigma l a b q
    Q ≠ 0 ∧
      A.triangleSectorGauge sigma l a b Q = 1 ∧
      Projectivization.mk ℝ Q (by
        exact A.triangleSectorNormalizedVector_ne_zero sigma l a b
          q.rep_nonzero
          (A.triangleSectorGauge_ne_zero_of_projective
            sigma l a b htriangle q hsector)) = q ∧
      Q ∈ A.arrangementClosedSignConeOn sigma {l, a, b} := by
  have hg := A.triangleSectorGauge_ne_zero_of_projective
    sigma l a b htriangle q hsector
  dsimp only [sectorExitNormalizedPoint]
  refine ⟨A.triangleSectorNormalizedVector_ne_zero sigma l a b
      q.rep_nonzero hg,
    A.triangleSectorGauge_normalizedVector sigma l a b hg, ?_,
    A.triangleSectorNormalizedVector_mem_of_projective
      sigma l a b htriangle q hsector⟩
  exact A.projectivization_mk_triangleSectorNormalizedVector
    sigma l a b q hg

theorem arrangementOrientedEvaluation_sectorExitNormalizedPoint_eq_zero
    (A : FiniteProjectiveLineArrangement Line) (sigma : Line → Bool)
    (l a b n : Line)
    (htriangle : ¬ ∃ r : RealProjectivePoint,
      A.Incident r l ∧ A.Incident r a ∧ A.Incident r b)
    (q : RealProjectivePoint)
    (hsector : A.projectivePointMemTriangleSector sigma l a b q)
    (hqn : A.Incident q n) :
    A.arrangementOrientedEvaluation sigma n
      (A.sectorExitNormalizedPoint sigma l a b q) = 0 := by
  obtain ⟨hQ0, _hQgauge, hmk, _hQsector⟩ :=
    A.sectorExitNormalizedPoint_facts sigma l a b htriangle q hsector
  apply (A.incident_projectivization_mk_iff_orientedEvaluation_eq_zero
    sigma n _ hQ0).1
  simpa only [hmk] using hqn

theorem arrangementOrientedEvaluation_sectorExitNormalizedPoint_pos
    (A : FiniteProjectiveLineArrangement Line) (sigma : Line → Bool)
    (l a b : Line)
    (htriangle : ¬ ∃ r : RealProjectivePoint,
      A.Incident r l ∧ A.Incident r a ∧ A.Incident r b)
    (q : RealProjectivePoint)
    (hsector : A.projectivePointMemTriangleSector sigma l a b q)
    (hql : ¬ A.Incident q l) :
    0 < A.arrangementOrientedEvaluation sigma l
      (A.sectorExitNormalizedPoint sigma l a b q) := by
  simpa only [sectorExitNormalizedPoint, triangleSectorHeight] using
    A.triangleSectorHeight_pos_of_projective
      sigma l a b htriangle q hsector hql

/-- Strict ordering of the three base intersections rules out the
transverse line being either outer support. -/
theorem sectorExit_transverse_ne_outer
    (A : FiniteProjectiveLineArrangement Line) (sigma : Line → Bool)
    {l a b c m : Line}
    (hla : l ≠ a) (hlb : l ≠ b) (hlc : l ≠ c)
    (hV2m : A.Incident (A.intersection l c) m)
    (h12 : A.sectorExitBaseParameter sigma l a b (A.intersection l a) <
      A.sectorExitBaseParameter sigma l a b (A.intersection l c))
    (h23 : A.sectorExitBaseParameter sigma l a b (A.intersection l c) <
      A.sectorExitBaseParameter sigma l a b (A.intersection l b)) :
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

/-- Finish one of the two symmetric outer-exit branches. -/
theorem sectorExit_finish_branch
    (A : FiniteProjectiveLineArrangement Line) (sigma : Line → Bool)
    (l a b m n : Line) (x : RealProjectivePoint)
    {X V Y : Homogeneous3} {h : ℝ}
    (hh0 : 0 < h) (hh1 : h < 1)
    (hY : Y = (1 - h) • V + h • X)
    (hY0 : Y ≠ 0) (hmn : m ≠ n)
    (hYm : A.arrangementOrientedEvaluation sigma m Y = 0)
    (hYn : A.arrangementOrientedEvaluation sigma n Y = 0)
    (hVbase : A.arrangementOrientedEvaluation sigma l V = 0)
    (hVgauge : A.triangleSectorGauge sigma l a b V = 1)
    (hXgauge : A.triangleSectorGauge sigma l a b X = 1)
    (hVsector : V ∈ A.arrangementClosedSignConeOn sigma {l, a, b})
    (hXsector : X ∈ A.arrangementClosedSignConeOn sigma {l, a, b})
    (hXheight : 0 < A.arrangementOrientedEvaluation sigma l X)
    (hxHeight : A.triangleSectorHeight sigma l a b x =
      A.arrangementOrientedEvaluation sigma l X) :
    ∃ y : RealProjectivePoint,
      y ∈ A.vertexSet ∧
      A.sectorExitNormalizedPoint sigma l a b y ∈
        A.arrangementClosedSignConeOn sigma {l, a, b} ∧
      A.Incident y m ∧ A.Incident y n ∧
      ¬ A.Incident y l ∧
      0 < A.triangleSectorHeight sigma l a b y ∧
      A.triangleSectorHeight sigma l a b y <
        A.triangleSectorHeight sigma l a b x := by
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
  have hYgauge : A.triangleSectorGauge sigma l a b Y = 1 := by
    rw [hY]
    exact A.triangleSectorGauge_barycentric_eq_one sigma l a b h
      hVgauge hXgauge
  have hYsector : Y ∈
      A.arrangementClosedSignConeOn sigma {l, a, b} := by
    rw [hY]
    exact A.barycentric_mem_arrangementClosedSignConeOn sigma l a b
      hh0.le hh1.le hVsector hXsector
  have hyNormalized :
      A.sectorExitNormalizedPoint sigma l a b y = Y := by
    apply A.triangleSectorNormalizedVector_eq_of_projectivization_mk
      sigma l a b y hY0 hYgauge
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
    exact (mul_ne_zero hh0.ne' hXheight.ne') hzero
  have hyHeight : A.triangleSectorHeight sigma l a b y =
      h * A.triangleSectorHeight sigma l a b x := by
    calc
      A.triangleSectorHeight sigma l a b y =
          A.arrangementOrientedEvaluation sigma l Y := by
        change A.arrangementOrientedEvaluation sigma l
          (A.sectorExitNormalizedPoint sigma l a b y) = _
        rw [hyNormalized]
      _ = h * A.arrangementOrientedEvaluation sigma l X := hyEval
      _ = h * A.triangleSectorHeight sigma l a b x := by
        rw [hxHeight]
  refine ⟨y, hyVertex, ?_, hym, hyn, hyNotBase, ?_, ?_⟩
  · simpa only [hyNormalized] using hYsector
  · rw [hyHeight]
    rw [hxHeight]
    exact mul_pos hh0 hXheight
  · rw [hyHeight]
    nlinarith

/-- Actual arrangement data produces one of the two homogeneous outer-exit
branches. -/
theorem sectorExit_barycentric_of_projective
    (A : FiniteProjectiveLineArrangement Line) (sigma : Line → Bool)
    (l a b c m : Line) (x : RealProjectivePoint)
    (htriangle : ¬ ∃ r : RealProjectivePoint,
      A.Incident r l ∧ A.Incident r a ∧ A.Incident r b)
    (hla : l ≠ a) (hlb : l ≠ b) (hlc : l ≠ c)
    (hml : m ≠ l) (hmc : m ≠ c)
    (hxsector : A.projectivePointMemTriangleSector sigma l a b x)
    (hV1sector : A.projectivePointMemTriangleSector sigma l a b
      (A.intersection l a))
    (hV2sector : A.projectivePointMemTriangleSector sigma l a b
      (A.intersection l c))
    (hV3sector : A.projectivePointMemTriangleSector sigma l a b
      (A.intersection l b))
    (hxNotBase : ¬ A.Incident x l)
    (hxa : A.Incident x a) (hxb : A.Incident x b)
    (hxc : A.Incident x c)
    (hV2m : A.Incident (A.intersection l c) m)
    (h12 : A.sectorExitBaseParameter sigma l a b (A.intersection l a) <
      A.sectorExitBaseParameter sigma l a b (A.intersection l c))
    (h23 : A.sectorExitBaseParameter sigma l a b (A.intersection l c) <
      A.sectorExitBaseParameter sigma l a b (A.intersection l b)) :
    (∃ h : ℝ, ∃ Y : Homogeneous3,
      0 < h ∧ h < 1 ∧
      Y = (1 - h) •
          A.sectorExitNormalizedPoint sigma l a b (A.intersection l a) +
        h • A.sectorExitNormalizedPoint sigma l a b x ∧
      Y ≠ 0 ∧
      A.arrangementOrientedEvaluation sigma m Y = 0 ∧
      A.arrangementOrientedEvaluation sigma a Y = 0) ∨
    (∃ h : ℝ, ∃ Y : Homogeneous3,
      0 < h ∧ h < 1 ∧
      Y = (1 - h) •
          A.sectorExitNormalizedPoint sigma l a b (A.intersection l b) +
        h • A.sectorExitNormalizedPoint sigma l a b x ∧
      Y ≠ 0 ∧
      A.arrangementOrientedEvaluation sigma m Y = 0 ∧
      A.arrangementOrientedEvaluation sigma b Y = 0) := by
  let v1 := A.intersection l a
  let v2 := A.intersection l c
  let v3 := A.intersection l b
  let X := A.sectorExitNormalizedPoint sigma l a b x
  let V1 := A.sectorExitNormalizedPoint sigma l a b v1
  let V2 := A.sectorExitNormalizedPoint sigma l a b v2
  let V3 := A.sectorExitNormalizedPoint sigma l a b v3
  obtain ⟨hX0, hXgauge, hmkX, hXsector⟩ :=
    A.sectorExitNormalizedPoint_facts sigma l a b htriangle x hxsector
  obtain ⟨_hV10, hV1gauge, _hmkV1, hV1sector'⟩ :=
    A.sectorExitNormalizedPoint_facts sigma l a b htriangle v1 (by
      simpa only [v1] using hV1sector)
  obtain ⟨_hV20, hV2gauge, _hmkV2, _hV2sector'⟩ :=
    A.sectorExitNormalizedPoint_facts sigma l a b htriangle v2 (by
      simpa only [v2] using hV2sector)
  obtain ⟨_hV30, hV3gauge, _hmkV3, hV3sector'⟩ :=
    A.sectorExitNormalizedPoint_facts sigma l a b htriangle v3 (by
      simpa only [v3] using hV3sector)
  have hXheight := A.arrangementOrientedEvaluation_sectorExitNormalizedPoint_pos
    sigma l a b htriangle x hxsector hxNotBase
  have hV1base :=
    A.arrangementOrientedEvaluation_sectorExitNormalizedPoint_eq_zero
      sigma l a b l htriangle v1 (by simpa only [v1] using hV1sector)
      (by simpa only [v1] using A.intersection_incident_left hla)
  have hV2base :=
    A.arrangementOrientedEvaluation_sectorExitNormalizedPoint_eq_zero
      sigma l a b l htriangle v2 (by simpa only [v2] using hV2sector)
      (by simpa only [v2] using A.intersection_incident_left hlc)
  have hVm :=
    A.arrangementOrientedEvaluation_sectorExitNormalizedPoint_eq_zero
      sigma l a b m htriangle v2 (by simpa only [v2] using hV2sector)
      (by simpa only [v2] using hV2m)
  obtain ⟨scale, delta, hscale, hform⟩ :=
    A.exists_sectorExit_middle_normalForm sigma l a b m htriangle
      (X := X) (V := V2) hXheight.ne' hXgauge hV2base hV2gauge hVm hml
  let coord := A.sectorExitCoordinateEquiv sigma l a b X
    htriangle hXheight.ne'
  have hcoordX : coord X = homogeneousLift (triangleExitTopPoint 0) := by
    simpa only [coord] using
      A.sectorExitCoordinateMap_apex sigma l a b hXheight.ne' hXgauge
  have hdelta : delta ≠ 0 := by
    apply A.sectorExit_delta_ne_zero sigma hmc hX0
      (by simpa only [X] using hmkX) hxNotBase hxc
      (by simpa only [v2] using A.intersection_incident_left hlc)
      (by simpa only [v2] using A.intersection_incident_right hlc)
      (by simpa only [v2] using hV2m) coord hcoordX
      (A.sectorExitBaseParameter sigma l a b v2) scale delta
    simpa only [coord, V2, v2, sectorExitBaseParameter] using hform
  let t1 := A.sectorExitBaseParameter sigma l a b v1
  let t2 := A.sectorExitBaseParameter sigma l a b v2
  let t3 := A.sectorExitBaseParameter sigma l a b v3
  have ht12 : t1 < t2 := by simpa only [t1, t2, v1, v2] using h12
  have ht23 : t2 < t3 := by simpa only [t2, t3, v2, v3] using h23
  have hcoordV1 : coord V1 =
      homogeneousLift (triangleExitBasePoint t1) := by
    simpa only [coord, V1, v1, t1, sectorExitBaseParameter] using
      A.sectorExitCoordinateMap_base sigma l a b
        (X := X) hV1base hV1gauge
  have hV3base :=
    A.arrangementOrientedEvaluation_sectorExitNormalizedPoint_eq_zero
      sigma l a b l htriangle v3 (by simpa only [v3] using hV3sector)
      (by simpa only [v3] using A.intersection_incident_left hlb)
  have hcoordV3 : coord V3 =
      homogeneousLift (triangleExitBasePoint t3) := by
    simpa only [coord, V3, v3, t3, sectorExitBaseParameter] using
      A.sectorExitCoordinateMap_base sigma l a b
        (X := X) hV3base hV3gauge
  have hform' : ∀ Z, A.arrangementOrientedEvaluation sigma m Z =
      scale * (coord Z ⬝ᵥ triangleExitMiddleCovector t2 delta) := by
    simpa only [coord, V2, v2, t2, sectorExitBaseParameter] using hform
  let middle := scale⁻¹ • A.arrangementOrientedEvaluation sigma m
  have hmiddle : ∀ Z, middle Z =
      coord Z ⬝ᵥ triangleExitMiddleCovector t2 delta := by
    intro Z
    simp only [middle, LinearMap.smul_apply, smul_eq_mul, hform' Z]
    rw [← mul_assoc, inv_mul_cancel₀ hscale, one_mul]
  have hleftV :=
    A.arrangementOrientedEvaluation_sectorExitNormalizedPoint_eq_zero
      sigma l a b a htriangle v1 (by simpa only [v1] using hV1sector)
      (by simpa only [v1] using A.intersection_incident_right hla)
  have hleftX :=
    A.arrangementOrientedEvaluation_sectorExitNormalizedPoint_eq_zero
      sigma l a b a htriangle x hxsector hxa
  have hrightV :=
    A.arrangementOrientedEvaluation_sectorExitNormalizedPoint_eq_zero
      sigma l a b b htriangle v3 (by simpa only [v3] using hV3sector)
      (by simpa only [v3] using A.intersection_incident_right hlb)
  have hrightX :=
    A.arrangementOrientedEvaluation_sectorExitNormalizedPoint_eq_zero
      sigma l a b b htriangle x hxsector hxb
  rcases triangleExit_transportedBarycentric coord middle
      (A.arrangementOrientedEvaluation sigma a)
      (A.arrangementOrientedEvaluation sigma b)
      t1 t2 t3 delta ht12 ht23 hdelta hcoordX hcoordV1 hcoordV3
      hmiddle hleftV hleftX hrightV hrightX with hleft | hright
  · rcases hleft with ⟨h, hh0, hh1, hrest⟩
    dsimp only at hrest
    rcases hrest with ⟨hY0, hYm', hYa, _hcoordY⟩
    have hYm : A.arrangementOrientedEvaluation sigma m
        ((1 - h) • V1 + h • X) = 0 := by
      simp only [middle, LinearMap.smul_apply, smul_eq_mul] at hYm'
      exact (mul_eq_zero.mp hYm').resolve_left (inv_ne_zero hscale)
    left
    refine ⟨h, (1 - h) • V1 + h • X, hh0, hh1, ?_, hY0, hYm, hYa⟩
    simp only [V1, X, v1]
  · rcases hright with ⟨h, hh0, hh1, hrest⟩
    dsimp only at hrest
    rcases hrest with ⟨hY0, hYm', hYb, _hcoordY⟩
    have hYm : A.arrangementOrientedEvaluation sigma m
        ((1 - h) • V3 + h • X) = 0 := by
      simp only [middle, LinearMap.smul_apply, smul_eq_mul] at hYm'
      exact (mul_eq_zero.mp hYm').resolve_left (inv_ne_zero hscale)
    right
    refine ⟨h, (1 - h) • V3 + h • X, hh0, hh1, ?_, hY0, hYm, hYb⟩
    simp only [V3, X, v3]

/-- Actual sector exit.  A transverse line through the strictly middle base
intersection meets one outer support at an arrangement vertex in the same
closed triangle sector and at strictly smaller positive normalized height. -/
theorem sectorExit_of_projective
    (A : FiniteProjectiveLineArrangement Line) (sigma : Line → Bool)
    (l a b c m : Line) (x : RealProjectivePoint)
    (htriangle : ¬ ∃ r : RealProjectivePoint,
      A.Incident r l ∧ A.Incident r a ∧ A.Incident r b)
    (hla : l ≠ a) (hlb : l ≠ b) (hlc : l ≠ c)
    (hml : m ≠ l) (hmc : m ≠ c)
    (hxsector : A.projectivePointMemTriangleSector sigma l a b x)
    (hV1sector : A.projectivePointMemTriangleSector sigma l a b
      (A.intersection l a))
    (hV2sector : A.projectivePointMemTriangleSector sigma l a b
      (A.intersection l c))
    (hV3sector : A.projectivePointMemTriangleSector sigma l a b
      (A.intersection l b))
    (hxNotBase : ¬ A.Incident x l)
    (hxa : A.Incident x a) (hxb : A.Incident x b)
    (hxc : A.Incident x c)
    (hV2m : A.Incident (A.intersection l c) m)
    (h12 : A.sectorExitBaseParameter sigma l a b (A.intersection l a) <
      A.sectorExitBaseParameter sigma l a b (A.intersection l c))
    (h23 : A.sectorExitBaseParameter sigma l a b (A.intersection l c) <
      A.sectorExitBaseParameter sigma l a b (A.intersection l b)) :
    ∃ y : RealProjectivePoint,
      y ∈ A.vertexSet ∧
      A.sectorExitNormalizedPoint sigma l a b y ∈
        A.arrangementClosedSignConeOn sigma {l, a, b} ∧
      A.Incident y m ∧
      (A.Incident y a ∨ A.Incident y b) ∧
      ¬ A.Incident y l ∧
      0 < A.triangleSectorHeight sigma l a b y ∧
      A.triangleSectorHeight sigma l a b y <
        A.triangleSectorHeight sigma l a b x := by
  let v1 := A.intersection l a
  let v3 := A.intersection l b
  let X := A.sectorExitNormalizedPoint sigma l a b x
  let V1 := A.sectorExitNormalizedPoint sigma l a b v1
  let V3 := A.sectorExitNormalizedPoint sigma l a b v3
  have houter := A.sectorExit_transverse_ne_outer sigma hla hlb hlc
    hV2m h12 h23
  have hexit := A.sectorExit_barycentric_of_projective
    sigma l a b c m x htriangle
    hla hlb hlc hml hmc hxsector hV1sector hV2sector hV3sector
    hxNotBase hxa hxb hxc hV2m h12 h23
  obtain ⟨_hX0, hXgauge, _hmkX, hXsector⟩ :=
    A.sectorExitNormalizedPoint_facts sigma l a b htriangle x hxsector
  obtain ⟨_hV10, hV1gauge, _hmkV1, hV1sector'⟩ :=
    A.sectorExitNormalizedPoint_facts sigma l a b htriangle v1 (by
      simpa only [v1] using hV1sector)
  obtain ⟨_hV30, hV3gauge, _hmkV3, hV3sector'⟩ :=
    A.sectorExitNormalizedPoint_facts sigma l a b htriangle v3 (by
      simpa only [v3] using hV3sector)
  have hXheight := A.arrangementOrientedEvaluation_sectorExitNormalizedPoint_pos
    sigma l a b htriangle x hxsector hxNotBase
  have hxHeight : A.triangleSectorHeight sigma l a b x =
      A.arrangementOrientedEvaluation sigma l X := by
    rfl
  have hV1base :=
    A.arrangementOrientedEvaluation_sectorExitNormalizedPoint_eq_zero
      sigma l a b l htriangle v1 (by simpa only [v1] using hV1sector)
      (by simpa only [v1] using A.intersection_incident_left hla)
  have hV3base :=
    A.arrangementOrientedEvaluation_sectorExitNormalizedPoint_eq_zero
      sigma l a b l htriangle v3 (by simpa only [v3] using hV3sector)
      (by simpa only [v3] using A.intersection_incident_left hlb)
  rcases hexit with hleft | hright
  · rcases hleft with ⟨h, Y, hh0, hh1, hY, hY0, hYm, hYa⟩
    obtain ⟨y, hyVertex, hySector, hym, hya, hyNotBase, hyPos, hyLt⟩ :=
      A.sectorExit_finish_branch sigma l a b m a x hh0 hh1
        (by simpa only [V1, X, v1] using hY) hY0 houter.1 hYm hYa
        hV1base hV1gauge hXgauge hV1sector' hXsector hXheight hxHeight
    exact ⟨y, hyVertex, hySector, hym, Or.inl hya,
      hyNotBase, hyPos, hyLt⟩
  · rcases hright with ⟨h, Y, hh0, hh1, hY, hY0, hYm, hYb⟩
    obtain ⟨y, hyVertex, hySector, hym, hyb, hyNotBase, hyPos, hyLt⟩ :=
      A.sectorExit_finish_branch sigma l a b m b x hh0 hh1
        (by simpa only [V3, X, v3] using hY) hY0 houter.2 hYm hYb
        hV3base hV3gauge hXgauge hV3sector' hXsector hXheight hxHeight
    exact ⟨y, hyVertex, hySector, hym, Or.inr hyb,
      hyNotBase, hyPos, hyLt⟩

/-- Compatibility wrapper for callers which already chose the positive
canonical representatives of all four sector points. -/
theorem sectorExit
    (A : FiniteProjectiveLineArrangement Line) (sigma : Line → Bool)
    (l a b c m : Line) (x : RealProjectivePoint)
    (htriangle : ¬ ∃ r : RealProjectivePoint,
      A.Incident r l ∧ A.Incident r a ∧ A.Incident r b)
    (hla : l ≠ a) (hlb : l ≠ b) (hlc : l ≠ c)
    (hml : m ≠ l) (hmc : m ≠ c)
    (hxsector : x.rep ∈
      A.arrangementClosedSignConeOn sigma {l, a, b})
    (hV1sector : (A.intersection l a).rep ∈
      A.arrangementClosedSignConeOn sigma {l, a, b})
    (hV2sector : (A.intersection l c).rep ∈
      A.arrangementClosedSignConeOn sigma {l, a, b})
    (hV3sector : (A.intersection l b).rep ∈
      A.arrangementClosedSignConeOn sigma {l, a, b})
    (hxNotBase : ¬ A.Incident x l)
    (hxa : A.Incident x a) (hxb : A.Incident x b)
    (hxc : A.Incident x c)
    (hV2m : A.Incident (A.intersection l c) m)
    (h12 : A.sectorExitBaseParameter sigma l a b (A.intersection l a) <
      A.sectorExitBaseParameter sigma l a b (A.intersection l c))
    (h23 : A.sectorExitBaseParameter sigma l a b (A.intersection l c) <
      A.sectorExitBaseParameter sigma l a b (A.intersection l b)) :
    ∃ y : RealProjectivePoint,
      y ∈ A.vertexSet ∧
      A.sectorExitNormalizedPoint sigma l a b y ∈
        A.arrangementClosedSignConeOn sigma {l, a, b} ∧
      A.Incident y m ∧
      (A.Incident y a ∨ A.Incident y b) ∧
      ¬ A.Incident y l ∧
      0 < A.triangleSectorHeight sigma l a b y ∧
      A.triangleSectorHeight sigma l a b y <
        A.triangleSectorHeight sigma l a b x := by
  exact A.sectorExit_of_projective sigma l a b c m x htriangle
    hla hlb hlc hml hmc (Or.inl hxsector) (Or.inl hV1sector)
    (Or.inl hV2sector) (Or.inl hV3sector) hxNotBase
    hxa hxb hxc hV2m h12 h23

/-- Compatibility form of the barycentric witness with already-positive
canonical representatives. -/
theorem sectorExit_barycentric
    (A : FiniteProjectiveLineArrangement Line) (sigma : Line → Bool)
    (l a b c m : Line) (x : RealProjectivePoint)
    (htriangle : ¬ ∃ r : RealProjectivePoint,
      A.Incident r l ∧ A.Incident r a ∧ A.Incident r b)
    (hla : l ≠ a) (hlb : l ≠ b) (hlc : l ≠ c)
    (hml : m ≠ l) (hmc : m ≠ c)
    (hxsector : x.rep ∈
      A.arrangementClosedSignConeOn sigma {l, a, b})
    (hV1sector : (A.intersection l a).rep ∈
      A.arrangementClosedSignConeOn sigma {l, a, b})
    (hV2sector : (A.intersection l c).rep ∈
      A.arrangementClosedSignConeOn sigma {l, a, b})
    (hV3sector : (A.intersection l b).rep ∈
      A.arrangementClosedSignConeOn sigma {l, a, b})
    (hxNotBase : ¬ A.Incident x l)
    (hxa : A.Incident x a) (hxb : A.Incident x b)
    (hxc : A.Incident x c)
    (hV2m : A.Incident (A.intersection l c) m)
    (h12 : A.sectorExitBaseParameter sigma l a b (A.intersection l a) <
      A.sectorExitBaseParameter sigma l a b (A.intersection l c))
    (h23 : A.sectorExitBaseParameter sigma l a b (A.intersection l c) <
      A.sectorExitBaseParameter sigma l a b (A.intersection l b)) :
    (∃ h : ℝ, ∃ Y : Homogeneous3,
      0 < h ∧ h < 1 ∧
      Y = (1 - h) •
          A.sectorExitNormalizedPoint sigma l a b (A.intersection l a) +
        h • A.sectorExitNormalizedPoint sigma l a b x ∧
      Y ≠ 0 ∧
      A.arrangementOrientedEvaluation sigma m Y = 0 ∧
      A.arrangementOrientedEvaluation sigma a Y = 0) ∨
    (∃ h : ℝ, ∃ Y : Homogeneous3,
      0 < h ∧ h < 1 ∧
      Y = (1 - h) •
          A.sectorExitNormalizedPoint sigma l a b (A.intersection l b) +
        h • A.sectorExitNormalizedPoint sigma l a b x ∧
      Y ≠ 0 ∧
      A.arrangementOrientedEvaluation sigma m Y = 0 ∧
      A.arrangementOrientedEvaluation sigma b Y = 0) := by
  exact A.sectorExit_barycentric_of_projective sigma l a b c m x htriangle
    hla hlb hlc hml hmc (Or.inl hxsector) (Or.inl hV1sector)
    (Or.inl hV2sector) (Or.inl hV3sector) hxNotBase
    hxa hxb hxc hV2m h12 h23

end FiniteProjectiveLineArrangement

end Erdos506.Incidence
