import Erdos506.V1.ElevenFiveLineHarmonicCap
import Erdos506.V1.ElevenFiveFourStarNormalTrace
import Erdos506.V3.CircleInversion

/-!
# Projective parameters for inversion of a line through the pivot

For a line written as `p + tD`, inversion about `p` sends its finite
nonzero parameter to `1 / (‖D‖² t)`.  Homogeneously this is the projectivity
represented by `[[0,1],[‖D‖²,0]]`.  The lemmas below make that elementary
calculation available before one chooses a four-star normal frame.
-/

namespace Erdos506.V1

open Erdos506.Incidence
open Erdos506.Finite
open Erdos506.V3
open Erdos506.V4
open Matrix
open scoped LinearAlgebra.Projectivization

noncomputable local instance inversionLineDecidableEqRP1 :
    DecidableEq RealProjectiveOnePoint := Classical.decEq _

/-- Squared direction length is homogeneous of degree two. -/
theorem directionSq_smul
    (D : Point2) (t : ℝ) :
    directionSq (t • D) = t ^ 2 * directionSq D := by
  simp [directionSq]
  ring

/-- The squared distance from the pivot along the affine line is the
expected quadratic function of its affine parameter. -/
theorem dist_sq_affineParamPoint_pivot
    (p D : Point2) (t : ℝ) :
    dist (affineParamPoint p D t) p ^ 2 = t ^ 2 * directionSq D := by
  rw [← directionSq_sub_eq_dist_sq]
  change directionSq (affineParamPoint p D t - p) = _
  have hsub : affineParamPoint p D t - p = t • D := by
    simp [affineParamPoint]
  rw [hsub, directionSq_smul]

/-- The elementary inversion formula on a line through its centre.  The
nonzero assumptions are precisely those needed to stay away from the pivot
and to divide by the line's squared direction. -/
theorem inversion_affineParamPoint_through_pivot
    (p D : Point2) (t : ℝ) (hD : D ≠ 0) (ht : t ≠ 0) :
    EuclideanGeometry.inversion p 1 (affineParamPoint p D t) =
      affineParamPoint p D ((directionSq D * t)⁻¹) := by
  have hDsq : directionSq D ≠ 0 := by
    intro hzero
    exact hD ((directionSq_eq_zero_iff D).mp hzero)
  have hdistSq : dist (affineParamPoint p D t) p ^ 2 ≠ 0 := by
    rw [dist_sq_affineParamPoint_pivot]
    exact mul_ne_zero (pow_ne_zero 2 ht) hDsq
  have hdist : dist (affineParamPoint p D t) p ≠ 0 := by
    intro hzero
    apply hdistSq
    rw [hzero]
    norm_num
  have hinversion (i : Fin 2) :
      EuclideanGeometry.inversion p 1 (affineParamPoint p D t) i =
        p i + (affineParamPoint p D t i - p i) /
          dist (affineParamPoint p D t) p ^ 2 := by
    simp [EuclideanGeometry.inversion]
    field_simp [hdist]
    ring
  ext i
  rw [hinversion i, affineParamPoint_apply,
    dist_sq_affineParamPoint_pivot]
  simp only [affineParamPoint_apply]
  field_simp [hDsq, ht]
  ring

/-- The homogeneous matrix of the inversion parameter map
`[t:1] ↦ [1:k t]`, whose affine coordinate is `1 / (k t)`. -/
def pivotLineInversionParameterMatrix (k : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  ![![0, 1], ![k, 0]]

@[simp] theorem pivotLineInversionParameterMatrix_det (k : ℝ) :
    (pivotLineInversionParameterMatrix k).det = -k := by
  simp [pivotLineInversionParameterMatrix, Matrix.det_fin_two]

/-- The parameter inversion is a genuine projectivity whenever the line
direction is nonzero. -/
noncomputable def pivotLineInversionParameterGL (k : ℝ) (hk : k ≠ 0) :
    GL (Fin 2) ℝ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero
    (pivotLineInversionParameterMatrix k) (by
      rw [pivotLineInversionParameterMatrix_det]
      exact neg_ne_zero.mpr hk)

theorem pivotLineInversionParameterGL_smul_vector
    (k t : ℝ) (hk : k ≠ 0) :
    pivotLineInversionParameterGL k hk • realProjectiveAffineVector t =
      ![1, k * t] := by
  change pivotLineInversionParameterMatrix k *ᵥ
      realProjectiveAffineVector t = _
  funext i
  fin_cases i <;>
    simp [pivotLineInversionParameterMatrix, Matrix.mulVec,
      dotProduct, Fin.sum_univ_two, realProjectiveAffineVector]
  all_goals ring

/-- On finite nonzero affine coordinates, the `GL₂` action is exactly the
reciprocal affine parameter prescribed by inversion. -/
theorem pivotLineInversionParameterGL_smul_affinePoint
    (k t : ℝ) (hk : k ≠ 0) (ht : t ≠ 0) :
    pivotLineInversionParameterGL k hk • realProjectiveAffinePoint t =
      realProjectiveAffinePoint ((k * t)⁻¹) := by
  unfold realProjectiveAffinePoint
  rw [Projectivization.smul_mk]
  apply (realProjective_mk_eq_mk_iff_bracket_eq_zero
    ((smul_ne_zero_iff_ne (pivotLineInversionParameterGL k hk)).mpr
      (realProjectiveAffineVector_ne_zero t))
    (realProjectiveAffineVector_ne_zero _)).mpr
  rw [pivotLineInversionParameterGL_smul_vector]
  have hkt : k * t ≠ 0 := mul_ne_zero hk ht
  simp [realProjectiveBracket, realProjectiveAffineVector]
  field_simp [hkt] <;> ring

/-- Combining the Euclidean formula with the homogeneous parameter change:
the affine parameter of an inverted point on the same directed line is the
`GL₂` image of its original parameter, with `k = ‖D‖²`. -/
theorem inversion_affineParamPoint_projective_parameter
    (p D : Point2) (t : ℝ) (hD : D ≠ 0) (ht : t ≠ 0) :
    EuclideanGeometry.inversion p 1 (affineParamPoint p D t) =
      affineParamPoint p D
        ((directionSq D * t)⁻¹) ∧
    pivotLineInversionParameterGL (directionSq D)
        (by
          intro hzero
          exact hD ((directionSq_eq_zero_iff D).mp hzero)) •
      realProjectiveAffinePoint t =
        realProjectiveAffinePoint ((directionSq D * t)⁻¹) := by
  constructor
  · exact inversion_affineParamPoint_through_pivot p D t hD ht
  · exact pivotLineInversionParameterGL_smul_affinePoint
      (directionSq D) t
      (by
        intro hzero
        exact hD ((directionSq_eq_zero_iff D).mp hzero)) ht

/-- In a shared affine coordinate `s` on the original line, inversion about
the point with coordinate `a` has homogeneous form
`[s:1] ↦ [1:k(s-a)]`. -/
def pivotLineInversionShiftMatrix (k a : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  ![![0, 1], ![k, -k * a]]

@[simp] theorem pivotLineInversionShiftMatrix_det (k a : ℝ) :
    (pivotLineInversionShiftMatrix k a).det = -k := by
  simp [pivotLineInversionShiftMatrix, Matrix.det_fin_two]

noncomputable def pivotLineInversionShiftGL (k a : ℝ) (hk : k ≠ 0) :
    GL (Fin 2) ℝ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero
    (pivotLineInversionShiftMatrix k a) (by
      rw [pivotLineInversionShiftMatrix_det]
      exact neg_ne_zero.mpr hk)

theorem pivotLineInversionShiftGL_smul_vector
    (k a s : ℝ) (hk : k ≠ 0) :
    pivotLineInversionShiftGL k a hk • realProjectiveAffineVector s =
      ![1, k * (s - a)] := by
  change pivotLineInversionShiftMatrix k a *ᵥ
      realProjectiveAffineVector s = _
  funext i
  fin_cases i <;>
    simp [pivotLineInversionShiftMatrix, Matrix.mulVec,
      dotProduct, Fin.sum_univ_two, realProjectiveAffineVector]
  all_goals ring

/-- The shared original-line parameter is carried to the finite parameter
on the inverted line by one explicitly displayed `GL₂` element. -/
theorem pivotLineInversionShiftGL_smul_affinePoint
    (k a s : ℝ) (hk : k ≠ 0) (hsa : s - a ≠ 0) :
    pivotLineInversionShiftGL k a hk • realProjectiveAffinePoint s =
      realProjectiveAffinePoint ((k * (s - a))⁻¹) := by
  unfold realProjectiveAffinePoint
  rw [Projectivization.smul_mk]
  apply (realProjective_mk_eq_mk_iff_bracket_eq_zero
    ((smul_ne_zero_iff_ne (pivotLineInversionShiftGL k a hk)).mpr
      (realProjectiveAffineVector_ne_zero s))
    (realProjectiveAffineVector_ne_zero _)).mpr
  rw [pivotLineInversionShiftGL_smul_vector]
  have hdenom : k * (s - a) ≠ 0 := mul_ne_zero hk hsa
  simp [realProjectiveBracket, realProjectiveAffineVector]
  field_simp [hdenom] <;> ring

/-- Coordinate form of inversion when the original line has one fixed
affine chart.  This is the compatibility needed for one line trace shared
by all possible deleted pivots. -/
theorem inversion_affineParamPoint_shared_parameter
    (B D : Point2) (a s : ℝ) (hD : D ≠ 0) (hsa : s - a ≠ 0) :
    EuclideanGeometry.inversion (affineParamPoint B D a) 1
      (affineParamPoint B D s) =
      affineParamPoint (affineParamPoint B D a) D
        ((directionSq D * (s - a))⁻¹) := by
  have hsub : affineParamPoint B D s =
      affineParamPoint (affineParamPoint B D a) D (s - a) := by
    ext i
    simp [affineParamPoint_apply]
    ring
  rw [hsub]
  exact inversion_affineParamPoint_through_pivot
    (affineParamPoint B D a) D (s - a) hD hsa

/-- The projective half of the preceding shared-chart formula. -/
theorem inversion_affineParamPoint_shared_projective_parameter
    (B D : Point2) (a s : ℝ) (hD : D ≠ 0) (hsa : s - a ≠ 0) :
    EuclideanGeometry.inversion (affineParamPoint B D a) 1
      (affineParamPoint B D s) =
      affineParamPoint (affineParamPoint B D a) D
        ((directionSq D * (s - a))⁻¹) ∧
    pivotLineInversionShiftGL (directionSq D) a
        (by
          intro hzero
          exact hD ((directionSq_eq_zero_iff D).mp hzero)) •
      realProjectiveAffinePoint s =
        realProjectiveAffinePoint ((directionSq D * (s - a))⁻¹) := by
  constructor
  · exact inversion_affineParamPoint_shared_parameter B D a s hD hsa
  · exact pivotLineInversionShiftGL_smul_affinePoint
      (directionSq D) a s
      (by
        intro hzero
        exact hD ((directionSq_eq_zero_iff D).mp hzero)) hsa

/-! ## Exact normal traces on the inverted base -/

/-- For the base line produced by deleting a point of an actual five-line,
the unconditional four-star survivor theorem supplies a relabeling whose
normal-coordinate trace is exactly the corresponding normal harmonic trace.
This is the finite/projective part of the five-line comparison; it makes no
claim yet relating that inverse coordinate to a chosen parameter of the
original line. -/
theorem elevenFive944LineBase_exists_relabelledBaseNormalTrace_eq_normalTrace
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    (cfg : Configuration Point) (hcard : Fintype.card Point = 11)
    (p : Point) (hpivot : p ∈ elevenFive944Pivots (blockSystem cfg))
    (b : GeometricBlock cfg)
    (hb : b ∈ (blockSystem cfg).lineBlocksOfSize 5)
    (hp : p ∈ geometricBlockSupport cfg b) :
    ∃ σ : Equiv.Perm FourStarVertex,
      let H := elevenFive944PivotFourStar cfg hcard p hpivot
      let r := elevenFive944LineBaseIndex cfg hcard p hpivot b hb hp
      let N := ((H.toProjectiveSkeleton H.geometricBoundary).relabel σ).toNormalForm
      N.determinants = fourStarNormalSurvivor ∧
        H.relabelledBaseNormalTrace σ N (σ r) =
          fourStarNormalTraceParameterSet (σ r) := by
  let H := elevenFive944PivotFourStar cfg hcard p hpivot
  let r := elevenFive944LineBaseIndex cfg hcard p hpivot b hb hp
  obtain ⟨σ, _, hdet, htraces⟩ :=
    H.exists_relabelledBaseNormalTrace_eq_normalTrace
  let N := ((H.toProjectiveSkeleton H.geometricBoundary).relabel σ).toNormalForm
  refine ⟨σ, ?_⟩
  change N.determinants = fourStarNormalSurvivor ∧
    H.relabelledBaseNormalTrace σ N (σ r) =
      fourStarNormalTraceParameterSet (σ r)
  exact ⟨hdet, htraces (σ r)⟩

end Erdos506.V1
