import Erdos506.Incidence.RealCircleProjectiveParametrization
import Erdos506.Incidence.RealProjectiveHarmonic
import Mathlib.Geometry.Euclidean.Inversion.Basic

/-!
# Harmonic transport through inversion of a circle through the centre

For a proper circle parametrised by homogeneous vectors `w,u : ℝ²`, invert
the point parametrised by `u` about the point parametrised by `w`.  The image
lies on a fixed affine line, with affine parameter

`(w ⬝ u) / [w,u]`.

The two homogeneous coordinates `w ⬝ u` and `[w,u]` are obtained from `u`
by an invertible two-by-two matrix depending only on `w`.  Consequently the
four-point harmonic relation is transported exactly by this inversion chart.
-/

namespace Erdos506.Incidence

open Erdos506.V3
open Erdos506.V4
open Matrix
open scoped LinearAlgebra.Projectivization

/-! ## The projective slope chart -/

/-- The Euclidean dot product on the concrete two-coordinate representatives
of the real projective line. -/
def realProjectiveDot
    (u v : RealProjectiveLineVector) : ℝ :=
  u 0 * v 0 + u 1 * v 1

/-- The matrix which sends `u` to the homogeneous affine coordinate pair
`(w ⬝ u, [w,u])`. -/
def properCirclePivotSlopeMatrix
    (w : RealProjectiveLineVector) : Matrix (Fin 2) (Fin 2) ℝ :=
  ![![w 0, w 1], ![-w 1, w 0]]

@[simp] theorem properCirclePivotSlopeMatrix_det
    (w : RealProjectiveLineVector) :
    (properCirclePivotSlopeMatrix w).det = realProjectiveLineNormSq w := by
  simp [properCirclePivotSlopeMatrix, Matrix.det_fin_two,
    realProjectiveLineNormSq]
  ring

/-- The projectivity underlying the slope chart based at `w`. -/
noncomputable def properCirclePivotSlopeGL
    (w : RealProjectiveLineVector) (hw : w ≠ 0) : GL (Fin 2) ℝ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero
    (properCirclePivotSlopeMatrix w)
    (by
      rw [properCirclePivotSlopeMatrix_det]
      exact (realProjectiveLineNormSq_pos hw).ne')

theorem properCirclePivotSlopeGL_smul_vector
    (w : RealProjectiveLineVector) (hw : w ≠ 0)
    (u : RealProjectiveLineVector) :
    properCirclePivotSlopeGL w hw • u =
      ![realProjectiveDot w u, realProjectiveBracket w u] := by
  change properCirclePivotSlopeMatrix w *ᵥ u = _
  funext i
  fin_cases i
  · simp [properCirclePivotSlopeMatrix, Matrix.mulVec, dotProduct,
      Fin.sum_univ_two, realProjectiveDot]
  · simp [properCirclePivotSlopeMatrix, Matrix.mulVec, dotProduct,
      Fin.sum_univ_two, realProjectiveBracket]
    ring

/-- The standard finite affine point `[t:1]` of `RP¹`. -/
def realProjectiveAffineVector (t : ℝ) : RealProjectiveLineVector :=
  ![t, 1]

theorem realProjectiveAffineVector_ne_zero (t : ℝ) :
    realProjectiveAffineVector t ≠ 0 := by
  intro hzero
  have hone := congrFun hzero (1 : Fin 2)
  simp [realProjectiveAffineVector] at hone

/-- The affine chart `t ↦ [t:1]` of the real projective line. -/
noncomputable def realProjectiveAffinePoint (t : ℝ) : RealProjectiveOnePoint :=
  Projectivization.mk ℝ (realProjectiveAffineVector t)
    (realProjectiveAffineVector_ne_zero t)

/-- The projective slope map sends `[u]` to the affine point whose coordinate
is `(w ⬝ u) / [w,u]`, whenever `u` is not projectively equal to `w`. -/
theorem properCirclePivotSlope_projective_eq_affine
    {w u : RealProjectiveLineVector}
    (hw : w ≠ 0) (hu : u ≠ 0)
    (hwu : realProjectiveBracket w u ≠ 0) :
    properCirclePivotSlopeGL w hw • Projectivization.mk ℝ u hu =
      realProjectiveAffinePoint
        (realProjectiveDot w u / realProjectiveBracket w u) := by
  unfold realProjectiveAffinePoint
  rw [Projectivization.smul_mk]
  apply (realProjective_mk_eq_mk_iff_bracket_eq_zero
    ((smul_ne_zero_iff_ne (properCirclePivotSlopeGL w hw)).mpr hu)
    (realProjectiveAffineVector_ne_zero _)).mpr
  rw [properCirclePivotSlopeGL_smul_vector]
  simp only [realProjectiveBracket, realProjectiveAffineVector,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  have hcancel :
      (w 0 * u 1 - w 1 * u 0) *
          (realProjectiveDot w u / (w 0 * u 1 - w 1 * u 0)) =
        realProjectiveDot w u := by
    exact mul_div_cancel₀ _ hwu
  rw [hcancel]
  ring

/-- `GL₂(ℝ)`-invariance of harmonicity as an equivalence. -/
theorem realProjectiveHarmonic_gl_smul_iff
    (g : GL (Fin 2) ℝ) {P Q R S : RealProjectiveOnePoint} :
    RealProjectiveHarmonic (g • P) (g • Q) (g • R) (g • S) ↔
      RealProjectiveHarmonic P Q R S := by
  constructor
  · intro h
    have hback := realProjectiveHarmonic_gl_smul g⁻¹ h
    simpa [smul_smul] using hback
  · exact realProjectiveHarmonic_gl_smul g

/-- Four circle parameters are harmonic exactly when their four finite slope
coordinates relative to a fifth parameter `w` are harmonic. -/
theorem properCirclePivotSlope_harmonic_iff
    {w u₀ u₁ u₂ u₃ : RealProjectiveLineVector}
    (hw : w ≠ 0)
    (hu₀ : u₀ ≠ 0) (hu₁ : u₁ ≠ 0)
    (hu₂ : u₂ ≠ 0) (hu₃ : u₃ ≠ 0)
    (hwu₀ : realProjectiveBracket w u₀ ≠ 0)
    (hwu₁ : realProjectiveBracket w u₁ ≠ 0)
    (hwu₂ : realProjectiveBracket w u₂ ≠ 0)
    (hwu₃ : realProjectiveBracket w u₃ ≠ 0) :
    RealProjectiveHarmonic
        (Projectivization.mk ℝ u₀ hu₀)
        (Projectivization.mk ℝ u₁ hu₁)
        (Projectivization.mk ℝ u₂ hu₂)
        (Projectivization.mk ℝ u₃ hu₃) ↔
      RealProjectiveHarmonic
        (realProjectiveAffinePoint
          (realProjectiveDot w u₀ / realProjectiveBracket w u₀))
        (realProjectiveAffinePoint
          (realProjectiveDot w u₁ / realProjectiveBracket w u₁))
        (realProjectiveAffinePoint
          (realProjectiveDot w u₂ / realProjectiveBracket w u₂))
        (realProjectiveAffinePoint
          (realProjectiveDot w u₃ / realProjectiveBracket w u₃)) := by
  rw [← properCirclePivotSlope_projective_eq_affine hw hu₀ hwu₀,
    ← properCirclePivotSlope_projective_eq_affine hw hu₁ hwu₁,
    ← properCirclePivotSlope_projective_eq_affine hw hu₂ hwu₂,
    ← properCirclePivotSlope_projective_eq_affine hw hu₃ hwu₃]
  exact (realProjectiveHarmonic_gl_smul_iff
    (properCirclePivotSlopeGL w hw)).symm

/-! ## The affine line obtained by inversion -/

/-- The normalized double-angle unit direction belonging to `w`. -/
noncomputable def properCircleUnitDirection
    (w : RealProjectiveLineVector) : Point2 :=
  pointOfCoords
    ((w 0 ^ 2 - w 1 ^ 2) / realProjectiveLineNormSq w)
    ((2 * w 0 * w 1) / realProjectiveLineNormSq w)

@[simp] theorem properCircleUnitDirection_apply_zero
    (w : RealProjectiveLineVector) :
    properCircleUnitDirection w 0 =
      (w 0 ^ 2 - w 1 ^ 2) / realProjectiveLineNormSq w := by
  simp [properCircleUnitDirection]

@[simp] theorem properCircleUnitDirection_apply_one
    (w : RealProjectiveLineVector) :
    properCircleUnitDirection w 1 =
      (2 * w 0 * w 1) / realProjectiveLineNormSq w := by
  simp [properCircleUnitDirection]

/-- Counterclockwise quarter-turn in the affine plane. -/
noncomputable def pointQuarterTurn (v : Point2) : Point2 :=
  pointOfCoords (-v 1) (v 0)

@[simp] theorem pointQuarterTurn_apply_zero (v : Point2) :
    pointQuarterTurn v 0 = -v 1 := by
  simp [pointQuarterTurn]

@[simp] theorem pointQuarterTurn_apply_one (v : Point2) :
    pointQuarterTurn v 1 = v 0 := by
  simp [pointQuarterTurn]

/-- A convenient origin on the line which is the inversion image of the
circle through the pivot parametrised by `w`. -/
noncomputable def properCirclePivotLineBase
    (c : ProperCircle) (w : RealProjectiveLineVector) : Point2 :=
  properCircleParamRaw c w -
    (2 * c.1.radius)⁻¹ • properCircleUnitDirection w

/-- A direction vector on the line which is the inversion image of the
circle through the pivot parametrised by `w`. -/
noncomputable def properCirclePivotLineDirection
    (c : ProperCircle) (w : RealProjectiveLineVector) : Point2 :=
  (2 * c.1.radius)⁻¹ • pointQuarterTurn (properCircleUnitDirection w)

/-- Squared chord length in the explicit double-angle parametrisation. -/
theorem dist_properCircleParamRaw_sq
    (c : ProperCircle) {w u : RealProjectiveLineVector}
    (hw : w ≠ 0) (hu : u ≠ 0) :
    dist (properCircleParamRaw c u) (properCircleParamRaw c w) ^ 2 =
      4 * c.1.radius ^ 2 * realProjectiveBracket w u ^ 2 /
        (realProjectiveLineNormSq w * realProjectiveLineNormSq u) := by
  have hnormw : realProjectiveLineNormSq w ≠ 0 :=
    (realProjectiveLineNormSq_pos hw).ne'
  have hnormu : realProjectiveLineNormSq u ≠ 0 :=
    (realProjectiveLineNormSq_pos hu).ne'
  rw [dist_eq_norm, EuclideanSpace.real_norm_sq_eq]
  simp only [Fin.sum_univ_two, PiLp.sub_apply,
    properCircleParamRaw_apply_zero, properCircleParamRaw_apply_one]
  field_simp [hnormw, hnormu]
  simp only [realProjectiveLineNormSq, realProjectiveBracket]
  ring

theorem properCircleParamRaw_ne_of_bracket_ne_zero
    (c : ProperCircle) {w u : RealProjectiveLineVector}
    (hw : w ≠ 0) (hu : u ≠ 0)
    (hwu : realProjectiveBracket w u ≠ 0) :
    properCircleParamRaw c u ≠ properCircleParamRaw c w := by
  intro heq
  have hprojective := properCircleParamRaw_projective_eq c hu hw heq
  have hzero :=
    (realProjective_mk_eq_mk_iff_bracket_eq_zero hu hw).mp hprojective
  apply hwu
  rw [realProjectiveBracket_swap, hzero, neg_zero]

/-- Exact slope formula for inversion in the unit circle about a point of a
proper circle.  The other points of the circle are sent to one affine line,
and their affine parameter is `(w ⬝ u) / [w,u]`. -/
theorem inversion_properCircleParamRaw_eq_pivotSlope
    (c : ProperCircle) {w u : RealProjectiveLineVector}
    (hw : w ≠ 0) (hu : u ≠ 0)
    (hwu : realProjectiveBracket w u ≠ 0) :
    EuclideanGeometry.inversion (properCircleParamRaw c w) 1
        (properCircleParamRaw c u) =
      affineParamPoint
        (properCirclePivotLineBase c w)
        (properCirclePivotLineDirection c w)
        (realProjectiveDot w u / realProjectiveBracket w u) := by
  have hnormw : realProjectiveLineNormSq w ≠ 0 :=
    (realProjectiveLineNormSq_pos hw).ne'
  have hnormu : realProjectiveLineNormSq u ≠ 0 :=
    (realProjectiveLineNormSq_pos hu).ne'
  have hpoints :
      properCircleParamRaw c u ≠ properCircleParamRaw c w :=
    properCircleParamRaw_ne_of_bracket_ne_zero c hw hu hwu
  have hdist :
      dist (properCircleParamRaw c u) (properCircleParamRaw c w) ≠ 0 :=
    dist_ne_zero.mpr hpoints
  have hdistSq := dist_properCircleParamRaw_sq c hw hu
  have hinversionCoord (i : Fin 2) :
      EuclideanGeometry.inversion (properCircleParamRaw c w) 1
          (properCircleParamRaw c u) i =
        properCircleParamRaw c w i +
          (properCircleParamRaw c u i - properCircleParamRaw c w i) /
            dist (properCircleParamRaw c u)
              (properCircleParamRaw c w) ^ 2 := by
    simp [EuclideanGeometry.inversion]
    field_simp [hdist]
    ring
  apply point2_eq_of_apply_zero_one
  · rw [hinversionCoord 0, hdistSq]
    simp only [affineParamPoint_apply, properCirclePivotLineBase,
      properCirclePivotLineDirection, PiLp.sub_apply, PiLp.smul_apply,
      smul_eq_mul, properCircleParamRaw_apply_zero,
      properCircleUnitDirection_apply_zero,
      properCircleUnitDirection_apply_one, pointQuarterTurn_apply_zero]
    field_simp [hnormw, hnormu, c.2.ne', hwu]
    simp only [realProjectiveLineNormSq, realProjectiveBracket,
      realProjectiveDot]
    ring
  · rw [hinversionCoord 1, hdistSq]
    simp only [affineParamPoint_apply, properCirclePivotLineBase,
      properCirclePivotLineDirection, PiLp.sub_apply, PiLp.smul_apply,
      smul_eq_mul, properCircleParamRaw_apply_one,
      properCircleUnitDirection_apply_zero,
      properCircleUnitDirection_apply_one, pointQuarterTurn_apply_one]
    field_simp [hnormw, hnormu, c.2.ne', hwu]
    simp only [realProjectiveLineNormSq, realProjectiveBracket,
      realProjectiveDot]
    ring

/-! ## Intrinsic proper-circle formulation -/

/-- The canonical projective parameter of an actual point of a proper
circle, using the explicit inverse vector from the parametrisation API. -/
noncomputable def properCirclePointParameter
    (c : ProperCircle) (p : ProperCirclePoint c) : RealProjectiveOnePoint :=
  Projectivization.mk ℝ (properCircleInverseVector c p.1)
    (properCircleInverseVector_ne_zero c p.1)

/-- The canonical vector parameter agrees with the inverse of the public
circle parametrisation equivalence. -/
theorem properCirclePointParameter_eq_equiv_symm
    (c : ProperCircle) (p : ProperCirclePoint c) :
    properCirclePointParameter c p = (properCircleProjectiveEquiv c).symm p := by
  apply (properCircleProjectiveEquiv c).injective
  apply Subtype.ext
  simp only [properCirclePointParameter, Equiv.apply_symm_apply,
    properCircleProjectiveEquiv]
  exact properCircleParamRaw_inverseVector c p.2

/-- Harmonicity of four actual points on a proper circle. -/
def ProperCircleProjectiveHarmonic
    (c : ProperCircle)
    (p₀ p₁ p₂ p₃ : ProperCirclePoint c) : Prop :=
  RealProjectiveHarmonic
    (properCirclePointParameter c p₀)
    (properCirclePointParameter c p₁)
    (properCirclePointParameter c p₂)
    (properCirclePointParameter c p₃)

/-- Distinct circle points have nonzero bracket in their canonical
projective representatives. -/
theorem properCircleInverseVector_bracket_ne_zero_of_ne
    (c : ProperCircle) {p q : ProperCirclePoint c} (hpq : p ≠ q) :
    realProjectiveBracket
      (properCircleInverseVector c p.1)
      (properCircleInverseVector c q.1) ≠ 0 := by
  intro hzero
  apply hpq
  apply Subtype.ext
  have hprojective :
      properCirclePointParameter c p = properCirclePointParameter c q := by
    exact (realProjective_mk_eq_mk_iff_bracket_eq_zero
      (properCircleInverseVector_ne_zero c p.1)
      (properCircleInverseVector_ne_zero c q.1)).mpr hzero
  have himage := congrArg (properCircleProjectiveParam c) hprojective
  simpa only [properCirclePointParameter, properCircleProjectiveParam_mk,
    properCircleParamRaw_inverseVector c p.2,
    properCircleParamRaw_inverseVector c q.2] using himage

/-- The affine slope coordinate of `p`, with respect to a distinct pivot
`o` on the same proper circle. -/
noncomputable def properCirclePointPivotSlope
    (c : ProperCircle) (o p : ProperCirclePoint c) : ℝ :=
  realProjectiveDot
      (properCircleInverseVector c o.1)
      (properCircleInverseVector c p.1) /
    realProjectiveBracket
      (properCircleInverseVector c o.1)
      (properCircleInverseVector c p.1)

/-- The raw inversion formula specialized to actual points of the proper
circle. -/
theorem inversion_properCirclePoint_eq_pivotSlope
    (c : ProperCircle) (o p : ProperCirclePoint c) (hop : o ≠ p) :
    EuclideanGeometry.inversion o.1 1 p.1 =
      affineParamPoint
        (properCirclePivotLineBase c (properCircleInverseVector c o.1))
        (properCirclePivotLineDirection c
          (properCircleInverseVector c o.1))
        (properCirclePointPivotSlope c o p) := by
  have hbr := properCircleInverseVector_bracket_ne_zero_of_ne c hop
  simpa only [properCirclePointPivotSlope,
    properCircleParamRaw_inverseVector c o.2,
    properCircleParamRaw_inverseVector c p.2] using
    inversion_properCircleParamRaw_eq_pivotSlope c
      (properCircleInverseVector_ne_zero c o.1)
      (properCircleInverseVector_ne_zero c p.1) hbr

/-- Proper-circle harmonicity is equivalent to harmonicity of the four
finite affine slope coordinates obtained by inverting about a fifth,
distinct point of the circle. -/
theorem properCircleProjectiveHarmonic_iff_pivotSlope
    (c : ProperCircle)
    (o p₀ p₁ p₂ p₃ : ProperCirclePoint c)
    (ho₀ : o ≠ p₀) (ho₁ : o ≠ p₁)
    (ho₂ : o ≠ p₂) (ho₃ : o ≠ p₃) :
    ProperCircleProjectiveHarmonic c p₀ p₁ p₂ p₃ ↔
      RealProjectiveHarmonic
        (realProjectiveAffinePoint (properCirclePointPivotSlope c o p₀))
        (realProjectiveAffinePoint (properCirclePointPivotSlope c o p₁))
        (realProjectiveAffinePoint (properCirclePointPivotSlope c o p₂))
        (realProjectiveAffinePoint (properCirclePointPivotSlope c o p₃)) := by
  unfold ProperCircleProjectiveHarmonic properCirclePointParameter
  exact properCirclePivotSlope_harmonic_iff
    (properCircleInverseVector_ne_zero c o.1)
    (properCircleInverseVector_ne_zero c p₀.1)
    (properCircleInverseVector_ne_zero c p₁.1)
    (properCircleInverseVector_ne_zero c p₂.1)
    (properCircleInverseVector_ne_zero c p₃.1)
    (properCircleInverseVector_bracket_ne_zero_of_ne c ho₀)
    (properCircleInverseVector_bracket_ne_zero_of_ne c ho₁)
    (properCircleInverseVector_bracket_ne_zero_of_ne c ho₂)
    (properCircleInverseVector_bracket_ne_zero_of_ne c ho₃)

end Erdos506.Incidence
