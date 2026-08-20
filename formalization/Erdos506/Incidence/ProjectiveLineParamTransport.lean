import Erdos506.Incidence.InversionHarmonicTransport
import Erdos506.Incidence.FourStarHarmonicNormal

/-!
# Transport between affine-line and projective-line parameters

The inverse image of a circle through the pivot is an affine line.  This
module records its homogeneous `RP¹` parametrisation and the two elementary
transport steps needed when that line is subsequently put into a projective
four-star normal form.
-/

namespace Erdos506.Incidence

open Matrix
open scoped LinearAlgebra.Projectivization

noncomputable section

local instance : DecidableEq RealProjectiveOnePoint := Classical.decEq _

/-- The explicit direction of the inversion image of a proper circle is
never zero.  This is the finite-direction hypothesis needed by the affine
projective-line parametrisation. -/
theorem properCirclePivotLineDirection_ne_zero
    (c : Erdos506.V4.ProperCircle)
    (w : RealProjectiveLineVector) (hw : w ≠ 0) :
    properCirclePivotLineDirection c w ≠ 0 := by
  have hnorm : realProjectiveLineNormSq w ≠ 0 :=
    (realProjectiveLineNormSq_pos hw).ne'
  have hunit : properCircleUnitDirection w ≠ 0 := by
    intro hzero
    have h0 := congrArg
      (fun z : Erdos506.V4.Point2 => z (0 : Fin 2)) hzero
    have h1 := congrArg
      (fun z : Erdos506.V4.Point2 => z (1 : Fin 2)) hzero
    have heq0 : w 0 ^ 2 - w 1 ^ 2 = 0 := by
      simp only [properCircleUnitDirection_apply_zero,
        PiLp.zero_apply] at h0
      field_simp [hnorm] at h0
      simpa using h0
    have heq1 : 2 * w 0 * w 1 = 0 := by
      simp only [properCircleUnitDirection_apply_one,
        PiLp.zero_apply] at h1
      field_simp [hnorm] at h1
      simpa using h1
    have hprod : w 0 * w 1 = 0 := by nlinarith [heq1]
    rcases mul_eq_zero.mp hprod with hw0 | hw1
    · apply hnorm
      simp [realProjectiveLineNormSq, hw0] at heq0 ⊢
      nlinarith
    · apply hnorm
      simp [realProjectiveLineNormSq, hw1] at heq0 ⊢
      nlinarith
  have hquarter : pointQuarterTurn (properCircleUnitDirection w) ≠ 0 := by
    intro hzero
    apply hunit
    ext j
    fin_cases j
    · simpa [pointQuarterTurn] using congrArg
        (fun z : Erdos506.V4.Point2 => z (1 : Fin 2)) hzero
    · simpa [pointQuarterTurn] using congrArg
        (fun z : Erdos506.V4.Point2 => z (0 : Fin 2)) hzero
  apply smul_ne_zero
  · exact inv_ne_zero (mul_ne_zero (by norm_num) c.2.ne')
  · exact hquarter

/-- The affine subspace represented by a base point and a nonzero direction.
It is deliberately exposed separately from `circlePivotLine`: geometric
clients may prove the equality in whichever circle--inversion interface is
available, while the projective parameter transport only needs this equality
and the preceding nonzero-direction theorem. -/
noncomputable def projectiveAffineLineCarrier
    (B D : Erdos506.V4.Point2) : AffineSubspace ℝ Erdos506.V4.Point2 :=
  affineSpan ℝ ({B, B + D} : Set Erdos506.V4.Point2)

/-- Homogeneous projective parametrisation of the affine line through `B`
with direction `D`.  The parameter `[s:t]` represents
`s • directionLift D + t • homogeneousLift B`. -/
def projectiveAffineLineParameter
    (B D : Erdos506.V4.Point2) (u : RealProjectiveLineVector) : Homogeneous3 :=
  u 0 • directionLift D + u 1 • homogeneousLift B

@[simp] theorem projectiveAffineLineParameter_apply
    (B D : Erdos506.V4.Point2) (u : RealProjectiveLineVector) :
    projectiveAffineLineParameter B D u =
      u 0 • directionLift D + u 1 • homogeneousLift B := rfl

/-- The finite affine parameter `t` is represented by `[t:1]`. -/
theorem projectiveAffineLineParameter_affine
    (B D : Erdos506.V4.Point2) (t : ℝ) :
    projectiveAffineLineParameter B D (realProjectiveAffineVector t) =
      homogeneousLift (Erdos506.V3.affineParamPoint B D t) := by
  ext i
  fin_cases i <;>
    simp [projectiveAffineLineParameter, realProjectiveAffineVector,
      homogeneousLift, directionLift, Erdos506.V3.affineParamPoint]
  all_goals ring

/-- In particular, the requested affine homogeneous identity. -/
theorem homogeneousLift_affineParamPoint_eq
    (B D : Erdos506.V4.Point2) (t : ℝ) :
    homogeneousLift (Erdos506.V3.affineParamPoint B D t) =
      t • directionLift D + homogeneousLift B := by
  simpa [projectiveAffineLineParameter, realProjectiveAffineVector] using
    (projectiveAffineLineParameter_affine B D t).symm

/-- A nonzero affine direction makes the homogeneous line parametrisation
injective. -/
theorem projectiveAffineLineParameter_injective
    (B D : Erdos506.V4.Point2) (hD : D ≠ 0) :
    Function.Injective (projectiveAffineLineParameter B D) := by
  intro u v huv
  have hlast := congrFun huv (2 : Fin 3)
  have hsecond : u 1 = v 1 := by
    simpa [projectiveAffineLineParameter, directionLift,
      homogeneousLift] using hlast
  have hcalc : u 0 • directionLift D + u 1 • homogeneousLift B =
      v 0 • directionLift D + v 1 • homogeneousLift B := by
    simpa [projectiveAffineLineParameter] using huv
  rw [hsecond] at hcalc
  have hcoef : u 0 • directionLift D = v 0 • directionLift D := by
    apply add_right_cancel (b := v 1 • homogeneousLift B)
    simpa [add_assoc] using hcalc
  have hdiff : (u 0 - v 0) • directionLift D = 0 := by
    rw [sub_smul]
    exact sub_eq_zero.mpr hcoef
  have hfirst : u 0 = v 0 := by
    have hDlift := directionLift_ne_zero hD
    exact sub_eq_zero.mp ((smul_eq_zero.mp hdiff).resolve_right hDlift)
  ext i
  fin_cases i <;> simp [hfirst, hsecond]

/-- A nonzero projective-line parameter has a nonzero point-vector image on
an affine line with nonzero direction. -/
theorem projectiveAffineLineParameter_ne_zero
    (B D : Erdos506.V4.Point2) (hD : D ≠ 0)
    {u : RealProjectiveLineVector} (hu : u ≠ 0) :
    projectiveAffineLineParameter B D u ≠ 0 := by
  intro hzero
  apply hu
  apply projectiveAffineLineParameter_injective B D hD
  have hzero' : projectiveAffineLineParameter B D 0 = 0 := by
    simp [projectiveAffineLineParameter]
  rw [hzero']
  exact hzero

/-! ## Construction of the parameter `GL₂` for a normal four-star line -/

/-- The two columns are the normal-line parameters of the transformed
direction and affine base point, respectively. -/
def fourStarNormalLineCoefficientMatrix
    (uD uB : RealProjectiveLineVector) : Matrix (Fin 2) (Fin 2) ℝ :=
  ![![uD 0, uB 0], ![uD 1, uB 1]]

theorem fourStarNormalLineCoefficientMatrix_mulVec
    (uD uB u : RealProjectiveLineVector) :
    fourStarNormalLineCoefficientMatrix uD uB *ᵥ u =
      u 0 • uD + u 1 • uB := by
  ext j
  fin_cases j <;>
    simp [fourStarNormalLineCoefficientMatrix, Matrix.mulVec,
      dotProduct, Fin.sum_univ_two]
  all_goals ring

theorem fourStarNormalLineParameter_linear
    (i : Fin 4) (r s : ℝ) (u v : RealProjectiveLineVector) :
    fourStarNormalLineParameter i (r • u + s • v) =
      r • fourStarNormalLineParameter i u +
        s • fourStarNormalLineParameter i v := by
  fin_cases i <;> ext j <;> fin_cases j <;>
    simp [fourStarNormalLineParameter]
  all_goals ring

theorem fourStarNormalLineParameter_zero (i : Fin 4) :
    fourStarNormalLineParameter i 0 = 0 := by
  fin_cases i <;> simp [fourStarNormalLineParameter]

/-- Every homogeneous vector incident with a standard normal base covector
has explicit `RP¹` coordinates in that base-line parametrisation. -/
theorem exists_fourStarNormalLineParameter_of_incident
    (i : Fin 4) {v : Homogeneous3}
    (hincident : projectiveCovectorNormalLine i ⬝ᵥ v = 0) :
    ∃ u : RealProjectiveLineVector,
      fourStarNormalLineParameter i u = v := by
  fin_cases i
  · have h0 : v 0 = 0 := by
      simpa [projectiveCovectorNormalLine, dotProduct,
        Fin.sum_univ_three] using hincident
    refine ⟨![v 1, v 2], ?_⟩
    ext j
    fin_cases j
    · simpa [fourStarNormalLineParameter] using h0.symm
    · simp [fourStarNormalLineParameter]
    · simp [fourStarNormalLineParameter]
  · have h1 : v 1 = 0 := by
      simpa [projectiveCovectorNormalLine, dotProduct,
        Fin.sum_univ_three] using hincident
    refine ⟨![v 0, v 2], ?_⟩
    ext j
    fin_cases j
    · simp [fourStarNormalLineParameter]
    · simpa [fourStarNormalLineParameter] using h1.symm
    · simp [fourStarNormalLineParameter]
  · have h2 : v 2 = 0 := by
      simpa [projectiveCovectorNormalLine, dotProduct,
        Fin.sum_univ_three] using hincident
    refine ⟨![v 0, v 1], ?_⟩
    ext j
    fin_cases j
    · simp [fourStarNormalLineParameter]
    · simp [fourStarNormalLineParameter]
    · simpa [fourStarNormalLineParameter] using h2.symm
  · have hsum : v 0 + v 1 + v 2 = 0 := by
      simpa [projectiveCovectorNormalLine, dotProduct,
        Fin.sum_univ_three] using hincident
    refine ⟨![v 0, v 1], ?_⟩
    ext j
    fin_cases j
    · simp [fourStarNormalLineParameter]
    · simp [fourStarNormalLineParameter]
    · simp [fourStarNormalLineParameter]
      linarith

/-- A projective `GL₃` maps the affine line parameters to the normal-line
parameters when its transformed direction and base point have the displayed
two normal coordinates. -/
theorem projectiveAffineLineParameter_normal_transport
    (G : GL (Fin 3) ℝ) (B D : Erdos506.V4.Point2) (i : Fin 4)
    (uD uB : RealProjectiveLineVector)
    (hDimage : G • directionLift D = fourStarNormalLineParameter i uD)
    (hBimage : G • homogeneousLift B = fourStarNormalLineParameter i uB)
    (u : RealProjectiveLineVector) :
    G • projectiveAffineLineParameter B D u =
      fourStarNormalLineParameter i
        (fourStarNormalLineCoefficientMatrix uD uB *ᵥ u) := by
  rw [fourStarNormalLineCoefficientMatrix_mulVec,
    fourStarNormalLineParameter_linear]
  calc
    G • projectiveAffineLineParameter B D u =
        G • (u 0 • directionLift D) + G • (u 1 • homogeneousLift B) := by
      rw [projectiveAffineLineParameter, smul_add]
    _ = u 0 • (G • directionLift D) +
        u 1 • (G • homogeneousLift B) := by
      rw [smul_comm G (u 0) (directionLift D),
        smul_comm G (u 1) (homogeneousLift B)]
    _ = u 0 • fourStarNormalLineParameter i uD +
        u 1 • fourStarNormalLineParameter i uB := by rw [hDimage, hBimage]

/-- The coefficient matrix is nonsingular: otherwise a nonzero parameter
would map to the zero point-vector, contradicting both the affine-line and
normal-line parametrisation injections. -/
theorem fourStarNormalLineCoefficientMatrix_det_ne_zero
    (G : GL (Fin 3) ℝ) (B D : Erdos506.V4.Point2) (hD : D ≠ 0) (i : Fin 4)
    (uD uB : RealProjectiveLineVector)
    (hDimage : G • directionLift D = fourStarNormalLineParameter i uD)
    (hBimage : G • homogeneousLift B = fourStarNormalLineParameter i uB) :
    (fourStarNormalLineCoefficientMatrix uD uB).det ≠ 0 := by
  intro hdet
  obtain ⟨u, hu, hMu⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  have himage : G • projectiveAffineLineParameter B D u = 0 := by
    rw [projectiveAffineLineParameter_normal_transport G B D i uD uB
      hDimage hBimage u, hMu, fourStarNormalLineParameter_zero]
  have hline : projectiveAffineLineParameter B D u = 0 := by
    have hback := congrArg (fun w : Homogeneous3 => G⁻¹ • w) himage
    simpa [smul_smul] using hback
  apply hu
  apply projectiveAffineLineParameter_injective B D hD
  have hzero : projectiveAffineLineParameter B D 0 = 0 := by
    simp [projectiveAffineLineParameter]
  rw [hzero]
  exact hline

/-- The explicitly constructed change of homogeneous parameters. -/
noncomputable def fourStarNormalLineCoefficientGL
    (G : GL (Fin 3) ℝ) (B D : Erdos506.V4.Point2) (hD : D ≠ 0) (i : Fin 4)
    (uD uB : RealProjectiveLineVector)
    (hDimage : G • directionLift D = fourStarNormalLineParameter i uD)
    (hBimage : G • homogeneousLift B = fourStarNormalLineParameter i uB) :
    GL (Fin 2) ℝ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero
    (fourStarNormalLineCoefficientMatrix uD uB)
    (fourStarNormalLineCoefficientMatrix_det_ne_zero G B D hD i uD uB
      hDimage hBimage)

theorem projectiveAffineLineParameter_normal_transport_gl
    (G : GL (Fin 3) ℝ) (B D : Erdos506.V4.Point2) (hD : D ≠ 0) (i : Fin 4)
    (uD uB : RealProjectiveLineVector)
    (hDimage : G • directionLift D = fourStarNormalLineParameter i uD)
    (hBimage : G • homogeneousLift B = fourStarNormalLineParameter i uB)
    (u : RealProjectiveLineVector) :
    G • projectiveAffineLineParameter B D u =
      fourStarNormalLineParameter i
        (fourStarNormalLineCoefficientGL G B D hD i uD uB hDimage hBimage • u) := by
  change G • projectiveAffineLineParameter B D u =
    fourStarNormalLineParameter i
      (fourStarNormalLineCoefficientMatrix uD uB *ᵥ u)
  exact projectiveAffineLineParameter_normal_transport G B D i uD uB
    hDimage hBimage u

/-- An ordered harmonic range stays harmonic after a `GL₂` change of
homogeneous parameter coordinates. -/
theorem realProjectiveHarmonic_parameter_gl_iff
    (g : GL (Fin 2) ℝ) {P Q R S : RealProjectiveOnePoint} :
    RealProjectiveHarmonic P Q R S ↔
      RealProjectiveHarmonic (g • P) (g • Q) (g • R) (g • S) :=
  (realProjectiveHarmonic_gl_smul_iff g).symm

/-- Order-free harmonic four-sets are preserved by every `GL₂` parameter
change.  This is the finite-set version used when a four-star trace is
identified with the image of pivot-slope parameters. -/
theorem isRealProjectiveHarmonicFour_image_gl
    (g : GL (Fin 2) ℝ) (T : Finset RealProjectiveOnePoint)
    (h : IsRealProjectiveHarmonicFour T) :
    IsRealProjectiveHarmonicFour (T.image fun P => g • P) := by
  classical
  rcases h with ⟨hcard, P, Q, R, S, hset, hdistinct, hharmonic⟩
  have hinjective : Function.Injective (fun X : RealProjectiveOnePoint => g • X) := by
    intro X Y hXY
    have hback := congrArg (fun Z : RealProjectiveOnePoint => g⁻¹ • Z) hXY
    simpa [smul_smul] using hback
  refine ⟨?_, g • P, g • Q, g • R, g • S, ?_, ?_,
    realProjectiveHarmonic_gl_smul g hharmonic⟩
  · rw [Finset.card_image_of_injective _ hinjective, hcard]
  · rw [← hset]
    ext Z
    simp
  · rcases hdistinct with ⟨hPQ, hPR, hPS, hQR, hQS, hRS⟩
    exact ⟨fun h => hPQ (hinjective h), fun h => hPR (hinjective h),
      fun h => hPS (hinjective h), fun h => hQR (hinjective h),
      fun h => hQS (hinjective h), fun h => hRS (hinjective h)⟩

/-- A set equality supplies the final bridge from a `GL₂`-changed source
parameter set to the target normal-line parameter set. -/
theorem isRealProjectiveHarmonicFour_of_eq_image_gl
    (g : GL (Fin 2) ℝ) {T U : Finset RealProjectiveOnePoint}
    (hT : IsRealProjectiveHarmonicFour T)
    (hU : U = T.image fun P => g • P) :
    IsRealProjectiveHarmonicFour U := by
  rw [hU]
  exact isRealProjectiveHarmonicFour_image_gl g T hT

/-- Specialized final bridge: once four pivot-slope parameters are identified
with the `GL₂` image of the normal-line trace parameters, their order-free
harmonicity transfers without choosing an ordering. -/
theorem isRealProjectiveHarmonicFour_of_image_gl_eq_fourStarNormalTrace
    (g : GL (Fin 2) ℝ) (T : Finset RealProjectiveOnePoint) (i : Fin 4)
    (hT : IsRealProjectiveHarmonicFour T)
    (himage : T.image (fun P => g • P) =
      fourStarNormalTraceParameterSet i) :
    IsRealProjectiveHarmonicFour (fourStarNormalTraceParameterSet i) := by
  rw [← himage]
  exact isRealProjectiveHarmonicFour_image_gl g T hT

/-- Conversely, a parameter set explicitly presented as the inverse `GL₂`
image of a normal four-star trace is harmonic.  This is the direction used
to return from normalized projective coordinates to pivot-slope parameters. -/
theorem isRealProjectiveHarmonicFour_of_eq_image_inv_fourStarNormalTrace
    (g : GL (Fin 2) ℝ) (T : Finset RealProjectiveOnePoint) (i : Fin 4)
    (hT : T = (fourStarNormalTraceParameterSet i).image
      (fun P => g⁻¹ • P)) :
    IsRealProjectiveHarmonicFour T := by
  rw [hT]
  exact isRealProjectiveHarmonicFour_image_gl g⁻¹
    (fourStarNormalTraceParameterSet i)
    (fourStarNormal_traceParameterSet_harmonic i)

end

end Erdos506.Incidence
