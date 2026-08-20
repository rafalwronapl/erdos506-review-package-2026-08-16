import Erdos506.Incidence.ProjectiveCoordinates
import Erdos506.Incidence.RealConicPencilInvolution
import Erdos506.V3.DirectedPower

/-!
# Projective parametrization of a proper real circle

For a proper circle with centre `(c₀,c₁)` and radius `r`, this file uses
the homogeneous double-angle parametrization

`[u:v] ↦ [c₀D + r(u²-v²) : c₁D + 2ruv : D]`,

where `D=u²+v²`.  Since `D>0` for a nonzero real pair, every image lies in
the affine chart and gives a point of the Euclidean circle.  The same
formula provides the bridge between affine chord lines and the quadratic
Veronese model of the conic.

For a projective centre `o=[o₀:o₁:o₂]`, the determinant expressing that
the chord through parameters `u,v` contains `o` factors as

`2 r [u,v] Bₒ(u,v)`.

Here `Bₒ` is a symmetric binary form.  The residual endpoint is therefore
the explicit projective involution from `RealConicPencilInvolution`, and
its action preserves or reverses the cyclic order supplied by
`RealProjectiveLineCyclicOrder`.
-/

namespace Erdos506.Incidence

open Erdos506.V3
open Erdos506.V4
open Matrix
open scoped LinearAlgebra.Projectivization

/-- Extensionality for the two concrete coordinates of `Point2`, avoiding
the proof-term wrappers introduced by `PiLp.ext` after `fin_cases`. -/
theorem point2_eq_of_apply_zero_one {p q : Point2}
    (hzero : p 0 = q 0) (hone : p 1 = q 1) : p = q := by
  ext i
  fin_cases i
  · simpa using hzero
  · simpa using hone

/-- Extensionality for the three concrete homogeneous coordinates. -/
theorem homogeneous3_eq_of_apply_zero_one_two {p q : Homogeneous3}
    (hzero : p 0 = q 0) (hone : p 1 = q 1)
    (htwo : p 2 = q 2) : p = q := by
  funext i
  fin_cases i
  · simpa using hzero
  · simpa using hone
  · simpa using htwo

/-! ## The affine and homogeneous parametrizations -/

/-- The positive quadratic denominator of a nonzero real homogeneous
pair. -/
def realProjectiveLineNormSq (u : RealProjectiveLineVector) : ℝ :=
  u 0 ^ 2 + u 1 ^ 2

theorem realProjectiveLineNormSq_pos
    {u : RealProjectiveLineVector} (hu : u ≠ 0) :
    0 < realProjectiveLineNormSq u := by
  have hcoord : u 0 ≠ 0 ∨ u 1 ≠ 0 := by
    by_contra h
    push Not at h
    apply hu
    funext i
    fin_cases i <;> simp_all
  rcases hcoord with h0 | h1
  · have hsquare : 0 < u 0 ^ 2 := sq_pos_of_ne_zero h0
    exact add_pos_of_pos_of_nonneg hsquare (sq_nonneg (u 1))
  · have hsquare : 0 < u 1 ^ 2 := sq_pos_of_ne_zero h1
    exact add_pos_of_nonneg_of_pos (sq_nonneg (u 0)) hsquare

@[simp] theorem realProjectiveLineNormSq_smul
    (a : ℝ) (u : RealProjectiveLineVector) :
    realProjectiveLineNormSq (a • u) =
      a ^ 2 * realProjectiveLineNormSq u := by
  simp [realProjectiveLineNormSq]
  ring

/-- The affine circle point attached to a nonzero homogeneous pair. -/
noncomputable def properCircleParamRaw
    (c : ProperCircle) (u : RealProjectiveLineVector) : Point2 :=
  pointOfCoords
    (c.1.center 0 + c.1.radius *
      ((u 0 ^ 2 - u 1 ^ 2) / realProjectiveLineNormSq u))
    (c.1.center 1 + c.1.radius *
      ((2 * u 0 * u 1) / realProjectiveLineNormSq u))

@[simp] theorem properCircleParamRaw_apply_zero
    (c : ProperCircle) (u : RealProjectiveLineVector) :
    properCircleParamRaw c u 0 =
      c.1.center 0 + c.1.radius *
        ((u 0 ^ 2 - u 1 ^ 2) / realProjectiveLineNormSq u) := by
  simp [properCircleParamRaw]

@[simp] theorem properCircleParamRaw_apply_one
    (c : ProperCircle) (u : RealProjectiveLineVector) :
    properCircleParamRaw c u 1 =
      c.1.center 1 + c.1.radius *
        ((2 * u 0 * u 1) / realProjectiveLineNormSq u) := by
  simp [properCircleParamRaw]

/-- The affine formula is invariant under nonzero rescaling. -/
theorem properCircleParamRaw_smul
    (c : ProperCircle) {u : RealProjectiveLineVector}
    (hu : u ≠ 0) {a : ℝ} (ha : a ≠ 0) :
    properCircleParamRaw c (a • u) = properCircleParamRaw c u := by
  have hden : realProjectiveLineNormSq u ≠ 0 :=
    (realProjectiveLineNormSq_pos hu).ne'
  apply point2_eq_of_apply_zero_one
  · simp only [properCircleParamRaw_apply_zero,
      realProjectiveLineNormSq_smul, Pi.smul_apply, smul_eq_mul]
    field_simp [ha, hden]
  · simp only [properCircleParamRaw_apply_one,
      realProjectiveLineNormSq_smul, Pi.smul_apply, smul_eq_mul]
    field_simp [ha, hden]

/-- Every raw parameter point lies on the proper circle. -/
theorem properCircleParamRaw_mem
    (c : ProperCircle) {u : RealProjectiveLineVector} (hu : u ≠ 0) :
    properCircleParamRaw c u ∈ (c.1 : Set Point2) := by
  apply (mem_properCircle_iff_equation c _).mpr
  have hden : realProjectiveLineNormSq u ≠ 0 :=
    (realProjectiveLineNormSq_pos hu).ne'
  simp only [circleEquation, properCircleEquationA,
    properCircleEquationB, properCircleEquationC,
    properCircleParamRaw_apply_zero, properCircleParamRaw_apply_one]
  field_simp [hden]
  simp only [realProjectiveLineNormSq]
  ring

/-- The scale-invariant affine parametrization `RP¹ → c`. -/
noncomputable def properCircleProjectiveParam
    (c : ProperCircle) : RealProjectiveOnePoint → Point2 :=
  Projectivization.lift
    (fun u : {u : RealProjectiveLineVector // u ≠ 0} =>
      properCircleParamRaw c u.1)
    (by
      intro u v a huv
      have ha : a ≠ 0 := by
        intro ha
        subst a
        simp at huv
        exact u.2 huv
      calc
        properCircleParamRaw c u.1 =
            properCircleParamRaw c (a • v.1) :=
          congrArg (properCircleParamRaw c) huv
        _ = properCircleParamRaw c v.1 :=
          properCircleParamRaw_smul c v.2 ha)

@[simp] theorem properCircleProjectiveParam_mk
    (c : ProperCircle) (u : RealProjectiveLineVector) (hu : u ≠ 0) :
    properCircleProjectiveParam c (Projectivization.mk ℝ u hu) =
      properCircleParamRaw c u := by
  rfl

theorem properCircleProjectiveParam_mem
    (c : ProperCircle) (P : RealProjectiveOnePoint) :
    properCircleProjectiveParam c P ∈ (c.1 : Set Point2) := by
  induction P using Projectivization.ind with
  | h u hu =>
      rw [properCircleProjectiveParam_mk]
      exact properCircleParamRaw_mem c hu

/-- The affine circle trace as a type. -/
abbrev ProperCirclePoint (c : ProperCircle) :=
  {p : Point2 // p ∈ (c.1 : Set Point2)}

/-- The parametrization with its circle-membership certificate attached. -/
noncomputable def properCircleProjectiveParamToCircle
    (c : ProperCircle) : RealProjectiveOnePoint → ProperCirclePoint c :=
  fun P => ⟨properCircleProjectiveParam c P,
    properCircleProjectiveParam_mem c P⟩

/-! ## Injectivity and the explicit inverse -/

/-- Polynomial identity behind injectivity of the double-angle map. -/
theorem realCircleDoubleAngle_cross_identity
    (u v : RealProjectiveLineVector) :
    (((u 0 ^ 2 - u 1 ^ 2) * realProjectiveLineNormSq v -
        (v 0 ^ 2 - v 1 ^ 2) * realProjectiveLineNormSq u) ^ 2 +
      ((2 * u 0 * u 1) * realProjectiveLineNormSq v -
        (2 * v 0 * v 1) * realProjectiveLineNormSq u) ^ 2) =
      4 * realProjectiveLineNormSq u * realProjectiveLineNormSq v *
        realProjectiveBracket u v ^ 2 := by
  simp only [realProjectiveLineNormSq, realProjectiveBracket]
  ring

/-- Equality of two raw circle points forces equality of their projective
parameters. -/
theorem properCircleParamRaw_projective_eq
    (c : ProperCircle)
    {u v : RealProjectiveLineVector} (hu : u ≠ 0) (hv : v ≠ 0)
    (hparam : properCircleParamRaw c u = properCircleParamRaw c v) :
    Projectivization.mk ℝ u hu = Projectivization.mk ℝ v hv := by
  have hdu : 0 < realProjectiveLineNormSq u :=
    realProjectiveLineNormSq_pos hu
  have hdv : 0 < realProjectiveLineNormSq v :=
    realProjectiveLineNormSq_pos hv
  have hx := congrArg (fun p : Point2 => p 0) hparam
  have hy := congrArg (fun p : Point2 => p 1) hparam
  simp only [properCircleParamRaw_apply_zero] at hx
  simp only [properCircleParamRaw_apply_one] at hy
  have hxnormalized :
      (u 0 ^ 2 - u 1 ^ 2) / realProjectiveLineNormSq u =
        (v 0 ^ 2 - v 1 ^ 2) / realProjectiveLineNormSq v := by
    nlinarith [c.2]
  have hynormalized :
      (2 * u 0 * u 1) / realProjectiveLineNormSq u =
        (2 * v 0 * v 1) / realProjectiveLineNormSq v := by
    nlinarith [c.2]
  have hxpolynomial :
      (u 0 ^ 2 - u 1 ^ 2) * realProjectiveLineNormSq v =
        (v 0 ^ 2 - v 1 ^ 2) * realProjectiveLineNormSq u := by
    exact (div_eq_div_iff hdu.ne' hdv.ne').mp hxnormalized
  have hypolynomial :
      (2 * u 0 * u 1) * realProjectiveLineNormSq v =
        (2 * v 0 * v 1) * realProjectiveLineNormSq u := by
    exact (div_eq_div_iff hdu.ne' hdv.ne').mp hynormalized
  have hidentity := realCircleDoubleAngle_cross_identity u v
  rw [hxpolynomial, hypolynomial] at hidentity
  have hbracketSq : realProjectiveBracket u v ^ 2 = 0 := by
    have hpositive :
        0 < 4 * realProjectiveLineNormSq u *
          realProjectiveLineNormSq v := by positivity
    nlinarith
  apply (realProjective_mk_eq_mk_iff_bracket_eq_zero hu hv).mpr
  nlinarith [hbracketSq]

theorem properCircleProjectiveParam_injective
    (c : ProperCircle) :
    Function.Injective (properCircleProjectiveParam c) := by
  intro P Q hPQ
  induction P using Projectivization.ind with
  | h u hu =>
      induction Q using Projectivization.ind with
      | h v hv =>
          simp only [properCircleProjectiveParam_mk] at hPQ
          exact properCircleParamRaw_projective_eq c hu hv hPQ

/-- Normalized first coordinate of a point relative to a proper circle. -/
noncomputable def properCircleNormalizedX
    (c : ProperCircle) (p : Point2) : ℝ :=
  (p 0 - c.1.center 0) / c.1.radius

/-- Normalized second coordinate of a point relative to a proper circle. -/
noncomputable def properCircleNormalizedY
    (c : ProperCircle) (p : Point2) : ℝ :=
  (p 1 - c.1.center 1) / c.1.radius

theorem properCircle_normalized_sq_add
    (c : ProperCircle) {p : Point2} (hp : p ∈ (c.1 : Set Point2)) :
    properCircleNormalizedX c p ^ 2 +
      properCircleNormalizedY c p ^ 2 = 1 := by
  have hdistance := EuclideanGeometry.mem_sphere'.mp hp
  change dist c.1.center p = c.1.radius at hdistance
  have hsquare := congrArg (fun x : ℝ => x ^ 2) hdistance
  dsimp at hsquare
  rw [dist_eq_norm, EuclideanSpace.real_norm_sq_eq] at hsquare
  simp [Fin.sum_univ_two] at hsquare
  simp only [properCircleNormalizedX, properCircleNormalizedY]
  field_simp [c.2.ne']
  nlinarith

theorem properCircle_recover_zero
    (c : ProperCircle) (p : Point2) :
    c.1.center 0 + c.1.radius * properCircleNormalizedX c p = p 0 := by
  simp [properCircleNormalizedX]
  field_simp [c.2.ne']
  ring

theorem properCircle_recover_one
    (c : ProperCircle) (p : Point2) :
    c.1.center 1 + c.1.radius * properCircleNormalizedY c p = p 1 := by
  simp [properCircleNormalizedY]
  field_simp [c.2.ne']
  ring

/-- A homogeneous inverse parameter for a point on the circle.  The west
pole uses `[0:1]`; all other points use `[1+x:y]`. -/
noncomputable def properCircleInverseVector
    (c : ProperCircle) (p : Point2) : RealProjectiveLineVector :=
  if properCircleNormalizedX c p = -1 then ![0, 1]
  else ![1 + properCircleNormalizedX c p,
    properCircleNormalizedY c p]

theorem properCircleInverseVector_ne_zero
    (c : ProperCircle) (p : Point2) :
    properCircleInverseVector c p ≠ 0 := by
  by_cases hx : properCircleNormalizedX c p = -1
  · simp [properCircleInverseVector, hx]
  · intro hzero
    have hfirst := congrFun hzero (0 : Fin 2)
    simp [properCircleInverseVector, hx] at hfirst
    exact hx (by linarith)

/-- The inverse vector maps back to the original circle point. -/
theorem properCircleParamRaw_inverseVector
    (c : ProperCircle) {p : Point2} (hp : p ∈ (c.1 : Set Point2)) :
    properCircleParamRaw c (properCircleInverseVector c p) = p := by
  let x := properCircleNormalizedX c p
  let y := properCircleNormalizedY c p
  have hunit : x ^ 2 + y ^ 2 = 1 := by
    simpa [x, y] using properCircle_normalized_sq_add c hp
  have hrecover0 : c.1.center 0 + c.1.radius * x = p 0 := by
    simpa [x] using properCircle_recover_zero c p
  have hrecover1 : c.1.center 1 + c.1.radius * y = p 1 := by
    simpa [y] using properCircle_recover_one c p
  by_cases hx : x = -1
  · have hy : y = 0 := by nlinarith
    have hx' : properCircleNormalizedX c p = -1 := by
      simpa [x] using hx
    have hinverse : properCircleInverseVector c p = ![0, 1] := by
      simp [properCircleInverseVector, hx']
    rw [hinverse]
    apply point2_eq_of_apply_zero_one
    · rw [properCircleParamRaw_apply_zero, ← hrecover0, hx]
      norm_num [realProjectiveLineNormSq]
    · rw [properCircleParamRaw_apply_one, ← hrecover1, hy]
      norm_num [realProjectiveLineNormSq]
  · have hxone : 1 + x ≠ 0 := by
      intro h
      apply hx
      linarith
    have hden : (1 + x) ^ 2 + y ^ 2 ≠ 0 := by
      positivity
    have hdenEq : (1 + x) ^ 2 + y ^ 2 = 2 * (1 + x) := by
      nlinarith [hunit]
    have hratio0 :
        (((1 + x) ^ 2 - y ^ 2) /
          ((1 + x) ^ 2 + y ^ 2)) = x := by
      field_simp [hden]
      nlinarith
    have hratio1 :
        (2 * (1 + x) * y /
          ((1 + x) ^ 2 + y ^ 2)) = y := by
      rw [hdenEq]
      field_simp [hxone]
    have hx' : properCircleNormalizedX c p ≠ -1 := by
      simpa [x] using hx
    have hinverse : properCircleInverseVector c p = ![1 + x, y] := by
      simp [properCircleInverseVector, hx', x, y]
    rw [hinverse]
    apply point2_eq_of_apply_zero_one
    · simp only [properCircleParamRaw_apply_zero,
        realProjectiveLineNormSq, Matrix.cons_val_zero,
        Matrix.cons_val_one]
      rw [hratio0]
      exact hrecover0
    · simp only [properCircleParamRaw_apply_one,
        realProjectiveLineNormSq, Matrix.cons_val_zero,
        Matrix.cons_val_one]
      rw [hratio1]
      exact hrecover1

theorem properCircleProjectiveParam_surjective_on_circle
    (c : ProperCircle) (p : Point2) (hp : p ∈ (c.1 : Set Point2)) :
    ∃ P : RealProjectiveOnePoint, properCircleProjectiveParam c P = p := by
  let u := properCircleInverseVector c p
  let hu : u ≠ 0 := properCircleInverseVector_ne_zero c p
  refine ⟨Projectivization.mk ℝ u hu, ?_⟩
  rw [properCircleProjectiveParam_mk]
  exact properCircleParamRaw_inverseVector c hp

/-- The explicit projective parametrization is an equivalence between
`RP¹` and the point set of the proper circle. -/
noncomputable def properCircleProjectiveEquiv
    (c : ProperCircle) : RealProjectiveOnePoint ≃ ProperCirclePoint c :=
  Equiv.ofBijective (properCircleProjectiveParamToCircle c) <| by
    constructor
    · intro P Q hPQ
      apply properCircleProjectiveParam_injective c
      exact congrArg Subtype.val hPQ
    · intro p
      obtain ⟨P, hP⟩ :=
        properCircleProjectiveParam_surjective_on_circle c p.1 p.2
      refine ⟨P, ?_⟩
      apply Subtype.ext
      exact hP

/-! ## Homogeneous Veronese transport -/

/-- Homogeneous quadratic coordinates of the parametrized circle. -/
def properCircleVeroneseVector
    (c : ProperCircle) (u : RealProjectiveLineVector) : Homogeneous3 :=
  ![c.1.center 0 * realProjectiveLineNormSq u +
      c.1.radius * (u 0 ^ 2 - u 1 ^ 2),
    c.1.center 1 * realProjectiveLineNormSq u +
      c.1.radius * (2 * u 0 * u 1),
    realProjectiveLineNormSq u]

theorem properCircleVeroneseVector_ne_zero
    (c : ProperCircle) {u : RealProjectiveLineVector} (hu : u ≠ 0) :
    properCircleVeroneseVector c u ≠ 0 := by
  intro hzero
  have hlast := congrFun hzero (2 : Fin 3)
  simp [properCircleVeroneseVector] at hlast
  exact (realProjectiveLineNormSq_pos hu).ne' hlast

theorem properCircleVeroneseVector_smul
    (c : ProperCircle) (a : ℝ) (u : RealProjectiveLineVector) :
    properCircleVeroneseVector c (a • u) =
      a ^ 2 • properCircleVeroneseVector c u := by
  ext i
  fin_cases i <;>
    simp [properCircleVeroneseVector,
      realProjectiveLineNormSq_smul] <;>
    ring

/-- The homogeneous Veronese parametrization of the projective completion
of the circle. -/
noncomputable def properCircleVeronesePoint
    (c : ProperCircle) : RealProjectiveOnePoint → RealProjectivePlane :=
  Projectivization.lift
    (fun u : {u : RealProjectiveLineVector // u ≠ 0} =>
      Projectivization.mk ℝ (properCircleVeroneseVector c u.1)
        (properCircleVeroneseVector_ne_zero c u.2))
    (by
      intro u v a huv
      have ha : a ≠ 0 := by
        intro ha
        subst a
        simp at huv
        exact u.2 huv
      apply (Projectivization.mk_eq_mk_iff' ℝ _ _
        (properCircleVeroneseVector_ne_zero c u.2)
        (properCircleVeroneseVector_ne_zero c v.2)).mpr
      refine ⟨a ^ 2, ?_⟩
      rw [← properCircleVeroneseVector_smul]
      exact congrArg (properCircleVeroneseVector c) huv.symm)

@[simp] theorem properCircleVeronesePoint_mk
    (c : ProperCircle) (u : RealProjectiveLineVector) (hu : u ≠ 0) :
    properCircleVeronesePoint c (Projectivization.mk ℝ u hu) =
      Projectivization.mk ℝ (properCircleVeroneseVector c u)
        (properCircleVeroneseVector_ne_zero c hu) := by
  rfl

/-- The homogeneous Veronese point is exactly the projective lift of the
affine parameter point. -/
theorem properCircleVeronesePoint_eq_projectivePoint
    (c : ProperCircle) (P : RealProjectiveOnePoint) :
    properCircleVeronesePoint c P =
      projectivePoint (properCircleProjectiveParam c P) := by
  induction P using Projectivization.ind with
  | h u hu =>
      rw [properCircleVeronesePoint_mk,
        properCircleProjectiveParam_mk]
      apply (Projectivization.mk_eq_mk_iff' ℝ _ _
        (properCircleVeroneseVector_ne_zero c hu)
        (homogeneousLift_ne_zero (properCircleParamRaw c u))).mpr
      refine ⟨realProjectiveLineNormSq u, ?_⟩
      have hden : realProjectiveLineNormSq u ≠ 0 :=
        (realProjectiveLineNormSq_pos hu).ne'
      apply homogeneous3_eq_of_apply_zero_one_two
      · simp only [Pi.smul_apply, smul_eq_mul,
          homogeneousLift_zero, properCircleParamRaw_apply_zero,
          properCircleVeroneseVector, Matrix.cons_val_zero]
        field_simp [hden]
      · simp only [Pi.smul_apply, smul_eq_mul,
          homogeneousLift_one, properCircleParamRaw_apply_one,
          properCircleVeroneseVector, Matrix.cons_val_one,
          Matrix.cons_val_zero]
        field_simp [hden]
      · change realProjectiveLineNormSq u * 1 =
          realProjectiveLineNormSq u
        ring

/-! ## Chords and their projective intersections -/

/-- The projective chord through two distinct circle parameters. -/
noncomputable def properCircleParamChord
    (c : ProperCircle) {P Q : RealProjectiveOnePoint} (hPQ : P ≠ Q) :
    RealProjectivePlane :=
  projectiveLine (properCircleProjectiveParam c P)
    (properCircleProjectiveParam c Q)
    ((properCircleProjectiveParam_injective c).ne hPQ)

/-- Chord formation commutes with the parametrization. -/
theorem properCircleParamChord_eq_cross
    (c : ProperCircle) {P Q : RealProjectiveOnePoint} (hPQ : P ≠ Q) :
    properCircleParamChord c hPQ =
      Projectivization.cross
        (properCircleVeronesePoint c P)
        (properCircleVeronesePoint c Q) := by
  unfold properCircleParamChord
  rw [properCircleVeronesePoint_eq_projectivePoint,
    properCircleVeronesePoint_eq_projectivePoint]
  exact (projectivePoint_cross_eq_projectiveLine
    ((properCircleProjectiveParam_injective c).ne hPQ)).symm

/-- Projective intersection of two parametrized chords.  Mathlib's total
`cross` convention also gives a value when the chord covectors coincide. -/
noncomputable def properCircleParamChordIntersection
    (c : ProperCircle)
    {P Q R S : RealProjectiveOnePoint} (hPQ : P ≠ Q) (hRS : R ≠ S) :
    RealProjectivePlane :=
  Projectivization.cross
    (properCircleParamChord c hPQ)
    (properCircleParamChord c hRS)

/-- Intersection transport entirely in homogeneous Veronese coordinates. -/
theorem properCircleParamChordIntersection_eq_cross
    (c : ProperCircle)
    {P Q R S : RealProjectiveOnePoint} (hPQ : P ≠ Q) (hRS : R ≠ S) :
    properCircleParamChordIntersection c hPQ hRS =
      Projectivization.cross
        (Projectivization.cross
          (properCircleVeronesePoint c P)
          (properCircleVeronesePoint c Q))
        (Projectivization.cross
          (properCircleVeronesePoint c R)
          (properCircleVeronesePoint c S)) := by
  rw [properCircleParamChordIntersection,
    properCircleParamChord_eq_cross,
    properCircleParamChord_eq_cross]

/-! ## The chord-pencil factorization -/

/-- First coefficient of the binary chord-pencil form associated with a
homogeneous projective centre. -/
def properCirclePencilA (c : ProperCircle) (o : Homogeneous3) : ℝ :=
  c.1.radius * o 2 - (o 0 - c.1.center 0 * o 2)

/-- Mixed coefficient of the binary chord-pencil form. -/
def properCirclePencilB (c : ProperCircle) (o : Homogeneous3) : ℝ :=
  -(o 1 - c.1.center 1 * o 2)

/-- Last coefficient of the binary chord-pencil form. -/
def properCirclePencilC (c : ProperCircle) (o : Homogeneous3) : ℝ :=
  c.1.radius * o 2 + (o 0 - c.1.center 0 * o 2)

/-- Exact determinant factorization for a chord and a projective centre. -/
theorem properCircleVeronese_chord_det
    (c : ProperCircle) (o : Homogeneous3)
    (u v : RealProjectiveLineVector) :
    Matrix.det ![properCircleVeroneseVector c u,
        properCircleVeroneseVector c v, o] =
      2 * c.1.radius * realProjectiveBracket u v *
        realConicPencilForm
          (properCirclePencilA c o)
          (properCirclePencilB c o)
          (properCirclePencilC c o) u v := by
  simp [properCircleVeroneseVector, realProjectiveLineNormSq,
    properCirclePencilA, properCirclePencilB, properCirclePencilC,
    realProjectiveBracket, realConicPencilForm,
    Matrix.det_fin_three]
  ring

/-- For two distinct parameters, incidence of the centre with their chord
is exactly the symmetric pencil equation. -/
theorem properCircleVeronese_chord_det_eq_zero_iff
    (c : ProperCircle) (o : Homogeneous3)
    {u v : RealProjectiveLineVector}
    (hdistinct : realProjectiveBracket u v ≠ 0) :
    Matrix.det ![properCircleVeroneseVector c u,
        properCircleVeroneseVector c v, o] = 0 ↔
      realConicPencilForm
        (properCirclePencilA c o)
        (properCirclePencilB c o)
        (properCirclePencilC c o) u v = 0 := by
  rw [properCircleVeronese_chord_det]
  have hprefactor :
      2 * c.1.radius * realProjectiveBracket u v ≠ 0 := by
    exact mul_ne_zero
      (mul_ne_zero (by norm_num) c.2.ne') hdistinct
  exact mul_eq_zero_iff_left hprefactor

/-- The nondegeneracy scalar of the chord-pencil form. -/
def properCirclePencilDeterminant
    (c : ProperCircle) (o : Homogeneous3) : ℝ :=
  properCirclePencilA c o * properCirclePencilC c o -
    properCirclePencilB c o ^ 2

/-- Expanded form: nondegeneracy says that the projective centre is not on
the projective circle. -/
theorem properCirclePencilDeterminant_eq
    (c : ProperCircle) (o : Homogeneous3) :
    properCirclePencilDeterminant c o =
      (c.1.radius * o 2) ^ 2 -
        (o 0 - c.1.center 0 * o 2) ^ 2 -
        (o 1 - c.1.center 1 * o 2) ^ 2 := by
  simp [properCirclePencilDeterminant, properCirclePencilA,
    properCirclePencilB, properCirclePencilC]
  ring

/-- The explicit residual-intersection projectivity of a nondegenerate
circle chord pencil. -/
noncomputable def properCirclePencilGL
    (c : ProperCircle) (o : Homogeneous3)
    (hnondegenerate : properCirclePencilDeterminant c o ≠ 0) :
    GL (Fin 2) ℝ :=
  realConicPencilGL
    (properCirclePencilA c o)
    (properCirclePencilB c o)
    (properCirclePencilC c o) hnondegenerate

/-- The residual endpoint is characterized exactly by the chord-incidence
equation with the chosen centre. -/
theorem properCirclePencil_residual_iff
    (c : ProperCircle) (o : Homogeneous3)
    (hnondegenerate : properCirclePencilDeterminant c o ≠ 0)
    {u v : RealProjectiveLineVector} (hu : u ≠ 0) (hv : v ≠ 0) :
    realConicPencilForm
        (properCirclePencilA c o)
        (properCirclePencilB c o)
        (properCirclePencilC c o) u v = 0 ↔
      Projectivization.mk ℝ v hv =
        properCirclePencilGL c o hnondegenerate •
          Projectivization.mk ℝ u hu := by
  rw [Projectivization.smul_mk]
  exact realConicPencil_residual_iff
    (properCirclePencilA c o)
    (properCirclePencilB c o)
    (properCirclePencilC c o) hnondegenerate hu hv

/-- The circle chord-pencil projectivity is an involution of `RP¹`. -/
theorem properCirclePencil_projective_involution
    (c : ProperCircle) (o : Homogeneous3)
    (hnondegenerate : properCirclePencilDeterminant c o ≠ 0)
    (P : RealProjectiveOnePoint) :
    properCirclePencilGL c o hnondegenerate •
        (properCirclePencilGL c o hnondegenerate • P) = P :=
  realConicPencilGL_projective_involution
    (properCirclePencilA c o)
    (properCirclePencilB c o)
    (properCirclePencilC c o) hnondegenerate P

/-- Minimal order theorem for the actual circle pencil: its residual
involution preserves every positive cyclic triple or reverses every such
triple. -/
theorem properCirclePencil_preserves_or_reverses_cyclicOrder
    (c : ProperCircle) (o : Homogeneous3)
    (hnondegenerate : properCirclePencilDeterminant c o ≠ 0) :
    (∀ P Q R : RealProjectiveOnePoint,
      RealProjectiveCyclic P Q R →
        RealProjectiveCyclic
          (properCirclePencilGL c o hnondegenerate • P)
          (properCirclePencilGL c o hnondegenerate • Q)
          (properCirclePencilGL c o hnondegenerate • R)) ∨
    (∀ P Q R : RealProjectiveOnePoint,
      RealProjectiveCyclic P Q R →
        RealProjectiveCyclic
          (properCirclePencilGL c o hnondegenerate • P)
          (properCirclePencilGL c o hnondegenerate • R)
          (properCirclePencilGL c o hnondegenerate • Q)) :=
  realConicPencil_preserves_or_reverses_cyclicOrder
    (properCirclePencilA c o)
    (properCirclePencilB c o)
    (properCirclePencilC c o) hnondegenerate

end Erdos506.Incidence
