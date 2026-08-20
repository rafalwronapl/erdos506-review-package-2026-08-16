import Erdos506.Incidence.SixConicSignaturesOnHostCap
import Erdos506.Incidence.CompleteQuadrangle
import Erdos506.Incidence.SixCirclePrinciple
import Mathlib.Tactic

/-!
# The unconditional four-outsider six-conic bound

This module proves the geometric input `U17` without using an event-principle
field.  The key positive object is the intersection of an outsider secant in
the full circle lift with the plane of the selected circle.  In the affine
coordinates already used by the radical-axis API it is represented by

`Fγ(q) • (p,1) - Fγ(p) • (q,1)`.

After division by the nonzero powers `Fγ`, this is the direction between two
normalized circle-lift points.  Three distinct normalized lifts are never
affinely collinear.  Thus the three opposite-edge repetitions of a complete
quadrangle cannot all occur: the first two force a parallelogram, while the
third would identify its two diagonal directions in characteristic zero.
-/

namespace Erdos506.Incidence

open Erdos506.Finite
open Erdos506.V1
open Erdos506.V4
open Matrix
open scoped BigOperators LinearAlgebra.Projectivization

universe u

/-! ## Normalized circle-lift coordinates -/

private noncomputable def sixConicCirclePower
    (c : ProperCircle) (p : Point2) : ℝ :=
  Erdos506.V3.circleEquation (Erdos506.V3.properCircleEquationA c)
    (Erdos506.V3.properCircleEquationB c)
    (Erdos506.V3.properCircleEquationC c) p

private theorem sixConicCirclePower_eq_zero_iff
    (c : ProperCircle) (p : Point2) :
    sixConicCirclePower c p = 0 ↔ p ∈ (c.1 : Set Point2) := by
  exact (Erdos506.V3.mem_properCircle_iff_equation c p).symm

private theorem sixConicCirclePower_ne_zero_of_not_mem
    (c : ProperCircle) {p : Point2} (hp : p ∉ (c.1 : Set Point2)) :
    sixConicCirclePower c p ≠ 0 := by
  intro hzero
  exact hp ((sixConicCirclePower_eq_zero_iff c p).mp hzero)

/-- Coordinates on the affine hyperplane complementary to the selected
circle plane in the four-dimensional circle lift. -/
private noncomputable def sixConicNormalizedLift
    (c : ProperCircle) (p : Point2) : Homogeneous3 :=
  (sixConicCirclePower c p)⁻¹ • homogeneousLift p

/-- The selected-circle secant vector.  Its projective class is the common
radical-axis centre attached to a full outsider edge. -/
private noncomputable def sixConicSecantVector
    (c : ProperCircle) (p q : Point2) : Homogeneous3 :=
  sixConicCirclePower c q • homogeneousLift p -
    sixConicCirclePower c p • homogeneousLift q

private theorem sixConicSecantVector_ne_zero
    (c : ProperCircle) {p q : Point2} (hpq : p ≠ q)
    (hp : sixConicCirclePower c p ≠ 0)
    (_hq : sixConicCirclePower c q ≠ 0) :
    sixConicSecantVector c p q ≠ 0 := by
  intro hzero
  have hlast := congrFun hzero (2 : Fin 3)
  have hpowers : sixConicCirclePower c q = sixConicCirclePower c p := by
    simp only [sixConicSecantVector, Pi.sub_apply, Pi.smul_apply,
      smul_eq_mul, homogeneousLift_two, mul_one, Pi.zero_apply] at hlast
    exact sub_eq_zero.mp hlast
  apply hpq
  ext i
  fin_cases i
  · have hcoord := congrFun hzero (0 : Fin 3)
    have hmul : sixConicCirclePower c p * (p 0 - q 0) = 0 := by
      simp only [sixConicSecantVector, Pi.sub_apply, Pi.smul_apply,
        smul_eq_mul, homogeneousLift_zero, Pi.zero_apply, hpowers] at hcoord
      calc
        sixConicCirclePower c p * (p 0 - q 0) =
            sixConicCirclePower c p * p 0 -
              sixConicCirclePower c p * q 0 := by ring
        _ = 0 := hcoord
    exact sub_eq_zero.mp ((mul_eq_zero.mp hmul).resolve_left hp)
  · have hcoord := congrFun hzero (1 : Fin 3)
    have hmul : sixConicCirclePower c p * (p 1 - q 1) = 0 := by
      simp only [sixConicSecantVector, Pi.sub_apply, Pi.smul_apply,
        smul_eq_mul, homogeneousLift_one, Pi.zero_apply, hpowers] at hcoord
      calc
        sixConicCirclePower c p * (p 1 - q 1) =
            sixConicCirclePower c p * p 1 -
              sixConicCirclePower c p * q 1 := by ring
        _ = 0 := hcoord
    exact sub_eq_zero.mp ((mul_eq_zero.mp hmul).resolve_left hp)

private theorem sixConicSecantVector_eq_normalized_sub
    (c : ProperCircle) {p q : Point2}
    (hp : sixConicCirclePower c p ≠ 0)
    (hq : sixConicCirclePower c q ≠ 0) :
    sixConicSecantVector c p q =
      (sixConicCirclePower c p * sixConicCirclePower c q) •
        (sixConicNormalizedLift c p - sixConicNormalizedLift c q) := by
  ext i
  simp only [sixConicSecantVector, sixConicNormalizedLift,
    Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
  field_simp [hp, hq]

private noncomputable def sixConicSecantCenter
    (c : ProperCircle) (p q : Point2) (hpq : p ≠ q)
    (hp : sixConicCirclePower c p ≠ 0)
    (hq : sixConicCirclePower c q ≠ 0) : RealProjectivePlane :=
  Projectivization.mk ℝ (sixConicSecantVector c p q)
    (sixConicSecantVector_ne_zero c hpq hp hq)

private theorem sixConicSecantCenter_ne_left
    (c : ProperCircle) {p q : Point2} (hpq : p ≠ q)
    (hp : sixConicCirclePower c p ≠ 0)
    (hq : sixConicCirclePower c q ≠ 0) :
    sixConicSecantCenter c p q hpq hp hq ≠ projectivePoint p := by
  intro heq
  have hscaled : ∃ a : ℝ,
      a • homogeneousLift p = sixConicSecantVector c p q :=
    (Projectivization.mk_eq_mk_iff' ℝ
      (sixConicSecantVector c p q) (homogeneousLift p)
      (sixConicSecantVector_ne_zero c hpq hp hq)
      (homogeneousLift_ne_zero p)).mp (by
        simpa [sixConicSecantCenter, projectivePoint] using heq)
  obtain ⟨a, ha⟩ := hscaled
  have hlast := congrFun ha (2 : Fin 3)
  have haValue : a = sixConicCirclePower c q -
      sixConicCirclePower c p := by
    simpa [sixConicSecantVector, Pi.smul_apply] using hlast
  have hcoord0 := congrFun ha (0 : Fin 3)
  have hcoord1 := congrFun ha (1 : Fin 3)
  apply hpq
  ext i
  fin_cases i
  · have hmul : sixConicCirclePower c p * (p 0 - q 0) = 0 := by
      simp only [sixConicSecantVector, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
        homogeneousLift_zero] at hcoord0
      rw [haValue] at hcoord0
      calc
        sixConicCirclePower c p * (p 0 - q 0) =
            (sixConicCirclePower c q * p 0 -
                sixConicCirclePower c p * q 0) -
              (sixConicCirclePower c q -
                sixConicCirclePower c p) * p 0 := by ring
        _ = 0 := by rw [← hcoord0]; ring
    exact sub_eq_zero.mp ((mul_eq_zero.mp hmul).resolve_left hp)
  · have hmul : sixConicCirclePower c p * (p 1 - q 1) = 0 := by
      simp only [sixConicSecantVector, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
        homogeneousLift_one] at hcoord1
      rw [haValue] at hcoord1
      calc
        sixConicCirclePower c p * (p 1 - q 1) =
            (sixConicCirclePower c q * p 1 -
                sixConicCirclePower c p * q 1) -
              (sixConicCirclePower c q -
                sixConicCirclePower c p) * p 1 := by ring
        _ = 0 := by rw [← hcoord1]; ring
    exact sub_eq_zero.mp ((mul_eq_zero.mp hmul).resolve_left hp)

private theorem sixConicSecantCenter_orthogonal_line
    (c : ProperCircle) {p q : Point2} (hpq : p ≠ q)
    (hp : sixConicCirclePower c p ≠ 0)
    (hq : sixConicCirclePower c q ≠ 0) :
    Projectivization.orthogonal
      (sixConicSecantCenter c p q hpq hp hq)
      (projectiveLine p q hpq) := by
  change sixConicSecantVector c p q ⬝ᵥ lineCovector p q = 0
  rw [sixConicSecantVector, sub_dotProduct, smul_dotProduct,
    smul_dotProduct]
  have hpLine := homogeneousIncident_lineCovector_left p q
  have hqLine := homogeneousIncident_lineCovector_right p q
  change homogeneousLift p ⬝ᵥ lineCovector p q = 0 at hpLine
  change homogeneousLift q ⬝ᵥ lineCovector p q = 0 at hqLine
  rw [hpLine, hqLine]
  ring

private theorem sixConicSecantCenter_orthogonal_radicalAxis_iff
    (gamma K : ProperCircle) (hgammaK : gamma ≠ K)
    {p q : Point2} (hpq : p ≠ q)
    (hpGamma : sixConicCirclePower gamma p ≠ 0)
    (hqGamma : sixConicCirclePower gamma q ≠ 0)
    (hpK : p ∈ (K.1 : Set Point2)) :
    Projectivization.orthogonal
        (sixConicSecantCenter gamma p q hpq hpGamma hqGamma)
        (projectiveRadicalAxis gamma K hgammaK) ↔
      q ∈ (K.1 : Set Point2) := by
  have hpKzero : sixConicCirclePower K p = 0 :=
    (sixConicCirclePower_eq_zero_iff K p).2 hpK
  rw [sixConicSecantCenter, projectiveRadicalAxis,
    Projectivization.orthogonal_mk]
  rw [sixConicSecantVector, sub_dotProduct, smul_dotProduct,
    smul_dotProduct,
    homogeneousLift_dot_radicalAxisCovector,
    homogeneousLift_dot_radicalAxisCovector]
  change
    sixConicCirclePower gamma q *
          (sixConicCirclePower gamma p - sixConicCirclePower K p) -
        sixConicCirclePower gamma p *
          (sixConicCirclePower gamma q - sixConicCirclePower K q) = 0 ↔ _
  rw [hpKzero]
  constructor
  · intro h
    apply (sixConicCirclePower_eq_zero_iff K q).1
    have hmul : sixConicCirclePower gamma p *
        sixConicCirclePower K q = 0 := by nlinarith
    exact (mul_eq_zero.mp hmul).resolve_left hpGamma
  · intro hqK
    rw [(sixConicCirclePower_eq_zero_iff K q).2 hqK]
    ring

/-! ## The real circle lift has no affine three-point line -/

private theorem sixConicCirclePower_affine_combination
    (c : ProperCircle) (p q : Point2) (a b : ℝ) (hab : a + b = 1) :
    sixConicCirclePower c (a • p + b • q) =
      a * sixConicCirclePower c p + b * sixConicCirclePower c q -
        a * b * Erdos506.V3.directionSq (p - q) := by
  simp only [sixConicCirclePower, Erdos506.V3.circleEquation,
    Erdos506.V3.properCircleEquationA,
    Erdos506.V3.properCircleEquationB,
    Erdos506.V3.properCircleEquationC, Erdos506.V3.directionSq]
  change
    (a * p 0 + b * q 0) ^ 2 + (a * p 1 + b * q 1) ^ 2 +
          (-2 * c.1.center 0) * (a * p 0 + b * q 0) +
          (-2 * c.1.center 1) * (a * p 1 + b * q 1) +
          (c.1.center 0 ^ 2 + c.1.center 1 ^ 2 - c.1.radius ^ 2) =
      a * (p 0 ^ 2 + p 1 ^ 2 + (-2 * c.1.center 0) * p 0 +
          (-2 * c.1.center 1) * p 1 +
          (c.1.center 0 ^ 2 + c.1.center 1 ^ 2 - c.1.radius ^ 2)) +
        b * (q 0 ^ 2 + q 1 ^ 2 + (-2 * c.1.center 0) * q 0 +
          (-2 * c.1.center 1) * q 1 +
          (c.1.center 0 ^ 2 + c.1.center 1 ^ 2 - c.1.radius ^ 2)) -
        a * b * ((p 0 - q 0) ^ 2 + (p 1 - q 1) ^ 2)
  have hbEq : b = 1 - a := by linarith
  rw [hbEq]
  ring

private theorem sixConicNormalizedLift_injective
    (c : ProperCircle) {p q : Point2}
    (_hp : sixConicCirclePower c p ≠ 0)
    (hq : sixConicCirclePower c q ≠ 0)
    (h : sixConicNormalizedLift c p = sixConicNormalizedLift c q) :
    p = q := by
  have hlast := congrFun h (2 : Fin 3)
  have hpqPower : sixConicCirclePower c p = sixConicCirclePower c q := by
    simp only [sixConicNormalizedLift, Pi.smul_apply, smul_eq_mul,
      homogeneousLift_two, mul_one] at hlast
    exact inv_injective hlast
  ext i
  fin_cases i
  · have hcoord := congrFun h (0 : Fin 3)
    simp only [sixConicNormalizedLift, Pi.smul_apply, smul_eq_mul,
      homogeneousLift_zero, hpqPower] at hcoord
    exact mul_left_cancel₀ (inv_ne_zero hq) hcoord
  · have hcoord := congrFun h (1 : Fin 3)
    simp only [sixConicNormalizedLift, Pi.smul_apply, smul_eq_mul,
      homogeneousLift_one, hpqPower] at hcoord
    exact mul_left_cancel₀ (inv_ne_zero hq) hcoord

/-- Three distinct normalized real circle lifts are affinely noncollinear.
This is the real no-line-on-the-circle-lift statement in the exact affine
chart needed below. -/
private theorem sixConicNormalizedLift_not_parallel
    (c : ProperCircle) {p q r : Point2}
    (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r)
    (hp : sixConicCirclePower c p ≠ 0)
    (hq : sixConicCirclePower c q ≠ 0)
    (hr : sixConicCirclePower c r ≠ 0) :
    ¬ ∃ t : ℝ,
      sixConicNormalizedLift c r - sixConicNormalizedLift c p =
        t • (sixConicNormalizedLift c q - sixConicNormalizedLift c p) := by
  rintro ⟨t, ht⟩
  let gp := sixConicCirclePower c p
  let gq := sixConicCirclePower c q
  let gr := sixConicCirclePower c r
  let a := (1 - t) * gr / gp
  let b := t * gr / gq
  have ht0 := congrFun ht (0 : Fin 3)
  have ht1 := congrFun ht (1 : Fin 3)
  have ht2 := congrFun ht (2 : Fin 3)
  have hab : a + b = 1 := by
    dsimp only [a, b, gp, gq, gr]
    simp only [sixConicNormalizedLift, Pi.sub_apply, Pi.smul_apply,
      smul_eq_mul, homogeneousLift_two] at ht2
    field_simp [hp, hq, hr] at ht2 ⊢
    nlinarith
  have hrcombo : r = a • p + b • q := by
    apply point2_eq_of_apply_zero_one
    · dsimp only [a, b, gp, gq, gr]
      simp only [sixConicNormalizedLift, Pi.sub_apply, Pi.smul_apply,
        smul_eq_mul, homogeneousLift_zero] at ht0
      change r 0 =
        (1 - t) * sixConicCirclePower c r /
              sixConicCirclePower c p * p 0 +
          t * sixConicCirclePower c r /
              sixConicCirclePower c q * q 0
      field_simp [hp, hq, hr] at ht0 ⊢
      nlinarith
    · dsimp only [a, b, gp, gq, gr]
      simp only [sixConicNormalizedLift, Pi.sub_apply, Pi.smul_apply,
        smul_eq_mul, homogeneousLift_one] at ht1
      change r 1 =
        (1 - t) * sixConicCirclePower c r /
              sixConicCirclePower c p * p 1 +
          t * sixConicCirclePower c r /
              sixConicCirclePower c q * q 1
      field_simp [hp, hq, hr] at ht1 ⊢
      nlinarith
  have hpower := sixConicCirclePower_affine_combination c p q a b hab
  rw [← hrcombo] at hpower
  have hlinearPower :
      a * sixConicCirclePower c p + b * sixConicCirclePower c q =
        sixConicCirclePower c r := by
    dsimp only [a, b, gp, gq, gr]
    field_simp [hp, hq]
    ring
  have hfactor : a * b * Erdos506.V3.directionSq (p - q) = 0 := by
    linarith [hpower, hlinearPower]
  have habzero : a = 0 ∨ b = 0 := by
    rcases mul_eq_zero.mp hfactor with hab0 | hdir
    · exact mul_eq_zero.mp hab0
    · exact (Erdos506.V3.directionSq_sub_ne_zero hpq hdir).elim
  rcases habzero with ha | hb
  · have htOne : t = 1 := by
      dsimp only [a, gp, gr] at ha
      field_simp [hp] at ha
      have haZero : (1 - t) * sixConicCirclePower c r = 0 := by
        linarith [ha]
      exact (sub_eq_zero.mp ((mul_eq_zero.mp haZero).resolve_right hr)).symm
    apply hqr
    have := ht
    rw [htOne, one_smul] at this
    exact (sixConicNormalizedLift_injective c hr hq
      (sub_left_injective this)).symm
  · have htZero : t = 0 := by
      dsimp only [b, gq, gr] at hb
      field_simp [hq] at hb
      have hbZero : t * sixConicCirclePower c r = 0 := by
        linarith [hb]
      exact (mul_eq_zero.mp hbZero).resolve_right hr
    apply hpr
    have := ht
    rw [htZero, zero_smul] at this
    exact (sixConicNormalizedLift_injective c hr hp
      (sub_eq_zero.mp this)).symm

private theorem two_coefficients_eq_zero_of_not_parallel
    {x y : Homogeneous3} (hx : x ≠ 0)
    (hy : ¬ ∃ t : ℝ, y = t • x)
    {a b : ℝ} (h : a • x + b • y = 0) : a = 0 ∧ b = 0 := by
  by_cases hb : b = 0
  · subst b
    simp only [zero_smul, add_zero] at h
    exact ⟨(smul_eq_zero.mp h).resolve_right hx, rfl⟩
  · exfalso
    apply hy
    refine ⟨-a / b, ?_⟩
    ext i
    have hi := congrFun h i
    simp only [Pi.add_apply, Pi.smul_apply, Pi.zero_apply,
      smul_eq_mul] at hi ⊢
    field_simp [hb]
    nlinarith

/-- Affine complete-quadrangle obstruction: three opposite side pairs of a
nondegenerate quadrangle cannot all have parallel directions over `ℝ`. -/
private theorem affineCompleteQuadrangle_not_three_parallel
    {a b c d : Homogeneous3}
    (hab : a ≠ b)
    (hnoncollinear : ¬ ∃ t : ℝ, c - a = t • (b - a))
    (hAB : ∃ r : ℝ, r ≠ 0 ∧ a - b = r • (c - d))
    (hAC : ∃ s : ℝ, s ≠ 0 ∧ a - c = s • (b - d))
    (hAD : ∃ t : ℝ, a - d = t • (b - c)) : False := by
  obtain ⟨r, hr, hAB⟩ := hAB
  obtain ⟨s, hs, hAC⟩ := hAC
  obtain ⟨t, hAD⟩ := hAD
  let x := b - a
  let y := c - a
  let z := d - a
  have hx : x ≠ 0 := sub_ne_zero.mpr hab.symm
  have hy : ¬ ∃ k : ℝ, y = k • x := by
    simpa [x, y] using hnoncollinear
  have hABraw : -x = r • (y - z) := by
    calc
      -x = a - b := by dsimp only [x]; module
      _ = r • (c - d) := hAB
      _ = r • (y - z) := by dsimp only [y, z]; module
  have hACraw : -y = s • (x - z) := by
    calc
      -y = a - c := by dsimp only [y]; module
      _ = s • (b - d) := hAC
      _ = s • (x - z) := by dsimp only [x, z]; module
  have hAB' : (-1 : ℝ) • x + (-r) • y + r • z = 0 := by
    calc
      (-1 : ℝ) • x + (-r) • y + r • z =
          -x - r • (y - z) := by module
      _ = 0 := by rw [hABraw]; module
  have hAC' : (-s) • x + (-1 : ℝ) • y + s • z = 0 := by
    calc
      (-s) • x + (-1 : ℝ) • y + s • z =
          -y - s • (x - z) := by module
      _ = 0 := by rw [hACraw]; module
  have helim : (s * (r - 1)) • x + (r * (1 - s)) • y = 0 := by
    calc
      _ = s • ((-1 : ℝ) • x + (-r) • y + r • z) -
          r • ((-s) • x + (-1 : ℝ) • y + s • z) := by module
      _ = 0 := by rw [hAB', hAC']; simp
  have hcoeff := two_coefficients_eq_zero_of_not_parallel hx hy helim
  have hrOne : r = 1 := by
    have : r - 1 = 0 := (mul_eq_zero.mp hcoeff.1).resolve_left hs
    linarith
  have hsOne : s = 1 := by
    have : 1 - s = 0 := (mul_eq_zero.mp hcoeff.2).resolve_left hr
    linarith
  have hz : z = x + y := by
    rw [hrOne] at hAB'
    apply sub_eq_zero.mp
    calc
      z - (x + y) =
          (-1 : ℝ) • x + (-1 : ℝ) • y + 1 • z := by module
      _ = 0 := by simpa only [one_smul] using hAB'
  have hADraw : -z = t • (x - y) := by
    calc
      -z = a - d := by dsimp only [z]; module
      _ = t • (b - c) := hAD
      _ = t • (x - y) := by dsimp only [x, y]; module
  have hAD' : (-1 - t) • x + (-1 + t) • y = 0 := by
    calc
      (-1 - t) • x + (-1 + t) • y =
          -z - t • (x - y) := by rw [hz]; module
      _ = 0 := by rw [hADraw]; module
  have hlast := two_coefficients_eq_zero_of_not_parallel hx hy hAD'
  linarith [hlast.1, hlast.2]

/-! ## Full-edge centres and normalized outsider secants -/

private theorem projectivePoint_orthogonal_projectiveLine_iff_mem_affineSpan
    {p q r : Point2} (hpq : p ≠ q) :
    Projectivization.orthogonal (projectivePoint r)
        (projectiveLine p q hpq) ↔
      r ∈ affineSpan ℝ ({p, q} : Set Point2) := by
  simpa only [projectivePoint, projectiveLine,
    Projectivization.orthogonal_mk, homogeneousIncident] using
      (homogeneousIncident_lineCovector_iff_mem_affineSpan hpq)

private theorem sixConicPairCircle_ne_gamma
    {α : Type u} [Fintype α] [DecidableEq α]
    {cfg : Configuration α}
    {gamma K : Erdos506.V1.DeterminedCircle cfg}
    {e : Finset α}
    (hgamma : (circleTrace cfg gamma.1).card = 6)
    (hK : K ∈ sixConicPairCircles cfg gamma e) :
    gamma ≠ K := by
  intro hEq
  subst K
  have hpair := (mem_sixConicPairCircles.mp hK).2
  rw [Finset.inter_self, hgamma] at hpair
  omega

/-- The pencil centre constructed from the three marked chords of a full
edge is the projective class of its selected-circle secant vector. -/
private theorem sixConicFullEdgeCenter_eq_secantCenter
    {α : Type u} [Fintype α] [DecidableEq α]
    (cfg : Configuration α)
    (gamma : Erdos506.V1.DeterminedCircle cfg)
    (hgamma : (circleTrace cfg gamma.1).card = 6)
    (X : Finset α)
    (hdisjoint : Disjoint (circleTrace cfg gamma.1) X)
    {e : Finset α} (heFull : e ∈ sixConicFullEdges cfg gamma X)
    {x y : α} (hxE : x ∈ e) (hyE : y ∈ e) (hxy : x ≠ y)
    (hxyCfg : cfg x ≠ cfg y)
    (hxPower : sixConicCirclePower gamma.1 (cfg x) ≠ 0)
    (hyPower : sixConicCirclePower gamma.1 (cfg y) ≠ 0) :
    sixConicFullEdgeCenter cfg gamma hgamma X hdisjoint heFull =
      sixConicSecantCenter gamma.1 (cfg x) (cfg y)
        hxyCfg hxPower hyPower := by
  classical
  have heSpec := mem_sixConicFullEdges.mp heFull
  have hePow := Finset.mem_powersetCard.mp heSpec.1
  have heCard : e.card = 2 := hePow.2
  let pe : KSubset α 2 := ⟨e, heCard⟩
  have hCcard : (sixConicPairCircles cfg gamma e).card = 3 := by
    change sixConicPairWeight cfg gamma e = 3
    exact heSpec.2
  have hCnonempty : (sixConicPairCircles cfg gamma e).Nonempty :=
    Finset.card_pos.mp (by omega)
  obtain ⟨K, hK⟩ := hCnonempty
  have hgammaK : gamma ≠ K :=
    sixConicPairCircle_ne_gamma hgamma hK
  have hgammaKcoe : gamma.1 ≠ K.1 :=
    determinedCircle_coe_ne_of_ne hgammaK
  have heK : e ⊆ circleTrace cfg K.1 :=
    (mem_sixConicPairCircles.mp hK).1
  have hxK : cfg x ∈ (K.1.1 : Set Point2) :=
    mem_circleTrace.mp (heK hxE)
  have hyK : cfg y ∈ (K.1.1 : Set Point2) :=
    mem_circleTrace.mp (heK hyE)
  have hxX : x ∈ X := hePow.1 hxE
  have hxNotGamma : cfg x ∉ (gamma.1.1 : Set Point2) := by
    intro hxGamma
    exact Finset.disjoint_left.mp hdisjoint
      (mem_circleTrace.mpr hxGamma) hxX
  let outsiderLine := projectiveChordLine cfg pe
  let hostAxis := projectiveRadicalAxis gamma.1 K.1 hgammaKcoe
  have hlineAxis : outsiderLine ≠ hostAxis := by
    dsimp only [outsiderLine, hostAxis]
    exact projectiveChordLine_ne_projectiveRadicalAxis_of_endpoint
      cfg gamma.1 K.1 hgammaKcoe pe hxE
        (not_projectivePoint_orthogonal_projectiveRadicalAxis_of_not_mem_mem
          hgammaKcoe hxNotGamma hxK)
  have hcenterLine : Projectivization.orthogonal
      (sixConicFullEdgeCenter cfg gamma hgamma X hdisjoint heFull)
      outsiderLine := by
    dsimp only [outsiderLine]
    exact sixConicFullEdgeCenter_on_outsiderChord
      cfg gamma hgamma X hdisjoint heFull
  have hcenterAxis : Projectivization.orthogonal
      (sixConicFullEdgeCenter cfg gamma hgamma X hdisjoint heFull)
      hostAxis := by
    dsimp only [hostAxis]
    exact sixConicFullEdgeCenter_on_circleHostAxis
      cfg gamma hgamma X hdisjoint heFull K hgammaK heK
  have hchordEq : outsiderLine =
      projectiveLine (cfg x) (cfg y) hxyCfg := by
    dsimp only [outsiderLine]
    exact projectiveChordLine_eq_projectiveLine_of_mem
      cfg pe hxE hyE hxy
  have hsecantLine : Projectivization.orthogonal
      (sixConicSecantCenter gamma.1 (cfg x) (cfg y)
        hxyCfg hxPower hyPower) outsiderLine := by
    rw [hchordEq]
    exact sixConicSecantCenter_orthogonal_line
      gamma.1 hxyCfg hxPower hyPower
  have hsecantAxis : Projectivization.orthogonal
      (sixConicSecantCenter gamma.1 (cfg x) (cfg y)
        hxyCfg hxPower hyPower) hostAxis := by
    dsimp only [hostAxis]
    exact (sixConicSecantCenter_orthogonal_radicalAxis_iff
      gamma.1 K.1 hgammaKcoe hxyCfg hxPower hyPower hxK).2 hyK
  calc
    sixConicFullEdgeCenter cfg gamma hgamma X hdisjoint heFull =
        Projectivization.cross outsiderLine hostAxis :=
      projectiveCovector_eq_cross_of_orthogonal hlineAxis
        (Projectivization.orthogonal_comm.mp hcenterLine)
        (Projectivization.orthogonal_comm.mp hcenterAxis)
    _ = sixConicSecantCenter gamma.1 (cfg x) (cfg y)
          hxyCfg hxPower hyPower :=
      (projectiveCovector_eq_cross_of_orthogonal hlineAxis
        (Projectivization.orthogonal_comm.mp hsecantLine)
        (Projectivization.orthogonal_comm.mp hsecantAxis)).symm

/-- Equal full signatures have the same projective pencil centre. -/
private theorem sixConicFullEdgeCenters_eq_of_signature_eq
    {α : Type u} [Fintype α] [DecidableEq α]
    (cfg : Configuration α)
    (gamma : Erdos506.V1.DeterminedCircle cfg)
    (hgamma : (circleTrace cfg gamma.1).card = 6)
    (X : Finset α)
    (hdisjoint : Disjoint (circleTrace cfg gamma.1) X)
    {e f : Finset α}
    (heFull : e ∈ sixConicFullEdges cfg gamma X)
    (hfFull : f ∈ sixConicFullEdges cfg gamma X)
    (hsignature :
      sixConicSignature cfg gamma e = sixConicSignature cfg gamma f) :
    sixConicFullEdgeCenter cfg gamma hgamma X hdisjoint heFull =
      sixConicFullEdgeCenter cfg gamma hgamma X hdisjoint hfFull := by
  classical
  have heSpec := mem_sixConicFullEdges.mp heFull
  have hePow := Finset.mem_powersetCard.mp heSpec.1
  have heDisjointGamma : Disjoint e (circleTrace cfg gamma.1) :=
    hdisjoint.symm.mono_left hePow.1
  have hsignatureCard : (sixConicSignature cfg gamma e).card = 3 := by
    rw [card_sixConicSignature hePow.2 heDisjointGamma, heSpec.2]
  obtain ⟨p, q, r, hpq, hpr, hqr, hsignatureEq⟩ :=
    Finset.card_eq_three.mp hsignatureCard
  have hpE : p ∈ sixConicSignature cfg gamma e := by
    rw [hsignatureEq]
    simp
  have hqE : q ∈ sixConicSignature cfg gamma e := by
    rw [hsignatureEq]
    simp
  have hpF : p ∈ sixConicSignature cfg gamma f := by
    rw [← hsignature]
    exact hpE
  have hqF : q ∈ sixConicSignature cfg gamma f := by
    rw [← hsignature]
    exact hqE
  have hpData := sixConicSignature_pair hpE
  have hqData := sixConicSignature_pair hqE
  have hpqDisjoint : Disjoint p q :=
    sixConicSignature_pairwiseDisjoint hePow.2 heDisjointGamma
      hpE hqE hpq
  let ep : KSubset α 2 := ⟨p, hpData.1⟩
  let eq : KSubset α 2 := ⟨q, hqData.1⟩
  let a : {x : α // x ∈ circleTrace cfg gamma.1} :=
    ⟨chordLabel ep 0, hpData.2 (chordLabel_mem ep 0)⟩
  let b : {x : α // x ∈ circleTrace cfg gamma.1} :=
    ⟨chordLabel ep 1, hpData.2 (chordLabel_mem ep 1)⟩
  let c : {x : α // x ∈ circleTrace cfg gamma.1} :=
    ⟨chordLabel eq 0, hqData.2 (chordLabel_mem eq 0)⟩
  let d : {x : α // x ∈ circleTrace cfg gamma.1} :=
    ⟨chordLabel eq 1, hqData.2 (chordLabel_mem eq 1)⟩
  have hab : a ≠ b := by
    intro hab
    apply chordLabel_zero_ne_one ep
    simpa only [a, b] using congrArg Subtype.val hab
  have hcd : c ≠ d := by
    intro hcd
    apply chordLabel_zero_ne_one eq
    simpa only [c, d] using congrArg Subtype.val hcd
  have hac : a ≠ c := by
    intro hac
    have hval : chordLabel ep 0 = chordLabel eq 0 := by
      simpa only [a, c] using congrArg Subtype.val hac
    exact Finset.disjoint_left.mp hpqDisjoint
      (chordLabel_mem ep 0) (by rw [hval]; exact chordLabel_mem eq 0)
  have had : a ≠ d := by
    intro had
    have hval : chordLabel ep 0 = chordLabel eq 1 := by
      simpa only [a, d] using congrArg Subtype.val had
    exact Finset.disjoint_left.mp hpqDisjoint
      (chordLabel_mem ep 0) (by rw [hval]; exact chordLabel_mem eq 1)
  have habVal : a.1 ≠ b.1 := by
    intro hval
    apply hab
    apply Subtype.ext
    exact hval
  have hcdVal : c.1 ≠ d.1 := by
    intro hval
    apply hcd
    apply Subtype.ext
    exact hval
  have hacVal : a.1 ≠ c.1 := by
    intro hval
    apply hac
    apply Subtype.ext
    exact hval
  have hadVal : a.1 ≠ d.1 := by
    intro hval
    apply had
    apply Subtype.ext
    exact hval
  have hpPair : p = {a.1, b.1} := by
    calc
      p = ep.1 := rfl
      _ = {chordLabel ep 0, chordLabel ep 1} := chordSupport_eq_pair ep
      _ = {a.1, b.1} := by rfl
  have hqPair : q = {c.1, d.1} := by
    calc
      q = eq.1 := rfl
      _ = {chordLabel eq 0, chordLabel eq 1} := chordSupport_eq_pair eq
      _ = {c.1, d.1} := by rfl
  have hpE' : {a.1, b.1} ∈ sixConicSignature cfg gamma e := by
    rw [← hpPair]
    exact hpE
  have hqE' : {c.1, d.1} ∈ sixConicSignature cfg gamma e := by
    rw [← hqPair]
    exact hqE
  have hpF' : {a.1, b.1} ∈ sixConicSignature cfg gamma f := by
    rw [← hpPair]
    exact hpF
  have hqF' : {c.1, d.1} ∈ sixConicSignature cfg gamma f := by
    rw [← hqPair]
    exact hqF
  let lineP := projectiveLine (cfg a.1) (cfg b.1)
    (cfg.injective.ne habVal)
  let lineQ := projectiveLine (cfg c.1) (cfg d.1)
    (cfg.injective.ne hcdVal)
  have hlines : lineP ≠ lineQ := by
    intro hEq
    have hnot : ¬Projectivization.orthogonal
        (projectivePoint (cfg a.1)) lineQ := by
      dsimp only [lineQ]
      exact properCircle_projectivePoint_not_on_chord gamma.1
        (mem_circleTrace.mp c.2) (mem_circleTrace.mp d.2)
        (mem_circleTrace.mp a.2)
        (cfg.injective.ne hcdVal)
        (cfg.injective.ne hacVal.symm)
        (cfg.injective.ne hadVal.symm)
    apply hnot
    rw [← hEq]
    dsimp only [lineP]
    exact Projectivization.orthogonal_comm.mp
      (projectiveLine_orthogonal_left
        (cfg.injective.ne habVal))
  have heP : Projectivization.orthogonal
      (sixConicFullEdgeCenter cfg gamma hgamma X hdisjoint heFull)
      lineP := by
    dsimp only [lineP]
    exact sixConicFullEdgeCenter_on_signatureChord
      cfg gamma hgamma X hdisjoint heFull a b hab hpE'
  have heQ : Projectivization.orthogonal
      (sixConicFullEdgeCenter cfg gamma hgamma X hdisjoint heFull)
      lineQ := by
    dsimp only [lineQ]
    exact sixConicFullEdgeCenter_on_signatureChord
      cfg gamma hgamma X hdisjoint heFull c d hcd hqE'
  have hfP : Projectivization.orthogonal
      (sixConicFullEdgeCenter cfg gamma hgamma X hdisjoint hfFull)
      lineP := by
    dsimp only [lineP]
    exact sixConicFullEdgeCenter_on_signatureChord
      cfg gamma hgamma X hdisjoint hfFull a b hab hpF'
  have hfQ : Projectivization.orthogonal
      (sixConicFullEdgeCenter cfg gamma hgamma X hdisjoint hfFull)
      lineQ := by
    dsimp only [lineQ]
    exact sixConicFullEdgeCenter_on_signatureChord
      cfg gamma hgamma X hdisjoint hfFull c d hcd hqF'
  calc
    sixConicFullEdgeCenter cfg gamma hgamma X hdisjoint heFull =
        Projectivization.cross lineP lineQ :=
      projectiveCovector_eq_cross_of_orthogonal hlines
        (Projectivization.orthogonal_comm.mp heP)
        (Projectivization.orthogonal_comm.mp heQ)
    _ = sixConicFullEdgeCenter cfg gamma hgamma X hdisjoint hfFull :=
      (projectiveCovector_eq_cross_of_orthogonal hlines
        (Projectivization.orthogonal_comm.mp hfP)
        (Projectivization.orthogonal_comm.mp hfQ)).symm

private theorem sixConicNormalized_sub_parallel_of_secantCenters_eq
    (gamma : ProperCircle) {p q r s : Point2}
    (hpq : p ≠ q) (hrs : r ≠ s)
    (hp : sixConicCirclePower gamma p ≠ 0)
    (hq : sixConicCirclePower gamma q ≠ 0)
    (hr : sixConicCirclePower gamma r ≠ 0)
    (hs : sixConicCirclePower gamma s ≠ 0)
    (hcenters :
      sixConicSecantCenter gamma p q hpq hp hq =
        sixConicSecantCenter gamma r s hrs hr hs) :
    ∃ t : ℝ, t ≠ 0 ∧
      sixConicNormalizedLift gamma p - sixConicNormalizedLift gamma q =
        t • (sixConicNormalizedLift gamma r -
          sixConicNormalizedLift gamma s) := by
  have hscaled : ∃ a : ℝ,
      a • sixConicSecantVector gamma r s =
        sixConicSecantVector gamma p q :=
    (Projectivization.mk_eq_mk_iff' ℝ
      (sixConicSecantVector gamma p q)
      (sixConicSecantVector gamma r s)
      (sixConicSecantVector_ne_zero gamma hpq hp hq)
      (sixConicSecantVector_ne_zero gamma hrs hr hs)).mp (by
        simpa only [sixConicSecantCenter] using hcenters)
  obtain ⟨a, ha⟩ := hscaled
  let t := a *
    (sixConicCirclePower gamma r * sixConicCirclePower gamma s) /
      (sixConicCirclePower gamma p * sixConicCirclePower gamma q)
  have hparallel :
      sixConicNormalizedLift gamma p - sixConicNormalizedLift gamma q =
        t • (sixConicNormalizedLift gamma r -
          sixConicNormalizedLift gamma s) := by
    rw [sixConicSecantVector_eq_normalized_sub gamma hp hq,
      sixConicSecantVector_eq_normalized_sub gamma hr hs] at ha
    ext i
    have hi := congrFun ha i
    dsimp only [t]
    simp only [Pi.smul_apply, smul_eq_mul] at hi ⊢
    field_simp [hp, hq, hr, hs]
    nlinarith
  refine ⟨t, ?_, hparallel⟩
  intro ht
  have hzero :
      sixConicNormalizedLift gamma p - sixConicNormalizedLift gamma q = 0 := by
    rw [hparallel, ht, zero_smul]
  exact hpq (sixConicNormalizedLift_injective gamma hp hq
    (sub_eq_zero.mp hzero))

/-! ## A repeated full signature supplies its four-point host -/

private theorem sixConicEqualSignature_has_host
    {α : Type u} [Fintype α] [DecidableEq α]
    (cfg : Configuration α)
    (gamma : Erdos506.V1.DeterminedCircle cfg)
    (hgamma : (circleTrace cfg gamma.1).card = 6)
    (X : Finset α)
    (hdisjoint : Disjoint (circleTrace cfg gamma.1) X)
    {e f : Finset α}
    (heFull : e ∈ sixConicFullEdges cfg gamma X)
    (hfFull : f ∈ sixConicFullEdges cfg gamma X)
    (hef : e ≠ f)
    (hsignature :
      sixConicSignature cfg gamma e = sixConicSignature cfg gamma f) :
    ∃ H : GeometricBlock cfg,
      e ∪ f ⊆ geometricBlockSupport cfg H := by
  classical
  have heSpec := mem_sixConicFullEdges.mp heFull
  have hfSpec := mem_sixConicFullEdges.mp hfFull
  have hePow := Finset.mem_powersetCard.mp heSpec.1
  have hfPow := Finset.mem_powersetCard.mp hfSpec.1
  have hefDisjoint : Disjoint e f :=
    sixConic_equal_full_signatures_disjoint
      cfg gamma hgamma X hdisjoint heFull hfFull hef hsignature
  obtain ⟨x, y, hxy, heEq⟩ := Finset.card_eq_two.mp hePow.2
  obtain ⟨z, w, hzw, hfEq⟩ := Finset.card_eq_two.mp hfPow.2
  have hxE : x ∈ e := by simp [heEq]
  have hyE : y ∈ e := by simp [heEq]
  have hzF : z ∈ f := by simp [hfEq]
  have hwF : w ∈ f := by simp [hfEq]
  have hcross {a b : α} (ha : a ∈ e) (hb : b ∈ f) : a ≠ b := by
    intro hab
    subst b
    exact Finset.disjoint_left.mp hefDisjoint ha hb
  have hxz : x ≠ z := hcross hxE hzF
  have hxw : x ≠ w := hcross hxE hwF
  have hyz : y ≠ z := hcross hyE hzF
  have hyw : y ≠ w := hcross hyE hwF
  have hxNotGamma : cfg x ∉ (gamma.1.1 : Set Point2) := by
    intro hxGamma
    exact Finset.disjoint_left.mp hdisjoint
      (mem_circleTrace.mpr hxGamma) (hePow.1 hxE)
  have hyNotGamma : cfg y ∉ (gamma.1.1 : Set Point2) := by
    intro hyGamma
    exact Finset.disjoint_left.mp hdisjoint
      (mem_circleTrace.mpr hyGamma) (hePow.1 hyE)
  have hzNotGamma : cfg z ∉ (gamma.1.1 : Set Point2) := by
    intro hzGamma
    exact Finset.disjoint_left.mp hdisjoint
      (mem_circleTrace.mpr hzGamma) (hfPow.1 hzF)
  have hwNotGamma : cfg w ∉ (gamma.1.1 : Set Point2) := by
    intro hwGamma
    exact Finset.disjoint_left.mp hdisjoint
      (mem_circleTrace.mpr hwGamma) (hfPow.1 hwF)
  have hxPower := sixConicCirclePower_ne_zero_of_not_mem
    gamma.1 hxNotGamma
  have hyPower := sixConicCirclePower_ne_zero_of_not_mem
    gamma.1 hyNotGamma
  have hzPower := sixConicCirclePower_ne_zero_of_not_mem
    gamma.1 hzNotGamma
  have hwPower := sixConicCirclePower_ne_zero_of_not_mem
    gamma.1 hwNotGamma
  have hxyCfg : cfg x ≠ cfg y := cfg.injective.ne hxy
  have hzwCfg : cfg z ≠ cfg w := cfg.injective.ne hzw
  have heCenter := sixConicFullEdgeCenter_eq_secantCenter
    cfg gamma hgamma X hdisjoint heFull hxE hyE hxy
      hxyCfg hxPower hyPower
  have hfCenter := sixConicFullEdgeCenter_eq_secantCenter
    cfg gamma hgamma X hdisjoint hfFull hzF hwF hzw
      hzwCfg hzPower hwPower
  have hfullCenters := sixConicFullEdgeCenters_eq_of_signature_eq
    cfg gamma hgamma X hdisjoint heFull hfFull hsignature
  have hsecants :
      sixConicSecantCenter gamma.1 (cfg x) (cfg y)
          hxyCfg hxPower hyPower =
        sixConicSecantCenter gamma.1 (cfg z) (cfg w)
          hzwCfg hzPower hwPower :=
    heCenter.symm.trans (hfullCenters.trans hfCenter)
  let A : KSubset α 3 := ⟨{x, y, z}, by
    simp [hxy, hxz, hyz]⟩
  by_cases hA : IsNoncollinear cfg A.1
  · let K := circleOfTriple cfg A hA
    have hAK : A.1 ⊆ circleTrace cfg K.1 :=
      triple_subset_circleOfTriple cfg A hA
    have hxK : cfg x ∈ (K.1.1 : Set Point2) := by
      apply mem_circleTrace.mp
      apply hAK
      simp [A]
    have hyK : cfg y ∈ (K.1.1 : Set Point2) := by
      apply mem_circleTrace.mp
      apply hAK
      simp [A]
    have hzK : cfg z ∈ (K.1.1 : Set Point2) := by
      apply mem_circleTrace.mp
      apply hAK
      simp [A]
    have hgammaK : gamma ≠ K := by
      intro hEq
      apply hzNotGamma
      rw [hEq]
      exact hzK
    have hgammaKcoe : gamma.1 ≠ K.1 :=
      determinedCircle_coe_ne_of_ne hgammaK
    have hxyAxis : Projectivization.orthogonal
        (sixConicSecantCenter gamma.1 (cfg x) (cfg y)
          hxyCfg hxPower hyPower)
        (projectiveRadicalAxis gamma.1 K.1 hgammaKcoe) :=
      (sixConicSecantCenter_orthogonal_radicalAxis_iff
        gamma.1 K.1 hgammaKcoe hxyCfg hxPower hyPower hxK).2 hyK
    have hzwAxis : Projectivization.orthogonal
        (sixConicSecantCenter gamma.1 (cfg z) (cfg w)
          hzwCfg hzPower hwPower)
        (projectiveRadicalAxis gamma.1 K.1 hgammaKcoe) := by
      rw [← hsecants]
      exact hxyAxis
    have hwK : cfg w ∈ (K.1.1 : Set Point2) :=
      (sixConicSecantCenter_orthogonal_radicalAxis_iff
        gamma.1 K.1 hgammaKcoe hzwCfg hzPower hwPower hzK).1 hzwAxis
    refine ⟨Sum.inr K, ?_⟩
    intro a ha
    change a ∈ circleTrace cfg K.1
    rw [Finset.mem_union, heEq, hfEq] at ha
    rcases ha with ha | ha
    · simp only [Finset.mem_insert, Finset.mem_singleton] at ha
      rcases ha with rfl | rfl
      · exact mem_circleTrace.mpr hxK
      · exact mem_circleTrace.mpr hyK
    · simp only [Finset.mem_insert, Finset.mem_singleton] at ha
      rcases ha with rfl | rfl
      · exact mem_circleTrace.mpr hzK
      · exact mem_circleTrace.mpr hwK
  · let pe : KSubset α 2 := ⟨e, hePow.2⟩
    let pf : KSubset α 2 := ⟨f, hfPow.2⟩
    have hcol : Collinear ℝ (supportPoints cfg A.1) := by
      simpa [IsNoncollinear] using hA
    have hxS : cfg x ∈ supportPoints cfg A.1 := by
      exact ⟨x, by simp [A], rfl⟩
    have hyS : cfg y ∈ supportPoints cfg A.1 := by
      exact ⟨y, by simp [A], rfl⟩
    have hzS : cfg z ∈ supportPoints cfg A.1 := by
      exact ⟨z, by simp [A], rfl⟩
    have hzAffine : cfg z ∈
        affineSpan ℝ ({cfg x, cfg y} : Set Point2) :=
      hcol.mem_affineSpan_of_mem_of_ne hxS hyS hzS hxyCfg
    have hchordE : projectiveChordLine cfg pe =
        projectiveLine (cfg x) (cfg y) hxyCfg :=
      projectiveChordLine_eq_projectiveLine_of_mem
        cfg pe (by simp [pe, heEq]) (by simp [pe, heEq]) hxy
    have hchordF : projectiveChordLine cfg pf =
        projectiveLine (cfg z) (cfg w) hzwCfg :=
      projectiveChordLine_eq_projectiveLine_of_mem
        cfg pf (by simp [pf, hfEq]) (by simp [pf, hfEq]) hzw
    have hzChordE : Projectivization.orthogonal
        (projectivePoint (cfg z)) (projectiveChordLine cfg pe) := by
      rw [hchordE]
      exact (projectivePoint_orthogonal_projectiveLine_iff_mem_affineSpan
        hxyCfg).2 hzAffine
    have hsecantE : Projectivization.orthogonal
        (sixConicSecantCenter gamma.1 (cfg z) (cfg w)
          hzwCfg hzPower hwPower) (projectiveChordLine cfg pe) := by
      rw [← hsecants, hchordE]
      exact sixConicSecantCenter_orthogonal_line
        gamma.1 hxyCfg hxPower hyPower
    have hsecantF : Projectivization.orthogonal
        (sixConicSecantCenter gamma.1 (cfg z) (cfg w)
          hzwCfg hzPower hwPower) (projectiveChordLine cfg pf) := by
      rw [hchordF]
      exact sixConicSecantCenter_orthogonal_line
        gamma.1 hzwCfg hzPower hwPower
    have hzChordF : Projectivization.orthogonal
        (projectivePoint (cfg z)) (projectiveChordLine cfg pf) :=
      projectivePoint_orthogonal_projectiveChordLine cfg pf hzF
    have hcenterNeZ :
        sixConicSecantCenter gamma.1 (cfg z) (cfg w)
          hzwCfg hzPower hwPower ≠ projectivePoint (cfg z) :=
      sixConicSecantCenter_ne_left
        gamma.1 hzwCfg hzPower hwPower
    have hchordsEq : projectiveChordLine cfg pe =
        projectiveChordLine cfg pf := by
      calc
        projectiveChordLine cfg pe = Projectivization.cross
            (sixConicSecantCenter gamma.1 (cfg z) (cfg w)
              hzwCfg hzPower hwPower) (projectivePoint (cfg z)) :=
          projectiveCovector_eq_cross_of_orthogonal hcenterNeZ
            hsecantE hzChordE
        _ = projectiveChordLine cfg pf :=
          (projectiveCovector_eq_cross_of_orthogonal hcenterNeZ
            hsecantF hzChordF).symm
    have hwChordE : Projectivization.orthogonal
        (projectivePoint (cfg w)) (projectiveChordLine cfg pe) := by
      rw [hchordsEq]
      exact projectivePoint_orthogonal_projectiveChordLine cfg pf hwF
    have hwAffine : cfg w ∈
        affineSpan ℝ ({cfg x, cfg y} : Set Point2) := by
      rw [hchordE] at hwChordE
      exact (projectivePoint_orthogonal_projectiveLine_iff_mem_affineSpan
        hxyCfg).1 hwChordE
    let L : DeterminedLine cfg :=
      ⟨lineOfPair cfg pe, lineOfPair_mem_determinedLines cfg pe⟩
    have hlineEq : lineOfPair cfg pe =
        affineSpan ℝ ({cfg x, cfg y} : Set Point2) := by
      unfold lineOfPair
      change affineSpan ℝ (cfg '' (e : Set α)) =
        affineSpan ℝ ({cfg x, cfg y} : Set Point2)
      rw [heEq]
      congr 1
      ext p
      simp [eq_comm]
    refine ⟨Sum.inl L, ?_⟩
    intro a ha
    change a ∈ lineSupport cfg L
    rw [mem_lineSupport]
    change cfg a ∈ lineOfPair cfg pe
    rw [hlineEq]
    have hxBase : cfg x ∈
        affineSpan ℝ ({cfg x, cfg y} : Set Point2) :=
      subset_affineSpan ℝ ({cfg x, cfg y} : Set Point2) (by simp)
    have hyBase : cfg y ∈
        affineSpan ℝ ({cfg x, cfg y} : Set Point2) :=
      subset_affineSpan ℝ ({cfg x, cfg y} : Set Point2) (by simp)
    rw [Finset.mem_union, heEq, hfEq] at ha
    rcases ha with ha | ha
    · simp only [Finset.mem_insert, Finset.mem_singleton] at ha
      rcases ha with rfl | rfl
      · exact hxBase
      · exact hyBase
    · simp only [Finset.mem_insert, Finset.mem_singleton] at ha
      rcases ha with rfl | rfl
      · exact hzAffine
      · exact hwAffine

/-! ## Finite adapters for repetition events and full-edge fibres -/

/-- Every concrete repetition event has a geometric host; no event-principle
field is used. -/
theorem sixConic_repetition_host_exists
    {α : Type u} [Fintype α] [DecidableEq α]
    (cfg : Configuration α)
    (gamma : Erdos506.V1.DeterminedCircle cfg)
    (hgamma : (circleTrace cfg gamma.1).card = 6)
    (X : Finset α) (hdisjoint : Disjoint (circleTrace cfg gamma.1) X)
    (E : Finset (Finset α))
    (hE : E ∈ sixConicRepetitionEvents cfg gamma X) :
    ∃ H : GeometricBlock cfg, SixConicEventHostedBy cfg E H := by
  classical
  have hEspec := mem_sixConicRepetitionEvents.mp hE
  have hEpow := Finset.mem_powersetCard.mp hEspec.1
  obtain ⟨e, f, hef, hEeq⟩ := Finset.card_eq_two.mp hEpow.2
  have heE : e ∈ E := by simp [hEeq]
  have hfE : f ∈ E := by simp [hEeq]
  have heFull := hEpow.1 heE
  have hfFull := hEpow.1 hfE
  have hsignature := hEspec.2 e heE f hfE
  obtain ⟨H, hhost⟩ := sixConicEqualSignature_has_host
    cfg gamma hgamma X hdisjoint heFull hfFull hef hsignature
  refine ⟨H, ?_⟩
  change E.biUnion id ⊆ geometricBlockSupport cfg H
  simpa [hEeq] using hhost

private noncomputable def u17FullSignatureFiber
    {α : Type u} [Fintype α] [DecidableEq α]
    (cfg : Configuration α)
    (gamma : Erdos506.V1.DeterminedCircle cfg)
    (Y : Finset α) (s : Finset (Finset α)) : Finset (Finset α) :=
  (sixConicFullEdges cfg gamma Y).filter fun e =>
    sixConicSignature cfg gamma e = s

private theorem u17FullSignatureFiber_card_le_two
    {α : Type u} [Fintype α] [DecidableEq α]
    (cfg : Configuration α)
    (gamma : Erdos506.V1.DeterminedCircle cfg)
    (hgamma : (circleTrace cfg gamma.1).card = 6)
    (Y : Finset α) (hY : Y.card = 4)
    (hdisjoint : Disjoint (circleTrace cfg gamma.1) Y)
    (s : Finset (Finset α)) :
    (u17FullSignatureFiber cfg gamma Y s).card ≤ 2 := by
  classical
  let fiber := u17FullSignatureFiber cfg gamma Y s
  have hhalf : fiber.card ≤ Y.card / 2 := by
    apply card_le_half_of_pairwiseDisjoint_pairs Y fiber
    · intro e he
      exact (Finset.mem_powersetCard.mp
        (mem_sixConicFullEdges.mp (Finset.mem_filter.mp he).1).1).1
    · intro e he
      exact (Finset.mem_powersetCard.mp
        (mem_sixConicFullEdges.mp (Finset.mem_filter.mp he).1).1).2
    · intro e he f hf hef
      have heData := Finset.mem_filter.mp he
      have hfData := Finset.mem_filter.mp hf
      exact sixConic_equal_full_signatures_disjoint
        cfg gamma hgamma Y hdisjoint heData.1 hfData.1 hef
          (heData.2.trans hfData.2.symm)
  rw [hY] at hhalf
  norm_num at hhalf ⊢
  exact hhalf

/-- If six full edges use at most three signatures, every active signature
occurs on exactly two edges. -/
private theorem u17FullSignatureFiber_card_eq_two
    {α : Type u} [Fintype α] [DecidableEq α]
    (cfg : Configuration α)
    (gamma : Erdos506.V1.DeterminedCircle cfg)
    (hgamma : (circleTrace cfg gamma.1).card = 6)
    (Y : Finset α) (hY : Y.card = 4)
    (hdisjoint : Disjoint (circleTrace cfg gamma.1) Y)
    (hfullCard : (sixConicFullEdges cfg gamma Y).card = 6)
    (hactiveCard : (sixConicActiveSignatures cfg gamma Y).card ≤ 3)
    {s : Finset (Finset α)}
    (hs : s ∈ sixConicActiveSignatures cfg gamma Y) :
    (u17FullSignatureFiber cfg gamma Y s).card = 2 := by
  classical
  let F := sixConicFullEdges cfg gamma Y
  let A := sixConicActiveSignatures cfg gamma Y
  let fiber := u17FullSignatureFiber cfg gamma Y
  change F.card = 6 at hfullCard
  have hsA : s ∈ A := by
    exact hs
  have hactiveCardA : A.card ≤ 3 := by
    exact hactiveCard
  have hcover : F = A.biUnion fiber := by
    ext e
    constructor
    · intro he
      have hsA : sixConicSignature cfg gamma e ∈ A := by
        dsimp only [A, sixConicActiveSignatures]
        exact Finset.mem_image.mpr ⟨e, he, rfl⟩
      exact Finset.mem_biUnion.mpr
        ⟨sixConicSignature cfg gamma e, hsA,
          Finset.mem_filter.mpr ⟨he, rfl⟩⟩
    · intro he
      rcases Finset.mem_biUnion.mp he with ⟨t, _ht, het⟩
      exact (Finset.mem_filter.mp het).1
  have hcardUnion : F.card ≤ ∑ t ∈ A, (fiber t).card := by
    rw [hcover]
    exact Finset.card_biUnion_le
  have hfiberUpper (t : Finset (Finset α)) : (fiber t).card ≤ 2 :=
    u17FullSignatureFiber_card_le_two
      cfg gamma hgamma Y hY hdisjoint t
  have hrest : (∑ t ∈ A.erase s, (fiber t).card) ≤
      2 * (A.erase s).card := by
    calc
      (∑ t ∈ A.erase s, (fiber t).card) ≤
          ∑ _t ∈ A.erase s, 2 := by
        exact Finset.sum_le_sum fun t _ht => hfiberUpper t
      _ = 2 * (A.erase s).card := by simp [Nat.mul_comm]
  have heraseCard : (A.erase s).card + 1 = A.card := by
    rw [Finset.card_erase_of_mem hsA]
    have hApos : 0 < A.card := Finset.card_pos.mpr ⟨s, hsA⟩
    omega
  have hdecomp :
      (∑ t ∈ A.erase s, (fiber t).card) + (fiber s).card =
        ∑ t ∈ A, (fiber t).card := by
    exact Finset.sum_erase_add A (fun t => (fiber t).card) hsA
  have hupper := hfiberUpper s
  have heraseUpper : (A.erase s).card ≤ 2 := by omega
  have hrestUpper : (∑ t ∈ A.erase s, (fiber t).card) ≤ 4 := by
    omega
  have hsumLower : 6 ≤ ∑ t ∈ A, (fiber t).card := by
    omega
  change (fiber s).card = 2
  apply Nat.le_antisymm hupper
  omega

/-- On a four-set, the second edge carrying the signature of `e` is its
unique disjoint (opposite) edge. -/
private theorem sixConicOppositeSignatures_eq
    {α : Type u} [Fintype α] [DecidableEq α]
    (cfg : Configuration α)
    (gamma : Erdos506.V1.DeterminedCircle cfg)
    (hgamma : (circleTrace cfg gamma.1).card = 6)
    (Y : Finset α) (hY : Y.card = 4)
    (hdisjoint : Disjoint (circleTrace cfg gamma.1) Y)
    (hfullCard : (sixConicFullEdges cfg gamma Y).card = 6)
    (hactiveCard : (sixConicActiveSignatures cfg gamma Y).card ≤ 3)
    {e k : Finset α}
    (heFull : e ∈ sixConicFullEdges cfg gamma Y)
    (hkCard : k.card = 2)
    (hUnion : e ∪ k = Y) :
    sixConicSignature cfg gamma e = sixConicSignature cfg gamma k := by
  classical
  let s := sixConicSignature cfg gamma e
  let fiber := u17FullSignatureFiber cfg gamma Y s
  have hsActive : s ∈ sixConicActiveSignatures cfg gamma Y := by
    dsimp only [s, sixConicActiveSignatures]
    exact Finset.mem_image.mpr ⟨e, heFull, rfl⟩
  have hfiberCard : fiber.card = 2 :=
    u17FullSignatureFiber_card_eq_two
      cfg gamma hgamma Y hY hdisjoint hfullCard hactiveCard hsActive
  have heFiber : e ∈ fiber := by
    exact Finset.mem_filter.mpr ⟨heFull, rfl⟩
  obtain ⟨f, hfFiber, hfe⟩ :=
    Finset.exists_mem_ne (s := fiber) (by omega) e
  have hfData := Finset.mem_filter.mp hfFiber
  have hfFull := hfData.1
  have hfSpec := mem_sixConicFullEdges.mp hfFull
  have hfPow := Finset.mem_powersetCard.mp hfSpec.1
  have hefDisjoint : Disjoint e f :=
    sixConic_equal_full_signatures_disjoint
      cfg gamma hgamma Y hdisjoint heFull hfFull hfe.symm
        hfData.2.symm
  have hfkSub : f ⊆ k := by
    intro x hxf
    have hxY : x ∈ Y := hfPow.1 hxf
    have hxUnion : x ∈ e ∪ k := by
      rw [hUnion]
      exact hxY
    rcases Finset.mem_union.mp hxUnion with hxe | hxk
    · exact (Finset.disjoint_left.mp hefDisjoint hxe hxf).elim
    · exact hxk
  have hfk : f = k :=
    Finset.eq_of_subset_of_card_le hfkSub (by rw [hfPow.2, hkCard])
  dsimp only [fiber, s] at hfData
  rw [hfk] at hfData
  exact hfData.2.symm

/-! ## Excluding six full edges on four outsiders -/

/- The finite pigeonhole/host part is kept opaque so that elaborating the
final complete-quadrangle contradiction does not repeatedly normalize the
signature fibres and their geometric host. -/
private theorem sixConicAllFull_activeSignatures_card_le_three
    {α : Type u} [Fintype α] [DecidableEq α]
    (cfg : Configuration α)
    (gamma : Erdos506.V1.DeterminedCircle cfg)
    (hgamma : (circleTrace cfg gamma.1).card = 6)
    (Y : Finset α) (hY : Y.card = 4)
    (hdisjoint : Disjoint (circleTrace cfg gamma.1) Y)
    (hallFull : ∀ e ∈ Y.powersetCard 2,
      e ∈ sixConicFullEdges cfg gamma Y) :
    (sixConicActiveSignatures cfg gamma Y).card ≤ 3 := by
  classical
  have hfullEq : sixConicFullEdges cfg gamma Y = Y.powersetCard 2 := by
    ext e
    constructor
    · intro he
      exact (mem_sixConicFullEdges.mp he).1
    · intro he
      exact hallFull e he
  have hfullCard : (sixConicFullEdges cfg gamma Y).card = 6 := by
    rw [hfullEq, Finset.card_powersetCard, hY]
    norm_num [Nat.choose]
  have hactiveFour :
      (sixConicActiveSignatures cfg gamma Y).card ≤ 4 :=
    sixConic_activeSignatures_card_le_four
      cfg gamma hgamma Y hdisjoint
  have himageLt :
      ((sixConicFullEdges cfg gamma Y).image fun e =>
        sixConicSignature cfg gamma e).card <
          (sixConicFullEdges cfg gamma Y).card := by
    change (sixConicActiveSignatures cfg gamma Y).card <
      (sixConicFullEdges cfg gamma Y).card
    omega
  obtain ⟨e, heFull, f, hfFull, hef, hsignature⟩ :=
    Finset.exists_ne_map_eq_of_card_image_lt himageLt
  obtain ⟨H, hEFH⟩ := sixConicEqualSignature_has_host
    cfg gamma hgamma Y hdisjoint heFull hfFull hef hsignature
  have hefDisjoint : Disjoint e f :=
    sixConic_equal_full_signatures_disjoint
      cfg gamma hgamma Y hdisjoint heFull hfFull hef hsignature
  have hePow := Finset.mem_powersetCard.mp
    (mem_sixConicFullEdges.mp heFull).1
  have hfPow := Finset.mem_powersetCard.mp
    (mem_sixConicFullEdges.mp hfFull).1
  have hUnionCard : (e ∪ f).card = 4 := by
    rw [Finset.card_union_of_disjoint hefDisjoint, hePow.2, hfPow.2]
  have hUnionSub : e ∪ f ⊆ Y := Finset.union_subset hePow.1 hfPow.1
  have hUnionEq : e ∪ f = Y :=
    Finset.eq_of_subset_of_card_le hUnionSub (by rw [hUnionCard, hY])
  have hYH : Y ⊆ geometricBlockSupport cfg H := by
    rw [← hUnionEq]
    exact hEFH
  have hactiveEqHost :
      sixConicActiveSignatures cfg gamma Y =
        sixConicSignaturesOnHost cfg gamma Y H := by
    ext s
    constructor
    · intro hs
      rw [sixConicActiveSignatures] at hs
      obtain ⟨g, hgFull, rfl⟩ := Finset.mem_image.mp hs
      have hgY := Finset.mem_powersetCard.mp
        (mem_sixConicFullEdges.mp hgFull).1
      rw [sixConicSignaturesOnHost]
      exact Finset.mem_image.mpr
        ⟨g, Finset.mem_filter.mpr ⟨hgFull, hgY.1.trans hYH⟩, rfl⟩
    · intro hs
      rw [sixConicSignaturesOnHost] at hs
      obtain ⟨g, hg, rfl⟩ := Finset.mem_image.mp hs
      rw [sixConicActiveSignatures]
      exact Finset.mem_image.mpr
        ⟨g, (Finset.mem_filter.mp hg).1, rfl⟩
  rw [hactiveEqHost]
  exact sixConicSignaturesOnHost_card_le_three
    cfg gamma hgamma Y hdisjoint H

private theorem sixConic_not_all_four_outsider_edges_full
    {α : Type u} [Fintype α] [DecidableEq α]
    (cfg : Configuration α)
    (gamma : Erdos506.V1.DeterminedCircle cfg)
    (hgamma : (circleTrace cfg gamma.1).card = 6)
    (Y : Finset α) (hY : Y.card = 4)
    (hdisjoint : Disjoint (circleTrace cfg gamma.1) Y)
    (hallFull : ∀ e ∈ Y.powersetCard 2,
      e ∈ sixConicFullEdges cfg gamma Y) : False := by
  classical
  have hfullEq : sixConicFullEdges cfg gamma Y = Y.powersetCard 2 := by
    ext e
    constructor
    · intro he
      exact (mem_sixConicFullEdges.mp he).1
    · intro he
      exact hallFull e he
  have hfullCard : (sixConicFullEdges cfg gamma Y).card = 6 := by
    rw [hfullEq, Finset.card_powersetCard, hY]
    norm_num [Nat.choose]
  have hactiveThree :
      (sixConicActiveSignatures cfg gamma Y).card ≤ 3 :=
    sixConicAllFull_activeSignatures_card_le_three
      cfg gamma hgamma Y hY hdisjoint hallFull
  obtain ⟨a, b, c, d, hab, hac, had, hbc, hbd, hcd, hYeq⟩ :=
    Finset.card_eq_four.mp hY
  have haY : a ∈ Y := by rw [hYeq]; simp
  have hbY : b ∈ Y := by rw [hYeq]; simp
  have hcY : c ∈ Y := by rw [hYeq]; simp
  have hdY : d ∈ Y := by rw [hYeq]; simp
  have pairSubset {u v : α} (hu : u ∈ Y) (hv : v ∈ Y) :
      {u, v} ⊆ Y := by
    intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl
    · exact hu
    · exact hv
  have hABpow : {a, b} ∈ Y.powersetCard 2 := by
    apply Finset.mem_powersetCard.mpr
    exact ⟨pairSubset haY hbY, by simp [hab]⟩
  have hCDpow : {c, d} ∈ Y.powersetCard 2 := by
    apply Finset.mem_powersetCard.mpr
    exact ⟨pairSubset hcY hdY, by simp [hcd]⟩
  have hACpow : {a, c} ∈ Y.powersetCard 2 := by
    apply Finset.mem_powersetCard.mpr
    exact ⟨pairSubset haY hcY, by simp [hac]⟩
  have hBDpow : {b, d} ∈ Y.powersetCard 2 := by
    apply Finset.mem_powersetCard.mpr
    exact ⟨pairSubset hbY hdY, by simp [hbd]⟩
  have hADpow : {a, d} ∈ Y.powersetCard 2 := by
    apply Finset.mem_powersetCard.mpr
    exact ⟨pairSubset haY hdY, by simp [had]⟩
  have hBCpow : {b, c} ∈ Y.powersetCard 2 := by
    apply Finset.mem_powersetCard.mpr
    exact ⟨pairSubset hbY hcY, by simp [hbc]⟩
  have hABFull := hallFull {a, b} hABpow
  have hCDFull := hallFull {c, d} hCDpow
  have hACFull := hallFull {a, c} hACpow
  have hBDFull := hallFull {b, d} hBDpow
  have hADFull := hallFull {a, d} hADpow
  have hBCFull := hallFull {b, c} hBCpow
  have hABCDUnion : {a, b} ∪ {c, d} = Y := by
    rw [hYeq]
    ext x
    simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
    tauto
  have hACBDUnion : {a, c} ∪ {b, d} = Y := by
    rw [hYeq]
    ext x
    simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
    tauto
  have hADBCUnion : {a, d} ∪ {b, c} = Y := by
    rw [hYeq]
    ext x
    simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
    tauto
  have hABCD : sixConicSignature cfg gamma {a, b} =
      sixConicSignature cfg gamma {c, d} :=
    sixConicOppositeSignatures_eq
      cfg gamma hgamma Y hY hdisjoint hfullCard hactiveThree hABFull
        (by simp [hcd]) hABCDUnion
  have hACBD : sixConicSignature cfg gamma {a, c} =
      sixConicSignature cfg gamma {b, d} :=
    sixConicOppositeSignatures_eq
      cfg gamma hgamma Y hY hdisjoint hfullCard hactiveThree hACFull
        (by simp [hbd]) hACBDUnion
  have hADBC : sixConicSignature cfg gamma {a, d} =
      sixConicSignature cfg gamma {b, c} :=
    sixConicOppositeSignatures_eq
      cfg gamma hgamma Y hY hdisjoint hfullCard hactiveThree hADFull
        (by simp [hbc]) hADBCUnion
  have hnotGamma (x : α) (hxY : x ∈ Y) :
      cfg x ∉ (gamma.1.1 : Set Point2) := by
    intro hxGamma
    exact Finset.disjoint_left.mp hdisjoint
      (mem_circleTrace.mpr hxGamma) hxY
  have haPower := sixConicCirclePower_ne_zero_of_not_mem
    gamma.1 (hnotGamma a haY)
  have hbPower := sixConicCirclePower_ne_zero_of_not_mem
    gamma.1 (hnotGamma b hbY)
  have hcPower := sixConicCirclePower_ne_zero_of_not_mem
    gamma.1 (hnotGamma c hcY)
  have hdPower := sixConicCirclePower_ne_zero_of_not_mem
    gamma.1 (hnotGamma d hdY)
  have secantEq (p q r s : α)
      (hpq : p ≠ q) (hrs : r ≠ s)
      (hpPower : sixConicCirclePower gamma.1 (cfg p) ≠ 0)
      (hqPower : sixConicCirclePower gamma.1 (cfg q) ≠ 0)
      (hrPower : sixConicCirclePower gamma.1 (cfg r) ≠ 0)
      (hsPower : sixConicCirclePower gamma.1 (cfg s) ≠ 0)
      (hpqFull : {p, q} ∈ sixConicFullEdges cfg gamma Y)
      (hrsFull : {r, s} ∈ sixConicFullEdges cfg gamma Y)
      (hsig : sixConicSignature cfg gamma {p, q} =
        sixConicSignature cfg gamma {r, s}) :
      sixConicSecantCenter gamma.1 (cfg p) (cfg q)
          (cfg.injective.ne hpq) hpPower hqPower =
        sixConicSecantCenter gamma.1 (cfg r) (cfg s)
          (cfg.injective.ne hrs) hrPower hsPower := by
    have hpqCenter := sixConicFullEdgeCenter_eq_secantCenter
      cfg gamma hgamma Y hdisjoint hpqFull
        (by simp) (by simp) hpq (cfg.injective.ne hpq) hpPower hqPower
    have hrsCenter := sixConicFullEdgeCenter_eq_secantCenter
      cfg gamma hgamma Y hdisjoint hrsFull
        (by simp) (by simp) hrs (cfg.injective.ne hrs) hrPower hsPower
    have hcenters := sixConicFullEdgeCenters_eq_of_signature_eq
      cfg gamma hgamma Y hdisjoint hpqFull hrsFull hsig
    exact hpqCenter.symm.trans (hcenters.trans hrsCenter)
  have hsecABCD := secantEq a b c d hab hcd
    haPower hbPower hcPower hdPower hABFull hCDFull hABCD
  have hsecACBD := secantEq a c b d hac hbd
    haPower hcPower hbPower hdPower hACFull hBDFull hACBD
  have hsecADBC := secantEq a d b c had hbc
    haPower hdPower hbPower hcPower hADFull hBCFull hADBC
  have hparallelABCD :=
    sixConicNormalized_sub_parallel_of_secantCenters_eq
      gamma.1 (cfg.injective.ne hab) (cfg.injective.ne hcd)
        haPower hbPower hcPower hdPower hsecABCD
  have hparallelACBD :=
    sixConicNormalized_sub_parallel_of_secantCenters_eq
      gamma.1 (cfg.injective.ne hac) (cfg.injective.ne hbd)
        haPower hcPower hbPower hdPower hsecACBD
  have hparallelADBC :=
    sixConicNormalized_sub_parallel_of_secantCenters_eq
      gamma.1 (cfg.injective.ne had) (cfg.injective.ne hbc)
        haPower hdPower hbPower hcPower hsecADBC
  let ua := sixConicNormalizedLift gamma.1 (cfg a)
  let ub := sixConicNormalizedLift gamma.1 (cfg b)
  let uc := sixConicNormalizedLift gamma.1 (cfg c)
  let ud := sixConicNormalizedLift gamma.1 (cfg d)
  have huab : ua ≠ ub := by
    intro hEq
    apply hab
    apply cfg.injective
    exact sixConicNormalizedLift_injective
      gamma.1 haPower hbPower hEq
  have hnoncollinear : ¬∃ t : ℝ, uc - ua = t • (ub - ua) := by
    simpa only [ua, ub, uc] using
      (sixConicNormalizedLift_not_parallel gamma.1
        (cfg.injective.ne hab) (cfg.injective.ne hac)
        (cfg.injective.ne hbc) haPower hbPower hcPower)
  have hAB : ∃ r : ℝ, r ≠ 0 ∧ ua - ub = r • (uc - ud) := by
    simpa only [ua, ub, uc, ud] using hparallelABCD
  have hAC : ∃ r : ℝ, r ≠ 0 ∧ ua - uc = r • (ub - ud) := by
    simpa only [ua, ub, uc, ud] using hparallelACBD
  have hAD : ∃ r : ℝ, ua - ud = r • (ub - uc) := by
    obtain ⟨r, _hr, hEq⟩ := hparallelADBC
    exact ⟨r, by simpa only [ua, ub, uc, ud] using hEq⟩
  exact affineCompleteQuadrangle_not_three_parallel
    huab hnoncollinear hAB hAC hAD

/-! ## The unconditional U17 endpoint -/

/- The six-edge saturation calculation is isolated from the geometric
contradiction.  In particular, the endpoint only combines two opaque facts
instead of elaborating a large bounded-sum argument under `by_contra`. -/
private theorem sixConic_all_four_outsider_edges_full_of_totalWeight_ge_eighteen
    {α : Type u} [Fintype α] [DecidableEq α]
    (cfg : Configuration α)
    (gamma : Erdos506.V1.DeterminedCircle cfg)
    (hgamma : (circleTrace cfg gamma.1).card = 6)
    (Y : Finset α) (hY : Y.card = 4)
    (hdisjoint : Disjoint (circleTrace cfg gamma.1) Y)
    (htotalLower : 18 ≤ sixConicTotalWeight cfg gamma Y) :
    ∀ e ∈ Y.powersetCard 2, e ∈ sixConicFullEdges cfg gamma Y := by
  classical
  have hpairCard : (Y.powersetCard 2).card = 6 := by
    rw [Finset.card_powersetCard, hY]
    norm_num [Nat.choose]
  intro e he
  have hePow := Finset.mem_powersetCard.mp he
  have heDisjointGamma : Disjoint e (circleTrace cfg gamma.1) :=
    hdisjoint.symm.mono_left hePow.1
  have hqUpper := sixConicPairWeight_le_three
    hgamma hePow.2 heDisjointGamma
  by_contra hnotFull
  have hqNeThree : sixConicPairWeight cfg gamma e ≠ 3 := by
    intro hthree
    exact hnotFull (mem_sixConicFullEdges.mpr ⟨he, hthree⟩)
  have hqTwo : sixConicPairWeight cfg gamma e ≤ 2 := by omega
  have hrest :
      (∑ f ∈ (Y.powersetCard 2).erase e,
        sixConicPairWeight cfg gamma f) ≤
          3 * ((Y.powersetCard 2).erase e).card := by
    calc
      (∑ f ∈ (Y.powersetCard 2).erase e,
          sixConicPairWeight cfg gamma f) ≤
          ∑ _f ∈ (Y.powersetCard 2).erase e, 3 := by
        apply Finset.sum_le_sum
        intro f hf
        have hfPow := Finset.mem_powersetCard.mp
          (Finset.mem_of_mem_erase hf)
        exact sixConicPairWeight_le_three hgamma hfPow.2
          (hdisjoint.symm.mono_left hfPow.1)
      _ = 3 * ((Y.powersetCard 2).erase e).card := by
        simp [Nat.mul_comm]
  have heraseCard : ((Y.powersetCard 2).erase e).card = 5 := by
    rw [Finset.card_erase_of_mem he, hpairCard]
  have hrestUpper :
      (∑ f ∈ (Y.powersetCard 2).erase e,
        sixConicPairWeight cfg gamma f) ≤ 15 := by
    omega
  have hdecomp :
      (∑ f ∈ (Y.powersetCard 2).erase e,
          sixConicPairWeight cfg gamma f) +
          sixConicPairWeight cfg gamma e =
        ∑ f ∈ Y.powersetCard 2, sixConicPairWeight cfg gamma f := by
    exact Finset.sum_erase_add (Y.powersetCard 2)
      (fun f => sixConicPairWeight cfg gamma f) he
  change 18 ≤
    ∑ f ∈ Y.powersetCard 2, sixConicPairWeight cfg gamma f at htotalLower
  omega

/-- Four outsiders contribute at most seventeen two-marked circles.  This
is the field-free form of the former U17 event clause. -/
theorem sixConicWeight_le_seventeen
    {α : Type u} [Fintype α] [DecidableEq α]
    (cfg : Configuration α)
    (gamma : Erdos506.V1.DeterminedCircle cfg)
    (hgamma : (circleTrace cfg gamma.1).card = 6)
    (Y : Finset α) (hY : Y.card = 4)
    (hdisjoint : Disjoint (circleTrace cfg gamma.1) Y) :
    sixConicWeight cfg gamma Y ≤ 17 := by
  by_contra hnot
  have hweightLower : 18 ≤ sixConicWeight cfg gamma Y := by omega
  have htotalLower : 18 ≤ sixConicTotalWeight cfg gamma Y := by
    rw [sixConicTotalWeight_eq_sixConicWeight]
    exact hweightLower
  have hallFull :=
    sixConic_all_four_outsider_edges_full_of_totalWeight_ge_eighteen
      cfg gamma hgamma Y hY hdisjoint htotalLower
  exact sixConic_not_all_four_outsider_edges_full
    cfg gamma hgamma Y hY hdisjoint hallFull

/-- The unconditional six-circle U17 principle obtained from the concrete
four-outsider theorem. -/
def realPlaneSixCircleU17Principle :
    RealPlaneSixCircleU17Principle.{u} where
  u17 := by
    intro α _ _ cfg gamma hgamma Y hY hdisjoint
    exact sixConicWeight_le_seventeen
      cfg gamma hgamma Y hY hdisjoint

end Erdos506.Incidence
