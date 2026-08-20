import Erdos506.Incidence.FiveConicMixedPageBridge
import Erdos506.Incidence.RealCircleProjectiveParametrization
import Erdos506.Incidence.RealProjectiveLineSuccessor
import Erdos506.Finite.KFiveNearOneFactorizationRelabel

/-!
# The one-single/two-double five-conic separator

This file isolates the projective calculation missing from the all-double
K2.1 endpoint.  After four points of a real conic are sent to
`∞, 0, 1, λ` with `1 < λ`, the fifth point in the complementary arc has
parameter `t > λ`.  Of the three diagonal sides of the four-point complete
quadrangle, only the first can contain that fifth point.  The calculation is
kept in raw homogeneous Veronese coordinates, so the subsequent projective
frame transport has a literal determinant target.

No cyclic-order or normal-form hypothesis is introduced at the configuration
boundary: this is only the explicit algebraic normal endpoint to which that
boundary will be transported.
-/

namespace Erdos506.Incidence

open Erdos506.Finite
open Erdos506.V1
open Erdos506.V4
open Matrix
open scoped LinearAlgebra.Projectivization

/-- The standard affine Veronese point of parameter `t`. -/
def fiveConicNormalPoint (t : ℝ) : Homogeneous3 := ![t ^ 2, t, 1]

/-- The Veronese point at infinity. -/
def fiveConicNormalInfinity : Homogeneous3 := ![1, 0, 0]

/-- The first diagonal centre of `∞,0,1,λ`: the intersection of the chords
`∞0` and `1λ`. -/
def fiveConicNormalDiagonalZero (lam : ℝ) : Homogeneous3 :=
  crossProduct
    (crossProduct fiveConicNormalInfinity (fiveConicNormalPoint 0))
    (crossProduct (fiveConicNormalPoint 1) (fiveConicNormalPoint lam))

/-- The second diagonal centre of `∞,0,1,λ`: the intersection of the chords
`∞1` and `0λ`. -/
def fiveConicNormalDiagonalOne (lam : ℝ) : Homogeneous3 :=
  crossProduct
    (crossProduct fiveConicNormalInfinity (fiveConicNormalPoint 1))
    (crossProduct (fiveConicNormalPoint 0) (fiveConicNormalPoint lam))

/-- The third diagonal centre of `∞,0,1,λ`: the intersection of the chords
`∞λ` and `01`. -/
def fiveConicNormalDiagonalTwo (lam : ℝ) : Homogeneous3 :=
  crossProduct
    (crossProduct fiveConicNormalInfinity (fiveConicNormalPoint lam))
    (crossProduct (fiveConicNormalPoint 0) (fiveConicNormalPoint 1))

private theorem fiveConicNormal_det_zero_one
    (lam t : ℝ) :
    Matrix.det ![fiveConicNormalPoint t,
      fiveConicNormalDiagonalZero lam,
      fiveConicNormalDiagonalOne lam] =
      -lam * (lam - 1) * (t ^ 2 - 2 * lam * t + lam) := by
  simp [fiveConicNormalPoint, fiveConicNormalInfinity,
    fiveConicNormalDiagonalZero, fiveConicNormalDiagonalOne,
    cross_apply, Matrix.det_fin_three]
  ring

private theorem fiveConicNormal_det_zero_two
    (lam t : ℝ) :
    Matrix.det ![fiveConicNormalPoint t,
      fiveConicNormalDiagonalZero lam,
      fiveConicNormalDiagonalTwo lam] =
      -lam * (lam - 1) * (t ^ 2 - 2 * t + lam) := by
  simp [fiveConicNormalPoint, fiveConicNormalInfinity,
    fiveConicNormalDiagonalZero, fiveConicNormalDiagonalTwo,
    cross_apply, Matrix.det_fin_three]
  ring

private theorem fiveConicNormal_det_one_two
    (lam t : ℝ) :
    Matrix.det ![fiveConicNormalPoint t,
      fiveConicNormalDiagonalOne lam,
      fiveConicNormalDiagonalTwo lam] =
      -lam * (t ^ 2 - lam) * (lam - 1) := by
  simp [fiveConicNormalPoint, fiveConicNormalInfinity,
    fiveConicNormalDiagonalOne, fiveConicNormalDiagonalTwo,
    cross_apply, Matrix.det_fin_three]
  ring

/-- In the normalized cyclic chart, the diagonal side joining the first and
third centres cannot pass through the fifth point in the complementary arc.
This is the positive polynomial `t² - 2t + λ`. -/
theorem fiveConicNormal_not_collinear_zero_two_of_one_lt
    {lam t : ℝ} (hlam : 1 < lam) (ht : lam < t) :
    Matrix.det ![fiveConicNormalPoint t,
      fiveConicNormalDiagonalZero lam,
      fiveConicNormalDiagonalTwo lam] ≠ 0 := by
  rw [fiveConicNormal_det_zero_two]
  have hpoly : 0 < t ^ 2 - 2 * t + lam := by
    nlinarith [sq_nonneg (t - 1)]
  exact mul_ne_zero
    (mul_ne_zero (neg_ne_zero.mpr (ne_of_gt (by linarith)))
      (ne_of_gt (by linarith)))
    (ne_of_gt hpoly)

/-- In the normalized cyclic chart, the diagonal side joining the second and
third centres cannot pass through the fifth point in the complementary arc.
This is the positive polynomial `t² - λ`. -/
theorem fiveConicNormal_not_collinear_one_two_of_one_lt
    {lam t : ℝ} (hlam : 1 < lam) (ht : lam < t) :
    Matrix.det ![fiveConicNormalPoint t,
      fiveConicNormalDiagonalOne lam,
      fiveConicNormalDiagonalTwo lam] ≠ 0 := by
  rw [fiveConicNormal_det_one_two]
  have hlampos : 0 < lam := by linarith
  have htpos : 0 < t := by linarith
  have hsq : 0 < t ^ 2 - lam ^ 2 := by
    have : 0 < (t - lam) * (t + lam) :=
      mul_pos (by linarith) (by linarith)
    nlinarith
  have hlamsq : 0 < lam ^ 2 - lam := by
    have : 0 < lam * (lam - 1) :=
      mul_pos hlampos (by linarith)
    nlinarith
  have hpoly : 0 < t ^ 2 - lam := by
    nlinarith
  exact mul_ne_zero
    (mul_ne_zero (neg_ne_zero.mpr (ne_of_gt hlampos))
      (ne_of_gt hpoly))
    (ne_of_gt (by linarith))

/-! ## Intrinsic cyclic parameters of an actual five-trace -/

universe u

/-- The intrinsic `RP¹` parameter of one labelled point on an actual selected
proper circle.  It is intentionally defined for every finite trace size; the
five-point specialization below only supplies the cyclic normal frame. -/
noncomputable def fiveConicTraceParameter
    {α : Type u} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (Gamma : DeterminedCircle cfg)
    (x : {x : α // x ∈ circleTrace cfg Gamma.1}) :
    RealProjectiveOnePoint :=
  (properCircleProjectiveEquiv Gamma.1).symm
    ⟨cfg x.1, mem_circleTrace.mp x.2⟩

@[simp] theorem properCircleProjectiveParam_fiveConicTraceParameter
    {α : Type u} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (Gamma : DeterminedCircle cfg)
    (x : {x : α // x ∈ circleTrace cfg Gamma.1}) :
    properCircleProjectiveParam Gamma.1
      (fiveConicTraceParameter cfg Gamma x) = cfg x.1 := by
  have h := (properCircleProjectiveEquiv Gamma.1).apply_symm_apply
    ⟨cfg x.1, mem_circleTrace.mp x.2⟩
  exact congrArg Subtype.val h

/-- The actual trace parametrization has no accidental identifications. -/
theorem fiveConicTraceParameter_injective
    {α : Type u} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (Gamma : DeterminedCircle cfg) :
    Function.Injective (fiveConicTraceParameter cfg Gamma) := by
  intro x y hxy
  apply Subtype.ext
  apply cfg.injective
  rw [← properCircleProjectiveParam_fiveConicTraceParameter cfg Gamma x,
    ← properCircleProjectiveParam_fiveConicTraceParameter cfg Gamma y,
    hxy]

/-- The five marked trace points in their intrinsic cyclic order.  The chart
is constructed by `projectiveCyclicLabel`; it is disjoint from the trace and
therefore makes no affine-normalization choice at the configuration level. -/
noncomputable def fiveConicCyclicLabel
    {α : Type u} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (Gamma : DeterminedCircle cfg)
    (hGamma : (circleTrace cfg Gamma.1).card = 5) :
    Fin 5 ≃ {x : α // x ∈ circleTrace cfg Gamma.1} := by
  have hcard : Fintype.card {x : α // x ∈ circleTrace cfg Gamma.1} = 5 := by
    simpa only [Fintype.card_coe] using hGamma
  exact (finCongr hcard.symm).trans
    (projectiveCyclicLabel (fiveConicTraceParameter cfg Gamma)
      (fiveConicTraceParameter_injective cfg Gamma))

/-- The two selected chords of the canonical cyclic colour `i`.  These are
the finite sets `Sᵢ` from the one-colour trace law, transported through the
intrinsic cyclic label of the actual five-trace. -/
noncomputable def fiveConicCyclicChordFactor
    {α : Type u} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (Gamma : DeterminedCircle cfg)
    (hGamma : (circleTrace cfg Gamma.1).card = 5) (i : Fin 5) :
    Finset (KFiveChord (circleTrace cfg Gamma.1)) :=
  (kFiveCyclicNearOneFactorizationCode.toFactorization.factor i).map
    (kFiveChordEquivOfVertexLabel
      (fiveConicCyclicLabel cfg Gamma hGamma)).toEmbedding

/-- The five cyclic colour factors partition the ten actual selected chords.
This is the finite uniqueness step used after the geometric separator puts a
single host chord in its colour factor. -/
theorem fiveConicCyclicChordFactor_unique
    {α : Type u} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (Gamma : DeterminedCircle cfg)
    (hGamma : (circleTrace cfg Gamma.1).card = 5)
    (e : KFiveChord (circleTrace cfg Gamma.1)) :
    ∃! i : Fin 5, e ∈ fiveConicCyclicChordFactor cfg Gamma hGamma i := by
  let label := fiveConicCyclicLabel cfg Gamma hGamma
  let E := kFiveChordEquivOfVertexLabel label
  let F := kFiveCyclicNearOneFactorizationCode.toFactorization
  let e' : FinFiveChord := E.symm e
  obtain ⟨i, hi, hunique⟩ := F.chord_unique e'
  refine ⟨i, ?_, ?_⟩
  · simpa [fiveConicCyclicChordFactor, label, E, F, e'] using hi
  · intro j hj
    apply hunique j
    simpa [fiveConicCyclicChordFactor, label, E, F, e'] using hj

/-- The concrete five-label enumeration agrees with the intrinsic cyclic
relation on the proper-circle parameter line. -/
theorem fiveConicCyclicLabel_parameter_sbtw_iff
    {α : Type u} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (Gamma : DeterminedCircle cfg)
    (hGamma : (circleTrace cfg Gamma.1).card = 5)
    (i j k : Fin 5) :
    RealProjectiveCyclic
      (fiveConicTraceParameter cfg Gamma
        (fiveConicCyclicLabel cfg Gamma hGamma i))
      (fiveConicTraceParameter cfg Gamma
        (fiveConicCyclicLabel cfg Gamma hGamma j))
      (fiveConicTraceParameter cfg Gamma
        (fiveConicCyclicLabel cfg Gamma hGamma k)) ↔
      sbtw i j k := by
  have hcard : Fintype.card {x : α // x ∈ circleTrace cfg Gamma.1} = 5 := by
    simpa only [Fintype.card_coe] using hGamma
  simpa [fiveConicCyclicLabel, hcard, Equiv.trans_apply, Fin.sbtw_iff] using
    (projectiveCyclicLabel_cyclic_iff_sbtw
      (fiveConicTraceParameter cfg Gamma)
      (fiveConicTraceParameter_injective cfg Gamma)
      (Fin.cast hcard.symm i) (Fin.cast hcard.symm j)
      (Fin.cast hcard.symm k))

/-! ## The literal direction contributed by one circle host -/

private theorem fiveConic_projectiveLine_eq_projectiveRadicalAxis_of_common_points
    (C D : ProperCircle) (hCD : C ≠ D) {p q : Point2}
    (hpC : p ∈ (C.1 : Set Point2))
    (hqC : q ∈ (C.1 : Set Point2))
    (hpD : p ∈ (D.1 : Set Point2))
    (hqD : q ∈ (D.1 : Set Point2))
    (hpq : p ≠ q) :
    projectiveLine p q hpq = projectiveRadicalAxis C D hCD := by
  let P := projectivePoint p
  let Q := projectivePoint q
  have hPQ : P ≠ Q := projectivePoint_injective.ne hpq
  have hPaxis : Projectivization.orthogonal P
      (projectiveRadicalAxis C D hCD) :=
    projectivePoint_orthogonal_projectiveRadicalAxis_of_mem hCD hpC hpD
  have hQaxis : Projectivization.orthogonal Q
      (projectiveRadicalAxis C D hCD) :=
    projectivePoint_orthogonal_projectiveRadicalAxis_of_mem hCD hqC hqD
  calc
    projectiveLine p q hpq = Projectivization.cross P Q := by
      symm
      simpa [P, Q] using (projectivePoint_cross_eq_projectiveLine hpq)
    _ = projectiveRadicalAxis C D hCD :=
      (projectiveCovector_eq_cross_of_orthogonal hPQ hPaxis hQaxis).symm

/-- A single proper-circle host of an outsider pair contributes its literal
direction to the trace axis of a proper-circle page.  This is the one-host
counterpart of the two-host direction lemmas used by the all-double router.

The selected chord `ab` is the radical axis of the selected circle and the
host; the outsider secant `xy` is the radical axis of the host and the page.
Their projective intersection is therefore on the selected/page radical
axis. -/
theorem properCircle_singleCircleHost_direction_on_page_axis
    (Gamma K C : ProperCircle)
    (hGammaK : Gamma ≠ K) (hGammaC : Gamma ≠ C) (hCK : C ≠ K)
    {a b x y : Point2}
    (haGamma : a ∈ (Gamma.1 : Set Point2))
    (hbGamma : b ∈ (Gamma.1 : Set Point2))
    (haC : a ∈ (C.1 : Set Point2))
    (hbC : b ∈ (C.1 : Set Point2))
    (hxC : x ∈ (C.1 : Set Point2))
    (hyC : y ∈ (C.1 : Set Point2))
    (hxK : x ∈ (K.1 : Set Point2))
    (hyK : y ∈ (K.1 : Set Point2))
    (haNotK : a ∉ (K.1 : Set Point2))
    (hab : a ≠ b) (hxy : x ≠ y) :
    Projectivization.orthogonal
      (Projectivization.cross (projectiveLine a b hab)
        (projectiveLine x y hxy))
      (projectiveRadicalAxis Gamma K hGammaK) := by
  have hAB : projectiveLine a b hab =
      projectiveRadicalAxis Gamma C hGammaC :=
    fiveConic_projectiveLine_eq_projectiveRadicalAxis_of_common_points
      Gamma C hGammaC haGamma hbGamma haC hbC hab
  have hXY : projectiveLine x y hxy =
      projectiveRadicalAxis C K hCK :=
    fiveConic_projectiveLine_eq_projectiveRadicalAxis_of_common_points
      C K hCK hxC hyC hxK hyK hxy
  have haxisNe : projectiveRadicalAxis Gamma K hGammaK ≠
      projectiveRadicalAxis Gamma C hGammaC := by
    intro hEq
    apply (not_projectivePoint_orthogonal_projectiveRadicalAxis_of_mem_not_mem
      hGammaK haGamma haNotK)
    rw [hEq]
    exact projectivePoint_orthogonal_projectiveRadicalAxis_of_mem
      hGammaC haGamma haC
  have hpencil := projectiveRadicalAxis_pencil_cross
    Gamma C K hGammaC hGammaK hCK
  have hcenter :
      Projectivization.cross (projectiveRadicalAxis Gamma C hGammaC)
        (projectiveRadicalAxis C K hCK) =
      Projectivization.cross (projectiveRadicalAxis Gamma K hGammaK)
        (projectiveRadicalAxis Gamma C hGammaC) := by
    calc
      Projectivization.cross (projectiveRadicalAxis Gamma C hGammaC)
          (projectiveRadicalAxis C K hCK) =
          Projectivization.cross (projectiveRadicalAxis C K hCK)
            (projectiveRadicalAxis Gamma C hGammaC) :=
        Projectivization.cross_comm _ _
      _ = Projectivization.cross (projectiveRadicalAxis Gamma K hGammaK)
            (projectiveRadicalAxis Gamma C hGammaC) := hpencil.symm
  rw [hAB, hXY, hcenter]
  exact Projectivization.cross_orthogonal_left haxisNe

end Erdos506.Incidence
