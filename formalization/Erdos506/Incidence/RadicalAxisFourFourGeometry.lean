import Erdos506.Incidence.CompleteQuadrangle
import Erdos506.Incidence.RadicalAxisCrossBlockPrinciple
import Erdos506.Incidence.RadicalAxisFourFourLedger
import Erdos506.V3.DirectedPower
import Mathlib.Tactic

/-!
# Radical-axis geometry for the four-by-four cross-block bound

This module contains the geometric layer: normalized circle coefficients,
radical axes, projective chord centres, the two-point fibre bound, and the
complete-quadrangle obstruction to the saturated three-centre profile.
The finite ledger is isolated in `RadicalAxisFourFourLedger`; the final
cross-block specialization is isolated in `RadicalAxisFourFour`.
-/

namespace Erdos506.Incidence

open Erdos506.Finite
open Erdos506.V1
open Erdos506.V3
open Erdos506.V4
open Matrix
open scoped BigOperators LinearAlgebra.Projectivization

/-! ## Circle coefficients and the radical axis -/

/-- The affine circle equation
`x^2 + y^2 + A*x + B*y + C = 0`, bundled as `(A,B,C)`.
Only these three coefficients are needed because the quadratic part is the
same for every Euclidean circle. -/
noncomputable def properCircleCoefficients (c : ProperCircle) : Homogeneous3 :=
  ![properCircleEquationA c, properCircleEquationB c,
    properCircleEquationC c]

@[simp] theorem properCircleCoefficients_zero (c : ProperCircle) :
    properCircleCoefficients c 0 = properCircleEquationA c := rfl

@[simp] theorem properCircleCoefficients_one (c : ProperCircle) :
    properCircleCoefficients c 1 = properCircleEquationB c := rfl

@[simp] theorem properCircleCoefficients_two (c : ProperCircle) :
    properCircleCoefficients c 2 = properCircleEquationC c := rfl

/-- Evaluating the coefficient covector on an affine homogeneous point adds
exactly the common quadratic term missing from the dot product. -/
theorem homogeneousLift_dot_properCircleCoefficients
    (c : ProperCircle) (p : Point2) :
    homogeneousLift p ⬝ᵥ properCircleCoefficients c =
      circleEquation (properCircleEquationA c)
        (properCircleEquationB c) (properCircleEquationC c) p -
          (p 0 ^ 2 + p 1 ^ 2) := by
  simp [properCircleCoefficients, homogeneousLift, circleEquation,
    dotProduct, Fin.sum_univ_three]
  ring

/-- The normalized coefficient vector determines a proper circle uniquely. -/
theorem properCircleCoefficients_injective :
    Function.Injective properCircleCoefficients := by
  intro c d hcoeff
  have hA := congrFun hcoeff (0 : Fin 3)
  have hB := congrFun hcoeff (1 : Fin 3)
  have hC := congrFun hcoeff (2 : Fin 3)
  have hcenter0 : c.1.center 0 = d.1.center 0 := by
    simp only [properCircleCoefficients_zero,
      properCircleEquationA] at hA
    linarith
  have hcenter1 : c.1.center 1 = d.1.center 1 := by
    simp only [properCircleCoefficients_one,
      properCircleEquationB] at hB
    linarith
  have hcenter : c.1.center = d.1.center := by
    ext i
    fin_cases i
    · exact hcenter0
    · exact hcenter1
  have hradiusSq : c.1.radius ^ 2 = d.1.radius ^ 2 := by
    simp only [properCircleCoefficients_two,
      properCircleEquationC] at hC
    rw [hcenter0, hcenter1] at hC
    linarith
  have hradius : c.1.radius = d.1.radius := by
    nlinarith [c.2, d.2]
  apply Subtype.ext
  apply EuclideanGeometry.Sphere.ext
  · exact hcenter
  · exact hradius

/-- Raw homogeneous covector of the radical axis of two circles. -/
noncomputable def radicalAxisCovector (c d : ProperCircle) : Homogeneous3 :=
  properCircleCoefficients c - properCircleCoefficients d

/-- Distinct normalized circle equations have a nonzero difference. -/
theorem radicalAxisCovector_ne_zero {c d : ProperCircle} (hcd : c ≠ d) :
    radicalAxisCovector c d ≠ 0 := by
  intro hzero
  apply hcd
  apply properCircleCoefficients_injective
  exact sub_eq_zero.mp hzero

/-- Evaluation on the radical-axis covector is the difference of the two
circle equations; their common quadratic part cancels. -/
theorem homogeneousLift_dot_radicalAxisCovector
    (c d : ProperCircle) (p : Point2) :
    homogeneousLift p ⬝ᵥ radicalAxisCovector c d =
      circleEquation (properCircleEquationA c)
          (properCircleEquationB c) (properCircleEquationC c) p -
        circleEquation (properCircleEquationA d)
          (properCircleEquationB d) (properCircleEquationC d) p := by
  rw [radicalAxisCovector, dotProduct_sub,
    homogeneousLift_dot_properCircleCoefficients,
    homogeneousLift_dot_properCircleCoefficients]
  ring

/-- Every common point of two circles is incident with their radical axis. -/
theorem homogeneousIncident_radicalAxis_of_mem
    {c d : ProperCircle} {p : Point2}
    (hc : p ∈ (c.1 : Set Point2)) (hd : p ∈ (d.1 : Set Point2)) :
    homogeneousIncident p (radicalAxisCovector c d) := by
  rw [homogeneousIncident, homogeneousLift_dot_radicalAxisCovector]
  rw [(mem_properCircle_iff_equation c p).mp hc,
    (mem_properCircle_iff_equation d p).mp hd]
  ring

/-- A point on exactly one of the two circles is not on their radical axis. -/

theorem not_homogeneousIncident_radicalAxis_of_mem_not_mem
    {c d : ProperCircle} {p : Point2}
    (hc : p ∈ (c.1 : Set Point2)) (hd : p ∉ (d.1 : Set Point2)) :
    ¬ homogeneousIncident p (radicalAxisCovector c d) := by
  intro hincident
  apply hd
  apply (mem_properCircle_iff_equation d p).mpr
  have hcEq := (mem_properCircle_iff_equation c p).mp hc
  rw [homogeneousIncident,
    homogeneousLift_dot_radicalAxisCovector, hcEq] at hincident
  linarith

/-- Symmetric exclusive-point form: a point on the second circle but not the
first is not on their (oriented) radical axis either. -/
theorem not_homogeneousIncident_radicalAxis_of_not_mem_mem
    {c d : ProperCircle} {p : Point2}
    (hc : p ∉ (c.1 : Set Point2)) (hd : p ∈ (d.1 : Set Point2)) :
    ¬ homogeneousIncident p (radicalAxisCovector c d) := by
  intro hincident
  apply hc
  apply (mem_properCircle_iff_equation c p).mpr
  have hdEq := (mem_properCircle_iff_equation d p).mp hd
  rw [homogeneousIncident,
    homogeneousLift_dot_radicalAxisCovector, hdEq] at hincident
  linarith

/-- The projective line represented by the radical-axis covector. -/
noncomputable def projectiveRadicalAxis
    (c d : ProperCircle) (hcd : c ≠ d) : RealProjectivePlane :=
  Projectivization.mk ℝ (radicalAxisCovector c d)
    (radicalAxisCovector_ne_zero hcd)

theorem projectivePoint_orthogonal_projectiveRadicalAxis_of_mem
    {c d : ProperCircle} (hcd : c ≠ d) {p : Point2}
    (hc : p ∈ (c.1 : Set Point2)) (hd : p ∈ (d.1 : Set Point2)) :
    Projectivization.orthogonal (projectivePoint p)
      (projectiveRadicalAxis c d hcd) := by
  simpa only [projectivePoint, projectiveRadicalAxis,
    Projectivization.orthogonal_mk, homogeneousIncident] using
      homogeneousIncident_radicalAxis_of_mem hc hd

theorem not_projectivePoint_orthogonal_projectiveRadicalAxis_of_mem_not_mem
    {c d : ProperCircle} (hcd : c ≠ d) {p : Point2}
    (hc : p ∈ (c.1 : Set Point2)) (hd : p ∉ (d.1 : Set Point2)) :
    ¬ Projectivization.orthogonal (projectivePoint p)
      (projectiveRadicalAxis c d hcd) := by
  simpa only [projectivePoint, projectiveRadicalAxis,
    Projectivization.orthogonal_mk, homogeneousIncident] using
      not_homogeneousIncident_radicalAxis_of_mem_not_mem hc hd

theorem not_projectivePoint_orthogonal_projectiveRadicalAxis_of_not_mem_mem
    {c d : ProperCircle} (hcd : c ≠ d) {p : Point2}
    (hc : p ∉ (c.1 : Set Point2)) (hd : p ∈ (d.1 : Set Point2)) :
    ¬ Projectivization.orthogonal (projectivePoint p)
      (projectiveRadicalAxis c d hcd) := by
  simpa only [projectivePoint, projectiveRadicalAxis,
    Projectivization.orthogonal_mk, homogeneousIncident] using
      not_homogeneousIncident_radicalAxis_of_not_mem_mem hc hd

/-! ## Two elementary projective-line lemmas -/

/-- A projective covector incident with two distinct projective points is
their cross product.  This is the uniqueness of the projective line through
two points, stated in the self-dual coordinate model used here. -/
theorem projectiveCovector_eq_cross_of_orthogonal
    {P Q ell : RealProjectivePlane} (hPQ : P ≠ Q)
    (hP : Projectivization.orthogonal P ell)
    (hQ : Projectivization.orthogonal Q ell) :
    ell = Projectivization.cross P Q := by
  induction P using Projectivization.ind with
  | h p hp =>
      induction Q using Projectivization.ind with
      | h q hq =>
          induction ell using Projectivization.ind with
          | h ell hell =>
              have hpq : crossProduct p q ≠ 0 := by
                exact mt
                  (Projectivization.mk_eq_mk_iff_crossProduct_eq_zero
                    hp hq).mpr hPQ
              have hpell : p ⬝ᵥ ell = 0 := by
                exact (Projectivization.orthogonal_mk hp hell).mp hP
              have hqell : q ⬝ᵥ ell = 0 := by
                exact (Projectivization.orthogonal_mk hq hell).mp hQ
              have hcross : crossProduct (crossProduct p q) ell = 0 := by
                rw [cross_cross_eq_smul_sub_smul, hpell, hqell]
                simp
              have hmk :
                  Projectivization.mk ℝ (crossProduct p q) hpq =
                    Projectivization.mk ℝ ell hell :=
                (Projectivization.mk_eq_mk_iff_crossProduct_eq_zero
                  hpq hell).2 hcross
              rw [Projectivization.cross_mk_of_ne hp hq hPQ]
              exact hmk.symm

/-- Homogeneous incidence with the cross-product covector is equivalent to
ordinary affine membership in the line through two distinct points. -/
theorem homogeneousIncident_lineCovector_iff_mem_affineSpan
    {p q r : Point2} (hpq : p ≠ q) :
    homogeneousIncident r (lineCovector p q) ↔
      r ∈ affineSpan ℝ ({p, q} : Set Point2) := by

  constructor
  · intro hincident
    have heq :
        (q 0 - p 0) * (r 1 - p 1) =
          (q 1 - p 1) * (r 0 - p 0) := by
      simp [homogeneousIncident, lineCovector_eq_vec, homogeneousLift,
        dotProduct, Fin.sum_univ_three] at hincident
      nlinarith
    apply mem_affineSpan_pair_iff_exists_lineMap_eq.mpr
    by_cases hx : q 0 - p 0 = 0
    · have hy : q 1 - p 1 ≠ 0 := by
        intro hy
        apply hpq
        ext i
        fin_cases i
        · exact (sub_eq_zero.mp hx).symm
        · exact (sub_eq_zero.mp hy).symm
      refine ⟨(r 1 - p 1) / (q 1 - p 1), ?_⟩
      ext i
      fin_cases i
      · simp [AffineMap.lineMap_apply]
        field_simp [hy]
        nlinarith
      · simp [AffineMap.lineMap_apply]
        field_simp [hy]
        ring
    · refine ⟨(r 0 - p 0) / (q 0 - p 0), ?_⟩
      ext i
      fin_cases i
      · simp [AffineMap.lineMap_apply]
        field_simp [hx]
        ring
      · simp [AffineMap.lineMap_apply]
        field_simp [hx]
        nlinarith
  · intro hline
    obtain ⟨t, rfl⟩ :=
      mem_affineSpan_pair_iff_exists_lineMap_eq.mp hline
    simp [homogeneousIncident, lineCovector_eq_vec, homogeneousLift,
      dotProduct, Fin.sum_univ_three, AffineMap.lineMap_apply]
    ring

/-- Three pairwise distinct points on a proper circle do not annihilate one
another's line covector. -/
theorem not_homogeneousIncident_lineCovector_of_mem_properCircle
    (c : ProperCircle) {p q r : Point2}
    (hp : p ∈ (c.1 : Set Point2)) (hq : q ∈ (c.1 : Set Point2))
    (hr : r ∈ (c.1 : Set Point2))
    (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r) :
    ¬ homogeneousIncident r (lineCovector p q) := by
  intro hincident
  have hrLine : r ∈ affineSpan ℝ ({p, q} : Set Point2) :=
    (homogeneousIncident_lineCovector_iff_mem_affineSpan hpq).mp hincident
  have hcol : Collinear ℝ ({r, p, q} : Set Point2) :=
    collinear_insert_of_mem_affineSpan_pair hrLine
  have hind : AffineIndependent ℝ ![p, q, r] :=
    (EuclideanGeometry.Sphere.cospherical c.1).affineIndependent_of_mem_of_ne
      hp hq hr hpq hpr hqr
  have hnotCol : ¬ Collinear ℝ ({p, q, r} : Set Point2) :=
    affineIndependent_iff_not_collinear_set.mp hind
  apply hnotCol
  have hset : ({r, p, q} : Set Point2) = ({p, q, r} : Set Point2) := by
    ext x
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    tauto
  rw [← hset]
  exact hcol

/-- Determinant form of the preceding noncollinearity statement. -/
theorem homogeneousLift_det_ne_zero_of_mem_properCircle
    (c : ProperCircle) {p q r : Point2}
    (hp : p ∈ (c.1 : Set Point2)) (hq : q ∈ (c.1 : Set Point2))
    (hr : r ∈ (c.1 : Set Point2))
    (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r) :
    Matrix.det ![homogeneousLift p, homogeneousLift q,
      homogeneousLift r] ≠ 0 := by
  intro hdet
  apply not_homogeneousIncident_lineCovector_of_mem_properCircle
    c hp hq hr hpq hpr hqr
  exact (homogeneousIncident_lineCovector_iff_det_eq_zero p q r).2 hdet


/-! ## Chords and their radical-axis centres -/

section Chords

variable {α : Type*}

/-- Unordered two-subsets of a specified finite point trace. -/
abbrev CircleChord (A : Finset α) := ↥(A.powersetCard 2)

section CircleChordPair

variable [DecidableEq α]

/-- Forget the ambient-trace proof and retain an unordered pair. -/
def circleChordPair {A : Finset α} (e : CircleChord A) : KSubset α 2 :=
  ⟨e.1, (Finset.mem_powersetCard.mp e.2).2⟩

end CircleChordPair

theorem circleChord_subset {A : Finset α} (e : CircleChord A) :
    e.1 ⊆ A :=
  (Finset.mem_powersetCard.mp e.2).1

theorem circleChord_card {A : Finset α} (e : CircleChord A) :
    e.1.card = 2 :=
  (Finset.mem_powersetCard.mp e.2).2

/-- A four-point trace has six unordered chords. -/
theorem fintype_card_circleChord (A : Finset α) :
    Fintype.card (CircleChord A) = Nat.choose A.card 2 := by
  rw [Fintype.card_coe, Finset.card_powersetCard]

theorem fintype_card_circleChord_of_card_four
    {A : Finset α} (hA : A.card = 4) :
    Fintype.card (CircleChord A) = 6 := by
  rw [fintype_card_circleChord, hA]
  norm_num [Nat.choose]

section DecidableChords

variable [DecidableEq α]

/-- Canonical enumeration of the two labels of an unordered pair. -/
noncomputable def chordEquiv (e : KSubset α 2) : ↥e.1 ≃ Fin 2 := by
  classical
  exact Finset.equivFinOfCardEq e.2

/-- The endpoint label in the canonical `Fin 2` enumeration. -/
noncomputable def chordLabel (e : KSubset α 2) (i : Fin 2) : α :=
  ((chordEquiv e).symm i).1

theorem chordLabel_mem (e : KSubset α 2) (i : Fin 2) :
    chordLabel e i ∈ e.1 :=
  ((chordEquiv e).symm i).2

theorem chordLabel_injective (e : KSubset α 2) :
    Function.Injective (chordLabel e) := by
  intro i j hij
  apply (chordEquiv e).symm.injective
  apply Subtype.ext
  exact hij

theorem chordLabel_zero_ne_one (e : KSubset α 2) :
    chordLabel e 0 ≠ chordLabel e 1 :=
  (chordLabel_injective e).ne (by decide)

theorem chordLabel_surjective_on_support (e : KSubset α 2)
    {x : α} (hx : x ∈ e.1) :
    ∃ i : Fin 2, chordLabel e i = x := by
  let xs : ↥e.1 := ⟨x, hx⟩
  refine ⟨chordEquiv e xs, ?_⟩
  exact congrArg Subtype.val ((chordEquiv e).symm_apply_apply xs)

theorem chordSupport_eq_pair (e : KSubset α 2) :
    e.1 = {chordLabel e 0, chordLabel e 1} := by
  ext x
  constructor
  · intro hx
    obtain ⟨i, rfl⟩ := chordLabel_surjective_on_support e hx
    fin_cases i <;> simp
  · intro hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact chordLabel_mem e 0
    · exact chordLabel_mem e 1

/-- Concrete affine endpoints of a labelled chord. -/
noncomputable def chordPoint (cfg : Configuration α)
    (e : KSubset α 2) (i : Fin 2) : Point2 :=
  cfg (chordLabel e i)

theorem chordPoint_zero_ne_one (cfg : Configuration α)
    (e : KSubset α 2) :
    chordPoint cfg e 0 ≠ chordPoint cfg e 1 :=
  cfg.injective.ne (chordLabel_zero_ne_one e)

/-- Projective line covector through the two endpoints of a chord. -/
noncomputable def projectiveChordLine (cfg : Configuration α)
    (e : KSubset α 2) : RealProjectivePlane :=
  projectiveLine (chordPoint cfg e 0) (chordPoint cfg e 1)
    (chordPoint_zero_ne_one cfg e)

/-- Every label of the unordered pair is incident with its projective chord
line, independently of the canonical endpoint ordering. -/
theorem projectivePoint_orthogonal_projectiveChordLine
    (cfg : Configuration α) (e : KSubset α 2) {x : α} (hx : x ∈ e.1) :
    Projectivization.orthogonal (projectivePoint (cfg x))
      (projectiveChordLine cfg e) := by
  obtain ⟨i, hi⟩ := chordLabel_surjective_on_support e hx

  rw [← hi, Projectivization.orthogonal_comm]
  fin_cases i
  · exact projectiveLine_orthogonal_left
      (chordPoint_zero_ne_one cfg e)
  · exact projectiveLine_orthogonal_right
      (chordPoint_zero_ne_one cfg e)

/-- The affine line spanned by the unordered pair is the affine span of its
two canonically enumerated endpoints. -/
theorem lineOfPair_eq_affineSpan_chordPoints
    [Fintype α]
    (cfg : Configuration α) (e : KSubset α 2) :
    lineOfPair cfg e = affineSpan ℝ
      ({chordPoint cfg e 0, chordPoint cfg e 1} : Set Point2) := by
  unfold lineOfPair
  rw [chordSupport_eq_pair e]
  congr 1
  ext p
  simp [chordPoint, eq_comm]

/-- Equal affine pair-spans give equal projective chord covectors. -/
theorem projectiveChordLine_eq_of_lineOfPair_eq
    [Fintype α]
    (cfg : Configuration α) (e k : KSubset α 2)
    (hline : lineOfPair cfg e = lineOfPair cfg k) :
    projectiveChordLine cfg e = projectiveChordLine cfg k := by
  let P := projectivePoint (chordPoint cfg e 0)
  let Q := projectivePoint (chordPoint cfg e 1)
  have hPQ : P ≠ Q :=
    projectivePoint_injective.ne (chordPoint_zero_ne_one cfg e)
  have hPLineE : Projectivization.orthogonal P
      (projectiveChordLine cfg e) := by
    exact projectivePoint_orthogonal_projectiveChordLine cfg e
      (chordLabel_mem e 0)
  have hQLineE : Projectivization.orthogonal Q
      (projectiveChordLine cfg e) := by
    exact projectivePoint_orthogonal_projectiveChordLine cfg e
      (chordLabel_mem e 1)
  have hpMem : chordPoint cfg e 0 ∈ lineOfPair cfg k := by
    rw [← hline, lineOfPair_eq_affineSpan_chordPoints]
    exact subset_affineSpan ℝ _ (by simp)
  have hqMem : chordPoint cfg e 1 ∈ lineOfPair cfg k := by
    rw [← hline, lineOfPair_eq_affineSpan_chordPoints]
    exact subset_affineSpan ℝ _ (by simp)
  rw [lineOfPair_eq_affineSpan_chordPoints] at hpMem hqMem
  have hPLineK : Projectivization.orthogonal P
      (projectiveChordLine cfg k) := by
    have hraw :=
      (homogeneousIncident_lineCovector_iff_mem_affineSpan
        (chordPoint_zero_ne_one cfg k)).2 hpMem
    simpa only [P, projectivePoint, projectiveChordLine, projectiveLine,
      Projectivization.orthogonal_mk, homogeneousIncident] using hraw
  have hQLineK : Projectivization.orthogonal Q
      (projectiveChordLine cfg k) := by
    have hraw :=
      (homogeneousIncident_lineCovector_iff_mem_affineSpan
        (chordPoint_zero_ne_one cfg k)).2 hqMem
    simpa only [Q, projectivePoint, projectiveChordLine, projectiveLine,
      Projectivization.orthogonal_mk, homogeneousIncident] using hraw
  calc
    projectiveChordLine cfg e = Projectivization.cross P Q :=
      projectiveCovector_eq_cross_of_orthogonal hPQ hPLineE hQLineE
    _ = projectiveChordLine cfg k :=
      (projectiveCovector_eq_cross_of_orthogonal
        hPQ hPLineK hQLineK).symm

end DecidableChords

/-- Distinct bundled determined circles have distinct underlying proper
circles. -/
theorem determinedCircle_coe_ne_of_ne
    [Fintype α]
    {cfg : Configuration α}
    {Γ Ω : Erdos506.V1.DeterminedCircle cfg} (hΓΩ : Γ ≠ Ω) :
    Γ.1 ≠ Ω.1 := by
  intro hcoe
  apply hΓΩ
  exact Subtype.ext hcoe

section DecidableChords

variable [DecidableEq α]

/-- Projective intersection of a chord line with a radical axis.  The
definition is total; in all exclusive-trace uses below the two lines are
proved distinct. -/
noncomputable def pairRadicalCenter (cfg : Configuration α)
    (c d : ProperCircle) (hcd : c ≠ d) (e : KSubset α 2) :
    RealProjectivePlane :=
  Projectivization.cross (projectiveChordLine cfg e)
    (projectiveRadicalAxis c d hcd)

/-- An endpoint not incident with the radical axis witnesses that its chord
line is different from that axis. -/
theorem projectiveChordLine_ne_projectiveRadicalAxis_of_endpoint
    (cfg : Configuration α) (c d : ProperCircle) (hcd : c ≠ d)
    (e : KSubset α 2) {x : α} (hx : x ∈ e.1)
    (hnot : ¬ Projectivization.orthogonal (projectivePoint (cfg x))
      (projectiveRadicalAxis c d hcd)) :
    projectiveChordLine cfg e ≠ projectiveRadicalAxis c d hcd := by
  intro heq
  apply hnot
  rw [← heq]
  exact projectivePoint_orthogonal_projectiveChordLine cfg e hx

/-- A chord whose endpoints lie on two distinct circles is their radical
axis, as a projective line covector. -/
theorem projectiveChordLine_eq_projectiveRadicalAxis_of_endpoints
    (cfg : Configuration α) (c d : ProperCircle) (hcd : c ≠ d)
    (e : KSubset α 2)

    (hc₀ : chordPoint cfg e 0 ∈ (c.1 : Set Point2))
    (hc₁ : chordPoint cfg e 1 ∈ (c.1 : Set Point2))
    (hd₀ : chordPoint cfg e 0 ∈ (d.1 : Set Point2))
    (hd₁ : chordPoint cfg e 1 ∈ (d.1 : Set Point2)) :
    projectiveChordLine cfg e = projectiveRadicalAxis c d hcd := by
  let P := projectivePoint (chordPoint cfg e 0)
  let Q := projectivePoint (chordPoint cfg e 1)
  have hPQ : P ≠ Q :=
    projectivePoint_injective.ne (chordPoint_zero_ne_one cfg e)
  have hPaxis : Projectivization.orthogonal P
      (projectiveRadicalAxis c d hcd) :=
    projectivePoint_orthogonal_projectiveRadicalAxis_of_mem
      hcd hc₀ hd₀
  have hQaxis : Projectivization.orthogonal Q
      (projectiveRadicalAxis c d hcd) :=
    projectivePoint_orthogonal_projectiveRadicalAxis_of_mem
      hcd hc₁ hd₁
  have haxis := projectiveCovector_eq_cross_of_orthogonal
    hPQ hPaxis hQaxis
  calc
    projectiveChordLine cfg e = Projectivization.cross P Q := by
      symm
      simpa [P, Q, projectiveChordLine] using
        (projectivePoint_cross_eq_projectiveLine
          (chordPoint_zero_ne_one cfg e))
    _ = projectiveRadicalAxis c d hcd := haxis.symm

/-- Every genuine chord/radical-axis intersection lies on the chord line. -/
theorem pairRadicalCenter_orthogonal_chordLine
    (cfg : Configuration α) (c d : ProperCircle) (hcd : c ≠ d)
    (e : KSubset α 2)
    (hne : projectiveChordLine cfg e ≠ projectiveRadicalAxis c d hcd) :
    Projectivization.orthogonal (pairRadicalCenter cfg c d hcd e)
      (projectiveChordLine cfg e) := by
  exact Projectivization.cross_orthogonal_left hne

/-- Every genuine chord/radical-axis intersection lies on the radical
axis. -/
theorem pairRadicalCenter_orthogonal_radicalAxis
    (cfg : Configuration α) (c d : ProperCircle) (hcd : c ≠ d)
    (e : KSubset α 2)
    (hne : projectiveChordLine cfg e ≠ projectiveRadicalAxis c d hcd) :
    Projectivization.orthogonal (pairRadicalCenter cfg c d hcd e)
      (projectiveRadicalAxis c d hcd) := by
  exact Projectivization.cross_orthogonal_right hne

/-- The three pairwise radical axes of three circles form a projective
pencil.  In raw coefficients this is just
`(c-h) × (c-d) = (d-h) × (c-d)`. -/
theorem projectiveRadicalAxis_pencil_cross
    (c d h : ProperCircle) (hcd : c ≠ d) (hch : c ≠ h) (hdh : d ≠ h) :
    Projectivization.cross (projectiveRadicalAxis c h hch)
        (projectiveRadicalAxis c d hcd) =
      Projectivization.cross (projectiveRadicalAxis d h hdh)
        (projectiveRadicalAxis c d hcd) := by
  let U := radicalAxisCovector c h
  let W := radicalAxisCovector d h
  let R := radicalAxisCovector c d
  have hU : U ≠ 0 := radicalAxisCovector_ne_zero hch
  have hW : W ≠ 0 := radicalAxisCovector_ne_zero hdh
  have hR : R ≠ 0 := radicalAxisCovector_ne_zero hcd
  have hcross : crossProduct U R = crossProduct W R := by
    ext i
    fin_cases i <;>
      simp [U, W, R, radicalAxisCovector, cross_apply] <;> ring
  change Projectivization.cross
      (Projectivization.mk ℝ U hU) (Projectivization.mk ℝ R hR) =
    Projectivization.cross
      (Projectivization.mk ℝ W hW) (Projectivization.mk ℝ R hR)
  by_cases hz : crossProduct U R = 0
  · have hzW : crossProduct W R = 0 := by rw [← hcross, hz]
    rw [Projectivization.cross_mk_of_cross_eq_zero hU hR hz,
      Projectivization.cross_mk_of_cross_eq_zero hW hR hzW]
    have hUR : Projectivization.mk ℝ U hU =
        Projectivization.mk ℝ R hR :=
      (Projectivization.mk_eq_mk_iff_crossProduct_eq_zero hU hR).2 hz
    have hWR : Projectivization.mk ℝ W hW =
        Projectivization.mk ℝ R hR :=
      (Projectivization.mk_eq_mk_iff_crossProduct_eq_zero hW hR).2 hzW
    exact hUR.trans hWR.symm
  · have hzW : crossProduct W R ≠ 0 := by
      rwa [← hcross]
    rw [Projectivization.cross_mk_of_cross_ne_zero hU hR hz,
      Projectivization.cross_mk_of_cross_ne_zero hW hR hzW]
    exact (Projectivization.mk_eq_mk_iff_crossProduct_eq_zero hz hzW).2 (by
      rw [← hcross, _root_.cross_self])

/-- Centre map for chords of the first exclusive trace. -/
noncomputable def firstExclusiveChordCenter
    [Fintype α]
    (cfg : Configuration α) (Γ Ω : Erdos506.V1.DeterminedCircle cfg)
    (hΓΩ : Γ ≠ Ω) :
    CircleChord (exclusiveCircleTrace cfg Γ Ω) → RealProjectivePlane :=
  fun e => pairRadicalCenter cfg Γ.1 Ω.1
    (determinedCircle_coe_ne_of_ne hΓΩ) (circleChordPair e)

/-- Centre map for chords of the second exclusive trace, using the same
orientation of the radical-axis covector. -/
noncomputable def secondExclusiveChordCenter
    [Fintype α]
    (cfg : Configuration α) (Γ Ω : Erdos506.V1.DeterminedCircle cfg)
    (hΓΩ : Γ ≠ Ω) :
    CircleChord (exclusiveCircleTrace cfg Ω Γ) → RealProjectivePlane :=
  fun e => pairRadicalCenter cfg Γ.1 Ω.1
    (determinedCircle_coe_ne_of_ne hΓΩ) (circleChordPair e)


theorem firstExclusiveChordLine_ne_radicalAxis
    [Fintype α]
    (cfg : Configuration α) (Γ Ω : Erdos506.V1.DeterminedCircle cfg)
    (hΓΩ : Γ ≠ Ω)
    (e : CircleChord (exclusiveCircleTrace cfg Γ Ω)) :
    projectiveChordLine cfg (circleChordPair e) ≠
      projectiveRadicalAxis Γ.1 Ω.1
        (determinedCircle_coe_ne_of_ne hΓΩ) := by
  let x := chordLabel (circleChordPair e) 0
  have hxE : x ∈ exclusiveCircleTrace cfg Γ Ω :=
    circleChord_subset e (chordLabel_mem (circleChordPair e) 0)
  have hx := Finset.mem_sdiff.mp hxE
  apply projectiveChordLine_ne_projectiveRadicalAxis_of_endpoint
    cfg Γ.1 Ω.1 (determinedCircle_coe_ne_of_ne hΓΩ)
      (circleChordPair e) (chordLabel_mem (circleChordPair e) 0)
  exact not_projectivePoint_orthogonal_projectiveRadicalAxis_of_mem_not_mem
    (determinedCircle_coe_ne_of_ne hΓΩ)
      (mem_circleTrace.mp hx.1) (by simpa using hx.2)

theorem secondExclusiveChordLine_ne_radicalAxis
    [Fintype α]
    (cfg : Configuration α) (Γ Ω : Erdos506.V1.DeterminedCircle cfg)
    (hΓΩ : Γ ≠ Ω)
    (e : CircleChord (exclusiveCircleTrace cfg Ω Γ)) :
    projectiveChordLine cfg (circleChordPair e) ≠
      projectiveRadicalAxis Γ.1 Ω.1
        (determinedCircle_coe_ne_of_ne hΓΩ) := by
  let x := chordLabel (circleChordPair e) 0
  have hxE : x ∈ exclusiveCircleTrace cfg Ω Γ :=
    circleChord_subset e (chordLabel_mem (circleChordPair e) 0)
  have hx := Finset.mem_sdiff.mp hxE
  apply projectiveChordLine_ne_projectiveRadicalAxis_of_endpoint
    cfg Γ.1 Ω.1 (determinedCircle_coe_ne_of_ne hΓΩ)
      (circleChordPair e) (chordLabel_mem (circleChordPair e) 0)
  exact not_projectivePoint_orthogonal_projectiveRadicalAxis_of_not_mem_mem
    (determinedCircle_coe_ne_of_ne hΓΩ)
      (by simpa using hx.2) (mem_circleTrace.mp hx.1)

theorem firstExclusiveChordCenter_on_radicalAxis
    [Fintype α]
    (cfg : Configuration α) (Γ Ω : Erdos506.V1.DeterminedCircle cfg)
    (hΓΩ : Γ ≠ Ω)
    (e : CircleChord (exclusiveCircleTrace cfg Γ Ω)) :
    Projectivization.orthogonal
      (firstExclusiveChordCenter cfg Γ Ω hΓΩ e)
      (projectiveRadicalAxis Γ.1 Ω.1
        (determinedCircle_coe_ne_of_ne hΓΩ)) :=
  pairRadicalCenter_orthogonal_radicalAxis cfg Γ.1 Ω.1
    (determinedCircle_coe_ne_of_ne hΓΩ) (circleChordPair e)
      (firstExclusiveChordLine_ne_radicalAxis cfg Γ Ω hΓΩ e)

theorem secondExclusiveChordCenter_on_radicalAxis
    [Fintype α]
    (cfg : Configuration α) (Γ Ω : Erdos506.V1.DeterminedCircle cfg)
    (hΓΩ : Γ ≠ Ω)
    (e : CircleChord (exclusiveCircleTrace cfg Ω Γ)) :
    Projectivization.orthogonal
      (secondExclusiveChordCenter cfg Γ Ω hΓΩ e)
      (projectiveRadicalAxis Γ.1 Ω.1
        (determinedCircle_coe_ne_of_ne hΓΩ)) :=
  pairRadicalCenter_orthogonal_radicalAxis cfg Γ.1 Ω.1
    (determinedCircle_coe_ne_of_ne hΓΩ) (circleChordPair e)
      (secondExclusiveChordLine_ne_radicalAxis cfg Γ Ω hΓΩ e)

/-- Two different chords of one proper circle which have the same
radical-axis centre are disjoint, provided the selected circle points are
not themselves on the axis. -/
theorem circleChords_disjoint_of_eq_pairRadicalCenter
    (cfg : Configuration α) (circle c d : ProperCircle) (hcd : c ≠ d)
    (A : Finset α)
    (hcircle : ∀ x ∈ A, cfg x ∈ (circle.1 : Set Point2))
    (hoffAxis : ∀ x ∈ A,
      ¬ Projectivization.orthogonal (projectivePoint (cfg x))
        (projectiveRadicalAxis c d hcd))
    (e k : CircleChord A) (hek : e ≠ k)
    (hcenter :
      pairRadicalCenter cfg c d hcd (circleChordPair e) =
        pairRadicalCenter cfg c d hcd (circleChordPair k)) :
    Disjoint e.1 k.1 := by
  rw [Finset.disjoint_left]
  intro x hxe hxk
  have hxA : x ∈ A := circleChord_subset e hxe
  have hlineE :
      projectiveChordLine cfg (circleChordPair e) ≠
        projectiveRadicalAxis c d hcd :=
    projectiveChordLine_ne_projectiveRadicalAxis_of_endpoint
      cfg c d hcd (circleChordPair e) hxe (hoffAxis x hxA)
  have hlineK :
      projectiveChordLine cfg (circleChordPair k) ≠
        projectiveRadicalAxis c d hcd :=
    projectiveChordLine_ne_projectiveRadicalAxis_of_endpoint
      cfg c d hcd (circleChordPair k) hxk
        (hoffAxis x (circleChord_subset k hxk))
  let P := projectivePoint (cfg x)
  let Q := pairRadicalCenter cfg c d hcd (circleChordPair e)
  have hQAxis : Projectivization.orthogonal Q
      (projectiveRadicalAxis c d hcd) :=
    pairRadicalCenter_orthogonal_radicalAxis cfg c d hcd
      (circleChordPair e) hlineE
  have hPQ : P ≠ Q := by
    intro hPQeq
    apply hoffAxis x hxA
    change Projectivization.orthogonal P (projectiveRadicalAxis c d hcd)
    rw [hPQeq]
    exact hQAxis
  have hPLineE : Projectivization.orthogonal P
      (projectiveChordLine cfg (circleChordPair e)) :=
    projectivePoint_orthogonal_projectiveChordLine cfg

      (circleChordPair e) hxe
  have hPLineK : Projectivization.orthogonal P
      (projectiveChordLine cfg (circleChordPair k)) :=
    projectivePoint_orthogonal_projectiveChordLine cfg
      (circleChordPair k) hxk
  have hQLineE : Projectivization.orthogonal Q
      (projectiveChordLine cfg (circleChordPair e)) :=
    pairRadicalCenter_orthogonal_chordLine cfg c d hcd
      (circleChordPair e) hlineE
  have hQLineK : Projectivization.orthogonal Q
      (projectiveChordLine cfg (circleChordPair k)) := by
    have hk := pairRadicalCenter_orthogonal_chordLine cfg c d hcd
      (circleChordPair k) hlineK
    rw [← hcenter] at hk
    exact hk
  have hlines :
      projectiveChordLine cfg (circleChordPair e) =
        projectiveChordLine cfg (circleChordPair k) := by
    calc
      projectiveChordLine cfg (circleChordPair e) =
          Projectivization.cross P Q :=
        projectiveCovector_eq_cross_of_orthogonal hPQ hPLineE hQLineE
      _ = projectiveChordLine cfg (circleChordPair k) :=
        (projectiveCovector_eq_cross_of_orthogonal
          hPQ hPLineK hQLineK).symm
  have hsupportNe : e.1 ≠ k.1 := by
    intro hsupp
    apply hek
    exact Subtype.ext hsupp
  have hkNotSubset : ¬ k.1 ⊆ e.1 := by
    intro hsub
    apply hsupportNe
    exact (Finset.eq_of_subset_of_card_le hsub (by
      rw [circleChord_card e, circleChord_card k])).symm
  obtain ⟨z, hzk, hzNotE⟩ := Finset.not_subset.mp hkNotSubset
  have hzLineK := projectivePoint_orthogonal_projectiveChordLine cfg
    (circleChordPair k) hzk
  rw [← hlines] at hzLineK
  have hzIncident : homogeneousIncident (cfg z)
      (lineCovector (chordPoint cfg (circleChordPair e) 0)
        (chordPoint cfg (circleChordPair e) 1)) := by
    simpa only [projectivePoint, projectiveChordLine, projectiveLine,
      Projectivization.orthogonal_mk, homogeneousIncident] using hzLineK
  have hzeroCircle := hcircle (chordLabel (circleChordPair e) 0)
    (circleChord_subset e (chordLabel_mem (circleChordPair e) 0))
  have honeCircle := hcircle (chordLabel (circleChordPair e) 1)
    (circleChord_subset e (chordLabel_mem (circleChordPair e) 1))
  have hzCircle := hcircle z (circleChord_subset k hzk)
  have hzeroZ : chordPoint cfg (circleChordPair e) 0 ≠ cfg z := by
    apply cfg.injective.ne
    intro heq
    apply hzNotE
    rw [← heq]
    exact chordLabel_mem (circleChordPair e) 0
  have honeZ : chordPoint cfg (circleChordPair e) 1 ≠ cfg z := by
    apply cfg.injective.ne
    intro heq
    apply hzNotE
    rw [← heq]
    exact chordLabel_mem (circleChordPair e) 1
  exact not_homogeneousIncident_lineCovector_of_mem_properCircle
    circle hzeroCircle honeCircle hzCircle
      (chordPoint_zero_ne_one cfg (circleChordPair e)) hzeroZ honeZ
        hzIncident

/-- A pairwise-disjoint family of two-subsets of a four-set has size at most
two. -/
theorem card_circleChords_le_two_of_pairwise_disjoint
    {A : Finset α} (hA : A.card = 4)
    (F : Finset (CircleChord A))
    (hdisjoint : (F : Set (CircleChord A)).PairwiseDisjoint
      fun e => e.1) :
    F.card ≤ 2 := by
  classical
  have hunionSubset : F.biUnion (fun e => e.1) ⊆ A := by
    intro x hx
    obtain ⟨e, heF, hxe⟩ := Finset.mem_biUnion.mp hx
    exact circleChord_subset e hxe
  have hunionLe : (F.biUnion (fun e => e.1)).card ≤ 4 := by
    rw [← hA]
    exact Finset.card_le_card hunionSubset
  have hunionCard : (F.biUnion (fun e => e.1)).card = 2 * F.card := by
    rw [Finset.card_biUnion hdisjoint]
    calc
      (∑ e ∈ F, e.1.card) = ∑ _e ∈ F, 2 := by
        apply Finset.sum_congr rfl
        intro e _he
        exact circleChord_card e
      _ = 2 * F.card := by simp [Nat.mul_comm]
  rw [hunionCard] at hunionLe
  omega

/-- Every centre fibre for the first exclusive four-trace contains at most
two chords. -/
theorem firstExclusiveChordCenter_fibre_card_le_two
    [Fintype α]
    (cfg : Configuration α) (Γ Ω : Erdos506.V1.DeterminedCircle cfg)
    (hΓΩ : Γ ≠ Ω)
    (hfour : (exclusiveCircleTrace cfg Γ Ω).card = 4)
    (q : RealProjectivePlane) :
    (fullFibre (firstExclusiveChordCenter cfg Γ Ω hΓΩ) q).card ≤ 2 := by

  classical
  apply card_circleChords_le_two_of_pairwise_disjoint hfour
  intro e he k hk hek
  apply circleChords_disjoint_of_eq_pairRadicalCenter
    cfg Γ.1 Γ.1 Ω.1 (determinedCircle_coe_ne_of_ne hΓΩ)
      (exclusiveCircleTrace cfg Γ Ω)
  · intro x hx
    exact mem_circleTrace.mp (Finset.mem_sdiff.mp hx).1
  · intro x hx
    have hx' := Finset.mem_sdiff.mp hx
    exact not_projectivePoint_orthogonal_projectiveRadicalAxis_of_mem_not_mem
      (determinedCircle_coe_ne_of_ne hΓΩ)
        (mem_circleTrace.mp hx'.1) (by simpa using hx'.2)
  · exact hek
  · change e ∈ fullFibre (firstExclusiveChordCenter cfg Γ Ω hΓΩ) q at he
    change k ∈ fullFibre (firstExclusiveChordCenter cfg Γ Ω hΓΩ) q at hk
    exact ((mem_fullFibre _ q e).mp he).trans
      ((mem_fullFibre _ q k).mp hk).symm

/-- Every centre fibre for the second exclusive four-trace contains at most
two chords. -/
theorem secondExclusiveChordCenter_fibre_card_le_two
    [Fintype α]
    (cfg : Configuration α) (Γ Ω : Erdos506.V1.DeterminedCircle cfg)
    (hΓΩ : Γ ≠ Ω)
    (hfour : (exclusiveCircleTrace cfg Ω Γ).card = 4)
    (q : RealProjectivePlane) :
    (fullFibre (secondExclusiveChordCenter cfg Γ Ω hΓΩ) q).card ≤ 2 := by
  classical
  apply card_circleChords_le_two_of_pairwise_disjoint hfour
  intro e he k hk hek
  apply circleChords_disjoint_of_eq_pairRadicalCenter
    cfg Ω.1 Γ.1 Ω.1 (determinedCircle_coe_ne_of_ne hΓΩ)
      (exclusiveCircleTrace cfg Ω Γ)
  · intro x hx
    exact mem_circleTrace.mp (Finset.mem_sdiff.mp hx).1
  · intro x hx
    have hx' := Finset.mem_sdiff.mp hx
    exact not_projectivePoint_orthogonal_projectiveRadicalAxis_of_not_mem_mem
      (determinedCircle_coe_ne_of_ne hΓΩ)
        (by simpa using hx'.2) (mem_circleTrace.mp hx'.1)
  · exact hek
  · change e ∈ fullFibre (secondExclusiveChordCenter cfg Γ Ω hΓΩ) q at he
    change k ∈ fullFibre (secondExclusiveChordCenter cfg Γ Ω hΓΩ) q at hk
    exact ((mem_fullFibre _ q e).mp he).trans
      ((mem_fullFibre _ q k).mp hk).symm

/-! ### Canonical chords of a four-point trace -/

end DecidableChords

/-- Canonical reindexing of a four-point trace. -/
noncomputable def fourTraceEquiv {A : Finset α} (hA : A.card = 4) :
    ↥A ≃ Fin 4 := by
  classical
  exact Finset.equivFinOfCardEq hA

/-- Label at a specified canonical index of a four-point trace. -/
noncomputable def fourTraceLabel {A : Finset α} (hA : A.card = 4)
    (i : Fin 4) : α :=
  ((fourTraceEquiv hA).symm i).1

theorem fourTraceLabel_mem {A : Finset α} (hA : A.card = 4) (i : Fin 4) :
    fourTraceLabel hA i ∈ A :=
  ((fourTraceEquiv hA).symm i).2

theorem fourTraceLabel_injective {A : Finset α} (hA : A.card = 4) :
    Function.Injective (fourTraceLabel hA) := by
  intro i j hij
  apply (fourTraceEquiv hA).symm.injective
  exact Subtype.ext hij

@[simp] theorem fourTraceLabel_inj {A : Finset α} (hA : A.card = 4)
    {i j : Fin 4} :
    fourTraceLabel hA i = fourTraceLabel hA j ↔ i = j :=
  (fourTraceLabel_injective hA).eq_iff

theorem fourTraceLabel_surjective_on_trace
    {A : Finset α} (hA : A.card = 4) {x : α} (hx : x ∈ A) :
    ∃ i : Fin 4, fourTraceLabel hA i = x := by
  let xs : ↥A := ⟨x, hx⟩
  refine ⟨fourTraceEquiv hA xs, ?_⟩
  exact congrArg Subtype.val ((fourTraceEquiv hA).symm_apply_apply xs)

section DecidableFourTrace

variable [DecidableEq α]

/-- Chord joining two distinct canonical vertices. -/
noncomputable def fourTraceChord {A : Finset α} (hA : A.card = 4)
    (i j : Fin 4) (hij : i ≠ j) : CircleChord A := by
  classical
  refine ⟨{fourTraceLabel hA i, fourTraceLabel hA j}, ?_⟩
  apply Finset.mem_powersetCard.mpr
  constructor
  · intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact fourTraceLabel_mem hA i
    · exact fourTraceLabel_mem hA j
  · simp [(fourTraceLabel_injective hA).ne hij]

@[simp] theorem fourTraceChord_support
    {A : Finset α} (hA : A.card = 4)
    (i j : Fin 4) (hij : i ≠ j) :
    (fourTraceChord hA i j hij).1 =
      {fourTraceLabel hA i, fourTraceLabel hA j} := rfl

private theorem fourTraceChord_complement_zero_one
    {A : Finset α} (hA : A.card = 4) :
    A \ (fourTraceChord hA 0 1 (by decide)).1 =
      (fourTraceChord hA 2 3 (by decide)).1 := by

  ext x
  constructor
  · intro hx
    have hxA := (Finset.mem_sdiff.mp hx).1
    have hxNot := (Finset.mem_sdiff.mp hx).2
    obtain ⟨i, rfl⟩ := fourTraceLabel_surjective_on_trace hA hxA
    fin_cases i
    · exact (hxNot (by simp [fourTraceChord])).elim
    · exact (hxNot (by simp [fourTraceChord])).elim
    · simp [fourTraceChord]
    · simp [fourTraceChord]
  · intro hx
    have hxPair : x = fourTraceLabel hA 2 ∨
        x = fourTraceLabel hA 3 := by
      simpa [fourTraceChord] using hx
    rcases hxPair with rfl | rfl
    · exact Finset.mem_sdiff.mpr
        ⟨fourTraceLabel_mem hA 2, by simp [fourTraceChord]⟩
    · exact Finset.mem_sdiff.mpr
        ⟨fourTraceLabel_mem hA 3, by simp [fourTraceChord]⟩

private theorem fourTraceChord_complement_zero_two
    {A : Finset α} (hA : A.card = 4) :
    A \ (fourTraceChord hA 0 2 (by decide)).1 =
      (fourTraceChord hA 1 3 (by decide)).1 := by
  ext x
  constructor
  · intro hx
    have hxA := (Finset.mem_sdiff.mp hx).1
    have hxNot := (Finset.mem_sdiff.mp hx).2
    obtain ⟨i, rfl⟩ := fourTraceLabel_surjective_on_trace hA hxA
    fin_cases i
    · exact (hxNot (by simp [fourTraceChord])).elim
    · simp [fourTraceChord]
    · exact (hxNot (by simp [fourTraceChord])).elim
    · simp [fourTraceChord]
  · intro hx
    have hxPair : x = fourTraceLabel hA 1 ∨
        x = fourTraceLabel hA 3 := by
      simpa [fourTraceChord] using hx
    rcases hxPair with rfl | rfl
    · exact Finset.mem_sdiff.mpr
        ⟨fourTraceLabel_mem hA 1, by simp [fourTraceChord]⟩
    · exact Finset.mem_sdiff.mpr
        ⟨fourTraceLabel_mem hA 3, by simp [fourTraceChord]⟩

private theorem fourTraceChord_complement_zero_three
    {A : Finset α} (hA : A.card = 4) :
    A \ (fourTraceChord hA 0 3 (by decide)).1 =
      (fourTraceChord hA 1 2 (by decide)).1 := by
  ext x
  constructor
  · intro hx
    have hxA := (Finset.mem_sdiff.mp hx).1
    have hxNot := (Finset.mem_sdiff.mp hx).2
    obtain ⟨i, rfl⟩ := fourTraceLabel_surjective_on_trace hA hxA
    fin_cases i
    · exact (hxNot (by simp [fourTraceChord])).elim
    · simp [fourTraceChord]
    · simp [fourTraceChord]
    · exact (hxNot (by simp [fourTraceChord])).elim
  · intro hx
    have hxPair : x = fourTraceLabel hA 1 ∨
        x = fourTraceLabel hA 2 := by
      simpa [fourTraceChord] using hx
    rcases hxPair with rfl | rfl
    · exact Finset.mem_sdiff.mpr
        ⟨fourTraceLabel_mem hA 1, by simp [fourTraceChord]⟩
    · exact Finset.mem_sdiff.mpr
        ⟨fourTraceLabel_mem hA 2, by simp [fourTraceChord]⟩

/-- A disjoint chord of a four-set is its set-theoretic complementary
chord. -/
theorem circleChord_eq_of_disjoint_of_complement_eq
    {A : Finset α} (e opposite k : CircleChord A)
    (hcomplement : A \ e.1 = opposite.1)
    (hdisjoint : Disjoint e.1 k.1) :
    k = opposite := by
  apply Subtype.ext
  have hsubDiff : k.1 ⊆ A \ e.1 := by
    intro x hxk
    apply Finset.mem_sdiff.mpr
    refine ⟨circleChord_subset k hxk, ?_⟩
    intro hxe
    exact Finset.disjoint_left.mp hdisjoint hxe hxk
  rw [hcomplement] at hsubDiff
  exact Finset.eq_of_subset_of_card_le hsubDiff (by
    rw [circleChord_card k, circleChord_card opposite])

/-- A two-element finite set contains an element different from any
prescribed `e`. -/
private theorem exists_ne_mem_of_card_eq_two
    {β : Type*} [DecidableEq β] {F : Finset β} (hF : F.card = 2)
    {e : β} :
    ∃ k ∈ F, k ≠ e := by
  by_contra hnot
  push Not at hnot
  have hsub : F ⊆ {e} := by
    intro k hk
    exact Finset.mem_singleton.mpr (hnot k hk)
  have hle := Finset.card_le_card hsub
  simp [hF] at hle

/-- Specialized disjointness statement for the first exclusive centre map. -/
theorem firstExclusiveChords_disjoint_of_eq_center
    [Fintype α]
    (cfg : Configuration α) (Γ Ω : Erdos506.V1.DeterminedCircle cfg)
    (hΓΩ : Γ ≠ Ω)
    (e k : CircleChord (exclusiveCircleTrace cfg Γ Ω)) (hek : e ≠ k)
    (hcenter : firstExclusiveChordCenter cfg Γ Ω hΓΩ e =
      firstExclusiveChordCenter cfg Γ Ω hΓΩ k) :
    Disjoint e.1 k.1 := by
  apply circleChords_disjoint_of_eq_pairRadicalCenter
    cfg Γ.1 Γ.1 Ω.1 (determinedCircle_coe_ne_of_ne hΓΩ)
      (exclusiveCircleTrace cfg Γ Ω)
  · intro x hx
    exact mem_circleTrace.mp (Finset.mem_sdiff.mp hx).1
  · intro x hx
    have hx' := Finset.mem_sdiff.mp hx
    exact not_projectivePoint_orthogonal_projectiveRadicalAxis_of_mem_not_mem
      (determinedCircle_coe_ne_of_ne hΓΩ)
        (mem_circleTrace.mp hx'.1) (by simpa using hx'.2)
  · exact hek
  · exact hcenter

end DecidableFourTrace

end Chords

/-! ## Excluding the saturated profile by a complete quadrangle -/

section DiagonalSaturation

variable {α : Type*} [DecidableEq α]

/-- A chord covector can be written using any chosen ordering of its two
support labels. -/
theorem projectiveChordLine_eq_projectiveLine_of_mem
    (cfg : Configuration α) (e : KSubset α 2) {a b : α}
    (ha : a ∈ e.1) (hb : b ∈ e.1) (hab : a ≠ b) :
    projectiveChordLine cfg e = projectiveLine (cfg a) (cfg b)
      (cfg.injective.ne hab) := by
  let P := projectivePoint (cfg a)
  let Q := projectivePoint (cfg b)
  have hPQ : P ≠ Q := projectivePoint_injective.ne (cfg.injective.ne hab)
  have hPChord : Projectivization.orthogonal P
      (projectiveChordLine cfg e) :=
    projectivePoint_orthogonal_projectiveChordLine cfg e ha
  have hQChord : Projectivization.orthogonal Q
      (projectiveChordLine cfg e) :=
    projectivePoint_orthogonal_projectiveChordLine cfg e hb
  calc
    projectiveChordLine cfg e = Projectivization.cross P Q :=
      projectiveCovector_eq_cross_of_orthogonal hPQ hPChord hQChord
    _ = projectiveLine (cfg a) (cfg b) (cfg.injective.ne hab) := by
      simpa [P, Q] using
        (projectivePoint_cross_eq_projectiveLine (cfg.injective.ne hab))

/-- Raw form of the intersection of two explicitly ordered chord lines. -/
theorem cross_projectiveLine_eq_mk_cross_lineCovectors
    {p q r s : Point2} (hpq : p ≠ q) (hrs : r ≠ s)
    (hcross : crossProduct (lineCovector p q) (lineCovector r s) ≠ 0) :
    Projectivization.cross (projectiveLine p q hpq)
        (projectiveLine r s hrs) =
      Projectivization.mk ℝ
        (crossProduct (lineCovector p q) (lineCovector r s)) hcross := by
  have hlines :
      Projectivization.mk ℝ (lineCovector p q) (lineCovector_ne_zero hpq) ≠
        Projectivization.mk ℝ (lineCovector r s) (lineCovector_ne_zero hrs) :=
    mt (Projectivization.mk_eq_mk_iff_crossProduct_eq_zero
      (lineCovector_ne_zero hpq) (lineCovector_ne_zero hrs)).mp hcross
  simpa only [projectiveLine] using
    (Projectivization.cross_mk_of_ne
      (lineCovector_ne_zero hpq) (lineCovector_ne_zero hrs) hlines)

/-- Equal first-side centres identify the common centre with the projective
intersection of the two chord lines. -/
theorem firstExclusiveChordCenter_eq_cross_of_eq_center
    [Fintype α]
    (cfg : Configuration α) (Γ Ω : Erdos506.V1.DeterminedCircle cfg)
    (hΓΩ : Γ ≠ Ω)
    (e k : CircleChord (exclusiveCircleTrace cfg Γ Ω))
    (hcenter : firstExclusiveChordCenter cfg Γ Ω hΓΩ e =
      firstExclusiveChordCenter cfg Γ Ω hΓΩ k)
    (hlines : projectiveChordLine cfg (circleChordPair e) ≠
      projectiveChordLine cfg (circleChordPair k)) :
    firstExclusiveChordCenter cfg Γ Ω hΓΩ e =
      Projectivization.cross
        (projectiveChordLine cfg (circleChordPair e))
        (projectiveChordLine cfg (circleChordPair k)) := by
  have heLine := pairRadicalCenter_orthogonal_chordLine
    cfg Γ.1 Ω.1 (determinedCircle_coe_ne_of_ne hΓΩ)
      (circleChordPair e)
      (firstExclusiveChordLine_ne_radicalAxis cfg Γ Ω hΓΩ e)
  have hkLine := pairRadicalCenter_orthogonal_chordLine
    cfg Γ.1 Ω.1 (determinedCircle_coe_ne_of_ne hΓΩ)
      (circleChordPair k)
      (firstExclusiveChordLine_ne_radicalAxis cfg Γ Ω hΓΩ k)
  have heLine' : Projectivization.orthogonal
      (projectiveChordLine cfg (circleChordPair e))
      (firstExclusiveChordCenter cfg Γ Ω hΓΩ e) :=
    Projectivization.orthogonal_comm.mp heLine
  have hkLine' : Projectivization.orthogonal
      (projectiveChordLine cfg (circleChordPair k))
      (firstExclusiveChordCenter cfg Γ Ω hΓΩ e) := by
    apply Projectivization.orthogonal_comm.mp
    rw [hcenter]
    exact hkLine
  exact projectiveCovector_eq_cross_of_orthogonal
    hlines heLine' hkLine'

/-- The saturated equality profile is impossible for the two exclusive
four-point traces of distinct proper circles. -/
theorem not_saturatedThreeCenterProfile_exclusiveCircleChords
    [Fintype α]
    (cfg : Configuration α) (Γ Ω : Erdos506.V1.DeterminedCircle cfg)
    (hΓΩ : Γ ≠ Ω)
    (hfourΓ : (exclusiveCircleTrace cfg Γ Ω).card = 4) :
    ¬ SaturatedThreeCenterProfile
      (firstExclusiveChordCenter cfg Γ Ω hΓΩ)
      (secondExclusiveChordCenter cfg Γ Ω hΓΩ) := by
  classical
  intro hprofile
  rcases hprofile with ⟨_hcentresCard, hfibres⟩
  let A := exclusiveCircleTrace cfg Γ Ω
  let f := firstExclusiveChordCenter cfg Γ Ω hΓΩ
  have hA : A.card = 4 := hfourΓ
  let a := fourTraceLabel hA 0
  let b := fourTraceLabel hA 1
  let c := fourTraceLabel hA 2
  let d := fourTraceLabel hA 3
  let eAB := fourTraceChord hA 0 1 (by decide)
  let eCD := fourTraceChord hA 2 3 (by decide)

  let eAC := fourTraceChord hA 0 2 (by decide)
  let eBD := fourTraceChord hA 1 3 (by decide)
  let eAD := fourTraceChord hA 0 3 (by decide)
  let eBC := fourTraceChord hA 1 2 (by decide)
  have oppositeCenter
      (e opposite : CircleChord A)
      (hcomplement : A \ e.1 = opposite.1) :
      f e = f opposite := by
    have hqmem : f e ∈ Finset.univ.image f :=
      Finset.mem_image.mpr ⟨e, Finset.mem_univ e, rfl⟩
    have hfiberCard : (fullFibre f (f e)).card = 2 :=
      (hfibres (f e) hqmem).1
    obtain ⟨k, hkFiber, hke⟩ :=
      exists_ne_mem_of_card_eq_two hfiberCard
    have hkCenter : f k = f e := (mem_fullFibre f (f e) k).mp hkFiber
    have hdisjoint := firstExclusiveChords_disjoint_of_eq_center
      cfg Γ Ω hΓΩ e k (Ne.symm hke) hkCenter.symm
    have hkOpposite := circleChord_eq_of_disjoint_of_complement_eq
      e opposite k hcomplement hdisjoint
    rw [← hkOpposite]
    exact hkCenter.symm
  have hABCD : f eAB = f eCD :=
    oppositeCenter eAB eCD (by
      simpa [A, eAB, eCD] using fourTraceChord_complement_zero_one hA)
  have hACBD : f eAC = f eBD :=
    oppositeCenter eAC eBD (by
      simpa [A, eAC, eBD] using fourTraceChord_complement_zero_two hA)
  have hADBC : f eAD = f eBC :=
    oppositeCenter eAD eBC (by
      simpa [A, eAD, eBC] using fourTraceChord_complement_zero_three hA)
  have hvertexΓ (i : Fin 4) :
      cfg (fourTraceLabel hA i) ∈ (Γ.1.1 : Set Point2) := by
    apply mem_circleTrace.mp
    exact (Finset.mem_sdiff.mp (fourTraceLabel_mem hA i)).1
  have habLabel : a ≠ b :=
    (fourTraceLabel_injective hA).ne (by decide)
  have hacLabel : a ≠ c :=
    (fourTraceLabel_injective hA).ne (by decide)
  have hadLabel : a ≠ d :=
    (fourTraceLabel_injective hA).ne (by decide)
  have hbcLabel : b ≠ c :=
    (fourTraceLabel_injective hA).ne (by decide)
  have hbdLabel : b ≠ d :=
    (fourTraceLabel_injective hA).ne (by decide)
  have hcdLabel : c ≠ d :=
    (fourTraceLabel_injective hA).ne (by decide)
  have hab : cfg a ≠ cfg b := cfg.injective.ne habLabel
  have hac : cfg a ≠ cfg c := cfg.injective.ne hacLabel
  have had : cfg a ≠ cfg d := cfg.injective.ne hadLabel
  have hbc : cfg b ≠ cfg c := cfg.injective.ne hbcLabel
  have hbd : cfg b ≠ cfg d := cfg.injective.ne hbdLabel
  have hcd : cfg c ≠ cfg d := cfg.injective.ne hcdLabel
  have haΓ : cfg a ∈ (Γ.1.1 : Set Point2) := hvertexΓ 0
  have hbΓ : cfg b ∈ (Γ.1.1 : Set Point2) := hvertexΓ 1
  have hcΓ : cfg c ∈ (Γ.1.1 : Set Point2) := hvertexΓ 2
  have hdΓ : cfg d ∈ (Γ.1.1 : Set Point2) := hvertexΓ 3
  have hgeneral : CompleteQuadrangleGeneralPosition
      (homogeneousLift (cfg a)) (homogeneousLift (cfg b))
      (homogeneousLift (cfg c)) (homogeneousLift (cfg d)) := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · exact homogeneousLift_det_ne_zero_of_mem_properCircle
        Γ.1 haΓ hbΓ hcΓ hab hac hbc
    · exact homogeneousLift_det_ne_zero_of_mem_properCircle
        Γ.1 haΓ hbΓ hdΓ hab had hbd
    · exact homogeneousLift_det_ne_zero_of_mem_properCircle
        Γ.1 haΓ hcΓ hdΓ hac had hcd
    · exact homogeneousLift_det_ne_zero_of_mem_properCircle
        Γ.1 hbΓ hcΓ hdΓ hbc hbd hcd
  have hlineAB : projectiveChordLine cfg (circleChordPair eAB) =
      projectiveLine (cfg a) (cfg b) hab := by
    apply projectiveChordLine_eq_projectiveLine_of_mem cfg
    · change a ∈ eAB.1
      simp [eAB, a, fourTraceChord]
    · change b ∈ eAB.1
      simp [eAB, b, fourTraceChord]
    · exact habLabel
  have hlineCD : projectiveChordLine cfg (circleChordPair eCD) =
      projectiveLine (cfg c) (cfg d) hcd := by
    apply projectiveChordLine_eq_projectiveLine_of_mem cfg
    · change c ∈ eCD.1
      simp [eCD, c, fourTraceChord]
    · change d ∈ eCD.1
      simp [eCD, d, fourTraceChord]
    · exact hcdLabel
  have hlineAC : projectiveChordLine cfg (circleChordPair eAC) =
      projectiveLine (cfg a) (cfg c) hac := by
    apply projectiveChordLine_eq_projectiveLine_of_mem cfg
    · change a ∈ eAC.1
      simp [eAC, a, fourTraceChord]
    · change c ∈ eAC.1
      simp [eAC, c, fourTraceChord]
    · exact hacLabel
  have hlineBD : projectiveChordLine cfg (circleChordPair eBD) =
      projectiveLine (cfg b) (cfg d) hbd := by
    apply projectiveChordLine_eq_projectiveLine_of_mem cfg
    · change b ∈ eBD.1
      simp [eBD, b, fourTraceChord]
    · change d ∈ eBD.1
      simp [eBD, d, fourTraceChord]
    · exact hbdLabel
  have hlineAD : projectiveChordLine cfg (circleChordPair eAD) =
      projectiveLine (cfg a) (cfg d) had := by
    apply projectiveChordLine_eq_projectiveLine_of_mem cfg
    · change a ∈ eAD.1
      simp [eAD, a, fourTraceChord]
    · change d ∈ eAD.1
      simp [eAD, d, fourTraceChord]
    · exact hadLabel
  have hlineBC : projectiveChordLine cfg (circleChordPair eBC) =
      projectiveLine (cfg b) (cfg c) hbc := by

    apply projectiveChordLine_eq_projectiveLine_of_mem cfg
    · change b ∈ eBC.1
      simp [eBC, b, fourTraceChord]
    · change c ∈ eBC.1
      simp [eBC, c, fourTraceChord]
    · exact hbcLabel
  have hABlineNe : projectiveChordLine cfg (circleChordPair eAB) ≠
      projectiveChordLine cfg (circleChordPair eCD) := by
    rw [hlineAB, hlineCD]
    exact mt (Projectivization.mk_eq_mk_iff_crossProduct_eq_zero
      (lineCovector_ne_zero hab) (lineCovector_ne_zero hcd)).mp
        (diagonalAB_CD_ne_zero hgeneral)
  have hAClineNe : projectiveChordLine cfg (circleChordPair eAC) ≠
      projectiveChordLine cfg (circleChordPair eBD) := by
    rw [hlineAC, hlineBD]
    exact mt (Projectivization.mk_eq_mk_iff_crossProduct_eq_zero
      (lineCovector_ne_zero hac) (lineCovector_ne_zero hbd)).mp
        (diagonalAC_BD_ne_zero hgeneral)
  have hADlineNe : projectiveChordLine cfg (circleChordPair eAD) ≠
      projectiveChordLine cfg (circleChordPair eBC) := by
    rw [hlineAD, hlineBC]
    exact mt (Projectivization.mk_eq_mk_iff_crossProduct_eq_zero
      (lineCovector_ne_zero had) (lineCovector_ne_zero hbc)).mp
        (diagonalAD_BC_ne_zero hgeneral)
  have hdiagAB : f eAB = projectiveDiagonalAB_CD
      (homogeneousLift (cfg a)) (homogeneousLift (cfg b))
      (homogeneousLift (cfg c)) (homogeneousLift (cfg d)) hgeneral := by
    calc
      f eAB = Projectivization.cross
          (projectiveChordLine cfg (circleChordPair eAB))
          (projectiveChordLine cfg (circleChordPair eCD)) :=
        firstExclusiveChordCenter_eq_cross_of_eq_center
          cfg Γ Ω hΓΩ eAB eCD hABCD hABlineNe
      _ = Projectivization.cross (projectiveLine (cfg a) (cfg b) hab)
          (projectiveLine (cfg c) (cfg d) hcd) := by rw [hlineAB, hlineCD]
      _ = _ := by
        simpa [projectiveDiagonalAB_CD, diagonalAB_CD, lineCovector] using
          (cross_projectiveLine_eq_mk_cross_lineCovectors
            hab hcd (diagonalAB_CD_ne_zero hgeneral))
  have hdiagAC : f eAC = projectiveDiagonalAC_BD
      (homogeneousLift (cfg a)) (homogeneousLift (cfg b))
      (homogeneousLift (cfg c)) (homogeneousLift (cfg d)) hgeneral := by
    calc
      f eAC = Projectivization.cross
          (projectiveChordLine cfg (circleChordPair eAC))
          (projectiveChordLine cfg (circleChordPair eBD)) :=
        firstExclusiveChordCenter_eq_cross_of_eq_center
          cfg Γ Ω hΓΩ eAC eBD hACBD hAClineNe
      _ = Projectivization.cross (projectiveLine (cfg a) (cfg c) hac)
          (projectiveLine (cfg b) (cfg d) hbd) := by rw [hlineAC, hlineBD]
      _ = _ := by
        simpa [projectiveDiagonalAC_BD, diagonalAC_BD, lineCovector] using
          (cross_projectiveLine_eq_mk_cross_lineCovectors
            hac hbd (diagonalAC_BD_ne_zero hgeneral))
  have hdiagAD : f eAD = projectiveDiagonalAD_BC
      (homogeneousLift (cfg a)) (homogeneousLift (cfg b))
      (homogeneousLift (cfg c)) (homogeneousLift (cfg d)) hgeneral := by
    calc
      f eAD = Projectivization.cross
          (projectiveChordLine cfg (circleChordPair eAD))
          (projectiveChordLine cfg (circleChordPair eBC)) :=
        firstExclusiveChordCenter_eq_cross_of_eq_center
          cfg Γ Ω hΓΩ eAD eBC hADBC hADlineNe
      _ = Projectivization.cross (projectiveLine (cfg a) (cfg d) had)
          (projectiveLine (cfg b) (cfg c) hbc) := by rw [hlineAD, hlineBC]
      _ = _ := by
        simpa [projectiveDiagonalAD_BC, diagonalAD_BC, lineCovector] using
          (cross_projectiveLine_eq_mk_cross_lineCovectors
            had hbc (diagonalAD_BC_ne_zero hgeneral))
  have hABaxis := firstExclusiveChordCenter_on_radicalAxis
    cfg Γ Ω hΓΩ eAB
  have hACaxis := firstExclusiveChordCenter_on_radicalAxis
    cfg Γ Ω hΓΩ eAC
  have hADaxis := firstExclusiveChordCenter_on_radicalAxis
    cfg Γ Ω hΓΩ eAD
  change Projectivization.orthogonal (f eAB)
    (projectiveRadicalAxis Γ.1 Ω.1
      (determinedCircle_coe_ne_of_ne hΓΩ)) at hABaxis
  change Projectivization.orthogonal (f eAC)
    (projectiveRadicalAxis Γ.1 Ω.1
      (determinedCircle_coe_ne_of_ne hΓΩ)) at hACaxis
  change Projectivization.orthogonal (f eAD)
    (projectiveRadicalAxis Γ.1 Ω.1
      (determinedCircle_coe_ne_of_ne hΓΩ)) at hADaxis
  rw [hdiagAB] at hABaxis
  rw [hdiagAC] at hACaxis
  rw [hdiagAD] at hADaxis
  exact (completeQuadrangle_projectiveDiagonals_noncollinear hgeneral)
    ⟨projectiveRadicalAxis Γ.1 Ω.1
        (determinedCircle_coe_ne_of_ne hΓΩ),
      hABaxis, hACaxis, hADaxis⟩

end DiagonalSaturation

end Erdos506.Incidence
