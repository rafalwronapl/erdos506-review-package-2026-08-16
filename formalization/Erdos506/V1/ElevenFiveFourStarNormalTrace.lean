import Erdos506.Incidence.ProjectiveLineParamTransport
import Erdos506.V1.ElevenFiveFourStarHarmonic

/-!
# Marked actual base traces in the `(9,4,4)` four-star

This module records the part of the normal-trace identification which is
already forced by the saturated finite four-star.  On each actual base
support the four points are precisely its private label and its three
intersections with the other bases.  This is the finite input needed before
the normal-frame calculation can identify their projective coordinates.
-/

namespace Erdos506.V1

open Erdos506.Block
open Erdos506.Finite
open Erdos506.Incidence
open Erdos506.V3
open Erdos506.V4

universe u

/-- The six intersections of distinct standard normal base covectors are
nonzero.  This local public form avoids relying on the private helper in the
normal-form construction. -/
private theorem fourStarNormalOppositeVertex_ne_zero
    (k l : Fin 4) (hkl : k ≠ l) :
    crossProduct (projectiveCovectorNormalLine k)
      (projectiveCovectorNormalLine l) ≠ 0 := by
  fin_cases k <;> fin_cases l <;>
    simp_all [projectiveCovectorNormalLine, cross_apply]

private theorem fourStarNormalCovector_ne_zero (i : Fin 4) :
    projectiveCovectorNormalLine i ≠ 0 := by
  fin_cases i <;> simp [projectiveCovectorNormalLine]

private theorem crossProduct_first_two_ne_zero_of_det_ne_zero
    {u v w : Homogeneous3} (hdet : Matrix.det ![u, v, w] ≠ 0) :
    crossProduct u v ≠ 0 := by
  intro hcross
  apply hdet
  calc
    Matrix.det ![u, v, w] = u ⬝ᵥ crossProduct v w :=
      (triple_product_eq_det u v w).symm
    _ = v ⬝ᵥ crossProduct w u := triple_product_permutation u v w
    _ = w ⬝ᵥ crossProduct u v := triple_product_permutation v w u
    _ = 0 := by rw [hcross, dotProduct_zero]

private theorem crossProduct_first_third_ne_zero_of_det_ne_zero
    {u v w : Homogeneous3} (hdet : Matrix.det ![u, v, w] ≠ 0) :
    crossProduct u w ≠ 0 := by
  intro hcross
  apply hdet
  calc
    Matrix.det ![u, v, w] = v ⬝ᵥ crossProduct w u := by
      exact (triple_product_eq_det u v w).symm.trans
        (triple_product_permutation u v w)
    _ = v ⬝ᵥ (-crossProduct u w) := by rw [cross_anticomm]
    _ = 0 := by rw [hcross]; simp

private theorem crossProduct_last_two_ne_zero_of_det_ne_zero
    {u v w : Homogeneous3} (hdet : Matrix.det ![u, v, w] ≠ 0) :
    crossProduct v w ≠ 0 := by
  intro hcross
  apply hdet
  calc
    Matrix.det ![u, v, w] = u ⬝ᵥ crossProduct v w :=
      (triple_product_eq_det u v w).symm
    _ = 0 := by rw [hcross, dotProduct_zero]

private theorem fourStarOppositeVertex_ne_zero
    (F : FourStarProjectiveSkeleton) (k l : Fin 4) (hkl : k ≠ l) :
    fourStarOppositeVertex F.baseLine k l ≠ 0 := by
  have h01 : crossProduct (F.baseLine 0) (F.baseLine 1) ≠ 0 :=
    crossProduct_first_two_ne_zero_of_det_ne_zero F.base_general_position.det_abc_ne
  have h02 : crossProduct (F.baseLine 0) (F.baseLine 2) ≠ 0 :=
    crossProduct_first_third_ne_zero_of_det_ne_zero F.base_general_position.det_abc_ne
  have h03 : crossProduct (F.baseLine 0) (F.baseLine 3) ≠ 0 :=
    crossProduct_first_third_ne_zero_of_det_ne_zero F.base_general_position.det_abd_ne
  have h12 : crossProduct (F.baseLine 1) (F.baseLine 2) ≠ 0 :=
    crossProduct_last_two_ne_zero_of_det_ne_zero F.base_general_position.det_abc_ne
  have h13 : crossProduct (F.baseLine 1) (F.baseLine 3) ≠ 0 :=
    crossProduct_last_two_ne_zero_of_det_ne_zero F.base_general_position.det_abd_ne
  have h23 : crossProduct (F.baseLine 2) (F.baseLine 3) ≠ 0 :=
    crossProduct_last_two_ne_zero_of_det_ne_zero F.base_general_position.det_acd_ne
  have h10 : crossProduct (F.baseLine 1) (F.baseLine 0) ≠ 0 := by
    rw [← cross_anticomm]
    exact neg_ne_zero.mpr h01
  have h20 : crossProduct (F.baseLine 2) (F.baseLine 0) ≠ 0 := by
    rw [← cross_anticomm]
    exact neg_ne_zero.mpr h02
  have h30 : crossProduct (F.baseLine 3) (F.baseLine 0) ≠ 0 := by
    rw [← cross_anticomm]
    exact neg_ne_zero.mpr h03
  have h21 : crossProduct (F.baseLine 2) (F.baseLine 1) ≠ 0 := by
    rw [← cross_anticomm]
    exact neg_ne_zero.mpr h12
  have h31 : crossProduct (F.baseLine 3) (F.baseLine 1) ≠ 0 := by
    rw [← cross_anticomm]
    exact neg_ne_zero.mpr h13
  have h32 : crossProduct (F.baseLine 3) (F.baseLine 2) ≠ 0 := by
    rw [← cross_anticomm]
    exact neg_ne_zero.mpr h23
  fin_cases k <;> fin_cases l <;> simp_all [fourStarOppositeVertex]

private theorem fourStarNormalLineParameter_choose_ne_zero
    (i : Fin 4) (v : Homogeneous3)
    (hincident : projectiveCovectorNormalLine i ⬝ᵥ v = 0)
    (hv : v ≠ 0) :
    (exists_fourStarNormalLineParameter_of_incident i hincident).choose ≠ 0 := by
  intro hzero
  have hvalue :=
    (exists_fourStarNormalLineParameter_of_incident i hincident).choose_spec
  rw [hzero, fourStarNormalLineParameter_zero] at hvalue
  exact hv hvalue.symm

/-! ## Inverse coordinates on a standard normal base line -/

/-- Projectivizing the injective homogeneous normal-line parametrisation is
still injective.  This is the small but essential step which lets an equality
of projective points recover an equality in `RP¹`, despite arbitrary
homogeneous scales. -/
theorem fourStarNormalLineParameter_projective_injective
    (i : Fin 4) {u v : RealProjectiveLineVector}
    (hu : u ≠ 0) (hv : v ≠ 0)
    (h : Projectivization.mk ℝ (fourStarNormalLineParameter i u)
        (fourStarNormalLineParameter_ne_zero i hu) =
      Projectivization.mk ℝ (fourStarNormalLineParameter i v)
        (fourStarNormalLineParameter_ne_zero i hv)) :
    Projectivization.mk ℝ u hu = Projectivization.mk ℝ v hv := by
  obtain ⟨a, ha⟩ :=
    (Projectivization.mk_eq_mk_iff' ℝ _ _
      (fourStarNormalLineParameter_ne_zero i hu)
      (fourStarNormalLineParameter_ne_zero i hv)).mp h
  apply (Projectivization.mk_eq_mk_iff' ℝ _ _ hu hv).mpr
  refine ⟨a, ?_⟩
  apply fourStarNormalLineParameter_injective i
  have hsmul : fourStarNormalLineParameter i (a • v) =
      a • fourStarNormalLineParameter i v := by
    simpa using (fourStarNormalLineParameter_linear i a 0 v 0)
  exact hsmul.trans ha

/-- Inverse projective coordinate extraction from a nonzero point-vector on
one standard normal base line.  `choose` is safe here because the normal-line
parametrisation is injective, and the preceding theorem proves that the
result is independent of homogeneous scaling. -/
noncomputable def fourStarNormalLineProjectiveCoordinate
    (i : Fin 4) (v : Homogeneous3)
    (hincident : projectiveCovectorNormalLine i ⬝ᵥ v = 0)
    (hv : v ≠ 0) : RealProjectiveOnePoint :=
  let u := (exists_fourStarNormalLineParameter_of_incident i hincident).choose
  Projectivization.mk ℝ u (by
    simpa [u] using
      fourStarNormalLineParameter_choose_ne_zero i v hincident hv)

/-- The extracted coordinate reparametrises the original homogeneous point. -/
theorem fourStarNormalLineProjectiveCoordinate_parameterizes
    (i : Fin 4) (v : Homogeneous3)
    (hincident : projectiveCovectorNormalLine i ⬝ᵥ v = 0)
    (hv : v ≠ 0) :
    Projectivization.mk ℝ
        (fourStarNormalLineParameter i
          (exists_fourStarNormalLineParameter_of_incident i hincident).choose)
        (fourStarNormalLineParameter_ne_zero i (by
          exact fourStarNormalLineParameter_choose_ne_zero i v hincident hv)) =
      Projectivization.mk ℝ v hv := by
  let u := (exists_fourStarNormalLineParameter_of_incident i hincident).choose
  have hu : u ≠ 0 := by
    simpa [u] using fourStarNormalLineParameter_choose_ne_zero i v hincident hv
  have hvalue : fourStarNormalLineParameter i u = v := by
    simpa [u] using
      (exists_fourStarNormalLineParameter_of_incident i hincident).choose_spec
  change Projectivization.mk ℝ (fourStarNormalLineParameter i u) _ =
    Projectivization.mk ℝ v _
  apply (Projectivization.mk_eq_mk_iff' ℝ _ _ _ _).mpr
  exact ⟨1, by simpa using hvalue.symm⟩

/-- If a normal point has an explicitly known `RP¹` representative, inverse
coordinate extraction returns precisely that representative. -/
theorem fourStarNormalLineProjectiveCoordinate_eq_of_projective
    (i : Fin 4) (v : Homogeneous3)
    (hincident : projectiveCovectorNormalLine i ⬝ᵥ v = 0)
    (hv : v ≠ 0) (u : RealProjectiveLineVector) (hu : u ≠ 0)
    (hprojective : Projectivization.mk ℝ v hv =
      Projectivization.mk ℝ (fourStarNormalLineParameter i u)
        (fourStarNormalLineParameter_ne_zero i hu)) :
    fourStarNormalLineProjectiveCoordinate i v hincident hv =
      Projectivization.mk ℝ u hu := by
  unfold fourStarNormalLineProjectiveCoordinate
  let w := (exists_fourStarNormalLineParameter_of_incident i hincident).choose
  have hw : w ≠ 0 := by
    intro hw
    have hvalue :=
      (exists_fourStarNormalLineParameter_of_incident i hincident).choose_spec
    have hvalue' : fourStarNormalLineParameter i w = v := by
      simpa [w] using hvalue
    rw [hw, fourStarNormalLineParameter_zero] at hvalue'
    exact hv hvalue'.symm
  apply fourStarNormalLineParameter_projective_injective i hw hu
  calc
    Projectivization.mk ℝ (fourStarNormalLineParameter i w)
        (fourStarNormalLineParameter_ne_zero i hw) =
      Projectivization.mk ℝ v hv := by
        simpa [w] using
          fourStarNormalLineProjectiveCoordinate_parameterizes i v hincident hv
    _ = Projectivization.mk ℝ (fourStarNormalLineParameter i u)
        (fourStarNormalLineParameter_ne_zero i hu) := hprojective

/-- Inverse coordinate extraction is injective at the level of projective
points on one fixed normal base line.  This is the scale-safe form needed for
the finite trace, whose source points have no preferred homogeneous lifts. -/
theorem fourStarNormalLineProjectiveCoordinate_projective_injective
    (i : Fin 4) (v w : Homogeneous3)
    (hv : v ≠ 0) (hw : w ≠ 0)
    (hvincident : projectiveCovectorNormalLine i ⬝ᵥ v = 0)
    (hwincident : projectiveCovectorNormalLine i ⬝ᵥ w = 0)
    (hcoordinate : fourStarNormalLineProjectiveCoordinate i v hvincident hv =
      fourStarNormalLineProjectiveCoordinate i w hwincident hw) :
    Projectivization.mk ℝ v hv = Projectivization.mk ℝ w hw := by
  let u := (exists_fourStarNormalLineParameter_of_incident i hvincident).choose
  let z := (exists_fourStarNormalLineParameter_of_incident i hwincident).choose
  have hu : u ≠ 0 := by
    intro hzero
    have hvalue :=
      (exists_fourStarNormalLineParameter_of_incident i hvincident).choose_spec
    have hvalue' : fourStarNormalLineParameter i u = v := by
      simpa [u] using hvalue
    rw [hzero, fourStarNormalLineParameter_zero] at hvalue'
    exact hv hvalue'.symm
  have hz : z ≠ 0 := by
    intro hzero
    have hvalue :=
      (exists_fourStarNormalLineParameter_of_incident i hwincident).choose_spec
    have hvalue' : fourStarNormalLineParameter i z = w := by
      simpa [z] using hvalue
    rw [hzero, fourStarNormalLineParameter_zero] at hvalue'
    exact hw hvalue'.symm
  have huz : Projectivization.mk ℝ u hu = Projectivization.mk ℝ z hz := by
    simpa [fourStarNormalLineProjectiveCoordinate, u, z] using hcoordinate
  obtain ⟨a, ha⟩ :=
    (Projectivization.mk_eq_mk_iff' ℝ _ _ hu hz).mp huz
  have hnormal : Projectivization.mk ℝ (fourStarNormalLineParameter i u)
      (fourStarNormalLineParameter_ne_zero i hu) =
      Projectivization.mk ℝ (fourStarNormalLineParameter i z)
        (fourStarNormalLineParameter_ne_zero i hz) := by
    apply (Projectivization.mk_eq_mk_iff' ℝ _ _
      (fourStarNormalLineParameter_ne_zero i hu)
      (fourStarNormalLineParameter_ne_zero i hz)).mpr
    refine ⟨a, ?_⟩
    have hsmul : fourStarNormalLineParameter i (a • z) =
        a • fourStarNormalLineParameter i z := by
      simpa using (fourStarNormalLineParameter_linear i a 0 z 0)
    exact hsmul.symm.trans (congrArg (fourStarNormalLineParameter i) ha)
  calc
    Projectivization.mk ℝ v hv =
        Projectivization.mk ℝ (fourStarNormalLineParameter i u)
          (fourStarNormalLineParameter_ne_zero i hu) := by
      simpa [u] using
        (fourStarNormalLineProjectiveCoordinate_parameterizes i v hvincident hv).symm
    _ = Projectivization.mk ℝ (fourStarNormalLineParameter i z)
          (fourStarNormalLineParameter_ne_zero i hz) := hnormal
    _ = Projectivization.mk ℝ w hw := by
      simpa [z] using
        fourStarNormalLineProjectiveCoordinate_parameterizes i w hwincident hw

/-- Changing a nonzero homogeneous representative by a sign does not change
its projective point. -/
theorem projectivization_mk_eq_mk_neg
    {v : Homogeneous3} (hv : v ≠ 0) :
    Projectivization.mk ℝ v hv =
      Projectivization.mk ℝ (-v) (neg_ne_zero.mpr hv) := by
  apply (Projectivization.mk_eq_mk_iff' ℝ _ _ hv (neg_ne_zero.mpr hv)).mpr
  exact ⟨-1, by simp⟩

/-- Table of the three standard pair-intersection coordinates on each normal
base.  It is intentionally stated independently of the actual four-star, so
the finite relabelled transport below only has to invoke this table. -/
theorem fourStarNormal_pairIntersection_parameter_mem
    (i j : Fin 4) (hij : i ≠ j) :
    ∃ (u : RealProjectiveLineVector) (hu : u ≠ 0),
      Projectivization.mk ℝ
          (crossProduct (projectiveCovectorNormalLine i)
            (projectiveCovectorNormalLine j))
          (fourStarNormalOppositeVertex_ne_zero i j hij) =
        Projectivization.mk ℝ (fourStarNormalLineParameter i u)
          (fourStarNormalLineParameter_ne_zero i hu) ∧
        Projectivization.mk ℝ u hu ∈ fourStarNormalTraceParameterSet i := by
  fin_cases i <;> fin_cases j
  · exact False.elim (hij rfl)

  · refine ⟨realProjectiveLineZeroVector, realProjectiveLineZeroVector_ne_zero, ?_, ?_⟩
    · change Projectivization.mk ℝ (crossProduct (projectiveCovectorNormalLine 0)
          (projectiveCovectorNormalLine 1)) _ =
        Projectivization.mk ℝ (fourStarNormalLineParameter 0 realProjectiveLineZeroVector) _
      apply (Projectivization.mk_eq_mk_iff' ℝ _ _ _ _).mpr
      exact ⟨1, by simpa using fourStarNormalLineParameter_zero_eq_cross01⟩
    · simp [fourStarNormalTraceParameterSet, realProjectiveLineZero]
  · refine ⟨realProjectiveLineInfinityVector, realProjectiveLineInfinityVector_ne_zero, ?_, ?_⟩
    · change Projectivization.mk ℝ (crossProduct (projectiveCovectorNormalLine 0)
          (projectiveCovectorNormalLine 2)) _ =
        Projectivization.mk ℝ (fourStarNormalLineParameter 0 realProjectiveLineInfinityVector) _
      apply (Projectivization.mk_eq_mk_iff' ℝ _ _ _ _).mpr
      exact ⟨-1, by simp [fourStarNormalLineParameter_infinity_eq_neg_cross02]⟩
    · simp [fourStarNormalTraceParameterSet, realProjectiveLineInfinity]
  · refine ⟨fourStarNormalMinusOneVector, fourStarNormalMinusOneVector_ne_zero, ?_, ?_⟩
    · change Projectivization.mk ℝ (crossProduct (projectiveCovectorNormalLine 0)
          (projectiveCovectorNormalLine 3)) _ =
        Projectivization.mk ℝ (fourStarNormalLineParameter 0 fourStarNormalMinusOneVector) _
      apply (Projectivization.mk_eq_mk_iff' ℝ _ _ _ _).mpr
      exact ⟨-1, by simp [fourStarNormalLineParameter_minusOne_eq_neg_cross03]⟩
    · simp [fourStarNormalTraceParameterSet, fourStarNormalMinusOne]
  · refine ⟨realProjectiveLineZeroVector, realProjectiveLineZeroVector_ne_zero, ?_, ?_⟩
    · change Projectivization.mk ℝ (crossProduct (projectiveCovectorNormalLine 1)
          (projectiveCovectorNormalLine 0)) _ =
        Projectivization.mk ℝ (fourStarNormalLineParameter 1 realProjectiveLineZeroVector) _
      apply (Projectivization.mk_eq_mk_iff' ℝ _ _ _ _).mpr
      exact ⟨-1, by simp [fourStarNormalLineParameter_zero_eq_neg_cross10]⟩
    · simp [fourStarNormalTraceParameterSet, realProjectiveLineZero]
  · exact False.elim (hij rfl)
  · refine ⟨realProjectiveLineInfinityVector, realProjectiveLineInfinityVector_ne_zero, ?_, ?_⟩
    · change Projectivization.mk ℝ (crossProduct (projectiveCovectorNormalLine 1)
          (projectiveCovectorNormalLine 2)) _ =
        Projectivization.mk ℝ (fourStarNormalLineParameter 1 realProjectiveLineInfinityVector) _
      apply (Projectivization.mk_eq_mk_iff' ℝ _ _ _ _).mpr
      exact ⟨1, by simpa using fourStarNormalLineParameter_infinity_eq_cross12⟩
    · simp [fourStarNormalTraceParameterSet, realProjectiveLineInfinity]
  · refine ⟨fourStarNormalMinusOneVector, fourStarNormalMinusOneVector_ne_zero, ?_, ?_⟩
    · change Projectivization.mk ℝ (crossProduct (projectiveCovectorNormalLine 1)
          (projectiveCovectorNormalLine 3)) _ =
        Projectivization.mk ℝ (fourStarNormalLineParameter 1 fourStarNormalMinusOneVector) _
      apply (Projectivization.mk_eq_mk_iff' ℝ _ _ _ _).mpr
      exact ⟨1, by simpa using fourStarNormalLineParameter_minusOne_eq_cross13⟩
    · simp [fourStarNormalTraceParameterSet, fourStarNormalMinusOne]
  · refine ⟨realProjectiveLineZeroVector, realProjectiveLineZeroVector_ne_zero, ?_, ?_⟩
    · change Projectivization.mk ℝ (crossProduct (projectiveCovectorNormalLine 2)
          (projectiveCovectorNormalLine 0)) _ =
        Projectivization.mk ℝ (fourStarNormalLineParameter 2 realProjectiveLineZeroVector) _
      apply (Projectivization.mk_eq_mk_iff' ℝ _ _ _ _).mpr
      exact ⟨1, by simpa using fourStarNormalLineParameter_zero_eq_cross20⟩
    · simp [fourStarNormalTraceParameterSet, realProjectiveLineZero]
  · refine ⟨realProjectiveLineInfinityVector, realProjectiveLineInfinityVector_ne_zero, ?_, ?_⟩
    · change Projectivization.mk ℝ (crossProduct (projectiveCovectorNormalLine 2)
          (projectiveCovectorNormalLine 1)) _ =
        Projectivization.mk ℝ (fourStarNormalLineParameter 2 realProjectiveLineInfinityVector) _
      apply (Projectivization.mk_eq_mk_iff' ℝ _ _ _ _).mpr
      exact ⟨-1, by simp [fourStarNormalLineParameter_infinity_eq_neg_cross21]⟩
    · simp [fourStarNormalTraceParameterSet, realProjectiveLineInfinity]
  · exact False.elim (hij rfl)
  · refine ⟨fourStarNormalMinusOneVector, fourStarNormalMinusOneVector_ne_zero, ?_, ?_⟩
    · change Projectivization.mk ℝ (crossProduct (projectiveCovectorNormalLine 2)
          (projectiveCovectorNormalLine 3)) _ =
        Projectivization.mk ℝ (fourStarNormalLineParameter 2 fourStarNormalMinusOneVector) _
      apply (Projectivization.mk_eq_mk_iff' ℝ _ _ _ _).mpr
      exact ⟨-1, by simp [fourStarNormalLineParameter_minusOne_eq_neg_cross23]⟩
    · simp [fourStarNormalTraceParameterSet, fourStarNormalMinusOne]
  · refine ⟨realProjectiveLineZeroVector, realProjectiveLineZeroVector_ne_zero, ?_, ?_⟩
    · change Projectivization.mk ℝ (crossProduct (projectiveCovectorNormalLine 3)
          (projectiveCovectorNormalLine 0)) _ =
        Projectivization.mk ℝ (fourStarNormalLineParameter 3 realProjectiveLineZeroVector) _
      apply (Projectivization.mk_eq_mk_iff' ℝ _ _ _ _).mpr
      exact ⟨1, by simpa using fourStarNormalLineParameter_zero_eq_cross30⟩
    · simp [fourStarNormalTraceParameterSet, realProjectiveLineZero]
  · refine ⟨realProjectiveLineInfinityVector, realProjectiveLineInfinityVector_ne_zero, ?_, ?_⟩
    · change Projectivization.mk ℝ (crossProduct (projectiveCovectorNormalLine 3)
          (projectiveCovectorNormalLine 1)) _ =
        Projectivization.mk ℝ (fourStarNormalLineParameter 3 realProjectiveLineInfinityVector) _
      apply (Projectivization.mk_eq_mk_iff' ℝ _ _ _ _).mpr
      exact ⟨-1, by simp [fourStarNormalLineParameter_infinity_eq_neg_cross31]⟩
    · simp [fourStarNormalTraceParameterSet, realProjectiveLineInfinity]
  · refine ⟨fourStarNormalMinusOneVector, fourStarNormalMinusOneVector_ne_zero, ?_, ?_⟩
    · change Projectivization.mk ℝ (crossProduct (projectiveCovectorNormalLine 3)
          (projectiveCovectorNormalLine 2)) _ =
        Projectivization.mk ℝ (fourStarNormalLineParameter 3 fourStarNormalMinusOneVector) _
      apply (Projectivization.mk_eq_mk_iff' ℝ _ _ _ _).mpr
      exact ⟨1, by simpa using fourStarNormalLineParameter_minusOne_eq_cross32⟩
    · simp [fourStarNormalTraceParameterSet, fourStarNormalMinusOne]
  · exact False.elim (hij rfl)

/-- The private marked point has the remaining normal-trace coordinate on
each base: `1` on the first three bases and `-2` on the fourth. -/
theorem fourStarNormal_private_parameter_mem (i : Fin 4) :
    ∃ (u : RealProjectiveLineVector) (hu : u ≠ 0),
      Projectivization.mk ℝ (fourStarNormalPrivatePoint fourStarNormalSurvivor i)
        (by fin_cases i <;> simp [fourStarNormalPrivatePoint, fourStarNormalSurvivor]) =
        Projectivization.mk ℝ (fourStarNormalLineParameter i u)
          (fourStarNormalLineParameter_ne_zero i hu) ∧
        Projectivization.mk ℝ u hu ∈ fourStarNormalTraceParameterSet i := by
  fin_cases i
  · refine ⟨realProjectiveLineOneVector, realProjectiveLineOneVector_ne_zero, ?_, ?_⟩
    · change Projectivization.mk ℝ (fourStarNormalPrivatePoint fourStarNormalSurvivor 0) _ =
        Projectivization.mk ℝ (fourStarNormalLineParameter 0 realProjectiveLineOneVector) _
      apply (Projectivization.mk_eq_mk_iff' ℝ _ _ _ _).mpr
      exact ⟨1, by simpa using fourStarNormalLineParameter_one_eq_private0⟩
    · simp [fourStarNormalTraceParameterSet, realProjectiveLineOne]
  · refine ⟨realProjectiveLineOneVector, realProjectiveLineOneVector_ne_zero, ?_, ?_⟩
    · change Projectivization.mk ℝ (fourStarNormalPrivatePoint fourStarNormalSurvivor 1) _ =
        Projectivization.mk ℝ (fourStarNormalLineParameter 1 realProjectiveLineOneVector) _
      apply (Projectivization.mk_eq_mk_iff' ℝ _ _ _ _).mpr
      exact ⟨1, by simpa using fourStarNormalLineParameter_one_eq_private1⟩
    · simp [fourStarNormalTraceParameterSet, realProjectiveLineOne]
  · refine ⟨realProjectiveLineOneVector, realProjectiveLineOneVector_ne_zero, ?_, ?_⟩
    · change Projectivization.mk ℝ (fourStarNormalPrivatePoint fourStarNormalSurvivor 2) _ =
        Projectivization.mk ℝ (fourStarNormalLineParameter 2 realProjectiveLineOneVector) _
      apply (Projectivization.mk_eq_mk_iff' ℝ _ _ _ _).mpr
      exact ⟨1, by simpa using fourStarNormalLineParameter_one_eq_private2⟩
    · simp [fourStarNormalTraceParameterSet, realProjectiveLineOne]
  · refine ⟨fourStarNormalMinusTwoVector, fourStarNormalMinusTwoVector_ne_zero, ?_, ?_⟩
    · change Projectivization.mk ℝ (fourStarNormalPrivatePoint fourStarNormalSurvivor 3) _ =
        Projectivization.mk ℝ (fourStarNormalLineParameter 3 fourStarNormalMinusTwoVector) _
      apply (Projectivization.mk_eq_mk_iff' ℝ _ _
        _ _).mpr
      exact ⟨(2 : ℝ)⁻¹, by
        simp [fourStarNormalLineParameter_minusTwo_eq_two_smul_private3]⟩
    · simp [fourStarNormalTraceParameterSet, fourStarNormalMinusTwo]

/-- Public normal-frame form of the intersection calculation.  It is the
projective equality needed to transport an *actual* pair intersection to the
corresponding standard normal intersection; no coordinate choice is made. -/
theorem fourStarNormalForm_transformed_oppositeVertex_projective_eq_normal
    {F : FourStarProjectiveSkeleton} (N : FourStarNormalForm F)
    (k l : Fin 4) (hkl : k ≠ l) :
    Projectivization.mk ℝ
        (projectivePointTransform N.frame.G
          (fourStarOppositeVertex F.baseLine k l))
        ((smul_ne_zero_iff_ne N.frame.G).mpr
          (fourStarOppositeVertex_ne_zero F k l hkl)) =
      Projectivization.mk ℝ
        (crossProduct (projectiveCovectorNormalLine k)
          (projectiveCovectorNormalLine l))
        (fourStarNormalOppositeVertex_ne_zero k l hkl) := by
  let v := fourStarOppositeVertex F.baseLine k l
  let vn := crossProduct (projectiveCovectorNormalLine k)
    (projectiveCovectorNormalLine l)
  have hv : v ≠ 0 := by
    simpa only [v] using fourStarOppositeVertex_ne_zero F k l hkl
  have hvn : vn ≠ 0 := by
    simpa only [vn] using fourStarNormalOppositeVertex_ne_zero k l hkl
  have hvmapped : projectivePointTransform N.frame.G v ≠ 0 :=
    (smul_ne_zero_iff_ne N.frame.G).mpr hv
  have hk0 := fourStarNormalCovector_ne_zero k
  have hl0 := fourStarNormalCovector_ne_zero l
  have hlines :
      Projectivization.mk ℝ (projectiveCovectorNormalLine k) hk0 ≠
        Projectivization.mk ℝ (projectiveCovectorNormalLine l) hl0 := by
    intro heq
    apply hvn
    exact (Projectivization.mk_eq_mk_iff_crossProduct_eq_zero hk0 hl0).1 heq
  have hkInc : projectiveCovectorNormalLine k ⬝ᵥ
      projectivePointTransform N.frame.G v = 0 := by
    apply (projectiveCovectorFrame_incident_normal_iff N.frame k _).2
    simpa only [v, fourStarOppositeVertex] using
      dot_self_cross (F.baseLine k) (F.baseLine l)
  have hlInc : projectiveCovectorNormalLine l ⬝ᵥ
      projectivePointTransform N.frame.G v = 0 := by
    apply (projectiveCovectorFrame_incident_normal_iff N.frame l _).2
    simpa only [v, fourStarOppositeVertex] using
      dot_cross_self (F.baseLine k) (F.baseLine l)
  have hkOrth : Projectivization.orthogonal
      (Projectivization.mk ℝ (projectiveCovectorNormalLine k) hk0)
      (Projectivization.mk ℝ
        (projectivePointTransform N.frame.G v) hvmapped) :=
    (Projectivization.orthogonal_mk hk0 hvmapped).2 hkInc
  have hlOrth : Projectivization.orthogonal
      (Projectivization.mk ℝ (projectiveCovectorNormalLine l) hl0)
      (Projectivization.mk ℝ
        (projectivePointTransform N.frame.G v) hvmapped) :=
    (Projectivization.orthogonal_mk hl0 hvmapped).2 hlInc
  change Projectivization.mk ℝ (projectivePointTransform N.frame.G v) hvmapped =
    Projectivization.mk ℝ vn hvn
  calc
    Projectivization.mk ℝ (projectivePointTransform N.frame.G v) hvmapped =
        Projectivization.cross
          (Projectivization.mk ℝ (projectiveCovectorNormalLine k) hk0)
          (Projectivization.mk ℝ (projectiveCovectorNormalLine l) hl0) :=
      projectiveCovector_eq_cross_of_orthogonal hlines hkOrth hlOrth
    _ = Projectivization.mk ℝ vn hvn := by
      rw [Projectivization.cross_mk_of_ne hk0 hl0 hlines]

/-- The preceding normal-frame equality specialized to the actual selected
intersection of two bases of an inverted `(9,4,4)` pivot. -/
theorem ElevenFivePivotInvertedFourStar.basePairIntersection_normalFrame_projective_eq
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (H : ElevenFivePivotInvertedFourStar cfg p)
    (N : FourStarNormalForm (H.toProjectiveSkeleton H.geometricBoundary))
    (k l : Fin 4) (hkl : k ≠ l) :
    Projectivization.mk ℝ
        (projectivePointTransform N.frame.G
          (homogeneousLift (pivotInversion cfg p
            (H.basePairIntersection k l hkl))))
        ((smul_ne_zero_iff_ne N.frame.G).mpr (homogeneousLift_ne_zero _)) =
      Projectivization.mk ℝ
        (crossProduct (projectiveCovectorNormalLine k)
          (projectiveCovectorNormalLine l))
        (fourStarNormalOppositeVertex_ne_zero k l hkl) := by
  have hbase := H.basePairIntersection_projective_eq_oppositeVertex k l hkl
  have haction : Projectivization.mk ℝ
      (projectivePointTransform N.frame.G
        (homogeneousLift (pivotInversion cfg p (H.basePairIntersection k l hkl))))
      ((smul_ne_zero_iff_ne N.frame.G).mpr (homogeneousLift_ne_zero _)) =
      Projectivization.mk ℝ
        (projectivePointTransform N.frame.G
          (fourStarOppositeVertex
            (H.toProjectiveSkeleton H.geometricBoundary).baseLine k l))
        ((smul_ne_zero_iff_ne N.frame.G).mpr
          (fourStarOppositeVertex_ne_zero
            (H.toProjectiveSkeleton H.geometricBoundary) k l hkl)) := by
    simpa only [projectivePointTransform, Projectivization.smul_mk] using
      congrArg (fun z : RealProjectivePlane => N.frame.G • z) hbase
  exact haction.trans
    (fourStarNormalForm_transformed_oppositeVertex_projective_eq_normal N k l hkl)

/-- The actual private label has the normal private coordinate attached to
the same base index. -/
theorem ElevenFivePivotInvertedFourStar.privateLabel_normalFrame_projective_eq
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (H : ElevenFivePivotInvertedFourStar cfg p)
    (N : FourStarNormalForm (H.toProjectiveSkeleton H.geometricBoundary))
    (i : Fin 4) :
    Projectivization.mk ℝ
        (projectivePointTransform N.frame.G
          (homogeneousLift (pivotInversion cfg p
            (H.privateBaseLabelling.label i))))
        ((smul_ne_zero_iff_ne N.frame.G).mpr (homogeneousLift_ne_zero _)) =
      Projectivization.mk ℝ
        (fourStarNormalPrivatePoint N.determinants i)
        (by
          intro hzero
          have hmap := N.transformed_privatePoint i
          change projectivePointTransform N.frame.G
              (homogeneousLift (pivotInversion cfg p
                (H.privateBaseLabelling.label i))) =
            N.pointScale i • fourStarNormalPrivatePoint N.determinants i at hmap
          rw [hzero, smul_zero] at hmap
          exact (smul_ne_zero_iff_ne N.frame.G).mpr
            (homogeneousLift_ne_zero _) hmap) := by
  have hnormal : fourStarNormalPrivatePoint N.determinants i ≠ 0 := by
    intro hzero
    have hmap := N.transformed_privatePoint i
    change projectivePointTransform N.frame.G
        (homogeneousLift (pivotInversion cfg p
          (H.privateBaseLabelling.label i))) =
        N.pointScale i • fourStarNormalPrivatePoint N.determinants i at hmap
    rw [hzero, smul_zero] at hmap
    exact (smul_ne_zero_iff_ne N.frame.G).mpr
      (homogeneousLift_ne_zero _) hmap
  have hmap := N.transformed_privatePoint i
  change projectivePointTransform N.frame.G
      (homogeneousLift (pivotInversion cfg p
        (H.privateBaseLabelling.label i))) =
      N.pointScale i • fourStarNormalPrivatePoint N.determinants i at hmap
  exact (Projectivization.mk_eq_mk_iff' ℝ _ _
    ((smul_ne_zero_iff_ne N.frame.G).mpr (homogeneousLift_ne_zero _))
    hnormal).2 ⟨N.pointScale i, hmap.symm⟩

/-- The pair-intersection transport with the survivor's relabeling made
explicit.  Thus normal index `i` refers to the original actual base
`σ.symm i`, exactly as in `FourStarProjectiveSkeleton.relabel`. -/
theorem ElevenFivePivotInvertedFourStar.relabelled_basePairIntersection_normalFrame_projective_eq
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (H : ElevenFivePivotInvertedFourStar cfg p)
    (σ : Equiv.Perm FourStarVertex)
    (N : FourStarNormalForm
      ((H.toProjectiveSkeleton H.geometricBoundary).relabel σ))
    (i j : Fin 4) (hij : i ≠ j) :
    Projectivization.mk ℝ
        (projectivePointTransform N.frame.G
          (homogeneousLift (pivotInversion cfg p
            (H.basePairIntersection (σ.symm i) (σ.symm j)
              (σ.symm.injective.ne hij)))))
        ((smul_ne_zero_iff_ne N.frame.G).mpr (homogeneousLift_ne_zero _)) =
      Projectivization.mk ℝ
        (crossProduct (projectiveCovectorNormalLine i)
          (projectiveCovectorNormalLine j))
        (fourStarNormalOppositeVertex_ne_zero i j hij) := by
  have hbase := H.basePairIntersection_projective_eq_oppositeVertex
    (σ.symm i) (σ.symm j) (σ.symm.injective.ne hij)
  have haction : Projectivization.mk ℝ
      (projectivePointTransform N.frame.G
        (homogeneousLift (pivotInversion cfg p
          (H.basePairIntersection (σ.symm i) (σ.symm j)
            (σ.symm.injective.ne hij)))))
      ((smul_ne_zero_iff_ne N.frame.G).mpr (homogeneousLift_ne_zero _)) =
      Projectivization.mk ℝ
        (projectivePointTransform N.frame.G
          (fourStarOppositeVertex
            (H.toProjectiveSkeleton H.geometricBoundary).baseLine
            (σ.symm i) (σ.symm j)))
        ((smul_ne_zero_iff_ne N.frame.G).mpr
          (fourStarOppositeVertex_ne_zero
            (H.toProjectiveSkeleton H.geometricBoundary)
            (σ.symm i) (σ.symm j) (σ.symm.injective.ne hij))) := by
    simpa only [projectivePointTransform, Projectivization.smul_mk] using
      congrArg (fun z : RealProjectivePlane => N.frame.G • z) hbase
  have hnormal :=
    fourStarNormalForm_transformed_oppositeVertex_projective_eq_normal N i j hij
  exact haction.trans (by
    simpa [FourStarProjectiveSkeleton.relabel, fourStarOppositeVertex] using hnormal)

/-- The relabelled private-point transport, in the same index convention as
the preceding pair-intersection theorem. -/
theorem ElevenFivePivotInvertedFourStar.relabelled_privateLabel_normalFrame_projective_eq
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (H : ElevenFivePivotInvertedFourStar cfg p)
    (σ : Equiv.Perm FourStarVertex)
    (N : FourStarNormalForm
      ((H.toProjectiveSkeleton H.geometricBoundary).relabel σ))
    (i : Fin 4) :
    Projectivization.mk ℝ
        (projectivePointTransform N.frame.G
          (homogeneousLift (pivotInversion cfg p
            (H.privateBaseLabelling.label (σ.symm i)))))
        ((smul_ne_zero_iff_ne N.frame.G).mpr (homogeneousLift_ne_zero _)) =
      Projectivization.mk ℝ
        (fourStarNormalPrivatePoint N.determinants i)
        (by
          intro hzero
          have hmap := N.transformed_privatePoint i
          change projectivePointTransform N.frame.G
              (homogeneousLift (pivotInversion cfg p
                (H.privateBaseLabelling.label (σ.symm i)))) =
            N.pointScale i • fourStarNormalPrivatePoint N.determinants i at hmap
          rw [hzero, smul_zero] at hmap
          exact (smul_ne_zero_iff_ne N.frame.G).mpr
            (homogeneousLift_ne_zero _) hmap) := by
  have hnormal : fourStarNormalPrivatePoint N.determinants i ≠ 0 := by
    intro hzero
    have hmap := N.transformed_privatePoint i
    change projectivePointTransform N.frame.G
        (homogeneousLift (pivotInversion cfg p
          (H.privateBaseLabelling.label (σ.symm i)))) =
        N.pointScale i • fourStarNormalPrivatePoint N.determinants i at hmap
    rw [hzero, smul_zero] at hmap
    exact (smul_ne_zero_iff_ne N.frame.G).mpr
      (homogeneousLift_ne_zero _) hmap
  have hmap := N.transformed_privatePoint i
  change projectivePointTransform N.frame.G
      (homogeneousLift (pivotInversion cfg p
        (H.privateBaseLabelling.label (σ.symm i)))) =
      N.pointScale i • fourStarNormalPrivatePoint N.determinants i at hmap
  exact (Projectivization.mk_eq_mk_iff' ℝ _ _
    ((smul_ne_zero_iff_ne N.frame.G).mpr (homogeneousLift_ne_zero _))
    hnormal).2 ⟨N.pointScale i, hmap.symm⟩

/-- The intrinsic `RP¹` coordinate of an actual point on the relabelled base
`i`, extracted after applying its normal frame. -/
noncomputable def ElevenFivePivotInvertedFourStar.relabelledBaseNormalCoordinate
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (H : ElevenFivePivotInvertedFourStar cfg p)
    (σ : Equiv.Perm FourStarVertex)
    (N : FourStarNormalForm
      ((H.toProjectiveSkeleton H.geometricBoundary).relabel σ))
    (i : Fin 4) (x : {x : AwayFrom p // x ∈ H.baseSupport (σ.symm i)}) :
    RealProjectiveOnePoint := by
  let v : Homogeneous3 := projectivePointTransform N.frame.G
    (homogeneousLift (pivotInversion cfg p x.1))
  have hv : v ≠ 0 :=
    (smul_ne_zero_iff_ne N.frame.G).mpr (homogeneousLift_ne_zero _)
  have hbase :
      ((H.toProjectiveSkeleton H.geometricBoundary).relabel σ).baseLine i ⬝ᵥ
        homogeneousLift (pivotInversion cfg p x.1) = 0 := by
    change H.canonicalBaseCovector (σ.symm i) ⬝ᵥ
      homogeneousLift (pivotInversion cfg p x.1) = 0
    rw [dotProduct_comm]
    exact (H.mem_baseSupport_iff_canonicalIncident (σ.symm i) x.1).mp x.2
  have hincident : projectiveCovectorNormalLine i ⬝ᵥ v = 0 := by
    dsimp only [v]
    exact (projectiveCovectorFrame_incident_normal_iff N.frame i _).2 hbase
  exact fourStarNormalLineProjectiveCoordinate i v hincident hv

/-- Any explicit normal homogeneous representative determines the extracted
coordinate of an actual relabelled base point.  This is the reusable bridge
used for the three intersections and the private point. -/
theorem ElevenFivePivotInvertedFourStar.relabelledBaseNormalCoordinate_eq_of_projective
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (H : ElevenFivePivotInvertedFourStar cfg p)
    (σ : Equiv.Perm FourStarVertex)
    (N : FourStarNormalForm
      ((H.toProjectiveSkeleton H.geometricBoundary).relabel σ))
    (i : Fin 4) (x : {x : AwayFrom p // x ∈ H.baseSupport (σ.symm i)})
    (u : RealProjectiveLineVector) (hu : u ≠ 0)
    (hprojective : Projectivization.mk ℝ
        (projectivePointTransform N.frame.G
          (homogeneousLift (pivotInversion cfg p x.1)))
        ((smul_ne_zero_iff_ne N.frame.G).mpr (homogeneousLift_ne_zero _)) =
      Projectivization.mk ℝ (fourStarNormalLineParameter i u)
        (fourStarNormalLineParameter_ne_zero i hu)) :
    H.relabelledBaseNormalCoordinate σ N i x = Projectivization.mk ℝ u hu := by
  unfold ElevenFivePivotInvertedFourStar.relabelledBaseNormalCoordinate
  let v := projectivePointTransform N.frame.G
    (homogeneousLift (pivotInversion cfg p x.1))
  have hincident : projectiveCovectorNormalLine i ⬝ᵥ v = 0 :=
    (projectiveCovectorFrame_incident_normal_iff N.frame i _).2 (by
      change H.canonicalBaseCovector (σ.symm i) ⬝ᵥ
        homogeneousLift (pivotInversion cfg p x.1) = 0
      rw [dotProduct_comm]
      exact (H.mem_baseSupport_iff_canonicalIncident (σ.symm i) x.1).mp x.2)
  have hv : v ≠ 0 :=
    (smul_ne_zero_iff_ne N.frame.G).mpr (homogeneousLift_ne_zero _)
  exact fourStarNormalLineProjectiveCoordinate_eq_of_projective
    i v hincident hv u hu (by simpa only [v] using hprojective)

/-- Equality of extracted coordinates on an actual relabelled base recovers
equality of the corresponding normal-frame projective points. -/
theorem ElevenFivePivotInvertedFourStar.relabelledBaseNormalCoordinate_projective_injective
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (H : ElevenFivePivotInvertedFourStar cfg p)
    (σ : Equiv.Perm FourStarVertex)
    (N : FourStarNormalForm
      ((H.toProjectiveSkeleton H.geometricBoundary).relabel σ))
    (i : Fin 4)
    (x y : {x : AwayFrom p // x ∈ H.baseSupport (σ.symm i)})
    (hcoordinate : H.relabelledBaseNormalCoordinate σ N i x =
      H.relabelledBaseNormalCoordinate σ N i y) :
    Projectivization.mk ℝ
        (projectivePointTransform N.frame.G
          (homogeneousLift (pivotInversion cfg p x.1)))
        ((smul_ne_zero_iff_ne N.frame.G).mpr (homogeneousLift_ne_zero _)) =
      Projectivization.mk ℝ
        (projectivePointTransform N.frame.G
          (homogeneousLift (pivotInversion cfg p y.1)))
        ((smul_ne_zero_iff_ne N.frame.G).mpr (homogeneousLift_ne_zero _)) := by
  unfold ElevenFivePivotInvertedFourStar.relabelledBaseNormalCoordinate at hcoordinate
  exact fourStarNormalLineProjectiveCoordinate_projective_injective i _ _ _ _ _ _
    hcoordinate

/-- The actual inverse-coordinate map on a relabelled base support is
injective.  Projectivization first cancels the normal `GL₃` frame and then the
affine chart and pivot inversion are both injective. -/
theorem ElevenFivePivotInvertedFourStar.relabelledBaseNormalCoordinate_injective
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (H : ElevenFivePivotInvertedFourStar cfg p)
    (σ : Equiv.Perm FourStarVertex)
    (N : FourStarNormalForm
      ((H.toProjectiveSkeleton H.geometricBoundary).relabel σ))
    (i : Fin 4) :
    Function.Injective (H.relabelledBaseNormalCoordinate σ N i) := by
  intro x y hcoordinate
  have hnormal := H.relabelledBaseNormalCoordinate_projective_injective σ N i x y
    hcoordinate
  have hback : projectivePoint (pivotInversion cfg p x.1) =
      projectivePoint (pivotInversion cfg p y.1) := by
    simpa only [projectivePoint, projectivePointTransform,
      Projectivization.smul_mk, inv_smul_smul] using
      congrArg (fun z : RealProjectivePlane => N.frame.G⁻¹ • z) hnormal
  apply Subtype.ext
  apply (pivotInversion cfg p).injective
  apply projectivePoint_injective
  exact hback

/-- Each actual relabelled pair intersection has one of the three prescribed
normal trace coordinates. -/
theorem ElevenFivePivotInvertedFourStar.relabelled_pairIntersection_coordinate_mem_normalTrace
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (H : ElevenFivePivotInvertedFourStar cfg p)
    (σ : Equiv.Perm FourStarVertex)
    (N : FourStarNormalForm
      ((H.toProjectiveSkeleton H.geometricBoundary).relabel σ))
    (i j : Fin 4) (hij : i ≠ j) :
    H.relabelledBaseNormalCoordinate σ N i
        ⟨H.basePairIntersection (σ.symm i) (σ.symm j)
            (σ.symm.injective.ne hij),
          H.basePairIntersection_mem_left (σ.symm i) (σ.symm j)
            (σ.symm.injective.ne hij)⟩ ∈
      fourStarNormalTraceParameterSet i := by
  obtain ⟨u, hu, hnormal, humem⟩ :=
    fourStarNormal_pairIntersection_parameter_mem i j hij
  have hactual := H.relabelled_basePairIntersection_normalFrame_projective_eq
    σ N i j hij
  have hprojective : Projectivization.mk ℝ
      (projectivePointTransform N.frame.G
        (homogeneousLift (pivotInversion cfg p
          (H.basePairIntersection (σ.symm i) (σ.symm j)
            (σ.symm.injective.ne hij)))))
      ((smul_ne_zero_iff_ne N.frame.G).mpr (homogeneousLift_ne_zero _)) =
      Projectivization.mk ℝ (fourStarNormalLineParameter i u)
        (fourStarNormalLineParameter_ne_zero i hu) :=
    hactual.trans hnormal
  rw [H.relabelledBaseNormalCoordinate_eq_of_projective σ N i
    ⟨H.basePairIntersection (σ.symm i) (σ.symm j)
        (σ.symm.injective.ne hij),
      H.basePairIntersection_mem_left (σ.symm i) (σ.symm j)
        (σ.symm.injective.ne hij)⟩ u hu hprojective]
  exact humem

/-- Under the survivor equality, the actual relabelled private label has the
fourth prescribed normal trace coordinate. -/
theorem ElevenFivePivotInvertedFourStar.relabelled_private_coordinate_mem_normalTrace
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (H : ElevenFivePivotInvertedFourStar cfg p)
    (σ : Equiv.Perm FourStarVertex)
    (N : FourStarNormalForm
      ((H.toProjectiveSkeleton H.geometricBoundary).relabel σ))
    (hN : N.determinants = fourStarNormalSurvivor)
    (i : Fin 4) :
    H.relabelledBaseNormalCoordinate σ N i
        ⟨H.privateBaseLabelling.label (σ.symm i),
          H.privateBaseLabelling.label_on_base (σ.symm i)⟩ ∈
      fourStarNormalTraceParameterSet i := by
  obtain ⟨u, hu, hnormal, humem⟩ := fourStarNormal_private_parameter_mem i
  have hactual := H.relabelled_privateLabel_normalFrame_projective_eq σ N i
  have hprojective : Projectivization.mk ℝ
      (projectivePointTransform N.frame.G
        (homogeneousLift (pivotInversion cfg p
          (H.privateBaseLabelling.label (σ.symm i)))))
      ((smul_ne_zero_iff_ne N.frame.G).mpr (homogeneousLift_ne_zero _)) =
      Projectivization.mk ℝ (fourStarNormalLineParameter i u)
        (fourStarNormalLineParameter_ne_zero i hu) := by
    have hactual' : Projectivization.mk ℝ
        (projectivePointTransform N.frame.G
          (homogeneousLift (pivotInversion cfg p
            (H.privateBaseLabelling.label (σ.symm i)))))
        ((smul_ne_zero_iff_ne N.frame.G).mpr (homogeneousLift_ne_zero _)) =
        Projectivization.mk ℝ (fourStarNormalPrivatePoint fourStarNormalSurvivor i)
          (by fin_cases i <;>
            simp [fourStarNormalPrivatePoint, fourStarNormalSurvivor]) := by
      simpa [hN] using hactual
    exact hactual'.trans hnormal
  rw [H.relabelledBaseNormalCoordinate_eq_of_projective σ N i
    ⟨H.privateBaseLabelling.label (σ.symm i),
      H.privateBaseLabelling.label_on_base (σ.symm i)⟩ u hu hprojective]
  exact humem

/-- A saturated actual base support consists exactly of its private point and
its three pair intersections. -/
theorem ElevenFivePivotInvertedFourStar.baseSupport_eq_private_insert_three_intersections
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (H : ElevenFivePivotInvertedFourStar cfg p)
    (i j k l : Fin 4)
    (hij : i ≠ j) (hik : i ≠ k) (hil : i ≠ l)
    (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l) :
    H.baseSupport i =
      {H.privateBaseLabelling.label i,
        H.basePairIntersection i j hij,
        H.basePairIntersection i k hik,
        H.basePairIntersection i l hil} := by
  classical
  let xj := H.basePairIntersection i j hij
  let xk := H.basePairIntersection i k hik
  let xl := H.basePairIntersection i l hil
  let z := H.privateBaseLabelling.label i
  have hzj : z ≠ xj := by
    intro heq
    apply H.finiteEndpointData.private_off i j hij
    change z ∈ H.baseSupport j
    rw [heq]
    exact H.basePairIntersection_mem_right i j hij
  have hzk : z ≠ xk := by
    intro heq
    apply H.finiteEndpointData.private_off i k hik
    change z ∈ H.baseSupport k
    rw [heq]
    exact H.basePairIntersection_mem_right i k hik
  have hzl : z ≠ xl := by
    intro heq
    apply H.finiteEndpointData.private_off i l hil
    change z ∈ H.baseSupport l
    rw [heq]
    exact H.basePairIntersection_mem_right i l hil
  have hjk' : xj ≠ xk := H.basePairIntersection_ne_of_three_distinct hij hik hjk
  have hjl' : xj ≠ xl := H.basePairIntersection_ne_of_three_distinct hij hil hjl
  have hkl' : xk ≠ xl := H.basePairIntersection_ne_of_three_distinct hik hil hkl
  let T : Finset (AwayFrom p) := {z, xj, xk, xl}
  have hsub : T ⊆ H.baseSupport i := by
    intro x hx
    simp only [T, Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact H.privateBaseLabelling.label_on_base i
    · exact H.basePairIntersection_mem_left i j hij
    · exact H.basePairIntersection_mem_left i k hik
    · exact H.basePairIntersection_mem_left i l hil
  have hTcard : T.card = 4 := by
    simp [T, hzj, hzk, hzl, hjk', hjl', hkl']
  have hEq : T = H.baseSupport i :=
    Finset.eq_of_subset_of_card_le hsub (by rw [H.baseSupport_card i, hTcard])
  simpa only [T, z, xj, xk, xl] using hEq.symm

/-- Relabeling changes the actual base index by `σ.symm`. -/
theorem ElevenFivePivotInvertedFourStar.relabelled_baseSupport_eq_private_insert_three_intersections
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (H : ElevenFivePivotInvertedFourStar cfg p)
    (σ : Equiv.Perm FourStarVertex) (i j k l : Fin 4)
    (hij : i ≠ j) (hik : i ≠ k) (hil : i ≠ l)
    (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l) :
    H.baseSupport (σ.symm i) =
      {H.privateBaseLabelling.label (σ.symm i),
        H.basePairIntersection (σ.symm i) (σ.symm j) (σ.symm.injective.ne hij),
        H.basePairIntersection (σ.symm i) (σ.symm k) (σ.symm.injective.ne hik),
        H.basePairIntersection (σ.symm i) (σ.symm l) (σ.symm.injective.ne hil)} := by
  exact H.baseSupport_eq_private_insert_three_intersections
    (σ.symm i) (σ.symm j) (σ.symm k) (σ.symm l)
    (σ.symm.injective.ne hij) (σ.symm.injective.ne hik)
    (σ.symm.injective.ne hil) (σ.symm.injective.ne hjk)
    (σ.symm.injective.ne hjl) (σ.symm.injective.ne hkl)

/-- The finite `RP¹` trace obtained by inverse-coordinate extraction on one
actual relabelled base support.  `image` is used deliberately: exact
four-point cardinality is a consequence, not an assumption. -/
noncomputable def ElevenFivePivotInvertedFourStar.relabelledBaseNormalTrace
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (H : ElevenFivePivotInvertedFourStar cfg p)
    (σ : Equiv.Perm FourStarVertex)
    (N : FourStarNormalForm
      ((H.toProjectiveSkeleton H.geometricBoundary).relabel σ))
    (i : Fin 4) : Finset RealProjectiveOnePoint := by
  classical
  exact (Finset.univ : Finset {x : AwayFrom p // x ∈ H.baseSupport (σ.symm i)}).image
    (H.relabelledBaseNormalCoordinate σ N i)

/-- No actual base point produces any spurious coordinate: after the proven
survivor normalization its finite trace is contained in the normal four-set.
This is the lossless finite half of the desired exact identification. -/
theorem ElevenFivePivotInvertedFourStar.relabelledBaseNormalTrace_subset_normalTrace
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (H : ElevenFivePivotInvertedFourStar cfg p)
    (σ : Equiv.Perm FourStarVertex)
    (N : FourStarNormalForm
      ((H.toProjectiveSkeleton H.geometricBoundary).relabel σ))
    (hN : N.determinants = fourStarNormalSurvivor)
    (i : Fin 4) :
    H.relabelledBaseNormalTrace σ N i ⊆ fourStarNormalTraceParameterSet i := by
  classical
  intro z hz
  rcases Finset.mem_image.mp hz with ⟨x, _hx, rfl⟩
  rcases x with ⟨x, hxmem⟩
  fin_cases i
  · have hsupport := H.relabelled_baseSupport_eq_private_insert_three_intersections
      σ 0 1 2 3 (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide)
    have hx := hxmem
    change x ∈ H.baseSupport (σ.symm 0) at hx
    rw [hsupport] at hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with h | h | h | h
    · subst x
      exact H.relabelled_private_coordinate_mem_normalTrace σ N hN 0
    · subst x
      exact H.relabelled_pairIntersection_coordinate_mem_normalTrace σ N 0 1 (by decide)
    · subst x
      exact H.relabelled_pairIntersection_coordinate_mem_normalTrace σ N 0 2 (by decide)
    · subst x
      exact H.relabelled_pairIntersection_coordinate_mem_normalTrace σ N 0 3 (by decide)
  · have hsupport := H.relabelled_baseSupport_eq_private_insert_three_intersections
      σ 1 0 2 3 (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide)
    have hx := hxmem
    change x ∈ H.baseSupport (σ.symm 1) at hx
    rw [hsupport] at hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with h | h | h | h
    · subst x
      exact H.relabelled_private_coordinate_mem_normalTrace σ N hN 1
    · subst x
      exact H.relabelled_pairIntersection_coordinate_mem_normalTrace σ N 1 0 (by decide)
    · subst x
      exact H.relabelled_pairIntersection_coordinate_mem_normalTrace σ N 1 2 (by decide)
    · subst x
      exact H.relabelled_pairIntersection_coordinate_mem_normalTrace σ N 1 3 (by decide)
  · have hsupport := H.relabelled_baseSupport_eq_private_insert_three_intersections
      σ 2 0 1 3 (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide)
    have hx := hxmem
    change x ∈ H.baseSupport (σ.symm 2) at hx
    rw [hsupport] at hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with h | h | h | h
    · subst x
      exact H.relabelled_private_coordinate_mem_normalTrace σ N hN 2
    · subst x
      exact H.relabelled_pairIntersection_coordinate_mem_normalTrace σ N 2 0 (by decide)
    · subst x
      exact H.relabelled_pairIntersection_coordinate_mem_normalTrace σ N 2 1 (by decide)
    · subst x
      exact H.relabelled_pairIntersection_coordinate_mem_normalTrace σ N 2 3 (by decide)
  · have hsupport := H.relabelled_baseSupport_eq_private_insert_three_intersections
      σ 3 0 1 2 (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide)
    have hx := hxmem
    change x ∈ H.baseSupport (σ.symm 3) at hx
    rw [hsupport] at hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with h | h | h | h
    · subst x
      exact H.relabelled_private_coordinate_mem_normalTrace σ N hN 3
    · subst x
      exact H.relabelled_pairIntersection_coordinate_mem_normalTrace σ N 3 0 (by decide)
    · subst x
      exact H.relabelled_pairIntersection_coordinate_mem_normalTrace σ N 3 1 (by decide)
    · subst x
      exact H.relabelled_pairIntersection_coordinate_mem_normalTrace σ N 3 2 (by decide)

/-- The normal trace has no missing parameter: inverse-coordinate extraction
is injective on the four actual base points, hence its previously proved
subset of the harmonic normal four-set is an equality. -/
theorem ElevenFivePivotInvertedFourStar.relabelledBaseNormalTrace_eq_normalTrace
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (H : ElevenFivePivotInvertedFourStar cfg p)
    (σ : Equiv.Perm FourStarVertex)
    (N : FourStarNormalForm
      ((H.toProjectiveSkeleton H.geometricBoundary).relabel σ))
    (hN : N.determinants = fourStarNormalSurvivor)
    (i : Fin 4) :
    H.relabelledBaseNormalTrace σ N i = fourStarNormalTraceParameterSet i := by
  classical
  have hsource :
      (Finset.univ : Finset {x : AwayFrom p // x ∈ H.baseSupport (σ.symm i)}).card = 4 := by
    rw [Finset.card_univ, Fintype.card_coe, H.baseSupport_card]
  have htracecard : (H.relabelledBaseNormalTrace σ N i).card = 4 := by
    unfold ElevenFivePivotInvertedFourStar.relabelledBaseNormalTrace
    rw [Finset.card_image_iff.mpr
      (H.relabelledBaseNormalCoordinate_injective σ N i).injOn, hsource]
  have hnormalcard : (fourStarNormalTraceParameterSet i).card = 4 :=
    (fourStarNormal_traceParameterSet_harmonic i).1
  apply Finset.eq_of_subset_of_card_le
  · exact H.relabelledBaseNormalTrace_subset_normalTrace σ N hN i
  · rw [hnormalcard, htracecard]

/-- Unconditionally, one relabelled normal frame simultaneously sends every
actual four-point base trace into its prescribed standard normal trace.  The
same `σ` is the survivor relabeling supplied by the determinant argument. -/
theorem ElevenFivePivotInvertedFourStar.exists_relabelledBaseNormalTrace_subset_normalTrace
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (H : ElevenFivePivotInvertedFourStar cfg p) :
    ∃ σ : Equiv.Perm FourStarVertex,
      fourStarRelabelTraceFamily σ H.sizeThreePrivateTraceFamily =
          fourStarCanonicalTrianglePendant ∧
        let N := ((H.toProjectiveSkeleton H.geometricBoundary).relabel σ).toNormalForm
        N.determinants = fourStarNormalSurvivor ∧
          ∀ i : Fin 4,
            H.relabelledBaseNormalTrace σ N i ⊆
              fourStarNormalTraceParameterSet i := by
  obtain ⟨σ, hfamily, hdet, hcoordinates⟩ :=
    H.exists_relabelled_trianglePendant_survivor
  let N := ((H.toProjectiveSkeleton H.geometricBoundary).relabel σ).toNormalForm
  have hN : N.determinants = fourStarNormalSurvivor :=
    FourStarNormalDeterminants.eq_fourStarNormalSurvivor _
      hcoordinates.1 hcoordinates.2.1 hcoordinates.2.2.1 hcoordinates.2.2.2
  refine ⟨σ, hfamily, ?_⟩
  change N.determinants = fourStarNormalSurvivor ∧ _
  refine ⟨hN, ?_⟩
  intro i
  exact H.relabelledBaseNormalTrace_subset_normalTrace σ N hN i

/-- The survivor relabeling gives an exact, simultaneous normal-coordinate
description of every actual four-point base support. -/
theorem ElevenFivePivotInvertedFourStar.exists_relabelledBaseNormalTrace_eq_normalTrace
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (H : ElevenFivePivotInvertedFourStar cfg p) :
    ∃ σ : Equiv.Perm FourStarVertex,
      fourStarRelabelTraceFamily σ H.sizeThreePrivateTraceFamily =
          fourStarCanonicalTrianglePendant ∧
        let N := ((H.toProjectiveSkeleton H.geometricBoundary).relabel σ).toNormalForm
        N.determinants = fourStarNormalSurvivor ∧
          ∀ i : Fin 4,
            H.relabelledBaseNormalTrace σ N i =
              fourStarNormalTraceParameterSet i := by
  obtain ⟨σ, hfamily, hdet, hcoordinates⟩ :=
    H.exists_relabelled_trianglePendant_survivor
  let N := ((H.toProjectiveSkeleton H.geometricBoundary).relabel σ).toNormalForm
  have hN : N.determinants = fourStarNormalSurvivor :=
    FourStarNormalDeterminants.eq_fourStarNormalSurvivor _
      hcoordinates.1 hcoordinates.2.1 hcoordinates.2.2.1 hcoordinates.2.2.2
  refine ⟨σ, hfamily, ?_⟩
  change N.determinants = fourStarNormalSurvivor ∧ _
  refine ⟨hN, ?_⟩
  intro i
  exact H.relabelledBaseNormalTrace_eq_normalTrace σ N hN i

/-- The unconditional pivot survivor supplies a relabeling whose actual
normal-frame determinant record is literally `fourStarNormalSurvivor`.
The finite motif equality is not discarded: it is returned alongside the
coordinate equality, so downstream trace arguments retain the same `σ`. -/
theorem ElevenFivePivotInvertedFourStar.exists_relabelled_normalFrame_survivor
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (H : ElevenFivePivotInvertedFourStar cfg p) :
    ∃ σ : Equiv.Perm FourStarVertex,
      fourStarRelabelTraceFamily σ H.sizeThreePrivateTraceFamily =
          fourStarCanonicalTrianglePendant ∧
        let N := ((H.toProjectiveSkeleton H.geometricBoundary).relabel σ).toNormalForm
        N.determinants = fourStarNormalSurvivor := by
  obtain ⟨σ, hfamily, hdet, hcoordinates⟩ :=
    H.exists_relabelled_trianglePendant_survivor
  refine ⟨σ, hfamily, ?_⟩
  dsimp only
  exact FourStarNormalDeterminants.eq_fourStarNormalSurvivor _
    hcoordinates.1 hcoordinates.2.1 hcoordinates.2.2.1 hcoordinates.2.2.2

/-- Duplicate spelling retained only as a local legacy wrapper. -/
theorem ElevenFivePivotInvertedFourStar.baseSupport_eq_private_insert_three_intersections_legacy
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (H : ElevenFivePivotInvertedFourStar cfg p)
    (i j k l : Fin 4)
    (hij : i ≠ j) (hik : i ≠ k) (hil : i ≠ l)
    (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l) :
    H.baseSupport i =
      {H.privateBaseLabelling.label i,
        H.basePairIntersection i j hij,
        H.basePairIntersection i k hik,
        H.basePairIntersection i l hil} := by
  classical
  let xj := H.basePairIntersection i j hij
  let xk := H.basePairIntersection i k hik
  let xl := H.basePairIntersection i l hil
  let z := H.privateBaseLabelling.label i
  have hzj : z ≠ xj := by
    intro heq
    apply H.finiteEndpointData.private_off i j hij
    change z ∈ H.baseSupport j
    rw [heq]
    exact H.basePairIntersection_mem_right i j hij
  have hzk : z ≠ xk := by
    intro heq
    apply H.finiteEndpointData.private_off i k hik
    change z ∈ H.baseSupport k
    rw [heq]
    exact H.basePairIntersection_mem_right i k hik
  have hzl : z ≠ xl := by
    intro heq
    apply H.finiteEndpointData.private_off i l hil
    change z ∈ H.baseSupport l
    rw [heq]
    exact H.basePairIntersection_mem_right i l hil
  have hjk' : xj ≠ xk :=
    H.basePairIntersection_ne_of_three_distinct hij hik hjk
  have hjl' : xj ≠ xl :=
    H.basePairIntersection_ne_of_three_distinct hij hil hjl
  have hkl' : xk ≠ xl :=
    H.basePairIntersection_ne_of_three_distinct hik hil hkl
  let T : Finset (AwayFrom p) := {z, xj, xk, xl}
  have hsub : T ⊆ H.baseSupport i := by
    intro x hx
    simp only [T, Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact H.privateBaseLabelling.label_on_base i
    · exact H.basePairIntersection_mem_left i j hij
    · exact H.basePairIntersection_mem_left i k hik
    · exact H.basePairIntersection_mem_left i l hil
  have hTcard : T.card = 4 := by
    simp [T, hzj, hzk, hzl, hjk', hjl', hkl']
  have hEq : T = H.baseSupport i :=
    Finset.eq_of_subset_of_card_le hsub (by
      rw [H.baseSupport_card i, hTcard])
  simpa only [T, z, xj, xk, xl] using hEq.symm

/-- Duplicate relabelled spelling retained only as a local legacy wrapper. -/
theorem ElevenFivePivotInvertedFourStar.relabelled_baseSupport_eq_private_insert_three_intersections_legacy
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (H : ElevenFivePivotInvertedFourStar cfg p)
    (σ : Equiv.Perm FourStarVertex) (i j k l : Fin 4)
    (hij : i ≠ j) (hik : i ≠ k) (hil : i ≠ l)
    (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l) :
    H.baseSupport (σ.symm i) =
      {H.privateBaseLabelling.label (σ.symm i),
        H.basePairIntersection (σ.symm i) (σ.symm j) (σ.symm.injective.ne hij),
        H.basePairIntersection (σ.symm i) (σ.symm k) (σ.symm.injective.ne hik),
        H.basePairIntersection (σ.symm i) (σ.symm l) (σ.symm.injective.ne hil)} := by
  exact H.baseSupport_eq_private_insert_three_intersections
    (σ.symm i) (σ.symm j) (σ.symm k) (σ.symm l)
    (σ.symm.injective.ne hij) (σ.symm.injective.ne hik)
    (σ.symm.injective.ne hil) (σ.symm.injective.ne hjk)
    (σ.symm.injective.ne hjl) (σ.symm.injective.ne hkl)

end Erdos506.V1
