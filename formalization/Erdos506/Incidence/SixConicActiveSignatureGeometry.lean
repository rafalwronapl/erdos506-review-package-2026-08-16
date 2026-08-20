import Erdos506.Incidence.RadicalAxisFourFourGeometry
import Erdos506.Incidence.RealCircleProjectiveParametrization
import Erdos506.Incidence.SixConicActiveSignatureCap
import Mathlib.Data.Finset.Sort
import Mathlib.Logic.Equiv.Fin.Rotate
import Mathlib.Order.Circular.ZMod
import Mathlib.Tactic

/-!
# The geometric four-signature bound on a six-point circle

This file closes the geometric bridge left explicit in
`SixConicActiveSignatureCap`.  The six marked points are first put in their
intrinsic cyclic order by an affine chart of `RP¹`.  For a full outsider
edge, the three marked chords are radical axes of a pencil of circles through
that edge.  Their common projective centre is off the selected circle, hence
the residual-intersection map is a genuine projective involution.  Its action
on the six cyclic labels is fixed-point-free and either preserves or reverses
cyclic order, so it is one of `R3,S1,S3,S5`.

No extremal bound, endpoint statement, or additional geometric witness is
assumed here.
-/

namespace Erdos506.Incidence

open Erdos506.V1
open Erdos506.V4
open Erdos506.Finite
open Matrix
open scoped LinearAlgebra.Projectivization

universe u

/-! ## A cyclic enumeration of a finite six-subset of `RP¹` -/

/-- A real affine coordinate on an `RP¹` chart whose point at infinity is
represented by `(1,t)`. -/
noncomputable def realProjectiveChartCoordinate
    (t : ℝ) (P : RealProjectiveOnePoint) : ℝ :=
  P.rep 0 / (P.rep 1 - t * P.rep 0)

private theorem div_mul_pair_cancel_left
    (x a b : ℝ) (ha : a ≠ 0) : x / a * (a * b) = x * b := by
  calc
    x / a * (a * b) = (x / a * a) * b := by ring
    _ = x * b := by rw [div_mul_cancel₀ x ha]

private theorem div_mul_pair_cancel_right
    (x a b : ℝ) (hb : b ≠ 0) : x / b * (a * b) = a * x := by
  calc
    x / b * (a * b) = a * (x / b * b) := by ring
    _ = a * x := by rw [div_mul_cancel₀ x hb]

private theorem realProjective_eq_of_chartCoordinate_eq
    (t : ℝ) {P Q : RealProjectiveOnePoint}
    (hP : P.rep 1 - t * P.rep 0 ≠ 0)
    (hQ : Q.rep 1 - t * Q.rep 0 ≠ 0)
    (hcoord : realProjectiveChartCoordinate t P =
      realProjectiveChartCoordinate t Q) :
    P = Q := by
  have hbracket : realProjectiveBracket P.rep Q.rep = 0 := by
    unfold realProjectiveChartCoordinate at hcoord
    have hmul := (div_eq_div_iff hP hQ).mp hcoord
    unfold realProjectiveBracket
    linear_combination hmul
  calc
    P = Projectivization.mk ℝ P.rep P.rep_nonzero :=
      (Projectivization.mk_rep P).symm
    _ = Projectivization.mk ℝ Q.rep Q.rep_nonzero :=
      (realProjective_mk_eq_mk_iff_bracket_eq_zero
        P.rep_nonzero Q.rep_nonzero).2 hbracket
    _ = Q := Projectivization.mk_rep Q

/-- Positivity of the representative triple bracket is an intrinsic
characterization of the cyclic relation. -/
private theorem realProjectiveCyclic_iff_rep
    (P Q R : RealProjectiveOnePoint) :
    RealProjectiveCyclic P Q R ↔
      0 < realProjectiveTripleBracket P.rep Q.rep R.rep := by
  constructor
  · rintro ⟨p, q, r, hp, hq, hr, hP, hQ, hR, hpositive⟩
    have hpScale : ∃ a : ℝ, a • p = P.rep := by
      apply (Projectivization.mk_eq_mk_iff' ℝ P.rep p
        P.rep_nonzero hp).1
      rw [Projectivization.mk_rep]
      exact hP
    have hqScale : ∃ b : ℝ, b • q = Q.rep := by
      apply (Projectivization.mk_eq_mk_iff' ℝ Q.rep q
        Q.rep_nonzero hq).1
      rw [Projectivization.mk_rep]
      exact hQ
    have hrScale : ∃ c : ℝ, c • r = R.rep := by
      apply (Projectivization.mk_eq_mk_iff' ℝ R.rep r
        R.rep_nonzero hr).1
      rw [Projectivization.mk_rep]
      exact hR
    obtain ⟨a, ha⟩ := hpScale
    obtain ⟨b, hb⟩ := hqScale
    obtain ⟨c, hc⟩ := hrScale
    have ha0 : a ≠ 0 := by
      intro ha0
      apply P.rep_nonzero
      rw [← ha, ha0, zero_smul]
    have hb0 : b ≠ 0 := by
      intro hb0
      apply Q.rep_nonzero
      rw [← hb, hb0, zero_smul]
    have hc0 : c ≠ 0 := by
      intro hc0
      apply R.rep_nonzero
      rw [← hc, hc0, zero_smul]
    rw [← ha, ← hb, ← hc,
      realProjectiveTripleBracket_smul]
    exact mul_pos (sq_pos_of_ne_zero (mul_ne_zero (mul_ne_zero ha0 hb0) hc0))
      hpositive
  · intro hpositive
    exact ⟨P.rep, Q.rep, R.rep, P.rep_nonzero, Q.rep_nonzero,
      R.rep_nonzero, (Projectivization.mk_rep P).symm,
      (Projectivization.mk_rep Q).symm,
      (Projectivization.mk_rep R).symm, hpositive⟩

private theorem realProjectiveChartCoordinate_sub_eq
    (t : ℝ) (P Q : RealProjectiveOnePoint)
    (hP : P.rep 1 - t * P.rep 0 ≠ 0)
    (hQ : Q.rep 1 - t * Q.rep 0 ≠ 0) :
    realProjectiveChartCoordinate t P -
        realProjectiveChartCoordinate t Q =
      realProjectiveBracket P.rep Q.rep /
        ((P.rep 1 - t * P.rep 0) *
          (Q.rep 1 - t * Q.rep 0)) := by
  apply (eq_div_iff (mul_ne_zero hP hQ)).2
  unfold realProjectiveChartCoordinate
  rw [sub_mul,
    div_mul_pair_cancel_left _ _ _ hP,
    div_mul_pair_cancel_right _ _ _ hQ]
  unfold realProjectiveBracket
  ring

private theorem square_three_mul_pairwise_div
    (a b c x y z : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) :
    (a * b * c) ^ 2 *
        ((x / (a * b)) * (y / (b * c)) * (z / (c * a))) =
      x * y * z := by
  field_simp [ha, hb, hc]

private theorem realProjectiveTripleBracket_chart
    (t : ℝ) (P Q R : RealProjectiveOnePoint)
    (hP : P.rep 1 - t * P.rep 0 ≠ 0)
    (hQ : Q.rep 1 - t * Q.rep 0 ≠ 0)
    (hR : R.rep 1 - t * R.rep 0 ≠ 0) :
    realProjectiveTripleBracket P.rep Q.rep R.rep =
      ((P.rep 1 - t * P.rep 0) *
        (Q.rep 1 - t * Q.rep 0) *
        (R.rep 1 - t * R.rep 0)) ^ 2 *
      ((realProjectiveChartCoordinate t P -
          realProjectiveChartCoordinate t Q) *
        (realProjectiveChartCoordinate t Q -
          realProjectiveChartCoordinate t R) *
        (realProjectiveChartCoordinate t R -
          realProjectiveChartCoordinate t P)) := by
  unfold realProjectiveTripleBracket
  rw [realProjectiveChartCoordinate_sub_eq t P Q hP hQ,
    realProjectiveChartCoordinate_sub_eq t Q R hQ hR,
    realProjectiveChartCoordinate_sub_eq t R P hR hP]
  symm
  exact square_three_mul_pairwise_div
    (P.rep 1 - t * P.rep 0)
    (Q.rep 1 - t * Q.rep 0)
    (R.rep 1 - t * R.rep 0)
    (realProjectiveBracket P.rep Q.rep)
    (realProjectiveBracket Q.rep R.rep)
    (realProjectiveBracket R.rep P.rep) hP hQ hR

private theorem sub_mul_sub_mul_sub_pos_iff_cyclic
    (a b c : ℝ) :
    0 < (a - b) * (b - c) * (c - a) ↔
      (a < b ∧ b < c) ∨ (b < c ∧ c < a) ∨ (c < a ∧ a < b) := by
  constructor
  · intro hprod
    rcases (mul_pos_iff.mp hprod) with ⟨habc, hca⟩ | ⟨habc, hca⟩
    · rcases (mul_pos_iff.mp habc) with ⟨hab, hbc⟩ | ⟨hab, hbc⟩
      · have hba : b < a := sub_pos.mp hab
        have hcb : c < b := sub_pos.mp hbc
        have hac : a < c := sub_pos.mp hca
        exact (lt_irrefl a (lt_trans hac (lt_trans hcb hba))).elim
      · exact Or.inl ⟨sub_neg.mp hab, sub_neg.mp hbc⟩
    · have hca' : c < a := sub_neg.mp hca
      rcases (mul_neg_iff.mp habc) with ⟨hab, hbc⟩ | ⟨hab, hbc⟩
      · exact Or.inr (Or.inl ⟨sub_neg.mp hbc, hca'⟩)
      · exact Or.inr (Or.inr ⟨hca', sub_neg.mp hab⟩)
  · rintro (h | h | h)
    · exact mul_pos
        (mul_pos_of_neg_of_neg (sub_neg.mpr h.1) (sub_neg.mpr h.2))
        (sub_pos.mpr (lt_trans h.1 h.2))
    · exact mul_pos_of_neg_of_neg
        (mul_neg_of_pos_of_neg
          (sub_pos.mpr (lt_trans h.1 h.2)) (sub_neg.mpr h.1))
        (sub_neg.mpr h.2)
    · exact mul_pos_of_neg_of_neg
        (mul_neg_of_neg_of_pos
          (sub_neg.mpr h.2) (sub_pos.mpr (lt_trans h.1 h.2)))
        (sub_neg.mpr h.1)

private theorem realProjectiveCyclic_iff_chart
    (t : ℝ) (P Q R : RealProjectiveOnePoint)
    (hP : P.rep 1 - t * P.rep 0 ≠ 0)
    (hQ : Q.rep 1 - t * Q.rep 0 ≠ 0)
    (hR : R.rep 1 - t * R.rep 0 ≠ 0) :
    RealProjectiveCyclic P Q R ↔
      (realProjectiveChartCoordinate t P <
          realProjectiveChartCoordinate t Q ∧
        realProjectiveChartCoordinate t Q <
          realProjectiveChartCoordinate t R) ∨
      (realProjectiveChartCoordinate t Q <
          realProjectiveChartCoordinate t R ∧
        realProjectiveChartCoordinate t R <
          realProjectiveChartCoordinate t P) ∨
      (realProjectiveChartCoordinate t R <
          realProjectiveChartCoordinate t P ∧
        realProjectiveChartCoordinate t P <
          realProjectiveChartCoordinate t Q) := by
  rw [realProjectiveCyclic_iff_rep,
    realProjectiveTripleBracket_chart t P Q R hP hQ hR]
  have hfactor : 0 < ((P.rep 1 - t * P.rep 0) *
      (Q.rep 1 - t * Q.rep 0) *
      (R.rep 1 - t * R.rep 0)) ^ 2 :=
    sq_pos_of_ne_zero (mul_ne_zero (mul_ne_zero hP hQ) hR)
  rw [mul_pos_iff_of_pos_left hfactor]
  exact sub_mul_sub_mul_sub_pos_iff_cyclic _ _ _

/-- The `RP¹` parameter belonging to one selected point of `gamma`. -/
noncomputable def sixConicTraceParameter
    {α : Type u} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (gamma : Erdos506.V1.DeterminedCircle cfg)
    (x : {x : α // x ∈ circleTrace cfg gamma.1}) :
    RealProjectiveOnePoint :=
  (properCircleProjectiveEquiv gamma.1).symm
    ⟨cfg x.1, mem_circleTrace.mp x.2⟩

@[simp] theorem properCircleProjectiveParam_sixConicTraceParameter
    {α : Type u} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (gamma : Erdos506.V1.DeterminedCircle cfg)
    (x : {x : α // x ∈ circleTrace cfg gamma.1}) :
    properCircleProjectiveParam gamma.1
      (sixConicTraceParameter cfg gamma x) = cfg x.1 := by
  have h := (properCircleProjectiveEquiv gamma.1).apply_symm_apply
    ⟨cfg x.1, mem_circleTrace.mp x.2⟩
  exact congrArg Subtype.val h

theorem sixConicTraceParameter_injective
    {α : Type u} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (gamma : Erdos506.V1.DeterminedCircle cfg) :
    Function.Injective (sixConicTraceParameter cfg gamma) := by
  intro x y hxy
  apply Subtype.ext
  apply cfg.injective
  rw [← properCircleProjectiveParam_sixConicTraceParameter cfg gamma x,
    ← properCircleProjectiveParam_sixConicTraceParameter cfg gamma y,
    hxy]

private noncomputable def sixConicChartForbidden
    {α : Type u} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (gamma : Erdos506.V1.DeterminedCircle cfg) : Finset ℝ := by
  classical
  exact (Finset.univ : Finset
    {x : α // x ∈ circleTrace cfg gamma.1}).image fun x =>
      let P := sixConicTraceParameter cfg gamma x
      if P.rep 0 = 0 then 0 else P.rep 1 / P.rep 0

private noncomputable def sixConicChartCut
    {α : Type u} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (gamma : Erdos506.V1.DeterminedCircle cfg) : ℝ := by
  classical
  exact if hS : (sixConicChartForbidden cfg gamma).Nonempty then
    (sixConicChartForbidden cfg gamma).max' hS + 1 else 0

private theorem sixConicChartCut_not_mem
    {α : Type u} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (gamma : Erdos506.V1.DeterminedCircle cfg) :
    sixConicChartCut cfg gamma ∉ sixConicChartForbidden cfg gamma := by
  classical
  unfold sixConicChartCut
  split_ifs with hS
  · intro hmem
    have hle := Finset.le_max' _ _ hmem
    linarith
  · intro hmem
    exact hS ⟨_, hmem⟩

private theorem sixConicTraceParameter_chartDenominator_ne_zero
    {α : Type u} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (gamma : Erdos506.V1.DeterminedCircle cfg)
    (x : {x : α // x ∈ circleTrace cfg gamma.1}) :
    let P := sixConicTraceParameter cfg gamma x
    P.rep 1 - sixConicChartCut cfg gamma * P.rep 0 ≠ 0 := by
  classical
  dsimp only
  let P := sixConicTraceParameter cfg gamma x
  by_cases hP0 : P.rep 0 = 0
  · intro hden
    have hP1 : P.rep 1 = 0 := by
      calc
        P.rep 1 = P.rep 1 - sixConicChartCut cfg gamma * P.rep 0 := by
          rw [hP0, mul_zero, sub_zero]
        _ = 0 := hden
    apply P.rep_nonzero
    funext i
    fin_cases i
    · exact hP0
    · exact hP1
  · intro hden
    have hcut : sixConicChartCut cfg gamma = P.rep 1 / P.rep 0 := by
      field_simp [hP0]
      linarith
    apply sixConicChartCut_not_mem cfg gamma
    apply Finset.mem_image.mpr
    refine ⟨x, Finset.mem_univ x, ?_⟩
    change (if P.rep 0 = 0 then 0 else P.rep 1 / P.rep 0) =
      sixConicChartCut cfg gamma
    rw [if_neg hP0, ← hcut]

private noncomputable def sixConicTraceChartCoordinate
    {α : Type u} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (gamma : Erdos506.V1.DeterminedCircle cfg)
    (x : {x : α // x ∈ circleTrace cfg gamma.1}) : ℝ :=
  realProjectiveChartCoordinate (sixConicChartCut cfg gamma)
    (sixConicTraceParameter cfg gamma x)

private theorem sixConicTraceChartCoordinate_injective
    {α : Type u} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (gamma : Erdos506.V1.DeterminedCircle cfg) :
    Function.Injective (sixConicTraceChartCoordinate cfg gamma) := by
  intro x y hxy
  apply sixConicTraceParameter_injective cfg gamma
  apply realProjective_eq_of_chartCoordinate_eq
    (sixConicChartCut cfg gamma)
    (sixConicTraceParameter_chartDenominator_ne_zero cfg gamma x)
    (sixConicTraceParameter_chartDenominator_ne_zero cfg gamma y)
  exact hxy

/-- The six trace labels, sorted in one affine chart of `RP¹`.  Cutting away
from all six parameters makes this a cyclic enumeration as proved below. -/
noncomputable def sixConicCyclicLabel
    {α : Type u} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (gamma : Erdos506.V1.DeterminedCircle cfg)
    (hgamma : (circleTrace cfg gamma.1).card = 6) :
    Fin 6 ≃ {x : α // x ∈ circleTrace cfg gamma.1} := by
  classical
  let T := {x : α // x ∈ circleTrace cfg gamma.1}
  letI : LinearOrder T := LinearOrder.lift'
    (sixConicTraceChartCoordinate cfg gamma)
    (sixConicTraceChartCoordinate_injective cfg gamma)
  have hcard : Fintype.card T = 6 := by
    change Fintype.card
      {x : α // x ∈ circleTrace cfg gamma.1} = 6
    simpa only [Fintype.card_coe] using hgamma
  exact (Fintype.orderIsoFinOfCardEq T hcard).toEquiv

private theorem sixConicCyclicLabel_coordinate_lt_iff
    {α : Type u} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (gamma : Erdos506.V1.DeterminedCircle cfg)
    (hgamma : (circleTrace cfg gamma.1).card = 6)
    (i j : Fin 6) :
    sixConicTraceChartCoordinate cfg gamma
        (sixConicCyclicLabel cfg gamma hgamma i) <
      sixConicTraceChartCoordinate cfg gamma
        (sixConicCyclicLabel cfg gamma hgamma j) ↔ i < j := by
  classical
  let T := {x : α // x ∈ circleTrace cfg gamma.1}
  letI : LinearOrder T := LinearOrder.lift'
    (sixConicTraceChartCoordinate cfg gamma)
    (sixConicTraceChartCoordinate_injective cfg gamma)
  have hcard : Fintype.card T = 6 := by
    change Fintype.card
      {x : α // x ∈ circleTrace cfg gamma.1} = 6
    simpa only [Fintype.card_coe] using hgamma
  change ((Fintype.orderIsoFinOfCardEq T hcard) i : T) <
      (Fintype.orderIsoFinOfCardEq T hcard) j ↔ i < j
  exact (Fintype.orderIsoFinOfCardEq T hcard).lt_iff_lt

private theorem sixConicCyclicLabel_parameter_sbtw_iff
    {α : Type u} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (gamma : Erdos506.V1.DeterminedCircle cfg)
    (hgamma : (circleTrace cfg gamma.1).card = 6)
    (i j k : Fin 6) :
    RealProjectiveCyclic
      (sixConicTraceParameter cfg gamma
        (sixConicCyclicLabel cfg gamma hgamma i))
      (sixConicTraceParameter cfg gamma
        (sixConicCyclicLabel cfg gamma hgamma j))
      (sixConicTraceParameter cfg gamma
        (sixConicCyclicLabel cfg gamma hgamma k)) ↔
      sbtw i j k := by
  let t := sixConicChartCut cfg gamma
  rw [realProjectiveCyclic_iff_chart t]
  · change
      ((sixConicTraceChartCoordinate cfg gamma
            (sixConicCyclicLabel cfg gamma hgamma i) <
          sixConicTraceChartCoordinate cfg gamma
            (sixConicCyclicLabel cfg gamma hgamma j) ∧
        sixConicTraceChartCoordinate cfg gamma
            (sixConicCyclicLabel cfg gamma hgamma j) <
          sixConicTraceChartCoordinate cfg gamma
            (sixConicCyclicLabel cfg gamma hgamma k)) ∨
      (sixConicTraceChartCoordinate cfg gamma
            (sixConicCyclicLabel cfg gamma hgamma j) <
          sixConicTraceChartCoordinate cfg gamma
            (sixConicCyclicLabel cfg gamma hgamma k) ∧
        sixConicTraceChartCoordinate cfg gamma
            (sixConicCyclicLabel cfg gamma hgamma k) <
          sixConicTraceChartCoordinate cfg gamma
            (sixConicCyclicLabel cfg gamma hgamma i)) ∨
      (sixConicTraceChartCoordinate cfg gamma
            (sixConicCyclicLabel cfg gamma hgamma k) <
          sixConicTraceChartCoordinate cfg gamma
            (sixConicCyclicLabel cfg gamma hgamma i) ∧
        sixConicTraceChartCoordinate cfg gamma
            (sixConicCyclicLabel cfg gamma hgamma i) <
          sixConicTraceChartCoordinate cfg gamma
            (sixConicCyclicLabel cfg gamma hgamma j))) ↔ sbtw i j k
    rw [sixConicCyclicLabel_coordinate_lt_iff cfg gamma hgamma i j,
      sixConicCyclicLabel_coordinate_lt_iff cfg gamma hgamma j k,
      sixConicCyclicLabel_coordinate_lt_iff cfg gamma hgamma k i]
    exact Fin.sbtw_iff.symm
  · exact sixConicTraceParameter_chartDenominator_ne_zero cfg gamma _
  · exact sixConicTraceParameter_chartDenominator_ne_zero cfg gamma _
  · exact sixConicTraceParameter_chartDenominator_ne_zero cfg gamma _

/-! ## The finite dihedral classifier -/

private def finSixSuccTable : Fin 6 → Fin 6 :=
  ![1, 2, 3, 4, 5, 0]

private def finSixPredTable : Fin 6 → Fin 6 :=
  ![5, 0, 1, 2, 3, 4]

@[simp] private theorem finRotate_six_eq_succTable
    (i : Fin 6) : finRotate 6 i = finSixSuccTable i := by
  revert i
  decide

@[simp] private theorem finRotate_six_symm_eq_predTable
    (i : Fin 6) : (finRotate 6).symm i = finSixPredTable i := by
  revert i
  decide

private def sixCycleDihedralPartner
    (code : SixCycleInvolutionCode) : Fin 6 → Fin 6 :=
  ![![3, 4, 5, 0, 1, 2],
    ![1, 0, 5, 4, 3, 2],
    ![3, 2, 1, 0, 5, 4],
    ![5, 4, 3, 2, 1, 0]] code

private theorem finSix_adjacent_iff
    (i j : Fin 6) :
    (i ≠ j ∧ ∀ k : Fin 6, ¬sbtw i k j) ↔
      j = finRotate 6 i := by
  rw [finRotate_six_eq_succTable]
  simp only [Fin.sbtw_iff]
  fin_cases i <;> fin_cases j <;> decide

private theorem finSix_commuting_fpf_involution_eq_R3
    (τ : Equiv.Perm (Fin 6))
    (hinvolution : ∀ i, τ (τ i) = i)
    (hfixedPointFree : ∀ i, τ i ≠ i)
    (hcommute : Function.Commute τ (finRotate 6)) :
    ∀ i, τ i = sixCycleDihedralPartner 0 i := by
  have h0 := hcommute 0
  have h1 := hcommute 1
  have h2 := hcommute 2
  have h3 := hcommute 3
  have h4 := hcommute 4
  have h5 := hcommute 5
  have hi0 := hinvolution 0
  have hi1 := hinvolution 1
  have hi2 := hinvolution 2
  have hi3 := hinvolution 3
  have hi4 := hinvolution 4
  have hi5 := hinvolution 5
  have hf0 := hfixedPointFree 0
  have hf1 := hfixedPointFree 1
  have hf2 := hfixedPointFree 2
  have hf3 := hfixedPointFree 3
  have hf4 := hfixedPointFree 4
  have hf5 := hfixedPointFree 5
  clear hcommute hinvolution hfixedPointFree
  generalize hτ0 : τ 0 = a
  fin_cases a <;>
    intro i <;> fin_cases i <;>
    simp_all [sixCycleDihedralPartner]

private theorem finSix_reversing_fpf_involution_classification
    (τ : Equiv.Perm (Fin 6))
    (hfixedPointFree : ∀ i, τ i ≠ i)
    (hsemiconj : Function.Semiconj τ (finRotate 6)
      (finRotate 6).symm) :
    ∃ code : SixCycleInvolutionCode,
      ∀ i, τ i = sixCycleDihedralPartner code i := by
  have h0 := hsemiconj 0
  have h1 := hsemiconj 1
  have h2 := hsemiconj 2
  have h3 := hsemiconj 3
  have h4 := hsemiconj 4
  have hf0 := hfixedPointFree 0
  have hf1 := hfixedPointFree 1
  have hf2 := hfixedPointFree 2
  clear hsemiconj hfixedPointFree
  generalize hτ0 : τ 0 = a
  have hτ1 : τ 1 = a - 1 := by
    simpa [hτ0, finSixSuccTable] using h0
  have hτ2 : τ 2 = (a - 1) - 1 := by
    simpa [hτ1, finSixSuccTable] using h1
  have hτ3 : τ 3 = ((a - 1) - 1) - 1 := by
    simpa [hτ2, finSixSuccTable] using h2
  have hτ4 : τ 4 = (((a - 1) - 1) - 1) - 1 := by
    simpa [hτ3, finSixSuccTable] using h3
  have hτ5 : τ 5 = ((((a - 1) - 1) - 1) - 1) - 1 := by
    simpa [hτ4, finSixSuccTable] using h4
  fin_cases a
  · exact (hf0 hτ0).elim
  · refine ⟨1, ?_⟩
    intro i
    fin_cases i
    · simpa [sixCycleDihedralPartner] using hτ0
    · simpa [sixCycleDihedralPartner] using hτ1
    · simpa [sixCycleDihedralPartner] using hτ2
    · simpa [sixCycleDihedralPartner] using hτ3
    · simpa [sixCycleDihedralPartner] using hτ4
    · simpa [sixCycleDihedralPartner] using hτ5
  · have hfix : τ 1 = 1 := by
      simpa using hτ1
    exact (hf1 hfix).elim
  · refine ⟨2, ?_⟩
    intro i
    fin_cases i
    · simpa [sixCycleDihedralPartner] using hτ0
    · simpa [sixCycleDihedralPartner] using hτ1
    · simpa [sixCycleDihedralPartner] using hτ2
    · simpa [sixCycleDihedralPartner] using hτ3
    · simpa [sixCycleDihedralPartner] using hτ4
    · simpa [sixCycleDihedralPartner] using hτ5
  · have hfix : τ 2 = 2 := by
      simpa using hτ2
    exact (hf2 hfix).elim
  · refine ⟨3, ?_⟩
    intro i
    fin_cases i
    · simpa [sixCycleDihedralPartner] using hτ0
    · simpa [sixCycleDihedralPartner] using hτ1
    · simpa [sixCycleDihedralPartner] using hτ2
    · simpa [sixCycleDihedralPartner] using hτ3
    · simpa [sixCycleDihedralPartner] using hτ4
    · simpa [sixCycleDihedralPartner] using hτ5

private theorem finSix_dihedral_classification
    (τ : Equiv.Perm (Fin 6))
    (hinvolution : ∀ i, τ (τ i) = i)
    (hfixedPointFree : ∀ i, τ i ≠ i)
    (horientation :
      (∀ i j k, sbtw i j k → sbtw (τ i) (τ j) (τ k)) ∨
      (∀ i j k, sbtw i j k → sbtw (τ i) (τ k) (τ j))) :
    ∃ code : SixCycleInvolutionCode,
      ∀ i, τ i = sixCycleDihedralPartner code i := by
  rcases horientation with hpreserve | hreverse
  · have hreflect : ∀ i j k, sbtw (τ i) (τ j) (τ k) → sbtw i j k := by
      intro i j k h
      simpa only [hinvolution] using hpreserve (τ i) (τ j) (τ k) h
    have hcommute : Function.Commute τ (finRotate 6) := by
      intro i
      apply (finSix_adjacent_iff (τ i) (τ (finRotate 6 i))).1
      refine ⟨τ.injective.ne ?_, ?_⟩
      · exact (finSix_adjacent_iff i (finRotate 6 i)).2 rfl |>.1
      · intro k hk
        obtain ⟨l, rfl⟩ := τ.surjective k
        exact ((finSix_adjacent_iff i (finRotate 6 i)).2 rfl).2 l
          (hreflect i l (finRotate 6 i) hk)
    exact ⟨0, finSix_commuting_fpf_involution_eq_R3
      τ hinvolution hfixedPointFree hcommute⟩
  · have hreflect : ∀ i j k, sbtw (τ i) (τ k) (τ j) → sbtw i j k := by
      intro i j k h
      have h' := hreverse (τ i) (τ k) (τ j) h
      simpa only [hinvolution] using h'
    have hreverseSucc : ∀ i,
        τ i = finRotate 6 (τ (finRotate 6 i)) := by
      intro i
      apply (finSix_adjacent_iff
        (τ (finRotate 6 i)) (τ i)).1
      refine ⟨τ.injective.ne ?_, ?_⟩
      · exact (((finSix_adjacent_iff i (finRotate 6 i)).2 rfl).1).symm
      · intro k hk
        obtain ⟨l, rfl⟩ := τ.surjective k
        exact ((finSix_adjacent_iff i (finRotate 6 i)).2 rfl).2 l
          (hreflect i l (finRotate 6 i) hk.cyclic_right)
    have hsemiconj : Function.Semiconj τ (finRotate 6)
        (finRotate 6).symm := by
      intro i
      apply (finRotate 6).injective
      simpa only [Equiv.apply_symm_apply] using (hreverseSucc i).symm
    exact finSix_reversing_fpf_involution_classification
      τ hfixedPointFree hsemiconj

private theorem sixCycleDihedralMatching_eq_partnerImage
    (code : SixCycleInvolutionCode) :
    sixCycleDihedralMatching code =
      (Finset.univ : Finset (Fin 6)).image fun i =>
        {i, sixCycleDihedralPartner code i} := by
  fin_cases code <;> decide

/-! ## Partners in a perfect matching -/

private theorem perfectMatching_existsUnique_partner
    {α : Type*} [DecidableEq α]
    {vertices : Finset α} {matching : Finset (Finset α)}
    (hm : SixConicPerfectMatchingOn vertices matching)
    (x : ↥vertices) :
    ∃! y : ↥vertices,
      y.1 ≠ x.1 ∧ {x.1, y.1} ∈ matching := by
  have hxUnion : x.1 ∈ matching.biUnion id := by
    rw [hm.covers]
    exact x.2
  obtain ⟨p, hpMatching, hxp⟩ := Finset.mem_biUnion.mp hxUnion
  obtain ⟨a, b, hab, hp⟩ := Finset.card_eq_two.mp
    (hm.pair p hpMatching).1
  have hxCases : x.1 = a ∨ x.1 = b := by
    simpa [hp] using hxp
  let y : α := if x.1 = a then b else a
  have hyPair : y ∈ p := by
    rcases hxCases with hxa | hxb
    · simp [y, hxa, hp]
    · have hxa : x.1 ≠ a := by
        intro h
        exact hab (h.symm.trans hxb)
      simp [y, hxa, hp]
  have hyVertices : y ∈ vertices := (hm.pair p hpMatching).2 hyPair
  have hxy : y ≠ x.1 := by
    rcases hxCases with hxa | hxb
    · dsimp only [y]
      rw [if_pos hxa, hxa]
      exact Ne.symm hab
    · have hxa : x.1 ≠ a := by
        intro h
        exact hab (h.symm.trans hxb)
      dsimp only [y]
      rw [if_neg hxa, hxb]
      exact hab
  have hpPair : p = {x.1, y} := by
    rw [hp]
    rcases hxCases with hxa | hxb
    · simp [y, hxa]
    · have hxa : x.1 ≠ a := by
        intro h
        exact hab (h.symm.trans hxb)
      rw [hxb]
      simp [y, hxa, Finset.pair_comm]
  refine ⟨⟨y, hyVertices⟩, ⟨hxy, hpPair ▸ hpMatching⟩, ?_⟩
  intro z hz
  apply Subtype.ext
  by_contra hyz
  have hpairsNe : ({x.1, y} : Finset α) ≠
      ({x.1, z.1} : Finset α) := by
    intro hpairs
    have hyMem : y ∈ ({x.1, z.1} : Finset α) := by
      rw [← hpairs]
      simp
    have hyVal : y = z.1 := by
      rcases Finset.mem_insert.mp hyMem with hyx | hyz'
      · exact (hxy hyx).elim
      · simpa only [Finset.mem_singleton] using hyz'
    exact hyz hyVal.symm
  have hdisjoint := hm.pairwiseDisjoint
    (hpPair ▸ hpMatching) hz.2 hpairsNe
  have hxLeft : x.1 ∈ ({x.1, y} : Finset α) :=
    Finset.mem_insert_self _ _
  have hxRight : x.1 ∈ ({x.1, z.1} : Finset α) :=
    Finset.mem_insert_self _ _
  exact (Finset.disjoint_left.mp hdisjoint) hxLeft hxRight

private noncomputable def perfectMatchingPartner
    {α : Type*} [DecidableEq α]
    {vertices : Finset α} {matching : Finset (Finset α)}
    (hm : SixConicPerfectMatchingOn vertices matching)
    (x : ↥vertices) : ↥vertices :=
  Classical.choose (perfectMatching_existsUnique_partner hm x)

private theorem perfectMatchingPartner_spec
    {α : Type*} [DecidableEq α]
    {vertices : Finset α} {matching : Finset (Finset α)}
    (hm : SixConicPerfectMatchingOn vertices matching)
    (x : ↥vertices) :
    (perfectMatchingPartner hm x).1 ≠ x.1 ∧
      {x.1, (perfectMatchingPartner hm x).1} ∈ matching :=
  (Classical.choose_spec (perfectMatching_existsUnique_partner hm x)).1

private theorem perfectMatchingPartner_involutive
    {α : Type*} [DecidableEq α]
    {vertices : Finset α} {matching : Finset (Finset α)}
    (hm : SixConicPerfectMatchingOn vertices matching)
    (x : ↥vertices) :
    perfectMatchingPartner hm (perfectMatchingPartner hm x) = x := by
  symm
  apply (Classical.choose_spec
    (perfectMatching_existsUnique_partner hm
      (perfectMatchingPartner hm x))).2
  refine ⟨(perfectMatchingPartner_spec hm x).1.symm, ?_⟩
  simpa [Finset.pair_comm] using (perfectMatchingPartner_spec hm x).2

private noncomputable def perfectMatchingLabelPerm
    {α : Type*} [DecidableEq α]
    {vertices : Finset α} {matching : Finset (Finset α)}
    (hm : SixConicPerfectMatchingOn vertices matching)
    (label : Fin 6 ≃ ↥vertices) : Equiv.Perm (Fin 6) where
  toFun i := label.symm (perfectMatchingPartner hm (label i))
  invFun i := label.symm (perfectMatchingPartner hm (label i))
  left_inv i := by
    apply label.injective
    simp only [Equiv.apply_symm_apply]
    exact perfectMatchingPartner_involutive hm (label i)
  right_inv i := by
    apply label.injective
    simp only [Equiv.apply_symm_apply]
    exact perfectMatchingPartner_involutive hm (label i)

private theorem perfectMatchingLabelPerm_partner
    {α : Type*} [DecidableEq α]
    {vertices : Finset α} {matching : Finset (Finset α)}
    (hm : SixConicPerfectMatchingOn vertices matching)
    (label : Fin 6 ≃ ↥vertices) (i : Fin 6) :
    label (perfectMatchingLabelPerm hm label i) =
      perfectMatchingPartner hm (label i) := by
  exact label.apply_symm_apply _

private theorem perfectMatching_eq_partner_image
    {α : Type*} [DecidableEq α]
    {vertices : Finset α} {matching : Finset (Finset α)}
    (hm : SixConicPerfectMatchingOn vertices matching) :
    matching = (Finset.univ : Finset ↥vertices).image fun x =>
      {x.1, (perfectMatchingPartner hm x).1} := by
  ext p
  constructor
  · intro hp
    have hpCard := (hm.pair p hp).1
    have hpNonempty : p.Nonempty := Finset.card_pos.mp (by omega)
    obtain ⟨x, hx⟩ := hpNonempty
    let xs : ↥vertices := ⟨x, (hm.pair p hp).2 hx⟩
    have hpartner := (perfectMatchingPartner_spec hm xs).2
    have heq : p = {xs.1, (perfectMatchingPartner hm xs).1} := by
      by_contra hne
      have hdisjoint := hm.pairwiseDisjoint hp hpartner hne
      exact Finset.disjoint_left.mp hdisjoint hx (by simp [xs])
    apply Finset.mem_image.mpr
    exact ⟨xs, Finset.mem_univ xs, heq.symm⟩
  · intro hp
    obtain ⟨x, _hx, rfl⟩ := Finset.mem_image.mp hp
    exact (perfectMatchingPartner_spec hm x).2

private theorem perfectMatching_eq_relabel_of_dihedralPerm
    {α : Type*} [DecidableEq α]
    {vertices : Finset α} {matching : Finset (Finset α)}
    (hm : SixConicPerfectMatchingOn vertices matching)
    (label : Fin 6 ≃ ↥vertices)
    (code : SixCycleInvolutionCode)
    (hcode : ∀ i, perfectMatchingLabelPerm hm label i =
      sixCycleDihedralPartner code i) :
    matching = relabelSixCycleMatching
      (fun i => (label i).1) code := by
  rw [perfectMatching_eq_partner_image hm,
    relabelSixCycleMatching, sixCycleDihedralMatching_eq_partnerImage]
  simp only [Finset.image_image]
  ext p
  simp only [Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨x, rfl⟩
    obtain ⟨i, rfl⟩ := label.surjective x
    refine ⟨i, ?_⟩
    rw [← perfectMatchingLabelPerm_partner hm label i, hcode i]
    simp
  · rintro ⟨i, rfl⟩
    refine ⟨label i, ?_⟩
    rw [← perfectMatchingLabelPerm_partner hm label i, hcode i]
    simp

/-! ## Projective centres off a proper circle -/

theorem properCircle_projectivePoint_not_on_chord
    (c : ProperCircle) {p q r : Point2}
    (hp : p ∈ (c.1 : Set Point2))
    (hq : q ∈ (c.1 : Set Point2))
    (hr : r ∈ (c.1 : Set Point2))
    (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r) :
    ¬Projectivization.orthogonal (projectivePoint r)
      (projectiveLine p q hpq) := by
  rw [projectivePoint_orthogonal_projectiveLine_iff_det_eq_zero]
  exact homogeneousLift_det_ne_zero_of_mem_properCircle
    c hp hq hr hpq hpr hqr

/-- A real projective point on the homogeneous completion of a proper
circle is necessarily affine. -/
private theorem properCirclePencilDeterminant_zero_gives_affine_point
    (c : ProperCircle) (O : RealProjectivePlane)
    (hzero : properCirclePencilDeterminant c O.rep = 0) :
    ∃ z : Point2, z ∈ (c.1 : Set Point2) ∧ O = projectivePoint z := by
  have hO2 : O.rep 2 ≠ 0 := by
    intro hO2
    have h := hzero
    rw [properCirclePencilDeterminant_eq] at h
    rw [hO2] at h
    norm_num at h
    have hO0 : O.rep 0 = 0 := by nlinarith [sq_nonneg (O.rep 0)]
    have hO1 : O.rep 1 = 0 := by nlinarith [sq_nonneg (O.rep 1)]
    apply O.rep_nonzero
    funext i
    fin_cases i
    · exact hO0
    · exact hO1
    · exact hO2
  let z : Point2 := Erdos506.V3.pointOfCoords (O.rep 0 / O.rep 2)
    (O.rep 1 / O.rep 2)
  have hz : z ∈ (c.1 : Set Point2) := by
    apply (Erdos506.V3.mem_properCircle_iff_equation c z).2
    have h := hzero
    rw [properCirclePencilDeterminant_eq] at h
    simp only [Erdos506.V3.circleEquation,
      Erdos506.V3.properCircleEquationA,
      Erdos506.V3.properCircleEquationB,
      Erdos506.V3.properCircleEquationC,
      z, Erdos506.V3.pointOfCoords_apply_zero,
      Erdos506.V3.pointOfCoords_apply_one]
    field_simp [hO2]
    nlinarith [h]
  refine ⟨z, hz, ?_⟩
  calc
    O = Projectivization.mk ℝ O.rep O.rep_nonzero :=
      (Projectivization.mk_rep O).symm
    _ = Projectivization.mk ℝ (homogeneousLift z)
        (homogeneousLift_ne_zero z) := by
      apply (Projectivization.mk_eq_mk_iff' ℝ O.rep
        (homogeneousLift z) O.rep_nonzero
        (homogeneousLift_ne_zero z)).2
      refine ⟨O.rep 2, ?_⟩
      apply homogeneous3_eq_of_apply_zero_one_two
      · simp only [Pi.smul_apply, smul_eq_mul, homogeneousLift_zero,
          z, Erdos506.V3.pointOfCoords_apply_zero]
        field_simp [hO2]
      · simp only [Pi.smul_apply, smul_eq_mul, homogeneousLift_one,
          z, Erdos506.V3.pointOfCoords_apply_one]
        field_simp [hO2]
      · simp only [Pi.smul_apply, smul_eq_mul, homogeneousLift_two, mul_one]
    _ = projectivePoint z := rfl

/-- The intersection of two disjoint real chords of a proper circle is not
on the projective completion of that circle. -/
private theorem properCirclePencilDeterminant_ne_zero_of_two_chords
    (c : ProperCircle) (O : RealProjectivePlane)
    {p q r s : Point2}
    (hp : p ∈ (c.1 : Set Point2))
    (hq : q ∈ (c.1 : Set Point2))
    (hr : r ∈ (c.1 : Set Point2))
    (hs : s ∈ (c.1 : Set Point2))
    (hpq : p ≠ q) (hrs : r ≠ s)
    (hpr : p ≠ r) (hps : p ≠ s)
    (hqr : q ≠ r) (hqs : q ≠ s)
    (hO₀ : Projectivization.orthogonal O
      (projectiveLine p q hpq))
    (hO₁ : Projectivization.orthogonal O
      (projectiveLine r s hrs)) :
    properCirclePencilDeterminant c O.rep ≠ 0 := by
  intro hzero
  obtain ⟨z, hz, hOz⟩ :=
    properCirclePencilDeterminant_zero_gives_affine_point c O hzero
  have hzp : z ≠ p := by
    intro hzp
    subst z
    exact properCircle_projectivePoint_not_on_chord c hr hs hp
      hrs hpr.symm hps.symm (hOz ▸ hO₁)
  have hzq : z ≠ q := by
    intro hzq
    subst z
    exact properCircle_projectivePoint_not_on_chord c hr hs hq
      hrs hqr.symm hqs.symm (hOz ▸ hO₁)
  exact properCircle_projectivePoint_not_on_chord c hp hq hz
    hpq hzp.symm hzq.symm (hOz ▸ hO₀)

private theorem properCircleVeronesePoint_eq_mk_rep
    (c : ProperCircle) (P : RealProjectiveOnePoint) :
    properCircleVeronesePoint c P =
      Projectivization.mk ℝ
        (properCircleVeroneseVector c P.rep)
        (properCircleVeroneseVector_ne_zero c P.rep_nonzero) := by
  conv_lhs => rw [← Projectivization.mk_rep P]
  exact properCircleVeronesePoint_mk c P.rep P.rep_nonzero

private theorem properCircleVeronese_det_eq_zero_of_incident_chord
    (c : ProperCircle) {P Q : RealProjectiveOnePoint} (hPQ : P ≠ Q)
    (O : RealProjectivePlane)
    (hO : Projectivization.orthogonal O
      (properCircleParamChord c hPQ)) :
    Matrix.det ![properCircleVeroneseVector c P.rep,
      properCircleVeroneseVector c Q.rep, O.rep] = 0 := by
  let p := properCircleVeroneseVector c P.rep
  let q := properCircleVeroneseVector c Q.rep
  have hp : p ≠ 0 := properCircleVeroneseVector_ne_zero c P.rep_nonzero
  have hq : q ≠ 0 := properCircleVeroneseVector_ne_zero c Q.rep_nonzero
  have hpq : Projectivization.mk ℝ p hp ≠
      Projectivization.mk ℝ q hq := by
    intro heq
    apply hPQ
    apply properCircleProjectiveParam_injective c
    apply projectivePoint_injective
    rw [← properCircleVeronesePoint_eq_projectivePoint c P,
      ← properCircleVeronesePoint_eq_projectivePoint c Q,
      properCircleVeronesePoint_eq_mk_rep,
      properCircleVeronesePoint_eq_mk_rep]
    exact heq
  have hcross : crossProduct p q ≠ 0 :=
    mt (Projectivization.mk_eq_mk_iff_crossProduct_eq_zero hp hq).2 hpq
  have hprojective : Projectivization.orthogonal
      (Projectivization.mk ℝ O.rep O.rep_nonzero)
      (Projectivization.cross
        (Projectivization.mk ℝ p hp)
        (Projectivization.mk ℝ q hq)) := by
    rw [Projectivization.mk_rep]
    rw [← properCircleVeronesePoint_eq_mk_rep c P,
      ← properCircleVeronesePoint_eq_mk_rep c Q,
      ← properCircleParamChord_eq_cross c hPQ]
    exact hO
  rw [Projectivization.cross_mk_of_cross_ne_zero hp hq hcross,
    Projectivization.orthogonal_mk O.rep_nonzero hcross] at hprojective
  change Matrix.det ![p, q, O.rep] = 0
  calc
    Matrix.det ![p, q, O.rep] =
        O.rep ⬝ᵥ crossProduct p q := by
      rw [triple_product_permutation O.rep p q,
        triple_product_eq_det]
    _ = 0 := hprojective

/-- Incidence with a nondegenerate chord pencil identifies the other
endpoint with the residual projective image. -/
private theorem properCirclePencil_pairs_affine_chord
    (c : ProperCircle) (O : RealProjectivePlane)
    (hnondegenerate : properCirclePencilDeterminant c O.rep ≠ 0)
    {p q : Point2}
    (hp : p ∈ (c.1 : Set Point2))
    (hq : q ∈ (c.1 : Set Point2)) (hpq : p ≠ q)
    (hO : Projectivization.orthogonal O
      (projectiveLine p q hpq)) :
    let P := (properCircleProjectiveEquiv c).symm ⟨p, hp⟩
    let Q := (properCircleProjectiveEquiv c).symm ⟨q, hq⟩
    Q = properCirclePencilGL c O.rep hnondegenerate • P := by
  dsimp only
  let P := (properCircleProjectiveEquiv c).symm ⟨p, hp⟩
  let Q := (properCircleProjectiveEquiv c).symm ⟨q, hq⟩
  have hPpoint : properCircleProjectiveParam c P = p := by
    exact congrArg Subtype.val
      ((properCircleProjectiveEquiv c).apply_symm_apply ⟨p, hp⟩)
  have hQpoint : properCircleProjectiveParam c Q = q := by
    exact congrArg Subtype.val
      ((properCircleProjectiveEquiv c).apply_symm_apply ⟨q, hq⟩)
  have hPQ : P ≠ Q := by
    intro h
    apply hpq
    rw [← hPpoint, ← hQpoint, h]
  have hOChord : Projectivization.orthogonal O
      (properCircleParamChord c hPQ) := by
    simpa [properCircleParamChord, hPpoint, hQpoint] using hO
  have hdet := properCircleVeronese_det_eq_zero_of_incident_chord
    c hPQ O hOChord
  have hbracket : realProjectiveBracket P.rep Q.rep ≠ 0 := by
    intro hzero
    apply hPQ
    calc
      P = Projectivization.mk ℝ P.rep P.rep_nonzero :=
        (Projectivization.mk_rep P).symm
      _ = Projectivization.mk ℝ Q.rep Q.rep_nonzero :=
        (realProjective_mk_eq_mk_iff_bracket_eq_zero
          P.rep_nonzero Q.rep_nonzero).2 hzero
      _ = Q := Projectivization.mk_rep Q
  have hform := (properCircleVeronese_chord_det_eq_zero_iff
    c O.rep hbracket).1 hdet
  have hresidual := (properCirclePencil_residual_iff c O.rep
    hnondegenerate P.rep_nonzero Q.rep_nonzero).1 hform
  simpa only [Projectivization.mk_rep] using hresidual

/-! ## The common pencil of one full outsider edge -/

private theorem sixConicPairCircle_ne_gamma
    {α : Type u} [Fintype α] [DecidableEq α]
    {cfg : Configuration α} {gamma c : Erdos506.V1.DeterminedCircle cfg}
    {e : Finset α}
    (hgamma : (circleTrace cfg gamma.1).card = 6)
    (hc : c ∈ sixConicPairCircles cfg gamma e) :
    gamma.1 ≠ c.1 := by
  intro hcircle
  have hpair := (mem_sixConicPairCircles.mp hc).2
  rw [← hcircle, Finset.inter_self, hgamma] at hpair
  omega

private theorem sixConicPairCircle_chordLine_eq_axis
    {α : Type u} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (gamma c : Erdos506.V1.DeterminedCircle cfg)
    {e : Finset α}
    (hgamma : (circleTrace cfg gamma.1).card = 6)
    (hc : c ∈ sixConicPairCircles cfg gamma e) :
    let p : KSubset α 2 :=
      ⟨circleTrace cfg c.1 ∩ circleTrace cfg gamma.1,
        (mem_sixConicPairCircles.mp hc).2⟩
    projectiveChordLine cfg p = projectiveRadicalAxis gamma.1 c.1
      (sixConicPairCircle_ne_gamma hgamma hc) := by
  dsimp only
  apply projectiveChordLine_eq_projectiveRadicalAxis_of_endpoints
  · exact mem_circleTrace.mp
      (Finset.mem_inter.mp (chordLabel_mem _ 0)).2
  · exact mem_circleTrace.mp
      (Finset.mem_inter.mp (chordLabel_mem _ 1)).2
  · exact mem_circleTrace.mp
      (Finset.mem_inter.mp (chordLabel_mem _ 0)).1
  · exact mem_circleTrace.mp
      (Finset.mem_inter.mp (chordLabel_mem _ 1)).1

private theorem sixConicPairCircle_outsiderLine_eq_axis
    {α : Type u} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) {gamma c d : Erdos506.V1.DeterminedCircle cfg}
    {e : Finset α} (he : e.card = 2)
    (hc : c ∈ sixConicPairCircles cfg gamma e)
    (hd : d ∈ sixConicPairCircles cfg gamma e) (hcd : c ≠ d) :
    projectiveChordLine cfg (⟨e, he⟩ : KSubset α 2) =
      projectiveRadicalAxis c.1 d.1
        (determinedCircle_coe_ne_of_ne hcd) := by
  apply projectiveChordLine_eq_projectiveRadicalAxis_of_endpoints
  · exact mem_circleTrace.mp
      ((mem_sixConicPairCircles.mp hc).1 (chordLabel_mem _ 0))
  · exact mem_circleTrace.mp
      ((mem_sixConicPairCircles.mp hc).1 (chordLabel_mem _ 1))
  · exact mem_circleTrace.mp
      ((mem_sixConicPairCircles.mp hd).1 (chordLabel_mem _ 0))
  · exact mem_circleTrace.mp
      ((mem_sixConicPairCircles.mp hd).1 (chordLabel_mem _ 1))

private theorem sixConicPairCircle_axes_ne
    {α : Type u} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) {gamma c d : Erdos506.V1.DeterminedCircle cfg}
    {e : Finset α}
    (hgamma : (circleTrace cfg gamma.1).card = 6)
    (he : e.card = 2)
    (hedisjoint : Disjoint e (circleTrace cfg gamma.1))
    (hc : c ∈ sixConicPairCircles cfg gamma e)
    (hd : d ∈ sixConicPairCircles cfg gamma e) (hcd : c ≠ d) :
    projectiveRadicalAxis gamma.1 c.1
        (sixConicPairCircle_ne_gamma hgamma hc) ≠
      projectiveRadicalAxis gamma.1 d.1
        (sixConicPairCircle_ne_gamma hgamma hd) := by
  let pc : KSubset α 2 :=
    ⟨circleTrace cfg c.1 ∩ circleTrace cfg gamma.1,
      (mem_sixConicPairCircles.mp hc).2⟩
  let a := chordLabel pc 0
  have haPairC : a ∈ circleTrace cfg c.1 ∩
      circleTrace cfg gamma.1 := chordLabel_mem pc 0
  have haGamma : cfg a ∈ (gamma.1.1 : Set Point2) :=
    mem_circleTrace.mp (Finset.mem_inter.mp haPairC).2
  have haC : cfg a ∈ (c.1.1 : Set Point2) :=
    mem_circleTrace.mp (Finset.mem_inter.mp haPairC).1
  have hpairsDisjoint := sixConicPairCircle_gammaPairs_disjoint
    he hedisjoint hc hd hcd
  have haNotD : cfg a ∉ (d.1.1 : Set Point2) := by
    intro haD
    have haPairD : a ∈ circleTrace cfg d.1 ∩
        circleTrace cfg gamma.1 :=
      Finset.mem_inter.mpr ⟨mem_circleTrace.mpr haD,
        (Finset.mem_inter.mp haPairC).2⟩
    exact Finset.disjoint_left.mp hpairsDisjoint haPairC haPairD
  intro haxes
  have haOnC := projectivePoint_orthogonal_projectiveRadicalAxis_of_mem
    (sixConicPairCircle_ne_gamma hgamma hc) haGamma haC
  have haNotOnD :=
    not_projectivePoint_orthogonal_projectiveRadicalAxis_of_mem_not_mem
      (sixConicPairCircle_ne_gamma hgamma hd) haGamma haNotD
  exact haNotOnD (haxes ▸ haOnC)

private theorem sixConicPairCircle_axis_through_baseCross
    {α : Type u} [Fintype α] [DecidableEq α]
    (cfg : Configuration α)
    {gamma c₀ c₁ c : Erdos506.V1.DeterminedCircle cfg}
    {e : Finset α}
    (hgamma : (circleTrace cfg gamma.1).card = 6)
    (he : e.card = 2)
    (hedisjoint : Disjoint e (circleTrace cfg gamma.1))
    (hc₀ : c₀ ∈ sixConicPairCircles cfg gamma e)
    (hc₁ : c₁ ∈ sixConicPairCircles cfg gamma e)
    (hc : c ∈ sixConicPairCircles cfg gamma e) (hc₀₁ : c₀ ≠ c₁) :
    Projectivization.orthogonal
      (Projectivization.cross
        (projectiveRadicalAxis gamma.1 c₀.1
          (sixConicPairCircle_ne_gamma hgamma hc₀))
        (projectiveRadicalAxis gamma.1 c₁.1
          (sixConicPairCircle_ne_gamma hgamma hc₁)))
      (projectiveRadicalAxis gamma.1 c.1
        (sixConicPairCircle_ne_gamma hgamma hc)) := by
  classical
  have hL₀₁ : projectiveRadicalAxis gamma.1 c₀.1
        (sixConicPairCircle_ne_gamma hgamma hc₀) ≠
      projectiveRadicalAxis gamma.1 c₁.1
        (sixConicPairCircle_ne_gamma hgamma hc₁) :=
    sixConicPairCircle_axes_ne cfg hgamma he hedisjoint hc₀ hc₁ hc₀₁
  by_cases hcEq : c = c₀
  · subst c
    exact Projectivization.cross_orthogonal_left hL₀₁
  · have hc₀c : c₀ ≠ c := Ne.symm hcEq
    have haxisC₀ : projectiveRadicalAxis gamma.1 c.1
          (sixConicPairCircle_ne_gamma hgamma hc) ≠
        projectiveRadicalAxis gamma.1 c₀.1
          (sixConicPairCircle_ne_gamma hgamma hc₀) :=
      sixConicPairCircle_axes_ne cfg hgamma he hedisjoint hc hc₀ hcEq
    have houtsiderC := sixConicPairCircle_outsiderLine_eq_axis
      cfg he hc₀ hc hc₀c
    have houtsider₁ := sixConicPairCircle_outsiderLine_eq_axis
      cfg he hc₀ hc₁ hc₀₁
    have hpencilC := projectiveRadicalAxis_pencil_cross
      gamma.1 c₀.1 c.1
      (sixConicPairCircle_ne_gamma hgamma hc₀)
      (sixConicPairCircle_ne_gamma hgamma hc)
      (determinedCircle_coe_ne_of_ne hc₀c)
    have hpencil₁ := projectiveRadicalAxis_pencil_cross
      gamma.1 c₀.1 c₁.1
      (sixConicPairCircle_ne_gamma hgamma hc₀)
      (sixConicPairCircle_ne_gamma hgamma hc₁)
      (determinedCircle_coe_ne_of_ne hc₀₁)
    rw [← houtsiderC] at hpencilC
    rw [← houtsider₁] at hpencil₁
    have hcross : Projectivization.cross
          (projectiveRadicalAxis gamma.1 c.1
            (sixConicPairCircle_ne_gamma hgamma hc))
          (projectiveRadicalAxis gamma.1 c₀.1
            (sixConicPairCircle_ne_gamma hgamma hc₀)) =
        Projectivization.cross
          (projectiveRadicalAxis gamma.1 c₁.1
            (sixConicPairCircle_ne_gamma hgamma hc₁))
          (projectiveRadicalAxis gamma.1 c₀.1
            (sixConicPairCircle_ne_gamma hgamma hc₀)) :=
      hpencilC.trans hpencil₁.symm
    rw [Projectivization.cross_comm
      (projectiveRadicalAxis gamma.1 c₀.1
        (sixConicPairCircle_ne_gamma hgamma hc₀))
      (projectiveRadicalAxis gamma.1 c₁.1
        (sixConicPairCircle_ne_gamma hgamma hc₁)), ← hcross]
    exact Projectivization.cross_orthogonal_left haxisC₀

private theorem sixConicPairCircle_baseCross_nondegenerate
    {α : Type u} [Fintype α] [DecidableEq α]
    (cfg : Configuration α)
    {gamma c₀ c₁ : Erdos506.V1.DeterminedCircle cfg}
    {e : Finset α}
    (hgamma : (circleTrace cfg gamma.1).card = 6)
    (he : e.card = 2)
    (hedisjoint : Disjoint e (circleTrace cfg gamma.1))
    (hc₀ : c₀ ∈ sixConicPairCircles cfg gamma e)
    (hc₁ : c₁ ∈ sixConicPairCircles cfg gamma e) (hc₀₁ : c₀ ≠ c₁) :
    properCirclePencilDeterminant gamma.1
      (Projectivization.cross
        (projectiveRadicalAxis gamma.1 c₀.1
          (sixConicPairCircle_ne_gamma hgamma hc₀))
        (projectiveRadicalAxis gamma.1 c₁.1
          (sixConicPairCircle_ne_gamma hgamma hc₁))).rep ≠ 0 := by
  let p₀ : KSubset α 2 :=
    ⟨circleTrace cfg c₀.1 ∩ circleTrace cfg gamma.1,
      (mem_sixConicPairCircles.mp hc₀).2⟩
  let p₁ : KSubset α 2 :=
    ⟨circleTrace cfg c₁.1 ∩ circleTrace cfg gamma.1,
      (mem_sixConicPairCircles.mp hc₁).2⟩
  let a := chordLabel p₀ 0
  let b := chordLabel p₀ 1
  let r := chordLabel p₁ 0
  let s := chordLabel p₁ 1
  have haPair : a ∈ p₀.1 := chordLabel_mem p₀ 0
  have hbPair : b ∈ p₀.1 := chordLabel_mem p₀ 1
  have hrPair : r ∈ p₁.1 := chordLabel_mem p₁ 0
  have hsPair : s ∈ p₁.1 := chordLabel_mem p₁ 1
  have haGamma : cfg a ∈ (gamma.1.1 : Set Point2) :=
    mem_circleTrace.mp (Finset.mem_inter.mp haPair).2
  have hbGamma : cfg b ∈ (gamma.1.1 : Set Point2) :=
    mem_circleTrace.mp (Finset.mem_inter.mp hbPair).2
  have hrGamma : cfg r ∈ (gamma.1.1 : Set Point2) :=
    mem_circleTrace.mp (Finset.mem_inter.mp hrPair).2
  have hsGamma : cfg s ∈ (gamma.1.1 : Set Point2) :=
    mem_circleTrace.mp (Finset.mem_inter.mp hsPair).2
  have hab : a ≠ b := chordLabel_zero_ne_one p₀
  have hrs : r ≠ s := chordLabel_zero_ne_one p₁
  have hpairsDisjoint := sixConicPairCircle_gammaPairs_disjoint
    he hedisjoint hc₀ hc₁ hc₀₁
  have har : a ≠ r := by
    intro har
    apply Finset.disjoint_left.mp hpairsDisjoint haPair
    rw [har]
    exact hrPair
  have has : a ≠ s := by
    intro has
    apply Finset.disjoint_left.mp hpairsDisjoint haPair
    rw [has]
    exact hsPair
  have hbr : b ≠ r := by
    intro hbr
    apply Finset.disjoint_left.mp hpairsDisjoint hbPair
    rw [hbr]
    exact hrPair
  have hbs : b ≠ s := by
    intro hbs
    apply Finset.disjoint_left.mp hpairsDisjoint hbPair
    rw [hbs]
    exact hsPair
  let O : RealProjectivePlane := Projectivization.cross
    (projectiveRadicalAxis gamma.1 c₀.1
      (sixConicPairCircle_ne_gamma hgamma hc₀))
    (projectiveRadicalAxis gamma.1 c₁.1
      (sixConicPairCircle_ne_gamma hgamma hc₁))
  have hOChord₀ : Projectivization.orthogonal O
      (projectiveChordLine cfg p₀) := by
    rw [sixConicPairCircle_chordLine_eq_axis cfg gamma c₀ hgamma hc₀]
    exact sixConicPairCircle_axis_through_baseCross cfg hgamma he
      hedisjoint hc₀ hc₁ hc₀ hc₀₁
  have hOChord₁ : Projectivization.orthogonal O
      (projectiveChordLine cfg p₁) := by
    rw [sixConicPairCircle_chordLine_eq_axis cfg gamma c₁ hgamma hc₁]
    exact sixConicPairCircle_axis_through_baseCross cfg hgamma he
      hedisjoint hc₀ hc₁ hc₁ hc₀₁
  have hOline₀ : Projectivization.orthogonal O
      (projectiveLine (cfg a) (cfg b) (cfg.injective.ne hab)) := by
    rw [← projectiveChordLine_eq_projectiveLine_of_mem cfg p₀
      haPair hbPair hab]
    exact hOChord₀
  have hOline₁ : Projectivization.orthogonal O
      (projectiveLine (cfg r) (cfg s) (cfg.injective.ne hrs)) := by
    rw [← projectiveChordLine_eq_projectiveLine_of_mem cfg p₁
      hrPair hsPair hrs]
    exact hOChord₁
  change properCirclePencilDeterminant gamma.1 O.rep ≠ 0
  exact properCirclePencilDeterminant_ne_zero_of_two_chords
    gamma.1 O haGamma hbGamma hrGamma hsGamma
    (cfg.injective.ne hab) (cfg.injective.ne hrs)
    (cfg.injective.ne har) (cfg.injective.ne has)
    (cfg.injective.ne hbr) (cfg.injective.ne hbs)
    hOline₀ hOline₁

private theorem sixConicFullEdge_commonCenter
    {α : Type u} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (gamma : Erdos506.V1.DeterminedCircle cfg)
    (hgamma : (circleTrace cfg gamma.1).card = 6)
    (X : Finset α)
    (hdisjoint : Disjoint (circleTrace cfg gamma.1) X)
    {e : Finset α} (heFull : e ∈ sixConicFullEdges cfg gamma X) :
    ∃ O : RealProjectivePlane,
      (∀ c : Erdos506.V1.DeterminedCircle cfg,
        (hc : c ∈ sixConicPairCircles cfg gamma e) →
          Projectivization.orthogonal O
            (projectiveRadicalAxis gamma.1 c.1
              (sixConicPairCircle_ne_gamma hgamma hc))) ∧
      properCirclePencilDeterminant gamma.1 O.rep ≠ 0 := by
  classical
  have heSpec := mem_sixConicFullEdges.mp heFull
  have hePow := Finset.mem_powersetCard.mp heSpec.1
  have heCard : e.card = 2 := hePow.2
  have heDisjointGamma : Disjoint e (circleTrace cfg gamma.1) :=
    hdisjoint.symm.mono_left hePow.1
  let C := sixConicPairCircles cfg gamma e
  have hCcard : C.card = 3 := by
    change sixConicPairWeight cfg gamma e = 3
    exact heSpec.2
  have hCtwo : 1 < C.card := by omega
  let hexistsPair := Finset.one_lt_card_iff.mp hCtwo
  let c0 := Classical.choose hexistsPair
  let hexistsSecond := Classical.choose_spec hexistsPair
  let c1 := Classical.choose hexistsSecond
  have hpairsSpec := Classical.choose_spec hexistsSecond
  have hc0 : c0 ∈ C := hpairsSpec.1
  have hc1 : c1 ∈ C := hpairsSpec.2.1
  have hc01 : c0 ≠ c1 := hpairsSpec.2.2
  change c0 ∈ sixConicPairCircles cfg gamma e at hc0
  change c1 ∈ sixConicPairCircles cfg gamma e at hc1
  let L0 := projectiveRadicalAxis gamma.1 c0.1
    (sixConicPairCircle_ne_gamma hgamma hc0)
  let L1 := projectiveRadicalAxis gamma.1 c1.1
    (sixConicPairCircle_ne_gamma hgamma hc1)
  let O : RealProjectivePlane := Projectivization.cross L0 L1
  have hcenter : ∀ c : Erdos506.V1.DeterminedCircle cfg,
      (hc : c ∈ sixConicPairCircles cfg gamma e) →
      Projectivization.orthogonal O
        (projectiveRadicalAxis gamma.1 c.1
          (sixConicPairCircle_ne_gamma hgamma hc)) := by
    intro c hc
    dsimp only [O, L0, L1]
    exact sixConicPairCircle_axis_through_baseCross cfg hgamma heCard
      heDisjointGamma hc0 hc1 hc hc01
  have hnondegenerate :
      properCirclePencilDeterminant gamma.1 O.rep ≠ 0 := by
    dsimp only [O, L0, L1]
    exact sixConicPairCircle_baseCross_nondegenerate cfg hgamma heCard
      heDisjointGamma hc0 hc1 hc01
  exact ⟨O, hcenter, hnondegenerate⟩

/-- Concrete projective-pencil data attached to one full outsider edge. -/
private structure SixConicFullEdgePencil
    {α : Type u} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (gamma : Erdos506.V1.DeterminedCircle cfg)
    (hgamma : (circleTrace cfg gamma.1).card = 6)
    (e : Finset α) where
  edgeCard : e.card = 2
  center : RealProjectivePlane
  nondegenerate :
    properCirclePencilDeterminant gamma.1 center.rep ≠ 0
  pairAxes :
    ∀ c : Erdos506.V1.DeterminedCircle cfg,
      (hc : c ∈ sixConicPairCircles cfg gamma e) →
        Projectivization.orthogonal center
          (projectiveRadicalAxis gamma.1 c.1
            (sixConicPairCircle_ne_gamma hgamma hc))
  outsider :
    Projectivization.orthogonal center
      (projectiveChordLine cfg (⟨e, edgeCard⟩ : KSubset α 2))
  chords :
    ∀ (a b : {x : α // x ∈ circleTrace cfg gamma.1}),
      (hab : a ≠ b) → {a.1, b.1} ∈ sixConicSignature cfg gamma e →
        Projectivization.orthogonal center
          (projectiveLine (cfg a.1) (cfg b.1)
            (cfg.injective.ne (Subtype.val_injective.ne hab)))
  pairs :
    ∀ (a b : {x : α // x ∈ circleTrace cfg gamma.1}),
      a ≠ b → {a.1, b.1} ∈ sixConicSignature cfg gamma e →
        sixConicTraceParameter cfg gamma b =
          properCirclePencilGL gamma.1 center.rep nondegenerate •
            sixConicTraceParameter cfg gamma a

private noncomputable def sixConicFullEdge_pencil
    {α : Type u} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (gamma : Erdos506.V1.DeterminedCircle cfg)
    (hgamma : (circleTrace cfg gamma.1).card = 6)
    (X : Finset α)
    (hdisjoint : Disjoint (circleTrace cfg gamma.1) X)
    {e : Finset α} (heFull : e ∈ sixConicFullEdges cfg gamma X) :
    SixConicFullEdgePencil cfg gamma hgamma e := by
  classical
  let hexists :=
    sixConicFullEdge_commonCenter cfg gamma hgamma X hdisjoint heFull
  let O := Classical.choose hexists
  have hcenter := (Classical.choose_spec hexists).1
  have hnondegenerate := (Classical.choose_spec hexists).2
  have heSpec := mem_sixConicFullEdges.mp heFull
  have hePow := Finset.mem_powersetCard.mp heSpec.1
  have heCard : e.card = 2 := hePow.2
  have heDisjointGamma : Disjoint e (circleTrace cfg gamma.1) :=
    hdisjoint.symm.mono_left hePow.1
  let C := sixConicPairCircles cfg gamma e
  have hCcard : C.card = 3 := by
    change sixConicPairWeight cfg gamma e = 3
    exact heSpec.2
  have hCtwo : 1 < C.card := by omega
  let hpairs := Finset.one_lt_card_iff.mp hCtwo
  let c0 := Classical.choose hpairs
  let hseconds := Classical.choose_spec hpairs
  let c1 := Classical.choose hseconds
  have hpairsSpec := Classical.choose_spec hseconds
  have hc0 : c0 ∈ C := hpairsSpec.1
  have hc1 : c1 ∈ C := hpairsSpec.2.1
  have hc01 : c0 ≠ c1 := hpairsSpec.2.2
  change c0 ∈ sixConicPairCircles cfg gamma e at hc0
  change c1 ∈ sixConicPairCircles cfg gamma e at hc1
  let L0 := projectiveRadicalAxis gamma.1 c0.1
    (sixConicPairCircle_ne_gamma hgamma hc0)
  let L1 := projectiveRadicalAxis gamma.1 c1.1
    (sixConicPairCircle_ne_gamma hgamma hc1)
  have hL01 : L0 ≠ L1 := by
    dsimp only [L0, L1]
    exact sixConicPairCircle_axes_ne cfg hgamma heCard
      heDisjointGamma hc0 hc1 hc01
  have hOeq : O = Projectivization.cross L0 L1 := by
    exact projectiveCovector_eq_cross_of_orthogonal hL01
      (Projectivization.orthogonal_comm.mp (hcenter c0 hc0))
      (Projectivization.orthogonal_comm.mp (hcenter c1 hc1))
  let pe : KSubset α 2 := ⟨e, heCard⟩
  let x := chordLabel pe 0
  have hxE : x ∈ e := chordLabel_mem pe 0
  have hxNotGamma : x ∉ circleTrace cfg gamma.1 := by
    intro hxGamma
    exact Finset.disjoint_left.mp heDisjointGamma hxE hxGamma
  have hxNotGammaPoint : cfg x ∉ (gamma.1.1 : Set Point2) := by
    intro hxGamma
    exact hxNotGamma (mem_circleTrace.mpr hxGamma)
  have hxC0 : cfg x ∈ (c0.1.1 : Set Point2) := by
    apply mem_circleTrace.mp
    exact (mem_sixConicPairCircles.mp hc0).1 hxE
  have hOutLine : projectiveChordLine cfg pe =
      projectiveRadicalAxis c0.1 c1.1
        (determinedCircle_coe_ne_of_ne hc01) :=
    sixConicPairCircle_outsiderLine_eq_axis cfg heCard hc0 hc1 hc01
  have hOutNeL0 : projectiveChordLine cfg pe ≠ L0 := by
    dsimp only [L0]
    exact projectiveChordLine_ne_projectiveRadicalAxis_of_endpoint
      cfg gamma.1 c0.1 (sixConicPairCircle_ne_gamma hgamma hc0)
      pe hxE
      (not_projectivePoint_orthogonal_projectiveRadicalAxis_of_not_mem_mem
        (sixConicPairCircle_ne_gamma hgamma hc0)
        hxNotGammaPoint hxC0)
  have hpencil := projectiveRadicalAxis_pencil_cross
    gamma.1 c0.1 c1.1
    (sixConicPairCircle_ne_gamma hgamma hc0)
    (sixConicPairCircle_ne_gamma hgamma hc1)
    (determinedCircle_coe_ne_of_ne hc01)
  have hOOutEq : O =
      Projectivization.cross (projectiveChordLine cfg pe) L0 := by
    calc
      O = Projectivization.cross L0 L1 := hOeq
      _ = Projectivization.cross L1 L0 :=
        Projectivization.cross_comm L0 L1
      _ = Projectivization.cross
          (projectiveRadicalAxis c0.1 c1.1
            (determinedCircle_coe_ne_of_ne hc01)) L0 := by
        dsimp only [L0, L1]
        exact hpencil
      _ = Projectivization.cross (projectiveChordLine cfg pe) L0 := by
        rw [hOutLine]
  have houtsider : Projectivization.orthogonal O
      (projectiveChordLine cfg pe) := by
    rw [hOOutEq]
    exact Projectivization.cross_orthogonal_left hOutNeL0
  have hchords :
      ∀ (a b : {x : α // x ∈ circleTrace cfg gamma.1}),
        (hab : a ≠ b) →
        {a.1, b.1} ∈ sixConicSignature cfg gamma e →
          Projectivization.orthogonal O
            (projectiveLine (cfg a.1) (cfg b.1)
              (cfg.injective.ne (Subtype.val_injective.ne hab))) := by
    intro a b hab hpair
    rw [sixConicSignature] at hpair
    obtain ⟨c, hc, hcpair⟩ := Finset.mem_image.mp hpair
    let p : KSubset α 2 :=
      ⟨circleTrace cfg c.1 ∩ circleTrace cfg gamma.1,
        (mem_sixConicPairCircles.mp hc).2⟩
    have haP : a.1 ∈ p.1 := by
      change a.1 ∈ circleTrace cfg c.1 ∩ circleTrace cfg gamma.1
      rw [hcpair]
      simp
    have hbP : b.1 ∈ p.1 := by
      change b.1 ∈ circleTrace cfg c.1 ∩ circleTrace cfg gamma.1
      rw [hcpair]
      simp
    have habVal : a.1 ≠ b.1 := Subtype.val_injective.ne hab
    have hOChord : Projectivization.orthogonal O
        (projectiveChordLine cfg p) := by
      rw [sixConicPairCircle_chordLine_eq_axis cfg gamma c hgamma hc]
      exact hcenter c hc
    rw [← projectiveChordLine_eq_projectiveLine_of_mem
      cfg p haP hbP habVal]
    exact hOChord
  refine ⟨heCard, O, hnondegenerate, hcenter, houtsider, hchords, ?_⟩
  intro a b hab hpair
  have hpairing := properCirclePencil_pairs_affine_chord
    gamma.1 O hnondegenerate
    (mem_circleTrace.mp a.2) (mem_circleTrace.mp b.2)
    (cfg.injective.ne (Subtype.val_injective.ne hab))
    (hchords a b hab hpair)
  simpa only [sixConicTraceParameter] using hpairing

/-! ## Positive full-edge pencil data used by host rigidity -/

/-- The common projective centre of the three trace chords belonging to a
full outsider edge. -/
noncomputable def sixConicFullEdgeCenter
    {α : Type u} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (gamma : Erdos506.V1.DeterminedCircle cfg)
    (hgamma : (circleTrace cfg gamma.1).card = 6)
    (X : Finset α)
    (hdisjoint : Disjoint (circleTrace cfg gamma.1) X)
    {e : Finset α} (heFull : e ∈ sixConicFullEdges cfg gamma X) :
    RealProjectivePlane :=
  (sixConicFullEdge_pencil
    cfg gamma hgamma X hdisjoint heFull).center

theorem sixConicFullEdge_card
    {α : Type u} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (gamma : Erdos506.V1.DeterminedCircle cfg)
    (hgamma : (circleTrace cfg gamma.1).card = 6)
    (X : Finset α)
    (hdisjoint : Disjoint (circleTrace cfg gamma.1) X)
    {e : Finset α} (heFull : e ∈ sixConicFullEdges cfg gamma X) :
    e.card = 2 :=
  (sixConicFullEdge_pencil
    cfg gamma hgamma X hdisjoint heFull).edgeCard

theorem sixConicFullEdgeCenter_nondegenerate
    {α : Type u} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (gamma : Erdos506.V1.DeterminedCircle cfg)
    (hgamma : (circleTrace cfg gamma.1).card = 6)
    (X : Finset α)
    (hdisjoint : Disjoint (circleTrace cfg gamma.1) X)
    {e : Finset α} (heFull : e ∈ sixConicFullEdges cfg gamma X) :
    properCirclePencilDeterminant gamma.1
      (sixConicFullEdgeCenter
        cfg gamma hgamma X hdisjoint heFull).rep ≠ 0 :=
  (sixConicFullEdge_pencil
    cfg gamma hgamma X hdisjoint heFull).nondegenerate

theorem sixConicFullEdgeCenter_on_outsiderChord
    {α : Type u} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (gamma : Erdos506.V1.DeterminedCircle cfg)
    (hgamma : (circleTrace cfg gamma.1).card = 6)
    (X : Finset α)
    (hdisjoint : Disjoint (circleTrace cfg gamma.1) X)
    {e : Finset α} (heFull : e ∈ sixConicFullEdges cfg gamma X) :
    Projectivization.orthogonal
      (sixConicFullEdgeCenter cfg gamma hgamma X hdisjoint heFull)
      (projectiveChordLine cfg
        (⟨e, sixConicFullEdge_card
          cfg gamma hgamma X hdisjoint heFull⟩ : KSubset α 2)) :=
  (sixConicFullEdge_pencil
    cfg gamma hgamma X hdisjoint heFull).outsider

theorem sixConicFullEdgeCenter_on_signatureChord
    {α : Type u} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (gamma : Erdos506.V1.DeterminedCircle cfg)
    (hgamma : (circleTrace cfg gamma.1).card = 6)
    (X : Finset α)
    (hdisjoint : Disjoint (circleTrace cfg gamma.1) X)
    {e : Finset α} (heFull : e ∈ sixConicFullEdges cfg gamma X)
    (a b : {x : α // x ∈ circleTrace cfg gamma.1})
    (hab : a ≠ b) (hpair : {a.1, b.1} ∈ sixConicSignature cfg gamma e) :
    Projectivization.orthogonal
      (sixConicFullEdgeCenter cfg gamma hgamma X hdisjoint heFull)
      (projectiveLine (cfg a.1) (cfg b.1)
        (cfg.injective.ne (Subtype.val_injective.ne hab))) :=
  (sixConicFullEdge_pencil
    cfg gamma hgamma X hdisjoint heFull).chords a b hab hpair

theorem sixConicFullEdgeCenter_pairs
    {α : Type u} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (gamma : Erdos506.V1.DeterminedCircle cfg)
    (hgamma : (circleTrace cfg gamma.1).card = 6)
    (X : Finset α)
    (hdisjoint : Disjoint (circleTrace cfg gamma.1) X)
    {e : Finset α} (heFull : e ∈ sixConicFullEdges cfg gamma X)
    (a b : {x : α // x ∈ circleTrace cfg gamma.1})
    (hab : a ≠ b) (hpair : {a.1, b.1} ∈ sixConicSignature cfg gamma e) :
    sixConicTraceParameter cfg gamma b =
      properCirclePencilGL gamma.1
          (sixConicFullEdgeCenter
            cfg gamma hgamma X hdisjoint heFull).rep
          (sixConicFullEdgeCenter_nondegenerate
            cfg gamma hgamma X hdisjoint heFull) •
        sixConicTraceParameter cfg gamma a :=
  (sixConicFullEdge_pencil
    cfg gamma hgamma X hdisjoint heFull).pairs a b hab hpair

/-- If the outsider edge lies on a second determined circle, its pencil
centre lies on the radical axis of that host circle and `gamma`. -/
theorem sixConicFullEdgeCenter_on_circleHostAxis
    {α : Type u} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (gamma : Erdos506.V1.DeterminedCircle cfg)
    (hgamma : (circleTrace cfg gamma.1).card = 6)
    (X : Finset α)
    (hdisjoint : Disjoint (circleTrace cfg gamma.1) X)
    {e : Finset α} (heFull : e ∈ sixConicFullEdges cfg gamma X)
    (K : Erdos506.V1.DeterminedCircle cfg) (hgammaK : gamma ≠ K)
    (heK : e ⊆ circleTrace cfg K.1) :
    Projectivization.orthogonal
      (sixConicFullEdgeCenter cfg gamma hgamma X hdisjoint heFull)
      (projectiveRadicalAxis gamma.1 K.1
        (determinedCircle_coe_ne_of_ne hgammaK)) := by
  classical
  let P := sixConicFullEdge_pencil
    cfg gamma hgamma X hdisjoint heFull
  change Projectivization.orthogonal P.center
    (projectiveRadicalAxis gamma.1 K.1
      (determinedCircle_coe_ne_of_ne hgammaK))
  have heSpec := mem_sixConicFullEdges.mp heFull
  have hePow := Finset.mem_powersetCard.mp heSpec.1
  have heDisjointGamma : Disjoint e (circleTrace cfg gamma.1) :=
    hdisjoint.symm.mono_left hePow.1
  let C := sixConicPairCircles cfg gamma e
  have hCcard : C.card = 3 := by
    change sixConicPairWeight cfg gamma e = 3
    exact heSpec.2
  have hCnonempty : C.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨c, hc⟩ := hCnonempty
  change c ∈ sixConicPairCircles cfg gamma e at hc
  have hgammaC := sixConicPairCircle_ne_gamma hgamma hc
  have hcenterC : Projectivization.orthogonal P.center
      (projectiveRadicalAxis gamma.1 c.1 hgammaC) :=
    P.pairAxes c hc
  by_cases hcK : c = K
  · subst c
    simpa only using hcenterC
  · have hcKcoe : c.1 ≠ K.1 := determinedCircle_coe_ne_of_ne hcK
    let pe : KSubset α 2 := ⟨e, P.edgeCard⟩
    have heC (i : Fin 2) : chordPoint cfg pe i ∈ (c.1.1 : Set Point2) := by
      apply mem_circleTrace.mp
      exact (mem_sixConicPairCircles.mp hc).1 (chordLabel_mem pe i)
    have heHost (i : Fin 2) : chordPoint cfg pe i ∈ (K.1.1 : Set Point2) := by
      apply mem_circleTrace.mp
      exact heK (chordLabel_mem pe i)
    have hOutAxis : projectiveChordLine cfg pe =
        projectiveRadicalAxis c.1 K.1 hcKcoe :=
      projectiveChordLine_eq_projectiveRadicalAxis_of_endpoints
        cfg c.1 K.1 hcKcoe pe (heC 0) (heC 1)
          (heHost 0) (heHost 1)
    have hcenterOut : Projectivization.orthogonal P.center
        (projectiveRadicalAxis c.1 K.1 hcKcoe) := by
      rw [← hOutAxis]
      exact P.outsider
    let LgammaC := projectiveRadicalAxis gamma.1 c.1 hgammaC
    let LcK := projectiveRadicalAxis c.1 K.1 hcKcoe
    let LgammaK := projectiveRadicalAxis gamma.1 K.1
      (determinedCircle_coe_ne_of_ne hgammaK)
    let x := chordLabel pe 0
    have hxE : x ∈ e := chordLabel_mem pe 0
    have hxNotGamma : x ∉ circleTrace cfg gamma.1 := by
      intro hxGamma
      exact Finset.disjoint_left.mp heDisjointGamma hxE hxGamma
    have hxNotGammaPoint : cfg x ∉ (gamma.1.1 : Set Point2) := by
      intro hxGamma
      exact hxNotGamma (mem_circleTrace.mpr hxGamma)
    have hxC : cfg x ∈ (c.1.1 : Set Point2) := heC 0
    have hxK : cfg x ∈ (K.1.1 : Set Point2) := heHost 0
    have hAxes : LgammaC ≠ LcK := by
      intro hEq
      apply
        (not_projectivePoint_orthogonal_projectiveRadicalAxis_of_not_mem_mem
          hgammaC hxNotGammaPoint hxC)
      change Projectivization.orthogonal
        (projectivePoint (cfg x)) LgammaC
      rw [hEq]
      exact projectivePoint_orthogonal_projectiveRadicalAxis_of_mem
        hcKcoe hxC hxK
    have hOcross : P.center =
        Projectivization.cross LgammaC LcK := by
      apply projectiveCovector_eq_cross_of_orthogonal hAxes
      · exact Projectivization.orthogonal_comm.mp hcenterC
      · exact Projectivization.orthogonal_comm.mp hcenterOut
    have hpencil := projectiveRadicalAxis_pencil_cross
      gamma.1 c.1 K.1 hgammaC
      (determinedCircle_coe_ne_of_ne hgammaK) hcKcoe
    have hOtarget : P.center =
        Projectivization.cross LgammaK LgammaC := by
      calc
        P.center = Projectivization.cross LgammaC LcK := hOcross
        _ = Projectivization.cross LcK LgammaC :=
          Projectivization.cross_comm LgammaC LcK
        _ = Projectivization.cross LgammaK LgammaC := by
          exact hpencil.symm
    change Projectivization.orthogonal P.center LgammaK
    by_cases hAxesTarget : LgammaK = LgammaC
    · rw [hAxesTarget]
      exact hcenterC
    · rw [hOtarget]
      exact Projectivization.cross_orthogonal_left hAxesTarget

/-! ## A reusable common-centre classifier -/

/-- A point at infinity never lies on the projective completion of a proper
circle, so it defines a nondegenerate residual-intersection involution. -/
theorem properCirclePencilDeterminant_pointAtInfinity_ne_zero
    (c : ProperCircle) (v : Point2) (hv : v ≠ 0) :
    properCirclePencilDeterminant c (pointAtInfinity v hv).rep ≠ 0 := by
  intro hzero
  obtain ⟨z, _hz, hprojective⟩ :=
    properCirclePencilDeterminant_zero_gives_affine_point
      c (pointAtInfinity v hv) hzero
  exact pointAtInfinity_ne_projectivePoint hv z hprojective

/-- Any perfect matching of six marked points on a proper circle whose three
chords have one nondegenerate projective centre is one of the four intrinsic
dihedral matchings.  This is the reusable geometric core behind both the
six-conic signature cap and the sharp parallel-chord case of Ungar's bound. -/
theorem sixConic_commonCenterPerfectMatching_dihedral
    {α : Type u} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (gamma : Erdos506.V1.DeterminedCircle cfg)
    (hgamma : (circleTrace cfg gamma.1).card = 6)
    (matching : Finset (Finset α))
    (hmatching : SixConicPerfectMatchingOn
      (circleTrace cfg gamma.1) matching)
    (O : RealProjectivePlane)
    (hnondegenerate : properCirclePencilDeterminant gamma.1 O.rep ≠ 0)
    (hchords : ∀
      (a b : {x : α // x ∈ circleTrace cfg gamma.1}),
      (hab : a ≠ b) → {a.1, b.1} ∈ matching →
        Projectivization.orthogonal O
          (projectiveLine (cfg a.1) (cfg b.1)
            (cfg.injective.ne (Subtype.val_injective.ne hab)))) :
    ∃ code : SixCycleInvolutionCode,
      matching = relabelSixCycleMatching
        (fun i => (sixConicCyclicLabel cfg gamma hgamma i).1) code := by
  classical
  let label := sixConicCyclicLabel cfg gamma hgamma
  let τ : Equiv.Perm (Fin 6) :=
    perfectMatchingLabelPerm hmatching label
  have haction : ∀ i : Fin 6,
      sixConicTraceParameter cfg gamma (label (τ i)) =
        properCirclePencilGL gamma.1 O.rep hnondegenerate •
          sixConicTraceParameter cfg gamma (label i) := by
    intro i
    rw [perfectMatchingLabelPerm_partner hmatching label i]
    have hab : label i ≠ perfectMatchingPartner hmatching (label i) := by
      intro h
      exact (perfectMatchingPartner_spec hmatching (label i)).1
        (congrArg Subtype.val h).symm
    have hpair := (perfectMatchingPartner_spec hmatching (label i)).2
    have hpairing := properCirclePencil_pairs_affine_chord
      gamma.1 O hnondegenerate
      (mem_circleTrace.mp (label i).2)
      (mem_circleTrace.mp (perfectMatchingPartner hmatching (label i)).2)
      (cfg.injective.ne (Subtype.val_injective.ne hab))
      (hchords (label i) (perfectMatchingPartner hmatching (label i))
        hab hpair)
    simpa only [sixConicTraceParameter] using hpairing
  have hinvolution : ∀ i, τ (τ i) = i := by
    intro i
    apply label.injective
    rw [perfectMatchingLabelPerm_partner hmatching label,
      perfectMatchingLabelPerm_partner hmatching label,
      perfectMatchingPartner_involutive hmatching]
  have hfixedPointFree : ∀ i, τ i ≠ i := by
    intro i hi
    have hlabel := congrArg label hi
    rw [perfectMatchingLabelPerm_partner hmatching label] at hlabel
    exact (perfectMatchingPartner_spec hmatching (label i)).1
      (congrArg Subtype.val hlabel)
  have horientation :
      (∀ i j k, sbtw i j k → sbtw (τ i) (τ j) (τ k)) ∨
      (∀ i j k, sbtw i j k → sbtw (τ i) (τ k) (τ j)) := by
    rcases properCirclePencil_preserves_or_reverses_cyclicOrder
      gamma.1 O.rep hnondegenerate with hpreserve | hreverse
    · left
      intro i j k hijk
      have hcyclic :=
        (sixConicCyclicLabel_parameter_sbtw_iff
          cfg gamma hgamma i j k).2 hijk
      have himage := hpreserve _ _ _ hcyclic
      rw [← haction i, ← haction j, ← haction k] at himage
      exact (sixConicCyclicLabel_parameter_sbtw_iff
        cfg gamma hgamma (τ i) (τ j) (τ k)).1 himage
    · right
      intro i j k hijk
      have hcyclic :=
        (sixConicCyclicLabel_parameter_sbtw_iff
          cfg gamma hgamma i j k).2 hijk
      have himage := hreverse _ _ _ hcyclic
      rw [← haction i, ← haction k, ← haction j] at himage
      exact (sixConicCyclicLabel_parameter_sbtw_iff
        cfg gamma hgamma (τ i) (τ k) (τ j)).1 himage
  obtain ⟨code, hcode⟩ := finSix_dihedral_classification
    τ hinvolution hfixedPointFree horientation
  exact ⟨code, perfectMatching_eq_relabel_of_dihedralPerm
    hmatching label code hcode⟩

/-! ## Construction of the public dihedral witness -/

/-- The real-circle geometry constructs the positive dihedral witness from
the configuration itself.  In particular, the witness is not an additional
argument or a field of the six-conic principle. -/
noncomputable def sixConic_activeSignature_dihedralWitness
    {α : Type u} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (gamma : Erdos506.V1.DeterminedCircle cfg)
    (hgamma : (circleTrace cfg gamma.1).card = 6)
    (X : Finset α)
    (hdisjoint : Disjoint (circleTrace cfg gamma.1) X) :
    SixConicActiveSignatureDihedralWitness cfg gamma X := by
  classical
  let label := sixConicCyclicLabel cfg gamma hgamma
  refine ⟨label, ?_⟩
  intro signature hsignature
  have hmatching := sixConic_activeSignature_isPerfectMatching
    cfg gamma hgamma X hdisjoint hsignature
  rw [sixConicActiveSignatures] at hsignature
  obtain ⟨e, heFull, rfl⟩ := Finset.mem_image.mp hsignature
  let pencil := sixConicFullEdge_pencil
    cfg gamma hgamma X hdisjoint heFull
  let τ : Equiv.Perm (Fin 6) :=
    perfectMatchingLabelPerm hmatching label
  have haction : ∀ i : Fin 6,
      sixConicTraceParameter cfg gamma (label (τ i)) =
        properCirclePencilGL gamma.1 pencil.center.rep
            pencil.nondegenerate •
          sixConicTraceParameter cfg gamma (label i) := by
    intro i
    rw [perfectMatchingLabelPerm_partner hmatching label i]
    apply pencil.pairs
    · intro h
      apply (perfectMatchingPartner_spec hmatching (label i)).1
      exact congrArg Subtype.val h.symm
    · exact (perfectMatchingPartner_spec hmatching (label i)).2
  have hinvolution : ∀ i, τ (τ i) = i := by
    intro i
    apply label.injective
    rw [perfectMatchingLabelPerm_partner hmatching label,
      perfectMatchingLabelPerm_partner hmatching label,
      perfectMatchingPartner_involutive hmatching]
  have hfixedPointFree : ∀ i, τ i ≠ i := by
    intro i hi
    have hlabel := congrArg label hi
    rw [perfectMatchingLabelPerm_partner hmatching label] at hlabel
    exact (perfectMatchingPartner_spec hmatching (label i)).1
      (congrArg Subtype.val hlabel)
  have horientation :
      (∀ i j k, sbtw i j k → sbtw (τ i) (τ j) (τ k)) ∨
      (∀ i j k, sbtw i j k → sbtw (τ i) (τ k) (τ j)) := by
    rcases properCirclePencil_preserves_or_reverses_cyclicOrder
      gamma.1 pencil.center.rep pencil.nondegenerate with
      hpreserve | hreverse
    · left
      intro i j k hijk
      have hcyclic :=
        (sixConicCyclicLabel_parameter_sbtw_iff
          cfg gamma hgamma i j k).2 hijk
      have himage := hpreserve _ _ _ hcyclic
      rw [← haction i, ← haction j, ← haction k] at himage
      exact (sixConicCyclicLabel_parameter_sbtw_iff
        cfg gamma hgamma (τ i) (τ j) (τ k)).1 himage
    · right
      intro i j k hijk
      have hcyclic :=
        (sixConicCyclicLabel_parameter_sbtw_iff
          cfg gamma hgamma i j k).2 hijk
      have himage := hreverse _ _ _ hcyclic
      rw [← haction i, ← haction k, ← haction j] at himage
      exact (sixConicCyclicLabel_parameter_sbtw_iff
        cfg gamma hgamma (τ i) (τ k) (τ j)).1 himage
  obtain ⟨code, hcode⟩ := finSix_dihedral_classification
    τ hinvolution hfixedPointFree horientation
  exact ⟨code, perfectMatching_eq_relabel_of_dihedralPerm
    hmatching label code hcode⟩

/-- Field-free replacement for
the active-signature cap. -/
theorem sixConic_activeSignatures_card_le_four
    {α : Type u} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (gamma : Erdos506.V1.DeterminedCircle cfg)
    (hgamma : (circleTrace cfg gamma.1).card = 6)
    (X : Finset α)
    (hdisjoint : Disjoint (circleTrace cfg gamma.1) X) :
    (sixConicActiveSignatures cfg gamma X).card ≤ 4 := by
  exact sixConic_activeSignatures_card_le_four_of_dihedralWitness
    cfg gamma hgamma X hdisjoint
    (sixConic_activeSignature_dihedralWitness
      cfg gamma hgamma X hdisjoint)

end Erdos506.Incidence
