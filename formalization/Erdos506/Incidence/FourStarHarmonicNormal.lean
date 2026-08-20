import Erdos506.Incidence.FourStarNormalForm
import Erdos506.Incidence.RealProjectiveHarmonic

/-!
# Harmonic traces in the normal four-star

The four standard base lines have an explicit homogeneous parametrisation by
`RP¹`.  At the unique surviving scalar normal form their three opposite
vertices and private point make a harmonic range on each base line.
-/

namespace Erdos506.Incidence

open Matrix
open scoped LinearAlgebra.Projectivization

noncomputable section

local instance : DecidableEq RealProjectiveOnePoint := Classical.decEq _

/-- Homogeneous parametrisation of the `i`-th standard base line. -/
def fourStarNormalLineParameter : Fin 4 -> RealProjectiveLineVector -> Homogeneous3 :=
  fun i u => match i with
    | 0 => ![0, u 0, u 1]
    | 1 => ![u 0, 0, u 1]
    | 2 => ![u 0, u 1, 0]
    | 3 => ![u 0, u 1, -u 0 - u 1]

/-- The parametrisation of each standard base line is injective. -/
theorem fourStarNormalLineParameter_injective (i : Fin 4) :
    Function.Injective (fourStarNormalLineParameter i) := by
  intro u v h
  funext j
  fin_cases i <;> fin_cases j
  · simpa [fourStarNormalLineParameter] using congrFun h (1 : Fin 3)
  · simpa [fourStarNormalLineParameter] using congrFun h (2 : Fin 3)
  · simpa [fourStarNormalLineParameter] using congrFun h (0 : Fin 3)
  · simpa [fourStarNormalLineParameter] using congrFun h (2 : Fin 3)
  · simpa [fourStarNormalLineParameter] using congrFun h (0 : Fin 3)
  · simpa [fourStarNormalLineParameter] using congrFun h (1 : Fin 3)
  · simpa [fourStarNormalLineParameter] using congrFun h (0 : Fin 3)
  · simpa [fourStarNormalLineParameter] using congrFun h (1 : Fin 3)

/-- A nonzero projective-line vector has a nonzero image on every normal base
line. -/
theorem fourStarNormalLineParameter_ne_zero
    (i : Fin 4) {u : RealProjectiveLineVector} (hu : u ≠ 0) :
    fourStarNormalLineParameter i u ≠ 0 := by
  intro h
  apply hu
  apply fourStarNormalLineParameter_injective i
  have hzero : fourStarNormalLineParameter i 0 = 0 := by
    fin_cases i <;> simp [fourStarNormalLineParameter]
  rw [hzero]
  exact h

/-- The parameter vector for affine coordinate `-1`. -/
def fourStarNormalMinusOneVector : RealProjectiveLineVector := ![1, -1]

/-- The parameter vector for affine coordinate `-2`. -/
def fourStarNormalMinusTwoVector : RealProjectiveLineVector := ![2, -1]

theorem fourStarNormalMinusOneVector_ne_zero :
    fourStarNormalMinusOneVector ≠ 0 := by
  intro h
  have h0 := congrFun h (0 : Fin 2)
  norm_num [fourStarNormalMinusOneVector] at h0

theorem fourStarNormalMinusTwoVector_ne_zero :
    fourStarNormalMinusTwoVector ≠ 0 := by
  intro h
  have h0 := congrFun h (0 : Fin 2)
  norm_num [fourStarNormalMinusTwoVector] at h0

noncomputable def fourStarNormalMinusOne : RealProjectiveOnePoint :=
  Projectivization.mk ℝ fourStarNormalMinusOneVector
    fourStarNormalMinusOneVector_ne_zero

noncomputable def fourStarNormalMinusTwo : RealProjectiveOnePoint :=
  Projectivization.mk ℝ fourStarNormalMinusTwoVector
    fourStarNormalMinusTwoVector_ne_zero

private theorem fourStarNormal_parameter_ne
    {u v : RealProjectiveLineVector} (hu : u ≠ 0) (hv : v ≠ 0)
    (hbracket : realProjectiveBracket u v ≠ 0) :
    Projectivization.mk ℝ u hu ≠ Projectivization.mk ℝ v hv := by
  intro h
  apply hbracket
  exact (realProjective_mk_eq_mk_iff_bracket_eq_zero hu hv).mp h

private theorem zero_ne_minusOne :
    realProjectiveLineZero ≠ fourStarNormalMinusOne := by
  apply fourStarNormal_parameter_ne
  norm_num [realProjectiveBracket, realProjectiveLineZeroVector,
    fourStarNormalMinusOneVector]

private theorem infinity_ne_minusOne :
    realProjectiveLineInfinity ≠ fourStarNormalMinusOne := by
  apply fourStarNormal_parameter_ne
  norm_num [realProjectiveBracket, realProjectiveLineInfinityVector,
    fourStarNormalMinusOneVector]

private theorem one_ne_minusOne :
    realProjectiveLineOne ≠ fourStarNormalMinusOne := by
  apply fourStarNormal_parameter_ne
  norm_num [realProjectiveBracket, realProjectiveLineOneVector,
    fourStarNormalMinusOneVector]

private theorem zero_ne_minusTwo :
    realProjectiveLineZero ≠ fourStarNormalMinusTwo := by
  apply fourStarNormal_parameter_ne
  norm_num [realProjectiveBracket, realProjectiveLineZeroVector,
    fourStarNormalMinusTwoVector]

private theorem infinity_ne_minusTwo :
    realProjectiveLineInfinity ≠ fourStarNormalMinusTwo := by
  apply fourStarNormal_parameter_ne
  norm_num [realProjectiveBracket, realProjectiveLineInfinityVector,
    fourStarNormalMinusTwoVector]

private theorem minusOne_ne_minusTwo :
    fourStarNormalMinusOne ≠ fourStarNormalMinusTwo := by
  apply fourStarNormal_parameter_ne
  norm_num [realProjectiveBracket, fourStarNormalMinusOneVector,
    fourStarNormalMinusTwoVector]

private theorem isRealProjectiveHarmonicFour_of_ordered
    (P Q R S : RealProjectiveOnePoint)
    (hPQ : P ≠ Q) (hPR : P ≠ R) (hPS : P ≠ S)
    (hQR : Q ≠ R) (hQS : Q ≠ S) (hRS : R ≠ S)
    (hharmonic : RealProjectiveHarmonic P Q R S) :
    IsRealProjectiveHarmonicFour ({P, Q, R, S} : Finset RealProjectiveOnePoint) := by
  refine ⟨?_, P, Q, R, S, rfl, ⟨hPQ, hPR, hPS, hQR, hQS, hRS⟩, hharmonic⟩
  have hP : P ∉ ({Q, R, S} : Finset RealProjectiveOnePoint) := by
    simp [hPQ, hPR, hPS]
  have hQ : Q ∉ ({R, S} : Finset RealProjectiveOnePoint) := by
    simp [hQR, hQS]
  have hR : R ∉ ({S} : Finset RealProjectiveOnePoint) := by
    simp [hRS]
  rw [Finset.card_insert_of_notMem hP,
    Finset.card_insert_of_notMem hQ,
    Finset.card_insert_of_notMem hR]
  norm_num

/-- The four parameter values occurring on the `i`-th normal base line. -/
noncomputable def fourStarNormalTraceParameterSet :
    Fin 4 -> Finset RealProjectiveOnePoint :=
  fun i => match i with
    | 0 => {realProjectiveLineZero, realProjectiveLineInfinity,
      realProjectiveLineOne, fourStarNormalMinusOne}
    | 1 => {realProjectiveLineZero, realProjectiveLineInfinity,
      realProjectiveLineOne, fourStarNormalMinusOne}
    | 2 => {realProjectiveLineZero, realProjectiveLineInfinity,
      realProjectiveLineOne, fourStarNormalMinusOne}
    | 3 => {realProjectiveLineZero, fourStarNormalMinusTwo,
      realProjectiveLineInfinity, fourStarNormalMinusOne}

/-- The scalar normal form left after the `T`-, cycle-, and triangle-pendant
exclusions. -/
noncomputable def fourStarNormalSurvivor : FourStarNormalDeterminants where
  a := 1
  b := 1
  c := 1
  d := -(1 / 2)
  a_ne_zero := by norm_num
  b_ne_zero := by norm_num
  c_ne_zero := by norm_num
  d_ne_zero := by norm_num
  a_ne_neg_one := by norm_num
  b_ne_neg_one := by norm_num
  c_ne_neg_one := by norm_num
  d_ne_neg_one := by norm_num

/-- The four scalar coordinates characterize the surviving normal form.
The remaining fields of `FourStarNormalDeterminants` are propositions, so
proof irrelevance makes the resulting structure equality canonical. -/
theorem FourStarNormalDeterminants.eq_fourStarNormalSurvivor
    (N : FourStarNormalDeterminants)
    (ha : N.a = 1) (hb : N.b = 1) (hc : N.c = 1)
    (hd : N.d = -1 / 2) :
    N = fourStarNormalSurvivor := by
  cases N with
  | mk a b c d ha0 hb0 hc0 hd0 ha1 hb1 hc1 hd1 =>
      simp only at ha hb hc hd
      subst a
      subst b
      subst c
      subst d
      congr <;> norm_num

/-! ## The four concrete traces -/

theorem fourStarNormalLineParameter_zero_eq_cross01 :
    fourStarNormalLineParameter 0 realProjectiveLineZeroVector =
      crossProduct (projectiveCovectorNormalLine 0)
        (projectiveCovectorNormalLine 1) := by
  simp [fourStarNormalLineParameter, realProjectiveLineZeroVector,
    projectiveCovectorNormalLine, cross_apply]

theorem fourStarNormalLineParameter_infinity_eq_neg_cross02 :
    fourStarNormalLineParameter 0 realProjectiveLineInfinityVector =
      -crossProduct (projectiveCovectorNormalLine 0)
        (projectiveCovectorNormalLine 2) := by
  simp [fourStarNormalLineParameter, realProjectiveLineInfinityVector,
    projectiveCovectorNormalLine, cross_apply]

theorem fourStarNormalLineParameter_minusOne_eq_neg_cross03 :
    fourStarNormalLineParameter 0 fourStarNormalMinusOneVector =
      -crossProduct (projectiveCovectorNormalLine 0)
        (projectiveCovectorNormalLine 3) := by
  simp [fourStarNormalLineParameter, fourStarNormalMinusOneVector,
    projectiveCovectorNormalLine, cross_apply]

theorem fourStarNormalLineParameter_one_eq_private0 :
    fourStarNormalLineParameter 0 realProjectiveLineOneVector =
      fourStarNormalPrivatePoint fourStarNormalSurvivor 0 := by
  simp [fourStarNormalLineParameter, realProjectiveLineOneVector,
    fourStarNormalPrivatePoint, fourStarNormalSurvivor]

theorem fourStarNormalLineParameter_zero_eq_neg_cross10 :
    fourStarNormalLineParameter 1 realProjectiveLineZeroVector =
      -crossProduct (projectiveCovectorNormalLine 1)
        (projectiveCovectorNormalLine 0) := by
  simp [fourStarNormalLineParameter, realProjectiveLineZeroVector,
    projectiveCovectorNormalLine, cross_apply]

theorem fourStarNormalLineParameter_infinity_eq_cross12 :
    fourStarNormalLineParameter 1 realProjectiveLineInfinityVector =
      crossProduct (projectiveCovectorNormalLine 1)
        (projectiveCovectorNormalLine 2) := by
  simp [fourStarNormalLineParameter, realProjectiveLineInfinityVector,
    projectiveCovectorNormalLine, cross_apply]

theorem fourStarNormalLineParameter_minusOne_eq_cross13 :
    fourStarNormalLineParameter 1 fourStarNormalMinusOneVector =
      crossProduct (projectiveCovectorNormalLine 1)
        (projectiveCovectorNormalLine 3) := by
  simp [fourStarNormalLineParameter, fourStarNormalMinusOneVector,
    projectiveCovectorNormalLine, cross_apply]

theorem fourStarNormalLineParameter_one_eq_private1 :
    fourStarNormalLineParameter 1 realProjectiveLineOneVector =
      fourStarNormalPrivatePoint fourStarNormalSurvivor 1 := by
  simp [fourStarNormalLineParameter, realProjectiveLineOneVector,
    fourStarNormalPrivatePoint, fourStarNormalSurvivor]

theorem fourStarNormalLineParameter_zero_eq_cross20 :
    fourStarNormalLineParameter 2 realProjectiveLineZeroVector =
      crossProduct (projectiveCovectorNormalLine 2)
        (projectiveCovectorNormalLine 0) := by
  simp [fourStarNormalLineParameter, realProjectiveLineZeroVector,
    projectiveCovectorNormalLine, cross_apply]

theorem fourStarNormalLineParameter_infinity_eq_neg_cross21 :
    fourStarNormalLineParameter 2 realProjectiveLineInfinityVector =
      -crossProduct (projectiveCovectorNormalLine 2)
        (projectiveCovectorNormalLine 1) := by
  simp [fourStarNormalLineParameter, realProjectiveLineInfinityVector,
    projectiveCovectorNormalLine, cross_apply]

theorem fourStarNormalLineParameter_minusOne_eq_neg_cross23 :
    fourStarNormalLineParameter 2 fourStarNormalMinusOneVector =
      -crossProduct (projectiveCovectorNormalLine 2)
        (projectiveCovectorNormalLine 3) := by
  simp [fourStarNormalLineParameter, fourStarNormalMinusOneVector,
    projectiveCovectorNormalLine, cross_apply]

theorem fourStarNormalLineParameter_one_eq_private2 :
    fourStarNormalLineParameter 2 realProjectiveLineOneVector =
      fourStarNormalPrivatePoint fourStarNormalSurvivor 2 := by
  simp [fourStarNormalLineParameter, realProjectiveLineOneVector,
    fourStarNormalPrivatePoint, fourStarNormalSurvivor]

theorem fourStarNormalLineParameter_zero_eq_cross30 :
    fourStarNormalLineParameter 3 realProjectiveLineZeroVector =
      crossProduct (projectiveCovectorNormalLine 3)
        (projectiveCovectorNormalLine 0) := by
  simp [fourStarNormalLineParameter, realProjectiveLineZeroVector,
    projectiveCovectorNormalLine, cross_apply]

theorem fourStarNormalLineParameter_infinity_eq_neg_cross31 :
    fourStarNormalLineParameter 3 realProjectiveLineInfinityVector =
      -crossProduct (projectiveCovectorNormalLine 3)
        (projectiveCovectorNormalLine 1) := by
  simp [fourStarNormalLineParameter, realProjectiveLineInfinityVector,
    projectiveCovectorNormalLine, cross_apply]

theorem fourStarNormalLineParameter_minusOne_eq_cross32 :
    fourStarNormalLineParameter 3 fourStarNormalMinusOneVector =
      crossProduct (projectiveCovectorNormalLine 3)
        (projectiveCovectorNormalLine 2) := by
  simp [fourStarNormalLineParameter, fourStarNormalMinusOneVector,
    projectiveCovectorNormalLine, cross_apply]

theorem fourStarNormalLineParameter_minusTwo_eq_two_smul_private3 :
    fourStarNormalLineParameter 3 fourStarNormalMinusTwoVector =
      (2 : ℝ) • fourStarNormalPrivatePoint fourStarNormalSurvivor 3 := by
  simp [fourStarNormalLineParameter, fourStarNormalMinusTwoVector,
    fourStarNormalPrivatePoint, fourStarNormalSurvivor]
  ring

/-! ## Ordered harmonic certificates -/

theorem fourStarNormal_trace0_harmonic :
    RealProjectiveHarmonic
      (Projectivization.mk ℝ realProjectiveLineZeroVector
        realProjectiveLineZeroVector_ne_zero)
      (Projectivization.mk ℝ realProjectiveLineInfinityVector
        realProjectiveLineInfinityVector_ne_zero)
      (Projectivization.mk ℝ realProjectiveLineOneVector
        realProjectiveLineOneVector_ne_zero)
      (Projectivization.mk ℝ fourStarNormalMinusOneVector
        fourStarNormalMinusOneVector_ne_zero) := by
  apply realProjectiveHarmonic_mk <;> try assumption
  norm_num [realProjectiveBracket, realProjectiveLineZeroVector,
    realProjectiveLineInfinityVector, realProjectiveLineOneVector,
    fourStarNormalMinusOneVector]

theorem fourStarNormal_trace1_harmonic :
    RealProjectiveHarmonic
      (Projectivization.mk ℝ realProjectiveLineZeroVector
        realProjectiveLineZeroVector_ne_zero)
      (Projectivization.mk ℝ realProjectiveLineInfinityVector
        realProjectiveLineInfinityVector_ne_zero)
      (Projectivization.mk ℝ realProjectiveLineOneVector
        realProjectiveLineOneVector_ne_zero)
      (Projectivization.mk ℝ fourStarNormalMinusOneVector
        fourStarNormalMinusOneVector_ne_zero) :=
  fourStarNormal_trace0_harmonic

theorem fourStarNormal_trace2_harmonic :
    RealProjectiveHarmonic
      (Projectivization.mk ℝ realProjectiveLineZeroVector
        realProjectiveLineZeroVector_ne_zero)
      (Projectivization.mk ℝ realProjectiveLineInfinityVector
        realProjectiveLineInfinityVector_ne_zero)
      (Projectivization.mk ℝ realProjectiveLineOneVector
        realProjectiveLineOneVector_ne_zero)
      (Projectivization.mk ℝ fourStarNormalMinusOneVector
        fourStarNormalMinusOneVector_ne_zero) :=
  fourStarNormal_trace0_harmonic

/-- On the fourth base line the harmonic ordering is
`(0,-2;∞,-1)`. -/
theorem fourStarNormal_trace3_harmonic :
    RealProjectiveHarmonic
      (Projectivization.mk ℝ realProjectiveLineZeroVector
        realProjectiveLineZeroVector_ne_zero)
      (Projectivization.mk ℝ fourStarNormalMinusTwoVector
        fourStarNormalMinusTwoVector_ne_zero)
      (Projectivization.mk ℝ realProjectiveLineInfinityVector
        realProjectiveLineInfinityVector_ne_zero)
      (Projectivization.mk ℝ fourStarNormalMinusOneVector
        fourStarNormalMinusOneVector_ne_zero) := by
  apply realProjectiveHarmonic_mk <;> try assumption
  norm_num [realProjectiveBracket, realProjectiveLineZeroVector,
    realProjectiveLineInfinityVector, fourStarNormalMinusOneVector,
    fourStarNormalMinusTwoVector]

/-- Each normal base-line trace is an order-free harmonic four-set. -/
theorem fourStarNormal_traceParameterSet_harmonic (i : Fin 4) :
    IsRealProjectiveHarmonicFour (fourStarNormalTraceParameterSet i) := by
  fin_cases i
  · simpa [fourStarNormalTraceParameterSet, fourStarNormalMinusOne] using
      (isRealProjectiveHarmonicFour_of_ordered
        realProjectiveLineZero realProjectiveLineInfinity realProjectiveLineOne
        fourStarNormalMinusOne
        realProjectiveLineZero_ne_infinity realProjectiveLineZero_ne_one
        zero_ne_minusOne realProjectiveLineInfinity_ne_one
        infinity_ne_minusOne one_ne_minusOne
        (by simpa [fourStarNormalMinusOne] using fourStarNormal_trace0_harmonic))
  · simpa [fourStarNormalTraceParameterSet, fourStarNormalMinusOne] using
      (isRealProjectiveHarmonicFour_of_ordered
        realProjectiveLineZero realProjectiveLineInfinity realProjectiveLineOne
        fourStarNormalMinusOne
        realProjectiveLineZero_ne_infinity realProjectiveLineZero_ne_one
        zero_ne_minusOne realProjectiveLineInfinity_ne_one
        infinity_ne_minusOne one_ne_minusOne
        (by simpa [fourStarNormalMinusOne] using fourStarNormal_trace1_harmonic))
  · simpa [fourStarNormalTraceParameterSet, fourStarNormalMinusOne] using
      (isRealProjectiveHarmonicFour_of_ordered
        realProjectiveLineZero realProjectiveLineInfinity realProjectiveLineOne
        fourStarNormalMinusOne
        realProjectiveLineZero_ne_infinity realProjectiveLineZero_ne_one
        zero_ne_minusOne realProjectiveLineInfinity_ne_one
        infinity_ne_minusOne one_ne_minusOne
        (by simpa [fourStarNormalMinusOne] using fourStarNormal_trace2_harmonic))
  · simpa [fourStarNormalTraceParameterSet, fourStarNormalMinusOne,
      fourStarNormalMinusTwo] using
      (isRealProjectiveHarmonicFour_of_ordered
        realProjectiveLineZero fourStarNormalMinusTwo
        realProjectiveLineInfinity fourStarNormalMinusOne
        zero_ne_minusTwo realProjectiveLineZero_ne_infinity zero_ne_minusOne
        infinity_ne_minusTwo.symm minusOne_ne_minusTwo.symm infinity_ne_minusOne
        (by simpa [fourStarNormalMinusOne, fourStarNormalMinusTwo] using
          fourStarNormal_trace3_harmonic))

end

end Erdos506.Incidence
