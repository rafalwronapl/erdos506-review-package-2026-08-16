import Erdos506.Incidence.RealProjectiveLineCyclicOrder

/-!
# A standard frame on the real projective line

The three points below are deliberately kept as homogeneous projective
points.  They form the common target frame for normalising triples on a
proper circle parameter line.
-/

namespace Erdos506.Incidence

open scoped LinearAlgebra.Projectivization

/-- The homogeneous representative of affine coordinate zero. -/
def realProjectiveLineZeroVector : RealProjectiveLineVector := ![0, 1]

/-- The homogeneous representative of the point at infinity. -/
def realProjectiveLineInfinityVector : RealProjectiveLineVector := ![1, 0]

/-- The homogeneous representative of affine coordinate one. -/
def realProjectiveLineOneVector : RealProjectiveLineVector := ![1, 1]

theorem realProjectiveLineZeroVector_ne_zero :
    realProjectiveLineZeroVector ≠ 0 := by
  intro h
  have h1 := congrFun h (1 : Fin 2)
  norm_num [realProjectiveLineZeroVector] at h1

theorem realProjectiveLineInfinityVector_ne_zero :
    realProjectiveLineInfinityVector ≠ 0 := by
  intro h
  have h0 := congrFun h (0 : Fin 2)
  norm_num [realProjectiveLineInfinityVector] at h0

theorem realProjectiveLineOneVector_ne_zero :
    realProjectiveLineOneVector ≠ 0 := by
  intro h
  have h0 := congrFun h (0 : Fin 2)
  norm_num [realProjectiveLineOneVector] at h0

/-- The affine coordinate zero in `RP¹`. -/
noncomputable def realProjectiveLineZero : RealProjectiveOnePoint :=
  Projectivization.mk ℝ realProjectiveLineZeroVector
    realProjectiveLineZeroVector_ne_zero

/-- The point at infinity in `RP¹`. -/
noncomputable def realProjectiveLineInfinity : RealProjectiveOnePoint :=
  Projectivization.mk ℝ realProjectiveLineInfinityVector
    realProjectiveLineInfinityVector_ne_zero

/-- The affine coordinate one in `RP¹`. -/
noncomputable def realProjectiveLineOne : RealProjectiveOnePoint :=
  Projectivization.mk ℝ realProjectiveLineOneVector
    realProjectiveLineOneVector_ne_zero

@[simp] theorem realProjectiveBracket_zero_infinity :
    realProjectiveBracket realProjectiveLineZeroVector
      realProjectiveLineInfinityVector = -1 := by
  simp [realProjectiveBracket, realProjectiveLineZeroVector,
    realProjectiveLineInfinityVector]

@[simp] theorem realProjectiveBracket_zero_one :
    realProjectiveBracket realProjectiveLineZeroVector
      realProjectiveLineOneVector = -1 := by
  simp [realProjectiveBracket, realProjectiveLineZeroVector,
    realProjectiveLineOneVector]

@[simp] theorem realProjectiveBracket_infinity_one :
    realProjectiveBracket realProjectiveLineInfinityVector
      realProjectiveLineOneVector = 1 := by
  simp [realProjectiveBracket, realProjectiveLineInfinityVector,
    realProjectiveLineOneVector]

theorem realProjectiveLineZero_ne_infinity :
    realProjectiveLineZero ≠ realProjectiveLineInfinity := by
  intro h
  have hbracket := (realProjective_mk_eq_mk_iff_bracket_eq_zero
    realProjectiveLineZeroVector_ne_zero
    realProjectiveLineInfinityVector_ne_zero).mp h
  norm_num at hbracket

theorem realProjectiveLineZero_ne_one :
    realProjectiveLineZero ≠ realProjectiveLineOne := by
  intro h
  have hbracket := (realProjective_mk_eq_mk_iff_bracket_eq_zero
    realProjectiveLineZeroVector_ne_zero
    realProjectiveLineOneVector_ne_zero).mp h
  norm_num at hbracket

theorem realProjectiveLineInfinity_ne_one :
    realProjectiveLineInfinity ≠ realProjectiveLineOne := by
  intro h
  have hbracket := (realProjective_mk_eq_mk_iff_bracket_eq_zero
    realProjectiveLineInfinityVector_ne_zero
    realProjectiveLineOneVector_ne_zero).mp h
  norm_num at hbracket

end Erdos506.Incidence
