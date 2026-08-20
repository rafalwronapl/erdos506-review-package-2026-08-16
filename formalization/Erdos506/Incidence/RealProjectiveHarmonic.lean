import Erdos506.Incidence.RealProjectiveLineFrame

/-!
# Harmonic four-tuples on the real projective line

This is a small projective interface.  Harmonicity is stated directly in
homogeneous brackets, so it is independent of chosen representatives and is
transported by every real projectivity.
-/

namespace Erdos506.Incidence

open Matrix
open scoped LinearAlgebra.Projectivization

/-- An ordered harmonic four-tuple on `RP¹`, expressed using homogeneous
representatives.  The equation is the cross-ratio condition `(P,Q;R,S)=-1`. -/
def RealProjectiveHarmonic
    (P Q R S : RealProjectiveOnePoint) : Prop :=
  ∃ (p q r s : RealProjectiveLineVector)
      (hp : p ≠ 0) (hq : q ≠ 0) (hr : r ≠ 0) (hs : s ≠ 0),
    P = Projectivization.mk ℝ p hp ∧
    Q = Projectivization.mk ℝ q hq ∧
    R = Projectivization.mk ℝ r hr ∧
    S = Projectivization.mk ℝ s hs ∧
    realProjectiveBracket p r * realProjectiveBracket q s +
      realProjectiveBracket p s * realProjectiveBracket q r = 0

/-- Concrete homogeneous representatives certify harmonicity. -/
theorem realProjectiveHarmonic_mk
    {p q r s : RealProjectiveLineVector}
    (hp : p ≠ 0) (hq : q ≠ 0) (hr : r ≠ 0) (hs : s ≠ 0)
    (hharmonic :
      realProjectiveBracket p r * realProjectiveBracket q s +
        realProjectiveBracket p s * realProjectiveBracket q r = 0) :
    RealProjectiveHarmonic
      (Projectivization.mk ℝ p hp) (Projectivization.mk ℝ q hq)
      (Projectivization.mk ℝ r hr) (Projectivization.mk ℝ s hs) := by
  exact ⟨p, q, r, s, hp, hq, hr, hs, rfl, rfl, rfl, rfl, hharmonic⟩

/-- Harmonicity is invariant under the standard `GL₂(ℝ)` action. -/
theorem realProjectiveHarmonic_gl_smul
    (g : GL (Fin 2) ℝ) {P Q R S : RealProjectiveOnePoint}
    (hharmonic : RealProjectiveHarmonic P Q R S) :
    RealProjectiveHarmonic (g • P) (g • Q) (g • R) (g • S) := by
  rcases hharmonic with
    ⟨p, q, r, s, hp, hq, hr, hs, hP, hQ, hR, hS, hbracket⟩
  let hp' : g • p ≠ 0 := (smul_ne_zero_iff_ne g).mpr hp
  let hq' : g • q ≠ 0 := (smul_ne_zero_iff_ne g).mpr hq
  let hr' : g • r ≠ 0 := (smul_ne_zero_iff_ne g).mpr hr
  let hs' : g • s ≠ 0 := (smul_ne_zero_iff_ne g).mpr hs
  refine ⟨g • p, g • q, g • r, g • s, hp', hq', hr', hs', ?_, ?_, ?_, ?_, ?_⟩
  · calc
      g • P = g • Projectivization.mk ℝ p hp :=
        congrArg (fun T : RealProjectiveOnePoint => g • T) hP
      _ = Projectivization.mk ℝ (g • p) hp' := by simp
  · calc
      g • Q = g • Projectivization.mk ℝ q hq :=
        congrArg (fun T : RealProjectiveOnePoint => g • T) hQ
      _ = Projectivization.mk ℝ (g • q) hq' := by simp
  · calc
      g • R = g • Projectivization.mk ℝ r hr :=
        congrArg (fun T : RealProjectiveOnePoint => g • T) hR
      _ = Projectivization.mk ℝ (g • r) hr' := by simp
  · calc
      g • S = g • Projectivization.mk ℝ s hs :=
        congrArg (fun T : RealProjectiveOnePoint => g • T) hS
      _ = Projectivization.mk ℝ (g • s) hs' := by simp
  · simp only [realProjectiveBracket_gl_smul]
    calc
      (g : Matrix (Fin 2) (Fin 2) ℝ).det * realProjectiveBracket p r *
          ((g : Matrix (Fin 2) (Fin 2) ℝ).det * realProjectiveBracket q s) +
        (g : Matrix (Fin 2) (Fin 2) ℝ).det * realProjectiveBracket p s *
          ((g : Matrix (Fin 2) (Fin 2) ℝ).det * realProjectiveBracket q r) =
          (g : Matrix (Fin 2) (Fin 2) ℝ).det ^ 2 *
            (realProjectiveBracket p r * realProjectiveBracket q s +
              realProjectiveBracket p s * realProjectiveBracket q r) := by ring
      _ = 0 := by rw [hbracket]; ring

/-- Pairwise distinctness of an ordered four-tuple. -/
def RealProjectiveFourDistinct
    (P Q R S : RealProjectiveOnePoint) : Prop :=
  P ≠ Q ∧ P ≠ R ∧ P ≠ S ∧ Q ≠ R ∧ Q ≠ S ∧ R ≠ S

/-- The order-free predicate saying that a four-element finite set admits a
harmonic ordering. -/
noncomputable def IsRealProjectiveHarmonicFour
    (T : Finset RealProjectiveOnePoint) : Prop := by
  classical
  exact T.card = 4 ∧ ∃ P Q R S : RealProjectiveOnePoint,
    ({P, Q, R, S} : Finset RealProjectiveOnePoint) = T ∧
    RealProjectiveFourDistinct P Q R S ∧
    RealProjectiveHarmonic P Q R S

/-- The standard frame exhibits the basic harmonic quadruple
`(0, ∞; 1, -1)` at the level of homogeneous brackets. -/
theorem realProjectiveHarmonic_standard_frame
    (minusOne : RealProjectiveLineVector) (hminusOne : minusOne ≠ 0)
    (hzero : realProjectiveBracket realProjectiveLineZeroVector minusOne = 1)
    (hinfinity : realProjectiveBracket realProjectiveLineInfinityVector minusOne = 1) :
    RealProjectiveHarmonic realProjectiveLineZero
      realProjectiveLineInfinity realProjectiveLineOne
      (Projectivization.mk ℝ minusOne hminusOne) := by
  apply realProjectiveHarmonic_mk
    realProjectiveLineZeroVector_ne_zero
    realProjectiveLineInfinityVector_ne_zero
    realProjectiveLineOneVector_ne_zero hminusOne
  rw [realProjectiveBracket_zero_one, hzero,
    realProjectiveBracket_infinity_one, hinfinity]
  norm_num

end Erdos506.Incidence
