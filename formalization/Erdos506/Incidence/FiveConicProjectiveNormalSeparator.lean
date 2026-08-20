import Erdos506.Incidence.FiveConicNormalSeparatorTransport
import Erdos506.Incidence.ProjectiveRepresentativeThreeCollinearity

/-!
# Projective-incidence form of the transported normal separator

This is the direct interface between a geometric page trace and the normal
five-conic calculation.  Its hypotheses are three literal incidences with
one projective covector.  No projective chart, scale, or normal-form
assumption is exposed to callers.
-/

namespace Erdos506.Incidence

open Erdos506.V4
open Matrix
open scoped LinearAlgebra.Projectivization

/-- The transported fifth normal conic point, retained as a projective point
so that actual page traces can be stated by ordinary orthogonality. -/
noncomputable def fiveConicTransportedNormalPoint
    (c : ProperCircle) (g : GL (Fin 2) ℝ) (t : ℝ) : RealProjectivePlane :=
  Projectivization.mk ℝ
    (fiveConicProjectiveTransport c g • fiveConicNormalPoint t)
    ((smul_ne_zero_iff_ne (fiveConicProjectiveTransport c g)).mpr
      (fiveConicNormalPoint_ne_zero t))

/-- The transported `i`-th normal complete-quadrangle diagonal point. -/
noncomputable def fiveConicTransportedNormalDiagonal
    (c : ProperCircle) (g : GL (Fin 2) ℝ) (lam : ℝ)
    (hlam : 1 < lam) (i : Fin 3) : RealProjectivePlane :=
  Projectivization.mk ℝ
    (fiveConicProjectiveTransport c g • fiveConicNormalDiagonal lam i)
    ((smul_ne_zero_iff_ne (fiveConicProjectiveTransport c g)).mpr
      (fiveConicNormalDiagonal_ne_zero hlam i))

/-- If a projective trace contains the transported fifth normal point and
two distinct transported diagonal centres, then those centres are exactly
the `0,1` pair of the normal separator. -/
theorem fiveConicTransportedNormal_collinear_diagonal_pair_eq_zero_one
    (c : ProperCircle) (g : GL (Fin 2) ℝ) {lam t : ℝ}
    (hlam : 1 < lam) (ht : lam < t)
    (i j : Fin 3) (hij : i ≠ j) (ell : RealProjectivePlane)
    (hpoint : Projectivization.orthogonal
      (fiveConicTransportedNormalPoint c g t) ell)
    (hi : Projectivization.orthogonal
      (fiveConicTransportedNormalDiagonal c g lam hlam i) ell)
    (hj : Projectivization.orthogonal
      (fiveConicTransportedNormalDiagonal c g lam hlam j) ell) :
    (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0) := by
  have hpointRaw :
      (fiveConicProjectiveTransport c g • fiveConicNormalPoint t) ⬝ᵥ
          ell.rep = 0 := by
    have h := hpoint
    rw [← Projectivization.mk_rep ell] at h
    exact (Projectivization.orthogonal_mk
      ((smul_ne_zero_iff_ne (fiveConicProjectiveTransport c g)).mpr
        (fiveConicNormalPoint_ne_zero t)) ell.rep_nonzero).mp
      (by simpa [fiveConicTransportedNormalPoint] using h)
  have hiRaw :
      (fiveConicProjectiveTransport c g • fiveConicNormalDiagonal lam i) ⬝ᵥ
          ell.rep = 0 := by
    have h := hi
    rw [← Projectivization.mk_rep ell] at h
    exact (Projectivization.orthogonal_mk
      ((smul_ne_zero_iff_ne (fiveConicProjectiveTransport c g)).mpr
        (fiveConicNormalDiagonal_ne_zero hlam i)) ell.rep_nonzero).mp
      (by simpa [fiveConicTransportedNormalDiagonal] using h)
  have hjRaw :
      (fiveConicProjectiveTransport c g • fiveConicNormalDiagonal lam j) ⬝ᵥ
          ell.rep = 0 := by
    have h := hj
    rw [← Projectivization.mk_rep ell] at h
    exact (Projectivization.orthogonal_mk
      ((smul_ne_zero_iff_ne (fiveConicProjectiveTransport c g)).mpr
        (fiveConicNormalDiagonal_ne_zero hlam j)) ell.rep_nonzero).mp
      (by simpa [fiveConicTransportedNormalDiagonal] using h)
  have hdet : Matrix.det ![
      fiveConicProjectiveTransport c g • fiveConicNormalPoint t,
      fiveConicProjectiveTransport c g • fiveConicNormalDiagonal lam i,
      fiveConicProjectiveTransport c g • fiveConicNormalDiagonal lam j] = 0 :=
    homogeneous_det_eq_zero_of_common_covector _ _ _ ell.rep ell.rep_nonzero
      hpointRaw hiRaw hjRaw
  exact fiveConicProjectiveTransport_collinear_diagonal_pair_eq_zero_one
    c g hlam ht i j hij hdet

end Erdos506.Incidence
