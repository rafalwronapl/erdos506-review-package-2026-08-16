import Erdos506.Incidence.ProjectiveRepresentativeIncidence

/-!
# Three projective points on one covector trace

The projective five-conic separator is calculated with raw homogeneous
determinants.  Actual page arguments, on the other hand, naturally produce
three incidences with one projective covector.  This small bridge converts
the latter into the former without choosing an affine chart or a scale for
any of the points.
-/

namespace Erdos506.Incidence

open Matrix
open scoped LinearAlgebra.Projectivization

/-- Three homogeneous vectors annihilated by one nonzero covector are
linearly dependent. -/
theorem homogeneous_det_eq_zero_of_common_covector
    (u v w ell : Homogeneous3) (hell : ell ≠ 0)
    (hu : u ⬝ᵥ ell = 0) (hv : v ⬝ᵥ ell = 0) (hw : w ⬝ᵥ ell = 0) :
    Matrix.det ![u, v, w] = 0 := by
  by_cases h0 : ell 0 = 0
  · by_cases h1 : ell 1 = 0
    · have h2 : ell 2 ≠ 0 := by
        intro h2
        apply hell
        ext k
        fin_cases k <;> simp [h0, h1, h2]
      have hu2 : u 2 = 0 := by
        simp only [dotProduct, Fin.sum_univ_three, h0, h1,
          mul_zero, zero_mul, zero_add, add_zero] at hu
        exact (mul_eq_zero.mp hu).resolve_right h2
      have hv2 : v 2 = 0 := by
        simp only [dotProduct, Fin.sum_univ_three, h0, h1,
          mul_zero, zero_mul, zero_add, add_zero] at hv
        exact (mul_eq_zero.mp hv).resolve_right h2
      have hw2 : w 2 = 0 := by
        simp only [dotProduct, Fin.sum_univ_three, h0, h1,
          mul_zero, zero_mul, zero_add, add_zero] at hw
        exact (mul_eq_zero.mp hw).resolve_right h2
      simp [Matrix.det_fin_three, hu2, hv2, hw2]
    · have hu1 : u 1 = -(u 2 * ell 2) / ell 1 := by
        simp only [dotProduct, Fin.sum_univ_three, h0,
          mul_zero, zero_mul, zero_add, add_zero] at hu
        field_simp [h1]
        linarith
      have hv1 : v 1 = -(v 2 * ell 2) / ell 1 := by
        simp only [dotProduct, Fin.sum_univ_three, h0,
          mul_zero, zero_mul, zero_add, add_zero] at hv
        field_simp [h1]
        linarith
      have hw1 : w 1 = -(w 2 * ell 2) / ell 1 := by
        simp only [dotProduct, Fin.sum_univ_three, h0,
          mul_zero, zero_mul, zero_add, add_zero] at hw
        field_simp [h1]
        linarith
      have hdet : Matrix.det ![u, v, w] =
          u 0 * v 1 * w 2 - u 0 * v 2 * w 1 -
            u 1 * v 0 * w 2 + u 1 * v 2 * w 0 +
              u 2 * v 0 * w 1 - u 2 * v 1 * w 0 := by
        simp [Matrix.det_fin_three]
      rw [hdet, hu1, hv1, hw1]
      field_simp [h1]
      ring
  · have hu0 : u 0 =
        -(u 1 * ell 1 + u 2 * ell 2) / ell 0 := by
      simp only [dotProduct, Fin.sum_univ_three] at hu
      field_simp [h0]
      linarith
    have hv0 : v 0 =
        -(v 1 * ell 1 + v 2 * ell 2) / ell 0 := by
      simp only [dotProduct, Fin.sum_univ_three] at hv
      field_simp [h0]
      linarith
    have hw0 : w 0 =
        -(w 1 * ell 1 + w 2 * ell 2) / ell 0 := by
      simp only [dotProduct, Fin.sum_univ_three] at hw
      field_simp [h0]
      linarith
    have hdet : Matrix.det ![u, v, w] =
        u 0 * v 1 * w 2 - u 0 * v 2 * w 1 -
          u 1 * v 0 * w 2 + u 1 * v 2 * w 0 +
            u 2 * v 0 * w 1 - u 2 * v 1 * w 0 := by
      simp [Matrix.det_fin_three]
    rw [hdet, hu0, hv0, hw0]
    field_simp [h0]
    ring

/-- If three projective points lie on one projective covector, the
determinant of their canonical representatives vanishes. -/
theorem det_rep_eq_zero_of_three_projective_orthogonal
    (U V W ell : RealProjectivePlane)
    (hU : Projectivization.orthogonal U ell)
    (hV : Projectivization.orthogonal V ell)
    (hW : Projectivization.orthogonal W ell) :
    Matrix.det ![U.rep, V.rep, W.rep] = 0 := by
  have hUraw := hU
  have hVraw := hV
  have hWraw := hW
  rw [← Projectivization.mk_rep U,
    ← Projectivization.mk_rep ell] at hUraw
  rw [← Projectivization.mk_rep V,
    ← Projectivization.mk_rep ell] at hVraw
  rw [← Projectivization.mk_rep W,
    ← Projectivization.mk_rep ell] at hWraw
  exact homogeneous_det_eq_zero_of_common_covector
    U.rep V.rep W.rep ell.rep ell.rep_nonzero
    ((Projectivization.orthogonal_mk U.rep_nonzero ell.rep_nonzero).mp hUraw)
    ((Projectivization.orthogonal_mk V.rep_nonzero ell.rep_nonzero).mp hVraw)
    ((Projectivization.orthogonal_mk W.rep_nonzero ell.rep_nonzero).mp hWraw)

end Erdos506.Incidence
