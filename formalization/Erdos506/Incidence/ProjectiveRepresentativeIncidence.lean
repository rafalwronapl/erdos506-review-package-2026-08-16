import Erdos506.Incidence.ProjectiveFiveFrame
import Erdos506.Incidence.RadicalAxisFourFourGeometry

/-!
# Determinants of projective representatives

Small raw-vector bridges used by the V1 golden-axis construction.
-/

namespace Erdos506.Incidence

open Matrix
open scoped LinearAlgebra.Projectivization

/-- Projective orthogonality becomes a determinant equation after choosing
affine representatives for the two points and the canonical representative
of the projective covector. -/
theorem det_homogeneousLift_homogeneousLift_rep_eq_zero_of_orthogonal
    {p q : Erdos506.V4.Point2} (hpq : p ≠ q) {Q : RealProjectivePlane}
    (horth : Projectivization.orthogonal Q
      (projectiveLine p q hpq)) :
    Matrix.det ![homogeneousLift p, homogeneousLift q, Q.rep] = 0 := by
  have hline :
      Projectivization.orthogonal Q
        (Projectivization.mk ℝ (lineCovector p q)
          (lineCovector_ne_zero hpq)) := by
    simpa only [projectiveLine] using horth
  rw [Projectivization.orthogonal_comm] at hline
  have hraw : lineCovector p q ⬝ᵥ Q.rep = 0 := by
    rw [← Projectivization.mk_rep Q] at hline
    exact (Projectivization.orthogonal_mk
      (lineCovector_ne_zero hpq) Q.rep_nonzero).mp hline
  calc
    Matrix.det ![homogeneousLift p, homogeneousLift q, Q.rep] =
        homogeneousLift p ⬝ᵥ
          crossProduct (homogeneousLift q) Q.rep := by
      exact (triple_product_eq_det _ _ _).symm
    _ = homogeneousLift q ⬝ᵥ
          crossProduct Q.rep (homogeneousLift p) :=
      triple_product_permutation _ _ _
    _ = Q.rep ⬝ᵥ lineCovector p q := by
      rw [lineCovector]
      exact triple_product_permutation _ _ _
    _ = lineCovector p q ⬝ᵥ Q.rep := dotProduct_comm _ _
    _ = 0 := hraw

end Erdos506.Incidence
