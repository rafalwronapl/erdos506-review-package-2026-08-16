import Erdos506.Incidence.CompleteQuadrangle
import Erdos506.Incidence.GoldenAxisProjective
import Erdos506.Incidence.RadicalAxisFourFourGeometry

/-!
# Reusable projective cores of five-conic trace rigidity

This file records the two coordinate-free geometric endpoints shared by the
`C = 39` and `C = 40` five-conic routers.

* The first is the all-double-triangle part of K2.1: the three diagonal
  centres of four distinct points of a proper real circle cannot lie on one
  trace line.
* The second exposes the already verified golden-axis determinant endpoint
  in an argument form rather than as a positive certificate.  It is the
  projective end of the K2.4 tangent-separation branch.

Both results are ordinary theorems over actual real-circle / homogeneous
incidence data.  They do not add a geometric principle or a configuration
certificate.
-/

namespace Erdos506.Incidence

open Erdos506.V4
open Matrix
open scoped LinearAlgebra.Projectivization

/-- Four pairwise distinct affine points of one proper real circle form a
projective complete quadrangle. -/
theorem properCircle_four_points_completeQuadrangleGeneralPosition
    (Gamma : ProperCircle) {a b c d : Point2}
    (ha : a ∈ (Gamma.1 : Set Point2))
    (hb : b ∈ (Gamma.1 : Set Point2))
    (hc : c ∈ (Gamma.1 : Set Point2))
    (hd : d ∈ (Gamma.1 : Set Point2))
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    CompleteQuadrangleGeneralPosition
      (homogeneousLift a) (homogeneousLift b)
      (homogeneousLift c) (homogeneousLift d) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact homogeneousLift_det_ne_zero_of_mem_properCircle
      Gamma ha hb hc hab hac hbc
  · exact homogeneousLift_det_ne_zero_of_mem_properCircle
      Gamma ha hb hd hab had hbd
  · exact homogeneousLift_det_ne_zero_of_mem_properCircle
      Gamma ha hc hd hac had hcd
  · exact homogeneousLift_det_ne_zero_of_mem_properCircle
      Gamma hb hc hd hbc hbd hcd

/-- K2.1, all-double-triangle clause: if four selected points lie on one
proper circle, no nonzero projective trace covector can contain all three
diagonal centres of their complete quadrangle. -/
theorem properCircle_allDoubleTriangle_trace_absurd
    (Gamma : ProperCircle) {a b c d : Point2}
    (ha : a ∈ (Gamma.1 : Set Point2))
    (hb : b ∈ (Gamma.1 : Set Point2))
    (hc : c ∈ (Gamma.1 : Set Point2))
    (hd : d ∈ (Gamma.1 : Set Point2))
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    (ell : Homogeneous3) (hell : ell ≠ 0)
    (hAB : diagonalAB_CD (homogeneousLift a) (homogeneousLift b)
      (homogeneousLift c) (homogeneousLift d) ⬝ᵥ ell = 0)
    (hAC : diagonalAC_BD (homogeneousLift a) (homogeneousLift b)
      (homogeneousLift c) (homogeneousLift d) ⬝ᵥ ell = 0)
    (hAD : diagonalAD_BC (homogeneousLift a) (homogeneousLift b)
      (homogeneousLift c) (homogeneousLift d) ⬝ᵥ ell = 0) : False := by
  exact completeQuadrangle_no_common_nonzero_covector
    (properCircle_four_points_completeQuadrangleGeneralPosition
      Gamma ha hb hc hd hab hac had hbc hbd hcd)
    hell hAB hAC hAD

/-- The raw projective K2.4 endpoint.  Five general-position conic points,
four chord-pair centres on one axis, and either of the two residual concurrent
three-line patterns are algebraically incompatible over `ℝ`.

The hypotheses are determinant incidences themselves; callers can construct
them from actual traces without introducing a normal-form assumption. -/
theorem fiveConic_goldenAxis_tangentSeparation_absurd
    (g : Fin 5 → Homogeneous3) (q : Fin 4 → Homogeneous3)
    (hgeneral : HomogeneousFiveGeneralPosition g)
    (hqzero : ∀ i, q i ≠ 0)
    (hcentres : GoldenAxisCenterIncidence g q)
    (haxis : GoldenAxisCollinear q)
    (hconcurrency : GoldenAxisEndConcurrent g q ∨
      GoldenAxisMiddleConcurrent g q) : False := by
  exact GoldenAxisProjectiveInput.not_realizable {
    toGoldenAxisProjectiveCore := {
      g := g
      q := q
      g_generalPosition := hgeneral
      q_ne_zero := hqzero
      centerIncidence := hcentres
      axisCollinear := haxis }
    concurrency := hconcurrency }

end Erdos506.Incidence
