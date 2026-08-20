import Erdos506.Incidence.FiveConicTraceCyclicNormalBridge
import Erdos506.Incidence.FiveConicProjectiveNormalSeparator

/-!
# Literal projective transport of a cyclic five-trace

The cyclic normal frame lives on the parameter line.  Here it is coupled to
the explicit binary-Veronese `GL₃` transport, yielding literal equalities of
projective plane points for all five marked points of an actual proper-circle
trace.
-/

namespace Erdos506.Incidence

open Erdos506.V3
open Erdos506.V4
open scoped LinearAlgebra.Projectivization

universe u

/-- The image of the normal infinite conic point under the concrete
proper-circle/projective-parameter transport. -/
noncomputable def fiveConicTransportedNormalInfinity
    (c : ProperCircle) (g : GL (Fin 2) ℝ) : RealProjectivePlane :=
  Projectivization.mk ℝ
    (fiveConicProjectiveTransport c g • fiveConicNormalInfinity)
    ((smul_ne_zero_iff_ne (fiveConicProjectiveTransport c g)).mpr
      fiveConicNormalInfinity_ne_zero)

/-- The transported finite normal point is literally the Veronese point of
the transported projective parameter. -/
theorem fiveConicTransportedNormalPoint_eq_properCircleVeronesePoint
    (c : ProperCircle) (g : GL (Fin 2) ℝ) (t : ℝ) :
    fiveConicTransportedNormalPoint c g t =
      properCircleVeronesePoint c (g • fiveConicAffinePoint t) := by
  unfold fiveConicTransportedNormalPoint fiveConicAffinePoint
  rw [Projectivization.smul_mk, properCircleVeronesePoint_mk]
  apply (Projectivization.mk_eq_mk_iff' ℝ _ _ _ _).mpr
  refine ⟨1, ?_⟩
  simpa using (fiveConicProjectiveTransport_normalPoint c g t).symm

/-- The analogous literal equality at the normal parameter infinity. -/
theorem fiveConicTransportedNormalInfinity_eq_properCircleVeronesePoint
    (c : ProperCircle) (g : GL (Fin 2) ℝ) :
    fiveConicTransportedNormalInfinity c g =
      properCircleVeronesePoint c (g • realProjectiveLineInfinity) := by
  unfold fiveConicTransportedNormalInfinity realProjectiveLineInfinity
  rw [Projectivization.smul_mk, properCircleVeronesePoint_mk]
  apply (Projectivization.mk_eq_mk_iff' ℝ _ _ _ _).mpr
  refine ⟨1, ?_⟩
  simpa using (fiveConicProjectiveTransport_normalInfinity c g).symm

/-- Inverting a parameter normalizer identifies an actual finite parameter
with the transported normal representative. -/
theorem fiveConicTransportedNormalPoint_eq_veronese_of_smul_eq_affine
    (c : ProperCircle) (g : GL (Fin 2) ℝ) (P : RealProjectiveOnePoint)
    (t : ℝ) (hP : g • P = fiveConicAffinePoint t) :
    fiveConicTransportedNormalPoint c g⁻¹ t =
      properCircleVeronesePoint c P := by
  calc
    fiveConicTransportedNormalPoint c g⁻¹ t =
        properCircleVeronesePoint c
          (g⁻¹ • fiveConicAffinePoint t) :=
      fiveConicTransportedNormalPoint_eq_properCircleVeronesePoint c g⁻¹ t
    _ = properCircleVeronesePoint c (g⁻¹ • (g • P)) := by rw [hP]
    _ = properCircleVeronesePoint c P := by rw [inv_smul_smul]

/-- The same inverse-normalizer identification at infinity. -/
theorem fiveConicTransportedNormalInfinity_eq_veronese_of_smul_eq
    (c : ProperCircle) (g : GL (Fin 2) ℝ) (P : RealProjectiveOnePoint)
    (hP : g • P = realProjectiveLineInfinity) :
    fiveConicTransportedNormalInfinity c g⁻¹ =
      properCircleVeronesePoint c P := by
  calc
    fiveConicTransportedNormalInfinity c g⁻¹ =
        properCircleVeronesePoint c
          (g⁻¹ • realProjectiveLineInfinity) :=
      fiveConicTransportedNormalInfinity_eq_properCircleVeronesePoint c g⁻¹
    _ = properCircleVeronesePoint c (g⁻¹ • (g • P)) := by rw [hP]
    _ = properCircleVeronesePoint c P := by rw [inv_smul_smul]

/-- An actual five-point circle trace has a completely explicit normal
projective realization.  The inverse parameter frame is the one used by the
plane-side `fiveConicProjectiveTransport`; all five point equalities below
are actual projective-plane equalities. -/
theorem exists_fiveConicTraceCyclic_projective_normal_form
    {α : Type u} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (Gamma : DeterminedCircle cfg)
    (hGamma : (circleTrace cfg Gamma.1).card = 5) :
    ∃ (g : GL (Fin 2) ℝ) (lam t : ℝ),
      0 < (g : Matrix (Fin 2) (Fin 2) ℝ).det ∧ 1 < lam ∧ lam < t ∧
        fiveConicTransportedNormalInfinity Gamma.1 g⁻¹ =
          properCircleVeronesePoint Gamma.1
            (fiveConicCyclicParameter cfg Gamma hGamma 0) ∧
          fiveConicTransportedNormalPoint Gamma.1 g⁻¹ 0 =
            properCircleVeronesePoint Gamma.1
              (fiveConicCyclicParameter cfg Gamma hGamma 1) ∧
            fiveConicTransportedNormalPoint Gamma.1 g⁻¹ 1 =
              properCircleVeronesePoint Gamma.1
                (fiveConicCyclicParameter cfg Gamma hGamma 2) ∧
              fiveConicTransportedNormalPoint Gamma.1 g⁻¹ lam =
                properCircleVeronesePoint Gamma.1
                  (fiveConicCyclicParameter cfg Gamma hGamma 3) ∧
                fiveConicTransportedNormalPoint Gamma.1 g⁻¹ t =
                  properCircleVeronesePoint Gamma.1
                    (fiveConicCyclicParameter cfg Gamma hGamma 4) := by
  obtain ⟨g, lam, t, hgdet, hlam, hlt, h0, h1, h2, h3, h4⟩ :=
    exists_fiveConicTraceCyclic_normal_form cfg Gamma hGamma
  refine ⟨g, lam, t, hgdet, hlam, hlt, ?_, ?_, ?_, ?_, ?_⟩
  · exact fiveConicTransportedNormalInfinity_eq_veronese_of_smul_eq
      Gamma.1 g (fiveConicCyclicParameter cfg Gamma hGamma 0) h0
  · exact fiveConicTransportedNormalPoint_eq_veronese_of_smul_eq_affine
      Gamma.1 g (fiveConicCyclicParameter cfg Gamma hGamma 1) 0 h1
  · exact fiveConicTransportedNormalPoint_eq_veronese_of_smul_eq_affine
      Gamma.1 g (fiveConicCyclicParameter cfg Gamma hGamma 2) 1 h2
  · exact fiveConicTransportedNormalPoint_eq_veronese_of_smul_eq_affine
      Gamma.1 g (fiveConicCyclicParameter cfg Gamma hGamma 3) lam h3
  · exact fiveConicTransportedNormalPoint_eq_veronese_of_smul_eq_affine
      Gamma.1 g (fiveConicCyclicParameter cfg Gamma hGamma 4) t h4

/-- The normal separator expressed directly on an actual cyclic five-trace.
The fifth marked trace point and the two diagonal centres are all literal
projective points.  Thus a page argument need only provide its three actual
incidences with one trace covector. -/
theorem exists_fiveConicTraceCyclic_projective_separator
    {α : Type u} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (Gamma : DeterminedCircle cfg)
    (hGamma : (circleTrace cfg Gamma.1).card = 5) :
    ∃ (g : GL (Fin 2) ℝ) (lam t : ℝ)
      (hlam : 1 < lam) (hlt : lam < t),
      0 < (g : Matrix (Fin 2) (Fin 2) ℝ).det ∧
        fiveConicTransportedNormalPoint Gamma.1 g⁻¹ t =
          properCircleVeronesePoint Gamma.1
            (fiveConicCyclicParameter cfg Gamma hGamma 4) ∧
          ∀ (i j : Fin 3) (ell : RealProjectivePlane), i ≠ j →
            Projectivization.orthogonal
              (properCircleVeronesePoint Gamma.1
                (fiveConicCyclicParameter cfg Gamma hGamma 4)) ell →
              Projectivization.orthogonal
              (fiveConicTransportedNormalDiagonal Gamma.1 g⁻¹ lam hlam i) ell →
            Projectivization.orthogonal
              (fiveConicTransportedNormalDiagonal Gamma.1 g⁻¹ lam hlam j) ell →
              (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0) := by
  obtain ⟨g, lam, t, hgdet, hlam, hlt, _h0, _h1, _h2, _h3, h4⟩ :=
    exists_fiveConicTraceCyclic_projective_normal_form cfg Gamma hGamma
  refine ⟨g, lam, t, hlam, hlt, hgdet, h4, ?_⟩
  intro i j ell hij hpoint hi hj
  apply fiveConicTransportedNormal_collinear_diagonal_pair_eq_zero_one
    Gamma.1 g⁻¹ hlam hlt i j hij ell
  · rw [h4]
    exact hpoint
  · exact hi
  · exact hj

end Erdos506.Incidence
