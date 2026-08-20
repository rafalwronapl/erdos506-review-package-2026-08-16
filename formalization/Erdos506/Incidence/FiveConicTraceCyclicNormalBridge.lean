import Erdos506.Incidence.FiveConicCyclicNormalForm

/-!
# Actual five-trace to cyclic normal parameters

This is the lossless adapter from the five labelled points of an actual
proper-circle trace to the normal parameter chart used by the one-single
separator.  The label order is the intrinsic cyclic enumeration already
constructed for the trace; no affine chart is chosen at the configuration
boundary.
-/

namespace Erdos506.Incidence

open Erdos506.V3
open Erdos506.V4
open scoped LinearAlgebra.Projectivization

universe u

/-- The intrinsic projective parameter of the `i`-th cyclicly labelled point
of an actual five-trace. -/
noncomputable def fiveConicCyclicParameter
    {α : Type u} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (Gamma : DeterminedCircle cfg)
    (hGamma : (circleTrace cfg Gamma.1).card = 5) (i : Fin 5) :
    RealProjectiveOnePoint :=
  fiveConicTraceParameter cfg Gamma
    (fiveConicCyclicLabel cfg Gamma hGamma i)

/-- Cyclic trace parameters remain injectively labelled. -/
theorem fiveConicCyclicParameter_injective
    {α : Type u} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (Gamma : DeterminedCircle cfg)
    (hGamma : (circleTrace cfg Gamma.1).card = 5) :
    Function.Injective (fiveConicCyclicParameter cfg Gamma hGamma) := by
  exact (fiveConicTraceParameter_injective cfg Gamma).comp
    (fiveConicCyclicLabel cfg Gamma hGamma).injective

/-- The cyclic parameter still maps to its original concrete trace point. -/
theorem properCircleProjectiveParam_fiveConicCyclicParameter
    {α : Type u} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (Gamma : DeterminedCircle cfg)
    (hGamma : (circleTrace cfg Gamma.1).card = 5) (i : Fin 5) :
    properCircleProjectiveParam Gamma.1
      (fiveConicCyclicParameter cfg Gamma hGamma i) =
        cfg (fiveConicCyclicLabel cfg Gamma hGamma i).1 := by
  exact properCircleProjectiveParam_fiveConicTraceParameter cfg Gamma
    (fiveConicCyclicLabel cfg Gamma hGamma i)

/-- The finite cyclic labels are exactly the intrinsic cyclic order of the
actual proper-circle parameters. -/
theorem fiveConicCyclicParameter_cyclic_iff_sbtw
    {α : Type u} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (Gamma : DeterminedCircle cfg)
    (hGamma : (circleTrace cfg Gamma.1).card = 5)
    (i j k : Fin 5) :
    RealProjectiveCyclic
      (fiveConicCyclicParameter cfg Gamma hGamma i)
      (fiveConicCyclicParameter cfg Gamma hGamma j)
      (fiveConicCyclicParameter cfg Gamma hGamma k) ↔ sbtw i j k := by
  exact fiveConicCyclicLabel_parameter_sbtw_iff cfg Gamma hGamma i j k

/-- Every actual labelled five-trace has a concrete orientation-preserving
normal parameter chart `∞,0,1,λ,t` with `1 < λ < t`.  The displayed five
equalities are literal projective actions on the actual trace parameters. -/
theorem exists_fiveConicTraceCyclic_normal_form
    {α : Type u} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (Gamma : DeterminedCircle cfg)
    (hGamma : (circleTrace cfg Gamma.1).card = 5) :
    ∃ (g : GL (Fin 2) ℝ) (lam t : ℝ),
      0 < (g : Matrix (Fin 2) (Fin 2) ℝ).det ∧ 1 < lam ∧ lam < t ∧
        g • fiveConicCyclicParameter cfg Gamma hGamma 0 =
            realProjectiveLineInfinity ∧
          g • fiveConicCyclicParameter cfg Gamma hGamma 1 =
              realProjectiveLineZero ∧
            g • fiveConicCyclicParameter cfg Gamma hGamma 2 =
                realProjectiveLineOne ∧
              g • fiveConicCyclicParameter cfg Gamma hGamma 3 =
                  fiveConicAffinePoint lam ∧
                g • fiveConicCyclicParameter cfg Gamma hGamma 4 =
                    fiveConicAffinePoint t := by
  let P : Fin 5 → RealProjectiveOnePoint :=
    fiveConicCyclicParameter cfg Gamma hGamma
  have hPinj : Function.Injective P := by
    simpa [P] using fiveConicCyclicParameter_injective cfg Gamma hGamma
  have h10 : P 1 ≠ P 0 := hPinj.ne (by decide)
  have h12 : P 1 ≠ P 2 := hPinj.ne (by decide)
  have h20 : P 2 ≠ P 0 := hPinj.ne (by decide)
  have h30 : P 3 ≠ P 0 := hPinj.ne (by decide)
  have h40 : P 4 ≠ P 0 := hPinj.ne (by decide)
  have h012 : sbtw (0 : Fin 5) 1 2 := by
    rw [Fin.sbtw_iff]
    omega
  have h230 : sbtw (2 : Fin 5) 3 0 := by
    rw [Fin.sbtw_iff]
    omega
  have h340 : sbtw (3 : Fin 5) 4 0 := by
    rw [Fin.sbtw_iff]
    omega
  have hc012 : RealProjectiveCyclic (P 0) (P 1) (P 2) := by
    simpa [P] using
      (fiveConicCyclicParameter_cyclic_iff_sbtw cfg Gamma hGamma 0 1 2).mpr
        h012
  have hc230 : RealProjectiveCyclic (P 2) (P 3) (P 0) := by
    simpa [P] using
      (fiveConicCyclicParameter_cyclic_iff_sbtw cfg Gamma hGamma 2 3 0).mpr
        h230
  have hc340 : RealProjectiveCyclic (P 3) (P 4) (P 0) := by
    simpa [P] using
      (fiveConicCyclicParameter_cyclic_iff_sbtw cfg Gamma hGamma 3 4 0).mpr
        h340
  obtain ⟨lam, t, hlam, hlt, hInf, hZero, hOne, hLam, hT⟩ :=
    exists_fiveConicCyclic_normal_form
      (P 0) (P 1) (P 2) (P 3) (P 4)
      h10 h12 h20 h30 h40 hc012 hc230 hc340
  let g : GL (Fin 2) ℝ := fiveConicCyclicNormalFrame (P 0) (P 1) (P 2)
    h10 h12 h20
  have hgdet : 0 < (g : Matrix (Fin 2) (Fin 2) ℝ).det := by
    simpa [g] using fiveConicCyclicNormalFrame_det_pos
      (P 0) (P 1) (P 2) h10 h12 h20 hc012
  refine ⟨g, lam, t, hgdet, hlam, hlt, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [P, g] using hInf
  · simpa [P, g] using hZero
  · simpa [P, g] using hOne
  · simpa [P, g] using hLam
  · simpa [P, g] using hT

end Erdos506.Incidence
