import Erdos506.Incidence.FiveConicCyclicProjectiveTransport

/-!
# Rooting a cyclic five-trace at a selected mark

For the one-single page law the selected trace mark is arbitrary.  This file
constructively re-roots the intrinsic cyclic five-labelling so that the
chosen mark becomes normal index `4`; the other four marks then occur as
`0,1,2,3` in cyclic order.  The finite rotation facts are checked directly
on `Fin 5` and carry no geometric assumption.
-/

namespace Erdos506.Incidence

open Erdos506.V3
open Erdos506.V4
open scoped LinearAlgebra.Projectivization

universe u

/-- Cyclicly enumerate a five-set starting immediately after `r`, with `r`
itself placed at final index `4`. -/
def fiveConicRootedCyclicIndex (r : Fin 5) : Fin 5 → Fin 5 :=
  ![finRotate 5 r,
    finRotate 5 (finRotate 5 r),
    finRotate 5 (finRotate 5 (finRotate 5 r)),
    finRotate 5 (finRotate 5 (finRotate 5 (finRotate 5 r))),
    r]

theorem fiveConicRootedCyclicIndex_injective (r : Fin 5) :
    Function.Injective (fiveConicRootedCyclicIndex r) := by
  fin_cases r <;> decide +kernel

/-- The rooted cyclic enumeration is a permutation of the five finite
indices.  Packaging it as an equivalence lets the finite chord transport use
the standard `kFiveChordEquivOfVertexLabel` API. -/
noncomputable def fiveConicRootedCyclicPerm (r : Fin 5) : Equiv.Perm (Fin 5) :=
  Equiv.ofBijective (fiveConicRootedCyclicIndex r)
    ⟨fiveConicRootedCyclicIndex_injective r,
      Finite.surjective_of_injective
        (fiveConicRootedCyclicIndex_injective r)⟩

@[simp] theorem fiveConicRootedCyclicPerm_apply (r i : Fin 5) :
    fiveConicRootedCyclicPerm r i = fiveConicRootedCyclicIndex r i :=
  rfl

@[simp] theorem fiveConicRootedCyclicIndex_four (r : Fin 5) :
    fiveConicRootedCyclicIndex r 4 = r := by
  fin_cases r <;> rfl

theorem fiveConicRootedCyclicIndex_one_ne_zero (r : Fin 5) :
    fiveConicRootedCyclicIndex r 1 ≠ fiveConicRootedCyclicIndex r 0 := by
  fin_cases r <;> decide +kernel

theorem fiveConicRootedCyclicIndex_one_ne_two (r : Fin 5) :
    fiveConicRootedCyclicIndex r 1 ≠ fiveConicRootedCyclicIndex r 2 := by
  fin_cases r <;> decide +kernel

theorem fiveConicRootedCyclicIndex_two_ne_zero (r : Fin 5) :
    fiveConicRootedCyclicIndex r 2 ≠ fiveConicRootedCyclicIndex r 0 := by
  fin_cases r <;> decide +kernel

theorem fiveConicRootedCyclicIndex_three_ne_zero (r : Fin 5) :
    fiveConicRootedCyclicIndex r 3 ≠ fiveConicRootedCyclicIndex r 0 := by
  fin_cases r <;> decide +kernel

theorem fiveConicRootedCyclicIndex_four_ne_zero (r : Fin 5) :
    fiveConicRootedCyclicIndex r 4 ≠ fiveConicRootedCyclicIndex r 0 := by
  fin_cases r <;> decide +kernel

theorem fiveConicRootedCyclicIndex_sbtw_zero_one_two (r : Fin 5) :
    sbtw (fiveConicRootedCyclicIndex r 0)
      (fiveConicRootedCyclicIndex r 1)
      (fiveConicRootedCyclicIndex r 2) := by
  fin_cases r <;> rw [Fin.sbtw_iff] <;> decide +kernel

theorem fiveConicRootedCyclicIndex_sbtw_two_three_zero (r : Fin 5) :
    sbtw (fiveConicRootedCyclicIndex r 2)
      (fiveConicRootedCyclicIndex r 3)
      (fiveConicRootedCyclicIndex r 0) := by
  fin_cases r <;> rw [Fin.sbtw_iff] <;> decide +kernel

theorem fiveConicRootedCyclicIndex_sbtw_three_four_zero (r : Fin 5) :
    sbtw (fiveConicRootedCyclicIndex r 3)
      (fiveConicRootedCyclicIndex r 4)
      (fiveConicRootedCyclicIndex r 0) := by
  fin_cases r <;> rw [Fin.sbtw_iff] <;> decide +kernel

/-- The projective parameter at rooted cyclic index `k`. -/
noncomputable def fiveConicRootedCyclicParameter
    {α : Type u} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (Gamma : DeterminedCircle cfg)
    (hGamma : (circleTrace cfg Gamma.1).card = 5)
    (r k : Fin 5) : RealProjectiveOnePoint :=
  fiveConicCyclicParameter cfg Gamma hGamma
    (fiveConicRootedCyclicIndex r k)

/-- The actual trace labelling associated with the rooted cyclic order. -/
noncomputable def fiveConicRootedCyclicLabel
    {α : Type u} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (Gamma : DeterminedCircle cfg)
    (hGamma : (circleTrace cfg Gamma.1).card = 5) (r : Fin 5) :
    Fin 5 ≃ {x : α // x ∈ circleTrace cfg Gamma.1} :=
  (fiveConicRootedCyclicPerm r).trans
    (fiveConicCyclicLabel cfg Gamma hGamma)

@[simp] theorem fiveConicRootedCyclicLabel_apply
    {α : Type u} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (Gamma : DeterminedCircle cfg)
    (hGamma : (circleTrace cfg Gamma.1).card = 5)
    (r i : Fin 5) :
    fiveConicRootedCyclicLabel cfg Gamma hGamma r i =
      fiveConicCyclicLabel cfg Gamma hGamma
        (fiveConicRootedCyclicIndex r i) :=
  rfl

@[simp] theorem fiveConicRootedCyclicLabel_four
    {α : Type u} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (Gamma : DeterminedCircle cfg)
    (hGamma : (circleTrace cfg Gamma.1).card = 5)
    (r : Fin 5) :
    fiveConicRootedCyclicLabel cfg Gamma hGamma r 4 =
      fiveConicCyclicLabel cfg Gamma hGamma r := by
  simp

@[simp] theorem fiveConicRootedCyclicParameter_eq_traceParameter_label
    {α : Type u} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (Gamma : DeterminedCircle cfg)
    (hGamma : (circleTrace cfg Gamma.1).card = 5)
    (r i : Fin 5) :
    fiveConicRootedCyclicParameter cfg Gamma hGamma r i =
      fiveConicTraceParameter cfg Gamma
        (fiveConicRootedCyclicLabel cfg Gamma hGamma r i) :=
  rfl

theorem fiveConicRootedCyclicLabel_ne
    {α : Type u} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (Gamma : DeterminedCircle cfg)
    (hGamma : (circleTrace cfg Gamma.1).card = 5)
    (r i j : Fin 5) (hij : i ≠ j) :
    (fiveConicRootedCyclicLabel cfg Gamma hGamma r i).1 ≠
      (fiveConicRootedCyclicLabel cfg Gamma hGamma r j).1 := by
  intro h
  apply hij
  apply (fiveConicRootedCyclicLabel cfg Gamma hGamma r).injective
  exact Subtype.ext h

@[simp] theorem properCircleProjectiveParam_fiveConicRootedCyclicParameter
    {α : Type u} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (Gamma : DeterminedCircle cfg)
    (hGamma : (circleTrace cfg Gamma.1).card = 5)
    (r i : Fin 5) :
    properCircleProjectiveParam Gamma.1
      (fiveConicRootedCyclicParameter cfg Gamma hGamma r i) =
        cfg (fiveConicRootedCyclicLabel cfg Gamma hGamma r i).1 := by
  rw [fiveConicRootedCyclicParameter_eq_traceParameter_label]
  exact properCircleProjectiveParam_fiveConicTraceParameter cfg Gamma
    (fiveConicRootedCyclicLabel cfg Gamma hGamma r i)

theorem fiveConicRootedCyclicParameter_injective
    {α : Type u} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (Gamma : DeterminedCircle cfg)
    (hGamma : (circleTrace cfg Gamma.1).card = 5) (r : Fin 5) :
    Function.Injective (fiveConicRootedCyclicParameter cfg Gamma hGamma r) := by
  exact (fiveConicCyclicParameter_injective cfg Gamma hGamma).comp
    (fiveConicRootedCyclicIndex_injective r)

private theorem fiveConicRootedCyclicParameter_cyclic_zero_one_two
    {α : Type u} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (Gamma : DeterminedCircle cfg)
    (hGamma : (circleTrace cfg Gamma.1).card = 5) (r : Fin 5) :
    RealProjectiveCyclic
      (fiveConicRootedCyclicParameter cfg Gamma hGamma r 0)
      (fiveConicRootedCyclicParameter cfg Gamma hGamma r 1)
      (fiveConicRootedCyclicParameter cfg Gamma hGamma r 2) := by
  simpa [fiveConicRootedCyclicParameter] using
    (fiveConicCyclicParameter_cyclic_iff_sbtw cfg Gamma hGamma
      (fiveConicRootedCyclicIndex r 0)
      (fiveConicRootedCyclicIndex r 1)
      (fiveConicRootedCyclicIndex r 2)).mpr
      (fiveConicRootedCyclicIndex_sbtw_zero_one_two r)

private theorem fiveConicRootedCyclicParameter_cyclic_two_three_zero
    {α : Type u} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (Gamma : DeterminedCircle cfg)
    (hGamma : (circleTrace cfg Gamma.1).card = 5) (r : Fin 5) :
    RealProjectiveCyclic
      (fiveConicRootedCyclicParameter cfg Gamma hGamma r 2)
      (fiveConicRootedCyclicParameter cfg Gamma hGamma r 3)
      (fiveConicRootedCyclicParameter cfg Gamma hGamma r 0) := by
  simpa [fiveConicRootedCyclicParameter] using
    (fiveConicCyclicParameter_cyclic_iff_sbtw cfg Gamma hGamma
      (fiveConicRootedCyclicIndex r 2)
      (fiveConicRootedCyclicIndex r 3)
      (fiveConicRootedCyclicIndex r 0)).mpr
      (fiveConicRootedCyclicIndex_sbtw_two_three_zero r)

private theorem fiveConicRootedCyclicParameter_cyclic_three_four_zero
    {α : Type u} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (Gamma : DeterminedCircle cfg)
    (hGamma : (circleTrace cfg Gamma.1).card = 5) (r : Fin 5) :
    RealProjectiveCyclic
      (fiveConicRootedCyclicParameter cfg Gamma hGamma r 3)
      (fiveConicRootedCyclicParameter cfg Gamma hGamma r 4)
      (fiveConicRootedCyclicParameter cfg Gamma hGamma r 0) := by
  simpa [fiveConicRootedCyclicParameter] using
    (fiveConicCyclicParameter_cyclic_iff_sbtw cfg Gamma hGamma
      (fiveConicRootedCyclicIndex r 3)
      (fiveConicRootedCyclicIndex r 4)
      (fiveConicRootedCyclicIndex r 0)).mpr
      (fiveConicRootedCyclicIndex_sbtw_three_four_zero r)

/-- Constructively normalize a cyclic five-trace with an arbitrary chosen
mark at final normal index `4`. -/
theorem exists_fiveConicTraceRootedCyclic_normal_form
    {α : Type u} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (Gamma : DeterminedCircle cfg)
    (hGamma : (circleTrace cfg Gamma.1).card = 5) (r : Fin 5) :
    ∃ (g : GL (Fin 2) ℝ) (lam t : ℝ),
      0 < (g : Matrix (Fin 2) (Fin 2) ℝ).det ∧ 1 < lam ∧ lam < t ∧
        g • fiveConicRootedCyclicParameter cfg Gamma hGamma r 0 =
            realProjectiveLineInfinity ∧
          g • fiveConicRootedCyclicParameter cfg Gamma hGamma r 1 =
              realProjectiveLineZero ∧
            g • fiveConicRootedCyclicParameter cfg Gamma hGamma r 2 =
                realProjectiveLineOne ∧
              g • fiveConicRootedCyclicParameter cfg Gamma hGamma r 3 =
                  fiveConicAffinePoint lam ∧
                g • fiveConicRootedCyclicParameter cfg Gamma hGamma r 4 =
                    fiveConicAffinePoint t := by
  let P : Fin 5 → RealProjectiveOnePoint :=
    fiveConicRootedCyclicParameter cfg Gamma hGamma r
  have hPinj : Function.Injective P := by
    simpa [P] using
      fiveConicRootedCyclicParameter_injective cfg Gamma hGamma r
  have h10 : P 1 ≠ P 0 := hPinj.ne (by decide)
  have h12 : P 1 ≠ P 2 := hPinj.ne (by decide)
  have h20 : P 2 ≠ P 0 := hPinj.ne (by decide)
  have h30 : P 3 ≠ P 0 := hPinj.ne (by decide)
  have h40 : P 4 ≠ P 0 := hPinj.ne (by decide)
  have hbase : RealProjectiveCyclic (P 0) (P 1) (P 2) := by
    simpa [P] using
      fiveConicRootedCyclicParameter_cyclic_zero_one_two cfg Gamma hGamma r
  have hlamCyclic : RealProjectiveCyclic (P 2) (P 3) (P 0) := by
    simpa [P] using
      fiveConicRootedCyclicParameter_cyclic_two_three_zero cfg Gamma hGamma r
  have htCyclic : RealProjectiveCyclic (P 3) (P 4) (P 0) := by
    simpa [P] using
      fiveConicRootedCyclicParameter_cyclic_three_four_zero cfg Gamma hGamma r
  obtain ⟨lam, t, hlam, hlt, hInf, hZero, hOne, hLam, hT⟩ :=
    exists_fiveConicCyclic_normal_form
      (P 0) (P 1) (P 2) (P 3) (P 4)
      h10 h12 h20 h30 h40 hbase hlamCyclic htCyclic
  let g : GL (Fin 2) ℝ := fiveConicCyclicNormalFrame (P 0) (P 1) (P 2)
    h10 h12 h20
  have hgdet : 0 < (g : Matrix (Fin 2) (Fin 2) ℝ).det := by
    simpa [g] using fiveConicCyclicNormalFrame_det_pos
      (P 0) (P 1) (P 2) h10 h12 h20 hbase
  refine ⟨g, lam, t, hgdet, hlam, hlt, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [P, g] using hInf
  · simpa [P, g] using hZero
  · simpa [P, g] using hOne
  · simpa [P, g] using hLam
  · simpa [P, g] using hT

/-- The rooted cyclic normalizer also gives literal projective-plane
equalities for all five actual trace points. -/
theorem exists_fiveConicTraceRootedCyclic_projective_normal_form
    {α : Type u} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (Gamma : DeterminedCircle cfg)
    (hGamma : (circleTrace cfg Gamma.1).card = 5) (r : Fin 5) :
    ∃ (g : GL (Fin 2) ℝ) (lam t : ℝ),
      0 < (g : Matrix (Fin 2) (Fin 2) ℝ).det ∧ 1 < lam ∧ lam < t ∧
        fiveConicTransportedNormalInfinity Gamma.1 g⁻¹ =
          properCircleVeronesePoint Gamma.1
            (fiveConicRootedCyclicParameter cfg Gamma hGamma r 0) ∧
          fiveConicTransportedNormalPoint Gamma.1 g⁻¹ 0 =
            properCircleVeronesePoint Gamma.1
              (fiveConicRootedCyclicParameter cfg Gamma hGamma r 1) ∧
            fiveConicTransportedNormalPoint Gamma.1 g⁻¹ 1 =
              properCircleVeronesePoint Gamma.1
                (fiveConicRootedCyclicParameter cfg Gamma hGamma r 2) ∧
              fiveConicTransportedNormalPoint Gamma.1 g⁻¹ lam =
                properCircleVeronesePoint Gamma.1
                  (fiveConicRootedCyclicParameter cfg Gamma hGamma r 3) ∧
                fiveConicTransportedNormalPoint Gamma.1 g⁻¹ t =
                  properCircleVeronesePoint Gamma.1
                    (fiveConicRootedCyclicParameter cfg Gamma hGamma r 4) := by
  obtain ⟨g, lam, t, hgdet, hlam, hlt, h0, h1, h2, h3, h4⟩ :=
    exists_fiveConicTraceRootedCyclic_normal_form cfg Gamma hGamma r
  refine ⟨g, lam, t, hgdet, hlam, hlt, ?_, ?_, ?_, ?_, ?_⟩
  · exact fiveConicTransportedNormalInfinity_eq_veronese_of_smul_eq
      Gamma.1 g (fiveConicRootedCyclicParameter cfg Gamma hGamma r 0) h0
  · exact fiveConicTransportedNormalPoint_eq_veronese_of_smul_eq_affine
      Gamma.1 g (fiveConicRootedCyclicParameter cfg Gamma hGamma r 1) 0 h1
  · exact fiveConicTransportedNormalPoint_eq_veronese_of_smul_eq_affine
      Gamma.1 g (fiveConicRootedCyclicParameter cfg Gamma hGamma r 2) 1 h2
  · exact fiveConicTransportedNormalPoint_eq_veronese_of_smul_eq_affine
      Gamma.1 g (fiveConicRootedCyclicParameter cfg Gamma hGamma r 3) lam h3
  · exact fiveConicTransportedNormalPoint_eq_veronese_of_smul_eq_affine
      Gamma.1 g (fiveConicRootedCyclicParameter cfg Gamma hGamma r 4) t h4

/-- The normal diagonal separator rooted at any chosen actual trace mark.
This is the projective K2.1 core in the exact form used by a one-single page:
the selected mark is index `4`, while the two double directions are two
diagonal centres of its four-point complement. -/
theorem exists_fiveConicTraceRootedCyclic_projective_separator
    {α : Type u} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (Gamma : DeterminedCircle cfg)
    (hGamma : (circleTrace cfg Gamma.1).card = 5) (r : Fin 5) :
    ∃ (g : GL (Fin 2) ℝ) (lam t : ℝ)
      (hlam : 1 < lam) (hlt : lam < t),
      0 < (g : Matrix (Fin 2) (Fin 2) ℝ).det ∧
        fiveConicTransportedNormalPoint Gamma.1 g⁻¹ t =
          properCircleVeronesePoint Gamma.1
            (fiveConicRootedCyclicParameter cfg Gamma hGamma r 4) ∧
          ∀ (i j : Fin 3) (ell : RealProjectivePlane), i ≠ j →
            Projectivization.orthogonal
              (properCircleVeronesePoint Gamma.1
                (fiveConicRootedCyclicParameter cfg Gamma hGamma r 4)) ell →
            Projectivization.orthogonal
              (fiveConicTransportedNormalDiagonal Gamma.1 g⁻¹ lam hlam i) ell →
            Projectivization.orthogonal
              (fiveConicTransportedNormalDiagonal Gamma.1 g⁻¹ lam hlam j) ell →
              (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0) := by
  obtain ⟨g, lam, t, hgdet, hlam, hlt, _h0, _h1, _h2, _h3, h4⟩ :=
    exists_fiveConicTraceRootedCyclic_projective_normal_form
      cfg Gamma hGamma r
  refine ⟨g, lam, t, hlam, hlt, hgdet, h4, ?_⟩
  intro i j ell hij hpoint hi hj
  apply fiveConicTransportedNormal_collinear_diagonal_pair_eq_zero_one
    Gamma.1 g⁻¹ hlam hlt i j hij ell
  · rw [h4]
    exact hpoint
  · exact hi
  · exact hj

end Erdos506.Incidence
