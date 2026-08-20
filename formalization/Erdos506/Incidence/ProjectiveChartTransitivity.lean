import Erdos506.Incidence.ProjectiveCompletion
import Erdos506.Incidence.ProjectiveCoordinates
import Mathlib.LinearAlgebra.Projectivization.Action

/-!
# Moving a projective point to a standard affine-chart point

The general linear group acts transitively on real projective space.  This
module records the small concrete specialization needed when choosing a
projective chart: an arbitrary point can be moved to `[0 : 0 : 1]`.  It also
extracts the corresponding equality of homogeneous representatives with a
nonzero real scale.
-/

namespace Erdos506.Incidence

open Matrix
open scoped LinearAlgebra.Projectivization

noncomputable section

/-- The standard homogeneous representative `[0 : 0 : 1]` used for the
origin of the affine chart. -/
def projectiveChartOriginVector : Homogeneous3 :=
  ![0, 0, 1]

/-- The standard chart-origin representative is nonzero. -/
theorem projectiveChartOriginVector_ne_zero :
    projectiveChartOriginVector ≠ 0 := by
  simp [projectiveChartOriginVector]

/-- The projective point `[0 : 0 : 1]`. -/
def projectiveChartOrigin : RealProjectivePoint :=
  Projectivization.mk ℝ projectiveChartOriginVector
    projectiveChartOriginVector_ne_zero

/-- Every point of the real projective plane can be moved to `[0 : 0 : 1]`
by a general linear transformation. -/
theorem exists_generalLinearGroup_smul_eq_projectiveChartOrigin
    (P : RealProjectivePoint) :
    ∃ G : LinearMap.GeneralLinearGroup ℝ Homogeneous3,
      G • P = projectiveChartOrigin := by
  letI : MulAction.IsPretransitive
      (LinearMap.GeneralLinearGroup ℝ Homogeneous3) RealProjectivePoint :=
    MulAction.isPretransitive_of_is_two_pretransitive
  exact MulAction.exists_smul_eq
    (LinearMap.GeneralLinearGroup ℝ Homogeneous3) P projectiveChartOrigin

/-- A projective equality with `[0 : 0 : 1]` gives a literal equality of
representatives.  The scalar is nonzero because `mk_eq_mk_iff` produces a
unit. -/
theorem exists_rep_scale_of_smul_eq_projectiveChartOrigin
    {P : RealProjectivePoint}
    {G : LinearMap.GeneralLinearGroup ℝ Homogeneous3}
    (hG : G • P = projectiveChartOrigin) :
    ∃ c : ℝ, c ≠ 0 ∧
      G • P.rep = c • projectiveChartOriginVector := by
  have hmk :
      Projectivization.mk ℝ (G • P.rep)
          ((smul_ne_zero_iff_ne G).mpr P.rep_nonzero) =
        Projectivization.mk ℝ projectiveChartOriginVector
          projectiveChartOriginVector_ne_zero := by
    calc
      Projectivization.mk ℝ (G • P.rep)
          ((smul_ne_zero_iff_ne G).mpr P.rep_nonzero) =
          G • Projectivization.mk ℝ P.rep P.rep_nonzero :=
        (Projectivization.smul_mk G P.rep_nonzero).symm
      _ = G • P := by rw [Projectivization.mk_rep]
      _ = projectiveChartOrigin := hG
      _ = Projectivization.mk ℝ projectiveChartOriginVector
          projectiveChartOriginVector_ne_zero := rfl
  obtain ⟨c, hc⟩ := (Projectivization.mk_eq_mk_iff ℝ _ _ _ _).mp hmk
  refine ⟨(c : ℝ), Units.ne_zero c, ?_⟩
  simpa only [Units.smul_def] using hc.symm

/-- Bundled chart-normalization interface: it returns the projective
transformation together with the nonzero scale relating the chosen
representatives. -/
theorem exists_generalLinearGroup_smul_rep_eq_projectiveChartOrigin
    (P : RealProjectivePoint) :
    ∃ (G : LinearMap.GeneralLinearGroup ℝ Homogeneous3) (c : ℝ),
      c ≠ 0 ∧ G • P = projectiveChartOrigin ∧
        G • P.rep = c • projectiveChartOriginVector := by
  obtain ⟨G, hG⟩ :=
    exists_generalLinearGroup_smul_eq_projectiveChartOrigin P
  obtain ⟨c, hc, hrep⟩ :=
    exists_rep_scale_of_smul_eq_projectiveChartOrigin hG
  exact ⟨G, c, hc, hG, hrep⟩

end

end Erdos506.Incidence
