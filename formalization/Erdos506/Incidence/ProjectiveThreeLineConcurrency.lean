import Erdos506.Incidence.RadicalAxisFourFourGeometry
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv

/-!
# Three-line concurrency in homogeneous coordinates

For three projective line covectors, vanishing of the row determinant is
exactly the existence of a nonzero homogeneous point annihilated by all
three covectors.  The statement deliberately uses representatives rather
than a projectivization quotient, which makes it directly usable with the
finite support/incidence API.
-/

namespace Erdos506.Incidence

open Matrix

/-- A nonzero homogeneous representative of the common projective point of
three line covectors. -/
def ThreeLineCommonPoint (ell₀ ell₁ ell₂ : Homogeneous3) : Prop :=
  ∃ representative : Homogeneous3, representative ≠ 0 ∧
    ell₀ ⬝ᵥ representative = 0 ∧ ell₁ ⬝ᵥ representative = 0 ∧
      ell₂ ⬝ᵥ representative = 0

/-- Three homogeneous covectors are linearly dependent exactly when they
have a nonzero common projective point.  The three displayed dot products
are simply the coordinates of the row matrix applied to that point. -/
theorem det_eq_zero_iff_threeLineCommonPoint
    (ell₀ ell₁ ell₂ : Homogeneous3) :
    Matrix.det ![ell₀, ell₁, ell₂] = 0 ↔
      ThreeLineCommonPoint ell₀ ell₁ ell₂ := by
  let M : Matrix (Fin 3) (Fin 3) ℝ := ![ell₀, ell₁, ell₂]
  constructor
  · intro hdet
    obtain ⟨r, hrne, hr⟩ :=
      Matrix.exists_mulVec_eq_zero_iff.mpr (by simpa [M] using hdet)
    refine ⟨r, hrne, ?_, ?_, ?_⟩
    · have hrow := congrFun hr (0 : Fin 3)
      simpa [M, Matrix.mulVec, dotProduct] using hrow
    · have hrow := congrFun hr (1 : Fin 3)
      simpa [M, Matrix.mulVec, dotProduct] using hrow
    · have hrow := congrFun hr (2 : Fin 3)
      simpa [M, Matrix.mulVec, dotProduct] using hrow
  · rintro ⟨r, hrne, h₀, h₁, h₂⟩
    apply Matrix.exists_mulVec_eq_zero_iff.mp
    refine ⟨r, hrne, ?_⟩
    ext i
    fin_cases i
    · simpa [M, Matrix.mulVec, dotProduct] using h₀
    · simpa [M, Matrix.mulVec, dotProduct] using h₁
    · simpa [M, Matrix.mulVec, dotProduct] using h₂

/-- A convenient expanded form of the preceding equivalence. -/
theorem det_eq_zero_iff_exists_common_nonzero_homogeneous
    (ell₀ ell₁ ell₂ : Homogeneous3) :
    Matrix.det ![ell₀, ell₁, ell₂] = 0 ↔
      ∃ r : Homogeneous3, r ≠ 0 ∧
        ell₀ ⬝ᵥ r = 0 ∧ ell₁ ⬝ᵥ r = 0 ∧ ell₂ ⬝ᵥ r = 0 := by
  constructor
  · intro h
    exact (det_eq_zero_iff_threeLineCommonPoint ell₀ ell₁ ell₂).mp h
  · rintro ⟨r, hr, h₀, h₁, h₂⟩
    exact (det_eq_zero_iff_threeLineCommonPoint ell₀ ell₁ ell₂).mpr
      ⟨r, hr, h₀, h₁, h₂⟩

/-- Two distinct projective line covectors have at most one common
projective point.  The conclusion is phrased on nonzero representatives,
which is the form needed to compare a determinant-kernel witness to an
actual selected affine intersection. -/
theorem projectiveCommonPoint_eq_of_two_distinct_covectors
    {ell₀ ell₁ r x : Homogeneous3}
    (hell₀ : ell₀ ≠ 0) (hell₁ : ell₁ ≠ 0)
    (hr : r ≠ 0) (hx : x ≠ 0)
    (hline : Projectivization.mk ℝ ell₀ hell₀ ≠
      Projectivization.mk ℝ ell₁ hell₁)
    (hr₀ : ell₀ ⬝ᵥ r = 0) (hr₁ : ell₁ ⬝ᵥ r = 0)
    (hx₀ : ell₀ ⬝ᵥ x = 0) (hx₁ : ell₁ ⬝ᵥ x = 0) :
    Projectivization.mk ℝ r hr = Projectivization.mk ℝ x hx := by
  let L₀ : RealProjectivePlane := Projectivization.mk ℝ ell₀ hell₀
  let L₁ : RealProjectivePlane := Projectivization.mk ℝ ell₁ hell₁
  let R : RealProjectivePlane := Projectivization.mk ℝ r hr
  let X : RealProjectivePlane := Projectivization.mk ℝ x hx
  have hR₀ : Projectivization.orthogonal L₀ R := by
    exact (Projectivization.orthogonal_mk hell₀ hr).mpr hr₀
  have hR₁ : Projectivization.orthogonal L₁ R := by
    exact (Projectivization.orthogonal_mk hell₁ hr).mpr hr₁
  have hX₀ : Projectivization.orthogonal L₀ X := by
    exact (Projectivization.orthogonal_mk hell₀ hx).mpr hx₀
  have hX₁ : Projectivization.orthogonal L₁ X := by
    exact (Projectivization.orthogonal_mk hell₁ hx).mpr hx₁
  change R = X
  calc
    R = Projectivization.cross L₀ L₁ :=
      projectiveCovector_eq_cross_of_orthogonal hline hR₀ hR₁
    _ = X :=
      (projectiveCovector_eq_cross_of_orthogonal hline hX₀ hX₁).symm

end Erdos506.Incidence
