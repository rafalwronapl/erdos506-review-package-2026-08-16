import Erdos506.Incidence.ProjectiveFiveFrame
import Erdos506.Incidence.CompleteQuadrangle

/-!
# A four-covector frame in the real projective plane

The four-star link is naturally described by four projective *lines*, hence
by homogeneous covectors.  This interface records their standard complete
quadrangle normal form and the contragredient action on line covectors.
The existence of a frame is kept as explicit data: this avoids silently
assuming a fifth point in general position merely to reuse a five-point
normalizer.
-/

namespace Erdos506.Incidence

open Matrix

/-- The standard four covectors of a projective complete quadrangle. -/
def projectiveCovectorNormalLine : Fin 4 → Homogeneous3 :=
  ![![1, 0, 0], ![0, 1, 0], ![0, 0, 1], ![1, 1, 1]]

/-- A projective normalization of four line covectors to the standard
complete-quadrangle frame.  The action on covectors is contragredient to the
usual action on homogeneous point vectors. -/
structure ProjectiveCovectorFrame (ell : Fin 4 → Homogeneous3) where
  G : GL (Fin 3) ℝ
  scale : Fin 4 → ℝ
  scale_ne_zero : ∀ i, scale i ≠ 0
  map_covector : ∀ i,
    ((G⁻¹ : GL (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ)ᵀ *ᵥ ell i =
      scale i • projectiveCovectorNormalLine i

/-- The contragredient action of a projectivity on a line covector. -/
def projectiveCovectorTransform (G : GL (Fin 3) ℝ)
    (ell : Homogeneous3) : Homogeneous3 :=
  ((G⁻¹ : GL (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ)ᵀ *ᵥ ell

/-- A point transforms by the standard left matrix action. -/
def projectivePointTransform (G : GL (Fin 3) ℝ)
    (p : Homogeneous3) : Homogeneous3 :=
  G • p

/-- The contragredient action preserves point--line incidence exactly. -/
theorem projectiveCovectorTransform_dot_pointTransform
    (G : GL (Fin 3) ℝ) (ell p : Homogeneous3) :
    projectiveCovectorTransform G ell ⬝ᵥ projectivePointTransform G p =
      ell ⬝ᵥ p := by
  change
    (((((G⁻¹ : GL (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ)ᵀ) *ᵥ ell) ⬝ᵥ
      ((G : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ p)) = ell ⬝ᵥ p
  calc
    (((((G⁻¹ : GL (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ)ᵀ) *ᵥ ell) ⬝ᵥ
        ((G : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ p)) =
        ((G : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ p) ⬝ᵥ
          ((((G⁻¹ : GL (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ)ᵀ) *ᵥ ell) :=
      dotProduct_comm _ _
    _ = ell ⬝ᵥ (((G⁻¹ : GL (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ
        ((G : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ p)) :=
      Matrix.dotProduct_transpose_mulVec _ _ _
    _ = ell ⬝ᵥ
        ((((G⁻¹ : GL (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ) *
          (G : Matrix (Fin 3) (Fin 3) ℝ)) *ᵥ p) := by
      rw [Matrix.mulVec_mulVec]
    _ = ell ⬝ᵥ p := by simp

/-- Incidence transport in zero form. -/
theorem projectiveCovectorTransform_incident_iff
    (G : GL (Fin 3) ℝ) (ell p : Homogeneous3) :
    projectiveCovectorTransform G ell ⬝ᵥ projectivePointTransform G p = 0 ↔
      ell ⬝ᵥ p = 0 := by
  rw [projectiveCovectorTransform_dot_pointTransform]

/-- A four-covector frame transports every displayed incidence to the
standard frame, with only the harmless nonzero line scale remaining. -/
theorem projectiveCovectorFrame_incident_normal_iff
    {ell : Fin 4 → Homogeneous3} (F : ProjectiveCovectorFrame ell)
    (i : Fin 4) (p : Homogeneous3) :
    projectiveCovectorNormalLine i ⬝ᵥ projectivePointTransform F.G p = 0 ↔
      ell i ⬝ᵥ p = 0 := by
  have htransport := projectiveCovectorTransform_incident_iff F.G (ell i) p
  change projectiveCovectorNormalLine i ⬝ᵥ (F.G • p) = 0 ↔
    ell i ⬝ᵥ p = 0
  unfold projectiveCovectorTransform projectivePointTransform at htransport
  rw [F.map_covector i, smul_dotProduct, smul_eq_mul] at htransport
  simpa [mul_eq_zero, F.scale_ne_zero i] using htransport

/-! ## Construction of the four-covector frame -/

/-- Matrix whose columns are the first three covectors. -/
private def projectiveCovectorBasisMatrix
    (ell : Fin 4 → Homogeneous3) : Matrix (Fin 3) (Fin 3) ℝ :=
  (![ell 0, ell 1, ell 2] : Matrix (Fin 3) (Fin 3) ℝ)ᵀ

private theorem projectiveCovectorBasisMatrix_det
    (ell : Fin 4 → Homogeneous3) :
    Matrix.det (projectiveCovectorBasisMatrix ell) =
      Matrix.det ![ell 0, ell 1, ell 2] := by
  simp [projectiveCovectorBasisMatrix]

/-- Four line covectors in complete-quadrangle general position admit the
standard contragredient frame recorded by `ProjectiveCovectorFrame`. -/
noncomputable def projectiveCovectorFrame
    (ell : Fin 4 → Homogeneous3)
    (hgp : CompleteQuadrangleGeneralPosition
      (ell 0) (ell 1) (ell 2) (ell 3)) :
    ProjectiveCovectorFrame ell := by
  classical
  have hdet012 : Matrix.det ![ell 0, ell 1, ell 2] ≠ 0 := hgp.det_abc_ne
  have hCdet : Matrix.det (projectiveCovectorBasisMatrix ell) ≠ 0 := by
    rw [projectiveCovectorBasisMatrix_det]
    exact hdet012
  let C : GL (Fin 3) ℝ :=
    Matrix.GeneralLinearGroup.mkOfDetNeZero
      (projectiveCovectorBasisMatrix ell) hCdet
  let e0 : Homogeneous3 := ![1, 0, 0]
  let e1 : Homogeneous3 := ![0, 1, 0]
  let e2 : Homogeneous3 := ![0, 0, 1]
  have hC0 : C • e0 = ell 0 := by
    change projectiveCovectorBasisMatrix ell *ᵥ e0 = ell 0
    ext i
    fin_cases i <;>
      simp [projectiveCovectorBasisMatrix, e0, Matrix.mulVec,
        dotProduct, Fin.sum_univ_three]
  have hC1 : C • e1 = ell 1 := by
    change projectiveCovectorBasisMatrix ell *ᵥ e1 = ell 1
    ext i
    fin_cases i <;>
      simp [projectiveCovectorBasisMatrix, e1, Matrix.mulVec,
        dotProduct, Fin.sum_univ_three]
  have hC2 : C • e2 = ell 2 := by
    change projectiveCovectorBasisMatrix ell *ᵥ e2 = ell 2
    ext i
    fin_cases i <;>
      simp [projectiveCovectorBasisMatrix, e2, Matrix.mulVec,
        dotProduct, Fin.sum_univ_three]
  have hCi0 : C⁻¹ • ell 0 = e0 := by rw [← hC0]; simp
  have hCi1 : C⁻¹ • ell 1 = e1 := by rw [← hC1]; simp
  have hCi2 : C⁻¹ • ell 2 = e2 := by rw [← hC2]; simp
  let z : Homogeneous3 := C⁻¹ • ell 3
  have hz0 : z 0 ≠ 0 := by
    have htrans : Matrix.det ![C⁻¹ • ell 1, C⁻¹ • ell 2,
        C⁻¹ • ell 3] ≠ 0 := by
      intro hzero
      exact hgp.det_bcd_ne
        ((det_eq_zero_iff_generalLinear_smul_three
          C⁻¹ (ell 1) (ell 2) (ell 3)).mp hzero)
    rw [hCi1, hCi2] at htrans
    intro hz
    apply htrans
    simp [e1, e2, z, Matrix.det_fin_three, hz]
  have hz1 : z 1 ≠ 0 := by
    have htrans : Matrix.det ![C⁻¹ • ell 0, C⁻¹ • ell 2,
        C⁻¹ • ell 3] ≠ 0 := by
      intro hzero
      exact hgp.det_acd_ne
        ((det_eq_zero_iff_generalLinear_smul_three
          C⁻¹ (ell 0) (ell 2) (ell 3)).mp hzero)
    rw [hCi0, hCi2] at htrans
    intro hz
    apply htrans
    simp [e0, e2, z, Matrix.det_fin_three, hz]
  have hz2 : z 2 ≠ 0 := by
    have htrans : Matrix.det ![C⁻¹ • ell 0, C⁻¹ • ell 1,
        C⁻¹ • ell 3] ≠ 0 := by
      intro hzero
      exact hgp.det_abd_ne
        ((det_eq_zero_iff_generalLinear_smul_three
          C⁻¹ (ell 0) (ell 1) (ell 3)).mp hzero)
    rw [hCi0, hCi1] at htrans
    intro hz
    apply htrans
    simp [e0, e1, z, Matrix.det_fin_three, hz]
  let Dmatrix : Matrix (Fin 3) (Fin 3) ℝ :=
    Matrix.diagonal fun i => (z i)⁻¹
  have hDdet : Matrix.det Dmatrix ≠ 0 := by
    rw [show Matrix.det Dmatrix = ∏ i, (z i)⁻¹ by
      simp [Dmatrix, Matrix.det_diagonal]]
    rw [Fin.prod_univ_three]
    exact mul_ne_zero (mul_ne_zero (inv_ne_zero hz0) (inv_ne_zero hz1))
      (inv_ne_zero hz2)
  let D : GL (Fin 3) ℝ :=
    Matrix.GeneralLinearGroup.mkOfDetNeZero Dmatrix hDdet
  have hD0 : D • e0 = (z 0)⁻¹ • e0 := by
    change Dmatrix *ᵥ e0 = _
    ext i
    fin_cases i <;>
      simp [Dmatrix, e0, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  have hD1 : D • e1 = (z 1)⁻¹ • e1 := by
    change Dmatrix *ᵥ e1 = _
    ext i
    fin_cases i <;>
      simp [Dmatrix, e1, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  have hD2 : D • e2 = (z 2)⁻¹ • e2 := by
    change Dmatrix *ᵥ e2 = _
    ext i
    fin_cases i <;>
      simp [Dmatrix, e2, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  have hDz : D • z = ![1, 1, 1] := by
    change Dmatrix *ᵥ z = ![1, 1, 1]
    ext i
    fin_cases i <;>
      simp [Dmatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_three,
        hz0, hz1, hz2]
  let H : GL (Fin 3) ℝ := D * C⁻¹
  have hH0 : H • ell 0 = (z 0)⁻¹ • e0 := by
    change (D * C⁻¹) • ell 0 = _
    rw [mul_smul, hCi0, hD0]
  have hH1 : H • ell 1 = (z 1)⁻¹ • e1 := by
    change (D * C⁻¹) • ell 1 = _
    rw [mul_smul, hCi1, hD1]
  have hH2 : H • ell 2 = (z 2)⁻¹ • e2 := by
    change (D * C⁻¹) • ell 2 = _
    rw [mul_smul, hCi2, hD2]
  have hH3 : H • ell 3 = ![1, 1, 1] := by
    change (D * C⁻¹) • ell 3 = _
    rw [mul_smul]
    exact hDz
  have hGdet : Matrix.det
      (((H⁻¹ : GL (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ)ᵀ) ≠ 0 := by
    rw [Matrix.det_transpose]
    exact (Matrix.GeneralLinearGroup.det (H⁻¹)).ne_zero
  let G : GL (Fin 3) ℝ := Matrix.GeneralLinearGroup.mkOfDetNeZero
    (((H⁻¹ : GL (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ)ᵀ) hGdet
  have htransform :
      (((G⁻¹ : GL (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ)ᵀ) =
        (H : Matrix (Fin 3) (Fin 3) ℝ) := by
    rw [Matrix.GeneralLinearGroup.coe_inv]
    change ((((↑H⁻¹ : Matrix (Fin 3) (Fin 3) ℝ)ᵀ)⁻¹)ᵀ) =
      (H : Matrix (Fin 3) (Fin 3) ℝ)
    rw [Matrix.transpose_nonsing_inv, Matrix.transpose_transpose]
    rw [Matrix.GeneralLinearGroup.coe_inv]
    exact Matrix.nonsing_inv_nonsing_inv (H : Matrix (Fin 3) (Fin 3) ℝ)
      ((Matrix.GeneralLinearGroup.det H).isUnit)
  refine
    { G := G
      scale := ![(z 0)⁻¹, (z 1)⁻¹, (z 2)⁻¹, 1]
      scale_ne_zero := ?_
      map_covector := ?_ }
  · intro i
    fin_cases i <;> simp [hz0, hz1, hz2]
  · intro i
    rw [htransform]
    fin_cases i
    · simpa [projectiveCovectorNormalLine, e0] using hH0
    · simpa [projectiveCovectorNormalLine, e1] using hH1
    · simpa [projectiveCovectorNormalLine, e2] using hH2
    · simpa [projectiveCovectorNormalLine] using hH3

end Erdos506.Incidence
