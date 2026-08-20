import Erdos506.Incidence.ProjectiveCoordinates
import Mathlib.Data.Matrix.Action
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Basic
import Mathlib.LinearAlgebra.Matrix.Nondegenerate

/-!
# A projective frame for five points in general position

Five nonzero vectors in `ℝ³`, no three projectively collinear, may be sent by
one element of `GL₃(ℝ)` to

`e₀, e₁, e₂, (1,1,1), (a,b,1)`

up to five independent nonzero scalars.  This file keeps the construction at
the homogeneous-vector level.  It also records the determinant transport and
common-line lemmas used by the geometric applications of the frame.
-/

namespace Erdos506.Incidence

open Matrix
open scoped LinearAlgebra.Projectivization

/-- Five homogeneous vectors are in general position when each vector is
nonzero and every determinant on three distinct indices is nonzero. -/
def HomogeneousFiveGeneralPosition
    (g : Fin 5 → Homogeneous3) : Prop :=
  (∀ i, g i ≠ 0) ∧
    ∀ i j k, i ≠ j → i ≠ k → j ≠ k →
      Matrix.det ![g i, g j, g k] ≠ 0

/-- The standard two-parameter normal form for five projective points. -/
def projectiveFiveNormalPoint (a b : ℝ) : Fin 5 → Homogeneous3 :=
  ![![1, 0, 0], ![0, 1, 0], ![0, 0, 1], ![1, 1, 1], ![a, b, 1]]

/-- A concrete `GL₃` normalization of five homogeneous projective points. -/
structure ProjectiveFiveFrame (g : Fin 5 → Homogeneous3) where
  G : GL (Fin 3) ℝ
  scale : Fin 5 → ℝ
  scale_ne_zero : ∀ i, scale i ≠ 0
  a : ℝ
  b : ℝ
  map_point : ∀ i,
    G • g i = scale i • projectiveFiveNormalPoint a b i

/-! ## Determinant transport -/

/-- Applying one general linear transformation to three row vectors
multiplies their determinant by the determinant of the transformation. -/
theorem det_generalLinear_smul_three
    (G : GL (Fin 3) ℝ) (u v w : Homogeneous3) :
    Matrix.det ![G • u, G • v, G • w] =
      (↑(Matrix.GeneralLinearGroup.det G) : ℝ) *
        Matrix.det ![u, v, w] := by
  change Matrix.det
      ![((G : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ u),
        ((G : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ v),
        ((G : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ w)] =
    Matrix.det (G : Matrix (Fin 3) (Fin 3) ℝ) *
      Matrix.det ![u, v, w]
  simp [Matrix.det_fin_three, Matrix.mulVec, dotProduct,
    Fin.sum_univ_three]
  ring

/-- An invertible linear transformation preserves determinant vanishing. -/
theorem det_eq_zero_iff_generalLinear_smul_three
    (G : GL (Fin 3) ℝ) (u v w : Homogeneous3) :
    Matrix.det ![G • u, G • v, G • w] = 0 ↔
      Matrix.det ![u, v, w] = 0 := by
  rw [det_generalLinear_smul_three]
  constructor
  · intro hzero
    exact (mul_eq_zero.mp hzero).resolve_left
      (Matrix.GeneralLinearGroup.det G).ne_zero
  · intro hzero
    rw [hzero, mul_zero]

private theorem det_smul_three
    (a b c : ℝ) (u v w : Homogeneous3) :
    Matrix.det ![a • u, b • v, c • w] =
      (a * b * c) * Matrix.det ![u, v, w] := by
  simp [Matrix.det_fin_three]
  ring

/-- Vanishing of the determinant of three projective representatives is
independent of the three nonzero representatives chosen. -/
theorem det_eq_zero_iff_of_projective_mk_eq
    {u v w u' v' w' : Homogeneous3}
    (hu : u ≠ 0) (hv : v ≠ 0) (hw : w ≠ 0)
    (hu' : u' ≠ 0) (hv' : v' ≠ 0) (hw' : w' ≠ 0)
    (hU : Projectivization.mk ℝ u hu =
      Projectivization.mk ℝ u' hu')
    (hV : Projectivization.mk ℝ v hv =
      Projectivization.mk ℝ v' hv')
    (hW : Projectivization.mk ℝ w hw =
      Projectivization.mk ℝ w' hw') :
    Matrix.det ![u, v, w] = 0 ↔
      Matrix.det ![u', v', w'] = 0 := by
  obtain ⟨a, ha⟩ :=
    (Projectivization.mk_eq_mk_iff' ℝ u u' hu hu').mp hU
  obtain ⟨b, hb⟩ :=
    (Projectivization.mk_eq_mk_iff' ℝ v v' hv hv').mp hV
  obtain ⟨c, hc⟩ :=
    (Projectivization.mk_eq_mk_iff' ℝ w w' hw hw').mp hW
  have ha0 : a ≠ 0 := by
    intro ha0
    apply hu
    subst a
    simpa using ha.symm
  have hb0 : b ≠ 0 := by
    intro hb0
    apply hv
    subst b
    simpa using hb.symm
  have hc0 : c ≠ 0 := by
    intro hc0
    apply hw
    subst c
    simpa using hc.symm
  have habc0 : a * b * c ≠ 0 :=
    mul_ne_zero (mul_ne_zero ha0 hb0) hc0
  have hdet :
      Matrix.det ![u, v, w] =
        (a * b * c) * Matrix.det ![u', v', w'] := by
    rw [← ha, ← hb, ← hc, det_smul_three]
  rw [hdet]
  constructor
  · intro hzero
    exact (mul_eq_zero.mp hzero).resolve_left habc0
  · intro hzero
    rw [hzero, mul_zero]

/-! ## Three lines through a common point -/

/-- Three line covectors incident with one nonzero homogeneous point are
linearly dependent. -/
theorem det_lineCovectors_eq_zero_of_common_point
    {r x0 y0 x1 y1 x2 y2 : Homogeneous3}
    (hr : r ≠ 0)
    (h0 : Matrix.det ![x0, y0, r] = 0)
    (h1 : Matrix.det ![x1, y1, r] = 0)
    (h2 : Matrix.det ![x2, y2, r] = 0) :
    Matrix.det ![crossProduct x0 y0, crossProduct x1 y1,
      crossProduct x2 y2] = 0 := by
  let M : Matrix (Fin 3) (Fin 3) ℝ :=
    ![crossProduct x0 y0, crossProduct x1 y1,
      crossProduct x2 y2]
  have hrow (x y : Homogeneous3)
      (hxy : Matrix.det ![x, y, r] = 0) :
      crossProduct x y ⬝ᵥ r = 0 := by
    calc
      crossProduct x y ⬝ᵥ r =
          r ⬝ᵥ crossProduct x y := dotProduct_comm _ _
      _ = x ⬝ᵥ crossProduct y r :=
        triple_product_permutation r x y
      _ = Matrix.det ![x, y, r] := triple_product_eq_det x y r
      _ = 0 := hxy
  have hMr : M *ᵥ r = 0 := by
    ext i
    fin_cases i
    · exact hrow x0 y0 h0
    · exact hrow x1 y1 h1
    · exact hrow x2 y2 h2
  by_contra hdet
  apply hr
  exact Matrix.eq_zero_of_mulVec_eq_zero hdet hMr

/-! ## Construction of the normal frame -/

private def projectiveBasisZero : Homogeneous3 := ![1, 0, 0]
private def projectiveBasisOne : Homogeneous3 := ![0, 1, 0]
private def projectiveBasisTwo : Homogeneous3 := ![0, 0, 1]
private def projectiveBasisSum : Homogeneous3 := ![1, 1, 1]

/-- Matrix whose first three columns are the first three vectors. -/
private def projectiveFiveBasisMatrix
    (g : Fin 5 → Homogeneous3) : Matrix (Fin 3) (Fin 3) ℝ :=
  (![g 0, g 1, g 2] : Matrix (Fin 3) (Fin 3) ℝ)ᵀ

private theorem projectiveFiveBasisMatrix_det
    (g : Fin 5 → Homogeneous3) :
    Matrix.det (projectiveFiveBasisMatrix g) =
      Matrix.det ![g 0, g 1, g 2] := by
  simp [projectiveFiveBasisMatrix]

private theorem projectiveFiveBasisMatrix_mulVec_zero
    (g : Fin 5 → Homogeneous3) :
    projectiveFiveBasisMatrix g *ᵥ projectiveBasisZero = g 0 := by
  ext i
  fin_cases i <;>
    simp [projectiveFiveBasisMatrix, projectiveBasisZero,
      Matrix.mulVec, dotProduct, Fin.sum_univ_three]

private theorem projectiveFiveBasisMatrix_mulVec_one
    (g : Fin 5 → Homogeneous3) :
    projectiveFiveBasisMatrix g *ᵥ projectiveBasisOne = g 1 := by
  ext i
  fin_cases i <;>
    simp [projectiveFiveBasisMatrix, projectiveBasisOne,
      Matrix.mulVec, dotProduct, Fin.sum_univ_three]

private theorem projectiveFiveBasisMatrix_mulVec_two
    (g : Fin 5 → Homogeneous3) :
    projectiveFiveBasisMatrix g *ᵥ projectiveBasisTwo = g 2 := by
  ext i
  fin_cases i <;>
    simp [projectiveFiveBasisMatrix, projectiveBasisTwo,
      Matrix.mulVec, dotProduct, Fin.sum_univ_three]

/-- Construct a normalized projective frame from five vectors in general
position. -/
noncomputable def projectiveFiveFrame
    (g : Fin 5 → Homogeneous3)
    (hgp : HomogeneousFiveGeneralPosition g) :
    ProjectiveFiveFrame g := by
  classical
  rcases hgp with ⟨hnonzero, hdet⟩
  have hdet012 : Matrix.det ![g 0, g 1, g 2] ≠ 0 :=
    hdet 0 1 2 (by decide) (by decide) (by decide)
  have hbasisDet : Matrix.det (projectiveFiveBasisMatrix g) ≠ 0 := by
    rw [projectiveFiveBasisMatrix_det]
    exact hdet012
  let C : GL (Fin 3) ℝ :=
    Matrix.GeneralLinearGroup.mkOfDetNeZero
      (projectiveFiveBasisMatrix g) hbasisDet
  have hC0 : C • projectiveBasisZero = g 0 := by
    change projectiveFiveBasisMatrix g *ᵥ projectiveBasisZero = g 0
    exact projectiveFiveBasisMatrix_mulVec_zero g
  have hC1 : C • projectiveBasisOne = g 1 := by
    change projectiveFiveBasisMatrix g *ᵥ projectiveBasisOne = g 1
    exact projectiveFiveBasisMatrix_mulVec_one g
  have hC2 : C • projectiveBasisTwo = g 2 := by
    change projectiveFiveBasisMatrix g *ᵥ projectiveBasisTwo = g 2
    exact projectiveFiveBasisMatrix_mulVec_two g
  have hCi0 : C⁻¹ • g 0 = projectiveBasisZero := by
    rw [← hC0]
    simp
  have hCi1 : C⁻¹ • g 1 = projectiveBasisOne := by
    rw [← hC1]
    simp
  have hCi2 : C⁻¹ • g 2 = projectiveBasisTwo := by
    rw [← hC2]
    simp
  let z : Homogeneous3 := C⁻¹ • g 3
  have hz0 : z 0 ≠ 0 := by
    have htrans :
        Matrix.det ![C⁻¹ • g 1, C⁻¹ • g 2, C⁻¹ • g 3] ≠ 0 := by
      intro hzero
      exact hdet 1 2 3 (by decide) (by decide) (by decide)
        ((det_eq_zero_iff_generalLinear_smul_three
          C⁻¹ (g 1) (g 2) (g 3)).mp hzero)
    rw [hCi1, hCi2] at htrans
    change Matrix.det ![projectiveBasisOne, projectiveBasisTwo, z] ≠ 0
      at htrans
    intro hz
    apply htrans
    simp [projectiveBasisOne, projectiveBasisTwo,
      Matrix.det_fin_three, hz]
  have hz1 : z 1 ≠ 0 := by
    have htrans :
        Matrix.det ![C⁻¹ • g 0, C⁻¹ • g 2, C⁻¹ • g 3] ≠ 0 := by
      intro hzero
      exact hdet 0 2 3 (by decide) (by decide) (by decide)
        ((det_eq_zero_iff_generalLinear_smul_three
          C⁻¹ (g 0) (g 2) (g 3)).mp hzero)
    rw [hCi0, hCi2] at htrans
    change Matrix.det ![projectiveBasisZero, projectiveBasisTwo, z] ≠ 0
      at htrans
    intro hz
    apply htrans
    simp [projectiveBasisZero, projectiveBasisTwo,
      Matrix.det_fin_three, hz]
  have hz2 : z 2 ≠ 0 := by
    have htrans :
        Matrix.det ![C⁻¹ • g 0, C⁻¹ • g 1, C⁻¹ • g 3] ≠ 0 := by
      intro hzero
      exact hdet 0 1 3 (by decide) (by decide) (by decide)
        ((det_eq_zero_iff_generalLinear_smul_three
          C⁻¹ (g 0) (g 1) (g 3)).mp hzero)
    rw [hCi0, hCi1] at htrans
    change Matrix.det ![projectiveBasisZero, projectiveBasisOne, z] ≠ 0
      at htrans
    intro hz
    apply htrans
    simp [projectiveBasisZero, projectiveBasisOne,
      Matrix.det_fin_three, hz]
  let Dmatrix : Matrix (Fin 3) (Fin 3) ℝ :=
    Matrix.diagonal (fun i => (z i)⁻¹)
  have hDdet : Matrix.det Dmatrix ≠ 0 := by
    rw [show Matrix.det Dmatrix = ∏ i, (z i)⁻¹ by
      simp [Dmatrix, Matrix.det_diagonal]]
    rw [Fin.prod_univ_three]
    exact mul_ne_zero (mul_ne_zero (inv_ne_zero hz0) (inv_ne_zero hz1))
      (inv_ne_zero hz2)
  let D : GL (Fin 3) ℝ :=
    Matrix.GeneralLinearGroup.mkOfDetNeZero Dmatrix hDdet
  have hD0 : D • projectiveBasisZero =
      (z 0)⁻¹ • projectiveBasisZero := by
    change Dmatrix *ᵥ projectiveBasisZero = _
    ext i
    fin_cases i <;>
      simp [Dmatrix, projectiveBasisZero, Matrix.mulVec,
        dotProduct, Fin.sum_univ_three]
  have hD1 : D • projectiveBasisOne =
      (z 1)⁻¹ • projectiveBasisOne := by
    change Dmatrix *ᵥ projectiveBasisOne = _
    ext i
    fin_cases i <;>
      simp [Dmatrix, projectiveBasisOne, Matrix.mulVec,
        dotProduct, Fin.sum_univ_three]
  have hD2 : D • projectiveBasisTwo =
      (z 2)⁻¹ • projectiveBasisTwo := by
    change Dmatrix *ᵥ projectiveBasisTwo = _
    ext i
    fin_cases i <;>
      simp [Dmatrix, projectiveBasisTwo, Matrix.mulVec,
        dotProduct, Fin.sum_univ_three]
  have hDz : D • z = projectiveBasisSum := by
    change Dmatrix *ᵥ z = projectiveBasisSum
    ext i
    fin_cases i <;>
      simp [Dmatrix, projectiveBasisSum, Matrix.mulVec,
        dotProduct, Fin.sum_univ_three, hz0, hz1, hz2]
  let G : GL (Fin 3) ℝ := D * C⁻¹
  have hG0 : G • g 0 = (z 0)⁻¹ • projectiveBasisZero := by
    change (D * C⁻¹) • g 0 = _
    rw [mul_smul, hCi0, hD0]
  have hG1 : G • g 1 = (z 1)⁻¹ • projectiveBasisOne := by
    change (D * C⁻¹) • g 1 = _
    rw [mul_smul, hCi1, hD1]
  have hG2 : G • g 2 = (z 2)⁻¹ • projectiveBasisTwo := by
    change (D * C⁻¹) • g 2 = _
    rw [mul_smul, hCi2, hD2]
  have hG3 : G • g 3 = projectiveBasisSum := by
    change (D * C⁻¹) • g 3 = _
    rw [mul_smul]
    change D • z = _
    exact hDz
  let w : Homogeneous3 := G • g 4
  have hw2 : w 2 ≠ 0 := by
    have htrans : Matrix.det ![G • g 0, G • g 1, G • g 4] ≠ 0 := by
      intro hzero
      exact hdet 0 1 4 (by decide) (by decide) (by decide)
        ((det_eq_zero_iff_generalLinear_smul_three
          G (g 0) (g 1) (g 4)).mp hzero)
    intro hw
    apply htrans
    rw [hG0, hG1]
    change Matrix.det
      ![(z 0)⁻¹ • projectiveBasisZero,
        (z 1)⁻¹ • projectiveBasisOne, w] = 0
    simp [projectiveBasisZero, projectiveBasisOne,
      Matrix.det_fin_three, hw]
  let scale : Fin 5 → ℝ :=
    ![(z 0)⁻¹, (z 1)⁻¹, (z 2)⁻¹, 1, w 2]
  have hscale : ∀ i, scale i ≠ 0 := by
    intro i
    fin_cases i <;> simp [scale, hz0, hz1, hz2, hw2]
  have hwNormal :
      w = w 2 • projectiveFiveNormalPoint
        (w 0 / w 2) (w 1 / w 2) 4 := by
    ext i
    fin_cases i
    · change w 0 = w 2 * (w 0 / w 2)
      field_simp [hw2]
    · change w 1 = w 2 * (w 1 / w 2)
      field_simp [hw2]
    · change w 2 = w 2 * 1
      ring
  refine
    { G := G
      scale := scale
      scale_ne_zero := hscale
      a := w 0 / w 2
      b := w 1 / w 2
      map_point := ?_ }
  intro i
  fin_cases i
  · simpa [scale, projectiveFiveNormalPoint, projectiveBasisZero]
      using hG0
  · simpa [scale, projectiveFiveNormalPoint, projectiveBasisOne]
      using hG1
  · simpa [scale, projectiveFiveNormalPoint, projectiveBasisTwo]
      using hG2
  · simpa [scale, projectiveFiveNormalPoint, projectiveBasisSum]
      using hG3
  · simpa [scale, w] using hwNormal

end Erdos506.Incidence
