import Erdos506.Incidence.FiveConicNormalSeparator

/-!
# The standard five-conic complete quadrangle

The normal separator uses the four conic parameters `∞,0,1,λ`.  This file
records their genuine complete-quadrangle general position for `1 < λ`, so
the three normal diagonal representatives can subsequently be used as
projective points without carrying an auxiliary nondegeneracy assumption.
-/

namespace Erdos506.Incidence

open Matrix

private theorem fiveConicNormal_det_infinity_zero_one :
    Matrix.det ![fiveConicNormalInfinity, fiveConicNormalPoint 0,
      fiveConicNormalPoint 1] = (-1 : ℝ) := by
  simp [fiveConicNormalInfinity, fiveConicNormalPoint,
    Matrix.det_fin_three]

private theorem fiveConicNormal_det_infinity_zero_parameter (lam : ℝ) :
    Matrix.det ![fiveConicNormalInfinity, fiveConicNormalPoint 0,
      fiveConicNormalPoint lam] = -lam := by
  simp [fiveConicNormalInfinity, fiveConicNormalPoint,
    Matrix.det_fin_three]

private theorem fiveConicNormal_det_infinity_one_parameter (lam : ℝ) :
    Matrix.det ![fiveConicNormalInfinity, fiveConicNormalPoint 1,
      fiveConicNormalPoint lam] = 1 - lam := by
  simp [fiveConicNormalInfinity, fiveConicNormalPoint,
    Matrix.det_fin_three]

private theorem fiveConicNormal_det_zero_one_parameter (lam : ℝ) :
    Matrix.det ![fiveConicNormalPoint 0, fiveConicNormalPoint 1,
      fiveConicNormalPoint lam] = lam * (1 - lam) := by
  simp [fiveConicNormalPoint, Matrix.det_fin_three]
  ring

/-- The four normal points `∞,0,1,λ` form a complete quadrangle whenever
`λ` lies past `1` in the affine chart. -/
theorem fiveConicNormal_completeQuadrangle {lam : ℝ} (hlam : 1 < lam) :
    CompleteQuadrangleGeneralPosition
      fiveConicNormalInfinity (fiveConicNormalPoint 0)
      (fiveConicNormalPoint 1) (fiveConicNormalPoint lam) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [fiveConicNormal_det_infinity_zero_one]
    norm_num
  · rw [fiveConicNormal_det_infinity_zero_parameter]
    intro h
    linarith
  · rw [fiveConicNormal_det_infinity_one_parameter]
    intro h
    linarith
  · rw [fiveConicNormal_det_zero_one_parameter]
    intro h
    rcases mul_eq_zero.mp h with hzero | hone <;> linarith

/-- Every normal diagonal representative is nonzero in the separator
chamber. -/
theorem fiveConicNormalDiagonal_ne_zero {lam : ℝ} (hlam : 1 < lam)
    (i : Fin 3) : fiveConicNormalDiagonal lam i ≠ 0 := by
  let h := fiveConicNormal_completeQuadrangle hlam
  fin_cases i
  · simpa [fiveConicNormalDiagonal, fiveConicNormalDiagonalZero,
      fiveConicNormalInfinity, diagonalAB_CD] using diagonalAB_CD_ne_zero h
  · simpa [fiveConicNormalDiagonal, fiveConicNormalDiagonalOne,
      fiveConicNormalInfinity, diagonalAC_BD] using diagonalAC_BD_ne_zero h
  · simpa [fiveConicNormalDiagonal, fiveConicNormalDiagonalTwo,
      fiveConicNormalInfinity, diagonalAD_BC] using diagonalAD_BC_ne_zero h

theorem fiveConicNormalPoint_ne_zero (t : ℝ) :
    fiveConicNormalPoint t ≠ 0 := by
  intro hzero
  have hlast : (1 : ℝ) = 0 := by
    simpa [fiveConicNormalPoint, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two] using
      congrFun hzero (2 : Fin 3)
  norm_num at hlast

theorem fiveConicNormalInfinity_ne_zero : fiveConicNormalInfinity ≠ 0 := by
  intro hzero
  have hfirst := congrFun hzero (0 : Fin 3)
  norm_num [fiveConicNormalInfinity] at hfirst

end Erdos506.Incidence
