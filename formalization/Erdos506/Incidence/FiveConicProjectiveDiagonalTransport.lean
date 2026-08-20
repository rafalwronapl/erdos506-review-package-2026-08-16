import Erdos506.Incidence.FiveConicProjectiveTransport

/-!
# Projective transport of complete-quadrangle diagonals

The cyclic five-conic separator is computed in binary Veronese coordinates.
To use it on an actual circle, its three diagonal centres must be transported
through the induced element of `GL₃`.  This file records that transport at the
projective level.  The proof uses only determinant incidence and uniqueness of
the intersection of two distinct projective lines; it does not choose an
affine chart for the plane.
-/

namespace Erdos506.Incidence

open Matrix
open scoped LinearAlgebra.Projectivization

private theorem fiveConic_generalLinear_smul_ne_zero
    (G : GL (Fin 3) ℝ) {v : Homogeneous3} (hv : v ≠ 0) :
    G • v ≠ 0 := by
  intro hzero
  apply hv
  have hback := congrArg (fun w : Homogeneous3 => G⁻¹ • w) hzero
  simpa [smul_smul] using hback

private theorem fiveConic_crossProduct_ne_zero_of_det_ne_zero
    {x y z : Homogeneous3} (hdet : Matrix.det ![x, y, z] ≠ 0) :
    crossProduct x y ≠ 0 := by
  intro hcross
  apply hdet
  calc
    Matrix.det ![x, y, z] = z ⬝ᵥ crossProduct x y := by
      symm
      calc
        z ⬝ᵥ crossProduct x y = x ⬝ᵥ crossProduct y z :=
          triple_product_permutation _ _ _
        _ = Matrix.det ![x, y, z] := triple_product_eq_det _ _ _
    _ = 0 := by rw [hcross, dotProduct_zero]

private theorem fiveConic_diagonalAB_CD_incident_left
    (a b c d : Homogeneous3) :
    Matrix.det ![a, b, diagonalAB_CD a b c d] = 0 := by
  simp [diagonalAB_CD, cross_apply, Matrix.det_fin_three]
  ring

private theorem fiveConic_diagonalAB_CD_incident_right
    (a b c d : Homogeneous3) :
    Matrix.det ![c, d, diagonalAB_CD a b c d] = 0 := by
  simp [diagonalAB_CD, cross_apply, Matrix.det_fin_three]
  ring

private theorem fiveConic_diagonalAC_BD_incident_left
    (a b c d : Homogeneous3) :
    Matrix.det ![a, c, diagonalAC_BD a b c d] = 0 := by
  simp [diagonalAC_BD, cross_apply, Matrix.det_fin_three]
  ring

private theorem fiveConic_diagonalAC_BD_incident_right
    (a b c d : Homogeneous3) :
    Matrix.det ![b, d, diagonalAC_BD a b c d] = 0 := by
  simp [diagonalAC_BD, cross_apply, Matrix.det_fin_three]
  ring

private theorem fiveConic_diagonalAD_BC_incident_left
    (a b c d : Homogeneous3) :
    Matrix.det ![a, d, diagonalAD_BC a b c d] = 0 := by
  simp [diagonalAD_BC, cross_apply, Matrix.det_fin_three]
  ring

private theorem fiveConic_diagonalAD_BC_incident_right
    (a b c d : Homogeneous3) :
    Matrix.det ![b, c, diagonalAD_BC a b c d] = 0 := by
  simp [diagonalAD_BC, cross_apply, Matrix.det_fin_three]
  ring

private def fiveConic_transportCompleteQuadrangle
    (G : GL (Fin 3) ℝ) {a b c d : Homogeneous3}
    (h : CompleteQuadrangleGeneralPosition a b c d) :
    CompleteQuadrangleGeneralPosition (G • a) (G • b) (G • c) (G • d) where
  det_abc_ne := by
    intro hzero
    apply h.det_abc_ne
    exact (det_eq_zero_iff_generalLinear_smul_three G a b c).mp hzero
  det_abd_ne := by
    intro hzero
    apply h.det_abd_ne
    exact (det_eq_zero_iff_generalLinear_smul_three G a b d).mp hzero
  det_acd_ne := by
    intro hzero
    apply h.det_acd_ne
    exact (det_eq_zero_iff_generalLinear_smul_three G a c d).mp hzero
  det_bcd_ne := by
    intro hzero
    apply h.det_bcd_ne
    exact (det_eq_zero_iff_generalLinear_smul_three G b c d).mp hzero

/-- The first diagonal point of a complete quadrangle commutes with every
projective linear change of coordinates. -/
theorem fiveConic_generalLinear_projectiveDiagonalAB_CD
    (G : GL (Fin 3) ℝ) {a b c d : Homogeneous3}
    (h : CompleteQuadrangleGeneralPosition a b c d) :
    Projectivization.mk ℝ (G • diagonalAB_CD a b c d)
        (fiveConic_generalLinear_smul_ne_zero G
          (diagonalAB_CD_ne_zero h)) =
      projectiveDiagonalAB_CD (G • a) (G • b) (G • c) (G • d)
        (fiveConic_transportCompleteQuadrangle G h) := by
  let hG : CompleteQuadrangleGeneralPosition
      (G • a) (G • b) (G • c) (G • d) :=
    fiveConic_transportCompleteQuadrangle G h
  have hdiag : G • diagonalAB_CD a b c d ≠ 0 :=
    fiveConic_generalLinear_smul_ne_zero G (diagonalAB_CD_ne_zero h)
  have hlineAB : crossProduct (G • a) (G • b) ≠ 0 :=
    fiveConic_crossProduct_ne_zero_of_det_ne_zero hG.det_abc_ne
  have hdetCDA : Matrix.det ![G • c, G • d, G • a] ≠ 0 := by
    intro hzero
    apply hG.det_acd_ne
    calc
      Matrix.det ![G • a, G • c, G • d] =
          Matrix.det ![G • c, G • d, G • a] := by
        simp [Matrix.det_fin_three]
        ring
      _ = 0 := hzero
  have hlineCD : crossProduct (G • c) (G • d) ≠ 0 :=
    fiveConic_crossProduct_ne_zero_of_det_ne_zero hdetCDA
  have hlines :
      Projectivization.mk ℝ (crossProduct (G • a) (G • b)) hlineAB ≠
        Projectivization.mk ℝ (crossProduct (G • c) (G • d)) hlineCD := by
    intro heq
    apply diagonalAB_CD_ne_zero hG
    exact (Projectivization.mk_eq_mk_iff_crossProduct_eq_zero
      hlineAB hlineCD).mp heq
  have horthAB : Projectivization.orthogonal
      (Projectivization.mk ℝ (crossProduct (G • a) (G • b)) hlineAB)
      (Projectivization.mk ℝ (G • diagonalAB_CD a b c d) hdiag) := by
    apply (Projectivization.orthogonal_mk hlineAB hdiag).2
    calc
      crossProduct (G • a) (G • b) ⬝ᵥ
          (G • diagonalAB_CD a b c d) =
          (G • diagonalAB_CD a b c d) ⬝ᵥ
            crossProduct (G • a) (G • b) := dotProduct_comm _ _
      _ = (G • a) ⬝ᵥ crossProduct (G • b)
          (G • diagonalAB_CD a b c d) :=
        triple_product_permutation _ _ _
      _ = Matrix.det ![G • a, G • b,
          G • diagonalAB_CD a b c d] :=
        triple_product_eq_det _ _ _
      _ = 0 := (det_eq_zero_iff_generalLinear_smul_three
        G a b (diagonalAB_CD a b c d)).mpr
          (fiveConic_diagonalAB_CD_incident_left a b c d)
  have horthCD : Projectivization.orthogonal
      (Projectivization.mk ℝ (crossProduct (G • c) (G • d)) hlineCD)
      (Projectivization.mk ℝ (G • diagonalAB_CD a b c d) hdiag) := by
    apply (Projectivization.orthogonal_mk hlineCD hdiag).2
    calc
      crossProduct (G • c) (G • d) ⬝ᵥ
          (G • diagonalAB_CD a b c d) =
          (G • diagonalAB_CD a b c d) ⬝ᵥ
            crossProduct (G • c) (G • d) := dotProduct_comm _ _
      _ = (G • c) ⬝ᵥ crossProduct (G • d)
          (G • diagonalAB_CD a b c d) :=
        triple_product_permutation _ _ _
      _ = Matrix.det ![G • c, G • d,
          G • diagonalAB_CD a b c d] :=
        triple_product_eq_det _ _ _
      _ = 0 := (det_eq_zero_iff_generalLinear_smul_three
        G c d (diagonalAB_CD a b c d)).mpr
          (fiveConic_diagonalAB_CD_incident_right a b c d)
  have hcross := projectiveCovector_eq_cross_of_orthogonal
    hlines horthAB horthCD
  rw [Projectivization.cross_mk_of_ne hlineAB hlineCD hlines] at hcross
  simpa only [projectiveDiagonalAB_CD, hG] using hcross

/-- The second diagonal point of a complete quadrangle commutes with every
projective linear change of coordinates. -/
theorem fiveConic_generalLinear_projectiveDiagonalAC_BD
    (G : GL (Fin 3) ℝ) {a b c d : Homogeneous3}
    (h : CompleteQuadrangleGeneralPosition a b c d) :
    Projectivization.mk ℝ (G • diagonalAC_BD a b c d)
        (fiveConic_generalLinear_smul_ne_zero G
          (diagonalAC_BD_ne_zero h)) =
      projectiveDiagonalAC_BD (G • a) (G • b) (G • c) (G • d)
        (fiveConic_transportCompleteQuadrangle G h) := by
  let hG : CompleteQuadrangleGeneralPosition
      (G • a) (G • b) (G • c) (G • d) :=
    fiveConic_transportCompleteQuadrangle G h
  have hdiag : G • diagonalAC_BD a b c d ≠ 0 :=
    fiveConic_generalLinear_smul_ne_zero G (diagonalAC_BD_ne_zero h)
  have hlineAC : crossProduct (G • a) (G • c) ≠ 0 :=
    fiveConic_crossProduct_ne_zero_of_det_ne_zero hG.det_acd_ne
  have hdetBDA : Matrix.det ![G • b, G • d, G • a] ≠ 0 := by
    intro hzero
    apply hG.det_abd_ne
    calc
      Matrix.det ![G • a, G • b, G • d] =
          Matrix.det ![G • b, G • d, G • a] := by
        simp [Matrix.det_fin_three]
        ring
      _ = 0 := hzero
  have hlineBD : crossProduct (G • b) (G • d) ≠ 0 :=
    fiveConic_crossProduct_ne_zero_of_det_ne_zero hdetBDA
  have hlines :
      Projectivization.mk ℝ (crossProduct (G • a) (G • c)) hlineAC ≠
        Projectivization.mk ℝ (crossProduct (G • b) (G • d)) hlineBD := by
    intro heq
    apply diagonalAC_BD_ne_zero hG
    exact (Projectivization.mk_eq_mk_iff_crossProduct_eq_zero
      hlineAC hlineBD).mp heq
  have horthAC : Projectivization.orthogonal
      (Projectivization.mk ℝ (crossProduct (G • a) (G • c)) hlineAC)
      (Projectivization.mk ℝ (G • diagonalAC_BD a b c d) hdiag) := by
    apply (Projectivization.orthogonal_mk hlineAC hdiag).2
    calc
      crossProduct (G • a) (G • c) ⬝ᵥ
          (G • diagonalAC_BD a b c d) =
          (G • diagonalAC_BD a b c d) ⬝ᵥ
            crossProduct (G • a) (G • c) := dotProduct_comm _ _
      _ = (G • a) ⬝ᵥ crossProduct (G • c)
          (G • diagonalAC_BD a b c d) :=
        triple_product_permutation _ _ _
      _ = Matrix.det ![G • a, G • c,
          G • diagonalAC_BD a b c d] :=
        triple_product_eq_det _ _ _
      _ = 0 := (det_eq_zero_iff_generalLinear_smul_three
        G a c (diagonalAC_BD a b c d)).mpr
          (fiveConic_diagonalAC_BD_incident_left a b c d)
  have horthBD : Projectivization.orthogonal
      (Projectivization.mk ℝ (crossProduct (G • b) (G • d)) hlineBD)
      (Projectivization.mk ℝ (G • diagonalAC_BD a b c d) hdiag) := by
    apply (Projectivization.orthogonal_mk hlineBD hdiag).2
    calc
      crossProduct (G • b) (G • d) ⬝ᵥ
          (G • diagonalAC_BD a b c d) =
          (G • diagonalAC_BD a b c d) ⬝ᵥ
            crossProduct (G • b) (G • d) := dotProduct_comm _ _
      _ = (G • b) ⬝ᵥ crossProduct (G • d)
          (G • diagonalAC_BD a b c d) :=
        triple_product_permutation _ _ _
      _ = Matrix.det ![G • b, G • d,
          G • diagonalAC_BD a b c d] :=
        triple_product_eq_det _ _ _
      _ = 0 := (det_eq_zero_iff_generalLinear_smul_three
        G b d (diagonalAC_BD a b c d)).mpr
          (fiveConic_diagonalAC_BD_incident_right a b c d)
  have hcross := projectiveCovector_eq_cross_of_orthogonal
    hlines horthAC horthBD
  rw [Projectivization.cross_mk_of_ne hlineAC hlineBD hlines] at hcross
  simpa only [projectiveDiagonalAC_BD, hG] using hcross

/-- The third diagonal point of a complete quadrangle commutes with every
projective linear change of coordinates. -/
theorem fiveConic_generalLinear_projectiveDiagonalAD_BC
    (G : GL (Fin 3) ℝ) {a b c d : Homogeneous3}
    (h : CompleteQuadrangleGeneralPosition a b c d) :
    Projectivization.mk ℝ (G • diagonalAD_BC a b c d)
        (fiveConic_generalLinear_smul_ne_zero G
          (diagonalAD_BC_ne_zero h)) =
      projectiveDiagonalAD_BC (G • a) (G • b) (G • c) (G • d)
        (fiveConic_transportCompleteQuadrangle G h) := by
  let hG : CompleteQuadrangleGeneralPosition
      (G • a) (G • b) (G • c) (G • d) :=
    fiveConic_transportCompleteQuadrangle G h
  have hdiag : G • diagonalAD_BC a b c d ≠ 0 :=
    fiveConic_generalLinear_smul_ne_zero G (diagonalAD_BC_ne_zero h)
  have hdetADB : Matrix.det ![G • a, G • d, G • b] ≠ 0 := by
    intro hzero
    apply hG.det_abd_ne
    calc
      Matrix.det ![G • a, G • b, G • d] =
          -Matrix.det ![G • a, G • d, G • b] := by
        simp [Matrix.det_fin_three]
        ring
      _ = 0 := by rw [hzero, neg_zero]
  have hlineAD : crossProduct (G • a) (G • d) ≠ 0 :=
    fiveConic_crossProduct_ne_zero_of_det_ne_zero hdetADB
  have hdetBCA : Matrix.det ![G • b, G • c, G • a] ≠ 0 := by
    intro hzero
    apply hG.det_abc_ne
    calc
      Matrix.det ![G • a, G • b, G • c] =
          Matrix.det ![G • b, G • c, G • a] := by
        simp [Matrix.det_fin_three]
        ring
      _ = 0 := hzero
  have hlineBC : crossProduct (G • b) (G • c) ≠ 0 :=
    fiveConic_crossProduct_ne_zero_of_det_ne_zero hdetBCA
  have hlines :
      Projectivization.mk ℝ (crossProduct (G • a) (G • d)) hlineAD ≠
        Projectivization.mk ℝ (crossProduct (G • b) (G • c)) hlineBC := by
    intro heq
    apply diagonalAD_BC_ne_zero hG
    exact (Projectivization.mk_eq_mk_iff_crossProduct_eq_zero
      hlineAD hlineBC).mp heq
  have horthAD : Projectivization.orthogonal
      (Projectivization.mk ℝ (crossProduct (G • a) (G • d)) hlineAD)
      (Projectivization.mk ℝ (G • diagonalAD_BC a b c d) hdiag) := by
    apply (Projectivization.orthogonal_mk hlineAD hdiag).2
    calc
      crossProduct (G • a) (G • d) ⬝ᵥ
          (G • diagonalAD_BC a b c d) =
          (G • diagonalAD_BC a b c d) ⬝ᵥ
            crossProduct (G • a) (G • d) := dotProduct_comm _ _
      _ = (G • a) ⬝ᵥ crossProduct (G • d)
          (G • diagonalAD_BC a b c d) :=
        triple_product_permutation _ _ _
      _ = Matrix.det ![G • a, G • d,
          G • diagonalAD_BC a b c d] :=
        triple_product_eq_det _ _ _
      _ = 0 := (det_eq_zero_iff_generalLinear_smul_three
        G a d (diagonalAD_BC a b c d)).mpr
          (fiveConic_diagonalAD_BC_incident_left a b c d)
  have horthBC : Projectivization.orthogonal
      (Projectivization.mk ℝ (crossProduct (G • b) (G • c)) hlineBC)
      (Projectivization.mk ℝ (G • diagonalAD_BC a b c d) hdiag) := by
    apply (Projectivization.orthogonal_mk hlineBC hdiag).2
    calc
      crossProduct (G • b) (G • c) ⬝ᵥ
          (G • diagonalAD_BC a b c d) =
          (G • diagonalAD_BC a b c d) ⬝ᵥ
            crossProduct (G • b) (G • c) := dotProduct_comm _ _
      _ = (G • b) ⬝ᵥ crossProduct (G • c)
          (G • diagonalAD_BC a b c d) :=
        triple_product_permutation _ _ _
      _ = Matrix.det ![G • b, G • c,
          G • diagonalAD_BC a b c d] :=
        triple_product_eq_det _ _ _
      _ = 0 := (det_eq_zero_iff_generalLinear_smul_three
        G b c (diagonalAD_BC a b c d)).mpr
          (fiveConic_diagonalAD_BC_incident_right a b c d)
  have hcross := projectiveCovector_eq_cross_of_orthogonal
    hlines horthAD horthBC
  rw [Projectivization.cross_mk_of_ne hlineAD hlineBC hlines] at hcross
  simpa only [projectiveDiagonalAD_BC, hG] using hcross

end Erdos506.Incidence
