import Erdos506.Incidence.FiveConicCyclicProjectiveTransport
import Erdos506.Incidence.FiveConicProjectiveDiagonalTransport

/-!
# Diagonal centres in the transported normal five-conic chart

The three normal diagonal representatives are not placeholders: after the
explicit proper-circle transport they are exactly the projective diagonals of
the four transported normal conic points.  This is the endpoint which lets
actual double-host directions be fed to the normal separator.
-/

namespace Erdos506.Incidence

open Erdos506.V4
open Matrix
open scoped LinearAlgebra.Projectivization

private theorem fiveConic_crossProduct_ne_zero_of_det_ne_zero'
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

private theorem projectiveDiagonalAB_CD_eq_cross_mk
    (a b c d : Homogeneous3)
    (h : CompleteQuadrangleGeneralPosition a b c d)
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (hd : d ≠ 0) :
    projectiveDiagonalAB_CD a b c d h =
      Projectivization.cross
        (Projectivization.cross (Projectivization.mk ℝ a ha)
          (Projectivization.mk ℝ b hb))
        (Projectivization.cross (Projectivization.mk ℝ c hc)
          (Projectivization.mk ℝ d hd)) := by
  have hab : crossProduct a b ≠ 0 :=
    fiveConic_crossProduct_ne_zero_of_det_ne_zero' h.det_abc_ne
  have hdetCDA : Matrix.det ![c, d, a] ≠ 0 := by
    intro hzero
    apply h.det_acd_ne
    calc
      Matrix.det ![a, c, d] = Matrix.det ![c, d, a] := by
        simp [Matrix.det_fin_three]
        ring
      _ = 0 := hzero
  have hcd : crossProduct c d ≠ 0 :=
    fiveConic_crossProduct_ne_zero_of_det_ne_zero' hdetCDA
  have hlines :
      Projectivization.mk ℝ (crossProduct a b) hab ≠
        Projectivization.mk ℝ (crossProduct c d) hcd := by
    intro heq
    apply diagonalAB_CD_ne_zero h
    exact (Projectivization.mk_eq_mk_iff_crossProduct_eq_zero hab hcd).mp heq
  rw [Projectivization.cross_mk_of_cross_ne_zero ha hb hab,
    Projectivization.cross_mk_of_cross_ne_zero hc hd hcd,
    Projectivization.cross_mk_of_ne hab hcd hlines]
  rfl

private theorem projectiveDiagonalAC_BD_eq_cross_mk
    (a b c d : Homogeneous3)
    (h : CompleteQuadrangleGeneralPosition a b c d)
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (hd : d ≠ 0) :
    projectiveDiagonalAC_BD a b c d h =
      Projectivization.cross
        (Projectivization.cross (Projectivization.mk ℝ a ha)
          (Projectivization.mk ℝ c hc))
        (Projectivization.cross (Projectivization.mk ℝ b hb)
          (Projectivization.mk ℝ d hd)) := by
  have hac : crossProduct a c ≠ 0 :=
    fiveConic_crossProduct_ne_zero_of_det_ne_zero' h.det_acd_ne
  have hdetBDA : Matrix.det ![b, d, a] ≠ 0 := by
    intro hzero
    apply h.det_abd_ne
    calc
      Matrix.det ![a, b, d] = Matrix.det ![b, d, a] := by
        simp [Matrix.det_fin_three]
        ring
      _ = 0 := hzero
  have hbd : crossProduct b d ≠ 0 :=
    fiveConic_crossProduct_ne_zero_of_det_ne_zero' hdetBDA
  have hlines :
      Projectivization.mk ℝ (crossProduct a c) hac ≠
        Projectivization.mk ℝ (crossProduct b d) hbd := by
    intro heq
    apply diagonalAC_BD_ne_zero h
    exact (Projectivization.mk_eq_mk_iff_crossProduct_eq_zero hac hbd).mp heq
  rw [Projectivization.cross_mk_of_cross_ne_zero ha hc hac,
    Projectivization.cross_mk_of_cross_ne_zero hb hd hbd,
    Projectivization.cross_mk_of_ne hac hbd hlines]
  rfl

private theorem projectiveDiagonalAD_BC_eq_cross_mk
    (a b c d : Homogeneous3)
    (h : CompleteQuadrangleGeneralPosition a b c d)
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (hd : d ≠ 0) :
    projectiveDiagonalAD_BC a b c d h =
      Projectivization.cross
        (Projectivization.cross (Projectivization.mk ℝ a ha)
          (Projectivization.mk ℝ d hd))
        (Projectivization.cross (Projectivization.mk ℝ b hb)
          (Projectivization.mk ℝ c hc)) := by
  have hdetADB : Matrix.det ![a, d, b] ≠ 0 := by
    intro hzero
    apply h.det_abd_ne
    calc
      Matrix.det ![a, b, d] = -Matrix.det ![a, d, b] := by
        simp [Matrix.det_fin_three]
        ring
      _ = 0 := by rw [hzero]; ring
  have had : crossProduct a d ≠ 0 :=
    fiveConic_crossProduct_ne_zero_of_det_ne_zero' hdetADB
  have hdetBCA : Matrix.det ![b, c, a] ≠ 0 := by
    intro hzero
    apply h.det_abc_ne
    calc
      Matrix.det ![a, b, c] = Matrix.det ![b, c, a] := by
        simp [Matrix.det_fin_three]
        ring
      _ = 0 := hzero
  have hbc : crossProduct b c ≠ 0 :=
    fiveConic_crossProduct_ne_zero_of_det_ne_zero' hdetBCA
  have hlines :
      Projectivization.mk ℝ (crossProduct a d) had ≠
        Projectivization.mk ℝ (crossProduct b c) hbc := by
    intro heq
    apply diagonalAD_BC_ne_zero h
    exact (Projectivization.mk_eq_mk_iff_crossProduct_eq_zero had hbc).mp heq
  rw [Projectivization.cross_mk_of_cross_ne_zero ha hd had,
    Projectivization.cross_mk_of_cross_ne_zero hb hc hbc,
    Projectivization.cross_mk_of_ne had hbc hlines]
  rfl

/-- General position of the first four normal conic points is preserved by
the explicit plane-side transport. -/
noncomputable def fiveConicTransportedNormalQuadrangle
    (c : ProperCircle) (g : GL (Fin 2) ℝ) (lam : ℝ)
    (hlam : 1 < lam) :
    CompleteQuadrangleGeneralPosition
      (fiveConicProjectiveTransport c g • fiveConicNormalInfinity)
      (fiveConicProjectiveTransport c g • fiveConicNormalPoint 0)
      (fiveConicProjectiveTransport c g • fiveConicNormalPoint 1)
      (fiveConicProjectiveTransport c g • fiveConicNormalPoint lam) where
  det_abc_ne := by
    intro hzero
    exact (fiveConicNormal_completeQuadrangle hlam).det_abc_ne
      ((det_eq_zero_iff_generalLinear_smul_three
        (fiveConicProjectiveTransport c g) fiveConicNormalInfinity
        (fiveConicNormalPoint 0) (fiveConicNormalPoint 1)).mp hzero)
  det_abd_ne := by
    intro hzero
    exact (fiveConicNormal_completeQuadrangle hlam).det_abd_ne
      ((det_eq_zero_iff_generalLinear_smul_three
        (fiveConicProjectiveTransport c g) fiveConicNormalInfinity
        (fiveConicNormalPoint 0) (fiveConicNormalPoint lam)).mp hzero)
  det_acd_ne := by
    intro hzero
    exact (fiveConicNormal_completeQuadrangle hlam).det_acd_ne
      ((det_eq_zero_iff_generalLinear_smul_three
        (fiveConicProjectiveTransport c g) fiveConicNormalInfinity
        (fiveConicNormalPoint 1) (fiveConicNormalPoint lam)).mp hzero)
  det_bcd_ne := by
    intro hzero
    exact (fiveConicNormal_completeQuadrangle hlam).det_bcd_ne
      ((det_eq_zero_iff_generalLinear_smul_three
        (fiveConicProjectiveTransport c g) (fiveConicNormalPoint 0)
        (fiveConicNormalPoint 1) (fiveConicNormalPoint lam)).mp hzero)

/-- The first transported normal diagonal is the first geometric diagonal
of the transported quadrangle. -/
theorem fiveConicTransportedNormalDiagonal_zero_eq_projectiveDiagonal
    (c : ProperCircle) (g : GL (Fin 2) ℝ) (lam : ℝ)
    (hlam : 1 < lam) :
    fiveConicTransportedNormalDiagonal c g lam hlam 0 =
      projectiveDiagonalAB_CD
        (fiveConicProjectiveTransport c g • fiveConicNormalInfinity)
        (fiveConicProjectiveTransport c g • fiveConicNormalPoint 0)
        (fiveConicProjectiveTransport c g • fiveConicNormalPoint 1)
        (fiveConicProjectiveTransport c g • fiveConicNormalPoint lam)
        (fiveConicTransportedNormalQuadrangle c g lam hlam) := by
  simpa [fiveConicTransportedNormalDiagonal, fiveConicNormalDiagonal,
    fiveConicNormalDiagonalZero, fiveConicNormalInfinity, diagonalAB_CD,
    fiveConicTransportedNormalQuadrangle] using
    (fiveConic_generalLinear_projectiveDiagonalAB_CD
      (fiveConicProjectiveTransport c g)
      (fiveConicNormal_completeQuadrangle hlam))

/-- The second transported normal diagonal is the second geometric diagonal
of the transported quadrangle. -/
theorem fiveConicTransportedNormalDiagonal_one_eq_projectiveDiagonal
    (c : ProperCircle) (g : GL (Fin 2) ℝ) (lam : ℝ)
    (hlam : 1 < lam) :
    fiveConicTransportedNormalDiagonal c g lam hlam 1 =
      projectiveDiagonalAC_BD
        (fiveConicProjectiveTransport c g • fiveConicNormalInfinity)
        (fiveConicProjectiveTransport c g • fiveConicNormalPoint 0)
        (fiveConicProjectiveTransport c g • fiveConicNormalPoint 1)
        (fiveConicProjectiveTransport c g • fiveConicNormalPoint lam)
        (fiveConicTransportedNormalQuadrangle c g lam hlam) := by
  simpa [fiveConicTransportedNormalDiagonal, fiveConicNormalDiagonal,
    fiveConicNormalDiagonalOne, fiveConicNormalInfinity, diagonalAC_BD,
    fiveConicTransportedNormalQuadrangle] using
    (fiveConic_generalLinear_projectiveDiagonalAC_BD
      (fiveConicProjectiveTransport c g)
      (fiveConicNormal_completeQuadrangle hlam))

/-- The third transported normal diagonal is the third geometric diagonal
of the transported quadrangle. -/
theorem fiveConicTransportedNormalDiagonal_two_eq_projectiveDiagonal
    (c : ProperCircle) (g : GL (Fin 2) ℝ) (lam : ℝ)
    (hlam : 1 < lam) :
    fiveConicTransportedNormalDiagonal c g lam hlam 2 =
      projectiveDiagonalAD_BC
        (fiveConicProjectiveTransport c g • fiveConicNormalInfinity)
        (fiveConicProjectiveTransport c g • fiveConicNormalPoint 0)
        (fiveConicProjectiveTransport c g • fiveConicNormalPoint 1)
        (fiveConicProjectiveTransport c g • fiveConicNormalPoint lam)
        (fiveConicTransportedNormalQuadrangle c g lam hlam) := by
  simpa [fiveConicTransportedNormalDiagonal, fiveConicNormalDiagonal,
    fiveConicNormalDiagonalTwo, fiveConicNormalInfinity, diagonalAD_BC,
    fiveConicTransportedNormalQuadrangle] using
    (fiveConic_generalLinear_projectiveDiagonalAD_BC
      (fiveConicProjectiveTransport c g)
      (fiveConicNormal_completeQuadrangle hlam))

/-- The first transported normal diagonal is literally the intersection of
the two corresponding transported conic chords. -/
theorem fiveConicTransportedNormalDiagonal_zero_eq_cross_veronese
    (c : ProperCircle) (g : GL (Fin 2) ℝ) (lam : ℝ)
    (hlam : 1 < lam)
    (Pinf Pzero Pone Plam : RealProjectiveOnePoint)
    (hInf : fiveConicTransportedNormalInfinity c g =
      properCircleVeronesePoint c Pinf)
    (hZero : fiveConicTransportedNormalPoint c g 0 =
      properCircleVeronesePoint c Pzero)
    (hOne : fiveConicTransportedNormalPoint c g 1 =
      properCircleVeronesePoint c Pone)
    (hLam : fiveConicTransportedNormalPoint c g lam =
      properCircleVeronesePoint c Plam) :
    fiveConicTransportedNormalDiagonal c g lam hlam 0 =
      Projectivization.cross
        (Projectivization.cross (properCircleVeronesePoint c Pinf)
          (properCircleVeronesePoint c Pzero))
        (Projectivization.cross (properCircleVeronesePoint c Pone)
          (properCircleVeronesePoint c Plam)) := by
  let G := fiveConicProjectiveTransport c g
  have hInfNe : G • fiveConicNormalInfinity ≠ 0 :=
    (smul_ne_zero_iff_ne G).mpr fiveConicNormalInfinity_ne_zero
  have hZeroNe : G • fiveConicNormalPoint 0 ≠ 0 :=
    (smul_ne_zero_iff_ne G).mpr (fiveConicNormalPoint_ne_zero 0)
  have hOneNe : G • fiveConicNormalPoint 1 ≠ 0 :=
    (smul_ne_zero_iff_ne G).mpr (fiveConicNormalPoint_ne_zero 1)
  have hLamNe : G • fiveConicNormalPoint lam ≠ 0 :=
    (smul_ne_zero_iff_ne G).mpr (fiveConicNormalPoint_ne_zero lam)
  calc
    fiveConicTransportedNormalDiagonal c g lam hlam 0 =
        projectiveDiagonalAB_CD
          (G • fiveConicNormalInfinity)
          (G • fiveConicNormalPoint 0)
          (G • fiveConicNormalPoint 1)
          (G • fiveConicNormalPoint lam)
          (fiveConicTransportedNormalQuadrangle c g lam hlam) := by
      simpa [G] using
        fiveConicTransportedNormalDiagonal_zero_eq_projectiveDiagonal
          c g lam hlam
    _ = Projectivization.cross
          (Projectivization.cross
            (Projectivization.mk ℝ (G • fiveConicNormalInfinity) hInfNe)
            (Projectivization.mk ℝ (G • fiveConicNormalPoint 0) hZeroNe))
          (Projectivization.cross
            (Projectivization.mk ℝ (G • fiveConicNormalPoint 1) hOneNe)
            (Projectivization.mk ℝ (G • fiveConicNormalPoint lam) hLamNe)) := by
      exact projectiveDiagonalAB_CD_eq_cross_mk _ _ _ _
        (fiveConicTransportedNormalQuadrangle c g lam hlam)
        hInfNe hZeroNe hOneNe hLamNe
    _ = _ := by
      change Projectivization.cross
          (Projectivization.cross
            (fiveConicTransportedNormalInfinity c g)
            (fiveConicTransportedNormalPoint c g 0))
          (Projectivization.cross
            (fiveConicTransportedNormalPoint c g 1)
            (fiveConicTransportedNormalPoint c g lam)) = _
      rw [hInf, hZero, hOne, hLam]

/-- The second transported normal diagonal is the intersection of the
`∞,1` and `0,λ` transported chords. -/
theorem fiveConicTransportedNormalDiagonal_one_eq_cross_veronese
    (c : ProperCircle) (g : GL (Fin 2) ℝ) (lam : ℝ)
    (hlam : 1 < lam)
    (Pinf Pzero Pone Plam : RealProjectiveOnePoint)
    (hInf : fiveConicTransportedNormalInfinity c g =
      properCircleVeronesePoint c Pinf)
    (hZero : fiveConicTransportedNormalPoint c g 0 =
      properCircleVeronesePoint c Pzero)
    (hOne : fiveConicTransportedNormalPoint c g 1 =
      properCircleVeronesePoint c Pone)
    (hLam : fiveConicTransportedNormalPoint c g lam =
      properCircleVeronesePoint c Plam) :
    fiveConicTransportedNormalDiagonal c g lam hlam 1 =
      Projectivization.cross
        (Projectivization.cross (properCircleVeronesePoint c Pinf)
          (properCircleVeronesePoint c Pone))
        (Projectivization.cross (properCircleVeronesePoint c Pzero)
          (properCircleVeronesePoint c Plam)) := by
  let G := fiveConicProjectiveTransport c g
  have hInfNe : G • fiveConicNormalInfinity ≠ 0 :=
    (smul_ne_zero_iff_ne G).mpr fiveConicNormalInfinity_ne_zero
  have hZeroNe : G • fiveConicNormalPoint 0 ≠ 0 :=
    (smul_ne_zero_iff_ne G).mpr (fiveConicNormalPoint_ne_zero 0)
  have hOneNe : G • fiveConicNormalPoint 1 ≠ 0 :=
    (smul_ne_zero_iff_ne G).mpr (fiveConicNormalPoint_ne_zero 1)
  have hLamNe : G • fiveConicNormalPoint lam ≠ 0 :=
    (smul_ne_zero_iff_ne G).mpr (fiveConicNormalPoint_ne_zero lam)
  calc
    fiveConicTransportedNormalDiagonal c g lam hlam 1 =
        projectiveDiagonalAC_BD
          (G • fiveConicNormalInfinity)
          (G • fiveConicNormalPoint 0)
          (G • fiveConicNormalPoint 1)
          (G • fiveConicNormalPoint lam)
          (fiveConicTransportedNormalQuadrangle c g lam hlam) := by
      simpa [G] using
        fiveConicTransportedNormalDiagonal_one_eq_projectiveDiagonal
          c g lam hlam
    _ = Projectivization.cross
          (Projectivization.cross
            (Projectivization.mk ℝ (G • fiveConicNormalInfinity) hInfNe)
            (Projectivization.mk ℝ (G • fiveConicNormalPoint 1) hOneNe))
          (Projectivization.cross
            (Projectivization.mk ℝ (G • fiveConicNormalPoint 0) hZeroNe)
            (Projectivization.mk ℝ (G • fiveConicNormalPoint lam) hLamNe)) := by
      exact projectiveDiagonalAC_BD_eq_cross_mk _ _ _ _
        (fiveConicTransportedNormalQuadrangle c g lam hlam)
        hInfNe hZeroNe hOneNe hLamNe
    _ = _ := by
      change Projectivization.cross
          (Projectivization.cross
            (fiveConicTransportedNormalInfinity c g)
            (fiveConicTransportedNormalPoint c g 1))
          (Projectivization.cross
            (fiveConicTransportedNormalPoint c g 0)
            (fiveConicTransportedNormalPoint c g lam)) = _
      rw [hInf, hZero, hOne, hLam]

/-- The third transported normal diagonal is the intersection of the
`∞,λ` and `0,1` transported chords. -/
theorem fiveConicTransportedNormalDiagonal_two_eq_cross_veronese
    (c : ProperCircle) (g : GL (Fin 2) ℝ) (lam : ℝ)
    (hlam : 1 < lam)
    (Pinf Pzero Pone Plam : RealProjectiveOnePoint)
    (hInf : fiveConicTransportedNormalInfinity c g =
      properCircleVeronesePoint c Pinf)
    (hZero : fiveConicTransportedNormalPoint c g 0 =
      properCircleVeronesePoint c Pzero)
    (hOne : fiveConicTransportedNormalPoint c g 1 =
      properCircleVeronesePoint c Pone)
    (hLam : fiveConicTransportedNormalPoint c g lam =
      properCircleVeronesePoint c Plam) :
    fiveConicTransportedNormalDiagonal c g lam hlam 2 =
      Projectivization.cross
        (Projectivization.cross (properCircleVeronesePoint c Pinf)
          (properCircleVeronesePoint c Plam))
        (Projectivization.cross (properCircleVeronesePoint c Pzero)
          (properCircleVeronesePoint c Pone)) := by
  let G := fiveConicProjectiveTransport c g
  have hInfNe : G • fiveConicNormalInfinity ≠ 0 :=
    (smul_ne_zero_iff_ne G).mpr fiveConicNormalInfinity_ne_zero
  have hZeroNe : G • fiveConicNormalPoint 0 ≠ 0 :=
    (smul_ne_zero_iff_ne G).mpr (fiveConicNormalPoint_ne_zero 0)
  have hOneNe : G • fiveConicNormalPoint 1 ≠ 0 :=
    (smul_ne_zero_iff_ne G).mpr (fiveConicNormalPoint_ne_zero 1)
  have hLamNe : G • fiveConicNormalPoint lam ≠ 0 :=
    (smul_ne_zero_iff_ne G).mpr (fiveConicNormalPoint_ne_zero lam)
  calc
    fiveConicTransportedNormalDiagonal c g lam hlam 2 =
        projectiveDiagonalAD_BC
          (G • fiveConicNormalInfinity)
          (G • fiveConicNormalPoint 0)
          (G • fiveConicNormalPoint 1)
          (G • fiveConicNormalPoint lam)
          (fiveConicTransportedNormalQuadrangle c g lam hlam) := by
      simpa [G] using
        fiveConicTransportedNormalDiagonal_two_eq_projectiveDiagonal
          c g lam hlam
    _ = Projectivization.cross
          (Projectivization.cross
            (Projectivization.mk ℝ (G • fiveConicNormalInfinity) hInfNe)
            (Projectivization.mk ℝ (G • fiveConicNormalPoint lam) hLamNe))
          (Projectivization.cross
            (Projectivization.mk ℝ (G • fiveConicNormalPoint 0) hZeroNe)
            (Projectivization.mk ℝ (G • fiveConicNormalPoint 1) hOneNe)) := by
      exact projectiveDiagonalAD_BC_eq_cross_mk _ _ _ _
        (fiveConicTransportedNormalQuadrangle c g lam hlam)
        hInfNe hZeroNe hOneNe hLamNe
    _ = _ := by
      change Projectivization.cross
          (Projectivization.cross
            (fiveConicTransportedNormalInfinity c g)
            (fiveConicTransportedNormalPoint c g lam))
          (Projectivization.cross
            (fiveConicTransportedNormalPoint c g 0)
            (fiveConicTransportedNormalPoint c g 1)) = _
      rw [hInf, hZero, hOne, hLam]

end Erdos506.Incidence
