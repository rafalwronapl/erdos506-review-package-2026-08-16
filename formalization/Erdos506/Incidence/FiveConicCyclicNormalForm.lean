import Erdos506.Incidence.FiveConicProjectiveTransport
import Erdos506.Incidence.RealProjectiveHarmonicFiveCap

/-!
# A constructive cyclic normal form for five real conic parameters

The projective calculation for the one-single/two-double separator uses the
cyclic normal chart

`∞, 0, 1, λ, t` with `1 < λ < t`.

This file constructs that chart from five actual points of `RP¹`.  The only
inputs are distinctness and the three intrinsic cyclic-orientation facts
which say that the displayed five points occur in that order.  In
particular, `λ` and `t` are recovered from the transformed projective points;
they are not normal-form assumptions.
-/

namespace Erdos506.Incidence

open Matrix
open scoped LinearAlgebra.Projectivization

/-- The projective parameter point represented by the affine vector
`[t : 1]`. -/
noncomputable def fiveConicAffinePoint (t : ℝ) : RealProjectiveOnePoint :=
  Projectivization.mk ℝ (fiveConicAffineParameterVector t)
    (fiveConicAffineParameterVector_ne_zero t)

/-- Any non-infinite real projective parameter has its literal affine
`[t : 1]` representative. -/
theorem realProjective_eq_fiveConicAffinePoint_of_ne_infinity
    (P : RealProjectiveOnePoint)
    (hP : P ≠ realProjectiveLineInfinity) :
    P = fiveConicAffinePoint (P.rep 0 / P.rep 1) := by
  have hrepOne : P.rep 1 ≠ 0 := by
    intro hzero
    apply hP
    calc
      P = Projectivization.mk ℝ P.rep P.rep_nonzero :=
        (Projectivization.mk_rep P).symm
      _ = realProjectiveLineInfinity := by
        unfold realProjectiveLineInfinity
        apply (realProjective_mk_eq_mk_iff_bracket_eq_zero
          P.rep_nonzero realProjectiveLineInfinityVector_ne_zero).mpr
        simp [realProjectiveBracket, realProjectiveLineInfinityVector,
          hzero]
  let t : ℝ := P.rep 0 / P.rep 1
  have hraw : Projectivization.mk ℝ P.rep P.rep_nonzero =
      fiveConicAffinePoint t := by
    unfold fiveConicAffinePoint
    apply (realProjective_mk_eq_mk_iff_bracket_eq_zero
      P.rep_nonzero (fiveConicAffineParameterVector_ne_zero _)).mpr
    simp only [realProjectiveBracket, fiveConicAffineParameterVector,
      Matrix.cons_val_zero, Matrix.cons_val_one]
    dsimp [t]
    field_simp [hrepOne]
    ring
  calc
    P = Projectivization.mk ℝ P.rep P.rep_nonzero :=
      (Projectivization.mk_rep P).symm
    _ = fiveConicAffinePoint t := hraw

/-- The intrinsic cyclic order `1,t,∞` is precisely the ordinary inequality
`1 < t` in the affine parameter chart. -/
theorem one_lt_of_realProjectiveCyclic_one_affine_infinity
    (t : ℝ)
    (h : RealProjectiveCyclic realProjectiveLineOne
      (fiveConicAffinePoint t) realProjectiveLineInfinity) :
    1 < t := by
  rcases h with ⟨u, v, w, hu, hv, hw, hOne, hAffine, hInfinity, hpositive⟩
  have hOne' : Projectivization.mk ℝ realProjectiveLineOneVector
      realProjectiveLineOneVector_ne_zero = Projectivization.mk ℝ u hu := by
    simpa [realProjectiveLineOne] using hOne
  have hAffine' : Projectivization.mk ℝ (fiveConicAffineParameterVector t)
      (fiveConicAffineParameterVector_ne_zero t) = Projectivization.mk ℝ v hv := by
    simpa [fiveConicAffinePoint] using hAffine
  have hInfinity' : Projectivization.mk ℝ realProjectiveLineInfinityVector
      realProjectiveLineInfinityVector_ne_zero = Projectivization.mk ℝ w hw := by
    simpa [realProjectiveLineInfinity] using hInfinity
  obtain ⟨a, ha⟩ := (Projectivization.mk_eq_mk_iff' ℝ
    realProjectiveLineOneVector u realProjectiveLineOneVector_ne_zero hu).mp hOne'
  obtain ⟨b, hb⟩ := (Projectivization.mk_eq_mk_iff' ℝ
    (fiveConicAffineParameterVector t) v
    (fiveConicAffineParameterVector_ne_zero t) hv).mp hAffine'
  obtain ⟨c, hc⟩ := (Projectivization.mk_eq_mk_iff' ℝ
    realProjectiveLineInfinityVector w realProjectiveLineInfinityVector_ne_zero hw).mp
      hInfinity'
  have ha0 : a ≠ 0 := by
    intro ha0
    apply realProjectiveLineOneVector_ne_zero
    rw [← ha, ha0, zero_smul]
  have hb0 : b ≠ 0 := by
    intro hb0
    apply fiveConicAffineParameterVector_ne_zero t
    rw [← hb, hb0, zero_smul]
  have hc0 : c ≠ 0 := by
    intro hc0
    apply realProjectiveLineInfinityVector_ne_zero
    rw [← hc, hc0, zero_smul]
  have hscaled : 0 < realProjectiveTripleBracket
      (a • u) (b • v) (c • w) := by
    rw [realProjectiveTripleBracket_smul]
    exact mul_pos
      (sq_pos_of_ne_zero (mul_ne_zero (mul_ne_zero ha0 hb0) hc0)) hpositive
  rw [ha, hb, hc] at hscaled
  norm_num [realProjectiveTripleBracket, realProjectiveBracket,
    fiveConicAffineParameterVector, realProjectiveLineOneVector,
    realProjectiveLineInfinityVector] at hscaled
  linarith

/-- The intrinsic cyclic order `λ,t,∞` is precisely `λ < t` in the same
affine parameter chart. -/
theorem affine_lt_of_realProjectiveCyclic_affine_affine_infinity
    (lam t : ℝ)
    (h : RealProjectiveCyclic (fiveConicAffinePoint lam)
      (fiveConicAffinePoint t) realProjectiveLineInfinity) :
    lam < t := by
  rcases h with ⟨u, v, w, hu, hv, hw, hLam, hAffine, hInfinity, hpositive⟩
  have hLam' : Projectivization.mk ℝ (fiveConicAffineParameterVector lam)
      (fiveConicAffineParameterVector_ne_zero lam) = Projectivization.mk ℝ u hu := by
    simpa [fiveConicAffinePoint] using hLam
  have hAffine' : Projectivization.mk ℝ (fiveConicAffineParameterVector t)
      (fiveConicAffineParameterVector_ne_zero t) = Projectivization.mk ℝ v hv := by
    simpa [fiveConicAffinePoint] using hAffine
  have hInfinity' : Projectivization.mk ℝ realProjectiveLineInfinityVector
      realProjectiveLineInfinityVector_ne_zero = Projectivization.mk ℝ w hw := by
    simpa [realProjectiveLineInfinity] using hInfinity
  obtain ⟨a, ha⟩ := (Projectivization.mk_eq_mk_iff' ℝ
    (fiveConicAffineParameterVector lam) u
    (fiveConicAffineParameterVector_ne_zero lam) hu).mp hLam'
  obtain ⟨b, hb⟩ := (Projectivization.mk_eq_mk_iff' ℝ
    (fiveConicAffineParameterVector t) v
    (fiveConicAffineParameterVector_ne_zero t) hv).mp hAffine'
  obtain ⟨c, hc⟩ := (Projectivization.mk_eq_mk_iff' ℝ
    realProjectiveLineInfinityVector w realProjectiveLineInfinityVector_ne_zero hw).mp
      hInfinity'
  have ha0 : a ≠ 0 := by
    intro ha0
    apply fiveConicAffineParameterVector_ne_zero lam
    rw [← ha, ha0, zero_smul]
  have hb0 : b ≠ 0 := by
    intro hb0
    apply fiveConicAffineParameterVector_ne_zero t
    rw [← hb, hb0, zero_smul]
  have hc0 : c ≠ 0 := by
    intro hc0
    apply realProjectiveLineInfinityVector_ne_zero
    rw [← hc, hc0, zero_smul]
  have hscaled : 0 < realProjectiveTripleBracket
      (a • u) (b • v) (c • w) := by
    rw [realProjectiveTripleBracket_smul]
    exact mul_pos
      (sq_pos_of_ne_zero (mul_ne_zero (mul_ne_zero ha0 hb0) hc0)) hpositive
  rw [ha, hb, hc] at hscaled
  norm_num [realProjectiveTripleBracket, realProjectiveBracket,
    fiveConicAffineParameterVector, realProjectiveLineInfinityVector] at hscaled
  linarith

/-- The `GL₂` normalizer which sends the first three cyclic points to
`∞,0,1` in the indicated order. -/
noncomputable def fiveConicCyclicNormalFrame
    (Pinf Pzero Pone : RealProjectiveOnePoint)
    (hzeroInf : Pzero ≠ Pinf) (hzeroOne : Pzero ≠ Pone)
    (honeInf : Pone ≠ Pinf) : GL (Fin 2) ℝ :=
  realProjectiveTripleFrame Pzero Pinf Pone hzeroInf hzeroOne honeInf

theorem fiveConicCyclicNormalFrame_smul_zero
    (Pinf Pzero Pone : RealProjectiveOnePoint)
    (hzeroInf : Pzero ≠ Pinf) (hzeroOne : Pzero ≠ Pone)
    (honeInf : Pone ≠ Pinf) :
    fiveConicCyclicNormalFrame Pinf Pzero Pone hzeroInf hzeroOne honeInf •
        Pzero = realProjectiveLineZero := by
  simpa [fiveConicCyclicNormalFrame] using
    (realProjectiveTripleFrame_smul_left Pzero Pinf Pone
      hzeroInf hzeroOne honeInf)

theorem fiveConicCyclicNormalFrame_smul_infinity
    (Pinf Pzero Pone : RealProjectiveOnePoint)
    (hzeroInf : Pzero ≠ Pinf) (hzeroOne : Pzero ≠ Pone)
    (honeInf : Pone ≠ Pinf) :
    fiveConicCyclicNormalFrame Pinf Pzero Pone hzeroInf hzeroOne honeInf •
        Pinf = realProjectiveLineInfinity := by
  simpa [fiveConicCyclicNormalFrame] using
    (realProjectiveTripleFrame_smul_right Pzero Pinf Pone
      hzeroInf hzeroOne honeInf)

theorem fiveConicCyclicNormalFrame_smul_one
    (Pinf Pzero Pone : RealProjectiveOnePoint)
    (hzeroInf : Pzero ≠ Pinf) (hzeroOne : Pzero ≠ Pone)
    (honeInf : Pone ≠ Pinf) :
    fiveConicCyclicNormalFrame Pinf Pzero Pone hzeroInf hzeroOne honeInf •
        Pone = realProjectiveLineOne := by
  simpa [fiveConicCyclicNormalFrame] using
    (realProjectiveTripleFrame_smul_one Pzero Pinf Pone
      hzeroInf hzeroOne honeInf)

/-- The cyclic normalizer is orientation preserving whenever the three
source points occur as `∞,0,1`. -/
theorem fiveConicCyclicNormalFrame_det_pos
    (Pinf Pzero Pone : RealProjectiveOnePoint)
    (hzeroInf : Pzero ≠ Pinf) (hzeroOne : Pzero ≠ Pone)
    (honeInf : Pone ≠ Pinf)
    (hcyclic : RealProjectiveCyclic Pinf Pzero Pone) :
    0 < ((fiveConicCyclicNormalFrame Pinf Pzero Pone
      hzeroInf hzeroOne honeInf : GL (Fin 2) ℝ) :
      Matrix (Fin 2) (Fin 2) ℝ).det := by
  change 0 < Matrix.det
    (realProjectiveTripleFrameMatrix Pzero Pinf Pone)
  rw [realProjectiveTripleFrameMatrix_det Pzero Pinf Pone
    hzeroInf hzeroOne honeInf]
  have hproduct : 0 <
      realProjectiveBracket Pinf.rep Pzero.rep *
        (realProjectiveBracket Pzero.rep Pone.rep *
          realProjectiveBracket Pone.rep Pinf.rep) := by
    rw [realProjectiveCyclic_iff_rep_tripleBracket] at hcyclic
    simpa only [realProjectiveTripleBracket, mul_assoc] using hcyclic
  rw [show -realProjectiveBracket Pzero.rep Pinf.rep =
      realProjectiveBracket Pinf.rep Pzero.rep by
        rw [realProjectiveBracket_swap]
        ring]
  exact (div_pos_iff).mpr (mul_pos_iff.mp hproduct)

/-- Constructively normalize five cyclic real projective parameters to
`∞,0,1,λ,t`, with the strict inequalities demanded by the normal separator.
The two later cyclic hypotheses place the fourth and fifth points in the
affine arc from `1` to `∞`. -/
theorem exists_fiveConicCyclic_normal_form
    (Pinf Pzero Pone Plam Pt : RealProjectiveOnePoint)
    (hzeroInf : Pzero ≠ Pinf) (hzeroOne : Pzero ≠ Pone)
    (honeInf : Pone ≠ Pinf) (hlamInf : Plam ≠ Pinf)
    (htInf : Pt ≠ Pinf)
    (hbase : RealProjectiveCyclic Pinf Pzero Pone)
    (hlam : RealProjectiveCyclic Pone Plam Pinf)
    (ht : RealProjectiveCyclic Plam Pt Pinf) :
    ∃ lam t : ℝ, 1 < lam ∧ lam < t ∧
      fiveConicCyclicNormalFrame Pinf Pzero Pone
          hzeroInf hzeroOne honeInf • Pinf = realProjectiveLineInfinity ∧
        fiveConicCyclicNormalFrame Pinf Pzero Pone
            hzeroInf hzeroOne honeInf • Pzero = realProjectiveLineZero ∧
          fiveConicCyclicNormalFrame Pinf Pzero Pone
              hzeroInf hzeroOne honeInf • Pone = realProjectiveLineOne ∧
            fiveConicCyclicNormalFrame Pinf Pzero Pone
                hzeroInf hzeroOne honeInf • Plam = fiveConicAffinePoint lam ∧
              fiveConicCyclicNormalFrame Pinf Pzero Pone
                  hzeroInf hzeroOne honeInf • Pt = fiveConicAffinePoint t := by
  let g : GL (Fin 2) ℝ := fiveConicCyclicNormalFrame Pinf Pzero Pone
    hzeroInf hzeroOne honeInf
  have hgzero : g • Pzero = realProjectiveLineZero := by
    simpa [g] using fiveConicCyclicNormalFrame_smul_zero
      Pinf Pzero Pone hzeroInf hzeroOne honeInf
  have hginf : g • Pinf = realProjectiveLineInfinity := by
    simpa [g] using fiveConicCyclicNormalFrame_smul_infinity
      Pinf Pzero Pone hzeroInf hzeroOne honeInf
  have hgone : g • Pone = realProjectiveLineOne := by
    simpa [g] using fiveConicCyclicNormalFrame_smul_one
      Pinf Pzero Pone hzeroInf hzeroOne honeInf
  have hgdet : 0 < ((g : Matrix (Fin 2) (Fin 2) ℝ).det) := by
    simpa [g] using fiveConicCyclicNormalFrame_det_pos
      Pinf Pzero Pone hzeroInf hzeroOne honeInf hbase
  have hglamInf : g • Plam ≠ realProjectiveLineInfinity := by
    intro hEq
    apply hlamInf
    have hEq' : g • Plam = g • Pinf := by simpa [hginf] using hEq
    have hback := congrArg (fun Z : RealProjectiveOnePoint => g⁻¹ • Z) hEq'
    simpa [smul_smul] using hback
  have hgtInf : g • Pt ≠ realProjectiveLineInfinity := by
    intro hEq
    apply htInf
    have hEq' : g • Pt = g • Pinf := by simpa [hginf] using hEq
    have hback := congrArg (fun Z : RealProjectiveOnePoint => g⁻¹ • Z) hEq'
    simpa [smul_smul] using hback
  let lam : ℝ := (g • Plam).rep 0 / (g • Plam).rep 1
  let t : ℝ := (g • Pt).rep 0 / (g • Pt).rep 1
  have hglam : g • Plam = fiveConicAffinePoint lam := by
    simpa [lam] using
      realProjective_eq_fiveConicAffinePoint_of_ne_infinity (g • Plam)
        hglamInf
  have hgt : g • Pt = fiveConicAffinePoint t := by
    simpa [t] using
      realProjective_eq_fiveConicAffinePoint_of_ne_infinity (g • Pt) hgtInf
  have hlamImage := realProjectiveCyclic_smul_of_det_pos g hgdet hlam
  have htImage := realProjectiveCyclic_smul_of_det_pos g hgdet ht
  rw [hgone, hglam, hginf] at hlamImage
  rw [hglam, hgt, hginf] at htImage
  refine ⟨lam, t,
    one_lt_of_realProjectiveCyclic_one_affine_infinity lam hlamImage,
    affine_lt_of_realProjectiveCyclic_affine_affine_infinity lam t htImage,
    hginf, hgzero, hgone, hglam, hgt⟩

end Erdos506.Incidence
