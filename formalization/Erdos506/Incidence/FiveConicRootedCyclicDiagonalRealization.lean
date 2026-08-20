import Erdos506.Incidence.FiveConicRootedCyclicTrace
import Erdos506.Incidence.FiveConicTransportedNormalDiagonals

/-!
# Actual chord realization of the rooted normal diagonals

The rooted cyclic normal form supplies projective points.  This file makes
the last identification needed by the C39 one-single page argument: its
three normal diagonals are literally the intersections of the three pairs of
actual selected chords.  The result contains only real projective
equalities; no extra incidence or normalisation premise is exposed.
-/

namespace Erdos506.Incidence

open Erdos506.V3
open Erdos506.V4
open scoped LinearAlgebra.Projectivization

universe u

private theorem properCircleVeronesePoint_fiveConicRootedCyclicParameter
    {α : Type u} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (Gamma : DeterminedCircle cfg)
    (hGamma : (circleTrace cfg Gamma.1).card = 5)
    (r i : Fin 5) :
    properCircleVeronesePoint Gamma.1
      (fiveConicRootedCyclicParameter cfg Gamma hGamma r i) =
        projectivePoint
          (cfg (fiveConicRootedCyclicLabel cfg Gamma hGamma r i).1) := by
  rw [properCircleVeronesePoint_eq_projectivePoint,
    properCircleProjectiveParam_fiveConicRootedCyclicParameter]

/-- Constructively realize the three normal diagonal centres as intersections
of actual selected chords.  Indices `0,1,2,3` are the four trace labels
after the selected page mark has been rooted at index `4`. -/
theorem exists_fiveConicTraceRootedCyclic_diagonal_realization
    {α : Type u} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (Gamma : DeterminedCircle cfg)
    (hGamma : (circleTrace cfg Gamma.1).card = 5) (r : Fin 5) :
    ∃ (g : GL (Fin 2) ℝ) (lam t : ℝ) (hlam : 1 < lam), lam < t ∧
      fiveConicTransportedNormalPoint Gamma.1 g⁻¹ t =
        projectivePoint
          (cfg (fiveConicRootedCyclicLabel cfg Gamma hGamma r 4).1) ∧
      fiveConicTransportedNormalDiagonal Gamma.1 g⁻¹ lam hlam 0 =
        Projectivization.cross
          (projectiveLine
            (cfg (fiveConicRootedCyclicLabel cfg Gamma hGamma r 0).1)
            (cfg (fiveConicRootedCyclicLabel cfg Gamma hGamma r 1).1)
            (cfg.injective.ne
              (fiveConicRootedCyclicLabel_ne cfg Gamma hGamma r 0 1
                (by decide))))
          (projectiveLine
            (cfg (fiveConicRootedCyclicLabel cfg Gamma hGamma r 2).1)
            (cfg (fiveConicRootedCyclicLabel cfg Gamma hGamma r 3).1)
            (cfg.injective.ne
              (fiveConicRootedCyclicLabel_ne cfg Gamma hGamma r 2 3
                (by decide)))) ∧
      fiveConicTransportedNormalDiagonal Gamma.1 g⁻¹ lam hlam 1 =
        Projectivization.cross
          (projectiveLine
            (cfg (fiveConicRootedCyclicLabel cfg Gamma hGamma r 0).1)
            (cfg (fiveConicRootedCyclicLabel cfg Gamma hGamma r 2).1)
            (cfg.injective.ne
              (fiveConicRootedCyclicLabel_ne cfg Gamma hGamma r 0 2
                (by decide))))
          (projectiveLine
            (cfg (fiveConicRootedCyclicLabel cfg Gamma hGamma r 1).1)
            (cfg (fiveConicRootedCyclicLabel cfg Gamma hGamma r 3).1)
            (cfg.injective.ne
              (fiveConicRootedCyclicLabel_ne cfg Gamma hGamma r 1 3
                (by decide)))) ∧
      fiveConicTransportedNormalDiagonal Gamma.1 g⁻¹ lam hlam 2 =
        Projectivization.cross
          (projectiveLine
            (cfg (fiveConicRootedCyclicLabel cfg Gamma hGamma r 0).1)
            (cfg (fiveConicRootedCyclicLabel cfg Gamma hGamma r 3).1)
            (cfg.injective.ne
              (fiveConicRootedCyclicLabel_ne cfg Gamma hGamma r 0 3
                (by decide))))
          (projectiveLine
            (cfg (fiveConicRootedCyclicLabel cfg Gamma hGamma r 1).1)
            (cfg (fiveConicRootedCyclicLabel cfg Gamma hGamma r 2).1)
            (cfg.injective.ne
              (fiveConicRootedCyclicLabel_ne cfg Gamma hGamma r 1 2
                (by decide)))) := by
  obtain ⟨g, lam, t, _hgdet, hlam, hlt, hInf, hZero, hOne, hLam, hMark⟩ :=
    exists_fiveConicTraceRootedCyclic_projective_normal_form
      cfg Gamma hGamma r
  let P : Fin 5 → RealProjectiveOnePoint :=
    fiveConicRootedCyclicParameter cfg Gamma hGamma r
  have hP0 : properCircleVeronesePoint Gamma.1 (P 0) =
      projectivePoint
        (cfg (fiveConicRootedCyclicLabel cfg Gamma hGamma r 0).1) := by
    simpa [P] using
      properCircleVeronesePoint_fiveConicRootedCyclicParameter
        cfg Gamma hGamma r 0
  have hP1 : properCircleVeronesePoint Gamma.1 (P 1) =
      projectivePoint
        (cfg (fiveConicRootedCyclicLabel cfg Gamma hGamma r 1).1) := by
    simpa [P] using
      properCircleVeronesePoint_fiveConicRootedCyclicParameter
        cfg Gamma hGamma r 1
  have hP2 : properCircleVeronesePoint Gamma.1 (P 2) =
      projectivePoint
        (cfg (fiveConicRootedCyclicLabel cfg Gamma hGamma r 2).1) := by
    simpa [P] using
      properCircleVeronesePoint_fiveConicRootedCyclicParameter
        cfg Gamma hGamma r 2
  have hP3 : properCircleVeronesePoint Gamma.1 (P 3) =
      projectivePoint
        (cfg (fiveConicRootedCyclicLabel cfg Gamma hGamma r 3).1) := by
    simpa [P] using
      properCircleVeronesePoint_fiveConicRootedCyclicParameter
        cfg Gamma hGamma r 3
  have hP4 : properCircleVeronesePoint Gamma.1 (P 4) =
      projectivePoint
        (cfg (fiveConicRootedCyclicLabel cfg Gamma hGamma r 4).1) := by
    simpa [P] using
      properCircleVeronesePoint_fiveConicRootedCyclicParameter
        cfg Gamma hGamma r 4
  have h01 : cfg (fiveConicRootedCyclicLabel cfg Gamma hGamma r 0).1 ≠
      cfg (fiveConicRootedCyclicLabel cfg Gamma hGamma r 1).1 :=
    cfg.injective.ne
      (fiveConicRootedCyclicLabel_ne cfg Gamma hGamma r 0 1 (by decide))
  have h23 : cfg (fiveConicRootedCyclicLabel cfg Gamma hGamma r 2).1 ≠
      cfg (fiveConicRootedCyclicLabel cfg Gamma hGamma r 3).1 :=
    cfg.injective.ne
      (fiveConicRootedCyclicLabel_ne cfg Gamma hGamma r 2 3 (by decide))
  have h02 : cfg (fiveConicRootedCyclicLabel cfg Gamma hGamma r 0).1 ≠
      cfg (fiveConicRootedCyclicLabel cfg Gamma hGamma r 2).1 :=
    cfg.injective.ne
      (fiveConicRootedCyclicLabel_ne cfg Gamma hGamma r 0 2 (by decide))
  have h13 : cfg (fiveConicRootedCyclicLabel cfg Gamma hGamma r 1).1 ≠
      cfg (fiveConicRootedCyclicLabel cfg Gamma hGamma r 3).1 :=
    cfg.injective.ne
      (fiveConicRootedCyclicLabel_ne cfg Gamma hGamma r 1 3 (by decide))
  have h03 : cfg (fiveConicRootedCyclicLabel cfg Gamma hGamma r 0).1 ≠
      cfg (fiveConicRootedCyclicLabel cfg Gamma hGamma r 3).1 :=
    cfg.injective.ne
      (fiveConicRootedCyclicLabel_ne cfg Gamma hGamma r 0 3 (by decide))
  have h12 : cfg (fiveConicRootedCyclicLabel cfg Gamma hGamma r 1).1 ≠
      cfg (fiveConicRootedCyclicLabel cfg Gamma hGamma r 2).1 :=
    cfg.injective.ne
      (fiveConicRootedCyclicLabel_ne cfg Gamma hGamma r 1 2 (by decide))
  refine ⟨g, lam, t, hlam, hlt, ?_, ?_, ?_, ?_⟩
  · calc
      fiveConicTransportedNormalPoint Gamma.1 g⁻¹ t =
          properCircleVeronesePoint Gamma.1 (P 4) := by
        simpa [P] using hMark
      _ = _ := hP4
  · calc
      fiveConicTransportedNormalDiagonal Gamma.1 g⁻¹ lam hlam 0 =
          Projectivization.cross
            (Projectivization.cross (properCircleVeronesePoint Gamma.1 (P 0))
              (properCircleVeronesePoint Gamma.1 (P 1)))
            (Projectivization.cross (properCircleVeronesePoint Gamma.1 (P 2))
              (properCircleVeronesePoint Gamma.1 (P 3))) := by
        simpa [P] using
          fiveConicTransportedNormalDiagonal_zero_eq_cross_veronese
            Gamma.1 g⁻¹ lam hlam (P 0) (P 1) (P 2) (P 3)
            hInf hZero hOne hLam
      _ = _ := by
        rw [hP0, hP1, hP2, hP3,
          projectivePoint_cross_eq_projectiveLine h01,
          projectivePoint_cross_eq_projectiveLine h23]
  · calc
      fiveConicTransportedNormalDiagonal Gamma.1 g⁻¹ lam hlam 1 =
          Projectivization.cross
            (Projectivization.cross (properCircleVeronesePoint Gamma.1 (P 0))
              (properCircleVeronesePoint Gamma.1 (P 2)))
            (Projectivization.cross (properCircleVeronesePoint Gamma.1 (P 1))
              (properCircleVeronesePoint Gamma.1 (P 3))) := by
        simpa [P] using
          fiveConicTransportedNormalDiagonal_one_eq_cross_veronese
            Gamma.1 g⁻¹ lam hlam (P 0) (P 1) (P 2) (P 3)
            hInf hZero hOne hLam
      _ = _ := by
        rw [hP0, hP1, hP2, hP3,
          projectivePoint_cross_eq_projectiveLine h02,
          projectivePoint_cross_eq_projectiveLine h13]
  · calc
      fiveConicTransportedNormalDiagonal Gamma.1 g⁻¹ lam hlam 2 =
          Projectivization.cross
            (Projectivization.cross (properCircleVeronesePoint Gamma.1 (P 0))
              (properCircleVeronesePoint Gamma.1 (P 3)))
            (Projectivization.cross (properCircleVeronesePoint Gamma.1 (P 1))
              (properCircleVeronesePoint Gamma.1 (P 2))) := by
        simpa [P] using
          fiveConicTransportedNormalDiagonal_two_eq_cross_veronese
            Gamma.1 g⁻¹ lam hlam (P 0) (P 1) (P 2) (P 3)
            hInf hZero hOne hLam
      _ = _ := by
        rw [hP0, hP1, hP2, hP3,
          projectivePoint_cross_eq_projectiveLine h03,
          projectivePoint_cross_eq_projectiveLine h12]

end Erdos506.Incidence
