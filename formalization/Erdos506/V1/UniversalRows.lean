import Erdos506.V1.BlockRows
import Erdos506.V1.RestoredPivot
import Erdos506.V1.LangerGrouping

/-!
# V1 universal inequalities from explicit incidence inputs

The exact rows live in `V1.BlockRows`.  This file adds only the geometric
sign conclusion supplied by an explicit real-plane Melchior principle.  The
principle remains an argument, so this module cannot be mistaken for an
unconditional proof of the still-missing projective arrangement theorem.
-/

namespace Erdos506.V1

open Erdos506.Incidence
open Erdos506.V4
open scoped BigOperators

universe u

theorem sigma_nonneg_of_realPlaneMelchior
    {α : Type u} [Fintype α] [DecidableEq α]
    (M : RealPlaneMelchiorPrinciple.{u})
    (cfg : Configuration α) (hadm : Admissible cfg)
    (hcard : 3 ≤ Fintype.card α) (p : α) :
    0 ≤ sigma cfg p := by
  change 0 ≤ (geometricBlockSystem cfg).pivotSigma p
  have hnoncol : Noncollinear (Erdos506.V3.pivotInversion cfg p) :=
    pivotInversion_noncollinear cfg hadm hcard p
  have hmel : LineMelchior (Erdos506.V3.pivotInversion cfg p) :=
    M.lineMelchior (Erdos506.V3.pivotInversion cfg p) hnoncol
  exact pivotSigma_nonneg_of_lineMelchior cfg p hmel

/-- The global `P` inequality obtained by summing all pivot Melchior
slacks. -/
theorem three_n_le_rowP_of_realPlaneMelchior
    {α : Type u} [Fintype α] [DecidableEq α]
    (M : RealPlaneMelchiorPrinciple.{u})
    (cfg : Configuration α) (hadm : Admissible cfg)
    (hcard : 3 ≤ Fintype.card α) :
    3 * (Fintype.card α : ℤ) ≤ rowP cfg := by
  have hnonneg : 0 ≤ ∑ p : α, sigma cfg p := by
    exact Finset.sum_nonneg fun p _hp =>
      sigma_nonneg_of_realPlaneMelchior M cfg hadm hcard p
  rw [sum_sigma_eq_rowP_sub_three_n] at hnonneg
  omega

theorem kappa_nonneg_of_realPlaneMelchior
    {α : Type u} [Fintype α] [DecidableEq α]
    (M : RealPlaneMelchiorPrinciple.{u})
    (cfg : Configuration α) (hadm : Admissible cfg)
    (hcard : 3 ≤ Fintype.card α) (p : α) :
    0 ≤ kappa cfg p := by
  change 0 ≤ (geometricBlockSystem cfg).restoredKappa p
  have hnoncol : Noncollinear (restoredPivotConfiguration cfg p) :=
    restoredPivotConfiguration_noncollinear cfg hadm hcard p
  have hmel : LineMelchior (restoredPivotConfiguration cfg p) :=
    M.lineMelchior (restoredPivotConfiguration cfg p) hnoncol
  exact restoredKappa_nonneg_of_lineMelchior cfg p hmel

/-- The global `D` inequality obtained by summing the restored-centre
Melchior slacks. -/
theorem rowD_le_n_mul_n_sub_four_of_realPlaneMelchior
    {α : Type u} [Fintype α] [DecidableEq α]
    (M : RealPlaneMelchiorPrinciple.{u})
    (cfg : Configuration α) (hadm : Admissible cfg)
    (hcard : 3 ≤ Fintype.card α) :
    rowD cfg ≤
      (Fintype.card α : ℤ) * ((Fintype.card α : ℤ) - 4) := by
  have hnonneg : 0 ≤ ∑ p : α, kappa cfg p := by
    exact Finset.sum_nonneg fun p _hp =>
      kappa_nonneg_of_realPlaneMelchior M cfg hadm hcard p
  rw [sum_kappa_eq_n_mul_n_sub_four_sub_rowD] at hnonneg
  omega

/-- Direct Melchior on the original determined lines gives the manuscript's
global line row. -/
theorem globalLineRow_le_choose_two_sub_three_of_realPlaneMelchior
    {α : Type u} [Fintype α] [DecidableEq α]
    (M : RealPlaneMelchiorPrinciple.{u})
    (cfg : Configuration α) (hadm : Admissible cfg) :
    globalLineRow cfg ≤ (Nat.choose (Fintype.card α) 2 : ℤ) - 3 := by
  have hmel : LineMelchior cfg := M.lineMelchior cfg hadm.1
  have hslack : 0 ≤ globalLineSlack cfg :=
    globalLineSlack_nonneg_of_lineMelchior cfg hmel
  rw [← choose_two_sub_three_sub_globalLineRow_eq_globalLineSlack] at hslack
  omega

/-- The manuscript's conditional Langer row, scaled by three to avoid
division.  The occupancy cap is kept explicit for every pivot image. -/
theorem n_mul_n_sub_one_mul_n_add_two_le_three_rowL_of_realPlaneLanger
    {α : Type u} [Fintype α] [DecidableEq α]
    (L : RealPlaneLangerPrinciple.{u})
    (cfg : Configuration α) (hadm : Admissible cfg)
    (hcard : 3 ≤ Fintype.card α)
    (hocc : ∀ p : α,
      LineOccupancyTwoThirds (Erdos506.V3.pivotInversion cfg p)) :
    (Fintype.card α : ℤ) * ((Fintype.card α : ℤ) - 1) *
        ((Fintype.card α : ℤ) + 2) ≤
      3 * rowL cfg := by
  let localLanger (p : α) : ℤ :=
    ∑ s ∈ (geometricBlockSystem cfg).nontrivialSizes,
      ((s : ℤ) - 1) *
        ((geometricBlockSystem cfg).blockDegree s p : ℤ)
  have hlocal (p : α) :
      ((Fintype.card α : ℤ) - 1) *
          ((Fintype.card α : ℤ) + 2) ≤ 3 * localLanger p := by
    have hnoncol : Noncollinear (Erdos506.V3.pivotInversion cfg p) :=
      pivotInversion_noncollinear cfg hadm hcard p
    have hbound := L.incidenceBound
      (Erdos506.V3.pivotInversion cfg p) hnoncol (hocc p)
    have haway :
        ((Fintype.card (Erdos506.V3.AwayFrom p) : ℤ)) =
          (Fintype.card α : ℤ) - 1 := by
      rw [Erdos506.V3.card_awayFrom]
      omega
    calc
      ((Fintype.card α : ℤ) - 1) *
          ((Fintype.card α : ℤ) + 2) =
          (Fintype.card (Erdos506.V3.AwayFrom p) : ℤ) *
            ((Fintype.card (Erdos506.V3.AwayFrom p) : ℤ) + 3) := by
        rw [haway]
        ring
      _ ≤ 3 * lineIncidence (Erdos506.V3.pivotInversion cfg p) := hbound
      _ = 3 * localLanger p := by
        unfold localLanger
        rw [pivotLangerSum_eq_lineIncidence]
  have hsum :
      (∑ _p : α,
        ((Fintype.card α : ℤ) - 1) *
          ((Fintype.card α : ℤ) + 2)) ≤
        ∑ p : α, 3 * localLanger p :=
    Finset.sum_le_sum fun p _hp => hlocal p
  have hrow := rowL_eq_sum_local_weighted_degree cfg
  change rowL cfg =
    ∑ p : α, ∑ s ∈ (geometricBlockSystem cfg).nontrivialSizes,
      ((s : ℤ) - 1) *
        ((geometricBlockSystem cfg).blockDegree s p : ℤ) at hrow
  calc
    (Fintype.card α : ℤ) * ((Fintype.card α : ℤ) - 1) *
        ((Fintype.card α : ℤ) + 2) =
        ∑ _p : α,
          ((Fintype.card α : ℤ) - 1) *
            ((Fintype.card α : ℤ) + 2) := by
      simp
      ring
    _ ≤ ∑ p : α, 3 * localLanger p := hsum
    _ = 3 * rowL cfg := by
      rw [← Finset.mul_sum]
      unfold localLanger
      rw [hrow]

end Erdos506.V1
