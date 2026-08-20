import Erdos506.V1.HalfCap

/-!
# The thirteen-point five-circle endpoint

This file formalizes the solver-free transfer in the five-circle branch of
the thirteen-point V1 proof.  The only geometric input is the explicit
real-plane Melchior interface already used by the universal `P` and `D` rows.
-/

namespace Erdos506.V1

open Erdos506.Block
open Erdos506.Block.BlockSystem
open Erdos506.Incidence
open Erdos506.V4
open scoped BigOperators

universe u

private theorem blockCount_eq_zero_of_cap
    {Point Block : Type*} [Fintype Point] [Fintype Block]
    [DecidableEq Point]
    (S : BlockSystem Point Block) {M s : ℕ}
    (hcap : BlockSizeCap S M) (hthree : 3 ≤ s) (hlarge : M < s) :
    S.blockCount s = 0 := by
  classical
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro b hb
  have hsize := S.mem_blocksOfSize.mp hb
  have hle := hcap b (by omega)
  omega

private theorem lineCount_eq_zero_of_cap
    {Point Block : Type*} [Fintype Point] [Fintype Block]
    [DecidableEq Point]
    (S : BlockSystem Point Block) {M s : ℕ}
    (hcap : BlockSizeCap S M) (hthree : 3 ≤ s) (hlarge : M < s) :
    S.lineCount s = 0 := by
  classical
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro b hb
  have hspec := S.mem_blocksOfKindSize.mp hb
  have hle := hcap b (by rw [hspec.2]; exact hthree)
  omega

private theorem circleCount_eq_zero_of_kind_cap
    {Point Block : Type*} [Fintype Point] [Fintype Block]
    [DecidableEq Point]
    (S : BlockSystem Point Block) {M s : ℕ}
    (hcap : ∀ b : Block, S.kind b = .circle → (S.support b).card ≤ M)
    (hlarge : M < s) :
    S.circleCount s = 0 := by
  classical
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro b hb
  have hspec := S.mem_blocksOfKindSize.mp hb
  have hle := hcap b hspec.1
  omega

private theorem blockDegree_eq_zero_of_blockCount_eq_zero
    {Point Block : Type*} [Fintype Point] [Fintype Block]
    [DecidableEq Point]
    (S : BlockSystem Point Block) (s : ℕ) (p : Point)
    (hzero : S.blockCount s = 0) :
    S.blockDegree s p = 0 := by
  have hinc := S.block_incidence s
  rw [hzero] at hinc
  have hle : S.blockDegree s p ≤ ∑ q : Point, S.blockDegree s q :=
    Finset.single_le_sum
      (fun q _hq => Nat.zero_le (S.blockDegree s q)) (Finset.mem_univ p)
  omega

private theorem blockDegree_le_blockCount
    {Point Block : Type*} [Fintype Point] [Fintype Block]
    [DecidableEq Point]
    (S : BlockSystem Point Block) (s : ℕ) (p : Point) :
    S.blockDegree s p ≤ S.blockCount s := by
  unfold BlockSystem.blockDegree BlockSystem.degreeIn BlockSystem.blockCount
  exact Finset.card_filter_le _ _

private theorem lineSupport_card_le_six_of_thirteen_of_circleCount_le_sixty
    {α : Type u} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (hadm : Admissible cfg)
    (hcard : Fintype.card α = 13)
    (hcount : Erdos506.V4.circleCount cfg ≤ 60)
    (L : DeterminedLine cfg) :
    (lineSupport cfg L).card ≤ 6 := by
  let s := (lineSupport cfg L).card
  by_contra hnot
  have hlarge : 7 ≤ s := by
    dsimp only [s]
    omega
  have hproper :
      (geometricBlockSupport cfg (Sum.inl L)).card < Fintype.card α :=
    geometricBlockSupport_card_lt_of_admissible cfg hadm (Sum.inl L)
  have hsmall : s ≤ 12 := by
    change s < Fintype.card α at hproper
    rw [hcard] at hproper
    omega
  have hpencil := richLinePencilBound_le_totalCircleCount
    (blockSystem cfg) (Sum.inl L) rfl
  rw [totalCircleCount_eq_card_determinedCircle,
    ← Erdos506.V3.circleCount_eq_card_determinedCircle] at hpencil
  rw [hcard] at hpencil
  change
    (13 - s) * Nat.choose s 2 - Nat.choose (13 - s) 2 * (s / 2) ≤
      Erdos506.V4.circleCount cfg at hpencil
  interval_cases s <;>
    norm_num [Nat.choose] at hpencil <;>
    omega

private theorem blockSizeCap_six_of_thirteen_of_circleCount_le
    {α : Type u} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (hadm : Admissible cfg)
    (hcard : Fintype.card α = 13)
    (hcount : Erdos506.V4.circleCount cfg ≤ 60)
    (hfive : ∀ c : DeterminedCircle cfg,
      (circleTrace cfg c.1).card ≤ 5) :
    BlockSizeCap (blockSystem cfg) 6 := by
  intro b _hthree
  cases b with
  | inl L =>
      simpa [blockSystem, geometricBlockSystem, geometricBlockSupport] using
        lineSupport_card_le_six_of_thirteen_of_circleCount_le_sixty
          cfg hadm hcard hcount L
  | inr c =>
      have hc := hfive c
      change (circleTrace cfg c.1).card ≤ 6
      omega

private theorem thirteen_five_global_rows
    {α : Type u} [Fintype α] [DecidableEq α]
    (Mel : RealPlaneMelchiorPrinciple.{u})
    (cfg : Configuration α) (hadm : Admissible cfg)
    (hcard : Fintype.card α = 13)
    (hcount : Erdos506.V4.circleCount cfg ≤ 60)
    (hfive : ∀ c : DeterminedCircle cfg,
      (circleTrace cfg c.1).card ≤ 5) :
    let S := blockSystem cfg
    ((S.blockCount 3 : ℤ) + 4 * (S.blockCount 4 : ℤ) +
        10 * (S.blockCount 5 : ℤ) + 20 * (S.blockCount 6 : ℤ) = 286) ∧
    (3 * (S.blockCount 3 : ℤ) - 5 * (S.blockCount 5 : ℤ) -
        12 * (S.blockCount 6 : ℤ) =
      39 + ∑ p : α, S.pivotSigma p) ∧
    (12 * (S.blockCount 4 : ℤ) + 35 * (S.blockCount 5 : ℤ) +
        72 * (S.blockCount 6 : ℤ) =
      819 - ∑ p : α, S.pivotSigma p) ∧
    ((S.totalCircleCount : ℤ) =
      (S.circleCount 3 : ℤ) + (S.circleCount 4 : ℤ) +
        (S.circleCount 5 : ℤ)) ∧
    (S.blockCount 3 = S.lineCount 3 + S.circleCount 3) ∧
    (S.blockCount 4 = S.lineCount 4 + S.circleCount 4) ∧
    (S.blockCount 5 = S.lineCount 5 + S.circleCount 5) ∧
    (S.blockCount 6 = S.lineCount 6) ∧
    (5 * (S.lineCount 3 : ℤ) + 12 * (S.lineCount 4 : ℤ) +
        20 * (S.lineCount 5 : ℤ) + 28 * (S.lineCount 6 : ℤ) ≤
      4 * (S.totalCircleCount : ℤ) - 169 + (S.circleCount 5 : ℤ)) ∧
    (5 * (3 * (S.lineCount 3 : ℤ) + 4 * (S.lineCount 4 : ℤ) +
        10 * (S.lineCount 5 : ℤ) + 12 * (S.lineCount 6 : ℤ)) ≤
      3 * (5 * (S.lineCount 3 : ℤ) + 12 * (S.lineCount 4 : ℤ) +
        20 * (S.lineCount 5 : ℤ) + 28 * (S.lineCount 6 : ℤ))) ∧
    (24 * 286 +
        27 * (3 * (S.blockCount 3 : ℤ) - 5 * (S.blockCount 5 : ℤ) -
          12 * (S.blockCount 6 : ℤ)) ≤
      35 * (3 * (S.lineCount 3 : ℤ) + 4 * (S.lineCount 4 : ℤ) +
        10 * (S.lineCount 5 : ℤ) + 12 * (S.lineCount 6 : ℤ) +
          3 * (S.totalCircleCount : ℤ))) := by
  classical
  dsimp only
  let S := blockSystem cfg
  have hcap : BlockSizeCap S 6 := by
    simpa [S] using blockSizeCap_six_of_thirteen_of_circleCount_le
      cfg hadm hcard hcount hfive
  have hcircleCap : ∀ b, S.kind b = .circle → (S.support b).card ≤ 5 := by
    intro b hb
    cases b with
    | inl L => cases hb
    | inr c =>
        simpa [S, blockSystem, geometricBlockSystem,
          geometricBlockKind, geometricBlockSupport] using hfive c
  have hb7 : S.blockCount 7 = 0 :=
    blockCount_eq_zero_of_cap S hcap (by omega) (by omega)
  have hb8 : S.blockCount 8 = 0 :=
    blockCount_eq_zero_of_cap S hcap (by omega) (by omega)
  have hb9 : S.blockCount 9 = 0 :=
    blockCount_eq_zero_of_cap S hcap (by omega) (by omega)
  have hb10 : S.blockCount 10 = 0 :=
    blockCount_eq_zero_of_cap S hcap (by omega) (by omega)
  have hb11 : S.blockCount 11 = 0 :=
    blockCount_eq_zero_of_cap S hcap (by omega) (by omega)
  have hb12 : S.blockCount 12 = 0 :=
    blockCount_eq_zero_of_cap S hcap (by omega) (by omega)
  have hb13 : S.blockCount 13 = 0 :=
    blockCount_eq_zero_of_cap S hcap (by omega) (by omega)
  have hl7 : S.lineCount 7 = 0 :=
    lineCount_eq_zero_of_cap S hcap (by omega) (by omega)
  have hl8 : S.lineCount 8 = 0 :=
    lineCount_eq_zero_of_cap S hcap (by omega) (by omega)
  have hl9 : S.lineCount 9 = 0 :=
    lineCount_eq_zero_of_cap S hcap (by omega) (by omega)
  have hl10 : S.lineCount 10 = 0 :=
    lineCount_eq_zero_of_cap S hcap (by omega) (by omega)
  have hl11 : S.lineCount 11 = 0 :=
    lineCount_eq_zero_of_cap S hcap (by omega) (by omega)
  have hl12 : S.lineCount 12 = 0 :=
    lineCount_eq_zero_of_cap S hcap (by omega) (by omega)
  have hl13 : S.lineCount 13 = 0 :=
    lineCount_eq_zero_of_cap S hcap (by omega) (by omega)
  have hc0 : S.circleCount 0 = 0 :=
    S.circleCount_eq_zero_of_lt_three (by omega)
  have hc1 : S.circleCount 1 = 0 :=
    S.circleCount_eq_zero_of_lt_three (by omega)
  have hc2 : S.circleCount 2 = 0 :=
    S.circleCount_eq_zero_of_lt_three (by omega)
  have hc6 : S.circleCount 6 = 0 :=
    circleCount_eq_zero_of_kind_cap S hcircleCap (by omega)
  have hc7 : S.circleCount 7 = 0 :=
    circleCount_eq_zero_of_kind_cap S hcircleCap (by omega)
  have hc8 : S.circleCount 8 = 0 :=
    circleCount_eq_zero_of_kind_cap S hcircleCap (by omega)
  have hc9 : S.circleCount 9 = 0 :=
    circleCount_eq_zero_of_kind_cap S hcircleCap (by omega)
  have hc10 : S.circleCount 10 = 0 :=
    circleCount_eq_zero_of_kind_cap S hcircleCap (by omega)
  have hc11 : S.circleCount 11 = 0 :=
    circleCount_eq_zero_of_kind_cap S hcircleCap (by omega)
  have hc12 : S.circleCount 12 = 0 :=
    circleCount_eq_zero_of_kind_cap S hcircleCap (by omega)
  have hc13 : S.circleCount 13 = 0 :=
    circleCount_eq_zero_of_kind_cap S hcircleCap (by omega)
  have hT := S.triple_partition_by_size
  rw [hcard] at hT
  norm_num [Finset.sum_range_succ, Nat.choose,
    hb7, hb8, hb9, hb10, hb11, hb12, hb13] at hT
  have hTz :
      (S.blockCount 3 : ℤ) + 4 * (S.blockCount 4 : ℤ) +
          10 * (S.blockCount 5 : ℤ) + 20 * (S.blockCount 6 : ℤ) = 286 := by
    exact_mod_cast hT
  have hsumSigma := S.sum_pivotSigma_eq_pivotRow_sub_three_n
  simp only [BlockSystem.pivotRow, BlockSystem.nontrivialSizes] at hsumSigma
  rw [hcard] at hsumSigma
  have hIcc : Finset.Icc 3 13 = {3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13} := by
    decide
  rw [hIcc] at hsumSigma
  norm_num [hb7, hb8, hb9, hb10, hb11, hb12, hb13] at hsumSigma
  have hQ :
      3 * (S.blockCount 3 : ℤ) - 5 * (S.blockCount 5 : ℤ) -
          12 * (S.blockCount 6 : ℤ) =
        39 + ∑ p : α, S.pivotSigma p := by
    omega
  have hBlock :
      12 * (S.blockCount 4 : ℤ) + 35 * (S.blockCount 5 : ℤ) +
          72 * (S.blockCount 6 : ℤ) =
        819 - ∑ p : α, S.pivotSigma p := by
    omega
  have htotalEq := S.totalCircleCount_eq_sum_circleCount
  rw [hcard] at htotalEq
  norm_num [Finset.sum_range_succ, hc0, hc1, hc2, hc6, hc7, hc8,
    hc9, hc10, hc11, hc12, hc13] at htotalEq
  have htotalZ :
      (S.totalCircleCount : ℤ) =
        (S.circleCount 3 : ℤ) + (S.circleCount 4 : ℤ) +
          (S.circleCount 5 : ℤ) := by
    exact_mod_cast htotalEq
  have hsplit3 := S.blockCount_eq_lineCount_add_circleCount 3
  have hsplit4 := S.blockCount_eq_lineCount_add_circleCount 4
  have hsplit5 := S.blockCount_eq_lineCount_add_circleCount 5
  have hsplit6raw := S.blockCount_eq_lineCount_add_circleCount 6
  rw [hc6, add_zero] at hsplit6raw
  have hD := rowD_le_n_mul_n_sub_four_of_realPlaneMelchior
    (α := α) Mel cfg hadm (by omega)
  change S.defectRow ≤
    (Fintype.card α : ℤ) * ((Fintype.card α : ℤ) - 4) at hD
  simp only [BlockSystem.defectRow, BlockSystem.nontrivialSizes] at hD
  rw [hcard, hIcc] at hD
  norm_num [hl7, hl8, hl9, hl10, hl11, hl12, hl13,
    hc6, hc7, hc8, hc9, hc10, hc11, hc12, hc13] at hD
  have hAupper :
      5 * (S.lineCount 3 : ℤ) + 12 * (S.lineCount 4 : ℤ) +
          20 * (S.lineCount 5 : ℤ) + 28 * (S.lineCount 6 : ℤ) ≤
        4 * (S.totalCircleCount : ℤ) - 169 + (S.circleCount 5 : ℤ) := by
    omega
  have hAlower :
      5 * (3 * (S.lineCount 3 : ℤ) + 4 * (S.lineCount 4 : ℤ) +
          10 * (S.lineCount 5 : ℤ) + 12 * (S.lineCount 6 : ℤ)) ≤
        3 * (5 * (S.lineCount 3 : ℤ) + 12 * (S.lineCount 4 : ℤ) +
          20 * (S.lineCount 5 : ℤ) + 28 * (S.lineCount 6 : ℤ)) := by
    omega
  have htransfer :
      24 * 286 +
          27 * (3 * (S.blockCount 3 : ℤ) - 5 * (S.blockCount 5 : ℤ) -
            12 * (S.blockCount 6 : ℤ)) ≤
        35 * (3 * (S.lineCount 3 : ℤ) + 4 * (S.lineCount 4 : ℤ) +
          10 * (S.lineCount 5 : ℤ) + 12 * (S.lineCount 6 : ℤ) +
            3 * (S.totalCircleCount : ℤ)) := by
    omega
  exact ⟨hTz, hQ, hBlock, htotalZ, hsplit3, hsplit4, hsplit5,
    hsplit6raw, hAupper, hAlower, htransfer⟩

/-! The remaining global elimination is Presburger arithmetic.  These small
lemmas keep each certificate sparse enough for deterministic replay. -/

private theorem thirteen_five_endpoint_bounds
    (C B4 B5 B6 C5 : ℕ) (K A S : ℤ)
    (hcount : C ≤ 60) (hK : 0 ≤ K)
    (hBlock : 12 * (B4 : ℤ) + 35 * (B5 : ℤ) + 72 * (B6 : ℤ) = 819 - K)
    (hC5le : C5 ≤ B5)
    (hAupper : A ≤ 4 * (C : ℤ) - 169 + (C5 : ℤ))
    (hAlower : 5 * S ≤ 3 * A)
    (htransfer : 24 * 286 + 27 * (39 + K) ≤ 35 * (S + 3 * (C : ℤ))) :
    59 ≤ C ∧ B5 ≤ 23 := by
  omega

private theorem thirteen_five_rich_line_identity
    (C B3 B4 B5 B6 C3 C4 C5 L3 L4 L5 L6 : ℕ) (K : ℤ)
    (hT : (B3 : ℤ) + 4 * (B4 : ℤ) + 10 * (B5 : ℤ) +
      20 * (B6 : ℤ) = 286)
    (hQ : 3 * (B3 : ℤ) - 5 * (B5 : ℤ) - 12 * (B6 : ℤ) = 39 + K)
    (htotal : (C : ℤ) = (C3 : ℤ) + (C4 : ℤ) + (C5 : ℤ))
    (hsplit3 : B3 = L3 + C3) (hsplit4 : B4 = L4 + C4)
    (hsplit5 : B5 = L5 + C5) (hsplit6 : B6 = L6) :
    4 * ((L3 : ℤ) + (L4 : ℤ) + (L5 : ℤ) + (L6 : ℤ)) =
      325 - 4 * (C : ℤ) - (B5 : ℤ) - 4 * (B6 : ℤ) + K := by
  have hsplit3z : (B3 : ℤ) = (L3 : ℤ) + (C3 : ℤ) := by
    exact_mod_cast hsplit3
  have hsplit4z : (B4 : ℤ) = (L4 : ℤ) + (C4 : ℤ) := by
    exact_mod_cast hsplit4
  have hsplit5z : (B5 : ℤ) = (L5 : ℤ) + (C5 : ℤ) := by
    exact_mod_cast hsplit5
  have hsplit6z : (B6 : ℤ) = (L6 : ℤ) := by
    exact_mod_cast hsplit6
  have hsumSplit :
      (B3 : ℤ) + (B4 : ℤ) + (B5 : ℤ) + (B6 : ℤ) =
        (L3 : ℤ) + (L4 : ℤ) + (L5 : ℤ) + (L6 : ℤ) + (C : ℤ) := by
    linear_combination hsplit3z + hsplit4z + hsplit5z + hsplit6z - htotal
  have hBQ :
      4 * ((B3 : ℤ) + (B4 : ℤ) + (B5 : ℤ) + (B6 : ℤ)) =
        325 + K - (B5 : ℤ) - 4 * (B6 : ℤ) := by
    linear_combination hT + hQ
  linear_combination hBQ - 4 * hsumSplit

private theorem thirteen_five_B5_lower
    (C B5 B6 C5 L3 L4 L5 L6 : ℕ) (K : ℤ)
    (hC5le : C5 ≤ B5) (hsplit6 : B6 = L6)
    (hL : 4 * ((L3 : ℤ) + (L4 : ℤ) + (L5 : ℤ) + (L6 : ℤ)) =
      325 - 4 * (C : ℤ) - (B5 : ℤ) - 4 * (B6 : ℤ) + K)
    (hAupper :
      5 * (L3 : ℤ) + 12 * (L4 : ℤ) + 20 * (L5 : ℤ) + 28 * (L6 : ℤ) ≤
        4 * (C : ℤ) - 169 + (C5 : ℤ)) :
    2301 - 36 * (C : ℤ) + 5 * K + 72 * (B6 : ℤ) ≤ 9 * (B5 : ℤ) := by
  omega

private theorem thirteen_five_profiles
    (C B3 B4 B5 B6 : ℕ) (K : ℤ)
    (hcount : C ≤ 60) (hCge : 59 ≤ C) (hK : 0 ≤ K) (hB5le : B5 ≤ 23)
    (hQ : 3 * (B3 : ℤ) - 5 * (B5 : ℤ) - 12 * (B6 : ℤ) = 39 + K)
    (hBlock : 12 * (B4 : ℤ) + 35 * (B5 : ℤ) + 72 * (B6 : ℤ) = 819 - K)
    (hB5lower :
      2301 - 36 * (C : ℤ) + 5 * K + 72 * (B6 : ℤ) ≤ 9 * (B5 : ℤ)) :
    B6 = 0 ∧
      ((K = 0 ∧ B3 = 48 ∧ B4 = 7 ∧ B5 = 21) ∨
       (K = 1 ∧ B3 = 50 ∧ B4 = 4 ∧ B5 = 22) ∨
       (K = 2 ∧ B3 = 52 ∧ B4 = 1 ∧ B5 = 23)) := by
  have hB6 : B6 = 0 := by omega
  have hB5ge : 16 ≤ B5 := by omega
  refine ⟨hB6, ?_⟩
  interval_cases B5 <;> omega

private theorem thirteen_five_point_row
    {Point Block : Type*} [Fintype Point] [Fintype Block]
    [DecidableEq Point]
    (S : BlockSystem Point Block) (hcard : Fintype.card Point = 13)
    (hcap : BlockSizeCap S 6) (hB6 : S.blockCount 6 = 0)
    (p : Point) :
    7 * (S.blockDegree 5 p : ℤ) + 3 * (S.blockDegree 4 p : ℤ) =
      63 - S.pivotSigma p := by
  have hb7 : S.blockCount 7 = 0 :=
    blockCount_eq_zero_of_cap S hcap (by omega) (by omega)
  have hb8 : S.blockCount 8 = 0 :=
    blockCount_eq_zero_of_cap S hcap (by omega) (by omega)
  have hb9 : S.blockCount 9 = 0 :=
    blockCount_eq_zero_of_cap S hcap (by omega) (by omega)
  have hb10 : S.blockCount 10 = 0 :=
    blockCount_eq_zero_of_cap S hcap (by omega) (by omega)
  have hb11 : S.blockCount 11 = 0 :=
    blockCount_eq_zero_of_cap S hcap (by omega) (by omega)
  have hb12 : S.blockCount 12 = 0 :=
    blockCount_eq_zero_of_cap S hcap (by omega) (by omega)
  have hb13 : S.blockCount 13 = 0 :=
    blockCount_eq_zero_of_cap S hcap (by omega) (by omega)
  have hd6 := blockDegree_eq_zero_of_blockCount_eq_zero S 6 p hB6
  have hd7 := blockDegree_eq_zero_of_blockCount_eq_zero S 7 p hb7
  have hd8 := blockDegree_eq_zero_of_blockCount_eq_zero S 8 p hb8
  have hd9 := blockDegree_eq_zero_of_blockCount_eq_zero S 9 p hb9
  have hd10 := blockDegree_eq_zero_of_blockCount_eq_zero S 10 p hb10
  have hd11 := blockDegree_eq_zero_of_blockCount_eq_zero S 11 p hb11
  have hd12 := blockDegree_eq_zero_of_blockCount_eq_zero S 12 p hb12
  have hd13 := blockDegree_eq_zero_of_blockCount_eq_zero S 13 p hb13
  have hpairs := S.pivot_pair_partition p
  rw [hcard] at hpairs
  norm_num [Finset.sum_range_succ, Nat.choose, hd6, hd7, hd8, hd9,
    hd10, hd11, hd12, hd13] at hpairs
  have hsigma :
      S.pivotSigma p =
        (S.blockDegree 3 p : ℤ) - (S.blockDegree 5 p : ℤ) - 3 := by
    unfold BlockSystem.pivotSigma BlockSystem.nontrivialSizes
    rw [hcard]
    have hIcc :
        Finset.Icc 3 13 = {3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13} := by
      decide
    rw [hIcc]
    norm_num [hd6, hd7, hd8, hd9, hd10, hd11, hd12, hd13]
    ring
  omega

private theorem thirteen_five_profile_zero_impossible
    {Point Block : Type*} [Fintype Point] [Fintype Block]
    [DecidableEq Point]
    (S : BlockSystem Point Block) (hcard : Fintype.card Point = 13)
    (hcap : BlockSizeCap S 6) (hB6 : S.blockCount 6 = 0)
    (hB4 : S.blockCount 4 = 7)
    (hsigma : ∀ p : Point, 0 ≤ S.pivotSigma p)
    (hK : (∑ p : Point, S.pivotSigma p) = 0) : False := by
  classical
  have hsigmaZero (p : Point) : S.pivotSigma p = 0 := by
    have hsingle :
        S.pivotSigma p ≤ ∑ q : Point, S.pivotSigma q :=
      Finset.single_le_sum (fun q _hq => hsigma q) (Finset.mem_univ p)
    rw [hK] at hsingle
    have hnonneg := hsigma p
    omega
  have hdichotomy (p : Point) :
      S.blockDegree 4 p = 0 ∨ S.blockDegree 4 p = 7 := by
    have hrow := thirteen_five_point_row S hcard hcap hB6 p
    rw [hsigmaZero p] at hrow
    have hle := blockDegree_le_blockCount S 4 p
    rw [hB4] at hle
    omega
  have hchoose (p : Point) :
      Nat.choose (S.blockDegree 4 p) 2 = 3 * S.blockDegree 4 p := by
    rcases hdichotomy p with hzero | hseven
    · simp [hzero]
    · simp [hseven, Nat.choose]
  have hinc := S.block_incidence 4
  have hsumChoose :
      (∑ p : Point, Nat.choose (S.blockDegree 4 p) 2) = 84 := by
    calc
      (∑ p : Point, Nat.choose (S.blockDegree 4 p) 2) =
          ∑ p : Point, 3 * S.blockDegree 4 p := by
            apply Fintype.sum_congr
            exact hchoose
      _ = 3 * ∑ p : Point, S.blockDegree 4 p := by
            rw [Finset.mul_sum]
      _ = 84 := by rw [hinc, hB4]
  have hmoment := S.second_moment_le_two_choose (S.blocksOfSize 4)
  change
    (∑ p : Point, Nat.choose (S.blockDegree 4 p) 2) ≤
      2 * Nat.choose (S.blockCount 4) 2 at hmoment
  rw [hsumChoose, hB4] at hmoment
  norm_num [Nat.choose] at hmoment

private theorem thirteen_five_profile_one_impossible
    {Point Block : Type*} [Fintype Point] [Fintype Block]
    [DecidableEq Point]
    (S : BlockSystem Point Block) (hcard : Fintype.card Point = 13)
    (hcap : BlockSizeCap S 6) (hB6 : S.blockCount 6 = 0)
    (hB4 : S.blockCount 4 = 4) (hB5 : S.blockCount 5 = 22)
    (hsigma : ∀ p : Point, 0 ≤ S.pivotSigma p)
    (hK : (∑ p : Point, S.pivotSigma p) = 1) : False := by
  have hsigmaLe (p : Point) : S.pivotSigma p ≤ 1 := by
    have hsingle :
        S.pivotSigma p ≤ ∑ q : Point, S.pivotSigma q :=
      Finset.single_le_sum (fun q _hq => hsigma q) (Finset.mem_univ p)
    rw [hK] at hsingle
    exact hsingle
  have hd5 (p : Point) :
      (S.blockDegree 5 p : ℤ) = 9 - S.pivotSigma p := by
    have hrow := thirteen_five_point_row S hcard hcap hB6 p
    have hle := blockDegree_le_blockCount S 4 p
    rw [hB4] at hle
    have hnonneg := hsigma p
    have hupper := hsigmaLe p
    omega
  have hinc5 := S.block_incidence 5
  have hinc5z :
      (∑ p : Point, (S.blockDegree 5 p : ℤ)) =
        5 * (S.blockCount 5 : ℤ) := by
    exact_mod_cast hinc5
  have hsum5 :
      (∑ p : Point, (S.blockDegree 5 p : ℤ)) = 116 := by
    calc
      (∑ p : Point, (S.blockDegree 5 p : ℤ)) =
          ∑ p : Point, (9 - S.pivotSigma p) := by
            apply Fintype.sum_congr
            exact hd5
      _ = 116 := by
        rw [Finset.sum_sub_distrib, hK]
        simp [hcard]
  rw [hB5] at hinc5z
  norm_num at hinc5z
  omega

private theorem thirteen_five_profile_two_impossible
    {Point Block : Type*} [Fintype Point] [Fintype Block]
    [DecidableEq Point]
    (S : BlockSystem Point Block) (hcard : Fintype.card Point = 13)
    (hcap : BlockSizeCap S 6) (hB6 : S.blockCount 6 = 0)
    (hB4 : S.blockCount 4 = 1)
    (hsigma : ∀ p : Point, 0 ≤ S.pivotSigma p)
    (hK : (∑ p : Point, S.pivotSigma p) = 2) : False := by
  classical
  have hexists : ∃ p : Point, 0 < S.pivotSigma p := by
    by_contra hnone
    have hall (p : Point) : S.pivotSigma p ≤ 0 := by
      by_contra hnot
      have hpos : 0 < S.pivotSigma p := by omega
      exact hnone ⟨p, hpos⟩
    have hzero (p : Point) : S.pivotSigma p = 0 := by
      exact le_antisymm (hall p) (hsigma p)
    have hsumzero : (∑ p : Point, S.pivotSigma p) = 0 := by
      simp [hzero]
    omega
  obtain ⟨p, hp⟩ := hexists
  have hsigmaLe : S.pivotSigma p ≤ 2 := by
    have hsingle :
        S.pivotSigma p ≤ ∑ q : Point, S.pivotSigma q :=
      Finset.single_le_sum (fun q _hq => hsigma q) (Finset.mem_univ p)
    rw [hK] at hsingle
    exact hsingle
  have hrow := thirteen_five_point_row S hcard hcap hB6 p
  have hdegree := blockDegree_le_blockCount S 4 p
  rw [hB4] at hdegree
  have hd5le : S.blockDegree 5 p ≤ 8 := by omega
  interval_cases hd5 : S.blockDegree 5 p <;> omega

/-- If every determined proper circle contains at most five selected labels,
then an admissible thirteen-point V1 configuration determines at least
sixty-one proper circles. -/
theorem circleCount_ge_sixty_one_of_card_thirteen_of_circleTrace_le_five
    {α : Type u} [Fintype α] [DecidableEq α]
    (Mel : RealPlaneMelchiorPrinciple.{u})
    (cfg : Configuration α) (hadm : Admissible cfg)
    (hcard : Fintype.card α = 13)
    (hfive : ∀ c : DeterminedCircle cfg,
      (circleTrace cfg c.1).card ≤ 5) :
    61 ≤ Erdos506.V4.circleCount cfg := by
  classical
  by_contra hnot
  have hcount : Erdos506.V4.circleCount cfg ≤ 60 := by omega
  let S := blockSystem cfg
  have hcap : BlockSizeCap S 6 := by
    simpa [S] using blockSizeCap_six_of_thirteen_of_circleCount_le
      cfg hadm hcard hcount hfive
  have hrows :
      ((S.blockCount 3 : ℤ) + 4 * (S.blockCount 4 : ℤ) +
          10 * (S.blockCount 5 : ℤ) + 20 * (S.blockCount 6 : ℤ) = 286) ∧
      (3 * (S.blockCount 3 : ℤ) - 5 * (S.blockCount 5 : ℤ) -
          12 * (S.blockCount 6 : ℤ) =
        39 + ∑ p : α, S.pivotSigma p) ∧
      (12 * (S.blockCount 4 : ℤ) + 35 * (S.blockCount 5 : ℤ) +
          72 * (S.blockCount 6 : ℤ) =
        819 - ∑ p : α, S.pivotSigma p) ∧
      ((S.totalCircleCount : ℤ) =
        (S.circleCount 3 : ℤ) + (S.circleCount 4 : ℤ) +
          (S.circleCount 5 : ℤ)) ∧
      (S.blockCount 3 = S.lineCount 3 + S.circleCount 3) ∧
      (S.blockCount 4 = S.lineCount 4 + S.circleCount 4) ∧
      (S.blockCount 5 = S.lineCount 5 + S.circleCount 5) ∧
      (S.blockCount 6 = S.lineCount 6) ∧
      (5 * (S.lineCount 3 : ℤ) + 12 * (S.lineCount 4 : ℤ) +
          20 * (S.lineCount 5 : ℤ) + 28 * (S.lineCount 6 : ℤ) ≤
        4 * (S.totalCircleCount : ℤ) - 169 + (S.circleCount 5 : ℤ)) ∧
      (5 * (3 * (S.lineCount 3 : ℤ) + 4 * (S.lineCount 4 : ℤ) +
          10 * (S.lineCount 5 : ℤ) + 12 * (S.lineCount 6 : ℤ)) ≤
        3 * (5 * (S.lineCount 3 : ℤ) + 12 * (S.lineCount 4 : ℤ) +
          20 * (S.lineCount 5 : ℤ) + 28 * (S.lineCount 6 : ℤ))) ∧
      (24 * 286 +
          27 * (3 * (S.blockCount 3 : ℤ) - 5 * (S.blockCount 5 : ℤ) -
            12 * (S.blockCount 6 : ℤ)) ≤
        35 * (3 * (S.lineCount 3 : ℤ) + 4 * (S.lineCount 4 : ℤ) +
          10 * (S.lineCount 5 : ℤ) + 12 * (S.lineCount 6 : ℤ) +
            3 * (S.totalCircleCount : ℤ))) := by
    simpa [S] using thirteen_five_global_rows Mel cfg hadm hcard hcount hfive
  rcases hrows with
    ⟨hT, hQ, hBlock, htotal, hsplit3, hsplit4, hsplit5,
      hsplit6, hAupper, hAlower, htransfer⟩
  have htotalLe : S.totalCircleCount ≤ 60 := by
    rw [totalCircleCount_eq_card_determinedCircle,
      ← Erdos506.V3.circleCount_eq_card_determinedCircle]
    exact hcount
  have hsigma (p : α) : 0 ≤ S.pivotSigma p := by
    have h := sigma_nonneg_of_realPlaneMelchior
      (α := α) Mel cfg hadm (by omega) p
    simpa [S, sigma] using h
  have hK : 0 ≤ ∑ p : α, S.pivotSigma p :=
    Finset.sum_nonneg fun p _hp => hsigma p
  have hC5le : S.circleCount 5 ≤ S.blockCount 5 := by omega
  have htransfer' :
      24 * 286 + 27 * (39 + ∑ p : α, S.pivotSigma p) ≤
        35 *
          (3 * (S.lineCount 3 : ℤ) + 4 * (S.lineCount 4 : ℤ) +
            10 * (S.lineCount 5 : ℤ) + 12 * (S.lineCount 6 : ℤ) +
              3 * (S.totalCircleCount : ℤ)) := by
    omega
  let A : ℤ :=
    5 * (S.lineCount 3 : ℤ) + 12 * (S.lineCount 4 : ℤ) +
      20 * (S.lineCount 5 : ℤ) + 28 * (S.lineCount 6 : ℤ)
  let W : ℤ :=
    3 * (S.lineCount 3 : ℤ) + 4 * (S.lineCount 4 : ℤ) +
      10 * (S.lineCount 5 : ℤ) + 12 * (S.lineCount 6 : ℤ)
  have hbounds := thirteen_five_endpoint_bounds
    S.totalCircleCount (S.blockCount 4) (S.blockCount 5) (S.blockCount 6)
      (S.circleCount 5) (∑ p : α, S.pivotSigma p) A W
      htotalLe hK hBlock hC5le (by simpa [A] using hAupper)
      (by simpa [A, W] using hAlower) (by simpa [W] using htransfer')
  have hL := thirteen_five_rich_line_identity
    S.totalCircleCount (S.blockCount 3) (S.blockCount 4) (S.blockCount 5)
      (S.blockCount 6) (S.circleCount 3) (S.circleCount 4)
      (S.circleCount 5) (S.lineCount 3) (S.lineCount 4)
      (S.lineCount 5) (S.lineCount 6) (∑ p : α, S.pivotSigma p)
      hT hQ htotal hsplit3 hsplit4 hsplit5 hsplit6
  have hB5lower := thirteen_five_B5_lower
    S.totalCircleCount (S.blockCount 5) (S.blockCount 6) (S.circleCount 5)
      (S.lineCount 3) (S.lineCount 4) (S.lineCount 5) (S.lineCount 6)
      (∑ p : α, S.pivotSigma p) hC5le hsplit6 hL hAupper
  have hprofiles := thirteen_five_profiles
    S.totalCircleCount (S.blockCount 3) (S.blockCount 4) (S.blockCount 5)
      (S.blockCount 6) (∑ p : α, S.pivotSigma p)
      htotalLe hbounds.1 hK hbounds.2 hQ hBlock hB5lower
  rcases hprofiles with ⟨hB6, hprofile⟩
  rcases hprofile with
    ⟨hK0, _hB3, hB4, _hB5⟩ |
      ⟨hK1, _hB3, hB4, hB5⟩ |
      ⟨hK2, _hB3, hB4, _hB5⟩
  · exact thirteen_five_profile_zero_impossible
      S hcard hcap hB6 hB4 hsigma hK0
  · exact thirteen_five_profile_one_impossible
      S hcard hcap hB6 hB4 hB5 hsigma hK1
  · exact thirteen_five_profile_two_impossible
      S hcard hcap hB6 hB4 hsigma hK2

end Erdos506.V1
