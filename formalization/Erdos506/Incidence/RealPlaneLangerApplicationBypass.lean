import Erdos506.V1.UniversalRows

/-!
# A cap-sensitive incidence bound from Melchior

This module records the elementary incidence estimate needed by the
application-specific replacement for Langer.  It uses only the line-pair
partition and Melchior.  For a line of size `d` under a cap `K`, the entire
coefficient calculation is the nonnegative slack

`3 * (d - 2) * (K - d)`.

The result is weaker than Langer, but becomes sufficient in the large V1
range once the rich-block pencil has lowered the cap.
-/

namespace Erdos506.Incidence

open Erdos506.Block
open Erdos506.Block.BlockSystem
open Erdos506.V1
open Erdos506.V4
open scoped BigOperators

private theorem two_mul_choose_two (n : Nat) :
    2 * Nat.choose n 2 = n * (n - 1) := by
  have h := Nat.choose_succ_right_eq n 1
  simp only [Nat.reduceAdd, Nat.choose_one_right] at h
  omega

/-- Melchior plus a maximum line size `K` gives a linear incidence bound.

This is deliberately stated directly for a real configuration, but its
proof after `hmel` is purely finite. -/
theorem six_choose_two_add_six_cap_le_cap_add_three_mul_lineIncidence
    {Point : Type*} [Fintype Point] [DecidableEq Point]
    (cfg : Configuration Point) (K : Nat)
    (hmel : LineMelchior cfg)
    (hcap : ∀ L : DeterminedLine cfg, (lineSupport cfg L).card ≤ K) :
    6 * (Nat.choose (Fintype.card Point) 2 : Int) + 6 * (K : Int) ≤
      ((K : Int) + 3) * lineIncidence cfg := by
  classical
  have hpair :
      (∑ L : DeterminedLine cfg,
          Nat.choose (lineSupport cfg L).card 2) =
        Nat.choose (Fintype.card Point) 2 := by
    have hsum :
        (∑ b : LineBlock (blockSystem cfg),
            Nat.choose ((blockSystem cfg).support b.1).card 2) =
          ∑ L : DeterminedLine cfg,
            Nat.choose (lineSupport cfg L).card 2 := by
      apply Fintype.sum_equiv (lineBlockEquiv cfg)
      intro b
      rcases b with ⟨b, hb⟩
      cases b with
      | inl L => rfl
      | inr c => cases hb
    rw [← hsum]
    exact (blockSystem cfg).line_pair_partition
  have hpoint (L : DeterminedLine cfg) :
      6 * (Nat.choose (lineSupport cfg L).card 2 : Int) +
          2 * (K : Int) *
            (3 - ((lineSupport cfg L).card : Int)) ≤
        ((K : Int) + 3) * ((lineSupport cfg L).card : Int) := by
    let d := (lineSupport cfg L).card
    have hdTwo : 2 ≤ d := two_le_lineSupport_card cfg L
    have hdCap : d ≤ K := hcap L
    have hchooseNat := two_mul_choose_two d
    have hchooseCast := congrArg (fun z : Nat => (z : Int)) hchooseNat
    have hchooseInt :
        2 * (Nat.choose d 2 : Int) =
          (d : Int) * ((d : Int) - 1) := by
      push_cast [Nat.cast_sub (by omega : 1 ≤ d)] at hchooseCast
      exact hchooseCast
    have hdTwoInt : (2 : Int) ≤ (d : Int) := by exact_mod_cast hdTwo
    have hdCapInt : (d : Int) ≤ (K : Int) := by exact_mod_cast hdCap
    have hnonneg :
        0 ≤ 3 * ((d : Int) - 2) * ((K : Int) - (d : Int)) := by
      exact mul_nonneg
        (mul_nonneg (by norm_num) (sub_nonneg.mpr hdTwoInt))
        (sub_nonneg.mpr hdCapInt)
    dsimp only [d] at hchooseInt hnonneg ⊢
    nlinarith
  have hsumPoint :
      (∑ L : DeterminedLine cfg,
          (6 * (Nat.choose (lineSupport cfg L).card 2 : Int) +
            2 * (K : Int) *
              (3 - ((lineSupport cfg L).card : Int)))) ≤
        ∑ L : DeterminedLine cfg,
          ((K : Int) + 3) * ((lineSupport cfg L).card : Int) :=
    Finset.sum_le_sum fun L _hL => hpoint L
  have hfinite :
      6 * (Nat.choose (Fintype.card Point) 2 : Int) +
          2 * (K : Int) *
            (∑ L : DeterminedLine cfg,
              (3 - ((lineSupport cfg L).card : Int))) ≤
        ((K : Int) + 3) * lineIncidence cfg := by
    have hpairInt :
        (∑ L : DeterminedLine cfg,
            (Nat.choose (lineSupport cfg L).card 2 : Int)) =
          (Nat.choose (Fintype.card Point) 2 : Int) := by
      exact_mod_cast hpair
    calc
      6 * (Nat.choose (Fintype.card Point) 2 : Int) +
            2 * (K : Int) *
              (∑ L : DeterminedLine cfg,
                (3 - ((lineSupport cfg L).card : Int))) =
          ∑ L : DeterminedLine cfg,
            (6 * (Nat.choose (lineSupport cfg L).card 2 : Int) +
              2 * (K : Int) *
                (3 - ((lineSupport cfg L).card : Int))) := by
            rw [Finset.sum_add_distrib, ← Finset.mul_sum,
              ← Finset.mul_sum, hpairInt]
      _ ≤ ∑ L : DeterminedLine cfg,
            ((K : Int) + 3) * ((lineSupport cfg L).card : Int) := hsumPoint
      _ = ((K : Int) + 3) * lineIncidence cfg := by
            simp only [lineIncidence, Finset.mul_sum]
  have hmelMul :
      6 * (K : Int) ≤
        2 * (K : Int) *
          (∑ L : DeterminedLine cfg,
            (3 - ((lineSupport cfg L).card : Int))) := by
    unfold LineMelchior at hmel
    have hKnonneg : 0 ≤ 2 * (K : Int) := by positivity
    nlinarith
  nlinarith [hmelMul, hfinite]

end Erdos506.Incidence

namespace Erdos506.V1

open Erdos506.Block.BlockSystem
open Erdos506.Incidence
open Erdos506.V3
open Erdos506.V4
open scoped BigOperators

universe u

/-- Summed pivot form of the cap-sensitive Melchior incidence bound. -/
theorem cap_add_two_mul_rowL_lower_of_realPlaneMelchior
    {α : Type u} [Fintype α] [DecidableEq α]
    (Mel : RealPlaneMelchiorPrinciple.{u})
    (cfg : Configuration α) (hadm : Admissible cfg)
    (hcard : 3 ≤ Fintype.card α) (M : Nat) (hM : 3 ≤ M)
    (hcap : ∀ b : GeometricBlock cfg,
      3 ≤ (geometricBlockSupport cfg b).card →
        (geometricBlockSupport cfg b).card ≤ M) :
    (Fintype.card α : Int) *
        (6 * (Nat.choose (Fintype.card α - 1) 2 : Int) +
          6 * ((M - 1 : Nat) : Int)) ≤
      ((M : Int) + 2) * rowL cfg := by
  let localIncidence (p : α) : Int :=
    lineIncidence (pivotInversion cfg p)
  have hlocal (p : α) :
      6 * (Nat.choose (Fintype.card α - 1) 2 : Int) +
          6 * ((M - 1 : Nat) : Int) ≤
        ((M : Int) + 2) * localIncidence p := by
    have hnoncol : Noncollinear (pivotInversion cfg p) :=
      pivotInversion_noncollinear cfg hadm hcard p
    have hmel : LineMelchior (pivotInversion cfg p) :=
      Mel.lineMelchior (pivotInversion cfg p) hnoncol
    have hpivotCap : ∀ L : DeterminedLine (pivotInversion cfg p),
        (lineSupport (pivotInversion cfg p) L).card ≤ M - 1 := by
      intro L
      obtain ⟨b, rfl⟩ := blockToPivotLine_surjective cfg p L
      have hbcap := hcap b.1 b.2.2
      have hbcard := card_lineSupport_blockToPivotLine cfg p b
      omega
    have hbound :=
      six_choose_two_add_six_cap_le_cap_add_three_mul_lineIncidence
        (pivotInversion cfg p) (M - 1) hmel hpivotCap
    rw [card_awayFrom] at hbound
    push_cast [Nat.cast_sub (by omega : 1 ≤ M)] at hbound
    dsimp only [localIncidence]
    push_cast [Nat.cast_sub (by omega : 1 ≤ M)]
    nlinarith
  have hsum :
      (∑ _p : α,
          (6 * (Nat.choose (Fintype.card α - 1) 2 : Int) +
            6 * ((M - 1 : Nat) : Int))) ≤
        ∑ p : α, ((M : Int) + 2) * localIncidence p :=
    Finset.sum_le_sum fun p _hp => hlocal p
  have hincidenceSum :
      (∑ p : α, localIncidence p) = rowL cfg := by
    have hrow := rowL_eq_sum_local_weighted_degree cfg
    change rowL cfg =
      ∑ p : α, ∑ s ∈ (geometricBlockSystem cfg).nontrivialSizes,
        ((s : Int) - 1) *
          ((geometricBlockSystem cfg).blockDegree s p : Int) at hrow
    rw [hrow]
    apply Fintype.sum_congr
    intro p
    exact (pivotLangerSum_eq_lineIncidence cfg p).symm
  calc
    (Fintype.card α : Int) *
        (6 * (Nat.choose (Fintype.card α - 1) 2 : Int) +
          6 * ((M - 1 : Nat) : Int)) =
        ∑ _p : α,
          (6 * (Nat.choose (Fintype.card α - 1) 2 : Int) +
            6 * ((M - 1 : Nat) : Int)) := by simp
    _ ≤ ∑ p : α, ((M : Int) + 2) * localIncidence p := hsum
    _ = ((M : Int) + 2) * rowL cfg := by
      rw [← Finset.mul_sum, hincidenceSum]

end Erdos506.V1
