import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Erdos506.Block.Counts

/-!
# Weighted incidence bound for five-blocks

This module isolates the finite double count used by the eleven-point
four-star argument.  A distinguished point family contributes four
five-block incidences at each of its points.  Five-lines are charged at their
trivial support capacity five, while five-circles may be charged at any
stronger supplied capacity.
-/

namespace Erdos506.Block

open scoped BigOperators

namespace BlockSystem

variable {Point Block : Type*} [Fintype Point] [Fintype Block]
  [DecidableEq Point]

/-- If every point of `H` has four incidences with the size-five line/circle
layers and every size-five circle contains at most two points of `H`, then
the weighted global incidence bound is `4|H| ≤ 5L₅ + 2C₅`. -/
theorem four_mul_card_le_five_mul_lineCount_add_two_mul_circleCount
    (S : BlockSystem Point Block) (H : Finset Point)
    (hdegree : ∀ p ∈ H,
      S.lineDegree 5 p + S.circleDegree 5 p = 4)
    (hcircle : ∀ b ∈ S.circleBlocksOfSize 5,
      (H ∩ S.support b).card ≤ 2) :
    4 * H.card ≤ 5 * S.lineCount 5 + 2 * S.circleCount 5 := by
  classical
  have hlineFubini := S.sum_degreeIn_over (S.lineBlocksOfSize 5) H
  have hcircleFubini := S.sum_degreeIn_over (S.circleBlocksOfSize 5) H
  have htotal :
      4 * H.card =
        (∑ p ∈ H, S.lineDegree 5 p) +
          ∑ p ∈ H, S.circleDegree 5 p := by
    calc
      4 * H.card = ∑ _p ∈ H, 4 := by
        simp [Nat.mul_comm]
      _ = ∑ p ∈ H, (S.lineDegree 5 p + S.circleDegree 5 p) := by
        apply Finset.sum_congr rfl
        intro p hp
        exact (hdegree p hp).symm
      _ = (∑ p ∈ H, S.lineDegree 5 p) +
          ∑ p ∈ H, S.circleDegree 5 p := by
        rw [Finset.sum_add_distrib]
  have hline :
      (∑ p ∈ H, S.lineDegree 5 p) ≤ 5 * S.lineCount 5 := by
    change (∑ p ∈ H, S.degreeIn (S.lineBlocksOfSize 5) p) ≤ _
    rw [hlineFubini]
    calc
      (∑ b ∈ S.lineBlocksOfSize 5, (H ∩ S.support b).card) ≤
          ∑ _b ∈ S.lineBlocksOfSize 5, 5 := by
        apply Finset.sum_le_sum
        intro b hb
        calc
          (H ∩ S.support b).card ≤ (S.support b).card := by
            exact Finset.card_le_card (Finset.inter_subset_right)
          _ = 5 := (S.mem_blocksOfKindSize.mp hb).2
      _ = 5 * S.lineCount 5 := by
        simp [lineCount, Nat.mul_comm]
  have hcircles :
      (∑ p ∈ H, S.circleDegree 5 p) ≤ 2 * S.circleCount 5 := by
    change (∑ p ∈ H, S.degreeIn (S.circleBlocksOfSize 5) p) ≤ _
    rw [hcircleFubini]
    calc
      (∑ b ∈ S.circleBlocksOfSize 5, (H ∩ S.support b).card) ≤
          ∑ _b ∈ S.circleBlocksOfSize 5, 2 := by
        exact Finset.sum_le_sum fun b hb => hcircle b hb
      _ = 2 * S.circleCount 5 := by
        simp [circleCount, Nat.mul_comm]
  omega

end BlockSystem

end Erdos506.Block
