import Erdos506.Block.RelativeTwoTwoCapacity
import Erdos506.Incidence.RadicalAxisCrossBlockPrinciple

/-!
# Combinatorial part of the cross-block capacity

The `5 + 4` bound does not require radical-axis geometry.  It follows from
unique ownership of triples in the geometric block system: after fixing a
pair on the four-point side, the two-point traces on the five-point side form
a matching.  This leaves only the sharper `4 + 4` bound as geometric input.
-/

namespace Erdos506.Incidence

open Erdos506.Block.BlockSystem
open Erdos506.V1
open Erdos506.V4

universe u

/-- Exclusive traces in the two directions are disjoint. -/
private theorem exclusiveCircleTrace_disjoint
    {α : Type*} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (Γ Ω : DeterminedCircle cfg) :
    Disjoint (exclusiveCircleTrace cfg Γ Ω)
      (exclusiveCircleTrace cfg Ω Γ) := by
  classical
  rw [Finset.disjoint_left]
  intro x hxΓ hxΩ
  have hxΓ' := Finset.mem_sdiff.mp hxΓ
  have hxΩ' := Finset.mem_sdiff.mp hxΩ
  exact hxΓ'.2 hxΩ'.1

/-- The cross-block capacity for exclusive traces of sizes five and four is
purely combinatorial; unique triple ownership already gives the bound `12`.
-/
theorem circleCrossBlocks_card_le_twelve_of_five_four
    {α : Type*} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (Γ Ω : DeterminedCircle cfg)
    (hfive : (exclusiveCircleTrace cfg Γ Ω).card = 5)
    (hfour : (exclusiveCircleTrace cfg Ω Γ).card = 4) :
    (circleCrossBlocks cfg Γ Ω).card ≤ 12 := by
  classical
  let D := exclusiveCircleTrace cfg Γ Ω
  let E := exclusiveCircleTrace cfg Ω Γ
  let F := circleCrossBlocks cfg Γ Ω
  have hDE : Disjoint D E := by
    exact exclusiveCircleTrace_disjoint cfg Γ Ω
  have htwoD : ∀ b ∈ F,
      ((geometricBlockSystem cfg).support b ∩ D).card = 2 := by
    intro b hb
    have hb' := Finset.mem_filter.mp hb
    exact hb'.2.1
  have htwoE : ∀ b ∈ F,
      ((geometricBlockSystem cfg).support b ∩ E).card = 2 := by
    intro b hb
    have hb' := Finset.mem_filter.mp hb
    exact hb'.2.2
  have hbound := (geometricBlockSystem cfg).relative_two_two_capacity_between
    D E F hDE htwoD
  have hsum :
      (∑ b ∈ F,
        Nat.choose ((geometricBlockSystem cfg).support b ∩ E).card 2) =
        F.card := by
    calc
      (∑ b ∈ F,
          Nat.choose ((geometricBlockSystem cfg).support b ∩ E).card 2) =
          ∑ _b ∈ F, 1 := by
        apply Finset.sum_congr rfl
        intro b hb
        rw [htwoE b hb]
        norm_num
      _ = F.card := by simp
  rw [hsum] at hbound
  change D.card = 5 at hfive
  change E.card = 4 at hfour
  rw [hfive, hfour] at hbound
  norm_num at hbound ⊢
  exact hbound

/-- Residual real-plane input after discharging the `5 + 4` capacity by
finite combinatorics. -/
structure RealPlaneFourFourCrossBlockPrinciple where
  four_four :
    ∀ {α : Type u} [Fintype α] [DecidableEq α]
      (cfg : Configuration α) (Γ Ω : DeterminedCircle cfg),
      Γ ≠ Ω →
      (exclusiveCircleTrace cfg Γ Ω).card = 4 →
      (exclusiveCircleTrace cfg Ω Γ).card = 4 →
      (circleCrossBlocks cfg Γ Ω).card ≤ 10

/-- Restore the former two-field interface: its `5 + 4` component is now a
theorem, while the genuinely geometric `4 + 4` component is supplied by the
residual principle. -/
def RealPlaneFourFourCrossBlockPrinciple.toCross
    (P : RealPlaneFourFourCrossBlockPrinciple.{u}) :
    RealPlaneRadicalAxisCrossBlockPrinciple.{u} where
  five_four := by
    intro α _ _ cfg Γ Ω _ hfive hfour
    exact circleCrossBlocks_card_le_twelve_of_five_four
      cfg Γ Ω hfive hfour
  four_four := P.four_four

end Erdos506.Incidence
