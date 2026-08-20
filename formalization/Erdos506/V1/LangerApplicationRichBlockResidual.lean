import Erdos506.V1.LangerApplicationFiniteWindow

/-!
# Lossless rich-block residual for the Langer-free finite window

This module contains data, not a callback: it records the actual block left
by the cap-sensitive master and all endpoint exclusions already proved by
the pencil and selected-seven arguments.
-/

namespace Erdos506.V1

open Erdos506.Block
open Erdos506.Block.BlockSystem
open Erdos506.Incidence
open Erdos506.V4

universe u

structure FiniteWindowRichBlockResidual
    {α : Type u} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) where
  window_lower : 14 ≤ Fintype.card α
  window_upper : Fintype.card α ≤ 22
  block : GeometricBlock cfg
  nontrivial : 3 ≤ (geometricBlockSupport cfg block).card
  aboveThreshold : finiteWindowCapThreshold (Fintype.card α) <
    (geometricBlockSupport cfg block).card
  atMostHalf : (geometricBlockSupport cfg block).card ≤
    Fintype.card α / 2
  strictAtLargeEven :
    (Fintype.card α = 18 ∨ Fintype.card α = 20 ∨
      Fintype.card α = 22) →
      (geometricBlockSupport cfg block).card < Fintype.card α / 2
  fourteen_size : Fintype.card α = 14 →
    (geometricBlockSupport cfg block).card = 6

/-- Every counterexample in `14 ≤ n ≤ 22` produces the lossless residual
record above. -/
noncomputable def finiteWindowRichBlockResidual_of_counterexample
    {α : Type u} [Fintype α] [DecidableEq α]
    (Mel : RealPlaneMelchiorPrinciple.{u})
    (cfg : Configuration α) (hadm : Admissible cfg)
    (hmin : 14 ≤ Fintype.card α) (hmax : Fintype.card α ≤ 22)
    (hcount : Erdos506.V4.circleCount cfg <
      Erdos506.v1UniformTarget (Fintype.card α)) :
    FiniteWindowRichBlockResidual cfg := by
  by_cases h14 : Fintype.card α = 14
  · have hcount72 : Erdos506.V4.circleCount cfg ≤ 72 := by
      rw [h14] at hcount
      norm_num [Erdos506.v1UniformTarget, Nat.choose] at hcount
      omega
    let hexists := exists_sixBlock_of_fourteen_counterexample
      Mel cfg hadm h14 hcount72
    let b := Classical.choose hexists
    have hb := Classical.choose_spec hexists
    refine ⟨hmin, hmax, b, hb.1, ?_, ?_, ?_, ?_⟩
    · rw [h14, hb.2]
      norm_num [finiteWindowCapThreshold]
    · rw [h14, hb.2]
      norm_num
    · intro hlarge
      rcases hlarge with h18 | h20 | h22 <;> omega
    · intro _h
      exact hb.2
  · have h15 : 15 ≤ Fintype.card α := by omega
    let hexists := exists_sharpTopIntervalBlock_of_finiteWindow_counterexample
      Mel cfg hadm h15 hmax hcount
    let b := Classical.choose hexists
    have hb := Classical.choose_spec hexists
    exact ⟨hmin, hmax, b, hb.1, hb.2.1, hb.2.2.1, hb.2.2.2,
      fun h => (h14 h).elim⟩

/-- The direct rich-line pencil already removes the `(16,8)` line endpoint
and every residual line endpoint from nineteen through twenty-two labels. -/
theorem FiniteWindowRichBlockResidual.line_impossible_of_sixteenEight_or_ge_nineteen
    {α : Type u} [Fintype α] [DecidableEq α]
    {cfg : Configuration α} (R : FiniteWindowRichBlockResidual cfg)
    (hline : (blockSystem cfg).kind R.block = .line)
    (hcase : (Fintype.card α = 16 ∧
        (geometricBlockSupport cfg R.block).card = 8) ∨
      19 ≤ Fintype.card α)
    (hcount : Erdos506.V4.circleCount cfg <
      Erdos506.v1UniformTarget (Fintype.card α)) : False := by
  have hpencil := richLinePencilBound_le_totalCircleCount
    (blockSystem cfg) R.block hline
  rw [totalCircleCount_eq_card_determinedCircle,
    ← Erdos506.V3.circleCount_eq_card_determinedCircle] at hpencil
  have hsupportCard : ((blockSystem cfg).support R.block).card =
      (geometricBlockSupport cfg R.block).card := by rfl
  rw [hsupportCard] at hpencil
  have htarget : Erdos506.v1UniformTarget (Fintype.card α) ≤
      (Fintype.card α - (geometricBlockSupport cfg R.block).card) *
          Nat.choose (geometricBlockSupport cfg R.block).card 2 -
        Nat.choose
            (Fintype.card α - (geometricBlockSupport cfg R.block).card) 2 *
          ((geometricBlockSupport cfg R.block).card / 2) := by
    rcases hcase with ⟨hn16, hs8⟩ | hn19
    · rw [hn16, hs8]
      norm_num [Erdos506.v1UniformTarget, Nat.choose]
    · have hwindowUpper := R.window_upper
      have hnCases : Fintype.card α = 19 ∨ Fintype.card α = 20 ∨
          Fintype.card α = 21 ∨ Fintype.card α = 22 := by omega
      rcases hnCases with hn19' | hn20 | hn21 | hn22
      · have hs : (geometricBlockSupport cfg R.block).card = 9 := by
          have hlower := R.aboveThreshold
          have hupper := R.atMostHalf
          rw [hn19'] at hlower hupper
          norm_num [finiteWindowCapThreshold] at hlower hupper
          omega
        rw [hn19', hs]
        norm_num [Erdos506.v1UniformTarget, Nat.choose]
      · have hs : (geometricBlockSupport cfg R.block).card = 9 := by
          have hlower := R.aboveThreshold
          have hstrict := R.strictAtLargeEven (Or.inr (Or.inl hn20))
          rw [hn20] at hlower hstrict
          norm_num [finiteWindowCapThreshold] at hlower hstrict
          omega
        rw [hn20, hs]
        norm_num [Erdos506.v1UniformTarget, Nat.choose]
      · have hs : (geometricBlockSupport cfg R.block).card = 10 := by
          have hlower := R.aboveThreshold
          have hupper := R.atMostHalf
          rw [hn21] at hlower hupper
          norm_num [finiteWindowCapThreshold] at hlower hupper
          omega
        rw [hn21, hs]
        norm_num [Erdos506.v1UniformTarget, Nat.choose]
      · have hs : (geometricBlockSupport cfg R.block).card = 10 := by
          have hlower := R.aboveThreshold
          have hstrict := R.strictAtLargeEven (Or.inr (Or.inr hn22))
          rw [hn22] at hlower hstrict
          norm_num [finiteWindowCapThreshold] at hlower hstrict
          omega
        rw [hn22, hs]
        norm_num [Erdos506.v1UniformTarget, Nat.choose]
  exact (not_le_of_gt hcount) (htarget.trans hpencil)

end Erdos506.V1
