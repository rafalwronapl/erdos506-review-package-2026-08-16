import Erdos506.V1.LangerApplicationTail
import Erdos506.V1.FourteenSelected

/-!
# The finite Langer-bypass window

The cap-sensitive master reduces every possible counterexample on fifteen
through twenty-two labels to one block in a short top interval.  The same
argument, combined with the existing selected-seven endpoint, leaves exactly
a six-block on fourteen labels.
-/

namespace Erdos506.V1

open Erdos506.Block
open Erdos506.Block.BlockSystem
open Erdos506.Incidence
open Erdos506.V4

universe u

/-- A numerical cap-master gap turns a geometric block cap into the uniform
circle bound. -/
theorem v1UniformTarget_le_circleCount_of_capMelchior_gap
    {α : Type u} [Fintype α] [DecidableEq α]
    (Mel : RealPlaneMelchiorPrinciple.{u})
    (cfg : Configuration α) (hadm : Admissible cfg)
    (hcard : 3 ≤ Fintype.card α) (K : Nat) (hK : 3 ≤ K)
    (hcap : BlockSizeCap (blockSystem cfg) K)
    (hgap : ((((K : Int) + 2) * 36 * (K : Int)) *
          ((Erdos506.v1UniformTarget (Fintype.card α) : Int) - 1)) <
        capMelchiorMasterNumerator (Fintype.card α) K) :
    Erdos506.v1UniformTarget (Fintype.card α) ≤
      Erdos506.V4.circleCount cfg := by
  have hmaster := capMelchiorMasterNumerator_le_geometricCircleCount
    Mel cfg hadm hcard K hK hcap
  by_contra hnot
  have hcount : Erdos506.V4.circleCount cfg <
      Erdos506.v1UniformTarget (Fintype.card α) := by omega
  have htargetPos : 1 ≤
      Erdos506.v1UniformTarget (Fintype.card α) := by
    by_cases hsmall : Fintype.card α ≤ 4
    · interval_cases h : Fintype.card α <;>
        norm_num [Erdos506.v1UniformTarget, Nat.choose] at hcard ⊢
    · have hhalf : 1 < (Fintype.card α - 1) / 2 := by omega
      have hchoose : Nat.choose (Fintype.card α - 1) 1 ≤
          Nat.choose (Fintype.card α - 1) 2 :=
        Nat.choose_le_succ_of_lt_half_left hhalf
      simp only [Nat.choose_one_right] at hchoose
      have hdiv : (Fintype.card α - 1) / 2 ≤ Fintype.card α - 1 :=
        Nat.div_le_self _ _
      unfold Erdos506.v1UniformTarget
      omega
  have hcountLeNat : Erdos506.V4.circleCount cfg ≤
      Erdos506.v1UniformTarget (Fintype.card α) - 1 := by omega
  have hcountLeCast : (Erdos506.V4.circleCount cfg : Int) ≤
      ((Erdos506.v1UniformTarget (Fintype.card α) - 1 : Nat) : Int) := by
    exact_mod_cast hcountLeNat
  have hcountLe : (Erdos506.V4.circleCount cfg : Int) ≤
      (Erdos506.v1UniformTarget (Fintype.card α) : Int) - 1 := by
    simpa only [Nat.cast_sub htargetPos, Nat.cast_one] using hcountLeCast
  have hcoeff : 0 ≤ (((K : Int) + 2) * 36 * (K : Int)) := by positivity
  have hscaledLe := mul_le_mul_of_nonneg_left hcountLe hcoeff
  exact (not_lt_of_ge hscaledLe) (hgap.trans_le hmaster)

/-- Lossless structural form of the cap-master reduction. -/
theorem exists_block_above_of_capMelchior_gap
    {α : Type u} [Fintype α] [DecidableEq α]
    (Mel : RealPlaneMelchiorPrinciple.{u})
    (cfg : Configuration α) (hadm : Admissible cfg)
    (hcard : 3 ≤ Fintype.card α) (H K : Nat) (hK : 3 ≤ K)
    (hcap : BlockSizeCap (blockSystem cfg) H)
    (hgap : ((((K : Int) + 2) * 36 * (K : Int)) *
          ((Erdos506.v1UniformTarget (Fintype.card α) : Int) - 1)) <
        capMelchiorMasterNumerator (Fintype.card α) K)
    (hcount : Erdos506.V4.circleCount cfg <
      Erdos506.v1UniformTarget (Fintype.card α)) :
    ∃ b : GeometricBlock cfg, 3 ≤ (geometricBlockSupport cfg b).card ∧
      K < (geometricBlockSupport cfg b).card ∧
      (geometricBlockSupport cfg b).card ≤ H := by
  by_contra hnone
  have hcapK : BlockSizeCap (blockSystem cfg) K := by
    intro b hb
    change 3 ≤ (geometricBlockSupport cfg b).card at hb
    have hbH := hcap b hb
    change (geometricBlockSupport cfg b).card ≤ H at hbH
    change (geometricBlockSupport cfg b).card ≤ K
    by_contra hbK
    exact hnone ⟨b, hb, by omega, hbH⟩
  have htarget := v1UniformTarget_le_circleCount_of_capMelchior_gap
    Mel cfg hadm hcard K hK hcapK hgap
  exact (not_le_of_gt hcount) htarget

/-- One arithmetic certificate covers the entire finite window. -/
theorem capMelchior_gap_finiteWindow
    (n : Nat) (hmin : 14 ≤ n) (hmax : n ≤ 22) :
    let K := (n - 4) / 2
    ((((K : Int) + 2) * 36 * (K : Int)) *
        ((Erdos506.v1UniformTarget n : Int) - 1)) <
      capMelchiorMasterNumerator n K := by
  interval_cases n <;>
    norm_num [capMelchiorMasterNumerator, Erdos506.v1UniformTarget,
      Nat.choose]

/-- Largest cap already excluded by the Melchior master in the finite
window.  The isolated value `n = 15` is the only parity endpoint where the
uniform formula must be lowered once more. -/
def finiteWindowCapThreshold (n : Nat) : Nat :=
  if n = 15 then 5 else (n - 3) / 2

/-- Sharp version of the common finite-window arithmetic certificate. -/
theorem capMelchior_gap_finiteWindow_sharp
    (n : Nat) (hmin : 14 ≤ n) (hmax : n ≤ 22) :
    ((((finiteWindowCapThreshold n : Int) + 2) * 36 *
        (finiteWindowCapThreshold n : Int)) *
        ((Erdos506.v1UniformTarget n : Int) - 1)) <
      capMelchiorMasterNumerator n (finiteWindowCapThreshold n) := by
  interval_cases n <;>
    norm_num [finiteWindowCapThreshold, capMelchiorMasterNumerator,
      Erdos506.v1UniformTarget, Nat.choose]

/-- For `15 ≤ n ≤ 22`, a counterexample contains a block strictly above
`(n - 4) / 2` and at most `n / 2`.  At `n = 18,20,22`, the pencil count
also removes the upper endpoint. -/
theorem exists_topIntervalBlock_of_finiteWindow_counterexample
    {α : Type u} [Fintype α] [DecidableEq α]
    (Mel : RealPlaneMelchiorPrinciple.{u})
    (cfg : Configuration α) (hadm : Admissible cfg)
    (hmin : 15 ≤ Fintype.card α) (hmax : Fintype.card α ≤ 22)
    (hcount : Erdos506.V4.circleCount cfg <
      Erdos506.v1UniformTarget (Fintype.card α)) :
    ∃ b : GeometricBlock cfg,
      3 ≤ (geometricBlockSupport cfg b).card ∧
      (Fintype.card α - 4) / 2 <
        (geometricBlockSupport cfg b).card ∧
      (geometricBlockSupport cfg b).card ≤ Fintype.card α / 2 ∧
      ((Fintype.card α = 18 ∨ Fintype.card α = 20 ∨
          Fintype.card α = 22) →
        (geometricBlockSupport cfg b).card < Fintype.card α / 2) := by
  have hcap := halfBlockCap_of_circleCount_lt_v1UniformTarget
    cfg hadm hmin hcount
  have hgap := capMelchior_gap_finiteWindow
    (Fintype.card α) (by omega) hmax
  obtain ⟨b, hb3, hbLower, hbUpper⟩ :=
    exists_block_above_of_capMelchior_gap
      Mel cfg hadm (by omega) (Fintype.card α / 2)
        ((Fintype.card α - 4) / 2) (by omega) hcap hgap hcount
  refine ⟨b, hb3, hbLower, hbUpper, ?_⟩
  intro hspecial
  by_contra hnot
  have heq : (geometricBlockSupport cfg b).card =
      Fintype.card α / 2 := by omega
  have hproper : (geometricBlockSupport cfg b).card < Fintype.card α :=
    geometricBlockSupport_card_lt_of_admissible cfg hadm b
  have hpencil := richBlockPencilBound_le_totalCircleCount
    (blockSystem cfg) b hproper hb3
  rw [totalCircleCount_eq_card_determinedCircle,
    ← Erdos506.V3.circleCount_eq_card_determinedCircle] at hpencil
  have heqSupport : ((blockSystem cfg).support b).card =
      Fintype.card α / 2 := by
    change (geometricBlockSupport cfg b).card = Fintype.card α / 2
    exact heq
  rw [heqSupport] at hpencil
  have htarget : Erdos506.v1UniformTarget (Fintype.card α) ≤
      richBlockPencilBound (Fintype.card α) (Fintype.card α / 2) := by
    rcases hspecial with h18 | h20 | h22
    · rw [h18]
      norm_num [richBlockPencilBound, Erdos506.v1UniformTarget, Nat.choose]
    · rw [h20]
      norm_num [richBlockPencilBound, Erdos506.v1UniformTarget, Nat.choose]
    · rw [h22]
      norm_num [richBlockPencilBound, Erdos506.v1UniformTarget, Nat.choose]
  exact (not_le_of_gt hcount) (htarget.trans hpencil)

/-- Sharp lossless residual: except for the two short endpoints `15,16`,
the distinguished block has the unique size left by the master and the
half-pencil bound. -/
theorem exists_sharpTopIntervalBlock_of_finiteWindow_counterexample
    {α : Type u} [Fintype α] [DecidableEq α]
    (Mel : RealPlaneMelchiorPrinciple.{u})
    (cfg : Configuration α) (hadm : Admissible cfg)
    (hmin : 15 ≤ Fintype.card α) (hmax : Fintype.card α ≤ 22)
    (hcount : Erdos506.V4.circleCount cfg <
      Erdos506.v1UniformTarget (Fintype.card α)) :
    ∃ b : GeometricBlock cfg,
      3 ≤ (geometricBlockSupport cfg b).card ∧
      finiteWindowCapThreshold (Fintype.card α) <
        (geometricBlockSupport cfg b).card ∧
      (geometricBlockSupport cfg b).card ≤ Fintype.card α / 2 ∧
      ((Fintype.card α = 18 ∨ Fintype.card α = 20 ∨
          Fintype.card α = 22) →
        (geometricBlockSupport cfg b).card < Fintype.card α / 2) := by
  have hcap := halfBlockCap_of_circleCount_lt_v1UniformTarget
    cfg hadm hmin hcount
  have hgap := capMelchior_gap_finiteWindow_sharp
    (Fintype.card α) (by omega) hmax
  obtain ⟨b, hb3, hbLower, hbUpper⟩ :=
    exists_block_above_of_capMelchior_gap
      Mel cfg hadm (by omega) (Fintype.card α / 2)
        (finiteWindowCapThreshold (Fintype.card α)) (by
          interval_cases h : Fintype.card α <;>
            norm_num [finiteWindowCapThreshold] at hmin hmax ⊢)
        hcap hgap hcount
  refine ⟨b, hb3, hbLower, hbUpper, ?_⟩
  intro hspecial
  by_contra hnot
  have heq : (geometricBlockSupport cfg b).card =
      Fintype.card α / 2 := by omega
  have hproper : (geometricBlockSupport cfg b).card < Fintype.card α :=
    geometricBlockSupport_card_lt_of_admissible cfg hadm b
  have hpencil := richBlockPencilBound_le_totalCircleCount
    (blockSystem cfg) b hproper hb3
  rw [totalCircleCount_eq_card_determinedCircle,
    ← Erdos506.V3.circleCount_eq_card_determinedCircle] at hpencil
  have heqSupport : ((blockSystem cfg).support b).card =
      Fintype.card α / 2 := by
    change (geometricBlockSupport cfg b).card = Fintype.card α / 2
    exact heq
  rw [heqSupport] at hpencil
  have htarget : Erdos506.v1UniformTarget (Fintype.card α) ≤
      richBlockPencilBound (Fintype.card α) (Fintype.card α / 2) := by
    rcases hspecial with h18 | h20 | h22
    · rw [h18]
      norm_num [richBlockPencilBound, Erdos506.v1UniformTarget, Nat.choose]
    · rw [h20]
      norm_num [richBlockPencilBound, Erdos506.v1UniformTarget, Nat.choose]
    · rw [h22]
      norm_num [richBlockPencilBound, Erdos506.v1UniformTarget, Nat.choose]
  exact (not_le_of_gt hcount) (htarget.trans hpencil)

/-- The already formalized selected-seven branch sharpens the fourteen-label
reduction to one block of size exactly six. -/
theorem exists_sixBlock_of_fourteen_counterexample
    {α : Type u} [Fintype α] [DecidableEq α]
    (Mel : RealPlaneMelchiorPrinciple.{u})
    (cfg : Configuration α) (hadm : Admissible cfg)
    (hcard : Fintype.card α = 14)
    (hcount : Erdos506.V4.circleCount cfg ≤ 72) :
    ∃ b : GeometricBlock cfg,
      3 ≤ (geometricBlockSupport cfg b).card ∧
      (geometricBlockSupport cfg b).card = 6 := by
  have hno7 : NoSevenCircle cfg := by
    intro c hc
    exact no_seven_circle_of_fourteen_of_circleCount_le
      Mel cfg hadm hcard hcount c hc
  have hcap := blockSizeCap_six_of_fourteen_of_circleCount_le
    cfg hadm hcard hcount hno7
  have hcountTarget : Erdos506.V4.circleCount cfg <
      Erdos506.v1UniformTarget (Fintype.card α) := by
    rw [hcard]
    norm_num [Erdos506.v1UniformTarget, Nat.choose]
    omega
  have hgapFive : ((((5 : Int) + 2) * 36 * (5 : Int)) *
        ((Erdos506.v1UniformTarget (Fintype.card α) : Int) - 1)) <
      capMelchiorMasterNumerator (Fintype.card α) 5 := by
    rw [hcard]
    norm_num [capMelchiorMasterNumerator, Erdos506.v1UniformTarget,
      Nat.choose]
  obtain ⟨b, hb3, hbLower, hbUpper⟩ :=
    exists_block_above_of_capMelchior_gap
      Mel cfg hadm (by omega) 6 5 (by omega) hcap hgapFive hcountTarget
  exact ⟨b, hb3, by omega⟩

end Erdos506.V1
