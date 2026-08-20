import Erdos506.V1.HalfCap

/-!
# Rich-block caps for the remaining finite V1 window

This module factors the common geometric bridge from the rich line/circle
pencils to a support-size cap.  The five finite instances below are purely
numerical and cover the contradictory circle-count thresholds at
`n = 9, ..., 13`.
-/

namespace Erdos506.V1

open Erdos506.Block
open Erdos506.Block.BlockSystem
open Erdos506.Incidence
open Erdos506.V4

universe u

/-- A numerical lower bound for every forbidden line size turns the sharp
line pencil into a uniform support cap. -/
theorem lineSupport_card_le_of_richLinePencil
    {α : Type u} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (hadm : Admissible cfg)
    {n C M : ℕ} (hcard : Fintype.card α = n)
    (hcount : Erdos506.V4.circleCount cfg ≤ C)
    (hbound : ∀ s : ℕ, M < s → s < n →
      C < (n - s) * Nat.choose s 2 -
        Nat.choose (n - s) 2 * (s / 2))
    (L : DeterminedLine cfg) :
    (lineSupport cfg L).card ≤ M := by
  let s := (lineSupport cfg L).card
  by_contra hnot
  have hlarge : M < s := by
    dsimp only [s]
    omega
  have hproper :
      (geometricBlockSupport cfg (Sum.inl L)).card < Fintype.card α :=
    geometricBlockSupport_card_lt_of_admissible cfg hadm (Sum.inl L)
  have hsn : s < n := by
    change s < Fintype.card α at hproper
    simpa [hcard] using hproper
  have hpencil := richLinePencilBound_le_totalCircleCount
    (blockSystem cfg) (Sum.inl L) rfl
  rw [totalCircleCount_eq_card_determinedCircle,
    ← Erdos506.V3.circleCount_eq_card_determinedCircle] at hpencil
  rw [hcard] at hpencil
  change
    (n - s) * Nat.choose s 2 - Nat.choose (n - s) 2 * (s / 2) ≤
      Erdos506.V4.circleCount cfg at hpencil
  have hlower := hbound s hlarge hsn
  omega

/-- A numerical lower bound for every forbidden proper-circle size turns the
common rich-block pencil into a uniform circle-trace cap. -/
theorem circleTrace_card_le_of_richBlockPencil
    {α : Type u} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (hadm : Admissible cfg)
    {n C M : ℕ} (hM : 3 ≤ M) (hcard : Fintype.card α = n)
    (hcount : Erdos506.V4.circleCount cfg ≤ C)
    (hbound : ∀ s : ℕ, M < s → s < n →
      C < richBlockPencilBound n s)
    (c : DeterminedCircle cfg) :
    (circleTrace cfg c.1).card ≤ M := by
  let s := (circleTrace cfg c.1).card
  by_contra hnot
  have hlarge : M < s := by
    dsimp only [s]
    omega
  have hproper :
      (geometricBlockSupport cfg (Sum.inr c)).card < Fintype.card α :=
    geometricBlockSupport_card_lt_of_admissible cfg hadm (Sum.inr c)
  have hsn : s < n := by
    change s < Fintype.card α at hproper
    simpa [hcard] using hproper
  have hpencil := richBlockPencilBound_le_totalCircleCount
    (blockSystem cfg) (Sum.inr c) hproper (by
      change 3 ≤ s
      omega)
  rw [totalCircleCount_eq_card_determinedCircle,
    ← Erdos506.V3.circleCount_eq_card_determinedCircle] at hpencil
  rw [hcard] at hpencil
  change richBlockPencilBound n s ≤ Erdos506.V4.circleCount cfg at hpencil
  have hlower := hbound s hlarge hsn
  omega

theorem lineSupport_card_le_four_of_nine_of_circleCount_le
    {α : Type u} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (hadm : Admissible cfg)
    (hcard : Fintype.card α = 9)
    (hcount : Erdos506.V4.circleCount cfg ≤ 24)
    (L : DeterminedLine cfg) :
    (lineSupport cfg L).card ≤ 4 := by
  apply lineSupport_card_le_of_richLinePencil cfg hadm hcard hcount
  intro s hs hsn
  interval_cases s <;> norm_num [Nat.choose]

theorem circleTrace_card_le_five_of_nine_of_circleCount_le
    {α : Type u} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (hadm : Admissible cfg)
    (hcard : Fintype.card α = 9)
    (hcount : Erdos506.V4.circleCount cfg ≤ 24)
    (c : DeterminedCircle cfg) :
    (circleTrace cfg c.1).card ≤ 5 := by
  apply circleTrace_card_le_of_richBlockPencil cfg hadm (by omega)
    hcard hcount
  intro s hs hsn
  interval_cases s <;>
    norm_num [richBlockPencilBound, Nat.choose]

theorem lineSupport_card_le_five_of_ten_of_circleCount_le
    {α : Type u} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (hadm : Admissible cfg)
    (hcard : Fintype.card α = 10)
    (hcount : Erdos506.V4.circleCount cfg ≤ 32)
    (L : DeterminedLine cfg) :
    (lineSupport cfg L).card ≤ 5 := by
  apply lineSupport_card_le_of_richLinePencil cfg hadm hcard hcount
  intro s hs hsn
  interval_cases s <;> norm_num [Nat.choose]

theorem circleTrace_card_le_six_of_ten_of_circleCount_le
    {α : Type u} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (hadm : Admissible cfg)
    (hcard : Fintype.card α = 10)
    (hcount : Erdos506.V4.circleCount cfg ≤ 32)
    (c : DeterminedCircle cfg) :
    (circleTrace cfg c.1).card ≤ 6 := by
  apply circleTrace_card_le_of_richBlockPencil cfg hadm (by omega)
    hcard hcount
  intro s hs hsn
  interval_cases s <;>
    norm_num [richBlockPencilBound, Nat.choose]

theorem lineSupport_card_le_five_of_eleven_of_circleCount_le
    {α : Type u} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (hadm : Admissible cfg)
    (hcard : Fintype.card α = 11)
    (hcount : Erdos506.V4.circleCount cfg ≤ 40)
    (L : DeterminedLine cfg) :
    (lineSupport cfg L).card ≤ 5 := by
  apply lineSupport_card_le_of_richLinePencil cfg hadm hcard hcount
  intro s hs hsn
  interval_cases s <;> norm_num [Nat.choose]

theorem circleTrace_card_le_six_of_eleven_of_circleCount_le
    {α : Type u} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (hadm : Admissible cfg)
    (hcard : Fintype.card α = 11)
    (hcount : Erdos506.V4.circleCount cfg ≤ 40)
    (c : DeterminedCircle cfg) :
    (circleTrace cfg c.1).card ≤ 6 := by
  apply circleTrace_card_le_of_richBlockPencil cfg hadm (by omega)
    hcard hcount
  intro s hs hsn
  interval_cases s <;>
    norm_num [richBlockPencilBound, Nat.choose]

theorem lineSupport_card_le_six_of_twelve_of_circleCount_le
    {α : Type u} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (hadm : Admissible cfg)
    (hcard : Fintype.card α = 12)
    (hcount : Erdos506.V4.circleCount cfg ≤ 50)
    (L : DeterminedLine cfg) :
    (lineSupport cfg L).card ≤ 6 := by
  apply lineSupport_card_le_of_richLinePencil cfg hadm hcard hcount
  intro s hs hsn
  interval_cases s <;> norm_num [Nat.choose]

theorem circleTrace_card_le_six_of_twelve_of_circleCount_le
    {α : Type u} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (hadm : Admissible cfg)
    (hcard : Fintype.card α = 12)
    (hcount : Erdos506.V4.circleCount cfg ≤ 50)
    (c : DeterminedCircle cfg) :
    (circleTrace cfg c.1).card ≤ 6 := by
  apply circleTrace_card_le_of_richBlockPencil cfg hadm (by omega)
    hcard hcount
  intro s hs hsn
  interval_cases s <;>
    norm_num [richBlockPencilBound, Nat.choose]

theorem lineSupport_card_le_six_of_thirteen_of_circleCount_le
    {α : Type u} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (hadm : Admissible cfg)
    (hcard : Fintype.card α = 13)
    (hcount : Erdos506.V4.circleCount cfg ≤ 60)
    (L : DeterminedLine cfg) :
    (lineSupport cfg L).card ≤ 6 := by
  apply lineSupport_card_le_of_richLinePencil cfg hadm hcard hcount
  intro s hs hsn
  interval_cases s <;> norm_num [Nat.choose]

theorem circleTrace_card_le_six_of_thirteen_of_circleCount_le
    {α : Type u} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (hadm : Admissible cfg)
    (hcard : Fintype.card α = 13)
    (hcount : Erdos506.V4.circleCount cfg ≤ 60)
    (c : DeterminedCircle cfg) :
    (circleTrace cfg c.1).card ≤ 6 := by
  apply circleTrace_card_le_of_richBlockPencil cfg hadm (by omega)
    hcard hcount
  intro s hs hsn
  interval_cases s <;>
    norm_num [richBlockPencilBound, Nat.choose]

end Erdos506.V1
