import Erdos506.V1.HalfCap

/-!
# The fourteen-point V1 endpoint

This module begins the direct `n = 14` dichotomy from the manuscript.  It
closes the branch in which no selected proper circle contains exactly seven
points.  The remaining seven-circle branch uses a separate relative-block
certificate and is deliberately not hidden behind a hypothesis here.
-/

namespace Erdos506.V1

open Erdos506.Block
open Erdos506.Block.BlockSystem
open Erdos506.Incidence
open Erdos506.V4

universe u

/-- Under the contradictory bound `C ≤ 72`, every proper circle on fourteen
points contains at most seven selected points. -/
theorem circleTrace_card_le_seven_of_fourteen_of_circleCount_le
    {α : Type u} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (hadm : Admissible cfg)
    (hcard : Fintype.card α = 14)
    (hcount : Erdos506.V4.circleCount cfg ≤ 72)
    (c : DeterminedCircle cfg) :
    (circleTrace cfg c.1).card ≤ 7 := by
  let s := (circleTrace cfg c.1).card
  by_contra hnot
  have hs8 : 8 ≤ s := by
    dsimp only [s]
    omega
  have hproper :
      (geometricBlockSupport cfg (Sum.inr c)).card < Fintype.card α :=
    geometricBlockSupport_card_lt_of_admissible cfg hadm (Sum.inr c)
  have hs13 : s ≤ 13 := by
    change s < Fintype.card α at hproper
    rw [hcard] at hproper
    omega
  have hpencil := richBlockPencilBound_le_totalCircleCount
    (blockSystem cfg) (Sum.inr c) hproper (by
      change 3 ≤ s
      omega)
  rw [totalCircleCount_eq_card_determinedCircle,
    ← Erdos506.V3.circleCount_eq_card_determinedCircle] at hpencil
  rw [hcard] at hpencil
  change richBlockPencilBound 14 s ≤ Erdos506.V4.circleCount cfg at hpencil
  interval_cases s <;>
    norm_num [richBlockPencilBound, Nat.choose] at hpencil <;>
    omega

/-- Under the contradictory bound `C ≤ 72`, every determined line on
fourteen points contains at most six selected points.  The sharp line pencil
is needed at support size seven. -/
theorem lineSupport_card_le_six_of_fourteen_of_circleCount_le
    {α : Type u} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (hadm : Admissible cfg)
    (hcard : Fintype.card α = 14)
    (hcount : Erdos506.V4.circleCount cfg ≤ 72)
    (L : DeterminedLine cfg) :
    (lineSupport cfg L).card ≤ 6 := by
  let s := (lineSupport cfg L).card
  by_contra hnot
  have hs7 : 7 ≤ s := by
    dsimp only [s]
    omega
  have hproper :
      (geometricBlockSupport cfg (Sum.inl L)).card < Fintype.card α :=
    geometricBlockSupport_card_lt_of_admissible cfg hadm (Sum.inl L)
  have hs13 : s ≤ 13 := by
    change s < Fintype.card α at hproper
    rw [hcard] at hproper
    omega
  have hline := richLinePencilBound_le_totalCircleCount
    (blockSystem cfg) (Sum.inl L) rfl
  rw [totalCircleCount_eq_card_determinedCircle,
    ← Erdos506.V3.circleCount_eq_card_determinedCircle] at hline
  rw [hcard] at hline
  change
    (14 - s) * Nat.choose s 2 - Nat.choose (14 - s) 2 * (s / 2) ≤
      Erdos506.V4.circleCount cfg at hline
  interval_cases s <;>
    norm_num [Nat.choose] at hline <;>
    omega

/-- No determined proper circle has a seven-point trace. -/
def NoSevenCircle
    {α : Type*} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) : Prop :=
  ∀ c : DeterminedCircle cfg, (circleTrace cfg c.1).card ≠ 7

/-- Under `n = 14` and `C ≤ 72`, absence of a seven-circle forces every
nontrivial generalized block to have size at most six.  Size seven is
excluded by the sharp line pencil or by `NoSevenCircle`; sizes eight through
thirteen are excluded by the common rich-block pencil. -/
theorem blockSizeCap_six_of_fourteen_of_circleCount_le
    {α : Type u} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (hadm : Admissible cfg)
    (hcard : Fintype.card α = 14)
    (hcount : Erdos506.V4.circleCount cfg ≤ 72)
    (hno7 : NoSevenCircle cfg) :
    BlockSizeCap (blockSystem cfg) 6 := by
  intro b hbsize
  cases b with
  | inl L =>
      simpa [geometricBlockSupport] using
        lineSupport_card_le_six_of_fourteen_of_circleCount_le
          cfg hadm hcard hcount L
  | inr c =>
      have hseven := circleTrace_card_le_seven_of_fourteen_of_circleCount_le
        cfg hadm hcard hcount c
      have hne : (circleTrace cfg c.1).card ≠ 7 := hno7 c
      simpa [geometricBlockSupport] using (show
        (circleTrace cfg c.1).card ≤ 6 by omega)

/-- The no-seven-circle half of the exact fourteen-point dichotomy. -/
theorem circleCount_ge_seventy_three_of_card_fourteen_of_noSevenCircle
    {α : Type u} [Fintype α] [DecidableEq α]
    (Mel : Erdos506.Incidence.RealPlaneMelchiorPrinciple.{u})
    (Lan : Erdos506.Incidence.RealPlaneLangerPrinciple.{u})
    (cfg : Configuration α) (hadm : Admissible cfg)
    (hcard : Fintype.card α = 14)
    (hno7 : NoSevenCircle cfg) :
    73 ≤ Erdos506.V4.circleCount cfg := by
  by_contra hnot
  have hcount : Erdos506.V4.circleCount cfg ≤ 72 := by omega
  have hcap := blockSizeCap_six_of_fourteen_of_circleCount_le
    cfg hadm hcard hcount hno7
  have hocc : ∀ p : α,
      Erdos506.Incidence.LineOccupancyTwoThirds
        (Erdos506.V3.pivotInversion cfg p) := by
    apply pivotOccupancy_of_blockSizeCap cfg 6 hcap
    rw [hcard]
    norm_num
  have hmaster := largeMasterNumerator_le_geometricCircleCount
    Mel Lan cfg hadm (by omega) 6 (by omega) hcap hocc
  rw [hcard] at hmaster
  norm_num [largeMasterNumerator, Nat.choose] at hmaster
  omega

end Erdos506.V1
