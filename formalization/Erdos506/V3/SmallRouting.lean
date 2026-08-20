import Erdos506.V3.SmallCases
import Erdos506.V3.FiveCircleStrict
import Erdos506.V3.FanoStrict

/-!
# Arithmetic routing for V3 on seven through ten labels

The strict Fano-wall estimate `c₄ ≤ 6` on seven labels and the real-geometry
exclusion `c₅ ≤ 5` on ten labels are now proved internally.  For eight, nine,
and ten labels the remaining input is summed Melchior.
-/

namespace Erdos506.V3

open Erdos506.V4

theorem circleCount_ge_target_of_card_seven_of_c4_le_six
    {α : Type*} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (hadm : Admissible cfg)
    (hα : Fintype.card α = 7)
    (hfano : circleCensus cfg 4 ≤ 6) :
    Erdos506.v3Target (Fintype.card α) ≤ circleCount cfg := by
  obtain ⟨g, hmax⟩ := exists_richestCircle cfg hadm.1 (by omega)
  let m := (circleTrace cfg g.1).card
  have hmge : 3 ≤ m := circleSupport_card_ge_three cfg g
  have hmlt : m < Fintype.card α := circleSupport_card_lt cfg hadm.2 g
  by_cases hm3 : m = 3
  · have hcap : ∀ c : DeterminedCircle cfg,
        (circleTrace cfg c.1).card ≤ 3 := by
      intro c
      have hc := hmax c
      change (circleTrace cfg c.1).card ≤ m at hc
      omega
    have hcount := circleCount_eq_choose_three_of_support_le_three
      cfg hadm.1 hcap
    rw [hα] at hcount ⊢
    norm_num [Erdos506.v3Target, Erdos506.v3GenericTarget, Nat.choose] at hcount ⊢
    omega
  · by_cases hm4 : m = 4
    · have hcap : ∀ c : DeterminedCircle cfg,
          (circleTrace cfg c.1).card ≤ 4 := by
        intro c
        have hc := hmax c
        change (circleTrace cfg c.1).card ≤ m at hc
        omega
      have hcount := circleCount_eq_c3_add_c4 cfg hcap
      have hpart := triplePartition_eq_c3_add_four_c4 cfg hadm.1 hcap
      rw [hα] at hpart ⊢
      norm_num [Erdos506.v3Target, Erdos506.v3GenericTarget, Nat.choose] at hpart ⊢
      omega
    · by_cases hm5 : m = 5
      · have hpencil := pencilBound_le_circleCount cfg hadm.1 g
        change pencilBound (Fintype.card α) m ≤ circleCount cfg at hpencil
        rw [hα, hm5] at hpencil
        norm_num [pencilBound, Nat.choose] at hpencil
        rw [hα]
        norm_num [Erdos506.v3Target, Erdos506.v3GenericTarget, Nat.choose]
        omega
      · have hm6 : m = 6 := by omega
        have hg : (circleTrace cfg g.1).card = Fintype.card α - 1 := by
          change m = Fintype.card α - 1
          omega
        have hcount := circleCount_eq_generic_of_nearCircle
          cfg hadm.1 g hg (by omega)
        rw [hα] at hcount ⊢
        norm_num [Erdos506.v3Target, Erdos506.v3GenericTarget, Nat.choose] at hcount ⊢
        omega

theorem circleCount_ge_target_of_card_seven
    {α : Type*} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (hadm : Admissible cfg)
    (hα : Fintype.card α = 7) :
    Erdos506.v3Target (Fintype.card α) ≤ circleCount cfg :=
  circleCount_ge_target_of_card_seven_of_c4_le_six cfg hadm hα
    (c4_le_six_of_card_seven cfg hadm.1 hα)

theorem circleCount_ge_target_of_card_eight_of_summedMelchior
    {α : Type*} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (hadm : Admissible cfg)
    (hα : Fintype.card α = 8) (hmel : SummedMelchior cfg) :
    Erdos506.v3Target (Fintype.card α) ≤ circleCount cfg := by
  obtain ⟨g, hmax⟩ := exists_richestCircle cfg hadm.1 (by omega)
  let m := (circleTrace cfg g.1).card
  have hmge : 3 ≤ m := circleSupport_card_ge_three cfg g
  have hmlt : m < Fintype.card α := circleSupport_card_lt cfg hadm.2 g
  by_cases hm3 : m = 3
  · have hcap : ∀ c : DeterminedCircle cfg,
        (circleTrace cfg c.1).card ≤ 3 := by
      intro c
      have hc := hmax c
      change (circleTrace cfg c.1).card ≤ m at hc
      omega
    have hcount := circleCount_eq_choose_three_of_support_le_three
      cfg hadm.1 hcap
    rw [hα] at hcount ⊢
    norm_num [Erdos506.v3Target, Nat.choose] at hcount ⊢
    omega
  · by_cases hm4 : m = 4
    · have hcap : ∀ c : DeterminedCircle cfg,
          (circleTrace cfg c.1).card ≤ 4 := by
        intro c
        have hc := hmax c
        change (circleTrace cfg c.1).card ≤ m at hc
        omega
      have hcount := circleCount_eq_c3_add_c4 cfg hcap
      have hpart := triplePartition_eq_c3_add_four_c4 cfg hadm.1 hcap
      have hc3 := c3_lower_of_summedMelchior_cap_four cfg hmel hcap
      rw [hα] at hpart hc3 ⊢
      norm_num [Erdos506.v3Target, Nat.choose] at hpart ⊢
      omega
    · have hpencil := pencilBound_le_circleCount cfg hadm.1 g
      change pencilBound (Fintype.card α) m ≤ circleCount cfg at hpencil
      have hmrange : m = 5 ∨ m = 6 ∨ m = 7 := by omega
      rcases hmrange with hm5 | hm6 | hm7
      · rw [hα, hm5] at hpencil
        norm_num [pencilBound, Nat.choose] at hpencil
        rw [hα]
        norm_num [Erdos506.v3Target, Nat.choose]
        omega
      · rw [hα, hm6] at hpencil
        norm_num [pencilBound, Nat.choose] at hpencil
        rw [hα]
        norm_num [Erdos506.v3Target, Nat.choose]
        omega
      · rw [hα, hm7] at hpencil
        norm_num [pencilBound, Nat.choose] at hpencil
        rw [hα]
        norm_num [Erdos506.v3Target, Nat.choose]
        omega

theorem circleCount_ge_target_of_card_nine_of_summedMelchior
    {α : Type*} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (hadm : Admissible cfg)
    (hα : Fintype.card α = 9) (hmel : SummedMelchior cfg) :
    Erdos506.v3Target (Fintype.card α) ≤ circleCount cfg := by
  obtain ⟨g, hmax⟩ := exists_richestCircle cfg hadm.1 (by omega)
  let m := (circleTrace cfg g.1).card
  have hmge : 3 ≤ m := circleSupport_card_ge_three cfg g
  have hmlt : m < Fintype.card α := circleSupport_card_lt cfg hadm.2 g
  by_cases hm3 : m = 3
  · have hcap : ∀ c : DeterminedCircle cfg,
        (circleTrace cfg c.1).card ≤ 3 := by
      intro c
      have hc := hmax c
      change (circleTrace cfg c.1).card ≤ m at hc
      omega
    have hcount := circleCount_eq_choose_three_of_support_le_three
      cfg hadm.1 hcap
    rw [hα] at hcount ⊢
    norm_num [Erdos506.v3Target, Erdos506.v3GenericTarget, Nat.choose] at hcount ⊢
    omega
  · by_cases hm4 : m = 4
    · have hcap : ∀ c : DeterminedCircle cfg,
          (circleTrace cfg c.1).card ≤ 4 := by
        intro c
        have hc := hmax c
        change (circleTrace cfg c.1).card ≤ m at hc
        omega
      have hcount := circleCount_eq_c3_add_c4 cfg hcap
      have hpart := triplePartition_eq_c3_add_four_c4 cfg hadm.1 hcap
      have hc3 := c3_lower_of_summedMelchior_cap_four cfg hmel hcap
      rw [hα] at hpart hc3 ⊢
      norm_num [Erdos506.v3Target, Erdos506.v3GenericTarget, Nat.choose] at hpart ⊢
      omega
    · have hpencil := pencilBound_le_circleCount cfg hadm.1 g
      change pencilBound (Fintype.card α) m ≤ circleCount cfg at hpencil
      have hmrange : m = 5 ∨ m = 6 ∨ m = 7 ∨ m = 8 := by omega
      rcases hmrange with hm5 | hm6 | hm7 | hm8
      · rw [hα, hm5] at hpencil
        norm_num [pencilBound, Nat.choose] at hpencil
        rw [hα]
        norm_num [Erdos506.v3Target, Erdos506.v3GenericTarget, Nat.choose]
        omega
      · rw [hα, hm6] at hpencil
        norm_num [pencilBound, Nat.choose] at hpencil
        rw [hα]
        norm_num [Erdos506.v3Target, Erdos506.v3GenericTarget, Nat.choose]
        omega
      · rw [hα, hm7] at hpencil
        norm_num [pencilBound, Nat.choose] at hpencil
        rw [hα]
        norm_num [Erdos506.v3Target, Erdos506.v3GenericTarget, Nat.choose]
        omega
      · rw [hα, hm8] at hpencil
        norm_num [pencilBound, Nat.choose] at hpencil
        rw [hα]
        norm_num [Erdos506.v3Target, Erdos506.v3GenericTarget, Nat.choose]
        omega

theorem circleCount_ge_target_of_card_ten_of_inputs
    {α : Type*} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (hadm : Admissible cfg)
    (hα : Fintype.card α = 10) (hmel : SummedMelchior cfg)
    (hfive : circleCensus cfg 5 ≤ 5) :
    Erdos506.v3Target (Fintype.card α) ≤ circleCount cfg := by
  obtain ⟨g, hmax⟩ := exists_richestCircle cfg hadm.1 (by omega)
  let m := (circleTrace cfg g.1).card
  have hmge : 3 ≤ m := circleSupport_card_ge_three cfg g
  have hmlt : m < Fintype.card α := circleSupport_card_lt cfg hadm.2 g
  by_cases hm3 : m = 3
  · have hcap : ∀ c : DeterminedCircle cfg,
        (circleTrace cfg c.1).card ≤ 3 := by
      intro c
      have hc := hmax c
      change (circleTrace cfg c.1).card ≤ m at hc
      omega
    have hcount := circleCount_eq_choose_three_of_support_le_three
      cfg hadm.1 hcap
    rw [hα] at hcount ⊢
    norm_num [Erdos506.v3Target, Erdos506.v3GenericTarget, Nat.choose] at hcount ⊢
    omega
  · by_cases hm4 : m = 4
    · have hcap : ∀ c : DeterminedCircle cfg,
          (circleTrace cfg c.1).card ≤ 4 := by
        intro c
        have hc := hmax c
        change (circleTrace cfg c.1).card ≤ m at hc
        omega
      have hcount := circleCount_eq_c3_add_c4 cfg hcap
      have hpart := triplePartition_eq_c3_add_four_c4 cfg hadm.1 hcap
      have hc3 := c3_lower_of_summedMelchior_cap_four cfg hmel hcap
      rw [hα] at hpart hc3 ⊢
      norm_num [Erdos506.v3Target, Erdos506.v3GenericTarget, Nat.choose] at hpart ⊢
      omega
    · by_cases hm5 : m = 5
      · have hcap : ∀ c : DeterminedCircle cfg,
            (circleTrace cfg c.1).card ≤ 5 := by
          intro c
          have hc := hmax c
          change (circleTrace cfg c.1).card ≤ m at hc
          omega
        have hcount := circleCount_eq_c3_add_c4_add_c5 cfg hcap
        have hpart := triplePartition_eq_c3_add_four_c4_add_ten_c5
          cfg hadm.1 hcap
        have hrow := melchior_c3_c5_row cfg hmel hcap
        rw [hα] at hpart hrow ⊢
        norm_num [Erdos506.v3Target, Erdos506.v3GenericTarget, Nat.choose] at hpart ⊢
        omega
      · have hpencil := pencilBound_le_circleCount cfg hadm.1 g
        change pencilBound (Fintype.card α) m ≤ circleCount cfg at hpencil
        have hmrange : m = 6 ∨ m = 7 ∨ m = 8 ∨ m = 9 := by omega
        rcases hmrange with hm6 | hm7 | hm8 | hm9
        · rw [hα, hm6] at hpencil
          norm_num [pencilBound, Nat.choose] at hpencil
          rw [hα]
          norm_num [Erdos506.v3Target, Erdos506.v3GenericTarget, Nat.choose]
          omega
        · rw [hα, hm7] at hpencil
          norm_num [pencilBound, Nat.choose] at hpencil
          rw [hα]
          norm_num [Erdos506.v3Target, Erdos506.v3GenericTarget, Nat.choose]
          omega
        · rw [hα, hm8] at hpencil
          norm_num [pencilBound, Nat.choose] at hpencil
          rw [hα]
          norm_num [Erdos506.v3Target, Erdos506.v3GenericTarget, Nat.choose]
          omega
        · rw [hα, hm9] at hpencil
          norm_num [pencilBound, Nat.choose] at hpencil
          rw [hα]
          norm_num [Erdos506.v3Target, Erdos506.v3GenericTarget, Nat.choose]
          omega

theorem circleCount_ge_target_of_card_ten_of_summedMelchior
    {α : Type*} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (hadm : Admissible cfg)
    (hα : Fintype.card α = 10) (hmel : SummedMelchior cfg) :
    Erdos506.v3Target (Fintype.card α) ≤ circleCount cfg :=
  circleCount_ge_target_of_card_ten_of_inputs cfg hadm hα hmel
    (c5_le_five_of_card_ten cfg hadm.1 hα)

end Erdos506.V3
