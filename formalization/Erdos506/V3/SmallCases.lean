import Erdos506.V3.Construction
import Erdos506.V3.Routing
import Erdos506.V3.SmallPacking

/-!
# The first three small V3 cases

These proofs route through a richest determined circle.  They establish the
sharp lower bounds for four, five, and six labels; the generic near-circle
construction supplies equality.
-/

namespace Erdos506.V3

open Erdos506.V4

theorem circleCount_ge_target_of_card_four
    {α : Type*} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (hadm : Admissible cfg)
    (hα : Fintype.card α = 4) :
    Erdos506.v3Target (Fintype.card α) ≤ circleCount cfg := by
  obtain ⟨g, hmax⟩ := exists_richestCircle cfg hadm.1 (by omega)
  have hgge := circleSupport_card_ge_three cfg g
  have hglt := circleSupport_card_lt cfg hadm.2 g
  have hg : (circleTrace cfg g.1).card = 3 := by omega
  have hcap : ∀ c : DeterminedCircle cfg,
      (circleTrace cfg c.1).card ≤ 3 := by
    intro c
    simpa [hg] using hmax c
  have hcount := circleCount_eq_choose_three_of_support_le_three
    cfg hadm.1 hcap
  rw [hα] at hcount ⊢
  norm_num [Erdos506.v3Target, Erdos506.v3GenericTarget, Nat.choose] at hcount ⊢
  exact hcount.ge

theorem circleCount_ge_target_of_card_five
    {α : Type*} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (hadm : Admissible cfg)
    (hα : Fintype.card α = 5) :
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
  · have hm4 : m = 4 := by omega
    have hg : (circleTrace cfg g.1).card = Fintype.card α - 1 := by
      change m = Fintype.card α - 1
      omega
    have hcount := circleCount_eq_generic_of_nearCircle
      cfg hadm.1 g hg (by omega)
    rw [hα] at hcount ⊢
    norm_num [Erdos506.v3Target, Erdos506.v3GenericTarget, Nat.choose] at hcount ⊢
    omega

theorem circleCount_ge_target_of_card_six
    {α : Type*} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (hadm : Admissible cfg)
    (hα : Fintype.card α = 6) :
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
      have hc4 := c4_le_three_of_card_six cfg hadm.1 hα
      rw [hα] at hpart ⊢
      norm_num [Erdos506.v3Target, Erdos506.v3GenericTarget, Nat.choose] at hpart ⊢
      omega
    · have hm5 : m = 5 := by omega
      have hg : (circleTrace cfg g.1).card = Fintype.card α - 1 := by
        change m = Fintype.card α - 1
        omega
      have hcount := circleCount_eq_generic_of_nearCircle
        cfg hadm.1 g hg (by omega)
      rw [hα] at hcount ⊢
      norm_num [Erdos506.v3Target, Erdos506.v3GenericTarget, Nat.choose] at hcount ⊢
      omega

theorem generic_target_attained_at_four_five_six :
    ∀ n ∈ ({4, 5, 6} : Finset ℕ),
      ∃ α : Type, ∃ _fin : Fintype α, ∃ _dec : DecidableEq α,
        ∃ cfg : Configuration α,
          Fintype.card α = n ∧ Admissible cfg ∧
            circleCount cfg = Erdos506.v3Target n := by
  intro n hn
  have hncases : n = 4 ∨ n = 5 ∨ n = 6 := by
    simpa only [Finset.mem_insert, Finset.mem_singleton] using hn
  have hn' : 4 ≤ n := by
    rcases hncases with rfl | rfl | rfl <;> omega
  have hnle : n ≤ 6 := by
    rcases hncases with rfl | rfl | rfl <;> omega
  obtain ⟨cfg, hcard, hadm, hcount⟩ :=
    exists_generic_extremal_configuration n hn'
  refine ⟨NearCircleLabels n, inferInstance, inferInstance, cfg, hcard, hadm, ?_⟩
  have hn8 : n ≠ 8 := by omega
  rw [Erdos506.v3Target_eq_generic hn8]
  exact hcount

end Erdos506.V3
