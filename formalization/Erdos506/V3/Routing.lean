import Erdos506.V3.Functional
import Erdos506.V3.RichCircle
import Erdos506.V3.RoutingArithmetic

/-!
# Richest-circle routing for V3

The theorem in this module assembles all finite counting and arithmetic for
the uniform range `n ≥ 11`.  Its sole remaining geometric input is the
explicit proposition `SummedMelchior cfg`.
-/

namespace Erdos506.V3

open Erdos506.V4
open scoped BigOperators

theorem determinedCircle_nonempty {α : Type*} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (hthree : NoThreeCollinear cfg)
    (hcard : 3 ≤ Fintype.card α) : Nonempty (DeterminedCircle cfg) := by
  have huniv : 3 ≤ (Finset.univ : Finset α).card := by simpa using hcard
  obtain ⟨s, hs, hscard⟩ := Finset.exists_subset_card_eq huniv
  let A : Erdos506.Finite.KSubset α 3 := ⟨s, hscard⟩
  exact ⟨circleOwner cfg hthree A⟩

theorem exists_richestCircle {α : Type*} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (hthree : NoThreeCollinear cfg)
    (hcard : 3 ≤ Fintype.card α) :
    ∃ g : DeterminedCircle cfg, ∀ c : DeterminedCircle cfg,
      (circleTrace cfg c.1).card ≤ (circleTrace cfg g.1).card := by
  classical
  letI : Nonempty (DeterminedCircle cfg) :=
    determinedCircle_nonempty cfg hthree hcard
  obtain ⟨g, _hg, hmax⟩ := Finset.exists_max_image
    (Finset.univ : Finset (DeterminedCircle cfg))
    (fun c => (circleTrace cfg c.1).card) Finset.univ_nonempty
  exact ⟨g, fun c => hmax c (Finset.mem_univ c)⟩

theorem circleCount_eq_choose_three_of_support_le_three
    {α : Type*} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (hthree : NoThreeCollinear cfg)
    (hcap : ∀ c : DeterminedCircle cfg, (circleTrace cfg c.1).card ≤ 3) :
    circleCount cfg = Nat.choose (Fintype.card α) 3 := by
  have hpart := triple_partition cfg hthree
  have hterm : ∀ c : DeterminedCircle cfg,
      Nat.choose (circleTrace cfg c.1).card 3 = 1 := by
    intro c
    have hc : (circleTrace cfg c.1).card = 3 :=
      Nat.le_antisymm (hcap c) (circleSupport_card_ge_three cfg c)
    rw [hc]
    norm_num [Nat.choose]
  simp_rw [hterm] at hpart
  simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul, Nat.mul_one] at hpart
  rw [circleCount_eq_card_determinedCircle cfg]
  exact hpart

/-- Complete richest-circle routing in the uniform range, conditional only
on the named summed-Melchior statement for the concrete configuration. -/
theorem circleCount_ge_generic_of_summedMelchior
    {α : Type*} [Fintype α] (cfg : Configuration α)
    (hcard : 11 ≤ Fintype.card α) (hadm : Admissible cfg)
    (hmel : SummedMelchior cfg) :
    Erdos506.v3GenericTarget (Fintype.card α) ≤ circleCount cfg := by
  classical
  obtain ⟨g, hmax⟩ := exists_richestCircle cfg hadm.1 (by omega)
  let n := Fintype.card α
  let m := (circleTrace cfg g.1).card
  have hmge : 3 ≤ m := circleSupport_card_ge_three cfg g
  have hmlt : m < n := hadm.2 g.1
  by_cases hrich : n / 2 < m
  · exact (v3GenericTarget_le_pencilBound n m hcard hrich hmlt).trans
      (pencilBound_le_circleCount cfg hadm.1 g)
  · have hmhalf : m ≤ n / 2 := by omega
    by_cases hm3 : m = 3
    · have hcap3 : ∀ c : DeterminedCircle cfg,
          (circleTrace cfg c.1).card ≤ 3 := by
        intro c
        simpa [m, hm3] using hmax c
      rw [circleCount_eq_choose_three_of_support_le_three cfg hadm.1 hcap3]
      exact v3GenericTarget_le_choose_three n (by omega)
    · have hm4 : 4 ≤ m := by omega
      have hcap : ∀ c : DeterminedCircle cfg,
          (circleTrace cfg c.1).card ≤ m := by
        intro c
        simpa [m] using hmax c
      have hfun := boundedSupportLower_le_circleCount cfg hadm.1
        (by omega) hmel m hm4 hcap
      have harith := genericTarget_sub_one_lt_boundedSupportLower
        n m hcard hm4 hmhalf
      have hltQ : (Erdos506.v3GenericTarget n : ℚ) <
          (circleCount cfg : ℚ) + 1 := by
        linarith
      have hltNat : Erdos506.v3GenericTarget n < circleCount cfg + 1 := by
        exact_mod_cast hltQ
      have hresult : Erdos506.v3GenericTarget n ≤ circleCount cfg := by omega
      simpa [n] using hresult

theorem circleCount_ge_target_of_summedMelchior
    {α : Type*} [Fintype α] (cfg : Configuration α)
    (hcard : 11 ≤ Fintype.card α) (hadm : Admissible cfg)
    (hmel : SummedMelchior cfg) :
    Erdos506.v3Target (Fintype.card α) ≤ circleCount cfg := by
  rw [Erdos506.v3Target_eq_generic (by omega)]
  exact circleCount_ge_generic_of_summedMelchior cfg hcard hadm hmel

end Erdos506.V3
