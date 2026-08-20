import Erdos506.V3.RichCircle

/-!
# Exact count for the near-circle incidence type

If one determined circle contains all but one selected point, every other
determined circle has exactly three selected points.  The triple partition
then gives the exact generic V3 value, independently of any construction of
such a configuration.
-/

namespace Erdos506.V3

open Erdos506.V4
open scoped BigOperators

theorem support_card_eq_three_of_ne_nearCircle
    {α : Type*} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (hthree : NoThreeCollinear cfg)
    (g c : DeterminedCircle cfg)
    (hg : (circleTrace cfg g.1).card = Fintype.card α - 1)
    (hcg : c ≠ g) :
    (circleTrace cfg c.1).card = 3 := by
  classical
  let S := circleTrace cfg c.1
  let G := circleTrace cfg g.1
  have hinter := (circleOwnership cfg hthree).card_inter_lt_of_ne hcg
  change (S ∩ G).card < 3 at hinter
  have houtsub : S \ G ⊆ outsiderLabels cfg g := by
    intro x hx
    exact mem_outsiderLabels.mpr (Finset.mem_sdiff.mp hx).2
  have houtcard : (S \ G).card ≤ 1 := by
    have hle := Finset.card_le_card houtsub
    rw [card_outsiderLabels cfg g, hg] at hle
    omega
  have hsplit := Finset.card_sdiff_add_card_inter S G
  have hupper : S.card ≤ 3 := by omega
  exact Nat.le_antisymm hupper (circleSupport_card_ge_three cfg c)

/-- A determined circle through `n-1` selected points forces exactly the
generic V3 circle count. -/
theorem circleCount_eq_generic_of_nearCircle
    {α : Type*} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (hthree : NoThreeCollinear cfg)
    (g : DeterminedCircle cfg)
    (hg : (circleTrace cfg g.1).card = Fintype.card α - 1)
    (hcard : 4 ≤ Fintype.card α) :
    circleCount cfg = Erdos506.v3GenericTarget (Fintype.card α) := by
  classical
  letI : Nonempty (DeterminedCircle cfg) := ⟨g⟩
  let f : DeterminedCircle cfg → ℕ :=
    fun c => Nat.choose (circleTrace cfg c.1).card 3
  have hother : ∀ c ∈ (Finset.univ.erase g : Finset (DeterminedCircle cfg)),
      f c = 1 := by
    intro c hc
    have hcg : c ≠ g := Finset.ne_of_mem_erase hc
    have hc3 := support_card_eq_three_of_ne_nearCircle cfg hthree g c hg hcg
    simp [f, hc3]
  have herase :
      (∑ c ∈ (Finset.univ.erase g : Finset (DeterminedCircle cfg)), f c) =
        (Finset.univ.erase g : Finset (DeterminedCircle cfg)).card := by
    calc
      (∑ c ∈ (Finset.univ.erase g : Finset (DeterminedCircle cfg)), f c) =
          ∑ _c ∈ (Finset.univ.erase g : Finset (DeterminedCircle cfg)), 1 := by
        apply Finset.sum_congr rfl
        intro c hc
        exact hother c hc
      _ = (Finset.univ.erase g : Finset (DeterminedCircle cfg)).card := by simp
  have hfg : f g = Nat.choose (Fintype.card α - 1) 3 := by
    simp [f, hg]
  have hpart : (∑ c : DeterminedCircle cfg, f c) =
      Nat.choose (Fintype.card α) 3 := by
    simpa [f] using triple_partition cfg hthree
  have hsplit :
      (Finset.univ.erase g : Finset (DeterminedCircle cfg)).card +
          Nat.choose (Fintype.card α - 1) 3 =
        Nat.choose (Fintype.card α) 3 := by
    calc
      (Finset.univ.erase g : Finset (DeterminedCircle cfg)).card +
          Nat.choose (Fintype.card α - 1) 3 =
          (∑ c ∈ (Finset.univ.erase g : Finset (DeterminedCircle cfg)), f c) + f g := by
            rw [herase, hfg]
      _ = ∑ c : DeterminedCircle cfg, f c :=
        Finset.sum_erase_add Finset.univ f (Finset.mem_univ g)
      _ = Nat.choose (Fintype.card α) 3 := hpart
  have heraseCard :
      (Finset.univ.erase g : Finset (DeterminedCircle cfg)).card + 1 =
        Fintype.card (DeterminedCircle cfg) := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ g), Finset.card_univ]
    have hnonzero : 0 < Fintype.card (DeterminedCircle cfg) :=
      Fintype.card_pos
    omega
  have hpascal := Nat.choose_succ_succ' (Fintype.card α - 1) 2
  have hnstep : Fintype.card α - 1 + 1 = Fintype.card α :=
    Nat.sub_add_cancel (by omega)
  rw [hnstep] at hpascal
  norm_num at hpascal
  rw [circleCount_eq_card_determinedCircle cfg, Erdos506.v3GenericTarget]
  omega

end Erdos506.V3
