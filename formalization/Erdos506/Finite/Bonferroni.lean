import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Powerset
import Mathlib.Tactic

/-!
# Finite two-term Bonferroni bounds

The lemmas here are purely finite.  They give the exact lower bound for a
union of equal-size families with bounded pairwise overlap and the matching
bound for disjoint two-subsets.
-/

namespace Erdos506.Finite

open scoped BigOperators

theorem card_biUnion_lower_of_card_inter_le
    {ι β : Type*} [DecidableEq ι] [DecidableEq β]
    (I : Finset ι) (F : ι → Finset β) (a h : ℕ)
    (hcard : ∀ i ∈ I, (F i).card = a)
    (hinter : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → (F i ∩ F j).card ≤ h) :
    I.card * a ≤ (I.biUnion F).card + Nat.choose I.card 2 * h := by
  classical
  induction I using Finset.induction_on with
  | empty => simp
  | @insert i S hi ih =>
      have ih' := ih
        (fun j hj => hcard j (by simp [hj]))
        (fun j hj k hk hjk => hinter j (by simp [hj]) k (by simp [hk]) hjk)
      have hinterUnion :
          ((S.biUnion F) ∩ F i).card ≤ S.card * h := by
        have hsub : (S.biUnion F) ∩ F i ⊆
            S.biUnion (fun j => F j ∩ F i) := by
          intro x hx
          rcases Finset.mem_inter.mp hx with ⟨hxU, hxi⟩
          rcases Finset.mem_biUnion.mp hxU with ⟨j, hjS, hxj⟩
          exact Finset.mem_biUnion.mpr ⟨j, hjS, Finset.mem_inter.mpr ⟨hxj, hxi⟩⟩
        calc
          ((S.biUnion F) ∩ F i).card ≤
              (S.biUnion (fun j => F j ∩ F i)).card :=
            Finset.card_le_card hsub
          _ ≤ ∑ j ∈ S, (F j ∩ F i).card := Finset.card_biUnion_le
          _ ≤ ∑ _j ∈ S, h := by
            apply Finset.sum_le_sum
            intro j hj
            exact hinter j (by simp [hj]) i (by simp) (by
              intro hji
              subst j
              exact hi hj)
          _ = S.card * h := by simp
      have hunion := Finset.card_union_add_card_inter (F i) (S.biUnion F)
      have hinterUnion' :
          (F i ∩ S.biUnion F).card ≤ S.card * h := by
        simpa [Finset.inter_comm] using hinterUnion
      have hiCard : (F i).card = a := hcard i (by simp)
      have hchoose : Nat.choose (S.card + 1) 2 =
          S.card + Nat.choose S.card 2 := by
        simpa using Nat.choose_succ_succ S.card 1
      simp only [Finset.biUnion_insert, Finset.card_insert_of_notMem hi]
      rw [hchoose]
      simp only [Nat.add_mul]
      omega

/-- Two-term Bonferroni when every member of the family has cardinality at
least `a`.  This is the form needed when a geometric pencil may lose a
different matching of exceptional pairs at each centre. -/
theorem card_biUnion_lower_of_card_ge_inter_le
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    (I : Finset α) (F : α → Finset β) (a h : ℕ)
    (hcard : ∀ i ∈ I, a ≤ (F i).card)
    (hinter : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → (F i ∩ F j).card ≤ h) :
    I.card * a ≤ (I.biUnion F).card + Nat.choose I.card 2 * h := by
  classical
  induction I using Finset.induction_on with
  | empty => simp
  | @insert i S hi ih =>
      have ih' := ih
        (fun j hj => hcard j (by simp [hj]))
        (fun j hj k hk hjk => hinter j (by simp [hj]) k (by simp [hk]) hjk)
      have hinterUnion :
          ((S.biUnion F) ∩ F i).card ≤ S.card * h := by
        have hsub : (S.biUnion F) ∩ F i ⊆
            S.biUnion (fun j => F j ∩ F i) := by
          intro x hx
          rcases Finset.mem_inter.mp hx with ⟨hxU, hxi⟩
          rcases Finset.mem_biUnion.mp hxU with ⟨j, hjS, hxj⟩
          exact Finset.mem_biUnion.mpr ⟨j, hjS, Finset.mem_inter.mpr ⟨hxj, hxi⟩⟩
        calc
          ((S.biUnion F) ∩ F i).card ≤
              (S.biUnion (fun j => F j ∩ F i)).card :=
            Finset.card_le_card hsub
          _ ≤ ∑ j ∈ S, (F j ∩ F i).card := Finset.card_biUnion_le
          _ ≤ ∑ _j ∈ S, h := by
            apply Finset.sum_le_sum
            intro j hj
            exact hinter j (by simp [hj]) i (by simp) (by
              intro hji
              subst j
              exact hi hj)
          _ = S.card * h := by simp
      have hunion := Finset.card_union_add_card_inter (F i) (S.biUnion F)
      have hinterUnion' :
          (F i ∩ S.biUnion F).card ≤ S.card * h := by
        simpa [Finset.inter_comm] using hinterUnion
      have hiCard : a ≤ (F i).card := hcard i (by simp)
      have hchoose : Nat.choose (S.card + 1) 2 =
          S.card + Nat.choose S.card 2 := by
        simpa using Nat.choose_succ_succ S.card 1
      simp only [Finset.biUnion_insert, Finset.card_insert_of_notMem hi]
      rw [hchoose]
      simp only [Nat.add_mul]
      omega

theorem card_le_half_of_pairwiseDisjoint_pairs
    {α : Type*} [DecidableEq α] (G : Finset α) (P : Finset (Finset α))
    (hsub : ∀ p ∈ P, p ⊆ G)
    (hpair : ∀ p ∈ P, p.card = 2)
    (hdisj : (P : Set (Finset α)).PairwiseDisjoint id) :
    P.card ≤ G.card / 2 := by
  classical
  have hUnionSub : P.biUnion id ⊆ G := by
    intro x hx
    rcases Finset.mem_biUnion.mp hx with ⟨p, hp, hxp⟩
    exact hsub p hp hxp
  have hUnionCard : (P.biUnion id).card = 2 * P.card := by
    rw [Finset.card_biUnion hdisj]
    calc
      (∑ p ∈ P, p.card) = ∑ _p ∈ P, 2 := by
        apply Finset.sum_congr rfl
        intro p hp
        exact hpair p hp
      _ = 2 * P.card := by simp [Nat.mul_comm]
  have hle := Finset.card_le_card hUnionSub
  rw [hUnionCard] at hle
  omega

end Erdos506.Finite
