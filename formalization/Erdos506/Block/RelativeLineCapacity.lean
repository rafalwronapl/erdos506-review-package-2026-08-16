import Erdos506.Block.RelativeRows

/-!
# Relative capacity for chord lines

For a fixed selected set `D`, consider line blocks meeting `D` in two
points.  Through any point outside `D`, their two-point traces in `D` are a
matching: two distinct full lines cannot share both the outside point and a
point of `D`.  Double counting gives the first-moment capacity used in the
five-circle branch at nine points.
-/

namespace Erdos506.Block.BlockSystem

open Erdos506.Finite
open scoped BigOperators

universe u v

variable {Point : Type u} {Block : Type v}
  [Fintype Point] [Fintype Block] [DecidableEq Point]

/-- If every line in `F` meets `D` in two points, then the total number of
outside incidences is at most `⌊|D|/2⌋` per outside point. -/
theorem relative_line_two_one_capacity
    (S : BlockSystem Point Block) (D : Finset Point)
    (F : Finset (S.LineBlock))
    (htwo : ∀ b ∈ F, (S.support b.1 ∩ D).card = 2) :
    (∑ b ∈ F, (S.support b.1 \ D).card) ≤
      D.card / 2 * (Fintype.card Point - D.card) := by
  classical
  let X : Finset Point := Finset.univ \ D
  let BFor : Point → Finset (S.LineBlock) := fun x =>
    F.filter fun b => x ∈ S.support b.1 \ D
  let insidePairs : Point → Finset (Finset Point) := fun x =>
    (BFor x).image fun b => S.support b.1 ∩ D

  have hsupportDisjoint (x : Point) (hx : x ∈ X)
      {b c : S.LineBlock} (hb : b ∈ BFor x) (hc : c ∈ BFor x)
      (hbc : b ≠ c) :
      Disjoint (S.support b.1 ∩ D) (S.support c.1 ∩ D) := by
    rw [Finset.disjoint_left]
    intro z hzb hzc
    have hxnotD : x ∉ D := (Finset.mem_sdiff.mp hx).2
    have hzD : z ∈ D := (Finset.mem_inter.mp hzb).2
    have hxz : x ≠ z := fun h => hxnotD (h ▸ hzD)
    have hxb : x ∈ S.support b.1 :=
      (Finset.mem_sdiff.mp (Finset.mem_filter.mp hb).2).1
    have hxc : x ∈ S.support c.1 :=
      (Finset.mem_sdiff.mp (Finset.mem_filter.mp hc).2).1
    have hsub : {x, z} ⊆ S.support b.1 ∩ S.support c.1 := by
      intro w hw
      simp only [Finset.mem_insert, Finset.mem_singleton] at hw
      rcases hw with rfl | rfl
      · exact Finset.mem_inter.mpr ⟨hxb, hxc⟩
      · exact Finset.mem_inter.mpr
          ⟨(Finset.mem_inter.mp hzb).1, (Finset.mem_inter.mp hzc).1⟩
    have hcard := Finset.card_le_card hsub
    have hlt := S.distinct_line_inter_card_lt_two hbc
    rw [Finset.card_pair hxz] at hcard
    omega

  have hcapacity (x : Point) (hx : x ∈ X) :
      (BFor x).card ≤ D.card / 2 := by
    have hsub : ∀ p ∈ insidePairs x, p ⊆ D := by
      intro p hp
      obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hp
      exact Finset.inter_subset_right
    have hpair : ∀ p ∈ insidePairs x, p.card = 2 := by
      intro p hp
      obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hp
      exact htwo b (Finset.mem_filter.mp hb).1
    have hdisj :
        ((insidePairs x : Finset (Finset Point)) :
          Set (Finset Point)).PairwiseDisjoint id := by
      intro p hp q hq hpq
      obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hp
      obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hq
      have hbc : b ≠ c := by
        intro h
        subst c
        exact hpq rfl
      exact hsupportDisjoint x hx hb hc hbc
    have hinj :
        Set.InjOn (fun b : S.LineBlock => S.support b.1 ∩ D) (BFor x) := by
      intro b hb c hc heq
      by_contra hbc
      have hdis := hsupportDisjoint x hx hb hc hbc
      have hself : Disjoint (S.support b.1 ∩ D) (S.support b.1 ∩ D) := by
        simpa [heq] using hdis
      have hempty : S.support b.1 ∩ D = ∅ := disjoint_self.mp hself
      have hbF : b ∈ F := (Finset.mem_filter.mp hb).1
      have := htwo b hbF
      rw [hempty] at this
      simp at this
    have hcard : (insidePairs x).card = (BFor x).card :=
      Finset.card_image_iff.mpr hinj
    have hmatch := card_le_half_of_pairwiseDisjoint_pairs
      D (insidePairs x) hsub hpair hdisj
    rwa [hcard] at hmatch

  have hdouble :
      (∑ b ∈ F, (S.support b.1 \ D).card) =
        ∑ x ∈ X, (BFor x).card := by
    calc
      (∑ b ∈ F, (S.support b.1 \ D).card) =
          ∑ b ∈ F, ∑ x ∈ X,
            if x ∈ S.support b.1 \ D then 1 else 0 := by
        apply Finset.sum_congr rfl
        intro b hb
        rw [← Finset.sum_filter]
        have heq : X.filter (fun x => x ∈ S.support b.1 \ D) =
            S.support b.1 \ D := by
          ext x
          simp [X]
        rw [heq]
        simp
      _ = ∑ x ∈ X, ∑ b ∈ F,
            if x ∈ S.support b.1 \ D then 1 else 0 := by
        rw [Finset.sum_comm]
      _ = ∑ x ∈ X, (BFor x).card := by
        apply Finset.sum_congr rfl
        intro x hx
        rw [← Finset.sum_filter]
        simp [BFor]
  rw [hdouble]
  calc
    (∑ x ∈ X, (BFor x).card) ≤
        ∑ _x ∈ X, D.card / 2 := by
      exact Finset.sum_le_sum fun x hx => hcapacity x hx
    _ = D.card / 2 * X.card := by
      simp [Nat.mul_comm]
    _ = D.card / 2 * (Fintype.card Point - D.card) := by
      congr 1
      dsimp only [X]
      rw [Finset.card_sdiff_of_subset (Finset.subset_univ D),
        Finset.card_univ]

end Erdos506.Block.BlockSystem
