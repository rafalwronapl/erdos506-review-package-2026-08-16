import Erdos506.Block.System
import Erdos506.Finite.Bonferroni

/-!
# Relative two-by-two capacity between disjoint point sets

This file isolates a finite consequence of unique triple ownership.  If every
block in a family contains two points of `D`, then, for each fixed pair in a
disjoint set `E`, those two-point `D`-traces form a matching.  Double-counting
the pairs in `E` therefore gives the stated capacity bound.
-/

namespace Erdos506.Block

open scoped BigOperators

namespace BlockSystem

variable {Point Block : Type*} [Fintype Point] [Fintype Block]
  [DecidableEq Point]

/-- If every block in `F` meets `D` in two points and `D` is disjoint from
`E`, then pairs cut out on `E` have total multiplicity at most the matching
capacity of `D` times the number of pairs in `E`.

Only unique ownership of triples is used.  In particular, the statement is
independent of the line/circle tag on a block. -/
theorem relative_two_two_capacity_between
    (S : BlockSystem Point Block) (D E : Finset Point) (F : Finset Block)
    (hDE : Disjoint D E)
    (htwoD : ∀ b ∈ F, (S.support b ∩ D).card = 2) :
    (∑ b ∈ F, Nat.choose (S.support b ∩ E).card 2) ≤
      D.card / 2 * Nat.choose E.card 2 := by
  classical
  let Q : Finset (Finset Point) := E.powersetCard 2
  let BFor : Finset Point → Finset Block := fun A =>
    F.filter fun b => A ⊆ S.support b ∩ E
  let insidePairs : Finset Point → Finset (Finset Point) := fun A =>
    (BFor A).image fun b => S.support b ∩ D

  have hsupportDisjoint (A : Finset Point) (hA : A ∈ Q)
      {b c : Block} (hb : b ∈ BFor A) (hc : c ∈ BFor A)
      (hbc : b ≠ c) :
      Disjoint (S.support b ∩ D) (S.support c ∩ D) := by
    have hAspec := Finset.mem_powersetCard.mp hA
    have hAcard : A.card = 2 := hAspec.2
    have hbA : A ⊆ S.support b ∩ E :=
      (Finset.mem_filter.mp hb).2
    have hcA : A ⊆ S.support c ∩ E :=
      (Finset.mem_filter.mp hc).2
    rw [Finset.disjoint_left]
    intro z hzb hzc
    have hzD : z ∈ D := (Finset.mem_inter.mp hzb).2
    have hznotA : z ∉ A := by
      intro hzA
      have hzE : z ∈ E := (Finset.mem_inter.mp (hbA hzA)).2
      exact (Finset.disjoint_left.mp hDE hzD) hzE
    have hsub : insert z A ⊆ S.support b ∩ S.support c := by
      intro w hw
      rcases Finset.mem_insert.mp hw with rfl | hwA
      · exact Finset.mem_inter.mpr
          ⟨(Finset.mem_inter.mp hzb).1, (Finset.mem_inter.mp hzc).1⟩
      · exact Finset.mem_inter.mpr
          ⟨(Finset.mem_inter.mp (hbA hwA)).1,
            (Finset.mem_inter.mp (hcA hwA)).1⟩
    have hcard : (insert z A).card = 3 := by
      rw [Finset.card_insert_of_notMem hznotA, hAcard]
    have hle := Finset.card_le_card hsub
    have hlt := S.distinct_block_inter_card_lt_three hbc
    omega

  have hcapacity (A : Finset Point) (hA : A ∈ Q) :
      (BFor A).card ≤ D.card / 2 := by
    have hsub : ∀ p ∈ insidePairs A, p ⊆ D := by
      intro p hp
      obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hp
      exact Finset.inter_subset_right
    have hpair : ∀ p ∈ insidePairs A, p.card = 2 := by
      intro p hp
      obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hp
      exact htwoD b (Finset.mem_filter.mp hb).1
    have hdisj :
        ((insidePairs A : Finset (Finset Point)) :
          Set (Finset Point)).PairwiseDisjoint id := by
      intro p hp q hq hpq
      obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hp
      obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hq
      have hbc : b ≠ c := by
        intro hbc
        subst c
        exact hpq rfl
      exact hsupportDisjoint A hA hb hc hbc
    have hinj : Set.InjOn (fun b => S.support b ∩ D) (BFor A) := by
      intro b hb c hc heq
      by_contra hbc
      have hdis := hsupportDisjoint A hA hb hc hbc
      have hself : Disjoint (S.support b ∩ D) (S.support b ∩ D) := by
        simpa [heq] using hdis
      have hempty : S.support b ∩ D = ∅ := disjoint_self.mp hself
      have hbF : b ∈ F := (Finset.mem_filter.mp hb).1
      have := htwoD b hbF
      rw [hempty] at this
      simp at this
    have hcard : (insidePairs A).card = (BFor A).card := by
      exact Finset.card_image_iff.mpr hinj
    have hmatch := Erdos506.Finite.card_le_half_of_pairwiseDisjoint_pairs
      D (insidePairs A) hsub hpair hdisj
    rwa [hcard] at hmatch

  have hflagCard (b : Block) :
      Nat.choose (S.support b ∩ E).card 2 =
        (Q.filter fun A => A ⊆ S.support b ∩ E).card := by
    rw [← Finset.card_powersetCard]
    apply congrArg Finset.card
    ext A
    simp only [Q, Finset.mem_filter, Finset.mem_powersetCard]
    constructor
    · intro hA
      exact ⟨⟨hA.1.trans Finset.inter_subset_right, hA.2⟩, hA.1⟩
    · rintro ⟨hAQ, hsub⟩
      exact ⟨hsub, hAQ.2⟩

  calc
    (∑ b ∈ F, Nat.choose (S.support b ∩ E).card 2) =
        ∑ b ∈ F, (Q.filter fun A => A ⊆ S.support b ∩ E).card := by
      apply Finset.sum_congr rfl
      intro b hb
      exact hflagCard b
    _ = ∑ b ∈ F, ∑ A ∈ Q,
        if A ⊆ S.support b ∩ E then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro b hb
      exact Finset.card_filter _ Q
    _ = ∑ A ∈ Q, ∑ b ∈ F,
        if A ⊆ S.support b ∩ E then 1 else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ A ∈ Q, (BFor A).card := by
      apply Finset.sum_congr rfl
      intro A hA
      symm
      exact Finset.card_filter _ F
    _ ≤ ∑ _A ∈ Q, D.card / 2 := by
      apply Finset.sum_le_sum
      intro A hA
      exact hcapacity A hA
    _ = D.card / 2 * Nat.choose E.card 2 := by
      simp [Q, Nat.mul_comm]

end BlockSystem
end Erdos506.Block
