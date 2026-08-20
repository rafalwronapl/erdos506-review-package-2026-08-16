import Erdos506.Block.Counts
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Incidence moments of finite block families

The results here are generic finite double counts.  They apply to arbitrary
subfamilies of a tagged block system and contain no geometric assumptions
beyond the unique triple-owner property already present in `BlockSystem`.
-/

namespace Erdos506.Block

open scoped BigOperators

namespace BlockSystem

variable {Point Block : Type*} [Fintype Point] [Fintype Block]
  [DecidableEq Point]

/-- Points lying in every support in a finite block subfamily. -/
def commonSupport (S : BlockSystem Point Block) (A : Finset Block) :
    Finset Point :=
  Finset.univ.filter fun p => ∀ b ∈ A, p ∈ S.support b

@[simp] theorem mem_commonSupport (S : BlockSystem Point Block)
    {A : Finset Block} {p : Point} :
    p ∈ S.commonSupport A ↔ ∀ b ∈ A, p ∈ S.support b := by
  simp [commonSupport]

/-- Weighted point--block Fubini identity. -/
theorem weighted_incidence_fubini
    {R : Type*} [CommSemiring R]
    (S : BlockSystem Point Block) (F : Finset Block) (w : Block → R) :
    (∑ p : Point, ∑ b ∈ F.filter (fun b => p ∈ S.support b), w b) =
      ∑ b ∈ F, ((S.support b).card : R) * w b := by
  classical
  simp only [Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b hb
  rw [← Finset.sum_filter]
  simp

/-- First incidence moment. -/
theorem first_moment (S : BlockSystem Point Block) (F : Finset Block) :
    (∑ p : Point, S.degreeIn F p) =
      ∑ b ∈ F, (S.support b).card :=
  S.sum_degreeIn F

/-- Taking powersets commutes with filtering when the resulting subsets are
filtered by pointwise satisfaction of the same predicate. -/
theorem powersetCard_filter_eq
    {α : Type*} [DecidableEq α] (F : Finset α) (r : ℕ)
    (q : α → Prop) [DecidablePred q] :
    (F.filter q).powersetCard r =
      (F.powersetCard r).filter (fun A => ∀ a ∈ A, q a) := by
  ext A
  simp only [Finset.mem_powersetCard, Finset.mem_filter]
  constructor
  · rintro ⟨hAF, hcard⟩
    exact ⟨⟨fun a ha => (Finset.mem_filter.mp (hAF ha)).1, hcard⟩,
      fun a ha => (Finset.mem_filter.mp (hAF ha)).2⟩
  · rintro ⟨⟨hAF, hcard⟩, hq⟩
    exact ⟨fun a ha => Finset.mem_filter.mpr ⟨hAF ha, hq a ha⟩, hcard⟩

/-- Binomial degree moments count pairs `(point, r-subfamily)` in the two
possible orders. -/
theorem binomial_degree_moment (S : BlockSystem Point Block)
    (F : Finset Block) (r : ℕ) :
    (∑ p : Point, Nat.choose (S.degreeIn F p) r) =
      ∑ A ∈ F.powersetCard r, (S.commonSupport A).card := by
  classical
  calc
    (∑ p : Point, Nat.choose (S.degreeIn F p) r) =
        ∑ p : Point,
          ((F.filter fun b => p ∈ S.support b).powersetCard r).card := by
      apply Fintype.sum_congr
      intro p
      simp [degreeIn]
    _ = ∑ p : Point,
        (((F.powersetCard r).filter fun A =>
          ∀ b ∈ A, p ∈ S.support b).card) := by
      apply Fintype.sum_congr
      intro p
      apply congrArg Finset.card
      ext A
      simp only [Finset.mem_powersetCard, Finset.mem_filter]
      constructor
      · rintro ⟨hAF, hcard⟩
        exact ⟨⟨fun b hb => (Finset.mem_filter.mp (hAF hb)).1, hcard⟩,
          fun b hb => (Finset.mem_filter.mp (hAF hb)).2⟩
      · rintro ⟨⟨hAF, hcard⟩, hp⟩
        exact ⟨fun b hb => Finset.mem_filter.mpr ⟨hAF hb, hp b hb⟩, hcard⟩
    _ = ∑ p : Point, ∑ A ∈ F.powersetCard r,
        if (∀ b ∈ A, p ∈ S.support b) then 1 else 0 := by
      apply Fintype.sum_congr
      intro p
      rw [Finset.card_eq_sum_ones, Finset.sum_filter]
    _ = ∑ A ∈ F.powersetCard r, ∑ p : Point,
        if (∀ b ∈ A, p ∈ S.support b) then 1 else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ A ∈ F.powersetCard r, (S.commonSupport A).card := by
      apply Finset.sum_congr rfl
      intro A hA
      simp only [commonSupport, Finset.card_eq_sum_ones, Finset.sum_filter]
      apply Fintype.sum_congr
      intro p
      by_cases hp : ∀ b ∈ A, p ∈ S.support b <;> simp [hp]

theorem commonSupport_pair (S : BlockSystem Point Block)
    [DecidableEq Block] {b c : Block} :
    S.commonSupport {b, c} = S.support b ∩ S.support c := by
  ext p
  simp [commonSupport]

/-- In a triple-owned system, two distinct blocks have at most two common
points. -/
theorem commonSupport_card_le_two (S : BlockSystem Point Block)
    {A : Finset Block} (hA : A.card = 2) :
    (S.commonSupport A).card ≤ 2 := by
  classical
  obtain ⟨b, c, hbc, rfl⟩ := Finset.card_eq_two.mp hA
  rw [S.commonSupport_pair]
  have hlt := S.distinct_block_inter_card_lt_three hbc
  omega

/-- The reusable pair-moment bound for any finite block subfamily. -/
theorem second_moment_le_two_choose (S : BlockSystem Point Block)
    (F : Finset Block) :
    (∑ p : Point, Nat.choose (S.degreeIn F p) 2) ≤
      2 * Nat.choose F.card 2 := by
  rw [S.binomial_degree_moment F 2]
  calc
    (∑ A ∈ F.powersetCard 2, (S.commonSupport A).card) ≤
        ∑ A ∈ F.powersetCard 2, 2 := by
      apply Finset.sum_le_sum
      intro A hA
      exact S.commonSupport_card_le_two (Finset.mem_powersetCard.mp hA).2
    _ = 2 * Nat.choose F.card 2 := by
      simp [Nat.mul_comm]

end BlockSystem
end Erdos506.Block
