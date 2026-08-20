import Erdos506.Finite.Packing
import Erdos506.V3.Census

/-!
# Complement packings for the small V3 cases

Four-point circle supports have pairwise intersection at most two.  On six
or seven labels their complements are therefore, respectively, disjoint
pairs or a packing of triples in which no pair is repeated.
-/

namespace Erdos506.V3

open Erdos506.Finite
open Erdos506.V4

noncomputable def circlesOfSize {α : Type*} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (s : ℕ) : Finset (DeterminedCircle cfg) := by
  letI : DecidableEq (DeterminedCircle cfg) := Classical.decEq _
  exact Finset.univ.filter fun c => (circleTrace cfg c.1).card = s

@[simp] theorem mem_circlesOfSize {α : Type*} [Fintype α] [DecidableEq α]
    {cfg : Configuration α} {s : ℕ} {c : DeterminedCircle cfg} :
    c ∈ circlesOfSize cfg s ↔ (circleTrace cfg c.1).card = s := by
  letI : DecidableEq (DeterminedCircle cfg) := Classical.decEq _
  simp [circlesOfSize]

theorem card_circlesOfSize {α : Type*} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (s : ℕ) :
    (circlesOfSize cfg s).card = circleCensus cfg s := by
  rfl

theorem circleTrace_injective {α : Type*} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (hthree : NoThreeCollinear cfg) :
    Function.Injective (fun c : DeterminedCircle cfg => circleTrace cfg c.1) := by
  letI : DecidableEq (DeterminedCircle cfg) := Classical.decEq _
  intro c d htrace
  by_contra hne
  have hlt := (circleOwnership cfg hthree).card_inter_lt_of_ne hne
  change (circleTrace cfg c.1 ∩ circleTrace cfg d.1).card < 3 at hlt
  have hge := circleSupport_card_ge_three cfg c
  change circleTrace cfg c.1 = circleTrace cfg d.1 at htrace
  rw [htrace] at hge
  rw [htrace, Finset.inter_self] at hlt
  omega

noncomputable def circleComplement {α : Type*} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (c : DeterminedCircle cfg) : Finset α := by
  exact Finset.univ \ circleTrace cfg c.1

theorem card_circleComplement {α : Type*} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (c : DeterminedCircle cfg) :
    (circleComplement cfg c).card =
      Fintype.card α - (circleTrace cfg c.1).card := by
  rw [circleComplement,
    Finset.card_sdiff_of_subset (Finset.subset_univ (circleTrace cfg c.1))]
  simp

theorem circleComplement_injective {α : Type*} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (hthree : NoThreeCollinear cfg) :
    Function.Injective (circleComplement cfg) := by
  intro c d hcomp
  apply circleTrace_injective cfg hthree
  ext x
  have hx := Finset.ext_iff.mp hcomp x
  simp only [circleComplement, Finset.mem_sdiff, Finset.mem_univ, true_and] at hx
  constructor
  · intro hxc
    by_contra hxd
    exact (hx.mpr hxd) hxc
  · intro hxd
    by_contra hxc
    exact (hx.mp hxc) hxd

noncomputable def circleComplementsOfSize {α : Type*} [Fintype α]
    [DecidableEq α]
    (cfg : Configuration α) (s : ℕ) : Finset (Finset α) := by
  letI : DecidableEq (DeterminedCircle cfg) := Classical.decEq _
  exact (circlesOfSize cfg s).image (circleComplement cfg)

theorem card_circleComplementsOfSize {α : Type*} [Fintype α]
    [DecidableEq α]
    (cfg : Configuration α) (hthree : NoThreeCollinear cfg) (s : ℕ) :
    (circleComplementsOfSize cfg s).card = circleCensus cfg s := by
  letI : DecidableEq (DeterminedCircle cfg) := Classical.decEq _
  rw [circleComplementsOfSize,
    Finset.card_image_of_injective _ (circleComplement_injective cfg hthree),
    card_circlesOfSize]

theorem circleComplement_inter_eq {α : Type*} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (c d : DeterminedCircle cfg) :
    circleComplement cfg c ∩ circleComplement cfg d =
      Finset.univ \ (circleTrace cfg c.1 ∪ circleTrace cfg d.1) := by
  ext x
  simp [circleComplement]

theorem circleComplement_inter_card_add_union_card {α : Type*} [Fintype α]
    [DecidableEq α]
    (cfg : Configuration α) (c d : DeterminedCircle cfg) :
    (circleComplement cfg c ∩ circleComplement cfg d).card +
        (circleTrace cfg c.1 ∪ circleTrace cfg d.1).card = Fintype.card α := by
  rw [circleComplement_inter_eq]
  simpa using Finset.card_sdiff_add_card_eq_card
    (Finset.subset_univ (circleTrace cfg c.1 ∪ circleTrace cfg d.1))

theorem circleComplement_inter_lt_one_of_card_six_size_four
    {α : Type*} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (hthree : NoThreeCollinear cfg)
    (hα : Fintype.card α = 6)
    {c d : DeterminedCircle cfg}
    (hc : (circleTrace cfg c.1).card = 4)
    (hd : (circleTrace cfg d.1).card = 4) (hcd : c ≠ d) :
    (circleComplement cfg c ∩ circleComplement cfg d).card < 1 := by
  have hinter := (circleOwnership cfg hthree).card_inter_lt_of_ne hcd
  change (circleTrace cfg c.1 ∩ circleTrace cfg d.1).card < 3 at hinter
  have hunion := Finset.card_union_add_card_inter
    (circleTrace cfg c.1) (circleTrace cfg d.1)
  have hcomp := circleComplement_inter_card_add_union_card cfg c d
  omega

theorem circleComplement_inter_lt_two_of_card_seven_size_four
    {α : Type*} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (hthree : NoThreeCollinear cfg)
    (hα : Fintype.card α = 7)
    {c d : DeterminedCircle cfg}
    (hc : (circleTrace cfg c.1).card = 4)
    (hd : (circleTrace cfg d.1).card = 4) (hcd : c ≠ d) :
    (circleComplement cfg c ∩ circleComplement cfg d).card < 2 := by
  have hinter := (circleOwnership cfg hthree).card_inter_lt_of_ne hcd
  change (circleTrace cfg c.1 ∩ circleTrace cfg d.1).card < 3 at hinter
  have hunion := Finset.card_union_add_card_inter
    (circleTrace cfg c.1) (circleTrace cfg d.1)
  have hcomp := circleComplement_inter_card_add_union_card cfg c d
  omega

theorem c4_le_three_of_card_six
    {α : Type*} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (hthree : NoThreeCollinear cfg)
    (hα : Fintype.card α = 6) :
    circleCensus cfg 4 ≤ 3 := by
  let P := circleComplementsOfSize cfg 4
  have hsub : ∀ p ∈ P, p ⊆ (Finset.univ : Finset α) := by
    intro p hp
    exact Finset.subset_univ p
  have hpair : ∀ p ∈ P, p.card = 2 := by
    intro p hp
    change p ∈ circleComplementsOfSize cfg 4 at hp
    rw [circleComplementsOfSize] at hp
    obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hp
    rw [card_circleComplement, (mem_circlesOfSize.mp hc), hα]
  have hinter : ∀ p ∈ P, ∀ q ∈ P, p ≠ q → (p ∩ q).card < 1 := by
    intro p hp q hq hpq
    change p ∈ circleComplementsOfSize cfg 4 at hp
    change q ∈ circleComplementsOfSize cfg 4 at hq
    rw [circleComplementsOfSize] at hp hq
    obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hq
    apply circleComplement_inter_lt_one_of_card_six_size_four cfg hthree hα
      (mem_circlesOfSize.mp hc) (mem_circlesOfSize.mp hd)
    intro hcd
    apply hpq
    rw [hcd]
  have hpack := card_mul_choose_le_choose_of_pairwise_inter_lt
    (Finset.univ : Finset α) P 2 1 hsub hpair hinter
  rw [show P.card = circleCensus cfg 4 by
    exact card_circleComplementsOfSize cfg hthree 4, Finset.card_univ, hα] at hpack
  norm_num [Nat.choose] at hpack
  omega

theorem c4_le_seven_of_card_seven
    {α : Type*} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (hthree : NoThreeCollinear cfg)
    (hα : Fintype.card α = 7) :
    circleCensus cfg 4 ≤ 7 := by
  let P := circleComplementsOfSize cfg 4
  have hsub : ∀ p ∈ P, p ⊆ (Finset.univ : Finset α) := by
    intro p hp
    exact Finset.subset_univ p
  have htriple : ∀ p ∈ P, p.card = 3 := by
    intro p hp
    change p ∈ circleComplementsOfSize cfg 4 at hp
    rw [circleComplementsOfSize] at hp
    obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hp
    rw [card_circleComplement, (mem_circlesOfSize.mp hc), hα]
  have hinter : ∀ p ∈ P, ∀ q ∈ P, p ≠ q → (p ∩ q).card < 2 := by
    intro p hp q hq hpq
    change p ∈ circleComplementsOfSize cfg 4 at hp
    change q ∈ circleComplementsOfSize cfg 4 at hq
    rw [circleComplementsOfSize] at hp hq
    obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hq
    apply circleComplement_inter_lt_two_of_card_seven_size_four cfg hthree hα
      (mem_circlesOfSize.mp hc) (mem_circlesOfSize.mp hd)
    intro hcd
    apply hpq
    rw [hcd]
  have hpack := card_mul_choose_le_choose_of_pairwise_inter_lt
    (Finset.univ : Finset α) P 3 2 hsub htriple hinter
  rw [show P.card = circleCensus cfg 4 by
    exact card_circleComplementsOfSize cfg hthree 4, Finset.card_univ, hα] at hpack
  norm_num [Nat.choose] at hpack
  omega

/-- If the seven-label packing bound is sharp, the complementary triples
form a Steiner triple system: every pair occurs in exactly one complement. -/
theorem complements_form_STS_of_card_seven_c4_eq_seven
    {α : Type*} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (hthree : NoThreeCollinear cfg)
    (hα : Fintype.card α = 7) (hc4 : circleCensus cfg 4 = 7) :
    ∀ A ∈ (Finset.univ : Finset α).powersetCard 2,
      ∃! p : Finset α,
        p ∈ circleComplementsOfSize cfg 4 ∧ A ⊆ p := by
  let P := circleComplementsOfSize cfg 4
  have hsub : ∀ p ∈ P, p ⊆ (Finset.univ : Finset α) := by
    intro p hp
    exact Finset.subset_univ p
  have htriple : ∀ p ∈ P, p.card = 3 := by
    intro p hp
    change p ∈ circleComplementsOfSize cfg 4 at hp
    rw [circleComplementsOfSize] at hp
    obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hp
    rw [card_circleComplement, (mem_circlesOfSize.mp hc), hα]
  have hinter : ∀ p ∈ P, ∀ q ∈ P, p ≠ q → (p ∩ q).card < 2 := by
    intro p hp q hq hpq
    change p ∈ circleComplementsOfSize cfg 4 at hp
    change q ∈ circleComplementsOfSize cfg 4 at hq
    rw [circleComplementsOfSize] at hp hq
    obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hq
    apply circleComplement_inter_lt_two_of_card_seven_size_four cfg hthree hα
      (mem_circlesOfSize.mp hc) (mem_circlesOfSize.mp hd)
    intro hcd
    apply hpq
    rw [hcd]
  have heq : P.card * Nat.choose 3 2 =
      Nat.choose (Finset.univ : Finset α).card 2 := by
    rw [show P.card = circleCensus cfg 4 by
      exact card_circleComplementsOfSize cfg hthree 4,
      hc4, Finset.card_univ, hα]
    norm_num [Nat.choose]
  intro A hA
  exact existsUnique_block_of_packing_equality
    (Finset.univ : Finset α) P 3 2 hsub htriple hinter heq hA

end Erdos506.V3
