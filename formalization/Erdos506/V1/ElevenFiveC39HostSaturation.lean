import Erdos506.V1.ElevenFiveC39HighHostFinish
import Erdos506.Block.RelativeTwoTwoCapacity
import Mathlib.Tactic

/-!
# Pair-fibre saturation for an eleven--five host

The C39 maximum-host cases use the elementary capacity `H <= 30` one step
more sharply.  This file records the lossless pairwise form of that capacity.
For a selected five-set `D`, the host weight is the sum, over the fifteen
outsider pairs, of the number of two-trace blocks containing that pair.
Every such fibre has size at most two by unique triple ownership.  Therefore
at `H = 30` every fibre is saturated.

Nothing here is a geometric normalisation or a new incidence hypothesis: the
fibres are filters of the actual block family.
-/

namespace Erdos506.V1

open Erdos506.Block
open Erdos506.Block.BlockSystem
open scoped BigOperators

universe u v

variable {Point : Type u} {Block : Type v}
  [Fintype Point] [Fintype Block] [DecidableEq Point]

/-- The actual two-trace host blocks which contain one fixed outside pair.
The outside condition on the pair is imposed in the theorems below; keeping
the fibre itself this literal makes it usable for every selected set. -/
noncomputable def elevenFiveHostPairFibre
    (S : BlockSystem Point Block) (D A : Finset Point) : Finset Block := by
  classical
  exact (elevenFiveHostFamily S D).filter fun b => A ⊆ S.support b

@[simp] theorem mem_elevenFiveHostPairFibre
    (S : BlockSystem Point Block) (D A : Finset Point) {b : Block} :
    b ∈ elevenFiveHostPairFibre S D A ↔
      b ∈ elevenFiveHostFamily S D ∧ A ⊆ S.support b := by
  classical
  simp [elevenFiveHostPairFibre]

/-- Double-counting the outsider pairs inside every actual two-trace host
block writes the host weight as the sum of its pair fibres. -/
theorem elevenFiveHostWeight_eq_sum_hostPairFibre_card
    (S : BlockSystem Point Block) (D : Finset Point) :
    elevenFiveHostWeight S D =
      ∑ A ∈ (Finset.univ \ D).powersetCard 2,
        (elevenFiveHostPairFibre S D A).card := by
  classical
  let Q : Finset (Finset Point) := (Finset.univ \ D).powersetCard 2
  let F : Finset Block := elevenFiveHostFamily S D
  have hflagCard (b : Block) :
      Nat.choose (S.support b \ D).card 2 =
        (Q.filter fun A => A ⊆ S.support b \ D).card := by
    rw [← Finset.card_powersetCard]
    apply congrArg Finset.card
    ext A
    simp only [Q, Finset.mem_filter, Finset.mem_powersetCard]
    constructor
    · intro hA
      refine ⟨⟨?_, hA.2⟩, hA.1⟩
      intro p hp
      exact Finset.mem_sdiff.mpr
        ⟨Finset.mem_univ p, (Finset.mem_sdiff.mp (hA.1 hp)).2⟩
    · rintro ⟨hAQ, hsub⟩
      exact ⟨hsub, hAQ.2⟩
  change (∑ b ∈ F, Nat.choose (S.support b \ D).card 2) =
    ∑ A ∈ Q, (F.filter fun b => A ⊆ S.support b).card
  calc
    (∑ b ∈ F, Nat.choose (S.support b \ D).card 2) =
        ∑ b ∈ F, (Q.filter fun A => A ⊆ S.support b \ D).card := by
      apply Finset.sum_congr rfl
      intro b _hb
      exact hflagCard b
    _ = ∑ b ∈ F, ∑ A ∈ Q,
        if A ⊆ S.support b \ D then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro b _hb
      exact Finset.card_filter _ Q
    _ = ∑ A ∈ Q, ∑ b ∈ F,
        if A ⊆ S.support b \ D then 1 else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ A ∈ Q, (F.filter fun b => A ⊆ S.support b \ D).card := by
      apply Finset.sum_congr rfl
      intro A _hA
      symm
      exact Finset.card_filter _ F
    _ = ∑ A ∈ Q, (F.filter fun b => A ⊆ S.support b).card := by
      apply Finset.sum_congr rfl
      intro A hA
      have hAoutside : A ⊆ Finset.univ \ D :=
        (Finset.mem_powersetCard.mp hA).1
      congr 1
      ext b
      constructor
      · intro hb
        have hb' := Finset.mem_filter.mp hb
        refine Finset.mem_filter.mpr ⟨hb'.1, ?_⟩
        intro x hx
        exact (Finset.mem_sdiff.mp (hb'.2 hx)).1
      · intro hb
        have hb' := Finset.mem_filter.mp hb
        refine Finset.mem_filter.mpr ⟨hb'.1, ?_⟩
        intro x hx
        exact Finset.mem_sdiff.mpr
          ⟨hb'.2 hx, (Finset.mem_sdiff.mp (hAoutside hx)).2⟩

/-- A fixed outsider pair has at most two two-trace host blocks.  This is
the per-pair part of the usual `H <= 30` proof. -/
theorem elevenFiveHostPairFibre_card_le_two
    (S : BlockSystem Point Block) (D : Finset Point) (hD : D.card = 5)
    {A : Finset Point} (hA : A ∈ (Finset.univ \ D).powersetCard 2) :
    (elevenFiveHostPairFibre S D A).card ≤ 2 := by
  classical
  let F : Finset Block := elevenFiveHostFamily S D
  have hAspec := Finset.mem_powersetCard.mp hA
  have hAoutside : A ⊆ Finset.univ \ D := hAspec.1
  have hAcard : A.card = 2 := hAspec.2
  have hDA : Disjoint D A := by
    rw [Finset.disjoint_left]
    intro x hxD hxA
    exact (Finset.mem_sdiff.mp (hAoutside hxA)).2 hxD
  have htwo (b : Block) (hb : b ∈ F) :
      (S.support b ∩ D).card = 2 := by
    exact (Finset.mem_filter.mp hb).2
  have hpoint (b : Block) :
      Nat.choose (S.support b ∩ A).card 2 =
        if A ⊆ S.support b then 1 else 0 := by
    by_cases hsub : A ⊆ S.support b
    · have hinter : S.support b ∩ A = A := by
        apply Finset.Subset.antisymm Finset.inter_subset_right
        intro x hx
        exact Finset.mem_inter.mpr ⟨hsub hx, hx⟩
      simp [hsub, hinter, hAcard]
    · have hinter_lt : (S.support b ∩ A).card < 2 := by
        have hinter_le : (S.support b ∩ A).card ≤ A.card :=
          Finset.card_le_card Finset.inter_subset_right
        by_contra hnot
        have hinter_ge : 2 ≤ (S.support b ∩ A).card := by omega
        have hinter_eq : S.support b ∩ A = A := by
          apply Finset.eq_of_subset_of_card_le Finset.inter_subset_right
          omega
        apply hsub
        intro x hx
        have hxinter : x ∈ S.support b ∩ A := by
          rw [hinter_eq]
          exact hx
        exact (Finset.mem_inter.mp hxinter).1
      rw [Nat.choose_eq_zero_of_lt hinter_lt]
      simp [hsub]
  have hsum :
      (∑ b ∈ F, Nat.choose (S.support b ∩ A).card 2) =
        (F.filter fun b => A ⊆ S.support b).card := by
    calc
      (∑ b ∈ F, Nat.choose (S.support b ∩ A).card 2) =
          ∑ b ∈ F, if A ⊆ S.support b then 1 else 0 := by
        apply Finset.sum_congr rfl
        intro b _hb
        exact hpoint b
      _ = (F.filter fun b => A ⊆ S.support b).card := by
        symm
        exact Finset.card_filter _ F
  have hcapacity :=
    Erdos506.Block.BlockSystem.relative_two_two_capacity_between
      S D A F hDA htwo
  rw [hsum, hD, hAcard] at hcapacity
  norm_num at hcapacity
  change (F.filter fun b => A ⊆ S.support b).card ≤ 2
  exact hcapacity

/-- At the extremal host weight thirty all fifteen outsider-pair fibres are
full.  This is the finite ``all double'' input for the H=30 K2.1 branch. -/
theorem elevenFiveHostPairFibre_card_eq_two_of_hostWeight_eq_thirty
    (S : BlockSystem Point Block) (D : Finset Point)
    (hpoint : Fintype.card Point = 11) (hD : D.card = 5)
    (hhost : elevenFiveHostWeight S D = 30)
    {A : Finset Point} (hA : A ∈ (Finset.univ \ D).powersetCard 2) :
    (elevenFiveHostPairFibre S D A).card = 2 := by
  classical
  let Q : Finset (Finset Point) := (Finset.univ \ D).powersetCard 2
  let f : Finset Point → ℕ := fun A =>
    (elevenFiveHostPairFibre S D A).card
  have hsum : (∑ A ∈ Q, f A) = 30 := by
    change (∑ A ∈ (Finset.univ \ D).powersetCard 2,
      (elevenFiveHostPairFibre S D A).card) = 30
    rw [← elevenFiveHostWeight_eq_sum_hostPairFibre_card S D]
    exact hhost
  have hupper (B : Finset Point) (hB : B ∈ Q) : f B ≤ 2 := by
    change (elevenFiveHostPairFibre S D B).card ≤ 2
    exact elevenFiveHostPairFibre_card_le_two S D hD hB
  have hAq : A ∈ Q := hA
  have hQcard : Q.card = 15 := by
    simp [Q, Finset.card_sdiff_of_subset (Finset.subset_univ D), hpoint,
      hD, Nat.choose]
  have heraseCard : (Q.erase A).card = 14 := by
    rw [Finset.card_erase_of_mem hAq, hQcard]
  have hrest : (∑ B ∈ Q.erase A, f B) ≤ 2 * (Q.erase A).card := by
    calc
      (∑ B ∈ Q.erase A, f B) ≤ ∑ _B ∈ Q.erase A, 2 := by
        apply Finset.sum_le_sum
        intro B hB
        exact hupper B (Finset.mem_erase.mp hB).2
      _ = 2 * (Q.erase A).card := by simp [Nat.mul_comm]
  have hdecomp :
      (∑ B ∈ Q.erase A, f B) + f A = ∑ B ∈ Q, f B := by
    exact Finset.sum_erase_add Q f hAq
  have hlower : 2 ≤ f A := by
    by_contra hnot
    have hsmall : f A ≤ 1 := by omega
    rw [← hdecomp] at hsum
    omega
  exact Nat.le_antisymm (hupper A hAq) hlower

/-- The next extremal face has one and only one missing host slot.  Thus at
host weight twenty-nine there is a unique outside pair with one host; every
other outside pair is double-hosted.  This is the exact finite input for the
H=29 page-colour branch. -/
theorem elevenFiveHostPairFibre_defect_profile_of_hostWeight_eq_twenty_nine
    (S : BlockSystem Point Block) (D : Finset Point)
    (hpoint : Fintype.card Point = 11) (hD : D.card = 5)
    (hhost : elevenFiveHostWeight S D = 29) :
    ∃ A ∈ (Finset.univ \ D).powersetCard 2,
      (elevenFiveHostPairFibre S D A).card = 1 ∧
        ∀ B ∈ (Finset.univ \ D).powersetCard 2, B ≠ A →
          (elevenFiveHostPairFibre S D B).card = 2 := by
  classical
  let Q : Finset (Finset Point) := (Finset.univ \ D).powersetCard 2
  let f : Finset Point → ℕ := fun A =>
    (elevenFiveHostPairFibre S D A).card
  have hsum : (∑ A ∈ Q, f A) = 29 := by
    change (∑ A ∈ (Finset.univ \ D).powersetCard 2,
      (elevenFiveHostPairFibre S D A).card) = 29
    rw [← elevenFiveHostWeight_eq_sum_hostPairFibre_card S D]
    exact hhost
  have hupper (B : Finset Point) (hB : B ∈ Q) : f B ≤ 2 := by
    change (elevenFiveHostPairFibre S D B).card ≤ 2
    exact elevenFiveHostPairFibre_card_le_two S D hD hB
  have hQcard : Q.card = 15 := by
    simp [Q, Finset.card_sdiff_of_subset (Finset.subset_univ D), hpoint,
      hD, Nat.choose]
  have hexception : ∃ A ∈ Q, f A < 2 := by
    by_contra hnone
    push_neg at hnone
    have hsumLower : (∑ _A ∈ Q, 2) ≤ ∑ A ∈ Q, f A := by
      apply Finset.sum_le_sum
      intro A hA
      exact hnone A hA
    have hsumTwo : (∑ _A ∈ Q, 2) = 30 := by simp [hQcard]
    omega
  obtain ⟨A, hAq, hAless⟩ := hexception
  have heraseCard : (Q.erase A).card = 14 := by
    rw [Finset.card_erase_of_mem hAq, hQcard]
  have hrest : (∑ B ∈ Q.erase A, f B) ≤ 2 * (Q.erase A).card := by
    calc
      (∑ B ∈ Q.erase A, f B) ≤ ∑ _B ∈ Q.erase A, 2 := by
        apply Finset.sum_le_sum
        intro B hB
        exact hupper B (Finset.mem_erase.mp hB).2
      _ = 2 * (Q.erase A).card := by simp [Nat.mul_comm]
  have hdecomp :
      (∑ B ∈ Q.erase A, f B) + f A = ∑ B ∈ Q, f B := by
    exact Finset.sum_erase_add Q f hAq
  have hApositive : 1 ≤ f A := by
    by_contra hnot
    have hAzero : f A = 0 := by omega
    have htotal := hsum
    rw [← hdecomp] at htotal
    omega
  have hAone : f A = 1 := by omega
  refine ⟨A, hAq, hAone, ?_⟩
  intro B hB hBA
  have hBupper := hupper B hB
  apply Nat.le_antisymm hBupper
  by_contra hnot
  have hBsmall : f B ≤ 1 := by omega
  have hBmem : B ∈ Q.erase A :=
    Finset.mem_erase.mpr ⟨hBA, hB⟩
  have heraseEraseCard : ((Q.erase A).erase B).card = 13 := by
    rw [Finset.card_erase_of_mem hBmem, heraseCard]
  have hrestrest :
      (∑ C ∈ (Q.erase A).erase B, f C) ≤
        2 * ((Q.erase A).erase B).card := by
    calc
      (∑ C ∈ (Q.erase A).erase B, f C) ≤
          ∑ _C ∈ (Q.erase A).erase B, 2 := by
        apply Finset.sum_le_sum
        intro C hC
        exact hupper C (Finset.mem_erase.mp
          (Finset.mem_erase.mp hC).2).2
      _ = 2 * ((Q.erase A).erase B).card := by simp [Nat.mul_comm]
  have hsplitB :
      (∑ C ∈ (Q.erase A).erase B, f C) + f B =
        ∑ C ∈ Q.erase A, f C := by
    exact Finset.sum_erase_add (Q.erase A) f hBmem
  have htotal := hsum
  rw [← hdecomp, ← hsplitB] at htotal
  omega

/-- At host weight twenty-eight the fifteen outsider-pair fibres have total
defect two.  Consequently either one fibre is empty and all the others are
double, or exactly two fibres are single and all the others are double.

This is the lossless finite entrance for the `H = 28` page analysis; in
particular it performs no case split on the six outsider labels. -/
theorem elevenFiveHostPairFibre_defect_profile_of_hostWeight_eq_twenty_eight
    (S : BlockSystem Point Block) (D : Finset Point)
    (hpoint : Fintype.card Point = 11) (hD : D.card = 5)
    (hhost : elevenFiveHostWeight S D = 28) :
    (∃ A ∈ (Finset.univ \ D).powersetCard 2,
        (elevenFiveHostPairFibre S D A).card = 0 ∧
          ∀ B ∈ (Finset.univ \ D).powersetCard 2, B ≠ A →
            (elevenFiveHostPairFibre S D B).card = 2) ∨
      (∃ A ∈ (Finset.univ \ D).powersetCard 2,
        ∃ B ∈ (Finset.univ \ D).powersetCard 2, A ≠ B ∧
          (elevenFiveHostPairFibre S D A).card = 1 ∧
          (elevenFiveHostPairFibre S D B).card = 1 ∧
          ∀ C ∈ (Finset.univ \ D).powersetCard 2,
            C ≠ A → C ≠ B →
              (elevenFiveHostPairFibre S D C).card = 2) := by
  classical
  let Q : Finset (Finset Point) := (Finset.univ \ D).powersetCard 2
  let f : Finset Point → Nat := fun A =>
    (elevenFiveHostPairFibre S D A).card
  have hsum : (∑ A ∈ Q, f A) = 28 := by
    change (∑ A ∈ (Finset.univ \ D).powersetCard 2,
      (elevenFiveHostPairFibre S D A).card) = 28
    rw [← elevenFiveHostWeight_eq_sum_hostPairFibre_card S D]
    exact hhost
  have hupper (A : Finset Point) (hA : A ∈ Q) : f A ≤ 2 := by
    exact elevenFiveHostPairFibre_card_le_two S D hD hA
  have hQcard : Q.card = 15 := by
    simp [Q, Finset.card_sdiff_of_subset (Finset.subset_univ D), hpoint,
      hD, Nat.choose]
  by_cases hzero : ∃ A ∈ Q, f A = 0
  · left
    obtain ⟨A, hAQ, hAzero⟩ := hzero
    refine ⟨A, hAQ, hAzero, ?_⟩
    intro B hBQ hBA
    have hAerase : (Q.erase A).card = 14 := by
      rw [Finset.card_erase_of_mem hAQ, hQcard]
    have hsplit : (∑ C ∈ Q.erase A, f C) + f A = ∑ C ∈ Q, f C :=
      Finset.sum_erase_add Q f hAQ
    have hrest : (∑ C ∈ Q.erase A, f C) = 28 := by
      rw [hAzero, hsum] at hsplit
      omega
    have htermLe (C : Finset Point) (hC : C ∈ Q.erase A) : f C ≤ 2 :=
      hupper C (Finset.mem_of_mem_erase hC)
    have hconst : (∑ _C ∈ Q.erase A, 2) = 28 := by
      simp [hAerase]
    have hall := (Finset.sum_eq_sum_iff_of_le htermLe).mp
      (hrest.trans hconst.symm)
    exact hall B (Finset.mem_erase.mpr ⟨hBA, hBQ⟩)
  · right
    have hpositive (A : Finset Point) (hA : A ∈ Q) : 1 ≤ f A := by
      have hne : f A ≠ 0 := by
        intro hA0
        exact hzero ⟨A, hA, hA0⟩
      omega
    have hsmall : ∃ A ∈ Q, f A < 2 := by
      by_contra hnone
      push_neg at hnone
      have hlower : (∑ _A ∈ Q, 2) ≤ ∑ A ∈ Q, f A := by
        apply Finset.sum_le_sum
        intro A hA
        exact hnone A hA
      have hconst : (∑ _A ∈ Q, 2) = 30 := by simp [hQcard]
      omega
    obtain ⟨A, hAQ, hAsmall⟩ := hsmall
    have hAone : f A = 1 := by
      have := hpositive A hAQ
      omega
    have hAerase : (Q.erase A).card = 14 := by
      rw [Finset.card_erase_of_mem hAQ, hQcard]
    have hsplitA : (∑ C ∈ Q.erase A, f C) + f A = ∑ C ∈ Q, f C :=
      Finset.sum_erase_add Q f hAQ
    have hsecond : ∃ B ∈ Q.erase A, f B < 2 := by
      by_contra hnone
      push_neg at hnone
      have hlower : (∑ _B ∈ Q.erase A, 2) ≤
          ∑ B ∈ Q.erase A, f B := by
        apply Finset.sum_le_sum
        intro B hB
        exact hnone B hB
      have hconst : (∑ _B ∈ Q.erase A, 2) = 28 := by
        simp [hAerase]
      omega
    obtain ⟨B, hBerase, hBsmall⟩ := hsecond
    have hBQ : B ∈ Q := Finset.mem_of_mem_erase hBerase
    have hBA : B ≠ A := (Finset.mem_erase.mp hBerase).1
    have hBone : f B = 1 := by
      have := hpositive B hBQ
      omega
    refine ⟨A, hAQ, B, hBQ, hBA.symm, hAone, hBone, ?_⟩
    intro C hCQ hCA hCB
    have hBmem : B ∈ Q.erase A :=
      Finset.mem_erase.mpr ⟨hBA, hBQ⟩
    have hrestCard : ((Q.erase A).erase B).card = 13 := by
      rw [Finset.card_erase_of_mem hBmem, hAerase]
    have hsplitB :
        (∑ E ∈ (Q.erase A).erase B, f E) + f B =
          ∑ E ∈ Q.erase A, f E :=
      Finset.sum_erase_add (Q.erase A) f hBmem
    have hrest : (∑ E ∈ (Q.erase A).erase B, f E) = 26 := by
      omega
    have htermLe (E : Finset Point)
        (hE : E ∈ (Q.erase A).erase B) : f E ≤ 2 :=
      hupper E (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hE))
    have hconst : (∑ _E ∈ (Q.erase A).erase B, 2) = 26 := by
      simp [hrestCard]
    have hall := (Finset.sum_eq_sum_iff_of_le htermLe).mp
      (hrest.trans hconst.symm)
    exact hall C (Finset.mem_erase.mpr
      ⟨hCB, Finset.mem_erase.mpr ⟨hCA, hCQ⟩⟩)

end Erdos506.V1
