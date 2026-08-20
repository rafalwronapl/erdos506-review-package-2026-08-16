import Erdos506.Finite.FanoDesign
import Erdos506.V3.FanoPattern
import Erdos506.V3.SmallPacking

/-!
# The strict seven-point Fano wall

Equality in the elementary packing bound would make the complements of the
seven four-point circles into an abstract Steiner triple system.  The finite
classification relabels that system as the canonical Fano plane, while
`FanoPattern.lean` proves that its complementary circle pattern cannot occur
over the real Euclidean plane.
-/

namespace Erdos506.V3

open Erdos506.Finite
open Erdos506.V4

abbrev FourCircleBlock
    {α : Type*} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) :=
  {c : DeterminedCircle cfg // c ∈ circlesOfSize cfg 4}

noncomputable instance instDecidableEqFourCircleBlock
    {α : Type*} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) : DecidableEq (FourCircleBlock cfg) :=
  Classical.decEq _

noncomputable def sevenSteinerDesignOfConfiguration
    {α : Type*} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (hthree : NoThreeCollinear cfg)
    (hα : Fintype.card α = 7) (hc4 : circleCensus cfg 4 = 7) :
    SevenSteinerDesign α (FourCircleBlock cfg) := by
  classical
  exact {
    line := fun b => circleComplement cfg b.1
    point_card := hα
    block_card := by
      let e : FourCircleBlock cfg ≃ ↥(circlesOfSize cfg 4) := {
        toFun b := ⟨b.1, b.2⟩
        invFun b := ⟨b.1, b.2⟩
        left_inv _ := rfl
        right_inv _ := rfl }
      rw [Fintype.card_congr e, Fintype.card_coe]
      simpa [card_circlesOfSize] using hc4
    line_card := by
      intro b
      rw [card_circleComplement, mem_circlesOfSize.mp b.2, hα]
    pair_unique := by
      intro A hA
      obtain ⟨p, ⟨hpP, hAp⟩, huniq⟩ :=
        complements_form_STS_of_card_seven_c4_eq_seven cfg hthree hα hc4 A hA
      rw [circleComplementsOfSize] at hpP
      obtain ⟨c, hc, hcp⟩ := Finset.mem_image.mp hpP
      let b : FourCircleBlock cfg := ⟨c, hc⟩
      refine ⟨b, ?_, ?_⟩
      · change A ⊆ circleComplement cfg c
        rw [hcp]
        exact hAp
      · intro y hy
        apply Subtype.ext
        apply circleComplement_injective cfg hthree
        have hyP : circleComplement cfg y.1 ∈ circleComplementsOfSize cfg 4 := by
          rw [circleComplementsOfSize]
          exact Finset.mem_image.mpr ⟨y.1, y.2, rfl⟩
        have hyp : circleComplement cfg y.1 = p := huniq _ ⟨hyP, hy⟩
        exact hyp.trans hcp.symm }

theorem mem_fanoCircleSupport_iff_not_mem_fanoCanonicalLine
    (i j : Fin 7) :
    i ∈ fanoCircleSupport j ↔ i ∉ fanoCanonicalLine j := by
  fin_cases i <;> fin_cases j <;> decide_cbv

theorem circleCensus_four_ne_seven_of_card_seven
    {α : Type*} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (hthree : NoThreeCollinear cfg)
    (hα : Fintype.card α = 7) : circleCensus cfg 4 ≠ 7 := by
  intro hc4
  let D := sevenSteinerDesignOfConfiguration cfg hthree hα hc4
  obtain ⟨P, B, hcanonical⟩ := D.exists_canonical_labeling
  let p : Fin 7 → Point2 := fun i => cfg (P i)
  let Γ : Fin 7 → ProperCircle := fun j => (B j).1.1
  have hp : Function.Injective p := by
    exact cfg.injective.comp P.injective
  have hinc : ∀ i j, p i ∈ ((Γ j).1 : Set Point2) ↔
      i ∈ fanoCircleSupport j := by
    intro i j
    have hcomp : P i ∈ circleComplement cfg (B j).1 ↔
        i ∈ fanoCanonicalLine j := by
      have h := D.mem_relabeledLines P B i j
      rw [hcanonical j] at h
      change i ∈ fanoCanonicalLine j ↔
        P i ∈ circleComplement cfg (B j).1 at h
      exact h.symm
    calc
      p i ∈ ((Γ j).1 : Set Point2) ↔
          P i ∈ circleTrace cfg (B j).1.1 := by simp [p, Γ]
      _ ↔ P i ∉ circleComplement cfg (B j).1 := by
        simp [circleComplement]
      _ ↔ i ∉ fanoCanonicalLine j := not_congr hcomp
      _ ↔ i ∈ fanoCircleSupport j :=
        (mem_fanoCircleSupport_iff_not_mem_fanoCanonicalLine i j).symm
  exact canonical_fano_circle_pattern_not_realizable p hp Γ hinc

theorem c4_le_six_of_card_seven
    {α : Type*} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (hthree : NoThreeCollinear cfg)
    (hα : Fintype.card α = 7) : circleCensus cfg 4 ≤ 6 := by
  have hle := c4_le_seven_of_card_seven cfg hthree hα
  have hne := circleCensus_four_ne_seven_of_card_seven cfg hthree hα
  omega

end Erdos506.V3
