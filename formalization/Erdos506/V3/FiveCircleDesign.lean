import Erdos506.Finite.SixFiveDesign
import Erdos506.V3.FiveCircle

/-!
# The incidence design forced by six five-point circles

This packages the equality information from `FiveCircle.lean` as the finite
six-by-five design used by the classification and inversion obstruction.
-/

namespace Erdos506.V3

open Erdos506.Finite
open Erdos506.V4

abbrev FiveCircleBlock
    {α : Type*} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) :=
  {c : DeterminedCircle cfg // c ∈ circlesOfSize cfg 5}

noncomputable instance instDecidableEqFiveCircleBlock
    {α : Type*} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) : DecidableEq (FiveCircleBlock cfg) :=
  Classical.decEq _

noncomputable def fiveCircleBlockSupport
    {α : Type*} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (b : FiveCircleBlock cfg) : Finset α :=
  circleTrace cfg b.1.1

theorem card_incident_fiveCircleBlocks_eq_degree
    {α : Type*} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (x : α) :
    ((Finset.univ : Finset (FiveCircleBlock cfg)).filter
      fun b => x ∈ fiveCircleBlockSupport cfg b).card =
      fiveCircleDegree cfg x := by
  classical
  simp [FiveCircleBlock, fiveCircleBlockSupport, fiveCircleDegree,
    incidenceDegree, incidenceIndicator]
  rw [Finset.filter_attach']
  simp only [Finset.card_map, Finset.card_attach]
  congr 1
  ext c
  simp [mem_circlesOfSize]

noncomputable def sixFiveDesignOfConfiguration
    {α : Type*} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (hthree : NoThreeCollinear cfg)
    (hα : Fintype.card α = 10) (hc5 : circleCensus cfg 5 = 6) :
    SixFiveDesign α (FiveCircleBlock cfg) := by
  classical
  exact {
    support := fiveCircleBlockSupport cfg
    point_card := hα
    block_card := by
      let e : FiveCircleBlock cfg ≃ ↥(circlesOfSize cfg 5) := {
        toFun b := ⟨b.1, b.2⟩
        invFun b := ⟨b.1, b.2⟩
        left_inv _ := rfl
        right_inv _ := rfl }
      rw [Fintype.card_congr e, Fintype.card_coe]
      simpa [card_circlesOfSize] using hc5
    support_card := by
      intro b
      exact mem_circlesOfSize.mp b.2
    profile_card := by
      intro x
      rw [card_incident_fiveCircleBlocks_eq_degree]
      exact (c5_eq_six_forces_design cfg hthree hα hc5).2 x
    pair_inter_card := by
      intro b c hbc
      exact (c5_eq_six_forces_design cfg hthree hα hc5).1
        b.1 b.2 c.1 c.2 (by
          intro h
          apply hbc
          exact Subtype.ext h) }

theorem fiveCircleProfile_injective
    {α : Type*} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (hthree : NoThreeCollinear cfg)
    (hα : Fintype.card α = 10) (hc5 : circleCensus cfg 5 = 6) :
    Function.Injective (sixFiveDesignOfConfiguration cfg hthree hα hc5).profile :=
  (sixFiveDesignOfConfiguration cfg hthree hα hc5).profile_injective

end Erdos506.V3
