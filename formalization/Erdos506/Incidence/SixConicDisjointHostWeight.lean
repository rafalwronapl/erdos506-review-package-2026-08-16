import Erdos506.Incidence.SixConicSignaturesOnHostCap
import Mathlib.Tactic

/-!
# Five-outsider weight on a disjoint host

The sharp bound `W ≤ 26` for five outsiders carried by one generalized host
is an aggregation consequence of the remaining six-conic interface.  Every
full edge contributes only one above the baseline weight two.  On a fixed
host there are at most three full signatures, and the field-free equal-
signature disjointness theorem makes every signature fiber a matching of
size at most two in a five-set.  Hence there are at most six full edges.
-/

namespace Erdos506.Incidence

open Erdos506.Finite
open Erdos506.V1
open Erdos506.V4
open scoped BigOperators

universe u

private noncomputable def disjointHostFullSignatureFiber
    {α : Type u} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (gamma : DeterminedCircle cfg)
    (X : Finset α) (s : Finset (Finset α)) : Finset (Finset α) :=
  (sixConicFullEdges cfg gamma X).filter fun e =>
    sixConicSignature cfg gamma e = s

private theorem disjointHostFullSignatureFiber_card_le_two
    {α : Type u} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (gamma : DeterminedCircle cfg)
    (hgamma : (circleTrace cfg gamma.1).card = 6)
    (X : Finset α) (hX : X.card = 5)
    (hdisjoint : Disjoint (circleTrace cfg gamma.1) X)
    (s : Finset (Finset α)) :
    (disjointHostFullSignatureFiber cfg gamma X s).card ≤ 2 := by
  classical
  let F := disjointHostFullSignatureFiber cfg gamma X s
  have hhalf : F.card ≤ X.card / 2 := by
    apply card_le_half_of_pairwiseDisjoint_pairs X F
    · intro e he
      exact (Finset.mem_powersetCard.mp
        (mem_sixConicFullEdges.mp (Finset.mem_filter.mp he).1).1).1
    · intro e he
      exact (Finset.mem_powersetCard.mp
        (mem_sixConicFullEdges.mp (Finset.mem_filter.mp he).1).1).2
    · intro e he f hf hef
      have heData := Finset.mem_filter.mp he
      have hfData := Finset.mem_filter.mp hf
      exact sixConic_equal_full_signatures_disjoint
        cfg gamma hgamma X hdisjoint heData.1 hfData.1 hef
          (heData.2.trans hfData.2.symm)
  rw [hX] at hhalf
  norm_num at hhalf ⊢
  exact hhalf

private theorem sixConicFullEdges_card_le_six_of_subset_host
    {α : Type u} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (gamma : DeterminedCircle cfg)
    (hgamma : (circleTrace cfg gamma.1).card = 6)
    (X : Finset α) (hX : X.card = 5)
    (hdisjoint : Disjoint (circleTrace cfg gamma.1) X)
    (H : GeometricBlock cfg)
    (hXH : X ⊆ geometricBlockSupport cfg H) :
    (sixConicFullEdges cfg gamma X).card ≤ 6 := by
  classical
  let A := sixConicSignaturesOnHost cfg gamma X H
  let F := sixConicFullEdges cfg gamma X
  let fiber := disjointHostFullSignatureFiber cfg gamma X
  have hcover : F = A.biUnion fiber := by
    ext e
    constructor
    · intro he
      have heX := (Finset.mem_powersetCard.mp
        (mem_sixConicFullEdges.mp he).1).1
      have heHost : e ⊆ geometricBlockSupport cfg H := heX.trans hXH
      have hs : sixConicSignature cfg gamma e ∈ A := by
        dsimp only [A, sixConicSignaturesOnHost]
        exact Finset.mem_image.mpr
          ⟨e, Finset.mem_filter.mpr ⟨he, heHost⟩, rfl⟩
      exact Finset.mem_biUnion.mpr
        ⟨sixConicSignature cfg gamma e, hs,
          Finset.mem_filter.mpr ⟨he, rfl⟩⟩
    · intro he
      rcases Finset.mem_biUnion.mp he with ⟨s, _hs, hes⟩
      exact (Finset.mem_filter.mp hes).1
  have hcardUnion : F.card ≤ ∑ s ∈ A, (fiber s).card := by
    rw [hcover]
    exact Finset.card_biUnion_le
  have hfiber : ∀ s ∈ A, (fiber s).card ≤ 2 := by
    intro s _hs
    exact disjointHostFullSignatureFiber_card_le_two
      cfg gamma hgamma X hX hdisjoint s
  have hsum : (∑ s ∈ A, (fiber s).card) ≤ 2 * A.card := by
    calc
      (∑ s ∈ A, (fiber s).card) ≤ ∑ _s ∈ A, 2 := by
        exact Finset.sum_le_sum fun s hs => hfiber s hs
      _ = 2 * A.card := by simp [Nat.mul_comm]
  have hA : A.card ≤ 3 :=
    sixConicSignaturesOnHost_card_le_three
      cfg gamma hgamma X hdisjoint H
  change F.card ≤ 6
  omega

private theorem sixConicPairWeight_le_two_add_fullIndicator
    {α : Type u} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (gamma : DeterminedCircle cfg)
    (hgamma : (circleTrace cfg gamma.1).card = 6)
    (X : Finset α)
    (hdisjoint : Disjoint (circleTrace cfg gamma.1) X)
    (e : Finset α) (he : e ∈ X.powersetCard 2) :
    sixConicPairWeight cfg gamma e ≤
      2 + if e ∈ sixConicFullEdges cfg gamma X then 1 else 0 := by
  have heSpec := Finset.mem_powersetCard.mp he
  have heDisjoint : Disjoint e (circleTrace cfg gamma.1) :=
    hdisjoint.symm.mono_left heSpec.1
  have hq := sixConicPairWeight_le_three hgamma heSpec.2 heDisjoint
  by_cases hfull : e ∈ sixConicFullEdges cfg gamma X
  · simp only [hfull, if_true]
    omega
  · have hne : sixConicPairWeight cfg gamma e ≠ 3 := by
      intro hthree
      exact hfull (mem_sixConicFullEdges.mpr ⟨he, hthree⟩)
    simp only [hfull, if_false]
    omega

private theorem sum_sixConicFullEdge_indicator
    {α : Type u} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (gamma : DeterminedCircle cfg)
    (X : Finset α) :
    (∑ e ∈ X.powersetCard 2,
      if e ∈ sixConicFullEdges cfg gamma X then 1 else 0) =
      (sixConicFullEdges cfg gamma X).card := by
  classical
  have hfilter :
      (X.powersetCard 2).filter
          (fun e => e ∈ sixConicFullEdges cfg gamma X) =
        sixConicFullEdges cfg gamma X := by
    ext e
    simp only [Finset.mem_filter]
    constructor
    · exact fun h => h.2
    · intro he
      exact ⟨(mem_sixConicFullEdges.mp he).1, he⟩
  rw [← Finset.sum_filter, hfilter]
  simp

private theorem sixConicWeight_le_twenty_add_fullEdges
    {α : Type u} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (gamma : DeterminedCircle cfg)
    (hgamma : (circleTrace cfg gamma.1).card = 6)
    (X : Finset α) (hX : X.card = 5)
    (hdisjoint : Disjoint (circleTrace cfg gamma.1) X) :
    sixConicWeight cfg gamma X ≤
      20 + (sixConicFullEdges cfg gamma X).card := by
  classical
  have hsum := Finset.sum_le_sum fun e he =>
    sixConicPairWeight_le_two_add_fullIndicator
      cfg gamma hgamma X hdisjoint e he
  change sixConicTotalWeight cfg gamma X ≤ _ at hsum
  rw [sixConicTotalWeight_eq_sixConicWeight] at hsum
  have hpairCard : (X.powersetCard 2).card = 10 := by
    rw [Finset.card_powersetCard, hX]
    norm_num [Nat.choose]
  have hindicator := sum_sixConicFullEdge_indicator cfg gamma X
  simp only [Finset.sum_add_distrib, Finset.sum_const,
    nsmul_eq_mul] at hsum
  rw [hpairCard, hindicator] at hsum
  omega

/-- Five outsiders on a generalized host disjoint from the selected
six-circle have total two-marked-circle weight at most `26`. -/
theorem sixConic_five_outsider_host_disjoint_weight_le
    {α : Type u} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (gamma : DeterminedCircle cfg)
    (hgamma : (circleTrace cfg gamma.1).card = 6)
    (X : Finset α) (hX : X.card = 5)
    (hdisjoint : Disjoint (circleTrace cfg gamma.1) X) :
    HasFiveOutsiderHostDisjoint cfg gamma X →
      sixConicWeight cfg gamma X ≤ 26 := by
  rintro ⟨H, hXH, _hHostGamma⟩
  have hfull := sixConicFullEdges_card_le_six_of_subset_host
    cfg gamma hgamma X hX hdisjoint H hXH
  have hweight := sixConicWeight_le_twenty_add_fullEdges
    cfg gamma hgamma X hX hdisjoint
  omega

end Erdos506.Incidence
