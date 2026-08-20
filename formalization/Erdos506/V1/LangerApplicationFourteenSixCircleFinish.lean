import Erdos506.V1.LangerApplicationFourteenSixCircleFunctional
import Erdos506.Finite.Packing

/-!
# The fourteen-point selected-six-circle endpoint

The relative functional gives `W ≥ 76`.  On the other hand, real-circle
geometry permits at most four active full matching signatures.  Equal
signatures have disjoint outsider edges, so on eight outsiders every
signature fiber has size at most four.  Thus there are at most sixteen
full edges and `W ≤ 2 * choose 8 2 + 16 = 72`, a contradiction.
-/

namespace Erdos506.V1

open Erdos506.Block
open Erdos506.Incidence
open Erdos506.V4
open scoped BigOperators

universe u

variable {alpha : Type u} [Fintype alpha] [DecidableEq alpha]

private noncomputable def fourteenSixSignatureFiber
    (cfg : Configuration alpha) (gamma : DeterminedCircle cfg)
    (X : Finset alpha) (s : Finset (Finset alpha)) :
    Finset (Finset alpha) :=
  (sixConicFullEdges cfg gamma X).filter fun e =>
    sixConicSignature cfg gamma e = s

/-- One full-signature fiber is a matching on the eight outsiders. -/
private theorem fourteenSix_signatureFiber_card_le_four
    (cfg : Configuration alpha) (gamma : DeterminedCircle cfg)
    (hgamma : (circleTrace cfg gamma.1).card = 6)
    (X : Finset alpha) (hX : X.card = 8)
    (hdisjoint : Disjoint (circleTrace cfg gamma.1) X)
    (s : Finset (Finset alpha)) :
    (fourteenSixSignatureFiber cfg gamma X s).card ≤ 4 := by
  classical
  have hpack := Erdos506.Finite.card_mul_choose_le_choose_of_pairwise_inter_lt
    X (fourteenSixSignatureFiber cfg gamma X s) 2 1
  have hsub : ∀ e ∈ fourteenSixSignatureFiber cfg gamma X s, e ⊆ X := by
    intro e he
    exact (Finset.mem_powersetCard.mp
      (mem_sixConicFullEdges.mp (Finset.mem_filter.mp he).1).1).1
  have hcard : ∀ e ∈ fourteenSixSignatureFiber cfg gamma X s,
      e.card = 2 := by
    intro e he
    exact (Finset.mem_powersetCard.mp
      (mem_sixConicFullEdges.mp (Finset.mem_filter.mp he).1).1).2
  have hinter : ∀ e ∈ fourteenSixSignatureFiber cfg gamma X s,
      ∀ f ∈ fourteenSixSignatureFiber cfg gamma X s, e ≠ f →
        (e ∩ f).card < 1 := by
    intro e he f hf hef
    have he' := Finset.mem_filter.mp he
    have hf' := Finset.mem_filter.mp hf
    have hdisj := sixConic_equal_full_signatures_disjoint
      cfg gamma hgamma X hdisjoint he'.1 hf'.1 hef
        (he'.2.trans hf'.2.symm)
    rw [Finset.disjoint_iff_inter_eq_empty] at hdisj
    simp [hdisj]
  have h := hpack hsub hcard hinter
  norm_num [hX, Nat.choose] at h
  omega

/-- Four dihedral signatures, each a four-edge matching, give at most
sixteen full outsider edges. -/
private theorem fourteenSix_fullEdges_card_le_sixteen
    (cfg : Configuration alpha) (gamma : DeterminedCircle cfg)
    (hgamma : (circleTrace cfg gamma.1).card = 6)
    (X : Finset alpha) (hX : X.card = 8)
    (hdisjoint : Disjoint (circleTrace cfg gamma.1) X) :
    (sixConicFullEdges cfg gamma X).card ≤ 16 := by
  classical
  let A := sixConicActiveSignatures cfg gamma X
  let F := sixConicFullEdges cfg gamma X
  let fiber := fourteenSixSignatureFiber cfg gamma X
  have hcover : F = A.biUnion fiber := by
    ext e
    constructor
    · intro he
      have hs : sixConicSignature cfg gamma e ∈ A := by
        exact Finset.mem_image.mpr ⟨e, he, rfl⟩
      exact Finset.mem_biUnion.mpr
        ⟨sixConicSignature cfg gamma e, hs,
          Finset.mem_filter.mpr ⟨he, rfl⟩⟩
    · intro he
      rcases Finset.mem_biUnion.mp he with ⟨s, _hs, hes⟩
      exact (Finset.mem_filter.mp hes).1
  have hcardUnion : F.card ≤ ∑ s ∈ A, (fiber s).card := by
    rw [hcover]
    exact Finset.card_biUnion_le
  have hfiber : ∀ s ∈ A, (fiber s).card ≤ 4 := by
    intro s _hs
    exact fourteenSix_signatureFiber_card_le_four
      cfg gamma hgamma X hX hdisjoint s
  have hsum : (∑ s ∈ A, (fiber s).card) ≤ 4 * A.card := by
    calc
      (∑ s ∈ A, (fiber s).card) ≤ ∑ _s ∈ A, 4 := by
        exact Finset.sum_le_sum fun s hs => hfiber s hs
      _ = 4 * A.card := by simp [Nat.mul_comm]
  have hA : A.card ≤ 4 :=
    sixConic_activeSignatures_card_le_four
      cfg gamma hgamma X hdisjoint
  change F.card ≤ 16
  omega

private theorem fourteenSix_pairWeight_le_two_add_fullIndicator
    (cfg : Configuration alpha) (gamma : DeterminedCircle cfg)
    (hgamma : (circleTrace cfg gamma.1).card = 6)
    (X : Finset alpha)
    (hdisjoint : Disjoint (circleTrace cfg gamma.1) X)
    (e : Finset alpha) (he : e ∈ X.powersetCard 2) :
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

private theorem fourteenSix_sum_fullEdge_indicator
    (cfg : Configuration alpha) (gamma : DeterminedCircle cfg)
    (X : Finset alpha) :
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

/-- The four-signature cap sharpens the eight-outsider weight to `72`. -/
theorem fourteenSix_sixConicWeight_le_seventy_two
    (cfg : Configuration alpha) (gamma : DeterminedCircle cfg)
    (hgamma : (circleTrace cfg gamma.1).card = 6)
    (X : Finset alpha) (hX : X.card = 8)
    (hdisjoint : Disjoint (circleTrace cfg gamma.1) X) :
    sixConicWeight cfg gamma X ≤ 72 := by
  classical
  have hsum := Finset.sum_le_sum fun e he =>
    fourteenSix_pairWeight_le_two_add_fullIndicator
      cfg gamma hgamma X hdisjoint e he
  change sixConicTotalWeight cfg gamma X ≤ _ at hsum
  rw [sixConicTotalWeight_eq_sixConicWeight] at hsum
  have hpairCard : (X.powersetCard 2).card = 28 := by
    rw [Finset.card_powersetCard, hX]
    norm_num [Nat.choose]
  have hindicator := fourteenSix_sum_fullEdge_indicator cfg gamma X
  simp only [Finset.sum_add_distrib, Finset.sum_const,
    nsmul_eq_mul] at hsum
  rw [hpairCard, hindicator] at hsum
  have hF := fourteenSix_fullEdges_card_le_sixteen
    cfg gamma hgamma X hX hdisjoint
  omega

/-- The fourteen-point selected-six-circle residual is impossible. -/
theorem FourteenSixCircleResidualData.impossible
    {cfg : Configuration alpha} {c : DeterminedCircle cfg}
    (R : FourteenSixCircleResidualData cfg c) : False := by
  let X := Finset.univ \ circleTrace cfg c.1
  have hX : X.card = 8 := by
    simpa [X] using R.outside_card
  have hdisjoint : Disjoint (circleTrace cfg c.1) X := by
    simp [X, Finset.disjoint_left]
  have hlower := R.fourteenWeight_ge_seventy_six
  rw [R.fourteenWeight_eq_sixConicWeight] at hlower
  have hlowerX : 76 ≤ sixConicWeight cfg c X := by
    simpa [X] using hlower
  have hupper := fourteenSix_sixConicWeight_le_seventy_two
    cfg c R.selected_card X hX hdisjoint
  omega

/-- Configuration-level endpoint matching the finite-window rich-block
router at `(14,6)`. -/
theorem FiniteWindowRichBlockResidual.circle_impossible_of_fourteen_six
    (Mel : RealPlaneMelchiorPrinciple.{u})
    {cfg : Configuration alpha} (R : FiniteWindowRichBlockResidual cfg)
    (hadm : Admissible cfg)
    (hcircle : (blockSystem cfg).kind R.block = .circle)
    (h14 : Fintype.card alpha = 14)
    (hsix : (geometricBlockSupport cfg R.block).card = 6)
    (hcount : Erdos506.V4.circleCount cfg <
      Erdos506.v1UniformTarget (Fintype.card alpha)) : False := by
  have hcount72 : Erdos506.V4.circleCount cfg ≤ 72 := by
    rw [h14] at hcount
    norm_num [Erdos506.v1UniformTarget, Nat.choose] at hcount
    omega
  cases hblock : R.block with
  | inl L =>
      rw [hblock] at hcircle
      cases hcircle
  | inr c =>
      rw [hblock] at hsix
      exact (fourteenSixCircleResidualData_of_configuration
        Mel cfg hadm h14 hcount72 c hsix).impossible

end Erdos506.V1
