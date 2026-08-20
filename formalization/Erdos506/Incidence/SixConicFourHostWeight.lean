import Erdos506.Incidence.SixConicEventCapacity
import Erdos506.Incidence.SixConicActiveSignatureGeometry
import Erdos506.Incidence.SixConicU17
import Mathlib.Tactic

/-!
# Five-outsider weight with a four-outsider host

If a five-set has a generalized host carrying four outsiders, every
repetition event is hosted there: its four endpoints and the four hosted
outsiders are two four-subsets of the same five-set, hence overlap in at
least three points, and triple ownership identifies their hosts.  The proved
event-capacity theorem then gives at most two repetition events.

There are at most four active signatures.  Equal-signature full edges form
matchings, so a signature fiber in a five-set has size one or two.  Therefore
the number of full edges is at most the number of active signatures plus the
number of repetition events, hence at most six.  Summing the pointwise bound
`q_e ≤ 2 + 1_{e full}` gives `W ≤ 20 + 6 = 26`.
-/

namespace Erdos506.Incidence

open Erdos506.Block
open Erdos506.Block.BlockSystem
open Erdos506.Finite
open Erdos506.V1
open Erdos506.V4
open scoped BigOperators

universe u

/-! ## Elementary repetition-event data -/

private theorem fourHostRepetitionEvent_card_two
    {α : Type u} [Fintype α] [DecidableEq α]
    {cfg : Configuration α} {gamma : DeterminedCircle cfg}
    {X : Finset α} {E : Finset (Finset α)}
    (hE : E ∈ sixConicRepetitionEvents cfg gamma X) : E.card = 2 := by
  exact (Finset.mem_powersetCard.mp
    (mem_sixConicRepetitionEvents.mp hE).1).2

private theorem fourHostRepetitionEvent_edge_full
    {α : Type u} [Fintype α] [DecidableEq α]
    {cfg : Configuration α} {gamma : DeterminedCircle cfg}
    {X : Finset α} {E : Finset (Finset α)} {e : Finset α}
    (hE : E ∈ sixConicRepetitionEvents cfg gamma X) (he : e ∈ E) :
    e ∈ sixConicFullEdges cfg gamma X := by
  exact (Finset.mem_powersetCard.mp
    (mem_sixConicRepetitionEvents.mp hE).1).1 he

private theorem fourHostRepetitionEvent_edge_card_two
    {α : Type u} [Fintype α] [DecidableEq α]
    {cfg : Configuration α} {gamma : DeterminedCircle cfg}
    {X : Finset α} {E : Finset (Finset α)} {e : Finset α}
    (hE : E ∈ sixConicRepetitionEvents cfg gamma X) (he : e ∈ E) :
    e.card = 2 := by
  exact (Finset.mem_powersetCard.mp
    (mem_sixConicFullEdges.mp
      (fourHostRepetitionEvent_edge_full hE he)).1).2

private theorem fourHostRepetitionEvent_edge_subset_X
    {α : Type u} [Fintype α] [DecidableEq α]
    {cfg : Configuration α} {gamma : DeterminedCircle cfg}
    {X : Finset α} {E : Finset (Finset α)} {e : Finset α}
    (hE : E ∈ sixConicRepetitionEvents cfg gamma X) (he : e ∈ E) :
    e ⊆ X := by
  exact (Finset.mem_powersetCard.mp
    (mem_sixConicFullEdges.mp
      (fourHostRepetitionEvent_edge_full hE he)).1).1

private theorem fourHostRepetitionEvent_union_subset_X
    {α : Type u} [Fintype α] [DecidableEq α]
    {cfg : Configuration α} {gamma : DeterminedCircle cfg}
    {X : Finset α} {E : Finset (Finset α)}
    (hE : E ∈ sixConicRepetitionEvents cfg gamma X) :
    E.biUnion id ⊆ X := by
  intro x hx
  rcases Finset.mem_biUnion.mp hx with ⟨e, he, hxe⟩
  exact fourHostRepetitionEvent_edge_subset_X hE he hxe

private theorem fourHostRepetitionEvent_union_card_four
    {α : Type u} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (gamma : DeterminedCircle cfg)
    (hgamma : (circleTrace cfg gamma.1).card = 6)
    (X : Finset α) (hdisjoint : Disjoint (circleTrace cfg gamma.1) X)
    {E : Finset (Finset α)}
    (hE : E ∈ sixConicRepetitionEvents cfg gamma X) :
    (E.biUnion id).card = 4 := by
  classical
  have hspec := mem_sixConicRepetitionEvents.mp hE
  have hEsub := (Finset.mem_powersetCard.mp hspec.1).1
  have hpairwise : (E : Set (Finset α)).PairwiseDisjoint id := by
    intro e he f hf hef
    exact sixConic_equal_full_signatures_disjoint
      cfg gamma hgamma X hdisjoint (hEsub he) (hEsub hf) hef
        (hspec.2 e he f hf)
  rw [Finset.card_biUnion hpairwise]
  calc
    (∑ e ∈ E, (id e).card) = ∑ _e ∈ E, 2 := by
      apply Finset.sum_congr rfl
      intro e he
      simpa using fourHostRepetitionEvent_edge_card_two hE he
    _ = 4 := by simp [fourHostRepetitionEvent_card_two hE]

/-! ## Every event lies on the four-outsider host -/

private theorem fourHost_repetition_event_hosted
    {α : Type u} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (gamma : DeterminedCircle cfg)
    (hgamma : (circleTrace cfg gamma.1).card = 6)
    (X : Finset α) (hX : X.card = 5)
    (hdisjoint : Disjoint (circleTrace cfg gamma.1) X)
    (H : GeometricBlock cfg)
    (hHcard : (geometricBlockSupport cfg H ∩ X).card = 4)
    {E : Finset (Finset α)}
    (hE : E ∈ sixConicRepetitionEvents cfg gamma X) :
    SixConicEventHostedBy cfg E H := by
  classical
  obtain ⟨K, hK⟩ := sixConic_repetition_host_exists
    cfg gamma hgamma X hdisjoint E hE
  let Y := geometricBlockSupport cfg H ∩ X
  let U := E.biUnion id
  have hYcard : Y.card = 4 := hHcard
  have hUcard : U.card = 4 :=
    fourHostRepetitionEvent_union_card_four
      cfg gamma hgamma X hdisjoint hE
  have hYsubX : Y ⊆ X := Finset.inter_subset_right
  have hUsubX : U ⊆ X := fourHostRepetitionEvent_union_subset_X hE
  have hunionSubX : Y ∪ U ⊆ X := Finset.union_subset hYsubX hUsubX
  have hunionCardLe : (Y ∪ U).card ≤ 5 := by
    have := Finset.card_le_card hunionSubX
    omega
  have hcardIdentity := Finset.card_union_add_card_inter Y U
  have hinterThree : 3 ≤ (Y ∩ U).card := by omega
  have hinterSub : Y ∩ U ⊆
      geometricBlockSupport cfg H ∩ geometricBlockSupport cfg K := by
    intro x hx
    have hxData := Finset.mem_inter.mp hx
    exact Finset.mem_inter.mpr
      ⟨(Finset.mem_inter.mp hxData.1).1, hK hxData.2⟩
  have hHK : H = K := by
    by_contra hne
    have hinter :=
      (geometricBlockSystem cfg).distinct_block_inter_card_lt_three hne
    change (geometricBlockSupport cfg H ∩
      geometricBlockSupport cfg K).card < 3 at hinter
    have hle := Finset.card_le_card hinterSub
    omega
  simpa [hHK] using hK

private theorem fourHost_repetitionEvents_eq_hostedBy
    {α : Type u} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (gamma : DeterminedCircle cfg)
    (hgamma : (circleTrace cfg gamma.1).card = 6)
    (X : Finset α) (hX : X.card = 5)
    (hdisjoint : Disjoint (circleTrace cfg gamma.1) X)
    (H : GeometricBlock cfg)
    (hHcard : (geometricBlockSupport cfg H ∩ X).card = 4) :
    sixConicRepetitionEvents cfg gamma X =
      sixConicEventsHostedBy cfg gamma X H := by
  classical
  apply Finset.Subset.antisymm
  · intro E hE
    exact Finset.mem_filter.mpr
      ⟨hE, fourHost_repetition_event_hosted
        cfg gamma hgamma X hX hdisjoint H hHcard hE⟩
  · intro E hE
    exact (Finset.mem_filter.mp hE).1

private theorem fourHost_repetitionEvents_card_le_two
    {α : Type u} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (gamma : DeterminedCircle cfg)
    (hgamma : (circleTrace cfg gamma.1).card = 6)
    (X : Finset α) (hX : X.card = 5)
    (hdisjoint : Disjoint (circleTrace cfg gamma.1) X)
    (H : GeometricBlock cfg)
    (hHcard : (geometricBlockSupport cfg H ∩ X).card = 4) :
    (sixConicRepetitionEvents cfg gamma X).card ≤ 2 := by
  have hcover := fourHost_repetitionEvents_eq_hostedBy
    cfg gamma hgamma X hX hdisjoint H hHcard
  have hcap := sixConicEventsHostedBy_card_le_hostEventCapacity
    cfg gamma hgamma X hdisjoint H
  have hcount : sixConicHostOutsiderCount cfg X H = 4 := hHcard
  rw [hcover]
  rw [hcount] at hcap
  norm_num [sixConicHostEventCapacity, Nat.choose] at hcap
  exact hcap

/-! ## Signature fibers and repetition counting -/

private noncomputable def fourHostFullSignatureFiber
    {α : Type u} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (gamma : DeterminedCircle cfg)
    (X : Finset α) (s : Finset (Finset α)) : Finset (Finset α) :=
  (sixConicFullEdges cfg gamma X).filter fun e =>
    sixConicSignature cfg gamma e = s

private theorem fourHostFullSignatureFiber_card_le_two
    {α : Type u} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (gamma : DeterminedCircle cfg)
    (hgamma : (circleTrace cfg gamma.1).card = 6)
    (X : Finset α) (hX : X.card = 5)
    (hdisjoint : Disjoint (circleTrace cfg gamma.1) X)
    (s : Finset (Finset α)) :
    (fourHostFullSignatureFiber cfg gamma X s).card ≤ 2 := by
  classical
  let F := fourHostFullSignatureFiber cfg gamma X s
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

private theorem fourHost_repetitionEvents_card_eq_sum_choose_fibers
    {α : Type u} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (gamma : DeterminedCircle cfg)
    (X : Finset α) :
    (sixConicRepetitionEvents cfg gamma X).card =
      ∑ s ∈ sixConicActiveSignatures cfg gamma X,
        Nat.choose (fourHostFullSignatureFiber cfg gamma X s).card 2 := by
  classical
  let A := sixConicActiveSignatures cfg gamma X
  let fiber := fourHostFullSignatureFiber cfg gamma X
  have hcover : sixConicRepetitionEvents cfg gamma X =
      A.biUnion fun s => (fiber s).powersetCard 2 := by
    ext E
    constructor
    · intro hE
      have hspec := mem_sixConicRepetitionEvents.mp hE
      obtain ⟨e, f, _hef, hEeq⟩ :=
        Finset.card_eq_two.mp (Finset.mem_powersetCard.mp hspec.1).2
      have heE : e ∈ E := by simp [hEeq]
      have hfE : f ∈ E := by simp [hEeq]
      let s := sixConicSignature cfg gamma e
      have hs : s ∈ A := by
        exact Finset.mem_image.mpr
          ⟨e, (Finset.mem_powersetCard.mp hspec.1).1 heE, rfl⟩
      have hEfiber : E ⊆ fiber s := by
        intro q hq
        exact Finset.mem_filter.mpr
          ⟨(Finset.mem_powersetCard.mp hspec.1).1 hq,
            hspec.2 q hq e heE⟩
      exact Finset.mem_biUnion.mpr ⟨s, hs,
        Finset.mem_powersetCard.mpr
          ⟨hEfiber, (Finset.mem_powersetCard.mp hspec.1).2⟩⟩
    · intro hE
      rcases Finset.mem_biUnion.mp hE with ⟨s, _hs, hEfiber⟩
      have hpow := Finset.mem_powersetCard.mp hEfiber
      apply mem_sixConicRepetitionEvents.mpr
      constructor
      · exact Finset.mem_powersetCard.mpr
          ⟨fun e he => (Finset.mem_filter.mp (hpow.1 he)).1, hpow.2⟩
      · intro e he f hf
        exact (Finset.mem_filter.mp (hpow.1 he)).2.trans
          (Finset.mem_filter.mp (hpow.1 hf)).2.symm
  have hdisjoint : (A : Set (Finset (Finset α))).PairwiseDisjoint
      (fun s => (fiber s).powersetCard 2) := by
    intro s _hs t _ht hst
    change Disjoint ((fiber s).powersetCard 2) ((fiber t).powersetCard 2)
    rw [Finset.disjoint_left]
    intro E hEs hEt
    have hsPow := Finset.mem_powersetCard.mp hEs
    obtain ⟨e, he⟩ : E.Nonempty := Finset.card_pos.mp (by omega)
    have hes := Finset.mem_filter.mp (hsPow.1 he)
    have het := Finset.mem_filter.mp
      ((Finset.mem_powersetCard.mp hEt).1 he)
    exact hst (hes.2.symm.trans het.2)
  rw [hcover, Finset.card_biUnion hdisjoint]
  apply Finset.sum_congr rfl
  intro s _hs
  rw [Finset.card_powersetCard]

private theorem sixConicFullEdges_card_le_six_of_four_host
    {α : Type u} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (gamma : DeterminedCircle cfg)
    (hgamma : (circleTrace cfg gamma.1).card = 6)
    (X : Finset α) (hX : X.card = 5)
    (hdisjoint : Disjoint (circleTrace cfg gamma.1) X)
    (H : GeometricBlock cfg)
    (hHcard : (geometricBlockSupport cfg H ∩ X).card = 4) :
    (sixConicFullEdges cfg gamma X).card ≤ 6 := by
  classical
  let A := sixConicActiveSignatures cfg gamma X
  let F := sixConicFullEdges cfg gamma X
  let fiber := fourHostFullSignatureFiber cfg gamma X
  have hA : A.card ≤ 4 :=
    sixConic_activeSignatures_card_le_four
      cfg gamma hgamma X hdisjoint
  have hfiberCard (s : Finset (Finset α)) (hs : s ∈ A) :
      1 ≤ (fiber s).card ∧ (fiber s).card ≤ 2 := by
    obtain ⟨e, he, hes⟩ := Finset.mem_image.mp hs
    have heFiber : e ∈ fiber s :=
      Finset.mem_filter.mpr ⟨he, hes⟩
    exact ⟨Finset.card_pos.mpr ⟨e, heFiber⟩,
      fourHostFullSignatureFiber_card_le_two
        cfg gamma hgamma X hX hdisjoint s⟩
  have hsumFiber : (∑ s ∈ A, (fiber s).card) = F.card := by
    have hcover : F = A.biUnion fiber := by
      ext e
      constructor
      · intro he
        exact Finset.mem_biUnion.mpr
          ⟨sixConicSignature cfg gamma e,
            Finset.mem_image.mpr ⟨e, he, rfl⟩,
            Finset.mem_filter.mpr ⟨he, rfl⟩⟩
      · intro he
        rcases Finset.mem_biUnion.mp he with ⟨s, _hs, hes⟩
        exact (Finset.mem_filter.mp hes).1
    have hdisjointFibers : (A : Set (Finset (Finset α))).PairwiseDisjoint
        fiber := by
      intro s _hs t _ht hst
      change Disjoint (fiber s) (fiber t)
      rw [Finset.disjoint_left]
      intro e hes het
      exact hst ((Finset.mem_filter.mp hes).2.symm.trans
        (Finset.mem_filter.mp het).2)
    rw [hcover, Finset.card_biUnion hdisjointFibers]
  have hevents :=
    fourHost_repetitionEvents_card_eq_sum_choose_fibers cfg gamma X
  change (sixConicRepetitionEvents cfg gamma X).card =
    ∑ s ∈ A, Nat.choose (fiber s).card 2 at hevents
  have hfirst :
      (∑ s ∈ A, (fiber s).card) ≤
        (∑ s ∈ A, Nat.choose (fiber s).card 2) + A.card := by
    have hpoint (s : Finset (Finset α)) (hs : s ∈ A) :
        (fiber s).card ≤ Nat.choose (fiber s).card 2 + 1 := by
      rcases hfiberCard s hs with ⟨hlower, hupper⟩
      interval_cases (fiber s).card <;> norm_num [Nat.choose] at *
    have h := Finset.sum_le_sum hpoint
    simpa [Finset.sum_add_distrib] using h
  have hrepetition := fourHost_repetitionEvents_card_le_two
    cfg gamma hgamma X hX hdisjoint H hHcard
  change F.card ≤ 6
  rw [hsumFiber, ← hevents] at hfirst
  omega

/-! ## Weight aggregation -/

private theorem fourHostPairWeight_le_two_add_fullIndicator
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

private theorem fourHost_sum_fullEdge_indicator
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

private theorem fourHostWeight_le_twenty_add_fullEdges
    {α : Type u} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (gamma : DeterminedCircle cfg)
    (hgamma : (circleTrace cfg gamma.1).card = 6)
    (X : Finset α) (hX : X.card = 5)
    (hdisjoint : Disjoint (circleTrace cfg gamma.1) X) :
    sixConicWeight cfg gamma X ≤
      20 + (sixConicFullEdges cfg gamma X).card := by
  classical
  have hsum := Finset.sum_le_sum fun e he =>
    fourHostPairWeight_le_two_add_fullIndicator
      cfg gamma hgamma X hdisjoint e he
  change sixConicTotalWeight cfg gamma X ≤ _ at hsum
  rw [sixConicTotalWeight_eq_sixConicWeight] at hsum
  have hpairCard : (X.powersetCard 2).card = 10 := by
    rw [Finset.card_powersetCard, hX]
    norm_num [Nat.choose]
  have hindicator := fourHost_sum_fullEdge_indicator cfg gamma X
  simp only [Finset.sum_add_distrib, Finset.sum_const,
    nsmul_eq_mul] at hsum
  rw [hpairCard, hindicator] at hsum
  omega

/-- A five-set with a generalized host carrying four outsiders has total
two-marked-circle weight at most `26`.  This derives the former S3 field from
the active-signature cap, repetition-host existence, and the proved event
capacity theorem. -/
theorem sixConic_four_outsider_host_weight_le
    {α : Type u} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (gamma : DeterminedCircle cfg)
    (hgamma : (circleTrace cfg gamma.1).card = 6)
    (X : Finset α) (hX : X.card = 5)
    (hdisjoint : Disjoint (circleTrace cfg gamma.1) X) :
    HasFourOutsiderHost cfg X → sixConicWeight cfg gamma X ≤ 26 := by
  rintro ⟨H, hHcard⟩
  have hfull := sixConicFullEdges_card_le_six_of_four_host
    cfg gamma hgamma X hX hdisjoint H hHcard
  have hweight := fourHostWeight_le_twenty_add_fullEdges
    cfg gamma hgamma X hX hdisjoint
  omega

end Erdos506.Incidence
