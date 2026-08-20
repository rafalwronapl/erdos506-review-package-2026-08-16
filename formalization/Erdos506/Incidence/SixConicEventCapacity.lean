import Erdos506.Incidence.SixConicSignaturesOnHostCap
import Erdos506.Incidence.SixConicU17

/-!
# Finite construction of the six-conic host-event capacity

The host-capacity clause is forced by the other local clauses.  There are
two independent bounds.

* A fixed four-set of endpoints supports at most two repetition events:
  three distinct perfect matchings would expose all six pairs as full edges,
  giving weight `18`, contrary to `u17`.
* On a fixed host there are at most three active signatures.  Equal-signature
  full edges form a matching, so every signature fiber has size at most
  `b / 2` and contributes at most `choose (b / 2) 2` events.

Taking the minimum gives exactly `sixConicHostEventCapacity`; the capacity
field itself is not an input to the construction.
-/

namespace Erdos506.Incidence

open Erdos506.Block
open Erdos506.Block.BlockSystem
open Erdos506.Finite
open Erdos506.V1
open Erdos506.V4
open scoped BigOperators

universe u

/-! ## Elementary data of a repetition event -/

private theorem repetitionEvent_card_two
    {alpha : Type u} [Fintype alpha] [DecidableEq alpha]
    {cfg : Configuration alpha} {gamma : DeterminedCircle cfg}
    {X : Finset alpha} {E : Finset (Finset alpha)}
    (hE : E ∈ sixConicRepetitionEvents cfg gamma X) : E.card = 2 := by
  exact (Finset.mem_powersetCard.mp
    (mem_sixConicRepetitionEvents.mp hE).1).2

private theorem repetitionEvent_edge_full
    {alpha : Type u} [Fintype alpha] [DecidableEq alpha]
    {cfg : Configuration alpha} {gamma : DeterminedCircle cfg}
    {X : Finset alpha} {E : Finset (Finset alpha)} {e : Finset alpha}
    (hE : E ∈ sixConicRepetitionEvents cfg gamma X) (he : e ∈ E) :
    e ∈ sixConicFullEdges cfg gamma X := by
  exact (Finset.mem_powersetCard.mp
    (mem_sixConicRepetitionEvents.mp hE).1).1 he

private theorem repetitionEvent_edge_card_two
    {alpha : Type u} [Fintype alpha] [DecidableEq alpha]
    {cfg : Configuration alpha} {gamma : DeterminedCircle cfg}
    {X : Finset alpha} {E : Finset (Finset alpha)} {e : Finset alpha}
    (hE : E ∈ sixConicRepetitionEvents cfg gamma X) (he : e ∈ E) :
    e.card = 2 := by
  exact (Finset.mem_powersetCard.mp
    (mem_sixConicFullEdges.mp (repetitionEvent_edge_full hE he)).1).2

private theorem repetitionEvent_edge_subset_X
    {alpha : Type u} [Fintype alpha] [DecidableEq alpha]
    {cfg : Configuration alpha} {gamma : DeterminedCircle cfg}
    {X : Finset alpha} {E : Finset (Finset alpha)} {e : Finset alpha}
    (hE : E ∈ sixConicRepetitionEvents cfg gamma X) (he : e ∈ E) :
    e ⊆ X := by
  exact (Finset.mem_powersetCard.mp
    (mem_sixConicFullEdges.mp (repetitionEvent_edge_full hE he)).1).1

private theorem repetitionEvent_union_subset_X
    {alpha : Type u} [Fintype alpha] [DecidableEq alpha]
    {cfg : Configuration alpha} {gamma : DeterminedCircle cfg}
    {X : Finset alpha} {E : Finset (Finset alpha)}
    (hE : E ∈ sixConicRepetitionEvents cfg gamma X) :
    E.biUnion id ⊆ X := by
  intro x hx
  rcases Finset.mem_biUnion.mp hx with ⟨e, he, hxe⟩
  exact repetitionEvent_edge_subset_X hE he hxe

private theorem repetitionEvent_union_card_four
    {alpha : Type u} [Fintype alpha] [DecidableEq alpha]
    (cfg : Configuration alpha) (gamma : DeterminedCircle cfg)
    (hgamma : (circleTrace cfg gamma.1).card = 6)
    (X : Finset alpha) (hdisjoint : Disjoint (circleTrace cfg gamma.1) X)
    {E : Finset (Finset alpha)}
    (hE : E ∈ sixConicRepetitionEvents cfg gamma X) :
    (E.biUnion id).card = 4 := by
  classical
  have hpairwise : (E : Set (Finset alpha)).PairwiseDisjoint id := by
    intro e he f hf hef
    exact sixConic_repetition_event_edges_disjoint
      cfg gamma hgamma X hdisjoint hE he hf hef
  rw [Finset.card_biUnion hpairwise]
  calc
    (∑ e ∈ E, (id e).card) = ∑ _e ∈ E, 2 := by
      apply Finset.sum_congr rfl
      intro e he
      simpa using repetitionEvent_edge_card_two hE he
    _ = 4 := by simp [repetitionEvent_card_two hE]

/-! A perfect matching containing a fixed edge is determined by its union. -/

private theorem repetitionEvent_eq_insert_complement
    {alpha : Type u} [Fintype alpha] [DecidableEq alpha]
    (cfg : Configuration alpha) (gamma : DeterminedCircle cfg)
    (hgamma : (circleTrace cfg gamma.1).card = 6)
    (X : Finset alpha) (hdisjoint : Disjoint (circleTrace cfg gamma.1) X)
    {E : Finset (Finset alpha)}
    (hE : E ∈ sixConicRepetitionEvents cfg gamma X)
    {e : Finset alpha} (he : e ∈ E) :
    E = {e, E.biUnion id \ e} := by
  classical
  obtain ⟨a, b, hab, hEeq⟩ := Finset.card_eq_two.mp
    (repetitionEvent_card_two hE)
  have haE : a ∈ E := by simp [hEeq]
  have hbE : b ∈ E := by simp [hEeq]
  have habDisjoint : Disjoint a b :=
    sixConic_repetition_event_edges_disjoint
      cfg gamma hgamma X hdisjoint hE haE hbE hab
  have hUnion : E.biUnion id = a ∪ b := by
    ext x
    simp [hEeq]
  have hba (x : alpha) (hxb : x ∈ b) : x ∉ a := by
    exact fun hxa => Finset.disjoint_left.mp habDisjoint hxa hxb
  have hab' (x : alpha) (hxa : x ∈ a) : x ∉ b := by
    exact fun hxb => Finset.disjoint_left.mp habDisjoint hxa hxb
  have hcompA : E.biUnion id \ a = b := by
    rw [hUnion]
    ext x
    simp only [Finset.mem_sdiff, Finset.mem_union]
    constructor
    · rintro ⟨hxa | hxb, hxna⟩
      · exact False.elim (hxna hxa)
      · exact hxb
    · intro hxb
      exact ⟨Or.inr hxb, hba x hxb⟩
  have hcompB : E.biUnion id \ b = a := by
    rw [hUnion]
    ext x
    simp only [Finset.mem_sdiff, Finset.mem_union]
    constructor
    · rintro ⟨hxa | hxb, hxnb⟩
      · exact hxa
      · exact False.elim (hxnb hxb)
    · intro hxa
      exact ⟨Or.inl hxa, hab' x hxa⟩
  have heCases : e = a ∨ e = b := by
    have := he
    rw [hEeq] at this
    simpa [eq_comm] using this
  rcases heCases with rfl | rfl
  · rw [hcompA, hEeq]
  · rw [hcompB, hEeq]
    ext q
    simp [or_comm]

private theorem repetitionEvent_eq_of_common_edge_of_union_eq
    {alpha : Type u} [Fintype alpha] [DecidableEq alpha]
    (cfg : Configuration alpha) (gamma : DeterminedCircle cfg)
    (hgamma : (circleTrace cfg gamma.1).card = 6)
    (X : Finset alpha) (hdisjoint : Disjoint (circleTrace cfg gamma.1) X)
    {E F : Finset (Finset alpha)}
    (hE : E ∈ sixConicRepetitionEvents cfg gamma X)
    (hF : F ∈ sixConicRepetitionEvents cfg gamma X)
    (hUnion : E.biUnion id = F.biUnion id)
    {e : Finset alpha} (heE : e ∈ E) (heF : e ∈ F) : E = F := by
  calc
    E = {e, E.biUnion id \ e} :=
      repetitionEvent_eq_insert_complement
        cfg gamma hgamma X hdisjoint hE heE
    _ = {e, F.biUnion id \ e} := by rw [hUnion]
    _ = F := (repetitionEvent_eq_insert_complement
      cfg gamma hgamma X hdisjoint hF heF).symm

/-! ## Bound one: at most two events on each endpoint four-set -/

private noncomputable def hostedEndpointFiber
    {alpha : Type u} [Fintype alpha] [DecidableEq alpha]
    (cfg : Configuration alpha) (gamma : DeterminedCircle cfg)
    (X : Finset alpha) (H : GeometricBlock cfg) (Y : Finset alpha) :
    Finset (Finset (Finset alpha)) :=
  (sixConicEventsHostedBy cfg gamma X H).filter fun E =>
    E.biUnion id = Y

private theorem hostedEndpointFiber_card_le_two
    {alpha : Type u} [Fintype alpha] [DecidableEq alpha]
    (cfg : Configuration alpha) (gamma : DeterminedCircle cfg)
    (hgamma : (circleTrace cfg gamma.1).card = 6)
    (X : Finset alpha) (hdisjoint : Disjoint (circleTrace cfg gamma.1) X)
    (H : GeometricBlock cfg) (Y : Finset alpha) :
    (hostedEndpointFiber cfg gamma X H Y).card ≤ 2 := by
  classical
  by_contra hnot
  have hthree : 3 ≤ (hostedEndpointFiber cfg gamma X H Y).card := by omega
  obtain ⟨P, hPsub, hPcard⟩ := Finset.exists_subset_card_eq hthree
  have hPevent (E : Finset (Finset alpha)) (hEP : E ∈ P) :
      E ∈ sixConicRepetitionEvents cfg gamma X :=
    (Finset.mem_filter.mp
      (show E ∈ sixConicEventsHostedBy cfg gamma X H from
        (Finset.mem_filter.mp (hPsub hEP)).1)).1
  have hPendpoints (E : Finset (Finset alpha)) (hEP : E ∈ P) :
      E.biUnion id = Y := (Finset.mem_filter.mp (hPsub hEP)).2
  have hPpairwise : (P : Set (Finset (Finset alpha))).PairwiseDisjoint id := by
    intro E hEP F hFP hEF
    change Disjoint E F
    rw [Finset.disjoint_left]
    intro e heE heF
    apply hEF
    exact repetitionEvent_eq_of_common_edge_of_union_eq
      cfg gamma hgamma X hdisjoint
      (hPevent E hEP) (hPevent F hFP)
      ((hPendpoints E hEP).trans (hPendpoints F hFP).symm) heE heF
  let U : Finset (Finset alpha) := P.biUnion id
  have hUcard : U.card = 6 := by
    dsimp [U]
    rw [Finset.card_biUnion hPpairwise]
    calc
      (∑ E ∈ P, (id E).card) = ∑ _E ∈ P, 2 := by
        apply Finset.sum_congr rfl
        intro E hEP
        simpa using repetitionEvent_card_two (hPevent E hEP)
      _ = 6 := by simp [hPcard]
  obtain ⟨E0, hE0P⟩ : P.Nonempty := Finset.card_pos.mp (by omega)
  have hYcard : Y.card = 4 := by
    rw [← hPendpoints E0 hE0P]
    exact repetitionEvent_union_card_four
      cfg gamma hgamma X hdisjoint (hPevent E0 hE0P)
  have hUsub : U ⊆ Y.powersetCard 2 := by
    intro e heU
    rcases Finset.mem_biUnion.mp heU with ⟨E, hEP, heE⟩
    apply Finset.mem_powersetCard.mpr
    constructor
    · intro x hxe
      rw [← hPendpoints E hEP]
      exact Finset.mem_biUnion.mpr ⟨e, heE, hxe⟩
    · exact repetitionEvent_edge_card_two (hPevent E hEP) heE
  have hPowersetCard : (Y.powersetCard 2).card = 6 := by
    rw [Finset.card_powersetCard, hYcard]
    norm_num [Nat.choose]
  have hUeq : U = Y.powersetCard 2 :=
    Finset.eq_of_subset_of_card_le hUsub (by omega)
  have hfull (e : Finset alpha) (he : e ∈ Y.powersetCard 2) :
      sixConicPairWeight cfg gamma e = 3 := by
    have heU : e ∈ U := by rw [hUeq]; exact he
    rcases Finset.mem_biUnion.mp heU with ⟨E, hEP, heE⟩
    exact (mem_sixConicFullEdges.mp
      (repetitionEvent_edge_full (hPevent E hEP) heE)).2
  have htotal : sixConicTotalWeight cfg gamma Y = 18 := by
    unfold sixConicTotalWeight
    calc
      (∑ e ∈ Y.powersetCard 2, sixConicPairWeight cfg gamma e) =
          ∑ _e ∈ Y.powersetCard 2, 3 := by
        apply Finset.sum_congr rfl
        intro e he
        exact hfull e he
      _ = 18 := by simp [hPowersetCard]
  have hweight : sixConicWeight cfg gamma Y = 18 := by
    rw [← sixConicTotalWeight_eq_sixConicWeight]
    exact htotal
  have hYsubX : Y ⊆ X := by
    rw [← hPendpoints E0 hE0P]
    exact repetitionEvent_union_subset_X (hPevent E0 hE0P)
  have hYdisjoint : Disjoint (circleTrace cfg gamma.1) Y :=
    hdisjoint.mono_right hYsubX
  have hu17 := sixConicWeight_le_seventeen
    cfg gamma hgamma Y hYcard hYdisjoint
  rw [hweight] at hu17
  omega

private theorem eventsHosted_card_le_two_choose_four
    {alpha : Type u} [Fintype alpha] [DecidableEq alpha]
    (cfg : Configuration alpha) (gamma : DeterminedCircle cfg)
    (hgamma : (circleTrace cfg gamma.1).card = 6)
    (X : Finset alpha) (hdisjoint : Disjoint (circleTrace cfg gamma.1) X)
    (H : GeometricBlock cfg) :
    (sixConicEventsHostedBy cfg gamma X H).card ≤
      2 * Nat.choose (sixConicHostOutsiderCount cfg X H) 4 := by
  classical
  let B := sixConicEventsHostedBy cfg gamma X H
  let A := B.image fun E => E.biUnion id
  let fiber := hostedEndpointFiber cfg gamma X H
  have hcover : B = A.biUnion fiber := by
    ext E
    constructor
    · intro hE
      exact Finset.mem_biUnion.mpr
        ⟨E.biUnion id, Finset.mem_image.mpr ⟨E, hE, rfl⟩,
          Finset.mem_filter.mpr ⟨hE, rfl⟩⟩
    · intro hE
      rcases Finset.mem_biUnion.mp hE with ⟨Y, _hY, hEfiber⟩
      exact (Finset.mem_filter.mp hEfiber).1
  have hfibersDisjoint :
      (A : Set (Finset alpha)).PairwiseDisjoint fiber := by
    intro Y _hY Z _hZ hYZ
    change Disjoint (fiber Y) (fiber Z)
    rw [Finset.disjoint_left]
    intro E hEY hEZ
    have hYeq := (Finset.mem_filter.mp hEY).2
    have hZeq := (Finset.mem_filter.mp hEZ).2
    exact hYZ (hYeq.symm.trans hZeq)
  have hBsum : B.card = ∑ Y ∈ A, (fiber Y).card := by
    rw [hcover, Finset.card_biUnion hfibersDisjoint]
  have hsum : (∑ Y ∈ A, (fiber Y).card) ≤ 2 * A.card := by
    calc
      (∑ Y ∈ A, (fiber Y).card) ≤ ∑ _Y ∈ A, 2 := by
        exact Finset.sum_le_sum fun Y _hY =>
          hostedEndpointFiber_card_le_two
            cfg gamma hgamma X hdisjoint H Y
      _ = 2 * A.card := by simp [Nat.mul_comm]
  let G := geometricBlockSupport cfg H ∩ X
  have hAsub : A ⊆ G.powersetCard 4 := by
    intro Y hYA
    obtain ⟨E, hEB, hEY⟩ := Finset.mem_image.mp hYA
    subst Y
    have hEdata := Finset.mem_filter.mp hEB
    have hErep := hEdata.1
    have hhost := hEdata.2
    apply Finset.mem_powersetCard.mpr
    constructor
    · intro x hx
      exact Finset.mem_inter.mpr
        ⟨hhost hx, repetitionEvent_union_subset_X hErep hx⟩
    · exact repetitionEvent_union_card_four
        cfg gamma hgamma X hdisjoint hErep
  have hAcard : A.card ≤ Nat.choose G.card 4 := by
    calc
      A.card ≤ (G.powersetCard 4).card := Finset.card_le_card hAsub
      _ = Nat.choose G.card 4 := by rw [Finset.card_powersetCard]
  change B.card ≤ 2 * Nat.choose G.card 4
  rw [hBsum]
  exact hsum.trans (Nat.mul_le_mul_left 2 hAcard)

/-! ## Bound two: three host signatures and matching fibers -/

private noncomputable def fullEdgesOnHost
    {alpha : Type u} [Fintype alpha] [DecidableEq alpha]
    (cfg : Configuration alpha) (gamma : DeterminedCircle cfg)
    (X : Finset alpha) (H : GeometricBlock cfg) : Finset (Finset alpha) :=
  (sixConicFullEdges cfg gamma X).filter fun e =>
    e ⊆ geometricBlockSupport cfg H

private noncomputable def hostSignatureFiber
    {alpha : Type u} [Fintype alpha] [DecidableEq alpha]
    (cfg : Configuration alpha) (gamma : DeterminedCircle cfg)
    (X : Finset alpha) (H : GeometricBlock cfg)
    (s : Finset (Finset alpha)) : Finset (Finset alpha) :=
  (fullEdgesOnHost cfg gamma X H).filter fun e =>
    sixConicSignature cfg gamma e = s

private theorem hostSignatureFiber_card_le_half
    {alpha : Type u} [Fintype alpha] [DecidableEq alpha]
    (cfg : Configuration alpha) (gamma : DeterminedCircle cfg)
    (hgamma : (circleTrace cfg gamma.1).card = 6)
    (X : Finset alpha) (hdisjoint : Disjoint (circleTrace cfg gamma.1) X)
    (H : GeometricBlock cfg) (s : Finset (Finset alpha)) :
    (hostSignatureFiber cfg gamma X H s).card ≤
      sixConicHostOutsiderCount cfg X H / 2 := by
  classical
  let G := geometricBlockSupport cfg H ∩ X
  let F := hostSignatureFiber cfg gamma X H s
  apply card_le_half_of_pairwiseDisjoint_pairs G F
  · intro e he
    have heData := Finset.mem_filter.mp he
    have heHost := Finset.mem_filter.mp heData.1
    have heX := (Finset.mem_powersetCard.mp
      (mem_sixConicFullEdges.mp heHost.1).1).1
    intro x hx
    exact Finset.mem_inter.mpr ⟨heHost.2 hx, heX hx⟩
  · intro e he
    have heFull := (Finset.mem_filter.mp
      (Finset.mem_filter.mp he).1).1
    exact (Finset.mem_powersetCard.mp
      (mem_sixConicFullEdges.mp heFull).1).2
  · intro e he f hf hef
    have heData := Finset.mem_filter.mp he
    have hfData := Finset.mem_filter.mp hf
    have heFull := (Finset.mem_filter.mp heData.1).1
    have hfFull := (Finset.mem_filter.mp hfData.1).1
    exact sixConic_equal_full_signatures_disjoint
      cfg gamma hgamma X hdisjoint heFull hfFull hef
        (heData.2.trans hfData.2.symm)

private theorem eventsHosted_card_le_three_choose_half
    {alpha : Type u} [Fintype alpha] [DecidableEq alpha]
    (cfg : Configuration alpha) (gamma : DeterminedCircle cfg)
    (hgamma : (circleTrace cfg gamma.1).card = 6)
    (X : Finset alpha) (hdisjoint : Disjoint (circleTrace cfg gamma.1) X)
    (H : GeometricBlock cfg) :
    (sixConicEventsHostedBy cfg gamma X H).card ≤
      3 * Nat.choose (sixConicHostOutsiderCount cfg X H / 2) 2 := by
  classical
  let B := sixConicEventsHostedBy cfg gamma X H
  let A := sixConicSignaturesOnHost cfg gamma X H
  let fiber := hostSignatureFiber cfg gamma X H
  have hcover : B = A.biUnion fun s => (fiber s).powersetCard 2 := by
    ext E
    constructor
    · intro hEB
      have hEdata := Finset.mem_filter.mp hEB
      have hErep := hEdata.1
      have hhost := hEdata.2
      have hEspec := mem_sixConicRepetitionEvents.mp hErep
      obtain ⟨e, heE⟩ : E.Nonempty :=
        Finset.card_pos.mp (by
          rw [(Finset.mem_powersetCard.mp hEspec.1).2]
          norm_num)
      let s := sixConicSignature cfg gamma e
      have heFull := (Finset.mem_powersetCard.mp hEspec.1).1 heE
      have heHost : e ⊆ geometricBlockSupport cfg H := by
        intro x hx
        exact hhost (Finset.mem_biUnion.mpr ⟨e, heE, hx⟩)
      have hsA : s ∈ A := by
        apply Finset.mem_image.mpr
        exact ⟨e, Finset.mem_filter.mpr ⟨heFull, heHost⟩, rfl⟩
      apply Finset.mem_biUnion.mpr
      refine ⟨s, hsA, Finset.mem_powersetCard.mpr ⟨?_, ?_⟩⟩
      · intro f hfE
        have hfFull := (Finset.mem_powersetCard.mp hEspec.1).1 hfE
        have hfHost : f ⊆ geometricBlockSupport cfg H := by
          intro x hx
          exact hhost (Finset.mem_biUnion.mpr ⟨f, hfE, hx⟩)
        apply Finset.mem_filter.mpr
        exact ⟨Finset.mem_filter.mpr ⟨hfFull, hfHost⟩,
          hEspec.2 f hfE e heE⟩
      · exact (Finset.mem_powersetCard.mp hEspec.1).2
    · intro hE
      rcases Finset.mem_biUnion.mp hE with ⟨s, _hs, hEpow⟩
      have hpow := Finset.mem_powersetCard.mp hEpow
      apply Finset.mem_filter.mpr
      constructor
      · apply mem_sixConicRepetitionEvents.mpr
        constructor
        · apply Finset.mem_powersetCard.mpr
          exact ⟨fun e he => (Finset.mem_filter.mp
            (Finset.mem_filter.mp (hpow.1 he)).1).1, hpow.2⟩
        · intro e he f hf
          exact (Finset.mem_filter.mp (hpow.1 he)).2.trans
            (Finset.mem_filter.mp (hpow.1 hf)).2.symm
      · intro x hx
        rcases Finset.mem_biUnion.mp hx with ⟨e, heE, hxe⟩
        exact (Finset.mem_filter.mp
          (Finset.mem_filter.mp (hpow.1 heE)).1).2 hxe
  have hfibersDisjoint :
      (A : Set (Finset (Finset alpha))).PairwiseDisjoint
        (fun s => (fiber s).powersetCard 2) := by
    intro s _hs t _ht hst
    change Disjoint ((fiber s).powersetCard 2) ((fiber t).powersetCard 2)
    rw [Finset.disjoint_left]
    intro E hEs hEt
    have hsPow := Finset.mem_powersetCard.mp hEs
    obtain ⟨e, heE⟩ : E.Nonempty := Finset.card_pos.mp (by omega)
    have hes := Finset.mem_filter.mp (hsPow.1 heE)
    have het := Finset.mem_filter.mp
      ((Finset.mem_powersetCard.mp hEt).1 heE)
    exact hst (hes.2.symm.trans het.2)
  have hBsum : B.card =
      ∑ s ∈ A, Nat.choose (fiber s).card 2 := by
    rw [hcover, Finset.card_biUnion hfibersDisjoint]
    apply Finset.sum_congr rfl
    intro s _hs
    rw [Finset.card_powersetCard]
  let b := sixConicHostOutsiderCount cfg X H
  have hfiber (s : Finset (Finset alpha)) : (fiber s).card ≤ b / 2 :=
    hostSignatureFiber_card_le_half
      cfg gamma hgamma X hdisjoint H s
  have hchoose (s : Finset (Finset alpha)) :
      Nat.choose (fiber s).card 2 ≤ Nat.choose (b / 2) 2 :=
    Nat.choose_le_choose 2 (hfiber s)
  have hsum : (∑ s ∈ A, Nat.choose (fiber s).card 2) ≤
      A.card * Nat.choose (b / 2) 2 := by
    calc
      (∑ s ∈ A, Nat.choose (fiber s).card 2) ≤
          ∑ _s ∈ A, Nat.choose (b / 2) 2 := by
        exact Finset.sum_le_sum fun s _hs => hchoose s
      _ = A.card * Nat.choose (b / 2) 2 := by simp
  have hA := sixConicSignaturesOnHost_card_le_three
    cfg gamma hgamma X hdisjoint H
  change B.card ≤ 3 * Nat.choose (b / 2) 2
  rw [hBsum]
  exact hsum.trans (Nat.mul_le_mul_right (Nat.choose (b / 2) 2) hA)

/-! ## Exact capacity -/

/-- The S2 event-capacity inequality is a theorem of the other local
six-conic clauses. -/
theorem sixConicEventsHostedBy_card_le_hostEventCapacity
    {alpha : Type u} [Fintype alpha] [DecidableEq alpha]
    (cfg : Configuration alpha) (gamma : DeterminedCircle cfg)
    (hgamma : (circleTrace cfg gamma.1).card = 6)
    (X : Finset alpha) (hdisjoint : Disjoint (circleTrace cfg gamma.1) X)
    (H : GeometricBlock cfg) :
    (sixConicEventsHostedBy cfg gamma X H).card ≤
      sixConicHostEventCapacity (sixConicHostOutsiderCount cfg X H) := by
  unfold sixConicHostEventCapacity
  rw [Nat.le_min]
  constructor
  · exact eventsHosted_card_le_two_choose_four
      cfg gamma hgamma X hdisjoint H
  · exact eventsHosted_card_le_three_choose_half
      cfg gamma hgamma X hdisjoint H

end Erdos506.Incidence
