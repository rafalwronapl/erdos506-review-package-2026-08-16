import Erdos506.Finite.Bonferroni
import Erdos506.V1.Carrier
import Mathlib.Tactic

/-!
# The six-marked-conic event interface

This file gives a semantic Lean vocabulary for clauses S1--S4 of the
manuscript's six-marked-conic lemma.  The edge weights, matching signatures,
repetition events, their geometric hosts, the weight `W`, and the line
incidence `J` are all defined from the concrete V1 line/circle carriers.

Triple ownership proves that the pairs in one signature are disjoint, hence
every edge weight is at most three.  It also proves uniqueness of a
generalized host once existence is known.  All former interface fields have
now been replaced by field-free geometric theorems; this module remains the
foundational vocabulary for their event definitions.
-/

namespace Erdos506.Incidence

open Erdos506.Block
open Erdos506.Block.BlockSystem
open Erdos506.Finite
open Erdos506.V1
open Erdos506.V4
open scoped BigOperators

universe u

/-- Determined circles through an outsider pair `e` whose trace on the
selected six-circle is exactly a two-set. -/
noncomputable def sixConicPairCircles
    {α : Type*} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (gamma : DeterminedCircle cfg)
    (e : Finset α) : Finset (DeterminedCircle cfg) := by
  letI : DecidableEq (DeterminedCircle cfg) := Classical.decEq _
  exact Finset.univ.filter fun c =>
    e ⊆ circleTrace cfg c.1 ∧
      (circleTrace cfg c.1 ∩ circleTrace cfg gamma.1).card = 2

/-- The paper's edge weight `q_e`. -/
noncomputable def sixConicPairWeight
    {α : Type*} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (gamma : DeterminedCircle cfg)
    (e : Finset α) : Nat :=
  (sixConicPairCircles cfg gamma e).card

/-- The matching signature carried by an outsider edge: one marked
two-subset of `gamma` for each circle counted by `q_e`. -/
noncomputable def sixConicSignature
    {α : Type*} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (gamma : DeterminedCircle cfg)
    (e : Finset α) : Finset (Finset α) := by
  classical
  exact (sixConicPairCircles cfg gamma e).image fun c =>
    circleTrace cfg c.1 ∩ circleTrace cfg gamma.1

@[simp] theorem mem_sixConicPairCircles
    {α : Type*} [Fintype α] [DecidableEq α]
    {cfg : Configuration α} {gamma c : DeterminedCircle cfg}
    {e : Finset α} :
    c ∈ sixConicPairCircles cfg gamma e ↔
      e ⊆ circleTrace cfg c.1 ∧
        (circleTrace cfg c.1 ∩ circleTrace cfg gamma.1).card = 2 := by
  classical
  simp [sixConicPairCircles]

theorem sixConicPairCircle_gammaPair_subset
    {α : Type*} [Fintype α] [DecidableEq α]
    {cfg : Configuration α} {gamma c : DeterminedCircle cfg}
    {e : Finset α} (_hc : c ∈ sixConicPairCircles cfg gamma e) :
    circleTrace cfg c.1 ∩ circleTrace cfg gamma.1 ⊆
      circleTrace cfg gamma.1 :=
  Finset.inter_subset_right

theorem sixConicPairCircle_gammaPair_card
    {α : Type*} [Fintype α] [DecidableEq α]
    {cfg : Configuration α} {gamma c : DeterminedCircle cfg}
    {e : Finset α} (hc : c ∈ sixConicPairCircles cfg gamma e) :
    (circleTrace cfg c.1 ∩ circleTrace cfg gamma.1).card = 2 :=
  (mem_sixConicPairCircles.mp hc).2

/-- Different circles counted at the same outsider pair have disjoint
marked pairs on `gamma`.  Otherwise the two circle blocks would share that
marked point and both endpoints of `e`, contradicting triple ownership. -/
theorem sixConicPairCircle_gammaPairs_disjoint
    {α : Type*} [Fintype α] [DecidableEq α]
    {cfg : Configuration α} {gamma : DeterminedCircle cfg}
    {e : Finset α} (he : e.card = 2)
    (hedisjoint : Disjoint e (circleTrace cfg gamma.1))
    {c d : DeterminedCircle cfg}
    (hc : c ∈ sixConicPairCircles cfg gamma e)
    (hd : d ∈ sixConicPairCircles cfg gamma e) (hcd : c ≠ d) :
    Disjoint
      (circleTrace cfg c.1 ∩ circleTrace cfg gamma.1)
      (circleTrace cfg d.1 ∩ circleTrace cfg gamma.1) := by
  rw [Finset.disjoint_left]
  intro z hzc hzd
  have hzGamma : z ∈ circleTrace cfg gamma.1 :=
    (Finset.mem_inter.mp hzc).2
  have hzNotE : z ∉ e := by
    intro hzE
    exact Finset.disjoint_left.mp hedisjoint hzE hzGamma
  have hec := (mem_sixConicPairCircles.mp hc).1
  have hed := (mem_sixConicPairCircles.mp hd).1
  have hsub : insert z e ⊆
      circleTrace cfg c.1 ∩ circleTrace cfg d.1 := by
    intro x hx
    rw [Finset.mem_inter]
    rcases Finset.mem_insert.mp hx with rfl | hxE
    · exact ⟨(Finset.mem_inter.mp hzc).1,
        (Finset.mem_inter.mp hzd).1⟩
    · exact ⟨hec hxE, hed hxE⟩
  have hcardInsert : (insert z e).card = 3 := by
    simp [hzNotE, he]
  have hinter :=
    (geometricBlockSystem cfg).distinct_block_inter_card_lt_three
      (b := (Sum.inr c : GeometricBlock cfg))
      (c := (Sum.inr d : GeometricBlock cfg)) (by
        intro h
        exact hcd (Sum.inr.inj h))
  change (circleTrace cfg c.1 ∩ circleTrace cfg d.1).card < 3 at hinter
  have hle := Finset.card_le_card hsub
  omega

/-- On the counted family, the map from a circle to its marked pair is
injective. -/
theorem sixConicPairCircle_gammaPair_injOn
    {α : Type*} [Fintype α] [DecidableEq α]
    {cfg : Configuration α} {gamma : DeterminedCircle cfg}
    {e : Finset α} (he : e.card = 2)
    (hedisjoint : Disjoint e (circleTrace cfg gamma.1)) :
    Set.InjOn
      (fun c : DeterminedCircle cfg =>
        circleTrace cfg c.1 ∩ circleTrace cfg gamma.1)
      (sixConicPairCircles cfg gamma e) := by
  intro c hc d hd hpair
  by_contra hcd
  have hdisj := sixConicPairCircle_gammaPairs_disjoint
    he hedisjoint hc hd hcd
  change
    circleTrace cfg c.1 ∩ circleTrace cfg gamma.1 =
      circleTrace cfg d.1 ∩ circleTrace cfg gamma.1 at hpair
  have hself : Disjoint
      (circleTrace cfg c.1 ∩ circleTrace cfg gamma.1)
      (circleTrace cfg c.1 ∩ circleTrace cfg gamma.1) := by
    simpa [hpair] using hdisj
  have hcard := sixConicPairCircle_gammaPair_card hc
  have hnonempty :
      (circleTrace cfg c.1 ∩ circleTrace cfg gamma.1).Nonempty :=
    Finset.card_pos.mp (by omega)
  obtain ⟨z, hz⟩ := hnonempty
  exact Finset.disjoint_left.mp hself hz hz

/-- The signature has exactly `q_e` members. -/
theorem card_sixConicSignature
    {α : Type*} [Fintype α] [DecidableEq α]
    {cfg : Configuration α} {gamma : DeterminedCircle cfg}
    {e : Finset α} (he : e.card = 2)
    (hedisjoint : Disjoint e (circleTrace cfg gamma.1)) :
    (sixConicSignature cfg gamma e).card =
      sixConicPairWeight cfg gamma e := by
  classical
  rw [sixConicSignature, sixConicPairWeight]
  exact Finset.card_image_iff.mpr
    (sixConicPairCircle_gammaPair_injOn he hedisjoint)

/-- Every member of an edge signature is a marked pair on `gamma`. -/
theorem sixConicSignature_pair
    {α : Type*} [Fintype α] [DecidableEq α]
    {cfg : Configuration α} {gamma : DeterminedCircle cfg}
    {e p : Finset α} (hp : p ∈ sixConicSignature cfg gamma e) :
    p.card = 2 ∧ p ⊆ circleTrace cfg gamma.1 := by
  classical
  rw [sixConicSignature] at hp
  obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hp
  exact ⟨sixConicPairCircle_gammaPair_card hc,
    sixConicPairCircle_gammaPair_subset hc⟩

/-- The marked pairs in one signature form a matching. -/
theorem sixConicSignature_pairwiseDisjoint
    {α : Type*} [Fintype α] [DecidableEq α]
    {cfg : Configuration α} {gamma : DeterminedCircle cfg}
    {e : Finset α} (he : e.card = 2)
    (hedisjoint : Disjoint e (circleTrace cfg gamma.1)) :
    ((sixConicSignature cfg gamma e : Finset (Finset α)) :
      Set (Finset α)).PairwiseDisjoint id := by
  classical
  intro p hp q hq hpq
  rw [sixConicSignature] at hp hq
  obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hp
  obtain ⟨d, hd, hdPair⟩ := Finset.mem_image.mp hq
  subst q
  apply sixConicPairCircle_gammaPairs_disjoint he hedisjoint hc hd
  intro hcd
  apply hpq
  simp [hcd]

/-- The elementary matching argument gives `q_e <= 3`.  This is not a
field of the projective principle. -/
theorem sixConicPairWeight_le_three
    {α : Type*} [Fintype α] [DecidableEq α]
    {cfg : Configuration α} {gamma : DeterminedCircle cfg}
    {e : Finset α} (hgamma : (circleTrace cfg gamma.1).card = 6)
    (he : e.card = 2)
    (hedisjoint : Disjoint e (circleTrace cfg gamma.1)) :
    sixConicPairWeight cfg gamma e ≤ 3 := by
  classical
  have hmatch := card_le_half_of_pairwiseDisjoint_pairs
    (circleTrace cfg gamma.1) (sixConicSignature cfg gamma e)
    (fun p hp => (sixConicSignature_pair hp).2)
    (fun p hp => (sixConicSignature_pair hp).1)
    (sixConicSignature_pairwiseDisjoint he hedisjoint)
  rw [card_sixConicSignature he hedisjoint, hgamma] at hmatch
  norm_num at hmatch ⊢
  exact hmatch

/-- Full outsider edges in `X`, namely those with `q_e = 3`. -/
noncomputable def sixConicFullEdges
    {α : Type*} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (gamma : DeterminedCircle cfg)
    (X : Finset α) : Finset (Finset α) :=
  (X.powersetCard 2).filter fun e =>
    sixConicPairWeight cfg gamma e = 3

@[simp] theorem mem_sixConicFullEdges
    {α : Type*} [Fintype α] [DecidableEq α]
    {cfg : Configuration α} {gamma : DeterminedCircle cfg}
    {X e : Finset α} :
    e ∈ sixConicFullEdges cfg gamma X ↔
      e ∈ X.powersetCard 2 ∧ sixConicPairWeight cfg gamma e = 3 := by
  classical
  simp [sixConicFullEdges]

/-- The distinct full matching signatures active on `X`. -/
noncomputable def sixConicActiveSignatures
    {α : Type*} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (gamma : DeterminedCircle cfg)
    (X : Finset α) : Finset (Finset (Finset α)) := by
  classical
  exact (sixConicFullEdges cfg gamma X).image fun e =>
    sixConicSignature cfg gamma e

/-- Active full signatures having a support edge on a fixed generalized
host.  In the circular lift their centres lie on the host's trace line. -/
noncomputable def sixConicSignaturesOnHost
    {α : Type*} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (gamma : DeterminedCircle cfg)
    (X : Finset α) (H : GeometricBlock cfg) :
    Finset (Finset (Finset α)) := by
  classical
  exact ((sixConicFullEdges cfg gamma X).filter fun e =>
    e ⊆ geometricBlockSupport cfg H).image fun e =>
      sixConicSignature cfg gamma e

/-- Unordered pairs of distinct full outsider edges carrying the same
matching signature. -/
noncomputable def sixConicRepetitionEvents
    {α : Type*} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (gamma : DeterminedCircle cfg)
    (X : Finset α) : Finset (Finset (Finset α)) :=
  ((sixConicFullEdges cfg gamma X).powersetCard 2).filter fun E =>
    ∀ e ∈ E, ∀ f ∈ E,
      sixConicSignature cfg gamma e = sixConicSignature cfg gamma f

@[simp] theorem mem_sixConicRepetitionEvents
    {α : Type*} [Fintype α] [DecidableEq α]
    {cfg : Configuration α} {gamma : DeterminedCircle cfg}
    {X : Finset α} {E : Finset (Finset α)} :
    E ∈ sixConicRepetitionEvents cfg gamma X ↔
      E ∈ (sixConicFullEdges cfg gamma X).powersetCard 2 ∧
        ∀ e ∈ E, ∀ f ∈ E,
          sixConicSignature cfg gamma e = sixConicSignature cfg gamma f := by
  classical
  simp [sixConicRepetitionEvents]

/-- A repetition event is hosted by `H` when all four of its outsider
endpoints lie on that maximal line or circle. -/
def SixConicEventHostedBy
    {α : Type*} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (E : Finset (Finset α))
    (H : GeometricBlock cfg) : Prop :=
  E.biUnion id ⊆ geometricBlockSupport cfg H

/-- Repetition events assigned to one generalized host. -/
noncomputable def sixConicEventsHostedBy
    {α : Type*} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (gamma : DeterminedCircle cfg)
    (X : Finset α) (H : GeometricBlock cfg) :
    Finset (Finset (Finset α)) := by
  classical
  exact (sixConicRepetitionEvents cfg gamma X).filter fun E =>
    SixConicEventHostedBy cfg E H

/-- Number of selected outsiders of `X` on a host. -/
noncomputable def sixConicHostOutsiderCount
    {α : Type*} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (X : Finset α)
    (H : GeometricBlock cfg) : Nat :=
  (geometricBlockSupport cfg H ∩ X).card

/-- The event-capacity expression in S2. -/
def sixConicHostEventCapacity (b : Nat) : Nat :=
  min (2 * Nat.choose b 4) (3 * Nat.choose (b / 2) 2)

/-- The global two-marked-circle weight `W`.  This is definitionally the
same circle-side sum used by the earlier U17 interface. -/
noncomputable def sixConicWeight
    {α : Type*} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (gamma : DeterminedCircle cfg)
    (X : Finset α) : Nat :=
  ∑ c : DeterminedCircle cfg,
    if (circleTrace cfg c.1 ∩ circleTrace cfg gamma.1).card = 2 then
      Nat.choose (circleTrace cfg c.1 ∩ X).card 2
    else 0

/-- Edge-side form of the same two-marked-circle weight. -/
noncomputable def sixConicTotalWeight
    {α : Type*} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (gamma : DeterminedCircle cfg)
    (X : Finset α) : Nat :=
  ∑ e ∈ X.powersetCard 2, sixConicPairWeight cfg gamma e

/-- Double counting pairs on each determined circle identifies the edge and
circle forms of `W`. -/
theorem sixConicTotalWeight_eq_sixConicWeight
    {α : Type*} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (gamma : DeterminedCircle cfg)
    (X : Finset α) :
    sixConicTotalWeight cfg gamma X = sixConicWeight cfg gamma X := by
  classical
  unfold sixConicTotalWeight sixConicWeight
  calc
    (∑ e ∈ X.powersetCard 2, sixConicPairWeight cfg gamma e) =
        ∑ e ∈ X.powersetCard 2, ∑ c : DeterminedCircle cfg,
          if e ⊆ circleTrace cfg c.1 ∧
              (circleTrace cfg c.1 ∩ circleTrace cfg gamma.1).card = 2
          then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro e _he
      rw [sixConicPairWeight, sixConicPairCircles,
        Finset.card_eq_sum_ones, Finset.sum_filter]
    _ = ∑ c : DeterminedCircle cfg, ∑ e ∈ X.powersetCard 2,
          if e ⊆ circleTrace cfg c.1 ∧
              (circleTrace cfg c.1 ∩ circleTrace cfg gamma.1).card = 2
          then 1 else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ c : DeterminedCircle cfg,
          if (circleTrace cfg c.1 ∩ circleTrace cfg gamma.1).card = 2 then
            Nat.choose (circleTrace cfg c.1 ∩ X).card 2
          else 0 := by
      apply Finset.sum_congr rfl
      intro c _hc
      by_cases hgamma :
          (circleTrace cfg c.1 ∩ circleTrace cfg gamma.1).card = 2
      · simp only [hgamma, and_true, if_true]
        rw [← Finset.sum_filter, ← Finset.card_eq_sum_ones]
        rw [← Finset.card_powersetCard]
        congr 1
        ext e
        simp only [Finset.mem_filter, Finset.mem_powersetCard]
        constructor
        · rintro ⟨⟨heX, heCard⟩, heCircle⟩
          exact ⟨fun x hx =>
            Finset.mem_inter.mpr ⟨heCircle hx, heX hx⟩, heCard⟩
        · rintro ⟨heInter, heCard⟩
          exact ⟨⟨fun x hx => (Finset.mem_inter.mp (heInter hx)).2,
            heCard⟩, fun x hx => (Finset.mem_inter.mp (heInter hx)).1⟩
      · simp [hgamma]

/-- Rewrite the weight of a subset `Y` as a filtered sum over the pairs of
an ambient finite set `X`. -/
theorem sixConicTotalWeight_eq_ambient_sum
    {α : Type*} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (gamma : DeterminedCircle cfg)
    {X Y : Finset α} (hYX : Y ⊆ X) :
    sixConicTotalWeight cfg gamma Y =
      ∑ e ∈ X.powersetCard 2,
        if e ⊆ Y then sixConicPairWeight cfg gamma e else 0 := by
  classical
  unfold sixConicTotalWeight
  rw [← Finset.sum_filter]
  congr 1
  ext e
  simp only [Finset.mem_powersetCard, Finset.mem_filter]
  constructor
  · rintro ⟨heY, heCard⟩
    exact ⟨⟨heY.trans hYX, heCard⟩, heY⟩
  · rintro ⟨⟨_heX, heCard⟩, heY⟩
    exact ⟨heY, heCard⟩

/-- Every pair of a five-set belongs to exactly three of its four-subsets,
so summing the four-subset weights counts the full weight three times. -/
theorem sum_sixConicTotalWeight_powersetCard_four
    {α : Type*} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (gamma : DeterminedCircle cfg)
    (X : Finset α) (hX : X.card = 5) :
    (∑ Y ∈ X.powersetCard 4, sixConicTotalWeight cfg gamma Y) =
      3 * sixConicTotalWeight cfg gamma X := by
  classical
  calc
    (∑ Y ∈ X.powersetCard 4, sixConicTotalWeight cfg gamma Y) =
        ∑ Y ∈ X.powersetCard 4, ∑ e ∈ X.powersetCard 2,
          if e ⊆ Y then sixConicPairWeight cfg gamma e else 0 := by
      apply Finset.sum_congr rfl
      intro Y hY
      exact sixConicTotalWeight_eq_ambient_sum cfg gamma
        (Finset.mem_powersetCard.mp hY).1
    _ = ∑ e ∈ X.powersetCard 2, ∑ Y ∈ X.powersetCard 4,
          if e ⊆ Y then sixConicPairWeight cfg gamma e else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ e ∈ X.powersetCard 2,
          3 * sixConicPairWeight cfg gamma e := by
      apply Finset.sum_congr rfl
      intro e he
      have heSpec := Finset.mem_powersetCard.mp he
      rw [← Finset.sum_filter]
      have hcount := Finset.card_filter_powersetCard_subset
        e X 4 heSpec.1 (by omega)
      simp only [Finset.sum_const, nsmul_eq_mul]
      rw [hcount, hX, heSpec.2]
      norm_num [Nat.choose]
    _ = 3 * sixConicTotalWeight cfg gamma X := by
      unfold sixConicTotalWeight
      rw [Finset.mul_sum]

/-- The line incidence `J`: incidences of labels in `X` with original
determined lines carrying exactly two marked points of `gamma`. -/
noncomputable def sixConicLineIncidence
    {α : Type*} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (gamma : DeterminedCircle cfg)
    (X : Finset α) : Nat :=
  ∑ L : DeterminedLine cfg,
    if (lineSupport cfg L ∩ circleTrace cfg gamma.1).card = 2 then
      (lineSupport cfg L ∩ X).card
    else 0

/-- There is one maximal generalized host carrying four outsiders. -/
def HasFourOutsiderHost
    {α : Type*} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (X : Finset α) : Prop :=
  ∃ H : GeometricBlock cfg,
    (geometricBlockSupport cfg H ∩ X).card = 4

/-- A maximal generalized host carries all five outsiders and no marked
point of `gamma`. -/
def HasFiveOutsiderHostDisjoint
    {α : Type*} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (gamma : DeterminedCircle cfg)
    (X : Finset α) : Prop :=
  ∃ H : GeometricBlock cfg,
    X ⊆ geometricBlockSupport cfg H ∧
      Disjoint (geometricBlockSupport cfg H) (circleTrace cfg gamma.1)

/-- A maximal generalized host carries all five outsiders and at least one
marked point of `gamma`. -/
def HasFiveOutsiderHostMeeting
    {α : Type*} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (gamma : DeterminedCircle cfg)
    (X : Finset α) : Prop :=
  ∃ H : GeometricBlock cfg,
    X ⊆ geometricBlockSupport cfg H ∧
      ¬Disjoint (geometricBlockSupport cfg H) (circleTrace cfg gamma.1)

/-- Multiplicities of the distinct active full signatures, as an unordered
multiset. -/
noncomputable def sixConicFullSignatureMultiplicityProfile
    {α : Type*} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (gamma : DeterminedCircle cfg)
    (X : Finset α) : Multiset Nat := by
  classical
  exact (sixConicActiveSignatures cfg gamma X).val.map fun s =>
    ((sixConicFullEdges cfg gamma X).filter fun e =>
      sixConicSignature cfg gamma e = s).card

/-- Distinct full edges carrying the same signature are disjoint.  This is
an incidence consequence of triple ownership, not additional projective
input: a common outsider together with either marked pair forces the two
corresponding circles to coincide, and two different marked pairs then give
two circles sharing three outsider points. -/
theorem sixConic_equal_full_signatures_disjoint
    {α : Type u} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (gamma : DeterminedCircle cfg)
    (_hgamma : (circleTrace cfg gamma.1).card = 6)
    (X : Finset α) (hdisjoint : Disjoint (circleTrace cfg gamma.1) X)
    {e f : Finset α}
    (he : e ∈ sixConicFullEdges cfg gamma X)
    (hf : f ∈ sixConicFullEdges cfg gamma X)
    (hef : e ≠ f)
    (hsignature :
      sixConicSignature cfg gamma e = sixConicSignature cfg gamma f) :
    Disjoint e f := by
  classical
  have heSpec := mem_sixConicFullEdges.mp he
  have hfSpec := mem_sixConicFullEdges.mp hf
  have hePow := Finset.mem_powersetCard.mp heSpec.1
  have hfPow := Finset.mem_powersetCard.mp hfSpec.1
  have heCard : e.card = 2 := hePow.2
  have hfCard : f.card = 2 := hfPow.2
  have heDisjoint : Disjoint e (circleTrace cfg gamma.1) :=
    hdisjoint.symm.mono_left hePow.1
  have hsignatureCard :
      (sixConicSignature cfg gamma e).card = 3 := by
    calc
      (sixConicSignature cfg gamma e).card =
          sixConicPairWeight cfg gamma e :=
        card_sixConicSignature heCard heDisjoint
      _ = 3 := heSpec.2
  rw [Finset.disjoint_left]
  intro x hxe hxf
  have hxX : x ∈ X := hePow.1 hxe
  have hxNotGamma : x ∉ circleTrace cfg gamma.1 := by
    intro hxGamma
    exact Finset.disjoint_left.mp hdisjoint hxGamma hxX

  have commonCircle (p : Finset α)
      (hp : p ∈ sixConicSignature cfg gamma e) :
      ∃ c : DeterminedCircle cfg,
        c ∈ sixConicPairCircles cfg gamma e ∧
        c ∈ sixConicPairCircles cfg gamma f ∧
        circleTrace cfg c.1 ∩ circleTrace cfg gamma.1 = p := by
    have hpF : p ∈ sixConicSignature cfg gamma f := by
      rw [← hsignature]
      exact hp
    rw [sixConicSignature] at hp hpF
    obtain ⟨c, hce, hcp⟩ := Finset.mem_image.mp hp
    obtain ⟨d, hdf, hdp⟩ := Finset.mem_image.mp hpF
    have hpCard : p.card = 2 := by
      rw [← hcp]
      exact sixConicPairCircle_gammaPair_card hce
    have hpSubC : p ⊆ circleTrace cfg c.1 := by
      rw [← hcp]
      exact Finset.inter_subset_left
    have hpSubD : p ⊆ circleTrace cfg d.1 := by
      rw [← hdp]
      exact Finset.inter_subset_left
    have hpSubGamma : p ⊆ circleTrace cfg gamma.1 := by
      rw [← hcp]
      exact Finset.inter_subset_right
    have hxNotP : x ∉ p := fun hxp => hxNotGamma (hpSubGamma hxp)
    have hsub : insert x p ⊆
        circleTrace cfg c.1 ∩ circleTrace cfg d.1 := by
      intro z hz
      rw [Finset.mem_inter]
      rcases Finset.mem_insert.mp hz with rfl | hzp
      · exact ⟨(mem_sixConicPairCircles.mp hce).1 hxe,
          (mem_sixConicPairCircles.mp hdf).1 hxf⟩
      · exact ⟨hpSubC hzp, hpSubD hzp⟩
    have hcardInsert : (insert x p).card = 3 := by
      simp [hxNotP, hpCard]
    have hcd : c = d := by
      by_contra hne
      have hinter :=
        (geometricBlockSystem cfg).distinct_block_inter_card_lt_three
          (b := (Sum.inr c : GeometricBlock cfg))
          (c := (Sum.inr d : GeometricBlock cfg)) (by
            intro h
            exact hne (Sum.inr.inj h))
      change (circleTrace cfg c.1 ∩ circleTrace cfg d.1).card < 3 at hinter
      have hle := Finset.card_le_card hsub
      omega
    subst d
    exact ⟨c, hce, hdf, hcp⟩

  obtain ⟨p, q, _r, hpq, _hpr, _hqr, hsignatureEq⟩ :=
    Finset.card_eq_three.mp hsignatureCard
  have hp : p ∈ sixConicSignature cfg gamma e := by
    rw [hsignatureEq]
    simp
  have hq : q ∈ sixConicSignature cfg gamma e := by
    rw [hsignatureEq]
    simp
  obtain ⟨c, hce, hcf, hcp⟩ := commonCircle p hp
  obtain ⟨d, hde, hdf, hdq⟩ := commonCircle q hq
  have hfNotSubE : ¬ f ⊆ e := by
    intro hfe
    apply hef
    exact (Finset.eq_of_subset_of_card_le hfe (by omega)).symm
  obtain ⟨y, hyf, hye⟩ := Finset.not_subset.mp hfNotSubE
  have hsub : insert y e ⊆
      circleTrace cfg c.1 ∩ circleTrace cfg d.1 := by
    intro z hz
    rw [Finset.mem_inter]
    rcases Finset.mem_insert.mp hz with rfl | hze
    · exact ⟨(mem_sixConicPairCircles.mp hcf).1 hyf,
        (mem_sixConicPairCircles.mp hdf).1 hyf⟩
    · exact ⟨(mem_sixConicPairCircles.mp hce).1 hze,
        (mem_sixConicPairCircles.mp hde).1 hze⟩
  have hcardInsert : (insert y e).card = 3 := by
    simp [hye, heCard]
  have hcd : c = d := by
    by_contra hne
    have hinter :=
      (geometricBlockSystem cfg).distinct_block_inter_card_lt_three
        (b := (Sum.inr c : GeometricBlock cfg))
        (c := (Sum.inr d : GeometricBlock cfg)) (by
          intro h
          exact hne (Sum.inr.inj h))
    change (circleTrace cfg c.1 ∩ circleTrace cfg d.1).card < 3 at hinter
    have hle := Finset.card_le_card hsub
    omega
  apply hpq
  calc
    p = circleTrace cfg c.1 ∩ circleTrace cfg gamma.1 := hcp.symm
    _ = circleTrace cfg d.1 ∩ circleTrace cfg gamma.1 := by rw [hcd]
    _ = q := hdq

/-- The two support edges of a repetition event are disjoint. -/
theorem sixConic_repetition_event_edges_disjoint
    {α : Type u} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (gamma : DeterminedCircle cfg)
    (hgamma : (circleTrace cfg gamma.1).card = 6)
    (X : Finset α) (hdisjoint : Disjoint (circleTrace cfg gamma.1) X)
    {E : Finset (Finset α)}
    (hE : E ∈ sixConicRepetitionEvents cfg gamma X)
    {e f : Finset α} (he : e ∈ E) (hf : f ∈ E) (hef : e ≠ f) :
    Disjoint e f := by
  have hEspec := mem_sixConicRepetitionEvents.mp hE
  have hEsub := (Finset.mem_powersetCard.mp hEspec.1).1
  exact sixConic_equal_full_signatures_disjoint
    cfg gamma hgamma X hdisjoint (hEsub he) (hEsub hf) hef
      (hEspec.2 e he f hf)

/-- The four endpoints of a repetition event determine at most one V1
geometric host.  Existence is projective input S2; uniqueness follows from
the matching conclusion and triple ownership. -/
theorem sixConic_repetition_host_unique
    {α : Type u} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (gamma : DeterminedCircle cfg)
    (hgamma : (circleTrace cfg gamma.1).card = 6)
    (X : Finset α) (hdisjoint : Disjoint (circleTrace cfg gamma.1) X)
    {E : Finset (Finset α)}
    (hE : E ∈ sixConicRepetitionEvents cfg gamma X)
    {H K : GeometricBlock cfg}
    (hH : SixConicEventHostedBy cfg E H)
    (hK : SixConicEventHostedBy cfg E K) : H = K := by
  classical
  have hEspec := mem_sixConicRepetitionEvents.mp hE
  have hEpow := Finset.mem_powersetCard.mp hEspec.1
  obtain ⟨e, f, hef, hEeq⟩ := Finset.card_eq_two.mp hEpow.2
  have heE : e ∈ E := by simp [hEeq]
  have hfE : f ∈ E := by simp [hEeq]
  have heFull := hEpow.1 heE
  have hfFull := hEpow.1 hfE
  have heCard := (Finset.mem_powersetCard.mp
    (mem_sixConicFullEdges.mp heFull).1).2
  have hfCard := (Finset.mem_powersetCard.mp
    (mem_sixConicFullEdges.mp hfFull).1).2
  have hefDisjoint := sixConic_repetition_event_edges_disjoint
    cfg gamma hgamma X hdisjoint hE heE hfE hef
  have hUnionCard : (e ∪ f).card = 4 := by
    rw [Finset.card_union_of_disjoint hefDisjoint, heCard, hfCard]
  have hsub : e ∪ f ⊆
      geometricBlockSupport cfg H ∩ geometricBlockSupport cfg K := by
    intro x hx
    rw [Finset.mem_inter]
    constructor
    · apply hH
      rcases Finset.mem_union.mp hx with hxe | hxf
      · exact Finset.mem_biUnion.mpr ⟨e, heE, hxe⟩
      · exact Finset.mem_biUnion.mpr ⟨f, hfE, hxf⟩
    · apply hK
      rcases Finset.mem_union.mp hx with hxe | hxf
      · exact Finset.mem_biUnion.mpr ⟨e, heE, hxe⟩
      · exact Finset.mem_biUnion.mpr ⟨f, hfE, hxf⟩
  by_contra hne
  have hinter :=
    (geometricBlockSystem cfg).distinct_block_inter_card_lt_three hne
  change (geometricBlockSupport cfg H ∩
    geometricBlockSupport cfg K).card < 3 at hinter
  have hle := Finset.card_le_card hsub
  omega

end Erdos506.Incidence
