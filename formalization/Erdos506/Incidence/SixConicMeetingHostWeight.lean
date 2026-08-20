import Erdos506.Incidence.SixConicActiveSignatureCap
import Mathlib.Tactic

/-!
# Five outsiders on a host meeting the selected six-circle

A full outsider edge has a perfect-matching signature, so every selected
point belongs to one of its three marked pairs.  If a five-outsider host
meets the selected circle, choose a selected point on the host and the
marked pair containing it.  The host and the circle counted by that pair
share the selected point and both endpoints of the outsider edge.  Triple
ownership identifies the two geometric blocks.  That block would then
contain the five outsiders and the whole marked pair, hence at least seven
selected labels, contradicting the supplied block cap six.

Thus no outsider edge is full, every edge weight is at most two, and the
ten edges have total weight at most twenty.  No six-conic-events principle
field is used.
-/

namespace Erdos506.Incidence

open Erdos506.Finite
open Erdos506.V1
open Erdos506.V4
open scoped BigOperators

universe u

/-- Field-free replacement for
the five-outsider meeting-host weight bound,
under the block cap six available at its eleven-point consumer. -/
theorem sixConic_five_outsider_host_meeting_weight_le_of_blockCap
    {α : Type u} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (gamma : DeterminedCircle cfg)
    (hgamma : (circleTrace cfg gamma.1).card = 6)
    (X : Finset α) (hX : X.card = 5)
    (hdisjoint : Disjoint (circleTrace cfg gamma.1) X)
    (hblockCap : ∀ H : GeometricBlock cfg,
      (geometricBlockSupport cfg H).card ≤ 6) :
    HasFiveOutsiderHostMeeting cfg gamma X →
      sixConicWeight cfg gamma X ≤ 20 := by
  classical
  rintro ⟨H, hXH, hhostMeets⟩
  have hedgeWeight : ∀ e ∈ X.powersetCard 2,
      sixConicPairWeight cfg gamma e ≤ 2 := by
    intro e he
    have hePow := Finset.mem_powersetCard.mp he
    have heDisjointGamma : Disjoint e (circleTrace cfg gamma.1) :=
      hdisjoint.symm.mono_left hePow.1
    have hweightThree :=
      sixConicPairWeight_le_three hgamma hePow.2 heDisjointGamma
    by_contra hnotTwo
    have hfullWeight : sixConicPairWeight cfg gamma e = 3 := by
      omega
    have heFull : e ∈ sixConicFullEdges cfg gamma X :=
      mem_sixConicFullEdges.mpr ⟨he, hfullWeight⟩
    have hsignatureActive :
        sixConicSignature cfg gamma e ∈
          sixConicActiveSignatures cfg gamma X := by
      rw [sixConicActiveSignatures]
      exact Finset.mem_image.mpr ⟨e, heFull, rfl⟩
    have hmatching := sixConic_activeSignature_isPerfectMatching
      cfg gamma hgamma X hdisjoint hsignatureActive
    rw [Finset.disjoint_left] at hhostMeets
    push Not at hhostMeets
    obtain ⟨z, hzH, hzGamma⟩ := hhostMeets
    have hzUnion : z ∈ (sixConicSignature cfg gamma e).biUnion id := by
      rw [hmatching.covers]
      exact hzGamma
    obtain ⟨p, hpSignature, hzP⟩ :=
      Finset.mem_biUnion.mp hzUnion
    have hpData := hmatching.pair p hpSignature
    rw [sixConicSignature] at hpSignature
    obtain ⟨c, hcPairCircle, hcPair⟩ :=
      Finset.mem_image.mp hpSignature
    have heC : e ⊆ circleTrace cfg c.1 :=
      (mem_sixConicPairCircles.mp hcPairCircle).1
    have hpC : p ⊆ circleTrace cfg c.1 := by
      intro a ha
      have haInter :
          a ∈ circleTrace cfg c.1 ∩ circleTrace cfg gamma.1 := by
        rw [hcPair]
        exact ha
      exact (Finset.mem_inter.mp haInter).1
    have hzC : z ∈ circleTrace cfg c.1 := hpC hzP
    have hzNotE : z ∉ e := by
      intro hzE
      exact Finset.disjoint_left.mp hdisjoint hzGamma (hePow.1 hzE)
    let T : KSubset α 3 := ⟨insert z e, by
      simp [hzNotE, hePow.2]⟩
    have hTH : T.1 ⊆ geometricBlockSupport cfg H := by
      intro a ha
      change a ∈ insert z e at ha
      rcases Finset.mem_insert.mp ha with rfl | haE
      · exact hzH
      · exact hXH (hePow.1 haE)
    have hTc : T.1 ⊆
        geometricBlockSupport cfg (Sum.inr c : GeometricBlock cfg) := by
      intro a ha
      change a ∈ insert z e at ha
      change a ∈ circleTrace cfg c.1
      rcases Finset.mem_insert.mp ha with rfl | haE
      · exact hzC
      · exact heC haE
    have hHowner := geometricTripleOwner_unique cfg T H hTH
    have hcOwner := geometricTripleOwner_unique cfg T
      (Sum.inr c : GeometricBlock cfg) hTc
    have hHc : H = (Sum.inr c : GeometricBlock cfg) :=
      hHowner.trans hcOwner.symm
    have hpH : p ⊆ geometricBlockSupport cfg H := by
      rw [hHc]
      exact hpC
    have hXpDisjoint : Disjoint X p := by
      rw [Finset.disjoint_left]
      intro a haX haP
      exact Finset.disjoint_left.mp hdisjoint (hpData.2 haP) haX
    have hXpCard : (X ∪ p).card = 7 := by
      rw [Finset.card_union_of_disjoint hXpDisjoint, hX, hpData.1]
    have hXpSub : X ∪ p ⊆ geometricBlockSupport cfg H := by
      intro a ha
      rcases Finset.mem_union.mp ha with haX | haP
      · exact hXH haX
      · exact hpH haP
    have hseven : 7 ≤ (geometricBlockSupport cfg H).card := by
      rw [← hXpCard]
      exact Finset.card_le_card hXpSub
    have hsix := hblockCap H
    omega
  have hsum := Finset.sum_le_sum hedgeWeight
  change sixConicTotalWeight cfg gamma X ≤ _ at hsum
  rw [sixConicTotalWeight_eq_sixConicWeight] at hsum
  have hpairCard : (X.powersetCard 2).card = 10 := by
    rw [Finset.card_powersetCard, hX]
    norm_num [Nat.choose]
  simp only [Finset.sum_const, nsmul_eq_mul] at hsum
  rw [hpairCard] at hsum
  omega

end Erdos506.Incidence
