import Erdos506.Finite.KFiveNearOneFactorizationPartition
import Erdos506.Incidence.RadicalAxisFiveFiveFactorizationWitness

namespace Erdos506.Incidence

open Erdos506.Finite
open Erdos506.V1
open Erdos506.V4

namespace FiveFiveCrossBlockSaturationWitness

universe u

variable {α : Type u} [Fintype α] [DecidableEq α]
  {cfg : Configuration α}
  {Γ Ω : Erdos506.V1.DeterminedCircle cfg}

/-- The second saturated chord family, reindexed by common centres, is a
near-one-factorization of the second exclusive five-trace. -/
noncomputable def secondNearOneFactorization
    (d : FiveFiveCrossBlockSaturationWitness cfg Γ Ω) :
    KFiveNearOneFactorization
      (exclusiveCircleTrace cfg Ω Γ) (FiveFiveCommonCenter d) := by
  classical
  let f := firstExclusiveChordCenter cfg Γ Ω d.hne
  let g := secondExclusiveChordCenter cfg Γ Ω d.hne
  let A := exclusiveCircleTrace cfg Ω Γ
  let Colour := FiveFiveCommonCenter d
  have hColour : Fintype.card Colour = 5 := by
    rw [Fintype.card_coe]
    simpa only [fiveFiveCommonCenterSet] using d.saturation.profile.1
  have hfactorCard : ∀ q : Colour, (fullFibre g q.1).card = 2 := by
    intro q
    have hq : q.1 ∈ Finset.univ.image f := by
      change q.1 ∈ fiveFiveCommonCenterSet d at q.2
      simpa only [fiveFiveCommonCenterSet, f] using q.2
    exact (d.saturation.profile.2 q.1 hq).2
  have hmatching : ∀ q : Colour, ∀ e, e ∈ fullFibre g q.1 →
      ∀ k, k ∈ fullFibre g q.1 → e ≠ k → Disjoint e.1 k.1 := by
    intro q e he k hk hek
    apply secondExclusiveChords_disjoint_of_eq_center cfg Γ Ω d.hne e k hek
    exact ((mem_fullFibre g q.1 e).mp he).trans
      ((mem_fullFibre g q.1 k).mp hk).symm
  have hunique : ∀ e : KFiveChord A, ∃! q : Colour, e ∈ fullFibre g q.1 := by
    intro e
    have hge : g e ∈ Finset.univ.image f := by
      rw [← d.saturation.centreImages_eq]
      exact Finset.mem_image.mpr ⟨e, Finset.mem_univ e, rfl⟩
    let q : Colour :=
      ⟨g e, by
        change g e ∈ Finset.univ.image f
        exact hge⟩
    refine ⟨q, (mem_fullFibre g q.1 e).mpr rfl, ?_⟩
    intro r hr
    apply Subtype.ext
    exact ((mem_fullFibre g r.1 e).mp hr).symm
  exact KFiveNearOneFactorization.ofPartition A d.saturation.secondExclusiveCard
    (fun q : Colour => fullFibre g q.1) hColour hfactorCard hmatching hunique

@[simp] theorem secondNearOneFactorization_factor
    (d : FiveFiveCrossBlockSaturationWitness cfg Γ Ω)
    (q : FiveFiveCommonCenter d) :
    d.secondNearOneFactorization.factor q =
      fullFibre (secondExclusiveChordCenter cfg Γ Ω d.hne) q.1 := rfl

noncomputable def secondOmittedColourEquiv
    (d : FiveFiveCrossBlockSaturationWitness cfg Γ Ω) :
    FiveFiveCommonCenter d ≃ ↥(exclusiveCircleTrace cfg Ω Γ) :=
  d.secondNearOneFactorization.omittedColourEquiv

end FiveFiveCrossBlockSaturationWitness

end Erdos506.Incidence
