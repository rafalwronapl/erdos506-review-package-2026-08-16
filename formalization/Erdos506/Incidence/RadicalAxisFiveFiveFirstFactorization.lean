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

/-- The first saturated chord family, indexed by common centres, is a
near-one-factorization of the first exclusive five-trace. -/
noncomputable def firstNearOneFactorization
    (d : FiveFiveCrossBlockSaturationWitness cfg Γ Ω) :
    KFiveNearOneFactorization
      (exclusiveCircleTrace cfg Γ Ω) (FiveFiveCommonCenter d) := by
  classical
  let f := firstExclusiveChordCenter cfg Γ Ω d.hne
  let A := exclusiveCircleTrace cfg Γ Ω
  let Colour := FiveFiveCommonCenter d
  have hColour : Fintype.card Colour = 5 := by
    rw [Fintype.card_coe]
    simpa only [fiveFiveCommonCenterSet] using d.saturation.profile.1
  have hfactorCard : ∀ q : Colour, (fullFibre f q.1).card = 2 := by
    intro q
    have hq : q.1 ∈ Finset.univ.image f := by
      change q.1 ∈ fiveFiveCommonCenterSet d at q.2
      simpa only [fiveFiveCommonCenterSet, f] using q.2
    exact (d.saturation.profile.2 q.1 hq).1
  have hmatching : ∀ q : Colour, ∀ e, e ∈ fullFibre f q.1 →
      ∀ k, k ∈ fullFibre f q.1 → e ≠ k → Disjoint e.1 k.1 := by
    intro q e he k hk hek
    apply firstExclusiveChords_disjoint_of_eq_center cfg Γ Ω d.hne e k hek
    exact ((mem_fullFibre f q.1 e).mp he).trans
      ((mem_fullFibre f q.1 k).mp hk).symm
  have hunique : ∀ e : KFiveChord A, ∃! q : Colour, e ∈ fullFibre f q.1 := by
    intro e
    let q : Colour :=
      ⟨f e, by
        change f e ∈ Finset.univ.image f
        exact Finset.mem_image.mpr ⟨e, Finset.mem_univ e, rfl⟩⟩
    refine ⟨q, (mem_fullFibre f q.1 e).mpr rfl, ?_⟩
    intro r hr
    apply Subtype.ext
    exact ((mem_fullFibre f r.1 e).mp hr).symm
  exact KFiveNearOneFactorization.ofPartition A d.saturation.firstExclusiveCard
    (fun q : Colour => fullFibre f q.1) hColour hfactorCard hmatching hunique

@[simp] theorem firstNearOneFactorization_factor
    (d : FiveFiveCrossBlockSaturationWitness cfg Γ Ω)
    (q : FiveFiveCommonCenter d) :
    d.firstNearOneFactorization.factor q =
      fullFibre (firstExclusiveChordCenter cfg Γ Ω d.hne) q.1 := rfl

noncomputable def firstOmittedColourEquiv
    (d : FiveFiveCrossBlockSaturationWitness cfg Γ Ω) :
    FiveFiveCommonCenter d ≃ ↥(exclusiveCircleTrace cfg Γ Ω) :=
  d.firstNearOneFactorization.omittedColourEquiv

end FiveFiveCrossBlockSaturationWitness

end Erdos506.Incidence
