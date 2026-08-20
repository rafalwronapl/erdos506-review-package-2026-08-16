import Erdos506.Incidence.RadicalAxisFiveFiveGeometry

/-!
# Shared witness and centre types for five-by-five factorization

This lightweight layer keeps the proof that the two circles are distinct
inside the saturated endpoint package.  Factorization constructors therefore
depend on one data argument rather than on a separate inequality binder.
-/

namespace Erdos506.Incidence

open Erdos506.Finite
open Erdos506.V1
open Erdos506.V4

universe u

/-- A five-by-five saturation package with its circle-inequality witness. -/
structure FiveFiveCrossBlockSaturationWitness
    {α : Type u} [Fintype α] [DecidableEq α]
    (cfg : Configuration α)
    (Γ Ω : Erdos506.V1.DeterminedCircle cfg) where
  hne : Γ ≠ Ω
  saturation : FiveFiveCrossBlockSaturationData cfg Γ Ω hne

/-- The image of the first exclusive-chord centre map. -/
noncomputable def fiveFiveFirstCenterSet
    {α : Type u} [Fintype α] [DecidableEq α]
    {cfg : Configuration α}
    {Γ Ω : Erdos506.V1.DeterminedCircle cfg}
    (d : FiveFiveCrossBlockSaturationWitness cfg Γ Ω) :
    Finset RealProjectivePlane := by
  classical
  exact
    (Finset.univ :
      Finset (CircleChord (exclusiveCircleTrace cfg Γ Ω))).image
        (firstExclusiveChordCenter cfg Γ Ω d.hne)

/-- The image of the second exclusive-chord centre map. -/
noncomputable def fiveFiveSecondCenterSet
    {α : Type u} [Fintype α] [DecidableEq α]
    {cfg : Configuration α}
    {Γ Ω : Erdos506.V1.DeterminedCircle cfg}
    (d : FiveFiveCrossBlockSaturationWitness cfg Γ Ω) :
    Finset RealProjectivePlane := by
  classical
  exact
    (Finset.univ :
      Finset (CircleChord (exclusiveCircleTrace cfg Ω Γ))).image
        (secondExclusiveChordCenter cfg Γ Ω d.hne)

/-- The common centre set is the first centre image. -/
noncomputable abbrev fiveFiveCommonCenterSet
    {α : Type u} [Fintype α] [DecidableEq α]
    {cfg : Configuration α}
    {Γ Ω : Erdos506.V1.DeterminedCircle cfg}
    (d : FiveFiveCrossBlockSaturationWitness cfg Γ Ω) :
    Finset RealProjectivePlane :=
  fiveFiveFirstCenterSet d

abbrev FiveFiveCommonCenter
    {α : Type u} [Fintype α] [DecidableEq α]
    {cfg : Configuration α}
    {Γ Ω : Erdos506.V1.DeterminedCircle cfg}
    (d : FiveFiveCrossBlockSaturationWitness cfg Γ Ω) : Type :=
  ↥(fiveFiveCommonCenterSet d)

abbrev FiveFiveSecondCenter
    {α : Type u} [Fintype α] [DecidableEq α]
    {cfg : Configuration α}
    {Γ Ω : Erdos506.V1.DeterminedCircle cfg}
    (d : FiveFiveCrossBlockSaturationWitness cfg Γ Ω) : Type :=
  ↥(fiveFiveSecondCenterSet d)

noncomputable instance instDecidableEqFiveFiveCommonCenter
    {α : Type u} [Fintype α] [DecidableEq α]
    {cfg : Configuration α}
    {Γ Ω : Erdos506.V1.DeterminedCircle cfg}
    (d : FiveFiveCrossBlockSaturationWitness cfg Γ Ω) :
    DecidableEq (FiveFiveCommonCenter d) :=
  Classical.decEq _

namespace FiveFiveCrossBlockSaturationWitness

variable {α : Type u} [Fintype α] [DecidableEq α]
  {cfg : Configuration α}
  {Γ Ω : Erdos506.V1.DeterminedCircle cfg}

/-- The identity-on-centres equivalence from the second image to the common
centre type chosen from the first image. -/
noncomputable def commonCenterEquiv
    (d : FiveFiveCrossBlockSaturationWitness cfg Γ Ω) :
    FiveFiveSecondCenter d ≃ FiveFiveCommonCenter d where
  toFun q := by
    classical
    refine ⟨q.1, ?_⟩
    change q.1 ∈ fiveFiveFirstCenterSet d
    simp only [fiveFiveFirstCenterSet]
    rw [← d.saturation.centreImages_eq]
    change q.1 ∈ fiveFiveSecondCenterSet d at q.2
    simpa only [fiveFiveSecondCenterSet] using q.2
  invFun q := by
    classical
    refine ⟨q.1, ?_⟩
    change q.1 ∈ fiveFiveSecondCenterSet d
    simp only [fiveFiveSecondCenterSet]
    rw [d.saturation.centreImages_eq]
    change q.1 ∈ fiveFiveCommonCenterSet d at q.2
    simpa only [fiveFiveCommonCenterSet] using q.2
  left_inv q := Subtype.ext rfl
  right_inv q := Subtype.ext rfl

@[simp] theorem commonCenterEquiv_val
    (d : FiveFiveCrossBlockSaturationWitness cfg Γ Ω)
    (q : FiveFiveSecondCenter d) :
    (d.commonCenterEquiv q).1 = q.1 := rfl

end FiveFiveCrossBlockSaturationWitness

end Erdos506.Incidence
