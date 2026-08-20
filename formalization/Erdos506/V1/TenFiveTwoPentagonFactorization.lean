import Erdos506.Finite.KFiveNearOneFactorizationPartition
import Erdos506.V1.TenFiveTwoPentagonSaturation

/-!
# K5 near-one-factorizations at the ten-point two-pentagon endpoint

The endpoint saturation data already contains the two base circles, their
inequality proof, and the saturated five-by-five centre profile.  This module
uses that one package to construct the two associated `K5`
near-one-factorizations with a literal common centre type.
-/

namespace Erdos506.V1

open Erdos506.Finite
open Erdos506.Incidence
open Erdos506.V4

universe u

/-! ## Common centre type -/

/-- The image of the first exclusive-chord centre map at the saturated
two-pentagon endpoint. -/
noncomputable def tenTwoPentagonFirstCenterSet
    {α : Type u} [Fintype α] [DecidableEq α]
    {cfg : Configuration α}
    (d : TenTwoPentagonSaturationData cfg) :
    Finset RealProjectivePlane := by
  classical
  exact
    (Finset.univ :
      Finset (CircleChord (exclusiveCircleTrace cfg d.base.Γ d.base.Ω))).image
        (firstExclusiveChordCenter cfg d.base.Γ d.base.Ω d.base.circles_ne)

/-- The image of the second exclusive-chord centre map at the saturated
two-pentagon endpoint. -/
noncomputable def tenTwoPentagonSecondCenterSet
    {α : Type u} [Fintype α] [DecidableEq α]
    {cfg : Configuration α}
    (d : TenTwoPentagonSaturationData cfg) :
    Finset RealProjectivePlane := by
  classical
  exact
    (Finset.univ :
      Finset (CircleChord (exclusiveCircleTrace cfg d.base.Ω d.base.Γ))).image
        (secondExclusiveChordCenter cfg d.base.Γ d.base.Ω d.base.circles_ne)

/-- The common centre set is chosen to be the first centre image. -/
noncomputable abbrev tenTwoPentagonCommonCenterSet
    {α : Type u} [Fintype α] [DecidableEq α]
    {cfg : Configuration α}
    (d : TenTwoPentagonSaturationData cfg) :
    Finset RealProjectivePlane :=
  tenTwoPentagonFirstCenterSet d

abbrev TenTwoPentagonCommonCenter
    {α : Type u} [Fintype α] [DecidableEq α]
    {cfg : Configuration α}
    (d : TenTwoPentagonSaturationData cfg) : Type :=
  ↥(tenTwoPentagonCommonCenterSet d)

abbrev TenTwoPentagonSecondCenter
    {α : Type u} [Fintype α] [DecidableEq α]
    {cfg : Configuration α}
    (d : TenTwoPentagonSaturationData cfg) : Type :=
  ↥(tenTwoPentagonSecondCenterSet d)

noncomputable instance instDecidableEqTenTwoPentagonCommonCenter
    {α : Type u} [Fintype α] [DecidableEq α]
    {cfg : Configuration α}
    (d : TenTwoPentagonSaturationData cfg) :
    DecidableEq (TenTwoPentagonCommonCenter d) :=
  Classical.decEq _

namespace TenTwoPentagonSaturationData

variable {α : Type u} [Fintype α] [DecidableEq α]
  {cfg : Configuration α}

/-- The value-preserving equivalence from the second centre image to the
common centre type. -/
noncomputable def commonCenterEquiv
    (d : TenTwoPentagonSaturationData cfg) :
    TenTwoPentagonSecondCenter d ≃ TenTwoPentagonCommonCenter d where
  toFun q := by
    classical
    refine ⟨q.1, ?_⟩
    change q.1 ∈ tenTwoPentagonFirstCenterSet d
    simp only [tenTwoPentagonFirstCenterSet]
    rw [← d.fiveFive.centreImages_eq]
    have hq := q.property
    change q.1 ∈ tenTwoPentagonSecondCenterSet d at hq
    simpa only [tenTwoPentagonSecondCenterSet] using hq
  invFun q := by
    classical
    refine ⟨q.1, ?_⟩
    change q.1 ∈ tenTwoPentagonSecondCenterSet d
    simp only [tenTwoPentagonSecondCenterSet]
    rw [d.fiveFive.centreImages_eq]
    have hq := q.property
    change q.1 ∈ tenTwoPentagonCommonCenterSet d at hq
    simpa only [tenTwoPentagonCommonCenterSet] using hq
  left_inv q := Subtype.ext rfl
  right_inv q := Subtype.ext rfl

/-! ## The two factor families -/

/-- The first saturated chord family is a near-one-factorization of the
first exclusive five-trace. -/
noncomputable def firstNearOneFactorization
    (d : TenTwoPentagonSaturationData cfg) :
    KFiveNearOneFactorization
      (exclusiveCircleTrace cfg d.base.Γ d.base.Ω)
      (TenTwoPentagonCommonCenter d) := by
  classical
  let f := firstExclusiveChordCenter cfg d.base.Γ d.base.Ω d.base.circles_ne
  let A := exclusiveCircleTrace cfg d.base.Γ d.base.Ω
  let Colour := TenTwoPentagonCommonCenter d
  have hColour : Fintype.card Colour = 5 := by
    rw [Fintype.card_coe]
    simpa only [tenTwoPentagonCommonCenterSet] using d.fiveFive.profile.1
  have hfactorCard : ∀ q : Colour, (fullFibre f q.1).card = 2 := by
    intro q
    have hq : q.1 ∈ Finset.univ.image f := by
      have hq' := q.property
      change q.1 ∈ tenTwoPentagonCommonCenterSet d at hq'
      simpa only [tenTwoPentagonCommonCenterSet, f] using hq'
    exact (d.fiveFive.profile.2 q.1 hq).1
  have hmatching : ∀ q : Colour, ∀ e, e ∈ fullFibre f q.1 →
      ∀ k, k ∈ fullFibre f q.1 → e ≠ k → Disjoint e.1 k.1 := by
    intro q e he k hk hek
    apply firstExclusiveChords_disjoint_of_eq_center
      cfg d.base.Γ d.base.Ω d.base.circles_ne e k hek
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
  exact KFiveNearOneFactorization.ofPartition A d.fiveFive.firstExclusiveCard
    (fun q : Colour => fullFibre f q.1) hColour hfactorCard hmatching hunique

@[simp] theorem firstNearOneFactorization_factor
    (d : TenTwoPentagonSaturationData cfg)
    (q : TenTwoPentagonCommonCenter d) :
    d.firstNearOneFactorization.factor q =
      fullFibre
        (firstExclusiveChordCenter cfg d.base.Γ d.base.Ω d.base.circles_ne) q.1 :=
  rfl

/-- The first centre-to-omitted-vertex bijection. -/
noncomputable def firstOmittedColourEquiv
    (d : TenTwoPentagonSaturationData cfg) :
    TenTwoPentagonCommonCenter d ≃
      ↥(exclusiveCircleTrace cfg d.base.Γ d.base.Ω) :=
  d.firstNearOneFactorization.omittedColourEquiv

/-- The second saturated chord family, reindexed by the common centres, is a
near-one-factorization of the second exclusive five-trace. -/
noncomputable def secondNearOneFactorization
    (d : TenTwoPentagonSaturationData cfg) :
    KFiveNearOneFactorization
      (exclusiveCircleTrace cfg d.base.Ω d.base.Γ)
      (TenTwoPentagonCommonCenter d) := by
  classical
  let f := firstExclusiveChordCenter cfg d.base.Γ d.base.Ω d.base.circles_ne
  let g := secondExclusiveChordCenter cfg d.base.Γ d.base.Ω d.base.circles_ne
  let A := exclusiveCircleTrace cfg d.base.Ω d.base.Γ
  let Colour := TenTwoPentagonCommonCenter d
  have hColour : Fintype.card Colour = 5 := by
    rw [Fintype.card_coe]
    simpa only [tenTwoPentagonCommonCenterSet] using d.fiveFive.profile.1
  have hfactorCard : ∀ q : Colour, (fullFibre g q.1).card = 2 := by
    intro q
    have hq : q.1 ∈ Finset.univ.image f := by
      have hq' := q.property
      change q.1 ∈ tenTwoPentagonCommonCenterSet d at hq'
      simpa only [tenTwoPentagonCommonCenterSet, f] using hq'
    exact (d.fiveFive.profile.2 q.1 hq).2
  have hmatching : ∀ q : Colour, ∀ e, e ∈ fullFibre g q.1 →
      ∀ k, k ∈ fullFibre g q.1 → e ≠ k → Disjoint e.1 k.1 := by
    intro q e he k hk hek
    apply secondExclusiveChords_disjoint_of_eq_center
      cfg d.base.Γ d.base.Ω d.base.circles_ne e k hek
    exact ((mem_fullFibre g q.1 e).mp he).trans
      ((mem_fullFibre g q.1 k).mp hk).symm
  have hunique : ∀ e : KFiveChord A, ∃! q : Colour, e ∈ fullFibre g q.1 := by
    intro e
    have hge : g e ∈ Finset.univ.image f := by
      rw [← d.fiveFive.centreImages_eq]
      exact Finset.mem_image.mpr ⟨e, Finset.mem_univ e, rfl⟩
    let q : Colour :=
      ⟨g e, by
        change g e ∈ Finset.univ.image f
        exact hge⟩
    refine ⟨q, (mem_fullFibre g q.1 e).mpr rfl, ?_⟩
    intro r hr
    apply Subtype.ext
    exact ((mem_fullFibre g r.1 e).mp hr).symm
  exact KFiveNearOneFactorization.ofPartition A d.fiveFive.secondExclusiveCard
    (fun q : Colour => fullFibre g q.1) hColour hfactorCard hmatching hunique

@[simp] theorem secondNearOneFactorization_factor
    (d : TenTwoPentagonSaturationData cfg)
    (q : TenTwoPentagonCommonCenter d) :
    d.secondNearOneFactorization.factor q =
      fullFibre
        (secondExclusiveChordCenter cfg d.base.Γ d.base.Ω d.base.circles_ne) q.1 :=
  rfl

/-- The second centre-to-omitted-vertex bijection. -/
noncomputable def secondOmittedColourEquiv
    (d : TenTwoPentagonSaturationData cfg) :
    TenTwoPentagonCommonCenter d ≃
      ↥(exclusiveCircleTrace cfg d.base.Ω d.base.Γ) :=
  d.secondNearOneFactorization.omittedColourEquiv

/-! ## Paired public adapter -/

/-- The two K5 near-one-factorizations at the saturated two-pentagon
endpoint, indexed by their common centre type. -/
structure TenTwoPentagonNearOneFactorizationData
    (d : TenTwoPentagonSaturationData cfg) where
  commonCenterEquiv :
    TenTwoPentagonSecondCenter d ≃ TenTwoPentagonCommonCenter d
  firstNearOneFactorization :
    KFiveNearOneFactorization
      (exclusiveCircleTrace cfg d.base.Γ d.base.Ω)
      (TenTwoPentagonCommonCenter d)
  secondNearOneFactorization :
    KFiveNearOneFactorization
      (exclusiveCircleTrace cfg d.base.Ω d.base.Γ)
      (TenTwoPentagonCommonCenter d)

/-- Package both K5 factor families and their common-centre transport. -/
noncomputable def toNearOneFactorizationData
    (d : TenTwoPentagonSaturationData cfg) :
    TenTwoPentagonNearOneFactorizationData d where
  commonCenterEquiv := TenTwoPentagonSaturationData.commonCenterEquiv d
  firstNearOneFactorization :=
    TenTwoPentagonSaturationData.firstNearOneFactorization d
  secondNearOneFactorization :=
    TenTwoPentagonSaturationData.secondNearOneFactorization d

end TenTwoPentagonSaturationData

end Erdos506.V1
