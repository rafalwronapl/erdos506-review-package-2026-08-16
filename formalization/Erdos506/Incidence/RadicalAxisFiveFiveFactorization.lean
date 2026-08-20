import Erdos506.Incidence.RadicalAxisFiveFiveFirstFactorization
import Erdos506.Incidence.RadicalAxisFiveFiveSecondFactorization

/-!
# Paired K5 near-one-factorizations at the five-by-five endpoint

The witness and the two independent factorization constructions are kept in
small layers.  This final adapter exposes their paired public package.
-/

namespace Erdos506.Incidence

open Erdos506.Finite
open Erdos506.V1
open Erdos506.V4

universe u

/-- The two near-one-factorizations at a saturated five-by-five endpoint,
with one literal common centre type. -/
structure FiveFiveNearOneFactorizationData
    {α : Type u} [Fintype α] [DecidableEq α]
    {cfg : Configuration α}
    {Γ Ω : Erdos506.V1.DeterminedCircle cfg}
    (d : FiveFiveCrossBlockSaturationWitness cfg Γ Ω) where
  commonCenterEquiv : FiveFiveSecondCenter d ≃ FiveFiveCommonCenter d
  commonCenterEquiv_val : ∀ q, (commonCenterEquiv q).1 = q.1
  firstNearOneFactorization :
    KFiveNearOneFactorization
      (exclusiveCircleTrace cfg Γ Ω) (FiveFiveCommonCenter d)
  secondNearOneFactorization :
    KFiveNearOneFactorization
      (exclusiveCircleTrace cfg Ω Γ) (FiveFiveCommonCenter d)

attribute [simp] FiveFiveNearOneFactorizationData.commonCenterEquiv_val

namespace FiveFiveCrossBlockSaturationWitness

variable {α : Type u} [Fintype α] [DecidableEq α]
  {cfg : Configuration α}
  {Γ Ω : Erdos506.V1.DeterminedCircle cfg}

/-- Package both factor families and the identity-on-values common-centre
transport supplied by saturated five-by-five data. -/
noncomputable def toNearOneFactorizationData
    (d : FiveFiveCrossBlockSaturationWitness cfg Γ Ω) :
    FiveFiveNearOneFactorizationData d where
  commonCenterEquiv := d.commonCenterEquiv
  commonCenterEquiv_val := d.commonCenterEquiv_val
  firstNearOneFactorization := d.firstNearOneFactorization
  secondNearOneFactorization := d.secondNearOneFactorization

@[simp] theorem toNearOneFactorizationData_first
    (d : FiveFiveCrossBlockSaturationWitness cfg Γ Ω) :
    d.toNearOneFactorizationData.firstNearOneFactorization =
      d.firstNearOneFactorization := rfl

@[simp] theorem toNearOneFactorizationData_second
    (d : FiveFiveCrossBlockSaturationWitness cfg Γ Ω) :
    d.toNearOneFactorizationData.secondNearOneFactorization =
      d.secondNearOneFactorization := rfl

end FiveFiveCrossBlockSaturationWitness

end Erdos506.Incidence
