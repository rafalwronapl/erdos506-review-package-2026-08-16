import Erdos506.V1.TenFiveTwoPentagonFactorization
import Erdos506.Finite.KFivePivotChord
import Erdos506.Finite.KFiveNearOneFactorizationRelabel
import Erdos506.Finite.KFiveGoldenRows

/-!
# Finite labels at the two-pentagon endpoint

This is the purely finite labelling layer of the golden-link endpoint.  It
selects a pivot on the first five-trace, uses the corresponding omitted
centre to normalize the second near-one-factorization, and then labels the
four remaining first-trace vertices by their pivot partners.
-/

namespace Erdos506.V1

open Erdos506.Finite
open Erdos506.Incidence
open Erdos506.V4

universe u

abbrev TenTwoPentagonFirstTrace
    {α : Type u} [Fintype α] [DecidableEq α]
    {cfg : Configuration α} (d : TenTwoPentagonSaturationData cfg) : Type u :=
  ↥(exclusiveCircleTrace cfg d.base.Γ d.base.Ω)

abbrev TenTwoPentagonSecondTrace
    {α : Type u} [Fintype α] [DecidableEq α]
    {cfg : Configuration α} (d : TenTwoPentagonSaturationData cfg) : Type u :=
  ↥(exclusiveCircleTrace cfg d.base.Ω d.base.Γ)

/-- The explicit identification of `Fin 4` with the nonzero elements of
`Fin 5`. -/
def finFourEquivNonzeroFinFive : Fin 4 ≃ {i : Fin 5 // i ≠ 0} where
  toFun i := ⟨i.succ, Fin.succ_ne_zero i⟩
  invFun i := i.1.pred i.2
  left_inv i := Fin.pred_succ i
  right_inv i := by
    apply Subtype.ext
    exact Fin.succ_pred i.1 i.2

namespace TenTwoPentagonSaturationData

variable {α : Type u} [Fintype α] [DecidableEq α]
  {cfg : Configuration α}

/-- An arbitrary but data-valued first five-trace label.  Its zero is the
pivot used below. -/
noncomputable def firstLabel
    (d : TenTwoPentagonSaturationData cfg) :
    Fin 5 ≃ TenTwoPentagonFirstTrace d :=
  (Finset.equivFinOfCardEq d.base.exclusiveTrace_Γ_Ω_card).symm

/-- The distinguished pivot on the first five-trace. -/
noncomputable def pivot
    (d : TenTwoPentagonSaturationData cfg) : TenTwoPentagonFirstTrace d :=
  d.firstLabel 0

/-- The common centre whose first factor omits the chosen pivot. -/
noncomputable def centerZero
    (d : TenTwoPentagonSaturationData cfg) : TenTwoPentagonCommonCenter d :=
  d.toNearOneFactorizationData.firstNearOneFactorization.omittedColourEquiv.symm
    d.pivot

@[simp] theorem first_omitted_centerZero
    (d : TenTwoPentagonSaturationData cfg) :
    d.toNearOneFactorizationData.firstNearOneFactorization.omittedColourEquiv
      d.centerZero = d.pivot := by
  simp [centerZero]

/-- An initial label of the second five-trace which puts the vertex omitted
by `centerZero` at zero. -/
noncomputable def secondInitialLabel
    (d : TenTwoPentagonSaturationData cfg) :
    Fin 5 ≃ TenTwoPentagonSecondTrace d :=
  finFiveVertexLabelWithZero d.base.exclusiveTrace_Ω_Γ_card
    (d.toNearOneFactorizationData.secondNearOneFactorization.omittedColourEquiv
      d.centerZero)

@[simp] theorem secondInitialLabel_zero
    (d : TenTwoPentagonSaturationData cfg) :
    d.secondInitialLabel 0 =
      d.toNearOneFactorizationData.secondNearOneFactorization.omittedColourEquiv
        d.centerZero := by
  exact finFiveVertexLabelWithZero_apply_zero _ _

/-- The canonical label of the second factorization, retaining its zero. -/
noncomputable def secondLabel
    (d : TenTwoPentagonSaturationData cfg) :
    Fin 5 ≃ TenTwoPentagonSecondTrace d :=
  d.toNearOneFactorizationData.secondNearOneFactorization.canonicalVertexLabel
    d.secondInitialLabel

@[simp] theorem secondLabel_zero
    (d : TenTwoPentagonSaturationData cfg) :
    d.secondLabel 0 =
      d.toNearOneFactorizationData.secondNearOneFactorization.omittedColourEquiv
        d.centerZero := by
  rw [secondLabel,
    KFiveNearOneFactorization.canonicalVertexLabel_zero]
  exact d.secondInitialLabel_zero

/-- The canonical factor family on the second trace. -/
@[simp] theorem secondLabel_pullbackFactorFamily
    (d : TenTwoPentagonSaturationData cfg) :
    d.toNearOneFactorizationData.secondNearOneFactorization.pullbackFactorFamily
      d.secondLabel = kFiveCanonicalFactorFamily := by
  exact KFiveNearOneFactorization.canonicalVertexLabel_factorFamily _ _

/-- Label common centres by the vertex they omit in the canonical second
factorization. -/
noncomputable def centerLabel
    (d : TenTwoPentagonSaturationData cfg) :
    Fin 5 ≃ TenTwoPentagonCommonCenter d :=
  d.secondLabel.trans
    d.toNearOneFactorizationData.secondNearOneFactorization.omittedColourEquiv.symm

/-- The common-centre labelling induced by the canonical second label. -/
theorem centerLabel_eq_colourLabel
    (d : TenTwoPentagonSaturationData cfg) :
    d.centerLabel =
      d.toNearOneFactorizationData.secondNearOneFactorization.colourLabel
        d.secondLabel := rfl

/-- The second factorization omits the second vertex carrying the same
finite label as a common centre. -/
@[simp] theorem second_omitted_centerLabel
    (d : TenTwoPentagonSaturationData cfg) (i : Fin 5) :
    d.toNearOneFactorizationData.secondNearOneFactorization.omittedColourEquiv
      (d.centerLabel i) = d.secondLabel i := by
  rw [d.centerLabel_eq_colourLabel]
  exact KFiveNearOneFactorization.omitted_colourLabel _ _ _

/-- The two explicit chords of golden row `i` belong to the second factor
indexed by the matching common centre. -/
theorem secondGoldenChord_mem_factor
    (d : TenTwoPentagonSaturationData cfg) (i : Fin 4) (j : Fin 2) :
    goldenLabelledChord d.secondLabel i j ∈
      d.toNearOneFactorizationData.secondNearOneFactorization.factor
        (d.centerLabel i.succ) := by
  rw [d.centerLabel_eq_colourLabel]
  exact goldenLabelledChord_mem_factor
    d.toNearOneFactorizationData.secondNearOneFactorization
      d.secondLabel d.secondLabel_pullbackFactorFamily i j

@[simp] theorem centerLabel_zero
    (d : TenTwoPentagonSaturationData cfg) :
    d.centerLabel 0 = d.centerZero := by
  apply d.toNearOneFactorizationData.secondNearOneFactorization.omittedColourEquiv.injective
  simp [centerLabel, d.secondLabel_zero]

/-- Label zero is exactly the common centre which omits the first pivot. -/
@[simp] theorem centerLabel_zero_omits_pivot
    (d : TenTwoPentagonSaturationData cfg) :
    d.toNearOneFactorizationData.firstNearOneFactorization.omittedColourEquiv
      (d.centerLabel 0) = d.pivot := by
  rw [d.centerLabel_zero]
  exact d.first_omitted_centerZero

private theorem centerLabel_succ_ne_centerZero
    (d : TenTwoPentagonSaturationData cfg) (i : Fin 4) :
    d.centerLabel i.succ ≠ d.centerZero := by
  intro h
  have hzero : d.centerLabel i.succ = d.centerLabel 0 := by
    rw [d.centerLabel_zero]
    exact h
  have : i.succ = 0 := d.centerLabel.injective hzero
  exact i.succ_ne_zero this

/-- A nonzero centre label does not omit the first pivot. -/
theorem pivot_ne_firstOmitted_centerLabel_succ
    (d : TenTwoPentagonSaturationData cfg) (i : Fin 4) :
    d.pivot ≠
      d.toNearOneFactorizationData.firstNearOneFactorization.omittedColourEquiv
        (d.centerLabel i.succ) := by
  intro h
  apply d.centerLabel_succ_ne_centerZero i
  apply (KFiveNearOneFactorization.omittedColourEquiv
    d.toNearOneFactorizationData.firstNearOneFactorization).injective
  rw [d.first_omitted_centerZero]
  exact h.symm

/-- The four nonzero centre labels, regarded as centres not omitting the
first pivot. -/
noncomputable def nonzeroCenterLabel
    (d : TenTwoPentagonSaturationData cfg) (i : Fin 4) :
    {c : TenTwoPentagonCommonCenter d //
      c ≠ (KFiveNearOneFactorization.omittedColourEquiv
        d.toNearOneFactorizationData.firstNearOneFactorization).symm d.pivot} :=
  ⟨d.centerLabel i.succ, by
    intro h
    apply d.pivot_ne_firstOmitted_centerLabel_succ i
    simpa using (congrArg
      (KFiveNearOneFactorization.omittedColourEquiv
        d.toNearOneFactorizationData.firstNearOneFactorization) h).symm⟩

/-- The four remaining first-trace vertices, labelled by the corresponding
nonzero common centres. -/
noncomputable def qLabel
    (d : TenTwoPentagonSaturationData cfg) :
    Fin 4 ≃ {x : TenTwoPentagonFirstTrace d // x ≠ d.pivot} := by
  let F := d.toNearOneFactorizationData.firstNearOneFactorization
  let f : Fin 4 → {x : TenTwoPentagonFirstTrace d // x ≠ d.pivot} := fun i =>
    F.pivotPartnerEquiv d.pivot (d.nonzeroCenterLabel i)
  have hinj : Function.Injective f := by
    intro i j hij
    have hcentres : d.nonzeroCenterLabel i = d.nonzeroCenterLabel j :=
      (F.pivotPartnerEquiv d.pivot).injective hij
    have hlabels : d.centerLabel i.succ = d.centerLabel j.succ :=
      congrArg Subtype.val hcentres
    have hsucc : i.succ = j.succ := d.centerLabel.injective hlabels
    exact Fin.succ_inj.mp hsucc
  have hfirstCard : Fintype.card (TenTwoPentagonFirstTrace d) = 5 := by
    simpa only [Fintype.card_coe] using d.base.exclusiveTrace_Γ_Ω_card
  have hcard : Fintype.card (Fin 4) =
      Fintype.card {x : TenTwoPentagonFirstTrace d // x ≠ d.pivot} := by
    simp [Fintype.card_subtype_compl, hfirstCard]
  exact Equiv.ofBijective f
    ((Fintype.bijective_iff_injective_and_card f).mpr ⟨hinj, hcard⟩)

@[simp] theorem qLabel_apply_val
    (d : TenTwoPentagonSaturationData cfg) (i : Fin 4) :
    (d.qLabel i).1 =
      d.toNearOneFactorizationData.firstNearOneFactorization.otherEndpoint
        (d.centerLabel i.succ) d.pivot
        (d.pivot_ne_firstOmitted_centerLabel_succ i) := by
  simp [qLabel, nonzeroCenterLabel,
    KFiveNearOneFactorization.pivotPartnerEquiv_apply_val]

@[simp] theorem qLabel_incidentChord_mem_factor
    (d : TenTwoPentagonSaturationData cfg) (i : Fin 4) :
    d.toNearOneFactorizationData.firstNearOneFactorization.incidentChord
        (d.centerLabel i.succ) d.pivot
        (d.pivot_ne_firstOmitted_centerLabel_succ i) ∈
      d.toNearOneFactorizationData.firstNearOneFactorization.factor
        (d.centerLabel i.succ) := by
  exact KFiveNearOneFactorization.incidentChord_mem_factor _ _ _ _

/-- The first golden chord through the pivot, paired with row `i`. -/
noncomputable def firstGoldenChord
    (d : TenTwoPentagonSaturationData cfg) (i : Fin 4) :
    KFiveChord (exclusiveCircleTrace cfg d.base.Γ d.base.Ω) :=
  d.toNearOneFactorizationData.firstNearOneFactorization.incidentChord
    (d.centerLabel i.succ) d.pivot (by
      intro h
      apply d.centerLabel_succ_ne_centerZero i
      apply (KFiveNearOneFactorization.omittedColourEquiv
        d.toNearOneFactorizationData.firstNearOneFactorization).injective
      simpa only [d.first_omitted_centerZero] using h.symm)

@[simp] theorem firstGoldenChord_mem_factor
    (d : TenTwoPentagonSaturationData cfg) (i : Fin 4) :
    d.firstGoldenChord i ∈
      d.toNearOneFactorizationData.firstNearOneFactorization.factor
        (d.centerLabel i.succ) :=
  d.qLabel_incidentChord_mem_factor i

@[simp] theorem qLabel_mem_firstGoldenChord
    (d : TenTwoPentagonSaturationData cfg) (i : Fin 4) :
    (d.qLabel i).1.1 ∈ (d.firstGoldenChord i).1 := by
  have h := KFiveNearOneFactorization.otherEndpoint_mem_incidentChord
    d.toNearOneFactorizationData.firstNearOneFactorization
      (d.centerLabel i.succ) d.pivot (by
        intro h
        apply d.centerLabel_succ_ne_centerZero i
        apply (KFiveNearOneFactorization.omittedColourEquiv
          d.toNearOneFactorizationData.firstNearOneFactorization).injective
        simpa only [d.first_omitted_centerZero] using h.symm)
  simpa only [firstGoldenChord, qLabel_apply_val] using h

/-- The selected first chord has precisely the pivot and its labelled partner
as endpoints.  This is the raw finite chord form used to supply the two
incidences in each golden-axis row. -/
@[simp] theorem firstGoldenChord_val_eq_pair
    (d : TenTwoPentagonSaturationData cfg) (i : Fin 4) :
    (d.firstGoldenChord i).1 = {d.pivot.1, (d.qLabel i).1.1} := by
  unfold firstGoldenChord
  simpa only [qLabel_apply_val] using
    (KFiveNearOneFactorization.incidentChord_val_eq_pair
      d.toNearOneFactorizationData.firstNearOneFactorization
      (d.centerLabel i.succ) d.pivot
      (d.pivot_ne_firstOmitted_centerLabel_succ i))

@[simp] theorem pivot_mem_qLabel_incidentChord
    (d : TenTwoPentagonSaturationData cfg) (i : Fin 4) :
    d.pivot.1 ∈
      (d.toNearOneFactorizationData.firstNearOneFactorization.incidentChord
        (d.centerLabel i.succ) d.pivot
        (d.pivot_ne_firstOmitted_centerLabel_succ i)).1 := by
  exact KFiveNearOneFactorization.vertex_mem_incidentChord _ _ _ _

@[simp] theorem pivot_mem_firstGoldenChord
    (d : TenTwoPentagonSaturationData cfg) (i : Fin 4) :
    d.pivot.1 ∈ (d.firstGoldenChord i).1 :=
  d.pivot_mem_qLabel_incidentChord i

end TenTwoPentagonSaturationData

end Erdos506.V1
