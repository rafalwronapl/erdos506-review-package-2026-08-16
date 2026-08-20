import Erdos506.Finite.FourPentagonLedgerResidualCap

/-!
# The residual equality classifier in the four-pentagon ledger

At cardinality seven, the residual colouring is a bijection.  The unique
candidate of colour six fixes one anchor, which in turn fixes the colour-zero
anchor.  Compatibility with those two anchors forces every remaining member
to lie in the canonical residual equality family.
-/

namespace Erdos506.Finite

private def residualAnchorZero : Finset (Fin 10) := {2, 3, 4, 6}

private def residualAnchorSix : Finset (Fin 10) := {4, 5, 6, 7}

private theorem residual_color_six_bad_candidates_empty :
    fourPentagonResidualCandidates.filter (fun Q =>
      fourPentagonResidualColor Q = 6 ∧ Q ≠ residualAnchorSix) = ∅ := by
  decide +kernel

private theorem residual_color_six_eq_anchor
    {Q : Finset (Fin 10)}
    (hQ : Q ∈ fourPentagonResidualCandidates)
    (hcolor : fourPentagonResidualColor Q = 6) :
    Q = residualAnchorSix := by
  by_contra hne
  have hbad : Q ∈ fourPentagonResidualCandidates.filter (fun R =>
      fourPentagonResidualColor R = 6 ∧ R ≠ residualAnchorSix) :=
    Finset.mem_filter.mpr ⟨hQ, hcolor, hne⟩
  rw [residual_color_six_bad_candidates_empty] at hbad
  simp at hbad

private theorem residual_color_zero_anchor_bad_candidates_empty :
    fourPentagonResidualCandidates.filter (fun Q =>
      fourPentagonResidualColor Q = 0 ∧
        (Q ∩ residualAnchorSix).card ≤ 2 ∧
        Q ≠ residualAnchorZero) = ∅ := by
  decide +kernel

private theorem residual_color_zero_eq_anchor
    {Q : Finset (Fin 10)}
    (hQ : Q ∈ fourPentagonResidualCandidates)
    (hcolor : fourPentagonResidualColor Q = 0)
    (hcapSix : (Q ∩ residualAnchorSix).card ≤ 2) :
    Q = residualAnchorZero := by
  by_contra hne
  have hbad : Q ∈ fourPentagonResidualCandidates.filter (fun R =>
      fourPentagonResidualColor R = 0 ∧
        (R ∩ residualAnchorSix).card ≤ 2 ∧
        R ≠ residualAnchorZero) :=
    Finset.mem_filter.mpr ⟨hQ, hcolor, hcapSix, hne⟩
  rw [residual_color_zero_anchor_bad_candidates_empty] at hbad
  simp at hbad

private theorem residual_anchor_compatible_bad_candidates_empty :
    fourPentagonResidualCandidates.filter (fun Q =>
      (Q ∩ residualAnchorSix).card ≤ 2 ∧
        (Q ∩ residualAnchorZero).card ≤ 2 ∧
        Q ∉ fourPentagonResidualEquality) = ∅ := by
  decide +kernel

private theorem residual_mem_equality_of_anchor_compatible
    {Q : Finset (Fin 10)}
    (hQ : Q ∈ fourPentagonResidualCandidates)
    (hcapSix : (Q ∩ residualAnchorSix).card ≤ 2)
    (hcapZero : (Q ∩ residualAnchorZero).card ≤ 2) :
    Q ∈ fourPentagonResidualEquality := by
  by_contra hnot
  have hbad : Q ∈ fourPentagonResidualCandidates.filter (fun R =>
      (R ∩ residualAnchorSix).card ≤ 2 ∧
        (R ∩ residualAnchorZero).card ≤ 2 ∧
        R ∉ fourPentagonResidualEquality) :=
    Finset.mem_filter.mpr ⟨hQ, hcapSix, hcapZero, hnot⟩
  rw [residual_anchor_compatible_bad_candidates_empty] at hbad
  simp at hbad

private theorem residualAnchorZero_mem_equality :
    residualAnchorZero ∈ fourPentagonResidualEquality := by
  decide

private theorem residualAnchorSix_mem_equality :
    residualAnchorSix ∈ fourPentagonResidualEquality := by
  decide

private theorem residualEquality_card :
    fourPentagonResidualEquality.card = 7 := by
  decide

/-- A compatible residual family attaining the seven-element cap is exactly
the canonical residual equality family. -/
theorem residual_eq_of_card_eq_seven
    (H : Finset (Finset (Fin 10)))
    (hH : H ⊆ fourPentagonResidualCandidates)
    (hcompat : fourPentagonCompatible H)
    (hcard : H.card = 7) : H = fourPentagonResidualEquality := by
  let color : {Q : Finset (Fin 10) // Q ∈ H} → Fin 7 :=
    fun Q => fourPentagonResidualColor Q.1
  have hcolorInj : Function.Injective color := by
    intro Q R hcolor
    apply Subtype.ext
    by_contra hQR
    change fourPentagonResidualColor Q.1 =
      fourPentagonResidualColor R.1 at hcolor
    have hlow := residual_same_color_conflict
      (hH Q.2) (hH R.2) hQR hcolor
    have hupp := hcompat Q.1 Q.2 R.1 R.2 hQR
    omega
  have hcardColor :
      Fintype.card {Q : Finset (Fin 10) // Q ∈ H} =
        Fintype.card (Fin 7) := by
    rw [Fintype.card_coe, hcard, Fintype.card_fin]
  have hcolorSurj : Function.Surjective color :=
    ((Fintype.bijective_iff_injective_and_card color).mpr
      ⟨hcolorInj, hcardColor⟩).2
  obtain ⟨Qsix, hQsixColor⟩ := hcolorSurj (6 : Fin 7)
  change fourPentagonResidualColor Qsix.1 = 6 at hQsixColor
  have hQsixAnchor : Qsix.1 = residualAnchorSix :=
    residual_color_six_eq_anchor (hH Qsix.2) hQsixColor
  obtain ⟨Qzero, hQzeroColor⟩ := hcolorSurj (0 : Fin 7)
  change fourPentagonResidualColor Qzero.1 = 0 at hQzeroColor
  have hQzeroNeSix : Qzero.1 ≠ Qsix.1 := by
    intro h
    have hfalse : (0 : Fin 7) = 6 := hQzeroColor.symm.trans
      ((congrArg fourPentagonResidualColor h).trans hQsixColor)
    exact (by decide : (0 : Fin 7) ≠ 6) hfalse
  have hQzeroCapSix := hcompat Qzero.1 Qzero.2
    Qsix.1 Qsix.2 hQzeroNeSix
  rw [hQsixAnchor] at hQzeroCapSix
  have hQzeroAnchor : Qzero.1 = residualAnchorZero :=
    residual_color_zero_eq_anchor (hH Qzero.2)
      hQzeroColor hQzeroCapSix
  have hsub : H ⊆ fourPentagonResidualEquality := by
    intro Q hQ
    by_cases hQsix : Q = residualAnchorSix
    · rw [hQsix]
      exact residualAnchorSix_mem_equality
    by_cases hQzero : Q = residualAnchorZero
    · rw [hQzero]
      exact residualAnchorZero_mem_equality
    have hQneSix : Q ≠ Qsix.1 := by
      rw [hQsixAnchor]
      exact hQsix
    have hcapSix := hcompat Q hQ Qsix.1 Qsix.2 hQneSix
    rw [hQsixAnchor] at hcapSix
    have hQneZero : Q ≠ Qzero.1 := by
      rw [hQzeroAnchor]
      exact hQzero
    have hcapZero := hcompat Q hQ Qzero.1 Qzero.2 hQneZero
    rw [hQzeroAnchor] at hcapZero
    exact residual_mem_equality_of_anchor_compatible
      (hH hQ) hcapSix hcapZero
  apply Finset.eq_of_subset_of_card_le hsub
  rw [residualEquality_card, hcard]

end Erdos506.Finite
