import Erdos506.V3.ExceptionalEight

/-!
# Classification and exact count for the exceptional construction

The coordinate certificates are imported from `ExceptionalEight`.  Here the
support-cover table is connected to the semantic circumcircle model, proving
that the determined-circle finset is exactly the image of the twenty listed
circles.
-/

namespace Erdos506.V3

open Erdos506.V4

theorem exceptionalEightCircle_mem_determinedCircles (i : Fin 20) :
    exceptionalEightCircle i ∈
      determinedCircles exceptionalEightConfiguration := by
  have hge := exceptionalEightSupport_card_ge_three i
  obtain ⟨t, htsub, htcard⟩ := Finset.exists_subset_card_eq hge
  let nt : NoncollinearTriple exceptionalEightConfiguration :=
    ⟨t, mem_noncollinearTriples.mpr
      ⟨htcard, exceptionalEight_noThree t htcard⟩⟩
  rw [mem_determinedCircles_iff]
  refine ⟨nt, ?_⟩
  intro x hx
  have hxSupport : x ∈ exceptionalEightSupport i := htsub hx
  have hxTrace : x ∈ circleTrace exceptionalEightConfiguration
      (exceptionalEightCircle i) := by
    rw [exceptionalEight_circleTrace]
    exact hxSupport
  exact mem_circleTrace.mp hxTrace

noncomputable def exceptionalEightListedCircles : Finset ProperCircle := by
  classical
  exact Finset.univ.image exceptionalEightCircle

theorem exceptionalEightCircle_injective :
    Function.Injective exceptionalEightCircle := by
  intro i j hij
  apply exceptionalEightSupport_injective
  have htrace := congrArg
    (circleTrace exceptionalEightConfiguration) hij
  simpa [exceptionalEight_circleTrace] using htrace

theorem exceptionalEight_determinedCircles_eq_listed :
    determinedCircles exceptionalEightConfiguration =
      exceptionalEightListedCircles := by
  classical
  apply Finset.Subset.antisymm
  · intro c hc
    obtain ⟨t, ht⟩ :=
      (mem_determinedCircles_iff exceptionalEightConfiguration c).mp hc
    have htcard := (mem_noncollinearTriples.mp t.2).1
    obtain ⟨i, hi⟩ := exceptionalEightSupport_covers_triples t.1 htcard
    have hiContains : ∀ x ∈ t.1,
        exceptionalEightConfiguration x ∈
          ((exceptionalEightCircle i).1 : Set Point2) := by
      intro x hx
      have hxTrace : x ∈ circleTrace exceptionalEightConfiguration
          (exceptionalEightCircle i) := by
        rw [exceptionalEight_circleTrace]
        exact hi hx
      exact mem_circleTrace.mp hxTrace
    have hcEq := properCircle_eq_properCircumcircle_of_support
      exceptionalEightConfiguration t c ht
    have hiEq := properCircle_eq_properCircumcircle_of_support
      exceptionalEightConfiguration t (exceptionalEightCircle i) hiContains
    have hci : c = exceptionalEightCircle i := hcEq.trans hiEq.symm
    rw [exceptionalEightListedCircles, hci]
    exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩
  · intro c hc
    rw [exceptionalEightListedCircles] at hc
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hc
    exact exceptionalEightCircle_mem_determinedCircles i

theorem exceptionalEight_circleCount :
    circleCount exceptionalEightConfiguration = 20 := by
  classical
  rw [circleCount, exceptionalEight_determinedCircles_eq_listed,
    exceptionalEightListedCircles,
    Finset.card_image_of_injective _ exceptionalEightCircle_injective]
  simp

theorem exceptionalEight_notConcyclic :
    NotConcyclic exceptionalEightConfiguration := by
  classical
  intro c
  by_cases hsmall : (circleTrace exceptionalEightConfiguration c).card < 3
  · simpa using (show
      (circleTrace exceptionalEightConfiguration c).card < 8 by omega)
  · have hge : 3 ≤ (circleTrace exceptionalEightConfiguration c).card := by
      omega
    obtain ⟨t, htsub, htcard⟩ := Finset.exists_subset_card_eq hge
    let nt : NoncollinearTriple exceptionalEightConfiguration :=
      ⟨t, mem_noncollinearTriples.mpr
        ⟨htcard, exceptionalEight_noThree t htcard⟩⟩
    have hc : c ∈ determinedCircles exceptionalEightConfiguration := by
      rw [mem_determinedCircles_iff]
      refine ⟨nt, ?_⟩
      intro x hx
      exact mem_circleTrace.mp (htsub hx)
    rw [exceptionalEight_determinedCircles_eq_listed,
      exceptionalEightListedCircles] at hc
    obtain ⟨i, hi, hci⟩ := Finset.mem_image.mp hc
    subst c
    rw [exceptionalEight_circleTrace]
    simpa using exceptionalEightSupport_card_lt_eight i

theorem exceptionalEight_admissible :
    Admissible exceptionalEightConfiguration :=
  ⟨exceptionalEight_noThree, exceptionalEight_notConcyclic⟩

theorem exists_exceptional_eight_extremal_configuration :
    ∃ cfg : Configuration (Fin 8),
      Admissible cfg ∧ circleCount cfg = Erdos506.v3Target 8 := by
  refine ⟨exceptionalEightConfiguration, exceptionalEight_admissible, ?_⟩
  rw [exceptionalEight_circleCount]
  norm_num [Erdos506.v3Target]

end Erdos506.V3
