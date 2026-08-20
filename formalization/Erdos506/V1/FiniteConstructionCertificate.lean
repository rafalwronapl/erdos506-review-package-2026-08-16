import Erdos506.V1.Carrier
import Erdos506.V3.EquationCircle

/-!
# Finite certificates for sharp V1 constructions

This module packages the common verification argument for explicit finite
configurations.  A certificate lists all determined proper circles by their
finite traces and proves that every noncollinear selected triple is covered by
one of those traces.  The resulting theorems identify `determinedCircles`,
compute `circleCount`, and establish V1 admissibility.
-/

namespace Erdos506.V1

open Erdos506.V4

/-- In the real affine plane, vanishing orientation of a triple with two
distinct anchor points is sufficient for collinearity. -/
theorem collinear_of_orientation_eq_zero_of_ne (p q r : Point2)
    (hpq : p ≠ q) (hori : Erdos506.V3.orientation p q r = 0) :
    Collinear ℝ ({p, q, r} : Set Point2) := by
  rw [collinear_iff_of_mem
    (show p ∈ ({p, q, r} : Set Point2) by simp)]
  refine ⟨q - p, ?_⟩
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl
  · exact ⟨0, by simp⟩
  · exact ⟨1, by simp⟩
  · by_cases hx0 : q 0 - p 0 = 0
    · have hy0 : q 1 - p 1 ≠ 0 := by
        intro hy
        apply hpq
        ext i
        fin_cases i
        · exact (sub_eq_zero.mp hx0).symm
        · exact (sub_eq_zero.mp hy).symm
      refine ⟨(x 1 - p 1) / (q 1 - p 1), ?_⟩
      ext i
      fin_cases i
      · simp [hx0]
        unfold Erdos506.V3.orientation at hori
        have hprod : (q 1 - p 1) * (x 0 - p 0) = 0 := by
          rw [hx0] at hori
          nlinarith
        have hzero := (mul_eq_zero.mp hprod).resolve_left hy0
        exact sub_eq_zero.mp hzero
      · simp
        field_simp
        ring
    · refine ⟨(x 0 - p 0) / (q 0 - p 0), ?_⟩
      ext i
      fin_cases i
      · simp
        field_simp
        ring
      · simp
        unfold Erdos506.V3.orientation at hori
        field_simp
        nlinarith

/-- A set is collinear when all its points have zero orientation with respect
to one fixed pair of distinct points in the set. -/
theorem collinear_set_of_orientation_eq_zero
    (S : Set Point2) (p q : Point2) (hp : p ∈ S) (hpq : p ≠ q)
    (hori : ∀ x ∈ S, Erdos506.V3.orientation p q x = 0) :
    Collinear ℝ S := by
  rw [collinear_iff_of_mem hp]
  refine ⟨q - p, ?_⟩
  intro x hx
  by_cases hx0 : q 0 - p 0 = 0
  · have hy0 : q 1 - p 1 ≠ 0 := by
      intro hy
      apply hpq
      ext i
      fin_cases i
      · exact (sub_eq_zero.mp hx0).symm
      · exact (sub_eq_zero.mp hy).symm
    refine ⟨(x 1 - p 1) / (q 1 - p 1), ?_⟩
    ext i
    fin_cases i
    · simp [hx0]
      have hor := hori x hx
      unfold Erdos506.V3.orientation at hor
      have hprod : (q 1 - p 1) * (x 0 - p 0) = 0 := by
        rw [hx0] at hor
        nlinarith
      have hzero := (mul_eq_zero.mp hprod).resolve_left hy0
      exact sub_eq_zero.mp hzero
    · simp
      field_simp
      ring
  · refine ⟨(x 0 - p 0) / (q 0 - p 0), ?_⟩
    ext i
    fin_cases i
    · simp
      field_simp
      ring
    · simp
      have hor := hori x hx
      unfold Erdos506.V3.orientation at hor
      field_simp
      nlinarith

theorem noncollinear_covered_of_circle_or_line
    {n c l : ℕ} (cfg : Configuration (Fin n))
    (circleSupport : Fin c → Finset (Fin n))
    (lineSupport : Fin l → Finset (Fin n))
    (hline : ∀ i, Collinear ℝ (supportPoints cfg (lineSupport i)))
    (hcoverAll : ∀ t : Finset (Fin n), t.card = 3 →
      (∃ i : Fin c, t ⊆ circleSupport i) ∨
        (∃ i : Fin l, t ⊆ lineSupport i))
    (t : Finset (Fin n)) (ht : t.card = 3)
    (hnon : IsNoncollinear cfg t) :
    ∃ i : Fin c, t ⊆ circleSupport i := by
  rcases hcoverAll t ht with hcircle | ⟨i, hi⟩
  · exact hcircle
  · exfalso
    apply hnon
    have htpos : 0 < t.card := by omega
    obtain ⟨a, ha⟩ := Finset.card_pos.mp htpos
    have haSmall : cfg a ∈ supportPoints cfg t := ⟨a, ha, rfl⟩
    have haLarge : cfg a ∈ supportPoints cfg (lineSupport i) :=
      ⟨a, hi ha, rfl⟩
    have hcol := hline i
    rw [collinear_iff_of_mem haLarge] at hcol
    rw [collinear_iff_of_mem haSmall]
    obtain ⟨v, hv⟩ := hcol
    refine ⟨v, ?_⟩
    intro p hp
    rcases hp with ⟨x, hx, rfl⟩
    exact hv (cfg x) ⟨x, hi hx, rfl⟩

section

variable {n c : ℕ}
variable (cfg : Configuration (Fin n))
variable (listedCircle : Fin c → ProperCircle)
variable (listedSupport : Fin c → Finset (Fin n))

variable (htrace : ∀ i, circleTrace cfg (listedCircle i) = listedSupport i)
variable (hthree : ∀ i, 3 ≤ (listedSupport i).card)
variable (hcover : ∀ t : Finset (Fin n), t.card = 3 → IsNoncollinear cfg t →
  ∃ i : Fin c, t ⊆ listedSupport i)

include listedSupport htrace hthree in
theorem listedCircle_mem_determinedCircles (i : Fin c) :
    listedCircle i ∈ determinedCircles cfg := by
  have hge := hthree i
  obtain ⟨t, htsub, htcard⟩ := Finset.exists_subset_card_eq hge
  have hnon : IsNoncollinear cfg t := by
    by_contra hcol
    exact not_triple_subset_circle_of_collinear cfg ⟨t, htcard⟩ hcol
      (listedCircle i) (by
        intro x hx
        rw [htrace i]
        exact htsub hx)
  let nt : NoncollinearTriple cfg :=
    ⟨t, mem_noncollinearTriples.mpr ⟨htcard, hnon⟩⟩
  rw [mem_determinedCircles_iff]
  refine ⟨nt, ?_⟩
  intro x hx
  apply mem_circleTrace.mp
  rw [htrace i]
  exact htsub hx

noncomputable def listedCircles : Finset ProperCircle := by
  classical
  exact Finset.univ.image listedCircle

include listedSupport htrace hthree hcover in
theorem determinedCircles_eq_listed :
    determinedCircles cfg = listedCircles listedCircle := by
  classical
  apply Finset.Subset.antisymm
  · intro d hd
    obtain ⟨t, ht⟩ := (mem_determinedCircles_iff cfg d).mp hd
    have htcard := (mem_noncollinearTriples.mp t.2).1
    have htnon := (mem_noncollinearTriples.mp t.2).2
    obtain ⟨i, hi⟩ := hcover t.1 htcard htnon
    have hiContains : ∀ x ∈ t.1, cfg x ∈ ((listedCircle i).1 : Set Point2) := by
      intro x hx
      apply mem_circleTrace.mp
      rw [htrace i]
      exact hi hx
    have hdEq := properCircle_eq_properCircumcircle_of_support cfg t d ht
    have hiEq := properCircle_eq_properCircumcircle_of_support
      cfg t (listedCircle i) hiContains
    have hdi : d = listedCircle i := hdEq.trans hiEq.symm
    rw [listedCircles, hdi]
    exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩
  · intro d hd
    rw [listedCircles] at hd
    obtain ⟨i, _hi, rfl⟩ := Finset.mem_image.mp hd
    exact listedCircle_mem_determinedCircles cfg listedCircle listedSupport
      htrace hthree i

include cfg htrace in
theorem listedCircle_injective
    (hsupportInj : Function.Injective listedSupport) :
    Function.Injective listedCircle := by
  intro i j hij
  apply hsupportInj
  have h := congrArg (circleTrace cfg) hij
  simpa [htrace] using h

include listedCircle htrace hthree hcover in
theorem circleCount_eq_listed_card
    (hsupportInj : Function.Injective listedSupport) :
    circleCount cfg = c := by
  classical
  rw [circleCount,
    determinedCircles_eq_listed cfg listedCircle listedSupport htrace hthree hcover,
    listedCircles,
    Finset.card_image_of_injective _
      (listedCircle_injective cfg listedCircle listedSupport htrace hsupportInj)]
  simp

include listedCircle htrace hthree hcover in
theorem admissible_of_finite_certificate
    (hn : 4 ≤ n)
    (hnoncollinear : Noncollinear cfg)
    (hsupportLt : ∀ i, (listedSupport i).card < n) :
    Admissible cfg := by
  classical
  refine ⟨hnoncollinear, ?_⟩
  intro d
  by_cases hsmall : (circleTrace cfg d).card < 3
  · have : (circleTrace cfg d).card < n := by omega
    simpa using this
  · have hge : 3 ≤ (circleTrace cfg d).card := by omega
    obtain ⟨t, htsub, htcard⟩ := Finset.exists_subset_card_eq hge
    have hnon : IsNoncollinear cfg t := by
      by_contra hcol
      exact not_triple_subset_circle_of_collinear cfg ⟨t, htcard⟩ hcol d htsub
    let nt : NoncollinearTriple cfg :=
      ⟨t, mem_noncollinearTriples.mpr ⟨htcard, hnon⟩⟩
    have hd : d ∈ determinedCircles cfg := by
      rw [mem_determinedCircles_iff]
      exact ⟨nt, fun x hx => mem_circleTrace.mp (htsub hx)⟩
    rw [determinedCircles_eq_listed cfg listedCircle listedSupport
      htrace hthree hcover, listedCircles] at hd
    obtain ⟨i, _hi, hdi⟩ := Finset.mem_image.mp hd
    subst d
    rw [htrace i]
    simpa using hsupportLt i

end

end Erdos506.V1
