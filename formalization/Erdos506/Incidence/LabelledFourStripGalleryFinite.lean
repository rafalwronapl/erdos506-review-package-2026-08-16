import Erdos506.Incidence.RealProjectiveOrdinaryEdgeTriangle

/-!
# Finite support API for the labelled four-strip gallery

The gallery entrance labels every arrangement line except its distinguished
line.  This file pulls actual projective incidence back to that fixed
eleven-element label type and records the pair-uniqueness and on-line
coverage facts needed by the cut-saturation argument.
-/

namespace Erdos506.Incidence

universe u

namespace FiniteProjectiveLineArrangement

variable {Line : Type u} [Fintype Line] [DecidableEq Line]

noncomputable local instance incidentDecidableForLabelledFourStripGalleryFinite
    (A : FiniteProjectiveLineArrangement Line)
    (p : RealProjectivePoint) (l : Line) :
    Decidable (A.Incident p l) :=
  Classical.propDecidable _

/-- Labels of all non-distinguished arrangement lines through `q`. -/
noncomputable def LabelledFourStripGalleryEntrance.labelSupport
    {A : FiniteProjectiveLineArrangement Line} {ell : Line}
    (G : A.LabelledFourStripGalleryEntrance ell)
    (q : RealProjectivePoint) : Finset GalleryLineLabel := by
  classical
  exact Finset.univ.filter fun s => A.Incident q (G.lineEquiv s).1

@[simp]
theorem LabelledFourStripGalleryEntrance.mem_labelSupport_iff
    {A : FiniteProjectiveLineArrangement Line} {ell : Line}
    (G : A.LabelledFourStripGalleryEntrance ell)
    (q : RealProjectivePoint) (s : GalleryLineLabel) :
    s ∈ G.labelSupport q ↔ A.Incident q (G.lineEquiv s).1 := by
  classical
  simp [LabelledFourStripGalleryEntrance.labelSupport]

/-- The actual non-distinguished line set represented by `labelSupport`. -/
noncomputable def LabelledFourStripGalleryEntrance.labelSupportLines
    {A : FiniteProjectiveLineArrangement Line} {ell : Line}
    (G : A.LabelledFourStripGalleryEntrance ell)
    (q : RealProjectivePoint) : Finset Line := by
  classical
  exact (G.labelSupport q).image fun s => (G.lineEquiv s).1

theorem LabelledFourStripGalleryEntrance.mem_labelSupportLines_iff
    {A : FiniteProjectiveLineArrangement Line} {ell : Line}
    (G : A.LabelledFourStripGalleryEntrance ell)
    (q : RealProjectivePoint) (m : Line) :
    m ∈ G.labelSupportLines q ↔ m ≠ ell ∧ A.Incident q m := by
  classical
  constructor
  · intro hm
    obtain ⟨s, hs, hsm⟩ := Finset.mem_image.mp hm
    have hsInc := (G.mem_labelSupport_iff q s).1 hs
    have hsNe : (G.lineEquiv s).1 ≠ ell := (G.lineEquiv s).2
    exact ⟨by simpa [hsm] using hsNe, by simpa [hsm] using hsInc⟩
  · rintro ⟨hmNe, hmInc⟩
    obtain ⟨s, hs⟩ := G.lineEquiv.surjective ⟨m, hmNe⟩
    apply Finset.mem_image.mpr
    refine ⟨s, (G.mem_labelSupport_iff q s).2 ?_, ?_⟩
    · simpa only [congrArg Subtype.val hs] using hmInc
    · exact congrArg Subtype.val hs

theorem LabelledFourStripGalleryEntrance.card_labelSupportLines
    {A : FiniteProjectiveLineArrangement Line} {ell : Line}
    (G : A.LabelledFourStripGalleryEntrance ell)
    (q : RealProjectivePoint) :
    (G.labelSupportLines q).card = (G.labelSupport q).card := by
  classical
  unfold LabelledFourStripGalleryEntrance.labelSupportLines
  exact Finset.card_image_iff.mpr G.line_injective.injOn

/-- The labelled support omits exactly the distinguished line, when that
line is incident with the vertex. -/
theorem LabelledFourStripGalleryEntrance.labelSupport_card_add_indicator
    {A : FiniteProjectiveLineArrangement Line} {ell : Line}
    (G : A.LabelledFourStripGalleryEntrance ell)
    (q : RealProjectivePoint) :
    (G.labelSupport q).card + (if A.Incident q ell then 1 else 0) =
      A.multiplicity q := by
  classical
  let I := (Finset.univ : Finset Line).filter fun m => A.Incident q m
  have hI : I = if A.Incident q ell then
      insert ell (G.labelSupportLines q) else G.labelSupportLines q := by
    ext m
    by_cases hmEll : m = ell
    · subst m
      by_cases hqEll : A.Incident q ell
      · simp [I, hqEll]
      · simp [I, hqEll, G.mem_labelSupportLines_iff]
    · have haway := G.mem_labelSupportLines_iff q m
      by_cases hqEll : A.Incident q ell <;>
        simp [I, hqEll, hmEll, haway]
  have hellNot : ell ∉ G.labelSupportLines q := by
    rw [G.mem_labelSupportLines_iff]
    simp
  unfold FiniteProjectiveLineArrangement.multiplicity
  change (G.labelSupport q).card +
      (if A.Incident q ell then 1 else 0) = I.card
  rw [hI]
  by_cases hqEll : A.Incident q ell
  · simp [hqEll, hellNot, G.card_labelSupportLines q, Nat.add_comm]
  · simp [hqEll, G.card_labelSupportLines q]

/-- Two distinct labelled supports determine at most one actual vertex. -/
theorem LabelledFourStripGalleryEntrance.eq_of_two_common_labels
    {A : FiniteProjectiveLineArrangement Line} {ell : Line}
    (G : A.LabelledFourStripGalleryEntrance ell)
    {q r : RealProjectivePoint} {x y : GalleryLineLabel}
    (hxy : x ≠ y)
    (hxq : x ∈ G.labelSupport q) (hyq : y ∈ G.labelSupport q)
    (hxr : x ∈ G.labelSupport r) (hyr : y ∈ G.labelSupport r) :
    q = r := by
  have hline : (G.lineEquiv x).1 ≠ (G.lineEquiv y).1 := by
    intro h
    exact hxy (G.line_injective h)
  have hq := A.eq_intersection_of_incident hline
    ((G.mem_labelSupport_iff q x).1 hxq)
    ((G.mem_labelSupport_iff q y).1 hyq)
  have hr := A.eq_intersection_of_incident hline
    ((G.mem_labelSupport_iff r x).1 hxr)
    ((G.mem_labelSupport_iff r y).1 hyr)
  exact hq.trans hr.symm

/-- Distinct actual vertices share at most one non-distinguished support. -/
theorem LabelledFourStripGalleryEntrance.labelSupport_inter_card_le_one
    {A : FiniteProjectiveLineArrangement Line} {ell : Line}
    (G : A.LabelledFourStripGalleryEntrance ell)
    {q r : RealProjectivePoint} (hqr : q ≠ r) :
    ((G.labelSupport q) ∩ (G.labelSupport r)).card ≤ 1 := by
  classical
  rw [Finset.card_le_one]
  intro x hx y hy
  by_contra hxy
  have hx' := Finset.mem_inter.mp hx
  have hy' := Finset.mem_inter.mp hy
  exact hqr (G.eq_of_two_common_labels hxy
    hx'.1 hy'.1 hx'.2 hy'.2)

/-- Every actual vertex on `ell` is one of the four rung vertices or one
of the three singleton vertices exported by the entrance. -/
theorem LabelledFourStripGalleryEntrance.exists_eq_rung_or_singleton_of_incident_ell
    {A : FiniteProjectiveLineArrangement Line} {ell : Line}
    (G : A.LabelledFourStripGalleryEntrance ell)
    {q : RealProjectivePoint} (hq : q ∈ A.vertexSet)
    (hqEll : A.Incident q ell) :
    (∃ i : Fin 4, q = G.rungVertex i) ∨
      (∃ i : Fin 3, q = G.singletonVertex i) := by
  classical
  obtain ⟨l, m, hlm, hinter⟩ := A.exists_lines_of_mem_vertexSet hq
  have hql : A.Incident q l := by
    rw [← hinter]
    exact A.intersection_incident_left hlm
  have hqm : A.Incident q m := by
    rw [← hinter]
    exact A.intersection_incident_right hlm
  obtain ⟨n, hnEll, hqn⟩ : ∃ n : Line, n ≠ ell ∧ A.Incident q n := by
    by_cases hlEll : l = ell
    · refine ⟨m, ?_, hqm⟩
      intro hmEll
      exact hlm (hlEll.trans hmEll.symm)
    · exact ⟨l, hlEll, hql⟩
  obtain ⟨s, hs⟩ := G.lineEquiv.surjective ⟨n, hnEll⟩
  have hsLine : (G.lineEquiv s).1 = n := congrArg Subtype.val hs
  cases s with
  | inl s =>
      cases s with
      | inl i =>
          left
          refine ⟨i, ?_⟩
          have hqInt : q = A.intersection ell (G.a i) :=
            A.eq_intersection_of_incident (G.a_ne_ell i).symm hqEll (by
              simpa [LabelledFourStripGalleryEntrance.a, hsLine] using hqn)
          exact hqInt.trans (G.rungVertex_eq_intersection i).symm
      | inr i =>
          left
          refine ⟨i, ?_⟩
          have hqB : A.Incident q (G.b i) := by
            simpa [LabelledFourStripGalleryEntrance.b, hsLine] using hqn
          have hrEll : A.Incident (G.rungVertex i) ell :=
            (G.rungIncident_iff i ell).2 (Or.inl rfl)
          have hrB : A.Incident (G.rungVertex i) (G.b i) :=
            (G.rungIncident_iff i (G.b i)).2 (Or.inr (Or.inr rfl))
          have hqInt := A.eq_intersection_of_incident
            (G.b_ne_ell i).symm hqEll hqB
          have hrInt := A.eq_intersection_of_incident
            (G.b_ne_ell i).symm hrEll hrB
          exact hqInt.trans hrInt.symm
  | inr i =>
      right
      refine ⟨i, ?_⟩
      have hqInt : q = A.intersection ell (G.c i) :=
        A.eq_intersection_of_incident (G.c_ne_ell i).symm hqEll (by
          simpa [LabelledFourStripGalleryEntrance.c, hsLine] using hqn)
      exact hqInt.trans (G.singletonVertex_eq_intersection i).symm

end FiniteProjectiveLineArrangement

end Erdos506.Incidence
