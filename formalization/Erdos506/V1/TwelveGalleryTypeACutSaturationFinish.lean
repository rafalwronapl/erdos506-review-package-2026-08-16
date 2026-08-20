import Erdos506.V1.TwelveGalleryTypeACensusFinish
import Erdos506.V1.TwelveGalleryTypeBFinish
import Erdos506.Incidence.LabelledFourStripGalleryFinite
import Mathlib.Tactic

/-!
# The finite Type-A cut-saturation finish

This module contains only the finite consumer after a labelled four-strip
gallery has been extracted.  The geometric entrance is the lossless
`LabelledFourStripGalleryEntrance` from
`RealProjectiveOrdinaryEdgeTriangle`; in particular, its six displayed
bases are containment statements and may still be upgraded.
-/

namespace Erdos506.V1

open Erdos506.Incidence
open Erdos506.Incidence.FiniteProjectiveLineArrangement
open Erdos506.Block Erdos506.Block.BlockSystem Erdos506.V4

universe u

noncomputable local instance twelveGalleryRealProjectivePointDecidableEq :
    DecidableEq RealProjectivePoint :=
  Classical.decEq _

noncomputable local instance twelveGalleryIncidentDecidable
    {Line : Type u} [Fintype Line] [DecidableEq Line]
    (A : FiniteProjectiveLineArrangement Line)
    (q : RealProjectivePoint) (l : Line) : Decidable (A.Incident q l) :=
  Classical.propDecidable _

/-- The actual vertices of an arrangement having multiplicity `s`.  This is
the arrangement-level census used below; it does not remember any affine or
block-system presentation. -/
noncomputable def twelveGalleryMultiplicityVertices
    {Line : Type u} [Fintype Line] [DecidableEq Line]
    (A : FiniteProjectiveLineArrangement Line) (s : Nat) :
    Finset RealProjectivePoint := by
  classical
  exact A.vertexSet.filter fun q => A.multiplicity q = s

/-- The complete actual-vertex census required by the Type-A consumer. -/
structure TwelveGalleryTypeAActualCensus
    {Line : Type u} [Fintype Line] [DecidableEq Line]
    (A : FiniteProjectiveLineArrangement Line) : Prop where
  multiplicity_two :
    (twelveGalleryMultiplicityVertices A 2).card = 6
  multiplicity_three :
    (twelveGalleryMultiplicityVertices A 3).card = 14
  multiplicity_four :
    (twelveGalleryMultiplicityVertices A 4).card = 3
  multiplicity_five :
    (twelveGalleryMultiplicityVertices A 5).card = 0
  multiplicity_le_four :
    ∀ q ∈ A.vertexSet, A.multiplicity q ≤ 4

/-- Forget the affine origin of the restored-dual census. -/
theorem TwelveGalleryTypeARestoredDualCensus.toActualCensus
    {alpha : Type u} [Fintype alpha] [DecidableEq alpha]
    {cfg : Configuration alpha} {p : alpha}
    (C : TwelveGalleryTypeARestoredDualCensus cfg p) :
    TwelveGalleryTypeAActualCensus
      (labelDualArrangement (restoredPivotConfiguration cfg p)) := by
  classical
  exact
    { multiplicity_two := by
        simpa only [twelveGalleryMultiplicityVertices,
          twelveDirectionDualMultiplicityVertices, labelDualVertexSet] using
          C.multiplicity_two
      multiplicity_three := by
        simpa only [twelveGalleryMultiplicityVertices,
          twelveDirectionDualMultiplicityVertices, labelDualVertexSet] using
          C.multiplicity_three
      multiplicity_four := by
        simpa only [twelveGalleryMultiplicityVertices,
          twelveDirectionDualMultiplicityVertices, labelDualVertexSet] using
          C.multiplicity_four
      multiplicity_five := by
        simpa only [twelveGalleryMultiplicityVertices,
          twelveDirectionDualMultiplicityVertices, labelDualVertexSet] using
          C.multiplicity_five
      multiplicity_le_four := by
        simpa only [labelDualVertexSet] using C.multiplicity_le_four }

/-! ## The literal eleven-label cut -/

def twelveGalleryALabel (i : Fin 4) : GalleryLineLabel :=
  .inl (.inl i)

def twelveGalleryBLabel (i : Fin 4) : GalleryLineLabel :=
  .inl (.inr i)

def twelveGalleryCLabel (i : Fin 3) : GalleryLineLabel :=
  .inr i

private def twelveGalleryTypeAAllLabels : List GalleryLineLabel :=
  [twelveGalleryALabel 0, twelveGalleryALabel 1,
    twelveGalleryALabel 2, twelveGalleryALabel 3,
    twelveGalleryBLabel 0, twelveGalleryBLabel 1,
    twelveGalleryBLabel 2, twelveGalleryBLabel 3,
    twelveGalleryCLabel 0, twelveGalleryCLabel 1,
    twelveGalleryCLabel 2]

private theorem twelveGalleryTypeAAllLabels_nodup :
    twelveGalleryTypeAAllLabels.Nodup := by
  decide

private theorem mem_twelveGalleryTypeAAllLabels
    (x : GalleryLineLabel) : x ∈ twelveGalleryTypeAAllLabels := by
  classical
  fin_cases x <;>
    simp [twelveGalleryTypeAAllLabels, twelveGalleryALabel,
      twelveGalleryBLabel, twelveGalleryCLabel]

private def twelveGalleryTypeASubsets
    (n : Nat) : List (Finset GalleryLineLabel) :=
  (List.sublistsLen n twelveGalleryTypeAAllLabels).map List.toFinset

private def twelveGalleryTypeASubsetChunk
    (n start count : Nat) : List (Finset GalleryLineLabel) :=
  (twelveGalleryTypeASubsets n).drop start |>.take count

private theorem list_all_eq_true_of_take_of_drop
    {α : Type u} (n : Nat) (l : List α) (p : α → Bool)
    (hTake : (l.take n).all p = true)
    (hDrop : (l.drop n).all p = true) :
    l.all p = true := by
  rw [← List.take_append_drop n l, List.all_append, hTake, hDrop]
  rfl

private theorem mem_twelveGalleryTypeASubsets_of_card
    (S : Finset GalleryLineLabel) {n : Nat} (hcard : S.card = n) :
    S ∈ twelveGalleryTypeASubsets n := by
  let l := twelveGalleryTypeAAllLabels.filter fun x => x ∈ S
  have hlSub : List.Sublist l twelveGalleryTypeAAllLabels := by
    exact List.filter_sublist
  have hlNodup : l.Nodup :=
    twelveGalleryTypeAAllLabels_nodup.filter _
  have hlFinset : l.toFinset = S := by
    ext x
    simp [l, mem_twelveGalleryTypeAAllLabels]
  have hlLength : l.length = n := by
    calc
      l.length = l.toFinset.card :=
        (List.toFinset_card_of_nodup hlNodup).symm
      _ = S.card := congrArg Finset.card hlFinset
      _ = n := hcard
  exact List.mem_map.mpr
    ⟨l, List.mem_sublistsLen.mpr ⟨hlSub, hlLength⟩, hlFinset⟩

@[simp]
theorem mem_labelSupport_twelveGalleryALabel
    {Line : Type u} [Fintype Line] [DecidableEq Line]
    {A : FiniteProjectiveLineArrangement Line} {ell : Line}
    (G : A.LabelledFourStripGalleryEntrance ell)
    (q : RealProjectivePoint) (i : Fin 4) :
    twelveGalleryALabel i ∈ G.labelSupport q ↔ A.Incident q (G.a i) := by
  simp [twelveGalleryALabel, LabelledFourStripGalleryEntrance.a]

@[simp]
theorem mem_labelSupport_twelveGalleryBLabel
    {Line : Type u} [Fintype Line] [DecidableEq Line]
    {A : FiniteProjectiveLineArrangement Line} {ell : Line}
    (G : A.LabelledFourStripGalleryEntrance ell)
    (q : RealProjectivePoint) (i : Fin 4) :
    twelveGalleryBLabel i ∈ G.labelSupport q ↔ A.Incident q (G.b i) := by
  simp [twelveGalleryBLabel, LabelledFourStripGalleryEntrance.b]

@[simp]
theorem mem_labelSupport_twelveGalleryCLabel
    {Line : Type u} [Fintype Line] [DecidableEq Line]
    {A : FiniteProjectiveLineArrangement Line} {ell : Line}
    (G : A.LabelledFourStripGalleryEntrance ell)
    (q : RealProjectivePoint) (i : Fin 3) :
    twelveGalleryCLabel i ∈ G.labelSupport q ↔ A.Incident q (G.c i) := by
  simp [twelveGalleryCLabel, LabelledFourStripGalleryEntrance.c]

def twelveGalleryUpperBaseLabels (i : Fin 3) : Finset GalleryLineLabel :=
  {twelveGalleryALabel (galleryStripLeft i),
    twelveGalleryALabel (galleryStripRight i), twelveGalleryCLabel i}

def twelveGalleryLowerBaseLabels (i : Fin 3) : Finset GalleryLineLabel :=
  {twelveGalleryBLabel (galleryStripLeft i),
    twelveGalleryBLabel (galleryStripRight i), twelveGalleryCLabel i}

abbrev TwelveGalleryTypeABaseSlot := Fin 3 ⊕ Fin 3

def twelveGalleryBaseLabels
    (s : TwelveGalleryTypeABaseSlot) : Finset GalleryLineLabel :=
  match s with
  | .inl i => twelveGalleryUpperBaseLabels i
  | .inr i => twelveGalleryLowerBaseLabels i

def twelveGalleryBaseVertex
    {Line : Type u} [Fintype Line] [DecidableEq Line]
    {A : FiniteProjectiveLineArrangement Line} {ell : Line}
    (G : A.LabelledFourStripGalleryEntrance ell)
    (s : TwelveGalleryTypeABaseSlot) : RealProjectivePoint :=
  match s with
  | .inl i => G.upperVertex i
  | .inr i => G.lowerVertex i

@[simp]
theorem twelveGalleryBaseLabels_card
    (s : TwelveGalleryTypeABaseSlot) :
    (twelveGalleryBaseLabels s).card = 3 := by
  fin_cases s <;> decide

theorem twelveGalleryBaseLabels_subset_labelSupport
    {Line : Type u} [Fintype Line] [DecidableEq Line]
    {A : FiniteProjectiveLineArrangement Line} {ell : Line}
    (G : A.LabelledFourStripGalleryEntrance ell)
    (s : TwelveGalleryTypeABaseSlot) :
    twelveGalleryBaseLabels s ⊆ G.labelSupport (twelveGalleryBaseVertex G s) := by
  intro x hx
  cases s with
  | inl i =>
      simp only [twelveGalleryBaseLabels, twelveGalleryUpperBaseLabels,
        Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl
      · exact (mem_labelSupport_twelveGalleryALabel G _ _).2
          (G.upperIncidence i).1
      · exact (mem_labelSupport_twelveGalleryALabel G _ _).2
          (G.upperIncidence i).2.1
      · exact (mem_labelSupport_twelveGalleryCLabel G _ _).2
          (G.upperIncidence i).2.2
  | inr i =>
      simp only [twelveGalleryBaseLabels, twelveGalleryLowerBaseLabels,
        Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl
      · exact (mem_labelSupport_twelveGalleryBLabel G _ _).2
          (G.lowerIncidence i).1
      · exact (mem_labelSupport_twelveGalleryBLabel G _ _).2
          (G.lowerIncidence i).2.1
      · exact (mem_labelSupport_twelveGalleryCLabel G _ _).2
          (G.lowerIncidence i).2.2

theorem twelveGalleryBaseVertex_mem_vertexSet
    {Line : Type u} [Fintype Line] [DecidableEq Line]
    {A : FiniteProjectiveLineArrangement Line} {ell : Line}
    (G : A.LabelledFourStripGalleryEntrance ell)
    (s : TwelveGalleryTypeABaseSlot) :
    twelveGalleryBaseVertex G s ∈ A.vertexSet := by
  cases s with
  | inl i =>
      have hne : G.a (galleryStripLeft i) ≠
          G.a (galleryStripRight i) := by
        intro h
        have hs := G.line_injective h
        simp [LabelledFourStripGalleryEntrance.a, galleryStripLeft,
          galleryStripRight] at hs
      have heq : G.upperVertex i =
          A.intersection (G.a (galleryStripLeft i))
            (G.a (galleryStripRight i)) :=
        A.eq_intersection_of_incident hne
          (G.upperIncidence i).1 (G.upperIncidence i).2.1
      rw [twelveGalleryBaseVertex, heq]
      exact A.intersection_mem_vertexSet hne
  | inr i =>
      have hne : G.b (galleryStripLeft i) ≠
          G.b (galleryStripRight i) := by
        intro h
        have hs := G.line_injective h
        simp [LabelledFourStripGalleryEntrance.b, galleryStripLeft,
          galleryStripRight] at hs
      have heq : G.lowerVertex i =
          A.intersection (G.b (galleryStripLeft i))
            (G.b (galleryStripRight i)) :=
        A.eq_intersection_of_incident hne
          (G.lowerIncidence i).1 (G.lowerIncidence i).2.1
      rw [twelveGalleryBaseVertex, heq]
      exact A.intersection_mem_vertexSet hne

theorem labelSupport_rungVertex_eq
    {Line : Type u} [Fintype Line] [DecidableEq Line]
    {A : FiniteProjectiveLineArrangement Line} {ell : Line}
    (G : A.LabelledFourStripGalleryEntrance ell) (i : Fin 4) :
    G.labelSupport (G.rungVertex i) =
      {twelveGalleryALabel i, twelveGalleryBLabel i} := by
  classical
  ext s
  rw [G.mem_labelSupport_iff]
  simp only [Finset.mem_insert, Finset.mem_singleton]
  constructor
  · intro hs
    rcases (G.rungIncident_iff i (G.lineEquiv s).1).1 hs with h | h | h
    · exact False.elim ((G.lineEquiv s).2 h)
    · left
      apply G.line_injective
      simpa [twelveGalleryALabel,
        LabelledFourStripGalleryEntrance.a] using h
    · right
      apply G.line_injective
      simpa [twelveGalleryBLabel,
        LabelledFourStripGalleryEntrance.b] using h
  · rintro (rfl | rfl)
    · simpa [twelveGalleryALabel,
        LabelledFourStripGalleryEntrance.a] using
        (G.rungIncident_iff i (G.a i)).2 (Or.inr (Or.inl rfl))
    · simpa [twelveGalleryBLabel,
        LabelledFourStripGalleryEntrance.b] using
        (G.rungIncident_iff i (G.b i)).2 (Or.inr (Or.inr rfl))

theorem labelSupport_singletonVertex_eq
    {Line : Type u} [Fintype Line] [DecidableEq Line]
    {A : FiniteProjectiveLineArrangement Line} {ell : Line}
    (G : A.LabelledFourStripGalleryEntrance ell) (i : Fin 3) :
    G.labelSupport (G.singletonVertex i) = {twelveGalleryCLabel i} := by
  classical
  ext s
  rw [G.mem_labelSupport_iff]
  simp only [Finset.mem_singleton]
  constructor
  · intro hs
    rcases (G.singletonIncident_iff i (G.lineEquiv s).1).1 hs with h | h
    · exact False.elim ((G.lineEquiv s).2 h)
    · apply G.line_injective
      simpa [twelveGalleryCLabel,
        LabelledFourStripGalleryEntrance.c] using h
  · intro h
    subst s
    simpa [twelveGalleryCLabel,
      LabelledFourStripGalleryEntrance.c] using
      (G.singletonIncident_iff i (G.c i)).2 (Or.inr rfl)

theorem twelveGalleryALabel_injective :
    Function.Injective twelveGalleryALabel := by
  intro i j h
  simpa [twelveGalleryALabel] using h

theorem twelveGalleryCLabel_injective :
    Function.Injective twelveGalleryCLabel := by
  intro i j h
  simpa [twelveGalleryCLabel] using h

theorem twelveGalleryRungVertex_multiplicity_eq_three
    {Line : Type u} [Fintype Line] [DecidableEq Line]
    {A : FiniteProjectiveLineArrangement Line} {ell : Line}
    (G : A.LabelledFourStripGalleryEntrance ell) (i : Fin 4) :
    A.multiplicity (G.rungVertex i) = 3 := by
  have h := G.labelSupport_card_add_indicator (G.rungVertex i)
  rw [labelSupport_rungVertex_eq] at h
  have hEll : A.Incident (G.rungVertex i) ell :=
    (G.rungIncident_iff i ell).2 (Or.inl rfl)
  simpa [hEll] using h.symm

theorem twelveGallerySingletonVertex_multiplicity_eq_two
    {Line : Type u} [Fintype Line] [DecidableEq Line]
    {A : FiniteProjectiveLineArrangement Line} {ell : Line}
    (G : A.LabelledFourStripGalleryEntrance ell) (i : Fin 3) :
    A.multiplicity (G.singletonVertex i) = 2 := by
  have h := G.labelSupport_card_add_indicator (G.singletonVertex i)
  rw [labelSupport_singletonVertex_eq] at h
  have hEll : A.Incident (G.singletonVertex i) ell :=
    (G.singletonIncident_iff i ell).2 (Or.inl rfl)
  simpa [hEll] using h.symm

theorem twelveGalleryRungVertex_mem_vertexSet
    {Line : Type u} [Fintype Line] [DecidableEq Line]
    {A : FiniteProjectiveLineArrangement Line} {ell : Line}
    (G : A.LabelledFourStripGalleryEntrance ell) (i : Fin 4) :
    G.rungVertex i ∈ A.vertexSet := by
  rw [G.rungVertex_eq_intersection i]
  exact A.intersection_mem_vertexSet (G.a_ne_ell i).symm

theorem twelveGallerySingletonVertex_mem_vertexSet
    {Line : Type u} [Fintype Line] [DecidableEq Line]
    {A : FiniteProjectiveLineArrangement Line} {ell : Line}
    (G : A.LabelledFourStripGalleryEntrance ell) (i : Fin 3) :
    G.singletonVertex i ∈ A.vertexSet := by
  rw [G.singletonVertex_eq_intersection i]
  exact A.intersection_mem_vertexSet (G.c_ne_ell i).symm

theorem twelveGalleryRungVertex_injective
    {Line : Type u} [Fintype Line] [DecidableEq Line]
    {A : FiniteProjectiveLineArrangement Line} {ell : Line}
    (G : A.LabelledFourStripGalleryEntrance ell) :
    Function.Injective G.rungVertex := by
  intro i j hij
  have hs := congrArg G.labelSupport hij
  rw [labelSupport_rungVertex_eq, labelSupport_rungVertex_eq] at hs
  have hm : twelveGalleryALabel i ∈
      ({twelveGalleryALabel j, twelveGalleryBLabel j} :
        Finset GalleryLineLabel) := by
    rw [← hs]
    simp
  have hijLabel : twelveGalleryALabel i = twelveGalleryALabel j := by
    simpa [twelveGalleryALabel, twelveGalleryBLabel] using hm
  exact twelveGalleryALabel_injective hijLabel

theorem twelveGallerySingletonVertex_injective
    {Line : Type u} [Fintype Line] [DecidableEq Line]
    {A : FiniteProjectiveLineArrangement Line} {ell : Line}
    (G : A.LabelledFourStripGalleryEntrance ell) :
    Function.Injective G.singletonVertex := by
  intro i j hij
  have hs := congrArg G.labelSupport hij
  rw [labelSupport_singletonVertex_eq,
    labelSupport_singletonVertex_eq] at hs
  apply twelveGalleryCLabel_injective
  have hm : twelveGalleryCLabel i ∈
      ({twelveGalleryCLabel j} : Finset GalleryLineLabel) := by
    rw [← hs]
    simp
  simpa using hm

theorem twelveGalleryBaseVertex_not_incident_ell
    {Line : Type u} [Fintype Line] [DecidableEq Line]
    {A : FiniteProjectiveLineArrangement Line} {ell : Line}
    (G : A.LabelledFourStripGalleryEntrance ell)
    (s : TwelveGalleryTypeABaseSlot) :
    ¬ A.Incident (twelveGalleryBaseVertex G s) ell := by
  intro hsEll
  have hsVertex := twelveGalleryBaseVertex_mem_vertexSet G s
  rcases G.exists_eq_rung_or_singleton_of_incident_ell hsVertex hsEll with
      ⟨i, hi⟩ | ⟨i, hi⟩
  · have hsub := twelveGalleryBaseLabels_subset_labelSupport G s
    rw [hi, labelSupport_rungVertex_eq] at hsub
    have hcard := Finset.card_le_card hsub
    rw [twelveGalleryBaseLabels_card] at hcard
    have hne : twelveGalleryALabel i ≠ twelveGalleryBLabel i := by
      simp [twelveGalleryALabel, twelveGalleryBLabel]
    simp [hne] at hcard
  · have hsub := twelveGalleryBaseLabels_subset_labelSupport G s
    rw [hi, labelSupport_singletonVertex_eq] at hsub
    have hcard := Finset.card_le_card hsub
    rw [twelveGalleryBaseLabels_card] at hcard
    norm_num at hcard

theorem twelveGalleryBaseVertex_labelSupport_card_eq_multiplicity
    {Line : Type u} [Fintype Line] [DecidableEq Line]
    {A : FiniteProjectiveLineArrangement Line} {ell : Line}
    (G : A.LabelledFourStripGalleryEntrance ell)
    (s : TwelveGalleryTypeABaseSlot) :
    (G.labelSupport (twelveGalleryBaseVertex G s)).card =
      A.multiplicity (twelveGalleryBaseVertex G s) := by
  have h := G.labelSupport_card_add_indicator (twelveGalleryBaseVertex G s)
  simp [twelveGalleryBaseVertex_not_incident_ell G s] at h
  exact h

theorem twelveGalleryBaseVertex_labelSupport_card_three_or_four
    {Line : Type u} [Fintype Line] [DecidableEq Line]
    {A : FiniteProjectiveLineArrangement Line} {ell : Line}
    (G : A.LabelledFourStripGalleryEntrance ell)
    (census : TwelveGalleryTypeAActualCensus A)
    (s : TwelveGalleryTypeABaseSlot) :
    (G.labelSupport (twelveGalleryBaseVertex G s)).card = 3 ∨
      (G.labelSupport (twelveGalleryBaseVertex G s)).card = 4 := by
  have hthree : 3 ≤
      (G.labelSupport (twelveGalleryBaseVertex G s)).card := by
    simpa using Finset.card_le_card
      (twelveGalleryBaseLabels_subset_labelSupport G s)
  have hfour : (G.labelSupport (twelveGalleryBaseVertex G s)).card ≤ 4 := by
    rw [twelveGalleryBaseVertex_labelSupport_card_eq_multiplicity G s]
    exact census.multiplicity_le_four _
      (twelveGalleryBaseVertex_mem_vertexSet G s)
  omega

private theorem twelveGalleryBaseLabels_union_card_ge_five_table :
    ∀ s t : TwelveGalleryTypeABaseSlot, s ≠ t →
      5 ≤ (twelveGalleryBaseLabels s ∪ twelveGalleryBaseLabels t).card := by
  classical
  decide

theorem twelveGalleryBaseVertex_injective
    {Line : Type u} [Fintype Line] [DecidableEq Line]
    {A : FiniteProjectiveLineArrangement Line} {ell : Line}
    (G : A.LabelledFourStripGalleryEntrance ell)
    (census : TwelveGalleryTypeAActualCensus A) :
    Function.Injective (twelveGalleryBaseVertex G) := by
  intro s t hst
  by_contra hne
  have hsSub := twelveGalleryBaseLabels_subset_labelSupport G s
  have htSub := twelveGalleryBaseLabels_subset_labelSupport G t
  have hunion : twelveGalleryBaseLabels s ∪ twelveGalleryBaseLabels t ⊆
      G.labelSupport (twelveGalleryBaseVertex G s) := by
    intro x hx
    rcases Finset.mem_union.mp hx with hx | hx
    · exact hsSub hx
    · rw [hst]
      exact htSub hx
  have hge := twelveGalleryBaseLabels_union_card_ge_five_table s t hne
  have hle := Finset.card_le_card hunion
  have hcap :=
    twelveGalleryBaseVertex_labelSupport_card_three_or_four G census s
  omega

noncomputable def twelveGalleryOnLineMultiplicityVertices
    {Line : Type u} [Fintype Line] [DecidableEq Line]
    (A : FiniteProjectiveLineArrangement Line) (ell : Line) (s : Nat) :
    Finset RealProjectivePoint :=
  (twelveGalleryMultiplicityVertices A s).filter fun q => A.Incident q ell

noncomputable def twelveGalleryOffLineMultiplicityVertices
    {Line : Type u} [Fintype Line] [DecidableEq Line]
    (A : FiniteProjectiveLineArrangement Line) (ell : Line) (s : Nat) :
    Finset RealProjectivePoint :=
  (twelveGalleryMultiplicityVertices A s).filter fun q => ¬ A.Incident q ell

theorem twelveGalleryOnLineMultiplicityVertices_two_eq
    {Line : Type u} [Fintype Line] [DecidableEq Line]
    {A : FiniteProjectiveLineArrangement Line} {ell : Line}
    (G : A.LabelledFourStripGalleryEntrance ell) :
    twelveGalleryOnLineMultiplicityVertices A ell 2 =
      Finset.univ.image G.singletonVertex := by
  classical
  ext q
  simp only [twelveGalleryOnLineMultiplicityVertices,
    twelveGalleryMultiplicityVertices, Finset.mem_filter,
    Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨⟨hqVertex, hqTwo⟩, hqEll⟩
    rcases G.exists_eq_rung_or_singleton_of_incident_ell hqVertex hqEll with
        ⟨i, hi⟩ | ⟨i, hi⟩
    · rw [hi, twelveGalleryRungVertex_multiplicity_eq_three] at hqTwo
      omega
    · exact ⟨i, hi.symm⟩
  · rintro ⟨i, rfl⟩
    exact ⟨⟨twelveGallerySingletonVertex_mem_vertexSet G i,
      twelveGallerySingletonVertex_multiplicity_eq_two G i⟩,
      (G.singletonIncident_iff i ell).2 (Or.inl rfl)⟩

theorem twelveGalleryOnLineMultiplicityVertices_three_eq
    {Line : Type u} [Fintype Line] [DecidableEq Line]
    {A : FiniteProjectiveLineArrangement Line} {ell : Line}
    (G : A.LabelledFourStripGalleryEntrance ell) :
    twelveGalleryOnLineMultiplicityVertices A ell 3 =
      Finset.univ.image G.rungVertex := by
  classical
  ext q
  simp only [twelveGalleryOnLineMultiplicityVertices,
    twelveGalleryMultiplicityVertices, Finset.mem_filter,
    Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨⟨hqVertex, hqThree⟩, hqEll⟩
    rcases G.exists_eq_rung_or_singleton_of_incident_ell hqVertex hqEll with
        ⟨i, hi⟩ | ⟨i, hi⟩
    · exact ⟨i, hi.symm⟩
    · rw [hi, twelveGallerySingletonVertex_multiplicity_eq_two] at hqThree
      omega
  · rintro ⟨i, rfl⟩
    exact ⟨⟨twelveGalleryRungVertex_mem_vertexSet G i,
      twelveGalleryRungVertex_multiplicity_eq_three G i⟩,
      (G.rungIncident_iff i ell).2 (Or.inl rfl)⟩

theorem twelveGalleryOnLineMultiplicityVertices_four_eq_empty
    {Line : Type u} [Fintype Line] [DecidableEq Line]
    {A : FiniteProjectiveLineArrangement Line} {ell : Line}
    (G : A.LabelledFourStripGalleryEntrance ell) :
    twelveGalleryOnLineMultiplicityVertices A ell 4 = ∅ := by
  classical
  ext q
  constructor
  · intro hq
    simp only [twelveGalleryOnLineMultiplicityVertices,
      twelveGalleryMultiplicityVertices, Finset.mem_filter] at hq
    rcases hq with ⟨⟨hqVertex, hqFour⟩, hqEll⟩
    rcases G.exists_eq_rung_or_singleton_of_incident_ell hqVertex hqEll with
        ⟨i, hi⟩ | ⟨i, hi⟩
    · rw [hi, twelveGalleryRungVertex_multiplicity_eq_three] at hqFour
      omega
    · rw [hi, twelveGallerySingletonVertex_multiplicity_eq_two] at hqFour
      omega
  · intro hq
    simpa using hq

theorem twelveGalleryOnLineMultiplicityVertices_two_card
    {Line : Type u} [Fintype Line] [DecidableEq Line]
    {A : FiniteProjectiveLineArrangement Line} {ell : Line}
    (G : A.LabelledFourStripGalleryEntrance ell) :
    (twelveGalleryOnLineMultiplicityVertices A ell 2).card = 3 := by
  rw [twelveGalleryOnLineMultiplicityVertices_two_eq G]
  rw [Finset.card_image_iff.mpr
    (twelveGallerySingletonVertex_injective G).injOn]
  simp

theorem twelveGalleryOnLineMultiplicityVertices_three_card
    {Line : Type u} [Fintype Line] [DecidableEq Line]
    {A : FiniteProjectiveLineArrangement Line} {ell : Line}
    (G : A.LabelledFourStripGalleryEntrance ell) :
    (twelveGalleryOnLineMultiplicityVertices A ell 3).card = 4 := by
  rw [twelveGalleryOnLineMultiplicityVertices_three_eq G]
  rw [Finset.card_image_iff.mpr
    (twelveGalleryRungVertex_injective G).injOn]
  simp

theorem twelveGalleryOffLineMultiplicityVertices_two_card
    {Line : Type u} [Fintype Line] [DecidableEq Line]
    {A : FiniteProjectiveLineArrangement Line} {ell : Line}
    (G : A.LabelledFourStripGalleryEntrance ell)
    (census : TwelveGalleryTypeAActualCensus A) :
    (twelveGalleryOffLineMultiplicityVertices A ell 2).card = 3 := by
  classical
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := twelveGalleryMultiplicityVertices A 2)
    (p := fun q => A.Incident q ell)
  have hsplit' :
      (twelveGalleryOnLineMultiplicityVertices A ell 2).card +
        (twelveGalleryOffLineMultiplicityVertices A ell 2).card =
          (twelveGalleryMultiplicityVertices A 2).card := by
    simpa [twelveGalleryOnLineMultiplicityVertices,
      twelveGalleryOffLineMultiplicityVertices] using hsplit
  rw [twelveGalleryOnLineMultiplicityVertices_two_card G,
    census.multiplicity_two] at hsplit'
  omega

theorem twelveGalleryOffLineMultiplicityVertices_three_card
    {Line : Type u} [Fintype Line] [DecidableEq Line]
    {A : FiniteProjectiveLineArrangement Line} {ell : Line}
    (G : A.LabelledFourStripGalleryEntrance ell)
    (census : TwelveGalleryTypeAActualCensus A) :
    (twelveGalleryOffLineMultiplicityVertices A ell 3).card = 10 := by
  classical
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := twelveGalleryMultiplicityVertices A 3)
    (p := fun q => A.Incident q ell)
  have hsplit' :
      (twelveGalleryOnLineMultiplicityVertices A ell 3).card +
        (twelveGalleryOffLineMultiplicityVertices A ell 3).card =
          (twelveGalleryMultiplicityVertices A 3).card := by
    simpa [twelveGalleryOnLineMultiplicityVertices,
      twelveGalleryOffLineMultiplicityVertices] using hsplit
  rw [twelveGalleryOnLineMultiplicityVertices_three_card G,
    census.multiplicity_three] at hsplit'
  omega

theorem twelveGalleryOffLineMultiplicityVertices_four_card
    {Line : Type u} [Fintype Line] [DecidableEq Line]
    {A : FiniteProjectiveLineArrangement Line} {ell : Line}
    (G : A.LabelledFourStripGalleryEntrance ell)
    (census : TwelveGalleryTypeAActualCensus A) :
    (twelveGalleryOffLineMultiplicityVertices A ell 4).card = 3 := by
  classical
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := twelveGalleryMultiplicityVertices A 4)
    (p := fun q => A.Incident q ell)
  have hsplit' :
      (twelveGalleryOnLineMultiplicityVertices A ell 4).card +
        (twelveGalleryOffLineMultiplicityVertices A ell 4).card =
          (twelveGalleryMultiplicityVertices A 4).card := by
    simpa [twelveGalleryOnLineMultiplicityVertices,
      twelveGalleryOffLineMultiplicityVertices] using hsplit
  rw [twelveGalleryOnLineMultiplicityVertices_four_eq_empty G,
    census.multiplicity_four] at hsplit'
  simp at hsplit'
  exact hsplit'

noncomputable def twelveGalleryUpgradedBaseSlots
    {Line : Type u} [Fintype Line] [DecidableEq Line]
    {A : FiniteProjectiveLineArrangement Line} {ell : Line}
    (G : A.LabelledFourStripGalleryEntrance ell) :
    Finset TwelveGalleryTypeABaseSlot :=
  Finset.univ.filter fun s =>
    (G.labelSupport (twelveGalleryBaseVertex G s)).card = 4

noncomputable def twelveGalleryExactBaseSlots
    {Line : Type u} [Fintype Line] [DecidableEq Line]
    {A : FiniteProjectiveLineArrangement Line} {ell : Line}
    (G : A.LabelledFourStripGalleryEntrance ell) :
    Finset TwelveGalleryTypeABaseSlot :=
  Finset.univ \ twelveGalleryUpgradedBaseSlots G

noncomputable def twelveGalleryExactBaseVertices
    {Line : Type u} [Fintype Line] [DecidableEq Line]
    {A : FiniteProjectiveLineArrangement Line} {ell : Line}
    (G : A.LabelledFourStripGalleryEntrance ell) :
    Finset RealProjectivePoint :=
  (twelveGalleryExactBaseSlots G).image (twelveGalleryBaseVertex G)

noncomputable def twelveGalleryUpgradedBaseVertices
    {Line : Type u} [Fintype Line] [DecidableEq Line]
    {A : FiniteProjectiveLineArrangement Line} {ell : Line}
    (G : A.LabelledFourStripGalleryEntrance ell) :
    Finset RealProjectivePoint :=
  (twelveGalleryUpgradedBaseSlots G).image (twelveGalleryBaseVertex G)

noncomputable def twelveGalleryResidualTripleVertices
    {Line : Type u} [Fintype Line] [DecidableEq Line]
    (A : FiniteProjectiveLineArrangement Line) (ell : Line)
    (G : A.LabelledFourStripGalleryEntrance ell) :
    Finset RealProjectivePoint :=
  twelveGalleryOffLineMultiplicityVertices A ell 3 \
    twelveGalleryExactBaseVertices G

noncomputable def twelveGalleryNonupgradeQuadVertices
    {Line : Type u} [Fintype Line] [DecidableEq Line]
    (A : FiniteProjectiveLineArrangement Line) (ell : Line)
    (G : A.LabelledFourStripGalleryEntrance ell) :
    Finset RealProjectivePoint :=
  twelveGalleryOffLineMultiplicityVertices A ell 4 \
    twelveGalleryUpgradedBaseVertices G

theorem twelveGalleryUpgradedBaseSlots_card_le_three
    {Line : Type u} [Fintype Line] [DecidableEq Line]
    {A : FiniteProjectiveLineArrangement Line} {ell : Line}
    (G : A.LabelledFourStripGalleryEntrance ell)
    (census : TwelveGalleryTypeAActualCensus A) :
    (twelveGalleryUpgradedBaseSlots G).card ≤ 3 := by
  classical
  have himage : (twelveGalleryUpgradedBaseVertices G).card =
      (twelveGalleryUpgradedBaseSlots G).card :=
    Finset.card_image_iff.mpr
      (twelveGalleryBaseVertex_injective G census).injOn
  have hsub : twelveGalleryUpgradedBaseVertices G ⊆
      twelveGalleryOffLineMultiplicityVertices A ell 4 := by
    intro q hq
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hq
    have hsFour :
        (G.labelSupport (twelveGalleryBaseVertex G s)).card = 4 :=
      (Finset.mem_filter.mp hs).2
    have hmult : A.multiplicity (twelveGalleryBaseVertex G s) = 4 := by
      rw [← twelveGalleryBaseVertex_labelSupport_card_eq_multiplicity G s]
      exact hsFour
    exact Finset.mem_filter.mpr ⟨
      Finset.mem_filter.mpr ⟨twelveGalleryBaseVertex_mem_vertexSet G s, hmult⟩,
      twelveGalleryBaseVertex_not_incident_ell G s⟩
  have hle := Finset.card_le_card hsub
  rw [twelveGalleryOffLineMultiplicityVertices_four_card G census,
    himage] at hle
  exact hle

theorem twelveGalleryExactBaseSlots_card_add_upgraded_card
    {Line : Type u} [Fintype Line] [DecidableEq Line]
    {A : FiniteProjectiveLineArrangement Line} {ell : Line}
    (G : A.LabelledFourStripGalleryEntrance ell) :
    (twelveGalleryExactBaseSlots G).card +
      (twelveGalleryUpgradedBaseSlots G).card = 6 := by
  classical
  rw [twelveGalleryExactBaseSlots,
    Finset.card_sdiff_of_subset (Finset.subset_univ _)]
  have huniv : (Finset.univ : Finset TwelveGalleryTypeABaseSlot).card = 6 := by
    decide
  have hle := Finset.card_le_card
    (show twelveGalleryUpgradedBaseSlots G ⊆
      (Finset.univ : Finset TwelveGalleryTypeABaseSlot) from
        Finset.subset_univ _)
  rw [huniv] at hle ⊢
  exact Nat.sub_add_cancel hle

theorem twelveGalleryExactBaseVertices_subset_offLine_three
    {Line : Type u} [Fintype Line] [DecidableEq Line]
    {A : FiniteProjectiveLineArrangement Line} {ell : Line}
    (G : A.LabelledFourStripGalleryEntrance ell)
    (census : TwelveGalleryTypeAActualCensus A) :
    twelveGalleryExactBaseVertices G ⊆
      twelveGalleryOffLineMultiplicityVertices A ell 3 := by
  classical
  intro q hq
  obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hq
  have hsNotFour :
      (G.labelSupport (twelveGalleryBaseVertex G s)).card ≠ 4 := by
    intro hsFour
    exact (Finset.mem_sdiff.mp hs).2
      (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hsFour⟩)
  have hsThree :
      (G.labelSupport (twelveGalleryBaseVertex G s)).card = 3 :=
    (twelveGalleryBaseVertex_labelSupport_card_three_or_four
      G census s).resolve_right hsNotFour
  have hmult : A.multiplicity (twelveGalleryBaseVertex G s) = 3 := by
    rw [← twelveGalleryBaseVertex_labelSupport_card_eq_multiplicity G s]
    exact hsThree
  exact Finset.mem_filter.mpr ⟨
    Finset.mem_filter.mpr ⟨twelveGalleryBaseVertex_mem_vertexSet G s, hmult⟩,
    twelveGalleryBaseVertex_not_incident_ell G s⟩

theorem twelveGalleryUpgradedBaseVertices_subset_offLine_four
    {Line : Type u} [Fintype Line] [DecidableEq Line]
    {A : FiniteProjectiveLineArrangement Line} {ell : Line}
    (G : A.LabelledFourStripGalleryEntrance ell) :
    twelveGalleryUpgradedBaseVertices G ⊆
      twelveGalleryOffLineMultiplicityVertices A ell 4 := by
  classical
  intro q hq
  obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hq
  have hsFour :
      (G.labelSupport (twelveGalleryBaseVertex G s)).card = 4 :=
    (Finset.mem_filter.mp hs).2
  have hmult : A.multiplicity (twelveGalleryBaseVertex G s) = 4 := by
    rw [← twelveGalleryBaseVertex_labelSupport_card_eq_multiplicity G s]
    exact hsFour
  exact Finset.mem_filter.mpr ⟨
    Finset.mem_filter.mpr ⟨twelveGalleryBaseVertex_mem_vertexSet G s, hmult⟩,
    twelveGalleryBaseVertex_not_incident_ell G s⟩

theorem twelveGalleryResidualTripleVertices_card
    {Line : Type u} [Fintype Line] [DecidableEq Line]
    {A : FiniteProjectiveLineArrangement Line} {ell : Line}
    (G : A.LabelledFourStripGalleryEntrance ell)
    (census : TwelveGalleryTypeAActualCensus A) :
    (twelveGalleryResidualTripleVertices A ell G).card =
      4 + (twelveGalleryUpgradedBaseSlots G).card := by
  classical
  have hbaseImage : (twelveGalleryExactBaseVertices G).card =
      (twelveGalleryExactBaseSlots G).card :=
    Finset.card_image_iff.mpr
      (twelveGalleryBaseVertex_injective G census).injOn
  rw [twelveGalleryResidualTripleVertices,
    Finset.card_sdiff_of_subset
      (twelveGalleryExactBaseVertices_subset_offLine_three G census),
    twelveGalleryOffLineMultiplicityVertices_three_card G census,
    hbaseImage]
  have hpartition := twelveGalleryExactBaseSlots_card_add_upgraded_card G
  omega

theorem twelveGalleryNonupgradeQuadVertices_card
    {Line : Type u} [Fintype Line] [DecidableEq Line]
    {A : FiniteProjectiveLineArrangement Line} {ell : Line}
    (G : A.LabelledFourStripGalleryEntrance ell)
    (census : TwelveGalleryTypeAActualCensus A) :
    (twelveGalleryNonupgradeQuadVertices A ell G).card =
      3 - (twelveGalleryUpgradedBaseSlots G).card := by
  classical
  have hbaseImage : (twelveGalleryUpgradedBaseVertices G).card =
      (twelveGalleryUpgradedBaseSlots G).card :=
    Finset.card_image_iff.mpr
      (twelveGalleryBaseVertex_injective G census).injOn
  rw [twelveGalleryNonupgradeQuadVertices,
    Finset.card_sdiff_of_subset
      (twelveGalleryUpgradedBaseVertices_subset_offLine_four G),
    twelveGalleryOffLineMultiplicityVertices_four_card G census,
    hbaseImage]

def twelveGalleryTypeABaseLabels : Finset (Finset GalleryLineLabel) :=
  (Finset.univ.image twelveGalleryUpperBaseLabels) ∪
    Finset.univ.image twelveGalleryLowerBaseLabels

def twelveGalleryTypeARungPairs : Finset (Finset GalleryLineLabel) :=
  Finset.univ.image fun i : Fin 4 =>
    {twelveGalleryALabel i, twelveGalleryBLabel i}

/-- Pairs already accounted for by the six displayed bases or by a rung on
the distinguished line. -/
def twelveGalleryTypeAUsedPairs : Finset (Finset GalleryLineLabel) :=
  twelveGalleryTypeARungPairs ∪
    twelveGalleryTypeABaseLabels.biUnion fun B => B.powersetCard 2

private def twelveGalleryLabelCode : GalleryLineLabel → Nat
  | .inl (.inl i) => i
  | .inl (.inr i) => 4 + i
  | .inr i => 8 + i

private def twelveGalleryTypeAUsedCodePairs : List (Nat × Nat) :=
  [(0, 1), (1, 2), (2, 3),
    (4, 5), (5, 6), (6, 7),
    (0, 4), (1, 5), (2, 6), (3, 7),
    (0, 8), (1, 8), (4, 8), (5, 8),
    (1, 9), (2, 9), (5, 9), (6, 9),
    (2, 10), (3, 10), (6, 10), (7, 10)]

private def twelveGalleryTypeAFastUsedPair
    (x y : GalleryLineLabel) : Bool :=
  twelveGalleryTypeAUsedCodePairs.contains
    (min (twelveGalleryLabelCode x) (twelveGalleryLabelCode y),
      max (twelveGalleryLabelCode x) (twelveGalleryLabelCode y))

private theorem twelveGalleryTypeABaseLabels_eq_image_slots :
    twelveGalleryTypeABaseLabels =
      Finset.univ.image twelveGalleryBaseLabels := by
  classical
  decide

private theorem twelveGalleryTypeAFastUsedPair_A0
    (y : GalleryLineLabel) :
    twelveGalleryTypeAFastUsedPair (twelveGalleryALabel 0) y =
      decide (({twelveGalleryALabel 0, y} : Finset GalleryLineLabel) ∈
        twelveGalleryTypeAUsedPairs) := by
  fin_cases y <;> decide

private theorem twelveGalleryTypeAFastUsedPair_A1
    (y : GalleryLineLabel) :
    twelveGalleryTypeAFastUsedPair (twelveGalleryALabel 1) y =
      decide (({twelveGalleryALabel 1, y} : Finset GalleryLineLabel) ∈
        twelveGalleryTypeAUsedPairs) := by
  fin_cases y <;> decide

private theorem twelveGalleryTypeAFastUsedPair_A2
    (y : GalleryLineLabel) :
    twelveGalleryTypeAFastUsedPair (twelveGalleryALabel 2) y =
      decide (({twelveGalleryALabel 2, y} : Finset GalleryLineLabel) ∈
        twelveGalleryTypeAUsedPairs) := by
  fin_cases y <;> decide

private theorem twelveGalleryTypeAFastUsedPair_A3
    (y : GalleryLineLabel) :
    twelveGalleryTypeAFastUsedPair (twelveGalleryALabel 3) y =
      decide (({twelveGalleryALabel 3, y} : Finset GalleryLineLabel) ∈
        twelveGalleryTypeAUsedPairs) := by
  fin_cases y <;> decide

private theorem twelveGalleryTypeAFastUsedPair_B0
    (y : GalleryLineLabel) :
    twelveGalleryTypeAFastUsedPair (twelveGalleryBLabel 0) y =
      decide (({twelveGalleryBLabel 0, y} : Finset GalleryLineLabel) ∈
        twelveGalleryTypeAUsedPairs) := by
  fin_cases y <;> decide

private theorem twelveGalleryTypeAFastUsedPair_B1
    (y : GalleryLineLabel) :
    twelveGalleryTypeAFastUsedPair (twelveGalleryBLabel 1) y =
      decide (({twelveGalleryBLabel 1, y} : Finset GalleryLineLabel) ∈
        twelveGalleryTypeAUsedPairs) := by
  fin_cases y <;> decide

private theorem twelveGalleryTypeAFastUsedPair_B2
    (y : GalleryLineLabel) :
    twelveGalleryTypeAFastUsedPair (twelveGalleryBLabel 2) y =
      decide (({twelveGalleryBLabel 2, y} : Finset GalleryLineLabel) ∈
        twelveGalleryTypeAUsedPairs) := by
  fin_cases y <;> decide

private theorem twelveGalleryTypeAFastUsedPair_B3
    (y : GalleryLineLabel) :
    twelveGalleryTypeAFastUsedPair (twelveGalleryBLabel 3) y =
      decide (({twelveGalleryBLabel 3, y} : Finset GalleryLineLabel) ∈
        twelveGalleryTypeAUsedPairs) := by
  fin_cases y <;> decide

private theorem twelveGalleryTypeAFastUsedPair_C0
    (y : GalleryLineLabel) :
    twelveGalleryTypeAFastUsedPair (twelveGalleryCLabel 0) y =
      decide (({twelveGalleryCLabel 0, y} : Finset GalleryLineLabel) ∈
        twelveGalleryTypeAUsedPairs) := by
  fin_cases y <;> decide

private theorem twelveGalleryTypeAFastUsedPair_C1
    (y : GalleryLineLabel) :
    twelveGalleryTypeAFastUsedPair (twelveGalleryCLabel 1) y =
      decide (({twelveGalleryCLabel 1, y} : Finset GalleryLineLabel) ∈
        twelveGalleryTypeAUsedPairs) := by
  fin_cases y <;> decide

private theorem twelveGalleryTypeAFastUsedPair_C2
    (y : GalleryLineLabel) :
    twelveGalleryTypeAFastUsedPair (twelveGalleryCLabel 2) y =
      decide (({twelveGalleryCLabel 2, y} : Finset GalleryLineLabel) ∈
        twelveGalleryTypeAUsedPairs) := by
  fin_cases y <;> decide

private theorem twelveGalleryTypeAFastUsedPair_eq_decide
    (x y : GalleryLineLabel) :
    twelveGalleryTypeAFastUsedPair x y =
      decide (({x, y} : Finset GalleryLineLabel) ∈
        twelveGalleryTypeAUsedPairs) := by
  fin_cases x
  all_goals
    first
    | exact twelveGalleryTypeAFastUsedPair_A0 y
    | exact twelveGalleryTypeAFastUsedPair_A1 y
    | exact twelveGalleryTypeAFastUsedPair_A2 y
    | exact twelveGalleryTypeAFastUsedPair_A3 y
    | exact twelveGalleryTypeAFastUsedPair_B0 y
    | exact twelveGalleryTypeAFastUsedPair_B1 y
    | exact twelveGalleryTypeAFastUsedPair_B2 y
    | exact twelveGalleryTypeAFastUsedPair_B3 y
    | exact twelveGalleryTypeAFastUsedPair_C0 y
    | exact twelveGalleryTypeAFastUsedPair_C1 y
    | exact twelveGalleryTypeAFastUsedPair_C2 y

theorem twelveGalleryTypeAUsedPair_has_owner
    {Line : Type u} [Fintype Line] [DecidableEq Line]
    {A : FiniteProjectiveLineArrangement Line} {ell : Line}
    (G : A.LabelledFourStripGalleryEntrance ell)
    {P : Finset GalleryLineLabel}
    (hP : P ∈ twelveGalleryTypeAUsedPairs) :
    (∃ i : Fin 4, P ⊆ G.labelSupport (G.rungVertex i)) ∨
      (∃ s : TwelveGalleryTypeABaseSlot,
        P ⊆ G.labelSupport (twelveGalleryBaseVertex G s)) := by
  classical
  rcases Finset.mem_union.mp hP with hRung | hBase
  · obtain ⟨i, _hi, rfl⟩ := Finset.mem_image.mp hRung
    left
    refine ⟨i, ?_⟩
    rw [labelSupport_rungVertex_eq]
  · obtain ⟨B, hB, hPB⟩ := Finset.mem_biUnion.mp hBase
    rw [twelveGalleryTypeABaseLabels_eq_image_slots] at hB
    obtain ⟨s, _hs, rfl⟩ := Finset.mem_image.mp hB
    right
    refine ⟨s, (Finset.mem_powersetCard.mp hPB).1.trans ?_⟩
    exact twelveGalleryBaseLabels_subset_labelSupport G s

theorem eq_of_galleryPair_subset_two_labelSupports
    {Line : Type u} [Fintype Line] [DecidableEq Line]
    {A : FiniteProjectiveLineArrangement Line} {ell : Line}
    (G : A.LabelledFourStripGalleryEntrance ell)
    {P : Finset GalleryLineLabel} {q r : RealProjectivePoint}
    (hcard : P.card = 2)
    (hPq : P ⊆ G.labelSupport q) (hPr : P ⊆ G.labelSupport r) :
    q = r := by
  obtain ⟨x, y, hxy, rfl⟩ := Finset.card_eq_two.mp hcard
  apply G.eq_of_two_common_labels hxy
  · exact hPq (by simp)
  · exact hPq (by simp)
  · exact hPr (by simp)
  · exact hPr (by simp)

def twelveGalleryTypeAH : Finset (Finset GalleryLineLabel) :=
  {{twelveGalleryALabel 0, twelveGalleryBLabel 1},
   {twelveGalleryALabel 0, twelveGalleryCLabel 1},
   {twelveGalleryALabel 1, twelveGalleryBLabel 0},
   {twelveGalleryALabel 2, twelveGalleryBLabel 3},
   {twelveGalleryALabel 3, twelveGalleryBLabel 2},
   {twelveGalleryBLabel 0, twelveGalleryCLabel 1},
   {twelveGalleryCLabel 0, twelveGalleryCLabel 1}}

noncomputable def twelveGalleryCutEdgesAt
    {Line : Type u} [Fintype Line] [DecidableEq Line]
    {A : FiniteProjectiveLineArrangement Line} {ell : Line}
    (G : A.LabelledFourStripGalleryEntrance ell)
    (q : RealProjectivePoint) : Finset (Finset GalleryLineLabel) :=
  (G.labelSupport q).powersetCard 2 ∩ twelveGalleryTypeAH

noncomputable def twelveGalleryConsumedCutEdges
    {Line : Type u} [Fintype Line] [DecidableEq Line]
    (A : FiniteProjectiveLineArrangement Line) (ell : Line)
    (G : A.LabelledFourStripGalleryEntrance ell) :
    Finset (Finset GalleryLineLabel) :=
  (twelveGalleryOffLineMultiplicityVertices A ell 4).biUnion
    (twelveGalleryCutEdgesAt G)

def TwelveGalleryTypeAResidualClique
    (S : Finset GalleryLineLabel) : Prop :=
  ∀ P ∈ S.powersetCard 2, P ∉ twelveGalleryTypeAUsedPairs

private abbrev twelveGalleryResidualCliqueDecidable
    (S : Finset GalleryLineLabel) :
    Decidable (TwelveGalleryTypeAResidualClique S) := by
  apply decidable_of_iff
    (∀ P : {P // P ∈ S.powersetCard 2},
      P.1 ∉ twelveGalleryTypeAUsedPairs)
  unfold TwelveGalleryTypeAResidualClique
  constructor
  · intro h P hP
    exact h ⟨P, hP⟩
  · intro h P
    exact h P.1 P.2

attribute [local instance] twelveGalleryResidualCliqueDecidable

def TwelveGalleryTypeAUpgradesBase
    (S : Finset GalleryLineLabel) : Prop :=
  ∃ B ∈ twelveGalleryTypeABaseLabels, B ⊆ S

private abbrev twelveGalleryUpgradesBaseDecidable
    (S : Finset GalleryLineLabel) :
    Decidable (TwelveGalleryTypeAUpgradesBase S) := by
  apply decidable_of_iff
    (∃ B : {B // B ∈ twelveGalleryTypeABaseLabels}, B.1 ⊆ S)
  unfold TwelveGalleryTypeAUpgradesBase
  constructor
  · rintro ⟨B, hsub⟩
    exact ⟨B.1, B.2, hsub⟩
  · rintro ⟨B, hB, hsub⟩
    exact ⟨⟨B, hB⟩, hsub⟩

attribute [local instance] twelveGalleryUpgradesBaseDecidable

private def TwelveGalleryTypeAFastResidualClique
    (S : Finset GalleryLineLabel) : Prop :=
  ∀ x ∈ S, ∀ y ∈ S, x ≠ y →
    twelveGalleryTypeAFastUsedPair x y = false

private abbrev twelveGalleryFastResidualCliqueDecidable
    (S : Finset GalleryLineLabel) :
    Decidable (TwelveGalleryTypeAFastResidualClique S) := by
  apply decidable_of_iff
    (∀ x : {x // x ∈ S}, ∀ y : {y // y ∈ S}, x.1 ≠ y.1 →
      twelveGalleryTypeAFastUsedPair x.1 y.1 = false)
  unfold TwelveGalleryTypeAFastResidualClique
  constructor
  · intro h x hx y hy hxy
    exact h ⟨x, hx⟩ ⟨y, hy⟩ hxy
  · intro h x y hxy
    exact h x.1 x.2 y.1 y.2 hxy

attribute [local instance] twelveGalleryFastResidualCliqueDecidable

private theorem twelveGalleryTypeA_fastResidual_of_residual
    {S : Finset GalleryLineLabel}
    (h : TwelveGalleryTypeAResidualClique S) :
    TwelveGalleryTypeAFastResidualClique S := by
  intro x hx y hy hxy
  cases hfast : twelveGalleryTypeAFastUsedPair x y with
  | false => rfl
  | true =>
      exfalso
      have hused : ({x, y} : Finset GalleryLineLabel) ∈
          twelveGalleryTypeAUsedPairs := by
        exact of_decide_eq_true
          (twelveGalleryTypeAFastUsedPair_eq_decide x y ▸ hfast)
      have hpairSub : ({x, y} : Finset GalleryLineLabel) ⊆ S := by
        intro z hz
        simp only [Finset.mem_insert, Finset.mem_singleton] at hz
        rcases hz with rfl | rfl
        · exact hx
        · exact hy
      exact h ({x, y})
        (Finset.mem_powersetCard.mpr
          ⟨hpairSub, Finset.card_pair hxy⟩)
        hused

private def TwelveGalleryTypeAFastUpgradesBase
    (S : Finset GalleryLineLabel) : Prop :=
  ∃ s : TwelveGalleryTypeABaseSlot,
    twelveGalleryBaseLabels s ⊆ S

private abbrev twelveGalleryFastUpgradesBaseDecidable
    (S : Finset GalleryLineLabel) :
    Decidable (TwelveGalleryTypeAFastUpgradesBase S) := by
  apply decidable_of_iff
    (∃ s : {s // s ∈ (Finset.univ : Finset TwelveGalleryTypeABaseSlot)},
      twelveGalleryBaseLabels s.1 ⊆ S)
  unfold TwelveGalleryTypeAFastUpgradesBase
  constructor
  · rintro ⟨s, hs⟩
    exact ⟨s.1, hs⟩
  · rintro ⟨s, hs⟩
    exact ⟨⟨s, Finset.mem_univ _⟩, hs⟩

attribute [local instance] twelveGalleryFastUpgradesBaseDecidable

private theorem twelveGalleryTypeA_not_fastUpgrades_of_not_upgrades
    {S : Finset GalleryLineLabel}
    (h : ¬ TwelveGalleryTypeAUpgradesBase S) :
    ¬ TwelveGalleryTypeAFastUpgradesBase S := by
  rintro ⟨s, hs⟩
  apply h
  refine ⟨twelveGalleryBaseLabels s, ?_, hs⟩
  rw [twelveGalleryTypeABaseLabels_eq_image_slots]
  exact Finset.mem_image.mpr ⟨s, Finset.mem_univ _, rfl⟩

theorem labelSupport_card_eq_multiplicity_of_not_incident
    {Line : Type u} [Fintype Line] [DecidableEq Line]
    {A : FiniteProjectiveLineArrangement Line} {ell : Line}
    (G : A.LabelledFourStripGalleryEntrance ell)
    (q : RealProjectivePoint) (hqEll : ¬ A.Incident q ell) :
    (G.labelSupport q).card = A.multiplicity q := by
  have h := G.labelSupport_card_add_indicator q
  simpa [hqEll] using h

theorem twelveGalleryResidualTriple_support_spec
    {Line : Type u} [Fintype Line] [DecidableEq Line]
    {A : FiniteProjectiveLineArrangement Line} {ell : Line}
    (G : A.LabelledFourStripGalleryEntrance ell)
    (census : TwelveGalleryTypeAActualCensus A)
    {q : RealProjectivePoint}
    (hq : q ∈ twelveGalleryResidualTripleVertices A ell G) :
    (G.labelSupport q).card = 3 ∧
      TwelveGalleryTypeAResidualClique (G.labelSupport q) := by
  classical
  have hqParts := Finset.mem_sdiff.mp hq
  have hqOff := Finset.mem_filter.mp hqParts.1
  have hqMult := Finset.mem_filter.mp hqOff.1
  have hqCard : (G.labelSupport q).card = 3 := by
    rw [labelSupport_card_eq_multiplicity_of_not_incident G q hqOff.2]
    exact hqMult.2
  refine ⟨hqCard, ?_⟩
  intro P hP hPUsed
  have hPcard : P.card = 2 := (Finset.mem_powersetCard.mp hP).2
  have hPsub : P ⊆ G.labelSupport q :=
    (Finset.mem_powersetCard.mp hP).1
  rcases twelveGalleryTypeAUsedPair_has_owner G hPUsed with
      ⟨i, hi⟩ | ⟨s, hs⟩
  · have hqr : q = G.rungVertex i :=
      eq_of_galleryPair_subset_two_labelSupports G hPcard hPsub hi
    apply hqOff.2
    rw [hqr]
    exact (G.rungIncident_iff i ell).2 (Or.inl rfl)
  · have hqb : q = twelveGalleryBaseVertex G s :=
      eq_of_galleryPair_subset_two_labelSupports G hPcard hPsub hs
    have hsNotUpgraded : s ∉ twelveGalleryUpgradedBaseSlots G := by
      intro hsUpgraded
      have hsFour := (Finset.mem_filter.mp hsUpgraded).2
      rw [← hqb] at hsFour
      omega
    have hsExact : s ∈ twelveGalleryExactBaseSlots G :=
      Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hsNotUpgraded⟩
    apply hqParts.2
    exact Finset.mem_image.mpr ⟨s, hsExact, hqb.symm⟩

theorem twelveGalleryNonupgradeQuad_support_spec
    {Line : Type u} [Fintype Line] [DecidableEq Line]
    {A : FiniteProjectiveLineArrangement Line} {ell : Line}
    (G : A.LabelledFourStripGalleryEntrance ell)
    (census : TwelveGalleryTypeAActualCensus A)
    {q : RealProjectivePoint}
    (hq : q ∈ twelveGalleryNonupgradeQuadVertices A ell G) :
    (G.labelSupport q).card = 4 ∧
      TwelveGalleryTypeAResidualClique (G.labelSupport q) ∧
      ¬ TwelveGalleryTypeAUpgradesBase (G.labelSupport q) := by
  classical
  have hqParts := Finset.mem_sdiff.mp hq
  have hqOff := Finset.mem_filter.mp hqParts.1
  have hqMult := Finset.mem_filter.mp hqOff.1
  have hqCard : (G.labelSupport q).card = 4 := by
    rw [labelSupport_card_eq_multiplicity_of_not_incident G q hqOff.2]
    exact hqMult.2
  have hresidual : TwelveGalleryTypeAResidualClique (G.labelSupport q) := by
    intro P hP hPUsed
    have hPcard : P.card = 2 := (Finset.mem_powersetCard.mp hP).2
    have hPsub : P ⊆ G.labelSupport q :=
      (Finset.mem_powersetCard.mp hP).1
    rcases twelveGalleryTypeAUsedPair_has_owner G hPUsed with
        ⟨i, hi⟩ | ⟨s, hs⟩
    · have hqr : q = G.rungVertex i :=
        eq_of_galleryPair_subset_two_labelSupports G hPcard hPsub hi
      apply hqOff.2
      rw [hqr]
      exact (G.rungIncident_iff i ell).2 (Or.inl rfl)
    · have hqb : q = twelveGalleryBaseVertex G s :=
        eq_of_galleryPair_subset_two_labelSupports G hPcard hPsub hs
      have hsUpgraded : s ∈ twelveGalleryUpgradedBaseSlots G :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
          rw [← hqb]
          exact hqCard⟩
      apply hqParts.2
      exact Finset.mem_image.mpr ⟨s, hsUpgraded, hqb.symm⟩
  refine ⟨hqCard, hresidual, ?_⟩
  rintro ⟨B, hB, hBsub⟩
  rw [twelveGalleryTypeABaseLabels_eq_image_slots] at hB
  obtain ⟨s, _hs, rfl⟩ := Finset.mem_image.mp hB
  have hbaseSub := twelveGalleryBaseLabels_subset_labelSupport G s
  have hthree : (twelveGalleryBaseLabels s).card = 3 :=
    twelveGalleryBaseLabels_card s
  obtain ⟨x, y, z, hxy, hxz, hyz, hbase⟩ :=
    Finset.card_eq_three.mp hthree
  rw [hbase] at hBsub hbaseSub
  have hxyPair : ({x, y} : Finset GalleryLineLabel).card = 2 := by
    simp [hxy]
  have hqb : q = twelveGalleryBaseVertex G s :=
    eq_of_galleryPair_subset_two_labelSupports G hxyPair
      (fun w hw => hBsub (by
        have hw' : w = x ∨ w = y := by simpa using hw
        simpa using hw'.imp_right Or.inl))
      (fun w hw => hbaseSub (by
        have hw' : w = x ∨ w = y := by simpa using hw
        simpa using hw'.imp_right Or.inl))
  have hsUpgraded : s ∈ twelveGalleryUpgradedBaseSlots G :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
      rw [← hqb]
      exact hqCard⟩
  apply hqParts.2
  exact Finset.mem_image.mpr ⟨s, hsUpgraded, hqb.symm⟩

def twelveGalleryTypeAX : Finset GalleryLineLabel :=
  {twelveGalleryALabel 0, twelveGalleryALabel 2,
    twelveGalleryBLabel 1, twelveGalleryBLabel 3}

def twelveGalleryTypeAY : Finset GalleryLineLabel :=
  {twelveGalleryALabel 1, twelveGalleryALabel 3,
    twelveGalleryBLabel 0, twelveGalleryBLabel 2}

private def twelveGalleryResidualThreeCheck
    (U : Finset GalleryLineLabel) : Bool :=
  decide (TwelveGalleryTypeAFastResidualClique U →
    (U.powersetCard 2 ∩ twelveGalleryTypeAH).card = 1)

private theorem twelveGalleryResidualThreeCheck_chunk_zero :
    (twelveGalleryTypeASubsetChunk 3 0 30).all
      twelveGalleryResidualThreeCheck = true := by
  decide_cbv

private theorem twelveGalleryResidualThreeCheck_chunk_thirty :
    (twelveGalleryTypeASubsetChunk 3 30 30).all
      twelveGalleryResidualThreeCheck = true := by
  decide_cbv

private theorem twelveGalleryResidualThreeCheck_chunk_sixty :
    (twelveGalleryTypeASubsetChunk 3 60 30).all
      twelveGalleryResidualThreeCheck = true := by
  decide_cbv

private theorem twelveGalleryResidualThreeCheck_chunk_ninety :
    (twelveGalleryTypeASubsetChunk 3 90 30).all
      twelveGalleryResidualThreeCheck = true := by
  decide_cbv

private theorem twelveGalleryResidualThreeCheck_chunk_oneTwenty :
    (twelveGalleryTypeASubsetChunk 3 120 30).all
      twelveGalleryResidualThreeCheck = true := by
  decide_cbv

private theorem twelveGalleryResidualThreeCheck_tail :
    ((twelveGalleryTypeASubsets 3).drop 150).all
      twelveGalleryResidualThreeCheck = true := by
  decide_cbv

private theorem twelveGalleryResidualThreeCheck_all :
    (twelveGalleryTypeASubsets 3).all
      twelveGalleryResidualThreeCheck = true := by
  apply list_all_eq_true_of_take_of_drop 30
  · simpa [twelveGalleryTypeASubsetChunk] using
      twelveGalleryResidualThreeCheck_chunk_zero
  apply list_all_eq_true_of_take_of_drop 30
  · simpa [twelveGalleryTypeASubsetChunk] using
      twelveGalleryResidualThreeCheck_chunk_thirty
  apply list_all_eq_true_of_take_of_drop 30
  · simpa [twelveGalleryTypeASubsetChunk] using
      twelveGalleryResidualThreeCheck_chunk_sixty
  apply list_all_eq_true_of_take_of_drop 30
  · simpa [twelveGalleryTypeASubsetChunk] using
      twelveGalleryResidualThreeCheck_chunk_ninety
  apply list_all_eq_true_of_take_of_drop 30
  · simpa [twelveGalleryTypeASubsetChunk] using
      twelveGalleryResidualThreeCheck_chunk_oneTwenty
  simpa using twelveGalleryResidualThreeCheck_tail

private theorem twelveGalleryTypeA_residual_three_table :
    ∀ T ∈ (Finset.univ : Finset GalleryLineLabel).powersetCard 3,
      TwelveGalleryTypeAResidualClique T →
        (T.powersetCard 2 ∩ twelveGalleryTypeAH).card = 1 := by
  intro T hT
  have hcheck :
      (twelveGalleryTypeASubsets 3).all
        twelveGalleryResidualThreeCheck = true :=
    twelveGalleryResidualThreeCheck_all
  have hTcheck := (List.all_eq_true.mp hcheck) T
    (mem_twelveGalleryTypeASubsets_of_card T
      (Finset.mem_powersetCard.mp hT).2)
  have hTcheck' :
      decide (TwelveGalleryTypeAFastResidualClique T →
        (T.powersetCard 2 ∩ twelveGalleryTypeAH).card = 1) = true := by
    simpa only [twelveGalleryResidualThreeCheck] using hTcheck
  intro hresidual
  exact (of_decide_eq_true hTcheck')
    (twelveGalleryTypeA_fastResidual_of_residual hresidual)

/-- Every residual exact triple uses exactly one edge of the seven-edge
cut.  The closed check has only the `11 choose 3` literal rows. -/
theorem twelveGalleryTypeA_residual_three_has_one_H
    (T : Finset GalleryLineLabel) (hcard : T.card = 3)
    (hresidual : TwelveGalleryTypeAResidualClique T) :
    (T.powersetCard 2 ∩ twelveGalleryTypeAH).card = 1 := by
  apply twelveGalleryTypeA_residual_three_table T
  · simp [hcard]
  · exact hresidual

private def twelveGalleryCResidualColor
    (i : Fin 3) (x : GalleryLineLabel) : Bool :=
  if i = 2 then
    [1, 5, 9].contains (twelveGalleryLabelCode x)
  else
    [3, 7, 10].contains (twelveGalleryLabelCode x)

private def twelveGalleryABColumn : GalleryLineLabel → Fin 4
  | .inl (.inl i) => i
  | .inl (.inr i) => i
  | .inr i => i.castSucc

private theorem twelveGallery_fast_not_mem
    {Q : Finset GalleryLineLabel}
    (hfast : TwelveGalleryTypeAFastResidualClique Q)
    {x y : GalleryLineLabel} (hx : x ∈ Q) (hxy : x ≠ y)
    (hused : twelveGalleryTypeAFastUsedPair x y = true) :
    y ∉ Q := by
  intro hy
  have hfalse := hfast x hx y hy hxy
  rw [hused] at hfalse
  exact Bool.noConfusion hfalse

private theorem twelveGalleryCResidualColor_used_C0
    (x y : GalleryLineLabel) :
    (twelveGalleryTypeAFastUsedPair (twelveGalleryCLabel 0) x = false ∧
      twelveGalleryTypeAFastUsedPair (twelveGalleryCLabel 0) y = false ∧
      x ≠ twelveGalleryCLabel 0 ∧ y ≠ twelveGalleryCLabel 0 ∧ x ≠ y ∧
      twelveGalleryCResidualColor 0 x =
        twelveGalleryCResidualColor 0 y) →
      twelveGalleryTypeAFastUsedPair x y = true := by
  fin_cases x <;> fin_cases y <;> decide

private theorem twelveGalleryCResidualColor_used_C1
    (x y : GalleryLineLabel) :
    (twelveGalleryTypeAFastUsedPair (twelveGalleryCLabel 1) x = false ∧
      twelveGalleryTypeAFastUsedPair (twelveGalleryCLabel 1) y = false ∧
      x ≠ twelveGalleryCLabel 1 ∧ y ≠ twelveGalleryCLabel 1 ∧ x ≠ y ∧
      twelveGalleryCResidualColor 1 x =
        twelveGalleryCResidualColor 1 y) →
      twelveGalleryTypeAFastUsedPair x y = true := by
  fin_cases x <;> fin_cases y <;> decide

private theorem twelveGalleryCResidualColor_used_C2
    (x y : GalleryLineLabel) :
    (twelveGalleryTypeAFastUsedPair (twelveGalleryCLabel 2) x = false ∧
      twelveGalleryTypeAFastUsedPair (twelveGalleryCLabel 2) y = false ∧
      x ≠ twelveGalleryCLabel 2 ∧ y ≠ twelveGalleryCLabel 2 ∧ x ≠ y ∧
      twelveGalleryCResidualColor 2 x =
        twelveGalleryCResidualColor 2 y) →
      twelveGalleryTypeAFastUsedPair x y = true := by
  fin_cases x <;> fin_cases y <;> decide

private theorem twelveGalleryCResidualColor_injective
    {Q : Finset GalleryLineLabel}
    (hfast : TwelveGalleryTypeAFastResidualClique Q)
    (i : Fin 3) (hi : twelveGalleryCLabel i ∈ Q) :
    Set.InjOn (twelveGalleryCResidualColor i)
      (Q.erase (twelveGalleryCLabel i) : Set GalleryLineLabel) := by
  intro x hx y hy hcolor
  have hxerase := Finset.mem_erase.mp hx
  have hyerase := Finset.mem_erase.mp hy
  have hcx := hfast (twelveGalleryCLabel i) hi x hxerase.2
    hxerase.1.symm
  have hcy := hfast (twelveGalleryCLabel i) hi y hyerase.2
    hyerase.1.symm
  by_contra hxy
  have hxyFast := hfast x hxerase.2 y hyerase.2 hxy
  have hused : twelveGalleryTypeAFastUsedPair x y = true := by
    fin_cases i
    · exact twelveGalleryCResidualColor_used_C0 x y
        ⟨hcx, hcy, hxerase.1, hyerase.1, hxy, hcolor⟩
    · exact twelveGalleryCResidualColor_used_C1 x y
        ⟨hcx, hcy, hxerase.1, hyerase.1, hxy, hcolor⟩
    · exact twelveGalleryCResidualColor_used_C2 x y
        ⟨hcx, hcy, hxerase.1, hyerase.1, hxy, hcolor⟩
  rw [hused] at hxyFast
  exact Bool.noConfusion hxyFast

private theorem twelveGalleryABColumn_same_used
    (x y : GalleryLineLabel) :
    (x ≠ twelveGalleryCLabel 0 ∧ x ≠ twelveGalleryCLabel 1 ∧
      x ≠ twelveGalleryCLabel 2 ∧ y ≠ twelveGalleryCLabel 0 ∧
      y ≠ twelveGalleryCLabel 1 ∧ y ≠ twelveGalleryCLabel 2 ∧ x ≠ y ∧
      twelveGalleryABColumn x = twelveGalleryABColumn y) →
      twelveGalleryTypeAFastUsedPair x y = true := by
  fin_cases x <;> fin_cases y <;> decide

private theorem twelveGalleryABColumn_injective
    {Q : Finset GalleryLineLabel}
    (hfast : TwelveGalleryTypeAFastResidualClique Q)
    (hnoC : ∀ i : Fin 3, twelveGalleryCLabel i ∉ Q) :
    Set.InjOn twelveGalleryABColumn (Q : Set GalleryLineLabel) := by
  intro x hx y hy hcolumn
  have hC0 := hnoC 0
  have hC1 := hnoC 1
  have hC2 := hnoC 2
  by_contra hxy
  have hxyFast := hfast x hx y hy hxy
  have hxC0 : x ≠ twelveGalleryCLabel 0 := by
    intro heq
    exact hC0 (heq ▸ hx)
  have hxC1 : x ≠ twelveGalleryCLabel 1 := by
    intro heq
    exact hC1 (heq ▸ hx)
  have hxC2 : x ≠ twelveGalleryCLabel 2 := by
    intro heq
    exact hC2 (heq ▸ hx)
  have hyC0 : y ≠ twelveGalleryCLabel 0 := by
    intro heq
    exact hC0 (heq ▸ hy)
  have hyC1 : y ≠ twelveGalleryCLabel 1 := by
    intro heq
    exact hC1 (heq ▸ hy)
  have hyC2 : y ≠ twelveGalleryCLabel 2 := by
    intro heq
    exact hC2 (heq ▸ hy)
  have hused := twelveGalleryABColumn_same_used x y
    ⟨hxC0, hxC1, hxC2, hyC0, hyC1, hyC2, hxy, hcolumn⟩
  rw [hused] at hxyFast
  exact Bool.noConfusion hxyFast

private theorem twelveGalleryTypeA_fastResidual_four_eq_X_or_Y
    {Q : Finset GalleryLineLabel} (hcard : Q.card = 4)
    (hfast : TwelveGalleryTypeAFastResidualClique Q) :
    Q = twelveGalleryTypeAX ∨ Q = twelveGalleryTypeAY := by
  have hnoC : ∀ i : Fin 3, twelveGalleryCLabel i ∉ Q := by
    intro i hi
    have hinj := twelveGalleryCResidualColor_injective hfast i hi
    have heraseCard : (Q.erase (twelveGalleryCLabel i)).card = 3 := by
      rw [Finset.card_erase_of_mem hi, hcard]
    have himageCard :
        ((Q.erase (twelveGalleryCLabel i)).image
          (twelveGalleryCResidualColor i)).card = 3 := by
      rw [Finset.card_image_iff.mpr hinj, heraseCard]
    have hle :
        ((Q.erase (twelveGalleryCLabel i)).image
          (twelveGalleryCResidualColor i)).card ≤
          (Finset.univ : Finset Bool).card :=
      Finset.card_le_card (Finset.subset_univ _)
    rw [himageCard] at hle
    norm_num at hle
  have hcolumnInj := twelveGalleryABColumn_injective hfast hnoC
  have himageCard : (Q.image twelveGalleryABColumn).card = 4 := by
    rw [Finset.card_image_iff.mpr hcolumnInj, hcard]
  have himage : Q.image twelveGalleryABColumn = Finset.univ := by
    apply Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
    rw [himageCard]
    decide
  have hchoice (i : Fin 4) :
      twelveGalleryALabel i ∈ Q ∨ twelveGalleryBLabel i ∈ Q := by
    have hi : i ∈ Q.image twelveGalleryABColumn := by
      rw [himage]
      exact Finset.mem_univ i
    obtain ⟨x, hx, hxi⟩ := Finset.mem_image.mp hi
    have hC0 := hnoC 0
    have hC1 := hnoC 1
    have hC2 := hnoC 2
    fin_cases i <;> fin_cases x <;>
      simp_all [twelveGalleryABColumn, twelveGalleryALabel,
        twelveGalleryBLabel, twelveGalleryCLabel]
  rcases hchoice 0 with hA0 | hB0
  · have hnA1 : twelveGalleryALabel 1 ∉ Q :=
      twelveGallery_fast_not_mem hfast hA0 (by decide) (by decide)
    have hB1 : twelveGalleryBLabel 1 ∈ Q :=
      (hchoice 1).resolve_left hnA1
    have hnB2 : twelveGalleryBLabel 2 ∉ Q :=
      twelveGallery_fast_not_mem hfast hB1 (by decide) (by decide)
    have hA2 : twelveGalleryALabel 2 ∈ Q :=
      (hchoice 2).resolve_right hnB2
    have hnA3 : twelveGalleryALabel 3 ∉ Q :=
      twelveGallery_fast_not_mem hfast hA2 (by decide) (by decide)
    have hB3 : twelveGalleryBLabel 3 ∈ Q :=
      (hchoice 3).resolve_left hnA3
    left
    symm
    apply Finset.eq_of_subset_of_card_le
    · intro x hx
      simp only [twelveGalleryTypeAX, Finset.mem_insert,
        Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact hA0
      · exact hA2
      · exact hB1
      · exact hB3
    · rw [hcard]
      decide
  · have hnB1 : twelveGalleryBLabel 1 ∉ Q :=
      twelveGallery_fast_not_mem hfast hB0 (by decide) (by decide)
    have hA1 : twelveGalleryALabel 1 ∈ Q :=
      (hchoice 1).resolve_right hnB1
    have hnA2 : twelveGalleryALabel 2 ∉ Q :=
      twelveGallery_fast_not_mem hfast hA1 (by decide) (by decide)
    have hB2 : twelveGalleryBLabel 2 ∈ Q :=
      (hchoice 2).resolve_left hnA2
    have hnB3 : twelveGalleryBLabel 3 ∉ Q :=
      twelveGallery_fast_not_mem hfast hB2 (by decide) (by decide)
    have hA3 : twelveGalleryALabel 3 ∈ Q :=
      (hchoice 3).resolve_right hnB3
    right
    symm
    apply Finset.eq_of_subset_of_card_le
    · intro x hx
      simp only [twelveGalleryTypeAY, Finset.mem_insert,
        Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact hA1
      · exact hA3
      · exact hB0
      · exact hB2
    · rw [hcard]
      decide

private theorem twelveGalleryTypeA_nonupgrade_four_table :
    ∀ Q ∈ (Finset.univ : Finset GalleryLineLabel).powersetCard 4,
      TwelveGalleryTypeAResidualClique Q →
      ¬ TwelveGalleryTypeAUpgradesBase Q →
          (Q = twelveGalleryTypeAX ∨ Q = twelveGalleryTypeAY) ∧
          (Q.powersetCard 2 ∩ twelveGalleryTypeAH).card = 2 := by
  intro Q hQ hresidual _hnonupgrade
  have hcard := (Finset.mem_powersetCard.mp hQ).2
  have hclass := twelveGalleryTypeA_fastResidual_four_eq_X_or_Y hcard
    (twelveGalleryTypeA_fastResidual_of_residual hresidual)
  rcases hclass with hX | hY
  · subst Q
    exact ⟨Or.inl rfl, by decide⟩
  · subst Q
    exact ⟨Or.inr rfl, by decide⟩

/-- The only non-upgrading residual quadruples are `X,Y`, and each consumes
two distinct cut edges. -/
theorem twelveGalleryTypeA_nonupgrade_four_eq_X_or_Y_and_cost_two
    (Q : Finset GalleryLineLabel) (hcard : Q.card = 4)
    (hresidual : TwelveGalleryTypeAResidualClique Q)
    (hnonupgrade : ¬ TwelveGalleryTypeAUpgradesBase Q) :
    (Q = twelveGalleryTypeAX ∨ Q = twelveGalleryTypeAY) ∧
      (Q.powersetCard 2 ∩ twelveGalleryTypeAH).card = 2 := by
  apply twelveGalleryTypeA_nonupgrade_four_table Q
  · simp [hcard]
  · exact hresidual
  · exact hnonupgrade

@[simp]
theorem twelveGalleryTypeAH_card : twelveGalleryTypeAH.card = 7 := by
  classical
  decide

theorem twelveGalleryCutEdgesAt_disjoint_of_ne
    {Line : Type u} [Fintype Line] [DecidableEq Line]
    {A : FiniteProjectiveLineArrangement Line} {ell : Line}
    (G : A.LabelledFourStripGalleryEntrance ell)
    {q r : RealProjectivePoint} (hqr : q ≠ r) :
    Disjoint (twelveGalleryCutEdgesAt G q)
      (twelveGalleryCutEdgesAt G r) := by
  classical
  rw [Finset.disjoint_left]
  intro P hPq hPr
  have hPq' := (Finset.mem_inter.mp hPq).1
  have hPr' := (Finset.mem_inter.mp hPr).1
  have hPcard : P.card = 2 := (Finset.mem_powersetCard.mp hPq').2
  apply hqr
  exact eq_of_galleryPair_subset_two_labelSupports G hPcard
    (Finset.mem_powersetCard.mp hPq').1
    (Finset.mem_powersetCard.mp hPr').1

theorem twelveGalleryConsumedCutEdges_subset_H
    {Line : Type u} [Fintype Line] [DecidableEq Line]
    {A : FiniteProjectiveLineArrangement Line} {ell : Line}
    (G : A.LabelledFourStripGalleryEntrance ell) :
    twelveGalleryConsumedCutEdges A ell G ⊆ twelveGalleryTypeAH := by
  classical
  intro P hP
  obtain ⟨q, _hq, hPq⟩ := Finset.mem_biUnion.mp hP
  exact (Finset.mem_inter.mp hPq).2

theorem twelveGalleryNonupgradeQuad_cutEdges_card_two
    {Line : Type u} [Fintype Line] [DecidableEq Line]
    {A : FiniteProjectiveLineArrangement Line} {ell : Line}
    (G : A.LabelledFourStripGalleryEntrance ell)
    (census : TwelveGalleryTypeAActualCensus A)
    {q : RealProjectivePoint}
    (hq : q ∈ twelveGalleryNonupgradeQuadVertices A ell G) :
    (twelveGalleryCutEdgesAt G q).card = 2 := by
  have hspec := twelveGalleryNonupgradeQuad_support_spec G census hq
  exact (twelveGalleryTypeA_nonupgrade_four_eq_X_or_Y_and_cost_two
    (G.labelSupport q) hspec.1 hspec.2.1 hspec.2.2).2

theorem twelveGallery_nonupgrade_cost_le_consumedCutEdges
    {Line : Type u} [Fintype Line] [DecidableEq Line]
    {A : FiniteProjectiveLineArrangement Line} {ell : Line}
    (G : A.LabelledFourStripGalleryEntrance ell)
    (census : TwelveGalleryTypeAActualCensus A) :
    2 * (3 - (twelveGalleryUpgradedBaseSlots G).card) ≤
      (twelveGalleryConsumedCutEdges A ell G).card := by
  classical
  let Q := twelveGalleryNonupgradeQuadVertices A ell G
  let E := fun q : RealProjectivePoint => twelveGalleryCutEdgesAt G q
  have hdisjoint : (Q : Set RealProjectivePoint).PairwiseDisjoint E := by
    intro q hq r hr hqr
    exact twelveGalleryCutEdgesAt_disjoint_of_ne G hqr
  have hunionCard : (Q.biUnion E).card = 2 * Q.card := by
    rw [Finset.card_biUnion hdisjoint]
    calc
      (∑ q ∈ Q, (E q).card) = ∑ _q ∈ Q, 2 := by
        apply Finset.sum_congr rfl
        intro q hq
        exact twelveGalleryNonupgradeQuad_cutEdges_card_two G census hq
      _ = 2 * Q.card := by simp [Nat.mul_comm]
  have hunionSub : Q.biUnion E ⊆
      twelveGalleryConsumedCutEdges A ell G := by
    intro P hP
    obtain ⟨q, hqQ, hPq⟩ := Finset.mem_biUnion.mp hP
    apply Finset.mem_biUnion.mpr
    refine ⟨q, ?_, hPq⟩
    exact (Finset.mem_sdiff.mp hqQ).1
  have hle := Finset.card_le_card hunionSub
  rw [hunionCard] at hle
  rw [twelveGalleryNonupgradeQuadVertices_card G census] at hle
  exact hle

theorem twelveGalleryResidualTriple_cutEdges_card_one
    {Line : Type u} [Fintype Line] [DecidableEq Line]
    {A : FiniteProjectiveLineArrangement Line} {ell : Line}
    (G : A.LabelledFourStripGalleryEntrance ell)
    (census : TwelveGalleryTypeAActualCensus A)
    {q : RealProjectivePoint}
    (hq : q ∈ twelveGalleryResidualTripleVertices A ell G) :
    (twelveGalleryCutEdgesAt G q).card = 1 := by
  have hspec := twelveGalleryResidualTriple_support_spec G census hq
  exact twelveGalleryTypeA_residual_three_has_one_H
    (G.labelSupport q) hspec.1 hspec.2

theorem twelveGallery_cut_defect
    {Line : Type u} [Fintype Line] [DecidableEq Line]
    {A : FiniteProjectiveLineArrangement Line} {ell : Line}
    (G : A.LabelledFourStripGalleryEntrance ell)
    (census : TwelveGalleryTypeAActualCensus A) :
    (twelveGalleryUpgradedBaseSlots G).card +
      (twelveGalleryConsumedCutEdges A ell G).card ≤ 3 := by
  classical
  let T := twelveGalleryResidualTripleVertices A ell G
  let E := fun q : RealProjectivePoint => twelveGalleryCutEdgesAt G q
  let C := twelveGalleryConsumedCutEdges A ell G
  have hdisjoint : (T : Set RealProjectivePoint).PairwiseDisjoint E := by
    intro q hq r hr hqr
    exact twelveGalleryCutEdgesAt_disjoint_of_ne G hqr
  have hunionCard : (T.biUnion E).card = T.card := by
    rw [Finset.card_biUnion hdisjoint]
    calc
      (∑ q ∈ T, (E q).card) = ∑ _q ∈ T, 1 := by
        apply Finset.sum_congr rfl
        intro q hq
        exact twelveGalleryResidualTriple_cutEdges_card_one G census hq
      _ = T.card := by simp
  have hunionSub : T.biUnion E ⊆ twelveGalleryTypeAH \ C := by
    intro P hP
    obtain ⟨q, hqT, hPq⟩ := Finset.mem_biUnion.mp hP
    have hPH : P ∈ twelveGalleryTypeAH := (Finset.mem_inter.mp hPq).2
    refine Finset.mem_sdiff.mpr ⟨hPH, ?_⟩
    intro hPC
    obtain ⟨r, hrFour, hPr⟩ := Finset.mem_biUnion.mp hPC
    have hPqPower := (Finset.mem_inter.mp hPq).1
    have hPrPower := (Finset.mem_inter.mp hPr).1
    have hPcard : P.card = 2 := (Finset.mem_powersetCard.mp hPqPower).2
    have hqr : q = r :=
      eq_of_galleryPair_subset_two_labelSupports G hPcard
        (Finset.mem_powersetCard.mp hPqPower).1
        (Finset.mem_powersetCard.mp hPrPower).1
    have hqThree :=
      (Finset.mem_filter.mp
        (Finset.mem_sdiff.mp hqT).1).1
    have hqMult : A.multiplicity q = 3 :=
      (Finset.mem_filter.mp hqThree).2
    have hrOuter := Finset.mem_filter.mp hrFour
    have hrInner := Finset.mem_filter.mp hrOuter.1
    have hrMult : A.multiplicity r = 4 := hrInner.2
    rw [hqr] at hqMult
    omega
  have hconsSub : C ⊆ twelveGalleryTypeAH :=
    twelveGalleryConsumedCutEdges_subset_H G
  have hconsLe := Finset.card_le_card hconsSub
  have hunionLe := Finset.card_le_card hunionSub
  rw [hunionCard,
    Finset.card_sdiff_of_subset hconsSub,
    twelveGalleryTypeAH_card] at hunionLe
  rw [twelveGalleryTypeAH_card] at hconsLe
  have hsum : T.card + C.card ≤ 7 := by
    calc
      T.card + C.card ≤ (7 - C.card) + C.card :=
        Nat.add_le_add_right hunionLe C.card
      _ = 7 := Nat.sub_add_cancel hconsLe
  dsimp only [T, C] at hsum
  rw [twelveGalleryResidualTripleVertices_card G census] at hsum
  omega

theorem twelveGallery_cut_eq_three_and_zero
    {Line : Type u} [Fintype Line] [DecidableEq Line]
    {A : FiniteProjectiveLineArrangement Line} {ell : Line}
    (G : A.LabelledFourStripGalleryEntrance ell)
    (census : TwelveGalleryTypeAActualCensus A) :
    (twelveGalleryUpgradedBaseSlots G).card = 3 ∧
      (twelveGalleryConsumedCutEdges A ell G).card = 0 := by
  have hbase := twelveGalleryUpgradedBaseSlots_card_le_three G census
  have hcost := twelveGallery_nonupgrade_cost_le_consumedCutEdges G census
  have hdefect := twelveGallery_cut_defect G census
  omega

def twelveGalleryEligibleBaseSlots : Finset TwelveGalleryTypeABaseSlot :=
  {.inl 0, .inr 0, .inl 2, .inr 2}

def TwelveGalleryTypeAAdmissibleUpgrade
    (s : TwelveGalleryTypeABaseSlot)
    (Q : Finset GalleryLineLabel) : Prop :=
  twelveGalleryBaseLabels s ⊆ Q ∧
    Q.card = 4 ∧
    (Q.powersetCard 2 ∩ twelveGalleryTypeAH).card = 0 ∧
    ∀ P ∈ Q.powersetCard 2, P ∈ twelveGalleryTypeAUsedPairs →
      P ⊆ twelveGalleryBaseLabels s

private abbrev twelveGalleryAdmissibleUpgradeDecidable
    (s : TwelveGalleryTypeABaseSlot) (Q : Finset GalleryLineLabel) :
    Decidable (TwelveGalleryTypeAAdmissibleUpgrade s Q) := by
  apply decidable_of_iff
    (twelveGalleryBaseLabels s ⊆ Q ∧
      Q.card = 4 ∧
      (Q.powersetCard 2 ∩ twelveGalleryTypeAH).card = 0 ∧
      ∀ P : {P // P ∈ Q.powersetCard 2},
        P.1 ∈ twelveGalleryTypeAUsedPairs →
          P.1 ⊆ twelveGalleryBaseLabels s)
  unfold TwelveGalleryTypeAAdmissibleUpgrade
  constructor
  · rintro ⟨hsub, hcard, hcut, hused⟩
    exact ⟨hsub, hcard, hcut, fun P hP => hused ⟨P, hP⟩⟩
  · rintro ⟨hsub, hcard, hcut, hused⟩
    exact ⟨hsub, hcard, hcut, fun P => hused P.1 P.2⟩

attribute [local instance] twelveGalleryAdmissibleUpgradeDecidable

private theorem twelveGallery_admissibleUpgrade_slot_table :
    ∀ s : TwelveGalleryTypeABaseSlot,
      ∀ Q ∈ (Finset.univ : Finset GalleryLineLabel).powersetCard 4,
        TwelveGalleryTypeAAdmissibleUpgrade s Q →
          s ∈ twelveGalleryEligibleBaseSlots := by
  intro s Q hQ
  intro h
  let B := twelveGalleryBaseLabels s
  have hBsub : B ⊆ Q := h.1
  have hBcard : B.card = 3 := by
    simpa [B] using twelveGalleryBaseLabels_card s
  have hdiffCard : (Q \ B).card = 1 := by
    rw [Finset.card_sdiff_of_subset hBsub, h.2.1, hBcard]
  obtain ⟨x, hxDiff⟩ := Finset.card_eq_one.mp hdiffCard
  have hxMem : x ∈ Q \ B := by
    rw [hxDiff]
    simp
  have hQeq : Q = insert x B := by
    apply Finset.Subset.antisymm
    · intro y hyQ
      by_cases hyB : y ∈ B
      · exact Finset.mem_insert_of_mem hyB
      · have hyDiff : y ∈ Q \ B :=
          Finset.mem_sdiff.mpr ⟨hyQ, hyB⟩
        rw [hxDiff] at hyDiff
        exact Finset.mem_insert.mpr (Or.inl (Finset.mem_singleton.mp hyDiff))
    · intro y hy
      rcases Finset.mem_insert.mp hy with rfl | hyB
      · exact (Finset.mem_sdiff.mp hxMem).1
      · exact hBsub hyB
  rw [hQeq] at h
  fin_cases s <;> simp [twelveGalleryEligibleBaseSlots] at ⊢
  all_goals
    revert h
    fin_cases x <;> decide

theorem twelveGallery_admissibleUpgrade_slot_eligible
    (s : TwelveGalleryTypeABaseSlot) (Q : Finset GalleryLineLabel)
    (h : TwelveGalleryTypeAAdmissibleUpgrade s Q) :
    s ∈ twelveGalleryEligibleBaseSlots := by
  apply twelveGallery_admissibleUpgrade_slot_table s Q
  · simp [h.2.1]
  · exact h

theorem twelveGallery_upgradedBase_admissible
    {Line : Type u} [Fintype Line] [DecidableEq Line]
    {A : FiniteProjectiveLineArrangement Line} {ell : Line}
    (G : A.LabelledFourStripGalleryEntrance ell)
    (census : TwelveGalleryTypeAActualCensus A)
    {s : TwelveGalleryTypeABaseSlot}
    (hs : s ∈ twelveGalleryUpgradedBaseSlots G) :
    TwelveGalleryTypeAAdmissibleUpgrade s
      (G.labelSupport (twelveGalleryBaseVertex G s)) := by
  classical
  let q := twelveGalleryBaseVertex G s
  have hqUpgraded : q ∈ twelveGalleryUpgradedBaseVertices G :=
    Finset.mem_image.mpr ⟨s, hs, rfl⟩
  have hqFour : q ∈ twelveGalleryOffLineMultiplicityVertices A ell 4 :=
    twelveGalleryUpgradedBaseVertices_subset_offLine_four G hqUpgraded
  have hcutEmpty : twelveGalleryCutEdgesAt G q = ∅ := by
    have hempty := Finset.card_eq_zero.mp
      (twelveGallery_cut_eq_three_and_zero G census).2
    apply Finset.Subset.antisymm
    · intro P hP
      have hPConsumed : P ∈ twelveGalleryConsumedCutEdges A ell G :=
        Finset.mem_biUnion.mpr ⟨q, hqFour, hP⟩
      rw [hempty] at hPConsumed
      simpa using hPConsumed
    · exact Finset.empty_subset _
  refine ⟨twelveGalleryBaseLabels_subset_labelSupport G s,
    (Finset.mem_filter.mp hs).2, ?_, ?_⟩
  · rw [show (G.labelSupport q).powersetCard 2 ∩
        twelveGalleryTypeAH = twelveGalleryCutEdgesAt G q by rfl,
      hcutEmpty]
    simp
  · intro P hP hPUsed
    have hPcard : P.card = 2 := (Finset.mem_powersetCard.mp hP).2
    have hPq : P ⊆ G.labelSupport q :=
      (Finset.mem_powersetCard.mp hP).1
    rcases Finset.mem_union.mp hPUsed with hRung | hBase
    · obtain ⟨i, _hi, rfl⟩ := Finset.mem_image.mp hRung
      have hPrung :
          {twelveGalleryALabel i, twelveGalleryBLabel i} ⊆
            G.labelSupport (G.rungVertex i) := by
        rw [labelSupport_rungVertex_eq]
      have heq : q = G.rungVertex i :=
        eq_of_galleryPair_subset_two_labelSupports G hPcard hPq hPrung
      exfalso
      apply twelveGalleryBaseVertex_not_incident_ell G s
      change A.Incident q ell
      rw [heq]
      exact (G.rungIncident_iff i ell).2 (Or.inl rfl)
    · obtain ⟨B, hB, hPB⟩ := Finset.mem_biUnion.mp hBase
      rw [twelveGalleryTypeABaseLabels_eq_image_slots] at hB
      obtain ⟨t, _ht, rfl⟩ := Finset.mem_image.mp hB
      have hPtBase : P ⊆ twelveGalleryBaseLabels t :=
        (Finset.mem_powersetCard.mp hPB).1
      have hPtSupport : P ⊆
          G.labelSupport (twelveGalleryBaseVertex G t) :=
        hPtBase.trans (twelveGalleryBaseLabels_subset_labelSupport G t)
      have heq : twelveGalleryBaseVertex G s =
          twelveGalleryBaseVertex G t :=
        eq_of_galleryPair_subset_two_labelSupports G hPcard hPq hPtSupport
      have hst : s = t := twelveGalleryBaseVertex_injective G census heq
      simpa [hst] using hPtBase

theorem twelveGalleryUpgradedBaseSlots_subset_eligible
    {Line : Type u} [Fintype Line] [DecidableEq Line]
    {A : FiniteProjectiveLineArrangement Line} {ell : Line}
    (G : A.LabelledFourStripGalleryEntrance ell)
    (census : TwelveGalleryTypeAActualCensus A) :
    twelveGalleryUpgradedBaseSlots G ⊆ twelveGalleryEligibleBaseSlots := by
  intro s hs
  exact twelveGallery_admissibleUpgrade_slot_eligible s _
    (twelveGallery_upgradedBase_admissible G census hs)

theorem twelveGallery_existsUnique_omittedEligibleBase
    {Line : Type u} [Fintype Line] [DecidableEq Line]
    {A : FiniteProjectiveLineArrangement Line} {ell : Line}
    (G : A.LabelledFourStripGalleryEntrance ell)
    (census : TwelveGalleryTypeAActualCensus A) :
    ∃! s : TwelveGalleryTypeABaseSlot,
      s ∈ twelveGalleryEligibleBaseSlots ∧
        s ∉ twelveGalleryUpgradedBaseSlots G := by
  classical
  let E := twelveGalleryEligibleBaseSlots
  let U := twelveGalleryUpgradedBaseSlots G
  have hsub : U ⊆ E := twelveGalleryUpgradedBaseSlots_subset_eligible G census
  have hEcard : E.card = 4 := by decide
  have hUcard : U.card = 3 := (twelveGallery_cut_eq_three_and_zero G census).1
  have hdiff : (E \ U).card = 1 := by
    rw [Finset.card_sdiff_of_subset hsub, hEcard, hUcard]
  obtain ⟨s, hs⟩ := Finset.card_eq_one.mp hdiff
  refine ⟨s, ?_, ?_⟩
  · have hsMem : s ∈ E \ U := by simp [hs]
    exact Finset.mem_sdiff.mp hsMem
  · intro t ht
    have htMem : t ∈ E \ U := Finset.mem_sdiff.mpr ht
    rw [hs] at htMem
    exact Finset.mem_singleton.mp htMem

theorem twelveGallery_residualTriple_cutEdges_cover_H
    {Line : Type u} [Fintype Line] [DecidableEq Line]
    {A : FiniteProjectiveLineArrangement Line} {ell : Line}
    (G : A.LabelledFourStripGalleryEntrance ell)
    (census : TwelveGalleryTypeAActualCensus A) :
    (twelveGalleryResidualTripleVertices A ell G).biUnion
        (twelveGalleryCutEdgesAt G) = twelveGalleryTypeAH := by
  classical
  let T := twelveGalleryResidualTripleVertices A ell G
  let E := fun q : RealProjectivePoint => twelveGalleryCutEdgesAt G q
  have hdisjoint : (T : Set RealProjectivePoint).PairwiseDisjoint E := by
    intro q hq r hr hqr
    exact twelveGalleryCutEdgesAt_disjoint_of_ne G hqr
  have hunionCard : (T.biUnion E).card = 7 := by
    rw [Finset.card_biUnion hdisjoint]
    calc
      (∑ q ∈ T, (E q).card) = ∑ _q ∈ T, 1 := by
        apply Finset.sum_congr rfl
        intro q hq
        exact twelveGalleryResidualTriple_cutEdges_card_one G census hq
      _ = T.card := by simp
      _ = 7 := by
        rw [twelveGalleryResidualTripleVertices_card G census,
          (twelveGallery_cut_eq_three_and_zero G census).1]
  have hunionSub : T.biUnion E ⊆ twelveGalleryTypeAH := by
    intro P hP
    obtain ⟨q, _hq, hPq⟩ := Finset.mem_biUnion.mp hP
    exact (Finset.mem_inter.mp hPq).2
  apply Finset.eq_of_subset_of_card_le hunionSub
  rw [twelveGalleryTypeAH_card, hunionCard]

theorem twelveGallery_exists_residualTriple_through_H
    {Line : Type u} [Fintype Line] [DecidableEq Line]
    {A : FiniteProjectiveLineArrangement Line} {ell : Line}
    (G : A.LabelledFourStripGalleryEntrance ell)
    (census : TwelveGalleryTypeAActualCensus A)
    {P : Finset GalleryLineLabel} (hP : P ∈ twelveGalleryTypeAH) :
    ∃ q ∈ twelveGalleryResidualTripleVertices A ell G,
      P ∈ twelveGalleryCutEdgesAt G q := by
  have hcover := twelveGallery_residualTriple_cutEdges_cover_H G census
  rw [← hcover] at hP
  exact Finset.mem_biUnion.mp hP

theorem twelveGallery_exists_upgradeExtra
    {Line : Type u} [Fintype Line] [DecidableEq Line]
    {A : FiniteProjectiveLineArrangement Line} {ell : Line}
    (G : A.LabelledFourStripGalleryEntrance ell)
    {s : TwelveGalleryTypeABaseSlot}
    (hs : s ∈ twelveGalleryUpgradedBaseSlots G) :
    ∃ x : GalleryLineLabel,
      x ∉ twelveGalleryBaseLabels s ∧
        G.labelSupport (twelveGalleryBaseVertex G s) =
          insert x (twelveGalleryBaseLabels s) := by
  classical
  let B := twelveGalleryBaseLabels s
  let Q := G.labelSupport (twelveGalleryBaseVertex G s)
  have hBQ : B ⊆ Q := twelveGalleryBaseLabels_subset_labelSupport G s
  have hBcard : B.card = 3 := twelveGalleryBaseLabels_card s
  have hQcard : Q.card = 4 := (Finset.mem_filter.mp hs).2
  have hdiffCard : (Q \ B).card = 1 := by
    rw [Finset.card_sdiff_of_subset hBQ, hQcard, hBcard]
  obtain ⟨x, hx⟩ := Finset.card_eq_one.mp hdiffCard
  have hxMem : x ∈ Q \ B := by simp [hx]
  refine ⟨x, (Finset.mem_sdiff.mp hxMem).2, ?_⟩
  calc
    Q = B ∪ (Q \ B) := (Finset.union_sdiff_of_subset hBQ).symm
    _ = insert x B := by rw [hx]; simp [Finset.union_comm]

def twelveGalleryNormalizedXLabel (x : Fin 4) : GalleryLineLabel :=
  match x.1 with
  | 0 => twelveGalleryALabel 3
  | 1 => twelveGalleryBLabel 2
  | 2 => twelveGalleryBLabel 3
  | _ => twelveGalleryCLabel 2

def twelveGalleryNormalizedYLabel (y : Fin 4) : GalleryLineLabel :=
  match y.1 with
  | 0 => twelveGalleryALabel 2
  | 1 => twelveGalleryALabel 3
  | 2 => twelveGalleryBLabel 3
  | _ => twelveGalleryCLabel 2

def twelveGalleryNormalizedZLabel (z : Fin 4) : GalleryLineLabel :=
  match z.1 with
  | 0 => twelveGalleryALabel 0
  | 1 => twelveGalleryBLabel 0
  | 2 => twelveGalleryBLabel 1
  | _ => twelveGalleryCLabel 0

def twelveGalleryNormalizedA1Quad (x : Fin 4) :
    Finset GalleryLineLabel :=
  insert (twelveGalleryNormalizedXLabel x)
    (twelveGalleryBaseLabels (.inl 0))

def twelveGalleryNormalizedB1Quad (y : Fin 4) :
    Finset GalleryLineLabel :=
  insert (twelveGalleryNormalizedYLabel y)
    (twelveGalleryBaseLabels (.inr 0))

def twelveGalleryNormalizedA3Quad (z : Fin 4) :
    Finset GalleryLineLabel :=
  insert (twelveGalleryNormalizedZLabel z)
    (twelveGalleryBaseLabels (.inl 2))

private theorem twelveGallery_normalizedA1_extra_table :
    ∀ x : GalleryLineLabel,
      TwelveGalleryTypeAAdmissibleUpgrade (.inl 0)
        (insert x (twelveGalleryBaseLabels (.inl 0))) →
      ∃ k : Fin 4, x = twelveGalleryNormalizedXLabel k := by
  intro x
  fin_cases x <;> decide

private theorem twelveGallery_normalizedB1_extra_table :
    ∀ y : GalleryLineLabel,
      TwelveGalleryTypeAAdmissibleUpgrade (.inr 0)
        (insert y (twelveGalleryBaseLabels (.inr 0))) →
      ∃ k : Fin 4, y = twelveGalleryNormalizedYLabel k := by
  intro y
  fin_cases y <;> decide

private theorem twelveGallery_normalizedA3_extra_table :
    ∀ z : GalleryLineLabel,
      TwelveGalleryTypeAAdmissibleUpgrade (.inl 2)
        (insert z (twelveGalleryBaseLabels (.inl 2))) →
      ∃ k : Fin 4, z = twelveGalleryNormalizedZLabel k := by
  intro z
  fin_cases z <;> decide

def twelveGalleryTypeAResidualTriples :
    Finset (Finset GalleryLineLabel) :=
  (Finset.univ : Finset GalleryLineLabel).powersetCard 3 |>.filter fun T =>
    Disjoint (T.powersetCard 2) twelveGalleryTypeAUsedPairs

def twelveGalleryNormalizedSurvivingCutEdges
    (x y z : Fin 4) : Finset (Finset GalleryLineLabel) :=
  twelveGalleryTypeAH.filter fun P =>
    ((twelveGalleryTypeAResidualTriples.filter fun T =>
      P ⊆ T ∧
      (T ∩ twelveGalleryNormalizedA1Quad x).card ≤ 1 ∧
      (T ∩ twelveGalleryNormalizedB1Quad y).card ≤ 1 ∧
      (T ∩ twelveGalleryNormalizedA3Quad z).card ≤ 1).Nonempty)

/-- The four rows in the complete corner table after normalizing the omitted
eligible base to `B3`. -/
inductive TwelveGalleryTypeACornerState
  | b2a2a0
  | b2b3c1
  | b2c3a0
  | c3b3b0
  deriving DecidableEq, Fintype

/-- The `x` entry of a corner state.  Values `0,1,2,3` name
`a3,b2,b3,c3`, respectively. -/
def TwelveGalleryTypeACornerState.xCode :
    TwelveGalleryTypeACornerState → Fin 4
  | .b2a2a0 => 1
  | .b2b3c1 => 1
  | .b2c3a0 => 1
  | .c3b3b0 => 3

/-- The `y` entry.  Values `0,1,2,3` name `a2,a3,b3,c3`. -/
def TwelveGalleryTypeACornerState.yCode :
    TwelveGalleryTypeACornerState → Fin 4
  | .b2a2a0 => 0
  | .b2b3c1 => 2
  | .b2c3a0 => 3
  | .c3b3b0 => 2

/-- The `z` entry.  Values `0,1,2,3` name `a0,b0,b1,c1`. -/
def TwelveGalleryTypeACornerState.zCode :
    TwelveGalleryTypeACornerState → Fin 4
  | .b2a2a0 => 0
  | .b2b3c1 => 3
  | .b2c3a0 => 0
  | .c3b3b0 => 1

/-- The literal four-line hand table, indexed by `z`.  Its entries are the
possible `(x,y)` pairs after pair uniqueness and preservation of the two
corner edges `h0,h4`. -/
def twelveGalleryTypeACornerTable (z : Fin 4) : Finset (Fin 4 × Fin 4) :=
  match z.1 with
  | 0 => {(1, 0), (1, 3)}
  | 1 => {(3, 2)}
  | 2 => ∅
  | _ => {(1, 2)}

private theorem twelveGallery_normalized_unique_table :
    ∀ x y z : Fin 4,
      TwelveGalleryTypeAAdmissibleUpgrade (.inl 0)
          (twelveGalleryNormalizedA1Quad x) →
      TwelveGalleryTypeAAdmissibleUpgrade (.inr 0)
          (twelveGalleryNormalizedB1Quad y) →
      TwelveGalleryTypeAAdmissibleUpgrade (.inl 2)
          (twelveGalleryNormalizedA3Quad z) →
      (twelveGalleryNormalizedA1Quad x ∩
          twelveGalleryNormalizedB1Quad y).card ≤ 1 →
      (twelveGalleryNormalizedA1Quad x ∩
          twelveGalleryNormalizedA3Quad z).card ≤ 1 →
      (twelveGalleryNormalizedB1Quad y ∩
          twelveGalleryNormalizedA3Quad z).card ≤ 1 →
      twelveGalleryNormalizedSurvivingCutEdges x y z =
          twelveGalleryTypeAH →
      (x, y) ∈ twelveGalleryTypeACornerTable z ∧
        x = 1 ∧ y = 3 ∧ z = 0 := by
  intro x y z
  fin_cases x <;> fin_cases y <;> fin_cases z <;> decide

/-- Every entry of the displayed corner table is one of the four named
states.  This is a four-row certificate, not a generated candidate list. -/
theorem twelveGalleryTypeACornerTable_eq_state
    (x y z : Fin 4) (hxy : (x, y) ∈ twelveGalleryTypeACornerTable z) :
    ∃ s : TwelveGalleryTypeACornerState,
      s.xCode = x ∧ s.yCode = y ∧ s.zCode = z := by
  fin_cases z <;> simp [twelveGalleryTypeACornerTable] at hxy
  · rcases hxy with h | h
    · refine ⟨.b2a2a0, ?_⟩
      simp [TwelveGalleryTypeACornerState.xCode,
        TwelveGalleryTypeACornerState.yCode,
        TwelveGalleryTypeACornerState.zCode, h]
    · refine ⟨.b2c3a0, ?_⟩
      simp [TwelveGalleryTypeACornerState.xCode,
        TwelveGalleryTypeACornerState.yCode,
        TwelveGalleryTypeACornerState.zCode, h]
  · refine ⟨.c3b3b0, ?_⟩
    simp [TwelveGalleryTypeACornerState.xCode,
      TwelveGalleryTypeACornerState.yCode,
      TwelveGalleryTypeACornerState.zCode, hxy]
  · refine ⟨.b2b3c1, ?_⟩
    simp [TwelveGalleryTypeACornerState.xCode,
      TwelveGalleryTypeACornerState.yCode,
      TwelveGalleryTypeACornerState.zCode, hxy]

theorem twelveGallery_normalized_upgrade_data
    {Line : Type u} [Fintype Line] [DecidableEq Line]
    {A : FiniteProjectiveLineArrangement Line} {ell : Line}
    (G : A.LabelledFourStripGalleryEntrance ell)
    (census : TwelveGalleryTypeAActualCensus A)
    (homit : (.inr 2 : TwelveGalleryTypeABaseSlot) ∉
      twelveGalleryUpgradedBaseSlots G) :
    ∃ x y z : Fin 4,
      G.labelSupport (twelveGalleryBaseVertex G (.inl 0)) =
          twelveGalleryNormalizedA1Quad x ∧
      G.labelSupport (twelveGalleryBaseVertex G (.inr 0)) =
          twelveGalleryNormalizedB1Quad y ∧
      G.labelSupport (twelveGalleryBaseVertex G (.inl 2)) =
          twelveGalleryNormalizedA3Quad z := by
  classical
  obtain ⟨o, ho, huniq⟩ :=
    twelveGallery_existsUnique_omittedEligibleBase G census
  have hoB3 : o = (.inr 2 : TwelveGalleryTypeABaseSlot) :=
    (huniq _ ⟨by decide, homit⟩).symm
  have hmem (s : TwelveGalleryTypeABaseSlot)
      (hsEligible : s ∈ twelveGalleryEligibleBaseSlots)
      (hsNe : s ≠ (.inr 2 : TwelveGalleryTypeABaseSlot)) :
      s ∈ twelveGalleryUpgradedBaseSlots G := by
    by_contra hsNot
    have hso : s = o := huniq s ⟨hsEligible, hsNot⟩
    exact hsNe (hso.trans hoB3)
  have hA1 : (.inl 0 : TwelveGalleryTypeABaseSlot) ∈
      twelveGalleryUpgradedBaseSlots G := hmem _ (by decide) (by decide)
  have hB1 : (.inr 0 : TwelveGalleryTypeABaseSlot) ∈
      twelveGalleryUpgradedBaseSlots G := hmem _ (by decide) (by decide)
  have hA3 : (.inl 2 : TwelveGalleryTypeABaseSlot) ∈
      twelveGalleryUpgradedBaseSlots G := hmem _ (by decide) (by decide)
  obtain ⟨xLabel, _hxOutside, hxSupport⟩ :=
    twelveGallery_exists_upgradeExtra G hA1
  obtain ⟨yLabel, _hyOutside, hySupport⟩ :=
    twelveGallery_exists_upgradeExtra G hB1
  obtain ⟨zLabel, _hzOutside, hzSupport⟩ :=
    twelveGallery_exists_upgradeExtra G hA3
  have hxAdmissible := twelveGallery_upgradedBase_admissible G census hA1
  have hyAdmissible := twelveGallery_upgradedBase_admissible G census hB1
  have hzAdmissible := twelveGallery_upgradedBase_admissible G census hA3
  rw [hxSupport] at hxAdmissible
  rw [hySupport] at hyAdmissible
  rw [hzSupport] at hzAdmissible
  obtain ⟨x, hx⟩ := twelveGallery_normalizedA1_extra_table xLabel hxAdmissible
  obtain ⟨y, hy⟩ := twelveGallery_normalizedB1_extra_table yLabel hyAdmissible
  obtain ⟨z, hz⟩ := twelveGallery_normalizedA3_extra_table zLabel hzAdmissible
  refine ⟨x, y, z, ?_, ?_, ?_⟩
  · simpa [twelveGalleryNormalizedA1Quad, hx] using hxSupport
  · simpa [twelveGalleryNormalizedB1Quad, hy] using hySupport
  · simpa [twelveGalleryNormalizedA3Quad, hz] using hzSupport

theorem twelveGallery_normalized_survivingCutEdges_eq_H
    {Line : Type u} [Fintype Line] [DecidableEq Line]
    {A : FiniteProjectiveLineArrangement Line} {ell : Line}
    (G : A.LabelledFourStripGalleryEntrance ell)
    (census : TwelveGalleryTypeAActualCensus A)
    (x y z : Fin 4)
    (hx : G.labelSupport (twelveGalleryBaseVertex G (.inl 0)) =
      twelveGalleryNormalizedA1Quad x)
    (hy : G.labelSupport (twelveGalleryBaseVertex G (.inr 0)) =
      twelveGalleryNormalizedB1Quad y)
    (hz : G.labelSupport (twelveGalleryBaseVertex G (.inl 2)) =
      twelveGalleryNormalizedA3Quad z) :
    twelveGalleryNormalizedSurvivingCutEdges x y z =
      twelveGalleryTypeAH := by
  classical
  ext P
  constructor
  · intro hP
    exact (Finset.mem_filter.mp hP).1
  · intro hPH
    apply Finset.mem_filter.mpr
    refine ⟨hPH, ?_⟩
    obtain ⟨q, hqResidual, hPq⟩ :=
      twelveGallery_exists_residualTriple_through_H G census hPH
    have hspec :=
      twelveGalleryResidualTriple_support_spec G census hqResidual
    have hqOff := (Finset.mem_sdiff.mp hqResidual).1
    have hqMult : A.multiplicity q = 3 :=
      (Finset.mem_filter.mp (Finset.mem_filter.mp hqOff).1).2
    have hneA1 : q ≠ twelveGalleryBaseVertex G (.inl 0) := by
      intro heq
      have hbaseMult :=
        twelveGalleryBaseVertex_labelSupport_card_eq_multiplicity
          G (.inl 0)
      rw [hx] at hbaseMult
      have hquadCard : (twelveGalleryNormalizedA1Quad x).card = 4 := by
        fin_cases x <;> decide
      rw [hquadCard] at hbaseMult
      rw [heq] at hqMult
      omega
    have hneB1 : q ≠ twelveGalleryBaseVertex G (.inr 0) := by
      intro heq
      have hbaseMult :=
        twelveGalleryBaseVertex_labelSupport_card_eq_multiplicity
          G (.inr 0)
      rw [hy] at hbaseMult
      have hquadCard : (twelveGalleryNormalizedB1Quad y).card = 4 := by
        fin_cases y <;> decide
      rw [hquadCard] at hbaseMult
      rw [heq] at hqMult
      omega
    have hneA3 : q ≠ twelveGalleryBaseVertex G (.inl 2) := by
      intro heq
      have hbaseMult :=
        twelveGalleryBaseVertex_labelSupport_card_eq_multiplicity
          G (.inl 2)
      rw [hz] at hbaseMult
      have hquadCard : (twelveGalleryNormalizedA3Quad z).card = 4 := by
        fin_cases z <;> decide
      rw [hquadCard] at hbaseMult
      rw [heq] at hqMult
      omega
    refine ⟨G.labelSupport q, ?_⟩
    · apply Finset.mem_filter.mpr
      refine ⟨?_, ?_⟩
      · apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_powersetCard.mpr
          ⟨Finset.subset_univ _, hspec.1⟩, ?_⟩
        rw [Finset.disjoint_left]
        intro R hR hRUsed
        exact hspec.2 R hR hRUsed
      · exact ⟨
          (Finset.mem_powersetCard.mp (Finset.mem_inter.mp hPq).1).1,
          by simpa [hx] using G.labelSupport_inter_card_le_one hneA1,
          by simpa [hy] using G.labelSupport_inter_card_le_one hneB1,
          by simpa [hz] using G.labelSupport_inter_card_le_one hneA3⟩

theorem twelveGallery_normalized_unique_supports
    {Line : Type u} [Fintype Line] [DecidableEq Line]
    {A : FiniteProjectiveLineArrangement Line} {ell : Line}
    (G : A.LabelledFourStripGalleryEntrance ell)
    (census : TwelveGalleryTypeAActualCensus A)
    (homit : (.inr 2 : TwelveGalleryTypeABaseSlot) ∉
      twelveGalleryUpgradedBaseSlots G) :
    G.labelSupport (twelveGalleryBaseVertex G (.inl 0)) =
        twelveGalleryNormalizedA1Quad 1 ∧
    G.labelSupport (twelveGalleryBaseVertex G (.inr 0)) =
        twelveGalleryNormalizedB1Quad 3 ∧
    G.labelSupport (twelveGalleryBaseVertex G (.inl 2)) =
        twelveGalleryNormalizedA3Quad 0 := by
  classical
  obtain ⟨x, y, z, hx, hy, hz⟩ :=
    twelveGallery_normalized_upgrade_data G census homit
  have hA1 : (.inl 0 : TwelveGalleryTypeABaseSlot) ∈
      twelveGalleryUpgradedBaseSlots G :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
      rw [hx]
      fin_cases x <;> decide⟩
  have hB1 : (.inr 0 : TwelveGalleryTypeABaseSlot) ∈
      twelveGalleryUpgradedBaseSlots G :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
      rw [hy]
      fin_cases y <;> decide⟩
  have hA3 : (.inl 2 : TwelveGalleryTypeABaseSlot) ∈
      twelveGalleryUpgradedBaseSlots G :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
      rw [hz]
      fin_cases z <;> decide⟩
  have hAdmA := twelveGallery_upgradedBase_admissible G census hA1
  have hAdmB := twelveGallery_upgradedBase_admissible G census hB1
  have hAdmC := twelveGallery_upgradedBase_admissible G census hA3
  rw [hx] at hAdmA
  rw [hy] at hAdmB
  rw [hz] at hAdmC
  have hAB : (twelveGalleryNormalizedA1Quad x ∩
      twelveGalleryNormalizedB1Quad y).card ≤ 1 := by
    simpa [hx, hy] using G.labelSupport_inter_card_le_one
      (show twelveGalleryBaseVertex G (.inl 0) ≠
          twelveGalleryBaseVertex G (.inr 0) by
        exact (twelveGalleryBaseVertex_injective G census).ne (by decide))
  have hAC : (twelveGalleryNormalizedA1Quad x ∩
      twelveGalleryNormalizedA3Quad z).card ≤ 1 := by
    simpa [hx, hz] using G.labelSupport_inter_card_le_one
      (show twelveGalleryBaseVertex G (.inl 0) ≠
          twelveGalleryBaseVertex G (.inl 2) by
        exact (twelveGalleryBaseVertex_injective G census).ne (by decide))
  have hBC : (twelveGalleryNormalizedB1Quad y ∩
      twelveGalleryNormalizedA3Quad z).card ≤ 1 := by
    simpa [hy, hz] using G.labelSupport_inter_card_le_one
      (show twelveGalleryBaseVertex G (.inr 0) ≠
          twelveGalleryBaseVertex G (.inl 2) by
        exact (twelveGalleryBaseVertex_injective G census).ne (by decide))
  have hsurvive := twelveGallery_normalized_survivingCutEdges_eq_H
    G census x y z hx hy hz
  have hnormal := twelveGallery_normalized_unique_table
    x y z hAdmA hAdmB hAdmC hAB hAC hBC hsurvive
  rcases hnormal.2 with ⟨rfl, rfl, rfl⟩
  exact ⟨hx, hy, hz⟩

def twelveGalleryTypeAH3 : Finset GalleryLineLabel :=
  {twelveGalleryALabel 2, twelveGalleryBLabel 3}

def twelveGalleryTypeAH4 : Finset GalleryLineLabel :=
  {twelveGalleryALabel 3, twelveGalleryBLabel 2}

def twelveGalleryTypeALeftH : Finset (Finset GalleryLineLabel) :=
  twelveGalleryTypeAH \ {twelveGalleryTypeAH3, twelveGalleryTypeAH4}

def twelveGalleryTypeAA3Neighbours : Finset GalleryLineLabel :=
  {twelveGalleryALabel 1, twelveGalleryBLabel 0,
    twelveGalleryBLabel 1, twelveGalleryBLabel 2,
    twelveGalleryCLabel 0, twelveGalleryCLabel 1}

def twelveGalleryTypeAB3Neighbours : Finset GalleryLineLabel :=
  {twelveGalleryALabel 0, twelveGalleryALabel 1,
    twelveGalleryALabel 2, twelveGalleryBLabel 0,
    twelveGalleryBLabel 1, twelveGalleryCLabel 0,
    twelveGalleryCLabel 1}

@[simp]
theorem twelveGalleryTypeALeftH_card :
    twelveGalleryTypeALeftH.card = 5 := by decide

@[simp]
theorem twelveGalleryTypeAA3Neighbours_card :
    twelveGalleryTypeAA3Neighbours.card = 6 := by decide

@[simp]
theorem twelveGalleryTypeAB3Neighbours_card :
    twelveGalleryTypeAB3Neighbours.card = 7 := by decide

abbrev TwelveGalleryTypeAHEdge :=
  {P : Finset GalleryLineLabel // P ∈ twelveGalleryTypeAH}

noncomputable def twelveGalleryResidualVertexFor
    {Line : Type u} [Fintype Line] [DecidableEq Line]
    {A : FiniteProjectiveLineArrangement Line} {ell : Line}
    (G : A.LabelledFourStripGalleryEntrance ell)
    (census : TwelveGalleryTypeAActualCensus A)
    (P : TwelveGalleryTypeAHEdge) : RealProjectivePoint :=
  Classical.choose
    (twelveGallery_exists_residualTriple_through_H G census P.2)

theorem twelveGalleryResidualVertexFor_mem
    {Line : Type u} [Fintype Line] [DecidableEq Line]
    {A : FiniteProjectiveLineArrangement Line} {ell : Line}
    (G : A.LabelledFourStripGalleryEntrance ell)
    (census : TwelveGalleryTypeAActualCensus A)
    (P : TwelveGalleryTypeAHEdge) :
    twelveGalleryResidualVertexFor G census P ∈
      twelveGalleryResidualTripleVertices A ell G :=
  (Classical.choose_spec
    (twelveGallery_exists_residualTriple_through_H G census P.2)).1

theorem twelveGalleryResidualVertexFor_edge_mem
    {Line : Type u} [Fintype Line] [DecidableEq Line]
    {A : FiniteProjectiveLineArrangement Line} {ell : Line}
    (G : A.LabelledFourStripGalleryEntrance ell)
    (census : TwelveGalleryTypeAActualCensus A)
    (P : TwelveGalleryTypeAHEdge) :
    P.1 ∈ twelveGalleryCutEdgesAt G
      (twelveGalleryResidualVertexFor G census P) :=
  (Classical.choose_spec
    (twelveGallery_exists_residualTriple_through_H G census P.2)).2

theorem twelveGalleryResidualVertexFor_injective
    {Line : Type u} [Fintype Line] [DecidableEq Line]
    {A : FiniteProjectiveLineArrangement Line} {ell : Line}
    (G : A.LabelledFourStripGalleryEntrance ell)
    (census : TwelveGalleryTypeAActualCensus A) :
    Function.Injective (twelveGalleryResidualVertexFor G census) := by
  intro P Q hPQ
  apply Subtype.ext
  have hPmem := twelveGalleryResidualVertexFor_edge_mem G census P
  have hQmem := twelveGalleryResidualVertexFor_edge_mem G census Q
  rw [hPQ] at hPmem
  have hcard := twelveGalleryResidualTriple_cutEdges_card_one G census
    (twelveGalleryResidualVertexFor_mem G census Q)
  obtain ⟨R, hR⟩ := Finset.card_eq_one.mp hcard
  rw [hR] at hPmem hQmem
  exact (Finset.mem_singleton.mp hPmem).trans
    (Finset.mem_singleton.mp hQmem).symm

def twelveGalleryTypeAH3Edge : TwelveGalleryTypeAHEdge :=
  ⟨twelveGalleryTypeAH3, by decide⟩

def twelveGalleryTypeAH4Edge : TwelveGalleryTypeAHEdge :=
  ⟨twelveGalleryTypeAH4, by decide⟩

def twelveGalleryTypeALeftHEdges : Finset TwelveGalleryTypeAHEdge :=
  Finset.univ.filter fun P => P.1 ∈ twelveGalleryTypeALeftH

@[simp]
theorem twelveGalleryTypeALeftHEdges_card :
    twelveGalleryTypeALeftHEdges.card = 5 := by decide

def twelveGalleryNormalLeftBadPairs :
    Finset (Finset GalleryLineLabel × Finset GalleryLineLabel) :=
  (twelveGalleryTypeALeftH.product twelveGalleryTypeAResidualTriples).filter
    fun PT =>
      PT.1 ⊆ PT.2 ∧
      (PT.2 ∩ twelveGalleryNormalizedA1Quad 1).card ≤ 1 ∧
      (PT.2 ∩ twelveGalleryNormalizedB1Quad 3).card ≤ 1 ∧
      (PT.2 ∩ twelveGalleryNormalizedA3Quad 0).card ≤ 1 ∧
      ¬ ((twelveGalleryALabel 3 ∈ PT.2 ∧
            twelveGalleryBLabel 3 ∉ PT.2 ∧
            PT.1 ⊆ twelveGalleryTypeAA3Neighbours) ∨
          (twelveGalleryBLabel 3 ∈ PT.2 ∧
            twelveGalleryALabel 3 ∉ PT.2 ∧
            PT.1 ⊆ twelveGalleryTypeAB3Neighbours))

private theorem twelveGalleryNormalLeftBadPairs_eq_empty :
    twelveGalleryNormalLeftBadPairs = ∅ := by decide

theorem twelveGallery_normal_left_pole
    (P T : Finset GalleryLineLabel)
    (hP : P ∈ twelveGalleryTypeALeftH)
    (hT : T ∈ twelveGalleryTypeAResidualTriples)
    (hPT : P ⊆ T)
    (hA1 : (T ∩ twelveGalleryNormalizedA1Quad 1).card ≤ 1)
    (hB1 : (T ∩ twelveGalleryNormalizedB1Quad 3).card ≤ 1)
    (hA3 : (T ∩ twelveGalleryNormalizedA3Quad 0).card ≤ 1) :
    (twelveGalleryALabel 3 ∈ T ∧
        twelveGalleryBLabel 3 ∉ T ∧
        P ⊆ twelveGalleryTypeAA3Neighbours) ∨
      (twelveGalleryBLabel 3 ∈ T ∧
        twelveGalleryALabel 3 ∉ T ∧
        P ⊆ twelveGalleryTypeAB3Neighbours) := by
  by_contra hbad
  have hmem : (P, T) ∈ twelveGalleryNormalLeftBadPairs :=
    Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hP, hT⟩,
      hPT, hA1, hB1, hA3, hbad⟩
  rw [twelveGalleryNormalLeftBadPairs_eq_empty] at hmem
  simpa using hmem

def twelveGalleryNormalH4BadTriples : Finset (Finset GalleryLineLabel) :=
  twelveGalleryTypeAResidualTriples.filter fun T =>
    twelveGalleryTypeAH4 ⊆ T ∧
    (T ∩ twelveGalleryNormalizedA1Quad 1).card ≤ 1 ∧
    (T ∩ twelveGalleryNormalizedB1Quad 3).card ≤ 1 ∧
    (T ∩ twelveGalleryNormalizedA3Quad 0).card ≤ 1 ∧
    ¬ (T \ {twelveGalleryALabel 3} ⊆
      twelveGalleryTypeAA3Neighbours)

def twelveGalleryNormalH3BadTriples : Finset (Finset GalleryLineLabel) :=
  twelveGalleryTypeAResidualTriples.filter fun T =>
    twelveGalleryTypeAH3 ⊆ T ∧
    (T ∩ twelveGalleryNormalizedA1Quad 1).card ≤ 1 ∧
    (T ∩ twelveGalleryNormalizedB1Quad 3).card ≤ 1 ∧
    (T ∩ twelveGalleryNormalizedA3Quad 0).card ≤ 1 ∧
    ¬ (T \ {twelveGalleryBLabel 3} ⊆
      twelveGalleryTypeAB3Neighbours)

private theorem twelveGalleryNormalH4BadTriples_eq_empty :
    twelveGalleryNormalH4BadTriples = ∅ := by decide

private theorem twelveGalleryNormalH3BadTriples_eq_empty :
    twelveGalleryNormalH3BadTriples = ∅ := by decide

theorem twelveGallery_normal_residual_support_spec
    {Line : Type u} [Fintype Line] [DecidableEq Line]
    {A : FiniteProjectiveLineArrangement Line} {ell : Line}
    (G : A.LabelledFourStripGalleryEntrance ell)
    (census : TwelveGalleryTypeAActualCensus A)
    (homit : (.inr 2 : TwelveGalleryTypeABaseSlot) ∉
      twelveGalleryUpgradedBaseSlots G)
    {q : RealProjectivePoint}
    (hq : q ∈ twelveGalleryResidualTripleVertices A ell G) :
    G.labelSupport q ∈ twelveGalleryTypeAResidualTriples ∧
      (G.labelSupport q ∩ twelveGalleryNormalizedA1Quad 1).card ≤ 1 ∧
      (G.labelSupport q ∩ twelveGalleryNormalizedB1Quad 3).card ≤ 1 ∧
      (G.labelSupport q ∩ twelveGalleryNormalizedA3Quad 0).card ≤ 1 := by
  classical
  have hnormal := twelveGallery_normalized_unique_supports G census homit
  have hspec := twelveGalleryResidualTriple_support_spec G census hq
  have hqOff := (Finset.mem_sdiff.mp hq).1
  have hqMult : A.multiplicity q = 3 :=
    (Finset.mem_filter.mp (Finset.mem_filter.mp hqOff).1).2
  have hne (s : TwelveGalleryTypeABaseSlot)
      (hsSupport : G.labelSupport (twelveGalleryBaseVertex G s) =
        twelveGalleryNormalizedA1Quad 1 ∨
        G.labelSupport (twelveGalleryBaseVertex G s) =
          twelveGalleryNormalizedB1Quad 3 ∨
        G.labelSupport (twelveGalleryBaseVertex G s) =
          twelveGalleryNormalizedA3Quad 0) :
      q ≠ twelveGalleryBaseVertex G s := by
    intro heq
    have hbaseCardMult :=
      twelveGalleryBaseVertex_labelSupport_card_eq_multiplicity G s
    have hbaseCard :
        (G.labelSupport (twelveGalleryBaseVertex G s)).card = 4 := by
      rcases hsSupport with hs | hs | hs
      · rw [hs]
        decide
      · rw [hs]
        decide
      · rw [hs]
        decide
    have hbaseMult : A.multiplicity (twelveGalleryBaseVertex G s) = 4 :=
      hbaseCardMult.symm.trans hbaseCard
    rw [heq] at hqMult
    omega
  have hneA := hne (.inl 0) (Or.inl hnormal.1)
  have hneB := hne (.inr 0) (Or.inr (Or.inl hnormal.2.1))
  have hneC := hne (.inl 2) (Or.inr (Or.inr hnormal.2.2))
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply Finset.mem_filter.mpr
    refine ⟨by simp [hspec.1], ?_⟩
    rw [Finset.disjoint_left]
    intro P hP hPUsed
    exact hspec.2 P hP hPUsed
  · simpa [hnormal.1] using G.labelSupport_inter_card_le_one hneA
  · simpa [hnormal.2.1] using G.labelSupport_inter_card_le_one hneB
  · simpa [hnormal.2.2] using G.labelSupport_inter_card_le_one hneC

theorem twelveGallery_normal_H4_otherLabels_subset
    {Line : Type u} [Fintype Line] [DecidableEq Line]
    {A : FiniteProjectiveLineArrangement Line} {ell : Line}
    (G : A.LabelledFourStripGalleryEntrance ell)
    (census : TwelveGalleryTypeAActualCensus A)
    (homit : (.inr 2 : TwelveGalleryTypeABaseSlot) ∉
      twelveGalleryUpgradedBaseSlots G) :
    G.labelSupport
          (twelveGalleryResidualVertexFor G census twelveGalleryTypeAH4Edge) \
        {twelveGalleryALabel 3} ⊆ twelveGalleryTypeAA3Neighbours := by
  let q := twelveGalleryResidualVertexFor G census twelveGalleryTypeAH4Edge
  have hq := twelveGalleryResidualVertexFor_mem G census
    twelveGalleryTypeAH4Edge
  have hs := twelveGallery_normal_residual_support_spec G census homit hq
  have hEdge := twelveGalleryResidualVertexFor_edge_mem G census
    twelveGalleryTypeAH4Edge
  have hH4sub : twelveGalleryTypeAH4 ⊆ G.labelSupport q :=
    (Finset.mem_powersetCard.mp (Finset.mem_inter.mp hEdge).1).1
  by_contra hnot
  have hbad : G.labelSupport q ∈ twelveGalleryNormalH4BadTriples :=
    Finset.mem_filter.mpr ⟨hs.1, hH4sub, hs.2.1, hs.2.2.1,
      hs.2.2.2, hnot⟩
  rw [twelveGalleryNormalH4BadTriples_eq_empty] at hbad
  simpa using hbad

theorem twelveGallery_normal_H3_otherLabels_subset
    {Line : Type u} [Fintype Line] [DecidableEq Line]
    {A : FiniteProjectiveLineArrangement Line} {ell : Line}
    (G : A.LabelledFourStripGalleryEntrance ell)
    (census : TwelveGalleryTypeAActualCensus A)
    (homit : (.inr 2 : TwelveGalleryTypeABaseSlot) ∉
      twelveGalleryUpgradedBaseSlots G) :
    G.labelSupport
          (twelveGalleryResidualVertexFor G census twelveGalleryTypeAH3Edge) \
        {twelveGalleryBLabel 3} ⊆ twelveGalleryTypeAB3Neighbours := by
  let q := twelveGalleryResidualVertexFor G census twelveGalleryTypeAH3Edge
  have hq := twelveGalleryResidualVertexFor_mem G census
    twelveGalleryTypeAH3Edge
  have hs := twelveGallery_normal_residual_support_spec G census homit hq
  have hEdge := twelveGalleryResidualVertexFor_edge_mem G census
    twelveGalleryTypeAH3Edge
  have hH3sub : twelveGalleryTypeAH3 ⊆ G.labelSupport q :=
    (Finset.mem_powersetCard.mp (Finset.mem_inter.mp hEdge).1).1
  by_contra hnot
  have hbad : G.labelSupport q ∈ twelveGalleryNormalH3BadTriples :=
    Finset.mem_filter.mpr ⟨hs.1, hH3sub, hs.2.1, hs.2.2.1,
      hs.2.2.2, hnot⟩
  rw [twelveGalleryNormalH3BadTriples_eq_empty] at hbad
  simpa using hbad

noncomputable def twelveGalleryNormalLeftAtA3
    {Line : Type u} [Fintype Line] [DecidableEq Line]
    {A : FiniteProjectiveLineArrangement Line} {ell : Line}
    (G : A.LabelledFourStripGalleryEntrance ell)
    (census : TwelveGalleryTypeAActualCensus A) :
    Finset TwelveGalleryTypeAHEdge :=
  twelveGalleryTypeALeftHEdges.filter fun P =>
    twelveGalleryALabel 3 ∈
      G.labelSupport (twelveGalleryResidualVertexFor G census P)

noncomputable def twelveGalleryNormalLeftAtB3
    {Line : Type u} [Fintype Line] [DecidableEq Line]
    {A : FiniteProjectiveLineArrangement Line} {ell : Line}
    (G : A.LabelledFourStripGalleryEntrance ell)
    (census : TwelveGalleryTypeAActualCensus A) :
    Finset TwelveGalleryTypeAHEdge :=
  twelveGalleryTypeALeftHEdges.filter fun P =>
    twelveGalleryALabel 3 ∉
      G.labelSupport (twelveGalleryResidualVertexFor G census P)

theorem twelveGalleryNormalLeftAt_card_sum
    {Line : Type u} [Fintype Line] [DecidableEq Line]
    {A : FiniteProjectiveLineArrangement Line} {ell : Line}
    (G : A.LabelledFourStripGalleryEntrance ell)
    (census : TwelveGalleryTypeAActualCensus A) :
    (twelveGalleryNormalLeftAtA3 G census).card +
      (twelveGalleryNormalLeftAtB3 G census).card = 5 := by
  classical
  simpa [twelveGalleryNormalLeftAtA3, twelveGalleryNormalLeftAtB3] using
    (Finset.card_filter_add_card_filter_not
      (s := twelveGalleryTypeALeftHEdges)
      (p := fun P => twelveGalleryALabel 3 ∈
        G.labelSupport (twelveGalleryResidualVertexFor G census P)))

theorem two_mul_card_succ_le_of_pair_capacity
    {ι α : Type*} [DecidableEq ι] [DecidableEq α]
    (I : Finset ι) (F : ι → Finset α) (D N : Finset α)
    (hpairwise : (I : Set ι).PairwiseDisjoint F)
    (hcard : ∀ i ∈ I, (F i).card = 2)
    (hsub : ∀ i ∈ I, F i ⊆ N)
    (hDcard : D.card = 2) (hDsub : D ⊆ N)
    (hDdisjoint : Disjoint (I.biUnion F) D) :
    2 * (I.card + 1) ≤ N.card := by
  classical
  have hUnionSub : I.biUnion F ∪ D ⊆ N := by
    intro x hx
    rcases Finset.mem_union.mp hx with hx | hx
    · obtain ⟨i, hi, hxi⟩ := Finset.mem_biUnion.mp hx
      exact hsub i hi hxi
    · exact hDsub hx
  have hFamilyCard : (I.biUnion F).card = 2 * I.card := by
    rw [Finset.card_biUnion hpairwise]
    calc
      (∑ i ∈ I, (F i).card) = ∑ _i ∈ I, 2 := by
        apply Finset.sum_congr rfl
        intro i hi
        exact hcard i hi
      _ = 2 * I.card := by simp [Nat.mul_comm]
  have hUnionCard := Finset.card_union_of_disjoint hDdisjoint
  have hle := Finset.card_le_card hUnionSub
  rw [hUnionCard, hFamilyCard, hDcard] at hle
  omega

theorem twelveGallery_normal_leftAtA3_spec
    {Line : Type u} [Fintype Line] [DecidableEq Line]
    {A : FiniteProjectiveLineArrangement Line} {ell : Line}
    (G : A.LabelledFourStripGalleryEntrance ell)
    (census : TwelveGalleryTypeAActualCensus A)
    (homit : (.inr 2 : TwelveGalleryTypeABaseSlot) ∉
      twelveGalleryUpgradedBaseSlots G)
    {P : TwelveGalleryTypeAHEdge}
    (hP : P ∈ twelveGalleryNormalLeftAtA3 G census) :
    twelveGalleryALabel 3 ∈ G.labelSupport
        (twelveGalleryResidualVertexFor G census P) ∧
      P.1 ⊆ twelveGalleryTypeAA3Neighbours := by
  have hPparts := Finset.mem_filter.mp hP
  have hPleft := (Finset.mem_filter.mp hPparts.1).2
  have hq := twelveGalleryResidualVertexFor_mem G census P
  have hs := twelveGallery_normal_residual_support_spec G census homit hq
  have hEdge := twelveGalleryResidualVertexFor_edge_mem G census P
  have hPsub : P.1 ⊆
      G.labelSupport (twelveGalleryResidualVertexFor G census P) :=
    (Finset.mem_powersetCard.mp (Finset.mem_inter.mp hEdge).1).1
  rcases twelveGallery_normal_left_pole P.1 _ hPleft hs.1 hPsub
      hs.2.1 hs.2.2.1 hs.2.2.2 with hA | hB
  · exact ⟨hA.1, hA.2.2⟩
  · exact False.elim (hB.2.1 hPparts.2)

theorem twelveGallery_normal_leftAtB3_spec
    {Line : Type u} [Fintype Line] [DecidableEq Line]
    {A : FiniteProjectiveLineArrangement Line} {ell : Line}
    (G : A.LabelledFourStripGalleryEntrance ell)
    (census : TwelveGalleryTypeAActualCensus A)
    (homit : (.inr 2 : TwelveGalleryTypeABaseSlot) ∉
      twelveGalleryUpgradedBaseSlots G)
    {P : TwelveGalleryTypeAHEdge}
    (hP : P ∈ twelveGalleryNormalLeftAtB3 G census) :
    twelveGalleryBLabel 3 ∈ G.labelSupport
        (twelveGalleryResidualVertexFor G census P) ∧
      P.1 ⊆ twelveGalleryTypeAB3Neighbours := by
  have hPparts := Finset.mem_filter.mp hP
  have hPleft := (Finset.mem_filter.mp hPparts.1).2
  have hq := twelveGalleryResidualVertexFor_mem G census P
  have hs := twelveGallery_normal_residual_support_spec G census homit hq
  have hEdge := twelveGalleryResidualVertexFor_edge_mem G census P
  have hPsub : P.1 ⊆
      G.labelSupport (twelveGalleryResidualVertexFor G census P) :=
    (Finset.mem_powersetCard.mp (Finset.mem_inter.mp hEdge).1).1
  rcases twelveGallery_normal_left_pole P.1 _ hPleft hs.1 hPsub
      hs.2.1 hs.2.2.1 hs.2.2.2 with hA | hB
  · exact False.elim (hPparts.2 hA.1)
  · exact ⟨hB.1, hB.2.2⟩

private theorem twelveGalleryTypeALeftHEdge_card_table :
    ∀ P ∈ twelveGalleryTypeALeftHEdges, P.1.card = 2 := by decide

theorem twelveGallery_normal_H4_otherLabels_card
    {Line : Type u} [Fintype Line] [DecidableEq Line]
    {A : FiniteProjectiveLineArrangement Line} {ell : Line}
    (G : A.LabelledFourStripGalleryEntrance ell)
    (census : TwelveGalleryTypeAActualCensus A) :
    (G.labelSupport
          (twelveGalleryResidualVertexFor G census twelveGalleryTypeAH4Edge) \
        {twelveGalleryALabel 3}).card = 2 := by
  let q := twelveGalleryResidualVertexFor G census twelveGalleryTypeAH4Edge
  have hq := twelveGalleryResidualVertexFor_mem G census
    twelveGalleryTypeAH4Edge
  have hspec := twelveGalleryResidualTriple_support_spec G census hq
  have hEdge := twelveGalleryResidualVertexFor_edge_mem G census
    twelveGalleryTypeAH4Edge
  have hH4sub : twelveGalleryTypeAH4 ⊆ G.labelSupport q :=
    (Finset.mem_powersetCard.mp (Finset.mem_inter.mp hEdge).1).1
  have hpole : twelveGalleryALabel 3 ∈ G.labelSupport q :=
    hH4sub (by decide)
  rw [Finset.card_sdiff_of_subset (by simpa using hpole), hspec.1]
  decide

theorem twelveGallery_normal_H3_otherLabels_card
    {Line : Type u} [Fintype Line] [DecidableEq Line]
    {A : FiniteProjectiveLineArrangement Line} {ell : Line}
    (G : A.LabelledFourStripGalleryEntrance ell)
    (census : TwelveGalleryTypeAActualCensus A) :
    (G.labelSupport
          (twelveGalleryResidualVertexFor G census twelveGalleryTypeAH3Edge) \
        {twelveGalleryBLabel 3}).card = 2 := by
  let q := twelveGalleryResidualVertexFor G census twelveGalleryTypeAH3Edge
  have hq := twelveGalleryResidualVertexFor_mem G census
    twelveGalleryTypeAH3Edge
  have hspec := twelveGalleryResidualTriple_support_spec G census hq
  have hEdge := twelveGalleryResidualVertexFor_edge_mem G census
    twelveGalleryTypeAH3Edge
  have hH3sub : twelveGalleryTypeAH3 ⊆ G.labelSupport q :=
    (Finset.mem_powersetCard.mp (Finset.mem_inter.mp hEdge).1).1
  have hpole : twelveGalleryBLabel 3 ∈ G.labelSupport q :=
    hH3sub (by decide)
  rw [Finset.card_sdiff_of_subset (by simpa using hpole), hspec.1]
  decide

theorem twelveGallery_normal_A3_capacity
    {Line : Type u} [Fintype Line] [DecidableEq Line]
    {A : FiniteProjectiveLineArrangement Line} {ell : Line}
    (G : A.LabelledFourStripGalleryEntrance ell)
    (census : TwelveGalleryTypeAActualCensus A)
    (homit : (.inr 2 : TwelveGalleryTypeABaseSlot) ∉
      twelveGalleryUpgradedBaseSlots G) :
    2 * ((twelveGalleryNormalLeftAtA3 G census).card + 1) ≤ 6 := by
  classical
  let I := twelveGalleryNormalLeftAtA3 G census
  let F := fun P : TwelveGalleryTypeAHEdge => P.1
  let D := G.labelSupport
      (twelveGalleryResidualVertexFor G census twelveGalleryTypeAH4Edge) \
        {twelveGalleryALabel 3}
  let N := twelveGalleryTypeAA3Neighbours
  have hpairwise : (I : Set TwelveGalleryTypeAHEdge).PairwiseDisjoint F := by
    intro P hP Q hQ hPQ
    change Disjoint (F P) (F Q)
    rw [Finset.disjoint_left]
    intro a haP haQ
    have hspecP := twelveGallery_normal_leftAtA3_spec G census homit hP
    have hspecQ := twelveGallery_normal_leftAtA3_spec G census homit hQ
    have hEdgeP := twelveGalleryResidualVertexFor_edge_mem G census P
    have hEdgeQ := twelveGalleryResidualVertexFor_edge_mem G census Q
    have haP' : a ∈ G.labelSupport
        (twelveGalleryResidualVertexFor G census P) :=
      (Finset.mem_powersetCard.mp (Finset.mem_inter.mp hEdgeP).1).1 haP
    have haQ' : a ∈ G.labelSupport
        (twelveGalleryResidualVertexFor G census Q) :=
      (Finset.mem_powersetCard.mp (Finset.mem_inter.mp hEdgeQ).1).1 haQ
    have hne : twelveGalleryALabel 3 ≠ a := by
      intro h
      subst a
      exact (by decide : twelveGalleryALabel 3 ∉
        twelveGalleryTypeAA3Neighbours) (hspecP.2 haP)
    have hvertices : twelveGalleryResidualVertexFor G census P =
        twelveGalleryResidualVertexFor G census Q :=
      G.eq_of_two_common_labels hne hspecP.1 haP' hspecQ.1 haQ'
    exact hPQ (twelveGalleryResidualVertexFor_injective G census hvertices)
  have hcard : ∀ P ∈ I, (F P).card = 2 := by
    intro P hP
    exact twelveGalleryTypeALeftHEdge_card_table P
      (Finset.mem_filter.mp hP).1
  have hsub : ∀ P ∈ I, F P ⊆ N := by
    intro P hP
    exact (twelveGallery_normal_leftAtA3_spec G census homit hP).2
  have hDcard : D.card = 2 :=
    twelveGallery_normal_H4_otherLabels_card G census
  have hDsub : D ⊆ N :=
    twelveGallery_normal_H4_otherLabels_subset G census homit
  have hDdisjoint : Disjoint (I.biUnion F) D := by
    rw [Finset.disjoint_left]
    intro a haI haD
    obtain ⟨P, hP, haP⟩ := Finset.mem_biUnion.mp haI
    have hspecP := twelveGallery_normal_leftAtA3_spec G census homit hP
    have hEdgeP := twelveGalleryResidualVertexFor_edge_mem G census P
    have haP' : a ∈ G.labelSupport
        (twelveGalleryResidualVertexFor G census P) :=
      (Finset.mem_powersetCard.mp (Finset.mem_inter.mp hEdgeP).1).1 haP
    have hEdge4 := twelveGalleryResidualVertexFor_edge_mem G census
      twelveGalleryTypeAH4Edge
    have hpole4 : twelveGalleryALabel 3 ∈ G.labelSupport
        (twelveGalleryResidualVertexFor G census twelveGalleryTypeAH4Edge) :=
      (Finset.mem_powersetCard.mp (Finset.mem_inter.mp hEdge4).1).1
        (by decide)
    have ha4 : a ∈ G.labelSupport
        (twelveGalleryResidualVertexFor G census twelveGalleryTypeAH4Edge) :=
      (Finset.mem_sdiff.mp haD).1
    have hne : twelveGalleryALabel 3 ≠ a := by
      intro h
      subst a
      exact (by decide : twelveGalleryALabel 3 ∉
        twelveGalleryTypeAA3Neighbours) (hspecP.2 haP)
    have hvertices : twelveGalleryResidualVertexFor G census P =
        twelveGalleryResidualVertexFor G census twelveGalleryTypeAH4Edge :=
      G.eq_of_two_common_labels hne hspecP.1 haP' hpole4 ha4
    have hPEdge : P = twelveGalleryTypeAH4Edge :=
      twelveGalleryResidualVertexFor_injective G census hvertices
    have hPleft := (Finset.mem_filter.mp
      (Finset.mem_filter.mp hP).1).2
    rw [hPEdge] at hPleft
    exact (by decide : twelveGalleryTypeAH4 ∉ twelveGalleryTypeALeftH) hPleft
  have hcap := two_mul_card_succ_le_of_pair_capacity
    I F D N hpairwise hcard hsub hDcard hDsub hDdisjoint
  simpa [I, N] using hcap

theorem twelveGallery_normal_B3_capacity
    {Line : Type u} [Fintype Line] [DecidableEq Line]
    {A : FiniteProjectiveLineArrangement Line} {ell : Line}
    (G : A.LabelledFourStripGalleryEntrance ell)
    (census : TwelveGalleryTypeAActualCensus A)
    (homit : (.inr 2 : TwelveGalleryTypeABaseSlot) ∉
      twelveGalleryUpgradedBaseSlots G) :
    2 * ((twelveGalleryNormalLeftAtB3 G census).card + 1) ≤ 7 := by
  classical
  let I := twelveGalleryNormalLeftAtB3 G census
  let F := fun P : TwelveGalleryTypeAHEdge => P.1
  let D := G.labelSupport
      (twelveGalleryResidualVertexFor G census twelveGalleryTypeAH3Edge) \
        {twelveGalleryBLabel 3}
  let N := twelveGalleryTypeAB3Neighbours
  have hpairwise : (I : Set TwelveGalleryTypeAHEdge).PairwiseDisjoint F := by
    intro P hP Q hQ hPQ
    change Disjoint (F P) (F Q)
    rw [Finset.disjoint_left]
    intro a haP haQ
    have hspecP := twelveGallery_normal_leftAtB3_spec G census homit hP
    have hspecQ := twelveGallery_normal_leftAtB3_spec G census homit hQ
    have hEdgeP := twelveGalleryResidualVertexFor_edge_mem G census P
    have hEdgeQ := twelveGalleryResidualVertexFor_edge_mem G census Q
    have haP' : a ∈ G.labelSupport
        (twelveGalleryResidualVertexFor G census P) :=
      (Finset.mem_powersetCard.mp (Finset.mem_inter.mp hEdgeP).1).1 haP
    have haQ' : a ∈ G.labelSupport
        (twelveGalleryResidualVertexFor G census Q) :=
      (Finset.mem_powersetCard.mp (Finset.mem_inter.mp hEdgeQ).1).1 haQ
    have hne : twelveGalleryBLabel 3 ≠ a := by
      intro h
      subst a
      exact (by decide : twelveGalleryBLabel 3 ∉
        twelveGalleryTypeAB3Neighbours) (hspecP.2 haP)
    have hvertices : twelveGalleryResidualVertexFor G census P =
        twelveGalleryResidualVertexFor G census Q :=
      G.eq_of_two_common_labels hne hspecP.1 haP' hspecQ.1 haQ'
    exact hPQ (twelveGalleryResidualVertexFor_injective G census hvertices)
  have hcard : ∀ P ∈ I, (F P).card = 2 := by
    intro P hP
    exact twelveGalleryTypeALeftHEdge_card_table P
      (Finset.mem_filter.mp hP).1
  have hsub : ∀ P ∈ I, F P ⊆ N := by
    intro P hP
    exact (twelveGallery_normal_leftAtB3_spec G census homit hP).2
  have hDcard : D.card = 2 :=
    twelveGallery_normal_H3_otherLabels_card G census
  have hDsub : D ⊆ N :=
    twelveGallery_normal_H3_otherLabels_subset G census homit
  have hDdisjoint : Disjoint (I.biUnion F) D := by
    rw [Finset.disjoint_left]
    intro a haI haD
    obtain ⟨P, hP, haP⟩ := Finset.mem_biUnion.mp haI
    have hspecP := twelveGallery_normal_leftAtB3_spec G census homit hP
    have hEdgeP := twelveGalleryResidualVertexFor_edge_mem G census P
    have haP' : a ∈ G.labelSupport
        (twelveGalleryResidualVertexFor G census P) :=
      (Finset.mem_powersetCard.mp (Finset.mem_inter.mp hEdgeP).1).1 haP
    have hEdge3 := twelveGalleryResidualVertexFor_edge_mem G census
      twelveGalleryTypeAH3Edge
    have hpole3 : twelveGalleryBLabel 3 ∈ G.labelSupport
        (twelveGalleryResidualVertexFor G census twelveGalleryTypeAH3Edge) :=
      (Finset.mem_powersetCard.mp (Finset.mem_inter.mp hEdge3).1).1
        (by decide)
    have ha3 : a ∈ G.labelSupport
        (twelveGalleryResidualVertexFor G census twelveGalleryTypeAH3Edge) :=
      (Finset.mem_sdiff.mp haD).1
    have hne : twelveGalleryBLabel 3 ≠ a := by
      intro h
      subst a
      exact (by decide : twelveGalleryBLabel 3 ∉
        twelveGalleryTypeAB3Neighbours) (hspecP.2 haP)
    have hvertices : twelveGalleryResidualVertexFor G census P =
        twelveGalleryResidualVertexFor G census twelveGalleryTypeAH3Edge :=
      G.eq_of_two_common_labels hne hspecP.1 haP' hpole3 ha3
    have hPEdge : P = twelveGalleryTypeAH3Edge :=
      twelveGalleryResidualVertexFor_injective G census hvertices
    have hPleft := (Finset.mem_filter.mp
      (Finset.mem_filter.mp hP).1).2
    rw [hPEdge] at hPleft
    exact (by decide : twelveGalleryTypeAH3 ∉ twelveGalleryTypeALeftH) hPleft
  have hcap := two_mul_card_succ_le_of_pair_capacity
    I F D N hpairwise hcard hsub hDcard hDsub hDdisjoint
  simpa [I, N] using hcap

theorem twelveGallery_normal_absurd_of_omitted_B3
    {Line : Type u} [Fintype Line] [DecidableEq Line]
    {A : FiniteProjectiveLineArrangement Line} {ell : Line}
    (G : A.LabelledFourStripGalleryEntrance ell)
    (census : TwelveGalleryTypeAActualCensus A)
    (homit : (.inr 2 : TwelveGalleryTypeABaseSlot) ∉
      twelveGalleryUpgradedBaseSlots G) : False := by
  have hsplit := twelveGalleryNormalLeftAt_card_sum G census
  have hA := twelveGallery_normal_A3_capacity G census homit
  have hB := twelveGallery_normal_B3_capacity G census homit
  omega

def twelveGallerySwapLabel : GalleryLineLabel → GalleryLineLabel
  | .inl (.inl i) => .inl (.inr i)
  | .inl (.inr i) => .inl (.inl i)
  | .inr i => .inr i

def twelveGallerySwapLabelEquiv : GalleryLineLabel ≃ GalleryLineLabel where
  toFun := twelveGallerySwapLabel
  invFun := twelveGallerySwapLabel
  left_inv := by
    intro s
    cases s with
    | inl ab => cases ab <;> rfl
    | inr i => rfl
  right_inv := by
    intro s
    cases s with
    | inl ab => cases ab <;> rfl
    | inr i => rfl

def twelveGalleryReverseFinFour (i : Fin 4) : Fin 4 :=
  ⟨3 - i.1, by omega⟩

def twelveGalleryReverseFinThree (i : Fin 3) : Fin 3 :=
  ⟨2 - i.1, by omega⟩

def twelveGalleryReverseLabel : GalleryLineLabel → GalleryLineLabel
  | .inl (.inl i) => .inl (.inl (twelveGalleryReverseFinFour i))
  | .inl (.inr i) => .inl (.inr (twelveGalleryReverseFinFour i))
  | .inr i => .inr (twelveGalleryReverseFinThree i)

def twelveGalleryReverseLabelEquiv : GalleryLineLabel ≃ GalleryLineLabel where
  toFun := twelveGalleryReverseLabel
  invFun := twelveGalleryReverseLabel
  left_inv := by
    intro s
    cases s with
    | inl ab =>
        cases ab with
        | inl i =>
            apply congrArg (fun j => Sum.inl (Sum.inl j))
            apply Fin.ext
            simp [twelveGalleryReverseLabel, twelveGalleryReverseFinFour]
            omega
        | inr i =>
            apply congrArg (fun j => Sum.inl (Sum.inr j))
            apply Fin.ext
            simp [twelveGalleryReverseLabel, twelveGalleryReverseFinFour]
            omega
    | inr i =>
        apply congrArg Sum.inr
        apply Fin.ext
        simp [twelveGalleryReverseLabel, twelveGalleryReverseFinThree]
        omega
  right_inv := by
    intro s
    cases s with
    | inl ab =>
        cases ab with
        | inl i =>
            apply congrArg (fun j => Sum.inl (Sum.inl j))
            apply Fin.ext
            simp [twelveGalleryReverseLabel, twelveGalleryReverseFinFour]
            omega
        | inr i =>
            apply congrArg (fun j => Sum.inl (Sum.inr j))
            apply Fin.ext
            simp [twelveGalleryReverseLabel, twelveGalleryReverseFinFour]
            omega
    | inr i =>
        apply congrArg Sum.inr
        apply Fin.ext
        simp [twelveGalleryReverseLabel, twelveGalleryReverseFinThree]
        omega

@[simp]
theorem twelveGalleryReverseFinFour_involutive (i : Fin 4) :
    twelveGalleryReverseFinFour (twelveGalleryReverseFinFour i) = i := by
  apply Fin.ext
  simp [twelveGalleryReverseFinFour]
  omega

@[simp]
theorem twelveGalleryReverseFinThree_involutive (i : Fin 3) :
    twelveGalleryReverseFinThree (twelveGalleryReverseFinThree i) = i := by
  apply Fin.ext
  simp [twelveGalleryReverseFinThree]
  omega

theorem twelveGalleryReverseFinFour_left (i : Fin 3) :
    twelveGalleryReverseFinFour (galleryStripLeft i) =
      galleryStripRight (twelveGalleryReverseFinThree i) := by
  apply Fin.ext
  simp [twelveGalleryReverseFinFour, twelveGalleryReverseFinThree,
    galleryStripLeft, galleryStripRight]
  omega

theorem twelveGalleryReverseFinFour_right (i : Fin 3) :
    twelveGalleryReverseFinFour (galleryStripRight i) =
      galleryStripLeft (twelveGalleryReverseFinThree i) := by
  apply Fin.ext
  simp [twelveGalleryReverseFinFour, twelveGalleryReverseFinThree,
    galleryStripLeft, galleryStripRight]

/-- Exchange the upper and lower rails of the labelled strip. -/
def twelveGallerySwapEntrance
    {Line : Type u} [Fintype Line] [DecidableEq Line]
    {A : FiniteProjectiveLineArrangement Line} {ell : Line}
    (G : A.LabelledFourStripGalleryEntrance ell) :
    A.LabelledFourStripGalleryEntrance ell where
  lineEquiv := twelveGallerySwapLabelEquiv.trans G.lineEquiv
  rungVertex := G.rungVertex
  singletonVertex := G.singletonVertex
  upperVertex := G.lowerVertex
  lowerVertex := G.upperVertex
  rungIncident_iff := by
    intro i m
    change A.Incident (G.rungVertex i) m ↔
      m = ell ∨ m = G.b i ∨ m = G.a i
    rw [G.rungIncident_iff]
    tauto
  singletonIncident_iff := by
    intro i m
    change A.Incident (G.singletonVertex i) m ↔ m = ell ∨ m = G.c i
    exact G.singletonIncident_iff i m
  upperIncidence := by
    intro i
    change A.Incident (G.lowerVertex i) (G.b (galleryStripLeft i)) ∧
      A.Incident (G.lowerVertex i) (G.b (galleryStripRight i)) ∧
      A.Incident (G.lowerVertex i) (G.c i)
    exact G.lowerIncidence i
  lowerIncidence := by
    intro i
    change A.Incident (G.upperVertex i) (G.a (galleryStripLeft i)) ∧
      A.Incident (G.upperVertex i) (G.a (galleryStripRight i)) ∧
      A.Incident (G.upperVertex i) (G.c i)
    exact G.upperIncidence i

/-- Reverse the order of the four rungs and of the three intervening
bases. -/
def twelveGalleryReverseEntrance
    {Line : Type u} [Fintype Line] [DecidableEq Line]
    {A : FiniteProjectiveLineArrangement Line} {ell : Line}
    (G : A.LabelledFourStripGalleryEntrance ell) :
    A.LabelledFourStripGalleryEntrance ell where
  lineEquiv := twelveGalleryReverseLabelEquiv.trans G.lineEquiv
  rungVertex := fun i => G.rungVertex (twelveGalleryReverseFinFour i)
  singletonVertex := fun i =>
    G.singletonVertex (twelveGalleryReverseFinThree i)
  upperVertex := fun i => G.upperVertex (twelveGalleryReverseFinThree i)
  lowerVertex := fun i => G.lowerVertex (twelveGalleryReverseFinThree i)
  rungIncident_iff := by
    intro i m
    change A.Incident (G.rungVertex (twelveGalleryReverseFinFour i)) m ↔
      m = ell ∨ m = G.a (twelveGalleryReverseFinFour i) ∨
        m = G.b (twelveGalleryReverseFinFour i)
    exact G.rungIncident_iff (twelveGalleryReverseFinFour i) m
  singletonIncident_iff := by
    intro i m
    change A.Incident
        (G.singletonVertex (twelveGalleryReverseFinThree i)) m ↔
      m = ell ∨ m = G.c (twelveGalleryReverseFinThree i)
    exact G.singletonIncident_iff (twelveGalleryReverseFinThree i) m
  upperIncidence := by
    intro i
    change A.Incident
        (G.upperVertex (twelveGalleryReverseFinThree i))
          (G.a (twelveGalleryReverseFinFour (galleryStripLeft i))) ∧
      A.Incident (G.upperVertex (twelveGalleryReverseFinThree i))
          (G.a (twelveGalleryReverseFinFour (galleryStripRight i))) ∧
      A.Incident (G.upperVertex (twelveGalleryReverseFinThree i))
          (G.c (twelveGalleryReverseFinThree i))
    rw [twelveGalleryReverseFinFour_left,
      twelveGalleryReverseFinFour_right]
    have h := G.upperIncidence (twelveGalleryReverseFinThree i)
    exact ⟨h.2.1, h.1, h.2.2⟩
  lowerIncidence := by
    intro i
    change A.Incident
        (G.lowerVertex (twelveGalleryReverseFinThree i))
          (G.b (twelveGalleryReverseFinFour (galleryStripLeft i))) ∧
      A.Incident (G.lowerVertex (twelveGalleryReverseFinThree i))
          (G.b (twelveGalleryReverseFinFour (galleryStripRight i))) ∧
      A.Incident (G.lowerVertex (twelveGalleryReverseFinThree i))
          (G.c (twelveGalleryReverseFinThree i))
    rw [twelveGalleryReverseFinFour_left,
      twelveGalleryReverseFinFour_right]
    have h := G.lowerIncidence (twelveGalleryReverseFinThree i)
    exact ⟨h.2.1, h.1, h.2.2⟩

/-- Relabelling an entrance does not change the number of non-`ell`
supports through an actual point. -/
theorem twelveGallery_labelSupport_card_eq_of_entrances
    {Line : Type u} [Fintype Line] [DecidableEq Line]
    {A : FiniteProjectiveLineArrangement Line} {ell : Line}
    (G H : A.LabelledFourStripGalleryEntrance ell)
    (q : RealProjectivePoint) :
    (G.labelSupport q).card = (H.labelSupport q).card := by
  have hG := G.labelSupport_card_add_indicator q
  have hH := H.labelSupport_card_add_indicator q
  omega

theorem twelveGallery_omitted_B3_swap_of_omitted_A3
    {Line : Type u} [Fintype Line] [DecidableEq Line]
    {A : FiniteProjectiveLineArrangement Line} {ell : Line}
    (G : A.LabelledFourStripGalleryEntrance ell)
    (homit : (.inl 2 : TwelveGalleryTypeABaseSlot) ∉
      twelveGalleryUpgradedBaseSlots G) :
    (.inr 2 : TwelveGalleryTypeABaseSlot) ∉
      twelveGalleryUpgradedBaseSlots (twelveGallerySwapEntrance G) := by
  classical
  intro hnew
  apply homit
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, ?_⟩
  have hnewCard := (Finset.mem_filter.mp hnew).2
  calc
    (G.labelSupport
        (twelveGalleryBaseVertex G (.inl 2))).card =
        ((twelveGallerySwapEntrance G).labelSupport
          (G.upperVertex 2)).card := by
            simpa [twelveGalleryBaseVertex] using
              (twelveGallery_labelSupport_card_eq_of_entrances G
                (twelveGallerySwapEntrance G) (G.upperVertex 2))
    _ = 4 := by
      simpa [twelveGalleryBaseVertex, twelveGallerySwapEntrance] using hnewCard

theorem twelveGallery_omitted_B3_reverse_of_omitted_B1
    {Line : Type u} [Fintype Line] [DecidableEq Line]
    {A : FiniteProjectiveLineArrangement Line} {ell : Line}
    (G : A.LabelledFourStripGalleryEntrance ell)
    (homit : (.inr 0 : TwelveGalleryTypeABaseSlot) ∉
      twelveGalleryUpgradedBaseSlots G) :
    (.inr 2 : TwelveGalleryTypeABaseSlot) ∉
      twelveGalleryUpgradedBaseSlots (twelveGalleryReverseEntrance G) := by
  classical
  intro hnew
  apply homit
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, ?_⟩
  have hnewCard := (Finset.mem_filter.mp hnew).2
  calc
    (G.labelSupport
        (twelveGalleryBaseVertex G (.inr 0))).card =
        ((twelveGalleryReverseEntrance G).labelSupport
          (G.lowerVertex 0)).card := by
            simpa [twelveGalleryBaseVertex] using
              (twelveGallery_labelSupport_card_eq_of_entrances G
                (twelveGalleryReverseEntrance G) (G.lowerVertex 0))
    _ = 4 := by
      simpa [twelveGalleryBaseVertex, twelveGalleryReverseEntrance,
        twelveGalleryReverseFinThree] using hnewCard

theorem twelveGallery_omitted_A3_reverse_of_omitted_A1
    {Line : Type u} [Fintype Line] [DecidableEq Line]
    {A : FiniteProjectiveLineArrangement Line} {ell : Line}
    (G : A.LabelledFourStripGalleryEntrance ell)
    (homit : (.inl 0 : TwelveGalleryTypeABaseSlot) ∉
      twelveGalleryUpgradedBaseSlots G) :
    (.inl 2 : TwelveGalleryTypeABaseSlot) ∉
      twelveGalleryUpgradedBaseSlots (twelveGalleryReverseEntrance G) := by
  classical
  intro hnew
  apply homit
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, ?_⟩
  have hnewCard := (Finset.mem_filter.mp hnew).2
  calc
    (G.labelSupport
        (twelveGalleryBaseVertex G (.inl 0))).card =
        ((twelveGalleryReverseEntrance G).labelSupport
          (G.upperVertex 0)).card := by
            simpa [twelveGalleryBaseVertex] using
              (twelveGallery_labelSupport_card_eq_of_entrances G
                (twelveGalleryReverseEntrance G) (G.upperVertex 0))
    _ = 4 := by
      simpa [twelveGalleryBaseVertex, twelveGalleryReverseEntrance,
        twelveGalleryReverseFinThree] using hnewCard

/-- The actual labelled entrance and the restored `(6,14,3)` census are
already inconsistent; no additional cut-saturation callback is needed. -/
theorem twelveGallery_typeA_actual_absurd
    {Line : Type u} [Fintype Line] [DecidableEq Line]
    {A : FiniteProjectiveLineArrangement Line} {ell : Line}
    (G : A.LabelledFourStripGalleryEntrance ell)
    (census : TwelveGalleryTypeAActualCensus A) : False := by
  obtain ⟨s, hs, _hsUnique⟩ :=
    twelveGallery_existsUnique_omittedEligibleBase G census
  have hcases :
      s = (.inl 0 : TwelveGalleryTypeABaseSlot) ∨
      s = (.inr 0 : TwelveGalleryTypeABaseSlot) ∨
      s = (.inl 2 : TwelveGalleryTypeABaseSlot) ∨
      s = (.inr 2 : TwelveGalleryTypeABaseSlot) := by
    simpa [twelveGalleryEligibleBaseSlots] using hs.1
  rcases hcases with hA1 | hB1 | hA3 | hB3
  · subst s
    exact twelveGallery_normal_absurd_of_omitted_B3
      (twelveGallerySwapEntrance (twelveGalleryReverseEntrance G)) census
      (twelveGallery_omitted_B3_swap_of_omitted_A3
        (twelveGalleryReverseEntrance G)
        (twelveGallery_omitted_A3_reverse_of_omitted_A1 G hs.2))
  · subst s
    exact twelveGallery_normal_absurd_of_omitted_B3
      (twelveGalleryReverseEntrance G) census
      (twelveGallery_omitted_B3_reverse_of_omitted_B1 G hs.2)
  · subst s
    exact twelveGallery_normal_absurd_of_omitted_B3
      (twelveGallerySwapEntrance G) census
      (twelveGallery_omitted_B3_swap_of_omitted_A3 G hs.2)
  · subst s
    exact twelveGallery_normal_absurd_of_omitted_B3 G census hs.2

/-- The remaining corner edge emptied by each non-normal row.  Codes
`3,5,6` are `h3,h5,h6`; the normal row empties none. -/
def TwelveGalleryTypeACornerState.emptiedEdge :
    TwelveGalleryTypeACornerState → Option (Fin 7)
  | .b2a2a0 => some 3
  | .b2b3c1 => some 6
  | .b2c3a0 => none
  | .c3b3b0 => some 5

/-- Preservation of all seven cut edges leaves the unique normal row. -/
theorem twelveGalleryTypeACornerState_eq_normal_of_no_empty
    (s : TwelveGalleryTypeACornerState) (h : s.emptiedEdge = none) :
    s = .b2c3a0 := by
  cases s <;> simp [TwelveGalleryTypeACornerState.emptiedEdge] at h ⊢

/-- Numerical part of cut saturation.  A non-upgrading quadruple costs two
distinct `H` edges; the fixed cut has only the imported defect budget
`e+h ≤ 3`. -/
structure TwelveGalleryTypeACutCounts where
  upgradedBases : Nat
  consumedEdges : Nat
  upgradedBases_le_three : upgradedBases ≤ 3
  nonupgrade_cost : 2 * (3 - upgradedBases) ≤ consumedEdges
  defect : upgradedBases + consumedEdges ≤ 3

/-- The defect wall and the two-edge cost force all three quadruples to
upgrade bases and leave every edge of `H` unconsumed. -/
theorem TwelveGalleryTypeACutCounts.eq_three_and_zero
    (C : TwelveGalleryTypeACutCounts) :
    C.upgradedBases = 3 ∧ C.consumedEdges = 0 := by
  rcases C with ⟨upgradedBases, consumedEdges, hle, hcost, hdefect⟩
  dsimp at *
  interval_cases upgradedBases <;> omega

/-- The final two-pole packing data.  The five left `H` edges choose one of
the poles; the mandatory right-edge triangle at each pole has already used
one pair of its incident residual edges. -/
structure TwelveGalleryTypeATwoPoleCapacity where
  atA3 : Nat
  atB3 : Nat
  five_split : atA3 + atB3 = 5
  a3_capacity : 2 * (atA3 + 1) ≤ 6
  b3_capacity : 2 * (atB3 + 1) ≤ 7

/-- Six and seven residual incident edges leave capacity only `2+2`, while
the left cut asks for five edge-disjoint residual triangles. -/
theorem TwelveGalleryTypeATwoPoleCapacity.false
    (C : TwelveGalleryTypeATwoPoleCapacity) : False := by
  rcases C with ⟨atA3, atB3, hsplit, hA3, hB3⟩
  omega

/-- Lossless finite certificate exported by the labelled gallery.  Its four
fields are exactly the four non-arithmetic checks in the paper proof:
the seven-edge cut count, the corner table, survival of all seven cut edges,
and the final two-pole packing. -/
structure TwelveGalleryTypeAFiniteCutCertificate where
  cut : TwelveGalleryTypeACutCounts
  x : Fin 4
  y : Fin 4
  z : Fin 4
  corner_table :
    cut.upgradedBases = 3 → cut.consumedEdges = 0 →
      (x, y) ∈ twelveGalleryTypeACornerTable z
  cut_edges_survive :
    cut.upgradedBases = 3 → cut.consumedEdges = 0 →
      ∀ s : TwelveGalleryTypeACornerState,
        s.xCode = x → s.yCode = y → s.zCode = z →
          s.emptiedEdge = none
  normal_capacity :
    cut.upgradedBases = 3 → cut.consumedEdges = 0 →
      x = 1 → y = 3 → z = 0 → TwelveGalleryTypeATwoPoleCapacity

/-- The finite cut-saturation certificate is contradictory.  The proof is
the literal chain `e+h≤3` → four states → unique normal form → `5>4`. -/
theorem TwelveGalleryTypeAFiniteCutCertificate.false
    (C : TwelveGalleryTypeAFiniteCutCertificate) : False := by
  obtain ⟨he, hh⟩ := C.cut.eq_three_and_zero
  obtain ⟨s, hsx, hsy, hsz⟩ :=
    twelveGalleryTypeACornerTable_eq_state C.x C.y C.z
      (C.corner_table he hh)
  have hempty : s.emptiedEdge = none :=
    C.cut_edges_survive he hh s hsx hsy hsz
  have hsnormal : s = .b2c3a0 :=
    twelveGalleryTypeACornerState_eq_normal_of_no_empty s hempty
  subst s
  have hx : C.x = 1 := by
    simpa [TwelveGalleryTypeACornerState.xCode] using hsx.symm
  have hy : C.y = 3 := by
    simpa [TwelveGalleryTypeACornerState.yCode] using hsy.symm
  have hz : C.z = 0 := by
    simpa [TwelveGalleryTypeACornerState.zCode] using hsz.symm
  exact (C.normal_capacity he hh hx hy hz).false

/-- Arrangement-level extraction seam.  It deliberately takes the actual
census and the lossless labelled entrance as parameters, while exporting
only the finite data consumed by the theorem above. -/
structure TwelveGalleryTypeACutSaturationInput
    {Line : Type u} [Fintype Line] [DecidableEq Line]
    (A : FiniteProjectiveLineArrangement Line) (ell : Line)
    (G : A.LabelledFourStripGalleryEntrance ell)
    (census : TwelveGalleryTypeAActualCensus A) where
  finiteCertificate : TwelveGalleryTypeAFiniteCutCertificate

/-- Unconditional construction of the legacy extraction interface.  The
actual entrance/census contradiction above is stronger than every field of
that interface. -/
noncomputable def twelveGallery_typeA_cutSaturationInput
    {Line : Type u} [Fintype Line] [DecidableEq Line]
    (A : FiniteProjectiveLineArrangement Line) (ell : Line)
    (G : A.LabelledFourStripGalleryEntrance ell)
    (census : TwelveGalleryTypeAActualCensus A) :
    TwelveGalleryTypeACutSaturationInput A ell G census :=
  (twelveGallery_typeA_actual_absurd G census).elim

/-- Configuration-free Type-A endpoint.  The entrance supplies the complete
`3D+4T` word, `census` supplies the actual `(6,14,3)` vertex profile, and the
extraction seam supplies precisely the seven-edge cut certificate. -/
theorem twelveGallery_typeA_cutSaturation_absurd
    {Line : Type u} [Fintype Line] [DecidableEq Line]
    (A : FiniteProjectiveLineArrangement Line) (ell : Line)
    (G : A.LabelledFourStripGalleryEntrance ell)
    (census : TwelveGalleryTypeAActualCensus A)
    (input : TwelveGalleryTypeACutSaturationInput A ell G census) : False :=
  input.finiteCertificate.false

/-- Callback-free arrangement-level endpoint. -/
theorem twelveGallery_typeA_cutSaturation_absurd_unconditional
    {Line : Type u} [Fintype Line] [DecidableEq Line]
    (A : FiniteProjectiveLineArrangement Line) (ell : Line)
    (G : A.LabelledFourStripGalleryEntrance ell)
    (census : TwelveGalleryTypeAActualCensus A) : False :=
  twelveGallery_typeA_actual_absurd G census

/-! ## Configuration-level Type-A assembly -/

/-- A genuine original line through the pivot gives the corresponding
marked vertex of the distinguished restored dual line. -/
noncomputable def twelveGalleryPivotLineToGap
    {alpha : Type u} [Fintype alpha] [DecidableEq alpha]
    (cfg : Configuration alpha) (p : alpha)
    (L : TwelveDirectionLinesThroughPivot cfg p) :
    (labelDualArrangement (restoredPivotConfiguration cfg p)).CircularGapSlot
      none := by
  classical
  let b : BlockThrough cfg p :=
    ⟨Sum.inl L.1, mem_lineSupport.mpr L.2⟩
  let D := blockToRestoredLine cfg p b
  refine ⟨determinedLineDualVertex (restoredPivotConfiguration cfg p) D, ?_⟩
  rw [lineVertexSet_eq_determinedLineDualVerticesThroughLabel]
  unfold determinedLineDualVerticesThroughLabel
  apply Finset.mem_image.mpr
  refine ⟨D, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, rfl⟩
  apply mem_lineSupport.mp
  exact (none_mem_lineSupport_blockToRestoredLine_iff_line cfg p b).mpr rfl

/-- The preceding map is lossless: marked vertices on the pivot dual line
are exactly original determined lines through the pivot. -/
noncomputable def twelveGalleryPivotLineGapEquiv
    {alpha : Type u} [Fintype alpha] [DecidableEq alpha]
    (cfg : Configuration alpha) (p : alpha) :
    TwelveDirectionLinesThroughPivot cfg p ≃
      (labelDualArrangement
        (restoredPivotConfiguration cfg p)).CircularGapSlot none := by
  classical
  apply Equiv.ofBijective (twelveGalleryPivotLineToGap cfg p)
  constructor
  · intro L M hLM
    let bL : BlockThrough cfg p :=
      ⟨Sum.inl L.1, mem_lineSupport.mpr L.2⟩
    let bM : BlockThrough cfg p :=
      ⟨Sum.inl M.1, mem_lineSupport.mpr M.2⟩
    have hv := congrArg Subtype.val hLM
    have hD : blockToRestoredLine cfg p bL =
        blockToRestoredLine cfg p bM := by
      apply determinedLineDualVertex_injective
        (restoredPivotConfiguration cfg p)
      simpa [twelveGalleryPivotLineToGap, bL, bM] using hv
    have hb : bL = bM := blockToRestoredLine_injective cfg p hD
    apply Subtype.ext
    exact Sum.inl_injective (congrArg Subtype.val hb)
  · intro q
    have hq : q.1 ∈ determinedLineDualVerticesThroughLabel
        (restoredPivotConfiguration cfg p) none := by
      simpa only [lineVertexSet_eq_determinedLineDualVerticesThroughLabel] using q.2
    unfold determinedLineDualVerticesThroughLabel at hq
    obtain ⟨D, hD, hDq⟩ := Finset.mem_image.mp hq
    let Dr : TwelveDirectionRestoredLinesThroughNone cfg p :=
      ⟨D, (Finset.mem_filter.mp hD).2⟩
    obtain ⟨L, hL⟩ :=
      (twelveDirectionLinesThroughPivotEquivRestoredNone cfg p).surjective Dr
    refine ⟨L, ?_⟩
    apply Subtype.ext
    have hDL : blockToRestoredLine cfg p
        ⟨Sum.inl L.1, mem_lineSupport.mpr L.2⟩ = D := by
      simpa [twelveDirectionLinesThroughPivotEquivRestoredNone, Dr] using
        congrArg Subtype.val hL
    change determinedLineDualVertex (restoredPivotConfiguration cfg p)
        (blockToRestoredLine cfg p
          ⟨Sum.inl L.1, mem_lineSupport.mpr L.2⟩) = q.1
    rw [hDL]
    exact hDq

theorem twelveGalleryPivotLineToGap_multiplicity
    {alpha : Type u} [Fintype alpha] [DecidableEq alpha]
    (cfg : Configuration alpha) (p : alpha)
    (L : TwelveDirectionLinesThroughPivot cfg p) :
    (labelDualArrangement (restoredPivotConfiguration cfg p)).multiplicity
        (twelveGalleryPivotLineToGap cfg p L).1 =
      (lineSupport cfg L.1).card := by
  let b : BlockThrough cfg p :=
    ⟨Sum.inl L.1, mem_lineSupport.mpr L.2⟩
  change (labelDualArrangement
      (restoredPivotConfiguration cfg p)).multiplicity
        (determinedLineDualVertex (restoredPivotConfiguration cfg p)
          (blockToRestoredLine cfg p b)) = _
  rw [labelDual_multiplicity_determinedLine]
  have hcard := card_lineSupport_blockToRestoredLine cfg p b
  simpa [b, geometricBlockSupport] using hcard

theorem twelveGallery_typeA_pivotLine_card_eq_two_or_three
    {alpha : Type u} [Fintype alpha] [DecidableEq alpha]
    (cfg : Configuration alpha) (p : alpha)
    (hcap : BlockSizeCap (blockSystem cfg) 6)
    (hl4 : (blockSystem cfg).lineDegree 4 p = 0)
    (hl5 : (blockSystem cfg).lineDegree 5 p = 0)
    (hl6 : (blockSystem cfg).lineDegree 6 p = 0)
    (L : TwelveDirectionLinesThroughPivot cfg p) :
    (lineSupport cfg L.1).card = 2 ∨
      (lineSupport cfg L.1).card = 3 := by
  rcases
      lineSupport_card_eq_two_or_three_or_four_or_five_of_local_twelveDirection
        cfg p hcap hl6 L.1 L.2 with h2 | h3 | h4 | h5
  · exact Or.inl h2
  · exact Or.inr h3
  · have hpos : 0 < Fintype.card
        (DeterminedLineOfSizeThrough cfg p 4) := by
      apply Fintype.card_pos_iff.mpr
      exact ⟨⟨⟨L.1, h4⟩, mem_lineSupport.mpr L.2⟩⟩
    rw [← lineDegree_eq_card_determinedLineOfSizeThrough cfg p 4, hl4] at hpos
    omega
  · have hpos : 0 < Fintype.card
        (DeterminedLineOfSizeThrough cfg p 5) := by
      apply Fintype.card_pos_iff.mpr
      exact ⟨⟨⟨L.1, h5⟩, mem_lineSupport.mpr L.2⟩⟩
    rw [← lineDegree_eq_card_determinedLineOfSizeThrough cfg p 5, hl5] at hpos
    omega

theorem twelveGallery_typeA_gapCard_seven
    {alpha : Type u} [Fintype alpha] [DecidableEq alpha]
    (cfg : Configuration alpha) (p : alpha)
    (hcap : BlockSizeCap (blockSystem cfg) 6)
    (census : TwelveGalleryTypeARestoredDualCensus cfg p)
    (hl3 : (blockSystem cfg).lineDegree 3 p = 4)
    (hl4 : (blockSystem cfg).lineDegree 4 p = 0)
    (hl5 : (blockSystem cfg).lineDegree 5 p = 0)
    (hl6 : (blockSystem cfg).lineDegree 6 p = 0) :
    Fintype.card
      ((labelDualArrangement
        (restoredPivotConfiguration cfg p)).CircularGapSlot none) = 7 := by
  change Fintype.card
      {q // q ∈ (labelDualArrangement
        (restoredPivotConfiguration cfg p)).lineVertexSet none} = 7
  rw [Fintype.card_coe,
    ← twelveDirectionPivotLineVertices_eq_lineVertexSet_none cfg p,
    card_twelveDirectionPivotLineVertices_eq_distinguishedLineVertices_of_lineDegree_six_eq_zero
      cfg p hcap hl6,
    census.lineDegree_two, hl3, hl4, hl5]

/-- Reordering the two subtype refinements does not lose the size tag. -/
def twelveGalleryLinesThroughPivotAtSizeEquiv
    {alpha : Type u} [Fintype alpha] [DecidableEq alpha]
    (cfg : Configuration alpha) (p : alpha) (s : Nat) :
    {L : TwelveDirectionLinesThroughPivot cfg p //
        (lineSupport cfg L.1).card = s} ≃
      DeterminedLineOfSizeThrough cfg p s where
  toFun L := ⟨⟨L.1.1, L.2⟩, mem_lineSupport.mpr L.1.2⟩
  invFun L := ⟨⟨L.1.1, mem_lineSupport.mp L.2⟩, L.1.2⟩
  left_inv L := by
    apply Subtype.ext
    apply Subtype.ext
    rfl
  right_inv L := by
    apply Subtype.ext
    apply Subtype.ext
    rfl

theorem twelveGallery_typeA_word_complete
    {alpha : Type u} [Fintype alpha] [DecidableEq alpha]
    (cfg : Configuration alpha) (p : alpha)
    (hcap : BlockSizeCap (blockSystem cfg) 6)
    (hl4 : (blockSystem cfg).lineDegree 4 p = 0)
    (hl5 : (blockSystem cfg).lineDegree 5 p = 0)
    (hl6 : (blockSystem cfg).lineDegree 6 p = 0)
    (hgapCard : Fintype.card
      ((labelDualArrangement
        (restoredPivotConfiguration cfg p)).CircularGapSlot none) = 7) :
    ∀ i : Fin 7,
      (labelDualArrangement
          (restoredPivotConfiguration cfg p)).multiplicity
          ((labelDualArrangement (restoredPivotConfiguration cfg p)).circularGapCyclicLabelSeven
            none hgapCard i).1 = 2 ∨
      (labelDualArrangement
          (restoredPivotConfiguration cfg p)).multiplicity
          ((labelDualArrangement (restoredPivotConfiguration cfg p)).circularGapCyclicLabelSeven
            none hgapCard i).1 = 3 := by
  intro i
  let A := labelDualArrangement (restoredPivotConfiguration cfg p)
  let q : A.CircularGapSlot none :=
    A.circularGapCyclicLabelSeven none hgapCard i
  let L : TwelveDirectionLinesThroughPivot cfg p :=
    (twelveGalleryPivotLineGapEquiv cfg p).symm q
  have hq : twelveGalleryPivotLineToGap cfg p L = q :=
    (twelveGalleryPivotLineGapEquiv cfg p).apply_symm_apply q
  have hmult := twelveGalleryPivotLineToGap_multiplicity cfg p L
  have hsize := twelveGallery_typeA_pivotLine_card_eq_two_or_three
    cfg p hcap hl4 hl5 hl6 L
  change A.multiplicity q.1 = 2 ∨ A.multiplicity q.1 = 3
  rw [← hq, hmult]
  exact hsize

theorem twelveGallery_typeA_word_ordinary_card
    {alpha : Type u} [Fintype alpha] [DecidableEq alpha]
    (cfg : Configuration alpha) (p : alpha)
    (census : TwelveGalleryTypeARestoredDualCensus cfg p)
    (hgapCard : Fintype.card
      ((labelDualArrangement
        (restoredPivotConfiguration cfg p)).CircularGapSlot none) = 7) :
    ((Finset.univ : Finset (Fin 7)).filter fun i =>
      (labelDualArrangement
          (restoredPivotConfiguration cfg p)).multiplicity
          ((labelDualArrangement (restoredPivotConfiguration cfg p)).circularGapCyclicLabelSeven
            none hgapCard i).1 = 2).card = 3 := by
  classical
  let A := labelDualArrangement (restoredPivotConfiguration cfg p)
  let word : Fin 7 → Nat := fun i =>
    A.multiplicity (A.circularGapCyclicLabelSeven none hgapCard i).1
  let C : Fin 7 ≃ TwelveDirectionLinesThroughPivot cfg p :=
    (A.circularGapCyclicLabelSeven none hgapCard).trans
      (twelveGalleryPivotLineGapEquiv cfg p).symm
  have hpres (i : Fin 7) :
      word i = (lineSupport cfg (C i).1).card := by
    have hm := twelveGalleryPivotLineToGap_multiplicity cfg p (C i)
    have hq := (twelveGalleryPivotLineGapEquiv cfg p).apply_symm_apply
      (A.circularGapCyclicLabelSeven none hgapCard i)
    change twelveGalleryPivotLineToGap cfg p (C i) =
      A.circularGapCyclicLabelSeven none hgapCard i at hq
    rw [hq] at hm
    exact hm
  let E : {i : Fin 7 // word i = 2} ≃
      {L : TwelveDirectionLinesThroughPivot cfg p //
        (lineSupport cfg L.1).card = 2} :=
    C.subtypeEquiv (fun i => by rw [hpres i])
  calc
    ((Finset.univ : Finset (Fin 7)).filter fun i =>
        (labelDualArrangement
            (restoredPivotConfiguration cfg p)).multiplicity
            ((labelDualArrangement (restoredPivotConfiguration cfg p)).circularGapCyclicLabelSeven
              none hgapCard i).1 = 2).card =
        Fintype.card {i : Fin 7 // word i = 2} := by
          simpa [A, word] using
            (Fintype.card_subtype (fun i : Fin 7 => word i = 2)).symm
    _ = Fintype.card
        {L : TwelveDirectionLinesThroughPivot cfg p //
          (lineSupport cfg L.1).card = 2} := Fintype.card_congr E
    _ = Fintype.card (DeterminedLineOfSizeThrough cfg p 2) :=
      Fintype.card_congr (twelveGalleryLinesThroughPivotAtSizeEquiv cfg p 2)
    _ = (blockSystem cfg).lineDegree 2 p :=
      (lineDegree_eq_card_determinedLineOfSizeThrough cfg p 2).symm
    _ = 3 := census.lineDegree_two

/-- Full configuration-level Type-A contradiction. -/
theorem twelveGallery_typeA_forbidden
    {alpha : Type u} [Fintype alpha] [DecidableEq alpha]
    (H : RealProjectiveArrangementGlobalInput.{u})
    (Kelly : RealPlaneKellyMoserPrinciple.{u})
    (Gram : RealPlaneTwelveGramPrinciple.{u})
    (cfg : Configuration alpha) (hadm : Admissible cfg)
    (hcard : Fintype.card alpha = 12)
    (hcap : BlockSizeCap (blockSystem cfg) 6) :
    ¬ ∃ p : alpha,
      (blockSystem cfg).blockDegree 3 p = 7 ∧
      (blockSystem cfg).blockDegree 4 p = 10 ∧
      (blockSystem cfg).blockDegree 5 p = 3 ∧
      (blockSystem cfg).blockDegree 6 p = 0 ∧
      (blockSystem cfg).lineDegree 3 p = 4 ∧
      (blockSystem cfg).lineDegree 4 p = 0 ∧
      (blockSystem cfg).lineDegree 5 p = 0 ∧
      (blockSystem cfg).lineDegree 6 p = 0 := by
  classical
  rintro ⟨p, hd3, hd4, hd5, hd6, hl3, hl4, hl5, hl6⟩
  let Mel : RealPlaneMelchiorPrinciple.{u} :=
    realPlaneMelchiorPrincipleOfGlobalInput H
  let EvenArr : RealPlaneEvenArrangementPrinciple.{u} :=
    realPlaneEvenArrangementPrincipleOfGlobalInput H
  have hrows : TwelveFiveLocalRows (blockSystem cfg) p :=
    twelveFiveLocalRows_of_configuration
      Mel EvenArr Kelly Gram cfg hadm hcard hcap p
  have census : TwelveGalleryTypeARestoredDualCensus cfg p :=
    twelveGallery_typeA_restoredDualCensus cfg hcap p hrows
      hd3 hd4 hd5 hd6 hl3 hl4 hl5 hl6
  let restored := restoredPivotConfiguration cfg p
  let A := labelDualArrangement restored
  have hnon : Noncollinear restored := by
    simpa only [restored] using
      restoredPivotConfiguration_noncollinear cfg hadm (by omega) p
  have hA : A.NonPencil := by
    simpa only [A] using
      labelDualArrangement_nonPencil_of_noncollinear restored hnon
  have hAcard : Fintype.card (Option (Erdos506.V3.AwayFrom p)) = 12 := by
    rw [Fintype.card_option, Erdos506.V3.card_awayFrom, hcard]
  have hgapCard : Fintype.card (A.CircularGapSlot none) = 7 := by
    simpa only [A, restored] using
      twelveGallery_typeA_gapCard_seven cfg p hcap census hl3 hl4 hl5 hl6
  have htri : ∀ F : A.ArrangementFace,
      (A.arrangementFaceBoundary F).card = 3 := by
    simpa only [A, restored] using
      twelveGallery_typeA_all_restoredPivot_dual_faces_triangular
        H Kelly Gram cfg hadm hcard hcap p
          hd3 hd4 hd5 hd6 hl3 hl4 hl5 hl6
  have hnoConcurrent : ∀ l : Option (Erdos506.V3.AwayFrom p),
      ¬ ∃ q : RealProjectivePoint,
        ∀ m : Option (Erdos506.V3.AwayFrom p), m ≠ l → A.Incident q m := by
    simpa only [A, restored] using
      twelveGallery_typeA_restored_no_concurrent_away
        cfg hcard hcap p hl6
  let word : Fin 7 → Nat := fun i =>
    A.multiplicity (A.circularGapCyclicLabelSeven none hgapCard i).1
  have hcomplete : ∀ i, word i = 2 ∨ word i = 3 := by
    simpa only [word, A, restored] using
      twelveGallery_typeA_word_complete
        cfg p hcap hl4 hl5 hl6 hgapCard
  have hthree :
      ((Finset.univ : Finset (Fin 7)).filter fun i => word i = 2).card = 3 := by
    simpa only [word, A, restored] using
      twelveGallery_typeA_word_ordinary_card cfg p census hgapCard
  have hnoAdjacent : ∀ i, word i = 2 →
      word (finRotate 7 i) ≠ 2 := by
    intro i hi hnext
    have hi' : A.multiplicity
        (A.circularGapCyclicLabelSeven none hgapCard i).1 = 2 := by
      simpa only [word] using hi
    have hnext' : A.multiplicity
        (A.circularGapSuccessor none
          (A.circularGapCyclicLabelSeven none hgapCard i)).1 = 2 := by
      rw [A.circularGapSuccessor_apply_labelSeven none hgapCard i]
      simpa only [word] using hnext
    have hconc :=
      A.exists_concurrent_away_of_circularGap_dd_of_all_faces_triangular
        hA none (A.circularGapCyclicLabelSeven none hgapCard i)
          hi' hnext' htri
    exact (hnoConcurrent none) hconc
  have hword : IsTTDTDTD word :=
    isTTDTDTD_of_three_ordinary_of_no_adjacent
      word hcomplete hthree hnoAdjacent
  obtain ⟨G⟩ := exists_labelledFourStripGalleryEntrance_of_isTTDTDTD
    A hA hAcard none hgapCard hword htri hnoConcurrent
  apply twelveGallery_typeA_actual_absurd G
  simpa only [A, restored] using census.toActualCensus

/-- The callback-free Type-A field consumed by the twelve-point router. -/
noncomputable def realPlaneTwelveGalleryTypeAPrinciple
    (H : RealProjectiveArrangementGlobalInput.{u})
    (Kelly : RealPlaneKellyMoserPrinciple.{u})
    (Gram : RealPlaneTwelveGramPrinciple.{u}) :
    RealPlaneTwelveGalleryTypeAPrinciple.{u} where
  typeAForbidden := by
    intro alpha _ _ cfg hadm hcard hcap
    exact twelveGallery_typeA_forbidden
      H Kelly Gram cfg hadm hcard hcap

end Erdos506.V1
