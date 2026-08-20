import Erdos506.Incidence.ProjectiveCompletion
import Erdos506.Incidence.SpannedLines

/-!
# Finite projective line arrangements

This module is the algebraic part of the bridge from a finite affine
configuration to the projective-line cellulation used by Melchior's theorem.
It intentionally contains no Euler relation, no faces, and no parity
argument.

The only geometric input of a `FiniteProjectiveLineArrangement` is a finite
family of *distinct* projective covectors.  From it we construct the finite
set of actual projective intersection points, not a set of formal pairs.
Consequently concurrent pairs are identified automatically.  The last
structure in the file states precisely the remaining affine-to-projective
realization obligation for `DeterminedLine cfg`.
-/

namespace Erdos506.Incidence

open Erdos506.Finite
open Erdos506.V4

/-- A finite family of pairwise distinct real projective lines. -/
structure FiniteProjectiveLineArrangement
    (Line : Type*) where
  projectiveLine : Line → RealProjectiveLine
  projectiveLine_injective : Function.Injective projectiveLine

namespace FiniteProjectiveLineArrangement

variable {Line : Type*} [Fintype Line] [DecidableEq Line]

/-- The (total) intersection operation used to enumerate vertices.  Its value
on equal indices is irrelevant and is excluded by `vertexSet`; making it
total keeps the finite-image construction elementary. -/
noncomputable def intersection
    (A : FiniteProjectiveLineArrangement Line) (l m : Line) :
    RealProjectivePoint :=
  if h : l = m then A.projectiveLine l else
    projectiveLineIntersection (A.projectiveLine l) (A.projectiveLine m) (by
      intro hline
      apply h
      exact A.projectiveLine_injective hline)

/-- All actual intersections of two different arrangement lines.  Since this
is a `Finset` of projective points, all concurrent pair-intersections are
represented by one vertex. -/
noncomputable def vertexSet
    (A : FiniteProjectiveLineArrangement Line) : Finset RealProjectivePoint := by
  classical
  let pairs : Finset (Line × Line) := Finset.univ.product Finset.univ
  exact (pairs.filter fun lm => lm.1 ≠ lm.2).image
    (fun lm => A.intersection lm.1 lm.2)

/-- Incidence of an actual projective point with an indexed arrangement line. -/
def Incident (A : FiniteProjectiveLineArrangement Line)
    (p : RealProjectivePoint) (l : Line) : Prop :=
  p ∈ A.projectiveLine l

/-- The intersection of two different indexed lines is a vertex. -/
theorem intersection_mem_vertexSet
    (A : FiniteProjectiveLineArrangement Line) {l m : Line} (hlm : l ≠ m) :
    A.intersection l m ∈ A.vertexSet := by
  classical
  change A.intersection l m ∈
    ((Finset.univ.product Finset.univ).filter
      (fun lm : Line × Line => lm.1 ≠ lm.2)).image
        (fun lm => A.intersection lm.1 lm.2)
  apply Finset.mem_image.mpr
  exact ⟨(l, m), by simp [hlm], rfl⟩

/-- The constructed intersection is incident with its first line. -/
theorem intersection_incident_left
    (A : FiniteProjectiveLineArrangement Line) {l m : Line} (hlm : l ≠ m) :
    A.Incident (A.intersection l m) l := by
  unfold Incident intersection
  rw [dif_neg hlm]
  exact projectiveLineIntersection_mem_left (by
    intro hline
    apply hlm
    exact A.projectiveLine_injective hline)

/-- The constructed intersection is incident with its second line. -/
theorem intersection_incident_right
    (A : FiniteProjectiveLineArrangement Line) {l m : Line} (hlm : l ≠ m) :
    A.Incident (A.intersection l m) m := by
  unfold Incident intersection
  rw [dif_neg hlm]
  exact projectiveLineIntersection_mem_right (by
    intro hline
    apply hlm
    exact A.projectiveLine_injective hline)

/-- Every vertex of `vertexSet` is produced by a pair of different lines. -/
theorem exists_lines_of_mem_vertexSet
    (A : FiniteProjectiveLineArrangement Line) {p : RealProjectivePoint}
    (hp : p ∈ A.vertexSet) :
    ∃ l m : Line, l ≠ m ∧ A.intersection l m = p := by
  classical
  unfold vertexSet at hp
  obtain ⟨lm, hlm, hvalue⟩ := Finset.mem_image.mp hp
  rcases lm with ⟨l, m⟩
  exact ⟨l, m, (Finset.mem_filter.mp hlm).2, hvalue⟩

/-- Any point incident with two different arrangement lines is their
constructed intersection.  This is the projective uniqueness theorem in the
form needed to merge concurrent pair-indices into genuine vertices. -/
theorem eq_intersection_of_incident
    (A : FiniteProjectiveLineArrangement Line) {l m : Line} (hlm : l ≠ m)
    {p : RealProjectivePoint} (hpl : A.Incident p l) (hpm : A.Incident p m) :
    p = A.intersection l m := by
  have hlines : A.projectiveLine l ≠ A.projectiveLine m := by
    intro hline
    apply hlm
    exact A.projectiveLine_injective hline
  obtain ⟨q, hq, hunique⟩ :=
    existsUnique_projectiveLineIntersection
      (A.projectiveLine l) (A.projectiveLine m) hlines
  have hpq : p = q := hunique p ⟨hpl, hpm⟩
  have hiq : A.intersection l m = q := hunique (A.intersection l m) ⟨
    A.intersection_incident_left hlm,
    A.intersection_incident_right hlm⟩
  exact hpq.trans hiq.symm

/-- The number of arrangement lines through a projective point. -/
noncomputable def multiplicity
    (A : FiniteProjectiveLineArrangement Line) (p : RealProjectivePoint) : Nat := by
  classical
  exact (Finset.univ.filter fun l => A.Incident p l).card

/-- The two lines defining a vertex are both counted by its multiplicity. -/
theorem two_le_multiplicity_intersection
    (A : FiniteProjectiveLineArrangement Line) {l m : Line} (hlm : l ≠ m) :
    2 ≤ A.multiplicity (A.intersection l m) := by
  classical
  unfold multiplicity
  have hsub : ({l, m} : Finset Line) ⊆
      Finset.univ.filter fun n => A.Incident (A.intersection l m) n := by
    intro n hn
    simp only [Finset.mem_insert, Finset.mem_singleton] at hn
    rcases hn with rfl | rfl
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        A.intersection_incident_left hlm⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        A.intersection_incident_right hlm⟩
  have hcard := Finset.card_le_card hsub
  simpa [hlm] using hcard

end FiniteProjectiveLineArrangement

/-- A lossless affine-to-projective realization of the already finite type
`DeterminedLine cfg`.  This is not a replacement assumption for a topological
argument: its two fields are exactly the algebraic facts still needed to turn
the pair-spanned affine lines into the arrangement above. -/
structure DeterminedLineProjectiveRealization
    {alpha : Type*} [Fintype alpha] [DecidableEq alpha]
    (cfg : Configuration alpha) where
  projectiveLine : DeterminedLine cfg → RealProjectiveLine
  projectiveLine_injective : Function.Injective projectiveLine
  label_incident_iff :
    ∀ (a : alpha) (L : DeterminedLine cfg),
      affinePointToProjective (cfg a) ∈ projectiveLine L ↔ cfg a ∈ L.1

namespace DeterminedLineProjectiveRealization

variable {alpha : Type*} [Fintype alpha] [DecidableEq alpha]
  {cfg : Configuration alpha}

/-- Forgetting the affine labels yields the finite projective arrangement of
the configuration's unique determined lines. -/
noncomputable def toArrangement (R : DeterminedLineProjectiveRealization cfg) :
    FiniteProjectiveLineArrangement (DeterminedLine cfg) := by
  classical
  exact {
    projectiveLine := R.projectiveLine
    projectiveLine_injective := R.projectiveLine_injective }

/-- Labels selected by a projective line of the realization. -/
noncomputable def labelIncidence
    (R : DeterminedLineProjectiveRealization cfg) (L : DeterminedLine cfg) :
    Finset alpha := by
  classical
  exact Finset.univ.filter fun a =>
    affinePointToProjective (cfg a) ∈ R.projectiveLine L

/-- The affine support census is exactly the incidence census of the
projective realization restricted to embedded configuration points. -/
theorem lineSupport_eq_labelIncidence
    (R : DeterminedLineProjectiveRealization cfg) (L : DeterminedLine cfg) :
    lineSupport cfg L = R.labelIncidence L := by
  classical
  ext a
  rw [mem_lineSupport]
  simp only [labelIncidence, Finset.mem_filter, Finset.mem_univ, true_and]
  exact (R.label_incident_iff a L).symm

end DeterminedLineProjectiveRealization

end Erdos506.Incidence
