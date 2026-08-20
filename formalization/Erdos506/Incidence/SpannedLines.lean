import Erdos506.Finite.KSubset
import Erdos506.Incidence.MelchiorCombinatorics
import Erdos506.V4.Model

/-!
# Finite spanned-line census

This module gives a canonical finite type of the affine lines spanned by a
finite labelled configuration.  It also states Melchior's inequality directly
on that finite census and connects any projective-cellulation certificate to
the statement.
-/

namespace Erdos506.Incidence

open Erdos506.Finite
open Erdos506.V4
open AffineSubspace
open scoped BigOperators

/-- The affine line spanned by an unordered pair of labels. -/
noncomputable def lineOfPair {α : Type*} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (A : KSubset α 2) : AffineSubspace ℝ Point2 :=
  affineSpan ℝ (cfg '' (A.1 : Set α))

/-- The finite image of all pair-spanned affine lines. -/
noncomputable def determinedLines {α : Type*} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) : Finset (AffineSubspace ℝ Point2) := by
  classical
  exact Finset.univ.image (lineOfPair cfg)

/-- A line together with evidence that two selected points span it. -/
abbrev DeterminedLine {α : Type*} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) :=
  {L : AffineSubspace ℝ Point2 // L ∈ determinedLines cfg}

/-- Selected labels lying on a determined affine line. -/
noncomputable def lineSupport {α : Type*} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (L : DeterminedLine cfg) : Finset α := by
  classical
  exact Finset.univ.filter fun x => cfg x ∈ L.1

@[simp] theorem mem_lineSupport {α : Type*} [Fintype α] [DecidableEq α]
    {cfg : Configuration α} {L : DeterminedLine cfg} {x : α} :
    x ∈ lineSupport cfg L ↔ cfg x ∈ L.1 := by
  classical
  simp [lineSupport]

theorem lineOfPair_mem_determinedLines {α : Type*} [Fintype α]
    [DecidableEq α] (cfg : Configuration α) (A : KSubset α 2) :
    lineOfPair cfg A ∈ determinedLines cfg := by
  classical
  simp [determinedLines]

/-- Every determined line has a pair that spans it. -/
theorem DeterminedLine.exists_pair {α : Type*} [Fintype α]
    [DecidableEq α] {cfg : Configuration α} (L : DeterminedLine cfg) :
    ∃ A : KSubset α 2, lineOfPair cfg A = L.1 := by
  classical
  have hmem := L.2
  change L.1 ∈ Finset.univ.image (lineOfPair cfg) at hmem
  obtain ⟨A, _hA, hline⟩ := Finset.mem_image.mp hmem
  exact ⟨A, hline⟩

/-- Both labels of a spanning pair lie in the support of its line. -/
theorem pair_subset_lineSupport {α : Type*} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (A : KSubset α 2) :
    A.1 ⊆ lineSupport cfg ⟨lineOfPair cfg A, lineOfPair_mem_determinedLines cfg A⟩ := by
  intro x hx
  rw [mem_lineSupport]
  apply subset_affineSpan ℝ (cfg '' (A.1 : Set α))
  exact ⟨x, hx, rfl⟩

/-- A pair of distinct selected points spans a one-dimensional affine
subspace. -/
theorem lineOfPair_direction_finrank {α : Type*} [Fintype α]
    [DecidableEq α] (cfg : Configuration α) (A : KSubset α 2) :
    Module.finrank ℝ (lineOfPair cfg A).direction = 1 := by
  rcases A with ⟨S, hS⟩
  obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp hS
  have himage :
      cfg '' (({a, b} : Finset α) : Set α) =
        ({cfg a, cfg b} : Set Point2) := by
    ext x
    simp [eq_comm]
  rw [lineOfPair, himage, direction_affineSpan,
    vectorSpan_pair_rev]
  exact finrank_span_singleton
    (sub_ne_zero.mpr (cfg.injective.ne hab).symm)

theorem DeterminedLine.direction_finrank {α : Type*} [Fintype α]
    [DecidableEq α] {cfg : Configuration α} (L : DeterminedLine cfg) :
    Module.finrank ℝ L.1.direction = 1 := by
  obtain ⟨A, hA⟩ := L.exists_pair
  rw [← hA]
  exact lineOfPair_direction_finrank cfg A

@[simp] theorem lineOfPair_pair {α : Type*} [Fintype α]
    [DecidableEq α] (cfg : Configuration α) {a b : α} (hab : a ≠ b) :
    lineOfPair cfg ⟨{a, b}, by simp [hab]⟩ =
      affineSpan ℝ ({cfg a, cfg b} : Set Point2) := by
  unfold lineOfPair
  congr 1
  ext x
  simp [eq_comm]

/-- Two selected points contained in an affine line span that whole line once
the target direction is known to be one-dimensional. -/
theorem lineOfPair_eq_of_mem_of_direction_finrank_one
    {α : Type*} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (A : KSubset α 2)
    (L : AffineSubspace ℝ Point2)
    (hmem : ∀ x ∈ A.1, cfg x ∈ L)
    (hfin : Module.finrank ℝ L.direction = 1) :
    lineOfPair cfg A = L := by
  have hle : lineOfPair cfg A ≤ L := by
    apply affineSpan_le.mpr
    rintro y ⟨x, hx, rfl⟩
    exact hmem x hx
  have hdirle := AffineSubspace.direction_le hle
  have hdirection : (lineOfPair cfg A).direction = L.direction :=
    Submodule.eq_of_le_of_finrank_eq hdirle
      ((lineOfPair_direction_finrank cfg A).trans hfin.symm)
  have hApos : 0 < A.1.card := by omega
  obtain ⟨a, ha⟩ := Finset.card_pos.mp hApos
  have hnonempty : ((lineOfPair cfg A : AffineSubspace ℝ Point2) : Set Point2).Nonempty := by
    refine ⟨cfg a, ?_⟩
    apply subset_affineSpan ℝ (cfg '' (A.1 : Set α))
    exact ⟨a, ha, rfl⟩
  exact AffineSubspace.eq_of_direction_eq_of_nonempty_of_le
    hdirection hnonempty hle

/-- Every determined line contains at least two selected labels. -/
theorem two_le_lineSupport_card {α : Type*} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (L : DeterminedLine cfg) :
    2 ≤ (lineSupport cfg L).card := by
  obtain ⟨A, hA⟩ := L.exists_pair
  let L' : DeterminedLine cfg :=
    ⟨lineOfPair cfg A, lineOfPair_mem_determinedLines cfg A⟩
  have hsub : A.1 ⊆ lineSupport cfg L' := pair_subset_lineSupport cfg A
  have hcard := Finset.card_le_card hsub
  have hL : L' = L := by
    apply Subtype.ext
    exact hA
  simpa [A.2, hL] using hcard

/-- Melchior's inequality for the lines spanned by a finite point set. -/
def LineMelchior {α : Type*} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) : Prop :=
  (3 : ℤ) ≤ ∑ L : DeterminedLine cfg, (3 - ((lineSupport cfg L).card : ℤ))

/-- A projective arrangement cellulation with the expected vertex
multiplicities proves the line-census form of Melchior. -/
theorem lineMelchior_of_cellulation {α Edge Face : Type*}
    [Fintype α] [DecidableEq α] [Fintype Edge] [Fintype Face]
    [DecidableEq Edge] (cfg : Configuration α)
    (C : ProjectiveArrangementCellulation (DeterminedLine cfg) Edge Face)
    (hmultiplicity :
      ∀ L : DeterminedLine cfg, C.multiplicity L = (lineSupport cfg L).card) :
    LineMelchior cfg := by
  unfold LineMelchior
  simpa only [hmultiplicity] using C.melchior

end Erdos506.Incidence
