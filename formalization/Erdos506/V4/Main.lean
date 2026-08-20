import Erdos506.Targets
import Erdos506.V4.CircleBridge

/-!
# Public V4 lower bound and equality classification

This module assembles the richest-line count and the circumcircle bridge for
the frozen no-four-concyclic variant, constructs an extremal near-pencil for
every `n ≥ 4`, and exports the bundled relational theorem.
-/

namespace Erdos506.V4

/-- Every V4-admissible configuration on at least four labels determines at
least the frozen target number of proper circles. -/
theorem circleCount_ge_target {α : Type*} [Fintype α]
    (cfg : Configuration α) (hcard : 4 ≤ Fintype.card α)
    (hadm : Admissible cfg) :
    Erdos506.v4Target (Fintype.card α) ≤ circleCount cfg := by
  change Nat.choose (Fintype.card α - 1) 2 ≤ circleCount cfg
  rw [circleCount_eq_tau cfg hadm.2]
  exact tau_ge_target cfg (by omega) hadm.1

/-- Among V4-admissible configurations, equality in the circle bound is
equivalent to the near-pencil incidence type. -/
theorem circleCount_eq_target_iff_nearPencil {α : Type*} [Fintype α]
    (cfg : Configuration α) (hcard : 4 ≤ Fintype.card α)
    (hadm : Admissible cfg) :
    circleCount cfg = Erdos506.v4Target (Fintype.card α) ↔ NearPencil cfg := by
  constructor
  · intro heq
    apply tau_eq_target_implies_nearPencil cfg hcard hadm.1
    change circleCount cfg = Nat.choose (Fintype.card α - 1) 2 at heq
    rw [circleCount_eq_tau cfg hadm.2] at heq
    exact heq
  · intro hnear
    change circleCount cfg = Nat.choose (Fintype.card α - 1) 2
    rw [circleCount_eq_tau cfg hadm.2]
    exact tau_eq_target_of_nearPencil cfg hcard hnear

/-- Bundled lower-bound and equality-classification statement. -/
theorem lowerBound_and_equality {α : Type*} [Fintype α]
    (cfg : Configuration α) (hcard : 4 ≤ Fintype.card α)
    (hadm : Admissible cfg) :
    Erdos506.v4Target (Fintype.card α) ≤ circleCount cfg ∧
      (circleCount cfg = Erdos506.v4Target (Fintype.card α) ↔ NearPencil cfg) :=
  ⟨circleCount_ge_target cfg hcard hadm,
    circleCount_eq_target_iff_nearPencil cfg hcard hadm⟩

/-- A canonical label type with `n - 1` axis labels and one outsider. -/
abbrev NearPencilLabels (n : ℕ) := Fin (n - 1) ⊕ Unit

/-- Coordinates for the explicit extremal near-pencil. -/
noncomputable def nearPencilPoint (n : ℕ) : NearPencilLabels n → Point2
  | Sum.inl i => EuclideanSpace.single (0 : Fin 2) (i.1 : ℝ)
  | Sum.inr _ => EuclideanSpace.single (1 : Fin 2) 1

theorem nearPencilPoint_injective (n : ℕ) :
    Function.Injective (nearPencilPoint n) := by
  intro x y h
  rcases x with i | u <;> rcases y with j | v
  · have hcoord := congrArg (fun p : Point2 => p (0 : Fin 2)) h
    simp [nearPencilPoint] at hcoord
    congr 1
    apply Fin.ext
    exact_mod_cast hcoord
  · have hcoord := congrArg (fun p : Point2 => p (1 : Fin 2)) h
    norm_num [nearPencilPoint] at hcoord
  · have hcoord := congrArg (fun p : Point2 => p (1 : Fin 2)) h
    norm_num [nearPencilPoint] at hcoord
  · cases u
    cases v
    rfl

/-- The explicit labelled near-pencil: `n - 1` points on the first coordinate
axis and one point on the second coordinate axis. -/
noncomputable def nearPencilConfiguration (n : ℕ) :
    Configuration (NearPencilLabels n) :=
  ⟨nearPencilPoint n, nearPencilPoint_injective n⟩

theorem axisLabel_mem_longLine (n : ℕ) (hn : 4 ≤ n) (i : Fin (n - 1)) :
    Sum.inl i ∈ lineTrace (nearPencilConfiguration n)
      (Sum.inl ⟨0, by omega⟩) (Sum.inl ⟨1, by omega⟩) := by
  rw [mem_lineTrace]
  apply mem_affineSpan_pair_iff_exists_lineMap_eq.mpr
  refine ⟨(i.1 : ℝ), ?_⟩
  ext j
  simp [nearPencilConfiguration, nearPencilPoint, AffineMap.lineMap_apply]

theorem outsider_not_mem_longLine (n : ℕ) (hn : 4 ≤ n) :
    Sum.inr () ∉ lineTrace (nearPencilConfiguration n)
      (Sum.inl ⟨0, by omega⟩) (Sum.inl ⟨1, by omega⟩) := by
  rw [mem_lineTrace]
  intro h
  obtain ⟨r, hr⟩ := mem_affineSpan_pair_iff_exists_lineMap_eq.mp h
  have hcoord := congrArg (fun p : Point2 => p (1 : Fin 2)) hr
  norm_num [nearPencilConfiguration, nearPencilPoint,
    AffineMap.lineMap_apply] at hcoord

theorem nearPencil_outsiders_eq_singleton (n : ℕ) (hn : 4 ≤ n) :
    outsiders (nearPencilConfiguration n)
      (Sum.inl ⟨0, by omega⟩) (Sum.inl ⟨1, by omega⟩) = {Sum.inr ()} := by
  classical
  ext x
  constructor
  · intro hx
    have hxnot := mem_outsiders.mp hx
    rcases x with i | u
    · exact False.elim (hxnot (axisLabel_mem_longLine n hn i))
    · cases u
      simp
  · intro hx
    have hxo : x = Sum.inr () := by simpa using hx
    subst x
    exact mem_outsiders.mpr (outsider_not_mem_longLine n hn)

theorem card_nearPencilLabels (n : ℕ) (hn : 4 ≤ n) :
    Fintype.card (NearPencilLabels n) = n := by
  simp [NearPencilLabels]
  omega

theorem nearPencilConfiguration_isNearPencil (n : ℕ) (hn : 4 ≤ n) :
    NearPencil (nearPencilConfiguration n) := by
  let a : NearPencilLabels n := Sum.inl ⟨0, by omega⟩
  let b : NearPencilLabels n := Sum.inl ⟨1, by omega⟩
  refine ⟨a, b, ?_, ?_⟩
  · simp [a, b]
  · have hsum := card_lineTrace_add_card_outsiders
      (nearPencilConfiguration n) a b
    have hout : (outsiders (nearPencilConfiguration n) a b).card = 1 := by
      rw [show outsiders (nearPencilConfiguration n) a b = {Sum.inr ()} by
        simpa [a, b] using nearPencil_outsiders_eq_singleton n hn]
      simp
    rw [card_nearPencilLabels n hn] at hsum ⊢
    omega

theorem nearPencilConfiguration_admissible (n : ℕ) (hn : 4 ≤ n) :
    Admissible (nearPencilConfiguration n) := by
  apply admissible_of_nearPencil (nearPencilConfiguration n)
  · simpa [card_nearPencilLabels n hn] using hn
  · exact nearPencilConfiguration_isNearPencil n hn

theorem nearPencilConfiguration_circleCount (n : ℕ) (hn : 4 ≤ n) :
    circleCount (nearPencilConfiguration n) = Erdos506.v4Target n := by
  have hcard : 4 ≤ Fintype.card (NearPencilLabels n) := by
    simpa [card_nearPencilLabels n hn] using hn
  have heq := (circleCount_eq_target_iff_nearPencil
    (nearPencilConfiguration n) hcard
    (nearPencilConfiguration_admissible n hn)).2
      (nearPencilConfiguration_isNearPencil n hn)
  simpa [card_nearPencilLabels n hn] using heq

/-- For every `n ≥ 4`, the explicit near-pencil is admissible and attains the
V4 target. -/
theorem exists_extremal_configuration (n : ℕ) (hn : 4 ≤ n) :
    ∃ cfg : Configuration (NearPencilLabels n),
      Fintype.card (NearPencilLabels n) = n ∧ Admissible cfg ∧
        circleCount cfg = Erdos506.v4Target n := by
  exact ⟨nearPencilConfiguration n, card_nearPencilLabels n hn,
    nearPencilConfiguration_admissible n hn,
    nearPencilConfiguration_circleCount n hn⟩

/-- The complete frozen V4 contract: universal lower bound, classification of
all equality cases, and existence of an extremal configuration for every
`n ≥ 4`. -/
theorem main (n : ℕ) (hn : 4 ≤ n) :
    (∀ (α : Type*) [Fintype α] (cfg : Configuration α),
      Fintype.card α = n → Admissible cfg →
        Erdos506.v4Target n ≤ circleCount cfg) ∧
    (∀ (α : Type*) [Fintype α] (cfg : Configuration α),
      Fintype.card α = n → Admissible cfg →
        (circleCount cfg = Erdos506.v4Target n ↔ NearPencil cfg)) ∧
    (∃ cfg : Configuration (NearPencilLabels n),
      Fintype.card (NearPencilLabels n) = n ∧ Admissible cfg ∧
        circleCount cfg = Erdos506.v4Target n) := by
  refine ⟨?_, ?_, exists_extremal_configuration n hn⟩
  · intro α _ cfg hsize hadm
    have hcard : 4 ≤ Fintype.card α := by omega
    simpa [hsize] using circleCount_ge_target cfg hcard hadm
  · intro α _ cfg hsize hadm
    have hcard : 4 ≤ Fintype.card α := by omega
    simpa [hsize] using circleCount_eq_target_iff_nearPencil cfg hcard hadm

end Erdos506.V4
