import Mathlib.Data.Finset.Powerset
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Geometry.Euclidean.Circumcenter
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional

/-!
# Finite labelled configurations for the V4 formalization

This module fixes the concrete real plane and the finite incidence objects
used by the no-four-concyclic variant.  It contains definitions and elementary
membership/cardinality lemmas only; no extremal bound is asserted here.
-/

namespace Erdos506.V4

/-- The concrete real Euclidean plane used by the frozen theorem. -/
abbrev Point2 := EuclideanSpace ℝ (Fin 2)

/-- A finite labelled configuration.  Injectivity makes distinctness of the
selected points structural. -/
abbrev Configuration (α : Type*) := α ↪ Point2

/-- The selected point set underlying a labelled configuration. -/
def pointSet {α : Type*} (cfg : Configuration α) : Set Point2 :=
  Set.range cfg

/-- Images of the labels in a finite support. -/
def supportPoints {α : Type*} (cfg : Configuration α) (t : Finset α) : Set Point2 :=
  cfg '' (t : Set α)

/-- All unordered three-label supports. -/
noncomputable def tripleSupports (α : Type*) [Fintype α] : Finset (Finset α) := by
  classical
  exact Finset.univ.powersetCard 3

/-- A support is noncollinear when its selected point images are not
collinear in the real affine plane. -/
def IsNoncollinear {α : Type*} (cfg : Configuration α) (t : Finset α) : Prop :=
  ¬Collinear ℝ (supportPoints cfg t)

/-- The unordered noncollinear triples of a configuration. -/
noncomputable def noncollinearTriples {α : Type*} [Fintype α]
    (cfg : Configuration α) : Finset (Finset α) := by
  classical
  exact (tripleSupports α).filter (IsNoncollinear cfg)

/-- Number of unordered noncollinear triples. -/
noncomputable def tau {α : Type*} [Fintype α] (cfg : Configuration α) : ℕ :=
  (noncollinearTriples cfg).card

/-- Labels whose images lie on the affine line through two selected labels. -/
noncomputable def lineTrace {α : Type*} [Fintype α] (cfg : Configuration α)
    (a b : α) : Finset α := by
  classical
  exact Finset.univ.filter fun x =>
    cfg x ∈ affineSpan ℝ ({cfg a, cfg b} : Set Point2)

/-- The selected configuration is not contained in one affine line. -/
def Noncollinear {α : Type*} (cfg : Configuration α) : Prop :=
  ¬Collinear ℝ (pointSet cfg)

/-- A near-pencil has a selected pair-line containing all but one label. -/
def NearPencil {α : Type*} [Fintype α] (cfg : Configuration α) : Prop :=
  ∃ a b, a ≠ b ∧ (lineTrace cfg a b).card = Fintype.card α - 1

/-- A proper Euclidean circle is a sphere of positive radius in `Point2`. -/
abbrev ProperCircle :=
  {s : EuclideanGeometry.Sphere Point2 // 0 < s.radius}

/-- Labels lying on a proper circle. -/
noncomputable def circleTrace {α : Type*} [Fintype α] (cfg : Configuration α)
    (c : ProperCircle) : Finset α := by
  classical
  exact Finset.univ.filter fun x => cfg x ∈ (c.1 : Set Point2)

/-- No proper Euclidean circle contains four selected labels. -/
def NoFourConcyclic {α : Type*} [Fintype α] (cfg : Configuration α) : Prop :=
  ∀ c : ProperCircle, (circleTrace cfg c).card ≤ 3

/-- The frozen V4 admissibility predicate. -/
def Admissible {α : Type*} [Fintype α] (cfg : Configuration α) : Prop :=
  Noncollinear cfg ∧ NoFourConcyclic cfg

@[simp] theorem mem_tripleSupports {α : Type*} [Fintype α] {t : Finset α} :
    t ∈ tripleSupports α ↔ t.card = 3 := by
  classical
  simp [tripleSupports]

theorem card_tripleSupports (α : Type*) [Fintype α] :
    (tripleSupports α).card = Nat.choose (Fintype.card α) 3 := by
  classical
  simp [tripleSupports]

@[simp] theorem mem_noncollinearTriples {α : Type*} [Fintype α]
    {cfg : Configuration α} {t : Finset α} :
    t ∈ noncollinearTriples cfg ↔ t.card = 3 ∧ IsNoncollinear cfg t := by
  classical
  simp [noncollinearTriples]

theorem tau_le_choose (α : Type*) [Fintype α] (cfg : Configuration α) :
    tau cfg ≤ Nat.choose (Fintype.card α) 3 := by
  classical
  rw [← card_tripleSupports α]
  exact Finset.card_filter_le _ _

@[simp] theorem mem_lineTrace {α : Type*} [Fintype α]
    {cfg : Configuration α} {a b x : α} :
    x ∈ lineTrace cfg a b ↔
      cfg x ∈ affineSpan ℝ ({cfg a, cfg b} : Set Point2) := by
  classical
  simp [lineTrace]

@[simp] theorem left_mem_lineTrace {α : Type*} [Fintype α]
    (cfg : Configuration α) (a b : α) : a ∈ lineTrace cfg a b := by
  rw [mem_lineTrace]
  apply subset_affineSpan ℝ ({cfg a, cfg b} : Set Point2)
  simp

@[simp] theorem right_mem_lineTrace {α : Type*} [Fintype α]
    (cfg : Configuration α) (a b : α) : b ∈ lineTrace cfg a b := by
  rw [mem_lineTrace]
  apply subset_affineSpan ℝ ({cfg a, cfg b} : Set Point2)
  simp

theorem two_le_card_lineTrace {α : Type*} [Fintype α]
    (cfg : Configuration α) {a b : α} (hab : a ≠ b) :
    2 ≤ (lineTrace cfg a b).card := by
  classical
  have hsub : ({a, b} : Finset α) ⊆ lineTrace cfg a b := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · rw [mem_lineTrace]
      apply subset_affineSpan ℝ _
      simp
    · rw [mem_lineTrace]
      apply subset_affineSpan ℝ _
      simp
  have hcard : ({a, b} : Finset α).card = 2 := by simp [hab]
  rw [← hcard]
  exact Finset.card_le_card hsub

@[simp] theorem mem_circleTrace {α : Type*} [Fintype α]
    {cfg : Configuration α} {c : ProperCircle} {x : α} :
    x ∈ circleTrace cfg c ↔ cfg x ∈ (c.1 : Set Point2) := by
  classical
  simp [circleTrace]

end Erdos506.V4
