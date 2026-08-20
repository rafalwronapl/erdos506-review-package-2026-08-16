import Erdos506.Finite.IncidenceMoments
import Mathlib.Data.Finset.Powerset
import Mathlib.Tactic

/-!
# The finite link skeleton of the four-star case

This file isolates the label-free finite part of the local four-star
argument.  The real-projective determinant calculation which excludes the
`T`-star and four-cycle cases belongs in a separate geometric layer.
-/

namespace Erdos506.Finite

open scoped BigOperators

/-- Four four-point base lines with the linear intersection cap. -/
def IsFourStarBaseFamily {Point : Type*} [DecidableEq Point]
    (B : Finset (Finset Point)) : Prop :=
  B.card = 4 ∧
  (∀ A ∈ B, A.card = 4) ∧
  (∀ A ∈ B, ∀ C ∈ B, A ≠ C → (A ∩ C).card ≤ 1)

/-- The finite target supplied by the complete-quadrangle count: every two
base lines meet once.  It is deliberately separated from the real geometry
which later labels the four private points. -/
def IsFourStarCompleteQuadrangle {Point : Type*} [DecidableEq Point]
    (B : Finset (Finset Point)) : Prop :=
  IsFourStarBaseFamily B ∧
  ∀ A ∈ B, ∀ C ∈ B, A ≠ C → (A ∩ C).card = 1

/-- The four private-point labels in the complete-quadrangle skeleton. -/
abbrev FourStarVertex := Fin 4

/-- All possible private pairs. -/
def fourStarEdges : Finset (Finset FourStarVertex) :=
  (Finset.univ : Finset FourStarVertex).powersetCard 2

@[simp] theorem fourStarEdges_card : fourStarEdges.card = 6 := by
  norm_num [fourStarEdges, Nat.choose]

/-- A four-edge simple graph on the four private labels.  This is the graph
formed by the additional `S`-lines after the absence of a `T`-line has been
established. -/
def IsFourStarPrivatePairFamily
    (E : Finset (Finset FourStarVertex)) : Prop :=
  E.card = 4 ∧ E ⊆ fourStarEdges

/-- The complement of the private-pair graph is a matching.  Equivalently,
the four selected private pairs form a four-cycle. -/
def IsFourStarFourCycle
    (E : Finset (Finset FourStarVertex)) : Prop :=
  (fourStarEdges \ E).card = 2 ∧
  ∀ e ∈ fourStarEdges \ E, ∀ f ∈ fourStarEdges \ E,
    e ≠ f → Disjoint e f

/-- The complement of the private-pair graph consists of two incident
edges.  Equivalently, the selected graph is a triangle with a pendant edge. -/
def IsFourStarTrianglePendant
    (E : Finset (Finset FourStarVertex)) : Prop :=
  ∃ e f : Finset FourStarVertex,
    fourStarEdges \ E = {e, f} ∧ ¬ Disjoint e f

/-- Every four-edge simple graph on four vertices is either a four-cycle or
a triangle with a pendant edge.  The proof is the exact two-edge complement
classification; no support catalogue is involved. -/
theorem fourStar_privatePair_cycle_or_trianglePendant
    (E : Finset (Finset FourStarVertex))
    (hE : IsFourStarPrivatePairFamily E) :
    IsFourStarFourCycle E ∨ IsFourStarTrianglePendant E := by
  classical
  have hcomp : (fourStarEdges \ E).card = 2 := by
    have hsum := Finset.card_sdiff_add_card fourStarEdges E
    have hunion : fourStarEdges ∪ E = fourStarEdges :=
      Finset.union_eq_left.2 hE.2
    rw [hunion, fourStarEdges_card, hE.1] at hsum
    omega
  obtain ⟨e, f, hef, hcompEq⟩ := Finset.card_eq_two.mp hcomp
  by_cases hdisj : Disjoint e f
  · left
    refine ⟨hcomp, ?_⟩
    intro e' he' f' hf' he'ne
    rw [hcompEq] at he' hf'
    simp only [Finset.mem_insert, Finset.mem_singleton] at he' hf'
    rcases he' with rfl | rfl <;> rcases hf' with rfl | rfl
    · exact (he'ne rfl).elim
    · exact hdisj
    · exact hdisj.symm
    · exact (he'ne rfl).elim
  · right
    exact ⟨e, f, hcompEq, hdisj⟩

/-- The three structural alternatives before the real determinant step.
`tStar` records the exceptional additional three-line; in its absence the
private-pair graph is classified by
`fourStar_privatePair_cycle_or_trianglePendant`. -/
inductive FourStarAdditionalLinePattern
  | tStar
  | fourCycle
  | trianglePendant
  deriving DecidableEq

end Erdos506.Finite
