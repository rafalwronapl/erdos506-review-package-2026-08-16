import Erdos506.Finite.UniformOwner
import Erdos506.V4.CircleBridge

/-!
# V3 configurations and circle ownership

V3 requires no three selected points to be collinear and excludes a single
proper circle containing the whole configuration.  Circle counting reuses the
semantic circumcircle model established for V4.
-/

namespace Erdos506.V3

open Erdos506.Finite
open Erdos506.V4

/-- Every three-label support is noncollinear. -/
def NoThreeCollinear {α : Type*} [Fintype α] (cfg : Configuration α) : Prop :=
  ∀ t : Finset α, t.card = 3 → IsNoncollinear cfg t

/-- No proper circle contains every selected label. -/
def NotConcyclic {α : Type*} [Fintype α] (cfg : Configuration α) : Prop :=
  ∀ c : ProperCircle, (circleTrace cfg c).card < Fintype.card α

/-- The frozen V3 admissibility predicate. -/
def Admissible {α : Type*} [Fintype α] (cfg : Configuration α) : Prop :=
  NoThreeCollinear cfg ∧ NotConcyclic cfg

/-- A determined circle, attached to the finite image of noncollinear
triples. -/
abbrev DeterminedCircle {α : Type*} [Fintype α] (cfg : Configuration α) :=
  {c : ProperCircle // c ∈ determinedCircles cfg}

noncomputable def attachedTripleOfKSubset {α : Type*} [Fintype α]
    [DecidableEq α]
    (cfg : Configuration α) (hthree : NoThreeCollinear cfg)
    (A : KSubset α 3) : NoncollinearTriple cfg :=
  ⟨A.1, mem_noncollinearTriples.mpr ⟨A.2, hthree A.1 A.2⟩⟩

noncomputable def circleOwner {α : Type*} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (hthree : NoThreeCollinear cfg)
    (A : KSubset α 3) : DeterminedCircle cfg := by
  classical
  let t := attachedTripleOfKSubset cfg hthree A
  refine ⟨properCircumcircle cfg t, ?_⟩
  rw [determinedCircles]
  exact Finset.mem_image.mpr ⟨t, by simp, rfl⟩

theorem circleOwner_contains {α : Type*} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (hthree : NoThreeCollinear cfg)
    (A : KSubset α 3) :
    A.1 ⊆ circleTrace cfg (circleOwner cfg hthree A).1 := by
  intro x hx
  apply mem_circleTrace.mpr
  exact support_mem_properCircumcircle cfg
    (attachedTripleOfKSubset cfg hthree A) hx

theorem circleOwner_unique {α : Type*} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (hthree : NoThreeCollinear cfg)
    (A : KSubset α 3) (c : DeterminedCircle cfg)
    (hA : A.1 ⊆ circleTrace cfg c.1) :
    c = circleOwner cfg hthree A := by
  apply Subtype.ext
  have hc := properCircle_eq_properCircumcircle_of_support cfg
    (attachedTripleOfKSubset cfg hthree A) c.1 (by
      intro x hx
      exact mem_circleTrace.mp (hA hx))
  simpa [circleOwner] using hc

/-- The explicit unique-owner structure on determined V3 circles. -/
noncomputable def circleOwnership {α : Type*} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (hthree : NoThreeCollinear cfg) :
    UniformOwner α (DeterminedCircle cfg) 3 where
  support c := circleTrace cfg c.1
  owner := circleOwner cfg hthree
  owner_contains := circleOwner_contains cfg hthree
  owner_unique := circleOwner_unique cfg hthree

theorem circleSupport_card_ge_three {α : Type*} [Fintype α]
    (cfg : Configuration α) (c : DeterminedCircle cfg) :
    3 ≤ (circleTrace cfg c.1).card := by
  classical
  obtain ⟨t, ht⟩ := (mem_determinedCircles_iff cfg c.1).mp c.2
  have hsub : t.1 ⊆ circleTrace cfg c.1 := by
    intro x hx
    exact mem_circleTrace.mpr (ht x hx)
  have htcard : t.1.card = 3 := (mem_noncollinearTriples.mp t.2).1
  rw [← htcard]
  exact Finset.card_le_card hsub

theorem circleSupport_card_lt {α : Type*} [Fintype α]
    (cfg : Configuration α) (hnot : NotConcyclic cfg)
    (c : DeterminedCircle cfg) :
    (circleTrace cfg c.1).card < Fintype.card α :=
  hnot c.1

theorem circleCount_eq_card_determinedCircle {α : Type*} [Fintype α]
    (cfg : Configuration α) :
    circleCount cfg = Fintype.card (DeterminedCircle cfg) := by
  classical
  simp [circleCount, DeterminedCircle]

/-- Every selected triple belongs to exactly one determined circle. -/
theorem triple_partition {α : Type*} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (hthree : NoThreeCollinear cfg) :
    (∑ c : DeterminedCircle cfg, Nat.choose (circleTrace cfg c.1).card 3) =
      Nat.choose (Fintype.card α) 3 :=
  (circleOwnership cfg hthree).sum_choose_support_card

end Erdos506.V3
