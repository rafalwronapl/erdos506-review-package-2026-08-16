import Erdos506.Finite.UniformOwner

/-!
# Abstract tagged block systems

This is the common finite interface for maximal line and circle traces.  A
geometric adapter must later construct the owners and prove uniqueness.
-/

namespace Erdos506.Block

open Erdos506.Finite

inductive BlockKind
  | line
  | circle
  deriving DecidableEq

structure BlockSystem (Point Block : Type*) [Fintype Point] [Fintype Block]
    [DecidableEq Point] where
  kind : Block → BlockKind
  support : Block → Finset Point
  line_min : ∀ b, kind b = .line → 2 ≤ (support b).card
  circle_min : ∀ b, kind b = .circle → 3 ≤ (support b).card
  tripleOwner : KSubset Point 3 → Block
  triple_contains : ∀ A, A.1 ⊆ support (tripleOwner A)
  triple_unique : ∀ A b, A.1 ⊆ support b → b = tripleOwner A
  lineOwner : KSubset Point 2 → {b : Block // kind b = .line}
  line_contains : ∀ A, A.1 ⊆ support (lineOwner A).1
  line_owner_unique : ∀ A (b : {b : Block // kind b = .line}),
    A.1 ⊆ support b.1 → b = lineOwner A

namespace BlockSystem

variable {Point Block : Type*} [Fintype Point] [Fintype Block]
  [DecidableEq Point]

abbrev LineBlock (S : BlockSystem Point Block) :=
  {b : Block // S.kind b = .line}

def tripleOwnership (S : BlockSystem Point Block) :
    UniformOwner Point Block 3 where
  support := S.support
  owner := S.tripleOwner
  owner_contains := S.triple_contains
  owner_unique := S.triple_unique

def lineOwnership (S : BlockSystem Point Block) :
    UniformOwner Point (LineBlock S) 2 where
  support b := S.support b.1
  owner := S.lineOwner
  owner_contains := S.line_contains
  owner_unique := S.line_owner_unique

theorem support_card_le_point_card (S : BlockSystem Point Block) (b : Block) :
    (S.support b).card ≤ Fintype.card Point := by
  classical
  simpa using Finset.card_le_card (Finset.subset_univ (S.support b))

/-- Triple ownership gives the global triple partition directly. -/
theorem triple_partition (S : BlockSystem Point Block) :
    (∑ b : Block, Nat.choose (S.support b).card 3) =
      Nat.choose (Fintype.card Point) 3 :=
  (S.tripleOwnership.sum_choose_support_card)

/-- Pair ownership by line blocks gives the global line-pair partition. -/
theorem line_pair_partition (S : BlockSystem Point Block) :
    (∑ b : LineBlock S, Nat.choose (S.support b.1).card 2) =
      Nat.choose (Fintype.card Point) 2 :=
  (S.lineOwnership.sum_choose_support_card)

theorem distinct_block_inter_card_lt_three (S : BlockSystem Point Block)
    {b c : Block} (hbc : b ≠ c) :
    (S.support b ∩ S.support c).card < 3 :=
  S.tripleOwnership.card_inter_lt_of_ne hbc

theorem distinct_line_inter_card_lt_two (S : BlockSystem Point Block)
    {b c : LineBlock S} (hbc : b ≠ c) :
    (S.support b.1 ∩ S.support c.1).card < 2 :=
  S.lineOwnership.card_inter_lt_of_ne hbc

end BlockSystem
end Erdos506.Block
