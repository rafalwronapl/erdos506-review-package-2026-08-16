import Erdos506.V1.LangerRow

/-!
# Grouping the V1 Langer incidence by support size

The geometric transfer is cached in `V1.LangerRow`.  This module contains
only the finite reindexing that identifies its block sum with the local
summand of the universal row `L`.
-/

namespace Erdos506.V1

open Erdos506.Block.BlockSystem
open Erdos506.Incidence
open Erdos506.V3
open Erdos506.V4
open scoped BigOperators

/-- The generic nontrivial-block subtype specialized to the geometric V1
system is the concrete pivot-block subtype used by the inversion dictionary. -/
def nontrivialBlockAtEquivPivotBlock
    {α : Type*} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (p : α) :
    NontrivialBlockAt (geometricBlockSystem cfg) p ≃ PivotBlock cfg p where
  toFun b := ⟨b.1, b.2⟩
  invFun b := ⟨b.1, by
    change p ∈ geometricBlockSupport cfg b.1 ∧
      3 ≤ (geometricBlockSupport cfg b.1).card
    exact b.2⟩
  left_inv b := Subtype.ext rfl
  right_inv b := Subtype.ext rfl

/-- The local support-size row is exactly the line incidence of the inverted
configuration. -/
theorem pivotLangerSum_eq_lineIncidence
    {α : Type*} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (p : α) :
    (∑ s ∈ (geometricBlockSystem cfg).nontrivialSizes,
        ((s : ℤ) - 1) *
          ((geometricBlockSystem cfg).blockDegree s p : ℤ)) =
      lineIncidence (pivotInversion cfg p) := by
  calc
    (∑ s ∈ (geometricBlockSystem cfg).nontrivialSizes,
        ((s : ℤ) - 1) *
          ((geometricBlockSystem cfg).blockDegree s p : ℤ)) =
        ∑ b : NontrivialBlockAt (geometricBlockSystem cfg) p,
          ((((geometricBlockSystem cfg).support b.1).card : ℤ) - 1) :=
      (geometricBlockSystem cfg).sum_nontrivialBlockAt_weight p
        (fun s => (s : ℤ) - 1)
    _ = ∑ b : PivotBlock cfg p,
        (((geometricBlockSupport cfg b.1).card : ℤ) - 1) := by
      apply Fintype.sum_equiv (nontrivialBlockAtEquivPivotBlock cfg p)
      intro b
      rfl
    _ = lineIncidence (pivotInversion cfg p) :=
      pivotBlockIncidence_eq_lineIncidence cfg p

end Erdos506.V1
