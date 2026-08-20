import Erdos506.Incidence.LangerPrinciple
import Erdos506.V1.PivotGeometry

/-!
# The V1 Langer incidence transfer

This module is kept separate from the inversion dictionary so that the
external Langer contract does not enlarge the core Melchior dependency
closure.
-/

namespace Erdos506.V1

open Erdos506.Block.BlockSystem
open Erdos506.Incidence
open Erdos506.V3
open Erdos506.V4
open scoped BigOperators

/-- The incidence of all image lines is the sum of `s-1` over nontrivial
V1 blocks through the pivot. -/
theorem pivotBlockIncidence_eq_lineIncidence
    {α : Type*} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (p : α) :
    (∑ b : PivotBlock cfg p,
        (((geometricBlockSupport cfg b.1).card : ℤ) - 1)) =
      lineIncidence (pivotInversion cfg p) := by
  unfold lineIncidence
  apply Fintype.sum_equiv (blockPivotLineEquiv cfg p)
  intro b
  change (((geometricBlockSupport cfg b.1).card : ℤ) - 1) =
    ((lineSupport (pivotInversion cfg p)
      (blockToPivotLine cfg p b)).card : ℤ)
  have hcard := card_lineSupport_blockToPivotLine cfg p b
  omega

end Erdos506.V1
