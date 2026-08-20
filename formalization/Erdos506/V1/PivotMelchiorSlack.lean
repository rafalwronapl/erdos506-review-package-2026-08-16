import Erdos506.Incidence.EvenArrangementPrinciple
import Erdos506.V1.PivotGeometry

/-!
# The V1 pivot expression as Melchior slack

This small module exposes only the equality needed to apply the
even-arrangement principle after V1 pivot inversion.  Keeping it below the
finite endpoint files avoids importing the nine-point development merely for
this universal dictionary identity.
-/

namespace Erdos506.V1

open Erdos506.Block.BlockSystem
open Erdos506.Incidence
open Erdos506.V3
open Erdos506.V4
open scoped BigOperators

/-- The signed V1 pivot expression is exactly the Melchior slack of the
inverted point configuration. -/
theorem pivotSigma_eq_lineMelchiorSlack_fieldFree
    {α : Type*} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (p : α) :
    (geometricBlockSystem cfg).pivotSigma p =
      lineMelchiorSlack (Erdos506.V3.pivotInversion cfg p) := by
  classical
  have hsum :
      (∑ b : PivotBlock cfg p,
          (4 - ((geometricBlockSupport cfg b.1).card : ℤ))) =
        ∑ L : DeterminedLine (Erdos506.V3.pivotInversion cfg p),
          (3 - ((lineSupport (Erdos506.V3.pivotInversion cfg p) L).card : ℤ)) := by
    apply Fintype.sum_equiv (blockPivotLineEquiv cfg p)
    intro b
    exact (pivotWeight_blockToPivotLine cfg p b).symm
  rw [(geometricBlockSystem cfg).pivotSigma_eq_sum_nontrivialBlockAt_sub_three]
  unfold lineMelchiorSlack
  exact congrArg (fun z : ℤ => z - 3) hsum

end Erdos506.V1
