import Erdos506.V1.TwelveSixLower

/-!
# Selected-six endpoint at twelve points

The heavy branch eliminations are cached in `TwelveSixUpper` and
`TwelveSixLower`; this module contains only the public scalar dispatch.
-/

namespace Erdos506.V1

open Erdos506.Block
open Erdos506.Block.BlockSystem
open Erdos506.Incidence
open Erdos506.V4
open scoped BigOperators

universe u

/-- Full selected-six-circle endpoint at twelve points. -/
theorem twelveSix_circleCount_ge_fifty_one
    {alpha : Type u} [Fintype alpha] [DecidableEq alpha]
    (Mel : RealPlaneMelchiorPrinciple.{u})
    (EvenArr : RealPlaneEvenArrangementPrinciple.{u})
    (Kelly : RealPlaneKellyMoserPrinciple.{u})
    (Gram : RealPlaneTwelveGramPrinciple.{u})
    (Gallery : RealPlaneTwelveGalleryPrinciple.{u})
    (Direction : RealPlaneTwelveDirectionPrinciple.{u})
    (cfg : Configuration alpha) (hadm : Admissible cfg)
    (hcard : Fintype.card alpha = 12)
    (gamma : DeterminedCircle cfg)
    (hgamma : (circleTrace cfg gamma.1).card = 6)
    (hcircle : forall c : DeterminedCircle cfg,
      (circleTrace cfg c.1).card <= 6) :
    51 <= Erdos506.V4.circleCount cfg := by
  classical
  by_contra htarget
  have hcount : Erdos506.V4.circleCount cfg <= 50 := by omega
  let S := blockSystem cfg
  have ctx : TwelveSixBranchContext S := by
    simpa [S] using twelveSixBranchContext_of_configuration
      Mel EvenArr Kelly Gram Gallery Direction cfg hadm hcard hcount
        gamma hgamma hcircle
  rcases twelveSixSpine_scalar_router S ctx.spine with
      h1 | h2 | h3 | h4
  · exact twelveSix_one_block_impossible S ctx h1.1
  · exact twelveSix_two_blocks_impossible S ctx h2.1
  · exact twelveSix_three_blocks_impossible S ctx h3.1
  · exact twelveSix_four_blocks_impossible S ctx h4.1

end Erdos506.V1

