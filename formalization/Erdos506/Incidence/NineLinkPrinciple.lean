import Erdos506.Finite.TetrahedralLinks
import Erdos506.V1.BlockRows

/-!
# The real nine-point link input

This file records only the local combinatorial conclusion of the real
nine-point link lemma needed by the ten-point maximum-four branch.  Under the
already checked pointwise profile, the supports of all generalized
three-blocks form a three-uniform hypergraph whose link at every selected
point is `C3 ⊔ C3 ⊔ 3K1`.

The principle is an explicit parameter.  It contains neither a circle-count
conclusion nor the final ten-point endpoint.
-/

namespace Erdos506.Incidence

open Erdos506.Block.BlockSystem
open Erdos506.Finite
open Erdos506.V1
open Erdos506.V4

universe u

/-- The precise finite output of the real nine-point link lemma.  The
hypotheses expose the complete local profile used after inversion: ten
selected points, six three-blocks and ten four-blocks through every pivot,
and no five-block. -/
structure RealPlaneNineLinkPrinciple where
  twoTriangleLinks :
    ∀ {α : Type u} [Fintype α] [DecidableEq α]
      (cfg : Configuration α),
      Erdos506.V1.Admissible cfg →
      Fintype.card α = 10 →
      (∀ p : α, (blockSystem cfg).blockDegree 3 p = 6) →
      (∀ p : α, (blockSystem cfg).blockDegree 4 p = 10) →
      (blockSystem cfg).blockCount 5 = 0 →
      TwoTriangleLinks
        (((blockSystem cfg).blocksOfSize 3).image
          (blockSystem cfg).support)

end Erdos506.Incidence
