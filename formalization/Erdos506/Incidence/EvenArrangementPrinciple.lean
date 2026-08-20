import Erdos506.Incidence.MelchiorPrinciple
import Erdos506.Incidence.CellulationParity

/-!
# The even-arrangement Melchior-slack interface

For an even non-pencil arrangement of real projective lines, the usual
two-colouring of the faces rules out Melchior slack one.  This file records
that topological input as an explicit structure; it does not postulate it as
a kernel axiom.  A future cellulation development can construct the
structure from the face two-colouring argument.
-/

namespace Erdos506.Incidence

open Erdos506.V4
open scoped BigOperators

universe u

/-- Melchior slack of the lines spanned by a finite point configuration. -/
noncomputable def lineMelchiorSlack {α : Type*} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) : ℤ :=
  (∑ L : DeterminedLine cfg,
    (3 - ((lineSupport cfg L).card : ℤ))) - 3

/-- The ordinary Melchior inequality is exactly nonnegativity of its slack. -/
theorem lineMelchior_iff_slack_nonneg
    {α : Type*} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) :
    LineMelchior cfg ↔ 0 ≤ lineMelchiorSlack cfg := by
  unfold LineMelchior lineMelchiorSlack
  omega

/-- Explicit real-plane input supplied by the face two-colouring of an even
projective line arrangement.  `Noncollinear cfg` is the dual non-pencil
hypothesis. -/
structure RealPlaneEvenArrangementPrinciple where
  slack_ne_one :
    ∀ {α : Type u} [Fintype α] [DecidableEq α]
      (cfg : Configuration α),
      Noncollinear cfg → Even (Fintype.card α) →
        lineMelchiorSlack cfg ≠ 1

end Erdos506.Incidence
