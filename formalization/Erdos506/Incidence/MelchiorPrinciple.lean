import Erdos506.Incidence.SpannedLines

/-!
# Reusable interface for the real-arrangement theorem

This structure packages Melchior's inequality for every finite noncollinear
set in the real affine plane.  `RealPlaneArrangementPrinciples` constructs its
public value from the completed projective line-arrangement cellulation.  The
explicit interface remains useful for local compatibility theorems and for
separating the finite routing from its geometric producer.
-/

namespace Erdos506.Incidence

open Erdos506.V4

universe u

/-- The general real-plane Melchior theorem, packaged as an explicit input. -/
structure RealPlaneMelchiorPrinciple where
  lineMelchior :
    ∀ {α : Type u} [Fintype α] [DecidableEq α]
      (cfg : Configuration α), Noncollinear cfg → LineMelchior cfg

end Erdos506.Incidence
