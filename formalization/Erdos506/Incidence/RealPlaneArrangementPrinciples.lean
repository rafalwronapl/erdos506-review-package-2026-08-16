import Erdos506.Incidence.RealProjectiveArrangementEulerFinish
import Erdos506.Incidence.RealPlaneEvenArrangementDerivation

/-!
# Unconditional real-plane arrangement principles

The completed real-projective arrangement topology supplies the common
global input used by both the Melchior and even-arrangement derivations.
This module exposes the resulting principles without callback parameters.
-/

namespace Erdos506.Incidence

universe u

/-- The unconditional real-plane Melchior principle assembled from the
actual finite projective arrangement. -/
noncomputable def realPlaneMelchiorPrinciple :
    RealPlaneMelchiorPrinciple.{u} :=
  realPlaneMelchiorPrincipleOfGlobalInput
    FiniteProjectiveLineArrangement.realProjectiveArrangementGlobalInput

/-- The unconditional even-arrangement principle assembled from the same
actual finite projective arrangement. -/
noncomputable def realPlaneEvenArrangementPrinciple :
    RealPlaneEvenArrangementPrinciple.{u} :=
  realPlaneEvenArrangementPrincipleOfGlobalInput
    FiniteProjectiveLineArrangement.realProjectiveArrangementGlobalInput

end Erdos506.Incidence
