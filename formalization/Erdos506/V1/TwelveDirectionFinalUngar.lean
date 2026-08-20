import Erdos506.Incidence.UngarSixConcyclicSharpCase

/-!
# The selected-six trace and the completed Ungar endpoint

The twelve-point direction argument ultimately has to turn equality in the
dual off-star count into a five-direction statement for the six points on
the selected proper circle.  This file records the other, unconditional half
of that final contradiction: the selected trace can be reindexed as an
actual `Fin 6` configuration, and its direction census is strictly larger
than five.

No arrangement hypothesis is encoded here.  The remaining work is the
off-star nonnegativity count together with the implication from equality of
`twelveDirectionEqualityGap` to a five-direction upper bound for the
configuration below.
-/

namespace Erdos506.V1

open Erdos506.Incidence
open Erdos506.V4

universe u

/-- The six labels on a selected proper circle, in the cyclic reindexing
already used by the six-conic API. -/
noncomputable def selectedSixTraceConfiguration
    {alpha : Type u} [Fintype alpha] [DecidableEq alpha]
    (cfg : Configuration alpha) (gamma : DeterminedCircle cfg)
    (hgamma : (circleTrace cfg gamma.1).card = 6) :
    Configuration (Fin 6) where
  toFun i := cfg ((sixConicCyclicLabel cfg gamma hgamma i).1)
  inj' := by
    intro i j hij
    apply (sixConicCyclicLabel cfg gamma hgamma).injective
    apply Subtype.ext
    exact cfg.injective hij

@[simp] theorem selectedSixTraceConfiguration_apply
    {alpha : Type u} [Fintype alpha] [DecidableEq alpha]
    (cfg : Configuration alpha) (gamma : DeterminedCircle cfg)
    (hgamma : (circleTrace cfg gamma.1).card = 6) (i : Fin 6) :
    selectedSixTraceConfiguration cfg gamma hgamma i =
      cfg ((sixConicCyclicLabel cfg gamma hgamma i).1) := rfl

/-- The selected circle contains all six labels of its reindexed trace
configuration. -/
theorem circleTrace_selectedSixTraceConfiguration_eq_univ
    {alpha : Type u} [Fintype alpha] [DecidableEq alpha]
    (cfg : Configuration alpha) (gamma : DeterminedCircle cfg)
    (hgamma : (circleTrace cfg gamma.1).card = 6) :
    circleTrace (selectedSixTraceConfiguration cfg gamma hgamma) gamma.1 =
      Finset.univ := by
  classical
  apply Finset.eq_univ_of_forall
  intro i
  apply mem_circleTrace.mpr
  change cfg ((sixConicCyclicLabel cfg gamma hgamma i).1) ∈
    (gamma.1.1 : Set Point2)
  exact mem_circleTrace.mp (sixConicCyclicLabel cfg gamma hgamma i).2

/-- Ungar's sharp six-point conclusion instantiated to the actual selected
six-circle trace. -/
theorem six_le_card_determinedDirections_selectedSixTrace
    {alpha : Type u} [Fintype alpha] [DecidableEq alpha]
    (cfg : Configuration alpha) (gamma : DeterminedCircle cfg)
    (hgamma : (circleTrace cfg gamma.1).card = 6) :
    6 ≤ (determinedDirections
      (selectedSixTraceConfiguration cfg gamma hgamma)).card := by
  have htrace :
      (circleTrace (selectedSixTraceConfiguration cfg gamma hgamma)
        gamma.1).card = 6 := by
    rw [circleTrace_selectedSixTraceConfiguration_eq_univ cfg gamma hgamma]
    simp
  exact six_le_card_determinedDirections_of_circleTrace_card_six
    (selectedSixTraceConfiguration cfg gamma hgamma) gamma.1 htrace

/-- The equality-case target of the twelve-point direction argument is
incompatible with the selected six-circle, in its exact finite form. -/
theorem five_lt_card_determinedDirections_selectedSixTrace
    {alpha : Type u} [Fintype alpha] [DecidableEq alpha]
    (cfg : Configuration alpha) (gamma : DeterminedCircle cfg)
    (hgamma : (circleTrace cfg gamma.1).card = 6) :
    5 < (determinedDirections
      (selectedSixTraceConfiguration cfg gamma hgamma)).card := by
  have h := six_le_card_determinedDirections_selectedSixTrace cfg gamma hgamma
  omega

/-- The exact contradiction that the remaining equality-extraction lemma
has to feed into. -/
theorem not_card_determinedDirections_selectedSixTrace_le_five
    {alpha : Type u} [Fintype alpha] [DecidableEq alpha]
    (cfg : Configuration alpha) (gamma : DeterminedCircle cfg)
    (hgamma : (circleTrace cfg gamma.1).card = 6) :
    ¬ (determinedDirections
      (selectedSixTraceConfiguration cfg gamma hgamma)).card ≤ 5 := by
  have h := five_lt_card_determinedDirections_selectedSixTrace cfg gamma hgamma
  omega

end Erdos506.V1
