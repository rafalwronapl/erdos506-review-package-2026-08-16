import Erdos506.V1.Model

/-!
# The six-marked-circle U17 input

This file isolates exactly equation U17 from the manuscript.  It is an
explicit input, not an axiom or a typeclass instance.  For a determined
circle `gamma` carrying six selected labels and a disjoint four-set `Y`, a
determined circle contributes one for every pair of `Y` that it contains,
provided that its trace on `gamma` has size exactly two.  Thus the displayed
sum is precisely `sum_e q_e` in the paper.
-/

namespace Erdos506.Incidence

open Erdos506.V1
open Erdos506.V4
open scoped BigOperators

universe u

/-- Equation U17 for a six-marked real circle, packaged as an explicit
geometric input.  No other conclusion of the six-conic-events lemma is
included in this interface. -/
structure RealPlaneSixCircleU17Principle where
  u17 :
    ∀ {α : Type u} [Fintype α] [DecidableEq α]
      (cfg : Configuration α) (gamma : DeterminedCircle cfg)
      (_hgamma : (circleTrace cfg gamma.1).card = 6)
      (Y : Finset α) (_hY : Y.card = 4)
      (_hdisjoint : Disjoint (circleTrace cfg gamma.1) Y),
      (∑ c : DeterminedCircle cfg,
        if (circleTrace cfg c.1 ∩ circleTrace cfg gamma.1).card = 2 then
          Nat.choose (circleTrace cfg c.1 ∩ Y).card 2
        else 0) ≤ 17

end Erdos506.Incidence
