import Erdos506.V1.BlockRows

/-!
# Ordinary-line and ordinary-circle inputs

The finite cases use Kelly--Moser only when the pivot configuration has
cardinality `10` through `13` (equivalently, after inversion, `9` through
`12` ordinary points).  This file records only that guarded local,
division-free consequence for the already formalized V1 pivot dictionary.
They are explicit parameters, not axioms or typeclass instances.

* Kelly--Moser gives at least `3q/7` ordinary lines on the `q = n - 1`
  inverted points.  Such lines are exactly three-blocks through the pivot.
* Lenchner gives at least `(2q-3)/7` finite ordinary intersections.  Under
  the inversion/duality dictionary these are ordinary proper circles through
  the pivot.  Its exceptional six-line arrangement is removed by `q ≠ 6`.

Neither structure contains a circle-count target or a finite-case endpoint.
-/

namespace Erdos506.Incidence

open Erdos506.V1
open Erdos506.V4

universe u

/-- The local Kelly--Moser row after the checked V1 pivot inversion. -/
structure RealPlaneKellyMoserPrinciple where
  pivot_three_block_bound :
    ∀ {α : Type u} [Fintype α] [DecidableEq α]
      (cfg : Configuration α),
      Erdos506.V1.Admissible cfg →
        10 ≤ Fintype.card α → Fintype.card α ≤ 13 → ∀ p : α,
        3 * (Fintype.card α - 1) ≤
          7 * blockDegree cfg 3 p

/-- The finite-ordinary-intersection consequence of Lenchner's theorem,
transported through the checked V1 pivot dictionary. -/
structure RealPlaneLenchnerPrinciple where
  pivot_ordinary_circle_bound :
    ∀ {α : Type u} [Fintype α] [DecidableEq α]
      (cfg : Configuration α),
      Erdos506.V1.Admissible cfg → Fintype.card α - 1 ≠ 6 → ∀ p : α,
        2 * (Fintype.card α - 1) ≤
          7 * circleDegree cfg 3 p + 3

end Erdos506.Incidence
