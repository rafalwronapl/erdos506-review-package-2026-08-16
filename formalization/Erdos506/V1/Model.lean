import Erdos506.V3.Model

/-!
# V1 configurations

V1 permits collinear triples.  Its only global exclusions are that the
selected points are not all collinear and are not all contained in one proper
Euclidean circle.  Circle determination and circle counting reuse the semantic
circumcircle model shared with V3 and V4.
-/

namespace Erdos506.V1

open Erdos506.V4

/-- No proper circle contains every selected label. -/
abbrev NotConcyclic {α : Type*} [Fintype α] (cfg : Configuration α) :=
  Erdos506.V3.NotConcyclic cfg

/-- The frozen V1 admissibility predicate. -/
def Admissible {α : Type*} [Fintype α] (cfg : Configuration α) : Prop :=
  Noncollinear cfg ∧ NotConcyclic cfg

/-- A proper circle determined by at least one noncollinear selected triple. -/
abbrev DeterminedCircle {α : Type*} [Fintype α] (cfg : Configuration α) :=
  Erdos506.V3.DeterminedCircle cfg

end Erdos506.V1
