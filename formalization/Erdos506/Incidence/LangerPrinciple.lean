import Erdos506.Incidence.SpannedLines

/-!
# Explicit interface for the real-plane Langer incidence theorem

The project currently formalizes the finite line census and every transfer
used by V1, but not the algebro-geometric proof of Langer's theorem itself.
This structure makes that remaining external theorem an explicit parameter;
it is a theorem contract, not a project axiom.
-/

namespace Erdos506.Incidence

open Erdos506.V4
open scoped BigOperators

universe u

/-- Every determined line contains at most two thirds of the selected
points, in a division-free form. -/
def LineOccupancyTwoThirds
    {α : Type*} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) : Prop :=
  ∀ L : DeterminedLine cfg,
    3 * (lineSupport cfg L).card ≤ 2 * Fintype.card α

/-- Total point-line incidence of the finite determined-line census. -/
noncomputable def lineIncidence
    {α : Type*} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) : ℤ :=
  ∑ L : DeterminedLine cfg, ((lineSupport cfg L).card : ℤ)

/-- The exact Langer/de Zeeuw input needed by the V1 manuscript, scaled to
avoid division. -/
structure RealPlaneLangerPrinciple where
  incidenceBound :
    ∀ {α : Type u} [Fintype α] [DecidableEq α]
      (cfg : Configuration α),
      Noncollinear cfg → LineOccupancyTwoThirds cfg →
        (Fintype.card α : ℤ) * ((Fintype.card α : ℤ) + 3) ≤
          3 * lineIncidence cfg

end Erdos506.Incidence
