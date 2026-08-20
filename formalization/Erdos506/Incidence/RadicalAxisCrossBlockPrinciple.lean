import Erdos506.V1.Carrier

/-!
# Radical-axis cross-block interface

The nine-point five-circle argument uses one genuinely metric fact.  Chords
of two distinct real circles determine a line or a concyclic four-set only
when their supporting lines meet on the radical axis.  Matching multiplicity
on that axis bounds the number of distinct cross-blocks by `12` in the
`5 + 4` case and by `10` in the `4 + 4` case.

This file records exactly that geometric input as an explicit structure.  It
does not postulate an axiom or include any part of the nine-point conclusion.
A later power-of-a-point/radical-axis development can construct the
structure.
-/

namespace Erdos506.Incidence

open Erdos506.V1
open Erdos506.V4

universe u

/-- Marked points belonging to the first circle but not the second. -/
noncomputable def exclusiveCircleTrace
    {α : Type*} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (Γ Ω : DeterminedCircle cfg) : Finset α :=
  circleTrace cfg Γ.1 \ circleTrace cfg Ω.1

/-- Geometric carriers containing two exclusive marked points from each of
two determined circles.  Extra selected points on a carrier are harmless:
the radical-axis argument counts the carrier through its two chord pairs. -/
noncomputable def circleCrossBlocks
    {α : Type*} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (Γ Ω : DeterminedCircle cfg) :
    Finset (GeometricBlock cfg) := by
  classical
  exact Finset.univ.filter fun b =>
    (geometricBlockSupport cfg b ∩ exclusiveCircleTrace cfg Γ Ω).card = 2 ∧
    (geometricBlockSupport cfg b ∩ exclusiveCircleTrace cfg Ω Γ).card = 2

/-- The two radical-axis capacities used by the analytic `n = 9` proof.
The hypotheses mention only the two exclusive marked traces and do not hide
a circle-count or endpoint conclusion. -/
structure RealPlaneRadicalAxisCrossBlockPrinciple where
  five_four :
    ∀ {α : Type u} [Fintype α] [DecidableEq α]
      (cfg : Configuration α) (Γ Ω : DeterminedCircle cfg),
      Γ ≠ Ω →
      (exclusiveCircleTrace cfg Γ Ω).card = 5 →
      (exclusiveCircleTrace cfg Ω Γ).card = 4 →
      (circleCrossBlocks cfg Γ Ω).card ≤ 12

  four_four :
    ∀ {α : Type u} [Fintype α] [DecidableEq α]
      (cfg : Configuration α) (Γ Ω : DeterminedCircle cfg),
      Γ ≠ Ω →
      (exclusiveCircleTrace cfg Γ Ω).card = 4 →
      (exclusiveCircleTrace cfg Ω Γ).card = 4 →
      (circleCrossBlocks cfg Γ Ω).card ≤ 10

end Erdos506.Incidence
