import Erdos506.V1.HalfCap
import Erdos506.V1.SmallBasic
import Erdos506.V3.Main

/-!
# Reduction of the finite V1 range

This module records the honest short router for the finite range.  A V1
configuration is already covered by V3 when it has no collinear triple, and
by V4 when it has no four concyclic selected points.  The cases on four and
five labels are closed in `SmallBasic`.

Consequently the genuinely V1-specific finite obligation consists only of
configurations on six through fourteen labels which have both a collinear
triple and a proper circle through at least four selected points.  The final
theorems below expose exactly that obligation as a hypothesis; they do not
pretend that the remaining finite geometry has already been formalized.
-/

namespace Erdos506.V1

open Erdos506.V4

universe u

/-- The part of a V1 configuration which is covered by neither the V3 nor the
V4 theorem. -/
def SmallHardCase {α : Type*} [Fintype α] (cfg : Configuration α) : Prop :=
  ¬ Erdos506.V3.NoThreeCollinear cfg ∧ ¬ Erdos506.V4.NoFourConcyclic cfg

/-- The already formalized V3 theorem is stronger than the V1 target whenever
the V1 configuration has no collinear triple. -/
theorem circleCount_ge_target_of_noThreeCollinear
    {α : Type u} [Fintype α] [DecidableEq α]
    (Mel : Erdos506.Incidence.RealPlaneMelchiorPrinciple.{u})
    (cfg : Configuration α) (hadm : Admissible cfg)
    (hcard : 4 ≤ Fintype.card α)
    (hthree : Erdos506.V3.NoThreeCollinear cfg) :
    Erdos506.v1Target (Fintype.card α) ≤
      Erdos506.V4.circleCount cfg := by
  have hv3 := Erdos506.V3.circleCount_ge_target_of_realPlaneMelchior
    Mel cfg hcard
    (show Erdos506.V3.Admissible cfg from ⟨hthree, hadm.2⟩)
  exact (Erdos506.v1Target_le_v3Target (Fintype.card α)).trans hv3

/-- The already formalized V4 theorem is stronger than the V1 target whenever
no proper circle contains four selected points. -/
theorem circleCount_ge_target_of_noFourConcyclic
    {α : Type*} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (hadm : Admissible cfg)
    (hcard : 4 ≤ Fintype.card α)
    (hfour : Erdos506.V4.NoFourConcyclic cfg) :
    Erdos506.v1Target (Fintype.card α) ≤
      Erdos506.V4.circleCount cfg := by
  have hv4 := Erdos506.V4.circleCount_ge_target cfg hcard
    (show Erdos506.V4.Admissible cfg from ⟨hadm.1, hfour⟩)
  exact (Erdos506.v1Target_le_v4Target hcard).trans hv4

/-- Reduction of `4 ≤ n ≤ 14` to the genuinely V1-specific hard core on
`6 ≤ n ≤ 14`.  The hypothesis `hard` is deliberately theorem-shaped: it is
the precise remaining finite-geometry boundary, not a project axiom. -/
theorem circleCount_ge_target_small_of_hard
    {α : Type u} [Fintype α] [DecidableEq α]
    (Mel : Erdos506.Incidence.RealPlaneMelchiorPrinciple.{u})
    (cfg : Configuration α) (hadm : Admissible cfg)
    (hmin : 4 ≤ Fintype.card α) (hmax : Fintype.card α ≤ 14)
    (hard : 6 ≤ Fintype.card α → Fintype.card α ≤ 14 →
      SmallHardCase cfg →
      Erdos506.v1Target (Fintype.card α) ≤
        Erdos506.V4.circleCount cfg) :
    Erdos506.v1Target (Fintype.card α) ≤
      Erdos506.V4.circleCount cfg := by
  by_cases h4 : Fintype.card α = 4
  · exact circleCount_ge_target_of_card_four cfg hadm h4
  by_cases h5 : Fintype.card α = 5
  · exact circleCount_ge_target_of_card_five cfg hadm h5
  have hcard6 : 6 ≤ Fintype.card α := by omega
  by_cases hthree : Erdos506.V3.NoThreeCollinear cfg
  · exact circleCount_ge_target_of_noThreeCollinear
      Mel cfg hadm hmin hthree
  by_cases hfour : Erdos506.V4.NoFourConcyclic cfg
  · exact circleCount_ge_target_of_noFourConcyclic
      cfg hadm hmin hfour
  exact hard hcard6 hmax ⟨hthree, hfour⟩

/-- Full-domain assembly after the hard finite core has been discharged.
For `n ≥ 15` it uses the formalized half-cap theorem; below fifteen it uses
`circleCount_ge_target_small_of_hard`. -/
theorem circleCount_ge_target_of_small_hard
    {α : Type u} [Fintype α] [DecidableEq α]
    (Mel : Erdos506.Incidence.RealPlaneMelchiorPrinciple.{u})
    (Lan : Erdos506.Incidence.RealPlaneLangerPrinciple.{u})
    (cfg : Configuration α) (hadm : Admissible cfg)
    (hcard : 4 ≤ Fintype.card α)
    (hard : 6 ≤ Fintype.card α → Fintype.card α ≤ 14 →
      SmallHardCase cfg →
      Erdos506.v1Target (Fintype.card α) ≤
        Erdos506.V4.circleCount cfg) :
    Erdos506.v1Target (Fintype.card α) ≤
      Erdos506.V4.circleCount cfg := by
  by_cases hlarge : 15 ≤ Fintype.card α
  · rw [Erdos506.v1Target_eq_uniform (by omega)]
    exact v1UniformTarget_le_circleCount_large
      Mel Lan cfg hadm hlarge
  · exact circleCount_ge_target_small_of_hard
      Mel cfg hadm hcard (by omega) hard

end Erdos506.V1
