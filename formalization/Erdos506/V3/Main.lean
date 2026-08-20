import Erdos506.Incidence.RealPlaneArrangementPrinciples
import Erdos506.V3.PivotGeometry
import Erdos506.V3.SmallRouting
import Erdos506.V3.ExceptionalEightMain

/-!
# Assembly of the V3 theorem

All V3 geometry, finite classifications, arithmetic routing, and extremal
constructions are assembled here.  The real-plane Melchior theorem is now
constructed from the completed projective-arrangement cellulation, so the
public lower bound has no geometric-principle parameter.
-/

namespace Erdos506.V3

open Erdos506.Incidence
open Erdos506.V4

universe u

/-- The real-plane Melchior principle supplies every pivot row and hence the
summed row used by the V3 functional. -/
theorem summedMelchior_of_realPlaneMelchior
    {α : Type u} [Fintype α] [DecidableEq α]
    (P : RealPlaneMelchiorPrinciple.{u})
    (cfg : Configuration α) (hadm : Admissible cfg)
    (hcard : 4 ≤ Fintype.card α) :
    SummedMelchior cfg := by
  apply summedMelchior_of_pivots
  intro p
  apply pivotMelchior_of_lineMelchior cfg hadm.1 p
  exact P.lineMelchior (pivotInversion cfg p)
    (pivotInversion_noncollinear cfg hadm.1 hadm.2 (by omega) p)

/-- Complete V3 lower-bound routing from an explicitly supplied real-plane
Melchior theorem.  This compatibility endpoint is also reused internally by
the V1 finite reduction. -/
theorem circleCount_ge_target_of_realPlaneMelchior
    {α : Type u} [Fintype α] [DecidableEq α]
    (P : RealPlaneMelchiorPrinciple.{u})
    (cfg : Configuration α) (hcard : 4 ≤ Fintype.card α)
    (hadm : Admissible cfg) :
    Erdos506.v3Target (Fintype.card α) ≤ circleCount cfg := by
  by_cases h4 : Fintype.card α = 4
  · exact circleCount_ge_target_of_card_four cfg hadm h4
  by_cases h5 : Fintype.card α = 5
  · exact circleCount_ge_target_of_card_five cfg hadm h5
  by_cases h6 : Fintype.card α = 6
  · exact circleCount_ge_target_of_card_six cfg hadm h6
  by_cases h7 : Fintype.card α = 7
  · exact circleCount_ge_target_of_card_seven cfg hadm h7
  have hmel := summedMelchior_of_realPlaneMelchior P cfg hadm hcard
  by_cases h8 : Fintype.card α = 8
  · exact circleCount_ge_target_of_card_eight_of_summedMelchior
      cfg hadm h8 hmel
  by_cases h9 : Fintype.card α = 9
  · exact circleCount_ge_target_of_card_nine_of_summedMelchior
      cfg hadm h9 hmel
  by_cases h10 : Fintype.card α = 10
  · exact circleCount_ge_target_of_card_ten_of_summedMelchior
      cfg hadm h10 hmel
  exact circleCount_ge_target_of_summedMelchior cfg (by omega) hadm hmel

/-- Complete parameter-free V3 lower bound. -/
theorem circleCount_ge_target
    {α : Type u} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (hcard : 4 ≤ Fintype.card α)
    (hadm : Admissible cfg) :
    Erdos506.v3Target (Fintype.card α) ≤ circleCount cfg :=
  circleCount_ge_target_of_realPlaneMelchior
    realPlaneMelchiorPrinciple cfg hcard hadm

/-- The sharp V3 value is attained for every `n ≥ 4`.  This construction
theorem is unconditional: the exceptional eight-point configuration is used
at `n = 8`, and the near-circle family is used otherwise. -/
theorem exists_v3_extremal_configuration (n : ℕ) (hn : 4 ≤ n) :
    ∃ α : Type, ∃ _fin : Fintype α, ∃ _dec : DecidableEq α,
      ∃ cfg : Configuration α,
        Fintype.card α = n ∧ Admissible cfg ∧
          circleCount cfg = Erdos506.v3Target n := by
  by_cases hn8 : n = 8
  · subst n
    refine ⟨Fin 8, inferInstance, inferInstance,
      exceptionalEightConfiguration, by simp, exceptionalEight_admissible, ?_⟩
    simpa [Erdos506.v3Target] using exceptionalEight_circleCount
  · obtain ⟨cfg, hcard, hadm, hcount⟩ :=
      exists_generic_extremal_configuration n hn
    refine ⟨NearCircleLabels n, inferInstance, inferInstance,
      cfg, hcard, hadm, ?_⟩
    rw [Erdos506.v3Target_eq_generic hn8]
    exact hcount

end Erdos506.V3
