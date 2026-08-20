import Erdos506.V1.FourteenSelected
import Erdos506.V1.Eight
import Erdos506.V1.Seven
import Erdos506.V1.SmallSixClassifier

/-!
# The reduced finite V1 router

The endpoints on six, seven, eight, and fourteen labels are now checked
directly.  The first assembly theorem leaves a callback on eight through
thirteen labels without requiring the extra even-arrangement input; the
refined public assembly accepts that explicit input and leaves only the
genuinely case-specific hard core on nine through thirteen labels.
-/

namespace Erdos506.V1

open Erdos506.V4

universe u

/-- On the finite window, the only remaining callback is the hard core
`8 ≤ n ≤ 13`. -/
theorem circleCount_ge_target_small_of_middle_hard
    {α : Type u} [Fintype α] [DecidableEq α]
    (Mel : Erdos506.Incidence.RealPlaneMelchiorPrinciple.{u})
    (Lan : Erdos506.Incidence.RealPlaneLangerPrinciple.{u})
    (cfg : Configuration α) (hadm : Admissible cfg)
    (hmin : 4 ≤ Fintype.card α) (hmax : Fintype.card α ≤ 14)
    (middle : 8 ≤ Fintype.card α → Fintype.card α ≤ 13 →
      SmallHardCase cfg →
      Erdos506.v1Target (Fintype.card α) ≤
        Erdos506.V4.circleCount cfg) :
    Erdos506.v1Target (Fintype.card α) ≤
      Erdos506.V4.circleCount cfg := by
  apply circleCount_ge_target_small_of_hard Mel cfg hadm hmin hmax
  intro hsix hfourteen hhard
  by_cases h6 : Fintype.card α = 6
  · exact circleCount_ge_target_of_card_six cfg hadm h6
  by_cases h7 : Fintype.card α = 7
  · have h := circleCount_ge_target_of_card_seven Mel cfg hadm h7
    rw [h7] at ⊢
    norm_num [Erdos506.v1Target] at ⊢
    exact h
  by_cases h14 : Fintype.card α = 14
  · have h := circleCount_ge_seventy_three_of_card_fourteen
      Mel Lan cfg hadm h14
    rw [h14] at ⊢
    norm_num [Erdos506.v1Target, Erdos506.v1UniformTarget,
      Nat.choose] at ⊢
    exact h
  exact middle (by omega) (by omega) hhard

/-- Full-domain assembly after only the hard cases `8 ≤ n ≤ 13` have been
supplied.  The large range still goes through the checked half-cap master. -/
theorem circleCount_ge_target_of_middle_hard
    {α : Type u} [Fintype α] [DecidableEq α]
    (Mel : Erdos506.Incidence.RealPlaneMelchiorPrinciple.{u})
    (Lan : Erdos506.Incidence.RealPlaneLangerPrinciple.{u})
    (cfg : Configuration α) (hadm : Admissible cfg)
    (hcard : 4 ≤ Fintype.card α)
    (middle : 8 ≤ Fintype.card α → Fintype.card α ≤ 13 →
      SmallHardCase cfg →
      Erdos506.v1Target (Fintype.card α) ≤
        Erdos506.V4.circleCount cfg) :
    Erdos506.v1Target (Fintype.card α) ≤
      Erdos506.V4.circleCount cfg := by
  by_cases hlarge : 15 ≤ Fintype.card α
  · rw [Erdos506.v1Target_eq_uniform (by omega)]
    exact v1UniformTarget_le_circleCount_large Mel Lan cfg hadm hlarge
  · exact circleCount_ge_target_small_of_middle_hard
      Mel Lan cfg hadm hcard (by omega) middle

/-- After supplying the explicit even-arrangement input, the only callback in
the finite window is the hard core `9 ≤ n ≤ 13`. -/
theorem circleCount_ge_target_small_of_nine_hard
    {α : Type u} [Fintype α] [DecidableEq α]
    (Mel : Erdos506.Incidence.RealPlaneMelchiorPrinciple.{u})
    (Lan : Erdos506.Incidence.RealPlaneLangerPrinciple.{u})
    (EvenArr : Erdos506.Incidence.RealPlaneEvenArrangementPrinciple.{u})
    (cfg : Configuration α) (hadm : Admissible cfg)
    (hmin : 4 ≤ Fintype.card α) (hmax : Fintype.card α ≤ 14)
    (middle : 9 ≤ Fintype.card α → Fintype.card α ≤ 13 →
      SmallHardCase cfg →
      Erdos506.v1Target (Fintype.card α) ≤
        Erdos506.V4.circleCount cfg) :
    Erdos506.v1Target (Fintype.card α) ≤
      Erdos506.V4.circleCount cfg := by
  apply circleCount_ge_target_small_of_middle_hard
    Mel Lan cfg hadm hmin hmax
  intro height hthirteen hhard
  by_cases h8 : Fintype.card α = 8
  · have h := circleCount_ge_target_of_card_eight
      Mel EvenArr cfg hadm h8
    rw [h8] at ⊢
    norm_num [Erdos506.v1Target] at ⊢
    exact h
  · exact middle (by omega) hthirteen hhard

/-- Full-domain assembly after only the hard cases `9 ≤ n ≤ 13` have been
supplied.  The case `n = 8` uses the explicit even-arrangement input, and the
large range uses the checked half-cap master. -/
theorem circleCount_ge_target_of_nine_hard
    {α : Type u} [Fintype α] [DecidableEq α]
    (Mel : Erdos506.Incidence.RealPlaneMelchiorPrinciple.{u})
    (Lan : Erdos506.Incidence.RealPlaneLangerPrinciple.{u})
    (EvenArr : Erdos506.Incidence.RealPlaneEvenArrangementPrinciple.{u})
    (cfg : Configuration α) (hadm : Admissible cfg)
    (hcard : 4 ≤ Fintype.card α)
    (middle : 9 ≤ Fintype.card α → Fintype.card α ≤ 13 →
      SmallHardCase cfg →
      Erdos506.v1Target (Fintype.card α) ≤
        Erdos506.V4.circleCount cfg) :
    Erdos506.v1Target (Fintype.card α) ≤
      Erdos506.V4.circleCount cfg := by
  apply circleCount_ge_target_of_middle_hard Mel Lan cfg hadm hcard
  intro height hthirteen hhard
  by_cases h8 : Fintype.card α = 8
  · have h := circleCount_ge_target_of_card_eight
      Mel EvenArr cfg hadm h8
    rw [h8] at ⊢
    norm_num [Erdos506.v1Target] at ⊢
    exact h
  · exact middle (by omega) hthirteen hhard

end Erdos506.V1
