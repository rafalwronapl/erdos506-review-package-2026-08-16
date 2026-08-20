import Erdos506.V1.FiniteHardCore
import Erdos506.V1.LangerApplicationTail

/-!
# Langer-free outer assembly

The large range `n >= 23` is already supplied by the cap-sensitive
Melchior master.  This leaf isolates the remaining finite window
`14 <= n <= 22` behind one theorem-shaped endpoint and reuses the completed
finite hard core below fourteen.  It does not assert a finite-window result.
-/

namespace Erdos506.V1

open Erdos506.Incidence Erdos506.V4

universe u

/-- Full-domain V1 assembly without a Langer parameter, once the finite
window `14..22` is discharged. -/
theorem circleCount_ge_target_of_exact_finite_hard_core_without_langer
    {alpha : Type u} [Fintype alpha] [DecidableEq alpha]
    (Mel : RealPlaneMelchiorPrinciple.{u})
    (EvenArr : RealPlaneEvenArrangementPrinciple.{u})
    (Cross : RealPlaneRadicalAxisCrossBlockPrinciple.{u})
    (Kelly : RealPlaneKellyMoserPrinciple.{u})
    (U17 : RealPlaneSixCircleU17Principle.{u})
    (cfg : Configuration alpha) (hadm : Admissible cfg)
    (hcard : 4 <= Fintype.card alpha)
    (finiteWindow : 14 <= Fintype.card alpha ->
      Fintype.card alpha <= 22 ->
        Erdos506.v1Target (Fintype.card alpha) <=
          Erdos506.V4.circleCount cfg)
    (tenFive : Fintype.card alpha = 10 -> SmallHardCase cfg ->
      forall c : DeterminedCircle cfg,
        (circleTrace cfg c.1).card = 5 ->
          33 <= Erdos506.V4.circleCount cfg)
    (elevenFiveOrSix : Fintype.card alpha = 11 -> SmallHardCase cfg ->
      forall c : DeterminedCircle cfg,
        Or ((circleTrace cfg c.1).card = 5)
          ((circleTrace cfg c.1).card = 6) ->
            41 <= Erdos506.V4.circleCount cfg)
    (twelveFiveOrSix : Fintype.card alpha = 12 -> SmallHardCase cfg ->
      forall c : DeterminedCircle cfg,
        Or ((circleTrace cfg c.1).card = 5)
          ((circleTrace cfg c.1).card = 6) ->
            51 <= Erdos506.V4.circleCount cfg)
    (thirteenSix : Fintype.card alpha = 13 -> SmallHardCase cfg ->
      forall c : DeterminedCircle cfg,
        (circleTrace cfg c.1).card = 6 ->
          61 <= Erdos506.V4.circleCount cfg) :
    Erdos506.v1Target (Fintype.card alpha) <=
      Erdos506.V4.circleCount cfg := by
  by_cases htail : 23 <= Fintype.card alpha
  · rw [Erdos506.v1Target_eq_uniform (by omega)]
    exact v1UniformTarget_le_circleCount_tail_without_langer
      Mel cfg hadm htail
  by_cases hwindow : 14 <= Fintype.card alpha
  · exact finiteWindow hwindow (by omega)
  have hmax : Fintype.card alpha <= 13 := by omega
  apply circleCount_ge_target_small_of_hard
    Mel cfg hadm hcard (by omega)
  intro hsix hthirteen hhard
  by_cases h6 : Fintype.card alpha = 6
  · exact circleCount_ge_target_of_card_six cfg hadm h6
  by_cases h7 : Fintype.card alpha = 7
  · have h := circleCount_ge_target_of_card_seven Mel cfg hadm h7
    rw [h7] at ⊢
    norm_num [Erdos506.v1Target] at ⊢
    exact h
  by_cases h8 : Fintype.card alpha = 8
  · have h := circleCount_ge_target_of_card_eight
      Mel EvenArr cfg hadm h8
    rw [h8] at ⊢
    norm_num [Erdos506.v1Target] at ⊢
    exact h
  by_cases h9 : Fintype.card alpha = 9
  · have h := circleCount_ge_twenty_five_of_card_nine
      Mel EvenArr Cross cfg hadm h9
    rw [h9]
    norm_num [Erdos506.v1Target, Erdos506.v1UniformTarget, Nat.choose]
    exact h
  by_cases h10 : Fintype.card alpha = 10
  · have h :=
      circleCount_ge_thirty_three_of_card_ten_of_five_circle_endpoint
        Mel EvenArr Kelly U17 cfg hadm h10 (tenFive h10 hhard)
    rw [h10]
    norm_num [Erdos506.v1Target, Erdos506.v1UniformTarget, Nat.choose]
    exact h
  by_cases h11 : Fintype.card alpha = 11
  · have h :=
      circleCount_ge_forty_one_of_card_eleven_of_five_or_six_endpoint
        Mel Kelly cfg hadm h11 (elevenFiveOrSix h11 hhard)
    rw [h11]
    norm_num [Erdos506.v1Target, Erdos506.v1UniformTarget, Nat.choose]
    exact h
  by_cases h12 : Fintype.card alpha = 12
  · have h :=
      circleCount_ge_fifty_one_of_card_twelve_of_five_or_six_endpoint
        Mel Kelly cfg hadm h12 (twelveFiveOrSix h12 hhard)
    rw [h12]
    norm_num [Erdos506.v1Target, Erdos506.v1UniformTarget, Nat.choose]
    exact h
  have h13 : Fintype.card alpha = 13 := by omega
  have h := circleCount_ge_sixty_one_of_card_thirteen_of_six_circle_hard
    Mel cfg hadm h13 (thirteenSix h13 hhard)
  rw [h13]
  norm_num [Erdos506.v1Target, Erdos506.v1UniformTarget, Nat.choose]
  exact h

end Erdos506.V1
