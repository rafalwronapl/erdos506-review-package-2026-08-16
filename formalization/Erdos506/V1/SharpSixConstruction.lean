import Erdos506.V1.FiniteConstructionCertificate
import Erdos506.V3.EquationCircle

/-! # The sharp six-point V1 construction -/

namespace Erdos506.V1

open Erdos506.V3 Erdos506.V4

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

noncomputable def sharpSixX : Fin 6 → ℝ :=
  ![0, 4, 1, 1, 2 / 5, 2]

noncomputable def sharpSixY : Fin 6 → ℝ :=
  ![0, 0, 0, 3, 6 / 5, 2]

noncomputable def sharpSixPoint (i : Fin 6) : Point2 :=
  pointOfCoords (sharpSixX i) (sharpSixY i)

theorem sharpSixPoint_injective : Function.Injective sharpSixPoint := by
  intro i j hij
  have hx := congrArg (fun p : Point2 => p (0 : Fin 2)) hij
  have hy := congrArg (fun p : Point2 => p (1 : Fin 2)) hij
  fin_cases i <;> fin_cases j <;>
    norm_num [sharpSixPoint, sharpSixX, sharpSixY] at *

noncomputable def sharpSixConfiguration : Configuration (Fin 6) :=
  ⟨sharpSixPoint, sharpSixPoint_injective⟩

def sharpSixCircleSupport : Fin 8 → Finset (Fin 6) :=
  ![{0, 1, 3}, {0, 1, 4, 5}, {0, 2, 3, 5}, {0, 2, 4},
    {1, 2, 3, 4}, {1, 2, 5}, {2, 4, 5}, {3, 4, 5}]

noncomputable def sharpSixD : Fin 8 → ℝ :=
  ![-4, -4, -1, -1, -5, -5, -3, -2]

noncomputable def sharpSixE : Fin 8 → ℝ :=
  ![-2, 0, -3, -1, -3, -1, -2, -4]

noncomputable def sharpSixF : Fin 8 → ℝ :=
  ![0, 0, 0, 0, 4, 4, 2, 4]

theorem sharpSix_radiusSq_pos (i : Fin 8) :
    0 < equationCircleRadiusSq (sharpSixD i) (sharpSixE i) (sharpSixF i) := by
  fin_cases i <;>
    norm_num [equationCircleRadiusSq, sharpSixD, sharpSixE, sharpSixF]

noncomputable def sharpSixCircle (i : Fin 8) : ProperCircle :=
  properCircleOfEquation (sharpSixD i) (sharpSixE i) (sharpSixF i)
    (sharpSix_radiusSq_pos i)

theorem sharpSixPoint_mem_circle_iff (i : Fin 8) (j : Fin 6) :
    sharpSixPoint j ∈ ((sharpSixCircle i).1 : Set Point2) ↔
      j ∈ sharpSixCircleSupport i := by
  rw [sharpSixCircle, mem_properCircleOfEquation_iff]
  fin_cases i <;> fin_cases j
  all_goals
    norm_num [circleEquation, sharpSixPoint, sharpSixX, sharpSixY,
      sharpSixD, sharpSixE, sharpSixF, sharpSixCircleSupport]
  all_goals decide

theorem sharpSix_circleTrace (i : Fin 8) :
    circleTrace sharpSixConfiguration (sharpSixCircle i) =
      sharpSixCircleSupport i := by
  ext j
  rw [mem_circleTrace]
  exact sharpSixPoint_mem_circle_iff i j

def sharpSixLineSupport : Fin 3 → Finset (Fin 6) :=
  ![{0, 1, 2}, {0, 3, 4}, {1, 3, 5}]

def sharpSixLineA : Fin 3 → Fin 6 := ![0, 0, 1]
def sharpSixLineB : Fin 3 → Fin 6 := ![1, 3, 3]

theorem sharpSixLineA_mem (i : Fin 3) :
    sharpSixLineA i ∈ sharpSixLineSupport i := by
  fin_cases i <;> decide

theorem sharpSixLineB_mem (i : Fin 3) :
    sharpSixLineB i ∈ sharpSixLineSupport i := by
  fin_cases i <;> decide

theorem sharpSixLineAB_ne (i : Fin 3) :
    sharpSixLineA i ≠ sharpSixLineB i := by
  fin_cases i <;> decide

theorem sharpSixLineSupport_collinear (i : Fin 3) :
    Collinear ℝ (supportPoints sharpSixConfiguration (sharpSixLineSupport i)) := by
  apply collinear_set_of_orientation_eq_zero
    (supportPoints sharpSixConfiguration (sharpSixLineSupport i))
    (sharpSixConfiguration (sharpSixLineA i))
    (sharpSixConfiguration (sharpSixLineB i))
  · exact ⟨sharpSixLineA i, sharpSixLineA_mem i, rfl⟩
  · exact sharpSixConfiguration.injective.ne (sharpSixLineAB_ne i)
  · intro p hp
    rcases hp with ⟨j, hj, rfl⟩
    fin_cases i <;> fin_cases j <;>
      simp_all [orientation, sharpSixConfiguration, sharpSixPoint,
        sharpSixX, sharpSixY, sharpSixLineA, sharpSixLineB,
        sharpSixLineSupport]
    all_goals norm_num

theorem sharpSix_all_triples_covered
    (t : Finset (Fin 6)) (ht : t.card = 3) :
    (∃ i : Fin 8, t ⊆ sharpSixCircleSupport i) ∨
      (∃ i : Fin 3, t ⊆ sharpSixLineSupport i) := by
  revert t
  decide

theorem sharpSix_noncollinear_triples_covered
    (t : Finset (Fin 6)) (ht : t.card = 3)
    (hnon : IsNoncollinear sharpSixConfiguration t) :
    ∃ i : Fin 8, t ⊆ sharpSixCircleSupport i :=
  noncollinear_covered_of_circle_or_line sharpSixConfiguration
    sharpSixCircleSupport sharpSixLineSupport sharpSixLineSupport_collinear
    sharpSix_all_triples_covered t ht hnon

theorem sharpSixCircleSupport_card_ge_three (i : Fin 8) :
    3 ≤ (sharpSixCircleSupport i).card := by
  fin_cases i <;> decide

theorem sharpSixCircleSupport_card_lt_six (i : Fin 8) :
    (sharpSixCircleSupport i).card < 6 := by
  fin_cases i <;> decide

theorem sharpSixCircleSupport_injective :
    Function.Injective sharpSixCircleSupport := by
  decide

theorem sharpSix_noncollinear : Noncollinear sharpSixConfiguration := by
  intro hcol
  have hsub :
      ({sharpSixPoint 0, sharpSixPoint 1, sharpSixPoint 3} : Set Point2) ⊆
        pointSet sharpSixConfiguration := by
    intro p hp
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
    rcases hp with rfl | rfl | rfl <;> exact ⟨_, rfl⟩
  have hpGlobal : sharpSixPoint 0 ∈ pointSet sharpSixConfiguration := ⟨0, rfl⟩
  rw [collinear_iff_of_mem hpGlobal] at hcol
  obtain ⟨v, hv⟩ := hcol
  have hpTriple : sharpSixPoint 0 ∈
      ({sharpSixPoint 0, sharpSixPoint 1, sharpSixPoint 3} : Set Point2) := by simp
  have htriple : Collinear ℝ
      ({sharpSixPoint 0, sharpSixPoint 1, sharpSixPoint 3} : Set Point2) := by
    rw [collinear_iff_of_mem hpTriple]
    refine ⟨v, ?_⟩
    intro p hp
    exact hv p (hsub hp)
  exact (not_collinear_of_orientation_ne_zero _ _ _ (by
    simp [orientation, sharpSixPoint, sharpSixX, sharpSixY])) htriple

theorem sharpSix_admissible : Admissible sharpSixConfiguration :=
  admissible_of_finite_certificate sharpSixConfiguration sharpSixCircle
    sharpSixCircleSupport sharpSix_circleTrace
    sharpSixCircleSupport_card_ge_three sharpSix_noncollinear_triples_covered
    (by norm_num) sharpSix_noncollinear sharpSixCircleSupport_card_lt_six

theorem sharpSix_circleCount :
    circleCount sharpSixConfiguration = 8 :=
  circleCount_eq_listed_card sharpSixConfiguration sharpSixCircle
    sharpSixCircleSupport sharpSix_circleTrace
    sharpSixCircleSupport_card_ge_three sharpSix_noncollinear_triples_covered
    sharpSixCircleSupport_injective

end Erdos506.V1
