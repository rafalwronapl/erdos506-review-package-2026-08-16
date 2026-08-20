import Erdos506.V1.FiniteConstructionCertificate
import Erdos506.V3.EquationCircle

/-! # The sharp eight-point V1 construction -/

namespace Erdos506.V1

open Erdos506.V3 Erdos506.V4

set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

noncomputable def sharpEightX : Fin 8 → ℝ :=
  ![0, 1, 1 / 3, 2 / 3, 2 / 3, 2 / 5, 1 / 3, 3 / 5]

noncomputable def sharpEightY : Fin 8 → ℝ :=
  ![0, 0, 0, 0, 1 / 3, 1 / 5, 1 / 3, 1 / 5]

noncomputable def sharpEightPoint (i : Fin 8) : Point2 :=
  pointOfCoords (sharpEightX i) (sharpEightY i)

theorem sharpEightPoint_injective : Function.Injective sharpEightPoint := by
  intro i j hij
  have hx := congrArg (fun p : Point2 => p (0 : Fin 2)) hij
  have hy := congrArg (fun p : Point2 => p (1 : Fin 2)) hij
  fin_cases i <;> fin_cases j <;>
    norm_num [sharpEightPoint, sharpEightX, sharpEightY] at *

noncomputable def sharpEightConfiguration : Configuration (Fin 8) :=
  ⟨sharpEightPoint, sharpEightPoint_injective⟩

def sharpEightCircleSupport : Fin 17 → Finset (Fin 8) :=
  ![
    {0, 1, 4, 6}, {0, 1, 5, 7}, {0, 2, 4, 7}, {0, 2, 5, 6},
    {0, 3, 6, 7}, {1, 2, 4, 5}, {1, 3, 4, 7}, {1, 3, 5, 6},
    {2, 3, 4, 6}, {2, 3, 5, 7}, {4, 5, 6, 7},
    {0, 3, 4}, {0, 3, 5}, {1, 2, 6}, {1, 2, 7}, {2, 6, 7}, {3, 4, 5}
  ]

noncomputable def sharpEightD : Fin 17 → ℝ :=
  ![-1, -1, -1 / 3, -1 / 3, -2 / 3, -4 / 3, -5 / 3, -5 / 3,
    -1, -1, -1, -2 / 3, -2 / 3, -4 / 3, -4 / 3, -5 / 6, -7 / 6]

noncomputable def sharpEightE : Fin 17 → ℝ :=
  ![1 / 3, 1, -1, -1 / 3, 0, 0, -1 / 3, -1,
    -1 / 3, -1 / 9, -2 / 3, -1 / 3, 1 / 3, -1 / 3, 1 / 3,
    -1 / 3, -1 / 3]

noncomputable def sharpEightF : Fin 17 → ℝ :=
  ![0, 0, 0, 0, 0, 1 / 3, 2 / 3, 2 / 3,
    2 / 9, 2 / 9, 1 / 3, 0, 0, 1 / 3, 1 / 3, 1 / 6, 1 / 3]

theorem sharpEight_radiusSq_pos (i : Fin 17) :
    0 < equationCircleRadiusSq (sharpEightD i) (sharpEightE i)
      (sharpEightF i) := by
  fin_cases i <;>
    norm_num [equationCircleRadiusSq, sharpEightD, sharpEightE, sharpEightF]

noncomputable def sharpEightCircle (i : Fin 17) : ProperCircle :=
  properCircleOfEquation (sharpEightD i) (sharpEightE i) (sharpEightF i)
    (sharpEight_radiusSq_pos i)

theorem sharpEightPoint_mem_circle_iff (i : Fin 17) (j : Fin 8) :
    sharpEightPoint j ∈ ((sharpEightCircle i).1 : Set Point2) ↔
      j ∈ sharpEightCircleSupport i := by
  rw [sharpEightCircle, mem_properCircleOfEquation_iff]
  fin_cases i <;> fin_cases j
  all_goals
    norm_num [circleEquation, sharpEightPoint, sharpEightX, sharpEightY,
      sharpEightD, sharpEightE, sharpEightF, sharpEightCircleSupport]
  all_goals decide

theorem sharpEight_circleTrace (i : Fin 17) :
    circleTrace sharpEightConfiguration (sharpEightCircle i) =
      sharpEightCircleSupport i := by
  ext j
  rw [mem_circleTrace]
  exact sharpEightPoint_mem_circle_iff i j

def sharpEightLineSupport : Fin 3 → Finset (Fin 8) :=
  ![{0, 1, 2, 3}, {0, 4, 5}, {1, 6, 7}]

def sharpEightLineA : Fin 3 → Fin 8 := ![0, 0, 1]
def sharpEightLineB : Fin 3 → Fin 8 := ![1, 4, 6]

theorem sharpEightLineA_mem (i : Fin 3) :
    sharpEightLineA i ∈ sharpEightLineSupport i := by
  fin_cases i <;> decide

theorem sharpEightLineB_mem (i : Fin 3) :
    sharpEightLineB i ∈ sharpEightLineSupport i := by
  fin_cases i <;> decide

theorem sharpEightLineAB_ne (i : Fin 3) :
    sharpEightLineA i ≠ sharpEightLineB i := by
  fin_cases i <;> decide

theorem sharpEightLineSupport_collinear (i : Fin 3) :
    Collinear ℝ
      (supportPoints sharpEightConfiguration (sharpEightLineSupport i)) := by
  apply collinear_set_of_orientation_eq_zero
    (supportPoints sharpEightConfiguration (sharpEightLineSupport i))
    (sharpEightConfiguration (sharpEightLineA i))
    (sharpEightConfiguration (sharpEightLineB i))
  · exact ⟨sharpEightLineA i, sharpEightLineA_mem i, rfl⟩
  · exact sharpEightConfiguration.injective.ne (sharpEightLineAB_ne i)
  · intro p hp
    rcases hp with ⟨j, hj, rfl⟩
    fin_cases i <;> fin_cases j <;>
      simp_all [orientation, sharpEightConfiguration, sharpEightPoint,
        sharpEightX, sharpEightY, sharpEightLineA, sharpEightLineB,
        sharpEightLineSupport]
    all_goals norm_num

theorem sharpEight_all_triples_covered
    (t : Finset (Fin 8)) (ht : t.card = 3) :
    (∃ i : Fin 17, t ⊆ sharpEightCircleSupport i) ∨
      (∃ i : Fin 3, t ⊆ sharpEightLineSupport i) := by
  revert t
  decide

theorem sharpEight_noncollinear_triples_covered
    (t : Finset (Fin 8)) (ht : t.card = 3)
    (hnon : IsNoncollinear sharpEightConfiguration t) :
    ∃ i : Fin 17, t ⊆ sharpEightCircleSupport i :=
  noncollinear_covered_of_circle_or_line sharpEightConfiguration
    sharpEightCircleSupport sharpEightLineSupport
    sharpEightLineSupport_collinear sharpEight_all_triples_covered t ht hnon

theorem sharpEightCircleSupport_card_ge_three (i : Fin 17) :
    3 ≤ (sharpEightCircleSupport i).card := by
  fin_cases i <;> decide

theorem sharpEightCircleSupport_card_lt_eight (i : Fin 17) :
    (sharpEightCircleSupport i).card < 8 := by
  fin_cases i <;> decide

theorem sharpEightCircleSupport_injective :
    Function.Injective sharpEightCircleSupport := by
  decide

theorem sharpEight_noncollinear : Noncollinear sharpEightConfiguration := by
  intro hcol
  let T : Set Point2 :=
    {sharpEightPoint 0, sharpEightPoint 1, sharpEightPoint 4}
  have hsub : T ⊆ pointSet sharpEightConfiguration := by
    intro p hp
    simp only [T, Set.mem_insert_iff, Set.mem_singleton_iff] at hp
    rcases hp with rfl | rfl | rfl <;> exact ⟨_, rfl⟩
  have hpGlobal : sharpEightPoint 0 ∈ pointSet sharpEightConfiguration := ⟨0, rfl⟩
  rw [collinear_iff_of_mem hpGlobal] at hcol
  obtain ⟨v, hv⟩ := hcol
  have hpT : sharpEightPoint 0 ∈ T := by simp [T]
  have htriple : Collinear ℝ T := by
    rw [collinear_iff_of_mem hpT]
    exact ⟨v, fun p hp => hv p (hsub hp)⟩
  exact (not_collinear_of_orientation_ne_zero _ _ _ (by
    simp [orientation, sharpEightPoint, sharpEightX, sharpEightY])) htriple

theorem sharpEight_admissible : Admissible sharpEightConfiguration :=
  admissible_of_finite_certificate sharpEightConfiguration sharpEightCircle
    sharpEightCircleSupport sharpEight_circleTrace
    sharpEightCircleSupport_card_ge_three sharpEight_noncollinear_triples_covered
    (by norm_num) sharpEight_noncollinear sharpEightCircleSupport_card_lt_eight

theorem sharpEight_circleCount :
    circleCount sharpEightConfiguration = 17 :=
  circleCount_eq_listed_card sharpEightConfiguration sharpEightCircle
    sharpEightCircleSupport sharpEight_circleTrace
    sharpEightCircleSupport_card_ge_three sharpEight_noncollinear_triples_covered
    sharpEightCircleSupport_injective

end Erdos506.V1
