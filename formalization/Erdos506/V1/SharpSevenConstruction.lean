import Erdos506.V1.FiniteConstructionCertificate
import Erdos506.V3.EquationCircle

/-! # The sharp seven-point V1 construction -/

namespace Erdos506.V1

open Erdos506.V3 Erdos506.V4

set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

noncomputable def sharpSevenU : ℝ := Real.sqrt 3

theorem sharpSevenU_pos : 0 < sharpSevenU := by
  rw [sharpSevenU]
  positivity

theorem sharpSevenU_sq : sharpSevenU ^ 2 = 3 := by
  norm_num [sharpSevenU]

noncomputable def sharpSevenX : Fin 7 → ℝ :=
  ![-1, 1, 0, 0, -1 / 2, 1 / 2, 0]

noncomputable def sharpSevenY : Fin 7 → ℝ :=
  ![0, 0, sharpSevenU, 0, sharpSevenU / 2, sharpSevenU / 2,
    sharpSevenU / 3]

noncomputable def sharpSevenPoint (i : Fin 7) : Point2 :=
  pointOfCoords (sharpSevenX i) (sharpSevenY i)

theorem sharpSevenPoint_injective : Function.Injective sharpSevenPoint := by
  intro i j hij
  have hx := congrArg (fun p : Point2 => p (0 : Fin 2)) hij
  have hy := congrArg (fun p : Point2 => p (1 : Fin 2)) hij
  have hu := sharpSevenU_pos
  fin_cases i <;> fin_cases j <;>
    norm_num [sharpSevenPoint, sharpSevenX, sharpSevenY] at * <;> linarith

noncomputable def sharpSevenConfiguration : Configuration (Fin 7) :=
  ⟨sharpSevenPoint, sharpSevenPoint_injective⟩

def sharpSevenCircleSupport : Fin 11 → Finset (Fin 7) :=
  ![
    {0, 1, 4, 5}, {0, 2, 3, 5}, {0, 3, 4, 6},
    {1, 2, 3, 4}, {1, 3, 5, 6}, {2, 4, 5, 6},
    {0, 1, 2}, {0, 1, 6}, {0, 2, 6}, {1, 2, 6}, {3, 4, 5}
  ]

noncomputable def sharpSevenD : Fin 11 → ℝ :=
  ![0, 1, 1, -1, -1, 0, 0, 0, 2, -2, 0]

noncomputable def sharpSevenE : Fin 11 → ℝ :=
  ![0, -sharpSevenU, -sharpSevenU / 3, -sharpSevenU,
    -sharpSevenU / 3, -4 * sharpSevenU / 3,
    -2 * sharpSevenU / 3, 2 * sharpSevenU / 3,
    -4 * sharpSevenU / 3, -4 * sharpSevenU / 3,
    -2 * sharpSevenU / 3]

noncomputable def sharpSevenF : Fin 11 → ℝ :=
  ![-1, 0, 0, 0, 0, 1, -1, -1, 1, 1, 0]

theorem sharpSeven_radiusSq_pos (i : Fin 11) :
    0 < equationCircleRadiusSq (sharpSevenD i) (sharpSevenE i)
      (sharpSevenF i) := by
  have hu2 := sharpSevenU_sq
  fin_cases i <;>
    norm_num [equationCircleRadiusSq, sharpSevenD, sharpSevenE,
      sharpSevenF] at * <;> nlinarith

noncomputable def sharpSevenCircle (i : Fin 11) : ProperCircle :=
  properCircleOfEquation (sharpSevenD i) (sharpSevenE i) (sharpSevenF i)
    (sharpSeven_radiusSq_pos i)

theorem sharpSevenPoint_mem_circle_iff (i : Fin 11) (j : Fin 7) :
    sharpSevenPoint j ∈ ((sharpSevenCircle i).1 : Set Point2) ↔
      j ∈ sharpSevenCircleSupport i := by
  rw [sharpSevenCircle, mem_properCircleOfEquation_iff]
  have hu2 := sharpSevenU_sq
  have hu := sharpSevenU_pos
  fin_cases i <;> fin_cases j
  all_goals
    simp [circleEquation, sharpSevenPoint, sharpSevenX, sharpSevenY,
      sharpSevenD, sharpSevenE, sharpSevenF, sharpSevenCircleSupport]
  all_goals nlinarith

theorem sharpSeven_circleTrace (i : Fin 11) :
    circleTrace sharpSevenConfiguration (sharpSevenCircle i) =
      sharpSevenCircleSupport i := by
  ext j
  rw [mem_circleTrace]
  exact sharpSevenPoint_mem_circle_iff i j

def sharpSevenLineSupport : Fin 6 → Finset (Fin 7) :=
  ![{0, 1, 3}, {0, 2, 4}, {0, 5, 6}, {1, 2, 5}, {1, 4, 6}, {2, 3, 6}]

def sharpSevenLineA : Fin 6 → Fin 7 := ![0, 0, 0, 1, 1, 2]
def sharpSevenLineB : Fin 6 → Fin 7 := ![1, 2, 5, 2, 4, 3]

theorem sharpSevenLineA_mem (i : Fin 6) :
    sharpSevenLineA i ∈ sharpSevenLineSupport i := by
  fin_cases i <;> decide

theorem sharpSevenLineB_mem (i : Fin 6) :
    sharpSevenLineB i ∈ sharpSevenLineSupport i := by
  fin_cases i <;> decide

theorem sharpSevenLineAB_ne (i : Fin 6) :
    sharpSevenLineA i ≠ sharpSevenLineB i := by
  fin_cases i <;> decide

theorem sharpSevenLineSupport_collinear (i : Fin 6) :
    Collinear ℝ
      (supportPoints sharpSevenConfiguration (sharpSevenLineSupport i)) := by
  apply collinear_set_of_orientation_eq_zero
    (supportPoints sharpSevenConfiguration (sharpSevenLineSupport i))
    (sharpSevenConfiguration (sharpSevenLineA i))
    (sharpSevenConfiguration (sharpSevenLineB i))
  · exact ⟨sharpSevenLineA i, sharpSevenLineA_mem i, rfl⟩
  · exact sharpSevenConfiguration.injective.ne (sharpSevenLineAB_ne i)
  · intro p hp
    rcases hp with ⟨j, hj, rfl⟩
    have hu2 := sharpSevenU_sq
    fin_cases i <;> fin_cases j <;>
      simp_all [orientation, sharpSevenConfiguration, sharpSevenPoint,
        sharpSevenX, sharpSevenY, sharpSevenLineA, sharpSevenLineB,
        sharpSevenLineSupport]
    all_goals nlinarith

theorem sharpSeven_all_triples_covered
    (t : Finset (Fin 7)) (ht : t.card = 3) :
    (∃ i : Fin 11, t ⊆ sharpSevenCircleSupport i) ∨
      (∃ i : Fin 6, t ⊆ sharpSevenLineSupport i) := by
  revert t
  decide

theorem sharpSeven_noncollinear_triples_covered
    (t : Finset (Fin 7)) (ht : t.card = 3)
    (hnon : IsNoncollinear sharpSevenConfiguration t) :
    ∃ i : Fin 11, t ⊆ sharpSevenCircleSupport i :=
  noncollinear_covered_of_circle_or_line sharpSevenConfiguration
    sharpSevenCircleSupport sharpSevenLineSupport
    sharpSevenLineSupport_collinear sharpSeven_all_triples_covered t ht hnon

theorem sharpSevenCircleSupport_card_ge_three (i : Fin 11) :
    3 ≤ (sharpSevenCircleSupport i).card := by
  fin_cases i <;> decide

theorem sharpSevenCircleSupport_card_lt_seven (i : Fin 11) :
    (sharpSevenCircleSupport i).card < 7 := by
  fin_cases i <;> decide

theorem sharpSevenCircleSupport_injective :
    Function.Injective sharpSevenCircleSupport := by
  decide

theorem sharpSeven_noncollinear : Noncollinear sharpSevenConfiguration := by
  intro hcol
  let T : Set Point2 :=
    {sharpSevenPoint 0, sharpSevenPoint 1, sharpSevenPoint 2}
  have hsub : T ⊆ pointSet sharpSevenConfiguration := by
    intro p hp
    simp only [T, Set.mem_insert_iff, Set.mem_singleton_iff] at hp
    rcases hp with rfl | rfl | rfl <;> exact ⟨_, rfl⟩
  have hpGlobal : sharpSevenPoint 0 ∈ pointSet sharpSevenConfiguration := ⟨0, rfl⟩
  rw [collinear_iff_of_mem hpGlobal] at hcol
  obtain ⟨v, hv⟩ := hcol
  have hpT : sharpSevenPoint 0 ∈ T := by simp [T]
  have htriple : Collinear ℝ T := by
    rw [collinear_iff_of_mem hpT]
    exact ⟨v, fun p hp => hv p (hsub hp)⟩
  apply (not_collinear_of_orientation_ne_zero _ _ _ ?_) htriple
  have hu := sharpSevenU_pos
  simp [orientation, sharpSevenPoint, sharpSevenX, sharpSevenY]
  linarith

theorem sharpSeven_admissible : Admissible sharpSevenConfiguration :=
  admissible_of_finite_certificate sharpSevenConfiguration sharpSevenCircle
    sharpSevenCircleSupport sharpSeven_circleTrace
    sharpSevenCircleSupport_card_ge_three sharpSeven_noncollinear_triples_covered
    (by norm_num) sharpSeven_noncollinear sharpSevenCircleSupport_card_lt_seven

theorem sharpSeven_circleCount :
    circleCount sharpSevenConfiguration = 11 :=
  circleCount_eq_listed_card sharpSevenConfiguration sharpSevenCircle
    sharpSevenCircleSupport sharpSeven_circleTrace
    sharpSevenCircleSupport_card_ge_three sharpSeven_noncollinear_triples_covered
    sharpSevenCircleSupport_injective

end Erdos506.V1
