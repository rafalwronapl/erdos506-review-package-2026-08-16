import Erdos506.V3.EquationCircle
import Erdos506.V3.Routing

/-!
# The exceptional eight-point V3 construction

All coordinates and all twenty circle equations are rational.  The twelve
four-point supports and eight three-point supports are exactly the table in
the paper.  Geometry is checked through `circleEquation`; the separate
finite support table proves that every one of the 56 triples is covered.
-/

namespace Erdos506.V3

open Erdos506.V4

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

noncomputable def exceptionalEightX : Fin 8 → ℝ :=
  ![1 / 2, -1 / 2, 1 / 10, -1 / 10, 1 / 5, -1 / 5, 1 / 13, -1 / 13]

noncomputable def exceptionalEightY : Fin 8 → ℝ :=
  ![3 / 2, 3 / 2, 17 / 10, 17 / 10, 7 / 5, 7 / 5, 21 / 13, 21 / 13]

noncomputable def exceptionalEightPoint (i : Fin 8) : Point2 :=
  pointOfCoords (exceptionalEightX i) (exceptionalEightY i)

theorem exceptionalEightPoint_injective :
    Function.Injective exceptionalEightPoint := by
  intro i j hij
  have hx := congrArg (fun p : Point2 => p (0 : Fin 2)) hij
  fin_cases i <;> fin_cases j <;>
    norm_num [exceptionalEightPoint, exceptionalEightX] at *

noncomputable def exceptionalEightConfiguration : Configuration (Fin 8) :=
  ⟨exceptionalEightPoint, exceptionalEightPoint_injective⟩

theorem exceptionalEight_orientation_ne_zero
    {i j k : Fin 8} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    orientation (exceptionalEightPoint i) (exceptionalEightPoint j)
      (exceptionalEightPoint k) ≠ 0 := by
  fin_cases i <;> fin_cases j <;> fin_cases k <;>
    norm_num [orientation, exceptionalEightPoint, exceptionalEightX,
      exceptionalEightY] at *

theorem exceptionalEight_three_noncollinear
    {i j k : Fin 8} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    ¬Collinear ℝ
      ({exceptionalEightPoint i, exceptionalEightPoint j,
        exceptionalEightPoint k} : Set Point2) :=
  not_collinear_of_orientation_ne_zero _ _ _
    (exceptionalEight_orientation_ne_zero hij hik hjk)

theorem exceptionalEight_noThree :
    NoThreeCollinear exceptionalEightConfiguration := by
  intro t ht
  obtain ⟨i, j, k, hij, hik, hjk, rfl⟩ := Finset.card_eq_three.mp ht
  have hsupp :
      supportPoints exceptionalEightConfiguration ({i, j, k} : Finset (Fin 8)) =
        ({exceptionalEightPoint i, exceptionalEightPoint j,
          exceptionalEightPoint k} : Set Point2) := by
    ext p
    simp [supportPoints, exceptionalEightConfiguration, eq_comm]
  rw [IsNoncollinear, hsupp]
  exact exceptionalEight_three_noncollinear hij hik hjk

def exceptionalEightSupport : Fin 20 → Finset (Fin 8) :=
  ![
    {0, 1, 2, 3}, {0, 1, 4, 5}, {0, 1, 6, 7},
    {0, 2, 4, 6}, {0, 2, 5, 7}, {0, 3, 4, 7},
    {1, 2, 5, 6}, {1, 3, 4, 6}, {1, 3, 5, 7},
    {2, 3, 4, 5}, {2, 3, 6, 7}, {4, 5, 6, 7},
    {0, 3, 5}, {0, 3, 6}, {0, 5, 6}, {1, 2, 4},
    {1, 2, 7}, {1, 4, 7}, {2, 4, 7}, {3, 5, 6}
  ]

noncomputable def exceptionalEightA : Fin 20 → ℝ :=
  ![
    0, 0, 0, -3 / 5, -1 / 3, -1 / 2,
    1 / 2, 1 / 3, 3 / 5, 0, 0, 0,
    -3 / 10, -3 / 2, -3 / 8, 3 / 10,
    3 / 2, 3 / 8, -3 / 20, 3 / 20
  ]

noncomputable def exceptionalEightB : Fin 20 → ℝ :=
  ![
    -2, -5, -1, -16 / 5, -8 / 3, -7 / 2,
    -7 / 2, -8 / 3, -16 / 5, -3, -37 / 11, -20 / 7,
    -29 / 10, -13 / 2, -19 / 8, -29 / 10,
    -13 / 2, -19 / 8, -61 / 20, -61 / 20
  ]

noncomputable def exceptionalEightC : Fin 20 → ℝ :=
  ![
    1 / 2, 5, -1, 13 / 5, 5 / 3, 3,
    3, 5 / 3, 13 / 5, 11 / 5, 31 / 11, 2,
    2, 8, 5 / 4, 2, 8, 5 / 4, 23 / 10, 23 / 10
  ]

theorem exceptionalEight_radiusSq_pos (i : Fin 20) :
    0 < equationCircleRadiusSq (exceptionalEightA i)
      (exceptionalEightB i) (exceptionalEightC i) := by
  fin_cases i <;>
    norm_num [equationCircleRadiusSq, exceptionalEightA,
      exceptionalEightB, exceptionalEightC]

noncomputable def exceptionalEightCircle (i : Fin 20) : ProperCircle :=
  properCircleOfEquation (exceptionalEightA i) (exceptionalEightB i)
    (exceptionalEightC i) (exceptionalEight_radiusSq_pos i)

theorem exceptionalEightPoint_mem_circle_iff (i : Fin 20) (j : Fin 8) :
    exceptionalEightPoint j ∈ ((exceptionalEightCircle i).1 : Set Point2) ↔
      j ∈ exceptionalEightSupport i := by
  rw [exceptionalEightCircle, mem_properCircleOfEquation_iff]
  fin_cases i <;> fin_cases j
  all_goals
    norm_num [circleEquation, exceptionalEightPoint, exceptionalEightX,
      exceptionalEightY, exceptionalEightA, exceptionalEightB,
      exceptionalEightC, exceptionalEightSupport]
  all_goals decide

theorem exceptionalEight_circleTrace (i : Fin 20) :
    circleTrace exceptionalEightConfiguration (exceptionalEightCircle i) =
      exceptionalEightSupport i := by
  ext j
  rw [mem_circleTrace]
  exact exceptionalEightPoint_mem_circle_iff i j

theorem exceptionalEightSupport_card_ge_three (i : Fin 20) :
    3 ≤ (exceptionalEightSupport i).card := by
  fin_cases i <;> decide

theorem exceptionalEightSupport_card_lt_eight (i : Fin 20) :
    (exceptionalEightSupport i).card < 8 := by
  fin_cases i <;> decide

theorem exceptionalEightSupport_injective :
    Function.Injective exceptionalEightSupport := by
  decide

theorem exceptionalEightSupport_covers_triples
    (t : Finset (Fin 8)) (ht : t.card = 3) :
    ∃ i : Fin 20, t ⊆ exceptionalEightSupport i := by
  revert t
  decide

end Erdos506.V3
