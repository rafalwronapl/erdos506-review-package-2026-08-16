import Erdos506.V1.ElevenFiveC40FinalK31ActualDualEntrance

/-!
# Actual parameter-grid tail for the residual K3.1 path

This module turns the two actual three-label pencils extracted from the
ten-point `(t₄,t₃) = (3,6)` census into the literal parameterized affine
`3×3` grid consumed by the real determinant endpoint.
-/

namespace Erdos506.V1

open Matrix
open Erdos506.Block
open Erdos506.Block.BlockSystem
open Erdos506.Incidence
open Erdos506.V3
open Erdos506.V4

universe u v

/-! ### Anchored affine levels -/

/-- The first framed left covector has affine level `-1`. -/
theorem three_four_path_dualAffine_column_coordinate_frame_zero
    {ell : Fin 4 → Homogeneous3} (F : ProjectiveCovectorFrame ell) :
    threeFourPathDualAffineColumnCoordinate
      (threeFourPathDualAffineCovector F (ell 0)) = -1 := by
  unfold threeFourPathDualAffineColumnCoordinate
  rw [three_four_path_dualAffineCovector_frame F 0]
  simp [twelveGridAffineFrameCovector, twelveGridAffineFrameScale,
    F.scale_ne_zero 0]

/-- The second framed left covector has affine level `0`. -/
theorem three_four_path_dualAffine_column_coordinate_frame_one
    {ell : Fin 4 → Homogeneous3} (F : ProjectiveCovectorFrame ell) :
    threeFourPathDualAffineColumnCoordinate
      (threeFourPathDualAffineCovector F (ell 1)) = 0 := by
  unfold threeFourPathDualAffineColumnCoordinate
  rw [three_four_path_dualAffineCovector_frame F 1]
  simp [twelveGridAffineFrameCovector, twelveGridAffineFrameScale]

/-- The first framed right covector has affine level `-1`. -/
theorem three_four_path_dualAffine_row_coordinate_frame_zero
    {ell : Fin 4 → Homogeneous3} (F : ProjectiveCovectorFrame ell) :
    threeFourPathDualAffineRowCoordinate
      (threeFourPathDualAffineCovector F (ell 2)) = -1 := by
  unfold threeFourPathDualAffineRowCoordinate
  rw [three_four_path_dualAffineCovector_frame F 2]
  simp [twelveGridAffineFrameCovector, twelveGridAffineFrameScale,
    F.scale_ne_zero 2]

/-- The second framed right covector has affine level `0`. -/
theorem three_four_path_dualAffine_row_coordinate_frame_one
    {ell : Fin 4 → Homogeneous3} (F : ProjectiveCovectorFrame ell) :
    threeFourPathDualAffineRowCoordinate
      (threeFourPathDualAffineCovector F (ell 3)) = 0 := by
  unfold threeFourPathDualAffineRowCoordinate
  rw [three_four_path_dualAffineCovector_frame F 3]
  simp [twelveGridAffineFrameCovector, twelveGridAffineFrameScale]

/-- Every actual left-pencil label has the standard parameterized column
level after the first two labels anchor the affine scale. -/
theorem three_four_path_actual_dualAffine_left_coordinate_eq_parameter
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    (cfg : Configuration Point) (left right : Fin 3 → Point)
    (F : ProjectiveCovectorFrame
      (threeFourPathActualDualFrameCovector cfg left right)) (i : Fin 3) :
    threeFourPathDualAffineColumnCoordinate
      (threeFourPathDualAffineCovector F (homogeneousLift (cfg (left i)))) =
      threeByThreePencilCoordinate
        (threeFourPathDualAffineColumnCoordinate
          (threeFourPathDualAffineCovector F
            (homogeneousLift (cfg (left 2))))) i := by
  fin_cases i
  · simpa [threeFourPathActualDualFrameCovector, threeByThreePencilCoordinate] using
      (three_four_path_dualAffine_column_coordinate_frame_zero F)
  · simpa [threeFourPathActualDualFrameCovector, threeByThreePencilCoordinate] using
      (three_four_path_dualAffine_column_coordinate_frame_one F)
  · simp [threeByThreePencilCoordinate]

/-- Every actual right-pencil label has the standard parameterized row
level after the first two labels anchor the affine scale. -/
theorem three_four_path_actual_dualAffine_right_coordinate_eq_parameter
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    (cfg : Configuration Point) (left right : Fin 3 → Point)
    (F : ProjectiveCovectorFrame
      (threeFourPathActualDualFrameCovector cfg left right)) (i : Fin 3) :
    threeFourPathDualAffineRowCoordinate
      (threeFourPathDualAffineCovector F (homogeneousLift (cfg (right i)))) =
      threeByThreePencilCoordinate
        (threeFourPathDualAffineRowCoordinate
          (threeFourPathDualAffineCovector F
            (homogeneousLift (cfg (right 2))))) i := by
  fin_cases i
  · simpa [threeFourPathActualDualFrameCovector, threeByThreePencilCoordinate] using
      (three_four_path_dualAffine_row_coordinate_frame_zero F)
  · simpa [threeFourPathActualDualFrameCovector, threeByThreePencilCoordinate] using
      (three_four_path_dualAffine_row_coordinate_frame_one F)
  · simp [threeByThreePencilCoordinate]

/-! ### All nine actual crossings -/

/-- A left label has a nonzero vertical-level coefficient in the actual
dual frame. -/
theorem three_four_path_actual_dualAffine_left_apply_zero_ne
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    (cfg : Configuration Point) (a b : LineBlock (blockSystem cfg))
    (hab : Disjoint ((blockSystem cfg).support a.1)
      ((blockSystem cfg).support b.1))
    (left right : Fin 3 → Point)
    (hleft : ∀ i, left i ∈ (blockSystem cfg).support a.1)
    (hright : ∀ i, right i ∈ (blockSystem cfg).support b.1)
    (hleftInj : Function.Injective left)
    (hrightInj : Function.Injective right)
    (F : ProjectiveCovectorFrame (threeFourPathActualDualFrameCovector cfg left right))
    (i : Fin 3) :
    threeFourPathDualAffineCovector F (homogeneousLift (cfg (left i))) 0 ≠ 0 := by
  exact three_four_path_dualAffine_left_pencil_apply_zero_ne F _
    (three_four_path_actual_left_not_right_pencil_cross
      cfg a b hab left right hleft hright hrightInj i)
    (three_four_path_actual_dual_cross_ne_zero cfg
      (by intro h; exact Fin.zero_ne_one (hrightInj h)))

/-- A right label has a nonzero horizontal-level coefficient in the actual
dual frame. -/
theorem three_four_path_actual_dualAffine_right_apply_one_ne
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    (cfg : Configuration Point) (a b : LineBlock (blockSystem cfg))
    (hab : Disjoint ((blockSystem cfg).support a.1)
      ((blockSystem cfg).support b.1))
    (left right : Fin 3 → Point)
    (hleft : ∀ i, left i ∈ (blockSystem cfg).support a.1)
    (hright : ∀ i, right i ∈ (blockSystem cfg).support b.1)
    (hleftInj : Function.Injective left)
    (hrightInj : Function.Injective right)
    (F : ProjectiveCovectorFrame (threeFourPathActualDualFrameCovector cfg left right))
    (i : Fin 3) :
    threeFourPathDualAffineCovector F (homogeneousLift (cfg (right i))) 1 ≠ 0 := by
  exact three_four_path_dualAffine_right_pencil_apply_one_ne F _
    (three_four_path_actual_right_not_left_pencil_cross
      cfg a b hab left right hleft hright hleftInj i)
    (three_four_path_actual_dual_cross_ne_zero cfg
      (by intro h; exact Fin.zero_ne_one (hleftInj h)))

/-- Any actual left/right cell has a nonzero raw dual crossing. -/
theorem three_four_path_actual_dual_cross_ne_zero_of_disjoint_support
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    (cfg : Configuration Point) (a b : LineBlock (blockSystem cfg))
    (hab : Disjoint ((blockSystem cfg).support a.1)
      ((blockSystem cfg).support b.1))
    (left right : Fin 3 → Point)
    (hleft : ∀ i, left i ∈ (blockSystem cfg).support a.1)
    (hright : ∀ i, right i ∈ (blockSystem cfg).support b.1)
    (i j : Fin 3) :
    crossProduct (homogeneousLift (cfg (left i)))
      (homogeneousLift (cfg (right j))) ≠ 0 := by
  apply three_four_path_actual_dual_cross_ne_zero cfg
  intro hij
  have hrightInA : right j ∈ (blockSystem cfg).support a.1 := hij ▸ hleft i
  exact Finset.disjoint_left.mp hab hrightInA (hright j)

/-- The literal affine coordinate of every actual left/right crossing is
the corresponding point of the parameterized `3×3` grid. -/
theorem three_four_path_actual_dualAffine_grid_coordinate_parameterized
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    (cfg : Configuration Point) (a b : LineBlock (blockSystem cfg))
    (hab : Disjoint ((blockSystem cfg).support a.1)
      ((blockSystem cfg).support b.1))
    (left right : Fin 3 → Point)
    (hleft : ∀ i, left i ∈ (blockSystem cfg).support a.1)
    (hright : ∀ i, right i ∈ (blockSystem cfg).support b.1)
    (hleftInj : Function.Injective left)
    (hrightInj : Function.Injective right)
    (F : ProjectiveCovectorFrame (threeFourPathActualDualFrameCovector cfg left right))
    (i j : Fin 3) :
    threeFourPathDualAffineGridCoordinate F
      (homogeneousLift (cfg (left i))) (homogeneousLift (cfg (right j))) =
      threeByThreeParameterizedGridPoint
        (threeFourPathDualAffineColumnCoordinate
          (threeFourPathDualAffineCovector F (homogeneousLift (cfg (left 2)))))
        (threeFourPathDualAffineRowCoordinate
          (threeFourPathDualAffineCovector F (homogeneousLift (cfg (right 2)))))
        (i, j) := by
  calc
    threeFourPathDualAffineGridCoordinate F
        (homogeneousLift (cfg (left i))) (homogeneousLift (cfg (right j))) =
        (threeFourPathDualAffineColumnCoordinate
          (threeFourPathDualAffineCovector F (homogeneousLift (cfg (left i)))),
          threeFourPathDualAffineRowCoordinate
            (threeFourPathDualAffineCovector F
              (homogeneousLift (cfg (right j))))) :=
      three_four_path_dualAffineGridCoordinate_of_normal_forms F _ _ _ _
        (three_four_path_actual_dualAffine_left_normal_form
          cfg a b hab left right hleft hright hleftInj hrightInj F i)
        (three_four_path_actual_dualAffine_right_normal_form
          cfg a b hab left right hleft hright hleftInj hrightInj F j)
        (three_four_path_actual_dualAffine_left_apply_zero_ne
          cfg a b hab left right hleft hright hleftInj hrightInj F i)
        (three_four_path_actual_dualAffine_right_apply_one_ne
          cfg a b hab left right hleft hright hleftInj hrightInj F j)
        (three_four_path_actual_dual_cross_ne_zero_of_disjoint_support
          cfg a b hab left right hleft hright i j)
    _ = threeByThreeParameterizedGridPoint
        (threeFourPathDualAffineColumnCoordinate
          (threeFourPathDualAffineCovector F (homogeneousLift (cfg (left 2)))))
        (threeFourPathDualAffineRowCoordinate
          (threeFourPathDualAffineCovector F (homogeneousLift (cfg (right 2)))))
        (i, j) := by
      simp only [threeByThreeParameterizedGridPoint]
      rw [three_four_path_actual_dualAffine_left_coordinate_eq_parameter,
        three_four_path_actual_dualAffine_right_coordinate_eq_parameter]

/-- Every actual left/right crossing is finite in the affine post-chart. -/
theorem three_four_path_actual_dualAffine_grid_point_apply_two_ne
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    (cfg : Configuration Point) (a b : LineBlock (blockSystem cfg))
    (hab : Disjoint ((blockSystem cfg).support a.1)
      ((blockSystem cfg).support b.1))
    (left right : Fin 3 → Point)
    (hleft : ∀ i, left i ∈ (blockSystem cfg).support a.1)
    (hright : ∀ i, right i ∈ (blockSystem cfg).support b.1)
    (hleftInj : Function.Injective left)
    (hrightInj : Function.Injective right)
    (F : ProjectiveCovectorFrame (threeFourPathActualDualFrameCovector cfg left right))
    (i j : Fin 3) :
    threeFourPathDualAffineGridPoint F
      (homogeneousLift (cfg (left i))) (homogeneousLift (cfg (right j))) 2 ≠ 0 := by
  exact three_four_path_dualAffineGridPoint_apply_two_ne_of_normal_forms F _ _ _ _
    (three_four_path_actual_dualAffine_left_normal_form
      cfg a b hab left right hleft hright hleftInj hrightInj F i)
    (three_four_path_actual_dualAffine_right_normal_form
      cfg a b hab left right hleft hright hleftInj hrightInj F j)
    (three_four_path_actual_dualAffine_left_apply_zero_ne
      cfg a b hab left right hleft hright hleftInj hrightInj F i)
    (three_four_path_actual_dualAffine_right_apply_one_ne
      cfg a b hab left right hleft hright hleftInj hrightInj F j)
    (three_four_path_actual_dual_cross_ne_zero_of_disjoint_support
      cfg a b hab left right hleft hright i j)

/-- The actual six-three-line `3,2,3` path cannot occur over the real
affine plane.  Its two middle fibres give the diagonal and one derangement
of one parameterized `3×3` grid, which is exactly the determinant endpoint
already proved in the real tail. -/
theorem three_four_path_six_actual_dual_grid_impossible
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    (cfg : Configuration Point) (hcard : Fintype.card Point = 10)
    (a b c : LineBlock (blockSystem cfg))
    (ha : ((blockSystem cfg).support a.1).card = 4)
    (hb : ((blockSystem cfg).support b.1).card = 4)
    (hc : ((blockSystem cfg).support c.1).card = 4)
    (hab : Disjoint ((blockSystem cfg).support a.1)
      ((blockSystem cfg).support b.1))
    (hca : ((blockSystem cfg).support c.1 ∩
      (blockSystem cfg).support a.1).card = 1)
    (hcb : ((blockSystem cfg).support c.1 ∩
      (blockSystem cfg).support b.1).card = 1)
    (hthree : (blockSystem cfg).lineCount 3 = 6) : False := by
  classical
  obtain ⟨m, n, hmn, hmiddle, hFm, hFn⟩ :=
    three_four_path_exists_two_middle_fibres_card_three
      (blockSystem cfg) hcard a b c ha hb hc hab hca hcb hthree
  have hm : m ∈ threeFourPathMiddlePrivate (blockSystem cfg) a b c := by
    rw [hmiddle]
    simp
  have hn : n ∈ threeFourPathMiddlePrivate (blockSystem cfg) a b c := by
    rw [hmiddle]
    simp
  let M := threeFourPathMiddleFibreMatching
    (blockSystem cfg) hcard a b c ha hb hc hab hca hcb hthree m hm hFm
  let left : Fin 3 → Point := fun i =>
    threeFourPathLeftPrivateLabel (blockSystem cfg) a b c ha hb hc hab hca hcb
      (M.symm i)
  let right : Fin 3 → Point := fun i =>
    threeFourPathRightPrivateLabel (blockSystem cfg) a b c ha hb hc hab hca hcb i
  have hleft : ∀ i, left i ∈ (blockSystem cfg).support a.1 := by
    intro i
    dsimp [left]
    exact three_four_path_leftPrivateLabel_mem
      (blockSystem cfg) a b c ha hb hc hab hca hcb (M.symm i)
  have hright : ∀ i, right i ∈ (blockSystem cfg).support b.1 := by
    intro i
    dsimp [right]
    exact three_four_path_rightPrivateLabel_mem
      (blockSystem cfg) a b c ha hb hc hab hca hcb i
  have hleftInj : Function.Injective left := by
    intro i j hij
    apply M.symm.injective
    apply three_four_path_leftPrivateLabel_injective
      (blockSystem cfg) a b c ha hb hc hab hca hcb
    simpa [left] using hij
  have hrightInj : Function.Injective right := by
    intro i j hij
    apply three_four_path_rightPrivateLabel_injective
      (blockSystem cfg) a b c ha hb hc hab hca hcb
    simpa [right] using hij
  let F := threeFourPathActualDualCovectorFrame
    cfg a b hab left right hleft hright hleftInj hrightInj
  let A : ℝ := threeFourPathDualAffineColumnCoordinate
    (threeFourPathDualAffineCovector F (homogeneousLift (cfg (left 2))))
  let B : ℝ := threeFourPathDualAffineRowCoordinate
    (threeFourPathDualAffineCovector F (homogeneousLift (cfg (right 2))))
  have hcoordinate : ∀ i j : Fin 3,
      threeFourPathDualAffineGridCoordinate F
        (homogeneousLift (cfg (left i))) (homogeneousLift (cfg (right j))) =
        threeByThreeParameterizedGridPoint A B (i, j) := by
    intro i j
    simpa [A, B] using
      (three_four_path_actual_dualAffine_grid_coordinate_parameterized
        cfg a b hab left right hleft hright hleftInj hrightInj F i j)
  have hfinite : ∀ i j : Fin 3,
      threeFourPathDualAffineGridPoint F
        (homogeneousLift (cfg (left i))) (homogeneousLift (cfg (right j))) 2 ≠ 0 := by
    intro i j
    exact three_four_path_actual_dualAffine_grid_point_apply_two_ne
      cfg a b hab left right hleft hright hleftInj hrightInj F i j
  have hdiagonal : ∀ i : Fin 3,
      homogeneousLift (cfg m) ⬝ᵥ
        crossProduct (homogeneousLift (cfg (left i)))
          (homogeneousLift (cfg (right i))) = 0 := by
    intro i
    simpa only [left, right, M] using
      (three_four_path_actual_first_matching_diagonal_cross_incident
        cfg hcard a b c ha hb hc hab hca hcb hthree m hm hFm i)
  have hdiagArea := three_four_path_dualAffineGridArea_eq_zero_of_common_covector
    F (homogeneousLift (cfg m))
    (homogeneousLift (cfg (left 0))) (homogeneousLift (cfg (right 0)))
    (homogeneousLift (cfg (left 1))) (homogeneousLift (cfg (right 1)))
    (homogeneousLift (cfg (left 2))) (homogeneousLift (cfg (right 2)))
    (homogeneousLift_ne_zero _) (hdiagonal 0) (hdiagonal 1) (hdiagonal 2)
    (hfinite 0 0) (hfinite 1 1) (hfinite 2 2)
  rw [hcoordinate 0 0, hcoordinate 1 1, hcoordinate 2 2] at hdiagArea
  have hdiag : ParameterizedThreeByThreeGridTransversal A B 0 := by
    simpa [ParameterizedThreeByThreeGridTransversal,
      parameterizedThreeByThreeTransversalDeterminant,
      parameterizedThreeByThreeTransversalPermutation,
      parameterizedThreeByThreeGridArea] using hdiagArea
  have hdiagPoly : B - A = 0 := by
    rw [ParameterizedThreeByThreeGridTransversal,
      parameterizedThreeByThreeTransversal_determinant_eq_polynomial] at hdiag
    simpa [parameterizedThreeByThreeTransversalPolynomial] using hdiag
  have hBA : B = A := by linarith
  let σ := threeFourPathTwoMiddleFibreRelativeMatching
    (blockSystem cfg) hcard a b c ha hb hc hab hca hcb hthree m n hm hn hFm hFn
  have hrelative : ∀ i : Fin 3,
      homogeneousLift (cfg n) ⬝ᵥ
        crossProduct (homogeneousLift (cfg (left i)))
          (homogeneousLift (cfg (right (σ i)))) = 0 := by
    intro i
    simpa only [left, right, M, σ] using
      (three_four_path_actual_second_matching_relative_cross_incident
        cfg hcard a b c ha hb hc hab hca hcb hthree m n hm hn hFm hFn i)
  rcases three_four_path_two_middle_fibre_relative_matching_code_three_or_four
      (blockSystem cfg) hcard a b c ha hb hc hab hca hcb hthree m n hmn hm hn hFm hFn
    with hcode | hcode
  · have harea := three_four_path_dualAffineGridArea_eq_zero_of_common_covector
      F (homogeneousLift (cfg n))
      (homogeneousLift (cfg (left 0))) (homogeneousLift (cfg (right (σ 0))))
      (homogeneousLift (cfg (left 1))) (homogeneousLift (cfg (right (σ 1))))
      (homogeneousLift (cfg (left 2))) (homogeneousLift (cfg (right (σ 2))))
      (homogeneousLift_ne_zero _) (hrelative 0) (hrelative 1) (hrelative 2)
      (hfinite 0 (σ 0)) (hfinite 1 (σ 1)) (hfinite 2 (σ 2))
    rw [hcoordinate 0 (σ 0), hcoordinate 1 (σ 1), hcoordinate 2 (σ 2)] at harea
    have hσ0 : σ 0 = 1 := by
      simpa [σ] using hcode 0
    have hσ1 : σ 1 = 2 := by
      simpa [σ] using hcode 1
    have hσ2 : σ 2 = 0 := by
      simpa [σ] using hcode 2
    rw [hσ0, hσ1, hσ2] at harea
    have hthreeCode : ParameterizedThreeByThreeGridTransversal A B 3 := by
      simpa [ParameterizedThreeByThreeGridTransversal,
        parameterizedThreeByThreeTransversalDeterminant,
        parameterizedThreeByThreeTransversalPermutation,
        parameterizedThreeByThreeGridArea] using harea
    exact parameterized_threeByThreeGrid_diagonal_no_disjoint_transversal
      (Or.inl (by simpa [hBA] using hthreeCode))
  · have harea := three_four_path_dualAffineGridArea_eq_zero_of_common_covector
      F (homogeneousLift (cfg n))
      (homogeneousLift (cfg (left 0))) (homogeneousLift (cfg (right (σ 0))))
      (homogeneousLift (cfg (left 1))) (homogeneousLift (cfg (right (σ 1))))
      (homogeneousLift (cfg (left 2))) (homogeneousLift (cfg (right (σ 2))))
      (homogeneousLift_ne_zero _) (hrelative 0) (hrelative 1) (hrelative 2)
      (hfinite 0 (σ 0)) (hfinite 1 (σ 1)) (hfinite 2 (σ 2))
    rw [hcoordinate 0 (σ 0), hcoordinate 1 (σ 1), hcoordinate 2 (σ 2)] at harea
    have hσ0 : σ 0 = 2 := by
      simpa [σ] using hcode 0
    have hσ1 : σ 1 = 0 := by
      simpa [σ] using hcode 1
    have hσ2 : σ 2 = 1 := by
      simpa [σ] using hcode 2
    rw [hσ0, hσ1, hσ2] at harea
    have hfourCode : ParameterizedThreeByThreeGridTransversal A B 4 := by
      simpa [ParameterizedThreeByThreeGridTransversal,
        parameterizedThreeByThreeTransversalDeterminant,
        parameterizedThreeByThreeTransversalPermutation,
        parameterizedThreeByThreeGridArea] using harea
    exact parameterized_threeByThreeGrid_diagonal_no_disjoint_transversal
      (Or.inr (by simpa [hBA] using hfourCode))

/-- The remaining K3.1 singleton carrier `(d₃,d₅) = (9,3)` is impossible.
After pivot inversion it is exactly the ten-point actual `3,2,3` path
eliminated by `three_four_path_six_actual_dual_grid_impossible`. -/
theorem elevenFive_threeFive_nine_singleton_impossible
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    (cfg : Configuration Point) (hcard : Fintype.card Point = 11)
    (p : Point) (hlocal : ElevenFiveLocalRows (blockSystem cfg) p)
    (hthree : (blockSystem cfg).blockDegree 3 p = 9)
    (hfive : (blockSystem cfg).blockDegree 5 p = 3)
    {b d : GeometricBlock cfg}
    (hb : b ∈ (blockSystem cfg).blocksOfSize 5)
    (hd : d ∈ (blockSystem cfg).blocksOfSize 5)
    (hbp : p ∈ geometricBlockSupport cfg b)
    (hdp : p ∈ geometricBlockSupport cfg d) (hbd : b ≠ d)
    (hinter : (geometricBlockSupport cfg b ∩
      geometricBlockSupport cfg d).card = 1) : False := by
  let Q := pivotInversion cfg p
  let B := elevenFiveFivePivotBlock cfg p b hb hbp
  let D := elevenFiveFivePivotBlock cfg p d hd hdp
  let A := elevenFiveFivePivotLineOfSize cfg p b hb hbp
  let C := elevenFiveFivePivotLineOfSize cfg p d hd hdp
  let a : (blockSystem Q).LineBlock := ⟨.inl A.1, rfl⟩
  let d' : (blockSystem Q).LineBlock := ⟨.inl C.1, rfl⟩
  have ha : ((blockSystem Q).support a.1).card = 4 := by
    change (lineSupport Q A.1).card = 4
    exact A.2
  have hd' : ((blockSystem Q).support d'.1).card = 4 := by
    change (lineSupport Q C.1).card = 4
    exact C.2
  have hA : lineSupport Q A.1 = awaySupport p (geometricBlockSupport cfg b) := by
    change lineSupport (pivotInversion cfg p) (blockToPivotLine cfg p B) = _
    exact lineSupport_blockToPivotLine cfg p B
  have hC : lineSupport Q C.1 = awaySupport p (geometricBlockSupport cfg d) := by
    change lineSupport (pivotInversion cfg p) (blockToPivotLine cfg p D) = _
    exact lineSupport_blockToPivotLine cfg p D
  have hpinter : p ∈ geometricBlockSupport cfg b ∩ geometricBlockSupport cfg d :=
    Finset.mem_inter.mpr ⟨hbp, hdp⟩
  have hawayZero :
      (awaySupport p (geometricBlockSupport cfg b ∩
        geometricBlockSupport cfg d)).card = 0 := by
    rw [card_awaySupport p _ hpinter, hinter]
  have hzero :
      (awaySupport p (geometricBlockSupport cfg b) ∩
        awaySupport p (geometricBlockSupport cfg d)).card = 0 := by
    rw [awaySupport_inter, hawayZero]
  have hab : Disjoint ((blockSystem Q).support a.1)
      ((blockSystem Q).support d'.1) := by
    rw [Finset.disjoint_iff_inter_eq_empty]
    change lineSupport Q A.1 ∩ lineSupport Q C.1 = ∅
    rw [hA, hC]
    exact Finset.card_eq_zero.mp hzero
  have hinvcard : Fintype.card (AwayFrom p) = 10 := by
    rw [card_awayFrom, hcard]
  have hinvthree : (blockSystem Q).lineCount 3 = 6 := by
    rcases (elevenFive_threeFive_k31_inverted_census cfg p hlocal
      (Or.inr hthree) hfive).1 with h6 | h9
    · omega
    · exact h9.2
  obtain ⟨e, he, hea, hed, heA, heC⟩ :=
    elevenFive_threeFive_singleton_inverted_path
      cfg hcard p hfive hb hd hbp hdp hbd hinter
  change ((blockSystem Q).support e.1 ∩ (blockSystem Q).support a.1).card = 1 at heA
  change ((blockSystem Q).support e.1 ∩ (blockSystem Q).support d'.1).card = 1 at heC
  exact three_four_path_six_actual_dual_grid_impossible
    Q hinvcard a d' e ha hd' he hab heA heC hinvthree

end Erdos506.V1
