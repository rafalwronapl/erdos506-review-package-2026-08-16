import Erdos506.Incidence.RadicalAxisFourFourGeometry
import Erdos506.Incidence.ProjectiveCompletion
import Mathlib.Tactic

/-!
# A barycentric exit from a real projective triangle

This file isolates the elementary coordinate step in the Felsner sector
argument.  In the affine gauge, the base has height zero, the selected point
has height one, and the three ordered base points have coordinates
`t1 < t2 < t3`.  A transverse line through the middle base point is recorded
by its height-one coordinate `delta`.
-/

namespace Erdos506.Incidence

open Erdos506.V4
open Matrix
open scoped LinearAlgebra.Projectivization

/-- If `a > 0` and the height-one displacement is negative, the left exit
parameter lies strictly between the base and the selected point. -/
theorem triangleExit_left_parameter_mem_unitInterval
    {a delta : ℝ} (ha : 0 < a) (hdelta : delta < 0) :
    0 < a / (a - delta) ∧ a / (a - delta) < 1 := by
  have hden : 0 < a - delta := by linarith
  exact ⟨div_pos ha hden, (div_lt_one hden).2 (by linarith)⟩

/-- If `b > 0` and the height-one displacement is positive, the right exit
parameter lies strictly between the base and the selected point. -/
theorem triangleExit_right_parameter_mem_unitInterval
    {b delta : ℝ} (hb : 0 < b) (hdelta : 0 < delta) :
    0 < b / (delta + b) ∧ b / (delta + b) < 1 := by
  have hden : 0 < delta + b := by linarith
  exact ⟨div_pos hb hden, (div_lt_one hden).2 (by linarith)⟩

/-- Scalar barycentric exit.  At height `h`, the transverse middle line has
first coordinate `t2 * (1-h) + delta*h`; one of the two outer chords has the
same coordinate at a strict intermediate height. -/
theorem triangleExit_barycentric
    (t1 t2 t3 delta : ℝ) (h12 : t1 < t2) (h23 : t2 < t3)
    (hdelta : delta ≠ 0) :
    (∃ h : ℝ, 0 < h ∧ h < 1 ∧
      t2 * (1 - h) + delta * h = t1 * (1 - h)) ∨
    (∃ h : ℝ, 0 < h ∧ h < 1 ∧
      t2 * (1 - h) + delta * h = t3 * (1 - h)) := by
  rcases lt_or_gt_of_ne hdelta with hneg | hpos
  · let a := t2 - t1
    have ha : 0 < a := by dsimp only [a]; linarith
    have hh := triangleExit_left_parameter_mem_unitInterval ha hneg
    left
    refine ⟨a / (a - delta), hh.1, hh.2, ?_⟩
    dsimp only [a]
    field_simp [ne_of_gt (show 0 < t2 - t1 - delta by linarith)]
    ring
  · let b := t3 - t2
    have hb : 0 < b := by dsimp only [b]; linarith
    have hh := triangleExit_right_parameter_mem_unitInterval hb hpos
    right
    refine ⟨b / (delta + b), hh.1, hh.2, ?_⟩
    dsimp only [b]
    field_simp [ne_of_gt (show 0 < delta + (t3 - t2) by linarith)]
    ring

/-! ## Canonical affine and homogeneous representatives -/

/-- A point of coordinate `t` on the height-zero base. -/
noncomputable def triangleExitBasePoint (t : ℝ) : Point2 :=
  Erdos506.V3.pointOfCoords t 0

/-- A point of coordinate `delta` on the height-one slice.  The selected
triangle vertex is `triangleExitTopPoint 0`. -/
noncomputable def triangleExitTopPoint (delta : ℝ) : Point2 :=
  Erdos506.V3.pointOfCoords delta 1

/-- The point at height `h` on the chord from the base coordinate `t` to the
selected vertex `(0,1)`. -/
noncomputable def triangleExitRayPoint (t h : ℝ) : Point2 :=
  Erdos506.V3.pointOfCoords (t * (1 - h)) h

/-- The point at height `h` on the line from `(t2,0)` to `(delta,1)`. -/
noncomputable def triangleExitMiddlePoint (t2 delta h : ℝ) : Point2 :=
  Erdos506.V3.pointOfCoords (t2 * (1 - h) + delta * h) h

theorem triangleExitBasePoint_ne_topPoint (t delta : ℝ) :
    triangleExitBasePoint t ≠ triangleExitTopPoint delta := by
  intro h
  have hcoord := congrArg (fun p : Point2 => p 1) h
  norm_num [triangleExitBasePoint, triangleExitTopPoint] at hcoord

/-- The ray formula is literally the affine segment parameterization. -/
theorem triangleExitRayPoint_eq_lineMap (t h : ℝ) :
    triangleExitRayPoint t h =
      AffineMap.lineMap (triangleExitBasePoint t)
        (triangleExitTopPoint 0) h := by
  ext i
  fin_cases i <;>
    simp [triangleExitRayPoint, triangleExitBasePoint,
      triangleExitTopPoint, AffineMap.lineMap_apply] <;> ring

/-- The middle-line formula is literally the affine segment
parameterization from `(t2,0)` to `(delta,1)`. -/
theorem triangleExitMiddlePoint_eq_lineMap (t2 delta h : ℝ) :
    triangleExitMiddlePoint t2 delta h =
      AffineMap.lineMap (triangleExitBasePoint t2)
        (triangleExitTopPoint delta) h := by
  ext i
  fin_cases i <;>
    simp [triangleExitMiddlePoint, triangleExitBasePoint,
      triangleExitTopPoint, AffineMap.lineMap_apply] <;> ring

/-- Homogeneously, the ray point is the barycentric combination of its base
endpoint and the selected height-one point. -/
theorem homogeneousLift_triangleExitRayPoint (t h : ℝ) :
    homogeneousLift (triangleExitRayPoint t h) =
      (1 - h) • homogeneousLift (triangleExitBasePoint t) +
        h • homogeneousLift (triangleExitTopPoint 0) := by
  ext i
  fin_cases i <;>
    simp [triangleExitRayPoint, triangleExitBasePoint,
      triangleExitTopPoint, homogeneousLift] <;> ring

/-- The analogous homogeneous barycentric formula for the transverse line. -/
theorem homogeneousLift_triangleExitMiddlePoint (t2 delta h : ℝ) :
    homogeneousLift (triangleExitMiddlePoint t2 delta h) =
      (1 - h) • homogeneousLift (triangleExitBasePoint t2) +
        h • homogeneousLift (triangleExitTopPoint delta) := by
  ext i
  fin_cases i <;>
    simp [triangleExitMiddlePoint, triangleExitBasePoint,
      triangleExitTopPoint, homogeneousLift] <;> ring

/-- A linear coordinate chart transports the canonical ray formula back to
the original homogeneous plane. -/
theorem triangleExit_coordinate_barycentric
    (coord : Homogeneous3 ≃ₗ[ℝ] Homogeneous3)
    {X V : Homogeneous3} (t h : ℝ)
    (hX : coord X = homogeneousLift (triangleExitTopPoint 0))
    (hV : coord V = homogeneousLift (triangleExitBasePoint t)) :
    coord ((1 - h) • V + h • X) =
      homogeneousLift (triangleExitRayPoint t h) := by
  rw [map_add, map_smul, map_smul, hV, hX]
  exact (homogeneousLift_triangleExitRayPoint t h).symm

/-- The transported barycentric point is nonzero: its canonical image has
gauge coordinate one. -/
theorem triangleExit_barycentricVector_ne_zero
    (coord : Homogeneous3 ≃ₗ[ℝ] Homogeneous3)
    {X V : Homogeneous3} (t h : ℝ)
    (hX : coord X = homogeneousLift (triangleExitTopPoint 0))
    (hV : coord V = homogeneousLift (triangleExitBasePoint t)) :
    (1 - h) • V + h • X ≠ 0 := by
  intro hzero
  have himage := congrArg coord hzero
  rw [triangleExit_coordinate_barycentric coord t h hX hV,
    map_zero] at himage
  exact homogeneousLift_ne_zero (triangleExitRayPoint t h) himage

theorem triangleExitRayPoint_mem_affineSpan (t h : ℝ) :
    triangleExitRayPoint t h ∈
      affineSpan ℝ
        ({triangleExitBasePoint t, triangleExitTopPoint 0} : Set Point2) := by
  apply mem_affineSpan_pair_iff_exists_lineMap_eq.mpr
  exact ⟨h, (triangleExitRayPoint_eq_lineMap t h).symm⟩

theorem triangleExitMiddlePoint_mem_affineSpan (t2 delta h : ℝ) :
    triangleExitMiddlePoint t2 delta h ∈
      affineSpan ℝ
        ({triangleExitBasePoint t2,
          triangleExitTopPoint delta} : Set Point2) := by
  apply mem_affineSpan_pair_iff_exists_lineMap_eq.mpr
  exact ⟨h, (triangleExitMiddlePoint_eq_lineMap t2 delta h).symm⟩

/-- A scalar exit equation identifies the two canonical affine
representatives, with no projective rescaling needed. -/
theorem triangleExitMiddlePoint_eq_rayPoint
    {t2 delta t h : ℝ}
    (heq : t2 * (1 - h) + delta * h = t * (1 - h)) :
    triangleExitMiddlePoint t2 delta h = triangleExitRayPoint t h := by
  ext i
  fin_cases i
  · simpa [triangleExitMiddlePoint, triangleExitRayPoint] using heq
  · simp [triangleExitMiddlePoint, triangleExitRayPoint]

/-- The canonical covector of the transverse line
`X = t2*Z + (delta-t2)*H`. -/
def triangleExitMiddleCovector (t2 delta : ℝ) : Homogeneous3 :=
  ![1, t2 - delta, -t2]

theorem triangleExitMiddleCovector_ne_zero (t2 delta : ℝ) :
    triangleExitMiddleCovector t2 delta ≠ 0 := by
  intro hzero
  have hcoord := congrFun hzero (0 : Fin 3)
  norm_num [triangleExitMiddleCovector] at hcoord

/-- The entire transverse affine parameterization annihilates its canonical
homogeneous covector. -/
theorem triangleExitMiddlePoint_incident (t2 delta h : ℝ) :
    homogeneousIncident (triangleExitMiddlePoint t2 delta h)
      (triangleExitMiddleCovector t2 delta) := by
  simp [homogeneousIncident, triangleExitMiddlePoint,
    triangleExitMiddleCovector, homogeneousLift, dotProduct,
    Fin.sum_univ_three]
  ring

/-- Pulling the canonical middle covector back along a coordinate
equivalence turns the scalar exit equation into actual homogeneous
incidence. -/
theorem triangleExit_barycentricVector_middle_eq_zero
    (coord : Homogeneous3 ≃ₗ[ℝ] Homogeneous3)
    (m : Homogeneous3 →ₗ[ℝ] ℝ)
    {X V : Homogeneous3} {t2 delta t h : ℝ}
    (hX : coord X = homogeneousLift (triangleExitTopPoint 0))
    (hV : coord V = homogeneousLift (triangleExitBasePoint t))
    (hm : ∀ Z, m Z =
      coord Z ⬝ᵥ triangleExitMiddleCovector t2 delta)
    (heq : t2 * (1 - h) + delta * h = t * (1 - h)) :
    m ((1 - h) • V + h • X) = 0 := by
  rw [hm, triangleExit_coordinate_barycentric coord t h hX hV,
    ← triangleExitMiddlePoint_eq_rayPoint heq]
  exact triangleExitMiddlePoint_incident t2 delta h

/-- A linear covector vanishing at both endpoints vanishes along their
barycentric chord. -/
theorem triangleExit_barycentricVector_line_eq_zero
    (f : Homogeneous3 →ₗ[ℝ] ℝ) {X V : Homogeneous3} (h : ℝ)
    (hV : f V = 0) (hX : f X = 0) :
    f ((1 - h) • V + h • X) = 0 := by
  rw [map_add, map_smul, map_smul, hV, hX]
  simp

/-- Coordinate-free homogeneous form of the exit.  The middle covector is
the pullback of its canonical equation, while `left` and `right` are the two
actual outer support covectors. -/
theorem triangleExit_transportedBarycentric
    (coord : Homogeneous3 ≃ₗ[ℝ] Homogeneous3)
    (middle left right : Homogeneous3 →ₗ[ℝ] ℝ)
    {X V1 V3 : Homogeneous3}
    (t1 t2 t3 delta : ℝ) (h12 : t1 < t2) (h23 : t2 < t3)
    (hdelta : delta ≠ 0)
    (hX : coord X = homogeneousLift (triangleExitTopPoint 0))
    (hV1 : coord V1 = homogeneousLift (triangleExitBasePoint t1))
    (hV3 : coord V3 = homogeneousLift (triangleExitBasePoint t3))
    (hmiddle : ∀ Z, middle Z =
      coord Z ⬝ᵥ triangleExitMiddleCovector t2 delta)
    (hleftV : left V1 = 0) (hleftX : left X = 0)
    (hrightV : right V3 = 0) (hrightX : right X = 0) :
    (∃ h : ℝ, 0 < h ∧ h < 1 ∧
      let Y := (1 - h) • V1 + h • X
      Y ≠ 0 ∧ middle Y = 0 ∧ left Y = 0 ∧
        coord Y = homogeneousLift (triangleExitRayPoint t1 h)) ∨
    (∃ h : ℝ, 0 < h ∧ h < 1 ∧
      let Y := (1 - h) • V3 + h • X
      Y ≠ 0 ∧ middle Y = 0 ∧ right Y = 0 ∧
        coord Y = homogeneousLift (triangleExitRayPoint t3 h)) := by
  rcases triangleExit_barycentric t1 t2 t3 delta h12 h23 hdelta with
    ⟨h, hh0, hh1, heq⟩ | ⟨h, hh0, hh1, heq⟩
  · left
    refine ⟨h, hh0, hh1, ?_, ?_, ?_, ?_⟩
    · exact triangleExit_barycentricVector_ne_zero coord t1 h hX hV1
    · exact triangleExit_barycentricVector_middle_eq_zero
        coord middle hX hV1 hmiddle heq
    · exact triangleExit_barycentricVector_line_eq_zero
        left h hleftV hleftX
    · exact triangleExit_coordinate_barycentric coord t1 h hX hV1
  · right
    refine ⟨h, hh0, hh1, ?_, ?_, ?_, ?_⟩
    · exact triangleExit_barycentricVector_ne_zero coord t3 h hX hV3
    · exact triangleExit_barycentricVector_middle_eq_zero
        coord middle hX hV3 hmiddle heq
    · exact triangleExit_barycentricVector_line_eq_zero
        right h hrightV hrightX
    · exact triangleExit_coordinate_barycentric coord t3 h hX hV3

/-- The corresponding actual projective line. -/
noncomputable def triangleExitMiddleLine (t2 delta : ℝ) :
    RealProjectiveLine :=
  Projectivization.mk ℝ (triangleExitMiddleCovector t2 delta)
    (triangleExitMiddleCovector_ne_zero t2 delta)

theorem triangleExitMiddlePoint_orthogonal_middleLine
    (t2 delta h : ℝ) :
    Projectivization.orthogonal
      (projectivePoint (triangleExitMiddlePoint t2 delta h))
      (triangleExitMiddleLine t2 delta) := by
  simpa only [projectivePoint, triangleExitMiddleLine,
    Projectivization.orthogonal_mk] using
      triangleExitMiddlePoint_incident t2 delta h

/-- The actual projective chord from `(t,0)` to the selected point `(0,1)`. -/
noncomputable def triangleExitOuterLine (t : ℝ) : RealProjectiveLine :=
  projectiveLine (triangleExitBasePoint t) (triangleExitTopPoint 0)
    (triangleExitBasePoint_ne_topPoint t 0)

theorem triangleExitRayPoint_orthogonal_outerLine (t h : ℝ) :
    Projectivization.orthogonal
      (projectivePoint (triangleExitRayPoint t h))
      (triangleExitOuterLine t) := by
  have hraw : homogeneousIncident (triangleExitRayPoint t h)
      (lineCovector (triangleExitBasePoint t) (triangleExitTopPoint 0)) :=
    (homogeneousIncident_lineCovector_iff_mem_affineSpan
      (triangleExitBasePoint_ne_topPoint t 0)).2
        (triangleExitRayPoint_mem_affineSpan t h)
  simpa only [projectivePoint, triangleExitOuterLine, projectiveLine,
    Projectivization.orthogonal_mk] using hraw

/-- Canonical projective exit: the produced affine-chart point lies on the
transverse middle line and on one of the two outer projective chords, at a
height strictly between zero and one. -/
theorem triangleExit_projective
    (t1 t2 t3 delta : ℝ) (h12 : t1 < t2) (h23 : t2 < t3)
    (hdelta : delta ≠ 0) :
    (∃ h : ℝ, 0 < h ∧ h < 1 ∧
      Projectivization.orthogonal
        (projectivePoint (triangleExitRayPoint t1 h))
        (triangleExitMiddleLine t2 delta) ∧
      Projectivization.orthogonal
        (projectivePoint (triangleExitRayPoint t1 h))
        (triangleExitOuterLine t1)) ∨
    (∃ h : ℝ, 0 < h ∧ h < 1 ∧
      Projectivization.orthogonal
        (projectivePoint (triangleExitRayPoint t3 h))
        (triangleExitMiddleLine t2 delta) ∧
      Projectivization.orthogonal
        (projectivePoint (triangleExitRayPoint t3 h))
        (triangleExitOuterLine t3)) := by
  rcases triangleExit_barycentric t1 t2 t3 delta h12 h23 hdelta with
    ⟨h, hh0, hh1, heq⟩ | ⟨h, hh0, hh1, heq⟩
  · left
    refine ⟨h, hh0, hh1, ?_, triangleExitRayPoint_orthogonal_outerLine t1 h⟩
    rw [← triangleExitMiddlePoint_eq_rayPoint heq]
    exact triangleExitMiddlePoint_orthogonal_middleLine t2 delta h
  · right
    refine ⟨h, hh0, hh1, ?_, triangleExitRayPoint_orthogonal_outerLine t3 h⟩
    rw [← triangleExitMiddlePoint_eq_rayPoint heq]
    exact triangleExitMiddlePoint_orthogonal_middleLine t2 delta h

end Erdos506.Incidence
