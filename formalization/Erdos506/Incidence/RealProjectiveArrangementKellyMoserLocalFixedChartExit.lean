import Erdos506.Incidence.RealProjectiveArrangementKellyMoserOuterFinish

/-!
# Local-gauge ordered fixed-chart exit

The global-gauge ordered exit only evaluates its gauge at the apex, the
three ordered returns, and the auxiliary axis return.  This leaf exposes
that exact local contract for minimizers in a projective triangle sector.
-/

namespace Erdos506.Incidence

open scoped LinearAlgebra.Projectivization

namespace FiniteProjectiveLineArrangement

variable {Line : Type*} [Fintype Line] [DecidableEq Line]

/-- Barycentric ordered exit requiring gauge nonvanishing only at the five
points which occur in the coordinate construction. -/
theorem fixedChartExit_barycentric_axis_ordered_of_localGauge
    (A : FiniteProjectiveLineArrangement Line) (sigma : Line -> Bool)
    (fixedGauge : (Fin 3 → Real) →ₗ[Real] Real)
    (l axis left right middle m : Line) (x : RealProjectivePoint)
    (hfx : fixedGauge x.rep ≠ 0)
    (hfv1 : fixedGauge (A.intersection l left).rep ≠ 0)
    (hfv2 : fixedGauge (A.intersection l middle).rep ≠ 0)
    (hfv3 : fixedGauge (A.intersection l right).rep ≠ 0)
    (hfaxis : fixedGauge (A.intersection l axis).rep ≠ 0)
    (hlaxis : l ≠ axis) (hlleft : l ≠ left)
    (hlright : l ≠ right) (hlmiddle : l ≠ middle)
    (hml : m ≠ l) (hmc : m ≠ middle)
    (hxNotBase : ¬ A.Incident x l)
    (hxleft : A.Incident x left) (hxright : A.Incident x right)
    (hxmiddle : A.Incident x middle)
    (hV2m : A.Incident (A.intersection l middle) m)
    (h12 : A.fixedChartBaseParameter sigma fixedGauge axis
        (A.intersection l left) <
      A.fixedChartBaseParameter sigma fixedGauge axis
        (A.intersection l middle))
    (h23 : A.fixedChartBaseParameter sigma fixedGauge axis
        (A.intersection l middle) <
      A.fixedChartBaseParameter sigma fixedGauge axis
        (A.intersection l right)) :
    (∃ h : Real, ∃ Y : Fin 3 -> Real,
      0 < h ∧ h < 1 ∧
      Y = (1 - h) • vertexChartNormalizedVector fixedGauge
          (A.intersection l left) +
        h • vertexChartNormalizedVector fixedGauge x ∧
      Y ≠ 0 ∧
      A.arrangementOrientedEvaluation sigma m Y = 0 ∧
      A.arrangementOrientedEvaluation sigma left Y = 0) ∨
    (∃ h : Real, ∃ Y : Fin 3 -> Real,
      0 < h ∧ h < 1 ∧
      Y = (1 - h) • vertexChartNormalizedVector fixedGauge
          (A.intersection l right) +
        h • vertexChartNormalizedVector fixedGauge x ∧
      Y ≠ 0 ∧
      A.arrangementOrientedEvaluation sigma m Y = 0 ∧
      A.arrangementOrientedEvaluation sigma right Y = 0) := by
  let v1 := A.intersection l left
  let v2 := A.intersection l middle
  let v3 := A.intersection l right
  let X := vertexChartNormalizedVector fixedGauge x
  let V1 := vertexChartNormalizedVector fixedGauge v1
  let V2 := vertexChartNormalizedVector fixedGauge v2
  let V3 := vertexChartNormalizedVector fixedGauge v3
  have hX0 : X ≠ 0 := vertexChartNormalizedVector_ne_zero _ _ hfx
  have hmkX : Projectivization.mk Real X hX0 = x := by
    simpa only [X] using
      projectivization_mk_vertexChartNormalizedVector fixedGauge x hfx
  have hXgauge : fixedGauge X = 1 := by
    simpa only [X] using
      vertexChartNormalizedVector_fixedGauge_eq_one fixedGauge x hfx
  have hXbase : A.arrangementOrientedEvaluation sigma l X ≠ 0 := by
    simpa only [X] using
      A.arrangementOrientedEvaluation_vertexChartNormalizedVector_ne_zero
        sigma fixedGauge hfx hxNotBase
  have hV1base : A.arrangementOrientedEvaluation sigma l V1 = 0 := by
    apply A.arrangementOrientedEvaluation_vertexChartNormalizedVector_eq_zero
      sigma fixedGauge hfv1
    simpa only [v1] using A.intersection_incident_left hlleft
  have hV2base : A.arrangementOrientedEvaluation sigma l V2 = 0 := by
    apply A.arrangementOrientedEvaluation_vertexChartNormalizedVector_eq_zero
      sigma fixedGauge hfv2
    simpa only [v2] using A.intersection_incident_left hlmiddle
  have hV3base : A.arrangementOrientedEvaluation sigma l V3 = 0 := by
    apply A.arrangementOrientedEvaluation_vertexChartNormalizedVector_eq_zero
      sigma fixedGauge hfv3
    simpa only [v3] using A.intersection_incident_left hlright
  have hV1gauge : fixedGauge V1 = 1 := by
    simpa only [V1, v1] using
      vertexChartNormalizedVector_fixedGauge_eq_one fixedGauge
        (A.intersection l left) hfv1
  have hV2gauge : fixedGauge V2 = 1 := by
    simpa only [V2, v2] using
      vertexChartNormalizedVector_fixedGauge_eq_one fixedGauge
        (A.intersection l middle) hfv2
  have hV3gauge : fixedGauge V3 = 1 := by
    simpa only [V3, v3] using
      vertexChartNormalizedVector_fixedGauge_eq_one fixedGauge
        (A.intersection l right) hfv3
  have hV2evalM : A.arrangementOrientedEvaluation sigma m V2 = 0 :=
    A.arrangementOrientedEvaluation_vertexChartNormalizedVector_eq_zero
      sigma fixedGauge hfv2 (by simpa only [v2] using hV2m)
  obtain ⟨scale, delta, hscale, hdelta, hform⟩ :=
    A.exists_fixedChart_middle_normalForm_delta_ne_zero
      sigma fixedGauge hlaxis hlmiddle hml hmc hfaxis
      hX0 hmkX hxNotBase hxmiddle
      (by simpa only [v2] using A.intersection_incident_left hlmiddle)
      (by simpa only [v2] using A.intersection_incident_right hlmiddle)
      (by simpa only [v2] using hV2m)
      hXbase hXgauge hV2base hV2gauge hV2evalM
  let coord := A.fixedChartArrangementCoordinateEquiv sigma fixedGauge
    l axis X hlaxis hfaxis hXbase
  let middleEval := scale⁻¹ • A.arrangementOrientedEvaluation sigma m
  have hmiddle : ∀ Z, middleEval Z =
      coord Z ⬝ᵥ triangleExitMiddleCovector
        (A.arrangementOrientedEvaluation sigma axis V2) delta := by
    intro Z
    simp only [middleEval, LinearMap.smul_apply, smul_eq_mul,
      hform Z, coord]
    rw [← mul_assoc, inv_mul_cancel₀ hscale, one_mul]
  let hkernel : ∀ Z,
      A.arrangementOrientedEvaluation sigma l Z = 0 ->
      A.arrangementOrientedEvaluation sigma axis Z = 0 ->
      fixedGauge Z = 0 -> Z = 0 :=
    fun Z hl ha hf =>
      A.eq_zero_of_two_orientedEvaluations_and_fixedGauge
        sigma fixedGauge hlaxis hfaxis Z hl ha hf
  have hmiddle' : ∀ Z, middleEval Z =
      fixedChartExitCoordinateEquiv
          (A.arrangementOrientedEvaluation sigma l)
          (A.arrangementOrientedEvaluation sigma axis)
          fixedGauge X hkernel hXbase Z ⬝ᵥ
        triangleExitMiddleCovector
          (A.arrangementOrientedEvaluation sigma axis V2) delta := by
    simpa only [coord, hkernel, fixedChartArrangementCoordinateEquiv]
      using hmiddle
  have hleftV : A.arrangementOrientedEvaluation sigma left V1 = 0 := by
    apply A.arrangementOrientedEvaluation_vertexChartNormalizedVector_eq_zero
      sigma fixedGauge hfv1
    simpa only [v1] using A.intersection_incident_right hlleft
  have hleftX : A.arrangementOrientedEvaluation sigma left X = 0 := by
    simpa only [X] using
      A.arrangementOrientedEvaluation_vertexChartNormalizedVector_eq_zero
        sigma fixedGauge hfx hxleft
  have hrightV : A.arrangementOrientedEvaluation sigma right V3 = 0 := by
    apply A.arrangementOrientedEvaluation_vertexChartNormalizedVector_eq_zero
      sigma fixedGauge hfv3
    simpa only [v3] using A.intersection_incident_right hlright
  have hrightX : A.arrangementOrientedEvaluation sigma right X = 0 := by
    simpa only [X] using
      A.arrangementOrientedEvaluation_vertexChartNormalizedVector_eq_zero
        sigma fixedGauge hfx hxright
  have ht12 : A.arrangementOrientedEvaluation sigma axis V1 <
      A.arrangementOrientedEvaluation sigma axis V2 := by
    simpa only [fixedChartBaseParameter, V1, V2, v1, v2] using h12
  have ht23 : A.arrangementOrientedEvaluation sigma axis V2 <
      A.arrangementOrientedEvaluation sigma axis V3 := by
    simpa only [fixedChartBaseParameter, V2, V3, v2, v3] using h23
  rcases fixedChart_transportedBarycentric_with_axis
      (A.arrangementOrientedEvaluation sigma l)
      (A.arrangementOrientedEvaluation sigma axis)
      (A.arrangementOrientedEvaluation sigma left)
      (A.arrangementOrientedEvaluation sigma right)
      fixedGauge middleEval hkernel hXbase hXgauge
      hV1base hV1gauge hV3base hV3gauge
      (A.arrangementOrientedEvaluation sigma axis V2) delta
      ht12 ht23 hdelta hmiddle'
      hleftV hleftX hrightV hrightX with hleftBranch | hrightBranch
  · left
    rcases hleftBranch with ⟨h, hh0, hh1, hrest⟩
    dsimp only at hrest
    rcases hrest with ⟨hY0, hYm', hYleft⟩
    have hYm : A.arrangementOrientedEvaluation sigma m
        ((1 - h) • V1 + h • X) = 0 := by
      simp only [middleEval, LinearMap.smul_apply, smul_eq_mul] at hYm'
      exact (mul_eq_zero.mp hYm').resolve_left (inv_ne_zero hscale)
    refine ⟨h, (1 - h) • V1 + h • X,
      hh0, hh1, ?_, hY0, hYm, hYleft⟩
    simp only [V1, X, v1]
  · right
    rcases hrightBranch with ⟨h, hh0, hh1, hrest⟩
    dsimp only at hrest
    rcases hrest with ⟨hY0, hYm', hYright⟩
    have hYm : A.arrangementOrientedEvaluation sigma m
        ((1 - h) • V3 + h • X) = 0 := by
      simp only [middleEval, LinearMap.smul_apply, smul_eq_mul] at hYm'
      exact (mul_eq_zero.mp hYm').resolve_left (inv_ne_zero hscale)
    refine ⟨h, (1 - h) • V3 + h • X,
      hh0, hh1, ?_, hY0, hYm, hYright⟩
    simp only [V3, X, v3]

/-- Actual ordered exit with exactly five local gauge hypotheses. -/
theorem fixedChartExit_axis_ordered_of_localGauge
    (A : FiniteProjectiveLineArrangement Line) (sigma : Line -> Bool)
    (fixedGauge : (Fin 3 → Real) →ₗ[Real] Real)
    (l axis left right middle m : Line) (x : RealProjectivePoint)
    (hfx : fixedGauge x.rep ≠ 0)
    (hfv1 : fixedGauge (A.intersection l left).rep ≠ 0)
    (hfv2 : fixedGauge (A.intersection l middle).rep ≠ 0)
    (hfv3 : fixedGauge (A.intersection l right).rep ≠ 0)
    (hfaxis : fixedGauge (A.intersection l axis).rep ≠ 0)
    (hxVertex : x ∈ A.vertexSet)
    (hlaxis : l ≠ axis) (hlleft : l ≠ left)
    (hlright : l ≠ right) (hlmiddle : l ≠ middle)
    (hml : m ≠ l) (hmc : m ≠ middle)
    (hxNotBase : ¬ A.Incident x l)
    (hxleft : A.Incident x left) (hxright : A.Incident x right)
    (hxmiddle : A.Incident x middle)
    (hV2m : A.Incident (A.intersection l middle) m)
    (h12 : A.fixedChartBaseParameter sigma fixedGauge axis
        (A.intersection l left) <
      A.fixedChartBaseParameter sigma fixedGauge axis
        (A.intersection l middle))
    (h23 : A.fixedChartBaseParameter sigma fixedGauge axis
        (A.intersection l middle) <
      A.fixedChartBaseParameter sigma fixedGauge axis
        (A.intersection l right)) :
    ∃ y : RealProjectivePoint, ∃ h : Real,
      0 < h ∧ h < 1 ∧ y ∈ A.vertexSet ∧
      A.Incident y m ∧ ¬ A.Incident y l ∧
      A.vertexChartLineHeight fixedGauge l y =
        h * A.vertexChartLineHeight fixedGauge l x ∧
      A.vertexChartLineHeight fixedGauge l y <
        A.vertexChartLineHeight fixedGauge l x ∧
      ((A.Incident y left ∧
        vertexChartNormalizedVector fixedGauge y =
          (1 - h) • vertexChartNormalizedVector fixedGauge
              (A.intersection l left) +
            h • vertexChartNormalizedVector fixedGauge x) ∨
       (A.Incident y right ∧
        vertexChartNormalizedVector fixedGauge y =
          (1 - h) • vertexChartNormalizedVector fixedGauge
              (A.intersection l right) +
            h • vertexChartNormalizedVector fixedGauge x)) := by
  have houter : m ≠ left ∧ m ≠ right := by
    constructor
    · intro hm
      subst m
      have heq : A.intersection l middle = A.intersection l left :=
        A.eq_intersection_of_incident hlleft
          (A.intersection_incident_left hlmiddle) hV2m
      rw [heq] at h12
      exact (lt_irrefl _ h12)
    · intro hm
      subst m
      have heq : A.intersection l middle = A.intersection l right :=
        A.eq_intersection_of_incident hlright
          (A.intersection_incident_left hlmiddle) hV2m
      rw [heq] at h23
      exact (lt_irrefl _ h23)
  rcases A.fixedChartExit_barycentric_axis_ordered_of_localGauge
      sigma fixedGauge l axis left right middle m x
      hfx hfv1 hfv2 hfv3 hfaxis
      hlaxis hlleft hlright hlmiddle hml hmc hxNotBase
      hxleft hxright hxmiddle hV2m h12 h23 with hleft | hright
  · rcases hleft with ⟨h, Y, hh0, hh1, hY, hY0, hYm, hYleft⟩
    have hVbase :=
      A.arrangementOrientedEvaluation_vertexChartNormalizedVector_eq_zero
        sigma fixedGauge hfv1 (A.intersection_incident_left hlleft)
    have hVgauge := vertexChartNormalizedVector_fixedGauge_eq_one
      fixedGauge (A.intersection l left) hfv1
    have hXgauge := vertexChartNormalizedVector_fixedGauge_eq_one
      fixedGauge x hfx
    have hXbase :=
      A.arrangementOrientedEvaluation_vertexChartNormalizedVector_ne_zero
        sigma fixedGauge hfx hxNotBase
    obtain ⟨y, hyVertex, hym, hyleft, hyNotBase, hyNorm,
        hyHeight, hyLt⟩ :=
      A.fixedChartExit_finish_branch sigma fixedGauge l m left x
        hh0 hh1 hY hY0 houter.1 hYm hYleft hVbase hVgauge
        hXgauge hXbase rfl
    exact ⟨y, h, hh0, hh1, hyVertex, hym, hyNotBase,
      hyHeight, hyLt, Or.inl ⟨hyleft, by simpa only [hY] using hyNorm⟩⟩
  · rcases hright with ⟨h, Y, hh0, hh1, hY, hY0, hYm, hYright⟩
    have hVbase :=
      A.arrangementOrientedEvaluation_vertexChartNormalizedVector_eq_zero
        sigma fixedGauge hfv3 (A.intersection_incident_left hlright)
    have hVgauge := vertexChartNormalizedVector_fixedGauge_eq_one
      fixedGauge (A.intersection l right) hfv3
    have hXgauge := vertexChartNormalizedVector_fixedGauge_eq_one
      fixedGauge x hfx
    have hXbase :=
      A.arrangementOrientedEvaluation_vertexChartNormalizedVector_ne_zero
        sigma fixedGauge hfx hxNotBase
    obtain ⟨y, hyVertex, hym, hyright, hyNotBase, hyNorm,
        hyHeight, hyLt⟩ :=
      A.fixedChartExit_finish_branch sigma fixedGauge l m right x
        hh0 hh1 hY hY0 houter.2 hYm hYright hVbase hVgauge
        hXgauge hXbase rfl
    exact ⟨y, h, hh0, hh1, hyVertex, hym, hyNotBase,
      hyHeight, hyLt, Or.inr ⟨hyright, by simpa only [hY] using hyNorm⟩⟩

end FiniteProjectiveLineArrangement

end Erdos506.Incidence
