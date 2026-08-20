import Erdos506.Incidence.RealProjectiveArrangementKellyMoserAttachmentFinish

/-!
# Actual fixed-chart exit from an empty Kelly triangle

This leaf upgrades the homogeneous strict-three-cone exit to an actual
arrangement vertex and retains its literal intersection identity.
-/

namespace Erdos506.Incidence

namespace FiniteProjectiveLineArrangement

variable {Line : Type*} [Fintype Line] [DecidableEq Line]

/-- A zero of an additional line in the strict triangle below an ordinary
apex yields a literal side intersection of strictly smaller fixed-chart
height. -/
theorem exists_lower_fixedChart_intersection_of_strictThreeCone_zero
    (A : FiniteProjectiveLineArrangement Line) (sigma : Line -> Bool)
    (fixedGauge : (Fin 3 → Real) →ₗ[Real] Real)
    (q : A.OrdinaryVertex) (l a b m : Line) (Z : Fin 3 -> Real)
    (htriangle : ¬ ∃ r : RealProjectivePoint,
      A.Incident r l ∧ A.Incident r a ∧ A.Incident r b)
    (hla : l ≠ a) (hlb : l ≠ b) (hab : a ≠ b)
    (hmK : m ∉ ({l, a, b} : Finset Line))
    (hqaway : ¬ A.Incident q.1 l)
    (hqa : A.Incident q.1 a) (hqb : A.Incident q.1 b)
    (hordinary : ∀ k : Line,
      A.Incident q.1 k ↔ k = a ∨ k = b)
    (hfq : fixedGauge q.1.rep ≠ 0)
    (hfVleft : fixedGauge (A.intersection l a).rep ≠ 0)
    (hfVright : fixedGauge (A.intersection l b).rep ≠ 0)
    (hXbase : 0 < A.arrangementOrientedEvaluation sigma l
      (vertexChartNormalizedVector fixedGauge q.1))
    (hVleftRight : 0 < A.arrangementOrientedEvaluation sigma b
      (vertexChartNormalizedVector fixedGauge (A.intersection l a)))
    (hVrightLeft : 0 < A.arrangementOrientedEvaluation sigma a
      (vertexChartNormalizedVector fixedGauge (A.intersection l b)))
    (hZ : Z ∈ A.arrangementSignConeOn sigma {l, a, b})
    (hZm : A.arrangementOrientedEvaluation sigma m Z = 0) :
    ∃ y : RealProjectivePoint, ∃ h : Real,
      0 < h ∧ h < 1 ∧ y ∈ A.vertexSet ∧
      ¬ A.Incident y l ∧
      A.vertexChartLineHeight fixedGauge l y <
        A.vertexChartLineHeight fixedGauge l q.1 ∧
      ((y = A.intersection m a ∧ A.Incident y m ∧ A.Incident y a ∧
        vertexChartNormalizedVector fixedGauge y =
          (1 - h) • vertexChartNormalizedVector fixedGauge
              (A.intersection l a) +
            h • vertexChartNormalizedVector fixedGauge q.1) ∨
       (y = A.intersection m b ∧ A.Incident y m ∧ A.Incident y b ∧
        vertexChartNormalizedVector fixedGauge y =
          (1 - h) • vertexChartNormalizedVector fixedGauge
              (A.intersection l b) +
            h • vertexChartNormalizedVector fixedGauge q.1)) := by
  let X := vertexChartNormalizedVector fixedGauge q.1
  let Vleft := vertexChartNormalizedVector fixedGauge (A.intersection l a)
  let Vright := vertexChartNormalizedVector fixedGauge (A.intersection l b)
  have hXleft : A.arrangementOrientedEvaluation sigma a X = 0 := by
    simpa only [X] using
      A.arrangementOrientedEvaluation_vertexChartNormalizedVector_eq_zero
        sigma fixedGauge hfq hqa
  have hXright : A.arrangementOrientedEvaluation sigma b X = 0 := by
    simpa only [X] using
      A.arrangementOrientedEvaluation_vertexChartNormalizedVector_eq_zero
        sigma fixedGauge hfq hqb
  have hVleftBase : A.arrangementOrientedEvaluation sigma l Vleft = 0 := by
    simpa only [Vleft] using
      A.arrangementOrientedEvaluation_vertexChartNormalizedVector_eq_zero
        sigma fixedGauge hfVleft (A.intersection_incident_left hla)
  have hVleftSide : A.arrangementOrientedEvaluation sigma a Vleft = 0 := by
    simpa only [Vleft] using
      A.arrangementOrientedEvaluation_vertexChartNormalizedVector_eq_zero
        sigma fixedGauge hfVleft (A.intersection_incident_right hla)
  have hVrightBase : A.arrangementOrientedEvaluation sigma l Vright = 0 := by
    simpa only [Vright] using
      A.arrangementOrientedEvaluation_vertexChartNormalizedVector_eq_zero
        sigma fixedGauge hfVright (A.intersection_incident_left hlb)
  have hVrightSide : A.arrangementOrientedEvaluation sigma b Vright = 0 := by
    simpa only [Vright] using
      A.arrangementOrientedEvaluation_vertexChartNormalizedVector_eq_zero
        sigma fixedGauge hfVright (A.intersection_incident_right hlb)
  have hXm : A.arrangementOrientedEvaluation sigma m X ≠ 0 := by
    apply A.arrangementOrientedEvaluation_vertexChartNormalizedVector_ne_zero
      sigma fixedGauge hfq
    intro hqm
    rcases (hordinary m).mp hqm with hma | hmb
    · subst m
      exact hmK (by simp)
    · subst m
      exact hmK (by simp)
  have hkernel : ∀ W : Fin 3 -> Real,
      A.arrangementOrientedEvaluation sigma l W = 0 ->
      A.arrangementOrientedEvaluation sigma a W = 0 ->
      A.arrangementOrientedEvaluation sigma b W = 0 -> W = 0 := by
    intro W hl ha hb
    exact A.eq_zero_of_three_orientedEvaluations_eq_zero
      sigma l a b htriangle W hl ha hb
  have hZbase : 0 < A.arrangementOrientedEvaluation sigma l Z :=
    hZ l (by simp)
  have hZleft : 0 < A.arrangementOrientedEvaluation sigma a Z :=
    hZ a (by simp)
  have hZright : 0 < A.arrangementOrientedEvaluation sigma b Z :=
    hZ b (by simp)
  have hexit := strictThreeCone_zero_exits_lower_side
    (A.arrangementOrientedEvaluation sigma l)
    (A.arrangementOrientedEvaluation sigma a)
    (A.arrangementOrientedEvaluation sigma b)
    (A.arrangementOrientedEvaluation sigma m)
    X Vleft Vright Z hkernel hXbase hXleft hXright
    hVleftBase hVleftSide (by simpa only [Vleft] using hVleftRight)
    hVrightBase hVrightSide (by simpa only [Vright] using hVrightLeft)
    hZbase hZleft hZright hZm hXm
  rcases hexit with hleft | hright
  · rcases hleft with ⟨h, hh0, hh1, hrest⟩
    dsimp only at hrest
    rcases hrest with ⟨hY0, hYm, hYa, _hYbase⟩
    have hma : m ≠ a := by
      intro h
      subst m
      exact hmK (by simp)
    obtain ⟨y, hyVertex, hym, hya, hyl, hyNorm, _hyHeight, hylt⟩ :=
      A.fixedChartExit_finish_branch sigma fixedGauge l m a q.1
        hh0 hh1 rfl hY0 hma hYm hYa hVleftBase
        (by
          simpa only [Vleft] using
            (vertexChartNormalizedVector_fixedGauge_eq_one fixedGauge
              (A.intersection l a) hfVleft))
        (by
          simpa only [X] using
            (vertexChartNormalizedVector_fixedGauge_eq_one
              fixedGauge q.1 hfq))
        hXbase.ne' rfl
    have hyEq : y = A.intersection m a :=
      A.eq_intersection_of_incident hma hym hya
    exact ⟨y, h, hh0, hh1, hyVertex, hyl, hylt,
      Or.inl ⟨hyEq, hym, hya,
        by simpa only [Vleft, X] using hyNorm⟩⟩
  · rcases hright with ⟨h, hh0, hh1, hrest⟩
    dsimp only at hrest
    rcases hrest with ⟨hY0, hYm, hYb, _hYbase⟩
    have hmb : m ≠ b := by
      intro h
      subst m
      exact hmK (by simp)
    obtain ⟨y, hyVertex, hym, hyb, hyl, hyNorm, _hyHeight, hylt⟩ :=
      A.fixedChartExit_finish_branch sigma fixedGauge l m b q.1
        hh0 hh1 rfl hY0 hmb hYm hYb hVrightBase
        (by
          simpa only [Vright] using
            (vertexChartNormalizedVector_fixedGauge_eq_one fixedGauge
              (A.intersection l b) hfVright))
        (by
          simpa only [X] using
            (vertexChartNormalizedVector_fixedGauge_eq_one
              fixedGauge q.1 hfq))
        hXbase.ne' rfl
    have hyEq : y = A.intersection m b :=
      A.eq_intersection_of_incident hmb hym hyb
    exact ⟨y, h, hh0, hh1, hyVertex, hyl, hylt,
      Or.inr ⟨hyEq, hym, hyb,
        by simpa only [Vright, X] using hyNorm⟩⟩

end FiniteProjectiveLineArrangement

end Erdos506.Incidence
