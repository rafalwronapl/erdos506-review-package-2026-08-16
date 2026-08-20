import Erdos506.V1.CircleCenterUpper
import Erdos506.V1.FiniteConstructionCertificate
import Erdos506.V3.Construction
import Erdos506.V3.EquationCircle

/-!
# The paired circle-and-centre construction

There are `r` antipodal pairs on the unit circle, optionally one further
boundary point, and the centre.  This supplies the uniform sharp examples for
V1.  The optional part is expressed as `Fin e`; applications use `e ≤ 1`.
-/

namespace Erdos506.V1

open Erdos506.V4
open scoped EuclideanGeometry

abbrev PairedBoundaryLabels (r e : ℕ) := (Fin r × Bool) ⊕ Fin e
abbrev PairedLabels (r e : ℕ) := CenterLabels (PairedBoundaryLabels r e)

noncomputable def pairedParameter {r : ℕ} (i : Fin r) : ℝ := i.1 + 1

theorem pairedParameter_pos {r : ℕ} (i : Fin r) : 0 < pairedParameter i := by
  unfold pairedParameter
  exact_mod_cast Nat.succ_pos i.1

theorem pairedParameter_injective {r : ℕ} :
    Function.Injective (pairedParameter (r := r)) := by
  intro i j hij
  apply Fin.ext
  unfold pairedParameter at hij
  have hij' : (i.1 : ℝ) = (j.1 : ℝ) := by linarith
  exact_mod_cast hij'

theorem rationalCirclePoint_second_pos {t : ℝ} (ht : 0 < t) :
    0 < Erdos506.V3.rationalCirclePoint t (1 : Fin 2) := by
  rw [Erdos506.V3.rationalCirclePoint_apply_one]
  positivity

noncomputable def pairedBoundaryPoint {r e : ℕ} :
    PairedBoundaryLabels r e → Point2
  | Sum.inl (i, false) => Erdos506.V3.rationalCirclePoint (pairedParameter i)
  | Sum.inl (i, true) => -Erdos506.V3.rationalCirclePoint (pairedParameter i)
  | Sum.inr _ => Erdos506.V3.rationalCirclePoint 0

theorem pairedBoundaryPoint_injective {r e : ℕ} (he : e ≤ 1) :
    Function.Injective (pairedBoundaryPoint (r := r) (e := e)) := by
  intro x y hxy
  rcases x with ⟨i, b⟩ | k <;> rcases y with ⟨j, c⟩ | l
  · cases b <;> cases c
    · have hij := Erdos506.V3.rationalCirclePoint_injective_nonneg
          (pairedParameter_pos i).le (pairedParameter_pos j).le hxy
      exact congrArg Sum.inl (Prod.ext (pairedParameter_injective hij) rfl)
    · have hy := congrArg (fun p : Point2 => p (1 : Fin 2)) hxy
      have hi := rationalCirclePoint_second_pos (pairedParameter_pos i)
      have hj := rationalCirclePoint_second_pos (pairedParameter_pos j)
      simp only [pairedBoundaryPoint, PiLp.neg_apply] at hy
      linarith
    · have hy := congrArg (fun p : Point2 => p (1 : Fin 2)) hxy
      have hi := rationalCirclePoint_second_pos (pairedParameter_pos i)
      have hj := rationalCirclePoint_second_pos (pairedParameter_pos j)
      simp only [pairedBoundaryPoint, PiLp.neg_apply] at hy
      linarith
    · have hneg :
          Erdos506.V3.rationalCirclePoint (pairedParameter i) =
            Erdos506.V3.rationalCirclePoint (pairedParameter j) := by
          exact neg_injective hxy
      have hij := Erdos506.V3.rationalCirclePoint_injective_nonneg
          (pairedParameter_pos i).le (pairedParameter_pos j).le hneg
      exact congrArg Sum.inl (Prod.ext (pairedParameter_injective hij) rfl)
  · exfalso
    cases b
    · have hy := congrArg (fun p : Point2 => p (1 : Fin 2)) hxy
      have hi := rationalCirclePoint_second_pos (pairedParameter_pos i)
      simp only [pairedBoundaryPoint,
        Erdos506.V3.rationalCirclePoint_apply_one] at hy
      rw [Erdos506.V3.rationalCirclePoint_apply_one] at hi
      norm_num at hy
      rcases hy with hy | hy
      · exact (ne_of_gt (pairedParameter_pos i)) hy
      · nlinarith [sq_nonneg (pairedParameter i)]
    · have hy := congrArg (fun p : Point2 => p (1 : Fin 2)) hxy
      have hi := rationalCirclePoint_second_pos (pairedParameter_pos i)
      simp only [pairedBoundaryPoint, PiLp.neg_apply,
        Erdos506.V3.rationalCirclePoint_apply_one] at hy
      rw [Erdos506.V3.rationalCirclePoint_apply_one] at hi
      norm_num at hy
      rcases hy with hy | hy
      · exact (ne_of_gt (pairedParameter_pos i)) hy
      · nlinarith [sq_nonneg (pairedParameter i)]
  · exfalso
    cases c
    · have hy := congrArg (fun p : Point2 => p (1 : Fin 2)) hxy
      have hj := rationalCirclePoint_second_pos (pairedParameter_pos j)
      simp only [pairedBoundaryPoint,
        Erdos506.V3.rationalCirclePoint_apply_one] at hy
      rw [Erdos506.V3.rationalCirclePoint_apply_one] at hj
      norm_num at hy
      linarith
    · have hy := congrArg (fun p : Point2 => p (1 : Fin 2)) hxy
      have hj := rationalCirclePoint_second_pos (pairedParameter_pos j)
      simp only [pairedBoundaryPoint, PiLp.neg_apply,
        Erdos506.V3.rationalCirclePoint_apply_one] at hy
      rw [Erdos506.V3.rationalCirclePoint_apply_one] at hj
      norm_num at hy
      rcases hy with hy | hy
      · exact (ne_of_gt (pairedParameter_pos j)) hy
      · nlinarith [sq_nonneg (pairedParameter j)]
  · apply congrArg Sum.inr
    apply Fin.ext
    omega

noncomputable def pairedPoint {r e : ℕ} : PairedLabels r e → Point2
  | Sum.inl x => pairedBoundaryPoint x
  | Sum.inr _ => 0

theorem pairedPoint_injective {r e : ℕ} (he : e ≤ 1) :
    Function.Injective (pairedPoint (r := r) (e := e)) := by
  intro x y hxy
  rcases x with x | u <;> rcases y with y | v
  · exact congrArg Sum.inl (pairedBoundaryPoint_injective he hxy)
  · have hnorm := congrArg norm hxy
    rcases x with ⟨i, b⟩ | k
    · cases b <;> simp only [pairedPoint, pairedBoundaryPoint, norm_neg,
          norm_zero] at hnorm <;>
        nlinarith [Erdos506.V3.rationalCirclePoint_norm_sq (pairedParameter i),
          norm_nonneg (Erdos506.V3.rationalCirclePoint (pairedParameter i))]
    · simp only [pairedPoint, pairedBoundaryPoint, norm_zero] at hnorm
      nlinarith [Erdos506.V3.rationalCirclePoint_norm_sq 0,
        norm_nonneg (Erdos506.V3.rationalCirclePoint 0)]
  · have hnorm := congrArg norm hxy
    rcases y with ⟨j, c⟩ | l
    · cases c <;> simp only [pairedPoint, pairedBoundaryPoint, norm_neg,
          norm_zero] at hnorm <;>
        nlinarith [Erdos506.V3.rationalCirclePoint_norm_sq (pairedParameter j),
          norm_nonneg (Erdos506.V3.rationalCirclePoint (pairedParameter j))]
    · simp only [pairedPoint, pairedBoundaryPoint, norm_zero] at hnorm
      nlinarith [Erdos506.V3.rationalCirclePoint_norm_sq 0,
        norm_nonneg (Erdos506.V3.rationalCirclePoint 0)]
  · cases u
    cases v
    rfl

noncomputable def pairedConfiguration (r e : ℕ) (he : e ≤ 1) :
    Configuration (PairedLabels r e) :=
  ⟨pairedPoint, pairedPoint_injective he⟩

theorem pairedBoundaryPoint_mem_baseSphere {r e : ℕ}
    (x : PairedBoundaryLabels r e) :
    pairedBoundaryPoint x ∈ Erdos506.V3.baseSphere := by
  rcases x with ⟨i, b⟩ | k
  · cases b
    · exact Erdos506.V3.rationalCirclePoint_mem_baseSphere _
    · rw [EuclideanGeometry.mem_sphere]
      change dist (-Erdos506.V3.rationalCirclePoint (pairedParameter i)) 0 = 1
      rw [dist_zero_right, norm_neg]
      simpa [dist_zero_right] using
        Erdos506.V3.rationalCirclePoint_dist_zero (pairedParameter i)
  · exact Erdos506.V3.rationalCirclePoint_mem_baseSphere 0

theorem paired_base_circleTrace {r e : ℕ} (he : e ≤ 1) :
    circleTrace (pairedConfiguration r e he) Erdos506.V3.baseProperCircle =
      boundaryLabels ( β := PairedBoundaryLabels r e) := by
  classical
  ext x
  rcases x with x | u
  · simp only [mem_boundaryLabels, iff_true]
    rw [mem_circleTrace]
    change pairedBoundaryPoint x ∈ Erdos506.V3.baseSphere
    exact pairedBoundaryPoint_mem_baseSphere x
  · cases u
    rw [mem_circleTrace]
    constructor
    · intro h
      change (0 : Point2) ∈ Erdos506.V3.baseSphere at h
      exact (Erdos506.V3.zero_not_mem_baseSphere h).elim
    · intro h
      exact (center_not_mem_boundaryLabels h).elim

theorem card_pairedBoundaryLabels (r e : ℕ) :
    Fintype.card (PairedBoundaryLabels r e) = 2 * r + e := by
  simp [PairedBoundaryLabels]
  omega

noncomputable def pairedBaseCircle {r e : ℕ} (he : e ≤ 1)
    (hboundary : 3 ≤ 2 * r + e) :
    DeterminedCircle (pairedConfiguration r e he) := by
  refine ⟨Erdos506.V3.baseProperCircle, ?_⟩
  apply mem_determinedCircles_of_three_le_circleTrace
  rw [paired_base_circleTrace, card_boundaryLabels,
    card_pairedBoundaryLabels]
  exact hboundary

noncomputable def pairedDiameterPair {r e : ℕ} (i : Fin r) :
    Finset (PairedLabels r e) :=
  {Sum.inl (Sum.inl (i, false)), Sum.inl (Sum.inl (i, true))}

theorem pairedDiameterPair_card {r e : ℕ} (i : Fin r) :
    (pairedDiameterPair (e := e) i).card = 2 := by
  simp [pairedDiameterPair]

theorem pairedDiameterPair_subset_baseTrace {r e : ℕ} (he : e ≤ 1)
    (hboundary : 3 ≤ 2 * r + e) (i : Fin r) :
    pairedDiameterPair (e := e) i ⊆
      circleTrace (pairedConfiguration r e he) (pairedBaseCircle he hboundary).1 := by
  change pairedDiameterPair (e := e) i ⊆
    circleTrace (pairedConfiguration r e he) Erdos506.V3.baseProperCircle
  rw [paired_base_circleTrace]
  intro x hx
  rw [pairedDiameterPair] at hx
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with rfl | rfl <;> exact mem_boundaryLabels _

theorem pairedDiameterPair_injective {r e : ℕ} :
    Function.Injective (pairedDiameterPair (r := r) (e := e)) := by
  intro i j hij
  have hmem : Sum.inl (Sum.inl (i, false)) ∈ pairedDiameterPair (e := e) j := by
    rw [← hij]
    simp [pairedDiameterPair]
  simp only [pairedDiameterPair, Finset.mem_insert, Finset.mem_singleton] at hmem
  rcases hmem with hmem | hmem
  · simpa using hmem
  · simp at hmem

theorem pairedDiameterPair_collinear {r e : ℕ} (he : e ≤ 1)
    (i : Fin r) :
    Collinear ℝ (supportPoints (pairedConfiguration r e he)
      (insert (centerLabel (β := PairedBoundaryLabels r e))
        (pairedDiameterPair (e := e) i))) := by
  let cfg := pairedConfiguration r e he
  let a : PairedLabels r e := centerLabel
  let b : PairedLabels r e := Sum.inl (Sum.inl (i, false))
  apply collinear_set_of_orientation_eq_zero
    (supportPoints cfg (insert a (pairedDiameterPair (e := e) i)))
    (cfg a) (cfg b)
  · exact ⟨a, by simp [a, pairedDiameterPair], rfl⟩
  · exact cfg.injective.ne (by simp [a, b, centerLabel])
  · intro p hp
    rcases hp with ⟨j, hj, rfl⟩
    have hj' : j = a ∨ j = b ∨
        j = Sum.inl (Sum.inl (i, true)) := by
      rcases Finset.mem_insert.mp hj with hj | hj
      · exact Or.inl hj
      · rw [pairedDiameterPair] at hj
        simp only [Finset.mem_insert, Finset.mem_singleton] at hj
        exact Or.inr hj
    rcases hj' with hj' | hj' | hj'
    · subst j
      simp [cfg, a, b, pairedConfiguration, pairedPoint,
        pairedBoundaryPoint, centerLabel, Erdos506.V3.orientation, PiLp.neg_apply]
    · subst j
      simp [cfg, a, b, pairedConfiguration, pairedPoint,
        pairedBoundaryPoint, centerLabel, Erdos506.V3.orientation, PiLp.neg_apply]
      ring
    · subst j
      simp [cfg, a, b, pairedConfiguration, pairedPoint,
        pairedBoundaryPoint, centerLabel, Erdos506.V3.orientation, PiLp.neg_apply]
      ring

theorem card_pairedLabels (r e : ℕ) :
    Fintype.card (PairedLabels r e) = 2 * r + e + 1 := by
  simp [PairedLabels, CenterLabels, card_pairedBoundaryLabels]
  omega

theorem pairedConfiguration_noncollinear {r e : ℕ} (he : e ≤ 1)
    (hboundary : 3 ≤ 2 * r + e) :
    Noncollinear (pairedConfiguration r e he) := by
  let cfg := pairedConfiguration r e he
  let g := pairedBaseCircle he hboundary
  obtain ⟨t, ht⟩ :=
    (mem_determinedCircles_iff cfg g.1).mp g.2
  intro hcol
  have htnon : IsNoncollinear cfg t.1 :=
    (mem_noncollinearTriples.mp t.2).2
  apply htnon
  apply hcol.subset
  intro p hp
  rcases hp with ⟨x, _hx, rfl⟩
  exact ⟨x, rfl⟩

theorem pairedConfiguration_notConcyclic {r e : ℕ} (he : e ≤ 1)
    (hboundary : 3 ≤ 2 * r + e) :
    NotConcyclic (pairedConfiguration r e he) := by
  classical
  let cfg := pairedConfiguration r e he
  let g := pairedBaseCircle he hboundary
  obtain ⟨t, htbase⟩ :=
    (mem_determinedCircles_iff cfg g.1).mp g.2
  intro c
  have hle : (circleTrace cfg c).card ≤ Fintype.card (PairedLabels r e) := by
    simpa using Finset.card_le_card (Finset.subset_univ (circleTrace cfg c))
  by_contra hnot
  have hge : Fintype.card (PairedLabels r e) ≤ (circleTrace cfg c).card :=
    Nat.le_of_not_gt hnot
  have hcard : (circleTrace cfg c).card = Fintype.card (PairedLabels r e) :=
    Nat.le_antisymm hle hge
  have hfull : circleTrace cfg c = Finset.univ := by
    apply Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
    simpa [hcard]
  have htc : ∀ x ∈ t.1, cfg x ∈ (c.1 : Set Point2) := by
    intro x hx
    apply mem_circleTrace.mp
    rw [hfull]
    simp
  have hc : c = g.1 := by
    have hc' := properCircle_eq_properCircumcircle_of_support cfg t c htc
    have hg' := properCircle_eq_properCircumcircle_of_support cfg t g.1 htbase
    exact hc'.trans hg'.symm
  have hcenter : centerLabel (β := PairedBoundaryLabels r e) ∈ circleTrace cfg c := by
    rw [hfull]
    simp
  have hcenter' := mem_circleTrace.mp hcenter
  rw [hc] at hcenter'
  change (0 : Point2) ∈ Erdos506.V3.baseSphere at hcenter'
  exact Erdos506.V3.zero_not_mem_baseSphere hcenter'

theorem pairedConfiguration_admissible {r e : ℕ} (he : e ≤ 1)
    (hboundary : 3 ≤ 2 * r + e) :
    Admissible (pairedConfiguration r e he) :=
  ⟨pairedConfiguration_noncollinear he hboundary,
    pairedConfiguration_notConcyclic he hboundary⟩

theorem pairedConfiguration_circleCount_le {r e : ℕ} (he : e ≤ 1)
    (hboundary : 3 ≤ 2 * r + e) :
    circleCount (pairedConfiguration r e he) ≤
      1 + Nat.choose (2 * r + e) 2 - r := by
  let cfg := pairedConfiguration r e he
  let g := pairedBaseCircle he hboundary
  have h := circleCount_le_circle_center_target
    (cfg := cfg) (g := g)
    (hg := paired_base_circleTrace he)
    (diameterPair := pairedDiameterPair (r := r) (e := e))
    (pairedDiameterPair_card (e := e))
    (pairedDiameterPair_subset_baseTrace he hboundary)
    pairedDiameterPair_injective
    (pairedDiameterPair_collinear he)
  simpa [card_pairedBoundaryLabels, Nat.mul_comm] using h

end Erdos506.V1
