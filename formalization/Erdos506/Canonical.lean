import Erdos506.V1.Sharpness

/-!
# Exact Formal Conjectures endpoint for Erdős Problem 506

This module uses the same `numCircles` definition and the same `IsLeast`
predicate as `FormalConjectures/ErdosProblems/506.lean`.  The bridge below
identifies that set-based count with the finite circumcircle count used by the
internal V1 development.
-/

namespace Erdos506

open EuclideanGeometry
open V4

/-- Verbatim mathematical definition used by Formal Conjectures. -/
noncomputable def numCircles (P : Set Point2) : ℕ :=
  Set.ncard {s : Sphere Point2 | 3 ≤ {p ∈ P | p ∈ s}.ncard}

noncomputable def sphereLabelTrace {α : Type*} [Fintype α]
    (cfg : Configuration α) (s : Sphere Point2) : Finset α := by
  classical
  exact Finset.univ.filter fun x => cfg x ∈ s

@[simp] theorem mem_sphereLabelTrace {α : Type*} [Fintype α]
    (cfg : Configuration α) (s : Sphere Point2) (x : α) :
    x ∈ sphereLabelTrace cfg s ↔ cfg x ∈ s := by
  classical
  simp [sphereLabelTrace]

theorem selectedOnSphere_eq_image {α : Type*} [Fintype α]
    (cfg : Configuration α) (s : Sphere Point2) :
    {p ∈ pointSet cfg | p ∈ s} =
      cfg '' (sphereLabelTrace cfg s : Set α) := by
  ext p
  constructor
  · rintro ⟨⟨x, rfl⟩, hx⟩
    exact ⟨x, mem_sphereLabelTrace cfg s x |>.mpr hx, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨⟨x, rfl⟩, (mem_sphereLabelTrace cfg s x).mp hx⟩

theorem selectedOnSphere_ncard {α : Type*} [Fintype α]
    (cfg : Configuration α) (s : Sphere Point2) :
    {p ∈ pointSet cfg | p ∈ s}.ncard = (sphereLabelTrace cfg s).card := by
  classical
  rw [selectedOnSphere_eq_image]
  rw [cfg.injective.injOn.ncard_image]
  simp

theorem circleTrace_eq_sphereLabelTrace {α : Type*} [Fintype α]
    (cfg : Configuration α) (c : ProperCircle) :
    circleTrace cfg c = sphereLabelTrace cfg c.1 := by
  classical
  ext x
  simp [mem_circleTrace, mem_sphereLabelTrace,
    EuclideanGeometry.mem_sphere, dist_eq_norm]

abbrev RichSphere {α : Type*} [Fintype α] (cfg : Configuration α) :=
  {s : Sphere Point2 // 3 ≤ {p ∈ pointSet cfg | p ∈ s}.ncard}

theorem richSphere_radius_pos {α : Type*} [Fintype α]
    (cfg : Configuration α) (s : RichSphere cfg) : 0 < s.1.radius := by
  classical
  have hcard : 3 ≤ (sphereLabelTrace cfg s.1).card := by
    rw [← selectedOnSphere_ncard cfg s.1]
    exact s.2
  have hone : 1 < (sphereLabelTrace cfg s.1).card := by omega
  obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.mp hone
  have hxs : cfg x ∈ s.1 := (mem_sphereLabelTrace cfg s.1 x).mp hx
  have hys : cfg y ∈ s.1 := (mem_sphereLabelTrace cfg s.1 y).mp hy
  have hrnonneg : 0 ≤ s.1.radius := s.1.radius_nonneg_of_mem hxs
  by_contra hnot
  have hrzero : s.1.radius = 0 := le_antisymm (le_of_not_gt hnot) hrnonneg
  have hxc : cfg x = s.1.center := by
    apply dist_eq_zero.mp
    rw [EuclideanGeometry.mem_sphere.mp hxs, hrzero]
  have hyc : cfg y = s.1.center := by
    apply dist_eq_zero.mp
    rw [EuclideanGeometry.mem_sphere.mp hys, hrzero]
  exact hxy (cfg.injective (hxc.trans hyc.symm))

noncomputable def richSphereToDetermined {α : Type*} [Fintype α]
    [DecidableEq α]
    (cfg : Configuration α) : RichSphere cfg → V1.DeterminedCircle cfg :=
  fun s => ⟨⟨s.1, richSphere_radius_pos cfg s⟩, by
    apply V1.mem_determinedCircles_of_three_le_circleTrace
    rw [circleTrace_eq_sphereLabelTrace,
      ← selectedOnSphere_ncard cfg s.1]
    exact s.2⟩

noncomputable def determinedToRichSphere {α : Type*} [Fintype α]
    (cfg : Configuration α) : V1.DeterminedCircle cfg → RichSphere cfg :=
  fun c => ⟨c.1.1, by
    rw [selectedOnSphere_ncard,
      ← circleTrace_eq_sphereLabelTrace cfg c.1]
    exact V3.circleSupport_card_ge_three cfg c⟩

noncomputable def richSphereEquivDetermined {α : Type*} [Fintype α]
    [DecidableEq α]
    (cfg : Configuration α) :
    RichSphere cfg ≃ V1.DeterminedCircle cfg where
  toFun := richSphereToDetermined cfg
  invFun := determinedToRichSphere cfg
  left_inv s := by
    apply Subtype.ext
    rfl
  right_inv c := by
    apply Subtype.ext
    rfl

theorem numCircles_pointSet_eq_circleCount {α : Type*} [Fintype α]
    (cfg : Configuration α) :
    numCircles (pointSet cfg) = circleCount cfg := by
  classical
  unfold numCircles
  calc
    Set.ncard {s : Sphere Point2 | 3 ≤
        {p ∈ pointSet cfg | p ∈ s}.ncard} =
        Set.ncard {c : ProperCircle | c ∈ determinedCircles cfg} :=
      Set.ncard_congr' (richSphereEquivDetermined cfg)
    _ = circleCount cfg := by simp [circleCount]

noncomputable def finsetConfiguration (P : Finset Point2) : Configuration P :=
  ⟨fun p => p.1, Subtype.val_injective⟩

theorem pointSet_finsetConfiguration (P : Finset Point2) :
    pointSet (finsetConfiguration P) = (P : Set Point2) := by
  ext p
  constructor
  · rintro ⟨x, rfl⟩
    exact x.2
  · intro hp
    exact ⟨⟨p, hp⟩, rfl⟩

noncomputable def configurationFinset {α : Type*} [Fintype α]
    (cfg : Configuration α) : Finset Point2 := by
  classical
  exact Finset.univ.image cfg

theorem card_configurationFinset {α : Type*} [Fintype α]
    (cfg : Configuration α) :
    (configurationFinset cfg).card = Fintype.card α := by
  classical
  rw [configurationFinset, Finset.card_image_of_injective _ cfg.injective]
  simp

theorem coe_configurationFinset {α : Type*} [Fintype α]
    (cfg : Configuration α) :
    (configurationFinset cfg : Set Point2) = pointSet cfg := by
  classical
  ext p
  simp [configurationFinset, pointSet]

theorem V1.notConcyclic_of_not_cospherical {α : Type*} [Fintype α]
    (cfg : Configuration α) (hcos : ¬Cospherical (pointSet cfg)) :
    V1.NotConcyclic cfg := by
  classical
  intro c
  have hle : (circleTrace cfg c).card ≤ Fintype.card α := by
    simpa using Finset.card_le_card (Finset.subset_univ (circleTrace cfg c))
  by_contra hnot
  have hge : Fintype.card α ≤ (circleTrace cfg c).card :=
    Nat.le_of_not_gt hnot
  have hfull : circleTrace cfg c = Finset.univ := by
    apply Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
    simpa using hge
  apply hcos
  rw [cospherical_iff_exists_sphere]
  refine ⟨c.1, ?_⟩
  rintro p ⟨x, rfl⟩
  apply mem_circleTrace.mp
  rw [hfull]
  simp

theorem not_cospherical_of_V1_notConcyclic
    {α : Type*} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (hcard : 3 ≤ Fintype.card α)
    (hnot : V1.NotConcyclic cfg) :
    ¬Cospherical (pointSet cfg) := by
  classical
  intro hcos
  rw [cospherical_iff_exists_sphere] at hcos
  obtain ⟨s, hs⟩ := hcos
  have htrace : sphereLabelTrace cfg s = Finset.univ := by
    ext x
    constructor
    · intro _
      simp
    · intro _
      exact (mem_sphereLabelTrace cfg s x).mpr (hs ⟨x, rfl⟩)
  have hselected : {p ∈ pointSet cfg | p ∈ s}.ncard = Fintype.card α := by
    rw [selectedOnSphere_ncard, htrace]
    simp
  let rs : RichSphere cfg := ⟨s, by rw [hselected]; exact hcard⟩
  let c : ProperCircle := ⟨s, richSphere_radius_pos cfg rs⟩
  have hcfull : circleTrace cfg c = Finset.univ := by
    rw [circleTrace_eq_sphereLabelTrace]
    exact htrace
  have hc := hnot c
  rw [hcfull] at hc
  simpa using hc

theorem finsetConfiguration_admissible (P : Finset Point2)
    (hnon : ¬Collinear ℝ (P : Set Point2))
    (hcos : ¬Cospherical (P : Set Point2)) :
    V1.Admissible (finsetConfiguration P) := by
  constructor
  · change ¬Collinear ℝ (pointSet (finsetConfiguration P))
    rw [pointSet_finsetConfiguration]
    exact hnon
  · apply V1.notConcyclic_of_not_cospherical
    rw [pointSet_finsetConfiguration]
    exact hcos

theorem configurationFinset_not_collinear
    {α : Type*} [Fintype α] (cfg : Configuration α)
    (hnon : Noncollinear cfg) :
    ¬Collinear ℝ (configurationFinset cfg : Set Point2) := by
  simpa [coe_configurationFinset] using hnon

theorem configurationFinset_not_cospherical
    {α : Type*} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (hcard : 3 ≤ Fintype.card α)
    (hnot : V1.NotConcyclic cfg) :
    ¬Cospherical (configurationFinset cfg : Set Point2) := by
  rw [coe_configurationFinset]
  exact not_cospherical_of_V1_notConcyclic cfg hcard hnot

/-- The exact open-problem endpoint from
`FormalConjectures/ErdosProblems/506.lean`, with its answer filled by
`v1Target`. -/
theorem erdos_506 (n : ℕ) (hn : 4 ≤ n) :
    IsLeast {k : ℕ | ∃ P : Finset Point2,
      P.card = n ∧ ¬Collinear ℝ (P : Set Point2) ∧
      ¬Cospherical (P : Set Point2) ∧
      numCircles (P : Set Point2) = k}
      (v1Target n) := by
  constructor
  · obtain ⟨alpha, fintypeAlpha, decEqAlpha, cfg,
        hcard, hadm, hcount⟩ := V1.exists_v1_extremizer n hn
    letI : Fintype alpha := fintypeAlpha
    letI : DecidableEq alpha := decEqAlpha
    let P := configurationFinset cfg
    refine ⟨P, ?_, ?_, ?_, ?_⟩
    · simpa [P, card_configurationFinset] using hcard
    · exact configurationFinset_not_collinear cfg hadm.1
    · apply configurationFinset_not_cospherical cfg
      · omega
      · exact hadm.2
    · rw [coe_configurationFinset,
        numCircles_pointSet_eq_circleCount, hcount]
  · intro k hk
    obtain ⟨P, hcard, hnon, hcos, hcount⟩ := hk
    let cfg := finsetConfiguration P
    have hadm : V1.Admissible cfg :=
      finsetConfiguration_admissible P hnon hcos
    have hcfgcard : Fintype.card P = n := by simpa using hcard
    have hlower := V1.circleCount_ge_v1Target cfg hadm (by
      simpa [hcfgcard] using hn)
    have hcircleCount : circleCount cfg = k := by
      rw [← numCircles_pointSet_eq_circleCount cfg,
        pointSet_finsetConfiguration, hcount]
    simpa [hcfgcard, hcircleCount] using hlower

end Erdos506
