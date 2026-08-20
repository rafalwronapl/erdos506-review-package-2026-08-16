import Erdos506.V1.TenFiveTwoPentagonGoldenMatching

/-!
# Concurrent golden-axis input at the two-pentagon endpoint

The three original three-lines through the chosen pivot give a matching in
the golden `2P4` graph after inversion.  The finite orbit classification
cycles that matching to one of the two canonical concurrency patterns.  This
file performs the same cyclic relabelling on the projective raw vectors and
turns the original common pivot into the common projective point required by
`GoldenAxisProjectiveInput`.
-/

namespace Erdos506.V1

open Erdos506.Finite
open Erdos506.Incidence
open Erdos506.V3
open Erdos506.V4

universe u

namespace TenTwoPentagonSaturationData

variable {α : Type u} [Fintype α] [DecidableEq α]
  {cfg : Configuration α}

/-! ## Simultaneous cyclic relabelling -/

/-- The second-pentagon raw vectors after the `k`-th canonical cycle. -/
noncomputable def cycledGoldenSecondRaw
    (d : TenTwoPentagonSaturationData cfg) (k : Fin 4) :
    Fin 5 → Homogeneous3 :=
  fun i => d.goldenSecondRaw ((kFiveStabilizerCycle ^ k.val) i)

/-- The four marked first-pentagon vectors after the matching cycle. -/
noncomputable def cycledGoldenFirstRaw
    (d : TenTwoPentagonSaturationData cfg) (k : Fin 4) :
    Fin 4 → Homogeneous3 :=
  fun i => d.goldenFirstRaw ((goldenCycleFour ^ k.val) i)

/-- A cycle power acts componentwise on a `q`-vertex. -/
theorem goldenCycleVertex_pow_apply_q :
    ∀ (k : Fin 4) (i : Fin 4),
      (goldenCycleVertex ^ k.val) (goldenQ i) =
        goldenQ ((goldenCycleFour ^ k.val) i) := by
  decide +kernel

/-- A cycle power acts componentwise on a `b`-vertex. -/
theorem goldenCycleVertex_pow_apply_b :
    ∀ (k : Fin 4) (i : Fin 5),
      (goldenCycleVertex ^ k.val) (goldenB i) =
        goldenB ((kFiveStabilizerCycle ^ k.val) i) := by
  decide +kernel

/-- The simultaneous cycle preserves each (unordered) golden chord; it may
reverse the displayed order of its two endpoints. -/
theorem kFiveStabilizerCycle_pow_goldenCenterChordEndpoint_pair :
    ∀ (k : Fin 4) (i : Fin 4) (j : Fin 2),
      ((kFiveStabilizerCycle ^ k.val) (goldenCenterChordEndpoint i j 0) =
          goldenCenterChordEndpoint ((goldenCycleFour ^ k.val) i) j 0 ∧
        (kFiveStabilizerCycle ^ k.val) (goldenCenterChordEndpoint i j 1) =
          goldenCenterChordEndpoint ((goldenCycleFour ^ k.val) i) j 1) ∨
      ((kFiveStabilizerCycle ^ k.val) (goldenCenterChordEndpoint i j 0) =
          goldenCenterChordEndpoint ((goldenCycleFour ^ k.val) i) j 1 ∧
        (kFiveStabilizerCycle ^ k.val) (goldenCenterChordEndpoint i j 1) =
          goldenCenterChordEndpoint ((goldenCycleFour ^ k.val) i) j 0) := by
  decide +kernel

private theorem det_swap_first_two_eq_zero
    (u v w : Homogeneous3) (h : Matrix.det ![u, v, w] = 0) :
    Matrix.det ![v, u, w] = 0 := by
  calc
    Matrix.det ![v, u, w] = -Matrix.det ![u, v, w] := by
      simp [Matrix.det_fin_three]
      ring
    _ = 0 := by rw [h]; simp

private theorem cycledGoldenCenterIncidence
    (d : TenTwoPentagonSaturationData cfg) (k : Fin 4) :
    GoldenAxisCenterIncidence
      (d.cycledGoldenSecondRaw k) (d.cycledGoldenFirstRaw k) := by
  intro i j
  have h := d.goldenProjectiveCore.centerIncidence
    ((goldenCycleFour ^ k.val) i) j
  rcases kFiveStabilizerCycle_pow_goldenCenterChordEndpoint_pair k i j with
    hsame | hswap
  · simpa only [cycledGoldenSecondRaw, cycledGoldenFirstRaw,
      hsame.1, hsame.2] using h
  · simpa only [cycledGoldenSecondRaw, cycledGoldenFirstRaw,
      hswap.1, hswap.2] using det_swap_first_two_eq_zero _ _ _ h

/-- The neutral projective core is stable under the simultaneous canonical
cycle on its five ordinary and four marked vectors. -/
noncomputable def cycledGoldenProjectiveCore
    (d : TenTwoPentagonSaturationData cfg) (k : Fin 4) :
    GoldenAxisProjectiveCore where
  g := d.cycledGoldenSecondRaw k
  q := d.cycledGoldenFirstRaw k
  g_generalPosition := by
    refine ⟨fun i => d.goldenProjectiveCore.g_generalPosition.1 _, ?_⟩
    intro i j l hij hil hjl
    exact d.goldenProjectiveCore.g_generalPosition.2 _ _ _
      ((kFiveStabilizerCycle ^ k.val).injective.ne hij)
      ((kFiveStabilizerCycle ^ k.val).injective.ne hil)
      ((kFiveStabilizerCycle ^ k.val).injective.ne hjl)
  q_ne_zero := fun i => d.goldenProjectiveCore.q_ne_zero _
  centerIncidence := d.cycledGoldenCenterIncidence k
  axisCollinear := fun i j l =>
    d.goldenProjectiveCore.axisCollinear _ _ _

/-! ## Original-line concurrency -/

/-- Three selected labels on one tagged source line have vanishing affine
homogeneous determinant. -/
private theorem det_eq_zero_of_mem_taggedLineAtSize
    (d : TenTwoPentagonSaturationData cfg)
    (b : TaggedLineAtSize cfg d.pivot.1 3)
    (x y : AwayFrom d.pivot.1) (hxy : x ≠ y)
    (hx : x.1 ∈ geometricBlockSupport cfg b.1)
    (hy : y.1 ∈ geometricBlockSupport cfg b.1) :
    Matrix.det ![
      homogeneousLift (pivotInversion cfg d.pivot.1 x),
      homogeneousLift (pivotInversion cfg d.pivot.1 y),
      homogeneousLift (cfg d.pivot.1)] = 0 := by
  rcases b with ⟨b, hbLine, _hbCard, hp⟩
  cases b with
  | inl L =>
      change x.1 ∈ lineSupport cfg L at hx
      change y.1 ∈ lineSupport cfg L at hy
      change d.pivot.1 ∈ lineSupport cfg L at hp
      let A : KSubset (AwayFrom d.pivot.1) 2 :=
        ⟨{x, y}, Finset.card_pair hxy⟩
      have hmem : ∀ z ∈ A.1,
          pivotInversion cfg d.pivot.1 z ∈ L.1 := by
        intro z hz
        simp only [A, Finset.mem_insert, Finset.mem_singleton] at hz
        rcases hz with hz | hz
        · subst z
          exact (pivotInversion_mem_line_iff cfg d.pivot.1 L hp x).2 hx
        · subst z
          exact (pivotInversion_mem_line_iff cfg d.pivot.1 L hp y).2 hy
      have hspan : affineSpan ℝ
          ({pivotInversion cfg d.pivot.1 x,
            pivotInversion cfg d.pivot.1 y} : Set Point2) = L.1 := by
        have howner := lineOfPair_eq_of_mem_of_direction_finrank_one
          (pivotInversion cfg d.pivot.1) A L.1 hmem L.direction_finrank
        have hexplicit : lineOfPair (pivotInversion cfg d.pivot.1) A =
            affineSpan ℝ
              ({pivotInversion cfg d.pivot.1 x,
                pivotInversion cfg d.pivot.1 y} : Set Point2) := by
          simpa only [A] using
            lineOfPair_pair (pivotInversion cfg d.pivot.1) hxy
        exact hexplicit.symm.trans howner
      apply (homogeneousIncident_lineCovector_iff_det_eq_zero
        (pivotInversion cfg d.pivot.1 x)
        (pivotInversion cfg d.pivot.1 y) (cfg d.pivot.1)).1
      apply (homogeneousIncident_lineCovector_iff_mem_affineSpan
        ((pivotInversion cfg d.pivot.1).injective.ne hxy)).2
      rw [hspan]
      exact mem_lineSupport.mp hp
  | inr c =>
      cases hbLine

/-- Membership of a classified golden edge recovers the corresponding
original label in its source three-line. -/
private theorem goldenEdgeVertex_mem_sourceLine
    (d : TenTwoPentagonSaturationData cfg)
    (hcard : Fintype.card α = 10)
    (hthree : (blockSystem cfg).lineDegree 3 d.pivot.1 = 3)
    (t : Fin 3) (v : GoldenOrdinaryVertex)
    (hv : v ∈ (d.taggedThreeLineGoldenEdge hcard hthree t).1) :
    (d.awayEquiv hcard v).1 ∈ geometricBlockSupport cfg
      (d.taggedThreeLineLabel hthree t).1 := by
  have hencoded : d.awayEquiv hcard v ∈
      d.encodeOrdinaryEdge hcard
        (d.taggedThreeLineGoldenEdge hcard hthree t) :=
    (d.mem_encodeOrdinaryEdge hcard _ v).2 hv
  rw [← d.taggedThreeLineGoldenEdge_support hcard hthree t,
    lineSupport_taggedThreeLineInvertedOrdinaryLine] at hencoded
  exact mem_awaySupport.mp hencoded

/-- Every edge in the classified three-edge image gives a determinant-zero
line through the original pivot. -/
private theorem det_goldenEdge_pivot_eq_zero
    (d : TenTwoPentagonSaturationData cfg)
    (hcard : Fintype.card α = 10)
    (hthree : (blockSystem cfg).lineDegree 3 d.pivot.1 = 3)
    (e : GoldenOrdinaryEdge) (he : e ∈ goldenThreeEdgeImage
      (d.taggedThreeLineGoldenEdge hcard hthree))
    (v w : GoldenOrdinaryVertex) (hv : v ∈ e.1) (hw : w ∈ e.1)
    (hvw : v ≠ w) :
    Matrix.det ![
      homogeneousLift (pivotInversion cfg d.pivot.1 (d.awayEquiv hcard v)),
      homogeneousLift (pivotInversion cfg d.pivot.1 (d.awayEquiv hcard w)),
      homogeneousLift (cfg d.pivot.1)] = 0 := by
  obtain ⟨t, _ht, het⟩ := Finset.mem_image.mp he
  have hv' : v ∈ (d.taggedThreeLineGoldenEdge hcard hthree t).1 := by
    rw [het]
    exact hv
  have hw' : w ∈ (d.taggedThreeLineGoldenEdge hcard hthree t).1 := by
    rw [het]
    exact hw
  have hlabels : d.awayEquiv hcard v ≠ d.awayEquiv hcard w :=
    (d.awayEquiv hcard).injective.ne hvw
  exact d.det_eq_zero_of_mem_taggedLineAtSize
    (d.taggedThreeLineLabel hthree t)
    (d.awayEquiv hcard v) (d.awayEquiv hcard w) hlabels
    (d.goldenEdgeVertex_mem_sourceLine hcard hthree t v hv')
    (d.goldenEdgeVertex_mem_sourceLine hcard hthree t w hw')

/-- A mapped displayed edge belongs to a mapped matching whenever its source
edge belongs to the original matching. -/
private theorem permutedEdge_mem_permutedMatching
    (σ : Equiv.Perm GoldenOrdinaryVertex)
    (M : Finset GoldenOrdinaryEdge) (e : GoldenOrdinaryEdge) (he : e ∈ M) :
    goldenPermuteEdgeEquiv σ e ∈ goldenPermuteMatching σ M := by
  exact Finset.mem_map.mpr ⟨e, he, rfl⟩

/-- The determinant supplied by a displayed edge after a cycle power. -/
private theorem det_permuted_pair_pivot_eq_zero
    (d : TenTwoPentagonSaturationData cfg)
    (hcard : Fintype.card α = 10)
    (hthree : (blockSystem cfg).lineDegree 3 d.pivot.1 = 3)
    (k : Fin 4) (v w : GoldenOrdinaryVertex) (hvw : v ≠ w)
    (he : goldenPermuteEdgeEquiv (goldenCycleVertex ^ k.val)
      (goldenOrdinaryEdgeOfNe v w hvw) ∈ goldenThreeEdgeImage
        (d.taggedThreeLineGoldenEdge hcard hthree)) :
    Matrix.det ![
      homogeneousLift (pivotInversion cfg d.pivot.1
        (d.awayEquiv hcard ((goldenCycleVertex ^ k.val) v))),
      homogeneousLift (pivotInversion cfg d.pivot.1
        (d.awayEquiv hcard ((goldenCycleVertex ^ k.val) w))),
      homogeneousLift (cfg d.pivot.1)] = 0 := by
  apply d.det_goldenEdge_pivot_eq_zero hcard hthree _ he
      ((goldenCycleVertex ^ k.val) v) ((goldenCycleVertex ^ k.val) w)
  · simp [goldenPermuteEdgeEquiv, goldenOrdinaryEdgeOfNe]
  · simp [goldenPermuteEdgeEquiv, goldenOrdinaryEdgeOfNe]
  · exact (goldenCycleVertex ^ k.val).injective.ne hvw

private theorem cycled_q_raw_eq
    (d : TenTwoPentagonSaturationData cfg)
    (hcard : Fintype.card α = 10) (k : Fin 4) (i : Fin 4) :
    homogeneousLift (pivotInversion cfg d.pivot.1
      (d.awayEquiv hcard ((goldenCycleVertex ^ k.val) (goldenQ i)))) =
        d.cycledGoldenFirstRaw k i := by
  rw [goldenCycleVertex_pow_apply_q]
  unfold cycledGoldenFirstRaw goldenFirstRaw goldenFirstPoint
  congr 2

private theorem cycled_b_raw_eq
    (d : TenTwoPentagonSaturationData cfg)
    (hcard : Fintype.card α = 10) (k : Fin 4) (i : Fin 5) :
    homogeneousLift (pivotInversion cfg d.pivot.1
      (d.awayEquiv hcard ((goldenCycleVertex ^ k.val) (goldenB i)))) =
        d.cycledGoldenSecondRaw k i := by
  rw [goldenCycleVertex_pow_apply_b]
  unfold cycledGoldenSecondRaw goldenSecondRaw goldenSecondPoint
  congr 2

/-! ## The final projective input -/

/-- The finite matching orbit and the concurrent original three-lines supply
one of the two canonical real projective concurrency inputs. -/
theorem tenTwoPentagon_goldenProjectiveInput
    (d : TenTwoPentagonSaturationData cfg)
    (hcard : Fintype.card α = 10)
    (hthree : (blockSystem cfg).lineDegree 3 d.pivot.1 = 3) :
    Nonempty GoldenAxisProjectiveInput := by
  classical
  obtain ⟨k, hend | hmiddle⟩ :=
    d.taggedThreeLineGoldenEdge_in_end_or_middle_orbit hcard hthree
  · refine ⟨{
      toGoldenAxisProjectiveCore := d.cycledGoldenProjectiveCore k
      concurrency := Or.inl ?_ }⟩
    refine ⟨homogeneousLift (cfg d.pivot.1), homogeneousLift_ne_zero _, ?_, ?_, ?_⟩
    · have he : goldenPermuteEdgeEquiv (goldenCycleVertex ^ k.val)
          (goldenQEdge 0) ∈ goldenThreeEdgeImage
            (d.taggedThreeLineGoldenEdge hcard hthree) := by
        rw [hend]
        apply permutedEdge_mem_permutedMatching
        simp [goldenCanonicalEndMatching]
      have hdet := d.det_permuted_pair_pivot_eq_zero hcard hthree k
        (goldenQ 0) (goldenB 1) (by simp [goldenQ, goldenB]) (by
          simpa only [goldenQEdge] using he)
      simpa only [d.cycled_q_raw_eq hcard k 0,
        d.cycled_b_raw_eq hcard k 1] using hdet
    · have he : goldenPermuteEdgeEquiv (goldenCycleVertex ^ k.val)
          (goldenQEdge 2) ∈ goldenThreeEdgeImage
            (d.taggedThreeLineGoldenEdge hcard hthree) := by
        rw [hend]
        apply permutedEdge_mem_permutedMatching
        simp [goldenCanonicalEndMatching]
      have hdet := d.det_permuted_pair_pivot_eq_zero hcard hthree k
        (goldenQ 2) (goldenB 3) (by simp [goldenQ, goldenB]) (by
          simpa only [goldenQEdge] using he)
      simpa only [d.cycled_q_raw_eq hcard k 2,
        d.cycled_b_raw_eq hcard k 3] using hdet
    · have he : goldenPermuteEdgeEquiv (goldenCycleVertex ^ k.val)
          (goldenQEdge 1) ∈ goldenThreeEdgeImage
            (d.taggedThreeLineGoldenEdge hcard hthree) := by
        rw [hend]
        apply permutedEdge_mem_permutedMatching
        simp [goldenCanonicalEndMatching]
      have hdet := d.det_permuted_pair_pivot_eq_zero hcard hthree k
        (goldenQ 1) (goldenB 2) (by simp [goldenQ, goldenB]) (by
          simpa only [goldenQEdge] using he)
      simpa only [d.cycled_q_raw_eq hcard k 1,
        d.cycled_b_raw_eq hcard k 2] using hdet
  · refine ⟨{
      toGoldenAxisProjectiveCore := d.cycledGoldenProjectiveCore k
      concurrency := Or.inr ?_ }⟩
    refine ⟨homogeneousLift (cfg d.pivot.1), homogeneousLift_ne_zero _, ?_, ?_, ?_⟩
    · have he : goldenPermuteEdgeEquiv (goldenCycleVertex ^ k.val)
          (goldenQEdge 0) ∈ goldenThreeEdgeImage
            (d.taggedThreeLineGoldenEdge hcard hthree) := by
        rw [hmiddle]
        apply permutedEdge_mem_permutedMatching
        simp [goldenCanonicalMiddleMatching]
      have hdet := d.det_permuted_pair_pivot_eq_zero hcard hthree k
        (goldenQ 0) (goldenB 1) (by simp [goldenQ, goldenB]) (by
          simpa only [goldenQEdge] using he)
      simpa only [d.cycled_q_raw_eq hcard k 0,
        d.cycled_b_raw_eq hcard k 1] using hdet
    · have he : goldenPermuteEdgeEquiv (goldenCycleVertex ^ k.val)
          (goldenQEdge 2) ∈ goldenThreeEdgeImage
            (d.taggedThreeLineGoldenEdge hcard hthree) := by
        rw [hmiddle]
        apply permutedEdge_mem_permutedMatching
        simp [goldenCanonicalMiddleMatching]
      have hdet := d.det_permuted_pair_pivot_eq_zero hcard hthree k
        (goldenQ 2) (goldenB 3) (by simp [goldenQ, goldenB]) (by
          simpa only [goldenQEdge] using he)
      simpa only [d.cycled_q_raw_eq hcard k 2,
        d.cycled_b_raw_eq hcard k 3] using hdet
    · have he : goldenPermuteEdgeEquiv (goldenCycleVertex ^ k.val)
          goldenBEdge24 ∈ goldenThreeEdgeImage
            (d.taggedThreeLineGoldenEdge hcard hthree) := by
        rw [hmiddle]
        apply permutedEdge_mem_permutedMatching
        simp [goldenCanonicalMiddleMatching]
      have hdet := d.det_permuted_pair_pivot_eq_zero hcard hthree k
        (goldenB 2) (goldenB 4) (by decide) (by
          simpa only [goldenBEdge24] using he)
      simpa only [d.cycled_b_raw_eq hcard k 2,
        d.cycled_b_raw_eq hcard k 4] using hdet

/-- The saturated two-pentagon endpoint with exactly three pivot three-lines
is impossible over the real affine plane. -/
theorem tenTwoPentagon_golden_contradiction
    (d : TenTwoPentagonSaturationData cfg)
    (hcard : Fintype.card α = 10)
    (hthree : (blockSystem cfg).lineDegree 3 d.pivot.1 = 3) : False :=
  (Classical.choice (d.tenTwoPentagon_goldenProjectiveInput hcard hthree)).not_realizable

end TenTwoPentagonSaturationData

end Erdos506.V1
