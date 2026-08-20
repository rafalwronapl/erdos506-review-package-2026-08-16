import Erdos506.Incidence.ProjectiveCoordinates
import Erdos506.Finite.FourPentagonNormalizer
import Erdos506.V1.TenFiveSixPower
import Erdos506.V3.MenelausPower

/-!
# Positive coordinates for the four-pentagon normal form

The abstract hypotheses in the ten-point four-pentagon branch first force a
specific finite incidence normal form.  This file isolates that normal form
as positive data and carries it through pivot inversion, projective affine-
chart coordinates, Menelaus, and normalized circle equations.  The output is
the three pre-resultant equations in `FourPentagonCoordinateData`.

The finite normalizer is imported from `Finite.FourPentagonNormalizer`;
this module turns its positive incidence data into coordinate equations.
No terminal contradiction is used here.
-/

namespace Erdos506.V1

open Erdos506.Block
open Erdos506.Block.BlockSystem
open Erdos506.Finite
open Erdos506.Incidence
open Erdos506.V3
open Erdos506.V4
open AffineSubspace
open Matrix

universe u

/-! ## Projective and circle-coordinate lemmas -/

/-- The homogeneous affine-chart determinant is the oriented two-dimensional
determinant of the two side directions. -/
theorem det_homogeneousLift_eq_det2 (A B C : Point2) :
    Matrix.det ![homogeneousLift A, homogeneousLift B, homogeneousLift C] =
      det2 (B - A) (C - A) := by
  simp [homogeneousLift, det2, Matrix.det_fin_three]
  ring

/-- Subtracting two normalized circle equations through `A` cancels the
common quadratic part.  The remaining coefficients are determined by one
nonzero directed point on each adjacent side. -/
theorem circle_difference_on_opposite_side
    (A B C : Point2) (Γ Δ : ProperCircle)
    {a b a' b' z : ℝ}
    (ha0 : a ≠ 0) (hb0 : b ≠ 0)
    (ha'0 : a' ≠ 0) (hb'0 : b' ≠ 0)
    (hΓA : A ∈ (Γ.1 : Set Point2))
    (hΓAB : affineParamPoint A (B - A) a ∈ (Γ.1 : Set Point2))
    (hΓAC : affineParamPoint A (C - A) b ∈ (Γ.1 : Set Point2))
    (hΓZ : affineParamPoint B (C - B) z ∈ (Γ.1 : Set Point2))
    (hΔA : A ∈ (Δ.1 : Set Point2))
    (hΔAB : affineParamPoint A (B - A) a' ∈ (Δ.1 : Set Point2))
    (hΔAC : affineParamPoint A (C - A) b' ∈ (Δ.1 : Set Point2))
    (hΔZ : affineParamPoint B (C - B) z ∈ (Δ.1 : Set Point2)) :
    directionSq (B - A) * (a - a') * (1 - z) +
        directionSq (C - A) * (b - b') * z = 0 := by
  let qA : ProperCircle → ℝ := fun c =>
    circleEquation (properCircleEquationA c)
      (properCircleEquationB c) (properCircleEquationC c) A
  let lB : ProperCircle → ℝ := fun c =>
    lineCircleLinearCoefficient (properCircleEquationA c)
      (properCircleEquationB c) A (B - A)
  let lC : ProperCircle → ℝ := fun c =>
    lineCircleLinearCoefficient (properCircleEquationA c)
      (properCircleEquationB c) A (C - A)
  have hΓAEq : qA Γ = 0 :=
    by simpa [qA] using (mem_properCircle_iff_equation Γ A).mp hΓA
  have hΔAEq : qA Δ = 0 :=
    by simpa [qA] using (mem_properCircle_iff_equation Δ A).mp hΔA
  have hΓaEq :
      directionSq (B - A) * a ^ 2 + lB Γ * a + qA Γ = 0 := by
    have h := (mem_properCircle_iff_equation Γ _).mp hΓAB
    rw [circleEquation_affineParamPoint] at h
    simpa [qA, lB] using h
  have hΓbEq :
      directionSq (C - A) * b ^ 2 + lC Γ * b + qA Γ = 0 := by
    have h := (mem_properCircle_iff_equation Γ _).mp hΓAC
    rw [circleEquation_affineParamPoint] at h
    simpa [qA, lC] using h
  have hΔaEq :
      directionSq (B - A) * a' ^ 2 + lB Δ * a' + qA Δ = 0 := by
    have h := (mem_properCircle_iff_equation Δ _).mp hΔAB
    rw [circleEquation_affineParamPoint] at h
    simpa [qA, lB] using h
  have hΔbEq :
      directionSq (C - A) * b' ^ 2 + lC Δ * b' + qA Δ = 0 := by
    have h := (mem_properCircle_iff_equation Δ _).mp hΔAC
    rw [circleEquation_affineParamPoint] at h
    simpa [qA, lC] using h
  have hΓaProd : a * (directionSq (B - A) * a + lB Γ) = 0 := by
    linear_combination hΓaEq - hΓAEq
  have hΓbProd : b * (directionSq (C - A) * b + lC Γ) = 0 := by
    linear_combination hΓbEq - hΓAEq
  have hΔaProd : a' * (directionSq (B - A) * a' + lB Δ) = 0 := by
    linear_combination hΔaEq - hΔAEq
  have hΔbProd : b' * (directionSq (C - A) * b' + lC Δ) = 0 := by
    linear_combination hΔbEq - hΔAEq
  have hΓaLin : lB Γ = -directionSq (B - A) * a := by
    have := (mul_eq_zero.mp hΓaProd).resolve_left ha0
    linarith
  have hΓbLin : lC Γ = -directionSq (C - A) * b := by
    have := (mul_eq_zero.mp hΓbProd).resolve_left hb0
    linarith
  have hΔaLin : lB Δ = -directionSq (B - A) * a' := by
    have := (mul_eq_zero.mp hΔaProd).resolve_left ha'0
    linarith
  have hΔbLin : lC Δ = -directionSq (C - A) * b' := by
    have := (mul_eq_zero.mp hΔbProd).resolve_left hb'0
    linarith
  have hΓZEq := (mem_properCircle_iff_equation Γ _).mp hΓZ
  have hΔZEq := (mem_properCircle_iff_equation Δ _).mp hΔZ
  have hdifference :
      circleEquation (properCircleEquationA Γ)
          (properCircleEquationB Γ) (properCircleEquationC Γ)
          (affineParamPoint B (C - B) z) -
        circleEquation (properCircleEquationA Δ)
          (properCircleEquationB Δ) (properCircleEquationC Δ)
          (affineParamPoint B (C - B) z) =
      (lB Γ - lB Δ) * (1 - z) +
        (lC Γ - lC Δ) * z + (qA Γ - qA Δ) := by
    simp [qA, lB, lC, circleEquation, lineCircleLinearCoefficient,
      affineParamPoint]
    ring
  rw [hΓZEq, hΔZEq, hΓAEq, hΔAEq,
    hΓaLin, hΓbLin, hΔaLin, hΔbLin] at hdifference
  linear_combination hdifference

/-! ## The algebraic projection to the public certificate -/

/-- Menelaus and the four normalized circle comparisons imply exactly the
three pre-resultant equations exposed by the residual interface. -/
noncomputable def fourPentagonCoordinateData_of_raw_equations
    {c2 b2 u v s t x y : ℝ}
    (hc2 : c2 ≠ 0) (_hb2 : b2 ≠ 0)
    (huv : DistinctSideParameters u v)
    (hst : DistinctSideParameters s t)
    (_hxy : DistinctSideParameters x y)
    (hmen_x : (u - s) * x - s * (u - 1) = 0)
    (hmen_y : (u - t) * y - t * (u - 1) = 0)
    (hmen_y' : (v - s) * y - s * (v - 1) = 0)
    (hpow_one :
      c2 * (v - u) * (1 - x) + b2 * (t - 1) * x = 0)
    (hpow_two :
      c2 * (v - 1) * (1 - x) + b2 * (t - s) * x = 0)
    (hpow_three :
      c2 * (v - u) * (1 - y) + b2 * (t - s) * y = 0)
    (hpow_last : c2 * v - b2 * t = 0) :
    FourPentagonCoordinateData := by
  rcases huv with ⟨hu0, hu1, _hv0, _hv1, huv⟩
  rcases hst with ⟨hs0, hs1, _ht0, _ht1, _hst⟩
  have hpowDiff :
      c2 * (1 - u) * (1 - x) + b2 * (s - 1) * x = 0 := by
    linear_combination hpow_one - hpow_two
  have hresultant :
      (s - 1) * (u - 1) * (s * b2 + c2 * u) = 0 := by
    linear_combination
      (-s * b2 + b2 - c2 * u + c2) * hmen_x +
        (u - s) * hpowDiff
  have hsu : s * b2 + c2 * u = 0 := by
    have hleft : (s - 1) * (u - 1) ≠ 0 :=
      mul_ne_zero (sub_ne_zero.mpr hs1) (sub_ne_zero.mpr hu1)
    exact (mul_eq_zero.mp hresultant).resolve_left hleft
  have hsvutScaled : c2 * (s * v + u * t) = 0 := by
    linear_combination s * hpow_last + t * hsu
  have hsvut : s * v + u * t = 0 :=
    (mul_eq_zero.mp hsvutScaled).resolve_left hc2
  have hxScaled :
      (-c2 * u) * ((s + t) - (s + 1) * x) = 0 := by
    linear_combination
      s * hpow_one - c2 * (1 - x) * hsvut - x * (t - 1) * hsu
  have hxLinear : (s + t) - (s + 1) * x = 0 := by
    have hfactor : -c2 * u ≠ 0 := mul_ne_zero (neg_ne_zero.mpr hc2) hu0
    exact (mul_eq_zero.mp hxScaled).resolve_left hfactor
  have hpolyOne : s ^ 2 * u + s * t - s - t * u = 0 := by
    linear_combination -(s + 1) * hmen_x - (u - s) * hxLinear
  have hyScaled :
      (-c2 * u) * ((s + t) - 2 * s * y) = 0 := by
    linear_combination
      s * hpow_three - c2 * (1 - y) * hsvut - y * (t - s) * hsu
  have hyLinear : (s + t) - 2 * s * y = 0 := by
    have hfactor : -c2 * u ≠ 0 := mul_ne_zero (neg_ne_zero.mpr hc2) hu0
    exact (mul_eq_zero.mp hyScaled).resolve_left hfactor
  have hpolyTwo :
      2 * s * t * u - s * t - s * u + t ^ 2 - t * u = 0 := by
    linear_combination (-2 * s) * hmen_y - (u - t) * hyLinear
  have heliminateY :
      (v - s) * t * (u - 1) - (u - t) * s * (v - 1) = 0 := by
    linear_combination -(v - s) * hmen_y + (u - t) * hmen_y'
  have huPolyThree :
      u * (s ^ 2 * t - s ^ 2 + s * t ^ 2 - s * t * u +
        t ^ 2 * u - t ^ 2) = 0 := by
    linear_combination
      (s * t - s * u + t * u - t) * hsvut - s * heliminateY
  have hpolyThree :
      s ^ 2 * t - s ^ 2 + s * t ^ 2 - s * t * u +
        t ^ 2 * u - t ^ 2 = 0 :=
    (mul_eq_zero.mp huPolyThree).resolve_left hu0
  have hsum : s + t ≠ 0 := by
    intro hzero
    have hsameScaled : s * (v - u) = 0 := by
      linear_combination hsvut - u * hzero
    have hvu : v = u := by
      have := (mul_eq_zero.mp hsameScaled).resolve_left hs0
      linarith
    exact huv hvu.symm
  exact {
    s := s
    t := t
    u := u
    s_ne_zero := hs0
    s_ne_one := hs1
    sum_ne_zero := hsum
    polynomial_one := hpolyOne
    polynomial_two := hpolyTwo
    polynomial_three := hpolyThree }

/-! ## From the finite normal form to the raw equations -/

/-- The forced finite support dictionary produces the public positive
coordinate certificate.  Thus the sole remaining gap at configuration level
is construction of `FourPentagonFiniteNormalForm` from the five-block count
and local degree row. -/
noncomputable def fourPentagonCoordinateData_of_finiteNormalForm
    {α : Type u} [Fintype α] [DecidableEq α]
    (cfg : Configuration α)
    (N : FourPentagonFiniteNormalForm (blockSystem cfg)) :
    FourPentagonCoordinateData := by
  classical
  let P := N.point
  let p : Fin 10 → Point2 := fun i => cfg (P i)
  let I : Fin 10 → Point2 := fun i =>
    EuclideanGeometry.inversion (p 0) 1 (p i)
  have hp : Function.Injective p := cfg.injective.comp P.injective
  have hIinj : Function.Injective I :=
    (EuclideanGeometry.inversion_injective (p 0) one_ne_zero).comp hp
  have hIne {i j : Fin 10} (hij : i ≠ j) : I i ≠ I j := hIinj.ne hij

  let PB₀ : PivotBlock cfg (P 0) :=
    ⟨N.five 0, (N.mem_five 0 0).2 (by decide),
      by
        change 3 ≤ ((blockSystem cfg).support (N.five 0)).card
        rw [N.five_size]
        omega⟩
  let PB₁ : PivotBlock cfg (P 0) :=
    ⟨N.five 1, (N.mem_five 0 1).2 (by decide),
      by
        change 3 ≤ ((blockSystem cfg).support (N.five 1)).card
        rw [N.five_size]
        omega⟩
  let PB₂ : PivotBlock cfg (P 0) :=
    ⟨N.five 2, (N.mem_five 0 2).2 (by decide),
      by
        change 3 ≤ ((blockSystem cfg).support (N.five 2)).card
        rw [N.five_size]
        omega⟩
  let L₀ := blockToPivotLine cfg (P 0) PB₀
  let L₁ := blockToPivotLine cfg (P 0) PB₁
  let L₂ := blockToPivotLine cfg (P 0) PB₂
  have hL₀ {i : Fin 10} (hi : i ≠ 0)
      (hmem : i ∈ fourPentagonFiveSupport 0) : I i ∈ L₀.1 := by
    let q : AwayFrom (P 0) := ⟨P i, P.injective.ne hi⟩
    have hq : q ∈ lineSupport (pivotInversion cfg (P 0)) L₀ := by
      change q ∈ lineSupport (pivotInversion cfg (P 0))
        (blockToPivotLine cfg (P 0) PB₀)
      rw [lineSupport_blockToPivotLine]
      exact mem_awaySupport.mpr ((N.mem_five i 0).2 hmem)
    simpa [I, p, P, pivotInversion, q] using mem_lineSupport.mp hq
  have hL₁ {i : Fin 10} (hi : i ≠ 0)
      (hmem : i ∈ fourPentagonFiveSupport 1) : I i ∈ L₁.1 := by
    let q : AwayFrom (P 0) := ⟨P i, P.injective.ne hi⟩
    have hq : q ∈ lineSupport (pivotInversion cfg (P 0)) L₁ := by
      change q ∈ lineSupport (pivotInversion cfg (P 0))
        (blockToPivotLine cfg (P 0) PB₁)
      rw [lineSupport_blockToPivotLine]
      exact mem_awaySupport.mpr ((N.mem_five i 1).2 hmem)
    simpa [I, p, P, pivotInversion, q] using mem_lineSupport.mp hq
  have hL₂ {i : Fin 10} (hi : i ≠ 0)
      (hmem : i ∈ fourPentagonFiveSupport 2) : I i ∈ L₂.1 := by
    let q : AwayFrom (P 0) := ⟨P i, P.injective.ne hi⟩
    have hq : q ∈ lineSupport (pivotInversion cfg (P 0)) L₂ := by
      change q ∈ lineSupport (pivotInversion cfg (P 0))
        (blockToPivotLine cfg (P 0) PB₂)
      rw [lineSupport_blockToPivotLine]
      exact mem_awaySupport.mpr ((N.mem_five i 2).2 hmem)
    simpa [I, p, P, pivotInversion, q] using mem_lineSupport.mp hq

  let huExists : ∃ r : ℝ,
      affineParamPoint (I 1) (I 4 - I 1) r = I 2 :=
    exists_affineParamPoint_of_mem_affineLine
      (L := L₀.1) (A := I 1) (B := I 4) (X := I 2)
      L₀.direction_finrank (hIne (by decide))
      (hL₀ (by decide) (by decide)) (hL₀ (by decide) (by decide))
      (hL₀ (by decide) (by decide))
  let u : ℝ := Classical.choose huExists
  have hu : affineParamPoint (I 1) (I 4 - I 1) u = I 2 :=
    Classical.choose_spec huExists
  let hvExists : ∃ r : ℝ,
      affineParamPoint (I 1) (I 4 - I 1) r = I 5 :=
    exists_affineParamPoint_of_mem_affineLine
      (L := L₀.1) (A := I 1) (B := I 4) (X := I 5)
      L₀.direction_finrank (hIne (by decide))
      (hL₀ (by decide) (by decide)) (hL₀ (by decide) (by decide))
      (hL₀ (by decide) (by decide))
  let v : ℝ := Classical.choose hvExists
  have hv : affineParamPoint (I 1) (I 4 - I 1) v = I 5 :=
    Classical.choose_spec hvExists
  let hsExists : ∃ r : ℝ,
      affineParamPoint (I 1) (I 6 - I 1) r = I 3 :=
    exists_affineParamPoint_of_mem_affineLine
      (L := L₁.1) (A := I 1) (B := I 6) (X := I 3)
      L₁.direction_finrank (hIne (by decide))
      (hL₁ (by decide) (by decide)) (hL₁ (by decide) (by decide))
      (hL₁ (by decide) (by decide))
  let s : ℝ := Classical.choose hsExists
  have hs : affineParamPoint (I 1) (I 6 - I 1) s = I 3 :=
    Classical.choose_spec hsExists
  let htExists : ∃ r : ℝ,
      affineParamPoint (I 1) (I 6 - I 1) r = I 7 :=
    exists_affineParamPoint_of_mem_affineLine
      (L := L₁.1) (A := I 1) (B := I 6) (X := I 7)
      L₁.direction_finrank (hIne (by decide))
      (hL₁ (by decide) (by decide)) (hL₁ (by decide) (by decide))
      (hL₁ (by decide) (by decide))
  let t : ℝ := Classical.choose htExists
  have ht : affineParamPoint (I 1) (I 6 - I 1) t = I 7 :=
    Classical.choose_spec htExists
  let hxExists : ∃ r : ℝ,
      affineParamPoint (I 4) (I 6 - I 4) r = I 8 :=
    exists_affineParamPoint_of_mem_affineLine
      (L := L₂.1) (A := I 4) (B := I 6) (X := I 8)
      L₂.direction_finrank (hIne (by decide))
      (hL₂ (by decide) (by decide)) (hL₂ (by decide) (by decide))
      (hL₂ (by decide) (by decide))
  let x : ℝ := Classical.choose hxExists
  have hx : affineParamPoint (I 4) (I 6 - I 4) x = I 8 :=
    Classical.choose_spec hxExists
  let hyExists : ∃ r : ℝ,
      affineParamPoint (I 4) (I 6 - I 4) r = I 9 :=
    exists_affineParamPoint_of_mem_affineLine
      (L := L₂.1) (A := I 4) (B := I 6) (X := I 9)
      L₂.direction_finrank (hIne (by decide))
      (hL₂ (by decide) (by decide)) (hL₂ (by decide) (by decide))
      (hL₂ (by decide) (by decide))
  let y : ℝ := Classical.choose hyExists
  have hy : affineParamPoint (I 4) (I 6 - I 4) y = I 9 :=
    Classical.choose_spec hyExists

  have huv : DistinctSideParameters u v :=
    distinctSideParameters_of_distinct_points
      (hIne (by decide)) (hIne (by decide))
      (hIne (by decide)) (hIne (by decide)) (hIne (by decide)) hu hv
  have hst : DistinctSideParameters s t :=
    distinctSideParameters_of_distinct_points
      (hIne (by decide)) (hIne (by decide))
      (hIne (by decide)) (hIne (by decide)) (hIne (by decide)) hs ht
  have hxy : DistinctSideParameters x y :=
    distinctSideParameters_of_distinct_points
      (hIne (by decide)) (hIne (by decide))
      (hIne (by decide)) (hIne (by decide)) (hIne (by decide)) hx hy

  have htriangleDet :
      Matrix.det ![homogeneousLift (I 1), homogeneousLift (I 4),
        homogeneousLift (I 6)] ≠ 0 := by
    intro hzero
    have hdetZero : det2 (I 4 - I 1) (I 6 - I 1) = 0 := by
      rw [← det_homogeneousLift_eq_det2]
      exact hzero
    obtain ⟨r, hr⟩ := exists_affineParamPoint_of_det2_eq_zero
      (hIne (by decide)) hdetZero
    have hCLine : I 6 ∈ L₀.1 := by
      rw [← hr, affineParamPoint_eq_lineMap]
      exact AffineMap.lineMap_mem r
        (hL₀ (by decide) (by decide)) (hL₀ (by decide) (by decide))
    let q : AwayFrom (P 0) := ⟨P 6, P.injective.ne (by decide)⟩
    have hq : q ∈ lineSupport (pivotInversion cfg (P 0)) L₀ := by
      apply mem_lineSupport.mpr
      simpa [q, pivotInversion, I, p, P] using hCLine
    change q ∈ lineSupport (pivotInversion cfg (P 0))
      (blockToPivotLine cfg (P 0) PB₀) at hq
    rw [lineSupport_blockToPivotLine] at hq
    have hbad := (N.mem_five 6 0).mp (mem_awaySupport.mp hq)
    revert hbad
    decide
  have hdet : det2 (I 4 - I 1) (I 6 - I 1) ≠ 0 := by
    rw [← det_homogeneousLift_eq_det2]
    exact htriangleDet

  let QB₀ : PivotBlock cfg (P 0) :=
    ⟨N.four 0, (N.mem_four 0 0).2 (by decide),
      by
        change 3 ≤ ((blockSystem cfg).support (N.four 0)).card
        rw [N.four_size]
        omega⟩
  let QB₁ : PivotBlock cfg (P 0) :=
    ⟨N.four 1, (N.mem_four 0 1).2 (by decide),
      by
        change 3 ≤ ((blockSystem cfg).support (N.four 1)).card
        rw [N.four_size]
        omega⟩
  let QB₂ : PivotBlock cfg (P 0) :=
    ⟨N.four 2, (N.mem_four 0 2).2 (by decide),
      by
        change 3 ≤ ((blockSystem cfg).support (N.four 2)).card
        rw [N.four_size]
        omega⟩
  let K₀ := blockToPivotLine cfg (P 0) QB₀
  let K₁ := blockToPivotLine cfg (P 0) QB₁
  let K₂ := blockToPivotLine cfg (P 0) QB₂
  have hK₀ {i : Fin 10} (hi : i ≠ 0)
      (hmem : i ∈ fourPentagonRequiredFourSupport 0) : I i ∈ K₀.1 := by
    let q : AwayFrom (P 0) := ⟨P i, P.injective.ne hi⟩
    have hq : q ∈ lineSupport (pivotInversion cfg (P 0)) K₀ := by
      change q ∈ lineSupport (pivotInversion cfg (P 0))
        (blockToPivotLine cfg (P 0) QB₀)
      rw [lineSupport_blockToPivotLine]
      exact mem_awaySupport.mpr ((N.mem_four i 0).2 hmem)
    simpa [I, p, P, pivotInversion, q] using mem_lineSupport.mp hq
  have hK₁ {i : Fin 10} (hi : i ≠ 0)
      (hmem : i ∈ fourPentagonRequiredFourSupport 1) : I i ∈ K₁.1 := by
    let q : AwayFrom (P 0) := ⟨P i, P.injective.ne hi⟩
    have hq : q ∈ lineSupport (pivotInversion cfg (P 0)) K₁ := by
      change q ∈ lineSupport (pivotInversion cfg (P 0))
        (blockToPivotLine cfg (P 0) QB₁)
      rw [lineSupport_blockToPivotLine]
      exact mem_awaySupport.mpr ((N.mem_four i 1).2 hmem)
    simpa [I, p, P, pivotInversion, q] using mem_lineSupport.mp hq
  have hK₂ {i : Fin 10} (hi : i ≠ 0)
      (hmem : i ∈ fourPentagonRequiredFourSupport 2) : I i ∈ K₂.1 := by
    let q : AwayFrom (P 0) := ⟨P i, P.injective.ne hi⟩
    have hq : q ∈ lineSupport (pivotInversion cfg (P 0)) K₂ := by
      change q ∈ lineSupport (pivotInversion cfg (P 0))
        (blockToPivotLine cfg (P 0) QB₂)
      rw [lineSupport_blockToPivotLine]
      exact mem_awaySupport.mpr ((N.mem_four i 2).2 hmem)
    simpa [I, p, P, pivotInversion, q] using mem_lineSupport.mp hq

  let hρExists : ∃ r : ℝ,
      affineParamPoint (I 2) (I 3 - I 2) r = I 8 :=
    exists_affineParamPoint_of_mem_affineLine
      (L := K₀.1) (A := I 2) (B := I 3) (X := I 8)
      K₀.direction_finrank (hIne (by decide))
      (hK₀ (by decide) (by decide)) (hK₀ (by decide) (by decide))
      (hK₀ (by decide) (by decide))
  let ρ : ℝ := Classical.choose hρExists
  have hρ : affineParamPoint (I 2) (I 3 - I 2) ρ = I 8 :=
    Classical.choose_spec hρExists
  let hσExists : ∃ r : ℝ,
      affineParamPoint (I 2) (I 7 - I 2) r = I 9 :=
    exists_affineParamPoint_of_mem_affineLine
      (L := K₁.1) (A := I 2) (B := I 7) (X := I 9)
      K₁.direction_finrank (hIne (by decide))
      (hK₁ (by decide) (by decide)) (hK₁ (by decide) (by decide))
      (hK₁ (by decide) (by decide))
  let σ : ℝ := Classical.choose hσExists
  have hσ : affineParamPoint (I 2) (I 7 - I 2) σ = I 9 :=
    Classical.choose_spec hσExists
  let hτExists : ∃ r : ℝ,
      affineParamPoint (I 5) (I 3 - I 5) r = I 9 :=
    exists_affineParamPoint_of_mem_affineLine
      (L := K₂.1) (A := I 5) (B := I 3) (X := I 9)
      K₂.direction_finrank (hIne (by decide))
      (hK₂ (by decide) (by decide)) (hK₂ (by decide) (by decide))
      (hK₂ (by decide) (by decide))
  let τ : ℝ := Classical.choose hτExists
  have hτ : affineParamPoint (I 5) (I 3 - I 5) τ = I 9 :=
    Classical.choose_spec hτExists

  have hmenXRaw := menelaus_parameter_equation hdet hu hs hx hρ
  have hmenYRaw := menelaus_parameter_equation hdet hu ht hy hσ
  have hmenY'Raw := menelaus_parameter_equation hdet hv hs hy hτ
  have hmenX : (u - s) * x - s * (u - 1) = 0 := by
    linear_combination hmenXRaw
  have hmenY : (u - t) * y - t * (u - 1) = 0 := by
    linear_combination hmenYRaw
  have hmenY' : (v - s) * y - s * (v - 1) = 0 := by
    linear_combination hmenY'Raw

  have hBaseO : P 0 ∉ geometricBlockSupport cfg (N.five 3) := by
    intro h
    have hbad := (N.mem_five 0 3).mp h
    revert hbad
    decide
  have hΓFO : P 0 ∉ geometricBlockSupport cfg (N.four 3) := by
    intro h
    have hbad := (N.mem_four 0 3).mp h
    revert hbad
    decide
  have hΓCO : P 0 ∉ geometricBlockSupport cfg (N.four 4) := by
    intro h
    have hbad := (N.mem_four 0 4).mp h
    revert hbad
    decide
  have hΓBO : P 0 ∉ geometricBlockSupport cfg (N.four 5) := by
    intro h
    have hbad := (N.mem_four 0 5).mp h
    revert hbad
    decide
  have hLastO : P 0 ∉ geometricBlockSupport cfg (N.four 6) := by
    intro h
    have hbad := (N.mem_four 0 6).mp h
    revert hbad
    decide
  let ΓBase := invertedAwayGeometricBlockCircle cfg (P 0) (N.five 3) hBaseO
  let ΓF := invertedAwayGeometricBlockCircle cfg (P 0) (N.four 3) hΓFO
  let ΓC := invertedAwayGeometricBlockCircle cfg (P 0) (N.four 4) hΓCO
  let ΓB := invertedAwayGeometricBlockCircle cfg (P 0) (N.four 5) hΓBO
  let ΓLast := invertedAwayGeometricBlockCircle cfg (P 0) (N.four 6) hLastO
  have hBase {i : Fin 10} (hi : i ∈ fourPentagonFiveSupport 3) :
      I i ∈ (ΓBase.1 : Set Point2) := by
    simpa [I, p, P, ΓBase] using
      inversion_mem_invertedAwayGeometricBlockCircle
        cfg (P 0) (N.five 3) hBaseO (P i) ((N.mem_five i 3).2 hi)
  have hΓF {i : Fin 10} (hi : i ∈ fourPentagonRequiredFourSupport 3) :
      I i ∈ (ΓF.1 : Set Point2) := by
    simpa [I, p, P, ΓF] using
      inversion_mem_invertedAwayGeometricBlockCircle
        cfg (P 0) (N.four 3) hΓFO (P i) ((N.mem_four i 3).2 hi)
  have hΓC {i : Fin 10} (hi : i ∈ fourPentagonRequiredFourSupport 4) :
      I i ∈ (ΓC.1 : Set Point2) := by
    simpa [I, p, P, ΓC] using
      inversion_mem_invertedAwayGeometricBlockCircle
        cfg (P 0) (N.four 4) hΓCO (P i) ((N.mem_four i 4).2 hi)
  have hΓB {i : Fin 10} (hi : i ∈ fourPentagonRequiredFourSupport 5) :
      I i ∈ (ΓB.1 : Set Point2) := by
    simpa [I, p, P, ΓB] using
      inversion_mem_invertedAwayGeometricBlockCircle
        cfg (P 0) (N.four 5) hΓBO (P i) ((N.mem_four i 5).2 hi)
  have hLast {i : Fin 10} (hi : i ∈ fourPentagonRequiredFourSupport 6) :
      I i ∈ (ΓLast.1 : Set Point2) := by
    simpa [I, p, P, ΓLast] using
      inversion_mem_invertedAwayGeometricBlockCircle
        cfg (P 0) (N.four 6) hLastO (P i) ((N.mem_four i 6).2 hi)

  have hBaseA : I 1 ∈ (ΓBase.1 : Set Point2) := hBase (by decide)
  have hBaseV : affineParamPoint (I 1) (I 4 - I 1) v ∈
      (ΓBase.1 : Set Point2) := by rw [hv]; exact hBase (by decide)
  have hBaseT : affineParamPoint (I 1) (I 6 - I 1) t ∈
      (ΓBase.1 : Set Point2) := by rw [ht]; exact hBase (by decide)
  have hBaseX : affineParamPoint (I 4) (I 6 - I 4) x ∈
      (ΓBase.1 : Set Point2) := by rw [hx]; exact hBase (by decide)
  have hBaseY : affineParamPoint (I 4) (I 6 - I 4) y ∈
      (ΓBase.1 : Set Point2) := by rw [hy]; exact hBase (by decide)
  have hΓFA : I 1 ∈ (ΓF.1 : Set Point2) := hΓF (by decide)
  have hΓFU : affineParamPoint (I 1) (I 4 - I 1) u ∈
      (ΓF.1 : Set Point2) := by rw [hu]; exact hΓF (by decide)
  have hΓFS : affineParamPoint (I 1) (I 6 - I 1) s ∈
      (ΓF.1 : Set Point2) := by rw [hs]; exact hΓF (by decide)
  have hΓFY : affineParamPoint (I 4) (I 6 - I 4) y ∈
      (ΓF.1 : Set Point2) := by rw [hy]; exact hΓF (by decide)
  have hΓCA : I 1 ∈ (ΓC.1 : Set Point2) := hΓC (by decide)
  have hΓCU : affineParamPoint (I 1) (I 4 - I 1) u ∈
      (ΓC.1 : Set Point2) := by rw [hu]; exact hΓC (by decide)
  have hΓCC : affineParamPoint (I 1) (I 6 - I 1) 1 ∈
      (ΓC.1 : Set Point2) := by
    rw [affineParamPoint_endpoint]
    exact hΓC (by decide)
  have hΓCX : affineParamPoint (I 4) (I 6 - I 4) x ∈
      (ΓC.1 : Set Point2) := by rw [hx]; exact hΓC (by decide)
  have hΓBA : I 1 ∈ (ΓB.1 : Set Point2) := hΓB (by decide)
  have hΓBB : affineParamPoint (I 1) (I 4 - I 1) 1 ∈
      (ΓB.1 : Set Point2) := by
    rw [affineParamPoint_endpoint]
    exact hΓB (by decide)
  have hΓBS : affineParamPoint (I 1) (I 6 - I 1) s ∈
      (ΓB.1 : Set Point2) := by rw [hs]; exact hΓB (by decide)
  have hΓBX : affineParamPoint (I 4) (I 6 - I 4) x ∈
      (ΓB.1 : Set Point2) := by rw [hx]; exact hΓB (by decide)
  have hLastB : affineParamPoint (I 1) (I 4 - I 1) 1 ∈
      (ΓLast.1 : Set Point2) := by
    rw [affineParamPoint_endpoint]
    exact hLast (by decide)
  have hLastV : affineParamPoint (I 1) (I 4 - I 1) v ∈
      (ΓLast.1 : Set Point2) := by rw [hv]; exact hLast (by decide)
  have hLastC : affineParamPoint (I 1) (I 6 - I 1) 1 ∈
      (ΓLast.1 : Set Point2) := by
    rw [affineParamPoint_endpoint]
    exact hLast (by decide)
  have hLastT : affineParamPoint (I 1) (I 6 - I 1) t ∈
      (ΓLast.1 : Set Point2) := by rw [ht]; exact hLast (by decide)

  have hu0 : u ≠ 0 := huv.1
  have hv0 : v ≠ 0 := huv.2.2.1
  have hv1 : v ≠ 1 := huv.2.2.2.1
  have hs0 : s ≠ 0 := hst.1
  have ht0 : t ≠ 0 := hst.2.2.1
  have ht1 : t ≠ 1 := hst.2.2.2.1
  have hpowOne := circle_difference_on_opposite_side
    (I 1) (I 4) (I 6) ΓBase ΓC
    hv0 ht0 hu0 one_ne_zero
    hBaseA hBaseV hBaseT hBaseX hΓCA hΓCU hΓCC hΓCX
  have hpowTwo := circle_difference_on_opposite_side
    (I 1) (I 4) (I 6) ΓBase ΓB
    hv0 ht0 one_ne_zero hs0
    hBaseA hBaseV hBaseT hBaseX hΓBA hΓBB hΓBS hΓBX
  have hpowThree := circle_difference_on_opposite_side
    (I 1) (I 4) (I 6) ΓBase ΓF
    hv0 ht0 hu0 hs0
    hBaseA hBaseV hBaseT hBaseY hΓFA hΓFU hΓFS hΓFY
  have hpowLastRaw := directed_power_of_four_cocircular_points
    ΓLast (I 1) (I 4 - I 1) (I 6 - I 1)
    (show (1 : ℝ) ≠ v by exact hv1.symm)
    (show (1 : ℝ) ≠ t by exact ht1.symm)
    hLastB hLastV hLastC hLastT
  have hpowLast :
      directionSq (I 4 - I 1) * v -
        directionSq (I 6 - I 1) * t = 0 := by
    linear_combination hpowLastRaw

  exact fourPentagonCoordinateData_of_raw_equations
    (directionSq_sub_ne_zero (hIne (by decide)))
    (directionSq_sub_ne_zero (hIne (by decide)))
    huv hst hxy hmenX hmenY hmenY'
    hpowOne hpowTwo hpowThree hpowLast

/-- Configuration-level four-pentagon coordinates.  The finite normal form
is constructed from the raw block hypotheses before the geometric coordinate
argument is applied. -/
noncomputable def finite_fourPentagonCoordinates
    {α : Type u} [Fintype α] [DecidableEq α]
    (cfg : Configuration α)
    (_hadm : Admissible cfg)
    (hcard : Fintype.card α = 10)
    (hcap : BlockSizeCap (blockSystem cfg) 5)
    (hd3 : ∀ p : α, (blockSystem cfg).blockDegree 3 p = 6 ∨
      (blockSystem cfg).blockDegree 3 p = 9)
    (hfour : (blockSystem cfg).blockCount 5 = 4) :
    FourPentagonCoordinateData :=
  fourPentagonCoordinateData_of_finiteNormalForm cfg
    (fourPentagonFiniteNormalForm (blockSystem cfg)
      hcard hcap hd3 hfour)

end Erdos506.V1
