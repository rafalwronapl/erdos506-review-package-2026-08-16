import Erdos506.V3.InversionLine
import Erdos506.V3.MenelausPower

/-!
# Non-realizability of the canonical Fano circle pattern

The seven supports below are complements of the seven Fano lines.  Inverting
at point `6` turns four of the circles into the four lines of a complete
quadrilateral.  Menelaus for one line and directed power for the remaining
three circles give opposite signs for the same nonzero product.
-/

namespace Erdos506.V3

open Erdos506.V4
open AffineSubspace

def fanoCircleSupport : Fin 7 → Finset (Fin 7) := ![
  {3, 4, 5, 6},
  {1, 2, 5, 6},
  {1, 2, 3, 4},
  {0, 2, 4, 6},
  {0, 2, 3, 5},
  {0, 1, 4, 5},
  {0, 1, 3, 6}
]

set_option maxHeartbeats 0 in
theorem canonical_fano_circle_pattern_not_realizable
    (p : Fin 7 → Point2) (hp : Function.Injective p)
    (Γ : Fin 7 → ProperCircle)
    (hinc : ∀ i j, p i ∈ ((Γ j).1 : Set Point2) ↔
      i ∈ fanoCircleSupport j) : False := by
  have hmem {i j : Fin 7} (h : i ∈ fanoCircleSupport j) :
      p i ∈ ((Γ j).1 : Set Point2) := (hinc i j).mpr h
  have hnmem {i j : Fin 7} (h : i ∉ fanoCircleSupport j) :
      p i ∉ ((Γ j).1 : Set Point2) := by
    intro hi
    exact h ((hinc i j).mp hi)
  let I : Fin 7 → Point2 := fun i =>
    EuclideanGeometry.inversion (p 6) 1 (p i)
  have hIinj : Function.Injective I :=
    (EuclideanGeometry.inversion_injective (p 6) one_ne_zero).comp hp
  have hpne {i j : Fin 7} (hij : i ≠ j) : p i ≠ p j := hp.ne hij
  have hIne {i j : Fin 7} (hij : i ≠ j) : I i ≠ I j := hIinj.ne hij

  obtain ⟨x, hx⟩ := exists_affineParamPoint_after_inversion_of_circle
    (o := p 6) (a := p 5) (b := p 4) (x := p 3) (Γ 0)
    (hpne (by decide)) (hpne (by decide)) (hpne (by decide))
    (hpne (by decide))
    (hmem (by decide)) (hmem (by decide)) (hmem (by decide))
    (hmem (by decide))
  obtain ⟨u, hu⟩ := exists_affineParamPoint_after_inversion_of_circle
    (o := p 6) (a := p 5) (b := p 2) (x := p 1) (Γ 1)
    (hpne (by decide)) (hpne (by decide)) (hpne (by decide))
    (hpne (by decide))
    (hmem (by decide)) (hmem (by decide)) (hmem (by decide))
    (hmem (by decide))
  obtain ⟨w, hw⟩ := exists_affineParamPoint_after_inversion_of_circle
    (o := p 6) (a := p 4) (b := p 2) (x := p 0) (Γ 3)
    (hpne (by decide)) (hpne (by decide)) (hpne (by decide))
    (hpne (by decide))
    (hmem (by decide)) (hmem (by decide)) (hmem (by decide))
    (hmem (by decide))
  obtain ⟨t, ht⟩ := exists_affineParamPoint_after_inversion_of_circle
    (o := p 6) (a := p 3) (b := p 1) (x := p 0) (Γ 6)
    (hpne (by decide)) (hpne (by decide)) (hpne (by decide))
    (hpne (by decide))
    (hmem (by decide)) (hmem (by decide)) (hmem (by decide))
    (hmem (by decide))
  change affineParamPoint (I 5) (I 4 - I 5) x = I 3 at hx
  change affineParamPoint (I 5) (I 2 - I 5) u = I 1 at hu
  change affineParamPoint (I 4) (I 2 - I 4) w = I 0 at hw
  change affineParamPoint (I 3) (I 1 - I 3) t = I 0 at ht
  have hxends := sideParameter_ne_endpoints_of_distinct_point
    (hIne (by decide)) (hIne (by decide)) hx
  have huends := sideParameter_ne_endpoints_of_distinct_point
    (hIne (by decide)) (hIne (by decide)) hu
  have hwends := sideParameter_ne_endpoints_of_distinct_point
    (hIne (by decide)) (hIne (by decide)) hw
  have hOneSubX : 1 - x ≠ 1 := by
    intro h
    apply hxends.1
    linarith
  have hOneSubU : 1 - u ≠ 1 := by
    intro h
    apply huends.1
    linarith
  have hOneSubW : 1 - w ≠ 1 := by
    intro h
    apply hwends.1
    linarith

  have hdet : det2 (I 4 - I 5) (I 2 - I 5) ≠ 0 := by
    intro hzero
    obtain ⟨r, hr⟩ := exists_affineParamPoint_of_det2_eq_zero
      (hIne (by decide)) hzero
    have hline : I 2 ∈ line[ℝ, I 5, I 4] := by
      apply mem_affineSpan_pair_iff_exists_lineMap_eq.mpr
      exact ⟨r, (affineParamPoint_eq_lineMap (I 5) (I 4) r).symm.trans hr⟩
    let q := EuclideanGeometry.inversion (p 6) 1 (Γ 0).1.center
    have hA : I 5 ∈ perpBisector (p 6) q :=
      inversion_mem_perpBisector_of_mem_circle_through_center
        (p 6) (p 5) (Γ 0) (hpne (by decide))
        (hmem (by decide)) (hmem (by decide))
    have hB : I 4 ∈ perpBisector (p 6) q :=
      inversion_mem_perpBisector_of_mem_circle_through_center
        (p 6) (p 4) (Γ 0) (hpne (by decide))
        (hmem (by decide)) (hmem (by decide))
    have hCperp : I 2 ∈ perpBisector (p 6) q :=
      (affineSpan_pair_le_of_mem_of_mem hA hB) hline
    have hCcircle : p 2 ∈ ((Γ 0).1 : Set Point2) :=
      (mem_circle_through_center_iff_inversion_mem_perpBisector
        (p 6) (p 2) (Γ 0) (hpne (by decide)) (hmem (by decide))).mpr hCperp
    exact hnmem (by decide) hCcircle
  have hmen : u * (1 - x) * (1 - w) + x * w * (1 - u) = 0 :=
    menelaus_parameter_equation hdet hx hu hw ht

  have hO2 : p 6 ∉ ((Γ 2).1 : Set Point2) := hnmem (by decide)
  have hO4 : p 6 ∉ ((Γ 4).1 : Set Point2) := hnmem (by decide)
  have hO5 : p 6 ∉ ((Γ 5).1 : Set Point2) := hnmem (by decide)
  let Γ₂ := invertedProperCircle (p 6) (Γ 2) hO2
  let Γ₄ := invertedProperCircle (p 6) (Γ 4) hO4
  let Γ₅ := invertedProperCircle (p 6) (Γ 5) hO5
  have hG2 {i : Fin 7} (hi : i ∈ fanoCircleSupport 2) :
      I i ∈ (Γ₂.1 : Set Point2) :=
    inversion_mem_invertedProperCircle (p 6) (p i) (Γ 2) hO2 (hmem hi)
  have hG4 {i : Fin 7} (hi : i ∈ fanoCircleSupport 4) :
      I i ∈ (Γ₄.1 : Set Point2) :=
    inversion_mem_invertedProperCircle (p 6) (p i) (Γ 4) hO4 (hmem hi)
  have hG5 {i : Fin 7} (hi : i ∈ fanoCircleSupport 5) :
      I i ∈ (Γ₅.1 : Set Point2) :=
    inversion_mem_invertedProperCircle (p 6) (p i) (Γ 5) hO5 (hmem hi)

  have hpow₁ : directionSq (I 4 - I 5) * x =
      directionSq (I 2 - I 5) * u := by
    have h := directed_power_of_four_cocircular_points Γ₂ (I 5)
      (I 4 - I 5) (I 2 - I 5)
      hxends.2 huends.2
      (by rw [hx]; exact hG2 (by decide))
      (by simp; exact hG2 (by decide))
      (by rw [hu]; exact hG2 (by decide))
      (by simp; exact hG2 (by decide))
    simpa using h
  have hpow₂ : directionSq (I 4 - I 5) * (1 - x) =
      directionSq (I 2 - I 4) * w := by
    have h := directed_power_of_four_cocircular_points Γ₄ (I 4)
      (I 5 - I 4) (I 2 - I 4)
      (t₁ := 1 - x) (t₂ := 1) (s₁ := w) (s₂ := 1)
      hOneSubX hwends.2
      (by rw [affineParamPoint_reverse, hx]; exact hG4 (by decide))
      (by simp; exact hG4 (by decide))
      (by rw [hw]; exact hG4 (by decide))
      (by simp; exact hG4 (by decide))
    simpa [directionSq_sub_comm] using h
  have hpow₃ : directionSq (I 2 - I 5) * (1 - u) =
      directionSq (I 2 - I 4) * (1 - w) := by
    have h := directed_power_of_four_cocircular_points Γ₅ (I 2)
      (I 5 - I 2) (I 4 - I 2)
      (t₁ := 1 - u) (t₂ := 1) (s₁ := 1 - w) (s₂ := 1)
      hOneSubU hOneSubW
      (by rw [affineParamPoint_reverse, hu]; exact hG5 (by decide))
      (by simp; exact hG5 (by decide))
      (by rw [affineParamPoint_reverse, hw]; exact hG5 (by decide))
      (by simp; exact hG5 (by decide))
    simpa [directionSq_sub_comm] using h
  exact no_menelaus_three_power_pattern
    (directionSq_sub_ne_zero (hIne (by decide)))
    (directionSq_sub_ne_zero (hIne (by decide)))
    huends.1 hxends.2 hwends.2 hmen hpow₁ hpow₂ hpow₃

end Erdos506.V3
