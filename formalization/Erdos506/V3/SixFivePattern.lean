import Erdos506.V3.InversionLine
import Erdos506.V3.TrianglePower
import Erdos506.Finite.SixFiveCanonical

/-!
# Non-realizability of the canonical six-five design

The ten rows below are the unique incidence pattern forced by equality in
the six-block packing bound.  This module proves directly that no injective
real-plane realization of that pattern by six proper circles exists.
-/

namespace Erdos506.V3

open Erdos506.V4
open Erdos506.Finite

abbrev sixFivePointProfile : Fin 10 → Finset (Fin 6) :=
  sixFiveCanonicalProfile

theorem canonical_six_five_pattern_not_realizable
    (p : Fin 10 → Point2) (hp : Function.Injective p)
    (Γ : Fin 6 → ProperCircle)
    (hinc : ∀ i j, p i ∈ ((Γ j).1 : Set Point2) ↔
      j ∈ sixFivePointProfile i) : False := by
  have hmem {i : Fin 10} {j : Fin 6}
      (h : j ∈ sixFivePointProfile i) :
      p i ∈ ((Γ j).1 : Set Point2) :=
    (hinc i j).mpr h
  have hnmem {i : Fin 10} {j : Fin 6}
      (h : j ∉ sixFivePointProfile i) :
      p i ∉ ((Γ j).1 : Set Point2) := by
    intro hij
    exact h ((hinc i j).mp hij)
  let I : Fin 10 → Point2 := fun i =>
    EuclideanGeometry.inversion (p 0) 1 (p i)
  have hIinj : Function.Injective I :=
    (EuclideanGeometry.inversion_injective (p 0) one_ne_zero).comp hp
  have hpne {i j : Fin 10} (hij : i ≠ j) : p i ≠ p j := hp.ne hij
  have hIne {i j : Fin 10} (hij : i ≠ j) : I i ≠ I j := hIinj.ne hij

  obtain ⟨x, hx⟩ := exists_affineParamPoint_after_inversion_of_circle
    (o := p 0) (a := p 1) (b := p 2) (x := p 4) (Γ 0)
    (hpne (by decide)) (hpne (by decide)) (hpne (by decide))
    (hpne (by decide))
    (hmem (by decide)) (hmem (by decide)) (hmem (by decide))
    (hmem (by decide))
  obtain ⟨y, hy⟩ := exists_affineParamPoint_after_inversion_of_circle
    (o := p 0) (a := p 1) (b := p 2) (x := p 5) (Γ 0)
    (hpne (by decide)) (hpne (by decide)) (hpne (by decide))
    (hpne (by decide))
    (hmem (by decide)) (hmem (by decide)) (hmem (by decide))
    (hmem (by decide))
  obtain ⟨u, hu⟩ := exists_affineParamPoint_after_inversion_of_circle
    (o := p 0) (a := p 1) (b := p 3) (x := p 6) (Γ 1)
    (hpne (by decide)) (hpne (by decide)) (hpne (by decide))
    (hpne (by decide))
    (hmem (by decide)) (hmem (by decide)) (hmem (by decide))
    (hmem (by decide))
  obtain ⟨v, hv⟩ := exists_affineParamPoint_after_inversion_of_circle
    (o := p 0) (a := p 1) (b := p 3) (x := p 7) (Γ 1)
    (hpne (by decide)) (hpne (by decide)) (hpne (by decide))
    (hpne (by decide))
    (hmem (by decide)) (hmem (by decide)) (hmem (by decide))
    (hmem (by decide))
  obtain ⟨w, hw⟩ := exists_affineParamPoint_after_inversion_of_circle
    (o := p 0) (a := p 2) (b := p 3) (x := p 8) (Γ 2)
    (hpne (by decide)) (hpne (by decide)) (hpne (by decide))
    (hpne (by decide))
    (hmem (by decide)) (hmem (by decide)) (hmem (by decide))
    (hmem (by decide))
  obtain ⟨z, hz⟩ := exists_affineParamPoint_after_inversion_of_circle
    (o := p 0) (a := p 2) (b := p 3) (x := p 9) (Γ 2)
    (hpne (by decide)) (hpne (by decide)) (hpne (by decide))
    (hpne (by decide))
    (hmem (by decide)) (hmem (by decide)) (hmem (by decide))
    (hmem (by decide))
  change affineParamPoint (I 1) (I 2 - I 1) x = I 4 at hx
  change affineParamPoint (I 1) (I 2 - I 1) y = I 5 at hy
  change affineParamPoint (I 1) (I 3 - I 1) u = I 6 at hu
  change affineParamPoint (I 1) (I 3 - I 1) v = I 7 at hv
  change affineParamPoint (I 2) (I 3 - I 2) w = I 8 at hw
  change affineParamPoint (I 2) (I 3 - I 2) z = I 9 at hz
  have hxy : DistinctSideParameters x y :=
    distinctSideParameters_of_distinct_points
      (hIne (by decide)) (hIne (by decide))
      (hIne (by decide)) (hIne (by decide)) (hIne (by decide)) hx hy
  have huv : DistinctSideParameters u v :=
    distinctSideParameters_of_distinct_points
      (hIne (by decide)) (hIne (by decide))
      (hIne (by decide)) (hIne (by decide)) (hIne (by decide)) hu hv
  have hwz : DistinctSideParameters w z :=
    distinctSideParameters_of_distinct_points
      (hIne (by decide)) (hIne (by decide))
      (hIne (by decide)) (hIne (by decide)) (hIne (by decide)) hw hz

  have hO4 : p 0 ∉ ((Γ 3).1 : Set Point2) := hnmem (by decide)
  have hO5 : p 0 ∉ ((Γ 4).1 : Set Point2) := hnmem (by decide)
  have hO6 : p 0 ∉ ((Γ 5).1 : Set Point2) := hnmem (by decide)
  let Γ₄ := invertedProperCircle (p 0) (Γ 3) hO4
  let Γ₅ := invertedProperCircle (p 0) (Γ 4) hO5
  let Γ₆ := invertedProperCircle (p 0) (Γ 5) hO6
  have hG4 {i : Fin 10} (hi : (3 : Fin 6) ∈ sixFivePointProfile i) :
      I i ∈ (Γ₄.1 : Set Point2) := by
    exact inversion_mem_invertedProperCircle (p 0) (p i) (Γ 3) hO4
      (hmem hi)
  have hG5 {i : Fin 10} (hi : (4 : Fin 6) ∈ sixFivePointProfile i) :
      I i ∈ (Γ₅.1 : Set Point2) := by
    exact inversion_mem_invertedProperCircle (p 0) (p i) (Γ 4) hO5
      (hmem hi)
  have hG6 {i : Fin 10} (hi : (5 : Fin 6) ∈ sixFivePointProfile i) :
      I i ∈ (Γ₆.1 : Set Point2) := by
    exact inversion_mem_invertedProperCircle (p 0) (p i) (Γ 5) hO6
      (hmem hi)
  apply no_six_five_triangle_pattern (I 1) (I 2) (I 3)
    (hIne (by decide)) (hIne (by decide)) (hIne (by decide))
    hxy huv hwz Γ₄ Γ₅ Γ₆
  · exact hG4 (by decide)
  · rw [hx]
    exact hG4 (by decide)
  · rw [hu]
    exact hG4 (by decide)
  · rw [hw]
    exact hG4 (by decide)
  · rw [hz]
    exact hG4 (by decide)
  · exact hG5 (by decide)
  · rw [hy]
    exact hG5 (by decide)
  · rw [hu]
    exact hG5 (by decide)
  · rw [hv]
    exact hG5 (by decide)
  · rw [hw]
    exact hG5 (by decide)
  · exact hG6 (by decide)
  · rw [hx]
    exact hG6 (by decide)
  · rw [hy]
    exact hG6 (by decide)
  · rw [hv]
    exact hG6 (by decide)
  · rw [hz]
    exact hG6 (by decide)

end Erdos506.V3
