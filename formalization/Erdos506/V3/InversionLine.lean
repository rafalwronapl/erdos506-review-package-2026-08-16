import Erdos506.V3.CircleInversion
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional

/-!
# Parametrising a line obtained by inversion

In the real two-dimensional Euclidean space a perpendicular bisector is an
affine line.  Consequently, two distinct points on it parametrise every
other point on it.  This is the linear-algebra bridge from Mathlib's
line/circle inversion theorem to the directed parameters used in V3.
-/

namespace Erdos506.V3

open Erdos506.V4
open AffineSubspace
open scoped EuclideanSpace

theorem affineParamPoint_eq_lineMap (p q : Point2) (t : ℝ) :
    affineParamPoint p (q - p) t = AffineMap.lineMap p q t := by
  simp [affineParamPoint, AffineMap.lineMap_apply]
  abel

theorem mem_affineSpan_pair_of_mem_perpBisector
    {o q a b x : Point2} (hoq : o ≠ q) (hab : a ≠ b)
    (ha : a ∈ perpBisector o q) (hb : b ∈ perpBisector o q)
    (hx : x ∈ perpBisector o q) :
    x ∈ line[ℝ, a, b] := by
  let p : AffineSubspace ℝ Point2 := perpBisector o q
  let l : AffineSubspace ℝ Point2 := line[ℝ, a, b]
  have hle : l ≤ p := affineSpan_pair_le_of_mem_of_mem ha hb
  have hdirle : l.direction ≤ p.direction := AffineSubspace.direction_le hle
  have hlfin : Module.finrank ℝ l.direction = 1 := by
    dsimp [l]
    rw [direction_affineSpan ℝ ({a, b} : Set Point2),
      vectorSpan_pair_rev]
    exact finrank_span_singleton (sub_ne_zero.mpr hab.symm)
  have hpfin : Module.finrank ℝ p.direction = 1 := by
    dsimp [p]
    rw [direction_perpBisector]
    exact Submodule.finrank_orthogonal_span_singleton
      (sub_ne_zero.mpr hoq.symm)
  have hdirection : l.direction = p.direction :=
    Submodule.eq_of_le_of_finrank_eq hdirle (hlfin.trans hpfin.symm)
  have hlp : l = p := AffineSubspace.eq_of_direction_eq_of_nonempty_of_le
    hdirection ⟨a, left_mem_affineSpan_pair ℝ a b⟩ hle
  change x ∈ l
  rw [hlp]
  exact hx

theorem exists_affineParamPoint_of_mem_perpBisector
    {o q a b x : Point2} (hoq : o ≠ q) (hab : a ≠ b)
    (ha : a ∈ perpBisector o q) (hb : b ∈ perpBisector o q)
    (hx : x ∈ perpBisector o q) :
    ∃ t : ℝ, affineParamPoint a (b - a) t = x := by
  obtain ⟨t, ht⟩ := mem_affineSpan_pair_iff_exists_lineMap_eq.mp
    (mem_affineSpan_pair_of_mem_perpBisector hoq hab ha hb hx)
  exact ⟨t, (affineParamPoint_eq_lineMap a b t).trans ht⟩

theorem properCircle_center_ne_of_mem (o : Point2) (c : ProperCircle)
    (ho : o ∈ (c.1 : Set Point2)) : c.1.center ≠ o := by
  have hd := EuclideanGeometry.mem_sphere'.mp ho
  change dist c.1.center o = c.1.radius at hd
  intro h
  rw [h, dist_self] at hd
  linarith [c.2]

theorem inversion_mem_perpBisector_of_mem_circle_through_center
    (o x : Point2) (c : ProperCircle) (hxo : x ≠ o)
    (ho : o ∈ (c.1 : Set Point2)) (hx : x ∈ (c.1 : Set Point2)) :
    EuclideanGeometry.inversion o 1 x ∈
      perpBisector o (EuclideanGeometry.inversion o 1 c.1.center) := by
  have hcne := properCircle_center_ne_of_mem o c ho
  apply (EuclideanGeometry.inversion_mem_perpBisector_inversion_iff
    one_ne_zero hxo hcne).mpr
  have hdx := EuclideanGeometry.mem_sphere'.mp hx
  have hdo := EuclideanGeometry.mem_sphere'.mp ho
  change dist c.1.center x = c.1.radius at hdx
  change dist c.1.center o = c.1.radius at hdo
  calc
    dist x c.1.center = dist c.1.center x := dist_comm _ _
    _ = c.1.radius := hdx
    _ = dist c.1.center o := hdo.symm

theorem mem_circle_through_center_iff_inversion_mem_perpBisector
    (o x : Point2) (c : ProperCircle) (hxo : x ≠ o)
    (ho : o ∈ (c.1 : Set Point2)) :
    x ∈ (c.1 : Set Point2) ↔
      EuclideanGeometry.inversion o 1 x ∈
        perpBisector o (EuclideanGeometry.inversion o 1 c.1.center) := by
  have hcne := properCircle_center_ne_of_mem o c ho
  constructor
  · exact fun hx => inversion_mem_perpBisector_of_mem_circle_through_center
      o x c hxo ho hx
  · intro hx
    have hd := (EuclideanGeometry.inversion_mem_perpBisector_inversion_iff
      one_ne_zero hxo hcne).mp hx
    have hdo := EuclideanGeometry.mem_sphere'.mp ho
    change dist c.1.center o = c.1.radius at hdo
    apply EuclideanGeometry.mem_sphere'.mpr
    change dist c.1.center x = c.1.radius
    calc
      dist c.1.center x = dist x c.1.center := dist_comm _ _
      _ = dist c.1.center o := hd
      _ = c.1.radius := hdo

theorem exists_affineParamPoint_after_inversion_of_circle
    {o a b x : Point2} (c : ProperCircle)
    (hoa : a ≠ o) (hob : b ≠ o) (hox : x ≠ o) (hab : a ≠ b)
    (ho : o ∈ (c.1 : Set Point2))
    (ha : a ∈ (c.1 : Set Point2)) (hb : b ∈ (c.1 : Set Point2))
    (hx : x ∈ (c.1 : Set Point2)) :
    ∃ t : ℝ,
      affineParamPoint (EuclideanGeometry.inversion o 1 a)
          (EuclideanGeometry.inversion o 1 b -
            EuclideanGeometry.inversion o 1 a) t =
        EuclideanGeometry.inversion o 1 x := by
  let q := EuclideanGeometry.inversion o 1 c.1.center
  have hoq : o ≠ q := by
    intro h
    have hc : c.1.center = o :=
      (EuclideanGeometry.center_eq_inversion one_ne_zero).mp h
    exact properCircle_center_ne_of_mem o c ho hc
  have hiab : EuclideanGeometry.inversion o 1 a ≠
      EuclideanGeometry.inversion o 1 b :=
    (EuclideanGeometry.inversion_injective o one_ne_zero).ne hab
  exact exists_affineParamPoint_of_mem_perpBisector hoq hiab
    (inversion_mem_perpBisector_of_mem_circle_through_center o a c hoa ho ha)
    (inversion_mem_perpBisector_of_mem_circle_through_center o b c hob ho hb)
    (inversion_mem_perpBisector_of_mem_circle_through_center o x c hox ho hx)

theorem distinctSideParameters_of_distinct_points
    {A B X Y : Point2} {x y : ℝ}
    (hAX : A ≠ X) (hBX : B ≠ X) (hAY : A ≠ Y) (hBY : B ≠ Y)
    (hXY : X ≠ Y)
    (hx : affineParamPoint A (B - A) x = X)
    (hy : affineParamPoint A (B - A) y = Y) :
    DistinctSideParameters x y := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro h
    subst x
    simp at hx
    exact hAX hx
  · intro h
    subst x
    simp at hx
    exact hBX hx
  · intro h
    subst y
    simp at hy
    exact hAY hy
  · intro h
    subst y
    simp at hy
    exact hBY hy
  · intro h
    apply hXY
    rw [← hx, ← hy, h]

theorem sideParameter_ne_endpoints_of_distinct_point
    {A B X : Point2} {x : ℝ}
    (hAX : A ≠ X) (hBX : B ≠ X)
    (hx : affineParamPoint A (B - A) x = X) :
    x ≠ 0 ∧ x ≠ 1 := by
  constructor
  · intro h
    subst x
    simp at hx
    exact hAX hx
  · intro h
    subst x
    simp at hx
    exact hBX hx

end Erdos506.V3
