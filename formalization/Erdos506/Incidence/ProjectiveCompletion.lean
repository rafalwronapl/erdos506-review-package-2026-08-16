import Erdos506.V4.Model
import Mathlib.Combinatorics.Configuration

/-!
# The real projective completion of the affine plane

This is the first geometric component needed by a projective-line-arrangement
adapter.  Mathlib represents the real projective plane as the
projectivization of homogeneous three-vectors and already proves its point /
line incidence axioms.  This module fixes the affine chart `z = 1`, supplies
the embedding of the project's `Point2`, and records the concrete cross
product constructions of a line through two affine points and of an
intersection of two projective lines.

It deliberately stops before the topological work of ordering vertices on a
projective line or forming faces.
-/

namespace Erdos506.Incidence

open Erdos506.V4
open scoped LinearAlgebra.Projectivization

/-- Points of the real projective completion of `Point2`, represented by
nonzero homogeneous three-vectors modulo rescaling. -/
abbrev RealProjectivePoint := ℙ ℝ (Fin 3 → ℝ)

/-- Projective lines are represented dually by homogeneous covectors.  The
ambient vector space is self-dual through the standard dot product. -/
abbrev RealProjectiveLine := RealProjectivePoint

/-- Embed the affine chart in the real projective plane by `x ↦ [x₀:x₁:1]`. -/
noncomputable def affinePointToProjective (x : Point2) : RealProjectivePoint :=
  Projectivization.mk ℝ ![x 0, x 1, 1] (by
    intro h
    have hlast : (1 : ℝ) = 0 := by
      simpa using congrFun h (2 : Fin 3)
    norm_num at hlast)

/-- The affine chart embedding is injective. -/
theorem affinePointToProjective_injective :
    Function.Injective affinePointToProjective := by
  intro x y hxy
  unfold affinePointToProjective at hxy
  obtain ⟨a, ha⟩ :=
    (Projectivization.mk_eq_mk_iff' ℝ _ _ _ _).mp hxy
  have haLast := congrFun ha (2 : Fin 3)
  have haOne : a = 1 := by
    simpa using haLast
  ext i
  fin_cases i
  · have haZero := congrFun ha (0 : Fin 3)
    simpa [haOne] using haZero.symm
  · have haOneCoord := congrFun ha (1 : Fin 3)
    simpa [haOne] using haOneCoord.symm

/-- Distinct affine points remain distinct after projective completion. -/
theorem affinePointToProjective_ne {x y : Point2} (hxy : x ≠ y) :
    affinePointToProjective x ≠ affinePointToProjective y :=
  fun h => hxy (affinePointToProjective_injective h)

/-- The homogeneous covector of the projective line through two distinct
affine points.  The inequality rules out the fallback branch in mathlib's
total projective cross-product operation. -/
noncomputable def projectiveLineThrough (x y : Point2) (_ : x ≠ y) :
    RealProjectiveLine :=
  by
    classical
    exact Projectivization.cross (affinePointToProjective x) (affinePointToProjective y)

/-- The first affine point lies on its homogeneous joining line. -/
theorem affinePoint_mem_projectiveLineThrough_left
  (x y : Point2) (hxy : x ≠ y) :
    affinePointToProjective x ∈ projectiveLineThrough x y hxy := by
  classical
  change (affinePointToProjective x).orthogonal
    (Projectivization.cross (affinePointToProjective x) (affinePointToProjective y))
  exact Projectivization.orthogonal_cross_left
    (affinePointToProjective_ne hxy)

/-- The second affine point lies on its homogeneous joining line. -/
theorem affinePoint_mem_projectiveLineThrough_right
  (x y : Point2) (hxy : x ≠ y) :
    affinePointToProjective y ∈ projectiveLineThrough x y hxy := by
  classical
  change (affinePointToProjective y).orthogonal
    (Projectivization.cross (affinePointToProjective x) (affinePointToProjective y))
  exact Projectivization.orthogonal_cross_right
    (affinePointToProjective_ne hxy)

/-- The projective intersection of two homogeneous line covectors.  For
distinct lines it is their unique common projective point, including the
points at infinity of parallel affine lines. -/
noncomputable def projectiveLineIntersection
    (l m : RealProjectiveLine) (_ : l ≠ m) : RealProjectivePoint :=
  by
    classical
    exact Projectivization.cross l m

/-- The cross-product intersection lies on the first of two distinct lines. -/
theorem projectiveLineIntersection_mem_left
    {l m : RealProjectiveLine} (hlm : l ≠ m) :
    projectiveLineIntersection l m hlm ∈ l := by
  classical
  change (Projectivization.cross l m).orthogonal l
  exact Projectivization.cross_orthogonal_left hlm

/-- The cross-product intersection lies on the second of two distinct lines. -/
theorem projectiveLineIntersection_mem_right
    {l m : RealProjectiveLine} (hlm : l ≠ m) :
    projectiveLineIntersection l m hlm ∈ m := by
  classical
  change (Projectivization.cross l m).orthogonal m
  exact Projectivization.cross_orthogonal_right hlm

/-- Two distinct real projective lines have exactly one common point.  This
is the usable uniqueness fact for the future finite arrangement vertex type. -/
theorem existsUnique_projectiveLineIntersection
    (l m : RealProjectiveLine) (hlm : l ≠ m) :
    ∃! p : RealProjectivePoint, p ∈ l ∧ p ∈ m := by
  classical
  exact Configuration.HasPoints.existsUnique_point
    RealProjectivePoint RealProjectiveLine l m hlm

end Erdos506.Incidence
