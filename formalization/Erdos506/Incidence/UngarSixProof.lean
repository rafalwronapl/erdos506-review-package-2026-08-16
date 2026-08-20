import Erdos506.Incidence.UngarSix

/-!
# The anchored direction kernel for Ungar's six-point theorem

This module contains the first geometric implication needed by a rotating-line
proof of the six-point case of Ungar's theorem.  It is deliberately free of
any order, convexity, or general-position assumption.

If two joins from a common point have the same projective direction, their
third endpoints lie on one affine line.  Thus every noncollinear triangle
already contributes two distinct directions.  The remaining part of Ungar is
the global rotating-line construction of six such distinct joins; it cannot
be replaced by a local triangle argument.
-/

namespace Erdos506.Incidence

open Erdos506.Finite
open Erdos506.V1
open Erdos506.V4

/-! ## Equal anchored directions are collinear -/

/-- Equal projective directions of the joins `a b` and `a c` force the three
points to be collinear.  Over `ℝ`, equality of the two singleton spans gives
a nonzero scalar taking `b - a` to `c - a`; this is precisely an affine-line
parameter for `c` on the line through `a` and `b`. -/
theorem collinear_of_directionOfPoints_eq
    {a b c : Point2}
    (hdir : directionOfPoints a b = directionOfPoints a c) :
    Collinear ℝ ({a, b, c} : Set Point2) := by
  unfold directionOfPoints at hdir
  rw [Submodule.span_singleton_eq_span_singleton] at hdir
  obtain ⟨u, hu⟩ := hdir
  have hc : c ∈ affineSpan ℝ ({a, b} : Set Point2) := by
    rw [mem_affineSpan_pair_iff_exists_lineMap_eq]
    refine ⟨(u : ℝ), ?_⟩
    rw [AffineMap.lineMap_apply]
    change (u : ℝ) • (b - a) + a = c
    have hu' : (u : ℝ) • (b - a) = c - a := by
      simpa only [Units.smul_def] using hu
    rw [hu']
    abel
  have hset : ({c, a, b} : Set Point2) = {a, b, c} := by
    ext x
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    tauto
  have hcol : Collinear ℝ ({c, a, b} : Set Point2) :=
    collinear_insert_of_mem_affineSpan_pair hc
  rwa [hset] at hcol

/-- A noncollinear triangle has different directions on the two sides
emanating from each chosen vertex. -/
theorem directionOfPoints_ne_of_not_collinear
    {a b c : Point2}
    (hnon : ¬ Collinear ℝ ({a, b, c} : Set Point2)) :
    directionOfPoints a b ≠ directionOfPoints a c := by
  intro hdir
  exact hnon (collinear_of_directionOfPoints_eq hdir)

/-- Reversing an oriented presentation of a pair does not change its
projective direction. -/
theorem directionOfPoints_comm (a b : Point2) :
    directionOfPoints a b = directionOfPoints b a := by
  unfold directionOfPoints
  rw [show a - b = -(b - a) by abel]
  simpa using (Submodule.span_neg ({b - a} : Set Point2)).symm

/-- The three sides of a noncollinear triangle have pairwise different
projective directions.  This is the complete local direction contribution
available before the global allowable-sequence argument of Ungar. -/
theorem triangle_directions_pairwise_of_not_collinear
    {a b c : Point2}
    (hnon : ¬ Collinear ℝ ({a, b, c} : Set Point2)) :
    directionOfPoints a b ≠ directionOfPoints a c ∧
      directionOfPoints a b ≠ directionOfPoints b c ∧
      directionOfPoints a c ≠ directionOfPoints b c := by
  constructor
  · exact directionOfPoints_ne_of_not_collinear hnon
  constructor
  · intro hdir
    apply hnon
    have hcol := collinear_of_directionOfPoints_eq
      ((directionOfPoints_comm a b).symm.trans hdir)
    have hset : ({b, a, c} : Set Point2) = {a, b, c} := by
      ext x
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      tauto
    rwa [hset] at hcol
  · intro hdir
    apply hnon
    have hcol := collinear_of_directionOfPoints_eq
      ((directionOfPoints_comm a c).symm.trans
        (hdir.trans (directionOfPoints_comm b c)))
    have hset : ({c, a, b} : Set Point2) = {a, b, c} := by
      ext x
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      tauto
    rwa [hset] at hcol

/-- Labelled form of the anchored-direction kernel.  It is the directly
usable local certificate for a rotating-line witness: once two pair indices
share `a`, their equal direction contradicts noncollinearity of `a,b,c`. -/
theorem directionOfPair_ne_of_not_collinear_of_shared_first
    {α : Type*} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) {a b c : α}
    (hab : a ≠ b) (hac : a ≠ c)
    (hnon : ¬ Collinear ℝ ({cfg a, cfg b, cfg c} : Set Point2)) :
    directionOfPair cfg ⟨{a, b}, by simp [hab]⟩ ≠
      directionOfPair cfg ⟨{a, c}, by simp [hac]⟩ := by
  rw [directionOfPair_eq_directionOfPoints cfg hab,
    directionOfPair_eq_directionOfPoints cfg hac]
  exact directionOfPoints_ne_of_not_collinear hnon

end Erdos506.Incidence
