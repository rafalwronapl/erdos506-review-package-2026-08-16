import Erdos506.Incidence.FiveConicOneSingleTraceRigidity
import Erdos506.Incidence.FiveConicMixedPageBridge

/-!
# One-host directions on both kinds of five-conic page

The one-single/two-double separator has one genuinely new local input: the
unique host of the single outsider pair.  When that host is a proper circle,
its selected chord gives the same projective direction on a circle page and
on a line page.  This module records both literal statements.

For a line host the selected chord and the outsider secant are the same
projective line.  We record that equality explicitly rather than pretending
that its self-intersection is an ordinary projective point.  This is the
exact degenerate branch that the later trace argument must treat separately.
-/

namespace Erdos506.Incidence

open Erdos506.V4
open scoped LinearAlgebra.Projectivization

/-! ## A proper-circle single host on a line page -/

/-- A single proper-circle host has its selected-chord/outside-secant
intersection on a determined line page.  This is the line-page counterpart
of `properCircle_singleCircleHost_direction_on_page_axis`. -/
theorem properCircle_singleCircleHost_direction_on_line_axis
    (Gamma C : ProperCircle) (hGammaC : Gamma ≠ C)
    {a b x y : Point2} (ell : RealProjectiveLine)
    (haGamma : a ∈ (Gamma.1 : Set Point2))
    (hbGamma : b ∈ (Gamma.1 : Set Point2))
    (haC : a ∈ (C.1 : Set Point2))
    (hbC : b ∈ (C.1 : Set Point2))
    (haNotEll : ¬ Projectivization.orthogonal (projectivePoint a) ell)
    (hab : a ≠ b) (hxy : x ≠ y)
    (hxyEll : projectiveLine x y hxy = ell) :
    Projectivization.orthogonal
      (Projectivization.cross (projectiveLine a b hab)
        (projectiveLine x y hxy)) ell := by
  exact properCircle_circleLineHost_direction_on_line_axis
    Gamma C hGammaC (a := a) (b := b) (c := x) (d := y) ell
    haGamma hbGamma haC hbC haNotEll hab hxy hxyEll

/-! ## The honest line-host branch -/

/-- Four labelled points on one determined line make the selected chord and
the outsider secant literally equal.  In particular this branch cannot be
silently fed to a construction that requires two distinct projective lines. -/
theorem determinedLine_singleHost_selectedChord_eq_outsiderSecant
    {α : Type*} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (L : DeterminedLine cfg)
    {a b x y : α}
    (ha : a ∈ lineSupport cfg L) (hb : b ∈ lineSupport cfg L)
    (hx : x ∈ lineSupport cfg L) (hy : y ∈ lineSupport cfg L)
    (hab : a ≠ b) (hxy : x ≠ y) :
    projectiveLine (cfg a) (cfg b) (cfg.injective.ne hab) =
      projectiveLine (cfg x) (cfg y) (cfg.injective.ne hxy) := by
  exact projectiveLine_eq_projectiveLine_of_four_mem_determinedLine
    cfg L ha hb hx hy hab hxy

end Erdos506.Incidence
