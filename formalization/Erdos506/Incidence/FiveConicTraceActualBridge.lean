import Erdos506.Incidence.DeterminedLineProjectiveRealization
import Erdos506.Incidence.FiveConicTraceRigidity

/-!
# Actual chord-trace bridge for five-conic rigidity

The projective K2 core is stated on homogeneous points and a trace covector.
This module is the lossless bridge from concrete labelled circle chords and a
concrete projective trace to that core.  In particular, it does not package a
"trace-rigidity certificate": its hypotheses are just six explicit chord
supports and three ordinary projective incidences.

The main theorem is the all-double-triangle clause of K2.1 in the form used
by a configuration-level router.  Four labelled points on an actual proper
circle determine the three opposite chord intersections.  No one projective
trace can contain all three.  A corollary specializes the trace to a genuine
`DeterminedLine` of a configuration.
-/

namespace Erdos506.Incidence

open Erdos506.Finite
open Erdos506.V4
open Matrix
open scoped LinearAlgebra.Projectivization

universe u

variable {alpha : Type u} [Fintype alpha] [DecidableEq alpha]

/-- A concrete two-label chord with the displayed support has the expected
projective chord covector. -/
private theorem projectiveChordLine_eq_projectiveLine_of_support_pair
    (cfg : Configuration alpha) (e : KSubset alpha 2) {x y : alpha}
    (he : e.1 = {x, y}) (hxy : x ≠ y) :
    projectiveChordLine cfg e =
      projectiveLine (cfg x) (cfg y) (cfg.injective.ne hxy) := by
  apply projectiveChordLine_eq_projectiveLine_of_mem cfg e
  · rw [he]
    simp
  · rw [he]
    simp
  · exact hxy

/-- The intersection of the two concrete opposite chords `ab` and `cd` is
the first diagonal point of the corresponding complete quadrangle. -/
private theorem projectiveChordIntersection_eq_projectiveDiagonalAB_CD
    (cfg : Configuration alpha) {a b c d : alpha}
    (hgeneral : CompleteQuadrangleGeneralPosition
      (homogeneousLift (cfg a)) (homogeneousLift (cfg b))
      (homogeneousLift (cfg c)) (homogeneousLift (cfg d)))
    (hab : a ≠ b) (hcd : c ≠ d)
    (eAB eCD : KSubset alpha 2)
    (heAB : eAB.1 = {a, b}) (heCD : eCD.1 = {c, d}) :
    Projectivization.cross (projectiveChordLine cfg eAB)
        (projectiveChordLine cfg eCD) =
      projectiveDiagonalAB_CD
        (homogeneousLift (cfg a)) (homogeneousLift (cfg b))
        (homogeneousLift (cfg c)) (homogeneousLift (cfg d)) hgeneral := by
  have hlineAB := projectiveChordLine_eq_projectiveLine_of_support_pair
    cfg eAB heAB hab
  have hlineCD := projectiveChordLine_eq_projectiveLine_of_support_pair
    cfg eCD heCD hcd
  calc
    Projectivization.cross (projectiveChordLine cfg eAB)
        (projectiveChordLine cfg eCD) =
        Projectivization.cross
          (projectiveLine (cfg a) (cfg b) (cfg.injective.ne hab))
          (projectiveLine (cfg c) (cfg d) (cfg.injective.ne hcd)) := by
          rw [hlineAB, hlineCD]
    _ = _ := by
      simpa [projectiveDiagonalAB_CD, diagonalAB_CD, lineCovector] using
        (cross_projectiveLine_eq_mk_cross_lineCovectors
          (cfg.injective.ne hab) (cfg.injective.ne hcd)
          (diagonalAB_CD_ne_zero hgeneral))

/-- The intersection of the two concrete opposite chords `ac` and `bd` is
the second diagonal point of the corresponding complete quadrangle. -/
private theorem projectiveChordIntersection_eq_projectiveDiagonalAC_BD
    (cfg : Configuration alpha) {a b c d : alpha}
    (hgeneral : CompleteQuadrangleGeneralPosition
      (homogeneousLift (cfg a)) (homogeneousLift (cfg b))
      (homogeneousLift (cfg c)) (homogeneousLift (cfg d)))
    (hac : a ≠ c) (hbd : b ≠ d)
    (eAC eBD : KSubset alpha 2)
    (heAC : eAC.1 = {a, c}) (heBD : eBD.1 = {b, d}) :
    Projectivization.cross (projectiveChordLine cfg eAC)
        (projectiveChordLine cfg eBD) =
      projectiveDiagonalAC_BD
        (homogeneousLift (cfg a)) (homogeneousLift (cfg b))
        (homogeneousLift (cfg c)) (homogeneousLift (cfg d)) hgeneral := by
  have hlineAC := projectiveChordLine_eq_projectiveLine_of_support_pair
    cfg eAC heAC hac
  have hlineBD := projectiveChordLine_eq_projectiveLine_of_support_pair
    cfg eBD heBD hbd
  calc
    Projectivization.cross (projectiveChordLine cfg eAC)
        (projectiveChordLine cfg eBD) =
        Projectivization.cross
          (projectiveLine (cfg a) (cfg c) (cfg.injective.ne hac))
          (projectiveLine (cfg b) (cfg d) (cfg.injective.ne hbd)) := by
          rw [hlineAC, hlineBD]
    _ = _ := by
      simpa [projectiveDiagonalAC_BD, diagonalAC_BD, lineCovector] using
        (cross_projectiveLine_eq_mk_cross_lineCovectors
          (cfg.injective.ne hac) (cfg.injective.ne hbd)
          (diagonalAC_BD_ne_zero hgeneral))

/-- The intersection of the two concrete opposite chords `ad` and `bc` is
the third diagonal point of the corresponding complete quadrangle. -/
private theorem projectiveChordIntersection_eq_projectiveDiagonalAD_BC
    (cfg : Configuration alpha) {a b c d : alpha}
    (hgeneral : CompleteQuadrangleGeneralPosition
      (homogeneousLift (cfg a)) (homogeneousLift (cfg b))
      (homogeneousLift (cfg c)) (homogeneousLift (cfg d)))
    (had : a ≠ d) (hbc : b ≠ c)
    (eAD eBC : KSubset alpha 2)
    (heAD : eAD.1 = {a, d}) (heBC : eBC.1 = {b, c}) :
    Projectivization.cross (projectiveChordLine cfg eAD)
        (projectiveChordLine cfg eBC) =
      projectiveDiagonalAD_BC
        (homogeneousLift (cfg a)) (homogeneousLift (cfg b))
        (homogeneousLift (cfg c)) (homogeneousLift (cfg d)) hgeneral := by
  have hlineAD := projectiveChordLine_eq_projectiveLine_of_support_pair
    cfg eAD heAD had
  have hlineBC := projectiveChordLine_eq_projectiveLine_of_support_pair
    cfg eBC heBC hbc
  calc
    Projectivization.cross (projectiveChordLine cfg eAD)
        (projectiveChordLine cfg eBC) =
        Projectivization.cross
          (projectiveLine (cfg a) (cfg d) (cfg.injective.ne had))
          (projectiveLine (cfg b) (cfg c) (cfg.injective.ne hbc)) := by
          rw [hlineAD, hlineBC]
    _ = _ := by
      simpa [projectiveDiagonalAD_BC, diagonalAD_BC, lineCovector] using
        (cross_projectiveLine_eq_mk_cross_lineCovectors
          (cfg.injective.ne had) (cfg.injective.ne hbc)
          (diagonalAD_BC_ne_zero hgeneral))

/-- K2.1 in actual labelled form.  Suppose `a,b,c,d` are four distinct
labels on one proper circle.  If the three displayed opposite chord pairs
have their projective intersections on a single actual trace `ell`, then the
incidences are inconsistent.

For a double-hosted outsider triangle, callers instantiate the six chords
with the two host chords of its three edges and take `ell` to be the block
trace.  Thus this theorem is a direct, lossless endpoint for the
all-double-triangle part of the one-colour trace law. -/
theorem properCircle_allDoubleTriangle_actualTrace_absurd
    (cfg : Configuration alpha) (Gamma : ProperCircle)
    {a b c d : alpha}
    (ha : a ∈ circleTrace cfg Gamma)
    (hb : b ∈ circleTrace cfg Gamma)
    (hc : c ∈ circleTrace cfg Gamma)
    (hd : d ∈ circleTrace cfg Gamma)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    (eAB eCD eAC eBD eAD eBC : KSubset alpha 2)
    (heAB : eAB.1 = {a, b}) (heCD : eCD.1 = {c, d})
    (heAC : eAC.1 = {a, c}) (heBD : eBD.1 = {b, d})
    (heAD : eAD.1 = {a, d}) (heBC : eBC.1 = {b, c})
    (ell : RealProjectivePlane)
    (hAB : Projectivization.orthogonal
      (Projectivization.cross (projectiveChordLine cfg eAB)
        (projectiveChordLine cfg eCD)) ell)
    (hAC : Projectivization.orthogonal
      (Projectivization.cross (projectiveChordLine cfg eAC)
        (projectiveChordLine cfg eBD)) ell)
    (hAD : Projectivization.orthogonal
      (Projectivization.cross (projectiveChordLine cfg eAD)
        (projectiveChordLine cfg eBC)) ell) : False := by
  have hgeneral : CompleteQuadrangleGeneralPosition
      (homogeneousLift (cfg a)) (homogeneousLift (cfg b))
      (homogeneousLift (cfg c)) (homogeneousLift (cfg d)) :=
    properCircle_four_points_completeQuadrangleGeneralPosition Gamma
      (mem_circleTrace.mp ha) (mem_circleTrace.mp hb)
      (mem_circleTrace.mp hc) (mem_circleTrace.mp hd)
      (cfg.injective.ne hab) (cfg.injective.ne hac) (cfg.injective.ne had)
      (cfg.injective.ne hbc) (cfg.injective.ne hbd) (cfg.injective.ne hcd)
  have hdiagAB := projectiveChordIntersection_eq_projectiveDiagonalAB_CD
    cfg hgeneral hab hcd eAB eCD heAB heCD
  have hdiagAC := projectiveChordIntersection_eq_projectiveDiagonalAC_BD
    cfg hgeneral hac hbd eAC eBD heAC heBD
  have hdiagAD := projectiveChordIntersection_eq_projectiveDiagonalAD_BC
    cfg hgeneral had hbc eAD eBC heAD heBC
  rw [hdiagAB] at hAB
  rw [hdiagAC] at hAC
  rw [hdiagAD] at hAD
  exact (completeQuadrangle_projectiveDiagonals_noncollinear hgeneral)
    ⟨ell, hAB, hAC, hAD⟩

/-- The same K2.1 endpoint when the trace is a concrete determined affine
line of the configuration. -/
theorem properCircle_allDoubleTriangle_determinedTrace_absurd
    (cfg : Configuration alpha) (Gamma : ProperCircle)
    {a b c d : alpha}
    (ha : a ∈ circleTrace cfg Gamma)
    (hb : b ∈ circleTrace cfg Gamma)
    (hc : c ∈ circleTrace cfg Gamma)
    (hd : d ∈ circleTrace cfg Gamma)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    (eAB eCD eAC eBD eAD eBC : KSubset alpha 2)
    (heAB : eAB.1 = {a, b}) (heCD : eCD.1 = {c, d})
    (heAC : eAC.1 = {a, c}) (heBD : eBD.1 = {b, d})
    (heAD : eAD.1 = {a, d}) (heBC : eBC.1 = {b, c})
    (L : DeterminedLine cfg)
    (hAB : Projectivization.orthogonal
      (Projectivization.cross (projectiveChordLine cfg eAB)
        (projectiveChordLine cfg eCD)) (determinedProjectiveLine cfg L))
    (hAC : Projectivization.orthogonal
      (Projectivization.cross (projectiveChordLine cfg eAC)
        (projectiveChordLine cfg eBD)) (determinedProjectiveLine cfg L))
    (hAD : Projectivization.orthogonal
      (Projectivization.cross (projectiveChordLine cfg eAD)
        (projectiveChordLine cfg eBC)) (determinedProjectiveLine cfg L)) :
    False := by
  exact properCircle_allDoubleTriangle_actualTrace_absurd
    cfg Gamma ha hb hc hd hab hac had hbc hbd hcd
    eAB eCD eAC eBD eAD eBC heAB heCD heAC heBD heAD heBC
    (determinedProjectiveLine cfg L) hAB hAC hAD

end Erdos506.Incidence
