import Erdos506.Incidence.FiveConicCirclePageBridge
import Erdos506.Incidence.DeterminedLineProjectiveRealization

/-!
# Mixed line--circle page directions for the five-conic trace law

The circle-page endpoint has a deliberately circle-only interface: it is
ideal when both hosts of an outsider pair are proper circles.  A saturated
actual host fibre can also have one line and one circle.  This file records
the exact projective replacement for that one mixed case.

There is no new incidence assumption here.  A line host through an outsider
pair supplies the same projective chord direction as the radical axis of the
page circle and the other circle host.  Consequently its chord centre lies
on the same selected/page trace as in the circle--circle case.  The exposed
lemmas are kept at the projective-line level so the C39 finite fibre adapter
can use actual determined lines without choosing a normal form.
-/

namespace Erdos506.Incidence

open Erdos506.Finite
open Erdos506.V4
open Matrix
open scoped LinearAlgebra.Projectivization

universe u

variable {alpha : Type u} [Fintype alpha] [DecidableEq alpha]

/-! ## Concrete determined-line realization -/

/-- Two distinct labelled points on a determined affine line determine its
projective covector.  This is the lossless conversion needed for a line host
in a C39 pair fibre. -/
theorem projectiveLine_eq_determinedProjectiveLine_of_mem
    (cfg : Configuration alpha) (L : DeterminedLine cfg) {a b : alpha}
    (ha : a ∈ lineSupport cfg L) (hb : b ∈ lineSupport cfg L)
    (hab : a ≠ b) :
    projectiveLine (cfg a) (cfg b) (cfg.injective.ne hab) =
      determinedProjectiveLine cfg L := by
  let P := affinePointToProjective (cfg a)
  let Q := affinePointToProjective (cfg b)
  have hPQ : P ≠ Q := by
    dsimp [P, Q]
    exact affinePointToProjective_ne (cfg.injective.ne hab)
  have hPline : Projectivization.orthogonal P
      (determinedProjectiveLine cfg L) := by
    change affinePointToProjective (cfg a) ∈ determinedProjectiveLine cfg L
    exact (affinePoint_mem_determinedProjectiveLine_iff cfg a L).2
      (mem_lineSupport.mp ha)
  have hQline : Projectivization.orthogonal Q
      (determinedProjectiveLine cfg L) := by
    change affinePointToProjective (cfg b) ∈ determinedProjectiveLine cfg L
    exact (affinePoint_mem_determinedProjectiveLine_iff cfg b L).2
      (mem_lineSupport.mp hb)
  calc
    projectiveLine (cfg a) (cfg b) (cfg.injective.ne hab) =
        Projectivization.cross P Q := by
          symm
          simpa [P, Q, affinePointToProjective_eq_projectivePoint] using
            (projectivePoint_cross_eq_projectiveLine (cfg.injective.ne hab))
    _ = determinedProjectiveLine cfg L :=
      (projectiveCovector_eq_cross_of_orthogonal hPQ hPline hQline).symm

/-- Four labelled points on one determined line give the same projective
line from either displayed pair.  In particular, a line host converts its
selected chord into the outsider-edge direction without a coordinate choice.
-/
theorem projectiveLine_eq_projectiveLine_of_four_mem_determinedLine
    (cfg : Configuration alpha) (L : DeterminedLine cfg) {a b x y : alpha}
    (ha : a ∈ lineSupport cfg L) (hb : b ∈ lineSupport cfg L)
    (hx : x ∈ lineSupport cfg L) (hy : y ∈ lineSupport cfg L)
    (hab : a ≠ b) (hxy : x ≠ y) :
    projectiveLine (cfg a) (cfg b) (cfg.injective.ne hab) =
      projectiveLine (cfg x) (cfg y) (cfg.injective.ne hxy) := by
  calc
    projectiveLine (cfg a) (cfg b) (cfg.injective.ne hab) =
        determinedProjectiveLine cfg L :=
      projectiveLine_eq_determinedProjectiveLine_of_mem cfg L ha hb hab
    _ = projectiveLine (cfg x) (cfg y) (cfg.injective.ne hxy) :=
      (projectiveLine_eq_determinedProjectiveLine_of_mem cfg L hx hy hxy).symm

/-! ## A public diagonal endpoint -/

private theorem mixed_cross_projectiveLine_eq_projectiveDiagonalAB_CD
    {a b c d : Point2}
    (hgeneral : CompleteQuadrangleGeneralPosition
      (homogeneousLift a) (homogeneousLift b)
      (homogeneousLift c) (homogeneousLift d))
    (hab : a ≠ b) (hcd : c ≠ d) :
    Projectivization.cross (projectiveLine a b hab) (projectiveLine c d hcd) =
      projectiveDiagonalAB_CD
        (homogeneousLift a) (homogeneousLift b)
        (homogeneousLift c) (homogeneousLift d) hgeneral := by
  simpa [projectiveDiagonalAB_CD, diagonalAB_CD, lineCovector] using
    (cross_projectiveLine_eq_mk_cross_lineCovectors
      hab hcd (diagonalAB_CD_ne_zero hgeneral))

private theorem mixed_cross_projectiveLine_eq_projectiveDiagonalAC_BD
    {a b c d : Point2}
    (hgeneral : CompleteQuadrangleGeneralPosition
      (homogeneousLift a) (homogeneousLift b)
      (homogeneousLift c) (homogeneousLift d))
    (hac : a ≠ c) (hbd : b ≠ d) :
    Projectivization.cross (projectiveLine a c hac) (projectiveLine b d hbd) =
      projectiveDiagonalAC_BD
        (homogeneousLift a) (homogeneousLift b)
        (homogeneousLift c) (homogeneousLift d) hgeneral := by
  simpa [projectiveDiagonalAC_BD, diagonalAC_BD, lineCovector] using
    (cross_projectiveLine_eq_mk_cross_lineCovectors
      hac hbd (diagonalAC_BD_ne_zero hgeneral))

private theorem mixed_cross_projectiveLine_eq_projectiveDiagonalAD_BC
    {a b c d : Point2}
    (hgeneral : CompleteQuadrangleGeneralPosition
      (homogeneousLift a) (homogeneousLift b)
      (homogeneousLift c) (homogeneousLift d))
    (had : a ≠ d) (hbc : b ≠ c) :
    Projectivization.cross (projectiveLine a d had) (projectiveLine b c hbc) =
      projectiveDiagonalAD_BC
        (homogeneousLift a) (homogeneousLift b)
        (homogeneousLift c) (homogeneousLift d) hgeneral := by
  simpa [projectiveDiagonalAD_BC, diagonalAD_BC, lineCovector] using
    (cross_projectiveLine_eq_mk_cross_lineCovectors
      had hbc (diagonalAD_BC_ne_zero hgeneral))

/-- The all-double diagonal obstruction in a form accepting any actual
projective trace.  This exposes the final step shared by circle pages and
line pages, including mixed line--circle host fibres. -/
theorem properCircle_allDoubleTriangle_projectiveLineTrace_absurd
    (Gamma : ProperCircle) {a b c d : Point2}
    (ha : a ∈ (Gamma.1 : Set Point2))
    (hb : b ∈ (Gamma.1 : Set Point2))
    (hc : c ∈ (Gamma.1 : Set Point2))
    (hd : d ∈ (Gamma.1 : Set Point2))
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    (ell : RealProjectivePlane)
    (hAB : Projectivization.orthogonal
      (Projectivization.cross (projectiveLine a b hab)
        (projectiveLine c d hcd)) ell)
    (hAC : Projectivization.orthogonal
      (Projectivization.cross (projectiveLine a c hac)
        (projectiveLine b d hbd)) ell)
    (hAD : Projectivization.orthogonal
      (Projectivization.cross (projectiveLine a d had)
        (projectiveLine b c hbc)) ell) : False := by
  have hgeneral : CompleteQuadrangleGeneralPosition
      (homogeneousLift a) (homogeneousLift b)
      (homogeneousLift c) (homogeneousLift d) :=
    properCircle_four_points_completeQuadrangleGeneralPosition Gamma
      ha hb hc hd hab hac had hbc hbd hcd
  rw [mixed_cross_projectiveLine_eq_projectiveDiagonalAB_CD hgeneral hab hcd] at hAB
  rw [mixed_cross_projectiveLine_eq_projectiveDiagonalAC_BD hgeneral hac hbd] at hAC
  rw [mixed_cross_projectiveLine_eq_projectiveDiagonalAD_BC hgeneral had hbc] at hAD
  exact (completeQuadrangle_projectiveDiagonals_noncollinear hgeneral)
    ⟨ell, hAB, hAC, hAD⟩

/-! ## Circle--circle and circle--line pair directions -/

private theorem mixed_projectiveLine_eq_projectiveRadicalAxis_of_common_points
    (C D : ProperCircle) (hCD : C ≠ D) {p q : Point2}
    (hpC : p ∈ (C.1 : Set Point2))
    (hqC : q ∈ (C.1 : Set Point2))
    (hpD : p ∈ (D.1 : Set Point2))
    (hqD : q ∈ (D.1 : Set Point2))
    (hpq : p ≠ q) :
    projectiveLine p q hpq = projectiveRadicalAxis C D hCD := by
  let P := projectivePoint p
  let Q := projectivePoint q
  have hPQ : P ≠ Q := projectivePoint_injective.ne hpq
  have hPaxis : Projectivization.orthogonal P
      (projectiveRadicalAxis C D hCD) :=
    projectivePoint_orthogonal_projectiveRadicalAxis_of_mem hCD hpC hpD
  have hQaxis : Projectivization.orthogonal Q
      (projectiveRadicalAxis C D hCD) :=
    projectivePoint_orthogonal_projectiveRadicalAxis_of_mem hCD hqC hqD
  calc
    projectiveLine p q hpq = Projectivization.cross P Q := by
      symm
      simpa [P, Q] using (projectivePoint_cross_eq_projectiveLine hpq)
    _ = projectiveRadicalAxis C D hCD :=
      (projectiveCovector_eq_cross_of_orthogonal hPQ hPaxis hQaxis).symm

/-- Two proper-circle hosts of one outsider edge force the intersection of
their selected chords onto the radical axis of the selected and page
circles.  This is the public direction factor behind the circle-page
adapter. -/
theorem properCircle_circleCircleHost_direction_on_page_axis
    (Gamma K C D : ProperCircle)
    (hGammaK : Gamma ≠ K) (hGammaC : Gamma ≠ C)
    (hGammaD : Gamma ≠ D) (hCD : C ≠ D) (hCK : C ≠ K)
    {a b c d x y : Point2}
    (haGamma : a ∈ (Gamma.1 : Set Point2))
    (hbGamma : b ∈ (Gamma.1 : Set Point2))
    (hcGamma : c ∈ (Gamma.1 : Set Point2))
    (hdGamma : d ∈ (Gamma.1 : Set Point2))
    (haC : a ∈ (C.1 : Set Point2))
    (hbC : b ∈ (C.1 : Set Point2))
    (hxC : x ∈ (C.1 : Set Point2))
    (hyC : y ∈ (C.1 : Set Point2))
    (hcD : c ∈ (D.1 : Set Point2))
    (hdD : d ∈ (D.1 : Set Point2))
    (hxD : x ∈ (D.1 : Set Point2))
    (hyD : y ∈ (D.1 : Set Point2))
    (hxK : x ∈ (K.1 : Set Point2))
    (hyK : y ∈ (K.1 : Set Point2))
    (haNotK : a ∉ (K.1 : Set Point2))
    (hab : a ≠ b) (hcd' : c ≠ d) (hxy : x ≠ y) :
    Projectivization.orthogonal
      (Projectivization.cross (projectiveLine a b hab)
        (projectiveLine c d hcd'))
      (projectiveRadicalAxis Gamma K hGammaK) := by
  have hAB : projectiveLine a b hab =
      projectiveRadicalAxis Gamma C hGammaC :=
    mixed_projectiveLine_eq_projectiveRadicalAxis_of_common_points
      Gamma C hGammaC haGamma hbGamma haC hbC hab
  have hCDline : projectiveLine c d hcd' =
      projectiveRadicalAxis Gamma D hGammaD :=
    mixed_projectiveLine_eq_projectiveRadicalAxis_of_common_points
      Gamma D hGammaD hcGamma hdGamma hcD hdD hcd'
  have hXYCD : projectiveLine x y hxy =
      projectiveRadicalAxis C D hCD :=
    mixed_projectiveLine_eq_projectiveRadicalAxis_of_common_points
      C D hCD hxC hyC hxD hyD hxy
  have hXYCK : projectiveLine x y hxy =
      projectiveRadicalAxis C K hCK :=
    mixed_projectiveLine_eq_projectiveRadicalAxis_of_common_points
      C K hCK hxC hyC hxK hyK hxy
  have hCDCK : projectiveRadicalAxis C D hCD =
      projectiveRadicalAxis C K hCK := hXYCD.symm.trans hXYCK
  have haxisNe : projectiveRadicalAxis Gamma K hGammaK ≠
      projectiveRadicalAxis Gamma C hGammaC := by
    intro hEq
    apply (not_projectivePoint_orthogonal_projectiveRadicalAxis_of_mem_not_mem
      hGammaK haGamma haNotK)
    rw [hEq]
    exact projectivePoint_orthogonal_projectiveRadicalAxis_of_mem
      hGammaC haGamma haC
  have hGammaCD := projectiveRadicalAxis_pencil_cross
    Gamma C D hGammaC hGammaD hCD
  have hGammaCK := projectiveRadicalAxis_pencil_cross
    Gamma C K hGammaC hGammaK hCK
  have hcenter :
      Projectivization.cross (projectiveRadicalAxis Gamma C hGammaC)
        (projectiveRadicalAxis Gamma D hGammaD) =
      Projectivization.cross (projectiveRadicalAxis Gamma K hGammaK)
        (projectiveRadicalAxis Gamma C hGammaC) := by
    calc
      Projectivization.cross (projectiveRadicalAxis Gamma C hGammaC)
          (projectiveRadicalAxis Gamma D hGammaD) =
          Projectivization.cross (projectiveRadicalAxis Gamma D hGammaD)
            (projectiveRadicalAxis Gamma C hGammaC) :=
        Projectivization.cross_comm _ _
      _ = Projectivization.cross (projectiveRadicalAxis C D hCD)
            (projectiveRadicalAxis Gamma C hGammaC) := hGammaCD
      _ = Projectivization.cross (projectiveRadicalAxis C K hCK)
            (projectiveRadicalAxis Gamma C hGammaC) := by rw [hCDCK]
      _ = Projectivization.cross (projectiveRadicalAxis Gamma K hGammaK)
            (projectiveRadicalAxis Gamma C hGammaC) := hGammaCK.symm
  rw [hAB, hCDline, hcenter]
  exact Projectivization.cross_orthogonal_left haxisNe

/-- A mixed line--circle pair fibre has the same direction conclusion on a
proper-circle page.  `hcdxy` is the literal fact supplied by the line host:
its two selected trace labels and the outsider edge lie on one line. -/
theorem properCircle_circleLineHost_direction_on_page_axis
    (Gamma K C : ProperCircle)
    (hGammaK : Gamma ≠ K) (hGammaC : Gamma ≠ C) (hCK : C ≠ K)
    {a b c d x y : Point2}
    (haGamma : a ∈ (Gamma.1 : Set Point2))
    (hbGamma : b ∈ (Gamma.1 : Set Point2))
    (haC : a ∈ (C.1 : Set Point2))
    (hbC : b ∈ (C.1 : Set Point2))
    (hxC : x ∈ (C.1 : Set Point2))
    (hyC : y ∈ (C.1 : Set Point2))
    (hxK : x ∈ (K.1 : Set Point2))
    (hyK : y ∈ (K.1 : Set Point2))
    (haNotK : a ∉ (K.1 : Set Point2))
    (hab : a ≠ b) (hcd' : c ≠ d) (hxy : x ≠ y)
    (hcdxy : projectiveLine c d hcd' = projectiveLine x y hxy) :
    Projectivization.orthogonal
      (Projectivization.cross (projectiveLine a b hab)
        (projectiveLine c d hcd'))
      (projectiveRadicalAxis Gamma K hGammaK) := by
  have hAB : projectiveLine a b hab =
      projectiveRadicalAxis Gamma C hGammaC :=
    mixed_projectiveLine_eq_projectiveRadicalAxis_of_common_points
      Gamma C hGammaC haGamma hbGamma haC hbC hab
  have hXYCK : projectiveLine x y hxy =
      projectiveRadicalAxis C K hCK :=
    mixed_projectiveLine_eq_projectiveRadicalAxis_of_common_points
      C K hCK hxC hyC hxK hyK hxy
  have hCDline : projectiveLine c d hcd' =
      projectiveRadicalAxis C K hCK := hcdxy.trans hXYCK
  have haxisNe : projectiveRadicalAxis Gamma K hGammaK ≠
      projectiveRadicalAxis Gamma C hGammaC := by
    intro hEq
    apply (not_projectivePoint_orthogonal_projectiveRadicalAxis_of_mem_not_mem
      hGammaK haGamma haNotK)
    rw [hEq]
    exact projectivePoint_orthogonal_projectiveRadicalAxis_of_mem
      hGammaC haGamma haC
  have hGammaCK := projectiveRadicalAxis_pencil_cross
    Gamma C K hGammaC hGammaK hCK
  have hcenter :
      Projectivization.cross (projectiveRadicalAxis Gamma C hGammaC)
        (projectiveRadicalAxis C K hCK) =
      Projectivization.cross (projectiveRadicalAxis Gamma K hGammaK)
        (projectiveRadicalAxis Gamma C hGammaC) := by
    calc
      Projectivization.cross (projectiveRadicalAxis Gamma C hGammaC)
          (projectiveRadicalAxis C K hCK) =
          Projectivization.cross (projectiveRadicalAxis C K hCK)
            (projectiveRadicalAxis Gamma C hGammaC) :=
        Projectivization.cross_comm _ _
      _ = Projectivization.cross (projectiveRadicalAxis Gamma K hGammaK)
            (projectiveRadicalAxis Gamma C hGammaC) := hGammaCK.symm
  rw [hAB, hCDline, hcenter]
  exact Projectivization.cross_orthogonal_left haxisNe

/-- On a line page, a circle--circle host pair has its chord intersection on
the page line.  This is the line-page analogue of the radical-axis direction
lemma. -/
theorem properCircle_circleCircleHost_direction_on_line_axis
    (Gamma C D : ProperCircle)
    (hGammaC : Gamma ≠ C) (hGammaD : Gamma ≠ D) (hCD : C ≠ D)
    {a b c d x y : Point2} (ell : RealProjectiveLine)
    (haGamma : a ∈ (Gamma.1 : Set Point2))
    (hbGamma : b ∈ (Gamma.1 : Set Point2))
    (hcGamma : c ∈ (Gamma.1 : Set Point2))
    (hdGamma : d ∈ (Gamma.1 : Set Point2))
    (haC : a ∈ (C.1 : Set Point2))
    (hbC : b ∈ (C.1 : Set Point2))
    (hxC : x ∈ (C.1 : Set Point2))
    (hyC : y ∈ (C.1 : Set Point2))
    (hcD : c ∈ (D.1 : Set Point2))
    (hdD : d ∈ (D.1 : Set Point2))
    (hxD : x ∈ (D.1 : Set Point2))
    (hyD : y ∈ (D.1 : Set Point2))
    (haNotEll : ¬ Projectivization.orthogonal (projectivePoint a) ell)
    (hab : a ≠ b) (hcd' : c ≠ d) (hxy : x ≠ y)
    (hxyEll : projectiveLine x y hxy = ell) :
    Projectivization.orthogonal
      (Projectivization.cross (projectiveLine a b hab)
        (projectiveLine c d hcd')) ell := by
  have hAB : projectiveLine a b hab =
      projectiveRadicalAxis Gamma C hGammaC :=
    mixed_projectiveLine_eq_projectiveRadicalAxis_of_common_points
      Gamma C hGammaC haGamma hbGamma haC hbC hab
  have hCDline : projectiveLine c d hcd' =
      projectiveRadicalAxis Gamma D hGammaD :=
    mixed_projectiveLine_eq_projectiveRadicalAxis_of_common_points
      Gamma D hGammaD hcGamma hdGamma hcD hdD hcd'
  have hXYCD : projectiveLine x y hxy =
      projectiveRadicalAxis C D hCD :=
    mixed_projectiveLine_eq_projectiveRadicalAxis_of_common_points
      C D hCD hxC hyC hxD hyD hxy
  have haxisNe : ell ≠ projectiveRadicalAxis Gamma C hGammaC := by
    intro hEq
    apply haNotEll
    rw [hEq]
    exact projectivePoint_orthogonal_projectiveRadicalAxis_of_mem
      hGammaC haGamma haC
  have hGammaCD := projectiveRadicalAxis_pencil_cross
    Gamma C D hGammaC hGammaD hCD
  have hcenter :
      Projectivization.cross (projectiveRadicalAxis Gamma C hGammaC)
        (projectiveRadicalAxis Gamma D hGammaD) =
      Projectivization.cross ell
        (projectiveRadicalAxis Gamma C hGammaC) := by
    calc
      Projectivization.cross (projectiveRadicalAxis Gamma C hGammaC)
          (projectiveRadicalAxis Gamma D hGammaD) =
          Projectivization.cross (projectiveRadicalAxis Gamma D hGammaD)
            (projectiveRadicalAxis Gamma C hGammaC) :=
        Projectivization.cross_comm _ _
      _ = Projectivization.cross (projectiveRadicalAxis C D hCD)
            (projectiveRadicalAxis Gamma C hGammaC) := hGammaCD
      _ = Projectivization.cross ell
            (projectiveRadicalAxis Gamma C hGammaC) := by
        rw [← hxyEll, hXYCD]
  rw [hAB, hCDline, hcenter]
  exact Projectivization.cross_orthogonal_left haxisNe

/-- On a line page, a line--circle host pair is even more direct: the line
host already is the page axis, so its selected chord meets the circle-host
chord on that axis. -/
theorem properCircle_circleLineHost_direction_on_line_axis
    (Gamma C : ProperCircle) (hGammaC : Gamma ≠ C)
    {a b c d : Point2} (ell : RealProjectiveLine)
    (haGamma : a ∈ (Gamma.1 : Set Point2))
    (hbGamma : b ∈ (Gamma.1 : Set Point2))
    (haC : a ∈ (C.1 : Set Point2))
    (hbC : b ∈ (C.1 : Set Point2))
    (haNotEll : ¬ Projectivization.orthogonal (projectivePoint a) ell)
    (hab : a ≠ b) (hcd' : c ≠ d)
    (hcdEll : projectiveLine c d hcd' = ell) :
    Projectivization.orthogonal
      (Projectivization.cross (projectiveLine a b hab)
        (projectiveLine c d hcd')) ell := by
  have hAB : projectiveLine a b hab =
      projectiveRadicalAxis Gamma C hGammaC :=
    mixed_projectiveLine_eq_projectiveRadicalAxis_of_common_points
      Gamma C hGammaC haGamma hbGamma haC hbC hab
  have haxisNe : ell ≠ projectiveRadicalAxis Gamma C hGammaC := by
    intro hEq
    apply haNotEll
    rw [hEq]
    exact projectivePoint_orthogonal_projectiveRadicalAxis_of_mem
      hGammaC haGamma haC
  have hcenter :
      Projectivization.cross (projectiveRadicalAxis Gamma C hGammaC) ell =
      Projectivization.cross ell (projectiveRadicalAxis Gamma C hGammaC) :=
    Projectivization.cross_comm _ _
  rw [hAB, hcdEll, hcenter]
  exact Projectivization.cross_orthogonal_left haxisNe

end Erdos506.Incidence
