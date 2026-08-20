import Erdos506.Incidence.FiveConicTraceActualBridge

/-!
# Circle-page realization of the five-conic all-double law

This is the direct circle-only realization of the first clause of K2.1.
The selected five-conic is `Γ`, a one-colour page is a second proper circle
`K`, and two proper-circle hosts of an outsider edge cut two chords on `Γ`.
Their chord intersection is on the radical axis of `Γ` and `K`.  Applying
this three times to an all-double outsider triangle contradicts the diagonal
triangle of four marked points of `Γ`.

The statement deliberately uses ordinary memberships and inequalities of
actual circles.  It adds no cyclic-order, normal-form, or trace-rigidity
certificate.  A separate adapter is needed only for generalized pages or
hosts which are affine lines.
-/

namespace Erdos506.Incidence

open Erdos506.V4
open Matrix
open scoped LinearAlgebra.Projectivization

/-! ## A projective diagonal formulation -/

private theorem cross_projectiveLine_eq_projectiveDiagonalAB_CD
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

private theorem cross_projectiveLine_eq_projectiveDiagonalAC_BD
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

private theorem cross_projectiveLine_eq_projectiveDiagonalAD_BC
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

private theorem properCircle_allDoubleTriangle_projectiveTrace_absurd
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
  rw [cross_projectiveLine_eq_projectiveDiagonalAB_CD hgeneral hab hcd] at hAB
  rw [cross_projectiveLine_eq_projectiveDiagonalAC_BD hgeneral hac hbd] at hAC
  rw [cross_projectiveLine_eq_projectiveDiagonalAD_BC hgeneral had hbc] at hAD
  exact (completeQuadrangle_projectiveDiagonals_noncollinear hgeneral)
    ⟨ell, hAB, hAC, hAD⟩

/-! ## One direction from two actual circle hosts -/

private theorem projectiveLine_eq_projectiveRadicalAxis_of_common_points
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

/-- Two circle hosts of the same outsider edge determine a point on the
trace axis of the selected circle and the page circle. -/
private theorem double_circle_host_direction_on_page_axis
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
    projectiveLine_eq_projectiveRadicalAxis_of_common_points
      Gamma C hGammaC haGamma hbGamma haC hbC hab
  have hCDline : projectiveLine c d hcd' =
      projectiveRadicalAxis Gamma D hGammaD :=
    projectiveLine_eq_projectiveRadicalAxis_of_common_points
      Gamma D hGammaD hcGamma hdGamma hcD hdD hcd'
  have hXYCD : projectiveLine x y hxy =
      projectiveRadicalAxis C D hCD :=
    projectiveLine_eq_projectiveRadicalAxis_of_common_points
      C D hCD hxC hyC hxD hyD hxy
  have hXYCK : projectiveLine x y hxy =
      projectiveRadicalAxis C K hCK :=
    projectiveLine_eq_projectiveRadicalAxis_of_common_points
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

/-! ## The actual circle-page K2.1 endpoint -/

/-- A proper-circle page through three outsiders cannot have all three
outsider edges double-hosted by proper circles on a selected proper
five-conic.  The four displayed marked points are the complement of the
page's one marked point, so none lies on the page. -/
theorem properCircle_circlePage_allDoubleTriangle_absurd
    (Gamma K : ProperCircle)
    {a b c d x y z : Point2}
    (haGamma : a ∈ (Gamma.1 : Set Point2))
    (hbGamma : b ∈ (Gamma.1 : Set Point2))
    (hcGamma : c ∈ (Gamma.1 : Set Point2))
    (hdGamma : d ∈ (Gamma.1 : Set Point2))
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    (hxK : x ∈ (K.1 : Set Point2))
    (hyK : y ∈ (K.1 : Set Point2))
    (hzK : z ∈ (K.1 : Set Point2))
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (haNotK : a ∉ (K.1 : Set Point2))
    (hbNotK : b ∉ (K.1 : Set Point2))
    (hcNotK : c ∉ (K.1 : Set Point2))
    (hdNotK : d ∉ (K.1 : Set Point2))
    (hxNotGamma : x ∉ (Gamma.1 : Set Point2))
    (hyNotGamma : y ∉ (Gamma.1 : Set Point2))
    (hzNotGamma : z ∉ (Gamma.1 : Set Point2))
    (CAB CCD CAC CBD CAD CBC : ProperCircle)
    (hCABCCD : CAB ≠ CCD) (hCACCBD : CAC ≠ CBD)
    (hCADCBC : CAD ≠ CBC)
    (haCAB : a ∈ (CAB.1 : Set Point2))
    (hbCAB : b ∈ (CAB.1 : Set Point2))
    (hxCAB : x ∈ (CAB.1 : Set Point2))
    (hyCAB : y ∈ (CAB.1 : Set Point2))
    (hcCCD : c ∈ (CCD.1 : Set Point2))
    (hdCCD : d ∈ (CCD.1 : Set Point2))
    (hxCCD : x ∈ (CCD.1 : Set Point2))
    (hyCCD : y ∈ (CCD.1 : Set Point2))
    (haCAC : a ∈ (CAC.1 : Set Point2))
    (hcCAC : c ∈ (CAC.1 : Set Point2))
    (hxCAC : x ∈ (CAC.1 : Set Point2))
    (hzCAC : z ∈ (CAC.1 : Set Point2))
    (hbCBD : b ∈ (CBD.1 : Set Point2))
    (hdCBD : d ∈ (CBD.1 : Set Point2))
    (hxCBD : x ∈ (CBD.1 : Set Point2))
    (hzCBD : z ∈ (CBD.1 : Set Point2))
    (haCAD : a ∈ (CAD.1 : Set Point2))
    (hdCAD : d ∈ (CAD.1 : Set Point2))
    (hyCAD : y ∈ (CAD.1 : Set Point2))
    (hzCAD : z ∈ (CAD.1 : Set Point2))
    (hbCBC : b ∈ (CBC.1 : Set Point2))
    (hcCBC : c ∈ (CBC.1 : Set Point2))
    (hyCBC : y ∈ (CBC.1 : Set Point2))
    (hzCBC : z ∈ (CBC.1 : Set Point2)) : False := by
  have hGammaK : Gamma ≠ K := by
    intro hEq
    apply hxNotGamma
    simpa [hEq] using hxK
  have hGammaCAB : Gamma ≠ CAB := by
    intro hEq
    apply hxNotGamma
    simpa [hEq] using hxCAB
  have hGammaCCD : Gamma ≠ CCD := by
    intro hEq
    apply hxNotGamma
    simpa [hEq] using hxCCD
  have hGammaCAC : Gamma ≠ CAC := by
    intro hEq
    apply hxNotGamma
    simpa [hEq] using hxCAC
  have hGammaCBD : Gamma ≠ CBD := by
    intro hEq
    apply hxNotGamma
    simpa [hEq] using hxCBD
  have hGammaCAD : Gamma ≠ CAD := by
    intro hEq
    apply hyNotGamma
    simpa [hEq] using hyCAD
  have hGammaCBC : Gamma ≠ CBC := by
    intro hEq
    apply hyNotGamma
    simpa [hEq] using hyCBC
  have hCABK : CAB ≠ K := by
    intro hEq
    apply haNotK
    simpa [hEq] using haCAB
  have hCACK : CAC ≠ K := by
    intro hEq
    apply haNotK
    simpa [hEq] using haCAC
  have hCADK : CAD ≠ K := by
    intro hEq
    apply haNotK
    simpa [hEq] using haCAD
  have hAB := double_circle_host_direction_on_page_axis
    Gamma K CAB CCD hGammaK hGammaCAB hGammaCCD hCABCCD hCABK
    haGamma hbGamma hcGamma hdGamma haCAB hbCAB hxCAB hyCAB
    hcCCD hdCCD hxCCD hyCCD hxK hyK haNotK hab hcd hxy
  have hAC := double_circle_host_direction_on_page_axis
    Gamma K CAC CBD hGammaK hGammaCAC hGammaCBD hCACCBD hCACK
    haGamma hcGamma hbGamma hdGamma haCAC hcCAC hxCAC hzCAC
    hbCBD hdCBD hxCBD hzCBD hxK hzK haNotK hac hbd hxz
  have hAD := double_circle_host_direction_on_page_axis
    Gamma K CAD CBC hGammaK hGammaCAD hGammaCBC hCADCBC hCADK
    haGamma hdGamma hbGamma hcGamma haCAD hdCAD hyCAD hzCAD
    hbCBC hcCBC hyCBC hzCBC hyK hzK haNotK had hbc hyz
  exact properCircle_allDoubleTriangle_projectiveTrace_absurd
    Gamma haGamma hbGamma hcGamma hdGamma hab hac had hbc hbd hcd
    (projectiveRadicalAxis Gamma K hGammaK) hAB hAC hAD

end Erdos506.Incidence
