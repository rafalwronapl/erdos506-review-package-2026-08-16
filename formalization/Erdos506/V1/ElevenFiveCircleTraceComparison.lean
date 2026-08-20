import Erdos506.V1.ElevenFiveFourStarHarmonicCompletion
import Erdos506.V1.ElevenFiveFourStarNormalTrace
import Erdos506.Incidence.ProjectiveLineParamTransport

/-!
# Canonical five-circle parameters through inversion

This is the geometric half of the remaining circle comparison.  It proves
without any extra hypothesis that the canonical parameter of a proper-circle
point is carried by the explicit pivot-slope `GL₂` map to the affine
parameter of its inverse on the pivot line.  Thus the only remaining step is
to compare that *actual affine line coordinate* with the coordinate selected
by the four-star normal frame.
-/

namespace Erdos506.V1

open Erdos506.Block
open Erdos506.Block.BlockSystem
open Erdos506.Incidence
open Erdos506.V3
open Erdos506.V4
open Matrix
open scoped LinearAlgebra.Projectivization

universe u

noncomputable local instance circleTraceDecidableEqRP1 :
    DecidableEq RealProjectiveOnePoint := Classical.decEq _

/-- The canonical circle parameter of a selected non-pivot point, after the
explicit slope projectivity based at the selected pivot. -/
theorem properCircleTraceParameter_pivotSlope
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    (cfg : Configuration Point) (c : ProperCircle)
    (p q : Point) (hp : p ∈ circleTrace cfg c) (hq : q ∈ circleTrace cfg c)
    (hpq : p ≠ q) :
    properCirclePivotSlopeGL (properCircleInverseVector c (cfg p))
        (properCircleInverseVector_ne_zero c (cfg p)) •
      properCircleTraceParameter cfg c ⟨q, hq⟩ =
        realProjectiveAffinePoint
          (properCirclePointPivotSlope c
            ⟨cfg p, mem_circleTrace.mp hp⟩
            ⟨cfg q, mem_circleTrace.mp hq⟩) := by
  let o : ProperCirclePoint c := ⟨cfg p, mem_circleTrace.mp hp⟩
  let x : ProperCirclePoint c := ⟨cfg q, mem_circleTrace.mp hq⟩
  have hox : o ≠ x := by
    intro h
    apply hpq
    apply cfg.injective
    exact congrArg Subtype.val h
  have hbr := properCircleInverseVector_bracket_ne_zero_of_ne c hox
  simpa [properCircleTraceParameter, properCircleTracePoint,
    properCirclePointParameter, properCirclePointPivotSlope, o, x] using
    (properCirclePivotSlope_projective_eq_affine
      (w := properCircleInverseVector c o.1)
      (u := properCircleInverseVector c x.1)
      (properCircleInverseVector_ne_zero c o.1)
      (properCircleInverseVector_ne_zero c x.1) hbr)

/-- The same explicit projective parameter is the affine coordinate of the
actual inverted selected point on its circle-pivot line. -/
theorem pivotInversion_properCircleTracePoint_eq_pivotSlope
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    (cfg : Configuration Point) (c : ProperCircle)
    (p q : Point) (hp : p ∈ circleTrace cfg c) (hq : q ∈ circleTrace cfg c)
    (hpq : p ≠ q) :
    pivotInversion cfg p ⟨q, hpq.symm⟩ =
      affineParamPoint
        (properCirclePivotLineBase c (properCircleInverseVector c (cfg p)))
        (properCirclePivotLineDirection c
          (properCircleInverseVector c (cfg p)))
        (properCirclePointPivotSlope c
          ⟨cfg p, mem_circleTrace.mp hp⟩
          ⟨cfg q, mem_circleTrace.mp hq⟩) := by
  let o : ProperCirclePoint c := ⟨cfg p, mem_circleTrace.mp hp⟩
  let x : ProperCirclePoint c := ⟨cfg q, mem_circleTrace.mp hq⟩
  have hox : o ≠ x := by
    intro h
    apply hpq
    apply cfg.injective
    exact congrArg Subtype.val h
  simpa [pivotInversion, o, x] using
    (inversion_properCirclePoint_eq_pivotSlope c o x hox)

/-- The finite four-star calculation applies to the actual base line of a
five-circle.  This theorem fixes the required relabelled index explicitly:
the original circle base `r` becomes `σ r` after the survivor relabeling. -/
theorem elevenFive944CircleBase_exists_relabelledNormalTrace
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    (cfg : Configuration Point) (hcard : Fintype.card Point = 11)
    (p : Point) (hpivot : p ∈ elevenFive944Pivots (blockSystem cfg))
    (b : GeometricBlock cfg)
    (hb : b ∈ (blockSystem cfg).circleBlocksOfSize 5)
    (hp : p ∈ geometricBlockSupport cfg b) :
    ∃ σ : Equiv.Perm Finite.FourStarVertex,
      let H := elevenFive944PivotFourStar cfg hcard p hpivot
      let r := elevenFive944CircleBaseIndex cfg hcard p hpivot b hb hp
      let N := ((H.toProjectiveSkeleton H.geometricBoundary).relabel σ).toNormalForm
      N.determinants = fourStarNormalSurvivor ∧
        H.relabelledBaseNormalTrace σ N (σ r) =
          fourStarNormalTraceParameterSet (σ r) := by
  let H := elevenFive944PivotFourStar cfg hcard p hpivot
  let r := elevenFive944CircleBaseIndex cfg hcard p hpivot b hb hp
  obtain ⟨σ, _, hN, htraces⟩ := H.exists_relabelledBaseNormalTrace_eq_normalTrace
  let N := ((H.toProjectiveSkeleton H.geometricBoundary).relabel σ).toNormalForm
  refine ⟨σ, ?_⟩
  change N.determinants = fourStarNormalSurvivor ∧
    H.relabelledBaseNormalTrace σ N (σ r) =
      fourStarNormalTraceParameterSet (σ r)
  exact ⟨hN, htraces (σ r)⟩

/-- The second, normal-frame projectivity is completely explicit once an
affine parametrisation of the actual relabelled base line is fixed.  This is
the precise local calculation needed after choosing two distinct inverted
circle points as affine base and direction. -/
theorem ElevenFivePivotInvertedFourStar.relabelledBaseNormalCoordinate_eq_affineParameterGL
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (H : ElevenFivePivotInvertedFourStar cfg p)
    (σ : Equiv.Perm Finite.FourStarVertex)
    (N : FourStarNormalForm
      ((H.toProjectiveSkeleton H.geometricBoundary).relabel σ))
    (i : Fin 4) (B D : Point2) (hD : D ≠ 0)
    (uD uB : RealProjectiveLineVector)
    (hDimage : N.frame.G • directionLift D = fourStarNormalLineParameter i uD)
    (hBimage : N.frame.G • homogeneousLift B = fourStarNormalLineParameter i uB)
    (x : {x : AwayFrom p // x ∈ H.baseSupport (σ.symm i)})
    (t : ℝ)
    (hx : pivotInversion cfg p x.1 = affineParamPoint B D t) :
    H.relabelledBaseNormalCoordinate σ N i x =
      fourStarNormalLineCoefficientGL N.frame.G B D hD i uD uB
        hDimage hBimage • realProjectiveAffinePoint t := by
  let g := fourStarNormalLineCoefficientGL N.frame.G B D hD i uD uB
    hDimage hBimage
  have hvector : N.frame.G • homogeneousLift (pivotInversion cfg p x.1) =
      fourStarNormalLineParameter i (g • realProjectiveAffineVector t) := by
    rw [hx, ← projectiveAffineLineParameter_affine]
    exact projectiveAffineLineParameter_normal_transport_gl
      N.frame.G B D hD i uD uB hDimage hBimage
      (realProjectiveAffineVector t)
  have hprojective : Projectivization.mk ℝ
      (projectivePointTransform N.frame.G
        (homogeneousLift (pivotInversion cfg p x.1)))
      ((smul_ne_zero_iff_ne N.frame.G).mpr (homogeneousLift_ne_zero _)) =
      Projectivization.mk ℝ
        (fourStarNormalLineParameter i (g • realProjectiveAffineVector t))
        (fourStarNormalLineParameter_ne_zero i
          ((smul_ne_zero_iff_ne g).mpr
            (realProjectiveAffineVector_ne_zero t))) := by
    apply (Projectivization.mk_eq_mk_iff' ℝ _ _
      ((smul_ne_zero_iff_ne N.frame.G).mpr (homogeneousLift_ne_zero _))
      (fourStarNormalLineParameter_ne_zero i
        ((smul_ne_zero_iff_ne g).mpr
          (realProjectiveAffineVector_ne_zero t)))).2
    refine ⟨1, ?_⟩
    simpa [projectivePointTransform] using hvector.symm
  rw [H.relabelledBaseNormalCoordinate_eq_of_projective σ N i x
    (g • realProjectiveAffineVector t)
    ((smul_ne_zero_iff_ne g).mpr (realProjectiveAffineVector_ne_zero t))
    hprojective]
  simp [g, realProjectiveAffinePoint]

/-- Two distinct actual points on a relabelled base line supply the two
coefficient vectors used by `fourStarNormalLineCoefficientGL`.  In
particular, this is not a new geometric assumption: it follows directly
from the canonical-base incidence covector. -/
theorem ElevenFivePivotInvertedFourStar.exists_normalAffineGLData_of_twoBasePoints
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (H : ElevenFivePivotInvertedFourStar cfg p)
    (σ : Equiv.Perm Finite.FourStarVertex)
    (N : FourStarNormalForm
      ((H.toProjectiveSkeleton H.geometricBoundary).relabel σ))
    (i : Fin 4)
    (x y : {x : AwayFrom p // x ∈ H.baseSupport (σ.symm i)})
    (hxy : x ≠ y) :
    ∃ uD uB : RealProjectiveLineVector,
      N.frame.G • directionLift
          (pivotInversion cfg p y.1 - pivotInversion cfg p x.1) =
        fourStarNormalLineParameter i uD ∧
      N.frame.G • homogeneousLift (pivotInversion cfg p x.1) =
        fourStarNormalLineParameter i uB := by
  have hxincident : projectiveCovectorNormalLine i ⬝ᵥ
      (N.frame.G • homogeneousLift (pivotInversion cfg p x.1)) = 0 :=
    (projectiveCovectorFrame_incident_normal_iff N.frame i _).2 (by
      change H.canonicalBaseCovector (σ.symm i) ⬝ᵥ
          homogeneousLift (pivotInversion cfg p x.1) = 0
      rw [dotProduct_comm]
      exact (H.mem_baseSupport_iff_canonicalIncident (σ.symm i) x.1).mp x.2)
  have hyincident : projectiveCovectorNormalLine i ⬝ᵥ
      (N.frame.G • homogeneousLift (pivotInversion cfg p y.1)) = 0 :=
    (projectiveCovectorFrame_incident_normal_iff N.frame i _).2 (by
      change H.canonicalBaseCovector (σ.symm i) ⬝ᵥ
          homogeneousLift (pivotInversion cfg p y.1) = 0
      rw [dotProduct_comm]
      exact (H.mem_baseSupport_iff_canonicalIncident (σ.symm i) y.1).mp y.2)
  have hlift : directionLift
      (pivotInversion cfg p y.1 - pivotInversion cfg p x.1) =
      homogeneousLift (pivotInversion cfg p y.1) -
        homogeneousLift (pivotInversion cfg p x.1) := by
    ext j
    fin_cases j <;>
      simp [directionLift, homogeneousLift, PiLp.sub_apply]
  have hDincident : projectiveCovectorNormalLine i ⬝ᵥ
      (N.frame.G • directionLift
        (pivotInversion cfg p y.1 - pivotInversion cfg p x.1)) = 0 := by
    rw [hlift, smul_sub, dotProduct_sub, hyincident, hxincident]
    ring
  obtain ⟨uD, huD⟩ :=
    exists_fourStarNormalLineParameter_of_incident i hDincident
  obtain ⟨uB, huB⟩ :=
    exists_fourStarNormalLineParameter_of_incident i hxincident
  exact ⟨uD, uB, huD.symm, huB.symm⟩

/-- Every relabelled four-star base has two distinct actual support points.
This packages the only finite choice needed to form an affine frame on that
base line. -/
theorem ElevenFivePivotInvertedFourStar.exists_two_relabelledBasePoints
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (H : ElevenFivePivotInvertedFourStar cfg p)
    (σ : Equiv.Perm Finite.FourStarVertex)
    (i : Fin 4) :
    ∃ x y : {x : AwayFrom p // x ∈ H.baseSupport (σ.symm i)}, x ≠ y := by
  apply Fintype.exists_pair_of_one_lt_card
  rw [Fintype.card_coe, H.baseSupport_card]
  norm_num

/-- The affine direction determined by two distinct deleted labels is
nonzero, so the normal-line coefficient matrix above is genuinely in
`GL₂`. -/
theorem pivotInversion_sub_ne_zero_of_ne
    {Point : Type u} [Fintype Point]
    (cfg : Configuration Point) (p : Point)
    (x y : AwayFrom p) (hxy : x ≠ y) :
    pivotInversion cfg p y - pivotInversion cfg p x ≠ 0 := by
  intro hzero
  apply hxy
  apply (pivotInversion cfg p).injective
  exact (sub_eq_zero.mp hzero).symm

/-- Homogeneous affine rebase from a slope coordinate `s` to the coordinate
`(s-a)/(b-a)` based at two distinct slope values `a` and `b`. -/
def pivotSlopeRebaseMatrix (a b : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  ![![1, -a], ![0, b - a]]

@[simp] theorem pivotSlopeRebaseMatrix_det (a b : ℝ) :
    (pivotSlopeRebaseMatrix a b).det = b - a := by
  simp [pivotSlopeRebaseMatrix, Matrix.det_fin_two]

noncomputable def pivotSlopeRebaseGL (a b : ℝ) (hab : b - a ≠ 0) :
    GL (Fin 2) ℝ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (pivotSlopeRebaseMatrix a b) (by
    rw [pivotSlopeRebaseMatrix_det]
    exact hab)

theorem pivotSlopeRebaseGL_smul_affinePoint
    (a b s : ℝ) (hab : b - a ≠ 0) :
    pivotSlopeRebaseGL a b hab • realProjectiveAffinePoint s =
      realProjectiveAffinePoint ((s - a) / (b - a)) := by
  unfold realProjectiveAffinePoint
  rw [Projectivization.smul_mk]
  apply (realProjective_mk_eq_mk_iff_bracket_eq_zero
    ((smul_ne_zero_iff_ne (pivotSlopeRebaseGL a b hab)).mpr
      (realProjectiveAffineVector_ne_zero s))
    (realProjectiveAffineVector_ne_zero _)).mpr
  change realProjectiveBracket
      (pivotSlopeRebaseMatrix a b *ᵥ realProjectiveAffineVector s)
      (realProjectiveAffineVector ((s - a) / (b - a))) = 0
  have hdenom : b - a ≠ 0 := hab
  simp [pivotSlopeRebaseMatrix, Matrix.mulVec, dotProduct,
    Fin.sum_univ_two, realProjectiveBracket, realProjectiveAffineVector]
  field_simp [hdenom]
  ring

/-- Rebased affine coordinates describe the same geometric line. -/
theorem affineParamPoint_rebase
    (B D : Point2) (a b s : ℝ) (hab : b - a ≠ 0) :
    affineParamPoint B D s =
      affineParamPoint (affineParamPoint B D a)
        (affineParamPoint B D b - affineParamPoint B D a)
        ((s - a) / (b - a)) := by
  ext j
  simp only [affineParamPoint_apply, PiLp.sub_apply, PiLp.smul_apply]
  field_simp [hab]
  ring

/-- A finite projective trace is recovered from its image under a `GL₂`
change by applying the inverse change.  This is the final set-theoretic
operation needed after the pointwise parameter comparison. -/
theorem Finset.eq_image_inv_of_image_eq
    (g : GL (Fin 2) ℝ) (S T : Finset RealProjectiveOnePoint)
    (himage : S.image (fun P => g • P) = T) :
    S = T.image (fun P => g⁻¹ • P) := by
  calc
    S = S.image (fun P => g⁻¹ • (g • P)) := by
      simpa [smul_smul] using (Finset.image_id' S).symm
    _ = (S.image (fun P => g • P)).image (fun P => g⁻¹ • P) := by
      rw [Finset.image_image]
      rfl
    _ = T.image (fun P => g⁻¹ • P) := by rw [himage]

/-- The canonical proper-circle trace of every five-circle through a neutral
`(9,4,4)` pivot is the inverse `GL₂` image of the corresponding exact
four-star normal trace. -/
theorem elevenFive944_normalCircleTraceTransport
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    (cfg : Configuration Point) (hcard : Fintype.card Point = 11)
    (p : Point) (hpivot : p ∈ elevenFive944Pivots (blockSystem cfg)) :
    (elevenFive944PivotFourStar cfg hcard p hpivot).HasNormalCircleTraceTransport := by
  classical
  let H := elevenFive944PivotFourStar cfg hcard p hpivot
  intro c hsize hpC
  let b : GeometricBlock cfg := Sum.inr c
  have hb : b ∈ (blockSystem cfg).circleBlocksOfSize 5 := by
    apply (blockSystem cfg).mem_blocksOfKindSize.mpr
    change geometricBlockKind (Sum.inr c) = .circle ∧
      (geometricBlockSupport cfg (Sum.inr c)).card = 5
    exact ⟨rfl, hsize⟩
  let r := elevenFive944CircleBaseIndex cfg hcard p hpivot b hb hpC
  have hbase : H.baseSupport r = awaySupport p (circleTrace cfg c.1) := by
    simpa [H, b] using
      (elevenFive944CircleBaseIndex_support cfg hcard p hpivot b hb hpC)
  obtain ⟨σ, hN, hnormal⟩ :=
    elevenFive944CircleBase_exists_relabelledNormalTrace
      cfg hcard p hpivot b hb hpC
  let i : Fin 4 := σ r
  let N := ((H.toProjectiveSkeleton H.geometricBoundary).relabel σ).toNormalForm
  have hbasei : H.baseSupport (σ.symm i) = awaySupport p (circleTrace cfg c.1) := by
    simpa [i] using hbase
  obtain ⟨x, y, hxy⟩ := H.exists_two_relabelledBasePoints σ i
  have hxC : x.1.1 ∈ circleTrace cfg c.1 := by
    apply mem_awaySupport.mp
    rw [← hbasei]
    exact x.2
  have hyC : y.1.1 ∈ circleTrace cfg c.1 := by
    apply mem_awaySupport.mp
    rw [← hbasei]
    exact y.2
  have hxp : p ≠ x.1.1 := x.1.2.symm
  have hyp : p ≠ y.1.1 := y.1.2.symm
  let a : ℝ := properCirclePointPivotSlope c.1
    ⟨cfg p, mem_circleTrace.mp hpC⟩ ⟨cfg x.1.1, mem_circleTrace.mp hxC⟩
  let d : ℝ := properCirclePointPivotSlope c.1
    ⟨cfg p, mem_circleTrace.mp hpC⟩ ⟨cfg y.1.1, mem_circleTrace.mp hyC⟩
  have hxinv : pivotInversion cfg p x.1 =
      affineParamPoint
        (properCirclePivotLineBase c.1 (properCircleInverseVector c.1 (cfg p)))
        (properCirclePivotLineDirection c.1
          (properCircleInverseVector c.1 (cfg p))) a := by
    simpa [a] using pivotInversion_properCircleTracePoint_eq_pivotSlope
      cfg c.1 p x.1.1 hpC hxC hxp
  have hyinv : pivotInversion cfg p y.1 =
      affineParamPoint
        (properCirclePivotLineBase c.1 (properCircleInverseVector c.1 (cfg p)))
        (properCirclePivotLineDirection c.1
          (properCircleInverseVector c.1 (cfg p))) d := by
    simpa [d] using pivotInversion_properCircleTracePoint_eq_pivotSlope
      cfg c.1 p y.1.1 hpC hyC hyp
  have hda : d - a ≠ 0 := by
    intro hzero
    have hda' : d = a := sub_eq_zero.mp hzero
    have hinv : pivotInversion cfg p y.1 = pivotInversion cfg p x.1 := by
      rw [hyinv, hxinv, hda']
    apply hxy
    apply Subtype.ext
    exact (pivotInversion cfg p).injective hinv.symm
  obtain ⟨uD, uB, hDimage, hBimage⟩ :=
    H.exists_normalAffineGLData_of_twoBasePoints σ N i x y hxy
  let gN := fourStarNormalLineCoefficientGL N.frame.G
    (pivotInversion cfg p x.1)
    (pivotInversion cfg p y.1 - pivotInversion cfg p x.1)
    (pivotInversion_sub_ne_zero_of_ne cfg p x.1 y.1
      (fun h => hxy (Subtype.ext h)))
    i uD uB hDimage hBimage
  let gR := pivotSlopeRebaseGL a d hda
  let gS := properCirclePivotSlopeGL
    (properCircleInverseVector c.1 (cfg p))
    (properCircleInverseVector_ne_zero c.1 (cfg p))
  let K : GL (Fin 2) ℝ := gN * gR * gS
  have hcoordinate (z : {z : AwayFrom p // z ∈ H.baseSupport (σ.symm i)})
      (hzC : z.1.1 ∈ circleTrace cfg c.1) :
      H.relabelledBaseNormalCoordinate σ N i z =
        K • properCircleTraceParameter cfg c.1 ⟨z.1.1, hzC⟩ := by
    have hzp : p ≠ z.1.1 := z.1.2.symm
    let s : ℝ := properCirclePointPivotSlope c.1
      ⟨cfg p, mem_circleTrace.mp hpC⟩
      ⟨cfg z.1.1, mem_circleTrace.mp hzC⟩
    have hzinv : pivotInversion cfg p z.1 =
        affineParamPoint
          (properCirclePivotLineBase c.1 (properCircleInverseVector c.1 (cfg p)))
          (properCirclePivotLineDirection c.1
            (properCircleInverseVector c.1 (cfg p))) s := by
      simpa [s] using pivotInversion_properCircleTracePoint_eq_pivotSlope
        cfg c.1 p z.1.1 hpC hzC hzp
    have hzrebase : pivotInversion cfg p z.1 =
        affineParamPoint (pivotInversion cfg p x.1)
          (pivotInversion cfg p y.1 - pivotInversion cfg p x.1)
          ((s - a) / (d - a)) := by
      calc
        pivotInversion cfg p z.1 =
            affineParamPoint
              (properCirclePivotLineBase c.1
                (properCircleInverseVector c.1 (cfg p)))
              (properCirclePivotLineDirection c.1
                (properCircleInverseVector c.1 (cfg p))) s := hzinv
        _ = affineParamPoint
              (affineParamPoint
                (properCirclePivotLineBase c.1
                  (properCircleInverseVector c.1 (cfg p)))
                (properCirclePivotLineDirection c.1
                  (properCircleInverseVector c.1 (cfg p))) a)
              (affineParamPoint
                (properCirclePivotLineBase c.1
                  (properCircleInverseVector c.1 (cfg p)))
                (properCirclePivotLineDirection c.1
                  (properCircleInverseVector c.1 (cfg p))) d -
                affineParamPoint
                  (properCirclePivotLineBase c.1
                    (properCircleInverseVector c.1 (cfg p)))
                  (properCirclePivotLineDirection c.1
                    (properCircleInverseVector c.1 (cfg p))) a)
              ((s - a) / (d - a)) :=
            affineParamPoint_rebase
              (properCirclePivotLineBase c.1
                (properCircleInverseVector c.1 (cfg p)))
              (properCirclePivotLineDirection c.1
                (properCircleInverseVector c.1 (cfg p))) a d s hda
        _ = affineParamPoint (pivotInversion cfg p x.1)
              (pivotInversion cfg p y.1 - pivotInversion cfg p x.1)
              ((s - a) / (d - a)) := by rw [← hxinv, ← hyinv]
    have hnormalcoord := H.relabelledBaseNormalCoordinate_eq_affineParameterGL
      σ N i (pivotInversion cfg p x.1)
      (pivotInversion cfg p y.1 - pivotInversion cfg p x.1)
      (pivotInversion_sub_ne_zero_of_ne cfg p x.1 y.1
        (fun h => hxy (Subtype.ext h))) uD uB hDimage hBimage z
      ((s - a) / (d - a)) hzrebase
    have hslope : gS • properCircleTraceParameter cfg c.1 ⟨z.1.1, hzC⟩ =
        realProjectiveAffinePoint s := by
      simpa [gS, s] using properCircleTraceParameter_pivotSlope
        cfg c.1 p z.1.1 hpC hzC hzp
    have hrebase : gR • realProjectiveAffinePoint s =
        realProjectiveAffinePoint ((s - a) / (d - a)) := by
      simpa [gR] using pivotSlopeRebaseGL_smul_affinePoint a d s hda
    calc
      H.relabelledBaseNormalCoordinate σ N i z =
          gN • realProjectiveAffinePoint ((s - a) / (d - a)) := by
        simpa [gN] using hnormalcoord
      _ = gN • (gR • realProjectiveAffinePoint s) := by rw [hrebase]
      _ = gN • (gR • (gS • properCircleTraceParameter cfg c.1
          ⟨z.1.1, hzC⟩)) := by rw [hslope]
      _ = K • properCircleTraceParameter cfg c.1 ⟨z.1.1, hzC⟩ := by
        simp only [K, mul_smul]
  let S := properCircleTraceParameterSetErase cfg c.1 ⟨p, hpC⟩
  have hsource (q : {q : Point // q ∈ circleTrace cfg c.1})
      (hqp : q.1 ≠ p) : properCircleTraceParameter cfg c.1 q ∈ S := by
    unfold S properCircleTraceParameterSetErase
    apply Finset.mem_erase.mpr
    constructor
    · intro heq
      apply hqp
      have hqeq := properCircleTraceParameter_injective cfg c.1 heq
      exact congrArg Subtype.val hqeq
    · exact properCircleTraceParameter_mem_parameterSet cfg c.1 q
  have himage : S.image (fun P => K • P) =
      H.relabelledBaseNormalTrace σ N i := by
    ext Q
    constructor
    · intro hQ
      rcases Finset.mem_image.mp hQ with ⟨P, hP, rfl⟩
      unfold S properCircleTraceParameterSetErase properCircleTraceParameterSet at hP
      rcases Finset.mem_erase.mp hP with ⟨hPne, hPmem⟩
      rcases Finset.mem_map.mp hPmem with ⟨q, _hq, hqP⟩
      have hqP' : properCircleTraceParameter cfg c.1 q = P := by
        simpa [properCircleTraceParameterEmbedding] using hqP
      have hqp : q.1 ≠ p := by
        intro hq
        apply hPne
        rw [← hqP']
        congr
        exact Subtype.ext hq
      let z : {z : AwayFrom p // z ∈ H.baseSupport (σ.symm i)} :=
        ⟨⟨q.1, hqp⟩, by
          rw [hbasei]
          exact mem_awaySupport.mpr q.2⟩
      apply Finset.mem_image.mpr
      refine ⟨z, Finset.mem_univ _, ?_⟩
      exact (hcoordinate z q.2).trans
        (congrArg (fun Q : RealProjectiveOnePoint => K • Q) hqP')
    · intro hQ
      rcases Finset.mem_image.mp hQ with ⟨z, _hz, rfl⟩
      have hzC : z.1.1 ∈ circleTrace cfg c.1 := by
        apply mem_awaySupport.mp
        rw [← hbasei]
        exact z.2
      apply Finset.mem_image.mpr
      let q : {q : Point // q ∈ circleTrace cfg c.1} := ⟨z.1.1, hzC⟩
      refine ⟨properCircleTraceParameter cfg c.1 q, hsource q z.1.2, ?_⟩
      simpa [q] using (hcoordinate z hzC).symm
  refine ⟨i, K, ?_⟩
  calc
    properCircleTraceParameterSetErase cfg c.1 ⟨p, hpC⟩ =
        (H.relabelledBaseNormalTrace σ N i).image (fun P => K⁻¹ • P) :=
      Finset.eq_image_inv_of_image_eq K S
        (H.relabelledBaseNormalTrace σ N i) himage
    _ = (fourStarNormalTraceParameterSet i).image (fun P => K⁻¹ • P) := by
      rw [hnormal]

/-!
The preceding calculations are unconditional.  The remaining assembly is
finite: choose two distinct of the four deleted circle labels, rebase the
pivot-slope affine coordinate at those two values, and map the resulting
four-element finite trace through the two explicit `GL₂` elements above.
No additional circle-incidence or harmonicity principle is required.
-/

end Erdos506.V1
