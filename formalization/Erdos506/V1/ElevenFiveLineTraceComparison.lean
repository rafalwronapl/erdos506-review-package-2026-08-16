import Erdos506.V1.ElevenFiveInversionLineParameter
import Erdos506.V1.ElevenFiveCircleTraceComparison
import Erdos506.Incidence.DeterminedLineProjectiveRealization

/-!
# The remaining parameter comparison on a five-line

The four-star calculation already identifies the inverse-coordinate trace of
the four points left after a pivot deletion.  What remains is one geometric
statement: the one parameter chosen on the original five-line, restricted
away from the pivot, is related to that inverse coordinate by a projective
change of parameter.  This file states that equality without hiding it in a
new structure hypothesis, and proves that it is precisely enough for the
existing five-line harmonic cap.

The shifted inversion matrix in `ElevenFiveInversionLineParameter` supplies
the first factor of the required projectivity.  The remaining factor is the
normal-frame coordinate change on the inverted base line.
-/

namespace Erdos506.V1

open Erdos506.Block
open Erdos506.Block.BlockSystem
open Erdos506.Incidence
open Erdos506.V3
open Erdos506.V4
open scoped LinearAlgebra.Projectivization

universe u

noncomputable local instance lineTraceDecidableEqRP1 :
    DecidableEq RealProjectiveOnePoint := Classical.decEq _

/-! ## The common affine parameter of the original five-line

`determinedLineProjectiveParameter` predates the trace comparison and only
records the bare existence of an embedding.  The following data retains the
actual spanning pair and its affine-coordinate equation.  This is the
coordinate that is shared by every possible pivot on the original line.
-/

/-- A concrete affine chart of a determined line, with its defining
spanning pair and the equation satisfied by every labelled point. -/
structure DeterminedLineAffineParameterData
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    (cfg : Configuration Point) (L : DeterminedLine cfg) where
  origin : Point
  endpoint : Point
  origin_ne_endpoint : origin ≠ endpoint
  coordinate : {x : Point // x ∈ lineSupport cfg L} → ℝ
  coordinate_spec : ∀ x : {x : Point // x ∈ lineSupport cfg L},
    affineParamPoint (cfg origin) (cfg endpoint - cfg origin) (coordinate x) = cfg x.1

/-- The canonical affine chart obtained from the canonical `exists_pair`
description of a determined line.  The construction is entirely geometric:
membership in the line is converted to a point of the affine span of its two
chosen endpoints. -/
private theorem exists_determinedLineCanonicalAffineParameterData
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    (cfg : Configuration Point) (L : DeterminedLine cfg) :
    ∃ D : DeterminedLineAffineParameterData cfg L, True := by
  classical
  let A := L.spanningPair
  have hA : lineOfPair cfg A = L.1 := L.spanningPair_spec
  obtain ⟨a, b, hab, hAcard⟩ := Finset.card_eq_two.mp A.2
  have hAeq : A = ⟨{a, b}, by simp [hab]⟩ := by
    apply Subtype.ext
    exact hAcard
  have hL : L.1 = affineSpan ℝ ({cfg a, cfg b} : Set Point2) := by
    calc
      L.1 = lineOfPair cfg A := hA.symm
      _ = lineOfPair cfg ⟨{a, b}, by simp [hab]⟩ := by rw [hAeq]
      _ = affineSpan ℝ ({cfg a, cfg b} : Set Point2) := by
        simpa using (lineOfPair_pair cfg hab)
  let coordinate : {x : Point // x ∈ lineSupport cfg L} → ℝ := fun x =>
    Classical.choose <| (mem_affineSpan_pair_iff_exists_lineMap_eq).mp (by
      rw [← hL]
      exact mem_lineSupport.mp x.2)
  refine ⟨⟨a, b, hab, coordinate, ?_⟩, trivial⟩
  intro x
  exact (affineParamPoint_eq_lineMap (cfg a) (cfg b) (coordinate x)).trans
    (Classical.choose_spec <|
      (mem_affineSpan_pair_iff_exists_lineMap_eq).mp (by
        rw [← hL]
        exact mem_lineSupport.mp x.2))

/-- The canonical affine chart, selected once from the preceding genuine
existence theorem. -/
noncomputable def determinedLineCanonicalAffineParameterData
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    (cfg : Configuration Point) (L : DeterminedLine cfg) :
    DeterminedLineAffineParameterData cfg L :=
  Classical.choose (exists_determinedLineCanonicalAffineParameterData cfg L)

/-- Homogenising the preceding affine coordinate gives the fixed projective
parameter of the whole original line. -/
noncomputable def DeterminedLineAffineParameterData.projectiveParameter
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {L : DeterminedLine cfg}
    (D : DeterminedLineAffineParameterData cfg L) :
    {x : Point // x ∈ lineSupport cfg L} ↪ RealProjectiveOnePoint where
  toFun x := realProjectiveAffinePoint (D.coordinate x)
  inj' := by
    intro x y hxy
    have hbracket :
        realProjectiveBracket
            (realProjectiveAffineVector (D.coordinate x))
            (realProjectiveAffineVector (D.coordinate y)) = 0 := by
      exact (realProjective_mk_eq_mk_iff_bracket_eq_zero
        (realProjectiveAffineVector_ne_zero (D.coordinate x))
        (realProjectiveAffineVector_ne_zero (D.coordinate y))).mp hxy
    have hcoordinate : D.coordinate x = D.coordinate y := by
      exact sub_eq_zero.mp (by
        simpa [realProjectiveBracket, realProjectiveAffineVector] using hbracket)
    apply Subtype.ext
    apply cfg.injective
    calc
      cfg x.1 = affineParamPoint (cfg D.origin)
          (cfg D.endpoint - cfg D.origin) (D.coordinate x) :=
        (D.coordinate_spec x).symm
      _ = affineParamPoint (cfg D.origin)
          (cfg D.endpoint - cfg D.origin) (D.coordinate y) := by
        rw [hcoordinate]
      _ = cfg y.1 := D.coordinate_spec y

@[simp] theorem DeterminedLineAffineParameterData.projectiveParameter_apply
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {L : DeterminedLine cfg}
    (D : DeterminedLineAffineParameterData cfg L)
    (x : {x : Point // x ∈ lineSupport cfg L}) :
    D.projectiveParameter x = realProjectiveAffinePoint (D.coordinate x) := rfl

/-- Every point of the canonical projective trace has the displayed affine
representative in the one chart shared by all pivot deletions. -/
theorem DeterminedLineAffineParameterData.projectiveParameter_spec
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {L : DeterminedLine cfg}
    (D : DeterminedLineAffineParameterData cfg L)
    (x : {x : Point // x ∈ lineSupport cfg L}) :
    affineParamPoint (cfg D.origin) (cfg D.endpoint - cfg D.origin)
        (D.coordinate x) = cfg x.1 :=
  D.coordinate_spec x

/-- On a genuine five-line, unwrap the line carrier and obtain the common
affine/projective parameter together with its literal spanning-pair spec.
No arbitrary parameter choice is used. -/
theorem elevenFive944_exists_commonAffineProjectiveParameter
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    (cfg : Configuration Point)
    (b : GeometricBlock cfg)
    (hb : b ∈ (blockSystem cfg).lineBlocksOfSize 5) :
    ∃ (L : DeterminedLine cfg) (hL : b = Sum.inl L)
      (D : DeterminedLineAffineParameterData cfg L),
      ∀ x : {x : Point // x ∈ geometricBlockSupport cfg b},
        ∃ y : {y : Point // y ∈ lineSupport cfg L},
          y.1 = x.1 ∧
          D.projectiveParameter y = realProjectiveAffinePoint (D.coordinate y) ∧
          affineParamPoint (cfg D.origin) (cfg D.endpoint - cfg D.origin)
            (D.coordinate y) = cfg x.1 := by
  classical
  have hkind := ((blockSystem cfg).mem_blocksOfKindSize.mp hb).1
  cases b with
  | inl L =>
      let D := determinedLineCanonicalAffineParameterData cfg L
      refine ⟨L, rfl, D, ?_⟩
      intro x
      let y : {y : Point // y ∈ lineSupport cfg L} := ⟨x.1, x.2⟩
      refine ⟨y, rfl, rfl, ?_⟩
      exact D.coordinate_spec y
  | inr c =>
      change BlockKind.circle = BlockKind.line at hkind
      cases hkind

/-- The normal coordinate of a deleted point of a five-line is obtained from
the one common original-line parameter by an explicit product of the shifted
inversion projectivity, an affine rebase, and the normal-frame projectivity.
The affine rebase is chosen from two actual points of the inverted base, so
all its nonsingularity obligations are geometric consequences. -/
theorem elevenFive944_fiveLineNormalCoordinateTransport
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    (cfg : Configuration Point) (hcard : Fintype.card Point = 11)
    (L : DeterminedLine cfg) (p : Point)
    (hLfive : (lineSupport cfg L).card = 5)
    (hpivot : p ∈ elevenFive944Pivots (blockSystem cfg))
    (hp : p ∈ lineSupport cfg L) :
    let D := determinedLineCanonicalAffineParameterData cfg L
    let H := elevenFive944PivotFourStar cfg hcard p hpivot
    let b : GeometricBlock cfg := Sum.inl L
    let hb : b ∈ (blockSystem cfg).lineBlocksOfSize 5 := by
      exact (blockSystem cfg).mem_blocksOfKindSize.mpr ⟨rfl, by
        simpa [b, geometricBlockSupport] using
          hLfive⟩
    ∀ (σ : Equiv.Perm Finite.FourStarVertex)
      (N : FourStarNormalForm
        ((H.toProjectiveSkeleton H.geometricBoundary).relabel σ))
      (i : Fin 4)
      (hi : i = σ (elevenFive944LineBaseIndex cfg hcard p hpivot b hb hp)),
      ∃ K : GL (Fin 2) ℝ,
        ∀ z : {z : AwayFrom p // z ∈ H.baseSupport (σ.symm i)},
          H.relabelledBaseNormalCoordinate σ N i z =
            K • D.projectiveParameter
              ⟨z.1.1, by
                have hbase := elevenFive944LineBaseIndex_support
                  cfg hcard p hpivot b hb hp
                have hbase' : H.baseSupport
                    (elevenFive944LineBaseIndex cfg hcard p hpivot b hb hp) =
                    awaySupport p (lineSupport cfg L) := by
                  simpa [b, geometricBlockSupport] using hbase
                apply mem_awaySupport.mp
                rw [← hbase']
                simpa [hi] using z.2⟩ := by
  classical
  dsimp only
  let D := determinedLineCanonicalAffineParameterData cfg L
  let H := elevenFive944PivotFourStar cfg hcard p hpivot
  let b : GeometricBlock cfg := Sum.inl L
  let hb : b ∈ (blockSystem cfg).lineBlocksOfSize 5 :=
    (blockSystem cfg).mem_blocksOfKindSize.mpr ⟨rfl, by
      simpa [b, geometricBlockSupport] using hLfive⟩
  intro σ N i hi
  obtain ⟨x, y, hxy⟩ := H.exists_two_relabelledBasePoints σ i
  let v : Point2 := cfg D.endpoint - cfg D.origin
  have hv : v ≠ 0 := by
    intro hv0
    apply D.origin_ne_endpoint
    apply cfg.injective
    exact (sub_eq_zero.mp hv0).symm
  let pp : {q : Point // q ∈ lineSupport cfg L} := ⟨p, hp⟩
  let a : ℝ := D.coordinate pp
  have hbase : H.baseSupport (elevenFive944LineBaseIndex cfg hcard p hpivot b hb hp) =
      awaySupport p (lineSupport cfg L) := by
    simpa [b, geometricBlockSupport] using
      (elevenFive944LineBaseIndex_support cfg hcard p hpivot b hb hp)
  have hbasei : H.baseSupport (σ.symm i) = awaySupport p (lineSupport cfg L) := by
    simpa [hi] using hbase
  have hxL : x.1.1 ∈ lineSupport cfg L := by
    apply mem_awaySupport.mp
    rw [← hbasei]
    exact x.2
  have hyL : y.1.1 ∈ lineSupport cfg L := by
    apply mem_awaySupport.mp
    rw [← hbasei]
    exact y.2
  let xx : {q : Point // q ∈ lineSupport cfg L} := ⟨x.1.1, hxL⟩
  let yy : {q : Point // q ∈ lineSupport cfg L} := ⟨y.1.1, hyL⟩
  let sx : ℝ := D.coordinate xx
  let sy : ℝ := D.coordinate yy
  have hpx : sx - a ≠ 0 := by
    intro hzero
    apply x.1.2
    apply cfg.injective
    calc
      cfg x.1.1 = affineParamPoint (cfg D.origin) v sx := by
        simpa [v, sx, xx] using (D.coordinate_spec xx).symm
      _ = affineParamPoint (cfg D.origin) v a := by rw [sub_eq_zero.mp hzero]
      _ = cfg p := by simpa [v, a, pp] using D.coordinate_spec pp
  have hpy : sy - a ≠ 0 := by
    intro hzero
    apply y.1.2
    apply cfg.injective
    calc
      cfg y.1.1 = affineParamPoint (cfg D.origin) v sy := by
        simpa [v, sy, yy] using (D.coordinate_spec yy).symm
      _ = affineParamPoint (cfg D.origin) v a := by rw [sub_eq_zero.mp hzero]
      _ = cfg p := by simpa [v, a, pp] using D.coordinate_spec pp
  let tx : ℝ := (directionSq v * (sx - a))⁻¹
  let ty : ℝ := (directionSq v * (sy - a))⁻¹
  have hxinv : pivotInversion cfg p x.1 = affineParamPoint (cfg p) v tx := by
    change EuclideanGeometry.inversion (cfg p) 1 (cfg x.1.1) = _
    rw [← D.coordinate_spec pp, ← D.coordinate_spec xx]
    simpa [tx] using inversion_affineParamPoint_shared_parameter
      (cfg D.origin) v a sx hv hpx
  have hyinv : pivotInversion cfg p y.1 = affineParamPoint (cfg p) v ty := by
    change EuclideanGeometry.inversion (cfg p) 1 (cfg y.1.1) = _
    rw [← D.coordinate_spec pp, ← D.coordinate_spec yy]
    simpa [ty] using inversion_affineParamPoint_shared_parameter
      (cfg D.origin) v a sy hv hpy
  have htyx : ty - tx ≠ 0 := by
    intro hzero
    apply hxy
    apply Subtype.ext
    apply (pivotInversion cfg p).injective
    rw [hyinv, hxinv, sub_eq_zero.mp hzero]
  obtain ⟨uD, uB, hDimage, hBimage⟩ :=
    H.exists_normalAffineGLData_of_twoBasePoints σ N i x y hxy
  let gN := fourStarNormalLineCoefficientGL N.frame.G
    (pivotInversion cfg p x.1)
    (pivotInversion cfg p y.1 - pivotInversion cfg p x.1)
    (pivotInversion_sub_ne_zero_of_ne cfg p x.1 y.1
      (fun h => hxy (Subtype.ext h))) i uD uB hDimage hBimage
  let gR := pivotSlopeRebaseGL tx ty htyx
  let gI := pivotLineInversionShiftGL (directionSq v) a (by
    intro hz
    exact hv ((directionSq_eq_zero_iff v).mp hz))
  refine ⟨gN * gR * gI, ?_⟩
  intro z
  have hzL : z.1.1 ∈ lineSupport cfg L := by
    apply mem_awaySupport.mp
    rw [← hbasei]
    exact z.2
  let zz : {q : Point // q ∈ lineSupport cfg L} := ⟨z.1.1, hzL⟩
  let sz : ℝ := D.coordinate zz
  have hpz : sz - a ≠ 0 := by
    intro hzero
    apply z.1.2
    apply cfg.injective
    calc
      cfg z.1.1 = affineParamPoint (cfg D.origin) v sz := by
        simpa [v, sz, zz] using (D.coordinate_spec zz).symm
      _ = affineParamPoint (cfg D.origin) v a := by rw [sub_eq_zero.mp hzero]
      _ = cfg p := by simpa [v, a, pp] using D.coordinate_spec pp
  let tz : ℝ := (directionSq v * (sz - a))⁻¹
  have hzinv : pivotInversion cfg p z.1 = affineParamPoint (cfg p) v tz := by
    change EuclideanGeometry.inversion (cfg p) 1 (cfg z.1.1) = _
    rw [← D.coordinate_spec pp, ← D.coordinate_spec zz]
    simpa [tz] using inversion_affineParamPoint_shared_parameter
      (cfg D.origin) v a sz hv hpz
  have hzrebase : pivotInversion cfg p z.1 =
      affineParamPoint (pivotInversion cfg p x.1)
        (pivotInversion cfg p y.1 - pivotInversion cfg p x.1)
        ((tz - tx) / (ty - tx)) := by
    calc
      pivotInversion cfg p z.1 = affineParamPoint (cfg p) v tz := hzinv
      _ = affineParamPoint (affineParamPoint (cfg p) v tx)
          (affineParamPoint (cfg p) v ty - affineParamPoint (cfg p) v tx)
          ((tz - tx) / (ty - tx)) :=
        affineParamPoint_rebase (cfg p) v tx ty tz htyx
      _ = _ := by rw [← hxinv, ← hyinv]
  have hnormal := H.relabelledBaseNormalCoordinate_eq_affineParameterGL
    σ N i (pivotInversion cfg p x.1)
    (pivotInversion cfg p y.1 - pivotInversion cfg p x.1)
    (pivotInversion_sub_ne_zero_of_ne cfg p x.1 y.1
      (fun h => hxy (Subtype.ext h))) uD uB hDimage hBimage z
    ((tz - tx) / (ty - tx)) hzrebase
  have hinversion : gI • D.projectiveParameter zz = realProjectiveAffinePoint tz := by
    simpa [gI, D.projectiveParameter_apply, tz] using
      pivotLineInversionShiftGL_smul_affinePoint (directionSq v) a sz
        (by
          intro hz
          exact hv ((directionSq_eq_zero_iff v).mp hz)) hpz
  have hrebase : gR • realProjectiveAffinePoint tz =
      realProjectiveAffinePoint ((tz - tx) / (ty - tx)) := by
    simpa [gR] using pivotSlopeRebaseGL_smul_affinePoint tx ty tz htyx
  calc
    H.relabelledBaseNormalCoordinate σ N i z =
        gN • realProjectiveAffinePoint ((tz - tx) / (ty - tx)) := by
      simpa [gN] using hnormal
    _ = gN • (gR • realProjectiveAffinePoint tz) := by rw [hrebase]
    _ = gN • (gR • (gI • D.projectiveParameter zz)) := by rw [hinversion]
    _ = (gN * gR * gI) • D.projectiveParameter zz := by simp [mul_smul]

/-- The pointwise common-chart calculation assembles to the public finite
five-line transport.  The normal index is the relabelled actual base
`σ r`; this is exactly the existential index allowed by
`HasFiveLineNormalTraceTransport`. -/
theorem elevenFive944_fiveLineHasNormalTraceTransport
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    (cfg : Configuration Point) (hcard : Fintype.card Point = 11)
    (b : GeometricBlock cfg)
    (hb : b ∈ (blockSystem cfg).lineBlocksOfSize 5) :
    HasFiveLineNormalTraceTransport (blockSystem cfg)
      (elevenFive944Pivots (blockSystem cfg)) b := by
  classical
  have hkind := ((blockSystem cfg).mem_blocksOfKindSize.mp hb).1
  have hsize := ((blockSystem cfg).mem_blocksOfKindSize.mp hb).2
  cases b with
  | inl L =>
      let D := determinedLineCanonicalAffineParameterData cfg L
      refine ⟨D.projectiveParameter, ?_⟩
      intro p hpivot hp
      let H := elevenFive944PivotFourStar cfg hcard p hpivot
      let r := elevenFive944LineBaseIndex cfg hcard p hpivot (Sum.inl L) hb hp
      obtain ⟨σ, hN, hnormal⟩ :=
        elevenFive944LineBase_exists_relabelledBaseNormalTrace_eq_normalTrace
          cfg hcard p hpivot (Sum.inl L) hb hp
      let i : Fin 4 := σ r
      let N := ((H.toProjectiveSkeleton H.geometricBoundary).relabel σ).toNormalForm
      obtain ⟨K, hcoordinate⟩ :=
        elevenFive944_fiveLineNormalCoordinateTransport cfg hcard L p
          (by simpa [geometricBlockSupport] using hsize) hpivot hp σ N i (by rfl)
      let S := (lineBlockProjectiveTrace (blockSystem cfg) (Sum.inl L)
        D.projectiveParameter).erase (D.projectiveParameter ⟨p, hp⟩)
      have hsource (q : {q : Point // q ∈ lineSupport cfg L})
          (hqp : q.1 ≠ p) : D.projectiveParameter q ∈ S := by
        unfold S lineBlockProjectiveTrace
        apply Finset.mem_erase.mpr
        constructor
        · intro heq
          apply hqp
          have hqeq := D.projectiveParameter.injective heq
          exact congrArg Subtype.val hqeq
        · exact Finset.mem_map_of_mem D.projectiveParameter (Finset.mem_univ q)
      have hbasei : H.baseSupport (σ.symm i) = awaySupport p (lineSupport cfg L) := by
        have hbase := elevenFive944LineBaseIndex_support cfg hcard p hpivot
          (Sum.inl L) hb hp
        simpa [i, geometricBlockSupport] using hbase
      have himage : S.image (fun P => K • P) =
          H.relabelledBaseNormalTrace σ N i := by
        ext Q
        constructor
        · intro hQ
          rcases Finset.mem_image.mp hQ with ⟨P, hP, rfl⟩
          unfold S lineBlockProjectiveTrace at hP
          rcases Finset.mem_erase.mp hP with ⟨hPne, hPmem⟩
          rcases Finset.mem_map.mp hPmem with ⟨q, _hq, hqP⟩
          have hqP' : D.projectiveParameter q = P := by
            simpa using hqP
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
          exact (hcoordinate z).trans
            (congrArg (fun Q : RealProjectiveOnePoint => K • Q) hqP')
        · intro hQ
          rcases Finset.mem_image.mp hQ with ⟨z, _hz, rfl⟩
          have hzL : z.1.1 ∈ lineSupport cfg L := by
            apply mem_awaySupport.mp
            rw [← hbasei]
            exact z.2
          let q : {q : Point // q ∈ lineSupport cfg L} := ⟨z.1.1, hzL⟩
          apply Finset.mem_image.mpr
          refine ⟨D.projectiveParameter q, hsource q z.1.2, ?_⟩
          simpa [q] using (hcoordinate z).symm
      refine ⟨i, K, ?_⟩
      calc
        (lineBlockProjectiveTrace (blockSystem cfg) (Sum.inl L)
            D.projectiveParameter).erase (D.projectiveParameter ⟨p, hp⟩) =
            (H.relabelledBaseNormalTrace σ N i).image (fun P => K⁻¹ • P) :=
          Finset.eq_image_inv_of_image_eq K S
            (H.relabelledBaseNormalTrace σ N i) himage
        _ = (fourStarNormalTraceParameterSet i).image (fun P => K⁻¹ • P) := by
          rw [hnormal]
  | inr c =>
      change BlockKind.circle = BlockKind.line at hkind
      cases hkind

/-- The five-line layer has the required cap with no additional transport
hypothesis: every actual five-line carries the common affine chart above. -/
theorem elevenFive944Pivots_fiveLine_cap
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    (cfg : Configuration Point) (hcard : Fintype.card Point = 11) :
    ∀ b ∈ (blockSystem cfg).lineBlocksOfSize 5,
      (elevenFive944Pivots (blockSystem cfg) ∩
        geometricBlockSupport cfg b).card ≤ 2 := by
  intro b hb
  exact elevenFive944Pivots_on_fiveLine_card_le_two_of_normalTraceTransport
    cfg b hb (elevenFive944_fiveLineHasNormalTraceTransport cfg hcard b hb)

/-- The literal unresolved equality for one actual five-line.  Its source is
one fixed parameter of the original line; its target is the actual
inverse-coordinate trace of the particular four-star base obtained after
deleting the pivot.  The equality is deliberately before the final normal
trace simplification, so it can be proved directly from the shifted inversion
formula and the normal-frame parameter transport. -/
def ElevenFive944LineTraceComparison
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    (cfg : Configuration Point) (hcard : Fintype.card Point = 11)
    (b : GeometricBlock cfg)
    (hb : b ∈ (blockSystem cfg).lineBlocksOfSize 5)
    (parameter : {x : Point // x ∈ geometricBlockSupport cfg b} ↪
      RealProjectiveOnePoint) : Prop :=
  ∀ p : Point, ∀ hpivot : p ∈ elevenFive944Pivots (blockSystem cfg),
    ∀ hp : p ∈ geometricBlockSupport cfg b,
      ∃ σ : Equiv.Perm Finite.FourStarVertex,
        let H := elevenFive944PivotFourStar cfg hcard p hpivot
        let r := elevenFive944LineBaseIndex cfg hcard p hpivot b hb hp
        let N := ((H.toProjectiveSkeleton H.geometricBoundary).relabel σ).toNormalForm
        ∃ q : GL (Fin 2) ℝ,
          N.determinants = fourStarNormalSurvivor ∧
            (lineBlockProjectiveTrace (blockSystem cfg) b parameter).erase
                (parameter ⟨p, hp⟩) =
              (H.relabelledBaseNormalTrace σ N (σ r)).image (fun P => q • P)

/-- The literal comparison immediately yields the generic normal-trace
certificate used by the five-line cap.  The target base index is `σ r`, as
it must be: after relabeling, the original base `r` is represented by
`σ r`. -/
theorem ElevenFive944LineTraceComparison.toHasFiveLineNormalTraceTransport
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    (cfg : Configuration Point) (hcard : Fintype.card Point = 11)
    (b : GeometricBlock cfg)
    (hb : b ∈ (blockSystem cfg).lineBlocksOfSize 5)
    (parameter : {x : Point // x ∈ geometricBlockSupport cfg b} ↪
      RealProjectiveOnePoint)
    (hcomparison : ElevenFive944LineTraceComparison cfg hcard b hb parameter) :
    HasFiveLineNormalTraceTransport (blockSystem cfg)
      (elevenFive944Pivots (blockSystem cfg)) b := by
  classical
  refine ⟨parameter, ?_⟩
  intro p hpivot hp
  obtain ⟨σ, q, hN, htrace⟩ := hcomparison p hpivot hp
  let H := elevenFive944PivotFourStar cfg hcard p hpivot
  let r := elevenFive944LineBaseIndex cfg hcard p hpivot b hb hp
  let N := ((H.toProjectiveSkeleton H.geometricBoundary).relabel σ).toNormalForm
  change ∃ i : Fin 4, ∃ g : GL (Fin 2) ℝ,
    (lineBlockProjectiveTrace (blockSystem cfg) b parameter).erase
        (parameter ⟨p, hp⟩) =
      (fourStarNormalTraceParameterSet i).image (fun P => g⁻¹ • P)
  refine ⟨σ r, q⁻¹, ?_⟩
  calc
    (lineBlockProjectiveTrace (blockSystem cfg) b parameter).erase
        (parameter ⟨p, hp⟩) =
      (H.relabelledBaseNormalTrace σ N (σ r)).image (fun P => q • P) := by
        simpa [H, r, N] using htrace
    _ = (fourStarNormalTraceParameterSet (σ r)).image (fun P => q • P) := by
        rw [H.relabelledBaseNormalTrace_eq_normalTrace σ N hN (σ r)]
    _ = (fourStarNormalTraceParameterSet (σ r)).image
        (fun P => (q⁻¹)⁻¹ • P) := by simp

/-- A convenient existential form: proving the one displayed comparison for
the fixed line parameter is enough to discharge the public line-layer
transport condition. -/
theorem hasFiveLineNormalTraceTransport_of_exists_comparison
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    (cfg : Configuration Point) (hcard : Fintype.card Point = 11)
    (b : GeometricBlock cfg)
    (hb : b ∈ (blockSystem cfg).lineBlocksOfSize 5)
  (hcomparison : ∃ parameter :
      {x : Point // x ∈ geometricBlockSupport cfg b} ↪ RealProjectiveOnePoint,
      ElevenFive944LineTraceComparison cfg hcard b hb parameter) :
    HasFiveLineNormalTraceTransport (blockSystem cfg)
      (elevenFive944Pivots (blockSystem cfg)) b := by
  obtain ⟨parameter, hparameter⟩ := hcomparison
  exact ElevenFive944LineTraceComparison.toHasFiveLineNormalTraceTransport
    cfg hcard b hb parameter hparameter

end Erdos506.V1
