import Erdos506.V1.TwelveDirectionFinish
import Erdos506.Incidence.ProjectiveChartTransitivity
import Erdos506.Incidence.ProjectiveCovectorFrame
import Erdos506.Incidence.ProjectiveRepresentativeThreeCollinearity

/-!
# The projective chart in the twelve-direction equality case

The six residual lines of the labelled dual arrangement are regarded, by
self-duality of `RP²`, as six projective points.  The common point of the
five star lines is regarded as the line at infinity.  Transitivity of the
general linear group moves that covector to `[0:0:1]`; the contragredient
map then moves the six dual points into its complementary affine chart.

The multiplicity bound has two roles.  First, no residual line can pass
through the centre of the star (otherwise all six residual lines do).
Second, the six residual dual points cannot be collinear.  The covering
hypothesis says that every one of their joins meets the line at infinity in
one of the star points, so their affine realization has at most five
directions.
-/

namespace Erdos506.V1

open Erdos506.Finite
open Erdos506.Incidence
open Erdos506.V3
open Erdos506.V4
open Matrix
open scoped LinearAlgebra.Projectivization

universe u

noncomputable section

/-! ## Elementary chart algebra -/

/-- The contragredient general-linear transformation attached to `G`. -/
def projectiveDualChartLinear
    (G : GL (Fin 3) ℝ) : GL (Fin 3) ℝ := by
  classical
  apply Matrix.GeneralLinearGroup.mkOfDetNeZero
    ((((G⁻¹ : GL (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ)ᵀ))
  rw [Matrix.det_transpose]
  exact (Matrix.GeneralLinearGroup.det (G⁻¹)).ne_zero

theorem projectiveDualChartLinear_smul
    (G : GL (Fin 3) ℝ) (v : Homogeneous3) :
    projectiveDualChartLinear G • v =
      projectiveCovectorTransform G v := by
  rfl

/-- Dehomogenization in the chart complementary to the last-coordinate
line.  All semantic uses below carry an explicit proof that `v 2 ≠ 0`. -/
def projectiveDualChartPoint (v : Homogeneous3) : Point2 :=
  pointOfCoords (v 0 / v 2) (v 1 / v 2)

@[simp] theorem projectiveDualChartPoint_apply_zero (v : Homogeneous3) :
    projectiveDualChartPoint v 0 = v 0 / v 2 := by
  simp [projectiveDualChartPoint]

@[simp] theorem projectiveDualChartPoint_apply_one (v : Homogeneous3) :
    projectiveDualChartPoint v 1 = v 1 / v 2 := by
  simp [projectiveDualChartPoint]

/-- A finite homogeneous vector is its last coordinate times the canonical
affine lift of its dehomogenization. -/
theorem eq_last_smul_homogeneousLift_projectiveDualChartPoint
    (v : Homogeneous3) (hv : v 2 ≠ 0) :
    v = v 2 • homogeneousLift (projectiveDualChartPoint v) := by
  ext i
  fin_cases i
  · simp [projectiveDualChartPoint]
    rw [mul_comm, div_mul_cancel₀ _ hv]
  · simp [projectiveDualChartPoint]
    rw [mul_comm, div_mul_cancel₀ _ hv]
  · simp [homogeneousLift]

/-- Equal dehomogenizations of two finite nonzero vectors represent the same
projective point. -/
theorem projectivization_eq_of_projectiveDualChartPoint_eq
    (v w : Homogeneous3) (hv : v 2 ≠ 0) (hw : w 2 ≠ 0)
    (hvw : projectiveDualChartPoint v = projectiveDualChartPoint w) :
    Projectivization.mk ℝ v (fun h => hv (congrFun h 2)) =
      Projectivization.mk ℝ w (fun h => hw (congrFun h 2)) := by
  have hzero := congrArg (fun z : Point2 => z 0) hvw
  have hone := congrArg (fun z : Point2 => z 1) hvw
  simp only [projectiveDualChartPoint_apply_zero] at hzero
  simp only [projectiveDualChartPoint_apply_one] at hone
  apply (Projectivization.mk_eq_mk_iff' ℝ _ _ _ _).2
  refine ⟨v 2 / w 2, ?_⟩
  ext i
  fin_cases i
  · change (v 2 / w 2) * w 0 = v 0
    field_simp [hv, hw] at hzero ⊢
    nlinarith
  · change (v 2 / w 2) * w 1 = v 1
    field_simp [hv, hw] at hone ⊢
    nlinarith
  · change (v 2 / w 2) * w 2 = v 2
    exact div_mul_cancel₀ _ hw

/-- If two finite chart points and a nonzero point at infinity are
projectively collinear, the latter spans their affine direction. -/
theorem directionOfPoints_projectiveDualChartPoint_eq
    (v w d : Homogeneous3)
    (hv : v 2 ≠ 0) (hw : w 2 ≠ 0)
    (hvw : projectiveDualChartPoint v ≠ projectiveDualChartPoint w)
    (hdlast : d 2 = 0) (hd : d ≠ 0)
    (hdet : Matrix.det ![v, w, d] = 0) :
    directionOfPoints (projectiveDualChartPoint v)
        (projectiveDualChartPoint w) =
      ℝ ∙ pointOfCoords (d 0) (d 1) := by
  let V := projectiveDualChartPoint v
  let W := projectiveDualChartPoint w
  have hcross : (W 0 - V 0) * d 1 = (W 1 - V 1) * d 0 := by
    have hdet' :
        -(v 0 * w 2 * d 1) + v 1 * w 2 * d 0 +
          v 2 * w 0 * d 1 - v 2 * w 1 * d 0 = 0 := by
      simpa [Matrix.det_fin_three, hdlast] using hdet
    dsimp [V, W]
    simp only [projectiveDualChartPoint_apply_zero,
      projectiveDualChartPoint_apply_one]
    field_simp [hv, hw]
    nlinarith
  have hdxy : pointOfCoords (d 0) (d 1) ≠ 0 := by
    intro hzero
    have hd0 := congrArg (fun z : Point2 => z 0) hzero
    have hd1 := congrArg (fun z : Point2 => z 1) hzero
    simp only [pointOfCoords_apply_zero, Pi.zero_apply] at hd0
    simp only [pointOfCoords_apply_one, Pi.zero_apply] at hd1
    apply hd
    ext i
    fin_cases i
    · exact hd0
    · exact hd1
    · exact hdlast
  unfold directionOfPoints
  rw [Submodule.span_singleton_eq_span_singleton]
  by_cases hx : W 0 - V 0 = 0
  · have hy : W 1 - V 1 ≠ 0 := by
      intro hy
      apply hvw
      change V = W
      ext i
      fin_cases i
      · exact (sub_eq_zero.mp hx).symm
      · exact (sub_eq_zero.mp hy).symm
    have hd0 : d 0 = 0 := by
      have : (W 1 - V 1) * d 0 = 0 := by
        rw [← hcross, hx, zero_mul]
      exact (mul_eq_zero.mp this).resolve_left hy
    have hd1 : d 1 ≠ 0 := by
      intro hd1
      apply hdxy
      ext i
      fin_cases i <;> simp [hd0, hd1]
    let c : ℝ := d 1 / (W 1 - V 1)
    have hc : c ≠ 0 := div_ne_zero hd1 hy
    refine ⟨Units.mk0 c hc, ?_⟩
    ext i
    fin_cases i
    · simpa only [Units.smul_def, Units.val_mk0, Pi.smul_apply,
        PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul,
        pointOfCoords_apply_zero, projectiveDualChartPoint_apply_zero,
        Fin.zero_eta, V, W, c] using
        (show c * (W 0 - V 0) = d 0 by simp [hx, hd0])
    · simpa only [Units.smul_def, Units.val_mk0, Pi.smul_apply,
        PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul,
        pointOfCoords_apply_one, projectiveDualChartPoint_apply_one,
        Fin.mk_one, V, W, c] using
        (div_mul_cancel₀ (d 1) hy)
  · have hd0 : d 0 ≠ 0 := by
      intro hd0
      have hd1 : d 1 = 0 := by
        have : (W 0 - V 0) * d 1 = 0 := by
          rw [hcross, hd0, mul_zero]
        exact (mul_eq_zero.mp this).resolve_left hx
      apply hdxy
      ext i
      fin_cases i <;> simp [hd0, hd1]
    let c : ℝ := d 0 / (W 0 - V 0)
    have hc : c ≠ 0 := div_ne_zero hd0 hx
    refine ⟨Units.mk0 c hc, ?_⟩
    ext i
    fin_cases i
    · simpa only [Units.smul_def, Units.val_mk0, Pi.smul_apply,
        PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul,
        pointOfCoords_apply_zero, projectiveDualChartPoint_apply_zero,
        Fin.zero_eta, V, W, c] using
        (div_mul_cancel₀ (d 0) hx)
    · have hcoord : c * (W 1 - V 1) = d 1 := by
        dsimp [c]
        field_simp [hx]
        nlinarith [hcross]
      simpa only [Units.smul_def, Units.val_mk0, Pi.smul_apply,
        PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul,
        pointOfCoords_apply_one, projectiveDualChartPoint_apply_one,
        Fin.mk_one, V, W, c] using hcoord

/-- Raw representatives detect projective point--line incidence. -/
theorem projective_mem_iff_rep_dot_rep_eq_zero
    (P L : RealProjectivePoint) :
    P ∈ L ↔ P.rep ⬝ᵥ L.rep = 0 := by
  change Projectivization.orthogonal P L ↔ _
  constructor
  · intro h
    rw [← Projectivization.mk_rep P, ← Projectivization.mk_rep L,
      Projectivization.orthogonal_mk] at h
    exact h
  · intro h
    rw [← Projectivization.mk_rep P, ← Projectivization.mk_rep L,
      Projectivization.orthogonal_mk]
    exact h

/-! ## The actual residual arrangement -/

/-- The missing chart bridge named in `TwelveDirectionFinish`. -/
theorem projectiveChartBridge_of_six_dual_lines_covered_by_five_pencil_lines
    {alpha : Type u} [Fintype alpha] [DecidableEq alpha]
    (cfg : Configuration alpha) (p : alpha) (c : DeterminedCircle cfg)
    (hp : p ∈ circleTrace cfg c.1)
    (hresidual : (twelveDirectionResidualLabels cfg p c hp).card = 6)
    (hmult : ∀ q ∈ labelDualVertexSet (restoredPivotConfiguration cfg p),
      (labelDualArrangement
        (restoredPivotConfiguration cfg p)).multiplicity q ≤ 5)
    (hcovered : ∀ {a b : Option (AwayFrom p)},
      a ∈ twelveDirectionResidualLabels cfg p c hp →
      b ∈ twelveDirectionResidualLabels cfg p c hp → a ≠ b →
      ∃ s ∈ twelveDirectionStarLabels cfg p c hp,
        (labelDualArrangement
          (restoredPivotConfiguration cfg p)).Incident
          ((labelDualArrangement
            (restoredPivotConfiguration cfg p)).intersection a b) s) :
    ∃ affineCfg : Configuration (Fin 6),
      Noncollinear affineCfg ∧ (determinedDirections affineCfg).card ≤ 5 := by
  classical
  let restored := restoredPivotConfiguration cfg p
  let A := labelDualArrangement restored
  let R := twelveDirectionResidualLabels cfg p c hp
  let S := twelveDirectionStarLabels cfg p c hp
  let O := twelveDirectionOffStarVertex cfg p c hp

  have hRcard : R.card = 6 := by
    simpa only [R] using hresidual

  have hstarIncident : ∀ s ∈ S, A.Incident O s := by
    intro s hs
    simpa only [A, O, S, restored] using
      (mem_twelveDirectionStarLabels_iff cfg p c hp s).mp hs

  have hnoSixConcurrent :
      ∀ q : RealProjectivePoint,
        (∀ a ∈ R, A.Incident q a) → False := by
    intro q hall
    have hRtwo : 1 < R.card := by omega
    obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp hRtwo
    have hqeq : q = A.intersection a b :=
      A.eq_intersection_of_incident hab (hall a ha) (hall b hb)
    have hqvertex : q ∈ A.vertexSet := by
      rw [hqeq]
      exact A.intersection_mem_vertexSet hab
    have hsub : R ⊆ Finset.univ.filter fun a => A.Incident q a := by
      intro a ha
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hall a ha⟩
    have hsix : 6 ≤ A.multiplicity q := by
      change 6 ≤ (Finset.univ.filter fun a => A.Incident q a).card
      rw [← hRcard]
      exact Finset.card_le_card hsub
    have hfive : A.multiplicity q ≤ 5 := by
      simpa only [A, restored, labelDualVertexSet] using hmult q hqvertex
    omega

  have hresidualAvoids : ∀ a ∈ R, ¬ A.Incident O a := by
    intro a ha haO
    apply hnoSixConcurrent O
    intro b hb
    by_cases hba : b = a
    · simpa [hba] using haO
    · have hab : a ≠ b := by
        intro hab
        exact hba hab.symm
      obtain ⟨s, hs, hqs⟩ := hcovered
        (by simpa only [R] using ha)
        (by simpa only [R] using hb) hab
      have has : a ≠ s := by
        intro has
        subst s
        exact ((mem_twelveDirectionResidualLabels_iff cfg p c hp a).mp
          (by simpa only [R] using ha)).2 (by simpa only [S] using hs)
      have hOeq : O = A.intersection a s :=
        A.eq_intersection_of_incident has haO (hstarIncident s hs)
      have hqeq : A.intersection a b = A.intersection a s :=
        A.eq_intersection_of_incident has
          (A.intersection_incident_left hab) hqs
      rw [hOeq, ← hqeq]
      exact A.intersection_incident_right hab

  have hstarCard : S.card ≤ 5 := by
    by_cases hsmall : S.card ≤ 1
    · omega
    · have htwo : 1 < S.card := by omega
      obtain ⟨s, hs, t, ht, hst⟩ := Finset.one_lt_card.mp htwo
      have hOeq : O = A.intersection s t :=
        A.eq_intersection_of_incident hst
          (hstarIncident s hs) (hstarIncident t ht)
      have hOvertex : O ∈ A.vertexSet := by
        rw [hOeq]
        exact A.intersection_mem_vertexSet hst
      have hsub : S ⊆ Finset.univ.filter fun a => A.Incident O a := by
        intro a ha
        exact Finset.mem_filter.mpr
          ⟨Finset.mem_univ _, hstarIncident a ha⟩
      have hle : S.card ≤ A.multiplicity O := by
        exact Finset.card_le_card hsub
      have hfive : A.multiplicity O ≤ 5 := by
        simpa only [A, restored, labelDualVertexSet] using hmult O hOvertex
      exact hle.trans hfive

  obtain ⟨G₀, scale, hscale, _hGO, hGOrep₀⟩ :=
    exists_generalLinearGroup_smul_rep_eq_projectiveChartOrigin O
  let G : GL (Fin 3) ℝ :=
    (Matrix.GeneralLinearGroup.toLin (n := Fin 3) (R := ℝ)).symm G₀
  have hGvector : ∀ v : Homogeneous3, G • v = G₀ • v := by
    intro v
    change (G : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ v = G₀.toLinearEquiv v
    simpa only [G, MulEquiv.apply_symm_apply, Matrix.mulVecLin_apply] using
      (Matrix.GeneralLinearGroup.toLin_apply G v).symm
  have hGOrep : G • O.rep = scale • projectiveChartOriginVector :=
    (hGvector O.rep).trans hGOrep₀
  let H : GL (Fin 3) ℝ := projectiveDualChartLinear G
  let chartVector : Option (AwayFrom p) → Homogeneous3 := fun a =>
    H • (A.projectiveLine a).rep
  let chartPoint : Option (AwayFrom p) → Point2 := fun a =>
    projectiveDualChartPoint (chartVector a)

  have hchartVector : ∀ a,
      chartVector a = projectiveCovectorTransform G (A.projectiveLine a).rep := by
    intro a
    exact projectiveDualChartLinear_smul G _

  have hchartVector_ne : ∀ a, chartVector a ≠ 0 := by
    intro a
    exact (smul_ne_zero_iff_ne H).mpr (A.projectiveLine a).rep_nonzero

  have hlast_iff : ∀ a, chartVector a 2 = 0 ↔ A.Incident O a := by
    intro a
    let P := A.projectiveLine a
    have hpair := projectiveCovectorTransform_dot_pointTransform
      G P.rep O.rep
    rw [← hchartVector a] at hpair
    change chartVector a ⬝ᵥ (G • O.rep) = P.rep ⬝ᵥ O.rep at hpair
    rw [hGOrep] at hpair
    have hcoordinate : scale * chartVector a 2 = P.rep ⬝ᵥ O.rep := by
      simpa [projectiveChartOriginVector, dotProduct,
        Fin.sum_univ_three, mul_comm] using hpair
    have hincident : A.Incident O a ↔ P.rep ⬝ᵥ O.rep = 0 := by
      change O ∈ P ↔ _
      rw [projective_mem_iff_rep_dot_rep_eq_zero, dotProduct_comm]
    rw [hincident, ← hcoordinate]
    exact ⟨fun h => by simp [h], fun h =>
      (mul_eq_zero.mp h).resolve_left hscale⟩

  have hresidualFinite : ∀ a ∈ R, chartVector a 2 ≠ 0 := by
    intro a ha
    exact fun hzero => hresidualAvoids a ha ((hlast_iff a).mp hzero)

  let base : Fin 6 ≃ ↥R :=
    (Fintype.equivFinOfCardEq
      (by simpa only [Fintype.card_coe] using hRcard)).symm
  let residualLabel : Fin 6 → Option (AwayFrom p) := fun i => (base i).1

  have hresidualLabel_mem : ∀ i, residualLabel i ∈ R := by
    intro i
    exact (base i).2

  have hchartPoint_injective_on_residual :
      Function.Injective (fun i : Fin 6 => chartPoint (residualLabel i)) := by
    intro i j hij
    have hi2 := hresidualFinite (residualLabel i) (hresidualLabel_mem i)
    have hj2 := hresidualFinite (residualLabel j) (hresidualLabel_mem j)
    have hmk := projectivization_eq_of_projectiveDualChartPoint_eq
      (chartVector (residualLabel i)) (chartVector (residualLabel j))
      hi2 hj2 hij
    have htrans :
        H • A.projectiveLine (residualLabel i) =
          H • A.projectiveLine (residualLabel j) := by
      rw [← Projectivization.mk_rep (A.projectiveLine (residualLabel i)),
        ← Projectivization.mk_rep (A.projectiveLine (residualLabel j)),
        Projectivization.smul_mk, Projectivization.smul_mk]
      exact hmk
    have hline : residualLabel i = residualLabel j :=
      A.projectiveLine_injective (MulAction.injective H htrans)
    exact base.injective (Subtype.ext hline)

  let affineCfg : Configuration (Fin 6) :=
    ⟨fun i => chartPoint (residualLabel i),
      hchartPoint_injective_on_residual⟩

  have hnoncollinear : Noncollinear affineCfg := by
    intro hcollinear
    have hzeroOne : affineCfg 0 ≠ affineCfg 1 :=
      affineCfg.injective.ne (by decide)
    let ell := lineCovector (affineCfg 0) (affineCfg 1)
    have hell : ell ≠ 0 := lineCovector_ne_zero hzeroOne
    let qvec : Homogeneous3 := G⁻¹ • ell
    have hqvec : qvec ≠ 0 := (smul_ne_zero_iff_ne G⁻¹).mpr hell
    let q : RealProjectivePoint := Projectivization.mk ℝ qvec hqvec
    have hall : ∀ a ∈ R, A.Incident q a := by
      intro a ha
      let ar : ↥R := ⟨a, ha⟩
      obtain ⟨i, hi⟩ := base.surjective ar
      have hilabel : residualLabel i = a := by
        exact congrArg Subtype.val hi
      have hmem : affineCfg i ∈
          affineSpan ℝ ({affineCfg 0, affineCfg 1} : Set Point2) :=
        hcollinear.mem_affineSpan_of_mem_of_ne
          (show affineCfg 0 ∈ pointSet affineCfg by exact ⟨0, rfl⟩)
          (show affineCfg 1 ∈ pointSet affineCfg by exact ⟨1, rfl⟩)
          (show affineCfg i ∈ pointSet affineCfg by exact ⟨i, rfl⟩)
          hzeroOne
      have hinc : homogeneousLift (affineCfg i) ⬝ᵥ ell = 0 :=
        (homogeneousIncident_lineCovector_iff_mem_affineSpan hzeroOne).2 hmem
      have hi2 := hresidualFinite (residualLabel i) (hresidualLabel_mem i)
      have hscaleVector :=
        eq_last_smul_homogeneousLift_projectiveDualChartPoint
          (chartVector (residualLabel i)) hi2
      have hinc' : homogeneousLift
          (projectiveDualChartPoint (chartVector (residualLabel i))) ⬝ᵥ ell = 0 := by
        simpa only [affineCfg, chartPoint] using hinc
      have htransInc : chartVector (residualLabel i) ⬝ᵥ ell = 0 := by
        rw [hscaleVector, smul_dotProduct, hinc', smul_zero]
      have hpair := projectiveCovectorTransform_dot_pointTransform G
        (A.projectiveLine (residualLabel i)).rep qvec
      rw [← hchartVector (residualLabel i)] at hpair
      change chartVector (residualLabel i) ⬝ᵥ (G • qvec) =
        (A.projectiveLine (residualLabel i)).rep ⬝ᵥ qvec at hpair
      have hGq : G • qvec = ell := by simp [qvec]
      rw [hGq, htransInc] at hpair
      change q ∈ A.projectiveLine a
      change Projectivization.orthogonal q (A.projectiveLine a)
      rw [show q = Projectivization.mk ℝ qvec hqvec by rfl,
        ← Projectivization.mk_rep (A.projectiveLine a)]
      apply (Projectivization.orthogonal_mk hqvec
        (A.projectiveLine a).rep_nonzero).2
      rw [← hilabel, dotProduct_comm]
      exact hpair.symm
    exact hnoSixConcurrent q hall

  let starDirection : Option (AwayFrom p) → Submodule ℝ Point2 := fun s =>
    ℝ ∙ pointOfCoords (chartVector s 0) (chartVector s 1)

  have hpairDirection : ∀ {i j : Fin 6}, i ≠ j →
      ∃ s ∈ S,
        directionOfPoints (affineCfg i) (affineCfg j) = starDirection s := by
    intro i j hij
    have hab : residualLabel i ≠ residualLabel j := by
      intro hab
      apply hij
      exact base.injective (Subtype.ext hab)
    obtain ⟨s, hs, hqs⟩ := hcovered
      (by simpa only [R] using hresidualLabel_mem i)
      (by simpa only [R] using hresidualLabel_mem j) hab
    refine ⟨s, hs, ?_⟩
    let Pa := A.projectiveLine (residualLabel i)
    let Pb := A.projectiveLine (residualLabel j)
    let Ps := A.projectiveLine s
    let q := A.intersection (residualLabel i) (residualLabel j)
    have hqa : Projectivization.orthogonal Pa q := by
      rw [Projectivization.orthogonal_comm]
      change A.Incident q (residualLabel i)
      exact A.intersection_incident_left hab
    have hqb : Projectivization.orthogonal Pb q := by
      rw [Projectivization.orthogonal_comm]
      change A.Incident q (residualLabel j)
      exact A.intersection_incident_right hab
    have hqs' : Projectivization.orthogonal Ps q := by
      rw [Projectivization.orthogonal_comm]
      change A.Incident q s
      exact hqs
    have hdet : Matrix.det ![Pa.rep, Pb.rep, Ps.rep] = 0 :=
      det_rep_eq_zero_of_three_projective_orthogonal
        Pa Pb Ps q hqa hqb hqs'
    have hdetChart : Matrix.det
        ![chartVector (residualLabel i), chartVector (residualLabel j),
          chartVector s] = 0 := by
      simpa only [chartVector, Pa, Pb, Ps] using
        (det_eq_zero_iff_generalLinear_smul_three H
          Pa.rep Pb.rep Ps.rep).2 hdet
    have hi2 := hresidualFinite (residualLabel i) (hresidualLabel_mem i)
    have hj2 := hresidualFinite (residualLabel j) (hresidualLabel_mem j)
    have hs2 : chartVector s 2 = 0 :=
      (hlast_iff s).2 (hstarIncident s hs)
    change directionOfPoints
        (projectiveDualChartPoint (chartVector (residualLabel i)))
        (projectiveDualChartPoint (chartVector (residualLabel j))) =
      ℝ ∙ pointOfCoords (chartVector s 0) (chartVector s 1)
    have hijChart :
        projectiveDualChartPoint (chartVector (residualLabel i)) ≠
          projectiveDualChartPoint (chartVector (residualLabel j)) := by
      simpa only [affineCfg, chartPoint] using affineCfg.injective.ne hij
    exact directionOfPoints_projectiveDualChartPoint_eq
      _ _ _ hi2 hj2 hijChart hs2
      (hchartVector_ne s) hdetChart

  have hdirectionsSubset :
      determinedDirections affineCfg ⊆ S.image starDirection := by
    intro D hD
    unfold determinedDirections at hD
    obtain ⟨K, _hK, rfl⟩ := Finset.mem_image.mp hD
    obtain ⟨i, j, hij, hKij⟩ := Finset.card_eq_two.mp K.2
    have hKeq : K = ⟨{i, j}, by simp [hij]⟩ := Subtype.ext hKij
    obtain ⟨s, hs, hdir⟩ := hpairDirection hij
    apply Finset.mem_image.mpr
    refine ⟨s, hs, ?_⟩
    rw [hKeq, directionOfPair_eq_directionOfPoints affineCfg hij]
    exact hdir.symm

  refine ⟨affineCfg, hnoncollinear, ?_⟩
  calc
    (determinedDirections affineCfg).card ≤ (S.image starDirection).card :=
      Finset.card_le_card hdirectionsSubset
    _ ≤ S.card := Finset.card_image_le
    _ ≤ 5 := hstarCard

/-- The real-plane direction principle, with the projective-chart bridge
discharged internally. -/
noncomputable def realPlaneTwelveDirectionPrinciple
    (Mel : RealPlaneMelchiorPrinciple.{u})
    (EvenArr : RealPlaneEvenArrangementPrinciple.{u})
    (Kelly : RealPlaneKellyMoserPrinciple.{u})
    (Gram : RealPlaneTwelveGramPrinciple.{u}) :
    RealPlaneTwelveDirectionPrinciple.{u} :=
  realPlaneTwelveDirectionPrinciple_of_projectiveChartBridge
    Mel EvenArr Kelly Gram
      (fun cfg p c hp =>
        projectiveChartBridge_of_six_dual_lines_covered_by_five_pencil_lines
          cfg p c hp)

end

end Erdos506.V1
