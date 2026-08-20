import Erdos506.Incidence.ProjectiveFiveFrame
import Erdos506.Incidence.GoldenAxisDeterminants
import Erdos506.Incidence.RadicalAxisFourFourGeometry

/-!
# Projective golden-axis obstruction

This file is the coordinate-free seam around the bounded determinant
certificate in `GoldenAxisDeterminants`.  Its input consists of five
homogeneous points in general position, four nonzero chord-pair centres on
one projective axis, and one of the two possible three-line pencils.  A
projective five-frame transports the data to the normal form used by the
certificate.
-/

namespace Erdos506.Incidence

open Matrix
open scoped LinearAlgebra.Projectivization

/-- Each of the four marked centres lies on both chords in its row of the
fixed near-one-factorization. -/
def GoldenAxisCenterIncidence
    (g : Fin 5 → Homogeneous3) (q : Fin 4 → Homogeneous3) : Prop :=
  ∀ i j,
    Matrix.det ![
      g (goldenCenterChordEndpoint i j 0),
      g (goldenCenterChordEndpoint i j 1),
      q i] = 0

/-- The four marked centres lie on one projective line.  The universal
determinant formulation is independent of all choices of representatives. -/
def GoldenAxisCollinear (q : Fin 4 → Homogeneous3) : Prop :=
  ∀ i j k, Matrix.det ![q i, q j, q k] = 0

/-- The end-edge representative of the concurrent three-line matching. -/
def GoldenAxisEndConcurrent
    (g : Fin 5 → Homogeneous3) (q : Fin 4 → Homogeneous3) : Prop :=
  ∃ r : Homogeneous3, r ≠ 0 ∧
    Matrix.det ![q 0, g 1, r] = 0 ∧
    Matrix.det ![q 2, g 3, r] = 0 ∧
    Matrix.det ![q 1, g 2, r] = 0

/-- The middle-edge representative of the concurrent three-line matching. -/
def GoldenAxisMiddleConcurrent
    (g : Fin 5 → Homogeneous3) (q : Fin 4 → Homogeneous3) : Prop :=
  ∃ r : Homogeneous3, r ≠ 0 ∧
    Matrix.det ![q 0, g 1, r] = 0 ∧
    Matrix.det ![q 2, g 3, r] = 0 ∧
    Matrix.det ![g 2, g 4, r] = 0

/-- Neutral projective input common to the two concurrency orbits. -/
structure GoldenAxisProjectiveCore where
  g : Fin 5 → Homogeneous3
  q : Fin 4 → Homogeneous3
  g_generalPosition : HomogeneousFiveGeneralPosition g
  q_ne_zero : ∀ i, q i ≠ 0
  centerIncidence : GoldenAxisCenterIncidence g q
  axisCollinear : GoldenAxisCollinear q

/-- A golden-axis core together with either representative concurrent
matching. -/
structure GoldenAxisProjectiveInput extends GoldenAxisProjectiveCore where
  concurrency :
    GoldenAxisEndConcurrent g q ∨ GoldenAxisMiddleConcurrent g q

private theorem generalLinear_smul_ne_zero
    (G : GL (Fin 3) ℝ) {v : Homogeneous3} (hv : v ≠ 0) :
    G • v ≠ 0 := by
  intro hzero
  apply hv
  have hinv := congrArg (fun w : Homogeneous3 => G⁻¹ • w) hzero
  simpa using hinv

private theorem det_smul_three_rows
    (a b c : ℝ) (u v w : Homogeneous3) :
    Matrix.det ![a • u, b • v, c • w] =
      (a * b * c) * Matrix.det ![u, v, w] := by
  simp [Matrix.det_fin_three]
  ring

/-- The normal points furnished by a projective five-frame remain in
general position. -/
private theorem projectiveFiveFrame_normal_generalPosition
    {g : Fin 5 → Homogeneous3}
    (hgp : HomogeneousFiveGeneralPosition g)
    (F : ProjectiveFiveFrame g) :
    HomogeneousFiveGeneralPosition
      (projectiveFiveNormalPoint F.a F.b) := by
  refine ⟨?_, ?_⟩
  · intro i
    have hmapped : F.G • g i ≠ 0 :=
      generalLinear_smul_ne_zero F.G (hgp.1 i)
    intro hnormal
    apply hmapped
    rw [F.map_point i, hnormal, smul_zero]
  · intro i j k hij hik hjk
    have hdet : Matrix.det ![F.G • g i, F.G • g j, F.G • g k] ≠ 0 := by
      intro hzero
      exact hgp.2 i j k hij hik hjk
        ((det_eq_zero_iff_generalLinear_smul_three
          F.G (g i) (g j) (g k)).mp hzero)
    intro hnormal
    apply hdet
    calc
      Matrix.det ![F.G • g i, F.G • g j, F.G • g k] =
          Matrix.det ![
            F.scale i • projectiveFiveNormalPoint F.a F.b i,
            F.scale j • projectiveFiveNormalPoint F.a F.b j,
            F.scale k • projectiveFiveNormalPoint F.a F.b k] := by
        rw [F.map_point i, F.map_point j, F.map_point k]
      _ = (F.scale i * F.scale j * F.scale k) *
          Matrix.det ![
            projectiveFiveNormalPoint F.a F.b i,
            projectiveFiveNormalPoint F.a F.b j,
            projectiveFiveNormalPoint F.a F.b k] :=
        det_smul_three_rows _ _ _ _ _ _
      _ = 0 := by rw [hnormal, mul_zero]

private theorem crossProduct_ne_zero_of_det_ne_zero
    {x y z : Homogeneous3}
    (hdet : Matrix.det ![x, y, z] ≠ 0) :
    crossProduct x y ≠ 0 := by
  intro hcross
  apply hdet
  calc
    Matrix.det ![x, y, z] = z ⬝ᵥ crossProduct x y := by
      symm
      calc
        z ⬝ᵥ crossProduct x y = x ⬝ᵥ crossProduct y z :=
          triple_product_permutation _ _ _
        _ = Matrix.det ![x, y, z] := triple_product_eq_det _ _ _
    _ = 0 := by rw [hcross]; simp

private theorem cross_crossProduct_ne_zero_of_det_ne_zero
    {x0 y0 x1 y1 : Homogeneous3}
    (hfirst : Matrix.det ![x0, y0, x1] ≠ 0)
    (hsecond : Matrix.det ![x1, y1, x0] ≠ 0) :
    crossProduct (crossProduct x0 y0) (crossProduct x1 y1) ≠ 0 := by
  have hline0 : crossProduct x0 y0 ≠ 0 :=
    crossProduct_ne_zero_of_det_ne_zero hfirst
  have hline1 : crossProduct x1 y1 ≠ 0 :=
    crossProduct_ne_zero_of_det_ne_zero hsecond
  intro hcross
  have hprojective :
      Projectivization.mk ℝ (crossProduct x0 y0) hline0 =
        Projectivization.mk ℝ (crossProduct x1 y1) hline1 :=
    (Projectivization.mk_eq_mk_iff_crossProduct_eq_zero
      hline0 hline1).2 hcross
  obtain ⟨s, hs⟩ :=
    (Projectivization.mk_eq_mk_iff' ℝ
      (crossProduct x0 y0) (crossProduct x1 y1)
      hline0 hline1).1 hprojective
  apply hfirst
  calc
    Matrix.det ![x0, y0, x1] = x1 ⬝ᵥ crossProduct x0 y0 := by
      symm
      calc
        x1 ⬝ᵥ crossProduct x0 y0 = x0 ⬝ᵥ crossProduct y0 x1 :=
          triple_product_permutation _ _ _
        _ = Matrix.det ![x0, y0, x1] := triple_product_eq_det _ _ _
    _ = x1 ⬝ᵥ (s • crossProduct x1 y1) := by rw [hs]
    _ = 0 := by simp

private theorem golden_firstChord_det_ne_zero
    {a b : ℝ}
    (hgp : HomogeneousFiveGeneralPosition
      (projectiveFiveNormalPoint a b)) (i : Fin 4) :
    Matrix.det ![
      projectiveFiveNormalPoint a b (goldenCenterChordEndpoint i 0 0),
      projectiveFiveNormalPoint a b (goldenCenterChordEndpoint i 0 1),
      projectiveFiveNormalPoint a b (goldenCenterChordEndpoint i 1 0)] ≠ 0 := by
  fin_cases i <;> apply hgp.2 <;> decide

private theorem golden_secondChord_det_ne_zero
    {a b : ℝ}
    (hgp : HomogeneousFiveGeneralPosition
      (projectiveFiveNormalPoint a b)) (i : Fin 4) :
    Matrix.det ![
      projectiveFiveNormalPoint a b (goldenCenterChordEndpoint i 1 0),
      projectiveFiveNormalPoint a b (goldenCenterChordEndpoint i 1 1),
      projectiveFiveNormalPoint a b (goldenCenterChordEndpoint i 0 0)] ≠ 0 := by
  fin_cases i <;> apply hgp.2 <;> decide

private theorem goldenCenterFromChords_ne_zero_of_generalPosition
    {a b : ℝ}
    (hgp : HomogeneousFiveGeneralPosition
      (projectiveFiveNormalPoint a b)) (i : Fin 4) :
    goldenCenterFromChords a b i ≠ 0 := by
  unfold goldenCenterFromChords
  exact cross_crossProduct_ne_zero_of_det_ne_zero
    (golden_firstChord_det_ne_zero hgp i)
    (golden_secondChord_det_ne_zero hgp i)

/-- Incidence survives the frame transformation and removal of the two
nonzero point scalars. -/
private theorem golden_normalized_center_incidence
    (core : GoldenAxisProjectiveCore)
    (F : ProjectiveFiveFrame core.g) (i : Fin 4) (j : Fin 2) :
    Matrix.det ![
      projectiveFiveNormalPoint F.a F.b
        (goldenCenterChordEndpoint i j 0),
      projectiveFiveNormalPoint F.a F.b
        (goldenCenterChordEndpoint i j 1),
      F.G • core.q i] = 0 := by
  have htransport : Matrix.det ![
      F.G • core.g (goldenCenterChordEndpoint i j 0),
      F.G • core.g (goldenCenterChordEndpoint i j 1),
      F.G • core.q i] = 0 :=
    (det_eq_zero_iff_generalLinear_smul_three F.G _ _ _).2
      (core.centerIncidence i j)
  rw [F.map_point (goldenCenterChordEndpoint i j 0),
    F.map_point (goldenCenterChordEndpoint i j 1)] at htransport
  have hfactored :
      (F.scale (goldenCenterChordEndpoint i j 0) *
          F.scale (goldenCenterChordEndpoint i j 1) * 1) *
        Matrix.det ![
          projectiveFiveNormalPoint F.a F.b
            (goldenCenterChordEndpoint i j 0),
          projectiveFiveNormalPoint F.a F.b
            (goldenCenterChordEndpoint i j 1),
          F.G • core.q i] = 0 := by
    rw [← det_smul_three_rows
      (F.scale (goldenCenterChordEndpoint i j 0))
      (F.scale (goldenCenterChordEndpoint i j 1)) 1]
    simpa using htransport
  exact (mul_eq_zero.mp hfactored).resolve_left
    (mul_ne_zero
      (mul_ne_zero
        (F.scale_ne_zero (goldenCenterChordEndpoint i j 0))
        (F.scale_ne_zero (goldenCenterChordEndpoint i j 1)))
      one_ne_zero)

/-- A transformed marked centre is the canonical double-cross centre, up
to its unavoidable nonzero homogeneous scalar. -/
private theorem transformed_center_projective_eq_canonical
    (core : GoldenAxisProjectiveCore)
    (F : ProjectiveFiveFrame core.g)
    (hnormal : HomogeneousFiveGeneralPosition
      (projectiveFiveNormalPoint F.a F.b))
    (i : Fin 4)
    (hq : F.G • core.q i ≠ 0)
    (hcanonical : goldenCanonicalCenter F.a F.b i ≠ 0) :
    Projectivization.mk ℝ (F.G • core.q i) hq =
      Projectivization.mk ℝ
        (goldenCanonicalCenter F.a F.b i) hcanonical := by
  let x0 := projectiveFiveNormalPoint F.a F.b
    (goldenCenterChordEndpoint i 0 0)
  let y0 := projectiveFiveNormalPoint F.a F.b
    (goldenCenterChordEndpoint i 0 1)
  let x1 := projectiveFiveNormalPoint F.a F.b
    (goldenCenterChordEndpoint i 1 0)
  let y1 := projectiveFiveNormalPoint F.a F.b
    (goldenCenterChordEndpoint i 1 1)
  have hdet0 : Matrix.det ![x0, y0, x1] ≠ 0 := by
    simpa only [x0, y0, x1] using golden_firstChord_det_ne_zero hnormal i
  have hdet1 : Matrix.det ![x1, y1, x0] ≠ 0 := by
    simpa only [x0, y1, x1] using golden_secondChord_det_ne_zero hnormal i
  have hline0 : crossProduct x0 y0 ≠ 0 :=
    crossProduct_ne_zero_of_det_ne_zero hdet0
  have hline1 : crossProduct x1 y1 ≠ 0 :=
    crossProduct_ne_zero_of_det_ne_zero hdet1
  have hcenter : crossProduct (crossProduct x0 y0)
      (crossProduct x1 y1) ≠ 0 :=
    cross_crossProduct_ne_zero_of_det_ne_zero hdet0 hdet1
  have hlines :
      Projectivization.mk ℝ (crossProduct x0 y0) hline0 ≠
        Projectivization.mk ℝ (crossProduct x1 y1) hline1 := by
    intro heq
    apply hcenter
    exact (Projectivization.mk_eq_mk_iff_crossProduct_eq_zero
      hline0 hline1).1 heq
  have hinc0 := golden_normalized_center_incidence core F i 0
  have hinc1 := golden_normalized_center_incidence core F i 1
  have horth0 : Projectivization.orthogonal
      (Projectivization.mk ℝ (crossProduct x0 y0) hline0)
      (Projectivization.mk ℝ (F.G • core.q i) hq) := by
    apply (Projectivization.orthogonal_mk hline0 hq).2
    calc
      crossProduct x0 y0 ⬝ᵥ (F.G • core.q i) =
          (F.G • core.q i) ⬝ᵥ crossProduct x0 y0 :=
        dotProduct_comm _ _
      _ = x0 ⬝ᵥ crossProduct y0 (F.G • core.q i) :=
        triple_product_permutation _ _ _
      _ = Matrix.det ![x0, y0, F.G • core.q i] :=
        triple_product_eq_det _ _ _
      _ = 0 := by simpa only [x0, y0] using hinc0
  have horth1 : Projectivization.orthogonal
      (Projectivization.mk ℝ (crossProduct x1 y1) hline1)
      (Projectivization.mk ℝ (F.G • core.q i) hq) := by
    apply (Projectivization.orthogonal_mk hline1 hq).2
    calc
      crossProduct x1 y1 ⬝ᵥ (F.G • core.q i) =
          (F.G • core.q i) ⬝ᵥ crossProduct x1 y1 :=
        dotProduct_comm _ _
      _ = x1 ⬝ᵥ crossProduct y1 (F.G • core.q i) :=
        triple_product_permutation _ _ _
      _ = Matrix.det ![x1, y1, F.G • core.q i] :=
        triple_product_eq_det _ _ _
      _ = 0 := by simpa only [x1, y1] using hinc1
  have hqCross :
      Projectivization.mk ℝ (F.G • core.q i) hq =
        Projectivization.cross
          (Projectivization.mk ℝ (crossProduct x0 y0) hline0)
          (Projectivization.mk ℝ (crossProduct x1 y1) hline1) :=
    projectiveCovector_eq_cross_of_orthogonal hlines horth0 horth1
  rw [Projectivization.cross_mk_of_ne hline0 hline1 hlines] at hqCross
  calc
    Projectivization.mk ℝ (F.G • core.q i) hq =
        Projectivization.mk ℝ (goldenCenterFromChords F.a F.b i)
          (goldenCenterFromChords_ne_zero_of_generalPosition hnormal i) := by
      simpa only [goldenCenterFromChords, x0, y0, x1, y1] using hqCross
    _ = Projectivization.mk ℝ
        (goldenCanonicalCenter F.a F.b i) hcanonical := by
      simp only [goldenCenterFromChords_eq_canonical]

private theorem frame_mapped_point_projective_eq_normal
    {g : Fin 5 → Homogeneous3} (F : ProjectiveFiveFrame g) (i : Fin 5)
    (hmapped : F.G • g i ≠ 0)
    (hnormal : projectiveFiveNormalPoint F.a F.b i ≠ 0) :
    Projectivization.mk ℝ (F.G • g i) hmapped =
      Projectivization.mk ℝ
        (projectiveFiveNormalPoint F.a F.b i) hnormal := by
  apply (Projectivization.mk_eq_mk_iff' ℝ _ _ hmapped hnormal).2
  exact ⟨F.scale i, (F.map_point i).symm⟩

/-- Transport any collinearity determinant of marked centres to their
canonical representatives. -/
private theorem canonical_center_det_eq_zero_of_axisCollinear
    (core : GoldenAxisProjectiveCore)
    (F : ProjectiveFiveFrame core.g)
    (hnormal : HomogeneousFiveGeneralPosition
      (projectiveFiveNormalPoint F.a F.b))
    (i j k : Fin 4) :
    Matrix.det ![
      goldenCanonicalCenter F.a F.b i,
      goldenCanonicalCenter F.a F.b j,
      goldenCanonicalCenter F.a F.b k] = 0 := by
  have hqi : F.G • core.q i ≠ 0 :=
    generalLinear_smul_ne_zero F.G (core.q_ne_zero i)
  have hqj : F.G • core.q j ≠ 0 :=
    generalLinear_smul_ne_zero F.G (core.q_ne_zero j)
  have hqk : F.G • core.q k ≠ 0 :=
    generalLinear_smul_ne_zero F.G (core.q_ne_zero k)
  have hci : goldenCanonicalCenter F.a F.b i ≠ 0 := by
    rw [← goldenCenterFromChords_eq_canonical]
    exact goldenCenterFromChords_ne_zero_of_generalPosition hnormal i
  have hcj : goldenCanonicalCenter F.a F.b j ≠ 0 := by
    rw [← goldenCenterFromChords_eq_canonical]
    exact goldenCenterFromChords_ne_zero_of_generalPosition hnormal j
  have hck : goldenCanonicalCenter F.a F.b k ≠ 0 := by
    rw [← goldenCenterFromChords_eq_canonical]
    exact goldenCenterFromChords_ne_zero_of_generalPosition hnormal k
  have hpi := transformed_center_projective_eq_canonical
    core F hnormal i hqi hci
  have hpj := transformed_center_projective_eq_canonical
    core F hnormal j hqj hcj
  have hpk := transformed_center_projective_eq_canonical
    core F hnormal k hqk hck
  have htransport : Matrix.det ![
      F.G • core.q i, F.G • core.q j, F.G • core.q k] = 0 :=
    (det_eq_zero_iff_generalLinear_smul_three F.G _ _ _).2
      (core.axisCollinear i j k)
  exact (det_eq_zero_iff_of_projective_mk_eq
    hqi hqj hqk hci hcj hck hpi hpj hpk).1 htransport

/-- Transport an incidence of a marked centre and a base point to canonical
normal-form representatives. -/
private theorem canonical_normal_incidence_of_frame
    (core : GoldenAxisProjectiveCore)
    (F : ProjectiveFiveFrame core.g)
    (hnormal : HomogeneousFiveGeneralPosition
      (projectiveFiveNormalPoint F.a F.b))
    (i : Fin 4) (j : Fin 5) {r : Homogeneous3} (hr : r ≠ 0)
    (hinc : Matrix.det ![core.q i, core.g j, r] = 0) :
    Matrix.det ![
      goldenCanonicalCenter F.a F.b i,
      projectiveFiveNormalPoint F.a F.b j,
      F.G • r] = 0 := by
  have hq : F.G • core.q i ≠ 0 :=
    generalLinear_smul_ne_zero F.G (core.q_ne_zero i)
  have hc : goldenCanonicalCenter F.a F.b i ≠ 0 := by
    rw [← goldenCenterFromChords_eq_canonical]
    exact goldenCenterFromChords_ne_zero_of_generalPosition hnormal i
  have hg : F.G • core.g j ≠ 0 :=
    generalLinear_smul_ne_zero F.G (core.g_generalPosition.1 j)
  have hn : projectiveFiveNormalPoint F.a F.b j ≠ 0 := hnormal.1 j
  have hr' : F.G • r ≠ 0 := generalLinear_smul_ne_zero F.G hr
  have hqProjective := transformed_center_projective_eq_canonical
    core F hnormal i hq hc
  have hgProjective := frame_mapped_point_projective_eq_normal
    F j hg hn
  have htransport : Matrix.det ![
      F.G • core.q i, F.G • core.g j, F.G • r] = 0 :=
    (det_eq_zero_iff_generalLinear_smul_three F.G _ _ _).2 hinc
  exact (det_eq_zero_iff_of_projective_mk_eq
    hq hg hr' hc hn hr' hqProjective hgProjective rfl).1 htransport

/-- Transport an incidence of two base points to normal-form
representatives. -/
private theorem normal_normal_incidence_of_frame
    (core : GoldenAxisProjectiveCore)
    (F : ProjectiveFiveFrame core.g)
    (hnormal : HomogeneousFiveGeneralPosition
      (projectiveFiveNormalPoint F.a F.b))
    (i j : Fin 5) {r : Homogeneous3} (hr : r ≠ 0)
    (hinc : Matrix.det ![core.g i, core.g j, r] = 0) :
    Matrix.det ![
      projectiveFiveNormalPoint F.a F.b i,
      projectiveFiveNormalPoint F.a F.b j,
      F.G • r] = 0 := by
  have hgi : F.G • core.g i ≠ 0 :=
    generalLinear_smul_ne_zero F.G (core.g_generalPosition.1 i)
  have hgj : F.G • core.g j ≠ 0 :=
    generalLinear_smul_ne_zero F.G (core.g_generalPosition.1 j)
  have hni : projectiveFiveNormalPoint F.a F.b i ≠ 0 := hnormal.1 i
  have hnj : projectiveFiveNormalPoint F.a F.b j ≠ 0 := hnormal.1 j
  have hr' : F.G • r ≠ 0 := generalLinear_smul_ne_zero F.G hr
  have hpi := frame_mapped_point_projective_eq_normal F i hgi hni
  have hpj := frame_mapped_point_projective_eq_normal F j hgj hnj
  have htransport : Matrix.det ![
      F.G • core.g i, F.G • core.g j, F.G • r] = 0 :=
    (det_eq_zero_iff_generalLinear_smul_three F.G _ _ _).2 hinc
  exact (det_eq_zero_iff_of_projective_mk_eq
    hgi hgj hr' hni hnj hr' hpi hpj rfl).1 htransport

/-- The neutral projective golden-axis input has no realization over the
reals. -/
theorem GoldenAxisProjectiveInput.not_realizable
    (input : GoldenAxisProjectiveInput) : False := by
  let F : ProjectiveFiveFrame input.g :=
    projectiveFiveFrame input.g input.g_generalPosition
  have hnormal : HomogeneousFiveGeneralPosition
      (projectiveFiveNormalPoint F.a F.b) :=
    projectiveFiveFrame_normal_generalPosition input.g_generalPosition F
  have hq123 : Matrix.det ![
      goldenCanonicalCenter F.a F.b 1,
      goldenCanonicalCenter F.a F.b 2,
      goldenCanonicalCenter F.a F.b 3] = 0 :=
    canonical_center_det_eq_zero_of_axisCollinear
      input.toGoldenAxisProjectiveCore F hnormal 1 2 3
  have hq023 : Matrix.det ![
      goldenCanonicalCenter F.a F.b 0,
      goldenCanonicalCenter F.a F.b 2,
      goldenCanonicalCenter F.a F.b 3] = 0 :=
    canonical_center_det_eq_zero_of_axisCollinear
      input.toGoldenAxisProjectiveCore F hnormal 0 2 3
  have hconcurrency :
      Matrix.det (goldenEndConcurrencyLines F.a F.b) = 0 ∨
        Matrix.det (goldenMiddleConcurrencyLines F.a F.b) = 0 := by
    rcases input.concurrency with hend | hmiddle
    · rcases hend with ⟨r, hr, h0, h1, h2⟩
      have hr' : F.G • r ≠ 0 := generalLinear_smul_ne_zero F.G hr
      have h0' := canonical_normal_incidence_of_frame
        input.toGoldenAxisProjectiveCore F hnormal 0 1 hr h0
      have h1' := canonical_normal_incidence_of_frame
        input.toGoldenAxisProjectiveCore F hnormal 2 3 hr h1
      have h2' := canonical_normal_incidence_of_frame
        input.toGoldenAxisProjectiveCore F hnormal 1 2 hr h2
      left
      simpa only [goldenEndConcurrencyLines] using
        (det_lineCovectors_eq_zero_of_common_point hr' h0' h1' h2')
    · rcases hmiddle with ⟨r, hr, h0, h1, h2⟩
      have hr' : F.G • r ≠ 0 := generalLinear_smul_ne_zero F.G hr
      have h0' := canonical_normal_incidence_of_frame
        input.toGoldenAxisProjectiveCore F hnormal 0 1 hr h0
      have h1' := canonical_normal_incidence_of_frame
        input.toGoldenAxisProjectiveCore F hnormal 2 3 hr h1
      have h2' := normal_normal_incidence_of_frame
        input.toGoldenAxisProjectiveCore F hnormal 2 4 hr h2
      right
      simpa only [goldenMiddleConcurrencyLines] using
        (det_lineCovectors_eq_zero_of_common_point hr' h0' h1' h2')
  exact goldenAxisDeterminants_not_realizable
    F.a F.b hq123 hq023 hconcurrency

end Erdos506.Incidence
