import Erdos506.V1.TwelveGridTransversalExtraction
import Erdos506.Incidence.ParameterizedThreeByThreeGridObstruction
import Erdos506.Incidence.ProjectiveCovectorFrame
import Erdos506.Incidence.ProjectiveThreeLineConcurrency
import Mathlib.Tactic

/-!
# The actual projective-frame entrance for the twelve-grid obstruction

The six-four reconstruction and `TwelveGridTransversalExtraction` retain the
actual affine labels and actual determined lines.  This file begins the last
geometric step without adding a coordinate-normalization field: four of the
actual pencil lines are converted to homogeneous covectors and shown to form
a complete quadrangle.  Its canonical `GL₃` frame is therefore available
constructively.

The subsequent sections will use the two extracted transversals to determine
the two remaining affine cross-ratios, and then transfer the concurrent
ordinary secants to the checked normalized-grid calculation.
-/

namespace Erdos506.V1

open Erdos506.Block
open Erdos506.Block.BlockSystem
open Erdos506.Finite
open Erdos506.Incidence
open Erdos506.V3
open Erdos506.V4
open Matrix
open scoped LinearAlgebra.Projectivization

universe u

/-! ## Raw covectors of the actual pencil lines -/

/-- A fixed nonzero homogeneous representative of an actual reconstructed
pencil line.  It is obtained from the canonical projective realization of
the determined affine line, not chosen as new data. -/
noncomputable def twelveGridActualPencilCovector
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (hcard : Fintype.card Point = 12)
    (H : TwelveGridInvertedLineCensus cfg p)
    (a : Fin 2) (r : Fin 3) : Homogeneous3 :=
  (twelveGridActualProjectivePencilLine hcard H a r).rep

theorem twelveGridActualPencilCovector_ne_zero
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (hcard : Fintype.card Point = 12)
    (H : TwelveGridInvertedLineCensus cfg p)
    (a : Fin 2) (r : Fin 3) :
    twelveGridActualPencilCovector hcard H a r ≠ 0 := by
  simpa [twelveGridActualPencilCovector] using
    (twelveGridActualProjectivePencilLine hcard H a r).rep_nonzero

@[simp] theorem twelveGridActualPencilCovector_projectivize
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (hcard : Fintype.card Point = 12)
    (H : TwelveGridInvertedLineCensus cfg p)
    (a : Fin 2) (r : Fin 3) :
    Projectivization.mk ℝ (twelveGridActualPencilCovector hcard H a r)
      (twelveGridActualPencilCovector_ne_zero hcard H a r) =
      twelveGridActualProjectivePencilLine hcard H a r := by
  simpa [twelveGridActualPencilCovector] using
    (Projectivization.mk_rep
      (twelveGridActualProjectivePencilLine hcard H a r))

/-- Raw homogeneous incidence with a reconstructed pencil covector is
exactly the original determined-line support incidence. -/
theorem twelveGridActualPencilCovector_incident_iff
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (hcard : Fintype.card Point = 12)
    (H : TwelveGridInvertedLineCensus cfg p)
    (a : Fin 2) (r : Fin 3) (q : AwayFrom p) :
    twelveGridActualPencilCovector hcard H a r ⬝ᵥ
        homogeneousLift (pivotInversion cfg p q) = 0 ↔
      q ∈ lineSupport (pivotInversion cfg p)
        (twelveGridActualPencilLine hcard H a r).1 := by
  have hmem := twelveGridActualProjectivePoint_mem_pencilLine_iff
    hcard H a r q
  calc
    twelveGridActualPencilCovector hcard H a r ⬝ᵥ
        homogeneousLift (pivotInversion cfg p q) = 0 ↔
      homogeneousLift (pivotInversion cfg p q) ⬝ᵥ
          twelveGridActualPencilCovector hcard H a r = 0 := by
        constructor
        · intro h
          calc
            homogeneousLift (pivotInversion cfg p q) ⬝ᵥ
                twelveGridActualPencilCovector hcard H a r =
                twelveGridActualPencilCovector hcard H a r ⬝ᵥ
                  homogeneousLift (pivotInversion cfg p q) :=
              dotProduct_comm _ _
            _ = 0 := h
        · intro h
          calc
            twelveGridActualPencilCovector hcard H a r ⬝ᵥ
                homogeneousLift (pivotInversion cfg p q) =
                homogeneousLift (pivotInversion cfg p q) ⬝ᵥ
                  twelveGridActualPencilCovector hcard H a r :=
              dotProduct_comm _ _
            _ = 0 := h
    _ ↔ projectivePoint (pivotInversion cfg p q) ∈
        Projectivization.mk ℝ
          (twelveGridActualPencilCovector hcard H a r)
          (twelveGridActualPencilCovector_ne_zero hcard H a r) := by
      change _ ↔ Projectivization.orthogonal
        (Projectivization.mk ℝ (homogeneousLift (pivotInversion cfg p q))
          (homogeneousLift_ne_zero _))
        (Projectivization.mk ℝ
          (twelveGridActualPencilCovector hcard H a r)
          (twelveGridActualPencilCovector_ne_zero hcard H a r))
      rw [Projectivization.orthogonal_mk]
    _ ↔ projectivePoint (pivotInversion cfg p q) ∈
        twelveGridActualProjectivePencilLine hcard H a r := by
      rw [twelveGridActualPencilCovector_projectivize]
    _ ↔ q ∈ lineSupport (pivotInversion cfg p)
        (twelveGridActualPencilLine hcard H a r).1 := by
      simpa only [twelveGridActualProjectivePoint,
        affinePointToProjective_eq_projectivePoint] using hmem

/-- Different numbered members of one reconstructed pencil give different
projective lines. -/
theorem twelveGridActualProjectivePencilLine_same_ne
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (hcard : Fintype.card Point = 12)
    (H : TwelveGridInvertedLineCensus cfg p)
    (a : Fin 2) {r s : Fin 3} (hrs : r ≠ s) :
    twelveGridActualProjectivePencilLine hcard H a r ≠
      twelveGridActualProjectivePencilLine hcard H a s := by
  intro hline
  apply hrs
  apply twelveGridActualPencilIndex_injective hcard H a
  apply H.fourLine.injective
  apply Subtype.ext
  apply determinedProjectiveLine_injective (pivotInversion cfg p)
  simpa [twelveGridActualProjectivePencilLine,
    twelveGridActualPencilLine] using hline

/-! ## Incidence exclusions forced by the saturated six-four grid -/

/-- The first pencil centre does not lie on a column line. -/
theorem twelveGridActualExternalPoint_zero_not_mem_column
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (hcard : Fintype.card Point = 12)
    (H : TwelveGridInvertedLineCensus cfg p) (s : Fin 3) :
    twelveGridActualExternalPoint hcard H 0 ∉
      lineSupport (pivotInversion cfg p)
        (twelveGridActualPencilLine hcard H 1 s).1 := by
  intro hmem
  have hzero : twelveGridActualPencilIndex hcard H 1 s ∈
      sixFourBasesThrough (twelveGridActualFourSupport H)
        (twelveGridActualExternalPoint hcard H 0) := by
    apply mem_sixFourBasesThrough.mpr
    simpa [twelveGridActualFourSupport,
      twelveGridActualPencilLine] using hmem
  have hone : twelveGridActualPencilIndex hcard H 1 s ∈
      sixFourBasesThrough (twelveGridActualFourSupport H)
        (twelveGridActualExternalPoint hcard H 1) := by
    apply mem_sixFourBasesThrough.mpr
    simpa [twelveGridActualFourSupport,
      twelveGridActualPencilLine] using
      (twelveGridActualExternalPoint_mem_pencilLine hcard H 1 s)
  exact (Finset.disjoint_left.mp
    (sixFourExternalBases_disjoint
      (twelveGridActualFourSupport_isSaturatedSixFour hcard H))) hzero hone

/-- The second pencil centre does not lie on a row line. -/
theorem twelveGridActualExternalPoint_one_not_mem_row
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (hcard : Fintype.card Point = 12)
    (H : TwelveGridInvertedLineCensus cfg p) (r : Fin 3) :
    twelveGridActualExternalPoint hcard H 1 ∉
      lineSupport (pivotInversion cfg p)
        (twelveGridActualPencilLine hcard H 0 r).1 := by
  intro hmem
  have hzero : twelveGridActualPencilIndex hcard H 0 r ∈
      sixFourBasesThrough (twelveGridActualFourSupport H)
        (twelveGridActualExternalPoint hcard H 0) := by
    apply mem_sixFourBasesThrough.mpr
    simpa [twelveGridActualFourSupport,
      twelveGridActualPencilLine] using
      (twelveGridActualExternalPoint_mem_pencilLine hcard H 0 r)
  have hone : twelveGridActualPencilIndex hcard H 0 r ∈
      sixFourBasesThrough (twelveGridActualFourSupport H)
        (twelveGridActualExternalPoint hcard H 1) := by
    apply mem_sixFourBasesThrough.mpr
    simpa [twelveGridActualFourSupport,
      twelveGridActualPencilLine] using hmem
  exact (Finset.disjoint_left.mp
    (sixFourExternalBases_disjoint
      (twelveGridActualFourSupport_isSaturatedSixFour hcard H))) hzero hone

/-- Two distinct members of one pencil have fewer than two actual labels in
common. -/
theorem twelveGridActualPencilLine_support_inter_lt_two
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (hcard : Fintype.card Point = 12)
    (H : TwelveGridInvertedLineCensus cfg p)
    (a : Fin 2) {r s : Fin 3} (hrs : r ≠ s) :
    (lineSupport (pivotInversion cfg p)
      (twelveGridActualPencilLine hcard H a r).1 ∩
      lineSupport (pivotInversion cfg p)
        (twelveGridActualPencilLine hcard H a s).1).card < 2 := by
  let Q := pivotInversion cfg p
  have hlineNe : (twelveGridActualPencilLine hcard H a r).1 ≠
      (twelveGridActualPencilLine hcard H a s).1 := by
    intro hline
    apply hrs
    apply twelveGridActualPencilIndex_injective hcard H a
    apply H.fourLine.injective
    apply Subtype.ext
    simpa [twelveGridActualPencilLine] using hline
  let bi : GeometricBlock Q :=
    Sum.inl (twelveGridActualPencilLine hcard H a r).1
  let bj : GeometricBlock Q :=
    Sum.inl (twelveGridActualPencilLine hcard H a s).1
  let Li : (blockSystem Q).LineBlock := ⟨bi, rfl⟩
  let Lj : (blockSystem Q).LineBlock := ⟨bj, rfl⟩
  have hLiNe : Li ≠ Lj := by
    intro h
    apply hlineNe
    simpa [Li, Lj, bi, bj] using h
  have hinter := (blockSystem Q).distinct_line_inter_card_lt_two hLiNe
  simpa [Q, Li, Lj, bi, bj, geometricBlockSupport] using hinter

/-- A grid crossing belongs to no other row of its pencil. -/
theorem twelveGridActualGridPoint_not_mem_other_row
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (hcard : Fintype.card Point = 12)
    (H : TwelveGridInvertedLineCensus cfg p)
    (r s r' : Fin 3) (hrr' : r ≠ r') :
    twelveGridActualGridPoint hcard H r s ∉
      lineSupport (pivotInversion cfg p)
        (twelveGridActualPencilLine hcard H 0 r').1 := by
  intro hother
  have hne := twelveGridActualExternalPoint_ne_gridPoint hcard H 0 r s
  have hsub : ({twelveGridActualExternalPoint hcard H 0,
      twelveGridActualGridPoint hcard H r s} : Finset (AwayFrom p)) ⊆
      lineSupport (pivotInversion cfg p)
        (twelveGridActualPencilLine hcard H 0 r).1 ∩
      lineSupport (pivotInversion cfg p)
        (twelveGridActualPencilLine hcard H 0 r').1 := by
    intro q hq
    simp only [Finset.mem_insert, Finset.mem_singleton] at hq
    rcases hq with rfl | rfl
    · exact Finset.mem_inter.mpr ⟨
        twelveGridActualExternalPoint_mem_pencilLine hcard H 0 r,
        twelveGridActualExternalPoint_mem_pencilLine hcard H 0 r'⟩
    · exact Finset.mem_inter.mpr ⟨
        twelveGridActualGridPoint_mem_row hcard H r s, hother⟩
  have hle := Finset.card_le_card hsub
  have hpair : ({twelveGridActualExternalPoint hcard H 0,
      twelveGridActualGridPoint hcard H r s} : Finset (AwayFrom p)).card = 2 :=
    Finset.card_pair hne
  rw [hpair] at hle
  have hlt := twelveGridActualPencilLine_support_inter_lt_two
    hcard H 0 hrr'
  omega

/-- A grid crossing belongs to no other column of its pencil. -/
theorem twelveGridActualGridPoint_not_mem_other_column
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (hcard : Fintype.card Point = 12)
    (H : TwelveGridInvertedLineCensus cfg p)
    (r s s' : Fin 3) (hss' : s ≠ s') :
    twelveGridActualGridPoint hcard H r s ∉
      lineSupport (pivotInversion cfg p)
        (twelveGridActualPencilLine hcard H 1 s').1 := by
  intro hother
  have hne := twelveGridActualExternalPoint_ne_gridPoint hcard H 1 r s
  have hsub : ({twelveGridActualExternalPoint hcard H 1,
      twelveGridActualGridPoint hcard H r s} : Finset (AwayFrom p)) ⊆
      lineSupport (pivotInversion cfg p)
        (twelveGridActualPencilLine hcard H 1 s).1 ∩
      lineSupport (pivotInversion cfg p)
        (twelveGridActualPencilLine hcard H 1 s').1 := by
    intro q hq
    simp only [Finset.mem_insert, Finset.mem_singleton] at hq
    rcases hq with rfl | rfl
    · exact Finset.mem_inter.mpr ⟨
        twelveGridActualExternalPoint_mem_pencilLine hcard H 1 s,
        twelveGridActualExternalPoint_mem_pencilLine hcard H 1 s'⟩
    · exact Finset.mem_inter.mpr ⟨
        twelveGridActualGridPoint_mem_column hcard H r s, hother⟩
  have hle := Finset.card_le_card hsub
  have hpair : ({twelveGridActualExternalPoint hcard H 1,
      twelveGridActualGridPoint hcard H r s} : Finset (AwayFrom p)).card = 2 :=
    Finset.card_pair hne
  rw [hpair] at hle
  have hlt := twelveGridActualPencilLine_support_inter_lt_two
    hcard H 1 hss'
  omega

/-! ## A projective four-line frame obtained from the actual grid -/

/-- The two first rows and two first columns, as raw covectors in the order
needed by `ProjectiveCovectorFrame`. -/
noncomputable def twelveGridActualFrameCovector
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (hcard : Fintype.card Point = 12)
    (H : TwelveGridInvertedLineCensus cfg p) : Fin 4 → Homogeneous3
  | 0 => twelveGridActualPencilCovector hcard H 0 0
  | 1 => twelveGridActualPencilCovector hcard H 0 1
  | 2 => twelveGridActualPencilCovector hcard H 1 0
  | 3 => twelveGridActualPencilCovector hcard H 1 1

private theorem twelveGridActualPencilCovector_det_ne_zero_of_point
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (hcard : Fintype.card Point = 12)
    (H : TwelveGridInvertedLineCensus cfg p)
    (a₀ a₁ a₂ : Fin 2) (r₀ r₁ r₂ : Fin 3)
    (hline : twelveGridActualProjectivePencilLine hcard H a₀ r₀ ≠
      twelveGridActualProjectivePencilLine hcard H a₁ r₁)
    (q : AwayFrom p)
    (hq₀ : q ∈ lineSupport (pivotInversion cfg p)
      (twelveGridActualPencilLine hcard H a₀ r₀).1)
    (hq₁ : q ∈ lineSupport (pivotInversion cfg p)
      (twelveGridActualPencilLine hcard H a₁ r₁).1)
    (hq₂ : q ∉ lineSupport (pivotInversion cfg p)
      (twelveGridActualPencilLine hcard H a₂ r₂).1) :
    Matrix.det ![twelveGridActualPencilCovector hcard H a₀ r₀,
      twelveGridActualPencilCovector hcard H a₁ r₁,
      twelveGridActualPencilCovector hcard H a₂ r₂] ≠ 0 := by
  intro hdet
  obtain ⟨z, hz, hz₀, hz₁, hz₂⟩ :=
    (det_eq_zero_iff_exists_common_nonzero_homogeneous
      (twelveGridActualPencilCovector hcard H a₀ r₀)
      (twelveGridActualPencilCovector hcard H a₁ r₁)
      (twelveGridActualPencilCovector hcard H a₂ r₂)).mp hdet
  let x : Homogeneous3 := homogeneousLift (pivotInversion cfg p q)
  have hx : x ≠ 0 := homogeneousLift_ne_zero _
  have hx₀ : twelveGridActualPencilCovector hcard H a₀ r₀ ⬝ᵥ x = 0 :=
    (twelveGridActualPencilCovector_incident_iff hcard H a₀ r₀ q).2 hq₀
  have hx₁ : twelveGridActualPencilCovector hcard H a₁ r₁ ⬝ᵥ x = 0 :=
    (twelveGridActualPencilCovector_incident_iff hcard H a₁ r₁ q).2 hq₁
  have hprojective :
      Projectivization.mk ℝ z hz = Projectivization.mk ℝ x hx :=
    projectiveCommonPoint_eq_of_two_distinct_covectors
      (twelveGridActualPencilCovector_ne_zero hcard H a₀ r₀)
      (twelveGridActualPencilCovector_ne_zero hcard H a₁ r₁) hz hx (by
        intro h
        apply hline
        simpa only [twelveGridActualPencilCovector_projectivize] using h)
      hz₀ hz₁ hx₀ hx₁
  have horth : Projectivization.orthogonal
      (Projectivization.mk ℝ
        (twelveGridActualPencilCovector hcard H a₂ r₂)
        (twelveGridActualPencilCovector_ne_zero hcard H a₂ r₂))
      (Projectivization.mk ℝ z hz) :=
    (Projectivization.orthogonal_mk
      (twelveGridActualPencilCovector_ne_zero hcard H a₂ r₂) hz).mpr hz₂
  rw [hprojective] at horth
  have hx₂ : twelveGridActualPencilCovector hcard H a₂ r₂ ⬝ᵥ x = 0 :=
    (Projectivization.orthogonal_mk
      (twelveGridActualPencilCovector_ne_zero hcard H a₂ r₂) hx).mp horth
  exact hq₂
    ((twelveGridActualPencilCovector_incident_iff hcard H a₂ r₂ q).1 hx₂)

/-- A cyclic rotation of three homogeneous rows does not change their
determinant. -/
private theorem twelveGridActual_det_rotate_rows
    (u v w : Homogeneous3) :
    Matrix.det ![u, v, w] = Matrix.det ![v, w, u] := by
  simp [Matrix.det_fin_three]
  ring

/-- The selected two rows and two columns are a projective complete
quadrangle.  This derives the only `GL₃` frame used below from the actual
line supports; it is not a normalization hypothesis. -/
theorem twelveGridActualFrameCovector_generalPosition
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (hcard : Fintype.card Point = 12)
    (H : TwelveGridInvertedLineCensus cfg p) :
    CompleteQuadrangleGeneralPosition
      (twelveGridActualFrameCovector hcard H 0)
      (twelveGridActualFrameCovector hcard H 1)
      (twelveGridActualFrameCovector hcard H 2)
      (twelveGridActualFrameCovector hcard H 3) := by
  constructor
  · simpa [twelveGridActualFrameCovector] using
      (twelveGridActualPencilCovector_det_ne_zero_of_point hcard H
        0 0 1 0 1 0
        (twelveGridActualProjectivePencilLine_same_ne hcard H 0 (by decide))
        (twelveGridActualExternalPoint hcard H 0)
        (twelveGridActualExternalPoint_mem_pencilLine hcard H 0 0)
        (twelveGridActualExternalPoint_mem_pencilLine hcard H 0 1)
        (twelveGridActualExternalPoint_zero_not_mem_column hcard H 0))
  · simpa [twelveGridActualFrameCovector] using
      (twelveGridActualPencilCovector_det_ne_zero_of_point hcard H
        0 0 1 0 1 1
        (twelveGridActualProjectivePencilLine_same_ne hcard H 0 (by decide))
        (twelveGridActualExternalPoint hcard H 0)
        (twelveGridActualExternalPoint_mem_pencilLine hcard H 0 0)
        (twelveGridActualExternalPoint_mem_pencilLine hcard H 0 1)
        (twelveGridActualExternalPoint_zero_not_mem_column hcard H 1))
  · rw [twelveGridActual_det_rotate_rows]
    simpa [twelveGridActualFrameCovector] using
      (twelveGridActualPencilCovector_det_ne_zero_of_point hcard H
        1 1 0 0 1 0
        (twelveGridActualProjectivePencilLine_same_ne hcard H 1 (by decide))
        (twelveGridActualExternalPoint hcard H 1)
        (twelveGridActualExternalPoint_mem_pencilLine hcard H 1 0)
        (twelveGridActualExternalPoint_mem_pencilLine hcard H 1 1)
        (twelveGridActualExternalPoint_one_not_mem_row hcard H 0))
  · rw [twelveGridActual_det_rotate_rows]
    simpa [twelveGridActualFrameCovector] using
      (twelveGridActualPencilCovector_det_ne_zero_of_point hcard H
        1 1 0 0 1 1
        (twelveGridActualProjectivePencilLine_same_ne hcard H 1 (by decide))
        (twelveGridActualExternalPoint hcard H 1)
        (twelveGridActualExternalPoint_mem_pencilLine hcard H 1 0)
        (twelveGridActualExternalPoint_mem_pencilLine hcard H 1 1)
        (twelveGridActualExternalPoint_one_not_mem_row hcard H 1))

/-- The canonical projective covector frame forced by the actual two-pencil
grid. -/
noncomputable def twelveGridActualCovectorFrame
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (hcard : Fintype.card Point = 12)
    (H : TwelveGridInvertedLineCensus cfg p) :
    ProjectiveCovectorFrame (twelveGridActualFrameCovector hcard H) :=
  projectiveCovectorFrame (twelveGridActualFrameCovector hcard H)
    (twelveGridActualFrameCovector_generalPosition hcard H)

/-! ## A concrete affine post-chart for the covector frame -/

/-- The fixed point-side matrix which turns the standard complete-quadrangle
frame into the affine rectangle with first levels `x = -1, x = 0` and
`y = -1, y = 0`. -/
def twelveGridAffinePostPointMatrix : Matrix (Fin 3) (Fin 3) ℝ :=
  ![![0, -1, 0], ![-1, -1, -1], ![1, 1, 0]]

/-- The contragredient matrix for `twelveGridAffinePostPointMatrix`.  The
two displayed matrices are explicit mutual inverse-transposes, so this is a
genuine projective coordinate change rather than an extra normalization
assumption. -/
def twelveGridAffinePostCovectorMatrix : Matrix (Fin 3) (Fin 3) ℝ :=
  ![![1, -1, 0], ![0, 0, -1], ![1, 0, -1]]

/-- The four affine frame covectors in the order used for the actual grid:
`x = -1`, `x = 0`, `y = -1`, `y = 0`. -/
def twelveGridAffineFrameCovector : Fin 4 → Homogeneous3
  | 0 => ![1, 0, 1]
  | 1 => ![1, 0, 0]
  | 2 => ![0, 1, 1]
  | 3 => ![0, 1, 0]

/-- The harmless representative signs introduced by the fixed post-chart. -/
def twelveGridAffineFrameScale : Fin 4 → ℝ
  | 0 => 1
  | 1 => -1
  | 2 => -1
  | 3 => -1

theorem twelveGridAffineFrameScale_ne_zero (i : Fin 4) :
    twelveGridAffineFrameScale i ≠ 0 := by
  fin_cases i <;> norm_num [twelveGridAffineFrameScale]

/-- Direct computation of the fixed post-chart on the standard four-line
frame. -/
theorem twelveGridAffinePostCovector_normalLine (i : Fin 4) :
    twelveGridAffinePostCovectorMatrix *ᵥ projectiveCovectorNormalLine i =
      twelveGridAffineFrameScale i • twelveGridAffineFrameCovector i := by
  fin_cases i <;> ext j <;> fin_cases j <;>
    norm_num [twelveGridAffinePostCovectorMatrix,
      twelveGridAffineFrameScale, twelveGridAffineFrameCovector,
      projectiveCovectorNormalLine, Matrix.mulVec, dotProduct,
      Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two]

/-- The fixed point and covector matrices preserve the homogeneous pairing. -/
theorem twelveGridAffinePost_dot (ell x : Homogeneous3) :
    (twelveGridAffinePostCovectorMatrix *ᵥ ell) ⬝ᵥ
        (twelveGridAffinePostPointMatrix *ᵥ x) = ell ⬝ᵥ x := by
  simp [twelveGridAffinePostCovectorMatrix,
    twelveGridAffinePostPointMatrix, Matrix.mulVec, dotProduct,
    Fin.sum_univ_three]
  ring

/-- An explicit left inverse for the point-side post-chart. -/
theorem twelveGridAffinePostPoint_leftInverse (x : Homogeneous3) :
    twelveGridAffinePostCovectorMatrix.transpose *ᵥ
        (twelveGridAffinePostPointMatrix *ᵥ x) = x := by
  ext i
  fin_cases i <;>
    simp [twelveGridAffinePostCovectorMatrix,
      twelveGridAffinePostPointMatrix, Matrix.mulVec, dotProduct,
      Fin.sum_univ_three] <;>
    ring

/-- The point-side fixed post-chart is injective. -/
theorem twelveGridAffinePostPoint_injective :
    Function.Injective (fun x : Homogeneous3 =>
      twelveGridAffinePostPointMatrix *ᵥ x) := by
  intro x y hxy
  have hleft := congrArg
    (fun z : Homogeneous3 => twelveGridAffinePostCovectorMatrix.transpose *ᵥ z)
    hxy
  simpa only [twelveGridAffinePostPoint_leftInverse] using hleft

/-- Apply the canonical actual covector frame and then the fixed affine
post-chart to a homogeneous point representative. -/
noncomputable def twelveGridActualAffineHomogeneous
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (hcard : Fintype.card Point = 12)
    (H : TwelveGridInvertedLineCensus cfg p) (x : Homogeneous3) : Homogeneous3 :=
  twelveGridAffinePostPointMatrix *ᵥ
    projectivePointTransform (twelveGridActualCovectorFrame hcard H).G x

/-- The corresponding contragredient transformation of a raw actual line
covector. -/
noncomputable def twelveGridActualAffineCovector
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (hcard : Fintype.card Point = 12)
    (H : TwelveGridInvertedLineCensus cfg p) (ell : Homogeneous3) :
    Homogeneous3 :=
  twelveGridAffinePostCovectorMatrix *ᵥ
    projectiveCovectorTransform (twelveGridActualCovectorFrame hcard H).G ell

/-- Homogeneous incidence is preserved by the derived actual affine chart. -/
theorem twelveGridActualAffineCovector_dot
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (hcard : Fintype.card Point = 12)
    (H : TwelveGridInvertedLineCensus cfg p)
    (ell x : Homogeneous3) :
    twelveGridActualAffineCovector hcard H ell ⬝ᵥ
        twelveGridActualAffineHomogeneous hcard H x = ell ⬝ᵥ x := by
  unfold twelveGridActualAffineCovector twelveGridActualAffineHomogeneous
  rw [twelveGridAffinePost_dot,
    projectiveCovectorTransform_dot_pointTransform]

/-- The four actual frame lines acquire exactly the intended affine
equations under the derived chart. -/
theorem twelveGridActualAffineCovector_frame
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (hcard : Fintype.card Point = 12)
    (H : TwelveGridInvertedLineCensus cfg p) (i : Fin 4) :
    twelveGridActualAffineCovector hcard H
      (twelveGridActualFrameCovector hcard H i) =
      ((twelveGridActualCovectorFrame hcard H).scale i *
        twelveGridAffineFrameScale i) • twelveGridAffineFrameCovector i := by
  let F := twelveGridActualCovectorFrame hcard H
  change twelveGridAffinePostCovectorMatrix *ᵥ
      projectiveCovectorTransform F.G
        (twelveGridActualFrameCovector hcard H i) = _
  calc
    twelveGridAffinePostCovectorMatrix *ᵥ
        projectiveCovectorTransform F.G
          (twelveGridActualFrameCovector hcard H i) =
        twelveGridAffinePostCovectorMatrix *ᵥ
          (F.scale i • projectiveCovectorNormalLine i) := by
      have h := congrArg (fun v : Homogeneous3 =>
        twelveGridAffinePostCovectorMatrix *ᵥ v) (F.map_covector i)
      simpa [projectiveCovectorTransform] using h
    _ = F.scale i •
        (twelveGridAffinePostCovectorMatrix *ᵥ projectiveCovectorNormalLine i) := by
      ext j
      fin_cases j <;>
        simp [twelveGridAffinePostCovectorMatrix, Matrix.mulVec,
          dotProduct, Fin.sum_univ_three] <;>
        ring
    _ = (F.scale i * twelveGridAffineFrameScale i) •
        twelveGridAffineFrameCovector i := by
      rw [twelveGridAffinePostCovector_normalLine]
      simp [smul_smul, mul_assoc]

/-- The transformed homogeneous representative of one actual inverted
label. -/
noncomputable def twelveGridActualAffinePoint
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (hcard : Fintype.card Point = 12)
    (H : TwelveGridInvertedLineCensus cfg p) (q : AwayFrom p) : Homogeneous3 :=
  twelveGridActualAffineHomogeneous hcard H
    (homogeneousLift (pivotInversion cfg p q))

/-- The transformed covector of one actual member of either reconstructed
pencil. -/
noncomputable def twelveGridActualAffinePencilCovector
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (hcard : Fintype.card Point = 12)
    (H : TwelveGridInvertedLineCensus cfg p)
    (a : Fin 2) (r : Fin 3) : Homogeneous3 :=
  twelveGridActualAffineCovector hcard H
    (twelveGridActualPencilCovector hcard H a r)

/-- The derived affine-chart transformation does not kill a nonzero
homogeneous point representative. -/
theorem twelveGridActualAffineHomogeneous_ne_zero
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (hcard : Fintype.card Point = 12)
    (H : TwelveGridInvertedLineCensus cfg p)
    (x : Homogeneous3) (hx : x ≠ 0) :
    twelveGridActualAffineHomogeneous hcard H x ≠ 0 := by
  intro hzero
  have hbefore : projectivePointTransform
      (twelveGridActualCovectorFrame hcard H).G x = 0 := by
    apply twelveGridAffinePostPoint_injective
    simpa [twelveGridActualAffineHomogeneous] using hzero
  have hbefore_ne : projectivePointTransform
      (twelveGridActualCovectorFrame hcard H).G x ≠ 0 := by
    simpa [projectivePointTransform] using
      ((smul_ne_zero_iff_ne (twelveGridActualCovectorFrame hcard H).G).mpr hx)
  exact hbefore_ne hbefore

/-- Every actual transformed label still has a nonzero homogeneous
representative. -/
theorem twelveGridActualAffinePoint_ne_zero
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (hcard : Fintype.card Point = 12)
    (H : TwelveGridInvertedLineCensus cfg p) (q : AwayFrom p) :
    twelveGridActualAffinePoint hcard H q ≠ 0 := by
  unfold twelveGridActualAffinePoint
  exact twelveGridActualAffineHomogeneous_ne_zero hcard H _
    (homogeneousLift_ne_zero _)

/-- Incidence with a transformed pencil covector remains exactly the
original actual-line support incidence. -/
theorem twelveGridActualAffinePencilCovector_incident_iff
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (hcard : Fintype.card Point = 12)
    (H : TwelveGridInvertedLineCensus cfg p)
    (a : Fin 2) (r : Fin 3) (q : AwayFrom p) :
    twelveGridActualAffinePencilCovector hcard H a r ⬝ᵥ
        twelveGridActualAffinePoint hcard H q = 0 ↔
      q ∈ lineSupport (pivotInversion cfg p)
        (twelveGridActualPencilLine hcard H a r).1 := by
  change twelveGridActualAffineCovector hcard H
      (twelveGridActualPencilCovector hcard H a r) ⬝ᵥ
      twelveGridActualAffineHomogeneous hcard H
        (homogeneousLift (pivotInversion cfg p q)) = 0 ↔ _
  rw [twelveGridActualAffineCovector_dot,
    twelveGridActualPencilCovector_incident_iff]

/-- The total representative scale of one of the four anchored affine
frame lines. -/
noncomputable def twelveGridActualAffineFrameScale
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (hcard : Fintype.card Point = 12)
    (H : TwelveGridInvertedLineCensus cfg p) (i : Fin 4) : ℝ :=
  (twelveGridActualCovectorFrame hcard H).scale i *
    twelveGridAffineFrameScale i

theorem twelveGridActualAffineFrameScale_ne_zero
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (hcard : Fintype.card Point = 12)
    (H : TwelveGridInvertedLineCensus cfg p) (i : Fin 4) :
    twelveGridActualAffineFrameScale hcard H i ≠ 0 := by
  exact mul_ne_zero ((twelveGridActualCovectorFrame hcard H).scale_ne_zero i)
    (twelveGridAffineFrameScale_ne_zero i)

/-- The first two members of the first actual pencil are the affine lines
`x = -1` and `x = 0`. -/
theorem twelveGridActualAffinePencilCovector_zero_zero
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (hcard : Fintype.card Point = 12)
    (H : TwelveGridInvertedLineCensus cfg p) :
    twelveGridActualAffinePencilCovector hcard H 0 0 =
      twelveGridActualAffineFrameScale hcard H 0 • (![1, 0, 1] : Homogeneous3) := by
  simpa [twelveGridActualAffinePencilCovector,
    twelveGridActualFrameCovector, twelveGridActualAffineFrameScale,
    twelveGridAffineFrameCovector, twelveGridAffineFrameScale] using
    (twelveGridActualAffineCovector_frame hcard H (0 : Fin 4))

theorem twelveGridActualAffinePencilCovector_zero_one
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (hcard : Fintype.card Point = 12)
    (H : TwelveGridInvertedLineCensus cfg p) :
    twelveGridActualAffinePencilCovector hcard H 0 1 =
      twelveGridActualAffineFrameScale hcard H 1 • (![1, 0, 0] : Homogeneous3) := by
  simpa [twelveGridActualAffinePencilCovector,
    twelveGridActualFrameCovector, twelveGridActualAffineFrameScale,
    twelveGridAffineFrameCovector, twelveGridAffineFrameScale] using
    (twelveGridActualAffineCovector_frame hcard H (1 : Fin 4))

/-- The first two members of the second actual pencil are the affine lines
`y = -1` and `y = 0`. -/
theorem twelveGridActualAffinePencilCovector_one_zero
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (hcard : Fintype.card Point = 12)
    (H : TwelveGridInvertedLineCensus cfg p) :
    twelveGridActualAffinePencilCovector hcard H 1 0 =
      twelveGridActualAffineFrameScale hcard H 2 • (![0, 1, 1] : Homogeneous3) := by
  simpa [twelveGridActualAffinePencilCovector,
    twelveGridActualFrameCovector, twelveGridActualAffineFrameScale,
    twelveGridAffineFrameCovector, twelveGridAffineFrameScale] using
    (twelveGridActualAffineCovector_frame hcard H (2 : Fin 4))

theorem twelveGridActualAffinePencilCovector_one_one
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (hcard : Fintype.card Point = 12)
    (H : TwelveGridInvertedLineCensus cfg p) :
    twelveGridActualAffinePencilCovector hcard H 1 1 =
      twelveGridActualAffineFrameScale hcard H 3 • (![0, 1, 0] : Homogeneous3) := by
  simpa [twelveGridActualAffinePencilCovector,
    twelveGridActualFrameCovector, twelveGridActualAffineFrameScale,
    twelveGridAffineFrameCovector, twelveGridAffineFrameScale] using
    (twelveGridActualAffineCovector_frame hcard H (3 : Fin 4))

private theorem twelveGrid_smul_covector_dot_eq_zero_iff
    {c : ℝ} (hc : c ≠ 0) (ell x : Homogeneous3) :
    (c • ell) ⬝ᵥ x = 0 ↔ ell ⬝ᵥ x = 0 := by
  rw [smul_dotProduct, smul_eq_mul]
  constructor
  · intro h
    exact (mul_eq_zero.mp h).resolve_left hc
  · intro h
    rw [h, mul_zero]

/-! ### The two actual pencil centres become the two ideal points -/

theorem twelveGridActualAffineExternal_zero_apply_zero
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (hcard : Fintype.card Point = 12)
    (H : TwelveGridInvertedLineCensus cfg p) :
    twelveGridActualAffinePoint hcard H
      (twelveGridActualExternalPoint hcard H 0) 0 = 0 := by
  have hinc := (twelveGridActualAffinePencilCovector_incident_iff
    hcard H 0 1 (twelveGridActualExternalPoint hcard H 0)).2
      (twelveGridActualExternalPoint_mem_pencilLine hcard H 0 1)
  rw [twelveGridActualAffinePencilCovector_zero_one] at hinc
  have hdot : (![1, 0, 0] : Homogeneous3) ⬝ᵥ
      twelveGridActualAffinePoint hcard H
        (twelveGridActualExternalPoint hcard H 0) = 0 :=
    (twelveGrid_smul_covector_dot_eq_zero_iff
      (twelveGridActualAffineFrameScale_ne_zero hcard H 1)
      _ _).mp hinc
  simpa [dotProduct, Fin.sum_univ_three] using hdot

theorem twelveGridActualAffineExternal_zero_apply_two
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (hcard : Fintype.card Point = 12)
    (H : TwelveGridInvertedLineCensus cfg p) :
    twelveGridActualAffinePoint hcard H
      (twelveGridActualExternalPoint hcard H 0) 2 = 0 := by
  have hinc := (twelveGridActualAffinePencilCovector_incident_iff
    hcard H 0 0 (twelveGridActualExternalPoint hcard H 0)).2
      (twelveGridActualExternalPoint_mem_pencilLine hcard H 0 0)
  rw [twelveGridActualAffinePencilCovector_zero_zero] at hinc
  have hdot : (![1, 0, 1] : Homogeneous3) ⬝ᵥ
      twelveGridActualAffinePoint hcard H
        (twelveGridActualExternalPoint hcard H 0) = 0 :=
    (twelveGrid_smul_covector_dot_eq_zero_iff
      (twelveGridActualAffineFrameScale_ne_zero hcard H 0)
      _ _).mp hinc
  have hsum : twelveGridActualAffinePoint hcard H
      (twelveGridActualExternalPoint hcard H 0) 0 +
      twelveGridActualAffinePoint hcard H
        (twelveGridActualExternalPoint hcard H 0) 2 = 0 := by
    simpa [dotProduct, Fin.sum_univ_three] using hdot
  linarith [hsum, twelveGridActualAffineExternal_zero_apply_zero hcard H]

theorem twelveGridActualAffineExternal_zero_apply_one_ne_zero
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (hcard : Fintype.card Point = 12)
    (H : TwelveGridInvertedLineCensus cfg p) :
    twelveGridActualAffinePoint hcard H
      (twelveGridActualExternalPoint hcard H 0) 1 ≠ 0 := by
  intro hzero
  apply twelveGridActualAffinePoint_ne_zero hcard H
    (twelveGridActualExternalPoint hcard H 0)
  ext i
  fin_cases i <;>
    simp [twelveGridActualAffineExternal_zero_apply_zero hcard H,
      twelveGridActualAffineExternal_zero_apply_two hcard H, hzero]

theorem twelveGridActualAffineExternal_one_apply_one
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (hcard : Fintype.card Point = 12)
    (H : TwelveGridInvertedLineCensus cfg p) :
    twelveGridActualAffinePoint hcard H
      (twelveGridActualExternalPoint hcard H 1) 1 = 0 := by
  have hinc := (twelveGridActualAffinePencilCovector_incident_iff
    hcard H 1 1 (twelveGridActualExternalPoint hcard H 1)).2
      (twelveGridActualExternalPoint_mem_pencilLine hcard H 1 1)
  rw [twelveGridActualAffinePencilCovector_one_one] at hinc
  have hdot : (![0, 1, 0] : Homogeneous3) ⬝ᵥ
      twelveGridActualAffinePoint hcard H
        (twelveGridActualExternalPoint hcard H 1) = 0 :=
    (twelveGrid_smul_covector_dot_eq_zero_iff
      (twelveGridActualAffineFrameScale_ne_zero hcard H 3)
      _ _).mp hinc
  simpa [dotProduct, Fin.sum_univ_three] using hdot

theorem twelveGridActualAffineExternal_one_apply_two
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (hcard : Fintype.card Point = 12)
    (H : TwelveGridInvertedLineCensus cfg p) :
    twelveGridActualAffinePoint hcard H
      (twelveGridActualExternalPoint hcard H 1) 2 = 0 := by
  have hinc := (twelveGridActualAffinePencilCovector_incident_iff
    hcard H 1 0 (twelveGridActualExternalPoint hcard H 1)).2
      (twelveGridActualExternalPoint_mem_pencilLine hcard H 1 0)
  rw [twelveGridActualAffinePencilCovector_one_zero] at hinc
  have hdot : (![0, 1, 1] : Homogeneous3) ⬝ᵥ
      twelveGridActualAffinePoint hcard H
        (twelveGridActualExternalPoint hcard H 1) = 0 :=
    (twelveGrid_smul_covector_dot_eq_zero_iff
      (twelveGridActualAffineFrameScale_ne_zero hcard H 2)
      _ _).mp hinc
  have hsum : twelveGridActualAffinePoint hcard H
      (twelveGridActualExternalPoint hcard H 1) 1 +
      twelveGridActualAffinePoint hcard H
        (twelveGridActualExternalPoint hcard H 1) 2 = 0 := by
    simpa [dotProduct, Fin.sum_univ_three] using hdot
  linarith [hsum, twelveGridActualAffineExternal_one_apply_one hcard H]

theorem twelveGridActualAffineExternal_one_apply_zero_ne_zero
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (hcard : Fintype.card Point = 12)
    (H : TwelveGridInvertedLineCensus cfg p) :
    twelveGridActualAffinePoint hcard H
      (twelveGridActualExternalPoint hcard H 1) 0 ≠ 0 := by
  intro hzero
  apply twelveGridActualAffinePoint_ne_zero hcard H
    (twelveGridActualExternalPoint hcard H 1)
  ext i
  fin_cases i <;>
    simp [twelveGridActualAffineExternal_one_apply_one hcard H,
      twelveGridActualAffineExternal_one_apply_two hcard H, hzero]

/-! ### Every member of a pencil is parallel in the derived affine chart -/

theorem twelveGridActualAffinePencilCovector_zero_apply_one
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (hcard : Fintype.card Point = 12)
    (H : TwelveGridInvertedLineCensus cfg p) (r : Fin 3) :
    twelveGridActualAffinePencilCovector hcard H 0 r 1 = 0 := by
  have hinc := (twelveGridActualAffinePencilCovector_incident_iff
    hcard H 0 r (twelveGridActualExternalPoint hcard H 0)).2
      (twelveGridActualExternalPoint_mem_pencilLine hcard H 0 r)
  have hprod : twelveGridActualAffinePencilCovector hcard H 0 r 1 *
      twelveGridActualAffinePoint hcard H
        (twelveGridActualExternalPoint hcard H 0) 1 = 0 := by
    simpa [dotProduct, Fin.sum_univ_three,
      twelveGridActualAffineExternal_zero_apply_zero hcard H,
      twelveGridActualAffineExternal_zero_apply_two hcard H] using hinc
  exact (mul_eq_zero.mp hprod).resolve_right
    (twelveGridActualAffineExternal_zero_apply_one_ne_zero hcard H)

theorem twelveGridActualAffinePencilCovector_zero_apply_zero_ne_zero
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (hcard : Fintype.card Point = 12)
    (H : TwelveGridInvertedLineCensus cfg p) (r : Fin 3) :
    twelveGridActualAffinePencilCovector hcard H 0 r 0 ≠ 0 := by
  intro hzero
  have hinc : twelveGridActualAffinePencilCovector hcard H 0 r ⬝ᵥ
      twelveGridActualAffinePoint hcard H
        (twelveGridActualExternalPoint hcard H 1) = 0 := by
    simp [dotProduct, Fin.sum_univ_three, hzero,
      twelveGridActualAffinePencilCovector_zero_apply_one hcard H r,
      twelveGridActualAffineExternal_one_apply_one hcard H,
      twelveGridActualAffineExternal_one_apply_two hcard H]
  apply twelveGridActualExternalPoint_one_not_mem_row hcard H r
  exact (twelveGridActualAffinePencilCovector_incident_iff
    hcard H 0 r (twelveGridActualExternalPoint hcard H 1)).1 hinc

theorem twelveGridActualAffinePencilCovector_one_apply_zero
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (hcard : Fintype.card Point = 12)
    (H : TwelveGridInvertedLineCensus cfg p) (s : Fin 3) :
    twelveGridActualAffinePencilCovector hcard H 1 s 0 = 0 := by
  have hinc := (twelveGridActualAffinePencilCovector_incident_iff
    hcard H 1 s (twelveGridActualExternalPoint hcard H 1)).2
      (twelveGridActualExternalPoint_mem_pencilLine hcard H 1 s)
  have hprod : twelveGridActualAffinePencilCovector hcard H 1 s 0 *
      twelveGridActualAffinePoint hcard H
        (twelveGridActualExternalPoint hcard H 1) 0 = 0 := by
    simpa [dotProduct, Fin.sum_univ_three,
      twelveGridActualAffineExternal_one_apply_one hcard H,
      twelveGridActualAffineExternal_one_apply_two hcard H] using hinc
  exact (mul_eq_zero.mp hprod).resolve_right
    (twelveGridActualAffineExternal_one_apply_zero_ne_zero hcard H)

theorem twelveGridActualAffinePencilCovector_one_apply_one_ne_zero
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (hcard : Fintype.card Point = 12)
    (H : TwelveGridInvertedLineCensus cfg p) (s : Fin 3) :
    twelveGridActualAffinePencilCovector hcard H 1 s 1 ≠ 0 := by
  intro hzero
  have hinc : twelveGridActualAffinePencilCovector hcard H 1 s ⬝ᵥ
      twelveGridActualAffinePoint hcard H
        (twelveGridActualExternalPoint hcard H 0) = 0 := by
    simp [dotProduct, Fin.sum_univ_three, hzero,
      twelveGridActualAffinePencilCovector_one_apply_zero hcard H s,
      twelveGridActualAffineExternal_zero_apply_zero hcard H,
      twelveGridActualAffineExternal_zero_apply_two hcard H]
  apply twelveGridActualExternalPoint_zero_not_mem_column hcard H s
  exact (twelveGridActualAffinePencilCovector_incident_iff
    hcard H 1 s (twelveGridActualExternalPoint hcard H 0)).1 hinc

/-! ### The two remaining affine cross-ratio parameters -/

/-- The affine `x`-level of a member of the first pencil. -/
noncomputable def twelveGridActualColumnCoordinate
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (hcard : Fintype.card Point = 12)
    (H : TwelveGridInvertedLineCensus cfg p) (r : Fin 3) : ℝ :=
  -(twelveGridActualAffinePencilCovector hcard H 0 r 2 /
    twelveGridActualAffinePencilCovector hcard H 0 r 0)

/-- The affine `y`-level of a member of the second pencil. -/
noncomputable def twelveGridActualRowCoordinate
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (hcard : Fintype.card Point = 12)
    (H : TwelveGridInvertedLineCensus cfg p) (s : Fin 3) : ℝ :=
  -(twelveGridActualAffinePencilCovector hcard H 1 s 2 /
    twelveGridActualAffinePencilCovector hcard H 1 s 1)

/-- Every first-pencil covector has equation `x = constant` in the derived
affine chart. -/
theorem twelveGridActualAffinePencilCovector_zero_normal_form
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (hcard : Fintype.card Point = 12)
    (H : TwelveGridInvertedLineCensus cfg p) (r : Fin 3) :
    twelveGridActualAffinePencilCovector hcard H 0 r =
      twelveGridActualAffinePencilCovector hcard H 0 r 0 •
        (![1, 0, -twelveGridActualColumnCoordinate hcard H r] : Homogeneous3) := by
  ext i
  fin_cases i
  · simp
  · simp [twelveGridActualAffinePencilCovector_zero_apply_one hcard H r]
  · have hne := twelveGridActualAffinePencilCovector_zero_apply_zero_ne_zero
        hcard H r
    simp [twelveGridActualColumnCoordinate]
    field_simp [hne]

/-- Every second-pencil covector has equation `y = constant` in the derived
affine chart. -/
theorem twelveGridActualAffinePencilCovector_one_normal_form
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (hcard : Fintype.card Point = 12)
    (H : TwelveGridInvertedLineCensus cfg p) (s : Fin 3) :
    twelveGridActualAffinePencilCovector hcard H 1 s =
      twelveGridActualAffinePencilCovector hcard H 1 s 1 •
        (![0, 1, -twelveGridActualRowCoordinate hcard H s] : Homogeneous3) := by
  ext i
  fin_cases i
  · simp [twelveGridActualAffinePencilCovector_one_apply_zero hcard H s]
  · simp
  · have hne := twelveGridActualAffinePencilCovector_one_apply_one_ne_zero
        hcard H s
    simp [twelveGridActualRowCoordinate]
    field_simp [hne]

theorem twelveGridActualColumnCoordinate_zero
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (hcard : Fintype.card Point = 12)
    (H : TwelveGridInvertedLineCensus cfg p) :
    twelveGridActualColumnCoordinate hcard H 0 = -1 := by
  unfold twelveGridActualColumnCoordinate
  rw [twelveGridActualAffinePencilCovector_zero_zero]
  simp [twelveGridActualAffineFrameScale_ne_zero hcard H 0]

theorem twelveGridActualColumnCoordinate_one
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (hcard : Fintype.card Point = 12)
    (H : TwelveGridInvertedLineCensus cfg p) :
    twelveGridActualColumnCoordinate hcard H 1 = 0 := by
  unfold twelveGridActualColumnCoordinate
  rw [twelveGridActualAffinePencilCovector_zero_one]
  simp

theorem twelveGridActualRowCoordinate_zero
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (hcard : Fintype.card Point = 12)
    (H : TwelveGridInvertedLineCensus cfg p) :
    twelveGridActualRowCoordinate hcard H 0 = -1 := by
  unfold twelveGridActualRowCoordinate
  rw [twelveGridActualAffinePencilCovector_one_zero]
  simp [twelveGridActualAffineFrameScale_ne_zero hcard H 2]

theorem twelveGridActualRowCoordinate_one
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (hcard : Fintype.card Point = 12)
    (H : TwelveGridInvertedLineCensus cfg p) :
    twelveGridActualRowCoordinate hcard H 1 = 0 := by
  unfold twelveGridActualRowCoordinate
  rw [twelveGridActualAffinePencilCovector_one_one]
  simp

/-- The two true projective parameters of the actual grid. -/
noncomputable def twelveGridActualColumnParameter
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (hcard : Fintype.card Point = 12)
    (H : TwelveGridInvertedLineCensus cfg p) : ℝ :=
  twelveGridActualColumnCoordinate hcard H 2

noncomputable def twelveGridActualRowParameter
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (hcard : Fintype.card Point = 12)
    (H : TwelveGridInvertedLineCensus cfg p) : ℝ :=
  twelveGridActualRowCoordinate hcard H 2

theorem twelveGridActualColumnCoordinate_eq_parameter
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (hcard : Fintype.card Point = 12)
    (H : TwelveGridInvertedLineCensus cfg p) (r : Fin 3) :
    twelveGridActualColumnCoordinate hcard H r =
      threeByThreePencilCoordinate (twelveGridActualColumnParameter hcard H) r := by
  fin_cases r
  · simpa [threeByThreePencilCoordinate] using
      twelveGridActualColumnCoordinate_zero hcard H
  · simpa [threeByThreePencilCoordinate] using
      twelveGridActualColumnCoordinate_one hcard H
  · simp [twelveGridActualColumnParameter, threeByThreePencilCoordinate]

theorem twelveGridActualRowCoordinate_eq_parameter
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (hcard : Fintype.card Point = 12)
    (H : TwelveGridInvertedLineCensus cfg p) (s : Fin 3) :
    twelveGridActualRowCoordinate hcard H s =
      threeByThreePencilCoordinate (twelveGridActualRowParameter hcard H) s := by
  fin_cases s
  · simpa [threeByThreePencilCoordinate] using
      twelveGridActualRowCoordinate_zero hcard H
  · simpa [threeByThreePencilCoordinate] using
      twelveGridActualRowCoordinate_one hcard H
  · simp [twelveGridActualRowParameter, threeByThreePencilCoordinate]

/-! ### The nine labelled crossings in the derived chart -/

theorem twelveGridActualAffineGridPoint_apply_two
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (hcard : Fintype.card Point = 12)
    (H : TwelveGridInvertedLineCensus cfg p) (r s : Fin 3) :
    twelveGridActualAffinePoint hcard H
      (twelveGridActualGridPoint hcard H r s) 2 ≠ 0 := by
  intro htwo
  have hx := (twelveGridActualAffinePencilCovector_incident_iff
    hcard H 0 r (twelveGridActualGridPoint hcard H r s)).2
      (twelveGridActualGridPoint_mem_row hcard H r s)
  have hy := (twelveGridActualAffinePencilCovector_incident_iff
    hcard H 1 s (twelveGridActualGridPoint hcard H r s)).2
      (twelveGridActualGridPoint_mem_column hcard H r s)
  rw [twelveGridActualAffinePencilCovector_zero_normal_form] at hx
  rw [twelveGridActualAffinePencilCovector_one_normal_form] at hy
  have hxeq : twelveGridActualAffinePoint hcard H
      (twelveGridActualGridPoint hcard H r s) 0 = 0 := by
    have hraw : (![1, 0,
        -twelveGridActualColumnCoordinate hcard H r] : Homogeneous3) ⬝ᵥ
        twelveGridActualAffinePoint hcard H
          (twelveGridActualGridPoint hcard H r s) = 0 :=
      (twelveGrid_smul_covector_dot_eq_zero_iff
        (twelveGridActualAffinePencilCovector_zero_apply_zero_ne_zero hcard H r)
        _ _).mp hx
    simpa [dotProduct, Fin.sum_univ_three, htwo] using hraw
  have hyeq : twelveGridActualAffinePoint hcard H
      (twelveGridActualGridPoint hcard H r s) 1 = 0 := by
    have hraw : (![0, 1,
        -twelveGridActualRowCoordinate hcard H s] : Homogeneous3) ⬝ᵥ
        twelveGridActualAffinePoint hcard H
          (twelveGridActualGridPoint hcard H r s) = 0 :=
      (twelveGrid_smul_covector_dot_eq_zero_iff
        (twelveGridActualAffinePencilCovector_one_apply_one_ne_zero hcard H s)
        _ _).mp hy
    simpa [dotProduct, Fin.sum_univ_three, htwo] using hraw
  apply twelveGridActualAffinePoint_ne_zero hcard H
    (twelveGridActualGridPoint hcard H r s)
  ext i
  fin_cases i <;> simp [hxeq, hyeq, htwo]

/-- Dehomogenize a transformed labelled grid crossing. -/
noncomputable def twelveGridActualAffineGridCoordinate
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (hcard : Fintype.card Point = 12)
    (H : TwelveGridInvertedLineCensus cfg p) (r s : Fin 3) : ℝ × ℝ :=
  (twelveGridActualAffinePoint hcard H
      (twelveGridActualGridPoint hcard H r s) 0 /
      twelveGridActualAffinePoint hcard H
        (twelveGridActualGridPoint hcard H r s) 2,
    twelveGridActualAffinePoint hcard H
      (twelveGridActualGridPoint hcard H r s) 1 /
      twelveGridActualAffinePoint hcard H
        (twelveGridActualGridPoint hcard H r s) 2)

theorem twelveGridActualAffineGridCoordinate_eq
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (hcard : Fintype.card Point = 12)
    (H : TwelveGridInvertedLineCensus cfg p) (r s : Fin 3) :
    twelveGridActualAffineGridCoordinate hcard H r s =
      (twelveGridActualColumnCoordinate hcard H r,
        twelveGridActualRowCoordinate hcard H s) := by
  apply Prod.ext
  · unfold twelveGridActualAffineGridCoordinate
    have hinc := (twelveGridActualAffinePencilCovector_incident_iff
      hcard H 0 r (twelveGridActualGridPoint hcard H r s)).2
        (twelveGridActualGridPoint_mem_row hcard H r s)
    rw [twelveGridActualAffinePencilCovector_zero_normal_form] at hinc
    have hraw : (![1, 0,
        -twelveGridActualColumnCoordinate hcard H r] : Homogeneous3) ⬝ᵥ
        twelveGridActualAffinePoint hcard H
          (twelveGridActualGridPoint hcard H r s) = 0 :=
      (twelveGrid_smul_covector_dot_eq_zero_iff
        (twelveGridActualAffinePencilCovector_zero_apply_zero_ne_zero hcard H r)
        _ _).mp hinc
    have hne := twelveGridActualAffineGridPoint_apply_two hcard H r s
    simp [dotProduct, Fin.sum_univ_three] at hraw
    field_simp [hne]
    linarith
  · unfold twelveGridActualAffineGridCoordinate
    have hinc := (twelveGridActualAffinePencilCovector_incident_iff
      hcard H 1 s (twelveGridActualGridPoint hcard H r s)).2
        (twelveGridActualGridPoint_mem_column hcard H r s)
    rw [twelveGridActualAffinePencilCovector_one_normal_form] at hinc
    have hraw : (![0, 1,
        -twelveGridActualRowCoordinate hcard H s] : Homogeneous3) ⬝ᵥ
        twelveGridActualAffinePoint hcard H
          (twelveGridActualGridPoint hcard H r s) = 0 :=
      (twelveGrid_smul_covector_dot_eq_zero_iff
        (twelveGridActualAffinePencilCovector_one_apply_one_ne_zero hcard H s)
        _ _).mp hinc
    have hne := twelveGridActualAffineGridPoint_apply_two hcard H r s
    simp [dotProduct, Fin.sum_univ_three] at hraw
    field_simp [hne]
    linarith

/-- Full lossless identification of the nine actual labelled crossings with
the parameterized grid `{−1,0,a} × {−1,0,b}`. -/
theorem twelveGridActualAffineGridCoordinate_parameterized
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (hcard : Fintype.card Point = 12)
    (H : TwelveGridInvertedLineCensus cfg p) (r s : Fin 3) :
    twelveGridActualAffineGridCoordinate hcard H r s =
      threeByThreeParameterizedGridPoint
        (twelveGridActualColumnParameter hcard H)
        (twelveGridActualRowParameter hcard H) (r, s) := by
  rw [twelveGridActualAffineGridCoordinate_eq]
  simp only [threeByThreeParameterizedGridPoint]
  rw [twelveGridActualColumnCoordinate_eq_parameter,
    twelveGridActualRowCoordinate_eq_parameter]

/-! ### A lossless affine chart on all eleven actual labels -/

/-- The transformed projective representative of an actual label has
nonzero third coordinate exactly when it belongs to the affine part of the
derived chart. -/
def TwelveGridActualAffineFinite
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (hcard : Fintype.card Point = 12)
    (H : TwelveGridInvertedLineCensus cfg p) (q : AwayFrom p) : Prop :=
  twelveGridActualAffinePoint hcard H q 2 ≠ 0

/-- Dehomogenization of every actual label which is finite in the derived
affine chart. -/
noncomputable def twelveGridActualAffineCoordinate
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (hcard : Fintype.card Point = 12)
    (H : TwelveGridInvertedLineCensus cfg p)
    (q : {q : AwayFrom p // TwelveGridActualAffineFinite hcard H q}) : ℝ × ℝ :=
  (twelveGridActualAffinePoint hcard H q.1 0 /
      twelveGridActualAffinePoint hcard H q.1 2,
    twelveGridActualAffinePoint hcard H q.1 1 /
      twelveGridActualAffinePoint hcard H q.1 2)

/-- The project's affine `Point2` corresponding to a displayed pair of real
coordinates.  Keeping this conversion explicit avoids identifying a product
with the finite-dimensional function space definitionally. -/
noncomputable def twelveGridAffinePairPoint2 (z : ℝ × ℝ) : Point2 :=
  EuclideanSpace.single (0 : Fin 2) z.1 +
    EuclideanSpace.single (1 : Fin 2) z.2

@[simp] theorem twelveGridAffinePairPoint2_apply_zero (z : ℝ × ℝ) :
    twelveGridAffinePairPoint2 z (0 : Fin 2) = z.1 := by
  simp [twelveGridAffinePairPoint2]

@[simp] theorem twelveGridAffinePairPoint2_apply_one (z : ℝ × ℝ) :
    twelveGridAffinePairPoint2 z (1 : Fin 2) = z.2 := by
  simp [twelveGridAffinePairPoint2]

/-- The transformed representative is the homogeneous lift of its affine
coordinate, up to precisely its nonzero last coordinate. -/
theorem twelveGridActualAffinePoint_eq_scale_homogeneousLift
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (hcard : Fintype.card Point = 12)
    (H : TwelveGridInvertedLineCensus cfg p)
    (q : {q : AwayFrom p // TwelveGridActualAffineFinite hcard H q}) :
    twelveGridActualAffinePoint hcard H q.1 =
      twelveGridActualAffinePoint hcard H q.1 2 •
        homogeneousLift
          (twelveGridAffinePairPoint2
            (twelveGridActualAffineCoordinate hcard H q)) := by
  ext i
  fin_cases i
  · simp [homogeneousLift, twelveGridActualAffineCoordinate,
      twelveGridAffinePairPoint2]
    rw [mul_comm, div_mul_cancel₀ _ q.2]
  · simp [homogeneousLift, twelveGridActualAffineCoordinate,
      twelveGridAffinePairPoint2]
    rw [mul_comm, div_mul_cancel₀ _ q.2]
  · simp [homogeneousLift, twelveGridAffinePairPoint2]

/-! ### The grid points are finite and retain their displayed coordinates -/

noncomputable def twelveGridActualAffineGridLabel
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (hcard : Fintype.card Point = 12)
    (H : TwelveGridInvertedLineCensus cfg p) (rs : Fin 3 × Fin 3) :
    {q : AwayFrom p // TwelveGridActualAffineFinite hcard H q} :=
  ⟨twelveGridActualGridPoint hcard H rs.1 rs.2,
    twelveGridActualAffineGridPoint_apply_two hcard H rs.1 rs.2⟩

theorem twelveGridActualAffineGridLabel_coordinate
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (hcard : Fintype.card Point = 12)
    (H : TwelveGridInvertedLineCensus cfg p) (rs : Fin 3 × Fin 3) :
    twelveGridActualAffineCoordinate hcard H
      (twelveGridActualAffineGridLabel hcard H rs) =
      threeByThreeParameterizedGridPoint
        (twelveGridActualColumnParameter hcard H)
        (twelveGridActualRowParameter hcard H) rs := by
  rcases rs with ⟨r, s⟩
  exact twelveGridActualAffineGridCoordinate_parameterized hcard H r s


end Erdos506.V1
