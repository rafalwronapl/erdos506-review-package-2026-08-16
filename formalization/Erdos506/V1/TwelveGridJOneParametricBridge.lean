import Erdos506.V1.TwelveGridJOneCap
import Erdos506.V1.TwelveGridParametricObstruction
import Erdos506.V1.TwelveGridParametricEndpoint
import Erdos506.Incidence.ParameterizedThreeByThreeGridThreeTransversal
import Mathlib.Tactic

/-!
# Projective-to-parametric bridge for the `j = 1` equality census

This is the real-projective continuation of the six-four reconstruction in
`TwelveGridJOneCap`.  It constructs its coordinate frame from four actual
reconstructed four-lines.  In particular, the affine chart and its two
parameters are derived data, never a normalization hypothesis.
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

/-! ## Raw covectors of the reconstructed pencil lines -/

noncomputable def twelveGridJOneProjectivePencilLine
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (hcard : Fintype.card Point = 12)
    (H : TwelveGridJOneInvertedLineCensus cfg p)
    (a : Fin 2) (r : Fin 3) : RealProjectiveLine :=
  determinedProjectiveLine (pivotInversion cfg p)
    (twelveGridJOnePencilLine hcard H a r).1

noncomputable def twelveGridJOnePencilCovector
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (hcard : Fintype.card Point = 12)
    (H : TwelveGridJOneInvertedLineCensus cfg p)
    (a : Fin 2) (r : Fin 3) : Homogeneous3 :=
  (twelveGridJOneProjectivePencilLine hcard H a r).rep

theorem twelveGridJOnePencilCovector_ne_zero
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (hcard : Fintype.card Point = 12)
    (H : TwelveGridJOneInvertedLineCensus cfg p)
    (a : Fin 2) (r : Fin 3) :
    twelveGridJOnePencilCovector hcard H a r ≠ 0 := by
  simpa [twelveGridJOnePencilCovector] using
    (twelveGridJOneProjectivePencilLine hcard H a r).rep_nonzero

@[simp] theorem twelveGridJOnePencilCovector_projectivize
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (hcard : Fintype.card Point = 12)
    (H : TwelveGridJOneInvertedLineCensus cfg p)
    (a : Fin 2) (r : Fin 3) :
    Projectivization.mk ℝ (twelveGridJOnePencilCovector hcard H a r)
      (twelveGridJOnePencilCovector_ne_zero hcard H a r) =
      twelveGridJOneProjectivePencilLine hcard H a r := by
  simpa [twelveGridJOnePencilCovector] using
    (Projectivization.mk_rep
      (twelveGridJOneProjectivePencilLine hcard H a r))

theorem twelveGridJOnePencilCovector_incident_iff
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (hcard : Fintype.card Point = 12)
    (H : TwelveGridJOneInvertedLineCensus cfg p)
    (a : Fin 2) (r : Fin 3) (q : AwayFrom p) :
    twelveGridJOnePencilCovector hcard H a r ⬝ᵥ
        homogeneousLift (pivotInversion cfg p q) = 0 ↔
      q ∈ lineSupport (pivotInversion cfg p)
        (twelveGridJOnePencilLine hcard H a r).1 := by
  have hmem := affinePoint_mem_determinedProjectiveLine_iff
    (pivotInversion cfg p) q (twelveGridJOnePencilLine hcard H a r).1
  calc
    twelveGridJOnePencilCovector hcard H a r ⬝ᵥ
        homogeneousLift (pivotInversion cfg p q) = 0 ↔
      homogeneousLift (pivotInversion cfg p q) ⬝ᵥ
          twelveGridJOnePencilCovector hcard H a r = 0 := by
        constructor
        · intro h
          calc
            homogeneousLift (pivotInversion cfg p q) ⬝ᵥ
                twelveGridJOnePencilCovector hcard H a r =
                twelveGridJOnePencilCovector hcard H a r ⬝ᵥ
                  homogeneousLift (pivotInversion cfg p q) :=
              dotProduct_comm _ _
            _ = 0 := h
        · intro h
          calc
            twelveGridJOnePencilCovector hcard H a r ⬝ᵥ
                homogeneousLift (pivotInversion cfg p q) =
                homogeneousLift (pivotInversion cfg p q) ⬝ᵥ
                  twelveGridJOnePencilCovector hcard H a r :=
              dotProduct_comm _ _
            _ = 0 := h
    _ ↔ projectivePoint (pivotInversion cfg p q) ∈
        Projectivization.mk ℝ
          (twelveGridJOnePencilCovector hcard H a r)
          (twelveGridJOnePencilCovector_ne_zero hcard H a r) := by
      change _ ↔ Projectivization.orthogonal
        (Projectivization.mk ℝ (homogeneousLift (pivotInversion cfg p q))
          (homogeneousLift_ne_zero _))
        (Projectivization.mk ℝ
          (twelveGridJOnePencilCovector hcard H a r)
          (twelveGridJOnePencilCovector_ne_zero hcard H a r))
      rw [Projectivization.orthogonal_mk]
    _ ↔ projectivePoint (pivotInversion cfg p q) ∈
        twelveGridJOneProjectivePencilLine hcard H a r := by
      rw [twelveGridJOnePencilCovector_projectivize]
    _ ↔ q ∈ lineSupport (pivotInversion cfg p)
        (twelveGridJOnePencilLine hcard H a r).1 := by
      simpa only [affinePointToProjective_eq_projectivePoint,
        mem_lineSupport] using hmem

theorem twelveGridJOneProjectivePencilLine_same_ne
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (hcard : Fintype.card Point = 12)
    (H : TwelveGridJOneInvertedLineCensus cfg p)
    (a : Fin 2) {r s : Fin 3} (hrs : r ≠ s) :
    twelveGridJOneProjectivePencilLine hcard H a r ≠
      twelveGridJOneProjectivePencilLine hcard H a s := by
  intro hline
  apply hrs
  apply twelveGridJOnePencilIndex_injective hcard H a
  apply H.fourLine.injective
  apply Subtype.ext
  apply determinedProjectiveLine_injective (pivotInversion cfg p)
  simpa [twelveGridJOneProjectivePencilLine,
    twelveGridJOnePencilLine] using hline

/-! ## Incidence exclusions of the saturated six-four grid -/

theorem twelveGridJOneExternalPoint_zero_not_mem_column
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (hcard : Fintype.card Point = 12)
    (H : TwelveGridJOneInvertedLineCensus cfg p) (s : Fin 3) :
    twelveGridJOneExternalPoint hcard H 0 ∉
      lineSupport (pivotInversion cfg p)
        (twelveGridJOnePencilLine hcard H 1 s).1 := by
  intro hmem
  have hzero : twelveGridJOnePencilIndex hcard H 1 s ∈
      sixFourBasesThrough (twelveGridJOneFourSupport H)
        (twelveGridJOneExternalPoint hcard H 0) := by
    apply mem_sixFourBasesThrough.mpr
    simpa [twelveGridJOneFourSupport,
      twelveGridJOnePencilLine] using hmem
  have hone : twelveGridJOnePencilIndex hcard H 1 s ∈
      sixFourBasesThrough (twelveGridJOneFourSupport H)
        (twelveGridJOneExternalPoint hcard H 1) := by
    apply mem_sixFourBasesThrough.mpr
    simpa [twelveGridJOneFourSupport,
      twelveGridJOnePencilLine] using
      (twelveGridJOneExternalPoint_mem_pencilLine hcard H 1 s)
  exact (Finset.disjoint_left.mp
    (sixFourExternalBases_disjoint
      (twelveGridJOneFourSupport_isSaturatedSixFour hcard H))) hzero hone

theorem twelveGridJOneExternalPoint_one_not_mem_row
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (hcard : Fintype.card Point = 12)
    (H : TwelveGridJOneInvertedLineCensus cfg p) (r : Fin 3) :
    twelveGridJOneExternalPoint hcard H 1 ∉
      lineSupport (pivotInversion cfg p)
        (twelveGridJOnePencilLine hcard H 0 r).1 := by
  intro hmem
  have hzero : twelveGridJOnePencilIndex hcard H 0 r ∈
      sixFourBasesThrough (twelveGridJOneFourSupport H)
        (twelveGridJOneExternalPoint hcard H 0) := by
    apply mem_sixFourBasesThrough.mpr
    simpa [twelveGridJOneFourSupport,
      twelveGridJOnePencilLine] using
      (twelveGridJOneExternalPoint_mem_pencilLine hcard H 0 r)
  have hone : twelveGridJOnePencilIndex hcard H 0 r ∈
      sixFourBasesThrough (twelveGridJOneFourSupport H)
        (twelveGridJOneExternalPoint hcard H 1) := by
    apply mem_sixFourBasesThrough.mpr
    simpa [twelveGridJOneFourSupport,
      twelveGridJOnePencilLine] using hmem
  exact (Finset.disjoint_left.mp
    (sixFourExternalBases_disjoint
      (twelveGridJOneFourSupport_isSaturatedSixFour hcard H))) hzero hone

theorem twelveGridJOnePencilLine_support_inter_lt_two
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (hcard : Fintype.card Point = 12)
    (H : TwelveGridJOneInvertedLineCensus cfg p)
    (a : Fin 2) {r s : Fin 3} (hrs : r ≠ s) :
    (lineSupport (pivotInversion cfg p)
      (twelveGridJOnePencilLine hcard H a r).1 ∩
      lineSupport (pivotInversion cfg p)
        (twelveGridJOnePencilLine hcard H a s).1).card < 2 := by
  let Q := pivotInversion cfg p
  have hlineNe : (twelveGridJOnePencilLine hcard H a r).1 ≠
      (twelveGridJOnePencilLine hcard H a s).1 := by
    intro hline
    apply hrs
    apply twelveGridJOnePencilIndex_injective hcard H a
    apply H.fourLine.injective
    apply Subtype.ext
    simpa [twelveGridJOnePencilLine] using hline
  let bi : GeometricBlock Q :=
    Sum.inl (twelveGridJOnePencilLine hcard H a r).1
  let bj : GeometricBlock Q :=
    Sum.inl (twelveGridJOnePencilLine hcard H a s).1
  let Li : (blockSystem Q).LineBlock := ⟨bi, rfl⟩
  let Lj : (blockSystem Q).LineBlock := ⟨bj, rfl⟩
  have hLiNe : Li ≠ Lj := by
    intro h
    apply hlineNe
    simpa [Li, Lj, bi, bj] using h
  have hinter := (blockSystem Q).distinct_line_inter_card_lt_two hLiNe
  simpa [Q, Li, Lj, bi, bj, geometricBlockSupport] using hinter

theorem twelveGridJOneGridPoint_not_mem_other_row
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (hcard : Fintype.card Point = 12)
    (H : TwelveGridJOneInvertedLineCensus cfg p)
    (r s r' : Fin 3) (hrr' : r ≠ r') :
    twelveGridJOneGridPoint hcard H r s ∉
      lineSupport (pivotInversion cfg p)
        (twelveGridJOnePencilLine hcard H 0 r').1 := by
  intro hother
  have hne := twelveGridJOneExternalPoint_ne_gridPoint hcard H 0 r s
  have hsub : ({twelveGridJOneExternalPoint hcard H 0,
      twelveGridJOneGridPoint hcard H r s} : Finset (AwayFrom p)) ⊆
      lineSupport (pivotInversion cfg p)
        (twelveGridJOnePencilLine hcard H 0 r).1 ∩
      lineSupport (pivotInversion cfg p)
        (twelveGridJOnePencilLine hcard H 0 r').1 := by
    intro q hq
    simp only [Finset.mem_insert, Finset.mem_singleton] at hq
    rcases hq with rfl | rfl
    · exact Finset.mem_inter.mpr ⟨
        twelveGridJOneExternalPoint_mem_pencilLine hcard H 0 r,
        twelveGridJOneExternalPoint_mem_pencilLine hcard H 0 r'⟩
    · exact Finset.mem_inter.mpr ⟨
        twelveGridJOneGridPoint_mem_row hcard H r s, hother⟩
  have hle := Finset.card_le_card hsub
  have hpair : ({twelveGridJOneExternalPoint hcard H 0,
      twelveGridJOneGridPoint hcard H r s} : Finset (AwayFrom p)).card = 2 :=
    Finset.card_pair hne
  rw [hpair] at hle
  have hlt := twelveGridJOnePencilLine_support_inter_lt_two hcard H 0 hrr'
  omega

theorem twelveGridJOneGridPoint_not_mem_other_column
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (hcard : Fintype.card Point = 12)
    (H : TwelveGridJOneInvertedLineCensus cfg p)
    (r s s' : Fin 3) (hss' : s ≠ s') :
    twelveGridJOneGridPoint hcard H r s ∉
      lineSupport (pivotInversion cfg p)
        (twelveGridJOnePencilLine hcard H 1 s').1 := by
  intro hother
  have hne := twelveGridJOneExternalPoint_ne_gridPoint hcard H 1 r s
  have hsub : ({twelveGridJOneExternalPoint hcard H 1,
      twelveGridJOneGridPoint hcard H r s} : Finset (AwayFrom p)) ⊆
      lineSupport (pivotInversion cfg p)
        (twelveGridJOnePencilLine hcard H 1 s).1 ∩
      lineSupport (pivotInversion cfg p)
        (twelveGridJOnePencilLine hcard H 1 s').1 := by
    intro q hq
    simp only [Finset.mem_insert, Finset.mem_singleton] at hq
    rcases hq with rfl | rfl
    · exact Finset.mem_inter.mpr ⟨
        twelveGridJOneExternalPoint_mem_pencilLine hcard H 1 s,
        twelveGridJOneExternalPoint_mem_pencilLine hcard H 1 s'⟩
    · exact Finset.mem_inter.mpr ⟨
        twelveGridJOneGridPoint_mem_column hcard H r s, hother⟩
  have hle := Finset.card_le_card hsub
  have hpair : ({twelveGridJOneExternalPoint hcard H 1,
      twelveGridJOneGridPoint hcard H r s} : Finset (AwayFrom p)).card = 2 :=
    Finset.card_pair hne
  rw [hpair] at hle
  have hlt := twelveGridJOnePencilLine_support_inter_lt_two hcard H 1 hss'
  omega

/-! ## The covector frame is derived from four actual pencil lines -/

noncomputable def twelveGridJOneFrameCovector
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (hcard : Fintype.card Point = 12)
    (H : TwelveGridJOneInvertedLineCensus cfg p) : Fin 4 → Homogeneous3
  | 0 => twelveGridJOnePencilCovector hcard H 0 0
  | 1 => twelveGridJOnePencilCovector hcard H 0 1
  | 2 => twelveGridJOnePencilCovector hcard H 1 0
  | 3 => twelveGridJOnePencilCovector hcard H 1 1

private theorem twelveGridJOnePencilCovector_det_ne_zero_of_point
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (hcard : Fintype.card Point = 12)
    (H : TwelveGridJOneInvertedLineCensus cfg p)
    (a₀ a₁ a₂ : Fin 2) (r₀ r₁ r₂ : Fin 3)
    (hline : twelveGridJOneProjectivePencilLine hcard H a₀ r₀ ≠
      twelveGridJOneProjectivePencilLine hcard H a₁ r₁)
    (q : AwayFrom p)
    (hq₀ : q ∈ lineSupport (pivotInversion cfg p)
      (twelveGridJOnePencilLine hcard H a₀ r₀).1)
    (hq₁ : q ∈ lineSupport (pivotInversion cfg p)
      (twelveGridJOnePencilLine hcard H a₁ r₁).1)
    (hq₂ : q ∉ lineSupport (pivotInversion cfg p)
      (twelveGridJOnePencilLine hcard H a₂ r₂).1) :
    Matrix.det ![twelveGridJOnePencilCovector hcard H a₀ r₀,
      twelveGridJOnePencilCovector hcard H a₁ r₁,
      twelveGridJOnePencilCovector hcard H a₂ r₂] ≠ 0 := by
  intro hdet
  obtain ⟨z, hz, hz₀, hz₁, hz₂⟩ :=
    (det_eq_zero_iff_exists_common_nonzero_homogeneous
      (twelveGridJOnePencilCovector hcard H a₀ r₀)
      (twelveGridJOnePencilCovector hcard H a₁ r₁)
      (twelveGridJOnePencilCovector hcard H a₂ r₂)).mp hdet
  let x : Homogeneous3 := homogeneousLift (pivotInversion cfg p q)
  have hx : x ≠ 0 := homogeneousLift_ne_zero _
  have hx₀ : twelveGridJOnePencilCovector hcard H a₀ r₀ ⬝ᵥ x = 0 :=
    (twelveGridJOnePencilCovector_incident_iff hcard H a₀ r₀ q).2 hq₀
  have hx₁ : twelveGridJOnePencilCovector hcard H a₁ r₁ ⬝ᵥ x = 0 :=
    (twelveGridJOnePencilCovector_incident_iff hcard H a₁ r₁ q).2 hq₁
  have hprojective :
      Projectivization.mk ℝ z hz = Projectivization.mk ℝ x hx :=
    projectiveCommonPoint_eq_of_two_distinct_covectors
      (twelveGridJOnePencilCovector_ne_zero hcard H a₀ r₀)
      (twelveGridJOnePencilCovector_ne_zero hcard H a₁ r₁) hz hx (by
        intro h
        apply hline
        simpa only [twelveGridJOnePencilCovector_projectivize] using h)
      hz₀ hz₁ hx₀ hx₁
  have horth : Projectivization.orthogonal
      (Projectivization.mk ℝ
        (twelveGridJOnePencilCovector hcard H a₂ r₂)
        (twelveGridJOnePencilCovector_ne_zero hcard H a₂ r₂))
      (Projectivization.mk ℝ z hz) :=
    (Projectivization.orthogonal_mk
      (twelveGridJOnePencilCovector_ne_zero hcard H a₂ r₂) hz).mpr hz₂
  rw [hprojective] at horth
  have hx₂ : twelveGridJOnePencilCovector hcard H a₂ r₂ ⬝ᵥ x = 0 :=
    (Projectivization.orthogonal_mk
      (twelveGridJOnePencilCovector_ne_zero hcard H a₂ r₂) hx).mp horth
  exact hq₂
    ((twelveGridJOnePencilCovector_incident_iff hcard H a₂ r₂ q).1 hx₂)

private theorem twelveGridJOne_det_rotate_rows
    (u v w : Homogeneous3) :
    Matrix.det ![u, v, w] = Matrix.det ![v, w, u] := by
  simp [Matrix.det_fin_three]
  ring

theorem twelveGridJOneFrameCovector_generalPosition
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (hcard : Fintype.card Point = 12)
    (H : TwelveGridJOneInvertedLineCensus cfg p) :
    CompleteQuadrangleGeneralPosition
      (twelveGridJOneFrameCovector hcard H 0)
      (twelveGridJOneFrameCovector hcard H 1)
      (twelveGridJOneFrameCovector hcard H 2)
      (twelveGridJOneFrameCovector hcard H 3) := by
  constructor
  · simpa [twelveGridJOneFrameCovector] using
      (twelveGridJOnePencilCovector_det_ne_zero_of_point hcard H
        0 0 1 0 1 0
        (twelveGridJOneProjectivePencilLine_same_ne hcard H 0 (by decide))
        (twelveGridJOneExternalPoint hcard H 0)
        (twelveGridJOneExternalPoint_mem_pencilLine hcard H 0 0)
        (twelveGridJOneExternalPoint_mem_pencilLine hcard H 0 1)
        (twelveGridJOneExternalPoint_zero_not_mem_column hcard H 0))
  · simpa [twelveGridJOneFrameCovector] using
      (twelveGridJOnePencilCovector_det_ne_zero_of_point hcard H
        0 0 1 0 1 1
        (twelveGridJOneProjectivePencilLine_same_ne hcard H 0 (by decide))
        (twelveGridJOneExternalPoint hcard H 0)
        (twelveGridJOneExternalPoint_mem_pencilLine hcard H 0 0)
        (twelveGridJOneExternalPoint_mem_pencilLine hcard H 0 1)
        (twelveGridJOneExternalPoint_zero_not_mem_column hcard H 1))
  · rw [twelveGridJOne_det_rotate_rows]
    simpa [twelveGridJOneFrameCovector] using
      (twelveGridJOnePencilCovector_det_ne_zero_of_point hcard H
        1 1 0 0 1 0
        (twelveGridJOneProjectivePencilLine_same_ne hcard H 1 (by decide))
        (twelveGridJOneExternalPoint hcard H 1)
        (twelveGridJOneExternalPoint_mem_pencilLine hcard H 1 0)
        (twelveGridJOneExternalPoint_mem_pencilLine hcard H 1 1)
        (twelveGridJOneExternalPoint_one_not_mem_row hcard H 0))
  · rw [twelveGridJOne_det_rotate_rows]
    simpa [twelveGridJOneFrameCovector] using
      (twelveGridJOnePencilCovector_det_ne_zero_of_point hcard H
        1 1 0 0 1 1
        (twelveGridJOneProjectivePencilLine_same_ne hcard H 1 (by decide))
        (twelveGridJOneExternalPoint hcard H 1)
        (twelveGridJOneExternalPoint_mem_pencilLine hcard H 1 0)
        (twelveGridJOneExternalPoint_mem_pencilLine hcard H 1 1)
        (twelveGridJOneExternalPoint_one_not_mem_row hcard H 1))

noncomputable def twelveGridJOneCovectorFrame
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (hcard : Fintype.card Point = 12)
    (H : TwelveGridJOneInvertedLineCensus cfg p) :
    ProjectiveCovectorFrame (twelveGridJOneFrameCovector hcard H) :=
  projectiveCovectorFrame (twelveGridJOneFrameCovector hcard H)
    (twelveGridJOneFrameCovector_generalPosition hcard H)

/-! ## The derived affine chart -/

/-- Apply the canonical JOne frame and the fixed affine post-chart to a
homogeneous point. -/
noncomputable def twelveGridJOneAffineHomogeneous
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (hcard : Fintype.card Point = 12)
    (H : TwelveGridJOneInvertedLineCensus cfg p) (x : Homogeneous3) :
    Homogeneous3 :=
  twelveGridAffinePostPointMatrix *ᵥ
    projectivePointTransform (twelveGridJOneCovectorFrame hcard H).G x

/-- The matching contragredient map on a raw line covector. -/
noncomputable def twelveGridJOneAffineCovector
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (hcard : Fintype.card Point = 12)
    (H : TwelveGridJOneInvertedLineCensus cfg p) (ell : Homogeneous3) :
    Homogeneous3 :=
  twelveGridAffinePostCovectorMatrix *ᵥ
    projectiveCovectorTransform (twelveGridJOneCovectorFrame hcard H).G ell

theorem twelveGridJOneAffineCovector_dot
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (hcard : Fintype.card Point = 12)
    (H : TwelveGridJOneInvertedLineCensus cfg p)
    (ell x : Homogeneous3) :
    twelveGridJOneAffineCovector hcard H ell ⬝ᵥ
        twelveGridJOneAffineHomogeneous hcard H x = ell ⬝ᵥ x := by
  unfold twelveGridJOneAffineCovector twelveGridJOneAffineHomogeneous
  rw [twelveGridAffinePost_dot,
    projectiveCovectorTransform_dot_pointTransform]

/-- The four actual frame lines acquire the displayed affine equations. -/
theorem twelveGridJOneAffineCovector_frame
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (hcard : Fintype.card Point = 12)
    (H : TwelveGridJOneInvertedLineCensus cfg p) (i : Fin 4) :
    twelveGridJOneAffineCovector hcard H
      (twelveGridJOneFrameCovector hcard H i) =
      ((twelveGridJOneCovectorFrame hcard H).scale i *
        twelveGridAffineFrameScale i) • twelveGridAffineFrameCovector i := by
  let F := twelveGridJOneCovectorFrame hcard H
  change twelveGridAffinePostCovectorMatrix *ᵥ
      projectiveCovectorTransform F.G
        (twelveGridJOneFrameCovector hcard H i) = _
  calc
    twelveGridAffinePostCovectorMatrix *ᵥ
        projectiveCovectorTransform F.G
          (twelveGridJOneFrameCovector hcard H i) =
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

noncomputable def twelveGridJOneAffinePoint
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (hcard : Fintype.card Point = 12)
    (H : TwelveGridJOneInvertedLineCensus cfg p) (q : AwayFrom p) :
    Homogeneous3 :=
  twelveGridJOneAffineHomogeneous hcard H
    (homogeneousLift (pivotInversion cfg p q))

noncomputable def twelveGridJOneAffinePencilCovector
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (hcard : Fintype.card Point = 12)
    (H : TwelveGridJOneInvertedLineCensus cfg p)
    (a : Fin 2) (r : Fin 3) : Homogeneous3 :=
  twelveGridJOneAffineCovector hcard H
    (twelveGridJOnePencilCovector hcard H a r)

theorem twelveGridJOneAffineHomogeneous_ne_zero
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (hcard : Fintype.card Point = 12)
    (H : TwelveGridJOneInvertedLineCensus cfg p)
    (x : Homogeneous3) (hx : x ≠ 0) :
    twelveGridJOneAffineHomogeneous hcard H x ≠ 0 := by
  intro hzero
  have hbefore : projectivePointTransform
      (twelveGridJOneCovectorFrame hcard H).G x = 0 := by
    apply twelveGridAffinePostPoint_injective
    simpa [twelveGridJOneAffineHomogeneous] using hzero
  have hbefore_ne : projectivePointTransform
      (twelveGridJOneCovectorFrame hcard H).G x ≠ 0 := by
    simpa [projectivePointTransform] using
      ((smul_ne_zero_iff_ne (twelveGridJOneCovectorFrame hcard H).G).mpr hx)
  exact hbefore_ne hbefore

theorem twelveGridJOneAffinePoint_ne_zero
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (hcard : Fintype.card Point = 12)
    (H : TwelveGridJOneInvertedLineCensus cfg p) (q : AwayFrom p) :
    twelveGridJOneAffinePoint hcard H q ≠ 0 := by
  unfold twelveGridJOneAffinePoint
  exact twelveGridJOneAffineHomogeneous_ne_zero hcard H _
    (homogeneousLift_ne_zero _)

theorem twelveGridJOneAffinePencilCovector_incident_iff
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (hcard : Fintype.card Point = 12)
    (H : TwelveGridJOneInvertedLineCensus cfg p)
    (a : Fin 2) (r : Fin 3) (q : AwayFrom p) :
    twelveGridJOneAffinePencilCovector hcard H a r ⬝ᵥ
        twelveGridJOneAffinePoint hcard H q = 0 ↔
      q ∈ lineSupport (pivotInversion cfg p)
        (twelveGridJOnePencilLine hcard H a r).1 := by
  change twelveGridJOneAffineCovector hcard H
      (twelveGridJOnePencilCovector hcard H a r) ⬝ᵥ
      twelveGridJOneAffineHomogeneous hcard H
        (homogeneousLift (pivotInversion cfg p q)) = 0 ↔ _
  rw [twelveGridJOneAffineCovector_dot,
    twelveGridJOnePencilCovector_incident_iff]

noncomputable def twelveGridJOneAffineFrameScale
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (hcard : Fintype.card Point = 12)
    (H : TwelveGridJOneInvertedLineCensus cfg p) (i : Fin 4) : ℝ :=
  (twelveGridJOneCovectorFrame hcard H).scale i *
    twelveGridAffineFrameScale i

theorem twelveGridJOneAffineFrameScale_ne_zero
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (hcard : Fintype.card Point = 12)
    (H : TwelveGridJOneInvertedLineCensus cfg p) (i : Fin 4) :
    twelveGridJOneAffineFrameScale hcard H i ≠ 0 := by
  exact mul_ne_zero ((twelveGridJOneCovectorFrame hcard H).scale_ne_zero i)
    (twelveGridAffineFrameScale_ne_zero i)

theorem twelveGridJOneAffinePencilCovector_zero_zero
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (hcard : Fintype.card Point = 12)
    (H : TwelveGridJOneInvertedLineCensus cfg p) :
    twelveGridJOneAffinePencilCovector hcard H 0 0 =
      twelveGridJOneAffineFrameScale hcard H 0 • (![1, 0, 1] : Homogeneous3) := by
  simpa [twelveGridJOneAffinePencilCovector,
    twelveGridJOneFrameCovector, twelveGridJOneAffineFrameScale,
    twelveGridAffineFrameCovector, twelveGridAffineFrameScale] using
    (twelveGridJOneAffineCovector_frame hcard H (0 : Fin 4))

theorem twelveGridJOneAffinePencilCovector_zero_one
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (hcard : Fintype.card Point = 12)
    (H : TwelveGridJOneInvertedLineCensus cfg p) :
    twelveGridJOneAffinePencilCovector hcard H 0 1 =
      twelveGridJOneAffineFrameScale hcard H 1 • (![1, 0, 0] : Homogeneous3) := by
  simpa [twelveGridJOneAffinePencilCovector,
    twelveGridJOneFrameCovector, twelveGridJOneAffineFrameScale,
    twelveGridAffineFrameCovector, twelveGridAffineFrameScale] using
    (twelveGridJOneAffineCovector_frame hcard H (1 : Fin 4))

theorem twelveGridJOneAffinePencilCovector_one_zero
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (hcard : Fintype.card Point = 12)
    (H : TwelveGridJOneInvertedLineCensus cfg p) :
    twelveGridJOneAffinePencilCovector hcard H 1 0 =
      twelveGridJOneAffineFrameScale hcard H 2 • (![0, 1, 1] : Homogeneous3) := by
  simpa [twelveGridJOneAffinePencilCovector,
    twelveGridJOneFrameCovector, twelveGridJOneAffineFrameScale,
    twelveGridAffineFrameCovector, twelveGridAffineFrameScale] using
    (twelveGridJOneAffineCovector_frame hcard H (2 : Fin 4))

theorem twelveGridJOneAffinePencilCovector_one_one
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (hcard : Fintype.card Point = 12)
    (H : TwelveGridJOneInvertedLineCensus cfg p) :
    twelveGridJOneAffinePencilCovector hcard H 1 1 =
      twelveGridJOneAffineFrameScale hcard H 3 • (![0, 1, 0] : Homogeneous3) := by
  simpa [twelveGridJOneAffinePencilCovector,
    twelveGridJOneFrameCovector, twelveGridJOneAffineFrameScale,
    twelveGridAffineFrameCovector, twelveGridAffineFrameScale] using
    (twelveGridJOneAffineCovector_frame hcard H (3 : Fin 4))

private theorem twelveGridJOne_smul_covector_dot_eq_zero_iff
    {c : ℝ} (hc : c ≠ 0) (ell x : Homogeneous3) :
    (c • ell) ⬝ᵥ x = 0 ↔ ell ⬝ᵥ x = 0 := by
  rw [smul_dotProduct, smul_eq_mul]
  constructor
  · intro h
    exact (mul_eq_zero.mp h).resolve_left hc
  · intro h
    rw [h, mul_zero]

/-! ### The pencil centres are the two ideal points of the derived chart -/

theorem twelveGridJOneAffineExternal_zero_apply_zero
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (hcard : Fintype.card Point = 12)
    (H : TwelveGridJOneInvertedLineCensus cfg p) :
    twelveGridJOneAffinePoint hcard H
      (twelveGridJOneExternalPoint hcard H 0) 0 = 0 := by
  have hinc := (twelveGridJOneAffinePencilCovector_incident_iff
    hcard H 0 1 (twelveGridJOneExternalPoint hcard H 0)).2
      (twelveGridJOneExternalPoint_mem_pencilLine hcard H 0 1)
  rw [twelveGridJOneAffinePencilCovector_zero_one] at hinc
  have hdot : (![1, 0, 0] : Homogeneous3) ⬝ᵥ
      twelveGridJOneAffinePoint hcard H
        (twelveGridJOneExternalPoint hcard H 0) = 0 :=
    (twelveGridJOne_smul_covector_dot_eq_zero_iff
      (twelveGridJOneAffineFrameScale_ne_zero hcard H 1)
      _ _).mp hinc
  simpa [dotProduct, Fin.sum_univ_three] using hdot

theorem twelveGridJOneAffineExternal_zero_apply_two
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (hcard : Fintype.card Point = 12)
    (H : TwelveGridJOneInvertedLineCensus cfg p) :
    twelveGridJOneAffinePoint hcard H
      (twelveGridJOneExternalPoint hcard H 0) 2 = 0 := by
  have hinc := (twelveGridJOneAffinePencilCovector_incident_iff
    hcard H 0 0 (twelveGridJOneExternalPoint hcard H 0)).2
      (twelveGridJOneExternalPoint_mem_pencilLine hcard H 0 0)
  rw [twelveGridJOneAffinePencilCovector_zero_zero] at hinc
  have hdot : (![1, 0, 1] : Homogeneous3) ⬝ᵥ
      twelveGridJOneAffinePoint hcard H
        (twelveGridJOneExternalPoint hcard H 0) = 0 :=
    (twelveGridJOne_smul_covector_dot_eq_zero_iff
      (twelveGridJOneAffineFrameScale_ne_zero hcard H 0)
      _ _).mp hinc
  have hsum : twelveGridJOneAffinePoint hcard H
      (twelveGridJOneExternalPoint hcard H 0) 0 +
      twelveGridJOneAffinePoint hcard H
        (twelveGridJOneExternalPoint hcard H 0) 2 = 0 := by
    simpa [dotProduct, Fin.sum_univ_three] using hdot
  linarith [hsum, twelveGridJOneAffineExternal_zero_apply_zero hcard H]

theorem twelveGridJOneAffineExternal_zero_apply_one_ne_zero
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (hcard : Fintype.card Point = 12)
    (H : TwelveGridJOneInvertedLineCensus cfg p) :
    twelveGridJOneAffinePoint hcard H
      (twelveGridJOneExternalPoint hcard H 0) 1 ≠ 0 := by
  intro hzero
  apply twelveGridJOneAffinePoint_ne_zero hcard H
    (twelveGridJOneExternalPoint hcard H 0)
  ext i
  fin_cases i <;>
    simp [twelveGridJOneAffineExternal_zero_apply_zero hcard H,
      twelveGridJOneAffineExternal_zero_apply_two hcard H, hzero]

theorem twelveGridJOneAffineExternal_one_apply_one
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (hcard : Fintype.card Point = 12)
    (H : TwelveGridJOneInvertedLineCensus cfg p) :
    twelveGridJOneAffinePoint hcard H
      (twelveGridJOneExternalPoint hcard H 1) 1 = 0 := by
  have hinc := (twelveGridJOneAffinePencilCovector_incident_iff
    hcard H 1 1 (twelveGridJOneExternalPoint hcard H 1)).2
      (twelveGridJOneExternalPoint_mem_pencilLine hcard H 1 1)
  rw [twelveGridJOneAffinePencilCovector_one_one] at hinc
  have hdot : (![0, 1, 0] : Homogeneous3) ⬝ᵥ
      twelveGridJOneAffinePoint hcard H
        (twelveGridJOneExternalPoint hcard H 1) = 0 :=
    (twelveGridJOne_smul_covector_dot_eq_zero_iff
      (twelveGridJOneAffineFrameScale_ne_zero hcard H 3)
      _ _).mp hinc
  simpa [dotProduct, Fin.sum_univ_three] using hdot

theorem twelveGridJOneAffineExternal_one_apply_two
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (hcard : Fintype.card Point = 12)
    (H : TwelveGridJOneInvertedLineCensus cfg p) :
    twelveGridJOneAffinePoint hcard H
      (twelveGridJOneExternalPoint hcard H 1) 2 = 0 := by
  have hinc := (twelveGridJOneAffinePencilCovector_incident_iff
    hcard H 1 0 (twelveGridJOneExternalPoint hcard H 1)).2
      (twelveGridJOneExternalPoint_mem_pencilLine hcard H 1 0)
  rw [twelveGridJOneAffinePencilCovector_one_zero] at hinc
  have hdot : (![0, 1, 1] : Homogeneous3) ⬝ᵥ
      twelveGridJOneAffinePoint hcard H
        (twelveGridJOneExternalPoint hcard H 1) = 0 :=
    (twelveGridJOne_smul_covector_dot_eq_zero_iff
      (twelveGridJOneAffineFrameScale_ne_zero hcard H 2)
      _ _).mp hinc
  have hsum : twelveGridJOneAffinePoint hcard H
      (twelveGridJOneExternalPoint hcard H 1) 1 +
      twelveGridJOneAffinePoint hcard H
        (twelveGridJOneExternalPoint hcard H 1) 2 = 0 := by
    simpa [dotProduct, Fin.sum_univ_three] using hdot
  linarith [hsum, twelveGridJOneAffineExternal_one_apply_one hcard H]

theorem twelveGridJOneAffineExternal_one_apply_zero_ne_zero
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (hcard : Fintype.card Point = 12)
    (H : TwelveGridJOneInvertedLineCensus cfg p) :
    twelveGridJOneAffinePoint hcard H
      (twelveGridJOneExternalPoint hcard H 1) 0 ≠ 0 := by
  intro hzero
  apply twelveGridJOneAffinePoint_ne_zero hcard H
    (twelveGridJOneExternalPoint hcard H 1)
  ext i
  fin_cases i <;>
    simp [twelveGridJOneAffineExternal_one_apply_one hcard H,
      twelveGridJOneAffineExternal_one_apply_two hcard H, hzero]

/-! ### All pencil members have a one-coordinate affine equation -/

theorem twelveGridJOneAffinePencilCovector_zero_apply_one
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (hcard : Fintype.card Point = 12)
    (H : TwelveGridJOneInvertedLineCensus cfg p) (r : Fin 3) :
    twelveGridJOneAffinePencilCovector hcard H 0 r 1 = 0 := by
  have hinc := (twelveGridJOneAffinePencilCovector_incident_iff
    hcard H 0 r (twelveGridJOneExternalPoint hcard H 0)).2
      (twelveGridJOneExternalPoint_mem_pencilLine hcard H 0 r)
  have hprod : twelveGridJOneAffinePencilCovector hcard H 0 r 1 *
      twelveGridJOneAffinePoint hcard H
        (twelveGridJOneExternalPoint hcard H 0) 1 = 0 := by
    simpa [dotProduct, Fin.sum_univ_three,
      twelveGridJOneAffineExternal_zero_apply_zero hcard H,
      twelveGridJOneAffineExternal_zero_apply_two hcard H] using hinc
  exact (mul_eq_zero.mp hprod).resolve_right
    (twelveGridJOneAffineExternal_zero_apply_one_ne_zero hcard H)

theorem twelveGridJOneAffinePencilCovector_zero_apply_zero_ne_zero
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (hcard : Fintype.card Point = 12)
    (H : TwelveGridJOneInvertedLineCensus cfg p) (r : Fin 3) :
    twelveGridJOneAffinePencilCovector hcard H 0 r 0 ≠ 0 := by
  intro hzero
  have hinc : twelveGridJOneAffinePencilCovector hcard H 0 r ⬝ᵥ
      twelveGridJOneAffinePoint hcard H
        (twelveGridJOneExternalPoint hcard H 1) = 0 := by
    simp [dotProduct, Fin.sum_univ_three, hzero,
      twelveGridJOneAffinePencilCovector_zero_apply_one hcard H r,
      twelveGridJOneAffineExternal_one_apply_one hcard H,
      twelveGridJOneAffineExternal_one_apply_two hcard H]
  apply twelveGridJOneExternalPoint_one_not_mem_row hcard H r
  exact (twelveGridJOneAffinePencilCovector_incident_iff
    hcard H 0 r (twelveGridJOneExternalPoint hcard H 1)).1 hinc

theorem twelveGridJOneAffinePencilCovector_one_apply_zero
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (hcard : Fintype.card Point = 12)
    (H : TwelveGridJOneInvertedLineCensus cfg p) (s : Fin 3) :
    twelveGridJOneAffinePencilCovector hcard H 1 s 0 = 0 := by
  have hinc := (twelveGridJOneAffinePencilCovector_incident_iff
    hcard H 1 s (twelveGridJOneExternalPoint hcard H 1)).2
      (twelveGridJOneExternalPoint_mem_pencilLine hcard H 1 s)
  have hprod : twelveGridJOneAffinePencilCovector hcard H 1 s 0 *
      twelveGridJOneAffinePoint hcard H
        (twelveGridJOneExternalPoint hcard H 1) 0 = 0 := by
    simpa [dotProduct, Fin.sum_univ_three,
      twelveGridJOneAffineExternal_one_apply_one hcard H,
      twelveGridJOneAffineExternal_one_apply_two hcard H] using hinc
  exact (mul_eq_zero.mp hprod).resolve_right
    (twelveGridJOneAffineExternal_one_apply_zero_ne_zero hcard H)

theorem twelveGridJOneAffinePencilCovector_one_apply_one_ne_zero
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (hcard : Fintype.card Point = 12)
    (H : TwelveGridJOneInvertedLineCensus cfg p) (s : Fin 3) :
    twelveGridJOneAffinePencilCovector hcard H 1 s 1 ≠ 0 := by
  intro hzero
  have hinc : twelveGridJOneAffinePencilCovector hcard H 1 s ⬝ᵥ
      twelveGridJOneAffinePoint hcard H
        (twelveGridJOneExternalPoint hcard H 0) = 0 := by
    simp [dotProduct, Fin.sum_univ_three, hzero,
      twelveGridJOneAffinePencilCovector_one_apply_zero hcard H s,
      twelveGridJOneAffineExternal_zero_apply_zero hcard H,
      twelveGridJOneAffineExternal_zero_apply_two hcard H]
  apply twelveGridJOneExternalPoint_zero_not_mem_column hcard H s
  exact (twelveGridJOneAffinePencilCovector_incident_iff
    hcard H 1 s (twelveGridJOneExternalPoint hcard H 0)).1 hinc

/-! ### The two remaining projective parameters -/

noncomputable def twelveGridJOneColumnCoordinate
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (hcard : Fintype.card Point = 12)
    (H : TwelveGridJOneInvertedLineCensus cfg p) (r : Fin 3) : ℝ :=
  -(twelveGridJOneAffinePencilCovector hcard H 0 r 2 /
    twelveGridJOneAffinePencilCovector hcard H 0 r 0)

noncomputable def twelveGridJOneRowCoordinate
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (hcard : Fintype.card Point = 12)
    (H : TwelveGridJOneInvertedLineCensus cfg p) (s : Fin 3) : ℝ :=
  -(twelveGridJOneAffinePencilCovector hcard H 1 s 2 /
    twelveGridJOneAffinePencilCovector hcard H 1 s 1)

theorem twelveGridJOneAffinePencilCovector_zero_normal_form
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (hcard : Fintype.card Point = 12)
    (H : TwelveGridJOneInvertedLineCensus cfg p) (r : Fin 3) :
    twelveGridJOneAffinePencilCovector hcard H 0 r =
      twelveGridJOneAffinePencilCovector hcard H 0 r 0 •
        (![1, 0, -twelveGridJOneColumnCoordinate hcard H r] : Homogeneous3) := by
  ext i
  fin_cases i
  · simp
  · simp [twelveGridJOneAffinePencilCovector_zero_apply_one hcard H r]
  · have hne := twelveGridJOneAffinePencilCovector_zero_apply_zero_ne_zero
        hcard H r
    simp [twelveGridJOneColumnCoordinate]
    field_simp [hne]

theorem twelveGridJOneAffinePencilCovector_one_normal_form
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (hcard : Fintype.card Point = 12)
    (H : TwelveGridJOneInvertedLineCensus cfg p) (s : Fin 3) :
    twelveGridJOneAffinePencilCovector hcard H 1 s =
      twelveGridJOneAffinePencilCovector hcard H 1 s 1 •
        (![0, 1, -twelveGridJOneRowCoordinate hcard H s] : Homogeneous3) := by
  ext i
  fin_cases i
  · simp [twelveGridJOneAffinePencilCovector_one_apply_zero hcard H s]
  · simp
  · have hne := twelveGridJOneAffinePencilCovector_one_apply_one_ne_zero
        hcard H s
    simp [twelveGridJOneRowCoordinate]
    field_simp [hne]

theorem twelveGridJOneColumnCoordinate_zero
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (hcard : Fintype.card Point = 12)
    (H : TwelveGridJOneInvertedLineCensus cfg p) :
    twelveGridJOneColumnCoordinate hcard H 0 = -1 := by
  unfold twelveGridJOneColumnCoordinate
  rw [twelveGridJOneAffinePencilCovector_zero_zero]
  simp [twelveGridJOneAffineFrameScale_ne_zero hcard H 0]

theorem twelveGridJOneColumnCoordinate_one
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (hcard : Fintype.card Point = 12)
    (H : TwelveGridJOneInvertedLineCensus cfg p) :
    twelveGridJOneColumnCoordinate hcard H 1 = 0 := by
  unfold twelveGridJOneColumnCoordinate
  rw [twelveGridJOneAffinePencilCovector_zero_one]
  simp

theorem twelveGridJOneRowCoordinate_zero
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (hcard : Fintype.card Point = 12)
    (H : TwelveGridJOneInvertedLineCensus cfg p) :
    twelveGridJOneRowCoordinate hcard H 0 = -1 := by
  unfold twelveGridJOneRowCoordinate
  rw [twelveGridJOneAffinePencilCovector_one_zero]
  simp [twelveGridJOneAffineFrameScale_ne_zero hcard H 2]

theorem twelveGridJOneRowCoordinate_one
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (hcard : Fintype.card Point = 12)
    (H : TwelveGridJOneInvertedLineCensus cfg p) :
    twelveGridJOneRowCoordinate hcard H 1 = 0 := by
  unfold twelveGridJOneRowCoordinate
  rw [twelveGridJOneAffinePencilCovector_one_one]
  simp

noncomputable def twelveGridJOneColumnParameter
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (hcard : Fintype.card Point = 12)
    (H : TwelveGridJOneInvertedLineCensus cfg p) : ℝ :=
  twelveGridJOneColumnCoordinate hcard H 2

noncomputable def twelveGridJOneRowParameter
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (hcard : Fintype.card Point = 12)
    (H : TwelveGridJOneInvertedLineCensus cfg p) : ℝ :=
  twelveGridJOneRowCoordinate hcard H 2

theorem twelveGridJOneColumnCoordinate_eq_parameter
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (hcard : Fintype.card Point = 12)
    (H : TwelveGridJOneInvertedLineCensus cfg p) (r : Fin 3) :
    twelveGridJOneColumnCoordinate hcard H r =
      threeByThreePencilCoordinate (twelveGridJOneColumnParameter hcard H) r := by
  fin_cases r
  · simpa [threeByThreePencilCoordinate] using
      twelveGridJOneColumnCoordinate_zero hcard H
  · simpa [threeByThreePencilCoordinate] using
      twelveGridJOneColumnCoordinate_one hcard H
  · simp [twelveGridJOneColumnParameter, threeByThreePencilCoordinate]

theorem twelveGridJOneRowCoordinate_eq_parameter
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (hcard : Fintype.card Point = 12)
    (H : TwelveGridJOneInvertedLineCensus cfg p) (s : Fin 3) :
    twelveGridJOneRowCoordinate hcard H s =
      threeByThreePencilCoordinate (twelveGridJOneRowParameter hcard H) s := by
  fin_cases s
  · simpa [threeByThreePencilCoordinate] using
      twelveGridJOneRowCoordinate_zero hcard H
  · simpa [threeByThreePencilCoordinate] using
      twelveGridJOneRowCoordinate_one hcard H
  · simp [twelveGridJOneRowParameter, threeByThreePencilCoordinate]

/-! ### The nine labelled grid crossings in the derived chart -/

theorem twelveGridJOneAffineGridPoint_apply_two
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (hcard : Fintype.card Point = 12)
    (H : TwelveGridJOneInvertedLineCensus cfg p) (r s : Fin 3) :
    twelveGridJOneAffinePoint hcard H
      (twelveGridJOneGridPoint hcard H r s) 2 ≠ 0 := by
  intro htwo
  have hx := (twelveGridJOneAffinePencilCovector_incident_iff
    hcard H 0 r (twelveGridJOneGridPoint hcard H r s)).2
      (twelveGridJOneGridPoint_mem_row hcard H r s)
  have hy := (twelveGridJOneAffinePencilCovector_incident_iff
    hcard H 1 s (twelveGridJOneGridPoint hcard H r s)).2
      (twelveGridJOneGridPoint_mem_column hcard H r s)
  rw [twelveGridJOneAffinePencilCovector_zero_normal_form] at hx
  rw [twelveGridJOneAffinePencilCovector_one_normal_form] at hy
  have hxeq : twelveGridJOneAffinePoint hcard H
      (twelveGridJOneGridPoint hcard H r s) 0 = 0 := by
    have hraw : (![1, 0,
        -twelveGridJOneColumnCoordinate hcard H r] : Homogeneous3) ⬝ᵥ
        twelveGridJOneAffinePoint hcard H
          (twelveGridJOneGridPoint hcard H r s) = 0 :=
      (twelveGridJOne_smul_covector_dot_eq_zero_iff
        (twelveGridJOneAffinePencilCovector_zero_apply_zero_ne_zero hcard H r)
        _ _).mp hx
    simpa [dotProduct, Fin.sum_univ_three, htwo] using hraw
  have hyeq : twelveGridJOneAffinePoint hcard H
      (twelveGridJOneGridPoint hcard H r s) 1 = 0 := by
    have hraw : (![0, 1,
        -twelveGridJOneRowCoordinate hcard H s] : Homogeneous3) ⬝ᵥ
        twelveGridJOneAffinePoint hcard H
          (twelveGridJOneGridPoint hcard H r s) = 0 :=
      (twelveGridJOne_smul_covector_dot_eq_zero_iff
        (twelveGridJOneAffinePencilCovector_one_apply_one_ne_zero hcard H s)
        _ _).mp hy
    simpa [dotProduct, Fin.sum_univ_three, htwo] using hraw
  apply twelveGridJOneAffinePoint_ne_zero hcard H
    (twelveGridJOneGridPoint hcard H r s)
  ext i
  fin_cases i <;> simp [hxeq, hyeq, htwo]

noncomputable def twelveGridJOneAffineGridCoordinate
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (hcard : Fintype.card Point = 12)
    (H : TwelveGridJOneInvertedLineCensus cfg p) (r s : Fin 3) : ℝ × ℝ :=
  (twelveGridJOneAffinePoint hcard H
      (twelveGridJOneGridPoint hcard H r s) 0 /
      twelveGridJOneAffinePoint hcard H
        (twelveGridJOneGridPoint hcard H r s) 2,
    twelveGridJOneAffinePoint hcard H
      (twelveGridJOneGridPoint hcard H r s) 1 /
      twelveGridJOneAffinePoint hcard H
        (twelveGridJOneGridPoint hcard H r s) 2)

theorem twelveGridJOneAffineGridCoordinate_eq
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (hcard : Fintype.card Point = 12)
    (H : TwelveGridJOneInvertedLineCensus cfg p) (r s : Fin 3) :
    twelveGridJOneAffineGridCoordinate hcard H r s =
      (twelveGridJOneColumnCoordinate hcard H r,
        twelveGridJOneRowCoordinate hcard H s) := by
  apply Prod.ext
  · unfold twelveGridJOneAffineGridCoordinate
    have hinc := (twelveGridJOneAffinePencilCovector_incident_iff
      hcard H 0 r (twelveGridJOneGridPoint hcard H r s)).2
        (twelveGridJOneGridPoint_mem_row hcard H r s)
    rw [twelveGridJOneAffinePencilCovector_zero_normal_form] at hinc
    have hraw : (![1, 0,
        -twelveGridJOneColumnCoordinate hcard H r] : Homogeneous3) ⬝ᵥ
        twelveGridJOneAffinePoint hcard H
          (twelveGridJOneGridPoint hcard H r s) = 0 :=
      (twelveGridJOne_smul_covector_dot_eq_zero_iff
        (twelveGridJOneAffinePencilCovector_zero_apply_zero_ne_zero hcard H r)
        _ _).mp hinc
    have hne := twelveGridJOneAffineGridPoint_apply_two hcard H r s
    simp [dotProduct, Fin.sum_univ_three] at hraw
    field_simp [hne]
    linarith
  · unfold twelveGridJOneAffineGridCoordinate
    have hinc := (twelveGridJOneAffinePencilCovector_incident_iff
      hcard H 1 s (twelveGridJOneGridPoint hcard H r s)).2
        (twelveGridJOneGridPoint_mem_column hcard H r s)
    rw [twelveGridJOneAffinePencilCovector_one_normal_form] at hinc
    have hraw : (![0, 1,
        -twelveGridJOneRowCoordinate hcard H s] : Homogeneous3) ⬝ᵥ
        twelveGridJOneAffinePoint hcard H
          (twelveGridJOneGridPoint hcard H r s) = 0 :=
      (twelveGridJOne_smul_covector_dot_eq_zero_iff
        (twelveGridJOneAffinePencilCovector_one_apply_one_ne_zero hcard H s)
        _ _).mp hinc
    have hne := twelveGridJOneAffineGridPoint_apply_two hcard H r s
    simp [dotProduct, Fin.sum_univ_three] at hraw
    field_simp [hne]
    linarith

theorem twelveGridJOneAffineGridCoordinate_parameterized
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (hcard : Fintype.card Point = 12)
    (H : TwelveGridJOneInvertedLineCensus cfg p) (r s : Fin 3) :
    twelveGridJOneAffineGridCoordinate hcard H r s =
      threeByThreeParameterizedGridPoint
        (twelveGridJOneColumnParameter hcard H)
        (twelveGridJOneRowParameter hcard H) (r, s) := by
  rw [twelveGridJOneAffineGridCoordinate_eq]
  simp only [threeByThreeParameterizedGridPoint]
  rw [twelveGridJOneColumnCoordinate_eq_parameter,
    twelveGridJOneRowCoordinate_eq_parameter]

/-! ### Finite labels and arbitrary actual lines -/

def TwelveGridJOneAffineFinite
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (hcard : Fintype.card Point = 12)
    (H : TwelveGridJOneInvertedLineCensus cfg p) (q : AwayFrom p) : Prop :=
  twelveGridJOneAffinePoint hcard H q 2 ≠ 0

noncomputable def twelveGridJOneAffineCoordinate
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (hcard : Fintype.card Point = 12)
    (H : TwelveGridJOneInvertedLineCensus cfg p)
    (q : {q : AwayFrom p // TwelveGridJOneAffineFinite hcard H q}) : ℝ × ℝ :=
  (twelveGridJOneAffinePoint hcard H q.1 0 /
      twelveGridJOneAffinePoint hcard H q.1 2,
    twelveGridJOneAffinePoint hcard H q.1 1 /
      twelveGridJOneAffinePoint hcard H q.1 2)

noncomputable def twelveGridJOneAffineGridLabel
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (hcard : Fintype.card Point = 12)
    (H : TwelveGridJOneInvertedLineCensus cfg p) (rs : Fin 3 × Fin 3) :
    {q : AwayFrom p // TwelveGridJOneAffineFinite hcard H q} :=
  ⟨twelveGridJOneGridPoint hcard H rs.1 rs.2,
    twelveGridJOneAffineGridPoint_apply_two hcard H rs.1 rs.2⟩

theorem twelveGridJOneAffineGridLabel_coordinate
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (hcard : Fintype.card Point = 12)
    (H : TwelveGridJOneInvertedLineCensus cfg p) (rs : Fin 3 × Fin 3) :
    twelveGridJOneAffineCoordinate hcard H
      (twelveGridJOneAffineGridLabel hcard H rs) =
      threeByThreeParameterizedGridPoint
        (twelveGridJOneColumnParameter hcard H)
        (twelveGridJOneRowParameter hcard H) rs := by
  rcases rs with ⟨r, s⟩
  exact twelveGridJOneAffineGridCoordinate_parameterized hcard H r s

theorem twelveGridJOneAffinePoint_eq_scale_homogeneousLift
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (hcard : Fintype.card Point = 12)
    (H : TwelveGridJOneInvertedLineCensus cfg p)
    (q : {q : AwayFrom p // TwelveGridJOneAffineFinite hcard H q}) :
    twelveGridJOneAffinePoint hcard H q.1 =
      twelveGridJOneAffinePoint hcard H q.1 2 •
        homogeneousLift
          (twelveGridAffinePairPoint2
            (twelveGridJOneAffineCoordinate hcard H q)) := by
  ext i
  fin_cases i
  · simp [homogeneousLift, twelveGridJOneAffineCoordinate,
      twelveGridAffinePairPoint2]
    rw [mul_comm, div_mul_cancel₀ _ q.2]
  · simp [homogeneousLift, twelveGridJOneAffineCoordinate,
      twelveGridAffinePairPoint2]
    rw [mul_comm, div_mul_cancel₀ _ q.2]
  · simp [homogeneousLift, twelveGridAffinePairPoint2]

noncomputable def twelveGridJOneLineCovector
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (hcard : Fintype.card Point = 12)
    (H : TwelveGridJOneInvertedLineCensus cfg p)
    (L : DeterminedLine (pivotInversion cfg p)) : Homogeneous3 :=
  (determinedProjectiveLine (pivotInversion cfg p) L).rep

theorem twelveGridJOneLineCovector_ne_zero
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (hcard : Fintype.card Point = 12)
    (H : TwelveGridJOneInvertedLineCensus cfg p)
    (L : DeterminedLine (pivotInversion cfg p)) :
    twelveGridJOneLineCovector hcard H L ≠ 0 := by
  simpa [twelveGridJOneLineCovector] using
    (determinedProjectiveLine (pivotInversion cfg p) L).rep_nonzero

theorem twelveGridJOneLineCovector_incident_iff
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (hcard : Fintype.card Point = 12)
    (H : TwelveGridJOneInvertedLineCensus cfg p)
    (L : DeterminedLine (pivotInversion cfg p)) (q : AwayFrom p) :
    twelveGridJOneLineCovector hcard H L ⬝ᵥ
        homogeneousLift (pivotInversion cfg p q) = 0 ↔
      q ∈ lineSupport (pivotInversion cfg p) L := by
  have hmem := affinePoint_mem_determinedProjectiveLine_iff
    (pivotInversion cfg p) q L
  calc
    twelveGridJOneLineCovector hcard H L ⬝ᵥ
        homogeneousLift (pivotInversion cfg p q) = 0 ↔
      homogeneousLift (pivotInversion cfg p q) ⬝ᵥ
          twelveGridJOneLineCovector hcard H L = 0 := by
        constructor
        · intro h
          calc
            homogeneousLift (pivotInversion cfg p q) ⬝ᵥ
                twelveGridJOneLineCovector hcard H L =
                twelveGridJOneLineCovector hcard H L ⬝ᵥ
                  homogeneousLift (pivotInversion cfg p q) := dotProduct_comm _ _
            _ = 0 := h
        · intro h
          calc
            twelveGridJOneLineCovector hcard H L ⬝ᵥ
                homogeneousLift (pivotInversion cfg p q) =
                homogeneousLift (pivotInversion cfg p q) ⬝ᵥ
                  twelveGridJOneLineCovector hcard H L := dotProduct_comm _ _
            _ = 0 := h
    _ ↔ projectivePoint (pivotInversion cfg p q) ∈
        Projectivization.mk ℝ (twelveGridJOneLineCovector hcard H L)
          (twelveGridJOneLineCovector_ne_zero hcard H L) := by
      change _ ↔ Projectivization.orthogonal
        (Projectivization.mk ℝ (homogeneousLift (pivotInversion cfg p q))
          (homogeneousLift_ne_zero _))
        (Projectivization.mk ℝ (twelveGridJOneLineCovector hcard H L)
          (twelveGridJOneLineCovector_ne_zero hcard H L))
      rw [Projectivization.orthogonal_mk]
    _ ↔ projectivePoint (pivotInversion cfg p q) ∈
        determinedProjectiveLine (pivotInversion cfg p) L := by
      simp [twelveGridJOneLineCovector]
    _ ↔ q ∈ lineSupport (pivotInversion cfg p) L := by
      simpa only [affinePointToProjective_eq_projectivePoint,
        mem_lineSupport] using hmem

noncomputable def twelveGridJOneAffineLineCovector
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (hcard : Fintype.card Point = 12)
    (H : TwelveGridJOneInvertedLineCensus cfg p)
    (L : DeterminedLine (pivotInversion cfg p)) : Homogeneous3 :=
  twelveGridJOneAffineCovector hcard H
    (twelveGridJOneLineCovector hcard H L)

theorem twelveGridJOneAffineCovector_ne_zero
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (hcard : Fintype.card Point = 12)
    (H : TwelveGridJOneInvertedLineCensus cfg p)
    (ell : Homogeneous3) (hell : ell ≠ 0) :
    twelveGridJOneAffineCovector hcard H ell ≠ 0 := by
  intro hzero
  have hself : ell ⬝ᵥ ell = 0 := by
    simpa [hzero] using
      (twelveGridJOneAffineCovector_dot hcard H ell ell).symm
  exact hell (dotProduct_self_eq_zero.mp hself)

theorem twelveGridJOneAffineLineCovector_ne_zero
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (hcard : Fintype.card Point = 12)
    (H : TwelveGridJOneInvertedLineCensus cfg p)
    (L : DeterminedLine (pivotInversion cfg p)) :
    twelveGridJOneAffineLineCovector hcard H L ≠ 0 := by
  exact twelveGridJOneAffineCovector_ne_zero hcard H _
    (twelveGridJOneLineCovector_ne_zero hcard H L)

theorem twelveGridJOneAffineLineCovector_incident_iff
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (hcard : Fintype.card Point = 12)
    (H : TwelveGridJOneInvertedLineCensus cfg p)
    (L : DeterminedLine (pivotInversion cfg p)) (q : AwayFrom p) :
    twelveGridJOneAffineLineCovector hcard H L ⬝ᵥ
        twelveGridJOneAffinePoint hcard H q = 0 ↔
      q ∈ lineSupport (pivotInversion cfg p) L := by
  change twelveGridJOneAffineCovector hcard H
      (twelveGridJOneLineCovector hcard H L) ⬝ᵥ
      twelveGridJOneAffineHomogeneous hcard H
        (homogeneousLift (pivotInversion cfg p q)) = 0 ↔ _
  rw [twelveGridJOneAffineCovector_dot,
    twelveGridJOneLineCovector_incident_iff]

/-- Three finite JOne labels on one actual determined line are affinely
collinear in the chart derived above. -/
theorem twelveGridJOneAffineArea_eq_zero_of_line
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (hcard : Fintype.card Point = 12)
    (H : TwelveGridJOneInvertedLineCensus cfg p)
    (L : DeterminedLine (pivotInversion cfg p))
    (u v w : {q : AwayFrom p // TwelveGridJOneAffineFinite hcard H q})
    (hu : u.1 ∈ lineSupport (pivotInversion cfg p) L)
    (hv : v.1 ∈ lineSupport (pivotInversion cfg p) L)
    (hw : w.1 ∈ lineSupport (pivotInversion cfg p) L) :
    parameterizedThreeByThreeAffineArea
      (twelveGridJOneAffineCoordinate hcard H u)
      (twelveGridJOneAffineCoordinate hcard H v)
      (twelveGridJOneAffineCoordinate hcard H w) = 0 := by
  let ell := twelveGridJOneAffineLineCovector hcard H L
  have hcoordinate_incident :
      ∀ q : {q : AwayFrom p // TwelveGridJOneAffineFinite hcard H q},
        q.1 ∈ lineSupport (pivotInversion cfg p) L →
          ell ⬝ᵥ homogeneousLift
            (twelveGridAffinePairPoint2
              (twelveGridJOneAffineCoordinate hcard H q)) = 0 := by
    intro q hq
    have hinc := (twelveGridJOneAffineLineCovector_incident_iff
      hcard H L q.1).2 hq
    rw [twelveGridJOneAffinePoint_eq_scale_homogeneousLift] at hinc
    rw [dotProduct_smul, smul_eq_mul] at hinc
    exact (mul_eq_zero.mp hinc).resolve_left q.2
  exact twelveGridAffineArea_eq_zero_of_common_covector ell
    (twelveGridJOneAffineLineCovector_ne_zero hcard H L) _ _ _
    (hcoordinate_incident u hu) (hcoordinate_incident v hv)
    (hcoordinate_incident w hw)

/-! ### Nondegeneracy follows from actual row and column ownership -/

theorem twelveGridJOneColumnCoordinate_injective
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (hcard : Fintype.card Point = 12)
    (H : TwelveGridJOneInvertedLineCensus cfg p) :
    Function.Injective (twelveGridJOneColumnCoordinate hcard H) := by
  intro r r' hrr
  by_contra hne
  let q := twelveGridJOneGridPoint hcard H r 0
  have hinc : twelveGridJOneAffinePencilCovector hcard H 0 r ⬝ᵥ
      twelveGridJOneAffinePoint hcard H q = 0 :=
    (twelveGridJOneAffinePencilCovector_incident_iff hcard H 0 r q).2
      (twelveGridJOneGridPoint_mem_row hcard H r 0)
  rw [twelveGridJOneAffinePencilCovector_zero_normal_form] at hinc
  have hbase : (![1, 0,
      -twelveGridJOneColumnCoordinate hcard H r] : Homogeneous3) ⬝ᵥ
        twelveGridJOneAffinePoint hcard H q = 0 := by
    rw [smul_dotProduct, smul_eq_mul] at hinc
    exact (mul_eq_zero.mp hinc).resolve_left
      (twelveGridJOneAffinePencilCovector_zero_apply_zero_ne_zero hcard H r)
  have hbase' : (![1, 0,
      -twelveGridJOneColumnCoordinate hcard H r'] : Homogeneous3) ⬝ᵥ
        twelveGridJOneAffinePoint hcard H q = 0 := by
    simpa [hrr] using hbase
  have hinc' : twelveGridJOneAffinePencilCovector hcard H 0 r' ⬝ᵥ
      twelveGridJOneAffinePoint hcard H q = 0 := by
    rw [twelveGridJOneAffinePencilCovector_zero_normal_form,
      smul_dotProduct, smul_eq_mul]
    simp [hbase']
  have hmem' : q ∈ lineSupport (pivotInversion cfg p)
      (twelveGridJOnePencilLine hcard H 0 r').1 :=
    (twelveGridJOneAffinePencilCovector_incident_iff hcard H 0 r' q).1 hinc'
  exact (twelveGridJOneGridPoint_not_mem_other_row hcard H r 0 r' hne) hmem'

theorem twelveGridJOneRowCoordinate_injective
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (hcard : Fintype.card Point = 12)
    (H : TwelveGridJOneInvertedLineCensus cfg p) :
    Function.Injective (twelveGridJOneRowCoordinate hcard H) := by
  intro s s' hss
  by_contra hne
  let q := twelveGridJOneGridPoint hcard H 0 s
  have hinc : twelveGridJOneAffinePencilCovector hcard H 1 s ⬝ᵥ
      twelveGridJOneAffinePoint hcard H q = 0 :=
    (twelveGridJOneAffinePencilCovector_incident_iff hcard H 1 s q).2
      (twelveGridJOneGridPoint_mem_column hcard H 0 s)
  rw [twelveGridJOneAffinePencilCovector_one_normal_form] at hinc
  have hbase : (![0, 1,
      -twelveGridJOneRowCoordinate hcard H s] : Homogeneous3) ⬝ᵥ
        twelveGridJOneAffinePoint hcard H q = 0 := by
    rw [smul_dotProduct, smul_eq_mul] at hinc
    exact (mul_eq_zero.mp hinc).resolve_left
      (twelveGridJOneAffinePencilCovector_one_apply_one_ne_zero hcard H s)
  have hbase' : (![0, 1,
      -twelveGridJOneRowCoordinate hcard H s'] : Homogeneous3) ⬝ᵥ
        twelveGridJOneAffinePoint hcard H q = 0 := by
    simpa [hss] using hbase
  have hinc' : twelveGridJOneAffinePencilCovector hcard H 1 s' ⬝ᵥ
      twelveGridJOneAffinePoint hcard H q = 0 := by
    rw [twelveGridJOneAffinePencilCovector_one_normal_form,
      smul_dotProduct, smul_eq_mul]
    simp [hbase']
  have hmem' : q ∈ lineSupport (pivotInversion cfg p)
      (twelveGridJOnePencilLine hcard H 1 s').1 :=
    (twelveGridJOneAffinePencilCovector_incident_iff hcard H 1 s' q).1 hinc'
  exact (twelveGridJOneGridPoint_not_mem_other_column hcard H 0 s s' hne) hmem'

theorem twelveGridJOneColumnParameter_ne_neg_one
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (hcard : Fintype.card Point = 12)
    (H : TwelveGridJOneInvertedLineCensus cfg p) :
    twelveGridJOneColumnParameter hcard H ≠ -1 := by
  intro h
  have hcoordinate : twelveGridJOneColumnCoordinate hcard H 2 =
      twelveGridJOneColumnCoordinate hcard H 0 := by
    calc
      twelveGridJOneColumnCoordinate hcard H 2 =
          twelveGridJOneColumnParameter hcard H := rfl
      _ = -1 := h
      _ = twelveGridJOneColumnCoordinate hcard H 0 :=
        (twelveGridJOneColumnCoordinate_zero hcard H).symm
  have hindex := twelveGridJOneColumnCoordinate_injective hcard H hcoordinate
  omega

theorem twelveGridJOneColumnParameter_ne_zero
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (hcard : Fintype.card Point = 12)
    (H : TwelveGridJOneInvertedLineCensus cfg p) :
    twelveGridJOneColumnParameter hcard H ≠ 0 := by
  intro h
  have hcoordinate : twelveGridJOneColumnCoordinate hcard H 2 =
      twelveGridJOneColumnCoordinate hcard H 1 := by
    calc
      twelveGridJOneColumnCoordinate hcard H 2 =
          twelveGridJOneColumnParameter hcard H := rfl
      _ = 0 := h
      _ = twelveGridJOneColumnCoordinate hcard H 1 :=
        (twelveGridJOneColumnCoordinate_one hcard H).symm
  have hindex := twelveGridJOneColumnCoordinate_injective hcard H hcoordinate
  omega

theorem twelveGridJOneRowParameter_ne_neg_one
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (hcard : Fintype.card Point = 12)
    (H : TwelveGridJOneInvertedLineCensus cfg p) :
    twelveGridJOneRowParameter hcard H ≠ -1 := by
  intro h
  have hcoordinate : twelveGridJOneRowCoordinate hcard H 2 =
      twelveGridJOneRowCoordinate hcard H 0 := by
    calc
      twelveGridJOneRowCoordinate hcard H 2 =
          twelveGridJOneRowParameter hcard H := rfl
      _ = -1 := h
      _ = twelveGridJOneRowCoordinate hcard H 0 :=
        (twelveGridJOneRowCoordinate_zero hcard H).symm
  have hindex := twelveGridJOneRowCoordinate_injective hcard H hcoordinate
  omega

theorem twelveGridJOneRowParameter_ne_zero
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (hcard : Fintype.card Point = 12)
    (H : TwelveGridJOneInvertedLineCensus cfg p) :
    twelveGridJOneRowParameter hcard H ≠ 0 := by
  intro h
  have hcoordinate : twelveGridJOneRowCoordinate hcard H 2 =
      twelveGridJOneRowCoordinate hcard H 1 := by
    calc
      twelveGridJOneRowCoordinate hcard H 2 =
          twelveGridJOneRowParameter hcard H := rfl
      _ = 0 := h
      _ = twelveGridJOneRowCoordinate hcard H 1 :=
        (twelveGridJOneRowCoordinate_one hcard H).symm
  have hindex := twelveGridJOneRowCoordinate_injective hcard H hcoordinate
  omega

/-! ## The three actual transversals become coded parameterized ones -/

theorem twelveGridJOneGridTransversal_exists_permutation
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (hcard : Fintype.card Point = 12)
    (H : TwelveGridJOneInvertedLineCensus cfg p)
    (T : TwelveGridJOneActualGridTransversal hcard H) :
    ∃ σ : Fin 3 → Fin 3, Function.Injective σ ∧
      ∀ r : Fin 3,
        twelveGridJOneGridPoint hcard H r (σ r) ∈
          lineSupport (pivotInversion cfg p) T.line.1 := by
  classical
  let S : Finset (AwayFrom p) :=
    lineSupport (pivotInversion cfg p) T.line.1
  have hgrid : ∀ q : ↥S, ∃ rs : Fin 3 × Fin 3,
      twelveGridJOneGridPoint hcard H rs.1 rs.2 = q.1 := by
    intro q
    rcases T.point_is_grid q.1 q.2 with ⟨r, s, hrs⟩
    exact ⟨(r, s), hrs⟩
  let labels : ↥S → Fin 3 × Fin 3 := fun q => Classical.choose (hgrid q)
  have hlabels (q : ↥S) :
      twelveGridJOneGridPoint hcard H (labels q).1 (labels q).2 = q.1 :=
    Classical.choose_spec (hgrid q)
  let row : ↥S → Fin 3 := fun q => (labels q).1
  let column : ↥S → Fin 3 := fun q => (labels q).2
  have hrow_injective : Function.Injective row := by
    intro x y hxy
    apply Subtype.ext
    apply Finset.card_le_one.mp (T.row_inter_card_le_one (row x)) x.1
    · refine Finset.mem_inter.mpr ⟨x.2, ?_⟩
      rw [← hlabels x]
      exact twelveGridJOneGridPoint_mem_row hcard H (row x) (column x)
    · refine Finset.mem_inter.mpr ⟨y.2, ?_⟩
      have hyrow : row y = row x := hxy.symm
      have hymem := twelveGridJOneGridPoint_mem_row hcard H
        (row y) (column y)
      have hylabel : twelveGridJOneGridPoint hcard H
          (row y) (column y) = y.1 := by
        simpa [row, column] using hlabels y
      rw [hylabel, hyrow] at hymem
      exact hymem
  have hS_card : Fintype.card ↥S = 3 := by
    rw [Fintype.card_coe]
    exact T.line.2
  let rowEquiv : ↥S ≃ Fin 3 := Equiv.ofBijective row
    ((Fintype.bijective_iff_injective_and_card row).mpr ⟨hrow_injective, by
      simp [hS_card]⟩)
  let pointOfRow : Fin 3 → ↥S := fun r => rowEquiv.symm r
  have hpointOfRow_row (r : Fin 3) : row (pointOfRow r) = r := by
    exact rowEquiv.apply_symm_apply r
  let σ : Fin 3 → Fin 3 := fun r => column (pointOfRow r)
  refine ⟨σ, ?_, ?_⟩
  · intro r s hrs
    have hpoint_eq : (pointOfRow r).1 = (pointOfRow s).1 := by
      apply Finset.card_le_one.mp (T.column_inter_card_le_one (σ r))
      · refine Finset.mem_inter.mpr ⟨(pointOfRow r).2, ?_⟩
        rw [← hlabels (pointOfRow r)]
        exact twelveGridJOneGridPoint_mem_column hcard H
          (row (pointOfRow r)) (column (pointOfRow r))
      · refine Finset.mem_inter.mpr ⟨(pointOfRow s).2, ?_⟩
        have hscolumn : column (pointOfRow s) = column (pointOfRow r) := by
          simpa [σ] using hrs.symm
        have hsmem := twelveGridJOneGridPoint_mem_column hcard H
          (row (pointOfRow s)) (column (pointOfRow s))
        have hslabel : twelveGridJOneGridPoint hcard H
            (row (pointOfRow s)) (column (pointOfRow s)) = (pointOfRow s).1 := by
          simpa [row, column] using hlabels (pointOfRow s)
        rw [hslabel, hscolumn] at hsmem
        exact hsmem
    have hpoint_subtype : pointOfRow r = pointOfRow s := Subtype.ext hpoint_eq
    calc
      r = row (pointOfRow r) := (hpointOfRow_row r).symm
      _ = row (pointOfRow s) := congrArg row hpoint_subtype
      _ = s := hpointOfRow_row s
  · intro r
    change twelveGridJOneGridPoint hcard H r
      (column (pointOfRow r)) ∈ S
    have hlabel : twelveGridJOneGridPoint hcard H
        (row (pointOfRow r)) (column (pointOfRow r)) = (pointOfRow r).1 := by
      simpa [row, column] using hlabels (pointOfRow r)
    have hcoord : twelveGridJOneGridPoint hcard H r
        (column (pointOfRow r)) = (pointOfRow r).1 := by
      calc
        twelveGridJOneGridPoint hcard H r (column (pointOfRow r)) =
            twelveGridJOneGridPoint hcard H (row (pointOfRow r))
              (column (pointOfRow r)) :=
          congrArg
            (fun z : Fin 3 => twelveGridJOneGridPoint hcard H z
              (column (pointOfRow r)))
            (hpointOfRow_row r).symm
        _ = (pointOfRow r).1 := hlabel
    rw [hcoord]
    exact (pointOfRow r).2

theorem twelveGridJOneGridTransversal_parameterized
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (hcard : Fintype.card Point = 12)
    (H : TwelveGridJOneInvertedLineCensus cfg p)
    (T : TwelveGridJOneActualGridTransversal hcard H) :
    ∃ t : Fin 6,
      ParameterizedThreeByThreeGridTransversal
        (twelveGridJOneColumnParameter hcard H)
        (twelveGridJOneRowParameter hcard H) t := by
  obtain ⟨σ, hσinj, hσmem⟩ :=
    twelveGridJOneGridTransversal_exists_permutation hcard H T
  obtain ⟨t, ht⟩ :=
    finThree_injective_eq_parameterizedTransversalPermutation σ hσinj
  refine ⟨t, ?_⟩
  have harea := twelveGridJOneAffineArea_eq_zero_of_line hcard H T.line.1
    (twelveGridJOneAffineGridLabel hcard H (0, σ 0))
    (twelveGridJOneAffineGridLabel hcard H (1, σ 1))
    (twelveGridJOneAffineGridLabel hcard H (2, σ 2))
    (hσmem 0) (hσmem 1) (hσmem 2)
  rw [twelveGridJOneAffineGridLabel_coordinate,
    twelveGridJOneAffineGridLabel_coordinate,
    twelveGridJOneAffineGridLabel_coordinate] at harea
  change parameterizedThreeByThreeTransversalDeterminant
      (twelveGridJOneColumnParameter hcard H)
      (twelveGridJOneRowParameter hcard H) t = 0
  simpa [parameterizedThreeByThreeTransversalDeterminant,
    ht 0, ht 1, ht 2] using harea

/-- The permutation of a JOne transversal is chosen only from its verified
finite support; it is not a coordinate-normalization choice. -/
noncomputable def twelveGridJOneTransversalPermutation
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (hcard : Fintype.card Point = 12)
    (H : TwelveGridJOneInvertedLineCensus cfg p)
    (T : TwelveGridJOneActualGridTransversal hcard H) : Fin 3 → Fin 3 :=
  Classical.choose (twelveGridJOneGridTransversal_exists_permutation hcard H T)

theorem twelveGridJOneTransversalPermutation_injective
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (hcard : Fintype.card Point = 12)
    (H : TwelveGridJOneInvertedLineCensus cfg p)
    (T : TwelveGridJOneActualGridTransversal hcard H) :
    Function.Injective (twelveGridJOneTransversalPermutation hcard H T) :=
  (Classical.choose_spec
    (twelveGridJOneGridTransversal_exists_permutation hcard H T)).1

theorem twelveGridJOneTransversalPermutation_mem
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (hcard : Fintype.card Point = 12)
    (H : TwelveGridJOneInvertedLineCensus cfg p)
    (T : TwelveGridJOneActualGridTransversal hcard H) (r : Fin 3) :
    twelveGridJOneGridPoint hcard H r
      (twelveGridJOneTransversalPermutation hcard H T r) ∈
      lineSupport (pivotInversion cfg p) T.line.1 :=
  (Classical.choose_spec
    (twelveGridJOneGridTransversal_exists_permutation hcard H T)).2 r

noncomputable def twelveGridJOneTransversalCode
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (hcard : Fintype.card Point = 12)
    (H : TwelveGridJOneInvertedLineCensus cfg p)
    (T : TwelveGridJOneActualGridTransversal hcard H) : Fin 6 :=
  Classical.choose
    (finThree_injective_eq_parameterizedTransversalPermutation
      (twelveGridJOneTransversalPermutation hcard H T)
      (twelveGridJOneTransversalPermutation_injective hcard H T))

theorem twelveGridJOneTransversalCode_spec
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (hcard : Fintype.card Point = 12)
    (H : TwelveGridJOneInvertedLineCensus cfg p)
    (T : TwelveGridJOneActualGridTransversal hcard H) (r : Fin 3) :
    twelveGridJOneTransversalPermutation hcard H T r =
      parameterizedThreeByThreeTransversalPermutation
        (twelveGridJOneTransversalCode hcard H T) r :=
  (Classical.choose_spec
    (finThree_injective_eq_parameterizedTransversalPermutation
      (twelveGridJOneTransversalPermutation hcard H T)
      (twelveGridJOneTransversalPermutation_injective hcard H T))) r

theorem twelveGridJOneTransversalCode_parameterized
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (hcard : Fintype.card Point = 12)
    (H : TwelveGridJOneInvertedLineCensus cfg p)
    (T : TwelveGridJOneActualGridTransversal hcard H) :
    ParameterizedThreeByThreeGridTransversal
      (twelveGridJOneColumnParameter hcard H)
      (twelveGridJOneRowParameter hcard H)
      (twelveGridJOneTransversalCode hcard H T) := by
  let σ := twelveGridJOneTransversalPermutation hcard H T
  have harea := twelveGridJOneAffineArea_eq_zero_of_line hcard H T.line.1
    (twelveGridJOneAffineGridLabel hcard H (0, σ 0))
    (twelveGridJOneAffineGridLabel hcard H (1, σ 1))
    (twelveGridJOneAffineGridLabel hcard H (2, σ 2))
    (twelveGridJOneTransversalPermutation_mem hcard H T 0)
    (twelveGridJOneTransversalPermutation_mem hcard H T 1)
    (twelveGridJOneTransversalPermutation_mem hcard H T 2)
  rw [twelveGridJOneAffineGridLabel_coordinate,
    twelveGridJOneAffineGridLabel_coordinate,
    twelveGridJOneAffineGridLabel_coordinate] at harea
  dsimp [σ] at harea
  change parameterizedThreeByThreeTransversalDeterminant
      (twelveGridJOneColumnParameter hcard H)
      (twelveGridJOneRowParameter hcard H)
      (twelveGridJOneTransversalCode hcard H T) = 0
  simpa [parameterizedThreeByThreeTransversalDeterminant,
    parameterizedThreeByThreeGridArea,
    twelveGridJOneTransversalCode_spec hcard H T 0,
    twelveGridJOneTransversalCode_spec hcard H T 1,
    twelveGridJOneTransversalCode_spec hcard H T 2] using harea

theorem twelveGridJOneTransversalCode_ne_of_line_ne
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (hcard : Fintype.card Point = 12)
    (H : TwelveGridJOneInvertedLineCensus cfg p)
    (T U : TwelveGridJOneActualGridTransversal hcard H)
    (hline : T.line ≠ U.line) :
    twelveGridJOneTransversalCode hcard H T ≠
      twelveGridJOneTransversalCode hcard H U := by
  intro hcode
  have hcolumn0 : twelveGridJOneTransversalPermutation hcard H U 0 =
      twelveGridJOneTransversalPermutation hcard H T 0 := by
    calc
      twelveGridJOneTransversalPermutation hcard H U 0 =
          parameterizedThreeByThreeTransversalPermutation
            (twelveGridJOneTransversalCode hcard H U) 0 :=
        twelveGridJOneTransversalCode_spec hcard H U 0
      _ = parameterizedThreeByThreeTransversalPermutation
            (twelveGridJOneTransversalCode hcard H T) 0 := by rw [hcode]
      _ = twelveGridJOneTransversalPermutation hcard H T 0 :=
        (twelveGridJOneTransversalCode_spec hcard H T 0).symm
  have hcolumn1 : twelveGridJOneTransversalPermutation hcard H U 1 =
      twelveGridJOneTransversalPermutation hcard H T 1 := by
    calc
      twelveGridJOneTransversalPermutation hcard H U 1 =
          parameterizedThreeByThreeTransversalPermutation
            (twelveGridJOneTransversalCode hcard H U) 1 :=
        twelveGridJOneTransversalCode_spec hcard H U 1
      _ = parameterizedThreeByThreeTransversalPermutation
            (twelveGridJOneTransversalCode hcard H T) 1 := by rw [hcode]
      _ = twelveGridJOneTransversalPermutation hcard H T 1 :=
        (twelveGridJOneTransversalCode_spec hcard H T 1).symm
  let q0 := twelveGridJOneGridPoint hcard H 0
    (twelveGridJOneTransversalPermutation hcard H T 0)
  let q1 := twelveGridJOneGridPoint hcard H 1
    (twelveGridJOneTransversalPermutation hcard H T 1)
  have hq01 : q0 ≠ q1 := by
    intro hq
    apply twelveGridJOneGridPoint_not_mem_other_row hcard H
      0 (twelveGridJOneTransversalPermutation hcard H T 0) 1 (by omega)
    change q0 ∈ lineSupport (pivotInversion cfg p)
      (twelveGridJOnePencilLine hcard H 0 1).1
    have hq1mem : q1 ∈ lineSupport (pivotInversion cfg p)
        (twelveGridJOnePencilLine hcard H 0 1).1 :=
      twelveGridJOneGridPoint_mem_row hcard H 1
        (twelveGridJOneTransversalPermutation hcard H T 1)
    exact hq ▸ hq1mem
  have hq0T : q0 ∈ lineSupport (pivotInversion cfg p) T.line.1 :=
    twelveGridJOneTransversalPermutation_mem hcard H T 0
  have hq1T : q1 ∈ lineSupport (pivotInversion cfg p) T.line.1 :=
    twelveGridJOneTransversalPermutation_mem hcard H T 1
  have hq0U : q0 ∈ lineSupport (pivotInversion cfg p) U.line.1 := by
    simpa [q0, hcolumn0] using
      (twelveGridJOneTransversalPermutation_mem hcard H U 0)
  have hq1U : q1 ∈ lineSupport (pivotInversion cfg p) U.line.1 := by
    simpa [q1, hcolumn1] using
      (twelveGridJOneTransversalPermutation_mem hcard H U 1)
  have hlines : T.line.1 = U.line.1 := twelveGridActualLine_eq_of_two_mem
    T.line.1 U.line.1 q0 q1 hq01 hq0T hq1T hq0U hq1U
  exact hline (Subtype.ext hlines)

theorem twelveGridJOneThreeTransversals_parameterized
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (hcard : Fintype.card Point = 12)
    (H : TwelveGridJOneInvertedLineCensus cfg p) :
    ∃ s t u : Fin 6, s ≠ t ∧ s ≠ u ∧ t ≠ u ∧
      ParameterizedThreeByThreeGridTransversal
        (twelveGridJOneColumnParameter hcard H)
        (twelveGridJOneRowParameter hcard H) s ∧
      ParameterizedThreeByThreeGridTransversal
        (twelveGridJOneColumnParameter hcard H)
        (twelveGridJOneRowParameter hcard H) t ∧
      ParameterizedThreeByThreeGridTransversal
        (twelveGridJOneColumnParameter hcard H)
        (twelveGridJOneRowParameter hcard H) u := by
  let T0 := twelveGridJOneThreeLineTransversal hcard H 0
  let T1 := twelveGridJOneThreeLineTransversal hcard H 1
  let T2 := twelveGridJOneThreeLineTransversal hcard H 2
  have h01 : T0.line ≠ T1.line := by
    intro h
    have hzeroone : (0 : Fin 3) = 1 :=
      twelveGridJOneThreeLineTransversal_line_injective hcard H h
    omega
  have h02 : T0.line ≠ T2.line := by
    intro h
    have hzeroone : (0 : Fin 3) = 2 :=
      twelveGridJOneThreeLineTransversal_line_injective hcard H h
    omega
  have h12 : T1.line ≠ T2.line := by
    intro h
    have hzeroone : (1 : Fin 3) = 2 :=
      twelveGridJOneThreeLineTransversal_line_injective hcard H h
    omega
  refine ⟨twelveGridJOneTransversalCode hcard H T0,
    twelveGridJOneTransversalCode hcard H T1,
    twelveGridJOneTransversalCode hcard H T2,
    twelveGridJOneTransversalCode_ne_of_line_ne hcard H T0 T1 h01,
    twelveGridJOneTransversalCode_ne_of_line_ne hcard H T0 T2 h02,
    twelveGridJOneTransversalCode_ne_of_line_ne hcard H T1 T2 h12,
    twelveGridJOneTransversalCode_parameterized hcard H T0,
    twelveGridJOneTransversalCode_parameterized hcard H T1,
    twelveGridJOneTransversalCode_parameterized hcard H T2⟩

/-- The JOne equality census is impossible: its six actual four-lines force
a parameterized real `3 × 3` grid, while its three actual three-lines give
three distinct grid transversals. -/
theorem twelveGridJOneInvertedLineCensus_impossible
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (hcard : Fintype.card Point = 12)
    (H : TwelveGridJOneInvertedLineCensus cfg p) : False := by
  obtain ⟨s, t, u, hst, hsu, htu, hs, ht, hu⟩ :=
    twelveGridJOneThreeTransversals_parameterized hcard H
  exact parameterizedThreeByThreeGrid_no_three_distinct_transversals
    (twelveGridJOneColumnParameter_ne_neg_one hcard H)
    (twelveGridJOneColumnParameter_ne_zero hcard H)
    (twelveGridJOneRowParameter_ne_neg_one hcard H)
    (twelveGridJOneRowParameter_ne_zero hcard H)
    hst hsu htu hs ht hu

/-- The remaining `j = 1` equality case is ruled out without a projective
normalization premise.  This is the exact former
`RealPlaneTwelveGridPrinciple.jOneFiveDegreeCap` interface. -/
theorem twelveGridJOne_five_degree_cap_unconditional
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    (cfg : Configuration Point) (_hadm : Admissible cfg)
    (hcard : Fintype.card Point = 12)
    (hcap : BlockSizeCap (blockSystem cfg) 5)
    (p : Point) (hthree : (blockSystem cfg).blockDegree 3 p = 10) :
    (blockSystem cfg).blockDegree 5 p ≤ 5 := by
  classical
  have hle := twelveGridJOne_five_degree_le_six (blockSystem cfg) hcard p
  by_contra hnot
  have hfive : (blockSystem cfg).blockDegree 5 p = 6 := by omega
  exact twelveGridJOneInvertedLineCensus_impossible hcard
    (twelveGridJOneInvertedLineCensus_of_degree_row cfg p hcard hcap hthree hfive)

end Erdos506.V1
