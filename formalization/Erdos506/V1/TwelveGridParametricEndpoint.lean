import Erdos506.V1.TwelveGridParametricObstruction
import Erdos506.V1.TwelveGeometry
import Erdos506.V1.TwelveGridNormalTransfer
import Mathlib.Tactic

/-!
# Finite endpoint for the actual twelve-grid chart

This module contains only consequences of the actual reconstructed census.
In particular, its transversal and secant data are obtained from the
enumerated determined lines; no affine normalization is postulated.
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

/-! ## The finite combinatorics of an actual transversal -/

/-- The three points of an actual transversal use every row and every column
exactly once.  This is the lossless bridge from the support formulation of
`TwelveGridActualGridTransversal` to a permutation of `Fin 3`. -/
theorem twelveGridActualGridTransversal_exists_permutation
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (hcard : Fintype.card Point = 12)
    (H : TwelveGridInvertedLineCensus cfg p)
    (T : TwelveGridActualGridTransversal hcard H) :
    ∃ σ : Fin 3 → Fin 3, Function.Injective σ ∧
      ∀ r : Fin 3,
        twelveGridActualGridPoint hcard H r (σ r) ∈
          lineSupport (pivotInversion cfg p) T.line.1 := by
  classical
  let S : Finset (AwayFrom p) :=
    lineSupport (pivotInversion cfg p) T.line.1
  have hgrid : ∀ q : ↥S, ∃ rs : Fin 3 × Fin 3,
      twelveGridActualGridPoint hcard H rs.1 rs.2 = q.1 := by
    intro q
    rcases T.point_is_grid q.1 q.2 with ⟨r, s, hrs⟩
    exact ⟨(r, s), hrs⟩
  let labels : ↥S → Fin 3 × Fin 3 := fun q => Classical.choose (hgrid q)
  have hlabels (q : ↥S) :
      twelveGridActualGridPoint hcard H (labels q).1 (labels q).2 = q.1 :=
    Classical.choose_spec (hgrid q)
  let row : ↥S → Fin 3 := fun q => (labels q).1
  let column : ↥S → Fin 3 := fun q => (labels q).2
  have hrow_injective : Function.Injective row := by
    intro x y hxy
    apply Subtype.ext
    apply Finset.card_le_one.mp (T.row_inter_card_le_one (row x)) x.1
    · refine Finset.mem_inter.mpr ⟨x.2, ?_⟩
      rw [← hlabels x]
      exact twelveGridActualGridPoint_mem_row hcard H (row x) (column x)
    · refine Finset.mem_inter.mpr ⟨y.2, ?_⟩
      have hyrow : row y = row x := hxy.symm
      have hymem := twelveGridActualGridPoint_mem_row hcard H
        (row y) (column y)
      have hylabel : twelveGridActualGridPoint hcard H
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
        exact twelveGridActualGridPoint_mem_column hcard H
          (row (pointOfRow r)) (column (pointOfRow r))
      · refine Finset.mem_inter.mpr ⟨(pointOfRow s).2, ?_⟩
        have hscolumn : column (pointOfRow s) = column (pointOfRow r) := by
          simpa [σ] using hrs.symm
        have hsmem := twelveGridActualGridPoint_mem_column hcard H
          (row (pointOfRow s)) (column (pointOfRow s))
        have hslabel : twelveGridActualGridPoint hcard H
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
    change twelveGridActualGridPoint hcard H r
      (column (pointOfRow r)) ∈ S
    have hlabel : twelveGridActualGridPoint hcard H
        (row (pointOfRow r)) (column (pointOfRow r)) = (pointOfRow r).1 := by
      simpa [row, column] using hlabels (pointOfRow r)
    have hcoord : twelveGridActualGridPoint hcard H r
        (column (pointOfRow r)) = (pointOfRow r).1 := by
      calc
        twelveGridActualGridPoint hcard H r (column (pointOfRow r)) =
            twelveGridActualGridPoint hcard H (row (pointOfRow r))
              (column (pointOfRow r)) :=
          congrArg
            (fun z : Fin 3 => twelveGridActualGridPoint hcard H z
              (column (pointOfRow r)))
            (hpointOfRow_row r).symm
        _ = (pointOfRow r).1 := hlabel
    rw [hcoord]
    exact (pointOfRow r).2

/-- Every injective self-map of `Fin 3` is one of the six displayed
transversal permutations. -/
theorem finThree_injective_eq_parameterizedTransversalPermutation
    (σ : Fin 3 → Fin 3) (hσ : Function.Injective σ) :
    ∃ t : Fin 6, ∀ r : Fin 3,
      σ r = parameterizedThreeByThreeTransversalPermutation t r := by
  have h01 : σ 0 ≠ σ 1 := by
    intro h
    have hzero : (0 : Fin 3) = 1 := hσ h
    omega
  have h02 : σ 0 ≠ σ 2 := by
    intro h
    have hzero : (0 : Fin 3) = 2 := hσ h
    omega
  have h12 : σ 1 ≠ σ 2 := by
    intro h
    have hone : (1 : Fin 3) = 2 := hσ h
    omega
  clear hσ
  have finThreeCases : ∀ x : Fin 3, x = 0 ∨ x = 1 ∨ x = 2 := by
    intro x
    fin_cases x <;> simp
  let t : Fin 6 :=
    if σ 0 = 0 then
      if σ 1 = 1 then 0 else 1
    else if σ 0 = 1 then
      if σ 1 = 0 then 2 else 3
    else if σ 1 = 0 then 4 else 5
  refine ⟨t, ?_⟩
  rcases finThreeCases (σ 0) with h0 | h0 | h0 <;>
    rcases finThreeCases (σ 1) with h1 | h1 | h1 <;>
    rcases finThreeCases (σ 2) with h2 | h2 | h2
  all_goals
    intro r
    fin_cases r <;>
      simp_all [t, parameterizedThreeByThreeTransversalPermutation,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two]

/-! ## Collinearity in the actual affine chart -/

/-- A canonical raw covector for any actual determined line, not only for a
member of one of the two reconstructed pencils. -/
noncomputable def twelveGridActualLineCovector
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (hcard : Fintype.card Point = 12)
    (H : TwelveGridInvertedLineCensus cfg p)
    (L : DeterminedLine (pivotInversion cfg p)) : Homogeneous3 :=
  (determinedProjectiveLine (pivotInversion cfg p) L).rep

theorem twelveGridActualLineCovector_ne_zero
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (hcard : Fintype.card Point = 12)
    (H : TwelveGridInvertedLineCensus cfg p)
    (L : DeterminedLine (pivotInversion cfg p)) :
    twelveGridActualLineCovector hcard H L ≠ 0 := by
  simpa [twelveGridActualLineCovector] using
    (determinedProjectiveLine (pivotInversion cfg p) L).rep_nonzero

/-- Raw homogeneous incidence of an arbitrary actual determined line is
precisely its original support incidence. -/
theorem twelveGridActualLineCovector_incident_iff
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (hcard : Fintype.card Point = 12)
    (H : TwelveGridInvertedLineCensus cfg p)
    (L : DeterminedLine (pivotInversion cfg p)) (q : AwayFrom p) :
    twelveGridActualLineCovector hcard H L ⬝ᵥ
        homogeneousLift (pivotInversion cfg p q) = 0 ↔
      q ∈ lineSupport (pivotInversion cfg p) L := by
  have hmem := affinePoint_mem_determinedProjectiveLine_iff
    (pivotInversion cfg p) q L
  calc
    twelveGridActualLineCovector hcard H L ⬝ᵥ
        homogeneousLift (pivotInversion cfg p q) = 0 ↔
      homogeneousLift (pivotInversion cfg p q) ⬝ᵥ
          twelveGridActualLineCovector hcard H L = 0 := by
        constructor
        · intro h
          calc
            homogeneousLift (pivotInversion cfg p q) ⬝ᵥ
                twelveGridActualLineCovector hcard H L =
                twelveGridActualLineCovector hcard H L ⬝ᵥ
                  homogeneousLift (pivotInversion cfg p q) :=
              dotProduct_comm _ _
            _ = 0 := h
        · intro h
          calc
            twelveGridActualLineCovector hcard H L ⬝ᵥ
                homogeneousLift (pivotInversion cfg p q) =
                homogeneousLift (pivotInversion cfg p q) ⬝ᵥ
                  twelveGridActualLineCovector hcard H L :=
              dotProduct_comm _ _
            _ = 0 := h
    _ ↔ projectivePoint (pivotInversion cfg p q) ∈
        Projectivization.mk ℝ (twelveGridActualLineCovector hcard H L)
          (twelveGridActualLineCovector_ne_zero hcard H L) := by
      change _ ↔ Projectivization.orthogonal
        (Projectivization.mk ℝ (homogeneousLift (pivotInversion cfg p q))
          (homogeneousLift_ne_zero _))
        (Projectivization.mk ℝ (twelveGridActualLineCovector hcard H L)
          (twelveGridActualLineCovector_ne_zero hcard H L))
      rw [Projectivization.orthogonal_mk]
    _ ↔ projectivePoint (pivotInversion cfg p q) ∈
        determinedProjectiveLine (pivotInversion cfg p) L := by
      simp [twelveGridActualLineCovector]
    _ ↔ q ∈ lineSupport (pivotInversion cfg p) L := by
      simpa only [affinePointToProjective_eq_projectivePoint,
        mem_lineSupport] using hmem

/-- The arbitrary-line covector after the canonical actual affine chart. -/
noncomputable def twelveGridActualAffineLineCovector
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (hcard : Fintype.card Point = 12)
    (H : TwelveGridInvertedLineCensus cfg p)
    (L : DeterminedLine (pivotInversion cfg p)) : Homogeneous3 :=
  twelveGridActualAffineCovector hcard H
    (twelveGridActualLineCovector hcard H L)

/-- The derived chart does not kill any nonzero covector. -/
theorem twelveGridActualAffineCovector_ne_zero
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (hcard : Fintype.card Point = 12)
    (H : TwelveGridInvertedLineCensus cfg p)
    (ell : Homogeneous3) (hell : ell ≠ 0) :
    twelveGridActualAffineCovector hcard H ell ≠ 0 := by
  intro hzero
  have hself : ell ⬝ᵥ ell = 0 := by
    simpa [hzero] using
      (twelveGridActualAffineCovector_dot hcard H ell ell).symm
  exact hell (dotProduct_self_eq_zero.mp hself)

theorem twelveGridActualAffineLineCovector_ne_zero
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (hcard : Fintype.card Point = 12)
    (H : TwelveGridInvertedLineCensus cfg p)
    (L : DeterminedLine (pivotInversion cfg p)) :
    twelveGridActualAffineLineCovector hcard H L ≠ 0 := by
  exact twelveGridActualAffineCovector_ne_zero hcard H _
    (twelveGridActualLineCovector_ne_zero hcard H L)

/-- Incidence with an arbitrary actual line survives in the affine chart. -/
theorem twelveGridActualAffineLineCovector_incident_iff
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (hcard : Fintype.card Point = 12)
    (H : TwelveGridInvertedLineCensus cfg p)
    (L : DeterminedLine (pivotInversion cfg p)) (q : AwayFrom p) :
    twelveGridActualAffineLineCovector hcard H L ⬝ᵥ
        twelveGridActualAffinePoint hcard H q = 0 ↔
      q ∈ lineSupport (pivotInversion cfg p) L := by
  change twelveGridActualAffineCovector hcard H
      (twelveGridActualLineCovector hcard H L) ⬝ᵥ
      twelveGridActualAffineHomogeneous hcard H
        (homogeneousLift (pivotInversion cfg p q)) = 0 ↔ _
  rw [twelveGridActualAffineCovector_dot,
    twelveGridActualLineCovector_incident_iff]

/-- Three finite affine points on one nonzero homogeneous covector have zero
oriented affine area. -/
theorem twelveGridAffineArea_eq_zero_of_common_covector
    (ell : Homogeneous3) (hell : ell ≠ 0)
    (u v w : ℝ × ℝ)
    (hu : ell ⬝ᵥ homogeneousLift (twelveGridAffinePairPoint2 u) = 0)
    (hv : ell ⬝ᵥ homogeneousLift (twelveGridAffinePairPoint2 v) = 0)
    (hw : ell ⬝ᵥ homogeneousLift (twelveGridAffinePairPoint2 w) = 0) :
    parameterizedThreeByThreeAffineArea u v w = 0 := by
  have hu' : ell 0 * u.1 + ell 1 * u.2 + ell 2 = 0 := by
    simpa [homogeneousLift, twelveGridAffinePairPoint2, dotProduct,
      Fin.sum_univ_three] using hu
  have hv' : ell 0 * v.1 + ell 1 * v.2 + ell 2 = 0 := by
    simpa [homogeneousLift, twelveGridAffinePairPoint2, dotProduct,
      Fin.sum_univ_three] using hv
  have hw' : ell 0 * w.1 + ell 1 * w.2 + ell 2 = 0 := by
    simpa [homogeneousLift, twelveGridAffinePairPoint2, dotProduct,
      Fin.sum_univ_three] using hw
  by_cases hzero : ell 0 = 0
  · by_cases hone : ell 1 = 0
    · have htwo : ell 2 = 0 := by simpa [hzero, hone] using hu'
      exfalso
      apply hell
      ext i
      fin_cases i <;> simp [hzero, hone, htwo]
    · have hu0 : ell 1 * u.2 + ell 2 = 0 := by
        simpa [hzero] using hu'
      have hv0 : ell 1 * v.2 + ell 2 = 0 := by
        simpa [hzero] using hv'
      have hw0 : ell 1 * w.2 + ell 2 = 0 := by
        simpa [hzero] using hw'
      have huv : ell 1 * (v.2 - u.2) = 0 := by
        linear_combination hv0 - hu0
      have huw : ell 1 * (w.2 - u.2) = 0 := by
        linear_combination hw0 - hu0
      have hvy : v.2 = u.2 := by
        have h : v.2 - u.2 = 0 := (mul_eq_zero.mp huv).resolve_left hone
        linarith
      have hwy : w.2 = u.2 := by
        have h : w.2 - u.2 = 0 := (mul_eq_zero.mp huw).resolve_left hone
        linarith
      rw [parameterizedThreeByThreeAffineArea, hvy, hwy]
      ring
  · have huv : ell 0 * (v.1 - u.1) + ell 1 * (v.2 - u.2) = 0 := by
      linear_combination hv' - hu'
    have huw : ell 0 * (w.1 - u.1) + ell 1 * (w.2 - u.2) = 0 := by
      linear_combination hw' - hu'
    have harea : ell 0 * parameterizedThreeByThreeAffineArea u v w = 0 := by
      calc
        ell 0 * parameterizedThreeByThreeAffineArea u v w =
            (ell 0 * (v.1 - u.1) + ell 1 * (v.2 - u.2)) * (w.2 - u.2) -
              (ell 0 * (w.1 - u.1) + ell 1 * (w.2 - u.2)) * (v.2 - u.2) := by
          simp [parameterizedThreeByThreeAffineArea]
          ring
        _ = 0 := by rw [huv, huw]; ring
    exact (mul_eq_zero.mp harea).resolve_left hzero

/-- Dehomogenized coordinates of finite actual points on any one actual line
are affinely collinear. -/
theorem twelveGridActualAffineArea_eq_zero_of_line
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (hcard : Fintype.card Point = 12)
    (H : TwelveGridInvertedLineCensus cfg p)
    (L : DeterminedLine (pivotInversion cfg p))
    (u v w : {q : AwayFrom p // TwelveGridActualAffineFinite hcard H q})
    (hu : u.1 ∈ lineSupport (pivotInversion cfg p) L)
    (hv : v.1 ∈ lineSupport (pivotInversion cfg p) L)
    (hw : w.1 ∈ lineSupport (pivotInversion cfg p) L) :
    parameterizedThreeByThreeAffineArea
      (twelveGridActualAffineCoordinate hcard H u)
      (twelveGridActualAffineCoordinate hcard H v)
      (twelveGridActualAffineCoordinate hcard H w) = 0 := by
  let ell := twelveGridActualAffineLineCovector hcard H L
  have hcoordinate_incident :
      ∀ q : {q : AwayFrom p // TwelveGridActualAffineFinite hcard H q},
        q.1 ∈ lineSupport (pivotInversion cfg p) L →
          ell ⬝ᵥ homogeneousLift
            (twelveGridAffinePairPoint2
              (twelveGridActualAffineCoordinate hcard H q)) = 0 := by
    intro q hq
    have hinc := (twelveGridActualAffineLineCovector_incident_iff
      hcard H L q.1).2 hq
    rw [twelveGridActualAffinePoint_eq_scale_homogeneousLift] at hinc
    rw [dotProduct_smul, smul_eq_mul] at hinc
    exact (mul_eq_zero.mp hinc).resolve_left q.2
  exact twelveGridAffineArea_eq_zero_of_common_covector ell
    (twelveGridActualAffineLineCovector_ne_zero hcard H L) _ _ _
    (hcoordinate_incident u hu) (hcoordinate_incident v hv)
    (hcoordinate_incident w hw)

/-! ## Nondegeneracy of the two actual parameters -/

/-- The three first-pencil levels in the derived affine chart are genuinely
different: otherwise a labelled grid crossing would lie on two different
actual rows. -/
theorem twelveGridActualColumnCoordinate_injective
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (hcard : Fintype.card Point = 12)
    (H : TwelveGridInvertedLineCensus cfg p) :
    Function.Injective (twelveGridActualColumnCoordinate hcard H) := by
  intro r r' hrr
  by_contra hne
  let q := twelveGridActualGridPoint hcard H r 0
  have hinc : twelveGridActualAffinePencilCovector hcard H 0 r ⬝ᵥ
      twelveGridActualAffinePoint hcard H q = 0 :=
    (twelveGridActualAffinePencilCovector_incident_iff hcard H 0 r q).2
      (twelveGridActualGridPoint_mem_row hcard H r 0)
  rw [twelveGridActualAffinePencilCovector_zero_normal_form] at hinc
  have hbase : (![1, 0,
      -twelveGridActualColumnCoordinate hcard H r] : Homogeneous3) ⬝ᵥ
        twelveGridActualAffinePoint hcard H q = 0 := by
    rw [smul_dotProduct, smul_eq_mul] at hinc
    exact (mul_eq_zero.mp hinc).resolve_left
      (twelveGridActualAffinePencilCovector_zero_apply_zero_ne_zero hcard H r)
  have hbase' : (![1, 0,
      -twelveGridActualColumnCoordinate hcard H r'] : Homogeneous3) ⬝ᵥ
        twelveGridActualAffinePoint hcard H q = 0 := by
    simpa [hrr] using hbase
  have hinc' : twelveGridActualAffinePencilCovector hcard H 0 r' ⬝ᵥ
      twelveGridActualAffinePoint hcard H q = 0 := by
    rw [twelveGridActualAffinePencilCovector_zero_normal_form,
      smul_dotProduct, smul_eq_mul]
    simp [hbase']
  have hmem' : q ∈ lineSupport (pivotInversion cfg p)
      (twelveGridActualPencilLine hcard H 0 r').1 :=
    (twelveGridActualAffinePencilCovector_incident_iff hcard H 0 r' q).1 hinc'
  exact (twelveGridActualGridPoint_not_mem_other_row hcard H r 0 r' hne) hmem'

/-- The three second-pencil levels in the derived affine chart are genuinely
different, by the analogous column-incidence argument. -/
theorem twelveGridActualRowCoordinate_injective
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (hcard : Fintype.card Point = 12)
    (H : TwelveGridInvertedLineCensus cfg p) :
    Function.Injective (twelveGridActualRowCoordinate hcard H) := by
  intro s s' hss
  by_contra hne
  let q := twelveGridActualGridPoint hcard H 0 s
  have hinc : twelveGridActualAffinePencilCovector hcard H 1 s ⬝ᵥ
      twelveGridActualAffinePoint hcard H q = 0 :=
    (twelveGridActualAffinePencilCovector_incident_iff hcard H 1 s q).2
      (twelveGridActualGridPoint_mem_column hcard H 0 s)
  rw [twelveGridActualAffinePencilCovector_one_normal_form] at hinc
  have hbase : (![0, 1,
      -twelveGridActualRowCoordinate hcard H s] : Homogeneous3) ⬝ᵥ
        twelveGridActualAffinePoint hcard H q = 0 := by
    rw [smul_dotProduct, smul_eq_mul] at hinc
    exact (mul_eq_zero.mp hinc).resolve_left
      (twelveGridActualAffinePencilCovector_one_apply_one_ne_zero hcard H s)
  have hbase' : (![0, 1,
      -twelveGridActualRowCoordinate hcard H s'] : Homogeneous3) ⬝ᵥ
        twelveGridActualAffinePoint hcard H q = 0 := by
    simpa [hss] using hbase
  have hinc' : twelveGridActualAffinePencilCovector hcard H 1 s' ⬝ᵥ
      twelveGridActualAffinePoint hcard H q = 0 := by
    rw [twelveGridActualAffinePencilCovector_one_normal_form,
      smul_dotProduct, smul_eq_mul]
    simp [hbase']
  have hmem' : q ∈ lineSupport (pivotInversion cfg p)
      (twelveGridActualPencilLine hcard H 1 s').1 :=
    (twelveGridActualAffinePencilCovector_incident_iff hcard H 1 s' q).1 hinc'
  exact (twelveGridActualGridPoint_not_mem_other_column hcard H 0 s s' hne) hmem'

theorem twelveGridActualColumnParameter_ne_neg_one
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (hcard : Fintype.card Point = 12)
    (H : TwelveGridInvertedLineCensus cfg p) :
    twelveGridActualColumnParameter hcard H ≠ -1 := by
  intro h
  have hcoordinate : twelveGridActualColumnCoordinate hcard H 2 =
      twelveGridActualColumnCoordinate hcard H 0 := by
    calc
      twelveGridActualColumnCoordinate hcard H 2 =
          twelveGridActualColumnParameter hcard H := rfl
      _ = -1 := h
      _ = twelveGridActualColumnCoordinate hcard H 0 :=
        (twelveGridActualColumnCoordinate_zero hcard H).symm
  have hindex := twelveGridActualColumnCoordinate_injective hcard H hcoordinate
  omega

theorem twelveGridActualColumnParameter_ne_zero
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (hcard : Fintype.card Point = 12)
    (H : TwelveGridInvertedLineCensus cfg p) :
    twelveGridActualColumnParameter hcard H ≠ 0 := by
  intro h
  have hcoordinate : twelveGridActualColumnCoordinate hcard H 2 =
      twelveGridActualColumnCoordinate hcard H 1 := by
    calc
      twelveGridActualColumnCoordinate hcard H 2 =
          twelveGridActualColumnParameter hcard H := rfl
      _ = 0 := h
      _ = twelveGridActualColumnCoordinate hcard H 1 :=
        (twelveGridActualColumnCoordinate_one hcard H).symm
  have hindex := twelveGridActualColumnCoordinate_injective hcard H hcoordinate
  omega

theorem twelveGridActualRowParameter_ne_neg_one
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (hcard : Fintype.card Point = 12)
    (H : TwelveGridInvertedLineCensus cfg p) :
    twelveGridActualRowParameter hcard H ≠ -1 := by
  intro h
  have hcoordinate : twelveGridActualRowCoordinate hcard H 2 =
      twelveGridActualRowCoordinate hcard H 0 := by
    calc
      twelveGridActualRowCoordinate hcard H 2 =
          twelveGridActualRowParameter hcard H := rfl
      _ = -1 := h
      _ = twelveGridActualRowCoordinate hcard H 0 :=
        (twelveGridActualRowCoordinate_zero hcard H).symm
  have hindex := twelveGridActualRowCoordinate_injective hcard H hcoordinate
  omega

theorem twelveGridActualRowParameter_ne_zero
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (hcard : Fintype.card Point = 12)
    (H : TwelveGridInvertedLineCensus cfg p) :
    twelveGridActualRowParameter hcard H ≠ 0 := by
  intro h
  have hcoordinate : twelveGridActualRowCoordinate hcard H 2 =
      twelveGridActualRowCoordinate hcard H 1 := by
    calc
      twelveGridActualRowCoordinate hcard H 2 =
          twelveGridActualRowParameter hcard H := rfl
      _ = 0 := h
      _ = twelveGridActualRowCoordinate hcard H 1 :=
        (twelveGridActualRowCoordinate_one hcard H).symm
  have hindex := twelveGridActualRowCoordinate_injective hcard H hcoordinate
  omega

/-! ## Actual transversals become the six coded parameterized transversals -/

/-- The three actual grid crossings of any actual transversal give one of the
six determinant-zero parameterized transversals in the derived chart. -/
theorem twelveGridActualGridTransversal_parameterized
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (hcard : Fintype.card Point = 12)
    (H : TwelveGridInvertedLineCensus cfg p)
    (T : TwelveGridActualGridTransversal hcard H) :
    ∃ t : Fin 6,
      ParameterizedThreeByThreeGridTransversal
        (twelveGridActualColumnParameter hcard H)
        (twelveGridActualRowParameter hcard H) t := by
  obtain ⟨σ, hσinj, hσmem⟩ :=
    twelveGridActualGridTransversal_exists_permutation hcard H T
  obtain ⟨t, ht⟩ :=
    finThree_injective_eq_parameterizedTransversalPermutation σ hσinj
  refine ⟨t, ?_⟩
  have harea := twelveGridActualAffineArea_eq_zero_of_line hcard H T.line.1
    (twelveGridActualAffineGridLabel hcard H (0, σ 0))
    (twelveGridActualAffineGridLabel hcard H (1, σ 1))
    (twelveGridActualAffineGridLabel hcard H (2, σ 2))
    (hσmem 0) (hσmem 1) (hσmem 2)
  rw [twelveGridActualAffineGridLabel_coordinate,
    twelveGridActualAffineGridLabel_coordinate,
    twelveGridActualAffineGridLabel_coordinate] at harea
  change parameterizedThreeByThreeTransversalDeterminant
      (twelveGridActualColumnParameter hcard H)
      (twelveGridActualRowParameter hcard H) t = 0
  simpa [parameterizedThreeByThreeTransversalDeterminant,
    ht 0, ht 1, ht 2] using harea

/-- Two different actual determined lines coincide as soon as they contain
the same two different actual labels. -/
theorem twelveGridActualLine_eq_of_two_mem
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (L R : DeterminedLine (pivotInversion cfg p))
    (x y : AwayFrom p) (hxy : x ≠ y)
    (hxL : x ∈ lineSupport (pivotInversion cfg p) L)
    (hyL : y ∈ lineSupport (pivotInversion cfg p) L)
    (hxR : x ∈ lineSupport (pivotInversion cfg p) R)
    (hyR : y ∈ lineSupport (pivotInversion cfg p) R) :
    L = R := by
  let A : KSubset (AwayFrom p) 2 := ⟨{x, y}, by simp [hxy]⟩
  have hAonL : ∀ z ∈ A.1, pivotInversion cfg p z ∈ L.1 := by
    intro z hz
    simp only [A, Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl
    · exact mem_lineSupport.mp hxL
    · exact mem_lineSupport.mp hyL
  have hAonR : ∀ z ∈ A.1, pivotInversion cfg p z ∈ R.1 := by
    intro z hz
    simp only [A, Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl
    · exact mem_lineSupport.mp hxR
    · exact mem_lineSupport.mp hyR
  apply Subtype.ext
  exact (lineOfPair_eq_of_mem_of_direction_finrank_one
    (pivotInversion cfg p) A L.1 hAonL L.direction_finrank).symm.trans
    (lineOfPair_eq_of_mem_of_direction_finrank_one
      (pivotInversion cfg p) A R.1 hAonR R.direction_finrank)

set_option maxHeartbeats 800000 in
/-- The two census three-lines yield two *different* coded parameterized
transversals.  Equality of their codes would make them share two distinct
labelled grid crossings, hence make their determined lines equal. -/
theorem twelveGridActualTwoTransversals_parameterized
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (hcard : Fintype.card Point = 12)
    (H : TwelveGridInvertedLineCensus cfg p) :
    ∃ s t : Fin 6, s ≠ t ∧
      ParameterizedThreeByThreeGridTransversal
        (twelveGridActualColumnParameter hcard H)
        (twelveGridActualRowParameter hcard H) s ∧
      ParameterizedThreeByThreeGridTransversal
        (twelveGridActualColumnParameter hcard H)
        (twelveGridActualRowParameter hcard H) t := by
  let T0 := twelveGridActualThreeLineTransversal hcard H 0
  let T1 := twelveGridActualThreeLineTransversal hcard H 1
  obtain ⟨σ0, hσ0inj, hσ0mem⟩ :=
    twelveGridActualGridTransversal_exists_permutation hcard H T0
  obtain ⟨σ1, hσ1inj, hσ1mem⟩ :=
    twelveGridActualGridTransversal_exists_permutation hcard H T1
  obtain ⟨s, hs⟩ :=
    finThree_injective_eq_parameterizedTransversalPermutation σ0 hσ0inj
  obtain ⟨t, ht⟩ :=
    finThree_injective_eq_parameterizedTransversalPermutation σ1 hσ1inj
  have hT0 : ParameterizedThreeByThreeGridTransversal
      (twelveGridActualColumnParameter hcard H)
      (twelveGridActualRowParameter hcard H) s := by
    have harea := twelveGridActualAffineArea_eq_zero_of_line hcard H T0.line.1
      (twelveGridActualAffineGridLabel hcard H (0, σ0 0))
      (twelveGridActualAffineGridLabel hcard H (1, σ0 1))
      (twelveGridActualAffineGridLabel hcard H (2, σ0 2))
      (hσ0mem 0) (hσ0mem 1) (hσ0mem 2)
    rw [twelveGridActualAffineGridLabel_coordinate,
      twelveGridActualAffineGridLabel_coordinate,
      twelveGridActualAffineGridLabel_coordinate] at harea
    change parameterizedThreeByThreeTransversalDeterminant
        (twelveGridActualColumnParameter hcard H)
        (twelveGridActualRowParameter hcard H) s = 0
    simpa [parameterizedThreeByThreeTransversalDeterminant,
      hs 0, hs 1, hs 2] using harea
  have hT1 : ParameterizedThreeByThreeGridTransversal
      (twelveGridActualColumnParameter hcard H)
      (twelveGridActualRowParameter hcard H) t := by
    have harea := twelveGridActualAffineArea_eq_zero_of_line hcard H T1.line.1
      (twelveGridActualAffineGridLabel hcard H (0, σ1 0))
      (twelveGridActualAffineGridLabel hcard H (1, σ1 1))
      (twelveGridActualAffineGridLabel hcard H (2, σ1 2))
      (hσ1mem 0) (hσ1mem 1) (hσ1mem 2)
    rw [twelveGridActualAffineGridLabel_coordinate,
      twelveGridActualAffineGridLabel_coordinate,
      twelveGridActualAffineGridLabel_coordinate] at harea
    change parameterizedThreeByThreeTransversalDeterminant
        (twelveGridActualColumnParameter hcard H)
        (twelveGridActualRowParameter hcard H) t = 0
    simpa [parameterizedThreeByThreeTransversalDeterminant,
      ht 0, ht 1, ht 2] using harea
  refine ⟨s, t, ?_, hT0, hT1⟩
  intro hst
  have hcolumn0 : σ1 0 = σ0 0 := by
    calc
      σ1 0 = parameterizedThreeByThreeTransversalPermutation t 0 := ht 0
      _ = parameterizedThreeByThreeTransversalPermutation s 0 := by rw [hst]
      _ = σ0 0 := (hs 0).symm
  have hcolumn1 : σ1 1 = σ0 1 := by
    calc
      σ1 1 = parameterizedThreeByThreeTransversalPermutation t 1 := ht 1
      _ = parameterizedThreeByThreeTransversalPermutation s 1 := by rw [hst]
      _ = σ0 1 := (hs 1).symm
  let q0 := twelveGridActualGridPoint hcard H 0 (σ0 0)
  let q1 := twelveGridActualGridPoint hcard H 1 (σ0 1)
  have hq01 : q0 ≠ q1 := by
    intro hq
    apply twelveGridActualGridPoint_not_mem_other_row hcard H 0 (σ0 0) 1
      (by omega)
    change q0 ∈ lineSupport (pivotInversion cfg p)
      (twelveGridActualPencilLine hcard H 0 1).1
    have hq1mem : q1 ∈ lineSupport (pivotInversion cfg p)
        (twelveGridActualPencilLine hcard H 0 1).1 :=
      twelveGridActualGridPoint_mem_row hcard H 1 (σ0 1)
    exact hq ▸ hq1mem
  have hq0T0 : q0 ∈ lineSupport (pivotInversion cfg p) T0.line.1 := hσ0mem 0
  have hq1T0 : q1 ∈ lineSupport (pivotInversion cfg p) T0.line.1 := hσ0mem 1
  have hq0T1 : q0 ∈ lineSupport (pivotInversion cfg p) T1.line.1 := by
    simpa [q0, hcolumn0] using hσ1mem 0
  have hq1T1 : q1 ∈ lineSupport (pivotInversion cfg p) T1.line.1 := by
    simpa [q1, hcolumn1] using hσ1mem 1
  have hlines : T0.line.1 = T1.line.1 := twelveGridActualLine_eq_of_two_mem
    T0.line.1 T1.line.1 q0 q1 hq01 hq0T0 hq1T0 hq0T1 hq1T1
  have htransversal : T0.line = T1.line := Subtype.ext hlines
  have hzeroone : (0 : Fin 2) = 1 :=
    twelveGridActualThreeLineTransversal_line_injective hcard H htransversal
  omega

/-! ## Projective normalized secants -/

/-- The homogeneous covector of one of the twelve ordinary secants of the
standard grid.  It is deliberately kept on the point side of the existing
`RealThreeByThreeGridSecant.incident` table, so that the finite and ideal
branches of the concurrency argument use the very same twelve codes. -/
noncomputable def twelveGridStandardSecantCovector
    (s : RealThreeByThreeGridSecant) : Homogeneous3 :=
  match s.1 with
  | 0 => ![1, 1, if s.2 then -1 else 1]
  | 1 => ![1, -1, if s.2 then -1 else 1]
  | 2 => ![1, 2, if s.2 then -1 else 1]
  | 3 => ![1, -2, if s.2 then -1 else 1]
  | 4 => ![2, 1, if s.2 then -1 else 1]
  | 5 => ![2, -1, if s.2 then -1 else 1]

/-- The determinant of three homogeneous point representatives, written
explicitly to keep all later projective transport elementary over `ℝ`. -/
def twelveGridHomogeneousDeterminant
    (u v w : Homogeneous3) : ℝ :=
  u 0 * (v 1 * w 2 - v 2 * w 1) -
    u 1 * (v 0 * w 2 - v 2 * w 0) +
      u 2 * (v 0 * w 1 - v 1 * w 0)

theorem twelveGridHomogeneousDeterminant_smul_left
    (c : ℝ) (u v w : Homogeneous3) :
    twelveGridHomogeneousDeterminant (c • u) v w =
      c * twelveGridHomogeneousDeterminant u v w := by
  simp [twelveGridHomogeneousDeterminant, smul_eq_mul]
  ring

theorem twelveGridHomogeneousDeterminant_smul_middle
    (c : ℝ) (u v w : Homogeneous3) :
    twelveGridHomogeneousDeterminant u (c • v) w =
      c * twelveGridHomogeneousDeterminant u v w := by
  simp [twelveGridHomogeneousDeterminant, smul_eq_mul]
  ring

theorem twelveGridHomogeneousDeterminant_smul_right
    (c : ℝ) (u v w : Homogeneous3) :
    twelveGridHomogeneousDeterminant u v (c • w) =
      c * twelveGridHomogeneousDeterminant u v w := by
  simp [twelveGridHomogeneousDeterminant, smul_eq_mul]
  ring

theorem twelveGridHomogeneousDeterminant_swap_first_two
    (u v w : Homogeneous3) :
    twelveGridHomogeneousDeterminant v u w =
      -twelveGridHomogeneousDeterminant u v w := by
  simp [twelveGridHomogeneousDeterminant]
  ring

/-- A nonzero covector has a two-dimensional kernel, so three homogeneous
points on that covector have zero determinant.  The coordinate proof avoids
adding an abstract rank hypothesis to the actual grid endpoint. -/
theorem twelveGridHomogeneousDeterminant_eq_zero_of_common_covector
    (ell u v w : Homogeneous3) (hell : ell ≠ 0)
    (hu : ell ⬝ᵥ u = 0) (hv : ell ⬝ᵥ v = 0)
    (hw : ell ⬝ᵥ w = 0) :
    twelveGridHomogeneousDeterminant u v w = 0 := by
  have hzero : ell 0 * twelveGridHomogeneousDeterminant u v w = 0 := by
    calc
      ell 0 * twelveGridHomogeneousDeterminant u v w =
          (ell ⬝ᵥ u) * (v 1 * w 2 - v 2 * w 1) -
            (ell ⬝ᵥ v) * (u 1 * w 2 - u 2 * w 1) +
              (ell ⬝ᵥ w) * (u 1 * v 2 - u 2 * v 1) := by
        simp [twelveGridHomogeneousDeterminant, dotProduct,
          Fin.sum_univ_three]
        ring
      _ = 0 := by rw [hu, hv, hw]; ring
  have hone : ell 1 * twelveGridHomogeneousDeterminant u v w = 0 := by
    calc
      ell 1 * twelveGridHomogeneousDeterminant u v w =
          -(ell ⬝ᵥ u) * (v 0 * w 2 - v 2 * w 0) +
            (ell ⬝ᵥ v) * (u 0 * w 2 - u 2 * w 0) -
              (ell ⬝ᵥ w) * (u 0 * v 2 - u 2 * v 0) := by
        simp [twelveGridHomogeneousDeterminant, dotProduct,
          Fin.sum_univ_three]
        ring
      _ = 0 := by rw [hu, hv, hw]; ring
  have htwo : ell 2 * twelveGridHomogeneousDeterminant u v w = 0 := by
    calc
      ell 2 * twelveGridHomogeneousDeterminant u v w =
          (ell ⬝ᵥ u) * (v 0 * w 1 - v 1 * w 0) -
            (ell ⬝ᵥ v) * (u 0 * w 1 - u 1 * w 0) +
              (ell ⬝ᵥ w) * (u 0 * v 1 - u 1 * v 0) := by
        simp [twelveGridHomogeneousDeterminant, dotProduct,
          Fin.sum_univ_three]
        ring
      _ = 0 := by rw [hu, hv, hw]; ring
  by_cases h0 : ell 0 = 0
  · by_cases h1 : ell 1 = 0
    · have h2 : ell 2 ≠ 0 := by
        intro h2
        apply hell
        ext i
        fin_cases i <;> simp [h0, h1, h2]
      exact (mul_eq_zero.mp htwo).resolve_left h2
    · exact (mul_eq_zero.mp hone).resolve_left h1
  · exact (mul_eq_zero.mp hzero).resolve_left h0

/-- The homogeneous lift of the coordinatewise affine relabelling.  The
translation is multiplied by the last coordinate, hence this is a genuine
projective linear map and also acts on ideal points. -/
noncomputable def twelveGridParameterizedNormalizeHomogeneous
    (ra rb : ParameterizedThreeByThreeGridRelabelling) (z : Homogeneous3) :
    Homogeneous3 :=
  ![ra.scale * z 0 + ra.normalizer 0 * z 2,
    rb.scale * z 1 + rb.normalizer 0 * z 2, z 2]

theorem twelveGridParameterizedNormalizeHomogeneous_smul
    (ra rb : ParameterizedThreeByThreeGridRelabelling)
    (c : ℝ) (z : Homogeneous3) :
    twelveGridParameterizedNormalizeHomogeneous ra rb (c • z) =
      c • twelveGridParameterizedNormalizeHomogeneous ra rb z := by
  ext i
  fin_cases i <;>
    simp [twelveGridParameterizedNormalizeHomogeneous,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      smul_eq_mul] <;>
    ring

theorem twelveGridParameterizedNormalizeHomogeneous_homogeneousLift
    (ra rb : ParameterizedThreeByThreeGridRelabelling) (z : ℝ × ℝ) :
    twelveGridParameterizedNormalizeHomogeneous ra rb
      (homogeneousLift (twelveGridAffinePairPoint2 z)) =
      homogeneousLift (twelveGridAffinePairPoint2
        (parameterizedThreeByThreeNormalizePoint ra rb z)) := by
  cases ra <;> cases rb <;>
    ext i <;> fin_cases i <;>
    simp [twelveGridParameterizedNormalizeHomogeneous,
      parameterizedThreeByThreeNormalizePoint,
      ParameterizedThreeByThreeGridRelabelling.normalizer,
      ParameterizedThreeByThreeGridRelabelling.scale,
      homogeneousLift, twelveGridAffinePairPoint2,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two] <;>
    ring

theorem twelveGridParameterizedNormalizeHomogeneous_determinant
    (ra rb : ParameterizedThreeByThreeGridRelabelling)
    (u v w : Homogeneous3) :
    twelveGridHomogeneousDeterminant
      (twelveGridParameterizedNormalizeHomogeneous ra rb u)
      (twelveGridParameterizedNormalizeHomogeneous ra rb v)
      (twelveGridParameterizedNormalizeHomogeneous ra rb w) =
      (ra.scale * rb.scale) * twelveGridHomogeneousDeterminant u v w := by
  cases ra <;> cases rb <;>
    simp [twelveGridHomogeneousDeterminant,
      twelveGridParameterizedNormalizeHomogeneous,
      ParameterizedThreeByThreeGridRelabelling.normalizer,
      ParameterizedThreeByThreeGridRelabelling.scale,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two] <;>
    ring

theorem twelveGridParameterizedNormalizeHomogeneous_determinant_eq_zero_iff
    (ra rb : ParameterizedThreeByThreeGridRelabelling)
    (u v w : Homogeneous3) :
    twelveGridHomogeneousDeterminant
      (twelveGridParameterizedNormalizeHomogeneous ra rb u)
      (twelveGridParameterizedNormalizeHomogeneous ra rb v)
      (twelveGridParameterizedNormalizeHomogeneous ra rb w) = 0 ↔
      twelveGridHomogeneousDeterminant u v w = 0 := by
  rw [twelveGridParameterizedNormalizeHomogeneous_determinant]
  have hra : ra.scale ≠ 0 := by
    cases ra <;>
      norm_num [ParameterizedThreeByThreeGridRelabelling.scale]
  have hrb : rb.scale ≠ 0 := by
    cases rb <;>
      norm_num [ParameterizedThreeByThreeGridRelabelling.scale]
  constructor
  · intro h
    exact (mul_eq_zero.mp h).resolve_left (mul_ne_zero hra hrb)
  · intro h
    rw [h, mul_zero]

theorem twelveGridStandardSecantCovector_incident
    (s : RealThreeByThreeGridSecant) (z : ℝ × ℝ) :
    twelveGridStandardSecantCovector s ⬝ᵥ
        homogeneousLift (twelveGridAffinePairPoint2 z) = 0 ↔
      s.incident z.1 z.2 := by
  rcases s with ⟨i, sign⟩
  fin_cases i <;> cases sign <;>
    norm_num [twelveGridStandardSecantCovector,
      RealThreeByThreeGridSecant.incident, homogeneousLift,
      twelveGridAffinePairPoint2, dotProduct, Fin.sum_univ_three,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two] <;>
    constructor <;> intro h <;> linarith

theorem twelveGridStandardSecantCovector_of_endpoint_determinant
    (s : RealThreeByThreeGridSecant) (z : Homogeneous3)
    (hdet : twelveGridHomogeneousDeterminant
      (homogeneousLift (twelveGridAffinePairPoint2
        (twelveGridPoint (twelveGridSecantEndpoints s).1)))
      (homogeneousLift (twelveGridAffinePairPoint2
        (twelveGridPoint (twelveGridSecantEndpoints s).2))) z = 0) :
    twelveGridStandardSecantCovector s ⬝ᵥ z = 0 := by
  rcases s with ⟨i, sign⟩
  fin_cases i <;> cases sign <;>
    norm_num [twelveGridHomogeneousDeterminant,
      twelveGridStandardSecantCovector, twelveGridSecantEndpoints,
      twelveGridPoint, twelveGridCoordinate, homogeneousLift,
      twelveGridAffinePairPoint2, dotProduct, Fin.sum_univ_three,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two] at hdet ⊢ <;>
    linarith

/-! ### The actual pivot and arbitrary actual line covectors -/

/-- The raw line-covector incidence lemma also applies to an arbitrary
geometric point of the affine plane, rather than only to a selected label.
This is what retains the original inversion pivot in the projective tail. -/
theorem twelveGridActualLineCovector_incident_point_iff
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (hcard : Fintype.card Point = 12)
    (H : TwelveGridInvertedLineCensus cfg p)
    (L : DeterminedLine (pivotInversion cfg p)) (x : Point2) :
    twelveGridActualLineCovector hcard H L ⬝ᵥ homogeneousLift x = 0 ↔
      x ∈ L.1 := by
  have hmem : affinePointToProjective x ∈
      determinedProjectiveLine (pivotInversion cfg p) L ↔ x ∈ L.1 := by
    change affinePointToProjective x ∈
        projectiveChordLine (pivotInversion cfg p) L.spanningPair ↔ x ∈ L.1
    rw [affinePoint_mem_projectiveChordLine_iff, L.spanningPair_spec]
  calc
    twelveGridActualLineCovector hcard H L ⬝ᵥ homogeneousLift x = 0 ↔
        homogeneousLift x ⬝ᵥ twelveGridActualLineCovector hcard H L = 0 := by
      rw [dotProduct_comm]
    _ ↔ affinePointToProjective x ∈ Projectivization.mk ℝ
        (twelveGridActualLineCovector hcard H L)
        (twelveGridActualLineCovector_ne_zero hcard H L) := by
      change _ ↔ Projectivization.orthogonal
        (Projectivization.mk ℝ (homogeneousLift x) (homogeneousLift_ne_zero x))
        (Projectivization.mk ℝ (twelveGridActualLineCovector hcard H L)
          (twelveGridActualLineCovector_ne_zero hcard H L))
      rw [Projectivization.orthogonal_mk]
    _ ↔ affinePointToProjective x ∈
        determinedProjectiveLine (pivotInversion cfg p) L := by
      simp [twelveGridActualLineCovector]
    _ ↔ x ∈ L.1 := hmem

/-- The canonical affine-chart representative of the original inversion
centre.  It need not be finite in this chart, so it stays homogeneous. -/
noncomputable def twelveGridActualAffinePivot
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (hcard : Fintype.card Point = 12)
    (H : TwelveGridInvertedLineCensus cfg p) : Homogeneous3 :=
  twelveGridActualAffineHomogeneous hcard H (homogeneousLift (cfg p))

theorem twelveGridActualAffinePivot_ne_zero
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (hcard : Fintype.card Point = 12)
    (H : TwelveGridInvertedLineCensus cfg p) :
    twelveGridActualAffinePivot hcard H ≠ 0 := by
  unfold twelveGridActualAffinePivot
  exact twelveGridActualAffineHomogeneous_ne_zero hcard H _
    (homogeneousLift_ne_zero _)

theorem twelveGridActualAffineHomogeneous_smul
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (hcard : Fintype.card Point = 12)
    (H : TwelveGridInvertedLineCensus cfg p)
    (c : ℝ) (x : Homogeneous3) :
    twelveGridActualAffineHomogeneous hcard H (c • x) =
      c • twelveGridActualAffineHomogeneous hcard H x := by
  unfold twelveGridActualAffineHomogeneous projectivePointTransform
  rw [smul_comm, Matrix.mulVec_smul]

theorem twelveGridActualAffineHomogeneous_injective
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (hcard : Fintype.card Point = 12)
    (H : TwelveGridInvertedLineCensus cfg p) :
    Function.Injective (twelveGridActualAffineHomogeneous hcard H) := by
  intro x y hxy
  have hframe : projectivePointTransform
      (twelveGridActualCovectorFrame hcard H).G x =
      projectivePointTransform (twelveGridActualCovectorFrame hcard H).G y := by
    apply twelveGridAffinePostPoint_injective
    simpa [twelveGridActualAffineHomogeneous] using hxy
  unfold projectivePointTransform at hframe
  calc
    x = (twelveGridActualCovectorFrame hcard H).G⁻¹ •
        ((twelveGridActualCovectorFrame hcard H).G • x) := by simp
    _ = (twelveGridActualCovectorFrame hcard H).G⁻¹ •
        ((twelveGridActualCovectorFrame hcard H).G • y) :=
      congrArg ((twelveGridActualCovectorFrame hcard H).G⁻¹ • ·) hframe
    _ = y := by simp

/-- Any actual ordinary line containing the original pivot remains incident
with the homogeneous pivot after the actual covector-frame chart. -/
theorem twelveGridActualAffineLineCovector_incident_pivot
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (hcard : Fintype.card Point = 12)
    (H : TwelveGridInvertedLineCensus cfg p)
    (L : DeterminedLine (pivotInversion cfg p)) (hpivot : cfg p ∈ L.1) :
    twelveGridActualAffineLineCovector hcard H L ⬝ᵥ
      twelveGridActualAffinePivot hcard H = 0 := by
  change twelveGridActualAffineCovector hcard H
      (twelveGridActualLineCovector hcard H L) ⬝ᵥ
      twelveGridActualAffineHomogeneous hcard H
        (homogeneousLift (cfg p)) = 0
  rw [twelveGridActualAffineCovector_dot]
  exact (twelveGridActualLineCovector_incident_point_iff hcard H L (cfg p)).2
    hpivot

/-- Dehomogenization for a nonzero-last-coordinate homogeneous vector. -/
noncomputable def twelveGridHomogeneousCoordinate (z : Homogeneous3) : ℝ × ℝ :=
  (z 0 / z 2, z 1 / z 2)

theorem twelveGridHomogeneous_eq_scale_homogeneousLift
    (z : Homogeneous3) (hz : z 2 ≠ 0) :
    z = z 2 • homogeneousLift
      (twelveGridAffinePairPoint2 (twelveGridHomogeneousCoordinate z)) := by
  ext i
  fin_cases i
  · simp [homogeneousLift, twelveGridAffinePairPoint2,
      twelveGridHomogeneousCoordinate]
    rw [mul_comm, div_mul_cancel₀ _ hz]
  · simp [homogeneousLift, twelveGridAffinePairPoint2,
      twelveGridHomogeneousCoordinate]
    rw [mul_comm, div_mul_cancel₀ _ hz]
  · simp [homogeneousLift, twelveGridAffinePairPoint2]

theorem twelveGridStandardSecant_incident_of_finite_homogeneous
    (s : RealThreeByThreeGridSecant) (z : Homogeneous3) (hz : z 2 ≠ 0)
    (hinc : twelveGridStandardSecantCovector s ⬝ᵥ z = 0) :
    s.incident (twelveGridHomogeneousCoordinate z).1
      (twelveGridHomogeneousCoordinate z).2 := by
  apply (twelveGridStandardSecantCovector_incident s
    (twelveGridHomogeneousCoordinate z)).mp
  rw [twelveGridHomogeneous_eq_scale_homogeneousLift z hz] at hinc
  rw [dotProduct_smul, smul_eq_mul] at hinc
  exact (mul_eq_zero.mp hinc).resolve_left hz

set_option maxHeartbeats 800000 in
/-- At an ideal point, all standard secants incident with that point have
the same direction.  This is the homogeneous companion to the finite
`external_not_three_distinct` calculation. -/
theorem twelveGridStandardSecant_same_direction_of_ideal
    (s t : RealThreeByThreeGridSecant) (z : Homogeneous3)
    (hz : z 2 = 0) (hzne : z ≠ 0)
    (hs : twelveGridStandardSecantCovector s ⬝ᵥ z = 0)
    (ht : twelveGridStandardSecantCovector t ⬝ᵥ z = 0) :
    s.direction = t.direction := by
  rcases s with ⟨i, si⟩
  rcases t with ⟨j, sj⟩
  have hij : i = j := by
    by_contra hne
    fin_cases i <;> fin_cases j
    all_goals try { exact hne rfl }
    all_goals
      norm_num [twelveGridStandardSecantCovector, dotProduct,
        Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_two, hz] at hs ht
      apply hzne
      ext k
      fin_cases k
      · change z 0 = 0
        linarith [hs, ht]
      · change z 1 = 0
        linarith [hs, ht]
      · change z 2 = 0
        exact hz
  exact (RealThreeByThreeGridSecant.direction_eq_iff _ _).2 hij

/-! ### The relabelled actual grid and the external pivot -/

theorem parameterizedThreeByThreeStandardPoint_eq_twelveGridPoint
    (ij : Fin 3 × Fin 3) :
    parameterizedThreeByThreeStandardPoint ij = twelveGridPoint ij := by
  rfl

theorem parameterizedThreeByThreeGridRelabelling_index_injective
    (r : ParameterizedThreeByThreeGridRelabelling) :
    Function.Injective r.index := by
  cases r <;> intro i j hij <;> fin_cases i <;> fin_cases j <;>
    simpa [ParameterizedThreeByThreeGridRelabelling.index,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two] using hij

theorem parameterizedThreeByThreeGridRelabelling_index_surjective
    (r : ParameterizedThreeByThreeGridRelabelling) :
    Function.Surjective r.index := by
  cases r
  · intro i
    fin_cases i
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
    · exact ⟨2, rfl⟩
  · intro i
    fin_cases i
    · exact ⟨2, rfl⟩
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
  · intro i
    fin_cases i
    · exact ⟨0, rfl⟩
    · exact ⟨2, rfl⟩
    · exact ⟨1, rfl⟩

theorem parameterizedThreeByThreeNormalizedIndex_injective
    (ra rb : ParameterizedThreeByThreeGridRelabelling) :
    Function.Injective (parameterizedThreeByThreeNormalizedIndex ra rb) := by
  rintro ⟨r, s⟩ ⟨r', s'⟩ h
  apply Prod.ext
  · exact parameterizedThreeByThreeGridRelabelling_index_injective ra
      (congrArg Prod.fst h)
  · exact parameterizedThreeByThreeGridRelabelling_index_injective rb
      (congrArg Prod.snd h)

theorem parameterizedThreeByThreeNormalizePoint_injective
    (ra rb : ParameterizedThreeByThreeGridRelabelling) :
    Function.Injective (parameterizedThreeByThreeNormalizePoint ra rb) := by
  rintro ⟨x, y⟩ ⟨x', y'⟩ h
  apply Prod.ext
  · have hx := congrArg Prod.fst h
    cases ra <;>
      simp [parameterizedThreeByThreeNormalizePoint,
        ParameterizedThreeByThreeGridRelabelling.normalizer] at hx <;>
      linarith
  · have hy := congrArg Prod.snd h
    cases rb <;>
      simp [parameterizedThreeByThreeNormalizePoint,
        ParameterizedThreeByThreeGridRelabelling.normalizer] at hy <;>
      linarith

theorem twelveGridParameterizedNormalizeHomogeneous_coordinate
    (ra rb : ParameterizedThreeByThreeGridRelabelling)
    (z : Homogeneous3) (hz : z 2 ≠ 0) :
    twelveGridHomogeneousCoordinate
      (twelveGridParameterizedNormalizeHomogeneous ra rb z) =
      parameterizedThreeByThreeNormalizePoint ra rb
        (twelveGridHomogeneousCoordinate z) := by
  apply Prod.ext <;> cases ra <;> cases rb <;>
    simp [twelveGridHomogeneousCoordinate,
      twelveGridParameterizedNormalizeHomogeneous,
      parameterizedThreeByThreeNormalizePoint,
      ParameterizedThreeByThreeGridRelabelling.normalizer,
      ParameterizedThreeByThreeGridRelabelling.scale,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two] <;>
    field_simp [hz] <;>
    ring

theorem twelveGridParameterizedNormalizeHomogeneous_ne_zero
    (ra rb : ParameterizedThreeByThreeGridRelabelling)
    (z : Homogeneous3) (hz : z ≠ 0) :
    twelveGridParameterizedNormalizeHomogeneous ra rb z ≠ 0 := by
  intro hzero
  have htwo : z 2 = 0 := by
    have h := congrFun hzero (2 : Fin 3)
    simpa [twelveGridParameterizedNormalizeHomogeneous,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two] using h
  have hra : ra.scale ≠ 0 := by
    cases ra <;>
      norm_num [ParameterizedThreeByThreeGridRelabelling.scale]
  have hrb : rb.scale ≠ 0 := by
    cases rb <;>
      norm_num [ParameterizedThreeByThreeGridRelabelling.scale]
  have hleft : ra.scale * z 0 = 0 := by
    have h := congrFun hzero (0 : Fin 3)
    simpa [twelveGridParameterizedNormalizeHomogeneous, htwo,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two] using h
  have hright : rb.scale * z 1 = 0 := by
    have h := congrFun hzero (1 : Fin 3)
    simpa [twelveGridParameterizedNormalizeHomogeneous, htwo,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two] using h
  have hzero0 : z 0 = 0 := (mul_eq_zero.mp hleft).resolve_left hra
  have hzero1 : z 1 = 0 := (mul_eq_zero.mp hright).resolve_left hrb
  apply hz
  ext i
  fin_cases i <;> simp [hzero0, hzero1, htwo]

/-- The relabelled homogeneous image of any labelled grid crossing is the
standard-grid lift, up to its already-recorded nonzero affine scale. -/
theorem twelveGridActualNormalizedGridPoint
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (hcard : Fintype.card Point = 12)
    (H : TwelveGridInvertedLineCensus cfg p)
    (ra rb : ParameterizedThreeByThreeGridRelabelling)
    (ha : twelveGridActualColumnParameter hcard H = ra.parameter)
    (hb : twelveGridActualRowParameter hcard H = rb.parameter)
    (rs : Fin 3 × Fin 3) :
    twelveGridParameterizedNormalizeHomogeneous ra rb
      (twelveGridActualAffinePoint hcard H
        (twelveGridActualGridPoint hcard H rs.1 rs.2)) =
      twelveGridActualAffinePoint hcard H
        (twelveGridActualGridPoint hcard H rs.1 rs.2) 2 •
        homogeneousLift (twelveGridAffinePairPoint2
          (twelveGridPoint
            (parameterizedThreeByThreeNormalizedIndex ra rb rs))) := by
  let q := twelveGridActualAffineGridLabel hcard H rs
  have hscale := twelveGridActualAffinePoint_eq_scale_homogeneousLift
    hcard H q
  have hcoordinate := twelveGridActualAffineGridLabel_coordinate hcard H rs
  change twelveGridParameterizedNormalizeHomogeneous ra rb
      (twelveGridActualAffinePoint hcard H q.1) = _
  rw [hscale, twelveGridParameterizedNormalizeHomogeneous_smul,
    twelveGridParameterizedNormalizeHomogeneous_homogeneousLift,
    hcoordinate, ha, hb,
    parameterizedThreeByThreeNormalize_gridPoint]
  simpa only [q, twelveGridActualAffineGridLabel,
    parameterizedThreeByThreeStandardPoint_eq_twelveGridPoint]

/-- A finite original pivot can never acquire the affine coordinates of a
labelled grid crossing: equality would invert one of the surviving labels
back to the deleted pivot. -/
theorem twelveGridActualAffinePivot_coordinate_ne_grid
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (hcard : Fintype.card Point = 12)
    (H : TwelveGridInvertedLineCensus cfg p)
    (hpivot : twelveGridActualAffinePivot hcard H 2 ≠ 0)
    (rs : Fin 3 × Fin 3) :
    twelveGridHomogeneousCoordinate (twelveGridActualAffinePivot hcard H) ≠
      threeByThreeParameterizedGridPoint
        (twelveGridActualColumnParameter hcard H)
        (twelveGridActualRowParameter hcard H) rs := by
  intro hcoordinate
  let q := twelveGridActualAffineGridLabel hcard H rs
  have hpivotScale := twelveGridHomogeneous_eq_scale_homogeneousLift
    (twelveGridActualAffinePivot hcard H) hpivot
  have hqScale := twelveGridActualAffinePoint_eq_scale_homogeneousLift
    hcard H q
  have hqcoordinate := twelveGridActualAffineGridLabel_coordinate hcard H rs
  have hqtwo : twelveGridActualAffinePoint hcard H q.1 2 ≠ 0 := q.2
  have hqScaleParam : twelveGridActualAffinePoint hcard H q.1 =
      twelveGridActualAffinePoint hcard H q.1 2 •
        homogeneousLift (twelveGridAffinePairPoint2
          (threeByThreeParameterizedGridPoint
            (twelveGridActualColumnParameter hcard H)
            (twelveGridActualRowParameter hcard H) rs)) :=
    hqScale.trans (congrArg (fun z =>
      twelveGridActualAffinePoint hcard H q.1 2 •
        homogeneousLift (twelveGridAffinePairPoint2 z)) hqcoordinate)
  have hsameLift : twelveGridActualAffinePivot hcard H =
      twelveGridActualAffinePivot hcard H 2 •
        homogeneousLift (twelveGridAffinePairPoint2
          (threeByThreeParameterizedGridPoint
            (twelveGridActualColumnParameter hcard H)
            (twelveGridActualRowParameter hcard H) rs)) := by
    exact hpivotScale.trans (congrArg (fun z =>
      twelveGridActualAffinePivot hcard H 2 •
        homogeneousLift (twelveGridAffinePairPoint2 z)) hcoordinate)
  have hscaled : twelveGridActualAffinePivot hcard H =
      (twelveGridActualAffinePivot hcard H 2 /
        twelveGridActualAffinePoint hcard H q.1 2) •
        twelveGridActualAffinePoint hcard H q.1 := by
    calc
      twelveGridActualAffinePivot hcard H =
          twelveGridActualAffinePivot hcard H 2 •
            homogeneousLift (twelveGridAffinePairPoint2
              (threeByThreeParameterizedGridPoint
                (twelveGridActualColumnParameter hcard H)
                (twelveGridActualRowParameter hcard H) rs)) := hsameLift
      _ = (twelveGridActualAffinePivot hcard H 2 /
            twelveGridActualAffinePoint hcard H q.1 2) •
          (twelveGridActualAffinePoint hcard H q.1 2 •
            homogeneousLift (twelveGridAffinePairPoint2
              (threeByThreeParameterizedGridPoint
                (twelveGridActualColumnParameter hcard H)
                (twelveGridActualRowParameter hcard H) rs))) := by
        rw [smul_smul]
        congr 1
        field_simp [hqtwo]
      _ = (twelveGridActualAffinePivot hcard H 2 /
            twelveGridActualAffinePoint hcard H q.1 2) •
          twelveGridActualAffinePoint hcard H q.1 := by
        rw [← hqScaleParam]
  have hbefore : homogeneousLift (cfg p) =
      (twelveGridActualAffinePivot hcard H 2 /
        twelveGridActualAffinePoint hcard H q.1 2) •
        homogeneousLift (pivotInversion cfg p q.1) := by
    apply twelveGridActualAffineHomogeneous_injective hcard H
    change twelveGridActualAffinePivot hcard H = _
    rw [twelveGridActualAffineHomogeneous_smul]
    exact hscaled
  have hscaleOne : twelveGridActualAffinePivot hcard H 2 /
      twelveGridActualAffinePoint hcard H q.1 2 = 1 := by
    have hlast := congrFun hbefore (2 : Fin 3)
    simpa using hlast.symm
  have hcenter : cfg p = pivotInversion cfg p q.1 := by
    apply homogeneousLift_injective
    simpa [hscaleOne] using hbefore
  change cfg p = EuclideanGeometry.inversion (cfg p) 1 (cfg q.1) at hcenter
  apply q.1.2
  apply cfg.injective
  exact (EuclideanGeometry.center_eq_inversion one_ne_zero).mp hcenter

theorem twelveGridActualNormalizedPivot_external
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (hcard : Fintype.card Point = 12)
    (H : TwelveGridInvertedLineCensus cfg p)
    (ra rb : ParameterizedThreeByThreeGridRelabelling)
    (ha : twelveGridActualColumnParameter hcard H = ra.parameter)
    (hb : twelveGridActualRowParameter hcard H = rb.parameter)
    (hpivot : twelveGridActualAffinePivot hcard H 2 ≠ 0) :
    RealThreeByThreeGridExternal
      (twelveGridHomogeneousCoordinate
        (twelveGridParameterizedNormalizeHomogeneous ra rb
          (twelveGridActualAffinePivot hcard H))).1
      (twelveGridHomogeneousCoordinate
        (twelveGridParameterizedNormalizeHomogeneous ra rb
          (twelveGridActualAffinePivot hcard H))).2 := by
  let P := twelveGridActualAffinePivot hcard H
  have hcoordinate := twelveGridParameterizedNormalizeHomogeneous_coordinate
    ra rb P hpivot
  by_contra hnot
  simp only [RealThreeByThreeGridExternal] at hnot
  have hxi : ∃ i : Fin 3,
      (twelveGridHomogeneousCoordinate
        (twelveGridParameterizedNormalizeHomogeneous ra rb P)).1 =
        twelveGridCoordinate i := by
    by_contra hx
    apply hnot
    left
    constructor
    · intro hm
      apply hx
      exact ⟨0, by simpa [twelveGridCoordinate] using hm⟩
    constructor
    · intro hz
      apply hx
      exact ⟨1, by simpa [twelveGridCoordinate] using hz⟩
    · intro hp
      apply hx
      refine ⟨2, ?_⟩
      norm_num [twelveGridCoordinate]
      exact hp
  have hyi : ∃ j : Fin 3,
      (twelveGridHomogeneousCoordinate
        (twelveGridParameterizedNormalizeHomogeneous ra rb P)).2 =
        twelveGridCoordinate j := by
    by_contra hy
    apply hnot
    right
    constructor
    · intro hm
      apply hy
      exact ⟨0, by simpa [twelveGridCoordinate] using hm⟩
    constructor
    · intro hz
      apply hy
      exact ⟨1, by simpa [twelveGridCoordinate] using hz⟩
    · intro hp
      apply hy
      refine ⟨2, ?_⟩
      norm_num [twelveGridCoordinate]
      exact hp
  obtain ⟨i, hi⟩ := hxi
  obtain ⟨j, hj⟩ := hyi
  obtain ⟨r, hr⟩ := parameterizedThreeByThreeGridRelabelling_index_surjective ra i
  obtain ⟨s, hs⟩ := parameterizedThreeByThreeGridRelabelling_index_surjective rb j
  have hnormalizedGrid := parameterizedThreeByThreeNormalize_gridPoint ra rb (r, s)
  have hnormalizedGrid' :
      parameterizedThreeByThreeNormalizePoint ra rb
        (threeByThreeParameterizedGridPoint
          (twelveGridActualColumnParameter hcard H)
          (twelveGridActualRowParameter hcard H) (r, s)) =
      twelveGridHomogeneousCoordinate
        (twelveGridParameterizedNormalizeHomogeneous ra rb P) := by
    rw [ha, hb, hnormalizedGrid]
    apply Prod.ext
    · simpa [parameterizedThreeByThreeStandardPoint,
        twelveGridPoint, twelveGridCoordinate,
        parameterizedThreeByThreeNormalizedIndex, hr] using hi.symm
    · simpa [parameterizedThreeByThreeStandardPoint,
        twelveGridPoint, twelveGridCoordinate,
        parameterizedThreeByThreeNormalizedIndex, hs] using hj.symm
  have hraw : threeByThreeParameterizedGridPoint
      (twelveGridActualColumnParameter hcard H)
      (twelveGridActualRowParameter hcard H) (r, s) =
      twelveGridHomogeneousCoordinate P := by
    apply parameterizedThreeByThreeNormalizePoint_injective ra rb
    rw [hnormalizedGrid', hcoordinate]
  exact twelveGridActualAffinePivot_coordinate_ne_grid hcard H hpivot (r, s)
    hraw.symm

/-! ### Recovering a support incidence from a transported determinant -/

theorem twelveGridHomogeneousDeterminant_eq_matrix_det
    (u v w : Homogeneous3) :
    twelveGridHomogeneousDeterminant u v w = Matrix.det ![u, v, w] := by
  simp [twelveGridHomogeneousDeterminant, Matrix.det_fin_three]
  ring

theorem twelveGridHomogeneous_dot_cross_eq_determinant
    (u v w : Homogeneous3) :
    w ⬝ᵥ crossProduct u v = twelveGridHomogeneousDeterminant u v w := by
  simp [twelveGridHomogeneousDeterminant, cross_apply, dotProduct,
    Fin.sum_univ_three]
  ring

/-- Two finite homogeneous representatives with different dehomogenized
coordinates represent different projective points. -/
theorem twelveGridFiniteProjective_ne_of_coordinate_ne
    (u v : Homogeneous3) (hu : u 2 ≠ 0) (hv : v 2 ≠ 0)
    (hcoord : twelveGridHomogeneousCoordinate u ≠
      twelveGridHomogeneousCoordinate v) :
    Projectivization.mk ℝ u (by
      intro h
      apply hu
      simpa [h]) ≠
      Projectivization.mk ℝ v (by
        intro h
        apply hv
        simpa [h]) := by
  intro hprojective
  obtain ⟨c, hc⟩ := (Projectivization.mk_eq_mk_iff' ℝ u v
    (by
      intro h
      apply hu
      simpa [h])
    (by
      intro h
      apply hv
      simpa [h])).mp hprojective
  have hc0 : c * v 0 = u 0 := by
    simpa [smul_eq_mul] using congrFun hc (0 : Fin 3)
  have hc1 : c * v 1 = u 1 := by
    simpa [smul_eq_mul] using congrFun hc (1 : Fin 3)
  have hc2 : c * v 2 = u 2 := by
    simpa [smul_eq_mul] using congrFun hc (2 : Fin 3)
  apply hcoord
  apply Prod.ext
  · unfold twelveGridHomogeneousCoordinate
    field_simp [hu, hv]
    rw [← hc0, ← hc2]
    ring
  · unfold twelveGridHomogeneousCoordinate
    field_simp [hu, hv]
    rw [← hc1, ← hc2]
    ring

/-- If a nonzero line covector contains two distinct finite homogeneous
points, determinant-zero for a third nonzero homogeneous point recovers
its incidence with that same covector.  This is the projective uniqueness
bridge used below for actual ordinary supports of cardinality two. -/
theorem twelveGridCovector_incident_of_homogeneous_determinant
    (ell u v w : Homogeneous3) (hell : ell ≠ 0)
    (hu : ell ⬝ᵥ u = 0) (hv : ell ⬝ᵥ v = 0)
    (huFinite : u 2 ≠ 0) (hvFinite : v 2 ≠ 0)
    (huv : twelveGridHomogeneousCoordinate u ≠
      twelveGridHomogeneousCoordinate v)
    (hwNe : w ≠ 0)
    (hdet : twelveGridHomogeneousDeterminant u v w = 0) :
    ell ⬝ᵥ w = 0 := by
  have huNe : u ≠ 0 := by
    intro hzero
    apply huFinite
    simpa [hzero] using congrFun hzero (2 : Fin 3)
  have hvNe : v ≠ 0 := by
    intro hzero
    apply hvFinite
    simpa [hzero] using congrFun hzero (2 : Fin 3)
  let U : RealProjectivePlane := Projectivization.mk ℝ u huNe
  let V : RealProjectivePlane := Projectivization.mk ℝ v hvNe
  let W : RealProjectivePlane := Projectivization.mk ℝ w hwNe
  let E : RealProjectivePlane := Projectivization.mk ℝ ell hell
  have hUV : U ≠ V := by
    simpa [U, V] using
      twelveGridFiniteProjective_ne_of_coordinate_ne u v huFinite hvFinite huv
  have hU : Projectivization.orthogonal U E := by
    change u ⬝ᵥ ell = 0
    rw [dotProduct_comm]
    exact hu
  have hV : Projectivization.orthogonal V E := by
    change v ⬝ᵥ ell = 0
    rw [dotProduct_comm]
    exact hv
  have hline : E = Projectivization.cross U V :=
    projectiveCovector_eq_cross_of_orthogonal hUV hU hV
  have hWcross : Projectivization.orthogonal W
      (Projectivization.cross U V) := by
    have hcrossNe : crossProduct u v ≠ 0 :=
      mt (Projectivization.mk_eq_mk_iff_crossProduct_eq_zero huNe hvNe).mpr hUV
    change Projectivization.orthogonal
      (Projectivization.mk ℝ w hwNe)
      (Projectivization.cross (Projectivization.mk ℝ u huNe)
        (Projectivization.mk ℝ v hvNe))
    rw [Projectivization.cross_mk_of_ne huNe hvNe hUV,
      Projectivization.orthogonal_mk]
    simpa [twelveGridHomogeneous_dot_cross_eq_determinant] using hdet
  rw [← hline] at hWcross
  change Projectivization.orthogonal
    (Projectivization.mk ℝ w hwNe)
    (Projectivization.mk ℝ ell hell) at hWcross
  have hraw : w ⬝ᵥ ell = 0 :=
    (Projectivization.orthogonal_mk hwNe hell).mp hWcross
  simpa [dotProduct_comm] using hraw

/-! ### Pulling a normalized third point back to an actual support -/

/-- A standard-grid third point which is collinear after the derived
relabelled chart belongs to the same actual determined line.  The proof uses
the exact covector uniqueness lemma above, rather than an unrecorded
projective-normalization assumption. -/
theorem twelveGridActualGridPoint_mem_line_of_normalized_collinear
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (hcard : Fintype.card Point = 12)
    (H : TwelveGridInvertedLineCensus cfg p)
    (L : DeterminedLine (pivotInversion cfg p))
    (i j k : Fin 3 × Fin 3) (hij : i ≠ j)
    (hi : twelveGridActualGridPoint hcard H i.1 i.2 ∈
      lineSupport (pivotInversion cfg p) L)
    (hj : twelveGridActualGridPoint hcard H j.1 j.2 ∈
      lineSupport (pivotInversion cfg p) L)
    (ra rb : ParameterizedThreeByThreeGridRelabelling)
    (ha : twelveGridActualColumnParameter hcard H = ra.parameter)
    (hb : twelveGridActualRowParameter hcard H = rb.parameter)
    (hdet : twelveGridHomogeneousDeterminant
      (homogeneousLift (twelveGridAffinePairPoint2
        (twelveGridPoint (parameterizedThreeByThreeNormalizedIndex ra rb i))))
      (homogeneousLift (twelveGridAffinePairPoint2
        (twelveGridPoint (parameterizedThreeByThreeNormalizedIndex ra rb j))))
      (homogeneousLift (twelveGridAffinePairPoint2
        (twelveGridPoint (parameterizedThreeByThreeNormalizedIndex ra rb k)))) = 0) :
    twelveGridActualGridPoint hcard H k.1 k.2 ∈
      lineSupport (pivotInversion cfg p) L := by
  have hdetNorm : twelveGridHomogeneousDeterminant
      (twelveGridParameterizedNormalizeHomogeneous ra rb
        (twelveGridActualAffinePoint hcard H
          (twelveGridActualGridPoint hcard H i.1 i.2)))
      (twelveGridParameterizedNormalizeHomogeneous ra rb
        (twelveGridActualAffinePoint hcard H
          (twelveGridActualGridPoint hcard H j.1 j.2)))
      (twelveGridParameterizedNormalizeHomogeneous ra rb
        (twelveGridActualAffinePoint hcard H
          (twelveGridActualGridPoint hcard H k.1 k.2))) = 0 := by
    rw [twelveGridActualNormalizedGridPoint hcard H ra rb ha hb i,
      twelveGridActualNormalizedGridPoint hcard H ra rb ha hb j,
      twelveGridActualNormalizedGridPoint hcard H ra rb ha hb k,
      twelveGridHomogeneousDeterminant_smul_left,
      twelveGridHomogeneousDeterminant_smul_middle,
      twelveGridHomogeneousDeterminant_smul_right, hdet]
    ring
  have hdetRaw : twelveGridHomogeneousDeterminant
      (twelveGridActualAffinePoint hcard H
        (twelveGridActualGridPoint hcard H i.1 i.2))
      (twelveGridActualAffinePoint hcard H
        (twelveGridActualGridPoint hcard H j.1 j.2))
      (twelveGridActualAffinePoint hcard H
        (twelveGridActualGridPoint hcard H k.1 k.2)) = 0 :=
    (twelveGridParameterizedNormalizeHomogeneous_determinant_eq_zero_iff
      ra rb _ _ _).mp hdetNorm
  have hcoordinate : twelveGridHomogeneousCoordinate
      (twelveGridActualAffinePoint hcard H
        (twelveGridActualGridPoint hcard H i.1 i.2)) ≠
      twelveGridHomogeneousCoordinate
        (twelveGridActualAffinePoint hcard H
          (twelveGridActualGridPoint hcard H j.1 j.2)) := by
    change twelveGridActualAffineGridCoordinate hcard H i.1 i.2 ≠
      twelveGridActualAffineGridCoordinate hcard H j.1 j.2
    rw [twelveGridActualAffineGridCoordinate_parameterized,
      twelveGridActualAffineGridCoordinate_parameterized]
    exact (threeByThreeParameterizedGridPoint_injective
      (twelveGridActualColumnParameter_ne_neg_one hcard H)
      (twelveGridActualColumnParameter_ne_zero hcard H)
      (twelveGridActualRowParameter_ne_neg_one hcard H)
      (twelveGridActualRowParameter_ne_zero hcard H)).ne hij
  have hiCov : twelveGridActualAffineLineCovector hcard H L ⬝ᵥ
      twelveGridActualAffinePoint hcard H
        (twelveGridActualGridPoint hcard H i.1 i.2) = 0 :=
    (twelveGridActualAffineLineCovector_incident_iff hcard H L
      (twelveGridActualGridPoint hcard H i.1 i.2)).2 hi
  have hjCov : twelveGridActualAffineLineCovector hcard H L ⬝ᵥ
      twelveGridActualAffinePoint hcard H
        (twelveGridActualGridPoint hcard H j.1 j.2) = 0 :=
    (twelveGridActualAffineLineCovector_incident_iff hcard H L
      (twelveGridActualGridPoint hcard H j.1 j.2)).2 hj
  have hkCov := twelveGridCovector_incident_of_homogeneous_determinant
    (twelveGridActualAffineLineCovector hcard H L)
    (twelveGridActualAffinePoint hcard H
      (twelveGridActualGridPoint hcard H i.1 i.2))
    (twelveGridActualAffinePoint hcard H
      (twelveGridActualGridPoint hcard H j.1 j.2))
    (twelveGridActualAffinePoint hcard H
      (twelveGridActualGridPoint hcard H k.1 k.2))
    (twelveGridActualAffineLineCovector_ne_zero hcard H L)
    hiCov hjCov
    (twelveGridActualAffineGridPoint_apply_two hcard H i.1 i.2)
    (twelveGridActualAffineGridPoint_apply_two hcard H j.1 j.2)
    hcoordinate
    (twelveGridActualAffinePoint_ne_zero hcard H
      (twelveGridActualGridPoint hcard H k.1 k.2)) hdetRaw
  exact (twelveGridActualAffineLineCovector_incident_iff hcard H L
    (twelveGridActualGridPoint hcard H k.1 k.2)).1 hkCov

/-! ### The finite ordinary-pair table of the standard grid -/

set_option maxHeartbeats 800000 in
/-- Every unordered pair of standard-grid points is either one of the twelve
ordinary secants in the explicit endpoint table, or has a third standard
grid point on its projective line.  This finite certificate is the precise
place where the cardinality-two support condition excludes the six
three-point rows, columns and diagonals. -/
theorem twelveGridStandardPair_secant_or_third
    (u v : Fin 3 × Fin 3) :
    (∃ s : RealThreeByThreeGridSecant,
      twelveGridSecantEndpoints s = (u, v) ∨
        twelveGridSecantEndpoints s = (v, u)) ∨
      ∃ w : Fin 3 × Fin 3, w ≠ u ∧ w ≠ v ∧
        twelveGridHomogeneousDeterminant
          (homogeneousLift (twelveGridAffinePairPoint2 (twelveGridPoint u)))
          (homogeneousLift (twelveGridAffinePairPoint2 (twelveGridPoint v)))
          (homogeneousLift (twelveGridAffinePairPoint2 (twelveGridPoint w))) = 0 := by
  rcases u with ⟨u0, u1⟩
  rcases v with ⟨v0, v1⟩
  fin_cases u0 <;> fin_cases u1 <;> fin_cases v0 <;> fin_cases v1
  · refine Or.inr ⟨(0, 1), by decide, by decide, ?_⟩
    norm_num [twelveGridHomogeneousDeterminant, twelveGridPoint,
      twelveGridCoordinate, homogeneousLift, twelveGridAffinePairPoint2,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two]
  · refine Or.inr ⟨(0, 2), by decide, by decide, ?_⟩
    norm_num [twelveGridHomogeneousDeterminant, twelveGridPoint,
      twelveGridCoordinate, homogeneousLift, twelveGridAffinePairPoint2,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two]
  · refine Or.inr ⟨(0, 1), by decide, by decide, ?_⟩
    norm_num [twelveGridHomogeneousDeterminant, twelveGridPoint,
      twelveGridCoordinate, homogeneousLift, twelveGridAffinePairPoint2,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two]
  · refine Or.inr ⟨(2, 0), by decide, by decide, ?_⟩
    norm_num [twelveGridHomogeneousDeterminant, twelveGridPoint,
      twelveGridCoordinate, homogeneousLift, twelveGridAffinePairPoint2,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two]
  · refine Or.inr ⟨(2, 2), by decide, by decide, ?_⟩
    norm_num [twelveGridHomogeneousDeterminant, twelveGridPoint,
      twelveGridCoordinate, homogeneousLift, twelveGridAffinePairPoint2,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two]
  · exact Or.inl ⟨(5, false), Or.inl rfl⟩
  · refine Or.inr ⟨(1, 0), by decide, by decide, ?_⟩
    norm_num [twelveGridHomogeneousDeterminant, twelveGridPoint,
      twelveGridCoordinate, homogeneousLift, twelveGridAffinePairPoint2,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two]
  · exact Or.inl ⟨(3, true), Or.inl rfl⟩
  · refine Or.inr ⟨(1, 1), by decide, by decide, ?_⟩
    norm_num [twelveGridHomogeneousDeterminant, twelveGridPoint,
      twelveGridCoordinate, homogeneousLift, twelveGridAffinePairPoint2,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two]
  · refine Or.inr ⟨(0, 2), by decide, by decide, ?_⟩
    norm_num [twelveGridHomogeneousDeterminant, twelveGridPoint,
      twelveGridCoordinate, homogeneousLift, twelveGridAffinePairPoint2,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two]
  · refine Or.inr ⟨(0, 0), by decide, by decide, ?_⟩
    norm_num [twelveGridHomogeneousDeterminant, twelveGridPoint,
      twelveGridCoordinate, homogeneousLift, twelveGridAffinePairPoint2,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two]
  · refine Or.inr ⟨(0, 0), by decide, by decide, ?_⟩
    norm_num [twelveGridHomogeneousDeterminant, twelveGridPoint,
      twelveGridCoordinate, homogeneousLift, twelveGridAffinePairPoint2,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two]
  · exact Or.inl ⟨(0, false), Or.inl rfl⟩
  · refine Or.inr ⟨(2, 1), by decide, by decide, ?_⟩
    norm_num [twelveGridHomogeneousDeterminant, twelveGridPoint,
      twelveGridCoordinate, homogeneousLift, twelveGridAffinePairPoint2,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two]
  · exact Or.inl ⟨(1, false), Or.inl rfl⟩
  · exact Or.inl ⟨(2, false), Or.inl rfl⟩
  · refine Or.inr ⟨(1, 1), by decide, by decide, ?_⟩
    norm_num [twelveGridHomogeneousDeterminant, twelveGridPoint,
      twelveGridCoordinate, homogeneousLift, twelveGridAffinePairPoint2,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two]
  · exact Or.inl ⟨(3, false), Or.inl rfl⟩
  · refine Or.inr ⟨(0, 1), by decide, by decide, ?_⟩
    norm_num [twelveGridHomogeneousDeterminant, twelveGridPoint,
      twelveGridCoordinate, homogeneousLift, twelveGridAffinePairPoint2,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two]
  · refine Or.inr ⟨(0, 0), by decide, by decide, ?_⟩
    norm_num [twelveGridHomogeneousDeterminant, twelveGridPoint,
      twelveGridCoordinate, homogeneousLift, twelveGridAffinePairPoint2,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two]
  · refine Or.inr ⟨(0, 0), by decide, by decide, ?_⟩
    norm_num [twelveGridHomogeneousDeterminant, twelveGridPoint,
      twelveGridCoordinate, homogeneousLift, twelveGridAffinePairPoint2,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two]
  · exact Or.inl ⟨(4, false), Or.inl rfl⟩
  · refine Or.inr ⟨(2, 0), by decide, by decide, ?_⟩
    norm_num [twelveGridHomogeneousDeterminant, twelveGridPoint,
      twelveGridCoordinate, homogeneousLift, twelveGridAffinePairPoint2,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two]
  · refine Or.inr ⟨(2, 2), by decide, by decide, ?_⟩
    norm_num [twelveGridHomogeneousDeterminant, twelveGridPoint,
      twelveGridCoordinate, homogeneousLift, twelveGridAffinePairPoint2,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two]
  · refine Or.inr ⟨(1, 1), by decide, by decide, ?_⟩
    norm_num [twelveGridHomogeneousDeterminant, twelveGridPoint,
      twelveGridCoordinate, homogeneousLift, twelveGridAffinePairPoint2,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two]
  · exact Or.inl ⟨(2, true), Or.inl rfl⟩
  · refine Or.inr ⟨(1, 2), by decide, by decide, ?_⟩
    norm_num [twelveGridHomogeneousDeterminant, twelveGridPoint,
      twelveGridCoordinate, homogeneousLift, twelveGridAffinePairPoint2,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two]
  · refine Or.inr ⟨(2, 0), by decide, by decide, ?_⟩
    norm_num [twelveGridHomogeneousDeterminant, twelveGridPoint,
      twelveGridCoordinate, homogeneousLift, twelveGridAffinePairPoint2,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two]
  · exact Or.inl ⟨(0, false), Or.inr rfl⟩
  · exact Or.inl ⟨(4, false), Or.inr rfl⟩
  · refine Or.inr ⟨(0, 0), by decide, by decide, ?_⟩
    norm_num [twelveGridHomogeneousDeterminant, twelveGridPoint,
      twelveGridCoordinate, homogeneousLift, twelveGridAffinePairPoint2,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two]
  · refine Or.inr ⟨(1, 2), by decide, by decide, ?_⟩
    norm_num [twelveGridHomogeneousDeterminant, twelveGridPoint,
      twelveGridCoordinate, homogeneousLift, twelveGridAffinePairPoint2,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two]
  · refine Or.inr ⟨(1, 1), by decide, by decide, ?_⟩
    norm_num [twelveGridHomogeneousDeterminant, twelveGridPoint,
      twelveGridCoordinate, homogeneousLift, twelveGridAffinePairPoint2,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two]
  · refine Or.inr ⟨(0, 0), by decide, by decide, ?_⟩
    norm_num [twelveGridHomogeneousDeterminant, twelveGridPoint,
      twelveGridCoordinate, homogeneousLift, twelveGridAffinePairPoint2,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two]
  · exact Or.inl ⟨(1, true), Or.inl rfl⟩
  · exact Or.inl ⟨(5, true), Or.inl rfl⟩
  · refine Or.inr ⟨(2, 2), by decide, by decide, ?_⟩
    norm_num [twelveGridHomogeneousDeterminant, twelveGridPoint,
      twelveGridCoordinate, homogeneousLift, twelveGridAffinePairPoint2,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two]
  · refine Or.inr ⟨(2, 1), by decide, by decide, ?_⟩
    norm_num [twelveGridHomogeneousDeterminant, twelveGridPoint,
      twelveGridCoordinate, homogeneousLift, twelveGridAffinePairPoint2,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two]
  · refine Or.inr ⟨(2, 0), by decide, by decide, ?_⟩
    norm_num [twelveGridHomogeneousDeterminant, twelveGridPoint,
      twelveGridCoordinate, homogeneousLift, twelveGridAffinePairPoint2,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two]
  · refine Or.inr ⟨(1, 2), by decide, by decide, ?_⟩
    norm_num [twelveGridHomogeneousDeterminant, twelveGridPoint,
      twelveGridCoordinate, homogeneousLift, twelveGridAffinePairPoint2,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two]
  · refine Or.inr ⟨(0, 0), by decide, by decide, ?_⟩
    norm_num [twelveGridHomogeneousDeterminant, twelveGridPoint,
      twelveGridCoordinate, homogeneousLift, twelveGridAffinePairPoint2,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two]
  · refine Or.inr ⟨(1, 0), by decide, by decide, ?_⟩
    norm_num [twelveGridHomogeneousDeterminant, twelveGridPoint,
      twelveGridCoordinate, homogeneousLift, twelveGridAffinePairPoint2,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two]
  · refine Or.inr ⟨(0, 2), by decide, by decide, ?_⟩
    norm_num [twelveGridHomogeneousDeterminant, twelveGridPoint,
      twelveGridCoordinate, homogeneousLift, twelveGridAffinePairPoint2,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two]
  · refine Or.inr ⟨(0, 1), by decide, by decide, ?_⟩
    norm_num [twelveGridHomogeneousDeterminant, twelveGridPoint,
      twelveGridCoordinate, homogeneousLift, twelveGridAffinePairPoint2,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two]
  · refine Or.inr ⟨(0, 0), by decide, by decide, ?_⟩
    norm_num [twelveGridHomogeneousDeterminant, twelveGridPoint,
      twelveGridCoordinate, homogeneousLift, twelveGridAffinePairPoint2,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two]
  · exact Or.inl ⟨(5, false), Or.inr rfl⟩
  · exact Or.inl ⟨(1, false), Or.inr rfl⟩
  · refine Or.inr ⟨(2, 2), by decide, by decide, ?_⟩
    norm_num [twelveGridHomogeneousDeterminant, twelveGridPoint,
      twelveGridCoordinate, homogeneousLift, twelveGridAffinePairPoint2,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two]
  · refine Or.inr ⟨(1, 1), by decide, by decide, ?_⟩
    norm_num [twelveGridHomogeneousDeterminant, twelveGridPoint,
      twelveGridCoordinate, homogeneousLift, twelveGridAffinePairPoint2,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two]
  · refine Or.inr ⟨(1, 0), by decide, by decide, ?_⟩
    norm_num [twelveGridHomogeneousDeterminant, twelveGridPoint,
      twelveGridCoordinate, homogeneousLift, twelveGridAffinePairPoint2,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two]
  · refine Or.inr ⟨(0, 0), by decide, by decide, ?_⟩
    norm_num [twelveGridHomogeneousDeterminant, twelveGridPoint,
      twelveGridCoordinate, homogeneousLift, twelveGridAffinePairPoint2,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two]
  · exact Or.inl ⟨(4, true), Or.inl rfl⟩
  · exact Or.inl ⟨(0, true), Or.inl rfl⟩
  · refine Or.inr ⟨(0, 2), by decide, by decide, ?_⟩
    norm_num [twelveGridHomogeneousDeterminant, twelveGridPoint,
      twelveGridCoordinate, homogeneousLift, twelveGridAffinePairPoint2,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two]
  · refine Or.inr ⟨(1, 0), by decide, by decide, ?_⟩
    norm_num [twelveGridHomogeneousDeterminant, twelveGridPoint,
      twelveGridCoordinate, homogeneousLift, twelveGridAffinePairPoint2,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two]
  · exact Or.inl ⟨(2, false), Or.inr rfl⟩
  · refine Or.inr ⟨(1, 1), by decide, by decide, ?_⟩
    norm_num [twelveGridHomogeneousDeterminant, twelveGridPoint,
      twelveGridCoordinate, homogeneousLift, twelveGridAffinePairPoint2,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two]
  · refine Or.inr ⟨(0, 0), by decide, by decide, ?_⟩
    norm_num [twelveGridHomogeneousDeterminant, twelveGridPoint,
      twelveGridCoordinate, homogeneousLift, twelveGridAffinePairPoint2,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two]
  · refine Or.inr ⟨(0, 2), by decide, by decide, ?_⟩
    norm_num [twelveGridHomogeneousDeterminant, twelveGridPoint,
      twelveGridCoordinate, homogeneousLift, twelveGridAffinePairPoint2,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two]
  · exact Or.inl ⟨(4, true), Or.inr rfl⟩
  · refine Or.inr ⟨(0, 0), by decide, by decide, ?_⟩
    norm_num [twelveGridHomogeneousDeterminant, twelveGridPoint,
      twelveGridCoordinate, homogeneousLift, twelveGridAffinePairPoint2,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two]
  · refine Or.inr ⟨(2, 2), by decide, by decide, ?_⟩
    norm_num [twelveGridHomogeneousDeterminant, twelveGridPoint,
      twelveGridCoordinate, homogeneousLift, twelveGridAffinePairPoint2,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two]
  · refine Or.inr ⟨(2, 1), by decide, by decide, ?_⟩
    norm_num [twelveGridHomogeneousDeterminant, twelveGridPoint,
      twelveGridCoordinate, homogeneousLift, twelveGridAffinePairPoint2,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two]
  · exact Or.inl ⟨(3, true), Or.inr rfl⟩
  · refine Or.inr ⟨(1, 1), by decide, by decide, ?_⟩
    norm_num [twelveGridHomogeneousDeterminant, twelveGridPoint,
      twelveGridCoordinate, homogeneousLift, twelveGridAffinePairPoint2,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two]
  · exact Or.inl ⟨(2, true), Or.inr rfl⟩
  · exact Or.inl ⟨(1, true), Or.inr rfl⟩
  · refine Or.inr ⟨(0, 1), by decide, by decide, ?_⟩
    norm_num [twelveGridHomogeneousDeterminant, twelveGridPoint,
      twelveGridCoordinate, homogeneousLift, twelveGridAffinePairPoint2,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two]
  · exact Or.inl ⟨(0, true), Or.inr rfl⟩
  · refine Or.inr ⟨(2, 2), by decide, by decide, ?_⟩
    norm_num [twelveGridHomogeneousDeterminant, twelveGridPoint,
      twelveGridCoordinate, homogeneousLift, twelveGridAffinePairPoint2,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two]
  · refine Or.inr ⟨(0, 0), by decide, by decide, ?_⟩
    norm_num [twelveGridHomogeneousDeterminant, twelveGridPoint,
      twelveGridCoordinate, homogeneousLift, twelveGridAffinePairPoint2,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two]
  · refine Or.inr ⟨(2, 0), by decide, by decide, ?_⟩
    norm_num [twelveGridHomogeneousDeterminant, twelveGridPoint,
      twelveGridCoordinate, homogeneousLift, twelveGridAffinePairPoint2,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two]
  · refine Or.inr ⟨(1, 1), by decide, by decide, ?_⟩
    norm_num [twelveGridHomogeneousDeterminant, twelveGridPoint,
      twelveGridCoordinate, homogeneousLift, twelveGridAffinePairPoint2,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two]
  · exact Or.inl ⟨(3, false), Or.inr rfl⟩
  · refine Or.inr ⟨(1, 2), by decide, by decide, ?_⟩
    norm_num [twelveGridHomogeneousDeterminant, twelveGridPoint,
      twelveGridCoordinate, homogeneousLift, twelveGridAffinePairPoint2,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two]
  · exact Or.inl ⟨(5, true), Or.inr rfl⟩
  · refine Or.inr ⟨(0, 0), by decide, by decide, ?_⟩
    norm_num [twelveGridHomogeneousDeterminant, twelveGridPoint,
      twelveGridCoordinate, homogeneousLift, twelveGridAffinePairPoint2,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two]
  · refine Or.inr ⟨(0, 2), by decide, by decide, ?_⟩
    norm_num [twelveGridHomogeneousDeterminant, twelveGridPoint,
      twelveGridCoordinate, homogeneousLift, twelveGridAffinePairPoint2,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two]
  · refine Or.inr ⟨(2, 1), by decide, by decide, ?_⟩
    norm_num [twelveGridHomogeneousDeterminant, twelveGridPoint,
      twelveGridCoordinate, homogeneousLift, twelveGridAffinePairPoint2,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two]
  · refine Or.inr ⟨(2, 0), by decide, by decide, ?_⟩
    norm_num [twelveGridHomogeneousDeterminant, twelveGridPoint,
      twelveGridCoordinate, homogeneousLift, twelveGridAffinePairPoint2,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two]
  · refine Or.inr ⟨(0, 0), by decide, by decide, ?_⟩
    norm_num [twelveGridHomogeneousDeterminant, twelveGridPoint,
      twelveGridCoordinate, homogeneousLift, twelveGridAffinePairPoint2,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two]

/-! ### From actual ordinary supports to normalized ordinary secants -/

/-- An actual ordinary line through the original pivot whose two support
labels are grid labels becomes one of the twelve standard ordinary secants
after the relabelling forced by the two actual transversals.  The endpoint
labels are retained, so distinct disjoint actual supports give distinct
standard secant codes below. -/
theorem twelveGridActualGridSecant_exists_normalized
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (hcard : Fintype.card Point = 12)
    (H : TwelveGridInvertedLineCensus cfg p)
    (L : DeterminedLineOfSize (pivotInversion cfg p) 2)
    (hpivot : cfg p ∈ L.1.1)
    (hgrid : ∀ q, q ∈ lineSupport (pivotInversion cfg p) L.1 →
      ∃ r s : Fin 3, twelveGridActualGridPoint hcard H r s = q)
    (ra rb : ParameterizedThreeByThreeGridRelabelling)
    (ha : twelveGridActualColumnParameter hcard H = ra.parameter)
    (hb : twelveGridActualRowParameter hcard H = rb.parameter) :
    ∃ (s : RealThreeByThreeGridSecant) (i j : Fin 3 × Fin 3),
      i ≠ j ∧
        twelveGridSecantEndpoints s =
          (parameterizedThreeByThreeNormalizedIndex ra rb i,
            parameterizedThreeByThreeNormalizedIndex ra rb j) ∧
        twelveGridActualGridPoint hcard H i.1 i.2 ∈
          lineSupport (pivotInversion cfg p) L.1 ∧
        twelveGridActualGridPoint hcard H j.1 j.2 ∈
          lineSupport (pivotInversion cfg p) L.1 ∧
        twelveGridStandardSecantCovector s ⬝ᵥ
          twelveGridParameterizedNormalizeHomogeneous ra rb
            (twelveGridActualAffinePivot hcard H) = 0 := by
  classical
  obtain ⟨x, y, hxy, hsupport⟩ := Finset.card_eq_two.mp L.2
  have hx : x ∈ lineSupport (pivotInversion cfg p) L.1 := by
    rw [hsupport]
    simp
  have hy : y ∈ lineSupport (pivotInversion cfg p) L.1 := by
    rw [hsupport]
    simp
  obtain ⟨ri, si, hix⟩ := hgrid x hx
  obtain ⟨rj, sj, hjy⟩ := hgrid y hy
  let i : Fin 3 × Fin 3 := (ri, si)
  let j : Fin 3 × Fin 3 := (rj, sj)
  have hi : twelveGridActualGridPoint hcard H i.1 i.2 = x := by
    simpa [i] using hix
  have hj : twelveGridActualGridPoint hcard H j.1 j.2 = y := by
    simpa [j] using hjy
  have hij : i ≠ j := by
    intro heq
    apply hxy
    calc
      x = twelveGridActualGridPoint hcard H i.1 i.2 := hi.symm
      _ = twelveGridActualGridPoint hcard H j.1 j.2 := by rw [heq]
      _ = y := hj
  have hmemi : twelveGridActualGridPoint hcard H i.1 i.2 ∈
      lineSupport (pivotInversion cfg p) L.1 := by
    rw [hi]
    exact hx
  have hmemj : twelveGridActualGridPoint hcard H j.1 j.2 ∈
      lineSupport (pivotInversion cfg p) L.1 := by
    rw [hj]
    exact hy
  let A := twelveGridActualAffinePoint hcard H
    (twelveGridActualGridPoint hcard H i.1 i.2)
  let B := twelveGridActualAffinePoint hcard H
    (twelveGridActualGridPoint hcard H j.1 j.2)
  let P := twelveGridActualAffinePivot hcard H
  let E := twelveGridActualAffineLineCovector hcard H L.1
  have hEA : E ⬝ᵥ A = 0 := by
    exact (twelveGridActualAffineLineCovector_incident_iff hcard H L.1
      (twelveGridActualGridPoint hcard H i.1 i.2)).2 hmemi
  have hEB : E ⬝ᵥ B = 0 := by
    exact (twelveGridActualAffineLineCovector_incident_iff hcard H L.1
      (twelveGridActualGridPoint hcard H j.1 j.2)).2 hmemj
  have hEP : E ⬝ᵥ P = 0 := by
    exact twelveGridActualAffineLineCovector_incident_pivot hcard H L.1 hpivot
  have hdetRaw : twelveGridHomogeneousDeterminant A B P = 0 := by
    exact twelveGridHomogeneousDeterminant_eq_zero_of_common_covector E A B P
      (twelveGridActualAffineLineCovector_ne_zero hcard H L.1) hEA hEB hEP
  have hdetNorm : twelveGridHomogeneousDeterminant
      (twelveGridParameterizedNormalizeHomogeneous ra rb A)
      (twelveGridParameterizedNormalizeHomogeneous ra rb B)
      (twelveGridParameterizedNormalizeHomogeneous ra rb P) = 0 :=
    (twelveGridParameterizedNormalizeHomogeneous_determinant_eq_zero_iff
      ra rb A B P).2 hdetRaw
  have hdetIJ : twelveGridHomogeneousDeterminant
      (homogeneousLift (twelveGridAffinePairPoint2
        (twelveGridPoint (parameterizedThreeByThreeNormalizedIndex ra rb i))))
      (homogeneousLift (twelveGridAffinePairPoint2
        (twelveGridPoint (parameterizedThreeByThreeNormalizedIndex ra rb j))))
      (twelveGridParameterizedNormalizeHomogeneous ra rb P) = 0 := by
    rw [twelveGridActualNormalizedGridPoint hcard H ra rb ha hb i,
      twelveGridActualNormalizedGridPoint hcard H ra rb ha hb j,
      twelveGridHomogeneousDeterminant_smul_left,
      twelveGridHomogeneousDeterminant_smul_middle] at hdetNorm
    exact (mul_eq_zero.mp
      ((mul_eq_zero.mp hdetNorm).resolve_left
        (twelveGridActualAffineGridPoint_apply_two hcard H i.1 i.2))).resolve_left
      (twelveGridActualAffineGridPoint_apply_two hcard H j.1 j.2)
  rcases twelveGridStandardPair_secant_or_third
      (parameterizedThreeByThreeNormalizedIndex ra rb i)
      (parameterizedThreeByThreeNormalizedIndex ra rb j) with hsec | hthird
  · obtain ⟨s, hends | hends⟩ := hsec
    · refine ⟨s, i, j, hij, hends, hmemi, hmemj, ?_⟩
      apply twelveGridStandardSecantCovector_of_endpoint_determinant s
        (twelveGridParameterizedNormalizeHomogeneous ra rb P)
      rw [hends]
      exact hdetIJ
    · refine ⟨s, j, i, hij.symm, hends, hmemj, hmemi, ?_⟩
      apply twelveGridStandardSecantCovector_of_endpoint_determinant s
        (twelveGridParameterizedNormalizeHomogeneous ra rb P)
      rw [hends, twelveGridHomogeneousDeterminant_swap_first_two, hdetIJ]
      ring
  · obtain ⟨w, hwi, hwj, hdet⟩ := hthird
    obtain ⟨rk, hrk⟩ := parameterizedThreeByThreeGridRelabelling_index_surjective
      ra w.1
    obtain ⟨sk, hsk⟩ := parameterizedThreeByThreeGridRelabelling_index_surjective
      rb w.2
    let k : Fin 3 × Fin 3 := (rk, sk)
    have hnormk : parameterizedThreeByThreeNormalizedIndex ra rb k = w := by
      dsimp [k, parameterizedThreeByThreeNormalizedIndex]
      exact Prod.ext hrk hsk
    have hdetk : twelveGridHomogeneousDeterminant
        (homogeneousLift (twelveGridAffinePairPoint2
          (twelveGridPoint (parameterizedThreeByThreeNormalizedIndex ra rb i))))
        (homogeneousLift (twelveGridAffinePairPoint2
          (twelveGridPoint (parameterizedThreeByThreeNormalizedIndex ra rb j))))
        (homogeneousLift (twelveGridAffinePairPoint2
          (twelveGridPoint (parameterizedThreeByThreeNormalizedIndex ra rb k)))) = 0 := by
      rw [hnormk]
      exact hdet
    have hmemk : twelveGridActualGridPoint hcard H k.1 k.2 ∈
        lineSupport (pivotInversion cfg p) L.1 :=
      twelveGridActualGridPoint_mem_line_of_normalized_collinear hcard H L.1
        i j k hij hmemi hmemj ra rb ha hb hdetk
    rw [hsupport] at hmemk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmemk
    exfalso
    rcases hmemk with hkx | hky
    · apply hwi
      have hki : k = i := (twelveGridActualGridPoint_injective hcard H)
        (by
          calc
            twelveGridActualGridPoint hcard H k.1 k.2 = x := hkx
            _ = twelveGridActualGridPoint hcard H i.1 i.2 := hi.symm)
      simpa [hki] using hnormk.symm
    · apply hwj
      have hkj : k = j := (twelveGridActualGridPoint_injective hcard H)
        (by
          calc
            twelveGridActualGridPoint hcard H k.1 k.2 = y := hky
            _ = twelveGridActualGridPoint hcard H j.1 j.2 := hj.symm)
      simpa [hkj] using hnormk.symm

/-! ### Three concurrent actual grid secants -/

/-- Three pairwise support-disjoint actual ordinary lines through the original
pivot cannot all be grid secants once the two extracted transversals have
forced the derived parameter chart.  In the finite chart this is the
standard external-point obstruction; at infinity it is the two-secant-per-
direction obstruction. -/
theorem twelveGridActualThreeGridSecants_concurrent_false
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (hcard : Fintype.card Point = 12)
    (H : TwelveGridInvertedLineCensus cfg p)
    (ra rb : ParameterizedThreeByThreeGridRelabelling)
    (ha : twelveGridActualColumnParameter hcard H = ra.parameter)
    (hb : twelveGridActualRowParameter hcard H = rb.parameter)
    (L0 L1 L2 : DeterminedLineOfSize (pivotInversion cfg p) 2)
    (h0pivot : cfg p ∈ L0.1.1)
    (h1pivot : cfg p ∈ L1.1.1)
    (h2pivot : cfg p ∈ L2.1.1)
    (h0grid : ∀ q, q ∈ lineSupport (pivotInversion cfg p) L0.1 →
      ∃ r s : Fin 3, twelveGridActualGridPoint hcard H r s = q)
    (h1grid : ∀ q, q ∈ lineSupport (pivotInversion cfg p) L1.1 →
      ∃ r s : Fin 3, twelveGridActualGridPoint hcard H r s = q)
    (h2grid : ∀ q, q ∈ lineSupport (pivotInversion cfg p) L2.1 →
      ∃ r s : Fin 3, twelveGridActualGridPoint hcard H r s = q)
    (h01 : Disjoint (lineSupport (pivotInversion cfg p) L0.1)
      (lineSupport (pivotInversion cfg p) L1.1))
    (h02 : Disjoint (lineSupport (pivotInversion cfg p) L0.1)
      (lineSupport (pivotInversion cfg p) L2.1))
    (h12 : Disjoint (lineSupport (pivotInversion cfg p) L1.1)
      (lineSupport (pivotInversion cfg p) L2.1)) :
    False := by
  classical
  obtain ⟨s0, i0, j0, hi0j0, hends0, h0i, h0j, hinc0⟩ :=
    twelveGridActualGridSecant_exists_normalized hcard H L0 h0pivot h0grid
      ra rb ha hb
  obtain ⟨s1, i1, j1, hi1j1, hends1, h1i, h1j, hinc1⟩ :=
    twelveGridActualGridSecant_exists_normalized hcard H L1 h1pivot h1grid
      ra rb ha hb
  obtain ⟨s2, i2, j2, hi2j2, hends2, h2i, h2j, hinc2⟩ :=
    twelveGridActualGridSecant_exists_normalized hcard H L2 h2pivot h2grid
      ra rb ha hb
  have hs01 : s0 ≠ s1 := by
    intro hs
    have hnorm : parameterizedThreeByThreeNormalizedIndex ra rb i0 =
        parameterizedThreeByThreeNormalizedIndex ra rb i1 := by
      calc
        parameterizedThreeByThreeNormalizedIndex ra rb i0 =
            (twelveGridSecantEndpoints s0).1 :=
          (congrArg Prod.fst hends0).symm
        _ = (twelveGridSecantEndpoints s1).1 := by rw [hs]
        _ = parameterizedThreeByThreeNormalizedIndex ra rb i1 :=
          congrArg Prod.fst hends1
    have hi : i0 = i1 :=
      parameterizedThreeByThreeNormalizedIndex_injective ra rb hnorm
    exact (Finset.disjoint_left.mp h01) h0i (by simpa [hi] using h1i)
  have hs02 : s0 ≠ s2 := by
    intro hs
    have hnorm : parameterizedThreeByThreeNormalizedIndex ra rb i0 =
        parameterizedThreeByThreeNormalizedIndex ra rb i2 := by
      calc
        parameterizedThreeByThreeNormalizedIndex ra rb i0 =
            (twelveGridSecantEndpoints s0).1 :=
          (congrArg Prod.fst hends0).symm
        _ = (twelveGridSecantEndpoints s2).1 := by rw [hs]
        _ = parameterizedThreeByThreeNormalizedIndex ra rb i2 :=
          congrArg Prod.fst hends2
    have hi : i0 = i2 :=
      parameterizedThreeByThreeNormalizedIndex_injective ra rb hnorm
    exact (Finset.disjoint_left.mp h02) h0i (by simpa [hi] using h2i)
  have hs12 : s1 ≠ s2 := by
    intro hs
    have hnorm : parameterizedThreeByThreeNormalizedIndex ra rb i1 =
        parameterizedThreeByThreeNormalizedIndex ra rb i2 := by
      calc
        parameterizedThreeByThreeNormalizedIndex ra rb i1 =
            (twelveGridSecantEndpoints s1).1 :=
          (congrArg Prod.fst hends1).symm
        _ = (twelveGridSecantEndpoints s2).1 := by rw [hs]
        _ = parameterizedThreeByThreeNormalizedIndex ra rb i2 :=
          congrArg Prod.fst hends2
    have hi : i1 = i2 :=
      parameterizedThreeByThreeNormalizedIndex_injective ra rb hnorm
    exact (Finset.disjoint_left.mp h12) h1i (by simpa [hi] using h2i)
  let Z := twelveGridParameterizedNormalizeHomogeneous ra rb
    (twelveGridActualAffinePivot hcard H)
  have hZne : Z ≠ 0 := by
    dsimp [Z]
    exact twelveGridParameterizedNormalizeHomogeneous_ne_zero ra rb
      (twelveGridActualAffinePivot hcard H)
      (twelveGridActualAffinePivot_ne_zero hcard H)
  by_cases hZfinite : Z 2 ≠ 0
  · have hpivot : twelveGridActualAffinePivot hcard H 2 ≠ 0 := by
      simpa only [Z, twelveGridParameterizedNormalizeHomogeneous,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two] using
        hZfinite
    have hExternal : RealThreeByThreeGridExternal
        (twelveGridHomogeneousCoordinate Z).1
        (twelveGridHomogeneousCoordinate Z).2 := by
      simpa only [Z] using
        (twelveGridActualNormalizedPivot_external hcard H ra rb ha hb hpivot)
    exact (RealThreeByThreeGridSecant.external_not_three_distinct
      s0 s1 s2
      (twelveGridHomogeneousCoordinate Z).1
      (twelveGridHomogeneousCoordinate Z).2
      hs01 hs02 hs12
      (twelveGridStandardSecant_incident_of_finite_homogeneous
        s0 Z hZfinite hinc0)
      (twelveGridStandardSecant_incident_of_finite_homogeneous
        s1 Z hZfinite hinc1)
      (twelveGridStandardSecant_incident_of_finite_homogeneous
        s2 Z hZfinite hinc2)) hExternal
  · have hZideal : Z 2 = 0 := not_ne_iff.mp hZfinite
    have hd01 : s0.direction = s1.direction :=
      twelveGridStandardSecant_same_direction_of_ideal
        s0 s1 Z hZideal hZne hinc0 hinc1
    have hd02 : s0.direction = s2.direction :=
      twelveGridStandardSecant_same_direction_of_ideal
        s0 s2 Z hZideal hZne hinc0 hinc2
    rcases RealThreeByThreeGridSecant.no_three_distinct_same_direction
        s0 s1 s2 hd01 hd02 with h | h | h
    · exact hs01 h
    · exact hs02 h
    · exact hs12 h

/-! ### The two forbidden local rows -/

/-- The type-zero local row is impossible from the actual line census alone.
The admissibility and five-line-count inputs are retained to give this
theorem exactly the former public grid-principle interface; the derived
projective argument itself needs no extra normalization assumption. -/
theorem twelveGrid_forbiddenGridTypeZero_unconditional
    {alpha : Type u} [Fintype alpha] [DecidableEq alpha]
    (cfg : Configuration alpha)
    (_hadm : Admissible cfg) (hcard : Fintype.card alpha = 12)
    (hcap : BlockSizeCap (blockSystem cfg) 5)
    (_hlineFive : (blockSystem cfg).lineCount 5 = 0) :
    Not (∃ p : alpha,
      (blockSystem cfg).blockDegree 3 p = 13 ∧
      (blockSystem cfg).blockDegree 5 p = 6 ∧
      (blockSystem cfg).lineDegree 3 p = 5 ∧
      (blockSystem cfg).lineDegree 4 p = 0) := by
  rintro ⟨p, hthree, hfive, hlineThree, hlineFour⟩
  let H := twelveGridInvertedLineCensus_of_typeZero_row cfg p hcard hcap
    hthree hfive hlineThree hlineFour
  obtain ⟨t0, t1, ht01, ht0, ht1⟩ :=
    twelveGridActualTwoTransversals_parameterized hcard H
  obtain ⟨ra, rb, ha, hb⟩ :=
    parameterizedThreeByThreeParameterCases_exists_relabelling
      (parameterizedThreeByThreeGrid_two_transversals_parameter_cases
        (twelveGridActualColumnParameter_ne_neg_one hcard H)
        (twelveGridActualColumnParameter_ne_zero hcard H)
        (twelveGridActualRowParameter_ne_neg_one hcard H)
        (twelveGridActualRowParameter_ne_zero hcard H)
        ht01 ht0 ht1)
  let S : Finset (Fin 5) :=
    twelveGridOriginalThreeLineGridSecantIndices hcard H 5 hlineThree
  have hSfour : 4 ≤ S.card := by
    simpa only [S] using
      (twelveGridTypeZero_gridSecantIndices_card_ge_four hcard H hlineThree)
  have hSthree : 2 < S.card := by omega
  obtain ⟨i, hi, j, hj, k, hk, hij, hik, hjk⟩ :=
    Finset.two_lt_card.mp hSthree
  exact twelveGridActualThreeGridSecants_concurrent_false hcard H ra rb ha hb
    (twelveGridOriginalThreeLineInvertedOrdinary
      (cfg := cfg) (p := p) 5 hlineThree i)
    (twelveGridOriginalThreeLineInvertedOrdinary
      (cfg := cfg) (p := p) 5 hlineThree j)
    (twelveGridOriginalThreeLineInvertedOrdinary
      (cfg := cfg) (p := p) 5 hlineThree k)
    (twelveGridOriginalThreeLineInvertedOrdinary_contains_pivot
      (cfg := cfg) (p := p) 5 hlineThree i)
    (twelveGridOriginalThreeLineInvertedOrdinary_contains_pivot
      (cfg := cfg) (p := p) 5 hlineThree j)
    (twelveGridOriginalThreeLineInvertedOrdinary_contains_pivot
      (cfg := cfg) (p := p) 5 hlineThree k)
    (twelveGridOriginalThreeLine_mem_gridSecantIndices
      hcard H 5 hlineThree hi)
    (twelveGridOriginalThreeLine_mem_gridSecantIndices
      hcard H 5 hlineThree hj)
    (twelveGridOriginalThreeLine_mem_gridSecantIndices
      hcard H 5 hlineThree hk)
    (twelveGridOriginalThreeLineInvertedOrdinary_disjoint
      (cfg := cfg) (p := p) 5 hlineThree hij)
    (twelveGridOriginalThreeLineInvertedOrdinary_disjoint
      (cfg := cfg) (p := p) 5 hlineThree hik)
    (twelveGridOriginalThreeLineInvertedOrdinary_disjoint
      (cfg := cfg) (p := p) 5 hlineThree hjk)

/-- The type-one local row is likewise impossible.  Its only numerical
difference is that four source three-lines still leave three pairwise
disjoint ordinary grid secants through the actual inversion pivot. -/
theorem twelveGrid_forbiddenGridTypeOne_unconditional
    {alpha : Type u} [Fintype alpha] [DecidableEq alpha]
    (cfg : Configuration alpha)
    (_hadm : Admissible cfg) (hcard : Fintype.card alpha = 12)
    (hcap : BlockSizeCap (blockSystem cfg) 5)
    (_hlineFive : (blockSystem cfg).lineCount 5 = 0) :
    Not (∃ p : alpha,
      (blockSystem cfg).blockDegree 3 p = 13 ∧
      (blockSystem cfg).blockDegree 5 p = 6 ∧
      (blockSystem cfg).lineDegree 3 p = 4 ∧
      (blockSystem cfg).lineDegree 4 p = 0) := by
  rintro ⟨p, hthree, hfive, hlineThree, hlineFour⟩
  let H := twelveGridInvertedLineCensus_of_typeOne_row cfg p hcard hcap
    hthree hfive hlineThree hlineFour
  obtain ⟨t0, t1, ht01, ht0, ht1⟩ :=
    twelveGridActualTwoTransversals_parameterized hcard H
  obtain ⟨ra, rb, ha, hb⟩ :=
    parameterizedThreeByThreeParameterCases_exists_relabelling
      (parameterizedThreeByThreeGrid_two_transversals_parameter_cases
        (twelveGridActualColumnParameter_ne_neg_one hcard H)
        (twelveGridActualColumnParameter_ne_zero hcard H)
        (twelveGridActualRowParameter_ne_neg_one hcard H)
        (twelveGridActualRowParameter_ne_zero hcard H)
        ht01 ht0 ht1)
  let S : Finset (Fin 4) :=
    twelveGridOriginalThreeLineGridSecantIndices hcard H 4 hlineThree
  have hSthree : 3 ≤ S.card := by
    simpa only [S] using
      (twelveGridTypeOne_gridSecantIndices_card_ge_three hcard H hlineThree)
  have hSthree' : 2 < S.card := by omega
  obtain ⟨i, hi, j, hj, k, hk, hij, hik, hjk⟩ :=
    Finset.two_lt_card.mp hSthree'
  exact twelveGridActualThreeGridSecants_concurrent_false hcard H ra rb ha hb
    (twelveGridOriginalThreeLineInvertedOrdinary
      (cfg := cfg) (p := p) 4 hlineThree i)
    (twelveGridOriginalThreeLineInvertedOrdinary
      (cfg := cfg) (p := p) 4 hlineThree j)
    (twelveGridOriginalThreeLineInvertedOrdinary
      (cfg := cfg) (p := p) 4 hlineThree k)
    (twelveGridOriginalThreeLineInvertedOrdinary_contains_pivot
      (cfg := cfg) (p := p) 4 hlineThree i)
    (twelveGridOriginalThreeLineInvertedOrdinary_contains_pivot
      (cfg := cfg) (p := p) 4 hlineThree j)
    (twelveGridOriginalThreeLineInvertedOrdinary_contains_pivot
      (cfg := cfg) (p := p) 4 hlineThree k)
    (twelveGridOriginalThreeLine_mem_gridSecantIndices
      hcard H 4 hlineThree hi)
    (twelveGridOriginalThreeLine_mem_gridSecantIndices
      hcard H 4 hlineThree hj)
    (twelveGridOriginalThreeLine_mem_gridSecantIndices
      hcard H 4 hlineThree hk)
    (twelveGridOriginalThreeLineInvertedOrdinary_disjoint
      (cfg := cfg) (p := p) 4 hlineThree hij)
    (twelveGridOriginalThreeLineInvertedOrdinary_disjoint
      (cfg := cfg) (p := p) 4 hlineThree hik)
    (twelveGridOriginalThreeLineInvertedOrdinary_disjoint
      (cfg := cfg) (p := p) 4 hlineThree hjk)

end Erdos506.V1
