import Erdos506.V1.TwelveDirectionOffStarGeometry
import Erdos506.Incidence.UngarSixGeneral

/-!
# The twelve-direction equality endpoint

This file isolates the last geometric input in the selected-six direction
argument.  Everything before the choice of an affine chart is proved for the
actual labelled dual arrangement:

* the no-six-line hypothesis needed by the local census is weakened from the
  global equation `lineCount 6 = 0` to `lineDegree 6 p = 0`;
* equality in the off-star estimate forces the extra vertices of the pivot
  line to be all the off-star vertices, each of multiplicity two;
* consequently every intersection of two of the six residual dual lines lies
  on one of the five lines of the concrete pencil.

The sole remaining parameter is named
`projectiveChartBridge_of_six_dual_lines_covered_by_five_pencil_lines`.  Its
conclusion is exactly the affine six-point witness consumed by the already
proved theorem `six_le_card_determinedDirections_of_noncollinear_finSix`.
No finite catalogue or decision-procedure certificate is used here.
-/

namespace Erdos506.V1

open Erdos506.Block
open Erdos506.Block.BlockSystem
open Erdos506.Finite
open Erdos506.Incidence
open Erdos506.V3
open Erdos506.V4

universe u

/-! ## The six residual dual lines -/

/-- The six labels which are neither the restored pivot nor one of the five
labels on the selected restored line. -/
noncomputable def twelveDirectionResidualLabels
    {alpha : Type u} [Fintype alpha] [DecidableEq alpha]
    (cfg : Configuration alpha) (p : alpha) (c : DeterminedCircle cfg)
    (hp : p ∈ circleTrace cfg c.1) : Finset (Option (AwayFrom p)) := by
  classical
  exact Finset.univ \ insert none (twelveDirectionStarLabels cfg p c hp)

theorem mem_twelveDirectionResidualLabels_iff
    {alpha : Type u} [Fintype alpha] [DecidableEq alpha]
    (cfg : Configuration alpha) (p : alpha) (c : DeterminedCircle cfg)
    (hp : p ∈ circleTrace cfg c.1) (a : Option (AwayFrom p)) :
    a ∈ twelveDirectionResidualLabels cfg p c hp ↔
      a ≠ none ∧ a ∉ twelveDirectionStarLabels cfg p c hp := by
  classical
  simp [twelveDirectionResidualLabels]

/-- Twelve labels split as the pivot, the five labels of the off-star, and
six residual labels. -/
theorem card_twelveDirectionResidualLabels
    {alpha : Type u} [Fintype alpha] [DecidableEq alpha]
    (cfg : Configuration alpha) (p : alpha) (c : DeterminedCircle cfg)
    (hp : p ∈ circleTrace cfg c.1)
    (hpoints : Fintype.card alpha = 12)
    (hcircle : (circleTrace cfg c.1).card = 6) :
    (twelveDirectionResidualLabels cfg p c hp).card = 6 := by
  classical
  have hnone : (none : Option (AwayFrom p)) ∉
      twelveDirectionStarLabels cfg p c hp := by
    intro h
    exact (twelveDirectionStarLabel_ne_none cfg p c hp h) rfl
  have hstar : (twelveDirectionStarLabels cfg p c hp).card = 5 :=
    card_twelveDirectionStarLabels cfg p c hp hcircle
  have htotal : Fintype.card (Option (AwayFrom p)) = 12 := by
    rw [Fintype.card_option, card_awayFrom, hpoints]
  unfold twelveDirectionResidualLabels
  rw [Finset.card_sdiff_of_subset (Finset.subset_univ _),
    Finset.card_univ]
  simp [hnone, hstar, htotal]

/-! ## Equality in the elementary off-star estimate -/

/-- The five forced intersections account exactly for the part removed from
the distinguished line. -/
theorem card_twelveDirectionExtraPivotVertices
    {alpha : Type u} [Fintype alpha] [DecidableEq alpha]
    (cfg : Configuration alpha) (p : alpha) (c : DeterminedCircle cfg)
    (hp : p ∈ circleTrace cfg c.1)
    (hcircle : (circleTrace cfg c.1).card = 6) :
    (twelveDirectionExtraPivotVertices cfg p c hp).card =
      (twelveDirectionPivotLineVertices cfg p).card - 5 := by
  classical
  unfold twelveDirectionExtraPivotVertices
  rw [Finset.card_sdiff_of_subset
      (twelveDirectionStarPivotIntersections_subset_pivotLineVertices
        cfg p c hp),
    card_twelveDirectionStarPivotIntersections cfg p c hp hcircle]

/-- If the actual gap vanishes, its defect is exactly the cardinality of the
extra part of the pivot line. -/
theorem twelveDirectionActualOffStarDefect_eq_card_extra_of_gap_eq_zero
    {alpha : Type u} [Fintype alpha] [DecidableEq alpha]
    (cfg : Configuration alpha) (p : alpha) (c : DeterminedCircle cfg)
    (hp : p ∈ circleTrace cfg c.1)
    (hcircle : (circleTrace cfg c.1).card = 6)
    (hgap : twelveDirectionActualEqualityGap cfg p c hp = 0) :
    twelveDirectionActualOffStarDefect cfg p c hp =
      (twelveDirectionExtraPivotVertices cfg p c hp).card := by
  have hpivot := five_le_card_twelveDirectionPivotLineVertices
    cfg p c hp hcircle
  have hextra := card_twelveDirectionExtraPivotVertices
    cfg p c hp hcircle
  simp only [twelveDirectionActualEqualityGap] at hgap
  omega

/-- Equality saturates the inclusion of the extra pivot vertices into the
off-star carrier. -/
theorem twelveDirectionExtraPivotVertices_eq_offStarVertices_of_gap_eq_zero
    {alpha : Type u} [Fintype alpha] [DecidableEq alpha]
    (cfg : Configuration alpha) (p : alpha) (c : DeterminedCircle cfg)
    (hp : p ∈ circleTrace cfg c.1)
    (hcircle : (circleTrace cfg c.1).card = 6)
    (hgap : twelveDirectionActualEqualityGap cfg p c hp = 0) :
    twelveDirectionExtraPivotVertices cfg p c hp =
      twelveDirectionOffStarVertices cfg p c hp := by
  apply Finset.eq_of_subset_of_card_le
    (twelveDirectionExtraPivotVertices_subset_offStarVertices cfg p c hp)
  have hdef :=
    twelveDirectionActualOffStarDefect_eq_card_extra_of_gap_eq_zero
      cfg p c hp hcircle hgap
  have hoff := card_twelveDirectionOffStarVertices_le_actualDefect
    cfg p c hp
  omega

/-- Equality also saturates every pointwise lower bound
`1 ≤ multiplicity - 1`: every off-star vertex is ordinary. -/
theorem labelDualMultiplicity_sub_one_eq_one_of_mem_offStar_of_gap_eq_zero
    {alpha : Type u} [Fintype alpha] [DecidableEq alpha]
    (cfg : Configuration alpha) (p : alpha) (c : DeterminedCircle cfg)
    (hp : p ∈ circleTrace cfg c.1)
    (hcircle : (circleTrace cfg c.1).card = 6)
    (hgap : twelveDirectionActualEqualityGap cfg p c hp = 0)
    {q : RealProjectivePoint}
    (hq : q ∈ twelveDirectionOffStarVertices cfg p c hp) :
    (labelDualArrangement (restoredPivotConfiguration cfg p)).multiplicity q - 1 = 1 := by
  classical
  let O := twelveDirectionOffStarVertices cfg p c hp
  let A := labelDualArrangement (restoredPivotConfiguration cfg p)
  let d : RealProjectivePoint → Nat := fun x => A.multiplicity x - 1
  change d q = 1
  have hEO :=
    twelveDirectionExtraPivotVertices_eq_offStarVertices_of_gap_eq_zero
      cfg p c hp hcircle hgap
  have hdef :=
    twelveDirectionActualOffStarDefect_eq_card_extra_of_gap_eq_zero
      cfg p c hp hcircle hgap
  have htotal : (∑ x ∈ O, d x) = O.card := by
    change twelveDirectionActualOffStarDefect cfg p c hp = O.card
    rw [hdef, hEO]
  have hqO : q ∈ O := by simpa only [O] using hq
  have hlow : 1 ≤ d q := by
    apply one_le_labelDualMultiplicity_sub_one_of_mem_vertexSet
      (restoredPivotConfiguration cfg p)
    exact ((mem_twelveDirectionOffStarVertices_iff cfg p c hp q).mp hq).1
  by_contra hne
  have htwo : 2 ≤ d q := by omega
  have hrest : (O.erase q).card ≤ ∑ x ∈ O.erase q, d x := by
    calc
      (O.erase q).card = ∑ x ∈ O.erase q, 1 := by
        rw [Finset.card_eq_sum_ones]
      _ ≤ ∑ x ∈ O.erase q, d x := by
        exact Finset.sum_le_sum (s := O.erase q) (fun x hx => by
          apply one_le_labelDualMultiplicity_sub_one_of_mem_vertexSet
            (restoredPivotConfiguration cfg p)
          have hxO : x ∈ O := (Finset.mem_erase.mp hx).2
          exact ((mem_twelveDirectionOffStarVertices_iff cfg p c hp x).mp
            (by simpa only [O] using hxO)).1)
  have hcontra : O.card < O.card := by
    calc
      O.card = (O.erase q).card + 1 :=
        (Finset.card_erase_add_one hqO).symm
      _ ≤ (∑ x ∈ O.erase q, d x) + 1 := Nat.add_le_add_right hrest 1
      _ < (∑ x ∈ O.erase q, d x) + d q :=
        Nat.add_lt_add_left (by omega) _
      _ = ∑ x ∈ O, d x := O.sum_erase_add d hqO
      _ = O.card := htotal
  exact (Nat.lt_irrefl _ hcontra)

/-- Three different incident indexed lines force multiplicity at least
three.  This tiny arrangement lemma is useful for reading the saturated
off-star count. -/
theorem three_le_multiplicity_of_three_incident
    {Line : Type*} [Fintype Line] [DecidableEq Line]
    (A : FiniteProjectiveLineArrangement Line)
    {q : RealProjectivePoint} {a b c : Line}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hqa : A.Incident q a) (hqb : A.Incident q b)
    (hqc : A.Incident q c) :
    3 ≤ A.multiplicity q := by
  classical
  unfold FiniteProjectiveLineArrangement.multiplicity
  have hsub : ({a, b, c} : Finset Line) ⊆
      Finset.univ.filter fun l => A.Incident q l := by
    intro l hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl | rfl | rfl
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hqa⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hqb⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hqc⟩
  have hcard := Finset.card_le_card hsub
  simpa [hab, hac, hbc, Ne.symm] using hcard

/-- The equality extractor in its final projective form.  Every join of two
residual labels is carried by one of the five pencil lines. -/
theorem residualIntersection_incident_star_of_gap_eq_zero
    {alpha : Type u} [Fintype alpha] [DecidableEq alpha]
    (cfg : Configuration alpha) (p : alpha) (c : DeterminedCircle cfg)
    (hp : p ∈ circleTrace cfg c.1)
    (hcircle : (circleTrace cfg c.1).card = 6)
    (hgap : twelveDirectionActualEqualityGap cfg p c hp = 0)
    {a b : Option (AwayFrom p)}
    (ha : a ∈ twelveDirectionResidualLabels cfg p c hp)
    (hb : b ∈ twelveDirectionResidualLabels cfg p c hp)
    (hab : a ≠ b) :
    ∃ s ∈ twelveDirectionStarLabels cfg p c hp,
      (labelDualArrangement (restoredPivotConfiguration cfg p)).Incident
        ((labelDualArrangement (restoredPivotConfiguration cfg p)).intersection a b) s := by
  classical
  let A := labelDualArrangement (restoredPivotConfiguration cfg p)
  let q := A.intersection a b
  by_contra hcovered
  have havoids : ∀ s ∈ twelveDirectionStarLabels cfg p c hp,
      ¬ A.Incident q s := by
    intro s hs hqs
    exact hcovered ⟨s, hs, hqs⟩
  have hqOff : q ∈ twelveDirectionOffStarVertices cfg p c hp := by
    apply (mem_twelveDirectionOffStarVertices_iff cfg p c hp q).mpr
    exact ⟨labelDualIntersection_mem_vertexSet
        (restoredPivotConfiguration cfg p) hab,
      havoids⟩
  have hordinary : A.multiplicity q - 1 = 1 := by
    simpa only [A, q] using
      labelDualMultiplicity_sub_one_eq_one_of_mem_offStar_of_gap_eq_zero
        cfg p c hp hcircle hgap hqOff
  have htwo : 2 ≤ A.multiplicity q := by
    exact two_le_labelDualMultiplicity_intersection
      (restoredPivotConfiguration cfg p) hab
  have hmult : A.multiplicity q = 2 := by omega
  have hEO :=
    twelveDirectionExtraPivotVertices_eq_offStarVertices_of_gap_eq_zero
      cfg p c hp hcircle hgap
  have hqExtra : q ∈ twelveDirectionExtraPivotVertices cfg p c hp := by
    rw [hEO]
    exact hqOff
  have hqPivot : q ∈ twelveDirectionPivotLineVertices cfg p :=
    (Finset.mem_sdiff.mp hqExtra).1
  have hqnone : A.Incident q none := by
    exact (mem_twelveDirectionPivotLineVertices_iff cfg p q).mp hqPivot |>.2
  have haNone : a ≠ none :=
    ((mem_twelveDirectionResidualLabels_iff cfg p c hp a).mp ha).1
  have hbNone : b ≠ none :=
    ((mem_twelveDirectionResidualLabels_iff cfg p c hp b).mp hb).1
  have hqa : A.Incident q a := by
    exact labelDualIntersection_incident_left
      (restoredPivotConfiguration cfg p) hab
  have hqb : A.Incident q b := by
    exact labelDualIntersection_incident_right
      (restoredPivotConfiguration cfg p) hab
  have hthree : 3 ≤ A.multiplicity q :=
    three_le_multiplicity_of_three_incident A
      haNone.symm hbNone.symm hab hqnone hqa hqb
  omega

/-! ## Localizing the no-six-line input at the chosen pivot -/

/-- A vanishing local six-line degree excludes a size-six line through the
chosen pivot; no global line census is needed. -/
theorem lineSupport_card_ne_six_of_lineDegree_six_eq_zero
    {alpha : Type u} [Fintype alpha] [DecidableEq alpha]
    (cfg : Configuration alpha) (p : alpha)
    (hline6 : (blockSystem cfg).lineDegree 6 p = 0)
    (L : DeterminedLine cfg) (hpL : cfg p ∈ L.1) :
    (lineSupport cfg L).card ≠ 6 := by
  classical
  intro hL
  have hblock : (Sum.inl L : GeometricBlock cfg) ∈
      (blockSystem cfg).lineBlocksOfSize 6 := by
    apply (blockSystem cfg).mem_blocksOfKindSize.mpr
    exact ⟨rfl, by simpa [geometricBlockSupport] using hL⟩
  have hpSupport : p ∈ (blockSystem cfg).support
      (Sum.inl L : GeometricBlock cfg) := by
    simpa [blockSystem, geometricBlockSystem, geometricBlockSupport] using
      (mem_lineSupport.mpr hpL)
  have hpos : 0 < (blockSystem cfg).lineDegree 6 p := by
    apply Finset.card_pos.mpr
    exact ⟨Sum.inl L, Finset.mem_filter.mpr ⟨hblock, hpSupport⟩⟩
  omega

/-- The support size classification for lines through the chosen pivot uses
only the local six-line degree. -/
theorem lineSupport_card_eq_two_or_three_or_four_or_five_of_local_twelveDirection
    {alpha : Type u} [Fintype alpha] [DecidableEq alpha]
    (cfg : Configuration alpha) (p : alpha)
    (hcap : BlockSizeCap (blockSystem cfg) 6)
    (hline6 : (blockSystem cfg).lineDegree 6 p = 0)
    (L : DeterminedLine cfg) (hpL : cfg p ∈ L.1) :
    (lineSupport cfg L).card = 2 ∨ (lineSupport cfg L).card = 3 ∨
      (lineSupport cfg L).card = 4 ∨ (lineSupport cfg L).card = 5 := by
  have hmin := two_le_lineSupport_card cfg L
  have hmax := lineSupport_card_le_six_of_blockSizeCap_six cfg hcap L
  have hne := lineSupport_card_ne_six_of_lineDegree_six_eq_zero
    cfg p hline6 L hpL
  omega

theorem twelveDirectionLineSizeSourceToLinesThroughPivot_surjective_of_lineDegree_six_eq_zero
    {alpha : Type u} [Fintype alpha] [DecidableEq alpha]
    (cfg : Configuration alpha) (p : alpha)
    (hcap : BlockSizeCap (blockSystem cfg) 6)
    (hline6 : (blockSystem cfg).lineDegree 6 p = 0) :
    Function.Surjective
      (twelveDirectionLineSizeSourceToLinesThroughPivot cfg p) := by
  intro L
  rcases lineSupport_card_eq_two_or_three_or_four_or_five_of_local_twelveDirection
    cfg p hcap hline6 L.1 L.2 with h2 | h3 | h4 | h5
  · let X : DeterminedLineOfSizeThrough cfg p 2 :=
      ⟨⟨L.1, h2⟩, mem_lineSupport.mpr L.2⟩
    exact ⟨.inl X, by rfl⟩
  · let X : DeterminedLineOfSizeThrough cfg p 3 :=
      ⟨⟨L.1, h3⟩, mem_lineSupport.mpr L.2⟩
    exact ⟨.inr (.inl X), by rfl⟩
  · let X : DeterminedLineOfSizeThrough cfg p 4 :=
      ⟨⟨L.1, h4⟩, mem_lineSupport.mpr L.2⟩
    exact ⟨.inr (.inr (.inl X)), by rfl⟩
  · let X : DeterminedLineOfSizeThrough cfg p 5 :=
      ⟨⟨L.1, h5⟩, mem_lineSupport.mpr L.2⟩
    exact ⟨.inr (.inr (.inr X)), by rfl⟩

noncomputable def twelveDirectionLineSizeSourceEquivLinesThroughPivot_of_lineDegree_six_eq_zero
    {alpha : Type u} [Fintype alpha] [DecidableEq alpha]
    (cfg : Configuration alpha) (p : alpha)
    (hcap : BlockSizeCap (blockSystem cfg) 6)
    (hline6 : (blockSystem cfg).lineDegree 6 p = 0) :
    TwelveDirectionLineSizeSource cfg p ≃
      TwelveDirectionLinesThroughPivot cfg p :=
  Equiv.ofBijective (twelveDirectionLineSizeSourceToLinesThroughPivot cfg p)
    ⟨twelveDirectionLineSizeSourceToLinesThroughPivot_injective cfg p,
      twelveDirectionLineSizeSourceToLinesThroughPivot_surjective_of_lineDegree_six_eq_zero
        cfg p hcap hline6⟩

/-- Local form of the exact distinguished-line census. -/
theorem card_twelveDirectionPivotLineVertices_eq_distinguishedLineVertices_of_lineDegree_six_eq_zero
    {alpha : Type u} [Fintype alpha] [DecidableEq alpha]
    (cfg : Configuration alpha) (p : alpha)
    (hcap : BlockSizeCap (blockSystem cfg) 6)
    (hline6 : (blockSystem cfg).lineDegree 6 p = 0) :
    (twelveDirectionPivotLineVertices cfg p).card =
      (blockSystem cfg).lineDegree 2 p + (blockSystem cfg).lineDegree 3 p +
        (blockSystem cfg).lineDegree 4 p + (blockSystem cfg).lineDegree 5 p := by
  rw [card_twelveDirectionPivotLineVertices_eq_card_linesThroughPivot]
  calc
    Nat.card (TwelveDirectionLinesThroughPivot cfg p) =
        Nat.card (TwelveDirectionLineSizeSource cfg p) :=
      Nat.card_congr
        (twelveDirectionLineSizeSourceEquivLinesThroughPivot_of_lineDegree_six_eq_zero
          cfg p hcap hline6).symm
    _ = Fintype.card (TwelveDirectionLineSizeSource cfg p) :=
      Nat.card_eq_fintype_card
    _ = Fintype.card (DeterminedLineOfSizeThrough cfg p 2) +
        Fintype.card (DeterminedLineOfSizeThrough cfg p 3) +
          Fintype.card (DeterminedLineOfSizeThrough cfg p 4) +
            Fintype.card (DeterminedLineOfSizeThrough cfg p 5) := by
      simp [TwelveDirectionLineSizeSource, Fintype.card_sum, Nat.add_assoc]
    _ = (blockSystem cfg).lineDegree 2 p +
        (blockSystem cfg).lineDegree 3 p +
          (blockSystem cfg).lineDegree 4 p +
            (blockSystem cfg).lineDegree 5 p := by
      rw [← lineDegree_eq_card_determinedLineOfSizeThrough,
        ← lineDegree_eq_card_determinedLineOfSizeThrough,
        ← lineDegree_eq_card_determinedLineOfSizeThrough,
        ← lineDegree_eq_card_determinedLineOfSizeThrough]

/-- The restored multiplicity bound likewise only needs to exclude a
size-six original line through `p`. -/
theorem labelDualMultiplicity_restored_le_five_of_blockSizeCap_of_lineDegree_six_eq_zero
    {alpha : Type u} [Fintype alpha] [DecidableEq alpha]
    (cfg : Configuration alpha) (p : alpha)
    (hcap : BlockSizeCap (blockSystem cfg) 6)
    (hline6 : (blockSystem cfg).lineDegree 6 p = 0)
    {q : RealProjectivePoint}
    (hq : q ∈ labelDualVertexSet (restoredPivotConfiguration cfg p)) :
    (labelDualArrangement (restoredPivotConfiguration cfg p)).multiplicity q ≤ 5 := by
  classical
  rw [labelDualVertexSet_eq_allDeterminedLineDualVertices] at hq
  unfold allDeterminedLineDualVertices at hq
  obtain ⟨L, _hL, hLq⟩ := Finset.mem_image.mp hq
  rw [← hLq, labelDual_multiplicity_determinedLine]
  obtain ⟨b, hb⟩ := (blockRestoredLineEquiv cfg p).surjective L
  rw [← hb]
  change (lineSupport (restoredPivotConfiguration cfg p)
    (blockToRestoredLine cfg p b)).card ≤ 5
  rcases b with ⟨b, hbp⟩
  cases b with
  | inl L =>
      have hcard := card_lineSupport_blockToRestoredLine cfg p
        (⟨.inl L, hbp⟩ : BlockThrough cfg p)
      change (lineSupport (restoredPivotConfiguration cfg p)
        (blockToRestoredLine cfg p ⟨.inl L, hbp⟩)).card =
          (lineSupport cfg L).card at hcard
      have hpL : cfg p ∈ L.1 := by
        apply mem_lineSupport.mp
        simpa [geometricBlockSupport] using hbp
      have hle := lineSupport_card_le_six_of_blockSizeCap_six cfg hcap L
      have hne := lineSupport_card_ne_six_of_lineDegree_six_eq_zero
        cfg p hline6 L hpL
      have hsmall : (lineSupport cfg L).card ≤ 5 := by omega
      exact hcard.trans_le hsmall
  | inr c =>
      have hcard := card_lineSupport_blockToRestoredLine cfg p
        (⟨.inr c, hbp⟩ : BlockThrough cfg p)
      have hmin := Erdos506.V3.circleSupport_card_ge_three cfg c
      have hle : (circleTrace cfg c.1).card ≤ 6 := by
        apply hcap (.inr c)
        simpa [geometricBlockSupport] using hmin
      change (lineSupport (restoredPivotConfiguration cfg p)
        (blockToRestoredLine cfg p ⟨.inr c, hbp⟩)).card =
          (circleTrace cfg c.1).card - 1 at hcard
      have hsmall : (circleTrace cfg c.1).card - 1 ≤ 5 := by omega
      exact hcard.trans_le hsmall

/-! ## The local actual/arithmetic dictionary -/

/-- The concrete defect dictionary with the global no-six-line hypothesis
replaced by its exact local use. -/
theorem twelveDirectionActualOffStarDefect_eq_twelveDirectionOffStarDefect_of_lineDegree_six_eq_zero
    {alpha : Type u} [Fintype alpha] [DecidableEq alpha]
    (cfg : Configuration alpha) (p : alpha) (c : DeterminedCircle cfg)
    (hp : p ∈ circleTrace cfg c.1)
    (hpoints : Fintype.card alpha = 12)
    (hcircle : (circleTrace cfg c.1).card = 6)
    (hcap : BlockSizeCap (blockSystem cfg) 6)
    (hline6 : (blockSystem cfg).lineDegree 6 p = 0) :
    (twelveDirectionActualOffStarDefect cfg p c hp : Int) =
      twelveDirectionOffStarDefect (blockSystem cfg) p := by
  classical
  have hmult : ∀ q ∈ labelDualVertexSet (restoredPivotConfiguration cfg p),
      (labelDualArrangement (restoredPivotConfiguration cfg p)).multiplicity q ≤ 5 := by
    intro q hq
    exact labelDualMultiplicity_restored_le_five_of_blockSizeCap_of_lineDegree_six_eq_zero
      cfg p hcap hline6 hq
  have htotal := twelveDirectionTotalDualDefect_eq_profile_sum cfg p hmult
  have hIcc : Finset.Icc 2 5 = {2, 3, 4, 5} := by
    ext s
    simp only [Finset.mem_Icc, Finset.mem_insert, Finset.mem_singleton]
    omega
  rw [hIcc] at htotal
  norm_num [Finset.sum_insert, Finset.sum_singleton] at htotal
  have htotalInt : (twelveDirectionTotalDualDefect cfg p : Int) =
      (twelveDirectionDualMultiplicityVertices
          (restoredPivotConfiguration cfg p) 2).card +
        (2 * (twelveDirectionDualMultiplicityVertices
          (restoredPivotConfiguration cfg p) 3).card +
        (3 * (twelveDirectionDualMultiplicityVertices
          (restoredPivotConfiguration cfg p) 4).card +
        4 * (twelveDirectionDualMultiplicityVertices
          (restoredPivotConfiguration cfg p) 5).card)) := by
    exact_mod_cast htotal
  rw [card_twelveDirectionDualMultiplicityVertices_restored_eq_twelveDirectionT2,
    card_twelveDirectionDualMultiplicityVertices_restored_eq_twelveDirectionT3,
    card_twelveDirectionDualMultiplicityVertices_restored_eq_twelveDirectionT4,
    card_twelveDirectionDualMultiplicityVertices_restored_eq_twelveDirectionT5
      cfg p hline6] at htotalInt
  have hpartition :=
    twelveDirectionTotalDualDefect_eq_actualOffStarDefect_add_starDefect cfg p c hp
  have hstar := twelveDirectionStarDefect_eq_thirty_nine
    cfg p c hp hpoints hcircle
  have hpartitionInt : (twelveDirectionTotalDualDefect cfg p : Int) =
      (twelveDirectionActualOffStarDefect cfg p c hp : Int) +
        (twelveDirectionStarDefect cfg p c hp : Int) := by
    exact_mod_cast hpartition
  rw [hstar] at hpartitionInt
  simp only [twelveDirectionOffStarDefect]
  omega

/-- Local equality of the genuine projective gap and the arithmetic gap. -/
theorem twelveDirectionActualEqualityGap_eq_twelveDirectionEqualityGap_of_lineDegree_six_eq_zero
    {alpha : Type u} [Fintype alpha] [DecidableEq alpha]
    (cfg : Configuration alpha) (p : alpha) (c : DeterminedCircle cfg)
    (hp : p ∈ circleTrace cfg c.1)
    (hpoints : Fintype.card alpha = 12)
    (hcircle : (circleTrace cfg c.1).card = 6)
    (hcap : BlockSizeCap (blockSystem cfg) 6)
    (hline6 : (blockSystem cfg).lineDegree 6 p = 0) :
    twelveDirectionActualEqualityGap cfg p c hp =
      twelveDirectionEqualityGap (blockSystem cfg) p := by
  simp only [twelveDirectionActualEqualityGap, twelveDirectionEqualityGap]
  rw [card_twelveDirectionPivotLineVertices_eq_distinguishedLineVertices_of_lineDegree_six_eq_zero
      cfg p hcap hline6,
    twelveDirectionActualOffStarDefect_eq_twelveDirectionOffStarDefect_of_lineDegree_six_eq_zero
      cfg p c hp hpoints hcircle hcap hline6]
  simp only [twelveDirectionDistinguishedLineVertices]
  omega

/-- A positive local six-block degree supplies a six-circle as soon as the
local six-line degree vanishes. -/
theorem exists_six_circle_through_of_blockDegree_six_pos_of_lineDegree_six_eq_zero
    {alpha : Type u} [Fintype alpha] [DecidableEq alpha]
    (cfg : Configuration alpha) (p : alpha)
    (hdegree : 0 < (blockSystem cfg).blockDegree 6 p)
    (hline6 : (blockSystem cfg).lineDegree 6 p = 0) :
    ∃ c : DeterminedCircle cfg,
      p ∈ circleTrace cfg c.1 ∧ (circleTrace cfg c.1).card = 6 := by
  classical
  let S := blockSystem cfg
  have hfilter : 0 <
      ((S.blocksOfSize 6).filter fun b => p ∈ S.support b).card := by
    simpa [S, BlockSystem.blockDegree, BlockSystem.degreeIn] using hdegree
  obtain ⟨b, hb⟩ := Finset.card_pos.mp hfilter
  have hb' := Finset.mem_filter.mp hb
  have hbsize : (S.support b).card = 6 := S.mem_blocksOfSize.mp hb'.1
  have hbp : p ∈ S.support b := hb'.2
  cases b with
  | inl L =>
      have hlineBlock : (Sum.inl L : GeometricBlock cfg) ∈
          S.lineBlocksOfSize 6 := by
        apply S.mem_blocksOfKindSize.mpr
        exact ⟨rfl, hbsize⟩
      have hpositive : 0 < S.lineDegree 6 p := by
        apply Finset.card_pos.mpr
        exact ⟨Sum.inl L, Finset.mem_filter.mpr ⟨hlineBlock, hbp⟩⟩
      change S.lineDegree 6 p = 0 at hline6
      omega
  | inr c =>
      refine ⟨c, ?_, ?_⟩
      · simpa [S, blockSystem, geometricBlockSystem,
          geometricBlockSupport] using hbp
      · simpa [S, blockSystem, geometricBlockSystem,
          geometricBlockSupport] using hbsize

/-! ## The single projective-chart parameter and the Ungar contradiction -/

/-- Strictness of the actual gap, assuming only the missing projective-chart
bridge.  The deliberately long parameter name states its exact job: turn the
six residual dual lines, whose pairwise intersections are covered by the five
lines of the pencil, into six noncollinear affine points with at most five
directions. -/
theorem twelveDirectionActualEqualityGap_pos_of_projectiveChartBridge
    {alpha : Type u} [Fintype alpha] [DecidableEq alpha]
    (cfg : Configuration alpha) (p : alpha) (c : DeterminedCircle cfg)
    (hp : p ∈ circleTrace cfg c.1)
    (hpoints : Fintype.card alpha = 12)
    (hcircle : (circleTrace cfg c.1).card = 6)
    (hcap : BlockSizeCap (blockSystem cfg) 6)
    (hline6 : (blockSystem cfg).lineDegree 6 p = 0)
    (projectiveChartBridge_of_six_dual_lines_covered_by_five_pencil_lines :
      (twelveDirectionResidualLabels cfg p c hp).card = 6 →
      (∀ q ∈ labelDualVertexSet (restoredPivotConfiguration cfg p),
        (labelDualArrangement (restoredPivotConfiguration cfg p)).multiplicity q ≤ 5) →
      (∀ {a b : Option (AwayFrom p)},
        a ∈ twelveDirectionResidualLabels cfg p c hp →
        b ∈ twelveDirectionResidualLabels cfg p c hp → a ≠ b →
        ∃ s ∈ twelveDirectionStarLabels cfg p c hp,
          (labelDualArrangement (restoredPivotConfiguration cfg p)).Incident
            ((labelDualArrangement (restoredPivotConfiguration cfg p)).intersection a b) s) →
      ∃ affineCfg : Configuration (Fin 6),
        Noncollinear affineCfg ∧ (determinedDirections affineCfg).card ≤ 5) :
    0 < twelveDirectionActualEqualityGap cfg p c hp := by
  have hnonneg := twelveDirectionActualEqualityGap_nonneg
    cfg p c hp hcircle
  by_contra hnotpos
  have hzero : twelveDirectionActualEqualityGap cfg p c hp = 0 := by omega
  have hresidual := card_twelveDirectionResidualLabels
    cfg p c hp hpoints hcircle
  have hmult : ∀ q ∈ labelDualVertexSet (restoredPivotConfiguration cfg p),
      (labelDualArrangement (restoredPivotConfiguration cfg p)).multiplicity q ≤ 5 := by
    intro q hq
    exact labelDualMultiplicity_restored_le_five_of_blockSizeCap_of_lineDegree_six_eq_zero
      cfg p hcap hline6 hq
  have hcovered : ∀ {a b : Option (AwayFrom p)},
      a ∈ twelveDirectionResidualLabels cfg p c hp →
      b ∈ twelveDirectionResidualLabels cfg p c hp → a ≠ b →
      ∃ s ∈ twelveDirectionStarLabels cfg p c hp,
        (labelDualArrangement (restoredPivotConfiguration cfg p)).Incident
          ((labelDualArrangement (restoredPivotConfiguration cfg p)).intersection a b) s := by
    intro a b ha hb hab
    exact residualIntersection_incident_star_of_gap_eq_zero
      cfg p c hp hcircle hzero ha hb hab
  obtain ⟨affineCfg, hnoncollinear, hfive⟩ :=
    projectiveChartBridge_of_six_dual_lines_covered_by_five_pencil_lines
      hresidual hmult hcovered
  have hungar :=
    six_le_card_determinedDirections_of_noncollinear_finSix
      affineCfg hnoncollinear
  omega

/-- Local strictness of the arithmetic gap. -/
theorem twelveDirectionEqualityGap_pos_of_projectiveChartBridge
    {alpha : Type u} [Fintype alpha] [DecidableEq alpha]
    (cfg : Configuration alpha) (p : alpha) (c : DeterminedCircle cfg)
    (hp : p ∈ circleTrace cfg c.1)
    (hpoints : Fintype.card alpha = 12)
    (hcircle : (circleTrace cfg c.1).card = 6)
    (hcap : BlockSizeCap (blockSystem cfg) 6)
    (hline6 : (blockSystem cfg).lineDegree 6 p = 0)
    (projectiveChartBridge_of_six_dual_lines_covered_by_five_pencil_lines :
      (twelveDirectionResidualLabels cfg p c hp).card = 6 →
      (∀ q ∈ labelDualVertexSet (restoredPivotConfiguration cfg p),
        (labelDualArrangement (restoredPivotConfiguration cfg p)).multiplicity q ≤ 5) →
      (∀ {a b : Option (AwayFrom p)},
        a ∈ twelveDirectionResidualLabels cfg p c hp →
        b ∈ twelveDirectionResidualLabels cfg p c hp → a ≠ b →
        ∃ s ∈ twelveDirectionStarLabels cfg p c hp,
          (labelDualArrangement (restoredPivotConfiguration cfg p)).Incident
            ((labelDualArrangement (restoredPivotConfiguration cfg p)).intersection a b) s) →
      ∃ affineCfg : Configuration (Fin 6),
        Noncollinear affineCfg ∧ (determinedDirections affineCfg).card ≤ 5) :
    0 < twelveDirectionEqualityGap (blockSystem cfg) p := by
  rw [← twelveDirectionActualEqualityGap_eq_twelveDirectionEqualityGap_of_lineDegree_six_eq_zero
    cfg p c hp hpoints hcircle hcap hline6]
  exact twelveDirectionActualEqualityGap_pos_of_projectiveChartBridge
    cfg p c hp hpoints hcircle hcap hline6
      projectiveChartBridge_of_six_dual_lines_covered_by_five_pencil_lines

/-- The public direction principle follows by the light arithmetic adapter
once the chart bridge is supplied uniformly. -/
noncomputable def realPlaneTwelveDirectionPrinciple_of_projectiveChartBridge
    (Mel : RealPlaneMelchiorPrinciple.{u})
    (EvenArr : RealPlaneEvenArrangementPrinciple.{u})
    (Kelly : RealPlaneKellyMoserPrinciple.{u})
    (Gram : RealPlaneTwelveGramPrinciple.{u})
    (projectiveChartBridge_of_six_dual_lines_covered_by_five_pencil_lines :
      ∀ {alpha : Type u} [Fintype alpha] [DecidableEq alpha]
        (cfg : Configuration alpha) (p : alpha) (c : DeterminedCircle cfg)
        (hp : p ∈ circleTrace cfg c.1),
        (twelveDirectionResidualLabels cfg p c hp).card = 6 →
        (∀ q ∈ labelDualVertexSet (restoredPivotConfiguration cfg p),
          (labelDualArrangement (restoredPivotConfiguration cfg p)).multiplicity q ≤ 5) →
        (∀ {a b : Option (AwayFrom p)},
          a ∈ twelveDirectionResidualLabels cfg p c hp →
          b ∈ twelveDirectionResidualLabels cfg p c hp → a ≠ b →
          ∃ s ∈ twelveDirectionStarLabels cfg p c hp,
            (labelDualArrangement (restoredPivotConfiguration cfg p)).Incident
              ((labelDualArrangement (restoredPivotConfiguration cfg p)).intersection a b) s) →
        ∃ affineCfg : Configuration (Fin 6),
          Noncollinear affineCfg ∧ (determinedDirections affineCfg).card ≤ 5) :
    RealPlaneTwelveDirectionPrinciple.{u} where
  directionBound := by
    intro alpha _ _ cfg hadm hpoints hcap gamma hkind hgamma hline p hdegree
    have hline6 : (blockSystem cfg).lineDegree 6 p = 0 :=
      twelveDirection_lineDegree_six_eq_zero_of_lineCount_six_eq_zero
        cfg p hline
    obtain ⟨c, hp, hcircle⟩ :=
      exists_six_circle_through_of_blockDegree_six_pos_of_lineDegree_six_eq_zero
        cfg p hdegree hline6
    have hgap : 0 < twelveDirectionEqualityGap (blockSystem cfg) p :=
      twelveDirectionEqualityGap_pos_of_projectiveChartBridge
        cfg p c hp hpoints hcircle hcap hline6
          (projectiveChartBridge_of_six_dual_lines_covered_by_five_pencil_lines
            cfg p c hp)
    have hrows : TwelveSixLocalRows (blockSystem cfg) p :=
      twelveSixLocalRows_of_configuration
        Mel EvenArr Kelly Gram cfg hadm hpoints hcap p
    have hsigma : 0 ≤ (blockSystem cfg).pivotSigma p := by
      exact sigma_nonneg_of_realPlaneMelchior Mel cfg hadm (by omega) p
    have hnum :=
      three_le_twelveDirectionDefectNumerator_of_gap_pos_of_sigma_nonneg
        (blockSystem cfg) p hrows hsigma hgap
    omega

end Erdos506.V1
