import Erdos506.V1.TwelveGridProjectiveNormalization
import Erdos506.V1.PivotThreeLines

/-!
# Actual transversals and pivot ordinary secants in the twelve-grid branch

The six actual four-lines reconstructed from the inverted census carry two
actual size-three lines.  This file proves that those lines are genuine
three-by-three-grid transversals, rather than merely abstract members of a
line-count census.  It also transports every original three-line through the
inversion pivot to an actual ordinary line, records its concurrence at the
inversion centre, and isolates the one possible exceptional ordinary line
joining the two pencil centres.

No projective normalization is chosen here.  The resulting endpoint is the
exact incidence input for the remaining projective grid lemma: two actual
transversals, and (in the two exceptional rows) at least four respectively
three actual grid secants concurrent at the original pivot.
-/

namespace Erdos506.V1

open Erdos506.Block
open Erdos506.Block.BlockSystem
open Erdos506.Finite
open Erdos506.Incidence
open Erdos506.V3
open Erdos506.V4

universe u

/-- The two reconstructed pencil centres are distinct actual inverted
labels. -/
theorem twelveGridActualExternalPoint_zero_ne_one
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (hcard : Fintype.card Point = 12)
    (H : TwelveGridInvertedLineCensus cfg p) :
    twelveGridActualExternalPoint hcard H 0 ≠
      twelveGridActualExternalPoint hcard H 1 := by
  intro h
  have h01 : (0 : Fin 2) = 1 :=
    twelveGridActualExternalPoint_injective hcard H h
  omega

/-- A reconstructed pencil centre is never one of the nine reconstructed
grid labels; their six-four degrees are respectively three and two. -/
theorem twelveGridActualExternalPoint_ne_gridPoint
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (hcard : Fintype.card Point = 12)
    (H : TwelveGridInvertedLineCensus cfg p)
    (a : Fin 2) (r s : Fin 3) :
    twelveGridActualExternalPoint hcard H a ≠
      twelveGridActualGridPoint hcard H r s := by
  intro h
  have ha := twelveGridActualExternalPoint_degree_eq_three hcard H a
  have hrs := twelveGridActualGridPoint_degree_eq_two hcard H r s
  rw [h] at ha
  omega

/-- Every actual inverted label belongs either to the external pencil-centre
pair or to the losslessly labelled nine-point grid. -/
theorem twelveGridActualPoint_external_or_grid
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (hcard : Fintype.card Point = 12)
    (H : TwelveGridInvertedLineCensus cfg p) (q : AwayFrom p) :
    (∃ a : Fin 2, twelveGridActualExternalPoint hcard H a = q) ∨
      (∃ r s : Fin 3, twelveGridActualGridPoint hcard H r s = q) := by
  rcases (H.fourLine_degree_profile hcard).2.2 q with htwo | hthree
  · right
    have hmem : q ∈ sixFourDegreeTwo (twelveGridActualFourSupport H) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, htwo⟩
    rw [← twelveGridActualGridImage_eq_degreeTwo hcard H] at hmem
    obtain ⟨⟨r, s⟩, _hrs, hq⟩ := Finset.mem_image.mp hmem
    exact ⟨r, s, hq⟩
  · left
    exact (sixFour_degree_eq_three_iff_external
      (twelveGridActualFourSupport_isSaturatedSixFour hcard H) q).mp hthree

/-- A size-three actual line and any reconstructed four-line meet in at
most one inverted label. -/
theorem twelveGridThreeLine_support_inter_pencil_lt_two
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (hcard : Fintype.card Point = 12)
    (H : TwelveGridInvertedLineCensus cfg p)
    (L : DeterminedLineOfSize (pivotInversion cfg p) 3)
    (a : Fin 2) (r : Fin 3) :
    (lineSupport (pivotInversion cfg p) L.1 ∩
      lineSupport (pivotInversion cfg p)
        (twelveGridActualPencilLine hcard H a r).1).card < 2 := by
  let Q := pivotInversion cfg p
  have hlineNe : L.1 ≠ (twelveGridActualPencilLine hcard H a r).1 := by
    intro h
    have hthree := L.2
    rw [h, (twelveGridActualPencilLine hcard H a r).2] at hthree
    omega
  let bi : GeometricBlock Q := Sum.inl L.1
  let bj : GeometricBlock Q :=
    Sum.inl (twelveGridActualPencilLine hcard H a r).1
  let Li : (blockSystem Q).LineBlock := ⟨bi, rfl⟩
  let Lj : (blockSystem Q).LineBlock := ⟨bj, rfl⟩
  have hLiNe : Li ≠ Lj := by
    intro h
    apply hlineNe
    simpa [Li, Lj, bi, bj] using h
  have hinter := (blockSystem Q).distinct_line_inter_card_lt_two hLiNe
  simpa [Q, Li, Lj, bi, bj, geometricBlockSupport] using hinter

/-- A size-two actual line and any reconstructed four-line meet in at most
one inverted label. -/
theorem twelveGridOrdinaryLine_support_inter_pencil_lt_two
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (hcard : Fintype.card Point = 12)
    (H : TwelveGridInvertedLineCensus cfg p)
    (L : DeterminedLineOfSize (pivotInversion cfg p) 2)
    (a : Fin 2) (r : Fin 3) :
    (lineSupport (pivotInversion cfg p) L.1 ∩
      lineSupport (pivotInversion cfg p)
        (twelveGridActualPencilLine hcard H a r).1).card < 2 := by
  let Q := pivotInversion cfg p
  have hlineNe : L.1 ≠ (twelveGridActualPencilLine hcard H a r).1 := by
    intro h
    have htwo := L.2
    rw [h, (twelveGridActualPencilLine hcard H a r).2] at htwo
    omega
  let bi : GeometricBlock Q := Sum.inl L.1
  let bj : GeometricBlock Q :=
    Sum.inl (twelveGridActualPencilLine hcard H a r).1
  let Li : (blockSystem Q).LineBlock := ⟨bi, rfl⟩
  let Lj : (blockSystem Q).LineBlock := ⟨bj, rfl⟩
  have hLiNe : Li ≠ Lj := by
    intro h
    apply hlineNe
    simpa [Li, Lj, bi, bj] using h
  have hinter := (blockSystem Q).distinct_line_inter_card_lt_two hLiNe
  simpa [Q, Li, Lj, bi, bj, geometricBlockSupport] using hinter

/-- An external pencil centre and a labelled grid crossing cannot lie
together on an actual size-three line. -/
theorem twelveGridThreeLine_external_grid_forbidden
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (hcard : Fintype.card Point = 12)
    (H : TwelveGridInvertedLineCensus cfg p)
    (L : DeterminedLineOfSize (pivotInversion cfg p) 3)
    (a : Fin 2) (r s : Fin 3)
    (hext : twelveGridActualExternalPoint hcard H a ∈
      lineSupport (pivotInversion cfg p) L.1)
    (hgrid : twelveGridActualGridPoint hcard H r s ∈
      lineSupport (pivotInversion cfg p) L.1) : False := by
  have hne := twelveGridActualExternalPoint_ne_gridPoint hcard H a r s
  fin_cases a
  · have hsub : ({twelveGridActualExternalPoint hcard H 0,
        twelveGridActualGridPoint hcard H r s} : Finset (AwayFrom p)) ⊆
        lineSupport (pivotInversion cfg p) L.1 ∩
          lineSupport (pivotInversion cfg p)
            (twelveGridActualPencilLine hcard H 0 r).1 := by
      intro q hq
      simp only [Finset.mem_insert, Finset.mem_singleton] at hq
      rcases hq with rfl | rfl
      · exact Finset.mem_inter.mpr ⟨hext,
          twelveGridActualExternalPoint_mem_pencilLine hcard H 0 r⟩
      · exact Finset.mem_inter.mpr ⟨hgrid,
          twelveGridActualGridPoint_mem_row hcard H r s⟩
    have hle := Finset.card_le_card hsub
    have hpair : ({twelveGridActualExternalPoint hcard H 0,
        twelveGridActualGridPoint hcard H r s} : Finset (AwayFrom p)).card = 2 := by
      exact Finset.card_pair hne
    rw [hpair] at hle
    have hlt := twelveGridThreeLine_support_inter_pencil_lt_two hcard H L 0 r
    omega
  · have hsub : ({twelveGridActualExternalPoint hcard H 1,
        twelveGridActualGridPoint hcard H r s} : Finset (AwayFrom p)) ⊆
        lineSupport (pivotInversion cfg p) L.1 ∩
          lineSupport (pivotInversion cfg p)
            (twelveGridActualPencilLine hcard H 1 s).1 := by
      intro q hq
      simp only [Finset.mem_insert, Finset.mem_singleton] at hq
      rcases hq with rfl | rfl
      · exact Finset.mem_inter.mpr ⟨hext,
          twelveGridActualExternalPoint_mem_pencilLine hcard H 1 s⟩
      · exact Finset.mem_inter.mpr ⟨hgrid,
          twelveGridActualGridPoint_mem_column hcard H r s⟩
    have hle := Finset.card_le_card hsub
    have hpair : ({twelveGridActualExternalPoint hcard H 1,
        twelveGridActualGridPoint hcard H r s} : Finset (AwayFrom p)).card = 2 := by
      exact Finset.card_pair hne
    rw [hpair] at hle
    have hlt := twelveGridThreeLine_support_inter_pencil_lt_two hcard H L 1 s
    omega

/-- An external pencil centre and a labelled grid crossing cannot lie
together on an actual ordinary line. -/
theorem twelveGridOrdinaryLine_external_grid_forbidden
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (hcard : Fintype.card Point = 12)
    (H : TwelveGridInvertedLineCensus cfg p)
    (L : DeterminedLineOfSize (pivotInversion cfg p) 2)
    (a : Fin 2) (r s : Fin 3)
    (hext : twelveGridActualExternalPoint hcard H a ∈
      lineSupport (pivotInversion cfg p) L.1)
    (hgrid : twelveGridActualGridPoint hcard H r s ∈
      lineSupport (pivotInversion cfg p) L.1) : False := by
  have hne := twelveGridActualExternalPoint_ne_gridPoint hcard H a r s
  fin_cases a
  · have hsub : ({twelveGridActualExternalPoint hcard H 0,
        twelveGridActualGridPoint hcard H r s} : Finset (AwayFrom p)) ⊆
        lineSupport (pivotInversion cfg p) L.1 ∩
          lineSupport (pivotInversion cfg p)
            (twelveGridActualPencilLine hcard H 0 r).1 := by
      intro q hq
      simp only [Finset.mem_insert, Finset.mem_singleton] at hq
      rcases hq with rfl | rfl
      · exact Finset.mem_inter.mpr ⟨hext,
          twelveGridActualExternalPoint_mem_pencilLine hcard H 0 r⟩
      · exact Finset.mem_inter.mpr ⟨hgrid,
          twelveGridActualGridPoint_mem_row hcard H r s⟩
    have hle := Finset.card_le_card hsub
    have hpair : ({twelveGridActualExternalPoint hcard H 0,
        twelveGridActualGridPoint hcard H r s} : Finset (AwayFrom p)).card = 2 := by
      exact Finset.card_pair hne
    rw [hpair] at hle
    have hlt := twelveGridOrdinaryLine_support_inter_pencil_lt_two hcard H L 0 r
    omega
  · have hsub : ({twelveGridActualExternalPoint hcard H 1,
        twelveGridActualGridPoint hcard H r s} : Finset (AwayFrom p)) ⊆
        lineSupport (pivotInversion cfg p) L.1 ∩
          lineSupport (pivotInversion cfg p)
            (twelveGridActualPencilLine hcard H 1 s).1 := by
      intro q hq
      simp only [Finset.mem_insert, Finset.mem_singleton] at hq
      rcases hq with rfl | rfl
      · exact Finset.mem_inter.mpr ⟨hext,
          twelveGridActualExternalPoint_mem_pencilLine hcard H 1 s⟩
      · exact Finset.mem_inter.mpr ⟨hgrid,
          twelveGridActualGridPoint_mem_column hcard H r s⟩
    have hle := Finset.card_le_card hsub
    have hpair : ({twelveGridActualExternalPoint hcard H 1,
        twelveGridActualGridPoint hcard H r s} : Finset (AwayFrom p)).card = 2 := by
      exact Finset.card_pair hne
    rw [hpair] at hle
    have hlt := twelveGridOrdinaryLine_support_inter_pencil_lt_two hcard H L 1 s
    omega

/-- No actual size-three line contains either reconstructed pencil centre. -/
theorem twelveGridThreeLine_external_not_mem
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (hcard : Fintype.card Point = 12)
    (H : TwelveGridInvertedLineCensus cfg p)
    (L : DeterminedLineOfSize (pivotInversion cfg p) 3)
    (a : Fin 2) :
    twelveGridActualExternalPoint hcard H a ∉
      lineSupport (pivotInversion cfg p) L.1 := by
  intro hext
  have hextNe := twelveGridActualExternalPoint_zero_ne_one hcard H
  have hnotSubset : ¬ lineSupport (pivotInversion cfg p) L.1 ⊆
      ({twelveGridActualExternalPoint hcard H 0,
        twelveGridActualExternalPoint hcard H 1} : Finset (AwayFrom p)) := by
    intro hsub
    have hle := Finset.card_le_card hsub
    have hpair : ({twelveGridActualExternalPoint hcard H 0,
        twelveGridActualExternalPoint hcard H 1} : Finset (AwayFrom p)).card = 2 := by
      simp [hextNe]
    rw [L.2, hpair] at hle
    omega
  obtain ⟨q, hq, hqnot⟩ := Finset.not_subset.mp hnotSubset
  rcases twelveGridActualPoint_external_or_grid hcard H q with hqext | hqgrid
  · obtain ⟨b, hb⟩ := hqext
    apply hqnot
    rw [← hb]
    fin_cases b <;> simp
  · obtain ⟨r, s, hgrid⟩ := hqgrid
    have hgridMem : twelveGridActualGridPoint hcard H r s ∈
        lineSupport (pivotInversion cfg p) L.1 := by
      rw [hgrid]
      exact hq
    exact twelveGridThreeLine_external_grid_forbidden hcard H L a r s hext hgridMem

/-- Every point of an actual size-three line has a concrete `Fin 3 x Fin 3`
grid coordinate. -/
theorem twelveGridThreeLine_point_is_grid
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (hcard : Fintype.card Point = 12)
    (H : TwelveGridInvertedLineCensus cfg p)
    (L : DeterminedLineOfSize (pivotInversion cfg p) 3)
    {q : AwayFrom p}
    (hq : q ∈ lineSupport (pivotInversion cfg p) L.1) :
    ∃ r s : Fin 3, twelveGridActualGridPoint hcard H r s = q := by
  rcases twelveGridActualPoint_external_or_grid hcard H q with hqext | hqgrid
  · obtain ⟨a, ha⟩ := hqext
    have hmem : twelveGridActualExternalPoint hcard H a ∈
        lineSupport (pivotInversion cfg p) L.1 := by
      rw [ha]
      exact hq
    exact False.elim (twelveGridThreeLine_external_not_mem hcard H L a hmem)
  · exact hqgrid

/-- A lossless actual transversal: its three points are actual grid labels,
and it meets each actual row and column in at most one labelled point.  Since
the support has cardinality three, these sparse incidences are exactly the
usual three-by-three transversal condition. -/
structure TwelveGridActualGridTransversal
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (hcard : Fintype.card Point = 12)
    (H : TwelveGridInvertedLineCensus cfg p) : Type u where
  line : DeterminedLineOfSize (pivotInversion cfg p) 3
  point_is_grid : ∀ q, q ∈ lineSupport (pivotInversion cfg p) line.1 →
    ∃ r s : Fin 3, twelveGridActualGridPoint hcard H r s = q
  row_inter_card_le_one : ∀ r : Fin 3,
    (lineSupport (pivotInversion cfg p) line.1 ∩
      lineSupport (pivotInversion cfg p)
        (twelveGridActualPencilLine hcard H 0 r).1).card ≤ 1
  column_inter_card_le_one : ∀ s : Fin 3,
    (lineSupport (pivotInversion cfg p) line.1 ∩
      lineSupport (pivotInversion cfg p)
        (twelveGridActualPencilLine hcard H 1 s).1).card ≤ 1

/-- Each of the two actual size-three census lines is a concrete grid
transversal. -/
noncomputable def twelveGridActualThreeLineTransversal
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (hcard : Fintype.card Point = 12)
    (H : TwelveGridInvertedLineCensus cfg p) (i : Fin 2) :
    TwelveGridActualGridTransversal hcard H where
  line := H.threeLine i
  point_is_grid := by
    intro q hq
    exact twelveGridThreeLine_point_is_grid hcard H (H.threeLine i) hq
  row_inter_card_le_one := by
    intro r
    have hlt := twelveGridThreeLine_support_inter_pencil_lt_two
      hcard H (H.threeLine i) 0 r
    omega
  column_inter_card_le_one := by
    intro s
    have hlt := twelveGridThreeLine_support_inter_pencil_lt_two
      hcard H (H.threeLine i) 1 s
    omega

/-- The two displayed actual transversals are distinct actual lines. -/
theorem twelveGridActualThreeLineTransversal_line_injective
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (hcard : Fintype.card Point = 12)
    (H : TwelveGridInvertedLineCensus cfg p) :
    Function.Injective (fun i : Fin 2 =>
      (twelveGridActualThreeLineTransversal hcard H i).line) := by
  simpa [twelveGridActualThreeLineTransversal] using H.threeLine.injective

/-- The two actual transversal supports have no repeated pair of grid
labels. -/
theorem twelveGridActualThreeLine_support_inter_lt_two
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (H : TwelveGridInvertedLineCensus cfg p)
    {i j : Fin 2} (hij : i ≠ j) :
    (lineSupport (pivotInversion cfg p) (H.threeLine i).1 ∩
      lineSupport (pivotInversion cfg p) (H.threeLine j).1).card < 2 := by
  let Q := pivotInversion cfg p
  let bi : GeometricBlock Q := Sum.inl (H.threeLine i).1
  let bj : GeometricBlock Q := Sum.inl (H.threeLine j).1
  let Li : (blockSystem Q).LineBlock := ⟨bi, rfl⟩
  let Lj : (blockSystem Q).LineBlock := ⟨bj, rfl⟩
  have hLiNe : Li ≠ Lj := by
    intro h
    have hline : (H.threeLine i).1 = (H.threeLine j).1 := by
      have h' := congrArg (fun L : (blockSystem Q).LineBlock => L.1) h
      simpa [Li, Lj, bi, bj] using h'
    exact hij (H.threeLine.injective (Subtype.ext hline))
  have hinter := (blockSystem Q).distinct_line_inter_card_lt_two hLiNe
  simpa [Q, Li, Lj, bi, bj, geometricBlockSupport] using hinter

/-- Enumerate the original size-three lines through the pivot without
discarding their provenance. -/
noncomputable def twelveGridOriginalThreeLineEquiv
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    (cfg : Configuration Point) (p : Point) (n : ℕ)
    (hlineThree : (blockSystem cfg).lineDegree 3 p = n) :
    Fin n ≃ TaggedLineAtSize cfg p 3 := by
  apply (Fintype.equivFinOfCardEq ?_).symm
  rw [← lineDegree_eq_card_taggedLineAtSize]
  exact hlineThree

/-- A tagged original three-line through the pivot is carried by an affine
line through the original pivot after inversion. -/
theorem taggedThreeLineInvertedOrdinaryLine_contains_pivot
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (b : TaggedLineAtSize cfg p 3) :
    cfg p ∈ (taggedThreeLineInvertedOrdinaryLine b).1.1 := by
  change cfg p ∈ (blockToPivotLine cfg p (taggedThreeLinePivotBlock b)).1
  cases hline : b.1 with
  | inl L =>
      have hpLine : p ∈ lineSupport cfg L := by
        simpa [hline, geometricBlockSupport] using b.2.2.2
      have hsizeLine : (lineSupport cfg L).card = 3 := by
        simpa [hline, geometricBlockSupport] using b.2.2.1
      have hcardLine : 3 ≤ (lineSupport cfg L).card := by
        omega
      let pb : PivotBlock cfg p :=
        ⟨Sum.inl L, by simpa [geometricBlockSupport] using hpLine,
          by simpa [geometricBlockSupport] using hcardLine⟩
      have hpb : taggedThreeLinePivotBlock b = pb := by
        apply Subtype.ext
        exact hline
      rw [hpb]
      simpa [pb, blockToPivotLine] using
        (mem_lineSupport.mp hpLine)
  | inr c =>
      have hkind : BlockKind.circle = BlockKind.line := by
        simpa [hline, geometricBlockKind] using b.2.1
      cases hkind

/-- The actual ordinary inverted line arising from the i-th original
three-line through the pivot. -/
noncomputable def twelveGridOriginalThreeLineInvertedOrdinary
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (n : ℕ) (hlineThree : (blockSystem cfg).lineDegree 3 p = n)
    (i : Fin n) :
    DeterminedLineOfSize (pivotInversion cfg p) 2 :=
  taggedThreeLineInvertedOrdinaryLine
    (twelveGridOriginalThreeLineEquiv cfg p n hlineThree i)

/-- The full ordinary-line census supplies the actual census index of every
ordinary line obtained from an original pivot three-line. -/
noncomputable def twelveGridOriginalThreeLineOrdinaryIndex
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (H : TwelveGridInvertedLineCensus cfg p)
    (n : ℕ) (hlineThree : (blockSystem cfg).lineDegree 3 p = n)
    (i : Fin n) : Fin 13 :=
  H.ordinaryLine.symm
    (twelveGridOriginalThreeLineInvertedOrdinary
      (cfg := cfg) (p := p) n hlineThree i)

/-- The preceding index is lossless: applying the actual ordinary census
recovers the original-line image exactly. -/
@[simp] theorem twelveGridOriginalThreeLineOrdinaryIndex_spec
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (H : TwelveGridInvertedLineCensus cfg p)
    (n : ℕ) (hlineThree : (blockSystem cfg).lineDegree 3 p = n)
    (i : Fin n) :
    H.ordinaryLine
      (twelveGridOriginalThreeLineOrdinaryIndex H n hlineThree i) =
      twelveGridOriginalThreeLineInvertedOrdinary
        (cfg := cfg) (p := p) n hlineThree i := by
  simp [twelveGridOriginalThreeLineOrdinaryIndex]

/-- Every ordinary line coming from an original three-line is concurrent at
the actual inversion centre. -/
theorem twelveGridOriginalThreeLineInvertedOrdinary_contains_pivot
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (n : ℕ) (hlineThree : (blockSystem cfg).lineDegree 3 p = n)
    (i : Fin n) :
    cfg p ∈
      (twelveGridOriginalThreeLineInvertedOrdinary
        (cfg := cfg) (p := p) n hlineThree i).1.1 := by
  exact taggedThreeLineInvertedOrdinaryLine_contains_pivot
    (twelveGridOriginalThreeLineEquiv cfg p n hlineThree i)

/-- Distinct original pivot three-lines give disjoint ordinary inverted
supports. -/
theorem twelveGridOriginalThreeLineInvertedOrdinary_disjoint
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (n : ℕ) (hlineThree : (blockSystem cfg).lineDegree 3 p = n)
    {i j : Fin n} (hij : i ≠ j) :
    Disjoint
      (lineSupport (pivotInversion cfg p)
        (twelveGridOriginalThreeLineInvertedOrdinary
          (cfg := cfg) (p := p) n hlineThree i).1)
      (lineSupport (pivotInversion cfg p)
        (twelveGridOriginalThreeLineInvertedOrdinary
          (cfg := cfg) (p := p) n hlineThree j).1) := by
  apply taggedThreeLineInvertedOrdinaryLines_disjoint
  exact (twelveGridOriginalThreeLineEquiv cfg p n hlineThree).injective.ne hij

/-- The finite pair of actual pencil centres, viewed as an actual
two-point support. -/
noncomputable def twelveGridExternalPair
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (hcard : Fintype.card Point = 12)
    (H : TwelveGridInvertedLineCensus cfg p) : Finset (AwayFrom p) :=
  {twelveGridActualExternalPoint hcard H 0,
    twelveGridActualExternalPoint hcard H 1}

theorem twelveGridExternalPair_card
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (hcard : Fintype.card Point = 12)
    (H : TwelveGridInvertedLineCensus cfg p) :
    (twelveGridExternalPair hcard H).card = 2 := by
  simp [twelveGridExternalPair,
    twelveGridActualExternalPoint_zero_ne_one hcard H]

/-- An actual ordinary line is either a genuine grid secant (both of its
actual labels are grid labels), or it is exactly the exceptional line joining
the two pencil centres. -/
theorem twelveGridOrdinaryLine_grid_or_externalPair
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (hcard : Fintype.card Point = 12)
    (H : TwelveGridInvertedLineCensus cfg p)
    (L : DeterminedLineOfSize (pivotInversion cfg p) 2) :
    (∀ q, q ∈ lineSupport (pivotInversion cfg p) L.1 →
      ∃ r s : Fin 3, twelveGridActualGridPoint hcard H r s = q) ∨
      lineSupport (pivotInversion cfg p) L.1 =
        twelveGridExternalPair hcard H := by
  classical
  by_cases hext : ∃ a : Fin 2, twelveGridActualExternalPoint hcard H a ∈
      lineSupport (pivotInversion cfg p) L.1
  · right
    obtain ⟨a, ha⟩ := hext
    have hsub : lineSupport (pivotInversion cfg p) L.1 ⊆
        twelveGridExternalPair hcard H := by
      intro q hq
      rcases twelveGridActualPoint_external_or_grid hcard H q with hqext | hqgrid
      · obtain ⟨b, hb⟩ := hqext
        rw [← hb]
        fin_cases b <;> simp [twelveGridExternalPair]
      · obtain ⟨r, s, hg⟩ := hqgrid
        exfalso
        apply twelveGridOrdinaryLine_external_grid_forbidden
          hcard H L a r s ha
        rw [hg]
        exact hq
    apply Finset.eq_of_subset_of_card_le hsub
    rw [twelveGridExternalPair_card hcard H, L.2]
  · left
    intro q hq
    rcases twelveGridActualPoint_external_or_grid hcard H q with hqext | hqgrid
    · obtain ⟨a, ha⟩ := hqext
      exfalso
      apply hext
      refine ⟨a, ?_⟩
      rw [ha]
      exact hq
    · exact hqgrid

/-- Each ordinary line coming from an original pivot three-line has the
grid-secant-versus-centre-pair dichotomy. -/
theorem twelveGridOriginalThreeLineInvertedOrdinary_grid_or_externalPair
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (hcard : Fintype.card Point = 12)
    (H : TwelveGridInvertedLineCensus cfg p)
    (n : ℕ) (hlineThree : (blockSystem cfg).lineDegree 3 p = n)
    (i : Fin n) :
    (∀ q, q ∈ lineSupport (pivotInversion cfg p)
        (twelveGridOriginalThreeLineInvertedOrdinary
          (cfg := cfg) (p := p) n hlineThree i).1 →
      ∃ r s : Fin 3, twelveGridActualGridPoint hcard H r s = q) ∨
      lineSupport (pivotInversion cfg p)
        (twelveGridOriginalThreeLineInvertedOrdinary
          (cfg := cfg) (p := p) n hlineThree i).1 =
        twelveGridExternalPair hcard H :=
  twelveGridOrdinaryLine_grid_or_externalPair hcard H
    (twelveGridOriginalThreeLineInvertedOrdinary
      (cfg := cfg) (p := p) n hlineThree i)

/-- At most one original pivot three-line can invert to the exceptional
centre-pair line.  The source ordinary lines are disjoint, while the centre
pair is nonempty. -/
theorem twelveGridOriginalThreeLineInvertedOrdinary_externalPair_unique
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (hcard : Fintype.card Point = 12)
    (H : TwelveGridInvertedLineCensus cfg p)
    (n : ℕ) (hlineThree : (blockSystem cfg).lineDegree 3 p = n)
    {i j : Fin n}
    (hi : lineSupport (pivotInversion cfg p)
        (twelveGridOriginalThreeLineInvertedOrdinary
          (cfg := cfg) (p := p) n hlineThree i).1 =
        twelveGridExternalPair hcard H)
    (hj : lineSupport (pivotInversion cfg p)
        (twelveGridOriginalThreeLineInvertedOrdinary
          (cfg := cfg) (p := p) n hlineThree j).1 =
        twelveGridExternalPair hcard H) :
    i = j := by
  by_contra hij
  have hdis := twelveGridOriginalThreeLineInvertedOrdinary_disjoint
    (cfg := cfg) (p := p) n hlineThree hij
  have hleft := Finset.disjoint_left.mp hdis
  apply hleft (a := twelveGridActualExternalPoint hcard H 0)
  · rw [hi]
    simp [twelveGridExternalPair]
  · rw [hj]
    simp [twelveGridExternalPair]

/-- Indices of original pivot three-lines whose ordinary image is the unique
possible centre-pair exception. -/
noncomputable def twelveGridOriginalThreeLineExceptionalIndices
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (hcard : Fintype.card Point = 12)
    (H : TwelveGridInvertedLineCensus cfg p)
    (n : ℕ) (hlineThree : (blockSystem cfg).lineDegree 3 p = n) :
    Finset (Fin n) :=
  (Finset.univ : Finset (Fin n)).filter fun i =>
    lineSupport (pivotInversion cfg p)
      (twelveGridOriginalThreeLineInvertedOrdinary
        (cfg := cfg) (p := p) n hlineThree i).1 =
      twelveGridExternalPair hcard H

/-- Indices of original pivot three-lines whose ordinary image is an actual
grid secant. -/
noncomputable def twelveGridOriginalThreeLineGridSecantIndices
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (hcard : Fintype.card Point = 12)
    (H : TwelveGridInvertedLineCensus cfg p)
    (n : ℕ) (hlineThree : (blockSystem cfg).lineDegree 3 p = n) :
    Finset (Fin n) :=
  (Finset.univ : Finset (Fin n)).filter fun i =>
    ¬ lineSupport (pivotInversion cfg p)
      (twelveGridOriginalThreeLineInvertedOrdinary
        (cfg := cfg) (p := p) n hlineThree i).1 =
      twelveGridExternalPair hcard H

/-- There is at most one exceptional centre-pair image among all original
pivot three-lines. -/
theorem twelveGridOriginalThreeLineExceptionalIndices_card_le_one
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (hcard : Fintype.card Point = 12)
    (H : TwelveGridInvertedLineCensus cfg p)
    (n : ℕ) (hlineThree : (blockSystem cfg).lineDegree 3 p = n) :
    (twelveGridOriginalThreeLineExceptionalIndices hcard H n hlineThree).card ≤ 1 := by
  classical
  rw [twelveGridOriginalThreeLineExceptionalIndices, Finset.card_le_one]
  intro i hi j hj
  exact twelveGridOriginalThreeLineInvertedOrdinary_externalPair_unique
    hcard H n hlineThree
    (Finset.mem_filter.mp hi).2 (Finset.mem_filter.mp hj).2

/-- Every nonexceptional original pivot three-line gives an actual ordinary
grid secant, with both endpoints carrying explicit Fin 3 times Fin 3
labels. -/
theorem twelveGridOriginalThreeLine_mem_gridSecantIndices
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (hcard : Fintype.card Point = 12)
    (H : TwelveGridInvertedLineCensus cfg p)
    (n : ℕ) (hlineThree : (blockSystem cfg).lineDegree 3 p = n)
    {i : Fin n}
    (hi : i ∈ twelveGridOriginalThreeLineGridSecantIndices hcard H n hlineThree) :
    ∀ q, q ∈ lineSupport (pivotInversion cfg p)
        (twelveGridOriginalThreeLineInvertedOrdinary
          (cfg := cfg) (p := p) n hlineThree i).1 →
      ∃ r s : Fin 3, twelveGridActualGridPoint hcard H r s = q := by
  have hnot := (Finset.mem_filter.mp hi).2
  rcases twelveGridOriginalThreeLineInvertedOrdinary_grid_or_externalPair
    hcard H n hlineThree i with hgrid | hpair
  · exact hgrid
  · exact False.elim (hnot hpair)

/-- All but at most one original pivot three-line become actual grid
secants. -/
theorem twelveGridOriginalThreeLineGridSecantIndices_card_ge_pred
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (hcard : Fintype.card Point = 12)
    (H : TwelveGridInvertedLineCensus cfg p)
    (n : ℕ) (hlineThree : (blockSystem cfg).lineDegree 3 p = n) :
    n - 1 ≤
      (twelveGridOriginalThreeLineGridSecantIndices hcard H n hlineThree).card := by
  classical
  have hbad := twelveGridOriginalThreeLineExceptionalIndices_card_le_one
    hcard H n hlineThree
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Fin n)))
    (p := fun i =>
      lineSupport (pivotInversion cfg p)
        (twelveGridOriginalThreeLineInvertedOrdinary
          (cfg := cfg) (p := p) n hlineThree i).1 =
        twelveGridExternalPair hcard H)
  have hsplit' :
      (twelveGridOriginalThreeLineExceptionalIndices hcard H n hlineThree).card +
        (twelveGridOriginalThreeLineGridSecantIndices hcard H n hlineThree).card =
        n := by
    simpa [twelveGridOriginalThreeLineExceptionalIndices,
      twelveGridOriginalThreeLineGridSecantIndices] using hsplit
  omega

/-- The complete incidence endpoint needed by the projective grid lemma.
It retains the two actual transversals, the original-line provenance of the
concurrent ordinary lines, their actual census indices, and the single
possible centre-pair exception. -/
structure TwelveGridTransversalExtraction
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (hcard : Fintype.card Point = 12)
    (H : TwelveGridInvertedLineCensus cfg p)
    (n : ℕ) (hlineThree : (blockSystem cfg).lineDegree 3 p = n) : Type u where
  transversal : Fin 2 → TwelveGridActualGridTransversal hcard H
  transversal_line : ∀ i, (transversal i).line = H.threeLine i
  pivotOrdinary : Fin n → DeterminedLineOfSize (pivotInversion cfg p) 2
  pivotOrdinary_actualIndex : Fin n → Fin 13
  pivotOrdinary_actual : ∀ i,
    H.ordinaryLine (pivotOrdinary_actualIndex i) = pivotOrdinary i
  pivotOrdinary_contains_pivot : ∀ i, cfg p ∈ (pivotOrdinary i).1.1
  pivotOrdinary_disjoint : ∀ ⦃i j⦄, i ≠ j →
    Disjoint
      (lineSupport (pivotInversion cfg p) (pivotOrdinary i).1)
      (lineSupport (pivotInversion cfg p) (pivotOrdinary j).1)
  pivotOrdinary_grid_or_externalPair : ∀ i,
    (∀ q, q ∈ lineSupport (pivotInversion cfg p) (pivotOrdinary i).1 →
      ∃ r s : Fin 3, twelveGridActualGridPoint hcard H r s = q) ∨
      lineSupport (pivotInversion cfg p) (pivotOrdinary i).1 =
        twelveGridExternalPair hcard H
  pivotOrdinary_externalPair_unique : ∀ ⦃i j⦄,
    lineSupport (pivotInversion cfg p) (pivotOrdinary i).1 =
      twelveGridExternalPair hcard H →
    lineSupport (pivotInversion cfg p) (pivotOrdinary j).1 =
      twelveGridExternalPair hcard H → i = j

/-- Construct the endpoint directly from the actual line census and the
given original three-line count. -/
noncomputable def twelveGridTransversalExtraction_of_census
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (hcard : Fintype.card Point = 12)
    (H : TwelveGridInvertedLineCensus cfg p)
    (n : ℕ) (hlineThree : (blockSystem cfg).lineDegree 3 p = n) :
    TwelveGridTransversalExtraction hcard H n hlineThree where
  transversal := fun i => twelveGridActualThreeLineTransversal hcard H i
  transversal_line := fun _ => rfl
  pivotOrdinary :=
    twelveGridOriginalThreeLineInvertedOrdinary
      (cfg := cfg) (p := p) n hlineThree
  pivotOrdinary_actualIndex :=
    twelveGridOriginalThreeLineOrdinaryIndex H n hlineThree
  pivotOrdinary_actual := fun i =>
    twelveGridOriginalThreeLineOrdinaryIndex_spec H n hlineThree i
  pivotOrdinary_contains_pivot := fun i =>
    twelveGridOriginalThreeLineInvertedOrdinary_contains_pivot
      (cfg := cfg) (p := p) n hlineThree i
  pivotOrdinary_disjoint := by
    intro i j hij
    exact twelveGridOriginalThreeLineInvertedOrdinary_disjoint
      (cfg := cfg) (p := p) n hlineThree hij
  pivotOrdinary_grid_or_externalPair := fun i =>
    twelveGridOriginalThreeLineInvertedOrdinary_grid_or_externalPair
      hcard H n hlineThree i
  pivotOrdinary_externalPair_unique := by
    intro i j hi hj
    exact twelveGridOriginalThreeLineInvertedOrdinary_externalPair_unique
      hcard H n hlineThree hi hj

/-- Type-zero supplies two actual transversals and five source ordinary
lines through the pivot, of which at least four are actual grid secants. -/
noncomputable def twelveGridTransversalExtraction_of_typeZero_row
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    (cfg : Configuration Point) (p : Point)
    (hcard : Fintype.card Point = 12)
    (hcap : Erdos506.V1.BlockSizeCap (blockSystem cfg) 5)
    (hthree : (blockSystem cfg).blockDegree 3 p = 13)
    (hfive : (blockSystem cfg).blockDegree 5 p = 6)
    (hlineThree : (blockSystem cfg).lineDegree 3 p = 5)
    (hlineFour : (blockSystem cfg).lineDegree 4 p = 0) :
    TwelveGridTransversalExtraction hcard
      (twelveGridInvertedLineCensus_of_typeZero_row cfg p hcard hcap hthree hfive
        hlineThree hlineFour) 5 hlineThree :=
  twelveGridTransversalExtraction_of_census hcard
    (twelveGridInvertedLineCensus_of_typeZero_row cfg p hcard hcap hthree hfive
      hlineThree hlineFour) 5 hlineThree

/-- Type-one supplies the same two actual transversals and four source
ordinary lines through the pivot, of which at least three are actual grid
secants. -/
noncomputable def twelveGridTransversalExtraction_of_typeOne_row
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    (cfg : Configuration Point) (p : Point)
    (hcard : Fintype.card Point = 12)
    (hcap : Erdos506.V1.BlockSizeCap (blockSystem cfg) 5)
    (hthree : (blockSystem cfg).blockDegree 3 p = 13)
    (hfive : (blockSystem cfg).blockDegree 5 p = 6)
    (hlineThree : (blockSystem cfg).lineDegree 3 p = 4)
    (hlineFour : (blockSystem cfg).lineDegree 4 p = 0) :
    TwelveGridTransversalExtraction hcard
      (twelveGridInvertedLineCensus_of_typeOne_row cfg p hcard hcap hthree hfive
        hlineThree hlineFour) 4 hlineThree :=
  twelveGridTransversalExtraction_of_census hcard
    (twelveGridInvertedLineCensus_of_typeOne_row cfg p hcard hcap hthree hfive
      hlineThree hlineFour) 4 hlineThree

/-- Numerical form of the type-zero endpoint: the five source ordinary
lines leave at least four actual grid secants through the pivot. -/
theorem twelveGridTypeZero_gridSecantIndices_card_ge_four
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (hcard : Fintype.card Point = 12)
    (H : TwelveGridInvertedLineCensus cfg p)
    (hlineThree : (blockSystem cfg).lineDegree 3 p = 5) :
    4 ≤ (twelveGridOriginalThreeLineGridSecantIndices
      hcard H 5 hlineThree).card := by
  simpa using
    (twelveGridOriginalThreeLineGridSecantIndices_card_ge_pred
      hcard H 5 hlineThree)

/-- Numerical form of the type-one endpoint: the four source ordinary
lines leave at least three actual grid secants through the pivot. -/
theorem twelveGridTypeOne_gridSecantIndices_card_ge_three
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (hcard : Fintype.card Point = 12)
    (H : TwelveGridInvertedLineCensus cfg p)
    (hlineThree : (blockSystem cfg).lineDegree 3 p = 4) :
    3 ≤ (twelveGridOriginalThreeLineGridSecantIndices
      hcard H 4 hlineThree).card := by
  simpa using
    (twelveGridOriginalThreeLineGridSecantIndices_card_ge_pred
      hcard H 4 hlineThree)

end Erdos506.V1
