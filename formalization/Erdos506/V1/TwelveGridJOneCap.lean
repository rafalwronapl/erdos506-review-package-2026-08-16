import Erdos506.V1.TwelveGridIncidenceExtraction
import Erdos506.Block.Moments
import Erdos506.Finite.IncidenceMoments
import Erdos506.Finite.SixFourGridReconstruction

/-!
# The `j = 1` grid entrance

For the local row `d3(p) = 10`, the only obstruction to the desired
five-degree cap is the equality case `d5(p) = 6`.  This file makes the
whole combinatorial part of that equality case explicit.  Pivot inversion
then has exactly ten ordinary lines, three three-lines, and six four-lines.

The remaining, genuinely projective, statement is that this exact incidence
census supplies a `TwelveGridNormalTransfer`: its six four-lines must form
the two pencils of a real `3 x 3` grid and its three three-lines must be the
three external transversals.  `TwelveGridNormalTransfer.impossible` closes
that last statement once such a normalization is constructed.
-/

namespace Erdos506.V1

open Erdos506.Block
open Erdos506.Block.BlockSystem
open Erdos506.Finite
open Erdos506.Incidence
open Erdos506.V3
open Erdos506.V4
open scoped BigOperators

universe u

/-! ## The numerical equality case -/

private theorem twelveGridJOne_two_mul_choose_two (n : Nat) :
    2 * Nat.choose n 2 = n * (n - 1) := by
  have h := Nat.choose_succ_right_eq n 1
  simpa [Nat.choose_one_right, Nat.mul_comm] using h

/-- Seven blocks of size at least five cannot pass through one selected
point of a twelve-point block system.  This is the local first/second-moment
argument, included here so that the `j = 1` reduction does not require the
separate Gram interface. -/
private theorem twelveGridJOne_seven_rich_through_point_impossible
    {Point Block : Type*} [Fintype Point] [Fintype Block]
    [DecidableEq Point] [DecidableEq Block]
    (S : BlockSystem Point Block) (hPoint : Fintype.card Point = 12)
    (F : Finset Block) (p : Point) (hFcard : F.card = 7)
    (hp : forall b, b ∈ F -> p ∈ S.support b)
    (hrich : forall b, b ∈ F -> 5 <= (S.support b).card) : False := by
  classical
  have hpDegree : S.degreeIn F p = 7 := by
    unfold BlockSystem.degreeIn
    have hfilter : F.filter (fun b => p ∈ S.support b) = F := by
      apply Finset.filter_eq_self.mpr
      exact hp
    rw [hfilter, hFcard]
  have hfirst := S.first_moment F
  have hfirstLower : 35 <= ∑ q : Point, S.degreeIn F q := by
    rw [hfirst]
    calc
      35 = ∑ _b ∈ F, 5 := by simp [hFcard]
      _ <= ∑ b ∈ F, (S.support b).card := by
        exact Finset.sum_le_sum fun b hb => hrich b hb
  have hsecond := S.second_moment_le_two_choose F
  rw [hFcard] at hsecond
  norm_num [Nat.choose] at hsecond
  have htwice_le_choose_add_three (n : Nat) :
      2 * n <= Nat.choose n 2 + 3 := by
    by_cases hn : n <= 3
    · interval_cases n <;> norm_num [Nat.choose]
    · have hn4 : 4 <= n := by omega
      have hsub : n - 1 + 1 = n := by omega
      have hchoose := twelveGridJOne_two_mul_choose_two n
      nlinarith
  have hpointwise (q : Point) :
      2 * S.degreeIn F q + (if q = p then 10 else 0) <=
        Nat.choose (S.degreeIn F q) 2 + 3 := by
    by_cases hqp : q = p
    · subst q
      simp [hpDegree, Nat.choose]
    · simpa [hqp] using htwice_le_choose_add_three (S.degreeIn F q)
  have hsum := Finset.sum_le_sum
    (s := (Finset.univ : Finset Point))
    (fun q _hq => hpointwise q)
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul] at hsum
  have hite : (∑ q : Point, if q = p then 10 else 0) = 10 := by simp
  rw [hite, hPoint] at hsum
  have htwice :
      (∑ q : Point, 2 * S.degreeIn F q) =
        2 * (∑ q : Point, S.degreeIn F q) := by
    rw [Finset.mul_sum]
  rw [htwice] at hsum
  omega

/-- The universal local five-degree bound on twelve labels. -/
theorem twelveGridJOne_five_degree_le_six
    {Point Block : Type*} [Fintype Point] [Fintype Block]
    [DecidableEq Point] [DecidableEq Block]
    (S : BlockSystem Point Block) (hPoint : Fintype.card Point = 12)
    (p : Point) : S.blockDegree 5 p <= 6 := by
  classical
  by_contra hnot
  have hseven : 7 <= S.blockDegree 5 p := by omega
  let P := (S.blocksOfSize 5).filter fun b => p ∈ S.support b
  have hPcard : P.card = S.blockDegree 5 p := rfl
  obtain ⟨F, hFP, hFcard⟩ :=
    Finset.exists_subset_card_eq (show 7 <= P.card by simpa [hPcard])
  exact twelveGridJOne_seven_rich_through_point_impossible S hPoint F p hFcard
    (fun b hb => (Finset.mem_filter.mp (hFP hb)).2)
    (fun b hb => by
      have hb5 := S.mem_blocksOfSize.mp (Finset.mem_filter.mp (hFP hb)).1
      omega)

/-- Under a five-block cap, the `d3 = 10, d5 = 6` equality case leaves
exactly three three-point lines after inversion. -/
theorem twelveGridJOne_lineCount_three
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    (cfg : Configuration Point) (p : Point)
    (hcard : Fintype.card Point = 12)
    (hcap : BlockSizeCap (blockSystem cfg) 5)
    (hthree : (blockSystem cfg).blockDegree 3 p = 10)
    (hfive : (blockSystem cfg).blockDegree 5 p = 6) :
    (blockSystem (pivotInversion cfg p)).lineCount 3 = 3 := by
  classical
  have htwo : (blockSystem (pivotInversion cfg p)).lineCount 2 = 10 := by
    rw [← blockDegree_three_eq_lineCount_two_pivotInversion]
    exact hthree
  have hfour : (blockSystem (pivotInversion cfg p)).lineCount 4 = 6 := by
    rw [← blockDegree_eq_lineCount_pivotInversion cfg p 5 (by omega)]
    exact hfive
  have hl5 := twelveGridPivotInversion_lineCount_eq_zero_of_gt_four
    cfg p hcap 5 (by omega)
  have hl6 := twelveGridPivotInversion_lineCount_eq_zero_of_gt_four
    cfg p hcap 6 (by omega)
  have hl7 := twelveGridPivotInversion_lineCount_eq_zero_of_gt_four
    cfg p hcap 7 (by omega)
  have hl8 := twelveGridPivotInversion_lineCount_eq_zero_of_gt_four
    cfg p hcap 8 (by omega)
  have hl9 := twelveGridPivotInversion_lineCount_eq_zero_of_gt_four
    cfg p hcap 9 (by omega)
  have hl10 := twelveGridPivotInversion_lineCount_eq_zero_of_gt_four
    cfg p hcap 10 (by omega)
  have hl11 := twelveGridPivotInversion_lineCount_eq_zero_of_gt_four
    cfg p hcap 11 (by omega)
  have hcardAway : Fintype.card (AwayFrom p) = 11 := by
    rw [Erdos506.V3.card_awayFrom, hcard]
  have hpairs := (blockSystem (pivotInversion cfg p)).line_pair_partition_by_size
  rw [hcardAway] at hpairs
  norm_num [Finset.sum_range_succ, Nat.choose,
    htwo, hfour, hl5, hl6, hl7, hl8, hl9, hl10, hl11] at hpairs
  omega

/-- Full finite inverted census for the sole equality case relevant to
`j = 1`. -/
structure TwelveGridJOneInvertedLineCensus
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    (cfg : Configuration Point) (p : Point) : Type u where
  ordinaryLine : Fin 10 ≃ DeterminedLineOfSize (pivotInversion cfg p) 2
  threeLine : Fin 3 ≃ DeterminedLineOfSize (pivotInversion cfg p) 3
  fourLine : Fin 6 ≃ DeterminedLineOfSize (pivotInversion cfg p) 4
  lineSupport_card_le_four : forall L : DeterminedLine (pivotInversion cfg p),
    (lineSupport (pivotInversion cfg p) L).card <= 4

/-- Construct the equality-case census from the literal degrees at the
pivot; no unrecorded line-count or incidence assumption is used. -/
noncomputable def twelveGridJOneInvertedLineCensus_of_degree_row
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    (cfg : Configuration Point) (p : Point)
    (hcard : Fintype.card Point = 12)
    (hcap : BlockSizeCap (blockSystem cfg) 5)
    (hthree : (blockSystem cfg).blockDegree 3 p = 10)
    (hfive : (blockSystem cfg).blockDegree 5 p = 6) :
    TwelveGridJOneInvertedLineCensus cfg p where
  ordinaryLine := by
    apply (Fintype.equivFinOfCardEq ?_).symm
    rw [← lineCount_eq_card_determinedLineOfSize,
      ← blockDegree_three_eq_lineCount_two_pivotInversion]
    exact hthree
  threeLine := by
    apply (Fintype.equivFinOfCardEq ?_).symm
    rw [← lineCount_eq_card_determinedLineOfSize]
    exact twelveGridJOne_lineCount_three cfg p hcard hcap hthree hfive
  fourLine := twelveGridPivotFourLineEquiv cfg p hfive
  lineSupport_card_le_four :=
    twelveGridPivotInversion_lineSupport_card_le_four cfg p hcap

/-! ## The actual six-four reconstruction in the equality census -/

/-- The six four-line supports of the `j = 1` equality census.  This is an
actual family of supports, not an abstract incidence choice. -/
noncomputable def twelveGridJOneFourSupport
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (H : TwelveGridJOneInvertedLineCensus cfg p) :
    Fin 6 → Finset (AwayFrom p) :=
  fun i => lineSupport (pivotInversion cfg p) (H.fourLine i).1

/-- Different selected four-lines have at most one inverted label in
common, by determined-line ownership. -/
theorem TwelveGridJOneInvertedLineCensus.fourLine_support_inter_lt_two
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (H : TwelveGridJOneInvertedLineCensus cfg p) {i j : Fin 6} (hij : i ≠ j) :
    (lineSupport (pivotInversion cfg p) (H.fourLine i).1 ∩
      lineSupport (pivotInversion cfg p) (H.fourLine j).1).card < 2 := by
  let Q := pivotInversion cfg p
  let bi : GeometricBlock Q := Sum.inl (H.fourLine i).1
  let bj : GeometricBlock Q := Sum.inl (H.fourLine j).1
  let Li : (blockSystem Q).LineBlock := ⟨bi, rfl⟩
  let Lj : (blockSystem Q).LineBlock := ⟨bj, rfl⟩
  have hLiNe : Li ≠ Lj := by
    intro h
    apply hij
    apply H.fourLine.injective
    apply Subtype.ext
    simpa [Li, Lj, bi, bj] using h
  have hinter := (blockSystem Q).distinct_line_inter_card_lt_two hLiNe
  simpa [Q, Li, Lj, bi, bj, geometricBlockSupport] using hinter

/-- The actual six supports are saturated automatically on the eleven
surviving labels.  In particular, no additional grid-incidence hypothesis is
needed for the `j = 1` equality case. -/
theorem twelveGridJOneFourSupport_isSaturatedSixFour
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (hcard : Fintype.card Point = 12)
    (H : TwelveGridJOneInvertedLineCensus cfg p) :
    IsSaturatedSixFour (twelveGridJOneFourSupport H) where
  point_card := by
    rw [Erdos506.V3.card_awayFrom, hcard]
  base_card := fun i => (H.fourLine i).2
  pair_inter_le_one := by
    intro i j hij
    have hinter := H.fourLine_support_inter_lt_two hij
    simpa [twelveGridJOneFourSupport, Nat.lt_succ_iff] using hinter

/-- The two degree-three labels of the actual six-four family. -/
noncomputable def twelveGridJOneExternalPoint
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (hcard : Fintype.card Point = 12)
    (H : TwelveGridJOneInvertedLineCensus cfg p) : Fin 2 → AwayFrom p :=
  sixFourExternalPoint (twelveGridJOneFourSupport_isSaturatedSixFour hcard H)

/-- The three four-line indices through a selected external label. -/
noncomputable def twelveGridJOnePencilIndex
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (hcard : Fintype.card Point = 12)
    (H : TwelveGridJOneInvertedLineCensus cfg p)
    (a : Fin 2) : Fin 3 → Fin 6 :=
  sixFourExternalBase (twelveGridJOneFourSupport_isSaturatedSixFour hcard H) a

/-- One reconstructed member of either actual pencil. -/
noncomputable def twelveGridJOnePencilLine
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (hcard : Fintype.card Point = 12)
    (H : TwelveGridJOneInvertedLineCensus cfg p)
    (a : Fin 2) (r : Fin 3) :
    DeterminedLineOfSize (pivotInversion cfg p) 4 :=
  H.fourLine (twelveGridJOnePencilIndex hcard H a r)

/-- The nine actual row--column crossings, with no coordinate normalization
chosen. -/
noncomputable def twelveGridJOneGridPoint
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (hcard : Fintype.card Point = 12)
    (H : TwelveGridJOneInvertedLineCensus cfg p)
    (r s : Fin 3) : AwayFrom p :=
  sixFourGridPoint (twelveGridJOneFourSupport_isSaturatedSixFour hcard H) r s

theorem twelveGridJOneExternalPoint_injective
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (hcard : Fintype.card Point = 12)
    (H : TwelveGridJOneInvertedLineCensus cfg p) :
    Function.Injective (twelveGridJOneExternalPoint hcard H) :=
  sixFourExternalPoint_injective
    (twelveGridJOneFourSupport_isSaturatedSixFour hcard H)

theorem twelveGridJOneExternalPoint_degree_eq_three
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (hcard : Fintype.card Point = 12)
    (H : TwelveGridJOneInvertedLineCensus cfg p) (a : Fin 2) :
    sixFourDegree (twelveGridJOneFourSupport H)
      (twelveGridJOneExternalPoint hcard H a) = 3 :=
  sixFourExternalPoint_degree_eq_three
    (twelveGridJOneFourSupport_isSaturatedSixFour hcard H) a

theorem twelveGridJOneExternalPoint_mem_pencilLine
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (hcard : Fintype.card Point = 12)
    (H : TwelveGridJOneInvertedLineCensus cfg p)
    (a : Fin 2) (r : Fin 3) :
    twelveGridJOneExternalPoint hcard H a ∈
      lineSupport (pivotInversion cfg p)
        (twelveGridJOnePencilLine hcard H a r).1 :=
  sixFourExternalPoint_mem_externalBase
    (twelveGridJOneFourSupport_isSaturatedSixFour hcard H) a r

theorem twelveGridJOneGridPoint_mem_row
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (hcard : Fintype.card Point = 12)
    (H : TwelveGridJOneInvertedLineCensus cfg p) (r s : Fin 3) :
    twelveGridJOneGridPoint hcard H r s ∈
      lineSupport (pivotInversion cfg p)
        (twelveGridJOnePencilLine hcard H 0 r).1 :=
  sixFourGridPoint_mem_row
    (twelveGridJOneFourSupport_isSaturatedSixFour hcard H) r s

theorem twelveGridJOneGridPoint_mem_column
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (hcard : Fintype.card Point = 12)
    (H : TwelveGridJOneInvertedLineCensus cfg p) (r s : Fin 3) :
    twelveGridJOneGridPoint hcard H r s ∈
      lineSupport (pivotInversion cfg p)
        (twelveGridJOnePencilLine hcard H 1 s).1 :=
  sixFourGridPoint_mem_column
    (twelveGridJOneFourSupport_isSaturatedSixFour hcard H) r s

theorem twelveGridJOneGridPoint_injective
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (hcard : Fintype.card Point = 12)
    (H : TwelveGridJOneInvertedLineCensus cfg p) :
    Function.Injective (fun rs : Fin 3 × Fin 3 =>
      twelveGridJOneGridPoint hcard H rs.1 rs.2) :=
  sixFourGridPoint_injective
    (twelveGridJOneFourSupport_isSaturatedSixFour hcard H)

theorem twelveGridJOneGridPoint_degree_eq_two
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (hcard : Fintype.card Point = 12)
    (H : TwelveGridJOneInvertedLineCensus cfg p) (r s : Fin 3) :
    sixFourDegree (twelveGridJOneFourSupport H)
      (twelveGridJOneGridPoint hcard H r s) = 2 :=
  sixFourGridPoint_degree_eq_two
    (twelveGridJOneFourSupport_isSaturatedSixFour hcard H) r s

theorem twelveGridJOneGridImage_eq_degreeTwo
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (hcard : Fintype.card Point = 12)
    (H : TwelveGridJOneInvertedLineCensus cfg p) :
    (Finset.univ : Finset (Fin 3 × Fin 3)).image
        (fun rs => twelveGridJOneGridPoint hcard H rs.1 rs.2) =
      sixFourDegreeTwo (twelveGridJOneFourSupport H) :=
  sixFourGridImage_eq_degreeTwo
    (twelveGridJOneFourSupport_isSaturatedSixFour hcard H)

theorem twelveGridJOnePoint_external_or_grid
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (hcard : Fintype.card Point = 12)
    (H : TwelveGridJOneInvertedLineCensus cfg p) (q : AwayFrom p) :
    (∃ a : Fin 2, twelveGridJOneExternalPoint hcard H a = q) ∨
      (∃ r s : Fin 3, twelveGridJOneGridPoint hcard H r s = q) := by
  rcases sixFour_degree_eq_two_or_three
      (twelveGridJOneFourSupport_isSaturatedSixFour hcard H) q with htwo | hthree
  · right
    have hmem : q ∈ sixFourDegreeTwo (twelveGridJOneFourSupport H) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, htwo⟩
    rw [← twelveGridJOneGridImage_eq_degreeTwo hcard H] at hmem
    obtain ⟨⟨r, s⟩, _hrs, hq⟩ := Finset.mem_image.mp hmem
    exact ⟨r, s, hq⟩
  · left
    exact (sixFour_degree_eq_three_iff_external
      (twelveGridJOneFourSupport_isSaturatedSixFour hcard H) q).mp hthree

theorem twelveGridJOnePencilIndex_injective
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (hcard : Fintype.card Point = 12)
    (H : TwelveGridJOneInvertedLineCensus cfg p) (a : Fin 2) :
    Function.Injective (twelveGridJOnePencilIndex hcard H a) :=
  sixFourExternalBase_injective
    (twelveGridJOneFourSupport_isSaturatedSixFour hcard H) a

theorem twelveGridJOnePencilIndex_zero_ne_one
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (hcard : Fintype.card Point = 12)
    (H : TwelveGridJOneInvertedLineCensus cfg p) (r s : Fin 3) :
    twelveGridJOnePencilIndex hcard H 0 r ≠
      twelveGridJOnePencilIndex hcard H 1 s :=
  sixFourExternalBase_zero_ne_one
    (twelveGridJOneFourSupport_isSaturatedSixFour hcard H) r s

theorem twelveGridJOneExternalPoint_zero_ne_one
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (hcard : Fintype.card Point = 12)
    (H : TwelveGridJOneInvertedLineCensus cfg p) :
    twelveGridJOneExternalPoint hcard H 0 ≠
      twelveGridJOneExternalPoint hcard H 1 := by
  intro h
  have h01 : (0 : Fin 2) = 1 :=
    twelveGridJOneExternalPoint_injective hcard H h
  omega

theorem twelveGridJOneExternalPoint_ne_gridPoint
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (hcard : Fintype.card Point = 12)
    (H : TwelveGridJOneInvertedLineCensus cfg p)
    (a : Fin 2) (r s : Fin 3) :
    twelveGridJOneExternalPoint hcard H a ≠
      twelveGridJOneGridPoint hcard H r s := by
  intro h
  have ha := twelveGridJOneExternalPoint_degree_eq_three hcard H a
  have hrs := twelveGridJOneGridPoint_degree_eq_two hcard H r s
  rw [h] at ha
  omega

/-- A three-line and a reconstructed four-line cannot share two selected
labels. -/
theorem twelveGridJOneThreeLine_support_inter_pencil_lt_two
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (hcard : Fintype.card Point = 12)
    (H : TwelveGridJOneInvertedLineCensus cfg p)
    (L : DeterminedLineOfSize (pivotInversion cfg p) 3)
    (a : Fin 2) (r : Fin 3) :
    (lineSupport (pivotInversion cfg p) L.1 ∩
      lineSupport (pivotInversion cfg p)
        (twelveGridJOnePencilLine hcard H a r).1).card < 2 := by
  let Q := pivotInversion cfg p
  have hlineNe : L.1 ≠ (twelveGridJOnePencilLine hcard H a r).1 := by
    intro h
    have hthree := L.2
    rw [h, (twelveGridJOnePencilLine hcard H a r).2] at hthree
    omega
  let bi : GeometricBlock Q := Sum.inl L.1
  let bj : GeometricBlock Q :=
    Sum.inl (twelveGridJOnePencilLine hcard H a r).1
  let Li : (blockSystem Q).LineBlock := ⟨bi, rfl⟩
  let Lj : (blockSystem Q).LineBlock := ⟨bj, rfl⟩
  have hLiNe : Li ≠ Lj := by
    intro h
    apply hlineNe
    simpa [Li, Lj, bi, bj] using h
  have hinter := (blockSystem Q).distinct_line_inter_card_lt_two hLiNe
  simpa [Q, Li, Lj, bi, bj, geometricBlockSupport] using hinter

/-- An external centre and one grid crossing cannot occur together on a
three-line, because their unique pencil line would then share two labels
with that three-line. -/
theorem twelveGridJOneThreeLine_external_grid_forbidden
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (hcard : Fintype.card Point = 12)
    (H : TwelveGridJOneInvertedLineCensus cfg p)
    (L : DeterminedLineOfSize (pivotInversion cfg p) 3)
    (a : Fin 2) (r s : Fin 3)
    (hext : twelveGridJOneExternalPoint hcard H a ∈
      lineSupport (pivotInversion cfg p) L.1)
    (hgrid : twelveGridJOneGridPoint hcard H r s ∈
      lineSupport (pivotInversion cfg p) L.1) : False := by
  have hne := twelveGridJOneExternalPoint_ne_gridPoint hcard H a r s
  fin_cases a
  · have hsub : ({twelveGridJOneExternalPoint hcard H 0,
        twelveGridJOneGridPoint hcard H r s} : Finset (AwayFrom p)) ⊆
        lineSupport (pivotInversion cfg p) L.1 ∩
          lineSupport (pivotInversion cfg p)
            (twelveGridJOnePencilLine hcard H 0 r).1 := by
      intro q hq
      simp only [Finset.mem_insert, Finset.mem_singleton] at hq
      rcases hq with rfl | rfl
      · exact Finset.mem_inter.mpr ⟨hext,
          twelveGridJOneExternalPoint_mem_pencilLine hcard H 0 r⟩
      · exact Finset.mem_inter.mpr ⟨hgrid,
          twelveGridJOneGridPoint_mem_row hcard H r s⟩
    have hle := Finset.card_le_card hsub
    have hpair : ({twelveGridJOneExternalPoint hcard H 0,
        twelveGridJOneGridPoint hcard H r s} : Finset (AwayFrom p)).card = 2 :=
      Finset.card_pair hne
    rw [hpair] at hle
    have hlt := twelveGridJOneThreeLine_support_inter_pencil_lt_two
      hcard H L 0 r
    omega
  · have hsub : ({twelveGridJOneExternalPoint hcard H 1,
        twelveGridJOneGridPoint hcard H r s} : Finset (AwayFrom p)) ⊆
        lineSupport (pivotInversion cfg p) L.1 ∩
          lineSupport (pivotInversion cfg p)
            (twelveGridJOnePencilLine hcard H 1 s).1 := by
      intro q hq
      simp only [Finset.mem_insert, Finset.mem_singleton] at hq
      rcases hq with rfl | rfl
      · exact Finset.mem_inter.mpr ⟨hext,
          twelveGridJOneExternalPoint_mem_pencilLine hcard H 1 s⟩
      · exact Finset.mem_inter.mpr ⟨hgrid,
          twelveGridJOneGridPoint_mem_column hcard H r s⟩
    have hle := Finset.card_le_card hsub
    have hpair : ({twelveGridJOneExternalPoint hcard H 1,
        twelveGridJOneGridPoint hcard H r s} : Finset (AwayFrom p)).card = 2 :=
      Finset.card_pair hne
    rw [hpair] at hle
    have hlt := twelveGridJOneThreeLine_support_inter_pencil_lt_two
      hcard H L 1 s
    omega

/-- No three-line in the equality census contains either reconstructed
pencil centre. -/
theorem twelveGridJOneThreeLine_external_not_mem
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (hcard : Fintype.card Point = 12)
    (H : TwelveGridJOneInvertedLineCensus cfg p)
    (L : DeterminedLineOfSize (pivotInversion cfg p) 3)
    (a : Fin 2) :
    twelveGridJOneExternalPoint hcard H a ∉
      lineSupport (pivotInversion cfg p) L.1 := by
  intro hext
  have hextNe := twelveGridJOneExternalPoint_zero_ne_one hcard H
  have hnotSubset : ¬ lineSupport (pivotInversion cfg p) L.1 ⊆
      ({twelveGridJOneExternalPoint hcard H 0,
        twelveGridJOneExternalPoint hcard H 1} : Finset (AwayFrom p)) := by
    intro hsub
    have hle := Finset.card_le_card hsub
    have hpair : ({twelveGridJOneExternalPoint hcard H 0,
        twelveGridJOneExternalPoint hcard H 1} : Finset (AwayFrom p)).card = 2 := by
      simp [hextNe]
    rw [L.2, hpair] at hle
    omega
  obtain ⟨q, hq, hqnot⟩ := Finset.not_subset.mp hnotSubset
  rcases twelveGridJOnePoint_external_or_grid hcard H q with hqext | hqgrid
  · obtain ⟨b, hb⟩ := hqext
    apply hqnot
    rw [← hb]
    fin_cases b <;> simp
  · obtain ⟨r, s, hgrid⟩ := hqgrid
    have hgridMem : twelveGridJOneGridPoint hcard H r s ∈
        lineSupport (pivotInversion cfg p) L.1 := by
      rw [hgrid]
      exact hq
    exact twelveGridJOneThreeLine_external_grid_forbidden hcard H L a r s
      hext hgridMem

/-- Every point of every actual three-line has an explicit grid label. -/
theorem twelveGridJOneThreeLine_point_is_grid
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (hcard : Fintype.card Point = 12)
    (H : TwelveGridJOneInvertedLineCensus cfg p)
    (L : DeterminedLineOfSize (pivotInversion cfg p) 3)
    {q : AwayFrom p}
    (hq : q ∈ lineSupport (pivotInversion cfg p) L.1) :
    ∃ r s : Fin 3, twelveGridJOneGridPoint hcard H r s = q := by
  rcases twelveGridJOnePoint_external_or_grid hcard H q with hqext | hqgrid
  · obtain ⟨a, ha⟩ := hqext
    have hmem : twelveGridJOneExternalPoint hcard H a ∈
        lineSupport (pivotInversion cfg p) L.1 := by
      rw [ha]
      exact hq
    exact False.elim
      (twelveGridJOneThreeLine_external_not_mem hcard H L a hmem)
  · exact hqgrid

/-- A lossless actual transversal in the `j = 1` equality census.  The
three-line has only grid labels and it meets each reconstructed row and
column in at most one label. -/
structure TwelveGridJOneActualGridTransversal
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (hcard : Fintype.card Point = 12)
    (H : TwelveGridJOneInvertedLineCensus cfg p) : Type u where
  line : DeterminedLineOfSize (pivotInversion cfg p) 3
  point_is_grid : ∀ q, q ∈ lineSupport (pivotInversion cfg p) line.1 →
    ∃ r s : Fin 3, twelveGridJOneGridPoint hcard H r s = q
  row_inter_card_le_one : ∀ r : Fin 3,
    (lineSupport (pivotInversion cfg p) line.1 ∩
      lineSupport (pivotInversion cfg p)
        (twelveGridJOnePencilLine hcard H 0 r).1).card ≤ 1
  column_inter_card_le_one : ∀ s : Fin 3,
    (lineSupport (pivotInversion cfg p) line.1 ∩
      lineSupport (pivotInversion cfg p)
        (twelveGridJOnePencilLine hcard H 1 s).1).card ≤ 1

/-- Each of the three equality-case three-lines is an actual transversal of
the reconstructed `3 × 3` grid. -/
noncomputable def twelveGridJOneThreeLineTransversal
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (hcard : Fintype.card Point = 12)
    (H : TwelveGridJOneInvertedLineCensus cfg p) (i : Fin 3) :
    TwelveGridJOneActualGridTransversal hcard H where
  line := H.threeLine i
  point_is_grid := by
    intro q hq
    exact twelveGridJOneThreeLine_point_is_grid hcard H (H.threeLine i) hq
  row_inter_card_le_one := by
    intro r
    have hlt := twelveGridJOneThreeLine_support_inter_pencil_lt_two
      hcard H (H.threeLine i) 0 r
    omega
  column_inter_card_le_one := by
    intro s
    have hlt := twelveGridJOneThreeLine_support_inter_pencil_lt_two
      hcard H (H.threeLine i) 1 s
    omega

/-- The three displayed `j = 1` transversals are pairwise distinct actual
lines; their distinctness comes directly from the line-count census. -/
theorem twelveGridJOneThreeLineTransversal_line_injective
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (hcard : Fintype.card Point = 12)
    (H : TwelveGridJOneInvertedLineCensus cfg p) :
    Function.Injective (fun i : Fin 3 =>
      (twelveGridJOneThreeLineTransversal hcard H i).line) := by
  simpa [twelveGridJOneThreeLineTransversal] using H.threeLine.injective

/-- Distinct equality-case three-lines cannot share two grid labels. -/
theorem twelveGridJOneThreeLine_support_inter_lt_two
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (H : TwelveGridJOneInvertedLineCensus cfg p)
    {i j : Fin 3} (hij : i ≠ j) :
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

/-- The complete non-normalized entrance supplied by the equality census:
two actual pencils, their nine actual crossings, and three distinct actual
transversals.  This contains no projective coordinate choice. -/
structure TwelveGridJOneThreeTransversalEntrance
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (hcard : Fintype.card Point = 12)
    (H : TwelveGridJOneInvertedLineCensus cfg p) : Type u where
  transversal : Fin 3 → TwelveGridJOneActualGridTransversal hcard H
  line_eq : ∀ i, (transversal i).line = H.threeLine i
  line_injective : Function.Injective (fun i => (transversal i).line)

/-- The equality census unconditionally supplies the full three-transversal
entrance. -/
noncomputable def twelveGridJOneThreeTransversalEntrance_of_census
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (hcard : Fintype.card Point = 12)
    (H : TwelveGridJOneInvertedLineCensus cfg p) :
    TwelveGridJOneThreeTransversalEntrance hcard H where
  transversal := twelveGridJOneThreeLineTransversal hcard H
  line_eq := by intro i; rfl
  line_injective := twelveGridJOneThreeLineTransversal_line_injective hcard H

/-! ## Projective exit -/

/-- The exact remaining projective entrance.  Its `census` component is
already constructed above; `normal` is precisely the unformalized theorem
that the equality census has the real `3 x 3` grid normalization and three
external transversals. -/
structure TwelveGridJOneNormalEntrance
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    (cfg : Configuration Point) (p : Point) : Type u where
  census : TwelveGridJOneInvertedLineCensus cfg p
  normal : TwelveGridNormalTransfer cfg p

/-- Any supplied projective entrance contradicts the checked real affine
grid calculation. -/
theorem TwelveGridJOneNormalEntrance.impossible
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (H : TwelveGridJOneNormalEntrance cfg p) : False :=
  H.normal.impossible

/-- The exact adapter needed to replace the `jOneFiveDegreeCap` field once
the projective grid entrance is constructed. -/
theorem twelveGridJOne_five_degree_cap_of_normal_entrance
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    (cfg : Configuration Point) (hadm : Admissible cfg)
    (hcard : Fintype.card Point = 12)
    (hcap : BlockSizeCap (blockSystem cfg) 5)
    (normalEntrance : forall p : Point,
      (blockSystem cfg).blockDegree 3 p = 10 ->
      (blockSystem cfg).blockDegree 5 p = 6 ->
      TwelveGridJOneNormalEntrance cfg p)
    (p : Point) (hthree : (blockSystem cfg).blockDegree 3 p = 10) :
    (blockSystem cfg).blockDegree 5 p <= 5 := by
  classical
  have hle := twelveGridJOne_five_degree_le_six (blockSystem cfg) hcard p
  by_contra hnot
  have hfive : (blockSystem cfg).blockDegree 5 p = 6 := by omega
  exact (normalEntrance p hthree hfive).impossible

end Erdos506.V1
