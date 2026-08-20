import Erdos506.V1.DirectKelly
import Erdos506.V1.InversionAugmentation
import Erdos506.V1.TenFiveThreePentagon

/-!
# Local real-nine bridge for the three-pentagon pivot

The checked pivot dictionary turns the exceptional ten-point pivot into a
nine-point affine configuration with six ordinary lines and ten three-lines.
What is not present in the current project is the real projective theorem
classifying those six ordinary lines as two triangles.  This module isolates
that one positive output and proves the rest of the transport.
-/

namespace Erdos506.V1

open Erdos506.Block
open Erdos506.Block.BlockSystem
open Erdos506.Incidence
open Erdos506.V3
open Erdos506.V4

universe u

/-- A positive, label-free form of the only part of the real nine-point
classification needed at the three-pentagon endpoint.  Every ordinary line
is an edge inside one of two three-sets. -/
structure NinePointOrdinaryTwoTriangleCover
    {Point : Type*} [Fintype Point] [DecidableEq Point]
    (cfg : Configuration Point) where
  triangle : Fin 2 → Finset Point
  triangle_card : ∀ i, (triangle i).card = 3
  side : DeterminedLineOfSize cfg 2 → Fin 2
  ordinary_subset : ∀ L,
    lineSupport cfg L.1 ⊆ triangle (side L)

/-- Minimal real-geometric input still absent from the current API.

The two numerical line counts already saturate all `choose(9,2)=36` pairs,
so they imply that no four labels are collinear.  `Noncollinear` rules out a
pencil and is supplied by V1 admissibility after pivot inversion. -/
structure RealPlaneNinePointOrdinaryCoverPrinciple where
  twoTriangleCover :
    ∀ {Point : Type u} [Fintype Point] [DecidableEq Point]
      (cfg : Configuration Point),
      Fintype.card Point = 9 →
      Noncollinear cfg →
      (blockSystem cfg).lineCount 2 = 6 →
      (blockSystem cfg).lineCount 3 = 10 →
      NinePointOrdinaryTwoTriangleCover cfg

/-! ## Exact pivot-size census -/

/-- Restrict the V1 pivot-block type to a fixed support size. -/
def threePentagonTaggedBlockPivotEquivAtSize
    {Point : Type*} [Fintype Point] [DecidableEq Point]
    (cfg : Configuration Point) (p : Point) (s : Nat) (hs : 3 ≤ s) :
    TaggedBlockAtSize cfg p s ≃
      {b : PivotBlock cfg p //
        (geometricBlockSupport cfg b.1).card = s} where
  toFun b :=
    ⟨⟨b.1, b.2.2, by rw [b.2.1]; exact hs⟩, b.2.1⟩
  invFun b := ⟨b.1.1, b.2, b.1.2.1⟩
  left_inv b := by ext; rfl
  right_inv b := by ext; rfl

/-- Fixed-size generalized blocks through a pivot are exactly the lines of
one-smaller size after inversion. -/
noncomputable def threePentagonPivotBlockAtSizeLineEquiv
    {Point : Type*} [Fintype Point] [DecidableEq Point]
    (cfg : Configuration Point) (p : Point) (s : Nat) (hs : 3 ≤ s) :
    TaggedBlockAtSize cfg p s ≃
      DeterminedLineOfSize (pivotInversion cfg p) (s - 1) :=
  (threePentagonTaggedBlockPivotEquivAtSize cfg p s hs).trans <|
    (blockPivotLineEquiv cfg p).subtypeEquiv fun b => by
      change (geometricBlockSupport cfg b.1).card = s ↔
        (lineSupport (pivotInversion cfg p)
          (blockToPivotLine cfg p b)).card = s - 1
      rw [card_lineSupport_blockToPivotLine]
      have hb := b.2.2
      omega

/-- Census form of the preceding fixed-size dictionary. -/
theorem threePentagon_blockDegree_eq_lineCount_pivotInversion
    {Point : Type*} [Fintype Point] [DecidableEq Point]
    (cfg : Configuration Point) (p : Point) (s : Nat) (hs : 3 ≤ s) :
    (blockSystem cfg).blockDegree s p =
      (blockSystem (pivotInversion cfg p)).lineCount (s - 1) := by
  rw [blockDegree_eq_card_taggedBlockAtSize,
    lineCount_eq_card_determinedLineOfSize]
  exact Fintype.card_congr
    (threePentagonPivotBlockAtSizeLineEquiv cfg p s hs)

/-! ## The four original three-lines -/

/-- Label the four original three-lines through the exceptional pivot. -/
noncomputable def threePentagonExceptionalThreeLines
    {Point : Type*} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point}
    (d : ThreePentagonExceptionalPivotData (blockSystem cfg)) :
    Fin 4 ≃ TaggedLineAtSize cfg d.pivot 3 := by
  have hcard : Fintype.card (TaggedLineAtSize cfg d.pivot 3) = 4 := by
    rw [← lineDegree_eq_card_taggedLineAtSize]
    exact d.three_line_degree
  exact (Fintype.equivFinOfCardEq hcard).symm

/-- Regard a labelled original three-line as a pivot block. -/
noncomputable def threePentagonExceptionalThreeLinePivotBlock
    {Point : Type*} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point}
    (d : ThreePentagonExceptionalPivotData (blockSystem cfg)) (i : Fin 4) :
    PivotBlock cfg d.pivot :=
  let b := threePentagonExceptionalThreeLines d i
  ⟨b.1, b.2.2.2, by rw [b.2.2.1]⟩

/-- Each original three-line becomes an ordinary line on the nine inverted
labels. -/
noncomputable def threePentagonExceptionalOrdinaryLine
    {Point : Type*} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point}
    (d : ThreePentagonExceptionalPivotData (blockSystem cfg)) (i : Fin 4) :
    DeterminedLineOfSize (pivotInversion cfg d.pivot) 2 := by
  let b := threePentagonExceptionalThreeLinePivotBlock d i
  refine ⟨blockToPivotLine cfg d.pivot b, ?_⟩
  rw [card_lineSupport_blockToPivotLine]
  change (geometricBlockSupport cfg
    (threePentagonExceptionalThreeLines d i).1).card - 1 = 2
  rw [(threePentagonExceptionalThreeLines d i).2.2.1]

theorem lineSupport_threePentagonExceptionalOrdinaryLine
    {Point : Type*} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point}
    (d : ThreePentagonExceptionalPivotData (blockSystem cfg)) (i : Fin 4) :
    lineSupport (pivotInversion cfg d.pivot)
        (threePentagonExceptionalOrdinaryLine d i).1 =
      awaySupport d.pivot
        (geometricBlockSupport cfg
          (threePentagonExceptionalThreeLines d i).1) := by
  change lineSupport (pivotInversion cfg d.pivot)
      (blockToPivotLine cfg d.pivot
        (threePentagonExceptionalThreeLinePivotBlock d i)) = _
  exact lineSupport_blockToPivotLine cfg d.pivot
    (threePentagonExceptionalThreeLinePivotBlock d i)

/-- Distinct original lines through the pivot become disjoint ordinary
two-sets after the pivot label is removed. -/
theorem threePentagonExceptionalOrdinaryLines_disjoint
    {Point : Type*} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point}
    (d : ThreePentagonExceptionalPivotData (blockSystem cfg))
    {i j : Fin 4} (hij : i ≠ j) :
    Disjoint
      (lineSupport (pivotInversion cfg d.pivot)
        (threePentagonExceptionalOrdinaryLine d i).1)
      (lineSupport (pivotInversion cfg d.pivot)
        (threePentagonExceptionalOrdinaryLine d j).1) := by
  classical
  rw [lineSupport_threePentagonExceptionalOrdinaryLine,
    lineSupport_threePentagonExceptionalOrdinaryLine]
  apply Finset.disjoint_left.mpr
  intro q hqi hqj
  let Bi := threePentagonExceptionalThreeLines d i
  let Bj := threePentagonExceptionalThreeLines d j
  have hBi : q.1 ∈ geometricBlockSupport cfg Bi.1 :=
    mem_awaySupport.mp hqi
  have hBj : q.1 ∈ geometricBlockSupport cfg Bj.1 :=
    mem_awaySupport.mp hqj
  have hblocks : Bi.1 ≠ Bj.1 := by
    intro h
    apply hij
    apply (threePentagonExceptionalThreeLines d).injective
    exact Subtype.ext h
  let Li : (blockSystem cfg).LineBlock := ⟨Bi.1, Bi.2.1⟩
  let Lj : (blockSystem cfg).LineBlock := ⟨Bj.1, Bj.2.1⟩
  have hlines : Li ≠ Lj := by
    intro h
    exact hblocks (congrArg Subtype.val h)
  have hinter := (blockSystem cfg).distinct_line_inter_card_lt_two hlines
  change (geometricBlockSupport cfg Bi.1 ∩
    geometricBlockSupport cfg Bj.1).card < 2 at hinter
  have hsubset : ({d.pivot, q.1} : Finset Point) ⊆
      geometricBlockSupport cfg Bi.1 ∩
        geometricBlockSupport cfg Bj.1 := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact Finset.mem_inter.mpr ⟨Bi.2.2.2, Bj.2.2.2⟩
    · exact Finset.mem_inter.mpr ⟨hBi, hBj⟩
  have hle := Finset.card_le_card hsubset
  have hpair : ({d.pivot, q.1} : Finset Point).card = 2 := by
    have hpq : d.pivot ≠ q.1 := Ne.symm q.2
    simp [hpq]
  rw [hpair] at hle
  omega

/-- The subtype inclusion of the nine inverted labels into the original ten
labels. -/
def awayFromEmbedding {Point : Type*} (p : Point) : AwayFrom p ↪ Point :=
  ⟨Subtype.val, Subtype.val_injective⟩

/-- Transport a two-triangle ordinary-line cover back to the original label
type and insert the four disjoint original three-lines. -/
noncomputable def fourMatchingAtExceptionalPivot_of_cover
    {Point : Type*} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point}
    (d : ThreePentagonExceptionalPivotData (blockSystem cfg))
    (cover : NinePointOrdinaryTwoTriangleCover
      (pivotInversion cfg d.pivot)) :
    FourMatchingInTwoTriangles Point where
  triangle i := (cover.triangle i).map (awayFromEmbedding d.pivot)
  edge i :=
    (lineSupport (pivotInversion cfg d.pivot)
      (threePentagonExceptionalOrdinaryLine d i).1).map
        (awayFromEmbedding d.pivot)
  side i := cover.side (threePentagonExceptionalOrdinaryLine d i)
  triangle_card i := by
    rw [Finset.card_map]
    exact cover.triangle_card i
  edge_card i := by
    rw [Finset.card_map]
    exact (threePentagonExceptionalOrdinaryLine d i).2
  edge_subset i :=
    (Finset.map_subset_map).2
      (cover.ordinary_subset
        (threePentagonExceptionalOrdinaryLine d i))
  edge_pairwise_disjoint i j hij :=
    (Finset.disjoint_map (awayFromEmbedding d.pivot)).mpr
      (threePentagonExceptionalOrdinaryLines_disjoint d hij)

/-- All remaining transport from the missing nine-point classification to
the already exposed local endpoint principle. -/
noncomputable def realPlaneLocalNineLink_of_ninePointOrdinaryCover
    (Nine : RealPlaneNinePointOrdinaryCoverPrinciple.{u}) :
    RealPlaneLocalNineLinkPrinciple.{u} where
  fourMatchingAtExceptionalPivot := by
    intro Point _ _ cfg hadm hcard d
    let inv := pivotInversion cfg d.pivot
    have hinvCard : Fintype.card (AwayFrom d.pivot) = 9 := by
      rw [card_awayFrom, hcard]
    have hinvNoncol : Noncollinear inv := by
      simpa [inv] using
        pivotInversion_noncollinear cfg hadm (by omega) d.pivot
    have hordinary : (blockSystem inv).lineCount 2 = 6 := by
      change (blockSystem (pivotInversion cfg d.pivot)).lineCount 2 = 6
      rw [← threePentagon_blockDegree_eq_lineCount_pivotInversion
        cfg d.pivot 3 (by omega)]
      exact d.three_degree
    have hthree : (blockSystem inv).lineCount 3 = 10 := by
      change (blockSystem (pivotInversion cfg d.pivot)).lineCount 3 = 10
      rw [← threePentagon_blockDegree_eq_lineCount_pivotInversion
        cfg d.pivot 4 (by omega)]
      exact d.four_degree
    let cover := Nine.twoTriangleCover inv hinvCard hinvNoncol
      hordinary hthree
    exact fourMatchingAtExceptionalPivot_of_cover d cover

end Erdos506.V1
