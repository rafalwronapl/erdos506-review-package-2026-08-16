import Erdos506.V1.DirectKelly
import Erdos506.V1.PivotGeometry

/-!
# Three-point lines under pivot inversion

This module exposes the small transport dictionary used by the golden-link
endpoint.  A three-point original line through the pivot becomes an ordinary
line of the pivot inversion, and distinct such lines have disjoint supports.
-/

namespace Erdos506.V1

open Erdos506.Block
open Erdos506.Block.BlockSystem
open Erdos506.Incidence
open Erdos506.V3
open Erdos506.V4

universe u

/-- Regard a three-point original line through `p` as a pivot block. -/
noncomputable def taggedThreeLinePivotBlock
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (b : TaggedLineAtSize cfg p 3) : PivotBlock cfg p :=
  ⟨b.1, b.2.2.2, by rw [b.2.2.1]⟩

/-- A three-point original line through the pivot becomes an ordinary line
of the pivot inversion. -/
noncomputable def taggedThreeLineInvertedOrdinaryLine
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (b : TaggedLineAtSize cfg p 3) :
    DeterminedLineOfSize (pivotInversion cfg p) 2 := by
  let pb := taggedThreeLinePivotBlock b
  refine ⟨blockToPivotLine cfg p pb, ?_⟩
  rw [card_lineSupport_blockToPivotLine]
  change (geometricBlockSupport cfg b.1).card - 1 = 2
  rw [b.2.2.1]

@[simp] theorem lineSupport_taggedThreeLineInvertedOrdinaryLine
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (b : TaggedLineAtSize cfg p 3) :
    lineSupport (pivotInversion cfg p)
        (taggedThreeLineInvertedOrdinaryLine b).1 =
      awaySupport p (geometricBlockSupport cfg b.1) := by
  change lineSupport (pivotInversion cfg p)
      (blockToPivotLine cfg p (taggedThreeLinePivotBlock b)) = _
  exact lineSupport_blockToPivotLine cfg p
    (taggedThreeLinePivotBlock b)

/-- Distinct original three-lines through `p` become disjoint ordinary lines
of the pivot inversion. -/
theorem taggedThreeLineInvertedOrdinaryLines_disjoint
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    {b c : TaggedLineAtSize cfg p 3} (hbc : b ≠ c) :
    Disjoint
      (lineSupport (pivotInversion cfg p)
        (taggedThreeLineInvertedOrdinaryLine b).1)
      (lineSupport (pivotInversion cfg p)
        (taggedThreeLineInvertedOrdinaryLine c).1) := by
  classical
  rw [lineSupport_taggedThreeLineInvertedOrdinaryLine,
    lineSupport_taggedThreeLineInvertedOrdinaryLine]
  apply Finset.disjoint_left.mpr
  intro q hqb hqc
  have hqb' : q.1 ∈ geometricBlockSupport cfg b.1 :=
    mem_awaySupport.mp hqb
  have hqc' : q.1 ∈ geometricBlockSupport cfg c.1 :=
    mem_awaySupport.mp hqc
  have hblocks : b.1 ≠ c.1 := by
    intro h
    exact hbc (Subtype.ext h)
  let Lb : (blockSystem cfg).LineBlock := ⟨b.1, b.2.1⟩
  let Lc : (blockSystem cfg).LineBlock := ⟨c.1, c.2.1⟩
  have hlines : Lb ≠ Lc := by
    intro h
    apply hblocks
    change Lb.1 = Lc.1
    exact congrArg
      (fun L : (blockSystem cfg).LineBlock => L.1) h
  have hinter := (blockSystem cfg).distinct_line_inter_card_lt_two hlines
  change (geometricBlockSupport cfg b.1 ∩
    geometricBlockSupport cfg c.1).card < 2 at hinter
  have hsubset : ({p, q.1} : Finset Point) ⊆
      geometricBlockSupport cfg b.1 ∩
        geometricBlockSupport cfg c.1 := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact Finset.mem_inter.mpr ⟨b.2.2.2, c.2.2.2⟩
    · exact Finset.mem_inter.mpr ⟨hqb', hqc'⟩
  have hle := Finset.card_le_card hsubset
  have hpair : ({p, q.1} : Finset Point).card = 2 := by
    simp [Ne.symm q.2]
  rw [hpair] at hle
  omega

end Erdos506.V1
