import Erdos506.V1.ElevenFiveHarmonicFiveCap
import Erdos506.V1.ElevenFive

/-!
# Singleton intersections at an eleven-point `(9,4,4)` pivot

This file records the direct complete-quadrangle consequence needed by the
`C = 40` singleton-exclusion argument.  If two size-five geometric blocks
meet at a `(9,4,4)` pivot, their two inverted four-point traces are two of the
four canonical base lines.  Those base lines meet in one selected inverted
point, so the original blocks have a second selected point in common.
-/

namespace Erdos506.V1

open Erdos506.Block
open Erdos506.Block.BlockSystem
open Erdos506.V3
open Erdos506.V4

universe u

/-- A size-five geometric block through `p`, bundled for the pivot dictionary.
Unlike `circleFivePivotBlock`, this construction is independent of the block
kind and is therefore usable in the `C = 40` singleton router. -/
def elevenFiveFivePivotBlock
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    (cfg : Configuration Point) (p : Point) (b : GeometricBlock cfg)
    (hb : b ∈ (blockSystem cfg).blocksOfSize 5)
    (hp : p ∈ geometricBlockSupport cfg b) : PivotBlock cfg p :=
  ⟨b, hp, by
    have hsize := (blockSystem cfg).mem_blocksOfSize.mp hb
    change (geometricBlockSupport cfg b).card = 5 at hsize
    omega⟩

/-- The inverted four-line associated with an arbitrary size-five block
through the pivot. -/
noncomputable def elevenFiveFivePivotLineOfSize
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    (cfg : Configuration Point) (p : Point) (b : GeometricBlock cfg)
    (hb : b ∈ (blockSystem cfg).blocksOfSize 5)
    (hp : p ∈ geometricBlockSupport cfg b) :
    DeterminedLineOfSize (pivotInversion cfg p) 4 :=
  ⟨blockToPivotLine cfg p (elevenFiveFivePivotBlock cfg p b hb hp), by
    rw [card_lineSupport_blockToPivotLine]
    have hsize := (blockSystem cfg).mem_blocksOfSize.mp hb
    change (geometricBlockSupport cfg b).card = 5 at hsize
    change (geometricBlockSupport cfg b).card - 1 = 4
    omega⟩

/-- The canonical base index occupied by an arbitrary size-five block through
a neutral `(9,4,4)` pivot. -/
noncomputable def elevenFive944FiveBaseIndex
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    (cfg : Configuration Point) (hcard : Fintype.card Point = 11)
    (p : Point) (hpivot : p ∈ elevenFive944Pivots (blockSystem cfg))
    (b : GeometricBlock cfg)
    (hb : b ∈ (blockSystem cfg).blocksOfSize 5)
    (hp : p ∈ geometricBlockSupport cfg b) : Fin 4 :=
  ((elevenFive944PivotFourStar cfg hcard p hpivot).sizeFourLineEquiv).symm
    (elevenFiveFivePivotLineOfSize cfg p b hb hp)

/-- At the selected index, the canonical base line is exactly the inverted
line of the original size-five block. -/
theorem elevenFive944FiveBaseIndex_line
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    (cfg : Configuration Point) (hcard : Fintype.card Point = 11)
    (p : Point) (hpivot : p ∈ elevenFive944Pivots (blockSystem cfg))
    (b : GeometricBlock cfg)
    (hb : b ∈ (blockSystem cfg).blocksOfSize 5)
    (hp : p ∈ geometricBlockSupport cfg b) :
    (elevenFive944PivotFourStar cfg hcard p hpivot).sizeFourLine
        (elevenFive944FiveBaseIndex cfg hcard p hpivot b hb hp) =
      blockToPivotLine cfg p (elevenFiveFivePivotBlock cfg p b hb hp) := by
  unfold elevenFive944FiveBaseIndex
    ElevenFivePivotInvertedFourStar.sizeFourLine
  exact congrArg Subtype.val (Equiv.apply_symm_apply _ _)

/-- The canonical base support is the original size-five support with the
pivot deleted. -/
theorem elevenFive944FiveBaseIndex_support
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    (cfg : Configuration Point) (hcard : Fintype.card Point = 11)
    (p : Point) (hpivot : p ∈ elevenFive944Pivots (blockSystem cfg))
    (b : GeometricBlock cfg)
    (hb : b ∈ (blockSystem cfg).blocksOfSize 5)
    (hp : p ∈ geometricBlockSupport cfg b) :
    (elevenFive944PivotFourStar cfg hcard p hpivot).baseSupport
        (elevenFive944FiveBaseIndex cfg hcard p hpivot b hb hp) =
      awaySupport p (geometricBlockSupport cfg b) := by
  unfold ElevenFivePivotInvertedFourStar.baseSupport
  rw [elevenFive944FiveBaseIndex_line]
  exact lineSupport_blockToPivotLine cfg p
    (elevenFiveFivePivotBlock cfg p b hb hp)

/-- Distinct size-five blocks through the pivot occupy distinct canonical
base indices. -/
theorem elevenFive944FiveBaseIndex_ne
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    (cfg : Configuration Point) (hcard : Fintype.card Point = 11)
    (p : Point) (hpivot : p ∈ elevenFive944Pivots (blockSystem cfg))
    {b c : GeometricBlock cfg}
    (hb : b ∈ (blockSystem cfg).blocksOfSize 5)
    (hc : c ∈ (blockSystem cfg).blocksOfSize 5)
    (hbp : p ∈ geometricBlockSupport cfg b)
    (hcp : p ∈ geometricBlockSupport cfg c)
    (hne : b ≠ c) :
    elevenFive944FiveBaseIndex cfg hcard p hpivot b hb hbp ≠
      elevenFive944FiveBaseIndex cfg hcard p hpivot c hc hcp := by
  intro hindex
  apply hne
  have hline :
      blockToPivotLine cfg p (elevenFiveFivePivotBlock cfg p b hb hbp) =
        blockToPivotLine cfg p (elevenFiveFivePivotBlock cfg p c hc hcp) := by
    rw [← elevenFive944FiveBaseIndex_line cfg hcard p hpivot b hb hbp,
      ← elevenFive944FiveBaseIndex_line cfg hcard p hpivot c hc hcp,
      hindex]
  have hpivotBlock := blockToPivotLine_injective cfg p hline
  exact congrArg Subtype.val hpivotBlock

/-- Removing the same pivot commutes with intersection of finite supports. -/
theorem awaySupport_inter
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    (p : Point) (A B : Finset Point) :
    awaySupport p A ∩ awaySupport p B = awaySupport p (A ∩ B) := by
  ext q
  simp only [Finset.mem_inter, mem_awaySupport]

/-- Two distinct size-five blocks through a `(9,4,4)` pivot cannot meet only
at that pivot.  This is the K3.2 branch of the `C = 40, L = 11` singleton
exclusion, proved without any additional geometric interface. -/
theorem elevenFive944_fiveBlock_inter_card_ne_one
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    (cfg : Configuration Point) (hcard : Fintype.card Point = 11)
    (p : Point) (hpivot : p ∈ elevenFive944Pivots (blockSystem cfg))
    {b c : GeometricBlock cfg}
    (hb : b ∈ (blockSystem cfg).blocksOfSize 5)
    (hc : c ∈ (blockSystem cfg).blocksOfSize 5)
    (hbp : p ∈ geometricBlockSupport cfg b)
    (hcp : p ∈ geometricBlockSupport cfg c)
    (hne : b ≠ c) :
    (geometricBlockSupport cfg b ∩ geometricBlockSupport cfg c).card ≠ 1 := by
  intro hinter
  let H := elevenFive944PivotFourStar cfg hcard p hpivot
  let i := elevenFive944FiveBaseIndex cfg hcard p hpivot b hb hbp
  let j := elevenFive944FiveBaseIndex cfg hcard p hpivot c hc hcp
  have hij : i ≠ j := by
    exact elevenFive944FiveBaseIndex_ne cfg hcard p hpivot hb hc hbp hcp hne
  have hone := H.baseSupport_inter_card_one hij
  have hpinter :
      p ∈ geometricBlockSupport cfg b ∩ geometricBlockSupport cfg c := by
    exact Finset.mem_inter.mpr ⟨hbp, hcp⟩
  have hawayZero :
      (awaySupport p
        (geometricBlockSupport cfg b ∩ geometricBlockSupport cfg c)).card = 0 := by
    rw [card_awaySupport p _ hpinter, hinter]
  have hzero :
      (awaySupport p (geometricBlockSupport cfg b) ∩
        awaySupport p (geometricBlockSupport cfg c)).card = 0 := by
    rw [awaySupport_inter, hawayZero]
  rw [elevenFive944FiveBaseIndex_support cfg hcard p hpivot b hb hbp,
    elevenFive944FiveBaseIndex_support cfg hcard p hpivot c hc hcp] at hone
  omega

/-! ## Arithmetic entrance to the remaining singleton branches -/

/-- Two distinct size-five blocks through one point force local five-degree
at least two. -/
theorem two_le_blockDegree_five_of_two_blocks
    {Point Block : Type*} [Fintype Point] [Fintype Block]
    [DecidableEq Point]
    (S : BlockSystem Point Block) (p : Point) {b c : Block}
    (hb : b ∈ S.blocksOfSize 5) (hc : c ∈ S.blocksOfSize 5)
    (hbp : p ∈ S.support b) (hcp : p ∈ S.support c) (hne : b ≠ c) :
    2 ≤ S.blockDegree 5 p := by
  classical
  have hsub : ({b, c} : Finset Block) ⊆
      (S.blocksOfSize 5).filter (fun d => p ∈ S.support d) := by
    intro d hd
    simp only [Finset.mem_insert, Finset.mem_singleton] at hd
    rcases hd with rfl | rfl
    · exact Finset.mem_filter.mpr ⟨hb, hbp⟩
    · exact Finset.mem_filter.mpr ⟨hc, hcp⟩
  have hle := Finset.card_le_card hsub
  rw [Finset.card_pair hne] at hle
  simpa [BlockSystem.blockDegree, BlockSystem.degreeIn] using hle

/-- Public C40 specialization of the three-degree spectrum. -/
theorem elevenFive_c40_threeDegree_values
    {Point Block : Type*} [Fintype Point] [Fintype Block]
    [DecidableEq Point]
    (S : BlockSystem Point Block) (p : Point)
    (hlocal : ElevenFiveLocalRows S p)
    (hC : S.totalCircleCount = 40) :
    S.blockDegree 3 p = 6 ∨ S.blockDegree 3 p = 9 ∨
      S.blockDegree 3 p = 12 := by
  have hpair := hlocal.pairRow
  have harms := hlocal.lineArmRow
  have hsplit := hlocal.threeSplit
  have hkelly := hlocal.kelly
  have hdelete := hlocal.deletion
  have hl3 : S.lineDegree 3 p ≤ 5 := by omega
  have hc3 : S.circleDegree 3 p ≤ 7 := by omega
  omega

/-- With the `L = 11` beta cap, the C40 local row has exactly the two pivot
domains displayed in the manuscript. -/
theorem elevenFive_c40_l11_pivot_domains_of_beta_cap
    {Point Block : Type*} [Fintype Point] [Fintype Block]
    [DecidableEq Point]
    (S : BlockSystem Point Block) (p : Point)
    (hlocal : ElevenFiveLocalRows S p)
    (hC : S.totalCircleCount = 40)
    (hbeta : S.blockDegree 3 p + S.blockDegree 4 p +
      S.blockDegree 5 p ≤ 18) :
    (S.blockDegree 3 p = 6 ∧
        (S.blockDegree 5 p = 1 ∨ S.blockDegree 5 p = 2 ∨
          S.blockDegree 5 p = 3)) ∨
      (S.blockDegree 3 p = 9 ∧
        (S.blockDegree 5 p = 3 ∨ S.blockDegree 5 p = 4)) := by
  have hpair := hlocal.pairRow
  have hlanger := hlocal.langer
  have hfive := hlocal.fiveDegreeCap
  rcases elevenFive_c40_threeDegree_values S p hlocal hC with h6 | h9 | h12
  · left
    constructor
    · exact h6
    · omega
  · right
    constructor
    · exact h9
    · omega
  · omega

/-- If two distinct five-blocks pass through a C40 `L = 11` pivot, only the
four profiles used by the singleton-exclusion dispatch remain. -/
theorem elevenFive_c40_l11_two_fiveBlocks_pivot_profiles
    {Point Block : Type*} [Fintype Point] [Fintype Block]
    [DecidableEq Point]
    (S : BlockSystem Point Block) (p : Point)
    (hlocal : ElevenFiveLocalRows S p)
    (hC : S.totalCircleCount = 40)
    (hbeta : S.blockDegree 3 p + S.blockDegree 4 p +
      S.blockDegree 5 p ≤ 18)
    {b c : Block}
    (hb : b ∈ S.blocksOfSize 5) (hc : c ∈ S.blocksOfSize 5)
    (hbp : p ∈ S.support b) (hcp : p ∈ S.support c) (hne : b ≠ c) :
    (S.blockDegree 3 p = 6 ∧ S.blockDegree 5 p = 2) ∨
      (S.blockDegree 3 p = 6 ∧ S.blockDegree 5 p = 3) ∨
      (S.blockDegree 3 p = 9 ∧ S.blockDegree 5 p = 3) ∨
      (S.blockDegree 3 p = 9 ∧ S.blockDegree 5 p = 4) := by
  have htwo := two_le_blockDegree_five_of_two_blocks
    S p hb hc hbp hcp hne
  rcases elevenFive_c40_l11_pivot_domains_of_beta_cap
    S p hlocal hC hbeta with ⟨h6, h5⟩ | ⟨h9, h5⟩
  · rcases h5 with h1 | h2 | h3
    · omega
    · exact Or.inl ⟨h6, h2⟩
    · exact Or.inr (Or.inl ⟨h6, h3⟩)
  · rcases h5 with h3 | h4
    · exact Or.inr (Or.inr (Or.inl ⟨h9, h3⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨h9, h4⟩))

end Erdos506.V1
