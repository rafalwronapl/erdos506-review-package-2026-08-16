import Erdos506.V1.ElevenFiveC40FinalFourStarBridge
import Erdos506.V1.ElevenFiveK3DisjointFourLines

/-!
# Exact finite K3.1 dispatch for the C40 singleton carrier

The unfinished real part of K3.1 starts from a very small, completely
canonical finite object.  This file derives that object without adding any
geometric certificate: three four-lines on ten labels, with a disjoint pair,
are necessarily a path.  The C40 local pair row then identifies the only two
possible three-line counts, `7` and `6`.
-/

namespace Erdos506.V1

open Erdos506.Block
open Erdos506.Block.BlockSystem
open Erdos506.Incidence
open Erdos506.V3
open Erdos506.V4

universe u v

/-- With exactly three four-point lines, a disjoint pair has a third
four-point line.  On ten labels that third line meets both members of the
pair once.  This is the entire finite input to the real-grid tail of K3.1. -/
theorem three_four_lines_disjoint_pair_path_exists
    {Point : Type u} {Block : Type v} [Fintype Point] [Fintype Block]
    [DecidableEq Point]
    (S : BlockSystem Point Block) (hcard : Fintype.card Point = 10)
    (hfour : S.lineCount 4 = 3) (a b : LineBlock S)
    (ha : (S.support a.1).card = 4)
    (hb : (S.support b.1).card = 4)
    (hab : Disjoint (S.support a.1) (S.support b.1)) :
    ∃ c : LineBlock S, c ≠ a ∧ c ≠ b ∧
      (S.support c.1).card = 4 ∧
      (S.support c.1 ∩ S.support a.1).card = 1 ∧
      (S.support c.1 ∩ S.support b.1).card = 1 := by
  classical
  let F := S.lineBlocksOfSize 4
  have hFcard : F.card = 3 := hfour
  have haF : a.1 ∈ F := by
    exact S.mem_blocksOfKindSize.mpr ⟨a.2, ha⟩
  have hbF : b.1 ∈ F := by
    exact S.mem_blocksOfKindSize.mpr ⟨b.2, hb⟩
  have habNe : a.1 ≠ b.1 := by
    intro heq
    have hnonempty : (S.support a.1).Nonempty := by
      apply Finset.card_pos.mp
      omega
    obtain ⟨q, hq⟩ := hnonempty
    have hq' : q ∈ S.support b.1 := by simpa [heq] using hq
    exact Finset.disjoint_left.mp hab hq hq'
  have hbErase : b.1 ∈ F.erase a.1 :=
    Finset.mem_erase.mpr ⟨Ne.symm habNe, hbF⟩
  let R := (F.erase a.1).erase b.1
  have hRcard : R.card = 1 := by
    dsimp [R]
    rw [Finset.card_erase_of_mem hbErase,
      Finset.card_erase_of_mem haF, hFcard]
  have hRpos : 0 < R.card := by omega
  obtain ⟨x, hxR⟩ := Finset.card_pos.mp hRpos
  have hxEraseA : x ∈ F.erase a.1 := Finset.mem_of_mem_erase hxR
  have hxF : x ∈ F := Finset.mem_of_mem_erase hxEraseA
  have hxa : x ≠ a.1 := (Finset.mem_erase.mp hxEraseA).1
  have hxb : x ≠ b.1 := (Finset.mem_erase.mp hxR).1
  have hxspec := S.mem_blocksOfKindSize.mp hxF
  let c : LineBlock S := ⟨x, hxspec.1⟩
  have hca : c ≠ a := by
    intro h
    apply hxa
    exact congrArg Subtype.val h
  have hcb : c ≠ b := by
    intro h
    apply hxb
    exact congrArg Subtype.val h
  have hc : (S.support c.1).card = 4 := by
    change (S.support x).card = 4
    exact hxspec.2
  have hpath := disjoint_four_lines_force_path S hcard a b c
    ha hb hc hab hca hcb
  exact ⟨c, hca, hcb, hc, hpath.1, hpath.2⟩

/-- The C40 local pair row fixes the remaining three-line layer at a
degree-three singleton carrier.  The two values are exactly the K3.1 rows:
`(d₃,d₄,d₅) = (6,7,3)` and `(9,6,3)`. -/
theorem elevenFive_c40_threeFive_k31_local_rows
    {Point : Type u} {Block : Type v} [Fintype Point] [Fintype Block]
    [DecidableEq Point] (S : BlockSystem Point Block) (p : Point)
    (hlocal : ElevenFiveLocalRows S p)
    (hthree : S.blockDegree 3 p = 6 ∨ S.blockDegree 3 p = 9)
    (hfive : S.blockDegree 5 p = 3) :
    (S.blockDegree 3 p = 6 ∧ S.blockDegree 4 p = 7) ∨
      (S.blockDegree 3 p = 9 ∧ S.blockDegree 4 p = 6) := by
  have hpair := hlocal.pairRow
  rcases hthree with h6 | h9
  · left
    constructor
    · exact h6
    · omega
  · right
    constructor
    · exact h9
    · omega

/-- Inversion spells the two K3.1 rows as exact ten-point line censuses.
This is the common dispatch boundary for every C40 singleton carrier of
five-degree three. -/
theorem elevenFive_threeFive_k31_inverted_census
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    (cfg : Configuration Point) (p : Point)
    (hlocal : ElevenFiveLocalRows (blockSystem cfg) p)
    (hthree : (blockSystem cfg).blockDegree 3 p = 6 ∨
      (blockSystem cfg).blockDegree 3 p = 9)
    (hfive : (blockSystem cfg).blockDegree 5 p = 3) :
    (((blockSystem cfg).blockDegree 3 p = 6 ∧
        (blockSystem (pivotInversion cfg p)).lineCount 3 = 7) ∨
      ((blockSystem cfg).blockDegree 3 p = 9 ∧
        (blockSystem (pivotInversion cfg p)).lineCount 3 = 6)) ∧
      (blockSystem (pivotInversion cfg p)).lineCount 4 = 3 := by
  rcases elevenFive_c40_threeFive_k31_local_rows
    (blockSystem cfg) p hlocal hthree hfive with h6 | h9
  · rcases h6 with ⟨hthree', hfour⟩
    constructor
    · left
      constructor
      · exact hthree'
      · rw [← blockDegree_eq_lineCount_pivotInversion cfg p 4 (by omega)]
        exact hfour
    · rw [← blockDegree_eq_lineCount_pivotInversion cfg p 5 (by omega)]
      exact hfive
  · rcases h9 with ⟨hthree', hfour⟩
    constructor
    · right
      constructor
      · exact hthree'
      · rw [← blockDegree_eq_lineCount_pivotInversion cfg p 4 (by omega)]
        exact hfour
    · rw [← blockDegree_eq_lineCount_pivotInversion cfg p 5 (by omega)]
      exact hfive

/-- A singleton intersection of two five-blocks at a degree-three pivot
materializes the exact K3.1 finite path after inversion.  In particular this
does not merely assert that a third line exists: it returns the actual third
inverted line and its two forced one-point intersections. -/
theorem elevenFive_threeFive_singleton_inverted_path
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    (cfg : Configuration Point) (hcard : Fintype.card Point = 11)
    (p : Point) (hfive : (blockSystem cfg).blockDegree 5 p = 3)
    {b d : GeometricBlock cfg}
    (hb : b ∈ (blockSystem cfg).blocksOfSize 5)
    (hd : d ∈ (blockSystem cfg).blocksOfSize 5)
    (hbp : p ∈ geometricBlockSupport cfg b)
    (hdp : p ∈ geometricBlockSupport cfg d) (hbd : b ≠ d)
    (hinter : (geometricBlockSupport cfg b ∩
      geometricBlockSupport cfg d).card = 1) :
    ∃ e : (blockSystem (pivotInversion cfg p)).LineBlock,
      ((blockSystem (pivotInversion cfg p)).support e.1).card = 4 ∧
      e.1 ≠ Sum.inl (blockToPivotLine cfg p
        (elevenFiveFivePivotBlock cfg p b hb hbp)) ∧
      e.1 ≠ Sum.inl (blockToPivotLine cfg p
        (elevenFiveFivePivotBlock cfg p d hd hdp)) ∧
      ((blockSystem (pivotInversion cfg p)).support e.1 ∩
        lineSupport (pivotInversion cfg p)
          (blockToPivotLine cfg p
            (elevenFiveFivePivotBlock cfg p b hb hbp))).card = 1 ∧
      ((blockSystem (pivotInversion cfg p)).support e.1 ∩
        lineSupport (pivotInversion cfg p)
          (blockToPivotLine cfg p
            (elevenFiveFivePivotBlock cfg p d hd hdp))).card = 1 := by
  let Q := pivotInversion cfg p
  let B := elevenFiveFivePivotBlock cfg p b hb hbp
  let D := elevenFiveFivePivotBlock cfg p d hd hdp
  let A := elevenFiveFivePivotLineOfSize cfg p b hb hbp
  let C := elevenFiveFivePivotLineOfSize cfg p d hd hdp
  let a : (blockSystem Q).LineBlock := ⟨.inl A.1, rfl⟩
  let d' : (blockSystem Q).LineBlock := ⟨.inl C.1, rfl⟩
  have ha : ((blockSystem Q).support a.1).card = 4 := by
    change (lineSupport Q A.1).card = 4
    exact A.2
  have hd' : ((blockSystem Q).support d'.1).card = 4 := by
    change (lineSupport Q C.1).card = 4
    exact C.2
  have hA : lineSupport Q A.1 = awaySupport p (geometricBlockSupport cfg b) := by
    change lineSupport (pivotInversion cfg p) (blockToPivotLine cfg p B) = _
    exact lineSupport_blockToPivotLine cfg p B
  have hC : lineSupport Q C.1 = awaySupport p (geometricBlockSupport cfg d) := by
    change lineSupport (pivotInversion cfg p) (blockToPivotLine cfg p D) = _
    exact lineSupport_blockToPivotLine cfg p D
  have hpinter : p ∈ geometricBlockSupport cfg b ∩ geometricBlockSupport cfg d :=
    Finset.mem_inter.mpr ⟨hbp, hdp⟩
  have hawayZero :
      (awaySupport p (geometricBlockSupport cfg b ∩
        geometricBlockSupport cfg d)).card = 0 := by
    rw [card_awaySupport p _ hpinter, hinter]
  have hzero :
      (awaySupport p (geometricBlockSupport cfg b) ∩
        awaySupport p (geometricBlockSupport cfg d)).card = 0 := by
    rw [awaySupport_inter, hawayZero]
  have hab : Disjoint ((blockSystem Q).support a.1)
      ((blockSystem Q).support d'.1) := by
    rw [Finset.disjoint_iff_inter_eq_empty]
    change lineSupport Q A.1 ∩ lineSupport Q C.1 = ∅
    rw [hA, hC]
    exact Finset.card_eq_zero.mp hzero
  have hinvcard : Fintype.card (AwayFrom p) = 10 := by
    rw [card_awayFrom, hcard]
  have hfour : (blockSystem Q).lineCount 4 = 3 := by
    change (blockSystem (pivotInversion cfg p)).lineCount 4 = 3
    rw [← blockDegree_eq_lineCount_pivotInversion cfg p 5 (by omega)]
    exact hfive
  obtain ⟨e, hea, hed, he, heaInter, hedInter⟩ :=
    three_four_lines_disjoint_pair_path_exists
      (blockSystem Q) hinvcard hfour a d' ha hd' hab
  refine ⟨e, he, ?_, ?_, ?_, ?_⟩
  · have hval : e.1 ≠ a.1 := by
      intro h
      apply hea
      exact Subtype.ext h
    simpa [a, A, B] using hval
  · have hval : e.1 ≠ d'.1 := by
      intro h
      apply hed
      exact Subtype.ext h
    simpa [d', C, D] using hval
  · change ((blockSystem Q).support e.1 ∩ lineSupport Q A.1).card = 1
    exact heaInter
  · change ((blockSystem Q).support e.1 ∩ lineSupport Q C.1).card = 1
    exact hedInter

end Erdos506.V1
