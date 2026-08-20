import Erdos506.V1.TenFiveThreePentagon
import Erdos506.V1.TenFiveThreePentagonArithmetic

/-!
# Finite exceptional pivot in the three-pentagon row

This module assembles the bounded arithmetic loss table from block-system
incidence and moment rows.  The first output stops before the four-block
degree: that coordinate needs the local pair row.  The final adapter obtains
the pair row honestly from `BlockSizeCap S 5`.

No real-nine-link statement is used here.
-/

namespace Erdos506.V1

open Erdos506.Block
open Erdos506.Block.BlockSystem
open scoped BigOperators

/-- The genuinely finite output of the loss classification, before the
local pair row is applied. -/
structure ThreePentagonExceptionalLossPivotData
    {Point Block : Type*} [Fintype Point] [Fintype Block]
    [DecidableEq Point] (S : BlockSystem Point Block) where
  pivot : Point
  three_degree : S.blockDegree 3 pivot = 6
  five_degree : S.blockDegree 5 pivot = 0
  four_line_degree : S.lineDegree 4 pivot = 0
  three_line_degree : S.lineDegree 3 pivot = 4

/-- Incidence and moment rows reduce the three-pentagon branch to the unique
exceptional local cell.  This theorem does not use a block-size cap because
it makes no assertion about `blockDegree 4`. -/
theorem finite_threePentagonExceptionalLossPivot_exists
    {Point Block : Type*} [Fintype Point] [Fintype Block]
    [DecidableEq Point]
    (S : BlockSystem Point Block)
    (hcard : Fintype.card Point = 10)
    (hB5 : S.blockCount 5 = 3)
    (hhigh : (tenHighPoints S).card = 2)
    (hL5 : S.lineCount 5 = 0)
    (hL4pos : 1 ≤ S.lineCount 4)
    (hL4cap : S.lineCount 4 ≤ 3)
    (hL34 : S.lineCount 3 + S.lineCount 4 = 10)
    (hlocal : ∀ p : Point, TenFiveLocalProfile S p) :
    ∃ p : Point,
      S.blockDegree 3 p = 6 ∧
      S.blockDegree 5 p = 0 ∧
      S.lineDegree 4 p = 0 ∧
      S.lineDegree 3 p = 4 := by
  classical
  have hd3 (p : Point) :
      S.blockDegree 3 p = 6 ∨ S.blockDegree 3 p = 9 :=
    (hlocal p).1
  have hq (p : Point) : S.lineDegree 4 p ≤ S.lineCount 4 :=
    lineDegree_le_lineCount S 4 p
  have hr (p : Point) : S.blockDegree 5 p ≤ 3 := by
    have hp := blockDegree_le_blockCount S 5 p
    rw [hB5] at hp
    exact hp
  have hl5p (p : Point) : S.lineDegree 5 p = 0 := by
    have hp := lineDegree_le_lineCount S 5 p
    omega
  have hallowed (p : Point) :
      tenLocalStateAllowed (S.blockDegree 3 p) (S.lineDegree 4 p)
        (S.blockDegree 5 p) :=
    ((hlocal p).2.2.1 (hl5p p)).1
  have hl3cap (p : Point) :
      S.lineDegree 3 p ≤
        tenLocalLine3Cap (S.blockDegree 3 p) (S.lineDegree 4 p)
          (S.blockDegree 5 p) :=
    ((hlocal p).2.2.1 (hl5p p)).2
  have hrsum : (∑ p : Point, S.blockDegree 5 p) = 15 := by
    have hinc := S.block_incidence 5
    rw [hB5] at hinc
    norm_num at hinc
    exact hinc
  have hsecond :
      (∑ p : Point, Nat.choose (S.blockDegree 5 p) 2) ≤ 6 := by
    have hm := S.second_moment_le_two_choose (S.blocksOfSize 5)
    change (∑ p : Point, Nat.choose (S.blockDegree 5 p) 2) ≤
      2 * Nat.choose (S.blockCount 5) 2 at hm
    rw [hB5] at hm
    norm_num [Nat.choose] at hm
    exact hm
  have hqsum :
      (∑ p : Point, S.lineDegree 4 p) = 4 * S.lineCount 4 :=
    S.line_incidence 4
  have hcross :
      (∑ p : Point, S.lineDegree 4 p * S.blockDegree 5 p) ≤
        6 * S.lineCount 4 := by
    have hne :
        ∀ b ∈ S.lineBlocksOfSize 4,
          ∀ c ∈ S.blocksOfSize 5, b ≠ c := by
      intro b hb c hc hbc
      subst c
      have hb4 := (S.mem_blocksOfKindSize.mp hb).2
      have hb5 := S.mem_blocksOfSize.mp hc
      omega
    have hm := sum_degreeIn_mul_degreeIn_le_two_mul
      S (S.lineBlocksOfSize 4) (S.blocksOfSize 5) hne
    change (∑ p : Point, S.lineDegree 4 p * S.blockDegree 5 p) ≤
      2 * S.lineCount 4 * S.blockCount 5 at hm
    rw [hB5] at hm
    omega
  have hl3sum :
      (∑ p : Point, S.lineDegree 3 p) =
        3 * (10 - S.lineCount 4) := by
    have hinc := S.line_incidence 3
    omega
  have hhighsum :
      (∑ p : Point,
        threePentagonHighIndicator (S.blockDegree 3 p)) = 2 := by
    calc
      (∑ p : Point,
          threePentagonHighIndicator (S.blockDegree 3 p)) =
          (tenHighPoints S).card := by
        simp [threePentagonHighIndicator, tenHighPoints]
      _ = 2 := hhigh
  exact threePentagon_exceptional_local_cell
    hcard (S.lineCount 4) hL4pos hL4cap
      (fun p => S.blockDegree 3 p)
      (fun p => S.lineDegree 4 p)
      (fun p => S.blockDegree 5 p)
      (fun p => S.lineDegree 3 p)
      hd3 hq hr hallowed hl3cap hrsum hsecond hqsum hcross hl3sum hhighsum

/-- Data-valued form of the finite loss classification. -/
noncomputable def finite_threePentagonExceptionalLossPivot
    {Point Block : Type*} [Fintype Point] [Fintype Block]
    [DecidableEq Point]
    (S : BlockSystem Point Block)
    (hcard : Fintype.card Point = 10)
    (hB5 : S.blockCount 5 = 3)
    (hhigh : (tenHighPoints S).card = 2)
    (hL5 : S.lineCount 5 = 0)
    (hL4pos : 1 ≤ S.lineCount 4)
    (hL4cap : S.lineCount 4 ≤ 3)
    (hL34 : S.lineCount 3 + S.lineCount 4 = 10)
    (hlocal : ∀ p : Point, TenFiveLocalProfile S p) :
    ThreePentagonExceptionalLossPivotData S := by
  classical
  have hex := finite_threePentagonExceptionalLossPivot_exists S hcard hB5
    hhigh hL5 hL4pos hL4cap hL34 hlocal
  let p := Classical.choose hex
  have hp := Classical.choose_spec hex
  exact
    { pivot := p
      three_degree := hp.1
      five_degree := hp.2.1
      four_line_degree := hp.2.2.1
      three_line_degree := hp.2.2.2 }

/-- The five-cap supplies exactly the missing local pair row, upgrading the
loss-table pivot to the four-coordinate endpoint datum. -/
noncomputable def ThreePentagonExceptionalLossPivotData.toExceptionalPivot
    {Point Block : Type*} [Fintype Point] [Fintype Block]
    [DecidableEq Point]
    {S : BlockSystem Point Block}
    (d : ThreePentagonExceptionalLossPivotData S)
    (hcard : Fintype.card Point = 10)
    (hcap : BlockSizeCap S 5) :
    ThreePentagonExceptionalPivotData S where
  pivot := d.pivot
  three_degree := d.three_degree
  four_degree := by
    have hpairs := (ten_local_pair_and_kappa S hcard hcap d.pivot).1
    rw [d.three_degree, d.five_degree] at hpairs
    omega
  five_degree := d.five_degree
  three_line_degree := d.three_line_degree

/-- Public finite constructor with the honest minimal currently available
source of the local pair row.  Its argument order matches the proposed
`threePentagonLink` repair: `hcap` follows `hcard`. -/
noncomputable def finite_threePentagonExceptionalPivot
    {Point Block : Type*} [Fintype Point] [Fintype Block]
    [DecidableEq Point]
    (S : BlockSystem Point Block)
    (hcard : Fintype.card Point = 10)
    (hcap : BlockSizeCap S 5)
    (hB5 : S.blockCount 5 = 3)
    (hhigh : (tenHighPoints S).card = 2)
    (hL5 : S.lineCount 5 = 0)
    (hL4pos : 1 ≤ S.lineCount 4)
    (hL4cap : S.lineCount 4 ≤ 3)
    (hL34 : S.lineCount 3 + S.lineCount 4 = 10)
    (hlocal : ∀ p : Point, TenFiveLocalProfile S p) :
    ThreePentagonExceptionalPivotData S :=
  (finite_threePentagonExceptionalLossPivot S hcard hB5 hhigh hL5
    hL4pos hL4cap hL34 hlocal).toExceptionalPivot hcard hcap

end Erdos506.V1
