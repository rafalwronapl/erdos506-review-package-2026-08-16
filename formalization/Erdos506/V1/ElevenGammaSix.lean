import Erdos506.Block.RelativeLineCapacity
import Erdos506.Incidence.OrdinaryPrinciples
import Erdos506.Incidence.SixConicDisjointHostWeight
import Erdos506.Incidence.SixConicFourHostWeight
import Erdos506.Incidence.SixConicLineIncidenceGeometry
import Erdos506.Incidence.SixConicMeetingHostWeight
import Erdos506.Incidence.SixConicU17
import Erdos506.V1.ElevenGammaSixFront
import Erdos506.V1.ElevenGammaSixLocalizedEvenCore
import Erdos506.V1.FiniteCaps
import Erdos506.V1.PivotMelchiorSlack
import Erdos506.V1.RichBlockPencil

/-!
# The eleven-point selected-six-circle boundary certificate

This file completes the solver-free arithmetic part of the manuscript's
`n = 11`, `Gamma_6` branch.  `ElevenGammaSixFront.lean` proves the common
lower bound `C >= 39`.  The data below record the exact remaining rows at
`C = 39, 40`, together with precisely the four consequences of the reusable
six-conic-events lemma which those boundary layers use.

The three constructors of `ElevenGammaSixFiveHost` are the three possible
owners of the unique five-outsider footprint: a circle meeting `Gamma`, the
outsider five-line, and an outsider five-circle.  The equations in
`ElevenGammaSixFiveHostRows` are equations (row6), (row26), and the three
host tables printed in `02_finite_n10_n12.tex`, lines 2683--2747.

This module deliberately keeps the finite certificate separate from its
geometric producer.  In particular, `ElevenGammaSixEventBounds` is not an
endpoint callback: its fields are the reusable S3/S4 bounds `W <= 26`,
`W <= 20`, and `J <= 14`, selected by the actual host type.  The final
outsider-circle case is discharged directly from the even-arrangement
principle.
-/

namespace Erdos506.V1

open Erdos506.Block
open Erdos506.Block.BlockSystem
open Erdos506.Incidence
open Erdos506.V4

universe u

section MaterializedRelativeCensus

variable {Point : Type u} {Block : Type*}
  [Fintype Point] [Fintype Block] [DecidableEq Point]

/-- Number of labels of a block on the selected six-set. -/
def elevenGammaSixInside (S : BlockSystem Point Block)
    (D : Finset Point) (b : Block) : Nat :=
  (S.support b ∩ D).card

/-- Number of labels of a block outside the selected six-set. -/
def elevenGammaSixOutside (S : BlockSystem Point Block)
    (D : Finset Point) (b : Block) : Nat :=
  (S.support b \ D).card

theorem elevenGammaSixInside_add_outside
    (S : BlockSystem Point Block) (D : Finset Point) (b : Block) :
    elevenGammaSixInside S D b + elevenGammaSixOutside S D b =
      (S.support b).card := by
  exact Finset.card_inter_add_card_sdiff (S.support b) D

/-- Every block distinct from the selected circle has selected trace at
most two, directly by triple ownership. -/
theorem elevenGammaSixInside_le_two_of_ne
    (S : BlockSystem Point Block) (D : Finset Point) (gamma b : Block)
    (hgammaSupport : S.support gamma = D) (hbgamma : b ≠ gamma) :
    elevenGammaSixInside S D b <= 2 := by
  have hinter := S.distinct_block_inter_card_lt_three hbgamma
  rw [hgammaSupport] at hinter
  exact Nat.le_of_lt_succ hinter

/-- At an eleven--six split every outside trace has size at most five. -/
theorem elevenGammaSixOutside_le_five
    (S : BlockSystem Point Block) (D : Finset Point)
    (hpoint : Fintype.card Point = 11) (hD : D.card = 6)
    (b : Block) : elevenGammaSixOutside S D b <= 5 := by
  have hsub : S.support b \ D ⊆ Finset.univ \ D := by
    intro p hp
    exact Finset.mem_sdiff.mpr
      ⟨Finset.mem_univ p, (Finset.mem_sdiff.mp hp).2⟩
  have hle := Finset.card_le_card hsub
  have hcard : (Finset.univ \ D).card = 5 := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ D),
      Finset.card_univ, hpoint, hD]
  simpa [elevenGammaSixOutside, hcard] using hle

/-- Blocks of one tag and one relative type `(g,x)`. -/
def elevenGammaSixRelativeBlocks
    (S : BlockSystem Point Block) (D : Finset Point)
    (kind : BlockKind) (g x : Nat) : Finset Block :=
  Finset.univ.filter fun b =>
    S.kind b = kind /\
      elevenGammaSixInside S D b = g /\
      elevenGammaSixOutside S D b = x

/-- The materialized relative count `c_gx` or `l_gx`. -/
def elevenGammaSixRelativeCount
    (S : BlockSystem Point Block) (D : Finset Point)
    (kind : BlockKind) (g x : Nat) : Nat :=
  (elevenGammaSixRelativeBlocks S D kind g x).card

/-- Number of blocks with an outsider footprint of size `x`, independent
of their tag and selected trace size. -/
def elevenGammaSixFootprintCount
    (S : BlockSystem Point Block) (D : Finset Point) (x : Nat) : Nat :=
  (Finset.univ.filter fun b => elevenGammaSixOutside S D b = x).card

/-- Summing a constant over one relative fibre evaluates to its materialized
relative count. -/
theorem elevenGammaSix_sum_relative_indicator
    (S : BlockSystem Point Block) (D : Finset Point)
    (kind : BlockKind) (g x a : Nat) :
    (∑ b : Block,
      if S.kind b = kind /\
          elevenGammaSixInside S D b = g /\
          elevenGammaSixOutside S D b = x then a else 0) =
      a * elevenGammaSixRelativeCount S D kind g x := by
  classical
  rw [elevenGammaSixRelativeCount, elevenGammaSixRelativeBlocks,
    ← Finset.sum_filter]
  simp [Nat.mul_comm]

theorem elevenGammaSix_sum_footprint_indicator
    (S : BlockSystem Point Block) (D : Finset Point) (x a : Nat) :
    (∑ b : Block,
      if elevenGammaSixOutside S D b = x then a else 0) =
      a * elevenGammaSixFootprintCount S D x := by
  classical
  rw [elevenGammaSixFootprintCount, ← Finset.sum_filter]
  simp [Nat.mul_comm]

/-- Replace a sum over line-tagged blocks by its ambient indicator sum. -/
theorem elevenGammaSix_sum_if_line
    (S : BlockSystem Point Block) (f : Block -> Nat) :
    (∑ b : Block, if S.kind b = .line then f b else 0) =
      ∑ b : LineBlock S, f b.1 := by
  classical
  calc
    (∑ b : Block, if S.kind b = .line then f b else 0) =
        ∑ b ∈ S.blocksOfKind .line, f b := by
      simp [BlockSystem.blocksOfKind, Finset.sum_filter]
    _ = ∑ b : LineBlock S, f b.1 := by
      simpa [BlockSystem.blocksOfKind] using
        (Finset.sum_subtype (S.blocksOfKind .line)
          (fun b => by simp [BlockSystem.blocksOfKind]) f)

/-- The outsider-triple ownership row, expressed through the three
materialized footprint counts. -/
theorem elevenGammaSix_footprint_row_of_blockSystem
    (S : BlockSystem Point Block) (D : Finset Point)
    (hpoint : Fintype.card Point = 11) (hD : D.card = 6) :
    elevenGammaSixFootprintCount S D 3 +
      4 * elevenGammaSixFootprintCount S D 4 +
      10 * elevenGammaSixFootprintCount S D 5 = 10 := by
  have hrow := S.relative_triple_partition D 0 (by omega)
  rw [hpoint, hD] at hrow
  norm_num [elevenGammaSixInside, elevenGammaSixOutside, Nat.choose]
    at hrow
  have hpointwise (b : Block) :
      Nat.choose (elevenGammaSixOutside S D b) 3 =
        (if elevenGammaSixOutside S D b = 3 then 1 else 0) +
        (if elevenGammaSixOutside S D b = 4 then 4 else 0) +
        (if elevenGammaSixOutside S D b = 5 then 10 else 0) := by
    have hx := elevenGammaSixOutside_le_five S D hpoint hD b
    interval_cases elevenGammaSixOutside S D b <;>
      norm_num [Nat.choose] at *
  have hsum :
      (∑ b : Block, Nat.choose (elevenGammaSixOutside S D b) 3) =
        elevenGammaSixFootprintCount S D 3 +
          4 * elevenGammaSixFootprintCount S D 4 +
          10 * elevenGammaSixFootprintCount S D 5 := by
    simp_rw [hpointwise]
    simp only [Finset.sum_add_distrib]
    rw [elevenGammaSix_sum_footprint_indicator,
      elevenGammaSix_sum_footprint_indicator,
      elevenGammaSix_sum_footprint_indicator]
    omega
  calc
    elevenGammaSixFootprintCount S D 3 +
          4 * elevenGammaSixFootprintCount S D 4 +
          10 * elevenGammaSixFootprintCount S D 5 =
        ∑ b : Block, Nat.choose (elevenGammaSixOutside S D b) 3 :=
      hsum.symm
    _ = 10 := hrow

/-- Two distinct blocks cannot both have four (or five) outsiders on a
five-set: their outsider traces would share at least three labels. -/
theorem elevenGammaSix_footprintCount_le_one
    (S : BlockSystem Point Block) (D : Finset Point)
    (hpoint : Fintype.card Point = 11) (hD : D.card = 6)
    (x : Nat) (hfour : 4 <= x) :
    elevenGammaSixFootprintCount S D x <= 1 := by
  classical
  rw [elevenGammaSixFootprintCount, Finset.card_le_one]
  intro b hb c hc
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb hc
  by_contra hbc
  let X : Finset Point := Finset.univ \ D
  let B : Finset Point := S.support b \ D
  let Cc : Finset Point := S.support c \ D
  have hXcard : X.card = 5 := by
    simp [X, Finset.card_sdiff_of_subset (Finset.subset_univ D),
      hpoint, hD]
  have hBX : B ⊆ X := by
    intro p hp
    exact Finset.mem_sdiff.mpr
      ⟨Finset.mem_univ p, (Finset.mem_sdiff.mp hp).2⟩
  have hCX : Cc ⊆ X := by
    intro p hp
    exact Finset.mem_sdiff.mpr
      ⟨Finset.mem_univ p, (Finset.mem_sdiff.mp hp).2⟩
  have hUnion : (B ∪ Cc).card <= 5 := by
    have hsub : B ∪ Cc ⊆ X := Finset.union_subset hBX hCX
    exact (Finset.card_le_card hsub).trans_eq hXcard
  have hcount := Finset.card_union_add_card_inter B Cc
  have hBcard : B.card = x := by simpa [B, elevenGammaSixOutside] using hb
  have hCcard : Cc.card = x := by simpa [Cc, elevenGammaSixOutside] using hc
  have hinterOutside : 3 <= (B ∩ Cc).card := by omega
  have hsubInter : B ∩ Cc ⊆ S.support b ∩ S.support c := by
    intro p hp
    exact Finset.mem_inter.mpr
      ⟨(Finset.mem_sdiff.mp (Finset.mem_inter.mp hp).1).1,
        (Finset.mem_sdiff.mp (Finset.mem_inter.mp hp).2).1⟩
  have hinterSupport := Finset.card_le_card hsubInter
  have hlt := S.distinct_block_inter_card_lt_three hbc
  omega

/-- Nontrivial mixed selected--outsider line-pair capacity already used. -/
def elevenGammaSixLineCapacityUsed
    (S : BlockSystem Point Block) (D : Finset Point) : Nat :=
  2 * elevenGammaSixRelativeCount S D .line 1 2 +
  3 * elevenGammaSixRelativeCount S D .line 1 3 +
  4 * elevenGammaSixRelativeCount S D .line 1 4 +
  5 * elevenGammaSixRelativeCount S D .line 1 5 +
  2 * elevenGammaSixRelativeCount S D .line 2 1 +
  4 * elevenGammaSixRelativeCount S D .line 2 2 +
  6 * elevenGammaSixRelativeCount S D .line 2 3 +
  8 * elevenGammaSixRelativeCount S D .line 2 4

/-- The displayed `sigma6` expression is exactly the nontrivial part of
the mixed line-pair partition. -/
theorem elevenGammaSixLineCapacityUsed_eq_sum
    (S : BlockSystem Point Block) (D : Finset Point) (gamma : Block)
    (hpoint : Fintype.card Point = 11) (hD : D.card = 6)
    (hgammaKind : S.kind gamma = .circle)
    (hgammaSupport : S.support gamma = D)
    (hlineCap : forall b, S.kind b = .line -> (S.support b).card <= 6) :
    elevenGammaSixLineCapacityUsed S D =
      ∑ b : LineBlock S,
        if 3 <= (S.support b.1).card then
          elevenGammaSixInside S D b.1 * elevenGammaSixOutside S D b.1
        else 0 := by
  classical
  have hpointwise (b : Block) :
      (if S.kind b = .line then
          (if 3 <= (S.support b).card then
            elevenGammaSixInside S D b * elevenGammaSixOutside S D b
          else 0)
        else 0) =
      (if S.kind b = .line /\
          elevenGammaSixInside S D b = 1 /\
          elevenGammaSixOutside S D b = 2 then 2 else 0) +
      (if S.kind b = .line /\
          elevenGammaSixInside S D b = 1 /\
          elevenGammaSixOutside S D b = 3 then 3 else 0) +
      (if S.kind b = .line /\
          elevenGammaSixInside S D b = 1 /\
          elevenGammaSixOutside S D b = 4 then 4 else 0) +
      (if S.kind b = .line /\
          elevenGammaSixInside S D b = 1 /\
          elevenGammaSixOutside S D b = 5 then 5 else 0) +
      (if S.kind b = .line /\
          elevenGammaSixInside S D b = 2 /\
          elevenGammaSixOutside S D b = 1 then 2 else 0) +
      (if S.kind b = .line /\
          elevenGammaSixInside S D b = 2 /\
          elevenGammaSixOutside S D b = 2 then 4 else 0) +
      (if S.kind b = .line /\
          elevenGammaSixInside S D b = 2 /\
          elevenGammaSixOutside S D b = 3 then 6 else 0) +
      (if S.kind b = .line /\
          elevenGammaSixInside S D b = 2 /\
          elevenGammaSixOutside S D b = 4 then 8 else 0) := by
    cases hkind : S.kind b with
    | circle => simp
    | line =>
        have hne : b ≠ gamma := by
          intro h
          subst b
          cases hgammaKind.symm.trans hkind
        have hi := elevenGammaSixInside_le_two_of_ne
          S D gamma b hgammaSupport hne
        have hx := elevenGammaSixOutside_le_five S D hpoint hD b
        have hsum := elevenGammaSixInside_add_outside S D b
        have hmin := S.line_min b hkind
        have hcap := hlineCap b hkind
        rw [← hsum] at hmin hcap
        rw [← hsum]
        interval_cases elevenGammaSixInside S D b <;>
          interval_cases elevenGammaSixOutside S D b <;>
          norm_num [hkind] at *
  rw [← elevenGammaSix_sum_if_line S (fun b =>
    if 3 <= (S.support b).card then
      elevenGammaSixInside S D b * elevenGammaSixOutside S D b
    else 0)]
  simp_rw [hpointwise]
  simp only [Finset.sum_add_distrib]
  rw [elevenGammaSix_sum_relative_indicator,
    elevenGammaSix_sum_relative_indicator,
    elevenGammaSix_sum_relative_indicator,
    elevenGammaSix_sum_relative_indicator,
    elevenGammaSix_sum_relative_indicator,
    elevenGammaSix_sum_relative_indicator,
    elevenGammaSix_sum_relative_indicator,
    elevenGammaSix_sum_relative_indicator]
  simp [elevenGammaSixLineCapacityUsed]

/-- The nontrivial mixed line contribution is at most the exact total of
the `6 * 5 = 30` selected--outsider line pairs. -/
theorem elevenGammaSixLineCapacityUsed_le_thirty
    (S : BlockSystem Point Block) (D : Finset Point) (gamma : Block)
    (hpoint : Fintype.card Point = 11) (hD : D.card = 6)
    (hgammaKind : S.kind gamma = .circle)
    (hgammaSupport : S.support gamma = D)
    (hlineCap : forall b, S.kind b = .line -> (S.support b).card <= 6) :
    elevenGammaSixLineCapacityUsed S D <= 30 := by
  rw [elevenGammaSixLineCapacityUsed_eq_sum S D gamma hpoint hD
    hgammaKind hgammaSupport hlineCap]
  have hpartition := S.relative_line_pair_partition D 1 (by omega)
  rw [hpoint, hD] at hpartition
  norm_num [elevenGammaSixInside, elevenGammaSixOutside, Nat.choose]
    at hpartition
  calc
    (∑ b : LineBlock S,
      if 3 <= (S.support b.1).card then
        elevenGammaSixInside S D b.1 * elevenGammaSixOutside S D b.1
      else 0) <=
        ∑ b : LineBlock S,
          elevenGammaSixInside S D b.1 *
            elevenGammaSixOutside S D b.1 := by
      apply Finset.sum_le_sum
      intro b _hb
      split <;> omega
    _ = 30 := hpartition

/-- Outsider incidence with ordinary three-circles. -/
def elevenGammaSixOrdinaryCircleIncidence
    (S : BlockSystem Point Block) (D : Finset Point) : Nat :=
  3 * elevenGammaSixRelativeCount S D .circle 0 3 +
  2 * elevenGammaSixRelativeCount S D .circle 1 2 +
  elevenGammaSixRelativeCount S D .circle 2 1

/-- The nonnegative part of the global Melchior line row at eleven points. -/
def elevenGammaSixLineMelchiorUsed
    (S : BlockSystem Point Block) (D : Finset Point) : Nat :=
  3 * elevenGammaSixRelativeCount S D .line 0 3 +
  7 * elevenGammaSixRelativeCount S D .line 0 4 +
  12 * elevenGammaSixRelativeCount S D .line 0 5 +
  3 * elevenGammaSixRelativeCount S D .line 1 2 +
  7 * elevenGammaSixRelativeCount S D .line 1 3 +
  12 * elevenGammaSixRelativeCount S D .line 1 4 +
  18 * elevenGammaSixRelativeCount S D .line 1 5 +
  3 * elevenGammaSixRelativeCount S D .line 2 1 +
  7 * elevenGammaSixRelativeCount S D .line 2 2 +
  12 * elevenGammaSixRelativeCount S D .line 2 3 +
  18 * elevenGammaSixRelativeCount S D .line 2 4

/-- Natural-number form of the global Melchior line row. -/
noncomputable def elevenGammaSixTotalLineMelchiorUsed
    (S : BlockSystem Point Block) : Nat :=
  ∑ b : LineBlock S,
    if 3 <= (S.support b.1).card then
      Nat.choose (S.support b.1).card 2 + (S.support b.1).card - 3
    else 0

/-- The relative Melchior expression is exactly the natural global line
row, after resolving every line by its selected and outsider trace sizes. -/
theorem elevenGammaSixLineMelchiorUsed_eq_total
    (S : BlockSystem Point Block) (D : Finset Point) (gamma : Block)
    (hpoint : Fintype.card Point = 11) (hD : D.card = 6)
    (hgammaKind : S.kind gamma = .circle)
    (hgammaSupport : S.support gamma = D)
    (hlineCap : forall b, S.kind b = .line -> (S.support b).card <= 6) :
    elevenGammaSixLineMelchiorUsed S D =
      elevenGammaSixTotalLineMelchiorUsed S := by
  classical
  have hpointwise (b : Block) :
      (if S.kind b = .line then
          (if 3 <= (S.support b).card then
            Nat.choose (S.support b).card 2 + (S.support b).card - 3
          else 0)
        else 0) =
      (if S.kind b = .line /\ elevenGammaSixInside S D b = 0 /\
          elevenGammaSixOutside S D b = 3 then 3 else 0) +
      (if S.kind b = .line /\ elevenGammaSixInside S D b = 0 /\
          elevenGammaSixOutside S D b = 4 then 7 else 0) +
      (if S.kind b = .line /\ elevenGammaSixInside S D b = 0 /\
          elevenGammaSixOutside S D b = 5 then 12 else 0) +
      (if S.kind b = .line /\ elevenGammaSixInside S D b = 1 /\
          elevenGammaSixOutside S D b = 2 then 3 else 0) +
      (if S.kind b = .line /\ elevenGammaSixInside S D b = 1 /\
          elevenGammaSixOutside S D b = 3 then 7 else 0) +
      (if S.kind b = .line /\ elevenGammaSixInside S D b = 1 /\
          elevenGammaSixOutside S D b = 4 then 12 else 0) +
      (if S.kind b = .line /\ elevenGammaSixInside S D b = 1 /\
          elevenGammaSixOutside S D b = 5 then 18 else 0) +
      (if S.kind b = .line /\ elevenGammaSixInside S D b = 2 /\
          elevenGammaSixOutside S D b = 1 then 3 else 0) +
      (if S.kind b = .line /\ elevenGammaSixInside S D b = 2 /\
          elevenGammaSixOutside S D b = 2 then 7 else 0) +
      (if S.kind b = .line /\ elevenGammaSixInside S D b = 2 /\
          elevenGammaSixOutside S D b = 3 then 12 else 0) +
      (if S.kind b = .line /\ elevenGammaSixInside S D b = 2 /\
          elevenGammaSixOutside S D b = 4 then 18 else 0) := by
    cases hk : S.kind b with
    | circle => simp
    | line =>
        have hne : b ≠ gamma := by
          intro h
          subst b
          cases hgammaKind.symm.trans hk
        have hi := elevenGammaSixInside_le_two_of_ne
          S D gamma b hgammaSupport hne
        have hx := elevenGammaSixOutside_le_five S D hpoint hD b
        have hsum := elevenGammaSixInside_add_outside S D b
        have hmin := S.line_min b hk
        have hcap := hlineCap b hk
        rw [← hsum] at hmin hcap
        rw [← hsum]
        interval_cases elevenGammaSixInside S D b <;>
          interval_cases elevenGammaSixOutside S D b <;>
          norm_num [Nat.choose, hk] at *
  unfold elevenGammaSixTotalLineMelchiorUsed
  rw [← elevenGammaSix_sum_if_line S (fun b =>
    if 3 <= (S.support b).card then
      Nat.choose (S.support b).card 2 + (S.support b).card - 3
    else 0)]
  simp_rw [hpointwise]
  simp only [Finset.sum_add_distrib]
  rw [elevenGammaSix_sum_relative_indicator,
    elevenGammaSix_sum_relative_indicator,
    elevenGammaSix_sum_relative_indicator,
    elevenGammaSix_sum_relative_indicator,
    elevenGammaSix_sum_relative_indicator,
    elevenGammaSix_sum_relative_indicator,
    elevenGammaSix_sum_relative_indicator,
    elevenGammaSix_sum_relative_indicator,
    elevenGammaSix_sum_relative_indicator,
    elevenGammaSix_sum_relative_indicator,
    elevenGammaSix_sum_relative_indicator]
  simp [elevenGammaSixLineMelchiorUsed]

/-- Casting the natural global line row recovers the signed row used by the
Melchior interface. -/
theorem elevenGammaSixTotalLineMelchiorUsed_cast
    (S : BlockSystem Point Block) :
    (elevenGammaSixTotalLineMelchiorUsed S : Int) = S.globalLineRow := by
  classical
  unfold elevenGammaSixTotalLineMelchiorUsed BlockSystem.globalLineRow
  rw [Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro b _hb
  by_cases hthree : 3 <= (S.support b.1).card
  · simp only [hthree, if_true]
    have hle : 3 <=
        Nat.choose (S.support b.1).card 2 + (S.support b.1).card := by
      omega
    rw [Nat.cast_sub hle, Nat.cast_add]
    norm_num
  · simp [hthree]

omit [Fintype Point] in
/-- On a five-set, a family of subsets of size at least three with pairwise
intersection at most one has total weight at most two, where triples have
weight one and larger subsets have weight two. -/
theorem fiveSet_largeTrace_weight_le_two
    {I : Type*} [DecidableEq I]
    (X : Finset Point) (hX : X.card = 5)
    (F : Finset I) (trace : I -> Finset Point)
    (hsub : forall i, i ∈ F -> trace i ⊆ X)
    (hthree : forall i, i ∈ F -> 3 <= (trace i).card)
    (hinter : forall i, i ∈ F -> forall j, j ∈ F -> i ≠ j ->
      (trace i ∩ trace j).card < 2) :
    (∑ i ∈ F, if (trace i).card = 3 then 1 else 2) <= 2 := by
  classical
  by_cases hhigh : exists i, i ∈ F /\ 4 <= (trace i).card
  · obtain ⟨i, hiF, hi4⟩ := hhigh
    have hsingleton : F = {i} := by
      apply Finset.eq_singleton_iff_unique_mem.mpr
      refine ⟨hiF, ?_⟩
      intro j hjF
      by_contra hji
      have hUsub : trace i ∪ trace j ⊆ X :=
        Finset.union_subset (hsub i hiF) (hsub j hjF)
      have hUle := Finset.card_le_card hUsub
      have hcount := Finset.card_union_add_card_inter (trace i) (trace j)
      have hj3 := hthree j hjF
      have hijNe : i ≠ j := by
        intro hij
        exact hji hij.symm
      have hij := hinter i hiF j hjF hijNe
      omega
    rw [hsingleton]
    have hi3ne : (trace i).card ≠ 3 := by omega
    simp [hi3ne]
  · have hcardF : F.card <= 2 := by
      by_contra hnot
      have hthreeF : 2 < F.card := by omega
      obtain ⟨i, hiF, j, hjF, k, hkF, hij, hik, hjk⟩ :=
        Finset.two_lt_card.mp hthreeF
      have hi3 : (trace i).card = 3 := by
        have := hthree i hiF
        have hnot4 : ¬4 <= (trace i).card := by
          intro hi4
          exact hhigh ⟨i, hiF, hi4⟩
        omega
      have hj3 : (trace j).card = 3 := by
        have := hthree j hjF
        have hnot4 : ¬4 <= (trace j).card := by
          intro hj4
          exact hhigh ⟨j, hjF, hj4⟩
        omega
      have hk3 : (trace k).card = 3 := by
        have := hthree k hkF
        have hnot4 : ¬4 <= (trace k).card := by
          intro hk4
          exact hhigh ⟨k, hkF, hk4⟩
        omega
      have hUsub : trace i ∪ trace j ⊆ X :=
        Finset.union_subset (hsub i hiF) (hsub j hjF)
      have hUle := Finset.card_le_card hUsub
      have hcount := Finset.card_union_add_card_inter (trace i) (trace j)
      have hijInter := hinter i hiF j hjF hij
      have hUcard : (trace i ∪ trace j).card = 5 := by omega
      have hUeq : trace i ∪ trace j = X :=
        Finset.eq_of_subset_of_card_le hUsub (by omega)
      have hkSubUnion : trace k ⊆ trace i ∪ trace j := by
        rw [hUeq]
        exact hsub k hkF
      have hkDecomp :
          trace k = (trace k ∩ trace i) ∪ (trace k ∩ trace j) := by
        ext p
        constructor
        · intro hp
          have hpU := hkSubUnion hp
          rcases Finset.mem_union.mp hpU with hpi | hpj
          · exact Finset.mem_union.mpr (Or.inl
              (Finset.mem_inter.mpr ⟨hp, hpi⟩))
          · exact Finset.mem_union.mpr (Or.inr
              (Finset.mem_inter.mpr ⟨hp, hpj⟩))
        · intro hp
          rcases Finset.mem_union.mp hp with hpki | hpkj
          · exact (Finset.mem_inter.mp hpki).1
          · exact (Finset.mem_inter.mp hpkj).1
      have hkiInter := hinter k hkF i hiF hik.symm
      have hkjInter := hinter k hkF j hjF hjk.symm
      have hkCardLe : (trace k).card <= 2 := by
        rw [hkDecomp]
        have hunion := Finset.card_union_le
          (trace k ∩ trace i) (trace k ∩ trace j)
        omega
      omega
    calc
      (∑ i ∈ F, if (trace i).card = 3 then 1 else 2) =
          ∑ _i ∈ F, 1 := by
        apply Finset.sum_congr rfl
        intro i hiF
        have hi3 : (trace i).card = 3 := by
          have := hthree i hiF
          have hnot4 : ¬4 <= (trace i).card := by
            intro hi4
            exact hhigh ⟨i, hiF, hi4⟩
          omega
        simp [hi3]
      _ = F.card := by simp
      _ <= 2 := hcardF

/-- Weight one for a three-outsider line footprint and two for a footprint
of size four or five. -/
def elevenGammaSixLargeLineFootprintWeight
    (S : BlockSystem Point Block) (D : Finset Point) : Nat :=
  elevenGammaSixRelativeCount S D .line 0 3 +
  elevenGammaSixRelativeCount S D .line 1 3 +
  elevenGammaSixRelativeCount S D .line 2 3 +
  2 * elevenGammaSixRelativeCount S D .line 0 4 +
  2 * elevenGammaSixRelativeCount S D .line 0 5 +
  2 * elevenGammaSixRelativeCount S D .line 1 4 +
  2 * elevenGammaSixRelativeCount S D .line 1 5 +
  2 * elevenGammaSixRelativeCount S D .line 2 4

/-- Sum form of the large-line footprint weight. -/
noncomputable def elevenGammaSixTotalLargeLineFootprintWeight
    (S : BlockSystem Point Block) (D : Finset Point) : Nat :=
  ∑ b : LineBlock S,
    if elevenGammaSixOutside S D b.1 = 3 then 1
    else if 4 <= elevenGammaSixOutside S D b.1 then 2 else 0

/-- Grouping the large-line footprint sum by relative type gives the
displayed `sigma_L` expression. -/
theorem elevenGammaSixTotalLargeLineFootprintWeight_eq_weight
    (S : BlockSystem Point Block) (D : Finset Point) (gamma : Block)
    (hpoint : Fintype.card Point = 11) (hD : D.card = 6)
    (hgammaKind : S.kind gamma = .circle)
    (hgammaSupport : S.support gamma = D)
    (hlineCap : forall b, S.kind b = .line -> (S.support b).card <= 6) :
    elevenGammaSixTotalLargeLineFootprintWeight S D =
      elevenGammaSixLargeLineFootprintWeight S D := by
  classical
  have hpointwise (b : Block) :
      (if S.kind b = .line then
          (if elevenGammaSixOutside S D b = 3 then 1
          else if 4 <= elevenGammaSixOutside S D b then 2 else 0)
        else 0) =
      (if S.kind b = .line /\ elevenGammaSixInside S D b = 0 /\
          elevenGammaSixOutside S D b = 3 then 1 else 0) +
      (if S.kind b = .line /\ elevenGammaSixInside S D b = 1 /\
          elevenGammaSixOutside S D b = 3 then 1 else 0) +
      (if S.kind b = .line /\ elevenGammaSixInside S D b = 2 /\
          elevenGammaSixOutside S D b = 3 then 1 else 0) +
      (if S.kind b = .line /\ elevenGammaSixInside S D b = 0 /\
          elevenGammaSixOutside S D b = 4 then 2 else 0) +
      (if S.kind b = .line /\ elevenGammaSixInside S D b = 0 /\
          elevenGammaSixOutside S D b = 5 then 2 else 0) +
      (if S.kind b = .line /\ elevenGammaSixInside S D b = 1 /\
          elevenGammaSixOutside S D b = 4 then 2 else 0) +
      (if S.kind b = .line /\ elevenGammaSixInside S D b = 1 /\
          elevenGammaSixOutside S D b = 5 then 2 else 0) +
      (if S.kind b = .line /\ elevenGammaSixInside S D b = 2 /\
          elevenGammaSixOutside S D b = 4 then 2 else 0) := by
    cases hk : S.kind b with
    | circle => simp
    | line =>
        have hne : b ≠ gamma := by
          intro h
          subst b
          cases hgammaKind.symm.trans hk
        have hi := elevenGammaSixInside_le_two_of_ne
          S D gamma b hgammaSupport hne
        have hx := elevenGammaSixOutside_le_five S D hpoint hD b
        have hsum := elevenGammaSixInside_add_outside S D b
        have hcap := hlineCap b hk
        rw [← hsum] at hcap
        interval_cases elevenGammaSixInside S D b <;>
          interval_cases elevenGammaSixOutside S D b <;>
          norm_num [hk] at *
  unfold elevenGammaSixTotalLargeLineFootprintWeight
  rw [← elevenGammaSix_sum_if_line S (fun b =>
    if elevenGammaSixOutside S D b = 3 then 1
    else if 4 <= elevenGammaSixOutside S D b then 2 else 0)]
  simp_rw [hpointwise]
  simp only [Finset.sum_add_distrib]
  rw [elevenGammaSix_sum_relative_indicator,
    elevenGammaSix_sum_relative_indicator,
    elevenGammaSix_sum_relative_indicator,
    elevenGammaSix_sum_relative_indicator,
    elevenGammaSix_sum_relative_indicator,
    elevenGammaSix_sum_relative_indicator,
    elevenGammaSix_sum_relative_indicator,
    elevenGammaSix_sum_relative_indicator]
  simp [elevenGammaSixLargeLineFootprintWeight]

/-- The large-line footprints form a pairwise-linear family on the five
outsiders, hence their total weight is at most two. -/
theorem elevenGammaSixTotalLargeLineFootprintWeight_le_two
    (S : BlockSystem Point Block) (D : Finset Point)
    (hpoint : Fintype.card Point = 11) (hD : D.card = 6) :
    elevenGammaSixTotalLargeLineFootprintWeight S D <= 2 := by
  classical
  let X : Finset Point := Finset.univ \ D
  let F : Finset (LineBlock S) := Finset.univ.filter fun b =>
    3 <= elevenGammaSixOutside S D b.1
  let trace : LineBlock S -> Finset Point := fun b => S.support b.1 \ D
  have hX : X.card = 5 := by
    simp [X, Finset.card_sdiff_of_subset (Finset.subset_univ D),
      hpoint, hD]
  have hsub : forall b, b ∈ F -> trace b ⊆ X := by
    intro b _hb p hp
    exact Finset.mem_sdiff.mpr
      ⟨Finset.mem_univ p, (Finset.mem_sdiff.mp hp).2⟩
  have hthree : forall b, b ∈ F -> 3 <= (trace b).card := by
    intro b hb
    exact (Finset.mem_filter.mp hb).2
  have hinter : forall b, b ∈ F -> forall c, c ∈ F -> b ≠ c ->
      (trace b ∩ trace c).card < 2 := by
    intro b _hb c _hc hbc
    have hsubInter : trace b ∩ trace c ⊆
        S.support b.1 ∩ S.support c.1 := by
      intro p hp
      exact Finset.mem_inter.mpr
        ⟨(Finset.mem_sdiff.mp (Finset.mem_inter.mp hp).1).1,
          (Finset.mem_sdiff.mp (Finset.mem_inter.mp hp).2).1⟩
    have hle := Finset.card_le_card hsubInter
    have hlt := S.distinct_line_inter_card_lt_two hbc
    omega
  have hpack := fiveSet_largeTrace_weight_le_two
    X hX F trace hsub hthree hinter
  unfold elevenGammaSixTotalLargeLineFootprintWeight
  calc
    (∑ b : LineBlock S,
        if elevenGammaSixOutside S D b.1 = 3 then 1
        else if 4 <= elevenGammaSixOutside S D b.1 then 2 else 0) =
        ∑ b : LineBlock S,
          if 3 <= elevenGammaSixOutside S D b.1 then
            (if elevenGammaSixOutside S D b.1 = 3 then 1 else 2)
          else 0 := by
      apply Finset.sum_congr rfl
      intro b _hb
      by_cases hthreeB : 3 <= elevenGammaSixOutside S D b.1
      · by_cases heq : elevenGammaSixOutside S D b.1 = 3
        · simp [heq]
        · have hfour : 4 <= elevenGammaSixOutside S D b.1 := by omega
          simp [hthreeB, heq, hfour]
      · have hnotFour : ¬4 <= elevenGammaSixOutside S D b.1 := by omega
        have hneThree : elevenGammaSixOutside S D b.1 ≠ 3 := by omega
        simp [hthreeB, hnotFour, hneThree]
    _ = ∑ b ∈ F, if (trace b).card = 3 then 1 else 2 := by
      rw [← Finset.sum_filter]
      rfl
    _ <= 2 := hpack

theorem elevenGammaSixLargeLineFootprintWeight_le_two
    (S : BlockSystem Point Block) (D : Finset Point) (gamma : Block)
    (hpoint : Fintype.card Point = 11) (hD : D.card = 6)
    (hgammaKind : S.kind gamma = .circle)
    (hgammaSupport : S.support gamma = D)
    (hlineCap : forall b, S.kind b = .line -> (S.support b).card <= 6) :
    elevenGammaSixLargeLineFootprintWeight S D <= 2 := by
  rw [← elevenGammaSixTotalLargeLineFootprintWeight_eq_weight
    S D gamma hpoint hD hgammaKind hgammaSupport hlineCap]
  exact elevenGammaSixTotalLargeLineFootprintWeight_le_two S D hpoint hD

/-- The relative-count form of the outside-pair circle weight `W`. -/
def elevenGammaSixWeight
    (S : BlockSystem Point Block) (D : Finset Point) : Nat :=
  elevenGammaSixRelativeCount S D .circle 2 2 +
  3 * elevenGammaSixRelativeCount S D .circle 2 3 +
  6 * elevenGammaSixRelativeCount S D .circle 2 4

/-- The relative-count form of the original chord-line incidence `J`. -/
def elevenGammaSixLineIncidence
    (S : BlockSystem Point Block) (D : Finset Point) : Nat :=
  elevenGammaSixRelativeCount S D .line 2 1 +
  2 * elevenGammaSixRelativeCount S D .line 2 2 +
  3 * elevenGammaSixRelativeCount S D .line 2 3 +
  4 * elevenGammaSixRelativeCount S D .line 2 4

/-- Sum form of the outside-pair circle weight, before grouping by relative
type.  This is the form transported to `sixConicWeight`. -/
noncomputable def elevenGammaSixTotalWeight
    (S : BlockSystem Point Block) (D : Finset Point) : Nat :=
  ∑ b : Block,
    if S.kind b = .circle /\ elevenGammaSixInside S D b = 2 then
      Nat.choose (elevenGammaSixOutside S D b) 2
    else 0

/-- Sum form of the two-selected-point line incidence, before grouping by
relative type.  This is the form transported to `sixConicLineIncidence`. -/
noncomputable def elevenGammaSixTotalLineIncidence
    (S : BlockSystem Point Block) (D : Finset Point) : Nat :=
  ∑ b : Block,
    if S.kind b = .line /\ elevenGammaSixInside S D b = 2 then
      elevenGammaSixOutside S D b
    else 0

/-- Outsider incidences with all ordinary three-circles, before grouping by
their selected trace size. -/
noncomputable def elevenGammaSixTotalOrdinaryCircleIncidence
    (S : BlockSystem Point Block) (D : Finset Point) : Nat :=
  ∑ b : Block,
    if S.kind b = .circle /\ (S.support b).card = 3 then
      elevenGammaSixOutside S D b
    else 0

/-- Outsider incidences with all generalized three-blocks. -/
def elevenGammaSixOutsiderThreeBlockIncidence
    (S : BlockSystem Point Block) (D : Finset Point) : Nat :=
  3 * elevenGammaSixRelativeCount S D .circle 0 3 +
  3 * elevenGammaSixRelativeCount S D .line 0 3 +
  2 * elevenGammaSixRelativeCount S D .circle 1 2 +
  2 * elevenGammaSixRelativeCount S D .line 1 2 +
  elevenGammaSixRelativeCount S D .circle 2 1 +
  elevenGammaSixRelativeCount S D .line 2 1

noncomputable def elevenGammaSixTotalOutsiderThreeBlockIncidence
    (S : BlockSystem Point Block) (D : Finset Point) : Nat :=
  ∑ b : Block,
    if (S.support b).card = 3 then elevenGammaSixOutside S D b else 0

/-- Restricted point--block incidence double count. -/
theorem elevenGammaSix_sum_degreeIn_on
    (S : BlockSystem Point Block) (F : Finset Block) (X : Finset Point) :
    (∑ p ∈ X, S.degreeIn F p) =
      ∑ b ∈ F, (S.support b ∩ X).card := by
  classical
  simp only [BlockSystem.degreeIn, Finset.card_eq_sum_ones,
    Finset.sum_filter]
  rw [Finset.sum_comm]
  simp [Finset.inter_comm]

/-- The ordinary-circle outsider incidence is the sum of ordinary-circle
degrees over the complement of the selected circle. -/
theorem elevenGammaSixTotalOrdinaryCircleIncidence_eq_sum_complement
    (S : BlockSystem Point Block) (D : Finset Point) :
    elevenGammaSixTotalOrdinaryCircleIncidence S D =
      ∑ p ∈ Finset.univ \ D, S.circleDegree 3 p := by
  classical
  have houtside (b : Block) :
      S.support b \ D = S.support b ∩ (Finset.univ \ D) := by
    ext p
    simp
  have hblocks : S.circleBlocksOfSize 3 =
      Finset.univ.filter fun b =>
        S.kind b = .circle ∧ (S.support b).card = 3 := by
    ext b
    simp
  calc
    elevenGammaSixTotalOrdinaryCircleIncidence S D =
        ∑ b ∈ S.circleBlocksOfSize 3,
          elevenGammaSixOutside S D b := by
      rw [hblocks, Finset.sum_filter]
      rfl
    _ = ∑ b ∈ S.circleBlocksOfSize 3,
          (S.support b ∩ (Finset.univ \ D)).card := by
      apply Finset.sum_congr rfl
      intro b _hb
      simp only [elevenGammaSixOutside, houtside]
    _ = ∑ p ∈ Finset.univ \ D, S.circleDegree 3 p := by
      change (∑ b ∈ S.circleBlocksOfSize 3,
          (S.support b ∩ (Finset.univ \ D)).card) =
        ∑ p ∈ Finset.univ \ D,
          S.degreeIn (S.circleBlocksOfSize 3) p
      exact (elevenGammaSix_sum_degreeIn_on S
        (S.circleBlocksOfSize 3) (Finset.univ \ D)).symm

theorem elevenGammaSixTotalOutsiderThreeBlockIncidence_eq_sum_complement
    (S : BlockSystem Point Block) (D : Finset Point) :
    elevenGammaSixTotalOutsiderThreeBlockIncidence S D =
      ∑ p ∈ Finset.univ \ D, S.blockDegree 3 p := by
  classical
  have houtside (b : Block) :
      S.support b \ D = S.support b ∩ (Finset.univ \ D) := by
    ext p
    simp
  have hblocks : S.blocksOfSize 3 =
      Finset.univ.filter fun b => (S.support b).card = 3 := by
    ext b
    simp
  calc
    elevenGammaSixTotalOutsiderThreeBlockIncidence S D =
        ∑ b ∈ S.blocksOfSize 3, elevenGammaSixOutside S D b := by
      rw [hblocks, Finset.sum_filter]
      rfl
    _ = ∑ b ∈ S.blocksOfSize 3,
          (S.support b ∩ (Finset.univ \ D)).card := by
      apply Finset.sum_congr rfl
      intro b _hb
      simp only [elevenGammaSixOutside, houtside]
    _ = ∑ p ∈ Finset.univ \ D, S.blockDegree 3 p := by
      change (∑ b ∈ S.blocksOfSize 3,
          (S.support b ∩ (Finset.univ \ D)).card) =
        ∑ p ∈ Finset.univ \ D,
          S.degreeIn (S.blocksOfSize 3) p
      exact (elevenGammaSix_sum_degreeIn_on S
        (S.blocksOfSize 3) (Finset.univ \ D)).symm

theorem elevenGammaSixTotalOutsiderThreeBlockIncidence_eq_grouped
    (S : BlockSystem Point Block) (D : Finset Point) (gamma : Block)
    (hD : D.card = 6) (hgammaSupport : S.support gamma = D) :
    elevenGammaSixTotalOutsiderThreeBlockIncidence S D =
      elevenGammaSixOutsiderThreeBlockIncidence S D := by
  classical
  have hpointwise (b : Block) :
      (if (S.support b).card = 3 then elevenGammaSixOutside S D b else 0) =
      (if S.kind b = .circle /\ elevenGammaSixInside S D b = 0 /\
          elevenGammaSixOutside S D b = 3 then 3 else 0) +
      (if S.kind b = .line /\ elevenGammaSixInside S D b = 0 /\
          elevenGammaSixOutside S D b = 3 then 3 else 0) +
      (if S.kind b = .circle /\ elevenGammaSixInside S D b = 1 /\
          elevenGammaSixOutside S D b = 2 then 2 else 0) +
      (if S.kind b = .line /\ elevenGammaSixInside S D b = 1 /\
          elevenGammaSixOutside S D b = 2 then 2 else 0) +
      (if S.kind b = .circle /\ elevenGammaSixInside S D b = 2 /\
          elevenGammaSixOutside S D b = 1 then 1 else 0) +
      (if S.kind b = .line /\ elevenGammaSixInside S D b = 2 /\
          elevenGammaSixOutside S D b = 1 then 1 else 0) := by
    by_cases hs : (S.support b).card = 3
    · have hne : b ≠ gamma := by
        intro h
        subst b
        rw [hgammaSupport, hD] at hs
        omega
      have hi := elevenGammaSixInside_le_two_of_ne
        S D gamma b hgammaSupport hne
      have hsum := elevenGammaSixInside_add_outside S D b
      rw [hs] at hsum
      have houtside : elevenGammaSixOutside S D b =
          3 - elevenGammaSixInside S D b := by
        omega
      cases hk : S.kind b <;>
        interval_cases elevenGammaSixInside S D b <;>
        simp [hs, houtside]
    · have hsum := elevenGammaSixInside_add_outside S D b
      by_cases hi0 : elevenGammaSixInside S D b = 0
      · have hx3 : elevenGammaSixOutside S D b ≠ 3 := by
          intro hx
          omega
        simp [hs, hi0, hx3]
      · by_cases hi1 : elevenGammaSixInside S D b = 1
        · have hx2 : elevenGammaSixOutside S D b ≠ 2 := by
            intro hx
            omega
          simp [hs, hi1, hx2]
        · by_cases hi2 : elevenGammaSixInside S D b = 2
          · have hx1 : elevenGammaSixOutside S D b ≠ 1 := by
              intro hx
              omega
            simp [hs, hi2, hx1]
          · simp [hs, hi0, hi1, hi2]
  unfold elevenGammaSixTotalOutsiderThreeBlockIncidence
  simp_rw [hpointwise]
  simp only [Finset.sum_add_distrib]
  rw [elevenGammaSix_sum_relative_indicator,
    elevenGammaSix_sum_relative_indicator,
    elevenGammaSix_sum_relative_indicator,
    elevenGammaSix_sum_relative_indicator,
    elevenGammaSix_sum_relative_indicator,
    elevenGammaSix_sum_relative_indicator]
  simp [elevenGammaSixOutsiderThreeBlockIncidence]

/-- Grouping ordinary three-circles by relative type gives exactly
`3 c03 + 2 c12 + c21`. -/
theorem elevenGammaSixTotalOrdinaryCircleIncidence_eq_ordinary
    (S : BlockSystem Point Block) (D : Finset Point) (gamma : Block)
    (hD : D.card = 6) (hgammaSupport : S.support gamma = D) :
    elevenGammaSixTotalOrdinaryCircleIncidence S D =
      elevenGammaSixOrdinaryCircleIncidence S D := by
  classical
  have hpointwise (b : Block) :
      (if S.kind b = .circle /\ (S.support b).card = 3 then
          elevenGammaSixOutside S D b
        else 0) =
      (if S.kind b = .circle /\ elevenGammaSixInside S D b = 0 /\
          elevenGammaSixOutside S D b = 3 then 3 else 0) +
      (if S.kind b = .circle /\ elevenGammaSixInside S D b = 1 /\
          elevenGammaSixOutside S D b = 2 then 2 else 0) +
      (if S.kind b = .circle /\ elevenGammaSixInside S D b = 2 /\
          elevenGammaSixOutside S D b = 1 then 1 else 0) := by
    by_cases hk : S.kind b = .circle
    · by_cases hs : (S.support b).card = 3
      · have hne : b ≠ gamma := by
          intro h
          subst b
          rw [hgammaSupport, hD] at hs
          omega
        have hi := elevenGammaSixInside_le_two_of_ne
          S D gamma b hgammaSupport hne
        have hsum := elevenGammaSixInside_add_outside S D b
        rw [hs] at hsum
        have houtside : elevenGammaSixOutside S D b =
            3 - elevenGammaSixInside S D b := by
          omega
        interval_cases elevenGammaSixInside S D b <;>
          norm_num [hk, hs, houtside]
      · have hsum := elevenGammaSixInside_add_outside S D b
        by_cases hi0 : elevenGammaSixInside S D b = 0
        · have hx3 : elevenGammaSixOutside S D b ≠ 3 := by
            intro hx
            omega
          simp [hk, hs, hi0, hx3]
        · by_cases hi1 : elevenGammaSixInside S D b = 1
          · have hx2 : elevenGammaSixOutside S D b ≠ 2 := by
              intro hx
              omega
            simp [hk, hs, hi1, hx2]
          · by_cases hi2 : elevenGammaSixInside S D b = 2
            · have hx1 : elevenGammaSixOutside S D b ≠ 1 := by
                intro hx
                omega
              simp [hk, hs, hi2, hx1]
            · simp [hk, hs, hi0, hi1, hi2]
    · simp [hk]
  unfold elevenGammaSixTotalOrdinaryCircleIncidence
  simp_rw [hpointwise]
  simp only [Finset.sum_add_distrib]
  rw [elevenGammaSix_sum_relative_indicator,
    elevenGammaSix_sum_relative_indicator,
    elevenGammaSix_sum_relative_indicator]
  simp [elevenGammaSixOrdinaryCircleIncidence]

/-- Under the six-circle cap, the sum form of `W` has exactly the three
relative contributions `1,3,6` displayed in the paper. -/
theorem elevenGammaSixTotalWeight_eq_weight
    (S : BlockSystem Point Block) (D : Finset Point)
    (hpoint : Fintype.card Point = 11) (hD : D.card = 6)
    (hcircleCap : forall b, S.kind b = .circle -> (S.support b).card <= 6) :
    elevenGammaSixTotalWeight S D = elevenGammaSixWeight S D := by
  classical
  have hpointwise (b : Block) :
      (if S.kind b = .circle /\ elevenGammaSixInside S D b = 2 then
          Nat.choose (elevenGammaSixOutside S D b) 2
        else 0) =
      (if S.kind b = .circle /\ elevenGammaSixInside S D b = 2 /\
          elevenGammaSixOutside S D b = 2 then 1 else 0) +
      (if S.kind b = .circle /\ elevenGammaSixInside S D b = 2 /\
          elevenGammaSixOutside S D b = 3 then 3 else 0) +
      (if S.kind b = .circle /\ elevenGammaSixInside S D b = 2 /\
          elevenGammaSixOutside S D b = 4 then 6 else 0) := by
    by_cases hk : S.kind b = .circle
    · by_cases hi : elevenGammaSixInside S D b = 2
      · have hx := elevenGammaSixOutside_le_five S D hpoint hD b
        have hsum := elevenGammaSixInside_add_outside S D b
        have hcap := hcircleCap b hk
        rw [← hsum, hi] at hcap
        interval_cases elevenGammaSixOutside S D b <;>
          norm_num [Nat.choose, hk, hi]; omega
      · simp [hk, hi]
    · simp [hk]
  unfold elevenGammaSixTotalWeight
  simp_rw [hpointwise]
  simp only [Finset.sum_add_distrib]
  rw [elevenGammaSix_sum_relative_indicator,
    elevenGammaSix_sum_relative_indicator,
    elevenGammaSix_sum_relative_indicator]
  simp [elevenGammaSixWeight]

/-- Under the line cap, the sum form of `J` has exactly the four relative
contributions `1,2,3,4`. -/
theorem elevenGammaSixTotalLineIncidence_eq_lineIncidence
    (S : BlockSystem Point Block) (D : Finset Point)
    (hpoint : Fintype.card Point = 11) (hD : D.card = 6)
    (hlineCap : forall b, S.kind b = .line -> (S.support b).card <= 6) :
    elevenGammaSixTotalLineIncidence S D =
      elevenGammaSixLineIncidence S D := by
  classical
  have hpointwise (b : Block) :
      (if S.kind b = .line /\ elevenGammaSixInside S D b = 2 then
          elevenGammaSixOutside S D b
        else 0) =
      (if S.kind b = .line /\ elevenGammaSixInside S D b = 2 /\
          elevenGammaSixOutside S D b = 1 then 1 else 0) +
      (if S.kind b = .line /\ elevenGammaSixInside S D b = 2 /\
          elevenGammaSixOutside S D b = 2 then 2 else 0) +
      (if S.kind b = .line /\ elevenGammaSixInside S D b = 2 /\
          elevenGammaSixOutside S D b = 3 then 3 else 0) +
      (if S.kind b = .line /\ elevenGammaSixInside S D b = 2 /\
          elevenGammaSixOutside S D b = 4 then 4 else 0) := by
    by_cases hk : S.kind b = .line
    · by_cases hi : elevenGammaSixInside S D b = 2
      · have hx := elevenGammaSixOutside_le_five S D hpoint hD b
        have hsum := elevenGammaSixInside_add_outside S D b
        have hcap := hlineCap b hk
        rw [← hsum, hi] at hcap
        interval_cases elevenGammaSixOutside S D b <;>
          norm_num [hk, hi]; omega
      · simp [hk, hi]
    · simp [hk]
  unfold elevenGammaSixTotalLineIncidence
  simp_rw [hpointwise]
  simp only [Finset.sum_add_distrib]
  rw [elevenGammaSix_sum_relative_indicator,
    elevenGammaSix_sum_relative_indicator,
    elevenGammaSix_sum_relative_indicator,
    elevenGammaSix_sum_relative_indicator]
  simp [elevenGammaSixLineIncidence]

/-- The ambient block-system sum for `W` is definitionally the semantic
six-conic weight on the five-point complement. -/
theorem elevenGammaSixTotalWeight_eq_sixConicWeight
    {α : Type u} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (gamma : DeterminedCircle cfg) :
    elevenGammaSixTotalWeight (blockSystem cfg)
        (circleTrace cfg gamma.1) =
      sixConicWeight cfg gamma
        (Finset.univ \ circleTrace cfg gamma.1) := by
  classical
  have houtside (c : DeterminedCircle cfg) :
      circleTrace cfg c.1 \ circleTrace cfg gamma.1 =
        circleTrace cfg c.1 ∩
          (Finset.univ \ circleTrace cfg gamma.1) := by
    ext p
    simp
  simp [elevenGammaSixTotalWeight, elevenGammaSixInside,
    elevenGammaSixOutside, sixConicWeight, blockSystem,
    geometricBlockSystem, geometricBlockKind, geometricBlockSupport,
    houtside]

/-- The ambient block-system sum for `J` is definitionally the semantic
six-conic line incidence on the five-point complement. -/
theorem elevenGammaSixTotalLineIncidence_eq_sixConicLineIncidence
    {α : Type u} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (gamma : DeterminedCircle cfg) :
    elevenGammaSixTotalLineIncidence (blockSystem cfg)
        (circleTrace cfg gamma.1) =
      sixConicLineIncidence cfg gamma
        (Finset.univ \ circleTrace cfg gamma.1) := by
  classical
  have houtside (L : DeterminedLine cfg) :
      lineSupport cfg L \ circleTrace cfg gamma.1 =
        lineSupport cfg L ∩
          (Finset.univ \ circleTrace cfg gamma.1) := by
    ext p
    simp
  simp [elevenGammaSixTotalLineIncidence, elevenGammaSixInside,
    elevenGammaSixOutside, sixConicLineIncidence, blockSystem,
    geometricBlockSystem, geometricBlockKind, geometricBlockSupport,
    houtside]

/-- The materialized relative-count weight agrees with the semantic
six-conic weight. -/
theorem elevenGammaSixWeight_eq_sixConicWeight
    {α : Type u} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (gamma : DeterminedCircle cfg)
    (hpoint : Fintype.card α = 11)
    (hgamma : (circleTrace cfg gamma.1).card = 6)
    (hcircleCap : forall c : DeterminedCircle cfg,
      (circleTrace cfg c.1).card <= 6) :
    elevenGammaSixWeight (blockSystem cfg) (circleTrace cfg gamma.1) =
      sixConicWeight cfg gamma
        (Finset.univ \ circleTrace cfg gamma.1) := by
  have hblockCap : forall b : GeometricBlock cfg,
      (blockSystem cfg).kind b = .circle ->
        ((blockSystem cfg).support b).card <= 6 := by
    intro b hb
    cases b with
    | inl L => cases hb
    | inr c => exact hcircleCap c
  calc
    elevenGammaSixWeight (blockSystem cfg) (circleTrace cfg gamma.1) =
        elevenGammaSixTotalWeight (blockSystem cfg)
          (circleTrace cfg gamma.1) :=
      (elevenGammaSixTotalWeight_eq_weight
        (blockSystem cfg) (circleTrace cfg gamma.1)
        hpoint hgamma hblockCap).symm
    _ = sixConicWeight cfg gamma
          (Finset.univ \ circleTrace cfg gamma.1) :=
      elevenGammaSixTotalWeight_eq_sixConicWeight cfg gamma

/-- The materialized relative-count incidence agrees with the semantic
six-conic line incidence. -/
theorem elevenGammaSixLineIncidence_eq_sixConicLineIncidence
    {α : Type u} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (gamma : DeterminedCircle cfg)
    (hpoint : Fintype.card α = 11)
    (hgamma : (circleTrace cfg gamma.1).card = 6)
    (hlineCap : forall L : DeterminedLine cfg,
      (lineSupport cfg L).card <= 6) :
    elevenGammaSixLineIncidence (blockSystem cfg)
        (circleTrace cfg gamma.1) =
      sixConicLineIncidence cfg gamma
        (Finset.univ \ circleTrace cfg gamma.1) := by
  have hblockCap : forall b : GeometricBlock cfg,
      (blockSystem cfg).kind b = .line ->
        ((blockSystem cfg).support b).card <= 6 := by
    intro b hb
    cases b with
    | inl L => exact hlineCap L
    | inr c => cases hb
  calc
    elevenGammaSixLineIncidence (blockSystem cfg)
        (circleTrace cfg gamma.1) =
        elevenGammaSixTotalLineIncidence (blockSystem cfg)
          (circleTrace cfg gamma.1) :=
      (elevenGammaSixTotalLineIncidence_eq_lineIncidence
        (blockSystem cfg) (circleTrace cfg gamma.1)
        hpoint hgamma hblockCap).symm
    _ = sixConicLineIncidence cfg gamma
          (Finset.univ \ circleTrace cfg gamma.1) :=
      elevenGammaSixTotalLineIncidence_eq_sixConicLineIncidence cfg gamma

/-- Five applications of U17, one on each four-subset of the outsider
five-set, give the integral cap `W <= 28`. -/
theorem elevenGammaSixWeight_le_twenty_eight
    {α : Type u} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (gamma : DeterminedCircle cfg)
    (hpoint : Fintype.card α = 11)
    (hgamma : (circleTrace cfg gamma.1).card = 6)
    (hcircleCap : forall c : DeterminedCircle cfg,
      (circleTrace cfg c.1).card <= 6) :
    elevenGammaSixWeight (blockSystem cfg) (circleTrace cfg gamma.1) <= 28 := by
  classical
  let X : Finset α := Finset.univ \ circleTrace cfg gamma.1
  have hX : X.card = 5 := by
    simp [X, Finset.card_sdiff_of_subset
      (Finset.subset_univ (circleTrace cfg gamma.1)), hpoint, hgamma]
  have hdisjoint : Disjoint (circleTrace cfg gamma.1) X := by
    simp [X, Finset.disjoint_left]
  have hsumLe :
      (∑ Y ∈ X.powersetCard 4,
          sixConicTotalWeight cfg gamma Y) <=
        ∑ _Y ∈ X.powersetCard 4, 17 := by
    apply Finset.sum_le_sum
    intro Y hY
    rw [sixConicTotalWeight_eq_sixConicWeight]
    have hYX := (Finset.mem_powersetCard.mp hY).1
    exact sixConicWeight_le_seventeen cfg gamma hgamma Y
      (Finset.mem_powersetCard.mp hY).2
      (hdisjoint.mono_right hYX)
  have hsumEq :=
    sum_sixConicTotalWeight_powersetCard_four cfg gamma X hX
  have hsemantic :=
    elevenGammaSixWeight_eq_sixConicWeight
      cfg gamma hpoint hgamma hcircleCap
  have hfive : (X.powersetCard 4).card = 5 := by
    rw [Finset.card_powersetCard, hX]
    norm_num [Nat.choose]
  simp only [Finset.sum_const, nsmul_eq_mul, hfive] at hsumLe
  rw [hsumEq, sixConicTotalWeight_eq_sixConicWeight] at hsumLe
  change elevenGammaSixWeight (blockSystem cfg)
    (circleTrace cfg gamma.1) = sixConicWeight cfg gamma X at hsemantic
  omega

/-- Kelly--Moser at each outsider gives the structural row used at the
five-footprint wall. -/
theorem twenty_five_le_elevenGammaSixOutsiderThreeBlockIncidence
    {α : Type u} [Fintype α] [DecidableEq α]
    (Kelly : RealPlaneKellyMoserPrinciple.{u})
    (cfg : Configuration α) (hadm : Admissible cfg)
    (hpoint : Fintype.card α = 11)
    (gamma : DeterminedCircle cfg)
    (hgamma : (circleTrace cfg gamma.1).card = 6) :
    25 <= elevenGammaSixOutsiderThreeBlockIncidence (blockSystem cfg)
      (circleTrace cfg gamma.1) := by
  classical
  let D : Finset α := circleTrace cfg gamma.1
  let X : Finset α := Finset.univ \ D
  let gammaBlock : GeometricBlock cfg := Sum.inr gamma
  have hX : X.card = 5 := by
    simp [X, D, Finset.card_sdiff_of_subset
      (Finset.subset_univ (circleTrace cfg gamma.1)), hpoint, hgamma]
  have hlocal (p : α) : 5 <= (blockSystem cfg).blockDegree 3 p := by
    have hp := Kelly.pivot_three_block_bound cfg hadm
      (by omega) (by omega) p
    rw [hpoint] at hp
    norm_num at hp
    simp only [Erdos506.V1.blockDegree] at hp
    omega
  have hsum :
      (∑ _p ∈ X, 5) <=
        ∑ p ∈ X, (blockSystem cfg).blockDegree 3 p :=
    Finset.sum_le_sum fun p _hp => hlocal p
  have htotal :=
    elevenGammaSixTotalOutsiderThreeBlockIncidence_eq_sum_complement
      (blockSystem cfg) D
  have hgrouped :=
    elevenGammaSixTotalOutsiderThreeBlockIncidence_eq_grouped
      (blockSystem cfg) D gammaBlock hgamma rfl
  change elevenGammaSixTotalOutsiderThreeBlockIncidence
      (blockSystem cfg) D =
    ∑ p ∈ X, (blockSystem cfg).blockDegree 3 p at htotal
  rw [← htotal, hgrouped] at hsum
  simpa [hX] using hsum

/-- The configuration-level Melchior row gives the exact remaining line
slack input `M <= 52`. -/
theorem elevenGammaSixLineMelchiorUsed_le_fifty_two
    {α : Type u} [Fintype α] [DecidableEq α]
    (Mel : RealPlaneMelchiorPrinciple.{u})
    (cfg : Configuration α) (hadm : Admissible cfg)
    (hpoint : Fintype.card α = 11)
    (gamma : DeterminedCircle cfg)
    (hgamma : (circleTrace cfg gamma.1).card = 6)
    (hlineCap : forall L : DeterminedLine cfg,
      (lineSupport cfg L).card <= 6) :
    elevenGammaSixLineMelchiorUsed (blockSystem cfg)
      (circleTrace cfg gamma.1) <= 52 := by
  let D : Finset α := circleTrace cfg gamma.1
  let gammaBlock : GeometricBlock cfg := Sum.inr gamma
  have hblockLineCap : forall b : GeometricBlock cfg,
      (blockSystem cfg).kind b = .line ->
        ((blockSystem cfg).support b).card <= 6 := by
    intro b hb
    cases b with
    | inl L => exact hlineCap L
    | inr c => cases hb
  have heq := elevenGammaSixLineMelchiorUsed_eq_total
    (blockSystem cfg) D gammaBlock hpoint hgamma rfl rfl hblockLineCap
  have hglobal :=
    globalLineRow_le_choose_two_sub_three_of_realPlaneMelchior
      Mel cfg hadm
  change (blockSystem cfg).globalLineRow <=
    (Nat.choose (Fintype.card α) 2 : Int) - 3 at hglobal
  rw [hpoint] at hglobal
  norm_num [Nat.choose] at hglobal
  have htotalZ :
      (elevenGammaSixTotalLineMelchiorUsed (blockSystem cfg) : Int) <=
        52 := by
    rw [elevenGammaSixTotalLineMelchiorUsed_cast]
    exact hglobal
  have htotal :
      elevenGammaSixTotalLineMelchiorUsed (blockSystem cfg) <= 52 := by
    exact_mod_cast htotalZ
  change elevenGammaSixLineMelchiorUsed (blockSystem cfg) D <= 52
  omega

/-- The full circle census, including the distinguished selected circle. -/
def elevenGammaSixCircleTotalCensus
    (S : BlockSystem Point Block) (D : Finset Point) : Nat :=
  1 +
  elevenGammaSixRelativeCount S D .circle 0 3 +
  elevenGammaSixRelativeCount S D .circle 0 4 +
  elevenGammaSixRelativeCount S D .circle 0 5 +
  elevenGammaSixRelativeCount S D .circle 1 2 +
  elevenGammaSixRelativeCount S D .circle 1 3 +
  elevenGammaSixRelativeCount S D .circle 1 4 +
  elevenGammaSixRelativeCount S D .circle 1 5 +
  elevenGammaSixRelativeCount S D .circle 2 1 +
  elevenGammaSixRelativeCount S D .circle 2 2 +
  elevenGammaSixRelativeCount S D .circle 2 3 +
  elevenGammaSixRelativeCount S D .circle 2 4

/-- Relative-type expansion of the three-outsider footprint count. -/
def elevenGammaSixFootprintThreeCensus
    (S : BlockSystem Point Block) (D : Finset Point) : Nat :=
  elevenGammaSixRelativeCount S D .circle 0 3 +
  elevenGammaSixRelativeCount S D .line 0 3 +
  elevenGammaSixRelativeCount S D .circle 1 3 +
  elevenGammaSixRelativeCount S D .line 1 3 +
  elevenGammaSixRelativeCount S D .circle 2 3 +
  elevenGammaSixRelativeCount S D .line 2 3

/-- Relative-type expansion of the four-outsider footprint count. -/
def elevenGammaSixFootprintFourCensus
    (S : BlockSystem Point Block) (D : Finset Point) : Nat :=
  elevenGammaSixRelativeCount S D .circle 0 4 +
  elevenGammaSixRelativeCount S D .line 0 4 +
  elevenGammaSixRelativeCount S D .circle 1 4 +
  elevenGammaSixRelativeCount S D .line 1 4 +
  elevenGammaSixRelativeCount S D .circle 2 4 +
  elevenGammaSixRelativeCount S D .line 2 4

/-- Relative-type expansion of the five-outsider footprint count.  A
selected trace of size two is absent because both block tags have cap six. -/
def elevenGammaSixFootprintFiveCensus
    (S : BlockSystem Point Block) (D : Finset Point) : Nat :=
  elevenGammaSixRelativeCount S D .circle 0 5 +
  elevenGammaSixRelativeCount S D .line 0 5 +
  elevenGammaSixRelativeCount S D .circle 1 5 +
  elevenGammaSixRelativeCount S D .line 1 5

/-- The `j = 1` relative triple row, in relative-count form. -/
def elevenGammaSixTripleOneCensus
    (S : BlockSystem Point Block) (D : Finset Point) : Nat :=
  elevenGammaSixRelativeCount S D .circle 1 2 +
  elevenGammaSixRelativeCount S D .line 1 2 +
  3 * elevenGammaSixRelativeCount S D .circle 1 3 +
  3 * elevenGammaSixRelativeCount S D .line 1 3 +
  6 * elevenGammaSixRelativeCount S D .circle 1 4 +
  6 * elevenGammaSixRelativeCount S D .line 1 4 +
  10 * elevenGammaSixRelativeCount S D .circle 1 5 +
  10 * elevenGammaSixRelativeCount S D .line 1 5 +
  2 * elevenGammaSixRelativeCount S D .circle 2 2 +
  2 * elevenGammaSixRelativeCount S D .line 2 2 +
  6 * elevenGammaSixRelativeCount S D .circle 2 3 +
  6 * elevenGammaSixRelativeCount S D .line 2 3 +
  12 * elevenGammaSixRelativeCount S D .circle 2 4 +
  12 * elevenGammaSixRelativeCount S D .line 2 4

/-- The `j = 2` relative triple row, in relative-count form. -/
def elevenGammaSixTripleTwoCensus
    (S : BlockSystem Point Block) (D : Finset Point) : Nat :=
  elevenGammaSixRelativeCount S D .circle 2 1 +
  elevenGammaSixRelativeCount S D .line 2 1 +
  2 * elevenGammaSixRelativeCount S D .circle 2 2 +
  2 * elevenGammaSixRelativeCount S D .line 2 2 +
  3 * elevenGammaSixRelativeCount S D .circle 2 3 +
  3 * elevenGammaSixRelativeCount S D .line 2 3 +
  4 * elevenGammaSixRelativeCount S D .circle 2 4 +
  4 * elevenGammaSixRelativeCount S D .line 2 4

/-- A footprint of positive size at least three belongs to a nonselected
block, so its selected trace has size zero, one, or two. -/
theorem elevenGammaSix_footprintCount_eq_six_relative_types
    (S : BlockSystem Point Block) (D : Finset Point) (gamma : Block)
    (hgammaSupport : S.support gamma = D) (x : Nat) (hthree : 3 <= x) :
    elevenGammaSixFootprintCount S D x =
      elevenGammaSixRelativeCount S D .circle 0 x +
      elevenGammaSixRelativeCount S D .line 0 x +
      elevenGammaSixRelativeCount S D .circle 1 x +
      elevenGammaSixRelativeCount S D .line 1 x +
      elevenGammaSixRelativeCount S D .circle 2 x +
      elevenGammaSixRelativeCount S D .line 2 x := by
  classical
  have hpointwise (b : Block) :
      (if elevenGammaSixOutside S D b = x then 1 else 0) =
      (if S.kind b = .circle /\
          elevenGammaSixInside S D b = 0 /\
          elevenGammaSixOutside S D b = x then 1 else 0) +
      (if S.kind b = .line /\
          elevenGammaSixInside S D b = 0 /\
          elevenGammaSixOutside S D b = x then 1 else 0) +
      (if S.kind b = .circle /\
          elevenGammaSixInside S D b = 1 /\
          elevenGammaSixOutside S D b = x then 1 else 0) +
      (if S.kind b = .line /\
          elevenGammaSixInside S D b = 1 /\
          elevenGammaSixOutside S D b = x then 1 else 0) +
      (if S.kind b = .circle /\
          elevenGammaSixInside S D b = 2 /\
          elevenGammaSixOutside S D b = x then 1 else 0) +
      (if S.kind b = .line /\
          elevenGammaSixInside S D b = 2 /\
          elevenGammaSixOutside S D b = x then 1 else 0) := by
    by_cases hb : b = gamma
    · subst b
      have hout : elevenGammaSixOutside S D gamma = 0 := by
        simp [elevenGammaSixOutside, hgammaSupport]
      have hxne : 0 ≠ x := by omega
      simp [hout, hxne]
    · have hi := elevenGammaSixInside_le_two_of_ne
        S D gamma b hgammaSupport hb
      cases hk : S.kind b <;>
        interval_cases elevenGammaSixInside S D b <;>
        simp
  have hleft := elevenGammaSix_sum_footprint_indicator S D x 1
  have hsum :
      (∑ b : Block, if elevenGammaSixOutside S D b = x then 1 else 0) =
        elevenGammaSixRelativeCount S D .circle 0 x +
        elevenGammaSixRelativeCount S D .line 0 x +
        elevenGammaSixRelativeCount S D .circle 1 x +
        elevenGammaSixRelativeCount S D .line 1 x +
        elevenGammaSixRelativeCount S D .circle 2 x +
        elevenGammaSixRelativeCount S D .line 2 x := by
    simp_rw [hpointwise]
    simp only [Finset.sum_add_distrib]
    rw [elevenGammaSix_sum_relative_indicator,
      elevenGammaSix_sum_relative_indicator,
      elevenGammaSix_sum_relative_indicator,
      elevenGammaSix_sum_relative_indicator,
      elevenGammaSix_sum_relative_indicator,
      elevenGammaSix_sum_relative_indicator]
    simp
  omega

/-- A relative type whose two selected and five outsider labels exceed a
support cap six is empty. -/
theorem elevenGammaSix_relativeCount_two_five_eq_zero
    (S : BlockSystem Point Block) (D : Finset Point) (kind : BlockKind)
    (hcap : forall b, S.kind b = kind -> (S.support b).card <= 6) :
    elevenGammaSixRelativeCount S D kind 2 5 = 0 := by
  classical
  rw [elevenGammaSixRelativeCount, Finset.card_eq_zero]
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro b hb
  have hspec := Finset.mem_filter.mp hb |>.2
  have hsum := elevenGammaSixInside_add_outside S D b
  have hle := hcap b hspec.1
  omega

theorem elevenGammaSix_exists_relative_block_of_count_eq_one
    (S : BlockSystem Point Block) (D : Finset Point)
    (kind : BlockKind) (g x : Nat)
    (hcount : elevenGammaSixRelativeCount S D kind g x = 1) :
    exists b : Block,
      S.kind b = kind /\
      elevenGammaSixInside S D b = g /\
      elevenGammaSixOutside S D b = x := by
  classical
  have hcountPos : 0 < elevenGammaSixRelativeCount S D kind g x := by
    omega
  have hpos : 0 < (elevenGammaSixRelativeBlocks S D kind g x).card := by
    simpa [elevenGammaSixRelativeCount] using hcountPos
  obtain ⟨b, hb⟩ := Finset.card_pos.mp hpos
  exact ⟨b, (Finset.mem_filter.mp hb).2⟩

/-- A line with one selected and all five outsider labels has support six.
Its rich-line pencil already contains at least forty-five proper circles, so
it cannot occur under the contradictory eleven-point bound. -/
theorem elevenGammaSix_l15_eq_zero_of_circleCount_le_forty
    (S : BlockSystem Point Block) (D : Finset Point)
    (hpoint : Fintype.card Point = 11)
    (hC : S.totalCircleCount <= 40) :
    elevenGammaSixRelativeCount S D .line 1 5 = 0 := by
  classical
  by_contra hnot
  have hpos : 0 < elevenGammaSixRelativeCount S D .line 1 5 := by omega
  have hblocksPos :
      0 < (elevenGammaSixRelativeBlocks S D .line 1 5).card := by
    simpa [elevenGammaSixRelativeCount] using hpos
  obtain ⟨b, hb⟩ := Finset.card_pos.mp hblocksPos
  have hbSpec := (Finset.mem_filter.mp hb).2
  rcases hbSpec with ⟨hbKind, hbInside, hbOutside⟩
  have hsum := elevenGammaSixInside_add_outside S D b
  have hbSize : (S.support b).card = 6 := by omega
  have hpencil := richLinePencilBound_le_totalCircleCount S b hbKind
  rw [hpoint, hbSize] at hpencil
  norm_num [Nat.choose] at hpencil
  omega

theorem elevenGammaSix_complement_subset_support_of_outside_five
    (S : BlockSystem Point Block) (D : Finset Point)
    (hpoint : Fintype.card Point = 11) (hD : D.card = 6)
    (b : Block) (houtside : elevenGammaSixOutside S D b = 5) :
    Finset.univ \ D ⊆ S.support b := by
  let X : Finset Point := Finset.univ \ D
  have hX : X.card = 5 := by
    simp [X, Finset.card_sdiff_of_subset (Finset.subset_univ D),
      hpoint, hD]
  have hsub : S.support b \ D ⊆ X := by
    intro p hp
    exact Finset.mem_sdiff.mpr
      ⟨Finset.mem_univ p, (Finset.mem_sdiff.mp hp).2⟩
  have hcard : (S.support b \ D).card = 5 := houtside
  have heq : S.support b \ D = X :=
    Finset.eq_of_subset_of_card_le hsub (by omega)
  intro p hp
  have hp' : p ∈ S.support b \ D := by
    rw [heq]
    exact hp
  exact (Finset.mem_sdiff.mp hp').1

theorem elevenGammaSix_support_disjoint_of_inside_zero
    (S : BlockSystem Point Block) (D : Finset Point) (b : Block)
    (hinside : elevenGammaSixInside S D b = 0) :
    Disjoint (S.support b) D := by
  rw [Finset.disjoint_iff_inter_eq_empty]
  apply Finset.card_eq_zero.mp
  simpa [elevenGammaSixInside] using hinside

theorem elevenGammaSix_support_not_disjoint_of_inside_pos
    (S : BlockSystem Point Block) (D : Finset Point) (b : Block)
    (hinside : 0 < elevenGammaSixInside S D b) :
    ¬Disjoint (S.support b) D := by
  intro hdisjoint
  rw [Finset.disjoint_iff_inter_eq_empty] at hdisjoint
  have hzero : (S.support b ∩ D).card = 0 := by rw [hdisjoint]; simp
  simp only [elevenGammaSixInside] at hinside
  omega

theorem elevenGammaSix_exists_four_outsider_block
    (S : BlockSystem Point Block) (D : Finset Point)
    (hcount : elevenGammaSixFootprintCount S D 4 = 1) :
    exists b : Block,
      (S.support b ∩ (Finset.univ \ D)).card = 4 := by
  classical
  have hcountPos : 0 < elevenGammaSixFootprintCount S D 4 := by omega
  have hpos : 0 <
      (Finset.univ.filter fun b => elevenGammaSixOutside S D b = 4).card := by
    simpa [elevenGammaSixFootprintCount] using hcountPos
  obtain ⟨b, hb⟩ := Finset.card_pos.mp hpos
  have houtside := (Finset.mem_filter.mp hb).2
  refine ⟨b, ?_⟩
  have heq : S.support b \ D =
      S.support b ∩ (Finset.univ \ D) := by
    ext p
    simp
  rw [← heq]
  exact houtside

/-- A line through all five outsiders owns every outsider pair, so no other
line can contain two outsiders. -/
theorem elevenGammaSix_l05_eq_one_forces_l12_l22_zero
    (S : BlockSystem Point Block) (D : Finset Point)
    (hpoint : Fintype.card Point = 11) (hD : D.card = 6)
    (hl05 : elevenGammaSixRelativeCount S D .line 0 5 = 1) :
    elevenGammaSixRelativeCount S D .line 1 2 = 0 /\
      elevenGammaSixRelativeCount S D .line 2 2 = 0 := by
  classical
  let X : Finset Point := Finset.univ \ D
  have hX : X.card = 5 := by
    simp [X, Finset.card_sdiff_of_subset (Finset.subset_univ D),
      hpoint, hD]
  obtain ⟨b, hbKind, hbInside, hbOutside⟩ :=
    elevenGammaSix_exists_relative_block_of_count_eq_one
      S D .line 0 5 hl05
  have hbSub : S.support b \ D ⊆ X := by
    intro p hp
    exact Finset.mem_sdiff.mpr
      ⟨Finset.mem_univ p, (Finset.mem_sdiff.mp hp).2⟩
  have hbCard : (S.support b \ D).card = 5 := hbOutside
  have hbX : S.support b \ D = X :=
    Finset.eq_of_subset_of_card_le hbSub (by omega)
  have hzero (g : Nat) (hg : g ≠ 0) :
      elevenGammaSixRelativeCount S D .line g 2 = 0 := by
    rw [elevenGammaSixRelativeCount, Finset.card_eq_zero]
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro c hc
    have hcSpec := (Finset.mem_filter.mp hc).2
    by_cases hcb : c = b
    · subst c
      omega
    · have hcSubX : S.support c \ D ⊆ X := by
        intro p hp
        exact Finset.mem_sdiff.mpr
          ⟨Finset.mem_univ p, (Finset.mem_sdiff.mp hp).2⟩
      have hcSubB : S.support c \ D ⊆ S.support b \ D := by
        rw [hbX]
        exact hcSubX
      have hcSubInter : S.support c \ D ⊆
          S.support b ∩ S.support c := by
        intro p hp
        exact Finset.mem_inter.mpr
          ⟨(Finset.mem_sdiff.mp (hcSubB hp)).1,
            (Finset.mem_sdiff.mp hp).1⟩
      have hle := Finset.card_le_card hcSubInter
      have hbcLine :
          (⟨b, hbKind⟩ : LineBlock S) ≠ ⟨c, hcSpec.1⟩ := by
        intro h
        exact hcb (congrArg Subtype.val h).symm
      have hlt := S.distinct_line_inter_card_lt_two hbcLine
      have hlt' : (S.support b ∩ S.support c).card < 2 := by
        simpa using hlt
      have hcOutside : (S.support c \ D).card = 2 := by
        simpa only [elevenGammaSixOutside] using hcSpec.2.2
      omega
  exact ⟨hzero 1 (by omega), hzero 2 (by omega)⟩

theorem elevenGammaSix_footprintThreeCensus_eq
    (S : BlockSystem Point Block) (D : Finset Point) (gamma : Block)
    (hgammaSupport : S.support gamma = D) :
    elevenGammaSixFootprintCount S D 3 =
      elevenGammaSixFootprintThreeCensus S D := by
  simpa [elevenGammaSixFootprintThreeCensus, add_assoc] using
    elevenGammaSix_footprintCount_eq_six_relative_types
      S D gamma hgammaSupport 3 (by omega)

theorem elevenGammaSix_footprintFourCensus_eq
    (S : BlockSystem Point Block) (D : Finset Point) (gamma : Block)
    (hgammaSupport : S.support gamma = D) :
    elevenGammaSixFootprintCount S D 4 =
      elevenGammaSixFootprintFourCensus S D := by
  simpa [elevenGammaSixFootprintFourCensus, add_assoc] using
    elevenGammaSix_footprintCount_eq_six_relative_types
      S D gamma hgammaSupport 4 (by omega)

theorem elevenGammaSix_footprintFiveCensus_eq
    (S : BlockSystem Point Block) (D : Finset Point) (gamma : Block)
    (hgammaSupport : S.support gamma = D)
    (hcircleCap : forall b, S.kind b = .circle -> (S.support b).card <= 6)
    (hlineCap : forall b, S.kind b = .line -> (S.support b).card <= 6) :
    elevenGammaSixFootprintCount S D 5 =
      elevenGammaSixFootprintFiveCensus S D := by
  have htypes := elevenGammaSix_footprintCount_eq_six_relative_types
    S D gamma hgammaSupport 5 (by omega)
  have hc25 := elevenGammaSix_relativeCount_two_five_eq_zero
    S D .circle hcircleCap
  have hl25 := elevenGammaSix_relativeCount_two_five_eq_zero
    S D .line hlineCap
  rw [hc25, hl25] at htypes
  simpa [elevenGammaSixFootprintFiveCensus, add_assoc] using htypes

/-- Direct expansion of the total circle count into the selected circle
and the eleven possible nonselected relative types. -/
theorem elevenGammaSix_circleTotalCensus_eq
    (S : BlockSystem Point Block) (D : Finset Point) (gamma : Block)
    (hpoint : Fintype.card Point = 11) (hD : D.card = 6)
    (hgammaKind : S.kind gamma = .circle)
    (hgammaSupport : S.support gamma = D)
    (hcircleCap : forall b, S.kind b = .circle -> (S.support b).card <= 6) :
    S.totalCircleCount = elevenGammaSixCircleTotalCensus S D := by
  classical
  have hcircle :
      (∑ b : Block, if S.kind b = .circle then 1 else 0) =
        S.totalCircleCount := by
    rw [← Finset.sum_filter]
    simp [BlockSystem.totalCircleCount, BlockSystem.blocksOfKind]
  have hpointwise (b : Block) :
      (if S.kind b = .circle then 1 else 0) =
      (if b = gamma then 1 else 0) +
      (if S.kind b = .circle /\
          elevenGammaSixInside S D b = 0 /\
          elevenGammaSixOutside S D b = 3 then 1 else 0) +
      (if S.kind b = .circle /\
          elevenGammaSixInside S D b = 0 /\
          elevenGammaSixOutside S D b = 4 then 1 else 0) +
      (if S.kind b = .circle /\
          elevenGammaSixInside S D b = 0 /\
          elevenGammaSixOutside S D b = 5 then 1 else 0) +
      (if S.kind b = .circle /\
          elevenGammaSixInside S D b = 1 /\
          elevenGammaSixOutside S D b = 2 then 1 else 0) +
      (if S.kind b = .circle /\
          elevenGammaSixInside S D b = 1 /\
          elevenGammaSixOutside S D b = 3 then 1 else 0) +
      (if S.kind b = .circle /\
          elevenGammaSixInside S D b = 1 /\
          elevenGammaSixOutside S D b = 4 then 1 else 0) +
      (if S.kind b = .circle /\
          elevenGammaSixInside S D b = 1 /\
          elevenGammaSixOutside S D b = 5 then 1 else 0) +
      (if S.kind b = .circle /\
          elevenGammaSixInside S D b = 2 /\
          elevenGammaSixOutside S D b = 1 then 1 else 0) +
      (if S.kind b = .circle /\
          elevenGammaSixInside S D b = 2 /\
          elevenGammaSixOutside S D b = 2 then 1 else 0) +
      (if S.kind b = .circle /\
          elevenGammaSixInside S D b = 2 /\
          elevenGammaSixOutside S D b = 3 then 1 else 0) +
      (if S.kind b = .circle /\
          elevenGammaSixInside S D b = 2 /\
          elevenGammaSixOutside S D b = 4 then 1 else 0) := by
    by_cases hb : b = gamma
    · subst b
      simp [elevenGammaSixInside, elevenGammaSixOutside,
        hgammaSupport, hD, hgammaKind]
    · have hi := elevenGammaSixInside_le_two_of_ne
        S D gamma b hgammaSupport hb
      have hx := elevenGammaSixOutside_le_five S D hpoint hD b
      have hsum := elevenGammaSixInside_add_outside S D b
      cases hk : S.kind b with
      | line => simp [hb]
      | circle =>
          have hmin := S.circle_min b hk
          have hcap := hcircleCap b hk
          rw [← hsum] at hmin hcap
          interval_cases elevenGammaSixInside S D b <;>
            interval_cases elevenGammaSixOutside S D b <;>
            norm_num [hk, hb] at *
  have hsum :
      (∑ b : Block, if S.kind b = .circle then 1 else 0) =
        elevenGammaSixCircleTotalCensus S D := by
    simp_rw [hpointwise]
    simp only [Finset.sum_add_distrib]
    rw [elevenGammaSix_sum_relative_indicator,
      elevenGammaSix_sum_relative_indicator,
      elevenGammaSix_sum_relative_indicator,
      elevenGammaSix_sum_relative_indicator,
      elevenGammaSix_sum_relative_indicator,
      elevenGammaSix_sum_relative_indicator,
      elevenGammaSix_sum_relative_indicator,
      elevenGammaSix_sum_relative_indicator,
      elevenGammaSix_sum_relative_indicator,
      elevenGammaSix_sum_relative_indicator,
      elevenGammaSix_sum_relative_indicator]
    simp [elevenGammaSixCircleTotalCensus]
  omega

/-- Direct construction of the `j = 2` relative triple row. -/
theorem elevenGammaSix_tripleTwoCensus_eq_seventy_five
    (S : BlockSystem Point Block) (D : Finset Point) (gamma : Block)
    (hpoint : Fintype.card Point = 11) (hD : D.card = 6)
    (hgammaKind : S.kind gamma = .circle)
    (hgammaSupport : S.support gamma = D)
    (hcircleCap : forall b, S.kind b = .circle -> (S.support b).card <= 6)
    (hlineCap : forall b, S.kind b = .line -> (S.support b).card <= 6) :
    elevenGammaSixTripleTwoCensus S D = 75 := by
  have hrow := S.relative_triple_partition D 2 (by omega)
  rw [hpoint, hD] at hrow
  norm_num [elevenGammaSixInside, elevenGammaSixOutside, Nat.choose]
    at hrow
  have hpointwise (b : Block) :
      Nat.choose (elevenGammaSixInside S D b) 2 *
          elevenGammaSixOutside S D b =
      (if S.kind b = .circle /\
          elevenGammaSixInside S D b = 2 /\
          elevenGammaSixOutside S D b = 1 then 1 else 0) +
      (if S.kind b = .line /\
          elevenGammaSixInside S D b = 2 /\
          elevenGammaSixOutside S D b = 1 then 1 else 0) +
      (if S.kind b = .circle /\
          elevenGammaSixInside S D b = 2 /\
          elevenGammaSixOutside S D b = 2 then 2 else 0) +
      (if S.kind b = .line /\
          elevenGammaSixInside S D b = 2 /\
          elevenGammaSixOutside S D b = 2 then 2 else 0) +
      (if S.kind b = .circle /\
          elevenGammaSixInside S D b = 2 /\
          elevenGammaSixOutside S D b = 3 then 3 else 0) +
      (if S.kind b = .line /\
          elevenGammaSixInside S D b = 2 /\
          elevenGammaSixOutside S D b = 3 then 3 else 0) +
      (if S.kind b = .circle /\
          elevenGammaSixInside S D b = 2 /\
          elevenGammaSixOutside S D b = 4 then 4 else 0) +
      (if S.kind b = .line /\
          elevenGammaSixInside S D b = 2 /\
          elevenGammaSixOutside S D b = 4 then 4 else 0) := by
    by_cases hb : b = gamma
    · subst b
      simp [elevenGammaSixInside, elevenGammaSixOutside,
        hgammaSupport, hD, hgammaKind, Nat.choose]
    · have hi := elevenGammaSixInside_le_two_of_ne
        S D gamma b hgammaSupport hb
      have hx := elevenGammaSixOutside_le_five S D hpoint hD b
      have hsum := elevenGammaSixInside_add_outside S D b
      cases hk : S.kind b with
      | circle =>
          have hcap := hcircleCap b hk
          rw [← hsum] at hcap
          interval_cases elevenGammaSixInside S D b <;>
            interval_cases elevenGammaSixOutside S D b <;>
            norm_num [Nat.choose, hk] at * <;> simp
      | line =>
          have hcap := hlineCap b hk
          rw [← hsum] at hcap
          interval_cases elevenGammaSixInside S D b <;>
            interval_cases elevenGammaSixOutside S D b <;>
            norm_num [Nat.choose, hk] at * <;> simp
  have hsum :
      (∑ b : Block,
        Nat.choose (elevenGammaSixInside S D b) 2 *
          elevenGammaSixOutside S D b) =
        elevenGammaSixTripleTwoCensus S D := by
    simp_rw [hpointwise]
    simp only [Finset.sum_add_distrib]
    rw [elevenGammaSix_sum_relative_indicator,
      elevenGammaSix_sum_relative_indicator,
      elevenGammaSix_sum_relative_indicator,
      elevenGammaSix_sum_relative_indicator,
      elevenGammaSix_sum_relative_indicator,
      elevenGammaSix_sum_relative_indicator,
      elevenGammaSix_sum_relative_indicator,
      elevenGammaSix_sum_relative_indicator]
    simp [elevenGammaSixTripleTwoCensus]
  exact hsum.symm.trans hrow

/-- Direct construction of the `j = 1` relative triple row. -/
theorem elevenGammaSix_tripleOneCensus_eq_sixty
    (S : BlockSystem Point Block) (D : Finset Point) (gamma : Block)
    (hpoint : Fintype.card Point = 11) (hD : D.card = 6)
    (hgammaKind : S.kind gamma = .circle)
    (hgammaSupport : S.support gamma = D)
    (hcircleCap : forall b, S.kind b = .circle -> (S.support b).card <= 6)
    (hlineCap : forall b, S.kind b = .line -> (S.support b).card <= 6) :
    elevenGammaSixTripleOneCensus S D = 60 := by
  have hrow := S.relative_triple_partition D 1 (by omega)
  rw [hpoint, hD] at hrow
  norm_num [elevenGammaSixInside, elevenGammaSixOutside, Nat.choose]
    at hrow
  have hpointwise (b : Block) :
      elevenGammaSixInside S D b *
          Nat.choose (elevenGammaSixOutside S D b) 2 =
      (if S.kind b = .circle /\
          elevenGammaSixInside S D b = 1 /\
          elevenGammaSixOutside S D b = 2 then 1 else 0) +
      (if S.kind b = .line /\
          elevenGammaSixInside S D b = 1 /\
          elevenGammaSixOutside S D b = 2 then 1 else 0) +
      (if S.kind b = .circle /\
          elevenGammaSixInside S D b = 1 /\
          elevenGammaSixOutside S D b = 3 then 3 else 0) +
      (if S.kind b = .line /\
          elevenGammaSixInside S D b = 1 /\
          elevenGammaSixOutside S D b = 3 then 3 else 0) +
      (if S.kind b = .circle /\
          elevenGammaSixInside S D b = 1 /\
          elevenGammaSixOutside S D b = 4 then 6 else 0) +
      (if S.kind b = .line /\
          elevenGammaSixInside S D b = 1 /\
          elevenGammaSixOutside S D b = 4 then 6 else 0) +
      (if S.kind b = .circle /\
          elevenGammaSixInside S D b = 1 /\
          elevenGammaSixOutside S D b = 5 then 10 else 0) +
      (if S.kind b = .line /\
          elevenGammaSixInside S D b = 1 /\
          elevenGammaSixOutside S D b = 5 then 10 else 0) +
      (if S.kind b = .circle /\
          elevenGammaSixInside S D b = 2 /\
          elevenGammaSixOutside S D b = 2 then 2 else 0) +
      (if S.kind b = .line /\
          elevenGammaSixInside S D b = 2 /\
          elevenGammaSixOutside S D b = 2 then 2 else 0) +
      (if S.kind b = .circle /\
          elevenGammaSixInside S D b = 2 /\
          elevenGammaSixOutside S D b = 3 then 6 else 0) +
      (if S.kind b = .line /\
          elevenGammaSixInside S D b = 2 /\
          elevenGammaSixOutside S D b = 3 then 6 else 0) +
      (if S.kind b = .circle /\
          elevenGammaSixInside S D b = 2 /\
          elevenGammaSixOutside S D b = 4 then 12 else 0) +
      (if S.kind b = .line /\
          elevenGammaSixInside S D b = 2 /\
          elevenGammaSixOutside S D b = 4 then 12 else 0) := by
    by_cases hb : b = gamma
    · subst b
      simp [elevenGammaSixInside, elevenGammaSixOutside,
        hgammaSupport, hD, hgammaKind]
    · have hi := elevenGammaSixInside_le_two_of_ne
        S D gamma b hgammaSupport hb
      have hx := elevenGammaSixOutside_le_five S D hpoint hD b
      have hsum := elevenGammaSixInside_add_outside S D b
      cases hk : S.kind b with
      | circle =>
          have hcap := hcircleCap b hk
          rw [← hsum] at hcap
          interval_cases elevenGammaSixInside S D b <;>
            interval_cases elevenGammaSixOutside S D b <;>
            norm_num [Nat.choose, hk] at * <;> simp
      | line =>
          have hcap := hlineCap b hk
          rw [← hsum] at hcap
          interval_cases elevenGammaSixInside S D b <;>
            interval_cases elevenGammaSixOutside S D b <;>
            norm_num [Nat.choose, hk] at * <;> simp
  have hsum :
      (∑ b : Block,
        elevenGammaSixInside S D b *
          Nat.choose (elevenGammaSixOutside S D b) 2) =
        elevenGammaSixTripleOneCensus S D := by
    simp_rw [hpointwise]
    simp only [Finset.sum_add_distrib]
    rw [elevenGammaSix_sum_relative_indicator,
      elevenGammaSix_sum_relative_indicator,
      elevenGammaSix_sum_relative_indicator,
      elevenGammaSix_sum_relative_indicator,
      elevenGammaSix_sum_relative_indicator,
      elevenGammaSix_sum_relative_indicator,
      elevenGammaSix_sum_relative_indicator,
      elevenGammaSix_sum_relative_indicator,
      elevenGammaSix_sum_relative_indicator,
      elevenGammaSix_sum_relative_indicator,
      elevenGammaSix_sum_relative_indicator,
      elevenGammaSix_sum_relative_indicator,
      elevenGammaSix_sum_relative_indicator,
      elevenGammaSix_sum_relative_indicator]
    simp [elevenGammaSixTripleOneCensus]
  exact hsum.symm.trans hrow

/-- Canonical front data obtained by counting the relative block types.
Every slack is defined by truncated subtraction from its paper bound; the
lemmas below prove that the relevant minuend really is large enough. -/
noncomputable def elevenGammaSixFrontDataOfBlockSystem
    (S : BlockSystem Point Block) (D : Finset Point) :
    ElevenGammaSixFrontData where
  C := S.totalCircleCount
  N3 := elevenGammaSixFootprintCount S D 3
  N4 := elevenGammaSixFootprintCount S D 4
  N5 := elevenGammaSixFootprintCount S D 5
  sigma6 := 30 - elevenGammaSixLineCapacityUsed S D
  sigma10 := elevenGammaSixOrdinaryCircleIncidence S D - 15
  sigma17 := 52 - elevenGammaSixLineMelchiorUsed S D
  sigma63 := 28 - elevenGammaSixWeight S D
  sigmaL := 2 - elevenGammaSixLargeLineFootprintWeight S D
  c04 := elevenGammaSixRelativeCount S D .circle 0 4
  c12 := elevenGammaSixRelativeCount S D .circle 1 2
  c13 := elevenGammaSixRelativeCount S D .circle 1 3
  c14 := elevenGammaSixRelativeCount S D .circle 1 4
  c24 := elevenGammaSixRelativeCount S D .circle 2 4
  l03 := elevenGammaSixRelativeCount S D .line 0 3
  l04 := elevenGammaSixRelativeCount S D .line 0 4
  l05 := elevenGammaSixRelativeCount S D .line 0 5
  l12 := elevenGammaSixRelativeCount S D .line 1 2
  l13 := elevenGammaSixRelativeCount S D .line 1 3
  l14 := elevenGammaSixRelativeCount S D .line 1 4
  l15 := elevenGammaSixRelativeCount S D .line 1 5
  l22 := elevenGammaSixRelativeCount S D .line 2 2
  l23 := elevenGammaSixRelativeCount S D .line 2 3
  l24 := elevenGammaSixRelativeCount S D .line 2 4

/-- The exact scalar assembly of the front conditions from a materialized
relative census.

The six row hypotheses are named separately because each has a direct
double-counting constructor below (or is a one-line relative-row
specialization).  The only inequalities are the five genuine slack bounds;
none of the hypotheses states F1, F2, the `C = 38` residue, or the endpoint.
-/
theorem elevenGammaSixFrontConditions_of_materializedRows
    (S : BlockSystem Point Block) (D : Finset Point)
    (hpoint : Fintype.card Point = 11) (hD : D.card = 6)
    (hcircleTotal :
      S.totalCircleCount = elevenGammaSixCircleTotalCensus S D)
    (hN3 : elevenGammaSixFootprintCount S D 3 =
      elevenGammaSixFootprintThreeCensus S D)
    (hN4 : elevenGammaSixFootprintCount S D 4 =
      elevenGammaSixFootprintFourCensus S D)
    (hN5 : elevenGammaSixFootprintCount S D 5 =
      elevenGammaSixFootprintFiveCensus S D)
    (htripleOne : elevenGammaSixTripleOneCensus S D = 60)
    (htripleTwo : elevenGammaSixTripleTwoCensus S D = 75)
    (hlineCapacity : elevenGammaSixLineCapacityUsed S D <= 30)
    (hordinary : 15 <= elevenGammaSixOrdinaryCircleIncidence S D)
    (hmelchior : elevenGammaSixLineMelchiorUsed S D <= 52)
    (hweight : elevenGammaSixWeight S D <= 28)
    (hlargeLines : elevenGammaSixLargeLineFootprintWeight S D <= 2) :
    ElevenGammaSixFrontConditions
      (elevenGammaSixFrontDataOfBlockSystem S D) := by
  have hfootprint :=
    elevenGammaSix_footprint_row_of_blockSystem S D hpoint hD
  have hN4cap :=
    elevenGammaSix_footprintCount_le_one S D hpoint hD 4 (by omega)
  have hN5cap :=
    elevenGammaSix_footprintCount_le_one S D hpoint hD 5 (by omega)
  have hsigma6 :
      (30 - elevenGammaSixLineCapacityUsed S D) +
        elevenGammaSixLineCapacityUsed S D = 30 :=
    Nat.sub_add_cancel hlineCapacity
  have hsigma10 :
      (elevenGammaSixOrdinaryCircleIncidence S D - 15) + 15 =
        elevenGammaSixOrdinaryCircleIncidence S D :=
    Nat.sub_add_cancel hordinary
  have hsigma17 :
      (52 - elevenGammaSixLineMelchiorUsed S D) +
        elevenGammaSixLineMelchiorUsed S D = 52 :=
    Nat.sub_add_cancel hmelchior
  have hsigma63 :
      (28 - elevenGammaSixWeight S D) +
        elevenGammaSixWeight S D = 28 :=
    Nat.sub_add_cancel hweight
  have hsigmaL :
      (2 - elevenGammaSixLargeLineFootprintWeight S D) +
        elevenGammaSixLargeLineFootprintWeight S D = 2 :=
    Nat.sub_add_cancel hlargeLines
  simp only [elevenGammaSixCircleTotalCensus] at hcircleTotal
  simp only [elevenGammaSixFootprintThreeCensus] at hN3
  simp only [elevenGammaSixFootprintFourCensus] at hN4
  simp only [elevenGammaSixFootprintFiveCensus] at hN5
  simp only [elevenGammaSixTripleOneCensus] at htripleOne
  simp only [elevenGammaSixTripleTwoCensus] at htripleTwo
  simp only [elevenGammaSixLineCapacityUsed] at hsigma6
  simp only [elevenGammaSixOrdinaryCircleIncidence] at hsigma10
  simp only [elevenGammaSixLineMelchiorUsed] at hsigma17
  simp only [elevenGammaSixWeight] at hsigma63
  simp only [elevenGammaSixLargeLineFootprintWeight] at hsigmaL
  have hF1 :
      10 * (elevenGammaSixFrontDataOfBlockSystem S D).C =
        320 + 9 * (elevenGammaSixFrontDataOfBlockSystem S D).N3 +
          6 * (elevenGammaSixFrontDataOfBlockSystem S D).N4 +
          5 * (elevenGammaSixFrontDataOfBlockSystem S D).sigma6 +
          10 * (elevenGammaSixFrontDataOfBlockSystem S D).sigma63 +
          10 * (elevenGammaSixFrontDataOfBlockSystem S D).sigmaL +
          10 * (elevenGammaSixFrontDataOfBlockSystem S D).c12 +
          20 * (elevenGammaSixFrontDataOfBlockSystem S D).c24 +
          10 * (elevenGammaSixFrontDataOfBlockSystem S D).l04 +
          10 * (elevenGammaSixFrontDataOfBlockSystem S D).l05 +
          10 * (elevenGammaSixFrontDataOfBlockSystem S D).l12 +
          15 * (elevenGammaSixFrontDataOfBlockSystem S D).l13 +
          30 * (elevenGammaSixFrontDataOfBlockSystem S D).l14 +
          35 * (elevenGammaSixFrontDataOfBlockSystem S D).l15 +
          10 * (elevenGammaSixFrontDataOfBlockSystem S D).l24 := by
    simp only [elevenGammaSixFrontDataOfBlockSystem,
      elevenGammaSixLineCapacityUsed,
      elevenGammaSixWeight,
      elevenGammaSixLargeLineFootprintWeight]
    omega
  constructor
  · simpa only [elevenGammaSixFrontDataOfBlockSystem] using hfootprint
  · simpa only [elevenGammaSixFrontDataOfBlockSystem] using hN4cap
  · simpa only [elevenGammaSixFrontDataOfBlockSystem] using hN5cap
  · exact hF1
  · intro hprofileC
    simp only [elevenGammaSixFrontDataOfBlockSystem] at hprofileC
    simp only [elevenGammaSixFrontDataOfBlockSystem,
      elevenGammaSixLineCapacityUsed,
      elevenGammaSixLineMelchiorUsed,
      elevenGammaSixWeight,
      elevenGammaSixLargeLineFootprintWeight,
      elevenGammaSixOrdinaryCircleIncidence]
    omega
  · intro hC hprofN3 hprofN4 hprofN5
    have hzero :
        (elevenGammaSixFrontDataOfBlockSystem S D).sigma6 = 0 /\
        (elevenGammaSixFrontDataOfBlockSystem S D).sigma63 = 0 /\
        (elevenGammaSixFrontDataOfBlockSystem S D).sigmaL = 0 /\
        (elevenGammaSixFrontDataOfBlockSystem S D).c12 = 0 /\
        (elevenGammaSixFrontDataOfBlockSystem S D).c24 = 0 /\
        (elevenGammaSixFrontDataOfBlockSystem S D).l04 = 0 /\
        (elevenGammaSixFrontDataOfBlockSystem S D).l05 = 0 /\
        (elevenGammaSixFrontDataOfBlockSystem S D).l12 = 0 /\
        (elevenGammaSixFrontDataOfBlockSystem S D).l13 = 0 /\
        (elevenGammaSixFrontDataOfBlockSystem S D).l14 = 0 /\
        (elevenGammaSixFrontDataOfBlockSystem S D).l15 = 0 /\
        (elevenGammaSixFrontDataOfBlockSystem S D).l24 = 0 := by
      simp only [elevenGammaSixFrontDataOfBlockSystem] at hF1 hC hprofN3 hprofN4 hprofN5
      simp only [elevenGammaSixFrontDataOfBlockSystem]
      clear hcircleTotal hN3 hN4 hN5 htripleOne htripleTwo
        hlineCapacity hordinary hmelchior hweight hlargeLines
        hfootprint hN4cap hN5cap hsigma6 hsigma10 hsigma17 hsigma63 hsigmaL
      omega
    simp only [elevenGammaSixFrontDataOfBlockSystem,
      elevenGammaSixLineCapacityUsed,
      elevenGammaSixWeight,
      elevenGammaSixLargeLineFootprintWeight] at hC hprofN3 hprofN4 hprofN5 hzero
    simp only [elevenGammaSixFrontDataOfBlockSystem,
      elevenGammaSixLineCapacityUsed,
      elevenGammaSixLineMelchiorUsed,
      elevenGammaSixWeight,
      elevenGammaSixLargeLineFootprintWeight,
      elevenGammaSixOrdinaryCircleIncidence] at hF1
    simp only [elevenGammaSixFrontDataOfBlockSystem,
      elevenGammaSixLineCapacityUsed,
      elevenGammaSixLineMelchiorUsed,
      elevenGammaSixWeight,
      elevenGammaSixLargeLineFootprintWeight,
      elevenGammaSixOrdinaryCircleIncidence]
    rcases hzero with
      ⟨hz6, hz63, hzL, hzc12, hzc24, hzl04, hzl05, hzl12,
        hzl13, hzl14, hzl15, hzl24⟩
    have hresidue :
        3 * elevenGammaSixRelativeCount S D .circle 1 3 +
          6 * elevenGammaSixRelativeCount S D .circle 1 4 +
          2 * elevenGammaSixRelativeCount S D .line 2 2 +
          6 * elevenGammaSixRelativeCount S D .line 2 3 = 4 := by
      clear hcircleTotal hN3 hN4 htripleTwo hlineCapacity hordinary
        hmelchior hweight hlargeLines hfootprint hN4cap hN5cap
        hsigma6 hsigma10 hsigma17 hsigmaL hF1 hC hprofN3 hprofN4
      omega
    have hsigma10Boundary :
        (elevenGammaSixOrdinaryCircleIncidence S D - 15) +
          3 * elevenGammaSixRelativeCount S D .circle 1 3 = 1 := by
      clear htripleOne htripleTwo hlineCapacity hordinary hmelchior
        hweight hlargeLines hfootprint hN4cap hN5cap hsigma6 hsigma17 hF1
      simp only [elevenGammaSixOrdinaryCircleIncidence]
      omega
    have hsigma17Boundary :
        (52 - elevenGammaSixLineMelchiorUsed S D) +
          elevenGammaSixRelativeCount S D .line 2 2 = 1 := by
      clear hcircleTotal hN3 hN4 hN5 htripleOne htripleTwo hlineCapacity
        hordinary hmelchior hweight hlargeLines hfootprint hN4cap hN5cap
        hsigma10 hsigma63 hF1 hC hprofN3 hprofN4 hprofN5
      simp only [elevenGammaSixLineMelchiorUsed]
      omega
    exact ⟨hresidue, hsigma10Boundary, hsigma17Boundary⟩

/-- Configuration-free BlockSystem constructor for the complete arithmetic
front.  All relative census rows are derived above; only the four named
nonnegative-slack bounds remain inputs. -/
theorem elevenGammaSixFrontConditions_of_blockSystem
    (S : BlockSystem Point Block) (D : Finset Point) (gamma : Block)
    (hpoint : Fintype.card Point = 11) (hD : D.card = 6)
    (hgammaKind : S.kind gamma = .circle)
    (hgammaSupport : S.support gamma = D)
    (hcircleCap : forall b, S.kind b = .circle -> (S.support b).card <= 6)
    (hlineCap : forall b, S.kind b = .line -> (S.support b).card <= 6)
    (hordinary : 15 <= elevenGammaSixOrdinaryCircleIncidence S D)
    (hmelchior : elevenGammaSixLineMelchiorUsed S D <= 52)
    (hweight : elevenGammaSixWeight S D <= 28)
    (hlargeLines : elevenGammaSixLargeLineFootprintWeight S D <= 2) :
    ElevenGammaSixFrontConditions
      (elevenGammaSixFrontDataOfBlockSystem S D) := by
  apply elevenGammaSixFrontConditions_of_materializedRows
    S D hpoint hD
  · exact elevenGammaSix_circleTotalCensus_eq
      S D gamma hpoint hD hgammaKind hgammaSupport hcircleCap
  · exact elevenGammaSix_footprintThreeCensus_eq
      S D gamma hgammaSupport
  · exact elevenGammaSix_footprintFourCensus_eq
      S D gamma hgammaSupport
  · exact elevenGammaSix_footprintFiveCensus_eq
      S D gamma hgammaSupport hcircleCap hlineCap
  · exact elevenGammaSix_tripleOneCensus_eq_sixty
      S D gamma hpoint hD hgammaKind hgammaSupport hcircleCap hlineCap
  · exact elevenGammaSix_tripleTwoCensus_eq_seventy_five
      S D gamma hpoint hD hgammaKind hgammaSupport hcircleCap hlineCap
  · exact elevenGammaSixLineCapacityUsed_le_thirty
      S D gamma hpoint hD hgammaKind hgammaSupport hlineCap
  · exact hordinary
  · exact hmelchior
  · exact hweight
  · exact hlargeLines

end MaterializedRelativeCensus

/-- The additional counts needed after the common `C >= 39` front.

`W` is the outside-pair circle weight and `J` is the incidence number of
outsiders with original lines carrying a pair of points of `Gamma`.
Only `c21`, `c22`, and `l21` were absent from the front data and survive in
the final six-variable boundary tables. -/
structure ElevenGammaSixBoundaryData where
  front : ElevenGammaSixFrontData
  W : Nat
  J : Nat
  c05 : Nat
  c15 : Nat
  c21 : Nat
  c22 : Nat
  l21 : Nat

/-- Canonical boundary data obtained from the same relative census as the
front.  No row or inequality is assumed in this definition. -/
noncomputable def elevenGammaSixBoundaryDataOfBlockSystem
    {Point : Type u} {Block : Type*}
    [Fintype Point] [Fintype Block] [DecidableEq Point]
    (S : BlockSystem Point Block) (D : Finset Point) :
    ElevenGammaSixBoundaryData where
  front := elevenGammaSixFrontDataOfBlockSystem S D
  W := elevenGammaSixWeight S D
  J := elevenGammaSixLineIncidence S D
  c05 := elevenGammaSixRelativeCount S D .circle 0 5
  c15 := elevenGammaSixRelativeCount S D .circle 1 5
  c21 := elevenGammaSixRelativeCount S D .circle 2 1
  c22 := elevenGammaSixRelativeCount S D .circle 2 2
  l21 := elevenGammaSixRelativeCount S D .line 2 1

/-- The three possible generalized hosts of the five-outsider footprint. -/
inductive ElevenGammaSixFiveHost where
  /-- A five-point circle containing one selected point of `Gamma`. -/
  | meetingCircle
  /-- The maximal line through all five outsiders. -/
  | outsiderLine
  /-- A proper circle through all five outsiders and disjoint from `Gamma`. -/
  | outsiderCircle
  deriving DecidableEq

/-- The exact reduced rows at `C = 40` in footprint C.

The first four conjuncts are shared by all hosts.  They state `c22 = W`,
`J = l21 + 2 l22`, the line-pair capacity row, and the summed pivot row.
The final conjunction is exactly the appropriate host table. -/
def ElevenGammaSixFiveHostRows
    (d : ElevenGammaSixBoundaryData)
    (host : ElevenGammaSixFiveHost) : Prop :=
  d.c22 = d.W /\
  d.J = d.l21 + 2 * d.front.l22 /\
  d.front.l12 + d.l21 + 2 * d.front.l22 <= 15 /\
  25 <= 2 * d.front.c12 + d.c21 +
    2 * d.front.l12 + d.l21 /\
  match host with
  | .meetingCircle =>
      d.c15 = 1 /\
      d.front.c12 + d.c21 + d.c22 = 38 /\
      d.front.c12 + 2 * d.c22 + d.front.l12 +
        2 * d.front.l22 = 50 /\
      d.c21 + 2 * d.c22 + d.l21 + 2 * d.front.l22 = 75
  | .outsiderLine =>
      d.front.l05 = 1 /\
      d.front.l12 = 0 /\
      d.front.l22 = 0 /\
      d.front.c12 + d.c21 + d.c22 = 39 /\
      d.front.c12 + 2 * d.c22 = 60 /\
      d.c21 + 2 * d.c22 + d.l21 = 75
  | .outsiderCircle =>
      d.c05 = 1 /\
      d.front.c12 + d.c21 + d.c22 = 38 /\
      d.front.c12 + 2 * d.c22 + d.front.l12 +
        2 * d.front.l22 = 60 /\
      d.c21 + 2 * d.c22 + d.l21 + 2 * d.front.l22 = 75 /\
      15 <= 2 * d.front.c12 + d.c21

/-- The sole retained finite classification: at the `C = 40`, footprint-C
wall, the unique five-outsider owner has one of the three displayed host
types and satisfies its exact reduced rows.

Unlike the earlier boundary interface, this structure contains neither a
slack definition nor an S3/S4 numerical bound. -/
structure ElevenGammaSixHostClassification
    (d : ElevenGammaSixBoundaryData) : Prop where
  profileC_at_forty :
    d.front.C = 40 ->
    d.front.N3 = 0 -> d.front.N4 = 0 -> d.front.N5 = 1 ->
      exists host, ElevenGammaSixFiveHostRows d host

/-- All host rows are forced by the materialized census.  F2 removes the
six-line type `l15`; the five-footprint row then leaves exactly `c15`,
`l05`, or `c05`.  Kelly--Moser supplies only the independent row26 lower
bound. -/
theorem elevenGammaSixHostClassification_of_materializedCensus
    {Point : Type u} {Block : Type*}
    [Fintype Point] [Fintype Block] [DecidableEq Point]
    (S : BlockSystem Point Block) (D : Finset Point) (gamma : Block)
    (hpoint : Fintype.card Point = 11) (hD : D.card = 6)
    (hgammaKind : S.kind gamma = .circle)
    (hgammaSupport : S.support gamma = D)
    (hcircleCap : forall b, S.kind b = .circle -> (S.support b).card <= 6)
    (hlineCap : forall b, S.kind b = .line -> (S.support b).card <= 6)
    (hordinary : 15 <= elevenGammaSixOrdinaryCircleIncidence S D)
    (hkelly : 25 <= elevenGammaSixOutsiderThreeBlockIncidence S D)
    (hfront : ElevenGammaSixFrontConditions
      (elevenGammaSixFrontDataOfBlockSystem S D)) :
    ElevenGammaSixHostClassification
      (elevenGammaSixBoundaryDataOfBlockSystem S D) := by
  constructor
  intro hC hN3 hN4 hN5
  have hF2 := hfront.f2_of_profileC hN5
  have hCfront :
      (elevenGammaSixFrontDataOfBlockSystem S D).C = 40 := hC
  have hl15Front :
      (elevenGammaSixFrontDataOfBlockSystem S D).l15 = 0 := by
    omega
  have hl15 : elevenGammaSixRelativeCount S D .line 1 5 = 0 := by
    simpa only [elevenGammaSixFrontDataOfBlockSystem] using hl15Front
  clear hF2 hCfront hl15Front hfront
  have hcircleTotal := elevenGammaSix_circleTotalCensus_eq
    S D gamma hpoint hD hgammaKind hgammaSupport hcircleCap
  have hN3row := elevenGammaSix_footprintThreeCensus_eq
    S D gamma hgammaSupport
  have hN4row := elevenGammaSix_footprintFourCensus_eq
    S D gamma hgammaSupport
  have hN5row := elevenGammaSix_footprintFiveCensus_eq
    S D gamma hgammaSupport hcircleCap hlineCap
  have htripleOne := elevenGammaSix_tripleOneCensus_eq_sixty
    S D gamma hpoint hD hgammaKind hgammaSupport hcircleCap hlineCap
  have htripleTwo := elevenGammaSix_tripleTwoCensus_eq_seventy_five
    S D gamma hpoint hD hgammaKind hgammaSupport hcircleCap hlineCap
  have hcapacity := elevenGammaSixLineCapacityUsed_le_thirty
    S D gamma hpoint hD hgammaKind hgammaSupport hlineCap
  change S.totalCircleCount = 40 at hC
  change elevenGammaSixFootprintCount S D 3 = 0 at hN3
  change elevenGammaSixFootprintCount S D 4 = 0 at hN4
  change elevenGammaSixFootprintCount S D 5 = 1 at hN5
  have hthreeZero := hN3row.symm.trans hN3
  simp only [elevenGammaSixFootprintThreeCensus] at hthreeZero
  have hc03 : elevenGammaSixRelativeCount S D .circle 0 3 = 0 := by
    omega
  have hl03 : elevenGammaSixRelativeCount S D .line 0 3 = 0 := by
    omega
  have hc13 : elevenGammaSixRelativeCount S D .circle 1 3 = 0 := by
    omega
  have hl13 : elevenGammaSixRelativeCount S D .line 1 3 = 0 := by
    omega
  have hc23 : elevenGammaSixRelativeCount S D .circle 2 3 = 0 := by
    omega
  have hl23 : elevenGammaSixRelativeCount S D .line 2 3 = 0 := by
    omega
  clear hthreeZero hN3row hN3
  have hfourZero := hN4row.symm.trans hN4
  simp only [elevenGammaSixFootprintFourCensus] at hfourZero
  have hc04 : elevenGammaSixRelativeCount S D .circle 0 4 = 0 := by
    omega
  have hl04 : elevenGammaSixRelativeCount S D .line 0 4 = 0 := by
    omega
  have hc14 : elevenGammaSixRelativeCount S D .circle 1 4 = 0 := by
    omega
  have hl14 : elevenGammaSixRelativeCount S D .line 1 4 = 0 := by
    omega
  have hc24 : elevenGammaSixRelativeCount S D .circle 2 4 = 0 := by
    omega
  have hl24 : elevenGammaSixRelativeCount S D .line 2 4 = 0 := by
    omega
  clear hfourZero hN4row hN4
  have hcircle40 := hcircleTotal.symm.trans hC
  simp only [elevenGammaSixCircleTotalCensus, hc03, hc04, hc13,
    hc14, hc23, hc24, add_zero] at hcircle40
  have hfiveSum := hN5row.symm.trans hN5
  simp only [elevenGammaSixFootprintFiveCensus, hl15, add_zero]
    at hfiveSum
  simp only [elevenGammaSixTripleOneCensus, hc13, hl13, hc14,
    hl14, hl15, hc23, hl23, hc24, hl24, mul_zero, add_zero]
    at htripleOne
  simp only [elevenGammaSixTripleTwoCensus, hc23, hl23, hc24,
    hl24, mul_zero, add_zero] at htripleTwo
  simp only [elevenGammaSixLineCapacityUsed, hl13, hl14, hl15,
    hl23, hl24, mul_zero, add_zero] at hcapacity
  simp only [elevenGammaSixOrdinaryCircleIncidence, hc03, mul_zero,
    zero_add] at hordinary
  simp only [elevenGammaSixOutsiderThreeBlockIncidence, hc03, hl03,
    mul_zero, zero_add] at hkelly
  have hc22W :
      elevenGammaSixRelativeCount S D .circle 2 2 =
        elevenGammaSixWeight S D := by
    simp only [elevenGammaSixWeight, hc23, hc24, mul_zero, add_zero]
  have hJrow :
      elevenGammaSixLineIncidence S D =
        elevenGammaSixRelativeCount S D .line 2 1 +
          2 * elevenGammaSixRelativeCount S D .line 2 2 := by
    simp only [elevenGammaSixLineIncidence, hl23, hl24, mul_zero,
      add_zero]
  have hrow6 :
      elevenGammaSixRelativeCount S D .line 1 2 +
        elevenGammaSixRelativeCount S D .line 2 1 +
        2 * elevenGammaSixRelativeCount S D .line 2 2 <= 15 := by
    omega
  have hrow26 :
      25 <= 2 * elevenGammaSixRelativeCount S D .circle 1 2 +
        elevenGammaSixRelativeCount S D .circle 2 1 +
        2 * elevenGammaSixRelativeCount S D .line 1 2 +
        elevenGammaSixRelativeCount S D .line 2 1 := by
    omega
  have hordinarySmall :
      15 <= 2 * elevenGammaSixRelativeCount S D .circle 1 2 +
        elevenGammaSixRelativeCount S D .circle 2 1 := by
    omega
  clear hcircleTotal hN5row hcapacity hordinary hkelly hC hN5 hc03
    hl03 hc13 hl13 hc23 hl23 hc04 hl04 hc14 hl14 hc24 hl24 hl15
    hgammaKind hgammaSupport hcircleCap hlineCap
  have hcases :
      elevenGammaSixRelativeCount S D .circle 1 5 = 1 \/
      elevenGammaSixRelativeCount S D .line 0 5 = 1 \/
      elevenGammaSixRelativeCount S D .circle 0 5 = 1 := by
    omega
  rcases hcases with hc15 | hl05 | hc05
  · refine ⟨.meetingCircle, ?_⟩
    simp only [ElevenGammaSixFiveHostRows,
      elevenGammaSixBoundaryDataOfBlockSystem,
      elevenGammaSixFrontDataOfBlockSystem]
    refine ⟨hc22W, hJrow, hrow6, hrow26, hc15, ?_⟩
    constructor
    · omega
    constructor <;> omega
  · obtain ⟨hl12, hl22⟩ :=
      elevenGammaSix_l05_eq_one_forces_l12_l22_zero
        S D hpoint hD hl05
    refine ⟨.outsiderLine, ?_⟩
    simp only [ElevenGammaSixFiveHostRows,
      elevenGammaSixBoundaryDataOfBlockSystem,
      elevenGammaSixFrontDataOfBlockSystem]
    refine ⟨hc22W, hJrow, hrow6, hrow26, hl05, hl12, hl22, ?_⟩
    constructor
    · omega
    constructor <;> omega
  · refine ⟨.outsiderCircle, ?_⟩
    simp only [ElevenGammaSixFiveHostRows,
      elevenGammaSixBoundaryDataOfBlockSystem,
      elevenGammaSixFrontDataOfBlockSystem]
    refine ⟨hc22W, hJrow, hrow6, hrow26, hc05, ?_⟩
    constructor
    · omega
    constructor
    · omega
    constructor
    · omega
    · exact hordinarySmall

/-- Exact scalar rows used to reduce the two boundary values.

`sigma63_row`, `lineCapacity`, and `melchiorSlack` are merely the
definitions of the three slacks already present in the front certificate.
The last field is the exhaustive three-host reduction in footprint C at
`C = 40`; it contains no geometric exclusion. -/
structure ElevenGammaSixBoundaryRows
    (d : ElevenGammaSixBoundaryData) : Prop where
  sigma63_row : d.W + d.front.sigma63 = 28
  lineCapacity :
    d.front.sigma6 +
      2 * d.front.l12 + 3 * d.front.l13 +
      4 * d.front.l14 + 5 * d.front.l15 +
      2 * d.l21 + 4 * d.front.l22 +
      6 * d.front.l23 + 8 * d.front.l24 = 30
  melchiorSlack :
    d.front.sigma17 +
      3 * d.front.l03 + 7 * d.front.l04 + 12 * d.front.l05 +
      3 * d.front.l12 + 7 * d.front.l13 +
      12 * d.front.l14 + 18 * d.front.l15 +
      3 * d.l21 + 7 * d.front.l22 +
      12 * d.front.l23 + 18 * d.front.l24 = 52
  J_row :
    d.J = d.l21 + 2 * d.front.l22 +
      3 * d.front.l23 + 4 * d.front.l24
  profileC_at_forty :
    d.front.C = 40 ->
    d.front.N3 = 0 -> d.front.N4 = 0 -> d.front.N5 = 1 ->
      exists host, ElevenGammaSixFiveHostRows d host

/-- Once the three boundary scalar bounds are available, the
canonical truncated-subtraction definitions give every boundary row.
The only non-scalar input is the named three-host classification. -/
theorem elevenGammaSixBoundaryRows_of_materializedCensus
    {Point : Type u} {Block : Type*}
    [Fintype Point] [Fintype Block] [DecidableEq Point]
    (S : BlockSystem Point Block) (D : Finset Point)
    (hlineCapacity : elevenGammaSixLineCapacityUsed S D <= 30)
    (hmelchior : elevenGammaSixLineMelchiorUsed S D <= 52)
    (hweight : elevenGammaSixWeight S D <= 28)
    (hhosts : ElevenGammaSixHostClassification
      (elevenGammaSixBoundaryDataOfBlockSystem S D)) :
    ElevenGammaSixBoundaryRows
      (elevenGammaSixBoundaryDataOfBlockSystem S D) := by
  constructor
  · change elevenGammaSixWeight S D +
      (28 - elevenGammaSixWeight S D) = 28
    omega
  · simp only [elevenGammaSixBoundaryDataOfBlockSystem,
      elevenGammaSixFrontDataOfBlockSystem]
    simp only [elevenGammaSixLineCapacityUsed] at hlineCapacity ⊢
    omega
  · simp only [elevenGammaSixBoundaryDataOfBlockSystem,
      elevenGammaSixFrontDataOfBlockSystem]
    simp only [elevenGammaSixLineMelchiorUsed] at hmelchior ⊢
    omega
  · rfl
  · exact hhosts.profileC_at_forty

/-- Exactly the S3/S4 information consumed by the boundary certificate.

The weight bounds are guarded by the footprint or host that makes them
valid.  Thus, for example, the stronger `W <= 20` conclusion is available
only for a five-circle meeting `Gamma`; it is not silently imposed on the
two disjoint-host cases. -/
structure ElevenGammaSixEventBounds
    (d : ElevenGammaSixBoundaryData) : Prop where
  four_outsider_host_weight_le :
    d.front.N3 = 6 -> d.front.N4 = 1 -> d.front.N5 = 0 -> d.W <= 26
  five_outsider_host_meeting_weight_le :
    ElevenGammaSixFiveHostRows d .meetingCircle -> d.W <= 20
  five_outsider_host_disjoint_weight_le :
    forall host,
      (host = .outsiderLine \/ host = .outsiderCircle) ->
      ElevenGammaSixFiveHostRows d host -> d.W <= 26
  line_incidence_le_fourteen : d.J <= 14

/-- Semantic bridge between the scalar boundary data and a concrete
selected circle with five outsiders.

This witness contains no numerical bound.  It only identifies `W` and `J`
with the semantic six-conic quantities and turns the three scalar host tags
into the corresponding geometric host predicates. -/
structure ElevenGammaSixGeometricEventWitness
    {α : Type u} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (gamma : DeterminedCircle cfg)
    (X : Finset α) (d : ElevenGammaSixBoundaryData) : Prop where
  gamma_card : (circleTrace cfg gamma.1).card = 6
  outsider_card : X.card = 5
  disjoint : Disjoint (circleTrace cfg gamma.1) X
  weight_eq : d.W = sixConicWeight cfg gamma X
  line_incidence_eq : d.J = sixConicLineIncidence cfg gamma X
  four_host :
    d.front.N3 = 6 -> d.front.N4 = 1 -> d.front.N5 = 0 ->
      HasFourOutsiderHost cfg X
  meeting_host :
    ElevenGammaSixFiveHostRows d .meetingCircle ->
      HasFiveOutsiderHostMeeting cfg gamma X
  disjoint_host :
    forall host,
      (host = .outsiderLine \/ host = .outsiderCircle) ->
      ElevenGammaSixFiveHostRows d host ->
        HasFiveOutsiderHostDisjoint cfg gamma X

/-- Canonical semantic witness for the relative census of a selected
six-circle.  Host geometry is recovered from the marker count stored in the
corresponding host row. -/
theorem elevenGammaSixGeometricEventWitness_of_configuration
    {α : Type u} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (gamma : DeterminedCircle cfg)
    (hpoint : Fintype.card α = 11)
    (hgamma : (circleTrace cfg gamma.1).card = 6)
    (hcircleCap : forall c : DeterminedCircle cfg,
      (circleTrace cfg c.1).card <= 6)
    (hlineCap : forall L : DeterminedLine cfg,
      (lineSupport cfg L).card <= 6) :
    ElevenGammaSixGeometricEventWitness cfg gamma
      (Finset.univ \ circleTrace cfg gamma.1)
      (elevenGammaSixBoundaryDataOfBlockSystem
        (blockSystem cfg) (circleTrace cfg gamma.1)) := by
  let S := blockSystem cfg
  let D : Finset α := circleTrace cfg gamma.1
  let X : Finset α := Finset.univ \ D
  constructor
  · exact hgamma
  · simp [Finset.card_sdiff_of_subset
      (Finset.subset_univ (circleTrace cfg gamma.1)), hpoint, hgamma]
  · simp [Finset.disjoint_left]
  · simp only [elevenGammaSixBoundaryDataOfBlockSystem]
    exact elevenGammaSixWeight_eq_sixConicWeight
      cfg gamma hpoint hgamma hcircleCap
  · simp only [elevenGammaSixBoundaryDataOfBlockSystem]
    exact elevenGammaSixLineIncidence_eq_sixConicLineIncidence
      cfg gamma hpoint hgamma hlineCap
  · intro _hN3 hN4 _hN5
    simp only [elevenGammaSixBoundaryDataOfBlockSystem,
      elevenGammaSixFrontDataOfBlockSystem] at hN4
    obtain ⟨b, hb⟩ :=
      elevenGammaSix_exists_four_outsider_block S D hN4
    exact ⟨b, by simpa [S, D, X, geometricBlockSupport] using hb⟩
  · intro hhost
    have hc15 := hhost.2.2.2.2.1
    simp only [elevenGammaSixBoundaryDataOfBlockSystem] at hc15
    obtain ⟨b, _hbKind, hbInside, hbOutside⟩ :=
      elevenGammaSix_exists_relative_block_of_count_eq_one
        S D .circle 1 5 hc15
    refine ⟨b, ?_, ?_⟩
    · change X ⊆ S.support b
      exact elevenGammaSix_complement_subset_support_of_outside_five
        S D hpoint hgamma b hbOutside
    · change ¬Disjoint (S.support b) D
      exact elevenGammaSix_support_not_disjoint_of_inside_pos
        S D b (by omega)
  · intro host hdisjointHost hhost
    rcases hdisjointHost with rfl | rfl
    · have hl05 := hhost.2.2.2.2.1
      simp only [elevenGammaSixBoundaryDataOfBlockSystem,
        elevenGammaSixFrontDataOfBlockSystem] at hl05
      obtain ⟨b, _hbKind, hbInside, hbOutside⟩ :=
        elevenGammaSix_exists_relative_block_of_count_eq_one
          S D .line 0 5 hl05
      refine ⟨b, ?_, ?_⟩
      · change X ⊆ S.support b
        exact elevenGammaSix_complement_subset_support_of_outside_five
          S D hpoint hgamma b hbOutside
      · change Disjoint (S.support b) D
        exact elevenGammaSix_support_disjoint_of_inside_zero
          S D b hbInside
    · have hc05 := hhost.2.2.2.2.1
      simp only [elevenGammaSixBoundaryDataOfBlockSystem] at hc05
      obtain ⟨b, _hbKind, hbInside, hbOutside⟩ :=
        elevenGammaSix_exists_relative_block_of_count_eq_one
          S D .circle 0 5 hc05
      refine ⟨b, ?_, ?_⟩
      · change X ⊆ S.support b
        exact elevenGammaSix_complement_subset_support_of_outside_five
          S D hpoint hgamma b hbOutside
      · change Disjoint (S.support b) D
        exact elevenGammaSix_support_disjoint_of_inside_zero
          S D b hbInside

/-- The canonical outsider-circle host row is impossible using the
field-free global `J ≤ 14`, Kelly--Moser, and the even-arrangement principle. -/
theorem elevenGammaSix_outsiderCircle_localized_even
    {α : Type u} [Fintype α] [DecidableEq α]
    (EvenArr : RealPlaneEvenArrangementPrinciple.{u})
    (Kelly : RealPlaneKellyMoserPrinciple.{u})
    (cfg : Configuration α) (hadm : Admissible cfg)
    (hpoint : Fintype.card α = 11)
    (gamma : DeterminedCircle cfg)
    (hgamma : (circleTrace cfg gamma.1).card = 6)
    (hcircleCap : ∀ c : DeterminedCircle cfg,
      (circleTrace cfg c.1).card ≤ 6)
    (hlineCap : ∀ L : DeterminedLine cfg,
      (lineSupport cfg L).card ≤ 6)
    (d : ElevenGammaSixBoundaryData)
    (hcanonical : d = elevenGammaSixBoundaryDataOfBlockSystem
      (blockSystem cfg) (circleTrace cfg gamma.1))
    (hgeo : ElevenGammaSixGeometricEventWitness cfg gamma
      (Finset.univ \ circleTrace cfg gamma.1) d)
    (hhost : ElevenGammaSixFiveHostRows d .outsiderCircle)
    (hW : d.W ≤ 26) : False := by
  classical
  subst d
  let S := blockSystem cfg
  let D : Finset α := circleTrace cfg gamma.1
  let X : Finset α := Finset.univ \ D
  have hJ :
      (elevenGammaSixBoundaryDataOfBlockSystem S D).J ≤ 14 := by
    rw [hgeo.line_incidence_eq]
    exact sixConic_line_incidence_le_fourteen
      cfg gamma hgeo.gamma_card X hgeo.outsider_card hgeo.disjoint
  change elevenGammaSixLineIncidence S D ≤ 14 at hJ
  change elevenGammaSixWeight S D ≤ 26 at hW
  simp only [ElevenGammaSixFiveHostRows,
    elevenGammaSixBoundaryDataOfBlockSystem,
    elevenGammaSixFrontDataOfBlockSystem] at hhost
  rcases hhost with
    ⟨hc22, hJrow, hrow6, hrow26, hc05,
      hcircles, hmixedOne, hmixedTwo, hsigma10⟩
  dsimp only [S, D] at hJ hW
  have hW26 : elevenGammaSixWeight S D = 26 := by
    dsimp only [S, D]
    omega
  have hJ14 : elevenGammaSixLineIncidence S D = 14 := by
    dsimp only [S, D]
    omega
  have hc05' : elevenGammaSixRelativeCount S D .circle 0 5 = 1 := by
    simpa only [S, D] using hc05
  obtain ⟨b, _hbKind, hbInside, hbOutside⟩ :=
    elevenGammaSix_exists_relative_block_of_count_eq_one
      S D .circle 0 5 hc05'
  have hbFootprint :
      b ∈ Finset.univ.filter (fun B => elevenGammaSixOutside S D B = 5) := by
    simp [hbOutside]
  have hN5pos : 0 < elevenGammaSixFootprintCount S D 5 := by
    rw [elevenGammaSixFootprintCount]
    exact Finset.card_pos.mpr ⟨b, hbFootprint⟩
  have hfootprint := elevenGammaSix_footprint_row_of_blockSystem
    S D hpoint hgamma
  have hN3 : elevenGammaSixFootprintCount S D 3 = 0 := by omega
  have hzero := elevenGammaSix_footprintThreeCensus_eq
    S D (Sum.inr gamma : GeometricBlock cfg) rfl
  have hthreeZero := hzero.symm.trans hN3
  simp only [elevenGammaSixFootprintThreeCensus] at hthreeZero
  have hthreeIncidence :
      elevenGammaSixOutsiderThreeBlockIncidence S D = 27 := by
    simp only [elevenGammaSixOutsiderThreeBlockIncidence]
    dsimp only [S, D] at hW26 hJ14 hthreeZero ⊢
    omega
  have hsum :=
    elevenGammaSixTotalOutsiderThreeBlockIncidence_eq_sum_complement S D
  have hgrouped :=
    elevenGammaSixTotalOutsiderThreeBlockIncidence_eq_grouped
      S D (Sum.inr gamma : GeometricBlock cfg) hgamma rfl
  have hthreeSum : (∑ p ∈ X, S.blockDegree 3 p) = 27 := by
    rw [← hsum, hgrouped]
    exact hthreeIncidence
  let H : GeometricBlock cfg := b
  have hXsub : X ⊆ S.support b :=
    elevenGammaSix_complement_subset_support_of_outside_five
      S D hpoint hgamma b hbOutside
  have hbCard : (S.support b).card = 5 := by
    have hsplit := elevenGammaSixInside_add_outside S D b
    omega
  have hH : geometricBlockSupport cfg H = X := by
    change S.support b = X
    exact (Finset.eq_of_subset_of_card_le hXsub (by
      have hXcard : X.card = 5 := by
        simp [X, D, Finset.card_sdiff_of_subset (Finset.subset_univ D),
          hpoint, hgamma]
      rw [hbCard, hXcard])).symm
  have hblockCap : BlockSizeCap S 6 := by
    intro B _hB
    cases B with
    | inl L => exact hlineCap L
    | inr c => exact hcircleCap c
  exact elevenGammaSix_localized_even_contradiction
    EvenArr Kelly cfg hadm hpoint gamma hgamma X hgeo.outsider_card
      hgeo.disjoint H hH hblockCap hthreeSum

/-- The field-free six-conic geometry supplies exactly the scalar S3/S4
bounds required by the eleven-point boundary certificate. -/
theorem elevenGammaSixEventBounds_of_geometry
    {α : Type u} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (gamma : DeterminedCircle cfg)
    (X : Finset α) (d : ElevenGammaSixBoundaryData)
    (hblockCap : ∀ H : GeometricBlock cfg,
      (geometricBlockSupport cfg H).card ≤ 6)
    (hgeo : ElevenGammaSixGeometricEventWitness cfg gamma X d) :
    ElevenGammaSixEventBounds d := by
  constructor
  · intro hN3 hN4 hN5
    rw [hgeo.weight_eq]
    exact sixConic_four_outsider_host_weight_le
      cfg gamma hgeo.gamma_card X hgeo.outsider_card hgeo.disjoint
        (hgeo.four_host hN3 hN4 hN5)
  · intro hhost
    rw [hgeo.weight_eq]
    exact sixConic_five_outsider_host_meeting_weight_le_of_blockCap
      cfg gamma hgeo.gamma_card X hgeo.outsider_card hgeo.disjoint
        hblockCap (hgeo.meeting_host hhost)
  · intro host hdisjointHost hhost
    rw [hgeo.weight_eq]
    exact sixConic_five_outsider_host_disjoint_weight_le
      cfg gamma hgeo.gamma_card X hgeo.outsider_card hgeo.disjoint
        (hgeo.disjoint_host host hdisjointHost hhost)
  · rw [hgeo.line_incidence_eq]
    exact sixConic_line_incidence_le_fourteen
      cfg gamma hgeo.gamma_card X hgeo.outsider_card hgeo.disjoint

/-- Footprint B cannot survive at `C = 39`: F1 forces `W >= 27`, while
the unique-four-host clause of S3 gives `W <= 26`. -/
theorem elevenGammaSix_profileB_thirty_nine_impossible
    (d : ElevenGammaSixBoundaryData)
    (hfront : ElevenGammaSixFrontConditions d.front)
    (hrows : ElevenGammaSixBoundaryRows d)
    (hevents : ElevenGammaSixEventBounds d)
    (hC : d.front.C = 39)
    (hN3 : d.front.N3 = 6)
    (hN4 : d.front.N4 = 1)
    (hN5 : d.front.N5 = 0) : False := by
  have hW : d.W <= 26 :=
    hevents.four_outsider_host_weight_le hN3 hN4 hN5
  have hF1 := hfront.f1
  have hsigma63 := hrows.sigma63_row
  omega

/-- At `C = 40` in footprint B, F1 and `W <= 26` make every boundary
residual vanish.  The tight line-capacity row then gives `J = 15`, contrary
to the global S4 bound. -/
theorem elevenGammaSix_profileB_forty_impossible
    (d : ElevenGammaSixBoundaryData)
    (hfront : ElevenGammaSixFrontConditions d.front)
    (hrows : ElevenGammaSixBoundaryRows d)
    (hevents : ElevenGammaSixEventBounds d)
    (hC : d.front.C = 40)
    (hN3 : d.front.N3 = 6)
    (hN4 : d.front.N4 = 1)
    (hN5 : d.front.N5 = 0) : False := by
  have hW : d.W <= 26 :=
    hevents.four_outsider_host_weight_le hN3 hN4 hN5
  have hF1 := hfront.f1
  have hsigma63 := hrows.sigma63_row
  have hcapacity := hrows.lineCapacity
  have hJrow := hrows.J_row
  have hJ := hevents.line_incidence_le_fourteen
  omega

/-- Footprint C at `C = 39` is already arithmetically impossible.  F2
gives `sigma17 + l22 = 1`; the tight capacity and Melchior slack definitions
would then require `12 l05 = 6`. -/
theorem elevenGammaSix_profileC_thirty_nine_impossible
    (d : ElevenGammaSixBoundaryData)
    (hfront : ElevenGammaSixFrontConditions d.front)
    (hrows : ElevenGammaSixBoundaryRows d)
    (hC : d.front.C = 39)
    (hN5 : d.front.N5 = 1) : False := by
  have hF2 := hfront.f2_of_profileC hN5
  have hcapacity := hrows.lineCapacity
  have hmelchior := hrows.melchiorSlack
  omega

/-- The meeting-circle host at `C = 40` forces `W >= 22` from rows 6 and
26, contradicting the meeting-host clause `W <= 20` of S3. -/
theorem elevenGammaSix_meeting_host_impossible
    (d : ElevenGammaSixBoundaryData)
    (hevents : ElevenGammaSixEventBounds d)
    (hhost : ElevenGammaSixFiveHostRows d .meetingCircle) : False := by
  have hW := hevents.five_outsider_host_meeting_weight_le hhost
  simp only [ElevenGammaSixFiveHostRows] at hhost
  rcases hhost with
    ⟨hc22, _hJ, hrow6, hrow26, _hc15,
      hcircles, hmixedOne, hmixedTwo⟩
  omega

/-- The outsider five-line host gives `J = 96 - 3 W`.  The disjoint-host
weight bound `W <= 26` therefore contradicts the global `J <= 14` bound. -/
theorem elevenGammaSix_outsider_line_host_impossible
    (d : ElevenGammaSixBoundaryData)
    (hevents : ElevenGammaSixEventBounds d)
    (hhost : ElevenGammaSixFiveHostRows d .outsiderLine) : False := by
  have hW := hevents.five_outsider_host_disjoint_weight_le
    .outsiderLine (Or.inl rfl) hhost
  have hJ := hevents.line_incidence_le_fourteen
  simp only [ElevenGammaSixFiveHostRows] at hhost
  rcases hhost with
    ⟨hc22, hJrow, hrow6, hrow26, _hl05, hd, hf,
      hcircles, hmixedOne, hmixedTwo⟩
  omega

/-- The outsider five-circle host forces the integral equalities `W = 26`
and `J = 14`.  The canonical geometry, Kelly--Moser, and the even-arrangement
principle then give the localized contradiction. -/
theorem elevenGammaSix_outsider_circle_host_impossible
    {alpha : Type u} [Fintype alpha] [DecidableEq alpha]
    (EvenArr : RealPlaneEvenArrangementPrinciple.{u})
    (Kelly : RealPlaneKellyMoserPrinciple.{u})
    (cfg : Configuration alpha) (hadm : Admissible cfg)
    (hpoint : Fintype.card alpha = 11)
    (gamma : DeterminedCircle cfg)
    (hgamma : (circleTrace cfg gamma.1).card = 6)
    (hcircleCap : forall c : DeterminedCircle cfg,
      (circleTrace cfg c.1).card <= 6)
    (hlineCap : forall L : DeterminedLine cfg,
      (lineSupport cfg L).card <= 6)
    (d : ElevenGammaSixBoundaryData)
    (hcanonical : d = elevenGammaSixBoundaryDataOfBlockSystem
      (blockSystem cfg) (circleTrace cfg gamma.1))
    (hgeo : ElevenGammaSixGeometricEventWitness cfg gamma
      (Finset.univ \ circleTrace cfg gamma.1) d)
    (hevents : ElevenGammaSixEventBounds d)
    (hhost : ElevenGammaSixFiveHostRows d .outsiderCircle) : False := by
  have hW := hevents.five_outsider_host_disjoint_weight_le
    .outsiderCircle (Or.inr rfl) hhost
  exact elevenGammaSix_outsiderCircle_localized_even
    EvenArr Kelly cfg hadm hpoint gamma hgamma hcircleCap hlineCap
      d hcanonical hgeo hhost hW

/-- Footprint C at `C = 40` has exactly three possible hosts, and the
preceding three certificates exclude all of them. -/
theorem elevenGammaSix_profileC_forty_impossible
    {alpha : Type u} [Fintype alpha] [DecidableEq alpha]
    (EvenArr : RealPlaneEvenArrangementPrinciple.{u})
    (Kelly : RealPlaneKellyMoserPrinciple.{u})
    (cfg : Configuration alpha) (hadm : Admissible cfg)
    (hpoint : Fintype.card alpha = 11)
    (gamma : DeterminedCircle cfg)
    (hgamma : (circleTrace cfg gamma.1).card = 6)
    (hcircleCap : forall c : DeterminedCircle cfg,
      (circleTrace cfg c.1).card <= 6)
    (hlineCap : forall L : DeterminedLine cfg,
      (lineSupport cfg L).card <= 6)
    (d : ElevenGammaSixBoundaryData)
    (hcanonical : d = elevenGammaSixBoundaryDataOfBlockSystem
      (blockSystem cfg) (circleTrace cfg gamma.1))
    (hgeo : ElevenGammaSixGeometricEventWitness cfg gamma
      (Finset.univ \ circleTrace cfg gamma.1) d)
    (hrows : ElevenGammaSixBoundaryRows d)
    (hevents : ElevenGammaSixEventBounds d)
    (hC : d.front.C = 40)
    (hN3 : d.front.N3 = 0)
    (hN4 : d.front.N4 = 0)
    (hN5 : d.front.N5 = 1) : False := by
  obtain ⟨host, hhost⟩ := hrows.profileC_at_forty hC hN3 hN4 hN5
  cases host with
  | meetingCircle =>
      exact elevenGammaSix_meeting_host_impossible d hevents hhost
  | outsiderLine =>
      exact elevenGammaSix_outsider_line_host_impossible d hevents hhost
  | outsiderCircle =>
      exact elevenGammaSix_outsider_circle_host_impossible
        EvenArr Kelly cfg hadm hpoint gamma hgamma hcircleCap hlineCap
          d hcanonical hgeo hevents hhost

/-- Full solver-free boundary certificate for the selected-six-circle
branch at eleven points: the exact front and boundary rows, together with
the reusable S3/S4 event bounds, imply `C >= 41`. -/
theorem elevenGammaSix_circleCount_ge_forty_one
    {alpha : Type u} [Fintype alpha] [DecidableEq alpha]
    (EvenArr : RealPlaneEvenArrangementPrinciple.{u})
    (Kelly : RealPlaneKellyMoserPrinciple.{u})
    (cfg : Configuration alpha) (hadm : Admissible cfg)
    (hpoint : Fintype.card alpha = 11)
    (gamma : DeterminedCircle cfg)
    (hgamma : (circleTrace cfg gamma.1).card = 6)
    (hcircleCap : forall c : DeterminedCircle cfg,
      (circleTrace cfg c.1).card <= 6)
    (hlineCap : forall L : DeterminedLine cfg,
      (lineSupport cfg L).card <= 6)
    (d : ElevenGammaSixBoundaryData)
    (hcanonical : d = elevenGammaSixBoundaryDataOfBlockSystem
      (blockSystem cfg) (circleTrace cfg gamma.1))
    (hgeo : ElevenGammaSixGeometricEventWitness cfg gamma
      (Finset.univ \ circleTrace cfg gamma.1) d)
    (hfront : ElevenGammaSixFrontConditions d.front)
    (hrows : ElevenGammaSixBoundaryRows d)
    (hevents : ElevenGammaSixEventBounds d) :
    41 <= d.front.C := by
  have hC39 : 39 <= d.front.C :=
    elevenGammaSix_front_circleCount_ge_thirty_nine d.front hfront
  by_contra hnot
  have hCle : d.front.C <= 40 := by omega
  have hprofile := elevenGammaSix_footprint_profiles
    d.front.N3 d.front.N4 d.front.N5
    hfront.footprint_row hfront.N4_le_one hfront.N5_le_one
  rcases hprofile with hA | hB | hC
  · rcases hA with ⟨hN3, hN4, _hN5⟩
    have hfortyOne :=
      elevenGammaSix_profileA_circleCount_ge_forty_one
        d.front hfront.f1 hN3 hN4
    omega
  · rcases hB with ⟨hN3, hN4, hN5⟩
    by_cases hcount : d.front.C = 39
    · exact elevenGammaSix_profileB_thirty_nine_impossible
        d hfront hrows hevents hcount hN3 hN4 hN5
    · have hcount40 : d.front.C = 40 := by omega
      exact elevenGammaSix_profileB_forty_impossible
        d hfront hrows hevents hcount40 hN3 hN4 hN5
  · rcases hC with ⟨hN3, hN4, hN5⟩
    by_cases hcount : d.front.C = 39
    · exact elevenGammaSix_profileC_thirty_nine_impossible
        d hfront hrows hcount hN5
    · have hcount40 : d.front.C = 40 := by omega
      exact elevenGammaSix_profileC_forty_impossible
        EvenArr Kelly cfg hadm hpoint gamma hgamma hcircleCap hlineCap
          d hcanonical hgeo hrows hevents hcount40 hN3 hN4 hN5

end Erdos506.V1
