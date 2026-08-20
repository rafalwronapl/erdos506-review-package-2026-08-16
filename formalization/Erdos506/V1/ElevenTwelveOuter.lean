import Erdos506.V1.DirectKelly
import Erdos506.V1.FiniteCaps

/-!
# The deletion-free outer router at eleven and twelve points

This file formalizes the manuscript's `T/O/G/K` and `T/O/G/P`
certificates.  Under the contradictory circle-count bounds, the rich-block
pencils first cap lines and proper circles.  The global certificates then
exclude circle caps three and four, leaving a proper circle with five or six
selected points.

Kelly--Moser remains an explicit parameter.  Its direct restored-pivot form
supplies the ordinary line/circle aggregate used by the outer certificates.
This module adds no geometric axiom or endpoint-specific callback.
-/

namespace Erdos506.V1

open Erdos506.Block
open Erdos506.Block.BlockSystem
open Erdos506.Incidence
open Erdos506.V4
open scoped BigOperators

universe u

private theorem blockCount_eq_zero_of_cap
    {Point Block : Type*} [Fintype Point] [Fintype Block]
    [DecidableEq Point]
    (S : BlockSystem Point Block) {M s : ℕ}
    (hcap : BlockSizeCap S M) (hthree : 3 ≤ s) (hlarge : M < s) :
    S.blockCount s = 0 := by
  classical
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro b hb
  have hsize := S.mem_blocksOfSize.mp hb
  have hle := hcap b (by omega)
  omega

private theorem lineCount_eq_zero_of_cap
    {Point Block : Type*} [Fintype Point] [Fintype Block]
    [DecidableEq Point]
    (S : BlockSystem Point Block) {M s : ℕ}
    (hcap : BlockSizeCap S M) (hthree : 3 ≤ s) (hlarge : M < s) :
    S.lineCount s = 0 := by
  classical
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro b hb
  have hspec := S.mem_blocksOfKindSize.mp hb
  have hle := hcap b (by rw [hspec.2]; exact hthree)
  omega

private theorem circleCount_eq_zero_of_kind_cap
    {Point Block : Type*} [Fintype Point] [Fintype Block]
    [DecidableEq Point]
    (S : BlockSystem Point Block) {M s : ℕ}
    (hcap : ∀ b : Block, S.kind b = .circle → (S.support b).card ≤ M)
    (hlarge : M < s) :
    S.circleCount s = 0 := by
  classical
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro b hb
  have hspec := S.mem_blocksOfKindSize.mp hb
  have hle := hcap b hspec.1
  omega

/-- Separate caps on determined lines and proper circles give a cap on the
tagged geometric block system. -/
theorem blockSizeCap_of_line_circle_caps
    {α : Type u} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (M : ℕ)
    (hline : ∀ L : DeterminedLine cfg, (lineSupport cfg L).card ≤ M)
    (hcircle : ∀ c : DeterminedCircle cfg,
      (circleTrace cfg c.1).card ≤ M) :
    BlockSizeCap (blockSystem cfg) M := by
  intro b _hthree
  cases b with
  | inl L =>
      simpa [blockSystem, geometricBlockSystem, geometricBlockSupport] using
        hline L
  | inr c =>
      simpa [blockSystem, geometricBlockSystem, geometricBlockSupport] using
        hcircle c

private theorem circle_kind_cap_of_trace_cap
    {α : Type u} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (M : ℕ)
    (hcircle : ∀ c : DeterminedCircle cfg,
      (circleTrace cfg c.1).card ≤ M) :
    ∀ b, (blockSystem cfg).kind b = .circle →
      ((blockSystem cfg).support b).card ≤ M := by
  intro b hb
  cases b with
  | inl L => cases hb
  | inr c =>
      simpa [blockSystem, geometricBlockSystem, geometricBlockKind,
        geometricBlockSupport] using hcircle c

private theorem globalLineRow_eq_weighted_lineCount
    {Point Block : Type*} [Fintype Point] [Fintype Block]
    [DecidableEq Point] (S : BlockSystem Point Block) :
    S.globalLineRow =
      ∑ s ∈ Finset.range (Fintype.card Point + 1),
        ((if 3 ≤ s then Nat.choose s 2 + s - 3 else 0 : ℕ) : ℤ) *
          (S.lineCount s : ℤ) := by
  classical
  let w : ℕ → ℕ := fun s =>
    if 3 ≤ s then Nat.choose s 2 + s - 3 else 0
  have hgroup := S.sum_kindCount_weight .line w
  have hsubtype :
      (∑ b : LineBlock S, w (S.support b.1).card) =
        ∑ b ∈ S.blocksOfKind .line, w (S.support b).card := by
    symm
    simpa [blocksOfKind] using
      (Finset.sum_subtype (S.blocksOfKind .line)
        (fun b => by simp [blocksOfKind])
        (fun b => w (S.support b).card))
  have hpoint (b : LineBlock S) :
      (if 3 ≤ (S.support b.1).card then
          (Nat.choose (S.support b.1).card 2 : ℤ) +
            ((S.support b.1).card : ℤ) - 3
        else 0) = (w (S.support b.1).card : ℤ) := by
    dsimp only [w]
    split_ifs with hthree
    · omega
    · rfl
  have hglobal :
      S.globalLineRow =
        ((∑ b ∈ S.blocksOfKind .line,
          w (S.support b).card : ℕ) : ℤ) := by
    unfold BlockSystem.globalLineRow
    calc
      (∑ b : LineBlock S,
          if 3 ≤ (S.support b.1).card then
            (Nat.choose (S.support b.1).card 2 : ℤ) +
              ((S.support b.1).card : ℤ) - 3
          else 0) =
          ∑ b : LineBlock S, (w (S.support b.1).card : ℤ) := by
            apply Fintype.sum_congr
            exact hpoint
      _ = ((∑ b : LineBlock S, w (S.support b.1).card : ℕ) : ℤ) := by
            norm_num
      _ = ((∑ b ∈ S.blocksOfKind .line,
          w (S.support b).card : ℕ) : ℤ) := by rw [hsubtype]
  rw [hglobal]
  rw [← hgroup]
  norm_num [w, BlockSystem.lineCount]

private theorem globalLineRow_eq_eleven
    {Point Block : Type*} [Fintype Point] [Fintype Block]
    [DecidableEq Point]
    (S : BlockSystem Point Block) (hcard : Fintype.card Point = 11)
    (hcap : BlockSizeCap S 5) :
    S.globalLineRow =
      3 * (S.lineCount 3 : ℤ) + 7 * (S.lineCount 4 : ℤ) +
        12 * (S.lineCount 5 : ℤ) := by
  have hl6 : S.lineCount 6 = 0 :=
    lineCount_eq_zero_of_cap S hcap (by omega) (by omega)
  have hl7 : S.lineCount 7 = 0 :=
    lineCount_eq_zero_of_cap S hcap (by omega) (by omega)
  have hl8 : S.lineCount 8 = 0 :=
    lineCount_eq_zero_of_cap S hcap (by omega) (by omega)
  have hl9 : S.lineCount 9 = 0 :=
    lineCount_eq_zero_of_cap S hcap (by omega) (by omega)
  have hl10 : S.lineCount 10 = 0 :=
    lineCount_eq_zero_of_cap S hcap (by omega) (by omega)
  have hl11 : S.lineCount 11 = 0 :=
    lineCount_eq_zero_of_cap S hcap (by omega) (by omega)
  rw [globalLineRow_eq_weighted_lineCount, hcard]
  norm_num [Finset.sum_range_succ, Nat.choose,
    hl6, hl7, hl8, hl9, hl10, hl11]

private theorem globalLineRow_eq_twelve
    {Point Block : Type*} [Fintype Point] [Fintype Block]
    [DecidableEq Point]
    (S : BlockSystem Point Block) (hcard : Fintype.card Point = 12)
    (hcap : BlockSizeCap S 6) :
    S.globalLineRow =
      3 * (S.lineCount 3 : ℤ) + 7 * (S.lineCount 4 : ℤ) +
        12 * (S.lineCount 5 : ℤ) + 18 * (S.lineCount 6 : ℤ) := by
  have hl7 : S.lineCount 7 = 0 :=
    lineCount_eq_zero_of_cap S hcap (by omega) (by omega)
  have hl8 : S.lineCount 8 = 0 :=
    lineCount_eq_zero_of_cap S hcap (by omega) (by omega)
  have hl9 : S.lineCount 9 = 0 :=
    lineCount_eq_zero_of_cap S hcap (by omega) (by omega)
  have hl10 : S.lineCount 10 = 0 :=
    lineCount_eq_zero_of_cap S hcap (by omega) (by omega)
  have hl11 : S.lineCount 11 = 0 :=
    lineCount_eq_zero_of_cap S hcap (by omega) (by omega)
  have hl12 : S.lineCount 12 = 0 :=
    lineCount_eq_zero_of_cap S hcap (by omega) (by omega)
  rw [globalLineRow_eq_weighted_lineCount, hcard]
  norm_num [Finset.sum_range_succ, Nat.choose,
    hl7, hl8, hl9, hl10, hl11, hl12]

/-- The summed Kelly--Moser row `K` at eleven points. -/
theorem fifty_five_le_three_blockCount_three_of_card_eleven
    {α : Type u} [Fintype α] [DecidableEq α]
    (Kelly : RealPlaneKellyMoserPrinciple.{u})
    (cfg : Configuration α) (hadm : Admissible cfg)
    (hcard : Fintype.card α = 11) :
    55 ≤ 3 * blockCount cfg 3 := by
  have hlocal (p : α) : 5 ≤ blockDegree cfg 3 p := by
    have hp := Kelly.pivot_three_block_bound cfg hadm
      (by omega) (by omega) p
    rw [hcard] at hp
    norm_num at hp
    omega
  have hsum :
      (∑ _p : α, 5) ≤ ∑ p : α, blockDegree cfg 3 p :=
    Finset.sum_le_sum fun p _hp => hlocal p
  rw [block_incidence] at hsum
  simpa [hcard] using hsum

private theorem blockSizeCap_five_of_eleven
    {α : Type u} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (hadm : Admissible cfg)
    (hcard : Fintype.card α = 11)
    (hcount : Erdos506.V4.circleCount cfg ≤ 40)
    (hcircle : ∀ c : DeterminedCircle cfg,
      (circleTrace cfg c.1).card ≤ 4) :
    BlockSizeCap (blockSystem cfg) 5 := by
  apply blockSizeCap_of_line_circle_caps cfg 5
  · exact lineSupport_card_le_five_of_eleven_of_circleCount_le
      cfg hadm hcard hcount
  · intro c
    have hc := hcircle c
    omega

private theorem blockSizeCap_six_of_twelve
    {α : Type u} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (hadm : Admissible cfg)
    (hcard : Fintype.card α = 12)
    (hcount : Erdos506.V4.circleCount cfg ≤ 50)
    (hcircle : ∀ c : DeterminedCircle cfg,
      (circleTrace cfg c.1).card ≤ 4) :
    BlockSizeCap (blockSystem cfg) 6 := by
  apply blockSizeCap_of_line_circle_caps cfg 6
  · exact lineSupport_card_le_six_of_twelve_of_circleCount_le
      cfg hadm hcard hcount
  · intro c
    have hc := hcircle c
    omega

private theorem totalCircleCount_eq_circleCount
    {α : Type u} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) :
    (blockSystem cfg).totalCircleCount = Erdos506.V4.circleCount cfg := by
  rw [totalCircleCount_eq_card_determinedCircle,
    ← Erdos506.V3.circleCount_eq_card_determinedCircle]

/-- The `m ≤ 3` branch at eleven points.  After clearing the manuscript's
factor `5/6`, the certificate is `6 T - 5 G ≤ 6 C`. -/
theorem circleCount_ge_one_hundred_twenty_two_of_card_eleven_of_circle_cap_three
    {α : Type u} [Fintype α] [DecidableEq α]
    (Mel : RealPlaneMelchiorPrinciple.{u})
    (cfg : Configuration α) (hadm : Admissible cfg)
    (hcard : Fintype.card α = 11)
    (hcount : Erdos506.V4.circleCount cfg ≤ 40)
    (hcircle : ∀ c : DeterminedCircle cfg,
      (circleTrace cfg c.1).card ≤ 3) :
    122 ≤ Erdos506.V4.circleCount cfg := by
  classical
  let S := blockSystem cfg
  have hcircle4 : ∀ c : DeterminedCircle cfg,
      (circleTrace cfg c.1).card ≤ 4 := by
    intro c
    have hc := hcircle c
    omega
  have hcap : BlockSizeCap S 5 := by
    simpa [S] using blockSizeCap_five_of_eleven
      cfg hadm hcard hcount hcircle4
  have hcircleCap :
      ∀ b, S.kind b = .circle → (S.support b).card ≤ 3 := by
    simpa [S] using circle_kind_cap_of_trace_cap cfg 3 hcircle
  have hb6 : S.blockCount 6 = 0 :=
    blockCount_eq_zero_of_cap S hcap (by omega) (by omega)
  have hb7 : S.blockCount 7 = 0 :=
    blockCount_eq_zero_of_cap S hcap (by omega) (by omega)
  have hb8 : S.blockCount 8 = 0 :=
    blockCount_eq_zero_of_cap S hcap (by omega) (by omega)
  have hb9 : S.blockCount 9 = 0 :=
    blockCount_eq_zero_of_cap S hcap (by omega) (by omega)
  have hb10 : S.blockCount 10 = 0 :=
    blockCount_eq_zero_of_cap S hcap (by omega) (by omega)
  have hb11 : S.blockCount 11 = 0 :=
    blockCount_eq_zero_of_cap S hcap (by omega) (by omega)
  have hc0 : S.circleCount 0 = 0 :=
    S.circleCount_eq_zero_of_lt_three (by omega)
  have hc1 : S.circleCount 1 = 0 :=
    S.circleCount_eq_zero_of_lt_three (by omega)
  have hc2 : S.circleCount 2 = 0 :=
    S.circleCount_eq_zero_of_lt_three (by omega)
  have hc4 : S.circleCount 4 = 0 :=
    circleCount_eq_zero_of_kind_cap S hcircleCap (by omega)
  have hc5 : S.circleCount 5 = 0 :=
    circleCount_eq_zero_of_kind_cap S hcircleCap (by omega)
  have hc6 : S.circleCount 6 = 0 :=
    circleCount_eq_zero_of_kind_cap S hcircleCap (by omega)
  have hc7 : S.circleCount 7 = 0 :=
    circleCount_eq_zero_of_kind_cap S hcircleCap (by omega)
  have hc8 : S.circleCount 8 = 0 :=
    circleCount_eq_zero_of_kind_cap S hcircleCap (by omega)
  have hc9 : S.circleCount 9 = 0 :=
    circleCount_eq_zero_of_kind_cap S hcircleCap (by omega)
  have hc10 : S.circleCount 10 = 0 :=
    circleCount_eq_zero_of_kind_cap S hcircleCap (by omega)
  have hc11 : S.circleCount 11 = 0 :=
    circleCount_eq_zero_of_kind_cap S hcircleCap (by omega)
  have hT := S.triple_partition_by_size
  rw [hcard] at hT
  norm_num [Finset.sum_range_succ, Nat.choose,
    hb6, hb7, hb8, hb9, hb10, hb11] at hT
  have hTz :
      (S.blockCount 3 : ℤ) + 4 * (S.blockCount 4 : ℤ) +
        10 * (S.blockCount 5 : ℤ) = 165 := by
    exact_mod_cast hT
  have hsplit3 :
      (S.blockCount 3 : ℤ) =
        (S.lineCount 3 : ℤ) + (S.circleCount 3 : ℤ) := by
    exact_mod_cast S.blockCount_eq_lineCount_add_circleCount 3
  have hsplit4 :
      (S.blockCount 4 : ℤ) =
        (S.lineCount 4 : ℤ) + (S.circleCount 4 : ℤ) := by
    exact_mod_cast S.blockCount_eq_lineCount_add_circleCount 4
  have hsplit5 :
      (S.blockCount 5 : ℤ) =
        (S.lineCount 5 : ℤ) + (S.circleCount 5 : ℤ) := by
    exact_mod_cast S.blockCount_eq_lineCount_add_circleCount 5
  have htotal := S.totalCircleCount_eq_sum_circleCount
  rw [hcard] at htotal
  norm_num [Finset.sum_range_succ,
    hc0, hc1, hc2, hc4, hc5, hc6, hc7, hc8, hc9, hc10, hc11] at htotal
  have hbridge : S.totalCircleCount = Erdos506.V4.circleCount cfg := by
    simpa [S] using totalCircleCount_eq_circleCount cfg
  rw [hbridge] at htotal
  have htotalZ :
      (Erdos506.V4.circleCount cfg : ℤ) = (S.circleCount 3 : ℤ) := by
    exact_mod_cast htotal
  have hG :=
    globalLineRow_le_choose_two_sub_three_of_realPlaneMelchior Mel cfg hadm
  change S.globalLineRow ≤
    (Nat.choose (Fintype.card α) 2 : ℤ) - 3 at hG
  rw [globalLineRow_eq_eleven S hcard hcap, hcard] at hG
  norm_num [Nat.choose] at hG
  omega

/-- The `m ≤ 3` branch at twelve points.  Clearing `10/9` gives the
integer certificate `9 T - 10 G ≤ 9 C`. -/
theorem circleCount_ge_one_hundred_fifty_of_card_twelve_of_circle_cap_three
    {α : Type u} [Fintype α] [DecidableEq α]
    (Mel : RealPlaneMelchiorPrinciple.{u})
    (cfg : Configuration α) (hadm : Admissible cfg)
    (hcard : Fintype.card α = 12)
    (hcount : Erdos506.V4.circleCount cfg ≤ 50)
    (hcircle : ∀ c : DeterminedCircle cfg,
      (circleTrace cfg c.1).card ≤ 3) :
    150 ≤ Erdos506.V4.circleCount cfg := by
  classical
  let S := blockSystem cfg
  have hcircle4 : ∀ c : DeterminedCircle cfg,
      (circleTrace cfg c.1).card ≤ 4 := by
    intro c
    have hc := hcircle c
    omega
  have hcap : BlockSizeCap S 6 := by
    simpa [S] using blockSizeCap_six_of_twelve
      cfg hadm hcard hcount hcircle4
  have hcircleCap :
      ∀ b, S.kind b = .circle → (S.support b).card ≤ 3 := by
    simpa [S] using circle_kind_cap_of_trace_cap cfg 3 hcircle
  have hb7 : S.blockCount 7 = 0 :=
    blockCount_eq_zero_of_cap S hcap (by omega) (by omega)
  have hb8 : S.blockCount 8 = 0 :=
    blockCount_eq_zero_of_cap S hcap (by omega) (by omega)
  have hb9 : S.blockCount 9 = 0 :=
    blockCount_eq_zero_of_cap S hcap (by omega) (by omega)
  have hb10 : S.blockCount 10 = 0 :=
    blockCount_eq_zero_of_cap S hcap (by omega) (by omega)
  have hb11 : S.blockCount 11 = 0 :=
    blockCount_eq_zero_of_cap S hcap (by omega) (by omega)
  have hb12 : S.blockCount 12 = 0 :=
    blockCount_eq_zero_of_cap S hcap (by omega) (by omega)
  have hc0 : S.circleCount 0 = 0 :=
    S.circleCount_eq_zero_of_lt_three (by omega)
  have hc1 : S.circleCount 1 = 0 :=
    S.circleCount_eq_zero_of_lt_three (by omega)
  have hc2 : S.circleCount 2 = 0 :=
    S.circleCount_eq_zero_of_lt_three (by omega)
  have hc4 : S.circleCount 4 = 0 :=
    circleCount_eq_zero_of_kind_cap S hcircleCap (by omega)
  have hc5 : S.circleCount 5 = 0 :=
    circleCount_eq_zero_of_kind_cap S hcircleCap (by omega)
  have hc6 : S.circleCount 6 = 0 :=
    circleCount_eq_zero_of_kind_cap S hcircleCap (by omega)
  have hc7 : S.circleCount 7 = 0 :=
    circleCount_eq_zero_of_kind_cap S hcircleCap (by omega)
  have hc8 : S.circleCount 8 = 0 :=
    circleCount_eq_zero_of_kind_cap S hcircleCap (by omega)
  have hc9 : S.circleCount 9 = 0 :=
    circleCount_eq_zero_of_kind_cap S hcircleCap (by omega)
  have hc10 : S.circleCount 10 = 0 :=
    circleCount_eq_zero_of_kind_cap S hcircleCap (by omega)
  have hc11 : S.circleCount 11 = 0 :=
    circleCount_eq_zero_of_kind_cap S hcircleCap (by omega)
  have hc12 : S.circleCount 12 = 0 :=
    circleCount_eq_zero_of_kind_cap S hcircleCap (by omega)
  have hT := S.triple_partition_by_size
  rw [hcard] at hT
  norm_num [Finset.sum_range_succ, Nat.choose,
    hb7, hb8, hb9, hb10, hb11, hb12] at hT
  have hTz :
      (S.blockCount 3 : ℤ) + 4 * (S.blockCount 4 : ℤ) +
        10 * (S.blockCount 5 : ℤ) + 20 * (S.blockCount 6 : ℤ) = 220 := by
    exact_mod_cast hT
  have hsplit3 :
      (S.blockCount 3 : ℤ) =
        (S.lineCount 3 : ℤ) + (S.circleCount 3 : ℤ) := by
    exact_mod_cast S.blockCount_eq_lineCount_add_circleCount 3
  have hsplit4 :
      (S.blockCount 4 : ℤ) =
        (S.lineCount 4 : ℤ) + (S.circleCount 4 : ℤ) := by
    exact_mod_cast S.blockCount_eq_lineCount_add_circleCount 4
  have hsplit5 :
      (S.blockCount 5 : ℤ) =
        (S.lineCount 5 : ℤ) + (S.circleCount 5 : ℤ) := by
    exact_mod_cast S.blockCount_eq_lineCount_add_circleCount 5
  have hsplit6 :
      (S.blockCount 6 : ℤ) =
        (S.lineCount 6 : ℤ) + (S.circleCount 6 : ℤ) := by
    exact_mod_cast S.blockCount_eq_lineCount_add_circleCount 6
  have htotal := S.totalCircleCount_eq_sum_circleCount
  rw [hcard] at htotal
  norm_num [Finset.sum_range_succ,
    hc0, hc1, hc2, hc4, hc5, hc6, hc7, hc8, hc9, hc10, hc11, hc12] at htotal
  have hbridge : S.totalCircleCount = Erdos506.V4.circleCount cfg := by
    simpa [S] using totalCircleCount_eq_circleCount cfg
  rw [hbridge] at htotal
  have htotalZ :
      (Erdos506.V4.circleCount cfg : ℤ) = (S.circleCount 3 : ℤ) := by
    exact_mod_cast htotal
  have hG :=
    globalLineRow_le_choose_two_sub_three_of_realPlaneMelchior Mel cfg hadm
  change S.globalLineRow ≤
    (Nat.choose (Fintype.card α) 2 : ℤ) - 3 at hG
  rw [globalLineRow_eq_twelve S hcard hcap, hcard] at hG
  norm_num [Nat.choose] at hG
  omega

/-- The summed pivot-Melchior row `P` at twelve points, reduced by the
six-block cap to `3 B₃ - 5 B₅ - 12 B₆ ≥ 36`. -/
theorem thirty_six_le_twelve_pivot_row
    {α : Type u} [Fintype α] [DecidableEq α]
    (Mel : RealPlaneMelchiorPrinciple.{u})
    (cfg : Configuration α) (hadm : Admissible cfg)
    (hcard : Fintype.card α = 12)
    (hcap : BlockSizeCap (blockSystem cfg) 6) :
    36 ≤ 3 * (blockCount cfg 3 : ℤ) - 5 * (blockCount cfg 5 : ℤ) -
      12 * (blockCount cfg 6 : ℤ) := by
  let S := blockSystem cfg
  have hb7 : S.blockCount 7 = 0 :=
    blockCount_eq_zero_of_cap S hcap (by omega) (by omega)
  have hb8 : S.blockCount 8 = 0 :=
    blockCount_eq_zero_of_cap S hcap (by omega) (by omega)
  have hb9 : S.blockCount 9 = 0 :=
    blockCount_eq_zero_of_cap S hcap (by omega) (by omega)
  have hb10 : S.blockCount 10 = 0 :=
    blockCount_eq_zero_of_cap S hcap (by omega) (by omega)
  have hb11 : S.blockCount 11 = 0 :=
    blockCount_eq_zero_of_cap S hcap (by omega) (by omega)
  have hb12 : S.blockCount 12 = 0 :=
    blockCount_eq_zero_of_cap S hcap (by omega) (by omega)
  have hP := three_n_le_rowP_of_realPlaneMelchior Mel cfg hadm (by omega)
  change 3 * (Fintype.card α : ℤ) ≤ S.pivotRow at hP
  unfold BlockSystem.pivotRow BlockSystem.nontrivialSizes at hP
  rw [hcard] at hP
  have hIcc : Finset.Icc 3 12 = {3, 4, 5, 6, 7, 8, 9, 10, 11, 12} := by
    decide
  rw [hIcc] at hP
  norm_num [hb7, hb8, hb9, hb10, hb11, hb12] at hP
  change (36 : ℤ) ≤
    3 * (S.blockCount 3 : ℤ) - 5 * (S.blockCount 5 : ℤ) -
      12 * (S.blockCount 6 : ℤ)
  omega

/-- The eleven-point `T/O/G/K` certificate, scaled by `24`.  Line
coefficients are `0, -11, 0` at sizes `3,4,5`, while each proper-circle
coefficient is `24`. -/
theorem circleCount_ge_forty_two_of_card_eleven_of_circle_cap_four
    {α : Type u} [Fintype α] [DecidableEq α]
    (Mel : RealPlaneMelchiorPrinciple.{u})
    (Kelly : RealPlaneKellyMoserPrinciple.{u})
    (cfg : Configuration α) (hadm : Admissible cfg)
    (hcard : Fintype.card α = 11)
    (hcount : Erdos506.V4.circleCount cfg ≤ 40)
    (hcircle : ∀ c : DeterminedCircle cfg,
      (circleTrace cfg c.1).card ≤ 4) :
    42 ≤ Erdos506.V4.circleCount cfg := by
  classical
  let S := blockSystem cfg
  have hcap : BlockSizeCap S 5 := by
    simpa [S] using blockSizeCap_five_of_eleven
      cfg hadm hcard hcount hcircle
  have hcircleCap :
      ∀ b, S.kind b = .circle → (S.support b).card ≤ 4 := by
    simpa [S] using circle_kind_cap_of_trace_cap cfg 4 hcircle
  have hb6 : S.blockCount 6 = 0 :=
    blockCount_eq_zero_of_cap S hcap (by omega) (by omega)
  have hb7 : S.blockCount 7 = 0 :=
    blockCount_eq_zero_of_cap S hcap (by omega) (by omega)
  have hb8 : S.blockCount 8 = 0 :=
    blockCount_eq_zero_of_cap S hcap (by omega) (by omega)
  have hb9 : S.blockCount 9 = 0 :=
    blockCount_eq_zero_of_cap S hcap (by omega) (by omega)
  have hb10 : S.blockCount 10 = 0 :=
    blockCount_eq_zero_of_cap S hcap (by omega) (by omega)
  have hb11 : S.blockCount 11 = 0 :=
    blockCount_eq_zero_of_cap S hcap (by omega) (by omega)
  have hc0 : S.circleCount 0 = 0 :=
    S.circleCount_eq_zero_of_lt_three (by omega)
  have hc1 : S.circleCount 1 = 0 :=
    S.circleCount_eq_zero_of_lt_three (by omega)
  have hc2 : S.circleCount 2 = 0 :=
    S.circleCount_eq_zero_of_lt_three (by omega)
  have hc5 : S.circleCount 5 = 0 :=
    circleCount_eq_zero_of_kind_cap S hcircleCap (by omega)
  have hc6 : S.circleCount 6 = 0 :=
    circleCount_eq_zero_of_kind_cap S hcircleCap (by omega)
  have hc7 : S.circleCount 7 = 0 :=
    circleCount_eq_zero_of_kind_cap S hcircleCap (by omega)
  have hc8 : S.circleCount 8 = 0 :=
    circleCount_eq_zero_of_kind_cap S hcircleCap (by omega)
  have hc9 : S.circleCount 9 = 0 :=
    circleCount_eq_zero_of_kind_cap S hcircleCap (by omega)
  have hc10 : S.circleCount 10 = 0 :=
    circleCount_eq_zero_of_kind_cap S hcircleCap (by omega)
  have hc11 : S.circleCount 11 = 0 :=
    circleCount_eq_zero_of_kind_cap S hcircleCap (by omega)
  have hT := S.triple_partition_by_size
  rw [hcard] at hT
  norm_num [Finset.sum_range_succ, Nat.choose,
    hb6, hb7, hb8, hb9, hb10, hb11] at hT
  have hTz :
      (S.blockCount 3 : ℤ) + 4 * (S.blockCount 4 : ℤ) +
        10 * (S.blockCount 5 : ℤ) = 165 := by
    exact_mod_cast hT
  have hsplit3 :
      (S.blockCount 3 : ℤ) =
        (S.lineCount 3 : ℤ) + (S.circleCount 3 : ℤ) := by
    exact_mod_cast S.blockCount_eq_lineCount_add_circleCount 3
  have hsplit4 :
      (S.blockCount 4 : ℤ) =
        (S.lineCount 4 : ℤ) + (S.circleCount 4 : ℤ) := by
    exact_mod_cast S.blockCount_eq_lineCount_add_circleCount 4
  have hsplit5 :
      (S.blockCount 5 : ℤ) =
        (S.lineCount 5 : ℤ) + (S.circleCount 5 : ℤ) := by
    exact_mod_cast S.blockCount_eq_lineCount_add_circleCount 5
  have htotal := S.totalCircleCount_eq_sum_circleCount
  rw [hcard] at htotal
  norm_num [Finset.sum_range_succ,
    hc0, hc1, hc2, hc5, hc6, hc7, hc8, hc9, hc10, hc11] at htotal
  have hbridge : S.totalCircleCount = Erdos506.V4.circleCount cfg := by
    simpa [S] using totalCircleCount_eq_circleCount cfg
  rw [hbridge] at htotal
  have htotalZ :
      (Erdos506.V4.circleCount cfg : ℤ) =
        (S.circleCount 3 : ℤ) + (S.circleCount 4 : ℤ) := by
    exact_mod_cast htotal
  have hG :=
    globalLineRow_le_choose_two_sub_three_of_realPlaneMelchior Mel cfg hadm
  change S.globalLineRow ≤
    (Nat.choose (Fintype.card α) 2 : ℤ) - 3 at hG
  rw [globalLineRow_eq_eleven S hcard hcap, hcard] at hG
  norm_num [Nat.choose] at hG
  have hKn :=
    fifty_five_le_three_blockCount_three_of_card_eleven
      Kelly cfg hadm hcard
  change 55 ≤ 3 * S.blockCount 3 at hKn
  have hK : (55 : ℤ) ≤ 3 * (S.blockCount 3 : ℤ) := by
    exact_mod_cast hKn
  have hl6 : S.lineCount 6 = 0 :=
    lineCount_eq_zero_of_cap S hcap (by omega) (by omega)
  have hl7 : S.lineCount 7 = 0 :=
    lineCount_eq_zero_of_cap S hcap (by omega) (by omega)
  have hl8 : S.lineCount 8 = 0 :=
    lineCount_eq_zero_of_cap S hcap (by omega) (by omega)
  have hl9 : S.lineCount 9 = 0 :=
    lineCount_eq_zero_of_cap S hcap (by omega) (by omega)
  have hl10 : S.lineCount 10 = 0 :=
    lineCount_eq_zero_of_cap S hcap (by omega) (by omega)
  have hl11 : S.lineCount 11 = 0 :=
    lineCount_eq_zero_of_cap S hcap (by omega) (by omega)
  have hPair := S.line_pair_partition_by_size
  rw [hcard] at hPair
  norm_num [Finset.sum_range_succ, Nat.choose,
    hl6, hl7, hl8, hl9, hl10, hl11] at hPair
  have hRn :=
    Kelly.fifty_five_le_restored_three_incidence_of_card_eleven
      cfg hadm hcard
  change 55 ≤ 2 * S.lineCount 2 + 3 * S.circleCount 3 at hRn
  have hR : (55 : ℤ) ≤ 2 * (S.lineCount 2 : ℤ) +
      3 * (S.circleCount 3 : ℤ) := by
    exact_mod_cast hRn
  omega

/-- The twelve-point `T/O/G/P` certificate, scaled by `60`.  Its line
coefficients are `0, -24, -29, 0` at sizes `3,4,5,6`, and every proper
circle has coefficient `60`. -/
theorem circleCount_ge_fifty_two_of_card_twelve_of_circle_cap_four
    {α : Type u} [Fintype α] [DecidableEq α]
    (Mel : RealPlaneMelchiorPrinciple.{u})
    (Kelly : RealPlaneKellyMoserPrinciple.{u})
    (cfg : Configuration α) (hadm : Admissible cfg)
    (hcard : Fintype.card α = 12)
    (hcount : Erdos506.V4.circleCount cfg ≤ 50)
    (hcircle : ∀ c : DeterminedCircle cfg,
      (circleTrace cfg c.1).card ≤ 4) :
    52 ≤ Erdos506.V4.circleCount cfg := by
  classical
  let S := blockSystem cfg
  have hcap : BlockSizeCap S 6 := by
    simpa [S] using blockSizeCap_six_of_twelve
      cfg hadm hcard hcount hcircle
  have hcircleCap :
      ∀ b, S.kind b = .circle → (S.support b).card ≤ 4 := by
    simpa [S] using circle_kind_cap_of_trace_cap cfg 4 hcircle
  have hb7 : S.blockCount 7 = 0 :=
    blockCount_eq_zero_of_cap S hcap (by omega) (by omega)
  have hb8 : S.blockCount 8 = 0 :=
    blockCount_eq_zero_of_cap S hcap (by omega) (by omega)
  have hb9 : S.blockCount 9 = 0 :=
    blockCount_eq_zero_of_cap S hcap (by omega) (by omega)
  have hb10 : S.blockCount 10 = 0 :=
    blockCount_eq_zero_of_cap S hcap (by omega) (by omega)
  have hb11 : S.blockCount 11 = 0 :=
    blockCount_eq_zero_of_cap S hcap (by omega) (by omega)
  have hb12 : S.blockCount 12 = 0 :=
    blockCount_eq_zero_of_cap S hcap (by omega) (by omega)
  have hc0 : S.circleCount 0 = 0 :=
    S.circleCount_eq_zero_of_lt_three (by omega)
  have hc1 : S.circleCount 1 = 0 :=
    S.circleCount_eq_zero_of_lt_three (by omega)
  have hc2 : S.circleCount 2 = 0 :=
    S.circleCount_eq_zero_of_lt_three (by omega)
  have hc5 : S.circleCount 5 = 0 :=
    circleCount_eq_zero_of_kind_cap S hcircleCap (by omega)
  have hc6 : S.circleCount 6 = 0 :=
    circleCount_eq_zero_of_kind_cap S hcircleCap (by omega)
  have hc7 : S.circleCount 7 = 0 :=
    circleCount_eq_zero_of_kind_cap S hcircleCap (by omega)
  have hc8 : S.circleCount 8 = 0 :=
    circleCount_eq_zero_of_kind_cap S hcircleCap (by omega)
  have hc9 : S.circleCount 9 = 0 :=
    circleCount_eq_zero_of_kind_cap S hcircleCap (by omega)
  have hc10 : S.circleCount 10 = 0 :=
    circleCount_eq_zero_of_kind_cap S hcircleCap (by omega)
  have hc11 : S.circleCount 11 = 0 :=
    circleCount_eq_zero_of_kind_cap S hcircleCap (by omega)
  have hc12 : S.circleCount 12 = 0 :=
    circleCount_eq_zero_of_kind_cap S hcircleCap (by omega)
  have hT := S.triple_partition_by_size
  rw [hcard] at hT
  norm_num [Finset.sum_range_succ, Nat.choose,
    hb7, hb8, hb9, hb10, hb11, hb12] at hT
  have hTz :
      (S.blockCount 3 : ℤ) + 4 * (S.blockCount 4 : ℤ) +
        10 * (S.blockCount 5 : ℤ) + 20 * (S.blockCount 6 : ℤ) = 220 := by
    exact_mod_cast hT
  have hsplit3 :
      (S.blockCount 3 : ℤ) =
        (S.lineCount 3 : ℤ) + (S.circleCount 3 : ℤ) := by
    exact_mod_cast S.blockCount_eq_lineCount_add_circleCount 3
  have hsplit4 :
      (S.blockCount 4 : ℤ) =
        (S.lineCount 4 : ℤ) + (S.circleCount 4 : ℤ) := by
    exact_mod_cast S.blockCount_eq_lineCount_add_circleCount 4
  have hsplit5 :
      (S.blockCount 5 : ℤ) =
        (S.lineCount 5 : ℤ) + (S.circleCount 5 : ℤ) := by
    exact_mod_cast S.blockCount_eq_lineCount_add_circleCount 5
  have hsplit6 :
      (S.blockCount 6 : ℤ) =
        (S.lineCount 6 : ℤ) + (S.circleCount 6 : ℤ) := by
    exact_mod_cast S.blockCount_eq_lineCount_add_circleCount 6
  have htotal := S.totalCircleCount_eq_sum_circleCount
  rw [hcard] at htotal
  norm_num [Finset.sum_range_succ,
    hc0, hc1, hc2, hc5, hc6, hc7, hc8, hc9, hc10, hc11, hc12] at htotal
  have hbridge : S.totalCircleCount = Erdos506.V4.circleCount cfg := by
    simpa [S] using totalCircleCount_eq_circleCount cfg
  rw [hbridge] at htotal
  have htotalZ :
      (Erdos506.V4.circleCount cfg : ℤ) =
        (S.circleCount 3 : ℤ) + (S.circleCount 4 : ℤ) := by
    exact_mod_cast htotal
  have hP := thirty_six_le_twelve_pivot_row Mel cfg hadm hcard hcap
  change (36 : ℤ) ≤ 3 * (S.blockCount 3 : ℤ) -
    5 * (S.blockCount 5 : ℤ) - 12 * (S.blockCount 6 : ℤ) at hP
  have hl7 : S.lineCount 7 = 0 :=
    lineCount_eq_zero_of_cap S hcap (by omega) (by omega)
  have hl8 : S.lineCount 8 = 0 :=
    lineCount_eq_zero_of_cap S hcap (by omega) (by omega)
  have hl9 : S.lineCount 9 = 0 :=
    lineCount_eq_zero_of_cap S hcap (by omega) (by omega)
  have hl10 : S.lineCount 10 = 0 :=
    lineCount_eq_zero_of_cap S hcap (by omega) (by omega)
  have hl11 : S.lineCount 11 = 0 :=
    lineCount_eq_zero_of_cap S hcap (by omega) (by omega)
  have hl12 : S.lineCount 12 = 0 :=
    lineCount_eq_zero_of_cap S hcap (by omega) (by omega)
  have hPair := S.line_pair_partition_by_size
  rw [hcard] at hPair
  norm_num [Finset.sum_range_succ, Nat.choose,
    hl7, hl8, hl9, hl10, hl11, hl12] at hPair
  have hRn :=
    Kelly.seventy_two_le_restored_three_incidence_of_card_twelve
      cfg hadm hcard
  change 72 ≤ 2 * S.lineCount 2 + 3 * S.circleCount 3 at hRn
  have hR : (72 : ℤ) ≤ 2 * (S.lineCount 2 : ℤ) +
      3 * (S.circleCount 3 : ℤ) := by
    exact_mod_cast hRn
  omega

/-- Eleven-point outer router: below the target there is a determined
proper circle through exactly five or six selected points. -/
theorem exists_circle_trace_card_five_or_six_of_card_eleven_of_circleCount_le
    {α : Type u} [Fintype α] [DecidableEq α]
    (Mel : RealPlaneMelchiorPrinciple.{u})
    (Kelly : RealPlaneKellyMoserPrinciple.{u})
    (cfg : Configuration α) (hadm : Admissible cfg)
    (hcard : Fintype.card α = 11)
    (hcount : Erdos506.V4.circleCount cfg ≤ 40) :
    ∃ c : DeterminedCircle cfg,
      (circleTrace cfg c.1).card = 5 ∨
        (circleTrace cfg c.1).card = 6 := by
  classical
  by_contra hnone
  simp only [not_exists, not_or] at hnone
  have hcircle4 : ∀ c : DeterminedCircle cfg,
      (circleTrace cfg c.1).card ≤ 4 := by
    intro c
    have hcap6 :=
      circleTrace_card_le_six_of_eleven_of_circleCount_le
        cfg hadm hcard hcount c
    have hne := hnone c
    omega
  have hlarge :=
    circleCount_ge_forty_two_of_card_eleven_of_circle_cap_four
      Mel Kelly cfg hadm hcard hcount hcircle4
  omega

/-- Twelve-point outer router: below the target there is a determined
proper circle through exactly five or six selected points. -/
theorem exists_circle_trace_card_five_or_six_of_card_twelve_of_circleCount_le
    {α : Type u} [Fintype α] [DecidableEq α]
    (Mel : RealPlaneMelchiorPrinciple.{u})
    (Kelly : RealPlaneKellyMoserPrinciple.{u})
    (cfg : Configuration α) (hadm : Admissible cfg)
    (hcard : Fintype.card α = 12)
    (hcount : Erdos506.V4.circleCount cfg ≤ 50) :
    ∃ c : DeterminedCircle cfg,
      (circleTrace cfg c.1).card = 5 ∨
        (circleTrace cfg c.1).card = 6 := by
  classical
  by_contra hnone
  simp only [not_exists, not_or] at hnone
  have hcircle4 : ∀ c : DeterminedCircle cfg,
      (circleTrace cfg c.1).card ≤ 4 := by
    intro c
    have hcap6 :=
      circleTrace_card_le_six_of_twelve_of_circleCount_le
        cfg hadm hcard hcount c
    have hne := hnone c
    omega
  have hlarge :=
    circleCount_ge_fifty_two_of_card_twelve_of_circle_cap_four
      Mel Kelly cfg hadm hcard hcount hcircle4
  omega

end Erdos506.V1
