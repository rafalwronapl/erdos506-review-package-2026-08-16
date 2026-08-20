import Erdos506.V1.ElevenFiveC40TwoBaseCapacity

/-!
# Finite entrance to the K3.1 disjoint-four-line case

Before the real projective part of K3.1, its line-system reduction is wholly
finite.  A disjoint pair of four-lines uses eight of ten labels; a third
four-line can use at most the two remaining labels away from that pair and
therefore meets both bases exactly once.  Thus the three lines have the
path incidence shape from which the `3,2,3` dual private families arise.

This module intentionally records that reduction without postulating a
geometric certificate.
-/

namespace Erdos506.V1

open Erdos506.Block
open Erdos506.Block.BlockSystem
open scoped BigOperators

universe u v

/-- In a ten-label line system, a third four-line distinct from two
disjoint four-lines meets each of them in exactly one label.  This is the
finite path reduction used at the start of K3.1. -/
theorem disjoint_four_lines_force_path
    {Point : Type u} {Block : Type v} [Fintype Point] [Fintype Block]
    [DecidableEq Point]
    (S : BlockSystem Point Block) (hcard : Fintype.card Point = 10)
    (a b c : LineBlock S)
    (ha : (S.support a.1).card = 4)
    (hb : (S.support b.1).card = 4)
    (hc : (S.support c.1).card = 4)
    (hab : Disjoint (S.support a.1) (S.support b.1))
    (hca : c ≠ a) (hcb : c ≠ b) :
    (S.support c.1 ∩ S.support a.1).card = 1 ∧
      (S.support c.1 ∩ S.support b.1).card = 1 := by
  classical
  let U := S.support a.1 ∪ S.support b.1
  have hU : U.card = 8 := by
    dsimp [U]
    rw [Finset.card_union_of_disjoint hab, ha, hb]
  have hUcomp : (Finset.univ \ U).card = 2 := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _),
      Finset.card_univ, hcard, hU]
  have hcaLt := S.distinct_line_inter_card_lt_two hca
  have hcbLt := S.distinct_line_inter_card_lt_two hcb
  change (S.support c.1 ∩ S.support a.1).card < 2 at hcaLt
  change (S.support c.1 ∩ S.support b.1).card < 2 at hcbLt
  have houtSub : S.support c.1 \ U ⊆ Finset.univ \ U := by
    intro q hq
    apply Finset.mem_sdiff.mpr
    exact ⟨Finset.mem_univ q, (Finset.mem_sdiff.mp hq).2⟩
  have hout : (S.support c.1 \ U).card ≤ 2 := by
    exact (Finset.card_le_card houtSub).trans_eq hUcomp
  have hsplit := Finset.card_inter_add_card_sdiff (S.support c.1) U
  rw [hc] at hsplit
  have hin : 2 ≤ (S.support c.1 ∩ U).card := by omega
  have hinterUnion : S.support c.1 ∩ U =
      (S.support c.1 ∩ S.support a.1) ∪
        (S.support c.1 ∩ S.support b.1) := by
    ext q
    simp only [U, Finset.mem_inter, Finset.mem_union]
    tauto
  have hinLe : (S.support c.1 ∩ U).card ≤
      (S.support c.1 ∩ S.support a.1).card +
        (S.support c.1 ∩ S.support b.1).card := by
    rw [hinterUnion]
    exact Finset.card_union_le _ _
  constructor <;> omega

end Erdos506.V1
