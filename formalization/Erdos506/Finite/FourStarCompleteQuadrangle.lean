import Erdos506.Finite.FourStarLink
import Erdos506.Block.Counts
import Mathlib.Tactic

/-!
# The overlap count behind the four-star complete quadrangle

The local four-star link has four four-point base lines on a ten-point set.
The lemmas in this file isolate the sharp finite overlap count: if one pair
of base lines were disjoint, their union would already need eleven points.
-/

namespace Erdos506.Finite

/-- The two-term Bonferroni bound specialized to four named finite sets.
Keeping the six intersections explicit is useful when one of them is known
to be empty. -/
theorem card_union_four_le_card_union_add_pair_intersections
    {α : Type*} [DecidableEq α]
    (A B C D : Finset α) :
    A.card + B.card + C.card + D.card ≤
      (A ∪ B ∪ C ∪ D).card +
        (A ∩ B).card + (A ∩ C).card + (A ∩ D).card +
          (B ∩ C).card + (B ∩ D).card + (C ∩ D).card := by
  have hCsub : (A ∪ B) ∩ C ⊆ (A ∩ C) ∪ (B ∩ C) := by
    intro x hx
    rcases Finset.mem_inter.mp hx with ⟨hxAB, hxC⟩
    rcases Finset.mem_union.mp hxAB with hxA | hxB
    · exact Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨hxA, hxC⟩)
    · exact Finset.mem_union_right _ (Finset.mem_inter.mpr ⟨hxB, hxC⟩)
  have hCinter : ((A ∪ B) ∩ C).card ≤
      (A ∩ C).card + (B ∩ C).card := by
    exact (Finset.card_le_card hCsub).trans
      (Finset.card_union_le (A ∩ C) (B ∩ C))
  have hDsub : (A ∪ B ∪ C) ∩ D ⊆
      ((A ∩ D) ∪ (B ∩ D)) ∪ (C ∩ D) := by
    intro x hx
    rcases Finset.mem_inter.mp hx with ⟨hxABC, hxD⟩
    rcases Finset.mem_union.mp hxABC with hxAB | hxC
    · rcases Finset.mem_union.mp hxAB with hxA | hxB
      · exact Finset.mem_union_left _ (Finset.mem_union_left _
          (Finset.mem_inter.mpr ⟨hxA, hxD⟩))
      · exact Finset.mem_union_left _ (Finset.mem_union_right _
          (Finset.mem_inter.mpr ⟨hxB, hxD⟩))
    · exact Finset.mem_union_right _ (Finset.mem_inter.mpr ⟨hxC, hxD⟩)
  have hDinter : ((A ∪ B ∪ C) ∩ D).card ≤
      (A ∩ D).card + (B ∩ D).card + (C ∩ D).card := by
    calc
      ((A ∪ B ∪ C) ∩ D).card ≤
          (((A ∩ D) ∪ (B ∩ D)) ∪ (C ∩ D)).card :=
        Finset.card_le_card hDsub
      _ ≤ ((A ∩ D) ∪ (B ∩ D)).card + (C ∩ D).card :=
        Finset.card_union_le _ _
      _ ≤ (A ∩ D).card + (B ∩ D).card + (C ∩ D).card := by
        gcongr
        exact Finset.card_union_le _ _
  have hAB := Finset.card_union_add_card_inter A B
  have hABC := Finset.card_union_add_card_inter (A ∪ B) C
  have hABCD := Finset.card_union_add_card_inter (A ∪ B ∪ C) D
  omega

/-- With four four-point sets in a ten-point universe and pairwise overlap
at most one, a specified pair cannot be disjoint. -/
theorem four_card_four_inter_nonempty_of_union_card_le_ten
    {α : Type*} [DecidableEq α]
    (A B C D : Finset α)
    (hA : A.card = 4) (hB : B.card = 4)
    (hC : C.card = 4) (hD : D.card = 4)
    (hUnion : (A ∪ B ∪ C ∪ D).card ≤ 10)
    (hAC : (A ∩ C).card ≤ 1) (hAD : (A ∩ D).card ≤ 1)
    (hBC : (B ∩ C).card ≤ 1) (hBD : (B ∩ D).card ≤ 1)
    (hCD : (C ∩ D).card ≤ 1) :
    (A ∩ B).Nonempty := by
  by_contra hEmpty
  have hAB : (A ∩ B).card = 0 := by
    simpa using congrArg Finset.card
      (Finset.not_nonempty_iff_eq_empty.mp hEmpty)
  have hbound := card_union_four_le_card_union_add_pair_intersections A B C D
  rw [hA, hB, hC, hD, hAB] at hbound
  omega

/-- Four size-four line blocks on ten points form a complete quadrangle:
every two distinct supports meet in exactly one point.  The counts of the
smaller line layers are irrelevant to this saturation step. -/
theorem line_four_inter_card_one_of_card_ten_count_four
    {Point Block : Type*} [Fintype Point] [Fintype Block]
    [DecidableEq Point]
    (S : Erdos506.Block.BlockSystem Point Block)
    (hPoint : Fintype.card Point = 10) (hfour : S.lineCount 4 = 4)
    {b c : Block} (hb : b ∈ S.lineBlocksOfSize 4)
    (hc : c ∈ S.lineBlocksOfSize 4) (hbc : b ≠ c) :
    (S.support b ∩ S.support c).card = 1 := by
  classical
  let L := S.lineBlocksOfSize 4
  have hLcard : L.card = 4 := hfour
  have hbL : b ∈ L := hb
  have hcL : c ∈ L := hc
  have hcErase : c ∈ L.erase b :=
    Finset.mem_erase.mpr ⟨Ne.symm hbc, hcL⟩
  let R := (L.erase b).erase c
  have hRcard : R.card = 2 := by
    change ((L.erase b).erase c).card = 2
    rw [Finset.card_erase_of_mem hcErase,
      Finset.card_erase_of_mem hbL, hLcard]
  obtain ⟨d, e, hde, hReq⟩ := Finset.card_eq_two.mp hRcard
  have hdR : d ∈ R := by rw [hReq]; simp
  have heR : e ∈ R := by rw [hReq]; simp
  have hdL : d ∈ L :=
    Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hdR)
  have heL : e ∈ L :=
    Finset.mem_of_mem_erase (Finset.mem_of_mem_erase heR)
  have hdb : d ≠ b :=
    (Finset.mem_erase.mp (Finset.mem_of_mem_erase hdR)).1
  have heb : e ≠ b :=
    (Finset.mem_erase.mp (Finset.mem_of_mem_erase heR)).1
  have hdc : d ≠ c := (Finset.mem_erase.mp hdR).1
  have hec : e ≠ c := (Finset.mem_erase.mp heR).1
  have hinter (x y : Block) (hx : x ∈ L) (hy : y ∈ L) (hxy : x ≠ y) :
      (S.support x ∩ S.support y).card ≤ 1 := by
    have hxkind : S.kind x = .line :=
      (S.mem_blocksOfKindSize.mp hx).1
    have hykind : S.kind y = .line :=
      (S.mem_blocksOfKindSize.mp hy).1
    have hlt := S.distinct_line_inter_card_lt_two
      (b := ⟨x, hxkind⟩) (c := ⟨y, hykind⟩) (by
        intro h
        apply hxy
        exact congrArg Subtype.val h)
    exact Nat.le_of_lt_succ hlt
  have hbcard : (S.support b).card = 4 :=
    (S.mem_blocksOfKindSize.mp hbL).2
  have hccard : (S.support c).card = 4 :=
    (S.mem_blocksOfKindSize.mp hcL).2
  have hdcard : (S.support d).card = 4 :=
    (S.mem_blocksOfKindSize.mp hdL).2
  have hecard : (S.support e).card = 4 :=
    (S.mem_blocksOfKindSize.mp heL).2
  have hunion :
      (S.support b ∪ S.support c ∪ S.support d ∪ S.support e).card ≤ 10 := by
    calc
      (S.support b ∪ S.support c ∪ S.support d ∪ S.support e).card ≤
          (Finset.univ : Finset Point).card :=
        Finset.card_le_card (Finset.subset_univ _)
      _ = 10 := by simp [hPoint]
  have hnonempty := four_card_four_inter_nonempty_of_union_card_le_ten
    (S.support b) (S.support c) (S.support d) (S.support e)
    hbcard hccard hdcard hecard hunion
    (hinter b d hbL hdL (Ne.symm hdb))
    (hinter b e hbL heL (Ne.symm heb))
    (hinter c d hcL hdL (Ne.symm hdc))
    (hinter c e hcL heL (Ne.symm hec))
    (hinter d e hdL heL hde)
  have hle : (S.support b ∩ S.support c).card ≤ 1 :=
    hinter b c hbL hcL hbc
  have hpos : 0 < (S.support b ∩ S.support c).card :=
    Finset.card_pos.mpr hnonempty
  omega

end Erdos506.Finite
