import Erdos506.V1.ElevenFiveC40SingletonExclusion

/-!
# The two-base capacity obstruction in the `C = 40` singleton row

Two disjoint four-point affine lines in a ten-point configuration leave a
two-point complement.  Every three-point line then uses at least two mixed
pairs across that complement.  Nine such lines would consume eighteen mixed
pairs, whereas line-pair ownership provides exactly sixteen.

The first theorem is deliberately a `BlockSystem` statement.  The second
only transports the two five-blocks through a pivot inversion; it needs no
additional geometric principle.
-/

namespace Erdos506.V1

open Erdos506.Block
open Erdos506.Block.BlockSystem
open Erdos506.Incidence
open Erdos506.V3
open Erdos506.V4
open scoped BigOperators

universe u v

/-- A ten-point line system cannot have two disjoint four-lines together
with nine three-lines.  The proof is the mixed-pair capacity count relative
to the two-point complement of the two bases. -/
theorem two_base_line_capacity_impossible
    {Point : Type u} {Block : Type v} [Fintype Point] [Fintype Block]
    [DecidableEq Point]
    (S : BlockSystem Point Block) (hcard : Fintype.card Point = 10)
    (a b : LineBlock S)
    (ha : (S.support a.1).card = 4)
    (hb : (S.support b.1).card = 4)
    (hab : Disjoint (S.support a.1) (S.support b.1))
    (hthree : S.lineCount 3 = 9) : False := by
  classical
  let D : Finset Point := Finset.univ \ (S.support a.1 ∪ S.support b.1)
  let f : Block → ℕ := fun x =>
    (S.support x ∩ D).card * (S.support x \ D).card
  have hunion : (S.support a.1 ∪ S.support b.1).card = 8 := by
    rw [Finset.card_union_of_disjoint hab, ha, hb]
  have hD : D.card = 2 := by
    dsimp [D]
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _),
      Finset.card_univ, hcard, hunion]
  have hterm (x : Block) (hx : x ∈ S.lineBlocksOfSize 3) :
      2 ≤ f x := by
    have hxspec := S.mem_blocksOfKindSize.mp hx
    let ell : LineBlock S := ⟨x, hxspec.1⟩
    have hneA : ell ≠ a := by
      intro heq
      have hcards := congrArg (fun z : LineBlock S => (S.support z.1).card) heq
      change (S.support x).card = (S.support a.1).card at hcards
      rw [hxspec.2, ha] at hcards
      omega
    have hneB : ell ≠ b := by
      intro heq
      have hcards := congrArg (fun z : LineBlock S => (S.support z.1).card) heq
      change (S.support x).card = (S.support b.1).card at hcards
      rw [hxspec.2, hb] at hcards
      omega
    have hinterA := S.distinct_line_inter_card_lt_two hneA
    have hinterB := S.distinct_line_inter_card_lt_two hneB
    change (S.support x ∩ S.support a.1).card < 2 at hinterA
    change (S.support x ∩ S.support b.1).card < 2 at hinterB
    have houtside : S.support x \ D =
        S.support x ∩ (S.support a.1 ∪ S.support b.1) := by
      ext q
      simp only [D, Finset.mem_sdiff, Finset.mem_univ, true_and,
        Finset.mem_inter, Finset.mem_union]
      tauto
    have houtsideUnion : (S.support x \ D).card =
        ((S.support x ∩ S.support a.1) ∪
          (S.support x ∩ S.support b.1)).card := by
      have hinterUnion : S.support x ∩ (S.support a.1 ∪ S.support b.1) =
          (S.support x ∩ S.support a.1) ∪
            (S.support x ∩ S.support b.1) := by
        ext q
        simp only [Finset.mem_inter, Finset.mem_union]
        tauto
      rw [houtside, hinterUnion]
    have hout : (S.support x \ D).card ≤ 2 := by
      rw [houtsideUnion]
      calc
        ((S.support x ∩ S.support a.1) ∪
            (S.support x ∩ S.support b.1)).card ≤
            (S.support x ∩ S.support a.1).card +
              (S.support x ∩ S.support b.1).card := Finset.card_union_le _ _
        _ ≤ 2 := by omega
    have hins : (S.support x ∩ D).card ≤ 2 :=
      (Finset.card_le_card Finset.inter_subset_right).trans_eq hD
    have hsplit := Finset.card_inter_add_card_sdiff (S.support x) D
    rw [hxspec.2] at hsplit
    change 2 ≤ (S.support x ∩ D).card * (S.support x \ D).card
    have hinsCases : (S.support x ∩ D).card = 1 ∨
        (S.support x ∩ D).card = 2 := by
      omega
    rcases hinsCases with hinsOne | hinsTwo
    · have houtTwo : (S.support x \ D).card = 2 := by omega
      norm_num [hinsOne, houtTwo]
    · have houtOne : (S.support x \ D).card = 1 := by omega
      norm_num [hinsTwo, houtOne]
  have hsmall :
      2 * (S.lineBlocksOfSize 3).card ≤
        ∑ x ∈ S.lineBlocksOfSize 3, f x := by
    calc
      2 * (S.lineBlocksOfSize 3).card =
          ∑ x ∈ S.lineBlocksOfSize 3, 2 := by simp [Nat.mul_comm]
      _ ≤ ∑ x ∈ S.lineBlocksOfSize 3, f x := by
          apply Finset.sum_le_sum
          intro x hx
          exact hterm x hx
  have hsubset :
      (∑ x ∈ S.lineBlocksOfSize 3, f x) ≤
        ∑ x ∈ S.blocksOfKind .line, f x := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro x hx
      exact S.mem_blocksOfKind.mpr (S.mem_blocksOfKindSize.mp hx).1
    · intro x _hx _hnot
      exact Nat.zero_le _
  have hfull :
      (∑ x : LineBlock S, f x.1) =
        ∑ x ∈ S.blocksOfKind .line, f x := by
    simpa [BlockSystem.blocksOfKind] using
      (Finset.sum_subtype (S.blocksOfKind .line)
        (fun x => by simp [BlockSystem.blocksOfKind]) f).symm
  have hpartition := S.relative_line_pair_partition D 1 (by omega)
  rw [hcard, hD] at hpartition
  norm_num [Nat.choose] at hpartition
  have htotal : (∑ x : LineBlock S, f x.1) = 16 := by
    simpa [f] using hpartition
  have hcapacity : 18 ≤ ∑ x : LineBlock S, f x.1 := by
    have hbound := hsmall.trans hsubset
    have hthreeCard : (S.lineBlocksOfSize 3).card = 9 := by
      simpa [BlockSystem.lineCount] using hthree
    rw [hthreeCard] at hbound
    norm_num at hbound
    rw [← hfull] at hbound
    exact hbound
  omega

/-- The C40 singleton profile `(d₃,d₅) = (6,2)` is impossible when its two
size-five blocks through the pivot meet only there.  The local pair row gives
`d₄ = 9`; after inversion these become the two bases and the preceding
capacity theorem closes the case. -/
theorem elevenFive_c40_two_base_singleton_impossible
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    (cfg : Configuration Point) (hcard : Fintype.card Point = 11)
    (p : Point) (hlocal : ElevenFiveLocalRows (blockSystem cfg) p)
    (hthree : (blockSystem cfg).blockDegree 3 p = 6)
    (hfive : (blockSystem cfg).blockDegree 5 p = 2)
    {b c : GeometricBlock cfg}
    (hb : b ∈ (blockSystem cfg).blocksOfSize 5)
    (hc : c ∈ (blockSystem cfg).blocksOfSize 5)
    (hbp : p ∈ geometricBlockSupport cfg b)
    (hcp : p ∈ geometricBlockSupport cfg c)
    (hbc : b ≠ c)
    (hinter : (geometricBlockSupport cfg b ∩
      geometricBlockSupport cfg c).card = 1) : False := by
  classical
  have hfour : (blockSystem cfg).blockDegree 4 p = 9 := by
    have hpair := hlocal.pairRow
    omega
  let Q := pivotInversion cfg p
  let A := elevenFiveFivePivotLineOfSize cfg p b hb hbp
  let B := elevenFiveFivePivotLineOfSize cfg p c hc hcp
  let a : (blockSystem Q).LineBlock := ⟨.inl A.1, rfl⟩
  let d : (blockSystem Q).LineBlock := ⟨.inl B.1, rfl⟩
  have ha : ((blockSystem Q).support a.1).card = 4 := by
    change (lineSupport Q A.1).card = 4
    exact A.2
  have hd : ((blockSystem Q).support d.1).card = 4 := by
    change (lineSupport Q B.1).card = 4
    exact B.2
  have hA : lineSupport Q A.1 = awaySupport p (geometricBlockSupport cfg b) := by
    change lineSupport (pivotInversion cfg p)
      (blockToPivotLine cfg p (elevenFiveFivePivotBlock cfg p b hb hbp)) = _
    exact lineSupport_blockToPivotLine cfg p
      (elevenFiveFivePivotBlock cfg p b hb hbp)
  have hB : lineSupport Q B.1 = awaySupport p (geometricBlockSupport cfg c) := by
    change lineSupport (pivotInversion cfg p)
      (blockToPivotLine cfg p (elevenFiveFivePivotBlock cfg p c hc hcp)) = _
    exact lineSupport_blockToPivotLine cfg p
      (elevenFiveFivePivotBlock cfg p c hc hcp)
  have hpinter : p ∈ geometricBlockSupport cfg b ∩
      geometricBlockSupport cfg c := Finset.mem_inter.mpr ⟨hbp, hcp⟩
  have hawayZero :
      (awaySupport p (geometricBlockSupport cfg b ∩
        geometricBlockSupport cfg c)).card = 0 := by
    rw [card_awaySupport p _ hpinter, hinter]
  have hzero :
      (awaySupport p (geometricBlockSupport cfg b) ∩
        awaySupport p (geometricBlockSupport cfg c)).card = 0 := by
    rw [awaySupport_inter, hawayZero]
  have hadisjoint : Disjoint ((blockSystem Q).support a.1)
      ((blockSystem Q).support d.1) := by
    rw [Finset.disjoint_iff_inter_eq_empty]
    change lineSupport Q A.1 ∩ lineSupport Q B.1 = ∅
    rw [hA, hB]
    exact Finset.card_eq_zero.mp hzero
  have hinvcard : Fintype.card (AwayFrom p) = 10 := by
    rw [card_awayFrom, hcard]
  have hinvthree : (blockSystem Q).lineCount 3 = 9 := by
    change (blockSystem (pivotInversion cfg p)).lineCount 3 = 9
    rw [← blockDegree_eq_lineCount_pivotInversion cfg p 4 (by omega)]
    exact hfour
  exact two_base_line_capacity_impossible (blockSystem Q) hinvcard a d
    ha hd hadisjoint hinvthree

end Erdos506.V1
