import Erdos506.V1.ElevenFiveC40FinalK31Finite
import Erdos506.Incidence.ParameterizedThreeByThreeGridObstruction

/-!
# The finite capacity half of the K3.1 real tail

For the `(d₃,d₄,d₅) = (6,7,3)` K3.1 row no projective normalization is
needed after all.  Relative to the two disjoint four-lines, their third
path-line consumes four mixed pairs and each of the seven three-lines
consumes at least two.  This demands eighteen mixed pairs although the
two-point complement has capacity sixteen.
-/

namespace Erdos506.V1

open Erdos506.Block
open Erdos506.Block.BlockSystem
open Erdos506.Incidence
open Erdos506.V3
open Erdos506.V4
open scoped BigOperators

universe u v

/-- The two labels left outside a disjoint pair of four-lines. -/
noncomputable def twoBaseComplement
    {Point : Type u} {Block : Type v} [Fintype Point] [Fintype Block]
    [DecidableEq Point] (S : BlockSystem Point Block)
    (a b : LineBlock S) : Finset Point :=
  Finset.univ \ (S.support a.1 ∪ S.support b.1)

/-- Number of pairs of a line crossing between the two-base complement and
the union of the two bases. -/
noncomputable def twoBaseMixedPairCount
    {Point : Type u} {Block : Type v} [Fintype Point] [Fintype Block]
    [DecidableEq Point] (S : BlockSystem Point Block)
    (a b : LineBlock S) (x : Block) : ℕ :=
  (S.support x ∩ twoBaseComplement S a b).card *
    (S.support x \ twoBaseComplement S a b).card

/-- A disjoint pair of four-lines together with its path connector leaves
room for at most six, not seven, three-lines on ten labels. -/
theorem two_base_path_seven_three_line_capacity_impossible
    {Point : Type u} {Block : Type v} [Fintype Point] [Fintype Block]
    [DecidableEq Point]
    (S : BlockSystem Point Block) (hcard : Fintype.card Point = 10)
    (a b c : LineBlock S)
    (ha : (S.support a.1).card = 4)
    (hb : (S.support b.1).card = 4)
    (hc : (S.support c.1).card = 4)
    (hab : Disjoint (S.support a.1) (S.support b.1))
    (hca : (S.support c.1 ∩ S.support a.1).card = 1)
    (hcb : (S.support c.1 ∩ S.support b.1).card = 1)
    (hthree : S.lineCount 3 = 7) : False := by
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
  have hconnector : f c.1 = 4 := by
    have hdisjInter : Disjoint (S.support c.1 ∩ S.support a.1)
        (S.support c.1 ∩ S.support b.1) := by
      apply Finset.disjoint_left.mpr
      intro q hqa hqb
      exact Finset.disjoint_left.mp hab (Finset.mem_inter.mp hqa).2
        (Finset.mem_inter.mp hqb).2
    have hinterUnion : S.support c.1 ∩ (S.support a.1 ∪ S.support b.1) =
        (S.support c.1 ∩ S.support a.1) ∪
          (S.support c.1 ∩ S.support b.1) := by
      ext q
      simp only [Finset.mem_inter, Finset.mem_union]
      tauto
    have hcout : (S.support c.1 \ D).card = 2 := by
      have houtside : S.support c.1 \ D =
          S.support c.1 ∩ (S.support a.1 ∪ S.support b.1) := by
        ext q
        simp only [D, Finset.mem_sdiff, Finset.mem_univ, true_and,
          Finset.mem_inter, Finset.mem_union]
        tauto
      rw [houtside, hinterUnion, Finset.card_union_of_disjoint hdisjInter,
        hca, hcb]
    have hsplit := Finset.card_inter_add_card_sdiff (S.support c.1) D
    rw [hc, hcout] at hsplit
    change (S.support c.1 ∩ D).card * (S.support c.1 \ D).card = 4
    rw [hcout]
    omega
  have hcNotThree : c.1 ∉ S.lineBlocksOfSize 3 := by
    intro h
    have hspec := S.mem_blocksOfKindSize.mp h
    have hcards : (S.support c.1).card = 3 := hspec.2
    omega
  have hsubset :
      (insert c.1 (S.lineBlocksOfSize 3)) ⊆ S.blocksOfKind .line := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_union, Finset.mem_singleton] at hx
    rcases hx with rfl | hx
    · exact S.mem_blocksOfKind.mpr c.2
    · exact S.mem_blocksOfKind.mpr (S.mem_blocksOfKindSize.mp hx).1
  have hwithConnector :
      (∑ x ∈ insert c.1 (S.lineBlocksOfSize 3), f x) ≤
        ∑ x ∈ S.blocksOfKind .line, f x := by
    apply Finset.sum_le_sum_of_subset_of_nonneg hsubset
    intro x _hx _hnot
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
    have hthreeCard : (S.lineBlocksOfSize 3).card = 7 := by
      simpa [BlockSystem.lineCount] using hthree
    have htripleLower : 14 ≤ ∑ x ∈ S.lineBlocksOfSize 3, f x := by
      rw [hthreeCard] at hsmall
      norm_num at hsmall
      exact hsmall
    have hlower : 18 ≤ ∑ x ∈ insert c.1 (S.lineBlocksOfSize 3), f x := by
      rw [Finset.sum_insert hcNotThree, hconnector]
      omega
    have hbound := hlower.trans hwithConnector
    rw [← hfull] at hbound
    exact hbound
  omega

/-- The equality form of the second K3.1 capacity row.  If the disjoint
four-line path has exactly six three-lines, every one of those three-lines
uses exactly two mixed pairs.  Together with the connector's four pairs,
these twelve pairs exhaust the remaining capacity sixteen. -/
theorem two_base_path_six_three_line_mixed_saturation
    {Point : Type u} {Block : Type v} [Fintype Point] [Fintype Block]
    [DecidableEq Point]
    (S : BlockSystem Point Block) (hcard : Fintype.card Point = 10)
    (a b c : LineBlock S)
    (ha : (S.support a.1).card = 4)
    (hb : (S.support b.1).card = 4)
    (hc : (S.support c.1).card = 4)
    (hab : Disjoint (S.support a.1) (S.support b.1))
    (hca : (S.support c.1 ∩ S.support a.1).card = 1)
    (hcb : (S.support c.1 ∩ S.support b.1).card = 1)
    (hthree : S.lineCount 3 = 6) :
    ∀ x ∈ S.lineBlocksOfSize 3, twoBaseMixedPairCount S a b x = 2 := by
  classical
  let D := twoBaseComplement S a b
  let f : Block → ℕ := fun x => twoBaseMixedPairCount S a b x
  have hunion : (S.support a.1 ∪ S.support b.1).card = 8 := by
    rw [Finset.card_union_of_disjoint hab, ha, hb]
  have hD : D.card = 2 := by
    change (Finset.univ \ (S.support a.1 ∪ S.support b.1)).card = 2
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
      simp only [D, twoBaseComplement, Finset.mem_sdiff, Finset.mem_univ,
        true_and, Finset.mem_inter, Finset.mem_union]
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
      norm_num [f, twoBaseMixedPairCount, D, hinsOne, houtTwo]
    · have houtOne : (S.support x \ D).card = 1 := by omega
      norm_num [f, twoBaseMixedPairCount, D, hinsTwo, houtOne]
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
  have hconnector : f c.1 = 4 := by
    have hdisjInter : Disjoint (S.support c.1 ∩ S.support a.1)
        (S.support c.1 ∩ S.support b.1) := by
      apply Finset.disjoint_left.mpr
      intro q hqa hqb
      exact Finset.disjoint_left.mp hab (Finset.mem_inter.mp hqa).2
        (Finset.mem_inter.mp hqb).2
    have hinterUnion : S.support c.1 ∩ (S.support a.1 ∪ S.support b.1) =
        (S.support c.1 ∩ S.support a.1) ∪
          (S.support c.1 ∩ S.support b.1) := by
      ext q
      simp only [Finset.mem_inter, Finset.mem_union]
      tauto
    have hcout : (S.support c.1 \ D).card = 2 := by
      have houtside : S.support c.1 \ D =
          S.support c.1 ∩ (S.support a.1 ∪ S.support b.1) := by
        ext q
        simp only [D, twoBaseComplement, Finset.mem_sdiff, Finset.mem_univ,
          true_and, Finset.mem_inter, Finset.mem_union]
        tauto
      rw [houtside, hinterUnion, Finset.card_union_of_disjoint hdisjInter,
        hca, hcb]
    have hsplit := Finset.card_inter_add_card_sdiff (S.support c.1) D
    rw [hc, hcout] at hsplit
    change f c.1 = 4
    change (S.support c.1 ∩ D).card * (S.support c.1 \ D).card = 4
    rw [hcout]
    omega
  have hcNotThree : c.1 ∉ S.lineBlocksOfSize 3 := by
    intro h
    have hspec := S.mem_blocksOfKindSize.mp h
    have hcards : (S.support c.1).card = 3 := hspec.2
    omega
  have hsubset :
      (insert c.1 (S.lineBlocksOfSize 3)) ⊆ S.blocksOfKind .line := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_union, Finset.mem_singleton] at hx
    rcases hx with rfl | hx
    · exact S.mem_blocksOfKind.mpr c.2
    · exact S.mem_blocksOfKind.mpr (S.mem_blocksOfKindSize.mp hx).1
  have hwithConnector :
      (∑ x ∈ insert c.1 (S.lineBlocksOfSize 3), f x) ≤
        ∑ x ∈ S.blocksOfKind .line, f x := by
    apply Finset.sum_le_sum_of_subset_of_nonneg hsubset
    intro x _hx _hnot
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
    simpa [f, twoBaseMixedPairCount] using hpartition
  have hthreeCard : (S.lineBlocksOfSize 3).card = 6 := by
    simpa [BlockSystem.lineCount] using hthree
  have hsumLower : 12 ≤ ∑ x ∈ S.lineBlocksOfSize 3, f x := by
    rw [hthreeCard] at hsmall
    norm_num at hsmall
    exact hsmall
  have hsumUpper : (∑ x ∈ S.lineBlocksOfSize 3, f x) ≤ 12 := by
    have hbound := hwithConnector
    rw [Finset.sum_insert hcNotThree, hconnector, ← hfull, htotal] at hbound
    omega
  have hsum : (∑ x ∈ S.lineBlocksOfSize 3, f x) = 12 := by omega
  intro x hx
  change f x = 2
  have hconst : (∑ y ∈ S.lineBlocksOfSize 3, 2) =
      ∑ y ∈ S.lineBlocksOfSize 3, f y := by
    rw [hsum]
    simp [hthreeCard]
  exact (Finset.sum_eq_sum_iff_of_le
    (fun y hy => hterm y hy)).mp hconst x hx |>.symm

/-- The coordinate endpoint of the `d₃=9` K3.1 grid tail.  Once one
middle line is the diagonal of a parameterized `3×3` grid, an edge-disjoint
second middle line is one of the two derangements.  With the common third
coordinate parameter forced by the two shared connector pencils, both
determinants have the strictly positive form `t²+t+1`. -/
theorem parameterized_threeByThreeGrid_diagonal_no_disjoint_transversal
    {t : ℝ}
    (hthree : ParameterizedThreeByThreeGridTransversal t t 3 ∨
      ParameterizedThreeByThreeGridTransversal t t 4) : False := by
  rcases hthree with h3 | h4
  · rw [ParameterizedThreeByThreeGridTransversal,
      parameterizedThreeByThreeTransversal_determinant_eq_polynomial] at h3
    have h3' : -t * t - t - 1 = 0 := by
      simpa [parameterizedThreeByThreeTransversalPolynomial] using h3
    have hsq := sq_nonneg (t + (1 / 2 : ℝ))
    nlinarith
  · rw [ParameterizedThreeByThreeGridTransversal,
      parameterizedThreeByThreeTransversal_determinant_eq_polynomial] at h4
    have h4' : t * t + t + 1 = 0 := by
      simpa [parameterizedThreeByThreeTransversalPolynomial] using h4
    have hsq := sq_nonneg (t + (1 / 2 : ℝ))
    nlinarith

/-- The `(d₃,d₅) = (6,3)` K3.1 singleton carrier is impossible.

The finite K3.1 extraction produces its disjoint-path triple after inversion;
the seven three-lines in this row then contradict the preceding mixed-pair
capacity theorem. -/
theorem elevenFive_threeFive_six_singleton_impossible
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    (cfg : Configuration Point) (hcard : Fintype.card Point = 11)
    (p : Point) (hlocal : ElevenFiveLocalRows (blockSystem cfg) p)
    (hthree : (blockSystem cfg).blockDegree 3 p = 6)
    (hfive : (blockSystem cfg).blockDegree 5 p = 3)
    {b d : GeometricBlock cfg}
    (hb : b ∈ (blockSystem cfg).blocksOfSize 5)
    (hd : d ∈ (blockSystem cfg).blocksOfSize 5)
    (hbp : p ∈ geometricBlockSupport cfg b)
    (hdp : p ∈ geometricBlockSupport cfg d) (hbd : b ≠ d)
    (hinter : (geometricBlockSupport cfg b ∩
      geometricBlockSupport cfg d).card = 1) : False := by
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
  have hinvthree : (blockSystem Q).lineCount 3 = 7 := by
    rcases (elevenFive_threeFive_k31_inverted_census cfg p hlocal
      (Or.inl hthree) hfive).1 with h6 | h9
    · exact h6.2
    · omega
  obtain ⟨e, he, hea, hed, heA, heC⟩ :=
    elevenFive_threeFive_singleton_inverted_path
      cfg hcard p hfive hb hd hbp hdp hbd hinter
  change ((blockSystem Q).support e.1 ∩ (blockSystem Q).support a.1).card = 1 at heA
  change ((blockSystem Q).support e.1 ∩ (blockSystem Q).support d'.1).card = 1 at heC
  exact two_base_path_seven_three_line_capacity_impossible
    (blockSystem Q) hinvcard a d' e ha hd' he hab heA heC hinvthree

end Erdos506.V1
