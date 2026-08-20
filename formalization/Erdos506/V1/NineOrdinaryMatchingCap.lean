import Erdos506.V1.DeletionLineCensus

/-!
# The nine-point ordinary-line matching cap

For a nine-point real configuration with line profile `(t₂,t₃)=(6,10)`,
pair ownership leaves no line of size at least four.  Delete any vertex.
The exact deletion census and the local line-arm row express the new number
of ordinary lines in terms of the original ordinary degree.  Melchior makes
the deleted slack nonnegative, while the even-arrangement principle excludes
slack one.  Consequently every original ordinary degree is zero or two.

Four pairwise disjoint ordinary lines would then cover eight vertices, each
of ordinary degree two, contradicting the global degree sum `2t₂=12`.  The
final theorem transports this cap back through pivot inversion: at a
ten-point pivot with `(d₃,d₄)=(6,10)`, at most three original three-lines can
pass through the pivot.
-/

namespace Erdos506.V1

open Erdos506.Block
open Erdos506.Block.BlockSystem
open Erdos506.Finite
open Erdos506.Incidence
open Erdos506.V3
open Erdos506.V4
open scoped BigOperators

universe u

/-! ## The `(6,10)` profile has a three-point line cap -/

private theorem lineCount_pos_of_determinedLine
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    (cfg : Configuration Point) (L : DeterminedLine cfg) (s : Nat)
    (hL : (lineSupport cfg L).card = s) :
    0 < (blockSystem cfg).lineCount s := by
  change 0 < ((blockSystem cfg).lineBlocksOfSize s).card
  apply Finset.card_pos.mpr
  refine ⟨Sum.inl L, ?_⟩
  exact (blockSystem cfg).mem_blocksOfKindSize.mpr ⟨rfl, hL⟩

/-- The counts `t₂=6,t₃=10` already spend all `choose(9,2)=36` pairs. -/
theorem ninePoint_line_cap_three_of_line_profile
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    (cfg : Configuration Point) (hcard : Fintype.card Point = 9)
    (htwo : (blockSystem cfg).lineCount 2 = 6)
    (hthree : (blockSystem cfg).lineCount 3 = 10) :
    ∀ L : DeterminedLine cfg, (lineSupport cfg L).card ≤ 3 := by
  classical
  have hpairs := (blockSystem cfg).line_pair_partition_by_size
  rw [hcard] at hpairs
  norm_num [Finset.sum_range_succ, Nat.choose, htwo, hthree] at hpairs
  intro L
  have hmin := two_le_lineSupport_card cfg L
  have hupper : (lineSupport cfg L).card ≤ Fintype.card Point :=
    Finset.card_le_univ _
  rw [hcard] at hupper
  by_contra hnot
  have hlower : 4 ≤ (lineSupport cfg L).card := by omega
  interval_cases hsize : (lineSupport cfg L).card <;>
    have hpos := lineCount_pos_of_determinedLine cfg L _ hsize <;>
    omega

private theorem lineCount_eq_zero_of_line_cap_three
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    (cfg : Configuration Point)
    (hcap : ∀ L : DeterminedLine cfg, (lineSupport cfg L).card ≤ 3)
    (s : Nat) (hs : 3 < s) :
    (blockSystem cfg).lineCount s = 0 := by
  classical
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro b hb
  have hspec := (blockSystem cfg).mem_blocksOfKindSize.mp hb
  cases b with
  | inl L =>
      have hupper := hcap L
      have hsize := hspec.2
      change (lineSupport cfg L).card = s at hsize
      omega
  | inr c => cases hspec.1

private theorem lineDegree_eq_zero_of_line_cap_three
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    (cfg : Configuration Point)
    (hcap : ∀ L : DeterminedLine cfg, (lineSupport cfg L).card ≤ 3)
    (p : Point) (s : Nat) (hs : 3 < s) :
    (blockSystem cfg).lineDegree s p = 0 := by
  have hzero := lineCount_eq_zero_of_line_cap_three cfg hcap s hs
  have hle : (blockSystem cfg).lineDegree s p ≤
      (blockSystem cfg).lineCount s := by
    unfold BlockSystem.lineDegree BlockSystem.degreeIn BlockSystem.lineCount
    exact Finset.card_filter_le _ _
  omega

/-! ## Melchior slack under the line cap -/

/-- Under a three-point line cap, every determined line has size two or
three. -/
private noncomputable def determinedLineEquivTwoOrThree
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    (cfg : Configuration Point)
    (hcap : ∀ L : DeterminedLine cfg, (lineSupport cfg L).card ≤ 3) :
    DeterminedLine cfg ≃
      DeterminedLineOfSize cfg 2 ⊕ DeterminedLineOfSize cfg 3 where
  toFun L := if htwo : (lineSupport cfg L).card = 2 then
      .inl ⟨L, htwo⟩
    else .inr ⟨L, by
      have hmin := two_le_lineSupport_card cfg L
      have hupper := hcap L
      omega⟩
  invFun
    | .inl L => L.1
    | .inr L => L.1
  left_inv L := by
    by_cases htwo : (lineSupport cfg L).card = 2
    · simp only [dif_pos htwo]
    · simp only [dif_neg htwo]
  right_inv L := by
    cases L with
    | inl L => simp [L.2]
    | inr L =>
        simp only
        split
        · rename_i htwo
          omega
        · rfl

private theorem lineMelchiorSlack_eq_lineCount_two_sub_three_of_line_cap
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    (cfg : Configuration Point)
    (hcap : ∀ L : DeterminedLine cfg, (lineSupport cfg L).card ≤ 3) :
    lineMelchiorSlack cfg =
      ((blockSystem cfg).lineCount 2 : Int) - 3 := by
  classical
  let e := determinedLineEquivTwoOrThree cfg hcap
  let weight : DeterminedLineOfSize cfg 2 ⊕
      DeterminedLineOfSize cfg 3 → Int
    | .inl L => 3 - ((lineSupport cfg L.1).card : Int)
    | .inr L => 3 - ((lineSupport cfg L.1).card : Int)
  have hsum :
      (∑ L : DeterminedLine cfg,
          (3 - ((lineSupport cfg L).card : Int))) =
        ∑ L : DeterminedLineOfSize cfg 2 ⊕
            DeterminedLineOfSize cfg 3, weight L := by
    apply Fintype.sum_equiv e
    intro L
    cases he : e L with
    | inl Ltwo =>
        have hinv := congrArg e.invFun he
        change e.invFun (e L) = Ltwo.1 at hinv
        have hL : L = Ltwo.1 := (e.left_inv L).symm.trans hinv
        rw [hL]
    | inr Lthree =>
        have hinv := congrArg e.invFun he
        change e.invFun (e L) = Lthree.1 at hinv
        have hL : L = Lthree.1 := (e.left_inv L).symm.trans hinv
        rw [hL]
  have htwoSum :
      (∑ L : DeterminedLineOfSize cfg 2, weight (.inl L)) =
        (Fintype.card (DeterminedLineOfSize cfg 2) : Int) := by
    calc
      (∑ L : DeterminedLineOfSize cfg 2, weight (.inl L)) =
          ∑ _L : DeterminedLineOfSize cfg 2, (1 : Int) := by
        apply Fintype.sum_congr
        intro L
        dsimp only [weight]
        rw [L.2]
        norm_num
      _ = (Fintype.card (DeterminedLineOfSize cfg 2) : Int) := by simp
  have hthreeSum :
      (∑ L : DeterminedLineOfSize cfg 3, weight (.inr L)) = 0 := by
    calc
      (∑ L : DeterminedLineOfSize cfg 3, weight (.inr L)) =
          ∑ _L : DeterminedLineOfSize cfg 3, (0 : Int) := by
        apply Fintype.sum_congr
        intro L
        dsimp only [weight]
        rw [L.2]
        norm_num
      _ = 0 := by simp
  unfold lineMelchiorSlack
  rw [hsum, Fintype.sum_sum_type, htwoSum, hthreeSum]
  simp only [add_zero]
  rw [← lineCount_eq_card_determinedLineOfSize cfg 2]

/-! ## Every ordinary degree is zero or two -/

/-- Vertex form of the nine-point ordinary matching cap. -/
theorem ninePoint_ordinary_line_degree_eq_zero_or_two
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    (Mel : RealPlaneMelchiorPrinciple.{u})
    (EvenArr : RealPlaneEvenArrangementPrinciple.{u})
    (cfg : Configuration Point) (hcard : Fintype.card Point = 9)
    (hcap : ∀ L : DeterminedLine cfg, (lineSupport cfg L).card ≤ 3)
    (htwo : (blockSystem cfg).lineCount 2 = 6)
    (hthree : (blockSystem cfg).lineCount 3 = 10)
    (p : Point) :
    (blockSystem cfg).lineDegree 2 p = 0 ∨
      (blockSystem cfg).lineDegree 2 p = 2 := by
  let S := blockSystem cfg
  let del := deletePointConfiguration cfg p
  have hld4 := lineDegree_eq_zero_of_line_cap_three cfg hcap p 4 (by omega)
  have hld5 := lineDegree_eq_zero_of_line_cap_three cfg hcap p 5 (by omega)
  have hld6 := lineDegree_eq_zero_of_line_cap_three cfg hcap p 6 (by omega)
  have hld7 := lineDegree_eq_zero_of_line_cap_three cfg hcap p 7 (by omega)
  have hld8 := lineDegree_eq_zero_of_line_cap_three cfg hcap p 8 (by omega)
  have hld9 := lineDegree_eq_zero_of_line_cap_three cfg hcap p 9 (by omega)
  have harms := S.line_arms p
  rw [hcard] at harms
  norm_num [S, Finset.sum_range_succ,
    hld4, hld5, hld6, hld7, hld8, hld9] at harms
  have harms' :
      S.lineDegree 2 p + 2 * S.lineDegree 3 p = 8 := by
    simpa only [S] using harms
  have hdeletedTwo := lineCount_two_deletePointConfiguration cfg p
  rw [htwo] at hdeletedTwo
  have hdeletedThree :=
    lineCount_three_deletePointConfiguration_of_line_cap_three cfg p hcap
  rw [hthree] at hdeletedThree
  have hdelCard : Fintype.card (AwayFrom p) = 8 := by
    rw [card_awayFrom, hcard]
  have hdelCap : ∀ L : DeterminedLine del,
      (lineSupport del L).card ≤ 3 := by
    simpa [del] using line_cap_three_deletePointConfiguration cfg p hcap
  have hdelNoncol : Noncollinear del := by
    apply deletePointConfiguration_noncollinear_of_line_cap cfg p
    · omega
    · intro L
      exact (hcap L).trans (by omega)
  have hmel : LineMelchior del := Mel.lineMelchior del hdelNoncol
  have hslackNonneg : 0 ≤ lineMelchiorSlack del :=
    (lineMelchior_iff_slack_nonneg del).mp hmel
  have heven : Even (Fintype.card (AwayFrom p)) := by
    rw [hdelCard]
    norm_num
  have hslackNe : lineMelchiorSlack del ≠ 1 :=
    EvenArr.slack_ne_one del hdelNoncol heven
  have hslackEq :=
    lineMelchiorSlack_eq_lineCount_two_sub_three_of_line_cap del hdelCap
  rw [hslackEq] at hslackNonneg hslackNe
  change S.lineDegree 2 p = 0 ∨ S.lineDegree 2 p = 2
  change (blockSystem del).lineCount 2 =
    6 - S.lineDegree 2 p + S.lineDegree 3 p at hdeletedTwo
  change (blockSystem del).lineCount 3 =
    10 - S.lineDegree 3 p at hdeletedThree
  omega

/-! ## Four disjoint ordinary lines are impossible -/

private theorem lineDegree_pos_of_mem_determinedLineOfSize
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    (cfg : Configuration Point) (p : Point) (s : Nat)
    (L : DeterminedLineOfSize cfg s) (hp : p ∈ lineSupport cfg L.1) :
    0 < (blockSystem cfg).lineDegree s p := by
  change 0 < (((blockSystem cfg).lineBlocksOfSize s).filter fun b =>
    p ∈ (blockSystem cfg).support b).card
  apply Finset.card_pos.mpr
  refine ⟨Sum.inl L.1, Finset.mem_filter.mpr ⟨?_, ?_⟩⟩
  · exact (blockSystem cfg).mem_blocksOfKindSize.mpr ⟨rfl, L.2⟩
  · exact hp

/-- Regard a three-point original line through `p` as a pivot block. -/
private noncomputable def matchingCapTaggedThreeLinePivotBlock
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (b : TaggedLineAtSize cfg p 3) : PivotBlock cfg p :=
  ⟨b.1, b.2.2.2, by rw [b.2.2.1]⟩

/-- A three-point original line through the pivot becomes an ordinary line
of the nine-point inversion. -/
private noncomputable def matchingCapInvertedOrdinaryLine
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (b : TaggedLineAtSize cfg p 3) :
    DeterminedLineOfSize (pivotInversion cfg p) 2 := by
  let pb := matchingCapTaggedThreeLinePivotBlock b
  refine ⟨blockToPivotLine cfg p pb, ?_⟩
  rw [card_lineSupport_blockToPivotLine]
  change (geometricBlockSupport cfg b.1).card - 1 = 2
  rw [b.2.2.1]

private theorem lineSupport_matchingCapInvertedOrdinaryLine
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (b : TaggedLineAtSize cfg p 3) :
    lineSupport (pivotInversion cfg p)
        (matchingCapInvertedOrdinaryLine b).1 =
      awaySupport p (geometricBlockSupport cfg b.1) := by
  change lineSupport (pivotInversion cfg p)
      (blockToPivotLine cfg p
        (matchingCapTaggedThreeLinePivotBlock b)) = _
  exact lineSupport_blockToPivotLine cfg p
    (matchingCapTaggedThreeLinePivotBlock b)

/-- Distinct original lines through `p` have disjoint away-supports. -/
private theorem matchingCapInvertedOrdinaryLines_disjoint
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    {b c : TaggedLineAtSize cfg p 3} (hbc : b ≠ c) :
    Disjoint
      (lineSupport (pivotInversion cfg p)
        (matchingCapInvertedOrdinaryLine b).1)
      (lineSupport (pivotInversion cfg p)
        (matchingCapInvertedOrdinaryLine c).1) := by
  classical
  rw [lineSupport_matchingCapInvertedOrdinaryLine,
    lineSupport_matchingCapInvertedOrdinaryLine]
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

/-! ## The ten-point exceptional-pivot cap -/

/-- At the exceptional ten-point row `(d₃,d₄)=(6,10)`, at most three
original three-lines pass through the pivot. -/
theorem tenExceptionalPivot_lineDegree_three_le_three
    {alpha : Type u} [Fintype alpha] [DecidableEq alpha]
    (Mel : RealPlaneMelchiorPrinciple.{u})
    (EvenArr : RealPlaneEvenArrangementPrinciple.{u})
    (cfg : Configuration alpha) (hadm : Admissible cfg)
    (hcard : Fintype.card alpha = 10) (p : alpha)
    (hd3 : (blockSystem cfg).blockDegree 3 p = 6)
    (hd4 : (blockSystem cfg).blockDegree 4 p = 10) :
    (blockSystem cfg).lineDegree 3 p ≤ 3 := by
  classical
  let inv := pivotInversion cfg p
  let S := blockSystem inv
  have hinvCard : Fintype.card (AwayFrom p) = 9 := by
    rw [card_awayFrom, hcard]
  have _hinvNoncol : Noncollinear inv := by
    simpa [inv] using pivotInversion_noncollinear cfg hadm (by omega) p
  have htwo : S.lineCount 2 = 6 := by
    change (blockSystem (pivotInversion cfg p)).lineCount 2 = 6
    rw [← blockDegree_eq_lineCount_pivotInversion
      cfg p 3 (by omega)]
    exact hd3
  have hthree : S.lineCount 3 = 10 := by
    change (blockSystem (pivotInversion cfg p)).lineCount 3 = 10
    rw [← blockDegree_eq_lineCount_pivotInversion
      cfg p 4 (by omega)]
    exact hd4
  have hcap : ∀ L : DeterminedLine inv,
      (lineSupport inv L).card ≤ 3 := by
    simpa [inv] using
      ninePoint_line_cap_three_of_line_profile inv hinvCard htwo hthree
  have hdegree (x : AwayFrom p) :
      S.lineDegree 2 x = 0 ∨ S.lineDegree 2 x = 2 := by
    simpa [S, inv] using
      ninePoint_ordinary_line_degree_eq_zero_or_two
        Mel EvenArr inv hinvCard hcap htwo hthree x
  by_contra hnot
  have hfour : 4 ≤ (blockSystem cfg).lineDegree 3 p := by omega
  have htagCard :
      4 ≤ Fintype.card (TaggedLineAtSize cfg p 3) := by
    rw [← lineDegree_eq_card_taggedLineAtSize]
    exact hfour
  let all : Finset (TaggedLineAtSize cfg p 3) := Finset.univ
  have hallCard : 4 ≤ all.card := by
    simpa [all] using htagCard
  obtain ⟨chosen, _hchosenSub, hchosenCard⟩ :=
    Finset.exists_subset_card_eq hallCard
  have hchosenType : Fintype.card ↥chosen = 4 := by
    simpa using hchosenCard
  let label : Fin 4 ≃ ↥chosen :=
    (Fintype.equivFinOfCardEq hchosenType).symm
  let B : Fin 4 → TaggedLineAtSize cfg p 3 := fun i => (label i).1
  have hBinj : Function.Injective B := by
    intro i j hij
    apply label.injective
    apply Subtype.ext
    exact hij
  let edge : Fin 4 → DeterminedLineOfSize inv 2 := fun i =>
    matchingCapInvertedOrdinaryLine (B i)
  let edgeSupport : Fin 4 → Finset (AwayFrom p) := fun i =>
    lineSupport inv (edge i).1
  let U : Finset (AwayFrom p) :=
    (Finset.univ : Finset (Fin 4)).biUnion edgeSupport
  have hpairwise :
      ((Finset.univ : Finset (Fin 4)) : Set (Fin 4)).PairwiseDisjoint
        edgeSupport := by
    intro i _hi j _hj hij
    exact matchingCapInvertedOrdinaryLines_disjoint
      (hBinj.ne hij)
  have hUcard : U.card = 8 := by
    unfold U
    rw [Finset.card_biUnion hpairwise]
    calc
      (∑ i ∈ (Finset.univ : Finset (Fin 4)), (edgeSupport i).card) =
          ∑ _i ∈ (Finset.univ : Finset (Fin 4)), 2 := by
        apply Finset.sum_congr rfl
        intro i _hi
        exact (edge i).2
      _ = 8 := by norm_num
  have hdegreeTwo (x : AwayFrom p) (hx : x ∈ U) :
      S.lineDegree 2 x = 2 := by
    have hpos : 0 < S.lineDegree 2 x := by
      obtain ⟨i, _hi, hxi⟩ := Finset.mem_biUnion.mp hx
      exact lineDegree_pos_of_mem_determinedLineOfSize
        inv x 2 (edge i) hxi
    rcases hdegree x with hzero | htwoDegree
    · omega
    · exact htwoDegree
  have hsumU : (∑ x ∈ U, S.lineDegree 2 x) = 16 := by
    calc
      (∑ x ∈ U, S.lineDegree 2 x) = ∑ _x ∈ U, 2 := by
        apply Finset.sum_congr rfl
        intro x hx
        exact hdegreeTwo x hx
      _ = 2 * U.card := by simp [Nat.mul_comm]
      _ = 16 := by rw [hUcard]
  have hsumLe : (∑ x ∈ U, S.lineDegree 2 x) ≤
      ∑ x : AwayFrom p, S.lineDegree 2 x := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · simp
    · intro x _hx _hnot
      exact Nat.zero_le _
  have hinc := S.line_incidence 2
  rw [htwo] at hinc
  norm_num at hinc
  omega

end Erdos506.V1
