import Erdos506.Incidence.RealProjectiveArrangementKellyMoserOuterFinal
import Erdos506.Incidence.RealProjectiveArrangementKellyMoserDegreeOneAttachmentFinish
import Erdos506.V1.DeletionLineCensus
import Erdos506.V1.UniversalRows

/-!
# The finite Kelly--Moser range used by V1

The V1 call graph only asks for ordinary-line bounds on configurations of
cardinality `9`, `10`, `11`, and `12`.  This file isolates those four finite
statements.  In particular, it does not manufacture a universal
`RealPlaneKellyMoserPrinciple` outside that range.
-/

namespace Erdos506.Incidence

open Erdos506.Block
open Erdos506.Block.BlockSystem
open Erdos506.V1
open Erdos506.V4
open scoped BigOperators

universe u

/-- Pure weak Kelly count.  Degree-zero lines contribute three attachments;
degree-one lines contribute one attachment, and degrees one or two consume
one of the two ordinary incidences at every ordinary vertex. -/
private theorem weakKelly_count
    {Vertex Line : Type*} [Fintype Vertex] [Fintype Line]
    (ordinary attached : Vertex → Line → Prop)
    (hordinary : ∀ x : Vertex,
      finiteRelationLeftDegree ordinary x = 2)
    (hattached : ∀ x : Vertex,
      finiteRelationLeftDegree attached x ≤ 4)
    (hzero : ∀ l : Line,
      finiteRelationRightDegree ordinary l = 0 →
        3 ≤ finiteRelationRightDegree attached l)
    (hone : ∀ l : Line,
      finiteRelationRightDegree ordinary l = 1 →
        1 ≤ finiteRelationRightDegree attached l) :
    3 * Fintype.card Line ≤ 8 * Fintype.card Vertex := by
  classical
  let small : Finset Line := Finset.univ.filter fun l =>
    finiteRelationRightDegree ordinary l = 1 ∨
      finiteRelationRightDegree ordinary l = 2
  have hordinarySum :
      (∑ l : Line, finiteRelationRightDegree ordinary l) =
        2 * Fintype.card Vertex := by
    rw [sum_finiteRelationRightDegree_eq_sum_finiteRelationLeftDegree]
    calc
      (∑ x : Vertex, finiteRelationLeftDegree ordinary x) =
          ∑ _x : Vertex, 2 := by
        apply Finset.sum_congr rfl
        intro x _hx
        exact hordinary x
      _ = 2 * Fintype.card Vertex := by simp [mul_comm]
  have hattachedSum :
      (∑ l : Line, finiteRelationRightDegree attached l) ≤
        4 * Fintype.card Vertex := by
    rw [sum_finiteRelationRightDegree_eq_sum_finiteRelationLeftDegree]
    calc
      (∑ x : Vertex, finiteRelationLeftDegree attached x) ≤
          ∑ _x : Vertex, 4 := by
        exact Finset.sum_le_sum fun x _hx => hattached x
      _ = 4 * Fintype.card Vertex := by simp [mul_comm]
  have hsmallCard : small.card ≤ 2 * Fintype.card Vertex := by
    calc
      small.card = ∑ _l ∈ small, 1 := by simp
      _ ≤ ∑ l ∈ small, finiteRelationRightDegree ordinary l := by
        apply Finset.sum_le_sum
        intro l hl
        have hl' := (Finset.mem_filter.mp hl).2
        omega
      _ ≤ ∑ l : Line, finiteRelationRightDegree ordinary l := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · exact Finset.filter_subset _ _
        · intro l _hl _hnot
          exact Nat.zero_le _
      _ = 2 * Fintype.card Vertex := hordinarySum
  have hline (l : Line) :
      3 ≤ finiteRelationRightDegree ordinary l +
        finiteRelationRightDegree attached l +
          (if finiteRelationRightDegree ordinary l = 1 ∨
              finiteRelationRightDegree ordinary l = 2 then 1 else 0) := by
    by_cases h0 : finiteRelationRightDegree ordinary l = 0
    · have ha := hzero l h0
      simp [h0]
      omega
    by_cases h1 : finiteRelationRightDegree ordinary l = 1
    · have ha := hone l h1
      simp [h1]
      omega
    by_cases h2 : finiteRelationRightDegree ordinary l = 2
    · simp [h1, h2]
    · simp [h1, h2]
      omega
  have htotal :
      3 * Fintype.card Line ≤
        (∑ l : Line, finiteRelationRightDegree ordinary l) +
          (∑ l : Line, finiteRelationRightDegree attached l) +
            small.card := by
    calc
      3 * Fintype.card Line = ∑ _l : Line, 3 := by simp [mul_comm]
      _ ≤ ∑ l : Line,
          (finiteRelationRightDegree ordinary l +
            finiteRelationRightDegree attached l +
              (if finiteRelationRightDegree ordinary l = 1 ∨
                  finiteRelationRightDegree ordinary l = 2 then 1 else 0)) := by
        exact Finset.sum_le_sum fun l _hl => hline l
      _ = (∑ l : Line, finiteRelationRightDegree ordinary l) +
          (∑ l : Line, finiteRelationRightDegree attached l) +
            small.card := by
        simp only [Finset.sum_add_distrib]
        simp [small]
  omega

private theorem defect_one_profile
    (a b c d e f g : ℕ)
    (h : a + 2 * b + 3 * c + 4 * d + 5 * e + 6 * f + 7 * g = 1) :
    a = 1 ∧ b = 0 ∧ c = 0 ∧ d = 0 ∧ e = 0 ∧ f = 0 ∧ g = 0 := by
  omega

private theorem defect_zero_profile
    (a b c d e f g h i : ℕ)
    (hz : a + 2 * b + 3 * c + 4 * d + 5 * e + 6 * f +
      7 * g + 8 * h + 9 * i = 0) :
    a = 0 ∧ b = 0 ∧ c = 0 ∧ d = 0 ∧ e = 0 ∧
      f = 0 ∧ g = 0 ∧ h = 0 ∧ i = 0 := by
  omega

private theorem twelve_defect_two_profile
    (t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 : ℕ)
    (hpair : 5 + 3 * t3 + 6 * t4 + 10 * t5 + 15 * t6 +
      21 * t7 + 28 * t8 + 36 * t9 + 45 * t10 + 55 * t11 +
      66 * t12 = 66)
    (hdefect : t4 + 2 * t5 + 3 * t6 + 4 * t7 + 5 * t8 +
      6 * t9 + 7 * t10 + 8 * t11 + 9 * t12 = 2) :
    t4 = 0 ∧ t5 = 1 ∧ t6 = 0 ∧ t7 = 0 ∧ t8 = 0 ∧
      t9 = 0 ∧ t10 = 0 ∧ t11 = 0 ∧ t12 = 0 := by
  have ht6 : t6 = 0 := by omega
  have ht7 : t7 = 0 := by omega
  have ht8 : t8 = 0 := by omega
  have ht9 : t9 = 0 := by omega
  have ht10 : t10 = 0 := by omega
  have ht11 : t11 = 0 := by omega
  have ht12 : t12 = 0 := by omega
  norm_num [ht6, ht7, ht8, ht9, ht10, ht11, ht12] at hpair hdefect
  have ht5 : t5 = 1 := by omega
  have ht4 : t4 = 0 := by omega
  exact ⟨ht4, ht5, ht6, ht7, ht8, ht9, ht10, ht11, ht12⟩

/-- The unconditional weak projective Kelly count, transported through the
label duality.  Its integral rounding already settles the odd sizes in the
finite V1 window and leaves only one extremal value at each even size. -/
private theorem weakKelly_lineCount_two
    {alpha : Type u} [Fintype alpha] [DecidableEq alpha]
    (cfg : Configuration alpha) (hnon : Noncollinear cfg) :
    3 * Fintype.card alpha <= 8 * (blockSystem cfg).lineCount 2 := by
  let A := labelDualArrangement cfg
  have hA : A.NonPencil := by
    simpa [A] using labelDualArrangement_nonPencil_of_noncollinear cfg hnon
  have hthreeCard := A.three_le_card_of_nonPencil hA
  have hweak :
      3 * Fintype.card alpha <= 8 * Fintype.card A.OrdinaryVertex := by
    by_cases hfour : 4 <= Fintype.card alpha
    · by_cases hhigh : ∀ l : alpha, 3 <= (A.lineVertexSet l).card
      · apply weakKelly_count
          (fun q : A.OrdinaryVertex => A.Incident q.1)
          A.OrdinaryVertexAttachedToLine
        · exact A.ordinaryVertexLineDegree_eq_two
        · exact A.ordinaryVertexAttachmentDegree_le_four hA
        · intro l hzero
          exact A.three_le_lineOrdinaryAttachmentDegree_of_degree_zero
            hA l (hhigh l) hzero
        · intro l hone
          exact A.one_le_lineOrdinaryAttachmentDegree_of_degree_one_highLine
            hA l (hhigh l) hone
      · push_neg at hhigh
        obtain ⟨l, hlow⟩ := hhigh
        have hstrong :=
          A.three_mul_card_le_seven_mul_card_ordinaryVertex_of_lineVertexSet_card_le_two
            hA hfour l (by omega)
        change 3 * Fintype.card alpha <=
          7 * Fintype.card A.OrdinaryVertex at hstrong
        omega
    · have hcardA : Fintype.card alpha = 3 := by omega
      have hstrong :=
        A.three_mul_card_le_seven_mul_card_ordinaryVertex_of_card_eq_three
          hA (by simpa [A] using hcardA)
      change 3 * Fintype.card alpha <=
        7 * Fintype.card A.OrdinaryVertex at hstrong
      omega
  change 3 * Fintype.card alpha <=
    8 * Fintype.card (labelDualArrangement cfg).OrdinaryVertex at hweak
  rwa [← lineCount_two_eq_card_labelDualOrdinaryVertex cfg] at hweak

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
  rw [hglobal, ← hgroup]
  norm_num [w, BlockSystem.lineCount]

private theorem globalLineSlack_eq_lineMelchiorSlack
    {alpha : Type*} [Fintype alpha] [DecidableEq alpha]
    (cfg : Configuration alpha) :
    (blockSystem cfg).globalLineSlack = lineMelchiorSlack cfg := by
  unfold BlockSystem.globalLineSlack lineMelchiorSlack
  congr 1
  apply Fintype.sum_equiv (lineBlockEquiv cfg)
  intro b
  rcases b with ⟨b, hb⟩
  cases b with
  | inl L => rfl
  | inr c => cases hb

private theorem lineDegree_le_lineCount
    {Point Block : Type*} [Fintype Point] [Fintype Block]
    [DecidableEq Point] (S : BlockSystem Point Block)
    (s : ℕ) (p : Point) : S.lineDegree s p ≤ S.lineCount s := by
  unfold BlockSystem.lineDegree BlockSystem.degreeIn BlockSystem.lineCount
  exact Finset.card_filter_le _ _

private theorem lineDegree_eq_zero_of_lineCount_eq_zero
    {Point Block : Type*} [Fintype Point] [Fintype Block]
    [DecidableEq Point] (S : BlockSystem Point Block)
    (s : ℕ) (p : Point) (hzero : S.lineCount s = 0) :
    S.lineDegree s p = 0 := by
  have hle := lineDegree_le_lineCount S s p
  omega

/-- Restrict the ordinary-line/dual-ordinary-vertex dictionary to carriers
through one fixed label. -/
noncomputable def determinedLineOfSizeTwoThroughEquivLabelDualIncident
    {alpha : Type u} [Fintype alpha] [DecidableEq alpha]
    (cfg : Configuration alpha) (p : alpha) :
    DeterminedLineOfSizeThrough cfg p 2 ≃
      {q : (labelDualArrangement cfg).OrdinaryVertex //
        (labelDualArrangement cfg).Incident q.1 p} :=
  (determinedLineOfSizeTwoEquivLabelDualOrdinaryVertex cfg).subtypeEquiv
    fun L => by
      change p ∈ lineSupport cfg L.1 ↔
        (labelDualArrangement cfg).Incident
          (determinedLineDualVertex cfg L.1) p
      rw [labelDual_incident_determinedLine_iff, mem_lineSupport]

/-- The ordinary-vertex degree of the dual line indexed by `p` is exactly
the number of ordinary affine lines through `p`. -/
theorem labelDual_lineOrdinaryVertexDegree_eq_lineDegree_two
    {alpha : Type u} [Fintype alpha] [DecidableEq alpha]
    (cfg : Configuration alpha) (p : alpha) :
    (labelDualArrangement cfg).lineOrdinaryVertexDegree p =
      (blockSystem cfg).lineDegree 2 p := by
  classical
  rw [lineDegree_eq_card_determinedLineOfSizeThrough]
  unfold FiniteProjectiveLineArrangement.lineOrdinaryVertexDegree
    finiteRelationRightDegree
  calc
    (Finset.univ.filter fun q : (labelDualArrangement cfg).OrdinaryVertex =>
        (labelDualArrangement cfg).Incident q.1 p).card =
        Fintype.card {q : (labelDualArrangement cfg).OrdinaryVertex //
          (labelDualArrangement cfg).Incident q.1 p} :=
      (Fintype.card_subtype _).symm
    _ = Fintype.card (DeterminedLineOfSizeThrough cfg p 2) :=
      Fintype.card_congr
        (determinedLineOfSizeTwoThroughEquivLabelDualIncident cfg p).symm

private theorem sum_lineOrdinaryAttachmentDegree_le_four_mul_card
    {Line : Type*} [Fintype Line] [DecidableEq Line]
    (A : FiniteProjectiveLineArrangement Line) (hA : A.NonPencil) :
    (∑ l : Line, A.lineOrdinaryAttachmentDegree l) ≤
      4 * Fintype.card A.OrdinaryVertex := by
  rw [show (∑ l : Line, A.lineOrdinaryAttachmentDegree l) =
      ∑ q : A.OrdinaryVertex, A.ordinaryVertexAttachmentDegree q by
    simpa only [FiniteProjectiveLineArrangement.lineOrdinaryAttachmentDegree,
      FiniteProjectiveLineArrangement.ordinaryVertexAttachmentDegree] using
      (sum_finiteRelationRightDegree_eq_sum_finiteRelationLeftDegree
        A.OrdinaryVertexAttachedToLine)]
  calc
    (∑ q : A.OrdinaryVertex, A.ordinaryVertexAttachmentDegree q) ≤
        ∑ _q : A.OrdinaryVertex, 4 := by
      exact Finset.sum_le_sum fun q _hq =>
        A.ordinaryVertexAttachmentDegree_le_four hA q
    _ = 4 * Fintype.card A.OrdinaryVertex := by simp [mul_comm]

/-- Ten real points span at least five ordinary lines.  This is the exact
`q = 10` Kelly--Moser instance needed by the eleven-point pivot route. -/
theorem five_le_lineCount_two_of_card_ten
    {alpha : Type u} [Fintype alpha] [DecidableEq alpha]
    (Mel : RealPlaneMelchiorPrinciple.{u})
    (EvenArr : RealPlaneEvenArrangementPrinciple.{u})
    (cfg : Configuration alpha) (hnon : Noncollinear cfg)
    (hcard : Fintype.card alpha = 10) :
    5 ≤ (blockSystem cfg).lineCount 2 := by
  classical
  let S := blockSystem cfg
  have hpair := S.line_pair_partition_by_size
  rw [hcard] at hpair
  norm_num [Finset.sum_range_succ, Nat.choose] at hpair
  have hGform : S.globalLineRow =
      3 * (S.lineCount 3 : ℤ) + 7 * (S.lineCount 4 : ℤ) +
      12 * (S.lineCount 5 : ℤ) + 18 * (S.lineCount 6 : ℤ) +
      25 * (S.lineCount 7 : ℤ) + 33 * (S.lineCount 8 : ℤ) +
      42 * (S.lineCount 9 : ℤ) + 52 * (S.lineCount 10 : ℤ) := by
    rw [globalLineRow_eq_weighted_lineCount, hcard]
    norm_num [Finset.sum_range_succ, Nat.choose]
  have hmel : LineMelchior cfg := Mel.lineMelchior cfg hnon
  have hslack : 0 ≤ S.globalLineSlack := by
    simpa [S] using globalLineSlack_nonneg_of_lineMelchior cfg hmel
  rw [← S.choose_two_sub_three_sub_globalLineRow_eq_globalLineSlack,
    hcard, hGform] at hslack
  norm_num [Nat.choose] at hslack
  have heven : Even (Fintype.card alpha) := by
    rw [hcard]
    norm_num
  have hne := EvenArr.slack_ne_one cfg hnon heven
  rw [← globalLineSlack_eq_lineMelchiorSlack cfg,
    ← S.choose_two_sub_three_sub_globalLineRow_eq_globalLineSlack,
    hcard, hGform] at hne
  norm_num [Nat.choose] at hne
  have hweak : 3 * Fintype.card alpha ≤ 8 * S.lineCount 2 := by
    simpa [S] using weakKelly_lineCount_two cfg hnon
  rw [hcard] at hweak
  change 5 ≤ S.lineCount 2
  by_contra hfive
  have htwoUpper : S.lineCount 2 ≤ 4 := by omega
  have htwoLower : 3 ≤ S.lineCount 2 := by omega
  interval_cases htwo : S.lineCount 2
  · have hl4 : S.lineCount 4 = 0 := by omega
    have hl5 : S.lineCount 5 = 0 := by omega
    have hl6 : S.lineCount 6 = 0 := by omega
    have hl7 : S.lineCount 7 = 0 := by omega
    have hl8 : S.lineCount 8 = 0 := by omega
    have hl9 : S.lineCount 9 = 0 := by omega
    have hl10 : S.lineCount 10 = 0 := by omega
    have hlocal (p : alpha) : 1 ≤ S.lineDegree 2 p := by
      have harms := S.line_arms p
      rw [hcard] at harms
      have hd4 := lineDegree_eq_zero_of_lineCount_eq_zero S 4 p hl4
      have hd5 := lineDegree_eq_zero_of_lineCount_eq_zero S 5 p hl5
      have hd6 := lineDegree_eq_zero_of_lineCount_eq_zero S 6 p hl6
      have hd7 := lineDegree_eq_zero_of_lineCount_eq_zero S 7 p hl7
      have hd8 := lineDegree_eq_zero_of_lineCount_eq_zero S 8 p hl8
      have hd9 := lineDegree_eq_zero_of_lineCount_eq_zero S 9 p hl9
      have hd10 := lineDegree_eq_zero_of_lineCount_eq_zero S 10 p hl10
      norm_num [Finset.sum_range_succ, hd4, hd5, hd6, hd7, hd8, hd9,
        hd10] at harms
      omega
    have hsum : 10 ≤ ∑ p : alpha, S.lineDegree 2 p := by
      calc
        10 = ∑ _p : alpha, 1 := by simp [hcard]
        _ ≤ ∑ p : alpha, S.lineDegree 2 p :=
          Finset.sum_le_sum fun p _hp => hlocal p
    rw [S.line_incidence 2, htwo] at hsum
    norm_num at hsum
  · have hrowNe : S.globalLineRow ≠ 41 := by
      intro hrow
      apply hne
      rw [← hGform]
      omega
    have hrowLower : 41 ≤ S.globalLineRow := by omega
    have hrow : S.globalLineRow = 42 := by omega
    have hdefect :
        S.lineCount 4 + 2 * S.lineCount 5 + 3 * S.lineCount 6 +
          4 * S.lineCount 7 + 5 * S.lineCount 8 +
          6 * S.lineCount 9 + 7 * S.lineCount 10 = 1 := by
      omega
    rcases defect_one_profile _ _ _ _ _ _ _ hdefect with
      ⟨hl4, hl5, hl6, hl7, hl8, hl9, hl10⟩
    norm_num [htwo, hl4, hl5, hl6, hl7, hl8, hl9, hl10] at hpair
    omega

/-- Twelve real points span at least six ordinary lines.  This is the exact
`q = 12` Kelly--Moser instance used by the restored twelve-point route. -/
theorem six_le_lineCount_two_of_card_twelve
    {alpha : Type u} [Fintype alpha] [DecidableEq alpha]
    (Mel : RealPlaneMelchiorPrinciple.{u})
    (EvenArr : RealPlaneEvenArrangementPrinciple.{u})
    (cfg : Configuration alpha) (hnon : Noncollinear cfg)
    (hcard : Fintype.card alpha = 12) :
    6 ≤ (blockSystem cfg).lineCount 2 := by
  classical
  let S := blockSystem cfg
  have hpair := S.line_pair_partition_by_size
  rw [hcard] at hpair
  norm_num [Finset.sum_range_succ, Nat.choose] at hpair
  have hGform : S.globalLineRow =
      3 * (S.lineCount 3 : ℤ) + 7 * (S.lineCount 4 : ℤ) +
      12 * (S.lineCount 5 : ℤ) + 18 * (S.lineCount 6 : ℤ) +
      25 * (S.lineCount 7 : ℤ) + 33 * (S.lineCount 8 : ℤ) +
      42 * (S.lineCount 9 : ℤ) + 52 * (S.lineCount 10 : ℤ) +
      63 * (S.lineCount 11 : ℤ) + 75 * (S.lineCount 12 : ℤ) := by
    rw [globalLineRow_eq_weighted_lineCount, hcard]
    norm_num [Finset.sum_range_succ, Nat.choose]
  have hmel : LineMelchior cfg := Mel.lineMelchior cfg hnon
  have hslack : 0 ≤ S.globalLineSlack := by
    simpa [S] using globalLineSlack_nonneg_of_lineMelchior cfg hmel
  rw [← S.choose_two_sub_three_sub_globalLineRow_eq_globalLineSlack,
    hcard, hGform] at hslack
  norm_num [Nat.choose] at hslack
  have heven : Even (Fintype.card alpha) := by
    rw [hcard]
    norm_num
  have hne := EvenArr.slack_ne_one cfg hnon heven
  rw [← globalLineSlack_eq_lineMelchiorSlack cfg,
    ← S.choose_two_sub_three_sub_globalLineRow_eq_globalLineSlack,
    hcard, hGform] at hne
  norm_num [Nat.choose] at hne
  have hweak : 3 * Fintype.card alpha ≤ 8 * S.lineCount 2 := by
    simpa [S] using weakKelly_lineCount_two cfg hnon
  rw [hcard] at hweak
  change 6 ≤ S.lineCount 2
  by_contra hsix
  have htwoUpper : S.lineCount 2 ≤ 5 := by omega
  have htwoLower : 3 ≤ S.lineCount 2 := by omega
  interval_cases htwo : S.lineCount 2
  · have hl4 : S.lineCount 4 = 0 := by omega
    have hl5 : S.lineCount 5 = 0 := by omega
    have hl6 : S.lineCount 6 = 0 := by omega
    have hl7 : S.lineCount 7 = 0 := by omega
    have hl8 : S.lineCount 8 = 0 := by omega
    have hl9 : S.lineCount 9 = 0 := by omega
    have hl10 : S.lineCount 10 = 0 := by omega
    have hl11 : S.lineCount 11 = 0 := by omega
    have hl12 : S.lineCount 12 = 0 := by omega
    have hlocal (p : alpha) : 1 ≤ S.lineDegree 2 p := by
      have harms := S.line_arms p
      rw [hcard] at harms
      have hd4 := lineDegree_eq_zero_of_lineCount_eq_zero S 4 p hl4
      have hd5 := lineDegree_eq_zero_of_lineCount_eq_zero S 5 p hl5
      have hd6 := lineDegree_eq_zero_of_lineCount_eq_zero S 6 p hl6
      have hd7 := lineDegree_eq_zero_of_lineCount_eq_zero S 7 p hl7
      have hd8 := lineDegree_eq_zero_of_lineCount_eq_zero S 8 p hl8
      have hd9 := lineDegree_eq_zero_of_lineCount_eq_zero S 9 p hl9
      have hd10 := lineDegree_eq_zero_of_lineCount_eq_zero S 10 p hl10
      have hd11 := lineDegree_eq_zero_of_lineCount_eq_zero S 11 p hl11
      have hd12 := lineDegree_eq_zero_of_lineCount_eq_zero S 12 p hl12
      norm_num [Finset.sum_range_succ, hd4, hd5, hd6, hd7, hd8, hd9,
        hd10, hd11, hd12] at harms
      omega
    have hsum : 12 ≤ ∑ p : alpha, S.lineDegree 2 p := by
      calc
        12 = ∑ _p : alpha, 1 := by simp [hcard]
        _ ≤ ∑ p : alpha, S.lineDegree 2 p :=
          Finset.sum_le_sum fun p _hp => hlocal p
    rw [S.line_incidence 2, htwo] at hsum
    norm_num at hsum
  · omega
  · have hrowNe62 : S.globalLineRow ≠ 62 := by
      intro hrow
      apply hne
      rw [← hGform]
      omega
    have hrowLower : 61 ≤ S.globalLineRow := by omega
    have hrowNe61 : S.globalLineRow ≠ 61 := by
      intro hrow
      have hdefect :
          S.lineCount 4 + 2 * S.lineCount 5 + 3 * S.lineCount 6 +
            4 * S.lineCount 7 + 5 * S.lineCount 8 +
            6 * S.lineCount 9 + 7 * S.lineCount 10 +
            8 * S.lineCount 11 + 9 * S.lineCount 12 = 0 := by
        omega
      rcases defect_zero_profile _ _ _ _ _ _ _ _ _ hdefect with
        ⟨hl4, hl5, hl6, hl7, hl8, hl9, hl10, hl11, hl12⟩
      norm_num [htwo, hl4, hl5, hl6, hl7, hl8, hl9, hl10, hl11,
        hl12] at hpair
      omega
    have hrow : S.globalLineRow = 63 := by omega
    have hdefect :
        S.lineCount 4 + 2 * S.lineCount 5 + 3 * S.lineCount 6 +
          4 * S.lineCount 7 + 5 * S.lineCount 8 +
          6 * S.lineCount 9 + 7 * S.lineCount 10 +
          8 * S.lineCount 11 + 9 * S.lineCount 12 = 2 := by
      omega
    have hpair5 := hpair
    rcases twelve_defect_two_profile
        (S.lineCount 3) (S.lineCount 4) (S.lineCount 5)
        (S.lineCount 6) (S.lineCount 7) (S.lineCount 8)
        (S.lineCount 9) (S.lineCount 10) (S.lineCount 11)
        (S.lineCount 12) hpair5 hdefect with
      ⟨hl4, hl5, hl6, hl7, hl8, hl9, hl10, hl11, hl12⟩
    have hlocal (p : alpha) : 1 ≤ S.lineDegree 2 p := by
      have harms := S.line_arms p
      rw [hcard] at harms
      have hd4 := lineDegree_eq_zero_of_lineCount_eq_zero S 4 p hl4
      have hd6 := lineDegree_eq_zero_of_lineCount_eq_zero S 6 p hl6
      have hd7 := lineDegree_eq_zero_of_lineCount_eq_zero S 7 p hl7
      have hd8 := lineDegree_eq_zero_of_lineCount_eq_zero S 8 p hl8
      have hd9 := lineDegree_eq_zero_of_lineCount_eq_zero S 9 p hl9
      have hd10 := lineDegree_eq_zero_of_lineCount_eq_zero S 10 p hl10
      have hd11 := lineDegree_eq_zero_of_lineCount_eq_zero S 11 p hl11
      have hd12 := lineDegree_eq_zero_of_lineCount_eq_zero S 12 p hl12
      norm_num [Finset.sum_range_succ, hd4, hd6, hd7, hd8, hd9,
        hd10, hd11, hd12] at harms
      omega
    have hsum : 12 ≤ ∑ p : alpha, S.lineDegree 2 p := by
      calc
        12 = ∑ _p : alpha, 1 := by simp [hcard]
        _ ≤ ∑ p : alpha, S.lineDegree 2 p :=
          Finset.sum_le_sum fun p _hp => hlocal p
    rw [S.line_incidence 2, htwo] at hsum
    norm_num at hsum

/-- Nine real points span at least four ordinary lines.  In the high-line
branch the only Melchior profile below four ordinary lines would be
`(L₂,L₃)=(3,11)`; six zero-degree dual lines then violate the global
Four-Attachment capacity. -/
theorem four_le_lineCount_two_of_card_nine
    {alpha : Type u} [Fintype alpha] [DecidableEq alpha]
    (Mel : RealPlaneMelchiorPrinciple.{u})
    (cfg : Configuration alpha) (hnon : Noncollinear cfg)
    (hcard : Fintype.card alpha = 9) :
    4 ≤ (blockSystem cfg).lineCount 2 := by
  classical
  let S := blockSystem cfg
  let A := labelDualArrangement cfg
  have hA : A.NonPencil := by
    simpa [A] using labelDualArrangement_nonPencil_of_noncollinear cfg hnon
  by_cases hlow : ∃ l : alpha, (A.lineVertexSet l).card ≤ 2
  · obtain ⟨l, hl⟩ := hlow
    have hk :=
      A.three_mul_card_le_seven_mul_card_ordinaryVertex_of_lineVertexSet_card_le_two
        hA (by omega) l hl
    change 3 * Fintype.card alpha ≤
      7 * Fintype.card (labelDualArrangement cfg).OrdinaryVertex at hk
    rw [hcard, ← lineCount_two_eq_card_labelDualOrdinaryVertex cfg] at hk
    omega
  have hhigh (l : alpha) : 3 ≤ (A.lineVertexSet l).card := by
    by_contra hthree
    have hle : (A.lineVertexSet l).card ≤ 2 := by omega
    exact hlow ⟨l, hle⟩
  have hpair := S.line_pair_partition_by_size
  rw [hcard] at hpair
  norm_num [Finset.sum_range_succ, Nat.choose] at hpair
  have hGform : S.globalLineRow =
      3 * (S.lineCount 3 : ℤ) + 7 * (S.lineCount 4 : ℤ) +
      12 * (S.lineCount 5 : ℤ) + 18 * (S.lineCount 6 : ℤ) +
      25 * (S.lineCount 7 : ℤ) + 33 * (S.lineCount 8 : ℤ) +
      42 * (S.lineCount 9 : ℤ) := by
    rw [globalLineRow_eq_weighted_lineCount, hcard]
    norm_num [Finset.sum_range_succ, Nat.choose]
  have hmel : LineMelchior cfg := Mel.lineMelchior cfg hnon
  have hslack : 0 ≤ S.globalLineSlack := by
    simpa [S] using globalLineSlack_nonneg_of_lineMelchior cfg hmel
  rw [← S.choose_two_sub_three_sub_globalLineRow_eq_globalLineSlack,
    hcard, hGform] at hslack
  norm_num [Nat.choose] at hslack
  have hweak : 3 * Fintype.card alpha ≤ 8 * S.lineCount 2 := by
    simpa [S] using weakKelly_lineCount_two cfg hnon
  rw [hcard] at hweak
  change 4 ≤ S.lineCount 2
  by_contra hfour
  have htwoUpper : S.lineCount 2 ≤ 3 := by omega
  have htwoLower : 3 ≤ S.lineCount 2 := by omega
  have htwo : S.lineCount 2 = 3 := by omega
  have hl4 : S.lineCount 4 = 0 := by omega
  have hl5 : S.lineCount 5 = 0 := by omega
  have hl6 : S.lineCount 6 = 0 := by omega
  have hl7 : S.lineCount 7 = 0 := by omega
  have hl8 : S.lineCount 8 = 0 := by omega
  have hl9 : S.lineCount 9 = 0 := by omega
  have hpositiveTwo (p : alpha) (hp : S.lineDegree 2 p ≠ 0) :
      2 ≤ S.lineDegree 2 p := by
    have harms := S.line_arms p
    rw [hcard] at harms
    have hd4 := lineDegree_eq_zero_of_lineCount_eq_zero S 4 p hl4
    have hd5 := lineDegree_eq_zero_of_lineCount_eq_zero S 5 p hl5
    have hd6 := lineDegree_eq_zero_of_lineCount_eq_zero S 6 p hl6
    have hd7 := lineDegree_eq_zero_of_lineCount_eq_zero S 7 p hl7
    have hd8 := lineDegree_eq_zero_of_lineCount_eq_zero S 8 p hl8
    have hd9 := lineDegree_eq_zero_of_lineCount_eq_zero S 9 p hl9
    norm_num [Finset.sum_range_succ, hd4, hd5, hd6, hd7, hd8, hd9] at harms
    omega
  let positiveLabels : Finset alpha :=
    Finset.univ.filter fun p => S.lineDegree 2 p ≠ 0
  let zeroLabels : Finset alpha :=
    Finset.univ.filter fun p => S.lineDegree 2 p = 0
  have hpositiveSum :
      2 * positiveLabels.card ≤
        ∑ p ∈ positiveLabels, S.lineDegree 2 p := by
    calc
      2 * positiveLabels.card = ∑ _p ∈ positiveLabels, 2 := by
        simp [mul_comm]
      _ ≤ ∑ p ∈ positiveLabels, S.lineDegree 2 p := by
        exact Finset.sum_le_sum fun p hp =>
          hpositiveTwo p (Finset.mem_filter.mp hp).2
  have hpositiveSumUpper :
      (∑ p ∈ positiveLabels, S.lineDegree 2 p) ≤ 6 := by
    calc
      (∑ p ∈ positiveLabels, S.lineDegree 2 p) ≤
          ∑ p : alpha, S.lineDegree 2 p := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · exact Finset.filter_subset _ _
        · intro p _hp _hnot
          exact Nat.zero_le _
      _ = 2 * S.lineCount 2 := S.line_incidence 2
      _ = 6 := by rw [htwo]
  have hpositiveCard : positiveLabels.card ≤ 3 := by omega
  have hpartition : zeroLabels.card + positiveLabels.card = 9 := by
    simpa [zeroLabels, positiveLabels, hcard] using
      (Finset.card_filter_add_card_filter_not
        (s := (Finset.univ : Finset alpha))
        (p := fun p => S.lineDegree 2 p = 0))
  have hzeroCard : 6 ≤ zeroLabels.card := by omega
  have hzeroAttachment (p : alpha) (hp : p ∈ zeroLabels) :
      3 ≤ A.lineOrdinaryAttachmentDegree p := by
    have hpzero : S.lineDegree 2 p = 0 :=
      (Finset.mem_filter.mp hp).2
    have hdualZero : A.lineOrdinaryVertexDegree p = 0 := by
      change (labelDualArrangement cfg).lineOrdinaryVertexDegree p = 0
      rw [labelDual_lineOrdinaryVertexDegree_eq_lineDegree_two]
      exact hpzero
    exact A.three_le_lineOrdinaryAttachmentDegree_of_degree_zero
      hA p (hhigh p) hdualZero
  have hzeroAttachmentSum :
      3 * zeroLabels.card ≤
        ∑ p ∈ zeroLabels, A.lineOrdinaryAttachmentDegree p := by
    calc
      3 * zeroLabels.card = ∑ _p ∈ zeroLabels, 3 := by
        simp [mul_comm]
      _ ≤ ∑ p ∈ zeroLabels, A.lineOrdinaryAttachmentDegree p := by
        exact Finset.sum_le_sum fun p hp => hzeroAttachment p hp
  have hzeroAttachmentSumFull :
      (∑ p ∈ zeroLabels, A.lineOrdinaryAttachmentDegree p) ≤
        ∑ p : alpha, A.lineOrdinaryAttachmentDegree p := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · exact Finset.filter_subset _ _
    · intro p _hp _hnot
      exact Nat.zero_le _
  have hattachmentDegreeSum :
      (∑ p : alpha, A.lineOrdinaryAttachmentDegree p) =
        ∑ q : A.OrdinaryVertex, A.ordinaryVertexAttachmentDegree q := by
    simpa only [FiniteProjectiveLineArrangement.lineOrdinaryAttachmentDegree,
      FiniteProjectiveLineArrangement.ordinaryVertexAttachmentDegree] using
      (sum_finiteRelationRightDegree_eq_sum_finiteRelationLeftDegree
        A.OrdinaryVertexAttachedToLine)
  have hattachmentUpper :
      (∑ p : alpha, A.lineOrdinaryAttachmentDegree p) ≤
        4 * Fintype.card A.OrdinaryVertex := by
    rw [hattachmentDegreeSum]
    calc
      (∑ q : A.OrdinaryVertex, A.ordinaryVertexAttachmentDegree q) ≤
          ∑ _q : A.OrdinaryVertex, 4 := by
        exact Finset.sum_le_sum fun q _hq =>
          A.ordinaryVertexAttachmentDegree_le_four hA q
      _ = 4 * Fintype.card A.OrdinaryVertex := by simp [mul_comm]
  have hordinaryCard : Fintype.card A.OrdinaryVertex = 3 := by
    change Fintype.card (labelDualArrangement cfg).OrdinaryVertex = 3
    rw [← lineCount_two_eq_card_labelDualOrdinaryVertex cfg, htwo]
  rw [hordinaryCard] at hattachmentUpper
  omega

/-- The all-triple branch of the exact eleven-label census under `L₂ ≤ 4`. -/
structure ElevenKellyFourOrdinaryAllTripleProfile
    {alpha : Type u} [Fintype alpha] [DecidableEq alpha]
    (cfg : Configuration alpha) : Prop where
  lineCount_two : (blockSystem cfg).lineCount 2 = 4
  lineCount_three : (blockSystem cfg).lineCount 3 = 17
  lineCount_four : (blockSystem cfg).lineCount 4 = 0
  lineCount_five : (blockSystem cfg).lineCount 5 = 0
  lineCount_six : (blockSystem cfg).lineCount 6 = 0
  lineCount_seven : (blockSystem cfg).lineCount 7 = 0
  lineCount_eight : (blockSystem cfg).lineCount 8 = 0
  lineCount_nine : (blockSystem cfg).lineCount 9 = 0
  lineCount_ten : (blockSystem cfg).lineCount 10 = 0
  lineCount_eleven : (blockSystem cfg).lineCount 11 = 0

/-- The unique-four-line branch of the exact eleven-label census under
`L₂ ≤ 4`. -/
structure ElevenKellyFourOrdinaryOneFourProfile
    {alpha : Type u} [Fintype alpha] [DecidableEq alpha]
    (cfg : Configuration alpha) : Prop where
  lineCount_two : (blockSystem cfg).lineCount 2 = 4
  lineCount_three : (blockSystem cfg).lineCount 3 = 15
  lineCount_four : (blockSystem cfg).lineCount 4 = 1
  lineCount_five : (blockSystem cfg).lineCount 5 = 0
  lineCount_six : (blockSystem cfg).lineCount 6 = 0
  lineCount_seven : (blockSystem cfg).lineCount 7 = 0
  lineCount_eight : (blockSystem cfg).lineCount 8 = 0
  lineCount_nine : (blockSystem cfg).lineCount 9 = 0
  lineCount_ten : (blockSystem cfg).lineCount 10 = 0
  lineCount_eleven : (blockSystem cfg).lineCount 11 = 0

/-- In the difficult eleven-label profile at least two labels have ordinary
line degree exactly one.  Summing
`3 d₄(p) ≤ d₂(p) + 2 · 1[d₂(p)=1]` gives `12 ≤ 8 + 2 #degreeOne`. -/
theorem two_le_card_lineDegree_two_eq_one_of_elevenKelly_oneFourProfile
    {alpha : Type u} [Fintype alpha] [DecidableEq alpha]
    (cfg : Configuration alpha) (hcard : Fintype.card alpha = 11)
    (profile : ElevenKellyFourOrdinaryOneFourProfile cfg) :
    2 ≤ (Finset.univ.filter fun p : alpha =>
      (blockSystem cfg).lineDegree 2 p = 1).card := by
  classical
  let S := blockSystem cfg
  let oneLabels : Finset alpha :=
    Finset.univ.filter fun p => S.lineDegree 2 p = 1
  have hpoint (p : alpha) :
      3 * S.lineDegree 4 p ≤ S.lineDegree 2 p +
        2 * (if S.lineDegree 2 p = 1 then 1 else 0) := by
    have harms := S.line_arms p
    rw [hcard] at harms
    have hd4le := lineDegree_le_lineCount S 4 p
    rw [profile.lineCount_four] at hd4le
    have hd5 := lineDegree_eq_zero_of_lineCount_eq_zero S 5 p
      profile.lineCount_five
    have hd6 := lineDegree_eq_zero_of_lineCount_eq_zero S 6 p
      profile.lineCount_six
    have hd7 := lineDegree_eq_zero_of_lineCount_eq_zero S 7 p
      profile.lineCount_seven
    have hd8 := lineDegree_eq_zero_of_lineCount_eq_zero S 8 p
      profile.lineCount_eight
    have hd9 := lineDegree_eq_zero_of_lineCount_eq_zero S 9 p
      profile.lineCount_nine
    have hd10 := lineDegree_eq_zero_of_lineCount_eq_zero S 10 p
      profile.lineCount_ten
    have hd11 := lineDegree_eq_zero_of_lineCount_eq_zero S 11 p
      profile.lineCount_eleven
    norm_num [Finset.sum_range_succ, hd5, hd6, hd7, hd8, hd9, hd10,
      hd11] at harms
    by_cases hone : S.lineDegree 2 p = 1
    · simp [hone]
      omega
    · simp [hone]
      omega
  have hindicator :
      (∑ p : alpha, if S.lineDegree 2 p = 1 then 1 else 0) =
        oneLabels.card := by
    change (∑ p ∈ (Finset.univ : Finset alpha),
      if S.lineDegree 2 p = 1 then 1 else 0) =
        ((Finset.univ : Finset alpha).filter fun p =>
          S.lineDegree 2 p = 1).card
    rw [Finset.card_eq_sum_ones, Finset.sum_filter]
  have hsum :
      (∑ p : alpha, 3 * S.lineDegree 4 p) ≤
        ∑ p : alpha, (S.lineDegree 2 p +
          2 * (if S.lineDegree 2 p = 1 then 1 else 0)) := by
    exact Finset.sum_le_sum fun p _hp => hpoint p
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at hsum
  rw [S.line_incidence 4, S.line_incidence 2,
    profile.lineCount_four, profile.lineCount_two, hindicator] at hsum
  change 2 ≤ oneLabels.card
  omega

/-- Consequently, one attachment on each degree-one label already supplies
the exact aggregate-two input used by the difficult-profile consumer. -/
theorem two_le_degreeOneAttachmentSum_of_elevenKelly_oneFourProfile
    {alpha : Type u} [Fintype alpha] [DecidableEq alpha]
    (cfg : Configuration alpha) (hcard : Fintype.card alpha = 11)
    (profile : ElevenKellyFourOrdinaryOneFourProfile cfg)
    (hattach : ∀ p : alpha, (blockSystem cfg).lineDegree 2 p = 1 →
      1 ≤ (labelDualArrangement cfg).lineOrdinaryAttachmentDegree p) :
    2 ≤ ∑ p ∈ (Finset.univ.filter fun p : alpha =>
        (blockSystem cfg).lineDegree 2 p = 1),
      (labelDualArrangement cfg).lineOrdinaryAttachmentDegree p := by
  classical
  let oneLabels : Finset alpha :=
    Finset.univ.filter fun p => (blockSystem cfg).lineDegree 2 p = 1
  have hcardOne : 2 ≤ oneLabels.card := by
    simpa [oneLabels] using
      two_le_card_lineDegree_two_eq_one_of_elevenKelly_oneFourProfile
        cfg hcard profile
  calc
    2 ≤ oneLabels.card := hcardOne
    _ = ∑ _p ∈ oneLabels, 1 := by simp
    _ ≤ ∑ p ∈ oneLabels,
        (labelDualArrangement cfg).lineOrdinaryAttachmentDegree p := by
      exact Finset.sum_le_sum fun p hp =>
        hattach p (Finset.mem_filter.mp hp).2

/-- Lossless Melchior/pair-row classification of the only two possible
eleven-label profiles with at most four ordinary lines. -/
theorem elevenKelly_fourOrdinary_exactProfiles
    {alpha : Type u} [Fintype alpha] [DecidableEq alpha]
    (Mel : RealPlaneMelchiorPrinciple.{u})
    (cfg : Configuration alpha) (hnon : Noncollinear cfg)
    (hcard : Fintype.card alpha = 11)
    (hfour : (blockSystem cfg).lineCount 2 ≤ 4) :
    ElevenKellyFourOrdinaryAllTripleProfile cfg ∨
      ElevenKellyFourOrdinaryOneFourProfile cfg := by
  classical
  let S := blockSystem cfg
  change S.lineCount 2 ≤ 4 at hfour
  have hpair := S.line_pair_partition_by_size
  rw [hcard] at hpair
  norm_num [Finset.sum_range_succ, Nat.choose] at hpair
  have hGform : S.globalLineRow =
      3 * (S.lineCount 3 : ℤ) + 7 * (S.lineCount 4 : ℤ) +
      12 * (S.lineCount 5 : ℤ) + 18 * (S.lineCount 6 : ℤ) +
      25 * (S.lineCount 7 : ℤ) + 33 * (S.lineCount 8 : ℤ) +
      42 * (S.lineCount 9 : ℤ) + 52 * (S.lineCount 10 : ℤ) +
      63 * (S.lineCount 11 : ℤ) := by
    rw [globalLineRow_eq_weighted_lineCount, hcard]
    norm_num [Finset.sum_range_succ, Nat.choose]
  have hmel : LineMelchior cfg := Mel.lineMelchior cfg hnon
  have hslack : 0 ≤ S.globalLineSlack := by
    simpa [S] using globalLineSlack_nonneg_of_lineMelchior cfg hmel
  rw [← S.choose_two_sub_three_sub_globalLineRow_eq_globalLineSlack,
    hcard, hGform] at hslack
  norm_num [Nat.choose] at hslack
  have hweak : 3 * Fintype.card alpha ≤ 8 * S.lineCount 2 := by
    simpa [S] using weakKelly_lineCount_two cfg hnon
  rw [hcard] at hweak
  have htwoLower : 3 ≤ S.lineCount 2 := by omega
  interval_cases htwo : S.lineCount 2
  · omega
  · have hfourUpper : S.lineCount 4 ≤ 1 := by omega
    interval_cases hl4 : S.lineCount 4
    · left
      exact ⟨by omega, by omega, hl4, by omega, by omega, by omega,
        by omega, by omega, by omega, by omega⟩
    · right
      exact ⟨by omega, by omega, hl4, by omega, by omega, by omega,
        by omega, by omega, by omega, by omega⟩

/-- The all-triple eleven-label profile is already impossible in the
high-line branch using only the unconditional degree-zero clause. -/
theorem elevenKelly_allTripleProfile_absurd
    {alpha : Type u} [Fintype alpha] [DecidableEq alpha]
    (cfg : Configuration alpha) (hnon : Noncollinear cfg)
    (hcard : Fintype.card alpha = 11)
    (hhigh : ∀ l : alpha,
      3 ≤ ((labelDualArrangement cfg).lineVertexSet l).card)
    (profile : ElevenKellyFourOrdinaryAllTripleProfile cfg) : False := by
  classical
  let S := blockSystem cfg
  let A := labelDualArrangement cfg
  have hA : A.NonPencil := by
    simpa [A] using labelDualArrangement_nonPencil_of_noncollinear cfg hnon
  have hpositiveTwo (p : alpha) (hp : S.lineDegree 2 p ≠ 0) :
      2 ≤ S.lineDegree 2 p := by
    have harms := S.line_arms p
    rw [hcard] at harms
    have hd4 := lineDegree_eq_zero_of_lineCount_eq_zero S 4 p
      profile.lineCount_four
    have hd5 := lineDegree_eq_zero_of_lineCount_eq_zero S 5 p
      profile.lineCount_five
    have hd6 := lineDegree_eq_zero_of_lineCount_eq_zero S 6 p
      profile.lineCount_six
    have hd7 := lineDegree_eq_zero_of_lineCount_eq_zero S 7 p
      profile.lineCount_seven
    have hd8 := lineDegree_eq_zero_of_lineCount_eq_zero S 8 p
      profile.lineCount_eight
    have hd9 := lineDegree_eq_zero_of_lineCount_eq_zero S 9 p
      profile.lineCount_nine
    have hd10 := lineDegree_eq_zero_of_lineCount_eq_zero S 10 p
      profile.lineCount_ten
    have hd11 := lineDegree_eq_zero_of_lineCount_eq_zero S 11 p
      profile.lineCount_eleven
    norm_num [Finset.sum_range_succ, hd4, hd5, hd6, hd7, hd8, hd9,
      hd10, hd11] at harms
    omega
  let positiveLabels : Finset alpha :=
    Finset.univ.filter fun p => S.lineDegree 2 p ≠ 0
  let zeroLabels : Finset alpha :=
    Finset.univ.filter fun p => S.lineDegree 2 p = 0
  have hpositiveSum :
      2 * positiveLabels.card ≤
        ∑ p ∈ positiveLabels, S.lineDegree 2 p := by
    calc
      2 * positiveLabels.card = ∑ _p ∈ positiveLabels, 2 := by
        simp [mul_comm]
      _ ≤ ∑ p ∈ positiveLabels, S.lineDegree 2 p := by
        exact Finset.sum_le_sum fun p hp =>
          hpositiveTwo p (Finset.mem_filter.mp hp).2

  have hpositiveSumUpper :
      (∑ p ∈ positiveLabels, S.lineDegree 2 p) ≤ 8 := by
    calc
      (∑ p ∈ positiveLabels, S.lineDegree 2 p) ≤
          ∑ p : alpha, S.lineDegree 2 p := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · exact Finset.filter_subset _ _
        · intro p _hp _hnot
          exact Nat.zero_le _
      _ = 2 * S.lineCount 2 := S.line_incidence 2
      _ = 8 := by rw [profile.lineCount_two]
  have hpositiveCard : positiveLabels.card ≤ 4 := by omega
  have hpartition : zeroLabels.card + positiveLabels.card = 11 := by
    simpa [zeroLabels, positiveLabels, hcard] using
      (Finset.card_filter_add_card_filter_not
        (s := (Finset.univ : Finset alpha))
        (p := fun p => S.lineDegree 2 p = 0))
  have hzeroCard : 7 ≤ zeroLabels.card := by omega
  have hzeroAttachment (p : alpha) (hp : p ∈ zeroLabels) :
      3 ≤ A.lineOrdinaryAttachmentDegree p := by
    have hpzero : S.lineDegree 2 p = 0 :=
      (Finset.mem_filter.mp hp).2
    have hdualZero : A.lineOrdinaryVertexDegree p = 0 := by
      change (labelDualArrangement cfg).lineOrdinaryVertexDegree p = 0
      rw [labelDual_lineOrdinaryVertexDegree_eq_lineDegree_two]
      exact hpzero
    exact A.three_le_lineOrdinaryAttachmentDegree_of_degree_zero
      hA p (hhigh p) hdualZero
  have hzeroAttachmentSum :
      3 * zeroLabels.card ≤
        ∑ p ∈ zeroLabels, A.lineOrdinaryAttachmentDegree p := by
    calc
      3 * zeroLabels.card = ∑ _p ∈ zeroLabels, 3 := by
        simp [mul_comm]
      _ ≤ ∑ p ∈ zeroLabels, A.lineOrdinaryAttachmentDegree p := by
        exact Finset.sum_le_sum fun p hp => hzeroAttachment p hp
  have hzeroAttachmentSumFull :
      (∑ p ∈ zeroLabels, A.lineOrdinaryAttachmentDegree p) ≤
        ∑ p : alpha, A.lineOrdinaryAttachmentDegree p := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · exact Finset.filter_subset _ _
    · intro p _hp _hnot
      exact Nat.zero_le _
  have hattachmentUpper :=
    sum_lineOrdinaryAttachmentDegree_le_four_mul_card A hA
  have hordinaryCard : Fintype.card A.OrdinaryVertex = 4 := by
    change Fintype.card (labelDualArrangement cfg).OrdinaryVertex = 4
    rw [← lineCount_two_eq_card_labelDualOrdinaryVertex cfg,
      profile.lineCount_two]
  rw [hordinaryCard] at hattachmentUpper
  omega

/-- Exact finite consumer for the sole difficult eleven-label profile.
Five zero-degree lines cost at least fifteen attachments; any aggregate of
two attachments on the disjoint degree-one layer exceeds the global
Four-Attachment capacity `16`. -/
theorem elevenKelly_oneFourProfile_absurd_of_degreeOneAttachmentSum_two
    {alpha : Type u} [Fintype alpha] [DecidableEq alpha]
    (cfg : Configuration alpha) (hnon : Noncollinear cfg)
    (hcard : Fintype.card alpha = 11)
    (hhigh : ∀ l : alpha,
      3 ≤ ((labelDualArrangement cfg).lineVertexSet l).card)
    (profile : ElevenKellyFourOrdinaryOneFourProfile cfg)
    (honeSum :
      2 ≤ ∑ p ∈ (Finset.univ.filter fun p : alpha =>
          (blockSystem cfg).lineDegree 2 p = 1),
        (labelDualArrangement cfg).lineOrdinaryAttachmentDegree p) : False := by
  classical
  let S := blockSystem cfg
  let A := labelDualArrangement cfg
  have hA : A.NonPencil := by
    simpa [A] using labelDualArrangement_nonPencil_of_noncollinear cfg hnon
  have hpositiveCost (p : alpha) (hp : S.lineDegree 2 p ≠ 0) :
      2 ≤ S.lineDegree 2 p + S.lineDegree 4 p := by
    have harms := S.line_arms p
    rw [hcard] at harms
    have hd4le := lineDegree_le_lineCount S 4 p
    rw [profile.lineCount_four] at hd4le
    have hd5 := lineDegree_eq_zero_of_lineCount_eq_zero S 5 p
      profile.lineCount_five
    have hd6 := lineDegree_eq_zero_of_lineCount_eq_zero S 6 p
      profile.lineCount_six
    have hd7 := lineDegree_eq_zero_of_lineCount_eq_zero S 7 p
      profile.lineCount_seven
    have hd8 := lineDegree_eq_zero_of_lineCount_eq_zero S 8 p
      profile.lineCount_eight
    have hd9 := lineDegree_eq_zero_of_lineCount_eq_zero S 9 p
      profile.lineCount_nine
    have hd10 := lineDegree_eq_zero_of_lineCount_eq_zero S 10 p
      profile.lineCount_ten
    have hd11 := lineDegree_eq_zero_of_lineCount_eq_zero S 11 p
      profile.lineCount_eleven
    norm_num [Finset.sum_range_succ, hd5, hd6, hd7, hd8, hd9, hd10,
      hd11] at harms
    omega
  let positiveLabels : Finset alpha :=
    Finset.univ.filter fun p => S.lineDegree 2 p ≠ 0
  let zeroLabels : Finset alpha :=
    Finset.univ.filter fun p => S.lineDegree 2 p = 0
  let oneLabels : Finset alpha :=
    Finset.univ.filter fun p => S.lineDegree 2 p = 1

  have hpositiveCostSum :
      2 * positiveLabels.card ≤
        ∑ p ∈ positiveLabels,
          (S.lineDegree 2 p + S.lineDegree 4 p) := by
    calc
      2 * positiveLabels.card = ∑ _p ∈ positiveLabels, 2 := by
        simp [mul_comm]
      _ ≤ ∑ p ∈ positiveLabels,
          (S.lineDegree 2 p + S.lineDegree 4 p) := by
        exact Finset.sum_le_sum fun p hp =>
          hpositiveCost p (Finset.mem_filter.mp hp).2
  have hpositiveCostSumUpper :
      (∑ p ∈ positiveLabels,
          (S.lineDegree 2 p + S.lineDegree 4 p)) ≤ 12 := by
    calc
      (∑ p ∈ positiveLabels,
          (S.lineDegree 2 p + S.lineDegree 4 p)) ≤
          ∑ p : alpha, (S.lineDegree 2 p + S.lineDegree 4 p) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · exact Finset.filter_subset _ _
        · intro p _hp _hnot
          exact Nat.zero_le _
      _ = (∑ p : alpha, S.lineDegree 2 p) +
          ∑ p : alpha, S.lineDegree 4 p := by
        rw [Finset.sum_add_distrib]
      _ = 2 * S.lineCount 2 + 4 * S.lineCount 4 := by
        rw [S.line_incidence 2, S.line_incidence 4]
      _ = 12 := by
        rw [profile.lineCount_two, profile.lineCount_four]
  have hpositiveCard : positiveLabels.card ≤ 6 := by omega
  have hpartition : zeroLabels.card + positiveLabels.card = 11 := by
    simpa [zeroLabels, positiveLabels, hcard] using
      (Finset.card_filter_add_card_filter_not
        (s := (Finset.univ : Finset alpha))
        (p := fun p => S.lineDegree 2 p = 0))
  have hzeroCard : 5 ≤ zeroLabels.card := by omega
  have honeSum' :
      2 ≤ ∑ p ∈ oneLabels, A.lineOrdinaryAttachmentDegree p := by
    simpa [oneLabels, S, A] using honeSum
  have hzeroAttachment (p : alpha) (hp : p ∈ zeroLabels) :
      3 ≤ A.lineOrdinaryAttachmentDegree p := by
    have hpzero : S.lineDegree 2 p = 0 :=
      (Finset.mem_filter.mp hp).2
    have hdualZero : A.lineOrdinaryVertexDegree p = 0 := by
      change (labelDualArrangement cfg).lineOrdinaryVertexDegree p = 0
      rw [labelDual_lineOrdinaryVertexDegree_eq_lineDegree_two]
      exact hpzero
    exact A.three_le_lineOrdinaryAttachmentDegree_of_degree_zero
      hA p (hhigh p) hdualZero
  have hzeroAttachmentSum :
      3 * zeroLabels.card ≤
        ∑ p ∈ zeroLabels, A.lineOrdinaryAttachmentDegree p := by
    calc
      3 * zeroLabels.card = ∑ _p ∈ zeroLabels, 3 := by
        simp [mul_comm]
      _ ≤ ∑ p ∈ zeroLabels, A.lineOrdinaryAttachmentDegree p := by
        exact Finset.sum_le_sum fun p hp => hzeroAttachment p hp
  have hdisjoint : Disjoint zeroLabels oneLabels := by
    apply Finset.disjoint_left.mpr
    intro p hpzero hpone
    have hz : S.lineDegree 2 p = 0 :=
      (Finset.mem_filter.mp hpzero).2
    have ho : S.lineDegree 2 p = 1 :=
      (Finset.mem_filter.mp hpone).2
    omega
  have hcombinedLower :
      17 ≤ ∑ p ∈ zeroLabels ∪ oneLabels,
        A.lineOrdinaryAttachmentDegree p := by
    rw [Finset.sum_union hdisjoint]
    omega
  have hcombinedFull :
      (∑ p ∈ zeroLabels ∪ oneLabels,
          A.lineOrdinaryAttachmentDegree p) ≤
        ∑ p : alpha, A.lineOrdinaryAttachmentDegree p := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · exact Finset.union_subset
        (Finset.filter_subset _ _) (Finset.filter_subset _ _)
    · intro p _hp _hnot
      exact Nat.zero_le _
  have hattachmentUpper :=
    sum_lineOrdinaryAttachmentDegree_le_four_mul_card A hA
  have hordinaryCard : Fintype.card A.OrdinaryVertex = 4 := by
    change Fintype.card (labelDualArrangement cfg).OrdinaryVertex = 4
    rw [← lineCount_two_eq_card_labelDualOrdinaryVertex cfg,
      profile.lineCount_two]
  rw [hordinaryCard] at hattachmentUpper
  omega

/-- Restricted `q = 11` Kelly endpoint.  Its only residual input is the
aggregate of two degree-one attachments in the exact one-four-line profile;
the low-line and all-triple branches are unconditional. -/
theorem five_le_lineCount_two_of_card_eleven_of_oneFourAttachmentSum_two
    {alpha : Type u} [Fintype alpha] [DecidableEq alpha]
    (Mel : RealPlaneMelchiorPrinciple.{u})
    (cfg : Configuration alpha) (hnon : Noncollinear cfg)
    (hcard : Fintype.card alpha = 11)
    (honeSum : ElevenKellyFourOrdinaryOneFourProfile cfg →
      2 ≤ ∑ p ∈ (Finset.univ.filter fun p : alpha =>
          (blockSystem cfg).lineDegree 2 p = 1),
        (labelDualArrangement cfg).lineOrdinaryAttachmentDegree p) :
    5 ≤ (blockSystem cfg).lineCount 2 := by
  classical
  let A := labelDualArrangement cfg
  have hA : A.NonPencil := by
    simpa [A] using labelDualArrangement_nonPencil_of_noncollinear cfg hnon
  by_cases hlow : ∃ l : alpha, (A.lineVertexSet l).card ≤ 2
  · obtain ⟨l, hl⟩ := hlow
    have hk :=
      A.three_mul_card_le_seven_mul_card_ordinaryVertex_of_lineVertexSet_card_le_two
        hA (by omega) l hl
    change 3 * Fintype.card alpha ≤
      7 * Fintype.card (labelDualArrangement cfg).OrdinaryVertex at hk
    rw [hcard, ← lineCount_two_eq_card_labelDualOrdinaryVertex cfg] at hk
    omega
  have hhigh (l : alpha) :
      3 ≤ ((labelDualArrangement cfg).lineVertexSet l).card := by
    change 3 ≤ (A.lineVertexSet l).card
    by_contra hthree
    have hle : (A.lineVertexSet l).card ≤ 2 := by omega
    exact hlow ⟨l, hle⟩
  by_contra hfive
  have hfour : (blockSystem cfg).lineCount 2 ≤ 4 := by omega
  rcases elevenKelly_fourOrdinary_exactProfiles Mel cfg hnon hcard hfour with
    profile | profile
  · exact elevenKelly_allTripleProfile_absurd cfg hnon hcard hhigh profile
  · exact elevenKelly_oneFourProfile_absurd_of_degreeOneAttachmentSum_two
      cfg hnon hcard hhigh profile (honeSum profile)

/-- The guarded eleven-point ordinary-line bound.  In the only difficult
profile, at least two indexed lines have ordinary degree one; the canonical
clean-edge sector gives one literal attachment on each such high line. -/
theorem five_le_lineCount_two_of_card_eleven
    {alpha : Type u} [Fintype alpha] [DecidableEq alpha]
    (Mel : RealPlaneMelchiorPrinciple.{u})
    (cfg : Configuration alpha) (hnon : Noncollinear cfg)
    (hcard : Fintype.card alpha = 11) :
    5 ≤ (blockSystem cfg).lineCount 2 := by
  classical
  let A := labelDualArrangement cfg
  have hA : A.NonPencil := by
    simpa [A] using labelDualArrangement_nonPencil_of_noncollinear cfg hnon
  by_cases hlow : ∃ l : alpha, (A.lineVertexSet l).card ≤ 2
  · obtain ⟨l, hl⟩ := hlow
    have hk :=
      A.three_mul_card_le_seven_mul_card_ordinaryVertex_of_lineVertexSet_card_le_two
        hA (by omega) l hl
    change 3 * Fintype.card alpha ≤
      7 * Fintype.card (labelDualArrangement cfg).OrdinaryVertex at hk
    rw [hcard, ← lineCount_two_eq_card_labelDualOrdinaryVertex cfg] at hk
    omega
  · have hhigh (l : alpha) :
        3 ≤ ((labelDualArrangement cfg).lineVertexSet l).card := by
      change 3 ≤ (A.lineVertexSet l).card
      by_contra hthree
      apply hlow
      exact ⟨l, by omega⟩
    apply five_le_lineCount_two_of_card_eleven_of_oneFourAttachmentSum_two
      Mel cfg hnon hcard
    intro profile
    apply two_le_degreeOneAttachmentSum_of_elevenKelly_oneFourProfile
      cfg hcard profile
    intro p hp
    have hone : A.lineOrdinaryVertexDegree p = 1 := by
      change (labelDualArrangement cfg).lineOrdinaryVertexDegree p = 1
      rw [labelDual_lineOrdinaryVertexDegree_eq_lineDegree_two]
      exact hp
    simpa only [A] using
      A.one_le_lineOrdinaryAttachmentDegree_of_degree_one_highLine
        hA p (hhigh p) hone

end Erdos506.Incidence
