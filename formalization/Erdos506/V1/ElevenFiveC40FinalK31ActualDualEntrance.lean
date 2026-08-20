import Erdos506.V1.ElevenFiveC40FinalRealTail
import Erdos506.Incidence.DeterminedLineArrangementCensus
import Erdos506.Incidence.ProjectiveCovectorFrame
import Erdos506.V1.TwelveGridParametricObstruction

/-!
# Actual-support entrance for the residual K3.1 grid

This module starts the remaining `(d₃,d₅)=(9,3)` K3.1 branch entirely from
the three actual four-line supports produced by the finite path lemma.  The
three private families are definitions, not extra data.  Their cardinalities
are the `3,2,3` dual pencil sizes used by the real parameter-grid tail.
-/

namespace Erdos506.V1

open Matrix
open Erdos506.Block
open Erdos506.Block.BlockSystem
open Erdos506.Incidence
open Erdos506.V4

universe u v

/-- Private labels on the left base of an actual three-four-line path. -/
def threeFourPathLeftPrivate
    {Point : Type u} {Block : Type v} [Fintype Point] [Fintype Block]
    [DecidableEq Point] (S : BlockSystem Point Block)
    (a c : LineBlock S) : Finset Point :=
  S.support a.1 \ S.support c.1

/-- The two labels private to the connector of an actual three-four-line
path. -/
def threeFourPathMiddlePrivate
    {Point : Type u} {Block : Type v} [Fintype Point] [Fintype Block]
    [DecidableEq Point] (S : BlockSystem Point Block)
    (a b c : LineBlock S) : Finset Point :=
  S.support c.1 \ (S.support a.1 ∪ S.support b.1)

/-- Private labels on the right base of an actual three-four-line path. -/
def threeFourPathRightPrivate
    {Point : Type u} {Block : Type v} [Fintype Point] [Fintype Block]
    [DecidableEq Point] (S : BlockSystem Point Block)
    (b c : LineBlock S) : Finset Point :=
  S.support b.1 \ S.support c.1

/-- The actual support path canonically has the dual private-family census
`3,2,3`.  No projective normalization has entered at this point. -/
theorem three_four_path_private_family_cards
    {Point : Type u} {Block : Type v} [Fintype Point] [Fintype Block]
    [DecidableEq Point]
    (S : BlockSystem Point Block) (a b c : LineBlock S)
    (ha : (S.support a.1).card = 4)
    (hb : (S.support b.1).card = 4)
    (hc : (S.support c.1).card = 4)
    (hab : Disjoint (S.support a.1) (S.support b.1))
    (hca : (S.support c.1 ∩ S.support a.1).card = 1)
    (hcb : (S.support c.1 ∩ S.support b.1).card = 1) :
    (threeFourPathLeftPrivate S a c).card = 3 ∧
      (threeFourPathMiddlePrivate S a b c).card = 2 ∧
        (threeFourPathRightPrivate S b c).card = 3 := by
  have hleft := Finset.card_sdiff_add_card_inter
    (S.support a.1) (S.support c.1)
  have hright := Finset.card_sdiff_add_card_inter
    (S.support b.1) (S.support c.1)
  have hinterDisjoint : Disjoint (S.support c.1 ∩ S.support a.1)
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
  have hmiddle := Finset.card_sdiff_add_card_inter
    (S.support c.1) (S.support a.1 ∪ S.support b.1)
  have hac : (S.support a.1 ∩ S.support c.1).card = 1 := by
    rw [Finset.inter_comm]
    exact hca
  rw [ha, hac] at hleft
  rw [hb] at hright
  have hbc : (S.support b.1 ∩ S.support c.1).card = 1 := by
    rw [Finset.inter_comm]
    exact hcb
  rw [hbc] at hright
  rw [hc, hinterUnion, Finset.card_union_of_disjoint hinterDisjoint,
    hca, hcb] at hmiddle
  have hleftCard : (S.support a.1 \ S.support c.1).card = 3 := by omega
  have hmiddleCard :
      (S.support c.1 \ (S.support a.1 ∪ S.support b.1)).card = 2 := by
    omega
  have hrightCard : (S.support b.1 \ S.support c.1).card = 3 := by omega
  constructor
  · simpa [threeFourPathLeftPrivate] using hleftCard
  constructor
  · simpa [threeFourPathMiddlePrivate] using hmiddleCard
  · simpa [threeFourPathRightPrivate] using hrightCard

/-- The three canonical private families of an actual path are pairwise
disjoint.  This is the finite label separation needed to form the three
dual line pencils. -/
theorem three_four_path_private_families_pairwise_disjoint
    {Point : Type u} {Block : Type v} [Fintype Point] [Fintype Block]
    [DecidableEq Point]
    (S : BlockSystem Point Block) (a b c : LineBlock S)
    (hab : Disjoint (S.support a.1) (S.support b.1)) :
    Disjoint (threeFourPathLeftPrivate S a c)
      (threeFourPathMiddlePrivate S a b c) ∧
      Disjoint (threeFourPathLeftPrivate S a c)
        (threeFourPathRightPrivate S b c) ∧
        Disjoint (threeFourPathMiddlePrivate S a b c)
          (threeFourPathRightPrivate S b c) := by
  constructor
  · apply Finset.disjoint_left.mpr
    intro q hleft hmiddle
    have hqa : q ∈ S.support a.1 := (Finset.mem_sdiff.mp hleft).1
    have hnot : q ∉ S.support a.1 ∪ S.support b.1 :=
      (Finset.mem_sdiff.mp hmiddle).2
    exact hnot (Finset.mem_union_left _ hqa)
  constructor
  · apply Finset.disjoint_left.mpr
    intro q hleft hright
    exact Finset.disjoint_left.mp hab
      (Finset.mem_sdiff.mp hleft).1 (Finset.mem_sdiff.mp hright).1
  · apply Finset.disjoint_left.mpr
    intro q hmiddle hright
    have hqb : q ∈ S.support b.1 := (Finset.mem_sdiff.mp hright).1
    have hnot : q ∉ S.support a.1 ∪ S.support b.1 :=
      (Finset.mem_sdiff.mp hmiddle).2
    exact hnot (Finset.mem_union_right _ hqb)

/-- The middle private family is literally the part of the connector in the
two-point complement of the disjoint bases.  This ties the `3,2,3` path
labels to the mixed-pair equality calculation. -/
theorem three_four_path_middlePrivate_eq_twoBaseComplement_inter
    {Point : Type u} {Block : Type v} [Fintype Point] [Fintype Block]
    [DecidableEq Point] (S : BlockSystem Point Block)
    (a b c : LineBlock S) :
    threeFourPathMiddlePrivate S a b c =
      S.support c.1 ∩ twoBaseComplement S a b := by
  ext q
  simp only [threeFourPathMiddlePrivate, twoBaseComplement,
    Finset.mem_sdiff, Finset.mem_inter, Finset.mem_union, Finset.mem_univ,
    true_and]

/-- A size-three support which uses exactly two mixed pairs across a chosen
cut has one point on one side and two on the other.  This is the precise
actual-support classification supplied by the equality K3.1 capacity row. -/
theorem card_three_mixedPair_eq_two_split
    {Point : Type u} [DecidableEq Point]
    (X D : Finset Point) (hX : X.card = 3)
    (hmixed : (X ∩ D).card * (X \ D).card = 2) :
    ((X ∩ D).card = 1 ∧ (X \ D).card = 2) ∨
      ((X ∩ D).card = 2 ∧ (X \ D).card = 1) := by
  have hsplit := Finset.card_inter_add_card_sdiff X D
  rw [hX] at hsplit
  have hinside : (X ∩ D).card ≤ 3 := by omega
  have houtside : (X \ D).card ≤ 3 := by omega
  interval_cases hIn : (X ∩ D).card <;>
    interval_cases hOut : (X \ D).card <;>
    norm_num [hIn, hOut] at * <;> omega

/-- Every size-three line in the equality `t₃=6` K3.1 path has the exact
`1+2` split across the two-base complement. -/
theorem three_four_path_six_three_line_split
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
    (hthree : S.lineCount 3 = 6)
    {x : Block} (hx : x ∈ S.lineBlocksOfSize 3) :
    ((S.support x ∩ twoBaseComplement S a b).card = 1 ∧
        (S.support x \ twoBaseComplement S a b).card = 2) ∨
      ((S.support x ∩ twoBaseComplement S a b).card = 2 ∧
        (S.support x \ twoBaseComplement S a b).card = 1) := by
  have hxcard : (S.support x).card = 3 :=
    (S.mem_blocksOfKindSize.mp hx).2
  have hmixed := two_base_path_six_three_line_mixed_saturation
    S hcard a b c ha hb hc hab hca hcb hthree x hx
  change (S.support x ∩ twoBaseComplement S a b).card *
      (S.support x \ twoBaseComplement S a b).card = 2 at hmixed
  exact card_three_mixedPair_eq_two_split (S.support x)
    (twoBaseComplement S a b) hxcard hmixed

/-- The unique left connector label of an actual three-four-line path. -/
noncomputable def threeFourPathLeftConnectorPoint
    {Point : Type u} {Block : Type v} [Fintype Point] [Fintype Block]
    [DecidableEq Point] (S : BlockSystem Point Block)
    (a c : LineBlock S)
    (hca : (S.support c.1 ∩ S.support a.1).card = 1) : Point :=
  (Finset.card_eq_one.mp hca).choose

/-- The unique right connector label of an actual three-four-line path. -/
noncomputable def threeFourPathRightConnectorPoint
    {Point : Type u} {Block : Type v} [Fintype Point] [Fintype Block]
    [DecidableEq Point] (S : BlockSystem Point Block)
    (b c : LineBlock S)
    (hcb : (S.support c.1 ∩ S.support b.1).card = 1) : Point :=
  (Finset.card_eq_one.mp hcb).choose

/-- The left connector point belongs to both actual supports. -/
theorem three_four_path_leftConnectorPoint_mem
    {Point : Type u} {Block : Type v} [Fintype Point] [Fintype Block]
    [DecidableEq Point] (S : BlockSystem Point Block)
    (a c : LineBlock S)
    (hca : (S.support c.1 ∩ S.support a.1).card = 1) :
    threeFourPathLeftConnectorPoint S a c hca ∈
      S.support c.1 ∩ S.support a.1 := by
  rw [(Finset.card_eq_one.mp hca).choose_spec]
  simp [threeFourPathLeftConnectorPoint]

/-- The right connector point belongs to both actual supports. -/
theorem three_four_path_rightConnectorPoint_mem
    {Point : Type u} {Block : Type v} [Fintype Point] [Fintype Block]
    [DecidableEq Point] (S : BlockSystem Point Block)
    (b c : LineBlock S)
    (hcb : (S.support c.1 ∩ S.support b.1).card = 1) :
    threeFourPathRightConnectorPoint S b c hcb ∈
      S.support c.1 ∩ S.support b.1 := by
  rw [(Finset.card_eq_one.mp hcb).choose_spec]
  simp [threeFourPathRightConnectorPoint]

/-- The left four-line is its connector point together with its three private
labels. -/
theorem three_four_path_left_support_eq_insert_private
    {Point : Type u} {Block : Type v} [Fintype Point] [Fintype Block]
    [DecidableEq Point] (S : BlockSystem Point Block)
    (a c : LineBlock S)
    (hca : (S.support c.1 ∩ S.support a.1).card = 1) :
    S.support a.1 = insert (threeFourPathLeftConnectorPoint S a c hca)
      (threeFourPathLeftPrivate S a c) := by
  let p := threeFourPathLeftConnectorPoint S a c hca
  have hsingle : S.support c.1 ∩ S.support a.1 = {p} := by
    simpa [p, threeFourPathLeftConnectorPoint] using
      (Finset.card_eq_one.mp hca).choose_spec
  have hp : p ∈ S.support c.1 ∩ S.support a.1 := by
    rw [hsingle]
    simp
  ext q
  constructor
  · intro hq
    by_cases hqc : q ∈ S.support c.1
    · simp only [Finset.mem_insert]
      have hqinter : q ∈ S.support c.1 ∩ S.support a.1 :=
        Finset.mem_inter.mpr ⟨hqc, hq⟩
      rw [hsingle] at hqinter
      exact Or.inl (by simpa using hqinter)
    · simp only [Finset.mem_insert]
      exact Or.inr (Finset.mem_sdiff.mpr ⟨hq, hqc⟩)
  · intro hq
    rcases Finset.mem_insert.mp hq with hq | hq
    · subst q
      exact (Finset.mem_inter.mp hp).2
    · exact (Finset.mem_sdiff.mp hq).1

/-- The right four-line is its connector point together with its three
private labels. -/
theorem three_four_path_right_support_eq_insert_private
    {Point : Type u} {Block : Type v} [Fintype Point] [Fintype Block]
    [DecidableEq Point] (S : BlockSystem Point Block)
    (b c : LineBlock S)
    (hcb : (S.support c.1 ∩ S.support b.1).card = 1) :
    S.support b.1 = insert (threeFourPathRightConnectorPoint S b c hcb)
      (threeFourPathRightPrivate S b c) := by
  let q := threeFourPathRightConnectorPoint S b c hcb
  have hsingle : S.support c.1 ∩ S.support b.1 = {q} := by
    simpa [q, threeFourPathRightConnectorPoint] using
      (Finset.card_eq_one.mp hcb).choose_spec
  have hq : q ∈ S.support c.1 ∩ S.support b.1 := by
    rw [hsingle]
    simp
  ext r
  constructor
  · intro hr
    by_cases hrc : r ∈ S.support c.1
    · simp only [Finset.mem_insert]
      have hrinter : r ∈ S.support c.1 ∩ S.support b.1 :=
        Finset.mem_inter.mpr ⟨hrc, hr⟩
      rw [hsingle] at hrinter
      exact Or.inl (by simpa using hrinter)
    · simp only [Finset.mem_insert]
      exact Or.inr (Finset.mem_sdiff.mpr ⟨hr, hrc⟩)
  · intro hr
    rcases Finset.mem_insert.mp hr with hr | hr
    · subst r
      exact (Finset.mem_inter.mp hq).2
    · exact (Finset.mem_sdiff.mp hr).1

/-- The connector support is precisely the two connector labels plus its two
private labels.  Disjoint base supports force the two chosen labels apart. -/
theorem three_four_path_middle_support_eq_insert_insert_private
    {Point : Type u} {Block : Type v} [Fintype Point] [Fintype Block]
    [DecidableEq Point] (S : BlockSystem Point Block)
    (a b c : LineBlock S)
    (hab : Disjoint (S.support a.1) (S.support b.1))
    (hca : (S.support c.1 ∩ S.support a.1).card = 1)
    (hcb : (S.support c.1 ∩ S.support b.1).card = 1) :
    S.support c.1 = insert (threeFourPathLeftConnectorPoint S a c hca)
      (insert (threeFourPathRightConnectorPoint S b c hcb)
        (threeFourPathMiddlePrivate S a b c)) := by
  let p := threeFourPathLeftConnectorPoint S a c hca
  let q := threeFourPathRightConnectorPoint S b c hcb
  have hleftSingle : S.support c.1 ∩ S.support a.1 = {p} := by
    simpa [p, threeFourPathLeftConnectorPoint] using
      (Finset.card_eq_one.mp hca).choose_spec
  have hrightSingle : S.support c.1 ∩ S.support b.1 = {q} := by
    simpa [q, threeFourPathRightConnectorPoint] using
      (Finset.card_eq_one.mp hcb).choose_spec
  have hp : p ∈ S.support c.1 ∩ S.support a.1 := by
    rw [hleftSingle]
    simp
  have hq : q ∈ S.support c.1 ∩ S.support b.1 := by
    rw [hrightSingle]
    simp
  have hpq : p ≠ q := by
    intro heq
    apply Finset.disjoint_left.mp hab (Finset.mem_inter.mp hp).2
    exact heq ▸ (Finset.mem_inter.mp hq).2
  ext r
  constructor
  · intro hr
    by_cases hrp : r = p
    · simp only [Finset.mem_insert]
      exact Or.inl (by simpa [p] using hrp)
    by_cases hrq : r = q
    · simp only [Finset.mem_insert]
      exact Or.inr (Or.inl (by simpa [q] using hrq))
    · simp only [Finset.mem_insert]
      refine Or.inr (Or.inr (Finset.mem_sdiff.mpr ⟨hr, ?_⟩))
      intro hrab
      rcases Finset.mem_union.mp hrab with hra | hrb
      · have hrinter : r ∈ S.support c.1 ∩ S.support a.1 :=
          Finset.mem_inter.mpr ⟨hr, hra⟩
        rw [hleftSingle] at hrinter
        exact hrp (by simpa using hrinter)
      · have hrinter : r ∈ S.support c.1 ∩ S.support b.1 :=
          Finset.mem_inter.mpr ⟨hr, hrb⟩
        rw [hrightSingle] at hrinter
        exact hrq (by simpa using hrinter)
  · intro hr
    rcases Finset.mem_insert.mp hr with hrp | hr
    · subst r
      exact (Finset.mem_inter.mp hp).1
    rcases Finset.mem_insert.mp hr with hrq | hr
    · subst r
      exact (Finset.mem_inter.mp hq).1
    · exact (Finset.mem_sdiff.mp hr).1

/-- On ten labels, the middle private family is not merely contained in the
two-base complement: it is exactly that two-point complement.  Thus the
middle dual pencil has a canonical actual carrier. -/
theorem three_four_path_middlePrivate_eq_twoBaseComplement
    {Point : Type u} {Block : Type v} [Fintype Point] [Fintype Block]
    [DecidableEq Point] (S : BlockSystem Point Block)
    (hcard : Fintype.card Point = 10) (a b c : LineBlock S)
    (ha : (S.support a.1).card = 4)
    (hb : (S.support b.1).card = 4)
    (hc : (S.support c.1).card = 4)
    (hab : Disjoint (S.support a.1) (S.support b.1))
    (hca : (S.support c.1 ∩ S.support a.1).card = 1)
    (hcb : (S.support c.1 ∩ S.support b.1).card = 1) :
    threeFourPathMiddlePrivate S a b c = twoBaseComplement S a b := by
  have hprivate := three_four_path_private_family_cards
    S a b c ha hb hc hab hca hcb
  have hmiddle : (threeFourPathMiddlePrivate S a b c).card = 2 :=
    hprivate.2.1
  have hunion : (S.support a.1 ∪ S.support b.1).card = 8 := by
    rw [Finset.card_union_of_disjoint hab, ha, hb]
  have hcomplement : (twoBaseComplement S a b).card = 2 := by
    change (Finset.univ \ (S.support a.1 ∪ S.support b.1)).card = 2
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _),
      Finset.card_univ, hcard, hunion]
  apply Finset.eq_of_subset_of_card_le
  · intro q hq
    have hnot : q ∉ S.support a.1 ∪ S.support b.1 :=
      (Finset.mem_sdiff.mp hq).2
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hnot⟩
  · rw [hmiddle, hcomplement]

/-- After identifying the middle private family with the two-base complement,
every actual triple-line in the equality K3.1 case has the `1+2` split over
the canonical middle pencil. -/
theorem three_four_path_six_three_line_middle_split
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
    (hthree : S.lineCount 3 = 6)
    {x : Block} (hx : x ∈ S.lineBlocksOfSize 3) :
    ((S.support x ∩ threeFourPathMiddlePrivate S a b c).card = 1 ∧
        (S.support x \ threeFourPathMiddlePrivate S a b c).card = 2) ∨
      ((S.support x ∩ threeFourPathMiddlePrivate S a b c).card = 2 ∧
        (S.support x \ threeFourPathMiddlePrivate S a b c).card = 1) := by
  have hsplit := three_four_path_six_three_line_split
    S hcard a b c ha hb hc hab hca hcb hthree hx
  have hmiddle := three_four_path_middlePrivate_eq_twoBaseComplement
    S hcard a b c ha hb hc hab hca hcb
  rw [← hmiddle] at hsplit
  exact hsplit

/-- Index a three-element actual finite carrier by the standard `Fin 3`.
This is an equivalence of its subtype, so it adds no labels or incidence
assumptions. -/
noncomputable def finThreeEquivFinset
    {Point : Type u} [DecidableEq Point]
    (X : Finset Point) (hX : X.card = 3) : Fin 3 ≃ ↥X :=
  (Fintype.equivFinOfCardEq (by simpa only [Fintype.card_coe] using hX)).symm

/-- Index a two-element actual finite carrier by the standard `Fin 2`. -/
noncomputable def finTwoEquivFinset
    {Point : Type u} [DecidableEq Point]
    (X : Finset Point) (hX : X.card = 2) : Fin 2 ≃ ↥X :=
  (Fintype.equivFinOfCardEq (by simpa only [Fintype.card_coe] using hX)).symm

/-- Every index of the left private pencil carries an actual private label. -/
theorem finThreeEquivFinset_mem
    {Point : Type u} [DecidableEq Point]
    (X : Finset Point) (hX : X.card = 3) (i : Fin 3) :
    (finThreeEquivFinset X hX i).1 ∈ X :=
  (finThreeEquivFinset X hX i).2

/-- Every index of the two-point middle pencil carries an actual private
label. -/
theorem finTwoEquivFinset_mem
    {Point : Type u} [DecidableEq Point]
    (X : Finset Point) (hX : X.card = 2) (i : Fin 2) :
    (finTwoEquivFinset X hX i).1 ∈ X :=
  (finTwoEquivFinset X hX i).2

/-- The actual `3,2,3` private-family census supplies standard finite
indices for the two three-pencils and the middle two-pencil. -/
noncomputable def three_four_path_private_family_indexing
    {Point : Type u} {Block : Type v} [Fintype Point] [Fintype Block]
    [DecidableEq Point]
    (S : BlockSystem Point Block) (a b c : LineBlock S)
    (ha : (S.support a.1).card = 4)
    (hb : (S.support b.1).card = 4)
    (hc : (S.support c.1).card = 4)
    (hab : Disjoint (S.support a.1) (S.support b.1))
    (hca : (S.support c.1 ∩ S.support a.1).card = 1)
    (hcb : (S.support c.1 ∩ S.support b.1).card = 1) :
    (Fin 3 ≃ ↥(threeFourPathLeftPrivate S a c)) ×
      (Fin 2 ≃ ↥(threeFourPathMiddlePrivate S a b c)) ×
        (Fin 3 ≃ ↥(threeFourPathRightPrivate S b c)) := by
  obtain ⟨hleft, hmiddle, hright⟩ := three_four_path_private_family_cards
    S a b c ha hb hc hab hca hcb
  exact ⟨finThreeEquivFinset _ hleft, finTwoEquivFinset _ hmiddle,
    finThreeEquivFinset _ hright⟩

/-- A triple-line using one of the two middle-pencil labels necessarily uses
one label from each outer private pencil.  This is the actual-support form of
one transversal edge of the dual `3×3` grid. -/
theorem three_four_path_three_line_one_middle_meets_both_bases
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
    {x : Block} (hx : x ∈ S.lineBlocksOfSize 3)
    (hmiddle : (S.support x ∩ threeFourPathMiddlePrivate S a b c).card = 1) :
    (S.support x ∩ S.support a.1).card = 1 ∧
      (S.support x ∩ S.support b.1).card = 1 := by
  have hxspec := S.mem_blocksOfKindSize.mp hx
  have hxcard : (S.support x).card = 3 := hxspec.2
  let ell : LineBlock S := ⟨x, hxspec.1⟩
  have hneA : ell ≠ a := by
    intro heq
    have hcards := congrArg (fun z : LineBlock S => (S.support z.1).card) heq
    change (S.support x).card = (S.support a.1).card at hcards
    rw [hxcard, ha] at hcards
    omega
  have hneB : ell ≠ b := by
    intro heq
    have hcards := congrArg (fun z : LineBlock S => (S.support z.1).card) heq
    change (S.support x).card = (S.support b.1).card at hcards
    rw [hxcard, hb] at hcards
    omega
  have hinterA := S.distinct_line_inter_card_lt_two hneA
  have hinterB := S.distinct_line_inter_card_lt_two hneB
  change (S.support x ∩ S.support a.1).card < 2 at hinterA
  change (S.support x ∩ S.support b.1).card < 2 at hinterB
  have hmiddleEq := three_four_path_middlePrivate_eq_twoBaseComplement
    S hcard a b c ha hb hc hab hca hcb
  have houtside : S.support x \ threeFourPathMiddlePrivate S a b c =
      S.support x ∩ (S.support a.1 ∪ S.support b.1) := by
    rw [hmiddleEq]
    ext q
    simp only [twoBaseComplement, Finset.mem_sdiff, Finset.mem_univ,
      true_and, Finset.mem_inter, Finset.mem_union]
    tauto
  have hinterUnion : S.support x ∩ (S.support a.1 ∪ S.support b.1) =
      (S.support x ∩ S.support a.1) ∪
        (S.support x ∩ S.support b.1) := by
    ext q
    simp only [Finset.mem_inter, Finset.mem_union]
    tauto
  have hdisjInter : Disjoint (S.support x ∩ S.support a.1)
      (S.support x ∩ S.support b.1) := by
    apply Finset.disjoint_left.mpr
    intro q hqa hqb
    exact Finset.disjoint_left.mp hab (Finset.mem_inter.mp hqa).2
      (Finset.mem_inter.mp hqb).2
  have hsplit := Finset.card_inter_add_card_sdiff
    (S.support x) (threeFourPathMiddlePrivate S a b c)
  rw [hxcard, hmiddle] at hsplit
  have houtcard : (S.support x \ threeFourPathMiddlePrivate S a b c).card = 2 :=
    by omega
  have hsum : (S.support x ∩ S.support a.1).card +
      (S.support x ∩ S.support b.1).card = 2 := by
    rw [← Finset.card_union_of_disjoint hdisjInter, ← hinterUnion, ← houtside]
    exact houtcard
  omega

/-- A triple-line through both middle-private labels has exactly one outer
private label, on precisely one of the two base pencils.  This is the other
local edge type in the actual `3,2,3` dual picture. -/
theorem three_four_path_three_line_two_middle_meets_one_base
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
    {x : Block} (hx : x ∈ S.lineBlocksOfSize 3)
    (hmiddle : (S.support x ∩ threeFourPathMiddlePrivate S a b c).card = 2) :
    ((S.support x ∩ S.support a.1).card = 1 ∧
        (S.support x ∩ S.support b.1).card = 0) ∨
      ((S.support x ∩ S.support a.1).card = 0 ∧
        (S.support x ∩ S.support b.1).card = 1) := by
  have hxspec := S.mem_blocksOfKindSize.mp hx
  have hxcard : (S.support x).card = 3 := hxspec.2
  let ell : LineBlock S := ⟨x, hxspec.1⟩
  have hneA : ell ≠ a := by
    intro heq
    have hcards := congrArg (fun z : LineBlock S => (S.support z.1).card) heq
    change (S.support x).card = (S.support a.1).card at hcards
    rw [hxcard, ha] at hcards
    omega
  have hneB : ell ≠ b := by
    intro heq
    have hcards := congrArg (fun z : LineBlock S => (S.support z.1).card) heq
    change (S.support x).card = (S.support b.1).card at hcards
    rw [hxcard, hb] at hcards
    omega
  have hinterA := S.distinct_line_inter_card_lt_two hneA
  have hinterB := S.distinct_line_inter_card_lt_two hneB
  change (S.support x ∩ S.support a.1).card < 2 at hinterA
  change (S.support x ∩ S.support b.1).card < 2 at hinterB
  have hmiddleEq := three_four_path_middlePrivate_eq_twoBaseComplement
    S hcard a b c ha hb hc hab hca hcb
  have houtside : S.support x \ threeFourPathMiddlePrivate S a b c =
      S.support x ∩ (S.support a.1 ∪ S.support b.1) := by
    rw [hmiddleEq]
    ext q
    simp only [twoBaseComplement, Finset.mem_sdiff, Finset.mem_univ,
      true_and, Finset.mem_inter, Finset.mem_union]
    tauto
  have hinterUnion : S.support x ∩ (S.support a.1 ∪ S.support b.1) =
      (S.support x ∩ S.support a.1) ∪
        (S.support x ∩ S.support b.1) := by
    ext q
    simp only [Finset.mem_inter, Finset.mem_union]
    tauto
  have hdisjInter : Disjoint (S.support x ∩ S.support a.1)
      (S.support x ∩ S.support b.1) := by
    apply Finset.disjoint_left.mpr
    intro q hqa hqb
    exact Finset.disjoint_left.mp hab (Finset.mem_inter.mp hqa).2
      (Finset.mem_inter.mp hqb).2
  have hsplit := Finset.card_inter_add_card_sdiff
    (S.support x) (threeFourPathMiddlePrivate S a b c)
  rw [hxcard, hmiddle] at hsplit
  have houtcard : (S.support x \ threeFourPathMiddlePrivate S a b c).card = 1 :=
    by omega
  have hsum : (S.support x ∩ S.support a.1).card +
      (S.support x ∩ S.support b.1).card = 1 := by
    rw [← Finset.card_union_of_disjoint hdisjInter, ← hinterUnion, ← houtside]
    exact houtcard
  omega

/-- In the equality K3.1 case, no actual triple-line can use both middle
private labels: those two labels already lie on the connector four-line.
Consequently every triple-line uses exactly one middle label. -/
theorem three_four_path_six_three_line_middle_card_eq_one
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
    (hthree : S.lineCount 3 = 6)
    {x : Block} (hx : x ∈ S.lineBlocksOfSize 3) :
    (S.support x ∩ threeFourPathMiddlePrivate S a b c).card = 1 := by
  have hxspec := S.mem_blocksOfKindSize.mp hx
  have hxcard : (S.support x).card = 3 := hxspec.2
  let ell : LineBlock S := ⟨x, hxspec.1⟩
  have hne : ell ≠ c := by
    intro heq
    have hcards := congrArg (fun z : LineBlock S => (S.support z.1).card) heq
    change (S.support x).card = (S.support c.1).card at hcards
    rw [hxcard, hc] at hcards
    omega
  have hinter := S.distinct_line_inter_card_lt_two hne
  change (S.support x ∩ S.support c.1).card < 2 at hinter
  have hprivateSub : threeFourPathMiddlePrivate S a b c ⊆ S.support c.1 := by
    intro q hq
    exact (Finset.mem_sdiff.mp hq).1
  have hinterSub : S.support x ∩ threeFourPathMiddlePrivate S a b c ⊆
      S.support x ∩ S.support c.1 := by
    intro q hq
    exact Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp hq).1,
      hprivateSub (Finset.mem_inter.mp hq).2⟩
  have hmiddleLe : (S.support x ∩ threeFourPathMiddlePrivate S a b c).card < 2 :=
    (Finset.card_le_card hinterSub).trans_lt hinter
  rcases three_four_path_six_three_line_middle_split
    S hcard a b c ha hb hc hab hca hcb hthree hx with hOne | hTwo
  · exact hOne.1
  · omega

/-- Thus every one of the six triple-lines is an actual transversal of the
two outer private three-pencils, marked by one middle-pencil label. -/
theorem three_four_path_six_three_line_is_actual_transversal
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
    (hthree : S.lineCount 3 = 6)
    {x : Block} (hx : x ∈ S.lineBlocksOfSize 3) :
    (S.support x ∩ threeFourPathMiddlePrivate S a b c).card = 1 ∧
      (S.support x ∩ S.support a.1).card = 1 ∧
        (S.support x ∩ S.support b.1).card = 1 := by
  have hmiddle := three_four_path_six_three_line_middle_card_eq_one
    S hcard a b c ha hb hc hab hca hcb hthree hx
  have hbases := three_four_path_three_line_one_middle_meets_both_bases
    S hcard a b c ha hb hc hab hca hcb hx hmiddle
  exact ⟨hmiddle, hbases.1, hbases.2⟩

/-- The outer labels of an actual transversal are genuinely private labels,
not either connector intersection.  Hence the six triple-lines live on the
literal `3,2,3` private families. -/
theorem three_four_path_six_three_line_is_private_transversal
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
    (hthree : S.lineCount 3 = 6)
    {x : Block} (hx : x ∈ S.lineBlocksOfSize 3) :
    (S.support x ∩ threeFourPathMiddlePrivate S a b c).card = 1 ∧
      (S.support x ∩ threeFourPathLeftPrivate S a c).card = 1 ∧
        (S.support x ∩ threeFourPathRightPrivate S b c).card = 1 := by
  obtain ⟨hmiddle, hleft, hright⟩ :=
    three_four_path_six_three_line_is_actual_transversal
      S hcard a b c ha hb hc hab hca hcb hthree hx
  have hxspec := S.mem_blocksOfKindSize.mp hx
  have hxcard : (S.support x).card = 3 := hxspec.2
  let ell : LineBlock S := ⟨x, hxspec.1⟩
  have hne : ell ≠ c := by
    intro heq
    have hcards := congrArg (fun z : LineBlock S => (S.support z.1).card) heq
    change (S.support x).card = (S.support c.1).card at hcards
    rw [hxcard, hc] at hcards
    omega
  have hinter := S.distinct_line_inter_card_lt_two hne
  change (S.support x ∩ S.support c.1).card < 2 at hinter
  have hmiddlePos : 0 < (S.support x ∩ threeFourPathMiddlePrivate S a b c).card :=
    by rw [hmiddle]; omega
  obtain ⟨m, hm⟩ := Finset.card_pos.mp hmiddlePos
  have hmx := (Finset.mem_inter.mp hm).1
  have hmprivate := (Finset.mem_inter.mp hm).2
  have hmc : m ∈ S.support c.1 := (Finset.mem_sdiff.mp hmprivate).1
  have hmnotA : m ∉ S.support a.1 := by
    intro hma
    exact (Finset.mem_sdiff.mp hmprivate).2 (Finset.mem_union_left _ hma)
  have hmnotB : m ∉ S.support b.1 := by
    intro hmb
    exact (Finset.mem_sdiff.mp hmprivate).2 (Finset.mem_union_right _ hmb)
  have hleftEq : S.support x ∩ S.support a.1 =
      S.support x ∩ threeFourPathLeftPrivate S a c := by
    apply Finset.Subset.antisymm
    · intro q hq
      have hqx := (Finset.mem_inter.mp hq).1
      have hqa := (Finset.mem_inter.mp hq).2
      have hqnotc : q ∉ S.support c.1 := by
        intro hqc
        have hmq : m ≠ q := by
          intro heq
          subst q
          exact hmnotA hqa
        have hpairSub : ({m, q} : Finset Point) ⊆
            S.support x ∩ S.support c.1 := by
          intro r hr
          simp only [Finset.mem_insert, Finset.mem_singleton] at hr
          rcases hr with rfl | rfl
          · exact Finset.mem_inter.mpr ⟨hmx, hmc⟩
          · exact Finset.mem_inter.mpr ⟨hqx, hqc⟩
        have hpairCard : ({m, q} : Finset Point).card = 2 := by
          simp [hmq]
        have htwo : 2 ≤ (S.support x ∩ S.support c.1).card := by
          rw [← hpairCard]
          exact Finset.card_le_card hpairSub
        omega
      exact Finset.mem_inter.mpr ⟨hqx, Finset.mem_sdiff.mpr ⟨hqa, hqnotc⟩⟩
    · intro q hq
      exact Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp hq).1,
        (Finset.mem_sdiff.mp (Finset.mem_inter.mp hq).2).1⟩
  have hrightEq : S.support x ∩ S.support b.1 =
      S.support x ∩ threeFourPathRightPrivate S b c := by
    apply Finset.Subset.antisymm
    · intro q hq
      have hqx := (Finset.mem_inter.mp hq).1
      have hqb := (Finset.mem_inter.mp hq).2
      have hqnotc : q ∉ S.support c.1 := by
        intro hqc
        have hmq : m ≠ q := by
          intro heq
          subst q
          exact hmnotB hqb
        have hpairSub : ({m, q} : Finset Point) ⊆
            S.support x ∩ S.support c.1 := by
          intro r hr
          simp only [Finset.mem_insert, Finset.mem_singleton] at hr
          rcases hr with rfl | rfl
          · exact Finset.mem_inter.mpr ⟨hmx, hmc⟩
          · exact Finset.mem_inter.mpr ⟨hqx, hqc⟩
        have hpairCard : ({m, q} : Finset Point).card = 2 := by
          simp [hmq]
        have htwo : 2 ≤ (S.support x ∩ S.support c.1).card := by
          rw [← hpairCard]
          exact Finset.card_le_card hpairSub
        omega
      exact Finset.mem_inter.mpr ⟨hqx, Finset.mem_sdiff.mpr ⟨hqb, hqnotc⟩⟩
    · intro q hq
      exact Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp hq).1,
        (Finset.mem_sdiff.mp (Finset.mem_inter.mp hq).2).1⟩
  exact ⟨hmiddle, by rw [← hleftEq]; exact hleft,
    by rw [← hrightEq]; exact hright⟩

/-- Double-counting the marked middle label on the six actual private
transversals.  The two middle-pencil fibres have total cardinality six. -/
theorem three_four_path_six_three_line_middle_fibre_card_sum
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
    (∑ m ∈ threeFourPathMiddlePrivate S a b c,
      ((S.lineBlocksOfSize 3).filter fun x => m ∈ S.support x).card) = 6 := by
  let M := threeFourPathMiddlePrivate S a b c
  let F := S.lineBlocksOfSize 3
  have hF : F.card = 6 := by
    simpa [F, BlockSystem.lineCount] using hthree
  have hmark (x : Block) (hx : x ∈ F) : (S.support x ∩ M).card = 1 := by
    exact three_four_path_six_three_line_middle_card_eq_one
      S hcard a b c ha hb hc hab hca hcb hthree hx
  have hcount (x : Block) :
      (∑ m ∈ M, if m ∈ S.support x then 1 else 0) =
        (S.support x ∩ M).card := by
    rw [← Finset.card_filter]
    congr 1
    ext m
    simp only [Finset.mem_filter, Finset.mem_inter]
    tauto
  calc
    (∑ m ∈ M, (F.filter fun x => m ∈ S.support x).card) =
        ∑ m ∈ M, ∑ x ∈ F, if m ∈ S.support x then 1 else 0 := by
          apply Finset.sum_congr rfl
          intro m hm
          rw [Finset.card_filter]
    _ = ∑ x ∈ F, ∑ m ∈ M, if m ∈ S.support x then 1 else 0 := by
          rw [Finset.sum_comm]
    _ = ∑ x ∈ F, (S.support x ∩ M).card := by
          apply Finset.sum_congr rfl
          intro x hx
          exact hcount x
    _ = ∑ x ∈ F, 1 := by
          apply Finset.sum_congr rfl
          intro x hx
          rw [hmark x hx]
    _ = 6 := by simp [hF]

/-- The canonical left private label on an actual triple-line of the K3.1
path.  Its existence is forced by the private-transversal theorem. -/
noncomputable def threeFourPathTripleLeftPrivatePoint
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
    (hthree : S.lineCount 3 = 6) (x : Block)
    (hx : x ∈ S.lineBlocksOfSize 3) : Point :=
  (Finset.card_eq_one.mp
    (three_four_path_six_three_line_is_private_transversal
      S hcard a b c ha hb hc hab hca hcb hthree hx).2.1).choose

/-- The canonical right private label on an actual triple-line of the K3.1
path. -/
noncomputable def threeFourPathTripleRightPrivatePoint
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
    (hthree : S.lineCount 3 = 6) (x : Block)
    (hx : x ∈ S.lineBlocksOfSize 3) : Point :=
  (Finset.card_eq_one.mp
    (three_four_path_six_three_line_is_private_transversal
      S hcard a b c ha hb hc hab hca hcb hthree hx).2.2).choose

/-- The canonical left choice belongs to its triple-line and to the literal
left private pencil. -/
theorem threeFourPathTripleLeftPrivatePoint_mem
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
    (hthree : S.lineCount 3 = 6) (x : Block)
    (hx : x ∈ S.lineBlocksOfSize 3) :
    threeFourPathTripleLeftPrivatePoint S hcard a b c ha hb hc hab hca hcb
      hthree x hx ∈ S.support x ∩ threeFourPathLeftPrivate S a c := by
  rw [(Finset.card_eq_one.mp
    (three_four_path_six_three_line_is_private_transversal
      S hcard a b c ha hb hc hab hca hcb hthree hx).2.1).choose_spec]
  simp [threeFourPathTripleLeftPrivatePoint]

/-- The canonical right choice belongs to its triple-line and to the literal
right private pencil. -/
theorem threeFourPathTripleRightPrivatePoint_mem
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
    (hthree : S.lineCount 3 = 6) (x : Block)
    (hx : x ∈ S.lineBlocksOfSize 3) :
    threeFourPathTripleRightPrivatePoint S hcard a b c ha hb hc hab hca hcb
      hthree x hx ∈ S.support x ∩ threeFourPathRightPrivate S b c := by
  rw [(Finset.card_eq_one.mp
    (three_four_path_six_three_line_is_private_transversal
      S hcard a b c ha hb hc hab hca hcb hthree hx).2.2).choose_spec]
  simp [threeFourPathTripleRightPrivatePoint]

/-- Inside one middle-label fibre, the canonical left-private label determines
the actual triple-line.  This is just uniqueness of a line through the pair
consisting of that middle and left-private label. -/
theorem three_four_path_middle_fibre_left_choice_injective
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
    (hthree : S.lineCount 3 = 6) (m : Point)
    {x y : Block} (hx : x ∈ S.lineBlocksOfSize 3)
    (hy : y ∈ S.lineBlocksOfSize 3)
    (hmx : m ∈ S.support x) (hmy : m ∈ S.support y)
    (hmprivate : m ∈ threeFourPathMiddlePrivate S a b c)
    (hleft : threeFourPathTripleLeftPrivatePoint
      S hcard a b c ha hb hc hab hca hcb hthree x hx =
        threeFourPathTripleLeftPrivatePoint
          S hcard a b c ha hb hc hab hca hcb hthree y hy) : x = y := by
  let ellx : LineBlock S := ⟨x, (S.mem_blocksOfKindSize.mp hx).1⟩
  let elly : LineBlock S := ⟨y, (S.mem_blocksOfKindSize.mp hy).1⟩
  by_contra hxy
  have hel : ellx ≠ elly := by
    intro heq
    apply hxy
    exact congrArg Subtype.val heq
  have hinter := S.distinct_line_inter_card_lt_two hel
  change (S.support x ∩ S.support y).card < 2 at hinter
  let l := threeFourPathTripleLeftPrivatePoint
    S hcard a b c ha hb hc hab hca hcb hthree x hx
  have hlx : l ∈ S.support x :=
    (Finset.mem_inter.mp
      (threeFourPathTripleLeftPrivatePoint_mem
        S hcard a b c ha hb hc hab hca hcb hthree x hx)).1
  have hly : l ∈ S.support y := by
    have hright := threeFourPathTripleLeftPrivatePoint_mem
      S hcard a b c ha hb hc hab hca hcb hthree y hy
    change threeFourPathTripleLeftPrivatePoint
      S hcard a b c ha hb hc hab hca hcb hthree x hx ∈ S.support y
    rw [hleft]
    exact (Finset.mem_inter.mp hright).1
  have hml : m ≠ l := by
    intro hml
    have hlprivate : l ∈ threeFourPathLeftPrivate S a c :=
      (Finset.mem_inter.mp
        (threeFourPathTripleLeftPrivatePoint_mem
          S hcard a b c ha hb hc hab hca hcb hthree x hx)).2
    rw [← hml] at hlprivate
    exact Finset.disjoint_left.mp
      (three_four_path_private_families_pairwise_disjoint S a b c hab).1.symm
      hmprivate hlprivate
  have hpairSub : ({m, l} : Finset Point) ⊆ S.support x ∩ S.support y := by
    intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl
    · exact Finset.mem_inter.mpr ⟨hmx, hmy⟩
    · exact Finset.mem_inter.mpr ⟨hlx, hly⟩
  have hpairCard : ({m, l} : Finset Point).card = 2 := by simp [hml]
  have htwo : 2 ≤ (S.support x ∩ S.support y).card := by
    rw [← hpairCard]
    exact Finset.card_le_card hpairSub
  omega

/-- Each fibre above one of the two middle-pencil labels contains at most
three triple-lines: map a line to its unique left-private label. -/
theorem three_four_path_middle_fibre_card_le_three
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
    (hthree : S.lineCount 3 = 6) (m : Point)
    (hm : m ∈ threeFourPathMiddlePrivate S a b c) :
    ((S.lineBlocksOfSize 3).filter fun x => m ∈ S.support x).card ≤ 3 := by
  classical
  let F := (S.lineBlocksOfSize 3).filter fun x => m ∈ S.support x
  let L := threeFourPathLeftPrivate S a c
  have hLcard : L.card = 3 := by
    obtain ⟨hleft, _, _⟩ := three_four_path_private_family_cards
      S a b c ha hb hc hab hca hcb
    exact hleft
  have hbound : F.card ≤ L.card := by
    apply Finset.card_le_card_of_injOn
      (fun x => if hx : x ∈ S.lineBlocksOfSize 3 then
        threeFourPathTripleLeftPrivatePoint
          S hcard a b c ha hb hc hab hca hcb hthree x hx else m)
    · intro x hx
      have hxthree : x ∈ S.lineBlocksOfSize 3 :=
        (Finset.mem_filter.mp hx).1
      simpa [hxthree] using (Finset.mem_inter.mp
        (threeFourPathTripleLeftPrivatePoint_mem
          S hcard a b c ha hb hc hab hca hcb hthree x hxthree)).2
    · intro x hx y hy heq
      have hxthree : x ∈ S.lineBlocksOfSize 3 :=
        (Finset.mem_filter.mp hx).1
      have hythree : y ∈ S.lineBlocksOfSize 3 :=
        (Finset.mem_filter.mp hy).1
      have hmx : m ∈ S.support x := (Finset.mem_filter.mp hx).2
      have hmy : m ∈ S.support y := (Finset.mem_filter.mp hy).2
      exact three_four_path_middle_fibre_left_choice_injective
        S hcard a b c ha hb hc hab hca hcb hthree m hxthree hythree
        hmx hmy hm (by simpa [hxthree, hythree] using heq)
  calc
    ((S.lineBlocksOfSize 3).filter fun x => m ∈ S.support x).card = F.card := rfl
    _ ≤ L.card := hbound
    _ = 3 := hLcard

/-- The six actual private transversals split into two exact three-line
fibres, one above each of the two middle-pencil labels. -/
theorem three_four_path_exists_two_middle_fibres_card_three
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
    ∃ m₀ m₁ : Point, m₀ ≠ m₁ ∧
      threeFourPathMiddlePrivate S a b c = {m₀, m₁} ∧
      ((S.lineBlocksOfSize 3).filter fun x => m₀ ∈ S.support x).card = 3 ∧
        ((S.lineBlocksOfSize 3).filter fun x => m₁ ∈ S.support x).card = 3 := by
  have hprivate := three_four_path_private_family_cards
    S a b c ha hb hc hab hca hcb
  obtain ⟨m₀, m₁, hmne, hM⟩ := Finset.card_eq_two.mp hprivate.2.1
  have hsum := three_four_path_six_three_line_middle_fibre_card_sum
    S hcard a b c ha hb hc hab hca hcb hthree
  rw [hM] at hsum
  have hmnot : m₀ ∉ ({m₁} : Finset Point) := by simpa using hmne
  rw [Finset.sum_insert hmnot, Finset.sum_singleton] at hsum
  have hm₀ : m₀ ∈ threeFourPathMiddlePrivate S a b c := by rw [hM]; simp
  have hm₁ : m₁ ∈ threeFourPathMiddlePrivate S a b c := by rw [hM]; simp
  have hle₀ := three_four_path_middle_fibre_card_le_three
    S hcard a b c ha hb hc hab hca hcb hthree m₀ hm₀
  have hle₁ := three_four_path_middle_fibre_card_le_three
    S hcard a b c ha hb hc hab hca hcb hthree m₁ hm₁
  refine ⟨m₀, m₁, hmne, hM, ?_, ?_⟩ <;> omega

/-- On an exact three-line middle fibre, the canonical left-private choice
uses all three left-pencil labels exactly once.  This is the first of the two
finite permutation encodings of the K3.1 grid. -/
theorem three_four_path_middle_fibre_left_choices_cover_private
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
    (hthree : S.lineCount 3 = 6) (m : Point)
    (hm : m ∈ threeFourPathMiddlePrivate S a b c)
    (hFcard : ((S.lineBlocksOfSize 3).filter fun x => m ∈ S.support x).card = 3) :
    ∃ f : Block → Point,
      ((S.lineBlocksOfSize 3).filter fun x => m ∈ S.support x).image f =
        threeFourPathLeftPrivate S a c ∧
      ∀ x (hx : x ∈ (S.lineBlocksOfSize 3).filter fun x => m ∈ S.support x),
        f x = threeFourPathTripleLeftPrivatePoint
          S hcard a b c ha hb hc hab hca hcb hthree x
            (Finset.mem_filter.mp hx).1 := by
  classical
  let F := (S.lineBlocksOfSize 3).filter fun x => m ∈ S.support x
  let L := threeFourPathLeftPrivate S a c
  let f : Block → Point := fun x => if hx : x ∈ S.lineBlocksOfSize 3 then
    threeFourPathTripleLeftPrivatePoint
      S hcard a b c ha hb hc hab hca hcb hthree x hx else m
  have hf (x : Block) (hxthree : x ∈ S.lineBlocksOfSize 3) :
      f x = threeFourPathTripleLeftPrivatePoint
        S hcard a b c ha hb hc hab hca hcb hthree x hxthree := by
    dsimp [f]
    rw [dif_pos hxthree]
  have hLcard : L.card = 3 := by
    obtain ⟨hleft, _, _⟩ := three_four_path_private_family_cards
      S a b c ha hb hc hab hca hcb
    exact hleft
  have himageSub : F.image f ⊆ L := by
    intro l hl
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hl
    have hxthree : x ∈ S.lineBlocksOfSize 3 :=
      (Finset.mem_filter.mp hx).1
    rw [hf x hxthree]
    exact (Finset.mem_inter.mp
      (threeFourPathTripleLeftPrivatePoint_mem
        S hcard a b c ha hb hc hab hca hcb hthree x hxthree)).2
  have hinj : Set.InjOn f ↑F := by
    intro x hx y hy hxy
    have hxthree : x ∈ S.lineBlocksOfSize 3 :=
      (Finset.mem_filter.mp hx).1
    have hythree : y ∈ S.lineBlocksOfSize 3 :=
      (Finset.mem_filter.mp hy).1
    have hmx : m ∈ S.support x := (Finset.mem_filter.mp hx).2
    have hmy : m ∈ S.support y := (Finset.mem_filter.mp hy).2
    have hchoice : threeFourPathTripleLeftPrivatePoint
        S hcard a b c ha hb hc hab hca hcb hthree x hxthree =
        threeFourPathTripleLeftPrivatePoint
          S hcard a b c ha hb hc hab hca hcb hthree y hythree :=
      (hf x hxthree).symm.trans (hxy.trans (hf y hythree))
    exact three_four_path_middle_fibre_left_choice_injective
      S hcard a b c ha hb hc hab hca hcb hthree m hxthree hythree
      hmx hmy hm hchoice
  have himageCard : (F.image f).card = 3 := by
    rw [Finset.card_image_iff.mpr hinj]
    exact hFcard
  have hcover : F.image f = L :=
    Finset.eq_of_subset_of_card_le himageSub (by rw [himageCard, hLcard])
  refine ⟨f, ?_, ?_⟩
  · exact hcover
  · intro x hx
    have hxthree : x ∈ S.lineBlocksOfSize 3 :=
      (Finset.mem_filter.mp hx).1
    exact hf x hxthree

/-- The symmetric second matching: every exact middle fibre also uses all
three right-private labels exactly once.  It is obtained by exchanging the
two outer bases in the first matching theorem. -/
theorem three_four_path_middle_fibre_right_choices_cover_private
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
    (hthree : S.lineCount 3 = 6) (m : Point)
    (hm : m ∈ threeFourPathMiddlePrivate S a b c)
    (hFcard : ((S.lineBlocksOfSize 3).filter fun x => m ∈ S.support x).card = 3) :
    ∃ f : Block → Point,
      ((S.lineBlocksOfSize 3).filter fun x => m ∈ S.support x).image f =
        threeFourPathRightPrivate S b c := by
  have hmswap : m ∈ threeFourPathMiddlePrivate S b a c := by
    simpa [threeFourPathMiddlePrivate, Finset.union_comm] using hm
  obtain ⟨f, hcover, _⟩ := three_four_path_middle_fibre_left_choices_cover_private
    S hcard b a c hb ha hc hab.symm hcb hca hthree m hmswap hFcard
  refine ⟨f, ?_⟩
  simpa [threeFourPathLeftPrivate, threeFourPathRightPrivate] using hcover

/-- The two three-line middle fibres have no shared private grid cell.  More
concretely, two triple-lines marked by different middle labels cannot have
both the same left and the same right private label.  This is the finite
relative-derangement condition before projective normalization. -/
theorem three_four_path_distinct_middle_fibres_no_shared_private_pair
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
    (hthree : S.lineCount 3 = 6) (m n : Point)
    (hmn : m ≠ n)
    {x y : Block} (hx : x ∈ S.lineBlocksOfSize 3)
    (hy : y ∈ S.lineBlocksOfSize 3)
    (hmx : m ∈ S.support x) (hny : n ∈ S.support y)
    (hml : m ∈ threeFourPathMiddlePrivate S a b c)
    (hnl : n ∈ threeFourPathMiddlePrivate S a b c)
    (hleft : threeFourPathTripleLeftPrivatePoint
      S hcard a b c ha hb hc hab hca hcb hthree x hx =
        threeFourPathTripleLeftPrivatePoint
          S hcard a b c ha hb hc hab hca hcb hthree y hy)
    (hright : threeFourPathTripleRightPrivatePoint
      S hcard a b c ha hb hc hab hca hcb hthree x hx =
        threeFourPathTripleRightPrivatePoint
          S hcard a b c ha hb hc hab hca hcb hthree y hy) : False := by
  let ellx : LineBlock S := ⟨x, (S.mem_blocksOfKindSize.mp hx).1⟩
  let elly : LineBlock S := ⟨y, (S.mem_blocksOfKindSize.mp hy).1⟩
  by_cases hxy : x = y
  · subst y
    have hmiddle := three_four_path_six_three_line_middle_card_eq_one
      S hcard a b c ha hb hc hab hca hcb hthree hx
    have hpairSub : ({m, n} : Finset Point) ⊆
        S.support x ∩ threeFourPathMiddlePrivate S a b c := by
      intro z hz
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with rfl | rfl
      · exact Finset.mem_inter.mpr ⟨hmx, hml⟩
      · exact Finset.mem_inter.mpr ⟨hny, hnl⟩
    have hpairCard : ({m, n} : Finset Point).card = 2 := by simp [hmn]
    have htwo : 2 ≤ (S.support x ∩ threeFourPathMiddlePrivate S a b c).card := by
      rw [← hpairCard]
      exact Finset.card_le_card hpairSub
    omega
  · have hel : ellx ≠ elly := by
      intro heq
      apply hxy
      exact congrArg Subtype.val heq
    have hinter := S.distinct_line_inter_card_lt_two hel
    change (S.support x ∩ S.support y).card < 2 at hinter
    let l := threeFourPathTripleLeftPrivatePoint
      S hcard a b c ha hb hc hab hca hcb hthree x hx
    let r := threeFourPathTripleRightPrivatePoint
      S hcard a b c ha hb hc hab hca hcb hthree x hx
    have hlx : l ∈ S.support x := (Finset.mem_inter.mp
      (threeFourPathTripleLeftPrivatePoint_mem
        S hcard a b c ha hb hc hab hca hcb hthree x hx)).1
    have hly : l ∈ S.support y := by
      change threeFourPathTripleLeftPrivatePoint
        S hcard a b c ha hb hc hab hca hcb hthree x hx ∈ S.support y
      rw [hleft]
      exact (Finset.mem_inter.mp
        (threeFourPathTripleLeftPrivatePoint_mem
          S hcard a b c ha hb hc hab hca hcb hthree y hy)).1
    have hrx : r ∈ S.support x := (Finset.mem_inter.mp
      (threeFourPathTripleRightPrivatePoint_mem
        S hcard a b c ha hb hc hab hca hcb hthree x hx)).1
    have hry : r ∈ S.support y := by
      change threeFourPathTripleRightPrivatePoint
        S hcard a b c ha hb hc hab hca hcb hthree x hx ∈ S.support y
      rw [hright]
      exact (Finset.mem_inter.mp
        (threeFourPathTripleRightPrivatePoint_mem
          S hcard a b c ha hb hc hab hca hcb hthree y hy)).1
    have hlr : l ≠ r := by
      intro heq
      have hlprivate : l ∈ threeFourPathLeftPrivate S a c :=
        (Finset.mem_inter.mp
          (threeFourPathTripleLeftPrivatePoint_mem
            S hcard a b c ha hb hc hab hca hcb hthree x hx)).2
      have hrprivate : r ∈ threeFourPathRightPrivate S b c :=
        (Finset.mem_inter.mp
          (threeFourPathTripleRightPrivatePoint_mem
            S hcard a b c ha hb hc hab hca hcb hthree x hx)).2
      rw [← heq] at hrprivate
      exact Finset.disjoint_left.mp
        (three_four_path_private_families_pairwise_disjoint S a b c hab).2.1
        hlprivate hrprivate
    have hpairSub : ({l, r} : Finset Point) ⊆ S.support x ∩ S.support y := by
      intro z hz
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with rfl | rfl
      · exact Finset.mem_inter.mpr ⟨hlx, hly⟩
      · exact Finset.mem_inter.mpr ⟨hrx, hry⟩
    have hpairCard : ({l, r} : Finset Point).card = 2 := by simp [hlr]
    have htwo : 2 ≤ (S.support x ∩ S.support y).card := by
      rw [← hpairCard]
      exact Finset.card_le_card hpairSub
    omega

/-- Canonical finite permutation census of the equality K3.1 path: the six
actual triple-lines split over two distinct middle labels into two 3-line
fibres, and each fibre covers both outer private three-pencils. -/
theorem three_four_path_two_fibre_two_matching_census
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
    ∃ m₀ m₁ : Point, m₀ ≠ m₁ ∧
      threeFourPathMiddlePrivate S a b c = {m₀, m₁} ∧
      ∃ f₀ f₁ g₀ g₁ : Block → Point,
        ((S.lineBlocksOfSize 3).filter fun x => m₀ ∈ S.support x).image f₀ =
          threeFourPathLeftPrivate S a c ∧
        ((S.lineBlocksOfSize 3).filter fun x => m₁ ∈ S.support x).image f₁ =
          threeFourPathLeftPrivate S a c ∧
        ((S.lineBlocksOfSize 3).filter fun x => m₀ ∈ S.support x).image g₀ =
          threeFourPathRightPrivate S b c ∧
        ((S.lineBlocksOfSize 3).filter fun x => m₁ ∈ S.support x).image g₁ =
          threeFourPathRightPrivate S b c := by
  obtain ⟨m₀, m₁, hmne, hM, hF₀, hF₁⟩ :=
    three_four_path_exists_two_middle_fibres_card_three
      S hcard a b c ha hb hc hab hca hcb hthree
  have hm₀ : m₀ ∈ threeFourPathMiddlePrivate S a b c := by rw [hM]; simp
  have hm₁ : m₁ ∈ threeFourPathMiddlePrivate S a b c := by rw [hM]; simp
  obtain ⟨f₀, hf₀, _⟩ := three_four_path_middle_fibre_left_choices_cover_private
    S hcard a b c ha hb hc hab hca hcb hthree m₀ hm₀ hF₀
  obtain ⟨f₁, hf₁, _⟩ := three_four_path_middle_fibre_left_choices_cover_private
    S hcard a b c ha hb hc hab hca hcb hthree m₁ hm₁ hF₁
  obtain ⟨g₀, hg₀⟩ := three_four_path_middle_fibre_right_choices_cover_private
    S hcard a b c ha hb hc hab hca hcb hthree m₀ hm₀ hF₀
  obtain ⟨g₁, hg₁⟩ := three_four_path_middle_fibre_right_choices_cover_private
    S hcard a b c ha hb hc hab hca hcb hthree m₁ hm₁ hF₁
  exact ⟨m₀, m₁, hmne, hM, f₀, f₁, g₀, g₁, hf₀, hf₁, hg₀, hg₁⟩

/-- Canonical `Fin 3` indexing of one exact middle fibre of actual
triple-lines. -/
noncomputable def threeFourPathMiddleFibreEquiv
    {Point : Type u} {Block : Type v} [Fintype Point] [Fintype Block]
    [DecidableEq Point] (S : BlockSystem Point Block) (m : Point)
    (hFcard : ((S.lineBlocksOfSize 3).filter fun x => m ∈ S.support x).card = 3) :
    Fin 3 ≃ ↥((S.lineBlocksOfSize 3).filter fun x => m ∈ S.support x) :=
  by
    classical
    exact finThreeEquivFinset _ hFcard

/-- The left private label carried by an indexed line of an exact middle
fibre.  Together with the coverage theorem it is a permutation of the left
private three-pencil. -/
noncomputable def threeFourPathMiddleFibreLeftChoice
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
    (hthree : S.lineCount 3 = 6) (m : Point)
    (hFcard : ((S.lineBlocksOfSize 3).filter fun x => m ∈ S.support x).card = 3)
    (i : Fin 3) : Point :=
  let e := threeFourPathMiddleFibreEquiv S m hFcard
  threeFourPathTripleLeftPrivatePoint S hcard a b c ha hb hc hab hca hcb
    hthree (e i).1 (Finset.mem_filter.mp (e i).2).1

/-- The right private label carried by an indexed line of an exact middle
fibre. -/
noncomputable def threeFourPathMiddleFibreRightChoice
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
    (hthree : S.lineCount 3 = 6) (m : Point)
    (hFcard : ((S.lineBlocksOfSize 3).filter fun x => m ∈ S.support x).card = 3)
    (i : Fin 3) : Point :=
  let e := threeFourPathMiddleFibreEquiv S m hFcard
  threeFourPathTripleRightPrivatePoint S hcard a b c ha hb hc hab hca hcb
    hthree (e i).1 (Finset.mem_filter.mp (e i).2).1

/-- Indexed form of the finite relative derangement: the two exact fibres
cannot select the same left-and-right private grid cell at any pair of
`Fin 3` indices. -/
theorem three_four_path_indexed_fibres_no_shared_private_pair
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
    (hthree : S.lineCount 3 = 6) (m n : Point)
    (hmn : m ≠ n)
    (hm : m ∈ threeFourPathMiddlePrivate S a b c)
    (hn : n ∈ threeFourPathMiddlePrivate S a b c)
    (hFm : ((S.lineBlocksOfSize 3).filter fun x => m ∈ S.support x).card = 3)
    (hFn : ((S.lineBlocksOfSize 3).filter fun x => n ∈ S.support x).card = 3)
    (i j : Fin 3)
    (hleft : threeFourPathMiddleFibreLeftChoice
      S hcard a b c ha hb hc hab hca hcb hthree m hFm i =
        threeFourPathMiddleFibreLeftChoice
          S hcard a b c ha hb hc hab hca hcb hthree n hFn j)
    (hright : threeFourPathMiddleFibreRightChoice
      S hcard a b c ha hb hc hab hca hcb hthree m hFm i =
        threeFourPathMiddleFibreRightChoice
          S hcard a b c ha hb hc hab hca hcb hthree n hFn j) : False := by
  let em := threeFourPathMiddleFibreEquiv S m hFm
  let en := threeFourPathMiddleFibreEquiv S n hFn
  have hxi : (em i).1 ∈ S.lineBlocksOfSize 3 :=
    (Finset.mem_filter.mp (em i).2).1
  have hyj : (en j).1 ∈ S.lineBlocksOfSize 3 :=
    (Finset.mem_filter.mp (en j).2).1
  have hmxi : m ∈ S.support (em i).1 :=
    (Finset.mem_filter.mp (em i).2).2
  have hnyj : n ∈ S.support (en j).1 :=
    (Finset.mem_filter.mp (en j).2).2
  apply three_four_path_distinct_middle_fibres_no_shared_private_pair
    S hcard a b c ha hb hc hab hca hcb hthree m n hmn hxi hyj
    hmxi hnyj hm hn
  · simpa [threeFourPathMiddleFibreLeftChoice, em, en] using hleft
  · simpa [threeFourPathMiddleFibreRightChoice, em, en] using hright

/-- Any injective code on the three standard fibre indices is canonically a
permutation.  This finite bridge is used to normalize the first matching to
the diagonal before reading the second matching as a relative permutation. -/
noncomputable def finThreePermutationOfInjective
    (f : Fin 3 → Fin 3) (hf : Function.Injective f) : Fin 3 ≃ Fin 3 :=
  Equiv.ofBijective f ⟨hf, Finite.injective_iff_surjective.mp hf⟩

/-- A relative permutation with no fixed index is one of the two derangements
of three letters.  We record the codes in the convention used by the
parameterized grid endpoint: `3` and `4`. -/
theorem finThree_derangement_code_three_or_four
    (σ : Fin 3 ≃ Fin 3) (hderange : ∀ i : Fin 3, σ i ≠ i) :
    (∀ i, σ i = ![1, 2, 0] i) ∨ (∀ i, σ i = ![2, 0, 1] i) := by
  fin_cases σ
  · exfalso
    exact hderange 0 rfl
  · exfalso
    apply hderange 0
    simp [Equiv.swap_apply_def]
  · exfalso
    apply hderange 2
    simp [Equiv.swap_apply_def]
  · left
    intro i
    fin_cases i <;> simp [Equiv.swap_apply_def]
  · exfalso
    apply hderange 1
    simp [Equiv.swap_apply_def]
  · right
    intro i
    fin_cases i <;> simp [Equiv.swap_apply_def]

/-- After normalizing one of two three-by-three matchings to the diagonal,
absence of a shared cell says exactly that their relative permutation has no
fixed point.  Hence its code is one of the two grid derangements. -/
theorem finThree_relative_permutation_code_three_or_four
    (first second : Fin 3 ≃ Fin 3)
    (hnoShared : ∀ i : Fin 3, first i ≠ second i) :
    ∃ σ : Fin 3 ≃ Fin 3,
      (∀ i, σ i ≠ i) ∧
      ((∀ i, σ i = ![1, 2, 0] i) ∨
        (∀ i, σ i = ![2, 0, 1] i)) := by
  let σ := first.symm.trans second
  have hderange : ∀ i : Fin 3, σ i ≠ i := by
    intro i hfix
    let j := first.symm i
    apply hnoShared j
    change first j = second j
    simpa [j, σ] using hfix.symm
  exact ⟨σ, hderange, finThree_derangement_code_three_or_four σ hderange⟩

/-! ## Actual dual-projective bridge -/

/-- Extract the determined affine line carried by a line-tagged block of a
concrete V1 block system.  This is definitionally available from the tagged
carrier, rather than being chosen as extra geometric data. -/
noncomputable def threeFourPathActualDeterminedLine
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    (cfg : Configuration Point) (ell : LineBlock (blockSystem cfg)) :
    DeterminedLine cfg := by
  rcases ell with ⟨b, hb⟩
  cases b with
  | inl L => exact L
  | inr C => simp [blockSystem, geometricBlockSystem, geometricBlockKind] at hb

/-- The concrete block-system support of a line block is the support of its
canonically extracted determined affine line. -/
theorem three_four_path_actualDeterminedLine_support
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    (cfg : Configuration Point) (ell : LineBlock (blockSystem cfg)) :
    lineSupport cfg (threeFourPathActualDeterminedLine cfg ell) =
      (blockSystem cfg).support ell.1 := by
  rcases ell with ⟨b, hb⟩
  cases b with
  | inl L => rfl
  | inr C => simp [blockSystem, geometricBlockSystem, geometricBlockKind] at hb

/-- The actual dual projective vertex represented by a concrete line block. -/
noncomputable def threeFourPathActualDualVertex
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    (cfg : Configuration Point) (ell : LineBlock (blockSystem cfg)) :
    RealProjectivePoint :=
  determinedLineDualVertex cfg (threeFourPathActualDeterminedLine cfg ell)

/-- Concrete block support membership is exactly incidence of the label's
dual projective line with the actual dual vertex of that block. -/
theorem three_four_path_actual_dual_incident_iff
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    (cfg : Configuration Point) (ell : LineBlock (blockSystem cfg)) (q : Point) :
    (labelDualArrangement cfg).Incident
      (threeFourPathActualDualVertex cfg ell) q ↔
        q ∈ (blockSystem cfg).support ell.1 := by
  change (labelDualArrangement cfg).Incident
      (determinedLineDualVertex cfg (threeFourPathActualDeterminedLine cfg ell)) q ↔ _
  rw [labelDual_incident_determinedLine_iff, ← mem_lineSupport,
    three_four_path_actualDeterminedLine_support]

/-- Two distinct labels on one concrete line block determine its actual dual
vertex as the literal intersection of their dual projective lines. -/
theorem three_four_path_actual_dualVertex_eq_labelIntersection
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    (cfg : Configuration Point) (ell : LineBlock (blockSystem cfg))
    {q r : Point} (hqr : q ≠ r)
    (hq : q ∈ (blockSystem cfg).support ell.1)
    (hr : r ∈ (blockSystem cfg).support ell.1) :
    threeFourPathActualDualVertex cfg ell =
      (labelDualArrangement cfg).intersection q r := by
  apply labelDual_eq_intersection_of_incident cfg hqr
  · exact (three_four_path_actual_dual_incident_iff cfg ell q).2 hq
  · exact (three_four_path_actual_dual_incident_iff cfg ell r).2 hr

/-! ## Fibre matchings on the two outer private pencils -/

/-- The right-private choice is injective on each fixed middle fibre, by the
same two-label line-ownership argument as on the left.  It is stated
explicitly rather than hidden behind a symmetry convention, since the two
resulting bijections will be compared as actual grid matchings. -/
theorem three_four_path_middle_fibre_right_choice_injective
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
    (hthree : S.lineCount 3 = 6) (m : Point)
    {x y : Block} (hx : x ∈ S.lineBlocksOfSize 3)
    (hy : y ∈ S.lineBlocksOfSize 3)
    (hmx : m ∈ S.support x) (hmy : m ∈ S.support y)
    (hmprivate : m ∈ threeFourPathMiddlePrivate S a b c)
    (hright : threeFourPathTripleRightPrivatePoint
      S hcard a b c ha hb hc hab hca hcb hthree x hx =
        threeFourPathTripleRightPrivatePoint
          S hcard a b c ha hb hc hab hca hcb hthree y hy) : x = y := by
  apply three_four_path_middle_fibre_left_choice_injective
    S hcard b a c hb ha hc hab.symm hcb hca hthree m hx hy hmx hmy
  · simpa [threeFourPathMiddlePrivate, Finset.union_comm] using hmprivate
  · simpa [threeFourPathTripleLeftPrivatePoint,
      threeFourPathTripleRightPrivatePoint,
      threeFourPathLeftPrivate, threeFourPathRightPrivate] using hright

/-- Each indexed member of an exact middle fibre carries a literal
left-private label. -/
theorem three_four_path_middle_fibre_left_choice_mem
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
    (hthree : S.lineCount 3 = 6) (m : Point)
    (hFcard : ((S.lineBlocksOfSize 3).filter fun x => m ∈ S.support x).card = 3)
    (i : Fin 3) :
    threeFourPathMiddleFibreLeftChoice
      S hcard a b c ha hb hc hab hca hcb hthree m hFcard i ∈
        threeFourPathLeftPrivate S a c := by
  have hmem := threeFourPathTripleLeftPrivatePoint_mem
    S hcard a b c ha hb hc hab hca hcb hthree
      (threeFourPathMiddleFibreEquiv S m hFcard i).1
      (Finset.mem_filter.mp
        (threeFourPathMiddleFibreEquiv S m hFcard i).2).1
  simpa [threeFourPathMiddleFibreLeftChoice] using
    (Finset.mem_inter.mp hmem).2

/-- Each indexed member of an exact middle fibre carries a literal
right-private label. -/
theorem three_four_path_middle_fibre_right_choice_mem
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
    (hthree : S.lineCount 3 = 6) (m : Point)
    (hFcard : ((S.lineBlocksOfSize 3).filter fun x => m ∈ S.support x).card = 3)
    (i : Fin 3) :
    threeFourPathMiddleFibreRightChoice
      S hcard a b c ha hb hc hab hca hcb hthree m hFcard i ∈
        threeFourPathRightPrivate S b c := by
  have hmem := threeFourPathTripleRightPrivatePoint_mem
    S hcard a b c ha hb hc hab hca hcb hthree
      (threeFourPathMiddleFibreEquiv S m hFcard i).1
      (Finset.mem_filter.mp
        (threeFourPathMiddleFibreEquiv S m hFcard i).2).1
  simpa [threeFourPathMiddleFibreRightChoice] using
    (Finset.mem_inter.mp hmem).2

/-- The canonical `Fin 3` code of a member of an actual three-label
carrier.  The subtype witness is part of the construction, so no label is
chosen externally. -/
noncomputable def finThreeCodeOfMem
    {Point : Type u} [DecidableEq Point]
    (X : Finset Point) (hX : X.card = 3) (q : Point) (hq : q ∈ X) : Fin 3 :=
  (finThreeEquivFinset X hX).symm ⟨q, hq⟩

/-- Decoding the canonical finite code recovers the original carrier
member. -/
theorem finThreeEquivFinset_codeOfMem
    {Point : Type u} [DecidableEq Point]
    (X : Finset Point) (hX : X.card = 3) (q : Point) (hq : q ∈ X) :
    (finThreeEquivFinset X hX (finThreeCodeOfMem X hX q hq)).1 = q := by
  simp [finThreeCodeOfMem]

/-- Equality of the canonical finite codes of members of one three-carrier
forces equality of the underlying labels. -/
theorem finThreeCodeOfMem_injective
    {Point : Type u} [DecidableEq Point]
    (X : Finset Point) (hX : X.card = 3) (q r : Point)
    (hq : q ∈ X) (hr : r ∈ X)
    (hcode : finThreeCodeOfMem X hX q hq = finThreeCodeOfMem X hX r hr) :
    q = r := by
  have hsub : (⟨q, hq⟩ : ↥X) = ⟨r, hr⟩ :=
    (finThreeEquivFinset X hX).symm.injective hcode
  exact congrArg Subtype.val hsub

/-- Read the left-private label of an indexed middle fibre as one of the
three canonical left-pencil indices. -/
noncomputable def threeFourPathMiddleFibreLeftCode
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
    (hthree : S.lineCount 3 = 6) (m : Point)
    (hFcard : ((S.lineBlocksOfSize 3).filter fun x => m ∈ S.support x).card = 3)
    (i : Fin 3) : Fin 3 :=
  finThreeCodeOfMem
    (threeFourPathLeftPrivate S a c)
    (three_four_path_private_family_cards S a b c ha hb hc hab hca hcb).1
    (threeFourPathMiddleFibreLeftChoice
      S hcard a b c ha hb hc hab hca hcb hthree m hFcard i)
    (three_four_path_middle_fibre_left_choice_mem
      S hcard a b c ha hb hc hab hca hcb hthree m hFcard i)

/-- The analogous canonical right-pencil index. -/
noncomputable def threeFourPathMiddleFibreRightCode
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
    (hthree : S.lineCount 3 = 6) (m : Point)
    (hFcard : ((S.lineBlocksOfSize 3).filter fun x => m ∈ S.support x).card = 3)
    (i : Fin 3) : Fin 3 :=
  finThreeCodeOfMem
    (threeFourPathRightPrivate S b c)
    (three_four_path_private_family_cards S a b c ha hb hc hab hca hcb).2.2
    (threeFourPathMiddleFibreRightChoice
      S hcard a b c ha hb hc hab hca hcb hthree m hFcard i)
    (three_four_path_middle_fibre_right_choice_mem
      S hcard a b c ha hb hc hab hca hcb hthree m hFcard i)

/-- On one middle fibre the canonical left-pencil code is injective. -/
theorem three_four_path_middle_fibre_leftCode_injective
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
    (hthree : S.lineCount 3 = 6) (m : Point)
    (hm : m ∈ threeFourPathMiddlePrivate S a b c)
    (hFcard : ((S.lineBlocksOfSize 3).filter fun x => m ∈ S.support x).card = 3) :
    Function.Injective (threeFourPathMiddleFibreLeftCode
      S hcard a b c ha hb hc hab hca hcb hthree m hFcard) := by
  intro i j hij
  have hchoice : threeFourPathMiddleFibreLeftChoice
      S hcard a b c ha hb hc hab hca hcb hthree m hFcard i =
        threeFourPathMiddleFibreLeftChoice
          S hcard a b c ha hb hc hab hca hcb hthree m hFcard j := by
    apply finThreeCodeOfMem_injective
      (threeFourPathLeftPrivate S a c)
      (three_four_path_private_family_cards S a b c ha hb hc hab hca hcb).1
      (threeFourPathMiddleFibreLeftChoice
        S hcard a b c ha hb hc hab hca hcb hthree m hFcard i)
      (threeFourPathMiddleFibreLeftChoice
        S hcard a b c ha hb hc hab hca hcb hthree m hFcard j)
      (three_four_path_middle_fibre_left_choice_mem
        S hcard a b c ha hb hc hab hca hcb hthree m hFcard i)
      (three_four_path_middle_fibre_left_choice_mem
        S hcard a b c ha hb hc hab hca hcb hthree m hFcard j)
    simpa [threeFourPathMiddleFibreLeftCode] using hij
  have hxi : (threeFourPathMiddleFibreEquiv S m hFcard i).1 ∈
      S.lineBlocksOfSize 3 :=
    (Finset.mem_filter.mp (threeFourPathMiddleFibreEquiv S m hFcard i).2).1
  have hxj : (threeFourPathMiddleFibreEquiv S m hFcard j).1 ∈
      S.lineBlocksOfSize 3 :=
    (Finset.mem_filter.mp (threeFourPathMiddleFibreEquiv S m hFcard j).2).1
  have hmi : m ∈ S.support (threeFourPathMiddleFibreEquiv S m hFcard i).1 :=
    (Finset.mem_filter.mp (threeFourPathMiddleFibreEquiv S m hFcard i).2).2
  have hmj : m ∈ S.support (threeFourPathMiddleFibreEquiv S m hFcard j).1 :=
    (Finset.mem_filter.mp (threeFourPathMiddleFibreEquiv S m hFcard j).2).2
  apply (threeFourPathMiddleFibreEquiv S m hFcard).injective
  apply Subtype.ext
  apply three_four_path_middle_fibre_left_choice_injective
    S hcard a b c ha hb hc hab hca hcb hthree m hxi hxj hmi hmj hm
  simpa [threeFourPathMiddleFibreLeftChoice] using hchoice

/-- On one middle fibre the canonical right-pencil code is injective. -/
theorem three_four_path_middle_fibre_rightCode_injective
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
    (hthree : S.lineCount 3 = 6) (m : Point)
    (hm : m ∈ threeFourPathMiddlePrivate S a b c)
    (hFcard : ((S.lineBlocksOfSize 3).filter fun x => m ∈ S.support x).card = 3) :
    Function.Injective (threeFourPathMiddleFibreRightCode
      S hcard a b c ha hb hc hab hca hcb hthree m hFcard) := by
  intro i j hij
  have hchoice : threeFourPathMiddleFibreRightChoice
      S hcard a b c ha hb hc hab hca hcb hthree m hFcard i =
        threeFourPathMiddleFibreRightChoice
          S hcard a b c ha hb hc hab hca hcb hthree m hFcard j := by
    apply finThreeCodeOfMem_injective
      (threeFourPathRightPrivate S b c)
      (three_four_path_private_family_cards S a b c ha hb hc hab hca hcb).2.2
      (threeFourPathMiddleFibreRightChoice
        S hcard a b c ha hb hc hab hca hcb hthree m hFcard i)
      (threeFourPathMiddleFibreRightChoice
        S hcard a b c ha hb hc hab hca hcb hthree m hFcard j)
      (three_four_path_middle_fibre_right_choice_mem
        S hcard a b c ha hb hc hab hca hcb hthree m hFcard i)
      (three_four_path_middle_fibre_right_choice_mem
        S hcard a b c ha hb hc hab hca hcb hthree m hFcard j)
    simpa [threeFourPathMiddleFibreRightCode] using hij
  have hxi : (threeFourPathMiddleFibreEquiv S m hFcard i).1 ∈
      S.lineBlocksOfSize 3 :=
    (Finset.mem_filter.mp (threeFourPathMiddleFibreEquiv S m hFcard i).2).1
  have hxj : (threeFourPathMiddleFibreEquiv S m hFcard j).1 ∈
      S.lineBlocksOfSize 3 :=
    (Finset.mem_filter.mp (threeFourPathMiddleFibreEquiv S m hFcard j).2).1
  have hmi : m ∈ S.support (threeFourPathMiddleFibreEquiv S m hFcard i).1 :=
    (Finset.mem_filter.mp (threeFourPathMiddleFibreEquiv S m hFcard i).2).2
  have hmj : m ∈ S.support (threeFourPathMiddleFibreEquiv S m hFcard j).1 :=
    (Finset.mem_filter.mp (threeFourPathMiddleFibreEquiv S m hFcard j).2).2
  apply (threeFourPathMiddleFibreEquiv S m hFcard).injective
  apply Subtype.ext
  apply three_four_path_middle_fibre_right_choice_injective
    S hcard a b c ha hb hc hab hca hcb hthree m hxi hxj hmi hmj hm
  simpa [threeFourPathMiddleFibreRightChoice] using hchoice

/-- The left labels in an exact three-line middle fibre form a genuine
permutation of the three left-private labels. -/
noncomputable def threeFourPathMiddleFibreLeftPermutation
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
    (hthree : S.lineCount 3 = 6) (m : Point)
    (hm : m ∈ threeFourPathMiddlePrivate S a b c)
    (hFcard : ((S.lineBlocksOfSize 3).filter fun x => m ∈ S.support x).card = 3) :
    Fin 3 ≃ Fin 3 :=
  finThreePermutationOfInjective
    (threeFourPathMiddleFibreLeftCode
      S hcard a b c ha hb hc hab hca hcb hthree m hFcard)
    (three_four_path_middle_fibre_leftCode_injective
      S hcard a b c ha hb hc hab hca hcb hthree m hm hFcard)

/-- The right labels in an exact three-line middle fibre form the symmetric
permutation of the three right-private labels. -/
noncomputable def threeFourPathMiddleFibreRightPermutation
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
    (hthree : S.lineCount 3 = 6) (m : Point)
    (hm : m ∈ threeFourPathMiddlePrivate S a b c)
    (hFcard : ((S.lineBlocksOfSize 3).filter fun x => m ∈ S.support x).card = 3) :
    Fin 3 ≃ Fin 3 :=
  finThreePermutationOfInjective
    (threeFourPathMiddleFibreRightCode
      S hcard a b c ha hb hc hab hca hcb hthree m hFcard)
    (three_four_path_middle_fibre_rightCode_injective
      S hcard a b c ha hb hc hab hca hcb hthree m hm hFcard)

/-- The actual grid matching carried by one middle label: use its
left-private label as the row index and its right-private label as the
column index.  Both sides are genuine finite permutations extracted from
the fibre, not a chosen grid labelling. -/
noncomputable def threeFourPathMiddleFibreMatching
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
    (hthree : S.lineCount 3 = 6) (m : Point)
    (hm : m ∈ threeFourPathMiddlePrivate S a b c)
    (hFcard : ((S.lineBlocksOfSize 3).filter fun x => m ∈ S.support x).card = 3) :
    Fin 3 ≃ Fin 3 :=
  (threeFourPathMiddleFibreLeftPermutation
    S hcard a b c ha hb hc hab hca hcb hthree m hm hFcard).symm.trans
    (threeFourPathMiddleFibreRightPermutation
      S hcard a b c ha hb hc hab hca hcb hthree m hm hFcard)

/-- Reading the matching at a left index selects the right-private code of
the unique actual triple-line with that left-private label. -/
theorem three_four_path_middle_fibre_matching_apply
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
    (hthree : S.lineCount 3 = 6) (m : Point)
    (hm : m ∈ threeFourPathMiddlePrivate S a b c)
    (hFcard : ((S.lineBlocksOfSize 3).filter fun x => m ∈ S.support x).card = 3)
    (i : Fin 3) :
    threeFourPathMiddleFibreMatching
      S hcard a b c ha hb hc hab hca hcb hthree m hm hFcard i =
      threeFourPathMiddleFibreRightCode
        S hcard a b c ha hb hc hab hca hcb hthree m hFcard
        ((threeFourPathMiddleFibreLeftPermutation
          S hcard a b c ha hb hc hab hca hcb hthree m hm hFcard).symm i) := by
  rfl

/-- The two actual fibre matchings have no shared grid cell.  This is the
literal support-level version of edge-disjoint transversals, transported to
the canonical `Fin 3` indices. -/
theorem three_four_path_two_middle_fibre_matchings_no_shared
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
    (hthree : S.lineCount 3 = 6) (m n : Point)
    (hmn : m ≠ n)
    (hm : m ∈ threeFourPathMiddlePrivate S a b c)
    (hn : n ∈ threeFourPathMiddlePrivate S a b c)
    (hFm : ((S.lineBlocksOfSize 3).filter fun x => m ∈ S.support x).card = 3)
    (hFn : ((S.lineBlocksOfSize 3).filter fun x => n ∈ S.support x).card = 3) :
    ∀ i : Fin 3,
      threeFourPathMiddleFibreMatching
        S hcard a b c ha hb hc hab hca hcb hthree m hm hFm i ≠
        threeFourPathMiddleFibreMatching
          S hcard a b c ha hb hc hab hca hcb hthree n hn hFn i := by
  intro i hmatch
  let im := (threeFourPathMiddleFibreLeftPermutation
    S hcard a b c ha hb hc hab hca hcb hthree m hm hFm).symm i
  let jn := (threeFourPathMiddleFibreLeftPermutation
    S hcard a b c ha hb hc hab hca hcb hthree n hn hFn).symm i
  have hleftCodeM : threeFourPathMiddleFibreLeftCode
      S hcard a b c ha hb hc hab hca hcb hthree m hFm im = i := by
    change (threeFourPathMiddleFibreLeftPermutation
      S hcard a b c ha hb hc hab hca hcb hthree m hm hFm) im = i
    exact (threeFourPathMiddleFibreLeftPermutation
      S hcard a b c ha hb hc hab hca hcb hthree m hm hFm).apply_symm_apply i
  have hleftCodeN : threeFourPathMiddleFibreLeftCode
      S hcard a b c ha hb hc hab hca hcb hthree n hFn jn = i := by
    change (threeFourPathMiddleFibreLeftPermutation
      S hcard a b c ha hb hc hab hca hcb hthree n hn hFn) jn = i
    exact (threeFourPathMiddleFibreLeftPermutation
      S hcard a b c ha hb hc hab hca hcb hthree n hn hFn).apply_symm_apply i
  have hleft : threeFourPathMiddleFibreLeftChoice
      S hcard a b c ha hb hc hab hca hcb hthree m hFm im =
        threeFourPathMiddleFibreLeftChoice
          S hcard a b c ha hb hc hab hca hcb hthree n hFn jn := by
    apply finThreeCodeOfMem_injective
      (threeFourPathLeftPrivate S a c)
      (three_four_path_private_family_cards S a b c ha hb hc hab hca hcb).1
      (threeFourPathMiddleFibreLeftChoice
        S hcard a b c ha hb hc hab hca hcb hthree m hFm im)
      (threeFourPathMiddleFibreLeftChoice
        S hcard a b c ha hb hc hab hca hcb hthree n hFn jn)
      (three_four_path_middle_fibre_left_choice_mem
        S hcard a b c ha hb hc hab hca hcb hthree m hFm im)
      (three_four_path_middle_fibre_left_choice_mem
        S hcard a b c ha hb hc hab hca hcb hthree n hFn jn)
    calc
      finThreeCodeOfMem _ _ _ _ =
          threeFourPathMiddleFibreLeftCode
            S hcard a b c ha hb hc hab hca hcb hthree m hFm im := rfl
      _ = i := hleftCodeM
      _ = threeFourPathMiddleFibreLeftCode
            S hcard a b c ha hb hc hab hca hcb hthree n hFn jn :=
          hleftCodeN.symm
      _ = finThreeCodeOfMem _ _ _ _ := rfl
  have hrightCode : threeFourPathMiddleFibreRightCode
      S hcard a b c ha hb hc hab hca hcb hthree m hFm im =
        threeFourPathMiddleFibreRightCode
          S hcard a b c ha hb hc hab hca hcb hthree n hFn jn := by
    calc
      threeFourPathMiddleFibreRightCode
          S hcard a b c ha hb hc hab hca hcb hthree m hFm im =
          threeFourPathMiddleFibreMatching
            S hcard a b c ha hb hc hab hca hcb hthree m hm hFm i := by
              simpa [im] using (three_four_path_middle_fibre_matching_apply
                S hcard a b c ha hb hc hab hca hcb hthree m hm hFm i).symm
      _ = threeFourPathMiddleFibreMatching
            S hcard a b c ha hb hc hab hca hcb hthree n hn hFn i := hmatch
      _ = threeFourPathMiddleFibreRightCode
            S hcard a b c ha hb hc hab hca hcb hthree n hFn jn := by
              simpa [jn] using (three_four_path_middle_fibre_matching_apply
                S hcard a b c ha hb hc hab hca hcb hthree n hn hFn i)
  have hright : threeFourPathMiddleFibreRightChoice
      S hcard a b c ha hb hc hab hca hcb hthree m hFm im =
        threeFourPathMiddleFibreRightChoice
          S hcard a b c ha hb hc hab hca hcb hthree n hFn jn := by
    apply finThreeCodeOfMem_injective
      (threeFourPathRightPrivate S b c)
      (three_four_path_private_family_cards S a b c ha hb hc hab hca hcb).2.2
      (threeFourPathMiddleFibreRightChoice
        S hcard a b c ha hb hc hab hca hcb hthree m hFm im)
      (threeFourPathMiddleFibreRightChoice
        S hcard a b c ha hb hc hab hca hcb hthree n hFn jn)
      (three_four_path_middle_fibre_right_choice_mem
        S hcard a b c ha hb hc hab hca hcb hthree m hFm im)
      (three_four_path_middle_fibre_right_choice_mem
        S hcard a b c ha hb hc hab hca hcb hthree n hFn jn)
    simpa [threeFourPathMiddleFibreRightCode] using hrightCode
  exact three_four_path_indexed_fibres_no_shared_private_pair
    S hcard a b c ha hb hc hab hca hcb hthree m n hmn hm hn hFm hFn im jn
    hleft hright

/-- The relative code of the two actual middle-fibre matchings is one of
the two real-grid derangements `3,4`.  This packages the finite K3.1
equality census in exactly the form consumed by the determinant endpoint. -/
theorem three_four_path_two_middle_fibre_relative_code_three_or_four
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
    (hthree : S.lineCount 3 = 6) (m n : Point)
    (hmn : m ≠ n)
    (hm : m ∈ threeFourPathMiddlePrivate S a b c)
    (hn : n ∈ threeFourPathMiddlePrivate S a b c)
    (hFm : ((S.lineBlocksOfSize 3).filter fun x => m ∈ S.support x).card = 3)
    (hFn : ((S.lineBlocksOfSize 3).filter fun x => n ∈ S.support x).card = 3) :
    ∃ σ : Fin 3 ≃ Fin 3,
      (∀ i, σ i ≠ i) ∧
      ((∀ i, σ i = ![1, 2, 0] i) ∨
        (∀ i, σ i = ![2, 0, 1] i)) := by
  exact finThree_relative_permutation_code_three_or_four
    (threeFourPathMiddleFibreMatching
      S hcard a b c ha hb hc hab hca hcb hthree m hm hFm)
    (threeFourPathMiddleFibreMatching
      S hcard a b c ha hb hc hab hca hcb hthree n hn hFn)
    (three_four_path_two_middle_fibre_matchings_no_shared
      S hcard a b c ha hb hc hab hca hcb hthree m n hmn hm hn hFm hFn)

/-! ## Actual dual grid frame -/

/-- Three actual labels carried by one determined line give the corresponding
dual incidence: the dual line of the third label passes through the literal
crossing of the first two label-dual lines. -/
theorem three_four_path_actual_dual_cross_incident_of_three_mem
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    (cfg : Configuration Point) (ell : LineBlock (blockSystem cfg))
    {m l r : Point} (hlr : l ≠ r)
    (hm : m ∈ (blockSystem cfg).support ell.1)
    (hl : l ∈ (blockSystem cfg).support ell.1)
    (hr : r ∈ (blockSystem cfg).support ell.1) :
    homogeneousLift (cfg m) ⬝ᵥ
      crossProduct (homogeneousLift (cfg l)) (homogeneousLift (cfg r)) = 0 := by
  let L := threeFourPathActualDeterminedLine cfg ell
  let A : Erdos506.Finite.KSubset Point 2 :=
    ⟨{l, r}, by simp [hlr]⟩
  have hlL : l ∈ lineSupport cfg L := by
    change l ∈ lineSupport cfg (threeFourPathActualDeterminedLine cfg ell)
    rw [three_four_path_actualDeterminedLine_support]
    exact hl
  have hrL : r ∈ lineSupport cfg L := by
    change r ∈ lineSupport cfg (threeFourPathActualDeterminedLine cfg ell)
    rw [three_four_path_actualDeterminedLine_support]
    exact hr
  have hmL : m ∈ lineSupport cfg L := by
    change m ∈ lineSupport cfg (threeFourPathActualDeterminedLine cfg ell)
    rw [three_four_path_actualDeterminedLine_support]
    exact hm
  have hmem : ∀ z ∈ A.1, cfg z ∈ L.1 := by
    intro z hz
    have hz' : z = l ∨ z = r := by simpa [A] using hz
    rcases hz' with rfl | rfl
    · exact mem_lineSupport.mp hlL
    · exact mem_lineSupport.mp hrL
  have hpair : lineOfPair cfg A = L.1 :=
    lineOfPair_eq_of_mem_of_direction_finrank_one cfg A L.1 hmem
      L.direction_finrank
  have hspan : affineSpan ℝ ({cfg l, cfg r} : Set Point2) = L.1 := by
    calc
      affineSpan ℝ ({cfg l, cfg r} : Set Point2) = lineOfPair cfg A := by
        simpa [A] using (lineOfPair_pair cfg hlr).symm
      _ = L.1 := hpair
  have hmspan : cfg m ∈ affineSpan ℝ ({cfg l, cfg r} : Set Point2) := by
    rw [hspan]
    exact mem_lineSupport.mp hmL
  have hincident : homogeneousIncident (cfg m) (lineCovector (cfg l) (cfg r)) :=
    (homogeneousIncident_lineCovector_iff_mem_affineSpan
      (cfg.injective.ne hlr)).mpr hmspan
  simpa [homogeneousIncident, lineCovector] using hincident

/-- Two labels on one actual base line and a label on a support-disjoint
second base line are projectively independent.  This is the exact finite
support source of the nonzero minors required by the dual covector frame. -/
theorem three_four_path_actual_det_ne_zero_of_two_left_one_right
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    (cfg : Configuration Point) (a b : LineBlock (blockSystem cfg))
    (hab : Disjoint ((blockSystem cfg).support a.1)
      ((blockSystem cfg).support b.1))
    {l₀ l₁ r : Point} (hl₀ : l₀ ∈ (blockSystem cfg).support a.1)
    (hl₁ : l₁ ∈ (blockSystem cfg).support a.1)
    (hr : r ∈ (blockSystem cfg).support b.1) (hl : l₀ ≠ l₁) :
    Matrix.det ![homogeneousLift (cfg l₀), homogeneousLift (cfg l₁),
      homogeneousLift (cfg r)] ≠ 0 := by
  intro hdet
  have hincident : homogeneousIncident (cfg r) (lineCovector (cfg l₀) (cfg l₁)) :=
    (homogeneousIncident_lineCovector_iff_det_eq_zero
      (cfg l₀) (cfg l₁) (cfg r)).2 hdet
  let L := threeFourPathActualDeterminedLine cfg a
  let A : Erdos506.Finite.KSubset Point 2 :=
    ⟨{l₀, l₁}, by simp [hl]⟩
  have hl₀L : l₀ ∈ lineSupport cfg L := by
    change l₀ ∈ lineSupport cfg (threeFourPathActualDeterminedLine cfg a)
    rw [three_four_path_actualDeterminedLine_support]
    exact hl₀
  have hl₁L : l₁ ∈ lineSupport cfg L := by
    change l₁ ∈ lineSupport cfg (threeFourPathActualDeterminedLine cfg a)
    rw [three_four_path_actualDeterminedLine_support]
    exact hl₁
  have hmem : ∀ z ∈ A.1, cfg z ∈ L.1 := by
    intro z hz
    have hz' : z = l₀ ∨ z = l₁ := by simpa [A] using hz
    rcases hz' with rfl | rfl
    · exact mem_lineSupport.mp hl₀L
    · exact mem_lineSupport.mp hl₁L
  have hpair : lineOfPair cfg A = L.1 :=
    lineOfPair_eq_of_mem_of_direction_finrank_one cfg A L.1 hmem
      L.direction_finrank
  have hspan : affineSpan ℝ ({cfg l₀, cfg l₁} : Set Point2) = L.1 := by
    calc
      affineSpan ℝ ({cfg l₀, cfg l₁} : Set Point2) = lineOfPair cfg A := by
        simpa [A] using (lineOfPair_pair cfg hl).symm
      _ = L.1 := hpair
  have hrspan : cfg r ∈ affineSpan ℝ ({cfg l₀, cfg l₁} : Set Point2) :=
    (homogeneousIncident_lineCovector_iff_mem_affineSpan
      (cfg.injective.ne hl)).mp hincident
  have hrL : r ∈ lineSupport cfg L := by
    apply mem_lineSupport.mpr
    rw [← hspan]
    exact hrspan
  have hra : r ∈ (blockSystem cfg).support a.1 := by
    change r ∈ lineSupport cfg (threeFourPathActualDeterminedLine cfg a) at hrL
    rw [three_four_path_actualDeterminedLine_support] at hrL
    exact hrL
  exact Finset.disjoint_left.mp hab hra hr

/-- Cyclically rotating three homogeneous rows leaves their determinant
unchanged. -/
theorem three_four_path_actual_det_rotate_rows
    (u v w : Homogeneous3) :
    Matrix.det ![u, v, w] = Matrix.det ![v, w, u] := by
  simp [Matrix.det_fin_three]
  ring

/-- The four raw covectors used to normalize a dual `3×3` grid: two actual
left-private label lines followed by two actual right-private label lines. -/
def threeFourPathActualDualFrameCovector
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    (cfg : Configuration Point) (left right : Fin 3 → Point) :
    Fin 4 → Homogeneous3
  | 0 => homogeneousLift (cfg (left 0))
  | 1 => homogeneousLift (cfg (left 1))
  | 2 => homogeneousLift (cfg (right 0))
  | 3 => homogeneousLift (cfg (right 1))

/-- Two actual disjoint three-label pencils supply a genuine projective
complete quadrangle.  The only input is literal support membership and
injectivity of their finite indexing. -/
theorem three_four_path_actual_dualFrame_generalPosition
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    (cfg : Configuration Point) (a b : LineBlock (blockSystem cfg))
    (hab : Disjoint ((blockSystem cfg).support a.1)
      ((blockSystem cfg).support b.1))
    (left right : Fin 3 → Point)
    (hleft : ∀ i, left i ∈ (blockSystem cfg).support a.1)
    (hright : ∀ i, right i ∈ (blockSystem cfg).support b.1)
    (hleftInj : Function.Injective left)
    (hrightInj : Function.Injective right) :
    CompleteQuadrangleGeneralPosition
      (threeFourPathActualDualFrameCovector cfg left right 0)
      (threeFourPathActualDualFrameCovector cfg left right 1)
      (threeFourPathActualDualFrameCovector cfg left right 2)
      (threeFourPathActualDualFrameCovector cfg left right 3) := by
  have hl01 : left 0 ≠ left 1 := by
    intro h
    have h01 : (0 : Fin 3) = 1 := hleftInj h
    omega
  have hr01 : right 0 ≠ right 1 := by
    intro h
    have h01 : (0 : Fin 3) = 1 := hrightInj h
    omega
  constructor
  · simpa [threeFourPathActualDualFrameCovector] using
      (three_four_path_actual_det_ne_zero_of_two_left_one_right
        cfg a b hab (hleft 0) (hleft 1) (hright 0) hl01)
  · simpa [threeFourPathActualDualFrameCovector] using
      (three_four_path_actual_det_ne_zero_of_two_left_one_right
        cfg a b hab (hleft 0) (hleft 1) (hright 1) hl01)
  · rw [three_four_path_actual_det_rotate_rows]
    simpa [threeFourPathActualDualFrameCovector] using
      (three_four_path_actual_det_ne_zero_of_two_left_one_right
        cfg b a hab.symm (hright 0) (hright 1) (hleft 0) hr01)
  · rw [three_four_path_actual_det_rotate_rows]
    simpa [threeFourPathActualDualFrameCovector] using
      (three_four_path_actual_det_ne_zero_of_two_left_one_right
        cfg b a hab.symm (hright 0) (hright 1) (hleft 1) hr01)

/-- The canonical projective covector frame forced by two actual disjoint
three-label pencils. -/
noncomputable def threeFourPathActualDualCovectorFrame
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    (cfg : Configuration Point) (a b : LineBlock (blockSystem cfg))
    (hab : Disjoint ((blockSystem cfg).support a.1)
      ((blockSystem cfg).support b.1))
    (left right : Fin 3 → Point)
    (hleft : ∀ i, left i ∈ (blockSystem cfg).support a.1)
    (hright : ∀ i, right i ∈ (blockSystem cfg).support b.1)
    (hleftInj : Function.Injective left)
    (hrightInj : Function.Injective right) :
    ProjectiveCovectorFrame (threeFourPathActualDualFrameCovector cfg left right) :=
  projectiveCovectorFrame (threeFourPathActualDualFrameCovector cfg left right)
    (three_four_path_actual_dualFrame_generalPosition
      cfg a b hab left right hleft hright hleftInj hrightInj)

/-! ### Affine post-chart for an actual dual frame -/

/-- Apply the fixed affine post-chart after an arbitrary actual dual
covector frame to a homogeneous point vector. -/
noncomputable def threeFourPathDualAffineHomogeneous
    {ell : Fin 4 → Homogeneous3} (F : ProjectiveCovectorFrame ell)
    (x : Homogeneous3) : Homogeneous3 :=
  twelveGridAffinePostPointMatrix *ᵥ projectivePointTransform F.G x

/-- The contragredient affine-chart transform of a raw dual line covector. -/
noncomputable def threeFourPathDualAffineCovector
    {ell : Fin 4 → Homogeneous3} (F : ProjectiveCovectorFrame ell)
    (u : Homogeneous3) : Homogeneous3 :=
  twelveGridAffinePostCovectorMatrix *ᵥ projectiveCovectorTransform F.G u

/-- The derived actual affine chart preserves the homogeneous pairing
exactly. -/
theorem three_four_path_dualAffineCovector_dot
    {ell : Fin 4 → Homogeneous3} (F : ProjectiveCovectorFrame ell)
    (u x : Homogeneous3) :
    threeFourPathDualAffineCovector F u ⬝ᵥ threeFourPathDualAffineHomogeneous F x =
      u ⬝ᵥ x := by
  unfold threeFourPathDualAffineCovector threeFourPathDualAffineHomogeneous
  rw [twelveGridAffinePost_dot,
    projectiveCovectorTransform_dot_pointTransform]

/-- The four frame covectors become the fixed affine rectangle lines
`x=-1,x=0,y=-1,y=0`, up to their unavoidable nonzero representatives. -/
theorem three_four_path_dualAffineCovector_frame
    {ell : Fin 4 → Homogeneous3} (F : ProjectiveCovectorFrame ell)
    (i : Fin 4) :
    threeFourPathDualAffineCovector F (ell i) =
      (F.scale i * twelveGridAffineFrameScale i) • twelveGridAffineFrameCovector i := by
  change twelveGridAffinePostCovectorMatrix *ᵥ
      projectiveCovectorTransform F.G (ell i) = _
  calc
    twelveGridAffinePostCovectorMatrix *ᵥ
        projectiveCovectorTransform F.G (ell i) =
        twelveGridAffinePostCovectorMatrix *ᵥ
          (F.scale i • projectiveCovectorNormalLine i) := by
      have h := congrArg (fun v : Homogeneous3 =>
        twelveGridAffinePostCovectorMatrix *ᵥ v) (F.map_covector i)
      simpa [projectiveCovectorTransform] using h
    _ = F.scale i •
        (twelveGridAffinePostCovectorMatrix *ᵥ projectiveCovectorNormalLine i) := by
      ext j
      fin_cases j <;>
        simp [twelveGridAffinePostCovectorMatrix, Matrix.mulVec,
          dotProduct, Fin.sum_univ_three] <;>
        ring
    _ = (F.scale i * twelveGridAffineFrameScale i) •
        twelveGridAffineFrameCovector i := by
      rw [twelveGridAffinePostCovector_normalLine]
      simp [smul_smul, mul_assoc]

/-- The total nonzero representative scale of an anchored affine frame
line. -/
noncomputable def threeFourPathDualAffineFrameScale
    {ell : Fin 4 → Homogeneous3} (F : ProjectiveCovectorFrame ell)
    (i : Fin 4) : ℝ :=
  F.scale i * twelveGridAffineFrameScale i

theorem three_four_path_dualAffineFrameScale_ne_zero
    {ell : Fin 4 → Homogeneous3} (F : ProjectiveCovectorFrame ell)
    (i : Fin 4) : threeFourPathDualAffineFrameScale F i ≠ 0 := by
  exact mul_ne_zero (F.scale_ne_zero i) (twelveGridAffineFrameScale_ne_zero i)

/-- The affine transform of a nonzero homogeneous vector remains nonzero. -/
theorem three_four_path_dualAffineHomogeneous_ne_zero
    {ell : Fin 4 → Homogeneous3} (F : ProjectiveCovectorFrame ell)
    (x : Homogeneous3) (hx : x ≠ 0) :
    threeFourPathDualAffineHomogeneous F x ≠ 0 := by
  intro hzero
  have hbefore : projectivePointTransform F.G x = 0 := by
    apply twelveGridAffinePostPoint_injective
    simpa [threeFourPathDualAffineHomogeneous] using hzero
  have hbefore_ne : projectivePointTransform F.G x ≠ 0 := by
    simpa [projectivePointTransform] using
      ((smul_ne_zero_iff_ne F.G).mpr hx)
  exact hbefore_ne hbefore

/-! ### Canonical actual matching cells -/

/-- For a fixed exact middle fibre, the canonical matching is realized by
an actual triple-line through the displayed left and right private labels.
The statement deliberately keeps the three labels as literal members of a
concrete support, so it can be transported to dual covector incidence without
introducing a synthetic grid object. -/
theorem three_four_path_middle_fibre_matching_support
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
    (hthree : S.lineCount 3 = 6) (m : Point)
    (hm : m ∈ threeFourPathMiddlePrivate S a b c)
    (hFcard : ((S.lineBlocksOfSize 3).filter fun x => m ∈ S.support x).card = 3)
    (i : Fin 3) :
    ∃ x : Block, x ∈ S.lineBlocksOfSize 3 ∧ m ∈ S.support x ∧
      (finThreeEquivFinset (threeFourPathLeftPrivate S a c)
        (three_four_path_private_family_cards S a b c ha hb hc hab hca hcb).1 i).1 ∈
          S.support x ∧
      (finThreeEquivFinset (threeFourPathRightPrivate S b c)
        (three_four_path_private_family_cards S a b c ha hb hc hab hca hcb).2.2
        (threeFourPathMiddleFibreMatching
          S hcard a b c ha hb hc hab hca hcb hthree m hm hFcard i)).1 ∈
          S.support x := by
  let e := threeFourPathMiddleFibreEquiv S m hFcard
  let j := (threeFourPathMiddleFibreLeftPermutation
    S hcard a b c ha hb hc hab hca hcb hthree m hm hFcard).symm i
  have hxthree : (e j).1 ∈ S.lineBlocksOfSize 3 :=
    (Finset.mem_filter.mp (e j).2).1
  have hmx : m ∈ S.support (e j).1 :=
    (Finset.mem_filter.mp (e j).2).2
  have hleftChoice : threeFourPathMiddleFibreLeftChoice
      S hcard a b c ha hb hc hab hca hcb hthree m hFcard j ∈
        S.support (e j).1 := by
    simpa [threeFourPathMiddleFibreLeftChoice, e] using
      (Finset.mem_inter.mp (threeFourPathTripleLeftPrivatePoint_mem
        S hcard a b c ha hb hc hab hca hcb hthree (e j).1 hxthree)).1
  have hrightChoice : threeFourPathMiddleFibreRightChoice
      S hcard a b c ha hb hc hab hca hcb hthree m hFcard j ∈
        S.support (e j).1 := by
    simpa [threeFourPathMiddleFibreRightChoice, e] using
      (Finset.mem_inter.mp (threeFourPathTripleRightPrivatePoint_mem
        S hcard a b c ha hb hc hab hca hcb hthree (e j).1 hxthree)).1
  have hleftCode : threeFourPathMiddleFibreLeftCode
      S hcard a b c ha hb hc hab hca hcb hthree m hFcard j = i := by
    change (threeFourPathMiddleFibreLeftPermutation
      S hcard a b c ha hb hc hab hca hcb hthree m hm hFcard) j = i
    exact (threeFourPathMiddleFibreLeftPermutation
      S hcard a b c ha hb hc hab hca hcb hthree m hm hFcard).apply_symm_apply i
  have hleftCanonical :
      (finThreeEquivFinset (threeFourPathLeftPrivate S a c)
        (three_four_path_private_family_cards S a b c ha hb hc hab hca hcb).1 i).1 =
        threeFourPathMiddleFibreLeftChoice
          S hcard a b c ha hb hc hab hca hcb hthree m hFcard j := by
    calc
      (finThreeEquivFinset (threeFourPathLeftPrivate S a c)
          (three_four_path_private_family_cards S a b c ha hb hc hab hca hcb).1 i).1 =
          (finThreeEquivFinset (threeFourPathLeftPrivate S a c)
            (three_four_path_private_family_cards S a b c ha hb hc hab hca hcb).1
            (threeFourPathMiddleFibreLeftCode
              S hcard a b c ha hb hc hab hca hcb hthree m hFcard j)).1 := by
            rw [hleftCode]
      _ = (finThreeEquivFinset (threeFourPathLeftPrivate S a c)
            (three_four_path_private_family_cards S a b c ha hb hc hab hca hcb).1
            (finThreeCodeOfMem (threeFourPathLeftPrivate S a c)
              (three_four_path_private_family_cards S a b c ha hb hc hab hca hcb).1
              (threeFourPathMiddleFibreLeftChoice
                S hcard a b c ha hb hc hab hca hcb hthree m hFcard j)
              (three_four_path_middle_fibre_left_choice_mem
                S hcard a b c ha hb hc hab hca hcb hthree m hFcard j))).1 := by
            rfl
      _ = threeFourPathMiddleFibreLeftChoice
            S hcard a b c ha hb hc hab hca hcb hthree m hFcard j :=
          finThreeEquivFinset_codeOfMem
            (threeFourPathLeftPrivate S a c)
            (three_four_path_private_family_cards S a b c ha hb hc hab hca hcb).1
            (threeFourPathMiddleFibreLeftChoice
              S hcard a b c ha hb hc hab hca hcb hthree m hFcard j)
            (three_four_path_middle_fibre_left_choice_mem
              S hcard a b c ha hb hc hab hca hcb hthree m hFcard j)
  have hmatching : threeFourPathMiddleFibreMatching
      S hcard a b c ha hb hc hab hca hcb hthree m hm hFcard i =
        threeFourPathMiddleFibreRightCode
          S hcard a b c ha hb hc hab hca hcb hthree m hFcard j := by
    simpa [j] using (three_four_path_middle_fibre_matching_apply
      S hcard a b c ha hb hc hab hca hcb hthree m hm hFcard i)
  have hrightCanonical :
      (finThreeEquivFinset (threeFourPathRightPrivate S b c)
        (three_four_path_private_family_cards S a b c ha hb hc hab hca hcb).2.2
        (threeFourPathMiddleFibreMatching
          S hcard a b c ha hb hc hab hca hcb hthree m hm hFcard i)).1 =
        threeFourPathMiddleFibreRightChoice
          S hcard a b c ha hb hc hab hca hcb hthree m hFcard j := by
    calc
      (finThreeEquivFinset (threeFourPathRightPrivate S b c)
          (three_four_path_private_family_cards S a b c ha hb hc hab hca hcb).2.2
          (threeFourPathMiddleFibreMatching
            S hcard a b c ha hb hc hab hca hcb hthree m hm hFcard i)).1 =
          (finThreeEquivFinset (threeFourPathRightPrivate S b c)
            (three_four_path_private_family_cards S a b c ha hb hc hab hca hcb).2.2
            (threeFourPathMiddleFibreRightCode
              S hcard a b c ha hb hc hab hca hcb hthree m hFcard j)).1 := by
            rw [hmatching]
      _ = (finThreeEquivFinset (threeFourPathRightPrivate S b c)
            (three_four_path_private_family_cards S a b c ha hb hc hab hca hcb).2.2
            (finThreeCodeOfMem (threeFourPathRightPrivate S b c)
              (three_four_path_private_family_cards S a b c ha hb hc hab hca hcb).2.2
              (threeFourPathMiddleFibreRightChoice
                S hcard a b c ha hb hc hab hca hcb hthree m hFcard j)
              (three_four_path_middle_fibre_right_choice_mem
                S hcard a b c ha hb hc hab hca hcb hthree m hFcard j))).1 := by
            rfl
      _ = threeFourPathMiddleFibreRightChoice
            S hcard a b c ha hb hc hab hca hcb hthree m hFcard j :=
          finThreeEquivFinset_codeOfMem
            (threeFourPathRightPrivate S b c)
            (three_four_path_private_family_cards S a b c ha hb hc hab hca hcb).2.2
            (threeFourPathMiddleFibreRightChoice
              S hcard a b c ha hb hc hab hca hcb hthree m hFcard j)
            (three_four_path_middle_fibre_right_choice_mem
              S hcard a b c ha hb hc hab hca hcb hthree m hFcard j)
  exact ⟨(e j).1, hxthree, hmx, hleftCanonical.symm ▸ hleftChoice,
    hrightCanonical.symm ▸ hrightChoice⟩

/-- The concrete relative matching of two middle fibres after the first one
has been normalized to the diagonal. -/
noncomputable def threeFourPathTwoMiddleFibreRelativeMatching
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
    (hthree : S.lineCount 3 = 6) (m n : Point)
    (hm : m ∈ threeFourPathMiddlePrivate S a b c)
    (hn : n ∈ threeFourPathMiddlePrivate S a b c)
    (hFm : ((S.lineBlocksOfSize 3).filter fun x => m ∈ S.support x).card = 3)
    (hFn : ((S.lineBlocksOfSize 3).filter fun x => n ∈ S.support x).card = 3) :
    Fin 3 ≃ Fin 3 :=
  (threeFourPathMiddleFibreMatching
    S hcard a b c ha hb hc hab hca hcb hthree m hm hFm).symm.trans
    (threeFourPathMiddleFibreMatching
      S hcard a b c ha hb hc hab hca hcb hthree n hn hFn)

/-- In the first-matching-normalized row coordinate, the relative matching
is literally the second matching evaluated at the inverse first coordinate. -/
theorem three_four_path_two_middle_fibre_relative_matching_apply
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
    (hthree : S.lineCount 3 = 6) (m n : Point)
    (hm : m ∈ threeFourPathMiddlePrivate S a b c)
    (hn : n ∈ threeFourPathMiddlePrivate S a b c)
    (hFm : ((S.lineBlocksOfSize 3).filter fun x => m ∈ S.support x).card = 3)
    (hFn : ((S.lineBlocksOfSize 3).filter fun x => n ∈ S.support x).card = 3)
    (i : Fin 3) :
    threeFourPathTwoMiddleFibreRelativeMatching
        S hcard a b c ha hb hc hab hca hcb hthree m n hm hn hFm hFn i =
      threeFourPathMiddleFibreMatching
        S hcard a b c ha hb hc hab hca hcb hthree n hn hFn
        ((threeFourPathMiddleFibreMatching
          S hcard a b c ha hb hc hab hca hcb hthree m hm hFm).symm i) := by
  rfl

/-- The literal relative matching is fixed-point-free because the two
actual fibres have no common private cell. -/
theorem three_four_path_two_middle_fibre_relative_matching_deranges
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
    (hthree : S.lineCount 3 = 6) (m n : Point)
    (hmn : m ≠ n)
    (hm : m ∈ threeFourPathMiddlePrivate S a b c)
    (hn : n ∈ threeFourPathMiddlePrivate S a b c)
    (hFm : ((S.lineBlocksOfSize 3).filter fun x => m ∈ S.support x).card = 3)
    (hFn : ((S.lineBlocksOfSize 3).filter fun x => n ∈ S.support x).card = 3) :
    ∀ i : Fin 3,
      threeFourPathTwoMiddleFibreRelativeMatching
        S hcard a b c ha hb hc hab hca hcb hthree m n hm hn hFm hFn i ≠ i := by
  intro i hfix
  let j := (threeFourPathMiddleFibreMatching
    S hcard a b c ha hb hc hab hca hcb hthree m hm hFm).symm i
  apply (three_four_path_two_middle_fibre_matchings_no_shared
    S hcard a b c ha hb hc hab hca hcb hthree m n hmn hm hn hFm hFn j)
  calc
    threeFourPathMiddleFibreMatching
        S hcard a b c ha hb hc hab hca hcb hthree m hm hFm j = i := by
          exact (threeFourPathMiddleFibreMatching
            S hcard a b c ha hb hc hab hca hcb hthree m hm hFm).apply_symm_apply i
    _ = threeFourPathTwoMiddleFibreRelativeMatching
          S hcard a b c ha hb hc hab hca hcb hthree m n hm hn hFm hFn i := hfix.symm
    _ = threeFourPathMiddleFibreMatching
          S hcard a b c ha hb hc hab hca hcb hthree n hn hFn j :=
        by simpa [j] using
          (three_four_path_two_middle_fibre_relative_matching_apply
            S hcard a b c ha hb hc hab hca hcb hthree m n hm hn hFm hFn i)

/-- The relative actual matching has exactly the two finite derangement
codes consumed by the real determinant endpoint. -/
theorem three_four_path_two_middle_fibre_relative_matching_code_three_or_four
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
    (hthree : S.lineCount 3 = 6) (m n : Point)
    (hmn : m ≠ n)
    (hm : m ∈ threeFourPathMiddlePrivate S a b c)
    (hn : n ∈ threeFourPathMiddlePrivate S a b c)
    (hFm : ((S.lineBlocksOfSize 3).filter fun x => m ∈ S.support x).card = 3)
    (hFn : ((S.lineBlocksOfSize 3).filter fun x => n ∈ S.support x).card = 3) :
    (∀ i, threeFourPathTwoMiddleFibreRelativeMatching
        S hcard a b c ha hb hc hab hca hcb hthree m n hm hn hFm hFn i = ![1, 2, 0] i) ∨
      (∀ i, threeFourPathTwoMiddleFibreRelativeMatching
        S hcard a b c ha hb hc hab hca hcb hthree m n hm hn hFm hFn i = ![2, 0, 1] i) := by
  exact finThree_derangement_code_three_or_four
    (threeFourPathTwoMiddleFibreRelativeMatching
      S hcard a b c ha hb hc hab hca hcb hthree m n hm hn hFm hFn)
    (three_four_path_two_middle_fibre_relative_matching_deranges
      S hcard a b c ha hb hc hab hca hcb hthree m n hmn hm hn hFm hFn)

/-- Transport one literal actual matching cell to the dual covector grid.
The middle label's dual covector vanishes at the crossing of its matching
left and right label covectors. -/
theorem three_four_path_actual_middle_fibre_matching_cross_incident
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    (cfg : Configuration Point) (hcard : Fintype.card Point = 10)
    (a b c : LineBlock (blockSystem cfg))
    (ha : ((blockSystem cfg).support a.1).card = 4)
    (hb : ((blockSystem cfg).support b.1).card = 4)
    (hc : ((blockSystem cfg).support c.1).card = 4)
    (hab : Disjoint ((blockSystem cfg).support a.1)
      ((blockSystem cfg).support b.1))
    (hca : ((blockSystem cfg).support c.1 ∩
      (blockSystem cfg).support a.1).card = 1)
    (hcb : ((blockSystem cfg).support c.1 ∩
      (blockSystem cfg).support b.1).card = 1)
    (hthree : (blockSystem cfg).lineCount 3 = 6) (m : Point)
    (hm : m ∈ threeFourPathMiddlePrivate (blockSystem cfg) a b c)
    (hFcard : (((blockSystem cfg).lineBlocksOfSize 3).filter
      fun x => m ∈ (blockSystem cfg).support x).card = 3)
    (i : Fin 3) :
    homogeneousLift (cfg m) ⬝ᵥ
      crossProduct
        (homogeneousLift (cfg
          (finThreeEquivFinset (threeFourPathLeftPrivate (blockSystem cfg) a c)
            (three_four_path_private_family_cards
              (blockSystem cfg) a b c ha hb hc hab hca hcb).1 i).1))
        (homogeneousLift (cfg
          (finThreeEquivFinset (threeFourPathRightPrivate (blockSystem cfg) b c)
            (three_four_path_private_family_cards
              (blockSystem cfg) a b c ha hb hc hab hca hcb).2.2
            (threeFourPathMiddleFibreMatching
              (blockSystem cfg) hcard a b c ha hb hc hab hca hcb hthree m hm hFcard i)).1)) = 0 := by
  obtain ⟨x, hx, hmx, hlx, hrx⟩ :=
    three_four_path_middle_fibre_matching_support
      (blockSystem cfg) hcard a b c ha hb hc hab hca hcb hthree m hm hFcard i
  let ell : LineBlock (blockSystem cfg) :=
    ⟨x, ((blockSystem cfg).mem_blocksOfKindSize.mp hx).1⟩
  have hleftPrivate :
      (finThreeEquivFinset (threeFourPathLeftPrivate (blockSystem cfg) a c)
        (three_four_path_private_family_cards
          (blockSystem cfg) a b c ha hb hc hab hca hcb).1 i).1 ∈
        threeFourPathLeftPrivate (blockSystem cfg) a c :=
    finThreeEquivFinset_mem _ _ _
  have hrightPrivate :
      (finThreeEquivFinset (threeFourPathRightPrivate (blockSystem cfg) b c)
        (three_four_path_private_family_cards
          (blockSystem cfg) a b c ha hb hc hab hca hcb).2.2
        (threeFourPathMiddleFibreMatching
          (blockSystem cfg) hcard a b c ha hb hc hab hca hcb hthree m hm hFcard i)).1 ∈
        threeFourPathRightPrivate (blockSystem cfg) b c :=
    finThreeEquivFinset_mem _ _ _
  have hlr :
      (finThreeEquivFinset (threeFourPathLeftPrivate (blockSystem cfg) a c)
        (three_four_path_private_family_cards
          (blockSystem cfg) a b c ha hb hc hab hca hcb).1 i).1 ≠
      (finThreeEquivFinset (threeFourPathRightPrivate (blockSystem cfg) b c)
        (three_four_path_private_family_cards
          (blockSystem cfg) a b c ha hb hc hab hca hcb).2.2
        (threeFourPathMiddleFibreMatching
          (blockSystem cfg) hcard a b c ha hb hc hab hca hcb hthree m hm hFcard i)).1 := by
    intro heq
    rw [← heq] at hrightPrivate
    exact Finset.disjoint_left.mp
      (three_four_path_private_families_pairwise_disjoint
        (blockSystem cfg) a b c hab).2.1 hleftPrivate hrightPrivate
  simpa [ell] using (three_four_path_actual_dual_cross_incident_of_three_mem
    cfg ell hlr (by simpa [ell] using hmx) (by simpa [ell] using hlx)
    (by simpa [ell] using hrx))

/-! ### Actual labels in the diagonal matching coordinate -/

/-- The literal left private carrier, with its canonical three-element
indexing exposed as a function to labels. -/
noncomputable def threeFourPathLeftPrivateLabel
    {Point : Type u} {Block : Type v} [Fintype Point] [Fintype Block]
    [DecidableEq Point]
    (S : BlockSystem Point Block) (a b c : LineBlock S)
    (ha : (S.support a.1).card = 4)
    (hb : (S.support b.1).card = 4)
    (hc : (S.support c.1).card = 4)
    (hab : Disjoint (S.support a.1) (S.support b.1))
    (hca : (S.support c.1 ∩ S.support a.1).card = 1)
    (hcb : (S.support c.1 ∩ S.support b.1).card = 1) :
    Fin 3 → Point := fun i =>
  (finThreeEquivFinset (threeFourPathLeftPrivate S a c)
    (three_four_path_private_family_cards S a b c ha hb hc hab hca hcb).1 i).1

/-- The literal right private carrier in the analogous canonical indexing. -/
noncomputable def threeFourPathRightPrivateLabel
    {Point : Type u} {Block : Type v} [Fintype Point] [Fintype Block]
    [DecidableEq Point]
    (S : BlockSystem Point Block) (a b c : LineBlock S)
    (ha : (S.support a.1).card = 4)
    (hb : (S.support b.1).card = 4)
    (hc : (S.support c.1).card = 4)
    (hab : Disjoint (S.support a.1) (S.support b.1))
    (hca : (S.support c.1 ∩ S.support a.1).card = 1)
    (hcb : (S.support c.1 ∩ S.support b.1).card = 1) :
    Fin 3 → Point := fun i =>
  (finThreeEquivFinset (threeFourPathRightPrivate S b c)
    (three_four_path_private_family_cards S a b c ha hb hc hab hca hcb).2.2 i).1

theorem three_four_path_leftPrivateLabel_mem
    {Point : Type u} {Block : Type v} [Fintype Point] [Fintype Block]
    [DecidableEq Point]
    (S : BlockSystem Point Block) (a b c : LineBlock S)
    (ha : (S.support a.1).card = 4)
    (hb : (S.support b.1).card = 4)
    (hc : (S.support c.1).card = 4)
    (hab : Disjoint (S.support a.1) (S.support b.1))
    (hca : (S.support c.1 ∩ S.support a.1).card = 1)
    (hcb : (S.support c.1 ∩ S.support b.1).card = 1) (i : Fin 3) :
    threeFourPathLeftPrivateLabel S a b c ha hb hc hab hca hcb i ∈
      S.support a.1 := by
  have hprivate : threeFourPathLeftPrivateLabel S a b c ha hb hc hab hca hcb i ∈
      threeFourPathLeftPrivate S a c := by
    simpa [threeFourPathLeftPrivateLabel] using
      (finThreeEquivFinset_mem (threeFourPathLeftPrivate S a c)
        (three_four_path_private_family_cards S a b c ha hb hc hab hca hcb).1 i)
  exact (Finset.mem_sdiff.mp hprivate).1

theorem three_four_path_rightPrivateLabel_mem
    {Point : Type u} {Block : Type v} [Fintype Point] [Fintype Block]
    [DecidableEq Point]
    (S : BlockSystem Point Block) (a b c : LineBlock S)
    (ha : (S.support a.1).card = 4)
    (hb : (S.support b.1).card = 4)
    (hc : (S.support c.1).card = 4)
    (hab : Disjoint (S.support a.1) (S.support b.1))
    (hca : (S.support c.1 ∩ S.support a.1).card = 1)
    (hcb : (S.support c.1 ∩ S.support b.1).card = 1) (i : Fin 3) :
    threeFourPathRightPrivateLabel S a b c ha hb hc hab hca hcb i ∈
      S.support b.1 := by
  have hprivate : threeFourPathRightPrivateLabel S a b c ha hb hc hab hca hcb i ∈
      threeFourPathRightPrivate S b c := by
    simpa [threeFourPathRightPrivateLabel] using
      (finThreeEquivFinset_mem (threeFourPathRightPrivate S b c)
        (three_four_path_private_family_cards S a b c ha hb hc hab hca hcb).2.2 i)
  exact (Finset.mem_sdiff.mp hprivate).1

theorem three_four_path_leftPrivateLabel_injective
    {Point : Type u} {Block : Type v} [Fintype Point] [Fintype Block]
    [DecidableEq Point]
    (S : BlockSystem Point Block) (a b c : LineBlock S)
    (ha : (S.support a.1).card = 4)
    (hb : (S.support b.1).card = 4)
    (hc : (S.support c.1).card = 4)
    (hab : Disjoint (S.support a.1) (S.support b.1))
    (hca : (S.support c.1 ∩ S.support a.1).card = 1)
    (hcb : (S.support c.1 ∩ S.support b.1).card = 1) :
    Function.Injective (threeFourPathLeftPrivateLabel S a b c ha hb hc hab hca hcb) := by
  intro i j hij
  apply (finThreeEquivFinset (threeFourPathLeftPrivate S a c)
    (three_four_path_private_family_cards S a b c ha hb hc hab hca hcb).1).injective
  apply Subtype.ext
  simpa [threeFourPathLeftPrivateLabel] using hij

theorem three_four_path_rightPrivateLabel_injective
    {Point : Type u} {Block : Type v} [Fintype Point] [Fintype Block]
    [DecidableEq Point]
    (S : BlockSystem Point Block) (a b c : LineBlock S)
    (ha : (S.support a.1).card = 4)
    (hb : (S.support b.1).card = 4)
    (hc : (S.support c.1).card = 4)
    (hab : Disjoint (S.support a.1) (S.support b.1))
    (hca : (S.support c.1 ∩ S.support a.1).card = 1)
    (hcb : (S.support c.1 ∩ S.support b.1).card = 1) :
    Function.Injective (threeFourPathRightPrivateLabel S a b c ha hb hc hab hca hcb) := by
  intro i j hij
  apply (finThreeEquivFinset (threeFourPathRightPrivate S b c)
    (three_four_path_private_family_cards S a b c ha hb hc hab hca hcb).2.2).injective
  apply Subtype.ext
  simpa [threeFourPathRightPrivateLabel] using hij

/-- In the right-indexed coordinate `i ↦ (M.symm i,i)`, the first middle
fibre is the literal diagonal of the actual dual grid. -/
theorem three_four_path_actual_first_matching_diagonal_cross_incident
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    (cfg : Configuration Point) (hcard : Fintype.card Point = 10)
    (a b c : LineBlock (blockSystem cfg))
    (ha : ((blockSystem cfg).support a.1).card = 4)
    (hb : ((blockSystem cfg).support b.1).card = 4)
    (hc : ((blockSystem cfg).support c.1).card = 4)
    (hab : Disjoint ((blockSystem cfg).support a.1)
      ((blockSystem cfg).support b.1))
    (hca : ((blockSystem cfg).support c.1 ∩
      (blockSystem cfg).support a.1).card = 1)
    (hcb : ((blockSystem cfg).support c.1 ∩
      (blockSystem cfg).support b.1).card = 1)
    (hthree : (blockSystem cfg).lineCount 3 = 6) (m : Point)
    (hm : m ∈ threeFourPathMiddlePrivate (blockSystem cfg) a b c)
    (hFm : (((blockSystem cfg).lineBlocksOfSize 3).filter
      fun x => m ∈ (blockSystem cfg).support x).card = 3)
    (i : Fin 3) :
    homogeneousLift (cfg m) ⬝ᵥ crossProduct
      (homogeneousLift (cfg (threeFourPathLeftPrivateLabel
        (blockSystem cfg) a b c ha hb hc hab hca hcb
        ((threeFourPathMiddleFibreMatching
          (blockSystem cfg) hcard a b c ha hb hc hab hca hcb hthree m hm hFm).symm i))))
      (homogeneousLift (cfg (threeFourPathRightPrivateLabel
        (blockSystem cfg) a b c ha hb hc hab hca hcb i))) = 0 := by
  have h := three_four_path_actual_middle_fibre_matching_cross_incident
    cfg hcard a b c ha hb hc hab hca hcb hthree m hm hFm
    ((threeFourPathMiddleFibreMatching
      (blockSystem cfg) hcard a b c ha hb hc hab hca hcb hthree m hm hFm).symm i)
  simpa [threeFourPathLeftPrivateLabel, threeFourPathRightPrivateLabel] using h

/-- The second middle fibre is the actual relative matching in the same
right-indexed coordinate. -/
theorem three_four_path_actual_second_matching_relative_cross_incident
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    (cfg : Configuration Point) (hcard : Fintype.card Point = 10)
    (a b c : LineBlock (blockSystem cfg))
    (ha : ((blockSystem cfg).support a.1).card = 4)
    (hb : ((blockSystem cfg).support b.1).card = 4)
    (hc : ((blockSystem cfg).support c.1).card = 4)
    (hab : Disjoint ((blockSystem cfg).support a.1)
      ((blockSystem cfg).support b.1))
    (hca : ((blockSystem cfg).support c.1 ∩
      (blockSystem cfg).support a.1).card = 1)
    (hcb : ((blockSystem cfg).support c.1 ∩
      (blockSystem cfg).support b.1).card = 1)
    (hthree : (blockSystem cfg).lineCount 3 = 6) (m n : Point)
    (hm : m ∈ threeFourPathMiddlePrivate (blockSystem cfg) a b c)
    (hn : n ∈ threeFourPathMiddlePrivate (blockSystem cfg) a b c)
    (hFm : (((blockSystem cfg).lineBlocksOfSize 3).filter
      fun x => m ∈ (blockSystem cfg).support x).card = 3)
    (hFn : (((blockSystem cfg).lineBlocksOfSize 3).filter
      fun x => n ∈ (blockSystem cfg).support x).card = 3)
    (i : Fin 3) :
    homogeneousLift (cfg n) ⬝ᵥ crossProduct
      (homogeneousLift (cfg (threeFourPathLeftPrivateLabel
        (blockSystem cfg) a b c ha hb hc hab hca hcb
        ((threeFourPathMiddleFibreMatching
          (blockSystem cfg) hcard a b c ha hb hc hab hca hcb hthree m hm hFm).symm i))))
      (homogeneousLift (cfg (threeFourPathRightPrivateLabel
        (blockSystem cfg) a b c ha hb hc hab hca hcb
        (threeFourPathTwoMiddleFibreRelativeMatching
          (blockSystem cfg) hcard a b c ha hb hc hab hca hcb hthree m n hm hn hFm hFn i)))) = 0 := by
  have h := three_four_path_actual_middle_fibre_matching_cross_incident
    cfg hcard a b c ha hb hc hab hca hcb hthree n hn hFn
    ((threeFourPathMiddleFibreMatching
      (blockSystem cfg) hcard a b c ha hb hc hab hca hcb hthree m hm hFm).symm i)
  simpa [threeFourPathLeftPrivateLabel, threeFourPathRightPrivateLabel,
    threeFourPathTwoMiddleFibreRelativeMatching] using h

/-! ### Elementary affine-chart algebra -/

/-- The composed projective-frame and affine-post-chart covector map is
injective on nonzero homogeneous representatives. -/
theorem three_four_path_dualAffineCovector_ne_zero
    {ell : Fin 4 → Homogeneous3} (F : ProjectiveCovectorFrame ell)
    (u : Homogeneous3) (hu : u ≠ 0) :
    threeFourPathDualAffineCovector F u ≠ 0 := by
  intro hzero
  have hself : u ⬝ᵥ u = 0 := by
    calc
      u ⬝ᵥ u = threeFourPathDualAffineCovector F u ⬝ᵥ
          threeFourPathDualAffineHomogeneous F u :=
        (three_four_path_dualAffineCovector_dot F u u).symm
      _ = 0 := by simp [hzero]
  exact hu (dotProduct_self_eq_zero.mp hself)

/-- Raw cross-product incidence transports verbatim through the actual
dual affine chart. -/
theorem three_four_path_dualAffine_cross_incident
    {ell : Fin 4 → Homogeneous3} (F : ProjectiveCovectorFrame ell)
    (u v w : Homogeneous3) (hinc : u ⬝ᵥ crossProduct v w = 0) :
    threeFourPathDualAffineCovector F u ⬝ᵥ
      threeFourPathDualAffineHomogeneous F (crossProduct v w) = 0 := by
  rw [three_four_path_dualAffineCovector_dot, hinc]

/-- Remove a nonzero homogeneous representative scale from an incidence
equation. -/
theorem three_four_path_smul_covector_dot_eq_zero_iff
    {r : ℝ} (hr : r ≠ 0) (u v : Homogeneous3) :
    (r • u) ⬝ᵥ v = 0 ↔ u ⬝ᵥ v = 0 := by
  rw [smul_dotProduct, smul_eq_mul]
  constructor
  · intro h
    exact (mul_eq_zero.mp h).resolve_left hr
  · intro h
    rw [h, mul_zero]

/-- The affine level encoded by a nonvertical normalized left-pencil
covector. -/
noncomputable def threeFourPathDualAffineColumnCoordinate (u : Homogeneous3) : ℝ :=
  -(u 2 / u 0)

/-- The affine level encoded by a nonhorizontal normalized right-pencil
covector. -/
noncomputable def threeFourPathDualAffineRowCoordinate (u : Homogeneous3) : ℝ :=
  -(u 2 / u 1)

/-- A covector whose middle coefficient vanishes is an affine vertical
level line after division by its nonzero first coefficient. -/
theorem three_four_path_dualAffine_column_normal_form
    (u : Homogeneous3) (huone : u 1 = 0) (huzero : u 0 ≠ 0) :
    u = u 0 • (![1, 0,
      -threeFourPathDualAffineColumnCoordinate u] : Homogeneous3) := by
  ext i
  fin_cases i
  · simp
  · simp [huone]
  · simp [threeFourPathDualAffineColumnCoordinate]
    field_simp [huzero]

/-- Symmetric affine normal form for a horizontal level line. -/
theorem three_four_path_dualAffine_row_normal_form
    (u : Homogeneous3) (huzero : u 0 = 0) (huone : u 1 ≠ 0) :
    u = u 1 • (![0, 1,
      -threeFourPathDualAffineRowCoordinate u] : Homogeneous3) := by
  ext i
  fin_cases i
  · simp [huzero]
  · simp
  · simp [threeFourPathDualAffineRowCoordinate]
    field_simp [huone]

/-- The transformed homogeneous representative of a crossing of two raw
dual covectors. -/
noncomputable def threeFourPathDualAffineGridPoint
    {ell : Fin 4 → Homogeneous3} (F : ProjectiveCovectorFrame ell)
    (u v : Homogeneous3) : Homogeneous3 :=
  threeFourPathDualAffineHomogeneous F (crossProduct u v)

/-- Dehomogenize an actual dual crossing in the derived affine chart. -/
noncomputable def threeFourPathDualAffineGridCoordinate
    {ell : Fin 4 → Homogeneous3} (F : ProjectiveCovectorFrame ell)
    (u v : Homogeneous3) : ℝ × ℝ :=
  (threeFourPathDualAffineGridPoint F u v 0 /
      threeFourPathDualAffineGridPoint F u v 2,
    threeFourPathDualAffineGridPoint F u v 1 /
      threeFourPathDualAffineGridPoint F u v 2)

theorem three_four_path_dualAffineGridPoint_incident_left
    {ell : Fin 4 → Homogeneous3} (F : ProjectiveCovectorFrame ell)
    (u v : Homogeneous3) :
    threeFourPathDualAffineCovector F u ⬝ᵥ
      threeFourPathDualAffineGridPoint F u v = 0 := by
  unfold threeFourPathDualAffineGridPoint
  exact three_four_path_dualAffine_cross_incident F u u v
    (dot_self_cross u v)

theorem three_four_path_dualAffineGridPoint_incident_right
    {ell : Fin 4 → Homogeneous3} (F : ProjectiveCovectorFrame ell)
    (u v : Homogeneous3) :
    threeFourPathDualAffineCovector F v ⬝ᵥ
      threeFourPathDualAffineGridPoint F u v = 0 := by
  unfold threeFourPathDualAffineGridPoint
  exact three_four_path_dualAffine_cross_incident F v u v
    (dot_cross_self u v)

theorem three_four_path_dualAffineGridPoint_ne_zero
    {ell : Fin 4 → Homogeneous3} (F : ProjectiveCovectorFrame ell)
    (u v : Homogeneous3) (hcross : crossProduct u v ≠ 0) :
    threeFourPathDualAffineGridPoint F u v ≠ 0 := by
  unfold threeFourPathDualAffineGridPoint
  exact three_four_path_dualAffineHomogeneous_ne_zero F _ hcross

/-- Once the two transformed pencil covectors have their vertical and
horizontal normal forms, their crossing is finite and has exactly the two
displayed affine levels. -/
theorem three_four_path_dualAffineGridCoordinate_of_normal_forms
    {ell : Fin 4 → Homogeneous3} (F : ProjectiveCovectorFrame ell)
    (u v : Homogeneous3) (x y : ℝ)
    (hux : threeFourPathDualAffineCovector F u =
      (threeFourPathDualAffineCovector F u 0) • (![1, 0, -x] : Homogeneous3))
    (hvy : threeFourPathDualAffineCovector F v =
      (threeFourPathDualAffineCovector F v 1) • (![0, 1, -y] : Homogeneous3))
    (hu0 : threeFourPathDualAffineCovector F u 0 ≠ 0)
    (hv1 : threeFourPathDualAffineCovector F v 1 ≠ 0)
    (hcross : crossProduct u v ≠ 0) :
    threeFourPathDualAffineGridCoordinate F u v = (x, y) := by
  let w := threeFourPathDualAffineGridPoint F u v
  have hleft : threeFourPathDualAffineCovector F u ⬝ᵥ w = 0 := by
    simpa [w] using three_four_path_dualAffineGridPoint_incident_left F u v
  have hright : threeFourPathDualAffineCovector F v ⬝ᵥ w = 0 := by
    simpa [w] using three_four_path_dualAffineGridPoint_incident_right F u v
  have hleft' : (![1, 0, -x] : Homogeneous3) ⬝ᵥ w = 0 := by
    rw [hux] at hleft
    exact (three_four_path_smul_covector_dot_eq_zero_iff hu0 _ _).mp hleft
  have hright' : (![0, 1, -y] : Homogeneous3) ⬝ᵥ w = 0 := by
    rw [hvy] at hright
    exact (three_four_path_smul_covector_dot_eq_zero_iff hv1 _ _).mp hright
  have hwne : w ≠ 0 := by
    simpa [w] using three_four_path_dualAffineGridPoint_ne_zero F u v hcross
  have hw2 : w 2 ≠ 0 := by
    intro hw2
    have hw0 : w 0 = 0 := by
      simpa [dotProduct, Fin.sum_univ_three, hw2] using hleft'
    have hw1 : w 1 = 0 := by
      simpa [dotProduct, Fin.sum_univ_three, hw2] using hright'
    apply hwne
    ext k
    fin_cases k <;> simp [hw0, hw1, hw2]
  apply Prod.ext
  · change w 0 / w 2 = x
    apply (div_eq_iff hw2).2
    have : w 0 - x * w 2 = 0 := by
      simpa [dotProduct, Fin.sum_univ_three] using hleft'
    linarith
  · change w 1 / w 2 = y
    apply (div_eq_iff hw2).2
    have : w 1 - y * w 2 = 0 := by
      simpa [dotProduct, Fin.sum_univ_three] using hright'
    linarith

/-! ### A two-pencil chart lemma -/

/-- Any covector through the first framed pencil centre becomes vertical in
the derived affine chart.  The proof uses only the two normalized frame
lines and the nonzero homogeneous representative of their crossing. -/
theorem three_four_path_dualAffine_left_pencil_apply_one
    {ell : Fin 4 → Homogeneous3} (F : ProjectiveCovectorFrame ell)
    (u : Homogeneous3)
    (hinc : u ⬝ᵥ crossProduct (ell 0) (ell 1) = 0)
    (hcross : crossProduct (ell 0) (ell 1) ≠ 0) :
    threeFourPathDualAffineCovector F u 1 = 0 := by
  let w := threeFourPathDualAffineGridPoint F (ell 0) (ell 1)
  have hwne : w ≠ 0 := by
    simpa [w] using three_four_path_dualAffineGridPoint_ne_zero
      F (ell 0) (ell 1) hcross
  have hzero : threeFourPathDualAffineCovector F (ell 0) ⬝ᵥ w = 0 := by
    simpa [w] using three_four_path_dualAffineGridPoint_incident_left
      F (ell 0) (ell 1)
  have hone : threeFourPathDualAffineCovector F (ell 1) ⬝ᵥ w = 0 := by
    simpa [w] using three_four_path_dualAffineGridPoint_incident_right
      F (ell 0) (ell 1)
  rw [three_four_path_dualAffineCovector_frame F 0] at hzero
  rw [three_four_path_dualAffineCovector_frame F 1] at hone
  have hszero : F.scale 0 * twelveGridAffineFrameScale 0 ≠ 0 :=
    mul_ne_zero (F.scale_ne_zero 0) (twelveGridAffineFrameScale_ne_zero 0)
  have hsone : F.scale 1 * twelveGridAffineFrameScale 1 ≠ 0 :=
    mul_ne_zero (F.scale_ne_zero 1) (twelveGridAffineFrameScale_ne_zero 1)
  have hzero' : twelveGridAffineFrameCovector 0 ⬝ᵥ w = 0 :=
    (three_four_path_smul_covector_dot_eq_zero_iff hszero _ _).mp hzero
  have hone' : twelveGridAffineFrameCovector 1 ⬝ᵥ w = 0 :=
    (three_four_path_smul_covector_dot_eq_zero_iff hsone _ _).mp hone
  have hw0 : w 0 = 0 := by
    simpa [twelveGridAffineFrameCovector, dotProduct, Fin.sum_univ_three] using hone'
  have hw2 : w 2 = 0 := by
    have : w 0 + w 2 = 0 := by
      simpa [twelveGridAffineFrameCovector, dotProduct, Fin.sum_univ_three] using hzero'
    linarith
  have hw1 : w 1 ≠ 0 := by
    intro hw1
    apply hwne
    ext k
    fin_cases k <;> simp [hw0, hw1, hw2]
  have htransport : threeFourPathDualAffineCovector F u ⬝ᵥ w = 0 := by
    simpa [w] using three_four_path_dualAffine_cross_incident
      F u (ell 0) (ell 1) hinc
  have hprod : threeFourPathDualAffineCovector F u 1 * w 1 = 0 := by
    simpa [dotProduct, Fin.sum_univ_three, hw0, hw2] using htransport
  exact (mul_eq_zero.mp hprod).resolve_right hw1

/-- A covector through the second framed pencil centre becomes horizontal in
the derived affine chart. -/
theorem three_four_path_dualAffine_right_pencil_apply_zero
    {ell : Fin 4 → Homogeneous3} (F : ProjectiveCovectorFrame ell)
    (u : Homogeneous3)
    (hinc : u ⬝ᵥ crossProduct (ell 2) (ell 3) = 0)
    (hcross : crossProduct (ell 2) (ell 3) ≠ 0) :
    threeFourPathDualAffineCovector F u 0 = 0 := by
  let w := threeFourPathDualAffineGridPoint F (ell 2) (ell 3)
  have hwne : w ≠ 0 := by
    simpa [w] using three_four_path_dualAffineGridPoint_ne_zero
      F (ell 2) (ell 3) hcross
  have htwo : threeFourPathDualAffineCovector F (ell 2) ⬝ᵥ w = 0 := by
    simpa [w] using three_four_path_dualAffineGridPoint_incident_left
      F (ell 2) (ell 3)
  have hthree : threeFourPathDualAffineCovector F (ell 3) ⬝ᵥ w = 0 := by
    simpa [w] using three_four_path_dualAffineGridPoint_incident_right
      F (ell 2) (ell 3)
  rw [three_four_path_dualAffineCovector_frame F 2] at htwo
  rw [three_four_path_dualAffineCovector_frame F 3] at hthree
  have hstwo : F.scale 2 * twelveGridAffineFrameScale 2 ≠ 0 :=
    mul_ne_zero (F.scale_ne_zero 2) (twelveGridAffineFrameScale_ne_zero 2)
  have hsthree : F.scale 3 * twelveGridAffineFrameScale 3 ≠ 0 :=
    mul_ne_zero (F.scale_ne_zero 3) (twelveGridAffineFrameScale_ne_zero 3)
  have htwo' : twelveGridAffineFrameCovector 2 ⬝ᵥ w = 0 :=
    (three_four_path_smul_covector_dot_eq_zero_iff hstwo _ _).mp htwo
  have hthree' : twelveGridAffineFrameCovector 3 ⬝ᵥ w = 0 :=
    (three_four_path_smul_covector_dot_eq_zero_iff hsthree _ _).mp hthree
  have hw1 : w 1 = 0 := by
    simpa [twelveGridAffineFrameCovector, dotProduct, Fin.sum_univ_three] using hthree'
  have hw2 : w 2 = 0 := by
    have : w 1 + w 2 = 0 := by
      simpa [twelveGridAffineFrameCovector, dotProduct, Fin.sum_univ_three] using htwo'
    linarith
  have hw0 : w 0 ≠ 0 := by
    intro hw0
    apply hwne
    ext k
    fin_cases k <;> simp [hw0, hw1, hw2]
  have htransport : threeFourPathDualAffineCovector F u ⬝ᵥ w = 0 := by
    simpa [w] using three_four_path_dualAffine_cross_incident
      F u (ell 2) (ell 3) hinc
  have hprod : threeFourPathDualAffineCovector F u 0 * w 0 = 0 := by
    simpa [dotProduct, Fin.sum_univ_three, hw1, hw2] using htransport
  exact (mul_eq_zero.mp hprod).resolve_right hw0

/-- A first-pencil covector not through the opposite centre has a nonzero
vertical-level coefficient. -/
theorem three_four_path_dualAffine_left_pencil_apply_zero_ne
    {ell : Fin 4 → Homogeneous3} (F : ProjectiveCovectorFrame ell)
    (u : Homogeneous3)
    (hnot : u ⬝ᵥ crossProduct (ell 2) (ell 3) ≠ 0)
    (hcross : crossProduct (ell 2) (ell 3) ≠ 0) :
    threeFourPathDualAffineCovector F u 0 ≠ 0 := by
  let w := threeFourPathDualAffineGridPoint F (ell 2) (ell 3)
  have hwne : w ≠ 0 := by
    simpa [w] using three_four_path_dualAffineGridPoint_ne_zero
      F (ell 2) (ell 3) hcross
  have htwo : threeFourPathDualAffineCovector F (ell 2) ⬝ᵥ w = 0 := by
    simpa [w] using three_four_path_dualAffineGridPoint_incident_left
      F (ell 2) (ell 3)
  have hthree : threeFourPathDualAffineCovector F (ell 3) ⬝ᵥ w = 0 := by
    simpa [w] using three_four_path_dualAffineGridPoint_incident_right
      F (ell 2) (ell 3)
  rw [three_four_path_dualAffineCovector_frame F 2] at htwo
  rw [three_four_path_dualAffineCovector_frame F 3] at hthree
  have hstwo : F.scale 2 * twelveGridAffineFrameScale 2 ≠ 0 :=
    mul_ne_zero (F.scale_ne_zero 2) (twelveGridAffineFrameScale_ne_zero 2)
  have hsthree : F.scale 3 * twelveGridAffineFrameScale 3 ≠ 0 :=
    mul_ne_zero (F.scale_ne_zero 3) (twelveGridAffineFrameScale_ne_zero 3)
  have htwo' : twelveGridAffineFrameCovector 2 ⬝ᵥ w = 0 :=
    (three_four_path_smul_covector_dot_eq_zero_iff hstwo _ _).mp htwo
  have hthree' : twelveGridAffineFrameCovector 3 ⬝ᵥ w = 0 :=
    (three_four_path_smul_covector_dot_eq_zero_iff hsthree _ _).mp hthree
  have hw1 : w 1 = 0 := by
    simpa [twelveGridAffineFrameCovector, dotProduct, Fin.sum_univ_three] using hthree'
  have hw2 : w 2 = 0 := by
    have : w 1 + w 2 = 0 := by
      simpa [twelveGridAffineFrameCovector, dotProduct, Fin.sum_univ_three] using htwo'
    linarith
  have hw0 : w 0 ≠ 0 := by
    intro hw0
    apply hwne
    ext k
    fin_cases k <;> simp [hw0, hw1, hw2]
  intro hu0
  apply hnot
  have htransport : threeFourPathDualAffineCovector F u ⬝ᵥ w =
      u ⬝ᵥ crossProduct (ell 2) (ell 3) := by
    simpa [w] using three_four_path_dualAffineCovector_dot
      F u (crossProduct (ell 2) (ell 3))
  rw [← htransport]
  simp [dotProduct, Fin.sum_univ_three, hu0, hw1, hw2]

/-- Symmetric nonvanishing of the horizontal-level coefficient. -/
theorem three_four_path_dualAffine_right_pencil_apply_one_ne
    {ell : Fin 4 → Homogeneous3} (F : ProjectiveCovectorFrame ell)
    (u : Homogeneous3)
    (hnot : u ⬝ᵥ crossProduct (ell 0) (ell 1) ≠ 0)
    (hcross : crossProduct (ell 0) (ell 1) ≠ 0) :
    threeFourPathDualAffineCovector F u 1 ≠ 0 := by
  let w := threeFourPathDualAffineGridPoint F (ell 0) (ell 1)
  have hwne : w ≠ 0 := by
    simpa [w] using three_four_path_dualAffineGridPoint_ne_zero
      F (ell 0) (ell 1) hcross
  have hzero : threeFourPathDualAffineCovector F (ell 0) ⬝ᵥ w = 0 := by
    simpa [w] using three_four_path_dualAffineGridPoint_incident_left
      F (ell 0) (ell 1)
  have hone : threeFourPathDualAffineCovector F (ell 1) ⬝ᵥ w = 0 := by
    simpa [w] using three_four_path_dualAffineGridPoint_incident_right
      F (ell 0) (ell 1)
  rw [three_four_path_dualAffineCovector_frame F 0] at hzero
  rw [three_four_path_dualAffineCovector_frame F 1] at hone
  have hszero : F.scale 0 * twelveGridAffineFrameScale 0 ≠ 0 :=
    mul_ne_zero (F.scale_ne_zero 0) (twelveGridAffineFrameScale_ne_zero 0)
  have hsone : F.scale 1 * twelveGridAffineFrameScale 1 ≠ 0 :=
    mul_ne_zero (F.scale_ne_zero 1) (twelveGridAffineFrameScale_ne_zero 1)
  have hzero' : twelveGridAffineFrameCovector 0 ⬝ᵥ w = 0 :=
    (three_four_path_smul_covector_dot_eq_zero_iff hszero _ _).mp hzero
  have hone' : twelveGridAffineFrameCovector 1 ⬝ᵥ w = 0 :=
    (three_four_path_smul_covector_dot_eq_zero_iff hsone _ _).mp hone
  have hw0 : w 0 = 0 := by
    simpa [twelveGridAffineFrameCovector, dotProduct, Fin.sum_univ_three] using hone'
  have hw2 : w 2 = 0 := by
    have : w 0 + w 2 = 0 := by
      simpa [twelveGridAffineFrameCovector, dotProduct, Fin.sum_univ_three] using hzero'
    linarith
  have hw1 : w 1 ≠ 0 := by
    intro hw1
    apply hwne
    ext k
    fin_cases k <;> simp [hw0, hw1, hw2]
  intro hu1
  apply hnot
  have htransport : threeFourPathDualAffineCovector F u ⬝ᵥ w =
      u ⬝ᵥ crossProduct (ell 0) (ell 1) := by
    simpa [w] using three_four_path_dualAffineCovector_dot
      F u (crossProduct (ell 0) (ell 1))
  rw [← htransport]
  simp [dotProduct, Fin.sum_univ_three, hu1, hw0, hw2]

/-! ### Finite crossings and affine collinearity -/

/-- A normalized vertical/horizontal pair has a finite crossing. -/
theorem three_four_path_dualAffineGridPoint_apply_two_ne_of_normal_forms
    {ell : Fin 4 → Homogeneous3} (F : ProjectiveCovectorFrame ell)
    (u v : Homogeneous3) (x y : ℝ)
    (hux : threeFourPathDualAffineCovector F u =
      (threeFourPathDualAffineCovector F u 0) • (![1, 0, -x] : Homogeneous3))
    (hvy : threeFourPathDualAffineCovector F v =
      (threeFourPathDualAffineCovector F v 1) • (![0, 1, -y] : Homogeneous3))
    (hu0 : threeFourPathDualAffineCovector F u 0 ≠ 0)
    (hv1 : threeFourPathDualAffineCovector F v 1 ≠ 0)
    (hcross : crossProduct u v ≠ 0) :
    threeFourPathDualAffineGridPoint F u v 2 ≠ 0 := by
  let w := threeFourPathDualAffineGridPoint F u v
  have hleft : threeFourPathDualAffineCovector F u ⬝ᵥ w = 0 := by
    simpa [w] using three_four_path_dualAffineGridPoint_incident_left F u v
  have hright : threeFourPathDualAffineCovector F v ⬝ᵥ w = 0 := by
    simpa [w] using three_four_path_dualAffineGridPoint_incident_right F u v
  have hleft' : (![1, 0, -x] : Homogeneous3) ⬝ᵥ w = 0 := by
    rw [hux] at hleft
    exact (three_four_path_smul_covector_dot_eq_zero_iff hu0 _ _).mp hleft
  have hright' : (![0, 1, -y] : Homogeneous3) ⬝ᵥ w = 0 := by
    rw [hvy] at hright
    exact (three_four_path_smul_covector_dot_eq_zero_iff hv1 _ _).mp hright
  intro hw2
  change w 2 = 0 at hw2
  have hw0 : w 0 = 0 := by
    have h : w 0 - x * w 2 = 0 := by
      simpa [dotProduct, Fin.sum_univ_three] using hleft'
    rw [hw2, mul_zero, sub_zero] at h
    exact h
  have hw1 : w 1 = 0 := by
    have h : w 1 - y * w 2 = 0 := by
      simpa [dotProduct, Fin.sum_univ_three] using hright'
    rw [hw2, mul_zero, sub_zero] at h
    exact h
  have hwne : w ≠ 0 := by
    simpa [w] using three_four_path_dualAffineGridPoint_ne_zero F u v hcross
  apply hwne
  funext k
  fin_cases k
  · exact hw0
  · exact hw1
  · exact hw2

/-- A finite homogeneous crossing is its last coordinate times the canonical
lift of its dehomogenized affine coordinate. -/
theorem three_four_path_dualAffineGridPoint_eq_scale_homogeneousLift
    {ell : Fin 4 → Homogeneous3} (F : ProjectiveCovectorFrame ell)
    (u v : Homogeneous3)
    (hfinite : threeFourPathDualAffineGridPoint F u v 2 ≠ 0) :
    threeFourPathDualAffineGridPoint F u v =
      threeFourPathDualAffineGridPoint F u v 2 •
        homogeneousLift (twelveGridAffinePairPoint2
          (threeFourPathDualAffineGridCoordinate F u v)) := by
  let w := threeFourPathDualAffineGridPoint F u v
  ext i
  fin_cases i
  · simp [w, threeFourPathDualAffineGridCoordinate, homogeneousLift,
      twelveGridAffinePairPoint2]
    rw [mul_comm, div_mul_cancel₀ _ hfinite]
  · simp [w, threeFourPathDualAffineGridCoordinate, homogeneousLift,
      twelveGridAffinePairPoint2]
    rw [mul_comm, div_mul_cancel₀ _ hfinite]
  · simp [w, homogeneousLift, twelveGridAffinePairPoint2]

/-- Three finite affine points annihilating one nonzero covector are
collinear, expressed by the elementary oriented-area equation. -/
theorem three_four_path_affineArea_eq_zero_of_common_covector
    (ell : Homogeneous3) (hell : ell ≠ 0)
    (u v w : ℝ × ℝ)
    (hu : ell ⬝ᵥ homogeneousLift (twelveGridAffinePairPoint2 u) = 0)
    (hv : ell ⬝ᵥ homogeneousLift (twelveGridAffinePairPoint2 v) = 0)
    (hw : ell ⬝ᵥ homogeneousLift (twelveGridAffinePairPoint2 w) = 0) :
    parameterizedThreeByThreeAffineArea u v w = 0 := by
  have hu' : ell 0 * u.1 + ell 1 * u.2 + ell 2 = 0 := by
    simpa [homogeneousLift, twelveGridAffinePairPoint2, dotProduct,
      Fin.sum_univ_three] using hu
  have hv' : ell 0 * v.1 + ell 1 * v.2 + ell 2 = 0 := by
    simpa [homogeneousLift, twelveGridAffinePairPoint2, dotProduct,
      Fin.sum_univ_three] using hv
  have hw' : ell 0 * w.1 + ell 1 * w.2 + ell 2 = 0 := by
    simpa [homogeneousLift, twelveGridAffinePairPoint2, dotProduct,
      Fin.sum_univ_three] using hw
  by_cases hzero : ell 0 = 0
  · by_cases hone : ell 1 = 0
    · have htwo : ell 2 = 0 := by simpa [hzero, hone] using hu'
      exfalso
      apply hell
      ext i
      fin_cases i <;> simp [hzero, hone, htwo]
    · have hu0 : ell 1 * u.2 + ell 2 = 0 := by
        simpa [hzero] using hu'
      have hv0 : ell 1 * v.2 + ell 2 = 0 := by
        simpa [hzero] using hv'
      have hw0 : ell 1 * w.2 + ell 2 = 0 := by
        simpa [hzero] using hw'
      have huv : ell 1 * (v.2 - u.2) = 0 := by
        linear_combination hv0 - hu0
      have huw : ell 1 * (w.2 - u.2) = 0 := by
        linear_combination hw0 - hu0
      have hvy : v.2 = u.2 := by
        have h : v.2 - u.2 = 0 := (mul_eq_zero.mp huv).resolve_left hone
        linarith
      have hwy : w.2 = u.2 := by
        have h : w.2 - u.2 = 0 := (mul_eq_zero.mp huw).resolve_left hone
        linarith
      rw [parameterizedThreeByThreeAffineArea, hvy, hwy]
      ring
  · have huv : ell 0 * (v.1 - u.1) + ell 1 * (v.2 - u.2) = 0 := by
      linear_combination hv' - hu'
    have huw : ell 0 * (w.1 - u.1) + ell 1 * (w.2 - u.2) = 0 := by
      linear_combination hw' - hu'
    have harea : ell 0 * parameterizedThreeByThreeAffineArea u v w = 0 := by
      calc
        ell 0 * parameterizedThreeByThreeAffineArea u v w =
            (ell 0 * (v.1 - u.1) + ell 1 * (v.2 - u.2)) * (w.2 - u.2) -
              (ell 0 * (w.1 - u.1) + ell 1 * (w.2 - u.2)) * (v.2 - u.2) := by
          simp [parameterizedThreeByThreeAffineArea]
          ring
        _ = 0 := by rw [huv, huw]; ring
    exact (mul_eq_zero.mp harea).resolve_left hzero

/-- A raw dual covector incident with three finite transformed crossings
gives the corresponding affine area equation. -/
theorem three_four_path_dualAffineGridArea_eq_zero_of_common_covector
    {ell : Fin 4 → Homogeneous3} (F : ProjectiveCovectorFrame ell)
    (z u₀ v₀ u₁ v₁ u₂ v₂ : Homogeneous3)
    (hz : z ≠ 0)
    (hinc₀ : z ⬝ᵥ crossProduct u₀ v₀ = 0)
    (hinc₁ : z ⬝ᵥ crossProduct u₁ v₁ = 0)
    (hinc₂ : z ⬝ᵥ crossProduct u₂ v₂ = 0)
    (hfinite₀ : threeFourPathDualAffineGridPoint F u₀ v₀ 2 ≠ 0)
    (hfinite₁ : threeFourPathDualAffineGridPoint F u₁ v₁ 2 ≠ 0)
    (hfinite₂ : threeFourPathDualAffineGridPoint F u₂ v₂ 2 ≠ 0) :
    parameterizedThreeByThreeAffineArea
      (threeFourPathDualAffineGridCoordinate F u₀ v₀)
      (threeFourPathDualAffineGridCoordinate F u₁ v₁)
      (threeFourPathDualAffineGridCoordinate F u₂ v₂) = 0 := by
  let z' := threeFourPathDualAffineCovector F z
  have hz' : z' ≠ 0 := by
    simpa [z'] using three_four_path_dualAffineCovector_ne_zero F z hz
  have hcoordinate_incident : ∀ (u v : Homogeneous3)
      (hinc : z ⬝ᵥ crossProduct u v = 0)
      (hfinite : threeFourPathDualAffineGridPoint F u v 2 ≠ 0),
      z' ⬝ᵥ homogeneousLift (twelveGridAffinePairPoint2
        (threeFourPathDualAffineGridCoordinate F u v)) = 0 := by
    intro u v hinc hfinite
    have hraw : z' ⬝ᵥ threeFourPathDualAffineGridPoint F u v = 0 := by
      dsimp [z']
      exact three_four_path_dualAffine_cross_incident F z u v hinc
    rw [three_four_path_dualAffineGridPoint_eq_scale_homogeneousLift
      F u v hfinite] at hraw
    rw [dotProduct_smul, smul_eq_mul] at hraw
    exact (mul_eq_zero.mp hraw).resolve_left hfinite
  exact three_four_path_affineArea_eq_zero_of_common_covector z' hz' _ _ _
    (hcoordinate_incident u₀ v₀ hinc₀ hfinite₀)
    (hcoordinate_incident u₁ v₁ hinc₁ hfinite₁)
    (hcoordinate_incident u₂ v₂ hinc₂ hfinite₂)

/-! ### Actual two-pencil normal forms -/

/-- Two different actual labels have distinct nonzero dual covectors. -/
theorem three_four_path_actual_dual_cross_ne_zero
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    (cfg : Configuration Point) {q r : Point} (hqr : q ≠ r) :
    crossProduct (homogeneousLift (cfg q)) (homogeneousLift (cfg r)) ≠ 0 := by
  simpa [lineCovector] using lineCovector_ne_zero (cfg.injective.ne hqr)

/-- Every actual left-pencil covector is incident with the dual centre of
the first two displayed left labels. -/
theorem three_four_path_actual_left_pencil_cross_incident
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    (cfg : Configuration Point) (a : LineBlock (blockSystem cfg))
    (left : Fin 3 → Point)
    (hleft : ∀ i, left i ∈ (blockSystem cfg).support a.1)
    (hleftInj : Function.Injective left) (i : Fin 3) :
    homogeneousLift (cfg (left i)) ⬝ᵥ
      crossProduct (homogeneousLift (cfg (left 0)))
        (homogeneousLift (cfg (left 1))) = 0 := by
  have h01 : left 0 ≠ left 1 := by
    intro h
    have : (0 : Fin 3) = 1 := hleftInj h
    omega
  exact three_four_path_actual_dual_cross_incident_of_three_mem
    cfg a h01 (hleft i) (hleft 0) (hleft 1)

/-- The symmetric actual right-pencil concurrency equation. -/
theorem three_four_path_actual_right_pencil_cross_incident
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    (cfg : Configuration Point) (b : LineBlock (blockSystem cfg))
    (right : Fin 3 → Point)
    (hright : ∀ i, right i ∈ (blockSystem cfg).support b.1)
    (hrightInj : Function.Injective right) (i : Fin 3) :
    homogeneousLift (cfg (right i)) ⬝ᵥ
      crossProduct (homogeneousLift (cfg (right 0)))
        (homogeneousLift (cfg (right 1))) = 0 := by
  have h01 : right 0 ≠ right 1 := by
    intro h
    have : (0 : Fin 3) = 1 := hrightInj h
    omega
  exact three_four_path_actual_dual_cross_incident_of_three_mem
    cfg b h01 (hright i) (hright 0) (hright 1)

/-- A left private label does not pass through the dual centre of the
right base pencil. -/
theorem three_four_path_actual_left_not_right_pencil_cross
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    (cfg : Configuration Point) (a b : LineBlock (blockSystem cfg))
    (hab : Disjoint ((blockSystem cfg).support a.1)
      ((blockSystem cfg).support b.1))
    (left right : Fin 3 → Point)
    (hleft : ∀ i, left i ∈ (blockSystem cfg).support a.1)
    (hright : ∀ i, right i ∈ (blockSystem cfg).support b.1)
    (hrightInj : Function.Injective right) (i : Fin 3) :
    homogeneousLift (cfg (left i)) ⬝ᵥ
      crossProduct (homogeneousLift (cfg (right 0)))
        (homogeneousLift (cfg (right 1))) ≠ 0 := by
  have h01 : right 0 ≠ right 1 := by
    intro h
    have : (0 : Fin 3) = 1 := hrightInj h
    omega
  have hdet := three_four_path_actual_det_ne_zero_of_two_left_one_right
    cfg b a hab.symm (hright 0) (hright 1) (hleft i) h01
  intro hzero
  apply hdet
  calc
    Matrix.det ![homogeneousLift (cfg (right 0)),
        homogeneousLift (cfg (right 1)), homogeneousLift (cfg (left i))] =
        homogeneousLift (cfg (right 0)) ⬝ᵥ
          crossProduct (homogeneousLift (cfg (right 1)))
            (homogeneousLift (cfg (left i))) :=
      (triple_product_eq_det _ _ _).symm
    _ = homogeneousLift (cfg (left i)) ⬝ᵥ
          crossProduct (homogeneousLift (cfg (right 0)))
            (homogeneousLift (cfg (right 1))) :=
      (triple_product_permutation _ _ _).symm
    _ = 0 := hzero

/-- Symmetrically, a right private label avoids the left pencil centre. -/
theorem three_four_path_actual_right_not_left_pencil_cross
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    (cfg : Configuration Point) (a b : LineBlock (blockSystem cfg))
    (hab : Disjoint ((blockSystem cfg).support a.1)
      ((blockSystem cfg).support b.1))
    (left right : Fin 3 → Point)
    (hleft : ∀ i, left i ∈ (blockSystem cfg).support a.1)
    (hright : ∀ i, right i ∈ (blockSystem cfg).support b.1)
    (hleftInj : Function.Injective left) (i : Fin 3) :
    homogeneousLift (cfg (right i)) ⬝ᵥ
      crossProduct (homogeneousLift (cfg (left 0)))
        (homogeneousLift (cfg (left 1))) ≠ 0 := by
  have h01 : left 0 ≠ left 1 := by
    intro h
    have : (0 : Fin 3) = 1 := hleftInj h
    omega
  have hdet := three_four_path_actual_det_ne_zero_of_two_left_one_right
    cfg a b hab (hleft 0) (hleft 1) (hright i) h01
  intro hzero
  apply hdet
  calc
    Matrix.det ![homogeneousLift (cfg (left 0)),
        homogeneousLift (cfg (left 1)), homogeneousLift (cfg (right i))] =
        homogeneousLift (cfg (left 0)) ⬝ᵥ
          crossProduct (homogeneousLift (cfg (left 1)))
            (homogeneousLift (cfg (right i))) :=
      (triple_product_eq_det _ _ _).symm
    _ = homogeneousLift (cfg (right i)) ⬝ᵥ
          crossProduct (homogeneousLift (cfg (left 0)))
            (homogeneousLift (cfg (left 1))) :=
      (triple_product_permutation _ _ _).symm
    _ = 0 := hzero

/-- Every actual left-pencil label has the canonical vertical level normal
form in the frame built from the first two labels of both pencils. -/
theorem three_four_path_actual_dualAffine_left_normal_form
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    (cfg : Configuration Point) (a b : LineBlock (blockSystem cfg))
    (hab : Disjoint ((blockSystem cfg).support a.1)
      ((blockSystem cfg).support b.1))
    (left right : Fin 3 → Point)
    (hleft : ∀ i, left i ∈ (blockSystem cfg).support a.1)
    (hright : ∀ i, right i ∈ (blockSystem cfg).support b.1)
    (hleftInj : Function.Injective left)
    (hrightInj : Function.Injective right)
    (F : ProjectiveCovectorFrame (threeFourPathActualDualFrameCovector cfg left right))
    (i : Fin 3) :
    threeFourPathDualAffineCovector F (homogeneousLift (cfg (left i))) =
      threeFourPathDualAffineCovector F (homogeneousLift (cfg (left i))) 0 •
        (![1, 0, -threeFourPathDualAffineColumnCoordinate
          (threeFourPathDualAffineCovector F (homogeneousLift (cfg (left i))))] :
          Homogeneous3) := by
  apply three_four_path_dualAffine_column_normal_form
  · exact three_four_path_dualAffine_left_pencil_apply_one F _
      (three_four_path_actual_left_pencil_cross_incident
        cfg a left hleft hleftInj i)
      (three_four_path_actual_dual_cross_ne_zero cfg
        (by intro h; exact Fin.zero_ne_one (hleftInj h)))
  · exact three_four_path_dualAffine_left_pencil_apply_zero_ne F _
      (three_four_path_actual_left_not_right_pencil_cross
        cfg a b hab left right hleft hright hrightInj i)
      (three_four_path_actual_dual_cross_ne_zero cfg
        (by intro h; exact Fin.zero_ne_one (hrightInj h)))

/-- Symmetric horizontal normal form for every actual right-pencil label. -/
theorem three_four_path_actual_dualAffine_right_normal_form
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    (cfg : Configuration Point) (a b : LineBlock (blockSystem cfg))
    (hab : Disjoint ((blockSystem cfg).support a.1)
      ((blockSystem cfg).support b.1))
    (left right : Fin 3 → Point)
    (hleft : ∀ i, left i ∈ (blockSystem cfg).support a.1)
    (hright : ∀ i, right i ∈ (blockSystem cfg).support b.1)
    (hleftInj : Function.Injective left)
    (hrightInj : Function.Injective right)
    (F : ProjectiveCovectorFrame (threeFourPathActualDualFrameCovector cfg left right))
    (i : Fin 3) :
    threeFourPathDualAffineCovector F (homogeneousLift (cfg (right i))) =
      threeFourPathDualAffineCovector F (homogeneousLift (cfg (right i))) 1 •
        (![0, 1, -threeFourPathDualAffineRowCoordinate
          (threeFourPathDualAffineCovector F (homogeneousLift (cfg (right i))))] :
          Homogeneous3) := by
  apply three_four_path_dualAffine_row_normal_form
  · exact three_four_path_dualAffine_right_pencil_apply_zero F _
      (three_four_path_actual_right_pencil_cross_incident
        cfg b right hright hrightInj i)
      (three_four_path_actual_dual_cross_ne_zero cfg
        (by intro h; exact Fin.zero_ne_one (hrightInj h)))
  · exact three_four_path_dualAffine_right_pencil_apply_one_ne F _
      (three_four_path_actual_right_not_left_pencil_cross
        cfg a b hab left right hleft hright hleftInj i)
      (three_four_path_actual_dual_cross_ne_zero cfg
        (by intro h; exact Fin.zero_ne_one (hleftInj h)))

end Erdos506.V1
