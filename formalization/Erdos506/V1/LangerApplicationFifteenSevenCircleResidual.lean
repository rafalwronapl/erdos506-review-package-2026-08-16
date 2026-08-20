import Erdos506.V1.LangerApplicationSixteenEightCircleSplit

/-!
# The lossless fifteen--seven rich-circle residual

The corrected circle pencil at `(15,7)` is six units short of the target.
This file keeps those six units as actual finite defects instead of replacing
the argument by the much weaker numerical conclusion `78 <= C`.
-/

namespace Erdos506.V1

open Erdos506.Block
open Erdos506.Block.BlockSystem
open Erdos506.Finite
open Erdos506.Incidence
open Erdos506.V4
open scoped BigOperators

universe u

variable {alpha : Type u} [Fintype alpha] [DecidableEq alpha]

noncomputable def fifteenSevenFanSum
    (cfg : Configuration alpha) (b : GeometricBlock cfg) : Nat :=
  ∑ x : BlockOutsider (blockSystem cfg) b,
    (circlePencil (blockSystem cfg) b x).card

noncomputable def fifteenSevenLinePairSum
    (cfg : Configuration alpha) (b : GeometricBlock cfg) : Nat :=
  ∑ x : BlockOutsider (blockSystem cfg) b,
    (lineBasePairs (blockSystem cfg) b x).card

noncomputable def fifteenSevenPairMoment
    (cfg : Configuration alpha) (b : GeometricBlock cfg) : Nat := by
  classical
  exact distinguishedPairMoment
    (Finset.univ : Finset (BlockOutsider (blockSystem cfg) b))
    (circlePencil (blockSystem cfg) b)

noncomputable def fifteenSevenOutsiderCircleBlocks
    (cfg : Configuration alpha) (b : GeometricBlock cfg) :
    Finset (GeometricBlock cfg) :=
  finsetRestrictionCircleBlocks cfg
    (blockOutsiders (blockSystem cfg) b)

noncomputable def fifteenSevenCoveredCircles
    (cfg : Configuration alpha) (b : GeometricBlock cfg) :
    Finset (GeometricBlock cfg) := by
  classical
  exact (Finset.univ.biUnion (circlePencil (blockSystem cfg) b)) ∪
    fifteenSevenOutsiderCircleBlocks cfg b

theorem card_inter_lineBasePairs_le_one
    {Point Block : Type*} [Fintype Point] [Fintype Block]
    [DecidableEq Point]
    (S : BlockSystem Point Block) (b : Block)
    (x y : BlockOutsider S b) (hxy : x ≠ y) :
    (lineBasePairs S b x ∩ lineBasePairs S b y).card ≤ 1 := by
  classical
  rw [Finset.card_le_one]
  intro p hp q hq
  have hp' := Finset.mem_inter.mp hp
  have hq' := Finset.mem_inter.mp hq
  have hpLine : S.kind (pencilOwner S b x p) = .line :=
    mem_lineBasePairs.mp hp'.1
  have hqLine : S.kind (pencilOwner S b x q) = .line :=
    mem_lineBasePairs.mp hq'.1
  have owner_eq_for_shared
      (r : BlockBasePair S b)
      (hrx : r ∈ lineBasePairs S b x)
      (hry : r ∈ lineBasePairs S b y) :
      pencilOwner S b x r = pencilOwner S b y r := by
    by_contra hne
    let Lx : LineBlock S :=
      ⟨pencilOwner S b x r, mem_lineBasePairs.mp hrx⟩
    let Ly : LineBlock S :=
      ⟨pencilOwner S b y r, mem_lineBasePairs.mp hry⟩
    have hlines : Lx ≠ Ly := by
      intro heq
      exact hne (congrArg Subtype.val heq)
    have hinter := S.distinct_line_inter_card_lt_two hlines
    have hsub : r.1 ⊆ S.support Lx.1 ∩ S.support Ly.1 := by
      intro z hz
      exact Finset.mem_inter.mpr
        ⟨pencilOwner_contains_pair S b x r hz,
          pencilOwner_contains_pair S b y r hz⟩
    have hle := Finset.card_le_card hsub
    have hrCard := (Finset.mem_powersetCard.mp r.2).2
    omega
  have hpOwner := owner_eq_for_shared p hp'.1 hp'.2
  have hqOwner := owner_eq_for_shared q hq'.1 hq'.2
  have howner : pencilOwner S b x p = pencilOwner S b x q := by
    by_contra hne
    let Lp : LineBlock S := ⟨pencilOwner S b x p, hpLine⟩
    let Lq : LineBlock S := ⟨pencilOwner S b x q, hqLine⟩
    have hlines : Lp ≠ Lq := by
      intro heq
      exact hne (congrArg Subtype.val heq)
    have hinter := S.distinct_line_inter_card_lt_two hlines
    have hxyVal : x.1 ≠ y.1 := Subtype.coe_injective.ne hxy
    have hsub : ({x.1, y.1} : Finset Point) ⊆
        S.support Lp.1 ∩ S.support Lq.1 := by
      intro z hz
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with rfl | rfl
      · exact Finset.mem_inter.mpr
          ⟨pencilOwner_contains_outsider S b x p,
            pencilOwner_contains_outsider S b x q⟩
      · exact Finset.mem_inter.mpr ⟨by
            change y.1 ∈ S.support (pencilOwner S b x p)
            rw [hpOwner]
            exact pencilOwner_contains_outsider S b y p, by
            change y.1 ∈ S.support (pencilOwner S b x q)
            rw [hqOwner]
            exact pencilOwner_contains_outsider S b y q⟩
    have hle := Finset.card_le_card hsub
    have hcard : ({x.1, y.1} : Finset Point).card = 2 := by
      simp [hxyVal]
    omega
  exact pencilOwner_injective S b x howner

theorem card_commonPencils_add_inter_lineBasePairs_le_three
    {Point Block : Type*} [Fintype Point] [Fintype Block]
    [DecidableEq Point]
    (S : BlockSystem Point Block) (b : Block)
    (hbase : (S.support b).card = 7)
    (x y : BlockOutsider S b) (hxy : x ≠ y) :
    (commonPencils S b x y).card +
      (lineBasePairs S b x ∩ lineBasePairs S b y).card ≤ 3 := by
  classical
  by_cases hempty : lineBasePairs S b x ∩ lineBasePairs S b y = ∅
  · rw [hempty]
    simp only [Finset.card_empty, Nat.add_zero]
    have h := card_commonPencils_le_half S b x y hxy
    rw [hbase] at h
    norm_num at h ⊢
    exact h
  · have hpNonempty : (lineBasePairs S b x ∩ lineBasePairs S b y).Nonempty :=
      Finset.nonempty_iff_ne_empty.mpr hempty
    obtain ⟨p, hp⟩ := hpNonempty
    have hp' := Finset.mem_inter.mp hp
    have hpLine : S.kind (pencilOwner S b x p) = .line :=
      mem_lineBasePairs.mp hp'.1
    have howners : pencilOwner S b x p = pencilOwner S b y p := by
      by_contra hne
      let Lx : LineBlock S := ⟨pencilOwner S b x p, hpLine⟩
      let Ly : LineBlock S :=
        ⟨pencilOwner S b y p, mem_lineBasePairs.mp hp'.2⟩
      have hlines : Lx ≠ Ly := by
        intro heq
        exact hne (congrArg Subtype.val heq)
      have hinter := S.distinct_line_inter_card_lt_two hlines
      have hsub : p.1 ⊆ S.support Lx.1 ∩ S.support Ly.1 := by
        intro z hz
        exact Finset.mem_inter.mpr
          ⟨pencilOwner_contains_pair S b x p hz,
            pencilOwner_contains_pair S b y p hz⟩
      have hle := Finset.card_le_card hsub
      have hpCard := (Finset.mem_powersetCard.mp p.2).2
      omega
    let L : LineBlock S := ⟨pencilOwner S b x p, hpLine⟩
    have hxL : x.1 ∈ S.support L.1 :=
      pencilOwner_contains_outsider S b x p
    have hyL : y.1 ∈ S.support L.1 := by
      change y.1 ∈ S.support (pencilOwner S b x p)
      rw [howners]
      exact pencilOwner_contains_outsider S b y p
    let P := commonPencilBasePairs S b x y
    have hPdisj : ((P : Finset (Finset Point)) :
        Set (Finset Point)).PairwiseDisjoint id := by
      exact commonPencilBasePairs_pairwiseDisjoint S b x y hxy
    have hAcard : ∀ A ∈ P, A.card = 2 := by
      intro A hA
      dsimp only [P] at hA
      rw [commonPencilBasePairs] at hA
      obtain ⟨c, _hc, rfl⟩ := Finset.mem_image.mp hA
      exact commonPencilBasePair_card S b x y c
    have hUnionCard : (P.biUnion id).card = 2 * P.card := by
      rw [Finset.card_biUnion hPdisj]
      calc
        (∑ A ∈ P, A.card) = ∑ _A ∈ P, 2 := by
          apply Finset.sum_congr rfl
          intro A hA
          rw [hAcard A hA]
        _ = 2 * P.card := by simp [Nat.mul_comm]
    have hpDisj : Disjoint p.1 (P.biUnion id) := by
      rw [Finset.disjoint_left]
      intro z hzp hzUnion
      obtain ⟨A, hAP, hzA⟩ := Finset.mem_biUnion.mp hzUnion
      dsimp only [P] at hAP
      rw [commonPencilBasePairs] at hAP
      obtain ⟨c, _hc, hAc⟩ := Finset.mem_image.mp hAP
      have hcross := line_trace_disjoint_commonPencilBasePair_generic
        S b L x y hxy hxL hyL c
      have hzLineBase : z ∈ S.support L.1 ∩ S.support b := by
        apply Finset.mem_inter.mpr
        refine ⟨?_, (Finset.mem_powersetCard.mp p.2).1 hzp⟩
        exact pencilOwner_contains_pair S b x p hzp
      have hzCommon : z ∈ commonPencilBasePair S b c := by
        rw [hAc]
        exact hzA
      exact (Finset.disjoint_left.mp hcross) hzLineBase hzCommon
    have hcover : p.1 ∪ P.biUnion id ⊆ S.support b := by
      intro z hz
      rcases Finset.mem_union.mp hz with hzp | hzP
      · exact (Finset.mem_powersetCard.mp p.2).1 hzp
      · obtain ⟨A, hAP, hzA⟩ := Finset.mem_biUnion.mp hzP
        dsimp only [P] at hAP
        rw [commonPencilBasePairs] at hAP
        obtain ⟨c, _hc, hAc⟩ := Finset.mem_image.mp hAP
        rw [← hAc] at hzA
        exact (Finset.mem_inter.mp hzA).2
    have hcardUnion : (p.1 ∪ P.biUnion id).card = 2 + 2 * P.card := by
      rw [Finset.card_union_of_disjoint hpDisj,
        (Finset.mem_powersetCard.mp p.2).2, hUnionCard]
    have hle := Finset.card_le_card hcover
    have hPcard : P.card = (commonPencils S b x y).card := by
      dsimp only [P]
      exact card_commonPencilBasePairs S b x y
    have hline := card_inter_lineBasePairs_le_one S b x y hxy
    rw [hcardUnion, hbase, hPcard] at hle
    omega

private theorem fifteenSeven_distinguishedPairTerm_eq_inter
    {Iota Beta : Type*} [DecidableEq Iota] [DecidableEq Beta]
    (I : Finset Iota) (F : Iota → Finset Beta)
    (A : Finset Iota) (hA : A ∈ I.powersetCard 2)
    {x y : Iota} (hxy : x ≠ y) (hAeq : A = {x, y}) :
    ((I.biUnion F).filter fun z => ∀ i ∈ A, z ∈ F i) = F x ∩ F y := by
  have hAspec := Finset.mem_powersetCard.mp hA
  have hxI : x ∈ I := hAspec.1 (by simp [hAeq])
  ext z
  constructor
  · intro hz
    have hall := (Finset.mem_filter.mp hz).2
    exact Finset.mem_inter.mpr
      ⟨hall x (by simp [hAeq]), hall y (by simp [hAeq])⟩
  · intro hz
    have hzxy := Finset.mem_inter.mp hz
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_biUnion.mpr ⟨x, hxI, hzxy.1⟩, ?_⟩
    intro i hi
    rw [hAeq] at hi
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl
    · exact hzxy.1
    · exact hzxy.2

private theorem fifteenSeven_add_distinguishedPairMoment_le_of_pair_cap
    {Iota Beta Gamma : Type*}
    [DecidableEq Iota] [DecidableEq Beta] [DecidableEq Gamma]
    (I : Finset Iota) (F : Iota → Finset Beta)
    (G : Iota → Finset Gamma) (h : Nat)
    (hinter : ∀ x ∈ I, ∀ y ∈ I, x ≠ y →
      (F x ∩ F y).card + (G x ∩ G y).card ≤ h) :
    distinguishedPairMoment I F + distinguishedPairMoment I G ≤
      Nat.choose I.card 2 * h := by
  classical
  unfold distinguishedPairMoment
  rw [← Finset.sum_add_distrib]
  calc
    _ ≤ ∑ _A ∈ I.powersetCard 2, h := by
      apply Finset.sum_le_sum
      intro A hA
      have hAspec := Finset.mem_powersetCard.mp hA
      obtain ⟨x, y, hxy, hAeq⟩ := Finset.card_eq_two.mp hAspec.2
      have hxI : x ∈ I := hAspec.1 (by rw [hAeq]; simp)
      have hyI : y ∈ I := hAspec.1 (by rw [hAeq]; simp)
      rw [fifteenSeven_distinguishedPairTerm_eq_inter I F A hA hxy hAeq,
        fifteenSeven_distinguishedPairTerm_eq_inter I G A hA hxy hAeq]
      exact hinter x hxI y hyI hxy
    _ = Nat.choose I.card 2 * h := by
      simp [Finset.card_powersetCard]

theorem fifteenSeven_linePairMoment_add_circlePairMoment_le
    (cfg : Configuration alpha) (b : GeometricBlock cfg)
    (h15 : Fintype.card alpha = 15)
    (hbase : (geometricBlockSupport cfg b).card = 7) :
    distinguishedPairMoment
        (Finset.univ : Finset (BlockOutsider (blockSystem cfg) b))
        (lineBasePairs (blockSystem cfg) b) +
      fifteenSevenPairMoment cfg b ≤ 84 := by
  classical
  let S := blockSystem cfg
  let I : Finset (BlockOutsider S b) := Finset.univ
  have hsevenS : (S.support b).card = 7 := by
    simpa only [S] using hbase
  have hpairCap : ∀ x ∈ I, ∀ y ∈ I, x ≠ y →
      (lineBasePairs S b x ∩ lineBasePairs S b y).card +
        (circlePencil S b x ∩ circlePencil S b y).card ≤ 3 := by
    intro x _hx y _hy hxy
    rw [circlePencil_inter_eq_commonPencils]
    have hpoint := card_commonPencils_add_inter_lineBasePairs_le_three
      S b hsevenS x y hxy
    omega
  have hpair :
      distinguishedPairMoment I (lineBasePairs S b) +
        distinguishedPairMoment I (circlePencil S b) ≤
          Nat.choose I.card 2 * 3 :=
    fifteenSeven_add_distinguishedPairMoment_le_of_pair_cap I
      (lineBasePairs S b) (circlePencil S b) 3 hpairCap
  have hIcard : I.card = 8 := by
    dsimp only [I]
    rw [Finset.card_univ, Fintype.card_coe, card_blockOutsiders,
      h15, hsevenS]
  unfold fifteenSevenPairMoment
  change distinguishedPairMoment I (lineBasePairs S b) +
    distinguishedPairMoment I (circlePencil S b) ≤ 84
  rw [hIcard] at hpair
  norm_num [Nat.choose] at hpair ⊢
  exact hpair

/-- Every possible loss in the `(15,7)` corrected pencil, retained with its
literal finite-set meaning.  Their sum is at most six. -/
structure FifteenSevenCirclePencilResidualData
    (cfg : Configuration alpha) (b : GeometricBlock cfg) : Prop where
  outsider_admissible :
    Admissible (finsetRestrictionConfiguration cfg
      (blockOutsiders (blockSystem cfg) b))
  fan_sum_lower : 144 ≤ fifteenSevenFanSum cfg b
  outsider_count_lower :
    17 ≤ (fifteenSevenOutsiderCircleBlocks cfg b).card
  pair_moment_upper : fifteenSevenPairMoment cfg b ≤ 84
  covered_add_one_le :
    (fifteenSevenCoveredCircles cfg b).card + 1 ≤
      (blockSystem cfg).totalCircleCount
  total_count_upper : (blockSystem cfg).totalCircleCount ≤ 84
  slack_le_six :
    (fifteenSevenFanSum cfg b - 144) +
      ((fifteenSevenOutsiderCircleBlocks cfg b).card - 17) +
      (84 - fifteenSevenPairMoment cfg b) +
      ((blockSystem cfg).totalCircleCount - 1 -
        (fifteenSevenCoveredCircles cfg b).card) +
      (84 - (blockSystem cfg).totalCircleCount) ≤ 6

/-- The fan excess is exactly the loss in the eight three-edge line
matchings on the selected seven-set. -/
theorem fifteenSevenLinePairSum_add_fanSum
    (cfg : Configuration alpha) (b : GeometricBlock cfg)
    (h15 : Fintype.card alpha = 15)
    (hseven : (geometricBlockSupport cfg b).card = 7) :
    fifteenSevenLinePairSum cfg b + fifteenSevenFanSum cfg b = 168 := by
  classical
  let S := blockSystem cfg
  have hsevenS : (S.support b).card = 7 := by
    simpa only [S] using hseven
  have hpoint (x : BlockOutsider S b) :
      (lineBasePairs S b x).card + (circlePencil S b x).card = 21 := by
    rw [card_circlePencil]
    have hpart := card_circleBasePairs_add_card_lineBasePairs S b x
    rw [hsevenS] at hpart
    norm_num [Nat.choose] at hpart ⊢
    omega
  unfold fifteenSevenLinePairSum fifteenSevenFanSum
  rw [← Finset.sum_add_distrib]
  calc
    (∑ x : BlockOutsider S b,
        ((lineBasePairs S b x).card + (circlePencil S b x).card)) =
        ∑ _x : BlockOutsider S b, 21 := by
      apply Fintype.sum_congr
      exact hpoint
    _ = 168 := by
      simp [card_blockOutsiders, h15, hsevenS]

theorem FifteenSevenCirclePencilResidualData.fan_excess_le_six
    {cfg : Configuration alpha} {b : GeometricBlock cfg}
    (R : FifteenSevenCirclePencilResidualData cfg b) :
    fifteenSevenFanSum cfg b - 144 ≤ 6 := by
  have h := R.slack_le_six
  omega

theorem FifteenSevenCirclePencilResidualData.pair_moment_defect_le_six
    {cfg : Configuration alpha} {b : GeometricBlock cfg}
    (R : FifteenSevenCirclePencilResidualData cfg b) :
    84 - fifteenSevenPairMoment cfg b ≤ 6 := by
  have h := R.slack_le_six
  omega

theorem FifteenSevenCirclePencilResidualData.core_slack_le_six
    {cfg : Configuration alpha} {b : GeometricBlock cfg}
    (R : FifteenSevenCirclePencilResidualData cfg b) :
    (fifteenSevenFanSum cfg b - 144) +
      (84 - fifteenSevenPairMoment cfg b) ≤ 6 := by
  have h := R.slack_le_six
  omega

/-- The genuinely geometric part of the residual also retains the circle
excess of the eight outsider centres.  This is the sharp quantity for a
simultaneous chord-packing theorem: a near-one-factor packing can have core
slack three, so the centre geometry cannot be discarded. -/
theorem FifteenSevenCirclePencilResidualData.outsider_chord_slack_le_six
    {cfg : Configuration alpha} {b : GeometricBlock cfg}
    (R : FifteenSevenCirclePencilResidualData cfg b) :
    (fifteenSevenFanSum cfg b - 144) +
      ((fifteenSevenOutsiderCircleBlocks cfg b).card - 17) +
      (84 - fifteenSevenPairMoment cfg b) <= 6 := by
  have h := R.slack_le_six
  omega

theorem FifteenSevenCirclePencilResidualData.pair_moment_lower
    {cfg : Configuration alpha} {b : GeometricBlock cfg}
    (R : FifteenSevenCirclePencilResidualData cfg b) :
    78 ≤ fifteenSevenPairMoment cfg b := by
  have h := R.slack_le_six
  omega

theorem FifteenSevenCirclePencilResidualData.line_pair_sum_lower
    {cfg : Configuration alpha} {b : GeometricBlock cfg}
    (R : FifteenSevenCirclePencilResidualData cfg b)
    (h15 : Fintype.card alpha = 15)
    (hseven : (geometricBlockSupport cfg b).card = 7) :
    18 ≤ fifteenSevenLinePairSum cfg b := by
  have hpartition := fifteenSevenLinePairSum_add_fanSum
    cfg b h15 hseven
  have hfan := R.fan_sum_lower
  have hexcess := R.fan_excess_le_six
  omega

/-- Pure packing already consumes three of the six available units. -/
theorem FifteenSevenCirclePencilResidualData.core_slack_lower_three
    {cfg : Configuration alpha} {b : GeometricBlock cfg}
    (R : FifteenSevenCirclePencilResidualData cfg b)
    (h15 : Fintype.card alpha = 15)
    (hseven : (geometricBlockSupport cfg b).card = 7) :
    3 ≤ (fifteenSevenFanSum cfg b - 144) +
      (84 - fifteenSevenPairMoment cfg b) := by
  classical
  let S := blockSystem cfg
  let I : Finset (BlockOutsider S b) := Finset.univ
  let L := lineBasePairs S b
  have hsevenS : (S.support b).card = 7 := by
    simpa only [S] using hseven
  have hbon : (∑ x ∈ I, (L x).card) ≤
      (I.biUnion L).card + distinguishedPairMoment I L := by
    have h := sum_family_card_add_distinguished_le I L
      (∅ : Finset (BlockBasePair S b)) (by simp)
    simpa using h
  have hunion : (I.biUnion L).card ≤ 21 := by
    have hsub := Finset.card_le_card
      (show I.biUnion L ⊆
        (Finset.univ : Finset (BlockBasePair S b)) from
          Finset.subset_univ _)
    have huniv :
        (Finset.univ : Finset (BlockBasePair S b)).card = 21 := by
      rw [Finset.card_univ, Fintype.card_coe,
        Finset.card_powersetCard, hsevenS]
      norm_num [Nat.choose]
    rw [huniv] at hsub
    exact hsub
  have hpartition := fifteenSevenLinePairSum_add_fanSum
    cfg b h15 hseven
  change (∑ x ∈ I, (L x).card) + fifteenSevenFanSum cfg b = 168
    at hpartition
  have hpairs := fifteenSeven_linePairMoment_add_circlePairMoment_le
    cfg b h15 hseven
  change distinguishedPairMoment I L +
    fifteenSevenPairMoment cfg b ≤ 84 at hpairs
  have hfan := R.fan_sum_lower
  have hmoment := R.pair_moment_upper
  omega

private theorem fifteenSeven_correctedPencil_master
    (cfg : Configuration alpha) (b : GeometricBlock cfg) :
    fifteenSevenFanSum cfg b +
        (fifteenSevenOutsiderCircleBlocks cfg b).card ≤
      (fifteenSevenCoveredCircles cfg b).card +
        fifteenSevenPairMoment cfg b := by
  classical
  let S := blockSystem cfg
  let O := blockOutsiders S b
  let Q := finsetRestrictionConfiguration cfg O
  let I : Finset (BlockOutsider S b) := Finset.univ
  let F : BlockOutsider S b → Finset (GeometricBlock cfg) := circlePencil S b
  let D := finsetRestrictionCircleBlocks cfg O
  let U := I.biUnion F
  have hdist : ∀ d ∈ D, d ∈ U →
      3 ≤ (I.filter fun x => d ∈ F x).card := by
    intro d hdD hdU
    dsimp only [D, finsetRestrictionCircleBlocks] at hdD
    obtain ⟨c, _hc, rfl⟩ := Finset.mem_image.mp hdD
    let C := liftFinsetRestrictionDeterminedCircle cfg O c
    have hinterBase :
        (S.support (Sum.inr C) ∩ S.support b).card = 2 := by
      rcases Finset.mem_biUnion.mp hdU with ⟨x, _hx, hxFan⟩
      obtain ⟨p, _hp, howner⟩ := mem_circlePencil.mp hxFan
      rw [← howner, pencilOwner_inter_base S b x p]
      exact (Finset.mem_powersetCard.mp p.2).2
    have htraceSub : circleTrace Q c.1 ⊆
        I.filter fun x => (Sum.inr C : GeometricBlock cfg) ∈ F x := by
      intro x hx
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ x, ?_⟩
      dsimp only [F]
      apply mem_circlePencil_of_kind_circle_of_inter_card_two
        S b x (Sum.inr C)
      · rfl
      · change x.1 ∈ circleTrace cfg C.1
        exact (mem_circleTrace_finsetRestriction_iff cfg O c.1 x).mp hx
      · exact hinterBase
    have hthree := Erdos506.V3.circleSupport_card_ge_three Q c
    exact hthree.trans (Finset.card_le_card htraceSub)
  have hmaster := sum_family_card_add_distinguished_le I F D (by
    simpa only [U] using hdist)
  simpa only [fifteenSevenFanSum, fifteenSevenOutsiderCircleBlocks,
    fifteenSevenCoveredCircles, fifteenSevenPairMoment,
    I, F, D, U, O, S] using hmaster

private theorem fifteenSeven_covered_add_one_le_total
    (cfg : Configuration alpha) (b : GeometricBlock cfg)
    (hcircle : (blockSystem cfg).kind b = .circle) :
    (fifteenSevenCoveredCircles cfg b).card + 1 ≤
      (blockSystem cfg).totalCircleCount := by
  classical
  let S := blockSystem cfg
  let O := blockOutsiders S b
  let Q := finsetRestrictionConfiguration cfg O
  let I : Finset (BlockOutsider S b) := Finset.univ
  let F : BlockOutsider S b → Finset (GeometricBlock cfg) := circlePencil S b
  let D := finsetRestrictionCircleBlocks cfg O
  let U := I.biUnion F
  have hbnotU : b ∉ U := by
    intro hbU
    rcases Finset.mem_biUnion.mp hbU with ⟨x, _hx, hbFan⟩
    obtain ⟨p, _hp, howner⟩ := mem_circlePencil.mp hbFan
    exact pencilOwner_ne_base S b x p howner
  have hbnotD : b ∉ D := by
    intro hbD
    dsimp only [D, finsetRestrictionCircleBlocks] at hbD
    obtain ⟨c, _hc, hcb⟩ := Finset.mem_image.mp hbD
    have htraceThree := Erdos506.V3.circleSupport_card_ge_three Q c
    have htraceNonempty : (circleTrace Q c.1).Nonempty := by
      apply Finset.nonempty_iff_ne_empty.mpr
      intro hempty
      rw [hempty] at htraceThree
      simp at htraceThree
    obtain ⟨x, hx⟩ := htraceNonempty
    have hxAmbient :=
      (mem_circleTrace_finsetRestriction_iff cfg O c.1 x).mp hx
    let C := liftFinsetRestrictionDeterminedCircle cfg O c
    have hsupportEq : S.support (Sum.inr C) = S.support b :=
      congrArg S.support hcb
    apply (mem_blockOutsiders.mp x.2)
    rw [← hsupportEq]
    change x.1 ∈ circleTrace cfg C.1
    exact hxAmbient
  have hcoveredSub : insert b (U ∪ D) ⊆ S.blocksOfKind .circle := by
    intro e he
    rcases Finset.mem_insert.mp he with rfl | he
    · exact S.mem_blocksOfKind.mpr hcircle
    · rcases Finset.mem_union.mp he with heU | heD
      · rcases Finset.mem_biUnion.mp heU with ⟨x, _hx, hxFan⟩
        exact S.mem_blocksOfKind.mpr (circlePencil_kind S b x hxFan)
      · dsimp only [D, finsetRestrictionCircleBlocks] at heD
        obtain ⟨c, _hc, rfl⟩ := Finset.mem_image.mp heD
        exact S.mem_blocksOfKind.mpr rfl
  have hcardSub := Finset.card_le_card hcoveredSub
  have hbnot : b ∉ U ∪ D := by
    intro hb
    rcases Finset.mem_union.mp hb with hbU | hbD
    · exact hbnotU hbU
    · exact hbnotD hbD
  rw [Finset.card_insert_of_notMem hbnot] at hcardSub
  change (U ∪ D).card + 1 ≤ S.totalCircleCount at hcardSub
  simpa only [fifteenSevenCoveredCircles,
    fifteenSevenOutsiderCircleBlocks, U, D, I, F, O, S] using hcardSub

/-- Configuration-level extraction of the complete six-unit residual. -/
theorem FiniteWindowRichBlockResidual.fifteen_seven_circle_residual
    (Mel : RealPlaneMelchiorPrinciple.{u})
    (EvenArr : RealPlaneEvenArrangementPrinciple.{u})
    {cfg : Configuration alpha} (R : FiniteWindowRichBlockResidual cfg)
    (hadm : Admissible cfg)
    (hcircle : (blockSystem cfg).kind R.block = .circle)
    (h15 : Fintype.card alpha = 15)
    (hseven : (geometricBlockSupport cfg R.block).card = 7)
    (hcount : Erdos506.V4.circleCount cfg <
      Erdos506.v1UniformTarget (Fintype.card alpha)) :
    FifteenSevenCirclePencilResidualData cfg R.block := by
  classical
  let S := blockSystem cfg
  let O := blockOutsiders S R.block
  let Q := finsetRestrictionConfiguration cfg O
  let I : Finset (BlockOutsider S R.block) := Finset.univ
  let F : BlockOutsider S R.block → Finset (GeometricBlock cfg) :=
    circlePencil S R.block
  let D := finsetRestrictionCircleBlocks cfg O
  let U := I.biUnion F
  have hsevenS : (S.support R.block).card = 7 := by
    simpa only [S] using hseven
  have hOcard : O.card = 8 := by
    dsimp only [O]
    rw [card_blockOutsiders, h15, hsevenS]
  have hIcard : I.card = 8 := by
    dsimp only [I]
    rw [Finset.card_univ, Fintype.card_coe, hOcard]
  have hQcard : Fintype.card (BlockOutsider S R.block) = 8 := by
    rw [Fintype.card_coe, hOcard]
  have hcap : BlockSizeCap S 7 := by
    have hhalf := halfBlockCap_of_circleCount_lt_v1UniformTarget
      cfg hadm (by omega) hcount
    rw [h15] at hhalf
    norm_num at hhalf
    exact hhalf
  have hQadm : Admissible Q := by
    exact admissible_finsetRestriction_blockOutsiders_of_cap
      cfg R.block 7 (by omega) hcap (by
        change 7 < O.card
        omega)
  have hQlower : 17 ≤ Erdos506.V4.circleCount Q :=
    circleCount_ge_target_of_card_eight
      Mel EvenArr Q hQadm hQcard
  have hDcard : D.card = Erdos506.V4.circleCount Q := by
    dsimp only [D, Q, O]
    exact card_finsetRestrictionCircleBlocks cfg _
  have htotal : S.totalCircleCount = Erdos506.V4.circleCount cfg := by
    rw [totalCircleCount_eq_card_determinedCircle,
      ← Erdos506.V3.circleCount_eq_card_determinedCircle]
  have htotalUpper : S.totalCircleCount ≤ 84 := by
    rw [htotal]
    rw [h15] at hcount
    norm_num [Erdos506.v1UniformTarget, Nat.choose] at hcount
    omega
  have hFcard : ∀ x ∈ I, 18 ≤ (F x).card := by
    intro x _hx
    dsimp only [F]
    rw [card_circlePencil]
    have h := card_circleBasePairs_lower S R.block x
    rw [hsevenS] at h
    norm_num [Nat.choose] at h ⊢
    exact h
  have hfanLower : 144 ≤ ∑ x ∈ I, (F x).card := by
    calc
      144 = ∑ _x ∈ I, 18 := by simp [hIcard]
      _ ≤ _ := Finset.sum_le_sum hFcard
  have hinter : ∀ x ∈ I, ∀ y ∈ I, x ≠ y →
      (F x ∩ F y).card ≤ 3 := by
    intro x _hx y _hy hxy
    dsimp only [F]
    rw [circlePencil_inter_eq_commonPencils]
    have h := card_commonPencils_le_half S R.block x y hxy
    rw [hsevenS] at h
    norm_num at h ⊢
    exact h
  have hmomentUpper : distinguishedPairMoment I F ≤ 84 := by
    have h := distinguishedPairMoment_le I F 3 hinter
    rw [hIcard] at h
    norm_num [Nat.choose] at h ⊢
    exact h
  have hfanLowerNamed : 144 ≤ fifteenSevenFanSum cfg R.block := by
    simpa only [fifteenSevenFanSum, I, F, S] using hfanLower
  have hDlowerRaw : 17 ≤ D.card := by
    rw [hDcard]
    exact hQlower
  have hDlowerNamed :
      17 ≤ (fifteenSevenOutsiderCircleBlocks cfg R.block).card := by
    simpa only [fifteenSevenOutsiderCircleBlocks, D, O, S] using hDlowerRaw
  have hmomentUpperNamed : fifteenSevenPairMoment cfg R.block ≤ 84 := by
    simpa only [fifteenSevenPairMoment, I, F, S] using hmomentUpper
  have hmasterNamed := fifteenSeven_correctedPencil_master cfg R.block
  have hcoveredAddNamed :=
    fifteenSeven_covered_add_one_le_total cfg R.block hcircle
  have htotalUpperNamed : (blockSystem cfg).totalCircleCount ≤ 84 := by
    simpa only [S] using htotalUpper
  have hslack :
      (fifteenSevenFanSum cfg R.block - 144) +
        ((fifteenSevenOutsiderCircleBlocks cfg R.block).card - 17) +
        (84 - fifteenSevenPairMoment cfg R.block) +
        ((blockSystem cfg).totalCircleCount - 1 -
          (fifteenSevenCoveredCircles cfg R.block).card) +
        (84 - (blockSystem cfg).totalCircleCount) ≤ 6 := by
    omega
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · change Admissible Q
    exact hQadm
  · exact hfanLowerNamed
  · exact hDlowerNamed
  · exact hmomentUpperNamed
  · exact hcoveredAddNamed
  · exact htotalUpperNamed
  · exact hslack

/-- Exact one-line consumer for the remaining simultaneous geometry of the
seven-circle chords and their eight outsider centres. -/
theorem FiniteWindowRichBlockResidual.circle_impossible_of_fifteen_seven_of_outsiderChordGap
    (Mel : RealPlaneMelchiorPrinciple.{u})
    (EvenArr : RealPlaneEvenArrangementPrinciple.{u})
    {cfg : Configuration alpha} (R : FiniteWindowRichBlockResidual cfg)
    (hadm : Admissible cfg)
    (hcircle : (blockSystem cfg).kind R.block = .circle)
    (h15 : Fintype.card alpha = 15)
    (hseven : (geometricBlockSupport cfg R.block).card = 7)
    (hcount : Erdos506.V4.circleCount cfg <
      Erdos506.v1UniformTarget (Fintype.card alpha))
    (hgap :
      7 ≤ (fifteenSevenFanSum cfg R.block - 144) +
        ((fifteenSevenOutsiderCircleBlocks cfg R.block).card - 17) +
        (84 - fifteenSevenPairMoment cfg R.block)) : False := by
  have E := R.fifteen_seven_circle_residual
    Mel EvenArr hadm hcircle h15 hseven hcount
  have := E.outsider_chord_slack_le_six
  omega

/-- The stronger pure chord gap remains a convenient compatibility
corollary.  The preceding mixed gap is the lossless geometric seam. -/
theorem FiniteWindowRichBlockResidual.circle_impossible_of_fifteen_seven_of_chordGap
    (Mel : RealPlaneMelchiorPrinciple.{u})
    (EvenArr : RealPlaneEvenArrangementPrinciple.{u})
    {cfg : Configuration alpha} (R : FiniteWindowRichBlockResidual cfg)
    (hadm : Admissible cfg)
    (hcircle : (blockSystem cfg).kind R.block = .circle)
    (h15 : Fintype.card alpha = 15)
    (hseven : (geometricBlockSupport cfg R.block).card = 7)
    (hcount : Erdos506.V4.circleCount cfg <
      Erdos506.v1UniformTarget (Fintype.card alpha))
    (hchordGap :
      7 ≤ (fifteenSevenFanSum cfg R.block - 144) +
        (84 - fifteenSevenPairMoment cfg R.block)) : False := by
  apply R.circle_impossible_of_fifteen_seven_of_outsiderChordGap
    Mel EvenArr hadm hcircle h15 hseven hcount
  omega

end Erdos506.V1
