import Erdos506.V1.LangerApplicationFifteenSevenCircleResidual

/-!
# The lossless seventeen--eight rich-circle residual

The corrected pencil has fourteen units of slack at `(17,8)`.  The line
matching complement already consumes eight of them.  This file retains the
remaining six units as literal finite defects.
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

noncomputable def seventeenEightFanSum
    (cfg : Configuration alpha) (b : GeometricBlock cfg) : Nat :=
  ∑ x : BlockOutsider (blockSystem cfg) b,
    (circlePencil (blockSystem cfg) b x).card

noncomputable def seventeenEightLinePairSum
    (cfg : Configuration alpha) (b : GeometricBlock cfg) : Nat :=
  ∑ x : BlockOutsider (blockSystem cfg) b,
    (lineBasePairs (blockSystem cfg) b x).card

noncomputable def seventeenEightPairMoment
    (cfg : Configuration alpha) (b : GeometricBlock cfg) : Nat :=
  distinguishedPairMoment
    (Finset.univ : Finset (BlockOutsider (blockSystem cfg) b))
    (circlePencil (blockSystem cfg) b)

noncomputable def seventeenEightOutsiderCircleBlocks
    (cfg : Configuration alpha) (b : GeometricBlock cfg) :
    Finset (GeometricBlock cfg) :=
  finsetRestrictionCircleBlocks cfg
    (blockOutsiders (blockSystem cfg) b)

noncomputable def seventeenEightCoveredCircles
    (cfg : Configuration alpha) (b : GeometricBlock cfg) :
    Finset (GeometricBlock cfg) :=
  (Finset.univ.biUnion (circlePencil (blockSystem cfg) b)) ∪
    seventeenEightOutsiderCircleBlocks cfg b

private theorem pencilOwner_eq_of_mem_lineBasePairs_both
    {Point Block : Type*} [Fintype Point] [Fintype Block]
    [DecidableEq Point]
    (S : BlockSystem Point Block) (b : Block)
    (x y : BlockOutsider S b) (p : BlockBasePair S b)
    (hpx : p ∈ lineBasePairs S b x)
    (hpy : p ∈ lineBasePairs S b y) :
    pencilOwner S b x p = pencilOwner S b y p := by
  by_contra hne
  let Lx : LineBlock S :=
    ⟨pencilOwner S b x p, mem_lineBasePairs.mp hpx⟩
  let Ly : LineBlock S :=
    ⟨pencilOwner S b y p, mem_lineBasePairs.mp hpy⟩
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

private theorem card_biUnion_commonPencilBasePairs
    {Point Block : Type*} [Fintype Point] [Fintype Block]
    [DecidableEq Point]
    (S : BlockSystem Point Block) (b : Block)
    (x y : BlockOutsider S b) (hxy : x ≠ y) :
    ((commonPencilBasePairs S b x y).biUnion id).card =
      2 * (commonPencils S b x y).card := by
  classical
  let P := commonPencilBasePairs S b x y
  have hPdisj : ((P : Finset (Finset Point)) :
      Set (Finset Point)).PairwiseDisjoint id :=
    commonPencilBasePairs_pairwiseDisjoint S b x y hxy
  rw [Finset.card_biUnion hPdisj]
  calc
    (∑ A ∈ P, A.card) = ∑ _A ∈ P, 2 := by
      apply Finset.sum_congr rfl
      intro A hA
      dsimp only [P] at hA
      rw [commonPencilBasePairs] at hA
      obtain ⟨c, _hc, rfl⟩ := Finset.mem_image.mp hA
      exact commonPencilBasePair_card S b x y c
    _ = 2 * P.card := by simp [Nat.mul_comm]
    _ = 2 * (commonPencils S b x y).card := by
      rw [card_commonPencilBasePairs]

private theorem card_commonPencils_le_three_of_shared_line
    {Point Block : Type*} [Fintype Point] [Fintype Block]
    [DecidableEq Point]
    (S : BlockSystem Point Block) (b : Block)
    (hbase : (S.support b).card = 8)
    (x y : BlockOutsider S b) (hxy : x ≠ y)
    (p : BlockBasePair S b)
    (hpx : p ∈ lineBasePairs S b x)
    (hpy : p ∈ lineBasePairs S b y) :
    (commonPencils S b x y).card ≤ 3 := by
  classical
  let L : LineBlock S :=
    ⟨pencilOwner S b x p, mem_lineBasePairs.mp hpx⟩
  have howner := pencilOwner_eq_of_mem_lineBasePairs_both
    S b x y p hpx hpy
  have hxL : x.1 ∈ S.support L.1 :=
    pencilOwner_contains_outsider S b x p
  have hyL : y.1 ∈ S.support L.1 := by
    rw [howner]
    exact pencilOwner_contains_outsider S b y p
  let P := commonPencilBasePairs S b x y
  have hpDisj : Disjoint p.1 (P.biUnion id) := by
    rw [Finset.disjoint_left]
    intro z hzp hzUnion
    obtain ⟨A, hAP, hzA⟩ := Finset.mem_biUnion.mp hzUnion
    dsimp only [P] at hAP
    rw [commonPencilBasePairs] at hAP
    obtain ⟨c, _hc, hAc⟩ := Finset.mem_image.mp hAP
    have hcross := line_trace_disjoint_commonPencilBasePair_generic
      S b L x y hxy hxL hyL c
    apply (Finset.disjoint_left.mp hcross) z
    · rw [pencilOwner_inter_base S b x p]
      exact hzp
    · rw [hAc]
      exact hzA
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
  have hle := Finset.card_le_card hcover
  rw [Finset.card_union_of_disjoint hpDisj,
    (Finset.mem_powersetCard.mp p.2).2,
    card_biUnion_commonPencilBasePairs S b x y hxy,
    hbase] at hle
  omega

theorem card_commonPencils_add_inter_lineBasePairs_le_four
    {Point Block : Type*} [Fintype Point] [Fintype Block]
    [DecidableEq Point]
    (S : BlockSystem Point Block) (b : Block)
    (hbase : (S.support b).card = 8)
    (x y : BlockOutsider S b) (hxy : x ≠ y) :
    (commonPencils S b x y).card +
      (lineBasePairs S b x ∩ lineBasePairs S b y).card ≤ 4 := by
  classical
  by_cases hempty :
      lineBasePairs S b x ∩ lineBasePairs S b y = ∅
  · rw [hempty]
    simp only [Finset.card_empty, Nat.add_zero]
    have h := card_commonPencils_le_half S b x y hxy
    rw [hbase] at h
    norm_num at h ⊢
    exact h
  · obtain ⟨p, hp⟩ := Finset.exists_mem_of_ne_empty hempty
    have hp' := Finset.mem_inter.mp hp
    have hcommon := card_commonPencils_le_three_of_shared_line
      S b hbase x y hxy p hp'.1 hp'.2
    have hline := card_inter_lineBasePairs_le_one S b x y hxy
    omega

private theorem distinguishedPairTerm_eq_inter
    {Iota Beta : Type*} [DecidableEq Iota] [DecidableEq Beta]
    (I : Finset Iota) (F : Iota → Finset Beta)
    (A : Finset Iota) (hA : A ∈ I.powersetCard 2)
    {x y : Iota} (hxy : x ≠ y) (hAeq : A = {x, y}) :
    ((I.biUnion F).filter fun z => ∀ i ∈ A, z ∈ F i) =
      F x ∩ F y := by
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

theorem add_distinguishedPairMoment_le_of_pair_cap
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
      have hxI := hAspec.1 (by simp [hAeq])
      have hyI := hAspec.1 (by simp [hAeq])
      rw [distinguishedPairTerm_eq_inter I F A hA hxy hAeq,
        distinguishedPairTerm_eq_inter I G A hA hxy hAeq]
      exact hinter x hxI y hyI hxy
    _ = Nat.choose I.card 2 * h := by
      simp [Finset.card_powersetCard]

theorem seventeenEight_linePairMoment_add_circlePairMoment_le
    (cfg : Configuration alpha) (b : GeometricBlock cfg)
    (h17 : Fintype.card alpha = 17)
    (height : (geometricBlockSupport cfg b).card = 8) :
    distinguishedPairMoment
        (Finset.univ : Finset (BlockOutsider (blockSystem cfg) b))
        (lineBasePairs (blockSystem cfg) b) +
      seventeenEightPairMoment cfg b ≤ 144 := by
  let S := blockSystem cfg
  let I : Finset (BlockOutsider S b) := Finset.univ
  have hpair := add_distinguishedPairMoment_le_of_pair_cap I
    (lineBasePairs S b) (circlePencil S b) 4 (by
      intro x _hx y _hy hxy
      simpa [commonPencils, Nat.add_comm] using
        (card_commonPencils_add_inter_lineBasePairs_le_four
          S b height x y hxy))
  have hIcard : I.card = 9 := by
    dsimp only [I]
    rw [Finset.card_univ, Fintype.card_coe, card_blockOutsiders,
      h17, height]
  change distinguishedPairMoment I (lineBasePairs S b) +
    distinguishedPairMoment I (circlePencil S b) ≤ 144
  rw [hIcard] at hpair
  norm_num [Nat.choose] at hpair ⊢
  exact hpair

theorem seventeenEightLinePairSum_add_fanSum
    (cfg : Configuration alpha) (b : GeometricBlock cfg)
    (h17 : Fintype.card alpha = 17)
    (height : (geometricBlockSupport cfg b).card = 8) :
    seventeenEightLinePairSum cfg b + seventeenEightFanSum cfg b = 252 := by
  let S := blockSystem cfg
  have hpoint (x : BlockOutsider S b) :
      (lineBasePairs S b x).card + (circlePencil S b x).card = 28 := by
    rw [card_circlePencil]
    have hpart := card_circleBasePairs_add_card_lineBasePairs S b x
    change (S.support b).card = 8 at height
    rw [height] at hpart
    norm_num [Nat.choose] at hpart ⊢
    omega
  unfold seventeenEightLinePairSum seventeenEightFanSum
  rw [← Finset.sum_add_distrib]
  calc
    (∑ x : BlockOutsider S b,
        ((lineBasePairs S b x).card + (circlePencil S b x).card)) =
        ∑ _x : BlockOutsider S b, 28 := by
      apply Fintype.sum_congr
      exact hpoint
    _ = 252 := by
      rw [Fintype.sum_const, Fintype.card_coe, card_blockOutsiders]
      rw [h17, height]
      norm_num

structure SeventeenEightCirclePencilResidualData
    (cfg : Configuration alpha) (b : GeometricBlock cfg) : Prop where
  outsider_admissible :
    Admissible (finsetRestrictionConfiguration cfg
      (blockOutsiders (blockSystem cfg) b))
  fan_sum_lower : 216 ≤ seventeenEightFanSum cfg b
  outsider_count_lower :
    25 ≤ (seventeenEightOutsiderCircleBlocks cfg b).card
  pair_moment_upper : seventeenEightPairMoment cfg b ≤ 144
  covered_add_one_le :
    (seventeenEightCoveredCircles cfg b).card + 1 ≤
      (blockSystem cfg).totalCircleCount
  total_count_upper : (blockSystem cfg).totalCircleCount ≤ 112
  slack_le_fourteen :
    (seventeenEightFanSum cfg b - 216) +
      ((seventeenEightOutsiderCircleBlocks cfg b).card - 25) +
      (144 - seventeenEightPairMoment cfg b) +
      ((blockSystem cfg).totalCircleCount - 1 -
        (seventeenEightCoveredCircles cfg b).card) +
      (112 - (blockSystem cfg).totalCircleCount) ≤ 14

theorem SeventeenEightCirclePencilResidualData.outsider_chord_slack_le_fourteen
    {cfg : Configuration alpha} {b : GeometricBlock cfg}
    (R : SeventeenEightCirclePencilResidualData cfg b) :
    (seventeenEightFanSum cfg b - 216) +
      ((seventeenEightOutsiderCircleBlocks cfg b).card - 25) +
      (144 - seventeenEightPairMoment cfg b) ≤ 14 := by
  omega

theorem SeventeenEightCirclePencilResidualData.core_slack_lower_eight
    {cfg : Configuration alpha} {b : GeometricBlock cfg}
    (_R : SeventeenEightCirclePencilResidualData cfg b)
    (h17 : Fintype.card alpha = 17)
    (height : (geometricBlockSupport cfg b).card = 8) :
    8 ≤ (seventeenEightFanSum cfg b - 216) +
      (144 - seventeenEightPairMoment cfg b) := by
  classical
  let S := blockSystem cfg
  let I : Finset (BlockOutsider S b) := Finset.univ
  let L := lineBasePairs S b
  have hbon : (∑ x ∈ I, (L x).card) ≤
      (I.biUnion L).card + distinguishedPairMoment I L := by
    have h := sum_family_card_add_distinguished_le I L
      (∅ : Finset (BlockBasePair S b)) (by simp)
    simpa using h
  have hunion : (I.biUnion L).card ≤ 28 := by
    have hsub := Finset.card_le_card
      (show I.biUnion L ⊆
        (Finset.univ : Finset (BlockBasePair S b)) from
          Finset.subset_univ _)
    have huniv :
        (Finset.univ : Finset (BlockBasePair S b)).card = 28 := by
      rw [Finset.card_univ, Fintype.card_coe,
        Finset.card_powersetCard, height]
      norm_num [Nat.choose]
    rw [huniv] at hsub
    exact hsub
  have hpartition := seventeenEightLinePairSum_add_fanSum
    cfg b h17 height
  change (∑ x ∈ I, (L x).card) + seventeenEightFanSum cfg b = 252
    at hpartition
  have hpairs := seventeenEight_linePairMoment_add_circlePairMoment_le
    cfg b h17 height
  change distinguishedPairMoment I L +
    seventeenEightPairMoment cfg b ≤ 144 at hpairs
  omega

private theorem seventeenEight_restrictionCircle_degree_ge_three
    (cfg : Configuration alpha) (b d : GeometricBlock cfg)
    (hdD : d ∈ seventeenEightOutsiderCircleBlocks cfg b)
    (hdU : d ∈ (Finset.univ :
      Finset (BlockOutsider (blockSystem cfg) b)).biUnion
        (circlePencil (blockSystem cfg) b)) :
    3 ≤ ((Finset.univ : Finset (BlockOutsider (blockSystem cfg) b)).filter
      fun x => d ∈ circlePencil (blockSystem cfg) b x).card := by
  classical
  let S := blockSystem cfg
  let O := blockOutsiders S b
  dsimp only [seventeenEightOutsiderCircleBlocks,
    finsetRestrictionCircleBlocks] at hdD
  obtain ⟨c, _hc, rfl⟩ := Finset.mem_image.mp hdD
  let C := liftFinsetRestrictionDeterminedCircle cfg O c
  have hinterBase :
      (S.support (Sum.inr C) ∩ S.support b).card = 2 := by
    rcases Finset.mem_biUnion.mp hdU with ⟨x, _hx, hxFan⟩
    obtain ⟨p, _hp, howner⟩ := mem_circlePencil.mp hxFan
    rw [← howner, pencilOwner_inter_base S b x p]
    exact (Finset.mem_powersetCard.mp p.2).2
  have htraceSub :
      circleTrace (finsetRestrictionConfiguration cfg O) c.1 ⊆
        (Finset.univ : Finset (BlockOutsider S b)).filter
          fun x => (Sum.inr C : GeometricBlock cfg) ∈ circlePencil S b x := by
    intro x hx
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ x, ?_⟩
    apply mem_circlePencil_of_kind_circle_of_inter_card_two
      S b x (Sum.inr C)
    · rfl
    · change x.1 ∈ circleTrace cfg C.1
      exact (mem_circleTrace_finsetRestriction_iff cfg O c.1 x).mp hx
    · exact hinterBase
  have hthree := Erdos506.V3.circleSupport_card_ge_three
    (finsetRestrictionConfiguration cfg O) c
  exact hthree.trans (Finset.card_le_card htraceSub)

private theorem base_not_mem_circlePencil_union
    (cfg : Configuration alpha) (b : GeometricBlock cfg) :
    b ∉ (Finset.univ :
      Finset (BlockOutsider (blockSystem cfg) b)).biUnion
        (circlePencil (blockSystem cfg) b) := by
  classical
  intro hbU
  rcases Finset.mem_biUnion.mp hbU with ⟨x, _hx, hbFan⟩
  obtain ⟨p, _hp, howner⟩ := mem_circlePencil.mp hbFan
  exact pencilOwner_ne_base (blockSystem cfg) b x p howner

private theorem base_not_mem_seventeenEightOutsiderCircleBlocks
    (cfg : Configuration alpha) (b : GeometricBlock cfg) :
    b ∉ seventeenEightOutsiderCircleBlocks cfg b := by
  classical
  let S := blockSystem cfg
  let O := blockOutsiders S b
  intro hbD
  dsimp only [seventeenEightOutsiderCircleBlocks,
    finsetRestrictionCircleBlocks] at hbD
  obtain ⟨c, _hc, hcb⟩ := Finset.mem_image.mp hbD
  have htraceThree := Erdos506.V3.circleSupport_card_ge_three
    (finsetRestrictionConfiguration cfg O) c
  obtain ⟨x, hx⟩ := Finset.exists_mem_of_ne_empty (by
    intro hempty
    rw [hempty] at htraceThree
    simp at htraceThree)
  have hxAmbient :=
    (mem_circleTrace_finsetRestriction_iff cfg O c.1 x).mp hx
  let C := liftFinsetRestrictionDeterminedCircle cfg O c
  have hsupportEq : S.support (Sum.inr C) = S.support b :=
    congrArg S.support hcb
  apply (mem_blockOutsiders.mp x.2)
  rw [← hsupportEq]
  change x.1 ∈ circleTrace cfg C.1
  exact hxAmbient

theorem seventeenEight_exact_cover
    (cfg : Configuration alpha) (b : GeometricBlock cfg)
    (hcircle : (blockSystem cfg).kind b = .circle) :
    seventeenEightFanSum cfg b +
        (seventeenEightOutsiderCircleBlocks cfg b).card ≤
      (seventeenEightCoveredCircles cfg b).card +
        seventeenEightPairMoment cfg b ∧
    (seventeenEightCoveredCircles cfg b).card + 1 ≤
      (blockSystem cfg).totalCircleCount := by
  classical
  let S := blockSystem cfg
  let I : Finset (BlockOutsider S b) := Finset.univ
  let F := circlePencil S b
  let D := seventeenEightOutsiderCircleBlocks cfg b
  let U := I.biUnion F
  have hmaster := sum_family_card_add_distinguished_le I F D (by
    intro d hdD hdU
    exact seventeenEight_restrictionCircle_degree_ge_three
      cfg b d hdD hdU)
  have hcoveredSub : insert b (U ∪ D) ⊆ S.blocksOfKind .circle := by
    intro e he
    rcases Finset.mem_insert.mp he with rfl | he
    · exact S.mem_blocksOfKind.mpr hcircle
    · rcases Finset.mem_union.mp he with heU | heD
      · rcases Finset.mem_biUnion.mp heU with ⟨x, _hx, hxFan⟩
        exact S.mem_blocksOfKind.mpr (circlePencil_kind S b x hxFan)
      · dsimp only [D, seventeenEightOutsiderCircleBlocks,
          finsetRestrictionCircleBlocks] at heD
        obtain ⟨c, _hc, rfl⟩ := Finset.mem_image.mp heD
        exact S.mem_blocksOfKind.mpr rfl
  have hbnot : b ∉ U ∪ D := by
    rw [Finset.mem_union, not_or]
    exact ⟨base_not_mem_circlePencil_union cfg b,
      base_not_mem_seventeenEightOutsiderCircleBlocks cfg b⟩
  have hcardSub := Finset.card_le_card hcoveredSub
  rw [Finset.card_insert_of_notMem hbnot] at hcardSub
  change (U ∪ D).card + 1 ≤ S.totalCircleCount at hcardSub
  change (∑ x ∈ I, (F x).card) + D.card ≤
    (U ∪ D).card + distinguishedPairMoment I F at hmaster
  exact ⟨hmaster, hcardSub⟩

private theorem seventeenEight_outsider_data
    (Mel : RealPlaneMelchiorPrinciple.{u})
    (EvenArr : RealPlaneEvenArrangementPrinciple.{u})
    (Cross : RealPlaneRadicalAxisCrossBlockPrinciple.{u})
    (cfg : Configuration alpha) (hadm : Admissible cfg)
    (b : GeometricBlock cfg)
    (h17 : Fintype.card alpha = 17)
    (height : (geometricBlockSupport cfg b).card = 8)
    (hcount : Erdos506.V4.circleCount cfg <
      Erdos506.v1UniformTarget (Fintype.card alpha)) :
    Admissible (finsetRestrictionConfiguration cfg
      (blockOutsiders (blockSystem cfg) b)) ∧
    25 ≤ (seventeenEightOutsiderCircleBlocks cfg b).card := by
  classical
  let S := blockSystem cfg
  let O := blockOutsiders S b
  let Q := finsetRestrictionConfiguration cfg O
  have hOcard : O.card = 9 := by
    dsimp only [O]
    rw [card_blockOutsiders, h17, height]
  have hQcard : Fintype.card (BlockOutsider S b) = 9 := by
    rw [Fintype.card_coe, hOcard]
  have hcap : BlockSizeCap S 8 := by
    have hhalf := halfBlockCap_of_circleCount_lt_v1UniformTarget
      cfg hadm (by omega) hcount
    rw [h17] at hhalf
    norm_num at hhalf
    exact hhalf
  have hQadm : Admissible Q := by
    exact admissible_finsetRestriction_blockOutsiders_of_cap
      cfg b 8 (by omega) hcap (by
        change 8 < O.card
        omega)
  have hQlower : 25 ≤ Erdos506.V4.circleCount Q :=
    circleCount_ge_twenty_five_of_card_nine
      Mel EvenArr Cross Q hQadm hQcard
  have hDcard : (seventeenEightOutsiderCircleBlocks cfg b).card =
      Erdos506.V4.circleCount Q := by
    dsimp only [seventeenEightOutsiderCircleBlocks, Q, O]
    exact card_finsetRestrictionCircleBlocks cfg _
  exact ⟨hQadm, by rw [hDcard]; exact hQlower⟩

private theorem seventeenEight_fan_moment_bounds
    (cfg : Configuration alpha) (b : GeometricBlock cfg)
    (h17 : Fintype.card alpha = 17)
    (height : (geometricBlockSupport cfg b).card = 8) :
    216 ≤ seventeenEightFanSum cfg b ∧
      seventeenEightPairMoment cfg b ≤ 144 := by
  classical
  let S := blockSystem cfg
  let I : Finset (BlockOutsider S b) := Finset.univ
  let F := circlePencil S b
  have hIcard : I.card = 9 := by
    dsimp only [I]
    rw [Finset.card_univ, Fintype.card_coe, card_blockOutsiders,
      h17, height]
  have hFcard : ∀ x ∈ I, 24 ≤ (F x).card := by
    intro x _hx
    dsimp only [F]
    rw [card_circlePencil]
    have h := card_circleBasePairs_lower S b x
    change (S.support b).card = 8 at height
    rw [height] at h
    norm_num [Nat.choose] at h ⊢
    exact h
  have hfan : 216 ≤ ∑ x ∈ I, (F x).card := by
    calc
      216 = ∑ _x ∈ I, 24 := by simp [hIcard]
      _ ≤ _ := Finset.sum_le_sum hFcard
  have hinter : ∀ x ∈ I, ∀ y ∈ I, x ≠ y →
      (F x ∩ F y).card ≤ 4 := by
    intro x _hx y _hy hxy
    dsimp only [F]
    have h := card_commonPencils_le_half S b x y hxy
    rw [height] at h
    norm_num at h ⊢
    exact h
  have hmoment := distinguishedPairMoment_le I F 4 hinter
  rw [hIcard] at hmoment
  norm_num [Nat.choose] at hmoment
  exact ⟨hfan, hmoment⟩

theorem FiniteWindowRichBlockResidual.seventeen_eight_circle_residual
    (Mel : RealPlaneMelchiorPrinciple.{u})
    (EvenArr : RealPlaneEvenArrangementPrinciple.{u})
    (Cross : RealPlaneRadicalAxisCrossBlockPrinciple.{u})
    {cfg : Configuration alpha} (R : FiniteWindowRichBlockResidual cfg)
    (hadm : Admissible cfg)
    (hcircle : (blockSystem cfg).kind R.block = .circle)
    (h17 : Fintype.card alpha = 17)
    (height : (geometricBlockSupport cfg R.block).card = 8)
    (hcount : Erdos506.V4.circleCount cfg <
      Erdos506.v1UniformTarget (Fintype.card alpha)) :
    SeventeenEightCirclePencilResidualData cfg R.block := by
  let S := blockSystem cfg
  let D := seventeenEightOutsiderCircleBlocks cfg R.block
  let U := seventeenEightCoveredCircles cfg R.block
  obtain ⟨hQadm, hDlower⟩ := seventeenEight_outsider_data
    Mel EvenArr Cross cfg hadm R.block h17 height hcount
  obtain ⟨hfan, hmoment⟩ :=
    seventeenEight_fan_moment_bounds cfg R.block h17 height
  obtain ⟨hmaster, hcovered⟩ :=
    seventeenEight_exact_cover cfg R.block hcircle
  have htotal : S.totalCircleCount ≤ 112 := by
    rw [totalCircleCount_eq_card_determinedCircle,
      ← Erdos506.V3.circleCount_eq_card_determinedCircle]
    rw [h17] at hcount
    norm_num [Erdos506.v1UniformTarget, Nat.choose] at hcount ⊢
    omega
  have hslack :
      (seventeenEightFanSum cfg R.block - 216) +
        (D.card - 25) +
        (144 - seventeenEightPairMoment cfg R.block) +
        (S.totalCircleCount - 1 - U.card) +
        (112 - S.totalCircleCount) ≤ 14 := by
    dsimp only [D, U] at hmaster hcovered hDlower ⊢
    omega
  refine ⟨hQadm, hfan, ?_, hmoment, ?_, htotal, ?_⟩
  · change 25 ≤ D.card
    exact hDlower
  · change U.card + 1 ≤ S.totalCircleCount
    exact hcovered
  · change
      (seventeenEightFanSum cfg R.block - 216) +
        (D.card - 25) +
        (144 - seventeenEightPairMoment cfg R.block) +
        (S.totalCircleCount - 1 - U.card) +
        (112 - S.totalCircleCount) ≤ 14
    exact hslack

/-- The single remaining `(17,8)` seam.  The finite line-pair packing gives
eight units unconditionally; simultaneous real-conic geometry must force a
seventh additional unit among the outsider-circle and chord defects. -/
theorem FiniteWindowRichBlockResidual.circle_impossible_of_seventeen_eight_of_outsiderChordGap
    (Mel : RealPlaneMelchiorPrinciple.{u})
    (EvenArr : RealPlaneEvenArrangementPrinciple.{u})
    (Cross : RealPlaneRadicalAxisCrossBlockPrinciple.{u})
    {cfg : Configuration alpha} (R : FiniteWindowRichBlockResidual cfg)
    (hadm : Admissible cfg)
    (hcircle : (blockSystem cfg).kind R.block = .circle)
    (h17 : Fintype.card alpha = 17)
    (height : (geometricBlockSupport cfg R.block).card = 8)
    (hcount : Erdos506.V4.circleCount cfg <
      Erdos506.v1UniformTarget (Fintype.card alpha))
    (hgap :
      15 ≤ (seventeenEightFanSum cfg R.block - 216) +
        ((seventeenEightOutsiderCircleBlocks cfg R.block).card - 25) +
        (144 - seventeenEightPairMoment cfg R.block)) : False := by
  have E := R.seventeen_eight_circle_residual
    Mel EvenArr Cross hadm hcircle h17 height hcount
  have := E.outsider_chord_slack_le_fourteen
  omega

end Erdos506.V1
