import Erdos506.V1.SmallSix
import Erdos506.V4.Main
import Erdos506.V3.InversionLine

/-!
# The equality classifier for a four-block on six points

This file isolates the sharp equality information hidden in the common
rich-block pencil.  It is stated for an abstract tagged `BlockSystem`, so it
can be reused independently of the eventual geometric labelling argument.
-/

namespace Erdos506.V1

open Erdos506.Block
open Erdos506.Block.BlockSystem
open Erdos506.Finite
open Erdos506.Incidence
open Erdos506.V3
open Erdos506.V4

variable {Point Block : Type*} [Fintype Point] [Fintype Block]
  [DecidableEq Point]

noncomputable local instance : DecidableEq Block := Classical.decEq Block

/-- The complete cardinality data on the equality face of the four-circle
pencil on six points. -/
structure FourCirclePencilEqualityData
    (S : BlockSystem Point Block) (b : Block)
    (x y : BlockOutsider S b) : Prop where
  totalCircleCount_eq : S.totalCircleCount = 7
  xCircleBasePairs_card : (circleBasePairs S b x).card = 4
  yCircleBasePairs_card : (circleBasePairs S b y).card = 4
  xLineBasePairs_card : (lineBasePairs S b x).card = 2
  yLineBasePairs_card : (lineBasePairs S b y).card = 2
  commonPencils_card : (commonPencils S b x y).card = 2
  pencilUnion_card : (circlePencil S b x ∪ circlePencil S b y).card = 6
  exhaustsCircleBlocks :
    insert b (circlePencil S b x ∪ circlePencil S b y) =
      S.blocksOfKind .circle

/-- Sharpness of the rich-circle pencil at `m = 4`, `q = 2`.

The proof uses only the abstract ownership axioms.  In particular it does
not assume the global block rows or any geometric inequality: the two
four-element fans and their at-most-two overlap already force seven circle
blocks, and a cap of seven makes every intervening inequality an equality. -/
theorem four_circle_pencil_equality
    (S : BlockSystem Point Block) (b : Block)
    (hb : S.kind b = .circle)
    (hbase : (S.support b).card = 4)
    (hCircle : S.totalCircleCount ≤ 7)
    (x y : BlockOutsider S b) (hxy : x ≠ y) :
    FourCirclePencilEqualityData S b x y := by
  classical
  have hxPairsLower : 4 ≤ (circleBasePairs S b x).card := by
    have h := card_circleBasePairs_lower S b x
    rw [hbase] at h
    norm_num [Nat.choose] at h
    exact h
  have hyPairsLower : 4 ≤ (circleBasePairs S b y).card := by
    have h := card_circleBasePairs_lower S b y
    rw [hbase] at h
    norm_num [Nat.choose] at h
    exact h
  have hxFanLower : 4 ≤ (circlePencil S b x).card := by
    rw [card_circlePencil]
    exact hxPairsLower
  have hyFanLower : 4 ≤ (circlePencil S b y).card := by
    rw [card_circlePencil]
    exact hyPairsLower
  have hcommonUpper : (commonPencils S b x y).card ≤ 2 := by
    have h := card_commonPencils_le_half S b x y hxy
    rw [hbase] at h
    norm_num at h
    exact h
  have hbnotX : b ∉ circlePencil S b x := by
    intro hbmem
    obtain ⟨u, _hu, hub⟩ := mem_circlePencil.mp hbmem
    exact pencilOwner_ne_base S b x u hub
  have hbnotY : b ∉ circlePencil S b y := by
    intro hbmem
    obtain ⟨u, _hu, hub⟩ := mem_circlePencil.mp hbmem
    exact pencilOwner_ne_base S b y u hub
  have hbnotUnion : b ∉ circlePencil S b x ∪ circlePencil S b y := by
    simp only [Finset.mem_union, not_or]
    exact ⟨hbnotX, hbnotY⟩
  have hcircleSubset :
      insert b (circlePencil S b x ∪ circlePencil S b y) ⊆
        S.blocksOfKind .circle := by
    intro c hc
    rcases Finset.mem_insert.mp hc with rfl | hc
    · exact (S.mem_blocksOfKind).2 hb
    · rcases Finset.mem_union.mp hc with hcx | hcy
      · exact (S.mem_blocksOfKind).2 (circlePencil_kind S b x hcx)
      · exact (S.mem_blocksOfKind).2 (circlePencil_kind S b y hcy)
  have hUnionUpper :
      (circlePencil S b x ∪ circlePencil S b y).card + 1 ≤
        S.totalCircleCount := by
    have hcard := Finset.card_le_card hcircleSubset
    rw [Finset.card_insert_of_notMem hbnotUnion] at hcard
    simpa [BlockSystem.totalCircleCount, Nat.add_comm] using hcard
  have hcardUnion := Finset.card_union_add_card_inter
    (circlePencil S b x) (circlePencil S b y)
  have hcommonEq :
      commonPencils S b x y =
        circlePencil S b x ∩ circlePencil S b y := by
    ext c
    simp [commonPencils]
  have hcommonCardEq :
      (commonPencils S b x y).card =
        (circlePencil S b x ∩ circlePencil S b y).card :=
    congrArg Finset.card hcommonEq
  have hcardUnion' :
      (circlePencil S b x ∪ circlePencil S b y).card +
          (commonPencils S b x y).card =
        (circlePencil S b x).card + (circlePencil S b y).card := by
    omega
  have htotal : S.totalCircleCount = 7 := by omega
  have hunion :
      (circlePencil S b x ∪ circlePencil S b y).card = 6 := by
    omega
  have hxFan : (circlePencil S b x).card = 4 := by
    omega
  have hyFan : (circlePencil S b y).card = 4 := by
    omega
  have hcommon : (commonPencils S b x y).card = 2 := by
    omega
  have hxPairs : (circleBasePairs S b x).card = 4 := by
    rw [← card_circlePencil S b x]
    exact hxFan
  have hyPairs : (circleBasePairs S b y).card = 4 := by
    rw [← card_circlePencil S b y]
    exact hyFan
  have hxLines : (lineBasePairs S b x).card = 2 := by
    have hpart := card_circleBasePairs_add_card_lineBasePairs S b x
    rw [hbase, hxPairs] at hpart
    norm_num [Nat.choose] at hpart
    omega
  have hyLines : (lineBasePairs S b y).card = 2 := by
    have hpart := card_circleBasePairs_add_card_lineBasePairs S b y
    rw [hbase, hyPairs] at hpart
    norm_num [Nat.choose] at hpart
    omega
  have hexhaust :
      insert b (circlePencil S b x ∪ circlePencil S b y) =
        S.blocksOfKind .circle := by
    apply Finset.eq_of_subset_of_card_le hcircleSubset
    rw [Finset.card_insert_of_notMem hbnotUnion, hunion]
    change S.totalCircleCount ≤ 7
    omega
  exact
    { totalCircleCount_eq := htotal
      xCircleBasePairs_card := hxPairs
      yCircleBasePairs_card := hyPairs
      xLineBasePairs_card := hxLines
      yLineBasePairs_card := hyLines
      commonPencils_card := hcommon
      pencilUnion_card := hunion
      exhaustsCircleBlocks := hexhaust }

/-- On six points a proper line with at least four points would, by its
stronger line-pencil bound, already force ten circle blocks. -/
theorem line_support_card_lt_four_of_six_of_circleCount_le_seven
    (S : BlockSystem Point Block)
    (hPoint : Fintype.card Point = 6)
    (hCircle : S.totalCircleCount ≤ 7)
    (l : Block) (hl : S.kind l = .line)
    (hlProper : (S.support l).card < Fintype.card Point) :
    (S.support l).card < 4 := by
  by_contra hnot
  have hfour : 4 ≤ (S.support l).card := by omega
  have hfive : (S.support l).card ≤ 5 := by omega
  have hpencil := richLinePencilBound_le_totalCircleCount S l hl
  interval_cases hsize : (S.support l).card <;>
    norm_num [hPoint, hsize, Nat.choose] at hpencil hCircle <;>
    omega

/-- The two outsiders of a four-support on a six-point ground set. -/
theorem exists_two_blockOutsiders
    (S : BlockSystem Point Block) (b : Block)
    (hPoint : Fintype.card Point = 6)
    (hbase : (S.support b).card = 4) :
    ∃ x y : BlockOutsider S b, x ≠ y := by
  classical
  have houtCard : (blockOutsiders S b).card = 2 := by
    rw [card_blockOutsiders, hPoint, hbase]
  obtain ⟨x, y, hxy, hout⟩ := Finset.card_eq_two.mp houtCard
  have hx : x ∈ blockOutsiders S b := by rw [hout]; simp
  have hy : y ∈ blockOutsiders S b := by rw [hout]; simp
  have hsubNe : (⟨x, hx⟩ : BlockOutsider S b) ≠ ⟨y, hy⟩ := by
    intro h
    exact hxy (congrArg Subtype.val h)
  exact ⟨⟨x, hx⟩, ⟨y, hy⟩, hsubNe⟩

/-- Existential form of `four_circle_pencil_equality`, convenient before a
labelling of the two outsiders has been chosen. -/
theorem exists_four_circle_pencil_equality
    (S : BlockSystem Point Block) (b : Block)
    (hb : S.kind b = .circle)
    (hPoint : Fintype.card Point = 6)
    (hbase : (S.support b).card = 4)
    (hCircle : S.totalCircleCount ≤ 7) :
    ∃ x y : BlockOutsider S b,
      x ≠ y ∧ FourCirclePencilEqualityData S b x y := by
  obtain ⟨x, y, hxy⟩ := exists_two_blockOutsiders S b hPoint hbase
  exact ⟨x, y, hxy,
    four_circle_pencil_equality S b hb hbase hCircle x y hxy⟩

/-- Base pairs which give the same circle block from both outsider pencils. -/
noncomputable def sharedCircleBasePairs
    (S : BlockSystem Point Block) (b : Block)
    (x y : BlockOutsider S b) : Finset (BlockBasePair S b) := by
  classical
  exact Finset.univ.filter fun u =>
    pencilOwner S b x u = pencilOwner S b y u ∧
      S.kind (pencilOwner S b x u) = .circle

@[simp] theorem mem_sharedCircleBasePairs
    {S : BlockSystem Point Block} {b : Block}
    {x y : BlockOutsider S b} {u : BlockBasePair S b} :
    u ∈ sharedCircleBasePairs S b x y ↔
      pencilOwner S b x u = pencilOwner S b y u ∧
        S.kind (pencilOwner S b x u) = .circle := by
  classical
  simp [sharedCircleBasePairs]

/-- Shared base pairs, mapped through either pencil, are exactly the common
circle blocks of the two pencils. -/
theorem image_sharedCircleBasePairs_eq_commonPencils
    (S : BlockSystem Point Block) (b : Block)
    (x y : BlockOutsider S b) :
    (sharedCircleBasePairs S b x y).image (pencilOwner S b x) =
      commonPencils S b x y := by
  classical
  ext c
  constructor
  · intro hc
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hc
    obtain ⟨howner, hcircle⟩ := mem_sharedCircleBasePairs.mp hu
    rw [commonPencils, Finset.mem_inter]
    constructor
    · exact mem_circlePencil.mpr
        ⟨u, mem_circleBasePairs.mpr hcircle, rfl⟩
    · exact mem_circlePencil.mpr
        ⟨u, mem_circleBasePairs.mpr (by simpa [howner] using hcircle),
          howner.symm⟩
  · intro hc
    rw [commonPencils, Finset.mem_inter] at hc
    obtain ⟨u, hu, huc⟩ := mem_circlePencil.mp hc.1
    obtain ⟨v, hv, hvc⟩ := mem_circlePencil.mp hc.2
    have huvVal : u.1 = v.1 := by
      have hsupports := congrArg
        (fun d => S.support d ∩ S.support b) (huc.trans hvc.symm)
      simpa [pencilOwner_inter_base S b x u,
        pencilOwner_inter_base S b y v] using hsupports
    have huv : u = v := Subtype.ext huvVal
    subst v
    apply Finset.mem_image.mpr
    refine ⟨u, mem_sharedCircleBasePairs.mpr ⟨?_, ?_⟩, huc⟩
    · exact huc.trans hvc.symm
    · exact mem_circleBasePairs.mp hu

theorem card_sharedCircleBasePairs
    (S : BlockSystem Point Block) (b : Block)
    (x y : BlockOutsider S b) :
    (sharedCircleBasePairs S b x y).card =
      (commonPencils S b x y).card := by
  classical
  rw [← image_sharedCircleBasePairs_eq_commonPencils S b x y,
    Finset.card_image_of_injective _ (pencilOwner_injective S b x)]

/-- The underlying two-subsets of the shared circle pairs. -/
noncomputable def sharedCircleBasePairValues
    (S : BlockSystem Point Block) (b : Block)
    (x y : BlockOutsider S b) : Finset (Finset Point) := by
  classical
  exact (sharedCircleBasePairs S b x y).image Subtype.val

theorem card_sharedCircleBasePairValues
    (S : BlockSystem Point Block) (b : Block)
    (x y : BlockOutsider S b) :
    (sharedCircleBasePairValues S b x y).card =
      (sharedCircleBasePairs S b x y).card := by
  classical
  rw [sharedCircleBasePairValues,
    Finset.card_image_of_injective _ Subtype.val_injective]

/-- The two descriptions of a common-pencil base pair agree: one starts
with a shared pair, the other starts with the common circle block. -/
theorem sharedCircleBasePairValues_eq_commonPencilBasePairs
    (S : BlockSystem Point Block) (b : Block)
    (x y : BlockOutsider S b) :
    sharedCircleBasePairValues S b x y =
      commonPencilBasePairs S b x y := by
  classical
  ext p
  constructor
  · intro hp
    rw [sharedCircleBasePairValues] at hp
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨howner, hcircle⟩ := mem_sharedCircleBasePairs.mp hu
    have hcCommon : pencilOwner S b x u ∈ commonPencils S b x y := by
      rw [commonPencils, Finset.mem_inter]
      exact
        ⟨mem_circlePencil.mpr
            ⟨u, mem_circleBasePairs.mpr hcircle, rfl⟩,
          mem_circlePencil.mpr
            ⟨u, mem_circleBasePairs.mpr (by simpa [howner] using hcircle),
              howner.symm⟩⟩
    let c : CommonPencilBlock S b x y :=
      ⟨pencilOwner S b x u, hcCommon⟩
    rw [commonPencilBasePairs]
    apply Finset.mem_image.mpr
    refine ⟨c, Finset.mem_univ c, ?_⟩
    change S.support (pencilOwner S b x u) ∩ S.support b = u.1
    exact pencilOwner_inter_base S b x u
  · intro hp
    rw [commonPencilBasePairs] at hp
    obtain ⟨c, _hc, hcp⟩ := Finset.mem_image.mp hp
    have hcxy := Finset.mem_inter.mp c.2
    obtain ⟨u, hu, huc⟩ := mem_circlePencil.mp hcxy.1
    obtain ⟨v, _hv, hvc⟩ := mem_circlePencil.mp hcxy.2
    have huvVal : u.1 = v.1 := by
      have hsupports := congrArg
        (fun d => S.support d ∩ S.support b) (huc.trans hvc.symm)
      simpa [pencilOwner_inter_base S b x u,
        pencilOwner_inter_base S b y v] using hsupports
    have huv : u = v := Subtype.ext huvVal
    subst v
    have huShared : u ∈ sharedCircleBasePairs S b x y := by
      apply mem_sharedCircleBasePairs.mpr
      exact ⟨huc.trans hvc.symm, mem_circleBasePairs.mp hu⟩
    rw [sharedCircleBasePairValues]
    apply Finset.mem_image.mpr
    refine ⟨u, huShared, ?_⟩
    rw [← hcp]
    change u.1 = S.support c.1 ∩ S.support b
    rw [← huc, pencilOwner_inter_base S b x u]

theorem sharedCircleBasePairValues_pairwiseDisjoint
    (S : BlockSystem Point Block) (b : Block)
    (x y : BlockOutsider S b) (hxy : x ≠ y) :
    ((sharedCircleBasePairValues S b x y : Finset (Finset Point)) :
      Set (Finset Point)).PairwiseDisjoint id := by
  rw [sharedCircleBasePairValues_eq_commonPencilBasePairs]
  exact commonPencilBasePairs_pairwiseDisjoint S b x y hxy

/-- With no line on four points, a base pair cannot be line-owned from both
outsiders. -/
theorem lineBasePairs_disjoint_of_line_support_lt_four
    (S : BlockSystem Point Block) (b : Block)
    (x y : BlockOutsider S b) (hxy : x ≠ y)
    (hlineSmall : ∀ l, S.kind l = .line → (S.support l).card < 4) :
    Disjoint (lineBasePairs S b x) (lineBasePairs S b y) := by
  classical
  rw [Finset.disjoint_left]
  intro u hux huy
  have hxLine : S.kind (pencilOwner S b x u) = .line :=
    mem_lineBasePairs.mp hux
  have hyLine : S.kind (pencilOwner S b y u) = .line :=
    mem_lineBasePairs.mp huy
  have howners : pencilOwner S b x u = pencilOwner S b y u := by
    by_contra hne
    let lx : LineBlock S := ⟨pencilOwner S b x u, hxLine⟩
    let ly : LineBlock S := ⟨pencilOwner S b y u, hyLine⟩
    have hlxy : lx ≠ ly := by
      intro h
      exact hne (congrArg Subtype.val h)
    have hinter := S.distinct_line_inter_card_lt_two hlxy
    change (S.support (pencilOwner S b x u) ∩
      S.support (pencilOwner S b y u)).card < 2 at hinter
    have hupair : u.1 ⊆
        S.support (pencilOwner S b x u) ∩
          S.support (pencilOwner S b y u) := by
      intro z hz
      exact Finset.mem_inter.mpr
        ⟨pencilOwner_contains_pair S b x u hz,
          pencilOwner_contains_pair S b y u hz⟩
    have hle := Finset.card_le_card hupair
    have hucard := (Finset.mem_powersetCard.mp u.2).2
    omega
  have hxnotU : x.1 ∉ u.1 := by
    intro hx
    exact (mem_blockOutsiders.mp x.2)
      ((Finset.mem_powersetCard.mp u.2).1 hx)
  have hynotU : y.1 ∉ u.1 := by
    intro hy
    exact (mem_blockOutsiders.mp y.2)
      ((Finset.mem_powersetCard.mp u.2).1 hy)
  have hxyVal : x.1 ≠ y.1 := Subtype.coe_injective.ne hxy
  let q : Finset Point := insert x.1 (insert y.1 u.1)
  have hqcard : q.card = 4 := by
    dsimp only [q]
    rw [Finset.card_insert_of_notMem (by simp [hxyVal, hxnotU]),
      Finset.card_insert_of_notMem hynotU,
      (Finset.mem_powersetCard.mp u.2).2]
  have hqsub : q ⊆ S.support (pencilOwner S b x u) := by
    intro z hz
    simp only [q, Finset.mem_insert] at hz
    rcases hz with rfl | rfl | hz
    · exact pencilOwner_contains_outsider S b x u
    · rw [howners]
      exact pencilOwner_contains_outsider S b y u
    · exact pencilOwner_contains_pair S b x u hz
  have hqle := Finset.card_le_card hqsub
  have := hlineSmall (pencilOwner S b x u) hxLine
  omega

/-- A shared circle pair is never a line pair in either pencil. -/
theorem lineBasePairs_disjoint_sharedCircleBasePairs_left
    (S : BlockSystem Point Block) (b : Block)
    (x y : BlockOutsider S b) :
    Disjoint (lineBasePairs S b x) (sharedCircleBasePairs S b x y) := by
  classical
  rw [Finset.disjoint_left]
  intro u huLine huShared
  have hline := mem_lineBasePairs.mp huLine
  have hcircle := (mem_sharedCircleBasePairs.mp huShared).2
  rw [hline] at hcircle
  cases hcircle

theorem lineBasePairs_disjoint_sharedCircleBasePairs_right
    (S : BlockSystem Point Block) (b : Block)
    (x y : BlockOutsider S b) :
    Disjoint (lineBasePairs S b y) (sharedCircleBasePairs S b x y) := by
  classical
  rw [Finset.disjoint_left]
  intro u huLine huShared
  have hline := mem_lineBasePairs.mp huLine
  obtain ⟨howner, hcircle⟩ := mem_sharedCircleBasePairs.mp huShared
  have hcircleY : S.kind (pencilOwner S b y u) = .circle := by
    simpa [howner] using hcircle
  rw [hline] at hcircleY
  cases hcircleY

/-- The equality face is a partition of the six base pairs into three
two-element classes: the line matching at `x`, the line matching at `y`, and
the shared-circle matching.  This is the abstract one-factorization core of
the labelled Pasch pattern. -/
theorem basePairs_partition_three_matchings
    (S : BlockSystem Point Block) (b : Block)
    (hbase : (S.support b).card = 4)
    (x y : BlockOutsider S b) (hxy : x ≠ y)
    (heq : FourCirclePencilEqualityData S b x y)
    (hlineSmall : ∀ l, S.kind l = .line → (S.support l).card < 4) :
    lineBasePairs S b x ∪ lineBasePairs S b y ∪
        sharedCircleBasePairs S b x y = Finset.univ := by
  classical
  have hxyDisj := lineBasePairs_disjoint_of_line_support_lt_four
    S b x y hxy hlineSmall
  have hxShared := lineBasePairs_disjoint_sharedCircleBasePairs_left
    S b x y
  have hyShared := lineBasePairs_disjoint_sharedCircleBasePairs_right
    S b x y
  have hUnionShared :
      Disjoint (lineBasePairs S b x ∪ lineBasePairs S b y)
        (sharedCircleBasePairs S b x y) := by
    rw [Finset.disjoint_union_left]
    exact ⟨hxShared, hyShared⟩
  apply Finset.eq_univ_of_card
  rw [Finset.card_union_of_disjoint hUnionShared,
    Finset.card_union_of_disjoint hxyDisj,
    heq.xLineBasePairs_card, heq.yLineBasePairs_card,
    card_sharedCircleBasePairs, heq.commonPencils_card]
  change 6 = Fintype.card (BlockBasePair S b)
  have hcardBase : Fintype.card (BlockBasePair S b) = 6 := by
    calc
      Fintype.card (BlockBasePair S b) =
          ((S.support b).powersetCard 2).card :=
        Fintype.card_coe _
      _ = Nat.choose (S.support b).card 2 := by simp
      _ = 6 := by rw [hbase]; norm_num [Nat.choose]
  omega

/-- A pointwise presentation of the abstract Pasch one-factorization.  The
indices in the field names anticipate the final six-point labelling: the
outsiders will become labels `2` and `3`. -/
structure PaschPencilLabels
    (S : BlockSystem Point Block) (b : Block)
    (x y : BlockOutsider S b) where
  p0 : Point
  p1 : Point
  p4 : Point
  p5 : Point
  p0_ne_p1 : p0 ≠ p1
  p0_ne_p4 : p0 ≠ p4
  p0_ne_p5 : p0 ≠ p5
  p1_ne_p4 : p1 ≠ p4
  p1_ne_p5 : p1 ≠ p5
  p4_ne_p5 : p4 ≠ p5
  baseSupport_eq : S.support b = {p0, p1, p4, p5}
  baseLabels_card : ({p0, p1, p4, p5} : Finset Point).card = 4
  xPair01 : {p0, p1} ∈ lineBasePairValues S b x
  xPair45 : {p4, p5} ∈ lineBasePairValues S b x
  yPair04 : {p0, p4} ∈ lineBasePairValues S b y
  yPair15 : {p1, p5} ∈ lineBasePairValues S b y
  sharedPair05 : {p0, p5} ∈ sharedCircleBasePairValues S b x y
  sharedPair14 : {p1, p4} ∈ sharedCircleBasePairValues S b x y

private theorem conflict_of_pairwiseDisjoint_pair_values
    {S : BlockSystem Point Block} {b : Block}
    (F : Finset (BlockBasePair S b))
    (hmatch : (((F.image Subtype.val : Finset (Finset Point)) :
      Set (Finset Point))).PairwiseDisjoint id)
    {u v : BlockBasePair S b} (hu : u ∈ F) (hv : v ∈ F)
    (huv : u ≠ v) {z : Point} (hzu : z ∈ u.1) (hzv : z ∈ v.1) :
    False := by
  classical
  have huVal : u.1 ∈ F.image Subtype.val :=
    Finset.mem_image.mpr ⟨u, hu, rfl⟩
  have hvVal : v.1 ∈ F.image Subtype.val :=
    Finset.mem_image.mpr ⟨v, hv, rfl⟩
  have huvVal : u.1 ≠ v.1 := by
    intro h
    exact huv (Subtype.ext h)
  have hdisj := hmatch huVal hvVal huvVal
  exact Finset.disjoint_left.mp hdisj hzu hzv

/-- The three matching classes on the equality face have the canonical
Pasch labelling. -/
theorem exists_paschPencilLabels
    (S : BlockSystem Point Block) (b : Block)
    (hbase : (S.support b).card = 4)
    (x y : BlockOutsider S b) (hxy : x ≠ y)
    (heq : FourCirclePencilEqualityData S b x y)
    (hlineSmall : ∀ l, S.kind l = .line → (S.support l).card < 4) :
    Nonempty (PaschPencilLabels S b x y) := by
  classical
  let X := lineBasePairs S b x
  let Y := lineBasePairs S b y
  let Z := sharedCircleBasePairs S b x y
  have hXcard : X.card = 2 := heq.xLineBasePairs_card
  obtain ⟨u, v, huv, hX⟩ := Finset.card_eq_two.mp hXcard
  have huX : u ∈ X := by rw [hX]; simp
  have hvX : v ∈ X := by rw [hX]; simp
  have hXmatch :
      (((X.image Subtype.val : Finset (Finset Point)) :
        Set (Finset Point))).PairwiseDisjoint id := by
    simpa [X, lineBasePairValues] using
      lineBasePairValues_pairwiseDisjoint_of_base_circle S b
        (by
          have huLine := mem_lineBasePairs.mp (show u ∈ lineBasePairs S b x from huX)
          cases hb : S.kind b with
          | circle => rfl
          | line =>
              have hownerCircle : S.kind (pencilOwner S b x u) = .circle :=
                pencilOwner_kind_circle_of_base_line S b hb x u
              rw [huLine] at hownerCircle
              cases hownerCircle)
        x
  have huvDisj : Disjoint u.1 v.1 := by
    have huVal : u.1 ∈ X.image Subtype.val :=
      Finset.mem_image.mpr ⟨u, huX, rfl⟩
    have hvVal : v.1 ∈ X.image Subtype.val :=
      Finset.mem_image.mpr ⟨v, hvX, rfl⟩
    exact hXmatch huVal hvVal (Subtype.val_injective.ne huv)
  have huCard : u.1.card = 2 := (Finset.mem_powersetCard.mp u.2).2
  have hvCard : v.1.card = 2 := (Finset.mem_powersetCard.mp v.2).2
  obtain ⟨a, b₁, hab, hu⟩ := Finset.card_eq_two.mp huCard
  obtain ⟨c, d, hcd, hv⟩ := Finset.card_eq_two.mp hvCard
  have hac : a ≠ c := by
    intro h
    subst c
    have haU : a ∈ u.1 := by rw [hu]; simp
    have haV : a ∈ v.1 := by rw [hv]; simp
    exact (Finset.disjoint_left.mp huvDisj) haU haV
  have had : a ≠ d := by
    intro h
    subst d
    have haU : a ∈ u.1 := by rw [hu]; simp
    have haV : a ∈ v.1 := by rw [hv]; simp
    exact (Finset.disjoint_left.mp huvDisj) haU haV
  have hbc : b₁ ≠ c := by
    intro h
    subst c
    have hbU : b₁ ∈ u.1 := by rw [hu]; simp
    have hbV : b₁ ∈ v.1 := by rw [hv]; simp
    exact (Finset.disjoint_left.mp huvDisj) hbU hbV
  have hbd : b₁ ≠ d := by
    intro h
    subst d
    have hbU : b₁ ∈ u.1 := by rw [hu]; simp
    have hbV : b₁ ∈ v.1 := by rw [hv]; simp
    exact (Finset.disjoint_left.mp huvDisj) hbU hbV
  have hbaseEq : S.support b = {a, b₁, c, d} := by
    have huvSub : u.1 ∪ v.1 ⊆ S.support b := by
      intro z hz
      rcases Finset.mem_union.mp hz with hzu | hzv
      · exact (Finset.mem_powersetCard.mp u.2).1 hzu
      · exact (Finset.mem_powersetCard.mp v.2).1 hzv
    have huvCard : (u.1 ∪ v.1).card = 4 := by
      rw [Finset.card_union_of_disjoint huvDisj, huCard, hvCard]
    have huvEq : u.1 ∪ v.1 = S.support b := by
      apply Finset.eq_of_subset_of_card_le huvSub
      omega
    rw [← huvEq, hu, hv]
    ext z
    simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_union]
    aesop
  have hlabelsCard : ({a, b₁, c, d} : Finset Point).card = 4 := by
    rw [← hbaseEq]
    exact hbase
  let pac : BlockBasePair S b := ⟨{a, c}, by
    apply Finset.mem_powersetCard.mpr
    constructor
    · rw [hbaseEq]
      intro z hz
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz ⊢
      aesop
    · simp [hac]⟩
  let pad : BlockBasePair S b := ⟨{a, d}, by
    apply Finset.mem_powersetCard.mpr
    constructor
    · rw [hbaseEq]
      intro z hz
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz ⊢
      aesop
    · simp [had]⟩
  let pbc : BlockBasePair S b := ⟨{b₁, c}, by
    apply Finset.mem_powersetCard.mpr
    constructor
    · rw [hbaseEq]
      intro z hz
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz ⊢
      aesop
    · simp [hbc]⟩
  let pbd : BlockBasePair S b := ⟨{b₁, d}, by
    apply Finset.mem_powersetCard.mpr
    constructor
    · rw [hbaseEq]
      intro z hz
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz ⊢
      aesop
    · simp [hbd]⟩
  have crossNotX (q : BlockBasePair S b)
      (hqU : ∃ z ∈ q.1, z ∈ u.1)
      (hqV : ∃ z ∈ q.1, z ∈ v.1) : q ∉ X := by
    intro hq
    rw [hX] at hq
    rcases Finset.mem_insert.mp hq with hqu | hqv
    · have hqEq : q = u := hqu
      obtain ⟨z, hzq, hzv⟩ := hqV
      have hzu : z ∈ u.1 := by simpa [hqEq] using hzq
      exact Finset.disjoint_left.mp huvDisj hzu hzv
    · have hqEq : q = v := Finset.mem_singleton.mp hqv
      obtain ⟨z, hzq, hzu⟩ := hqU
      have hzv : z ∈ v.1 := by simpa [hqEq] using hzq
      exact Finset.disjoint_left.mp huvDisj hzu hzv
  have hacNotX : pac ∉ X := crossNotX pac
    ⟨a, by simp [pac], by simp [hu]⟩
    ⟨c, by simp [pac], by simp [hv]⟩
  have hadNotX : pad ∉ X := crossNotX pad
    ⟨a, by simp [pad], by simp [hu]⟩
    ⟨d, by simp [pad], by simp [hv]⟩
  have hbcNotX : pbc ∉ X := crossNotX pbc
    ⟨b₁, by simp [pbc], by simp [hu]⟩
    ⟨c, by simp [pbc], by simp [hv]⟩
  have hbdNotX : pbd ∉ X := crossNotX pbd
    ⟨b₁, by simp [pbd], by simp [hu]⟩
    ⟨d, by simp [pbd], by simp [hv]⟩
  have hpartition : X ∪ Y ∪ Z = Finset.univ := by
    simpa [X, Y, Z] using basePairs_partition_three_matchings
      S b hbase x y hxy heq hlineSmall
  have inYorZ (q : BlockBasePair S b) (hqX : q ∉ X) : q ∈ Y ∨ q ∈ Z := by
    have hqAll : q ∈ X ∪ Y ∪ Z := by rw [hpartition]; simp
    simp only [Finset.mem_union] at hqAll
    rcases hqAll with (hq | hq) | hq
    · exact (hqX hq).elim
    · exact Or.inl hq
    · exact Or.inr hq
  have hYmatch :
      (((Y.image Subtype.val : Finset (Finset Point)) :
        Set (Finset Point))).PairwiseDisjoint id := by
    simpa [Y, lineBasePairValues] using
      lineBasePairValues_pairwiseDisjoint_of_base_circle S b
        (by
          have huLine := mem_lineBasePairs.mp (show u ∈ lineBasePairs S b x from huX)
          cases hb : S.kind b with
          | circle => rfl
          | line =>
              have hownerCircle : S.kind (pencilOwner S b x u) = .circle :=
                pencilOwner_kind_circle_of_base_line S b hb x u
              rw [huLine] at hownerCircle
              cases hownerCircle)
        y
  have hZmatch :
      (((Z.image Subtype.val : Finset (Finset Point)) :
        Set (Finset Point))).PairwiseDisjoint id := by
    simpa [Z, sharedCircleBasePairValues] using
      sharedCircleBasePairValues_pairwiseDisjoint S b x y hxy
  have pac_ne_pad : pac ≠ pad := by
    intro h
    have hcMem : c ∈ pad.1 := by
      rw [← congrArg Subtype.val h]
      simp [pac]
    simp [pad, hac.symm, hcd] at hcMem
  have pac_ne_pbc : pac ≠ pbc := by
    intro h
    have haMem : a ∈ pbc.1 := by
      rw [← congrArg Subtype.val h]
      simp [pac]
    simp [pbc, hab, hac] at haMem
  have pad_ne_pbd : pad ≠ pbd := by
    intro h
    have haMem : a ∈ pbd.1 := by
      rw [← congrArg Subtype.val h]
      simp [pad]
    simp [pbd, hab, had] at haMem
  by_cases hacY : pac ∈ Y
  · have hadZ : pad ∈ Z := by
      rcases inYorZ pad hadNotX with hadY | hadZ
      · exact (conflict_of_pairwiseDisjoint_pair_values Y hYmatch (z := a)
          hacY hadY pac_ne_pad (by simp [pac]) (by simp [pad])).elim
      · exact hadZ
    have hbcZ : pbc ∈ Z := by
      rcases inYorZ pbc hbcNotX with hbcY | hbcZ
      · exact (conflict_of_pairwiseDisjoint_pair_values Y hYmatch (z := c)
          hacY hbcY pac_ne_pbc (by simp [pac]) (by simp [pbc])).elim
      · exact hbcZ
    have hbdY : pbd ∈ Y := by
      rcases inYorZ pbd hbdNotX with hbdY | hbdZ
      · exact hbdY
      · exact (conflict_of_pairwiseDisjoint_pair_values Z hZmatch (z := d)
          hadZ hbdZ pad_ne_pbd (by simp [pad]) (by simp [pbd])).elim
    refine ⟨{
      p0 := a, p1 := b₁, p4 := c, p5 := d
      p0_ne_p1 := hab
      p0_ne_p4 := hac
      p0_ne_p5 := had
      p1_ne_p4 := hbc
      p1_ne_p5 := hbd
      p4_ne_p5 := hcd
      baseSupport_eq := hbaseEq
      baseLabels_card := hlabelsCard
      xPair01 := by
        rw [lineBasePairValues]
        exact Finset.mem_image.mpr ⟨u, huX, hu⟩
      xPair45 := by
        rw [lineBasePairValues]
        exact Finset.mem_image.mpr ⟨v, hvX, hv⟩
      yPair04 := by rw [lineBasePairValues]; exact Finset.mem_image.mpr ⟨pac, hacY, rfl⟩
      yPair15 := by rw [lineBasePairValues]; exact Finset.mem_image.mpr ⟨pbd, hbdY, rfl⟩
      sharedPair05 := by rw [sharedCircleBasePairValues]; exact Finset.mem_image.mpr ⟨pad, hadZ, rfl⟩
      sharedPair14 := by rw [sharedCircleBasePairValues]; exact Finset.mem_image.mpr ⟨pbc, hbcZ, rfl⟩ }⟩
  · have hacZ : pac ∈ Z := (inYorZ pac hacNotX).resolve_left hacY
    have hadY : pad ∈ Y := by
      rcases inYorZ pad hadNotX with hadY | hadZ
      · exact hadY
      · exact (conflict_of_pairwiseDisjoint_pair_values Z hZmatch (z := a)
          hacZ hadZ pac_ne_pad (by simp [pac]) (by simp [pad])).elim
    have hbcY : pbc ∈ Y := by
      rcases inYorZ pbc hbcNotX with hbcY | hbcZ
      · exact hbcY
      · exact (conflict_of_pairwiseDisjoint_pair_values Z hZmatch (z := c)
          hacZ hbcZ pac_ne_pbc (by simp [pac]) (by simp [pbc])).elim
    have hbdZ : pbd ∈ Z := by
      rcases inYorZ pbd hbdNotX with hbdY | hbdZ
      · exact (conflict_of_pairwiseDisjoint_pair_values Y hYmatch (z := d)
          hadY hbdY pad_ne_pbd (by simp [pad]) (by simp [pbd])).elim
      · exact hbdZ
    have hbaseSwap : S.support b = {a, b₁, d, c} := by
      simpa only [Finset.pair_comm c d] using hbaseEq
    have hcardSwap : ({a, b₁, d, c} : Finset Point).card = 4 := by
      rw [← hbaseSwap]
      exact hbase
    have hx01 : {a, b₁} ∈ lineBasePairValues S b x := by
      rw [lineBasePairValues]
      exact Finset.mem_image.mpr ⟨u, huX, hu⟩
    have hx54 : {d, c} ∈ lineBasePairValues S b x := by
      rw [lineBasePairValues]
      apply Finset.mem_image.mpr
      refine ⟨v, hvX, ?_⟩
      simpa only [Finset.pair_comm c d] using hv
    have hy0d : {a, d} ∈ lineBasePairValues S b y := by
      rw [lineBasePairValues]
      exact Finset.mem_image.mpr ⟨pad, hadY, rfl⟩
    have hy1c : {b₁, c} ∈ lineBasePairValues S b y := by
      rw [lineBasePairValues]
      exact Finset.mem_image.mpr ⟨pbc, hbcY, rfl⟩
    have hz0c : {a, c} ∈ sharedCircleBasePairValues S b x y := by
      rw [sharedCircleBasePairValues]
      exact Finset.mem_image.mpr ⟨pac, hacZ, rfl⟩
    have hz1d : {b₁, d} ∈ sharedCircleBasePairValues S b x y := by
      rw [sharedCircleBasePairValues]
      exact Finset.mem_image.mpr ⟨pbd, hbdZ, rfl⟩
    refine ⟨{
      p0 := a, p1 := b₁, p4 := d, p5 := c
      p0_ne_p1 := hab
      p0_ne_p4 := had
      p0_ne_p5 := hac
      p1_ne_p4 := hbd
      p1_ne_p5 := hbc
      p4_ne_p5 := hcd.symm
      baseSupport_eq := hbaseSwap
      baseLabels_card := hcardSwap
      xPair01 := hx01
      xPair45 := hx54
      yPair04 := hy0d
      yPair15 := hy1c
      sharedPair05 := hz0c
      sharedPair14 := hz1d }⟩

/-- The six labels associated to a Pasch pencil: the two outsiders occupy
positions `2` and `3`. -/
def paschPointLabel
    {S : BlockSystem Point Block} {b : Block}
    {x y : BlockOutsider S b} (L : PaschPencilLabels S b x y) :
    Fin 6 → Point :=
  ![L.p0, L.p1, x.1, y.1, L.p4, L.p5]

theorem paschPointLabel_injective
    {S : BlockSystem Point Block} {b : Block}
    {x y : BlockOutsider S b} (hxy : x ≠ y)
    (L : PaschPencilLabels S b x y) :
    Function.Injective (paschPointLabel L) := by
  have hx0 : x.1 ≠ L.p0 := by
    intro h
    apply mem_blockOutsiders.mp x.2
    rw [h, L.baseSupport_eq]
    simp
  have hx1 : x.1 ≠ L.p1 := by
    intro h
    apply mem_blockOutsiders.mp x.2
    rw [h, L.baseSupport_eq]
    simp
  have hx4 : x.1 ≠ L.p4 := by
    intro h
    apply mem_blockOutsiders.mp x.2
    rw [h, L.baseSupport_eq]
    simp
  have hx5 : x.1 ≠ L.p5 := by
    intro h
    apply mem_blockOutsiders.mp x.2
    rw [h, L.baseSupport_eq]
    simp
  have hy0 : y.1 ≠ L.p0 := by
    intro h
    apply mem_blockOutsiders.mp y.2
    rw [h, L.baseSupport_eq]
    simp
  have hy1 : y.1 ≠ L.p1 := by
    intro h
    apply mem_blockOutsiders.mp y.2
    rw [h, L.baseSupport_eq]
    simp
  have hy4 : y.1 ≠ L.p4 := by
    intro h
    apply mem_blockOutsiders.mp y.2
    rw [h, L.baseSupport_eq]
    simp
  have hy5 : y.1 ≠ L.p5 := by
    intro h
    apply mem_blockOutsiders.mp y.2
    rw [h, L.baseSupport_eq]
    simp
  have hxyVal : x.1 ≠ y.1 := Subtype.coe_injective.ne hxy
  have h01 := L.p0_ne_p1
  have h04 := L.p0_ne_p4
  have h05 := L.p0_ne_p5
  have h14 := L.p1_ne_p4
  have h15 := L.p1_ne_p5
  have h45 := L.p4_ne_p5
  intro i j hij
  fin_cases i <;> fin_cases j <;>
    simp_all [paschPointLabel]

/-- A line-owned base pair places the outsider on the affine line through
the two displayed base points. -/
theorem outsider_mem_affineSpan_of_mem_lineBasePairValues
    {α : Type*} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (b : GeometricBlock cfg)
    (x : BlockOutsider (blockSystem cfg) b)
    {a d : α} (had : a ≠ d)
    (hp : {a, d} ∈ lineBasePairValues (blockSystem cfg) b x) :
    cfg x.1 ∈ affineSpan ℝ ({cfg a, cfg d} : Set Point2) := by
  classical
  rw [lineBasePairValues] at hp
  obtain ⟨u, huLine, hu⟩ := Finset.mem_image.mp hp
  have hkind :
      geometricBlockKind (pencilOwner (blockSystem cfg) b x u) = .line :=
    mem_lineBasePairs.mp huLine
  cases howner : pencilOwner (blockSystem cfg) b x u with
  | inr c =>
      rw [howner] at hkind
      cases hkind
  | inl l =>
      have hxSupport := pencilOwner_contains_outsider
        (blockSystem cfg) b x u
      rw [howner] at hxSupport
      change x.1 ∈ lineSupport cfg l at hxSupport
      have hxLine : cfg x.1 ∈ l.1 := mem_lineSupport.mp hxSupport
      let A : KSubset α 2 := ⟨{a, d}, by simp [had]⟩
      have hmem : ∀ z ∈ A.1, cfg z ∈ l.1 := by
        intro z hz
        apply mem_lineSupport.mp
        have hzSupport := pencilOwner_contains_pair (blockSystem cfg) b x u (by
          rw [hu]
          exact hz)
        rw [howner] at hzSupport
        exact hzSupport
      have hlineEq : lineOfPair cfg A = l.1 :=
        lineOfPair_eq_of_mem_of_direction_finrank_one cfg A l.1 hmem
          l.direction_finrank
      have hpairEq : lineOfPair cfg A =
          affineSpan ℝ ({cfg a, cfg d} : Set Point2) := by
        simpa [A] using lineOfPair_pair cfg had
      rw [← hpairEq, hlineEq]
      exact hxLine

/-- A shared pair supplies one proper circle containing that pair and both
outsiders. -/
theorem exists_circle_through_sharedCircleBasePairValue
    {α : Type*} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (b : GeometricBlock cfg)
    (x y : BlockOutsider (blockSystem cfg) b)
    {a d : α}
    (hp : {a, d} ∈ sharedCircleBasePairValues (blockSystem cfg) b x y) :
    ∃ c : ProperCircle,
      cfg a ∈ (c.1 : Set Point2) ∧ cfg d ∈ (c.1 : Set Point2) ∧
      cfg x.1 ∈ (c.1 : Set Point2) ∧ cfg y.1 ∈ (c.1 : Set Point2) := by
  classical
  rw [sharedCircleBasePairValues] at hp
  obtain ⟨u, huShared, hu⟩ := Finset.mem_image.mp hp
  obtain ⟨howners, hcircle⟩ := mem_sharedCircleBasePairs.mp huShared
  cases howner : pencilOwner (blockSystem cfg) b x u with
  | inl l =>
      rw [howner] at hcircle
      cases hcircle
  | inr c =>
      refine ⟨c.1, ?_, ?_, ?_, ?_⟩
      · have haTrace := pencilOwner_contains_pair
          (blockSystem cfg) b x u (by rw [hu]; simp : a ∈ u.1)
        rw [howner] at haTrace
        exact mem_circleTrace.mp haTrace
      · have hdTrace := pencilOwner_contains_pair
          (blockSystem cfg) b x u (by rw [hu]; simp : d ∈ u.1)
        rw [howner] at hdTrace
        exact mem_circleTrace.mp hdTrace
      · have hxTrace := pencilOwner_contains_outsider
          (blockSystem cfg) b x u
        rw [howner] at hxTrace
        exact mem_circleTrace.mp hxTrace
      · have hyTrace := pencilOwner_contains_outsider
          (blockSystem cfg) b y u
        have hownerY : pencilOwner (blockSystem cfg) b y u = Sum.inr c :=
          howners.symm.trans howner
        rw [hownerY] at hyTrace
        exact mem_circleTrace.mp hyTrace

theorem exists_circle_of_geometricBlock_kind_circle
    {α : Type*} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (b : GeometricBlock cfg)
    (hb : geometricBlockKind b = .circle) :
    ∃ c : ProperCircle, ∀ z ∈ geometricBlockSupport cfg b,
      cfg z ∈ (c.1 : Set Point2) := by
  cases b with
  | inl l => cases hb
  | inr c =>
      refine ⟨c.1, ?_⟩
      intro z hz
      exact mem_circleTrace.mp hz

/-- The abstract Pasch labels on a geometric block system contradict the
similarity-safe terminal obstruction from `SmallSix`. -/
theorem no_geometric_paschPencilLabels
    {α : Type*} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (b : GeometricBlock cfg)
    (hb : geometricBlockKind b = .circle)
    (x y : BlockOutsider (blockSystem cfg) b) (hxy : x ≠ y)
    (L : PaschPencilLabels (blockSystem cfg) b x y)
    (hlineSmall : ∀ l : GeometricBlock cfg,
      geometricBlockKind l = .line →
        (geometricBlockSupport cfg l).card < 4) : False := by
  classical
  let q : Fin 6 → α := paschPointLabel L
  let p : Fin 6 → Point2 := fun i => cfg (q i)
  have hqInj : Function.Injective q := paschPointLabel_injective hxy L
  have hpInj : Function.Injective p := cfg.injective.comp hqInj
  have hx01 := outsider_mem_affineSpan_of_mem_lineBasePairValues
    cfg b x L.p0_ne_p1 L.xPair01
  have hy04 := outsider_mem_affineSpan_of_mem_lineBasePairValues
    cfg b y L.p0_ne_p4 L.yPair04
  have hy15 := outsider_mem_affineSpan_of_mem_lineBasePairValues
    cfg b y L.p1_ne_p5 L.yPair15
  have hx45 := outsider_mem_affineSpan_of_mem_lineBasePairValues
    cfg b x L.p4_ne_p5 L.xPair45
  have hline₂ : p 2 ∈ affineSpan ℝ ({p 0, p 1} : Set Point2) := by
    simpa [p, q, paschPointLabel] using hx01
  have hline₄ : p 4 ∈ affineSpan ℝ ({p 0, p 3} : Set Point2) := by
    have hspan : affineSpan ℝ ({cfg L.p0, cfg y.1} : Set Point2) =
        affineSpan ℝ ({cfg L.p0, cfg L.p4} : Set Point2) :=
      affineSpan_pair_eq_of_mem_of_mem
        (subset_affineSpan ℝ ({cfg L.p0, cfg L.p4} : Set Point2) (by simp)) hy04
        (cfg.injective.ne (by
          intro h
          apply mem_blockOutsiders.mp y.2
          rw [← h, L.baseSupport_eq]
          simp))
        (cfg.injective.ne L.p0_ne_p4)
    change cfg L.p4 ∈ affineSpan ℝ ({cfg L.p0, cfg y.1} : Set Point2)
    rw [hspan]
    exact subset_affineSpan ℝ ({cfg L.p0, cfg L.p4} : Set Point2) (by simp)
  have hline₅₁₃ : p 5 ∈ affineSpan ℝ ({p 1, p 3} : Set Point2) := by
    have hspan : affineSpan ℝ ({cfg L.p1, cfg y.1} : Set Point2) =
        affineSpan ℝ ({cfg L.p1, cfg L.p5} : Set Point2) :=
      affineSpan_pair_eq_of_mem_of_mem
        (subset_affineSpan ℝ ({cfg L.p1, cfg L.p5} : Set Point2) (by simp)) hy15
        (cfg.injective.ne (by
          intro h
          apply mem_blockOutsiders.mp y.2
          rw [← h, L.baseSupport_eq]
          simp))
        (cfg.injective.ne L.p1_ne_p5)
    change cfg L.p5 ∈ affineSpan ℝ ({cfg L.p1, cfg y.1} : Set Point2)
    rw [hspan]
    exact subset_affineSpan ℝ ({cfg L.p1, cfg L.p5} : Set Point2) (by simp)
  have hline₅₂₄ : p 5 ∈ affineSpan ℝ ({p 2, p 4} : Set Point2) := by
    have hspan : affineSpan ℝ ({cfg x.1, cfg L.p4} : Set Point2) =
        affineSpan ℝ ({cfg L.p4, cfg L.p5} : Set Point2) :=
      affineSpan_pair_eq_of_mem_of_mem hx45
        (subset_affineSpan ℝ ({cfg L.p4, cfg L.p5} : Set Point2) (by simp))
        (cfg.injective.ne (by
          intro h
          apply mem_blockOutsiders.mp x.2
          rw [h, L.baseSupport_eq]
          simp))
        (cfg.injective.ne L.p4_ne_p5)
    change cfg L.p5 ∈ affineSpan ℝ ({cfg x.1, cfg L.p4} : Set Point2)
    rw [hspan]
    exact subset_affineSpan ℝ ({cfg L.p4, cfg L.p5} : Set Point2) (by simp)
  have hdet : det2 (p 1 - p 0) (p 3 - p 0) ≠ 0 := by
    intro hzero
    have hp01 : p 0 ≠ p 1 := hpInj.ne (by decide)
    obtain ⟨r, hr⟩ := exists_affineParamPoint_of_det2_eq_zero
      hp01 hzero
    have hyLine : p 3 ∈ affineSpan ℝ ({p 0, p 1} : Set Point2) := by
      apply mem_affineSpan_pair_iff_exists_lineMap_eq.mpr
      exact ⟨r, (affineParamPoint_eq_lineMap (p 0) (p 1) r).symm.trans hr⟩
    let A : KSubset α 2 := ⟨{L.p0, L.p1}, by simp [L.p0_ne_p1]⟩
    let l : GeometricBlock cfg := (geometricLineOwner cfg A).1
    have hlKind : geometricBlockKind l = .line :=
      (geometricLineOwner cfg A).2
    have hlSmall := hlineSmall l hlKind
    have h0Support : L.p0 ∈ geometricBlockSupport cfg l := by
      exact geometricLineOwner_contains cfg A (by simp [A])
    have h1Support : L.p1 ∈ geometricBlockSupport cfg l := by
      exact geometricLineOwner_contains cfg A (by simp [A])
    have hlineEq : lineOfPair cfg A =
        affineSpan ℝ ({cfg L.p0, cfg L.p1} : Set Point2) := by
      simpa [A] using lineOfPair_pair cfg L.p0_ne_p1
    have hxSupport : x.1 ∈ geometricBlockSupport cfg l := by
      change x.1 ∈ lineSupport cfg
        ⟨lineOfPair cfg A, lineOfPair_mem_determinedLines cfg A⟩
      rw [mem_lineSupport]
      change cfg x.1 ∈ lineOfPair cfg A
      rw [hlineEq]
      simpa [p, q, paschPointLabel] using hline₂
    have hySupport : y.1 ∈ geometricBlockSupport cfg l := by
      change y.1 ∈ lineSupport cfg
        ⟨lineOfPair cfg A, lineOfPair_mem_determinedLines cfg A⟩
      rw [mem_lineSupport]
      change cfg y.1 ∈ lineOfPair cfg A
      rw [hlineEq]
      simpa [p, q, paschPointLabel] using hyLine
    have hqCard : ({L.p0, L.p1, x.1, y.1} : Finset α).card = 4 := by
      have h01 : q 0 ≠ q 1 := hqInj.ne (by decide)
      have h02 : q 0 ≠ q 2 := hqInj.ne (by decide)
      have h03 : q 0 ≠ q 3 := hqInj.ne (by decide)
      have h12 : q 1 ≠ q 2 := hqInj.ne (by decide)
      have h13 : q 1 ≠ q 3 := hqInj.ne (by decide)
      have h23 : q 2 ≠ q 3 := hqInj.ne (by decide)
      simp [q, paschPointLabel] at h01 h02 h03 h12 h13 h23
      simp [h01, h02, h03, h12, h13, h23]
    have hqSub : ({L.p0, L.p1, x.1, y.1} : Finset α) ⊆
        geometricBlockSupport cfg l := by
      intro z hz
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with rfl | rfl | rfl | rfl
      · exact h0Support
      · exact h1Support
      · exact hxSupport
      · exact hySupport
    have hle := Finset.card_le_card hqSub
    omega
  obtain ⟨c₀, hc₀⟩ := exists_circle_of_geometricBlock_kind_circle cfg b hb
  have hc₀₀ := hc₀ L.p0 (by
    change L.p0 ∈ (blockSystem cfg).support b
    rw [L.baseSupport_eq]; simp)
  have hc₀₁ := hc₀ L.p1 (by
    change L.p1 ∈ (blockSystem cfg).support b
    rw [L.baseSupport_eq]; simp)
  have hc₀₄ := hc₀ L.p4 (by
    change L.p4 ∈ (blockSystem cfg).support b
    rw [L.baseSupport_eq]; simp)
  have hc₀₅ := hc₀ L.p5 (by
    change L.p5 ∈ (blockSystem cfg).support b
    rw [L.baseSupport_eq]; simp)
  obtain ⟨c₁, hc₁₀, hc₁₅, hc₁₂, hc₁₃⟩ :=
    exists_circle_through_sharedCircleBasePairValue
      cfg b x y L.sharedPair05
  obtain ⟨c₂, hc₂₁, hc₂₄, hc₂₂, hc₂₃⟩ :=
    exists_circle_through_sharedCircleBasePairValue
      cfg b x y L.sharedPair14
  have hc₀all : ∀ i ∈ ({0, 1, 4, 5} : Finset (Fin 6)),
      p i ∈ (c₀.1 : Set Point2) := by
    intro i hi
    fin_cases i
    · simpa [p, q, paschPointLabel] using hc₀₀
    · simpa [p, q, paschPointLabel] using hc₀₁
    · norm_num [Fin.ext_iff] at hi
    · norm_num [Fin.ext_iff] at hi
    · simpa [p, q, paschPointLabel] using hc₀₄
    · simpa [p, q, paschPointLabel] using hc₀₅
  have hc₁all : ∀ i ∈ ({0, 2, 3, 5} : Finset (Fin 6)),
      p i ∈ (c₁.1 : Set Point2) := by
    intro i hi
    fin_cases i
    · simpa [p, q, paschPointLabel] using hc₁₀
    · norm_num [Fin.ext_iff] at hi
    · simpa [p, q, paschPointLabel] using hc₁₂
    · simpa [p, q, paschPointLabel] using hc₁₃
    · norm_num [Fin.ext_iff] at hi
    · simpa [p, q, paschPointLabel] using hc₁₅
  have hc₂all : ∀ i ∈ ({1, 2, 3, 4} : Finset (Fin 6)),
      p i ∈ (c₂.1 : Set Point2) := by
    intro i hi
    fin_cases i
    · norm_num [Fin.ext_iff] at hi
    · simpa [p, q, paschPointLabel] using hc₂₁
    · simpa [p, q, paschPointLabel] using hc₂₂
    · simpa [p, q, paschPointLabel] using hc₂₃
    · simpa [p, q, paschPointLabel] using hc₂₄
    · norm_num [Fin.ext_iff] at hi
  apply no_labelled_pasch_three_circle_pattern p hpInj hdet
    hline₂ hline₄ hline₅₁₃ hline₅₂₄ c₀ c₁ c₂
    hc₀all hc₁all hc₂all

/-- V1 admissibility makes every geometric block a proper subset of the
label set.  This local version keeps the six-point classifier independent of
the large-case half-cap router. -/
theorem smallSix_geometricBlockSupport_card_lt
    {α : Type*} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (hadm : Admissible cfg)
    (b : GeometricBlock cfg) :
    (geometricBlockSupport cfg b).card < Fintype.card α := by
  cases b with
  | inr c =>
      exact Erdos506.V3.circleSupport_card_lt cfg hadm.2 c
  | inl l =>
      change (lineSupport cfg l).card < Fintype.card α
      by_contra hnot
      have hle : (lineSupport cfg l).card ≤ Fintype.card α := by
        simpa using Finset.card_le_univ (lineSupport cfg l)
      have heq : (lineSupport cfg l).card = Fintype.card α := by omega
      have hall : lineSupport cfg l = Finset.univ :=
        Finset.eq_univ_of_card _ heq
      apply hadm.1
      have hcolLine : Collinear ℝ (l.1 : Set Point2) := by
        rw [collinear_iff_finrank_le_one,
          ← AffineSubspace.direction_eq_vectorSpan]
        rw [l.direction_finrank]
      apply hcolLine.subset
      rintro z ⟨a, rfl⟩
      apply mem_lineSupport.mp
      rw [hall]
      simp

/-- Literal six-point lower bound, before rewriting the frozen target. -/
theorem eight_le_circleCount_of_card_six
    {α : Type*} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (hadm : Admissible cfg)
    (hα : Fintype.card α = 6) :
    8 ≤ Erdos506.V4.circleCount cfg := by
  classical
  by_contra hnot
  have hCircle : Erdos506.V4.circleCount cfg ≤ 7 := by omega
  by_cases hfour : Erdos506.V4.NoFourConcyclic cfg
  · have hv4 := Erdos506.V4.circleCount_ge_target cfg (by omega)
      (show Erdos506.V4.Admissible cfg from ⟨hadm.1, hfour⟩)
    rw [hα] at hv4
    norm_num [Erdos506.v4Target, Nat.choose] at hv4
    omega
  · have hfour' : ∃ c : ProperCircle,
        ¬(circleTrace cfg c).card ≤ 3 := by
      simpa only [Erdos506.V4.NoFourConcyclic, not_forall] using hfour
    obtain ⟨c, hcnot⟩ := hfour'
    have hcFour : 4 ≤ (circleTrace cfg c).card := by omega
    have hcProper : (circleTrace cfg c).card < Fintype.card α := hadm.2 c
    obtain ⟨t, htSub, htCard⟩ := Finset.exists_subset_card_eq
      (show 3 ≤ (circleTrace cfg c).card by omega)
    let A : KSubset α 3 := ⟨t, htCard⟩
    have htNoncollinear : IsNoncollinear cfg t := by
      by_contra htcol
      exact not_triple_subset_circle_of_collinear cfg A htcol c htSub
    let nt : NoncollinearTriple cfg :=
      ⟨t, mem_noncollinearTriples.mpr ⟨htCard, htNoncollinear⟩⟩
    have hcDetermined : c ∈ determinedCircles cfg := by
      rw [mem_determinedCircles_iff]
      refine ⟨nt, ?_⟩
      intro z hz
      exact mem_circleTrace.mp (htSub hz)
    let g : DeterminedCircle cfg := ⟨c, hcDetermined⟩
    let b : GeometricBlock cfg := Sum.inr g
    have hbKind : geometricBlockKind b = .circle := rfl
    have hbFour : 4 ≤ (geometricBlockSupport cfg b).card := by
      simpa [b, g] using hcFour
    have hbProper : (geometricBlockSupport cfg b).card < Fintype.card α := by
      simpa [b, g] using hcProper
    have htotal : (blockSystem cfg).totalCircleCount =
        Erdos506.V4.circleCount cfg := by
      rw [totalCircleCount_eq_card_determinedCircle,
        ← Erdos506.V3.circleCount_eq_card_determinedCircle]
    have hBlockCircle : (blockSystem cfg).totalCircleCount ≤ 7 := by
      rw [htotal]
      exact hCircle
    have hbCard : (geometricBlockSupport cfg b).card = 4 := by
      by_contra hne
      have hbFive : (geometricBlockSupport cfg b).card = 5 := by
        omega
      have hbSize : 3 ≤ ((blockSystem cfg).support b).card := by
        change 3 ≤ (geometricBlockSupport cfg b).card
        omega
      have hpencil := richBlockPencilBound_le_totalCircleCount
        (blockSystem cfg) b hbProper hbSize
      rw [htotal] at hpencil
      change richBlockPencilBound (Fintype.card α)
        (geometricBlockSupport cfg b).card ≤
          Erdos506.V4.circleCount cfg at hpencil
      rw [hα, hbFive] at hpencil
      norm_num [richBlockPencilBound, Nat.choose] at hpencil
      omega
    obtain ⟨x, y, hxy, heq⟩ := exists_four_circle_pencil_equality
      (blockSystem cfg) b hbKind hα hbCard hBlockCircle
    have hlineSmall : ∀ l : GeometricBlock cfg,
        geometricBlockKind l = .line →
          (geometricBlockSupport cfg l).card < 4 := by
      intro l hl
      apply line_support_card_lt_four_of_six_of_circleCount_le_seven
        (blockSystem cfg) hα hBlockCircle l hl
      exact smallSix_geometricBlockSupport_card_lt cfg hadm l
    obtain ⟨L⟩ := exists_paschPencilLabels
      (blockSystem cfg) b hbCard x y hxy heq hlineSmall
    exact no_geometric_paschPencilLabels
      cfg b hbKind x y hxy L hlineSmall

/-- The corrected public V1 lower bound at six labels. -/
theorem circleCount_ge_target_of_card_six
    {α : Type*} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (hadm : Admissible cfg)
    (hα : Fintype.card α = 6) :
    Erdos506.v1Target (Fintype.card α) ≤
      Erdos506.V4.circleCount cfg := by
  have h := eight_le_circleCount_of_card_six cfg hadm hα
  rw [hα]
  norm_num [Erdos506.v1Target]
  exact h

end Erdos506.V1
