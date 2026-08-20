import Erdos506.Finite.Bonferroni
import Erdos506.V1.BlockRows

/-!
# A common rich-block pencil for V1

This file treats rich lines and rich circles through one abstract tagged
`BlockSystem`.  For an outsider `x` and a pair `u` on a fixed block `b`, the
unique owner of `insert x u` is a circle except for a matching of line-owned
pairs when `b` itself is a circle.  Two outsider pencils overlap in at most
another matching.  Bonferroni then gives the manuscript's common lower bound.
-/

namespace Erdos506.V1

open Erdos506.Block
open Erdos506.Block.BlockSystem
open Erdos506.Finite
open Erdos506.V4

variable {Point Block : Type*} [Fintype Point] [Fintype Block]
  [DecidableEq Point]

private theorem blockKind_ne_line_iff_circle (k : BlockKind) :
    k ≠ .line ↔ k = .circle := by
  cases k <;> simp

private theorem three_le_card_union_of_card_two_of_ne
    {α : Type*} [DecidableEq α] {u v : Finset α}
    (hu : u.card = 2) (hv : v.card = 2) (huv : u ≠ v) :
    3 ≤ (u ∪ v).card := by
  have hinter : (u ∩ v).card ≤ 1 := by
    by_contra hnot
    have hleft : (u ∩ v).card ≤ u.card :=
      Finset.card_le_card Finset.inter_subset_left
    have hright : (u ∩ v).card ≤ v.card :=
      Finset.card_le_card Finset.inter_subset_right
    have hcard : (u ∩ v).card = 2 := by omega
    have hEqLeft : u ∩ v = u :=
      Finset.eq_of_subset_of_card_le Finset.inter_subset_left (by omega)
    have hEqRight : u ∩ v = v :=
      Finset.eq_of_subset_of_card_le Finset.inter_subset_right (by omega)
    exact huv (hEqLeft.symm.trans hEqRight)
  have hunion := Finset.card_union_add_card_inter u v
  omega

noncomputable def blockOutsiders (S : BlockSystem Point Block) (b : Block) :
    Finset Point :=
  Finset.univ \ S.support b

@[simp] theorem mem_blockOutsiders {S : BlockSystem Point Block}
    {b : Block} {x : Point} :
    x ∈ blockOutsiders S b ↔ x ∉ S.support b := by
  classical
  simp [blockOutsiders]

theorem card_blockOutsiders (S : BlockSystem Point Block) (b : Block) :
    (blockOutsiders S b).card = Fintype.card Point - (S.support b).card := by
  classical
  rw [blockOutsiders, Finset.card_sdiff_of_subset (Finset.subset_univ _)]
  simp

abbrev BlockBasePair (S : BlockSystem Point Block) (b : Block) :=
  {u : Finset Point // u ∈ (S.support b).powersetCard 2}

abbrev BlockOutsider (S : BlockSystem Point Block) (b : Block) :=
  {x : Point // x ∈ blockOutsiders S b}

noncomputable def pencilTriple (S : BlockSystem Point Block) (b : Block)
    (x : BlockOutsider S b) (u : BlockBasePair S b) : KSubset Point 3 := by
  refine ⟨insert x.1 u.1, ?_⟩
  have hu := Finset.mem_powersetCard.mp u.2
  have hxnot : x.1 ∉ u.1 := by
    intro hx
    exact (mem_blockOutsiders.mp x.2) (hu.1 hx)
  simp [hxnot, hu.2]

noncomputable def pencilOwner (S : BlockSystem Point Block) (b : Block)
    (x : BlockOutsider S b) (u : BlockBasePair S b) : Block :=
  S.tripleOwner (pencilTriple S b x u)

theorem pencilOwner_contains_outsider (S : BlockSystem Point Block)
    (b : Block) (x : BlockOutsider S b) (u : BlockBasePair S b) :
    x.1 ∈ S.support (pencilOwner S b x u) := by
  exact S.triple_contains (pencilTriple S b x u) (by
    simp [pencilTriple])

theorem pencilOwner_contains_pair (S : BlockSystem Point Block)
    (b : Block) (x : BlockOutsider S b) (u : BlockBasePair S b) :
    u.1 ⊆ S.support (pencilOwner S b x u) := by
  intro z hz
  exact S.triple_contains (pencilTriple S b x u) (by
    simp [pencilTriple, hz])

theorem pencilOwner_ne_base (S : BlockSystem Point Block) (b : Block)
    (x : BlockOutsider S b) (u : BlockBasePair S b) :
    pencilOwner S b x u ≠ b := by
  intro h
  have hx := pencilOwner_contains_outsider S b x u
  rw [h] at hx
  exact (mem_blockOutsiders.mp x.2) hx

theorem pencilOwner_inter_base (S : BlockSystem Point Block) (b : Block)
    (x : BlockOutsider S b) (u : BlockBasePair S b) :
    S.support (pencilOwner S b x u) ∩ S.support b = u.1 := by
  classical
  symm
  apply Finset.eq_of_subset_of_card_le
  · intro z hz
    exact Finset.mem_inter.mpr
      ⟨pencilOwner_contains_pair S b x u hz,
        (Finset.mem_powersetCard.mp u.2).1 hz⟩
  · have hlt := S.distinct_block_inter_card_lt_three
      (pencilOwner_ne_base S b x u)
    have huCard := (Finset.mem_powersetCard.mp u.2).2
    omega

theorem pencilOwner_injective (S : BlockSystem Point Block) (b : Block)
    (x : BlockOutsider S b) :
    Function.Injective (pencilOwner S b x) := by
  intro u v huv
  apply Subtype.ext
  have h := congrArg (fun c => S.support c ∩ S.support b) huv
  simpa [pencilOwner_inter_base S b x u,
    pencilOwner_inter_base S b x v] using h

noncomputable def circleBasePairs (S : BlockSystem Point Block) (b : Block)
    (x : BlockOutsider S b) : Finset (BlockBasePair S b) := by
  classical
  exact Finset.univ.filter
    (fun u => S.kind (pencilOwner S b x u) = .circle)

noncomputable def lineBasePairs (S : BlockSystem Point Block) (b : Block)
    (x : BlockOutsider S b) : Finset (BlockBasePair S b) := by
  classical
  exact Finset.univ.filter
    (fun u => S.kind (pencilOwner S b x u) = .line)

@[simp] theorem mem_circleBasePairs {S : BlockSystem Point Block} {b : Block}
    {x : BlockOutsider S b} {u : BlockBasePair S b} :
    u ∈ circleBasePairs S b x ↔
      S.kind (pencilOwner S b x u) = .circle := by
  classical
  simp [circleBasePairs]

@[simp] theorem mem_lineBasePairs {S : BlockSystem Point Block} {b : Block}
    {x : BlockOutsider S b} {u : BlockBasePair S b} :
    u ∈ lineBasePairs S b x ↔
      S.kind (pencilOwner S b x u) = .line := by
  classical
  simp [lineBasePairs]

theorem card_circleBasePairs_add_card_lineBasePairs
    (S : BlockSystem Point Block) (b : Block) (x : BlockOutsider S b) :
    (circleBasePairs S b x).card + (lineBasePairs S b x).card =
      Nat.choose (S.support b).card 2 := by
  classical
  have h := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (BlockBasePair S b)))
    (p := fun u => S.kind (pencilOwner S b x u) = .line)
  rw [Finset.card_univ, Fintype.card_coe] at h
  simpa [circleBasePairs, lineBasePairs, blockKind_ne_line_iff_circle,
    Nat.add_comm] using h

theorem pencilOwner_kind_circle_of_base_line (S : BlockSystem Point Block)
    (b : Block) (hb : S.kind b = .line) (x : BlockOutsider S b)
    (u : BlockBasePair S b) :
    S.kind (pencilOwner S b x u) = .circle := by
  cases howner : S.kind (pencilOwner S b x u) with
  | circle => rfl
  | line =>
      have heq : pencilOwner S b x u = b := by
        by_contra hne
        let c : LineBlock S := ⟨pencilOwner S b x u, howner⟩
        let d : LineBlock S := ⟨b, hb⟩
        have hcd : c ≠ d := by
          intro h
          exact hne (congrArg Subtype.val h)
        have hlt := S.distinct_line_inter_card_lt_two hcd
        change (S.support (pencilOwner S b x u) ∩ S.support b).card < 2 at hlt
        have hsub : u.1 ⊆
            S.support (pencilOwner S b x u) ∩ S.support b := by
          intro z hz
          exact Finset.mem_inter.mpr
            ⟨pencilOwner_contains_pair S b x u hz,
              (Finset.mem_powersetCard.mp u.2).1 hz⟩
        have hle := Finset.card_le_card hsub
        have huCard := (Finset.mem_powersetCard.mp u.2).2
        exact (by omega)
      have hx := pencilOwner_contains_outsider S b x u
      rw [heq] at hx
      exact ((mem_blockOutsiders.mp x.2) hx).elim

theorem lineBasePairs_eq_empty_of_base_line (S : BlockSystem Point Block)
    (b : Block) (hb : S.kind b = .line) (x : BlockOutsider S b) :
    lineBasePairs S b x = ∅ := by
  classical
  ext u
  simp only [mem_lineBasePairs, Finset.notMem_empty, iff_false]
  rw [pencilOwner_kind_circle_of_base_line S b hb x u]
  simp

noncomputable def lineBasePairValues (S : BlockSystem Point Block) (b : Block)
    (x : BlockOutsider S b) : Finset (Finset Point) := by
  classical
  exact (lineBasePairs S b x).image Subtype.val

theorem card_lineBasePairValues (S : BlockSystem Point Block) (b : Block)
    (x : BlockOutsider S b) :
    (lineBasePairValues S b x).card = (lineBasePairs S b x).card := by
  classical
  rw [lineBasePairValues,
    Finset.card_image_of_injective _ Subtype.val_injective]

theorem lineBasePairValues_pairwiseDisjoint_of_base_circle
    (S : BlockSystem Point Block) (b : Block) (hb : S.kind b = .circle)
    (x : BlockOutsider S b) :
    ((lineBasePairValues S b x : Finset (Finset Point)) :
      Set (Finset Point)).PairwiseDisjoint id := by
  classical
  intro p hp q hq hpq
  change Disjoint p q
  rw [Finset.disjoint_left]
  intro z hzp hzq
  rw [lineBasePairValues] at hp hq
  obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hp
  obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hq
  have huv : u.1 ≠ v.1 := hpq
  have huLine : S.kind (pencilOwner S b x u) = .line :=
    mem_lineBasePairs.mp hu
  have hvLine : S.kind (pencilOwner S b x v) = .line :=
    mem_lineBasePairs.mp hv
  have howners : pencilOwner S b x u = pencilOwner S b x v := by
    by_contra hne
    let c : LineBlock S := ⟨pencilOwner S b x u, huLine⟩
    let d : LineBlock S := ⟨pencilOwner S b x v, hvLine⟩
    have hcd : c ≠ d := by
      intro h
      exact hne (congrArg Subtype.val h)
    have hlt := S.distinct_line_inter_card_lt_two hcd
    change (S.support (pencilOwner S b x u) ∩
      S.support (pencilOwner S b x v)).card < 2 at hlt
    have hzBase : z ∈ S.support b :=
      (Finset.mem_powersetCard.mp u.2).1 hzp
    have hxz : x.1 ≠ z := by
      intro hxz
      subst z
      exact (mem_blockOutsiders.mp x.2) hzBase
    have hsub : ({x.1, z} : Finset Point) ⊆
        S.support (pencilOwner S b x u) ∩
          S.support (pencilOwner S b x v) := by
      intro w hw
      simp only [Finset.mem_insert, Finset.mem_singleton] at hw
      rcases hw with rfl | rfl
      · exact Finset.mem_inter.mpr
          ⟨pencilOwner_contains_outsider S b x u,
            pencilOwner_contains_outsider S b x v⟩
      · exact Finset.mem_inter.mpr
          ⟨pencilOwner_contains_pair S b x u hzp,
            pencilOwner_contains_pair S b x v hzq⟩
    have hle := Finset.card_le_card hsub
    have hcard : ({x.1, z} : Finset Point).card = 2 := by simp [hxz]
    exact (by omega)
  have hUnionCard : 3 ≤ (u.1 ∪ v.1).card :=
    three_le_card_union_of_card_two_of_ne
      (Finset.mem_powersetCard.mp u.2).2
      (Finset.mem_powersetCard.mp v.2).2 huv
  have hBaseOwner : b ≠ pencilOwner S b x u := by
    intro h
    have := congrArg S.kind h
    rw [hb, huLine] at this
    cases this
  have hinterlt := S.distinct_block_inter_card_lt_three hBaseOwner
  have hsub : u.1 ∪ v.1 ⊆
      S.support b ∩ S.support (pencilOwner S b x u) := by
    intro w hw
    rcases Finset.mem_union.mp hw with hwu | hwv
    · exact Finset.mem_inter.mpr
        ⟨(Finset.mem_powersetCard.mp u.2).1 hwu,
          pencilOwner_contains_pair S b x u hwu⟩
    · exact Finset.mem_inter.mpr
        ⟨(Finset.mem_powersetCard.mp v.2).1 hwv,
          by
            rw [howners]
            exact pencilOwner_contains_pair S b x v hwv⟩
  have hle := Finset.card_le_card hsub
  exact (by omega)

theorem card_lineBasePairs_le_half_of_base_circle
    (S : BlockSystem Point Block) (b : Block) (hb : S.kind b = .circle)
    (x : BlockOutsider S b) :
    (lineBasePairs S b x).card ≤ (S.support b).card / 2 := by
  classical
  let P := lineBasePairValues S b x
  have hsub : ∀ p ∈ P, p ⊆ S.support b := by
    intro p hp
    change p ∈ lineBasePairValues S b x at hp
    rw [lineBasePairValues] at hp
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hp
    exact (Finset.mem_powersetCard.mp u.2).1
  have hpair : ∀ p ∈ P, p.card = 2 := by
    intro p hp
    change p ∈ lineBasePairValues S b x at hp
    rw [lineBasePairValues] at hp
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hp
    exact (Finset.mem_powersetCard.mp u.2).2
  have hmatch := card_le_half_of_pairwiseDisjoint_pairs
    (S.support b) P hsub hpair
    (by simpa [P] using
      lineBasePairValues_pairwiseDisjoint_of_base_circle S b hb x)
  rw [card_lineBasePairValues S b x] at hmatch
  exact hmatch

theorem card_circleBasePairs_lower (S : BlockSystem Point Block) (b : Block)
    (x : BlockOutsider S b) :
    Nat.choose (S.support b).card 2 - (S.support b).card / 2 ≤
      (circleBasePairs S b x).card := by
  have hpart := card_circleBasePairs_add_card_lineBasePairs S b x
  have hbad : (lineBasePairs S b x).card ≤ (S.support b).card / 2 := by
    cases hb : S.kind b with
    | line => rw [lineBasePairs_eq_empty_of_base_line S b hb x]; simp
    | circle => exact card_lineBasePairs_le_half_of_base_circle S b hb x
  omega

noncomputable def circlePencil (S : BlockSystem Point Block) (b : Block)
    (x : BlockOutsider S b) : Finset Block := by
  classical
  exact (circleBasePairs S b x).image (pencilOwner S b x)

@[simp] theorem mem_circlePencil {S : BlockSystem Point Block} {b : Block}
    {x : BlockOutsider S b} {c : Block} :
    c ∈ circlePencil S b x ↔
      ∃ u : BlockBasePair S b, u ∈ circleBasePairs S b x ∧
        pencilOwner S b x u = c := by
  classical
  simp [circlePencil]

theorem card_circlePencil (S : BlockSystem Point Block) (b : Block)
    (x : BlockOutsider S b) :
    (circlePencil S b x).card = (circleBasePairs S b x).card := by
  classical
  rw [circlePencil, Finset.card_image_of_injective _
    (pencilOwner_injective S b x)]

theorem circlePencil_kind (S : BlockSystem Point Block) (b : Block)
    (x : BlockOutsider S b) {c : Block} (hc : c ∈ circlePencil S b x) :
    S.kind c = .circle := by
  obtain ⟨u, hu, rfl⟩ := mem_circlePencil.mp hc
  exact mem_circleBasePairs.mp hu

theorem outsider_mem_support_of_mem_circlePencil
    (S : BlockSystem Point Block) (b : Block) (x : BlockOutsider S b)
    {c : Block} (hc : c ∈ circlePencil S b x) :
    x.1 ∈ S.support c := by
  obtain ⟨u, hu, rfl⟩ := mem_circlePencil.mp hc
  exact pencilOwner_contains_outsider S b x u

noncomputable def commonPencils (S : BlockSystem Point Block) (b : Block)
    (x y : BlockOutsider S b) : Finset Block := by
  classical
  exact circlePencil S b x ∩ circlePencil S b y

theorem circlePencil_inter_eq_commonPencils
    (S : BlockSystem Point Block) (b : Block)
    [DecidableEq Block] (x y : BlockOutsider S b) :
    circlePencil S b x ∩ circlePencil S b y = commonPencils S b x y := by
  ext
  simp [commonPencils]

abbrev CommonPencilBlock (S : BlockSystem Point Block) (b : Block)
    (x y : BlockOutsider S b) :=
  {c : Block // c ∈ commonPencils S b x y}

noncomputable def commonPencilBasePair (S : BlockSystem Point Block)
    (b : Block) {x y : BlockOutsider S b}
    (c : CommonPencilBlock S b x y) : Finset Point :=
  S.support c.1 ∩ S.support b

theorem commonPencilBasePair_card (S : BlockSystem Point Block) (b : Block)
    (x y : BlockOutsider S b) (c : CommonPencilBlock S b x y) :
    (commonPencilBasePair S b c).card = 2 := by
  classical
  have hcFan : c.1 ∈ circlePencil S b x := (Finset.mem_inter.mp c.2).1
  obtain ⟨u, hu, howner⟩ := mem_circlePencil.mp hcFan
  unfold commonPencilBasePair
  rw [← howner, pencilOwner_inter_base S b x u]
  exact (Finset.mem_powersetCard.mp u.2).2

theorem commonPencilBasePair_injective (S : BlockSystem Point Block)
    (b : Block) (x y : BlockOutsider S b) :
    Function.Injective (commonPencilBasePair S b :
      CommonPencilBlock S b x y → Finset Point) := by
  classical
  intro c d hpair
  apply Subtype.ext
  have hcFan : c.1 ∈ circlePencil S b x := (Finset.mem_inter.mp c.2).1
  have hdFan : d.1 ∈ circlePencil S b x := (Finset.mem_inter.mp d.2).1
  obtain ⟨u, hu, hcu⟩ := mem_circlePencil.mp hcFan
  obtain ⟨v, hv, hcv⟩ := mem_circlePencil.mp hdFan
  have hpair' := hpair
  unfold commonPencilBasePair at hpair'
  rw [← hcu, ← hcv, pencilOwner_inter_base S b x u,
    pencilOwner_inter_base S b x v] at hpair'
  have huv : u = v := Subtype.ext hpair'
  exact hcu.symm.trans ((congrArg (pencilOwner S b x) huv).trans hcv)

noncomputable def commonPencilBasePairs (S : BlockSystem Point Block)
    (b : Block) (x y : BlockOutsider S b) : Finset (Finset Point) := by
  classical
  exact Finset.univ.image (commonPencilBasePair S b :
    CommonPencilBlock S b x y → Finset Point)

theorem card_commonPencilBasePairs (S : BlockSystem Point Block) (b : Block)
    (x y : BlockOutsider S b) :
    (commonPencilBasePairs S b x y).card = (commonPencils S b x y).card := by
  classical
  rw [commonPencilBasePairs, Finset.card_image_of_injective _
    (commonPencilBasePair_injective S b x y)]
  simp

theorem commonPencilBasePairs_pairwiseDisjoint
    (S : BlockSystem Point Block) (b : Block)
    (x y : BlockOutsider S b) (hxy : x ≠ y) :
    ((commonPencilBasePairs S b x y : Finset (Finset Point)) :
      Set (Finset Point)).PairwiseDisjoint id := by
  classical
  intro p hp q hq hpq
  change Disjoint p q
  rw [Finset.disjoint_left]
  intro z hzp hzq
  rw [commonPencilBasePairs] at hp hq
  obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hp
  obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hq
  have hcd : c.1 ≠ d.1 := by
    intro h
    apply hpq
    have hcd' : c = d := Subtype.ext h
    subst d
    rfl
  have hcBoth := Finset.mem_inter.mp c.2
  have hdBoth := Finset.mem_inter.mp d.2
  have hxc := outsider_mem_support_of_mem_circlePencil S b x hcBoth.1
  have hxd := outsider_mem_support_of_mem_circlePencil S b x hdBoth.1
  have hyc := outsider_mem_support_of_mem_circlePencil S b y hcBoth.2
  have hyd := outsider_mem_support_of_mem_circlePencil S b y hdBoth.2
  have hzc : z ∈ S.support c.1 := (Finset.mem_inter.mp hzp).1
  have hzd : z ∈ S.support d.1 := (Finset.mem_inter.mp hzq).1
  have hzBase : z ∈ S.support b := (Finset.mem_inter.mp hzp).2
  have hxy' : x.1 ≠ y.1 := Subtype.coe_injective.ne hxy
  have hxz : x.1 ≠ z := by
    intro hxz
    subst z
    exact (mem_blockOutsiders.mp x.2) hzBase
  have hyz : y.1 ≠ z := by
    intro hyz
    subst z
    exact (mem_blockOutsiders.mp y.2) hzBase
  have hsub : ({x.1, y.1, z} : Finset Point) ⊆
      S.support c.1 ∩ S.support d.1 := by
    intro w hw
    simp only [Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with rfl | rfl | rfl
    · exact Finset.mem_inter.mpr ⟨hxc, hxd⟩
    · exact Finset.mem_inter.mpr ⟨hyc, hyd⟩
    · exact Finset.mem_inter.mpr ⟨hzc, hzd⟩
  have hthreeCard : ({x.1, y.1, z} : Finset Point).card = 3 := by
    simp [hxy', hxz, hyz]
  have hle := Finset.card_le_card hsub
  have hlt := S.distinct_block_inter_card_lt_three hcd
  omega

theorem card_commonPencils_le_half (S : BlockSystem Point Block) (b : Block)
    (x y : BlockOutsider S b) (hxy : x ≠ y) :
    (commonPencils S b x y).card ≤ (S.support b).card / 2 := by
  classical
  let P := commonPencilBasePairs S b x y
  have hsub : ∀ p ∈ P, p ⊆ S.support b := by
    intro p hp z hz
    change p ∈ commonPencilBasePairs S b x y at hp
    rw [commonPencilBasePairs] at hp
    obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hp
    exact (Finset.mem_inter.mp hz).2
  have hpair : ∀ p ∈ P, p.card = 2 := by
    intro p hp
    change p ∈ commonPencilBasePairs S b x y at hp
    rw [commonPencilBasePairs] at hp
    obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hp
    exact commonPencilBasePair_card S b x y c
  have hmatch := card_le_half_of_pairwiseDisjoint_pairs
    (S.support b) P hsub hpair
    (by simpa [P] using commonPencilBasePairs_pairwiseDisjoint S b x y hxy)
  rw [card_commonPencilBasePairs S b x y] at hmatch
  exact hmatch

noncomputable def circlePencilForPoint (S : BlockSystem Point Block) (b : Block)
    (x : Point) : Finset Block := by
  classical
  by_cases hx : x ∈ blockOutsiders S b
  · exact circlePencil S b ⟨x, hx⟩
  · exact ∅

theorem circlePencilForPoint_eq (S : BlockSystem Point Block) (b : Block)
    {x : Point} (hx : x ∈ blockOutsiders S b) :
    circlePencilForPoint S b x = circlePencil S b ⟨x, hx⟩ := by
  classical
  simp [circlePencilForPoint, hx]

theorem richLinePencilBound_le_totalCircleCount
    (S : BlockSystem Point Block) (b : Block) (hb : S.kind b = .line) :
    (Fintype.card Point - (S.support b).card) *
        Nat.choose (S.support b).card 2 -
      Nat.choose (Fintype.card Point - (S.support b).card) 2 *
        ((S.support b).card / 2) ≤ S.totalCircleCount := by
  classical
  let I := blockOutsiders S b
  let F := circlePencilForPoint S b
  let a := Nat.choose (S.support b).card 2
  let h := (S.support b).card / 2
  have hcard : ∀ x ∈ I, (F x).card = a := by
    intro x hx
    dsimp only [F, a]
    rw [circlePencilForPoint_eq S b hx, card_circlePencil]
    have hall : circleBasePairs S b ⟨x, hx⟩ = Finset.univ := by
      classical
      apply Finset.eq_univ_of_forall
      intro u
      exact mem_circleBasePairs.mpr
        (pencilOwner_kind_circle_of_base_line S b hb ⟨x, hx⟩ u)
    rw [hall, Finset.card_univ, Fintype.card_coe]
    simp
  have hinter : ∀ x ∈ I, ∀ y ∈ I, x ≠ y → (F x ∩ F y).card ≤ h := by
    intro x hx y hy hxy
    dsimp only [F, h]
    rw [circlePencilForPoint_eq S b hx, circlePencilForPoint_eq S b hy]
    exact card_commonPencils_le_half S b ⟨x, hx⟩ ⟨y, hy⟩ (by
      intro heq
      exact hxy (congrArg Subtype.val heq))
  have hbon := card_biUnion_lower_of_card_inter_le I F a h hcard hinter
  let U := I.biUnion F
  change I.card * a ≤ U.card + Nat.choose I.card 2 * h at hbon
  have hsub : U ⊆ S.blocksOfKind .circle := by
    intro c hc
    rcases Finset.mem_biUnion.mp hc with ⟨x, hx, hcFan⟩
    dsimp only [F] at hcFan
    rw [circlePencilForPoint_eq S b hx] at hcFan
    exact (S.mem_blocksOfKind).2
      (circlePencil_kind S b ⟨x, hx⟩ hcFan)
  have htotal : U.card ≤ S.totalCircleCount := by
    exact Finset.card_le_card hsub
  have hIcard : I.card = Fintype.card Point - (S.support b).card :=
    card_blockOutsiders S b
  rw [← hIcard]
  change I.card * a - Nat.choose I.card 2 * h ≤ S.totalCircleCount
  omega

theorem richCirclePencilBound_le_totalCircleCount
    (S : BlockSystem Point Block) (b : Block) (hb : S.kind b = .circle) :
    1 + (Fintype.card Point - (S.support b).card) *
        (Nat.choose (S.support b).card 2 - (S.support b).card / 2) -
      Nat.choose (Fintype.card Point - (S.support b).card) 2 *
        ((S.support b).card / 2) ≤ S.totalCircleCount := by
  classical
  let I := blockOutsiders S b
  let F := circlePencilForPoint S b
  let a := Nat.choose (S.support b).card 2 - (S.support b).card / 2
  let h := (S.support b).card / 2
  have hcard : ∀ x ∈ I, a ≤ (F x).card := by
    intro x hx
    dsimp only [F, a]
    rw [circlePencilForPoint_eq S b hx, card_circlePencil]
    exact card_circleBasePairs_lower S b ⟨x, hx⟩
  have hinter : ∀ x ∈ I, ∀ y ∈ I, x ≠ y → (F x ∩ F y).card ≤ h := by
    intro x hx y hy hxy
    dsimp only [F, h]
    rw [circlePencilForPoint_eq S b hx, circlePencilForPoint_eq S b hy]
    exact card_commonPencils_le_half S b ⟨x, hx⟩ ⟨y, hy⟩ (by
      intro heq
      exact hxy (congrArg Subtype.val heq))
  have hbon := card_biUnion_lower_of_card_ge_inter_le I F a h hcard hinter
  let U := I.biUnion F
  change I.card * a ≤ U.card + Nat.choose I.card 2 * h at hbon
  have hbnot : b ∉ U := by
    intro hbU
    rcases Finset.mem_biUnion.mp hbU with ⟨x, hx, hbFan⟩
    dsimp only [F] at hbFan
    rw [circlePencilForPoint_eq S b hx] at hbFan
    obtain ⟨u, hu, howner⟩ := mem_circlePencil.mp hbFan
    exact pencilOwner_ne_base S b ⟨x, hx⟩ u howner
  have hsub : insert b U ⊆ S.blocksOfKind .circle := by
    intro c hc
    rcases Finset.mem_insert.mp hc with rfl | hcU
    · exact (S.mem_blocksOfKind).2 hb
    · rcases Finset.mem_biUnion.mp hcU with ⟨x, hx, hcFan⟩
      dsimp only [F] at hcFan
      rw [circlePencilForPoint_eq S b hx] at hcFan
      exact (S.mem_blocksOfKind).2
        (circlePencil_kind S b ⟨x, hx⟩ hcFan)
  have htotal : U.card + 1 ≤ S.totalCircleCount := by
    have hle := Finset.card_le_card hsub
    rw [Finset.card_insert_of_notMem hbnot] at hle
    simpa [Nat.add_comm] using hle
  have hIcard : I.card = Fintype.card Point - (S.support b).card :=
    card_blockOutsiders S b
  rw [← hIcard]
  change 1 + I.card * a - Nat.choose I.card 2 * h ≤ S.totalCircleCount
  omega

/-- The common manuscript expression for a rich line or rich circle. -/
def richBlockPencilBound (n s : ℕ) : ℕ :=
  1 + (n - s) * (Nat.choose s 2 - s / 2) -
    Nat.choose (n - s) 2 * (s / 2)

theorem richBlockPencilBound_le_totalCircleCount
    (S : BlockSystem Point Block) (b : Block)
    (hproper : (S.support b).card < Fintype.card Point)
    (hsize : 3 ≤ (S.support b).card) :
    richBlockPencilBound (Fintype.card Point) (S.support b).card ≤
      S.totalCircleCount := by
  cases hb : S.kind b with
  | circle =>
      simpa [richBlockPencilBound] using
        richCirclePencilBound_le_totalCircleCount S b hb
  | line =>
      have hline := richLinePencilBound_le_totalCircleCount
        S b hb
      have hq : 1 ≤ Fintype.card Point - (S.support b).card := by omega
      have hh : 1 ≤ (S.support b).card / 2 := by omega
      let q := Fintype.card Point - (S.support b).card
      let C := Nat.choose (S.support b).card 2
      let h := (S.support b).card / 2
      let B := Nat.choose q 2 * h
      have hC : 0 < C := by
        dsimp only [C]
        exact Nat.choose_pos (by omega)
      have hhpos : 0 < h := by
        dsimp only [h]
        omega
      have hdrop : C - h < C := Nat.sub_lt hC hhpos
      have hqpos : 0 < q := by
        dsimp only [q]
        omega
      have hmul : q * (C - h) < q * C :=
        Nat.mul_lt_mul_of_pos_left hdrop hqpos
      have hnum : 1 + q * (C - h) ≤ q * C := by omega
      have hsub : 1 + q * (C - h) - B ≤ q * C - B :=
        Nat.sub_le_sub_right hnum B
      simpa [richBlockPencilBound, q, C, h, B] using hsub.trans hline

end Erdos506.V1
