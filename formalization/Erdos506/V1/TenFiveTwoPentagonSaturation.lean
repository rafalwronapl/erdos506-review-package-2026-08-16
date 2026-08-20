import Erdos506.Incidence.RadicalAxisFiveFiveGeometry
import Erdos506.V1.BlockRows
import Erdos506.V1.TenFiveTwoPentagonMeeting

/-!
# Saturation of the ten-point two-pentagon endpoint

At the exact two-pentagon row, the two five-blocks are disjoint circles and
their supports partition the ten selected points.  Every four-block therefore
cuts a two-point chord on each base circle.  The twenty four-blocks saturate
the unconditional five-by-five radical-axis capacity, so the complete
five-centre equality package is available.  Since there are no four-lines,
all saturated cross-blocks are circles.
-/

namespace Erdos506.V1

open Erdos506.Block
open Erdos506.Block.BlockSystem
open Erdos506.Incidence
open Erdos506.V4

universe u

/-! ## The two base circles -/

/-- The trace of the circle obtained from a circle-tagged geometric block is
the support of that block. -/
@[simp] theorem circleTrace_circleBlockEquiv
    {α : Type*} [Fintype α] [DecidableEq α]
    (cfg : Configuration α)
    (b : {b : GeometricBlock cfg // geometricBlockKind b = .circle}) :
    circleTrace cfg ((circleBlockEquiv cfg) b).1 =
      geometricBlockSupport cfg b.1 := by
  rcases b with ⟨b, hb⟩
  cases b with
  | inl L => cases hb
  | inr c => rfl

/-- The two actual generalized five-blocks, tagged as distinct disjoint
circles. -/
structure TenTwoPentagonBaseCircles
    {α : Type*} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) where
  first : GeometricBlock cfg
  second : GeometricBlock cfg
  first_mem : first ∈ (blockSystem cfg).blocksOfSize 5
  second_mem : second ∈ (blockSystem cfg).blocksOfSize 5
  blocks_ne : first ≠ second
  first_kind : geometricBlockKind first = .circle
  second_kind : geometricBlockKind second = .circle
  supports_disjoint :
    Disjoint (geometricBlockSupport cfg first)
      (geometricBlockSupport cfg second)

namespace TenTwoPentagonBaseCircles

variable {α : Type*} [Fintype α] [DecidableEq α]
  {cfg : Configuration α}

/-- The first base block with its circle tag attached. -/
def firstTagged (d : TenTwoPentagonBaseCircles cfg) :
    {b : GeometricBlock cfg // geometricBlockKind b = .circle} :=
  ⟨d.first, d.first_kind⟩

/-- The second base block with its circle tag attached. -/
def secondTagged (d : TenTwoPentagonBaseCircles cfg) :
    {b : GeometricBlock cfg // geometricBlockKind b = .circle} :=
  ⟨d.second, d.second_kind⟩

/-- The determined circle carried by the first five-block. -/
noncomputable def Γ (d : TenTwoPentagonBaseCircles cfg) :
    DeterminedCircle cfg :=
  circleBlockEquiv cfg d.firstTagged

/-- The determined circle carried by the second five-block. -/
noncomputable def Ω (d : TenTwoPentagonBaseCircles cfg) :
    DeterminedCircle cfg :=
  circleBlockEquiv cfg d.secondTagged

/-- The two determined base circles are distinct. -/
theorem circles_ne (d : TenTwoPentagonBaseCircles cfg) : d.Γ ≠ d.Ω := by
  intro hcircles
  change (circleBlockEquiv cfg) d.firstTagged =
    (circleBlockEquiv cfg) d.secondTagged at hcircles
  have htagged := (circleBlockEquiv cfg).injective hcircles
  exact d.blocks_ne (congrArg Subtype.val htagged)

@[simp] theorem circleTrace_Γ (d : TenTwoPentagonBaseCircles cfg) :
    circleTrace cfg d.Γ.1 = geometricBlockSupport cfg d.first := by
  simpa only [Γ] using circleTrace_circleBlockEquiv cfg d.firstTagged

@[simp] theorem circleTrace_Ω (d : TenTwoPentagonBaseCircles cfg) :
    circleTrace cfg d.Ω.1 = geometricBlockSupport cfg d.second := by
  simpa only [Ω] using circleTrace_circleBlockEquiv cfg d.secondTagged

/-- The two disjoint five-supports exhaust the ten selected points. -/
theorem supports_union_eq_univ
    (d : TenTwoPentagonBaseCircles cfg)
    (hcard : Fintype.card α = 10) :
    geometricBlockSupport cfg d.first ∪
        geometricBlockSupport cfg d.second = Finset.univ := by
  classical
  have hfirstCard : (geometricBlockSupport cfg d.first).card = 5 :=
    (blockSystem cfg).mem_blocksOfSize.mp d.first_mem
  have hsecondCard : (geometricBlockSupport cfg d.second).card = 5 :=
    (blockSystem cfg).mem_blocksOfSize.mp d.second_mem
  apply Finset.eq_univ_of_card
  rw [Finset.card_union_of_disjoint d.supports_disjoint,
    hfirstCard, hsecondCard, hcard]

@[simp] theorem exclusiveTrace_Γ_Ω
    (d : TenTwoPentagonBaseCircles cfg) :
    exclusiveCircleTrace cfg d.Γ d.Ω =
      geometricBlockSupport cfg d.first := by
  unfold exclusiveCircleTrace
  rw [d.circleTrace_Γ, d.circleTrace_Ω]
  exact Finset.sdiff_eq_self_of_disjoint d.supports_disjoint

@[simp] theorem exclusiveTrace_Ω_Γ
    (d : TenTwoPentagonBaseCircles cfg) :
    exclusiveCircleTrace cfg d.Ω d.Γ =
      geometricBlockSupport cfg d.second := by
  unfold exclusiveCircleTrace
  rw [d.circleTrace_Ω, d.circleTrace_Γ]
  exact Finset.sdiff_eq_self_of_disjoint d.supports_disjoint.symm

@[simp] theorem exclusiveTrace_Γ_Ω_card
    (d : TenTwoPentagonBaseCircles cfg) :
    (exclusiveCircleTrace cfg d.Γ d.Ω).card = 5 := by
  rw [d.exclusiveTrace_Γ_Ω]
  exact (blockSystem cfg).mem_blocksOfSize.mp d.first_mem

@[simp] theorem exclusiveTrace_Ω_Γ_card
    (d : TenTwoPentagonBaseCircles cfg) :
    (exclusiveCircleTrace cfg d.Ω d.Γ).card = 5 := by
  rw [d.exclusiveTrace_Ω_Γ]
  exact (blockSystem cfg).mem_blocksOfSize.mp d.second_mem

end TenTwoPentagonBaseCircles

/-! ## Four-block saturation -/

private theorem kind_eq_circle_of_mem_blocksOfSize_of_lineCount_eq_zero
    {Point Block : Type*} [Fintype Point] [Fintype Block]
    [DecidableEq Point]
    (S : BlockSystem Point Block) {s : ℕ} {b : Block}
    (hb : b ∈ S.blocksOfSize s) (hline : S.lineCount s = 0) :
    S.kind b = .circle := by
  classical
  cases hkind : S.kind b with
  | line =>
      exfalso
      have hbline : b ∈ S.lineBlocksOfSize s :=
        S.mem_blocksOfKindSize.mpr
          ⟨hkind, S.mem_blocksOfSize.mp hb⟩
      have hpos : 0 < S.lineCount s := by
        change 0 < (S.lineBlocksOfSize s).card
        exact Finset.card_pos.mpr ⟨b, hbline⟩
      omega
  | circle => rfl

/-- A four-block meets each member of a disjoint covering pair of
five-blocks in exactly two points. -/
private theorem fourBlock_inter_base_supports_eq_two
    {α : Type*} [Fintype α] [DecidableEq α]
    {cfg : Configuration α}
    (d : TenTwoPentagonBaseCircles cfg)
    (hcard : Fintype.card α = 10)
    {H : GeometricBlock cfg}
    (hH : H ∈ (blockSystem cfg).blocksOfSize 4) :
    (geometricBlockSupport cfg H ∩
          geometricBlockSupport cfg d.first).card = 2 ∧
      (geometricBlockSupport cfg H ∩
          geometricBlockSupport cfg d.second).card = 2 := by
  classical
  let S := blockSystem cfg
  have hHCard : (S.support H).card = 4 := S.mem_blocksOfSize.mp hH
  have hfirstCard : (S.support d.first).card = 5 :=
    S.mem_blocksOfSize.mp d.first_mem
  have hsecondCard : (S.support d.second).card = 5 :=
    S.mem_blocksOfSize.mp d.second_mem
  have hHFirst : H ≠ d.first := by
    intro hEq
    rw [hEq] at hHCard
    omega
  have hHSecond : H ≠ d.second := by
    intro hEq
    rw [hEq] at hHCard
    omega
  have hfirstLt := S.distinct_block_inter_card_lt_three hHFirst
  have hsecondLt := S.distinct_block_inter_card_lt_three hHSecond
  have hcover : S.support d.first ∪ S.support d.second = Finset.univ := by
    simpa [S] using d.supports_union_eq_univ hcard
  have hHSub : S.support H ⊆ S.support d.first ∪ S.support d.second := by
    rw [hcover]
    exact Finset.subset_univ _
  have hdecomp :
      S.support H =
        (S.support H ∩ S.support d.first) ∪
          (S.support H ∩ S.support d.second) := by
    ext p
    constructor
    · intro hp
      rcases Finset.mem_union.mp (hHSub hp) with hpFirst | hpSecond
      · exact Finset.mem_union_left _
          (Finset.mem_inter.mpr ⟨hp, hpFirst⟩)
      · exact Finset.mem_union_right _
          (Finset.mem_inter.mpr ⟨hp, hpSecond⟩)
    · intro hp
      rcases Finset.mem_union.mp hp with hpFirst | hpSecond
      · exact (Finset.mem_inter.mp hpFirst).1
      · exact (Finset.mem_inter.mp hpSecond).1
  have hunionLe := Finset.card_union_le
    (S.support H ∩ S.support d.first)
    (S.support H ∩ S.support d.second)
  rw [← hdecomp, hHCard] at hunionLe
  change
    (S.support H ∩ S.support d.first).card = 2 ∧
      (S.support H ∩ S.support d.second).card = 2
  omega

private theorem fourBlocks_subset_circleCrossBlocks
    {α : Type*} [Fintype α] [DecidableEq α]
    {cfg : Configuration α}
    (d : TenTwoPentagonBaseCircles cfg)
    (hcard : Fintype.card α = 10) :
    (blockSystem cfg).blocksOfSize 4 ⊆
      circleCrossBlocks cfg d.Γ d.Ω := by
  classical
  intro H hH
  have hintersections :=
    fourBlock_inter_base_supports_eq_two d hcard hH
  rw [circleCrossBlocks, Finset.mem_filter]
  refine ⟨Finset.mem_univ H, ?_⟩
  rw [d.exclusiveTrace_Γ_Ω, d.exclusiveTrace_Ω_Γ]
  exact hintersections

/-! ## Packaged endpoint data -/

/-- The two-pentagon endpoint together with the saturated five-by-five
radical-axis ledger. -/
structure TenTwoPentagonSaturationData
    {α : Type*} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) where
  base : TenTwoPentagonBaseCircles cfg
  crossBlocks_eq_fourBlocks :
    circleCrossBlocks cfg base.Γ base.Ω =
      (blockSystem cfg).blocksOfSize 4
  allCrossBlocks_circle :
    ∀ H : CircleCrossBlock cfg base.Γ base.Ω,
      geometricBlockKind H.1 = .circle
  fiveFive :
    FiveFiveCrossBlockSaturationData cfg base.Γ base.Ω base.circles_ne

namespace TenTwoPentagonSaturationData

variable {α : Type*} [Fintype α] [DecidableEq α]
  {cfg : Configuration α}

/-- Every cross-block in the saturated endpoint is circle-tagged. -/
@[simp] theorem crossBlock_kind_circle
    (d : TenTwoPentagonSaturationData cfg)
    (H : CircleCrossBlock cfg d.base.Γ d.base.Ω) :
    geometricBlockKind H.1 = .circle :=
  d.allCrossBlocks_circle H

end TenTwoPentagonSaturationData

/-! ## Configuration-level construction -/

/-- The exact ten-point two-pentagon row saturates the unconditional
five-by-five cross-block capacity. -/
noncomputable def tenTwoPentagon_saturation
    {α : Type u} [Fintype α] [DecidableEq α]
    (Mel : RealPlaneMelchiorPrinciple.{u})
    (EvenArr : RealPlaneEvenArrangementPrinciple.{u})
    (cfg : Configuration α) (hadm : Admissible cfg)
    (hcard : Fintype.card α = 10)
    (hB3 : (blockSystem cfg).blockCount 3 = 20)
    (hB4 : (blockSystem cfg).blockCount 4 = 20)
    (hB5 : (blockSystem cfg).blockCount 5 = 2)
    (hL3 : (blockSystem cfg).lineCount 3 = 10)
    (hL4 : (blockSystem cfg).lineCount 4 = 0)
    (hL5 : (blockSystem cfg).lineCount 5 = 0)
    (hd3 : ∀ p : α, (blockSystem cfg).blockDegree 3 p = 6) :
    TenTwoPentagonSaturationData cfg := by
  classical
  let S := blockSystem cfg
  have hFiveCard : (S.blocksOfSize 5).card = 2 := by
    simpa [S, BlockSystem.blockCount] using hB5
  let label : Fin 2 ≃ ↥(S.blocksOfSize 5) :=
    (Finset.equivFinOfCardEq hFiveCard).symm
  let b : GeometricBlock cfg := (label 0).1
  let c : GeometricBlock cfg := (label 1).1
  have hb : b ∈ S.blocksOfSize 5 := (label 0).2
  have hc : c ∈ S.blocksOfSize 5 := (label 1).2
  have hbc : b ≠ c := by
    intro h
    have h01 : (0 : Fin 2) = 1 := label.injective (Subtype.ext h)
    exact (by decide : (0 : Fin 2) ≠ 1) h01
  have hL5S : S.lineCount 5 = 0 := by simpa [S] using hL5
  have hbKind : S.kind b = .circle :=
    kind_eq_circle_of_mem_blocksOfSize_of_lineCount_eq_zero S hb hL5S
  have hcKind : S.kind c = .circle :=
    kind_eq_circle_of_mem_blocksOfSize_of_lineCount_eq_zero S hc hL5S
  have hdisjoint : Disjoint (S.support b) (S.support c) := by
    simpa [S] using
      tenTwoPentagon_fiveBlocks_pairwise_disjoint
        Mel EvenArr cfg hadm hcard hB3 hB4 hB5 hL3 hL4 hL5 hd3
          b (by simpa [S] using hb) c (by simpa [S] using hc) hbc
  let base : TenTwoPentagonBaseCircles cfg :=
    { first := b
      second := c
      first_mem := by simpa [S] using hb
      second_mem := by simpa [S] using hc
      blocks_ne := hbc
      first_kind := by simpa [S] using hbKind
      second_kind := by simpa [S] using hcKind
      supports_disjoint := by simpa [S] using hdisjoint }
  have hfourSubset : S.blocksOfSize 4 ⊆
      circleCrossBlocks cfg base.Γ base.Ω := by
    simpa [S] using fourBlocks_subset_circleCrossBlocks base hcard
  have hfourCard : (S.blocksOfSize 4).card = 20 := by
    simpa [S, BlockSystem.blockCount] using hB4
  have hcrossLe :
      (circleCrossBlocks cfg base.Γ base.Ω).card ≤ 20 :=
    circleCrossBlocks_card_le_twenty_of_five_five
      cfg base.Γ base.Ω base.circles_ne
        base.exclusiveTrace_Γ_Ω_card base.exclusiveTrace_Ω_Γ_card
  have hfourLeCross := Finset.card_le_card hfourSubset
  have hcrossCard :
      (circleCrossBlocks cfg base.Γ base.Ω).card = 20 := by
    omega
  have hcrossEq :
      circleCrossBlocks cfg base.Γ base.Ω = S.blocksOfSize 4 := by
    symm
    apply Finset.eq_of_subset_of_card_le hfourSubset
    omega
  have hL4S : S.lineCount 4 = 0 := by simpa [S] using hL4
  have hallCircle :
      ∀ H : CircleCrossBlock cfg base.Γ base.Ω,
        geometricBlockKind H.1 = .circle := by
    intro H
    have hHFour : H.1 ∈ S.blocksOfSize 4 := by
      rw [← hcrossEq]
      exact H.2
    have hkind : S.kind H.1 = .circle :=
      kind_eq_circle_of_mem_blocksOfSize_of_lineCount_eq_zero
        S hHFour hL4S
    change geometricBlockKind H.1 = .circle at hkind
    exact hkind
  have hcrossFintype :
      Fintype.card (CircleCrossBlock cfg base.Γ base.Ω) = 20 := by
    simpa only [Fintype.card_coe] using hcrossCard
  have hfiveFive :
      FiveFiveCrossBlockSaturationData
        cfg base.Γ base.Ω base.circles_ne :=
    fiveFiveCrossBlockSaturationData_of_cross_card_twenty
      cfg base.Γ base.Ω base.circles_ne
        base.exclusiveTrace_Γ_Ω_card base.exclusiveTrace_Ω_Γ_card
          hcrossFintype
  exact
    { base := base
      crossBlocks_eq_fourBlocks := by
        change circleCrossBlocks cfg base.Γ base.Ω =
          (blockSystem cfg).blocksOfSize 4 at hcrossEq
        exact hcrossEq
      allCrossBlocks_circle := hallCircle
      fiveFive := hfiveFive }

end Erdos506.V1
