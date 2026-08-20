import Erdos506.V1.ElevenFiveC40FourteenSevenPageCapFinish

/-!
# The real four-star endpoint for the last C40/L14 seven-block row

The finite page analysis leaves a `3K2` defect graph.  At either neutral
high pivot its four incident five-circles form a saturated four-star after
inversion.  The three circles in the opposite high fibre each select a
private edge and the complementary base intersection.  Three such edges
cannot avoid the four actual size-three traces among the six four-star
edges; an intersection gives three common selected points.
-/

namespace Erdos506.V1

open Erdos506.Block
open Erdos506.Block.BlockSystem
open Erdos506.Finite
open Erdos506.Incidence
open Erdos506.V3
open Erdos506.V4

universe u

attribute [local instance] c40FourteenSeven_geometricBlockDecidableEq

/-- A three-edge subfamily of the six four-star edges meets every
four-edge private-pair family. -/
private theorem fourStar_threeEdges_meets_privatePairFamily
    (R E : Finset (Finset FourStarVertex))
    (hRcard : R.card = 3) (hRsub : R ⊆ fourStarEdges)
    (hE : IsFourStarPrivatePairFamily E) :
    ∃ e, e ∈ R ∧ e ∈ E := by
  classical
  by_contra h
  push_neg at h
  have hdisj : Disjoint R E := Finset.disjoint_left.mpr h
  have hunionSub : R ∪ E ⊆ fourStarEdges :=
    Finset.union_subset hRsub hE.2
  have hcard := Finset.card_le_card hunionSub
  rw [Finset.card_union_of_disjoint hdisj, hRcard, hE.1,
    fourStarEdges_card] at hcard
  omega

/-! ## Recovering the four original five-blocks from the inverted star -/

noncomputable def ElevenFivePivotInvertedFourStar.baseBlock
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (H : ElevenFivePivotInvertedFourStar cfg p) (i : Fin 4) :
    GeometricBlock cfg :=
  ((blockPivotLineEquiv cfg p).symm (H.sizeFourLine i)).1

theorem ElevenFivePivotInvertedFourStar.baseBlock_pivot
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (H : ElevenFivePivotInvertedFourStar cfg p) (i : Fin 4) :
    p ∈ geometricBlockSupport cfg (H.baseBlock i) :=
  ((blockPivotLineEquiv cfg p).symm (H.sizeFourLine i)).2.1

theorem ElevenFivePivotInvertedFourStar.baseBlock_support
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (H : ElevenFivePivotInvertedFourStar cfg p) (i : Fin 4) :
    H.baseSupport i = awaySupport p
      (geometricBlockSupport cfg (H.baseBlock i)) := by
  unfold ElevenFivePivotInvertedFourStar.baseSupport
    ElevenFivePivotInvertedFourStar.baseBlock
  rw [← lineSupport_blockToPivotLine cfg p
    ((blockPivotLineEquiv cfg p).symm (H.sizeFourLine i))]
  congr 1
  exact (Equiv.apply_symm_apply
    (blockPivotLineEquiv cfg p) (H.sizeFourLine i)).symm

theorem ElevenFivePivotInvertedFourStar.baseBlock_five
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (H : ElevenFivePivotInvertedFourStar cfg p) (i : Fin 4) :
    H.baseBlock i ∈ (blockSystem cfg).blocksOfSize 5 := by
  apply (blockSystem cfg).mem_blocksOfSize.mpr
  change (geometricBlockSupport cfg (H.baseBlock i)).card = 5
  have haway := congrArg Finset.card (H.baseBlock_support i)
  rw [H.baseSupport_card i,
    card_awaySupport p _ (H.baseBlock_pivot i)] at haway
  omega

theorem ElevenFivePivotInvertedFourStar.baseBlock_injective
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (H : ElevenFivePivotInvertedFourStar cfg p) :
    Function.Injective H.baseBlock := by
  intro i j hij
  apply H.sizeFourLine_injective
  have hpbeq :
      (blockPivotLineEquiv cfg p).symm (H.sizeFourLine i) =
        (blockPivotLineEquiv cfg p).symm (H.sizeFourLine j) := by
    apply Subtype.ext
    simpa [ElevenFivePivotInvertedFourStar.baseBlock] using hij
  have h := congrArg (blockToPivotLine cfg p) hpbeq
  change (blockPivotLineEquiv cfg p)
      ((blockPivotLineEquiv cfg p).symm (H.sizeFourLine i)) =
    (blockPivotLineEquiv cfg p)
      ((blockPivotLineEquiv cfg p).symm (H.sizeFourLine j)) at h
  simpa only [Equiv.apply_symm_apply] using h

theorem ElevenFivePivotInvertedFourStar.exists_baseBlock_eq
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (H : ElevenFivePivotInvertedFourStar cfg p)
    {b : GeometricBlock cfg}
    (hb : b ∈ (blockSystem cfg).blocksOfSize 5)
    (hbp : p ∈ geometricBlockSupport cfg b) :
    ∃ i : Fin 4, H.baseBlock i = b := by
  let pb : PivotBlock cfg p := ⟨b, hbp, by
    have hcard := (blockSystem cfg).mem_blocksOfSize.mp hb
    change (geometricBlockSupport cfg b).card = 5 at hcard
    omega⟩
  let L : DeterminedLineOfSize (pivotInversion cfg p) 4 :=
    ⟨blockToPivotLine cfg p pb, by
      rw [card_lineSupport_blockToPivotLine]
      change (geometricBlockSupport cfg b).card - 1 = 4
      have hcard := (blockSystem cfg).mem_blocksOfSize.mp hb
      change (geometricBlockSupport cfg b).card = 5 at hcard
      rw [hcard]⟩
  let i : Fin 4 := H.sizeFourLineEquiv.symm L
  refine ⟨i, ?_⟩
  have hline : H.sizeFourLine i = blockToPivotLine cfg p pb :=
    congrArg Subtype.val (Equiv.apply_symm_apply H.sizeFourLineEquiv L)
  have hpbeq :
      (blockPivotLineEquiv cfg p).symm (H.sizeFourLine i) = pb := by
    apply blockToPivotLine_injective cfg p
    change (blockPivotLineEquiv cfg p)
        ((blockPivotLineEquiv cfg p).symm (H.sizeFourLine i)) =
      blockToPivotLine cfg p pb
    rw [Equiv.apply_symm_apply]
    exact hline
  exact congrArg Subtype.val hpbeq

private theorem finFour_sum_eq_seven_of_unique_one
    (d : Fin 4 → ℕ)
    (hvalues : ∀ i, d i = 1 ∨ d i = 2)
    (hone : ∃! i, d i = 1) :
    ∑ i : Fin 4, d i = 7 := by
  classical
  obtain ⟨k, hk, hunique⟩ := hone
  have hfilter : ((Finset.univ : Finset (Fin 4)).filter
      fun i => d i = 1) = {k} := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_singleton]
    constructor
    · exact fun hi => hunique i hi
    · rintro rfl
      exact hk
  have hid : (∑ i : Fin 4, d i) +
      ((Finset.univ : Finset (Fin 4)).filter fun i => d i = 1).card = 8 := by
    calc
      (∑ i : Fin 4, d i) +
          ((Finset.univ : Finset (Fin 4)).filter fun i => d i = 1).card =
          ∑ i : Fin 4, (d i + if d i = 1 then 1 else 0) := by
            rw [Finset.card_eq_sum_ones, Finset.sum_filter,
              Finset.sum_add_distrib]
      _ = ∑ _i : Fin 4, 2 := by
        apply Finset.sum_congr rfl
        intro i _hi
        rcases hvalues i with hi | hi <;> simp [hi]
      _ = 8 := by norm_num
  rw [hfilter] at hid
  simp only [Finset.card_singleton] at hid
  omega

private theorem ElevenFivePivotInvertedFourStar.privateTrace_card_three_of_sum
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (H : ElevenFivePivotInvertedFourStar cfg p)
    (C : Finset (AwayFrom p)) (hCcard : C.card = 5)
    (hsum : ∑ i : Fin 4, (C ∩ H.baseSupport i).card = 7) :
    (fourStarPrivateBaseTrace H.privateBaseLabelling C).card = 3 := by
  classical
  have hdegreeSum :
      (∑ x ∈ C, fourStarDegree H.baseSupport x) = 7 := by
    rw [sum_fourStarDegree_over]
    exact hsum
  have hprofile : ∀ x ∈ C,
      fourStarDegree H.baseSupport x = 1 ∨
        fourStarDegree H.baseSupport x = 2 := by
    intro x _hx
    exact fourStarDegree_eq_one_or_two H.baseSupportSaturated x
  have hid := sum_fourStarDegree_add_card_degreeOne_eq_two_mul_card
    H.baseSupport C hprofile
  have hprivateFilter :
      (C.filter fun x => fourStarDegree H.baseSupport x = 1).card = 3 := by
    omega
  rw [fourStarPrivateBaseTrace_card]
  have hcarrier : fourStarBaseCarrier H.baseSupport = Finset.univ :=
    H.baseSupport_carrier_eq_univ
  have heq : C ∩ fourStarPrivateSet H.baseSupport =
      C.filter fun x => fourStarDegree H.baseSupport x = 1 := by
    ext x
    simp [fourStarPrivateSet, fourStarBaseDegree, fourStarDegree, hcarrier]
  rw [heq]
  exact hprivateFilter

/-- One five-point trace across a saturated four-star selects a private
edge and also contains the intersection of the two complementary bases. -/
structure FourStarFiveTraceRisk
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (H : ElevenFivePivotInvertedFourStar cfg p)
    (C : Finset (AwayFrom p)) where
  edge : Finset FourStarVertex
  edge_mem : edge ∈ fourStarEdges
  oppositeFirst : FourStarVertex
  oppositeSecond : FourStarVertex
  opposite_ne : oppositeFirst ≠ oppositeSecond
  opposite_complement :
    ({oppositeFirst, oppositeSecond} : Finset FourStarVertex) =
      (Finset.univ : Finset FourStarVertex) \ edge
  private_mem : ∀ i ∈ edge, H.privateBaseLabelling.label i ∈ C
  cross_mem : H.basePairIntersection oppositeFirst oppositeSecond opposite_ne ∈ C

noncomputable def ElevenFivePivotInvertedFourStar.fiveTraceRisk
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (H : ElevenFivePivotInvertedFourStar cfg p)
    (C : Finset (AwayFrom p)) (hCcard : C.card = 5)
    (hsum : ∑ i : Fin 4, (C ∩ H.baseSupport i).card = 7)
    (hmeets : ∀ i : Fin 4, (C ∩ H.baseSupport i).Nonempty) :
    FourStarFiveTraceRisk H C := by
  classical
  let trace := fourStarPrivateBaseTrace H.privateBaseLabelling C
  have htraceCard : trace.card = 3 := by
    simpa [trace] using H.privateTrace_card_three_of_sum C hCcard hsum
  have htraceSub : trace ⊆ (Finset.univ : Finset (Fin 4)) := by
    exact Finset.filter_subset _ _
  let omitted := (Finset.univ : Finset (Fin 4)) \ trace
  have homittedCard : omitted.card = 1 := by
    rw [show omitted = (Finset.univ : Finset (Fin 4)) \ trace by rfl,
      Finset.card_sdiff_of_subset htraceSub, Finset.card_univ,
      Fintype.card_fin, htraceCard]
  let k := Classical.choose (Finset.card_eq_one.mp homittedCard)
  have homittedEq := Classical.choose_spec (Finset.card_eq_one.mp homittedCard)
  have hkDef : k = Classical.choose (Finset.card_eq_one.mp homittedCard) := rfl
  rw [← hkDef] at homittedEq
  have hkOmitted : k ∈ omitted := by rw [homittedEq]; simp
  have hkNotTrace : k ∉ trace := (Finset.mem_sdiff.mp hkOmitted).2
  let x := Classical.choose (hmeets k)
  have hx := Classical.choose_spec (hmeets k)
  have hxC : x ∈ C := (Finset.mem_inter.mp hx).1
  have hxBase : x ∈ H.baseSupport k := (Finset.mem_inter.mp hx).2
  have hxCarrier : x ∈ fourStarBaseCarrier H.baseSupport := by
    rw [H.baseSupport_carrier_eq_univ]
    simp
  have hxDegree : fourStarBaseDegree H.baseSupport x = 2 := by
    rcases H.baseSupportProfile.degree_one_or_two x hxCarrier with hxOne | hxTwo
    · have hxPrivate : x ∈ fourStarPrivateSet H.baseSupport :=
        Finset.mem_filter.mpr ⟨hxCarrier, hxOne⟩
      have hxOnPrivateBase : x ∈ fourStarPrivateOnBase H.baseSupport k :=
        Finset.mem_inter.mpr ⟨hxBase, hxPrivate⟩
      have hlabelOnPrivateBase : H.privateBaseLabelling.label k ∈
          fourStarPrivateOnBase H.baseSupport k :=
        Finset.mem_inter.mpr
          ⟨H.privateBaseLabelling.label_on_base k,
            H.privateBaseLabelling.label_mem_private k⟩
      have hxEq : x = H.privateBaseLabelling.label k :=
        Finset.card_le_one.mp (by
          rw [H.privateOnBase_card_eq_one k]) x hxOnPrivateBase
            (H.privateBaseLabelling.label k) hlabelOnPrivateBase
      apply False.elim
      apply hkNotTrace
      simp only [trace, fourStarPrivateBaseTrace, Finset.mem_filter,
        Finset.mem_univ, true_and]
      simpa [← hxEq] using hxC
    · exact hxTwo
  let incidentBases := (Finset.univ : Finset (Fin 4)).filter fun i =>
    x ∈ H.baseSupport i
  have hincidentCard : incidentBases.card = 2 := by
    simpa [incidentBases, fourStarBaseDegree] using hxDegree
  have hkIncident : k ∈ incidentBases := by
    simp [incidentBases, hxBase]
  have heraseCard : (incidentBases.erase k).card = 1 := by
    rw [Finset.card_erase_of_mem hkIncident, hincidentCard]
  let l := Classical.choose (Finset.card_eq_one.mp heraseCard)
  have heraseEq := Classical.choose_spec (Finset.card_eq_one.mp heraseCard)
  have hlDef : l = Classical.choose (Finset.card_eq_one.mp heraseCard) := rfl
  rw [← hlDef] at heraseEq
  have hlErase : l ∈ incidentBases.erase k := by rw [heraseEq]; simp
  have hlIncident : l ∈ incidentBases := (Finset.mem_erase.mp hlErase).2
  have hkl : k ≠ l := by
    exact fun h => (Finset.mem_erase.mp hlErase).1 h.symm
  have hincidentEq : incidentBases = {k, l} := by
    rw [← heraseEq]
    exact (Finset.insert_erase hkIncident).symm
  let edge : Finset FourStarVertex :=
    (Finset.univ : Finset FourStarVertex) \ {k, l}
  have hedgeCard : edge.card = 2 := by
    rw [show edge = (Finset.univ : Finset (Fin 4)) \ {k, l} by rfl,
      Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ,
      Fintype.card_fin]
    simp [hkl]
  have hedgeMem : edge ∈ fourStarEdges := by
    apply Finset.mem_powersetCard.mpr
    exact ⟨Finset.subset_univ _, hedgeCard⟩
  have hprivateMem : ∀ i ∈ edge,
      H.privateBaseLabelling.label i ∈ C := by
    intro i hiEdge
    have hiNotK : i ≠ k := by
      intro hik
      subst i
      exact (Finset.mem_sdiff.mp hiEdge).2 (by simp)
    have hiTrace : i ∈ trace := by
      by_contra hi
      have hiOmitted : i ∈ omitted :=
        Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hi⟩
      rw [homittedEq] at hiOmitted
      exact hiNotK (Finset.mem_singleton.mp hiOmitted)
    simpa [trace, fourStarPrivateBaseTrace] using hiTrace
  have hcrossEq : x = H.basePairIntersection k l hkl := by
    have hlIncident' : l ∈
        (Finset.univ : Finset (Fin 4)).filter
          (fun i => x ∈ H.baseSupport i) := by
      simpa only [incidentBases] using hlIncident
    have hxL : x ∈ H.baseSupport l :=
      (Finset.mem_filter.mp hlIncident').2
    have hyK := H.basePairIntersection_mem_left k l hkl
    have hyL := H.basePairIntersection_mem_right k l hkl
    exact Finset.card_le_one.mp (by
      rw [H.baseSupport_inter_card_one hkl]) x
        (Finset.mem_inter.mpr ⟨hxBase, hxL⟩)
        (H.basePairIntersection k l hkl)
        (Finset.mem_inter.mpr ⟨hyK, hyL⟩)
  refine
    { edge := edge
      edge_mem := hedgeMem
      oppositeFirst := k
      oppositeSecond := l
      opposite_ne := hkl
      opposite_complement := ?_
      private_mem := hprivateMem
      cross_mem := by simpa [← hcrossEq] using hxC }
  simp [edge, hkl]

/-- Three distinct proper-circle five-traces carrying three distinct risky
edges of one actual four-star. -/
structure FourStarThreeFiveTraceRiskFamily
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (H : ElevenFivePivotInvertedFourStar cfg p) where
  trace : Fin 3 → Finset (AwayFrom p)
  traceRisk : ∀ t, FourStarFiveTraceRisk H (trace t)
  edge_injective : Function.Injective fun t => (traceRisk t).edge
  circle : Fin 3 → ProperCircle
  trace_on_circle : ∀ t,
    trace t ⊆ circleTrace (pivotInversion cfg p) (circle t)

private theorem FourStarFiveTraceRisk.cross_eq_of_edge_eq
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    {H : ElevenFivePivotInvertedFourStar cfg p}
    {C D : Finset (AwayFrom p)}
    (R : FourStarFiveTraceRisk H C) (U : FourStarFiveTraceRisk H D)
    (hedge : R.edge = U.edge) :
    H.basePairIntersection R.oppositeFirst R.oppositeSecond R.opposite_ne =
      H.basePairIntersection U.oppositeFirst U.oppositeSecond U.opposite_ne := by
  have hpair :
      ({R.oppositeFirst, R.oppositeSecond} : Finset (Fin 4)) =
        {U.oppositeFirst, U.oppositeSecond} := by
    rw [R.opposite_complement, U.opposite_complement, hedge]
  let x := H.basePairIntersection R.oppositeFirst R.oppositeSecond R.opposite_ne
  have hxFirst : x ∈ H.baseSupport U.oppositeFirst := by
    have hmem : U.oppositeFirst ∈
        ({R.oppositeFirst, R.oppositeSecond} : Finset (Fin 4)) := by
      rw [hpair]
      simp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with h | h
    · simpa [h] using
        H.basePairIntersection_mem_left R.oppositeFirst R.oppositeSecond R.opposite_ne
    · simpa [h] using
        H.basePairIntersection_mem_right R.oppositeFirst R.oppositeSecond R.opposite_ne
  have hxSecond : x ∈ H.baseSupport U.oppositeSecond := by
    have hmem : U.oppositeSecond ∈
        ({R.oppositeFirst, R.oppositeSecond} : Finset (Fin 4)) := by
      rw [hpair]
      simp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with h | h
    · simpa [h] using
        H.basePairIntersection_mem_left R.oppositeFirst R.oppositeSecond R.opposite_ne
    · simpa [h] using
        H.basePairIntersection_mem_right R.oppositeFirst R.oppositeSecond R.opposite_ne
  exact Finset.card_le_one.mp (by
    rw [H.baseSupport_inter_card_one U.opposite_ne]) x
      (Finset.mem_inter.mpr ⟨hxFirst, hxSecond⟩)
      (H.basePairIntersection U.oppositeFirst U.oppositeSecond U.opposite_ne)
      (Finset.mem_inter.mpr
        ⟨H.basePairIntersection_mem_left _ _ _,
          H.basePairIntersection_mem_right _ _ _⟩)

private theorem ElevenFivePivotInvertedFourStar.riskEdge_on_sizeThreeLine_impossible
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (H : ElevenFivePivotInvertedFourStar cfg p)
    {C : Finset (AwayFrom p)} (R : FourStarFiveTraceRisk H C)
    (c : ProperCircle)
    (hcircle : C ⊆ circleTrace (pivotInversion cfg p) c)
    (r : Fin 4) (htrace : H.sizeThreePrivateTrace r = R.edge) : False := by
  classical
  have hedgeCard : R.edge.card = 2 :=
    (Finset.mem_powersetCard.mp R.edge_mem).2
  obtain ⟨i, j, hij, hedgeEq⟩ := Finset.card_eq_two.mp hedgeCard
  have hiEdge : i ∈ R.edge := by rw [hedgeEq]; simp
  have hjEdge : j ∈ R.edge := by rw [hedgeEq]; simp
  have hiNotFirst : i ≠ R.oppositeFirst := by
    intro h
    subst i
    have hkComp : R.oppositeFirst ∈
        (Finset.univ : Finset (Fin 4)) \ R.edge := by
      rw [← R.opposite_complement]
      simp
    exact (Finset.mem_sdiff.mp hkComp).2 hiEdge
  have hjNotFirst : j ≠ R.oppositeFirst := by
    intro h
    subst j
    have hkComp : R.oppositeFirst ∈
        (Finset.univ : Finset (Fin 4)) \ R.edge := by
      rw [← R.opposite_complement]
      simp
    exact (Finset.mem_sdiff.mp hkComp).2 hjEdge
  let x := H.basePairIntersection R.oppositeFirst R.oppositeSecond R.opposite_ne
  have hlabelNe : H.privateBaseLabelling.label i ≠
      H.privateBaseLabelling.label j :=
    H.privateBaseLabelling.label_injective.ne hij
  have hxNeI : x ≠ H.privateBaseLabelling.label i := by
    intro hxi
    apply H.finiteEndpointData.private_off i R.oppositeFirst hiNotFirst
    change H.privateBaseLabelling.label i ∈ H.baseSupport R.oppositeFirst
    rw [← hxi]
    exact H.basePairIntersection_mem_left _ _ _
  have hxNeJ : x ≠ H.privateBaseLabelling.label j := by
    intro hxj
    apply H.finiteEndpointData.private_off j R.oppositeFirst hjNotFirst
    change H.privateBaseLabelling.label j ∈ H.baseSupport R.oppositeFirst
    rw [← hxj]
    exact H.basePairIntersection_mem_left _ _ _
  let Aset : Finset (AwayFrom p) :=
    {H.privateBaseLabelling.label i, H.privateBaseLabelling.label j, x}
  have hAcard : Aset.card = 3 := by
    simp [Aset, hlabelNe, Ne.symm hxNeI, Ne.symm hxNeJ]
  let A : Erdos506.Finite.KSubset (AwayFrom p) 3 := ⟨Aset, hAcard⟩
  have htracePair : H.sizeThreePrivateTrace r = ({i, j} : Finset (Fin 4)) :=
    htrace.trans hedgeEq
  have hlineSub : A.1 ⊆
      lineSupport (pivotInversion cfg p) (H.sizeThreeLine r) := by
    intro y hy
    simp only [A, Aset, Finset.mem_insert, Finset.mem_singleton] at hy
    rcases hy with rfl | rfl | rfl
    · apply (H.mem_sizeThreePrivateTrace_iff r i).mp
      rw [htracePair]
      simp
    · apply (H.mem_sizeThreePrivateTrace_iff r j).mp
      rw [htracePair]
      simp
    · exact H.basePairIntersection_mem_sizeThreeSupport_of_trace_pair'
        r i j R.oppositeFirst R.oppositeSecond
          (by simpa [hedgeEq] using hedgeCard) htracePair
            (by simpa [hedgeEq] using R.opposite_complement)
  have hcircleSub : A.1 ⊆ circleTrace (pivotInversion cfg p) c := by
    intro y hy
    apply hcircle
    simp only [A, Aset, Finset.mem_insert, Finset.mem_singleton] at hy
    rcases hy with rfl | rfl | rfl
    · exact R.private_mem i hiEdge
    · exact R.private_mem j hjEdge
    · exact R.cross_mem
  have hcollinear : ¬ IsNoncollinear (pivotInversion cfg p) A.1 := by
    intro hnoncollinear
    exact not_triple_subset_line_of_noncollinear
      (pivotInversion cfg p) A hnoncollinear (H.sizeThreeLine r) hlineSub
  exact not_triple_subset_circle_of_collinear
    (pivotInversion cfg p) A hcollinear c hcircleSub

/-- The pigeonhole step `3 + 4 > 6`, followed by the actual affine
line/proper-circle contradiction. -/
theorem FourStarThreeFiveTraceRiskFamily.impossible
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    {H : ElevenFivePivotInvertedFourStar cfg p}
    (F : FourStarThreeFiveTraceRiskFamily H) : False := by
  classical
  let R : Finset (Finset FourStarVertex) :=
    (Finset.univ : Finset (Fin 3)).image fun t => (F.traceRisk t).edge
  let E := H.sizeThreePrivateTraceFamily
  have hRcard : R.card = 3 := by
    rw [show R = (Finset.univ : Finset (Fin 3)).image
      (fun t => (F.traceRisk t).edge) by rfl,
      Finset.card_image_of_injective _ F.edge_injective]
    norm_num
  have hRsub : R ⊆ fourStarEdges := by
    intro e he
    rcases Finset.mem_image.mp he with ⟨t, _ht, rfl⟩
    exact (F.traceRisk t).edge_mem
  have hE : IsFourStarPrivatePairFamily E := by
    rcases H.additionalThreeLineClassification.tStar_or_privatePairs with
      hT | hpair
    · exact False.elim (H.not_additionalThreeLine_tStar hT)
    · simpa [E, H.additionalThreeLine_privatePairFamily_eq] using hpair
  obtain ⟨e, heR, heE⟩ :=
    fourStar_threeEdges_meets_privatePairFamily R E hRcard hRsub hE
  have heR' : e ∈ (Finset.univ : Finset (Fin 3)).image
      (fun t => (F.traceRisk t).edge) := by simpa only [R] using heR
  obtain ⟨t, _ht, hte⟩ := Finset.mem_image.mp heR'
  have heE' : e ∈ (Finset.univ : Finset (Fin 4)).image
      H.sizeThreePrivateTrace := by
    simpa only [E,
      ElevenFivePivotInvertedFourStar.sizeThreePrivateTraceFamily] using heE
  obtain ⟨r, _hr, hre⟩ := Finset.mem_image.mp heE'
  apply H.riskEdge_on_sizeThreeLine_impossible
    (F.traceRisk t) (F.circle t) (F.trace_on_circle t) r
  exact hre.trans hte.symm

private theorem ElevenFiveC40M39ThreeMatchingBipartiteTrace.leftHigh_mem_of_singletonNeighbour_right
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point}
    (T : ElevenFiveC40M39ThreeMatchingBipartiteTrace cfg)
    {c b : GeometricBlock cfg}
    (hcRight : c ∈ T.page.highFibre T.rightHigh)
    (hb : b ∈ elevenFiveC40M39SingletonNeighbours (blockSystem cfg) c) :
    T.leftHigh ∈ geometricBlockSupport cfg b := by
  classical
  let S := blockSystem cfg
  have hbData := Finset.mem_filter.mp hb
  have hbErase := Finset.mem_erase.mp hbData.1
  have hcOther := (Finset.mem_filter.mp hcRight).1
  have hcOther' : c ∈ (S.blocksOfSize 5).erase T.page.clean := by
    simpa only [S,
      ElevenFiveC40M39ThreeMatchingPageResidual.otherBlocks] using hcOther
  have hcErase := Finset.mem_erase.mp hcOther'
  let A : Finset (GeometricBlock cfg) := {b, c}
  have hA : A ∈ elevenFiveC40M39DefectEdges S := by
    apply Finset.mem_filter.mpr
    constructor
    · apply Finset.mem_powersetCard.mpr
      refine ⟨?_, by simp [A, hbErase.1]⟩
      intro d hd
      simp only [A, Finset.mem_insert, Finset.mem_singleton] at hd
      rcases hd with rfl | rfl
      · exact hbErase.2
      · exact hcErase.2
    · simpa [A, S.commonSupport_pair, Finset.inter_comm] using hbData.2
  obtain ⟨l, hlLeft, r, hrRight, hAeq⟩ :=
    T.edge_split A (by simpa [S] using hA)
  have hcA : c ∈ A := by simp [A]
  have hbA : b ∈ A := by simp [A]
  have hcEqR : c = r := by
    rw [hAeq] at hcA
    rcases Finset.mem_insert.mp hcA with hcl | hcr
    · have hcLeft : c ∈ T.page.highFibre T.leftHigh := by
        simpa [hcl] using hlLeft
      exact False.elim ((Finset.disjoint_left.mp T.fibres_disjoint)
        hcLeft hcRight)
    · exact Finset.mem_singleton.mp hcr
  have hbEqL : b = l := by
    rw [hAeq] at hbA
    rcases Finset.mem_insert.mp hbA with hbl | hbr
    · exact hbl
    · have hbr' : b = r := Finset.mem_singleton.mp hbr
      exact False.elim (hbErase.1 (hbr'.trans hcEqR.symm))
  have hlData := Finset.mem_filter.mp hlLeft
  simpa [hbEqL] using hlData.2

private theorem ElevenFiveC40M39ThreeMatchingBipartiteTrace.leftHigh_not_mem_right
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point}
    (T : ElevenFiveC40M39ThreeMatchingBipartiteTrace cfg)
    {c : GeometricBlock cfg}
    (hcRight : c ∈ T.page.highFibre T.rightHigh) :
    T.leftHigh ∉ geometricBlockSupport cfg c := by
  intro hp
  have hcOther := (Finset.mem_filter.mp hcRight).1
  have hcLeft : c ∈ T.page.highFibre T.leftHigh :=
    Finset.mem_filter.mpr ⟨hcOther, hp⟩
  exact (Finset.disjoint_left.mp T.fibres_disjoint) hcLeft hcRight

private theorem ElevenFiveC40M39ThreeMatchingBipartiteTrace.rightTrace_baseIntersection_unique_one
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point}
    (T : ElevenFiveC40M39ThreeMatchingBipartiteTrace cfg)
    (H : ElevenFivePivotInvertedFourStar cfg T.leftHigh)
    {c : GeometricBlock cfg}
    (hcRight : c ∈ T.page.highFibre T.rightHigh) :
    ∃! i : Fin 4,
      (geometricBlockSupport cfg c ∩
        geometricBlockSupport cfg (H.baseBlock i)).card = 1 := by
  classical
  let S := blockSystem cfg
  let N := elevenFiveC40M39SingletonNeighbours S c
  have hcOther := (Finset.mem_filter.mp hcRight).1
  have hcOther' : c ∈ (S.blocksOfSize 5).erase T.page.clean := by
    simpa only [S,
      ElevenFiveC40M39ThreeMatchingPageResidual.otherBlocks] using hcOther
  have hcErase := Finset.mem_erase.mp hcOther'
  have hdegree := T.page.other_degree_one c (by simpa [S] using hcErase.2)
    hcErase.1
  have hNcard : N.card = 1 := by
    change (elevenFiveC40M39SingletonNeighbours S c).card = 1
    simpa only [S, elevenFiveC40M39DefectDegree] using hdegree
  obtain ⟨b, hNeq⟩ := Finset.card_eq_one.mp hNcard
  have hbN : b ∈ N := by rw [hNeq]; simp
  have hbN' : b ∈ elevenFiveC40M39SingletonNeighbours S c := by
    simpa only [N] using hbN
  have hbData := Finset.mem_filter.mp hbN'
  have hbErase := Finset.mem_erase.mp hbData.1
  have hbp : T.leftHigh ∈ geometricBlockSupport cfg b :=
    T.leftHigh_mem_of_singletonNeighbour_right hcRight
      (by simpa [N, S] using hbN)
  obtain ⟨k, hkBlock⟩ := H.exists_baseBlock_eq
    (by simpa [S] using hbErase.2) hbp
  refine ⟨k, ?_, ?_⟩
  · simpa [hkBlock] using hbData.2
  · intro i hi
    have hpNotC := T.leftHigh_not_mem_right hcRight
    have hbaseNe : H.baseBlock i ≠ c := by
      intro h
      apply hpNotC
      rw [← h]
      exact H.baseBlock_pivot i
    have hiN : H.baseBlock i ∈ N := by
      apply Finset.mem_filter.mpr
      constructor
      · apply Finset.mem_erase.mpr
        exact ⟨hbaseNe, H.baseBlock_five i⟩
      · simpa [S] using hi
    have hbaseEq : H.baseBlock i = b := by
      rw [hNeq] at hiN
      exact Finset.mem_singleton.mp hiN
    exact H.baseBlock_injective (hbaseEq.trans hkBlock.symm)

private theorem ElevenFiveC40M39ThreeMatchingBipartiteTrace.rightTrace_baseIntersection_one_or_two
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point}
    (T : ElevenFiveC40M39ThreeMatchingBipartiteTrace cfg)
    (H : ElevenFivePivotInvertedFourStar cfg T.leftHigh)
    (hnodisjoint : ∀ b ∈ (blockSystem cfg).blocksOfSize 5,
      ∀ c ∈ (blockSystem cfg).blocksOfSize 5, b ≠ c →
        ((blockSystem cfg).support b ∩
          (blockSystem cfg).support c).card ≠ 0)
    {c : GeometricBlock cfg}
    (hcRight : c ∈ T.page.highFibre T.rightHigh) (i : Fin 4) :
    (geometricBlockSupport cfg c ∩
      geometricBlockSupport cfg (H.baseBlock i)).card = 1 ∨
    (geometricBlockSupport cfg c ∩
      geometricBlockSupport cfg (H.baseBlock i)).card = 2 := by
  let S := blockSystem cfg
  have hcOther := (Finset.mem_filter.mp hcRight).1
  have hcOther' : c ∈ (S.blocksOfSize 5).erase T.page.clean := by
    simpa only [S,
      ElevenFiveC40M39ThreeMatchingPageResidual.otherBlocks] using hcOther
  have hcErase := Finset.mem_erase.mp hcOther'
  have hpNotC := T.leftHigh_not_mem_right hcRight
  have hne : c ≠ H.baseBlock i := by
    intro h
    apply hpNotC
    rw [h]
    exact H.baseBlock_pivot i
  have hpos := hnodisjoint c (by simpa [S] using hcErase.2)
    (H.baseBlock i) (H.baseBlock_five i) hne
  have hlt := S.distinct_block_inter_card_lt_three hne
  change (geometricBlockSupport cfg c ∩
    geometricBlockSupport cfg (H.baseBlock i)).card < 3 at hlt
  change (geometricBlockSupport cfg c ∩
    geometricBlockSupport cfg (H.baseBlock i)).card ≠ 0 at hpos
  omega

private theorem ElevenFiveC40M39ThreeMatchingBipartiteTrace.rightTrace_away_sum_seven
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point}
    (T : ElevenFiveC40M39ThreeMatchingBipartiteTrace cfg)
    (H : ElevenFivePivotInvertedFourStar cfg T.leftHigh)
    (hnodisjoint : ∀ b ∈ (blockSystem cfg).blocksOfSize 5,
      ∀ c ∈ (blockSystem cfg).blocksOfSize 5, b ≠ c →
        ((blockSystem cfg).support b ∩
          (blockSystem cfg).support c).card ≠ 0)
    {c : GeometricBlock cfg}
    (hcRight : c ∈ T.page.highFibre T.rightHigh) :
    ∑ i : Fin 4,
      (awaySupport T.leftHigh (geometricBlockSupport cfg c) ∩
        H.baseSupport i).card = 7 := by
  have hone := T.rightTrace_baseIntersection_unique_one H hcRight
  have hvalues := T.rightTrace_baseIntersection_one_or_two H hnodisjoint hcRight
  have horiginal : ∑ i : Fin 4,
      (geometricBlockSupport cfg c ∩
        geometricBlockSupport cfg (H.baseBlock i)).card = 7 :=
    finFour_sum_eq_seven_of_unique_one _ hvalues hone
  have hpNotC := T.leftHigh_not_mem_right hcRight
  calc
    ∑ i : Fin 4,
        (awaySupport T.leftHigh (geometricBlockSupport cfg c) ∩
          H.baseSupport i).card =
        ∑ i : Fin 4,
          (geometricBlockSupport cfg c ∩
            geometricBlockSupport cfg (H.baseBlock i)).card := by
          apply Finset.sum_congr rfl
          intro i _hi
          rw [H.baseBlock_support, awaySupport_inter,
            card_awaySupport_of_not_mem]
          exact fun hp => hpNotC (Finset.mem_inter.mp hp).1
    _ = 7 := horiginal

private theorem ElevenFiveC40M39ThreeMatchingBipartiteTrace.rightTrace_away_meets
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point}
    (T : ElevenFiveC40M39ThreeMatchingBipartiteTrace cfg)
    (H : ElevenFivePivotInvertedFourStar cfg T.leftHigh)
    (hnodisjoint : ∀ b ∈ (blockSystem cfg).blocksOfSize 5,
      ∀ c ∈ (blockSystem cfg).blocksOfSize 5, b ≠ c →
        ((blockSystem cfg).support b ∩
          (blockSystem cfg).support c).card ≠ 0)
    {c : GeometricBlock cfg}
    (hcRight : c ∈ T.page.highFibre T.rightHigh) (i : Fin 4) :
    (awaySupport T.leftHigh (geometricBlockSupport cfg c) ∩
      H.baseSupport i).Nonempty := by
  have hvalue := T.rightTrace_baseIntersection_one_or_two
    H hnodisjoint hcRight i
  have hpNotC := T.leftHigh_not_mem_right hcRight
  apply Finset.card_pos.mp
  rw [H.baseBlock_support, awaySupport_inter,
    card_awaySupport_of_not_mem]
  · rcases hvalue with h | h <;> omega
  · exact fun hp => hpNotC (Finset.mem_inter.mp hp).1

noncomputable def ElevenFiveC40M39ThreeMatchingBipartiteTrace.rightAwayTrace
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point}
    (T : ElevenFiveC40M39ThreeMatchingBipartiteTrace cfg) (t : Fin 3) :
    Finset (AwayFrom T.leftHigh) :=
  awaySupport T.leftHigh (geometricBlockSupport cfg (T.rightBlock t))

private theorem ElevenFiveC40M39ThreeMatchingBipartiteTrace.leftHigh_not_mem_rightCircle
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point}
    (T : ElevenFiveC40M39ThreeMatchingBipartiteTrace cfg) (t : Fin 3) :
    cfg T.leftHigh ∉ ((T.rightCircle t).1 : Set Point2) := by
  intro hp
  apply T.leftHigh_not_mem_right (T.rightBlock_mem t)
  rw [T.rightBlock_eq_circle t]
  exact mem_circleTrace.mpr hp

noncomputable def ElevenFiveC40M39ThreeMatchingBipartiteTrace.rightInvertedCircle
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point}
    (T : ElevenFiveC40M39ThreeMatchingBipartiteTrace cfg) (t : Fin 3) :
    ProperCircle :=
  invertedProperCircle (cfg T.leftHigh) (T.rightCircle t).1
    (T.leftHigh_not_mem_rightCircle t)

noncomputable def ElevenFiveC40M39ThreeMatchingBipartiteTrace.rightTraceRisk
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point}
    (T : ElevenFiveC40M39ThreeMatchingBipartiteTrace cfg)
    (H : ElevenFivePivotInvertedFourStar cfg T.leftHigh)
    (hnodisjoint : ∀ b ∈ (blockSystem cfg).blocksOfSize 5,
      ∀ c ∈ (blockSystem cfg).blocksOfSize 5, b ≠ c →
        ((blockSystem cfg).support b ∩
          (blockSystem cfg).support c).card ≠ 0)
    (t : Fin 3) : FourStarFiveTraceRisk H (T.rightAwayTrace t) := by
  apply H.fiveTraceRisk
  · change (awaySupport T.leftHigh
      (geometricBlockSupport cfg (T.rightBlock t))).card = 5
    rw [card_awaySupport_of_not_mem]
    · exact (blockSystem cfg).mem_blocksOfSize.mp (T.rightBlock_five t)
    · exact T.leftHigh_not_mem_right (T.rightBlock_mem t)
  · exact T.rightTrace_away_sum_seven H hnodisjoint (T.rightBlock_mem t)
  · exact T.rightTrace_away_meets H hnodisjoint (T.rightBlock_mem t)

private theorem ElevenFiveC40M39ThreeMatchingBipartiteTrace.rightAwayTrace_on_invertedCircle
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point}
    (T : ElevenFiveC40M39ThreeMatchingBipartiteTrace cfg) (t : Fin 3) :
    T.rightAwayTrace t ⊆
      circleTrace (pivotInversion cfg T.leftHigh) (T.rightInvertedCircle t) := by
  intro q hq
  have hqBlock : q.1 ∈ geometricBlockSupport cfg (T.rightBlock t) :=
    mem_awaySupport.mp hq
  have hqCircle : cfg q.1 ∈ ((T.rightCircle t).1 : Set Point2) := by
    apply mem_circleTrace.mp
    rw [T.rightBlock_eq_circle t] at hqBlock
    simpa only [geometricBlockSupport] using hqBlock
  apply mem_circleTrace.mpr
  simpa [ElevenFiveC40M39ThreeMatchingBipartiteTrace.rightInvertedCircle,
    pivotInversion] using
      inversion_mem_invertedProperCircle (cfg T.leftHigh) (cfg q.1)
        (T.rightCircle t).1 (T.leftHigh_not_mem_rightCircle t) hqCircle

private theorem ElevenFiveC40M39ThreeMatchingBipartiteTrace.rightTraceRisk_edge_injective
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point}
    (T : ElevenFiveC40M39ThreeMatchingBipartiteTrace cfg)
    (H : ElevenFivePivotInvertedFourStar cfg T.leftHigh)
    (hnodisjoint : ∀ b ∈ (blockSystem cfg).blocksOfSize 5,
      ∀ c ∈ (blockSystem cfg).blocksOfSize 5, b ≠ c →
        ((blockSystem cfg).support b ∩
          (blockSystem cfg).support c).card ≠ 0) :
    Function.Injective fun t : Fin 3 => (T.rightTraceRisk H hnodisjoint t).edge := by
  classical
  intro t u hedge
  by_contra htu
  let Rt := T.rightTraceRisk H hnodisjoint t
  let Ru := T.rightTraceRisk H hnodisjoint u
  have hblocks : T.rightBlock t ≠ T.rightBlock u := by
    intro h
    apply htu
    apply T.rightIndex.injective
    apply Subtype.ext
    exact h
  have hedgeCard : Rt.edge.card = 2 :=
    (Finset.mem_powersetCard.mp Rt.edge_mem).2
  obtain ⟨i, j, hij, hedgeEq⟩ := Finset.card_eq_two.mp hedgeCard
  have hiRt : i ∈ Rt.edge := by rw [hedgeEq]; simp
  have hjRt : j ∈ Rt.edge := by rw [hedgeEq]; simp
  have hedge' : Rt.edge = Ru.edge := by simpa only [Rt, Ru] using hedge
  have hiRu : i ∈ Ru.edge := by rw [← hedge']; exact hiRt
  have hjRu : j ∈ Ru.edge := by rw [← hedge']; exact hjRt
  let x := H.basePairIntersection Rt.oppositeFirst Rt.oppositeSecond Rt.opposite_ne
  have hcrossEq : x =
      H.basePairIntersection Ru.oppositeFirst Ru.oppositeSecond Ru.opposite_ne :=
    Rt.cross_eq_of_edge_eq Ru (by simpa [Rt, Ru] using hedge)
  let a := H.privateBaseLabelling.label i
  let b := H.privateBaseLabelling.label j
  have hab : a ≠ b := H.privateBaseLabelling.label_injective.ne hij
  have hiNotFirst : i ≠ Rt.oppositeFirst := by
    intro h
    subst i
    have hkComp : Rt.oppositeFirst ∈
        (Finset.univ : Finset (Fin 4)) \ Rt.edge := by
      rw [← Rt.opposite_complement]
      simp
    exact (Finset.mem_sdiff.mp hkComp).2 hiRt
  have hjNotFirst : j ≠ Rt.oppositeFirst := by
    intro h
    subst j
    have hkComp : Rt.oppositeFirst ∈
        (Finset.univ : Finset (Fin 4)) \ Rt.edge := by
      rw [← Rt.opposite_complement]
      simp
    exact (Finset.mem_sdiff.mp hkComp).2 hjRt
  have hxa : x ≠ a := by
    intro h
    apply H.finiteEndpointData.private_off i Rt.oppositeFirst hiNotFirst
    change H.privateBaseLabelling.label i ∈ H.baseSupport Rt.oppositeFirst
    change x = H.privateBaseLabelling.label i at h
    rw [← h]
    exact H.basePairIntersection_mem_left _ _ _
  have hxb : x ≠ b := by
    intro h
    apply H.finiteEndpointData.private_off j Rt.oppositeFirst hjNotFirst
    change H.privateBaseLabelling.label j ∈ H.baseSupport Rt.oppositeFirst
    change x = H.privateBaseLabelling.label j at h
    rw [← h]
    exact H.basePairIntersection_mem_left _ _ _
  have habVal : a.1 ≠ b.1 := fun h => hab (Subtype.ext h)
  have hxaVal : x.1 ≠ a.1 := fun h => hxa (Subtype.ext h)
  have hxbVal : x.1 ≠ b.1 := fun h => hxb (Subtype.ext h)
  let A : Finset Point := {a.1, b.1, x.1}
  have hAcard : A.card = 3 := by
    simp [A, habVal, Ne.symm hxaVal, Ne.symm hxbVal]
  have hAt : A ⊆ geometricBlockSupport cfg (T.rightBlock t) := by
    intro y hy
    simp only [A, Finset.mem_insert, Finset.mem_singleton] at hy
    rcases hy with rfl | rfl | rfl
    · exact mem_awaySupport.mp (Rt.private_mem i hiRt)
    · exact mem_awaySupport.mp (Rt.private_mem j hjRt)
    · exact mem_awaySupport.mp Rt.cross_mem
  have hAu : A ⊆ geometricBlockSupport cfg (T.rightBlock u) := by
    intro y hy
    simp only [A, Finset.mem_insert, Finset.mem_singleton] at hy
    rcases hy with rfl | rfl | rfl
    · exact mem_awaySupport.mp (Ru.private_mem i hiRu)
    · exact mem_awaySupport.mp (Ru.private_mem j hjRu)
    · apply mem_awaySupport.mp
      rw [hcrossEq]
      exact Ru.cross_mem
  have hsub : A ⊆ geometricBlockSupport cfg (T.rightBlock t) ∩
      geometricBlockSupport cfg (T.rightBlock u) := fun y hy =>
    Finset.mem_inter.mpr ⟨hAt hy, hAu hy⟩
  have hle := Finset.card_le_card hsub
  have hlt := (blockSystem cfg).distinct_block_inter_card_lt_three hblocks
  change (geometricBlockSupport cfg (T.rightBlock t) ∩
    geometricBlockSupport cfg (T.rightBlock u)).card < 3 at hlt
  rw [hAcard] at hle
  omega

noncomputable def ElevenFiveC40M39ThreeMatchingBipartiteTrace.leftHighRiskFamily
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point}
    (T : ElevenFiveC40M39ThreeMatchingBipartiteTrace cfg)
    (H : ElevenFivePivotInvertedFourStar cfg T.leftHigh)
    (hnodisjoint : ∀ b ∈ (blockSystem cfg).blocksOfSize 5,
      ∀ c ∈ (blockSystem cfg).blocksOfSize 5, b ≠ c →
        ((blockSystem cfg).support b ∩
          (blockSystem cfg).support c).card ≠ 0) :
    FourStarThreeFiveTraceRiskFamily H where
  trace := T.rightAwayTrace
  traceRisk := T.rightTraceRisk H hnodisjoint
  edge_injective := T.rightTraceRisk_edge_injective H hnodisjoint
  circle := T.rightInvertedCircle
  trace_on_circle := T.rightAwayTrace_on_invertedCircle

theorem ElevenFiveC40M39ThreeMatchingBipartiteTrace.leftHigh_impossible
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point}
    (T : ElevenFiveC40M39ThreeMatchingBipartiteTrace cfg)
    (H : ElevenFivePivotInvertedFourStar cfg T.leftHigh)
    (hnodisjoint : ∀ b ∈ (blockSystem cfg).blocksOfSize 5,
      ∀ c ∈ (blockSystem cfg).blocksOfSize 5, b ≠ c →
        ((blockSystem cfg).support b ∩
          (blockSystem cfg).support c).card ≠ 0) : False :=
  (T.leftHighRiskFamily H hnodisjoint).impossible

/-- Swap the two high fibres; this lets the one-sided four-star endpoint
handle whichever of the two highs is the neutral `(9,4,4)` pivot. -/
def ElevenFiveC40M39ThreeMatchingBipartiteTrace.swap
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point}
    (T : ElevenFiveC40M39ThreeMatchingBipartiteTrace cfg) :
    ElevenFiveC40M39ThreeMatchingBipartiteTrace cfg where
  page := T.page
  leftHigh := T.rightHigh
  rightHigh := T.leftHigh
  high_ne := T.high_ne.symm
  clean_high_eq := by simpa [Finset.pair_comm] using T.clean_high_eq
  left_card := T.right_card
  right_card := T.left_card
  fibres_disjoint := T.fibres_disjoint.symm
  fibres_cover := by simpa [Finset.union_comm] using T.fibres_cover
  edge_split := by
    intro A hA
    obtain ⟨b, hb, c, hc, hEq⟩ := T.edge_split A hA
    exact ⟨c, hc, b, hb, by simpa [Finset.pair_comm] using hEq⟩

/-- Full unconditional real endpoint for the last no-disjoint moment-39
`3K2` row. -/
theorem elevenFive_c40_l14_b5_seven_m39_threeMatching_impossible
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    (cfg : Configuration Point) (hpoint : Fintype.card Point = 11)
    (hcap : BlockSizeCap (blockSystem cfg) 5)
    (hlocal : ∀ p : Point, ElevenFiveLocalRows (blockSystem cfg) p)
    (hglobal : ElevenFiveGlobalRows (blockSystem cfg))
    (hC : (blockSystem cfg).totalCircleCount = 40)
    (hL : elevenFiveLineTotal (blockSystem cfg) = 14)
    (hfive : (blockSystem cfg).blockCount 5 = 7)
    (hmoment : elevenFiveSecondMoment (blockSystem cfg) = 39)
    (hnodisjoint : ∀ b ∈ (blockSystem cfg).blocksOfSize 5,
      ∀ c ∈ (blockSystem cfg).blocksOfSize 5, b ≠ c →
        ((blockSystem cfg).support b ∩
          (blockSystem cfg).support c).card ≠ 0) : False := by
  obtain ⟨T, p, hpivot, hp⟩ :=
    elevenFive_c40_l14_b5_seven_m39_bipartiteTrace_exists_944
      cfg hpoint hcap hlocal hglobal hC hL hfive hmoment hnodisjoint
  rcases hp with hp | hp
  · subst p
    exact T.leftHigh_impossible
      (elevenFive944PivotFourStar cfg hpoint T.leftHigh hpivot) hnodisjoint
  · subst p
    exact T.swap.leftHigh_impossible
      (elevenFive944PivotFourStar cfg hpoint T.rightHigh hpivot) hnodisjoint

end Erdos506.V1
