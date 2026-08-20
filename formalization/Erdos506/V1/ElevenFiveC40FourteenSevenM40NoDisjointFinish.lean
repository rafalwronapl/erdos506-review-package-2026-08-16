import Erdos506.V1.ElevenFiveC40FourteenSevenThreeMatchingRealFinish

/-!
# The no-disjoint moment-40 C40/L14 seven-block seam

Relative to a degree-four five-block pivot, every opposite five-circle
meets each of the four inverted bases once or twice.  Its five selected
points therefore contain two, three, or four private labels.  In all three
cases one private edge is accompanied by the complementary base
intersection.  This feeds the common four-star collision endpoint.
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

private theorem ElevenFivePivotInvertedFourStar.privateTrace_card_of_degreeSum
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (H : ElevenFivePivotInvertedFourStar cfg p)
    (C : Finset (AwayFrom p)) (hCcard : C.card = 5)
    (m : ℕ) (hsum : ∑ i : Fin 4, (C ∩ H.baseSupport i).card = m) :
    (fourStarPrivateBaseTrace H.privateBaseLabelling C).card + m = 10 := by
  classical
  have hdegreeSum :
      (∑ x ∈ C, fourStarDegree H.baseSupport x) = m := by
    rw [sum_fourStarDegree_over]
    exact hsum
  have hprofile : ∀ x ∈ C,
      fourStarDegree H.baseSupport x = 1 ∨
        fourStarDegree H.baseSupport x = 2 := by
    intro x _hx
    exact fourStarDegree_eq_one_or_two H.baseSupportSaturated x
  have hid := sum_fourStarDegree_add_card_degreeOne_eq_two_mul_card
    H.baseSupport C hprofile
  rw [fourStarPrivateBaseTrace_card]
  have hcarrier : fourStarBaseCarrier H.baseSupport = Finset.univ :=
    H.baseSupport_carrier_eq_univ
  have heq : C ∩ fourStarPrivateSet H.baseSupport =
      C.filter fun x => fourStarDegree H.baseSupport x = 1 := by
    ext x
    simp [fourStarPrivateSet, fourStarBaseDegree, fourStarDegree, hcarrier]
  rw [heq]
  omega

private noncomputable def ElevenFivePivotInvertedFourStar.fiveTraceRisk_of_sum_six
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (H : ElevenFivePivotInvertedFourStar cfg p)
    (C : Finset (AwayFrom p)) (hCcard : C.card = 5)
    (hsum : ∑ i : Fin 4, (C ∩ H.baseSupport i).card = 6) :
    FourStarFiveTraceRisk H C := by
  classical
  let trace := fourStarPrivateBaseTrace H.privateBaseLabelling C
  have htraceCard : trace.card = 4 := by
    have h := H.privateTrace_card_of_degreeSum C hCcard 6 hsum
    simpa [trace] using (show
      (fourStarPrivateBaseTrace H.privateBaseLabelling C).card = 4 by omega)
  have htraceSub : trace ⊆ (Finset.univ : Finset (Fin 4)) :=
    Finset.filter_subset _ _
  have htraceEq : trace = Finset.univ := by
    apply Finset.eq_of_subset_of_card_le htraceSub
    rw [Finset.card_univ, Fintype.card_fin, htraceCard]
  have hprivateCard :
      (C ∩ fourStarPrivateSet H.baseSupport).card = 4 := by
    rw [← fourStarPrivateBaseTrace_card H.privateBaseLabelling C]
    exact htraceCard
  have hnotSub : ¬ C ⊆ fourStarPrivateSet H.baseSupport := by
    intro hsub
    have heq : C ∩ fourStarPrivateSet H.baseSupport = C :=
      Finset.inter_eq_left.mpr hsub
    rw [heq, hCcard] at hprivateCard
    omega
  have hex := Finset.not_subset.mp hnotSub
  let x := Classical.choose hex
  have hxSpec := Classical.choose_spec hex
  have hxC : x ∈ C := hxSpec.1
  have hxNotPrivate : x ∉ fourStarPrivateSet H.baseSupport := hxSpec.2
  have hxCarrier : x ∈ fourStarBaseCarrier H.baseSupport := by
    rw [H.baseSupport_carrier_eq_univ]
    simp
  have hxDegree : fourStarBaseDegree H.baseSupport x = 2 := by
    rcases H.baseSupportProfile.degree_one_or_two x hxCarrier with hx | hx
    · exact False.elim (hxNotPrivate (Finset.mem_filter.mpr ⟨hxCarrier, hx⟩))
    · exact hx
  let I := (Finset.univ : Finset (Fin 4)).filter fun i => x ∈ H.baseSupport i
  have hIcard : I.card = 2 := by simpa [I, fourStarBaseDegree] using hxDegree
  have htwo := Finset.card_eq_two.mp hIcard
  let k := Classical.choose htwo
  have hkSpec : ∃ l, k ≠ l ∧ I = {k, l} := by
    simpa only [k] using Classical.choose_spec htwo
  let l := Classical.choose hkSpec
  have hlSpec : k ≠ l ∧ I = {k, l} := by
    simpa only [l] using Classical.choose_spec hkSpec
  have hkl : k ≠ l := hlSpec.1
  have hIeq : I = {k, l} := hlSpec.2
  let edge : Finset FourStarVertex :=
    (Finset.univ : Finset FourStarVertex) \ {k, l}
  have hedgeCard : edge.card = 2 := by
    rw [show edge = (Finset.univ : Finset (Fin 4)) \ {k, l} by rfl,
      Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ,
      Fintype.card_fin]
    simp [hkl]
  have hedgeMem : edge ∈ fourStarEdges :=
    Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hedgeCard⟩
  have hxK : x ∈ H.baseSupport k := by
    have : k ∈ I := by rw [hIeq]; simp
    exact (Finset.mem_filter.mp this).2
  have hxL : x ∈ H.baseSupport l := by
    have : l ∈ I := by rw [hIeq]; simp
    exact (Finset.mem_filter.mp this).2
  have hxEq : x = H.basePairIntersection k l hkl :=
    Finset.card_le_one.mp (by rw [H.baseSupport_inter_card_one hkl]) x
      (Finset.mem_inter.mpr ⟨hxK, hxL⟩)
      (H.basePairIntersection k l hkl)
      (Finset.mem_inter.mpr
        ⟨H.basePairIntersection_mem_left _ _ _,
          H.basePairIntersection_mem_right _ _ _⟩)
  refine
    { edge := edge
      edge_mem := hedgeMem
      oppositeFirst := k
      oppositeSecond := l
      opposite_ne := hkl
      opposite_complement := by simp [edge, hkl]
      private_mem := ?_
      cross_mem := by rw [← hxEq]; exact hxC }
  intro i _hi
  have hiTrace : i ∈ trace := by rw [htraceEq]; simp
  simpa [trace, fourStarPrivateBaseTrace] using hiTrace

private noncomputable def ElevenFivePivotInvertedFourStar.fiveTraceRisk_of_sum_eight
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (H : ElevenFivePivotInvertedFourStar cfg p)
    (C : Finset (AwayFrom p)) (hCcard : C.card = 5)
    (hsum : ∑ i : Fin 4, (C ∩ H.baseSupport i).card = 8)
    (hupper : ∀ i : Fin 4, (C ∩ H.baseSupport i).card ≤ 2) :
    FourStarFiveTraceRisk H C := by
  classical
  let trace := fourStarPrivateBaseTrace H.privateBaseLabelling C
  have htraceCard : trace.card = 2 := by
    have h := H.privateTrace_card_of_degreeSum C hCcard 8 hsum
    simpa [trace] using (show
      (fourStarPrivateBaseTrace H.privateBaseLabelling C).card = 2 by omega)
  have hedgeMem : trace ∈ fourStarEdges :=
    Finset.mem_powersetCard.mpr ⟨Finset.filter_subset _ _, htraceCard⟩
  have htraceSub : trace ⊆ (Finset.univ : Finset (Fin 4)) :=
    Finset.filter_subset _ _
  let opposite := (Finset.univ : Finset (Fin 4)) \ trace
  have hoppositeCard : opposite.card = 2 := by
    rw [show opposite = (Finset.univ : Finset (Fin 4)) \ trace by rfl,
      Finset.card_sdiff_of_subset htraceSub,
      Finset.card_univ, Fintype.card_fin, htraceCard]
  have htwo := Finset.card_eq_two.mp hoppositeCard
  let k := Classical.choose htwo
  have hkSpec : ∃ l, k ≠ l ∧ opposite = {k, l} := by
    simpa only [k] using Classical.choose_spec htwo
  let l := Classical.choose hkSpec
  have hlSpec : k ≠ l ∧ opposite = {k, l} := by
    simpa only [l] using Classical.choose_spec hkSpec
  have hkl : k ≠ l := hlSpec.1
  have hoppositeEq : opposite = {k, l} := hlSpec.2
  have hkNotTrace : k ∉ trace := by
    intro hk
    have hkOpp : k ∈ opposite := by rw [hoppositeEq]; simp
    exact (Finset.mem_sdiff.mp hkOpp).2 hk
  have hlNotTrace : l ∉ trace := by
    intro hl
    have hlOpp : l ∈ opposite := by rw [hoppositeEq]; simp
    exact (Finset.mem_sdiff.mp hlOpp).2 hl
  have hinterCard (i : Fin 4) : (C ∩ H.baseSupport i).card = 2 := by
    have hrest :
        (∑ j ∈ (Finset.univ : Finset (Fin 4)).erase i,
          (C ∩ H.baseSupport j).card) ≤ 6 := by
      calc
        (∑ j ∈ (Finset.univ : Finset (Fin 4)).erase i,
            (C ∩ H.baseSupport j).card) ≤
            ∑ _j ∈ (Finset.univ : Finset (Fin 4)).erase i, 2 := by
              apply Finset.sum_le_sum
              intro j _hj
              exact hupper j
        _ = 6 := by simp
    have hsplit := Finset.sum_erase_add
      (Finset.univ : Finset (Fin 4))
      (fun j => (C ∩ H.baseSupport j).card) (Finset.mem_univ i)
    rw [hsum] at hsplit
    change (∑ j ∈ (Finset.univ : Finset (Fin 4)).erase i,
      (C ∩ H.baseSupport j).card) +
        (C ∩ H.baseSupport i).card = 8 at hsplit
    have := hupper i
    omega
  have hprivateCard :
      (C ∩ fourStarPrivateSet H.baseSupport).card = 2 := by
    rw [← fourStarPrivateBaseTrace_card H.privateBaseLabelling C]
    exact htraceCard
  let N := C \ fourStarPrivateSet H.baseSupport
  have hNcard : N.card = 3 := by
    have hsplit := Finset.card_inter_add_card_sdiff
      C (fourStarPrivateSet H.baseSupport)
    change (C ∩ fourStarPrivateSet H.baseSupport).card + N.card = C.card at hsplit
    omega
  have homitted_not_private (i : Fin 4) (hi : i ∉ trace) :
      C ∩ H.baseSupport i ⊆ N := by
    intro x hx
    apply Finset.mem_sdiff.mpr
    refine ⟨(Finset.mem_inter.mp hx).1, ?_⟩
    intro hxPrivate
    have hxOnPrivateBase : x ∈ fourStarPrivateOnBase H.baseSupport i :=
      Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp hx).2, hxPrivate⟩
    have hlabelOnPrivateBase : H.privateBaseLabelling.label i ∈
        fourStarPrivateOnBase H.baseSupport i :=
      Finset.mem_inter.mpr
        ⟨H.privateBaseLabelling.label_on_base i,
          H.privateBaseLabelling.label_mem_private i⟩
    have hxEq : x = H.privateBaseLabelling.label i :=
      Finset.card_le_one.mp (by rw [H.privateOnBase_card_eq_one i])
        x hxOnPrivateBase (H.privateBaseLabelling.label i)
          hlabelOnPrivateBase
    apply hi
    simp only [trace, fourStarPrivateBaseTrace, Finset.mem_filter,
      Finset.mem_univ, true_and]
    simpa [← hxEq] using (Finset.mem_inter.mp hx).1
  let A := C ∩ H.baseSupport k
  let B := C ∩ H.baseSupport l
  have hAcard : A.card = 2 := by simpa [A] using hinterCard k
  have hBcard : B.card = 2 := by simpa [B] using hinterCard l
  have hAsub : A ⊆ N := by simpa [A] using homitted_not_private k hkNotTrace
  have hBsub : B ⊆ N := by simpa [B] using homitted_not_private l hlNotTrace
  have hinterNonempty : (A ∩ B).Nonempty := by
    by_contra h
    have hempty : A ∩ B = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
    have hdisjoint : Disjoint A B := Finset.disjoint_iff_inter_eq_empty.mpr hempty
    have hunionSub : A ∪ B ⊆ N := Finset.union_subset hAsub hBsub
    have hle := Finset.card_le_card hunionSub
    rw [Finset.card_union_of_disjoint hdisjoint, hAcard, hBcard, hNcard] at hle
    omega
  let x := Classical.choose hinterNonempty
  have hxAB := Classical.choose_spec hinterNonempty
  have hxA : x ∈ A := (Finset.mem_inter.mp hxAB).1
  have hxB : x ∈ B := (Finset.mem_inter.mp hxAB).2
  have hxK : x ∈ H.baseSupport k := (Finset.mem_inter.mp hxA).2
  have hxL : x ∈ H.baseSupport l := (Finset.mem_inter.mp hxB).2
  have hxC : x ∈ C := (Finset.mem_inter.mp hxA).1
  have hxEq : x = H.basePairIntersection k l hkl :=
    Finset.card_le_one.mp (by rw [H.baseSupport_inter_card_one hkl]) x
      (Finset.mem_inter.mpr ⟨hxK, hxL⟩)
      (H.basePairIntersection k l hkl)
      (Finset.mem_inter.mpr
        ⟨H.basePairIntersection_mem_left _ _ _,
          H.basePairIntersection_mem_right _ _ _⟩)
  refine
    { edge := trace
      edge_mem := hedgeMem
      oppositeFirst := k
      oppositeSecond := l
      opposite_ne := hkl
      opposite_complement := by simpa [opposite] using hoppositeEq.symm
      private_mem := ?_
      cross_mem := by rw [← hxEq]; exact hxC }
  intro i hi
  simpa [trace, fourStarPrivateBaseTrace] using hi

private noncomputable def ElevenFivePivotInvertedFourStar.fiveTraceRisk_of_sum_cases
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (H : ElevenFivePivotInvertedFourStar cfg p)
    (C : Finset (AwayFrom p)) (hCcard : C.card = 5)
    (hmeets : ∀ i : Fin 4, (C ∩ H.baseSupport i).Nonempty)
    (hupper : ∀ i : Fin 4, (C ∩ H.baseSupport i).card ≤ 2)
    (hsumCases :
      (∑ i : Fin 4, (C ∩ H.baseSupport i).card) = 6 ∨
      (∑ i : Fin 4, (C ∩ H.baseSupport i).card) = 7 ∨
      (∑ i : Fin 4, (C ∩ H.baseSupport i).card) = 8) :
    FourStarFiveTraceRisk H C := by
  exact Classical.choice (by
    rcases hsumCases with h6 | h7 | h8
    · exact ⟨H.fiveTraceRisk_of_sum_six C hCcard h6⟩
    · exact ⟨H.fiveTraceRisk C hCcard h7 hmeets⟩
    · exact ⟨H.fiveTraceRisk_of_sum_eight C hCcard h8 hupper⟩)

/-! ## The finite no-`944` branch -/

/-- In no-disjoint moment `40`, exactly two unordered pairs of five-blocks
have singleton common support. -/
private theorem c40M40_defectEdges_card_two
    {Point : Type u} {Block : Type*} [Fintype Point] [Fintype Block]
    [DecidableEq Point] [DecidableEq Block]
    (S : BlockSystem Point Block)
    (hfive : S.blockCount 5 = 7)
    (hmoment : elevenFiveSecondMoment S = 40)
    (hnodisjoint : ∀ b ∈ S.blocksOfSize 5, ∀ c ∈ S.blocksOfSize 5,
      b ≠ c → (S.support b ∩ S.support c).card ≠ 0) :
    (elevenFiveC40M39DefectEdges S).card = 2 := by
  classical
  let F := S.blocksOfSize 5
  let Q := F.powersetCard 2
  let O := Q.filter fun A => (S.commonSupport A).card = 1
  have hFcard : F.card = 7 := by
    simpa [F, BlockSystem.blockCount] using hfive
  have hqsum :
      (∑ A ∈ Q, (S.commonSupport A).card) = 40 := by
    have hmoment' :
        (∑ A ∈ Q, (S.commonSupport A).card) =
          elevenFiveSecondMoment S := by
      change (∑ A ∈ F.powersetCard 2, (S.commonSupport A).card) =
        ∑ p : Point, Nat.choose (S.degreeIn F p) 2
      exact (S.binomial_degree_moment F 2).symm
    exact hmoment'.trans hmoment
  have hsum :
      (∑ A ∈ Q, ((S.commonSupport A).card +
        (if (S.commonSupport A).card = 1 then 1 else 0))) =
        ∑ _A ∈ Q, 2 := by
    apply Finset.sum_congr rfl
    intro A hA
    have hqLe : (S.commonSupport A).card ≤ 2 :=
      S.commonSupport_card_le_two (Finset.mem_powersetCard.mp hA).2
    obtain ⟨b, c, hbc, hAeq⟩ :=
      Finset.card_eq_two.mp (Finset.mem_powersetCard.mp hA).2
    have hb : b ∈ S.blocksOfSize 5 :=
      (Finset.mem_powersetCard.mp hA).1 (by simp [hAeq])
    have hc : c ∈ S.blocksOfSize 5 :=
      (Finset.mem_powersetCard.mp hA).1 (by simp [hAeq])
    have hqNe : (S.commonSupport A).card ≠ 0 := by
      rw [hAeq, S.commonSupport_pair]
      exact hnodisjoint b hb c hc hbc
    by_cases hqOne : (S.commonSupport A).card = 1
    · simp [hqOne]
    · have hqTwo : (S.commonSupport A).card = 2 := by omega
      simp [hqTwo]
  have hleft :
      (∑ A ∈ Q, ((S.commonSupport A).card +
        (if (S.commonSupport A).card = 1 then 1 else 0))) =
        (∑ A ∈ Q, (S.commonSupport A).card) + O.card := by
    rw [Finset.sum_add_distrib]
    congr 1
    rw [← Finset.sum_filter]
    simp [O]
  have hright : (∑ _A ∈ Q, 2) = 42 := by
    simp [Q, Finset.card_powersetCard, hFcard, Nat.choose]
  rw [hleft, hright, hqsum] at hsum
  have hOcard : O.card = 2 := by omega
  simpa [elevenFiveC40M39DefectEdges, O, Q, F] using hOcard

/-- Degree-two five-incidence points on one five-block. -/
private def c40M40LowOnFiveBlock
    {Point : Type u} {Block : Type*} [Fintype Point] [Fintype Block]
    [DecidableEq Point]
    (S : BlockSystem Point Block) (b : Block) : Finset Point :=
  (S.support b).filter fun p => S.blockDegree 5 p = 2

/-- Fubini around one selected five-block, with the self-intersection
removed from both sides. -/
private theorem c40M40_sum_degree_sub_one_eq_other_intersections
    {Point : Type u} {Block : Type*} [Fintype Point] [Fintype Block]
    [DecidableEq Point] [DecidableEq Block]
    (S : BlockSystem Point Block) (b : Block)
    (hb : b ∈ S.blocksOfSize 5) :
    (∑ p ∈ S.support b, (S.blockDegree 5 p - 1)) =
      ∑ c ∈ (S.blocksOfSize 5).erase b,
        (S.support b ∩ S.support c).card := by
  classical
  let F := S.blocksOfSize 5
  have hbF : b ∈ F := by simpa [F] using hb
  have hbcard : (S.support b).card = 5 := S.mem_blocksOfSize.mp hb
  have hdegree := S.sum_degreeIn_over F (S.support b)
  change (∑ p ∈ S.support b, S.blockDegree 5 p) =
    ∑ c ∈ F, (S.support b ∩ S.support c).card at hdegree
  have hpositive (p : Point) (hp : p ∈ S.support b) :
      0 < S.blockDegree 5 p := by
    have hmem : b ∈ F.filter fun c => p ∈ S.support c :=
      Finset.mem_filter.mpr ⟨hbF, hp⟩
    have hpos := Finset.card_pos.mpr ⟨b, hmem⟩
    simpa [F, BlockSystem.blockDegree, BlockSystem.degreeIn] using hpos
  have hleftSplit :
      (∑ p ∈ S.support b, S.blockDegree 5 p) =
        (∑ p ∈ S.support b, (S.blockDegree 5 p - 1)) + 5 := by
    calc
      (∑ p ∈ S.support b, S.blockDegree 5 p) =
          ∑ p ∈ S.support b, ((S.blockDegree 5 p - 1) + 1) := by
        apply Finset.sum_congr rfl
        intro p hp
        have hpPos := hpositive p hp
        omega
      _ = (∑ p ∈ S.support b, (S.blockDegree 5 p - 1)) + 5 := by
        rw [Finset.sum_add_distrib]
        simp [hbcard]
  have hrightSplit :
      (∑ c ∈ F, (S.support b ∩ S.support c).card) =
        (∑ c ∈ F.erase b, (S.support b ∩ S.support c).card) + 5 := by
    calc
      (∑ c ∈ F, (S.support b ∩ S.support c).card) =
          (∑ c ∈ F.erase b, (S.support b ∩ S.support c).card) +
            (S.support b ∩ S.support b).card :=
        (Finset.sum_erase_add F
          (fun c => (S.support b ∩ S.support c).card) hbF).symm
      _ = (∑ c ∈ F.erase b, (S.support b ∩ S.support c).card) + 5 := by
        simp [hbcard]
  rw [hleftSplit, hrightSplit] at hdegree
  have hcancel := Nat.add_right_cancel hdegree
  simpa only [F] using hcancel

/-- The selected-block side of the M40 Fubini identity.  Relative to the
degree-three baseline, a degree-four point adds one and the unique
degree-two point removes one. -/
private theorem c40M40_sum_degree_sub_one_add_low_eq_ten_add_high
    {Point : Type u} {Block : Type*} [Fintype Point] [Fintype Block]
    [DecidableEq Point] [DecidableEq Block]
    (S : BlockSystem Point Block) (b : Block)
    (hb : b ∈ S.blocksOfSize 5)
    (hprofile : ∀ p : Point,
      S.blockDegree 5 p = 2 ∨ S.blockDegree 5 p = 3 ∨
        S.blockDegree 5 p = 4) :
    (∑ p ∈ S.support b, (S.blockDegree 5 p - 1)) +
        (c40M40LowOnFiveBlock S b).card =
      10 + (elevenFiveC40M39HighOnFiveBlock S b).card := by
  classical
  have hbcard : (S.support b).card = 5 := S.mem_blocksOfSize.mp hb
  have hpoint (p : Point) :
      (S.blockDegree 5 p - 1) +
          (if S.blockDegree 5 p = 2 then 1 else 0) =
        2 + (if S.blockDegree 5 p = 4 then 1 else 0) := by
    rcases hprofile p with htwo | hthree | hfour
    · simp [htwo]
    · simp [hthree]
    · simp [hfour]
  have hsum :
      (∑ p ∈ S.support b,
          ((S.blockDegree 5 p - 1) +
            (if S.blockDegree 5 p = 2 then 1 else 0))) =
        ∑ p ∈ S.support b,
          (2 + (if S.blockDegree 5 p = 4 then 1 else 0)) := by
    apply Finset.sum_congr rfl
    intro p _hp
    exact hpoint p
  simp only [Finset.sum_add_distrib] at hsum
  have hlow :
      (∑ p ∈ S.support b,
        if S.blockDegree 5 p = 2 then 1 else 0) =
        (c40M40LowOnFiveBlock S b).card := by
    simp [c40M40LowOnFiveBlock]
  have hhigh :
      (∑ p ∈ S.support b,
        if S.blockDegree 5 p = 4 then 1 else 0) =
        (elevenFiveC40M39HighOnFiveBlock S b).card := by
    simp [elevenFiveC40M39HighOnFiveBlock]
  rw [hlow, hhigh] at hsum
  simpa [hbcard] using hsum

/-- In the no-disjoint face, every one of the six other intersections is
two, except for one unit lost at each singleton neighbour. -/
private theorem c40M40_other_intersections_add_defectDegree_eq_twelve
    {Point : Type u} {Block : Type*} [Fintype Point] [Fintype Block]
    [DecidableEq Point] [DecidableEq Block]
    (S : BlockSystem Point Block) (b : Block)
    (hb : b ∈ S.blocksOfSize 5)
    (hfive : S.blockCount 5 = 7)
    (hnodisjoint : ∀ c ∈ S.blocksOfSize 5, b ≠ c →
      (S.support b ∩ S.support c).card ≠ 0) :
    (∑ c ∈ (S.blocksOfSize 5).erase b,
        (S.support b ∩ S.support c).card) +
      elevenFiveC40M39DefectDegree S b = 12 := by
  classical
  let F := S.blocksOfSize 5
  let R := F.erase b
  let N := R.filter fun c => (S.support b ∩ S.support c).card = 1
  have hbF : b ∈ F := by simpa [F] using hb
  have hFcard : F.card = 7 := by
    simpa [F, BlockSystem.blockCount] using hfive
  have hRcard : R.card = 6 := by
    simp [R, Finset.card_erase_of_mem hbF, hFcard]
  have hterm (c : Block) (hc : c ∈ R) :
      (S.support b ∩ S.support c).card +
        (if (S.support b ∩ S.support c).card = 1 then 1 else 0) = 2 := by
    have hcspec := Finset.mem_erase.mp (by simpa [R] using hc)
    have hcF : c ∈ S.blocksOfSize 5 := by simpa [F] using hcspec.2
    have hbc : b ≠ c := Ne.symm hcspec.1
    have hneZero := hnodisjoint c hcF hbc
    have hlt := S.distinct_block_inter_card_lt_three hbc
    have hle : (S.support b ∩ S.support c).card ≤ 2 := by omega
    by_cases hone : (S.support b ∩ S.support c).card = 1
    · simp [hone]
    · have htwo : (S.support b ∩ S.support c).card = 2 := by omega
      simp [htwo]
  have hsum :
      (∑ c ∈ R, ((S.support b ∩ S.support c).card +
        (if (S.support b ∩ S.support c).card = 1 then 1 else 0))) =
        ∑ _c ∈ R, 2 := by
    apply Finset.sum_congr rfl
    intro c hc
    exact hterm c hc
  have hleft :
      (∑ c ∈ R, ((S.support b ∩ S.support c).card +
        (if (S.support b ∩ S.support c).card = 1 then 1 else 0))) =
        (∑ c ∈ R, (S.support b ∩ S.support c).card) + N.card := by
    rw [Finset.sum_add_distrib]
    congr 1
    rw [← Finset.sum_filter]
    simp [N]
  have hright : (∑ _c ∈ R, 2) = 12 := by simp [hRcard]
  rw [hleft, hright] at hsum
  simpa [elevenFiveC40M39DefectDegree,
    elevenFiveC40M39SingletonNeighbours, N, R, F] using hsum

/-- Exact local M40 defect identity:
`highOn(b) + defectDegree(b) = 2 + lowOn(b)`. -/
private theorem c40M40_high_add_defect_eq_two_add_low
    {Point : Type u} {Block : Type*} [Fintype Point] [Fintype Block]
    [DecidableEq Point] [DecidableEq Block]
    (S : BlockSystem Point Block)
    (hpoint : Fintype.card Point = 11)
    (hlocal : ∀ p : Point, ElevenFiveLocalRows S p)
    (hglobal : ElevenFiveGlobalRows S)
    (hfive : S.blockCount 5 = 7)
    (hmoment : elevenFiveSecondMoment S = 40)
    (b : Block) (hb : b ∈ S.blocksOfSize 5)
    (hnodisjoint : ∀ c ∈ S.blocksOfSize 5, b ≠ c →
      (S.support b ∩ S.support c).card ≠ 0) :
    (elevenFiveC40M39HighOnFiveBlock S b).card +
        elevenFiveC40M39DefectDegree S b =
      2 + (c40M40LowOnFiveBlock S b).card := by
  obtain ⟨_hfour, _hthree, _htwo, hprofile⟩ :=
    elevenFive_c40_l14_b5_seven_secondMoment_forty_profile
      S hpoint hlocal hglobal hfive hmoment
  have hselected :=
    c40M40_sum_degree_sub_one_add_low_eq_ten_add_high
      S b hb hprofile
  have hfubini := c40M40_sum_degree_sub_one_eq_other_intersections S b hb
  have hdefect := c40M40_other_intersections_add_defectDegree_eq_twelve
    S b hb hfive hnodisjoint
  omega

/-- Under the no-neutral-pivot assumption, every degree-four five-pivot
has three-degree twelve. -/
private theorem c40M40_high_three_eq_twelve_of_no944
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    (cfg : Configuration Point)
    (hlocal : ∀ p : Point, ElevenFiveLocalRows (blockSystem cfg) p)
    (hC : (blockSystem cfg).totalCircleCount = 40)
    (hno944 : ∀ p : Point,
      p ∉ elevenFive944Pivots (blockSystem cfg))
    (p : Point) (hp4 : (blockSystem cfg).blockDegree 5 p = 4) :
    (blockSystem cfg).blockDegree 3 p = 12 := by
  let S := blockSystem cfg
  have hnotSix : S.blockDegree 3 p ≠ 6 := by
    intro h6
    have hsigma := (hlocal p).sigmaRow
    change elevenFiveSigmaAt S p + 3 + S.blockDegree 5 p =
      S.blockDegree 3 p at hsigma
    rw [hp4, h6] at hsigma
    omega
  rcases elevenFive_c40_threeDegree_values S p (hlocal p) hC with
    h6 | h9 | h12
  · exact False.elim (hnotSix h6)
  · have h4 : S.blockDegree 4 p = 4 := by
      have hpair := (hlocal p).pairRow
      change S.blockDegree 3 p + 3 * S.blockDegree 4 p +
        6 * S.blockDegree 5 p = 45 at hpair
      change S.blockDegree 5 p = 4 at hp4
      rw [h9, hp4] at hpair
      omega
    exact False.elim (hno944 p
      ((mem_elevenFive944Pivots S p).2 ⟨h9, h4, hp4⟩))
  · exact h12

/-- Two distinct degree-twelve points on a five-block force three-mass at
least `42`. -/
private theorem c40M40_threeMass_ge_fortyTwo_of_two_twelve
    {Point : Type u} {Block : Type*} [Fintype Point] [Fintype Block]
    [DecidableEq Point] [DecidableEq Block]
    (S : BlockSystem Point Block)
    (hvalues : ∀ x : Point,
      S.blockDegree 3 x = 6 ∨ S.blockDegree 3 x = 9 ∨
        S.blockDegree 3 x = 12)
    (b : Block) (hb : b ∈ S.blocksOfSize 5)
    {p q : Point} (hpq : p ≠ q)
    (hpB : p ∈ S.support b) (hqB : q ∈ S.support b)
    (hp12 : S.blockDegree 3 p = 12)
    (hq12 : S.blockDegree 3 q = 12) :
    42 ≤ ∑ x ∈ S.support b, S.blockDegree 3 x := by
  classical
  have hbcard : (S.support b).card = 5 := S.mem_blocksOfSize.mp hb
  have hpointLower (x : Point) (hx : x ∈ S.support b) :
      6 + (if x = p then 6 else 0) + (if x = q then 6 else 0) ≤
        S.blockDegree 3 x := by
    by_cases hxp : x = p
    · subst x
      simp [hp12, hpq]
    · by_cases hxq : x = q
      · subst x
        simp [hq12, hxp]
      · rcases hvalues x with h6 | h9 | h12
        all_goals simp [hxp, hxq]
        all_goals omega
  have hsum := Finset.sum_le_sum fun x hx => hpointLower x hx
  have hleft :
      (∑ x ∈ S.support b,
        (6 + (if x = p then 6 else 0) + (if x = q then 6 else 0))) = 42 := by
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
    simp [hbcard, hpB, hqB]
  change 42 ≤ ∑ x ∈ S.support b, S.blockDegree 3 x
  rw [← hleft]
  exact hsum

/-- A singleton intersection in the M40 profile is carried either by the
unique degree-two point, or by a `(12,3)` point. -/
private theorem c40M40_singleton_carrier_two_or_twelveThree
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    (cfg : Configuration Point) (hpoint : Fintype.card Point = 11)
    (hlocal : ∀ p : Point, ElevenFiveLocalRows (blockSystem cfg) p)
    (hC : (blockSystem cfg).totalCircleCount = 40)
    (hprofile : ∀ p : Point,
      (blockSystem cfg).blockDegree 5 p = 2 ∨
      (blockSystem cfg).blockDegree 5 p = 3 ∨
      (blockSystem cfg).blockDegree 5 p = 4)
    {b c : GeometricBlock cfg}
    (hb : b ∈ (blockSystem cfg).blocksOfSize 5)
    (hc : c ∈ (blockSystem cfg).blocksOfSize 5)
    (hbc : b ≠ c)
    (hsingle : ((blockSystem cfg).support b ∩
      (blockSystem cfg).support c).card = 1) :
    ∃ p : Point,
      p ∈ (blockSystem cfg).support b ∧
      p ∈ (blockSystem cfg).support c ∧
      ((blockSystem cfg).blockDegree 5 p = 2 ∨
        ((blockSystem cfg).blockDegree 5 p = 3 ∧
          (blockSystem cfg).blockDegree 3 p = 12)) := by
  classical
  let S := blockSystem cfg
  obtain ⟨p, hinterEq⟩ := Finset.card_eq_one.mp hsingle
  have hpInter : p ∈ S.support b ∩ S.support c := by
    rw [hinterEq]
    simp
  have hpB := (Finset.mem_inter.mp hpInter).1
  have hpC := (Finset.mem_inter.mp hpInter).2
  rcases hprofile p with hp2 | hp3 | hp4
  · exact ⟨p, hpB, hpC, Or.inl hp2⟩
  · have hp12 := elevenFive_c40_singleton_carrier_twelve_of_fiveDegree_three
      cfg hpoint p (hlocal p) hC hp3 hb hc
        (by simpa [S, blockSystem, geometricBlockSystem,
          geometricBlockSupport] using hpB)
        (by simpa [S, blockSystem, geometricBlockSystem,
          geometricBlockSupport] using hpC)
        hbc (by simpa [S] using hsingle)
    exact ⟨p, hpB, hpC, Or.inr ⟨hp3, hp12⟩⟩
  · exact False.elim
      (elevenFive_degreeFourPivot_fiveBlock_inter_card_ne_one
        cfg hpoint p hp4 hb hc
          (by simpa [S, blockSystem, geometricBlockSystem,
            geometricBlockSupport] using hpB)
          (by simpa [S, blockSystem, geometricBlockSystem,
            geometricBlockSupport] using hpC)
          hbc (by simpa [S] using hsingle))

/-- Two global singleton edges give defect degree at most two at every
five-block. -/
private theorem c40M40_defectDegree_le_two
    {Point : Type u} {Block : Type*} [Fintype Point] [Fintype Block]
    [DecidableEq Point] [DecidableEq Block]
    (S : BlockSystem Point Block)
    (hcard : (elevenFiveC40M39DefectEdges S).card = 2)
    (b : Block) (hb : b ∈ S.blocksOfSize 5) :
    elevenFiveC40M39DefectDegree S b ≤ 2 := by
  classical
  let N := elevenFiveC40M39SingletonNeighbours S b
  let O := elevenFiveC40M39DefectEdges S
  let edge : Block → Finset Block := fun c => {b, c}
  have hedge (c : Block) (hc : c ∈ N) : edge c ∈ O := by
    have hc' := hc
    change c ∈ ((S.blocksOfSize 5).erase b).filter (fun c =>
      (S.support b ∩ S.support c).card = 1) at hc'
    have hcData := Finset.mem_filter.mp hc'
    have hcErase := Finset.mem_erase.mp hcData.1
    apply Finset.mem_filter.mpr
    constructor
    · apply Finset.mem_powersetCard.mpr
      constructor
      · intro d hd
        simp only [edge, Finset.mem_insert, Finset.mem_singleton] at hd
        rcases hd with rfl | rfl
        · exact hb
        · exact hcErase.2
      · simp [edge, Ne.symm hcErase.1]
    · simpa [edge, S.commonSupport_pair] using hcData.2
  let f : {c // c ∈ N} → {A // A ∈ O} := fun c =>
    ⟨edge c.1, hedge c.1 c.2⟩
  have hf : Function.Injective f := by
    intro c d hcd
    apply Subtype.ext
    have hedgeEq : edge c.1 = edge d.1 := congrArg Subtype.val hcd
    have hc' := c.2
    change c.1 ∈ ((S.blocksOfSize 5).erase b).filter (fun e =>
      (S.support b ∩ S.support e).card = 1) at hc'
    have hd' := d.2
    change d.1 ∈ ((S.blocksOfSize 5).erase b).filter (fun e =>
      (S.support b ∩ S.support e).card = 1) at hd'
    have hcData := Finset.mem_filter.mp hc'
    have hdData := Finset.mem_filter.mp hd'
    have hcNe : c.1 ≠ b := (Finset.mem_erase.mp hcData.1).1
    have hdNe : d.1 ≠ b := (Finset.mem_erase.mp hdData.1).1
    have hcMem : c.1 ∈ edge d.1 := by
      rw [← hedgeEq]
      simp [edge]
    simp only [edge, Finset.mem_insert, Finset.mem_singleton] at hcMem
    rcases hcMem with hcb | hcd'
    · exact False.elim (hcNe hcb)
    · exact hcd'
  have hle := Fintype.card_le_of_injective f hf
  have hle' : N.card ≤ O.card := by
    simpa only [Fintype.card_coe] using hle
  simpa [N, O, elevenFiveC40M39DefectDegree, hcard] using hle'

/-- Under no `944`, the universal degree-six baseline plus the degree-four
pivot indicators gives a blockwise mass lower bound. -/
private theorem c40M40_threeMass_ge_thirty_add_six_high
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    (cfg : Configuration Point)
    (hlocal : ∀ p : Point, ElevenFiveLocalRows (blockSystem cfg) p)
    (hC : (blockSystem cfg).totalCircleCount = 40)
    (hno944 : ∀ p : Point,
      p ∉ elevenFive944Pivots (blockSystem cfg))
    (b : GeometricBlock cfg)
    (hb : b ∈ (blockSystem cfg).blocksOfSize 5) :
    30 + 6 * (elevenFiveC40M39HighOnFiveBlock
      (blockSystem cfg) b).card ≤
      ∑ x ∈ (blockSystem cfg).support b,
        (blockSystem cfg).blockDegree 3 x := by
  classical
  let S := blockSystem cfg
  have hbcard : (S.support b).card = 5 := by
    exact S.mem_blocksOfSize.mp (by simpa [S] using hb)
  have hpointLower (x : Point) (hx : x ∈ S.support b) :
      6 + (if S.blockDegree 5 x = 4 then 6 else 0) ≤
        S.blockDegree 3 x := by
    by_cases hx4 : S.blockDegree 5 x = 4
    · have hx12 := c40M40_high_three_eq_twelve_of_no944
        cfg hlocal hC hno944 x hx4
      change S.blockDegree 3 x = 12 at hx12
      rw [hx4, hx12]
      norm_num
    · rcases elevenFive_c40_threeDegree_values S x (hlocal x) hC with
        h6 | h9 | h12 <;> simp [hx4] <;> omega
  have hsum := Finset.sum_le_sum fun x hx => hpointLower x hx
  have hleft :
      (∑ x ∈ S.support b,
        (6 + (if S.blockDegree 5 x = 4 then 6 else 0))) =
      30 + 6 * (elevenFiveC40M39HighOnFiveBlock S b).card := by
    have hhighIndicator :
        (∑ x ∈ S.support b,
          if S.blockDegree 5 x = 4 then 6 else 0) =
            6 * (elevenFiveC40M39HighOnFiveBlock S b).card := by
      change (∑ x ∈ S.support b,
        if S.blockDegree 5 x = 4 then 6 else 0) =
          6 * ((S.support b).filter fun x =>
            S.blockDegree 5 x = 4).card
      calc
        (∑ x ∈ S.support b,
            if S.blockDegree 5 x = 4 then 6 else 0) =
            ∑ _x ∈ (S.support b).filter (fun x =>
              S.blockDegree 5 x = 4), 6 := by
                rw [Finset.sum_filter]
        _ = 6 * ((S.support b).filter fun x =>
              S.blockDegree 5 x = 4).card := by
                simp [Nat.mul_comm]
    rw [Finset.sum_add_distrib, hhighIndicator]
    simp [hbcard]
  change 30 + 6 * (elevenFiveC40M39HighOnFiveBlock S b).card ≤
    ∑ x ∈ S.support b, S.blockDegree 3 x
  rw [← hleft]
  exact hsum

/-- A further `(12,3)` point on the block adds six units independently of
the degree-four pivot indicators. -/
private theorem c40M40_threeMass_ge_thirtySix_add_six_high
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    (cfg : Configuration Point)
    (hlocal : ∀ p : Point, ElevenFiveLocalRows (blockSystem cfg) p)
    (hC : (blockSystem cfg).totalCircleCount = 40)
    (hno944 : ∀ p : Point,
      p ∉ elevenFive944Pivots (blockSystem cfg))
    (b : GeometricBlock cfg)
    (hb : b ∈ (blockSystem cfg).blocksOfSize 5)
    (p : Point) (hpB : p ∈ (blockSystem cfg).support b)
    (hp3 : (blockSystem cfg).blockDegree 5 p = 3)
    (hp12 : (blockSystem cfg).blockDegree 3 p = 12) :
    36 + 6 * (elevenFiveC40M39HighOnFiveBlock
      (blockSystem cfg) b).card ≤
      ∑ x ∈ (blockSystem cfg).support b,
        (blockSystem cfg).blockDegree 3 x := by
  classical
  let S := blockSystem cfg
  change p ∈ S.support b at hpB
  change S.blockDegree 5 p = 3 at hp3
  change S.blockDegree 3 p = 12 at hp12
  have hbcard : (S.support b).card = 5 := by
    exact S.mem_blocksOfSize.mp (by simpa [S] using hb)
  have hpointLower (x : Point) (hx : x ∈ S.support b) :
      6 + (if S.blockDegree 5 x = 4 then 6 else 0) +
          (if x = p then 6 else 0) ≤ S.blockDegree 3 x := by
    by_cases hxp : x = p
    · subst x
      simp [hp3, hp12]
    · by_cases hx4 : S.blockDegree 5 x = 4
      · have hx12 := c40M40_high_three_eq_twelve_of_no944
          cfg hlocal hC hno944 x hx4
        change S.blockDegree 3 x = 12 at hx12
        simp [hxp, hx4, hx12]
      · rcases elevenFive_c40_threeDegree_values S x (hlocal x) hC with
          h6 | h9 | h12 <;> simp [hxp, hx4] <;> omega
  have hsum := Finset.sum_le_sum fun x hx => hpointLower x hx
  have hleft :
      (∑ x ∈ S.support b,
        (6 + (if S.blockDegree 5 x = 4 then 6 else 0) +
          (if x = p then 6 else 0))) =
      36 + 6 * (elevenFiveC40M39HighOnFiveBlock S b).card := by
    have hhighIndicator :
        (∑ x ∈ S.support b,
          if S.blockDegree 5 x = 4 then 6 else 0) =
            6 * (elevenFiveC40M39HighOnFiveBlock S b).card := by
      change (∑ x ∈ S.support b,
        if S.blockDegree 5 x = 4 then 6 else 0) =
          6 * ((S.support b).filter fun x =>
            S.blockDegree 5 x = 4).card
      calc
        (∑ x ∈ S.support b,
            if S.blockDegree 5 x = 4 then 6 else 0) =
            ∑ _x ∈ (S.support b).filter (fun x =>
              S.blockDegree 5 x = 4), 6 := by
                rw [Finset.sum_filter]
        _ = 6 * ((S.support b).filter fun x =>
              S.blockDegree 5 x = 4).card := by
                simp [Nat.mul_comm]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, hhighIndicator]
    simp [hbcard, hpB]
    omega
  change 36 + 6 * (elevenFiveC40M39HighOnFiveBlock S b).card ≤
    ∑ x ∈ S.support b, S.blockDegree 3 x
  rw [← hleft]
  exact hsum

/-- Every five-block incident with a singleton defect has three-mass at
least `42` in the no-`944` branch. -/
private theorem c40M40_dirty_threeMass_ge_fortyTwo
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    (cfg : Configuration Point) (hpoint : Fintype.card Point = 11)
    (hlocal : ∀ p : Point, ElevenFiveLocalRows (blockSystem cfg) p)
    (hglobal : ElevenFiveGlobalRows (blockSystem cfg))
    (hC : (blockSystem cfg).totalCircleCount = 40)
    (hfive : (blockSystem cfg).blockCount 5 = 7)
    (hmoment : elevenFiveSecondMoment (blockSystem cfg) = 40)
    (hnodisjoint : ∀ b ∈ (blockSystem cfg).blocksOfSize 5,
      ∀ c ∈ (blockSystem cfg).blocksOfSize 5, b ≠ c →
        ((blockSystem cfg).support b ∩
          (blockSystem cfg).support c).card ≠ 0)
    (hno944 : ∀ p : Point,
      p ∉ elevenFive944Pivots (blockSystem cfg))
    (b : GeometricBlock cfg)
    (hb : b ∈ (blockSystem cfg).blocksOfSize 5)
    (hdirty : 0 < elevenFiveC40M39DefectDegree (blockSystem cfg) b) :
    42 ≤ ∑ p ∈ (blockSystem cfg).support b,
      (blockSystem cfg).blockDegree 3 p := by
  classical
  let S := blockSystem cfg
  change 42 ≤ ∑ p ∈ S.support b, S.blockDegree 3 p
  change 0 < elevenFiveC40M39DefectDegree S b at hdirty
  let N := elevenFiveC40M39SingletonNeighbours S b
  obtain ⟨_hfour, _hthree, htwo, hprofile⟩ :=
    elevenFive_c40_l14_b5_seven_secondMoment_forty_profile
      S hpoint (by simpa [S] using hlocal) (by simpa [S] using hglobal)
        (by simpa [S] using hfive) (by simpa [S] using hmoment)
  have hedgeCard := c40M40_defectEdges_card_two S
    (by simpa [S] using hfive) (by simpa [S] using hmoment)
      (by simpa [S] using hnodisjoint)
  have hdegreeLe := c40M40_defectDegree_le_two S hedgeCard b
    (by simpa [S] using hb)
  have hidentity := c40M40_high_add_defect_eq_two_add_low
    S hpoint (by simpa [S] using hlocal) (by simpa [S] using hglobal)
      (by simpa [S] using hfive) (by simpa [S] using hmoment)
        b (by simpa [S] using hb)
          (fun c hc hbc => hnodisjoint b hb c (by simpa [S] using hc) hbc)
  have hvalues (x : Point) : S.blockDegree 3 x = 6 ∨
      S.blockDegree 3 x = 9 ∨ S.blockDegree 3 x = 12 :=
    elevenFive_c40_threeDegree_values S x
      (by simpa [S] using hlocal x) (by simpa [S] using hC)
  interval_cases hdegree : elevenFiveC40M39DefectDegree S b
  · have hNcard : N.card = 1 := by
      simpa [N, elevenFiveC40M39DefectDegree] using hdegree
    obtain ⟨c, hNeq⟩ := Finset.card_eq_one.mp hNcard
    have hcN : c ∈ N := by rw [hNeq]; simp
    have hcN' := hcN
    change c ∈ ((S.blocksOfSize 5).erase b).filter (fun d =>
      (S.support b ∩ S.support d).card = 1) at hcN'
    have hcData := Finset.mem_filter.mp hcN'
    have hcErase := Finset.mem_erase.mp hcData.1
    have hc : c ∈ S.blocksOfSize 5 := hcErase.2
    have hbc : b ≠ c := Ne.symm hcErase.1
    obtain ⟨p, hpB, _hpC, hpCase⟩ :=
      c40M40_singleton_carrier_two_or_twelveThree
        cfg hpoint hlocal hC (by simpa [S] using hprofile)
          (by simpa [S] using hb) (by simpa [S] using hc) hbc
            (by simpa [S] using hcData.2)
    rcases hpCase with hp2 | ⟨hp3, hp12⟩
    · have hpLow : p ∈ c40M40LowOnFiveBlock S b :=
        Finset.mem_filter.mpr ⟨hpB, by simpa [S] using hp2⟩
      have hlowPos : 0 < (c40M40LowOnFiveBlock S b).card :=
        Finset.card_pos.mpr ⟨p, hpLow⟩
      have hmass := c40M40_threeMass_ge_thirty_add_six_high
        cfg hlocal hC hno944 b hb
      change 30 + 6 * (elevenFiveC40M39HighOnFiveBlock S b).card ≤
        ∑ x ∈ S.support b, S.blockDegree 3 x at hmass
      omega
    · have hmass := c40M40_threeMass_ge_thirtySix_add_six_high
        cfg hlocal hC hno944 b hb p
          (by simpa [S] using hpB) hp3 hp12
      change 36 + 6 * (elevenFiveC40M39HighOnFiveBlock S b).card ≤
        ∑ x ∈ S.support b, S.blockDegree 3 x at hmass
      omega
  · have hNcard : N.card = 2 := by
      simpa [N, elevenFiveC40M39DefectDegree] using hdegree
    obtain ⟨c, d, hcd, hNeq⟩ := Finset.card_eq_two.mp hNcard
    have hcN : c ∈ N := by rw [hNeq]; simp
    have hdN : d ∈ N := by rw [hNeq]; simp
    have hcN' := hcN
    change c ∈ ((S.blocksOfSize 5).erase b).filter (fun e =>
      (S.support b ∩ S.support e).card = 1) at hcN'
    have hdN' := hdN
    change d ∈ ((S.blocksOfSize 5).erase b).filter (fun e =>
      (S.support b ∩ S.support e).card = 1) at hdN'
    have hcData := Finset.mem_filter.mp hcN'
    have hdData := Finset.mem_filter.mp hdN'
    have hcErase := Finset.mem_erase.mp hcData.1
    have hdErase := Finset.mem_erase.mp hdData.1
    have hc : c ∈ S.blocksOfSize 5 := hcErase.2
    have hd : d ∈ S.blocksOfSize 5 := hdErase.2
    have hbc : b ≠ c := Ne.symm hcErase.1
    have hbd : b ≠ d := Ne.symm hdErase.1
    obtain ⟨p, hpB, hpC, hpCase⟩ :=
      c40M40_singleton_carrier_two_or_twelveThree
        cfg hpoint hlocal hC (by simpa [S] using hprofile)
          (by simpa [S] using hb) (by simpa [S] using hc) hbc
            (by simpa [S] using hcData.2)
    obtain ⟨q, hqB, hqD, hqCase⟩ :=
      c40M40_singleton_carrier_two_or_twelveThree
        cfg hpoint hlocal hC (by simpa [S] using hprofile)
          (by simpa [S] using hb) (by simpa [S] using hd) hbd
            (by simpa [S] using hdData.2)
    have hpq : p ≠ q := fiveBlock_two_singleton_neighbours_carriers_ne
      S hpoint (by simpa [S] using hb) hc hd hbc hbd hcd
        (Finset.mem_inter.mpr ⟨hpB, hpC⟩)
        (Finset.mem_inter.mpr ⟨hqB, hqD⟩)
        hcData.2 hdData.2
    rcases hpCase with hp2 | ⟨hp3, hp12⟩ <;>
      rcases hqCase with hq2 | ⟨hq3, hq12⟩
    · let L := (Finset.univ : Finset Point).filter fun x =>
          S.blockDegree 5 x = 2
      have hLcard : L.card = 1 := by
        simpa [L, elevenFiveC40FourteenSevenDegreeCount] using htwo
      change S.blockDegree 5 p = 2 at hp2
      change S.blockDegree 5 q = 2 at hq2
      have hpL : p ∈ L := by simp [L, hp2]
      have hqL : q ∈ L := by simp [L, hq2]
      exact False.elim (hpq
        (Finset.card_le_one.mp (by omega : L.card ≤ 1) p hpL q hqL))
    · have hpLow : p ∈ c40M40LowOnFiveBlock S b :=
        Finset.mem_filter.mpr ⟨hpB, by simpa [S] using hp2⟩
      have hlowPos : 0 < (c40M40LowOnFiveBlock S b).card :=
        Finset.card_pos.mpr ⟨p, hpLow⟩
      have hmass := c40M40_threeMass_ge_thirtySix_add_six_high
        cfg hlocal hC hno944 b hb q
          (by simpa [S] using hqB) hq3 hq12
      change 36 + 6 * (elevenFiveC40M39HighOnFiveBlock S b).card ≤
        ∑ x ∈ S.support b, S.blockDegree 3 x at hmass
      omega
    · have hqLow : q ∈ c40M40LowOnFiveBlock S b :=
        Finset.mem_filter.mpr ⟨hqB, by simpa [S] using hq2⟩
      have hlowPos : 0 < (c40M40LowOnFiveBlock S b).card :=
        Finset.card_pos.mpr ⟨q, hqLow⟩
      have hmass := c40M40_threeMass_ge_thirtySix_add_six_high
        cfg hlocal hC hno944 b hb p
          (by simpa [S] using hpB) hp3 hp12
      change 36 + 6 * (elevenFiveC40M39HighOnFiveBlock S b).card ≤
        ∑ x ∈ S.support b, S.blockDegree 3 x at hmass
      omega
    · exact c40M40_threeMass_ge_fortyTwo_of_two_twelve
        S hvalues b (by simpa [S] using hb) hpq hpB hqB
          (by simpa [S] using hp12) (by simpa [S] using hq12)

/-- If none of the three degree-four five-pivots is neutral, the exact
M40 degree profile sharpens the mixed weighted mass to at most `309`. -/
private theorem c40M40_weighted_three_five_le_309_of_no944
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    (cfg : Configuration Point) (hpoint : Fintype.card Point = 11)
    (hlocal : ∀ p : Point, ElevenFiveLocalRows (blockSystem cfg) p)
    (hglobal : ElevenFiveGlobalRows (blockSystem cfg))
    (hC : (blockSystem cfg).totalCircleCount = 40)
    (hL : elevenFiveLineTotal (blockSystem cfg) = 14)
    (hfive : (blockSystem cfg).blockCount 5 = 7)
    (hmoment : elevenFiveSecondMoment (blockSystem cfg) = 40)
    (hno944 : ∀ p : Point,
      p ∉ elevenFive944Pivots (blockSystem cfg)) :
    (∑ p : Point, (blockSystem cfg).blockDegree 3 p *
      (blockSystem cfg).blockDegree 5 p) ≤ 309 := by
  classical
  let S := blockSystem cfg
  let H := (Finset.univ : Finset Point).filter fun p =>
    S.blockDegree 5 p = 4
  let L := (Finset.univ : Finset Point).filter fun p =>
    S.blockDegree 5 p = 2
  obtain ⟨hfour, _hthree, htwo, hprofile⟩ :=
    elevenFive_c40_l14_b5_seven_secondMoment_forty_profile
      S hpoint (by simpa [S] using hlocal) (by simpa [S] using hglobal)
        (by simpa [S] using hfive) (by simpa [S] using hmoment)
  have hHcard : H.card = 3 := by simpa [H] using hfour
  have hLcard : L.card = 1 := by
    simpa [L, elevenFiveC40FourteenSevenDegreeCount] using htwo
  have hthreeSum : (∑ p : Point, S.blockDegree 3 p) = 93 := by
    obtain ⟨hthreeCount, _hfourCount⟩ :=
      elevenFive_c40_l14_b5_seven_block_census
        S (by simpa [S] using hglobal) (by simpa [S] using hC)
          (by simpa [S] using hL) (by simpa [S] using hfive)
    rw [hglobal.threeIncidence, hthreeCount]
  have hHsum : (∑ p ∈ H, S.blockDegree 3 p) = 36 := by
    calc
      (∑ p ∈ H, S.blockDegree 3 p) = ∑ _p ∈ H, 12 := by
        apply Finset.sum_congr rfl
        intro p hp
        have hp4 : S.blockDegree 5 p = 4 :=
          (Finset.mem_filter.mp hp).2
        exact c40M40_high_three_eq_twelve_of_no944
          cfg hlocal hC hno944 p (by simpa [S] using hp4)
      _ = 36 := by simp [hHcard]
  have hLlower : 6 ≤ ∑ p ∈ L, S.blockDegree 3 p := by
    calc
      6 = ∑ _p ∈ L, 6 := by simp [hLcard]
      _ ≤ ∑ p ∈ L, S.blockDegree 3 p := by
        apply Finset.sum_le_sum
        intro p _hp
        rcases elevenFive_c40_threeDegree_values S p
          (by simpa [S] using hlocal p) (by simpa [S] using hC) with
          h6 | h9 | h12 <;> omega
  have hpointEq (p : Point) :
      S.blockDegree 3 p * S.blockDegree 5 p +
          (if p ∈ L then S.blockDegree 3 p else 0) =
        3 * S.blockDegree 3 p +
          (if p ∈ H then S.blockDegree 3 p else 0) := by
    rcases hprofile p with hp2 | hp3 | hp4
    · simp [H, L, hp2, Nat.mul_comm]
      omega
    · simp [H, L, hp3, Nat.mul_comm]
    · simp [H, L, hp4, Nat.mul_comm]
      omega
  have hsumEq :
      (∑ p : Point, S.blockDegree 3 p * S.blockDegree 5 p) +
          (∑ p ∈ L, S.blockDegree 3 p) =
        3 * (∑ p : Point, S.blockDegree 3 p) +
          (∑ p ∈ H, S.blockDegree 3 p) := by
    have hsum :
        (∑ p : Point,
            (S.blockDegree 3 p * S.blockDegree 5 p +
              (if p ∈ L then S.blockDegree 3 p else 0))) =
          ∑ p : Point,
            (3 * S.blockDegree 3 p +
              (if p ∈ H then S.blockDegree 3 p else 0)) := by
      apply Finset.sum_congr rfl
      intro p _hp
      exact hpointEq p
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
      ← Finset.mul_sum] at hsum
    have hLif :
        (∑ p : Point, if p ∈ L then S.blockDegree 3 p else 0) =
          ∑ p ∈ L, S.blockDegree 3 p := by
      rw [← Finset.sum_filter]
      simp
    have hHif :
        (∑ p : Point, if p ∈ H then S.blockDegree 3 p else 0) =
          ∑ p ∈ H, S.blockDegree 3 p := by
      rw [← Finset.sum_filter]
      simp
    rw [hLif, hHif] at hsum
    exact hsum
  rw [hthreeSum, hHsum] at hsumEq
  change (∑ p : Point, S.blockDegree 3 p * S.blockDegree 5 p) ≤ 309
  omega

/-- Every selected five-block has three-mass at least `42` in the no-`944`
M40 face, whether or not it is incident with a singleton defect. -/
private theorem c40M40_threeMass_ge_fortyTwo
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    (cfg : Configuration Point) (hpoint : Fintype.card Point = 11)
    (hcap : BlockSizeCap (blockSystem cfg) 5)
    (hlocal : ∀ p : Point, ElevenFiveLocalRows (blockSystem cfg) p)
    (hglobal : ElevenFiveGlobalRows (blockSystem cfg))
    (hC : (blockSystem cfg).totalCircleCount = 40)
    (hL : elevenFiveLineTotal (blockSystem cfg) = 14)
    (hfive : (blockSystem cfg).blockCount 5 = 7)
    (hmoment : elevenFiveSecondMoment (blockSystem cfg) = 40)
    (hnodisjoint : ∀ b ∈ (blockSystem cfg).blocksOfSize 5,
      ∀ c ∈ (blockSystem cfg).blocksOfSize 5, b ≠ c →
        ((blockSystem cfg).support b ∩
          (blockSystem cfg).support c).card ≠ 0)
    (hno944 : ∀ p : Point,
      p ∉ elevenFive944Pivots (blockSystem cfg))
    (b : GeometricBlock cfg)
    (hb : b ∈ (blockSystem cfg).blocksOfSize 5) :
    42 ≤ ∑ p ∈ (blockSystem cfg).support b,
      (blockSystem cfg).blockDegree 3 p := by
  by_cases hzero : elevenFiveC40M39DefectDegree (blockSystem cfg) b = 0
  · have hall := elevenFive_c40_m39_all_inter_two_of_defectDegree_zero
      (blockSystem cfg) b hb hzero
        (fun c hc hbc => hnodisjoint b hb c hc hbc)
    have h49 := elevenFive_c40_l14_b5_seven_clean_threeMass_ge_fortyNine
      cfg hpoint hcap hlocal hglobal hC hL hfive b hb
        (fun c hc hcb => hall c hc hcb)
    omega
  · have hdirty :
        0 < elevenFiveC40M39DefectDegree (blockSystem cfg) b := by omega
    exact c40M40_dirty_threeMass_ge_fortyTwo
      cfg hpoint hlocal hglobal hC hfive hmoment hnodisjoint hno944
        b hb hdirty

/-- The purely finite/page-cap branch: moment `40` with no disjoint
five-block pair cannot avoid a neutral `(9,4,4)` pivot. -/
theorem elevenFive_c40_l14_b5_seven_m40_no944_impossible
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    (cfg : Configuration Point) (hpoint : Fintype.card Point = 11)
    (hcap : BlockSizeCap (blockSystem cfg) 5)
    (hlocal : ∀ p : Point, ElevenFiveLocalRows (blockSystem cfg) p)
    (hglobal : ElevenFiveGlobalRows (blockSystem cfg))
    (hC : (blockSystem cfg).totalCircleCount = 40)
    (hL : elevenFiveLineTotal (blockSystem cfg) = 14)
    (hfive : (blockSystem cfg).blockCount 5 = 7)
    (hmoment : elevenFiveSecondMoment (blockSystem cfg) = 40)
    (hnodisjoint : ∀ b ∈ (blockSystem cfg).blocksOfSize 5,
      ∀ c ∈ (blockSystem cfg).blocksOfSize 5, b ≠ c →
        ((blockSystem cfg).support b ∩
          (blockSystem cfg).support c).card ≠ 0)
    (hno944 : ∀ p : Point,
      p ∉ elevenFive944Pivots (blockSystem cfg)) : False := by
  classical
  let S := blockSystem cfg
  let F := S.blocksOfSize 5
  let E := elevenFiveC40M39DefectEdges S
  let D := E.biUnion fun A => A
  let Z := F \ D
  let mass : GeometricBlock cfg → ℕ := fun b =>
    ∑ p ∈ S.support b, S.blockDegree 3 p
  have hFcard : F.card = 7 := by
    simpa [F, S, BlockSystem.blockCount] using hfive
  have hEcard : E.card = 2 := by
    simpa [E] using c40M40_defectEdges_card_two S
      (by simpa [S] using hfive) (by simpa [S] using hmoment)
        (by simpa [S] using hnodisjoint)
  have hedgeCard (A : Finset (GeometricBlock cfg)) (hAE : A ∈ E) :
      A.card = 2 := by
    have hAE' := hAE
    change A ∈ ((S.blocksOfSize 5).powersetCard 2).filter (fun B =>
      (S.commonSupport B).card = 1) at hAE'
    have hpow := (Finset.mem_filter.mp hAE').1
    exact (Finset.mem_powersetCard.mp hpow).2
  have hDsub : D ⊆ F := by
    intro b hbD
    have hbD' : b ∈ E.biUnion (fun A => A) := by
      simpa only [D] using hbD
    rcases Finset.mem_biUnion.mp hbD' with ⟨A, hAE, hbA⟩
    have hAE' := hAE
    change A ∈ ((S.blocksOfSize 5).powersetCard 2).filter (fun B =>
      (S.commonSupport B).card = 1) at hAE'
    have hpow := (Finset.mem_filter.mp hAE').1
    exact (Finset.mem_powersetCard.mp hpow).1 hbA
  have hDcard : D.card ≤ 4 := by
    have hraw : D.card ≤ ∑ A ∈ E, A.card := by
      change (E.biUnion fun A => A).card ≤ ∑ A ∈ E, A.card
      exact Finset.card_biUnion_le
    have hsum : (∑ A ∈ E, A.card) = 4 := by
      calc
        (∑ A ∈ E, A.card) = ∑ _A ∈ E, 2 := by
          apply Finset.sum_congr rfl
          intro A hAE
          exact hedgeCard A hAE
        _ = 4 := by simp [hEcard]
    omega
  have hZsub : Z ⊆ F := Finset.sdiff_subset
  have hZcard : 3 ≤ Z.card := by
    have hcardSplit := Finset.card_sdiff_of_subset hDsub
    change Z.card = F.card - D.card at hcardSplit
    omega
  have hcleanDegree (b : GeometricBlock cfg) (hbZ : b ∈ Z) :
      elevenFiveC40M39DefectDegree S b = 0 := by
    have hbF : b ∈ F := hZsub hbZ
    have hbZ' : b ∈ F \ D := by simpa only [Z] using hbZ
    have hbNotD : b ∉ D := (Finset.mem_sdiff.mp hbZ').2
    by_contra hnot
    have hpos : 0 < elevenFiveC40M39DefectDegree S b := by omega
    let N := elevenFiveC40M39SingletonNeighbours S b
    have hNpos : 0 < N.card := by
      simpa [N, elevenFiveC40M39DefectDegree] using hpos
    obtain ⟨c, hcN⟩ := Finset.card_pos.mp hNpos
    have hcN' := hcN
    change c ∈ ((S.blocksOfSize 5).erase b).filter (fun d =>
      (S.support b ∩ S.support d).card = 1) at hcN'
    have hcData := Finset.mem_filter.mp hcN'
    have hcErase := Finset.mem_erase.mp hcData.1
    let A : Finset (GeometricBlock cfg) := {b, c}
    have hAE : A ∈ E := by
      apply Finset.mem_filter.mpr
      constructor
      · apply Finset.mem_powersetCard.mpr
        constructor
        · intro d hd
          simp only [A, Finset.mem_insert, Finset.mem_singleton] at hd
          rcases hd with rfl | rfl
          · exact hbF
          · exact hcErase.2
        · simp [A, Ne.symm hcErase.1]
      · simpa [A, S.commonSupport_pair] using hcData.2
    apply hbNotD
    apply Finset.mem_biUnion.mpr
    exact ⟨A, by simpa [E] using hAE, by simp [A]⟩
  have hcleanMass (b : GeometricBlock cfg) (hbZ : b ∈ Z) :
      51 ≤ mass b := by
    have hbF : b ∈ F := hZsub hbZ
    have hdegree := hcleanDegree b hbZ
    have hall := elevenFive_c40_m39_all_inter_two_of_defectDegree_zero
      S b (by simpa [F] using hbF) hdegree
        (fun c hc hbc => hnodisjoint b (by simpa [S, F] using hbF)
          c (by simpa [S] using hc) hbc)
    have h49 := elevenFive_c40_l14_b5_seven_clean_threeMass_ge_fortyNine
      cfg hpoint hcap hlocal hglobal hC hL hfive b
        (by simpa [S, F] using hbF)
          (fun c hc hcb => by simpa [S] using hall c (by simpa [S] using hc) hcb)
    have hdvd : 3 ∣ mass b := by
      apply Finset.dvd_sum
      intro p hp
      rcases elevenFive_c40_threeDegree_values S p
        (by simpa [S] using hlocal p) (by simpa [S] using hC) with
        h6 | h9 | h12
      · simp [mass, h6]
      · simp [mass, h9]
      · simp [mass, h12]
    obtain ⟨k, hk⟩ := hdvd
    change 49 ≤ mass b at h49
    omega
  have hmassPoint (b : GeometricBlock cfg) (hbF : b ∈ F) :
      (if b ∈ Z then 51 else 42) ≤ mass b := by
    by_cases hbZ : b ∈ Z
    · simpa [hbZ] using hcleanMass b hbZ
    · have hbCfg : b ∈ (blockSystem cfg).blocksOfSize 5 := by
        change b ∈ S.blocksOfSize 5
        exact hbF
      have h42 := c40M40_threeMass_ge_fortyTwo
        cfg hpoint hcap hlocal hglobal hC hL hfive hmoment
          hnodisjoint hno944 b hbCfg
      change 42 ≤ mass b at h42
      simpa only [hbZ, if_false] using h42
  have hmassLower :
      (∑ b ∈ F, (if b ∈ Z then 51 else 42)) ≤
        ∑ b ∈ F, mass b :=
    Finset.sum_le_sum fun b hb => hmassPoint b hb
  have hweightLower :
      321 ≤ ∑ b ∈ F, (if b ∈ Z then 51 else 42) := by
    have hfilter : F.filter (fun b => b ∈ Z) = Z := by
      ext b
      simp only [Finset.mem_filter]
      constructor
      · exact fun h => h.2
      · exact fun hbZ => ⟨hZsub hbZ, hbZ⟩
    have hnineIndicator :
        (∑ b ∈ F, if b ∈ Z then 9 else 0) = 9 * Z.card := by
      calc
        (∑ b ∈ F, if b ∈ Z then 9 else 0) =
            ∑ _b ∈ F.filter (fun b => b ∈ Z), 9 := by
              rw [Finset.sum_filter]
        _ = ∑ _b ∈ Z, 9 := by rw [hfilter]
        _ = 9 * Z.card := by simp [Nat.mul_comm]
    have hweightEq :
        (∑ b ∈ F, (if b ∈ Z then 51 else 42)) =
          42 * F.card + 9 * Z.card := by
      calc
        (∑ b ∈ F, (if b ∈ Z then 51 else 42)) =
            ∑ b ∈ F, (42 + if b ∈ Z then 9 else 0) := by
          apply Finset.sum_congr rfl
          intro b _hb
          by_cases hbZ : b ∈ Z <;> simp [hbZ]
        _ = 42 * F.card + 9 * Z.card := by
          rw [Finset.sum_add_distrib, hnineIndicator]
          simp [Nat.mul_comm]
    rw [hweightEq, hFcard]
    omega
  have hfubini := elevenFive_fiveBlock_threeMass_sum_eq_weighted S
  have hmassWeighted :
      (∑ b ∈ F, mass b) =
        ∑ p : Point, S.blockDegree 3 p * S.blockDegree 5 p := by
    simpa [F, mass] using hfubini
  have hupper := c40M40_weighted_three_five_le_309_of_no944
    cfg hpoint hlocal hglobal hC hL hfive hmoment hno944
  have hupperS :
      (∑ p : Point, S.blockDegree 3 p * S.blockDegree 5 p) ≤ 309 := by
    simpa [S] using hupper
  rw [hmassWeighted] at hmassLower
  omega

/-! ## The actual `944` branch -/

private theorem c40M40_lineCount_five_eq_zero
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    (cfg : Configuration Point)
    (hglobal : ElevenFiveGlobalRows (blockSystem cfg))
    (hC : (blockSystem cfg).totalCircleCount = 40)
    (hL : elevenFiveLineTotal (blockSystem cfg) = 14)
    (hfive : (blockSystem cfg).blockCount 5 = 7) :
    (blockSystem cfg).lineCount 5 = 0 := by
  have hcut := elevenFive_k4_cut (blockSystem cfg) hglobal hC hL
  omega

/-- The three size-five circles not through a degree-four pivot. -/
structure ElevenFiveC40M40OppositeCircleFamily
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    (cfg : Configuration Point) (p : Point) where
  block : Fin 3 → GeometricBlock cfg
  block_five : ∀ t, block t ∈ (blockSystem cfg).blocksOfSize 5
  pivot_not_mem : ∀ t, p ∉ geometricBlockSupport cfg (block t)
  block_injective : Function.Injective block
  circle : Fin 3 → DeterminedCircle cfg
  block_eq_circle : ∀ t, block t = Sum.inr (circle t)

private noncomputable def elevenFive_c40_m40_oppositeCircleFamily
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    (cfg : Configuration Point) (p : Point)
    (hp4 : (blockSystem cfg).blockDegree 5 p = 4)
    (hfive : (blockSystem cfg).blockCount 5 = 7)
    (hlineFive : (blockSystem cfg).lineCount 5 = 0) :
    ElevenFiveC40M40OppositeCircleFamily cfg p := by
  classical
  let S := blockSystem cfg
  let F := S.blocksOfSize 5
  let P := F.filter fun b => p ∈ S.support b
  let O := F.filter fun b => p ∉ S.support b
  have hFcard : F.card = 7 := by
    simpa [F, S, BlockSystem.blockCount] using hfive
  have hPcard : P.card = 4 := by
    simpa [P, F, S, BlockSystem.blockDegree, BlockSystem.degreeIn] using hp4
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := F) (p := fun b => p ∈ S.support b)
  have hOcard : O.card = 3 := by
    change P.card + O.card = F.card at hsplit
    omega
  let index : Fin 3 ≃ ↑O := (Finset.equivFinOfCardEq hOcard).symm
  let block : Fin 3 → GeometricBlock cfg := fun t => (index t).1
  have hblockFive (t : Fin 3) : block t ∈ S.blocksOfSize 5 := by
    exact (Finset.mem_filter.mp (index t).2).1
  have hpNot (t : Fin 3) : p ∉ S.support (block t) := by
    exact (Finset.mem_filter.mp (index t).2).2
  have hblockInj : Function.Injective block := by
    intro t v htv
    apply index.injective
    exact Subtype.ext htv
  have hblockCircle (t : Fin 3) :
      ∃ Gamma : DeterminedCircle cfg, block t = Sum.inr Gamma := by
    cases hbt : block t with
    | inl L =>
        have hbLine : (Sum.inl L : GeometricBlock cfg) ∈
            S.lineBlocksOfSize 5 := by
          apply S.mem_blocksOfKindSize.mpr
          refine ⟨?_, S.mem_blocksOfSize.mp (by simpa [hbt] using hblockFive t)⟩
          simp [S, blockSystem, geometricBlockSystem, geometricBlockKind]
        have hlineCard : (S.lineBlocksOfSize 5).card = 0 := by
          simpa [BlockSystem.lineCount] using hlineFive
        exact False.elim (by
          have hpositive := Finset.card_pos.mpr ⟨Sum.inl L, hbLine⟩
          omega)
    | inr Gamma => exact ⟨Gamma, rfl⟩
  choose circle hcircle using hblockCircle
  exact
    { block := block
      block_five := fun t => by simpa [S] using hblockFive t
      pivot_not_mem := fun t => by
        simpa [S, blockSystem, geometricBlockSystem,
          geometricBlockSupport] using hpNot t
      block_injective := hblockInj
      circle := circle
      block_eq_circle := hcircle }

noncomputable def ElevenFiveC40M40OppositeCircleFamily.awayTrace
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (T : ElevenFiveC40M40OppositeCircleFamily cfg p) (t : Fin 3) :
    Finset (AwayFrom p) :=
  awaySupport p (geometricBlockSupport cfg (T.block t))

private theorem ElevenFiveC40M40OppositeCircleFamily.awayTrace_card
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (T : ElevenFiveC40M40OppositeCircleFamily cfg p) (t : Fin 3) :
    (T.awayTrace t).card = 5 := by
  rw [ElevenFiveC40M40OppositeCircleFamily.awayTrace,
    card_awaySupport_of_not_mem]
  · exact (blockSystem cfg).mem_blocksOfSize.mp (T.block_five t)
  · exact T.pivot_not_mem t

private theorem ElevenFiveC40M40OppositeCircleFamily.pivot_not_mem_circle
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (T : ElevenFiveC40M40OppositeCircleFamily cfg p) (t : Fin 3) :
    cfg p ∉ ((T.circle t).1 : Set Point2) := by
  intro hp
  apply T.pivot_not_mem t
  rw [T.block_eq_circle t]
  exact mem_circleTrace.mpr hp

noncomputable def ElevenFiveC40M40OppositeCircleFamily.invertedCircle
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (T : ElevenFiveC40M40OppositeCircleFamily cfg p) (t : Fin 3) :
    ProperCircle :=
  invertedProperCircle (cfg p) (T.circle t).1
    (T.pivot_not_mem_circle t)

private theorem ElevenFiveC40M40OppositeCircleFamily.awayTrace_on_invertedCircle
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (T : ElevenFiveC40M40OppositeCircleFamily cfg p) (t : Fin 3) :
    T.awayTrace t ⊆
      circleTrace (pivotInversion cfg p) (T.invertedCircle t) := by
  intro q hq
  have hqBlock : q.1 ∈ geometricBlockSupport cfg (T.block t) :=
    mem_awaySupport.mp hq
  have hqCircle : cfg q.1 ∈ ((T.circle t).1 : Set Point2) := by
    apply mem_circleTrace.mp
    rw [T.block_eq_circle t] at hqBlock
    simpa only [geometricBlockSupport] using hqBlock
  apply mem_circleTrace.mpr
  simpa [ElevenFiveC40M40OppositeCircleFamily.invertedCircle,
    pivotInversion] using
      inversion_mem_invertedProperCircle (cfg p) (cfg q.1)
        (T.circle t).1 (T.pivot_not_mem_circle t) hqCircle

private theorem ElevenFiveC40M40OppositeCircleFamily.baseIntersection_one_or_two
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (T : ElevenFiveC40M40OppositeCircleFamily cfg p)
    (H : ElevenFivePivotInvertedFourStar cfg p)
    (hnodisjoint : ∀ b ∈ (blockSystem cfg).blocksOfSize 5,
      ∀ c ∈ (blockSystem cfg).blocksOfSize 5, b ≠ c →
        ((blockSystem cfg).support b ∩
          (blockSystem cfg).support c).card ≠ 0)
    (t : Fin 3) (i : Fin 4) :
    (geometricBlockSupport cfg (T.block t) ∩
      geometricBlockSupport cfg (H.baseBlock i)).card = 1 ∨
    (geometricBlockSupport cfg (T.block t) ∩
      geometricBlockSupport cfg (H.baseBlock i)).card = 2 := by
  let S := blockSystem cfg
  have hne : T.block t ≠ H.baseBlock i := by
    intro h
    apply T.pivot_not_mem t
    rw [h]
    exact H.baseBlock_pivot i
  have hpos := hnodisjoint (T.block t) (T.block_five t)
    (H.baseBlock i) (H.baseBlock_five i) hne
  have hlt := S.distinct_block_inter_card_lt_three hne
  change (geometricBlockSupport cfg (T.block t) ∩
    geometricBlockSupport cfg (H.baseBlock i)).card < 3 at hlt
  change (geometricBlockSupport cfg (T.block t) ∩
    geometricBlockSupport cfg (H.baseBlock i)).card ≠ 0 at hpos
  omega

private theorem ElevenFiveC40M40OppositeCircleFamily.away_baseIntersection_card
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (T : ElevenFiveC40M40OppositeCircleFamily cfg p)
    (H : ElevenFivePivotInvertedFourStar cfg p)
    (t : Fin 3) (i : Fin 4) :
    (T.awayTrace t ∩ H.baseSupport i).card =
      (geometricBlockSupport cfg (T.block t) ∩
        geometricBlockSupport cfg (H.baseBlock i)).card := by
  rw [ElevenFiveC40M40OppositeCircleFamily.awayTrace,
    H.baseBlock_support, awaySupport_inter,
    card_awaySupport_of_not_mem]
  exact fun hp => T.pivot_not_mem t (Finset.mem_inter.mp hp).1

private theorem ElevenFiveC40M40OppositeCircleFamily.away_meets
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (T : ElevenFiveC40M40OppositeCircleFamily cfg p)
    (H : ElevenFivePivotInvertedFourStar cfg p)
    (hnodisjoint : ∀ b ∈ (blockSystem cfg).blocksOfSize 5,
      ∀ c ∈ (blockSystem cfg).blocksOfSize 5, b ≠ c →
        ((blockSystem cfg).support b ∩
          (blockSystem cfg).support c).card ≠ 0)
    (t : Fin 3) (i : Fin 4) :
    (T.awayTrace t ∩ H.baseSupport i).Nonempty := by
  apply Finset.card_pos.mp
  rw [T.away_baseIntersection_card H t i]
  rcases T.baseIntersection_one_or_two H hnodisjoint t i with h | h <;>
    omega

private theorem ElevenFiveC40M40OppositeCircleFamily.away_upper
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (T : ElevenFiveC40M40OppositeCircleFamily cfg p)
    (H : ElevenFivePivotInvertedFourStar cfg p)
    (hnodisjoint : ∀ b ∈ (blockSystem cfg).blocksOfSize 5,
      ∀ c ∈ (blockSystem cfg).blocksOfSize 5, b ≠ c →
        ((blockSystem cfg).support b ∩
          (blockSystem cfg).support c).card ≠ 0)
    (t : Fin 3) (i : Fin 4) :
    (T.awayTrace t ∩ H.baseSupport i).card ≤ 2 := by
  rw [T.away_baseIntersection_card H t i]
  rcases T.baseIntersection_one_or_two H hnodisjoint t i with h | h <;>
    omega

private theorem ElevenFiveC40M40OppositeCircleFamily.singletonBaseIndices_card_le_two
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (T : ElevenFiveC40M40OppositeCircleFamily cfg p)
    (H : ElevenFivePivotInvertedFourStar cfg p)
    (hdefectCard :
      (elevenFiveC40M39DefectEdges (blockSystem cfg)).card = 2)
    (t : Fin 3) :
    ((Finset.univ : Finset (Fin 4)).filter fun i =>
      (geometricBlockSupport cfg (T.block t) ∩
        geometricBlockSupport cfg (H.baseBlock i)).card = 1).card ≤ 2 := by
  classical
  let S := blockSystem cfg
  let I := (Finset.univ : Finset (Fin 4)).filter fun i =>
    (S.support (T.block t) ∩ S.support (H.baseBlock i)).card = 1
  let N := elevenFiveC40M39SingletonNeighbours S (T.block t)
  have hNle : N.card ≤ 2 :=
    c40M40_defectDegree_le_two S hdefectCard (T.block t) (T.block_five t)
  have hbaseN (i : Fin 4) (hi : i ∈ I) : H.baseBlock i ∈ N := by
    have hi' : i ∈ (Finset.univ : Finset (Fin 4)).filter (fun i =>
        (S.support (T.block t) ∩ S.support (H.baseBlock i)).card = 1) := by
      simpa only [I] using hi
    have hiOne := (Finset.mem_filter.mp hi').2
    have hne : H.baseBlock i ≠ T.block t := by
      intro h
      apply T.pivot_not_mem t
      rw [← h]
      exact H.baseBlock_pivot i
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_erase.mpr ⟨hne, H.baseBlock_five i⟩, hiOne⟩
  let f : {i // i ∈ I} → {b // b ∈ N} := fun i =>
    ⟨H.baseBlock i.1, hbaseN i.1 i.2⟩
  have hf : Function.Injective f := by
    intro i j hij
    apply Subtype.ext
    apply H.baseBlock_injective
    have hval := congrArg Subtype.val hij
    simpa only [f] using hval
  have hle := Fintype.card_le_of_injective f hf
  have hle' : I.card ≤ N.card := by
    simpa only [Fintype.card_coe] using hle
  change I.card ≤ 2
  omega

private theorem ElevenFiveC40M40OppositeCircleFamily.away_sum_cases
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (T : ElevenFiveC40M40OppositeCircleFamily cfg p)
    (H : ElevenFivePivotInvertedFourStar cfg p)
    (hnodisjoint : ∀ b ∈ (blockSystem cfg).blocksOfSize 5,
      ∀ c ∈ (blockSystem cfg).blocksOfSize 5, b ≠ c →
        ((blockSystem cfg).support b ∩
          (blockSystem cfg).support c).card ≠ 0)
    (hdefectCard :
      (elevenFiveC40M39DefectEdges (blockSystem cfg)).card = 2)
    (t : Fin 3) :
    (∑ i : Fin 4, (T.awayTrace t ∩ H.baseSupport i).card) = 6 ∨
    (∑ i : Fin 4, (T.awayTrace t ∩ H.baseSupport i).card) = 7 ∨
    (∑ i : Fin 4, (T.awayTrace t ∩ H.baseSupport i).card) = 8 := by
  classical
  let d : Fin 4 → ℕ := fun i =>
    (T.awayTrace t ∩ H.baseSupport i).card
  let I := (Finset.univ : Finset (Fin 4)).filter fun i => d i = 1
  have hvalues (i : Fin 4) : d i = 1 ∨ d i = 2 := by
    change (T.awayTrace t ∩ H.baseSupport i).card = 1 ∨
      (T.awayTrace t ∩ H.baseSupport i).card = 2
    rw [T.away_baseIntersection_card H t i]
    exact T.baseIntersection_one_or_two H hnodisjoint t i
  have hIle : I.card ≤ 2 := by
    have hraw := T.singletonBaseIndices_card_le_two H hdefectCard t
    have hIEq : I = (Finset.univ : Finset (Fin 4)).filter fun i =>
        (geometricBlockSupport cfg (T.block t) ∩
          geometricBlockSupport cfg (H.baseBlock i)).card = 1 := by
      ext i
      simp only [I, d, Finset.mem_filter, Finset.mem_univ, true_and]
      rw [T.away_baseIntersection_card H t i]
    rw [hIEq]
    exact hraw
  have hid : (∑ i : Fin 4, d i) + I.card = 8 := by
    calc
      (∑ i : Fin 4, d i) + I.card =
          ∑ i : Fin 4, (d i + if d i = 1 then 1 else 0) := by
        rw [Finset.card_eq_sum_ones, Finset.sum_filter,
          Finset.sum_add_distrib]
      _ = ∑ _i : Fin 4, 2 := by
        apply Finset.sum_congr rfl
        intro i _hi
        rcases hvalues i with hi | hi <;> simp [hi]
      _ = 8 := by norm_num
  change (∑ i : Fin 4, d i) = 6 ∨
    (∑ i : Fin 4, d i) = 7 ∨ (∑ i : Fin 4, d i) = 8
  omega

noncomputable def ElevenFiveC40M40OppositeCircleFamily.traceRisk
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (T : ElevenFiveC40M40OppositeCircleFamily cfg p)
    (H : ElevenFivePivotInvertedFourStar cfg p)
    (hnodisjoint : ∀ b ∈ (blockSystem cfg).blocksOfSize 5,
      ∀ c ∈ (blockSystem cfg).blocksOfSize 5, b ≠ c →
        ((blockSystem cfg).support b ∩
          (blockSystem cfg).support c).card ≠ 0)
    (hdefectCard :
      (elevenFiveC40M39DefectEdges (blockSystem cfg)).card = 2)
    (t : Fin 3) : FourStarFiveTraceRisk H (T.awayTrace t) := by
  apply H.fiveTraceRisk_of_sum_cases
  · exact T.awayTrace_card t
  · exact T.away_meets H hnodisjoint t
  · exact T.away_upper H hnodisjoint t
  · exact T.away_sum_cases H hnodisjoint hdefectCard t

private theorem c40M40_risk_cross_eq_of_edge_eq
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

private theorem ElevenFiveC40M40OppositeCircleFamily.traceRisk_edge_injective
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (T : ElevenFiveC40M40OppositeCircleFamily cfg p)
    (H : ElevenFivePivotInvertedFourStar cfg p)
    (hnodisjoint : ∀ b ∈ (blockSystem cfg).blocksOfSize 5,
      ∀ c ∈ (blockSystem cfg).blocksOfSize 5, b ≠ c →
        ((blockSystem cfg).support b ∩
          (blockSystem cfg).support c).card ≠ 0)
    (hdefectCard :
      (elevenFiveC40M39DefectEdges (blockSystem cfg)).card = 2) :
    Function.Injective fun t : Fin 3 =>
      (T.traceRisk H hnodisjoint hdefectCard t).edge := by
  classical
  intro t v hedge
  by_contra htv
  let Rt := T.traceRisk H hnodisjoint hdefectCard t
  let Rv := T.traceRisk H hnodisjoint hdefectCard v
  have hblocks : T.block t ≠ T.block v := by
    intro hblocks
    exact htv (T.block_injective hblocks)
  have hedgeCard : Rt.edge.card = 2 :=
    (Finset.mem_powersetCard.mp Rt.edge_mem).2
  obtain ⟨i, j, hij, hedgeEq⟩ := Finset.card_eq_two.mp hedgeCard
  have hiRt : i ∈ Rt.edge := by rw [hedgeEq]; simp
  have hjRt : j ∈ Rt.edge := by rw [hedgeEq]; simp
  have hedge' : Rt.edge = Rv.edge := by simpa only [Rt, Rv] using hedge
  have hiRv : i ∈ Rv.edge := by rw [← hedge']; exact hiRt
  have hjRv : j ∈ Rv.edge := by rw [← hedge']; exact hjRt
  let x := H.basePairIntersection Rt.oppositeFirst Rt.oppositeSecond Rt.opposite_ne
  have hcrossEq : x =
      H.basePairIntersection Rv.oppositeFirst Rv.oppositeSecond Rv.opposite_ne :=
    c40M40_risk_cross_eq_of_edge_eq Rt Rv hedge'
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
  have hAt : A ⊆ geometricBlockSupport cfg (T.block t) := by
    intro y hy
    simp only [A, Finset.mem_insert, Finset.mem_singleton] at hy
    rcases hy with rfl | rfl | rfl
    · exact mem_awaySupport.mp (Rt.private_mem i hiRt)
    · exact mem_awaySupport.mp (Rt.private_mem j hjRt)
    · exact mem_awaySupport.mp Rt.cross_mem
  have hAv : A ⊆ geometricBlockSupport cfg (T.block v) := by
    intro y hy
    simp only [A, Finset.mem_insert, Finset.mem_singleton] at hy
    rcases hy with rfl | rfl | rfl
    · exact mem_awaySupport.mp (Rv.private_mem i hiRv)
    · exact mem_awaySupport.mp (Rv.private_mem j hjRv)
    · apply mem_awaySupport.mp
      rw [hcrossEq]
      exact Rv.cross_mem
  have hsub : A ⊆ geometricBlockSupport cfg (T.block t) ∩
      geometricBlockSupport cfg (T.block v) := fun y hy =>
    Finset.mem_inter.mpr ⟨hAt hy, hAv hy⟩
  have hle := Finset.card_le_card hsub
  have hlt := (blockSystem cfg).distinct_block_inter_card_lt_three hblocks
  change (geometricBlockSupport cfg (T.block t) ∩
    geometricBlockSupport cfg (T.block v)).card < 3 at hlt
  rw [hAcard] at hle
  omega

noncomputable def ElevenFiveC40M40OppositeCircleFamily.riskFamily
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (T : ElevenFiveC40M40OppositeCircleFamily cfg p)
    (H : ElevenFivePivotInvertedFourStar cfg p)
    (hnodisjoint : ∀ b ∈ (blockSystem cfg).blocksOfSize 5,
      ∀ c ∈ (blockSystem cfg).blocksOfSize 5, b ≠ c →
        ((blockSystem cfg).support b ∩
          (blockSystem cfg).support c).card ≠ 0)
    (hdefectCard :
      (elevenFiveC40M39DefectEdges (blockSystem cfg)).card = 2) :
    FourStarThreeFiveTraceRiskFamily H where
  trace := T.awayTrace
  traceRisk := T.traceRisk H hnodisjoint hdefectCard
  edge_injective := T.traceRisk_edge_injective H hnodisjoint hdefectCard
  circle := T.invertedCircle
  trace_on_circle := T.awayTrace_on_invertedCircle

/-- A neutral pivot in the no-disjoint M40 face supplies three opposite
proper-circle risks, so the actual four-star endpoint is contradictory. -/
theorem elevenFive_c40_l14_b5_seven_m40_944_impossible
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    (cfg : Configuration Point) (hpoint : Fintype.card Point = 11)
    (hglobal : ElevenFiveGlobalRows (blockSystem cfg))
    (hC : (blockSystem cfg).totalCircleCount = 40)
    (hL : elevenFiveLineTotal (blockSystem cfg) = 14)
    (hfive : (blockSystem cfg).blockCount 5 = 7)
    (hmoment : elevenFiveSecondMoment (blockSystem cfg) = 40)
    (hnodisjoint : ∀ b ∈ (blockSystem cfg).blocksOfSize 5,
      ∀ c ∈ (blockSystem cfg).blocksOfSize 5, b ≠ c →
        ((blockSystem cfg).support b ∩
          (blockSystem cfg).support c).card ≠ 0)
    (p : Point) (hp : p ∈ elevenFive944Pivots (blockSystem cfg)) : False := by
  classical
  let H := elevenFive944PivotFourStar cfg hpoint p hp
  have hp4 : (blockSystem cfg).blockDegree 5 p = 4 :=
    blockDegree_five_eq_four_of_mem_elevenFive944Pivots hp
  have hlineFive := c40M40_lineCount_five_eq_zero
    cfg hglobal hC hL hfive
  let T := elevenFive_c40_m40_oppositeCircleFamily
    cfg p hp4 hfive hlineFive
  have hdefectCard := c40M40_defectEdges_card_two (blockSystem cfg)
    hfive hmoment hnodisjoint
  exact (T.riskFamily H hnodisjoint hdefectCard).impossible

/-- Full moment-40 no-disjoint endpoint, with no residual finite or
external-trace hypothesis. -/
theorem elevenFive_c40_l14_b5_seven_m40_noDisjoint_impossible
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    (cfg : Configuration Point) (hpoint : Fintype.card Point = 11)
    (hcap : BlockSizeCap (blockSystem cfg) 5)
    (hlocal : ∀ p : Point, ElevenFiveLocalRows (blockSystem cfg) p)
    (hglobal : ElevenFiveGlobalRows (blockSystem cfg))
    (hC : (blockSystem cfg).totalCircleCount = 40)
    (hL : elevenFiveLineTotal (blockSystem cfg) = 14)
    (hfive : (blockSystem cfg).blockCount 5 = 7)
    (hmoment : elevenFiveSecondMoment (blockSystem cfg) = 40)
    (hnodisjoint : ∀ b ∈ (blockSystem cfg).blocksOfSize 5,
      ∀ c ∈ (blockSystem cfg).blocksOfSize 5, b ≠ c →
        ((blockSystem cfg).support b ∩
          (blockSystem cfg).support c).card ≠ 0) : False := by
  classical
  by_cases hex : ∃ p : Point,
      p ∈ elevenFive944Pivots (blockSystem cfg)
  · obtain ⟨p, hp⟩ := hex
    exact elevenFive_c40_l14_b5_seven_m40_944_impossible
      cfg hpoint hglobal hC hL hfive hmoment hnodisjoint p hp
  · apply elevenFive_c40_l14_b5_seven_m40_no944_impossible
      cfg hpoint hcap hlocal hglobal hC hL hfive hmoment hnodisjoint
    intro p hp
    exact hex ⟨p, hp⟩

end Erdos506.V1
