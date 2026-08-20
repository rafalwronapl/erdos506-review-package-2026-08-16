import Erdos506.V1.ElevenFiveC39H28ZeroFibrePageCap
import Erdos506.V1.ElevenFiveC39H28SingletonDoubleCountFinish
import Mathlib.Tactic

/-!
# Closing the C39 H28 singleton-or-disjoint router

The H28 page cap routes every proper size-five circle either to a singleton
size-five neighbour or to a disjoint size-five neighbour.  This file closes
that weaker alternative globally.

The finite observation is that, for five or six size-five blocks on eleven
points with five-degree at most four, the pair moment is at most three below
its all-double maximum.  A disjoint pair costs two units.  It is therefore
the unique disjoint pair, so every block outside its two endpoints must be
covered by a singleton pair.  At least two singleton pairs are needed, which
cost two further units, a contradiction.  If there is no disjoint pair, the
existing singleton-graph double count applies unchanged.
-/

namespace Erdos506.V1

open Erdos506.Block
open Erdos506.Block.BlockSystem
open Erdos506.Incidence
open Erdos506.V3
open Erdos506.V4
open scoped BigOperators

universe u v

private theorem c39H28_mixed_hostTotal_le
    {Point : Type u} {Block : Type v} [Fintype Point] [Fintype Block]
    [DecidableEq Point]
    (S : BlockSystem Point Block) (hcard : Fintype.card Point = 11)
    (hcircle : ∀ b ∈ S.circleBlocksOfSize 5,
      elevenFiveHostWeight S (S.support b) ≤ 28) :
    elevenFiveFiveBlockHostTotal S ≤
      28 * S.blockCount 5 + 2 * S.lineCount 5 := by
  classical
  have hpoint (b : Block) (hb : b ∈ S.blocksOfSize 5) :
      elevenFiveHostWeight S (S.support b) ≤
        28 + 2 * (if S.kind b = .line then 1 else 0) := by
    have hsize := S.mem_blocksOfSize.mp hb
    cases hkind : S.kind b with
    | line =>
        have hthirty := elevenFiveHostWeight_le_thirty S (S.support b)
          hcard hsize
        simp [hkind]
        omega
    | circle =>
        have hmem : b ∈ S.circleBlocksOfSize 5 :=
          S.mem_blocksOfKindSize.mpr ⟨hkind, hsize⟩
        have htwentyEight := hcircle b hmem
        simp [hkind]
        omega
  have hsum := Finset.sum_le_sum fun b hb => hpoint b hb
  have hindicator :
      (∑ b ∈ S.blocksOfSize 5,
        if S.kind b = .line then 1 else 0) = S.lineCount 5 := by
    rw [← Finset.sum_filter]
    have hfilter : (S.blocksOfSize 5).filter
        (fun b => S.kind b = .line) = S.lineBlocksOfSize 5 := by
      ext b
      simp [BlockSystem.blocksOfSize, BlockSystem.blocksOfKindSize,
        BlockSystem.blocksOfKind, and_comm]
    rw [hfilter]
    simp [BlockSystem.lineCount]
  have hright :
      (∑ b ∈ S.blocksOfSize 5,
        (28 + 2 * (if S.kind b = .line then 1 else 0))) =
        28 * S.blockCount 5 + 2 * S.lineCount 5 := by
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, hindicator]
    simp [BlockSystem.blockCount, Nat.mul_comm]
  change (∑ b ∈ S.blocksOfSize 5,
    elevenFiveHostWeight S (S.support b)) ≤ _
  rw [hright] at hsum
  exact hsum

private theorem c39H28_twice_degree_le_choose_add_three (z : Nat)
    (hz : z ≤ 4) : 2 * z ≤ Nat.choose z 2 + 3 := by
  interval_cases z <;> norm_num [Nat.choose]

/-- Pure finite core of the mixed-neighbour argument.  Once one disjoint
pair exists, a five- or six-member size-five family cannot give every block
either a singleton neighbour or a disjoint neighbour. -/
theorem fiveBlock_singletonOrDisjoint_absurd_of_five_or_six
    {Point : Type u} {Block : Type v} [Fintype Point] [Fintype Block]
    [DecidableEq Point] [DecidableEq Block]
    (S : BlockSystem Point Block)
    (hpoint : Fintype.card Point = 11)
    (hdegree : ∀ p : Point, S.blockDegree 5 p ≤ 4)
    (hfive : S.blockCount 5 = 5 ∨ S.blockCount 5 = 6)
    (hneighbour : ∀ b ∈ S.blocksOfSize 5,
      (∃ c, c ∈ S.blocksOfSize 5 ∧ b ≠ c ∧
        (S.support b ∩ S.support c).card = 1) ∨
      (∃ c, c ∈ S.blocksOfSize 5 ∧ b ≠ c ∧
        (S.support b ∩ S.support c).card = 0))
    (hdisjoint : ∃ f, f ∈ S.blocksOfSize 5 ∧
      ∃ g, g ∈ S.blocksOfSize 5 ∧ f ≠ g ∧
        (S.support f ∩ S.support g).card = 0) : False := by
  classical
  let F := S.blocksOfSize 5
  let Q := F.powersetCard 2
  let q : Finset Block → Nat := fun A => (S.commonSupport A).card
  let Z := Q.filter fun A => q A = 0
  let O := Q.filter fun A => q A = 1

  have hFcases : F.card = 5 ∨ F.card = 6 := by
    simpa [F, BlockSystem.blockCount] using hfive

  have hdegreeMoment :
      10 * F.card ≤ elevenFiveSecondMoment S + 33 := by
    have hsum := Finset.sum_le_sum
      (s := (Finset.univ : Finset Point)) fun p _hp =>
        c39H28_twice_degree_le_choose_add_three
          (S.blockDegree 5 p) (hdegree p)
    have hleft :
        (∑ p : Point, 2 * S.blockDegree 5 p) = 10 * F.card := by
      rw [← Finset.mul_sum, S.block_incidence 5]
      change 2 * (5 * S.blockCount 5) = 10 * S.blockCount 5
      omega
    have hright :
        (∑ p : Point, (Nat.choose (S.blockDegree 5 p) 2 + 3)) =
          elevenFiveSecondMoment S + 33 := by
      simp [elevenFiveSecondMoment, Finset.sum_add_distrib, hpoint]
    rw [hleft, hright] at hsum
    exact hsum

  have hterm (A : Finset Block) (hA : A ∈ Q) :
      q A + (if q A = 0 then 2 else 0) +
          (if q A = 1 then 1 else 0) ≤ 2 := by
    have hA' : A ∈ F.powersetCard 2 := by simpa [Q] using hA
    have hqLe : q A ≤ 2 := by
      dsimp [q]
      exact S.commonSupport_card_le_two
        (Finset.mem_powersetCard.mp hA').2
    interval_cases hq : q A <;> simp [hq]

  have hqsum : (∑ A ∈ Q, q A) = elevenFiveSecondMoment S := by
    change (∑ A ∈ F.powersetCard 2, (S.commonSupport A).card) =
      ∑ p : Point, Nat.choose (S.degreeIn F p) 2
    exact (S.binomial_degree_moment F 2).symm
  have hZsum :
      (∑ A ∈ Q, if q A = 0 then 2 else 0) = 2 * Z.card := by
    rw [← Finset.sum_filter]
    simp [Z, Nat.mul_comm]
  have hOsum :
      (∑ A ∈ Q, if q A = 1 then 1 else 0) = O.card := by
    rw [← Finset.sum_filter]
    simp [O]
  have hconstant :
      (∑ _A ∈ Q, 2) = 2 * Nat.choose F.card 2 := by
    simp [Q, Nat.mul_comm]
  have hpairBudget :
      elevenFiveSecondMoment S + 2 * Z.card + O.card ≤
        2 * Nat.choose F.card 2 := by
    have hsum := Finset.sum_le_sum fun A hA => hterm A hA
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
      hqsum, hZsum, hOsum, hconstant] at hsum
    exact hsum
  have hdefect : 2 * Z.card + O.card ≤ 3 := by
    rcases hFcases with hFfive | hFsix
    · rw [hFfive] at hdegreeMoment hpairBudget
      norm_num [Nat.choose] at hdegreeMoment hpairBudget
      omega
    · rw [hFsix] at hdegreeMoment hpairBudget
      norm_num [Nat.choose] at hdegreeMoment hpairBudget
      omega

  have hpairMem {b c : Block} (hb : b ∈ F) (hc : c ∈ F)
      (hbc : b ≠ c) : ({b, c} : Finset Block) ∈ Q := by
    change ({b, c} : Finset Block) ∈ F.powersetCard 2
    refine Finset.mem_powersetCard.mpr ⟨?_, ?_⟩
    · intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact hb
      · exact hc
    · simp [hbc]

  obtain ⟨f, hf, g, hg, hfg, hfgZero⟩ := hdisjoint
  have hfF : f ∈ F := by simpa [F] using hf
  have hgF : g ∈ F := by simpa [F] using hg
  let z : Finset Block := {f, g}
  have hzQ : z ∈ Q := by simpa [z] using hpairMem hfF hgF hfg
  have hqz : q z = 0 := by
    dsimp [q, z]
    rw [S.commonSupport_pair]
    exact hfgZero
  have hzZ : z ∈ Z := Finset.mem_filter.mpr ⟨hzQ, hqz⟩
  have hZpos : 0 < Z.card := Finset.card_pos.mpr ⟨z, hzZ⟩
  have hZleOne : Z.card ≤ 1 := by omega

  let C : Finset Block := O.biUnion fun A => A
  have hcover : F \ z ⊆ C := by
    intro b hb
    have hbF : b ∈ F := (Finset.mem_sdiff.mp hb).1
    have hbNotZ : b ∉ z := (Finset.mem_sdiff.mp hb).2
    rcases hneighbour b (by simpa [F] using hbF) with
        ⟨c, hc, hbc, hinter⟩ | ⟨c, hc, hbc, hinter⟩
    · have hcF : c ∈ F := by simpa [F] using hc
      let A : Finset Block := {b, c}
      have hAO : A ∈ O := by
        apply Finset.mem_filter.mpr
        refine ⟨by simpa [A] using hpairMem hbF hcF hbc, ?_⟩
        dsimp [q, A]
        rw [S.commonSupport_pair]
        exact hinter
      change b ∈ O.biUnion (fun A => A)
      exact Finset.mem_biUnion.mpr ⟨A, hAO, by simp [A]⟩
    · have hcF : c ∈ F := by simpa [F] using hc
      let A : Finset Block := {b, c}
      have hAZ : A ∈ Z := by
        apply Finset.mem_filter.mpr
        refine ⟨by simpa [A] using hpairMem hbF hcF hbc, ?_⟩
        dsimp [q, A]
        rw [S.commonSupport_pair]
        exact hinter
      have hAz : A = z :=
        Finset.card_le_one.mp hZleOne A hAZ z hzZ
      have hbA : b ∈ A := by simp [A]
      have hbZ : b ∈ z := by
        rw [← hAz]
        exact hbA
      exact (hbNotZ hbZ).elim

  have hzSubF : z ⊆ F := by
    intro b hb
    simp only [z, Finset.mem_insert, Finset.mem_singleton] at hb
    rcases hb with rfl | rfl
    · exact hfF
    · exact hgF
  have hzCard : z.card = 2 := by simp [z, hfg]
  have hFge : 5 ≤ F.card := by
    rcases hFcases with hFfive | hFsix <;> omega
  have hcoveredLower : 3 ≤ (F \ z).card := by
    rw [Finset.card_sdiff_of_subset hzSubF, hzCard]
    omega
  have hCcardLower : 3 ≤ C.card :=
    le_trans hcoveredLower (Finset.card_le_card hcover)

  have hOmemberCard (A : Finset Block) (hAO : A ∈ O) : A.card = 2 := by
    have hAQ : A ∈ Q := (Finset.mem_filter.mp hAO).1
    have hAQ' : A ∈ F.powersetCard 2 := by simpa [Q] using hAQ
    exact (Finset.mem_powersetCard.mp hAQ').2
  have hCcardRaw : C.card ≤ ∑ A ∈ O, A.card := by
    change (O.biUnion fun A => A).card ≤ ∑ A ∈ O, A.card
    exact Finset.card_biUnion_le
  have hOcardSum : (∑ A ∈ O, A.card) = 2 * O.card := by
    calc
      (∑ A ∈ O, A.card) = ∑ _A ∈ O, 2 := by
        apply Finset.sum_congr rfl
        intro A hAO
        exact hOmemberCard A hAO
      _ = 2 * O.card := by simp [Nat.mul_comm]
  have hCcardUpper : C.card ≤ 2 * O.card := by omega
  have hOtwo : 2 ≤ O.card := by omega
  omega

/-- C39 finite tail with the exact neighbour alternative exposed by the
H28 router.  No page-cap or geometric extraction hypothesis occurs here. -/
theorem elevenFive_c39_h28_singletonOrDisjointDoubleCount
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    (cfg : Configuration Point)
    (hpoint : Fintype.card Point = 11)
    (hcap : BlockSizeCap (blockSystem cfg) 5)
    (hlocal : ∀ p : Point, ElevenFiveLocalRows (blockSystem cfg) p)
    (hglobal : ElevenFiveGlobalRows (blockSystem cfg))
    (hC : (blockSystem cfg).totalCircleCount = 39)
    (hL : elevenFiveLineTotal (blockSystem cfg) = 12)
    (hcircle : ∀ b ∈ (blockSystem cfg).circleBlocksOfSize 5,
      elevenFiveHostWeight (blockSystem cfg)
        ((blockSystem cfg).support b) ≤ 28)
    (hneighbour : ∀ b ∈ (blockSystem cfg).circleBlocksOfSize 5,
      ((∃ c, c ∈ (blockSystem cfg).blocksOfSize 5 ∧
          ((blockSystem cfg).support c ∩
            (blockSystem cfg).support b).card = 1) ∨
        (∃ c, c ∈ (blockSystem cfg).blocksOfSize 5 ∧
          ((blockSystem cfg).support c ∩
            (blockSystem cfg).support b).card = 0))) : False := by
  classical
  let S := blockSystem cfg
  let F := S.blocksOfSize 5
  change BlockSizeCap S 5 at hcap
  change (∀ p : Point, ElevenFiveLocalRows S p) at hlocal
  change ElevenFiveGlobalRows S at hglobal
  change S.totalCircleCount = 39 at hC
  change elevenFiveLineTotal S = 12 at hL
  change (∀ b ∈ S.circleBlocksOfSize 5,
    elevenFiveHostWeight S (S.support b) ≤ 28) at hcircle
  change (∀ b ∈ S.circleBlocksOfSize 5,
    ((∃ c, c ∈ S.blocksOfSize 5 ∧
        (S.support c ∩ S.support b).card = 1) ∨
      (∃ c, c ∈ S.blocksOfSize 5 ∧
        (S.support c ∩ S.support b).card = 0))) at hneighbour

  have hhigh := elevenFive_c39_l12_high_count_row
    S hpoint hlocal hglobal hC hL
  have hlineCut := elevenFive_c39_l12_line_cut S hglobal hC hL
  have hlineMelchior := hglobal.lineMelchior
  rw [hL] at hlineMelchior
  have hlineFiveLe : S.lineCount 5 ≤ 1 := by omega
  have hhostUpper := c39H28_mixed_hostTotal_le S hpoint hcircle
  have hhostMoment := elevenFive_c39_l12_host_moment
    S hpoint hcap hlocal hglobal hC hL
  have hfiveLower : 5 ≤ S.blockCount 5 := by omega
  have hfiveUpper : S.blockCount 5 ≤ 6 := by omega
  have hlineFive : S.lineCount 5 = 0 := by omega
  have hfiveCases : S.blockCount 5 = 5 ∨ S.blockCount 5 = 6 := by omega

  have hFcircle (b : GeometricBlock cfg) (hb : b ∈ F) :
      b ∈ S.circleBlocksOfSize 5 := by
    have hsize : (S.support b).card = 5 := S.mem_blocksOfSize.mp hb
    cases hkind : S.kind b with
    | circle => exact S.mem_blocksOfKindSize.mpr ⟨hkind, hsize⟩
    | line =>
        exfalso
        have hbline : b ∈ S.lineBlocksOfSize 5 :=
          S.mem_blocksOfKindSize.mpr ⟨hkind, hsize⟩
        have hpos : 0 < S.lineCount 5 := by
          change 0 < (S.lineBlocksOfSize 5).card
          exact Finset.card_pos.mpr ⟨b, hbline⟩
        omega

  have hneighbourF (b : GeometricBlock cfg) (hb : b ∈ F) :
      (∃ c, c ∈ F ∧ b ≠ c ∧
        (S.support b ∩ S.support c).card = 1) ∨
      (∃ c, c ∈ F ∧ b ≠ c ∧
        (S.support b ∩ S.support c).card = 0) := by
    rcases hneighbour b (hFcircle b hb) with
        ⟨c, hc, hinter⟩ | ⟨c, hc, hinter⟩
    · have hbc : b ≠ c := by
        intro hbc
        subst c
        have hsize := S.mem_blocksOfSize.mp hb
        rw [Finset.inter_self, hsize] at hinter
        omega
      exact Or.inl ⟨c, by simpa [F] using hc, hbc,
        by simpa [Finset.inter_comm] using hinter⟩
    · have hbc : b ≠ c := by
        intro hbc
        subst c
        have hsize := S.mem_blocksOfSize.mp hb
        rw [Finset.inter_self, hsize] at hinter
        omega
      exact Or.inr ⟨c, by simpa [F] using hc, hbc,
        by simpa [Finset.inter_comm] using hinter⟩

  by_cases hdisjoint : ∃ f, f ∈ F ∧ ∃ g, g ∈ F ∧
      f ≠ g ∧ (S.support f ∩ S.support g).card = 0
  · exact fiveBlock_singletonOrDisjoint_absurd_of_five_or_six
      S hpoint (fun p => (hlocal p).fiveDegreeCap) hfiveCases
        (fun b hb => hneighbourF b (by simpa [F] using hb))
        (by simpa [F] using hdisjoint)
  · have hsingleton : ∀ b ∈ S.circleBlocksOfSize 5,
        ∃ c, c ∈ S.blocksOfSize 5 ∧
          (S.support c ∩ S.support b).card = 1 := by
      intro b hb
      have hbF : b ∈ F := by
        apply S.mem_blocksOfSize.mpr
        exact (S.mem_blocksOfKindSize.mp hb).2
      rcases hneighbourF b hbF with
          ⟨c, hc, _hbc, hinter⟩ | ⟨c, hc, hbc, hinter⟩
      · exact ⟨c, by simpa [F] using hc,
          by simpa [Finset.inter_comm] using hinter⟩
      · exfalso
        exact hdisjoint ⟨b, hbF, c, hc, hbc, hinter⟩
    exact (elevenFive_c39_h28_singletonGraphDoubleCount cfg)
      hpoint hcap hlocal hglobal hC hL hcircle hsingleton

/-- The completed H28 page-cap router and the mixed finite double count
contradict the full C39/L12 rows. -/
theorem elevenFive_c39_l12_absurd_of_pageCapInput_rows
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    (cfg : Configuration Point)
    (hGoodall : ElevenFiveC39H28PageCapInput cfg)
    (hpoint : Fintype.card Point = 11)
    (hcap : BlockSizeCap (blockSystem cfg) 5)
    (hlocal : ∀ p : Point, ElevenFiveLocalRows (blockSystem cfg) p)
    (hglobal : ElevenFiveGlobalRows (blockSystem cfg))
    (hC : (blockSystem cfg).totalCircleCount = 39)
    (hL : elevenFiveLineTotal (blockSystem cfg) = 12) : False := by
  have hcircle : ∀ b ∈ (blockSystem cfg).circleBlocksOfSize 5,
      elevenFiveHostWeight (blockSystem cfg)
        ((blockSystem cfg).support b) ≤ 28 := by
    intro b hb
    rcases b with L | Gamma
    · have hkind := ((blockSystem cfg).mem_blocksOfKindSize.mp hb).1
      change (.line : BlockKind) = .circle at hkind
      cases hkind
    · have hD := ((blockSystem cfg).mem_blocksOfKindSize.mp hb).2
      change (circleTrace cfg Gamma.1).card = 5 at hD
      change elevenFiveHostWeight (blockSystem cfg)
        (circleTrace cfg Gamma.1) ≤ 28
      have hthirty := elevenFiveHostWeight_le_thirty
        (blockSystem cfg) (circleTrace cfg Gamma.1) hpoint hD
      have hne29 := elevenFive_c39_hostWeight_ne_twenty_nine
        cfg hpoint hcap hglobal hC hL Gamma hD
      have hne30 := elevenFive_c39_hostWeight_ne_thirty
        cfg hpoint hcap hglobal hC hL Gamma hD
      omega
  have hneighbour :=
    elevenFive_c39_l12_every_circleBlock_singleton_or_disjoint
      cfg hGoodall hpoint hcap hlocal hglobal hC hL
  exact elevenFive_c39_h28_singletonOrDisjointDoubleCount
    cfg hpoint hcap hlocal hglobal hC hL hcircle hneighbour

/-- Configuration-level C39 contradiction, still exposing only the finite
page-cap callback. -/
theorem elevenFive_c39_l12_absurd_of_pageCapInput_without_langer
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    (Mel : RealPlaneMelchiorPrinciple.{u})
    (EvenArr : RealPlaneEvenArrangementPrinciple.{u})
    (Cross : RealPlaneRadicalAxisCrossBlockPrinciple.{u})
    (Kelly : RealPlaneKellyMoserPrinciple.{u})
    (U17 : RealPlaneSixCircleU17Principle.{u})
    (TenGeometry : RealPlaneTenFiveGeometry.{u})
    (cfg : Configuration Point) (hadm : Admissible cfg)
    (hGoodall : ElevenFiveC39H28PageCapInput cfg)
    (hcard : Fintype.card Point = 11)
    (hcap : BlockSizeCap (blockSystem cfg) 5)
    (hCcount : Erdos506.V4.circleCount cfg = 39)
    (hL : elevenFiveLineTotal (blockSystem cfg) = 12) : False := by
  have hbridge : (blockSystem cfg).totalCircleCount =
      Erdos506.V4.circleCount cfg := by
    rw [totalCircleCount_eq_card_determinedCircle,
      ← Erdos506.V3.circleCount_eq_card_determinedCircle]
  have hC : (blockSystem cfg).totalCircleCount = 39 := by omega
  have hCupper : (blockSystem cfg).totalCircleCount ≤ 40 := by omega
  have hlocal : ∀ p : Point,
      ElevenFiveLocalRows (blockSystem cfg) p := by
    intro p
    exact elevenFiveLocalRows_of_configuration_without_langer
      Mel EvenArr Cross Kelly U17 TenGeometry
        cfg hadm hcard hcap hCupper p
  have hglobal : ElevenFiveGlobalRows (blockSystem cfg) :=
    elevenFiveGlobalRows_of_configuration Mel cfg hadm hcard hcap hlocal
  exact elevenFive_c39_l12_absurd_of_pageCapInput_rows
    cfg hGoodall hcard hcap hlocal hglobal hC hL

/-- Compatibility wrapper retaining the historical global parameter list. -/
theorem elevenFive_c39_l12_absurd_of_pageCapInput
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    (Mel : RealPlaneMelchiorPrinciple.{u})
    (_Langer : RealPlaneLangerPrinciple.{u})
    (EvenArr : RealPlaneEvenArrangementPrinciple.{u})
    (Cross : RealPlaneRadicalAxisCrossBlockPrinciple.{u})
    (Kelly : RealPlaneKellyMoserPrinciple.{u})
    (U17 : RealPlaneSixCircleU17Principle.{u})
    (TenGeometry : RealPlaneTenFiveGeometry.{u})
    (cfg : Configuration Point) (hadm : Admissible cfg)
    (hGoodall : ElevenFiveC39H28PageCapInput cfg)
    (hcard : Fintype.card Point = 11)
    (hcap : BlockSizeCap (blockSystem cfg) 5)
    (hCcount : Erdos506.V4.circleCount cfg = 39)
    (hL : elevenFiveLineTotal (blockSystem cfg) = 12) : False :=
  elevenFive_c39_l12_absurd_of_pageCapInput_without_langer
    Mel EvenArr Cross Kelly U17 TenGeometry cfg hadm hGoodall
      hcard hcap hCcount hL

/-- Fully unconditional C39/L12 endpoint.  The host-pair-fibre theorem
materializes the page-cap callback internally. -/
theorem elevenFive_c39_l12_absurd_of_hostPairFibres_without_langer
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    (Mel : RealPlaneMelchiorPrinciple.{u})
    (EvenArr : RealPlaneEvenArrangementPrinciple.{u})
    (Cross : RealPlaneRadicalAxisCrossBlockPrinciple.{u})
    (Kelly : RealPlaneKellyMoserPrinciple.{u})
    (U17 : RealPlaneSixCircleU17Principle.{u})
    (TenGeometry : RealPlaneTenFiveGeometry.{u})
    (cfg : Configuration Point) (hadm : Admissible cfg)
    (hcard : Fintype.card Point = 11)
    (hcap : BlockSizeCap (blockSystem cfg) 5)
    (hCcount : Erdos506.V4.circleCount cfg = 39)
    (hL : elevenFiveLineTotal (blockSystem cfg) = 12) : False :=
  elevenFive_c39_l12_absurd_of_pageCapInput_without_langer
    Mel EvenArr Cross Kelly U17 TenGeometry cfg hadm
      (elevenFiveC39H28PageCapInput_of_hostPairFibres cfg)
        hcard hcap hCcount hL

/-- Compatibility wrapper retaining the historical global parameter list. -/
theorem elevenFive_c39_l12_absurd_of_hostPairFibres
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    (Mel : RealPlaneMelchiorPrinciple.{u})
    (_Langer : RealPlaneLangerPrinciple.{u})
    (EvenArr : RealPlaneEvenArrangementPrinciple.{u})
    (Cross : RealPlaneRadicalAxisCrossBlockPrinciple.{u})
    (Kelly : RealPlaneKellyMoserPrinciple.{u})
    (U17 : RealPlaneSixCircleU17Principle.{u})
    (TenGeometry : RealPlaneTenFiveGeometry.{u})
    (cfg : Configuration Point) (hadm : Admissible cfg)
    (hcard : Fintype.card Point = 11)
    (hcap : BlockSizeCap (blockSystem cfg) 5)
    (hCcount : Erdos506.V4.circleCount cfg = 39)
    (hL : elevenFiveLineTotal (blockSystem cfg) = 12) : False :=
  elevenFive_c39_l12_absurd_of_hostPairFibres_without_langer
    Mel EvenArr Cross Kelly U17 TenGeometry cfg hadm
      hcard hcap hCcount hL

end Erdos506.V1
