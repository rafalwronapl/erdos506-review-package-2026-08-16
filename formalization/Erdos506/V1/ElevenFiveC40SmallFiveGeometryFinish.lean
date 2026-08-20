import Erdos506.V1.ElevenFiveC40SmallFiveFinish
import Erdos506.V1.ElevenFiveC39H30Finish
import Erdos506.V1.ElevenFiveC39H28ZeroFibrePageCap

/-!
# Geometry of the C40/L11 five-block faces

This file isolates the part of the `B₅ = 5` geometric finish which is
already supplied by the actual K2.1 circle-page router.  In the all-double
face, a proper five-circle containing only degree-six pivots has host weight
29 or 30.  Exact incidence rows give respectively five or three `(1,3)`
pages, contradicting the existing sharp K2.1 bounds.

The remaining two routes are K2.4 routes: they require the actual
golden-axis collinearity and omitted-colour concurrency which are not
consequences of the numerical predicate
`ElevenFiveC40B5FiveGeometricResidual` alone.
-/

namespace Erdos506.V1

open Erdos506.Block
open Erdos506.Block.BlockSystem
open Erdos506.Incidence
open Erdos506.V3
open Erdos506.V4
open scoped BigOperators

universe u v

/-- Equality in the universal pair-intersection bound forces every member
of a finite block family to meet every other member in two points. -/
theorem blockFamily_inter_card_eq_two_of_pairMoment_maximum
    {Point : Type u} {Block : Type v} [Fintype Point] [Fintype Block]
    [DecidableEq Point] [DecidableEq Block]
    (S : BlockSystem Point Block) (F : Finset Block)
    (hmoment : (∑ p : Point, Nat.choose (S.degreeIn F p) 2) =
      2 * Nat.choose F.card 2) :
    ∀ b ∈ F, ∀ c ∈ F, b ≠ c →
      (S.support b ∩ S.support c).card = 2 := by
  classical
  let Q := F.powersetCard 2
  let q : Finset Block → ℕ := fun A => (S.commonSupport A).card
  have hQcard : Q.card = Nat.choose F.card 2 := by
    simp [Q]
  have htotal : (∑ A ∈ Q, q A) = 2 * Nat.choose F.card 2 := by
    change (∑ A ∈ F.powersetCard 2, (S.commonSupport A).card) = _
    rw [← S.binomial_degree_moment F 2]
    exact hmoment
  have htermLe (A : Finset Block) (hA : A ∈ Q) : q A ≤ 2 := by
    dsimp [q]
    apply S.commonSupport_card_le_two
    have hA' : A ∈ F.powersetCard 2 := by simpa [Q] using hA
    exact (Finset.mem_powersetCard.mp hA').2
  have hconstant : (∑ _A ∈ Q, 2) = 2 * Nat.choose F.card 2 := by
    simp only [Finset.sum_const, nsmul_eq_mul]
    rw [hQcard, Nat.mul_comm]
    norm_num
  have hall := (Finset.sum_eq_sum_iff_of_le htermLe).mp
    (htotal.trans hconstant.symm)
  intro b hb c hc hbc
  have hpair : ({b, c} : Finset Block) ∈ Q := by
    change ({b, c} : Finset Block) ∈ F.powersetCard 2
    refine Finset.mem_powersetCard.mpr ⟨?_, ?_⟩
    · intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact hb
      · exact hc
    · simp [hbc]
  have hpairValue := hall ({b, c} : Finset Block) hpair
  simpa [q, S.commonSupport_pair] using hpairValue

/-- In the five-block moment-20 face all ten distinct pairs are double. -/
theorem fiveBlock_inter_card_eq_two_of_secondMoment_twenty
    {Point : Type u} {Block : Type v} [Fintype Point] [Fintype Block]
    [DecidableEq Point] [DecidableEq Block]
    (S : BlockSystem Point Block)
    (hfive : S.blockCount 5 = 5)
    (hmoment : elevenFiveSecondMoment S = 20) :
    ∀ b ∈ S.blocksOfSize 5, ∀ c ∈ S.blocksOfSize 5,
      b ≠ c → (S.support b ∩ S.support c).card = 2 := by
  classical
  let F := S.blocksOfSize 5
  have hFcard : F.card = 5 := by
    simpa [F, BlockSystem.blockCount] using hfive
  have hmoment' :
      (∑ p : Point, Nat.choose (S.degreeIn F p) 2) =
        2 * Nat.choose F.card 2 := by
    simpa [F, BlockSystem.blockDegree, elevenFiveSecondMoment,
      hFcard, Nat.choose] using hmoment
  exact blockFamily_inter_card_eq_two_of_pairMoment_maximum
    S F hmoment'

/-- Two distinct line blocks cannot occur in an all-double five-block
family. -/
theorem fiveBlock_lineCount_le_one_of_allDouble
    {Point : Type u} {Block : Type v} [Fintype Point] [Fintype Block]
    [DecidableEq Point] [DecidableEq Block]
    (S : BlockSystem Point Block)
    (hallDouble : ∀ b ∈ S.blocksOfSize 5, ∀ c ∈ S.blocksOfSize 5,
      b ≠ c → (S.support b ∩ S.support c).card = 2) :
    S.lineCount 5 ≤ 1 := by
  classical
  by_contra hnot
  have htwo : 1 < (S.lineBlocksOfSize 5).card := by
    change ¬ S.lineCount 5 ≤ 1 at hnot
    simpa [BlockSystem.lineCount] using (show 1 < S.lineCount 5 by omega)
  obtain ⟨b, hb, c, hc, hbc⟩ := Finset.one_lt_card.mp htwo
  have hbSpec := S.mem_blocksOfKindSize.mp hb
  have hcSpec := S.mem_blocksOfKindSize.mp hc
  have hbFive : b ∈ S.blocksOfSize 5 := S.mem_blocksOfSize.mpr hbSpec.2
  have hcFive : c ∈ S.blocksOfSize 5 := S.mem_blocksOfSize.mpr hcSpec.2
  have hdouble := hallDouble b hbFive c hcFive hbc
  let lb : LineBlock S := ⟨b, hbSpec.1⟩
  let lc : LineBlock S := ⟨c, hcSpec.1⟩
  have hlbc : lb ≠ lc := by
    intro h
    exact hbc (congrArg Subtype.val h)
  have hline := S.distinct_line_inter_card_lt_two hlbc
  have hline' : (S.support b ∩ S.support c).card < 2 := by
    simpa [lb, lc] using hline
  omega

/-- The selected five-block has degree mass thirteen when its other four
five-blocks all meet it twice. -/
private theorem fiveBlock_support_degree_sum_eq_thirteen_of_allDouble
    {Point : Type u} {Block : Type v} [Fintype Point] [Fintype Block]
    [DecidableEq Point] [DecidableEq Block]
    (S : BlockSystem Point Block) (b : Block)
    (hb : b ∈ S.blocksOfSize 5)
    (hfive : S.blockCount 5 = 5)
    (hallDouble : ∀ c ∈ S.blocksOfSize 5, c ≠ b →
      (S.support b ∩ S.support c).card = 2) :
    (∑ p ∈ S.support b, S.blockDegree 5 p) = 13 := by
  classical
  let F := S.blocksOfSize 5
  have hbF : b ∈ F := by simpa [F] using hb
  have hFcard : F.card = 5 := by
    simpa [F, BlockSystem.blockCount] using hfive
  have hother (c : Block) (hc : c ∈ F.erase b) :
      (S.support b ∩ S.support c).card = 2 := by
    exact hallDouble c (by simpa [F] using Finset.mem_of_mem_erase hc)
      (Finset.mem_erase.mp hc).1
  have hotherSum :
      (∑ c ∈ F.erase b, (S.support b ∩ S.support c).card) = 8 := by
    calc
      (∑ c ∈ F.erase b, (S.support b ∩ S.support c).card) =
          ∑ _c ∈ F.erase b, 2 := by
        apply Finset.sum_congr rfl
        intro c hc
        exact hother c hc
      _ = 8 := by
        simp [Finset.card_erase_of_mem hbF, hFcard]
  have hself : (S.support b ∩ S.support b).card = 5 := by
    simp [S.mem_blocksOfSize.mp hb]
  have hsplit := Finset.sum_erase_add F
    (fun c => (S.support b ∩ S.support c).card) hbF
  have hinc := S.sum_degreeIn_over F (S.support b)
  change (∑ p ∈ S.support b, S.blockDegree 5 p) =
    ∑ c ∈ F, (S.support b ∩ S.support c).card at hinc
  rw [hinc]
  calc
    (∑ c ∈ F, (S.support b ∩ S.support c).card) =
        (∑ c ∈ F.erase b,
          (S.support b ∩ S.support c).card) +
            (S.support b ∩ S.support b).card := hsplit.symm
    _ = 13 := by rw [hotherSum, hself]

/-- Incidence on a selected five-block, expressed through the one- and
two-trace relative fibres of one fixed support size. -/
private theorem selectedFive_support_degree_eq_relativeCount_one_two
    {Point : Type u} {Block : Type v} [Fintype Point] [Fintype Block]
    [DecidableEq Point] [DecidableEq Block]
    (S : BlockSystem Point Block) (b : Block)
    (hb : b ∈ S.blocksOfSize 5)
    (s x₁ x₂ : ℕ) (hsne : s ≠ 5)
    (hx₁ : 1 + x₁ = s) (hx₂ : 2 + x₂ = s) :
    (∑ p ∈ S.support b, S.blockDegree s p) =
      elevenFiveRelativeCount S (S.support b) 1 x₁ +
        2 * elevenFiveRelativeCount S (S.support b) 2 x₂ := by
  classical
  have hinc := S.sum_degreeIn_over (S.blocksOfSize s) (S.support b)
  change (∑ p ∈ S.support b, S.blockDegree s p) =
    ∑ c ∈ S.blocksOfSize s,
      (S.support b ∩ S.support c).card at hinc
  rw [hinc]
  calc
    (∑ c ∈ S.blocksOfSize s,
        (S.support b ∩ S.support c).card) =
        ∑ c : Block, if c ∈ S.blocksOfSize s then
          (S.support b ∩ S.support c).card else 0 := by
      unfold BlockSystem.blocksOfSize
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro c hc
      by_cases hcs : (S.support c).card = s
      · simp [hcs]
      · simp [hcs]
    _ = ∑ c : Block,
        ((if (S.support c ∩ S.support b).card = 1 ∧
              (S.support c \ S.support b).card = x₁ then 1 else 0) +
          2 * (if (S.support c ∩ S.support b).card = 2 ∧
              (S.support c \ S.support b).card = x₂ then 1 else 0)) := by
      apply Finset.sum_congr rfl
      intro c _hc
      by_cases hcs : c ∈ S.blocksOfSize s
      · have hcSize := S.mem_blocksOfSize.mp hcs
        have hcb : c ≠ b := by
          intro hcb
          subst c
          have hbSize := S.mem_blocksOfSize.mp hb
          exact hsne (by omega)
        have hinter := S.distinct_block_inter_card_lt_three hcb
        have hiLe : (S.support c ∩ S.support b).card ≤ 2 := by
          omega
        have hsplit :=
          Finset.card_inter_add_card_sdiff (S.support c) (S.support b)
        interval_cases hi : (S.support c ∩ S.support b).card
        · have hi' : (S.support b ∩ S.support c).card = 0 := by
            simpa [Finset.inter_comm] using hi
          rw [Finset.card_eq_zero.mp hi']
          simp [hcs, hi]
        · have ho : (S.support c \ S.support b).card = x₁ := by omega
          have hi' : (S.support b ∩ S.support c).card = 1 := by
            simpa [Finset.inter_comm] using hi
          simp [hcs, hi, hi', ho]
        · have ho : (S.support c \ S.support b).card = x₂ := by omega
          have hi' : (S.support b ∩ S.support c).card = 2 := by
            simpa [Finset.inter_comm] using hi
          simp [hcs, hi, hi', ho]
      · have hone : ¬ ((S.support c ∩ S.support b).card = 1 ∧
            (S.support c \ S.support b).card = x₁) := by
          rintro ⟨hi, ho⟩
          apply hcs
          apply S.mem_blocksOfSize.mpr
          have hsplit :=
            Finset.card_inter_add_card_sdiff (S.support c) (S.support b)
          omega
        have htwo : ¬ ((S.support c ∩ S.support b).card = 2 ∧
            (S.support c \ S.support b).card = x₂) := by
          rintro ⟨hi, ho⟩
          apply hcs
          apply S.mem_blocksOfSize.mpr
          have hsplit :=
            Finset.card_inter_add_card_sdiff (S.support c) (S.support b)
          omega
        simp [hcs, hone, htwo]
    _ = elevenFiveRelativeCount S (S.support b) 1 x₁ +
        2 * elevenFiveRelativeCount S (S.support b) 2 x₂ := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum]
      have hone :
          (∑ c : Block,
            if (S.support c ∩ S.support b).card = 1 ∧
                (S.support c \ S.support b).card = x₁ then 1 else 0) =
            elevenFiveRelativeCount S (S.support b) 1 x₁ := by
        rw [← Finset.sum_filter, ← Finset.card_eq_sum_ones]
        unfold elevenFiveRelativeCount
        apply congrArg Finset.card
        ext c
        simp
      have htwo :
          (∑ c : Block,
            if (S.support c ∩ S.support b).card = 2 ∧
                (S.support c \ S.support b).card = x₂ then 1 else 0) =
            elevenFiveRelativeCount S (S.support b) 2 x₂ := by
        rw [← Finset.sum_filter, ← Finset.card_eq_sum_ones]
        unfold elevenFiveRelativeCount
        apply congrArg Finset.card
        ext c
        simp
      rw [hone, htwo]

/-- In an all-double five-block family, the four neighbours of a selected
five-block are exactly its four `(2,3)` relative blocks. -/
private theorem relativeCount_two_three_eq_four_of_allDouble
    {Point : Type u} {Block : Type v} [Fintype Point] [Fintype Block]
    [DecidableEq Point] [DecidableEq Block]
    (S : BlockSystem Point Block) (b : Block)
    (hb : b ∈ S.blocksOfSize 5)
    (hfive : S.blockCount 5 = 5)
    (hallDouble : ∀ c ∈ S.blocksOfSize 5, c ≠ b →
      (S.support c ∩ S.support b).card = 2) :
    elevenFiveRelativeCount S (S.support b) 2 3 = 4 := by
  classical
  let A := (Finset.univ : Finset Block).filter fun c =>
    (S.support c ∩ S.support b).card = 2 ∧
      (S.support c \ S.support b).card = 3
  let F := S.blocksOfSize 5
  have hbF : b ∈ F := by simpa [F] using hb
  have hAF : A = F.erase b := by
    ext c
    simp only [A, F, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_erase]
    constructor
    · rintro ⟨hi, ho⟩
      have hsplit :=
        Finset.card_inter_add_card_sdiff (S.support c) (S.support b)
      have hcFive : c ∈ S.blocksOfSize 5 := by
        apply S.mem_blocksOfSize.mpr
        omega
      have hcb : c ≠ b := by
        intro hcb
        subst c
        have hbSize := S.mem_blocksOfSize.mp hb
        simp [hbSize] at hi
      exact ⟨hcb, hcFive⟩
    · rintro ⟨hcb, hcFive⟩
      have hi := hallDouble c hcFive hcb
      have hcSize := S.mem_blocksOfSize.mp hcFive
      have hsplit :=
        Finset.card_inter_add_card_sdiff (S.support c) (S.support b)
      refine ⟨hi, ?_⟩
      omega
  change A.card = 4
  rw [hAF, Finset.card_erase_of_mem hbF]
  have hFcard : F.card = 5 := by
    simpa [F, BlockSystem.blockCount] using hfive
  rw [hFcard]

/-- Actual K2.1 closes an all-double face as soon as the selected proper
five-circle avoids the unique degree-nine pivot. -/
theorem elevenFive_allDouble_low_properFiveCircle_absurd
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    (cfg : Configuration Point) (Gamma : DeterminedCircle cfg)
    (hpoint : Fintype.card Point = 11)
    (hcap : BlockSizeCap (blockSystem cfg) 5)
    (hlocal : ∀ p : Point, ElevenFiveLocalRows (blockSystem cfg) p)
    (hD : (circleTrace cfg Gamma.1).card = 5)
    (hfour : (blockSystem cfg).blockCount 4 = 23)
    (hfive : (blockSystem cfg).blockCount 5 = 5)
    (hallDoubleAt : ∀ c ∈ (blockSystem cfg).blocksOfSize 5,
      c ≠ (Sum.inr Gamma : GeometricBlock cfg) →
        ((blockSystem cfg).support (Sum.inr Gamma) ∩
          (blockSystem cfg).support c).card = 2)
    (hlow : ∀ p ∈ circleTrace cfg Gamma.1,
      (blockSystem cfg).blockDegree 3 p = 6) : False := by
  classical
  let S := blockSystem cfg
  let D := circleTrace cfg Gamma.1
  let b : GeometricBlock cfg := Sum.inr Gamma
  have hb : b ∈ S.blocksOfSize 5 := by
    apply S.mem_blocksOfSize.mpr
    simpa [S, b, D, blockSystem, geometricBlockSystem,
      geometricBlockSupport] using hD
  have hDb : S.support b = D := by
    simp [S, b, D, blockSystem, geometricBlockSystem, geometricBlockSupport]
  have hsumFive : (∑ p ∈ D, S.blockDegree 5 p) = 13 := by
    rw [← hDb]
    apply fiveBlock_support_degree_sum_eq_thirteen_of_allDouble
      S b hb (by simpa [S] using hfive)
    intro c hc hcb
    exact hallDoubleAt c (by simpa [S] using hc) (by simpa [b] using hcb)
  have hsumThree : (∑ p ∈ D, S.blockDegree 3 p) = 30 := by
    calc
      (∑ p ∈ D, S.blockDegree 3 p) = ∑ _p ∈ D, 6 := by
        apply Finset.sum_congr rfl
        intro p hp
        exact hlow p (by simpa [D] using hp)
      _ = 30 := by simp [hD, D]
  have hpointRow (p : Point) (hp : p ∈ D) :
      S.blockDegree 4 p + 2 * S.blockDegree 5 p = 13 := by
    have hpair := (hlocal p).pairRow
    have hthree := hlow p (by simpa [D] using hp)
    change S.blockDegree 3 p + 3 * S.blockDegree 4 p +
      6 * S.blockDegree 5 p = 45 at hpair
    change S.blockDegree 3 p = 6 at hthree
    omega
  have hsumPoint :
      (∑ p ∈ D, (S.blockDegree 4 p + 2 * S.blockDegree 5 p)) =
        ∑ _p ∈ D, 13 := by
    apply Finset.sum_congr rfl
    intro p hp
    exact hpointRow p hp
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at hsumPoint
  have hsumFour : (∑ p ∈ D, S.blockDegree 4 p) = 39 := by
    rw [hsumFive] at hsumPoint
    simp [hD, D] at hsumPoint
    omega
  have hthreeRelative :=
    selectedFive_support_degree_eq_relativeCount_one_two
      S b hb 3 2 1 (by omega) (by omega) (by omega)
  have hfourRelative :=
    selectedFive_support_degree_eq_relativeCount_one_two
      S b hb 4 3 2 (by omega) (by omega) (by omega)
  rw [hDb] at hthreeRelative hfourRelative
  have hA23 : elevenFiveRelativeCount S D 2 3 = 4 := by
    rw [← hDb]
    apply relativeCount_two_three_eq_four_of_allDouble
      S b hb (by simpa [S] using hfive)
    intro c hc hcb
    have h := hallDoubleAt c (by simpa [S] using hc)
      (by simpa [b] using hcb)
    simpa [Finset.inter_comm, b] using h
  have hrowTwo :=
    elevenFive_relativeCount_two_one_add_two_mul_two_two_add_three_mul_two_three_eq_sixty
      S D b hpoint (by simpa [D] using hD) hb hDb (by simpa [S] using hcap)
  have hhostRow :=
    elevenFiveHostWeight_eq_relativeCount22_add_three_mul_relativeCount23
      S D (by simpa [S] using hcap)
  have hhostCap := elevenFiveHostWeight_le_thirty S D
    hpoint (by simpa [D] using hD)
  have hA22Lower : 17 ≤ elevenFiveRelativeCount S D 2 2 := by
    omega
  have hhostCases : elevenFiveHostWeight S D = 29 ∨
      elevenFiveHostWeight S D = 30 := by
    omega
  rcases hhostCases with hhost | hhost
  · have hK21 := elevenFive_c39_h29_relativeCount_one_three_le_one
      cfg Gamma hpoint hD (by simpa [S, D] using hhost)
    have hK21S : elevenFiveRelativeCount S D 1 3 ≤ 1 := by
      simpa [S, D] using hK21
    have hA13 : elevenFiveRelativeCount S D 1 3 = 5 := by
      omega
    omega
  · have hK21 := elevenFive_c39_h30_relativeCount_one_three_eq_zero
      cfg Gamma hpoint hD (by simpa [S, D] using hhost)
    have hK21S : elevenFiveRelativeCount S D 1 3 = 0 := by
      simpa [S, D] using hK21
    have hA13 : elevenFiveRelativeCount S D 1 3 = 3 := by
      omega
    omega

/-- If exactly one degree-nine pivot lies on a proper five-circle whose
four five-block neighbours are double, K2.1 removes host weights 29 and 30.
The universal host cap therefore forces the genuine K2.4 value 28. -/
theorem elevenFive_doubleNeighbour_oneHigh_properFiveCircle_host_eq_twentyEight
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    (cfg : Configuration Point) (Gamma : DeterminedCircle cfg)
    (hpoint : Fintype.card Point = 11)
    (hcap : BlockSizeCap (blockSystem cfg) 5)
    (hlocal : ∀ p : Point, ElevenFiveLocalRows (blockSystem cfg) p)
    (hD : (circleTrace cfg Gamma.1).card = 5)
    (hfive : (blockSystem cfg).blockCount 5 = 5)
    (hallDoubleAt : ∀ c ∈ (blockSystem cfg).blocksOfSize 5,
      c ≠ (Sum.inr Gamma : GeometricBlock cfg) →
        ((blockSystem cfg).support (Sum.inr Gamma) ∩
          (blockSystem cfg).support c).card = 2)
    (hsumThree :
      (∑ p ∈ circleTrace cfg Gamma.1,
        (blockSystem cfg).blockDegree 3 p) = 33) :
    elevenFiveHostWeight (blockSystem cfg) (circleTrace cfg Gamma.1) = 28 := by
  classical
  let S := blockSystem cfg
  let D := circleTrace cfg Gamma.1
  let b : GeometricBlock cfg := Sum.inr Gamma
  have hb : b ∈ S.blocksOfSize 5 := by
    apply S.mem_blocksOfSize.mpr
    simpa [S, b, D, blockSystem, geometricBlockSystem,
      geometricBlockSupport] using hD
  have hDb : S.support b = D := by
    simp [S, b, D, blockSystem, geometricBlockSystem, geometricBlockSupport]
  have hsumFive : (∑ p ∈ D, S.blockDegree 5 p) = 13 := by
    rw [← hDb]
    apply fiveBlock_support_degree_sum_eq_thirteen_of_allDouble
      S b hb (by simpa [S] using hfive)
    intro c hc hcb
    exact hallDoubleAt c (by simpa [S] using hc) (by simpa [b] using hcb)
  have hsumPair :
      (∑ p ∈ D, (S.blockDegree 3 p + 3 * S.blockDegree 4 p +
        6 * S.blockDegree 5 p)) = ∑ _p ∈ D, 45 := by
    apply Finset.sum_congr rfl
    intro p _hp
    simpa [S] using (hlocal p).pairRow
  have hsumPairLinear :
      (∑ p ∈ D, S.blockDegree 3 p) +
          3 * (∑ p ∈ D, S.blockDegree 4 p) +
            6 * (∑ p ∈ D, S.blockDegree 5 p) = 225 := by
    calc
      (∑ p ∈ D, S.blockDegree 3 p) +
          3 * (∑ p ∈ D, S.blockDegree 4 p) +
            6 * (∑ p ∈ D, S.blockDegree 5 p) =
          ∑ p ∈ D, (S.blockDegree 3 p + 3 * S.blockDegree 4 p +
            6 * S.blockDegree 5 p) := by
              simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
      _ = ∑ _p ∈ D, 45 := hsumPair
      _ = 225 := by simp [hD, D]
  have hsumThreeS : (∑ p ∈ D, S.blockDegree 3 p) = 33 := by
    simpa [S, D] using hsumThree
  have hsumFour : (∑ p ∈ D, S.blockDegree 4 p) = 38 := by
    rw [hsumThreeS, hsumFive] at hsumPairLinear
    omega
  have hthreeRelative :=
    selectedFive_support_degree_eq_relativeCount_one_two
      S b hb 3 2 1 (by omega) (by omega) (by omega)
  have hfourRelative :=
    selectedFive_support_degree_eq_relativeCount_one_two
      S b hb 4 3 2 (by omega) (by omega) (by omega)
  rw [hDb] at hthreeRelative hfourRelative
  rw [hsumThreeS] at hthreeRelative
  have hA23 : elevenFiveRelativeCount S D 2 3 = 4 := by
    rw [← hDb]
    apply relativeCount_two_three_eq_four_of_allDouble
      S b hb (by simpa [S] using hfive)
    intro c hc hcb
    have h := hallDoubleAt c (by simpa [S] using hc)
      (by simpa [b] using hcb)
    simpa [Finset.inter_comm, b] using h
  have hrowTwo :=
    elevenFive_relativeCount_two_one_add_two_mul_two_two_add_three_mul_two_three_eq_sixty
      S D b hpoint (by simpa [D] using hD) hb hDb (by simpa [S] using hcap)
  have hhostRow :=
    elevenFiveHostWeight_eq_relativeCount22_add_three_mul_relativeCount23
      S D (by simpa [S] using hcap)
  have hhostCap := elevenFiveHostWeight_le_thirty S D
    hpoint (by simpa [D] using hD)
  have hA22Lower : 16 ≤ elevenFiveRelativeCount S D 2 2 := by
    rw [hA23] at hrowTwo
    omega
  have hhostCases : elevenFiveHostWeight S D = 28 ∨
      elevenFiveHostWeight S D = 29 ∨
        elevenFiveHostWeight S D = 30 := by
    omega
  rcases hhostCases with hhost | hhost | hhost
  · simpa [S, D] using hhost
  · have hK21 := elevenFive_c39_h29_relativeCount_one_three_le_one
      cfg Gamma hpoint hD (by simpa [S, D] using hhost)
    have hK21S : elevenFiveRelativeCount S D 1 3 ≤ 1 := by
      simpa [S, D] using hK21
    have hA13 : elevenFiveRelativeCount S D 1 3 = 4 := by
      omega
    omega
  · have hK21 := elevenFive_c39_h30_relativeCount_one_three_eq_zero
      cfg Gamma hpoint hD (by simpa [S, D] using hhost)
    have hK21S : elevenFiveRelativeCount S D 1 3 = 0 := by
      simpa [S, D] using hK21
    have hA13 : elevenFiveRelativeCount S D 1 3 = 2 := by
      omega
    omega

/-- Common actual entrance for both remaining faces: any proper five-circle
with four double five-block neighbours has the H28 zero fibre. -/
theorem elevenFive_c40_l11_b5_five_doubleNeighbourCircle_h28_zeroFibre
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    (cfg : Configuration Point) (Gamma : DeterminedCircle cfg)
    (hpoint : Fintype.card Point = 11)
    (hcap : BlockSizeCap (blockSystem cfg) 5)
    (hlocal : ∀ p : Point, ElevenFiveLocalRows (blockSystem cfg) p)
    (hglobal : ElevenFiveGlobalRows (blockSystem cfg))
    (hC : (blockSystem cfg).totalCircleCount = 40)
    (hL : elevenFiveLineTotal (blockSystem cfg) = 11)
    (hfive : (blockSystem cfg).blockCount 5 = 5)
    (hbeta : ∀ p : Point,
      (blockSystem cfg).blockDegree 3 p +
        (blockSystem cfg).blockDegree 4 p +
          (blockSystem cfg).blockDegree 5 p ≤ 18)
    (hD : (circleTrace cfg Gamma.1).card = 5)
    (hallDoubleAt : ∀ c ∈ (blockSystem cfg).blocksOfSize 5,
      c ≠ (Sum.inr Gamma : GeometricBlock cfg) →
        ((blockSystem cfg).support (Sum.inr Gamma) ∩
          (blockSystem cfg).support c).card = 2) :
    elevenFiveHostWeight (blockSystem cfg) (circleTrace cfg Gamma.1) = 28 ∧
      elevenFiveRelativeCount (blockSystem cfg)
        (circleTrace cfg Gamma.1) 1 4 = 0 := by
  classical
  let S := blockSystem cfg
  let D := circleTrace cfg Gamma.1
  let H := (Finset.univ : Finset Point).filter fun p =>
    S.blockDegree 3 p = 9
  obtain ⟨hHcard, hthreeValues⟩ :=
    elevenFive_c40_l11_b5_five_threeDegree_census
      S hpoint (by simpa [S] using hlocal) (by simpa [S] using hglobal)
        (by simpa [S] using hC) (by simpa [S] using hL)
          (by simpa [S] using hfive) (by simpa [S] using hbeta)
  have hHcard' : H.card = 1 := by simpa [H] using hHcard
  have hHpos : 0 < H.card := by omega
  obtain ⟨q, hqH⟩ := Finset.card_pos.mp hHpos
  have hqThree : S.blockDegree 3 q = 9 := (Finset.mem_filter.mp hqH).2
  let b : GeometricBlock cfg := Sum.inr Gamma
  have hb : b ∈ S.blocksOfSize 5 := by
    apply S.mem_blocksOfSize.mpr
    simpa [S, b, D, blockSystem, geometricBlockSystem,
      geometricBlockSupport] using hD
  have hDb : S.support b = D := by
    simp [S, b, D, blockSystem, geometricBlockSystem, geometricBlockSupport]
  have hallAt : ∀ c ∈ S.blocksOfSize 5, c ≠ b →
      (S.support b ∩ S.support c).card = 2 := by
    intro c hc hcb
    exact hallDoubleAt c (by simpa [S] using hc) (by simpa [b] using hcb)
  have hfourBlock : S.blockCount 4 = 23 := by
    have htriple := hglobal.tripleRow
    have htotal := hglobal.blockTotal
    rw [hfive] at htriple
    rw [hC, hL, hfive] at htotal
    change S.blockCount 3 + 4 * S.blockCount 4 + 10 * 5 = 165 at htriple
    change S.blockCount 3 + S.blockCount 4 + 5 = 40 + 11 at htotal
    omega
  have hzero : elevenFiveRelativeCount S D 1 4 = 0 := by
    apply elevenFive_relativeCount_one_four_eq_zero_of_no_sizeFive_singleton
    rintro ⟨c, hc, hinter⟩
    by_cases hcb : c = b
    · subst c
      rw [← hDb] at hinter
      have hbSize := S.mem_blocksOfSize.mp hb
      simp [hbSize] at hinter
    · have htwo := hallAt c hc hcb
      rw [hDb] at htwo
      have htwo' : (S.support c ∩ D).card = 2 := by
        simpa [Finset.inter_comm] using htwo
      omega
  by_cases hqD : q ∈ D
  · have hotherLow : ∀ p ∈ D, p ≠ q →
        S.blockDegree 3 p = 6 := by
      intro p hp hpq
      rcases hthreeValues p with hpSix | hpNine
      · exact hpSix
      · have hpH : p ∈ H := by simp [H, hpNine]
        have heq := Finset.card_le_one.mp (by omega : H.card ≤ 1)
          p hpH q hqH
        exact False.elim (hpq heq)
    let R := D.erase q
    have hRcard : R.card = 4 := by
      dsimp [R]
      rw [Finset.card_erase_of_mem hqD, hD]
    have hRsum : (∑ p ∈ R, S.blockDegree 3 p) = 24 := by
      calc
        (∑ p ∈ R, S.blockDegree 3 p) = ∑ _p ∈ R, 6 := by
          apply Finset.sum_congr rfl
          intro p hp
          exact hotherLow p (Finset.mem_of_mem_erase hp)
            (Finset.mem_erase.mp hp).1
        _ = 24 := by simp [hRcard]
    have hsplitD := Finset.sum_erase_add D
      (fun p => S.blockDegree 3 p) hqD
    have hsumThree : (∑ p ∈ D, S.blockDegree 3 p) = 33 := by
      change (∑ p ∈ R, S.blockDegree 3 p) +
        S.blockDegree 3 q = _ at hsplitD
      rw [hRsum, hqThree] at hsplitD
      norm_num at hsplitD
      exact hsplitD.symm
    have hhost :=
      elevenFive_doubleNeighbour_oneHigh_properFiveCircle_host_eq_twentyEight
        cfg Gamma hpoint hcap hlocal hD hfive
          (by
            intro c hc hcb
            exact hallAt c (by simpa [S] using hc)
              (by simpa [b] using hcb))
          (by simpa [S, D] using hsumThree)
    exact ⟨hhost, by simpa [S, D] using hzero⟩
  · have hlow : ∀ p ∈ D, S.blockDegree 3 p = 6 := by
      intro p hp
      rcases hthreeValues p with hpSix | hpNine
      · exact hpSix
      · have hpH : p ∈ H := by simp [H, hpNine]
        have hpq := Finset.card_le_one.mp (by omega : H.card ≤ 1)
          p hpH q hqH
        subst p
        exact False.elim (hqD hp)
    exact False.elim
      (elevenFive_allDouble_low_properFiveCircle_absurd
        cfg Gamma hpoint hcap hlocal hD (by simpa [S] using hfourBlock)
          hfive
          (by
            intro c hc hcb
            exact hallAt c (by simpa [S] using hc)
              (by simpa [b] using hcb))
          (by simpa [S, D] using hlow))

/-- The unconditional H28 pair-fibre page cap is incompatible with a
proper five-circle whose four other five-blocks are all double.  The local
C40 census gives three-degree mass at most `33`, while the five-block row
has mass `13`; hence the four-block mass is at least `38`.  At `H = 28`
the four double neighbours give `A₂₃ = 4` and `A₂₂ = 16`, so the four-block
incidence row forces `A₁₃ ≥ 6`, contradicting the finite cap `A₁₃ ≤ 4`. -/
theorem elevenFive_c40_l11_b5_five_doubleNeighbourCircle_impossible_of_pageCap
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    (cfg : Configuration Point) (Gamma : DeterminedCircle cfg)
    (hpoint : Fintype.card Point = 11)
    (hcap : BlockSizeCap (blockSystem cfg) 5)
    (hlocal : ∀ p : Point, ElevenFiveLocalRows (blockSystem cfg) p)
    (hglobal : ElevenFiveGlobalRows (blockSystem cfg))
    (hC : (blockSystem cfg).totalCircleCount = 40)
    (hL : elevenFiveLineTotal (blockSystem cfg) = 11)
    (hfive : (blockSystem cfg).blockCount 5 = 5)
    (hbeta : ∀ p : Point,
      (blockSystem cfg).blockDegree 3 p +
        (blockSystem cfg).blockDegree 4 p +
          (blockSystem cfg).blockDegree 5 p ≤ 18)
    (hD : (circleTrace cfg Gamma.1).card = 5)
    (hallDoubleAt : ∀ c ∈ (blockSystem cfg).blocksOfSize 5,
      c ≠ (Sum.inr Gamma : GeometricBlock cfg) →
        ((blockSystem cfg).support (Sum.inr Gamma) ∩
          (blockSystem cfg).support c).card = 2) : False := by
  classical
  let S := blockSystem cfg
  let D := circleTrace cfg Gamma.1
  let b : GeometricBlock cfg := Sum.inr Gamma
  have hb : b ∈ S.blocksOfSize 5 := by
    apply S.mem_blocksOfSize.mpr
    simpa [S, b, D, blockSystem, geometricBlockSystem,
      geometricBlockSupport] using hD
  have hDb : S.support b = D := by
    simp [S, b, D, blockSystem, geometricBlockSystem,
      geometricBlockSupport]
  obtain ⟨hhost, hzero⟩ :=
    elevenFive_c40_l11_b5_five_doubleNeighbourCircle_h28_zeroFibre
      cfg Gamma hpoint hcap hlocal hglobal hC hL hfive hbeta hD
        hallDoubleAt
  have hpageCap :=
    elevenFiveC39H28PageCapInput_of_hostPairFibres cfg
      Gamma hpoint hD hhost hzero
  have hsumFive : (∑ p ∈ D, S.blockDegree 5 p) = 13 := by
    rw [← hDb]
    apply fiveBlock_support_degree_sum_eq_thirteen_of_allDouble
      S b hb (by simpa [S] using hfive)
    intro c hc hcb
    exact hallDoubleAt c (by simpa [S] using hc)
      (by simpa [b] using hcb)
  have hA23 : elevenFiveRelativeCount S D 2 3 = 4 := by
    rw [← hDb]
    apply relativeCount_two_three_eq_four_of_allDouble
      S b hb (by simpa [S] using hfive)
    intro c hc hcb
    have h := hallDoubleAt c (by simpa [S] using hc)
      (by simpa [b] using hcb)
    simpa [Finset.inter_comm, b] using h
  have hhostRow :=
    elevenFiveHostWeight_eq_relativeCount22_add_three_mul_relativeCount23
      S D (by simpa [S] using hcap)
  have hhostS : elevenFiveHostWeight S D = 28 := by
    simpa [S, D] using hhost
  have hA22 : elevenFiveRelativeCount S D 2 2 = 16 := by
    omega
  let H := (Finset.univ : Finset Point).filter fun p =>
    S.blockDegree 3 p = 9
  let K := D.filter fun p => S.blockDegree 3 p = 9
  obtain ⟨hHcard, hthreeValues⟩ :=
    elevenFive_c40_l11_b5_five_threeDegree_census
      S hpoint (by simpa [S] using hlocal) (by simpa [S] using hglobal)
        (by simpa [S] using hC) (by simpa [S] using hL)
          (by simpa [S] using hfive) (by simpa [S] using hbeta)
  have hKsub : K ⊆ H := by
    intro p hp
    have hpK := Finset.mem_filter.mp hp
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ p, hpK.2⟩
  have hKcard : K.card ≤ 1 := by
    have hle := Finset.card_le_card hKsub
    have hHcard' : H.card = 1 := by simpa [H] using hHcard
    omega
  have hpointThree (p : Point) : S.blockDegree 3 p =
      6 + (if S.blockDegree 3 p = 9 then 3 else 0) := by
    rcases hthreeValues p with hp | hp
    · simp [hp]
    · simp [hp]
  have hindicator :
      (∑ p ∈ D, if S.blockDegree 3 p = 9 then 3 else 0) =
        3 * K.card := by
    rw [← Finset.sum_filter]
    change (∑ _p ∈ K, 3) = 3 * K.card
    simp [Nat.mul_comm]
  have hsumThreeLe : (∑ p ∈ D, S.blockDegree 3 p) ≤ 33 := by
    calc
      (∑ p ∈ D, S.blockDegree 3 p) =
          ∑ p ∈ D, (6 +
            (if S.blockDegree 3 p = 9 then 3 else 0)) := by
        apply Finset.sum_congr rfl
        intro p _hp
        exact hpointThree p
      _ = (∑ _p ∈ D, 6) +
          (∑ p ∈ D, if S.blockDegree 3 p = 9 then 3 else 0) := by
        rw [Finset.sum_add_distrib]
      _ = 6 * D.card + 3 * K.card := by
        rw [hindicator]
        simp [Nat.mul_comm]
      _ ≤ 33 := by
        have hDcard : D.card = 5 := by simpa [D] using hD
        omega
  have hsumPair :
      (∑ p ∈ D, (S.blockDegree 3 p + 3 * S.blockDegree 4 p +
        6 * S.blockDegree 5 p)) = ∑ _p ∈ D, 45 := by
    apply Finset.sum_congr rfl
    intro p _hp
    simpa [S] using (hlocal p).pairRow
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at hsumPair
  have hsumFourLower : 38 ≤ (∑ p ∈ D, S.blockDegree 4 p) := by
    rw [hsumFive] at hsumPair
    have hDcard : D.card = 5 := by simpa [D] using hD
    have hconst : (∑ _p ∈ D, 45) = 225 := by simp [hDcard]
    rw [hconst] at hsumPair
    omega
  have hfourRelative :=
    selectedFive_support_degree_eq_relativeCount_one_two
      S b hb 4 3 2 (by omega) (by omega) (by omega)
  rw [hDb] at hfourRelative
  have hpageCapS : elevenFiveRelativeCount S D 1 3 ≤ 4 := by
    simpa [S, D] using hpageCap
  omega

/-- The all-double face with no degree-four five-block pivot contains an
actual proper five-circle avoiding the unique degree-nine pivot; the
preceding K2.1 endpoint therefore excludes it. -/
theorem elevenFive_c40_l11_b5_five_allDouble_noDegreeFour_impossible
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    (cfg : Configuration Point)
    (hpoint : Fintype.card Point = 11)
    (hcap : BlockSizeCap (blockSystem cfg) 5)
    (hlocal : ∀ p : Point, ElevenFiveLocalRows (blockSystem cfg) p)
    (hglobal : ElevenFiveGlobalRows (blockSystem cfg))
    (hC : (blockSystem cfg).totalCircleCount = 40)
    (hL : elevenFiveLineTotal (blockSystem cfg) = 11)
    (hfive : (blockSystem cfg).blockCount 5 = 5)
    (hbeta : ∀ p : Point,
      (blockSystem cfg).blockDegree 3 p +
        (blockSystem cfg).blockDegree 4 p +
          (blockSystem cfg).blockDegree 5 p ≤ 18)
    (hmoment : elevenFiveSecondMoment (blockSystem cfg) = 20)
    (hfourDegree :
      elevenFiveC40SmallFiveDegreeCount (blockSystem cfg) 4 = 0) : False := by
  classical
  let S := blockSystem cfg
  let H := (Finset.univ : Finset Point).filter fun p =>
    S.blockDegree 3 p = 9
  obtain ⟨hHcard, hthreeValues⟩ :=
    elevenFive_c40_l11_b5_five_threeDegree_census
      S hpoint (by simpa [S] using hlocal) (by simpa [S] using hglobal)
        (by simpa [S] using hC) (by simpa [S] using hL)
          (by simpa [S] using hfive) (by simpa [S] using hbeta)
  have hHcard' : H.card = 1 := by simpa [H] using hHcard
  have hHpos : 0 < H.card := by omega
  obtain ⟨q, hqH⟩ := Finset.card_pos.mp hHpos
  have hqThree : S.blockDegree 3 q = 9 := (Finset.mem_filter.mp hqH).2
  have hfourCard : ((Finset.univ : Finset Point).filter fun p =>
      S.blockDegree 5 p = 4).card = 0 := by
    simpa [S, elevenFiveC40SmallFiveDegreeCount] using hfourDegree
  have hfourEmpty : ((Finset.univ : Finset Point).filter fun p =>
      S.blockDegree 5 p = 4) = ∅ := Finset.card_eq_zero.mp hfourCard
  have hnoFour (p : Point) : S.blockDegree 5 p ≠ 4 := by
    intro hp
    have hpMem : p ∈ ((Finset.univ : Finset Point).filter fun x =>
        S.blockDegree 5 x = 4) := by simp [hp]
    rw [hfourEmpty] at hpMem
    simp at hpMem
  have hqFive : S.blockDegree 5 q = 3 := by
    rcases elevenFive_c40_l11_pivot_domains_of_beta_cap
      S q (hlocal q) hC (hbeta q) with
        ⟨hqSix, _hlow⟩ | ⟨_hqNine, hhigh⟩
    · omega
    · rcases hhigh with hthree | hfour
      · exact hthree
      · exact False.elim (hnoFour q hfour)
  have hallDouble :=
    fiveBlock_inter_card_eq_two_of_secondMoment_twenty
      S (by simpa [S] using hfive) (by simpa [S] using hmoment)
  have hlineLe : S.lineCount 5 ≤ 1 :=
    fiveBlock_lineCount_le_one_of_allDouble S hallDouble
  have hsplit := S.blockCount_eq_lineCount_add_circleCount 5
  have hcircleGe : 4 ≤ S.circleCount 5 := by
    rw [show S.blockCount 5 = 5 by simpa [S] using hfive] at hsplit
    omega
  have hcircleAvoids : ∃ b ∈ S.circleBlocksOfSize 5,
      q ∉ S.support b := by
    by_contra hnot
    have hallCircle : ∀ b ∈ S.circleBlocksOfSize 5,
        q ∈ S.support b := by
      intro b hb
      by_contra hqb
      exact hnot ⟨b, hb, hqb⟩
    have hcircleFilter :
        (S.circleBlocksOfSize 5).filter (fun b => q ∈ S.support b) =
          S.circleBlocksOfSize 5 := by
      exact Finset.filter_eq_self.mpr hallCircle
    have hfilterSub :
        (S.circleBlocksOfSize 5).filter (fun b => q ∈ S.support b) ⊆
          (S.blocksOfSize 5).filter (fun b => q ∈ S.support b) := by
      intro b hb
      have hb' := Finset.mem_filter.mp hb
      apply Finset.mem_filter.mpr
      exact ⟨S.mem_blocksOfSize.mpr
        (S.mem_blocksOfKindSize.mp hb'.1).2, hb'.2⟩
    have hcircleDegree : S.circleDegree 5 q = S.circleCount 5 := by
      unfold BlockSystem.circleDegree BlockSystem.degreeIn
        BlockSystem.circleCount
      rw [hcircleFilter]
    have hdegreeLe' : S.circleDegree 5 q ≤ S.blockDegree 5 q := by
      simpa [BlockSystem.circleDegree, BlockSystem.blockDegree,
        BlockSystem.degreeIn] using Finset.card_le_card hfilterSub
    rw [hcircleDegree, hqFive] at hdegreeLe'
    omega
  obtain ⟨b, hbCircle, hqb⟩ := hcircleAvoids
  rcases b with L | Gamma
  · have hkind := (S.mem_blocksOfKindSize.mp hbCircle).1
    simp [S, blockSystem, geometricBlockSystem, geometricBlockKind] at hkind
  · have hD : (circleTrace cfg Gamma.1).card = 5 := by
      have hsize := (S.mem_blocksOfKindSize.mp hbCircle).2
      simpa [S, blockSystem, geometricBlockSystem,
        geometricBlockSupport] using hsize
    have hqOutside : q ∉ circleTrace cfg Gamma.1 := by
      simpa [S, blockSystem, geometricBlockSystem,
        geometricBlockSupport] using hqb
    have hlow : ∀ p ∈ circleTrace cfg Gamma.1,
        S.blockDegree 3 p = 6 := by
      intro p hp
      rcases hthreeValues p with hpSix | hpNine
      · exact hpSix
      · have hpH : p ∈ H := by simp [H, hpNine]
        have hpq := Finset.card_le_one.mp (by omega : H.card ≤ 1)
          p hpH q hqH
        subst p
        exact False.elim (hqOutside hp)
    have hfourBlock : S.blockCount 4 = 23 := by
      have htriple := hglobal.tripleRow
      have htotal := hglobal.blockTotal
      rw [hfive] at htriple
      rw [hC, hL, hfive] at htotal
      change S.blockCount 3 + 4 * S.blockCount 4 + 10 * 5 = 165 at htriple
      change S.blockCount 3 + S.blockCount 4 + 5 = 40 + 11 at htotal
      omega
    exact elevenFive_allDouble_low_properFiveCircle_absurd
      cfg Gamma hpoint hcap hlocal hD (by simpa [S] using hfourBlock)
        hfive (by
          intro c hc hcb
          exact hallDouble (Sum.inr Gamma)
            (by simpa [S, blockSystem, geometricBlockSystem,
              geometricBlockSupport] using hD)
            c hc hcb.symm)
          (by simpa [S] using hlow)

/-- Every surviving all-double five-block face exposes an actual H28
proper-circle fibre with no singleton five-block neighbour.  If the chosen
circle avoids the unique high pivot, K2.1 already gives a contradiction;
otherwise its trace has degree-three mass 33 and the preceding router
forces host weight 28. -/
theorem elevenFive_c40_l11_b5_five_allDouble_exists_h28_zeroFibre
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    (cfg : Configuration Point)
    (hpoint : Fintype.card Point = 11)
    (hcap : BlockSizeCap (blockSystem cfg) 5)
    (hlocal : ∀ p : Point, ElevenFiveLocalRows (blockSystem cfg) p)
    (hglobal : ElevenFiveGlobalRows (blockSystem cfg))
    (hC : (blockSystem cfg).totalCircleCount = 40)
    (hL : elevenFiveLineTotal (blockSystem cfg) = 11)
    (hfive : (blockSystem cfg).blockCount 5 = 5)
    (hbeta : ∀ p : Point,
      (blockSystem cfg).blockDegree 3 p +
        (blockSystem cfg).blockDegree 4 p +
          (blockSystem cfg).blockDegree 5 p ≤ 18)
    (hmoment : elevenFiveSecondMoment (blockSystem cfg) = 20) :
    ∃ Gamma : DeterminedCircle cfg,
      (circleTrace cfg Gamma.1).card = 5 ∧
      elevenFiveHostWeight (blockSystem cfg)
        (circleTrace cfg Gamma.1) = 28 ∧
      elevenFiveRelativeCount (blockSystem cfg)
        (circleTrace cfg Gamma.1) 1 4 = 0 := by
  classical
  let S := blockSystem cfg
  have hallDouble :=
    fiveBlock_inter_card_eq_two_of_secondMoment_twenty
      S (by simpa [S] using hfive) (by simpa [S] using hmoment)
  have hlineLe : S.lineCount 5 ≤ 1 :=
    fiveBlock_lineCount_le_one_of_allDouble S hallDouble
  have hsplit := S.blockCount_eq_lineCount_add_circleCount 5
  have hcircleGe : 4 ≤ S.circleCount 5 := by
    rw [show S.blockCount 5 = 5 by simpa [S] using hfive] at hsplit
    omega
  have hcircleNonempty : (S.circleBlocksOfSize 5).Nonempty := by
    rw [← Finset.card_pos]
    change 0 < S.circleCount 5
    omega
  obtain ⟨b, hbCircle⟩ := hcircleNonempty
  rcases b with L | Gamma
  · have hkind := (S.mem_blocksOfKindSize.mp hbCircle).1
    simp [S, blockSystem, geometricBlockSystem, geometricBlockKind] at hkind
  · have hD : (circleTrace cfg Gamma.1).card = 5 := by
      have hsize := (S.mem_blocksOfKindSize.mp hbCircle).2
      simpa [S, blockSystem, geometricBlockSystem,
        geometricBlockSupport] using hsize
    let base : GeometricBlock cfg := Sum.inr Gamma
    have hbase : base ∈ S.blocksOfSize 5 := by
      apply S.mem_blocksOfSize.mpr
      simpa [S, base, blockSystem, geometricBlockSystem,
        geometricBlockSupport] using hD
    have hallAt : ∀ c ∈ (blockSystem cfg).blocksOfSize 5,
        c ≠ (Sum.inr Gamma : GeometricBlock cfg) →
          ((blockSystem cfg).support (Sum.inr Gamma) ∩
            (blockSystem cfg).support c).card = 2 := by
      intro c hc hcb
      have hcS : c ∈ S.blocksOfSize 5 := by simpa [S] using hc
      have hdouble := hallDouble base hbase c hcS (by
        simpa [base] using hcb.symm)
      simpa [S, base] using hdouble
    obtain ⟨hhost, hzero⟩ :=
      elevenFive_c40_l11_b5_five_doubleNeighbourCircle_h28_zeroFibre
        cfg Gamma hpoint hcap hlocal hglobal hC hL hfive hbeta hD hallAt
    exact ⟨Gamma, hD, hhost, hzero⟩

/-- In the two-defect face, one of the three blocks outside the unique
disjoint pair is an actual proper circle.  Its four other five-blocks all
meet it twice.  This strengthened selector deliberately retains that local
incidence datum for the page-cap endpoint. -/
theorem elevenFive_c40_l11_b5_five_twoDefect_exists_doubleNeighbourCircle
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    (cfg : Configuration Point)
    (hpoint : Fintype.card Point = 11)
    (hlocal : ∀ p : Point, ElevenFiveLocalRows (blockSystem cfg) p)
    (hC : (blockSystem cfg).totalCircleCount = 40)
    (hfive : (blockSystem cfg).blockCount 5 = 5)
    (hbeta : ∀ p : Point,
      (blockSystem cfg).blockDegree 3 p +
        (blockSystem cfg).blockDegree 4 p +
          (blockSystem cfg).blockDegree 5 p ≤ 18)
    (hmoment : elevenFiveSecondMoment (blockSystem cfg) = 18) :
    ∃ Gamma : DeterminedCircle cfg,
      (circleTrace cfg Gamma.1).card = 5 ∧
      ∀ c ∈ (blockSystem cfg).blocksOfSize 5,
        c ≠ (Sum.inr Gamma : GeometricBlock cfg) →
          ((blockSystem cfg).support (Sum.inr Gamma) ∩
            (blockSystem cfg).support c).card = 2 := by
  classical
  let S := blockSystem cfg
  let F := S.blocksOfSize 5
  have hnoSingleton : ∀ b ∈ S.blocksOfSize 5,
      ∀ c ∈ S.blocksOfSize 5, b ≠ c →
        (S.support b ∩ S.support c).card ≠ 1 := by
    intro b hb c hc hbc hsingle
    obtain ⟨p, hpEq⟩ := Finset.card_eq_one.mp hsingle
    have hp : p ∈ S.support b ∩ S.support c := by
      rw [hpEq]
      simp
    exact elevenFive_c40_l11_fiveBlock_singleton_impossible
      cfg hpoint p (hlocal p) hC (hbeta p) hb hc
        (Finset.mem_inter.mp hp).1 (Finset.mem_inter.mp hp).2
          hbc hsingle
  obtain ⟨f, hf, g, hg, hfg, _hdisjoint, hallDouble, _hunique,
      _q, _hq, _hqUnique⟩ :=
    fiveBlock_unique_disjoint_pair_outsider_degree_three_of_five
      S hpoint (by simpa [S] using hfive)
        (by simpa [S] using hmoment) hnoSingleton
  have hFcard : F.card = 5 := by
    simpa [F, BlockSystem.blockCount] using
      (show S.blockCount 5 = 5 by simpa [S] using hfive)
  have hgfMem : g ∈ F.erase f := by
    exact Finset.mem_erase.mpr
      ⟨hfg.symm, by simpa [F] using hg⟩
  let R := (F.erase f).erase g
  have hRcard : R.card = 3 := by
    dsimp [R]
    rw [Finset.card_erase_of_mem hgfMem,
      Finset.card_erase_of_mem (by simpa [F] using hf), hFcard]
  have hRspec (b : GeometricBlock cfg) (hb : b ∈ R) :
      b ∈ S.blocksOfSize 5 ∧ b ≠ f ∧ b ≠ g := by
    have hbg := Finset.mem_erase.mp hb
    have hbf := Finset.mem_erase.mp hbg.2
    exact ⟨by simpa [F] using hbf.2, hbf.1, hbg.1⟩
  have hpairNe (b : GeometricBlock cfg) (hb : b ∈ R)
      (c : GeometricBlock cfg) :
      ({b, c} : Finset (GeometricBlock cfg)) ≠ {f, g} := by
    intro hpair
    have hbFG : b ∈ ({f, g} : Finset (GeometricBlock cfg)) := by
      rw [← hpair]
      simp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hbFG
    rcases hbFG with hbf | hbg
    · exact (hRspec b hb).2.1 hbf
    · exact (hRspec b hb).2.2 hbg
  have hcircleFinish (Gamma : DeterminedCircle cfg)
      (hGammaR : (Sum.inr Gamma : GeometricBlock cfg) ∈ R) :
      ∃ Delta : DeterminedCircle cfg,
        (circleTrace cfg Delta.1).card = 5 ∧
        ∀ c ∈ (blockSystem cfg).blocksOfSize 5,
          c ≠ (Sum.inr Delta : GeometricBlock cfg) →
            ((blockSystem cfg).support (Sum.inr Delta) ∩
              (blockSystem cfg).support c).card = 2 := by
    have hbase := (hRspec (Sum.inr Gamma) hGammaR).1
    have hD : (circleTrace cfg Gamma.1).card = 5 := by
      have hsize := S.mem_blocksOfSize.mp hbase
      simpa [S, blockSystem, geometricBlockSystem,
        geometricBlockSupport] using hsize
    have hallAt : ∀ c ∈ (blockSystem cfg).blocksOfSize 5,
        c ≠ (Sum.inr Gamma : GeometricBlock cfg) →
          ((blockSystem cfg).support (Sum.inr Gamma) ∩
            (blockSystem cfg).support c).card = 2 := by
      intro c hc hcb
      have hcS : c ∈ S.blocksOfSize 5 := by simpa [S] using hc
      have hdouble := hallDouble (Sum.inr Gamma) hbase c hcS hcb.symm
        (hpairNe (Sum.inr Gamma) hGammaR c)
      simpa [S] using hdouble
    exact ⟨Gamma, hD, hallAt⟩
  have hRtwo : 1 < R.card := by omega
  obtain ⟨b, hbR, c, hcR, hbc⟩ := Finset.one_lt_card.mp hRtwo
  rcases b with Lb | Gamma
  · rcases c with Lc | Delta
    · have hbFive := (hRspec (Sum.inl Lb) hbR).1
      have hcFive := (hRspec (Sum.inl Lc) hcR).1
      have hdouble := hallDouble (Sum.inl Lb) hbFive
        (Sum.inl Lc) hcFive hbc
          (hpairNe (Sum.inl Lb) hbR (Sum.inl Lc))
      let lb : LineBlock S := ⟨Sum.inl Lb, by
        simp [S, blockSystem, geometricBlockSystem, geometricBlockKind]⟩
      let lc : LineBlock S := ⟨Sum.inl Lc, by
        simp [S, blockSystem, geometricBlockSystem, geometricBlockKind]⟩
      have hlbc : lb ≠ lc := by
        intro h
        exact hbc (congrArg Subtype.val h)
      have hline := S.distinct_line_inter_card_lt_two hlbc
      have hline' :
          (S.support (Sum.inl Lb) ∩ S.support (Sum.inl Lc)).card < 2 := by
        simpa [lb, lc] using hline
      omega
    · exact hcircleFinish Delta hcR
  · exact hcircleFinish Gamma hbR

/-- In the two-defect face the three five-blocks outside the unique
disjoint pair are mutually double.  Two of them cannot both be line
blocks, so one is an actual proper five-circle with four double
five-block neighbours; the common router therefore exposes its H28
zero fibre. -/
theorem elevenFive_c40_l11_b5_five_twoDefect_exists_h28_zeroFibre
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    (cfg : Configuration Point)
    (hpoint : Fintype.card Point = 11)
    (hcap : BlockSizeCap (blockSystem cfg) 5)
    (hlocal : ∀ p : Point, ElevenFiveLocalRows (blockSystem cfg) p)
    (hglobal : ElevenFiveGlobalRows (blockSystem cfg))
    (hC : (blockSystem cfg).totalCircleCount = 40)
    (hL : elevenFiveLineTotal (blockSystem cfg) = 11)
    (hfive : (blockSystem cfg).blockCount 5 = 5)
    (hbeta : ∀ p : Point,
      (blockSystem cfg).blockDegree 3 p +
        (blockSystem cfg).blockDegree 4 p +
          (blockSystem cfg).blockDegree 5 p ≤ 18)
    (hmoment : elevenFiveSecondMoment (blockSystem cfg) = 18) :
    ∃ Gamma : DeterminedCircle cfg,
      (circleTrace cfg Gamma.1).card = 5 ∧
      elevenFiveHostWeight (blockSystem cfg)
        (circleTrace cfg Gamma.1) = 28 ∧
      elevenFiveRelativeCount (blockSystem cfg)
        (circleTrace cfg Gamma.1) 1 4 = 0 := by
  classical
  let S := blockSystem cfg
  let F := S.blocksOfSize 5
  have hnoSingleton : ∀ b ∈ S.blocksOfSize 5,
      ∀ c ∈ S.blocksOfSize 5, b ≠ c →
        (S.support b ∩ S.support c).card ≠ 1 := by
    intro b hb c hc hbc hsingle
    obtain ⟨p, hpEq⟩ := Finset.card_eq_one.mp hsingle
    have hp : p ∈ S.support b ∩ S.support c := by
      rw [hpEq]
      simp
    exact elevenFive_c40_l11_fiveBlock_singleton_impossible
      cfg hpoint p (hlocal p) hC (hbeta p) hb hc
        (Finset.mem_inter.mp hp).1 (Finset.mem_inter.mp hp).2
          hbc hsingle
  obtain ⟨f, hf, g, hg, hfg, _hdisjoint, hallDouble, _hunique,
      _q, _hq, _hqUnique⟩ :=
    fiveBlock_unique_disjoint_pair_outsider_degree_three_of_five
      S hpoint (by simpa [S] using hfive)
        (by simpa [S] using hmoment) hnoSingleton
  have hFcard : F.card = 5 := by
    simpa [F, BlockSystem.blockCount] using
      (show S.blockCount 5 = 5 by simpa [S] using hfive)
  have hgfMem : g ∈ F.erase f := by
    exact Finset.mem_erase.mpr
      ⟨hfg.symm, by simpa [F] using hg⟩
  let R := (F.erase f).erase g
  have hRcard : R.card = 3 := by
    dsimp [R]
    rw [Finset.card_erase_of_mem hgfMem,
      Finset.card_erase_of_mem (by simpa [F] using hf), hFcard]
  have hRspec (b : GeometricBlock cfg) (hb : b ∈ R) :
      b ∈ S.blocksOfSize 5 ∧ b ≠ f ∧ b ≠ g := by
    have hbg := Finset.mem_erase.mp hb
    have hbf := Finset.mem_erase.mp hbg.2
    exact ⟨by simpa [F] using hbf.2, hbf.1, hbg.1⟩
  have hpairNe (b : GeometricBlock cfg) (hb : b ∈ R)
      (c : GeometricBlock cfg) :
      ({b, c} : Finset (GeometricBlock cfg)) ≠ {f, g} := by
    intro hpair
    have hbFG : b ∈ ({f, g} : Finset (GeometricBlock cfg)) := by
      rw [← hpair]
      simp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hbFG
    rcases hbFG with hbf | hbg
    · exact (hRspec b hb).2.1 hbf
    · exact (hRspec b hb).2.2 hbg
  have hcircleFinish (Gamma : DeterminedCircle cfg)
      (hGammaR : (Sum.inr Gamma : GeometricBlock cfg) ∈ R) :
      ∃ Delta : DeterminedCircle cfg,
        (circleTrace cfg Delta.1).card = 5 ∧
        elevenFiveHostWeight (blockSystem cfg)
          (circleTrace cfg Delta.1) = 28 ∧
        elevenFiveRelativeCount (blockSystem cfg)
          (circleTrace cfg Delta.1) 1 4 = 0 := by
    have hbase := (hRspec (Sum.inr Gamma) hGammaR).1
    have hD : (circleTrace cfg Gamma.1).card = 5 := by
      have hsize := S.mem_blocksOfSize.mp hbase
      simpa [S, blockSystem, geometricBlockSystem,
        geometricBlockSupport] using hsize
    have hallAt : ∀ c ∈ (blockSystem cfg).blocksOfSize 5,
        c ≠ (Sum.inr Gamma : GeometricBlock cfg) →
          ((blockSystem cfg).support (Sum.inr Gamma) ∩
            (blockSystem cfg).support c).card = 2 := by
      intro c hc hcb
      have hcS : c ∈ S.blocksOfSize 5 := by simpa [S] using hc
      have hdouble := hallDouble (Sum.inr Gamma) hbase c hcS hcb.symm
        (hpairNe (Sum.inr Gamma) hGammaR c)
      simpa [S] using hdouble
    obtain ⟨hhost, hzero⟩ :=
      elevenFive_c40_l11_b5_five_doubleNeighbourCircle_h28_zeroFibre
        cfg Gamma hpoint hcap hlocal hglobal hC hL hfive hbeta hD hallAt
    exact ⟨Gamma, hD, hhost, hzero⟩
  have hRtwo : 1 < R.card := by omega
  obtain ⟨b, hbR, c, hcR, hbc⟩ := Finset.one_lt_card.mp hRtwo
  rcases b with Lb | Gamma
  · rcases c with Lc | Delta
    · have hbFive := (hRspec (Sum.inl Lb) hbR).1
      have hcFive := (hRspec (Sum.inl Lc) hcR).1
      have hdouble := hallDouble (Sum.inl Lb) hbFive
        (Sum.inl Lc) hcFive hbc
          (hpairNe (Sum.inl Lb) hbR (Sum.inl Lc))
      let lb : LineBlock S := ⟨Sum.inl Lb, by
        simp [S, blockSystem, geometricBlockSystem, geometricBlockKind]⟩
      let lc : LineBlock S := ⟨Sum.inl Lc, by
        simp [S, blockSystem, geometricBlockSystem, geometricBlockKind]⟩
      have hlbc : lb ≠ lc := by
        intro h
        exact hbc (congrArg Subtype.val h)
      have hline := S.distinct_line_inter_card_lt_two hlbc
      have hline' :
          (S.support (Sum.inl Lb) ∩ S.support (Sum.inl Lc)).card < 2 := by
        simpa [lb, lc] using hline
      omega
    · exact hcircleFinish Delta hcR
  · exact hcircleFinish Gamma hbR

/-- The two faces which genuinely need the K2.4 golden-axis incidence
extraction.  The K2.1 all-double/low face is deliberately absent. -/
def ElevenFiveC40B5FiveGoldenResidual
    {Point : Type u} {Block : Type v} [Fintype Point] [Fintype Block]
    [DecidableEq Point]
    (S : BlockSystem Point Block) : Prop :=
  (elevenFiveSecondMoment S = 18 ∧
      elevenFiveC40SmallFiveDegreeCount S 4 = 0 ∧
      elevenFiveC40SmallFiveDegreeCount S 1 = 1 ∧
      elevenFiveC40SmallFiveDegreeCount S 2 = 6) ∨
    (elevenFiveSecondMoment S = 20 ∧
      elevenFiveC40SmallFiveDegreeCount S 4 = 1 ∧
      elevenFiveC40SmallFiveDegreeCount S 1 = 2 ∧
      elevenFiveC40SmallFiveDegreeCount S 2 = 5)

/-- Exact unconditional reduction after applying K2.1: only the two
golden-axis branches remain. -/
theorem elevenFive_c40_l11_b5_five_geometricResidual_reduces_to_goldenResidual
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    (cfg : Configuration Point)
    (hpoint : Fintype.card Point = 11)
    (hcap : BlockSizeCap (blockSystem cfg) 5)
    (hlocal : ∀ p : Point, ElevenFiveLocalRows (blockSystem cfg) p)
    (hglobal : ElevenFiveGlobalRows (blockSystem cfg))
    (hC : (blockSystem cfg).totalCircleCount = 40)
    (hL : elevenFiveLineTotal (blockSystem cfg) = 11)
    (hfive : (blockSystem cfg).blockCount 5 = 5)
    (hbeta : ∀ p : Point,
      (blockSystem cfg).blockDegree 3 p +
        (blockSystem cfg).blockDegree 4 p +
          (blockSystem cfg).blockDegree 5 p ≤ 18)
    (hresidual :
      ElevenFiveC40B5FiveGeometricResidual (blockSystem cfg)) :
    ElevenFiveC40B5FiveGoldenResidual (blockSystem cfg) := by
  rcases hresidual with htwoDefect | hallDoubleLow | hallDoubleHigh
  · exact Or.inl htwoDefect
  · exact False.elim
      (elevenFive_c40_l11_b5_five_allDouble_noDegreeFour_impossible
        cfg hpoint hcap hlocal hglobal hC hL hfive hbeta
          hallDoubleLow.1 hallDoubleLow.2.1)
  · exact Or.inr hallDoubleHigh

/-- Both surviving numerical faces expose the same actual H28 proper-circle
zero fibre.  This is the maximal unconditional entrance to the existing
K2.4 golden-axis adapter. -/
theorem elevenFive_c40_l11_b5_five_goldenResidual_exists_h28_zeroFibre
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    (cfg : Configuration Point)
    (hpoint : Fintype.card Point = 11)
    (hcap : BlockSizeCap (blockSystem cfg) 5)
    (hlocal : ∀ p : Point, ElevenFiveLocalRows (blockSystem cfg) p)
    (hglobal : ElevenFiveGlobalRows (blockSystem cfg))
    (hC : (blockSystem cfg).totalCircleCount = 40)
    (hL : elevenFiveLineTotal (blockSystem cfg) = 11)
    (hfive : (blockSystem cfg).blockCount 5 = 5)
    (hbeta : ∀ p : Point,
      (blockSystem cfg).blockDegree 3 p +
        (blockSystem cfg).blockDegree 4 p +
          (blockSystem cfg).blockDegree 5 p ≤ 18)
    (hresidual :
      ElevenFiveC40B5FiveGoldenResidual (blockSystem cfg)) :
    ∃ Gamma : DeterminedCircle cfg,
      (circleTrace cfg Gamma.1).card = 5 ∧
      elevenFiveHostWeight (blockSystem cfg)
        (circleTrace cfg Gamma.1) = 28 ∧
      elevenFiveRelativeCount (blockSystem cfg)
        (circleTrace cfg Gamma.1) 1 4 = 0 := by
  rcases hresidual with htwoDefect | hallDoubleHigh
  · exact elevenFive_c40_l11_b5_five_twoDefect_exists_h28_zeroFibre
      cfg hpoint hcap hlocal hglobal hC hL hfive hbeta htwoDefect.1
  · exact elevenFive_c40_l11_b5_five_allDouble_exists_h28_zeroFibre
      cfg hpoint hcap hlocal hglobal hC hL hfive hbeta hallDoubleHigh.1

/-- Full unconditional numerical-to-geometric front for `B₅ = 5`: the
K2.1 face is impossible, and either remaining face produces an actual H28
zero fibre. -/
theorem elevenFive_c40_l11_b5_five_geometricResidual_exists_h28_zeroFibre
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    (cfg : Configuration Point)
    (hpoint : Fintype.card Point = 11)
    (hcap : BlockSizeCap (blockSystem cfg) 5)
    (hlocal : ∀ p : Point, ElevenFiveLocalRows (blockSystem cfg) p)
    (hglobal : ElevenFiveGlobalRows (blockSystem cfg))
    (hC : (blockSystem cfg).totalCircleCount = 40)
    (hL : elevenFiveLineTotal (blockSystem cfg) = 11)
    (hfive : (blockSystem cfg).blockCount 5 = 5)
    (hbeta : ∀ p : Point,
      (blockSystem cfg).blockDegree 3 p +
        (blockSystem cfg).blockDegree 4 p +
          (blockSystem cfg).blockDegree 5 p ≤ 18)
    (hresidual :
      ElevenFiveC40B5FiveGeometricResidual (blockSystem cfg)) :
    ∃ Gamma : DeterminedCircle cfg,
      (circleTrace cfg Gamma.1).card = 5 ∧
      elevenFiveHostWeight (blockSystem cfg)
        (circleTrace cfg Gamma.1) = 28 ∧
      elevenFiveRelativeCount (blockSystem cfg)
        (circleTrace cfg Gamma.1) 1 4 = 0 := by
  apply elevenFive_c40_l11_b5_five_goldenResidual_exists_h28_zeroFibre
    cfg hpoint hcap hlocal hglobal hC hL hfive hbeta
  exact elevenFive_c40_l11_b5_five_geometricResidual_reduces_to_goldenResidual
    cfg hpoint hcap hlocal hglobal hC hL hfive hbeta hresidual

/-- The unconditional pair-fibre page cap removes every remaining
`B₅ = 5` geometric face.  Moment `20` makes the entire five-block family
all-double.  In moment `18`, the strengthened two-defect selector retains
an actual circle outside the unique disjoint pair and hence its four double
neighbours.  Both cases feed the same local page-cap contradiction. -/
theorem elevenFive_c40_l11_b5_five_geometricResidual_impossible
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    (cfg : Configuration Point)
    (hpoint : Fintype.card Point = 11)
    (hcap : BlockSizeCap (blockSystem cfg) 5)
    (hlocal : ∀ p : Point, ElevenFiveLocalRows (blockSystem cfg) p)
    (hglobal : ElevenFiveGlobalRows (blockSystem cfg))
    (hC : (blockSystem cfg).totalCircleCount = 40)
    (hL : elevenFiveLineTotal (blockSystem cfg) = 11)
    (hfive : (blockSystem cfg).blockCount 5 = 5)
    (hbeta : ∀ p : Point,
      (blockSystem cfg).blockDegree 3 p +
        (blockSystem cfg).blockDegree 4 p +
          (blockSystem cfg).blockDegree 5 p ≤ 18) :
    ¬ ElevenFiveC40B5FiveGeometricResidual (blockSystem cfg) := by
  intro hresidual
  have hallDoubleMomentTwenty
      (hmoment : elevenFiveSecondMoment (blockSystem cfg) = 20) : False := by
    classical
    let S := blockSystem cfg
    have hallDouble :=
      fiveBlock_inter_card_eq_two_of_secondMoment_twenty
        S (by simpa [S] using hfive) (by simpa [S] using hmoment)
    obtain ⟨Gamma, hD, _hhost, _hzero⟩ :=
      elevenFive_c40_l11_b5_five_allDouble_exists_h28_zeroFibre
        cfg hpoint hcap hlocal hglobal hC hL hfive hbeta hmoment
    have hbase : (Sum.inr Gamma : GeometricBlock cfg) ∈
        S.blocksOfSize 5 := by
      apply S.mem_blocksOfSize.mpr
      simpa [S, blockSystem, geometricBlockSystem,
        geometricBlockSupport] using hD
    have hallAt : ∀ c ∈ (blockSystem cfg).blocksOfSize 5,
        c ≠ (Sum.inr Gamma : GeometricBlock cfg) →
          ((blockSystem cfg).support (Sum.inr Gamma) ∩
            (blockSystem cfg).support c).card = 2 := by
      intro c hc hcb
      have hdouble := hallDouble (Sum.inr Gamma) hbase c
        (by simpa [S] using hc) hcb.symm
      simpa [S] using hdouble
    exact
      elevenFive_c40_l11_b5_five_doubleNeighbourCircle_impossible_of_pageCap
        cfg Gamma hpoint hcap hlocal hglobal hC hL hfive hbeta hD hallAt
  rcases hresidual with htwoDefect | hallDoubleLow | hallDoubleHigh
  · obtain ⟨Gamma, hD, hallAt⟩ :=
      elevenFive_c40_l11_b5_five_twoDefect_exists_doubleNeighbourCircle
        cfg hpoint hlocal hC hfive hbeta htwoDefect.1
    exact
      elevenFive_c40_l11_b5_five_doubleNeighbourCircle_impossible_of_pageCap
        cfg Gamma hpoint hcap hlocal hglobal hC hL hfive hbeta hD hallAt
  · exact hallDoubleMomentTwenty hallDoubleLow.1
  · exact hallDoubleMomentTwenty hallDoubleHigh.1

/-- Collision-ready configuration-level exclusion of the complete
`B₅ = 5` branch. -/
theorem elevenFive_c40_l11_b5_five_impossible_of_configuration_without_langer
    (Mel : RealPlaneMelchiorPrinciple.{u})
    (EvenArr : RealPlaneEvenArrangementPrinciple.{u})
    (Cross : RealPlaneRadicalAxisCrossBlockPrinciple.{u})
    (Kelly : RealPlaneKellyMoserPrinciple.{u})
    (U17 : RealPlaneSixCircleU17Principle.{u})
    (TenGeometry : RealPlaneTenFiveGeometry.{u})
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    (cfg : Configuration Point) (hadm : Admissible cfg)
    (hpoint : Fintype.card Point = 11)
    (hcap : BlockSizeCap (blockSystem cfg) 5)
    (hC : Erdos506.V4.circleCount cfg = 40)
    (hL : elevenFiveLineTotal (blockSystem cfg) = 11)
    (hfive : (blockSystem cfg).blockCount 5 = 5) : False := by
  have hCtotal : (blockSystem cfg).totalCircleCount = 40 := by
    rw [totalCircleCount_eq_card_determinedCircle,
      ← Erdos506.V3.circleCount_eq_card_determinedCircle]
    exact hC
  have hCupper : (blockSystem cfg).totalCircleCount ≤ 40 := by omega
  have hlocal : ∀ p : Point,
      ElevenFiveLocalRows (blockSystem cfg) p := fun p =>
    elevenFiveLocalRows_of_configuration_without_langer
      Mel EvenArr Cross Kelly U17 TenGeometry
        cfg hadm hpoint hcap hCupper p
  have hglobal : ElevenFiveGlobalRows (blockSystem cfg) :=
    elevenFiveGlobalRows_of_configuration Mel cfg hadm hpoint hcap hlocal
  have hbeta := elevenFive_c40_l11_beta_cap
    Mel EvenArr Cross Kelly U17 TenGeometry
      cfg hadm hpoint hcap hglobal hCtotal hL
  have hresidual :=
    elevenFive_c40_l11_b5_five_reduces_to_geometricResidual
      cfg hpoint hlocal hglobal hCtotal hL hfive hbeta
  exact elevenFive_c40_l11_b5_five_geometricResidual_impossible
    cfg hpoint hcap hlocal hglobal hCtotal hL hfive hbeta hresidual

/-- Compatibility wrapper retaining the historical global parameter list. -/
theorem elevenFive_c40_l11_b5_five_impossible_of_configuration
    (Mel : RealPlaneMelchiorPrinciple.{u})
    (_Langer : RealPlaneLangerPrinciple.{u})
    (EvenArr : RealPlaneEvenArrangementPrinciple.{u})
    (Cross : RealPlaneRadicalAxisCrossBlockPrinciple.{u})
    (Kelly : RealPlaneKellyMoserPrinciple.{u})
    (U17 : RealPlaneSixCircleU17Principle.{u})
    (TenGeometry : RealPlaneTenFiveGeometry.{u})
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    (cfg : Configuration Point) (hadm : Admissible cfg)
    (hpoint : Fintype.card Point = 11)
    (hcap : BlockSizeCap (blockSystem cfg) 5)
    (hC : Erdos506.V4.circleCount cfg = 40)
    (hL : elevenFiveLineTotal (blockSystem cfg) = 11)
    (hfive : (blockSystem cfg).blockCount 5 = 5) : False :=
  elevenFive_c40_l11_b5_five_impossible_of_configuration_without_langer
    Mel EvenArr Cross Kelly U17 TenGeometry
      cfg hadm hpoint hcap hC hL hfive

end Erdos506.V1
