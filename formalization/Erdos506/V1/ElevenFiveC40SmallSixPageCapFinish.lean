import Erdos506.V1.ElevenFiveC40SmallSixFinish
import Erdos506.V1.ElevenFiveC39H30Finish
import Erdos506.V1.ElevenFiveC39H28ZeroFibrePageCap
import Mathlib.Tactic

/-!
# The C40/L11 six-block page-cap finish

The three numerical faces left in `ElevenFiveC40SmallSixFinish` do not in
fact require the K3.2/K3.3 harmonic comparison.  In moment thirty every
pair of size-five blocks is double.  In moment twenty-eight there is one
disjoint pair and every other pair is double.  In either case one can select
an actual proper five-circle whose five other size-five blocks all meet it
twice.

For such a circle the local rows give `A23 = 5`, five-degree mass fifteen,
and host weight in `[28,30]`.  Host weights twenty-nine and thirty contradict
the existing K2.1 page caps.  At host weight twenty-eight the four-page
host-pair-fibre cap contradicts the lower bound `A13 >= 6`.
-/

namespace Erdos506.V1

open Erdos506.Block
open Erdos506.Block.BlockSystem
open Erdos506.Incidence
open Erdos506.V3
open Erdos506.V4
open scoped BigOperators

universe u v

/-- Incidence on a selected size-five block, split into the one- and
two-trace relative fibres of blocks of one fixed, different size. -/
private theorem c40SmallSixPageCap_selected_support_degree
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

/-- Five double neighbours give five-degree mass `5 + 5 * 2 = 15` on
the selected size-five support. -/
private theorem c40SmallSixPageCap_support_fiveDegree_sum_eq_fifteen
    {Point : Type u} {Block : Type v} [Fintype Point] [Fintype Block]
    [DecidableEq Point] [DecidableEq Block]
    (S : BlockSystem Point Block) (b : Block)
    (hb : b ∈ S.blocksOfSize 5)
    (hfive : S.blockCount 5 = 6)
    (hallDouble : ∀ c ∈ S.blocksOfSize 5, c ≠ b →
      (S.support b ∩ S.support c).card = 2) :
    (∑ p ∈ S.support b, S.blockDegree 5 p) = 15 := by
  classical
  let F := S.blocksOfSize 5
  have hbF : b ∈ F := by simpa [F] using hb
  have hFcard : F.card = 6 := by
    simpa [F, BlockSystem.blockCount] using hfive
  have hother (c : Block) (hc : c ∈ F.erase b) :
      (S.support b ∩ S.support c).card = 2 :=
    hallDouble c (by simpa [F] using Finset.mem_of_mem_erase hc)
      (Finset.mem_erase.mp hc).1
  have hotherSum :
      (∑ c ∈ F.erase b, (S.support b ∩ S.support c).card) = 10 := by
    calc
      (∑ c ∈ F.erase b, (S.support b ∩ S.support c).card) =
          ∑ _c ∈ F.erase b, 2 := by
        apply Finset.sum_congr rfl
        intro c hc
        exact hother c hc
      _ = 10 := by
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
    _ = 15 := by rw [hotherSum, hself]

/-- The five other size-five blocks are exactly the selected block's five
relative `(2,3)` blocks. -/
private theorem c40SmallSixPageCap_relativeCount_two_three_eq_five
    {Point : Type u} {Block : Type v} [Fintype Point] [Fintype Block]
    [DecidableEq Point] [DecidableEq Block]
    (S : BlockSystem Point Block) (b : Block)
    (hb : b ∈ S.blocksOfSize 5)
    (hfive : S.blockCount 5 = 6)
    (hallDouble : ∀ c ∈ S.blocksOfSize 5, c ≠ b →
      (S.support c ∩ S.support b).card = 2) :
    elevenFiveRelativeCount S (S.support b) 2 3 = 5 := by
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
  change A.card = 5
  rw [hAF, Finset.card_erase_of_mem hbF]
  have hFcard : F.card = 6 := by
    simpa [F, BlockSystem.blockCount] using hfive
  rw [hFcard]

/-- A double subfamily containing two distinct blocks contains an actual
proper circle: two distinct line blocks cannot meet in two points. -/
private theorem c40SmallSixPageCap_exists_circle_of_double_subfamily
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    (cfg : Configuration Point)
    (R : Finset (GeometricBlock cfg))
    (hRtwo : 1 < R.card)
    (hRfive : ∀ b ∈ R, b ∈ (blockSystem cfg).blocksOfSize 5)
    (hRdouble : ∀ b ∈ R, ∀ c ∈ R, b ≠ c →
      ((blockSystem cfg).support b ∩
        (blockSystem cfg).support c).card = 2)
    (hallAt : ∀ b ∈ R,
      ∀ c ∈ (blockSystem cfg).blocksOfSize 5, c ≠ b →
        ((blockSystem cfg).support b ∩
          (blockSystem cfg).support c).card = 2) :
    ∃ Gamma : DeterminedCircle cfg,
      (circleTrace cfg Gamma.1).card = 5 ∧
      ∀ c ∈ (blockSystem cfg).blocksOfSize 5,
        c ≠ (Sum.inr Gamma : GeometricBlock cfg) →
          ((blockSystem cfg).support (Sum.inr Gamma) ∩
            (blockSystem cfg).support c).card = 2 := by
  classical
  let S := blockSystem cfg
  obtain ⟨b, hbR, c, hcR, hbc⟩ := Finset.one_lt_card.mp hRtwo
  have hcircleFinish (Gamma : DeterminedCircle cfg)
      (hGammaR : (Sum.inr Gamma : GeometricBlock cfg) ∈ R) :
      ∃ Delta : DeterminedCircle cfg,
        (circleTrace cfg Delta.1).card = 5 ∧
        ∀ c ∈ (blockSystem cfg).blocksOfSize 5,
          c ≠ (Sum.inr Delta : GeometricBlock cfg) →
            ((blockSystem cfg).support (Sum.inr Delta) ∩
              (blockSystem cfg).support c).card = 2 := by
    have hbase := hRfive (Sum.inr Gamma) hGammaR
    have hD : (circleTrace cfg Gamma.1).card = 5 := by
      have hsize := S.mem_blocksOfSize.mp (by simpa [S] using hbase)
      simpa [S, blockSystem, geometricBlockSystem,
        geometricBlockSupport] using hsize
    exact ⟨Gamma, hD, hallAt (Sum.inr Gamma) hGammaR⟩
  rcases b with Lb | Gamma
  · rcases c with Lc | Delta
    · have hdouble := hRdouble (Sum.inl Lb) hbR
        (Sum.inl Lc) hcR hbc
      have hdoubleS :
          (S.support (Sum.inl Lb) ∩ S.support (Sum.inl Lc)).card = 2 := by
        simpa [S] using hdouble
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

/-- In the moment-thirty face, any two members of the six-block family
give a proper circle with five double neighbours. -/
theorem elevenFive_c40_l11_b5_six_allDouble_exists_doubleNeighbourCircle
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    (cfg : Configuration Point)
    (hfive : (blockSystem cfg).blockCount 5 = 6)
    (hmoment : elevenFiveSecondMoment (blockSystem cfg) = 30) :
    ∃ Gamma : DeterminedCircle cfg,
      (circleTrace cfg Gamma.1).card = 5 ∧
      ∀ c ∈ (blockSystem cfg).blocksOfSize 5,
        c ≠ (Sum.inr Gamma : GeometricBlock cfg) →
          ((blockSystem cfg).support (Sum.inr Gamma) ∩
            (blockSystem cfg).support c).card = 2 := by
  classical
  let S := blockSystem cfg
  let F := S.blocksOfSize 5
  have hFcard : F.card = 6 := by
    simpa [F, S, BlockSystem.blockCount] using hfive
  have hFtwo : 1 < F.card := by omega
  have hallDouble := elevenFive_c40_l11_b5_six_allDouble_of_secondMoment_thirty
    S (by simpa [S] using hfive) (by simpa [S] using hmoment)
  apply c40SmallSixPageCap_exists_circle_of_double_subfamily cfg F hFtwo
  · intro b hb
    simpa [S, F] using hb
  · intro b hb c hc hbc
    exact hallDouble b (by simpa [F] using hb)
      c (by simpa [F] using hc) hbc
  · intro b hb c hc hcb
    exact hallDouble b (by simpa [F] using hb)
      c (by simpa [S] using hc) hcb.symm

/-- In the moment-twenty-eight face, the four blocks outside the unique
disjoint pair are mutually double.  One of them is a proper circle and it
has five double neighbours in the whole six-block family. -/
theorem elevenFive_c40_l11_b5_six_twoDefect_exists_doubleNeighbourCircle
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    (cfg : Configuration Point)
    (hpoint : Fintype.card Point = 11)
    (hlocal : ∀ p : Point, ElevenFiveLocalRows (blockSystem cfg) p)
    (hC : (blockSystem cfg).totalCircleCount = 40)
    (hfive : (blockSystem cfg).blockCount 5 = 6)
    (hbeta : ∀ p : Point,
      (blockSystem cfg).blockDegree 3 p +
        (blockSystem cfg).blockDegree 4 p +
          (blockSystem cfg).blockDegree 5 p ≤ 18)
    (hmoment : elevenFiveSecondMoment (blockSystem cfg) = 28) :
    ∃ Gamma : DeterminedCircle cfg,
      (circleTrace cfg Gamma.1).card = 5 ∧
      ∀ c ∈ (blockSystem cfg).blocksOfSize 5,
        c ≠ (Sum.inr Gamma : GeometricBlock cfg) →
          ((blockSystem cfg).support (Sum.inr Gamma) ∩
            (blockSystem cfg).support c).card = 2 := by
  classical
  let S := blockSystem cfg
  let F := S.blocksOfSize 5
  obtain ⟨f, hf, g, hg, hfg, _hdisjoint, hallDouble,
      _q, _hq, _Hq⟩ :=
    elevenFive_c40_l11_b5_six_twoDefect_reaches_k32_fourStar
      cfg hpoint hlocal hC hfive hbeta hmoment
  have hfF : f ∈ F := by simpa [F, S] using hf
  have hgF : g ∈ F := by simpa [F, S] using hg
  have hFcard : F.card = 6 := by
    simpa [F, S, BlockSystem.blockCount] using hfive
  have hgfMem : g ∈ F.erase f :=
    Finset.mem_erase.mpr ⟨hfg.symm, hgF⟩
  let R := (F.erase f).erase g
  have hRcard : R.card = 4 := by
    dsimp [R]
    rw [Finset.card_erase_of_mem hgfMem,
      Finset.card_erase_of_mem hfF, hFcard]
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
  have hRtwo : 1 < R.card := by omega
  apply c40SmallSixPageCap_exists_circle_of_double_subfamily cfg R hRtwo
  · intro b hb
    simpa [S] using (hRspec b hb).1
  · intro b hb c hc hbc
    exact hallDouble b (by simpa [S] using (hRspec b hb).1)
      c (by simpa [S] using (hRspec c hc).1) hbc (hpairNe b hb c)
  · intro b hb c hc hcb
    exact hallDouble b (by simpa [S] using (hRspec b hb).1)
      c hc hcb.symm (hpairNe b hb c)

/-- A proper size-five circle with five double size-five neighbours is
incompatible with the H28/H29/H30 page caps. -/
theorem elevenFive_c40_l11_b5_six_doubleNeighbourCircle_impossible_of_pageCap
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    (cfg : Configuration Point) (Gamma : DeterminedCircle cfg)
    (hpoint : Fintype.card Point = 11)
    (hcap : BlockSizeCap (blockSystem cfg) 5)
    (hlocal : ∀ p : Point, ElevenFiveLocalRows (blockSystem cfg) p)
    (hglobal : ElevenFiveGlobalRows (blockSystem cfg))
    (hC : (blockSystem cfg).totalCircleCount = 40)
    (hL : elevenFiveLineTotal (blockSystem cfg) = 11)
    (hfive : (blockSystem cfg).blockCount 5 = 6)
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
  have hallAt : ∀ c ∈ S.blocksOfSize 5, c ≠ b →
      (S.support b ∩ S.support c).card = 2 := by
    intro c hc hcb
    exact hallDoubleAt c (by simpa [S] using hc) (by simpa [b] using hcb)
  have hzero : elevenFiveRelativeCount S D 1 4 = 0 := by
    apply elevenFive_relativeCount_one_four_eq_zero_of_no_sizeFive_singleton
    rintro ⟨c, hc, hinter⟩
    by_cases hcb : c = b
    · subst c
      rw [← hDb] at hinter
      have hbSize := S.mem_blocksOfSize.mp hb
      simp [hbSize] at hinter
    · have htwo := hallAt c hc hcb
      have htwo' : (S.support c ∩ D).card = 2 := by
        rw [← hDb]
        simpa [Finset.inter_comm] using htwo
      omega
  have hsumFive : (∑ p ∈ D, S.blockDegree 5 p) = 15 := by
    rw [← hDb]
    apply c40SmallSixPageCap_support_fiveDegree_sum_eq_fifteen
      S b hb (by simpa [S] using hfive)
    intro c hc hcb
    exact hallAt c hc hcb
  have hA23 : elevenFiveRelativeCount S D 2 3 = 5 := by
    rw [← hDb]
    apply c40SmallSixPageCap_relativeCount_two_three_eq_five
      S b hb (by simpa [S] using hfive)
    intro c hc hcb
    simpa [Finset.inter_comm] using hallAt c hc hcb
  have hrowTwo :=
    elevenFive_relativeCount_two_one_add_two_mul_two_two_add_three_mul_two_three_eq_sixty
      S D b hpoint (by simpa [D] using hD) hb hDb (by simpa [S] using hcap)
  have hhostRow :=
    elevenFiveHostWeight_eq_relativeCount22_add_three_mul_relativeCount23
      S D (by simpa [S] using hcap)
  have hhostCap := elevenFiveHostWeight_le_thirty S D
    hpoint (by simpa [D] using hD)

  let H := (Finset.univ : Finset Point).filter fun p =>
    S.blockDegree 3 p = 9
  let K := D.filter fun p => S.blockDegree 3 p = 9
  obtain ⟨hHcard, hthreeValues⟩ :=
    elevenFive_c40_l11_b5_six_threeDegree_profile
      S hpoint (by simpa [S] using hlocal) (by simpa [S] using hglobal)
        (by simpa [S] using hC) (by simpa [S] using hL)
          (by simpa [S] using hfive) (by simpa [S] using hbeta)
  have hKsub : K ⊆ H := by
    intro p hp
    have hpK := Finset.mem_filter.mp hp
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ p, hpK.2⟩
  have hKcard : K.card ≤ 3 := by
    have hle := Finset.card_le_card hKsub
    have hHcard' : H.card = 3 := by simpa [H] using hHcard
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
  have hsumThreeLe : (∑ p ∈ D, S.blockDegree 3 p) ≤ 39 := by
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
      _ ≤ 39 := by
        have hDcard : D.card = 5 := by simpa [D] using hD
        omega
  have hthreeRelative :=
    c40SmallSixPageCap_selected_support_degree
      S b hb 3 2 1 (by omega) (by omega) (by omega)
  rw [hDb] at hthreeRelative
  have hA21Upper : elevenFiveRelativeCount S D 2 1 ≤ 19 := by
    omega
  have hA22Lower : 13 ≤ elevenFiveRelativeCount S D 2 2 := by
    omega
  have hhostCases : elevenFiveHostWeight S D = 28 ∨
      elevenFiveHostWeight S D = 29 ∨
        elevenFiveHostWeight S D = 30 := by
    omega

  have hsumPair :
      (∑ p ∈ D, (S.blockDegree 3 p + 3 * S.blockDegree 4 p +
        6 * S.blockDegree 5 p)) = ∑ _p ∈ D, 45 := by
    apply Finset.sum_congr rfl
    intro p _hp
    simpa [S] using (hlocal p).pairRow
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at hsumPair
  have hsumFourLower : 32 ≤ (∑ p ∈ D, S.blockDegree 4 p) := by
    rw [hsumFive] at hsumPair
    have hDcard : D.card = 5 := by simpa [D] using hD
    have hconst : (∑ _p ∈ D, 45) = 225 := by simp [hDcard]
    rw [hconst] at hsumPair
    omega
  have hfourRelative :=
    c40SmallSixPageCap_selected_support_degree
      S b hb 4 3 2 (by omega) (by omega) (by omega)
  rw [hDb] at hfourRelative

  rcases hhostCases with hhost | hhost | hhost
  · have hhostCfg : elevenFiveHostWeight (blockSystem cfg)
        (circleTrace cfg Gamma.1) = 28 := by simpa [S, D] using hhost
    have hzeroCfg : elevenFiveRelativeCount (blockSystem cfg)
        (circleTrace cfg Gamma.1) 1 4 = 0 := by simpa [S, D] using hzero
    have hpageCap := elevenFiveC39H28PageCapInput_of_hostPairFibres cfg
      Gamma hpoint hD hhostCfg hzeroCfg
    have hpageCapS : elevenFiveRelativeCount S D 1 3 ≤ 4 := by
      simpa [S, D] using hpageCap
    have hA22 : elevenFiveRelativeCount S D 2 2 = 13 := by omega
    omega
  · have hK21 := elevenFive_c39_h29_relativeCount_one_three_le_one
      cfg Gamma hpoint hD (by simpa [S, D] using hhost)
    have hK21S : elevenFiveRelativeCount S D 1 3 ≤ 1 := by
      simpa [S, D] using hK21
    have hA22 : elevenFiveRelativeCount S D 2 2 = 14 := by omega
    omega
  · have hK21 := elevenFive_c39_h30_relativeCount_one_three_eq_zero
      cfg Gamma hpoint hD (by simpa [S, D] using hhost)
    have hK21S : elevenFiveRelativeCount S D 1 3 = 0 := by
      simpa [S, D] using hK21
    have hA22 : elevenFiveRelativeCount S D 2 2 = 15 := by omega
    omega

/-- Every one of the three former K3.2/K3.3 residual profiles supplies the
same page-cap entrance. -/
theorem elevenFive_c40_l11_b5_six_k32k33Residual_exists_doubleNeighbourCircle
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    (cfg : Configuration Point)
    (hpoint : Fintype.card Point = 11)
    (hlocal : ∀ p : Point, ElevenFiveLocalRows (blockSystem cfg) p)
    (hC : (blockSystem cfg).totalCircleCount = 40)
    (hfive : (blockSystem cfg).blockCount 5 = 6)
    (hbeta : ∀ p : Point,
      (blockSystem cfg).blockDegree 3 p +
        (blockSystem cfg).blockDegree 4 p +
          (blockSystem cfg).blockDegree 5 p ≤ 18)
    (hresidual : ElevenFiveC40B5SixK32K33Residual (blockSystem cfg)) :
    ∃ Gamma : DeterminedCircle cfg,
      (circleTrace cfg Gamma.1).card = 5 ∧
      ∀ c ∈ (blockSystem cfg).blocksOfSize 5,
        c ≠ (Sum.inr Gamma : GeometricBlock cfg) →
          ((blockSystem cfg).support (Sum.inr Gamma) ∩
            (blockSystem cfg).support c).card = 2 := by
  rcases hresidual with htwoDefect | hallDoubleOne | hallDoubleTwo
  · exact elevenFive_c40_l11_b5_six_twoDefect_exists_doubleNeighbourCircle
      cfg hpoint hlocal hC hfive hbeta htwoDefect.1
  · exact elevenFive_c40_l11_b5_six_allDouble_exists_doubleNeighbourCircle
      cfg hfive hallDoubleOne.1
  · exact elevenFive_c40_l11_b5_six_allDouble_exists_doubleNeighbourCircle
      cfg hfive hallDoubleTwo.1

/-- The complete six-block residual is impossible by the local page-cap
argument, without K3.2 or K3.3. -/
theorem elevenFive_c40_l11_b5_six_k32k33Residual_impossible
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    (cfg : Configuration Point)
    (hpoint : Fintype.card Point = 11)
    (hcap : BlockSizeCap (blockSystem cfg) 5)
    (hlocal : ∀ p : Point, ElevenFiveLocalRows (blockSystem cfg) p)
    (hglobal : ElevenFiveGlobalRows (blockSystem cfg))
    (hC : (blockSystem cfg).totalCircleCount = 40)
    (hL : elevenFiveLineTotal (blockSystem cfg) = 11)
    (hfive : (blockSystem cfg).blockCount 5 = 6)
    (hbeta : ∀ p : Point,
      (blockSystem cfg).blockDegree 3 p +
        (blockSystem cfg).blockDegree 4 p +
          (blockSystem cfg).blockDegree 5 p ≤ 18) :
    ¬ ElevenFiveC40B5SixK32K33Residual (blockSystem cfg) := by
  intro hresidual
  obtain ⟨Gamma, hD, hallAt⟩ :=
    elevenFive_c40_l11_b5_six_k32k33Residual_exists_doubleNeighbourCircle
      cfg hpoint hlocal hC hfive hbeta hresidual
  exact elevenFive_c40_l11_b5_six_doubleNeighbourCircle_impossible_of_pageCap
    cfg Gamma hpoint hcap hlocal hglobal hC hL hfive hbeta hD hallAt

/-- Collision-ready configuration-level exclusion of the complete
`B₅ = 6` branch. -/
theorem elevenFive_c40_l11_b5_six_impossible_of_configuration_without_langer
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
    (hfive : (blockSystem cfg).blockCount 5 = 6) : False := by
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
  have hresidual := elevenFive_c40_l11_b5_six_reduces_to_k32k33Residual
    cfg hpoint hlocal hglobal hCtotal hL hfive hbeta
  exact elevenFive_c40_l11_b5_six_k32k33Residual_impossible
    cfg hpoint hcap hlocal hglobal hCtotal hL hfive hbeta hresidual

/-- Compatibility wrapper retaining the historical global parameter list. -/
theorem elevenFive_c40_l11_b5_six_impossible_of_configuration
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
    (hfive : (blockSystem cfg).blockCount 5 = 6) : False :=
  elevenFive_c40_l11_b5_six_impossible_of_configuration_without_langer
    Mel EvenArr Cross Kelly U17 TenGeometry
      cfg hadm hpoint hcap hC hL hfive

end Erdos506.V1
