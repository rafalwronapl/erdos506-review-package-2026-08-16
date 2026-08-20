import Erdos506.V1.ElevenFiveC40FinalSevenDefect

/-!
# The cardinal-three seven-defect profile

The remaining harmonic-card-three face in the C40 `L = 11, B5 = 7` row
has one unit of five-incidence slack.  This file records the resulting
literal `4^3 3^7 2` profile and its pair moment, before the final
disjoint-pair row argument.
-/

namespace Erdos506.V1

open Erdos506.Block
open Erdos506.Block.BlockSystem
open Erdos506.Incidence
open Erdos506.V4
open scoped BigOperators

universe u

/-- If the seven-five C40 row has three harmonic pivots, its five-degrees
are exactly `4^3 3^7 2`.  The proof is the equality case of the global
five-incidence bound, not a support enumeration. -/
theorem elevenFive_c40_l11_harmonic_three_fiveDegree_profile
    {Point Block : Type*} [Fintype Point] [Fintype Block]
    [DecidableEq Point]
    (S : BlockSystem Point Block) (hcard : Fintype.card Point = 11)
    (hglobal : ElevenFiveGlobalRows S) (hfive : S.blockCount 5 = 7)
    (hbound : ∀ p : Point, S.blockDegree 5 p <=
      3 + (if p ∈ elevenFiveHarmonicPivots S then 1 else 0))
    (hH : (elevenFiveHarmonicPivots S).card = 3) :
    ((Finset.univ : Finset Point).filter
      fun p => S.blockDegree 5 p = 4).card = 3 ∧
      ((Finset.univ : Finset Point).filter
        fun p => S.blockDegree 5 p = 2).card = 1 ∧
      ∀ p : Point, S.blockDegree 5 p = 2 ∨
        S.blockDegree 5 p = 3 ∨ S.blockDegree 5 p = 4 := by
  classical
  let H := elevenFiveHarmonicPivots S
  have hH' : H.card = 3 := by simpa [H] using hH
  have hboundH (p : Point) : S.blockDegree 5 p <=
      3 + (if p ∈ H then 1 else 0) := by
    simpa [H] using hbound p
  have hHdegree (p : Point) (hp : p ∈ H) : S.blockDegree 5 p = 4 := by
    have hp' : S.blockDegree 3 p = 9 ∧ S.blockDegree 4 p = 4 ∧
        S.blockDegree 5 p = 4 := by
      simpa [H, elevenFiveHarmonicPivots] using hp
    exact hp'.2.2
  have hdegreeFour_iff (p : Point) : S.blockDegree 5 p = 4 ↔ p ∈ H := by
    constructor
    · intro hd
      by_contra hp
      have hle := hboundH p
      simp [hp, hd] at hle
    · exact hHdegree p
  have hindicator :
      (∑ p : Point, if p ∈ H then 1 else 0) = H.card := by
    simp
  have hcapSum :
      (∑ p : Point, (3 + (if p ∈ H then 1 else 0))) = 36 := by
    rw [Finset.sum_add_distrib, hindicator]
    simp [hcard, hH']
  have hdegreeSum : (∑ p : Point, S.blockDegree 5 p) = 35 := by
    rw [hglobal.fiveIncidence, hfive]
  let slack : Point → Nat := fun p =>
    (3 + (if p ∈ H then 1 else 0)) - S.blockDegree 5 p
  have hslackDecomp (p : Point) : S.blockDegree 5 p + slack p =
      3 + (if p ∈ H then 1 else 0) := by
    dsimp [slack]
    exact Nat.add_sub_of_le (hboundH p)
  have hsumSlack : (∑ p : Point, slack p) = 1 := by
    have hsumAdd :
        (∑ p : Point, S.blockDegree 5 p) + (∑ p : Point, slack p) = 36 := by
      calc
        (∑ p : Point, S.blockDegree 5 p) + (∑ p : Point, slack p) =
            ∑ p : Point, (S.blockDegree 5 p + slack p) :=
          Finset.sum_add_distrib.symm
        _ = ∑ p : Point, (3 + (if p ∈ H then 1 else 0)) := by
          apply Finset.sum_congr rfl
          intro p _hp
          exact hslackDecomp p
        _ = 36 := hcapSum
    rw [hdegreeSum] at hsumAdd
    omega
  have hslackLe (p : Point) : slack p <= 1 := by
    have hle : slack p <= ∑ q : Point, slack q :=
      Finset.single_le_sum (fun q _hq => Nat.zero_le (slack q))
        (Finset.mem_univ p)
    rwa [hsumSlack] at hle
  have hprofile (p : Point) : S.blockDegree 5 p = 2 ∨
      S.blockDegree 5 p = 3 ∨ S.blockDegree 5 p = 4 := by
    by_cases hp : p ∈ H
    · exact Or.inr (Or.inr (hHdegree p hp))
    · have hle := hboundH p
      simp only [hp, if_false] at hle
      have hslack := hslackLe p
      simp only [slack, hp, if_false, Nat.add_zero] at hslack
      omega
  have hslackIndicator (p : Point) : slack p =
      if S.blockDegree 5 p = 2 then 1 else 0 := by
    by_cases hp : p ∈ H
    · have hd := hHdegree p hp
      simp [slack, hp, hd]
    · rcases hprofile p with htwo | hthree | hfour
      · simp [slack, hp, htwo]
      · simp [slack, hp, hthree]
      · have hle := hboundH p
        simp [hp, hfour] at hle
  have hlowIndicator :
      (∑ p : Point, if S.blockDegree 5 p = 2 then 1 else 0) =
        ((Finset.univ : Finset Point).filter
          fun p => S.blockDegree 5 p = 2).card := by
    simp
  have hlow : ((Finset.univ : Finset Point).filter
      fun p => S.blockDegree 5 p = 2).card = 1 := by
    calc
      ((Finset.univ : Finset Point).filter
          fun p => S.blockDegree 5 p = 2).card =
          ∑ p : Point, if S.blockDegree 5 p = 2 then 1 else 0 :=
        hlowIndicator.symm
      _ = ∑ p : Point, slack p := by
        apply Finset.sum_congr rfl
        intro p _hp
        exact (hslackIndicator p).symm
      _ = 1 := hsumSlack
  have hhighSet : ((Finset.univ : Finset Point).filter
      fun p => S.blockDegree 5 p = 4) = H := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact hdegreeFour_iff p
  refine ⟨?_, hlow, hprofile⟩
  rw [hhighSet, hH']

/-- The literal profile `4^3 3^7 2` has five-block pair moment `40`. -/
theorem fiveBlock_secondMoment_eq_forty_of_four_three_two_profile
    {Point Block : Type*} [Fintype Point] [Fintype Block]
    [DecidableEq Point]
    (S : BlockSystem Point Block) (hcard : Fintype.card Point = 11)
    (hfour : ((Finset.univ : Finset Point).filter
      fun p => S.blockDegree 5 p = 4).card = 3)
    (htwo : ((Finset.univ : Finset Point).filter
      fun p => S.blockDegree 5 p = 2).card = 1)
    (hprofile : ∀ p : Point, S.blockDegree 5 p = 2 ∨
      S.blockDegree 5 p = 3 ∨ S.blockDegree 5 p = 4) :
    ∑ p : Point, Nat.choose (S.blockDegree 5 p) 2 = 40 := by
  classical
  have hpoint (p : Point) : Nat.choose (S.blockDegree 5 p) 2 =
      1 + 2 * (if S.blockDegree 5 p = 2 then 0 else 1) +
        3 * (if S.blockDegree 5 p = 4 then 1 else 0) := by
    rcases hprofile p with htwo' | hthree | hfour'
    · norm_num [htwo', Nat.choose]
    · norm_num [hthree, Nat.choose]
    · norm_num [hfour', Nat.choose]
  have htwoIndicator :
      (∑ p : Point, if S.blockDegree 5 p = 2 then 1 else 0) =
        ((Finset.univ : Finset Point).filter
          fun p => S.blockDegree 5 p = 2).card := by
    simp
  have hfourIndicator :
      (∑ p : Point, if S.blockDegree 5 p = 4 then 1 else 0) =
        ((Finset.univ : Finset Point).filter
          fun p => S.blockDegree 5 p = 4).card := by
    simp
  have hnonTwoIndicator :
      (∑ p : Point, if S.blockDegree 5 p = 2 then 0 else 1) = 10 := by
    let T := (Finset.univ : Finset Point).filter
      fun p => ¬ S.blockDegree 5 p = 2
    have hTsum : (∑ p : Point,
        if S.blockDegree 5 p = 2 then 0 else 1) = T.card := by
      calc
        (∑ p : Point, if S.blockDegree 5 p = 2 then 0 else 1) =
            ∑ p : Point,
              if ¬ S.blockDegree 5 p = 2 then 1 else 0 := by
              apply Fintype.sum_congr
              intro p
              by_cases hp : S.blockDegree 5 p = 2 <;> simp [hp]
        _ = ((Finset.univ : Finset Point).filter
            fun p => ¬ S.blockDegree 5 p = 2).card := by
              rw [← Finset.sum_filter]
              simp
        _ = T.card := by rfl
    have hpartition := Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset Point))
      (p := fun p => S.blockDegree 5 p = 2)
    have hTcard : T.card = 10 := by
      rw [htwo] at hpartition
      have hpartition' : 1 + T.card = 11 := by
        simpa [T, hcard] using hpartition
      omega
    exact hTsum.trans hTcard
  calc
    (∑ p : Point, Nat.choose (S.blockDegree 5 p) 2) =
        ∑ p : Point, (1 +
          2 * (if S.blockDegree 5 p = 2 then 0 else 1) +
            3 * (if S.blockDegree 5 p = 4 then 1 else 0)) := by
      apply Finset.sum_congr rfl
      intro p _hp
      exact hpoint p
    _ = (∑ _p : Point, 1) +
        2 * (∑ p : Point, if S.blockDegree 5 p = 2 then 0 else 1) +
          3 * (∑ p : Point,
            if S.blockDegree 5 p = 4 then 1 else 0) := by
      simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
    _ = 40 := by
      rw [hnonTwoIndicator, hfourIndicator, hfour]
      simp [hcard]

/-- Configuration-level moment entry for the surviving cardinal-three
seven-defect face. -/
theorem elevenFive_c40_l11_sevenDefect_harmonic_three_secondMoment_eq_forty
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    (cfg : Configuration Point) (hcard : Fintype.card Point = 11)
    (hlocal : ∀ p : Point, ElevenFiveLocalRows (blockSystem cfg) p)
    (hglobal : ElevenFiveGlobalRows (blockSystem cfg))
    (hC : (blockSystem cfg).totalCircleCount = 40)
    (hfive : (blockSystem cfg).blockCount 5 = 7)
    (hbeta : ∀ p : Point,
      (blockSystem cfg).blockDegree 3 p +
          (blockSystem cfg).blockDegree 4 p +
            (blockSystem cfg).blockDegree 5 p <= 18)
    (hH : (elevenFiveHarmonicPivots (blockSystem cfg)).card = 3) :
    elevenFiveSecondMoment (blockSystem cfg) = 40 := by
  have hbound : ∀ p : Point, (blockSystem cfg).blockDegree 5 p <=
      3 + (if p ∈ elevenFiveHarmonicPivots (blockSystem cfg) then 1 else 0) := by
    intro p
    exact elevenFive_c40_l11_fiveDegree_le_three_add_harmonic
      (blockSystem cfg) p (hlocal p) hC (hbeta p)
  obtain ⟨hfour, htwo, hprofile⟩ :=
    elevenFive_c40_l11_harmonic_three_fiveDegree_profile
      (blockSystem cfg) hcard hglobal hfive hbound hH
  simpa [elevenFiveSecondMoment] using
    fiveBlock_secondMoment_eq_forty_of_four_three_two_profile
      (blockSystem cfg) hcard hfour htwo hprofile

/-- The surviving cardinal-three seven-defect profile therefore has an
actual disjoint pair of five-blocks.  This is the exact geometric entrance
for the final row-defect contradiction. -/
theorem elevenFive_c40_l11_sevenDefect_harmonic_three_exists_disjoint_pair
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    (cfg : Configuration Point) (hcard : Fintype.card Point = 11)
    (hlocal : ∀ p : Point, ElevenFiveLocalRows (blockSystem cfg) p)
    (hglobal : ElevenFiveGlobalRows (blockSystem cfg))
    (hC : (blockSystem cfg).totalCircleCount = 40)
    (hfive : (blockSystem cfg).blockCount 5 = 7)
    (hbeta : ∀ p : Point,
      (blockSystem cfg).blockDegree 3 p +
          (blockSystem cfg).blockDegree 4 p +
            (blockSystem cfg).blockDegree 5 p <= 18)
    (hH : (elevenFiveHarmonicPivots (blockSystem cfg)).card = 3) :
    ∃ b ∈ (blockSystem cfg).blocksOfSize 5,
      ∃ c ∈ (blockSystem cfg).blocksOfSize 5,
        b ≠ c ∧ (geometricBlockSupport cfg b ∩
          geometricBlockSupport cfg c).card = 0 := by
  have hmoment :=
    elevenFive_c40_l11_sevenDefect_harmonic_three_secondMoment_eq_forty
      cfg hcard hlocal hglobal hC hfive hbeta hH
  exact elevenFive_c40_l11_exists_disjoint_pair_of_secondMoment_eq_forty
    cfg hcard hlocal hC hbeta hfive hmoment

/-- In a seven-block family of pair moment `40`, one disjoint pair consumes
the entire defect `42 - 40`: every other distinct pair meets in two points.
This is a pure incidence-moment equality case. -/
theorem fiveBlock_inter_card_eq_two_of_secondMoment_forty_of_disjoint_pair
    {Point Block : Type*} [Fintype Point] [Fintype Block]
    [DecidableEq Point] [DecidableEq Block]
    (S : BlockSystem Point Block) (hfive : S.blockCount 5 = 7)
    (hmoment : ∑ p : Point, Nat.choose (S.blockDegree 5 p) 2 = 40)
    {f g : Block} (hf : f ∈ S.blocksOfSize 5)
    (hg : g ∈ S.blocksOfSize 5) (hfg : f ≠ g)
    (hdisjoint : (S.support f ∩ S.support g).card = 0) :
    ∀ b ∈ S.blocksOfSize 5, ∀ c ∈ S.blocksOfSize 5,
      b ≠ c → ({b, c} : Finset Block) ≠ ({f, g} : Finset Block) →
        (S.support b ∩ S.support c).card = 2 := by
  classical
  let F := S.blocksOfSize 5
  let Q := F.powersetCard 2
  let q : Finset Block → Nat := fun A => (S.commonSupport A).card
  have hFcard : F.card = 7 := by
    simpa [F, BlockSystem.blockCount] using hfive
  have hQcard : Q.card = 21 := by
    simp [Q, hFcard, Nat.choose]
  have hpairTotal :
      (∑ A ∈ Q, q A) = 40 := by
    change (∑ A ∈ F.powersetCard 2, (S.commonSupport A).card) = 40
    rw [← S.binomial_degree_moment F 2]
    simpa [F, BlockSystem.blockDegree] using hmoment
  have hspecial : ({f, g} : Finset Block) ∈ Q := by
    change ({f, g} : Finset Block) ∈ F.powersetCard 2
    refine Finset.mem_powersetCard.mpr ⟨?_, ?_⟩
    · intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact hf
      · exact hg
    · simp [hfg]
  have hzero : q ({f, g} : Finset Block) = 0 := by
    dsimp [q]
    rw [S.commonSupport_pair]
    exact hdisjoint
  have hrestCard : (Q.erase ({f, g} : Finset Block)).card = 20 := by
    rw [Finset.card_erase_of_mem hspecial, hQcard]
  have hsplit := Finset.sum_erase_add Q q hspecial
  have hrestSum :
      (∑ A ∈ Q.erase ({f, g} : Finset Block), q A) = 40 := by
    rw [hzero, hpairTotal] at hsplit
    omega
  have htermLe (A : Finset Block)
      (hA : A ∈ Q.erase ({f, g} : Finset Block)) : q A ≤ 2 := by
    dsimp [q]
    apply S.commonSupport_card_le_two
    have hAQ : A ∈ Q := Finset.mem_of_mem_erase hA
    have hAF : A ∈ F.powersetCard 2 := by
      simpa [Q] using hAQ
    exact (Finset.mem_powersetCard.mp hAF).2
  have hrestConst :
      (∑ _A ∈ Q.erase ({f, g} : Finset Block), 2) = 40 := by
    simp [hrestCard]
  have hall := (Finset.sum_eq_sum_iff_of_le htermLe).mp
    (hrestSum.trans hrestConst.symm)
  intro b hb c hc hbc hpairNe
  have hbcMem : ({b, c} : Finset Block) ∈ Q.erase ({f, g} : Finset Block) := by
    refine Finset.mem_erase.mpr ⟨hpairNe, ?_⟩
    change ({b, c} : Finset Block) ∈ F.powersetCard 2
    refine Finset.mem_powersetCard.mpr ⟨?_, ?_⟩
    · intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact hb
      · exact hc
    · simp [hbc]
  have hterm := hall {b, c} hbcMem
  simpa [q, S.commonSupport_pair] using hterm

/-- The two endpoints of the unique disjoint pair in the saturated
seven-block moment face each carry five-degree mass `15`. -/
theorem fiveBlock_support_degree_sum_eq_fifteen_of_secondMoment_forty_of_disjoint_pair
    {Point Block : Type*} [Fintype Point] [Fintype Block]
    [DecidableEq Point] [DecidableEq Block]
    (S : BlockSystem Point Block) (hfive : S.blockCount 5 = 7)
    (hmoment : ∑ p : Point, Nat.choose (S.blockDegree 5 p) 2 = 40)
    {f g : Block} (hf : f ∈ S.blocksOfSize 5)
    (hg : g ∈ S.blocksOfSize 5) (hfg : f ≠ g)
    (hdisjoint : (S.support f ∩ S.support g).card = 0) :
    (∑ p ∈ S.support f, S.blockDegree 5 p) = 15 ∧
      (∑ p ∈ S.support g, S.blockDegree 5 p) = 15 := by
  classical
  let F := S.blocksOfSize 5
  have hFcard : F.card = 7 := by
    simpa [F, BlockSystem.blockCount] using hfive
  have hother :=
    fiveBlock_inter_card_eq_two_of_secondMoment_forty_of_disjoint_pair
      S hfive hmoment hf hg hfg hdisjoint
  have hgf : g ≠ f := hfg.symm
  have hgfMem : g ∈ F.erase f := by
    exact Finset.mem_erase.mpr ⟨hgf, by simpa [F] using hg⟩
  let RF := (F.erase f).erase g
  have hRFcard : RF.card = 5 := by
    dsimp [RF]
    rw [Finset.card_erase_of_mem hgfMem,
      Finset.card_erase_of_mem (by simpa [F] using hf), hFcard]
  have hRFterm (b : Block) (hb : b ∈ RF) :
      (S.support f ∩ S.support b).card = 2 := by
    have hbEraseF : b ∈ F.erase f := Finset.mem_of_mem_erase hb
    have hbF : b ∈ S.blocksOfSize 5 := by
      simpa [F] using Finset.mem_of_mem_erase hbEraseF
    have hfb : f ≠ b := (Finset.mem_erase.mp hbEraseF).1.symm
    have hbg : b ≠ g := (Finset.mem_erase.mp hb).1
    have hpairNe : ({f, b} : Finset Block) ≠ {f, g} := by
      intro heq
      have hbin : b ∈ ({f, g} : Finset Block) := by
        rw [← heq]
        simp
      simp only [Finset.mem_insert, Finset.mem_singleton] at hbin
      rcases hbin with hbf | hbg'
      · exact hfb hbf.symm
      · exact hbg hbg'
    exact hother f hf b hbF hfb hpairNe
  have hRFsum :
      (∑ b ∈ RF, (S.support f ∩ S.support b).card) = 10 := by
    calc
      (∑ b ∈ RF, (S.support f ∩ S.support b).card) =
          ∑ _b ∈ RF, 2 := by
        apply Finset.sum_congr rfl
        intro b hb
        exact hRFterm b hb
      _ = 10 := by norm_num [hRFcard]
  have hselfF : (S.support f ∩ S.support f).card = 5 := by
    simp [S.mem_blocksOfSize.mp hf]
  have hsplitF := Finset.sum_erase_add F
    (fun b => (S.support f ∩ S.support b).card) (by simpa [F] using hf)
  have hsplitFg := Finset.sum_erase_add (F.erase f)
    (fun b => (S.support f ∩ S.support b).card) hgfMem
  have hFtotal :
      (∑ b ∈ F, (S.support f ∩ S.support b).card) = 15 := by
    calc
      (∑ b ∈ F, (S.support f ∩ S.support b).card) =
          (∑ b ∈ F.erase f, (S.support f ∩ S.support b).card) +
            (S.support f ∩ S.support f).card := hsplitF.symm
      _ = ((∑ b ∈ RF, (S.support f ∩ S.support b).card) +
            (S.support f ∩ S.support g).card) +
            (S.support f ∩ S.support f).card := by
        dsimp [RF]
        rw [hsplitFg]
      _ = 15 := by rw [hRFsum, hdisjoint, hselfF]
  have hfubiniF := S.sum_degreeIn_over F (S.support f)
  change (∑ p ∈ S.support f, S.blockDegree 5 p) =
      ∑ b ∈ F, (S.support f ∩ S.support b).card at hfubiniF
  have hrowF : (∑ p ∈ S.support f, S.blockDegree 5 p) = 15 :=
    hfubiniF.trans hFtotal
  have hfgMem : f ∈ F.erase g := by
    exact Finset.mem_erase.mpr ⟨hfg, by simpa [F] using hf⟩
  let RG := (F.erase g).erase f
  have hRGcard : RG.card = 5 := by
    dsimp [RG]
    rw [Finset.card_erase_of_mem hfgMem,
      Finset.card_erase_of_mem (by simpa [F] using hg), hFcard]
  have hRGterm (b : Block) (hb : b ∈ RG) :
      (S.support g ∩ S.support b).card = 2 := by
    have hbEraseG : b ∈ F.erase g := Finset.mem_of_mem_erase hb
    have hbF : b ∈ S.blocksOfSize 5 := by
      simpa [F] using Finset.mem_of_mem_erase hbEraseG
    have hgb : g ≠ b := (Finset.mem_erase.mp hbEraseG).1.symm
    have hbf : b ≠ f := (Finset.mem_erase.mp hb).1
    have hpairNe : ({g, b} : Finset Block) ≠ {f, g} := by
      intro heq
      have hbin : b ∈ ({f, g} : Finset Block) := by
        rw [← heq]
        simp
      simp only [Finset.mem_insert, Finset.mem_singleton] at hbin
      rcases hbin with hbf' | hbg'
      · exact hbf hbf'
      · exact hgb hbg'.symm
    exact hother g hg b hbF hgb hpairNe
  have hRGsum :
      (∑ b ∈ RG, (S.support g ∩ S.support b).card) = 10 := by
    calc
      (∑ b ∈ RG, (S.support g ∩ S.support b).card) =
          ∑ _b ∈ RG, 2 := by
        apply Finset.sum_congr rfl
        intro b hb
        exact hRGterm b hb
      _ = 10 := by norm_num [hRGcard]
  have hdisjointG : (S.support g ∩ S.support f).card = 0 := by
    simpa [Finset.inter_comm] using hdisjoint
  have hselfG : (S.support g ∩ S.support g).card = 5 := by
    simp [S.mem_blocksOfSize.mp hg]
  have hsplitG := Finset.sum_erase_add F
    (fun b => (S.support g ∩ S.support b).card) (by simpa [F] using hg)
  have hsplitGf := Finset.sum_erase_add (F.erase g)
    (fun b => (S.support g ∩ S.support b).card) hfgMem
  have hGtotal :
      (∑ b ∈ F, (S.support g ∩ S.support b).card) = 15 := by
    calc
      (∑ b ∈ F, (S.support g ∩ S.support b).card) =
          (∑ b ∈ F.erase g, (S.support g ∩ S.support b).card) +
            (S.support g ∩ S.support g).card := hsplitG.symm
      _ = ((∑ b ∈ RG, (S.support g ∩ S.support b).card) +
            (S.support g ∩ S.support f).card) +
            (S.support g ∩ S.support g).card := by
        dsimp [RG]
        rw [hsplitGf]
      _ = 15 := by rw [hRGsum, hdisjointG, hselfG]
  have hfubiniG := S.sum_degreeIn_over F (S.support g)
  change (∑ p ∈ S.support g, S.blockDegree 5 p) =
      ∑ b ∈ F, (S.support g ∩ S.support b).card at hfubiniG
  exact ⟨hrowF, hfubiniG.trans hGtotal⟩

end Erdos506.V1
