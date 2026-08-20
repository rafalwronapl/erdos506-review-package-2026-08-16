import Erdos506.V1.ElevenFiveC40FinalTwoDefectMoment

/-!
# The common two-defect entrance for the C40 small faces

This file isolates the part of the `B₅ = 5,6` small-face argument which is
purely finite.  If the five-block pair moment is two below its all-double
maximum and singleton intersections are absent, there is one unordered
disjoint pair.  Every other pair is double, and on eleven points the unique
point outside the two disjoint five-blocks has five-degree `m - 2`.
-/

namespace Erdos506.V1

open Erdos506.Block
open Erdos506.Block.BlockSystem
open scoped BigOperators

universe u v

/-- A two-unit defect from the all-double pair moment, together with the
absence of singleton intersections, produces a disjoint pair. -/
theorem fiveBlock_exists_disjoint_pair_of_pairMoment_defect_two
    {Point : Type u} {Block : Type v} [Fintype Point] [Fintype Block]
    [DecidableEq Point] [DecidableEq Block]
    (S : BlockSystem Point Block) (m : ℕ) (hm : 2 ≤ m)
    (hfive : S.blockCount 5 = m)
    (hmoment : elevenFiveSecondMoment S = 2 * Nat.choose m 2 - 2)
    (hnosingleton : ∀ b ∈ S.blocksOfSize 5, ∀ c ∈ S.blocksOfSize 5,
      b ≠ c → (S.support b ∩ S.support c).card ≠ 1) :
    ∃ b ∈ S.blocksOfSize 5, ∃ c ∈ S.blocksOfSize 5,
      b ≠ c ∧ (S.support b ∩ S.support c).card = 0 := by
  classical
  let F := S.blocksOfSize 5
  have hFcard : F.card = m := by
    simpa [F, BlockSystem.blockCount] using hfive
  have hpairTotal :
      (∑ A ∈ F.powersetCard 2, (S.commonSupport A).card) =
        2 * Nat.choose F.card 2 - 2 := by
    rw [← S.binomial_degree_moment F 2]
    simpa [F, BlockSystem.blockDegree, elevenFiveSecondMoment, hFcard]
      using hmoment
  by_contra hdisjoint
  have hterm (A : Finset Block) (hA : A ∈ F.powersetCard 2) :
      (S.commonSupport A).card = 2 := by
    obtain ⟨b, c, hbc, hAeq⟩ :=
      Finset.card_eq_two.mp (Finset.mem_powersetCard.mp hA).2
    have hAsub := (Finset.mem_powersetCard.mp hA).1
    have hb : b ∈ S.blocksOfSize 5 := by
      simpa [F] using hAsub (by rw [hAeq]; simp)
    have hc : c ∈ S.blocksOfSize 5 := by
      simpa [F] using hAsub (by rw [hAeq]; simp)
    have hzero : (S.support b ∩ S.support c).card ≠ 0 := by
      intro hzero
      apply hdisjoint
      exact ⟨b, hb, c, hc, hbc, hzero⟩
    have hone : (S.support b ∩ S.support c).card ≠ 1 :=
      hnosingleton b hb c hc hbc
    have hlt : (S.support b ∩ S.support c).card < 3 :=
      S.distinct_block_inter_card_lt_three hbc
    rw [hAeq, S.commonSupport_pair]
    omega
  have hmax :
      (∑ A ∈ F.powersetCard 2, (S.commonSupport A).card) =
        2 * Nat.choose F.card 2 := by
    calc
      (∑ A ∈ F.powersetCard 2, (S.commonSupport A).card) =
          ∑ _A ∈ F.powersetCard 2, 2 := by
        apply Finset.sum_congr rfl
        intro A hA
        exact hterm A hA
      _ = 2 * Nat.choose F.card 2 := by
        simp [Nat.mul_comm]
  have hchoosePos : 0 < Nat.choose F.card 2 := by
    apply Nat.choose_pos
    rw [hFcard]
    exact hm
  have htwoUnits : 2 ≤ 2 * Nat.choose F.card 2 := by omega
  rw [hmax] at hpairTotal
  omega

/-- At either endpoint of a disjoint pair which exhausts a two-unit moment
defect, the five-degree row has mass `5 + 2(m-2) = 2m+1`. -/
theorem fiveBlock_support_degree_sum_eq_two_mul_add_one_of_pairMoment_defect_two
    {Point : Type u} {Block : Type v} [Fintype Point] [Fintype Block]
    [DecidableEq Point] [DecidableEq Block]
    (S : BlockSystem Point Block) (m : ℕ) (hm : 2 ≤ m)
    (hfive : S.blockCount 5 = m)
    (hmoment : elevenFiveSecondMoment S = 2 * Nat.choose m 2 - 2)
    {f g : Block} (hf : f ∈ S.blocksOfSize 5)
    (hg : g ∈ S.blocksOfSize 5) (hfg : f ≠ g)
    (hdisjoint : (S.support f ∩ S.support g).card = 0) :
    (∑ p ∈ S.support f, S.blockDegree 5 p) = 2 * m + 1 := by
  classical
  let F := S.blocksOfSize 5
  have hFcard : F.card = m := by
    simpa [F, BlockSystem.blockCount] using hfive
  have hfF : f ∈ F := by simpa [F] using hf
  have hgF : g ∈ F := by simpa [F] using hg
  have hmoment' :
      (∑ p : Point, Nat.choose (S.degreeIn F p) 2) =
        2 * Nat.choose F.card 2 - 2 := by
    simpa [F, BlockSystem.blockDegree, elevenFiveSecondMoment, hFcard]
      using hmoment
  have hother :=
    blockFamily_inter_card_eq_two_of_pairMoment_defect_two_of_disjoint_pair
      S F hmoment' hfF hgF hfg hdisjoint
  have hgf : g ≠ f := hfg.symm
  have hgfMem : g ∈ F.erase f := Finset.mem_erase.mpr ⟨hgf, hgF⟩
  let R := (F.erase f).erase g
  have hRcard : R.card = m - 2 := by
    dsimp [R]
    rw [Finset.card_erase_of_mem hgfMem,
      Finset.card_erase_of_mem hfF, hFcard]
    omega
  have hRterm (b : Block) (hb : b ∈ R) :
      (S.support f ∩ S.support b).card = 2 := by
    have hbEraseF : b ∈ F.erase f := Finset.mem_of_mem_erase hb
    have hbF : b ∈ F := Finset.mem_of_mem_erase hbEraseF
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
    exact hother f hfF b hbF hfb hpairNe
  have hRsum :
      (∑ b ∈ R, (S.support f ∩ S.support b).card) = 2 * (m - 2) := by
    calc
      (∑ b ∈ R, (S.support f ∩ S.support b).card) =
          ∑ _b ∈ R, 2 := by
        apply Finset.sum_congr rfl
        intro b hb
        exact hRterm b hb
      _ = 2 * (m - 2) := by simp [hRcard, Nat.mul_comm]
  have hself : (S.support f ∩ S.support f).card = 5 := by
    simp [S.mem_blocksOfSize.mp hf]
  have hsplitF := Finset.sum_erase_add F
    (fun b => (S.support f ∩ S.support b).card) hfF
  have hsplitFg := Finset.sum_erase_add (F.erase f)
    (fun b => (S.support f ∩ S.support b).card) hgfMem
  have hFtotal :
      (∑ b ∈ F, (S.support f ∩ S.support b).card) = 2 * m + 1 := by
    calc
      (∑ b ∈ F, (S.support f ∩ S.support b).card) =
          (∑ b ∈ F.erase f, (S.support f ∩ S.support b).card) +
            (S.support f ∩ S.support f).card := hsplitF.symm
      _ = ((∑ b ∈ R, (S.support f ∩ S.support b).card) +
            (S.support f ∩ S.support g).card) +
            (S.support f ∩ S.support f).card := by
        dsimp [R]
        rw [hsplitFg]
      _ = 2 * m + 1 := by
        rw [hRsum, hdisjoint, hself]
        omega
  have hfubini := S.sum_degreeIn_over F (S.support f)
  change (∑ p ∈ S.support f, S.blockDegree 5 p) =
    ∑ b ∈ F, (S.support f ∩ S.support b).card at hfubini
  exact hfubini.trans hFtotal

/-- The full finite two-defect package on eleven points: there is a unique
unordered disjoint pair, all other distinct pairs are double, and the unique
point outside its ten-point union has five-degree `m - 2`. -/
theorem fiveBlock_unique_disjoint_pair_outsider_of_pairMoment_defect_two
    {Point : Type u} {Block : Type v} [Fintype Point] [Fintype Block]
    [DecidableEq Point] [DecidableEq Block]
    (S : BlockSystem Point Block) (hcard : Fintype.card Point = 11)
    (m : ℕ) (hm : 2 ≤ m) (hfive : S.blockCount 5 = m)
    (hmoment : elevenFiveSecondMoment S = 2 * Nat.choose m 2 - 2)
    (hnosingleton : ∀ b ∈ S.blocksOfSize 5, ∀ c ∈ S.blocksOfSize 5,
      b ≠ c → (S.support b ∩ S.support c).card ≠ 1) :
    ∃ f ∈ S.blocksOfSize 5, ∃ g ∈ S.blocksOfSize 5,
      f ≠ g ∧ (S.support f ∩ S.support g).card = 0 ∧
      (∀ b ∈ S.blocksOfSize 5, ∀ c ∈ S.blocksOfSize 5,
        b ≠ c → ({b, c} : Finset Block) ≠ {f, g} →
          (S.support b ∩ S.support c).card = 2) ∧
      (∀ b ∈ S.blocksOfSize 5, ∀ c ∈ S.blocksOfSize 5,
        b ≠ c → (S.support b ∩ S.support c).card = 0 →
          ({b, c} : Finset Block) = {f, g}) ∧
      ∃! q : Point,
        q ∉ S.support f ∪ S.support g ∧ S.blockDegree 5 q = m - 2 := by
  classical
  obtain ⟨f, hf, g, hg, hfg, hdisjoint⟩ :=
    fiveBlock_exists_disjoint_pair_of_pairMoment_defect_two
      S m hm hfive hmoment hnosingleton
  let F := S.blocksOfSize 5
  have hFcard : F.card = m := by
    simpa [F, BlockSystem.blockCount] using hfive
  have hmoment' :
      (∑ p : Point, Nat.choose (S.degreeIn F p) 2) =
        2 * Nat.choose F.card 2 - 2 := by
    simpa [F, BlockSystem.blockDegree, elevenFiveSecondMoment, hFcard]
      using hmoment
  have hother :=
    blockFamily_inter_card_eq_two_of_pairMoment_defect_two_of_disjoint_pair
      S F hmoment' (by simpa [F] using hf) (by simpa [F] using hg)
        hfg hdisjoint
  have hallDouble (b : Block) (hb : b ∈ S.blocksOfSize 5)
      (c : Block) (hc : c ∈ S.blocksOfSize 5) (hbc : b ≠ c)
      (hpairNe : ({b, c} : Finset Block) ≠ {f, g}) :
      (S.support b ∩ S.support c).card = 2 :=
    hother b (by simpa [F] using hb) c (by simpa [F] using hc)
      hbc hpairNe
  have hunique (b : Block) (hb : b ∈ S.blocksOfSize 5)
      (c : Block) (hc : c ∈ S.blocksOfSize 5) (hbc : b ≠ c)
      (hbcZero : (S.support b ∩ S.support c).card = 0) :
      ({b, c} : Finset Block) = {f, g} := by
    by_contra hpairNe
    have htwo := hother b (by simpa [F] using hb)
      c (by simpa [F] using hc) hbc hpairNe
    omega
  have hrowF :=
    fiveBlock_support_degree_sum_eq_two_mul_add_one_of_pairMoment_defect_two
      S m hm hfive hmoment hf hg hfg hdisjoint
  have hdisjointG : (S.support g ∩ S.support f).card = 0 := by
    simpa [Finset.inter_comm] using hdisjoint
  have hrowG :=
    fiveBlock_support_degree_sum_eq_two_mul_add_one_of_pairMoment_defect_two
      S m hm hfive hmoment hg hf hfg.symm hdisjointG
  have hFGdisjoint : Disjoint (S.support f) (S.support g) := by
    rw [Finset.disjoint_left]
    intro p hpf hpg
    have hp : p ∈ S.support f ∩ S.support g :=
      Finset.mem_inter.mpr ⟨hpf, hpg⟩
    have hempty : S.support f ∩ S.support g = ∅ :=
      Finset.card_eq_zero.mp hdisjoint
    simpa [hempty] using hp
  let V := S.support f ∪ S.support g
  have hVcard : V.card = 10 := by
    dsimp [V]
    rw [Finset.card_union_of_disjoint hFGdisjoint,
      S.mem_blocksOfSize.mp hf, S.mem_blocksOfSize.mp hg]
  have hcomplCard : ((Finset.univ : Finset Point) \ V).card = 1 := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ V),
      Finset.card_univ, hcard, hVcard]
  obtain ⟨q, hqEq⟩ := Finset.card_eq_one.mp hcomplCard
  have hqCompl : q ∈ (Finset.univ : Finset Point) \ V := by
    rw [hqEq]
    simp
  have hqOutsideV : q ∉ V := (Finset.mem_sdiff.mp hqCompl).2
  have hVsum : (∑ p ∈ V, S.blockDegree 5 p) = 4 * m + 2 := by
    dsimp [V]
    rw [Finset.sum_union hFGdisjoint, hrowF, hrowG]
    omega
  have htotal := S.block_incidence 5
  rw [hfive] at htotal
  have hsplit :
      (∑ p ∈ (Finset.univ : Finset Point) \ V, S.blockDegree 5 p) +
          (∑ p ∈ V, S.blockDegree 5 p) =
        ∑ p : Point, S.blockDegree 5 p := by
    exact Finset.sum_sdiff (Finset.subset_univ V)
  have hqDegree : S.blockDegree 5 q = m - 2 := by
    rw [hqEq] at hsplit
    simp only [Finset.sum_singleton] at hsplit
    rw [hVsum, htotal] at hsplit
    omega
  refine ⟨f, hf, g, hg, hfg, hdisjoint, hallDouble, hunique, q, ?_, ?_⟩
  · exact ⟨by simpa [V] using hqOutsideV, hqDegree⟩
  · intro r hr
    have hrCompl : r ∈ (Finset.univ : Finset Point) \ V :=
      Finset.mem_sdiff.mpr
        ⟨Finset.mem_univ r, by simpa [V] using hr.1⟩
    rw [hqEq] at hrCompl
    simpa using hrCompl

/-- Numeric small-face specialization: five blocks have moment `18`, and
the unique point outside the disjoint pair has five-degree three. -/
theorem fiveBlock_unique_disjoint_pair_outsider_degree_three_of_five
    {Point : Type u} {Block : Type v} [Fintype Point] [Fintype Block]
    [DecidableEq Point] [DecidableEq Block]
    (S : BlockSystem Point Block) (hcard : Fintype.card Point = 11)
    (hfive : S.blockCount 5 = 5) (hmoment : elevenFiveSecondMoment S = 18)
    (hnosingleton : ∀ b ∈ S.blocksOfSize 5, ∀ c ∈ S.blocksOfSize 5,
      b ≠ c → (S.support b ∩ S.support c).card ≠ 1) :
    ∃ f ∈ S.blocksOfSize 5, ∃ g ∈ S.blocksOfSize 5,
      f ≠ g ∧ (S.support f ∩ S.support g).card = 0 ∧
      (∀ b ∈ S.blocksOfSize 5, ∀ c ∈ S.blocksOfSize 5,
        b ≠ c → ({b, c} : Finset Block) ≠ {f, g} →
          (S.support b ∩ S.support c).card = 2) ∧
      (∀ b ∈ S.blocksOfSize 5, ∀ c ∈ S.blocksOfSize 5,
        b ≠ c → (S.support b ∩ S.support c).card = 0 →
          ({b, c} : Finset Block) = {f, g}) ∧
      ∃! q : Point,
        q ∉ S.support f ∪ S.support g ∧ S.blockDegree 5 q = 3 := by
  simpa [Nat.choose] using
    (fiveBlock_unique_disjoint_pair_outsider_of_pairMoment_defect_two
      S hcard 5 (by norm_num) hfive hmoment hnosingleton)

/-- Numeric small-face specialization: six blocks have moment `28`, and
the unique point outside the disjoint pair has five-degree four. -/
theorem fiveBlock_unique_disjoint_pair_outsider_degree_four_of_six
    {Point : Type u} {Block : Type v} [Fintype Point] [Fintype Block]
    [DecidableEq Point] [DecidableEq Block]
    (S : BlockSystem Point Block) (hcard : Fintype.card Point = 11)
    (hfive : S.blockCount 5 = 6) (hmoment : elevenFiveSecondMoment S = 28)
    (hnosingleton : ∀ b ∈ S.blocksOfSize 5, ∀ c ∈ S.blocksOfSize 5,
      b ≠ c → (S.support b ∩ S.support c).card ≠ 1) :
    ∃ f ∈ S.blocksOfSize 5, ∃ g ∈ S.blocksOfSize 5,
      f ≠ g ∧ (S.support f ∩ S.support g).card = 0 ∧
      (∀ b ∈ S.blocksOfSize 5, ∀ c ∈ S.blocksOfSize 5,
        b ≠ c → ({b, c} : Finset Block) ≠ {f, g} →
          (S.support b ∩ S.support c).card = 2) ∧
      (∀ b ∈ S.blocksOfSize 5, ∀ c ∈ S.blocksOfSize 5,
        b ≠ c → (S.support b ∩ S.support c).card = 0 →
          ({b, c} : Finset Block) = {f, g}) ∧
      ∃! q : Point,
        q ∉ S.support f ∪ S.support g ∧ S.blockDegree 5 q = 4 := by
  simpa [Nat.choose] using
    (fiveBlock_unique_disjoint_pair_outsider_of_pairMoment_defect_two
      S hcard 6 (by norm_num) hfive hmoment hnosingleton)

end Erdos506.V1
