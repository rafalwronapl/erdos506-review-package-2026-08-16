import Erdos506.V1.ElevenFiveC40FinalCompleteDispatcher
import Mathlib.Algebra.BigOperators.Ring.Nat

/-!
# Parity extraction for C40 five-block defects

The five-block second moment is the sum of all pair-intersection
cardinalities.  Since distinct blocks have intersection cardinality at most
two, an odd second moment supplies an actual singleton pair.  This is the
shared finite entrance for the odd-defect C40 faces.
-/

namespace Erdos506.V1

open Erdos506.Block
open Erdos506.Block.BlockSystem
open Erdos506.Incidence
open Erdos506.V4
open scoped BigOperators

universe u

/-- An odd second moment of a size-five block family has a singleton pair.
This is a generic block-system lemma; no geometric witness is assumed. -/
theorem fiveBlock_singleton_of_odd_secondMoment
    {Point Block : Type*} [Fintype Point] [Fintype Block]
    [DecidableEq Point]
    (S : BlockSystem Point Block)
    (hodd : Odd (∑ p : Point, Nat.choose (S.blockDegree 5 p) 2)) :
    ∃ b ∈ S.blocksOfSize 5, ∃ c ∈ S.blocksOfSize 5,
      b ≠ c ∧ (S.support b ∩ S.support c).card = 1 := by
  classical
  let F := S.blocksOfSize 5
  have hmoment := S.binomial_degree_moment F 2
  have hoddPairs : Odd
      (∑ A ∈ F.powersetCard 2, (S.commonSupport A).card) := by
    rw [← hmoment]
    simpa [F, BlockSystem.blockDegree] using hodd
  have hoddFamily : Odd ((F.powersetCard 2).filter fun A =>
      Odd (S.commonSupport A).card).card :=
    (Finset.odd_sum_iff_odd_card_odd
      (s := F.powersetCard 2)
      (fun A => (S.commonSupport A).card)).mp hoddPairs
  obtain ⟨q, hq⟩ := hoddFamily
  have hpos : 0 < ((F.powersetCard 2).filter fun A =>
      Odd (S.commonSupport A).card).card := by
    omega
  obtain ⟨A, hA⟩ := Finset.card_pos.mp hpos
  have hApow : A ∈ F.powersetCard 2 := (Finset.mem_filter.mp hA).1
  have hAodd : Odd (S.commonSupport A).card :=
    (Finset.mem_filter.mp hA).2
  have hAsub : A ⊆ F := (Finset.mem_powersetCard.mp hApow).1
  obtain ⟨b, c, hbc, hAeq⟩ :=
    Finset.card_eq_two.mp (Finset.mem_powersetCard.mp hApow).2
  have hbF : b ∈ F := hAsub (by rw [hAeq]; simp)
  have hcF : c ∈ F := hAsub (by rw [hAeq]; simp)
  have hoddInter : Odd (S.support b ∩ S.support c).card := by
    rw [hAeq, S.commonSupport_pair] at hAodd
    exact hAodd
  have hinterLt : (S.support b ∩ S.support c).card < 3 :=
    S.distinct_block_inter_card_lt_three hbc
  obtain ⟨k, hk⟩ := hoddInter
  refine ⟨b, by simpa [F] using hbF, c, by simpa [F] using hcF,
    hbc, ?_⟩
  omega

/-- Configuration-level form of the odd-five-moment singleton extraction. -/
theorem elevenFive_fiveBlock_singleton_of_odd_secondMoment
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    (cfg : Configuration Point)
    (hodd : Odd (elevenFiveSecondMoment (blockSystem cfg))) :
    ∃ b ∈ (blockSystem cfg).blocksOfSize 5,
      ∃ c ∈ (blockSystem cfg).blocksOfSize 5,
        b ≠ c ∧ (geometricBlockSupport cfg b ∩
          geometricBlockSupport cfg c).card = 1 := by
  simpa [elevenFiveSecondMoment, blockSystem,
    geometricBlockSystem, geometricBlockSupport] using
    fiveBlock_singleton_of_odd_secondMoment (blockSystem cfg) hodd

/-- In the C40 `L = 11` local domain, an odd five-block second moment is
impossible: parity first produces a singleton pair, and the complete local
dispatcher eliminates its carrier. -/
theorem elevenFive_c40_l11_odd_secondMoment_impossible
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    (cfg : Configuration Point) (hcard : Fintype.card Point = 11)
    (hlocal : ∀ p : Point, ElevenFiveLocalRows (blockSystem cfg) p)
    (hC : (blockSystem cfg).totalCircleCount = 40)
    (hbeta : ∀ p : Point,
      (blockSystem cfg).blockDegree 3 p +
          (blockSystem cfg).blockDegree 4 p +
            (blockSystem cfg).blockDegree 5 p ≤ 18)
    (hodd : Odd (elevenFiveSecondMoment (blockSystem cfg))) : False := by
  obtain ⟨b, hb, c, hc, hne, hinter⟩ :=
    elevenFive_fiveBlock_singleton_of_odd_secondMoment cfg hodd
  obtain ⟨p, hpinter⟩ := Finset.card_eq_one.mp hinter
  have hpcommon : p ∈ geometricBlockSupport cfg b ∩
      geometricBlockSupport cfg c := by
    rw [hpinter]
    simp
  have hbp : p ∈ geometricBlockSupport cfg b :=
    (Finset.mem_inter.mp hpcommon).1
  have hcp : p ∈ geometricBlockSupport cfg c :=
    (Finset.mem_inter.mp hpcommon).2
  exact elevenFive_c40_l11_fiveBlock_singleton_impossible
    cfg hcard p (hlocal p) hC (hbeta p) hb hc hbp hcp hne hinter

/-- The completed singleton dispatcher forces even five-block pair moment
throughout the C40 `L = 11` local domain. -/
theorem elevenFive_c40_l11_secondMoment_even
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    (cfg : Configuration Point) (hcard : Fintype.card Point = 11)
    (hlocal : ∀ p : Point, ElevenFiveLocalRows (blockSystem cfg) p)
    (hC : (blockSystem cfg).totalCircleCount = 40)
    (hbeta : ∀ p : Point,
      (blockSystem cfg).blockDegree 3 p +
          (blockSystem cfg).blockDegree 4 p +
            (blockSystem cfg).blockDegree 5 p ≤ 18) :
    Even (elevenFiveSecondMoment (blockSystem cfg)) := by
  by_contra hnot
  exact elevenFive_c40_l11_odd_secondMoment_impossible
    cfg hcard hlocal hC hbeta (Nat.not_even_iff_odd.mp hnot)

/-- The odd `39` five-block moment of the first seven-block C40 face cannot
occur in the `L = 11` layer. -/
theorem elevenFive_c40_l11_secondMoment_ne_thirtyNine
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    (cfg : Configuration Point) (hcard : Fintype.card Point = 11)
    (hlocal : ∀ p : Point, ElevenFiveLocalRows (blockSystem cfg) p)
    (hC : (blockSystem cfg).totalCircleCount = 40)
    (hbeta : ∀ p : Point,
      (blockSystem cfg).blockDegree 3 p +
          (blockSystem cfg).blockDegree 4 p +
            (blockSystem cfg).blockDegree 5 p ≤ 18)
    (hmoment : elevenFiveSecondMoment (blockSystem cfg) = 39) : False := by
  apply elevenFive_c40_l11_odd_secondMoment_impossible
    cfg hcard hlocal hC hbeta
  rw [hmoment]
  norm_num

/-- The five-degree profile `4^2 3^9` has pair moment `39`.  This is the
odd-defect face in the seven-five C40 row. -/
theorem fiveBlock_secondMoment_eq_thirtyNine_of_four_three_profile
    {Point Block : Type*} [Fintype Point] [Fintype Block]
    [DecidableEq Point]
    (S : BlockSystem Point Block) (hcard : Fintype.card Point = 11)
    (hfour : ((Finset.univ : Finset Point).filter
      fun p => S.blockDegree 5 p = 4).card = 2)
    (hprofile : ∀ p : Point,
      S.blockDegree 5 p = 3 ∨ S.blockDegree 5 p = 4) :
    ∑ p : Point, Nat.choose (S.blockDegree 5 p) 2 = 39 := by
  classical
  have hpoint (p : Point) : Nat.choose (S.blockDegree 5 p) 2 =
      3 + 3 * (if S.blockDegree 5 p = 4 then 1 else 0) := by
    rcases hprofile p with hthree | hfour
    · simp [hthree]
    · norm_num [hfour, Nat.choose]
  have hfilter : (∑ p : Point,
      if S.blockDegree 5 p = 4 then 1 else 0) =
      ((Finset.univ : Finset Point).filter
        fun p => S.blockDegree 5 p = 4).card := by
    simp
  calc
    ∑ p : Point, Nat.choose (S.blockDegree 5 p) 2 =
        ∑ p : Point,
          (3 + 3 * (if S.blockDegree 5 p = 4 then 1 else 0)) := by
      apply Finset.sum_congr rfl
      intro p _hp
      exact hpoint p
    _ = 39 := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, hfilter]
      simp [hcard, hfour]

/-- The odd seven-five face `d_5=4^2 3^9` is impossible in the C40
`L = 11` layer.  Its concrete moment is `39`, so it yields the singleton
eliminated by the completed local dispatcher. -/
theorem elevenFive_c40_l11_four_three_fiveDegree_profile_impossible
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    (cfg : Configuration Point) (hcard : Fintype.card Point = 11)
    (hlocal : ∀ p : Point, ElevenFiveLocalRows (blockSystem cfg) p)
    (hC : (blockSystem cfg).totalCircleCount = 40)
    (hbeta : ∀ p : Point,
      (blockSystem cfg).blockDegree 3 p +
          (blockSystem cfg).blockDegree 4 p +
            (blockSystem cfg).blockDegree 5 p ≤ 18)
    (hfour : ((Finset.univ : Finset Point).filter
      fun p => (blockSystem cfg).blockDegree 5 p = 4).card = 2)
    (hprofile : ∀ p : Point,
      (blockSystem cfg).blockDegree 5 p = 3 ∨
        (blockSystem cfg).blockDegree 5 p = 4) : False := by
  apply elevenFive_c40_l11_secondMoment_ne_thirtyNine
    cfg hcard hlocal hC hbeta
  exact fiveBlock_secondMoment_eq_thirtyNine_of_four_three_profile
    (blockSystem cfg) hcard hfour hprofile

/-- A seven-block family with pair moment `40` and no singleton
intersections has an actual disjoint pair.  The missing two units from the
maximum pair moment `42` cannot be carried by anything else. -/
theorem fiveBlock_exists_disjoint_pair_of_secondMoment_eq_forty
    {Point Block : Type*} [Fintype Point] [Fintype Block]
    [DecidableEq Point]
    (S : BlockSystem Point Block) (hfive : S.blockCount 5 = 7)
    (hmoment : ∑ p : Point, Nat.choose (S.blockDegree 5 p) 2 = 40)
    (hnosingleton : ∀ b ∈ S.blocksOfSize 5, ∀ c ∈ S.blocksOfSize 5,
      b ≠ c → (S.support b ∩ S.support c).card ≠ 1) :
    ∃ b ∈ S.blocksOfSize 5, ∃ c ∈ S.blocksOfSize 5,
      b ≠ c ∧ (S.support b ∩ S.support c).card = 0 := by
  classical
  let F := S.blocksOfSize 5
  have hFcard : F.card = 7 := by
    simpa [F, BlockSystem.blockCount] using hfive
  have hpairTotal :
      (∑ A ∈ F.powersetCard 2, (S.commonSupport A).card) = 40 := by
    rw [← S.binomial_degree_moment F 2]
    simpa [F, BlockSystem.blockDegree] using hmoment
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
      (∑ A ∈ F.powersetCard 2, (S.commonSupport A).card) = 42 := by
    calc
      (∑ A ∈ F.powersetCard 2, (S.commonSupport A).card) =
          ∑ _A ∈ F.powersetCard 2, 2 := by
        apply Finset.sum_congr rfl
        intro A hA
        exact hterm A hA
      _ = 42 := by simp [hFcard, Nat.choose]
  omega

/-- In the C40 `L = 11` domain, the concrete seven-block moment-`40` face
therefore contains a disjoint pair of five-blocks. -/
theorem elevenFive_c40_l11_exists_disjoint_pair_of_secondMoment_eq_forty
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    (cfg : Configuration Point) (hcard : Fintype.card Point = 11)
    (hlocal : ∀ p : Point, ElevenFiveLocalRows (blockSystem cfg) p)
    (hC : (blockSystem cfg).totalCircleCount = 40)
    (hbeta : ∀ p : Point,
      (blockSystem cfg).blockDegree 3 p +
          (blockSystem cfg).blockDegree 4 p +
            (blockSystem cfg).blockDegree 5 p ≤ 18)
    (hfive : (blockSystem cfg).blockCount 5 = 7)
    (hmoment : elevenFiveSecondMoment (blockSystem cfg) = 40) :
    ∃ b ∈ (blockSystem cfg).blocksOfSize 5,
      ∃ c ∈ (blockSystem cfg).blocksOfSize 5,
        b ≠ c ∧ (geometricBlockSupport cfg b ∩
          geometricBlockSupport cfg c).card = 0 := by
  apply fiveBlock_exists_disjoint_pair_of_secondMoment_eq_forty
    (blockSystem cfg) hfive
  · simpa [elevenFiveSecondMoment] using hmoment
  · intro b hb c hc hne hsingle
    obtain ⟨p, hpinter⟩ := Finset.card_eq_one.mp hsingle
    have hp : p ∈ (blockSystem cfg).support b ∩
        (blockSystem cfg).support c := by
      rw [hpinter]
      simp
    have hpcommon : p ∈ geometricBlockSupport cfg b ∩
        geometricBlockSupport cfg c := by
      simpa [blockSystem, geometricBlockSystem,
        geometricBlockSupport] using hp
    exact elevenFive_c40_l11_fiveBlock_singleton_impossible
      cfg hcard p (hlocal p) hC (hbeta p) hb hc
        (Finset.mem_inter.mp hpcommon).1
        (Finset.mem_inter.mp hpcommon).2 hne hsingle

end Erdos506.V1
