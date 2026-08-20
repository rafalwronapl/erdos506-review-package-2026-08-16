import Erdos506.V1.ElevenFiveC40FourteenSevenPageCapFinish

/-!
# The disjoint branch of the C40/L14/B5=7 moment-39 face

For seven five-blocks the all-double pair moment is `42`.  At moment `39`,
an actual disjoint pair spends two of the three missing units.  The remaining
unit is therefore one unique singleton pair; every other pair is double.
This lossless finite reducer is combined below with the existing page-cap
mass bounds.
-/

namespace Erdos506.V1

open Erdos506.Block
open Erdos506.Block.BlockSystem
open Erdos506.Incidence
open Erdos506.V3
open Erdos506.V4
open scoped BigOperators

universe u v

/-- A disjoint pair in a seven-five-block moment-39 family leaves exactly
one singleton pair, and all remaining distinct pairs are double. -/
theorem fiveBlock_m39_disjoint_pair_has_unique_singleton_pair
    {Point : Type u} {Block : Type v} [Fintype Point] [Fintype Block]
    [DecidableEq Point] [DecidableEq Block]
    (S : BlockSystem Point Block) (hfive : S.blockCount 5 = 7)
    (hmoment : elevenFiveSecondMoment S = 39)
    {f g : Block} (hf : f ∈ S.blocksOfSize 5)
    (hg : g ∈ S.blocksOfSize 5) (hfg : f ≠ g)
    (hdisjoint : (S.support f ∩ S.support g).card = 0) :
    ∃ A ∈ (S.blocksOfSize 5).powersetCard 2,
      A ≠ ({f, g} : Finset Block) ∧
      (S.commonSupport A).card = 1 ∧
      ∀ b ∈ S.blocksOfSize 5, ∀ c ∈ S.blocksOfSize 5,
        b ≠ c → ({b, c} : Finset Block) ≠ ({f, g} : Finset Block) →
          ({b, c} : Finset Block) ≠ A →
            (S.support b ∩ S.support c).card = 2 := by
  classical
  let F := S.blocksOfSize 5
  let Q := F.powersetCard 2
  let q : Finset Block → ℕ := fun A => (S.commonSupport A).card
  let d : Finset Block → ℕ := fun A => 2 - q A
  let RQ := Q.erase ({f, g} : Finset Block)
  have hFcard : F.card = 7 := by
    simpa [F, BlockSystem.blockCount] using hfive
  have hQcard : Q.card = 21 := by
    simp [Q, hFcard, Nat.choose]
  have hpairTotal : (∑ A ∈ Q, q A) = 39 := by
    change (∑ A ∈ F.powersetCard 2, (S.commonSupport A).card) = 39
    rw [← S.binomial_degree_moment F 2]
    simpa [F, BlockSystem.blockDegree, elevenFiveSecondMoment] using hmoment
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
  have hRQcard : RQ.card = 20 := by
    dsimp [RQ]
    rw [Finset.card_erase_of_mem hspecial, hQcard]
  have hsplit := Finset.sum_erase_add Q q hspecial
  have hRQsum : (∑ A ∈ RQ, q A) = 39 := by
    dsimp [RQ]
    rw [hzero, hpairTotal] at hsplit
    omega
  have htermLe (A : Finset Block) (hA : A ∈ RQ) : q A ≤ 2 := by
    dsimp [q]
    apply S.commonSupport_card_le_two
    have hAQ : A ∈ Q := Finset.mem_of_mem_erase (by simpa [RQ] using hA)
    have hAF : A ∈ F.powersetCard 2 := by simpa [Q] using hAQ
    exact (Finset.mem_powersetCard.mp hAF).2
  have hdecomp (A : Finset Block) (hA : A ∈ RQ) : q A + d A = 2 := by
    dsimp [d]
    exact Nat.add_sub_of_le (htermLe A hA)
  have hdefSum : (∑ A ∈ RQ, d A) = 1 := by
    have hadd :
        (∑ A ∈ RQ, q A) + (∑ A ∈ RQ, d A) = 40 := by
      calc
        (∑ A ∈ RQ, q A) + (∑ A ∈ RQ, d A) =
            ∑ A ∈ RQ, (q A + d A) := Finset.sum_add_distrib.symm
        _ = ∑ _A ∈ RQ, 2 := by
          apply Finset.sum_congr rfl
          intro A hA
          exact hdecomp A hA
        _ = 40 := by simp [hRQcard]
    rw [hRQsum] at hadd
    omega
  have hdLeOne (A : Finset Block) (hA : A ∈ RQ) : d A ≤ 1 := by
    have hle : d A ≤ ∑ B ∈ RQ, d B :=
      Finset.single_le_sum (fun B _hB => Nat.zero_le (d B)) hA
    rwa [hdefSum] at hle
  have hexists : ∃ A ∈ RQ, d A = 1 := by
    by_contra hnot
    push_neg at hnot
    have hzeroD (A : Finset Block) (hA : A ∈ RQ) : d A = 0 := by
      have hle := hdLeOne A hA
      have hne := hnot A hA
      omega
    have hsumZero : (∑ A ∈ RQ, d A) = 0 := by
      apply Finset.sum_eq_zero
      intro A hA
      exact hzeroD A hA
    omega
  obtain ⟨A, hARQ, hdA⟩ := hexists
  have hAerase := Finset.mem_erase.mp (by simpa [RQ] using hARQ)
  have hAone : q A = 1 := by
    have hle := htermLe A hARQ
    dsimp [d] at hdA
    omega
  refine ⟨A, by simpa [Q, F] using hAerase.2, hAerase.1, ?_, ?_⟩
  · simpa [q] using hAone
  · intro b hb c hc hbc hpairFG hpairA
    let B : Finset Block := {b, c}
    have hBQ : B ∈ Q := by
      change ({b, c} : Finset Block) ∈ F.powersetCard 2
      refine Finset.mem_powersetCard.mpr ⟨?_, ?_⟩
      · intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl
        · simpa [F] using hb
        · simpa [F] using hc
      · simp [hbc]
    have hBRQ : B ∈ RQ := by
      apply Finset.mem_erase.mpr
      exact ⟨by simpa [B] using hpairFG, by simpa [RQ, Q] using hBQ⟩
    have hBErase : B ∈ RQ.erase A := by
      exact Finset.mem_erase.mpr ⟨by simpa [B] using hpairA, hBRQ⟩
    have hsumErase := Finset.sum_erase_add RQ d hARQ
    have hrestZero : (∑ C ∈ RQ.erase A, d C) = 0 := by
      rw [hdefSum, hdA] at hsumErase
      omega
    have hdBLe : d B ≤ ∑ C ∈ RQ.erase A, d C :=
      Finset.single_le_sum (fun C _hC => Nat.zero_le (d C)) hBErase
    rw [hrestZero] at hdBLe
    have hdB : d B = 0 := by omega
    have hqLe := htermLe B hBRQ
    dsimp [d] at hdB
    have hqB : q B = 2 := by omega
    simpa [B, q, S.commonSupport_pair] using hqB

/-- The M39 branch with an actual disjoint pair is impossible.  Neither
endpoint can contain a degree-four pivot: its five other neighbours supply
at most ten intersection incidences, while one degree-four pivot would make
its support degree sum at least sixteen.  The two global degree-four pivots
would therefore both have to lie in the one-point complement of the two
disjoint five-supports. -/
theorem elevenFive_c40_l14_b5_seven_secondMoment_thirtyNine_disjoint_impossible
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    (cfg : Configuration Point)
    (hpoint : Fintype.card Point = 11)
    (hcap : BlockSizeCap (blockSystem cfg) 5)
    (hlocal : ∀ p : Point, ElevenFiveLocalRows (blockSystem cfg) p)
    (hglobal : ElevenFiveGlobalRows (blockSystem cfg))
    (hC : (blockSystem cfg).totalCircleCount = 40)
    (hL : elevenFiveLineTotal (blockSystem cfg) = 14)
    (hfive : (blockSystem cfg).blockCount 5 = 7)
    (hmoment : elevenFiveSecondMoment (blockSystem cfg) = 39)
    {f g : GeometricBlock cfg}
    (hf : f ∈ (blockSystem cfg).blocksOfSize 5)
    (hg : g ∈ (blockSystem cfg).blocksOfSize 5)
    (hfg : f ≠ g)
    (hdisjoint : ((blockSystem cfg).support f ∩
      (blockSystem cfg).support g).card = 0) : False := by
  classical
  let S := blockSystem cfg
  let F := S.blocksOfSize 5
  have hfF : f ∈ F := by simpa [F, S] using hf
  have hgF : g ∈ F := by simpa [F, S] using hg
  have hFcard : F.card = 7 := by
    simpa [F, S, BlockSystem.blockCount] using hfive
  have hFGdisjoint : Disjoint (S.support f) (S.support g) := by
    rw [Finset.disjoint_left]
    intro p hpf hpg
    have hp : p ∈ S.support f ∩ S.support g :=
      Finset.mem_inter.mpr ⟨hpf, hpg⟩
    have hempty : S.support f ∩ S.support g = ∅ :=
      Finset.card_eq_zero.mp (by simpa [S] using hdisjoint)
    simpa [hempty] using hp
  let V := S.support f ∪ S.support g
  have hVcard : V.card = 10 := by
    dsimp [V]
    rw [Finset.card_union_of_disjoint hFGdisjoint,
      S.mem_blocksOfSize.mp (by simpa [S] using hf),
      S.mem_blocksOfSize.mp (by simpa [S] using hg)]
  have hcomplCard : ((Finset.univ : Finset Point) \ V).card = 1 := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ V),
      Finset.card_univ, hpoint, hVcard]
  obtain ⟨hfour, _hthree, hprofile⟩ :=
    elevenFive_c40_l14_b5_seven_secondMoment_thirtyNine_profile
      S hpoint (by simpa [S] using hlocal) (by simpa [S] using hglobal)
        (by simpa [S] using hfive) (by simpa [S] using hmoment)
  have hnoHighEndpoint (b c : GeometricBlock cfg)
      (hb : b ∈ S.blocksOfSize 5) (hc : c ∈ S.blocksOfSize 5)
      (hbc : b ≠ c) (hzero : (S.support b ∩ S.support c).card = 0) :
      ∀ p ∈ S.support b, S.blockDegree 5 p ≠ 4 := by
    have hbF : b ∈ F := by simpa [F] using hb
    have hcF : c ∈ F := by simpa [F] using hc
    have hcErase : c ∈ F.erase b :=
      Finset.mem_erase.mpr ⟨hbc.symm, hcF⟩
    let T := (F.erase b).erase c
    have hTcard : T.card = 5 := by
      dsimp [T]
      rw [Finset.card_erase_of_mem hcErase,
        Finset.card_erase_of_mem hbF, hFcard]
    have hTbound :
        (∑ x ∈ T, (S.support b ∩ S.support x).card) ≤ 10 := by
      calc
        (∑ x ∈ T, (S.support b ∩ S.support x).card) ≤
            ∑ _x ∈ T, 2 := by
          apply Finset.sum_le_sum
          intro x hx
          have hxErase : x ∈ F.erase b := Finset.mem_of_mem_erase hx
          have hbx : b ≠ x := (Finset.mem_erase.mp hxErase).1.symm
          have hlt := S.distinct_block_inter_card_lt_three hbx
          omega
        _ = 10 := by simp [hTcard]
    have hsplitC := Finset.sum_erase_add (F.erase b)
      (fun x => (S.support b ∩ S.support x).card) hcErase
    have hotherLe :
        (∑ x ∈ F.erase b, (S.support b ∩ S.support x).card) ≤ 10 := by
      have hsplitC' :
          (∑ x ∈ T, (S.support b ∩ S.support x).card) +
              (S.support b ∩ S.support c).card =
            ∑ x ∈ F.erase b,
              (S.support b ∩ S.support x).card := by
        simpa [T] using hsplitC
      rw [hzero] at hsplitC'
      omega
    have hfubini := S.sum_degreeIn_over F (S.support b)
    change (∑ p ∈ S.support b, S.blockDegree 5 p) =
      ∑ x ∈ F, (S.support b ∩ S.support x).card at hfubini
    have hsplitB := Finset.sum_erase_add F
      (fun x => (S.support b ∩ S.support x).card) hbF
    have hbcard : (S.support b).card = 5 := S.mem_blocksOfSize.mp hb
    have hself : (S.support b ∩ S.support b).card = 5 := by
      simp [hbcard]
    have hrightLe :
        (∑ x ∈ F, (S.support b ∩ S.support x).card) ≤ 15 := by
      change
        (∑ x ∈ F.erase b, (S.support b ∩ S.support x).card) +
            (S.support b ∩ S.support b).card =
          ∑ x ∈ F, (S.support b ∩ S.support x).card at hsplitB
      rw [hself] at hsplitB
      omega
    intro p hp hp4
    have hpointLower (x : Point) (hx : x ∈ S.support b) :
        3 + (if x = p then 1 else 0) ≤ S.blockDegree 5 x := by
      by_cases hxp : x = p
      · subst x
        simp [hp4]
      · rcases hprofile x with hx3 | hx4
        · simp [hxp, hx3]
        · simp [hxp, hx4]
    have hleftLower :
        16 ≤ ∑ x ∈ S.support b, S.blockDegree 5 x := by
      have hsum :
          (∑ x ∈ S.support b, (3 + (if x = p then 1 else 0))) ≤
            ∑ x ∈ S.support b, S.blockDegree 5 x :=
        Finset.sum_le_sum (fun x hx => hpointLower x hx)
      have hleft :
          (∑ x ∈ S.support b,
            (3 + (if x = p then 1 else 0))) = 16 := by
        rw [Finset.sum_add_distrib]
        simp [hbcard, hp]
      omega
    omega
  have hnoHighF : ∀ p ∈ S.support f, S.blockDegree 5 p ≠ 4 :=
    hnoHighEndpoint f g (by simpa [S] using hf) (by simpa [S] using hg)
      hfg (by simpa [S] using hdisjoint)
  have hnoHighG : ∀ p ∈ S.support g, S.blockDegree 5 p ≠ 4 :=
    hnoHighEndpoint g f (by simpa [S] using hg) (by simpa [S] using hf)
      hfg.symm (by simpa [S, Finset.inter_comm] using hdisjoint)
  let H := (Finset.univ : Finset Point).filter fun p =>
    S.blockDegree 5 p = 4
  have hHcard : H.card = 2 := by simpa [H] using hfour
  have hHsub : H ⊆ (Finset.univ : Finset Point) \ V := by
    intro p hpH
    have hp4 : S.blockDegree 5 p = 4 := (Finset.mem_filter.mp hpH).2
    apply Finset.mem_sdiff.mpr
    refine ⟨Finset.mem_univ p, ?_⟩
    intro hpV
    have hpUnion : p ∈ S.support f ∪ S.support g := by
      simpa [V] using hpV
    rcases Finset.mem_union.mp hpUnion with hpf | hpg
    · exact hnoHighF p hpf hp4
    · exact hnoHighG p hpg hp4
  have hcardLe := Finset.card_le_card hHsub
  rw [hHcard, hcomplCard] at hcardLe
  omega

end Erdos506.V1
