import Erdos506.V1.ElevenFiveC40FinalFourteenEightProfile
import Erdos506.V1.ElevenFiveC40FinalTwoDefectMoment
import Erdos506.V1.ElevenFiveC40FinalFourStarBridge
import Erdos506.V1.ElevenFiveC40FinalK31ActualGridTail

/-!
# The unconditional C40 `L = 14, B₅ = 8` endpoint

The beta cap turns the last eight-five profile into the literal degree
profile `4^7 3^4`.  Its pair moment is two below the all-double maximum.
The complete singleton exclusion therefore yields one disjoint pair; the
two saturated support rows then contradict the seven degree-four pivots.
-/

namespace Erdos506.V1

open Erdos506.Block
open Erdos506.Block.BlockSystem
open Erdos506.Incidence
open Erdos506.V3
open Erdos506.V4
open scoped BigOperators

universe u v

/-- The literal profile `4^7 3^4` has five-block pair moment `54`. -/
theorem fiveBlock_secondMoment_eq_fiftyFour_of_four_three_profile
    {Point Block : Type*} [Fintype Point] [Fintype Block]
    [DecidableEq Point]
    (S : BlockSystem Point Block) (hcard : Fintype.card Point = 11)
    (hfour : ((Finset.univ : Finset Point).filter
      fun p => S.blockDegree 5 p = 4).card = 7)
    (hprofile : ∀ p : Point, S.blockDegree 5 p = 3 ∨
      S.blockDegree 5 p = 4) :
    ∑ p : Point, Nat.choose (S.blockDegree 5 p) 2 = 54 := by
  classical
  have hpoint (p : Point) : Nat.choose (S.blockDegree 5 p) 2 =
      3 + 3 * (if S.blockDegree 5 p = 4 then 1 else 0) := by
    rcases hprofile p with hthree | hfour'
    · norm_num [hthree, Nat.choose]
    · norm_num [hfour', Nat.choose]
  have hindicator :
      (∑ p : Point, if S.blockDegree 5 p = 4 then 1 else 0) =
        ((Finset.univ : Finset Point).filter
          fun p => S.blockDegree 5 p = 4).card := by
    simp
  calc
    (∑ p : Point, Nat.choose (S.blockDegree 5 p) 2) =
        ∑ p : Point, (3 + 3 *
          (if S.blockDegree 5 p = 4 then 1 else 0)) := by
      apply Finset.sum_congr rfl
      intro p _hp
      exact hpoint p
    _ = (∑ _p : Point, 3) + 3 *
        (∑ p : Point, if S.blockDegree 5 p = 4 then 1 else 0) := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum]
    _ = 54 := by
      rw [hindicator, hfour]
      simp [hcard]

/-- In the eight-five face, every singleton five-block intersection is
already ruled out by one of the completed local K3/FourStar endpoints. -/
theorem elevenFive_c40_l14_eightDefect_fiveBlock_inter_card_ne_one
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    (cfg : Configuration Point) (hcard : Fintype.card Point = 11)
    (hlocal : ∀ p : Point, ElevenFiveLocalRows (blockSystem cfg) p)
    (hglobal : ElevenFiveGlobalRows (blockSystem cfg))
    (hC : (blockSystem cfg).totalCircleCount = 40)
    (hL : elevenFiveLineTotal (blockSystem cfg) = 14)
    (hfive : (blockSystem cfg).blockCount 5 = 8)
    (hbeta : ∀ p : Point,
      (blockSystem cfg).blockDegree 3 p +
          (blockSystem cfg).blockDegree 4 p +
            (blockSystem cfg).blockDegree 5 p ≤ 21)
    (hharmonic : 4 *
      (elevenFiveHarmonicPivots (blockSystem cfg)).card ≤
        2 * (blockSystem cfg).blockCount 5)
    {b c : GeometricBlock cfg}
    (hb : b ∈ (blockSystem cfg).blocksOfSize 5)
    (hc : c ∈ (blockSystem cfg).blocksOfSize 5)
    (hne : b ≠ c) :
    (geometricBlockSupport cfg b ∩ geometricBlockSupport cfg c).card ≠ 1 := by
  intro hinter
  obtain ⟨p, hpinter⟩ := Finset.card_eq_one.mp hinter
  have hpMem : p ∈ geometricBlockSupport cfg b ∩
      geometricBlockSupport cfg c := by
    rw [hpinter]
    simp
  obtain ⟨_hfour, _hthree, hprofile, hcarrier⟩ :=
    elevenFive_c40_l14_eightDefect_fiveDegree_profile
      (blockSystem cfg) hcard hlocal hglobal hC hL hfive hbeta hharmonic
  have hbp : p ∈ geometricBlockSupport cfg b :=
    (Finset.mem_inter.mp hpMem).1
  have hcp : p ∈ geometricBlockSupport cfg c :=
    (Finset.mem_inter.mp hpMem).2
  rcases hprofile p with hthree | hfour
  · rcases hcarrier p hthree with h6 | h9
    · exact elevenFive_threeFive_six_singleton_impossible
        cfg hcard p (hlocal p) h6 hthree hb hc hbp hcp hne hinter
    · exact elevenFive_threeFive_nine_singleton_impossible
        cfg hcard p (hlocal p) h9 hthree hb hc hbp hcp hne hinter
  · exact elevenFive_degreeFourPivot_fiveBlock_inter_card_ne_one
      cfg hcard p hfour hb hc hbp hcp hne hinter

/-- A family of eight five-blocks with pair moment `54` and no singleton
intersections has an actual disjoint pair. -/
theorem fiveBlock_exists_disjoint_pair_of_secondMoment_fiftyFour
    {Point Block : Type*} [Fintype Point] [Fintype Block]
    [DecidableEq Point]
    (S : BlockSystem Point Block) (hfive : S.blockCount 5 = 8)
    (hmoment : ∑ p : Point, Nat.choose (S.blockDegree 5 p) 2 = 54)
    (hnosingleton : ∀ b ∈ S.blocksOfSize 5, ∀ c ∈ S.blocksOfSize 5,
      b ≠ c → (S.support b ∩ S.support c).card ≠ 1) :
    ∃ b ∈ S.blocksOfSize 5, ∃ c ∈ S.blocksOfSize 5,
      b ≠ c ∧ (S.support b ∩ S.support c).card = 0 := by
  classical
  let F := S.blocksOfSize 5
  have hFcard : F.card = 8 := by
    simpa [F, BlockSystem.blockCount] using hfive
  have hpairTotal :
      (∑ A ∈ F.powersetCard 2, (S.commonSupport A).card) = 54 := by
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
      (∑ A ∈ F.powersetCard 2, (S.commonSupport A).card) = 56 := by
    calc
      (∑ A ∈ F.powersetCard 2, (S.commonSupport A).card) =
          ∑ _A ∈ F.powersetCard 2, 2 := by
        apply Finset.sum_congr rfl
        intro A hA
        exact hterm A hA
      _ = 56 := by simp [hFcard, Nat.choose]
  omega

/-- Once the `54`-moment defect supplies a disjoint pair, every other pair
is double and either endpoint has five-degree row sum `17`. -/
theorem fiveBlock_support_degree_sum_eq_seventeen_of_secondMoment_fiftyFour_of_disjoint_pair
    {Point Block : Type*} [Fintype Point] [Fintype Block]
    [DecidableEq Point] [DecidableEq Block]
    (S : BlockSystem Point Block) (hfive : S.blockCount 5 = 8)
    (hmoment : ∑ p : Point, Nat.choose (S.blockDegree 5 p) 2 = 54)
    {f g : Block} (hf : f ∈ S.blocksOfSize 5)
    (hg : g ∈ S.blocksOfSize 5) (hfg : f ≠ g)
    (hdisjoint : (S.support f ∩ S.support g).card = 0) :
    (∑ p ∈ S.support f, S.blockDegree 5 p) = 17 := by
  classical
  let F := S.blocksOfSize 5
  have hFcard : F.card = 8 := by
    simpa [F, BlockSystem.blockCount] using hfive
  have hmoment' :
      (∑ p : Point, Nat.choose (S.degreeIn F p) 2) =
        2 * Nat.choose F.card 2 - 2 := by
    calc
      (∑ p : Point, Nat.choose (S.degreeIn F p) 2) = 54 := by
        simpa [F, BlockSystem.blockDegree] using hmoment
      _ = 2 * Nat.choose F.card 2 - 2 := by
        rw [hFcard]
        norm_num [Nat.choose]
  have hother :=
    blockFamily_inter_card_eq_two_of_pairMoment_defect_two_of_disjoint_pair
      S F hmoment' (by simpa [F] using hf) (by simpa [F] using hg)
        hfg hdisjoint
  have hgf : g ≠ f := hfg.symm
  have hgfMem : g ∈ F.erase f := by
    exact Finset.mem_erase.mpr ⟨hgf, by simpa [F] using hg⟩
  let RF := (F.erase f).erase g
  have hRFcard : RF.card = 6 := by
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
    exact hother f (by simpa [F] using hf) b hbF hfb hpairNe
  have hRFsum :
      (∑ b ∈ RF, (S.support f ∩ S.support b).card) = 12 := by
    calc
      (∑ b ∈ RF, (S.support f ∩ S.support b).card) =
          ∑ _b ∈ RF, 2 := by
        apply Finset.sum_congr rfl
        intro b hb
        exact hRFterm b hb
      _ = 12 := by norm_num [hRFcard]
  have hselfF : (S.support f ∩ S.support f).card = 5 := by
    simp [S.mem_blocksOfSize.mp hf]
  have hsplitF := Finset.sum_erase_add F
    (fun b => (S.support f ∩ S.support b).card) (by simpa [F] using hf)
  have hsplitFg := Finset.sum_erase_add (F.erase f)
    (fun b => (S.support f ∩ S.support b).card) hgfMem
  have hFtotal :
      (∑ b ∈ F, (S.support f ∩ S.support b).card) = 17 := by
    calc
      (∑ b ∈ F, (S.support f ∩ S.support b).card) =
          (∑ b ∈ F.erase f, (S.support f ∩ S.support b).card) +
            (S.support f ∩ S.support f).card := hsplitF.symm
      _ = ((∑ b ∈ RF, (S.support f ∩ S.support b).card) +
            (S.support f ∩ S.support g).card) +
            (S.support f ∩ S.support f).card := by
          dsimp [RF]
          rw [hsplitFg]
      _ = 17 := by rw [hRFsum, hdisjoint, hselfF]
  have hfubiniF := S.sum_degreeIn_over F (S.support f)
  change (∑ p ∈ S.support f, S.blockDegree 5 p) =
      ∑ b ∈ F, (S.support f ∩ S.support b).card at hfubiniF
  exact hfubiniF.trans hFtotal

/-- The finite profile `4^7 3^4` is incompatible with the absence of
singleton intersections.  The pair-moment defect gives a disjoint pair;
the saturated rows put only four high pivots in its ten-point union, while
at most one of the seven high pivots can lie outside that union. -/
theorem fiveBlock_four_three_profile_impossible_of_no_singleton
    {Point Block : Type*} [Fintype Point] [Fintype Block]
    [DecidableEq Point] [DecidableEq Block]
    (S : BlockSystem Point Block) (hcard : Fintype.card Point = 11)
    (hfive : S.blockCount 5 = 8)
    (hfour : ((Finset.univ : Finset Point).filter
      fun p => S.blockDegree 5 p = 4).card = 7)
    (hprofile : ∀ p : Point, S.blockDegree 5 p = 3 ∨
      S.blockDegree 5 p = 4)
    (hnosingleton : ∀ b ∈ S.blocksOfSize 5, ∀ c ∈ S.blocksOfSize 5,
      b ≠ c → (S.support b ∩ S.support c).card ≠ 1) : False := by
  classical
  let H := (Finset.univ : Finset Point).filter
    fun p => S.blockDegree 5 p = 4
  have hHcard : H.card = 7 := by simpa [H] using hfour
  have hmoment := fiveBlock_secondMoment_eq_fiftyFour_of_four_three_profile
    S hcard hfour hprofile
  obtain ⟨f, hf, g, hg, hfg, hdisjoint⟩ :=
    fiveBlock_exists_disjoint_pair_of_secondMoment_fiftyFour
      S hfive hmoment hnosingleton
  have hrowF :=
    fiveBlock_support_degree_sum_eq_seventeen_of_secondMoment_fiftyFour_of_disjoint_pair
      S hfive hmoment hf hg hfg hdisjoint
  have hdisjointG : (S.support g ∩ S.support f).card = 0 := by
    simpa [Finset.inter_comm] using hdisjoint
  have hrowG :=
    fiveBlock_support_degree_sum_eq_seventeen_of_secondMoment_fiftyFour_of_disjoint_pair
      S hfive hmoment hg hf hfg.symm hdisjointG
  have hpoint (p : Point) : S.blockDegree 5 p =
      3 + (if p ∈ H then 1 else 0) := by
    rcases hprofile p with hthree | hfour'
    · have hpH : p ∉ H := by simp [H, hthree]
      simp [hpH, hthree]
    · have hpH : p ∈ H := by simp [H, hfour']
      simp [hpH, hfour']
  have hindicator (D T : Finset Point) :
      (∑ p ∈ D, if p ∈ T then 1 else 0) = (D ∩ T).card := by
    rw [← Finset.sum_filter]
    have hfilter : D.filter (fun p => p ∈ T) = D ∩ T := by
      ext p
      simp only [Finset.mem_filter, Finset.mem_inter]
    rw [hfilter]
    simp
  have hsupportBalance (b : Block) (hb : b ∈ S.blocksOfSize 5) :
      (∑ p ∈ S.support b, S.blockDegree 5 p) =
        15 + (S.support b ∩ H).card := by
    calc
      (∑ p ∈ S.support b, S.blockDegree 5 p) =
          ∑ p ∈ S.support b,
            (3 + (if p ∈ H then 1 else 0)) := by
          apply Finset.sum_congr rfl
          intro p _hp
          exact hpoint p
      _ = (∑ _p ∈ S.support b, 3) +
          ∑ p ∈ S.support b, if p ∈ H then 1 else 0 := by
          rw [Finset.sum_add_distrib]
      _ = 15 + (S.support b ∩ H).card := by
          rw [hindicator]
          simp [S.mem_blocksOfSize.mp hb]
  have hFhigh : (S.support f ∩ H).card = 2 := by
    have hbalance := hsupportBalance f hf
    rw [hrowF] at hbalance
    omega
  have hGhigh : (S.support g ∩ H).card = 2 := by
    have hbalance := hsupportBalance g hg
    rw [hrowG] at hbalance
    omega
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
  have hHoutsideSub : H \ V ⊆ (Finset.univ : Finset Point) \ V := by
    intro p hp
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ p,
      (Finset.mem_sdiff.mp hp).2⟩
  have hHoutside : (H \ V).card ≤ 1 := by
    have hle := Finset.card_le_card hHoutsideSub
    rwa [hcomplCard] at hle
  have hHsplit := Finset.card_inter_add_card_sdiff H V
  have hHinside : 6 ≤ (H ∩ V).card := by
    rw [hHcard] at hHsplit
    omega
  have hHdisjoint : Disjoint (S.support f ∩ H) (S.support g ∩ H) := by
    rw [Finset.disjoint_left]
    intro p hpf hpg
    exact Finset.disjoint_left.mp hFGdisjoint
      (Finset.mem_inter.mp hpf).1 (Finset.mem_inter.mp hpg).1
  have hHunion : H ∩ V =
      (S.support f ∩ H) ∪ (S.support g ∩ H) := by
    dsimp [V]
    ext p
    constructor
    · intro hp
      rcases Finset.mem_inter.mp hp with ⟨hpH, hpFG⟩
      rcases Finset.mem_union.mp hpFG with hpf | hpg
      · exact Finset.mem_union.mpr (Or.inl
          (Finset.mem_inter.mpr ⟨hpf, hpH⟩))
      · exact Finset.mem_union.mpr (Or.inr
          (Finset.mem_inter.mpr ⟨hpg, hpH⟩))
    · intro hp
      rcases Finset.mem_union.mp hp with hpf | hpg
      · rcases Finset.mem_inter.mp hpf with ⟨hpf, hpH⟩
        exact Finset.mem_inter.mpr ⟨hpH,
          Finset.mem_union.mpr (Or.inl hpf)⟩
      · rcases Finset.mem_inter.mp hpg with ⟨hpg, hpH⟩
        exact Finset.mem_inter.mpr ⟨hpH,
          Finset.mem_union.mpr (Or.inr hpg)⟩
  have hHinsideEq : (H ∩ V).card =
      (S.support f ∩ H).card + (S.support g ∩ H).card := by
    rw [hHunion, Finset.card_union_of_disjoint hHdisjoint]
  rw [hHinsideEq, hFhigh, hGhigh] at hHinside
  omega

/-- The actual `C = 40, L = 14, B₅ = 8` row is impossible once the
pivot-inversion beta cap and the already-proved harmonic cap are available. -/
theorem elevenFive_c40_l14_eightDefect_impossible_of_beta_cap
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    (cfg : Configuration Point) (hcard : Fintype.card Point = 11)
    (hlocal : ∀ p : Point, ElevenFiveLocalRows (blockSystem cfg) p)
    (hglobal : ElevenFiveGlobalRows (blockSystem cfg))
    (hC : (blockSystem cfg).totalCircleCount = 40)
    (hL : elevenFiveLineTotal (blockSystem cfg) = 14)
    (hfive : (blockSystem cfg).blockCount 5 = 8)
    (hbeta : ∀ p : Point,
      (blockSystem cfg).blockDegree 3 p +
          (blockSystem cfg).blockDegree 4 p +
            (blockSystem cfg).blockDegree 5 p ≤ 21)
    (hharmonic : 4 *
      (elevenFiveHarmonicPivots (blockSystem cfg)).card ≤
        2 * (blockSystem cfg).blockCount 5) : False := by
  classical
  obtain ⟨hfour, _hthree, hprofile, _hcarrier⟩ :=
    elevenFive_c40_l14_eightDefect_fiveDegree_profile
      (blockSystem cfg) hcard hlocal hglobal hC hL hfive hbeta hharmonic
  apply fiveBlock_four_three_profile_impossible_of_no_singleton
    (blockSystem cfg) hcard hfive hfour hprofile
  intro b hb c hc hbc hsingle
  have hsingleGeo : (geometricBlockSupport cfg b ∩
      geometricBlockSupport cfg c).card = 1 := by
    simpa [blockSystem, geometricBlockSystem,
      geometricBlockSupport] using hsingle
  exact elevenFive_c40_l14_eightDefect_fiveBlock_inter_card_ne_one
    cfg hcard hlocal hglobal hC hL hfive hbeta hharmonic hb hc hbc hsingleGeo

/-- The former public `C = 40, L = 14, B₅ = 8` collision field is
unconditional: the ordinary rows, pivot-inversion beta cap, and the
established harmonic cap already contradict its numerical hypotheses. -/
theorem elevenFive_c40_l14_eightDefectCollision_unconditional_without_langer
    (Mel : RealPlaneMelchiorPrinciple.{u})
    (EvenArr : RealPlaneEvenArrangementPrinciple.{u})
    (Cross : RealPlaneRadicalAxisCrossBlockPrinciple.{u})
    (Kelly : RealPlaneKellyMoserPrinciple.{u})
    (U17 : RealPlaneSixCircleU17Principle.{u})
    (TenGeometry : RealPlaneTenFiveGeometry.{u})
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    (cfg : Configuration Point) (hadm : Admissible cfg)
    (hcard : Fintype.card Point = 11)
    (hcap : BlockSizeCap (blockSystem cfg) 5)
    (hC : Erdos506.V4.circleCount cfg = 40)
    (hL : elevenFiveLineTotal (blockSystem cfg) = 14)
    (hfive : (blockSystem cfg).blockCount 5 = 8) :
    ElevenFiveTripleCollision (blockSystem cfg) := by
  have hCtotal : (blockSystem cfg).totalCircleCount = 40 := by
    rw [totalCircleCount_eq_card_determinedCircle,
      ← Erdos506.V3.circleCount_eq_card_determinedCircle]
    exact hC
  have hCupper : (blockSystem cfg).totalCircleCount ≤ 40 := by
    omega
  have hlocal : ∀ p : Point,
      ElevenFiveLocalRows (blockSystem cfg) p := fun p =>
    elevenFiveLocalRows_of_configuration_without_langer
      Mel EvenArr Cross Kelly U17 TenGeometry
        cfg hadm hcard hcap hCupper p
  have hglobal : ElevenFiveGlobalRows (blockSystem cfg) :=
    elevenFiveGlobalRows_of_configuration
      Mel cfg hadm hcard hcap hlocal
  have hbeta := elevenFive_c40_l14_beta_cap
    Mel EvenArr Cross Kelly U17 TenGeometry
      cfg hadm hcard hcap hglobal hCtotal hL
  have hharmonic : 4 *
      (elevenFiveHarmonicPivots (blockSystem cfg)).card ≤
        2 * (blockSystem cfg).blockCount 5 := by
    apply elevenFive_harmonicIncidenceCap_of_normalCircleTraceTransport_and_fiveLineCap
      cfg hcard
    · intro p hp
      exact elevenFive944_normalCircleTraceTransport cfg hcard p hp
    · exact elevenFive944Pivots_fiveLine_cap cfg hcard
  exact False.elim
    (elevenFive_c40_l14_eightDefect_impossible_of_beta_cap
      cfg hcard hlocal hglobal hCtotal hL hfive hbeta hharmonic)

/-- Compatibility wrapper retaining the historical global parameter list. -/
theorem elevenFive_c40_l14_eightDefectCollision_unconditional
    (Mel : RealPlaneMelchiorPrinciple.{u})
    (_Langer : RealPlaneLangerPrinciple.{u})
    (EvenArr : RealPlaneEvenArrangementPrinciple.{u})
    (Cross : RealPlaneRadicalAxisCrossBlockPrinciple.{u})
    (Kelly : RealPlaneKellyMoserPrinciple.{u})
    (U17 : RealPlaneSixCircleU17Principle.{u})
    (TenGeometry : RealPlaneTenFiveGeometry.{u})
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    (cfg : Configuration Point) (hadm : Admissible cfg)
    (hcard : Fintype.card Point = 11)
    (hcap : BlockSizeCap (blockSystem cfg) 5)
    (hC : Erdos506.V4.circleCount cfg = 40)
    (hL : elevenFiveLineTotal (blockSystem cfg) = 14)
    (hfive : (blockSystem cfg).blockCount 5 = 8) :
    ElevenFiveTripleCollision (blockSystem cfg) :=
  elevenFive_c40_l14_eightDefectCollision_unconditional_without_langer
    Mel EvenArr Cross Kelly U17 TenGeometry
      cfg hadm hcard hcap hC hL hfive

end Erdos506.V1
