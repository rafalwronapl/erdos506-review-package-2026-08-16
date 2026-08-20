import Erdos506.V1.ElevenFiveC40SmallProfileFinish
import Erdos506.V1.ElevenFiveC40FinalBetaCapCount
import Erdos506.V1.ElevenFiveFourStarRealization

/-!
# The C40/L11 six-block small-face front

The exact profile theorem leaves five numerical faces when `B₅ = 6`.
Two of them are already excluded by the finite block calculus.  In the
moment-28 face with no degree-four point, the two-defect outsider theorem
produces a degree-four point.  In the all-double face with one degree-four
point and two degree-one points, a block through a degree-one point has
degree mass at most fourteen, whereas all-double incidence forces fifteen.

The remaining three faces are precisely the branches whose manuscript
closures use the triangle-pendant part of K3.2, and in one branch the
harmonic uniqueness part of K3.3.  They are packaged below as one residual.
-/

namespace Erdos506.V1

open Erdos506.Block
open Erdos506.Block.BlockSystem
open Erdos506.Incidence
open Erdos506.V3
open Erdos506.V4
open scoped BigOperators

universe u v

/-- The exact three K3.2/K3.3 faces left after the purely finite `B₅ = 6`
dispatch. -/
def ElevenFiveC40B5SixK32K33Residual
    {Point : Type u} {Block : Type v} [Fintype Point] [Fintype Block]
    [DecidableEq Point]
    (S : BlockSystem Point Block) : Prop :=
  (elevenFiveSecondMoment S = 28 ∧
      elevenFiveC40SmallDegreeCount S 4 = 1 ∧
      elevenFiveC40SmallDegreeCount S 1 = 0 ∧
      elevenFiveC40SmallDegreeCount S 2 = 4 ∧
      elevenFiveC40SmallDegreeCount S 3 = 6) ∨
    (elevenFiveSecondMoment S = 30 ∧
      elevenFiveC40SmallDegreeCount S 4 = 2 ∧
      elevenFiveC40SmallDegreeCount S 1 = 1 ∧
      elevenFiveC40SmallDegreeCount S 2 = 3 ∧
      elevenFiveC40SmallDegreeCount S 3 = 5) ∨
    (elevenFiveSecondMoment S = 30 ∧
      elevenFiveC40SmallDegreeCount S 4 = 3 ∧
      elevenFiveC40SmallDegreeCount S 1 = 0 ∧
      elevenFiveC40SmallDegreeCount S 2 = 6 ∧
      elevenFiveC40SmallDegreeCount S 3 = 2)

private theorem c40SmallSix_noSingleton
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    (cfg : Configuration Point) (hcard : Fintype.card Point = 11)
    (hlocal : ∀ p : Point, ElevenFiveLocalRows (blockSystem cfg) p)
    (hC : (blockSystem cfg).totalCircleCount = 40)
    (hbeta : ∀ p : Point,
      (blockSystem cfg).blockDegree 3 p +
        (blockSystem cfg).blockDegree 4 p +
          (blockSystem cfg).blockDegree 5 p ≤ 18) :
    ∀ b ∈ (blockSystem cfg).blocksOfSize 5,
      ∀ c ∈ (blockSystem cfg).blocksOfSize 5, b ≠ c →
        ((blockSystem cfg).support b ∩
          (blockSystem cfg).support c).card ≠ 1 := by
  intro b hb c hc hbc hinter
  obtain ⟨p, hpEq⟩ := Finset.card_eq_one.mp hinter
  have hp : p ∈ (blockSystem cfg).support b ∩
      (blockSystem cfg).support c := by
    rw [hpEq]
    simp
  exact elevenFive_c40_l11_fiveBlock_singleton_impossible
    cfg hcard p (hlocal p) hC (hbeta p) hb hc
      (Finset.mem_inter.mp hp).1 (Finset.mem_inter.mp hp).2 hbc hinter

/-- Every degree-four five-block pivot in the C40/L11 beta domain has the
full `(d₃,d₄,d₅) = (9,4,4)` row, hence is an actual inverted four-star. -/
theorem elevenFive_c40_l11_degreeFour_reaches_k32_fourStar
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    (cfg : Configuration Point) (hcard : Fintype.card Point = 11)
    (hlocal : ∀ p : Point, ElevenFiveLocalRows (blockSystem cfg) p)
    (hC : (blockSystem cfg).totalCircleCount = 40)
    (hbeta : ∀ p : Point,
      (blockSystem cfg).blockDegree 3 p +
        (blockSystem cfg).blockDegree 4 p +
          (blockSystem cfg).blockDegree 5 p ≤ 18)
    (q : Point) (hqFour : (blockSystem cfg).blockDegree 5 q = 4) :
    ElevenFivePivotInvertedFourStar cfg q := by
  classical
  let S := blockSystem cfg
  have hdegreeFourSub := elevenFive_c40_l11_small_degreeFour_subset_degreeNine
    S (by simpa [S] using hlocal) (by simpa [S] using hC)
      (by simpa [S] using hbeta)
  have hqFourS : S.blockDegree 5 q = 4 := by simpa [S] using hqFour
  have hqNine : S.blockDegree 3 q = 9 := by
    have hqMem : q ∈ ((Finset.univ : Finset Point).filter fun p =>
        S.blockDegree 5 p = 4) := by
      simp [hqFourS]
    exact (Finset.mem_filter.mp (hdegreeFourSub hqMem)).2
  have hqBlockFour : S.blockDegree 4 q = 4 := by
    have hpair := (hlocal q).pairRow
    change S.blockDegree 3 q + 3 * S.blockDegree 4 q +
      6 * S.blockDegree 5 q = 45 at hpair
    omega
  exact
    { pivot_count_three := by simpa [S] using hqNine
      pivot_count_four := by simpa [S] using hqBlockFour
      pivot_count_five := hqFour
      inverted_card := by rw [card_awayFrom, hcard] }

/-- The nominal moment-28 face with no degree-four point is impossible:
the unique outsider of the disjoint pair has five-degree four. -/
theorem elevenFive_c40_l11_b5_six_zeroFour_twoDefect_impossible
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    (cfg : Configuration Point) (hcard : Fintype.card Point = 11)
    (hlocal : ∀ p : Point, ElevenFiveLocalRows (blockSystem cfg) p)
    (hC : (blockSystem cfg).totalCircleCount = 40)
    (hfive : (blockSystem cfg).blockCount 5 = 6)
    (hbeta : ∀ p : Point,
      (blockSystem cfg).blockDegree 3 p +
        (blockSystem cfg).blockDegree 4 p +
          (blockSystem cfg).blockDegree 5 p ≤ 18)
    (hmoment : elevenFiveSecondMoment (blockSystem cfg) = 28)
    (hfour : elevenFiveC40SmallDegreeCount (blockSystem cfg) 4 = 0) :
    False := by
  classical
  let S := blockSystem cfg
  have hnoSingleton := c40SmallSix_noSingleton cfg hcard hlocal hC hbeta
  obtain ⟨f, hf, g, hg, hfg, hdisjoint, _hallDouble, _hunique,
      q, hq, _hqUnique⟩ :=
    fiveBlock_unique_disjoint_pair_outsider_degree_four_of_six
      S hcard (by simpa [S] using hfive)
        (by simpa [S] using hmoment) (by simpa [S] using hnoSingleton)
  have hqFour : S.blockDegree 5 q = 4 := hq.2
  have hqMem : q ∈ ((Finset.univ : Finset Point).filter fun p =>
      S.blockDegree 5 p = 4) := by
    simp [hqFour]
  have hzero : ((Finset.univ : Finset Point).filter fun p =>
      S.blockDegree 5 p = 4).card = 0 := by
    simpa [S, elevenFiveC40SmallDegreeCount] using hfour
  have hempty := Finset.card_eq_zero.mp hzero
  rw [hempty] at hqMem
  simp at hqMem

/-- Every moment-28 six-block face reaches an actual `(9,4,4)` inverted
four-star at the unique point outside its disjoint pair.  This is the exact
entrance to the remaining K3.2 branch. -/
theorem elevenFive_c40_l11_b5_six_twoDefect_reaches_k32_fourStar
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    (cfg : Configuration Point) [DecidableEq (GeometricBlock cfg)]
    (hcard : Fintype.card Point = 11)
    (hlocal : ∀ p : Point, ElevenFiveLocalRows (blockSystem cfg) p)
    (hC : (blockSystem cfg).totalCircleCount = 40)
    (hfive : (blockSystem cfg).blockCount 5 = 6)
    (hbeta : ∀ p : Point,
      (blockSystem cfg).blockDegree 3 p +
        (blockSystem cfg).blockDegree 4 p +
          (blockSystem cfg).blockDegree 5 p ≤ 18)
    (hmoment : elevenFiveSecondMoment (blockSystem cfg) = 28) :
    ∃ f ∈ (blockSystem cfg).blocksOfSize 5,
      ∃ g ∈ (blockSystem cfg).blocksOfSize 5,
        f ≠ g ∧
          ((blockSystem cfg).support f ∩
            (blockSystem cfg).support g).card = 0 ∧
          (∀ b ∈ (blockSystem cfg).blocksOfSize 5,
            ∀ c ∈ (blockSystem cfg).blocksOfSize 5,
              b ≠ c →
                ({b, c} : Finset (GeometricBlock cfg)) ≠
                  ({f, g} : Finset (GeometricBlock cfg)) →
                ((blockSystem cfg).support b ∩
                  (blockSystem cfg).support c).card = 2) ∧
          ∃ q : Point,
            q ∉ (blockSystem cfg).support f ∪
              (blockSystem cfg).support g ∧
            ElevenFivePivotInvertedFourStar cfg q := by
  classical
  let S := blockSystem cfg
  have hnoSingleton := c40SmallSix_noSingleton cfg hcard hlocal hC hbeta
  obtain ⟨f, hf, g, hg, hfg, hdisjoint, hallDouble, _hunique,
      q, hq, _hqUnique⟩ :=
    fiveBlock_unique_disjoint_pair_outsider_degree_four_of_six
      S hcard (by simpa [S] using hfive)
        (by simpa [S] using hmoment) (by simpa [S] using hnoSingleton)
  have H : ElevenFivePivotInvertedFourStar cfg q :=
    elevenFive_c40_l11_degreeFour_reaches_k32_fourStar
      cfg hcard hlocal hC hbeta q (by simpa [S] using hq.2)
  refine ⟨f, by simpa [S] using hf, g, by simpa [S] using hg,
    hfg, by simpa [S] using hdisjoint, ?_, q, ?_, H⟩
  · intro b hb c hc hbc hpairNe
    exact hallDouble b (by simpa [S] using hb) c (by simpa [S] using hc)
      hbc (by simpa [S] using hpairNe)
  · simpa [S] using hq.1

/-! ## The all-double finite row -/

/-- Equality in the six-block pair moment forces every distinct pair to
meet in two points. -/
private theorem c40SmallSix_allDouble_of_secondMoment_thirty
    {Point : Type u} {Block : Type v} [Fintype Point] [Fintype Block]
    [DecidableEq Point] [DecidableEq Block]
    (S : BlockSystem Point Block)
    (hfive : S.blockCount 5 = 6)
    (hmoment : elevenFiveSecondMoment S = 30) :
    ∀ b ∈ S.blocksOfSize 5, ∀ c ∈ S.blocksOfSize 5,
      b ≠ c → (S.support b ∩ S.support c).card = 2 := by
  classical
  let F := S.blocksOfSize 5
  have hFcard : F.card = 6 := by
    simpa [F, BlockSystem.blockCount] using hfive
  have hmoment' :
      (∑ p : Point, Nat.choose (S.degreeIn F p) 2) =
        2 * Nat.choose F.card 2 := by
    simpa [F, BlockSystem.blockDegree, elevenFiveSecondMoment,
      hFcard, Nat.choose] using hmoment
  let Q := F.powersetCard 2
  let q : Finset Block → ℕ := fun A => (S.commonSupport A).card
  have hQcard : Q.card = Nat.choose F.card 2 := by simp [Q]
  have htotal : (∑ A ∈ Q, q A) = 2 * Nat.choose F.card 2 := by
    change (∑ A ∈ F.powersetCard 2, (S.commonSupport A).card) = _
    rw [← S.binomial_degree_moment F 2]
    exact hmoment'
  have htermLe (A : Finset Block) (hA : A ∈ Q) : q A ≤ 2 := by
    dsimp [q]
    apply S.commonSupport_card_le_two
    have hA' : A ∈ F.powersetCard 2 := by simpa [Q] using hA
    exact (Finset.mem_powersetCard.mp hA').2
  have hconstant : (∑ _A ∈ Q, 2) = 2 * Nat.choose F.card 2 := by
    simp [hQcard, Nat.mul_comm]
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

/-- Public six-block specialization of the all-double equality row. -/
theorem elevenFive_c40_l11_b5_six_allDouble_of_secondMoment_thirty
    {Point : Type u} {Block : Type v} [Fintype Point] [Fintype Block]
    [DecidableEq Point] [DecidableEq Block]
    (S : BlockSystem Point Block)
    (hfive : S.blockCount 5 = 6)
    (hmoment : elevenFiveSecondMoment S = 30) :
    ∀ b ∈ S.blocksOfSize 5, ∀ c ∈ S.blocksOfSize 5,
      b ≠ c → (S.support b ∩ S.support c).card = 2 :=
  c40SmallSix_allDouble_of_secondMoment_thirty S hfive hmoment

/-- Two degree-four pivots among six five-blocks lie together on at least
two of the five-blocks.  This is the finite common-block entrance needed
before comparing their harmonic four-stars. -/
theorem c40SmallSix_two_degreeFour_common_fiveBlocks
    {Point : Type u} {Block : Type v} [Fintype Point] [Fintype Block]
    [DecidableEq Point] [DecidableEq Block]
    (S : BlockSystem Point Block) (hfive : S.blockCount 5 = 6)
    (p q : Point) (hp : S.blockDegree 5 p = 4)
    (hq : S.blockDegree 5 q = 4) :
    2 ≤ (((S.blocksOfSize 5).filter fun b => p ∈ S.support b) ∩
      ((S.blocksOfSize 5).filter fun b => q ∈ S.support b)).card := by
  classical
  let F := S.blocksOfSize 5
  let P := F.filter fun b => p ∈ S.support b
  let Q := F.filter fun b => q ∈ S.support b
  have hFcard : F.card = 6 := by
    simpa [F, BlockSystem.blockCount] using hfive
  have hPcardRaw : P.card = S.blockDegree 5 p := rfl
  have hQcardRaw : Q.card = S.blockDegree 5 q := rfl
  have hPcard : P.card = 4 := hPcardRaw.trans hp
  have hQcard : Q.card = 4 := hQcardRaw.trans hq
  have hunionSub : P ∪ Q ⊆ F :=
    Finset.union_subset (Finset.filter_subset _ _) (Finset.filter_subset _ _)
  have hunionLe := Finset.card_le_card hunionSub
  have hformula := Finset.card_union_add_card_inter P Q
  change 2 ≤ (P ∩ Q).card
  omega

/-- A member of the six-block all-double family has five-degree mass
`5 + 5·2 = 15` on its support. -/
private theorem c40SmallSix_support_degree_sum_eq_fifteen_of_allDouble
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
        have hEraseCard : (F.erase b).card = 5 := by
          rw [Finset.card_erase_of_mem hbF, hFcard]
        simp [hEraseCard]
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

/-- The all-double profile with one degree-four point and two degree-one
points is impossible.  A five-block through a degree-one point has mass at
most `1 + 4 + 3·3 = 14`, but the all-double row gives mass fifteen. -/
theorem elevenFive_c40_l11_b5_six_oneFour_twoOne_allDouble_impossible
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    (cfg : Configuration Point) (hcard : Fintype.card Point = 11)
    (hlocal : ∀ p : Point, ElevenFiveLocalRows (blockSystem cfg) p)
    (hC : (blockSystem cfg).totalCircleCount = 40)
    (hfive : (blockSystem cfg).blockCount 5 = 6)
    (hbeta : ∀ p : Point,
      (blockSystem cfg).blockDegree 3 p +
        (blockSystem cfg).blockDegree 4 p +
          (blockSystem cfg).blockDegree 5 p ≤ 18)
    (hmoment : elevenFiveSecondMoment (blockSystem cfg) = 30)
    (hfour : elevenFiveC40SmallDegreeCount (blockSystem cfg) 4 = 1)
    (hone : elevenFiveC40SmallDegreeCount (blockSystem cfg) 1 = 2) :
    False := by
  classical
  let S := blockSystem cfg
  let F := S.blocksOfSize 5
  let A : Finset Point := (Finset.univ : Finset Point).filter fun p =>
    S.blockDegree 5 p = 4
  have hAcard : A.card = 1 := by
    simpa [A, S, elevenFiveC40SmallDegreeCount] using hfour
  have honeCard : ((Finset.univ : Finset Point).filter fun p =>
      S.blockDegree 5 p = 1).card = 2 := by
    simpa [S, elevenFiveC40SmallDegreeCount] using hone
  have honePos : 0 < ((Finset.univ : Finset Point).filter fun p =>
      S.blockDegree 5 p = 1).card := by omega
  obtain ⟨u, huMem⟩ := Finset.card_pos.mp honePos
  have huOne : S.blockDegree 5 u = 1 := (Finset.mem_filter.mp huMem).2
  have hincidentPos : 0 < (F.filter fun b => u ∈ S.support b).card := by
    change 0 < S.blockDegree 5 u
    omega
  obtain ⟨b, hbInc⟩ := Finset.card_pos.mp hincidentPos
  have hbData := Finset.mem_filter.mp hbInc
  have hbF : b ∈ F := hbData.1
  have hub : u ∈ S.support b := hbData.2
  have hallDouble := c40SmallSix_allDouble_of_secondMoment_thirty
    S (by simpa [S] using hfive) (by simpa [S] using hmoment)
  have hrow : (∑ p ∈ S.support b, S.blockDegree 5 p) = 15 := by
    apply c40SmallSix_support_degree_sum_eq_fifteen_of_allDouble
      S b (by simpa [F] using hbF) (by simpa [S] using hfive)
    intro c hc hcb
    exact hallDouble b (by simpa [F] using hbF) c hc hcb.symm
  let R := (S.support b).erase u
  have hRcard : R.card = 4 := by
    dsimp [R]
    rw [Finset.card_erase_of_mem hub, S.mem_blocksOfSize.mp hbF]
  have hpointBound (x : Point) :
      S.blockDegree 5 x ≤ 3 + (if x ∈ A then 1 else 0) := by
    rcases elevenFive_c40_l11_small_fiveDegree_values
      S (by simpa [S] using hlocal) (by simpa [S] using hC)
        (by simpa [S] using hbeta) x with h1 | h2 | h3 | h4
    · simp [A, h1]
    · simp [A, h2]
    · simp [A, h3]
    · simp [A, h4]
  have hsumLe := Finset.sum_le_sum
    (s := R) fun x _hx => hpointBound x
  rw [Finset.sum_add_distrib] at hsumLe
  have hthreeSum : (∑ _x ∈ R, 3) = 12 := by simp [hRcard]
  rw [hthreeSum] at hsumLe
  have hindicator :
      (∑ x ∈ R, if x ∈ A then 1 else 0) =
        (R.filter fun x => x ∈ A).card := by
    rw [← Finset.sum_filter]
    simp
  have hfilterSub : (R.filter fun x => x ∈ A) ⊆ A := by
    intro x hx
    exact (Finset.mem_filter.mp hx).2
  have hindicatorLe :
      (∑ x ∈ R, if x ∈ A then 1 else 0) ≤ 1 := by
    rw [hindicator]
    have hle := Finset.card_le_card hfilterSub
    omega
  have hsumR : (∑ x ∈ R, S.blockDegree 5 x) ≤ 13 := by omega
  have hsplit := Finset.sum_erase_add (S.support b)
    (fun x => S.blockDegree 5 x) hub
  change (∑ x ∈ R, S.blockDegree 5 x) + S.blockDegree 5 u =
    ∑ x ∈ S.support b, S.blockDegree 5 x at hsplit
  rw [hrow, huOne] at hsplit
  omega

/-- Maximal finite `B₅ = 6` reduction: only the three genuine
K3.2/K3.3 branches survive. -/
theorem elevenFive_c40_l11_b5_six_reduces_to_k32k33Residual
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    (cfg : Configuration Point) (hcard : Fintype.card Point = 11)
    (hlocal : ∀ p : Point, ElevenFiveLocalRows (blockSystem cfg) p)
    (hglobal : ElevenFiveGlobalRows (blockSystem cfg))
    (hC : (blockSystem cfg).totalCircleCount = 40)
    (hL : elevenFiveLineTotal (blockSystem cfg) = 11)
    (hfive : (blockSystem cfg).blockCount 5 = 6)
    (hbeta : ∀ p : Point,
      (blockSystem cfg).blockDegree 3 p +
        (blockSystem cfg).blockDegree 4 p +
          (blockSystem cfg).blockDegree 5 p ≤ 18) :
    ElevenFiveC40B5SixK32K33Residual (blockSystem cfg) := by
  rcases elevenFive_c40_l11_b5_six_arithmetic_profiles
    cfg hcard hlocal hglobal hC hL hfive hbeta with
      hfirst | hsecond | hthird | hfourth | hfifth
  · exact False.elim
      (elevenFive_c40_l11_b5_six_zeroFour_twoDefect_impossible
        cfg hcard hlocal hC hfive hbeta hfirst.1 hfirst.2.1)
  · exact Or.inl hsecond
  · exact False.elim
      (elevenFive_c40_l11_b5_six_oneFour_twoOne_allDouble_impossible
        cfg hcard hlocal hC hfive hbeta hthird.1 hthird.2.1
          hthird.2.2.1)
  · exact Or.inr (Or.inl hfourth)
  · exact Or.inr (Or.inr hfifth)

/-- Every one of the three surviving profiles contains a concrete
`(9,4,4)` pivot at which the K3.2 four-star API applies. -/
theorem elevenFive_c40_l11_b5_six_k32k33Residual_exists_fourStar
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    (cfg : Configuration Point) (hcard : Fintype.card Point = 11)
    (hlocal : ∀ p : Point, ElevenFiveLocalRows (blockSystem cfg) p)
    (hC : (blockSystem cfg).totalCircleCount = 40)
    (hbeta : ∀ p : Point,
      (blockSystem cfg).blockDegree 3 p +
        (blockSystem cfg).blockDegree 4 p +
          (blockSystem cfg).blockDegree 5 p ≤ 18)
    (hresidual :
      ElevenFiveC40B5SixK32K33Residual (blockSystem cfg)) :
    ∃ q : Point, ElevenFivePivotInvertedFourStar cfg q := by
  classical
  let S := blockSystem cfg
  let A : Finset Point := (Finset.univ : Finset Point).filter fun p =>
    S.blockDegree 5 p = 4
  have hApos : 0 < A.card := by
    rcases hresidual with hfirst | hsecond | hthird
    · have hAcard : A.card = 1 := by
        simpa [A, S, elevenFiveC40SmallDegreeCount] using hfirst.2.1
      omega
    · have hAcard : A.card = 2 := by
        simpa [A, S, elevenFiveC40SmallDegreeCount] using hsecond.2.1
      omega
    · have hAcard : A.card = 3 := by
        simpa [A, S, elevenFiveC40SmallDegreeCount] using hthird.2.1
      omega
  obtain ⟨q, hqA⟩ := Finset.card_pos.mp hApos
  have hqFour : (blockSystem cfg).blockDegree 5 q = 4 := by
    have hqFourS : S.blockDegree 5 q = 4 := (Finset.mem_filter.mp hqA).2
    simpa [S] using hqFourS
  exact ⟨q, elevenFive_c40_l11_degreeFour_reaches_k32_fourStar
    cfg hcard hlocal hC hbeta q hqFour⟩

/-- In either surviving all-double profile there are two different actual
four-star pivots sharing at least two five-blocks.  The remaining K3.3 step
must compare the harmonic structures induced on one of those common
blocks. -/
theorem elevenFive_c40_l11_b5_six_allDoubleResidual_two_fourStars
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    (cfg : Configuration Point) [DecidableEq (GeometricBlock cfg)]
    (hcard : Fintype.card Point = 11)
    (hlocal : ∀ p : Point, ElevenFiveLocalRows (blockSystem cfg) p)
    (hC : (blockSystem cfg).totalCircleCount = 40)
    (hfive : (blockSystem cfg).blockCount 5 = 6)
    (hbeta : ∀ p : Point,
      (blockSystem cfg).blockDegree 3 p +
        (blockSystem cfg).blockDegree 4 p +
          (blockSystem cfg).blockDegree 5 p ≤ 18)
    (hmoment : elevenFiveSecondMoment (blockSystem cfg) = 30)
    (hresidual :
      ElevenFiveC40B5SixK32K33Residual (blockSystem cfg)) :
    ∃ p q : Point, p ≠ q ∧
      ElevenFivePivotInvertedFourStar cfg p ∧
      ElevenFivePivotInvertedFourStar cfg q ∧
      2 ≤ ((((blockSystem cfg).blocksOfSize 5).filter fun b =>
          p ∈ (blockSystem cfg).support b) ∩
        (((blockSystem cfg).blocksOfSize 5).filter fun b =>
          q ∈ (blockSystem cfg).support b)).card := by
  classical
  let S := blockSystem cfg
  let A : Finset Point := (Finset.univ : Finset Point).filter fun p =>
    S.blockDegree 5 p = 4
  have hAtwo : 1 < A.card := by
    rcases hresidual with hfirst | hsecond | hthird
    · have hmomentFirst : elevenFiveSecondMoment S = 28 := by
        simpa [S] using hfirst.1
      have hmomentS : elevenFiveSecondMoment S = 30 := by
        simpa [S] using hmoment
      omega
    · have hAcard : A.card = 2 := by
        simpa [A, S, elevenFiveC40SmallDegreeCount] using hsecond.2.1
      omega
    · have hAcard : A.card = 3 := by
        simpa [A, S, elevenFiveC40SmallDegreeCount] using hthird.2.1
      omega
  obtain ⟨p, hpA, q, hqA, hpq⟩ := Finset.one_lt_card.mp hAtwo
  have hpFourS : S.blockDegree 5 p = 4 := (Finset.mem_filter.mp hpA).2
  have hqFourS : S.blockDegree 5 q = 4 := (Finset.mem_filter.mp hqA).2
  have hpFour : (blockSystem cfg).blockDegree 5 p = 4 := by
    simpa [S] using hpFourS
  have hqFour : (blockSystem cfg).blockDegree 5 q = 4 := by
    simpa [S] using hqFourS
  have Hp : ElevenFivePivotInvertedFourStar cfg p :=
    elevenFive_c40_l11_degreeFour_reaches_k32_fourStar
      cfg hcard hlocal hC hbeta p hpFour
  have Hq : ElevenFivePivotInvertedFourStar cfg q :=
    elevenFive_c40_l11_degreeFour_reaches_k32_fourStar
      cfg hcard hlocal hC hbeta q hqFour
  have hcommon := c40SmallSix_two_degreeFour_common_fiveBlocks
    S (by simpa [S] using hfive) p q hpFourS hqFourS
  exact ⟨p, q, hpq, Hp, Hq, by simpa [S] using hcommon⟩

/-- Maximal finite endpoint: the exact residual is accompanied by an
actual K3.2 four-star anchor. -/
theorem elevenFive_c40_l11_b5_six_reduces_to_k32k33Endpoint
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    (cfg : Configuration Point) (hcard : Fintype.card Point = 11)
    (hlocal : ∀ p : Point, ElevenFiveLocalRows (blockSystem cfg) p)
    (hglobal : ElevenFiveGlobalRows (blockSystem cfg))
    (hC : (blockSystem cfg).totalCircleCount = 40)
    (hL : elevenFiveLineTotal (blockSystem cfg) = 11)
    (hfive : (blockSystem cfg).blockCount 5 = 6)
    (hbeta : ∀ p : Point,
      (blockSystem cfg).blockDegree 3 p +
        (blockSystem cfg).blockDegree 4 p +
          (blockSystem cfg).blockDegree 5 p ≤ 18) :
    ElevenFiveC40B5SixK32K33Residual (blockSystem cfg) ∧
      ∃ q : Point, ElevenFivePivotInvertedFourStar cfg q := by
  have hresidual := elevenFive_c40_l11_b5_six_reduces_to_k32k33Residual
    cfg hcard hlocal hglobal hC hL hfive hbeta
  exact ⟨hresidual,
    elevenFive_c40_l11_b5_six_k32k33Residual_exists_fourStar
      cfg hcard hlocal hC hbeta hresidual⟩

/-- Configuration-level materialization of the maximal unconditional
`B₅ = 6` front. -/
theorem elevenFive_c40_l11_b5_six_k32k33Residual_of_configuration
    (Mel : RealPlaneMelchiorPrinciple.{u})
    (Langer : RealPlaneLangerPrinciple.{u})
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
    (hL : elevenFiveLineTotal (blockSystem cfg) = 11)
    (hfive : (blockSystem cfg).blockCount 5 = 6) :
    ElevenFiveC40B5SixK32K33Residual (blockSystem cfg) := by
  have hCtotal : (blockSystem cfg).totalCircleCount = 40 := by
    rw [totalCircleCount_eq_card_determinedCircle,
      ← Erdos506.V3.circleCount_eq_card_determinedCircle]
    exact hC
  have hCupper : (blockSystem cfg).totalCircleCount ≤ 40 := by omega
  have hlocal : ∀ p : Point,
      ElevenFiveLocalRows (blockSystem cfg) p := fun p =>
    elevenFiveLocalRows_of_configuration
      Mel Langer EvenArr Cross Kelly U17 TenGeometry
        cfg hadm hcard hcap hCupper p
  have hglobal : ElevenFiveGlobalRows (blockSystem cfg) :=
    elevenFiveGlobalRows_of_configuration Mel cfg hadm hcard hcap hlocal
  have hbeta := elevenFive_c40_l11_beta_cap
    Mel EvenArr Cross Kelly U17 TenGeometry
      cfg hadm hcard hcap hglobal hCtotal hL
  exact elevenFive_c40_l11_b5_six_reduces_to_k32k33Residual
    cfg hcard hlocal hglobal hCtotal hL hfive hbeta

/-- Configuration-level form of the maximal endpoint, retaining both the
exact residual profile and a concrete `(9,4,4)` four-star anchor. -/
theorem elevenFive_c40_l11_b5_six_k32k33Endpoint_of_configuration
    (Mel : RealPlaneMelchiorPrinciple.{u})
    (Langer : RealPlaneLangerPrinciple.{u})
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
    (hL : elevenFiveLineTotal (blockSystem cfg) = 11)
    (hfive : (blockSystem cfg).blockCount 5 = 6) :
    ElevenFiveC40B5SixK32K33Residual (blockSystem cfg) ∧
      ∃ q : Point, ElevenFivePivotInvertedFourStar cfg q := by
  have hCtotal : (blockSystem cfg).totalCircleCount = 40 := by
    rw [totalCircleCount_eq_card_determinedCircle,
      ← Erdos506.V3.circleCount_eq_card_determinedCircle]
    exact hC
  have hCupper : (blockSystem cfg).totalCircleCount ≤ 40 := by omega
  have hlocal : ∀ p : Point,
      ElevenFiveLocalRows (blockSystem cfg) p := fun p =>
    elevenFiveLocalRows_of_configuration
      Mel Langer EvenArr Cross Kelly U17 TenGeometry
        cfg hadm hcard hcap hCupper p
  have hglobal : ElevenFiveGlobalRows (blockSystem cfg) :=
    elevenFiveGlobalRows_of_configuration Mel cfg hadm hcard hcap hlocal
  have hbeta := elevenFive_c40_l11_beta_cap
    Mel EvenArr Cross Kelly U17 TenGeometry
      cfg hadm hcard hcap hglobal hCtotal hL
  exact elevenFive_c40_l11_b5_six_reduces_to_k32k33Endpoint
    cfg hcard hlocal hglobal hCtotal hL hfive hbeta

end Erdos506.V1
