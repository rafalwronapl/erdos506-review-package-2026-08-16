import Erdos506.V1.TwelveGeometry
import Erdos506.Block.Moments
import Erdos506.Finite.IncidenceMoments
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.LinearAlgebra.QuadraticForm.Dual

/-!
# Construction of the twelve-point Gram principle

The five fields of `RealPlaneTwelveGramPrinciple` are consequences of the
unique-triple-owner block calculus.  The global rich-block bound is the usual
centred-incidence-vector argument: after adjoining one positive coordinate,
the rich blocks give a linearly independent obtuse family in a vector space
of dimension at most twelve.  The local and six-block bounds use the same
Gram inequalities in their first/second-moment form.
-/

namespace Erdos506.V1

open Erdos506.Block
open Erdos506.Block.BlockSystem
open Erdos506.Incidence
open Erdos506.V4
open Module Real
open scoped BigOperators InnerProductSpace

universe u

noncomputable section

private theorem rich_size_layers_disjoint
    {Point Block : Type*} [Fintype Point] [Fintype Block]
    [DecidableEq Point]
    (S : BlockSystem Point Block) :
    Disjoint (S.blocksOfSize 5) (S.blocksOfSize 6) := by
  classical
  apply Finset.disjoint_left.mpr
  intro b hb5 hb6
  have h5 := S.mem_blocksOfSize.mp hb5
  have h6 := S.mem_blocksOfSize.mp hb6
  omega

/-! ## A seven-block local obstruction -/

private theorem two_mul_choose_two_local (n : Nat) :
    2 * Nat.choose n 2 = n * (n - 1) := by
  have h := Nat.choose_succ_right_eq n 1
  simpa [Nat.choose_one_right, Nat.mul_comm] using h

private theorem twice_le_choose_add_three (n : Nat) :
    2 * n <= Nat.choose n 2 + 3 := by
  by_cases hn : n <= 3
  · interval_cases n <;> norm_num [Nat.choose]
  · have hn4 : 4 <= n := by omega
    have hsub : n - 1 + 1 = n := by omega
    have hchoose := two_mul_choose_two_local n
    nlinarith

/-- Seven blocks of size at least five cannot all pass through one point on
a twelve-point ground set. -/
private theorem seven_rich_blocks_through_point_impossible
    {Point Block : Type*} [Fintype Point] [Fintype Block]
    [DecidableEq Point] [DecidableEq Block]
    (S : BlockSystem Point Block) (hPoint : Fintype.card Point = 12)
    (F : Finset Block) (p : Point) (hFcard : F.card = 7)
    (hp : forall b, b ∈ F -> p ∈ S.support b)
    (hrich : forall b, b ∈ F -> 5 <= (S.support b).card) : False := by
  classical
  have hpDegree : S.degreeIn F p = 7 := by
    unfold BlockSystem.degreeIn
    have hfilter : F.filter (fun b => p ∈ S.support b) = F := by
      apply Finset.filter_eq_self.mpr
      exact hp
    rw [hfilter, hFcard]
  have hfirst := S.first_moment F
  have hfirstLower : 35 <= ∑ q : Point, S.degreeIn F q := by
    rw [hfirst]
    calc
      35 = ∑ _b ∈ F, 5 := by simp [hFcard]
      _ <= ∑ b ∈ F, (S.support b).card := by
        exact Finset.sum_le_sum fun b hb => hrich b hb
  have hsecond := S.second_moment_le_two_choose F
  rw [hFcard] at hsecond
  norm_num [Nat.choose] at hsecond
  have hpointwise (q : Point) :
      2 * S.degreeIn F q + (if q = p then 10 else 0) <=
        Nat.choose (S.degreeIn F q) 2 + 3 := by
    by_cases hqp : q = p
    · subst q
      simp [hpDegree, Nat.choose]
    · simpa [hqp] using twice_le_choose_add_three (S.degreeIn F q)
  have hsum := Finset.sum_le_sum
    (s := (Finset.univ : Finset Point))
    (fun q _hq => hpointwise q)
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul] at hsum
  have hite : (∑ q : Point, if q = p then 10 else 0) = 10 := by simp
  rw [hite, hPoint] at hsum
  have htwice :
      (∑ q : Point, 2 * S.degreeIn F q) =
        2 * (∑ q : Point, S.degreeIn F q) := by
    rw [Finset.mul_sum]
  rw [htwice] at hsum
  omega

private theorem twelve_five_degree_cap
    {Point Block : Type*} [Fintype Point] [Fintype Block]
    [DecidableEq Point] [DecidableEq Block]
    (S : BlockSystem Point Block) (hPoint : Fintype.card Point = 12)
    (p : Point) : S.blockDegree 5 p <= 6 := by
  classical
  by_contra hnot
  have hseven : 7 <= S.blockDegree 5 p := by omega
  let P := (S.blocksOfSize 5).filter fun b => p ∈ S.support b
  have hPcard : P.card = S.blockDegree 5 p := rfl
  obtain ⟨F, hFP, hFcard⟩ :=
    Finset.exists_subset_card_eq (show 7 <= P.card by simpa [hPcard])
  apply seven_rich_blocks_through_point_impossible S hPoint F p hFcard
  · intro b hb
    exact (Finset.mem_filter.mp (hFP hb)).2
  · intro b hb
    have hb5 := S.mem_blocksOfSize.mp (Finset.mem_filter.mp (hFP hb)).1
    omega

private theorem twelve_five_degree_cap_on_six
    {Point Block : Type*} [Fintype Point] [Fintype Block]
    [DecidableEq Point] [DecidableEq Block]
    (S : BlockSystem Point Block) (hPoint : Fintype.card Point = 12)
    (p : Point) (hsix : 0 < S.blockDegree 6 p) :
    S.blockDegree 5 p <= 5 := by
  classical
  by_contra hnot
  have hsixFive : 6 <= S.blockDegree 5 p := by omega
  let P5 := (S.blocksOfSize 5).filter fun b => p ∈ S.support b
  have hP5card : P5.card = S.blockDegree 5 p := rfl
  obtain ⟨F5, hF5P, hF5card⟩ :=
    Finset.exists_subset_card_eq (show 6 <= P5.card by simpa [hP5card])
  let P6 := (S.blocksOfSize 6).filter fun b => p ∈ S.support b
  have hP6card : P6.card = S.blockDegree 6 p := rfl
  obtain ⟨b6, hb6⟩ : P6.Nonempty := Finset.card_pos.mp (by simpa [hP6card])
  have hb6size : (S.support b6).card = 6 :=
    S.mem_blocksOfSize.mp (Finset.mem_filter.mp hb6).1
  have hb6p : p ∈ S.support b6 := (Finset.mem_filter.mp hb6).2
  have hb6not : b6 ∉ F5 := by
    intro hb
    have hb5size := S.mem_blocksOfSize.mp
      (Finset.mem_filter.mp (hF5P hb)).1
    omega
  let F := insert b6 F5
  have hFcard : F.card = 7 := by simp [F, hb6not, hF5card]
  apply seven_rich_blocks_through_point_impossible S hPoint F p hFcard
  · intro b hb
    rcases Finset.mem_insert.mp hb with rfl | hbF5
    · exact hb6p
    · exact (Finset.mem_filter.mp (hF5P hbF5)).2
  · intro b hb
    rcases Finset.mem_insert.mp hb with rfl | hbF5
    · omega
    · have hb5size := S.mem_blocksOfSize.mp
        (Finset.mem_filter.mp (hF5P hbF5)).1
      omega

/-! ## The global centred-vector bound -/

private def twelveSumLinear (Point : Type*) [Fintype Point] :
    EuclideanSpace Real Point →ₗ[Real] Real where
  toFun x := ∑ p : Point, x p
  map_add' x y := by simp [Finset.sum_add_distrib]
  map_smul' c x := by simp [Finset.mul_sum]

private def twelveBalanced (Point : Type*) [Fintype Point] :
    Submodule Real (EuclideanSpace Real Point) :=
  LinearMap.ker (twelveSumLinear Point)

private def scaledCenteredIncidence
    {Point Block : Type*} [Fintype Point] [Fintype Block]
    [DecidableEq Point]
    (S : BlockSystem Point Block) (hPoint : Fintype.card Point = 12)
    (b : Block) : twelveBalanced Point := by
  classical
  refine ⟨WithLp.toLp 2 (fun p : Point =>
    12 * (if p ∈ S.support b then (1 : Real) else 0) -
      ((S.support b).card : Real)), ?_⟩
  change (∑ p : Point,
    (12 * (if p ∈ S.support b then (1 : Real) else 0) -
      ((S.support b).card : Real))) = 0
  rw [Finset.sum_sub_distrib]
  simp [hPoint]
  ring

private theorem scaledCenteredIncidence_inner
    {Point Block : Type*} [Fintype Point] [Fintype Block]
    [DecidableEq Point]
    (S : BlockSystem Point Block) (hPoint : Fintype.card Point = 12)
    (b c : Block) :
    inner Real (scaledCenteredIncidence S hPoint b)
        (scaledCenteredIncidence S hPoint c) =
      144 * ((S.support b ∩ S.support c).card : Real) -
        12 * ((S.support b).card : Real) * ((S.support c).card : Real) := by
  classical
  simp only [Submodule.coe_inner, scaledCenteredIncidence,
    PiLp.inner_apply, Real.inner_apply]
  simp_rw [sub_mul, mul_sub]
  simp [hPoint, Finset.inter_comm]
  ring

private theorem rich_family_card_le_twelve
    {Point Block : Type*} [Fintype Point] [Fintype Block]
    [DecidableEq Point] [DecidableEq Block]
    (S : BlockSystem Point Block) (hPoint : Fintype.card Point = 12)
    (F : Finset Block)
    (hsize : forall b, b ∈ F ->
      (S.support b).card = 5 ∨ (S.support b).card = 6) :
    F.card <= 12 := by
  classical
  let V := twelveBalanced Point
  let W := WithLp 2 (V × Real)
  let z : F → W := fun b => WithLp.toLp 2
    (scaledCenteredIncidence S hPoint b.1, (1 : Real))
  let positive : Module.Dual Real W :=
    { toFun := fun x => ((WithLp.ofLp x : V × Real)).2
      map_add' := fun x y => rfl
      map_smul' := fun c x => rfl }
  have hpositive (b : F) : 0 < positive (z b) := by
    simp [positive, z]
  have hpair : Pairwise fun (b c : F) =>
      (innerₗ W) (z b) (z c) <= 0 := by
    intro b c hbc
    have hbcBlock : b.1 ≠ c.1 := by
      intro heq
      apply hbc
      exact Subtype.ext heq
    have hinterNat : (S.support b.1 ∩ S.support c.1).card <= 2 := by
      have hlt := S.distinct_block_inter_card_lt_three hbcBlock
      omega
    have hinterReal :
        ((S.support b.1 ∩ S.support c.1).card : Real) <= 2 := by
      exact_mod_cast hinterNat
    have hbsize := hsize b.1 b.2
    have hcsize := hsize c.1 c.2
    simp only [z, innerₗ_apply_apply]
    change inner Real (scaledCenteredIncidence S hPoint b.1)
        (scaledCenteredIncidence S hPoint c.1) + 1 * 1 <= 0
    rw [scaledCenteredIncidence_inner S hPoint]
    rcases hbsize with hb5 | hb6
    · rcases hcsize with hc5 | hc6
      · rw [hb5, hc5]
        norm_num
        linarith [hinterReal]
      · rw [hb5, hc6]
        norm_num
        linarith [hinterReal]
    · rcases hcsize with hc5 | hc6
      · rw [hb6, hc5]
        norm_num
        linarith [hinterReal]
      · rw [hb6, hc6]
        norm_num
        linarith [hinterReal]
  have hposdef :
      (LinearMap.BilinMap.toQuadraticMap (innerₗ W)).PosDef := by
    intro x hx
    change 0 < inner Real x x
    exact real_inner_self_pos.mpr hx
  have hLI : LinearIndependent Real z :=
    LinearMap.BilinForm.linearIndependent_of_pairwise_le_zero
      (innerₗ W) hposdef positive z hpositive hpair
  have hcardFinrank : F.card <= Module.finrank Real W := by
    simpa using hLI.fintype_card_le_finrank
  have honeNotBalanced :
      WithLp.toLp 2 (fun _p : Point => (1 : Real)) ∉ twelveBalanced Point := by
    simp [twelveBalanced, twelveSumLinear, hPoint]
  have hbalancedNeTop : twelveBalanced Point ≠ ⊤ := by
    intro htop
    apply honeNotBalanced
    rw [htop]
    exact Submodule.mem_top
  have hbalanced : Module.finrank Real V <= 11 := by
    have hlt := Submodule.finrank_lt hbalancedNeTop
    rw [finrank_euclideanSpace, hPoint] at hlt
    exact Nat.le_pred_of_lt hlt
  have hW : Module.finrank Real W <= 12 := by
    change Module.finrank Real (WithLp 2 (V × Real)) <= 12
    rw [(WithLp.linearEquiv 2 Real (V × Real)).finrank_eq,
      Module.finrank_prod]
    simp only [Module.finrank_self]
    omega
  exact hcardFinrank.trans hW

private theorem twelve_rich_block_cap
    {Point Block : Type*} [Fintype Point] [Fintype Block]
    [DecidableEq Point] [DecidableEq Block]
    (S : BlockSystem Point Block) (hPoint : Fintype.card Point = 12) :
    S.blockCount 6 + S.blockCount 5 <= 12 := by
  classical
  let F := S.blocksOfSize 5 ∪ S.blocksOfSize 6
  have hF := rich_family_card_le_twelve S hPoint F (by
    intro b hb
    rcases Finset.mem_union.mp hb with hb5 | hb6
    · exact Or.inl (S.mem_blocksOfSize.mp hb5)
    · exact Or.inr (S.mem_blocksOfSize.mp hb6))
  have hcardF : F.card = S.blockCount 5 + S.blockCount 6 := by
    rw [Finset.card_union_of_disjoint (rich_size_layers_disjoint S)]
    rfl
  rw [hcardF] at hF
  omega

/-! ## Weighted first and second moments -/

private theorem sum_degreeIn_mul_degreeIn_le_two_mul_local
    {Point Block : Type*} [Fintype Point] [Fintype Block]
    [DecidableEq Point] [DecidableEq Block]
    (S : BlockSystem Point Block) (F G : Finset Block)
    (hne : forall b, b ∈ F -> forall c, c ∈ G -> b ≠ c) :
    (∑ p : Point, S.degreeIn F p * S.degreeIn G p) <=
      2 * F.card * G.card := by
  classical
  let indicator : Point → Block → Nat := fun p b =>
    if p ∈ S.support b then 1 else 0
  have hdegree (H : Finset Block) (p : Point) :
      S.degreeIn H p = ∑ b ∈ H, indicator p b := by
    simp [BlockSystem.degreeIn, indicator]
  simp_rw [hdegree]
  calc
    (∑ p : Point,
        (∑ b ∈ F, indicator p b) * (∑ c ∈ G, indicator p c)) =
        ∑ p : Point, ∑ b ∈ F, ∑ c ∈ G,
          indicator p b * indicator p c := by
      apply Fintype.sum_congr
      intro p
      rw [Finset.sum_mul_sum]
    _ = ∑ b ∈ F, ∑ p : Point, ∑ c ∈ G,
          indicator p b * indicator p c := by
      rw [Finset.sum_comm]
    _ = ∑ b ∈ F, ∑ c ∈ G, ∑ p : Point,
          indicator p b * indicator p c := by
      apply Finset.sum_congr rfl
      intro b hb
      rw [Finset.sum_comm]
    _ = ∑ b ∈ F, ∑ c ∈ G, (S.support b ∩ S.support c).card := by
      apply Finset.sum_congr rfl
      intro b hb
      apply Finset.sum_congr rfl
      intro c hc
      simpa [indicator, Erdos506.Finite.incidenceIndicator] using
        (Erdos506.Finite.sum_indicator_mul_eq_card_inter S.support b c)
    _ <= ∑ b ∈ F, ∑ _c ∈ G, 2 := by
      apply Finset.sum_le_sum
      intro b hb
      apply Finset.sum_le_sum
      intro c hc
      have hlt := S.distinct_block_inter_card_lt_three (hne b hb c hc)
      omega
    _ = 2 * F.card * G.card := by
      simp [Nat.mul_comm, Nat.mul_left_comm]

private theorem degree_square_sum_le
    {Point Block : Type*} [Fintype Point] [Fintype Block]
    [DecidableEq Point] [DecidableEq Block]
    (S : BlockSystem Point Block) (s : Nat) :
    (∑ p : Point, (S.blockDegree s p) ^ 2) <=
      s * S.blockCount s + 4 * Nat.choose (S.blockCount s) 2 := by
  have hfirst := S.block_incidence s
  have hsecond := S.second_moment_le_two_choose (S.blocksOfSize s)
  change (∑ p : Point, Nat.choose (S.blockDegree s p) 2) <=
    2 * Nat.choose (S.blockCount s) 2 at hsecond
  calc
    (∑ p : Point, (S.blockDegree s p) ^ 2) =
        (∑ p : Point, S.blockDegree s p) +
          2 * (∑ p : Point, Nat.choose (S.blockDegree s p) 2) := by
      calc
        _ = ∑ p : Point,
            (S.blockDegree s p + 2 * Nat.choose (S.blockDegree s p) 2) := by
          apply Fintype.sum_congr
          intro p
          cases hd : S.blockDegree s p with
          | zero => simp [Nat.choose]
          | succ n =>
              rw [two_mul_choose_two_local]
              simp
              ring
        _ = _ := by
          simp only [Finset.sum_add_distrib, Finset.mul_sum]
    _ <= s * S.blockCount s +
          2 * (2 * Nat.choose (S.blockCount s) 2) := by
      exact Nat.add_le_add (le_of_eq hfirst) (Nat.mul_le_mul_left 2 hsecond)
    _ = s * S.blockCount s + 4 * Nat.choose (S.blockCount s) 2 := by ring

private theorem five_degree_square_sum_le
    {Point Block : Type*} [Fintype Point] [Fintype Block]
    [DecidableEq Point] [DecidableEq Block]
    (S : BlockSystem Point Block) :
    (∑ p : Point, (S.blockDegree 5 p) ^ 2) <=
      2 * (S.blockCount 5) ^ 2 + 3 * S.blockCount 5 := by
  have h := degree_square_sum_le S 5
  calc
    _ <= 5 * S.blockCount 5 + 4 * Nat.choose (S.blockCount 5) 2 := h
    _ = _ := by
      cases hk : S.blockCount 5 with
      | zero => simp
      | succ k =>
          calc
            5 * (k + 1) + 4 * Nat.choose (k + 1) 2 =
                5 * (k + 1) + 2 * (2 * Nat.choose (k + 1) 2) := by ring
            _ = 5 * (k + 1) + 2 * ((k + 1) * k) := by
              rw [two_mul_choose_two_local]
              simp
            _ = 2 * (k + 1) ^ 2 + 3 * (k + 1) := by ring

private theorem six_degree_square_sum_le
    {Point Block : Type*} [Fintype Point] [Fintype Block]
    [DecidableEq Point] [DecidableEq Block]
    (S : BlockSystem Point Block) :
    (∑ p : Point, (S.blockDegree 6 p) ^ 2) <=
      2 * (S.blockCount 6) ^ 2 + 4 * S.blockCount 6 := by
  have h := degree_square_sum_le S 6
  calc
    _ <= 6 * S.blockCount 6 + 4 * Nat.choose (S.blockCount 6) 2 := h
    _ = _ := by
      cases hm : S.blockCount 6 with
      | zero => simp
      | succ m =>
          calc
            6 * (m + 1) + 4 * Nat.choose (m + 1) 2 =
                6 * (m + 1) + 2 * (2 * Nat.choose (m + 1) 2) := by ring
            _ = 6 * (m + 1) + 2 * ((m + 1) * m) := by
              rw [two_mul_choose_two_local]
              simp
            _ = 2 * (m + 1) ^ 2 + 4 * (m + 1) := by ring

private theorem five_six_cross_moment_le
    {Point Block : Type*} [Fintype Point] [Fintype Block]
    [DecidableEq Point] [DecidableEq Block]
    (S : BlockSystem Point Block) :
    (∑ p : Point, S.blockDegree 5 p * S.blockDegree 6 p) <=
      2 * S.blockCount 5 * S.blockCount 6 := by
  classical
  have hne : forall b, b ∈ S.blocksOfSize 5 ->
      forall c, c ∈ S.blocksOfSize 6 -> b ≠ c := by
    intro b hb c hc hbc
    subst c
    have h5 := S.mem_blocksOfSize.mp hb
    have h6 := S.mem_blocksOfSize.mp hc
    omega
  simpa only [BlockSystem.blockDegree, BlockSystem.blockCount] using
    sum_degreeIn_mul_degreeIn_le_two_mul_local
      S (S.blocksOfSize 5) (S.blocksOfSize 6) hne

private theorem weighted_rich_moments
    {Point Block : Type*} [Fintype Point] [Fintype Block]
    [DecidableEq Point] [DecidableEq Block]
    (S : BlockSystem Point Block) (a b : Nat) :
    let k := S.blockCount 5
    let m := S.blockCount 6
    (∑ p : Point, (a * S.blockDegree 5 p + b * S.blockDegree 6 p)) =
        5 * a * k + 6 * b * m ∧
      (∑ p : Point,
        (a * S.blockDegree 5 p + b * S.blockDegree 6 p) ^ 2) <=
        a ^ 2 * (2 * k ^ 2 + 3 * k) +
          b ^ 2 * (2 * m ^ 2 + 4 * m) +
          4 * a * b * k * m := by
  dsimp
  have h5 := five_degree_square_sum_le S
  have h6 := six_degree_square_sum_le S
  have hcross := five_six_cross_moment_le S
  constructor
  · rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
      S.block_incidence 5, S.block_incidence 6]
    ring
  · calc
      (∑ p : Point,
        (a * S.blockDegree 5 p + b * S.blockDegree 6 p) ^ 2) =
          a ^ 2 * (∑ p : Point, (S.blockDegree 5 p) ^ 2) +
            b ^ 2 * (∑ p : Point, (S.blockDegree 6 p) ^ 2) +
            2 * a * b *
              (∑ p : Point, S.blockDegree 5 p * S.blockDegree 6 p) := by
        simp_rw [show forall x y : Nat,
          (a * x + b * y) ^ 2 =
            a ^ 2 * x ^ 2 + b ^ 2 * y ^ 2 + 2 * a * b * (x * y) by
              intro x y
              ring]
        simp only [Finset.sum_add_distrib, Finset.mul_sum]
      _ <= a ^ 2 * (2 * S.blockCount 5 ^ 2 + 3 * S.blockCount 5) +
            b ^ 2 * (2 * S.blockCount 6 ^ 2 + 4 * S.blockCount 6) +
            2 * a * b * (2 * S.blockCount 5 * S.blockCount 6) := by
        exact Nat.add_le_add
          (Nat.add_le_add (Nat.mul_le_mul_left _ h5) (Nat.mul_le_mul_left _ h6))
          (Nat.mul_le_mul_left _ hcross)
      _ = _ := by ring

private theorem weighted_rich_cauchy
    {Point Block : Type*} [Fintype Point] [Fintype Block]
    [DecidableEq Point] [DecidableEq Block]
    (S : BlockSystem Point Block) (hPoint : Fintype.card Point = 12)
    (a b : Nat) :
    let k := S.blockCount 5
    let m := S.blockCount 6
    (5 * a * k + 6 * b * m) ^ 2 <=
      12 * (a ^ 2 * (2 * k ^ 2 + 3 * k) +
        b ^ 2 * (2 * m ^ 2 + 4 * m) + 4 * a * b * k * m) := by
  dsimp
  obtain ⟨hfirst, hsecond⟩ := weighted_rich_moments S a b
  have hcauchy := sq_sum_le_card_mul_sum_sq
    (s := (Finset.univ : Finset Point))
    (f := fun p => a * S.blockDegree 5 p + b * S.blockDegree 6 p)
  simp only [Finset.card_univ] at hcauchy
  rw [hfirst, hPoint] at hcauchy
  exact hcauchy.trans (Nat.mul_le_mul_left 12 hsecond)

private theorem twelve_six_block_caps
    {Point Block : Type*} [Fintype Point] [Fintype Block]
    [DecidableEq Point] [DecidableEq Block]
    (S : BlockSystem Point Block) (hPoint : Fintype.card Point = 12) :
    S.blockCount 6 <= 4 ∧
      (S.blockCount 6 = 4 → S.blockCount 5 = 0) ∧
      (S.blockCount 6 = 3 → S.blockCount 5 <= 3) ∧
      (S.blockCount 6 = 2 → S.blockCount 5 <= 8) ∧
      (S.blockCount 6 = 1 → S.blockCount 5 <= 11) := by
  let k := S.blockCount 5
  let m := S.blockCount 6
  have hmcap : m <= 4 := by
    have h := weighted_rich_cauchy S hPoint 0 1
    change S.blockCount 6 <= 4
    norm_num at h
    nlinarith
  have hm4 : m = 4 → k = 0 := by
    intro hm
    have h := weighted_rich_cauchy S hPoint 1 1
    change S.blockCount 6 = 4 at hm
    change S.blockCount 5 = 0
    rw [hm] at h
    norm_num at h
    nlinarith
  have hm3 : m = 3 → k <= 3 := by
    intro hm
    have h := weighted_rich_cauchy S hPoint 1 2
    change S.blockCount 6 = 3 at hm
    change S.blockCount 5 <= 3
    rw [hm] at h
    norm_num at h
    nlinarith
  have hm2weak : m = 2 → k <= 9 := by
    intro hm
    have h := weighted_rich_cauchy S hPoint 2 5
    change S.blockCount 6 = 2 at hm
    change S.blockCount 5 <= 9
    rw [hm] at h
    norm_num at h
    nlinarith
  have hm2 : m = 2 → k <= 8 := by
    intro hm
    have hk9le := hm2weak hm
    by_contra hnot
    have hk : k = 9 := by omega
    let f : Point → Nat := fun p =>
      4 * S.blockDegree 5 p + 9 * S.blockDegree 6 p
    obtain ⟨hfirst, hsecond⟩ := weighted_rich_moments S 4 9
    dsimp [k, m] at hk hm
    rw [hk, hm] at hfirst hsecond
    norm_num at hfirst hsecond
    have hcauchy := sq_sum_le_card_mul_sum_sq
      (s := (Finset.univ : Finset Point)) (f := f)
    simp only [Finset.card_univ] at hcauchy
    change (∑ p : Point, f p) = 288 at hfirst
    change (∑ p : Point, (f p) ^ 2) <= 6912 at hsecond
    rw [hfirst, hPoint] at hcauchy
    have hsquares : (∑ p : Point, (f p) ^ 2) = 6912 := by omega
    have hfirstZ : (∑ p : Point, (f p : Int)) = 288 := by
      exact_mod_cast hfirst
    have hsquaresZ : (∑ p : Point, (f p : Int) ^ 2) = 6912 := by
      exact_mod_cast hsquares
    have hvariance :
        (∑ p : Point, ((f p : Int) - 24) ^ 2) = 0 := by
      calc
        _ = (∑ p : Point, (f p : Int) ^ 2) -
              48 * (∑ p : Point, (f p : Int)) +
              576 * Fintype.card Point := by
            simp_rw [show forall z : Int, (z - 24) ^ 2 = z ^ 2 - 48 * z + 576 by
              intro z
              ring]
            simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib,
              Finset.mul_sum, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
            ring
        _ = 0 := by rw [hfirstZ, hsquaresZ, hPoint]; norm_num
    have hconstant (p : Point) : f p = 24 := by
      have hall := (Finset.sum_eq_zero_iff_of_nonneg
        (fun q (_hq : q ∈ (Finset.univ : Finset Point)) =>
          sq_nonneg ((f q : Int) - 24))).mp hvariance
      have hpzero := hall p (Finset.mem_univ p)
      have hpInt : (f p : Int) = 24 := by nlinarith
      exact_mod_cast hpInt
    have hmRaw : (S.blocksOfSize 6).card = 2 := hm
    obtain ⟨b, c, hbc, hblocks⟩ := Finset.card_eq_two.mp hmRaw
    have hbmem : b ∈ S.blocksOfSize 6 := by simp [hblocks]
    have hcmem : c ∈ S.blocksOfSize 6 := by simp [hblocks]
    have hbcard : (S.support b).card = 6 := S.mem_blocksOfSize.mp hbmem
    have hinter : (S.support b ∩ S.support c).card <= 2 := by
      have hlt := S.distinct_block_inter_card_lt_three hbc
      omega
    have hsplit := Finset.card_inter_add_card_sdiff (S.support b) (S.support c)
    have hdiffpos : 0 < (S.support b \ S.support c).card := by omega
    obtain ⟨p, hp⟩ := Finset.card_pos.mp hdiffpos
    have hpB : p ∈ S.support b := (Finset.mem_sdiff.mp hp).1
    have hpC : p ∉ S.support c := (Finset.mem_sdiff.mp hp).2
    have hd6 : S.blockDegree 6 p = 1 := by
      unfold BlockSystem.blockDegree BlockSystem.degreeIn
      rw [hblocks]
      rw [Finset.filter_insert, Finset.filter_singleton]
      simp only [hpB, hpC, if_true, if_false]
      exact Finset.card_singleton b
    have hpconst := hconstant p
    dsimp [f] at hpconst
    rw [hd6] at hpconst
    omega
  have hm1 : m = 1 → k <= 11 := by
    intro hm
    have hrich := twelve_rich_block_cap S hPoint
    dsimp [k, m] at hm ⊢
    omega
  exact ⟨by simpa [m] using hmcap,
    by simpa [m, k] using hm4,
    by simpa [m, k] using hm3,
    by simpa [m, k] using hm2,
    by simpa [m, k] using hm1⟩

/-! ## Public construction -/

/-- All five twelve-point Gram fields, constructed from finite incidence and
real linear algebra. -/
noncomputable def realPlaneTwelveGramPrinciple :
    RealPlaneTwelveGramPrinciple where
  fiveBlockCap := by
    classical
    intro alpha _ _ cfg _hadm hcard _hcap
    let S := blockSystem cfg
    have hrich := twelve_rich_block_cap S hcard
    dsimp [S] at hrich ⊢
    omega
  fiveDegreeCap := by
    classical
    intro alpha _ _ cfg _hadm hcard _hcap p
    exact twelve_five_degree_cap (blockSystem cfg) hcard p
  fiveDegreeCapOnSixBlock := by
    classical
    intro alpha _ _ cfg _hadm hcard _hcap p hsix
    exact twelve_five_degree_cap_on_six (blockSystem cfg) hcard p hsix
  richBlockCap := by
    classical
    intro alpha _ _ cfg _hadm hcard _hcap
    exact twelve_rich_block_cap (blockSystem cfg) hcard
  sixBlockCaps := by
    classical
    intro alpha _ _ cfg _hadm hcard _hcap
    exact twelve_six_block_caps (blockSystem cfg) hcard

end

end Erdos506.V1
