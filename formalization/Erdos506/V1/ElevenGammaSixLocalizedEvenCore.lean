import Erdos506.Incidence.EvenArrangementPrinciple
import Erdos506.V1.DirectKelly
import Erdos506.V1.LargeMaster
import Erdos506.V1.PivotMelchiorSlack

/-!
# Field-free localized even obstruction for the eleven--six branch

This is the acyclic geometric core of the localized `J ≤ 13` argument.  It
does not mention the boundary tables or the six-conic-events principle.  Its
input is the equality which those tables force at a disjoint five-host: the
sum of three-block degrees over the five outsiders is `27`.
-/

namespace Erdos506.V1

open Erdos506.Block
open Erdos506.Block.BlockSystem
open Erdos506.Incidence
open Erdos506.V3
open Erdos506.V4
open scoped BigOperators

universe u

private theorem elevenGammaSix_blockDegree_eq_zero_of_cap_six
    {Point Block : Type*} [Fintype Point] [Fintype Block]
    [DecidableEq Point]
    (S : BlockSystem Point Block) (hcap : BlockSizeCap S 6)
    (p : Point) {s : Nat} (hs : 7 ≤ s) :
    S.blockDegree s p = 0 := by
  classical
  have hzero : S.blockCount s = 0 := by
    apply Finset.card_eq_zero.mpr
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro b hb
    have hbSize := S.mem_blocksOfSize.mp hb
    have hbCap : (S.support b).card ≤ 6 := hcap b (by omega)
    omega
  have hle : S.blockDegree s p ≤ S.blockCount s := by
    unfold BlockSystem.blockDegree BlockSystem.degreeIn BlockSystem.blockCount
    exact Finset.card_filter_le _ _
  omega

/-- Three labels outside the selected six-set already identify the disjoint
five-host, by unique triple ownership. -/
theorem elevenGammaSix_fiveHost_eq_of_three_outside
    {Point Block : Type*} [Fintype Point] [Fintype Block]
    [DecidableEq Point]
    (S : BlockSystem Point Block) (D X : Finset Point)
    (H b : Block)
    (hXcompl : X = Finset.univ \ D)
    (hhost : S.support H = X)
    (houtside : 3 ≤ (S.support b \ D).card) : b = H := by
  classical
  obtain ⟨A, hAsub, hAcard⟩ := Finset.exists_subset_card_eq houtside
  let T : Erdos506.Finite.KSubset Point 3 := ⟨A, hAcard⟩
  have hbOwner : b = S.tripleOwner T :=
    S.triple_unique T b (fun q hq =>
      (Finset.mem_sdiff.mp (hAsub hq)).1)
  have hAX : A ⊆ X := by
    intro q hq
    have hqOut := hAsub hq
    rw [hXcompl]
    exact Finset.mem_sdiff.mpr
      ⟨Finset.mem_univ q, (Finset.mem_sdiff.mp hqOut).2⟩
  have hHOwner : H = S.tripleOwner T :=
    S.triple_unique T H (by simpa [hhost] using hAX)
  exact hbOwner.trans hHOwner.symm

private theorem elevenGammaSix_fiveHost_unique_rich_through_outsider
    {Point Block : Type*} [Fintype Point] [Fintype Block]
    [DecidableEq Point]
    (S : BlockSystem Point Block) (D X : Finset Point)
    (gamma H b : Block)
    (hgamma : S.support gamma = D)
    (hXcompl : X = Finset.univ \ D)
    (hhost : S.support H = X)
    (p : Point) (hpX : p ∈ X) (hpb : p ∈ S.support b)
    (hbSize : 5 ≤ (S.support b).card) : b = H := by
  have hpComp : p ∈ Finset.univ \ D := by
    rw [← hXcompl]
    exact hpX
  have hbgamma : b ≠ gamma := by
    intro h
    subst b
    have hpD : p ∈ D := by simpa [hgamma] using hpb
    exact (Finset.mem_sdiff.mp hpComp).2 hpD
  have hinter : (S.support b ∩ D).card ≤ 2 := by
    have hlt := S.distinct_block_inter_card_lt_three hbgamma
    rw [hgamma] at hlt
    exact Nat.le_of_lt_succ hlt
  have hsplit := Finset.card_inter_add_card_sdiff (S.support b) D
  have houtside : 3 ≤ (S.support b \ D).card := by omega
  exact elevenGammaSix_fiveHost_eq_of_three_outside
    S D X H b hXcompl hhost houtside

private theorem elevenGammaSix_unique_five_host_degrees
    {Point Block : Type*} [Fintype Point] [Fintype Block]
    [DecidableEq Point]
    (S : BlockSystem Point Block) (D X : Finset Point)
    (gamma H : Block)
    (hgamma : S.support gamma = D)
    (hXcompl : X = Finset.univ \ D)
    (hhost : S.support H = X)
    (hX : X.card = 5)
    (p : Point) (hp : p ∈ X) :
    S.blockDegree 5 p = 1 ∧ S.blockDegree 6 p = 0 := by
  classical
  have hHSize : (S.support H).card = 5 := by simpa [hhost] using hX
  have hHMem : H ∈ S.blocksOfSize 5 := S.mem_blocksOfSize.mpr hHSize
  have hHp : p ∈ S.support H := by simpa [hhost] using hp
  have hfive :
      (S.blocksOfSize 5).filter (fun b => p ∈ S.support b) = {H} := by
    ext b
    simp only [Finset.mem_filter, Finset.mem_singleton]
    constructor
    · rintro ⟨hb, hpb⟩
      exact elevenGammaSix_fiveHost_unique_rich_through_outsider
        S D X gamma H b hgamma hXcompl hhost p hp hpb
          (by rw [S.mem_blocksOfSize.mp hb])
    · rintro rfl
      exact ⟨hHMem, hHp⟩
  have hsix :
      (S.blocksOfSize 6).filter (fun b => p ∈ S.support b) = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro b hb
    obtain ⟨hb, hpb⟩ := Finset.mem_filter.mp hb
    have hbH := elevenGammaSix_fiveHost_unique_rich_through_outsider
      S D X gamma H b hgamma hXcompl hhost p hp hpb
        (by
          have hbSize := S.mem_blocksOfSize.mp hb
          omega)
    subst b
    have hbSize := S.mem_blocksOfSize.mp hb
    omega
  constructor
  · simpa [BlockSystem.blockDegree, BlockSystem.degreeIn] using
      congrArg Finset.card hfive
  · simpa [BlockSystem.blockDegree, BlockSystem.degreeIn] using
      congrArg Finset.card hsix

/-- A disjoint five-host together with outsider three-degree sum `27` is
impossible.  Kelly forces a degree-five outsider; the unique rich host then
makes its ten-point pivot inversion have Melchior slack exactly one. -/
theorem elevenGammaSix_localized_even_contradiction
    {α : Type u} [Fintype α] [DecidableEq α]
    (EvenArr : RealPlaneEvenArrangementPrinciple.{u})
    (Kelly : RealPlaneKellyMoserPrinciple.{u})
    (cfg : Configuration α) (hadm : Admissible cfg)
    (hpoint : Fintype.card α = 11)
    (gamma : DeterminedCircle cfg)
    (hgamma : (circleTrace cfg gamma.1).card = 6)
    (X : Finset α) (hX : X.card = 5)
    (hdisjoint : Disjoint (circleTrace cfg gamma.1) X)
    (H : GeometricBlock cfg)
    (hH : geometricBlockSupport cfg H = X)
    (hcap : BlockSizeCap (blockSystem cfg) 6)
    (hthreeSum :
      (∑ p ∈ X, (blockSystem cfg).blockDegree 3 p) = 27) : False := by
  classical
  let S := blockSystem cfg
  let D : Finset α := circleTrace cfg gamma.1
  have hXsub : X ⊆ Finset.univ \ D := by
    intro p hp
    refine Finset.mem_sdiff.mpr ⟨Finset.mem_univ p, ?_⟩
    intro hpD
    exact Finset.disjoint_left.mp hdisjoint hpD hp
  have hcomplCard : (Finset.univ \ D).card = 5 := by
    simp [D, Finset.card_sdiff_of_subset (Finset.subset_univ D),
      hpoint, hgamma]
  have hXcompl : X = Finset.univ \ D :=
    Finset.eq_of_subset_of_card_le hXsub (by rw [hX, hcomplCard])
  have hkelly (p : α) : 5 ≤ S.blockDegree 3 p := by
    have hp := Kelly.pivot_three_block_bound cfg hadm
      (by omega) (by omega) p
    rw [hpoint] at hp
    norm_num at hp
    change 30 ≤ 7 * S.blockDegree 3 p at hp
    omega
  have hexists : ∃ p ∈ X, S.blockDegree 3 p = 5 := by
    by_contra hnot
    push Not at hnot
    have hsumLower : (∑ _p ∈ X, 6) ≤ ∑ p ∈ X, S.blockDegree 3 p :=
      Finset.sum_le_sum fun p hp => by
        have hle := hkelly p
        have hne := hnot p hp
        omega
    simp [hX] at hsumLower
    change (∑ p ∈ X, S.blockDegree 3 p) = 27 at hthreeSum
    omega
  obtain ⟨p, hpX, hd3⟩ := hexists
  let gammaBlock : GeometricBlock cfg := Sum.inr gamma
  have hgammaSupport : S.support gammaBlock = D := rfl
  have hhostSupport : S.support H = X := hH
  obtain ⟨hd5, hd6⟩ := elevenGammaSix_unique_five_host_degrees
    S D X gammaBlock H hgammaSupport hXcompl hhostSupport hX p hpX
  have hd7 : S.blockDegree 7 p = 0 :=
    elevenGammaSix_blockDegree_eq_zero_of_cap_six S hcap p (by omega)
  have hd8 : S.blockDegree 8 p = 0 :=
    elevenGammaSix_blockDegree_eq_zero_of_cap_six S hcap p (by omega)
  have hd9 : S.blockDegree 9 p = 0 :=
    elevenGammaSix_blockDegree_eq_zero_of_cap_six S hcap p (by omega)
  have hd10 : S.blockDegree 10 p = 0 :=
    elevenGammaSix_blockDegree_eq_zero_of_cap_six S hcap p (by omega)
  have hd11 : S.blockDegree 11 p = 0 :=
    elevenGammaSix_blockDegree_eq_zero_of_cap_six S hcap p (by omega)
  have hIcc : Finset.Icc 3 11 = {3, 4, 5, 6, 7, 8, 9, 10, 11} := by decide
  have hsigma : S.pivotSigma p = 1 := by
    unfold BlockSystem.pivotSigma BlockSystem.nontrivialSizes
    rw [hpoint, hIcc]
    norm_num [hd3, hd5, hd6, hd7, hd8, hd9, hd10, hd11]
  have hnoncol : Noncollinear (pivotInversion cfg p) :=
    pivotInversion_noncollinear cfg hadm (by omega) p
  have hpivotCard : Fintype.card (AwayFrom p) = 10 := by
    rw [card_awayFrom, hpoint]
  have heven : Even (Fintype.card (AwayFrom p)) := by
    rw [hpivotCard]
    norm_num
  have hne := EvenArr.slack_ne_one (pivotInversion cfg p) hnoncol heven
  rw [← pivotSigma_eq_lineMelchiorSlack_fieldFree cfg p] at hne
  exact hne (by simpa [S] using hsigma)

end Erdos506.V1
