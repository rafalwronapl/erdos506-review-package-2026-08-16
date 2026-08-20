import Erdos506.Block.Moments
import Erdos506.Finite.SixFiveCanonical

/-!
# The punctured-pentagon transversal cap

Five five-subsets of a ten-set in a triple-owned block system force the
punctured complementary-pentagon design. This file proves the finite statement
needed in the ten-point five-block branch:

* the five-block degrees are exactly two or three;
* all pairs of five-blocks meet in exactly two points;
* adjoining the five degree-two points as a formal sixth block gives a
  `SixFiveDesign`;
* the existing canonical classification of that design reduces the
  four-blocks through a degree-three point to the punctured-pentagon
  transversal ledger; and
* the ledger has no compatible triple.

The formal sixth block is only a finite-set device. It is not asserted to be
a geometric line or circle.
-/

namespace Erdos506.Finite

open Erdos506.Block
open Erdos506.Block.BlockSystem
open scoped BigOperators

private theorem degreeIn_le_card
    {Point Block : Type*} [Fintype Point] [Fintype Block]
    [DecidableEq Point]
    (S : BlockSystem Point Block) (F : Finset Block) (p : Point) :
    S.degreeIn F p ≤ F.card := by
  classical
  exact Finset.card_filter_le _ _

/-- If all weights on a finite set are two or three, their sum records the
number of weight-two elements. -/
private theorem sum_add_card_filter_eq_three_mul_card
    {α : Type*} [DecidableEq α] (A : Finset α) (d : α → Nat)
    (hprofile : ∀ x, x ∈ A → d x = 2 ∨ d x = 3) :
    (∑ x ∈ A, d x) + (A.filter fun x => d x = 2).card = 3 * A.card := by
  classical
  calc
    (∑ x ∈ A, d x) + (A.filter fun x => d x = 2).card =
        (∑ x ∈ A, d x) +
          ∑ x ∈ A, if d x = 2 then 1 else 0 := by
            congr 1
            rw [Finset.card_eq_sum_ones, Finset.sum_filter]
    _ = ∑ x ∈ A, (d x + if d x = 2 then 1 else 0) := by
          rw [Finset.sum_add_distrib]
    _ = ∑ _x ∈ A, 3 := by
          apply Finset.sum_congr rfl
          intro x hx
          rcases hprofile x hx with hdegree | hdegree <;> simp [hdegree]
    _ = 3 * A.card := by simp [Nat.mul_comm]

/-- Fubini identity for the degree sum over one distinguished support. -/
private theorem sum_degreeIn_over_support
    {Point Block : Type*} [Fintype Point] [Fintype Block]
    [DecidableEq Point]
    (S : BlockSystem Point Block) (F : Finset Block) (b : Block) :
    (∑ x ∈ S.support b, S.degreeIn F x) =
      ∑ c ∈ F, (S.support b ∩ S.support c).card := by
  classical
  simp only [BlockSystem.degreeIn, Finset.card_eq_sum_ones,
    Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro c hc
  simp

/-- Supports of blocks of size at least three are injective: a common
three-subset invokes uniqueness of the triple owner. -/
private theorem support_injOn_blocksOfSize
    {Point Block : Type*} [Fintype Point] [Fintype Block]
    [DecidableEq Point]
    (S : BlockSystem Point Block) (s : Nat) (hs : 3 ≤ s) :
    Set.InjOn S.support (S.blocksOfSize s : Set Block) := by
  classical
  intro b hb c hc hsupport
  have hbcard : (S.support b).card = s := S.mem_blocksOfSize.mp hb
  obtain ⟨A, hAsub, hAcard⟩ :=
    Finset.exists_subset_card_eq (show 3 ≤ (S.support b).card by omega)
  let K : KSubset Point 3 := ⟨A, hAcard⟩
  have hbOwner : b = S.tripleOwner K := by
    apply S.triple_unique K b
    exact hAsub
  have hcOwner : c = S.tripleOwner K := by
    apply S.triple_unique K c
    intro x hx
    rw [← hsupport]
    exact hAsub hx
  exact hbOwner.trans hcOwner.symm

/-- Equality data forced by five five-blocks on ten points. This is the
moment entrance to the punctured-pentagon design. -/
theorem fiveBlock_puncture_profile
    {Point Block : Type*} [Fintype Point] [Fintype Block]
    [DecidableEq Point]
    (S : BlockSystem Point Block)
    (hPoint : Fintype.card Point = 10)
    (hfive : S.blockCount 5 = 5) :
    (∀ x : Point, S.blockDegree 5 x = 2 ∨ S.blockDegree 5 x = 3) ∧
      ∀ b ∈ S.blocksOfSize 5, ∀ c ∈ S.blocksOfSize 5,
        b ≠ c → (S.support b ∩ S.support c).card = 2 := by
  classical
  let F := S.blocksOfSize 5
  have hF : F.card = 5 := hfive
  have hdegreeCap (x : Point) : S.blockDegree 5 x ≤ 5 := by
    exact (degreeIn_le_card S F x).trans_eq hF
  have hfirst : (∑ x : Point, S.blockDegree 5 x) = 25 := by
    have h := S.block_incidence 5
    rw [hfive] at h
    norm_num at h
    exact h
  have hmoment :
      (∑ x : Point, Nat.choose (S.blockDegree 5 x) 2) ≤ 20 := by
    have h := S.second_moment_le_two_choose F
    change (∑ x : Point, Nat.choose (S.blockDegree 5 x) 2) ≤
      2 * Nat.choose (S.blockCount 5) 2 at h
    rw [hfive] at h
    norm_num [Nat.choose] at h
    exact h
  have hpoint (x : Point) :
      2 * S.blockDegree 5 x ≤ Nat.choose (S.blockDegree 5 x) 2 + 3 := by
    have hx := hdegreeCap x
    interval_cases hd : S.blockDegree 5 x <;>
      norm_num [Nat.choose] at *
  have hlower :
      2 * (∑ x : Point, S.blockDegree 5 x) ≤
        (∑ x : Point, Nat.choose (S.blockDegree 5 x) 2) +
          3 * Fintype.card Point := by
    calc
      2 * (∑ x : Point, S.blockDegree 5 x) =
          ∑ x : Point, 2 * S.blockDegree 5 x := by
            rw [Finset.mul_sum]
      _ ≤ ∑ x : Point,
          (Nat.choose (S.blockDegree 5 x) 2 + 3) :=
        Finset.sum_le_sum fun x _hx => hpoint x
      _ = (∑ x : Point, Nat.choose (S.blockDegree 5 x) 2) +
          3 * Fintype.card Point := by
            simp [Finset.sum_add_distrib, Finset.sum_const, Nat.mul_comm]
  have hmomentEq :
      (∑ x : Point, Nat.choose (S.blockDegree 5 x) 2) = 20 := by
    rw [hfirst, hPoint] at hlower
    omega
  have hsumEq :
      (∑ x : Point, 2 * S.blockDegree 5 x) =
        ∑ x : Point, (Nat.choose (S.blockDegree 5 x) 2 + 3) := by
    simp only [← Finset.mul_sum, Finset.sum_add_distrib,
      Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rw [hfirst, hmomentEq, hPoint]
    norm_num
  have hprofile : ∀ x : Point,
      S.blockDegree 5 x = 2 ∨ S.blockDegree 5 x = 3 := by
    intro x
    have hx := (Finset.sum_eq_sum_iff_of_le
      (fun y (_hy : y ∈ (Finset.univ : Finset Point)) => hpoint y)).mp
        hsumEq x (Finset.mem_univ x)
    have hcap := hdegreeCap x
    interval_cases hd : S.blockDegree 5 x <;>
      norm_num [Nat.choose] at hx <;> omega
  refine ⟨hprofile, ?_⟩
  have hpairTotal :
      (∑ A ∈ F.powersetCard 2, (S.commonSupport A).card) = 20 := by
    rw [← S.binomial_degree_moment F 2]
    exact hmomentEq
  have hconst : (∑ _A ∈ F.powersetCard 2, 2) = 20 := by
    simp [hF, Nat.choose]
  have htotal :
      (∑ A ∈ F.powersetCard 2, (S.commonSupport A).card) =
        ∑ _A ∈ F.powersetCard 2, 2 := hpairTotal.trans hconst.symm
  have htermLe : ∀ A ∈ F.powersetCard 2,
      (S.commonSupport A).card ≤ 2 := by
    intro A hA
    exact S.commonSupport_card_le_two (Finset.mem_powersetCard.mp hA).2
  intro b hb c hc hbc
  have hbcMem : ({b, c} : Finset Block) ∈ F.powersetCard 2 := by
    apply Finset.mem_powersetCard.mpr
    constructor
    · intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact hb
      · exact hc
    · simp [hbc]
  have hterm :=
    (Finset.sum_eq_sum_iff_of_le htermLe).mp htotal {b, c} hbcMem
  rw [S.commonSupport_pair] at hterm
  omega

/-- The canonical support belonging to a block label in the classified
six-by-five design. -/
def sixFiveCanonicalSupport (j : Fin 6) : Finset (Fin 10) :=
  Finset.univ.filter fun i => j ∈ sixFiveCanonicalProfile i

/-- Four-subsets through `p` that respect all five surviving columns after
column `missing` is punctured. -/
def canonicalPuncturedTransversals (p : Fin 10) (missing : Fin 6) :
    Finset (Finset (Fin 10)) :=
  ((Finset.univ : Finset (Fin 10)).powersetCard 4).filter fun Q =>
    p ∈ Q ∧ ∀ j : Fin 6, j ≠ missing →
      (Q ∩ sixFiveCanonicalSupport j).card ≤ 2

/-- Pairwise compatibility of four-block supports. -/
def puncturedTransversalsCompatible (T : Finset (Finset (Fin 10))) : Prop :=
  ∀ Q ∈ T, ∀ R ∈ T, Q ≠ R → (Q ∩ R).card ≤ 2

instance instDecidablePuncturedTransversalsCompatible
    (T : Finset (Finset (Fin 10))) :
    Decidable (puncturedTransversalsCompatible T) := by
  unfold puncturedTransversalsCompatible
  exact Finset.decidableDforallFinset

/-- The fixed punctured-pentagon ledger has no compatible triple. The
calculation expands the canonical ten-row incidence table. It is the Lean
form of the four residual triples `DRT`, `QRS`, `QRT`, `QES`, whose
compatibility graph is a path. -/
private theorem canonicalPuncturedTransversals_no_triple_at_zero
    (missing : Fin 6) (hmissing : missing ∉ sixFiveCanonicalProfile 0) :
    (((canonicalPuncturedTransversals 0 missing).powersetCard 3).filter
      puncturedTransversalsCompatible) = ∅ := by
  fin_cases missing <;> simp [sixFiveCanonicalProfile] at hmissing
  all_goals decide +kernel

private theorem canonicalPuncturedTransversals_no_triple_at_one
    (missing : Fin 6) (hmissing : missing ∉ sixFiveCanonicalProfile 1) :
    (((canonicalPuncturedTransversals 1 missing).powersetCard 3).filter
      puncturedTransversalsCompatible) = ∅ := by
  fin_cases missing <;> simp [sixFiveCanonicalProfile] at hmissing
  all_goals decide +kernel

private theorem canonicalPuncturedTransversals_no_triple_at_two
    (missing : Fin 6) (hmissing : missing ∉ sixFiveCanonicalProfile 2) :
    (((canonicalPuncturedTransversals 2 missing).powersetCard 3).filter
      puncturedTransversalsCompatible) = ∅ := by
  fin_cases missing <;> simp [sixFiveCanonicalProfile] at hmissing
  all_goals decide +kernel

private theorem canonicalPuncturedTransversals_no_triple_at_three
    (missing : Fin 6) (hmissing : missing ∉ sixFiveCanonicalProfile 3) :
    (((canonicalPuncturedTransversals 3 missing).powersetCard 3).filter
      puncturedTransversalsCompatible) = ∅ := by
  fin_cases missing <;> simp [sixFiveCanonicalProfile] at hmissing
  all_goals decide +kernel

private theorem canonicalPuncturedTransversals_no_triple_at_four
    (missing : Fin 6) (hmissing : missing ∉ sixFiveCanonicalProfile 4) :
    (((canonicalPuncturedTransversals 4 missing).powersetCard 3).filter
      puncturedTransversalsCompatible) = ∅ := by
  fin_cases missing <;> simp [sixFiveCanonicalProfile] at hmissing
  all_goals decide +kernel

private theorem canonicalPuncturedTransversals_no_triple_at_five
    (missing : Fin 6) (hmissing : missing ∉ sixFiveCanonicalProfile 5) :
    (((canonicalPuncturedTransversals 5 missing).powersetCard 3).filter
      puncturedTransversalsCompatible) = ∅ := by
  fin_cases missing <;> simp [sixFiveCanonicalProfile] at hmissing
  all_goals decide +kernel

private theorem canonicalPuncturedTransversals_no_triple_at_six
    (missing : Fin 6) (hmissing : missing ∉ sixFiveCanonicalProfile 6) :
    (((canonicalPuncturedTransversals 6 missing).powersetCard 3).filter
      puncturedTransversalsCompatible) = ∅ := by
  fin_cases missing <;> simp [sixFiveCanonicalProfile] at hmissing
  all_goals decide +kernel

private theorem canonicalPuncturedTransversals_no_triple_at_seven
    (missing : Fin 6) (hmissing : missing ∉ sixFiveCanonicalProfile 7) :
    (((canonicalPuncturedTransversals 7 missing).powersetCard 3).filter
      puncturedTransversalsCompatible) = ∅ := by
  fin_cases missing <;> simp [sixFiveCanonicalProfile] at hmissing
  all_goals decide +kernel

private theorem canonicalPuncturedTransversals_no_triple_at_eight
    (missing : Fin 6) (hmissing : missing ∉ sixFiveCanonicalProfile 8) :
    (((canonicalPuncturedTransversals 8 missing).powersetCard 3).filter
      puncturedTransversalsCompatible) = ∅ := by
  fin_cases missing <;> simp [sixFiveCanonicalProfile] at hmissing
  all_goals decide +kernel

private theorem canonicalPuncturedTransversals_no_triple_at_nine
    (missing : Fin 6) (hmissing : missing ∉ sixFiveCanonicalProfile 9) :
    (((canonicalPuncturedTransversals 9 missing).powersetCard 3).filter
      puncturedTransversalsCompatible) = ∅ := by
  fin_cases missing <;> simp [sixFiveCanonicalProfile] at hmissing
  all_goals decide +kernel

theorem canonicalPuncturedTransversals_no_compatible_triple :
    ∀ p : Fin 10, ∀ missing : Fin 6,
      missing ∉ sixFiveCanonicalProfile p →
      (((canonicalPuncturedTransversals p missing).powersetCard 3).filter
        puncturedTransversalsCompatible) = ∅ := by
  intro p missing hmissing
  fin_cases p
  · exact canonicalPuncturedTransversals_no_triple_at_zero missing hmissing
  · exact canonicalPuncturedTransversals_no_triple_at_one missing hmissing
  · exact canonicalPuncturedTransversals_no_triple_at_two missing hmissing
  · exact canonicalPuncturedTransversals_no_triple_at_three missing hmissing
  · exact canonicalPuncturedTransversals_no_triple_at_four missing hmissing
  · exact canonicalPuncturedTransversals_no_triple_at_five missing hmissing
  · exact canonicalPuncturedTransversals_no_triple_at_six missing hmissing
  · exact canonicalPuncturedTransversals_no_triple_at_seven missing hmissing
  · exact canonicalPuncturedTransversals_no_triple_at_eight missing hmissing
  · exact canonicalPuncturedTransversals_no_triple_at_nine missing hmissing

/-- Five five-blocks on ten points allow at most two four-blocks through a
five-degree-three point. Only the finite triple-owner API is used. -/
theorem blockDegree_four_le_two_of_fiveBlock_puncture
    {Point Block : Type*} [Fintype Point] [Fintype Block]
    [DecidableEq Point]
    (S : BlockSystem Point Block)
    (hPoint : Fintype.card Point = 10)
    (hfive : S.blockCount 5 = 5)
    (p : Point) (hp : S.blockDegree 5 p = 3) :
    S.blockDegree 4 p ≤ 2 := by
  classical
  let F := S.blocksOfSize 5
  have hF : F.card = 5 := hfive
  let d : Point → Nat := fun x => S.blockDegree 5 x
  obtain ⟨hprofile, hinterFive⟩ := fiveBlock_puncture_profile S hPoint hfive
  let U : Finset Point := Finset.univ.filter fun x => d x = 2
  have hfirst : (∑ x : Point, d x) = 25 := by
    have h := S.block_incidence 5
    rw [hfive] at h
    norm_num at h
    simpa [d] using h
  have hUcard : U.card = 5 := by
    have h := sum_add_card_filter_eq_three_mul_card
      (Finset.univ : Finset Point) d (fun x _hx => hprofile x)
    change (∑ x : Point, d x) + U.card = 3 * Fintype.card Point at h
    rw [hfirst, hPoint] at h
    omega
  have hUinter : ∀ b ∈ F, (S.support b ∩ U).card = 2 := by
    intro b hb
    have hbcard : (S.support b).card = 5 := S.mem_blocksOfSize.mp hb
    have hsumErase :
        (∑ c ∈ F.erase b, (S.support b ∩ S.support c).card) = 8 := by
      calc
        (∑ c ∈ F.erase b, (S.support b ∩ S.support c).card) =
            ∑ _c ∈ F.erase b, 2 := by
              apply Finset.sum_congr rfl
              intro c hc
              have hcF := (Finset.mem_erase.mp hc).2
              have hbc : b ≠ c := fun h => (Finset.mem_erase.mp hc).1 h.symm
              exact hinterFive b hb c hcF hbc
        _ = 8 := by
              rw [Finset.sum_const, nsmul_eq_mul,
                Finset.card_erase_of_mem hb, hF]
              norm_num
    have hsplit := Finset.sum_erase_add F
      (fun c => (S.support b ∩ S.support c).card) hb
    have hsupportSum :
        (∑ x ∈ S.support b, d x) = 13 := by
      change (∑ x ∈ S.support b, S.degreeIn F x) = 13
      rw [sum_degreeIn_over_support]
      rw [← hsplit]
      simp [hsumErase, hbcard]
    have hfilter := sum_add_card_filter_eq_three_mul_card
      (S.support b) d (fun x _hx => hprofile x)
    rw [hsupportSum, hbcard] at hfilter
    have hfilterCard :
        ((S.support b).filter fun x => d x = 2).card = 2 := by omega
    have heq : S.support b ∩ U =
        (S.support b).filter fun x => d x = 2 := by
      ext x
      simp [U]
    rw [heq, hfilterCard]

  let OldBlock := {b : Block // b ∈ F}
  let AugBlock := Option OldBlock
  let augSupport : AugBlock → Finset Point
    | none => U
    | some b => S.support b.1
  have oldProfileCard (x : Point) :
      ((Finset.univ : Finset OldBlock).filter
        fun b => x ∈ S.support b.1).card = d x := by
    change ((Finset.univ : Finset {b : Block // b ∈ F}).filter
        fun b => x ∈ S.support b.1).card =
      (F.filter fun b => x ∈ S.support b).card
    rw [Finset.univ_eq_attach, Finset.filter_attach']
    simp only [Finset.card_map, Finset.card_attach]
    congr 1
    ext b
    simp
  let D : SixFiveDesign Point AugBlock := by
    classical
    refine
      { support := augSupport
        point_card := hPoint
        block_card := ?_
        support_card := ?_
        profile_card := ?_
        pair_inter_card := ?_ }
    · simp [AugBlock, OldBlock]
      exact hF
    · intro b
      cases b with
      | none => simpa [augSupport] using hUcard
      | some b =>
          simpa [augSupport] using S.mem_blocksOfSize.mp b.2
    · intro x
      rw [Finset.card_eq_sum_ones, Finset.sum_filter]
      change (∑ q : Option OldBlock,
        if x ∈ augSupport q then 1 else 0) = 3
      rw [Fintype.sum_option]
      have holdsum :
          (∑ b : OldBlock, if x ∈ S.support b.1 then 1 else 0) = d x := by
        rw [← oldProfileCard x, Finset.card_eq_sum_ones, Finset.sum_filter]
      rw [holdsum]
      rcases hprofile x with hx | hx <;> simp [augSupport, U, d, hx]
    · intro b c hbc
      cases b with
      | none =>
          cases c with
          | none => exact (hbc rfl).elim
          | some c =>
              simpa [augSupport, Finset.inter_comm] using hUinter c.1 c.2
      | some b =>
          cases c with
          | none => simpa [augSupport] using hUinter b.1 b.2
          | some c =>
              have hne : b.1 ≠ c.1 := by
                intro h
                exact hbc (congrArg some (Subtype.ext h))
              simpa [augSupport] using hinterFive b.1 b.2 c.1 c.2 hne

  obtain ⟨P, B, hcanonical⟩ := D.exists_canonical_labeling
  let pivot : Fin 10 := P.symm p
  let missing : Fin 6 := B.symm (none : AugBlock)
  have hmissingB : B missing = (none : AugBlock) := by
    exact B.apply_symm_apply none
  have hpnotU : p ∉ U := by simp [U, d, hp]
  have hmissing : missing ∉ sixFiveCanonicalProfile pivot := by
    intro hm
    have hm' : missing ∈ D.relabeledProfiles P B pivot := by
      rw [hcanonical pivot]
      exact hm
    have hsupp := (D.mem_relabeledProfiles P B pivot missing).mp hm'
    exact hpnotU (by simpa [pivot, missing, D, augSupport] using hsupp)
  have hcolumn (j : Fin 6) :
      (D.support (B j)).preimage P P.injective.injOn =
        sixFiveCanonicalSupport j := by
    ext i
    rw [Finset.mem_preimage]
    rw [← D.mem_relabeledProfiles P B i j, hcanonical i]
    simp [sixFiveCanonicalSupport]

  let G := (S.blocksOfSize 4).filter fun b => p ∈ S.support b
  change G.card ≤ 2
  by_contra hnot
  have hthree : 3 ≤ G.card := by omega
  obtain ⟨T, hTG, hTcard⟩ := Finset.exists_subset_card_eq hthree
  let pullSupport : Block → Finset (Fin 10) := fun b =>
    (S.support b).preimage P P.injective.injOn
  have hpullCard (b : Block) : (pullSupport b).card = (S.support b).card := by
    exact card_preimage_equiv P (S.support b)
  have hpullInterCard (b c : Block) :
      (pullSupport b ∩ pullSupport c).card =
        (S.support b ∩ S.support c).card := by
    rw [← card_preimage_equiv P (S.support b ∩ S.support c)]
    congr 1
    ext i
    simp [pullSupport]
  have hpullInj : Set.InjOn pullSupport (G : Set Block) := by
    intro b hb c hc heq
    have hsupp : S.support b = S.support c := by
      ext x
      obtain ⟨i, rfl⟩ := P.surjective x
      have hi := Finset.ext_iff.mp heq i
      simpa [pullSupport] using hi
    have hb4 : b ∈ S.blocksOfSize 4 := (Finset.mem_filter.mp hb).1
    have hc4 : c ∈ S.blocksOfSize 4 := (Finset.mem_filter.mp hc).1
    exact support_injOn_blocksOfSize S 4 (by omega) hb4 hc4 hsupp
  let T' := T.image pullSupport
  have hT'card : T'.card = 3 := by
    rw [Finset.card_image_iff.mpr (hpullInj.mono hTG), hTcard]
  have hT'sub : T' ⊆ canonicalPuncturedTransversals pivot missing := by
    intro Q hQ
    obtain ⟨b, hbT, rfl⟩ := Finset.mem_image.mp hQ
    have hbG := hTG hbT
    have hb4 : b ∈ S.blocksOfSize 4 := (Finset.mem_filter.mp hbG).1
    have hpb : p ∈ S.support b := (Finset.mem_filter.mp hbG).2
    apply Finset.mem_filter.mpr
    constructor
    · apply Finset.mem_powersetCard.mpr
      constructor
      · exact Finset.subset_univ _
      · rw [hpullCard]
        exact S.mem_blocksOfSize.mp hb4
    · constructor
      · simpa [pullSupport, pivot] using hpb
      · intro j hj
        have hBj : B j ≠ (none : AugBlock) := by
          intro hnone
          apply hj
          apply B.injective
          exact hnone.trans hmissingB.symm
        cases hbj : B j with
        | none => exact (hBj hbj).elim
        | some old =>
            have hbne : b ≠ old.1 := by
              intro heq
              have hbcard := S.mem_blocksOfSize.mp hb4
              have holdcard := S.mem_blocksOfSize.mp old.2
              rw [heq] at hbcard
              omega
            have hinter := S.distinct_block_inter_card_lt_three hbne
            have hpullColumn :
                (pullSupport b ∩ sixFiveCanonicalSupport j).card =
                  (S.support b ∩ S.support old.1).card := by
              rw [← hcolumn j, hbj]
              change (pullSupport b ∩
                (S.support old.1).preimage P P.injective.injOn).card = _
              exact hpullInterCard b old.1
            rw [hpullColumn]
            omega
  have hcompat : puncturedTransversalsCompatible T' := by
    intro Q hQ R hR hQR
    obtain ⟨b, hbT, rfl⟩ := Finset.mem_image.mp hQ
    obtain ⟨c, hcT, rfl⟩ := Finset.mem_image.mp hR
    have hbc : b ≠ c := by
      intro h
      apply hQR
      simp [h]
    rw [hpullInterCard]
    have hinter := S.distinct_block_inter_card_lt_three hbc
    omega
  have hpower : T' ∈
      (canonicalPuncturedTransversals pivot missing).powersetCard 3 := by
    exact Finset.mem_powersetCard.mpr ⟨hT'sub, hT'card⟩
  have hbad : T' ∈
      (((canonicalPuncturedTransversals pivot missing).powersetCard 3).filter
        puncturedTransversalsCompatible) :=
    Finset.mem_filter.mpr ⟨hpower, hcompat⟩
  rw [canonicalPuncturedTransversals_no_compatible_triple
    pivot missing hmissing] at hbad
  simp at hbad

end Erdos506.Finite
