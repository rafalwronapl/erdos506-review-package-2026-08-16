import Erdos506.Block.RelativeLineCapacity
import Erdos506.Incidence.RadicalAxisCrossBlockPrinciple
import Erdos506.V1.FiniteCaps
import Erdos506.V1.NineFiveArithmetic
import Erdos506.V1.UniversalRows

/-!
# The nine-point branch with a selected five-circle

This file develops the common four-outsider fan around a selected
five-circle.  The only non-incidence input intended for the terminal
concyclic case is the explicit radical-axis cross-block principle.
-/

namespace Erdos506.V1

open Erdos506.Block
open Erdos506.Block.BlockSystem
open Erdos506.Finite
open Erdos506.Incidence
open Erdos506.V3
open Erdos506.V4
open scoped BigOperators

universe u v

section Fan

variable {Point : Type u} {Block : Type v}
  [Fintype Point] [Fintype Block] [DecidableEq Point]

/-- The circle blocks in the outsider fan of a selected base block. -/
noncomputable def nineFiveFanUnion
    (S : BlockSystem Point Block) (g : Block) : Finset Block := by
  classical
  exact (Finset.univ : Finset (BlockOutsider S g)).biUnion
    (circlePencil S g)

/-- Number of outsider fans containing one block. -/
noncomputable def nineFiveFanDegree
    (S : BlockSystem Point Block) (g c : Block) : ℕ := by
  classical
  exact ((Finset.univ : Finset (BlockOutsider S g)).filter
    (fun x => c ∈ circlePencil S g x)).card

/-- The number of failed base-pairs, summed over the four outsiders.  These
are precisely the chord-line incidences in the manuscript. -/
noncomputable def nineFiveR
    (S : BlockSystem Point Block) (g : Block) : ℕ :=
  ∑ x : BlockOutsider S g, (lineBasePairs S g x).card

/-- Line blocks whose trace on the selected five-set is a chord. -/
noncomputable def nineFiveChordLines
    (S : BlockSystem Point Block) (g : Block) : Finset (LineBlock S) := by
  classical
  exact (Finset.univ : Finset (LineBlock S)).filter fun L =>
    (S.support L.1 ∩ S.support g).card = 2

/-- The same manuscript quantity as a first moment over chord lines. -/
noncomputable def nineFiveChordIncidence
    (S : BlockSystem Point Block) (g : Block) : ℕ :=
  ∑ L ∈ nineFiveChordLines S g, (S.support L.1 \ S.support g).card

/-- Fan blocks containing three outsiders.  Under the five-circle cap there
is no fan block containing all four outsiders. -/
noncomputable def nineFiveTripleFanBlocks
    (S : BlockSystem Point Block) (g : Block) : Finset Block := by
  classical
  exact (nineFiveFanUnion S g).filter
    (fun c => (S.support c \ S.support g).card = 3)

/-- Circle blocks other than the base meeting it in at most one point. -/
noncomputable def nineFiveLowCircleBlocks
    (S : BlockSystem Point Block) (g : Block) : Finset Block := by
  classical
  exact (S.blocksOfKind .circle).filter fun c =>
    c ≠ g ∧ (S.support c ∩ S.support g).card ≤ 1

/-- Binomial second moment of outsider-fan membership. -/
noncomputable def nineFivePairMoment
    (S : BlockSystem Point Block) (g : Block) : ℕ := by
  classical
  exact ∑ c ∈ nineFiveFanUnion S g,
    Nat.choose (nineFiveFanDegree S g c) 2

/-- The six unordered pairs of outsiders.  This private index set keeps the
pair-moment saturation argument compact. -/
private noncomputable def nineFiveOutsiderPairs
    (S : BlockSystem Point Block) (g : Block) :
    Finset (Finset (BlockOutsider S g)) :=
  (Finset.univ : Finset (BlockOutsider S g)).powersetCard 2

/-- Number of fan blocks common to every outsider in a finite index set. -/
private noncomputable def nineFivePairCommonCount
    (S : BlockSystem Point Block) (g : Block)
    (A : Finset (BlockOutsider S g)) : ℕ := by
  classical
  exact (((Finset.univ : Finset (BlockOutsider S g)).biUnion
    (circlePencil S g)).filter fun c =>
      ∀ x ∈ A, c ∈ circlePencil S g x).card

/-- The four outsiders, represented as a finite set. -/
noncomputable def nineFiveOutside
    (S : BlockSystem Point Block) (g : Block) : Finset Point :=
  Finset.univ \ S.support g

/-- Circle blocks of relative trace type `(r,t)` with respect to the
selected base. -/
noncomputable def nineFiveCircleType
    (S : BlockSystem Point Block) (g : Block) (r t : ℕ) : Finset Block := by
  classical
  exact (S.blocksOfKind .circle).filter fun c =>
    (S.support c ∩ S.support g).card = r ∧
      (S.support c \ S.support g).card = t

/-- Line blocks of relative trace type `(r,t)` with respect to the selected
base. -/
noncomputable def nineFiveLineType
    (S : BlockSystem Point Block) (g : Block) (r t : ℕ) : Finset Block := by
  classical
  exact (S.blocksOfKind .line).filter fun c =>
    (S.support c ∩ S.support g).card = r ∧
      (S.support c \ S.support g).card = t

/-- Three-subsets wholly supported on the outsiders. -/
noncomputable def nineFiveOutsiderTriples
    (S : BlockSystem Point Block) (g : Block) :
    Finset (KSubset Point 3) := by
  classical
  exact Finset.univ.filter fun A => A.1 ⊆ nineFiveOutside S g

/-- The generalized carriers owned by the outsider triples. -/
noncomputable def nineFiveOutsiderTripleOwners
    (S : BlockSystem Point Block) (g : Block) : Finset Block := by
  classical
  exact (nineFiveOutsiderTriples S g).image S.tripleOwner

/-- The two census classes that can own an outsider triple in general
position.  Bundling the union keeps its classical block equality internal. -/
noncomputable def nineFiveOutsiderTripleTerminalUnion
    (S : BlockSystem Point Block) (g : Block) : Finset Block := by
  classical
  exact nineFiveTripleFanBlocks S g ∪ nineFiveLowCircleBlocks S g

/-- Outsider triples whose owner contains exactly one selected point of the
base circle.  In the exactly-three-collinear equality case these are the
two triple shadows that would have to cover all six outsider pairs. -/
noncomputable def nineFiveSpecialOutsiderTriples
    (S : BlockSystem Point Block) (g : Block) :
    Finset (KSubset Point 3) := by
  classical
  exact (nineFiveOutsiderTriples S g).filter fun A =>
    (S.support (S.tripleOwner A) ∩ S.support g).card = 1

/-- The underlying three-sets of the special outsider triples. -/
noncomputable def nineFiveSpecialOutsiderTripleSupports
    (S : BlockSystem Point Block) (g : Block) :
    Finset (Finset Point) := by
  classical
  exact (nineFiveSpecialOutsiderTriples S g).image Subtype.val

/-- Semantic incidence data for the case in which exactly one of the four
outsider triples is line-owned. -/
structure NineFiveExactlyThreeOutsiders
    (S : BlockSystem Point Block) (g : Block) (Y : KSubset Point 3) : Prop where
  mem_outsiders : Y ∈ nineFiveOutsiderTriples S g
  owner_line : S.kind (S.tripleOwner Y) = .line
  other_owner_circle : ∀ A ∈ nineFiveOutsiderTriples S g,
    A ≠ Y → S.kind (S.tripleOwner A) = .circle

/-- The three circle owners complementary to the unique line-owned outsider
triple. -/
noncomputable def nineFiveExactlyThreeCircleOwners
    (S : BlockSystem Point Block) (g : Block) (Y : KSubset Point 3) :
    Finset Block := by
  classical
  exact ((nineFiveOutsiderTriples S g).erase Y).image S.tripleOwner

/-- A finite-family Fubini identity: choosing an `r`-subset of indices in
whose sets an element lies is the same as choosing the element first. -/
private theorem family_binomial_degree_fubini
    {ι β : Type*} [DecidableEq ι] [DecidableEq β]
    (I : Finset ι) (F : ι → Finset β) (r : ℕ) :
    (∑ A ∈ I.powersetCard r,
        ((I.biUnion F).filter fun b => ∀ i ∈ A, b ∈ F i).card) =
      ∑ b ∈ I.biUnion F,
        Nat.choose ((I.filter fun i => b ∈ F i).card) r := by
  classical
  calc
    (∑ A ∈ I.powersetCard r,
        ((I.biUnion F).filter fun b => ∀ i ∈ A, b ∈ F i).card) =
        ∑ A ∈ I.powersetCard r, ∑ b ∈ I.biUnion F,
          if (∀ i ∈ A, b ∈ F i) then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro A hA
      rw [Finset.card_eq_sum_ones, Finset.sum_filter]
    _ = ∑ b ∈ I.biUnion F, ∑ A ∈ I.powersetCard r,
          if (∀ i ∈ A, b ∈ F i) then 1 else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ b ∈ I.biUnion F,
        ((I.filter fun i => b ∈ F i).powersetCard r).card := by
      apply Finset.sum_congr rfl
      intro b hb
      rw [powersetCard_filter_eq]
      rw [Finset.card_eq_sum_ones, Finset.sum_filter]
    _ = ∑ b ∈ I.biUnion F,
        Nat.choose ((I.filter fun i => b ∈ F i).card) r := by
      apply Finset.sum_congr rfl
      intro b hb
      rw [Finset.card_powersetCard]

/-- Pairwise intersection caps bound the second binomial degree moment of an
arbitrary finite family. -/
private theorem family_pair_moment_le
    {ι β : Type*} [DecidableEq ι] [DecidableEq β]
    (I : Finset ι) (F : ι → Finset β) (h : ℕ)
    (hinter : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → (F i ∩ F j).card ≤ h) :
    (∑ b ∈ I.biUnion F,
        Nat.choose ((I.filter fun i => b ∈ F i).card) 2) ≤
      Nat.choose I.card 2 * h := by
  classical
  have hmoment := family_binomial_degree_fubini I F 2
  rw [← hmoment]
  calc
    (∑ A ∈ I.powersetCard 2,
        ((I.biUnion F).filter fun b => ∀ i ∈ A, b ∈ F i).card) ≤
        ∑ _A ∈ I.powersetCard 2, h := by
      apply Finset.sum_le_sum
      intro A hA
      have hAspec := Finset.mem_powersetCard.mp hA
      obtain ⟨i, j, hij, hAeq⟩ := Finset.card_eq_two.mp hAspec.2
      have hiI : i ∈ I := hAspec.1 (by simp [hAeq])
      have hjI : j ∈ I := hAspec.1 (by simp [hAeq])
      have heq :
          ((I.biUnion F).filter fun b => ∀ k ∈ A, b ∈ F k) =
            F i ∩ F j := by
        ext b
        constructor
        · intro hb
          have hall := (Finset.mem_filter.mp hb).2
          exact Finset.mem_inter.mpr
            ⟨hall i (by simp [hAeq]), hall j (by simp [hAeq])⟩
        · intro hb
          have hbij := Finset.mem_inter.mp hb
          apply Finset.mem_filter.mpr
          refine ⟨Finset.mem_biUnion.mpr ⟨i, hiI, hbij.1⟩, ?_⟩
          intro k hk
          rw [hAeq] at hk
          simp only [Finset.mem_insert, Finset.mem_singleton] at hk
          rcases hk with rfl | rfl
          · exact hbij.1
          · exact hbij.2
      rw [heq]
      exact hinter i hiI j hjI hij
    _ = Nat.choose I.card 2 * h := by
      simp [Finset.card_powersetCard]

/-- If every summand is at most `h` and the sum attains the obvious
cardinality bound, then every summand is exactly `h`. -/
private theorem eq_two_of_sum_eq_two_mul_card_of_le
    {α : Type*} [DecidableEq α]
    (I : Finset α) (f : α → ℕ)
    (hle : ∀ a ∈ I, f a ≤ 2)
    (hsum : (∑ a ∈ I, f a) = I.card * 2) :
    ∀ a ∈ I, f a = 2 := by
  intro a ha
  have hsumAdd :
      (∑ b ∈ I, f b) + (∑ b ∈ I, (2 - f b)) = I.card * 2 := by
    rw [← Finset.sum_add_distrib]
    calc
      (∑ b ∈ I, (f b + (2 - f b))) = ∑ _b ∈ I, 2 := by
        apply Finset.sum_congr rfl
        intro b hb
        have := hle b hb
        omega
      _ = I.card * 2 := by simp
  have hzero : (∑ b ∈ I, (2 - f b)) = 0 := by omega
  have hsingle : 2 - f a ≤ ∑ b ∈ I, (2 - f b) :=
    Finset.single_le_sum (fun b _hb => Nat.zero_le (2 - f b)) ha
  have hfa := hle a ha
  omega

/-- For a two-set of indices, simultaneous family membership is precisely
the intersection of the two indexed sets. -/
private theorem family_pair_filter_eq_inter
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    (I : Finset α) (F : α → Finset β)
    {A : Finset α} (hA : A ∈ I.powersetCard 2) :
    ∃ i j, i ∈ I ∧ j ∈ I ∧ i ≠ j ∧ A = {i, j} ∧
      ((I.biUnion F).filter fun b => ∀ k ∈ A, b ∈ F k) = F i ∩ F j := by
  classical
  have hAspec := Finset.mem_powersetCard.mp hA
  obtain ⟨i, j, hij, hAeq⟩ := Finset.card_eq_two.mp hAspec.2
  refine ⟨i, j, hAspec.1 (by simp [hAeq]), hAspec.1 (by simp [hAeq]),
    hij, hAeq, ?_⟩
  ext b
  constructor
  · intro hb
    have hall := (Finset.mem_filter.mp hb).2
    exact Finset.mem_inter.mpr
      ⟨hall i (by simp [hAeq]), hall j (by simp [hAeq])⟩
  · intro hb
    have hbij := Finset.mem_inter.mp hb
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_biUnion.mpr
      ⟨i, hAspec.1 (by simp [hAeq]), hbij.1⟩, ?_⟩
    intro k hk
    rw [hAeq] at hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hk
    rcases hk with rfl | rfl
    · exact hbij.1
    · exact hbij.2

/-! The equality case is proved once for an opaque finite family.  Keeping
`I` and `F` abstract here prevents the elaborator from normalizing the full
geometric definition of `circlePencil` while checking finite Fubini. -/
private theorem family_pair_inter_card_eq_two_of_card_four_of_moment_eq_twelve
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    (I : Finset α) (F : α → Finset β)
    (hIcard : I.card = 4)
    (hinter : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → (F i ∩ F j).card ≤ 2)
    (hmoment : (∑ b ∈ I.biUnion F,
      Nat.choose ((I.filter fun i => b ∈ F i).card) 2) = 12)
    {x y : α} (hx : x ∈ I) (hy : y ∈ I) (hxy : x ≠ y) :
    (F x ∩ F y).card = 2 := by
  classical
  let J : Finset (Finset α) := I.powersetCard 2
  let q : Finset α → ℕ := fun A =>
    ((I.biUnion F).filter fun b => ∀ i ∈ A, b ∈ F i).card
  have hqle : ∀ A ∈ J, q A ≤ 2 := by
    intro A hA
    have hA' : A ∈ I.powersetCard 2 := by simpa [J] using hA
    obtain ⟨i, j, hi, hj, hij, _hAeq, hfilter⟩ :=
      family_pair_filter_eq_inter I F hA'
    dsimp only [q]
    rw [hfilter]
    exact hinter i hi j hj hij
  have hJcard : J.card = 6 := by
    dsimp only [J]
    rw [Finset.card_powersetCard, hIcard]
    norm_num [Nat.choose]
  have hsumTwelve : (∑ A ∈ J, q A) = 12 := by
    dsimp only [J, q]
    exact (family_binomial_degree_fubini I F 2).trans hmoment
  have hsum : (∑ A ∈ J, q A) = J.card * 2 := by
    rw [hsumTwelve, hJcard]
  have hall := eq_two_of_sum_eq_two_mul_card_of_le J q hqle hsum
  have hpair : ({x, y} : Finset α) ∈ J := by
    dsimp only [J]
    apply Finset.mem_powersetCard.mpr
    refine ⟨?_, Finset.card_pair hxy⟩
    intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl
    · exact hx
    · exact hy
  have hq := hall ({x, y} : Finset α) hpair
  have hfilter :
      ((I.biUnion F).filter fun b =>
        ∀ i ∈ ({x, y} : Finset α), b ∈ F i) = F x ∩ F y := by
    ext b
    constructor
    · intro hb
      have hallb := (Finset.mem_filter.mp hb).2
      exact Finset.mem_inter.mpr
        ⟨hallb x (by simp), hallb y (by simp)⟩
    · intro hb
      have hbxy := Finset.mem_inter.mp hb
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_biUnion.mpr ⟨x, hx, hbxy.1⟩, ?_⟩
      intro i hi
      simp only [Finset.mem_insert, Finset.mem_singleton] at hi
      rcases hi with rfl | rfl
      · exact hbxy.1
      · exact hbxy.2
  dsimp only [q] at hq
  rw [hfilter] at hq
  exact hq

/-- On a literal pair, the packaged common-count is `commonPencils`. -/
private theorem nineFive_pairCommonCount_pair
    (S : BlockSystem Point Block) (g : Block)
    (x y : BlockOutsider S g) :
    nineFivePairCommonCount S g {x, y} =
      (commonPencils S g x y).card := by
  classical
  unfold nineFivePairCommonCount
  apply congrArg Finset.card
  change
    ((Finset.univ : Finset (BlockOutsider S g)).biUnion
        (circlePencil S g)).filter
        (fun c => ∀ z ∈ ({x, y} : Finset (BlockOutsider S g)),
          c ∈ circlePencil S g z) =
      circlePencil S g x ∩ circlePencil S g y
  ext c
  constructor
  · intro hc
    have hallc := (Finset.mem_filter.mp hc).2
    exact Finset.mem_inter.mpr
      ⟨hallc x (by simp), hallc y (by simp)⟩
  · intro hc
    have hc' := Finset.mem_inter.mp hc
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_biUnion.mpr ⟨x, Finset.mem_univ x, hc'.1⟩, ?_⟩
    intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl
    · exact hc'.1
    · exact hc'.2

set_option maxHeartbeats 800000 in
/-- Each outsider-pair summand is bounded by the two-circle common-pencil
cap. -/
private theorem nineFive_pairCommonCount_le_two
    (S : BlockSystem Point Block) (g : Block)
    (hgcard : (S.support g).card = 5)
    (A : Finset (BlockOutsider S g))
    (hA : A ∈ nineFiveOutsiderPairs S g) :
    nineFivePairCommonCount S g A ≤ 2 := by
  classical
  unfold nineFiveOutsiderPairs at hA
  obtain ⟨i, j, _hi, _hj, hij, _hAeq, _hfilter⟩ :=
    family_pair_filter_eq_inter
      (Finset.univ : Finset (BlockOutsider S g)) (circlePencil S g) hA
  rw [_hAeq, nineFive_pairCommonCount_pair]
  have hcap := card_commonPencils_le_half S g i j hij
  rw [hgcard] at hcap
  norm_num at hcap ⊢
  exact hcap

/-- Four outsiders have exactly six unordered pairs. -/
private theorem nineFive_outsiderPairs_card_eq_six
    (S : BlockSystem Point Block) (g : Block)
    (hpoint : Fintype.card Point = 9)
    (hgcard : (S.support g).card = 5) :
    (nineFiveOutsiderPairs S g).card = 6 := by
  classical
  have hout : Fintype.card (BlockOutsider S g) = 4 := by
    rw [Fintype.card_coe, card_blockOutsiders, hpoint, hgcard]
  unfold nineFiveOutsiderPairs
  rw [Finset.card_powersetCard, Finset.card_univ, hout]
  norm_num [Nat.choose]

/-- The four outsiders give at most two failed base-pairs each. -/
theorem nineFiveR_le_eight
    (S : BlockSystem Point Block) (g : Block)
    (hgkind : S.kind g = .circle)
    (hpoint : Fintype.card Point = 9)
    (hgcard : (S.support g).card = 5) :
    nineFiveR S g ≤ 8 := by
  unfold nineFiveR
  calc
    (∑ x : BlockOutsider S g, (lineBasePairs S g x).card) ≤
        ∑ _x : BlockOutsider S g, 2 := by
      exact Finset.sum_le_sum fun x _hx => by
        have h := card_lineBasePairs_le_half_of_base_circle S g hgkind x
        rw [hgcard] at h
        norm_num at h ⊢
        exact h
    _ = 8 := by
      have hout : (blockOutsiders S g).card = 4 := by
        rw [card_blockOutsiders, hpoint, hgcard]
      simp [hout]

/-- The relative line-capacity theorem gives the same numerical cap directly
for the first moment over all chord lines. -/
theorem nineFiveChordIncidence_le_eight
    (S : BlockSystem Point Block) (g : Block)
    (hpoint : Fintype.card Point = 9)
    (hgcard : (S.support g).card = 5) :
    nineFiveChordIncidence S g ≤ 8 := by
  have hcap := S.relative_line_two_one_capacity
    (S.support g) (nineFiveChordLines S g) (by
      intro L hL
      exact (Finset.mem_filter.mp hL).2)
  unfold nineFiveChordIncidence
  rw [hpoint, hgcard] at hcap
  norm_num at hcap ⊢
  exact hcap



/-- At each outsider, the ten base pairs split into circle-fan members and
failed chord-line pairs. -/
theorem nineFive_sum_fan_add_R_eq_forty
    (S : BlockSystem Point Block) (g : Block)
    (hpoint : Fintype.card Point = 9)
    (hgcard : (S.support g).card = 5) :
    (∑ x : BlockOutsider S g, (circlePencil S g x).card) +
      nineFiveR S g = 40 := by
  have hpointwise (x : BlockOutsider S g) :
      (circlePencil S g x).card + (lineBasePairs S g x).card = 10 := by
    rw [card_circlePencil,
      card_circleBasePairs_add_card_lineBasePairs, hgcard]
    norm_num [Nat.choose]
  unfold nineFiveR
  rw [← Finset.sum_add_distrib]
  calc
    (∑ x : BlockOutsider S g,
        ((circlePencil S g x).card + (lineBasePairs S g x).card)) =
        ∑ _x : BlockOutsider S g, 10 := by
      apply Fintype.sum_congr
      exact hpointwise
    _ = 40 := by
      have hout : (blockOutsiders S g).card = 4 := by
        rw [card_blockOutsiders, hpoint, hgcard]
      simp [hout]

/-- Conversely, a circle block meeting the base in exactly two points belongs
to the fan of each outsider on that block. -/
theorem mem_circlePencil_of_circle_of_inter_card_two
    (S : BlockSystem Point Block) (g c : Block)
    (x : BlockOutsider S g)
    (hcircle : S.kind c = .circle)
    (hinter : (S.support c ∩ S.support g).card = 2)
    (hxc : x.1 ∈ S.support c) :
    c ∈ circlePencil S g x := by
  classical
  let u : BlockBasePair S g :=
    ⟨S.support c ∩ S.support g,
      Finset.mem_powersetCard.mpr ⟨Finset.inter_subset_right, hinter⟩⟩
  have htriple : (pencilTriple S g x u).1 ⊆ S.support c := by
    intro z hz
    simp only [pencilTriple, Finset.mem_insert] at hz
    rcases hz with rfl | hz
    · exact hxc
    · exact (Finset.mem_inter.mp hz).1
  have howner : pencilOwner S g x u = c := by
    exact (S.triple_unique (pencilTriple S g x u) c htriple).symm
  apply mem_circlePencil.mpr
  refine ⟨u, ?_, howner⟩
  apply mem_circleBasePairs.mpr
  rw [howner]
  exact hcircle

/-- A block in the fan union is a non-base circle meeting the base in exactly
two points. -/
theorem nineFive_fan_block_spec
    (S : BlockSystem Point Block) (g c : Block)
    (hc : c ∈ nineFiveFanUnion S g) :
    S.kind c = .circle ∧ c ≠ g ∧
      (S.support c ∩ S.support g).card = 2 := by
  classical
  rw [nineFiveFanUnion] at hc
  obtain ⟨x, _hx, hcx⟩ := Finset.mem_biUnion.mp hc
  obtain ⟨u, hu, howner⟩ := mem_circlePencil.mp hcx
  refine ⟨circlePencil_kind S g x hcx, ?_, ?_⟩
  · intro hcg
    exact pencilOwner_ne_base S g x u (howner.trans hcg)
  · rw [← howner, pencilOwner_inter_base S g x u]
    exact (Finset.mem_powersetCard.mp u.2).2

/-- On a fan block, fan degree is exactly the number of its outsider
points. -/
theorem nineFiveFanDegree_eq_outside_card
    (S : BlockSystem Point Block) (g c : Block)
    (hc : c ∈ nineFiveFanUnion S g) :
    nineFiveFanDegree S g c = (S.support c \ S.support g).card := by
  classical
  obtain ⟨hcircle, _hcne, hinter⟩ := nineFive_fan_block_spec S g c hc
  unfold nineFiveFanDegree
  apply Finset.card_bij
      (fun x _hx => x.1)
      (fun x hx => by
        have hfan := (Finset.mem_filter.mp hx).2
        exact Finset.mem_sdiff.mpr
          ⟨outsider_mem_support_of_mem_circlePencil S g x hfan,
            mem_blockOutsiders.mp x.2⟩)
  · intro x hx y hy hxy
    exact Subtype.ext hxy
  · intro p hp
    let x : BlockOutsider S g :=
      ⟨p, mem_blockOutsiders.mpr (Finset.mem_sdiff.mp hp).2⟩
    refine ⟨x, Finset.mem_filter.mpr ⟨Finset.mem_univ x, ?_⟩, rfl⟩
    exact mem_circlePencil_of_circle_of_inter_card_two
      S g c x hcircle hinter (Finset.mem_sdiff.mp hp).1

/-- First-moment Fubini for the outsider fan. -/
theorem nineFive_sum_fan_eq_sum_degree
    (S : BlockSystem Point Block) (g : Block) :
    (∑ x : BlockOutsider S g, (circlePencil S g x).card) =
      ∑ c ∈ nineFiveFanUnion S g, nineFiveFanDegree S g c := by
  classical
  let I : Finset (BlockOutsider S g) := Finset.univ
  let F : BlockOutsider S g → Finset Block := circlePencil S g
  let U : Finset Block := I.biUnion F
  change (∑ x ∈ I, (F x).card) =
    ∑ c ∈ U, (I.filter fun x => c ∈ F x).card
  calc
    (∑ x ∈ I, (F x).card) =
        ∑ x ∈ I, ∑ c ∈ U,
          if c ∈ F x then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro x hx
      have hfilter :
          U.filter (fun c => c ∈ F x) = F x := by
        ext c
        constructor
        · intro hc
          exact (Finset.mem_filter.mp hc).2
        · intro hc
          apply Finset.mem_filter.mpr
          exact ⟨Finset.mem_biUnion.mpr ⟨x, hx, hc⟩, hc⟩
      rw [← Finset.sum_filter, hfilter]
      simp
    _ = ∑ c ∈ U, ∑ x ∈ I,
          if c ∈ F x then 1 else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ c ∈ U, (I.filter fun x => c ∈ F x).card := by
      apply Finset.sum_congr rfl
      intro c hc
      rw [← Finset.sum_filter]
      simp

/-- The failed-pair definition of `R` is exactly the first moment over
chord lines.  This public bridge is shared by the exactly-three and
concyclic scalar rows. -/
theorem nineFiveR_eq_nineFiveChordIncidence
    (S : BlockSystem Point Block) (g : Block)
    (hgkind : S.kind g = .circle)
    (hpoint : Fintype.card Point = 9)
    (hgcard : (S.support g).card = 5) :
    nineFiveR S g = nineFiveChordIncidence S g := by
  classical
  have hpointwise (b : Block) :
      Nat.choose (S.support b ∩ S.support g).card 2 *
          Nat.choose (S.support b \ S.support g).card 1 =
        (if b ∈ nineFiveFanUnion S g then
            (S.support b \ S.support g).card else 0) +
          (if S.kind b = .line ∧
              (S.support b ∩ S.support g).card = 2 then
            (S.support b \ S.support g).card else 0) := by
    cases hkind : S.kind b with
    | line =>
        have hbne : b ≠ g := by
          intro heq
          rw [heq, hgkind] at hkind
          cases hkind
        have hinterLe : (S.support b ∩ S.support g).card ≤ 2 := by
          have := S.distinct_block_inter_card_lt_three hbne
          omega
        have hbnotFan : b ∉ nineFiveFanUnion S g := by
          intro hb
          have := (nineFive_fan_block_spec S g b hb).1
          rw [hkind] at this
          cases this
        interval_cases hinter : (S.support b ∩ S.support g).card <;>
          norm_num [Nat.choose, hkind, hbnotFan, hinter]
    | circle =>
        by_cases hbg : b = g
        · subst b
          have hgnotFan : g ∉ nineFiveFanUnion S g := by
            intro hg
            exact (nineFive_fan_block_spec S g g hg).2.1 rfl
          simp [hgnotFan]
        · have hinterLe : (S.support b ∩ S.support g).card ≤ 2 := by
            have := S.distinct_block_inter_card_lt_three hbg
            omega
          interval_cases hinter : (S.support b ∩ S.support g).card
          · have hbnotFan : b ∉ nineFiveFanUnion S g := by
              intro hb
              have htwo := (nineFive_fan_block_spec S g b hb).2.2
              omega
            norm_num [Nat.choose, hkind, hbnotFan, hinter]
          · have hbnotFan : b ∉ nineFiveFanUnion S g := by
              intro hb
              have htwo := (nineFive_fan_block_spec S g b hb).2.2
              omega
            norm_num [Nat.choose, hkind, hbnotFan, hinter]
          · have hsplit := Finset.card_inter_add_card_sdiff
              (S.support b) (S.support g)
            have hmin := S.circle_min b hkind
            have houtPos : 0 < (S.support b \ S.support g).card := by omega
            obtain ⟨p, hp⟩ := Finset.card_pos.mp houtPos
            let x : BlockOutsider S g :=
              ⟨p, mem_blockOutsiders.mpr (Finset.mem_sdiff.mp hp).2⟩
            have hfan : b ∈ circlePencil S g x :=
              mem_circlePencil_of_circle_of_inter_card_two S g b x
                hkind hinter (Finset.mem_sdiff.mp hp).1
            have hbFan : b ∈ nineFiveFanUnion S g :=
              Finset.mem_biUnion.mpr ⟨x, Finset.mem_univ x, hfan⟩
            simp [hbFan, Nat.choose]
  have hfanAll :
      (∑ b : Block, if b ∈ nineFiveFanUnion S g then
          (S.support b \ S.support g).card else 0) =
        ∑ x : BlockOutsider S g, (circlePencil S g x).card := by
    calc
      _ = ∑ b ∈ nineFiveFanUnion S g,
          (S.support b \ S.support g).card := by
        rw [← Finset.sum_filter]
        simp
      _ = ∑ b ∈ nineFiveFanUnion S g,
          nineFiveFanDegree S g b := by
        apply Finset.sum_congr rfl
        intro b hb
        rw [nineFiveFanDegree_eq_outside_card S g b hb]
      _ = _ := (nineFive_sum_fan_eq_sum_degree S g).symm
  have hlineAll :
      (∑ b : Block, if S.kind b = .line ∧
          (S.support b ∩ S.support g).card = 2 then
            (S.support b \ S.support g).card else 0) =
        nineFiveChordIncidence S g := by
    calc
      _ = ∑ b : Block, if S.kind b = .line then
            (if (S.support b ∩ S.support g).card = 2 then
              (S.support b \ S.support g).card else 0) else 0 := by
        apply Fintype.sum_congr
        intro b
        by_cases hline : S.kind b = .line <;>
          by_cases hinter : (S.support b ∩ S.support g).card = 2 <;>
          simp [hline, hinter]
      _ = ∑ L : LineBlock S,
          if (S.support L.1 ∩ S.support g).card = 2 then
            (S.support L.1 \ S.support g).card else 0 := by
        simpa [BlockSystem.blocksOfKind, Finset.sum_filter, and_comm] using
          (Finset.sum_subtype (p := fun b => S.kind b = .line)
            (S.blocksOfKind .line)
            (fun b : Block => by simp [BlockSystem.blocksOfKind])
            (fun b => if (S.support b ∩ S.support g).card = 2 then
              (S.support b \ S.support g).card else 0))
      _ = nineFiveChordIncidence S g := by
        unfold nineFiveChordIncidence nineFiveChordLines
        rw [Finset.sum_filter]
  have hrelative := S.relative_triple_partition (S.support g) 2 (by omega)
  rw [hpoint, hgcard] at hrelative
  norm_num [Nat.choose] at hrelative
  have htotal :
      (∑ b : Block,
        Nat.choose (S.support b ∩ S.support g).card 2 *
          Nat.choose (S.support b \ S.support g).card 1) =
        (∑ x : BlockOutsider S g, (circlePencil S g x).card) +
          nineFiveChordIncidence S g := by
    calc
      _ = ∑ b : Block,
          ((if b ∈ nineFiveFanUnion S g then
              (S.support b \ S.support g).card else 0) +
            (if S.kind b = .line ∧
                (S.support b ∩ S.support g).card = 2 then
              (S.support b \ S.support g).card else 0)) := by
        apply Fintype.sum_congr
        exact hpointwise
      _ = (∑ b : Block, if b ∈ nineFiveFanUnion S g then
              (S.support b \ S.support g).card else 0) +
            ∑ b : Block, if S.kind b = .line ∧
                (S.support b ∩ S.support g).card = 2 then
              (S.support b \ S.support g).card else 0 := by
        rw [Finset.sum_add_distrib]
      _ = _ := by rw [hfanAll, hlineAll]
  have htotal' :
      (∑ b : Block,
        Nat.choose (S.support b ∩ S.support g).card 2 *
          (S.support b \ S.support g).card) =
        (∑ x : BlockOutsider S g, (circlePencil S g x).card) +
          nineFiveChordIncidence S g := by
    simpa [Nat.choose] using htotal
  rw [htotal'] at hrelative
  have hfanR := nineFive_sum_fan_add_R_eq_forty S g hpoint hgcard
  omega

set_option maxHeartbeats 800000 in
/-- Every outsider pair belongs to at most two common fan circles, so the
second binomial fan moment is at most twelve. -/
theorem nineFivePairMoment_le_twelve
    (S : BlockSystem Point Block) (g : Block)
    (hpoint : Fintype.card Point = 9)
    (hgcard : (S.support g).card = 5) :
    nineFivePairMoment S g ≤ 12 := by
  classical
  unfold nineFivePairMoment
  have hpair := family_pair_moment_le
    (Finset.univ : Finset (BlockOutsider S g)) (circlePencil S g) 2 (by
      intro x _hx y _hy hxy
      change (commonPencils S g x y).card ≤ 2
      have h := card_commonPencils_le_half S g x y hxy
      rw [hgcard] at h
      norm_num at h ⊢
      exact h)
  have hout : (blockOutsiders S g).card = 4 := by
    rw [card_blockOutsiders, hpoint, hgcard]
  change
    (∑ c ∈ (Finset.univ : Finset (BlockOutsider S g)).biUnion
        (circlePencil S g),
      Nat.choose
        (((Finset.univ : Finset (BlockOutsider S g)).filter
          fun x => c ∈ circlePencil S g x).card) 2) ≤ 12
  calc
    _ ≤ Nat.choose
        (Finset.univ : Finset (BlockOutsider S g)).card 2 * 2 := hpair
    _ = 12 := by
      rw [Finset.card_univ, Fintype.card_coe, hout]
      norm_num [Nat.choose]

set_option maxHeartbeats 800000 in
/-- Equality in the pair Bonferroni cap makes every outsider pair lie on
exactly two common fan circles. -/
theorem nineFive_commonPencils_card_eq_two_of_pairMoment_eq_twelve
    (S : BlockSystem Point Block) (g : Block)
    (hpoint : Fintype.card Point = 9)
    (hgcard : (S.support g).card = 5)
    (hmoment : nineFivePairMoment S g = 12)
    (x y : BlockOutsider S g) (hxy : x ≠ y) :
    (commonPencils S g x y).card = 2 := by
  classical
  let I : Finset (BlockOutsider S g) := Finset.univ
  let F : BlockOutsider S g → Finset Block := circlePencil S g
  have hIcard : I.card = 4 := by
    dsimp only [I]
    rw [Finset.card_univ, Fintype.card_coe, card_blockOutsiders,
      hpoint, hgcard]
  have hinter : ∀ i ∈ I, ∀ j ∈ I, i ≠ j →
      (F i ∩ F j).card ≤ 2 := by
    intro i _hi j _hj hij
    dsimp only [F]
    have hcap := card_commonPencils_le_half S g i j hij
    rw [hgcard] at hcap
    norm_num at hcap ⊢
    exact hcap
  have hmoment' :
      (∑ b ∈ I.biUnion F,
        Nat.choose ((I.filter fun i => b ∈ F i).card) 2) = 12 := by
    change nineFivePairMoment S g = 12
    exact hmoment
  have h := family_pair_inter_card_eq_two_of_card_four_of_moment_eq_twelve
    I F hIcard hinter hmoment' (Finset.mem_univ x) (Finset.mem_univ y) hxy
  change (circlePencil S g x ∩ circlePencil S g y).card = 2
  exact h

/-- At equality, the two common fan circles carry two disjoint base pairs. -/
theorem nineFive_commonPencilBasePairs_exact
    (S : BlockSystem Point Block) (g : Block)
    (hpoint : Fintype.card Point = 9)
    (hgcard : (S.support g).card = 5)
    (hmoment : nineFivePairMoment S g = 12)
    (x y : BlockOutsider S g) (hxy : x ≠ y) :
    (commonPencilBasePairs S g x y).card = 2 ∧
      ((commonPencilBasePairs S g x y : Finset (Finset Point)) :
        Set (Finset Point)).PairwiseDisjoint id := by
  constructor
  · rw [card_commonPencilBasePairs,
      nineFive_commonPencils_card_eq_two_of_pairMoment_eq_twelve
        S g hpoint hgcard hmoment x y hxy]
  · exact commonPencilBasePairs_pairwiseDisjoint S g x y hxy

/-- A line through an outsider pair has base trace disjoint from the base
pair of every common fan circle through that outsider pair. -/
private theorem line_trace_disjoint_commonPencilBasePair
    (S : BlockSystem Point Block) (g : Block)
    (L : LineBlock S) (x y : BlockOutsider S g) (hxy : x ≠ y)
    (hxL : x.1 ∈ S.support L.1) (hyL : y.1 ∈ S.support L.1)
    (c : CommonPencilBlock S g x y) :
    Disjoint (S.support L.1 ∩ S.support g)
      (commonPencilBasePair S g c) := by
  classical
  rw [Finset.disjoint_left]
  intro z hzL hzc
  have hcBoth := Finset.mem_inter.mp c.2
  have hxc := outsider_mem_support_of_mem_circlePencil S g x hcBoth.1
  have hyc := outsider_mem_support_of_mem_circlePencil S g y hcBoth.2
  have hzc' : z ∈ S.support c.1 := (Finset.mem_inter.mp hzc).1
  have hzLine : z ∈ S.support L.1 := (Finset.mem_inter.mp hzL).1
  have hzBase : z ∈ S.support g := (Finset.mem_inter.mp hzL).2
  have hblocks : L.1 ≠ c.1 := by
    intro heq
    have hcircle := circlePencil_kind S g x hcBoth.1
    rw [← heq, L.2] at hcircle
    cases hcircle
  have hinter := S.distinct_block_inter_card_lt_three hblocks
  have hxy' : x.1 ≠ y.1 := Subtype.coe_injective.ne hxy
  have hxz : x.1 ≠ z := by
    intro heq
    subst z
    exact (mem_blockOutsiders.mp x.2) hzBase
  have hyz : y.1 ≠ z := by
    intro heq
    subst z
    exact (mem_blockOutsiders.mp y.2) hzBase
  have hsub : ({x.1, y.1, z} : Finset Point) ⊆
      S.support L.1 ∩ S.support c.1 := by
    intro w hw
    simp only [Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with rfl | rfl | rfl
    · exact Finset.mem_inter.mpr ⟨hxL, hxc⟩
    · exact Finset.mem_inter.mpr ⟨hyL, hyc⟩
    · exact Finset.mem_inter.mpr ⟨hzLine, hzc'⟩
  have hcard : ({x.1, y.1, z} : Finset Point).card = 3 := by
    simp [hxy', hxz, hyz]
  have hle := Finset.card_le_card hsub
  omega

/-- Equality in the pair moment rules out a line with two base points and
two outsiders: its base pair would be a third disjoint pair on a five-set. -/
theorem nineFiveLineType_two_two_eq_empty_of_pairMoment_eq_twelve
    (S : BlockSystem Point Block) (g : Block)
    (hpoint : Fintype.card Point = 9)
    (hgcard : (S.support g).card = 5)
    (hmoment : nineFivePairMoment S g = 12) :
    nineFiveLineType S g 2 2 = ∅ := by
  classical
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro L hL
  have hspec := Finset.mem_filter.mp hL
  have hLkind := S.mem_blocksOfKind.mp hspec.1
  have hinside : (S.support L ∩ S.support g).card = 2 := hspec.2.1
  have houtside : (S.support L \ S.support g).card = 2 := hspec.2.2
  obtain ⟨p, q, hpq, houtEq⟩ :=
    Finset.card_eq_two.mp houtside
  have hpMem : p ∈ S.support L \ S.support g := by
    rw [houtEq]
    simp
  have hqMem : q ∈ S.support L \ S.support g := by
    rw [houtEq]
    simp
  have hpOut : p ∉ S.support g := (Finset.mem_sdiff.mp hpMem).2
  have hqOut : q ∉ S.support g := (Finset.mem_sdiff.mp hqMem).2
  let x : BlockOutsider S g :=
    ⟨p, mem_blockOutsiders.mpr hpOut⟩
  let y : BlockOutsider S g :=
    ⟨q, mem_blockOutsiders.mpr hqOut⟩
  have hxy : x ≠ y := by
    intro heq
    exact hpq (congrArg Subtype.val heq)
  have hxL : x.1 ∈ S.support L := (Finset.mem_sdiff.mp hpMem).1
  have hyL : y.1 ∈ S.support L := (Finset.mem_sdiff.mp hqMem).1
  let LB : LineBlock S := ⟨L, hLkind⟩
  let Q : Finset Point := S.support L ∩ S.support g
  have hPexact := nineFive_commonPencilBasePairs_exact
    S g hpoint hgcard hmoment x y hxy
  obtain ⟨A, B, hAB, hPeq⟩ := Finset.card_eq_two.mp hPexact.1
  have hAcard : A.card = 2 := by
    have hA : A ∈ commonPencilBasePairs S g x y := by simp [hPeq]
    rw [commonPencilBasePairs] at hA
    obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hA
    exact commonPencilBasePair_card S g x y c
  have hBcard : B.card = 2 := by
    have hB : B ∈ commonPencilBasePairs S g x y := by simp [hPeq]
    rw [commonPencilBasePairs] at hB
    obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hB
    exact commonPencilBasePair_card S g x y c
  have hABdisj : Disjoint A B := by
    have hpw := hPexact.2
    exact hpw (by simp [hPeq]) (by simp [hPeq]) hAB
  have hQcard : Q.card = 2 := hinside
  have hQAdisj : Disjoint Q A := by
    have hA : A ∈ commonPencilBasePairs S g x y := by simp [hPeq]
    rw [commonPencilBasePairs] at hA
    obtain ⟨c, hc, hAc⟩ := Finset.mem_image.mp hA
    rw [← hAc]
    exact line_trace_disjoint_commonPencilBasePair
      S g LB x y hxy hxL hyL c
  have hQBdisj : Disjoint Q B := by
    have hB : B ∈ commonPencilBasePairs S g x y := by simp [hPeq]
    rw [commonPencilBasePairs] at hB
    obtain ⟨c, hc, hBc⟩ := Finset.mem_image.mp hB
    rw [← hBc]
    exact line_trace_disjoint_commonPencilBasePair
      S g LB x y hxy hxL hyL c
  have hUnionSub : Q ∪ A ∪ B ⊆ S.support g := by
    intro z hz
    rcases Finset.mem_union.mp hz with hz | hzB
    · rcases Finset.mem_union.mp hz with hzQ | hzA
      · exact (Finset.mem_inter.mp hzQ).2
      · have hA : A ∈ commonPencilBasePairs S g x y := by
          simp [hPeq]
        rw [commonPencilBasePairs] at hA
        obtain ⟨c, hc, hAc⟩ := Finset.mem_image.mp hA
        exact (Finset.mem_inter.mp (hAc.symm ▸ hzA)).2
    · have hB : B ∈ commonPencilBasePairs S g x y := by
        simp [hPeq]
      rw [commonPencilBasePairs] at hB
      obtain ⟨c, hc, hBc⟩ := Finset.mem_image.mp hB
      exact (Finset.mem_inter.mp (hBc.symm ▸ hzB)).2
  have hQA : Disjoint Q A := hQAdisj
  have hQAB : Disjoint (Q ∪ A) B := by
    exact Finset.disjoint_union_left.mpr ⟨hQBdisj, hABdisj⟩
  have hUnionCard : (Q ∪ A ∪ B).card = 6 := by
    rw [Finset.card_union_of_disjoint hQAB,
      Finset.card_union_of_disjoint hQA, hQcard, hAcard, hBcard]
  have hle := Finset.card_le_card hUnionSub
  omega

/-- Once equality has removed circle and line types `(1,2)`, every outsider
pair extends through the unused base point to a special three-outsider
owner.  The outside cap `3` is the direct incidence consequence of having
one and only one three-outsider line. -/
theorem nineFive_special_pair_coverage_of_pairMoment_eq_twelve
    (S : BlockSystem Point Block) (g : Block)
    (hpoint : Fintype.card Point = 9)
    (hgcard : (S.support g).card = 5)
    (hmoment : nineFivePairMoment S g = 12)
    (hlineCap : ∀ b, S.kind b = .line → (S.support b).card ≤ 4)
    (houtsideCap : ∀ b, (S.support b \ S.support g).card ≤ 3)
    (hcircleOneTwo : nineFiveCircleType S g 1 2 = ∅)
    (hlineOneTwo : nineFiveLineType S g 1 2 = ∅) :
    ∀ E : Finset Point,
      E ⊆ nineFiveOutside S g → E.card = 2 →
      ∃ A ∈ nineFiveSpecialOutsiderTripleSupports S g, E ⊆ A := by
  classical
  intro E hEX hEcard
  obtain ⟨p, q, hpq, hEeq⟩ := Finset.card_eq_two.mp hEcard
  have hpX : p ∈ nineFiveOutside S g := hEX (by simp [hEeq])
  have hqX : q ∈ nineFiveOutside S g := hEX (by simp [hEeq])
  have hpOut : p ∉ S.support g := (Finset.mem_sdiff.mp hpX).2
  have hqOut : q ∉ S.support g := (Finset.mem_sdiff.mp hqX).2
  let x : BlockOutsider S g := ⟨p, mem_blockOutsiders.mpr hpOut⟩
  let y : BlockOutsider S g := ⟨q, mem_blockOutsiders.mpr hqOut⟩
  have hxy : x ≠ y := by
    intro heq
    exact hpq (congrArg Subtype.val heq)
  have hPexact := nineFive_commonPencilBasePairs_exact
    S g hpoint hgcard hmoment x y hxy
  obtain ⟨A, B, hAB, hPeq⟩ := Finset.card_eq_two.mp hPexact.1
  have hAin : A ∈ commonPencilBasePairs S g x y := by simp [hPeq]
  have hBin : B ∈ commonPencilBasePairs S g x y := by simp [hPeq]
  have hAcard : A.card = 2 := by
    rw [commonPencilBasePairs] at hAin
    obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hAin
    exact commonPencilBasePair_card S g x y c
  have hBcard : B.card = 2 := by
    rw [commonPencilBasePairs] at hBin
    obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hBin
    exact commonPencilBasePair_card S g x y c
  have hAsub : A ⊆ S.support g := by
    rw [commonPencilBasePairs] at hAin
    obtain ⟨c, hc, hAc⟩ := Finset.mem_image.mp hAin
    intro z hz
    exact (Finset.mem_inter.mp (hAc.symm ▸ hz)).2
  have hBsub : B ⊆ S.support g := by
    rw [commonPencilBasePairs] at hBin
    obtain ⟨c, hc, hBc⟩ := Finset.mem_image.mp hBin
    intro z hz
    exact (Finset.mem_inter.mp (hBc.symm ▸ hz)).2
  have hABdisj : Disjoint A B := by
    exact hPexact.2 (by simp [hPeq]) (by simp [hPeq]) hAB
  have hABcard : (A ∪ B).card = 4 := by
    rw [Finset.card_union_of_disjoint hABdisj, hAcard, hBcard]
  have hABsub : A ∪ B ⊆ S.support g := Finset.union_subset hAsub hBsub
  obtain ⟨z, hzG, hzAB⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (show (A ∪ B).card < (S.support g).card by
      omega)
  have hpz : p ≠ z := by
    intro heq
    exact hpOut (heq ▸ hzG)
  have hqz : q ≠ z := by
    intro heq
    exact hqOut (heq ▸ hzG)
  let Tset : Finset Point := {p, q, z}
  have hTcard : Tset.card = 3 := by simp [Tset, hpq, hpz, hqz]
  let T : KSubset Point 3 := ⟨Tset, hTcard⟩
  let d : Block := S.tripleOwner T
  have hTsub : Tset ⊆ S.support d := S.triple_contains T
  have hpD : p ∈ S.support d := hTsub (by simp [Tset])
  have hqD : q ∈ S.support d := hTsub (by simp [Tset])
  have hzD : z ∈ S.support d := hTsub (by simp [Tset])
  have hdne : d ≠ g := by
    intro heq
    exact hpOut (heq ▸ hpD)
  have hinterLe : (S.support d ∩ S.support g).card ≤ 2 := by
    have := S.distinct_block_inter_card_lt_three hdne
    omega
  have hinterPos : 1 ≤ (S.support d ∩ S.support g).card :=
    Finset.one_le_card.mpr ⟨z, Finset.mem_inter.mpr ⟨hzD, hzG⟩⟩
  have hlineTwoTwo :=
    nineFiveLineType_two_two_eq_empty_of_pairMoment_eq_twelve
      S g hpoint hgcard hmoment
  have hinterNeTwo : (S.support d ∩ S.support g).card ≠ 2 := by
    intro hinterEq
    cases hkind : S.kind d with
    | line =>
        have hsplit := Finset.card_inter_add_card_sdiff
          (S.support d) (S.support g)
        have htotalLe := hlineCap d hkind
        have houtLower : 2 ≤ (S.support d \ S.support g).card := by
          have hsub : ({p, q} : Finset Point) ⊆
              S.support d \ S.support g := by
            intro w hw
            simp only [Finset.mem_insert, Finset.mem_singleton] at hw
            rcases hw with rfl | rfl
            · exact Finset.mem_sdiff.mpr ⟨hpD, hpOut⟩
            · exact Finset.mem_sdiff.mpr ⟨hqD, hqOut⟩
          simpa [Finset.card_pair hpq] using Finset.card_le_card hsub
        have houtEq : (S.support d \ S.support g).card = 2 := by omega
        have hdmem : d ∈ nineFiveLineType S g 2 2 :=
          Finset.mem_filter.mpr
            ⟨S.mem_blocksOfKind.mpr hkind, hinterEq, houtEq⟩
        rw [hlineTwoTwo] at hdmem
        exact Finset.notMem_empty d hdmem
    | circle =>
        have hxFan : d ∈ circlePencil S g x :=
          mem_circlePencil_of_circle_of_inter_card_two
            S g d x hkind hinterEq hpD
        have hyFan : d ∈ circlePencil S g y :=
          mem_circlePencil_of_circle_of_inter_card_two
            S g d y hkind hinterEq hqD
        let c : CommonPencilBlock S g x y :=
          ⟨d, Finset.mem_inter.mpr ⟨hxFan, hyFan⟩⟩
        have htraceMem : S.support d ∩ S.support g ∈
            commonPencilBasePairs S g x y := by
          rw [commonPencilBasePairs]
          exact Finset.mem_image.mpr ⟨c, Finset.mem_univ c, rfl⟩
        rw [hPeq] at htraceMem
        have hzTrace : z ∈ S.support d ∩ S.support g :=
          Finset.mem_inter.mpr ⟨hzD, hzG⟩
        simp only [Finset.mem_insert, Finset.mem_singleton] at htraceMem
        rcases htraceMem with htrace | htrace
        · exact hzAB (Finset.mem_union_left B (htrace ▸ hzTrace))
        · exact hzAB (Finset.mem_union_right A (htrace ▸ hzTrace))
  have hinterEq : (S.support d ∩ S.support g).card = 1 := by omega
  have houtLower : 2 ≤ (S.support d \ S.support g).card := by
    have hsub : ({p, q} : Finset Point) ⊆ S.support d \ S.support g := by
      intro w hw
      simp only [Finset.mem_insert, Finset.mem_singleton] at hw
      rcases hw with rfl | rfl
      · exact Finset.mem_sdiff.mpr ⟨hpD, hpOut⟩
      · exact Finset.mem_sdiff.mpr ⟨hqD, hqOut⟩
    simpa [Finset.card_pair hpq] using Finset.card_le_card hsub
  have houtNeTwo : (S.support d \ S.support g).card ≠ 2 := by
    intro houtEq
    cases hkind : S.kind d with
    | line =>
        have hdmem : d ∈ nineFiveLineType S g 1 2 :=
          Finset.mem_filter.mpr
            ⟨S.mem_blocksOfKind.mpr hkind, hinterEq, houtEq⟩
        rw [hlineOneTwo] at hdmem
        exact Finset.notMem_empty d hdmem
    | circle =>
        have hdmem : d ∈ nineFiveCircleType S g 1 2 :=
          Finset.mem_filter.mpr
            ⟨S.mem_blocksOfKind.mpr hkind, hinterEq, houtEq⟩
        rw [hcircleOneTwo] at hdmem
        exact Finset.notMem_empty d hdmem
  have houtEq : (S.support d \ S.support g).card = 3 := by
    have := houtsideCap d
    omega
  let Aout : KSubset Point 3 :=
    ⟨S.support d \ S.support g, houtEq⟩
  have hAoutTrip : Aout ∈ nineFiveOutsiderTriples S g := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ Aout, ?_⟩
    intro w hw
    exact Finset.mem_sdiff.mpr
      ⟨Finset.mem_univ w, (Finset.mem_sdiff.mp hw).2⟩
  have howner : S.tripleOwner Aout = d := by
    exact (S.triple_unique Aout d Finset.sdiff_subset).symm
  have hspecial : Aout ∈ nineFiveSpecialOutsiderTriples S g := by
    apply Finset.mem_filter.mpr
    refine ⟨hAoutTrip, ?_⟩
    rw [howner]
    exact hinterEq
  refine ⟨Aout.1, Finset.mem_image.mpr ⟨Aout, hspecial, rfl⟩, ?_⟩
  rw [hEeq]
  intro w hw
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl
  · exact Finset.mem_sdiff.mpr ⟨hpD, hpOut⟩
  · exact Finset.mem_sdiff.mpr ⟨hqD, hqOut⟩

/-- Under the five-circle cap, every block in the fan union belongs to
between one and three outsider fans. -/
theorem nineFive_fan_degree_bounds
    (S : BlockSystem Point Block) (g c : Block)
    (hcircleCap : ∀ b, S.kind b = .circle → (S.support b).card ≤ 5)
    (hc : c ∈ nineFiveFanUnion S g) :
    1 ≤ nineFiveFanDegree S g c ∧ nineFiveFanDegree S g c ≤ 3 := by
  classical
  obtain ⟨hcircle, _hcne, hinter⟩ := nineFive_fan_block_spec S g c hc
  have hsplit := Finset.card_inter_add_card_sdiff
    (S.support c) (S.support g)
  have hupper : (S.support c \ S.support g).card ≤ 3 := by
    have := hcircleCap c hcircle
    omega
  have hlower : 1 ≤ (S.support c \ S.support g).card := by
    rw [nineFiveFanUnion] at hc
    obtain ⟨x, _hx, hxc⟩ := Finset.mem_biUnion.mp hc
    have hxout : x.1 ∈ S.support c \ S.support g :=
      Finset.mem_sdiff.mpr
        ⟨outsider_mem_support_of_mem_circlePencil S g x hxc,
          mem_blockOutsiders.mp x.2⟩
    exact Finset.one_le_card.mpr ⟨x.1, hxout⟩
  rw [nineFiveFanDegree_eq_outside_card S g c hc]
  exact ⟨hlower, hupper⟩

/-- Exact first/second-moment identity for the four-outsider fan.  The
correction term consists precisely of fan circles through three outsiders. -/
theorem nineFive_fan_moment_identity
    (S : BlockSystem Point Block) (g : Block)
    (hcircleCap : ∀ b, S.kind b = .circle → (S.support b).card ≤ 5) :
    (nineFiveFanUnion S g).card + nineFivePairMoment S g =
      (∑ x : BlockOutsider S g, (circlePencil S g x).card) +
        (nineFiveTripleFanBlocks S g).card := by
  classical
  let U := nineFiveFanUnion S g
  have hpointwise (c : Block) (hc : c ∈ U) :
      1 + Nat.choose (nineFiveFanDegree S g c) 2 =
        nineFiveFanDegree S g c +
          (if (S.support c \ S.support g).card = 3 then 1 else 0) := by
    have hbounds := nineFive_fan_degree_bounds S g c hcircleCap hc
    have hdegree := nineFiveFanDegree_eq_outside_card S g c hc
    rw [hdegree] at hbounds ⊢
    rcases hbounds with ⟨hlower, hupper⟩
    interval_cases h : (S.support c \ S.support g).card <;>
      norm_num [Nat.choose]
  have hsumDegree := nineFive_sum_fan_eq_sum_degree S g
  change U.card + nineFivePairMoment S g =
    (∑ x : BlockOutsider S g, (circlePencil S g x).card) +
      (U.filter fun c => (S.support c \ S.support g).card = 3).card
  calc
    U.card + nineFivePairMoment S g =
        ∑ c ∈ U, (1 + Nat.choose (nineFiveFanDegree S g c) 2) := by
      unfold nineFivePairMoment
      rw [Finset.card_eq_sum_ones, Finset.sum_add_distrib]
    _ = ∑ c ∈ U, (nineFiveFanDegree S g c +
          if (S.support c \ S.support g).card = 3 then 1 else 0) := by
      apply Finset.sum_congr rfl
      intro c hc
      exact hpointwise c hc
    _ = (∑ c ∈ U, nineFiveFanDegree S g c) +
        ∑ c ∈ U,
          if (S.support c \ S.support g).card = 3 then 1 else 0 := by
      rw [Finset.sum_add_distrib]
    _ = (∑ x : BlockOutsider S g, (circlePencil S g x).card) +
        (U.filter fun c =>
          (S.support c \ S.support g).card = 3).card := by
      rw [← hsumDegree]
      rw [Finset.card_eq_sum_ones, Finset.sum_filter]

/-- Bonferroni, made exact by the degree-three correction, gives the
manuscript lower bound for the union of the four outsider fans. -/
theorem nineFive_fan_union_master_lower
    (S : BlockSystem Point Block) (g : Block)
    (hpoint : Fintype.card Point = 9)
    (hgcard : (S.support g).card = 5)
    (hcircleCap : ∀ b, S.kind b = .circle → (S.support b).card ≤ 5) :
    28 + (nineFiveTripleFanBlocks S g).card ≤
      (nineFiveFanUnion S g).card + nineFiveR S g := by
  have hid := nineFive_fan_moment_identity S g hcircleCap
  have hpair := nineFivePairMoment_le_twelve S g hpoint hgcard
  have hfan := nineFive_sum_fan_add_R_eq_forty S g hpoint hgcard
  omega

/-- The base circle, the two-trace fan union, and the circles meeting the
base in at most one point form an exact partition of all circle blocks. -/
theorem nineFive_totalCircleCount_partition
    (S : BlockSystem Point Block) (g : Block)
    (hgkind : S.kind g = .circle) :
    S.totalCircleCount = 1 + (nineFiveFanUnion S g).card +
      (nineFiveLowCircleBlocks S g).card := by
  classical
  let U := nineFiveFanUnion S g
  let V := nineFiveLowCircleBlocks S g
  have hpartition : S.blocksOfKind .circle = insert g (U ∪ V) := by
    ext c
    constructor
    · intro hc
      have hcircle := S.mem_blocksOfKind.mp hc
      by_cases hcg : c = g
      · simp [hcg]
      · have hinterlt := S.distinct_block_inter_card_lt_three hcg
        by_cases hinter : (S.support c ∩ S.support g).card ≤ 1
        · apply Finset.mem_insert_of_mem
          apply Finset.mem_union_right
          exact Finset.mem_filter.mpr ⟨hc, hcg, hinter⟩
        · have hintereq : (S.support c ∩ S.support g).card = 2 := by
            omega
          have hsplit := Finset.card_inter_add_card_sdiff
            (S.support c) (S.support g)
          have hcmin := S.circle_min c hcircle
          have houtpos : 0 < (S.support c \ S.support g).card := by
            omega
          obtain ⟨p, hp⟩ := Finset.card_pos.mp houtpos
          let x : BlockOutsider S g :=
            ⟨p, mem_blockOutsiders.mpr (Finset.mem_sdiff.mp hp).2⟩
          have hcfan : c ∈ circlePencil S g x :=
            mem_circlePencil_of_circle_of_inter_card_two
              S g c x hcircle hintereq (Finset.mem_sdiff.mp hp).1
          apply Finset.mem_insert_of_mem
          apply Finset.mem_union_left
          exact Finset.mem_biUnion.mpr ⟨x, Finset.mem_univ x, hcfan⟩
    · intro hc
      rcases Finset.mem_insert.mp hc with rfl | hc
      · exact S.mem_blocksOfKind.mpr hgkind
      · rcases Finset.mem_union.mp hc with hcU | hcV
        · exact S.mem_blocksOfKind.mpr
            (nineFive_fan_block_spec S g c hcU).1
        · exact (Finset.mem_filter.mp hcV).1
  have hgU : g ∉ U := by
    intro hg
    exact (nineFive_fan_block_spec S g g hg).2.1 rfl
  have hgV : g ∉ V := by
    intro hg
    exact (Finset.mem_filter.mp hg).2.1 rfl
  have hUV : Disjoint U V := by
    rw [Finset.disjoint_left]
    intro c hcU hcV
    have htwo := (nineFive_fan_block_spec S g c hcU).2.2
    have hle := (Finset.mem_filter.mp hcV).2.2
    omega
  change (S.blocksOfKind .circle).card = 1 + U.card + V.card
  rw [hpartition, Finset.card_insert_of_notMem]
  · rw [Finset.card_union_of_disjoint hUV]
    omega
  · simpa using ⟨hgU, hgV⟩

/-- The exact four-outsider master row used by every geometric case. -/
theorem nineFive_master
    (S : BlockSystem Point Block) (g : Block)
    (hpoint : Fintype.card Point = 9)
    (hgkind : S.kind g = .circle)
    (hgcard : (S.support g).card = 5)
    (hcircleCap : ∀ b, S.kind b = .circle → (S.support b).card ≤ 5)
    (hcircles : S.totalCircleCount ≤ 24) :
    5 + (nineFiveTripleFanBlocks S g).card +
        (nineFiveLowCircleBlocks S g).card ≤ nineFiveR S g := by
  have hlower := nineFive_fan_union_master_lower
    S g hpoint hgcard hcircleCap
  have hpartition := nineFive_totalCircleCount_partition S g hgkind
  omega

/-- Exact global form behind the exactly-three-collinear equality case. -/
theorem nineFive_circle_pair_master_identity
    (S : BlockSystem Point Block) (g : Block)
    (hpoint : Fintype.card Point = 9)
    (hgkind : S.kind g = .circle)
    (hgcard : (S.support g).card = 5)
    (hcircleCap : ∀ b, S.kind b = .circle → (S.support b).card ≤ 5) :
    S.totalCircleCount + nineFivePairMoment S g + nineFiveR S g =
      41 + (nineFiveTripleFanBlocks S g).card +
        (nineFiveLowCircleBlocks S g).card := by
  have hmoment := nineFive_fan_moment_identity S g hcircleCap
  have hfan := nineFive_sum_fan_add_R_eq_forty S g hpoint hgcard
  have hpartition := nineFive_totalCircleCount_partition S g hgkind
  omega

/-- Once three outsider-triple circles are known, the common master and
pair Bonferroni cap force equality in every row used by the terminal
pair-shadow argument. -/
theorem nineFive_three_collinear_forced_rows
    (S : BlockSystem Point Block) (g : Block)
    (hpoint : Fintype.card Point = 9)
    (hgkind : S.kind g = .circle)
    (hgcard : (S.support g).card = 5)
    (hcircleCap : ∀ b, S.kind b = .circle → (S.support b).card ≤ 5)
    (hcircles : S.totalCircleCount ≤ 24)
    (hthree : 3 ≤ (nineFiveTripleFanBlocks S g).card +
      (nineFiveLowCircleBlocks S g).card) :
    nineFiveR S g = 8 ∧
      (nineFiveTripleFanBlocks S g).card +
        (nineFiveLowCircleBlocks S g).card = 3 ∧
      nineFivePairMoment S g = 12 ∧ S.totalCircleCount = 24 := by
  have hR := nineFiveR_le_eight S g hgkind hpoint hgcard
  have hmaster := nineFive_master S g hpoint hgkind hgcard
    hcircleCap hcircles
  have hI := nineFivePairMoment_le_twelve S g hpoint hgcard
  have hidentity := nineFive_circle_pair_master_identity
    S g hpoint hgkind hgcard hcircleCap
  have hCeq : S.totalCircleCount + nineFivePairMoment S g = 36 := by
    omega
  exact nine_five_three_collinear_forced_rows hR hthree hmaster hI
    hCeq hcircles

omit [Fintype Point] in
/-- Two distinct three-subsets cannot cover the pair-shadow of a four-set.
This is the exact finite obstruction used at the end of the
exactly-three-collinear case. -/
theorem exists_pair_not_covered_by_two_triples
    {X : Finset Point} {T : Finset (Finset Point)}
    (hTcard : T.card = 2)
    (htriples : ∀ A ∈ T, A ⊆ X ∧ A.card = 3) :
    ∃ E : Finset Point, E ⊆ X ∧ E.card = 2 ∧
      ∀ A ∈ T, ¬ E ⊆ A := by
  classical
  obtain ⟨A, B, hAB, hTeq⟩ := Finset.card_eq_two.mp hTcard
  have hA := htriples A (by simp [hTeq])
  have hB := htriples B (by simp [hTeq])
  obtain ⟨E, hEX, hEcard, hEA, hEB⟩ :=
    exists_pair_not_subset_either_of_ne_of_card_eq
      hA.1 hB.1 (by rw [hA.2, hB.2]) hAB
  refine ⟨E, hEX, hEcard, ?_⟩
  intro C hC
  simp only [hTeq, Finset.mem_insert, Finset.mem_singleton] at hC
  rcases hC with rfl | rfl
  · exact hEA
  · exact hEB

/-- Forgetting the bundled cardinality proof does not identify two special
outsider triples. -/
theorem nineFiveSpecialOutsiderTripleSupports_card
    (S : BlockSystem Point Block) (g : Block) :
    (nineFiveSpecialOutsiderTripleSupports S g).card =
      (nineFiveSpecialOutsiderTriples S g).card := by
  classical
  unfold nineFiveSpecialOutsiderTripleSupports
  rw [Finset.card_image_of_injective _ Subtype.val_injective]

/-- Every member of the special family really is a three-subset of the
four outsiders. -/
theorem nineFiveSpecialOutsiderTripleSupports_spec
    (S : BlockSystem Point Block) (g : Block) :
    ∀ A ∈ nineFiveSpecialOutsiderTripleSupports S g,
      A ⊆ nineFiveOutside S g ∧ A.card = 3 := by
  classical
  intro A hA
  obtain ⟨A', hA', rfl⟩ := Finset.mem_image.mp hA
  have hOut := (Finset.mem_filter.mp
    (Finset.mem_filter.mp hA').1).2
  exact ⟨hOut, A'.2⟩

/-- The final two scalar rows in the exactly-three-collinear case force
the special triple family to have cardinality two.  Here `a` is the number
of circle shadows, `s` records whether the three-outsider line contains a
base point, and `ell` counts the remaining `(1,2)` lines. -/
theorem nineFiveSpecialOutsiderTriples_card_eq_two_of_rows
    (S : BlockSystem Point Block) (g : Block)
    {a s ell : ℕ}
    (hcard : (nineFiveSpecialOutsiderTriples S g).card = a + s)
    (htriple : ell + 3 * a + 3 * s = 6)
    (hline : 3 * ell + 4 * s ≤ 6) :
    (nineFiveSpecialOutsiderTriples S g).card = 2 := by
  omega

/-- Pair-shadow terminal after the forced equality rows: two special
outsider triples cannot own a continuation of every outsider pair. -/
theorem nineFive_three_collinear_pair_shadow_impossible
    (S : BlockSystem Point Block) (g : Block)
    {a s ell : ℕ}
    (hcard : (nineFiveSpecialOutsiderTriples S g).card = a + s)
    (htriple : ell + 3 * a + 3 * s = 6)
    (hline : 3 * ell + 4 * s ≤ 6)
    (hcover : ∀ E : Finset Point,
      E ⊆ nineFiveOutside S g → E.card = 2 →
      ∃ A ∈ nineFiveSpecialOutsiderTripleSupports S g, E ⊆ A) :
    False := by
  have hspecial := nineFiveSpecialOutsiderTriples_card_eq_two_of_rows
    S g hcard htriple hline
  have hsupports :
      (nineFiveSpecialOutsiderTripleSupports S g).card = 2 := by
    rw [nineFiveSpecialOutsiderTripleSupports_card, hspecial]
  obtain ⟨E, hEX, hEcard, hmiss⟩ :=
    exists_pair_not_covered_by_two_triples hsupports
      (nineFiveSpecialOutsiderTripleSupports_spec S g)
  obtain ⟨A, hA, hEA⟩ := hcover E hEX hEcard
  exact hmiss A hA hEA

/-- There are exactly four outsider labels in the selected five-circle
branch. -/
theorem nineFiveOutside_card
    (S : BlockSystem Point Block) (g : Block)
    (hpoint : Fintype.card Point = 9)
    (hgcard : (S.support g).card = 5) :
    (nineFiveOutside S g).card = 4 := by
  unfold nineFiveOutside
  rw [Finset.card_sdiff_of_subset (Finset.subset_univ (S.support g)),
    Finset.card_univ, hpoint, hgcard]

/-- The four outsider labels have four three-subsets. -/
theorem nineFiveOutsiderTriples_card
    (S : BlockSystem Point Block) (g : Block)
    (hpoint : Fintype.card Point = 9)
    (hgcard : (S.support g).card = 5) :
    (nineFiveOutsiderTriples S g).card = 4 := by
  classical
  let X := nineFiveOutside S g
  let T := nineFiveOutsiderTriples S g
  have hTX : T.card = (X.powersetCard 3).card := by
    apply Finset.card_bij (fun A _hA => A.1)
    · intro A hA
      have hspec := Finset.mem_filter.mp hA
      exact Finset.mem_powersetCard.mpr ⟨hspec.2, A.2⟩
    · intro A hA B hB hAB
      exact Subtype.ext hAB
    · intro A hA
      have hspec := Finset.mem_powersetCard.mp hA
      let A' : KSubset Point 3 := ⟨A, hspec.2⟩
      refine ⟨A', ?_, rfl⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ A', hspec.1⟩
  rw [hTX, Finset.card_powersetCard,
    nineFiveOutside_card S g hpoint hgcard]
  norm_num [Nat.choose]

/-- If no circle contains all four outsiders, their circle-owned triples
have four distinct generalized owners. -/
theorem nineFiveOutsiderTripleOwners_card
    (S : BlockSystem Point Block) (g : Block)
    (hpoint : Fintype.card Point = 9)
    (hgcard : (S.support g).card = 5)
    (htripleCircle : ∀ A ∈ nineFiveOutsiderTriples S g,
      S.kind (S.tripleOwner A) = .circle)
    (hnotConcyclic : ∀ c, S.kind c = .circle →
      ¬ nineFiveOutside S g ⊆ S.support c) :
    (nineFiveOutsiderTripleOwners S g).card = 4 := by
  classical
  have hXcard := nineFiveOutside_card S g hpoint hgcard
  have hinj : Set.InjOn S.tripleOwner
      (nineFiveOutsiderTriples S g : Set (KSubset Point 3)) := by
    intro A hA B hB howner
    by_contra hAB
    have hAX : A.1 ⊆ nineFiveOutside S g :=
      (Finset.mem_filter.mp hA).2
    have hBX : B.1 ⊆ nineFiveOutside S g :=
      (Finset.mem_filter.mp hB).2
    have hUnionSub : A.1 ∪ B.1 ⊆ nineFiveOutside S g :=
      Finset.union_subset hAX hBX
    have hUnionCard : (A.1 ∪ B.1).card = 4 := by
      have hAle : A.1.card ≤ (A.1 ∪ B.1).card :=
        Finset.card_le_card Finset.subset_union_left
      have hUle := Finset.card_le_card hUnionSub
      by_contra hnot
      have hUthree : (A.1 ∪ B.1).card ≤ 3 := by omega
      have hAU : A.1 = A.1 ∪ B.1 :=
        Finset.eq_of_subset_of_card_le Finset.subset_union_left (by
          rw [A.2]
          exact hUthree)
      have hBsubA : B.1 ⊆ A.1 := by
        rw [hAU]
        exact Finset.subset_union_right
      have hBA : B.1 = A.1 :=
        Finset.eq_of_subset_of_card_le hBsubA (by rw [A.2, B.2])
      exact hAB (Subtype.ext hBA.symm)
    have hUnion : A.1 ∪ B.1 = nineFiveOutside S g :=
      Finset.eq_of_subset_of_card_le hUnionSub (by
        rw [hXcard, hUnionCard])
    have hsub : nineFiveOutside S g ⊆ S.support (S.tripleOwner A) := by
      rw [← hUnion]
      apply Finset.union_subset
      · exact S.triple_contains A
      · rw [howner]
        exact S.triple_contains B
    exact hnotConcyclic (S.tripleOwner A) (htripleCircle A hA) hsub
  unfold nineFiveOutsiderTripleOwners
  rw [Finset.card_image_iff.mpr hinj,
    nineFiveOutsiderTriples_card S g hpoint hgcard]

/-- The unique line-owned outsider triple prevents a circle from containing
all four outsiders. -/
theorem nineFive_notConcyclic_of_exactlyThree
    (S : BlockSystem Point Block) (g : Block) (Y : KSubset Point 3)
    (hexact : NineFiveExactlyThreeOutsiders S g Y) :
    ∀ c, S.kind c = .circle →
      ¬ nineFiveOutside S g ⊆ S.support c := by
  intro c hcircle hXc
  have hYX : Y.1 ⊆ nineFiveOutside S g :=
    (Finset.mem_filter.mp hexact.mem_outsiders).2
  have hcOwner := S.triple_unique Y c (hYX.trans hXc)
  rw [hcOwner, hexact.owner_line] at hcircle
  cases hcircle

/-- In the exactly-three case no block contains all four outsiders, hence
every block has outsider trace at most three. -/
theorem nineFive_outside_card_le_three_of_exactlyThree
    (S : BlockSystem Point Block) (g : Block) (Y : KSubset Point 3)
    (hpoint : Fintype.card Point = 9)
    (hgcard : (S.support g).card = 5)
    (hexact : NineFiveExactlyThreeOutsiders S g Y) :
    ∀ b, (S.support b \ S.support g).card ≤ 3 := by
  classical
  intro b
  by_contra hnot
  have hXcard := nineFiveOutside_card S g hpoint hgcard
  have houtSub : S.support b \ S.support g ⊆ nineFiveOutside S g := by
    intro p hp
    exact Finset.mem_sdiff.mpr
      ⟨Finset.mem_univ p, (Finset.mem_sdiff.mp hp).2⟩
  have houtCard : (S.support b \ S.support g).card = 4 := by
    have hle := Finset.card_le_card houtSub
    omega
  have houtEq : S.support b \ S.support g = nineFiveOutside S g :=
    Finset.eq_of_subset_of_card_le houtSub (by rw [hXcard, houtCard])
  have hYsub : Y.1 ⊆ S.support b := by
    intro p hp
    have hpX := (Finset.mem_filter.mp hexact.mem_outsiders).2 hp
    exact (Finset.mem_sdiff.mp (houtEq ▸ hpX)).1
  have hbY := S.triple_unique Y b hYsub
  let T := nineFiveOutsiderTriples S g
  have hTcard : T.card = 4 :=
    nineFiveOutsiderTriples_card S g hpoint hgcard
  have hEraseCard : (T.erase Y).card = 3 := by
    rw [Finset.card_erase_of_mem hexact.mem_outsiders, hTcard]
  obtain ⟨A, hA⟩ : (T.erase Y).Nonempty :=
    Finset.card_pos.mp (by omega)
  have hAT : A ∈ T := Finset.mem_of_mem_erase hA
  have hAY : A ≠ Y := Finset.ne_of_mem_erase hA
  have hAsub : A.1 ⊆ S.support b := by
    intro p hp
    have hpX := (Finset.mem_filter.mp hAT).2 hp
    exact (Finset.mem_sdiff.mp (houtEq ▸ hpX)).1
  have hbA := S.triple_unique A b hAsub
  have howners : S.tripleOwner Y = S.tripleOwner A := hbY.symm.trans hbA
  have hcircle := hexact.other_owner_circle A hAT hAY
  rw [← howners, hexact.owner_line] at hcircle
  cases hcircle

/-- A circle-owned outsider triple has its owner in the fan-three/low
terminal union. -/
theorem nineFive_circleOutsiderTripleOwner_mem_terminal
    (S : BlockSystem Point Block) (g : Block) (A : KSubset Point 3)
    (hA : A ∈ nineFiveOutsiderTriples S g)
    (hcircle : S.kind (S.tripleOwner A) = .circle)
    (hcircleCap : ∀ b, S.kind b = .circle → (S.support b).card ≤ 5) :
    S.tripleOwner A ∈ nineFiveOutsiderTripleTerminalUnion S g := by
  classical
  have hAX : A.1 ⊆ nineFiveOutside S g :=
    (Finset.mem_filter.mp hA).2
  have hAout : A.1 ⊆
      S.support (S.tripleOwner A) \ S.support g := by
    intro p hp
    exact Finset.mem_sdiff.mpr
      ⟨S.triple_contains A hp, (Finset.mem_sdiff.mp (hAX hp)).2⟩
  have houtLower : 3 ≤
      (S.support (S.tripleOwner A) \ S.support g).card := by
    have := Finset.card_le_card hAout
    simpa [A.2] using this
  have hne : S.tripleOwner A ≠ g := by
    intro heq
    obtain ⟨p, hp⟩ : A.1.Nonempty := Finset.card_pos.mp (by omega)
    exact (Finset.mem_sdiff.mp (hAout hp)).2
      (heq ▸ S.triple_contains A hp)
  have hinterlt := S.distinct_block_inter_card_lt_three hne
  unfold nineFiveOutsiderTripleTerminalUnion
  by_cases hinter :
      (S.support (S.tripleOwner A) ∩ S.support g).card ≤ 1
  · apply Finset.mem_union_right
    exact Finset.mem_filter.mpr
      ⟨S.mem_blocksOfKind.mpr hcircle, hne, hinter⟩
  · have hintereq :
        (S.support (S.tripleOwner A) ∩ S.support g).card = 2 := by
      omega
    have hsplit := Finset.card_inter_add_card_sdiff
      (S.support (S.tripleOwner A)) (S.support g)
    have houtUpper :
        (S.support (S.tripleOwner A) \ S.support g).card ≤ 3 := by
      have := hcircleCap (S.tripleOwner A) hcircle
      omega
    have houtEq :
        (S.support (S.tripleOwner A) \ S.support g).card = 3 := by
      omega
    obtain ⟨p, hp⟩ := Finset.card_pos.mp (show
      0 < (S.support (S.tripleOwner A) \ S.support g).card by omega)
    let x : BlockOutsider S g :=
      ⟨p, mem_blockOutsiders.mpr (Finset.mem_sdiff.mp hp).2⟩
    have hfan : S.tripleOwner A ∈ circlePencil S g x :=
      mem_circlePencil_of_circle_of_inter_card_two S g
        (S.tripleOwner A) x hcircle hintereq
          (Finset.mem_sdiff.mp hp).1
    apply Finset.mem_union_left
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_biUnion.mpr ⟨x, Finset.mem_univ x, hfan⟩, houtEq⟩

/-- The three non-line outsider triples have three distinct circle owners. -/
theorem nineFiveExactlyThreeCircleOwners_card
    (S : BlockSystem Point Block) (g : Block) (Y : KSubset Point 3)
    (hpoint : Fintype.card Point = 9)
    (hgcard : (S.support g).card = 5)
    (hexact : NineFiveExactlyThreeOutsiders S g Y) :
    (nineFiveExactlyThreeCircleOwners S g Y).card = 3 := by
  classical
  let T := nineFiveOutsiderTriples S g
  let D := T.erase Y
  have hXcard := nineFiveOutside_card S g hpoint hgcard
  have hnotConcyclic := nineFive_notConcyclic_of_exactlyThree S g Y hexact
  have hinj : Set.InjOn S.tripleOwner (D : Set (KSubset Point 3)) := by
    intro A hA B hB howner
    by_contra hAB
    have hAT : A ∈ T := Finset.mem_of_mem_erase hA
    have hBT : B ∈ T := Finset.mem_of_mem_erase hB
    have hAY : A ≠ Y := Finset.ne_of_mem_erase hA
    have hAX : A.1 ⊆ nineFiveOutside S g :=
      (Finset.mem_filter.mp hAT).2
    have hBX : B.1 ⊆ nineFiveOutside S g :=
      (Finset.mem_filter.mp hBT).2
    have hUnionSub : A.1 ∪ B.1 ⊆ nineFiveOutside S g :=
      Finset.union_subset hAX hBX
    have hUnionCard : (A.1 ∪ B.1).card = 4 := by
      have hAle : A.1.card ≤ (A.1 ∪ B.1).card :=
        Finset.card_le_card Finset.subset_union_left
      have hUle := Finset.card_le_card hUnionSub
      by_contra hnot
      have hUthree : (A.1 ∪ B.1).card ≤ 3 := by omega
      have hAU : A.1 = A.1 ∪ B.1 :=
        Finset.eq_of_subset_of_card_le Finset.subset_union_left (by
          rw [A.2]
          exact hUthree)
      have hBsubA : B.1 ⊆ A.1 := by
        rw [hAU]
        exact Finset.subset_union_right
      have hBA : B.1 = A.1 :=
        Finset.eq_of_subset_of_card_le hBsubA (by rw [A.2, B.2])
      exact hAB (Subtype.ext hBA.symm)
    have hUnion : A.1 ∪ B.1 = nineFiveOutside S g :=
      Finset.eq_of_subset_of_card_le hUnionSub (by
        rw [hXcard, hUnionCard])
    have hsub : nineFiveOutside S g ⊆ S.support (S.tripleOwner A) := by
      rw [← hUnion]
      apply Finset.union_subset
      · exact S.triple_contains A
      · rw [howner]
        exact S.triple_contains B
    exact hnotConcyclic (S.tripleOwner A)
      (hexact.other_owner_circle A hAT hAY) hsub
  unfold nineFiveExactlyThreeCircleOwners
  rw [Finset.card_image_iff.mpr hinj,
    Finset.card_erase_of_mem hexact.mem_outsiders,
    nineFiveOutsiderTriples_card S g hpoint hgcard]

/-- The three circle owners inject into the terminal union. -/
theorem nineFiveExactlyThreeCircleOwners_subset_terminal
    (S : BlockSystem Point Block) (g : Block) (Y : KSubset Point 3)
    (hexact : NineFiveExactlyThreeOutsiders S g Y)
    (hcircleCap : ∀ b, S.kind b = .circle → (S.support b).card ≤ 5) :
    nineFiveExactlyThreeCircleOwners S g Y ⊆
      nineFiveOutsiderTripleTerminalUnion S g := by
  classical
  intro c hc
  obtain ⟨A, hA, rfl⟩ := Finset.mem_image.mp hc
  have hAT : A ∈ nineFiveOutsiderTriples S g :=
    Finset.mem_of_mem_erase hA
  have hAY : A ≠ Y := Finset.ne_of_mem_erase hA
  exact nineFive_circleOutsiderTripleOwner_mem_terminal S g A hAT
    (hexact.other_owner_circle A hAT hAY) hcircleCap

/-- The direct geometric exactly-three hypothesis supplies the `3 ≤ H+V`
input of the forced arithmetic rows. -/
theorem nineFive_exactlyThree_three_le_terminal
    (S : BlockSystem Point Block) (g : Block) (Y : KSubset Point 3)
    (hpoint : Fintype.card Point = 9)
    (hgcard : (S.support g).card = 5)
    (hexact : NineFiveExactlyThreeOutsiders S g Y)
    (hcircleCap : ∀ b, S.kind b = .circle → (S.support b).card ≤ 5) :
    3 ≤ (nineFiveTripleFanBlocks S g).card +
      (nineFiveLowCircleBlocks S g).card := by
  have hcard := nineFiveExactlyThreeCircleOwners_card
    S g Y hpoint hgcard hexact
  have hsub := Finset.card_le_card
    (nineFiveExactlyThreeCircleOwners_subset_terminal
      S g Y hexact hcircleCap)
  have hunion : (nineFiveOutsiderTripleTerminalUnion S g).card ≤
      (nineFiveTripleFanBlocks S g).card +
        (nineFiveLowCircleBlocks S g).card := by
    classical
    unfold nineFiveOutsiderTripleTerminalUnion
    exact Finset.card_union_le _ _
  omega

/-- Full forced equality row under the semantic exactly-three incidence
hypothesis. -/
theorem nineFive_exactlyThree_forced_rows
    (S : BlockSystem Point Block) (g : Block) (Y : KSubset Point 3)
    (hpoint : Fintype.card Point = 9)
    (hgkind : S.kind g = .circle)
    (hgcard : (S.support g).card = 5)
    (hcircleCap : ∀ b, S.kind b = .circle → (S.support b).card ≤ 5)
    (hcircles : S.totalCircleCount ≤ 24)
    (hexact : NineFiveExactlyThreeOutsiders S g Y) :
    nineFiveR S g = 8 ∧
      (nineFiveTripleFanBlocks S g).card +
        (nineFiveLowCircleBlocks S g).card = 3 ∧
      nineFivePairMoment S g = 12 ∧ S.totalCircleCount = 24 := by
  apply nineFive_three_collinear_forced_rows S g hpoint hgkind hgcard
    hcircleCap hcircles
  exact nineFive_exactlyThree_three_le_terminal S g Y hpoint hgcard
    hexact hcircleCap

/-- Equality makes the terminal union exactly the three circle owners. -/
theorem nineFiveExactlyThreeCircleOwners_eq_terminal
    (S : BlockSystem Point Block) (g : Block) (Y : KSubset Point 3)
    (hpoint : Fintype.card Point = 9)
    (hgcard : (S.support g).card = 5)
    (hexact : NineFiveExactlyThreeOutsiders S g Y)
    (hcircleCap : ∀ b, S.kind b = .circle → (S.support b).card ≤ 5)
    (hterminal : (nineFiveTripleFanBlocks S g).card +
      (nineFiveLowCircleBlocks S g).card = 3) :
    nineFiveExactlyThreeCircleOwners S g Y =
      nineFiveOutsiderTripleTerminalUnion S g := by
  classical
  have hsub := nineFiveExactlyThreeCircleOwners_subset_terminal
    S g Y hexact hcircleCap
  apply Finset.eq_of_subset_of_card_le hsub
  have howners := nineFiveExactlyThreeCircleOwners_card
    S g Y hpoint hgcard hexact
  have hunion := Finset.card_union_le
    (nineFiveTripleFanBlocks S g) (nineFiveLowCircleBlocks S g)
  unfold nineFiveOutsiderTripleTerminalUnion
  omega

/-- In the exactly-three equality case there is no circle of relative type
`(1,2)`: every terminal circle is one of the three outsider-triple owners. -/
theorem nineFiveCircleType_one_two_eq_empty_of_exactlyThree
    (S : BlockSystem Point Block) (g : Block) (Y : KSubset Point 3)
    (hpoint : Fintype.card Point = 9)
    (hgcard : (S.support g).card = 5)
    (hexact : NineFiveExactlyThreeOutsiders S g Y)
    (hcircleCap : ∀ b, S.kind b = .circle → (S.support b).card ≤ 5)
    (hterminal : (nineFiveTripleFanBlocks S g).card +
      (nineFiveLowCircleBlocks S g).card = 3) :
    nineFiveCircleType S g 1 2 = ∅ := by
  classical
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro c hc
  have hspec := Finset.mem_filter.mp hc
  have hcircle := S.mem_blocksOfKind.mp hspec.1
  have hcne : c ≠ g := by
    intro heq
    rw [heq] at hspec
    simp at hspec
  have hcLow : c ∈ nineFiveLowCircleBlocks S g :=
    Finset.mem_filter.mpr
      ⟨S.mem_blocksOfKind.mpr hcircle, hcne, by omega⟩
  have hcTerminal : c ∈ nineFiveOutsiderTripleTerminalUnion S g := by
    classical
    unfold nineFiveOutsiderTripleTerminalUnion
    exact Finset.mem_union_right _ hcLow
  rw [← nineFiveExactlyThreeCircleOwners_eq_terminal
    S g Y hpoint hgcard hexact hcircleCap hterminal] at hcTerminal
  obtain ⟨A, hA, howner⟩ := Finset.mem_image.mp hcTerminal
  have hAT : A ∈ nineFiveOutsiderTriples S g :=
    Finset.mem_of_mem_erase hA
  have hAX : A.1 ⊆ nineFiveOutside S g :=
    (Finset.mem_filter.mp hAT).2
  have hAout : A.1 ⊆ S.support c \ S.support g := by
    intro p hp
    exact Finset.mem_sdiff.mpr
      ⟨howner ▸ S.triple_contains A hp,
        (Finset.mem_sdiff.mp (hAX hp)).2⟩
  have hle := Finset.card_le_card hAout
  rw [A.2, hspec.2.2] at hle
  omega

/-- The four circle-owned outsider triples all occur either as `(2,3)` fan
circles or among the circles with at most one selected-base point. -/
theorem nineFive_outsiderTripleOwners_subset
    (S : BlockSystem Point Block) (g : Block)
    (hcircleCap : ∀ b, S.kind b = .circle → (S.support b).card ≤ 5)
    (htripleCircle : ∀ A ∈ nineFiveOutsiderTriples S g,
      S.kind (S.tripleOwner A) = .circle) :
    nineFiveOutsiderTripleOwners S g ⊆
      nineFiveOutsiderTripleTerminalUnion S g := by
  classical
  unfold nineFiveOutsiderTripleTerminalUnion
  intro c hc
  obtain ⟨A, hA, rfl⟩ := Finset.mem_image.mp hc
  have hAX : A.1 ⊆ nineFiveOutside S g :=
    (Finset.mem_filter.mp hA).2
  have hcircle := htripleCircle A hA
  have hAout : A.1 ⊆ S.support (S.tripleOwner A) \ S.support g := by
    intro p hp
    exact Finset.mem_sdiff.mpr
      ⟨S.triple_contains A hp,
        (Finset.mem_sdiff.mp (hAX hp)).2⟩
  have houtLower : 3 ≤
      (S.support (S.tripleOwner A) \ S.support g).card := by
    have := Finset.card_le_card hAout
    simpa [A.2] using this
  have hne : S.tripleOwner A ≠ g := by
    intro heq
    obtain ⟨p, hp⟩ : A.1.Nonempty := Finset.card_pos.mp (by omega)
    exact (Finset.mem_sdiff.mp (hAout hp)).2 (heq ▸ S.triple_contains A hp)
  have hinterlt := S.distinct_block_inter_card_lt_three hne
  by_cases hinter :
      (S.support (S.tripleOwner A) ∩ S.support g).card ≤ 1
  · apply Finset.mem_union_right
    exact Finset.mem_filter.mpr
      ⟨S.mem_blocksOfKind.mpr hcircle, hne, hinter⟩
  · have hintereq :
        (S.support (S.tripleOwner A) ∩ S.support g).card = 2 := by
      omega
    have hsplit := Finset.card_inter_add_card_sdiff
      (S.support (S.tripleOwner A)) (S.support g)
    have houtUpper :
        (S.support (S.tripleOwner A) \ S.support g).card ≤ 3 := by
      have := hcircleCap (S.tripleOwner A) hcircle
      omega
    have houtEq :
        (S.support (S.tripleOwner A) \ S.support g).card = 3 := by
      omega
    obtain ⟨p, hp⟩ := Finset.card_pos.mp (show
      0 < (S.support (S.tripleOwner A) \ S.support g).card by omega)
    let x : BlockOutsider S g :=
      ⟨p, mem_blockOutsiders.mpr (Finset.mem_sdiff.mp hp).2⟩
    have hfan : S.tripleOwner A ∈ circlePencil S g x :=
      mem_circlePencil_of_circle_of_inter_card_two S g
        (S.tripleOwner A) x hcircle hintereq
          (Finset.mem_sdiff.mp hp).1
    apply Finset.mem_union_left
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_biUnion.mpr ⟨x, Finset.mem_univ x, hfan⟩, houtEq⟩

/-- Terminal contradiction for outsider general position.  The hypotheses
are the direct incidence meaning of that case: each outsider triple owns a
circle, while no circle contains the full outsider four-set. -/
theorem nineFive_general_position_impossible
    (S : BlockSystem Point Block) (g : Block)
    (hpoint : Fintype.card Point = 9)
    (hgkind : S.kind g = .circle)
    (hgcard : (S.support g).card = 5)
    (hcircleCap : ∀ b, S.kind b = .circle → (S.support b).card ≤ 5)
    (hcircles : S.totalCircleCount ≤ 24)
    (htripleCircle : ∀ A ∈ nineFiveOutsiderTriples S g,
      S.kind (S.tripleOwner A) = .circle)
    (hnotConcyclic : ∀ c, S.kind c = .circle →
      ¬ nineFiveOutside S g ⊆ S.support c) :
    False := by
  have hR := nineFiveR_le_eight S g hgkind hpoint hgcard
  have hmaster := nineFive_master S g hpoint hgkind hgcard
    hcircleCap hcircles
  have howners := nineFiveOutsiderTripleOwners_card S g hpoint hgcard
    htripleCircle hnotConcyclic
  have hsub := nineFive_outsiderTripleOwners_subset S g hcircleCap
    htripleCircle
  have hcardSub := Finset.card_le_card hsub
  have hcardUnion : (nineFiveOutsiderTripleTerminalUnion S g).card ≤
      (nineFiveTripleFanBlocks S g).card +
        (nineFiveLowCircleBlocks S g).card := by
    classical
    unfold nineFiveOutsiderTripleTerminalUnion
    exact Finset.card_union_le _ _
  apply nine_five_general_position_arithmetic hR
    (R := nineFiveR S g)
    (h := (nineFiveTripleFanBlocks S g).card +
      (nineFiveLowCircleBlocks S g).card)
  · omega
  · simpa [Nat.add_assoc] using hmaster

/-- Two line blocks containing two common labels coincide. -/
private theorem line_eq_of_two_le_inter
    (S : BlockSystem Point Block) {b c : Block}
    (hb : S.kind b = .line) (hc : S.kind c = .line)
    (htwo : 2 ≤ (S.support b ∩ S.support c).card) :
    b = c := by
  by_contra hne
  let b' : LineBlock S := ⟨b, hb⟩
  let c' : LineBlock S := ⟨c, hc⟩
  have hne' : b' ≠ c' := by
    intro heq
    exact hne (congrArg Subtype.val heq)
  have hlt := S.distinct_line_inter_card_lt_two hne'
  exact (not_lt_of_ge htwo) hlt

/-- Terminal contradiction when all four outsiders lie on one line.  The
line-card hypothesis is the direct numerical consequence of the rich-line
cap in the nine-point counterexample. -/
theorem nineFive_four_collinear_impossible
    (S : BlockSystem Point Block) (g ell : Block)
    (hpoint : Fintype.card Point = 9)
    (hgkind : S.kind g = .circle)
    (hgcard : (S.support g).card = 5)
    (hcircleCap : ∀ b, S.kind b = .circle → (S.support b).card ≤ 5)
    (hcircles : S.totalCircleCount ≤ 24)
    (hellkind : S.kind ell = .line)
    (hXell : nineFiveOutside S g ⊆ S.support ell)
    (hellcard : (S.support ell).card ≤ 4) :
    False := by
  classical
  let X := nineFiveOutside S g
  let A := nineFiveCircleType S g 1 2
  let B := nineFiveCircleType S g 2 2
  let U := nineFiveFanUnion S g
  let H := nineFiveTripleFanBlocks S g
  let V := nineFiveLowCircleBlocks S g
  have hXcard : X.card = 4 := nineFiveOutside_card S g hpoint hgcard
  have hXeq : X = S.support ell :=
    Finset.eq_of_subset_of_card_le hXell (by
      rw [hXcard]
      exact hellcard)
  have hellInside : (S.support ell ∩ S.support g).card = 0 := by
    rw [← hXeq]
    simp [X, nineFiveOutside]
  have houtSubInter (c : Block) :
      S.support c \ S.support g ⊆ S.support c ∩ S.support ell := by
    intro p hp
    exact Finset.mem_inter.mpr ⟨(Finset.mem_sdiff.mp hp).1,
      hXell (Finset.mem_sdiff.mpr
        ⟨Finset.mem_univ p, (Finset.mem_sdiff.mp hp).2⟩)⟩
  have hcircleOutside (c : Block) (hc : S.kind c = .circle) :
      (S.support c \ S.support g).card ≤ 2 := by
    have hcell : c ≠ ell := by
      intro heq
      rw [heq, hellkind] at hc
      cases hc
    have hinter := S.distinct_block_inter_card_lt_three hcell
    have hle := Finset.card_le_card (houtSubInter c)
    omega
  have hlineOfOutsidePair (c : Block) (hc : S.kind c = .line)
      (htwo : 2 ≤ (S.support c \ S.support g).card) : c = ell := by
    apply line_eq_of_two_le_inter S hc hellkind
    exact htwo.trans (Finset.card_le_card (houtSubInter c))
  have hweight (c : Block) :
      Nat.choose (S.support c ∩ S.support g).card 1 *
          Nat.choose (S.support c \ S.support g).card 2 =
        (if c ∈ A then 1 else 0) + (if c ∈ B then 2 else 0) := by
    cases hkind : S.kind c with
    | line =>
        by_cases hout : 2 ≤ (S.support c \ S.support g).card
        · have hcell := hlineOfOutsidePair c hkind hout
          have hin : (S.support c ∩ S.support g).card = 0 := by
            rw [hcell]
            exact hellInside
          simp [A, B, nineFiveCircleType, hkind, hin]
        · have hout' : (S.support c \ S.support g).card < 2 := by omega
          have hchoose : Nat.choose (S.support c \ S.support g).card 2 = 0 :=
            Nat.choose_eq_zero_of_lt hout'
          simp [A, B, nineFiveCircleType, hkind, hchoose]
    | circle =>
        have houtLe := hcircleOutside c hkind
        by_cases hout : 2 ≤ (S.support c \ S.support g).card
        · have houtEq : (S.support c \ S.support g).card = 2 := by omega
          have hcne : c ≠ g := by
            intro heq
            rw [heq] at houtEq
            simp at houtEq
          have hinLe : (S.support c ∩ S.support g).card ≤ 2 := by
            have := S.distinct_block_inter_card_lt_three hcne
            omega
          interval_cases hin : (S.support c ∩ S.support g).card <;>
            norm_num [A, B, nineFiveCircleType, hkind, houtEq,
              hin, Nat.choose]
        · have hout' : (S.support c \ S.support g).card < 2 := by omega
          have hchoose : Nat.choose (S.support c \ S.support g).card 2 = 0 :=
            Nat.choose_eq_zero_of_lt hout'
          have houtNe : (S.support c \ S.support g).card ≠ 2 := by omega
          simp [A, B, nineFiveCircleType, hkind, hchoose, houtNe]
  have hrelative := S.relative_triple_partition (S.support g) 1 (by omega)
  rw [hpoint, hgcard] at hrelative
  norm_num [Nat.choose] at hrelative
  have hrelativeSum :
      (∑ c : Block,
        Nat.choose (S.support c ∩ S.support g).card 1 *
          Nat.choose (S.support c \ S.support g).card 2) =
        A.card + 2 * B.card := by
    calc
      _ = ∑ c : Block,
          ((if c ∈ A then 1 else 0) + (if c ∈ B then 2 else 0)) := by
        apply Fintype.sum_congr
        exact hweight
      _ = (∑ c : Block, if c ∈ A then 1 else 0) +
          ∑ c : Block, if c ∈ B then 2 else 0 := by
        rw [Finset.sum_add_distrib]
      _ = A.card + 2 * B.card := by simp [Nat.mul_comm]
  have hrelativeSum' :
      (∑ c : Block, (S.support c ∩ S.support g).card *
          Nat.choose (S.support c \ S.support g).card 2) =
        A.card + 2 * B.card := by
    simpa [Nat.choose] using hrelativeSum
  rw [hrelativeSum'] at hrelative
  have hBcapRaw := S.relative_two_two_capacity (S.support g) B (by
    intro c hc
    exact (Finset.mem_filter.mp hc).2.1)
  have hBsum :
      (∑ c ∈ B, Nat.choose (S.support c \ S.support g).card 2) =
        B.card := by
    rw [Finset.card_eq_sum_ones]
    apply Finset.sum_congr rfl
    intro c hc
    have hout := (Finset.mem_filter.mp hc).2.2
    norm_num [hout, Nat.choose]
  rw [hBsum, hpoint, hgcard] at hBcapRaw
  norm_num [Nat.choose] at hBcapRaw
  have hHzero : H.card = 0 := by
    apply Finset.card_eq_zero.mpr
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro c hc
    have hspec := nineFive_fan_block_spec S g c (Finset.mem_filter.mp hc).1
    have hout := (Finset.mem_filter.mp hc).2
    have hcell : c ≠ ell := by
      intro heq
      rw [heq, hellkind] at hspec
      cases hspec.1
    have hinter := S.distinct_block_inter_card_lt_three hcell
    have hle := Finset.card_le_card (houtSubInter c)
    omega
  have hVeqA : V = A := by
    ext c
    constructor
    · intro hc
      have hspec := Finset.mem_filter.mp hc
      have hcircle := S.mem_blocksOfKind.mp hspec.1
      have houtLe := hcircleOutside c hcircle
      have hsplit := Finset.card_inter_add_card_sdiff
        (S.support c) (S.support g)
      have hmin := S.circle_min c hcircle
      have hinEq : (S.support c ∩ S.support g).card = 1 := by omega
      have houtEq : (S.support c \ S.support g).card = 2 := by omega
      exact Finset.mem_filter.mpr
        ⟨S.mem_blocksOfKind.mpr hcircle, hinEq, houtEq⟩
    · intro hc
      have hspec := Finset.mem_filter.mp hc
      have hcircle := S.mem_blocksOfKind.mp hspec.1
      have hcne : c ≠ g := by
        intro heq
        rw [heq] at hspec
        simp at hspec
      exact Finset.mem_filter.mpr
        ⟨S.mem_blocksOfKind.mpr hcircle, hcne, by omega⟩
  have hUfilterB :
      U.filter (fun c => (S.support c \ S.support g).card = 2) = B := by
    ext c
    constructor
    · intro hc
      have hc' := Finset.mem_filter.mp hc
      have hspec := nineFive_fan_block_spec S g c hc'.1
      exact Finset.mem_filter.mpr
        ⟨S.mem_blocksOfKind.mpr hspec.1, hspec.2.2, hc'.2⟩
    · intro hc
      have hspec := Finset.mem_filter.mp hc
      have hcircle := S.mem_blocksOfKind.mp hspec.1
      obtain ⟨p, hp⟩ := Finset.card_pos.mp (show
        0 < (S.support c \ S.support g).card by omega)
      let x : BlockOutsider S g :=
        ⟨p, mem_blockOutsiders.mpr (Finset.mem_sdiff.mp hp).2⟩
      have hfan := mem_circlePencil_of_circle_of_inter_card_two
        S g c x hcircle hspec.2.1 (Finset.mem_sdiff.mp hp).1
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_biUnion.mpr ⟨x, Finset.mem_univ x, hfan⟩,
          hspec.2.2⟩
  have hPairEqB : nineFivePairMoment S g = B.card := by
    unfold nineFivePairMoment
    calc
      (∑ c ∈ U, Nat.choose (nineFiveFanDegree S g c) 2) =
          ∑ c ∈ U,
            if (S.support c \ S.support g).card = 2 then 1 else 0 := by
        apply Finset.sum_congr rfl
        intro c hc
        have hdegree := nineFiveFanDegree_eq_outside_card S g c hc
        have houtLe := hcircleOutside c
          (nineFive_fan_block_spec S g c hc).1
        have houtPos := (nineFive_fan_degree_bounds S g c hcircleCap hc).1
        rw [hdegree] at houtPos ⊢
        interval_cases hout : (S.support c \ S.support g).card <;>
          norm_num [Nat.choose]
      _ = (U.filter fun c =>
          (S.support c \ S.support g).card = 2).card := by
        rw [Finset.card_eq_sum_ones, Finset.sum_filter]
      _ = B.card := congrArg Finset.card hUfilterB
  have hmoment := nineFive_fan_moment_identity S g hcircleCap
  have hfanR := nineFive_sum_fan_add_R_eq_forty S g hpoint hgcard
  have hURB : U.card + B.card + nineFiveR S g = 40 := by
    have hmoment' : U.card + B.card =
        (∑ x : BlockOutsider S g, (circlePencil S g x).card) + H.card := by
      simpa [U, H, hPairEqB] using hmoment
    rw [hHzero] at hmoment'
    omega
  have hpartition := nineFive_totalCircleCount_partition S g hgkind
  have hpartition' : S.totalCircleCount = 1 + U.card + V.card := by
    simpa [U, V] using hpartition
  have hR := nineFiveR_le_eight S g hgkind hpoint hgcard
  have hUsub : U.card = 40 - nineFiveR S g - B.card := by omega
  apply nine_five_four_collinear_arithmetic
    (R := nineFiveR S g) (a := A.card) (b := B.card)
      (C := S.totalCircleCount)
  · exact hR
  · exact hrelative
  · exact hBcapRaw
  · omega
  · rw [hUsub, hVeqA] at hpartition'
    exact hpartition'
  · exact hcircles

/-- Summing a block indicator over the line subtype counts the indicated
line blocks. -/
private theorem nineFive_sum_line_indicator_eq_card
    [DecidableEq Block]
    (S : BlockSystem Point Block) (F : Finset Block)
    (hline : ∀ b ∈ F, S.kind b = .line) :
    (∑ L : LineBlock S, if L.1 ∈ F then 1 else 0) = F.card := by
  classical
  calc
    (∑ L : LineBlock S, if L.1 ∈ F then 1 else 0) =
        ((Finset.univ : Finset (LineBlock S)).filter fun L =>
          L.1 ∈ F).card := by
      rw [Finset.card_eq_sum_ones, Finset.sum_filter]
    _ = F.card := by
      apply Finset.card_bij (fun L _hL => L.1)
      · intro L hL
        exact (Finset.mem_filter.mp hL).2
      · intro L hL K hK hLK
        exact Subtype.ext hLK
      · intro b hb
        let L : LineBlock S := ⟨b, hline b hb⟩
        exact ⟨L, Finset.mem_filter.mpr ⟨Finset.mem_univ L, hb⟩, rfl⟩

set_option maxHeartbeats 1600000 in
set_option linter.unnecessarySeqFocus false in
/-- Terminal contradiction when exactly one outsider triple is line-owned.
The hypotheses are precisely the finite caps and the Melchior global row
available in a nine-point counterexample. -/
theorem nineFive_exactlyThree_impossible
    (S : BlockSystem Point Block) (g : Block) (Y : KSubset Point 3)
    (hpoint : Fintype.card Point = 9)
    (hgkind : S.kind g = .circle)
    (hgcard : (S.support g).card = 5)
    (hlineCap : ∀ b, S.kind b = .line → (S.support b).card ≤ 4)
    (hcircleCap : ∀ b, S.kind b = .circle → (S.support b).card ≤ 5)
    (hcircles : S.totalCircleCount ≤ 24)
    (hglobal : S.globalLineRow ≤ 33)
    (hexact : NineFiveExactlyThreeOutsiders S g Y) :
    False := by
  classical
  let U := nineFiveFanUnion S g
  let C12 := nineFiveCircleType S g 1 2
  let C13 := nineFiveCircleType S g 1 3
  let L12 := nineFiveLineType S g 1 2
  let L13 := nineFiveLineType S g 1 3
  let U21 := nineFiveLineType S g 2 1
  let V22 := nineFiveLineType S g 2 2
  let Z03 := nineFiveLineType S g 0 3
  let T := nineFiveSpecialOutsiderTriples S g
  have houtsideCap := nineFive_outside_card_le_three_of_exactlyThree
    S g Y hpoint hgcard hexact
  obtain ⟨hR, hterminal, hmoment, _hcircleEq⟩ :=
    nineFive_exactlyThree_forced_rows S g Y hpoint hgkind hgcard
      hcircleCap hcircles hexact
  have hcircleOneTwo :=
    nineFiveCircleType_one_two_eq_empty_of_exactlyThree
      S g Y hpoint hgcard hexact hcircleCap hterminal
  have hlineTwoTwo :=
    nineFiveLineType_two_two_eq_empty_of_pairMoment_eq_twelve
      S g hpoint hgcard hmoment
  have hinterBaseLe (c : Block) (hcne : c ≠ g) :
      (S.support c ∩ S.support g).card ≤ 2 := by
    have hlt := S.distinct_block_inter_card_lt_three hcne
    omega

  have hSpecialTrace (A : KSubset Point 3) (hA : A ∈ T) :
      S.support (S.tripleOwner A) \ S.support g = A.1 := by
    have hAT : A ∈ nineFiveOutsiderTriples S g :=
      (Finset.mem_filter.mp hA).1
    have hAX : A.1 ⊆ nineFiveOutside S g :=
      (Finset.mem_filter.mp hAT).2
    have hsub : A.1 ⊆
        S.support (S.tripleOwner A) \ S.support g := by
      intro p hp
      exact Finset.mem_sdiff.mpr
        ⟨S.triple_contains A hp, (Finset.mem_sdiff.mp (hAX hp)).2⟩
    have hle := houtsideCap (S.tripleOwner A)
    have heq : A.1 = S.support (S.tripleOwner A) \ S.support g :=
      Finset.eq_of_subset_of_card_le hsub (by simpa [A.2] using hle)
    exact heq.symm
  have hSpecialUnionCard : T.card = (C13 ∪ L13).card := by
    apply Finset.card_bij (fun A _hA => S.tripleOwner A)
    · intro A hA
      have hinter := (Finset.mem_filter.mp hA).2
      have hout :
          (S.support (S.tripleOwner A) \ S.support g).card = 3 := by
        rw [hSpecialTrace A hA, A.2]
      cases hkind : S.kind (S.tripleOwner A) with
      | line =>
          apply Finset.mem_union_right
          exact Finset.mem_filter.mpr
            ⟨S.mem_blocksOfKind.mpr hkind, hinter, hout⟩
      | circle =>
          apply Finset.mem_union_left
          exact Finset.mem_filter.mpr
            ⟨S.mem_blocksOfKind.mpr hkind, hinter, hout⟩
    · intro A hA B hB howner
      apply Subtype.ext
      rw [← hSpecialTrace A hA, ← hSpecialTrace B hB, howner]
    · intro c hc
      rcases Finset.mem_union.mp hc with hc | hc
      · have hspec := Finset.mem_filter.mp hc
        let A : KSubset Point 3 :=
          ⟨S.support c \ S.support g, hspec.2.2⟩
        have hAT : A ∈ nineFiveOutsiderTriples S g := by
          apply Finset.mem_filter.mpr
          refine ⟨Finset.mem_univ A, ?_⟩
          intro p hp
          exact Finset.mem_sdiff.mpr
            ⟨Finset.mem_univ p, (Finset.mem_sdiff.mp hp).2⟩
        have howner : S.tripleOwner A = c :=
          (S.triple_unique A c Finset.sdiff_subset).symm
        have hA : A ∈ T := by
          apply Finset.mem_filter.mpr
          refine ⟨hAT, ?_⟩
          rw [howner]
          exact hspec.2.1
        exact ⟨A, hA, howner⟩
      · have hspec := Finset.mem_filter.mp hc
        let A : KSubset Point 3 :=
          ⟨S.support c \ S.support g, hspec.2.2⟩
        have hAT : A ∈ nineFiveOutsiderTriples S g := by
          apply Finset.mem_filter.mpr
          refine ⟨Finset.mem_univ A, ?_⟩
          intro p hp
          exact Finset.mem_sdiff.mpr
            ⟨Finset.mem_univ p, (Finset.mem_sdiff.mp hp).2⟩
        have howner : S.tripleOwner A = c :=
          (S.triple_unique A c Finset.sdiff_subset).symm
        have hA : A ∈ T := by
          apply Finset.mem_filter.mpr
          refine ⟨hAT, ?_⟩
          rw [howner]
          exact hspec.2.1
        exact ⟨A, hA, howner⟩
  have hC13L13disj : Disjoint C13 L13 := by
    rw [Finset.disjoint_left]
    intro c hcC hcL
    have hcKind := S.mem_blocksOfKind.mp (Finset.mem_filter.mp hcC).1
    have hlKind := S.mem_blocksOfKind.mp (Finset.mem_filter.mp hcL).1
    rw [hcKind] at hlKind
    cases hlKind
  have hcard : T.card = C13.card + L13.card := by
    rw [hSpecialUnionCard, Finset.card_union_of_disjoint hC13L13disj]

  have hYoutSub : Y.1 ⊆
      S.support (S.tripleOwner Y) \ S.support g := by
    have hYX : Y.1 ⊆ nineFiveOutside S g :=
      (Finset.mem_filter.mp hexact.mem_outsiders).2
    intro p hp
    exact Finset.mem_sdiff.mpr
      ⟨S.triple_contains Y hp, (Finset.mem_sdiff.mp (hYX hp)).2⟩
  have hYoutEq :
      S.support (S.tripleOwner Y) \ S.support g = Y.1 := by
    have hle := houtsideCap (S.tripleOwner Y)
    have heq : Y.1 =
        S.support (S.tripleOwner Y) \ S.support g :=
      Finset.eq_of_subset_of_card_le hYoutSub (by simpa [Y.2] using hle)
    exact heq.symm
  have hYinterLe :
      (S.support (S.tripleOwner Y) ∩ S.support g).card ≤ 1 := by
    have hsplit := Finset.card_inter_add_card_sdiff
      (S.support (S.tripleOwner Y)) (S.support g)
    have hcap := hlineCap (S.tripleOwner Y) hexact.owner_line
    have hout :
        (S.support (S.tripleOwner Y) \ S.support g).card = 3 := by
      rw [hYoutEq, Y.2]
    omega
  have hYmem : S.tripleOwner Y ∈ Z03 ∪ L13 := by
    interval_cases hinter :
        (S.support (S.tripleOwner Y) ∩ S.support g).card
    · apply Finset.mem_union_left
      exact Finset.mem_filter.mpr
        ⟨S.mem_blocksOfKind.mpr hexact.owner_line, hinter, by
          rw [hYoutEq, Y.2]⟩
    · apply Finset.mem_union_right
      exact Finset.mem_filter.mpr
        ⟨S.mem_blocksOfKind.mpr hexact.owner_line, hinter, by
          rw [hYoutEq, Y.2]⟩
  have hZLsubset : Z03 ∪ L13 ⊆ {S.tripleOwner Y} := by
    intro c hc
    rcases Finset.mem_union.mp hc with hc | hc
    · have hspec := Finset.mem_filter.mp hc
      have hkind := S.mem_blocksOfKind.mp hspec.1
      let A : KSubset Point 3 :=
        ⟨S.support c \ S.support g, hspec.2.2⟩
      have hAT : A ∈ nineFiveOutsiderTriples S g := by
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_univ A, ?_⟩
        intro p hp
        exact Finset.mem_sdiff.mpr
          ⟨Finset.mem_univ p, (Finset.mem_sdiff.mp hp).2⟩
      have howner : S.tripleOwner A = c :=
        (S.triple_unique A c Finset.sdiff_subset).symm
      have hAY : A = Y := by
        by_contra hne
        have hcircle := hexact.other_owner_circle A hAT hne
        rw [howner, hkind] at hcircle
        cases hcircle
      simp only [Finset.mem_singleton]
      rw [← howner, hAY]
    · have hspec := Finset.mem_filter.mp hc
      have hkind := S.mem_blocksOfKind.mp hspec.1
      let A : KSubset Point 3 :=
        ⟨S.support c \ S.support g, hspec.2.2⟩
      have hAT : A ∈ nineFiveOutsiderTriples S g := by
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_univ A, ?_⟩
        intro p hp
        exact Finset.mem_sdiff.mpr
          ⟨Finset.mem_univ p, (Finset.mem_sdiff.mp hp).2⟩
      have howner : S.tripleOwner A = c :=
        (S.triple_unique A c Finset.sdiff_subset).symm
      have hAY : A = Y := by
        by_contra hne
        have hcircle := hexact.other_owner_circle A hAT hne
        rw [howner, hkind] at hcircle
        cases hcircle
      simp only [Finset.mem_singleton]
      rw [← howner, hAY]
  have hZLunion : Z03 ∪ L13 = {S.tripleOwner Y} := by
    apply Finset.Subset.antisymm hZLsubset
    intro c hc
    have hcEq : c = S.tripleOwner Y := Finset.mem_singleton.mp hc
    subst c
    exact hYmem
  have hZLdisj : Disjoint Z03 L13 := by
    rw [Finset.disjoint_left]
    intro c hcZ hcL
    have hz := (Finset.mem_filter.mp hcZ).2.1
    have hl := (Finset.mem_filter.mp hcL).2.1
    omega
  have hZLcard : Z03.card + L13.card = 1 := by
    rw [← Finset.card_union_of_disjoint hZLdisj, hZLunion]
    simp

  have hTripleWeight (c : Block) :
      Nat.choose (S.support c ∩ S.support g).card 1 *
          Nat.choose (S.support c \ S.support g).card 2 =
        (if c ∈ U then
          2 * Nat.choose (nineFiveFanDegree S g c) 2 else 0) +
        (if c ∈ C12 then 1 else 0) +
        3 * (if c ∈ C13 then 1 else 0) +
        (if c ∈ L12 then 1 else 0) +
        3 * (if c ∈ L13 then 1 else 0) +
        2 * (if c ∈ V22 then 1 else 0) := by
    by_cases hfan : c ∈ U
    · have hspec := nineFive_fan_block_spec S g c hfan
      have hdegree := nineFiveFanDegree_eq_outside_card S g c hfan
      have houtLe := houtsideCap c
      interval_cases hout : (S.support c \ S.support g).card <;>
        norm_num [U, C12, C13, L12, L13, V22, nineFiveCircleType,
          nineFiveLineType, BlockSystem.blocksOfKind, hfan, hspec.1,
          hspec.2.2, hdegree, hout, Nat.choose] <;> simp
    · by_cases hcg : c = g
      · subst c
        simp [U, C12, C13, L12, L13, V22, nineFiveCircleType,
          nineFiveLineType, BlockSystem.blocksOfKind, hfan, hgkind,
          hgcard]
      · have hinterLe := hinterBaseLe c hcg
        have houtLe := houtsideCap c
        cases hkind : S.kind c with
        | line =>
            have hsplit := Finset.card_inter_add_card_sdiff
              (S.support c) (S.support g)
            have hcap := hlineCap c hkind
            have hmin := S.line_min c hkind
            interval_cases hinter : (S.support c ∩ S.support g).card <;>
              interval_cases hout : (S.support c \ S.support g).card <;>
              norm_num [U, C12, C13, L12, L13, V22,
                nineFiveCircleType, nineFiveLineType,
                BlockSystem.blocksOfKind, hfan, hkind, hinter, hout,
                Nat.choose] <;> (try simp) <;> omega
        | circle =>
            have htwoZero
                (hinter : (S.support c ∩ S.support g).card = 2) :
                (S.support c \ S.support g).card = 0 := by
              by_contra hzero
              have houtPos : 0 < (S.support c \ S.support g).card :=
                Nat.pos_of_ne_zero hzero
              obtain ⟨p, hp⟩ := Finset.card_pos.mp houtPos
              let x : BlockOutsider S g :=
                ⟨p, mem_blockOutsiders.mpr (Finset.mem_sdiff.mp hp).2⟩
              have hpencil := mem_circlePencil_of_circle_of_inter_card_two
                S g c x hkind hinter (Finset.mem_sdiff.mp hp).1
              apply hfan
              exact Finset.mem_biUnion.mpr
                ⟨x, Finset.mem_univ x, hpencil⟩
            interval_cases hinter : (S.support c ∩ S.support g).card
            · simp [U, C12, C13, L12, L13, V22,
                nineFiveCircleType, nineFiveLineType,
                BlockSystem.blocksOfKind, hfan, hkind, hinter, Nat.choose]
            · interval_cases hout : (S.support c \ S.support g).card <;>
                norm_num [U, C12, C13, L12, L13, V22,
                  nineFiveCircleType, nineFiveLineType,
                  BlockSystem.blocksOfKind, hfan, hkind, hinter, hout,
                  Nat.choose] <;> simp
            · have houtZero := htwoZero (by omega)
              norm_num [U, C12, C13, L12, L13, V22,
                nineFiveCircleType, nineFiveLineType,
                BlockSystem.blocksOfKind, hfan, hkind, hinter, houtZero,
                Nat.choose]
  have hsumFan :
      (∑ c : Block, if c ∈ U then
          2 * Nat.choose (nineFiveFanDegree S g c) 2 else 0) =
        2 * nineFivePairMoment S g := by
    change (∑ c : Block, if c ∈ U then
      2 * Nat.choose (nineFiveFanDegree S g c) 2 else 0) =
        2 * ∑ c ∈ U, Nat.choose (nineFiveFanDegree S g c) 2
    calc
      _ = ∑ c ∈ U,
          2 * Nat.choose (nineFiveFanDegree S g c) 2 := by
        rw [← Finset.sum_filter]
        simp
      _ = _ := by rw [← Finset.mul_sum]
  have hrelative := S.relative_triple_partition (S.support g) 1 (by omega)
  rw [hpoint, hgcard] at hrelative
  norm_num [Nat.choose] at hrelative
  have hrelativeSum :
      (∑ c : Block,
        Nat.choose (S.support c ∩ S.support g).card 1 *
          Nat.choose (S.support c \ S.support g).card 2) =
        2 * nineFivePairMoment S g + C12.card + 3 * C13.card +
          L12.card + 3 * L13.card + 2 * V22.card := by
    calc
      _ = ∑ c : Block,
          ((if c ∈ U then
              2 * Nat.choose (nineFiveFanDegree S g c) 2 else 0) +
            (if c ∈ C12 then 1 else 0) +
            3 * (if c ∈ C13 then 1 else 0) +
            (if c ∈ L12 then 1 else 0) +
            3 * (if c ∈ L13 then 1 else 0) +
            2 * (if c ∈ V22 then 1 else 0)) := by
        apply Fintype.sum_congr
        exact hTripleWeight
      _ = _ := by
        simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
        rw [hsumFan]
        simp
  have hrelativeSum' :
      (∑ c : Block, (S.support c ∩ S.support g).card *
          Nat.choose (S.support c \ S.support g).card 2) =
        2 * nineFivePairMoment S g + C12.card + 3 * C13.card +
          L12.card + 3 * L13.card + 2 * V22.card := by
    simpa [Nat.choose] using hrelativeSum
  rw [hrelativeSum'] at hrelative
  have hC12zero : C12.card = 0 := by
    simp [C12, hcircleOneTwo]
  have hV22zero : V22.card = 0 := by
    simp [V22, hlineTwoTwo]
  have htriple : L12.card + 3 * C13.card + 3 * L13.card = 6 := by
    omega

  have hChordPoint (L : LineBlock S) :
      (if L ∈ nineFiveChordLines S g then
          (S.support L.1 \ S.support g).card else 0) =
        (if L.1 ∈ U21 then 1 else 0) +
          2 * (if L.1 ∈ V22 then 1 else 0) := by
    by_cases hchord : L ∈ nineFiveChordLines S g
    · have hinter := (Finset.mem_filter.mp hchord).2
      have houtLe := houtsideCap L.1
      have hsplit := Finset.card_inter_add_card_sdiff
        (S.support L.1) (S.support g)
      have hcap := hlineCap L.1 L.2
      interval_cases hout : (S.support L.1 \ S.support g).card <;>
        norm_num [hchord, U21, V22, nineFiveLineType,
          BlockSystem.blocksOfKind, L.2, hinter, hout] <;> omega
    · have hnotU : L.1 ∉ U21 := by
        intro hU
        apply hchord
        exact Finset.mem_filter.mpr
          ⟨Finset.mem_univ L, (Finset.mem_filter.mp hU).2.1⟩
      have hnotV : L.1 ∉ V22 := by
        intro hV
        apply hchord
        exact Finset.mem_filter.mpr
          ⟨Finset.mem_univ L, (Finset.mem_filter.mp hV).2.1⟩
      simp [hchord, hnotU, hnotV]
  have hUkind : ∀ c ∈ U21, S.kind c = .line := by
    intro c hc
    exact S.mem_blocksOfKind.mp (Finset.mem_filter.mp hc).1
  have hVkind : ∀ c ∈ V22, S.kind c = .line := by
    intro c hc
    exact S.mem_blocksOfKind.mp (Finset.mem_filter.mp hc).1
  have hL12kind : ∀ c ∈ L12, S.kind c = .line := by
    intro c hc
    exact S.mem_blocksOfKind.mp (Finset.mem_filter.mp hc).1
  have hL13kind : ∀ c ∈ L13, S.kind c = .line := by
    intro c hc
    exact S.mem_blocksOfKind.mp (Finset.mem_filter.mp hc).1
  have hZkind : ∀ c ∈ Z03, S.kind c = .line := by
    intro c hc
    exact S.mem_blocksOfKind.mp (Finset.mem_filter.mp hc).1
  have hsumU := nineFive_sum_line_indicator_eq_card S U21 hUkind
  have hsumV := nineFive_sum_line_indicator_eq_card S V22 hVkind
  have hsumL12 := nineFive_sum_line_indicator_eq_card S L12 hL12kind
  have hsumL13 := nineFive_sum_line_indicator_eq_card S L13 hL13kind
  have hsumZ := nineFive_sum_line_indicator_eq_card S Z03 hZkind
  have hRuv : nineFiveR S g = U21.card + 2 * V22.card := by
    rw [nineFiveR_eq_nineFiveChordIncidence S g hgkind hpoint hgcard]
    unfold nineFiveChordIncidence
    calc
      (∑ L ∈ nineFiveChordLines S g,
          (S.support L.1 \ S.support g).card) =
          ∑ L : LineBlock S,
            if L ∈ nineFiveChordLines S g then
              (S.support L.1 \ S.support g).card else 0 := by
        rw [← Finset.sum_filter]
        simp
      _ = ∑ L : LineBlock S,
          ((if L.1 ∈ U21 then 1 else 0) +
            2 * (if L.1 ∈ V22 then 1 else 0)) := by
        apply Fintype.sum_congr
        exact hChordPoint
      _ = U21.card + 2 * V22.card := by
        simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
        rw [hsumU, hsumV]
  have hLineWeight (L : LineBlock S) :
      (if 3 ≤ (S.support L.1).card then
          (Nat.choose (S.support L.1).card 2 : ℤ) +
            ((S.support L.1).card : ℤ) - 3
        else 0) =
        3 * (if L.1 ∈ U21 then (1 : ℤ) else 0) +
          7 * (if L.1 ∈ V22 then (1 : ℤ) else 0) +
          3 * (if L.1 ∈ L12 then (1 : ℤ) else 0) +
          7 * (if L.1 ∈ L13 then (1 : ℤ) else 0) +
          3 * (if L.1 ∈ Z03 then (1 : ℤ) else 0) := by
    have hLneG : L.1 ≠ g := by
      intro heq
      have hk := L.2
      rw [heq, hgkind] at hk
      cases hk
    have hinterLe := hinterBaseLe L.1 hLneG
    have houtLe := houtsideCap L.1
    have hsplit := Finset.card_inter_add_card_sdiff
      (S.support L.1) (S.support g)
    have hcap := hlineCap L.1 L.2
    have hmin := S.line_min L.1 L.2
    have hsize : (S.support L.1).card =
        (S.support L.1 ∩ S.support g).card +
          (S.support L.1 \ S.support g).card := by
      omega
    have hinterEmpty :
        S.support L.1 ∩ S.support g = ∅ ↔
          (S.support L.1 ∩ S.support g).card = 0 :=
      Finset.card_eq_zero.symm
    interval_cases hinter : (S.support L.1 ∩ S.support g).card <;>
      interval_cases hout : (S.support L.1 \ S.support g).card <;>
      norm_num [U21, V22, L12, L13, Z03, nineFiveLineType,
        BlockSystem.blocksOfKind, L.2, hinter, hout, hsize,
        hinterEmpty, Nat.choose] <;> omega
  have hsumUZ :
      (∑ L : LineBlock S, if L.1 ∈ U21 then (1 : ℤ) else 0) =
        (U21.card : ℤ) := by exact_mod_cast hsumU
  have hsumVZ :
      (∑ L : LineBlock S, if L.1 ∈ V22 then (1 : ℤ) else 0) =
        (V22.card : ℤ) := by exact_mod_cast hsumV
  have hsumL12Z :
      (∑ L : LineBlock S, if L.1 ∈ L12 then (1 : ℤ) else 0) =
        (L12.card : ℤ) := by exact_mod_cast hsumL12
  have hsumL13Z :
      (∑ L : LineBlock S, if L.1 ∈ L13 then (1 : ℤ) else 0) =
        (L13.card : ℤ) := by exact_mod_cast hsumL13
  have hsumZZ :
      (∑ L : LineBlock S, if L.1 ∈ Z03 then (1 : ℤ) else 0) =
        (Z03.card : ℤ) := by exact_mod_cast hsumZ
  have hGlobalEq : S.globalLineRow =
      3 * (U21.card : ℤ) + 7 * (V22.card : ℤ) +
        3 * (L12.card : ℤ) + 7 * (L13.card : ℤ) +
        3 * (Z03.card : ℤ) := by
    unfold BlockSystem.globalLineRow
    calc
      _ = ∑ L : LineBlock S,
          (3 * (if L.1 ∈ U21 then (1 : ℤ) else 0) +
            7 * (if L.1 ∈ V22 then (1 : ℤ) else 0) +
            3 * (if L.1 ∈ L12 then (1 : ℤ) else 0) +
            7 * (if L.1 ∈ L13 then (1 : ℤ) else 0) +
            3 * (if L.1 ∈ Z03 then (1 : ℤ) else 0)) := by
        apply Fintype.sum_congr
        exact hLineWeight
      _ = _ := by
        simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
        rw [hsumUZ, hsumVZ, hsumL12Z, hsumL13Z, hsumZZ]
  have hUcard : U21.card = 8 := by omega
  have hline : 3 * L12.card + 4 * L13.card ≤ 6 := by
    rw [hGlobalEq, hUcard, hV22zero] at hglobal
    omega
  have hspecial : T.card = 2 :=
    nineFiveSpecialOutsiderTriples_card_eq_two_of_rows
      S g hcard htriple hline
  have hL12zero : L12.card = 0 := by omega
  have hlineOneTwo : nineFiveLineType S g 1 2 = ∅ := by
    apply Finset.card_eq_zero.mp
    simpa [L12] using hL12zero
  have hcover := nineFive_special_pair_coverage_of_pairMoment_eq_twelve
    S g hpoint hgcard hmoment hlineCap houtsideCap
      hcircleOneTwo hlineOneTwo
  exact nineFive_three_collinear_pair_shadow_impossible
    S g hcard htriple hline hcover

end Fan

end Erdos506.V1
