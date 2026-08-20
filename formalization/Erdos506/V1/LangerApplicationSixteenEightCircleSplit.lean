import Erdos506.V1.LangerApplicationRichCircleEasyFinish
import Erdos506.V1.Eight

/-!
# The sharp sixteen--eight rich-circle split

For a counterexample on sixteen labels with a selected eight-circle, the
induced configuration on the eight outsiders is automatically noncollinear:
otherwise its spanning eight-line already gives far more than the target by
the rich-line pencil.  Hence the outsider configuration is either admissible,
in which case the existing corrected circle pencil is sharp, or it is carried
by a second eight-circle.  This file records that lossless split without
hiding the remaining geometric equality case in a callback.
-/

namespace Erdos506.V1

open Erdos506.Block
open Erdos506.Block.BlockSystem
open Erdos506.Finite
open Erdos506.Incidence
open Erdos506.V4
open scoped BigOperators

universe u

variable {alpha : Type u} [Fintype alpha] [DecidableEq alpha]

section ExactDistinguishedBonferroni

variable {Iota Beta : Type*} [DecidableEq Iota] [DecidableEq Beta]

noncomputable def distinguishedPairMoment
    (I : Finset Iota) (F : Iota → Finset Beta) : Nat :=
  ∑ A ∈ I.powersetCard 2,
    ((I.biUnion F).filter fun x => ∀ i ∈ A, x ∈ F i).card

private theorem distinguished_family_degree_sum
    (I : Finset Iota) (F : Iota → Finset Beta) :
    (∑ x ∈ I.biUnion F, (I.filter fun i => x ∈ F i).card) =
      ∑ i ∈ I, (F i).card := by
  classical
  calc
    _ = ∑ x ∈ I.biUnion F, ∑ i ∈ I,
          if x ∈ F i then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro x _hx
      rw [Finset.card_eq_sum_ones, Finset.sum_filter]
    _ = ∑ i ∈ I, ∑ x ∈ I.biUnion F,
          if x ∈ F i then 1 else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ i ∈ I, (F i).card := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [← Finset.sum_filter]
      have heq : (I.biUnion F).filter (fun x => x ∈ F i) = F i := by
        ext x
        simp only [Finset.mem_filter, Finset.mem_biUnion]
        constructor
        · exact fun hx => hx.2
        · exact fun hx => ⟨⟨i, hi, hx⟩, hx⟩
      rw [heq]
      simp

private theorem distinguished_pairMoment_eq_degree_choose
    (I : Finset Iota) (F : Iota → Finset Beta) :
    distinguishedPairMoment I F =
      ∑ x ∈ I.biUnion F,
        Nat.choose ((I.filter fun i => x ∈ F i).card) 2 := by
  classical
  unfold distinguishedPairMoment
  calc
    _ = ∑ A ∈ I.powersetCard 2, ∑ x ∈ I.biUnion F,
          if (∀ i ∈ A, x ∈ F i) then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro A _hA
      rw [Finset.card_eq_sum_ones, Finset.sum_filter]
    _ = ∑ x ∈ I.biUnion F, ∑ A ∈ I.powersetCard 2,
          if (∀ i ∈ A, x ∈ F i) then 1 else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ x ∈ I.biUnion F,
        ((I.filter fun i => x ∈ F i).powersetCard 2).card := by
      apply Finset.sum_congr rfl
      intro x _hx
      rw [powersetCard_filter_eq]
      rw [Finset.card_eq_sum_ones, Finset.sum_filter]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro x _hx
      rw [Finset.card_powersetCard]

private theorem degree_le_one_add_choose_two (d : Nat) (hd : 1 ≤ d) :
    d ≤ 1 + Nat.choose d 2 := by
  cases d with
  | zero => omega
  | succ d =>
      cases d with
      | zero => norm_num [Nat.choose]
      | succ k =>
          have hrec : Nat.choose (k + 2) 2 =
              (k + 1) + Nat.choose (k + 1) 2 := by
            simpa using Nat.choose_succ_succ (k + 1) 1
          rw [hrec]
          omega

private theorem degree_add_one_le_one_add_choose_two
    (d : Nat) (hd : 3 ≤ d) : d + 1 ≤ 1 + Nat.choose d 2 := by
  cases d with
  | zero => omega
  | succ d =>
      cases d with
      | zero => omega
      | succ d =>
          cases d with
          | zero => omega
          | succ k =>
              have hrec : Nat.choose (k + 3) 2 =
                  (k + 2) + Nat.choose (k + 2) 2 := by
                simpa using Nat.choose_succ_succ (k + 2) 1
              have hpos : 0 < Nat.choose (k + 2) 2 :=
                Nat.choose_pos (by omega)
              rw [hrec]
              omega

theorem sum_family_card_add_distinguished_le
    (I : Finset Iota) (F : Iota → Finset Beta) (D : Finset Beta)
    (hdist : ∀ x ∈ D, x ∈ I.biUnion F →
      3 ≤ (I.filter fun i => x ∈ F i).card) :
    (∑ i ∈ I, (F i).card) + D.card ≤
      ((I.biUnion F) ∪ D).card + distinguishedPairMoment I F := by
  classical
  let U := I.biUnion F
  let deg := fun x => (I.filter fun i => x ∈ F i).card
  have hdegPos : ∀ x ∈ U, 1 ≤ deg x := by
    intro x hx
    rcases Finset.mem_biUnion.mp hx with ⟨i, hi, hxi⟩
    apply Finset.one_le_card.mpr
    exact ⟨i, Finset.mem_filter.mpr ⟨hi, hxi⟩⟩
  have hpoint (x : Beta) (hx : x ∈ U) :
      deg x + (if x ∈ D then 1 else 0) ≤
        1 + Nat.choose (deg x) 2 := by
    by_cases hxD : x ∈ D
    · simp only [hxD, if_true]
      exact degree_add_one_le_one_add_choose_two _ (hdist x hxD hx)
    · simp only [hxD, if_false, Nat.add_zero]
      exact degree_le_one_add_choose_two _ (hdegPos x hx)
  have hsum := Finset.sum_le_sum (fun x hx => hpoint x hx)
  have hindicator :
      (∑ x ∈ U, if x ∈ D then 1 else 0) = (U ∩ D).card := by
    rw [← Finset.sum_filter]
    have heq : U.filter (fun x => x ∈ D) = U ∩ D := by ext x; simp
    rw [heq]
    simp
  have hdegree := distinguished_family_degree_sum I F
  have hpair := distinguished_pairMoment_eq_degree_choose I F
  dsimp only [U, deg] at hsum hindicator hdegree hpair ⊢
  have hsumNat :
      (∑ i ∈ I, (F i).card) + ((I.biUnion F) ∩ D).card ≤
        (I.biUnion F).card + distinguishedPairMoment I F := by
    simpa only [Finset.sum_add_distrib, hindicator, hdegree, hpair,
      Finset.sum_const, nsmul_eq_mul, Nat.mul_one] using hsum
  have hunion :
      ((I.biUnion F) ∪ D).card + ((I.biUnion F) ∩ D).card =
        (I.biUnion F).card + D.card :=
    Finset.card_union_add_card_inter (I.biUnion F) D
  omega

theorem distinguishedPairMoment_le
    (I : Finset Iota) (F : Iota → Finset Beta) (h : Nat)
    (hinter : ∀ i ∈ I, ∀ j ∈ I, i ≠ j →
      (F i ∩ F j).card ≤ h) :
    distinguishedPairMoment I F ≤ Nat.choose I.card 2 * h := by
  classical
  unfold distinguishedPairMoment
  calc
    _ ≤ ∑ _A ∈ I.powersetCard 2, h := by
      apply Finset.sum_le_sum
      intro A hA
      have hAspec := Finset.mem_powersetCard.mp hA
      obtain ⟨i, j, hij, hAeq⟩ := Finset.card_eq_two.mp hAspec.2
      have hiA : i ∈ A := by rw [hAeq]; simp
      have hjA : j ∈ A := by rw [hAeq]; simp
      have hi := hAspec.1 hiA
      have hj := hAspec.1 hjA
      have heq :
          ((I.biUnion F).filter fun x => ∀ k ∈ A, x ∈ F k) =
            F i ∩ F j := by
        ext x
        constructor
        · intro hx
          have hall := (Finset.mem_filter.mp hx).2
          exact Finset.mem_inter.mpr
            ⟨hall i hiA, hall j hjA⟩
        · intro hx
          have hxij := Finset.mem_inter.mp hx
          apply Finset.mem_filter.mpr
          refine ⟨Finset.mem_biUnion.mpr ⟨i, hi, hxij.1⟩, ?_⟩
          intro k hk
          rw [hAeq] at hk
          simp only [Finset.mem_insert, Finset.mem_singleton] at hk
          rcases hk with rfl | rfl
          · exact hxij.1
          · exact hxij.2
      rw [heq]
      exact hinter i hi j hj hij
    _ = Nat.choose I.card 2 * h := by
      simp [Finset.card_powersetCard]

private theorem eq_of_le_of_sum_eq_card_mul
    {Gamma : Type*} [DecidableEq Gamma]
    (J : Finset Gamma) (f : Gamma → Nat) (M : Nat)
    (hle : ∀ x ∈ J, f x ≤ M)
    (hsum : (∑ x ∈ J, f x) = J.card * M) :
    ∀ x ∈ J, f x = M := by
  intro x hx
  have hcomp : (∑ y ∈ J, (M - f y)) = 0 := by
    have hadd :
        (∑ y ∈ J, f y) + (∑ y ∈ J, (M - f y)) =
          J.card * M := by
      rw [← Finset.sum_add_distrib]
      calc
        _ = ∑ _y ∈ J, M := by
          apply Finset.sum_congr rfl
          intro y hy
          have := hle y hy
          omega
        _ = J.card * M := by simp
    omega
  have hsingle : M - f x ≤ ∑ y ∈ J, (M - f y) :=
    Finset.single_le_sum (fun y _hy => Nat.zero_le (M - f y)) hx
  have hxle := hle x hx
  omega

end ExactDistinguishedBonferroni

/-- The two pointwise equality rows hidden in a sharp corrected eight-circle
pencil. -/
structure SixteenEightCirclePencilEqualityData
    {Point Block : Type*} [Fintype Point] [Fintype Block]
    [DecidableEq Point]
    (S : BlockSystem Point Block) (b : Block) where
  fan_card : ∀ x : BlockOutsider S b, (circlePencil S b x).card = 24
  line_pair_card : ∀ x : BlockOutsider S b,
    (lineBasePairs S b x).card = 4
  common_card : ∀ x y : BlockOutsider S b, x ≠ y →
    (commonPencils S b x y).card = 4

private theorem family_pair_inter_card_eq_of_moment_eq
    {Iota Beta : Type*} [DecidableEq Iota] [DecidableEq Beta]
    (I : Finset Iota) (F : Iota → Finset Beta) (h : Nat)
    (hinter : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → (F i ∩ F j).card ≤ h)
    (hmoment : distinguishedPairMoment I F = Nat.choose I.card 2 * h)
    {x y : Iota} (hx : x ∈ I) (hy : y ∈ I) (hxy : x ≠ y) :
    (F x ∩ F y).card = h := by
  classical
  let J := I.powersetCard 2
  let pairTerm := fun A : Finset Iota =>
    ((I.biUnion F).filter fun e => ∀ z ∈ A, e ∈ F z).card
  have htermLe : ∀ A ∈ J, pairTerm A ≤ h := by
    intro A hA
    have hAspec := Finset.mem_powersetCard.mp hA
    obtain ⟨i, j, hij, hAeq⟩ := Finset.card_eq_two.mp hAspec.2
    have hiA : i ∈ A := by rw [hAeq]; simp
    have hjA : j ∈ A := by rw [hAeq]; simp
    have hi := hAspec.1 hiA
    have hj := hAspec.1 hjA
    have heq : pairTerm A = (F i ∩ F j).card := by
      dsimp only [pairTerm]
      congr 1
      ext e
      constructor
      · intro he
        have hall := (Finset.mem_filter.mp he).2
        exact Finset.mem_inter.mpr ⟨hall i hiA, hall j hjA⟩
      · intro he
        have heij := Finset.mem_inter.mp he
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_biUnion.mpr ⟨i, hi, heij.1⟩, ?_⟩
        intro z hz
        rw [hAeq] at hz
        simp only [Finset.mem_insert, Finset.mem_singleton] at hz
        rcases hz with rfl | rfl
        · exact heij.1
        · exact heij.2
    rw [heq]
    exact hinter i hi j hj hij
  have hsum : (∑ A ∈ J, pairTerm A) = J.card * h := by
    change distinguishedPairMoment I F = J.card * h
    simpa only [J, Finset.card_powersetCard] using hmoment
  have heach := eq_of_le_of_sum_eq_card_mul J pairTerm h htermLe hsum
  let A : Finset Iota := {x, y}
  have hA : A ∈ J := by
    apply Finset.mem_powersetCard.mpr
    refine ⟨?_, by simp [A, hxy]⟩
    intro z hz
    simp only [A, Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl
    · exact hx
    · exact hy
  have heq : pairTerm A = (F x ∩ F y).card := by
    dsimp only [pairTerm]
    congr 1
    ext e
    constructor
    · intro he
      have hall := (Finset.mem_filter.mp he).2
      exact Finset.mem_inter.mpr
        ⟨hall x (by simp [A]), hall y (by simp [A])⟩
    · intro he
      have hexy := Finset.mem_inter.mp he
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_biUnion.mpr ⟨x, hx, hexy.1⟩, ?_⟩
      intro z hz
      simp only [A, Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with rfl | rfl
      · exact hexy.1
      · exact hexy.2
  rw [← heq]
  exact heach A hA

private theorem eight_family_sharp_of_union_upper
    {Iota Beta : Type*} [DecidableEq Iota] [DecidableEq Beta]
    (I : Finset Iota) (F : Iota → Finset Beta) (D : Finset Beta)
    (hIcard : I.card = 8) (hDcard : D.card = 17)
    (hFcard : ∀ x ∈ I, 24 ≤ (F x).card)
    (hinter : ∀ x ∈ I, ∀ y ∈ I, x ≠ y → (F x ∩ F y).card ≤ 4)
    (hdist : ∀ d ∈ D, d ∈ I.biUnion F →
      3 ≤ (I.filter fun x => d ∈ F x).card)
    (hunionUpper : ((I.biUnion F) ∪ D).card ≤ 97) :
    (∀ x ∈ I, (F x).card = 24) ∧
      ∀ x ∈ I, ∀ y ∈ I, x ≠ y → (F x ∩ F y).card = 4 := by
  classical
  have hmaster := sum_family_card_add_distinguished_le I F D hdist
  have hmomentUpper : distinguishedPairMoment I F ≤ 112 := by
    have h := distinguishedPairMoment_le I F 4 hinter
    rw [hIcard] at h
    norm_num [Nat.choose] at h ⊢
    exact h
  have hsumLower : 192 ≤ ∑ x ∈ I, (F x).card := by
    calc
      192 = ∑ _x ∈ I, 24 := by simp [hIcard]
      _ ≤ _ := Finset.sum_le_sum hFcard
  have hsumEq : (∑ x ∈ I, (F x).card) = 192 := by
    omega
  have hmomentEq : distinguishedPairMoment I F = 112 := by
    omega
  have hmomentExact : distinguishedPairMoment I F =
      Nat.choose I.card 2 * 4 := by
    rw [hmomentEq, hIcard]
    norm_num [Nat.choose]
  refine ⟨?_, ?_⟩
  · intro x hxI
    have hrest : (I.erase x).card * 24 ≤
        ∑ y ∈ I.erase x, (F y).card := by
      calc
        _ = ∑ _y ∈ I.erase x, 24 := by simp
        _ ≤ _ := by
          apply Finset.sum_le_sum
          intro y hy
          exact hFcard y (Finset.mem_of_mem_erase hy)
    have herase : (I.erase x).card = 7 := by
      rw [Finset.card_erase_of_mem hxI, hIcard]
    have hdecomp :
        (∑ y ∈ I.erase x, (F y).card) + (F x).card = 192 := by
      rw [Finset.sum_erase_add I (fun y => (F y).card) hxI, hsumEq]
    have hxLower := hFcard x hxI
    omega
  · intro x hxI y hyI hxy
    exact family_pair_inter_card_eq_of_moment_eq I F 4 hinter
      hmomentExact hxI hyI hxy

private theorem sixteenEightCirclePencilSharpCore_of_counts
    (cfg : Configuration alpha) (b : GeometricBlock cfg)
    (hcircle : (blockSystem cfg).kind b = .circle)
    (h16 : Fintype.card alpha = 16)
    (height : (geometricBlockSupport cfg b).card = 8)
    (hQcount : Erdos506.V4.circleCount
      (finsetRestrictionConfiguration cfg
        (blockOutsiders (blockSystem cfg) b)) = 17)
    (hcount : Erdos506.V4.circleCount cfg = 98) :
    (∀ x : BlockOutsider (blockSystem cfg) b,
      (circlePencil (blockSystem cfg) b x).card = 24) ∧
    ∀ x y : BlockOutsider (blockSystem cfg) b, x ≠ y →
      (commonPencils (blockSystem cfg) b x y).card = 4 := by
  classical
  let S := blockSystem cfg
  let O := blockOutsiders S b
  let I : Finset (BlockOutsider S b) := Finset.univ
  let F : BlockOutsider S b → Finset (GeometricBlock cfg) := circlePencil S b
  let D := finsetRestrictionCircleBlocks cfg O
  let U := I.biUnion F
  have heightS : (S.support b).card = 8 := by
    simpa only [S] using height
  have hIcard : I.card = 8 := by
    dsimp only [I]
    rw [Finset.card_univ, Fintype.card_coe, card_blockOutsiders,
      h16, heightS]
  have hDcard : D.card = 17 := by
    rw [show D.card = Erdos506.V4.circleCount
      (finsetRestrictionConfiguration cfg O) by
        exact card_finsetRestrictionCircleBlocks cfg O]
    simpa [O, S] using hQcount
  have hFcard : ∀ x ∈ I, 24 ≤ (F x).card := by
    intro x _hx
    dsimp only [F]
    rw [card_circlePencil]
    have h := card_circleBasePairs_lower S b x
    rw [heightS] at h
    norm_num [Nat.choose] at h ⊢
    exact h
  have hinter : ∀ x ∈ I, ∀ y ∈ I, x ≠ y →
      (F x ∩ F y).card ≤ 4 := by
    intro x _hx y _hy hxy
    dsimp only [F]
    rw [circlePencil_inter_eq_commonPencils]
    have h := card_commonPencils_le_half S b x y hxy
    rw [heightS] at h
    norm_num at h ⊢
    exact h
  have hdist : ∀ d ∈ D, d ∈ U →
      3 ≤ (I.filter fun x => d ∈ F x).card := by
    intro d hdD hdU
    dsimp only [D, finsetRestrictionCircleBlocks] at hdD
    obtain ⟨c, _hc, rfl⟩ := Finset.mem_image.mp hdD
    let C := liftFinsetRestrictionDeterminedCircle cfg O c
    have hinterBase :
        (S.support (Sum.inr C) ∩ S.support b).card = 2 := by
      rcases Finset.mem_biUnion.mp hdU with ⟨x, _hx, hxFan⟩
      obtain ⟨u, _hu, howner⟩ := mem_circlePencil.mp hxFan
      rw [← howner, pencilOwner_inter_base S b x u]
      exact (Finset.mem_powersetCard.mp u.2).2
    have htraceSub :
        circleTrace (finsetRestrictionConfiguration cfg O) c.1 ⊆
          I.filter fun x => (Sum.inr C : GeometricBlock cfg) ∈ F x := by
      intro x hx
      apply Finset.mem_filter.mpr
      refine ⟨by simp [I], ?_⟩
      dsimp only [F]
      apply mem_circlePencil_of_kind_circle_of_inter_card_two
        S b x (Sum.inr C)
      · rfl
      · change x.1 ∈ circleTrace cfg C.1
        exact (mem_circleTrace_finsetRestriction_iff cfg O c.1 x).mp hx
      · exact hinterBase
    have hthree := Erdos506.V3.circleSupport_card_ge_three
      (finsetRestrictionConfiguration cfg O) c
    exact hthree.trans (Finset.card_le_card htraceSub)
  have hbnotU : b ∉ U := by
    intro hbU
    rcases Finset.mem_biUnion.mp hbU with ⟨x, _hx, hbFan⟩
    obtain ⟨u, _hu, howner⟩ := mem_circlePencil.mp hbFan
    exact pencilOwner_ne_base S b x u howner
  have hbnotD : b ∉ D := by
    intro hbD
    dsimp only [D, finsetRestrictionCircleBlocks] at hbD
    obtain ⟨c, _hc, hcb⟩ := Finset.mem_image.mp hbD
    have htraceThree := Erdos506.V3.circleSupport_card_ge_three
      (finsetRestrictionConfiguration cfg O) c
    have htraceNonempty :
        (circleTrace (finsetRestrictionConfiguration cfg O) c.1).Nonempty := by
      apply Finset.nonempty_iff_ne_empty.mpr
      intro hempty
      rw [hempty] at htraceThree
      simp at htraceThree
    obtain ⟨x, hx⟩ := htraceNonempty
    have hxAmbient :=
      (mem_circleTrace_finsetRestriction_iff cfg O c.1 x).mp hx
    let C := liftFinsetRestrictionDeterminedCircle cfg O c
    have hsupportEq : S.support (Sum.inr C) = S.support b :=
      congrArg S.support hcb
    apply (mem_blockOutsiders.mp x.2)
    rw [← hsupportEq]
    change x.1 ∈ circleTrace cfg C.1
    exact hxAmbient
  have hsub : insert b (U ∪ D) ⊆ S.blocksOfKind .circle := by
    intro e he
    rcases Finset.mem_insert.mp he with rfl | he
    · exact S.mem_blocksOfKind.mpr hcircle
    · rcases Finset.mem_union.mp he with heU | heD
      · rcases Finset.mem_biUnion.mp heU with ⟨x, _hx, hxFan⟩
        exact S.mem_blocksOfKind.mpr (circlePencil_kind S b x hxFan)
      · dsimp only [D, finsetRestrictionCircleBlocks] at heD
        obtain ⟨c, _hc, rfl⟩ := Finset.mem_image.mp heD
        exact S.mem_blocksOfKind.mpr rfl
  have hunionUpper : (U ∪ D).card ≤ 97 := by
    have hcardSub := Finset.card_le_card hsub
    have hbnot : b ∉ U ∪ D := by
      intro hb
      rcases Finset.mem_union.mp hb with hbU | hbD
      · exact hbnotU hbU
      · exact hbnotD hbD
    rw [Finset.card_insert_of_notMem hbnot] at hcardSub
    have htotal : S.totalCircleCount = 98 := by
      rw [totalCircleCount_eq_card_determinedCircle,
        ← Erdos506.V3.circleCount_eq_card_determinedCircle]
      exact hcount
    change (U ∪ D).card + 1 ≤ S.totalCircleCount at hcardSub
    omega
  change ∀ d ∈ D, d ∈ I.biUnion F →
      3 ≤ (I.filter fun x => d ∈ F x).card at hdist
  change (I.biUnion F ∪ D).card ≤ 97 at hunionUpper
  obtain ⟨hfanOn, hpairOn⟩ := eight_family_sharp_of_union_upper
    I F D hIcard hDcard hFcard hinter hdist hunionUpper
  refine ⟨?_, ?_⟩
  · intro x
    have hxI : x ∈ I := Finset.mem_univ x
    change (F x).card = 24
    exact hfanOn x hxI
  · intro x y hxy
    have hxI : x ∈ I := Finset.mem_univ x
    have hyI : y ∈ I := Finset.mem_univ y
    rw [← circlePencil_inter_eq_commonPencils]
    change (F x ∩ F y).card = 4
    exact hpairOn x hxI y hyI hxy

private theorem sixteenEightCirclePencilEqualityData_of_counts
    (cfg : Configuration alpha) (b : GeometricBlock cfg)
    (hcircle : (blockSystem cfg).kind b = .circle)
    (h16 : Fintype.card alpha = 16)
    (height : (geometricBlockSupport cfg b).card = 8)
    (hQcount : Erdos506.V4.circleCount
      (finsetRestrictionConfiguration cfg
        (blockOutsiders (blockSystem cfg) b)) = 17)
    (hcount : Erdos506.V4.circleCount cfg = 98) :
    SixteenEightCirclePencilEqualityData (blockSystem cfg) b := by
  classical
  let S := blockSystem cfg
  have heightS : (S.support b).card = 8 := by
    simpa only [S] using height
  obtain ⟨hfanEq, hcommonEq⟩ :=
    sixteenEightCirclePencilSharpCore_of_counts
      cfg b hcircle h16 height hQcount hcount
  change ∀ x : BlockOutsider S b,
    (circlePencil S b x).card = 24 at hfanEq
  change ∀ x y : BlockOutsider S b, x ≠ y →
    (commonPencils S b x y).card = 4 at hcommonEq
  have hlineEq (x : BlockOutsider S b) :
      (lineBasePairs S b x).card = 4 := by
    have hpart := card_circleBasePairs_add_card_lineBasePairs S b x
    have hcirclePairs : (circleBasePairs S b x).card = 24 := by
      rw [← card_circlePencil]
      exact hfanEq x
    rw [hcirclePairs, heightS] at hpart
    norm_num [Nat.choose] at hpart
    omega
  exact ⟨hfanEq, hlineEq, hcommonEq⟩

theorem line_trace_disjoint_commonPencilBasePair_generic
    {Point Block : Type*} [Fintype Point] [Fintype Block]
    [DecidableEq Point]
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

private theorem lineBasePairs_disjoint_of_sixteenEightEquality
    {Point Block : Type*} [Fintype Point] [Fintype Block]
    [DecidableEq Point]
    (S : BlockSystem Point Block) (g : Block)
    (hgcard : (S.support g).card = 8)
    (E : SixteenEightCirclePencilEqualityData S g)
    (x y : BlockOutsider S g) (hxy : x ≠ y) :
    Disjoint (lineBasePairs S g x) (lineBasePairs S g y) := by
  classical
  rw [Finset.disjoint_left]
  intro u hux huy
  have hxKind := mem_lineBasePairs.mp hux
  have hyKind := mem_lineBasePairs.mp huy
  let Lx : LineBlock S := ⟨pencilOwner S g x u, hxKind⟩
  let Ly : LineBlock S := ⟨pencilOwner S g y u, hyKind⟩
  have howners : Lx.1 = Ly.1 := by
    by_contra hne
    have hlt := S.distinct_line_inter_card_lt_two (show Lx ≠ Ly by
      intro heq
      exact hne (congrArg Subtype.val heq))
    have husub : u.1 ⊆ S.support Lx.1 ∩ S.support Ly.1 := by
      intro z hz
      exact Finset.mem_inter.mpr
        ⟨pencilOwner_contains_pair S g x u hz,
          pencilOwner_contains_pair S g y u hz⟩
    have hule := Finset.card_le_card husub
    have hucard := (Finset.mem_powersetCard.mp u.2).2
    omega
  have hxL : x.1 ∈ S.support Lx.1 :=
    pencilOwner_contains_outsider S g x u
  have hyL : y.1 ∈ S.support Lx.1 := by
    rw [howners]
    exact pencilOwner_contains_outsider S g y u
  let P := commonPencilBasePairs S g x y
  have hPcard : P.card = 4 := by
    dsimp only [P]
    rw [card_commonPencilBasePairs, E.common_card x y hxy]
  have hPdisj : ((P : Finset (Finset Point)) : Set (Finset Point)).PairwiseDisjoint id := by
    exact commonPencilBasePairs_pairwiseDisjoint S g x y hxy
  have hAcard : ∀ A ∈ P, A.card = 2 := by
    intro A hA
    dsimp only [P] at hA
    rw [commonPencilBasePairs] at hA
    obtain ⟨c, _hc, rfl⟩ := Finset.mem_image.mp hA
    exact commonPencilBasePair_card S g x y c
  have hUnionCard : (P.biUnion id).card = 8 := by
    rw [Finset.card_biUnion hPdisj]
    calc
      (∑ A ∈ P, A.card) = ∑ _A ∈ P, 2 := by
        apply Finset.sum_congr rfl
        intro A hA
        rw [hAcard A hA]
      _ = 8 := by simp [hPcard]
  have hUnionSub : P.biUnion id ⊆ S.support g := by
    intro z hz
    obtain ⟨A, hAP, hzA⟩ := Finset.mem_biUnion.mp hz
    dsimp only [P] at hAP
    rw [commonPencilBasePairs] at hAP
    obtain ⟨c, _hc, hAc⟩ := Finset.mem_image.mp hAP
    rw [← hAc] at hzA
    exact (Finset.mem_inter.mp hzA).2
  have hUnionEq : P.biUnion id = S.support g := by
    apply Finset.eq_of_subset_of_card_le hUnionSub
    rw [hUnionCard, hgcard]
  have huCard := (Finset.mem_powersetCard.mp u.2).2
  have huNonempty : u.1.Nonempty := by
    apply Finset.nonempty_iff_ne_empty.mpr
    intro hempty
    rw [hempty] at huCard
    simp at huCard
  obtain ⟨z, hz⟩ := huNonempty
  have hzLine : z ∈ S.support Lx.1 :=
    pencilOwner_contains_pair S g x u hz
  have hzBase : z ∈ S.support g :=
    (Finset.mem_powersetCard.mp u.2).1 hz
  have hzUnion : z ∈ P.biUnion id := by rw [hUnionEq]; exact hzBase
  obtain ⟨A, hAP, hzA⟩ := Finset.mem_biUnion.mp hzUnion
  dsimp only [P] at hAP
  rw [commonPencilBasePairs] at hAP
  obtain ⟨c, hc, hAc⟩ := Finset.mem_image.mp hAP
  have hdisj := line_trace_disjoint_commonPencilBasePair_generic
    S g Lx x y hxy hxL hyL c
  have hzQ : z ∈ S.support Lx.1 ∩ S.support g :=
    Finset.mem_inter.mpr ⟨hzLine, hzBase⟩
  apply (Finset.disjoint_left.mp hdisj) hzQ
  rw [hAc]
  exact hzA

/-- Eight disjoint four-matchings cannot fit into the twenty-eight pairs of
an eight-set. -/
theorem sixteenEightCirclePencilEqualityData_impossible
    {Point Block : Type*} [Fintype Point] [Fintype Block]
    [DecidableEq Point]
    (S : BlockSystem Point Block) (g : Block)
    (hgcard : (S.support g).card = 8)
    (hout : (blockOutsiders S g).card = 8)
    (E : SixteenEightCirclePencilEqualityData S g) : False := by
  classical
  let I : Finset (BlockOutsider S g) := Finset.univ
  let F : BlockOutsider S g → Finset (BlockBasePair S g) :=
    lineBasePairs S g
  have hIcard : I.card = 8 := by
    dsimp only [I]
    rw [Finset.card_univ, Fintype.card_coe, hout]
  have hdisj : ((I : Finset (BlockOutsider S g)) :
      Set (BlockOutsider S g)).PairwiseDisjoint F := by
    intro x _hx y _hy hxy
    exact lineBasePairs_disjoint_of_sixteenEightEquality
      S g hgcard E x y hxy
  have hUnionCard : (I.biUnion F).card = 32 := by
    rw [Finset.card_biUnion hdisj]
    calc
      (∑ x ∈ I, (F x).card) = ∑ _x ∈ I, 4 := by
        apply Finset.sum_congr rfl
        intro x _hx
        exact E.line_pair_card x
      _ = 32 := by simp [hIcard]
  have hUniverseCard :
      (Finset.univ : Finset (BlockBasePair S g)).card = 28 := by
    rw [Finset.card_univ, Fintype.card_coe,
      Finset.card_powersetCard, hgcard]
    norm_num [Nat.choose]
  have hle := Finset.card_le_card
    (show I.biUnion F ⊆
      (Finset.univ : Finset (BlockBasePair S g)) from Finset.subset_univ _)
  rw [hUnionCard, hUniverseCard] at hle
  omega

private theorem sixteenEightCircle_outsider_noncollinear
    (cfg : Configuration alpha) (hadm : Admissible cfg)
    (b : GeometricBlock cfg)
    (h16 : Fintype.card alpha = 16)
    (height : (geometricBlockSupport cfg b).card = 8)
    (hcount : Erdos506.V4.circleCount cfg <
      Erdos506.v1UniformTarget (Fintype.card alpha)) :
    Noncollinear (finsetRestrictionConfiguration cfg
      (blockOutsiders (blockSystem cfg) b)) := by
  classical
  let S := blockSystem cfg
  let O := blockOutsiders S b
  let Q := finsetRestrictionConfiguration cfg O
  have heightS : (S.support b).card = 8 := by
    simpa only [S] using height
  have hOcard : O.card = 8 := by
    dsimp only [O]
    rw [card_blockOutsiders, h16, heightS]
  have hQcard : Fintype.card (BlockOutsider S b) = 8 := by
    rw [Fintype.card_coe, hOcard]
  intro hcol
  obtain ⟨a, d, had⟩ := Fintype.exists_pair_of_one_lt_card (by omega :
    1 < Fintype.card (BlockOutsider S b))
  have had' : a.1 ≠ d.1 := by
    intro heq
    exact had (Subtype.ext heq)
  let A : KSubset alpha 2 := ⟨{a.1, d.1}, by simp [had']⟩
  let L : DeterminedLine cfg :=
    ⟨lineOfPair cfg A, lineOfPair_mem_determinedLines cfg A⟩
  have hall (q : BlockOutsider S b) : q.1 ∈ lineSupport cfg L := by
    have haRange : Q a ∈ pointSet Q := ⟨a, rfl⟩
    have hdRange : Q d ∈ pointSet Q := ⟨d, rfl⟩
    have hqRange : Q q ∈ pointSet Q := ⟨q, rfl⟩
    have hadQ : Q a ≠ Q d := Q.injective.ne had
    have hspan := hcol.mem_affineSpan_of_mem_of_ne
      haRange hdRange hqRange hadQ
    apply mem_lineSupport.mpr
    change cfg q.1 ∈ lineOfPair cfg A
    have hlinePair : lineOfPair cfg A =
        affineSpan ℝ ({cfg a.1, cfg d.1} : Set Point2) := by
      simpa [A] using lineOfPair_pair cfg had'
    rw [hlinePair]
    simpa [Q, finsetRestrictionConfiguration] using hspan
  let K : GeometricBlock cfg := Sum.inl L
  have hOsub : O ⊆ S.support K := by
    intro x hx
    exact hall ⟨x, hx⟩
  have hKlower : 8 ≤ (S.support K).card := by
    rw [← hOcard]
    exact Finset.card_le_card hOsub
  have hcap := halfBlockCap_of_circleCount_lt_v1UniformTarget
    cfg hadm (by omega) hcount
  have hKupper : (S.support K).card ≤ 8 := by
    have hlarge : 3 ≤ ((blockSystem cfg).support K).card := by
      change 3 ≤ (S.support K).card
      omega
    have h := hcap K hlarge
    change (S.support K).card ≤ Fintype.card alpha / 2 at h
    rw [h16] at h
    norm_num at h
    exact h
  have hKcard : (S.support K).card = 8 := by omega
  have hpencil := richLinePencilBound_le_totalCircleCount
    (blockSystem cfg) K (by rfl)
  rw [totalCircleCount_eq_card_determinedCircle,
    ← Erdos506.V3.circleCount_eq_card_determinedCircle] at hpencil
  rw [h16, hKcard] at hpencil
  rw [h16] at hcount
  norm_num [richBlockPencilBound, Nat.choose,
    Erdos506.v1UniformTarget] at hpencil hcount
  omega

private theorem sixteenEightCircle_outsider_circle_of_notConcyclic
    (cfg : Configuration alpha) (b : GeometricBlock cfg)
    (hOcard : (blockOutsiders (blockSystem cfg) b).card = 8)
    (hcap : BlockSizeCap (blockSystem cfg) 8)
    (hnot : ¬ NotConcyclic (finsetRestrictionConfiguration cfg
      (blockOutsiders (blockSystem cfg) b))) :
    ∃ d : DeterminedCircle cfg,
      circleTrace cfg d.1 = blockOutsiders (blockSystem cfg) b := by
  classical
  let S := blockSystem cfg
  let O := blockOutsiders S b
  let Q := finsetRestrictionConfiguration cfg O
  have hOcardO : O.card = 8 := by
    simpa only [O, S] using hOcard
  have hQcard : Fintype.card (BlockOutsider S b) = 8 := by
    rw [Fintype.card_coe, hOcardO]
  change ¬ (∀ c : ProperCircle,
    (circleTrace Q c).card < Fintype.card (BlockOutsider S b)) at hnot
  push_neg at hnot
  obtain ⟨omega, homega⟩ := hnot
  have htraceLe : (circleTrace Q omega).card ≤
      Fintype.card (BlockOutsider S b) := by
    simpa using Finset.card_le_univ (circleTrace Q omega)
  have htraceCard : (circleTrace Q omega).card = 8 := by omega
  have htraceUniv : circleTrace Q omega = Finset.univ := by
    apply Finset.eq_univ_of_card
    change (circleTrace Q omega).card =
      Fintype.card (BlockOutsider S b)
    exact htraceCard.trans hQcard.symm
  have hunivThree : 3 ≤
      (Finset.univ : Finset (BlockOutsider S b)).card := by
    rw [Finset.card_univ, Fintype.card_coe, hOcardO]
    norm_num
  obtain ⟨A, hAsub, hAcard⟩ :=
    Finset.exists_subset_card_eq hunivThree
  have hAnon : IsNoncollinear Q A := by
    by_contra hcol
    apply not_triple_subset_circle_of_collinear
      Q ⟨A, hAcard⟩ hcol omega
    intro q hq
    rw [htraceUniv]
    simp
  let t : NoncollinearTriple Q :=
    ⟨A, mem_noncollinearTriples.mpr ⟨hAcard, hAnon⟩⟩
  have homegaDetermined : omega ∈ determinedCircles Q := by
    apply (mem_determinedCircles_iff Q omega).mpr
    refine ⟨t, ?_⟩
    intro q hq
    apply mem_circleTrace.mp
    rw [htraceUniv]
    simp
  let dQ : DeterminedCircle Q := ⟨omega, homegaDetermined⟩
  let d : DeterminedCircle cfg :=
    liftFinsetRestrictionDeterminedCircle cfg O dQ
  have hOsub : O ⊆ circleTrace cfg d.1 := by
    intro q hq
    let qO : BlockOutsider S b := ⟨q, hq⟩
    have hqTrace : qO ∈ circleTrace Q omega := by
      rw [htraceUniv]
      simp
    exact (mem_circleTrace_finsetRestriction_iff cfg O omega qO).mp hqTrace
  have hdThree : 3 ≤ (circleTrace cfg d.1).card := by
    have := Finset.card_le_card hOsub
    rw [hOcardO] at this
    omega
  have hdUpper : (circleTrace cfg d.1).card ≤ 8 := by
    exact hcap (Sum.inr d) hdThree
  have htraceEq : circleTrace cfg d.1 = O := by
    have hOeq : O = circleTrace cfg d.1 := by
      apply Finset.eq_of_subset_of_card_le hOsub
      rw [hOcardO]
      exact hdUpper
    exact hOeq.symm
  exact ⟨d, by simpa [O, S] using htraceEq⟩

private theorem four_mul_choose_three_le_circleSixteen_add_defect
    {Point Block : Type*} [Fintype Point] [Fintype Block]
    [DecidableEq Point]
    (S : BlockSystem Point Block) (b : Block)
    (hcard : (S.support b).card ≤ 4) :
    4 * (Nat.choose (S.support b).card 3 : Int) ≤
      16 * (if S.kind b = .circle then (1 : Int) else 0) +
        S.blockDefectContribution b := by
  cases hkind : S.kind b with
  | line =>
      have hmin := S.line_min b hkind
      have hne : (BlockKind.line : BlockKind) ≠ .circle := by decide
      interval_cases hs : (S.support b).card <;>
        norm_num [Nat.choose, BlockSystem.blockDefectContribution,
          hkind, hs, hne] at hmin hcard ⊢
  | circle =>
      have hmin := S.circle_min b hkind
      interval_cases hs : (S.support b).card <;>
        norm_num [Nat.choose, BlockSystem.blockDefectContribution,
          hkind, hs] at hmin hcard ⊢

/-- Lossless sharp split at the `(16,8)` rich-circle endpoint.  In the
admissible outsider branch both inequalities are equalities.  The only
alternative is a second determined eight-circle whose trace is exactly the
outsider half. -/
theorem FiniteWindowRichBlockResidual.sixteen_eight_circle_tight_split
    (Mel : RealPlaneMelchiorPrinciple.{u})
    (EvenArr : RealPlaneEvenArrangementPrinciple.{u})
    {cfg : Configuration alpha} (R : FiniteWindowRichBlockResidual cfg)
    (hadm : Admissible cfg)
    (hcircle : (blockSystem cfg).kind R.block = .circle)
    (h16 : Fintype.card alpha = 16)
    (height : (geometricBlockSupport cfg R.block).card = 8)
    (hcount : Erdos506.V4.circleCount cfg <
      Erdos506.v1UniformTarget (Fintype.card alpha)) :
    (Admissible (finsetRestrictionConfiguration cfg
        (blockOutsiders (blockSystem cfg) R.block)) ∧
      Erdos506.V4.circleCount (finsetRestrictionConfiguration cfg
        (blockOutsiders (blockSystem cfg) R.block)) = 17 ∧
      Erdos506.V4.circleCount cfg = 98) ∨
    ∃ d : DeterminedCircle cfg,
      circleTrace cfg d.1 = blockOutsiders (blockSystem cfg) R.block := by
  classical
  let S := blockSystem cfg
  let O := blockOutsiders S R.block
  let Q := finsetRestrictionConfiguration cfg O
  have heightS : (S.support R.block).card = 8 := by
    simpa only [S] using height
  have hOcard : O.card = 8 := by
    dsimp only [O]
    rw [card_blockOutsiders, h16, heightS]
  have hQcard : Fintype.card (BlockOutsider S R.block) = 8 := by
    rw [Fintype.card_coe, hOcard]
  have hQnon : Noncollinear Q := by
    simpa [Q, O, S] using sixteenEightCircle_outsider_noncollinear
      cfg hadm R.block h16 height hcount
  have hcap : BlockSizeCap S 8 := by
    simpa [S, h16] using halfBlockCap_of_circleCount_lt_v1UniformTarget
      cfg hadm (by omega) hcount
  by_cases hQnot : NotConcyclic Q
  · left
    have hQadm : Admissible Q := ⟨hQnon, hQnot⟩
    have hQlower : 17 ≤ Erdos506.V4.circleCount Q :=
      circleCount_ge_target_of_card_eight
        Mel EvenArr Q hQadm hQcard
    have hcorrect := richCirclePencilNumerator_add_outsiderCircleCount_le
      cfg R.block hcircle
    rw [totalCircleCount_eq_card_determinedCircle,
      ← Erdos506.V3.circleCount_eq_card_determinedCircle] at hcorrect
    change
      1 + (Fintype.card alpha - (geometricBlockSupport cfg R.block).card) *
            (Nat.choose (geometricBlockSupport cfg R.block).card 2 -
              (geometricBlockSupport cfg R.block).card / 2) +
          Erdos506.V4.circleCount Q ≤
        Erdos506.V4.circleCount cfg +
          Nat.choose
              (Fintype.card alpha -
                (geometricBlockSupport cfg R.block).card) 2 *
            ((geometricBlockSupport cfg R.block).card / 2) at hcorrect
    rw [h16, height] at hcorrect
    norm_num [Nat.choose] at hcorrect
    have hcfgUpper : Erdos506.V4.circleCount cfg ≤ 98 := by
      rw [h16] at hcount
      norm_num [Erdos506.v1UniformTarget, Nat.choose] at hcount
      omega
    have hQeq : Erdos506.V4.circleCount Q = 17 := by omega
    have hcfgEq : Erdos506.V4.circleCount cfg = 98 := by omega
    exact ⟨hQadm, hQeq, hcfgEq⟩
  · right
    simpa [Q, O, S] using
      sixteenEightCircle_outsider_circle_of_notConcyclic
        cfg R.block (by simpa [O, S] using hOcard) hcap
          (by simpa [Q, O, S] using hQnot)

/-- Two disjoint eight-circles already force at least 106 circles.  The
proof is one summed local inequality and Melchior's defect bound. -/
theorem FiniteWindowRichBlockResidual.sixteen_eight_disjointCircle_impossible
    (Mel : RealPlaneMelchiorPrinciple.{u})
    {cfg : Configuration alpha} (R : FiniteWindowRichBlockResidual cfg)
    (hadm : Admissible cfg)
    (hcircle : (blockSystem cfg).kind R.block = .circle)
    (h16 : Fintype.card alpha = 16)
    (height : (geometricBlockSupport cfg R.block).card = 8)
    (hcount : Erdos506.V4.circleCount cfg <
      Erdos506.v1UniformTarget (Fintype.card alpha))
    (d : DeterminedCircle cfg)
    (hd : circleTrace cfg d.1 =
      blockOutsiders (blockSystem cfg) R.block) : False := by
  classical
  let S := blockSystem cfg
  let O := blockOutsiders S R.block
  let delta : GeometricBlock cfg := Sum.inr d
  have heightS : (S.support R.block).card = 8 := by
    simpa only [S] using height
  have hcircleS : S.kind R.block = .circle := by
    simpa only [S] using hcircle
  have hdeltaCircle : S.kind delta = .circle := by
    rfl
  have hOcard : O.card = 8 := by
    dsimp only [O]
    rw [card_blockOutsiders, h16, heightS]
  have hdeltaCard : (S.support delta).card = 8 := by
    change (circleTrace cfg d.1).card = 8
    rw [hd]
    simpa [O, S] using hOcard
  have hdeltaNe : delta ≠ R.block := by
    intro heq
    have hsupp := congrArg S.support heq
    have hdeltaO : S.support delta = O := by
      change circleTrace cfg d.1 = O
      simpa only [O, S] using hd
    have hDO : S.support R.block = O := by
      exact hsupp.symm.trans hdeltaO
    have hONonempty : O.Nonempty := by
      apply Finset.nonempty_iff_ne_empty.mpr
      intro hempty
      rw [hempty] at hOcard
      simp at hOcard
    obtain ⟨q, hqO⟩ := hONonempty
    have hqNot : q ∉ S.support R.block := by
      exact mem_blockOutsiders.mp hqO
    exact hqNot (by rw [hDO]; exact hqO)
  have hsmall (a : GeometricBlock cfg)
      (ha : a ≠ R.block) (hdelta : a ≠ delta) :
      (S.support a).card ≤ 4 := by
    have hleft := S.distinct_block_inter_card_lt_three ha
    have hright := S.distinct_block_inter_card_lt_three hdelta
    have hcover : S.support a ⊆
        (S.support a ∩ S.support R.block) ∪
          (S.support a ∩ S.support delta) := by
      intro q hq
      by_cases hqBase : q ∈ S.support R.block
      · exact Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨hq, hqBase⟩)
      · have hqO : q ∈ O := by
          exact mem_blockOutsiders.mpr hqBase
        have hqDelta : q ∈ S.support delta := by
          change q ∈ circleTrace cfg d.1
          rw [hd]
          simpa [O, S] using hqO
        exact Finset.mem_union_right _
          (Finset.mem_inter.mpr ⟨hq, hqDelta⟩)
    calc
      (S.support a).card ≤
          ((S.support a ∩ S.support R.block) ∪
            (S.support a ∩ S.support delta)).card :=
        Finset.card_le_card hcover
      _ ≤ (S.support a ∩ S.support R.block).card +
          (S.support a ∩ S.support delta).card :=
        Finset.card_union_le _ _
      _ ≤ 4 := by omega
  have hlocal (a : GeometricBlock cfg) :
      4 * (Nat.choose (S.support a).card 3 : Int) ≤
        16 * (if S.kind a = .circle then (1 : Int) else 0) +
          S.blockDefectContribution a +
          (if a = R.block then (176 : Int) else 0) +
          (if a = delta then (176 : Int) else 0) := by
    by_cases ha : a = R.block
    · subst a
      simp only [if_pos rfl, if_neg (Ne.symm hdeltaNe)]
      simp only [BlockSystem.blockDefectContribution, hcircleS, heightS]
      norm_num [Nat.choose]
    by_cases hdelta : a = delta
    · subst a
      simp only [if_neg hdeltaNe, if_pos rfl]
      simp only [BlockSystem.blockDefectContribution, hdeltaCircle, hdeltaCard]
      norm_num [Nat.choose]
    · simpa [ha, hdelta] using
        four_mul_choose_three_le_circleSixteen_add_defect
          S a (hsmall a ha hdelta)
  have htripleNat := S.triple_partition
  rw [h16] at htripleNat
  norm_num [Nat.choose] at htripleNat
  have htriple :
      (∑ a : GeometricBlock cfg,
        (Nat.choose (S.support a).card 3 : Int)) = 560 := by
    rw [Fintype.sum_sum_type]
    exact_mod_cast htripleNat
  have htripleFour :
      (∑ a : GeometricBlock cfg,
        4 * (Nat.choose (S.support a).card 3 : Int)) = 2240 := by
    rw [← Finset.mul_sum, htriple]
    norm_num
  have hcircleSum :
      (∑ a : GeometricBlock cfg,
        16 * (if S.kind a = .circle then (1 : Int) else 0)) =
          16 * (S.totalCircleCount : Int) := by
    rw [← Finset.mul_sum, ← Finset.sum_filter]
    simp [BlockSystem.totalCircleCount, BlockSystem.blocksOfKind]
  have hbaseSum :
      (∑ a : GeometricBlock cfg,
        if a = R.block then (176 : Int) else 0) = 176 := by
    simp
  have hdeltaSum :
      (∑ a : GeometricBlock cfg,
        if a = delta then (176 : Int) else 0) = 176 := by
    simp
  have hsum := Finset.sum_le_sum (s := Finset.univ)
    (fun a _ha => hlocal a)
  simp only [Finset.sum_add_distrib] at hsum
  rw [htripleFour, hcircleSum,
    ← S.defectRow_eq_sum_blockDefectContribution,
    hbaseSum, hdeltaSum] at hsum
  have hdefect := rowD_le_n_mul_n_sub_four_of_realPlaneMelchior
    Mel cfg hadm (by omega)
  change S.defectRow ≤
    (Fintype.card alpha : Int) * ((Fintype.card alpha : Int) - 4)
      at hdefect
  rw [h16] at hdefect
  norm_num at hdefect
  rw [totalCircleCount_eq_card_determinedCircle,
    ← Erdos506.V3.circleCount_eq_card_determinedCircle] at hsum
  rw [h16] at hcount
  norm_num [Erdos506.v1UniformTarget, Nat.choose] at hcount
  omega

/-- After the disjoint-circle branch is removed, the whole `(16,8)` circle
residual is the single sharp corrected-pencil equality case. -/
theorem FiniteWindowRichBlockResidual.sixteen_eight_circle_reduces_to_tight_outsiders
    (Mel : RealPlaneMelchiorPrinciple.{u})
    (EvenArr : RealPlaneEvenArrangementPrinciple.{u})
    {cfg : Configuration alpha} (R : FiniteWindowRichBlockResidual cfg)
    (hadm : Admissible cfg)
    (hcircle : (blockSystem cfg).kind R.block = .circle)
    (h16 : Fintype.card alpha = 16)
    (height : (geometricBlockSupport cfg R.block).card = 8)
    (hcount : Erdos506.V4.circleCount cfg <
      Erdos506.v1UniformTarget (Fintype.card alpha)) :
    Admissible (finsetRestrictionConfiguration cfg
        (blockOutsiders (blockSystem cfg) R.block)) ∧
      Erdos506.V4.circleCount (finsetRestrictionConfiguration cfg
        (blockOutsiders (blockSystem cfg) R.block)) = 17 ∧
      Erdos506.V4.circleCount cfg = 98 := by
  rcases R.sixteen_eight_circle_tight_split
      Mel EvenArr hadm hcircle h16 height hcount with htight | ⟨d, hd⟩
  · exact htight
  · exact (R.sixteen_eight_disjointCircle_impossible
      Mel hadm hcircle h16 height hcount d hd).elim

/-- The formerly one-unit-short `(16,8)` rich-circle endpoint. -/
theorem FiniteWindowRichBlockResidual.circle_impossible_of_sixteen_eight
    (Mel : RealPlaneMelchiorPrinciple.{u})
    (EvenArr : RealPlaneEvenArrangementPrinciple.{u})
    {cfg : Configuration alpha} (R : FiniteWindowRichBlockResidual cfg)
    (hadm : Admissible cfg)
    (hcircle : (blockSystem cfg).kind R.block = .circle)
    (h16 : Fintype.card alpha = 16)
    (height : (geometricBlockSupport cfg R.block).card = 8)
    (hcount : Erdos506.V4.circleCount cfg <
      Erdos506.v1UniformTarget (Fintype.card alpha)) : False := by
  obtain ⟨_hQadm, hQcount, hcfgCount⟩ :=
    R.sixteen_eight_circle_reduces_to_tight_outsiders
      Mel EvenArr hadm hcircle h16 height hcount
  have E := sixteenEightCirclePencilEqualityData_of_counts
    cfg R.block hcircle h16 height hQcount hcfgCount
  have heightS : ((blockSystem cfg).support R.block).card = 8 := by
    simpa only using height
  have hout : (blockOutsiders (blockSystem cfg) R.block).card = 8 := by
    rw [card_blockOutsiders, h16, heightS]
  exact sixteenEightCirclePencilEqualityData_impossible
    (blockSystem cfg) R.block height hout E

end Erdos506.V1
