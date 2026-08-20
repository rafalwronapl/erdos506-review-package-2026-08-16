import Erdos506.V1.LangerApplicationOutsiderCirclePencilFinish
import Erdos506.V1.Eleven
import Erdos506.V1.Twelve

/-!
# Outsider correction for the rich-circle finite-window tail

This is the circle-base analogue of the rich-line outsider correction.  The
only extra point is that a circle base may lose some base pairs to line
owners, so the pencil sizes have a common lower bound rather than a common
exact size.
-/

namespace Erdos506.V1

open Erdos506.Block
open Erdos506.Block.BlockSystem
open Erdos506.Finite
open Erdos506.Incidence
open Erdos506.V4

open scoped BigOperators

universe u v

section LowerBoundMultiBonferroni

variable {Iota Beta : Type*} [DecidableEq Iota] [DecidableEq Beta]

private theorem lower_family_degree_sum
    (I : Finset Iota) (F : Iota → Finset Beta) :
    (∑ x ∈ I.biUnion F, (I.filter fun i => x ∈ F i).card) =
      ∑ i ∈ I, (F i).card := by
  classical
  calc
    _ = ∑ x ∈ I.biUnion F, ∑ i ∈ I, if x ∈ F i then 1 else 0 := by
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
        apply Finset.eq_of_subset_of_card_le
        · intro x hx
          exact (Finset.mem_filter.mp hx).2
        · exact Finset.card_le_card (by
            intro x hx
            exact Finset.mem_filter.mpr
              ⟨Finset.mem_biUnion.mpr ⟨i, hi, hx⟩, hx⟩)
      rw [heq]
      simp

private theorem lower_family_binomial_degree_fubini
    (I : Finset Iota) (F : Iota → Finset Beta) (r : ℕ) :
    (∑ A ∈ I.powersetCard r,
        ((I.biUnion F).filter fun x => ∀ i ∈ A, x ∈ F i).card) =
      ∑ x ∈ I.biUnion F,
        Nat.choose ((I.filter fun i => x ∈ F i).card) r := by
  classical
  calc
    _ = ∑ A ∈ I.powersetCard r, ∑ x ∈ I.biUnion F,
          if (∀ i ∈ A, x ∈ F i) then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro A _hA
      rw [Finset.card_eq_sum_ones, Finset.sum_filter]
    _ = ∑ x ∈ I.biUnion F, ∑ A ∈ I.powersetCard r,
          if (∀ i ∈ A, x ∈ F i) then 1 else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ x ∈ I.biUnion F,
        ((I.filter fun i => x ∈ F i).powersetCard r).card := by
      apply Finset.sum_congr rfl
      intro x _hx
      rw [powersetCard_filter_eq]
      rw [Finset.card_eq_sum_ones, Finset.sum_filter]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro x _hx
      rw [Finset.card_powersetCard]

private theorem lower_family_pair_moment_le
    (I : Finset Iota) (F : Iota → Finset Beta) (h : ℕ)
    (hinter : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → (F i ∩ F j).card ≤ h) :
    (∑ x ∈ I.biUnion F,
        Nat.choose ((I.filter fun i => x ∈ F i).card) 2) ≤
      Nat.choose I.card 2 * h := by
  classical
  rw [← lower_family_binomial_degree_fubini I F 2]
  calc
    _ ≤ ∑ _A ∈ I.powersetCard 2, h := by
      apply Finset.sum_le_sum
      intro A hA
      have hAspec := Finset.mem_powersetCard.mp hA
      obtain ⟨i, j, hij, hAeq⟩ := Finset.card_eq_two.mp hAspec.2
      have hi : i ∈ I := hAspec.1 (by simp [hAeq])
      have hj : j ∈ I := hAspec.1 (by simp [hAeq])
      have heq :
          ((I.biUnion F).filter fun x => ∀ k ∈ A, x ∈ F k) =
            F i ∩ F j := by
        ext x
        constructor
        · intro hx
          have hall := (Finset.mem_filter.mp hx).2
          exact Finset.mem_inter.mpr
            ⟨hall i (by simp [hAeq]), hall j (by simp [hAeq])⟩
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

private theorem lower_degree_le_one_add_choose_two (d : ℕ) (hd : 1 ≤ d) :
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

private theorem lower_degree_add_one_le_one_add_choose_two (d : ℕ)
    (hd : 3 ≤ d) : d + 1 ≤ 1 + Nat.choose d 2 := by
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

/-- Distinguished elements may be added to a two-term Bonferroni lower
bound even when family sizes are only bounded below. -/
theorem card_biUnion_union_distinguished_lower_of_card_ge
    (I : Finset Iota) (F : Iota → Finset Beta) (D : Finset Beta)
    (a h : ℕ)
    (hcard : ∀ i ∈ I, a ≤ (F i).card)
    (hinter : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → (F i ∩ F j).card ≤ h)
    (hdist : ∀ x ∈ D, x ∈ I.biUnion F →
      3 ≤ (I.filter fun i => x ∈ F i).card) :
    I.card * a + D.card ≤
      ((I.biUnion F) ∪ D).card + Nat.choose I.card 2 * h := by
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
      exact lower_degree_add_one_le_one_add_choose_two _ (hdist x hxD hx)
    · simp only [hxD, if_false, Nat.add_zero]
      exact lower_degree_le_one_add_choose_two _ (hdegPos x hx)
  have hsum :
      (∑ x ∈ U, (deg x + (if x ∈ D then 1 else 0))) ≤
        ∑ x ∈ U, (1 + Nat.choose (deg x) 2) := by
    apply Finset.sum_le_sum
    intro x hx
    exact hpoint x hx
  have hfirst : I.card * a ≤ ∑ x ∈ U, deg x := by
    rw [lower_family_degree_sum I F]
    calc
      I.card * a = ∑ _i ∈ I, a := by simp
      _ ≤ ∑ i ∈ I, (F i).card := by
        apply Finset.sum_le_sum
        intro i hi
        exact hcard i hi
  have hindicator :
      (∑ x ∈ U, if x ∈ D then 1 else 0) = (U ∩ D).card := by
    rw [← Finset.sum_filter]
    have heq : U.filter (fun x => x ∈ D) = U ∩ D := by
      ext x
      simp
    rw [heq]
    simp
  have hpair := lower_family_pair_moment_le I F h hinter
  dsimp only [U, deg] at hsum hfirst hindicator hpair ⊢
  have hsum' :
      (∑ x ∈ I.biUnion F, (I.filter fun i => x ∈ F i).card) +
          ((I.biUnion F) ∩ D).card ≤
        (I.biUnion F).card +
          ∑ x ∈ I.biUnion F, (I.filter fun i => x ∈ F i).card.choose 2 := by
    simpa only [Finset.sum_add_distrib, hindicator,
      Finset.sum_const, nsmul_eq_mul, Nat.mul_one] using hsum
  have hsumNat :
      I.card * a + ((I.biUnion F) ∩ D).card ≤
        (I.biUnion F).card +
          ∑ x ∈ I.biUnion F, (I.filter fun i => x ∈ F i).card.choose 2 := by
    exact (Nat.add_le_add_right hfirst _).trans hsum'
  have hunion :
      ((I.biUnion F) ∪ D).card + ((I.biUnion F) ∩ D).card =
        (I.biUnion F).card + D.card :=
    Finset.card_union_add_card_inter (I.biUnion F) D
  have hcombined :
      I.card * a + ((I.biUnion F) ∩ D).card ≤
        (I.biUnion F).card + Nat.choose I.card 2 * h := by
    exact hsumNat.trans (Nat.add_le_add_left hpair _)
  omega

end LowerBoundMultiBonferroni

section RichCircleCorrection

variable {α : Type u} [Fintype α] [DecidableEq α]

/-- The induced outsider circle count corrects the rich-circle pencil, while
the base circle itself supplies the final separate unit. -/
theorem richCirclePencilNumerator_add_outsiderCircleCount_le
    (cfg : Configuration α) (b : GeometricBlock cfg)
    (hb : (blockSystem cfg).kind b = .circle) :
    1 + (Fintype.card α - (geometricBlockSupport cfg b).card) *
          (Nat.choose (geometricBlockSupport cfg b).card 2 -
            (geometricBlockSupport cfg b).card / 2) +
        Erdos506.V4.circleCount
          (finsetRestrictionConfiguration cfg
            (blockOutsiders (blockSystem cfg) b)) ≤
      (blockSystem cfg).totalCircleCount +
        Nat.choose
            (Fintype.card α - (geometricBlockSupport cfg b).card) 2 *
          ((geometricBlockSupport cfg b).card / 2) := by
  classical
  let S := blockSystem cfg
  let O := blockOutsiders S b
  let I : Finset (BlockOutsider S b) := Finset.univ
  let F : BlockOutsider S b → Finset (GeometricBlock cfg) := circlePencil S b
  let D := finsetRestrictionCircleBlocks cfg O
  let a := Nat.choose (S.support b).card 2 - (S.support b).card / 2
  let h := (S.support b).card / 2
  have hcard : ∀ x ∈ I, a ≤ (F x).card := by
    intro x _hx
    dsimp only [F, a]
    rw [card_circlePencil]
    exact card_circleBasePairs_lower S b x
  have hinter : ∀ x ∈ I, ∀ y ∈ I, x ≠ y →
      (F x ∩ F y).card ≤ h := by
    intro x _hx y _hy hxy
    dsimp only [F, h]
    rw [circlePencil_inter_eq_commonPencils]
    exact card_commonPencils_le_half S b x y hxy
  have hdist : ∀ d ∈ D, d ∈ I.biUnion F →
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
  have hfinite := card_biUnion_union_distinguished_lower_of_card_ge
    I F D a h hcard hinter hdist
  have hbnotU : b ∉ I.biUnion F := by
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
    have htraceSub :
        circleTrace (finsetRestrictionConfiguration cfg O) c.1 ⊆
          (Finset.univ : Finset (BlockOutsider S b)) := Finset.subset_univ _
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
  have hbnot : b ∉ (I.biUnion F) ∪ D := by
    simp only [Finset.mem_union, not_or]
    exact ⟨hbnotU, hbnotD⟩
  have hsub : insert b ((I.biUnion F) ∪ D) ⊆ S.blocksOfKind .circle := by
    intro d hd
    rcases Finset.mem_insert.mp hd with rfl | hdRest
    · exact S.mem_blocksOfKind.mpr hb
    · rcases Finset.mem_union.mp hdRest with hdU | hdD
      · rcases Finset.mem_biUnion.mp hdU with ⟨x, _hx, hxFan⟩
        exact S.mem_blocksOfKind.mpr (circlePencil_kind S b x hxFan)
      · dsimp only [D, finsetRestrictionCircleBlocks] at hdD
        obtain ⟨c, _hc, rfl⟩ := Finset.mem_image.mp hdD
        exact S.mem_blocksOfKind.mpr rfl
  have htotal := Finset.card_le_card hsub
  rw [Finset.card_insert_of_notMem hbnot] at htotal
  have hIcard : I.card = Fintype.card α - (S.support b).card := by
    dsimp only [I]
    rw [Finset.card_univ, Fintype.card_coe, card_blockOutsiders]
  have hDcard : D.card = Erdos506.V4.circleCount
      (finsetRestrictionConfiguration cfg O) :=
    card_finsetRestrictionCircleBlocks cfg O
  rw [hIcard, hDcard] at hfinite
  change ((I.biUnion F) ∪ D).card + 1 ≤ S.totalCircleCount at htotal
  change
    1 + (Fintype.card α - (S.support b).card) *
          (Nat.choose (S.support b).card 2 - (S.support b).card / 2) +
        Erdos506.V4.circleCount (finsetRestrictionConfiguration cfg O) ≤
      S.totalCircleCount +
        Nat.choose (Fintype.card α - (S.support b).card) 2 *
          ((S.support b).card / 2)
  dsimp only [a, h] at hfinite
  omega

end RichCircleCorrection

end Erdos506.V1
