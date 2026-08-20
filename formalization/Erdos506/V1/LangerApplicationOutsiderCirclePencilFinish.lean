import Erdos506.V1.LangerApplicationFifteenLineSevenFinish
import Erdos506.V1.NineComplete
import Erdos506.V1.TenFive

/-!
# Outsider-circle correction to a rich-line pencil

The circles determined by the induced outsider configuration correct the
two-term Bonferroni pencil count one-for-one.  A distinguished circle outside
the pencil union is a new circle; one inside the union contains at least three
outsider centres and therefore contributes one unit of higher-overlap slack.
-/

namespace Erdos506.V1

open Erdos506.Block
open Erdos506.Block.BlockSystem
open Erdos506.Finite
open Erdos506.Incidence
open Erdos506.V4

open scoped BigOperators

universe u v

section FiniteMultiBonferroni

variable {Iota Beta : Type*} [DecidableEq Iota] [DecidableEq Beta]

/-- First-moment Fubini for membership degrees in a finite family. -/
private theorem family_degree_sum
    (I : Finset Iota) (F : Iota → Finset Beta) :
    (∑ x ∈ I.biUnion F, (I.filter fun i => x ∈ F i).card) =
      ∑ i ∈ I, (F i).card := by
  classical
  calc
    (∑ x ∈ I.biUnion F, (I.filter fun i => x ∈ F i).card) =
        ∑ x ∈ I.biUnion F, ∑ i ∈ I, if x ∈ F i then 1 else 0 := by
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

/-- Binomial-degree Fubini, used only at degree two below. -/
private theorem family_binomial_degree_fubini
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

/-- Pairwise caps bound the second membership-degree moment. -/
private theorem family_pair_moment_le
    (I : Finset Iota) (F : Iota → Finset Beta) (h : ℕ)
    (hinter : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → (F i ∩ F j).card ≤ h) :
    (∑ x ∈ I.biUnion F,
        Nat.choose ((I.filter fun i => x ∈ F i).card) 2) ≤
      Nat.choose I.card 2 * h := by
  classical
  rw [← family_binomial_degree_fubini I F 2]
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

private theorem degree_le_one_add_choose_two (d : ℕ) (hd : 1 ≤ d) :
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

private theorem degree_add_one_le_one_add_choose_two (d : ℕ)
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

/-- Every distinguished element contributes one unit beyond the two-term
Bonferroni bound, provided an element already in the union belongs to at
least three family members. -/
theorem card_biUnion_union_distinguished_lower
    (I : Finset Iota) (F : Iota → Finset Beta) (D : Finset Beta)
    (a h : ℕ)
    (hcard : ∀ i ∈ I, (F i).card = a)
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
      exact degree_add_one_le_one_add_choose_two _ (hdist x hxD hx)
    · simp only [hxD, if_false, Nat.add_zero]
      exact degree_le_one_add_choose_two _ (hdegPos x hx)
  have hsum :
      (∑ x ∈ U, (deg x + (if x ∈ D then 1 else 0))) ≤
        ∑ x ∈ U, (1 + Nat.choose (deg x) 2) := by
    apply Finset.sum_le_sum
    intro x hx
    exact hpoint x hx
  have hfirst : (∑ x ∈ U, deg x) = I.card * a := by
    calc
      _ = ∑ i ∈ I, (F i).card := family_degree_sum I F
      _ = ∑ _i ∈ I, a := by
        apply Finset.sum_congr rfl
        intro i hi
        exact hcard i hi
      _ = I.card * a := by simp
  have hindicator :
      (∑ x ∈ U, if x ∈ D then 1 else 0) = (U ∩ D).card := by
    rw [← Finset.sum_filter]
    have heq : U.filter (fun x => x ∈ D) = U ∩ D := by
      ext x
      simp
    rw [heq]
    simp
  have hpair := family_pair_moment_le I F h hinter
  dsimp only [U, deg] at hsum hfirst hindicator hpair ⊢
  have hsumNat :
      I.card * a + ((I.biUnion F) ∩ D).card ≤
        (I.biUnion F).card +
          ∑ x ∈ I.biUnion F, (I.filter fun i => x ∈ F i).card.choose 2 := by
    simpa only [Finset.sum_add_distrib, hfirst, hindicator,
      Finset.sum_const, nsmul_eq_mul, Nat.mul_one] using hsum
  have hunion :
      ((I.biUnion F) ∪ D).card + ((I.biUnion F) ∩ D).card =
        (I.biUnion F).card + D.card :=
    Finset.card_union_add_card_inter (I.biUnion F) D
  have hcombined :
      I.card * a + ((I.biUnion F) ∩ D).card ≤
        (I.biUnion F).card + Nat.choose I.card 2 * h := by
    exact hsumNat.trans (Nat.add_le_add_left hpair _)
  omega

end FiniteMultiBonferroni

section FinsetRestriction

variable {α : Type u} [Fintype α] [DecidableEq α]

/-- Configuration induced on a finite subset of labels. -/
noncomputable def finsetRestrictionConfiguration
    (cfg : Configuration α) (D : Finset α) :
    Configuration {x // x ∈ D} where
  toFun x := cfg x.1
  inj' := by
    intro x y hxy
    apply Subtype.ext
    exact cfg.injective hxy

private theorem supportPoints_finsetRestriction_map
    (cfg : Configuration α) (D : Finset α)
    (T : Finset {x // x ∈ D}) :
    supportPoints cfg (T.map (Function.Embedding.subtype _)) =
      supportPoints (finsetRestrictionConfiguration cfg D) T := by
  ext p
  simp [supportPoints, finsetRestrictionConfiguration]

/-- Every circle determined after finite restriction is still determined in
the ambient configuration. -/
theorem determinedCircle_mem_ambient_of_finsetRestriction
    (cfg : Configuration α) (D : Finset α)
    (c : DeterminedCircle (finsetRestrictionConfiguration cfg D)) :
    c.1 ∈ determinedCircles cfg := by
  classical
  obtain ⟨t, ht⟩ :=
    (mem_determinedCircles_iff (finsetRestrictionConfiguration cfg D) c.1).mp c.2
  let T : Finset α := t.1.map (Function.Embedding.subtype _)
  have hTcard : T.card = 3 := by
    dsimp only [T]
    rw [Finset.card_map]
    exact (mem_noncollinearTriples.mp t.2).1
  have hTnon : IsNoncollinear cfg T := by
    have htNon := (mem_noncollinearTriples.mp t.2).2
    unfold IsNoncollinear at htNon ⊢
    rw [supportPoints_finsetRestriction_map]
    exact htNon
  let t' : NoncollinearTriple cfg :=
    ⟨T, mem_noncollinearTriples.mpr ⟨hTcard, hTnon⟩⟩
  apply (mem_determinedCircles_iff cfg c.1).mpr
  refine ⟨t', ?_⟩
  intro x hx
  change x ∈ T at hx
  dsimp only [T] at hx
  obtain ⟨y, hy, rfl⟩ := Finset.mem_map.mp hx
  exact ht y hy

/-- Canonical injective lift of restricted determined circles. -/
noncomputable def liftFinsetRestrictionDeterminedCircle
    (cfg : Configuration α) (D : Finset α) :
    DeterminedCircle (finsetRestrictionConfiguration cfg D) →
      DeterminedCircle cfg := fun c =>
  ⟨c.1, determinedCircle_mem_ambient_of_finsetRestriction cfg D c⟩

theorem liftFinsetRestrictionDeterminedCircle_injective
    (cfg : Configuration α) (D : Finset α) :
    Function.Injective (liftFinsetRestrictionDeterminedCircle cfg D) := by
  intro c d hcd
  apply Subtype.ext
  exact congrArg (fun z : DeterminedCircle cfg => z.1) hcd

@[simp] theorem mem_circleTrace_finsetRestriction_iff
    (cfg : Configuration α) (D : Finset α)
    (c : ProperCircle) (x : {x // x ∈ D}) :
    x ∈ circleTrace (finsetRestrictionConfiguration cfg D) c ↔
      x.1 ∈ circleTrace cfg c := by
  simp [circleTrace, finsetRestrictionConfiguration]

/-- Ambient geometric circle blocks supplied by the restricted
configuration. -/
noncomputable def finsetRestrictionCircleBlocks
    (cfg : Configuration α) (D : Finset α) :
    Finset (GeometricBlock cfg) := by
  classical
  exact Finset.univ.image fun c :
    DeterminedCircle (finsetRestrictionConfiguration cfg D) =>
      Sum.inr (liftFinsetRestrictionDeterminedCircle cfg D c)

theorem card_finsetRestrictionCircleBlocks
    (cfg : Configuration α) (D : Finset α) :
    (finsetRestrictionCircleBlocks cfg D).card =
      Erdos506.V4.circleCount (finsetRestrictionConfiguration cfg D) := by
  classical
  have hinj : Function.Injective (fun c :
      DeterminedCircle (finsetRestrictionConfiguration cfg D) =>
      (Sum.inr (liftFinsetRestrictionDeterminedCircle cfg D c) :
        GeometricBlock cfg)) := by
    intro c d hcd
    injection hcd with h
    exact liftFinsetRestrictionDeterminedCircle_injective cfg D h
  rw [finsetRestrictionCircleBlocks,
    Finset.card_image_of_injective _ hinj, Finset.card_univ,
    ← Erdos506.V3.circleCount_eq_card_determinedCircle]

end FinsetRestriction

section OutsiderCircleCorrection

variable {α : Type u} [Fintype α] [DecidableEq α]

/-- The full induced outsider circle count is an additive correction to the
rich-line pencil numerator. -/
theorem richLinePencilNumerator_add_outsiderCircleCount_le
    (cfg : Configuration α) (b : GeometricBlock cfg)
    (hb : (blockSystem cfg).kind b = .line) :
    (Fintype.card α - (geometricBlockSupport cfg b).card) *
          Nat.choose (geometricBlockSupport cfg b).card 2 +
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
  let a := Nat.choose (S.support b).card 2
  let h := (S.support b).card / 2
  have hcard : ∀ x ∈ I, (F x).card = a := by
    intro x _hx
    dsimp only [F, a]
    rw [card_circlePencil]
    have hall : circleBasePairs S b x = Finset.univ := by
      apply Finset.eq_univ_of_forall
      intro u
      exact mem_circleBasePairs.mpr
        (pencilOwner_kind_circle_of_base_line S b hb x u)
    rw [hall, Finset.card_univ, Fintype.card_coe]
    simp
  have hinter : ∀ x ∈ I, ∀ y ∈ I, x ≠ y →
      (F x ∩ F y).card ≤ h := by
    intro x _hx y _hy hxy
    have hFx : F x = circlePencil S b x := rfl
    have hFy : F y = circlePencil S b y := rfl
    have hh : h = (S.support b).card / 2 := rfl
    rw [hFx, hFy, hh, circlePencil_inter_eq_commonPencils]
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
  have hfinite := card_biUnion_union_distinguished_lower
    I F D a h hcard hinter hdist
  have hsub : (I.biUnion F) ∪ D ⊆ S.blocksOfKind .circle := by
    intro d hd
    rcases Finset.mem_union.mp hd with hdU | hdD
    · rcases Finset.mem_biUnion.mp hdU with ⟨x, _hx, hxFan⟩
      exact S.mem_blocksOfKind.mpr (circlePencil_kind S b x hxFan)
    · dsimp only [D, finsetRestrictionCircleBlocks] at hdD
      obtain ⟨c, _hc, rfl⟩ := Finset.mem_image.mp hdD
      exact S.mem_blocksOfKind.mpr rfl
  have htotal := Finset.card_le_card hsub
  have hIcard : I.card = Fintype.card α - (S.support b).card := by
    dsimp only [I]
    rw [Finset.card_univ, Fintype.card_coe, card_blockOutsiders]
  have hDcard : D.card = Erdos506.V4.circleCount
      (finsetRestrictionConfiguration cfg O) := by
    exact card_finsetRestrictionCircleBlocks cfg O
  rw [hIcard, hDcard] at hfinite
  change ((I.biUnion F) ∪ D).card ≤ S.totalCircleCount at htotal
  change
    (Fintype.card α - (geometricBlockSupport cfg b).card) *
          Nat.choose (geometricBlockSupport cfg b).card 2 +
        Erdos506.V4.circleCount
          (finsetRestrictionConfiguration cfg
            (blockOutsiders (blockSystem cfg) b)) ≤
      ((I.biUnion F) ∪ D).card +
        Nat.choose
            (Fintype.card α - (geometricBlockSupport cfg b).card) 2 *
          ((geometricBlockSupport cfg b).card / 2) at hfinite
  change ((I.biUnion F) ∪ D).card ≤ (blockSystem cfg).totalCircleCount at htotal
  omega

end OutsiderCircleCorrection

section OutsiderAdmissibility

variable {α : Type u} [Fintype α] [DecidableEq α]

/-- A block cap strictly below the number of outsiders makes the induced
outsider configuration admissible: the cap rules out both a containing line
and a containing circle. -/
theorem admissible_finsetRestriction_blockOutsiders_of_cap
    (cfg : Configuration α) (b : GeometricBlock cfg) (M : ℕ)
    (hM : 2 ≤ M) (hcap : BlockSizeCap (blockSystem cfg) M)
    (hlarge : M < (blockOutsiders (blockSystem cfg) b).card) :
    Admissible (finsetRestrictionConfiguration cfg
      (blockOutsiders (blockSystem cfg) b)) := by
  classical
  let S := blockSystem cfg
  let O := blockOutsiders S b
  let Q := finsetRestrictionConfiguration cfg O
  obtain ⟨A, hAout, hAcircle⟩ :=
    exists_circle_owned_triple_in_blockOutsiders_of_cap
      S b M hM hcap hlarge
  have hAnon : IsNoncollinear cfg A.1 := by
    by_contra hcol
    have hline : S.kind (S.tripleOwner A) = .line := by
      change geometricBlockKind (geometricTripleOwner cfg A) = .line
      simp [geometricTripleOwner, hcol]
      rfl
    rw [hAcircle] at hline
    cases hline
  have hQnon : Noncollinear Q := by
    intro hcol
    apply hAnon
    apply Collinear.subset _ hcol
    rintro p ⟨x, hxA, rfl⟩
    exact ⟨⟨x, hAout hxA⟩, rfl⟩
  have hQnotCircle : NotConcyclic Q := by
    intro c
    have hle : (circleTrace Q c).card ≤ Fintype.card (BlockOutsider S b) := by
      simpa using Finset.card_le_univ (circleTrace Q c)
    apply lt_of_le_of_ne hle
    intro heq
    have hall : circleTrace Q c = Finset.univ :=
      Finset.eq_univ_of_card _ heq
    let t : NoncollinearTriple cfg :=
      ⟨A.1, mem_noncollinearTriples.mpr ⟨A.2, hAnon⟩⟩
    have hcA : ∀ x ∈ A.1, cfg x ∈ (c.1 : Set Point2) := by
      intro x hx
      let x' : BlockOutsider S b := ⟨x, hAout hx⟩
      have hxTrace : x' ∈ circleTrace Q c := by
        rw [hall]
        simp
      exact mem_circleTrace.mp
        ((mem_circleTrace_finsetRestriction_iff cfg O c x').mp hxTrace)
    let C : DeterminedCircle cfg :=
      ⟨c, (mem_determinedCircles_iff cfg c).mpr ⟨t, hcA⟩⟩
    have houtSub : O ⊆ circleTrace cfg C.1 := by
      intro x hx
      let x' : BlockOutsider S b := ⟨x, hx⟩
      have hxTrace : x' ∈ circleTrace Q c := by
        rw [hall]
        simp
      exact (mem_circleTrace_finsetRestriction_iff cfg O c x').mp hxTrace
    have hcardSub := Finset.card_le_card houtSub
    have hlargeO : M < O.card := by
      simpa [O, S] using hlarge
    have hthree : 3 ≤ (circleTrace cfg C.1).card := by
      have hthreeO : 3 ≤ O.card := by omega
      exact hthreeO.trans hcardSub
    have hCcap := hcap (Sum.inr C) hthree
    change (circleTrace cfg C.1).card ≤ M at hCcap
    omega
  exact ⟨hQnon, hQnotCircle⟩

end OutsiderAdmissibility

section FiniteWindowEndpoints

variable {α : Type u} [Fintype α] [DecidableEq α]

/-- The nine-outsider correction closes both remaining middle line cases. -/
theorem FiniteWindowRichBlockResidual.line_impossible_of_sixteen_seven_or_seventeen_eight
    (Mel : RealPlaneMelchiorPrinciple.{u})
    (EvenArr : RealPlaneEvenArrangementPrinciple.{u})
    (Cross : RealPlaneRadicalAxisCrossBlockPrinciple.{u})
    {cfg : Configuration α} (R : FiniteWindowRichBlockResidual cfg)
    (hadm : Admissible cfg)
    (hline : (blockSystem cfg).kind R.block = .line)
    (hcase :
      (Fintype.card α = 16 ∧
        (geometricBlockSupport cfg R.block).card = 7) ∨
      (Fintype.card α = 17 ∧
        (geometricBlockSupport cfg R.block).card = 8))
    (hcount : Erdos506.V4.circleCount cfg <
      Erdos506.v1UniformTarget (Fintype.card α)) : False := by
  let S := blockSystem cfg
  let O := blockOutsiders S R.block
  let Q := finsetRestrictionConfiguration cfg O
  have hcap := halfBlockCap_of_circleCount_lt_v1UniformTarget
    cfg hadm (by omega) hcount
  have hcorrect := richLinePencilNumerator_add_outsiderCircleCount_le
    cfg R.block hline
  rcases hcase with ⟨h16, hseven⟩ | ⟨h17, height⟩
  · have hsevenS : (S.support R.block).card = 7 := by
      simpa [S] using hseven
    have hcapEight : BlockSizeCap S 8 := by
      rw [h16] at hcap
      norm_num at hcap
      exact hcap
    have hOcard : O.card = 9 := by
      dsimp only [O]
      rw [card_blockOutsiders, h16, hsevenS]
    have hQcard : Fintype.card (BlockOutsider S R.block) = 9 := by
      rw [Fintype.card_coe, hOcard]
    have hQadm : Admissible Q := by
      exact admissible_finsetRestriction_blockOutsiders_of_cap
        cfg R.block 8 (by omega) hcapEight
          (by simpa [S, O, hOcard])
    have hQcount : 25 ≤ Erdos506.V4.circleCount Q :=
      circleCount_ge_twenty_five_of_card_nine
        Mel EvenArr Cross Q hQadm hQcard
    rw [totalCircleCount_eq_card_determinedCircle,
      ← Erdos506.V3.circleCount_eq_card_determinedCircle] at hcorrect
    rw [h16, hseven] at hcorrect
    norm_num [Nat.choose] at hcorrect
    rw [h16] at hcount
    norm_num [Erdos506.v1UniformTarget, Nat.choose] at hcount
    have hQcount' : 25 ≤ Erdos506.V4.circleCount
        (finsetRestrictionConfiguration cfg
          (blockOutsiders (blockSystem cfg) R.block)) := by
      simpa [Q, O, S] using hQcount
    omega
  · have heightS : (S.support R.block).card = 8 := by
      simpa [S] using height
    have hcapEight : BlockSizeCap S 8 := by
      rw [h17] at hcap
      norm_num at hcap
      exact hcap
    have hOcard : O.card = 9 := by
      dsimp only [O]
      rw [card_blockOutsiders, h17, heightS]
    have hQcard : Fintype.card (BlockOutsider S R.block) = 9 := by
      rw [Fintype.card_coe, hOcard]
    have hQadm : Admissible Q := by
      exact admissible_finsetRestriction_blockOutsiders_of_cap
        cfg R.block 8 (by omega) hcapEight
          (by simpa [S, O, hOcard])
    have hQcount : 25 ≤ Erdos506.V4.circleCount Q :=
      circleCount_ge_twenty_five_of_card_nine
        Mel EvenArr Cross Q hQadm hQcard
    rw [totalCircleCount_eq_card_determinedCircle,
      ← Erdos506.V3.circleCount_eq_card_determinedCircle] at hcorrect
    rw [h17, height] at hcorrect
    norm_num [Nat.choose] at hcorrect
    rw [h17] at hcount
    norm_num [Erdos506.v1UniformTarget, Nat.choose] at hcount
    have hQcount' : 25 ≤ Erdos506.V4.circleCount
        (finsetRestrictionConfiguration cfg
          (blockOutsiders (blockSystem cfg) R.block)) := by
      simpa [Q, O, S] using hQcount
    omega

/-- Ten outsiders contribute their already proved thirty-three circles and
close the `(18,8)` line residual. -/
theorem FiniteWindowRichBlockResidual.line_impossible_of_eighteen_eight
    (Mel : RealPlaneMelchiorPrinciple.{u})
    (EvenArr : RealPlaneEvenArrangementPrinciple.{u})
    (Cross : RealPlaneRadicalAxisCrossBlockPrinciple.{u})
    (Kelly : RealPlaneKellyMoserPrinciple.{u})
    (U17 : RealPlaneSixCircleU17Principle.{u})
    (Geometry : RealPlaneTenFiveGeometry.{u})
    {cfg : Configuration α} (R : FiniteWindowRichBlockResidual cfg)
    (hadm : Admissible cfg)
    (hline : (blockSystem cfg).kind R.block = .line)
    (h18 : Fintype.card α = 18)
    (height : (geometricBlockSupport cfg R.block).card = 8)
    (hcount : Erdos506.V4.circleCount cfg <
      Erdos506.v1UniformTarget (Fintype.card α)) : False := by
  let S := blockSystem cfg
  let O := blockOutsiders S R.block
  let Q := finsetRestrictionConfiguration cfg O
  have heightS : (S.support R.block).card = 8 := by
    simpa [S] using height
  have hcap := halfBlockCap_of_circleCount_lt_v1UniformTarget
    cfg hadm (by omega) hcount
  have hcapNine : BlockSizeCap S 9 := by
    rw [h18] at hcap
    norm_num at hcap
    exact hcap
  have hOcard : O.card = 10 := by
    dsimp only [O]
    rw [card_blockOutsiders, h18, heightS]
  have hQcard : Fintype.card (BlockOutsider S R.block) = 10 := by
    rw [Fintype.card_coe, hOcard]
  have hQadm : Admissible Q := by
    exact admissible_finsetRestriction_blockOutsiders_of_cap
      cfg R.block 9 (by omega) hcapNine
        (by simpa [S, O, hOcard])
  have hQcount : 33 ≤ Erdos506.V4.circleCount Q :=
    circleCount_ge_thirty_three_of_card_ten
      Mel EvenArr Cross Kelly U17 Geometry Q hQadm hQcard
  have hcorrect := richLinePencilNumerator_add_outsiderCircleCount_le
    cfg R.block hline
  rw [totalCircleCount_eq_card_determinedCircle,
    ← Erdos506.V3.circleCount_eq_card_determinedCircle] at hcorrect
  rw [h18, height] at hcorrect
  norm_num [Nat.choose] at hcorrect
  rw [h18] at hcount
  norm_num [Erdos506.v1UniformTarget, Nat.choose] at hcount
  have hQcount' : 33 ≤ Erdos506.V4.circleCount
      (finsetRestrictionConfiguration cfg
        (blockOutsiders (blockSystem cfg) R.block)) := by
    simpa [Q, O, S] using hQcount
  omega

end FiniteWindowEndpoints

end Erdos506.V1
