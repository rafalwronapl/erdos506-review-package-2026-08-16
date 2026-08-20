import Erdos506.Block.SignedRows
import Erdos506.Finite.Bonferroni

/-!
# Relative signed rows for abstract block systems

This file packages two finite reorganizations used by the small-order
arguments.  The first restricts the pivot row to a chosen set of labels.
The second writes the global defect row directly as a sum over blocks.
-/

namespace Erdos506.Block

open scoped BigOperators

namespace BlockSystem

variable {Point Block : Type*} [Fintype Point] [Fintype Block]
  [DecidableEq Point]

/-- The pivot moment carried by a selected set `D`.  Only supports of size at
least three participate, exactly as in `pivotSigma`. -/
def subsetPivotMoment (S : BlockSystem Point Block) (D : Finset Point) : ℤ :=
  ∑ b : Block,
    if 3 ≤ (S.support b).card then
      ((S.support b ∩ D).card : ℤ) *
        (4 - ((S.support b).card : ℤ))
    else 0

/-- Restricting the pivot row to `D` is the sum of the local pivot slacks,
with the three units removed in `pivotSigma` restored at every point. -/
theorem subsetPivotMoment_eq (S : BlockSystem Point Block)
    (D : Finset Point) :
    S.subsetPivotMoment D =
      3 * (D.card : ℤ) + ∑ p ∈ D, S.pivotSigma p := by
  classical
  have hpivot (p : Point) :
      S.pivotSigma p =
        (∑ b : Block,
          if p ∈ S.support b ∧ 3 ≤ (S.support b).card then
            4 - ((S.support b).card : ℤ)
          else 0) - 3 := by
    calc
      S.pivotSigma p =
          (∑ b : NontrivialBlockAt S p,
            (4 - ((S.support b.1).card : ℤ))) - 3 :=
        S.pivotSigma_eq_sum_nontrivialBlockAt_sub_three p
      _ = (∑ b : Block,
          if p ∈ S.support b ∧ 3 ≤ (S.support b).card then
            4 - ((S.support b).card : ℤ)
          else 0) - 3 := by
        rw [S.sum_nontrivialBlockAt_weight_indicator p
          (fun b => 4 - ((S.support b).card : ℤ))]
  rw [subsetPivotMoment]
  calc
    (∑ b : Block,
        if 3 ≤ (S.support b).card then
          ((S.support b ∩ D).card : ℤ) *
            (4 - ((S.support b).card : ℤ))
        else 0) =
        ∑ b : Block, ∑ p ∈ D,
          if p ∈ S.support b ∧ 3 ≤ (S.support b).card then
            4 - ((S.support b).card : ℤ)
          else 0 := by
      apply Fintype.sum_congr
      intro b
      by_cases hthree : 3 ≤ (S.support b).card
      · simp only [hthree, and_true, ↓reduceIte]
        rw [← Finset.sum_filter]
        have hfilter :
            D.filter (fun p => p ∈ S.support b) = D ∩ S.support b := by
          ext p
          simp
        rw [hfilter]
        simp
        rw [Finset.inter_comm D (S.support b)]
        ring
      · simp [hthree]
    _ = ∑ p ∈ D, ∑ b : Block,
          if p ∈ S.support b ∧ 3 ≤ (S.support b).card then
            4 - ((S.support b).card : ℤ)
          else 0 := by
      rw [Finset.sum_comm]
    _ = 3 * (D.card : ℤ) + ∑ p ∈ D, S.pivotSigma p := by
      simp_rw [hpivot]
      simp
      ring

/-- Nonnegative local pivot slacks force the selected pivot moment to be at
least three times the size of the selected set. -/
theorem three_mul_card_le_subsetPivotMoment
    (S : BlockSystem Point Block) (D : Finset Point)
    (hnonneg : ∀ p ∈ D, 0 ≤ S.pivotSigma p) :
    3 * (D.card : ℤ) ≤ S.subsetPivotMoment D := by
  rw [S.subsetPivotMoment_eq D]
  have hsum : 0 ≤ ∑ p ∈ D, S.pivotSigma p := by
    exact Finset.sum_nonneg fun p hp => hnonneg p hp
  omega

/-- The contribution of one tagged block to the global defect row. -/
def blockDefectContribution (S : BlockSystem Point Block) (b : Block) : ℤ :=
  match S.kind b with
  | .circle =>
      ((S.support b).card : ℤ) * (((S.support b).card : ℤ) - 4)
  | .line =>
      2 * ((S.support b).card : ℤ) * (((S.support b).card : ℤ) - 2)

private theorem sum_kind_nontrivial_weight
    (S : BlockSystem Point Block) (k : BlockKind) (w : ℕ → ℤ)
    (hzero : ∀ b, S.kind b = k → ¬3 ≤ (S.support b).card →
      w (S.support b).card = 0) :
    (∑ s ∈ S.nontrivialSizes,
        w s * ((S.blocksOfKindSize k s).card : ℤ)) =
      ∑ b ∈ S.blocksOfKind k, w (S.support b).card := by
  classical
  let F : Finset Block :=
    (S.blocksOfKind k).filter fun b => 3 ≤ (S.support b).card
  have hmaps : ∀ b ∈ F, (S.support b).card ∈ S.nontrivialSizes := by
    intro b hb
    have hb' := Finset.mem_filter.mp hb
    exact Finset.mem_Icc.mpr
      ⟨hb'.2, S.support_card_le_point_card b⟩
  have hgroup := Finset.sum_fiberwise_of_maps_to hmaps
    (fun b : Block => w (S.support b).card)
  calc
    (∑ s ∈ S.nontrivialSizes,
        w s * ((S.blocksOfKindSize k s).card : ℤ)) =
        ∑ s ∈ S.nontrivialSizes,
          ∑ b ∈ F with (S.support b).card = s,
            w (S.support b).card := by
      apply Finset.sum_congr rfl
      intro s hs
      have hs3 : 3 ≤ s := (Finset.mem_Icc.mp hs).1
      have hfiber :
          F.filter (fun b => (S.support b).card = s) =
            S.blocksOfKindSize k s := by
        ext b
        constructor
        · intro hb
          have hb' := Finset.mem_filter.mp hb
          have hbF := Finset.mem_filter.mp hb'.1
          exact S.mem_blocksOfKindSize.mpr
            ⟨S.mem_blocksOfKind.mp hbF.1, hb'.2⟩
        · intro hb
          have hb' := S.mem_blocksOfKindSize.mp hb
          apply Finset.mem_filter.mpr
          refine ⟨Finset.mem_filter.mpr
            ⟨S.mem_blocksOfKind.mpr hb'.1, ?_⟩, hb'.2⟩
          rw [hb'.2]
          exact hs3
      rw [hfiber]
      calc
        w s * ((S.blocksOfKindSize k s).card : ℤ) =
            ((S.blocksOfKindSize k s).card : ℤ) * w s := by ring
        _ = ∑ _b ∈ S.blocksOfKindSize k s, w s := by simp
        _ = ∑ b ∈ S.blocksOfKindSize k s,
            w (S.support b).card := by
          apply Finset.sum_congr rfl
          intro b hb
          rw [(S.mem_blocksOfKindSize.mp hb).2]
    _ = ∑ b ∈ F, w (S.support b).card := hgroup
    _ = ∑ b ∈ S.blocksOfKind k,
        if 3 ≤ (S.support b).card then w (S.support b).card else 0 := by
      simp [F, Finset.sum_filter]
    _ = ∑ b ∈ S.blocksOfKind k, w (S.support b).card := by
      apply Finset.sum_congr rfl
      intro b hb
      by_cases hthree : 3 ≤ (S.support b).card
      · simp [hthree]
      · simp [hthree, hzero b (S.mem_blocksOfKind.mp hb) hthree]

/-- The size-grouped definition of `defectRow` is exactly the sum of the
corresponding contribution over all tagged blocks.  A two-point line is
outside `nontrivialSizes`, but its contribution is zero. -/
theorem defectRow_eq_sum_blockDefectContribution
    (S : BlockSystem Point Block) :
    S.defectRow = ∑ b : Block, S.blockDefectContribution b := by
  classical
  let wcircle : ℕ → ℤ := fun s => (s : ℤ) * ((s : ℤ) - 4)
  let wline : ℕ → ℤ := fun s => 2 * (s : ℤ) * ((s : ℤ) - 2)
  have hcircle := S.sum_kind_nontrivial_weight .circle wcircle (by
    intro b hb hsmall
    exact (hsmall (S.circle_min b hb)).elim)
  have hline := S.sum_kind_nontrivial_weight .line wline (by
    intro b hb hsmall
    have hmin := S.line_min b hb
    have hcard : (S.support b).card = 2 := by omega
    simp [wline, hcard])
  unfold defectRow
  change
    (∑ s ∈ S.nontrivialSizes,
        wcircle s * ((S.blocksOfKindSize .circle s).card : ℤ)) +
      (∑ s ∈ S.nontrivialSizes,
        wline s * ((S.blocksOfKindSize .line s).card : ℤ)) = _
  rw [hcircle, hline]
  calc
    (∑ b ∈ S.blocksOfKind .circle, wcircle (S.support b).card) +
        ∑ b ∈ S.blocksOfKind .line, wline (S.support b).card =
        (∑ b : Block,
          if S.kind b = .circle then wcircle (S.support b).card else 0) +
        ∑ b : Block,
          if S.kind b = .line then wline (S.support b).card else 0 := by
      simp [blocksOfKind, Finset.sum_filter]
    _ = ∑ b : Block, S.blockDefectContribution b := by
      rw [← Finset.sum_add_distrib]
      apply Fintype.sum_congr
      intro b
      cases hkind : S.kind b <;>
        simp [hkind, wcircle, wline, blockDefectContribution]

/-- If every block in `F` meets `D` in two points, then its outside pairs
have the matching capacity forced by unique triple ownership.  For each
fixed outside pair, the corresponding two-point traces in `D` are pairwise
disjoint, so at most `D.card / 2` blocks can contain that pair. -/
theorem relative_two_two_capacity
    (S : BlockSystem Point Block) (D : Finset Point) (F : Finset Block)
    (htwo : ∀ b ∈ F, (S.support b ∩ D).card = 2) :
    (∑ b ∈ F, Nat.choose (S.support b \ D).card 2) ≤
      D.card / 2 * Nat.choose (Fintype.card Point - D.card) 2 := by
  classical
  let Q : Finset (Finset Point) :=
    (Finset.univ \ D).powersetCard 2
  let BFor : Finset Point → Finset Block := fun A =>
    F.filter fun b => A ⊆ S.support b \ D
  let insidePairs : Finset Point → Finset (Finset Point) := fun A =>
    (BFor A).image fun b => S.support b ∩ D

  have hsupportDisjoint (A : Finset Point) (hA : A ∈ Q)
      {b c : Block} (hb : b ∈ BFor A) (hc : c ∈ BFor A)
      (hbc : b ≠ c) :
      Disjoint (S.support b ∩ D) (S.support c ∩ D) := by
    have hAspec := Finset.mem_powersetCard.mp hA
    have hAcard : A.card = 2 := hAspec.2
    have hbA : A ⊆ S.support b \ D :=
      (Finset.mem_filter.mp hb).2
    have hcA : A ⊆ S.support c \ D :=
      (Finset.mem_filter.mp hc).2
    rw [Finset.disjoint_left]
    intro z hzb hzc
    have hzD : z ∈ D := (Finset.mem_inter.mp hzb).2
    have hznotA : z ∉ A := by
      intro hzA
      exact (Finset.mem_sdiff.mp (hbA hzA)).2 hzD
    have hsub : insert z A ⊆ S.support b ∩ S.support c := by
      intro w hw
      rcases Finset.mem_insert.mp hw with rfl | hwA
      · exact Finset.mem_inter.mpr
          ⟨(Finset.mem_inter.mp hzb).1, (Finset.mem_inter.mp hzc).1⟩
      · exact Finset.mem_inter.mpr
          ⟨(Finset.mem_sdiff.mp (hbA hwA)).1,
            (Finset.mem_sdiff.mp (hcA hwA)).1⟩
    have hcard : (insert z A).card = 3 := by
      rw [Finset.card_insert_of_notMem hznotA, hAcard]
    have hle := Finset.card_le_card hsub
    have hlt := S.distinct_block_inter_card_lt_three hbc
    omega

  have hcapacity (A : Finset Point) (hA : A ∈ Q) :
      (BFor A).card ≤ D.card / 2 := by
    have hsub : ∀ p ∈ insidePairs A, p ⊆ D := by
      intro p hp
      obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hp
      exact Finset.inter_subset_right
    have hpair : ∀ p ∈ insidePairs A, p.card = 2 := by
      intro p hp
      obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hp
      exact htwo b (Finset.mem_filter.mp hb).1
    have hdisj :
        ((insidePairs A : Finset (Finset Point)) :
          Set (Finset Point)).PairwiseDisjoint id := by
      intro p hp q hq hpq
      obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hp
      obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hq
      have hbc : b ≠ c := by
        intro hbc
        subst c
        exact hpq rfl
      exact hsupportDisjoint A hA hb hc hbc
    have hinj : Set.InjOn (fun b => S.support b ∩ D) (BFor A) := by
      intro b hb c hc heq
      by_contra hbc
      have hdis := hsupportDisjoint A hA hb hc hbc
      have hself : Disjoint (S.support b ∩ D) (S.support b ∩ D) := by
        simpa [heq] using hdis
      have hempty : S.support b ∩ D = ∅ := disjoint_self.mp hself
      have hbF : b ∈ F := (Finset.mem_filter.mp hb).1
      have := htwo b hbF
      rw [hempty] at this
      simp at this
    have hcard : (insidePairs A).card = (BFor A).card := by
      exact Finset.card_image_iff.mpr hinj
    have hmatch := Erdos506.Finite.card_le_half_of_pairwiseDisjoint_pairs
      D (insidePairs A) hsub hpair hdisj
    rwa [hcard] at hmatch

  have hflagCard (b : Block) :
      Nat.choose (S.support b \ D).card 2 =
        (Q.filter fun A => A ⊆ S.support b \ D).card := by
    rw [← Finset.card_powersetCard]
    apply congrArg Finset.card
    ext A
    simp only [Q, Finset.mem_filter, Finset.mem_powersetCard]
    constructor
    · intro hA
      refine ⟨⟨?_, hA.2⟩, hA.1⟩
      intro p hp
      exact Finset.mem_sdiff.mpr
        ⟨Finset.mem_univ p, (Finset.mem_sdiff.mp (hA.1 hp)).2⟩
    · rintro ⟨hAQ, hsub⟩
      exact ⟨hsub, hAQ.2⟩

  calc
    (∑ b ∈ F, Nat.choose (S.support b \ D).card 2) =
        ∑ b ∈ F, (Q.filter fun A => A ⊆ S.support b \ D).card := by
      apply Finset.sum_congr rfl
      intro b hb
      exact hflagCard b
    _ = ∑ b ∈ F, ∑ A ∈ Q,
        if A ⊆ S.support b \ D then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro b hb
      exact Finset.card_filter _ Q
    _ = ∑ A ∈ Q, ∑ b ∈ F,
        if A ⊆ S.support b \ D then 1 else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ A ∈ Q, (BFor A).card := by
      apply Finset.sum_congr rfl
      intro A hA
      symm
      exact Finset.card_filter _ F
    _ ≤ ∑ _A ∈ Q, D.card / 2 := by
      apply Finset.sum_le_sum
      intro A hA
      exact hcapacity A hA
    _ = D.card / 2 * Nat.choose (Fintype.card Point - D.card) 2 := by
      simp [Q, Finset.card_sdiff_of_subset (Finset.subset_univ D),
        Nat.mul_comm]

end BlockSystem
end Erdos506.Block
