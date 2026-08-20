import Erdos506.Finite.FanoDesign
import Erdos506.V1.SmallReduction
import Erdos506.V3.FanoPattern

/-!
# The seven-point V1 endpoint

This file closes the lower endpoint on seven selected points.  A hypothetical
configuration with at most ten circles first has block cap four and line cap
three by the rich-block pencils.  The exact `T`, `P`, and `D` rows then force
seven four-point circle blocks.  Their complementary triples form an abstract
Steiner triple system, hence have the canonical Fano labeling; the already
formalized metric obstruction to the complementary Fano circle pattern gives
the contradiction.
-/

namespace Erdos506.V1

open Erdos506.Block
open Erdos506.Block.BlockSystem
open Erdos506.Finite
open Erdos506.V4

universe u

private theorem blockCount_eq_zero_of_cap
    {Point Block : Type*} [Fintype Point] [Fintype Block]
    [DecidableEq Point]
    (S : BlockSystem Point Block) {M s : ℕ}
    (hcap : BlockSizeCap S M) (hthree : 3 ≤ s) (hlarge : M < s) :
    S.blockCount s = 0 := by
  classical
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro b hb
  have hsize := S.mem_blocksOfSize.mp hb
  have hle := hcap b (by omega)
  omega

private theorem lineCount_eq_zero_of_cap
    {Point Block : Type*} [Fintype Point] [Fintype Block]
    [DecidableEq Point]
    (S : BlockSystem Point Block) {M s : ℕ}
    (hcap : ∀ b, S.kind b = .line → (S.support b).card ≤ M)
    (hlarge : M < s) : S.lineCount s = 0 := by
  classical
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro b hb
  have hspec := S.mem_blocksOfKindSize.mp hb
  have hle := hcap b hspec.1
  omega

private theorem circleCount_eq_zero_of_cap
    {Point Block : Type*} [Fintype Point] [Fintype Block]
    [DecidableEq Point]
    (S : BlockSystem Point Block) {M s : ℕ}
    (hcap : BlockSizeCap S M) (hlarge : M < s) :
    S.circleCount s = 0 := by
  classical
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro b hb
  have hspec := S.mem_blocksOfKindSize.mp hb
  have hle := hcap b (S.circle_min b hspec.1)
  omega

/-- On seven labels, ten circles rule out every block of size at least five. -/
theorem blockSizeCap_four_of_card_seven_of_circleCount_le_ten
    {α : Type u} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (hadm : Admissible cfg)
    (hcard : Fintype.card α = 7)
    (hcount : Erdos506.V4.circleCount cfg ≤ 10) :
    BlockSizeCap (blockSystem cfg) 4 := by
  intro b hthree
  have hproper : ((blockSystem cfg).support b).card < Fintype.card α :=
    geometricBlockSupport_card_lt_of_admissible cfg hadm b
  by_contra hnot
  have hfive : 5 ≤ ((blockSystem cfg).support b).card := by omega
  have hpencil := richBlockPencilBound_le_totalCircleCount
    (blockSystem cfg) b hproper hthree
  rw [totalCircleCount_eq_card_determinedCircle,
    ← Erdos506.V3.circleCount_eq_card_determinedCircle] at hpencil
  rw [hcard] at hproper hpencil
  let s := ((blockSystem cfg).support b).card
  change richBlockPencilBound 7 s ≤ Erdos506.V4.circleCount cfg at hpencil
  change s < 7 at hproper
  change 5 ≤ s at hfive
  interval_cases s <;>
    norm_num [richBlockPencilBound, Nat.choose] at hpencil <;> omega

/-- Under the same hypothesis every determined line contains at most three
selected points.  The size-four case needs the sharper line pencil. -/
theorem lineSupport_card_le_three_of_card_seven_of_circleCount_le_ten
    {α : Type u} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (hadm : Admissible cfg)
    (hcard : Fintype.card α = 7)
    (hcount : Erdos506.V4.circleCount cfg ≤ 10) :
    ∀ b : GeometricBlock cfg,
      geometricBlockKind b = .line →
        (geometricBlockSupport cfg b).card ≤ 3 := by
  have hcap := blockSizeCap_four_of_card_seven_of_circleCount_le_ten
    cfg hadm hcard hcount
  intro b hb
  change ((blockSystem cfg).support b).card ≤ 3
  by_contra hnot
  have hthree : 3 ≤ ((blockSystem cfg).support b).card := by omega
  have hle := hcap b hthree
  have hfour : ((blockSystem cfg).support b).card = 4 := by omega
  have hpencil := richLinePencilBound_le_totalCircleCount
    (blockSystem cfg) b hb
  rw [totalCircleCount_eq_card_determinedCircle,
    ← Erdos506.V3.circleCount_eq_card_determinedCircle] at hpencil
  rw [hcard, hfour] at hpencil
  norm_num [Nat.choose] at hpencil
  omega

/-- The seven four-circle blocks, regarded as an indexed finite type. -/
abbrev FourCircleBlockV1
    {α : Type*} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) :=
  ↥((blockSystem cfg).circleBlocksOfSize 4)

noncomputable def fourCircleComplement
    {Point Block : Type*} [Fintype Point] [Fintype Block]
    [DecidableEq Point]
    (S : BlockSystem Point Block)
    (b : ↥(S.circleBlocksOfSize 4)) : Finset Point :=
  Finset.univ \ S.support b.1

private theorem fourCircleComplement_card
    {Point Block : Type*} [Fintype Point] [Fintype Block]
    [DecidableEq Point]
    (S : BlockSystem Point Block) (hcard : Fintype.card Point = 7)
    (b : ↥(S.circleBlocksOfSize 4)) :
    (fourCircleComplement S b).card = 3 := by
  have hbsize := (S.mem_blocksOfKindSize.mp b.2).2
  rw [fourCircleComplement,
    Finset.card_sdiff_of_subset (Finset.subset_univ (S.support b.1)),
    Finset.card_univ, hcard, hbsize]

private theorem fourCircleComplement_injective
    {Point Block : Type*} [Fintype Point] [Fintype Block]
    [DecidableEq Point]
    (S : BlockSystem Point Block) :
    Function.Injective (fourCircleComplement S) := by
  classical
  intro b c hcomp
  apply Subtype.ext
  by_contra hne
  have hsupp : S.support b.1 = S.support c.1 := by
    ext x
    have hx := Finset.ext_iff.mp hcomp x
    simp only [fourCircleComplement, Finset.mem_sdiff,
      Finset.mem_univ, true_and] at hx
    tauto
  have hinter := S.distinct_block_inter_card_lt_three hne
  rw [hsupp, Finset.inter_self] at hinter
  have hcsize := (S.mem_blocksOfKindSize.mp c.2).2
  omega

noncomputable def fourCircleComplementFamily
    {Point Block : Type*} [Fintype Point] [Fintype Block]
    [DecidableEq Point]
    (S : BlockSystem Point Block) : Finset (Finset Point) :=
  Finset.univ.image (fourCircleComplement S)

private theorem fourCircleComplementFamily_card
    {Point Block : Type*} [Fintype Point] [Fintype Block]
    [DecidableEq Point]
    (S : BlockSystem Point Block) :
    (fourCircleComplementFamily S).card = S.circleCount 4 := by
  classical
  rw [fourCircleComplementFamily,
    Finset.card_image_of_injective _ (fourCircleComplement_injective S),
    Finset.card_univ, Fintype.card_coe]
  rfl

private theorem fourCircleComplement_inter_lt_two
    {Point Block : Type*} [Fintype Point] [Fintype Block]
    [DecidableEq Point]
    (S : BlockSystem Point Block) (hcard : Fintype.card Point = 7)
    {b c : ↥(S.circleBlocksOfSize 4)} (hbc : b ≠ c) :
    (fourCircleComplement S b ∩ fourCircleComplement S c).card < 2 := by
  have hblocks : b.1 ≠ c.1 := by
    intro h
    exact hbc (Subtype.ext h)
  have hinter := S.distinct_block_inter_card_lt_three hblocks
  have hbsize := (S.mem_blocksOfKindSize.mp b.2).2
  have hcsize := (S.mem_blocksOfKindSize.mp c.2).2
  have hunion := Finset.card_union_add_card_inter (S.support b.1) (S.support c.1)
  have hcomp :
      (fourCircleComplement S b ∩ fourCircleComplement S c).card +
          (S.support b.1 ∪ S.support c.1).card = Fintype.card Point := by
    simp only [fourCircleComplement]
    have heq :
        (Finset.univ \ S.support b.1) ∩ (Finset.univ \ S.support c.1) =
          Finset.univ \ (S.support b.1 ∪ S.support c.1) := by
      ext x
      simp
    rw [heq]
    exact Finset.card_sdiff_add_card_eq_card
      (Finset.subset_univ (S.support b.1 ∪ S.support c.1))
  omega

/-- Equality in the complementary-triple packing yields an STS(7), without
any no-three-collinear assumption. -/
noncomputable def sevenSteinerDesignOfFourCircleBlocks
    {Point Block : Type*} [Fintype Point] [Fintype Block]
    [DecidableEq Point] [DecidableEq Block]
    (S : BlockSystem Point Block) (hcard : Fintype.card Point = 7)
    (hc4 : S.circleCount 4 = 7) :
    SevenSteinerDesign Point ↥(S.circleBlocksOfSize 4) := by
  classical
  let P := fourCircleComplementFamily S
  have hPcard : P.card = 7 := by
    simpa [P, fourCircleComplementFamily_card] using hc4
  have hsub : ∀ p ∈ P, p ⊆ (Finset.univ : Finset Point) := by
    intro p hp
    exact Finset.subset_univ p
  have htriple : ∀ p ∈ P, p.card = 3 := by
    intro p hp
    simp only [P] at hp
    rw [fourCircleComplementFamily] at hp
    obtain ⟨b, _hb, rfl⟩ := Finset.mem_image.mp hp
    exact fourCircleComplement_card S hcard b
  have hinter : ∀ p ∈ P, ∀ q ∈ P, p ≠ q → (p ∩ q).card < 2 := by
    intro p hp q hq hpq
    simp only [P] at hp hq
    rw [fourCircleComplementFamily] at hp hq
    obtain ⟨b, _hb, rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨c, _hc, rfl⟩ := Finset.mem_image.mp hq
    apply fourCircleComplement_inter_lt_two S hcard
    intro hbc
    exact hpq (congrArg (fourCircleComplement S) hbc)
  have heq : P.card * Nat.choose 3 2 =
      Nat.choose (Finset.univ : Finset Point).card 2 := by
    rw [hPcard, Finset.card_univ, hcard]
    norm_num [Nat.choose]
  exact {
    line := fourCircleComplement S
    point_card := hcard
    block_card := by
      rw [Fintype.card_coe]
      exact hc4
    line_card := fourCircleComplement_card S hcard
    pair_unique := by
      intro A hA
      obtain ⟨p, hp, huniq⟩ := existsUnique_block_of_packing_equality
        (Finset.univ : Finset Point) P 3 2 hsub htriple hinter heq hA
      simp only [P] at hp
      rw [fourCircleComplementFamily] at hp
      obtain ⟨b, _hb, hbp⟩ := Finset.mem_image.mp hp.1
      refine ⟨b, ?_, ?_⟩
      · change A ⊆ fourCircleComplement S b
        rw [hbp]
        exact hp.2
      · intro c hc
        apply fourCircleComplement_injective S
        exact (huniq (fourCircleComplement S c) ⟨by
          change fourCircleComplement S c ∈ fourCircleComplementFamily S
          rw [fourCircleComplementFamily]
          exact Finset.mem_image.mpr ⟨c, Finset.mem_univ _, rfl⟩, hc⟩).trans hbp.symm }

private def properCircleOfGeometricBlock
    {α : Type*} [Fintype α] [DecidableEq α]
    {cfg : Configuration α} :
    (b : GeometricBlock cfg) → geometricBlockKind b = .circle → ProperCircle
  | .inl _, h => by simp [geometricBlockKind] at h
  | .inr c, _ => c.1

/-- The proper circle carried by a circle-tagged size-four geometric block. -/
def fourCircleProperCircle
    {α : Type*} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (b : FourCircleBlockV1 cfg) : ProperCircle :=
  properCircleOfGeometricBlock b.1
    ((blockSystem cfg).mem_blocksOfKindSize.mp b.2).1

@[simp] theorem mem_fourCircleProperCircle_iff
    {α : Type*} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (b : FourCircleBlockV1 cfg) (x : α) :
    cfg x ∈ ((fourCircleProperCircle cfg b).1 : Set Point2) ↔
      x ∈ (blockSystem cfg).support b.1 := by
  rcases b with ⟨b, hb⟩
  cases b with
  | inl L =>
      have hkind := ((blockSystem cfg).mem_blocksOfKindSize.mp hb).1
      simp [blockSystem, geometricBlockSystem, geometricBlockKind] at hkind
  | inr c =>
      simp [fourCircleProperCircle, properCircleOfGeometricBlock,
        blockSystem, geometricBlockSystem, geometricBlockSupport]

/-- Seven four-point circle blocks cannot occur in a real V1 configuration.
The proof factors through the abstract STS(7) classifier and the canonical
Fano circle obstruction. -/
theorem circleBlockCount_four_ne_seven_of_card_seven
    {α : Type u} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (hcard : Fintype.card α = 7) :
    circleBlockCount cfg 4 ≠ 7 := by
  classical
  intro hc4
  let S := blockSystem cfg
  have hc4S : S.circleCount 4 = 7 := by
    simpa [S, circleBlockCount] using hc4
  let D := sevenSteinerDesignOfFourCircleBlocks S hcard hc4S
  obtain ⟨P, B, hcanonical⟩ := D.exists_canonical_labeling
  let p : Fin 7 → Point2 := fun i => cfg (P i)
  let Γ : Fin 7 → ProperCircle := fun j => fourCircleProperCircle cfg (B j)
  have hp : Function.Injective p := cfg.injective.comp P.injective
  have hinc : ∀ i j, p i ∈ ((Γ j).1 : Set Point2) ↔
      i ∈ Erdos506.V3.fanoCircleSupport j := by
    intro i j
    have hcomp : P i ∈ fourCircleComplement S (B j) ↔
        i ∈ fanoCanonicalLine j := by
      have h := D.mem_relabeledLines P B i j
      rw [hcanonical j] at h
      change i ∈ fanoCanonicalLine j ↔
        P i ∈ fourCircleComplement S (B j) at h
      exact h.symm
    calc
      p i ∈ ((Γ j).1 : Set Point2) ↔
          P i ∈ S.support (B j).1 := by
            change cfg (P i) ∈
                ((fourCircleProperCircle cfg (B j)).1 : Set Point2) ↔
              P i ∈ (blockSystem cfg).support (B j).1
            exact mem_fourCircleProperCircle_iff cfg (B j) (P i)
      _ ↔ P i ∉ fourCircleComplement S (B j) := by
        simp [fourCircleComplement]
      _ ↔ i ∉ fanoCanonicalLine j := not_congr hcomp
      _ ↔ i ∈ Erdos506.V3.fanoCircleSupport j :=
        (Erdos506.V3.mem_fanoCircleSupport_iff_not_mem_fanoCanonicalLine i j).symm
  exact Erdos506.V3.canonical_fano_circle_pattern_not_realizable p hp Γ hinc

/-- The exact `T/P/D` rows force the forbidden equality face when a
seven-point configuration has at most ten circles. -/
theorem circleBlockCount_four_eq_seven_of_card_seven_of_circleCount_le_ten
    {α : Type u} [Fintype α] [DecidableEq α]
    (Mel : Erdos506.Incidence.RealPlaneMelchiorPrinciple.{u})
    (cfg : Configuration α) (hadm : Admissible cfg)
    (hcard : Fintype.card α = 7)
    (hcount : Erdos506.V4.circleCount cfg ≤ 10) :
    circleBlockCount cfg 4 = 7 := by
  let S := blockSystem cfg
  have hcap : BlockSizeCap S 4 := by
    simpa [S] using
      blockSizeCap_four_of_card_seven_of_circleCount_le_ten
        cfg hadm hcard hcount
  have hlinecap : ∀ b, S.kind b = .line → (S.support b).card ≤ 3 := by
    simpa [S, blockSystem] using
      lineSupport_card_le_three_of_card_seven_of_circleCount_le_ten
        cfg hadm hcard hcount
  have hb5 : S.blockCount 5 = 0 :=
    blockCount_eq_zero_of_cap S hcap (by omega) (by omega)
  have hb6 : S.blockCount 6 = 0 :=
    blockCount_eq_zero_of_cap S hcap (by omega) (by omega)
  have hb7 : S.blockCount 7 = 0 :=
    blockCount_eq_zero_of_cap S hcap (by omega) (by omega)
  have hl4 : S.lineCount 4 = 0 :=
    lineCount_eq_zero_of_cap S hlinecap (by omega)
  have hl5 : S.lineCount 5 = 0 :=
    lineCount_eq_zero_of_cap S hlinecap (by omega)
  have hl6 : S.lineCount 6 = 0 :=
    lineCount_eq_zero_of_cap S hlinecap (by omega)
  have hl7 : S.lineCount 7 = 0 :=
    lineCount_eq_zero_of_cap S hlinecap (by omega)
  have hc0 : S.circleCount 0 = 0 :=
    S.circleCount_eq_zero_of_lt_three (by omega)
  have hc1 : S.circleCount 1 = 0 :=
    S.circleCount_eq_zero_of_lt_three (by omega)
  have hc2 : S.circleCount 2 = 0 :=
    S.circleCount_eq_zero_of_lt_three (by omega)
  have hc5 : S.circleCount 5 = 0 :=
    circleCount_eq_zero_of_cap S hcap (by omega)
  have hc6 : S.circleCount 6 = 0 :=
    circleCount_eq_zero_of_cap S hcap (by omega)
  have hc7 : S.circleCount 7 = 0 :=
    circleCount_eq_zero_of_cap S hcap (by omega)
  have hT := S.triple_partition_by_size
  rw [hcard] at hT
  norm_num [Finset.sum_range_succ, Nat.choose, hb5, hb6, hb7] at hT
  have hP := three_n_le_rowP_of_realPlaneMelchior
    (α := α) Mel cfg hadm (by omega)
  change 3 * (Fintype.card α : ℤ) ≤ S.pivotRow at hP
  simp only [BlockSystem.pivotRow, BlockSystem.nontrivialSizes] at hP
  rw [hcard] at hP
  have hIcc : Finset.Icc 3 7 = {3, 4, 5, 6, 7} := by decide
  rw [hIcc] at hP
  norm_num [hb5, hb6, hb7] at hP
  have hD := rowD_le_n_mul_n_sub_four_of_realPlaneMelchior
    (α := α) Mel cfg hadm (by omega)
  change S.defectRow ≤
    (Fintype.card α : ℤ) * ((Fintype.card α : ℤ) - 4) at hD
  simp only [BlockSystem.defectRow, BlockSystem.nontrivialSizes] at hD
  rw [hcard] at hD
  rw [hIcc] at hD
  norm_num [hl4, hl5, hl6, hl7, hc5, hc6, hc7] at hD
  have hsplit3 := S.blockCount_eq_lineCount_add_circleCount 3
  have hsplit4 := S.blockCount_eq_lineCount_add_circleCount 4
  rw [hl4, zero_add] at hsplit4
  have htotalEq := S.totalCircleCount_eq_sum_circleCount
  rw [hcard] at htotalEq
  norm_num [Finset.sum_range_succ, hc0, hc1, hc2, hc5, hc6, hc7] at htotalEq
  have htotal : S.totalCircleCount ≤ 10 := by
    rw [totalCircleCount_eq_card_determinedCircle,
      ← Erdos506.V3.circleCount_eq_card_determinedCircle]
    exact hcount
  have hc4S : S.circleCount 4 = 7 := by omega
  simpa [S, circleBlockCount] using hc4S

/-- Every admissible seven-point V1 configuration determines at least eleven
proper circles. -/
theorem circleCount_ge_target_of_card_seven
    {α : Type u} [Fintype α] [DecidableEq α]
    (Mel : Erdos506.Incidence.RealPlaneMelchiorPrinciple.{u})
    (cfg : Configuration α) (hadm : Admissible cfg)
    (hcard : Fintype.card α = 7) :
    11 ≤ Erdos506.V4.circleCount cfg := by
  by_contra hnot
  have hcount : Erdos506.V4.circleCount cfg ≤ 10 := by omega
  have hc4 :=
    circleBlockCount_four_eq_seven_of_card_seven_of_circleCount_le_ten
      Mel cfg hadm hcard hcount
  exact circleBlockCount_four_ne_seven_of_card_seven cfg hcard hc4

end Erdos506.V1
