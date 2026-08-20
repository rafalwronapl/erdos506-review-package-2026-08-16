import Erdos506.V1.ElevenFiveC39H28Finish

/-!
# Arithmetic extraction before the H28 golden-axis seam

The published actual adapter is intentionally wider than the C39/L12 row:
it receives only the point count, a five-trace, host weight `28`, and
`A14 = 0`.  In particular it receives neither the global C39 rows nor the
four indexed `A13` pages and their host chords.  Consequently the two facts
in `ElevenFiveC39H28GoldenAxisMissingIncidence` cannot be reconstructed from
that interface alone.

This file records the maximal short extraction available from the existing
unconditional rows.  They force at least four `A13` pages; any independently
proved four-page cap saturates the row at `A13 = 4` and outside-rich weight
three.  The signed row then materializes the actual outsider five-block.
-/

namespace Erdos506.V1

open Erdos506.Block
open Erdos506.Block.BlockSystem
open Erdos506.Incidence
open Erdos506.V4

universe u

/-- In the full C39/L12 row, the H28 face with `A14 = 0` has at least four
relative `(1,3)` pages.  This is the unconditional arithmetic half of the
paper's zero-fibre/four-page extraction. -/
theorem elevenFive_c39_h28_relativeCount_one_three_ge_four_of_zero_one_four
    {α : Type u} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (hpoint : Fintype.card α = 11)
    (hcap : BlockSizeCap (blockSystem cfg) 5)
    (hglobal : ElevenFiveGlobalRows (blockSystem cfg))
    (hC : (blockSystem cfg).totalCircleCount = 39)
    (hL : elevenFiveLineTotal (blockSystem cfg) = 12)
    (Gamma : DeterminedCircle cfg)
    (hD : (circleTrace cfg Gamma.1).card = 5)
    (hhost : elevenFiveHostWeight (blockSystem cfg)
      (circleTrace cfg Gamma.1) = 28)
    (hzero : elevenFiveRelativeCount (blockSystem cfg)
      (circleTrace cfg Gamma.1) 1 4 = 0) :
    4 ≤ elevenFiveRelativeCount (blockSystem cfg)
      (circleTrace cfg Gamma.1) 1 3 := by
  have hfront := elevenFive_c39_h28_front_equation
    cfg hcap hglobal hC hL Gamma hD hhost
  have hqcap := elevenFiveOutsideRichWeight_le_three
    (blockSystem cfg) (circleTrace cfg Gamma.1) hpoint hD
  omega

/-- Once the actual zero-fibre page argument supplies its sharp cap
`A13 ≤ 4`, the already formalized front is saturated: there are exactly four
pages and the outside-rich weight is exactly three. -/
theorem elevenFive_c39_h28_front_saturated_of_zero_one_four_and_page_cap
    {α : Type u} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (hpoint : Fintype.card α = 11)
    (hcap : BlockSizeCap (blockSystem cfg) 5)
    (hglobal : ElevenFiveGlobalRows (blockSystem cfg))
    (hC : (blockSystem cfg).totalCircleCount = 39)
    (hL : elevenFiveLineTotal (blockSystem cfg) = 12)
    (Gamma : DeterminedCircle cfg)
    (hD : (circleTrace cfg Gamma.1).card = 5)
    (hhost : elevenFiveHostWeight (blockSystem cfg)
      (circleTrace cfg Gamma.1) = 28)
    (hzero : elevenFiveRelativeCount (blockSystem cfg)
      (circleTrace cfg Gamma.1) 1 4 = 0)
    (hpageCap : elevenFiveRelativeCount (blockSystem cfg)
      (circleTrace cfg Gamma.1) 1 3 ≤ 4) :
    elevenFiveRelativeCount (blockSystem cfg)
        (circleTrace cfg Gamma.1) 1 3 = 4 ∧
      elevenFiveOutsideRichWeight (blockSystem cfg)
        (circleTrace cfg Gamma.1) = 3 := by
  have hlower :=
    elevenFive_c39_h28_relativeCount_one_three_ge_four_of_zero_one_four
      cfg hpoint hcap hglobal hC hL Gamma hD hhost hzero
  have hfront := elevenFive_c39_h28_front_equation
    cfg hcap hglobal hC hL Gamma hD hhost
  omega

/-- At H28, outside-rich weight three and the signed high-point row force
one actual block disjoint from the selected five-trace and having five
outsiders.  Thus the paper's outsider `K5` is not an additional geometric
assumption once the four-page front is saturated. -/
theorem elevenFive_c39_h28_relativeCount_zero_five_eq_one_of_outsideRich_eq_three
    {α : Type u} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (hpoint : Fintype.card α = 11)
    (hcap : BlockSizeCap (blockSystem cfg) 5)
    (hlocal : ∀ p : α, ElevenFiveLocalRows (blockSystem cfg) p)
    (hglobal : ElevenFiveGlobalRows (blockSystem cfg))
    (hC : (blockSystem cfg).totalCircleCount = 39)
    (hL : elevenFiveLineTotal (blockSystem cfg) = 12)
    (Gamma : DeterminedCircle cfg)
    (hD : (circleTrace cfg Gamma.1).card = 5)
    (hhost : elevenFiveHostWeight (blockSystem cfg)
      (circleTrace cfg Gamma.1) = 28)
    (hzero : elevenFiveRelativeCount (blockSystem cfg)
      (circleTrace cfg Gamma.1) 1 4 = 0)
    (hrich : elevenFiveOutsideRichWeight (blockSystem cfg)
      (circleTrace cfg Gamma.1) = 3) :
    elevenFiveRelativeCount (blockSystem cfg)
      (circleTrace cfg Gamma.1) 0 5 = 1 := by
  classical
  let S := blockSystem cfg
  let D := circleTrace cfg Gamma.1
  let b : GeometricBlock cfg := Sum.inr Gamma
  have hb : b ∈ S.circleBlocksOfSize 5 := by
    apply S.mem_blocksOfKindSize.mpr
    change geometricBlockKind (Sum.inr Gamma) = .circle ∧
      (geometricBlockSupport cfg (Sum.inr Gamma)).card = 5
    exact ⟨rfl, hD⟩
  have hDb : S.support b = D := by
    simp [S, b, D, blockSystem, geometricBlockSystem,
      geometricBlockSupport]
  have hzeroB : elevenFiveRelativeCount S (S.support b) 1 4 = 0 := by
    rw [hDb]
    simpa [S, D] using hzero
  have hsigned := elevenFive_c39_rebased_signed_front_of_rows
    S hpoint (by simpa [S] using hcap)
      (fun p => by simpa [S] using hlocal p)
      (by simpa [S] using hglobal) (by simpa [S] using hC)
      (by simpa [S] using hL) b hb hzeroB
  have hhostB : elevenFiveHostWeight S (S.support b) = 28 := by
    rw [hDb]
    simpa [S, D] using hhost
  have hrichB : elevenFiveOutsideRichWeight S (S.support b) = 3 := by
    rw [hDb]
    simpa [S, D] using hrich
  have hbSize : (S.support b).card = 5 :=
    (S.mem_blocksOfKindSize.mp hb).2
  have hycap := elevenFive_relativeCount_zero_five_le_one
    S (S.support b) hpoint hbSize
  have heq := hsigned.2
  rw [hhostB, hrichB] at heq
  norm_num at heq
  have hyB : elevenFiveRelativeCount S (S.support b) 0 5 = 1 := by
    omega
  rw [hDb] at hyB
  simpa [S, D] using hyB

/-- Literal witness form of the preceding count: an actual geometric block
is disjoint from the selected trace and has exactly five outsider labels. -/
theorem elevenFive_c39_h28_exists_outsider_fiveBlock_of_relativeCount_zero_five_eq_one
    {α : Type u} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (Gamma : DeterminedCircle cfg)
    (hy : elevenFiveRelativeCount (blockSystem cfg)
      (circleTrace cfg Gamma.1) 0 5 = 1) :
    ∃ B : GeometricBlock cfg,
      (geometricBlockSupport cfg B ∩ circleTrace cfg Gamma.1).card = 0 ∧
        (geometricBlockSupport cfg B \ circleTrace cfg Gamma.1).card = 5 := by
  have hpos : 0 < elevenFiveRelativeCount (blockSystem cfg)
      (circleTrace cfg Gamma.1) 0 5 := by omega
  rw [elevenFiveRelativeCount] at hpos
  obtain ⟨B, hB⟩ := Finset.card_pos.mp hpos
  exact ⟨B, (Finset.mem_filter.mp hB).2.1,
    (Finset.mem_filter.mp hB).2.2⟩

end Erdos506.V1
