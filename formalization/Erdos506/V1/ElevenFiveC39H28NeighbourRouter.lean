import Erdos506.V1.ElevenFiveC39H28GoldenAxisExtractionFinish
import Erdos506.V1.ElevenFiveC39H29Finish

/-!
# The C39 neighbour router below host weight twenty-nine

For a proper five-circle of host weight at most twenty-eight, the signed
C39 front already supplies a singleton size-five neighbour below weight
twenty-eight.  At weight twenty-eight there are two cases.  A positive
`A14` is itself a singleton neighbour.  If `A14 = 0`, a sharp Goodall
four-page cap saturates the H28 front; the existing signed extraction then
materializes a size-five block disjoint from the selected circle.

The only parameter below is the local H28 page cap.  It is kept separate
from the arithmetic router so that the configuration-level Goodall theorem
can be connected without changing the global Dewey count.
-/

namespace Erdos506.V1

open Erdos506.Block
open Erdos506.Block.BlockSystem
open Erdos506.Incidence
open Erdos506.V4

universe u

/-- Exact local interface expected from the Goodall page-cap argument. -/
def ElevenFiveC39H28PageCapInput
    {alpha : Type u} [Fintype alpha] [DecidableEq alpha]
    (cfg : Configuration alpha) : Prop :=
  ∀ (Gamma : DeterminedCircle cfg)
    (_hpoint : Fintype.card alpha = 11)
    (hD : (circleTrace cfg Gamma.1).card = 5)
    (_hhost : elevenFiveHostWeight (blockSystem cfg)
      (circleTrace cfg Gamma.1) = 28),
    elevenFiveRelativeCount (blockSystem cfg)
      (circleTrace cfg Gamma.1) 1 4 = 0 →
      elevenFiveRelativeCount (blockSystem cfg)
        (circleTrace cfg Gamma.1) 1 3 ≤ 4

/-- The zero-`A14` H28 branch needs no golden-axis input once the four-page
cap is available: the saturated signed row produces an actual disjoint
size-five block. -/
theorem elevenFive_c39_h28_exists_disjoint_sizeFive_of_pageCap
    {alpha : Type u} [Fintype alpha] [DecidableEq alpha]
    (cfg : Configuration alpha)
    (hpoint : Fintype.card alpha = 11)
    (hcap : BlockSizeCap (blockSystem cfg) 5)
    (hlocal : ∀ p : alpha, ElevenFiveLocalRows (blockSystem cfg) p)
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
    ∃ c, c ∈ (blockSystem cfg).blocksOfSize 5 ∧
      ((blockSystem cfg).support c ∩ circleTrace cfg Gamma.1).card = 0 := by
  obtain ⟨_pages, hrich⟩ :=
    elevenFive_c39_h28_front_saturated_of_zero_one_four_and_page_cap
      cfg hpoint hcap hglobal hC hL Gamma hD hhost hzero hpageCap
  have hy :=
    elevenFive_c39_h28_relativeCount_zero_five_eq_one_of_outsideRich_eq_three
      cfg hpoint hcap hlocal hglobal hC hL Gamma hD hhost hzero hrich
  obtain ⟨B, hBdisjoint, hBoutside⟩ :=
    elevenFive_c39_h28_exists_outsider_fiveBlock_of_relativeCount_zero_five_eq_one
      cfg Gamma hy
  have hBdisjoint' :
      ((blockSystem cfg).support B ∩ circleTrace cfg Gamma.1).card = 0 := by
    simpa [blockSystem, geometricBlockSystem, geometricBlockSupport] using
      hBdisjoint
  have hBoutside' :
      ((blockSystem cfg).support B \ circleTrace cfg Gamma.1).card = 5 := by
    simpa [blockSystem, geometricBlockSystem, geometricBlockSupport] using
      hBoutside
  have hBsize : ((blockSystem cfg).support B).card = 5 := by
    have hsplit := Finset.card_inter_add_card_sdiff
      ((blockSystem cfg).support B) (circleTrace cfg Gamma.1)
    omega
  exact ⟨B, (blockSystem cfg).mem_blocksOfSize.mpr hBsize, hBdisjoint'⟩

/-- For one selected proper five-circle of host weight at most twenty-eight,
the full C39/L12 rows give either a singleton size-five neighbour or a
disjoint size-five neighbour. -/
theorem elevenFive_c39_l12_fiveCircle_singleton_or_disjoint_of_host_le_twentyEight
    {alpha : Type u} [Fintype alpha] [DecidableEq alpha]
    (cfg : Configuration alpha)
    (hGoodall : ElevenFiveC39H28PageCapInput cfg)
    (hpoint : Fintype.card alpha = 11)
    (hcap : BlockSizeCap (blockSystem cfg) 5)
    (hlocal : ∀ p : alpha, ElevenFiveLocalRows (blockSystem cfg) p)
    (hglobal : ElevenFiveGlobalRows (blockSystem cfg))
    (hC : (blockSystem cfg).totalCircleCount = 39)
    (hL : elevenFiveLineTotal (blockSystem cfg) = 12)
    (Gamma : DeterminedCircle cfg)
    (hD : (circleTrace cfg Gamma.1).card = 5)
    (hhostLe : elevenFiveHostWeight (blockSystem cfg)
      (circleTrace cfg Gamma.1) ≤ 28) :
    (∃ c, c ∈ (blockSystem cfg).blocksOfSize 5 ∧
      ((blockSystem cfg).support c ∩ circleTrace cfg Gamma.1).card = 1) ∨
    (∃ c, c ∈ (blockSystem cfg).blocksOfSize 5 ∧
      ((blockSystem cfg).support c ∩ circleTrace cfg Gamma.1).card = 0) := by
  let b : GeometricBlock cfg := Sum.inr Gamma
  have hb : b ∈ (blockSystem cfg).circleBlocksOfSize 5 := by
    apply (blockSystem cfg).mem_blocksOfKindSize.mpr
    exact ⟨rfl, by
      simpa [b, blockSystem, geometricBlockSystem,
        geometricBlockSupport] using hD⟩
  by_cases hhost : elevenFiveHostWeight (blockSystem cfg)
      (circleTrace cfg Gamma.1) = 28
  · by_cases hpos : 0 < elevenFiveRelativeCount (blockSystem cfg)
        (circleTrace cfg Gamma.1) 1 4
    · exact Or.inl
        ((elevenFive_relativeCount_one_four_pos_iff_exists_sizeFive_singleton
          (blockSystem cfg) (circleTrace cfg Gamma.1)).mp hpos)
    · have hzero : elevenFiveRelativeCount (blockSystem cfg)
          (circleTrace cfg Gamma.1) 1 4 = 0 := by omega
      exact Or.inr (elevenFive_c39_h28_exists_disjoint_sizeFive_of_pageCap
        cfg hpoint hcap hlocal hglobal hC hL Gamma hD hhost hzero
          (hGoodall Gamma hpoint hD hhost hzero))
  · have hhost27 : elevenFiveHostWeight (blockSystem cfg)
        (circleTrace cfg Gamma.1) ≤ 27 := by omega
    apply Or.inl
    exact elevenFive_c39_singleton_exists_of_rebased_signed_front
      (blockSystem cfg) (circleTrace cfg Gamma.1) hpoint hD hhost27
        (elevenFive_c39_rebased_signed_front_of_rows
          (blockSystem cfg) hpoint hcap hlocal hglobal hC hL b hb)

/-- Block-indexed form used directly by a global count over proper
five-circles. -/
theorem elevenFive_c39_l12_circleBlock_singleton_or_disjoint_of_host_le_twentyEight
    {alpha : Type u} [Fintype alpha] [DecidableEq alpha]
    (cfg : Configuration alpha)
    (hGoodall : ElevenFiveC39H28PageCapInput cfg)
    (hpoint : Fintype.card alpha = 11)
    (hcap : BlockSizeCap (blockSystem cfg) 5)
    (hlocal : ∀ p : alpha, ElevenFiveLocalRows (blockSystem cfg) p)
    (hglobal : ElevenFiveGlobalRows (blockSystem cfg))
    (hC : (blockSystem cfg).totalCircleCount = 39)
    (hL : elevenFiveLineTotal (blockSystem cfg) = 12)
    (b : GeometricBlock cfg)
    (hb : b ∈ (blockSystem cfg).circleBlocksOfSize 5)
    (hhostLe : elevenFiveHostWeight (blockSystem cfg)
      ((blockSystem cfg).support b) ≤ 28) :
    (∃ c, c ∈ (blockSystem cfg).blocksOfSize 5 ∧
      ((blockSystem cfg).support c ∩ (blockSystem cfg).support b).card = 1) ∨
    (∃ c, c ∈ (blockSystem cfg).blocksOfSize 5 ∧
      ((blockSystem cfg).support c ∩ (blockSystem cfg).support b).card = 0) := by
  rcases b with L | Gamma
  · have hkind := ((blockSystem cfg).mem_blocksOfKindSize.mp hb).1
    change (.line : BlockKind) = .circle at hkind
    cases hkind
  · have hD := ((blockSystem cfg).mem_blocksOfKindSize.mp hb).2
    change (circleTrace cfg Gamma.1).card = 5 at hD
    change elevenFiveHostWeight (blockSystem cfg)
      (circleTrace cfg Gamma.1) ≤ 28 at hhostLe
    change
      (∃ c, c ∈ (blockSystem cfg).blocksOfSize 5 ∧
        ((blockSystem cfg).support c ∩ circleTrace cfg Gamma.1).card = 1) ∨
      (∃ c, c ∈ (blockSystem cfg).blocksOfSize 5 ∧
        ((blockSystem cfg).support c ∩ circleTrace cfg Gamma.1).card = 0)
    exact
      elevenFive_c39_l12_fiveCircle_singleton_or_disjoint_of_host_le_twentyEight
        cfg hGoodall hpoint hcap hlocal hglobal hC hL Gamma hD hhostLe

/-- Fully quantified form for the Dewey global count.  The unconditional
H29 and H30 routers reduce every proper five-circle to host weight at most
twenty-eight; the preceding theorem then supplies the required neighbour
alternative. -/
theorem elevenFive_c39_l12_every_circleBlock_singleton_or_disjoint
    {alpha : Type u} [Fintype alpha] [DecidableEq alpha]
    (cfg : Configuration alpha)
    (hGoodall : ElevenFiveC39H28PageCapInput cfg)
    (hpoint : Fintype.card alpha = 11)
    (hcap : BlockSizeCap (blockSystem cfg) 5)
    (hlocal : ∀ p : alpha, ElevenFiveLocalRows (blockSystem cfg) p)
    (hglobal : ElevenFiveGlobalRows (blockSystem cfg))
    (hC : (blockSystem cfg).totalCircleCount = 39)
    (hL : elevenFiveLineTotal (blockSystem cfg) = 12) :
    ∀ b ∈ (blockSystem cfg).circleBlocksOfSize 5,
      ((∃ c, c ∈ (blockSystem cfg).blocksOfSize 5 ∧
          ((blockSystem cfg).support c ∩
            (blockSystem cfg).support b).card = 1) ∨
        (∃ c, c ∈ (blockSystem cfg).blocksOfSize 5 ∧
          ((blockSystem cfg).support c ∩
            (blockSystem cfg).support b).card = 0)) := by
  intro b hb
  have hhostLe : elevenFiveHostWeight (blockSystem cfg)
      ((blockSystem cfg).support b) ≤ 28 := by
    rcases b with L | Gamma
    · have hkind := ((blockSystem cfg).mem_blocksOfKindSize.mp hb).1
      change (.line : BlockKind) = .circle at hkind
      cases hkind
    · have hD := ((blockSystem cfg).mem_blocksOfKindSize.mp hb).2
      change (circleTrace cfg Gamma.1).card = 5 at hD
      change elevenFiveHostWeight (blockSystem cfg)
        (circleTrace cfg Gamma.1) ≤ 28
      have hthirty := elevenFiveHostWeight_le_thirty
        (blockSystem cfg) (circleTrace cfg Gamma.1) hpoint hD
      have hne29 := elevenFive_c39_hostWeight_ne_twenty_nine
        cfg hpoint hcap hglobal hC hL Gamma hD
      have hne30 := elevenFive_c39_hostWeight_ne_thirty
        cfg hpoint hcap hglobal hC hL Gamma hD
      omega
  exact
    elevenFive_c39_l12_circleBlock_singleton_or_disjoint_of_host_le_twentyEight
      cfg hGoodall hpoint hcap hlocal hglobal hC hL b hb hhostLe

end Erdos506.V1
