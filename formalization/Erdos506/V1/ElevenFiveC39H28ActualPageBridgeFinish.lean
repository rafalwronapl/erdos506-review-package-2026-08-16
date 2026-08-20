import Erdos506.V1.ElevenFiveC39H28GoldenAxisExtractionFinish
import Erdos506.Incidence.GoldenAxisActualPageBridge

/-!
# Full-row C39/H28 entrance to the actual-page golden bridge

The unconditional arithmetic front already gives four `A13` pages after a
sharp page cap, then an outsider five-block.  What remains is one finite
page-indexing statement: the four pages and their literal host chords must
be put into the golden rows and the surviving three-page matching must be
put into its end or middle orbit.

`ElevenFiveC39H28FinitePageIndexSeam` states exactly that residual.  The
theorems below consume it only in the full C39/L12/H28 row, construct all
other data with existing theorems, and recover the former configuration
adapter.  Thus no global normal-form or unrestricted geometric principle is
introduced.
-/

namespace Erdos506.V1

open Erdos506.Block
open Erdos506.Block.BlockSystem
open Erdos506.Incidence
open Erdos506.V4

universe u

/-- The sole finite/page-index residual in the full C39/L12/H28 zero-fibre
row.  Its first component is the sharp four-page cap.  After the arithmetic
front has materialized the four pages and an outsider five-block, its second
component labels the actual pages and host chords in the normalized golden
end/middle pattern.

The returned `GoldenAxisActualPageHostData` contains only literal nonzero
page/axis covectors and their incidences; the conic representatives,
general position, canonical chord-pair centres, and centre incidences are
constructed independently by the existing H28 adapter module. -/
def ElevenFiveC39H28FinitePageIndexSeam
    {alpha : Type u} [Fintype alpha] [DecidableEq alpha]
    (cfg : Configuration alpha) : Prop :=
  ∀
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
      (circleTrace cfg Gamma.1) 1 4 = 0),
    elevenFiveRelativeCount (blockSystem cfg)
        (circleTrace cfg Gamma.1) 1 3 ≤ 4 ∧
      ∀
        (_hpages : elevenFiveRelativeCount (blockSystem cfg)
          (circleTrace cfg Gamma.1) 1 3 = 4)
        (_hrich : elevenFiveOutsideRichWeight (blockSystem cfg)
          (circleTrace cfg Gamma.1) = 3)
        (B : GeometricBlock cfg),
        (geometricBlockSupport cfg B ∩ circleTrace cfg Gamma.1).card = 0 →
        (geometricBlockSupport cfg B \ circleTrace cfg Gamma.1).card = 5 →
          ∃ r : Fin 5,
            let g := elevenFiveC39H28GoldenTraceRaw cfg Gamma hD r
            let q := elevenFiveC39H28GoldenCenterRaw g
            GoldenAxisActualPageHostData g q

/-- The exact full-row H28 zero-fibre contradiction, conditional only on
the finite page-index seam above. -/
theorem elevenFive_c39_h28_zeroFibre_absurd_of_finitePageIndexSeam
    {alpha : Type u} [Fintype alpha] [DecidableEq alpha]
    (cfg : Configuration alpha)
    (hfinite : ElevenFiveC39H28FinitePageIndexSeam cfg)
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
      (circleTrace cfg Gamma.1) 1 4 = 0) : False := by
  obtain ⟨hpageCap, hindex⟩ :=
    hfinite hpoint hcap hlocal hglobal hC hL Gamma hD hhost hzero
  obtain ⟨hpages, hrich⟩ :=
    elevenFive_c39_h28_front_saturated_of_zero_one_four_and_page_cap
      cfg hpoint hcap hglobal hC hL Gamma hD hhost hzero hpageCap
  have hy :=
    elevenFive_c39_h28_relativeCount_zero_five_eq_one_of_outsideRich_eq_three
      cfg hpoint hcap hlocal hglobal hC hL Gamma hD hhost hzero hrich
  obtain ⟨B, hBdisjoint, hBoutside⟩ :=
    elevenFive_c39_h28_exists_outsider_fiveBlock_of_relativeCount_zero_five_eq_one
      cfg Gamma hy
  obtain ⟨r, hdata⟩ :=
    hindex hpages hrich B hBdisjoint hBoutside
  exact GoldenAxisActualPageHostData.absurd
    (elevenFiveC39H28GoldenTraceRaw_generalPosition cfg Gamma hD r)
    (elevenFiveC39H28GoldenCenterRaw_ne_zero
      (elevenFiveC39H28GoldenTraceRaw_generalPosition cfg Gamma hD r))
    (elevenFiveC39H28GoldenCenterRaw_centerIncidence
      (elevenFiveC39H28GoldenTraceRaw cfg Gamma hD r))
    hdata

/-- On a fixed configuration carrying the full C39/L12 rows, the minimal
finite page-index seam recovers the former local H28 adapter.  This is the
drop-in bridge needed by the existing singleton-graph tail. -/
theorem elevenFiveC39H28GoldenAxisActualAdapter_of_fullRows_finitePageIndexSeam
    {alpha : Type u} [Fintype alpha] [DecidableEq alpha]
    (cfg : Configuration alpha)
    (hfinite : ElevenFiveC39H28FinitePageIndexSeam cfg)
    (hpoint : Fintype.card alpha = 11)
    (hcap : BlockSizeCap (blockSystem cfg) 5)
    (hlocal : ∀ p : alpha, ElevenFiveLocalRows (blockSystem cfg) p)
    (hglobal : ElevenFiveGlobalRows (blockSystem cfg))
    (hC : (blockSystem cfg).totalCircleCount = 39)
    (hL : elevenFiveLineTotal (blockSystem cfg) = 12) :
    ElevenFiveC39H28GoldenAxisActualAdapter cfg := by
  intro Gamma _hpoint hD hhost hzero
  exact elevenFive_c39_h28_zeroFibre_absurd_of_finitePageIndexSeam
    cfg hfinite hpoint hcap hlocal hglobal hC hL Gamma hD hhost hzero

end Erdos506.V1
