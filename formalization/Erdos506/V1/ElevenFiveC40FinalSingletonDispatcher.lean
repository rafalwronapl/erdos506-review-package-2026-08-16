import Erdos506.V1.ElevenFiveC40FinalRealTail

/-!
# Shared C40 singleton dispatcher

All finite K3.1 and four-star branches are now combined at the level of an
actual singleton intersection of two five-blocks.  The only local profile not
eliminated by the present development is `(d₃,d₅) = (9,3)`, whose remaining
content is exactly the real grid tail isolated in `ElevenFiveC40FinalRealTail`.
-/

namespace Erdos506.V1

open Erdos506.Block
open Erdos506.Block.BlockSystem
open Erdos506.Incidence
open Erdos506.V3
open Erdos506.V4

universe u v

/-- The three already unconditional singleton exclusions at a C40 pivot:
the two-base row `(6,2)`, its path refinement `(6,3)`, and every four-base
row `d₅=4`. -/
theorem elevenFive_c40_singleton_impossible_of_common_profiles
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    (cfg : Configuration Point) (hcard : Fintype.card Point = 11)
    (p : Point) (hlocal : ElevenFiveLocalRows (blockSystem cfg) p)
    {b c : GeometricBlock cfg}
    (hb : b ∈ (blockSystem cfg).blocksOfSize 5)
    (hc : c ∈ (blockSystem cfg).blocksOfSize 5)
    (hbp : p ∈ geometricBlockSupport cfg b)
    (hcp : p ∈ geometricBlockSupport cfg c) (hne : b ≠ c)
    (hinter : (geometricBlockSupport cfg b ∩
      geometricBlockSupport cfg c).card = 1)
    (hprofile :
      ((blockSystem cfg).blockDegree 3 p = 6 ∧
        (blockSystem cfg).blockDegree 5 p = 2) ∨
      ((blockSystem cfg).blockDegree 3 p = 6 ∧
        (blockSystem cfg).blockDegree 5 p = 3) ∨
      (blockSystem cfg).blockDegree 5 p = 4) : False := by
  rcases hprofile with htwo | hthree | hfour
  · exact elevenFive_c40_two_base_singleton_impossible
      cfg hcard p hlocal htwo.1 htwo.2 hb hc hbp hcp hne hinter
  · exact elevenFive_threeFive_six_singleton_impossible
      cfg hcard p hlocal hthree.1 hthree.2 hb hc hbp hcp hne hinter
  · exact elevenFive_degreeFourPivot_fiveBlock_inter_card_ne_one
      cfg hcard p hfour hb hc hbp hcp hne hinter

/-- In the `C=40,L=11` local domain, a singleton intersection can survive
the finite dispatcher only at the one real K3.1 profile `(d₃,d₅)=(9,3)`.
This is the exact common residual, rather than a collection of four C40
certificates. -/
theorem elevenFive_c40_l11_singleton_only_nine_three
    {Point : Type u} [Fintype Point]
    [DecidableEq Point]
    (cfg : Configuration Point) (hcard : Fintype.card Point = 11)
    (p : Point) (hlocal : ElevenFiveLocalRows (blockSystem cfg) p)
    (hC : (blockSystem cfg).totalCircleCount = 40)
    (hbeta : (blockSystem cfg).blockDegree 3 p +
      (blockSystem cfg).blockDegree 4 p +
        (blockSystem cfg).blockDegree 5 p ≤ 18)
    {b c : GeometricBlock cfg}
    (hb : b ∈ (blockSystem cfg).blocksOfSize 5)
    (hc : c ∈ (blockSystem cfg).blocksOfSize 5)
    (hbp : p ∈ geometricBlockSupport cfg b)
    (hcp : p ∈ geometricBlockSupport cfg c) (hne : b ≠ c)
    (hinter : (geometricBlockSupport cfg b ∩
      geometricBlockSupport cfg c).card = 1) :
    (blockSystem cfg).blockDegree 3 p = 9 ∧
      (blockSystem cfg).blockDegree 5 p = 3 := by
  rcases elevenFive_c40_l11_two_fiveBlocks_pivot_profiles
    (blockSystem cfg) p hlocal hC hbeta hb hc hbp hcp hne with
      h62 | h63 | h93 | h94
  · exact False.elim (elevenFive_c40_singleton_impossible_of_common_profiles
      cfg hcard p hlocal hb hc hbp hcp hne hinter (Or.inl h62))
  · exact False.elim (elevenFive_c40_singleton_impossible_of_common_profiles
      cfg hcard p hlocal hb hc hbp hcp hne hinter (Or.inr (Or.inl h63)))
  · exact h93
  · exact False.elim (elevenFive_c40_singleton_impossible_of_common_profiles
      cfg hcard p hlocal hb hc hbp hcp hne hinter (Or.inr (Or.inr h94.2)))

end Erdos506.V1
