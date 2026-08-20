import Erdos506.V1.ElevenFiveC40FinalK31ActualGridTail
import Erdos506.V1.ElevenFiveC40FinalSingletonDispatcher

/-!
# Complete local C40 singleton dispatcher

The real `K3.1` tail closes the last local profile left by the former
singleton dispatcher.  Consequently, at a C40 `L = 11` pivot satisfying the
standard beta cap, two distinct five-blocks through the pivot cannot have a
singleton intersection.

This is deliberately a local theorem: the four global C40 residual rows still
need a separate incidence-to-singleton (or direct collision) extraction.
-/

namespace Erdos506.V1

open Erdos506.Block
open Erdos506.Block.BlockSystem
open Erdos506.Incidence
open Erdos506.V3
open Erdos506.V4

universe u

/-- Every one of the four C40 `L = 11` two-five-block pivot profiles now
excludes a singleton intersection. -/
theorem elevenFive_c40_l11_fiveBlock_inter_card_ne_one
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    (cfg : Configuration Point) (hcard : Fintype.card Point = 11)
    (p : Point) (hlocal : ElevenFiveLocalRows (blockSystem cfg) p)
    (hC : (blockSystem cfg).totalCircleCount = 40)
    (hbeta : (blockSystem cfg).blockDegree 3 p +
      (blockSystem cfg).blockDegree 4 p +
        (blockSystem cfg).blockDegree 5 p <= 18)
    {b c : GeometricBlock cfg}
    (hb : b ∈ (blockSystem cfg).blocksOfSize 5)
    (hc : c ∈ (blockSystem cfg).blocksOfSize 5)
    (hbp : p ∈ geometricBlockSupport cfg b)
    (hcp : p ∈ geometricBlockSupport cfg c) (hne : b ≠ c) :
    (geometricBlockSupport cfg b ∩ geometricBlockSupport cfg c).card ≠ 1 := by
  intro hinter
  rcases elevenFive_c40_l11_two_fiveBlocks_pivot_profiles
    (blockSystem cfg) p hlocal hC hbeta hb hc hbp hcp hne with
      h62 | h63 | h93 | h94
  · exact elevenFive_c40_singleton_impossible_of_common_profiles
      cfg hcard p hlocal hb hc hbp hcp hne hinter (Or.inl h62)
  · exact elevenFive_c40_singleton_impossible_of_common_profiles
      cfg hcard p hlocal hb hc hbp hcp hne hinter (Or.inr (Or.inl h63))
  · exact elevenFive_threeFive_nine_singleton_impossible
      cfg hcard p hlocal h93.1 h93.2 hb hc hbp hcp hne hinter
  · exact elevenFive_c40_singleton_impossible_of_common_profiles
      cfg hcard p hlocal hb hc hbp hcp hne hinter (Or.inr (Or.inr h94.2))

/-- Contradiction form of the complete C40 `L = 11` singleton dispatcher. -/
theorem elevenFive_c40_l11_fiveBlock_singleton_impossible
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    (cfg : Configuration Point) (hcard : Fintype.card Point = 11)
    (p : Point) (hlocal : ElevenFiveLocalRows (blockSystem cfg) p)
    (hC : (blockSystem cfg).totalCircleCount = 40)
    (hbeta : (blockSystem cfg).blockDegree 3 p +
      (blockSystem cfg).blockDegree 4 p +
        (blockSystem cfg).blockDegree 5 p <= 18)
    {b c : GeometricBlock cfg}
    (hb : b ∈ (blockSystem cfg).blocksOfSize 5)
    (hc : c ∈ (blockSystem cfg).blocksOfSize 5)
    (hbp : p ∈ geometricBlockSupport cfg b)
    (hcp : p ∈ geometricBlockSupport cfg c) (hne : b ≠ c)
    (hinter : (geometricBlockSupport cfg b ∩
      geometricBlockSupport cfg c).card = 1) : False :=
  elevenFive_c40_l11_fiveBlock_inter_card_ne_one
    cfg hcard p hlocal hC hbeta hb hc hbp hcp hne hinter

end Erdos506.V1
