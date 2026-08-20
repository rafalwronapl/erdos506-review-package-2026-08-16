import Erdos506.V1.TwelveSixSpineData

/-!
# Scalar router for the twelve-point selected-six-circle branch

The materialized spine leaves exactly four possible values of the number
of six-blocks.  This module records that small arithmetic dispatch.
-/

namespace Erdos506.V1

open Erdos506.Block
open Erdos506.Block.BlockSystem
open Erdos506.Incidence
open Erdos506.V4
open scoped BigOperators

universe u

/-- The universal spine reduces the selected-six branch to four scalar
routers.  The bounds on `s` use only nonnegativity of the natural kappa
total and the printed Gram caps. -/
theorem twelveSixSpine_scalar_router
    {Point Block : Type*} [Fintype Point] [Fintype Block]
    [DecidableEq Point]
    (S : BlockSystem Point Block) (h : TwelveSixSpine S) :
    (S.blockCount 6 = 1 /\ S.blockCount 5 <= 11 /\ h.s <= 1) \/
    (S.blockCount 6 = 2 /\ S.blockCount 5 <= 8 /\ h.s <= 2) \/
    (S.blockCount 6 = 3 /\ S.blockCount 5 <= 3 /\ h.s <= 2) \/
    (S.blockCount 6 = 4 /\ S.blockCount 5 = 0 /\ h.s <= 2) := by
  rcases h.sixBlockCaps with ⟨hmcap, hm4, hm3, hm2, hm1⟩
  have hmpos := h.sixBlockPositive
  have hm : S.blockCount 6 = 1 \/ S.blockCount 6 = 2 \/
      S.blockCount 6 = 3 \/ S.blockCount 6 = 4 := by
    omega
  rcases hm with hm | hm | hm | hm
  · apply Or.inl
    refine ⟨hm, hm1 hm, ?_⟩
    have hQ := h.kappaTotal
    omega
  · apply Or.inr
    apply Or.inl
    refine ⟨hm, hm2 hm, ?_⟩
    have hQ := h.kappaTotal
    omega
  · apply Or.inr
    apply Or.inr
    apply Or.inl
    refine ⟨hm, hm3 hm, ?_⟩
    have hQ := h.kappaTotal
    omega
  · apply Or.inr
    apply Or.inr
    apply Or.inr
    refine ⟨hm, hm4 hm, ?_⟩
    have hQ := h.kappaTotal
    omega

end Erdos506.V1
