import Erdos506.V1.PivotGeometry
import Erdos506.V1.TenFiveTwoPentagonCrossBlocks

/-!
# Pivot lines carried by saturated two-pentagon cross-blocks

A compatible pair determines a saturated cross-block.  When that block
contains a selected pivot, it is a `PivotBlock`; every non-pivot endpoint of
either of its two chords then lies on the associated line after inversion.
-/

namespace Erdos506.V1

open Erdos506.Incidence
open Erdos506.V3
open Erdos506.V4

universe u

namespace TenTwoPentagonSaturationData

variable {α : Type u} [Fintype α] [DecidableEq α]
  {cfg : Configuration α}

/-- Every saturated cross-block contains the four distinct endpoints of its
two exclusive chords. -/
theorem crossBlock_support_card_ge_four
    (d : TenTwoPentagonSaturationData cfg)
    (H : CircleCrossBlock cfg d.base.Γ d.base.Ω) :
    4 ≤ (geometricBlockSupport cfg H.1).card := by
  classical
  let e := crossBlockFirstChord cfg d.base.Γ d.base.Ω H
  let k := crossBlockSecondChord cfg d.base.Γ d.base.Ω H
  let U := e.1 ∪ k.1
  have hdisjoint : Disjoint e.1 k.1 :=
    (exclusiveCircleTrace_disjoint cfg d.base.Γ d.base.Ω).mono
      (circleChord_subset e) (circleChord_subset k)
  have hUcard : U.card = 4 := by
    rw [Finset.card_union_of_disjoint hdisjoint,
      circleChord_card e, circleChord_card k]
  have hUsub : U ⊆ geometricBlockSupport cfg H.1 := by
    intro x hx
    rcases Finset.mem_union.mp hx with hx | hx
    · exact crossBlockFirstChord_subset_support cfg d.base.Γ d.base.Ω H hx
    · exact crossBlockSecondChord_subset_support cfg d.base.Γ d.base.Ω H hx
  rw [← hUcard]
  exact Finset.card_le_card hUsub

/-- A compatible pair whose saturated cross-block contains `pivot`, regarded
as a V1 pivot block. -/
noncomputable def compatiblePairPivotBlock
    (d : TenTwoPentagonSaturationData cfg) (pivot : α)
    (p : d.CompatibleChordPair)
    (hpivot : pivot ∈ geometricBlockSupport cfg
      (d.crossBlockOfCompatiblePair p).1) :
    PivotBlock cfg pivot :=
  ⟨(d.crossBlockOfCompatiblePair p).1, hpivot, by
    have hfour := d.crossBlock_support_card_ge_four
      (d.crossBlockOfCompatiblePair p)
    omega⟩

@[simp] theorem compatiblePairPivotBlock_val
    (d : TenTwoPentagonSaturationData cfg) (pivot : α)
    (p : d.CompatibleChordPair)
    (hpivot : pivot ∈ geometricBlockSupport cfg
      (d.crossBlockOfCompatiblePair p).1) :
    (d.compatiblePairPivotBlock pivot p hpivot).1 =
      (d.crossBlockOfCompatiblePair p).1 := rfl

/-- A non-pivot endpoint of the first chord of a compatible pair lies on the
line obtained by inverting its pivot-containing cross-block. -/
theorem firstChordEndpoint_mem_compatiblePairPivotLine
    (d : TenTwoPentagonSaturationData cfg) (pivot : α)
    (p : d.CompatibleChordPair)
    (hpivot : pivot ∈ geometricBlockSupport cfg
      (d.crossBlockOfCompatiblePair p).1)
    (x : α) (hx : x ∈ p.1.1.1) (hxp : x ≠ pivot) :
    (⟨x, hxp⟩ : AwayFrom pivot) ∈
      lineSupport (pivotInversion cfg pivot)
        (blockToPivotLine cfg pivot
          (d.compatiblePairPivotBlock pivot p hpivot)) := by
  have hxH : x ∈ geometricBlockSupport cfg
      (d.crossBlockOfCompatiblePair p).1 := by
    apply crossBlockFirstChord_subset_support cfg d.base.Γ d.base.Ω
      (d.crossBlockOfCompatiblePair p)
    simpa only [d.crossBlockFirstChord_crossBlockOfCompatiblePair p] using hx
  rw [lineSupport_blockToPivotLine]
  apply mem_awaySupport.mpr
  change x ∈ geometricBlockSupport cfg
    (d.compatiblePairPivotBlock pivot p hpivot).1
  simpa only [compatiblePairPivotBlock_val] using hxH

/-- A non-pivot endpoint of the second chord of a compatible pair lies on the
line obtained by inverting its pivot-containing cross-block. -/
theorem secondChordEndpoint_mem_compatiblePairPivotLine
    (d : TenTwoPentagonSaturationData cfg) (pivot : α)
    (p : d.CompatibleChordPair)
    (hpivot : pivot ∈ geometricBlockSupport cfg
      (d.crossBlockOfCompatiblePair p).1)
    (x : α) (hx : x ∈ p.1.2.1) (hxp : x ≠ pivot) :
    (⟨x, hxp⟩ : AwayFrom pivot) ∈
      lineSupport (pivotInversion cfg pivot)
        (blockToPivotLine cfg pivot
          (d.compatiblePairPivotBlock pivot p hpivot)) := by
  have hxH : x ∈ geometricBlockSupport cfg
      (d.crossBlockOfCompatiblePair p).1 := by
    apply crossBlockSecondChord_subset_support cfg d.base.Γ d.base.Ω
      (d.crossBlockOfCompatiblePair p)
    simpa only [d.crossBlockSecondChord_crossBlockOfCompatiblePair p] using hx
  rw [lineSupport_blockToPivotLine]
  apply mem_awaySupport.mpr
  change x ∈ geometricBlockSupport cfg
    (d.compatiblePairPivotBlock pivot p hpivot).1
  simpa only [compatiblePairPivotBlock_val] using hxH

end TenTwoPentagonSaturationData

end Erdos506.V1
