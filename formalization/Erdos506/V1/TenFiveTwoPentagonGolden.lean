import Erdos506.V1.TenFiveTwoPentagonGoldenConcurrency
import Erdos506.V1.TenFiveTwoPentagonRows

/-!
# Assembly of the ten-point golden two-pentagon contradiction

This file records the endpoint-local consequences which are independent of
the final finite matching normalization.  The selected pivot belongs to the
first of the two disjoint five-blocks and not to the second, so its size-five
degree is one.  The exact local rows then force three original three-lines
through that pivot.
-/

namespace Erdos506.V1

open Erdos506.Block
open Erdos506.Block.BlockSystem
open Erdos506.Incidence
open Erdos506.V4

universe u

namespace TenTwoPentagonSaturationData

variable {α : Type u} [Fintype α] [DecidableEq α]
  {cfg : Configuration α}

/-- The unordered pair of the two distinguished size-five blocks. -/
noncomputable def baseFiveBlocks
    (d : TenTwoPentagonSaturationData cfg) : Finset (GeometricBlock cfg) := by
  classical
  exact {d.base.first, d.base.second}

/-- The two selected base blocks exhaust the size-five layer. -/
theorem blocksOfSize_five_eq_base_pair
    (d : TenTwoPentagonSaturationData cfg)
    (hB5 : (blockSystem cfg).blockCount 5 = 2) :
    (blockSystem cfg).blocksOfSize 5 = d.baseFiveBlocks := by
  classical
  let S := blockSystem cfg
  have hsubset : d.baseFiveBlocks ⊆ S.blocksOfSize 5 := by
    intro b hb
    simp only [baseFiveBlocks, Finset.mem_insert, Finset.mem_singleton] at hb
    rcases hb with rfl | rfl
    · exact d.base.first_mem
    · exact d.base.second_mem
  have hpairCard :
      d.baseFiveBlocks.card = 2 := by
    simp [baseFiveBlocks, d.base.blocks_ne]
  symm
  apply Finset.eq_of_subset_of_card_le hsubset
  change S.blockCount 5 ≤
    d.baseFiveBlocks.card
  rw [hB5, hpairCard]

/-- The distinguished pivot lies in exactly one size-five block. -/
theorem goldenPivot_blockDegree_five_eq_one
    (d : TenTwoPentagonSaturationData cfg)
    (hB5 : (blockSystem cfg).blockCount 5 = 2) :
    (blockSystem cfg).blockDegree 5 d.pivot.1 = 1 := by
  classical
  have hpFirst : d.pivot.1 ∈
      (blockSystem cfg).support d.base.first := by
    change d.pivot.1 ∈ geometricBlockSupport cfg d.base.first
    simpa only [d.base.exclusiveTrace_Γ_Ω] using d.pivot.2
  have hpSecond : d.pivot.1 ∉
      (blockSystem cfg).support d.base.second := by
    change d.pivot.1 ∉ geometricBlockSupport cfg d.base.second
    exact d.pivot_not_mem_secondSupport
  unfold BlockSystem.blockDegree BlockSystem.degreeIn
  rw [d.blocksOfSize_five_eq_base_pair hB5]
  have hfilter : d.baseFiveBlocks.filter (fun b =>
      d.pivot.1 ∈ (blockSystem cfg).support b) =
      ({d.base.first} : Finset (GeometricBlock cfg)) := by
    ext b
    simp only [baseFiveBlocks, Finset.mem_filter, Finset.mem_insert,
      Finset.mem_singleton]
    constructor
    · rintro ⟨rfl | rfl, hp⟩
      · rfl
      · exact (hpSecond hp).elim
    · intro hb
      rw [hb]
      exact ⟨Or.inl rfl, hpFirst⟩
  rw [hfilter]
  exact Finset.card_singleton _

/-- The exact point rows force three original three-lines through the golden
pivot. -/
theorem goldenPivot_lineDegree_three_eq_three
    (d : TenTwoPentagonSaturationData cfg)
    (Mel : RealPlaneMelchiorPrinciple.{u})
    (EvenArr : RealPlaneEvenArrangementPrinciple.{u})
    (hadm : Admissible cfg)
    (hcard : Fintype.card α = 10)
    (hB3 : (blockSystem cfg).blockCount 3 = 20)
    (hB4 : (blockSystem cfg).blockCount 4 = 20)
    (hB5 : (blockSystem cfg).blockCount 5 = 2)
    (hL3 : (blockSystem cfg).lineCount 3 = 10)
    (hL4 : (blockSystem cfg).lineCount 4 = 0)
    (hL5 : (blockSystem cfg).lineCount 5 = 0)
    (hd3 : ∀ p : α, (blockSystem cfg).blockDegree 3 p = 6) :
    (blockSystem cfg).lineDegree 3 d.pivot.1 = 3 := by
  have hrows := tenTwoPentagon_point_rows Mel EvenArr cfg hadm hcard
    hB3 hB4 hB5 hL3 hL4 hL5 hd3 d.pivot.1
  have hd5 := d.goldenPivot_blockDegree_five_eq_one hB5
  omega

/-- The exact two-pentagon row has no realization in the real affine plane.
The saturation constructor supplies the two disjoint five-circles, the
point rows force three source lines through the selected pivot, and the
golden matching/projective obstruction closes the endpoint. -/
theorem tenTwoPentagon_golden_impossible
    (Mel : RealPlaneMelchiorPrinciple.{u})
    (EvenArr : RealPlaneEvenArrangementPrinciple.{u})
    {alpha : Type u} [Fintype alpha] [DecidableEq alpha]
    (cfg : Configuration alpha) (hadm : Admissible cfg)
    (hcard : Fintype.card alpha = 10)
    (_hcircle : (blockSystem cfg).totalCircleCount = 32)
    (hB3 : (blockSystem cfg).blockCount 3 = 20)
    (hB4 : (blockSystem cfg).blockCount 4 = 20)
    (hB5 : (blockSystem cfg).blockCount 5 = 2)
    (hL3 : (blockSystem cfg).lineCount 3 = 10)
    (hL4 : (blockSystem cfg).lineCount 4 = 0)
    (hL5 : (blockSystem cfg).lineCount 5 = 0)
    (hd3 : forall p : alpha,
      (blockSystem cfg).blockDegree 3 p = 6) : False := by
  let d := tenTwoPentagon_saturation Mel EvenArr cfg hadm hcard
    hB3 hB4 hB5 hL3 hL4 hL5 hd3
  have hthree : (blockSystem cfg).lineDegree 3 d.pivot.1 = 3 :=
    d.goldenPivot_lineDegree_three_eq_three Mel EvenArr hadm hcard
      hB3 hB4 hB5 hL3 hL4 hL5 hd3
  exact d.tenTwoPentagon_golden_contradiction hcard hthree

end TenTwoPentagonSaturationData

end Erdos506.V1
