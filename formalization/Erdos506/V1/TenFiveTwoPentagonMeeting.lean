import Erdos506.V1.NineOrdinaryMatchingCap
import Erdos506.V1.TenFiveTwoPentagonRows

/-!
# The meeting branch of the ten-point two-pentagon endpoint

If the two generalized five-blocks meet, their union has at most nine
points.  A point outside that union has five-degree zero.  The saturated
endpoint rows force the exceptional profile

`(d₃,d₄,d₅;l₃) = (6,10,0;4)`.

The field-free nine-point ordinary-matching cap rules out `l₃ = 4` at that
pivot.  Hence the two five-blocks are necessarily disjoint.
-/

namespace Erdos506.V1

open Erdos506.Block
open Erdos506.Block.BlockSystem
open Erdos506.Incidence
open Erdos506.V4

universe u

/-- In the exact two-pentagon row, the two generalized five-blocks cannot
meet.  This is the complete meeting half of the endpoint dichotomy. -/
theorem tenTwoPentagon_fiveBlocks_pairwise_disjoint
    {α : Type u} [Fintype α] [DecidableEq α]
    (Mel : RealPlaneMelchiorPrinciple.{u})
    (EvenArr : RealPlaneEvenArrangementPrinciple.{u})
    (cfg : Configuration α) (hadm : Admissible cfg)
    (hcard : Fintype.card α = 10)
    (hB3 : (blockSystem cfg).blockCount 3 = 20)
    (hB4 : (blockSystem cfg).blockCount 4 = 20)
    (hB5 : (blockSystem cfg).blockCount 5 = 2)
    (hL3 : (blockSystem cfg).lineCount 3 = 10)
    (hL4 : (blockSystem cfg).lineCount 4 = 0)
    (hL5 : (blockSystem cfg).lineCount 5 = 0)
    (hd3 : ∀ p : α, (blockSystem cfg).blockDegree 3 p = 6) :
    ∀ b ∈ (blockSystem cfg).blocksOfSize 5,
      ∀ c ∈ (blockSystem cfg).blocksOfSize 5, b ≠ c →
        Disjoint ((blockSystem cfg).support b)
          ((blockSystem cfg).support c) := by
  classical
  let S := blockSystem cfg
  change ∀ b ∈ S.blocksOfSize 5, ∀ c ∈ S.blocksOfSize 5, b ≠ c →
    Disjoint (S.support b) (S.support c)
  intro b hb c hc hbc
  by_contra hnotDisjoint
  rw [Finset.disjoint_left] at hnotDisjoint
  push Not at hnotDisjoint
  obtain ⟨x, hxb, hxc⟩ := hnotDisjoint
  have hinterPos : 0 < (S.support b ∩ S.support c).card := by
    exact Finset.card_pos.mpr ⟨x, Finset.mem_inter.mpr ⟨hxb, hxc⟩⟩
  have hbcard : (S.support b).card = 5 := S.mem_blocksOfSize.mp hb
  have hccard : (S.support c).card = 5 := S.mem_blocksOfSize.mp hc
  have hunionCount := Finset.card_union_add_card_inter
    (S.support b) (S.support c)
  have hunionLe : (S.support b ∪ S.support c).card ≤ 9 := by omega
  have hunionLtUniv :
      (S.support b ∪ S.support c).card <
        (Finset.univ : Finset α).card := by
    simp only [Finset.card_univ, hcard]
    omega
  obtain ⟨p, _hpUniv, hpOutside⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card hunionLtUniv
  have hpb : p ∉ S.support b := by
    intro hp
    exact hpOutside (Finset.mem_union_left _ hp)
  have hpc : p ∉ S.support c := by
    intro hp
    exact hpOutside (Finset.mem_union_right _ hp)
  have hpairSubset : ({b, c} : Finset (GeometricBlock cfg)) ⊆
      S.blocksOfSize 5 := by
    intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl
    · exact hb
    · exact hc
  have hpairCard : ({b, c} : Finset (GeometricBlock cfg)).card = 2 := by
    simp [hbc]
  have hblocksEq : S.blocksOfSize 5 = {b, c} := by
    symm
    apply Finset.eq_of_subset_of_card_le hpairSubset
    change S.blockCount 5 ≤ ({b, c} : Finset (GeometricBlock cfg)).card
    rw [hpairCard, hB5]
  have hd5p : S.blockDegree 5 p = 0 := by
    unfold BlockSystem.blockDegree BlockSystem.degreeIn
    rw [hblocksEq]
    simp [hpb, hpc]
  have hrows :
      S.blockDegree 4 p + 2 * S.blockDegree 5 p = 10 ∧
        S.lineDegree 3 p + S.blockDegree 5 p = 4 := by
    simpa [S] using tenTwoPentagon_point_rows Mel EvenArr cfg hadm hcard
      hB3 hB4 hB5 hL3 hL4 hL5 hd3 p
  have hd4p : S.blockDegree 4 p = 10 := by omega
  have hl3p : S.lineDegree 3 p = 4 := by omega
  have hbound := tenExceptionalPivot_lineDegree_three_le_three
    Mel EvenArr cfg hadm hcard p (hd3 p) hd4p
  change S.lineDegree 3 p ≤ 3 at hbound
  rw [hl3p] at hbound
  omega

end Erdos506.V1
