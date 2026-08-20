import Erdos506.Incidence.CrossBlockCombinatorics
import Erdos506.Incidence.RadicalAxisFourFourGeometry

/-!
# The unconditional four-by-four cross-block capacity

This thin module specializes the radical-axis chord geometry to cross-blocks
and exports the residual real-plane principle.
-/

namespace Erdos506.Incidence

open Erdos506.Finite
open Erdos506.V1
open Erdos506.V3
open Erdos506.V4
open Matrix
open scoped BigOperators LinearAlgebra.Projectivization

/-! ## Cross-blocks inject into compatible chord pairs -/

section CrossBlocks

variable {α : Type*} [Fintype α] [DecidableEq α]

theorem exclusiveCircleTrace_disjoint
    (cfg : Configuration α) (Γ Ω : Erdos506.V1.DeterminedCircle cfg) :
    Disjoint (exclusiveCircleTrace cfg Γ Ω)
      (exclusiveCircleTrace cfg Ω Γ) := by
  classical
  rw [Finset.disjoint_left]
  intro x hxΓ hxΩ
  have hxΓ' := Finset.mem_sdiff.mp hxΓ
  have hxΩ' := Finset.mem_sdiff.mp hxΩ
  exact hxΓ'.2 hxΩ'.1

/-- Cross-blocks, regarded as an attached finite type. -/
abbrev CircleCrossBlock (cfg : Configuration α)
    (Γ Ω : Erdos506.V1.DeterminedCircle cfg) := ↥(circleCrossBlocks cfg Γ Ω)

/-- The two-point trace of a cross-block on the first exclusive circle. -/
noncomputable def crossBlockFirstChord
    (cfg : Configuration α) (Γ Ω : Erdos506.V1.DeterminedCircle cfg)
    (b : CircleCrossBlock cfg Γ Ω) :
    CircleChord (exclusiveCircleTrace cfg Γ Ω) := by
  classical
  refine ⟨geometricBlockSupport cfg b.1 ∩
      exclusiveCircleTrace cfg Γ Ω, ?_⟩
  apply Finset.mem_powersetCard.mpr
  refine ⟨Finset.inter_subset_right, ?_⟩
  have hb := b.2
  change b.1 ∈ Finset.univ.filter (fun H =>
    (geometricBlockSupport cfg H ∩ exclusiveCircleTrace cfg Γ Ω).card = 2 ∧
    (geometricBlockSupport cfg H ∩ exclusiveCircleTrace cfg Ω Γ).card = 2) at hb
  exact (Finset.mem_filter.mp hb).2.1

/-- The two-point trace of a cross-block on the second exclusive circle. -/
noncomputable def crossBlockSecondChord
    (cfg : Configuration α) (Γ Ω : Erdos506.V1.DeterminedCircle cfg)
    (b : CircleCrossBlock cfg Γ Ω) :
    CircleChord (exclusiveCircleTrace cfg Ω Γ) := by
  classical
  refine ⟨geometricBlockSupport cfg b.1 ∩
      exclusiveCircleTrace cfg Ω Γ, ?_⟩
  apply Finset.mem_powersetCard.mpr
  refine ⟨Finset.inter_subset_right, ?_⟩
  have hb := b.2
  change b.1 ∈ Finset.univ.filter (fun H =>
    (geometricBlockSupport cfg H ∩ exclusiveCircleTrace cfg Γ Ω).card = 2 ∧
    (geometricBlockSupport cfg H ∩ exclusiveCircleTrace cfg Ω Γ).card = 2) at hb
  exact (Finset.mem_filter.mp hb).2.2

theorem crossBlockFirstChord_subset_support
    (cfg : Configuration α) (Γ Ω : Erdos506.V1.DeterminedCircle cfg)
    (b : CircleCrossBlock cfg Γ Ω) :
    (crossBlockFirstChord cfg Γ Ω b).1 ⊆ geometricBlockSupport cfg b.1 :=
  Finset.inter_subset_left

theorem crossBlockSecondChord_subset_support
    (cfg : Configuration α) (Γ Ω : Erdos506.V1.DeterminedCircle cfg)
    (b : CircleCrossBlock cfg Γ Ω) :
    (crossBlockSecondChord cfg Γ Ω b).1 ⊆ geometricBlockSupport cfg b.1 :=
  Finset.inter_subset_left

/-- The ordered pair of exclusive chords cut out by a cross-block. -/
noncomputable def crossBlockChordPair
    (cfg : Configuration α) (Γ Ω : Erdos506.V1.DeterminedCircle cfg) :
    CircleCrossBlock cfg Γ Ω →
      CircleChord (exclusiveCircleTrace cfg Γ Ω) ×
        CircleChord (exclusiveCircleTrace cfg Ω Γ) :=
  fun b => ⟨crossBlockFirstChord cfg Γ Ω b,
    crossBlockSecondChord cfg Γ Ω b⟩

/-- A cross-block is determined by its two exclusive chord traces. -/
theorem crossBlockChordPair_injective
    (cfg : Configuration α) (Γ Ω : Erdos506.V1.DeterminedCircle cfg) :
    Function.Injective (crossBlockChordPair cfg Γ Ω) := by
  classical
  intro b c hpairs
  have hfirst : (crossBlockFirstChord cfg Γ Ω b).1 =
      (crossBlockFirstChord cfg Γ Ω c).1 :=
    congrArg (fun z => z.1.1) hpairs
  have hsecond : (crossBlockSecondChord cfg Γ Ω b).1 =
      (crossBlockSecondChord cfg Γ Ω c).1 :=
    congrArg (fun z => z.2.1) hpairs
  let U := (crossBlockFirstChord cfg Γ Ω b).1 ∪
    (crossBlockSecondChord cfg Γ Ω b).1
  have hpairDisjoint : Disjoint
      (crossBlockFirstChord cfg Γ Ω b).1
      (crossBlockSecondChord cfg Γ Ω b).1 :=
    (exclusiveCircleTrace_disjoint cfg Γ Ω).mono
      (circleChord_subset (crossBlockFirstChord cfg Γ Ω b))
      (circleChord_subset (crossBlockSecondChord cfg Γ Ω b))
  have hUcard : U.card = 4 := by
    rw [Finset.card_union_of_disjoint hpairDisjoint,
      circleChord_card (crossBlockFirstChord cfg Γ Ω b),
      circleChord_card (crossBlockSecondChord cfg Γ Ω b)]
  have hUb : U ⊆ geometricBlockSupport cfg b.1 := by
    intro x hx

    rcases Finset.mem_union.mp hx with hx | hx
    · exact crossBlockFirstChord_subset_support cfg Γ Ω b hx
    · exact crossBlockSecondChord_subset_support cfg Γ Ω b hx
  have hUc : U ⊆ geometricBlockSupport cfg c.1 := by
    intro x hx
    rcases Finset.mem_union.mp hx with hx | hx
    · apply crossBlockFirstChord_subset_support cfg Γ Ω c
      rw [← hfirst]
      exact hx
    · apply crossBlockSecondChord_subset_support cfg Γ Ω c
      rw [← hsecond]
      exact hx
  apply Subtype.ext
  by_contra hbc
  have hinter := (geometricBlockSystem cfg).distinct_block_inter_card_lt_three hbc
  change (geometricBlockSupport cfg b.1 ∩
    geometricBlockSupport cfg c.1).card < 3 at hinter
  have hUinter : U ⊆ geometricBlockSupport cfg b.1 ∩
      geometricBlockSupport cfg c.1 := by
    intro x hx
    exact Finset.mem_inter.mpr ⟨hUb hx, hUc hx⟩
  have hfourLe := Finset.card_le_card hUinter
  rw [hUcard] at hfourLe
  omega

/-- The radical centres of two chord pairs hosted by the same geometric
block agree. -/
theorem chordCenters_eq_of_common_geometricBlock
    (cfg : Configuration α) (Γ Ω : Erdos506.V1.DeterminedCircle cfg) (hΓΩ : Γ ≠ Ω)
    (e : CircleChord (exclusiveCircleTrace cfg Γ Ω))
    (k : CircleChord (exclusiveCircleTrace cfg Ω Γ))
    (H : GeometricBlock cfg)
    (heH : e.1 ⊆ geometricBlockSupport cfg H)
    (hkH : k.1 ⊆ geometricBlockSupport cfg H) :
    firstExclusiveChordCenter cfg Γ Ω hΓΩ e =
      secondExclusiveChordCenter cfg Γ Ω hΓΩ k := by
  cases H with
  | inl L =>
      have heLine : lineOfPair cfg (circleChordPair e) = L.1 :=
        lineOfPair_eq_of_mem_of_direction_finrank_one cfg
          (circleChordPair e) L.1 (by
            intro x hx
            apply mem_lineSupport.mp
            exact heH hx) L.direction_finrank
      have hkLine : lineOfPair cfg (circleChordPair k) = L.1 :=
        lineOfPair_eq_of_mem_of_direction_finrank_one cfg
          (circleChordPair k) L.1 (by
            intro x hx
            apply mem_lineSupport.mp
            exact hkH hx) L.direction_finrank
      have hprojective := projectiveChordLine_eq_of_lineOfPair_eq cfg
        (circleChordPair e) (circleChordPair k)
          (heLine.trans hkLine.symm)
      unfold firstExclusiveChordCenter secondExclusiveChordCenter
      unfold pairRadicalCenter
      rw [hprojective]
  | inr K =>
      have heΓ (i : Fin 2) :
          chordPoint cfg (circleChordPair e) i ∈ (Γ.1.1 : Set Point2) := by
        apply mem_circleTrace.mp
        exact (Finset.mem_sdiff.mp
          (circleChord_subset e (chordLabel_mem (circleChordPair e) i))).1
      have hkΩ (i : Fin 2) :
          chordPoint cfg (circleChordPair k) i ∈ (Ω.1.1 : Set Point2) := by
        apply mem_circleTrace.mp
        exact (Finset.mem_sdiff.mp
          (circleChord_subset k (chordLabel_mem (circleChordPair k) i))).1
      have heK (i : Fin 2) :
          chordPoint cfg (circleChordPair e) i ∈ (K.1.1 : Set Point2) := by
        apply mem_circleTrace.mp
        exact heH (chordLabel_mem (circleChordPair e) i)
      have hkK (i : Fin 2) :
          chordPoint cfg (circleChordPair k) i ∈ (K.1.1 : Set Point2) := by
        apply mem_circleTrace.mp
        exact hkH (chordLabel_mem (circleChordPair k) i)
      have hΓK : Γ.1 ≠ K.1 := by
        intro hΓK
        have hkNotΓ := (Finset.mem_sdiff.mp
          (circleChord_subset k
            (chordLabel_mem (circleChordPair k) 0))).2
        apply hkNotΓ
        apply mem_circleTrace.mpr
        rw [hΓK]
        exact hkK 0
      have hΩK : Ω.1 ≠ K.1 := by
        intro hΩK
        have heNotΩ := (Finset.mem_sdiff.mp
          (circleChord_subset e
            (chordLabel_mem (circleChordPair e) 0))).2
        apply heNotΩ
        apply mem_circleTrace.mpr
        rw [hΩK]
        exact heK 0
      have heAxis : projectiveChordLine cfg (circleChordPair e) =
          projectiveRadicalAxis Γ.1 K.1 hΓK :=
        projectiveChordLine_eq_projectiveRadicalAxis_of_endpoints
          cfg Γ.1 K.1 hΓK (circleChordPair e)
            (heΓ 0) (heΓ 1) (heK 0) (heK 1)
      have hkAxis : projectiveChordLine cfg (circleChordPair k) =
          projectiveRadicalAxis Ω.1 K.1 hΩK :=
        projectiveChordLine_eq_projectiveRadicalAxis_of_endpoints
          cfg Ω.1 K.1 hΩK (circleChordPair k)

            (hkΩ 0) (hkΩ 1) (hkK 0) (hkK 1)
      unfold firstExclusiveChordCenter secondExclusiveChordCenter
      unfold pairRadicalCenter
      rw [heAxis, hkAxis]
      exact projectiveRadicalAxis_pencil_cross Γ.1 Ω.1 K.1
        (determinedCircle_coe_ne_of_ne hΓΩ) hΓK hΩK

/-- Every cross-block produces a compatible pair of chord centres. -/
theorem crossBlockChordPair_compatible
    (cfg : Configuration α) (Γ Ω : Erdos506.V1.DeterminedCircle cfg) (hΓΩ : Γ ≠ Ω)
    (b : CircleCrossBlock cfg Γ Ω) :
    firstExclusiveChordCenter cfg Γ Ω hΓΩ
        (crossBlockFirstChord cfg Γ Ω b) =
      secondExclusiveChordCenter cfg Γ Ω hΓΩ
        (crossBlockSecondChord cfg Γ Ω b) :=
  chordCenters_eq_of_common_geometricBlock cfg Γ Ω hΓΩ
    (crossBlockFirstChord cfg Γ Ω b)
    (crossBlockSecondChord cfg Γ Ω b) b.1
      (crossBlockFirstChord_subset_support cfg Γ Ω b)
      (crossBlockSecondChord_subset_support cfg Γ Ω b)

/-- Hence the number of cross-blocks is at most the number of compatible
chord pairs. -/
theorem circleCrossBlocks_card_le_compatiblePairs
    (cfg : Configuration α) (Γ Ω : Erdos506.V1.DeterminedCircle cfg) (hΓΩ : Γ ≠ Ω) :
    (circleCrossBlocks cfg Γ Ω).card ≤
      (compatiblePairs
        (firstExclusiveChordCenter cfg Γ Ω hΓΩ)
        (secondExclusiveChordCenter cfg Γ Ω hΓΩ)).card := by
  classical
  let φ : CircleCrossBlock cfg Γ Ω →
      ↥(compatiblePairs
        (firstExclusiveChordCenter cfg Γ Ω hΓΩ)
        (secondExclusiveChordCenter cfg Γ Ω hΓΩ)) := fun b =>
    ⟨crossBlockChordPair cfg Γ Ω b,
      (mem_compatiblePairs _ _ _ _).2
        (crossBlockChordPair_compatible cfg Γ Ω hΓΩ b)⟩
  have hφ : Function.Injective φ := by
    intro b c hbc
    apply crossBlockChordPair_injective cfg Γ Ω
    exact congrArg Subtype.val hbc
  exact (by
    simpa only [Fintype.card_coe] using
      (Fintype.card_le_of_injective φ hφ))

end CrossBlocks

/-! ## Public four-by-four capacity -/

/-- The residual four-by-four cross-block capacity is an unconditional
theorem of real Euclidean/projective geometry. -/
theorem circleCrossBlocks_card_le_ten_of_four_four
    {α : Type*} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (Γ Ω : Erdos506.V1.DeterminedCircle cfg)
    (hΓΩ : Γ ≠ Ω)
    (hfourΓ : (exclusiveCircleTrace cfg Γ Ω).card = 4)
    (hfourΩ : (exclusiveCircleTrace cfg Ω Γ).card = 4) :
    (circleCrossBlocks cfg Γ Ω).card ≤ 10 := by
  classical
  let f := firstExclusiveChordCenter cfg Γ Ω hΓΩ
  let g := secondExclusiveChordCenter cfg Γ Ω hΓΩ
  have hX : Fintype.card (CircleChord (exclusiveCircleTrace cfg Γ Ω)) = 6 :=
    fintype_card_circleChord_of_card_four hfourΓ
  have hY : Fintype.card (CircleChord (exclusiveCircleTrace cfg Ω Γ)) = 6 :=
    fintype_card_circleChord_of_card_four hfourΩ
  have hf : ∀ q, (fullFibre f q).card ≤ 2 := by
    intro q
    exact firstExclusiveChordCenter_fibre_card_le_two
      cfg Γ Ω hΓΩ hfourΓ q
  have hg : ∀ q, (fullFibre g q).card ≤ 2 := by
    intro q
    exact secondExclusiveChordCenter_fibre_card_le_two
      cfg Γ Ω hΓΩ hfourΩ q
  have hnot : ¬ SaturatedThreeCenterProfile f g := by
    exact not_saturatedThreeCenterProfile_exclusiveCircleChords
      cfg Γ Ω hΓΩ hfourΓ
  have hcompatible : (compatiblePairs f g).card ≤ 10 :=
    card_compatiblePairs_le_ten_of_not_saturated
      f g hX hY hf hg hnot
  exact (circleCrossBlocks_card_le_compatiblePairs cfg Γ Ω hΓΩ).trans
    hcompatible

universe u

private theorem realPlaneFourFourCrossBlockPrinciple_four_four
    {α : Type u} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (Γ Ω : Erdos506.V1.DeterminedCircle cfg)
    (hΓΩ : Γ ≠ Ω)
    (hfourΓ : (exclusiveCircleTrace cfg Γ Ω).card = 4)
    (hfourΩ : (exclusiveCircleTrace cfg Ω Γ).card = 4) :
    (circleCrossBlocks cfg Γ Ω).card ≤ 10 := by
  exact circleCrossBlocks_card_le_ten_of_four_four
    cfg Γ Ω hΓΩ hfourΓ hfourΩ

/-- Kernel-checked constructor for the former residual principle. -/
def realPlaneFourFourCrossBlockPrinciple :
    RealPlaneFourFourCrossBlockPrinciple.{u} where
  four_four := realPlaneFourFourCrossBlockPrinciple_four_four

end Erdos506.Incidence
