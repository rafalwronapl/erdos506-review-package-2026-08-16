import Erdos506.Incidence.RadicalAxisFourFour
import Erdos506.Incidence.RadicalAxisFiveFiveLedger

/-!
# Radical-axis geometry for the five-by-five cross-block endpoint

This module combines the existing radical-axis chord geometry with the
ten-by-ten finite ledger.  It gives the unconditional cross-block capacity
twenty and packages the equality case as a canonical equivalence between
cross-blocks and compatible chord pairs.
-/

namespace Erdos506.Incidence

open Erdos506.Block.BlockSystem
open Erdos506.Finite
open Erdos506.V1
open Erdos506.V3
open Erdos506.V4
open Matrix
open scoped BigOperators LinearAlgebra.Projectivization

section FiveChordGeometry

variable {α : Type*} [Fintype α] [DecidableEq α]

omit [Fintype α] [DecidableEq α] in
/-- A five-point trace has ten unordered chords. -/
theorem fintype_card_circleChord_of_card_five
    {A : Finset α} (hA : A.card = 5) :
    Fintype.card (CircleChord A) = 10 := by
  rw [fintype_card_circleChord, hA]
  norm_num [Nat.choose]

omit [Fintype α] in
/-- A pairwise-disjoint family of chords in a set of at most five points
contains at most two chords. -/
theorem card_circleChords_le_two_of_pairwise_disjoint_of_card_le_five
    {A : Finset α} (hA : A.card ≤ 5)
    (F : Finset (CircleChord A))
    (hdisj : (F : Set (CircleChord A)).PairwiseDisjoint fun e => e.1) :
    F.card ≤ 2 := by
  classical
  have hunionSubset : F.biUnion (fun e => e.1) ⊆ A := by
    intro x hx
    obtain ⟨e, heF, hxe⟩ := Finset.mem_biUnion.mp hx
    exact circleChord_subset e hxe
  have hunionLe : (F.biUnion (fun e => e.1)).card ≤ 5 :=
    (Finset.card_le_card hunionSubset).trans hA
  have hunionCard : (F.biUnion (fun e => e.1)).card = 2 * F.card := by
    rw [Finset.card_biUnion hdisj]
    calc
      (∑ e ∈ F, e.1.card) = ∑ _e ∈ F, 2 := by
        apply Finset.sum_congr rfl
        intro e _he
        exact circleChord_card e
      _ = 2 * F.card := by simp [Nat.mul_comm]
  rw [hunionCard] at hunionLe
  omega

/-- Symmetric equal-centre disjointness for chords of the second exclusive
trace. -/
theorem secondExclusiveChords_disjoint_of_eq_center
    (cfg : Configuration α) (Γ Ω : Erdos506.V1.DeterminedCircle cfg)
    (hΓΩ : Γ ≠ Ω)
    (e k : CircleChord (exclusiveCircleTrace cfg Ω Γ)) (hek : e ≠ k)
    (hcenter : secondExclusiveChordCenter cfg Γ Ω hΓΩ e =
      secondExclusiveChordCenter cfg Γ Ω hΓΩ k) :
    Disjoint e.1 k.1 := by
  apply circleChords_disjoint_of_eq_pairRadicalCenter
    cfg Ω.1 Γ.1 Ω.1 (determinedCircle_coe_ne_of_ne hΓΩ)
      (exclusiveCircleTrace cfg Ω Γ)
  · intro x hx
    exact mem_circleTrace.mp (Finset.mem_sdiff.mp hx).1
  · intro x hx
    have hx' := Finset.mem_sdiff.mp hx
    exact not_projectivePoint_orthogonal_projectiveRadicalAxis_of_not_mem_mem
      (determinedCircle_coe_ne_of_ne hΓΩ)
        (by simpa using hx'.2) (mem_circleTrace.mp hx'.1)
  · exact hek
  · exact hcenter

/-- Every centre fibre for a first exclusive five-trace contains at most
two chords. -/
theorem firstExclusiveChordCenter_fibre_card_le_two_of_card_five
    (cfg : Configuration α) (Γ Ω : Erdos506.V1.DeterminedCircle cfg)
    (hΓΩ : Γ ≠ Ω)
    (hfirst : (exclusiveCircleTrace cfg Γ Ω).card = 5)
    (q : RealProjectivePlane) :
    (fullFibre (firstExclusiveChordCenter cfg Γ Ω hΓΩ) q).card ≤ 2 := by
  classical
  apply card_circleChords_le_two_of_pairwise_disjoint_of_card_le_five
    (by omega)
  intro e he k hk hek
  apply firstExclusiveChords_disjoint_of_eq_center cfg Γ Ω hΓΩ e k hek
  change e ∈ fullFibre (firstExclusiveChordCenter cfg Γ Ω hΓΩ) q at he
  change k ∈ fullFibre (firstExclusiveChordCenter cfg Γ Ω hΓΩ) q at hk
  exact ((mem_fullFibre _ q e).mp he).trans
    ((mem_fullFibre _ q k).mp hk).symm

/-- Every centre fibre for a second exclusive five-trace contains at most
two chords. -/
theorem secondExclusiveChordCenter_fibre_card_le_two_of_card_five
    (cfg : Configuration α) (Γ Ω : Erdos506.V1.DeterminedCircle cfg)
    (hΓΩ : Γ ≠ Ω)
    (hsecond : (exclusiveCircleTrace cfg Ω Γ).card = 5)
    (q : RealProjectivePlane) :
    (fullFibre (secondExclusiveChordCenter cfg Γ Ω hΓΩ) q).card ≤ 2 := by
  classical
  apply card_circleChords_le_two_of_pairwise_disjoint_of_card_le_five
    (by omega)
  intro e he k hk hek
  apply secondExclusiveChords_disjoint_of_eq_center cfg Γ Ω hΓΩ e k hek
  change e ∈ fullFibre (secondExclusiveChordCenter cfg Γ Ω hΓΩ) q at he
  change k ∈ fullFibre (secondExclusiveChordCenter cfg Γ Ω hΓΩ) q at hk
  exact ((mem_fullFibre _ q e).mp he).trans
    ((mem_fullFibre _ q k).mp hk).symm

end FiveChordGeometry

/-! ## Five-by-five cross-block capacity -/

section FiveFiveCrossBlocks

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- Two disjoint five-point traces admit at most twenty cross-blocks. -/
theorem circleCrossBlocks_card_le_twenty_of_five_five
    (cfg : Configuration α) (Γ Ω : Erdos506.V1.DeterminedCircle cfg)
    (_hΓΩ : Γ ≠ Ω)
    (hfirst : (exclusiveCircleTrace cfg Γ Ω).card = 5)
    (hsecond : (exclusiveCircleTrace cfg Ω Γ).card = 5) :
    (circleCrossBlocks cfg Γ Ω).card ≤ 20 := by
  classical
  let D := exclusiveCircleTrace cfg Γ Ω
  let E := exclusiveCircleTrace cfg Ω Γ
  let F := circleCrossBlocks cfg Γ Ω
  have hDE : Disjoint D E := by
    exact exclusiveCircleTrace_disjoint cfg Γ Ω
  have htwoD : ∀ b ∈ F,
      ((geometricBlockSystem cfg).support b ∩ D).card = 2 := by
    intro b hb
    exact (Finset.mem_filter.mp hb).2.1
  have htwoE : ∀ b ∈ F,
      ((geometricBlockSystem cfg).support b ∩ E).card = 2 := by
    intro b hb
    exact (Finset.mem_filter.mp hb).2.2
  have hbound := (geometricBlockSystem cfg).relative_two_two_capacity_between
    D E F hDE htwoD
  have hsum :
      (∑ b ∈ F,
        Nat.choose ((geometricBlockSystem cfg).support b ∩ E).card 2) =
        F.card := by
    calc
      (∑ b ∈ F,
          Nat.choose ((geometricBlockSystem cfg).support b ∩ E).card 2) =
          ∑ _b ∈ F, 1 := by
        apply Finset.sum_congr rfl
        intro b hb
        rw [htwoE b hb]
        norm_num
      _ = F.card := by simp
  rw [hsum] at hbound
  change D.card = 5 at hfirst
  change E.card = 5 at hsecond
  norm_num [hfirst, hsecond, Nat.choose] at hbound
  simpa only [F] using hbound

/-! ## Canonical compatible-pair map and equality equivalence -/

/-- A cross-block bundled with the proof that its two chord centres agree. -/
noncomputable def crossBlockCompatiblePair
    (cfg : Configuration α) (Γ Ω : Erdos506.V1.DeterminedCircle cfg)
    (hΓΩ : Γ ≠ Ω) :
    CircleCrossBlock cfg Γ Ω →
      ↥(compatiblePairs
        (firstExclusiveChordCenter cfg Γ Ω hΓΩ)
        (secondExclusiveChordCenter cfg Γ Ω hΓΩ)) :=
  fun H =>
    ⟨crossBlockChordPair cfg Γ Ω H,
      (mem_compatiblePairs _ _ _ _).2
        (crossBlockChordPair_compatible cfg Γ Ω hΓΩ H)⟩

@[simp] theorem crossBlockCompatiblePair_val
    (cfg : Configuration α) (Γ Ω : Erdos506.V1.DeterminedCircle cfg)
    (hΓΩ : Γ ≠ Ω) (H : CircleCrossBlock cfg Γ Ω) :
    (crossBlockCompatiblePair cfg Γ Ω hΓΩ H).1 =
      crossBlockChordPair cfg Γ Ω H := rfl

/-- The canonical compatible-pair map is injective. -/
theorem crossBlockCompatiblePair_injective
    (cfg : Configuration α) (Γ Ω : Erdos506.V1.DeterminedCircle cfg)
    (hΓΩ : Γ ≠ Ω) :
    Function.Injective (crossBlockCompatiblePair cfg Γ Ω hΓΩ) := by
  intro H K hHK
  apply crossBlockChordPair_injective cfg Γ Ω
  exact congrArg Subtype.val hHK

/-- Equality of finite cardinalities upgrades the canonical injection to an
equivalence. -/
noncomputable def crossBlockCompatiblePairEquiv
    (cfg : Configuration α) (Γ Ω : Erdos506.V1.DeterminedCircle cfg)
    (hΓΩ : Γ ≠ Ω)
    (hcard :
      Fintype.card (CircleCrossBlock cfg Γ Ω) =
        Fintype.card
          ↥(compatiblePairs
            (firstExclusiveChordCenter cfg Γ Ω hΓΩ)
            (secondExclusiveChordCenter cfg Γ Ω hΓΩ))) :
    CircleCrossBlock cfg Γ Ω ≃
      ↥(compatiblePairs
        (firstExclusiveChordCenter cfg Γ Ω hΓΩ)
        (secondExclusiveChordCenter cfg Γ Ω hΓΩ)) :=
  Equiv.ofBijective (crossBlockCompatiblePair cfg Γ Ω hΓΩ)
    ((Fintype.bijective_iff_injective_and_card _).2
      ⟨crossBlockCompatiblePair_injective cfg Γ Ω hΓΩ, hcard⟩)

@[simp] theorem crossBlockCompatiblePairEquiv_apply_val
    (cfg : Configuration α) (Γ Ω : Erdos506.V1.DeterminedCircle cfg)
    (hΓΩ : Γ ≠ Ω)
    (hcard :
      Fintype.card (CircleCrossBlock cfg Γ Ω) =
        Fintype.card
          ↥(compatiblePairs
            (firstExclusiveChordCenter cfg Γ Ω hΓΩ)
            (secondExclusiveChordCenter cfg Γ Ω hΓΩ)))
    (H : CircleCrossBlock cfg Γ Ω) :
    (crossBlockCompatiblePairEquiv cfg Γ Ω hΓΩ hcard H).1 =
      crossBlockChordPair cfg Γ Ω H := rfl

@[simp] theorem crossBlockCompatiblePairEquiv_symm_val
    (cfg : Configuration α) (Γ Ω : Erdos506.V1.DeterminedCircle cfg)
    (hΓΩ : Γ ≠ Ω)
    (hcard :
      Fintype.card (CircleCrossBlock cfg Γ Ω) =
        Fintype.card
          ↥(compatiblePairs
            (firstExclusiveChordCenter cfg Γ Ω hΓΩ)
            (secondExclusiveChordCenter cfg Γ Ω hΓΩ)))
    (p :
      ↥(compatiblePairs
        (firstExclusiveChordCenter cfg Γ Ω hΓΩ)
        (secondExclusiveChordCenter cfg Γ Ω hΓΩ))) :
    crossBlockChordPair cfg Γ Ω
        ((crossBlockCompatiblePairEquiv cfg Γ Ω hΓΩ hcard).symm p) =
      p.1 := by
  have happly :=
    (crossBlockCompatiblePairEquiv cfg Γ Ω hΓΩ hcard).apply_symm_apply p
  simpa only [crossBlockCompatiblePairEquiv_apply_val] using
    congrArg Subtype.val happly

/-! ## Packaged equality data -/

/-- Complete equality data at the five-by-five cross-block endpoint. -/
structure FiveFiveCrossBlockSaturationData
    (cfg : Configuration α) (Γ Ω : Erdos506.V1.DeterminedCircle cfg)
    (hΓΩ : Γ ≠ Ω) where
  firstExclusiveCard :
    (exclusiveCircleTrace cfg Γ Ω).card = 5
  secondExclusiveCard :
    (exclusiveCircleTrace cfg Ω Γ).card = 5
  crossBlockCard :
    Fintype.card (CircleCrossBlock cfg Γ Ω) = 20
  compatiblePairCard :
    (compatiblePairs
      (firstExclusiveChordCenter cfg Γ Ω hΓΩ)
      (secondExclusiveChordCenter cfg Γ Ω hΓΩ)).card = 20
  profile :
    SaturatedFiveCenterProfile
      (firstExclusiveChordCenter cfg Γ Ω hΓΩ)
      (secondExclusiveChordCenter cfg Γ Ω hΓΩ)

namespace FiveFiveCrossBlockSaturationData

variable {cfg : Configuration α}
  {Γ Ω : Erdos506.V1.DeterminedCircle cfg}
  {hΓΩ : Γ ≠ Ω}

/-- Saturation forces the two chord-centre images to coincide. -/
theorem centreImages_eq
    (d : FiveFiveCrossBlockSaturationData cfg Γ Ω hΓΩ) :
    (by classical
      exact Finset.univ.image (secondExclusiveChordCenter cfg Γ Ω hΓΩ)) =
      (by classical
        exact Finset.univ.image (firstExclusiveChordCenter cfg Γ Ω hΓΩ)) := by
  exact image_eq_of_saturatedFiveCenterProfile
    (firstExclusiveChordCenter cfg Γ Ω hΓΩ)
    (secondExclusiveChordCenter cfg Γ Ω hΓΩ)
    (fintype_card_circleChord_of_card_five d.secondExclusiveCard)
    d.profile

/-- The canonical cross-block/compatible-pair equivalence at saturation. -/
noncomputable def crossBlockEquiv
    (d : FiveFiveCrossBlockSaturationData cfg Γ Ω hΓΩ) :
    CircleCrossBlock cfg Γ Ω ≃
      ↥(compatiblePairs
        (firstExclusiveChordCenter cfg Γ Ω hΓΩ)
        (secondExclusiveChordCenter cfg Γ Ω hΓΩ)) := by
  have hcompatible :
      Fintype.card
        ↥(compatiblePairs
          (firstExclusiveChordCenter cfg Γ Ω hΓΩ)
          (secondExclusiveChordCenter cfg Γ Ω hΓΩ)) = 20 := by
    simpa only [Fintype.card_coe] using d.compatiblePairCard
  exact crossBlockCompatiblePairEquiv cfg Γ Ω hΓΩ
    (d.crossBlockCard.trans hcompatible.symm)

@[simp] theorem crossBlockEquiv_apply_val
    (d : FiveFiveCrossBlockSaturationData cfg Γ Ω hΓΩ)
    (H : CircleCrossBlock cfg Γ Ω) :
    (d.crossBlockEquiv H).1 = crossBlockChordPair cfg Γ Ω H := rfl

@[simp] theorem crossBlockEquiv_symm_val
    (d : FiveFiveCrossBlockSaturationData cfg Γ Ω hΓΩ)
    (p :
      ↥(compatiblePairs
        (firstExclusiveChordCenter cfg Γ Ω hΓΩ)
        (secondExclusiveChordCenter cfg Γ Ω hΓΩ))) :
    crossBlockChordPair cfg Γ Ω (d.crossBlockEquiv.symm p) = p.1 := by
  have happly := d.crossBlockEquiv.apply_symm_apply p
  simpa only [crossBlockEquiv_apply_val] using
    congrArg Subtype.val happly

end FiveFiveCrossBlockSaturationData

/-- Twenty cross-blocks force the complete five-centre equality package. -/
theorem fiveFiveCrossBlockSaturationData_of_cross_card_twenty
    (cfg : Configuration α) (Γ Ω : Erdos506.V1.DeterminedCircle cfg)
    (hΓΩ : Γ ≠ Ω)
    (hfirst : (exclusiveCircleTrace cfg Γ Ω).card = 5)
    (hsecond : (exclusiveCircleTrace cfg Ω Γ).card = 5)
    (hcross : Fintype.card (CircleCrossBlock cfg Γ Ω) = 20) :
    FiveFiveCrossBlockSaturationData cfg Γ Ω hΓΩ := by
  let f := firstExclusiveChordCenter cfg Γ Ω hΓΩ
  let g := secondExclusiveChordCenter cfg Γ Ω hΓΩ
  have hX : Fintype.card (CircleChord
      (exclusiveCircleTrace cfg Γ Ω)) = 10 :=
    fintype_card_circleChord_of_card_five hfirst
  have hY : Fintype.card (CircleChord
      (exclusiveCircleTrace cfg Ω Γ)) = 10 :=
    fintype_card_circleChord_of_card_five hsecond
  have hf : ∀ q, (fullFibre f q).card ≤ 2 := by
    intro q
    exact firstExclusiveChordCenter_fibre_card_le_two_of_card_five
      cfg Γ Ω hΓΩ hfirst q
  have hg : ∀ q, (fullFibre g q).card ≤ 2 := by
    intro q
    exact secondExclusiveChordCenter_fibre_card_le_two_of_card_five
      cfg Γ Ω hΓΩ hsecond q
  have hcompatibleLe : (compatiblePairs f g).card ≤ 20 :=
    card_compatiblePairs_le_twenty f g hX hg
  have hcrossFinset : (circleCrossBlocks cfg Γ Ω).card = 20 := by
    simpa only [Fintype.card_coe] using hcross
  have hcrossLe : (circleCrossBlocks cfg Γ Ω).card ≤
      (compatiblePairs f g).card := by
    simpa only [f, g] using
      circleCrossBlocks_card_le_compatiblePairs cfg Γ Ω hΓΩ
  have hcompatible : (compatiblePairs f g).card = 20 := by omega
  have hprofile : SaturatedFiveCenterProfile f g :=
    saturatedFiveCenterProfile_of_card_compatiblePairs_eq_twenty
      f g hX hY hf hg hcompatible
  refine
    { firstExclusiveCard := hfirst
      secondExclusiveCard := hsecond
      crossBlockCard := hcross
      compatiblePairCard := ?_
      profile := ?_ }
  · simpa only [f, g] using hcompatible
  · simpa only [f, g] using hprofile

end FiveFiveCrossBlocks

end Erdos506.Incidence
