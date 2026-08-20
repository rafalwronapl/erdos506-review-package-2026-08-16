import Erdos506.V1.TwelveDirectionProof

/-!
# The six-point direction problem

This file records the lossless finite reductions for the six-point instance
of Ungar's direction theorem.  The direction census itself is the one
defined in `V1.TwelveDirectionProof`; no additional geometric principle is
assumed here.

The remaining theorem is the genuinely geometric assertion that every
noncollinear six-point configuration supplies the certificate constructed
below.  Keeping the certificate explicit separates that missing angular/
rotating-line argument from the finite bookkeeping used by its consumers.
-/

namespace Erdos506.Incidence

open Erdos506.Finite
open Erdos506.V1
open Erdos506.V4

variable {alpha : Type*} [Fintype alpha] [DecidableEq alpha]

/-- Every pair direction occurs in the finite census of all determined
directions. -/
theorem directionOfPair_mem_determinedDirections
    (cfg : Configuration alpha) (A : KSubset alpha 2) :
    directionOfPair cfg A ∈ determinedDirections cfg := by
  classical
  unfold determinedDirections
  exact Finset.mem_image.mpr ⟨A, Finset.mem_univ _, rfl⟩

/-- Six explicitly indexed pair directions certify the desired lower bound.
This is a purely finite statement: the injectivity hypothesis says exactly
that the six displayed pair directions are different. -/
theorem six_le_card_determinedDirections_of_pair_witness
    (cfg : Configuration alpha) (w : Fin 6 → KSubset alpha 2)
    (hw : Function.Injective (fun i => directionOfPair cfg (w i))) :
    6 ≤ (determinedDirections cfg).card := by
  classical
  let W : Finset (Submodule ℝ Point2) :=
    Finset.univ.image (fun i => directionOfPair cfg (w i))
  have hW : W ⊆ determinedDirections cfg := by
    intro D hD
    obtain ⟨i, _hi, rfl⟩ := Finset.mem_image.mp hD
    exact directionOfPair_mem_determinedDirections cfg (w i)
  calc
    6 = W.card := by
      dsimp [W]
      rw [Finset.card_image_of_injective _ hw]
      simp
    _ ≤ (determinedDirections cfg).card := Finset.card_le_card hW

/-- An affine normalization is lossless for the six-direction lower bound.
Consequently a rotating-line proof may first move any convenient affine frame
to standard coordinates and only has to construct a pair witness there. -/
theorem six_le_card_determinedDirections_of_affineEquiv
    (e : Point2 ≃ᵃ[ℝ] Point2) (cfg : Configuration alpha)
    (h : 6 ≤ (determinedDirections (affineEquivConfiguration e cfg)).card) :
    6 ≤ (determinedDirections cfg).card := by
  rw [card_determinedDirections_affineEquiv] at h
  exact h

/-- In a noncollinear labelled six-point configuration, the two fixed labels
`0, 1` and some third label form a noncollinear triangle.  This is the first
lossless step of a possible affine-frame normalization. -/
theorem exists_noncollinear_triple_finSix
    (cfg : Configuration (Fin 6)) (hnon : Noncollinear cfg) :
    ∃ c : Fin 6, ¬ Collinear ℝ ({cfg 0, cfg 1, cfg c} : Set Point2) := by
  classical
  by_contra h
  apply hnon
  have h01 : cfg 0 ≠ cfg 1 := cfg.injective.ne (by decide)
  rw [collinear_iff_of_mem (show cfg 0 ∈ pointSet cfg by exact ⟨0, rfl⟩)]
  refine ⟨cfg 1 -ᵥ cfg 0, ?_⟩
  intro p hp
  obtain ⟨c, rfl⟩ := hp
  have hcol : Collinear ℝ ({cfg 0, cfg 1, cfg c} : Set Point2) := by
    by_contra hnot
    exact h ⟨c, hnot⟩
  have hmem : cfg c ∈ affineSpan ℝ ({cfg 0, cfg 1} : Set Point2) :=
    hcol.mem_affineSpan_of_mem_of_ne (by simp) (by simp) (by simp) h01
  obtain ⟨t, ht⟩ := mem_affineSpan_pair_iff_exists_lineMap_eq.mp hmem
  exact ⟨t, by rw [← ht, AffineMap.lineMap_apply]⟩

end Erdos506.Incidence
