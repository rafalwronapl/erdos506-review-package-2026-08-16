import Erdos506.Incidence.UngarSixProof

/-!
# The finite counting endpoint of the six-point rotating-line argument

For a direction `D`, its *parallel class* is the finite collection of
unordered pairs of labels whose joining line has direction `D`.  A rotating
line (or allowable-sequence) proof supplies information about these classes:
the switches occurring at one angle are exactly one such class.

The results below deliberately isolate the counting endpoint.  They are not
an additional geometric assumption: once geometry proves a uniform bound on
the size of the parallel classes, the lower bound for determined directions
is automatic.  In particular, a two-switch bound already gives eight
directions for six points, which is stronger than the six directions needed
in the twelve-point branch.
-/

namespace Erdos506.Finite

open Erdos506.Incidence
open Erdos506.V1
open Erdos506.V4

variable {alpha : Type*} [Fintype alpha] [DecidableEq alpha]

/-- The finite parallel class of a projective direction in a labelled
configuration.  This is the batch of pair-switches occurring at that
direction in an allowable sequence. -/
noncomputable def directionPairClass
    (cfg : Configuration alpha) (D : Submodule ℝ Point2) :
    Finset (KSubset alpha 2) :=
  Finset.univ.filter (fun A => directionOfPair cfg A = D)

/-- A uniform bound on the batches of equal-direction pair switches bounds
the total number of pairs by `m` times the number of directions. -/
theorem card_kSubset_two_le_direction_capacity_mul
    (cfg : Configuration alpha) (m : ℕ)
    (hcapacity : ∀ D ∈ determinedDirections cfg,
      (directionPairClass cfg D).card ≤ m) :
    Fintype.card (KSubset alpha 2) ≤ m * (determinedDirections cfg).card := by
  classical
  have hcount := Finset.card_le_mul_card_image
    (Finset.univ : Finset (KSubset alpha 2)) m (by
      intro D hD
      exact hcapacity D (by simpa [determinedDirections] using hD))
  simpa [directionPairClass, determinedDirections] using hcount

/-- The useful easy branch of the six-point Ungar argument: if the
rotating-line analysis shows that no direction has more than two pair
switches, then the configuration determines at least eight directions. -/
theorem eight_le_card_determinedDirections_of_pair_class_cap_two
    (cfg : Configuration (Fin 6))
    (hcapacity : ∀ D ∈ determinedDirections cfg,
      (directionPairClass cfg D).card ≤ 2) :
    8 ≤ (determinedDirections cfg).card := by
  have hcount := card_kSubset_two_le_direction_capacity_mul cfg 2 hcapacity
  have hchoose : Nat.choose 6 2 = 15 := by decide
  have hpairs : Fintype.card (KSubset (Fin 6) 2) = 15 := by
    rw [card_kSubset]
    simpa using hchoose
  omega

/-- The sharp finite reduction for the six-point rotating-line proof.  If
every direction batch has at most three switches, then fewer than six
directions can occur only in the unique extremal situation in which *every*
batch has exactly three switches.  Thus an allowable-sequence proof of
Ungar only has to exclude this equality case; it does not need any further
counting argument. -/
theorem six_le_card_determinedDirections_of_pair_class_cap_three
    (cfg : Configuration (Fin 6))
    (hcapacity : ∀ D ∈ determinedDirections cfg,
      (directionPairClass cfg D).card ≤ 3)
    (hstrict : ∃ D ∈ determinedDirections cfg,
      (directionPairClass cfg D).card ≤ 2) :
    6 ≤ (determinedDirections cfg).card := by
  classical
  let S := determinedDirections cfg
  let f : Submodule ℝ Point2 → ℕ := fun D => (directionPairClass cfg D).card
  have hchoose : Nat.choose 6 2 = 15 := by decide
  have hpairs : Fintype.card (KSubset (Fin 6) 2) = 15 := by
    rw [card_kSubset]
    simpa using hchoose
  have hsum : 15 = ∑ D ∈ S, f D := by
    have h := Finset.card_eq_sum_card_image (directionOfPair cfg)
      (Finset.univ : Finset (KSubset (Fin 6) 2))
    simpa [S, f, directionPairClass, determinedDirections, hpairs] using h
  obtain ⟨D, hD, hDsmall⟩ := hstrict
  change 6 ≤ S.card
  have hrest : ∑ E ∈ S.erase D, f E ≤ 3 * (S.erase D).card := by
    calc
      ∑ E ∈ S.erase D, f E ≤ ∑ _E ∈ S.erase D, 3 := by
        apply Finset.sum_le_sum
        intro E hE
        exact hcapacity E (by simpa [S] using (Finset.mem_erase.mp hE).2)
      _ = 3 * (S.erase D).card := by simp [Nat.mul_comm]
  have hsplit : f D + ∑ E ∈ S.erase D, f E = ∑ E ∈ S, f E :=
    Finset.add_sum_erase S f (by simpa [S] using hD)
  have hDsmall' : f D ≤ 2 := by simpa [S, f] using hDsmall
  have herase : (S.erase D).card = S.card - 1 :=
    Finset.card_erase_of_mem (by simpa [S] using hD)
  omega

end Erdos506.Finite
