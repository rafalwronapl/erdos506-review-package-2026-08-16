import Erdos506.Incidence.SixConicEventsPrinciple
import Mathlib.Tactic

/-!
# The four active signatures on six marked conic points

The elementary incidence API already proves that a full signature consists
of three pairwise-disjoint marked pairs.  Since the selected trace has six
points, this is a perfect matching of that trace.

The remaining real-projective step in S1 is different.  Projection from the
common centre of the three chords must be promoted to a projective
involution of the conic.  After cyclically labelling the six real points,
that involution preserves or reverses cyclic order.  Its fixed-point-free
action on the marked labels is therefore one of

* `R3 = 03 | 14 | 25`,
* `S1 = 01 | 25 | 34`,
* `S3 = 03 | 12 | 45`,
* `S5 = 05 | 14 | 23`.

`ProjectiveCoordinates` and `CompleteQuadrangle` currently provide
homogeneous points, chord lines, and the noncollinearity of a complete
quadrangle's diagonal points.  They do not yet provide a projective
parameterization of a nonsingular conic, its residual-intersection
involution, or cyclic-order preservation.  Consequently this file exposes
that missing geometry as positive classification data, rather than hiding
the desired cardinal inequality in an assumption.  Once the classification
witness is constructed from coordinates, the cap four below is purely
finite.
-/

namespace Erdos506.Incidence

open Erdos506.V1
open Erdos506.V4
open scoped BigOperators

universe u

/-! ## The already available perfect-matching reduction -/

/-- A finite family of pairs is a perfect matching of `vertices` when its
members are two-subsets of `vertices`, are pairwise disjoint, and cover all
vertices. -/
structure SixConicPerfectMatchingOn
    {alpha : Type*} [DecidableEq alpha]
    (vertices : Finset alpha) (matching : Finset (Finset alpha)) : Prop where
  pair : ∀ p ∈ matching, p.card = 2 ∧ p ⊆ vertices
  pairwiseDisjoint :
    (matching : Set (Finset alpha)).PairwiseDisjoint id
  covers : matching.biUnion id = vertices

/-- Every active full signature is already provably a perfect matching of
the selected six-point trace.  No projective involution theorem is used in
this reduction. -/
theorem sixConic_activeSignature_isPerfectMatching
    {alpha : Type u} [Fintype alpha] [DecidableEq alpha]
    (cfg : Configuration alpha) (gamma : DeterminedCircle cfg)
    (hgamma : (circleTrace cfg gamma.1).card = 6)
    (X : Finset alpha)
    (hdisjoint : Disjoint (circleTrace cfg gamma.1) X)
    {signature : Finset (Finset alpha)}
    (hsignature :
      signature ∈ sixConicActiveSignatures cfg gamma X) :
    SixConicPerfectMatchingOn
      (circleTrace cfg gamma.1) signature := by
  classical
  rw [sixConicActiveSignatures] at hsignature
  obtain ⟨e, heFull, rfl⟩ := Finset.mem_image.mp hsignature
  have heData := mem_sixConicFullEdges.mp heFull
  have hePow := Finset.mem_powersetCard.mp heData.1
  have heDisjoint : Disjoint e (circleTrace cfg gamma.1) :=
    hdisjoint.symm.mono_left hePow.1
  have hsignatureCard :
      (sixConicSignature cfg gamma e).card = 3 := by
    rw [card_sixConicSignature hePow.2 heDisjoint, heData.2]
  have hpairs : ∀ p ∈ sixConicSignature cfg gamma e,
      p.card = 2 ∧ p ⊆ circleTrace cfg gamma.1 := by
    intro p hp
    exact sixConicSignature_pair hp
  have hpairwise :
      ((sixConicSignature cfg gamma e : Finset (Finset alpha)) :
        Set (Finset alpha)).PairwiseDisjoint id :=
    sixConicSignature_pairwiseDisjoint hePow.2 heDisjoint
  have hunionSubset :
      (sixConicSignature cfg gamma e).biUnion id ⊆
        circleTrace cfg gamma.1 := by
    intro x hx
    rcases Finset.mem_biUnion.mp hx with ⟨p, hp, hxp⟩
    exact (hpairs p hp).2 hxp
  have hunionCard :
      ((sixConicSignature cfg gamma e).biUnion id).card = 6 := by
    rw [Finset.card_biUnion hpairwise]
    calc
      (∑ p ∈ sixConicSignature cfg gamma e, (id p).card) =
          ∑ _p ∈ sixConicSignature cfg gamma e, 2 := by
        apply Finset.sum_congr rfl
        intro p hp
        exact (hpairs p hp).1
      _ = 2 * (sixConicSignature cfg gamma e).card := by
        simp [Nat.mul_comm]
      _ = 6 := by omega
  have hcover :
      (sixConicSignature cfg gamma e).biUnion id =
        circleTrace cfg gamma.1 := by
    apply Finset.eq_of_subset_of_card_le hunionSubset
    rw [hgamma, hunionCard]
  exact ⟨hpairs, hpairwise, hcover⟩

/-! ## Four cyclic involution matchings -/

/-- Codes for `R3`, `S1`, `S3`, and `S5`, in that order. -/
abbrev SixCycleInvolutionCode := Fin 4

/-- The half-turn matching `R3`. -/
def sixCycleR3Matching : Finset (Finset (Fin 6)) :=
  {{0, 3}, {1, 4}, {2, 5}}

/-- The edge-reflection matching `S1`. -/
def sixCycleS1Matching : Finset (Finset (Fin 6)) :=
  {{0, 1}, {2, 5}, {3, 4}}

/-- The edge-reflection matching `S3`. -/
def sixCycleS3Matching : Finset (Finset (Fin 6)) :=
  {{0, 3}, {1, 2}, {4, 5}}

/-- The edge-reflection matching `S5`. -/
def sixCycleS5Matching : Finset (Finset (Fin 6)) :=
  {{0, 5}, {1, 4}, {2, 3}}

/-- The four fixed-point-free involution matchings of six cyclic labels. -/
def sixCycleDihedralMatching
    (code : SixCycleInvolutionCode) : Finset (Finset (Fin 6)) :=
  ![sixCycleR3Matching, sixCycleS1Matching,
    sixCycleS3Matching, sixCycleS5Matching] code

/-- Relabel a canonical cyclic matching by six actual point labels. -/
noncomputable def relabelSixCycleMatching
    {alpha : Type*} [DecidableEq alpha]
    (label : Fin 6 -> alpha) (code : SixCycleInvolutionCode) :
    Finset (Finset alpha) :=
  (sixCycleDihedralMatching code).image
    (fun pair => pair.image label)

/-! ## The exact missing geometric bridge -/

/-- Positive data supplied by the real-conic involution argument.

`cyclicLabel` identifies the actual marked trace with six labels in its real
cyclic order.  The present point/configuration API has no predicate recording
that order, so its geometric force is recorded by `classified`: every active
signature is the relabelling of one of the four explicit dihedral
fixed-point-free involution matchings above.

This is deliberately not a field saying that the number of signatures is at
most four.  It retains the cyclic labelling and the matching realized by each
signature, which are the constructive outputs needed from the future
coordinate proof. -/
structure SixConicActiveSignatureDihedralWitness
    {alpha : Type u} [Fintype alpha] [DecidableEq alpha]
    (cfg : Configuration alpha) (gamma : DeterminedCircle cfg)
    (X : Finset alpha) where
  cyclicLabel :
    Fin 6 ≃ {x : alpha // x ∈ circleTrace cfg gamma.1}
  classified :
    ∀ signature ∈ sixConicActiveSignatures cfg gamma X,
      ∃ code : SixCycleInvolutionCode,
        signature = relabelSixCycleMatching
          (fun i => (cyclicLabel i).1) code

/-- Once the real-conic classification witness has been constructed, the
four-signature bound is the finite image bound for the four codes
`R3,S1,S3,S5`.  The surrounding hypotheses match the former S1 field and
make this theorem a direct eventual call-site replacement. -/
theorem sixConic_activeSignatures_card_le_four_of_dihedralWitness
    {alpha : Type u} [Fintype alpha] [DecidableEq alpha]
    (cfg : Configuration alpha) (gamma : DeterminedCircle cfg)
    (_hgamma : (circleTrace cfg gamma.1).card = 6)
    (X : Finset alpha)
    (_hdisjoint : Disjoint (circleTrace cfg gamma.1) X)
    (witness : SixConicActiveSignatureDihedralWitness cfg gamma X) :
    (sixConicActiveSignatures cfg gamma X).card ≤ 4 := by
  classical
  let candidates : Finset (Finset (Finset alpha)) :=
    (Finset.univ : Finset SixCycleInvolutionCode).image
      (fun code => relabelSixCycleMatching
        (fun i => (witness.cyclicLabel i).1) code)
  have hsubset : sixConicActiveSignatures cfg gamma X ⊆
      candidates := by
    intro signature hsignature
    obtain ⟨code, hcode⟩ :=
      witness.classified signature hsignature
    exact Finset.mem_image.mpr
      ⟨code, Finset.mem_univ code, hcode.symm⟩
  calc
    (sixConicActiveSignatures cfg gamma X).card ≤ candidates.card :=
      Finset.card_le_card hsubset
    _ ≤ (Finset.univ : Finset SixCycleInvolutionCode).card := by
      dsimp only [candidates]
      exact Finset.card_image_le
    _ = 4 := by simp [SixCycleInvolutionCode]

end Erdos506.Incidence
