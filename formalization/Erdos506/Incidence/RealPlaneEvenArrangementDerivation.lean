import Erdos506.Incidence.RealPlaneMelchiorDerivation
import Erdos506.Incidence.RealProjectiveEvenArrangementColorFinish
import Erdos506.Incidence.CellulationTwoColorExcess

/-!
# The real-plane even-arrangement principle from the common cellulation

The actual parity colouring of the projective arrangement is now available:
every geometric edge has exactly one incident face of each colour.  This
file connects that geometric result to the finite two-colour excess identity
and then transports the resulting slack obstruction back to determined
lines.

Consequently the even-arrangement principle needs no topological input beyond
the same `RealProjectiveArrangementGlobalInput` already isolated for
Melchior.  Once Euler and the three-edges-per-face theorem are supplied, the
two global principles are discharged together.
-/

namespace Erdos506.Incidence

open Erdos506.V4

universe u

noncomputable local instance arrangementFaceFintypeForEvenArrangementDerivation
    {Line : Type*} [Fintype Line] [DecidableEq Line]
    (A : FiniteProjectiveLineArrangement Line) : Fintype A.ArrangementFace :=
  A.arrangementFaceFintype

/-- A noncollinear configuration has a nontrivial label type.  This small
helper only chooses a base line for the normalized projective sign word. -/
private theorem nontrivial_of_noncollinear
    {alpha : Type u} [Fintype alpha] [DecidableEq alpha]
    (cfg : Configuration alpha) (hnon : Noncollinear cfg) :
    Nontrivial alpha := by
  by_contra htrivial
  haveI : Subsingleton alpha :=
    not_nontrivial_iff_subsingleton.mp htrivial
  apply hnon
  rcases isEmpty_or_nonempty alpha with hEmpty | hNonempty
  · letI : IsEmpty alpha := hEmpty
    have hpointSet : pointSet cfg = ∅ := by
      ext p
      simp [pointSet]
    rw [hpointSet]
    exact collinear_empty ℝ Point2
  · letI : Nonempty alpha := hNonempty
    let a : alpha := Classical.choice hNonempty
    have hsubset : pointSet cfg ⊆ ({cfg a} : Set Point2) := by
      rintro p ⟨b, rfl⟩
      simp [Subsingleton.elim b a]
    exact (collinear_singleton (k := ℝ) (cfg a)).subset hsubset

/-- The common projective cellulation and the actual face parity colouring
exclude Melchior slack one for every even noncollinear configuration. -/
theorem lineMelchiorSlack_ne_one_of_realProjectiveArrangementGlobalInput
    (H : RealProjectiveArrangementGlobalInput.{u})
    {alpha : Type u} [Fintype alpha] [DecidableEq alpha]
    (cfg : Configuration alpha) (hnon : Noncollinear cfg)
    (heven : Even (Fintype.card alpha)) :
    lineMelchiorSlack cfg ≠ 1 := by
  classical
  letI : Nontrivial alpha := nontrivial_of_noncollinear cfg hnon
  let A := labelDualArrangement cfg
  letI : DecidableEq A.GeometricEdge :=
    geometricEdgeDecidableEqForMelchiorDerivation A
  let C := labelDualProjectiveArrangementCellulation H cfg hnon
  let base : alpha := Classical.choice (inferInstance : Nonempty alpha)
  have hA : A.NonPencil := by
    simpa [A] using labelDualArrangement_nonPencil_of_noncollinear cfg hnon
  have hone : ∀ (e : A.GeometricEdge) (b : Bool),
      (Finset.univ.filter fun F : A.ArrangementFace =>
        A.arrangementFaceParityColor base F = b ∧
          e ∈ C.faceBoundary F).card = 1 := by
    intro e b
    change (Finset.univ.filter fun F : A.ArrangementFace =>
      A.arrangementFaceParityColor base F = b ∧
        e ∈ A.arrangementFaceBoundary F).card = 1
    exact A.card_filter_parityColor_and_mem_arrangementFaceBoundary_eq_one
      hA heven base e b
  have hcell : C.melchiorSlack ≠ 1 := by
    exact C.melchiorSlack_ne_one_of_oneFacePerColorAtEveryEdge
      (A.arrangementFaceParityColor base) hone
  have hslack : lineMelchiorSlack cfg = C.melchiorSlack :=
    lineMelchiorSlack_eq_dualCellulationSlack cfg C (fun _L => rfl)
  rw [hslack]
  exact hcell

/-- Assembly of the real-plane even-arrangement principle from precisely the
same global topology package used by the Melchior construction. -/
noncomputable def realPlaneEvenArrangementPrincipleOfGlobalInput
    (H : RealProjectiveArrangementGlobalInput.{u}) :
    RealPlaneEvenArrangementPrinciple.{u} where
  slack_ne_one := fun cfg hnon heven =>
    lineMelchiorSlack_ne_one_of_realProjectiveArrangementGlobalInput
      H cfg hnon heven

end Erdos506.Incidence
