import Erdos506.Incidence.RealPlaneMelchiorDerivation

/-!
# The common global counting boundary for real projective arrangements

`RealProjectiveArrangementTopology` already proves that the actual complement
components are finite and that every actual geometric edge is incident with
exactly two of them.  Consequently its closure-defined boundaries satisfy the
exact face--edge handshake.

There are precisely two further geometric facts in
`RealProjectiveArrangementGlobalInput`:

* Euler's identity for the actual vertices, cyclic edges, and complement
  components;
* every actual face has at least three boundary edges.

Neither fact follows merely from the two-sided-edge theorem.  The shortest
constructive route to Euler is deletion/insertion of one indexed line.  If
the old arrangement cuts the new projective line in `k` distinct points and
`s` of them were not already old vertices, one needs a comparison theorem
saying that the resulting `k` open cyclic arcs split `k` old faces.  The
changes are then `ΔV = s`, `ΔE = k + s`, and `ΔF = k`; this formulation also
handles a new line through old multiple vertices.  The current API has the
cyclic arcs for a fixed arrangement, but does not yet compare faces of an
arrangement with those of a restriction.

For the second fact one needs a cyclic-boundary theorem for a chamber (or,
equivalently, the theorem that the closure of its strict homogeneous sign
cone is a full-dimensional pointed polyhedral cone).  It must identify the
facets of that cone with `arrangementFaceBoundary`.  Pointed cones in
dimension three have at least three facets.  The current API proves the two
faces at an edge, but has no converse theorem producing even one boundary
edge from an arbitrary face, so this step cannot be replaced by local
two-sidedness.

This file records everything after that exact boundary.  In particular, the
signed face-excess identity below is unconditional apart from the already
necessary non-pencil hypothesis.  Its natural-number refinement isolates the
single use of the three-edge theorem and is also the common numerical entry
point for the even-arrangement colouring and the simplicial Gallery-A case.
-/

namespace Erdos506.Incidence

open scoped BigOperators

universe u

namespace FiniteProjectiveLineArrangement

variable {Line : Type u} [Fintype Line] [DecidableEq Line]

noncomputable local instance arrangementFaceFintypeForGlobalFinish
    (A : FiniteProjectiveLineArrangement Line) : Fintype A.ArrangementFace :=
  A.arrangementFaceFintype

noncomputable local instance geometricEdgeDecidableEqForGlobalFinish
    (A : FiniteProjectiveLineArrangement Line) : DecidableEq A.GeometricEdge :=
  Classical.decEq _

/-- The ordinary (natural-number) excess of the boundary of a genuine face
over a triangle. -/
noncomputable def arrangementFaceBoundaryExcess
    (A : FiniteProjectiveLineArrangement Line) (F : A.ArrangementFace) : ℕ :=
  (A.arrangementFaceBoundary F).card - 3

/-- The signed version of face-boundary excess.  Unlike natural subtraction,
this makes sense before the three-edge theorem is available. -/
noncomputable def arrangementFaceBoundarySignedExcess
    (A : FiniteProjectiveLineArrangement Line) (F : A.ArrangementFace) : ℤ :=
  ((A.arrangementFaceBoundary F).card : ℤ) - 3

/-- The already-proved two-sided-edge theorem gives the exact total signed
face excess.  This is the maximal global identity which does not use either
of the two fields still missing from `RealProjectiveArrangementGlobalInput`.
-/
theorem sum_arrangementFaceBoundarySignedExcess_eq
    (A : FiniteProjectiveLineArrangement Line) (hA : A.NonPencil) :
    (∑ F : A.ArrangementFace, A.arrangementFaceBoundarySignedExcess F) =
      2 * (Fintype.card A.GeometricEdge : ℤ) -
        3 * (Fintype.card A.ArrangementFace : ℤ) := by
  classical
  have hhandshake :
      (∑ F : A.ArrangementFace,
          ((A.arrangementFaceBoundary F).card : ℤ)) =
        2 * (Fintype.card A.GeometricEdge : ℤ) := by
    exact_mod_cast
      A.sum_arrangementFaceBoundary_card_eq_two_mul_card_geometricEdge hA
  unfold arrangementFaceBoundarySignedExcess
  rw [Finset.sum_sub_distrib, hhandshake]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  ring

/-- Once every face has at least three sides, the face--edge handshake splits
exactly into the triangular contribution and the sum of natural excesses. -/
theorem three_mul_card_arrangementFace_add_sum_boundaryExcess_eq
    (A : FiniteProjectiveLineArrangement Line) (hA : A.NonPencil)
    (hface : ∀ F : A.ArrangementFace,
      3 ≤ (A.arrangementFaceBoundary F).card) :
    3 * Fintype.card A.ArrangementFace +
        (∑ F : A.ArrangementFace, A.arrangementFaceBoundaryExcess F) =
      2 * Fintype.card A.GeometricEdge := by
  classical
  calc
    3 * Fintype.card A.ArrangementFace +
          (∑ F : A.ArrangementFace, A.arrangementFaceBoundaryExcess F) =
        (∑ _F : A.ArrangementFace, 3) +
          ∑ F : A.ArrangementFace, A.arrangementFaceBoundaryExcess F := by
            simp [mul_comm]
    _ = ∑ F : A.ArrangementFace,
          (3 + A.arrangementFaceBoundaryExcess F) :=
      Finset.sum_add_distrib.symm
    _ = ∑ F : A.ArrangementFace,
          (A.arrangementFaceBoundary F).card := by
      apply Finset.sum_congr rfl
      intro F _hF
      exact Nat.add_sub_of_le (hface F)
    _ = 2 * Fintype.card A.GeometricEdge :=
      A.sum_arrangementFaceBoundary_card_eq_two_mul_card_geometricEdge hA

/-- The concrete face--edge inequality, with no abstract cellulation in its
statement.  Its only new input is exactly the outstanding three-edge fact. -/
theorem three_mul_card_arrangementFace_le_two_mul_card_geometricEdge
    (A : FiniteProjectiveLineArrangement Line) (hA : A.NonPencil)
    (hface : ∀ F : A.ArrangementFace,
      3 ≤ (A.arrangementFaceBoundary F).card) :
    3 * Fintype.card A.ArrangementFace ≤
      2 * Fintype.card A.GeometricEdge := by
  have hsum :=
    A.three_mul_card_arrangementFace_add_sum_boundaryExcess_eq hA hface
  omega

/-- Equality in the face--edge inequality is exactly simpliciality of every
actual face.  This is the numerical hand-off needed by the Gallery-A branch.
-/
theorem three_mul_card_arrangementFace_eq_two_mul_card_geometricEdge_iff
    (A : FiniteProjectiveLineArrangement Line) (hA : A.NonPencil)
    (hface : ∀ F : A.ArrangementFace,
      3 ≤ (A.arrangementFaceBoundary F).card) :
    3 * Fintype.card A.ArrangementFace =
        2 * Fintype.card A.GeometricEdge ↔
      ∀ F : A.ArrangementFace,
        (A.arrangementFaceBoundary F).card = 3 := by
  classical
  constructor
  · intro heq F
    have hsum :=
      A.three_mul_card_arrangementFace_add_sum_boundaryExcess_eq hA hface
    have hsumZero :
        (∑ G : A.ArrangementFace, A.arrangementFaceBoundaryExcess G) = 0 := by
      omega
    have hle :
        A.arrangementFaceBoundaryExcess F ≤
          ∑ G : A.ArrangementFace, A.arrangementFaceBoundaryExcess G :=
      Finset.single_le_sum
        (fun G _hG => Nat.zero_le (A.arrangementFaceBoundaryExcess G))
        (Finset.mem_univ F)
    rw [hsumZero] at hle
    have hzero : A.arrangementFaceBoundaryExcess F = 0 := by omega
    unfold arrangementFaceBoundaryExcess at hzero
    have hthree := hface F
    omega
  · intro hall
    calc
      3 * Fintype.card A.ArrangementFace =
          ∑ _F : A.ArrangementFace, 3 := by simp [mul_comm]
      _ = ∑ F : A.ArrangementFace,
          (A.arrangementFaceBoundary F).card := by
        apply Finset.sum_congr rfl
        intro F _hF
        exact (hall F).symm
      _ = 2 * Fintype.card A.GeometricEdge :=
        A.sum_arrangementFaceBoundary_card_eq_two_mul_card_geometricEdge hA

/-- The actual arrangement adapter.  No combinatorial proxy for a face or an
edge is introduced: once the two explicit global theorems are supplied, all
other fields come from the existing vertex, cyclic-edge, and closure-incidence
API.  This is the common cellulation object on which the Melchior, colouring,
and simplicial-gallery arguments can operate. -/
noncomputable def projectiveArrangementCellulationOfGlobalInput
    (A : FiniteProjectiveLineArrangement Line)
    (H : RealProjectiveArrangementGlobalInput.{u}) (hA : A.NonPencil) :
    ProjectiveArrangementCellulation
      {p // p ∈ A.vertexSet} A.GeometricEdge A.ArrangementFace := by
  classical
  exact
    { multiplicity := fun p => A.multiplicity p.1
      faceBoundary := A.arrangementFaceBoundary
      euler := H.euler A hA
      edgeCount := by
        calc
          Fintype.card A.GeometricEdge =
              ∑ p ∈ A.vertexSet, A.multiplicity p :=
            A.card_geometricEdge_eq_sum_multiplicity
          _ = ∑ p : {p // p ∈ A.vertexSet}, A.multiplicity p.1 := by
            conv_lhs => rw [← Finset.sum_attach]
            rw [Finset.attach_eq_univ]
      faceHasThreeEdges := H.faceHasThreeEdges A hA
      edgeHasTwoFaces := A.edgeHasTwoFaces_arrangementFaceBoundary hA }

end FiniteProjectiveLineArrangement

end Erdos506.Incidence
