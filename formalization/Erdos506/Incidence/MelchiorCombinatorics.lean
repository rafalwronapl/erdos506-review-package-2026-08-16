import Mathlib

/-!
# The finite counting core of Melchior's inequality

This file separates the entirely finite part of Melchior's argument from the
geometric/topological construction of the projective line arrangement.

For a projective cellulation coming from a non-pencil arrangement, the input
records exactly the three facts used by the classical proof:

* Euler's relation `V + F = E + 1` for the real projective plane;
* the number of edges is the sum of the line multiplicities at the vertices;
* every face has at least three boundary edges and every edge borders exactly
  two faces.

The theorem `ProjectiveArrangementCellulation.melchior` derives the full
Melchior row from those data.  In particular, no geometric assumption is
silently bundled into the arithmetic proof; the future arrangement module has
to construct this structure and prove every field.
-/

namespace Erdos506.Incidence

open scoped BigOperators

/-- Finite data exposed by the projective cellulation of a line arrangement.

`multiplicity v` is the number of arrangement lines through `v`, while
`faceBoundary f` is the set of arrangement edges on the boundary of `f`.
The structure deliberately stores only claims that the geometric adapter must
prove, rather than postulating Melchior's inequality itself. -/
structure ProjectiveArrangementCellulation
    (Vertex Edge Face : Type*)
    [Fintype Vertex] [Fintype Edge] [Fintype Face] [DecidableEq Edge] where
  multiplicity : Vertex → ℕ
  faceBoundary : Face → Finset Edge
  euler : Fintype.card Vertex + Fintype.card Face = Fintype.card Edge + 1
  edgeCount : Fintype.card Edge = ∑ v : Vertex, multiplicity v
  faceHasThreeEdges : ∀ f : Face, 3 ≤ (faceBoundary f).card
  edgeHasTwoFaces :
    ∀ e : Edge, (Finset.univ.filter fun f : Face => e ∈ faceBoundary f).card = 2

namespace ProjectiveArrangementCellulation

variable {Vertex Edge Face : Type*}
  [Fintype Vertex] [Fintype Edge] [Fintype Face] [DecidableEq Edge]

/-- Double-count incidences between faces and boundary edges. -/
theorem sum_faceBoundary_card
    (C : ProjectiveArrangementCellulation Vertex Edge Face) :
    (∑ f : Face, (C.faceBoundary f).card) = 2 * Fintype.card Edge := by
  calc
    (∑ f : Face, (C.faceBoundary f).card) =
        ∑ f : Face, ∑ e : Edge, if e ∈ C.faceBoundary f then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro f hf
      simp
    _ = ∑ e : Edge, ∑ f : Face,
          if e ∈ C.faceBoundary f then 1 else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ _e : Edge, 2 := by
      apply Finset.sum_congr rfl
      intro e he
      simpa using C.edgeHasTwoFaces e
    _ = 2 * Fintype.card Edge := by simp [mul_comm]

/-- The face-edge handshake inequality `3F ≤ 2E`. -/
theorem face_edge_handshake
    (C : ProjectiveArrangementCellulation Vertex Edge Face) :
    3 * Fintype.card Face ≤ 2 * Fintype.card Edge := by
  calc
    3 * Fintype.card Face = ∑ _f : Face, 3 := by simp [mul_comm]
    _ ≤ ∑ f : Face, (C.faceBoundary f).card := by
      exact Finset.sum_le_sum fun f _ => C.faceHasThreeEdges f
    _ = 2 * Fintype.card Edge := C.sum_faceBoundary_card

/-- Melchior's inequality in the coefficient form used after inversion:
`3 ≤ ∑ᵥ (3 - multiplicity v)`.

The sum is integer-valued because vertices of multiplicity at least four make
negative contributions. -/
theorem melchior
    (C : ProjectiveArrangementCellulation Vertex Edge Face) :
    (3 : ℤ) ≤ ∑ v : Vertex, (3 - (C.multiplicity v : ℤ)) := by
  have hface :
      (3 : ℤ) * Fintype.card Face ≤ 2 * Fintype.card Edge := by
    exact_mod_cast C.face_edge_handshake
  have heuler :
      (Fintype.card Vertex : ℤ) + Fintype.card Face =
        Fintype.card Edge + 1 := by
    exact_mod_cast C.euler
  have hedge :
      (Fintype.card Edge : ℤ) =
        ∑ v : Vertex, (C.multiplicity v : ℤ) := by
    exact_mod_cast C.edgeCount
  have hsum :
      (∑ v : Vertex, (3 - (C.multiplicity v : ℤ))) =
        3 * (Fintype.card Vertex : ℤ) - Fintype.card Edge := by
    rw [Finset.sum_sub_distrib]
    simp [← hedge, mul_comm]
  rw [hsum]
  omega

end ProjectiveArrangementCellulation

end Erdos506.Incidence
