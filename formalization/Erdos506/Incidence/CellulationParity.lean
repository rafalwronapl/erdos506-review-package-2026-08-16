import Erdos506.Incidence.MelchiorCombinatorics

/-!
# Parity boundary for projective arrangement cellulations

The face-colouring part of the even-arrangement argument is not yet in
mathlib.  This file isolates the completely finite consequence needed from
that topology.  In particular, it does not introduce a replacement axiom for
the missing colouring theorem.

For a projective cellulation, Melchior slack one and an even number of edges
force an odd number of faces.  Thus a future geometric adapter need only prove
the corresponding face-parity statement in order to exclude slack one.
-/

namespace Erdos506.Incidence

open scoped BigOperators

namespace ProjectiveArrangementCellulation

variable {Vertex Edge Face : Type*}
  [Fintype Vertex] [Fintype Edge] [Fintype Face] [DecidableEq Edge]

/-- The Melchior slack associated to the finite data of a projective
cellulation. -/
noncomputable def melchiorSlack
    (C : ProjectiveArrangementCellulation Vertex Edge Face) : ℤ :=
  (∑ v : Vertex, (3 - (C.multiplicity v : ℤ))) - 3

/-- Euler and the edge--vertex incidence count give an exact expression for
the cellulation's Melchior slack. -/
theorem melchiorSlack_eq
    (C : ProjectiveArrangementCellulation Vertex Edge Face) :
    C.melchiorSlack =
      3 * (Fintype.card Vertex : ℤ) - Fintype.card Edge - 3 := by
  have hedge :
      (Fintype.card Edge : ℤ) =
        ∑ v : Vertex, (C.multiplicity v : ℤ) := by
    exact_mod_cast C.edgeCount
  unfold melchiorSlack
  rw [Finset.sum_sub_distrib]
  simp [← hedge, mul_comm]

/-- A slack-one cellulation with an even edge set has an odd number of
faces.  This is the finite parity obstruction supplied to the later
face-colouring construction. -/
theorem odd_face_card_of_melchiorSlack_eq_one_of_edge_even
    (C : ProjectiveArrangementCellulation Vertex Edge Face)
    (hedge : Even (Fintype.card Edge))
    (hslack : C.melchiorSlack = 1) :
    Odd (Fintype.card Face) := by
  apply Nat.not_even_iff_odd.mp
  intro hface
  obtain ⟨e, he⟩ := hedge
  obtain ⟨f, hf⟩ := hface
  have hformula := C.melchiorSlack_eq
  have heuler := C.euler
  omega

/-- Consequently, the missing topological assertion that the relevant
cellulation has an even number of faces rules out Melchior slack one. -/
theorem melchiorSlack_ne_one_of_edge_even_of_face_even
    (C : ProjectiveArrangementCellulation Vertex Edge Face)
    (hedge : Even (Fintype.card Edge))
    (hface : Even (Fintype.card Face)) :
    C.melchiorSlack ≠ 1 := by
  intro hslack
  have hodd := C.odd_face_card_of_melchiorSlack_eq_one_of_edge_even hedge hslack
  obtain ⟨e, he⟩ := hface
  obtain ⟨o, ho⟩ := hodd
  omega

end ProjectiveArrangementCellulation

end Erdos506.Incidence
