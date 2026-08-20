import Erdos506.Incidence.CellulationParity

/-!
# The finite two-colour excess obstruction

For an even real-projective line arrangement, the product of the defining
linear forms two-colours the complement faces.  Every geometric edge then
has one incident face of each colour.  This file records the completely
finite consequence of that geometric colouring: Melchior slack cannot be
one.

The theorem below deliberately assumes only the two colour-wise handshakes.
Constructing those handshakes from actual arrangement sign patterns remains
the separate geometric adapter.
-/

namespace Erdos506.Incidence

open scoped BigOperators

namespace ProjectiveArrangementCellulation

variable {Vertex Edge Face : Type*}
  [Fintype Vertex] [Fintype Edge] [Fintype Face] [DecidableEq Edge]

/-- A colour class contributes three sides per face plus its nonnegative
boundary excess. -/
private theorem three_mul_card_add_sum_boundaryExcess_eq_of_handshake
    (C : ProjectiveArrangementCellulation Vertex Edge Face)
    (faces : Finset Face)
    (hhandshake :
      (∑ f ∈ faces, (C.faceBoundary f).card) = Fintype.card Edge) :
    3 * faces.card +
        (∑ f ∈ faces, ((C.faceBoundary f).card - 3)) =
      Fintype.card Edge := by
  calc
    3 * faces.card +
          (∑ f ∈ faces, ((C.faceBoundary f).card - 3)) =
        (∑ _f ∈ faces, 3) +
          ∑ f ∈ faces, ((C.faceBoundary f).card - 3) := by
            simp [mul_comm]
    _ = ∑ f ∈ faces,
          (3 + ((C.faceBoundary f).card - 3)) :=
      Finset.sum_add_distrib.symm
    _ = ∑ f ∈ faces, (C.faceBoundary f).card := by
      apply Finset.sum_congr rfl
      intro f _hf
      exact Nat.add_sub_of_le (C.faceHasThreeEdges f)
    _ = Fintype.card Edge := hhandshake

/-- If the faces admit a two-colouring for which each colour sees every edge
exactly once, the cellulation's Melchior slack is not one.

Indeed, writing `k₀,k₁` for the two sums of boundary excesses gives
`E = 3 F₀ + k₀ = 3 F₁ + k₁`.  Euler and the total face partition
identify the Melchior slack with `k₀+k₁`; this sum cannot be one because
`k₀` and `k₁` are congruent modulo three. -/
theorem melchiorSlack_ne_one_of_twoColorHandshake
    (C : ProjectiveArrangementCellulation Vertex Edge Face)
    (color : Face → Bool)
    (hhandshake : ∀ b : Bool,
      (∑ f ∈ (Finset.univ.filter fun f : Face => color f = b),
          (C.faceBoundary f).card) = Fintype.card Edge) :
    C.melchiorSlack ≠ 1 := by
  classical
  let F0 : Finset Face := Finset.univ.filter fun f => color f = false
  let F1 : Finset Face := Finset.univ.filter fun f => color f = true
  let k0 : ℕ := ∑ f ∈ F0, ((C.faceBoundary f).card - 3)
  let k1 : ℕ := ∑ f ∈ F1, ((C.faceBoundary f).card - 3)
  have hdisjoint : Disjoint F0 F1 := by
    rw [Finset.disjoint_left]
    intro f hf0 hf1
    have hfalse : color f = false := (Finset.mem_filter.mp hf0).2
    have htrue : color f = true := (Finset.mem_filter.mp hf1).2
    simp [hfalse] at htrue
  have hunion : F0 ∪ F1 = Finset.univ := by
    ext f
    simp only [F0, F1, Finset.mem_union, Finset.mem_filter,
      Finset.mem_univ, true_and]
    cases hcolor : color f <;> simp
  have hfaceCard :
      Fintype.card Face = F0.card + F1.card := by
    have hcard := Finset.card_union_of_disjoint hdisjoint
    rw [hunion, Finset.card_univ] at hcard
    omega
  have hzeroHandshake :
      (∑ f ∈ F0, (C.faceBoundary f).card) = Fintype.card Edge := by
    simpa [F0] using hhandshake false
  have honeHandshake :
      (∑ f ∈ F1, (C.faceBoundary f).card) = Fintype.card Edge := by
    simpa [F1] using hhandshake true
  have hk0 : 3 * F0.card + k0 = Fintype.card Edge := by
    exact C.three_mul_card_add_sum_boundaryExcess_eq_of_handshake
      F0 hzeroHandshake
  have hk1 : 3 * F1.card + k1 = Fintype.card Edge := by
    exact C.three_mul_card_add_sum_boundaryExcess_eq_of_handshake
      F1 honeHandshake
  intro hslack
  have hformula := C.melchiorSlack_eq
  have heuler := C.euler
  have hksum : k0 + k1 = 1 := by
    rw [hslack] at hformula
    omega
  omega

/-- Exactly one incident face of each colour at every edge implies the two
colour-wise handshakes used above. -/
theorem colorHandshake_of_oneFacePerEdge
    (C : ProjectiveArrangementCellulation Vertex Edge Face)
    (color : Face → Bool)
    (hone : ∀ (e : Edge) (b : Bool),
      (Finset.univ.filter fun f : Face =>
        color f = b ∧ e ∈ C.faceBoundary f).card = 1)
    (b : Bool) :
    (∑ f ∈ (Finset.univ.filter fun f : Face => color f = b),
        (C.faceBoundary f).card) = Fintype.card Edge := by
  classical
  let Fb : Finset Face := Finset.univ.filter fun f => color f = b
  calc
    (∑ f ∈ Fb, (C.faceBoundary f).card) =
        ∑ f ∈ Fb, ∑ e : Edge, if e ∈ C.faceBoundary f then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro f _hf
      simp
    _ = ∑ e : Edge, ∑ f ∈ Fb,
          if e ∈ C.faceBoundary f then 1 else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ _e : Edge, 1 := by
      apply Finset.sum_congr rfl
      intro e _he
      simpa [Fb, Finset.filter_filter, and_comm, and_left_comm,
        and_assoc] using hone e b
    _ = Fintype.card Edge := by simp

/-- Finite endpoint in the form most convenient for an actual arrangement:
every edge has one face of each colour. -/
theorem melchiorSlack_ne_one_of_oneFacePerColorAtEveryEdge
    (C : ProjectiveArrangementCellulation Vertex Edge Face)
    (color : Face → Bool)
    (hone : ∀ (e : Edge) (b : Bool),
      (Finset.univ.filter fun f : Face =>
        color f = b ∧ e ∈ C.faceBoundary f).card = 1) :
    C.melchiorSlack ≠ 1 := by
  apply C.melchiorSlack_ne_one_of_twoColorHandshake color
  intro b
  exact C.colorHandshake_of_oneFacePerEdge color hone b

end ProjectiveArrangementCellulation

end Erdos506.Incidence
