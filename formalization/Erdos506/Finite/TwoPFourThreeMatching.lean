import Erdos506.Finite.KFiveNearOneFactorizationOrbit

/-!
# Three-edge matchings in two copies of `P4`

The golden two-pentagon link has nine labelled vertices.  Four of them are
the chord centres `q₁, ..., q₄`; the other five are the pentagon vertices
`b₀, ..., b₄`.  Its six ordinary edges are

`q₁b₁, q₂b₂, q₃b₃, q₄b₄, b₁b₃, b₂b₄`.

Thus the ordinary graph is the disjoint union of the paths

`q₁ - b₁ - b₃ - q₃` and `q₂ - b₂ - b₄ - q₄`.

Every three-edge matching consists of the two end edges of one path and one
edge of the other.  The canonical near-one-factorization cycle interchanges
the paths and its square reverses both.  Consequently there are just two
normal forms: the remaining edge is an end edge or it is the middle edge.

All finite assertions in this file are checked by Lean's kernel evaluator.
-/

namespace Erdos506.Finite

/-- The four `q`-vertices and five `b`-vertices of the golden ordinary graph. -/
abbrev GoldenOrdinaryVertex := Fin 4 ⊕ Fin 5

/-- An edge of the complete graph on the nine golden ordinary vertices. -/
abbrev GoldenOrdinaryEdge :=
  ↥((Finset.univ : Finset GoldenOrdinaryVertex).powersetCard 2)

/-- The vertex `q_(i+1)`.  Thus Lean index zero denotes manuscript index one. -/
def goldenQ (i : Fin 4) : GoldenOrdinaryVertex :=
  Sum.inl i

/-- The vertex `b_i`. -/
def goldenB (i : Fin 5) : GoldenOrdinaryVertex :=
  Sum.inr i

/-- Package two distinct golden vertices as an edge. -/
def goldenOrdinaryEdgeOfNe (x y : GoldenOrdinaryVertex) (hxy : x ≠ y) :
    GoldenOrdinaryEdge :=
  ⟨{x, y}, by
    rw [Finset.mem_powersetCard]
    exact ⟨Finset.subset_univ _, by simp [hxy]⟩⟩

/-- The edge `q_(i+1)b_(i+1)`. -/
def goldenQEdge (i : Fin 4) : GoldenOrdinaryEdge :=
  goldenOrdinaryEdgeOfNe (goldenQ i) (goldenB i.succ) (by simp [goldenQ, goldenB])

/-- The middle edge `b₁b₃` of the odd path. -/
def goldenBEdge13 : GoldenOrdinaryEdge :=
  goldenOrdinaryEdgeOfNe (goldenB 1) (goldenB 3) (by decide)

/-- The middle edge `b₂b₄` of the even path. -/
def goldenBEdge24 : GoldenOrdinaryEdge :=
  goldenOrdinaryEdgeOfNe (goldenB 2) (goldenB 4) (by decide)

/-- The six ordinary edges, displayed as two disjoint copies of `P4`. -/
def goldenOrdinaryEdges : Finset GoldenOrdinaryEdge :=
  { goldenQEdge 0, goldenQEdge 1, goldenQEdge 2, goldenQEdge 3,
    goldenBEdge13, goldenBEdge24 }

/-! ## The simultaneous cyclic relabelling -/

/-- The cycle on `q₁, ..., q₄`, in zero-based `Fin 4` coordinates. -/
def goldenCycleFour : Equiv.Perm (Fin 4) where
  toFun := (![1, 2, 3, 0] : Fin 4 → Fin 4)
  invFun := (![3, 0, 1, 2] : Fin 4 → Fin 4)
  left_inv := by decide +kernel
  right_inv := by decide +kernel

/--
Simultaneously cycle the four `q`-vertices and the five pentagon vertices.
The right summand deliberately reuses the canonical-factorization
stabilizer `(1 2 3 4)` from `KFiveNearOneFactorizationOrbit`.
-/
def goldenCycleVertex : Equiv.Perm GoldenOrdinaryVertex :=
  Equiv.Perm.sumCongr goldenCycleFour kFiveStabilizerCycle

/-- Relabel a golden edge by a permutation of its vertices. -/
def goldenPermuteEdgeEquiv (σ : Equiv.Perm GoldenOrdinaryVertex) :
    GoldenOrdinaryEdge ≃ GoldenOrdinaryEdge where
  toFun e :=
    ⟨e.1.map σ.toEmbedding, by
      rw [Finset.mem_powersetCard]
      refine ⟨Finset.subset_univ _, ?_⟩
      rw [Finset.card_map]
      exact (Finset.mem_powersetCard.mp e.2).2⟩
  invFun e :=
    ⟨e.1.map σ.symm.toEmbedding, by
      rw [Finset.mem_powersetCard]
      refine ⟨Finset.subset_univ _, ?_⟩
      rw [Finset.card_map]
      exact (Finset.mem_powersetCard.mp e.2).2⟩
  left_inv e := by
    apply Subtype.ext
    ext x
    simp
  right_inv e := by
    apply Subtype.ext
    ext x
    simp

/-- Relabel every edge of a matching. -/
def goldenPermuteMatching (σ : Equiv.Perm GoldenOrdinaryVertex)
    (M : Finset GoldenOrdinaryEdge) : Finset GoldenOrdinaryEdge :=
  M.map (goldenPermuteEdgeEquiv σ).toEmbedding

/-- The `q`- and `b`-cycles have the same orientation. -/
theorem goldenCycleFour_succ_compatible :
    ∀ i : Fin 4,
      (goldenCycleFour i).succ = kFiveStabilizerCycle i.succ := by
  decide +kernel

/-- Every relevant power of the pentagon cycle fixes the distinguished zero. -/
theorem kFiveStabilizerCycle_pow_fixes_zero :
    ∀ k : Fin 4, (kFiveStabilizerCycle ^ k.val) 0 = 0 := by
  decide +kernel

/-- Every relevant power remains in the stabilizer of the canonical table. -/
theorem kFiveStabilizerCycle_pow_preserves_canonical :
    ∀ k : Fin 4,
      KFivePreservesCanonical (kFiveStabilizerCycle ^ k.val) := by
  unfold KFivePreservesCanonical
  decide +kernel

/-- On the nine-vertex graph, every relevant power fixes `b₀`. -/
theorem goldenCycleVertex_pow_fixes_bZero :
    ∀ k : Fin 4,
      (goldenCycleVertex ^ k.val) (goldenB 0) = goldenB 0 := by
  decide +kernel

/-- The simultaneous cycle is an automorphism of the six-edge ordinary graph. -/
theorem goldenCycleVertex_preserves_ordinaryEdges :
    goldenPermuteMatching goldenCycleVertex goldenOrdinaryEdges =
      goldenOrdinaryEdges := by
  decide +kernel

/-! ## The two three-matching normal forms -/

/--
The end form: both end edges of the odd path and an end edge of the even
path, namely `q₁b₁, q₃b₃, q₂b₂`.
-/
def goldenCanonicalEndMatching : Finset GoldenOrdinaryEdge :=
  {goldenQEdge 0, goldenQEdge 2, goldenQEdge 1}

/--
The middle form: both end edges of the odd path and the middle edge of the
even path, namely `q₁b₁, q₃b₃, b₂b₄`.
-/
def goldenCanonicalMiddleMatching : Finset GoldenOrdinaryEdge :=
  {goldenQEdge 0, goldenQEdge 2, goldenBEdge24}

/-- Pairwise vertex-disjointness for a finite family of golden edges. -/
def GoldenOrdinaryIsMatching (M : Finset GoldenOrdinaryEdge) : Prop :=
  ∀ e ∈ M, ∀ f ∈ M, e ≠ f → Disjoint e.1 f.1

private instance (M : Finset GoldenOrdinaryEdge) :
    Decidable (GoldenOrdinaryIsMatching M) := by
  unfold GoldenOrdinaryIsMatching
  infer_instance

/-- Both displayed normal forms are three-edge matchings in the graph. -/
theorem goldenCanonicalMatchings_valid :
    goldenCanonicalEndMatching ∈ goldenOrdinaryEdges.powersetCard 3 ∧
      GoldenOrdinaryIsMatching goldenCanonicalEndMatching ∧
    goldenCanonicalMiddleMatching ∈ goldenOrdinaryEdges.powersetCard 3 ∧
      GoldenOrdinaryIsMatching goldenCanonicalMiddleMatching := by
  decide +kernel

/--
Closed finite certificate for normalizing a three-edge matching.  Quantifying
over the subtype of the twenty three-subsets keeps the certificate small and
makes its exhaustive boundary explicit.
-/
private theorem goldenThreeMatching_end_or_middle_certificate :
    ∀ M : ↥(goldenOrdinaryEdges.powersetCard 3),
      GoldenOrdinaryIsMatching M.1 →
        ∃ k : Fin 4,
          goldenPermuteMatching (goldenCycleVertex ^ k.val) M.1 =
              goldenCanonicalEndMatching ∨
            goldenPermuteMatching (goldenCycleVertex ^ k.val) M.1 =
              goldenCanonicalMiddleMatching := by
  decide +kernel

/--
Every pairwise-disjoint three-edge subset of the two `P4`s can be carried by
a canonical-factorization cycle power to the end form or the middle form.
-/
theorem goldenThreeMatching_end_or_middle
    (M : Finset GoldenOrdinaryEdge)
    (hM : M ∈ goldenOrdinaryEdges.powersetCard 3)
    (hmatching : GoldenOrdinaryIsMatching M) :
    ∃ k : Fin 4,
      goldenPermuteMatching (goldenCycleVertex ^ k.val) M =
          goldenCanonicalEndMatching ∨
        goldenPermuteMatching (goldenCycleVertex ^ k.val) M =
          goldenCanonicalMiddleMatching := by
  exact goldenThreeMatching_end_or_middle_certificate ⟨M, hM⟩ hmatching

/-- The equivalent orbit-oriented form, convenient when constructing cases. -/
theorem goldenThreeMatching_in_end_or_middle_orbit
    (M : Finset GoldenOrdinaryEdge)
    (hM : M ∈ goldenOrdinaryEdges.powersetCard 3)
    (hmatching : GoldenOrdinaryIsMatching M) :
    ∃ k : Fin 4,
      M = goldenPermuteMatching (goldenCycleVertex ^ k.val)
          goldenCanonicalEndMatching ∨
        M = goldenPermuteMatching (goldenCycleVertex ^ k.val)
          goldenCanonicalMiddleMatching := by
  -- This is another closed orientation of the same four-element orbit.
  have hcertificate :
      ∀ N : ↥(goldenOrdinaryEdges.powersetCard 3),
        GoldenOrdinaryIsMatching N.1 →
          ∃ k : Fin 4,
            N.1 = goldenPermuteMatching (goldenCycleVertex ^ k.val)
                goldenCanonicalEndMatching ∨
              N.1 = goldenPermuteMatching (goldenCycleVertex ^ k.val)
                goldenCanonicalMiddleMatching := by
    decide +kernel
  exact hcertificate ⟨M, hM⟩ hmatching

end Erdos506.Finite
