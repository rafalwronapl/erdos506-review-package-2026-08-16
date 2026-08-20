import Erdos506.Finite.FourStarLink
import Mathlib.Data.Fintype.Powerset

/-!
# Canonical labels for the three four-star motifs

The private vertices of a four-star have no preferred names.  This file
isolates the finite relabelling needed before applying the determinant
identities.  A permutation acts on every private trace, and the three
possible motifs are put into the precise index conventions used by
`FourStarRigidity`:

* `T012,S03,S13,S23` for a `T`-star;
* `S01,S12,S23,S03` for a four-cycle;
* `S01,S02,S12,S03` for a triangle with a pendant edge.

The `T`-star predicate records exactly the facts supplied by the actual
four size-three lines: four traces of size two or three, pairwise
intersection at most one, and one trace of size three.  In particular, it
does not assume the desired canonical catalogue.
-/

namespace Erdos506.Finite

/-- Relabel one private trace by a permutation of the four private
vertices. -/
def fourStarRelabelTrace (σ : Equiv.Perm FourStarVertex)
    (T : Finset FourStarVertex) : Finset FourStarVertex :=
  T.map σ.toEmbedding

/-- Relabelling is an equivalence on private traces. -/
def fourStarRelabelTraceEquiv (σ : Equiv.Perm FourStarVertex) :
    Finset FourStarVertex ≃ Finset FourStarVertex :=
  σ.finsetCongr

/-- Relabel every private trace in a family. -/
def fourStarRelabelTraceFamily (σ : Equiv.Perm FourStarVertex)
    (E : Finset (Finset FourStarVertex)) :
    Finset (Finset FourStarVertex) :=
  E.map (fourStarRelabelTraceEquiv σ).toEmbedding

@[simp] theorem fourStarRelabelTraceEquiv_apply
    (σ : Equiv.Perm FourStarVertex) (T : Finset FourStarVertex) :
    fourStarRelabelTraceEquiv σ T = fourStarRelabelTrace σ T := rfl

@[simp] theorem mem_fourStarRelabelTraceFamily
    (σ : Equiv.Perm FourStarVertex)
    (E : Finset (Finset FourStarVertex)) (T : Finset FourStarVertex) :
    T ∈ fourStarRelabelTraceFamily σ E ↔
      fourStarRelabelTrace σ.symm T ∈ E := by
  simp [fourStarRelabelTraceFamily, fourStarRelabelTraceEquiv,
    fourStarRelabelTrace]

/-- The canonical `T012,S03,S13,S23` trace family. -/
def fourStarCanonicalTStar : Finset (Finset FourStarVertex) :=
  {{0, 1, 2}, {0, 3}, {1, 3}, {2, 3}}

/-- The canonical cycle `S01,S12,S23,S03`. -/
def fourStarCanonicalFourCycle : Finset (Finset FourStarVertex) :=
  {{0, 1}, {1, 2}, {2, 3}, {0, 3}}

/-- The canonical triangle-pendant `S01,S02,S12,S03`. -/
def fourStarCanonicalTrianglePendant : Finset (Finset FourStarVertex) :=
  {{0, 1}, {0, 2}, {1, 2}, {0, 3}}

/-- The label-free finite content of an actual `T`-star trace family.

The intersection condition is inherited from uniqueness of a geometric
line through two selected points.  It forces the three remaining traces to
join the vertex outside the three-trace to its three vertices. -/
def IsFourStarTStarTraceFamily
    (E : Finset (Finset FourStarVertex)) : Prop :=
  E.card = 4 ∧
    (∀ T ∈ E, T.card = 2 ∨ T.card = 3) ∧
    (∀ T ∈ E, ∀ U ∈ E, T ≠ U → (T ∩ U).card ≤ 1) ∧
    ∃ T ∈ E, T.card = 3

private instance (E : Finset (Finset FourStarVertex)) :
    Decidable (IsFourStarTStarTraceFamily E) := by
  unfold IsFourStarTStarTraceFamily
  infer_instance

private instance (E : Finset (Finset FourStarVertex)) :
    Decidable (IsFourStarPrivatePairFamily E) := by
  unfold IsFourStarPrivatePairFamily
  infer_instance

private instance (E : Finset (Finset FourStarVertex)) :
    Decidable (IsFourStarFourCycle E) := by
  unfold IsFourStarFourCycle
  infer_instance

private instance (E : Finset (Finset FourStarVertex)) :
    Decidable (IsFourStarTrianglePendant E) := by
  unfold IsFourStarTrianglePendant
  infer_instance

/-- All two- and three-element private traces which can occur in the
four-star link.  Restricting the closed certificate to this ten-element set
avoids enumerating irrelevant arbitrary subsets of `Fin 4`. -/
def fourStarTStarTraceCandidates : Finset (Finset FourStarVertex) :=
  (Finset.univ : Finset FourStarVertex).powersetCard 2 ∪
    (Finset.univ : Finset FourStarVertex).powersetCard 3

private def FourStarTStarRelabelPredicate
    (E : Finset (Finset FourStarVertex)) : Prop :=
  IsFourStarTStarTraceFamily E →
    ∃ σ : Equiv.Perm FourStarVertex,
      fourStarRelabelTraceFamily σ E = fourStarCanonicalTStar

private instance (E : Finset (Finset FourStarVertex)) :
    Decidable (FourStarTStarRelabelPredicate E) :=
  inferInstanceAs (Decidable (
    IsFourStarTStarTraceFamily E →
      ∃ σ : Equiv.Perm FourStarVertex,
        fourStarRelabelTraceFamily σ E = fourStarCanonicalTStar))

private def FourStarPairMotifRelabelPredicate
    (E : Finset (Finset FourStarVertex)) : Prop :=
  (IsFourStarPrivatePairFamily E → IsFourStarFourCycle E →
    ∃ σ : Equiv.Perm FourStarVertex,
      fourStarRelabelTraceFamily σ E = fourStarCanonicalFourCycle) ∧
  (IsFourStarPrivatePairFamily E → IsFourStarTrianglePendant E →
    ∃ σ : Equiv.Perm FourStarVertex,
      fourStarRelabelTraceFamily σ E =
        fourStarCanonicalTrianglePendant)

private instance (E : Finset (Finset FourStarVertex)) :
    Decidable (FourStarPairMotifRelabelPredicate E) :=
  inferInstanceAs (Decidable (
    (IsFourStarPrivatePairFamily E → IsFourStarFourCycle E →
      ∃ σ : Equiv.Perm FourStarVertex,
        fourStarRelabelTraceFamily σ E = fourStarCanonicalFourCycle) ∧
    (IsFourStarPrivatePairFamily E → IsFourStarTrianglePendant E →
      ∃ σ : Equiv.Perm FourStarVertex,
        fourStarRelabelTraceFamily σ E =
          fourStarCanonicalTrianglePendant)))

private theorem fourStar_tStar_relabel_certificate :
    ∀ E : ↥fourStarTStarTraceCandidates.powerset,
      FourStarTStarRelabelPredicate E.1 := by
  decide +kernel

private theorem fourStar_pair_motif_relabel_certificate :
    ∀ E : ↥fourStarEdges.powerset,
      FourStarPairMotifRelabelPredicate E.1 := by
  decide +kernel

/-- Every actual `T`-star admits the canonical labelling
`T012,S03,S13,S23`. -/
theorem exists_fourStarRelabelTraceFamily_eq_canonicalTStar
    (E : Finset (Finset FourStarVertex))
    (hE : IsFourStarTStarTraceFamily E) :
    ∃ σ : Equiv.Perm FourStarVertex,
      fourStarRelabelTraceFamily σ E = fourStarCanonicalTStar := by
  have hsubset : E ⊆ fourStarTStarTraceCandidates := by
    intro T hT
    rcases hE.2.1 T hT with htwo | hthree
    · apply Finset.mem_union_left
      exact Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, htwo⟩
    · apply Finset.mem_union_right
      exact Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hthree⟩
  let E' : ↥fourStarTStarTraceCandidates.powerset :=
    ⟨E, Finset.mem_powerset.mpr hsubset⟩
  exact fourStar_tStar_relabel_certificate E' hE

/-- Every four-cycle private-pair family admits the canonical labelling
`S01,S12,S23,S03`. -/
theorem exists_fourStarRelabelTraceFamily_eq_canonicalFourCycle
    (E : Finset (Finset FourStarVertex))
    (hfamily : IsFourStarPrivatePairFamily E)
    (hcycle : IsFourStarFourCycle E) :
    ∃ σ : Equiv.Perm FourStarVertex,
      fourStarRelabelTraceFamily σ E = fourStarCanonicalFourCycle := by
  let E' : ↥fourStarEdges.powerset :=
    ⟨E, Finset.mem_powerset.mpr hfamily.2⟩
  exact (fourStar_pair_motif_relabel_certificate E').1 hfamily hcycle

/-- Every triangle-pendant private-pair family admits the canonical
labelling `S01,S02,S12,S03`. -/
theorem exists_fourStarRelabelTraceFamily_eq_canonicalTrianglePendant
    (E : Finset (Finset FourStarVertex))
    (hfamily : IsFourStarPrivatePairFamily E)
    (hpendant : IsFourStarTrianglePendant E) :
    ∃ σ : Equiv.Perm FourStarVertex,
      fourStarRelabelTraceFamily σ E =
        fourStarCanonicalTrianglePendant := by
  let E' : ↥fourStarEdges.powerset :=
    ⟨E, Finset.mem_powerset.mpr hfamily.2⟩
  exact (fourStar_pair_motif_relabel_certificate E').2 hfamily hpendant

end Erdos506.Finite
