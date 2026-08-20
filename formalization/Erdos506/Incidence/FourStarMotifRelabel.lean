import Erdos506.Finite.FourStarMotifRelabel
import Erdos506.Incidence.FourStarRigidity

/-!
# Determinant endpoints for canonically relabelled four-star motifs

`FourStarMotifRelabel` supplies the finite permutation.  This file is the
small incidence adapter: determinant vanishings attached to the actual
unlabelled traces become the exact canonical equations consumed by
`FourStarRigidity` and `FourStarNormalForm`.

The projective skeleton is relabelled along the finite permutation.  Thus
the canonical determinant package is stated on an honest
`FourStarProjectiveSkeleton`, and `FourStarNormalForm` can be applied to it
without any mismatch between the finite and projective index orders.
-/

namespace Erdos506.Incidence

open Erdos506.Finite

/-- Nonvanishing of a three-row determinant is independent of the ordering
of those rows.  Packaging the six cases once keeps the finite `Fin 4`
dispatch below small and avoids repeatedly normalizing symbolic determinants. -/
private theorem det_three_all_orders_ne
    (u v w : Homogeneous3) (h : Matrix.det ![u, v, w] ≠ 0) :
    Matrix.det ![u, w, v] ≠ 0 ∧
    Matrix.det ![v, u, w] ≠ 0 ∧
    Matrix.det ![v, w, u] ≠ 0 ∧
    Matrix.det ![w, u, v] ≠ 0 ∧
    Matrix.det ![w, v, u] ≠ 0 := by
  constructor
  · intro hz
    apply h
    calc
      Matrix.det ![u, v, w] = -Matrix.det ![u, w, v] := by
        simp [Matrix.det_fin_three]
        ring
      _ = 0 := by rw [hz]; simp
  constructor
  · intro hz
    apply h
    calc
      Matrix.det ![u, v, w] = -Matrix.det ![v, u, w] := by
        simp [Matrix.det_fin_three]
        ring
      _ = 0 := by rw [hz]; simp
  constructor
  · intro hz
    apply h
    calc
      Matrix.det ![u, v, w] = Matrix.det ![v, w, u] := by
        simp [Matrix.det_fin_three]
        ring
      _ = 0 := hz
  constructor
  · intro hz
    apply h
    calc
      Matrix.det ![u, v, w] = Matrix.det ![w, u, v] := by
        simp [Matrix.det_fin_three]
        ring
      _ = 0 := hz
  · intro hz
    apply h
    calc
      Matrix.det ![u, v, w] = -Matrix.det ![w, v, u] := by
        simp [Matrix.det_fin_three]
        ring
      _ = 0 := by rw [hz]; simp

set_option maxHeartbeats 1000000 in
private theorem FourStarProjectiveSkeleton.base_det_ne_zero
    (F : FourStarProjectiveSkeleton) (i j k : FourStarVertex)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    Matrix.det ![F.baseLine i, F.baseLine j, F.baseLine k] ≠ 0 := by
  have h012 := F.base_general_position.det_abc_ne
  have h013 := F.base_general_position.det_abd_ne
  have h023 := F.base_general_position.det_acd_ne
  have h123 := F.base_general_position.det_bcd_ne
  obtain ⟨h021, h102, h120, h201, h210⟩ :=
    det_three_all_orders_ne _ _ _ h012
  obtain ⟨h031, h103, h130, h301, h310⟩ :=
    det_three_all_orders_ne _ _ _ h013
  obtain ⟨h032, h203, h230, h302, h320⟩ :=
    det_three_all_orders_ne _ _ _ h023
  obtain ⟨h132, h213, h231, h312, h321⟩ :=
    det_three_all_orders_ne _ _ _ h123
  fin_cases i <;> fin_cases j <;> fin_cases k
  all_goals try { exact (hij rfl).elim }
  all_goals try { exact (hik rfl).elim }
  all_goals try { exact (hjk rfl).elim }
  all_goals
    first
    | simpa using h012
    | simpa using h021
    | simpa using h102
    | simpa using h120
    | simpa using h201
    | simpa using h210
    | simpa using h013
    | simpa using h031
    | simpa using h103
    | simpa using h130
    | simpa using h301
    | simpa using h310
    | simpa using h023
    | simpa using h032
    | simpa using h203
    | simpa using h230
    | simpa using h302
    | simpa using h320
    | simpa using h123
    | simpa using h132
    | simpa using h213
    | simpa using h231
    | simpa using h312
    | simpa using h321

/-- Relabel the four base covectors and their four private points along a
permutation.  Complete-quadrangle general position and private incidence
are invariant under this operation. -/
def FourStarProjectiveSkeleton.relabel
    (F : FourStarProjectiveSkeleton)
    (σ : Equiv.Perm FourStarVertex) : FourStarProjectiveSkeleton where
  baseLine i := F.baseLine (σ.symm i)
  privatePoint i := F.privatePoint (σ.symm i)
  base_general_position := by
    constructor
    · exact F.base_det_ne_zero _ _ _
        (σ.symm.injective.ne (by decide))
        (σ.symm.injective.ne (by decide))
        (σ.symm.injective.ne (by decide))
    · exact F.base_det_ne_zero _ _ _
        (σ.symm.injective.ne (by decide))
        (σ.symm.injective.ne (by decide))
        (σ.symm.injective.ne (by decide))
    · exact F.base_det_ne_zero _ _ _
        (σ.symm.injective.ne (by decide))
        (σ.symm.injective.ne (by decide))
        (σ.symm.injective.ne (by decide))
    · exact F.base_det_ne_zero _ _ _
        (σ.symm.injective.ne (by decide))
        (σ.symm.injective.ne (by decide))
        (σ.symm.injective.ne (by decide))
  private_ne_zero i := F.private_ne_zero (σ.symm i)
  private_on_base i := F.private_on_base (σ.symm i)
  private_off_base i j hij :=
    F.private_off_base (σ.symm i) (σ.symm j) (σ.symm.injective.ne hij)

@[simp] theorem FourStarProjectiveSkeleton.relabel_baseLine
    (F : FourStarProjectiveSkeleton)
    (σ : Equiv.Perm FourStarVertex) (i : FourStarVertex) :
    (F.relabel σ).baseLine i = F.baseLine (σ.symm i) := rfl

@[simp] theorem FourStarProjectiveSkeleton.relabel_privatePoint
    (F : FourStarProjectiveSkeleton)
    (σ : Equiv.Perm FourStarVertex) (i : FourStarVertex) :
    (F.relabel σ).privatePoint i = F.privatePoint (σ.symm i) := rfl

@[simp] theorem fourStarTDet_relabel
    (F : FourStarProjectiveSkeleton)
    (σ : Equiv.Perm FourStarVertex) (i j k : FourStarVertex) :
    fourStarTDet (F.relabel σ) i j k =
      fourStarTDet F (σ.symm i) (σ.symm j) (σ.symm k) := rfl

@[simp] theorem fourStarSDet_relabel
    (F : FourStarProjectiveSkeleton)
    (σ : Equiv.Perm FourStarVertex) (i j k l : FourStarVertex) :
    fourStarSDet (F.relabel σ) i j k l =
      fourStarSDet F (σ.symm i) (σ.symm j) (σ.symm k) (σ.symm l) := rfl

/-- Determinant vanishings carried by an actual family of private traces.
For a pair `{i,j}`, the indices `k,l` enumerate its complementary base
lines.  Quantifying over both enumerations makes the interface independent
of all ordering choices. -/
structure FourStarTraceDeterminantData (F : FourStarProjectiveSkeleton)
    (E : Finset (Finset FourStarVertex)) : Prop where
  t_zero : ∀ i j k : FourStarVertex,
    ({i, j, k} : Finset FourStarVertex).card = 3 →
      {i, j, k} ∈ E → fourStarTDet F i j k = 0
  s_zero : ∀ i j k l : FourStarVertex,
    ({i, j} : Finset FourStarVertex).card = 2 →
      {i, j} ∈ E →
        ({k, l} : Finset FourStarVertex) =
          (Finset.univ : Finset FourStarVertex) \ {i, j} →
            fourStarSDet F i j k l = 0

/-- Canonical determinant package `T012,S03,S13,S23`. -/
structure FourStarCanonicalTStarDeterminants
    (F : FourStarProjectiveSkeleton) : Prop where
  t012 : fourStarTDet F 0 1 2 = 0
  s03 : fourStarSDet F 0 3 1 2 = 0
  s13 : fourStarSDet F 1 3 0 2 = 0
  s23 : fourStarSDet F 2 3 0 1 = 0

/-- Canonical determinant package `S01,S12,S23,S03`. -/
structure FourStarCanonicalFourCycleDeterminants
    (F : FourStarProjectiveSkeleton) : Prop where
  s01 : fourStarSDet F 0 1 2 3 = 0
  s12 : fourStarSDet F 1 2 0 3 = 0
  s23 : fourStarSDet F 2 3 0 1 = 0
  s03 : fourStarSDet F 0 3 1 2 = 0

/-- Canonical determinant package `S01,S02,S12,S03`. -/
structure FourStarCanonicalTrianglePendantDeterminants
    (F : FourStarProjectiveSkeleton) : Prop where
  s01 : fourStarSDet F 0 1 2 3 = 0
  s02 : fourStarSDet F 0 2 1 3 = 0
  s12 : fourStarSDet F 1 2 0 3 = 0
  s03 : fourStarSDet F 0 3 1 2 = 0

private theorem fourStar_preimage_trace_mem
    {σ : Equiv.Perm FourStarVertex}
    {E C : Finset (Finset FourStarVertex)}
    (hσ : fourStarRelabelTraceFamily σ E = C)
    {T : Finset FourStarVertex} (hT : T ∈ C) :
    fourStarRelabelTrace σ.symm T ∈ E := by
  apply (mem_fourStarRelabelTraceFamily σ E T).mp
  rw [hσ]
  exact hT

private theorem fourStar_complement_pair_relabel
    (σ : Equiv.Perm FourStarVertex) (i j k l : FourStarVertex)
    (hcomp : ({k, l} : Finset FourStarVertex) =
      (Finset.univ : Finset FourStarVertex) \ {i, j}) :
    ({σ.symm k, σ.symm l} : Finset FourStarVertex) =
      (Finset.univ : Finset FourStarVertex) \ {σ.symm i, σ.symm j} := by
  have hmap := congrArg
    (fun T : Finset FourStarVertex => T.map σ.symm.toEmbedding) hcomp
  simpa [Finset.map_sdiff, Finset.map_univ_equiv] using hmap

private theorem fourStarTDet_relabel_eq_zero_of_mem
    {F : FourStarProjectiveSkeleton}
    {E C : Finset (Finset FourStarVertex)}
    (D : FourStarTraceDeterminantData F E)
    {σ : Equiv.Perm FourStarVertex}
    (hσ : fourStarRelabelTraceFamily σ E = C)
    (i j k : FourStarVertex)
    (hcard : ({i, j, k} : Finset FourStarVertex).card = 3)
    (hmem : ({i, j, k} : Finset FourStarVertex) ∈ C) :
    fourStarTDet (F.relabel σ) i j k = 0 := by
  have hpre := fourStar_preimage_trace_mem hσ hmem
  have hpre' : ({σ.symm i, σ.symm j, σ.symm k} :
      Finset FourStarVertex) ∈ E := by
    simpa [fourStarRelabelTrace] using hpre
  have hcard' : ({σ.symm i, σ.symm j, σ.symm k} :
      Finset FourStarVertex).card = 3 := by
    calc
      ({σ.symm i, σ.symm j, σ.symm k} : Finset FourStarVertex).card =
          (({i, j, k} : Finset FourStarVertex).map
            σ.symm.toEmbedding).card := by
              congr 1
              ext x
              simp
      _ = ({i, j, k} : Finset FourStarVertex).card := Finset.card_map _
      _ = 3 := hcard
  simpa using D.t_zero _ _ _ hcard' hpre'

private theorem fourStarSDet_relabel_eq_zero_of_mem
    {F : FourStarProjectiveSkeleton}
    {E C : Finset (Finset FourStarVertex)}
    (D : FourStarTraceDeterminantData F E)
    {σ : Equiv.Perm FourStarVertex}
    (hσ : fourStarRelabelTraceFamily σ E = C)
    (i j k l : FourStarVertex)
    (hcard : ({i, j} : Finset FourStarVertex).card = 2)
    (hmem : ({i, j} : Finset FourStarVertex) ∈ C)
    (hcomp : ({k, l} : Finset FourStarVertex) =
      (Finset.univ : Finset FourStarVertex) \ {i, j}) :
    fourStarSDet (F.relabel σ) i j k l = 0 := by
  have hpre := fourStar_preimage_trace_mem hσ hmem
  have hpre' : ({σ.symm i, σ.symm j} : Finset FourStarVertex) ∈ E := by
    simpa [fourStarRelabelTrace] using hpre
  have hcard' : ({σ.symm i, σ.symm j} :
      Finset FourStarVertex).card = 2 := by
    calc
      ({σ.symm i, σ.symm j} : Finset FourStarVertex).card =
          (({i, j} : Finset FourStarVertex).map
            σ.symm.toEmbedding).card := by
              congr 1
              ext x
              simp
      _ = ({i, j} : Finset FourStarVertex).card := Finset.card_map _
      _ = 2 := hcard
  simpa using D.s_zero _ _ _ _ hcard' hpre'
    (fourStar_complement_pair_relabel σ i j k l hcomp)

/-- An actual `T`-star and its determinant incidences admit the precise
canonical endpoint `T012,S03,S13,S23`. -/
theorem exists_fourStarCanonicalTStarDeterminants
    (F : FourStarProjectiveSkeleton)
    (E : Finset (Finset FourStarVertex))
    (hE : IsFourStarTStarTraceFamily E)
    (D : FourStarTraceDeterminantData F E) :
    ∃ σ : Equiv.Perm FourStarVertex,
      fourStarRelabelTraceFamily σ E = fourStarCanonicalTStar ∧
        FourStarCanonicalTStarDeterminants (F.relabel σ) := by
  obtain ⟨σ, hσ⟩ :=
    exists_fourStarRelabelTraceFamily_eq_canonicalTStar E hE
  refine ⟨σ, hσ, ?_⟩
  constructor
  · exact fourStarTDet_relabel_eq_zero_of_mem D hσ 0 1 2
      (by decide +kernel) (by simp [fourStarCanonicalTStar])
  · exact fourStarSDet_relabel_eq_zero_of_mem D hσ 0 3 1 2
      (by decide +kernel) (by simp [fourStarCanonicalTStar])
      (by decide +kernel)
  · exact fourStarSDet_relabel_eq_zero_of_mem D hσ 1 3 0 2
      (by decide +kernel) (by simp [fourStarCanonicalTStar])
      (by decide +kernel)
  · exact fourStarSDet_relabel_eq_zero_of_mem D hσ 2 3 0 1
      (by decide +kernel) (by simp [fourStarCanonicalTStar])
      (by decide +kernel)

/-- A four-cycle and its determinant incidences admit the precise canonical
endpoint `S01,S12,S23,S03`. -/
theorem exists_fourStarCanonicalFourCycleDeterminants
    (F : FourStarProjectiveSkeleton)
    (E : Finset (Finset FourStarVertex))
    (hfamily : IsFourStarPrivatePairFamily E)
    (hcycle : IsFourStarFourCycle E)
    (D : FourStarTraceDeterminantData F E) :
    ∃ σ : Equiv.Perm FourStarVertex,
      fourStarRelabelTraceFamily σ E = fourStarCanonicalFourCycle ∧
        FourStarCanonicalFourCycleDeterminants (F.relabel σ) := by
  obtain ⟨σ, hσ⟩ :=
    exists_fourStarRelabelTraceFamily_eq_canonicalFourCycle E hfamily hcycle
  refine ⟨σ, hσ, ?_⟩
  constructor
  · exact fourStarSDet_relabel_eq_zero_of_mem D hσ 0 1 2 3
      (by decide +kernel) (by simp [fourStarCanonicalFourCycle])
      (by decide +kernel)
  · exact fourStarSDet_relabel_eq_zero_of_mem D hσ 1 2 0 3
      (by decide +kernel) (by simp [fourStarCanonicalFourCycle])
      (by decide +kernel)
  · exact fourStarSDet_relabel_eq_zero_of_mem D hσ 2 3 0 1
      (by decide +kernel) (by simp [fourStarCanonicalFourCycle])
      (by decide +kernel)
  · exact fourStarSDet_relabel_eq_zero_of_mem D hσ 0 3 1 2
      (by decide +kernel) (by simp [fourStarCanonicalFourCycle])
      (by decide +kernel)

/-- A triangle-pendant and its determinant incidences admit the precise
canonical endpoint `S01,S02,S12,S03`. -/
theorem exists_fourStarCanonicalTrianglePendantDeterminants
    (F : FourStarProjectiveSkeleton)
    (E : Finset (Finset FourStarVertex))
    (hfamily : IsFourStarPrivatePairFamily E)
    (hpendant : IsFourStarTrianglePendant E)
    (D : FourStarTraceDeterminantData F E) :
    ∃ σ : Equiv.Perm FourStarVertex,
      fourStarRelabelTraceFamily σ E =
        fourStarCanonicalTrianglePendant ∧
        FourStarCanonicalTrianglePendantDeterminants (F.relabel σ) := by
  obtain ⟨σ, hσ⟩ :=
    exists_fourStarRelabelTraceFamily_eq_canonicalTrianglePendant
      E hfamily hpendant
  refine ⟨σ, hσ, ?_⟩
  constructor
  · exact fourStarSDet_relabel_eq_zero_of_mem D hσ 0 1 2 3
      (by decide +kernel) (by simp [fourStarCanonicalTrianglePendant])
      (by decide +kernel)
  · exact fourStarSDet_relabel_eq_zero_of_mem D hσ 0 2 1 3
      (by decide +kernel) (by simp [fourStarCanonicalTrianglePendant])
      (by decide +kernel)
  · exact fourStarSDet_relabel_eq_zero_of_mem D hσ 1 2 0 3
      (by decide +kernel) (by simp [fourStarCanonicalTrianglePendant])
      (by decide +kernel)
  · exact fourStarSDet_relabel_eq_zero_of_mem D hσ 0 3 1 2
      (by decide +kernel) (by simp [fourStarCanonicalTrianglePendant])
      (by decide +kernel)

end Erdos506.Incidence
