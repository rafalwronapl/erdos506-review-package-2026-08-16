import Erdos506.Finite.KFiveNearOneFactorizationRelabel
import Erdos506.Incidence.GoldenAxisDeterminants

/-!
# Canonical K5 rows used by the golden-axis obstruction

This file is the small finite seam between the canonical
near-one-factorization and the four chord rows used by the projective
golden-axis certificate.
-/

namespace Erdos506.Finite

open Erdos506.Incidence

/-- The chord in row `i + 1` and position `j` of the canonical table. -/
def goldenCanonicalChord (i : Fin 4) (j : Fin 2) : FinFiveChord :=
  ⟨{goldenCenterChordEndpoint i j 0,
      goldenCenterChordEndpoint i j 1}, by
    fin_cases i <;> fin_cases j <;> decide⟩

@[simp] theorem goldenCanonicalChord_val
    (i : Fin 4) (j : Fin 2) :
    (goldenCanonicalChord i j).1 =
      {goldenCenterChordEndpoint i j 0,
        goldenCenterChordEndpoint i j 1} := rfl

/-- The four nonzero rows of the canonical K5 factorization are precisely
the rows in `goldenCenterChordEndpoint`. -/
theorem kFiveCanonicalFactorFamily_succ
    (i : Fin 4) :
    kFiveCanonicalFactorFamily i.succ =
      {goldenCanonicalChord i 0, goldenCanonicalChord i 1} := by
  fin_cases i <;>
    decide +kernel

theorem goldenCanonicalChord_mem_succ
    (i : Fin 4) (j : Fin 2) :
    goldenCanonicalChord i j ∈
      kFiveCanonicalFactorFamily i.succ := by
  rw [kFiveCanonicalFactorFamily_succ]
  fin_cases j <;> simp

/-- Transport the displayed golden chord to an arbitrary canonical vertex
labelling. -/
noncomputable def goldenLabelledChord
    {α : Type*} [DecidableEq α] {A : Finset α}
    (v : Fin 5 ≃ ↥A) (i : Fin 4) (j : Fin 2) : KFiveChord A :=
  kFiveChordEquivOfVertexLabel v (goldenCanonicalChord i j)

@[simp] theorem mem_goldenLabelledChord
    {α : Type*} [DecidableEq α] {A : Finset α}
    (v : Fin 5 ≃ ↥A) (i : Fin 4) (j : Fin 2) (k : Fin 2) :
    (v (goldenCenterChordEndpoint i j k)).1 ∈
      (goldenLabelledChord v i j).1 := by
  exact (mem_kFiveChordEquivOfVertexLabel v (goldenCanonicalChord i j)
    (goldenCenterChordEndpoint i j k)).2 (by
      fin_cases k <;> simp [goldenCanonicalChord])

/-- Each displayed golden chord belongs to its canonical row. -/
@[simp] theorem goldenCanonicalChord_mem
    (i : Fin 4) (j : Fin 2) :
    goldenCanonicalChord i j ∈
      kFiveCanonicalFactorFamily i.succ := by
  exact goldenCanonicalChord_mem_succ i j

/-- A displayed chord transported by a label belongs to the corresponding
factor of any abstract factorization whose pulled-back family is canonical. -/
theorem goldenLabelledChord_mem_factorAtVertex
    {α Colour : Type*} [DecidableEq α]
    [Fintype Colour] [DecidableEq Colour]
    {A : Finset α} (F : KFiveNearOneFactorization A Colour)
    (v : Fin 5 ≃ ↥A)
    (hcanonical : F.pullbackFactorFamily v = kFiveCanonicalFactorFamily)
    (i : Fin 4) (j : Fin 2) :
    goldenLabelledChord v i j ∈ F.factorAtVertex (v i.succ) := by
  apply (F.mem_pullbackFactorFamily v i.succ
    (goldenCanonicalChord i j)).mp
  rw [hcanonical]
  exact goldenCanonicalChord_mem_succ i j

/-- The omitted-colour label induced by `v` sends `i` to the colour whose
factor is the canonical row `i`. -/
noncomputable def KFiveNearOneFactorization.colourLabel
    {α Colour : Type*} [DecidableEq α]
    [Fintype Colour] [DecidableEq Colour]
    {A : Finset α} (F : KFiveNearOneFactorization A Colour)
    (v : Fin 5 ≃ ↥A) : Fin 5 ≃ Colour :=
  v.trans F.omittedColourEquiv.symm

@[simp] theorem KFiveNearOneFactorization.omitted_colourLabel
    {α Colour : Type*} [DecidableEq α]
    [Fintype Colour] [DecidableEq Colour]
    {A : Finset α} (F : KFiveNearOneFactorization A Colour)
    (v : Fin 5 ≃ ↥A) (i : Fin 5) :
    F.omittedColourEquiv (F.colourLabel v i) = v i := by
  simp [KFiveNearOneFactorization.colourLabel]

theorem goldenLabelledChord_mem_factor
    {α Colour : Type*} [DecidableEq α]
    [Fintype Colour] [DecidableEq Colour]
    {A : Finset α} (F : KFiveNearOneFactorization A Colour)
    (v : Fin 5 ≃ ↥A)
    (hcanonical : F.pullbackFactorFamily v = kFiveCanonicalFactorFamily)
    (i : Fin 4) (j : Fin 2) :
    goldenLabelledChord v i j ∈ F.factor (F.colourLabel v i.succ) := by
  have h := goldenLabelledChord_mem_factorAtVertex
    F v hcanonical i j
  simpa [KFiveNearOneFactorization.factorAtVertex,
    KFiveNearOneFactorization.colourLabel] using h

end Erdos506.Finite
