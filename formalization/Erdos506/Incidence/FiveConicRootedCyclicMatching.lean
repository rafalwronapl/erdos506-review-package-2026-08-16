import Erdos506.Incidence.FiveConicRootedCyclicFactor

/-!
# The finite third-matching endpoint for a rooted five-conic page

After the selected trace mark has been rooted at vertex `4`, the two
double-host directions singled out by the projective separator are the first
two rows of `kFiveRowOptions 4`.  A single host chord is excluded from both
of those rows by ordinary triple ownership.  This small finite file records
the resulting, exact endpoint: the chord is in the remaining row, hence in
the cyclic factor of the rooted mark.

There is no geometric hypothesis here.  The geometric page adapter supplies
the two exclusions; this file only performs the closed `K₅` calculation.
-/

namespace Erdos506.Incidence

open Erdos506.Finite
open Erdos506.V3
open Erdos506.V4

universe u

/-- Pull an actual selected chord back through the rooted cyclic trace
labelling. -/
noncomputable def fiveConicRootedCyclicChordIndex
    {α : Type u} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (Gamma : DeterminedCircle cfg)
    (hGamma : (circleTrace cfg Gamma.1).card = 5) (r : Fin 5)
    (e : KFiveChord (circleTrace cfg Gamma.1)) : FinFiveChord :=
  (kFiveChordEquivOfVertexLabel
    (fiveConicRootedCyclicLabel cfg Gamma hGamma r)).symm e

/-- The remaining normal matching after rows zero and one have been
excluded. -/
theorem finFiveChord_mem_row_two_of_avoids_four_not_rows_zero_one
    (e : FinFiveChord) (havoid : (4 : Fin 5) ∉ e.1)
    (hzero : e ∉ kFiveRowOptions 4 0)
    (hone : e ∉ kFiveRowOptions 4 1) :
    e ∈ kFiveRowOptions 4 2 := by
  rcases finFiveChord_eq_zero_three_or_one_two_of_avoids_four_not_rows_zero_one
      e havoid hzero hone with h | h
  · rw [h]
    decide +kernel
  · rw [h]
    decide +kernel

/-- In the original cyclic trace, a chord identified with either rooted
third-diagonal chord belongs to the factor of the rooted mark. -/
theorem fiveConicRootedCyclicChord_mem_factor_of_eq_zero_three_or_one_two
    {α : Type u} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (Gamma : DeterminedCircle cfg)
    (hGamma : (circleTrace cfg Gamma.1).card = 5) (r : Fin 5)
    (e : KFiveChord (circleTrace cfg Gamma.1))
    (he : e = fiveConicRootedCyclicChord cfg Gamma hGamma r 0 3 (by decide) ∨
      e = fiveConicRootedCyclicChord cfg Gamma hGamma r 1 2 (by decide)) :
    e ∈ fiveConicCyclicChordFactor cfg Gamma hGamma r := by
  rcases he with h | h
  · rw [h]
    exact fiveConicRootedCyclicChord_zero_three_mem_factor cfg Gamma hGamma r
  · rw [h]
    exact fiveConicRootedCyclicChord_one_two_mem_factor cfg Gamma hGamma r

/-- An actual selected chord whose rooted finite code is in the remaining
normal row belongs to the factor of the root mark. -/
theorem fiveConicRootedCyclicChord_mem_factor_of_index_mem_row_two
    {α : Type u} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (Gamma : DeterminedCircle cfg)
    (hGamma : (circleTrace cfg Gamma.1).card = 5) (r : Fin 5)
    (e : KFiveChord (circleTrace cfg Gamma.1))
    (hrow : fiveConicRootedCyclicChordIndex cfg Gamma hGamma r e ∈
      kFiveRowOptions 4 2) :
    e ∈ fiveConicCyclicChordFactor cfg Gamma hGamma r := by
  let E := kFiveChordEquivOfVertexLabel
    (fiveConicRootedCyclicLabel cfg Gamma hGamma r)
  let e' : FinFiveChord := E.symm e
  have he : e = E e' := (E.apply_symm_apply e).symm
  have hrow' : e' ∈ kFiveRowOptions 4 2 := by
    simpa [fiveConicRootedCyclicChordIndex, E, e'] using hrow
  have hcases : e' = kFiveChord03 ∨ e' = kFiveChord12 := by
    simpa [kFiveRowOptions] using hrow'
  apply fiveConicRootedCyclicChord_mem_factor_of_eq_zero_three_or_one_two
    cfg Gamma hGamma r e
  rcases hcases with h | h
  · left
    calc
      e = E e' := he
      _ = E kFiveChord03 := by rw [h]
      _ = fiveConicRootedCyclicChord cfg Gamma hGamma r 0 3 (by decide) := by
        symm
        simpa [E] using
          fiveConicRootedCyclicChord_eq_chordEquiv_rootedLabel
            cfg Gamma hGamma r 0 3 (by decide)
  · right
    calc
      e = E e' := he
      _ = E kFiveChord12 := by rw [h]
      _ = fiveConicRootedCyclicChord cfg Gamma hGamma r 1 2 (by decide) := by
        symm
        simpa [E] using
          fiveConicRootedCyclicChord_eq_chordEquiv_rootedLabel
            cfg Gamma hGamma r 1 2 (by decide)

/-- The finite third-row conclusion in a form convenient for actual host
traces: avoid the rooted page mark and rule out the two double rows. -/
theorem fiveConicRootedCyclicChord_mem_factor_of_avoids_root_not_rows_zero_one
    {α : Type u} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (Gamma : DeterminedCircle cfg)
    (hGamma : (circleTrace cfg Gamma.1).card = 5) (r : Fin 5)
    (e : KFiveChord (circleTrace cfg Gamma.1))
    (havoid : (fiveConicRootedCyclicLabel cfg Gamma hGamma r 4).1 ∉ e.1)
    (hzero : fiveConicRootedCyclicChordIndex cfg Gamma hGamma r e ∉
      kFiveRowOptions 4 0)
    (hone : fiveConicRootedCyclicChordIndex cfg Gamma hGamma r e ∉
      kFiveRowOptions 4 1) :
    e ∈ fiveConicCyclicChordFactor cfg Gamma hGamma r := by
  let E := kFiveChordEquivOfVertexLabel
    (fiveConicRootedCyclicLabel cfg Gamma hGamma r)
  let e' : FinFiveChord := E.symm e
  have havoid' : (4 : Fin 5) ∉ e'.1 := by
    intro hfour
    apply havoid
    have hmem := (mem_kFiveChordEquivOfVertexLabel
      (fiveConicRootedCyclicLabel cfg Gamma hGamma r) e' 4).mpr hfour
    simpa [E, e'] using hmem
  have hzero' : e' ∉ kFiveRowOptions 4 0 := by
    simpa [fiveConicRootedCyclicChordIndex, E, e'] using hzero
  have hone' : e' ∉ kFiveRowOptions 4 1 := by
    simpa [fiveConicRootedCyclicChordIndex, E, e'] using hone
  apply fiveConicRootedCyclicChord_mem_factor_of_index_mem_row_two
    cfg Gamma hGamma r e
  simpa [fiveConicRootedCyclicChordIndex, E, e'] using
    (finFiveChord_mem_row_two_of_avoids_four_not_rows_zero_one
      e' havoid' hzero' hone')

/-- A directly usable finite endpoint.  The four inequalities say that the
single host chord is not one of the two selected chords in either of the
first two double matchings.  Hence it has the colour of the rooted page
mark. -/
theorem fiveConicRootedCyclicChord_mem_factor_of_avoids_root_not_first_two_matchings
    {α : Type u} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (Gamma : DeterminedCircle cfg)
    (hGamma : (circleTrace cfg Gamma.1).card = 5) (r : Fin 5)
    (e : KFiveChord (circleTrace cfg Gamma.1))
    (havoid : (fiveConicRootedCyclicLabel cfg Gamma hGamma r 4).1 ∉ e.1)
    (h01 : e ≠ fiveConicRootedCyclicChord cfg Gamma hGamma r 0 1 (by decide))
    (h23 : e ≠ fiveConicRootedCyclicChord cfg Gamma hGamma r 2 3 (by decide))
    (h02 : e ≠ fiveConicRootedCyclicChord cfg Gamma hGamma r 0 2 (by decide))
    (h13 : e ≠ fiveConicRootedCyclicChord cfg Gamma hGamma r 1 3 (by decide)) :
    e ∈ fiveConicCyclicChordFactor cfg Gamma hGamma r := by
  let E := kFiveChordEquivOfVertexLabel
    (fiveConicRootedCyclicLabel cfg Gamma hGamma r)
  let e' : FinFiveChord := E.symm e
  have he : e = E e' := (E.apply_symm_apply e).symm
  apply fiveConicRootedCyclicChord_mem_factor_of_avoids_root_not_rows_zero_one
    cfg Gamma hGamma r e havoid
  · intro hmem
    have hcases : e' = kFiveChord01 ∨ e' = kFiveChord23 := by
      simpa [fiveConicRootedCyclicChordIndex, E, e', kFiveRowOptions] using hmem
    rcases hcases with h | h
    · apply h01
      calc
        e = E e' := he
        _ = E kFiveChord01 := by rw [h]
        _ = fiveConicRootedCyclicChord cfg Gamma hGamma r 0 1 (by decide) := by
          symm
          simpa [E] using
            fiveConicRootedCyclicChord_eq_chordEquiv_rootedLabel
              cfg Gamma hGamma r 0 1 (by decide)
    · apply h23
      calc
        e = E e' := he
        _ = E kFiveChord23 := by rw [h]
        _ = fiveConicRootedCyclicChord cfg Gamma hGamma r 2 3 (by decide) := by
          symm
          simpa [E] using
            fiveConicRootedCyclicChord_eq_chordEquiv_rootedLabel
              cfg Gamma hGamma r 2 3 (by decide)
  · intro hmem
    have hcases : e' = kFiveChord02 ∨ e' = kFiveChord13 := by
      simpa [fiveConicRootedCyclicChordIndex, E, e', kFiveRowOptions] using hmem
    rcases hcases with h | h
    · apply h02
      calc
        e = E e' := he
        _ = E kFiveChord02 := by rw [h]
        _ = fiveConicRootedCyclicChord cfg Gamma hGamma r 0 2 (by decide) := by
          symm
          simpa [E] using
            fiveConicRootedCyclicChord_eq_chordEquiv_rootedLabel
              cfg Gamma hGamma r 0 2 (by decide)
    · apply h13
      calc
        e = E e' := he
        _ = E kFiveChord13 := by rw [h]
        _ = fiveConicRootedCyclicChord cfg Gamma hGamma r 1 3 (by decide) := by
          symm
          simpa [E] using
            fiveConicRootedCyclicChord_eq_chordEquiv_rootedLabel
              cfg Gamma hGamma r 1 3 (by decide)

end Erdos506.Incidence
