import Erdos506.Incidence.FiveConicRootedCyclicTrace
import Erdos506.Finite.KFiveNearOneFactorizationRelabel

/-!
# The rooted normal third diagonal matching is the actual page colour

When a cyclic five-trace is rooted at a mark `r`, the third normal diagonal
is supported by the two chords `03` and `12`.  In the original cyclic
labelling these are exactly the two chords in the near-one factor of colour
`r`.  This finite statement connects the projective separator to the actual
factor partition without assigning a colour by hand.
-/

namespace Erdos506.Incidence

open Erdos506.Finite
open Erdos506.V3
open Erdos506.V4

universe u

/-- The finite chord obtained from a rooted pair of normal indices. -/
noncomputable def fiveConicRootedFinChord
    (r : Fin 5) (i j : Fin 5) (hij0 : i ≠ j) : FinFiveChord :=
  ⟨{fiveConicRootedCyclicIndex r i, fiveConicRootedCyclicIndex r j}, by
    have himage : fiveConicRootedCyclicIndex r i ≠
        fiveConicRootedCyclicIndex r j :=
      (fiveConicRootedCyclicIndex_injective r).ne hij0
    simp [himage]⟩

/-- The actual chord corresponding to a rooted pair of normal indices. -/
noncomputable def fiveConicRootedCyclicChord
    {α : Type u} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (Gamma : DeterminedCircle cfg)
    (hGamma : (circleTrace cfg Gamma.1).card = 5)
    (r i j : Fin 5) (hij : i ≠ j) : KFiveChord (circleTrace cfg Gamma.1) :=
  kFiveChordEquivOfVertexLabel (fiveConicCyclicLabel cfg Gamma hGamma)
    (fiveConicRootedFinChord r i j hij)

/-- Re-express a rooted chord using the rooted vertex equivalence itself.
This removes the bookkeeping permutation before a host trace is pulled back
to `Fin 5`. -/
theorem fiveConicRootedCyclicChord_eq_chordEquiv_rootedLabel
    {α : Type u} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (Gamma : DeterminedCircle cfg)
    (hGamma : (circleTrace cfg Gamma.1).card = 5)
    (r i j : Fin 5) (hij : i ≠ j) :
    fiveConicRootedCyclicChord cfg Gamma hGamma r i j hij =
      kFiveChordEquivOfVertexLabel
        (fiveConicRootedCyclicLabel cfg Gamma hGamma r)
        ⟨{i, j}, by simp [hij]⟩ := by
  rw [fiveConicRootedCyclicChord, fiveConicRootedCyclicLabel,
    kFiveChordEquivOfVertexLabel_trans_perm]
  apply congrArg (kFiveChordEquivOfVertexLabel
    (fiveConicCyclicLabel cfg Gamma hGamma))
  apply Subtype.ext
  ext k
  simp [fiveConicRootedFinChord, kFivePermuteChordEquiv]

private theorem fiveConicRootedFinChord_zero_three_mem_factor
    (r : Fin 5) :
    fiveConicRootedFinChord r 0 3 (by decide) ∈
      kFiveCyclicNearOneFactorizationCode.toFactorization.factor r := by
  fin_cases r <;> decide +kernel

private theorem fiveConicRootedFinChord_one_two_mem_factor
    (r : Fin 5) :
    fiveConicRootedFinChord r 1 2 (by decide) ∈
      kFiveCyclicNearOneFactorizationCode.toFactorization.factor r := by
  fin_cases r <;> decide +kernel

/-- On the four normal vertices other than `4`, a chord not belonging to
either of the first two diagonal matchings is one of the two third-diagonal
chords.  This is a closed finite fact, used after triple ownership excludes
the four double-host trace chords. -/
theorem finFiveChord_eq_zero_three_or_one_two_of_avoids_four_not_rows_zero_one
    (e : FinFiveChord) (havoid : (4 : Fin 5) ∉ e.1)
    (hzero : e ∉ kFiveRowOptions 4 0)
    (hone : e ∉ kFiveRowOptions 4 1) :
    e = kFiveChord03 ∨ e = kFiveChord12 := by
  decide +revert

/-- The rooted `03` normal chord belongs to the actual cyclic factor of the
root mark. -/
theorem fiveConicRootedCyclicChord_zero_three_mem_factor
    {α : Type u} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (Gamma : DeterminedCircle cfg)
    (hGamma : (circleTrace cfg Gamma.1).card = 5) (r : Fin 5) :
    fiveConicRootedCyclicChord cfg Gamma hGamma r 0 3 (by decide) ∈
      fiveConicCyclicChordFactor cfg Gamma hGamma r := by
  unfold fiveConicRootedCyclicChord fiveConicCyclicChordFactor
  exact Finset.mem_map.mpr ⟨fiveConicRootedFinChord r 0 3 (by decide),
    fiveConicRootedFinChord_zero_three_mem_factor r, rfl⟩

/-- The rooted `12` normal chord belongs to the same actual cyclic factor. -/
theorem fiveConicRootedCyclicChord_one_two_mem_factor
    {α : Type u} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (Gamma : DeterminedCircle cfg)
    (hGamma : (circleTrace cfg Gamma.1).card = 5) (r : Fin 5) :
    fiveConicRootedCyclicChord cfg Gamma hGamma r 1 2 (by decide) ∈
      fiveConicCyclicChordFactor cfg Gamma hGamma r := by
  unfold fiveConicRootedCyclicChord fiveConicCyclicChordFactor
  exact Finset.mem_map.mpr ⟨fiveConicRootedFinChord r 1 2 (by decide),
    fiveConicRootedFinChord_one_two_mem_factor r, rfl⟩

end Erdos506.Incidence
