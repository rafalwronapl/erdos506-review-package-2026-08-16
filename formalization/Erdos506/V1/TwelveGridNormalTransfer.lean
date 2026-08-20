import Erdos506.V1.PivotGeometry
import Erdos506.Incidence.RealThreeByThreeGrid

/-!
# The affine exit from the twelve-point grid branch

The two exceptional local rows in `RealPlaneTwelveGridPrinciple` are stated
only with block degrees.  Their geometric proof first inverts at the marked
point, extracts six four-lines, and normalizes the resulting `3 x 3` grid.
The abstract `BlockSystem` deliberately forgets the supports and coordinates
needed for that extraction.

This file formalizes the *lossless last step* of that argument.  A future
grid-entrance lemma need only construct `TwelveGridNormalTransfer` from one
of the two degree rows.  The contradiction from the normalized affine data
is then entirely checked here, with no finite search and no new geometric
principle.
-/

namespace Erdos506.V1

open Erdos506.Incidence
open Erdos506.V3
open Erdos506.V4

/-- The three affine coordinates used in the standard normal form. -/
def twelveGridCoordinate (i : Fin 3) : ℝ :=
  (i : ℝ) - 1

/-- The normalized affine `3 x 3` grid `{-1,0,1}²`. -/
def twelveGridPoint (ij : Fin 3 × Fin 3) : ℝ × ℝ :=
  (twelveGridCoordinate ij.1, twelveGridCoordinate ij.2)

/-- The two grid endpoints of each of the twelve ordinary secants.

The indices agree exactly with `RealThreeByThreeGridSecant.incident`:
the `Bool` is the sign of the constant term.  This is an explicit table,
rather than an existential endpoint choice, so the normalization certificate
can be transported without losing any incidence data. -/
def twelveGridSecantEndpoints (s : RealThreeByThreeGridSecant) :
    (Fin 3 × Fin 3) × (Fin 3 × Fin 3) :=
  match s.1, s.2 with
  | 0, false => ((0, 1), (1, 0))
  | 0, true  => ((1, 2), (2, 1))
  | 1, false => ((0, 1), (1, 2))
  | 1, true  => ((1, 0), (2, 1))
  | 2, false => ((0, 1), (2, 0))
  | 2, true  => ((0, 2), (2, 1))
  | 3, false => ((0, 1), (2, 2))
  | 3, true  => ((0, 0), (2, 1))
  | 4, false => ((0, 2), (1, 0))
  | 4, true  => ((1, 2), (2, 0))
  | 5, false => ((0, 0), (1, 2))
  | 5, true  => ((1, 0), (2, 2))

/-- Every entry of the endpoint table is incident with its named normalized
ordinary secant. -/
theorem twelveGridSecantEndpoints_incident
    (s : RealThreeByThreeGridSecant) :
    s.incident (twelveGridPoint (twelveGridSecantEndpoints s).1).1
      (twelveGridPoint (twelveGridSecantEndpoints s).1).2 /\
    s.incident (twelveGridPoint (twelveGridSecantEndpoints s).2).1
      (twelveGridPoint (twelveGridSecantEndpoints s).2).2 := by
  rcases s with ⟨i, sign⟩
  fin_cases i <;> cases sign <;>
    norm_num [twelveGridSecantEndpoints, twelveGridPoint,
      twelveGridCoordinate, RealThreeByThreeGridSecant.incident]

/-- Concrete affine data produced after inverting a twelve-point grid row.

`gridCoordinates` is the affine part of the projective normalization.  The
three entries of `externalSecants` are the transversal ordinary secants
through the remaining external point.  All fields are positive, concrete
data: this structure does not state any degree bound or any conclusion of
the twelve-point theorem.  `normalization` is deliberately exposed: the
currently missing grid-entrance development must prove that it is induced by
the relevant projective chart, rather than silently identifying the original
affine coordinates with normalized ones. -/
structure TwelveGridNormalTransfer
    {α : Type*} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (p : α) where
  normalization : AwayFrom p → ℝ × ℝ
  normalization_injective : Function.Injective normalization
  grid : Fin 3 × Fin 3 → AwayFrom p
  grid_injective : Function.Injective grid
  gridCoordinates : ∀ ij : Fin 3 × Fin 3,
    normalization (grid ij) = twelveGridPoint ij
  external : AwayFrom p
  externalOutside : RealThreeByThreeGridExternal
    (normalization external).1 (normalization external).2
  externalSecants : Fin 3 → RealThreeByThreeGridSecant
  externalSecants_distinct : Function.Injective externalSecants
  externalSecants_incident : ∀ i : Fin 3,
    (externalSecants i).incident
      (normalization external).1 (normalization external).2

/-- Transport the endpoint table to the actual inverted configuration.
This is the exact coordinate dictionary a grid-entrance proof obtains once
its six four-lines have been projectively normalized. -/
theorem TwelveGridNormalTransfer.gridSecantEndpoints_incident
    {α : Type*} [Fintype α] [DecidableEq α]
    {cfg : Configuration α} {p : α}
    (T : TwelveGridNormalTransfer cfg p)
    (s : RealThreeByThreeGridSecant) :
    s.incident
      (T.normalization (T.grid (twelveGridSecantEndpoints s).1)).1
      (T.normalization (T.grid (twelveGridSecantEndpoints s).1)).2 /\
    s.incident
      (T.normalization (T.grid (twelveGridSecantEndpoints s).2)).1
      (T.normalization (T.grid (twelveGridSecantEndpoints s).2)).2 := by
  have htable := twelveGridSecantEndpoints_incident s
  rw [T.gridCoordinates (twelveGridSecantEndpoints s).1,
    T.gridCoordinates (twelveGridSecantEndpoints s).2]
  exact htable

/-- The normalized affine grid has no external point on three distinct
ordinary secants.  This closes the geometric tail of either forbidden-grid
row as soon as its projective/affine grid entrance has been constructed. -/
theorem TwelveGridNormalTransfer.impossible
    {α : Type*} [Fintype α] [DecidableEq α]
    {cfg : Configuration α} {p : α}
    (T : TwelveGridNormalTransfer cfg p) : False := by
  have hpair01 : T.externalSecants 0 ≠ T.externalSecants 1 := by
    intro h
    have : (0 : Fin 3) = 1 := T.externalSecants_distinct h
    omega
  have hpair02 : T.externalSecants 0 ≠ T.externalSecants 2 := by
    intro h
    have : (0 : Fin 3) = 2 := T.externalSecants_distinct h
    omega
  have hpair12 : T.externalSecants 1 ≠ T.externalSecants 2 := by
    intro h
    have : (1 : Fin 3) = 2 := T.externalSecants_distinct h
    omega
  exact
    (RealThreeByThreeGridSecant.external_not_three_distinct
      (T.externalSecants 0) (T.externalSecants 1) (T.externalSecants 2)
      (T.normalization T.external).1
      (T.normalization T.external).2
      hpair01 hpair02 hpair12
      (T.externalSecants_incident 0)
      (T.externalSecants_incident 1)
      (T.externalSecants_incident 2)) T.externalOutside

end Erdos506.V1
