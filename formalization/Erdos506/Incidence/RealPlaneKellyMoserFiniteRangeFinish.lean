import Erdos506.Incidence.RealPlaneKellyMoserFiniteSizes

/-!
# The guarded Kelly--Moser principle used by V1

The public pivot interface only asks for configurations of cardinality
`10..13`.  After pivot inversion these are exactly the four finite ordinary
line bounds `q = 9,10,11,12` proved in `RealPlaneKellyMoserFiniteSizes`.
-/

namespace Erdos506.Incidence

open Erdos506.V1
open Erdos506.V3
open Erdos506.V4

universe u

/-- Dispatch the four unconditional finite ordinary-line endpoints. -/
theorem ordinary_line_bound_of_card_nine_twelve
    {alpha : Type u} [Fintype alpha] [DecidableEq alpha]
    (Mel : RealPlaneMelchiorPrinciple.{u})
    (EvenArr : RealPlaneEvenArrangementPrinciple.{u})
    (cfg : Configuration alpha) (hnon : Noncollinear cfg)
    (hmin : 9 ≤ Fintype.card alpha)
    (hmax : Fintype.card alpha ≤ 12) :
    3 * Fintype.card alpha ≤ 7 * (blockSystem cfg).lineCount 2 := by
  interval_cases hcard : Fintype.card alpha
  · have h := four_le_lineCount_two_of_card_nine
      Mel cfg hnon hcard
    omega
  · have h := five_le_lineCount_two_of_card_ten
      Mel EvenArr cfg hnon hcard
    omega
  · have h := five_le_lineCount_two_of_card_eleven
      Mel cfg hnon hcard
    omega
  · have h := six_le_lineCount_two_of_card_twelve
      Mel EvenArr cfg hnon hcard
    omega

/-- The actual guarded Kelly--Moser value.  No assertion outside the
`10..13` pivot range is needed or manufactured. -/
noncomputable def realPlaneKellyMoserPrincipleOfFiniteSizes
    (Mel : RealPlaneMelchiorPrinciple.{u})
    (EvenArr : RealPlaneEvenArrangementPrinciple.{u}) :
    RealPlaneKellyMoserPrinciple.{u} where
  pivot_three_block_bound := by
    intro alpha _ _ cfg hadm hmin hmax p
    have hcard : 3 ≤ Fintype.card alpha := by omega
    have hnon : Noncollinear (pivotInversion cfg p) :=
      pivotInversion_noncollinear cfg hadm hcard p
    have hawayMin : 9 ≤ Fintype.card (AwayFrom p) := by
      rw [card_awayFrom]
      omega
    have hawayMax : Fintype.card (AwayFrom p) ≤ 12 := by
      rw [card_awayFrom]
      omega
    have hdirect := ordinary_line_bound_of_card_nine_twelve
      Mel EvenArr (pivotInversion cfg p) hnon hawayMin hawayMax
    rw [card_awayFrom,
      ← blockDegree_three_eq_lineCount_two_pivotInversion] at hdirect
    exact hdirect

end Erdos506.Incidence
