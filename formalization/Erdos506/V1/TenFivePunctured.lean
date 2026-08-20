import Erdos506.Finite.PuncturedPentagon
import Erdos506.V1.NineOrdinaryMatchingCap
import Erdos506.V1.TenFiveSixPower
import Erdos506.V1.TenFiveFourPentagon
import Erdos506.V1.TenFiveThreePentagonFinite
import Erdos506.V1.TenFiveTwoPentagonGolden

/-!
# Finite adapter for the ten-point punctured-pentagon field

The reduction interface historically exposed this cap as a real-plane input.
The proof is in fact a theorem of the existing triple-owned block API.  This
adapter keeps the exact configuration-level argument order used by
`RealPlaneTenFiveReductionPrinciple.puncturedPentagonTransversalCap`.
-/

namespace Erdos506.V1

open Erdos506.Block
open Erdos506.Block.BlockSystem
open Erdos506.Finite
open Erdos506.Incidence
open Erdos506.V4

universe u

/-- Configuration-level adapter with the exact signature of the former
punctured-pentagon reduction field.  Admissibility and the global size cap are
not needed: triple-owner uniqueness already supplies every intersection guard
used by the finite theorem. -/
theorem finite_puncturedPentagonTransversalCap
    {α : Type u} [Fintype α] [DecidableEq α]
    (cfg : Configuration α)
    (_hadm : Admissible cfg)
    (hcard : Fintype.card α = 10)
    (_hcap : BlockSizeCap (blockSystem cfg) 5)
    (hfive : (blockSystem cfg).blockCount 5 = 5)
    (p : α)
    (hp : (blockSystem cfg).blockDegree 5 p = 3) :
    (blockSystem cfg).blockDegree 4 p ≤ 2 := by
  exact blockDegree_four_le_two_of_fiveBlock_puncture
    (blockSystem cfg) hcard hfive p hp

/-- All five ten-point reduction fields are now constructed internally.
The former residual argument is unnecessary: its sole two-pentagon field
is ruled out by the golden-axis contradiction. -/
noncomputable def realPlaneTenFiveReductionPrinciple
    (Mel : RealPlaneMelchiorPrinciple.{u})
    (EvenArr : RealPlaneEvenArrangementPrinciple.{u}) :
    RealPlaneTenFiveReductionPrinciple.{u} where
  sixFivePowerCoordinates := finite_sixFivePowerCoordinates
  puncturedPentagonTransversalCap := by
    intro alpha _ _ cfg hadm hcard hcap hfive p hp
    exact finite_puncturedPentagonTransversalCap
      cfg hadm hcard hcap hfive p hp
  fourPentagonCoordinates := finite_fourPentagonCoordinates
  threePentagonLink := by
    intro alpha _ _ cfg hadm hcard hcap _hcircle hB5 hhigh hL5 hL4pos
      hL4cap hL34 hlocal
    let d := finite_threePentagonExceptionalPivot
      (blockSystem cfg) hcard hcap hB5 hhigh hL5 hL4pos hL4cap hL34 hlocal
    have hbound := tenExceptionalPivot_lineDegree_three_le_three
      Mel EvenArr cfg hadm hcard d.pivot d.three_degree d.four_degree
    have hfalse : False := by
      rw [d.three_line_degree] at hbound
      omega
    exact hfalse.elim
  twoPentagonEndpoint := by
    intro alpha _ _ cfg hadm hcard hcircle hB3 hB4 hB5 hL3 hL4 hL5 hd3
    have hfalse :=
      TenTwoPentagonSaturationData.tenTwoPentagon_golden_impossible
        Mel EvenArr cfg hadm hcard hcircle hB3 hB4 hB5 hL3 hL4 hL5 hd3
    exact hfalse.elim

end Erdos506.V1
