import Erdos506.V1.TwelveGridJOneParametricBridge

/-!
# Fully discharged twelve-grid geometry

All three former local grid rows are now consequences of the actual
inverted-line census and its projective parameter charts.
-/

namespace Erdos506.V1

open Erdos506.Block
open Erdos506.Block.BlockSystem
open Erdos506.Incidence
open Erdos506.V4

universe u

/-- The legacy twelve-grid principle with all of its local fields discharged
by the verified actual-grid theorems. -/
noncomputable def realPlaneTwelveGridPrinciple :
    RealPlaneTwelveGridPrinciple.{u} where
  jOneFiveDegreeCap := twelveGridJOne_five_degree_cap_unconditional
  forbiddenGridTypeZero := twelveGrid_forbiddenGridTypeZero_unconditional
  forbiddenGridTypeOne := twelveGrid_forbiddenGridTypeOne_unconditional

end Erdos506.V1
