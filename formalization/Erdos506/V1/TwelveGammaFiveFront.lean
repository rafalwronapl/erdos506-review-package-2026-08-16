import Mathlib.Tactic

/-!
# Arithmetic front for the twelve-point selected-five-circle branch

This file records the solver-free integer arithmetic in the first part of
the manuscript's `n = 12`, `Gamma_5` analysis.  It deliberately stops before
the endpoint arguments at `C = 47, ..., 50`.

The four fields of `TwelveGammaFiveFrontConditions` are the cleared forms of
`eq:n12-g5-triples`, `eq:n12-g5-block`, `eq:n12-g5-lines`, and
`eq:n12-g5-added`.  Subtractions have been moved across the equality or
inequality, so every expression is an equality or inequality of natural
numbers.

The bound `B5 <= 12` is exposed as a separate hypothesis.  In the paper it
comes from the obtuse-family argument for five-blocks; no version of that
geometric argument is encoded here.  With this cap, the added-centre row
already gives the honest common front `C >= 47`.

The final two declarations also record the three nonnegative-sum rows of the
paper's optional `q`-front.  They are an arithmetic interface only: a caller
must separately establish the geometric hypotheses which produce those
rows.  In particular, this module does not claim the full `C >= 51` endpoint
or a theorem about configurations.
-/

namespace Erdos506.V1

/-- The global counts in the twelve-point selected-five-circle spine. -/
structure TwelveGammaFiveFrontData where
  C : Nat
  B3 : Nat
  B4 : Nat
  B5 : Nat
  B6 : Nat
  K : Nat
  L : Nat

/-- The four exact global rows in the five-circle spine, together with the
explicit five-block cap used by the arithmetic front.

`blockRow`, `lineRow`, and `addedCenterRow` are written without truncated
natural-number subtraction.  They are obtained from the displayed rows in
the manuscript simply by moving all negative terms to the other side. -/
structure TwelveGammaFiveFrontConditions
    (d : TwelveGammaFiveFrontData) : Prop where
  fiveBlockCap : d.B5 <= 12
  tripleRow :
    d.B3 + 4 * d.B4 + 10 * d.B5 + 20 * d.B6 = 220
  blockRow :
    12 * d.B4 + 35 * d.B5 + 72 * d.B6 + d.K = 624
  lineRow :
    4 * d.L + 4 * d.C + d.B5 + 4 * d.B6 = 256 + d.K
  addedCenterRow :
    1776 + 5 * d.K + 72 * d.B6 <= 36 * d.C + 9 * d.B5

/-- The added-centre row and the explicit obtuse-family cap already exclude
all circle counts below `47`.  The other three spine rows are not needed for
this first lower bound. -/
theorem twelveGammaFive_addedCenter_circleCount_ge_forty_seven
    {C B5 B6 K : Nat}
    (hB5 : B5 <= 12)
    (hadded : 1776 + 5 * K + 72 * B6 <= 36 * C + 9 * B5) :
    47 <= C := by
  omega

/-- The common solver-free arithmetic front for the twelve-point
selected-five-circle branch. -/
theorem twelveGammaFive_front_circleCount_ge_forty_seven
    (d : TwelveGammaFiveFrontData)
    (h : TwelveGammaFiveFrontConditions d) :
    47 <= d.C := by
  exact twelveGammaFive_addedCenter_circleCount_ge_forty_seven
    h.fiveBlockCap h.addedCenterRow

/-- The three exact nonnegative-sum identities in `eq:n12-q-sums`.

The fields `sumJ`, `sumU`, and `sumQ` stand for `sum j`, `sum u`, and
`sum q`.  Their nonnegativity is represented by their type.  The displayed
subtractions in the paper are again cleared by moving terms across the
equalities. -/
structure TwelveGammaFiveQSumData where
  C : Nat
  k : Nat
  h : Nat
  sumJ : Nat
  sumU : Nat
  sumQ : Nat

structure TwelveGammaFiveQSumConditions
    (d : TwelveGammaFiveQSumData) : Prop where
  jSumRow : d.sumJ + 16 = 2 * d.k
  uSumRow : d.sumU + 132 + d.h = 3 * d.C
  qSumRow : d.sumQ + 140 + d.k + d.h = 3 * d.C

/-- Once the geometric `q`-front has supplied its three nonnegative-sum
rows, their arithmetic alone gives `k >= 8`, `k + h <= 3 C - 140`, and hence
the integral lower bound `C >= 50`.

This is conditional only on the displayed scalar rows and is not the final
twelve-point endpoint. -/
theorem twelveGammaFive_qSum_circleCount_ge_fifty
    (d : TwelveGammaFiveQSumData)
    (hrows : TwelveGammaFiveQSumConditions d) :
    8 <= d.k /\ 140 + d.k + d.h <= 3 * d.C /\ 50 <= d.C := by
  rcases hrows with ⟨hj, _hu, hq⟩
  constructor
  · omega
  · constructor <;> omega

end Erdos506.V1
