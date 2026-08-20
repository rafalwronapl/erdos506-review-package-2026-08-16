import Erdos506.V1.ThirteenSixConservationB

/-!
# Terminal materialization for the thirteen-point selected-six branch

This module keeps the terminal Presburger calculation separate from the
geometric endpoint.  In particular, `J` is the signed residual used in the
paper; it is not identified with any line-incidence count.
-/

namespace Erdos506.V1

open Erdos506.Block
open Erdos506.Block.BlockSystem
open Erdos506.Incidence
open Erdos506.V4
open scoped BigOperators

universe u v

section TerminalSpine

variable {Point : Type u} {Block : Type v}
  [Fintype Point] [Fintype Block] [DecidableEq Point]

def thirteenSixEventCapacitySum
    (S : BlockSystem Point Block) (D : Finset Point) : Nat :=
  2 * thirteenSixRelativeCount S D .circle 0 4 +
  3 * thirteenSixRelativeCount S D .circle 0 5 +
  9 * thirteenSixRelativeCount S D .circle 0 6 +
  2 * thirteenSixRelativeCount S D .line 0 4 +
  2 * thirteenSixRelativeCount S D .circle 2 4

/-- Scalar copy of the eight affine rows and the retained second budget.
All expensive Presburger lemmas below quantify only over this data, never
over a block system or a geometric configuration. -/
structure ThirteenSixTerminalSpine where
  c03 : Nat
  h : Nat
  k : Nat
  A6 : Nat
  c12 : Nat
  y : Nat
  z : Nat
  c15 : Nat
  c21 : Nat
  c22 : Nat
  f : Nat
  g : Nat
  l03 : Nat
  ell : Nat
  l12 : Nat
  w : Nat
  l21 : Nat
  t : Nat
  p : Nat
  C : Nat
  C3 : Nat
  W : Nat
  u : Nat
  v : Nat
  d : Nat
  r : Nat
  j : Nat
  circleRow :
    1 + c03 + h + k + A6 + c12 + y + z + c15 + c21 + c22 + f + g = C
  ordinaryRow : c03 + c12 + c21 = C3
  row0 :
    c03 + 4 * h + 10 * k + 20 * A6 + y + 4 * z + 10 * c15 + f +
      4 * g + l03 + 4 * ell + w + p = 35
  row1 :
    c12 + 3 * y + 6 * z + 10 * c15 + 2 * c22 + 6 * f + 12 * g +
      l12 + 3 * w + 2 * t + 6 * p = 126
  row2 : c21 + 2 * c22 + 3 * f + 4 * g + l21 + 2 * t + 3 * p = 105
  weightRow : c22 + 3 * f + 6 * g = W
  momentXRow :
    (3 : Int) * c03 - 5 * k - 12 * A6 + 2 * c12 - 4 * z - 10 * c15 +
      c21 - 3 * f - 8 * g + 3 * l03 + 2 * l12 + l21 - 3 * p = 21 + u
  momentGammaRow :
    (-12 : Int) + c12 - z - 2 * c15 + 2 * c21 - 2 * f - 4 * g +
      l12 + 2 * l21 - 2 * p = 18 + v
  circleSlack : C + d = 60
  ordinarySlack : C3 = 13 + j
  weightSlack : W = 48 + r
  secondBudget :
    12 * h + 26 * k + 36 * A6 + 3 * y + 5 * z + 2 * f +
      40 * ell + 31 * w + 22 * t + 48 * p + 6 * u + 3 * v + 36 * d ≤
        12 + 6 * r

namespace ThirteenSixTerminalSpine

def eventCapacity (x : ThirteenSixTerminalSpine) : Nat :=
  2 * x.h + 3 * x.k + 9 * x.A6 + 2 * x.ell + 2 * x.g

/-- The signed `J` of the manuscript before nonnegativity is proved. -/
def paperJZ (x : ThirteenSixTerminalSpine) : Int :=
  21 + 18 * (x.r : Int) -
    (24 * (x.g : Int) + 24 * x.h + 36 * x.k + 84 * x.A6 + 24 * x.ell)

def paperJ (x : ThirteenSixTerminalSpine) : Nat :=
  Int.toNat x.paperJZ

def capacityData (x : ThirteenSixTerminalSpine)
    (repetitionEvents : Nat) : ThirteenSixCapacityGapData where
  r := x.r
  repetitionEvents := repetitionEvents
  E := x.eventCapacity
  A6 := x.A6
  h := x.h
  k := x.k
  ell := x.ell
  g := x.g
  y := x.y
  z := x.z
  f := x.f
  w := x.w
  t := x.t
  p := x.p
  u := x.u
  v := x.v
  d := x.d

end ThirteenSixTerminalSpine

/-- Materialize the pure terminal spine from the canonical relative census. -/
def thirteenSixTerminalSpineOfBlockSystem
    (S : BlockSystem Point Block) (D : Finset Point)
    {C C3 W u v d r j : Nat}
    (rows : ThirteenSixAffineRows S D C C3 W u v d r j)
    (hbudget :
      12 * thirteenSixRelativeCount S D .circle 0 4 +
        26 * thirteenSixRelativeCount S D .circle 0 5 +
        36 * thirteenSixRelativeCount S D .circle 0 6 +
        3 * thirteenSixRelativeCount S D .circle 1 3 +
        5 * thirteenSixRelativeCount S D .circle 1 4 +
        2 * thirteenSixRelativeCount S D .circle 2 3 +
        40 * thirteenSixRelativeCount S D .line 0 4 +
        31 * thirteenSixRelativeCount S D .line 1 3 +
        22 * thirteenSixRelativeCount S D .line 2 2 +
        48 * thirteenSixRelativeCount S D .line 2 3 +
        6 * u + 3 * v + 36 * d ≤ 12 + 6 * r) :
    ThirteenSixTerminalSpine :=
  { c03 := thirteenSixRelativeCount S D .circle 0 3
    h := thirteenSixRelativeCount S D .circle 0 4
    k := thirteenSixRelativeCount S D .circle 0 5
    A6 := thirteenSixRelativeCount S D .circle 0 6
    c12 := thirteenSixRelativeCount S D .circle 1 2
    y := thirteenSixRelativeCount S D .circle 1 3
    z := thirteenSixRelativeCount S D .circle 1 4
    c15 := thirteenSixRelativeCount S D .circle 1 5
    c21 := thirteenSixRelativeCount S D .circle 2 1
    c22 := thirteenSixRelativeCount S D .circle 2 2
    f := thirteenSixRelativeCount S D .circle 2 3
    g := thirteenSixRelativeCount S D .circle 2 4
    l03 := thirteenSixRelativeCount S D .line 0 3
    ell := thirteenSixRelativeCount S D .line 0 4
    l12 := thirteenSixRelativeCount S D .line 1 2
    w := thirteenSixRelativeCount S D .line 1 3
    l21 := thirteenSixRelativeCount S D .line 2 1
    t := thirteenSixRelativeCount S D .line 2 2
    p := thirteenSixRelativeCount S D .line 2 3
    C := C
    C3 := C3
    W := W
    u := u
    v := v
    d := d
    r := r
    j := j
    circleRow := rows.circleRow
    ordinaryRow := rows.ordinaryRow
    row0 := rows.row0
    row1 := rows.row1
    row2 := rows.row2
    weightRow := rows.weightRow
    momentXRow := rows.momentXRow
    momentGammaRow := rows.momentGammaRow
    circleSlack := rows.circleSlack
    ordinarySlack := rows.ordinarySlack
    weightSlack := rows.weightSlack
    secondBudget := hbudget }

/-! The signed-`J` certificate is kept in small, opaque stages.  In
particular, no tactic below is asked to eliminate all census variables at
once. -/

/-- The eight manuscript rows, normalized over `Int`, together with `B₀`. -/
private structure ThirteenSixPaperAffineRows
    (x : ThirteenSixTerminalSpine) : Prop where
  circle :
    (1 : Int) + x.c03 + x.h + x.k + x.A6 + x.c12 + x.y + x.z + x.c15 +
        x.c21 + x.c22 + x.f + x.g =
      60 - x.d
  ordinary : (x.c03 : Int) + x.c12 + x.c21 = 13 + x.j
  row0 :
    (x.c03 : Int) + 4 * x.h + 10 * x.k + 20 * x.A6 + x.y + 4 * x.z +
        10 * x.c15 + x.f + 4 * x.g + x.l03 + 4 * x.ell + x.w + x.p =
      35
  row1 :
    (x.c12 : Int) + 3 * x.y + 6 * x.z + 10 * x.c15 + 2 * x.c22 +
        6 * x.f + 12 * x.g + x.l12 + 3 * x.w + 2 * x.t + 6 * x.p =
      126
  row2 :
    (x.c21 : Int) + 2 * x.c22 + 3 * x.f + 4 * x.g + x.l21 + 2 * x.t +
        3 * x.p =
      105
  weight : (x.c22 : Int) + 3 * x.f + 6 * x.g = 48 + x.r
  momentX :
    (3 : Int) * x.c03 - 5 * x.k - 12 * x.A6 + 2 * x.c12 - 4 * x.z -
        10 * x.c15 + x.c21 - 3 * x.f - 8 * x.g + 3 * x.l03 +
        2 * x.l12 + x.l21 - 3 * x.p =
      21 + x.u
  momentGamma :
    (-12 : Int) + x.c12 - x.z - 2 * x.c15 + 2 * x.c21 - 2 * x.f -
        4 * x.g + x.l12 + 2 * x.l21 - 2 * x.p =
      18 + x.v
  budget :
    (12 : Int) * x.h + 26 * x.k + 36 * x.A6 + 3 * x.y + 5 * x.z +
        2 * x.f + 40 * x.ell + 31 * x.w + 22 * x.t + 48 * x.p +
        6 * x.u + 3 * x.v + 36 * x.d ≤
      12 + 6 * x.r

private theorem thirteenSix_paperAffineRows
    (x : ThirteenSixTerminalSpine) : ThirteenSixPaperAffineRows x := by
  have hC :
      (1 : Int) + x.c03 + x.h + x.k + x.A6 + x.c12 + x.y + x.z + x.c15 +
          x.c21 + x.c22 + x.f + x.g =
        x.C := by
    exact_mod_cast x.circleRow
  have hCs : (x.C : Int) + x.d = 60 := by
    exact_mod_cast x.circleSlack
  have hO : (x.c03 : Int) + x.c12 + x.c21 = x.C3 := by
    exact_mod_cast x.ordinaryRow
  have hOs : (x.C3 : Int) = 13 + x.j := by
    exact_mod_cast x.ordinarySlack
  have hW : (x.c22 : Int) + 3 * x.f + 6 * x.g = x.W := by
    exact_mod_cast x.weightRow
  have hWs : (x.W : Int) = 48 + x.r := by
    exact_mod_cast x.weightSlack
  refine
    { circle := by linarith only [hC, hCs]
      ordinary := by linarith only [hO, hOs]
      row0 := by exact_mod_cast x.row0
      row1 := by exact_mod_cast x.row1
      row2 := by exact_mod_cast x.row2
      weight := by linarith only [hW, hWs]
      momentX := x.momentXRow
      momentGamma := x.momentGammaRow
      budget := by exact_mod_cast x.secondBudget }

private def thirteenSixPaperN (x : ThirteenSixTerminalSpine) : Int :=
  x.j + x.y + x.z

private def thirteenSixPaperK0 (x : ThirteenSixTerminalSpine) : Int :=
  thirteenSixPaperN x + 2 * x.u + x.v + 4 * x.h + 8 * x.k + 12 * x.A6 +
    10 * x.ell + 8 * x.d + 4 * x.t + 7 * x.w

private def thirteenSixPaperQ0 (x : ThirteenSixTerminalSpine) : Int :=
  thirteenSixPaperN x + x.u + 4 * x.h + 8 * x.k + 12 * x.A6 +
    8 * x.ell + 8 * x.d + 2 * x.t + 5 * x.w + 7 * x.p

private def thirteenSixPaperB0 (x : ThirteenSixTerminalSpine) : Int :=
  12 * (x.h : Int) + 26 * x.k + 36 * x.A6 + 3 * x.y + 5 * x.z +
    2 * x.f + 40 * x.ell + 31 * x.w + 22 * x.t + 48 * x.p +
    6 * x.u + 3 * x.v + 36 * x.d - (12 + 6 * x.r)

private def thirteenSixPaperB1 (x : ThirteenSixTerminalSpine) : Int :=
  9 * thirteenSixPaperN x + 36 * x.h + 72 * x.k + 108 * x.A6 +
    76 * x.ell + 49 * x.w + 22 * x.t + 49 * x.p + 72 * x.d +
    11 * x.u + 2 * x.v - (21 + 18 * x.r)

private def thirteenSixPaperH (x : ThirteenSixTerminalSpine) : Int :=
  2 * (x.j : Int) + x.y - x.v + 4 * x.h + 7 * x.k + 12 * x.A6 +
    x.ell + 2 * x.d - 10 * x.p - 5 * x.t - 2 * x.w - 2 * x.r

private def thirteenSixPaperF0 (x : ThirteenSixTerminalSpine) : Int :=
  14 * (x.f : Int) -
    (180 * x.A6 + 24 * x.ell - 30 * x.r + 36 * x.d + 60 * x.h +
      36 * x.j + 106 * x.k - 140 * x.p - 66 * x.t + 2 * x.u -
      13 * x.v - 21 * x.w + 15 * x.y + x.z)

private def thirteenSixPaperMuZ (x : ThirteenSixTerminalSpine) : Int :=
  x.f - thirteenSixPaperH x

private def thirteenSixPaperEMu (x : ThirteenSixTerminalSpine) : Int :=
  thirteenSixPaperK0 x + 7 * x.j - 2 * x.r - 14 * thirteenSixPaperMuZ x

private def thirteenSixPaperL (x : ThirteenSixTerminalSpine) : Int :=
  3 + 2 * (x.r : Int) -
    (thirteenSixPaperQ0 x + 4 * thirteenSixPaperMuZ x - 2 * x.j)

private def thirteenSixPaperS (x : ThirteenSixTerminalSpine) : Int :=
  6 - (x.k : Int) - 5 * x.ell - 6 * x.d - 5 * x.t - 5 * x.w -
    24 * x.p - 21 * thirteenSixPaperMuZ x + 12 * x.j

private def thirteenSixPaperDeltaZ (x : ThirteenSixTerminalSpine) : Int :=
  7 * thirteenSixPaperMuZ x - 4 * x.j

private def thirteenSixPaperJRhs (x : ThirteenSixTerminalSpine) : Int :=
  49 * (x.f : Int) + 12 * x.j - 60 * thirteenSixPaperDeltaZ x +
    14 * (x.y + x.z) + 7 * x.y + 63 * x.u + 14 * x.v + 105 * x.k +
    168 * x.ell + 252 * x.d - 161 * x.p + 42 * x.t + 189 * x.w

/-- `F₀=0`, with the fixed row multipliers from the appendix. -/
private theorem thirteenSix_paper_F0_eq_zero
    (x : ThirteenSixTerminalSpine) (rows : ThirteenSixPaperAffineRows x) :
    thirteenSixPaperF0 x = 0 := by
  unfold thirteenSixPaperF0
  linear_combination
    -36 * rows.circle + 36 * rows.ordinary - 6 * rows.row0 +
      9 * rows.row1 + 24 * rows.row2 - 30 * rows.weight +
      2 * rows.momentX - 13 * rows.momentGamma

private theorem thirteenSix_paper_B01_identity
    (x : ThirteenSixTerminalSpine) :
    7 * thirteenSixPaperB0 x - 4 * thirteenSixPaperB1 x -
        thirteenSixPaperF0 x =
      0 := by
  unfold thirteenSixPaperB0 thirteenSixPaperB1 thirteenSixPaperF0
    thirteenSixPaperN
  ring

private theorem thirteenSix_paper_EMu_eq_zero
    (x : ThirteenSixTerminalSpine) (hF0 : thirteenSixPaperF0 x = 0) :
    thirteenSixPaperEMu x = 0 := by
  have hid : thirteenSixPaperEMu x = -thirteenSixPaperF0 x := by
    unfold thirteenSixPaperEMu thirteenSixPaperK0 thirteenSixPaperN
      thirteenSixPaperMuZ thirteenSixPaperH thirteenSixPaperF0
    ring
  rw [hid, hF0]
  norm_num

private theorem thirteenSix_paper_B1mu_identity
    (x : ThirteenSixTerminalSpine) :
    thirteenSixPaperB1 x =
      7 * (thirteenSixPaperQ0 x + 4 * thirteenSixPaperMuZ x - 2 * x.j -
        (3 + 2 * x.r)) + 2 * thirteenSixPaperEMu x := by
  unfold thirteenSixPaperB1 thirteenSixPaperQ0 thirteenSixPaperEMu
    thirteenSixPaperK0 thirteenSixPaperN
  ring

private theorem thirteenSix_paper_mu_nonnegative_arithmetic
    {K0 j r mu : Int}
    (hK0 : 0 ≤ K0) (hj : 0 ≤ j) (hr0 : 0 ≤ r) (hr6 : r ≤ 6)
    (hrow : K0 + 7 * j - 2 * r - 14 * mu = 0) :
    0 ≤ mu := by
  omega

private theorem thirteenSix_paper_S_identity
    (x : ThirteenSixTerminalSpine) (hF0 : thirteenSixPaperF0 x = 0) :
    thirteenSixPaperS x =
      (x.f : Int) + 2 * thirteenSixPaperL x + x.z := by
  have hid :
      thirteenSixPaperS x -
          ((x.f : Int) + 2 * thirteenSixPaperL x + x.z) =
        -thirteenSixPaperF0 x := by
    unfold thirteenSixPaperS thirteenSixPaperL thirteenSixPaperQ0
      thirteenSixPaperN thirteenSixPaperMuZ thirteenSixPaperH
      thirteenSixPaperF0
    ring
  rw [hF0] at hid
  linarith only [hid]

private theorem thirteenSix_paper_delta_identity
    (x : ThirteenSixTerminalSpine) :
    3 * thirteenSixPaperDeltaZ x =
      6 - x.k - 5 * x.ell - 6 * x.d - 5 * x.t - 5 * x.w - 24 * x.p -
        thirteenSixPaperS x := by
  unfold thirteenSixPaperDeltaZ thirteenSixPaperS
  ring

private theorem thirteenSix_paper_v_identity
    (x : ThirteenSixTerminalSpine) (hEMu : thirteenSixPaperEMu x = 0) :
    (x.v : Int) =
      2 * thirteenSixPaperDeltaZ x + 2 * x.r - (x.y + x.z) - 2 * x.u -
        4 * x.h - 8 * x.k - 12 * x.A6 - 10 * x.ell - 8 * x.d -
        4 * x.t - 7 * x.w := by
  have hid :
      (x.v : Int) -
          (2 * thirteenSixPaperDeltaZ x + 2 * x.r - (x.y + x.z) -
            2 * x.u - 4 * x.h - 8 * x.k - 12 * x.A6 - 10 * x.ell -
            8 * x.d - 4 * x.t - 7 * x.w) =
        thirteenSixPaperEMu x := by
    unfold thirteenSixPaperDeltaZ thirteenSixPaperEMu thirteenSixPaperK0
      thirteenSixPaperN
    ring
  rw [hEMu] at hid
  linarith only [hid]

private theorem thirteenSix_paper_f_identity
    (x : ThirteenSixTerminalSpine) :
    (x.f : Int) =
      2 * x.j + thirteenSixPaperMuZ x + x.y - x.v + 4 * x.h + 7 * x.k +
        12 * x.A6 + x.ell + 2 * x.d - 10 * x.p - 5 * x.t - 2 * x.w -
        2 * x.r := by
  unfold thirteenSixPaperMuZ thirteenSixPaperH
  ring

/-- Direct terminal `E_J` row certificate.  The ten fixed multipliers are
for `(R_C,R_O,R_0,R_1,R_2,R_W,R_X,R_Γ,E_μ-definition,J-definition)`. -/
private theorem thirteenSix_paper_EJ_identity
    (x : ThirteenSixTerminalSpine) (rows : ThirteenSixPaperAffineRows x) :
    7 * x.paperJZ = thirteenSixPaperJRhs x := by
  have hMu :
      thirteenSixPaperMuZ x = (x.f : Int) - thirteenSixPaperH x := rfl
  have hJ :
      x.paperJZ =
        21 + 18 * (x.r : Int) -
          (24 * (x.g : Int) + 24 * x.h + 36 * x.k + 84 * x.A6 +
            24 * x.ell) := rfl
  unfold thirteenSixPaperJRhs thirteenSixPaperDeltaZ thirteenSixPaperH at *
  linear_combination
    -1092 * rows.circle + 1092 * rows.ordinary - 189 * rows.row0 +
      280 * rows.row1 + 749 * rows.row2 - 966 * rows.weight +
      63 * rows.momentX - 406 * rows.momentGamma + 420 * hMu + 7 * hJ

private theorem thirteenSix_paper_delta_le_two_arithmetic
    {delta k ell d t w p S : Int}
    (hk : 0 ≤ k) (hell : 0 ≤ ell) (hd : 0 ≤ d) (ht : 0 ≤ t)
    (hw : 0 ≤ w) (hp : 0 ≤ p) (hS : 0 ≤ S)
    (hrow : 3 * delta = 6 - k - 5 * ell - 6 * d - 5 * t - 5 * w -
      24 * p - S) :
    delta ≤ 2 := by
  linarith

private theorem thirteenSix_paper_J_rhs_nonnegative_of_pair
    (x : ThirteenSixTerminalSpine)
    (hpair :
      0 ≤ 12 * (x.j : Int) - 60 * thirteenSixPaperDeltaZ x - 161 * x.p) :
    0 ≤ thirteenSixPaperJRhs x := by
  have hpositive :
      0 ≤ 49 * (x.f : Int) + 14 * (x.y + x.z) + 7 * x.y + 63 * x.u +
        14 * x.v + 105 * x.k + 168 * x.ell + 252 * x.d + 42 * x.t +
        189 * x.w := by
    positivity
  unfold thirteenSixPaperJRhs
  linarith only [hpositive, hpair]

private theorem thirteenSix_paper_delta_one_j_lower_arithmetic
    {mu j : Int} (hj : 0 ≤ j)
    (hrow : 1 = 7 * mu - 4 * j) :
    5 ≤ j := by
  omega

private theorem thirteenSix_paper_delta_two_zeros_arithmetic
    {k ell d t w S : Int}
    (hk : 0 ≤ k) (hell : 0 ≤ ell) (hd : 0 ≤ d) (ht : 0 ≤ t)
    (hw : 0 ≤ w) (hS : 0 ≤ S)
    (hrow : 6 = 6 - k - 5 * ell - 6 * d - 5 * t - 5 * w - S) :
    k = 0 ∧ ell = 0 ∧ d = 0 ∧ t = 0 ∧ w = 0 ∧ S = 0 := by
  omega

private theorem thirteenSix_paper_delta_two_j_cases_arithmetic
    {mu j : Int} (hj : 0 ≤ j)
    (hrow : 2 = 7 * mu - 4 * j) :
    j = 3 ∨ 10 ≤ j := by
  omega

private theorem thirteenSix_paper_delta_two_mu_arithmetic
    {mu j : Int} (hj : j = 3) (hrow : 2 = 7 * mu - 4 * j) :
    mu = 2 := by
  omega

private theorem thirteenSix_paper_positive_delta_cases_arithmetic
    {delta : Int} (hpos : 0 < delta) (hle : delta ≤ 2) :
    delta = 1 ∨ delta = 2 := by
  omega

private theorem thirteenSix_paper_extreme_uv_lower_arithmetic
    {B u v r : Int}
    (hQ : B + u + 2 ≤ 2 * r)
    (hV : v + B + 2 * u = 4 + 2 * r) :
    6 ≤ u + v := by
  linarith only [hQ, hV]

private theorem thirteenSix_paperJZ_nonnegative
    (x : ThirteenSixTerminalSpine) (hr : x.r ≤ 6) : 0 ≤ x.paperJZ := by
  let rows := thirteenSix_paperAffineRows x
  have hF0 : thirteenSixPaperF0 x = 0 :=
    thirteenSix_paper_F0_eq_zero x rows
  have hEMu : thirteenSixPaperEMu x = 0 :=
    thirteenSix_paper_EMu_eq_zero x hF0
  have hK0 : 0 ≤ thirteenSixPaperK0 x := by
    unfold thirteenSixPaperK0 thirteenSixPaperN
    positivity
  have hrZ : (x.r : Int) ≤ 6 := by exact_mod_cast hr
  have hmu : 0 ≤ thirteenSixPaperMuZ x := by
    exact thirteenSix_paper_mu_nonnegative_arithmetic
      (K0 := thirteenSixPaperK0 x) (j := (x.j : Int))
      (r := (x.r : Int)) (mu := thirteenSixPaperMuZ x)
      hK0 (by exact_mod_cast Nat.zero_le x.j)
        (by exact_mod_cast Nat.zero_le x.r) hrZ hEMu
  have hB0 : thirteenSixPaperB0 x ≤ 0 := by
    unfold thirteenSixPaperB0
    exact sub_nonpos.mpr rows.budget
  have hB1 : thirteenSixPaperB1 x ≤ 0 := by
    have hid := thirteenSix_paper_B01_identity x
    rw [hF0] at hid
    linarith only [hB0, hid]
  have hQ :
      thirteenSixPaperQ0 x + 4 * thirteenSixPaperMuZ x - 2 * x.j ≤
        3 + 2 * x.r := by
    have hid := thirteenSix_paper_B1mu_identity x
    rw [hEMu] at hid
    linarith only [hB1, hid]
  have hL : 0 ≤ thirteenSixPaperL x := by
    unfold thirteenSixPaperL
    linarith only [hQ]
  have hSrow := thirteenSix_paper_S_identity x hF0
  have hS : 0 ≤ thirteenSixPaperS x := by
    rw [hSrow]
    positivity
  have hdeltaRow := thirteenSix_paper_delta_identity x
  have hdeltaLe : thirteenSixPaperDeltaZ x ≤ 2 := by
    exact thirteenSix_paper_delta_le_two_arithmetic
      (delta := thirteenSixPaperDeltaZ x) (k := (x.k : Int))
      (ell := (x.ell : Int)) (d := (x.d : Int)) (t := (x.t : Int))
      (w := (x.w : Int)) (p := (x.p : Int)) (S := thirteenSixPaperS x)
      (by exact_mod_cast Nat.zero_le x.k)
      (by exact_mod_cast Nat.zero_le x.ell)
      (by exact_mod_cast Nat.zero_le x.d)
      (by exact_mod_cast Nat.zero_le x.t)
      (by exact_mod_cast Nat.zero_le x.w)
      (by exact_mod_cast Nat.zero_le x.p) hS hdeltaRow
  have hV := thirteenSix_paper_v_identity x hEMu
  have hEJ := thirteenSix_paper_EJ_identity x rows
  have hdeltaDef :
      thirteenSixPaperDeltaZ x =
        7 * thirteenSixPaperMuZ x - 4 * (x.j : Int) := rfl
  have hJnonneg_of_rhs (hRhs : 0 ≤ thirteenSixPaperJRhs x) :
      0 ≤ x.paperJZ := by
    linarith only [hEJ, hRhs]
  by_cases hp : x.p = 0
  · have hpZ : (x.p : Int) = 0 := by exact_mod_cast hp
    by_cases hdelta0 : thirteenSixPaperDeltaZ x ≤ 0
    · apply hJnonneg_of_rhs
      apply thirteenSix_paper_J_rhs_nonnegative_of_pair
      rw [hpZ]
      have hj : 0 ≤ (x.j : Int) := by positivity
      linarith only [hj, hdelta0]
    · have hdeltaPos : 0 < thirteenSixPaperDeltaZ x := lt_of_not_ge hdelta0
      have hdeltaCases :
          thirteenSixPaperDeltaZ x = 1 ∨ thirteenSixPaperDeltaZ x = 2 := by
        exact thirteenSix_paper_positive_delta_cases_arithmetic
          hdeltaPos hdeltaLe
      rcases hdeltaCases with hdelta1 | hdelta2
      · have hj5 : (5 : Int) ≤ x.j := by
          apply thirteenSix_paper_delta_one_j_lower_arithmetic
            (mu := thirteenSixPaperMuZ x) (j := (x.j : Int))
          · positivity
          · linarith only [hdelta1, hdeltaDef]
        apply hJnonneg_of_rhs
        apply thirteenSix_paper_J_rhs_nonnegative_of_pair
        rw [hpZ, hdelta1]
        linarith only [hj5]
      · have hzeroRows :
            (x.k : Int) = 0 ∧ (x.ell : Int) = 0 ∧ (x.d : Int) = 0 ∧
              (x.t : Int) = 0 ∧ (x.w : Int) = 0 ∧
                thirteenSixPaperS x = 0 := by
          apply thirteenSix_paper_delta_two_zeros_arithmetic
          · positivity
          · positivity
          · positivity
          · positivity
          · positivity
          · exact hS
          · rw [hdelta2, hpZ] at hdeltaRow
            norm_num at hdeltaRow ⊢
            exact hdeltaRow
        rcases hzeroRows with ⟨hk, hell, hd, ht, hw, _hSzero⟩
        have hjCases : (x.j : Int) = 3 ∨ 10 ≤ (x.j : Int) := by
          apply thirteenSix_paper_delta_two_j_cases_arithmetic
            (mu := thirteenSixPaperMuZ x) (j := (x.j : Int))
          · positivity
          · linarith only [hdelta2, hdeltaDef]
        rcases hjCases with hj3 | hj10
        · have hmu2 : thirteenSixPaperMuZ x = 2 := by
            apply thirteenSix_paper_delta_two_mu_arithmetic hj3
            linarith only [hdelta2, hdeltaDef]
          let B : Int := (x.y : Int) + x.z + 4 * x.h + 12 * x.A6
          have hQspecial : B + x.u + 2 ≤ 2 * x.r := by
            unfold thirteenSixPaperQ0 thirteenSixPaperN at hQ
            rw [hj3, hmu2, hk, hell, hd, ht, hw, hpZ] at hQ
            norm_num at hQ
            change
              (x.y : Int) + x.z + 4 * x.h + 12 * x.A6 + x.u + 2 ≤
                2 * x.r
            linarith only [hQ]
          have hVspecial : (x.v : Int) + B + 2 * x.u = 4 + 2 * x.r := by
            have hVcopy := hV
            rw [hdelta2, hk, hell, hd, ht, hw] at hVcopy
            norm_num at hVcopy
            change
              (x.v : Int) +
                  ((x.y : Int) + x.z + 4 * x.h + 12 * x.A6) + 2 * x.u =
                4 + 2 * x.r
            linarith only [hVcopy]
          have huv : (6 : Int) ≤ x.u + x.v :=
            thirteenSix_paper_extreme_uv_lower_arithmetic hQspecial hVspecial
          have hRhs : 0 ≤ thirteenSixPaperJRhs x := by
            unfold thirteenSixPaperJRhs
            rw [hdelta2, hpZ, hk, hell, hd, ht, hw, hj3]
            have hrest :
                0 ≤ 49 * (x.f : Int) + 14 * (x.y + x.z) + 7 * x.y := by
              positivity
            have hu : 0 ≤ (x.u : Int) := by positivity
            linarith only [hrest, huv, hu]
          apply hJnonneg_of_rhs
          exact hRhs
        · apply hJnonneg_of_rhs
          apply thirteenSix_paper_J_rhs_nonnegative_of_pair
          rw [hpZ, hdelta2]
          linarith only [hj10]
  · have hpZ : (1 : Int) ≤ x.p := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr hp
    have hdeltaP :
        thirteenSixPaperDeltaZ x ≤ 2 - 8 * (x.p : Int) := by
      have hk : 0 ≤ (x.k : Int) := by positivity
      have hell : 0 ≤ (x.ell : Int) := by positivity
      have hd : 0 ≤ (x.d : Int) := by positivity
      have ht : 0 ≤ (x.t : Int) := by positivity
      have hw : 0 ≤ (x.w : Int) := by positivity
      linarith only [hdeltaRow, hk, hell, hd, ht, hw, hS]
    apply hJnonneg_of_rhs
    apply thirteenSix_paper_J_rhs_nonnegative_of_pair
    have hj : 0 ≤ (x.j : Int) := by positivity
    linarith only [hj, hpZ, hdeltaP]

private theorem thirteenSix_paperJ_cast
    (x : ThirteenSixTerminalSpine) (hr : x.r ≤ 6) :
    (x.paperJ : Int) = x.paperJZ := by
  unfold ThirteenSixTerminalSpine.paperJ
  exact Int.toNat_of_nonneg (thirteenSix_paperJZ_nonnegative x hr)

theorem thirteenSix_paperJ_definition
    (x : ThirteenSixTerminalSpine) (hr : x.r ≤ 6) :
    x.paperJ + 12 * x.eventCapacity =
      21 + 18 * x.r + 24 * x.A6 := by
  have hcast := thirteenSix_paperJ_cast x hr
  unfold ThirteenSixTerminalSpine.paperJZ at hcast
  unfold ThirteenSixTerminalSpine.eventCapacity
  omega

private theorem thirteenSix_capacity_gap_arithmetic
    (x : ThirteenSixTerminalSpine) (hr : x.r ≤ 6) :
    4 * x.eventCapacity ≤ 6 * x.r + 7 + 8 * x.A6 := by
  have hJ := thirteenSix_paperJ_definition x hr
  omega

theorem thirteenSixCapacityGapConditions_of_spine
    (x : ThirteenSixTerminalSpine) (repetitionEvents : Nat)
    (hr : x.r ≤ 6)
    (hrepetitionLower : thirteenSixRho x.r ≤ repetitionEvents)
    (hrepetitionHost : repetitionEvents ≤ x.eventCapacity)
    (hA6 : x.A6 = 0) :
    ThirteenSixCapacityGapConditions (x.capacityData repetitionEvents) := by
  constructor
  · exact hr
  · exact hrepetitionLower
  · exact hrepetitionHost
  · exact thirteenSix_capacity_gap_arithmetic x hr
  · exact hA6
  · rfl
  · exact x.secondBudget

private theorem thirteenSix_terminal_E_cases_arithmetic
    {r repetitionEvents E A6 : Nat}
    (hr : r = 2 ∨ r = 3) (hA6 : A6 = 0)
    (hlower : thirteenSixRho r ≤ repetitionEvents)
    (hhost : repetitionEvents ≤ E)
    (hcap : 4 * E ≤ 6 * r + 7 + 8 * A6) :
    (r = 2 ∧ E = 4) ∨ (r = 3 ∧ E = 6) := by
  rcases hr with hr2 | hr3
  · left
    refine ⟨hr2, ?_⟩
    subst r
    norm_num [thirteenSixRho] at hlower
    omega
  · right
    refine ⟨hr3, ?_⟩
    subst r
    norm_num [thirteenSixRho] at hlower
    omega

private theorem thirteenSix_terminal_forced_zeros_arithmetic
    {r E h k A6 ell g y z f w t p u v d : Nat}
    (hcases : (r = 2 ∧ E = 4) ∨ (r = 3 ∧ E = 6))
    (hA6 : A6 = 0)
    (hE : E = 2 * h + 3 * k + 9 * A6 + 2 * ell + 2 * g)
    (hbudget :
      12 * h + 26 * k + 36 * A6 + 3 * y + 5 * z + 2 * f +
        40 * ell + 31 * w + 22 * t + 48 * p + 6 * u + 3 * v + 36 * d ≤
          12 + 6 * r) :
    k = 0 ∧ ell = 0 ∧ d = 0 ∧ w = 0 ∧ p = 0 := by
  rcases hcases with ⟨hr, hEvalue⟩ | ⟨hr, hEvalue⟩ <;> omega

def thirteenSixTerminalMuZ (x : ThirteenSixTerminalSpine) : Int :=
  x.f - (2 * (x.j : Int) + x.y - x.v + 4 * x.h - 5 * x.t - 2 * x.r)

private theorem thirteenSix_terminal_mu_multiple_arithmetic
    (x : ThirteenSixTerminalSpine)
    (hk : x.k = 0) (hA6 : x.A6 = 0) (hell : x.ell = 0)
    (hd : x.d = 0) (hw : x.w = 0) (hp : x.p = 0) :
    8 * (x.j : Int) + x.y + x.z + 2 * x.u + x.v + 4 * x.h +
        4 * x.t - 2 * x.r =
      14 * thirteenSixTerminalMuZ x := by
  have hC := x.circleRow
  have hO := x.ordinaryRow
  have h0 := x.row0
  have h1 := x.row1
  have h2 := x.row2
  have hW := x.weightRow
  have hX := x.momentXRow
  have hG := x.momentGammaRow
  have hCs := x.circleSlack
  have hOs := x.ordinarySlack
  have hWs := x.weightSlack
  unfold thirteenSixTerminalMuZ
  omega

private theorem thirteenSix_terminal_mu_nonnegative_arithmetic
    {r j y z u v h t : Nat} {muZ : Int}
    (hr : r = 2 ∨ r = 3)
    (hmultiple :
      8 * (j : Int) + y + z + 2 * u + v + 4 * h + 4 * t - 2 * r =
        14 * muZ) :
    0 ≤ muZ := by
  rcases hr with hr2 | hr3 <;> omega

def thirteenSixTerminalDeltaZ
    (x : ThirteenSixTerminalSpine) (mu : Nat) : Int :=
  7 * (mu : Int) - 4 * x.j

private theorem thirteenSix_terminal_delta_upper_arithmetic
    (x : ThirteenSixTerminalSpine) (mu : Nat)
    (hr : x.r = 2 ∨ x.r = 3)
    (hk : x.k = 0) (hA6 : x.A6 = 0) (hell : x.ell = 0)
    (hd : x.d = 0) (hw : x.w = 0) (hp : x.p = 0)
    (hmultiple :
      8 * (x.j : Int) + x.y + x.z + 2 * x.u + x.v + 4 * x.h +
          4 * x.t - 2 * x.r = 14 * (mu : Int)) :
    thirteenSixTerminalDeltaZ x mu ≤ 2 := by
  have hbudget := x.secondBudget
  unfold thirteenSixTerminalDeltaZ
  rcases hr with hr2 | hr3 <;> omega

private theorem thirteenSix_terminal_v_row_signed
    (x : ThirteenSixTerminalSpine) (mu : Nat)
    (hk : x.k = 0) (hA6 : x.A6 = 0) (hell : x.ell = 0)
    (hd : x.d = 0) (hw : x.w = 0) (hp : x.p = 0)
    (hmu : (mu : Int) = thirteenSixTerminalMuZ x) :
    (x.v : Int) + x.y + x.z + 2 * x.u + 4 * x.h + 4 * x.t =
      2 * thirteenSixTerminalDeltaZ x mu + 2 * x.r := by
  have hC := x.circleRow
  have hO := x.ordinaryRow
  have h0 := x.row0
  have h1 := x.row1
  have h2 := x.row2
  have hW := x.weightRow
  have hX := x.momentXRow
  have hG := x.momentGammaRow
  have hCs := x.circleSlack
  have hOs := x.ordinarySlack
  have hWs := x.weightSlack
  unfold thirteenSixTerminalMuZ at hmu
  unfold thirteenSixTerminalDeltaZ
  omega

private theorem thirteenSix_terminal_f_row
    (x : ThirteenSixTerminalSpine) (mu : Nat)
    (hmu : (mu : Int) = thirteenSixTerminalMuZ x) :
    x.f + x.v + 5 * x.t + 2 * x.r =
      2 * x.j + mu + x.y + 4 * x.h := by
  have hC := x.circleRow
  have hO := x.ordinaryRow
  have h0 := x.row0
  have h1 := x.row1
  have h2 := x.row2
  have hW := x.weightRow
  have hX := x.momentXRow
  have hG := x.momentGammaRow
  have hCs := x.circleSlack
  have hOs := x.ordinarySlack
  have hWs := x.weightSlack
  unfold thirteenSixTerminalMuZ at hmu
  omega

private theorem thirteenSix_terminal_budget_row
    (x : ThirteenSixTerminalSpine) (mu : Nat)
    (hcases :
      (x.r = 2 ∧ x.eventCapacity = 4) ∨
      (x.r = 3 ∧ x.eventCapacity = 6))
    (hk : x.k = 0) (hA6 : x.A6 = 0) (hell : x.ell = 0)
    (hd : x.d = 0) (hw : x.w = 0) (hp : x.p = 0)
    (hmu : (mu : Int) = thirteenSixTerminalMuZ x) :
    x.y + x.z + x.u + 4 * x.h + 2 * x.t + 4 * mu ≤
      3 + 2 * x.r + x.j := by
  have hC := x.circleRow
  have hO := x.ordinaryRow
  have h0 := x.row0
  have h1 := x.row1
  have h2 := x.row2
  have hW := x.weightRow
  have hX := x.momentXRow
  have hG := x.momentGammaRow
  have hCs := x.circleSlack
  have hOs := x.ordinarySlack
  have hWs := x.weightSlack
  have hbudget := x.secondBudget
  unfold ThirteenSixTerminalSpine.eventCapacity at hcases
  unfold thirteenSixTerminalMuZ at hmu
  rcases hcases with hcase | hcase <;> omega

private theorem thirteenSix_terminal_J_row
    (x : ThirteenSixTerminalSpine) (mu : Nat)
    (hr : x.r ≤ 6)
    (hk : x.k = 0) (hA6 : x.A6 = 0) (hell : x.ell = 0)
    (hd : x.d = 0) (hw : x.w = 0) (hp : x.p = 0)
    (hmu : (mu : Int) = thirteenSixTerminalMuZ x) :
    x.paperJ + 123 * mu + 24 * x.r + 9 * x.t =
      7 * (x.y + x.z) + 48 * x.h + 90 * x.j + 19 * x.u + 8 * x.y := by
  have hC := x.circleRow
  have hO := x.ordinaryRow
  have h0 := x.row0
  have h1 := x.row1
  have h2 := x.row2
  have hW := x.weightRow
  have hX := x.momentXRow
  have hG := x.momentGammaRow
  have hCs := x.circleSlack
  have hOs := x.ordinarySlack
  have hWs := x.weightSlack
  have hJdef := thirteenSix_paperJ_definition x hr
  unfold ThirteenSixTerminalSpine.eventCapacity at hJdef
  unfold thirteenSixTerminalMuZ at hmu
  omega

private theorem thirteenSix_terminal_J_cases_arithmetic
    {r E A6 J : Nat}
    (hcases : (r = 2 ∧ E = 4) ∨ (r = 3 ∧ E = 6))
    (hA6 : A6 = 0)
    (hJ : J + 12 * E = 21 + 18 * r + 24 * A6) :
    (r = 2 ∧ J = 9) ∨ (r = 3 ∧ J = 3) := by
  rcases hcases with hcase | hcase <;> omega

private theorem thirteenSix_terminal_delta_nonnegative_arithmetic
    {r J mu j y z u v h t f : Nat} {deltaZ : Int}
    (hcases : (r = 2 ∧ J = 9) ∨ (r = 3 ∧ J = 3))
    (hdelta : deltaZ = 7 * (mu : Int) - 4 * j)
    (hv :
      (v : Int) + y + z + 2 * u + 4 * h + 4 * t =
        2 * deltaZ + 2 * r)
    (hf : f + v + 5 * t + 2 * r = 2 * j + mu + y + 4 * h)
    (hbudget : y + z + u + 4 * h + 2 * t + 4 * mu ≤ 3 + 2 * r + j)
    (hJ :
      J + 123 * mu + 24 * r + 9 * t =
        7 * (y + z) + 48 * h + 90 * j + 19 * u + 8 * y) :
    0 ≤ deltaZ := by
  rcases hcases with hcase | hcase <;> omega

private theorem thirteenSix_terminal_delta_row_arithmetic
    {delta j mu : Nat} {deltaZ : Int}
    (hcast : (delta : Int) = deltaZ)
    (hdef : deltaZ = 7 * (mu : Int) - 4 * j) :
    delta + 4 * j = 7 * mu := by
  omega

private theorem thirteenSix_terminal_v_row_arithmetic
    {r delta y z u v h t : Nat} {deltaZ : Int}
    (hcast : (delta : Int) = deltaZ)
    (hv :
      (v : Int) + y + z + 2 * u + 4 * h + 4 * t =
        2 * deltaZ + 2 * r) :
    v + (y + z) + 2 * u + 4 * h + 4 * t = 2 * delta + 2 * r := by
  omega

theorem thirteenSixTerminalConditions_of_spine
    (x : ThirteenSixTerminalSpine) (repetitionEvents : Nat)
    (gapRows : ThirteenSixCapacityGapConditions (x.capacityData repetitionEvents))
    (hr : x.r = 2 ∨ x.r = 3) :
    ∃ terminal : ThirteenSixTerminalData,
      ThirteenSixTerminalConditions x.r x.paperJ terminal := by
  have hEcases := thirteenSix_terminal_E_cases_arithmetic hr
    gapRows.A6_eq_zero gapRows.repetition_lower
      gapRows.repetition_host_capacity gapRows.capacityGap
  have hzeros := thirteenSix_terminal_forced_zeros_arithmetic
    hEcases gapRows.A6_eq_zero gapRows.E_definition gapRows.secondBudget
  rcases hzeros with ⟨hk, hell, hd, hw, hp⟩
  have hmuMultiple := thirteenSix_terminal_mu_multiple_arithmetic
    x hk gapRows.A6_eq_zero hell hd hw hp
  have hmuNonneg := thirteenSix_terminal_mu_nonnegative_arithmetic
    hr hmuMultiple
  let mu := Int.toNat (thirteenSixTerminalMuZ x)
  have hmuCast : (mu : Int) = thirteenSixTerminalMuZ x := by
    exact Int.toNat_of_nonneg hmuNonneg
  have hmuMultipleNat :
      8 * (x.j : Int) + x.y + x.z + 2 * x.u + x.v + 4 * x.h +
          4 * x.t - 2 * x.r = 14 * (mu : Int) := by
    rw [hmuCast]
    exact hmuMultiple
  have hdeltaUpper := thirteenSix_terminal_delta_upper_arithmetic
    x mu hr hk gapRows.A6_eq_zero hell hd hw hp hmuMultipleNat
  have hvSigned := thirteenSix_terminal_v_row_signed
    x mu hk gapRows.A6_eq_zero hell hd hw hp hmuCast
  have hfRow := thirteenSix_terminal_f_row
    x mu hmuCast
  have hbudgetRow := thirteenSix_terminal_budget_row
    x mu hEcases hk gapRows.A6_eq_zero hell hd hw hp hmuCast
  have hJrow := thirteenSix_terminal_J_row
    x mu gapRows.r_le_six hk gapRows.A6_eq_zero hell hd hw hp hmuCast
  have hJcases := thirteenSix_terminal_J_cases_arithmetic
    hEcases gapRows.A6_eq_zero
      (thirteenSix_paperJ_definition x gapRows.r_le_six)
  have hdeltaNonneg := thirteenSix_terminal_delta_nonnegative_arithmetic
    hJcases rfl hvSigned hfRow hbudgetRow hJrow
  let delta := Int.toNat (thirteenSixTerminalDeltaZ x mu)
  have hdeltaCast : (delta : Int) = thirteenSixTerminalDeltaZ x mu := by
    exact Int.toNat_of_nonneg hdeltaNonneg
  have hdeltaLe : delta ≤ 2 := by
    rw [← hdeltaCast] at hdeltaUpper
    exact_mod_cast hdeltaUpper
  have hdeltaRow : delta + 4 * x.j = 7 * mu := by
    apply thirteenSix_terminal_delta_row_arithmetic hdeltaCast
    rfl
  have hvRow :
      x.v + (x.y + x.z) + 2 * x.u + 4 * x.h + 4 * x.t =
        2 * delta + 2 * x.r :=
    thirteenSix_terminal_v_row_arithmetic hdeltaCast hvSigned
  let terminal : ThirteenSixTerminalData :=
    { delta := delta
      j := x.j
      mu := mu
      a := x.y + x.z
      y := x.y
      u := x.u
      v := x.v
      h := x.h
      t := x.t
      f := x.f }
  refine ⟨terminal, ?_⟩
  exact
    { delta_le_two := by simpa only [terminal] using hdeltaLe
      y_le_a := by simp [terminal]
      delta_row := by simpa only [terminal] using hdeltaRow
      v_row := by simpa only [terminal] using hvRow
      f_row := by simpa only [terminal] using hfRow
      budget := by simpa only [terminal] using hbudgetRow
      J_row := by simpa only [terminal] using hJrow }

private theorem thirteenSix_paperJ_definition_of_A6_zero
    (x : ThirteenSixTerminalSpine) (hr : x.r ≤ 6) (hA6 : x.A6 = 0) :
    x.paperJ + 12 * x.eventCapacity = 21 + 18 * x.r := by
  have hJ := thirteenSix_paperJ_definition x hr
  omega

theorem thirteenSixTerminalSpine_arithmetic_impossible
    (x : ThirteenSixTerminalSpine) (repetitionEvents : Nat)
    (hr : x.r ≤ 6)
    (hrepetitionLower : thirteenSixRho x.r ≤ repetitionEvents)
    (hrepetitionHost : repetitionEvents ≤ x.eventCapacity)
    (hA6 : x.A6 = 0) : False := by
  let gap := x.capacityData repetitionEvents
  have gapRows : ThirteenSixCapacityGapConditions gap := by
    exact thirteenSixCapacityGapConditions_of_spine
      x repetitionEvents hr hrepetitionLower hrepetitionHost hA6
  have hr23 := thirteenSix_capacity_gap_leaves_two_or_three gap gapRows
  obtain ⟨terminal, terminalRows⟩ :=
    thirteenSixTerminalConditions_of_spine x repetitionEvents gapRows hr23
  apply thirteenSix_full_arithmetic_impossible
  exact
    { gap := gap
      gapRows := gapRows
      J := x.paperJ
      J_definition := thirteenSix_paperJ_definition_of_A6_zero x hr hA6
      terminal := terminal
      terminalRows := fun _hr => terminalRows }

theorem thirteenSix_materialized_arithmetic_impossible
    (S : BlockSystem Point Block) (D : Finset Point)
    {C C3 W u v d r j repetitionEvents : Nat}
    (rows : ThirteenSixAffineRows S D C C3 W u v d r j)
    (hr : r ≤ 6)
    (hrepetitionLower : thirteenSixRho r ≤ repetitionEvents)
    (hrepetitionHost : repetitionEvents ≤ thirteenSixEventCapacitySum S D)
    (hA6 : thirteenSixRelativeCount S D .circle 0 6 = 0)
    (hbudget :
      12 * thirteenSixRelativeCount S D .circle 0 4 +
        26 * thirteenSixRelativeCount S D .circle 0 5 +
        36 * thirteenSixRelativeCount S D .circle 0 6 +
        3 * thirteenSixRelativeCount S D .circle 1 3 +
        5 * thirteenSixRelativeCount S D .circle 1 4 +
        2 * thirteenSixRelativeCount S D .circle 2 3 +
        40 * thirteenSixRelativeCount S D .line 0 4 +
        31 * thirteenSixRelativeCount S D .line 1 3 +
        22 * thirteenSixRelativeCount S D .line 2 2 +
        48 * thirteenSixRelativeCount S D .line 2 3 +
        6 * u + 3 * v + 36 * d ≤ 12 + 6 * r) : False := by
  let x := thirteenSixTerminalSpineOfBlockSystem S D rows hbudget
  apply thirteenSixTerminalSpine_arithmetic_impossible x repetitionEvents
  · change r ≤ 6
    exact hr
  · change thirteenSixRho r ≤ repetitionEvents
    exact hrepetitionLower
  · change repetitionEvents ≤ thirteenSixEventCapacitySum S D
    exact hrepetitionHost
  · change thirteenSixRelativeCount S D .circle 0 6 = 0
    exact hA6

end TerminalSpine

end Erdos506.V1
