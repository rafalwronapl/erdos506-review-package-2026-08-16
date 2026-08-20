import Mathlib.Tactic

/-!
# Arithmetic front for the eleven-point selected-six-circle branch

This file checks the part of the manuscript's `n = 11`, `Gamma_6` argument
which does not use the sharp six-conic event bounds.  It is deliberately an
arithmetic interface: the entries below are the nonnegative slacks and block
counts occurring in equations F1 and F2 of `02_finite_n10_n12.tex`.

The first identity is F1 multiplied by ten and the second is F2 multiplied
by twenty-four.  In footprint B, the three additional equalities are exactly
the `C = 38` boundary reduction printed after F2.  Thus there are no rational
coefficients and no appeal to an external solver certificate.

The result is the honest common front `C >= 39`.  It does **not** assert the
final `C >= 41`: excluding `C = 39, 40` needs the manuscript's sharper
six-conic bounds `W <= 26`, `W <= 20`, `J <= 14`, and localized `J <= 13`,
which are intentionally absent from the current U17-only principle.
-/

namespace Erdos506.V1

/-- Natural-number data used by the cleared F1/F2 certificates.

All fields are counts or nonnegative slacks.  The names follow the paper;
for example, `c12` counts circle blocks of relative type `(1,2)`, while
`l23` counts line blocks of relative type `(2,3)`.
-/
structure ElevenGammaSixFrontData where
  C : Nat
  N3 : Nat
  N4 : Nat
  N5 : Nat
  sigma6 : Nat
  sigma10 : Nat
  sigma17 : Nat
  sigma63 : Nat
  sigmaL : Nat
  c04 : Nat
  c12 : Nat
  c13 : Nat
  c14 : Nat
  c24 : Nat
  l03 : Nat
  l04 : Nat
  l05 : Nat
  l12 : Nat
  l13 : Nat
  l14 : Nat
  l15 : Nat
  l22 : Nat
  l23 : Nat
  l24 : Nat

/-- The three possible partitions of the ten outsider triples.

They are called footprints A, B, and C in the manuscript.
-/
def ElevenGammaSixFootprintProfile
    (N3 N4 N5 : Nat) : Prop :=
  (N3 = 10 /\ N4 = 0 /\ N5 = 0) \/
  (N3 = 6 /\ N4 = 1 /\ N5 = 0) \/
  (N3 = 0 /\ N4 = 0 /\ N5 = 1)

/-- The exact cleared rows needed for the common `C >= 39` front.

`f1` is ten times equation F1.  In footprint C, `f2_of_profileC` is
twenty-four times equation F2.  The last field records the exact integral
boundary rows which eliminate the sole value `C = 38` left by F1 in
footprint B.
-/
structure ElevenGammaSixFrontConditions
    (d : ElevenGammaSixFrontData) : Prop where
  footprint_row : d.N3 + 4 * d.N4 + 10 * d.N5 = 10
  N4_le_one : d.N4 <= 1
  N5_le_one : d.N5 <= 1
  f1 :
    10 * d.C =
      320 + 9 * d.N3 + 6 * d.N4 +
        5 * d.sigma6 + 10 * d.sigma63 + 10 * d.sigmaL +
        10 * d.c12 + 20 * d.c24 +
        10 * d.l04 + 10 * d.l05 + 10 * d.l12 +
        15 * d.l13 + 30 * d.l14 + 35 * d.l15 + 10 * d.l24
  f2_of_profileC : d.N5 = 1 ->
    24 * d.C =
      934 + 3 * d.sigma6 + 12 * d.sigma10 + 2 * d.sigma17 +
        48 * d.c04 + 36 * d.c13 + 48 * d.c14 +
        18 * d.l03 + 38 * d.l04 + 12 * d.l12 +
        35 * d.l13 + 60 * d.l14 + 27 * d.l15 +
        2 * d.l22 + 18 * d.l23 + 36 * d.l24
  footprintB_at_thirty_eight :
    d.C = 38 -> d.N3 = 6 -> d.N4 = 1 -> d.N5 = 0 ->
      3 * d.c13 + 6 * d.c14 + 2 * d.l22 + 6 * d.l23 = 4 /\
      d.sigma10 + 3 * d.c13 = 1 /\
      d.sigma17 + d.l22 = 1

/-- The outsider-triple row and the two elementary footprint caps leave
exactly the manuscript's three profiles. -/
theorem elevenGammaSix_footprint_profiles
    (N3 N4 N5 : Nat)
    (hrow : N3 + 4 * N4 + 10 * N5 = 10)
    (hN4 : N4 <= 1) (hN5 : N5 <= 1) :
    ElevenGammaSixFootprintProfile N3 N4 N5 := by
  unfold ElevenGammaSixFootprintProfile
  interval_cases N5 <;> interval_cases N4 <;> omega

/-- F1 alone gives the stronger lower bound in footprint A. -/
theorem elevenGammaSix_profileA_circleCount_ge_forty_one
    (d : ElevenGammaSixFrontData)
    (hF1 :
      10 * d.C =
        320 + 9 * d.N3 + 6 * d.N4 +
          5 * d.sigma6 + 10 * d.sigma63 + 10 * d.sigmaL +
          10 * d.c12 + 20 * d.c24 +
          10 * d.l04 + 10 * d.l05 + 10 * d.l12 +
          15 * d.l13 + 30 * d.l14 + 35 * d.l15 + 10 * d.l24)
    (hN3 : d.N3 = 10) (hN4 : d.N4 = 0) :
    41 <= d.C := by
  omega

/-- F2 gives the integral lower bound in footprint C. -/
theorem elevenGammaSix_profileC_circleCount_ge_thirty_nine
    (d : ElevenGammaSixFrontData)
    (hF2 :
      24 * d.C =
        934 + 3 * d.sigma6 + 12 * d.sigma10 + 2 * d.sigma17 +
          48 * d.c04 + 36 * d.c13 + 48 * d.c14 +
          18 * d.l03 + 38 * d.l04 + 12 * d.l12 +
          35 * d.l13 + 60 * d.l14 + 27 * d.l15 +
          2 * d.l22 + 18 * d.l23 + 36 * d.l24) :
    39 <= d.C := by
  omega

/-- F1 gives `C >= 38` in footprint B, and the exact equality rows at
`C = 38` are arithmetically inconsistent. -/
theorem elevenGammaSix_profileB_circleCount_ge_thirty_nine
    (d : ElevenGammaSixFrontData)
    (hF1 :
      10 * d.C =
        320 + 9 * d.N3 + 6 * d.N4 +
          5 * d.sigma6 + 10 * d.sigma63 + 10 * d.sigmaL +
          10 * d.c12 + 20 * d.c24 +
          10 * d.l04 + 10 * d.l05 + 10 * d.l12 +
          15 * d.l13 + 30 * d.l14 + 35 * d.l15 + 10 * d.l24)
    (hN3 : d.N3 = 6) (hN4 : d.N4 = 1)
    (hboundary : d.C = 38 ->
      3 * d.c13 + 6 * d.c14 + 2 * d.l22 + 6 * d.l23 = 4 /\
      d.sigma10 + 3 * d.c13 = 1 /\
      d.sigma17 + d.l22 = 1) :
    39 <= d.C := by
  have hCge : 38 <= d.C := by omega
  by_contra hnot
  have hC : d.C = 38 := by omega
  obtain ⟨hresidue, hsigma10, hsigma17⟩ := hboundary hC
  omega

/-- The common arithmetic front of the eleven-point selected-six-circle
branch: every one of the three outsider-footprint profiles has `C >= 39`.

This theorem closes all of the low-count part of the branch without using
the stronger six-conic event inequalities needed at `C = 39, 40`.
-/
theorem elevenGammaSix_front_circleCount_ge_thirty_nine
    (d : ElevenGammaSixFrontData)
    (h : ElevenGammaSixFrontConditions d) :
    39 <= d.C := by
  have hprofile := elevenGammaSix_footprint_profiles
    d.N3 d.N4 d.N5 h.footprint_row h.N4_le_one h.N5_le_one
  rcases hprofile with hA | hB | hC
  · rcases hA with ⟨hN3, hN4, _hN5⟩
    have hfortyOne :=
      elevenGammaSix_profileA_circleCount_ge_forty_one d h.f1 hN3 hN4
    omega
  · rcases hB with ⟨hN3, hN4, hN5⟩
    apply elevenGammaSix_profileB_circleCount_ge_thirty_nine
      d h.f1 hN3 hN4
    intro hcount
    exact h.footprintB_at_thirty_eight hcount hN3 hN4 hN5
  · rcases hC with ⟨_hN3, _hN4, hN5⟩
    exact elevenGammaSix_profileC_circleCount_ge_thirty_nine
      d (h.f2_of_profileC hN5)

end Erdos506.V1
