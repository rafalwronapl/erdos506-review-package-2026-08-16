import Mathlib.Tactic

/-!
# Low-ordinary arithmetic for the eleven-point selected-six branch

This module isolates four small Presburger certificates used by the
geometric selected-six proof.  It deliberately imports no configuration or
incidence geometry.
-/

namespace Erdos506.V1

/-- The outsider-triple row and the four-footprint cap leave exactly the
three manuscript profiles. -/
theorem elevenGammaSix_lowOrdinary_footprint_trichotomy
    (N3 N4 N5 : Nat)
    (hF : N3 + 4 * N4 + 10 * N5 = 10)
    (h4 : N4 <= 1) (h5 : N5 <= 1) :
    (N3 = 10 /\ N4 = 0 /\ N5 = 0) \/
      (N3 = 6 /\ N4 = 1 /\ N5 = 0) \/
      (N3 = 0 /\ N4 = 0 /\ N5 = 1) := by
  omega

/-- The ten-three-footprint profile is incompatible with the low ordinary
row and the line-capacity rows. -/
theorem elevenGammaSix_lowOrdinary_n3_ten_impossible
    (c03 c12 c13 c21 c22 c23 l03 l12 l13 l21 l22 l23 : Nat)
    (hN3 : c03 + l03 + c13 + l13 + c23 + l23 = 10)
    (hT1 :
      c12 + l12 + 3 * (c13 + l13) + 2 * (c22 + l22) +
        6 * (c23 + l23) = 60)
    (hT2 :
      c21 + l21 + 2 * (c22 + l22) + 3 * (c23 + l23) = 75)
    (hLC : 2 * l12 + 3 * l13 + 2 * l21 + 4 * l22 + 6 * l23 <= 30)
    (hO : 3 * c03 + 2 * c12 + c21 <= 14)
    (hLarge : l03 + l13 + l23 <= 2) : False := by
  omega

/-- In the six-three/one-four profile, the circle census, the sharp weight
bound, and `J <= 14` are already contradictory. -/
theorem elevenGammaSix_lowOrdinary_n3_six_n4_one_impossible
    (A c12 c21 c22 c23 c24 J : Nat)
    (hA : 5 <= A)
    (hC : A + c12 + c21 + c22 <= 39)
    (hT2 : c21 + 2 * c22 + 3 * c23 + 4 * c24 + J = 75)
    (hW : c22 + 3 * c23 + 6 * c24 <= 26)
    (hJ : J <= 14) : False := by
  omega

/-- Once the size-three and size-four relative fibres vanish, the four
possible owners of the unique five-footprint reduce to two exact endpoints. -/
theorem elevenGammaSix_lowOrdinary_unique_five_endpoint
    (C c05 c12 c15 c21 c22 l05 l12 l15 l21 l22 : Nat)
    (hC : C <= 40)
    (hCircle : C = 1 + c05 + c12 + c15 + c21 + c22)
    (hN5 : c05 + l05 + c15 + l15 = 1)
    (hT1 : c12 + l12 + 10 * (c15 + l15) + 2 * (c22 + l22) = 60)
    (hT2 : c21 + l21 + 2 * (c22 + l22) = 75)
    (hLC : 2 * l12 + 5 * l15 + 2 * l21 + 4 * l22 <= 30)
    (hO : 2 * c12 + c21 <= 14)
    (hMel : 12 * l05 + 3 * l12 + 18 * l15 + 3 * l21 + 7 * l22 <= 52)
    (hK : 25 <= 2 * c12 + 2 * l12 + c21 + l21)
    (hJ : l21 + 2 * l22 <= 14)
    (hc15 : c15 = 1 -> c22 <= 20)
    (hl05 : l05 = 1 -> c22 <= 26)
    (hc05 : c05 = 1 -> c22 <= 26) :
    (l15 = 1 /\ c05 = 0 /\ c15 = 0 /\ l05 = 0 /\ C = 40 /\
        2 * c12 + c21 = 14 /\
        2 * c12 + 2 * l12 + c21 + l21 = 25 /\
        c22 = 25 /\ l21 + 2 * l22 = 11) \/
      (c05 = 1 /\ c15 = 0 /\ l05 = 0 /\ l15 = 0 /\ C = 40 /\
        2 * c12 + 2 * l12 + c21 + l21 = 27 /\ c22 = 26 /\
        11 <= l21 + 2 * l22 /\ l21 + 2 * l22 <= 13) := by
  have hcases : c05 = 1 \/ l05 = 1 \/ c15 = 1 \/ l15 = 1 := by
    omega
  rcases hcases with hc05one | hl05one | hc15one | hl15one
  · have hweight := hc05 hc05one
    right
    omega
  · have hweight := hl05 hl05one
    omega
  · have hweight := hc15 hc15one
    omega
  · left
    omega

end Erdos506.V1
