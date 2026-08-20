import Erdos506.V1.TwelveGridIncidenceExtraction
import Erdos506.Finite.SixFourIncidenceMoments

/-!
# Moment saturation for the twelve-point grid entrance

This module applies the geometry-free `6`-by-`4` incidence wall to the six
four-lines extracted after pivot inversion.  In particular, the incidence
graph no longer has an unresolved intersection case: every pair of the six
lines meets once, and their eleven selected labels have degree profile
`3,3,2^9`.
-/

namespace Erdos506.V1

open Erdos506.Block
open Erdos506.Block.BlockSystem
open Erdos506.Finite
open Erdos506.Incidence
open Erdos506.V3
open Erdos506.V4

open scoped BigOperators

universe u

/-- The finite six-four moment hypotheses are supplied by the actual
four-line supports in the inverted census. -/
theorem TwelveGridInvertedLineCensus.isSaturatedSixFour
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (hcard : Fintype.card Point = 12)
    (H : TwelveGridInvertedLineCensus cfg p) :
    IsSaturatedSixFour
      (fun i => lineSupport (pivotInversion cfg p) (H.fourLine i).1) where
  point_card := by
    rw [Erdos506.V3.card_awayFrom, hcard]
  base_card := H.fourLine_support_card
  pair_inter_le_one := by
    intro i j hij
    have hinter := H.fourLine_support_inter_lt_two hij
    omega

/-- Every pair among the six actual inverted four-lines has one selected
intersection. -/
theorem TwelveGridInvertedLineCensus.fourLine_support_inter_eq_one
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (hcard : Fintype.card Point = 12)
    (H : TwelveGridInvertedLineCensus cfg p) {i j : Fin 6} (hij : i ≠ j) :
    (lineSupport (pivotInversion cfg p) (H.fourLine i).1 ∩
      lineSupport (pivotInversion cfg p) (H.fourLine j).1).card = 1 := by
  exact sixFour_pair_inter_eq_one (H.isSaturatedSixFour hcard) i j hij

/-- The six actual four-line supports have the forced `3,3,2^9` incidence
profile on the eleven inverted labels. -/
theorem TwelveGridInvertedLineCensus.fourLine_degree_profile
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (hcard : Fintype.card Point = 12)
    (H : TwelveGridInvertedLineCensus cfg p) :
    (sixFourDegreeThree
      (fun i => lineSupport (pivotInversion cfg p) (H.fourLine i).1)).card = 2 ∧
      (sixFourDegreeTwo
        (fun i => lineSupport (pivotInversion cfg p) (H.fourLine i).1)).card = 9 ∧
      ∀ x : AwayFrom p,
        sixFourDegree
          (fun i => lineSupport (pivotInversion cfg p) (H.fourLine i).1) x = 2 ∨
          sixFourDegree
            (fun i => lineSupport (pivotInversion cfg p) (H.fourLine i).1) x = 3 :=
  sixFour_degree_profile (H.isSaturatedSixFour hcard)

/-- The corresponding first and second moments of the actual support family. -/
theorem TwelveGridInvertedLineCensus.fourLine_moments
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (hcard : Fintype.card Point = 12)
    (H : TwelveGridInvertedLineCensus cfg p) :
    (∑ x : AwayFrom p,
      sixFourDegree
        (fun i => lineSupport (pivotInversion cfg p) (H.fourLine i).1) x) = 24 ∧
      (∑ x : AwayFrom p,
        (sixFourDegree
          (fun i => lineSupport (pivotInversion cfg p) (H.fourLine i).1) x) ^ 2) = 54 ∧
      (∑ x : AwayFrom p,
        Nat.choose
          (sixFourDegree
            (fun i => lineSupport (pivotInversion cfg p) (H.fourLine i).1) x) 2) = 15 := by
  refine ⟨sixFour_degree_sum_eq_twenty_four (H.isSaturatedSixFour hcard),
    sixFour_square_degree_sum_eq_fifty_four (H.isSaturatedSixFour hcard),
    sixFour_choose_degree_sum_eq_fifteen (H.isSaturatedSixFour hcard)⟩

end Erdos506.V1
