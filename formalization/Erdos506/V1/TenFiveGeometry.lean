import Erdos506.V1.TenFive
import Erdos506.V3.SixFivePower

/-!
# Geometric certificates for the ten-point five-block branch

`TenFive` deliberately stops at five named geometric kernels.  This module
refines those kernels into the positive incidence and coordinate data that
occur in the manuscript.  In particular, none of the interfaces below has a
`False` field or accepts the desired circle-count conclusion as a premise.

The algebraic contradictions are closed here.  What remains to be supplied
by real-plane geometry is exactly the following list.

* In the equality case of the five-block packing bound, invert the canonical
  six-by-five generalized-block design and produce its six power equations.
* For five blocks, produce the punctured-pentagon pivot and its transversal
  cap `d4 <= 2`.
* For four blocks, carry the finite normalization and the side-coordinate
  construction as far as the three displayed polynomial equations.
* At the three-block rich-line endpoint, carry the exceptional local profile
  through the real nine-point link lemma, producing four disjoint matching
  edges inside two triangles.
* At the two-block endpoint, distinguish the meeting case (the same local
  link certificate) from the disjoint case and produce the golden-wall
  coordinate/determinant certificate.

Thus `RealPlaneTenFiveReductionPrinciple.toGeometry` is a configuration-level
constructor for `RealPlaneTenFiveGeometry`, while keeping every still-missing
geometric bridge visible and independently replaceable.
-/

namespace Erdos506.V1

open Erdos506.Block
open Erdos506.Block.BlockSystem
open Erdos506.Finite
open Erdos506.Incidence
open Erdos506.V3
open Erdos506.V4

universe u

/-! ## Algebraic certificates -/

/-- The six directed power-of-a-point equations obtained after inversion of
the canonical six-by-five design.  These are the variables and nonvanishing
conditions of the manuscript, not an encoded endpoint. -/
structure SixFivePowerData where
  a2 : Real
  b2 : Real
  c2 : Real
  x : Real
  y : Real
  u : Real
  v : Real
  w : Real
  z : Real
  a2_ne_zero : a2 ≠ 0
  b2_ne_zero : b2 ≠ 0
  c2_ne_zero : c2 ≠ 0
  v_ne_zero : v ≠ 0
  z_ne_zero : z ≠ 0
  u_ne_one : u ≠ 1
  v_ne_one : v ≠ 1
  w_ne_one : w ≠ 1
  power_one : c2 * (1 - x) = a2 * w * z
  power_two : b2 * (1 - u) = a2 * (1 - w) * (1 - z)
  power_three : c2 * y = b2 * u * v
  power_four : a2 * (1 - w) = b2 * (1 - u) * (1 - v)
  power_five : c2 * x * y = b2 * v
  power_six : c2 * (1 - x) * (1 - y) = a2 * z

/-- The existing division-free power calculation closes the six-block
certificate. -/
theorem SixFivePowerData.not_realizable (d : SixFivePowerData) : False := by
  exact six_five_power_equations_contradiction
    d.a2_ne_zero d.b2_ne_zero d.c2_ne_zero d.v_ne_zero d.z_ne_zero
    d.u_ne_one d.v_ne_one d.w_ne_one d.power_one d.power_two
    d.power_three d.power_four d.power_five d.power_six

/-- The three polynomial equations left by the forced four-pentagon
incidence pattern after Menelaus and power-of-a-point elimination.

Keeping `u` and the three pre-resultant equations here makes the interface
strictly closer to the geometric coordinate construction than assuming the
two already-factorized terminal equations. -/
structure FourPentagonCoordinateData where
  s : Real
  t : Real
  u : Real
  s_ne_zero : s ≠ 0
  s_ne_one : s ≠ 1
  sum_ne_zero : s + t ≠ 0
  polynomial_one : s ^ 2 * u + s * t - s - t * u = 0
  polynomial_two :
    2 * s * t * u - s * t - s * u + t ^ 2 - t * u = 0
  polynomial_three :
    s ^ 2 * t - s ^ 2 + s * t ^ 2 - s * t * u +
      t ^ 2 * u - t ^ 2 = 0

/-- The four-pentagon coordinate certificate has no real realization.  The
two resultants are derived here, followed by the final
`s (s - 1)^2 (3t - 1)` identity. -/
theorem FourPentagonCoordinateData.not_realizable
    (d : FourPentagonCoordinateData) : False := by
  have hfactor_one :
      (d.s + d.t) *
          (d.s ^ 2 * d.t - 3 * d.s * d.t + d.s + d.t ^ 2) = 0 := by
    calc
      (d.s + d.t) *
          (d.s ^ 2 * d.t - 3 * d.s * d.t + d.s + d.t ^ 2) =
          -((d.s ^ 2 - d.t) *
              (2 * d.s * d.t * d.u - d.s * d.t - d.s * d.u +
                d.t ^ 2 - d.t * d.u) -
            (2 * d.s * d.t - d.s - d.t) *
              (d.s ^ 2 * d.u + d.s * d.t - d.s - d.t * d.u)) := by
            ring
      _ = 0 := by rw [d.polynomial_one, d.polynomial_two]; ring
  have hfactor_two :
      (d.s + d.t) *
          (d.s ^ 3 * d.t - d.s ^ 3 + d.s ^ 2 * d.t -
            2 * d.s * d.t ^ 2 + d.t ^ 2) = 0 := by
    calc
      (d.s + d.t) *
          (d.s ^ 3 * d.t - d.s ^ 3 + d.s ^ 2 * d.t -
            2 * d.s * d.t ^ 2 + d.t ^ 2) =
          (d.s ^ 2 - d.t) *
              (d.s ^ 2 * d.t - d.s ^ 2 + d.s * d.t ^ 2 -
                d.s * d.t * d.u + d.t ^ 2 * d.u - d.t ^ 2) -
            (-d.s * d.t + d.t ^ 2) *
              (d.s ^ 2 * d.u + d.s * d.t - d.s - d.t * d.u) := by
            ring
      _ = 0 := by rw [d.polynomial_one, d.polynomial_three]; ring
  have hfirst :
      d.s ^ 2 * d.t - 3 * d.s * d.t + d.s + d.t ^ 2 = 0 :=
    (mul_eq_zero.mp hfactor_one).resolve_left d.sum_ne_zero
  have hsecond :
      d.s ^ 3 * d.t - d.s ^ 3 + d.s ^ 2 * d.t -
        2 * d.s * d.t ^ 2 + d.t ^ 2 = 0 :=
    (mul_eq_zero.mp hfactor_two).resolve_left d.sum_ne_zero
  have hterminal :
      d.s * (d.s - 1) ^ 2 * (3 * d.t - 1) = 0 := by
    calc
      d.s * (d.s - 1) ^ 2 * (3 * d.t - 1) =
          (d.s ^ 3 * d.t - d.s ^ 3 + d.s ^ 2 * d.t -
              2 * d.s * d.t ^ 2 + d.t ^ 2) -
            (1 - 2 * d.s) *
              (d.s ^ 2 * d.t - 3 * d.s * d.t + d.s + d.t ^ 2) := by
            ring
      _ = 0 := by rw [hfirst, hsecond]; ring
  have hs_minus_one : d.s - 1 ≠ 0 := sub_ne_zero.mpr d.s_ne_one
  have hcoefficient : d.s * (d.s - 1) ^ 2 ≠ 0 :=
    mul_ne_zero d.s_ne_zero (pow_ne_zero 2 hs_minus_one)
  have ht : 3 * d.t - 1 = 0 :=
    (mul_eq_zero.mp hterminal).resolve_left hcoefficient
  nlinarith [hfirst, sq_nonneg d.s]

/-- Projective coordinates and the concurrent-matching determinant at the
disjoint two-pentagon endpoint.  The two equations for `a` are precisely the
golden wall; the alternative consists of the two determinant orbits from the
manuscript before reduction modulo that wall. -/
structure GoldenLinkCoordinateData where
  a : Real
  b : Real
  a_eq_one_sub_b : a = 1 - b
  a_eq_b_sq : a = b ^ 2
  concurrency :
    (-(a - 1) * (a * b - a + b) = 0) ∨
      (a ^ 2 * b - a ^ 2 + a * b - b ^ 2 = 0)

/-- Neither concurrent-matching determinant can vanish on the golden wall. -/
theorem GoldenLinkCoordinateData.not_realizable
    (d : GoldenLinkCoordinateData) : False := by
  have hgolden : d.b ^ 2 + d.b - 1 = 0 := by
    nlinarith [d.a_eq_one_sub_b, d.a_eq_b_sq]
  rcases d.concurrency with hfirst | hsecond
  · have hlinear : 4 - 6 * d.b = 0 := by
      calc
        4 - 6 * d.b =
            (-(d.a - 1) * (d.a * d.b - d.a + d.b)) -
              (4 - d.b) * (d.b ^ 2 + d.b - 1) := by
                rw [d.a_eq_one_sub_b]
                ring
        _ = 0 := by rw [hfirst, hgolden]; ring
    nlinarith [hgolden]
  · have hlinear : 11 * d.b - 7 = 0 := by
      calc
        11 * d.b - 7 =
            (d.a ^ 2 * d.b - d.a ^ 2 + d.a * d.b - d.b ^ 2) -
              (d.b - 6) * (d.b ^ 2 + d.b - 1) := by
                rw [d.a_eq_one_sub_b]
                ring
        _ = 0 := by rw [hsecond, hgolden]; ring
    nlinarith [hgolden]

/-! ## Positive incidence certificates -/

/-- Four pairwise disjoint two-sets assigned to two three-sets.  This is the
label-free finite trace of the forbidden four-edge matching in
`C3 disjoint-union C3`. -/
structure FourMatchingInTwoTriangles (Point : Type*) [DecidableEq Point] where
  triangle : Fin 2 → Finset Point
  edge : Fin 4 → Finset Point
  side : Fin 4 → Fin 2
  triangle_card : forall i, (triangle i).card = 3
  edge_card : forall i, (edge i).card = 2
  edge_subset : forall i, edge i ⊆ triangle (side i)
  edge_pairwise_disjoint :
    forall i j, i ≠ j → Disjoint (edge i) (edge j)

/-- A three-set cannot contain two disjoint two-sets, so the side assignment
would inject four labels into two labels. -/
theorem FourMatchingInTwoTriangles.not_realizable
    {Point : Type*} [DecidableEq Point]
    (d : FourMatchingInTwoTriangles Point) : False := by
  have hside : Function.Injective d.side := by
    intro i j hij
    by_contra hne
    have hdisjoint := d.edge_pairwise_disjoint i j hne
    have hsubset : d.edge i ∪ d.edge j ⊆ d.triangle (d.side i) :=
      Finset.union_subset (d.edge_subset i) (by
        simpa [hij] using d.edge_subset j)
    have hcard := Finset.card_le_card hsubset
    rw [Finset.card_union_of_disjoint hdisjoint,
      d.edge_card i, d.edge_card j, d.triangle_card (d.side i)] at hcard
    omega
  have hcard := Fintype.card_le_of_injective d.side hside
  norm_num at hcard

/-- The exact local profile which the three-pentagon loss table (or the
meeting two-pentagon case) feeds into the real nine-point link lemma.  The
last field is the resulting incidence trace; the preceding fields keep the
route to that trace auditable. -/
structure LocalNineLinkMatchingData
    {Point Block : Type*} [Fintype Point] [Fintype Block]
    [DecidableEq Point]
    (S : BlockSystem Point Block) where
  pivot : Point
  three_degree : S.blockDegree 3 pivot = 6
  four_degree : S.blockDegree 4 pivot = 10
  five_degree : S.blockDegree 5 pivot = 0
  three_line_degree : S.lineDegree 3 pivot = 4
  matching : FourMatchingInTwoTriangles Point

/-- The disjoint alternative of the two-pentagon dichotomy, including the
two actual generalized blocks and the coordinate certificate produced by
the quadratic lift. -/
structure DisjointGoldenLinkData
    {Point Block : Type*} [Fintype Point] [Fintype Block]
    [DecidableEq Point]
    (S : BlockSystem Point Block) where
  first : Block
  second : Block
  first_mem : first ∈ S.blocksOfSize 5
  second_mem : second ∈ S.blocksOfSize 5
  blocks_ne : first ≠ second
  first_circle : S.kind first = .circle
  second_circle : S.kind second = .circle
  supports_disjoint : Disjoint (S.support first) (S.support second)
  coordinates : GoldenLinkCoordinateData

/-- The two geometric alternatives for the exact `B5 = 2` row. -/
inductive TwoPentagonEndpointData
    {Point Block : Type*} [Fintype Point] [Fintype Block]
    [DecidableEq Point]
    (S : BlockSystem Point Block)
  | meeting (link : LocalNineLinkMatchingData S)
  | disjoint (golden : DisjointGoldenLinkData S)

/-! ## The remaining real-plane reduction interface -/

/-- Positive real-plane outputs needed to construct the five kernels in
`RealPlaneTenFiveGeometry`.

The first and third fields are coordinate extraction statements.  The
second is the finite punctured-transversal statement.  The fourth includes
the finite three-pentagon loss classification followed by the local
nine-point link output.  The last field packages the meeting/disjoint split
and the quadratic-lift coordinate output.  No field states that a complete
configuration is impossible. -/
structure RealPlaneTenFiveReductionPrinciple where
  sixFivePowerCoordinates :
    forall {alpha : Type u} [Fintype alpha] [DecidableEq alpha]
      (cfg : Configuration alpha),
      Admissible cfg →
      Fintype.card alpha = 10 →
      BlockSizeCap (blockSystem cfg) 5 →
      (blockSystem cfg).blockCount 5 = 6 →
      SixFivePowerData
  puncturedPentagonTransversalCap :
    forall {alpha : Type u} [Fintype alpha] [DecidableEq alpha]
      (cfg : Configuration alpha),
      Admissible cfg →
      Fintype.card alpha = 10 →
      BlockSizeCap (blockSystem cfg) 5 →
      (blockSystem cfg).blockCount 5 = 5 →
      forall p : alpha,
        (blockSystem cfg).blockDegree 5 p = 3 →
          (blockSystem cfg).blockDegree 4 p ≤ 2
  fourPentagonCoordinates :
    forall {alpha : Type u} [Fintype alpha] [DecidableEq alpha]
      (cfg : Configuration alpha),
      Admissible cfg →
      Fintype.card alpha = 10 →
      BlockSizeCap (blockSystem cfg) 5 →
      (forall p : alpha, (blockSystem cfg).blockDegree 3 p = 6 ∨
        (blockSystem cfg).blockDegree 3 p = 9) →
      (blockSystem cfg).blockCount 5 = 4 →
      FourPentagonCoordinateData
  threePentagonLink :
    forall {alpha : Type u} [Fintype alpha] [DecidableEq alpha]
      (cfg : Configuration alpha),
      Admissible cfg →
      Fintype.card alpha = 10 →
      BlockSizeCap (blockSystem cfg) 5 →
      (blockSystem cfg).totalCircleCount = 32 →
      (blockSystem cfg).blockCount 5 = 3 →
      (tenHighPoints (blockSystem cfg)).card = 2 →
      (blockSystem cfg).lineCount 5 = 0 →
      1 ≤ (blockSystem cfg).lineCount 4 →
      (blockSystem cfg).lineCount 4 ≤ 3 →
      (blockSystem cfg).lineCount 3 +
          (blockSystem cfg).lineCount 4 = 10 →
      (forall p : alpha, TenFiveLocalProfile (blockSystem cfg) p) →
      LocalNineLinkMatchingData (blockSystem cfg)
  twoPentagonEndpoint :
    forall {alpha : Type u} [Fintype alpha] [DecidableEq alpha]
      (cfg : Configuration alpha),
      Admissible cfg →
      Fintype.card alpha = 10 →
      (blockSystem cfg).totalCircleCount = 32 →
      (blockSystem cfg).blockCount 3 = 20 →
      (blockSystem cfg).blockCount 4 = 20 →
      (blockSystem cfg).blockCount 5 = 2 →
      (blockSystem cfg).lineCount 3 = 10 →
      (blockSystem cfg).lineCount 4 = 0 →
      (blockSystem cfg).lineCount 5 = 0 →
      (forall p : alpha, (blockSystem cfg).blockDegree 3 p = 6) →
      TwoPentagonEndpointData (blockSystem cfg)

/-! ## Configuration-level assembly -/

/-- The generic triple-owner moment gives the non-strict packing bound
`B5 <= 6` for generalized blocks. -/
theorem ten_five_block_count_le_six
    {alpha : Type u} [Fintype alpha] [DecidableEq alpha]
    (cfg : Configuration alpha) (hcard : Fintype.card alpha = 10) :
    (blockSystem cfg).blockCount 5 ≤ 6 := by
  classical
  let S := blockSystem cfg
  have hbound :=
    card_le_six_of_five_subsets_card_ten_inter_le_two
      (S.blocksOfSize 5) S.support hcard
      (fun b hb => S.mem_blocksOfSize.mp hb)
      (fun b _hb c _hc hbc => by
        have hlt := S.distinct_block_inter_card_lt_three hbc
        omega)
  simpa [S, BlockSystem.blockCount] using hbound

/-- Five five-blocks on ten labels necessarily have a point of five-degree
three.  This is the moment part of the punctured-pentagon argument and needs
no geometric input.

Indeed, if `r != 3` and `r <= 5`, then
`5r <= 2 * choose r 2 + 8`.  Summing would give `125 <= 120`, because the
first incidence moment is `25` and the pair moment is at most `20`. -/
theorem exists_five_degree_three_of_blockCount_five_eq_five
    {Point Block : Type*} [Fintype Point] [Fintype Block]
    [DecidableEq Point]
    (S : BlockSystem Point Block) (hcard : Fintype.card Point = 10)
    (hB5 : S.blockCount 5 = 5) :
    ∃ p : Point, S.blockDegree 5 p = 3 := by
  classical
  by_contra hnone
  push Not at hnone
  have hr (p : Point) : S.blockDegree 5 p ≤ 5 :=
    (blockDegree_le_blockCount S 5 p).trans_eq hB5
  have hpoint (p : Point) :
      5 * S.blockDegree 5 p ≤
        2 * Nat.choose (S.blockDegree 5 p) 2 + 8 := by
    have hrp := hr p
    have hne := hnone p
    interval_cases hdegree : S.blockDegree 5 p <;>
      norm_num [Nat.choose] at *
  have hincidence := S.block_incidence 5
  rw [hB5] at hincidence
  norm_num at hincidence
  have hmoment := S.second_moment_le_two_choose (S.blocksOfSize 5)
  change (∑ p : Point, Nat.choose (S.blockDegree 5 p) 2) ≤
    2 * Nat.choose (S.blockCount 5) 2 at hmoment
  rw [hB5] at hmoment
  norm_num [Nat.choose] at hmoment
  have hsum :
      5 * (∑ p : Point, S.blockDegree 5 p) ≤
        2 * (∑ p : Point, Nat.choose (S.blockDegree 5 p) 2) +
          8 * Fintype.card Point := by
    calc
      5 * (∑ p : Point, S.blockDegree 5 p) =
          ∑ p : Point, 5 * S.blockDegree 5 p := by
            rw [Finset.mul_sum]
      _ ≤ ∑ p : Point,
          (2 * Nat.choose (S.blockDegree 5 p) 2 + 8) :=
        Finset.sum_le_sum fun p _hp => hpoint p
      _ = 2 * (∑ p : Point, Nat.choose (S.blockDegree 5 p) 2) +
          8 * Fintype.card Point := by
            simp only [Finset.sum_add_distrib, ← Finset.mul_sum,
              Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
            rw [hcard]
            norm_num
  rw [hincidence, hcard] at hsum
  omega

/-- Assemble the five public geometric kernels from positive incidence and
coordinate reductions.  All terminal contradictions are discharged in this
module. -/
def RealPlaneTenFiveReductionPrinciple.toGeometry
    (R : RealPlaneTenFiveReductionPrinciple.{u}) :
    RealPlaneTenFiveGeometry.{u} where
  fiveBlockPacking := by
    intro alpha _ _ cfg hadm hcard hcap
    have hle6 := ten_five_block_count_le_six cfg hcard
    by_contra hnot
    have hsix : (blockSystem cfg).blockCount 5 = 6 := by omega
    exact (R.sixFivePowerCoordinates cfg hadm hcard hcap hsix).not_realizable
  puncturedPentagon := by
    intro alpha _ _ cfg hadm hcard hcap hd3 hfive
    let S := blockSystem cfg
    obtain ⟨p, hp⟩ :=
      exists_five_degree_three_of_blockCount_five_eq_five S hcard hfive
    have hpairs := (ten_local_pair_and_kappa S hcard hcap p).1
    have hdegree :
        S.blockDegree 3 p = 6 ∨ S.blockDegree 3 p = 9 := by
      simpa [S] using hd3 p
    have hfourDegree : S.blockDegree 4 p ≤ 2 := by
      simpa [S] using
        R.puncturedPentagonTransversalCap cfg hadm hcard hcap hfive p hp
    rcases hdegree with hdegree | hdegree <;> omega
  fourPentagon := by
    intro alpha _ _ cfg hadm hcard hcap hd3 hfour
    exact (R.fourPentagonCoordinates cfg hadm hcard hcap hd3 hfour).not_realizable
  threePentagonRichLine := by
    intro alpha _ _ cfg hadm hcard hcap hcircle hfive hhigh hline5
      hline4pos hline4cap hline34 hlocal
    exact (R.threePentagonLink cfg hadm hcard hcap hcircle hfive hhigh hline5
      hline4pos hline4cap hline34 hlocal).matching.not_realizable
  disjointGoldenLink := by
    intro alpha _ _ cfg hadm hcard hcircle hb3 hb4 hb5 hl3 hl4 hl5 hd3
    rcases R.twoPentagonEndpoint cfg hadm hcard hcircle hb3 hb4 hb5
        hl3 hl4 hl5 hd3 with link | golden
    · exact link.matching.not_realizable
    · exact golden.coordinates.not_realizable

end Erdos506.V1
