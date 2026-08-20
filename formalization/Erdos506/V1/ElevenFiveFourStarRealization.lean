import Erdos506.Finite.FourStarCompleteQuadrangle
import Erdos506.Incidence.FourStarRigidity
import Erdos506.Incidence.RadicalAxisFourFourGeometry
import Erdos506.V1.InversionAugmentation
import Erdos506.V3.PivotGeometry

/-!
# Concrete projective realization of an inverted eleven-five four-star

This is the deliberately small bridge between the finite four-star link and
the real projective endpoint.  Its line covectors are *not* extra data: each
is the cross product of two actual points of the inverted configuration.

The remaining boundary is explicit.  The finite counts choose and classify
the four lines and their private points, while the facts that these particular
lines are a projective complete quadrangle and have the triangle-pendant
determinant pattern still need a geometric extraction theorem.  No such
assertion is hidden in this file.
-/

namespace Erdos506.V1

open Erdos506.Block
open Erdos506.Incidence
open Erdos506.V3
open Erdos506.V4

universe u

/-- The line covector obtained from two distinct labelled points of a concrete
configuration. -/
def fourStarConcreteCovector {Point : Type u}
    (Q : Configuration Point) (a b : Point) : Homogeneous3 :=
  lineCovector (Q a) (Q b)

/-- A concrete four-star witness in a real affine configuration.  The finite
line supports are retained so the object can be filled directly from the
inverted configuration; the four homogeneous covectors are then definitions,
not fields.

The affine/projective compatibility is derived below from
`DeterminedLine.exists_pair`, so it is not a field.  In contrast,
`base_general_position` is precisely the no-three-concurrent part of the
finite-to-projective bridge. -/
structure FourStarConcreteQuadrangle {Point : Type u} [Fintype Point]
    [DecidableEq Point] (Q : Configuration Point) where
  line : Fin 4 → DeterminedLine Q
  line_injective : Function.Injective line
  line_support_card : ∀ i, (lineSupport Q (line i)).card = 4
  endpoint : Fin 4 → Fin 2 → Point
  endpoint_mem : ∀ i j, endpoint i j ∈ lineSupport Q (line i)
  endpoint_ne : ∀ i, endpoint i 0 ≠ endpoint i 1
  privateLabel : Fin 4 → Point
  private_on : ∀ i, privateLabel i ∈ lineSupport Q (line i)
  private_off : ∀ i j, i ≠ j → privateLabel i ∉ lineSupport Q (line j)
  base_general_position : CompleteQuadrangleGeneralPosition
    (fourStarConcreteCovector Q (endpoint 0 0) (endpoint 0 1))
    (fourStarConcreteCovector Q (endpoint 1 0) (endpoint 1 1))
    (fourStarConcreteCovector Q (endpoint 2 0) (endpoint 2 1))
    (fourStarConcreteCovector Q (endpoint 3 0) (endpoint 3 1))

/-- The four covectors extracted from the actual endpoints. -/
def FourStarConcreteQuadrangle.baseLine {Point : Type u} [Fintype Point]
    [DecidableEq Point] {Q : Configuration Point}
    (R : FourStarConcreteQuadrangle Q) : Fin 4 → Homogeneous3 :=
  fun i => fourStarConcreteCovector Q (R.endpoint i 0) (R.endpoint i 1)

/-- The four projective points extracted from the actual private labels. -/
def FourStarConcreteQuadrangle.privatePoint {Point : Type u} [Fintype Point]
    [DecidableEq Point] {Q : Configuration Point}
    (R : FourStarConcreteQuadrangle Q) : Fin 4 → Homogeneous3 :=
  fun i => homogeneousLift (Q (R.privateLabel i))

theorem FourStarConcreteQuadrangle.baseLine_ne_zero
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {Q : Configuration Point} (R : FourStarConcreteQuadrangle Q) (i : Fin 4) :
    R.baseLine i ≠ 0 := by
  apply lineCovector_ne_zero
  exact Q.injective.ne (R.endpoint_ne i)

/-- Membership in one of the four finite supports is equivalent to incidence
with the covector calculated from its two concrete endpoints.  This is fully
derived from the determined-line API. -/
theorem FourStarConcreteQuadrangle.mem_lineSupport_iff_incident
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {Q : Configuration Point} (R : FourStarConcreteQuadrangle Q)
    (i : Fin 4) (x : Point) :
    x ∈ lineSupport Q (R.line i) ↔
      homogeneousIncident (Q x) (R.baseLine i) := by
  have hab : R.endpoint i 0 ≠ R.endpoint i 1 := R.endpoint_ne i
  let A : Erdos506.Finite.KSubset Point 2 :=
    ⟨{R.endpoint i 0, R.endpoint i 1}, by simp [hab]⟩
  have hmem : ∀ z ∈ A.1, Q z ∈ (R.line i).1 := by
    intro z hz
    have hz' : z = R.endpoint i 0 ∨ z = R.endpoint i 1 := by
      simpa [A] using hz
    rcases hz' with rfl | rfl
    · exact mem_lineSupport.mp (R.endpoint_mem i 0)
    · exact mem_lineSupport.mp (R.endpoint_mem i 1)
  have hpair : lineOfPair Q A = (R.line i).1 :=
    lineOfPair_eq_of_mem_of_direction_finrank_one Q A (R.line i).1 hmem
      (R.line i).direction_finrank
  have hspan : affineSpan ℝ ({Q (R.endpoint i 0), Q (R.endpoint i 1)} : Set Point2) =
      (R.line i).1 := by
    calc
      affineSpan ℝ ({Q (R.endpoint i 0), Q (R.endpoint i 1)} : Set Point2) =
          lineOfPair Q A := by
            simpa [A] using (lineOfPair_pair Q hab).symm
      _ = (R.line i).1 := hpair
  rw [mem_lineSupport]
  rw [← hspan]
  exact (homogeneousIncident_lineCovector_iff_mem_affineSpan
    (Q.injective.ne hab)).symm

/-- The concrete witness canonically supplies the homogeneous four-star
skeleton.  In particular, all its line covectors are obtained from `Q`; no
separate projective-line authority is introduced. -/
noncomputable def FourStarConcreteQuadrangle.toProjectiveSkeleton
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {Q : Configuration Point} (R : FourStarConcreteQuadrangle Q) :
    FourStarProjectiveSkeleton where
  baseLine := R.baseLine
  privatePoint := R.privatePoint
  base_general_position := by
    simpa [FourStarConcreteQuadrangle.baseLine,
      fourStarConcreteCovector] using R.base_general_position
  private_ne_zero := fun i => homogeneousLift_ne_zero _
  private_on_base := by
    intro i
    exact (R.mem_lineSupport_iff_incident i (R.privateLabel i)).mp (R.private_on i)
  private_off_base := by
    intro i j hij hzero
    have hincident : homogeneousIncident (Q (R.privateLabel i)) (R.baseLine j) :=
      hzero
    exact R.private_off i j hij
      ((R.mem_lineSupport_iff_incident j (R.privateLabel i)).mpr hincident)

/-- After supplying a four-covector frame, the concrete support incidence is
literally the standard-frame incidence.  This is the normalization transport
used by a later determinant calculation. -/
theorem FourStarConcreteQuadrangle.mem_lineSupport_iff_normal_incident
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {Q : Configuration Point} (R : FourStarConcreteQuadrangle Q)
    (F : ProjectiveCovectorFrame R.baseLine) (i : Fin 4) (x : Point) :
    projectiveCovectorNormalLine i ⬝ᵥ
        projectivePointTransform F.G (homogeneousLift (Q x)) = 0 ↔
      x ∈ lineSupport Q (R.line i) := by
  rw [projectiveCovectorFrame_incident_normal_iff F]
  simpa [homogeneousIncident, dotProduct_comm] using
    (R.mem_lineSupport_iff_incident i x).symm

/-- The exact local input supplied by a `(9,4,4)` pivot after inversion.
The fields record only the original pivot row and the ten-point cardinality;
the four size-four lines are extracted canonically below. -/
structure ElevenFivePivotInvertedFourStar {Point : Type u} [Fintype Point]
    [DecidableEq Point] (cfg : Configuration Point) (p : Point) where
  pivot_count_three : (blockSystem cfg).blockDegree 3 p = 9
  pivot_count_four : (blockSystem cfg).blockDegree 4 p = 4
  pivot_count_five : (blockSystem cfg).blockDegree 5 p = 4
  inverted_card : Fintype.card (AwayFrom p) = 10

/-- The pivot dictionary converts the three original local counts exactly to
the `(2,3,4) = (9,4,4)` line census of the inverted ten-point
configuration. -/
theorem ElevenFivePivotInvertedFourStar.inverted_line_profile
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (H : ElevenFivePivotInvertedFourStar cfg p) :
    (blockSystem (pivotInversion cfg p)).lineCount 2 = 9 ∧
      (blockSystem (pivotInversion cfg p)).lineCount 3 = 4 ∧
        (blockSystem (pivotInversion cfg p)).lineCount 4 = 4 := by
  constructor
  · rw [← blockDegree_eq_lineCount_pivotInversion cfg p 3 (by omega)]
    exact H.pivot_count_three
  constructor
  · rw [← blockDegree_eq_lineCount_pivotInversion cfg p 4 (by omega)]
    exact H.pivot_count_four
  · rw [← blockDegree_eq_lineCount_pivotInversion cfg p 5 (by omega)]
    exact H.pivot_count_five

/-- Canonical finite indexing of the four size-four affine lines in the
inverted configuration. -/
noncomputable def ElevenFivePivotInvertedFourStar.sizeFourLineEquiv
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (H : ElevenFivePivotInvertedFourStar cfg p) :
    Fin 4 ≃ DeterminedLineOfSize (pivotInversion cfg p) 4 := by
  apply (Fintype.equivFinOfCardEq ?_).symm
  rw [← lineCount_eq_card_determinedLineOfSize]
  exact H.inverted_line_profile.2.2

/-- The four concrete determined lines supplied by the `d₅=4` pivot row. -/
noncomputable def ElevenFivePivotInvertedFourStar.sizeFourLine
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (H : ElevenFivePivotInvertedFourStar cfg p) :
    Fin 4 → DeterminedLine (pivotInversion cfg p) :=
  fun i => (H.sizeFourLineEquiv i).1

theorem ElevenFivePivotInvertedFourStar.sizeFourLine_injective
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (H : ElevenFivePivotInvertedFourStar cfg p) :
    Function.Injective H.sizeFourLine := by
  intro i j hij
  apply H.sizeFourLineEquiv.injective
  apply Subtype.ext
  exact hij

theorem ElevenFivePivotInvertedFourStar.sizeFourLine_support_card
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (H : ElevenFivePivotInvertedFourStar cfg p) (i : Fin 4) :
    (lineSupport (pivotInversion cfg p) (H.sizeFourLine i)).card = 4 :=
  (H.sizeFourLineEquiv i).2

/-- Each canonically extracted four-line has two distinct concrete endpoints
in its own finite support.  This is the endpoint part of the realization
bridge, derived solely from the `DeterminedLine` API. -/
theorem ElevenFivePivotInvertedFourStar.sizeFourLine_exists_endpoints
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (H : ElevenFivePivotInvertedFourStar cfg p) (i : Fin 4) :
    ∃ a b : AwayFrom p, a ≠ b ∧
      a ∈ lineSupport (pivotInversion cfg p) (H.sizeFourLine i) ∧
        b ∈ lineSupport (pivotInversion cfg p) (H.sizeFourLine i) := by
  obtain ⟨A, hA⟩ := (H.sizeFourLine i).exists_pair
  obtain ⟨a, b, hab, hcard⟩ := Finset.card_eq_two.mp A.2
  let L : DeterminedLine (pivotInversion cfg p) :=
    ⟨lineOfPair (pivotInversion cfg p) A,
      lineOfPair_mem_determinedLines (pivotInversion cfg p) A⟩
  have hL : L = H.sizeFourLine i := Subtype.ext hA
  have hsub := pair_subset_lineSupport (pivotInversion cfg p) A
  refine ⟨a, b, hab, ?_, ?_⟩
  · exact hL ▸ hsub (by simp [hcard])
  · exact hL ▸ hsub (by simp [hcard])

/-- Saturation of the finite four-star: any two of the canonically indexed
size-four inverted lines meet in exactly one selected inverted point. -/
theorem ElevenFivePivotInvertedFourStar.sizeFourLine_inter_card_one
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (H : ElevenFivePivotInvertedFourStar cfg p) {i j : Fin 4} (hij : i ≠ j) :
    (lineSupport (pivotInversion cfg p) (H.sizeFourLine i) ∩
      lineSupport (pivotInversion cfg p) (H.sizeFourLine j)).card = 1 := by
  let Q := pivotInversion cfg p
  let bi : GeometricBlock Q := Sum.inl (H.sizeFourLine i)
  let bj : GeometricBlock Q := Sum.inl (H.sizeFourLine j)
  have hbi : bi ∈ (blockSystem Q).lineBlocksOfSize 4 := by
    apply (blockSystem Q).mem_blocksOfKindSize.mpr
    exact ⟨rfl, H.sizeFourLine_support_card i⟩
  have hbj : bj ∈ (blockSystem Q).lineBlocksOfSize 4 := by
    apply (blockSystem Q).mem_blocksOfKindSize.mpr
    exact ⟨rfl, H.sizeFourLine_support_card j⟩
  have hne : bi ≠ bj := by
    intro h
    apply hij
    apply H.sizeFourLine_injective
    simpa [bi, bj] using h
  have hfinite := Erdos506.Finite.line_four_inter_card_one_of_card_ten_count_four
    (blockSystem Q) H.inverted_card H.inverted_line_profile.2.2 hbi hbj hne
  simpa [Q, bi, bj, geometricBlockSupport] using hfinite

/-- The exact residual geometric data after the finite pivot extraction.
Its base lines are fixed to `H.sizeFourLine`, whose cardinality, injectivity,
and pairwise one-point intersections have already been derived above.  Thus
Endpoint choices can be selected globally from
`sizeFourLine_exists_endpoints`; private labels and the genuinely projective
no-three-concurrent condition remain as the substantive boundary data. -/
structure ElevenFiveFourStarGeometricBoundary
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (H : ElevenFivePivotInvertedFourStar cfg p) where
  endpoint : Fin 4 → Fin 2 → AwayFrom p
  endpoint_mem : ∀ i j,
    endpoint i j ∈ lineSupport (pivotInversion cfg p) (H.sizeFourLine i)
  endpoint_ne : ∀ i, endpoint i 0 ≠ endpoint i 1
  privateLabel : Fin 4 → AwayFrom p
  private_on : ∀ i,
    privateLabel i ∈ lineSupport (pivotInversion cfg p) (H.sizeFourLine i)
  private_off : ∀ i j, i ≠ j →
    privateLabel i ∉ lineSupport (pivotInversion cfg p) (H.sizeFourLine j)
  base_general_position : CompleteQuadrangleGeneralPosition
    (fourStarConcreteCovector (pivotInversion cfg p) (endpoint 0 0) (endpoint 0 1))
    (fourStarConcreteCovector (pivotInversion cfg p) (endpoint 1 0) (endpoint 1 1))
    (fourStarConcreteCovector (pivotInversion cfg p) (endpoint 2 0) (endpoint 2 1))
    (fourStarConcreteCovector (pivotInversion cfg p) (endpoint 3 0) (endpoint 3 1))

/-- Materialize the canonical finite line family as a concrete projective
quadrangle once the residual geometric boundary has been discharged. -/
noncomputable def ElevenFiveFourStarGeometricBoundary.toConcreteQuadrangle
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    {H : ElevenFivePivotInvertedFourStar cfg p}
    (G : ElevenFiveFourStarGeometricBoundary H) :
    FourStarConcreteQuadrangle (pivotInversion cfg p) where
  line := H.sizeFourLine
  line_injective := H.sizeFourLine_injective
  line_support_card := H.sizeFourLine_support_card
  endpoint := G.endpoint
  endpoint_mem := G.endpoint_mem
  endpoint_ne := G.endpoint_ne
  privateLabel := G.privateLabel
  private_on := G.private_on
  private_off := G.private_off
  base_general_position := G.base_general_position

/-- A pivot-inverted four-star already carries a projective skeleton over the
actual inverted coordinates. -/
noncomputable def ElevenFivePivotInvertedFourStar.toProjectiveSkeleton
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (H : ElevenFivePivotInvertedFourStar cfg p)
    (G : ElevenFiveFourStarGeometricBoundary H) : FourStarProjectiveSkeleton :=
  G.toConcreteQuadrangle.toProjectiveSkeleton

/-- The determinant endpoint required of the triangle-pendant branch.  It is
kept separate from the concrete realization because the finite `T`/cycle/
triangle-pendant classification does not yet attach its four selected lines
to these four indexed covectors. -/
structure ElevenFiveTrianglePendantEndpoint {Point : Type u} [Fintype Point]
    [DecidableEq Point] {cfg : Configuration Point} {p : Point}
    (H : ElevenFivePivotInvertedFourStar cfg p)
    (G : ElevenFiveFourStarGeometricBoundary H) where
  determinant_pattern : IsFourStarTrianglePendantDeterminantal
    (H.toProjectiveSkeleton G)
  coordinates : FourStarTrianglePendantCoordinates

/-- The scalar conclusion of the triangle-pendant determinant endpoint. -/
theorem elevenFive_trianglePendant_endpoint_coordinates
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (H : ElevenFivePivotInvertedFourStar cfg p)
    (G : ElevenFiveFourStarGeometricBoundary H)
    (E : ElevenFiveTrianglePendantEndpoint H G) :
    E.coordinates.a = 1 ∧ E.coordinates.b = 1 ∧
      E.coordinates.c = 1 ∧ E.coordinates.d = -1 / 2 :=
  fourStar_trianglePendant_coordinates_unique E.coordinates

/-!
## Explicit remaining theorem boundary

The intended next theorem has the following mathematical shape:

```
  (H : ElevenFivePivotInvertedFourStar cfg p) →
  (E : ElevenFiveTrianglePendantEndpoint H) →
  ∀ L, L ∈ H.quadrangle.line '' Finset.univ → Harmonic (lineSupport _ L)
```

It is not stated here because the repository currently has neither (1) a
proved extraction of the indexed private-line trichotomy from the four
three-lines in the finite block system nor (2) a coordinate-independent
`Harmonic` predicate for four affine points on an arbitrary projective line.
The existing `RealProjectiveHarmonic` predicate lives on `RP¹`, so asserting
the displayed conclusion now would merely move these two missing bridges into
structure fields.
-/

end Erdos506.V1
