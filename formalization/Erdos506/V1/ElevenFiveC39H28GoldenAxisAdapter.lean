import Erdos506.V1.ElevenFiveC39H28Finish
import Erdos506.Incidence.FiveConicRootedCyclicTrace

/-!
# The projective seam of the H28 golden-axis adapter

This file carries out every part of the H28 adapter which follows from an
actual five-point circle trace alone.  After choosing a rooted cyclic label,
the five homogeneous representatives are the literal affine lifts of the
five selected points.  They are in homogeneous general position.  The four
marked representatives are then defined, without a projective normal-form
choice, as the intersections of the two actual chord lines in the four rows
of `goldenCenterChordEndpoint`.  General position makes them nonzero, and
their eight centre incidences hold by construction.

Consequently the only configuration-dependent input still needed by
`fiveConic_goldenAxis_tangentSeparation_absurd` is

* collinearity of these four canonical actual centres, and
* one of the two displayed omitted-colour concurrency patterns.

`ElevenFiveC39H28GoldenAxisMissingIncidence` records precisely those two
facts.  The H28 interface currently supplies only the point count, trace
size, host weight and vanishing `(1,4)` count.  In particular it does not
supply the zero-fibre/four-page/outsider-five-block residual from which the
two facts above are obtained in the paper.  The final theorem below is
therefore the maximal assumption-free projective bridge: an extraction of
that residual incidence data implies the existing actual-adapter interface,
with no new geometric principle or normal-form hypothesis.
-/

namespace Erdos506.V1

open Erdos506.Incidence
open Erdos506.V4
open Matrix

universe u

/-- The five literal homogeneous representatives of an actual circle trace,
in rooted cyclic order. -/
noncomputable def elevenFiveC39H28GoldenTraceRaw
    {α : Type u} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (Gamma : DeterminedCircle cfg)
    (hD : (circleTrace cfg Gamma.1).card = 5) (r : Fin 5) :
    Fin 5 → Homogeneous3 :=
  fun i => homogeneousLift
    (cfg (fiveConicRootedCyclicLabel cfg Gamma hD r i).1)

/-- The four canonical actual chord-pair centres.  Each value is literally
the double-cross intersection of the two rows prescribed by
`goldenCenterChordEndpoint`. -/
def elevenFiveC39H28GoldenCenterRaw
    (g : Fin 5 → Homogeneous3) : Fin 4 → Homogeneous3 :=
  fun i => diagonalAB_CD
    (g (goldenCenterChordEndpoint i 0 0))
    (g (goldenCenterChordEndpoint i 0 1))
    (g (goldenCenterChordEndpoint i 1 0))
    (g (goldenCenterChordEndpoint i 1 1))

/-- Literal representatives of five distinct points of one proper circle
are in homogeneous five-point general position. -/
theorem elevenFiveC39H28GoldenTraceRaw_generalPosition
    {α : Type u} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (Gamma : DeterminedCircle cfg)
    (hD : (circleTrace cfg Gamma.1).card = 5) (r : Fin 5) :
    HomogeneousFiveGeneralPosition
      (elevenFiveC39H28GoldenTraceRaw cfg Gamma hD r) := by
  refine ⟨fun i => homogeneousLift_ne_zero _, ?_⟩
  intro i j k hij hik hjk
  exact homogeneousLift_det_ne_zero_of_mem_properCircle Gamma.1
    (mem_circleTrace.mp
      (fiveConicRootedCyclicLabel cfg Gamma hD r i).2)
    (mem_circleTrace.mp
      (fiveConicRootedCyclicLabel cfg Gamma hD r j).2)
    (mem_circleTrace.mp
      (fiveConicRootedCyclicLabel cfg Gamma hD r k).2)
    (cfg.injective.ne
      (fiveConicRootedCyclicLabel_ne cfg Gamma hD r i j hij))
    (cfg.injective.ne
      (fiveConicRootedCyclicLabel_ne cfg Gamma hD r i k hik))
    (cfg.injective.ne
      (fiveConicRootedCyclicLabel_ne cfg Gamma hD r j k hjk))

private theorem completeQuadrangleGeneralPosition_of_five
    {g : Fin 5 → Homogeneous3}
    (hgeneral : HomogeneousFiveGeneralPosition g)
    (a b c d : Fin 5)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    CompleteQuadrangleGeneralPosition (g a) (g b) (g c) (g d) := by
  exact ⟨
    hgeneral.2 a b c hab hac hbc,
    hgeneral.2 a b d hab had hbd,
    hgeneral.2 a c d hac had hcd,
    hgeneral.2 b c d hbc hbd hcd⟩

/-- Every canonical actual chord-pair centre is a nonzero homogeneous
representative. -/
theorem elevenFiveC39H28GoldenCenterRaw_ne_zero
    {g : Fin 5 → Homogeneous3}
    (hgeneral : HomogeneousFiveGeneralPosition g) :
    ∀ i, elevenFiveC39H28GoldenCenterRaw g i ≠ 0 := by
  intro i
  fin_cases i
  · exact diagonalAB_CD_ne_zero
      (completeQuadrangleGeneralPosition_of_five hgeneral
        0 2 3 4 (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide))
  · exact diagonalAB_CD_ne_zero
      (completeQuadrangleGeneralPosition_of_five hgeneral
        0 3 1 4 (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide))
  · exact diagonalAB_CD_ne_zero
      (completeQuadrangleGeneralPosition_of_five hgeneral
        0 4 1 2 (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide))
  · exact diagonalAB_CD_ne_zero
      (completeQuadrangleGeneralPosition_of_five hgeneral
        0 1 2 3 (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide))

private theorem diagonalAB_CD_first_incidence
    (a b c d : Homogeneous3) :
    Matrix.det ![a, b, diagonalAB_CD a b c d] = 0 := by
  calc
    Matrix.det ![a, b, diagonalAB_CD a b c d] =
        diagonalAB_CD a b c d ⬝ᵥ crossProduct a b := by
      symm
      calc
        diagonalAB_CD a b c d ⬝ᵥ crossProduct a b =
            a ⬝ᵥ crossProduct b (diagonalAB_CD a b c d) :=
          triple_product_permutation _ _ _
        _ = Matrix.det ![a, b, diagonalAB_CD a b c d] :=
          triple_product_eq_det _ _ _
    _ = crossProduct a b ⬝ᵥ diagonalAB_CD a b c d :=
      dotProduct_comm _ _
    _ = 0 := by
      simpa only [diagonalAB_CD] using
        (dot_self_cross (crossProduct a b) (crossProduct c d))

private theorem diagonalAB_CD_second_incidence
    (a b c d : Homogeneous3) :
    Matrix.det ![c, d, diagonalAB_CD a b c d] = 0 := by
  calc
    Matrix.det ![c, d, diagonalAB_CD a b c d] =
        diagonalAB_CD a b c d ⬝ᵥ crossProduct c d := by
      symm
      calc
        diagonalAB_CD a b c d ⬝ᵥ crossProduct c d =
            c ⬝ᵥ crossProduct d (diagonalAB_CD a b c d) :=
          triple_product_permutation _ _ _
        _ = Matrix.det ![c, d, diagonalAB_CD a b c d] :=
          triple_product_eq_det _ _ _
    _ = crossProduct c d ⬝ᵥ diagonalAB_CD a b c d :=
      dotProduct_comm _ _
    _ = 0 := by
      simpa only [diagonalAB_CD] using
        (dot_cross_self (crossProduct a b) (crossProduct c d))

/-- The eight golden centre incidences need no H28 hypothesis: they hold
definitionally for the actual double-cross centres. -/
theorem elevenFiveC39H28GoldenCenterRaw_centerIncidence
    (g : Fin 5 → Homogeneous3) :
    GoldenAxisCenterIncidence g
      (elevenFiveC39H28GoldenCenterRaw g) := by
  intro i j
  fin_cases j
  · exact diagonalAB_CD_first_incidence
      (g (goldenCenterChordEndpoint i 0 0))
      (g (goldenCenterChordEndpoint i 0 1))
      (g (goldenCenterChordEndpoint i 1 0))
      (g (goldenCenterChordEndpoint i 1 1))
  · exact diagonalAB_CD_second_incidence
      (g (goldenCenterChordEndpoint i 0 0))
      (g (goldenCenterChordEndpoint i 0 1))
      (g (goldenCenterChordEndpoint i 1 0))
      (g (goldenCenterChordEndpoint i 1 1))

/-- The exact remaining projective content of the actual H28 residual.
The representatives, their general position, their nonzeroness, and all
centre incidences are deliberately absent: the preceding theorems construct
and prove those facts from the actual five-trace. -/
def ElevenFiveC39H28GoldenAxisMissingIncidence
    {α : Type u} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (Gamma : DeterminedCircle cfg)
    (hD : (circleTrace cfg Gamma.1).card = 5) : Prop :=
  ∃ r : Fin 5,
    let g := elevenFiveC39H28GoldenTraceRaw cfg Gamma hD r
    let q := elevenFiveC39H28GoldenCenterRaw g
    GoldenAxisCollinear q ∧
      (GoldenAxisEndConcurrent g q ∨ GoldenAxisMiddleConcurrent g q)

/-- Once the two genuinely residual incidence statements have been
extracted, the existing raw K2.4 endpoint closes the configuration. -/
theorem elevenFiveC39H28GoldenAxisMissingIncidence_absurd
    {α : Type u} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (Gamma : DeterminedCircle cfg)
    (hD : (circleTrace cfg Gamma.1).card = 5)
    (hmissing : ElevenFiveC39H28GoldenAxisMissingIncidence cfg Gamma hD) :
    False := by
  rcases hmissing with ⟨r, haxis, hconcurrency⟩
  let g := elevenFiveC39H28GoldenTraceRaw cfg Gamma hD r
  let q := elevenFiveC39H28GoldenCenterRaw g
  exact fiveConic_goldenAxis_tangentSeparation_absurd g q
    (elevenFiveC39H28GoldenTraceRaw_generalPosition cfg Gamma hD r)
    (elevenFiveC39H28GoldenCenterRaw_ne_zero
      (elevenFiveC39H28GoldenTraceRaw_generalPosition cfg Gamma hD r))
    (elevenFiveC39H28GoldenCenterRaw_centerIncidence g)
    haxis hconcurrency

/-- Configuration-level name for the sole extraction which is not provided
by the present H28 interface.  It mirrors that interface exactly and asks
only for `ElevenFiveC39H28GoldenAxisMissingIncidence`, not for a normal form
or an additional geometric principle. -/
def ElevenFiveC39H28GoldenAxisMissingIncidenceExtraction
    {α : Type u} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) : Prop :=
  ∀ (Gamma : DeterminedCircle cfg)
    (_hpoint : Fintype.card α = 11)
    (hD : (circleTrace cfg Gamma.1).card = 5)
    (_hhost : elevenFiveHostWeight (blockSystem cfg)
      (circleTrace cfg Gamma.1) = 28),
    elevenFiveRelativeCount (blockSystem cfg)
      (circleTrace cfg Gamma.1) 1 4 = 0 →
      ElevenFiveC39H28GoldenAxisMissingIncidence cfg Gamma hD

/-- Maximal bridge to the already published H28 interface.  No additional
geometric axiom is introduced: a proof of the concrete residual extraction
is consumed immediately by the raw five-conic contradiction. -/
theorem elevenFiveC39H28GoldenAxisActualAdapter_of_missingIncidenceExtraction
    {α : Type u} [Fintype α] [DecidableEq α]
    (cfg : Configuration α)
    (hextract :
      ElevenFiveC39H28GoldenAxisMissingIncidenceExtraction cfg) :
    ElevenFiveC39H28GoldenAxisActualAdapter cfg := by
  intro Gamma hpoint hD hhost hzero
  exact elevenFiveC39H28GoldenAxisMissingIncidence_absurd cfg Gamma hD
    (hextract Gamma hpoint hD hhost hzero)

end Erdos506.V1
