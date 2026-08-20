import Erdos506.Incidence.UngarSixConcyclicSharpCase
import Erdos506.V1.TwelveSixRows

/-!
# The exact twelve-point direction-defect dictionary

The selected-six-circle direction step has a small integral interface.  At a
pivot, after inversion, restoration and duality, the off-star defect `δ` and
the number `R` of vertices on the distinguished line are determined by the
four local block and line multiplicities.  The manuscript identity

`δ - (R - 5) = (11 + σ - 2 d₅ - 6 d₆) / 3`

is recorded here without division.  Thus the remaining geometric work is
precisely the strictness statement `0 < δ - (R - 5)`: its equality case is
the six-real-point, five-direction configuration now excluded by the
formalized six-point circle theorem.

No direction inequality is assumed in this file.  Everything below is an
exact conversion of already materialized local rows.
-/

namespace Erdos506.V1

open Erdos506.Block
open Erdos506.Block.BlockSystem
open Erdos506.Incidence
open Erdos506.V4

universe u

/-- In the restored pivot arrangement, the `t₂` contribution written in
the original block/line census. -/
noncomputable def twelveDirectionT2
    {Point Block : Type*} [Fintype Point] [Fintype Block]
    [DecidableEq Point] (S : BlockSystem Point Block) (p : Point) : ℤ :=
  (S.blockDegree 3 p : ℤ) - S.lineDegree 3 p + S.lineDegree 2 p

/-- The restored `t₃` contribution. -/
noncomputable def twelveDirectionT3
    {Point Block : Type*} [Fintype Point] [Fintype Block]
    [DecidableEq Point] (S : BlockSystem Point Block) (p : Point) : ℤ :=
  (S.blockDegree 4 p : ℤ) - S.lineDegree 4 p + S.lineDegree 3 p

/-- The restored `t₄` contribution. -/
noncomputable def twelveDirectionT4
    {Point Block : Type*} [Fintype Point] [Fintype Block]
    [DecidableEq Point] (S : BlockSystem Point Block) (p : Point) : ℤ :=
  (S.blockDegree 5 p : ℤ) - S.lineDegree 5 p + S.lineDegree 4 p

/-- The restored `t₅` contribution. -/
noncomputable def twelveDirectionT5
    {Point Block : Type*} [Fintype Point] [Fintype Block]
    [DecidableEq Point] (S : BlockSystem Point Block) (p : Point) : ℤ :=
  (S.blockDegree 6 p : ℤ) + S.lineDegree 5 p

/-- The off-star defect of the fivefold vertex supplied by a six-block
through the pivot, expressed entirely in the local census. -/
noncomputable def twelveDirectionOffStarDefect
    {Point Block : Type*} [Fintype Point] [Fintype Block]
    [DecidableEq Point] (S : BlockSystem Point Block) (p : Point) : ℤ :=
  twelveDirectionT2 S p + 2 * twelveDirectionT3 S p +
    3 * twelveDirectionT4 S p + 4 * (twelveDirectionT5 S p - 1) - 35

/-- Number of vertices on the distinguished dual line. -/
noncomputable def twelveDirectionDistinguishedLineVertices
    {Point Block : Type*} [Fintype Point] [Fintype Block]
    [DecidableEq Point] (S : BlockSystem Point Block) (p : Point) : ℤ :=
  S.lineDegree 2 p + S.lineDegree 3 p +
    S.lineDegree 4 p + S.lineDegree 5 p

/-- The nonnegative integer whose strict positivity is the sole geometric
strictness assertion in the ordinary-direction proof. -/
noncomputable def twelveDirectionEqualityGap
    {Point Block : Type*} [Fintype Point] [Fintype Block]
    [DecidableEq Point] (S : BlockSystem Point Block) (p : Point) : ℤ :=
  twelveDirectionOffStarDefect S p -
    (twelveDirectionDistinguishedLineVertices S p - 5)

/-- Division-free form of the pivot direction-defect identity.  The two
rows used here are exactly the pair partition and the pivot Melchior row;
all line-degree terms cancel. -/
theorem three_mul_twelveDirectionEqualityGap_of_rows
    {Point Block : Type*} [Fintype Point] [Fintype Block]
    [DecidableEq Point] (S : BlockSystem Point Block) (p : Point)
    (sigma : ℤ)
    (hpair : (S.blockDegree 3 p : ℤ) + 3 * S.blockDegree 4 p +
        6 * S.blockDegree 5 p + 10 * S.blockDegree 6 p = 55)
    (hsigma : sigma + 3 + S.blockDegree 5 p +
        2 * S.blockDegree 6 p = S.blockDegree 3 p) :
    3 * twelveDirectionEqualityGap S p =
      11 + sigma - 2 * S.blockDegree 5 p - 6 * S.blockDegree 6 p := by
  simp only [twelveDirectionEqualityGap, twelveDirectionOffStarDefect,
    twelveDirectionDistinguishedLineVertices, twelveDirectionT2,
    twelveDirectionT3, twelveDirectionT4, twelveDirectionT5]
  omega

/-- Specialization of the division-free identity to the natural local rows
already available in the selected-six branch. -/
theorem three_mul_twelveDirectionEqualityGap_of_twelveSixRows
    {Point Block : Type*} [Fintype Point] [Fintype Block]
    [DecidableEq Point] (S : BlockSystem Point Block) (p : Point)
    (hrows : TwelveSixLocalRows S p) :
    3 * twelveDirectionEqualityGap S p =
      11 + (twelveSixSigmaAt S p : ℤ) -
        2 * S.blockDegree 5 p - 6 * S.blockDegree 6 p := by
  apply three_mul_twelveDirectionEqualityGap_of_rows S p
    (twelveSixSigmaAt S p)
  · exact_mod_cast hrows.pairRow
  · exact_mod_cast hrows.sigmaRow

/-- Once the equality census is ruled out, the defect numerator is at least
three.  This is the exact strict form consumed by the public direction
principle, before replacing `toNat pivotSigma` by `pivotSigma`. -/
theorem three_le_twelveDirectionDefectNumerator_of_gap_pos
    {Point Block : Type*} [Fintype Point] [Fintype Block]
    [DecidableEq Point] (S : BlockSystem Point Block) (p : Point)
    (hrows : TwelveSixLocalRows S p)
    (hgap : 0 < twelveDirectionEqualityGap S p) :
    3 ≤ 11 + (twelveSixSigmaAt S p : ℤ) -
      2 * S.blockDegree 5 p - 6 * S.blockDegree 6 p := by
  have hid := three_mul_twelveDirectionEqualityGap_of_twelveSixRows S p hrows
  omega

/-- Lossless cast from the natural selected-six slack to the genuine pivot
slack.  Keeping it separate makes explicit that no hidden sign convention is
used by the direction-defect calculation. -/
theorem three_le_twelveDirectionDefectNumerator_of_gap_pos_of_sigma_nonneg
    {Point Block : Type*} [Fintype Point] [Fintype Block]
    [DecidableEq Point] (S : BlockSystem Point Block) (p : Point)
    (hrows : TwelveSixLocalRows S p)
    (hsigma : 0 ≤ S.pivotSigma p)
    (hgap : 0 < twelveDirectionEqualityGap S p) :
    3 ≤ 11 + S.pivotSigma p -
      2 * S.blockDegree 5 p - 6 * S.blockDegree 6 p := by
  have hnum := three_le_twelveDirectionDefectNumerator_of_gap_pos
    S p hrows hgap
  have hcast : (twelveSixSigmaAt S p : ℤ) = S.pivotSigma p := by
    simpa [twelveSixSigmaAt] using Int.toNat_of_nonneg hsigma
  rw [hcast] at hnum
  exact hnum

end Erdos506.V1
