import Erdos506.Incidence.ProjectiveCoordinates
import Erdos506.Incidence.ProjectiveFiveFrame

/-!
# Golden-axis determinant certificates

This file contains the bounded coordinate calculation used at the disjoint
golden-link endpoint.  The five projective points are in the normal form
`projectiveFiveNormalPoint a b`.  Four rows of the near-one-factorization

* `02 | 34`,
* `03 | 14`,
* `04 | 12`,
* `01 | 23`

give four double-cross centres.  We expand those centres, the two
collinearity determinants, and the two possible three-line concurrency
determinants.  The last theorem is a self-contained real-algebra certificate
that the three required determinant vanishings cannot occur together.
-/

namespace Erdos506.Incidence

open Matrix

/-- Endpoints of the two chords in each of the four relevant rows of the
near-one-factorization.  The arguments are respectively the row, the chord
inside the row, and the endpoint inside the chord. -/
def goldenCenterChordEndpoint : Fin 4 → Fin 2 → Fin 2 → Fin 5 :=
  ![
    ![![0, 2], ![3, 4]],
    ![![0, 3], ![1, 4]],
    ![![0, 4], ![1, 2]],
    ![![0, 1], ![2, 3]]
  ]

/-- Intersection of the two chord lines in one row of
`goldenCenterChordEndpoint`. -/
def goldenCenterFromChords (a b : ℝ) (i : Fin 4) : Homogeneous3 :=
  crossProduct
    (crossProduct
      (projectiveFiveNormalPoint a b (goldenCenterChordEndpoint i 0 0))
      (projectiveFiveNormalPoint a b (goldenCenterChordEndpoint i 0 1)))
    (crossProduct
      (projectiveFiveNormalPoint a b (goldenCenterChordEndpoint i 1 0))
      (projectiveFiveNormalPoint a b (goldenCenterChordEndpoint i 1 1)))

/-- The four canonical representatives, indexed by `0,1,2,3` for the
manuscript centres `q₁,q₂,q₃,q₄`. -/
def goldenCanonicalCenter (a b : ℝ) : Fin 4 → Homogeneous3 :=
  ![
    ![a - b, 0, 1 - b],
    ![a, 1, 1],
    ![0, b, 1],
    ![-1, -1, 0]
  ]

theorem goldenCenterFromChords_zero (a b : ℝ) :
    goldenCenterFromChords a b 0 = ![a - b, 0, 1 - b] := by
  ext i
  fin_cases i <;>
    simp [goldenCenterFromChords, goldenCenterChordEndpoint,
      projectiveFiveNormalPoint, cross_apply]

theorem goldenCenterFromChords_one (a b : ℝ) :
    goldenCenterFromChords a b 1 = ![a, 1, 1] := by
  ext i
  fin_cases i <;>
    simp [goldenCenterFromChords, goldenCenterChordEndpoint,
      projectiveFiveNormalPoint, cross_apply]

theorem goldenCenterFromChords_two (a b : ℝ) :
    goldenCenterFromChords a b 2 = ![0, b, 1] := by
  ext i
  fin_cases i <;>
    simp [goldenCenterFromChords, goldenCenterChordEndpoint,
      projectiveFiveNormalPoint, cross_apply]

theorem goldenCenterFromChords_three (a b : ℝ) :
    goldenCenterFromChords a b 3 = ![-1, -1, 0] := by
  ext i
  fin_cases i <;>
    simp [goldenCenterFromChords, goldenCenterChordEndpoint,
      projectiveFiveNormalPoint, cross_apply]

/-- All four double-cross calculations agree with the canonical centre
table. -/
theorem goldenCenterFromChords_eq_canonical (a b : ℝ) (i : Fin 4) :
    goldenCenterFromChords a b i = goldenCanonicalCenter a b i := by
  fin_cases i
  · simpa [goldenCanonicalCenter] using goldenCenterFromChords_zero a b
  · simpa [goldenCanonicalCenter] using goldenCenterFromChords_one a b
  · simpa [goldenCanonicalCenter] using goldenCenterFromChords_two a b
  · simpa [goldenCanonicalCenter] using goldenCenterFromChords_three a b

/-! ## Collinearity determinants -/

/-- In the reindexed centre table this is the manuscript determinant
`det(q₂,q₃,q₄)`. -/
theorem goldenCanonicalCenter_det_q123 (a b : ℝ) :
    Matrix.det ![
      goldenCanonicalCenter a b 1,
      goldenCanonicalCenter a b 2,
      goldenCanonicalCenter a b 3] = a + b - 1 := by
  simp [goldenCanonicalCenter, Matrix.det_fin_three]
  ring

/-- In the reindexed centre table this is the manuscript determinant
`det(q₁,q₃,q₄)`. -/
theorem goldenCanonicalCenter_det_q023 (a b : ℝ) :
    Matrix.det ![
      goldenCanonicalCenter a b 0,
      goldenCanonicalCenter a b 2,
      goldenCanonicalCenter a b 3] = a - b ^ 2 := by
  simp [goldenCanonicalCenter, Matrix.det_fin_three]
  ring

/-! ## Concurrency determinants -/

/-- The three line covectors for the representative in which the third
matching edge is an end edge. -/
def goldenEndConcurrencyLines (a b : ℝ) : Fin 3 → Homogeneous3 :=
  ![
    crossProduct (goldenCanonicalCenter a b 0)
      (projectiveFiveNormalPoint a b 1),
    crossProduct (goldenCanonicalCenter a b 2)
      (projectiveFiveNormalPoint a b 3),
    crossProduct (goldenCanonicalCenter a b 1)
      (projectiveFiveNormalPoint a b 2)
  ]

/-- The three line covectors for the representative in which the third
matching edge is the middle edge. -/
def goldenMiddleConcurrencyLines (a b : ℝ) : Fin 3 → Homogeneous3 :=
  ![
    crossProduct (goldenCanonicalCenter a b 0)
      (projectiveFiveNormalPoint a b 1),
    crossProduct (goldenCanonicalCenter a b 2)
      (projectiveFiveNormalPoint a b 3),
    crossProduct (projectiveFiveNormalPoint a b 2)
      (projectiveFiveNormalPoint a b 4)
  ]

/-- Expanded line-covector matrix for the end-edge representative. -/
theorem goldenEndConcurrencyLines_eq_matrix (a b : ℝ) :
    goldenEndConcurrencyLines a b =
      ![![b - 1, 0, a - b], ![b - 1, 1, -b], ![1, -a, 0]] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [goldenEndConcurrencyLines, goldenCanonicalCenter,
      projectiveFiveNormalPoint, cross_apply]

/-- Expanded line-covector matrix for the middle-edge representative. -/
theorem goldenMiddleConcurrencyLines_eq_matrix (a b : ℝ) :
    goldenMiddleConcurrencyLines a b =
      ![![b - 1, 0, a - b], ![b - 1, 1, -b], ![-b, a, 0]] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [goldenMiddleConcurrencyLines, goldenCanonicalCenter,
      projectiveFiveNormalPoint, cross_apply]

/-- Exact concurrency determinant for the end-edge orbit. -/
theorem goldenEndConcurrencyLines_det (a b : ℝ) :
    Matrix.det (goldenEndConcurrencyLines a b) =
      -(a - 1) * (a * b - a + b) := by
  rw [goldenEndConcurrencyLines_eq_matrix]
  simp [Matrix.det_fin_three]
  ring

/-- Exact concurrency determinant for the middle-edge orbit. -/
theorem goldenMiddleConcurrencyLines_det (a b : ℝ) :
    Matrix.det (goldenMiddleConcurrencyLines a b) =
      a ^ 2 * b - a ^ 2 + a * b - b ^ 2 := by
  rw [goldenMiddleConcurrencyLines_eq_matrix]
  simp [Matrix.det_fin_three]
  ring

/-! ## Algebraic incompatibility on the golden wall -/

private theorem goldenEndScalar_not_realizable
    {a b : ℝ}
    (hq123 : a + b - 1 = 0)
    (hq023 : a - b ^ 2 = 0)
    (hend : -(a - 1) * (a * b - a + b) = 0) : False := by
  have ha : a = 1 - b := by
    nlinarith [hq123]
  have hab : a = b ^ 2 := by
    nlinarith [hq023]
  have hgolden : b ^ 2 + b - 1 = 0 := by
    nlinarith [ha, hab]
  have hlinear : 4 - 6 * b = 0 := by
    calc
      4 - 6 * b =
          (-(a - 1) * (a * b - a + b)) -
            (4 - b) * (b ^ 2 + b - 1) := by
              rw [ha]
              ring
      _ = 0 := by rw [hend, hgolden]; ring
  nlinarith [hgolden, hlinear]

private theorem goldenMiddleScalar_not_realizable
    {a b : ℝ}
    (hq123 : a + b - 1 = 0)
    (hq023 : a - b ^ 2 = 0)
    (hmiddle : a ^ 2 * b - a ^ 2 + a * b - b ^ 2 = 0) : False := by
  have ha : a = 1 - b := by
    nlinarith [hq123]
  have hab : a = b ^ 2 := by
    nlinarith [hq023]
  have hgolden : b ^ 2 + b - 1 = 0 := by
    nlinarith [ha, hab]
  have hlinear : 11 * b - 7 = 0 := by
    calc
      11 * b - 7 =
          (a ^ 2 * b - a ^ 2 + a * b - b ^ 2) -
            (b - 6) * (b ^ 2 + b - 1) := by
              rw [ha]
              ring
      _ = 0 := by rw [hmiddle, hgolden]; ring
  nlinarith [hgolden, hlinear]

/-- The two golden-axis collinearity determinants cannot vanish together
with either representative concurrency determinant.  All hypotheses and
all conclusions are raw homogeneous-coordinate determinant equations, so
concurrency at infinity is included. -/
theorem goldenAxisDeterminants_not_realizable
    (a b : ℝ)
    (hq123 : Matrix.det ![
      goldenCanonicalCenter a b 1,
      goldenCanonicalCenter a b 2,
      goldenCanonicalCenter a b 3] = 0)
    (hq023 : Matrix.det ![
      goldenCanonicalCenter a b 0,
      goldenCanonicalCenter a b 2,
      goldenCanonicalCenter a b 3] = 0)
    (hconcurrency :
      Matrix.det (goldenEndConcurrencyLines a b) = 0 ∨
        Matrix.det (goldenMiddleConcurrencyLines a b) = 0) : False := by
  have hq123' : a + b - 1 = 0 := by
    simpa only [goldenCanonicalCenter_det_q123] using hq123
  have hq023' : a - b ^ 2 = 0 := by
    simpa only [goldenCanonicalCenter_det_q023] using hq023
  rcases hconcurrency with hend | hmiddle
  · have hend' : -(a - 1) * (a * b - a + b) = 0 := by
      simpa only [goldenEndConcurrencyLines_det] using hend
    exact goldenEndScalar_not_realizable hq123' hq023' hend'
  · have hmiddle' :
        a ^ 2 * b - a ^ 2 + a * b - b ^ 2 = 0 := by
      simpa only [goldenMiddleConcurrencyLines_det] using hmiddle
    exact goldenMiddleScalar_not_realizable hq123' hq023' hmiddle'

end Erdos506.Incidence
