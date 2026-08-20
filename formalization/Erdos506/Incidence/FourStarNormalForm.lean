import Erdos506.Incidence.FourStarRigidity
import Erdos506.Incidence.RadicalAxisFourFourGeometry

/-!
# Normal form of a real projective four-star

The four base-line covectors of a `FourStarProjectiveSkeleton` form a
complete quadrangle.  The canonical `projectiveCovectorFrame` therefore
sends them to the four standard covectors.  Incidence and non-incidence then
put the four transformed private points, up to nonzero point scales, in the
normal form used by `FourStarNormalDeterminants`.

This module performs that extraction.  It also transports every determinant
of three private points, and hence every `T`-line condition, to the normal
representatives.  Transport of the mixed `S`-determinants additionally needs
the covariance of the cross product under the contragredient line action and
is deliberately kept separate.
-/

namespace Erdos506.Incidence

open Matrix

/-! ## The canonical frame and its private points -/

/-- The canonical complete-quadrangle frame attached to the four base-line
covectors of a projective four-star. -/
noncomputable def FourStarProjectiveSkeleton.normalFrame
    (F : FourStarProjectiveSkeleton) :
    ProjectiveCovectorFrame F.baseLine :=
  projectiveCovectorFrame F.baseLine F.base_general_position

/-- A private point after applying the point action of the canonical
covector frame. -/
noncomputable def FourStarProjectiveSkeleton.transformedPrivatePoint
    (F : FourStarProjectiveSkeleton) : Fin 4 → Homogeneous3 :=
  fun i => projectivePointTransform F.normalFrame.G (F.privatePoint i)

/-- A transformed private point remains incident with its own standard base
line. -/
theorem FourStarProjectiveSkeleton.transformedPrivatePoint_on_base
    (F : FourStarProjectiveSkeleton) (i : Fin 4) :
    projectiveCovectorNormalLine i ⬝ᵥ F.transformedPrivatePoint i = 0 := by
  change projectiveCovectorNormalLine i ⬝ᵥ
    projectivePointTransform F.normalFrame.G (F.privatePoint i) = 0
  rw [projectiveCovectorFrame_incident_normal_iff F.normalFrame]
  simpa only [dotProduct_comm] using F.private_on_base i

/-- A transformed private point remains off each of the other three standard
base lines. -/
theorem FourStarProjectiveSkeleton.transformedPrivatePoint_off_base
    (F : FourStarProjectiveSkeleton) (i j : Fin 4) (hij : i ≠ j) :
    projectiveCovectorNormalLine j ⬝ᵥ F.transformedPrivatePoint i ≠ 0 := by
  intro hzero
  have hbase :=
    (projectiveCovectorFrame_incident_normal_iff F.normalFrame
      j (F.privatePoint i)).mp hzero
  exact F.private_off_base i j hij (by
    simpa only [dotProduct_comm] using hbase)

/-! ## Extracted normal-form data -/

/-- A projective four-star expressed in the scalar normal coordinates of
`FourStarNormalDeterminants`.

The equation `transformed_privatePoint` records the unavoidable independent
nonzero choice of homogeneous representative at each private point. -/
structure FourStarNormalForm (F : FourStarProjectiveSkeleton) where
  frame : ProjectiveCovectorFrame F.baseLine
  determinants : FourStarNormalDeterminants
  pointScale : Fin 4 → ℝ
  pointScale_ne_zero : ∀ i, pointScale i ≠ 0
  transformed_privatePoint : ∀ i,
    projectivePointTransform frame.G (F.privatePoint i) =
      pointScale i • fourStarNormalPrivatePoint determinants i

/-- Every real projective four-star admits the concrete scalar normal form.
The chosen frame is the canonical `projectiveCovectorFrame` of its four base
covectors. -/
noncomputable def FourStarProjectiveSkeleton.toNormalForm
    (F : FourStarProjectiveSkeleton) : FourStarNormalForm F := by
  classical
  let w : Fin 4 → Homogeneous3 := F.transformedPrivatePoint

  have hw00 : w 0 0 = 0 := by
    have h := F.transformedPrivatePoint_on_base 0
    simpa [w, projectiveCovectorNormalLine, dotProduct,
      Fin.sum_univ_three] using h
  have hw01 : w 0 1 ≠ 0 := by
    have h := F.transformedPrivatePoint_off_base 0 1 (by decide)
    simpa [w, projectiveCovectorNormalLine, dotProduct,
      Fin.sum_univ_three] using h
  have hw02 : w 0 2 ≠ 0 := by
    have h := F.transformedPrivatePoint_off_base 0 2 (by decide)
    simpa [w, projectiveCovectorNormalLine, dotProduct,
      Fin.sum_univ_three] using h
  have hw0sum : w 0 0 + w 0 1 + w 0 2 ≠ 0 := by
    have h := F.transformedPrivatePoint_off_base 0 3 (by decide)
    simpa [w, projectiveCovectorNormalLine, dotProduct,
      Fin.sum_univ_three] using h

  have hw11 : w 1 1 = 0 := by
    have h := F.transformedPrivatePoint_on_base 1
    simpa [w, projectiveCovectorNormalLine, dotProduct,
      Fin.sum_univ_three] using h
  have hw10 : w 1 0 ≠ 0 := by
    have h := F.transformedPrivatePoint_off_base 1 0 (by decide)
    simpa [w, projectiveCovectorNormalLine, dotProduct,
      Fin.sum_univ_three] using h
  have hw12 : w 1 2 ≠ 0 := by
    have h := F.transformedPrivatePoint_off_base 1 2 (by decide)
    simpa [w, projectiveCovectorNormalLine, dotProduct,
      Fin.sum_univ_three] using h
  have hw1sum : w 1 0 + w 1 1 + w 1 2 ≠ 0 := by
    have h := F.transformedPrivatePoint_off_base 1 3 (by decide)
    simpa [w, projectiveCovectorNormalLine, dotProduct,
      Fin.sum_univ_three] using h

  have hw22 : w 2 2 = 0 := by
    have h := F.transformedPrivatePoint_on_base 2
    simpa [w, projectiveCovectorNormalLine, dotProduct,
      Fin.sum_univ_three] using h
  have hw20 : w 2 0 ≠ 0 := by
    have h := F.transformedPrivatePoint_off_base 2 0 (by decide)
    simpa [w, projectiveCovectorNormalLine, dotProduct,
      Fin.sum_univ_three] using h
  have hw21 : w 2 1 ≠ 0 := by
    have h := F.transformedPrivatePoint_off_base 2 1 (by decide)
    simpa [w, projectiveCovectorNormalLine, dotProduct,
      Fin.sum_univ_three] using h
  have hw2sum : w 2 0 + w 2 1 + w 2 2 ≠ 0 := by
    have h := F.transformedPrivatePoint_off_base 2 3 (by decide)
    simpa [w, projectiveCovectorNormalLine, dotProduct,
      Fin.sum_univ_three] using h

  have hw3sum : w 3 0 + w 3 1 + w 3 2 = 0 := by
    have h := F.transformedPrivatePoint_on_base 3
    simpa [w, projectiveCovectorNormalLine, dotProduct,
      Fin.sum_univ_three] using h
  have hw30 : w 3 0 ≠ 0 := by
    have h := F.transformedPrivatePoint_off_base 3 0 (by decide)
    simpa [w, projectiveCovectorNormalLine, dotProduct,
      Fin.sum_univ_three] using h
  have hw31 : w 3 1 ≠ 0 := by
    have h := F.transformedPrivatePoint_off_base 3 1 (by decide)
    simpa [w, projectiveCovectorNormalLine, dotProduct,
      Fin.sum_univ_three] using h
  have hw32 : w 3 2 ≠ 0 := by
    have h := F.transformedPrivatePoint_off_base 3 2 (by decide)
    simpa [w, projectiveCovectorNormalLine, dotProduct,
      Fin.sum_univ_three] using h

  let a : ℝ := w 0 2 / w 0 1
  let b : ℝ := w 1 2 / w 1 0
  let c : ℝ := w 2 1 / w 2 0
  let d : ℝ := w 3 1 / w 3 0

  have ha0 : a ≠ 0 := div_ne_zero hw02 hw01
  have hb0 : b ≠ 0 := div_ne_zero hw12 hw10
  have hc0 : c ≠ 0 := div_ne_zero hw21 hw20
  have hd0 : d ≠ 0 := div_ne_zero hw31 hw30

  have haNeg : a ≠ -1 := by
    intro ha
    have hratio : w 0 2 = -(w 0 1) := by
      have hratio' : w 0 2 = (-1 : ℝ) * w 0 1 :=
        (div_eq_iff hw01).mp (by simpa [a] using ha)
      simpa using hratio'
    apply hw0sum
    rw [hw00, hratio]
    ring
  have hbNeg : b ≠ -1 := by
    intro hb
    have hratio : w 1 2 = -(w 1 0) := by
      have hratio' : w 1 2 = (-1 : ℝ) * w 1 0 :=
        (div_eq_iff hw10).mp (by simpa [b] using hb)
      simpa using hratio'
    apply hw1sum
    rw [hw11, hratio]
    ring
  have hcNeg : c ≠ -1 := by
    intro hc
    have hratio : w 2 1 = -(w 2 0) := by
      have hratio' : w 2 1 = (-1 : ℝ) * w 2 0 :=
        (div_eq_iff hw20).mp (by simpa [c] using hc)
      simpa using hratio'
    apply hw2sum
    rw [hw22, hratio]
    ring
  have hdNeg : d ≠ -1 := by
    intro hd
    have hratio : w 3 1 = -(w 3 0) := by
      have hratio' : w 3 1 = (-1 : ℝ) * w 3 0 :=
        (div_eq_iff hw30).mp (by simpa [d] using hd)
      simpa using hratio'
    apply hw32
    rw [hratio] at hw3sum
    linarith

  let normal : FourStarNormalDeterminants :=
    { a := a
      b := b
      c := c
      d := d
      a_ne_zero := ha0
      b_ne_zero := hb0
      c_ne_zero := hc0
      d_ne_zero := hd0
      a_ne_neg_one := haNeg
      b_ne_neg_one := hbNeg
      c_ne_neg_one := hcNeg
      d_ne_neg_one := hdNeg }
  let pointScale : Fin 4 → ℝ := ![w 0 1, w 1 0, w 2 0, w 3 0]
  have hscale : ∀ i, pointScale i ≠ 0 := by
    intro i
    fin_cases i <;> simp [pointScale, hw01, hw10, hw20, hw30]
  have hmap : ∀ i,
      w i = pointScale i • fourStarNormalPrivatePoint normal i := by
    intro i
    fin_cases i
    · ext j
      fin_cases j
      · simpa [pointScale, normal, fourStarNormalPrivatePoint] using hw00
      · simp [pointScale, normal, fourStarNormalPrivatePoint]
      · change w 0 2 = w 0 1 * (w 0 2 / w 0 1)
        field_simp [hw01]
    · ext j
      fin_cases j
      · simp [pointScale, normal, fourStarNormalPrivatePoint]
      · simpa [pointScale, normal, fourStarNormalPrivatePoint] using hw11
      · change w 1 2 = w 1 0 * (w 1 2 / w 1 0)
        field_simp [hw10]
    · ext j
      fin_cases j
      · simp [pointScale, normal, fourStarNormalPrivatePoint]
      · change w 2 1 = w 2 0 * (w 2 1 / w 2 0)
        field_simp [hw20]
      · simpa [pointScale, normal, fourStarNormalPrivatePoint] using hw22
    · ext j
      fin_cases j
      · simp [pointScale, normal, fourStarNormalPrivatePoint]
      · change w 3 1 = w 3 0 * (w 3 1 / w 3 0)
        field_simp [hw30]
      · change w 3 2 = w 3 0 * (-1 - w 3 1 / w 3 0)
        field_simp [hw30]; linarith [hw3sum]
  exact
    { frame := F.normalFrame
      determinants := normal
      pointScale := pointScale
      pointScale_ne_zero := hscale
      transformed_privatePoint := by
        intro i
        simpa only [w] using hmap i }

@[simp] theorem FourStarProjectiveSkeleton.toNormalForm_frame
    (F : FourStarProjectiveSkeleton) :
    F.toNormalForm.frame = F.normalFrame := rfl

/-! ## Transport of private-point determinants -/

private theorem fourStar_det_smul_three
    (a b c : ℝ) (u v w : Homogeneous3) :
    Matrix.det ![a • u, b • v, c • w] =
      (a * b * c) * Matrix.det ![u, v, w] := by
  simp [Matrix.det_fin_three]
  ring

/-- The point scales in a normal form do not affect vanishing of a
three-point determinant. -/
private theorem FourStarNormalForm.det_scaled_eq_zero_iff
    {F : FourStarProjectiveSkeleton} (N : FourStarNormalForm F)
    (i j k : Fin 4) :
    Matrix.det ![
        N.pointScale i • fourStarNormalPrivatePoint N.determinants i,
        N.pointScale j • fourStarNormalPrivatePoint N.determinants j,
        N.pointScale k • fourStarNormalPrivatePoint N.determinants k] = 0 ↔
      Matrix.det ![
        fourStarNormalPrivatePoint N.determinants i,
        fourStarNormalPrivatePoint N.determinants j,
        fourStarNormalPrivatePoint N.determinants k] = 0 := by
  rw [fourStar_det_smul_three]
  constructor
  · intro hzero
    exact (mul_eq_zero.mp hzero).resolve_left
      (mul_ne_zero
        (mul_ne_zero (N.pointScale_ne_zero i) (N.pointScale_ne_zero j))
        (N.pointScale_ne_zero k))
  · intro hzero
    rw [hzero, mul_zero]

/-- A `T`-determinant vanishes in the original projective skeleton exactly
when the corresponding determinant of the extracted normal representatives
vanishes. -/
theorem FourStarNormalForm.tDet_eq_zero_iff
    {F : FourStarProjectiveSkeleton} (N : FourStarNormalForm F)
    (i j k : Fin 4) :
    fourStarTDet F i j k = 0 ↔
      Matrix.det ![
        fourStarNormalPrivatePoint N.determinants i,
        fourStarNormalPrivatePoint N.determinants j,
        fourStarNormalPrivatePoint N.determinants k] = 0 := by
  have htransport := det_eq_zero_iff_generalLinear_smul_three
    N.frame.G (F.privatePoint i) (F.privatePoint j) (F.privatePoint k)
  change Matrix.det ![
      projectivePointTransform N.frame.G (F.privatePoint i),
      projectivePointTransform N.frame.G (F.privatePoint j),
      projectivePointTransform N.frame.G (F.privatePoint k)] = 0 ↔
    Matrix.det ![F.privatePoint i, F.privatePoint j,
      F.privatePoint k] = 0 at htransport
  rw [N.transformed_privatePoint i, N.transformed_privatePoint j,
    N.transformed_privatePoint k] at htransport
  change Matrix.det ![F.privatePoint i, F.privatePoint j,
    F.privatePoint k] = 0 ↔ _
  exact htransport.symm.trans (N.det_scaled_eq_zero_iff i j k)

/-- In particular, the normal polynomial `b + a*c` is the transported
`T₁₂₃` condition. -/
theorem FourStarNormalForm.t123_eq_zero_iff
    {F : FourStarProjectiveSkeleton} (N : FourStarNormalForm F) :
    fourStarTDet F 0 1 2 = 0 ↔
      N.determinants.b + N.determinants.a * N.determinants.c = 0 := by
  rw [N.tDet_eq_zero_iff, fourStarNormal_t123]

/-! ## Transport of opposite vertices and `S`-determinants -/

private theorem crossProduct_first_two_ne_zero_of_det_ne_zero
    {u v w : Homogeneous3} (hdet : Matrix.det ![u, v, w] ≠ 0) :
    crossProduct u v ≠ 0 := by
  intro hcross
  apply hdet
  calc
    Matrix.det ![u, v, w] = u ⬝ᵥ crossProduct v w :=
      (triple_product_eq_det u v w).symm
    _ = v ⬝ᵥ crossProduct w u := triple_product_permutation u v w
    _ = w ⬝ᵥ crossProduct u v := triple_product_permutation v w u
    _ = 0 := by rw [hcross, dotProduct_zero]

private theorem crossProduct_first_third_ne_zero_of_det_ne_zero
    {u v w : Homogeneous3} (hdet : Matrix.det ![u, v, w] ≠ 0) :
    crossProduct u w ≠ 0 := by
  intro hcross
  apply hdet
  calc
    Matrix.det ![u, v, w] = u ⬝ᵥ crossProduct v w :=
      (triple_product_eq_det u v w).symm
    _ = v ⬝ᵥ crossProduct w u := triple_product_permutation u v w
    _ = v ⬝ᵥ (-crossProduct u w) := by rw [cross_anticomm]
    _ = 0 := by rw [hcross]; simp

private theorem crossProduct_last_two_ne_zero_of_det_ne_zero
    {u v w : Homogeneous3} (hdet : Matrix.det ![u, v, w] ≠ 0) :
    crossProduct v w ≠ 0 := by
  intro hcross
  apply hdet
  calc
    Matrix.det ![u, v, w] = u ⬝ᵥ crossProduct v w :=
      (triple_product_eq_det u v w).symm
    _ = 0 := by rw [hcross, dotProduct_zero]

private theorem FourStarProjectiveSkeleton.oppositeVertex_ne_zero
    (F : FourStarProjectiveSkeleton) (k l : Fin 4) (hkl : k ≠ l) :
    fourStarOppositeVertex F.baseLine k l ≠ 0 := by
  have h01 : crossProduct (F.baseLine 0) (F.baseLine 1) ≠ 0 :=
    crossProduct_first_two_ne_zero_of_det_ne_zero
      F.base_general_position.det_abc_ne
  have h02 : crossProduct (F.baseLine 0) (F.baseLine 2) ≠ 0 :=
    crossProduct_first_third_ne_zero_of_det_ne_zero
      F.base_general_position.det_abc_ne
  have h03 : crossProduct (F.baseLine 0) (F.baseLine 3) ≠ 0 :=
    crossProduct_first_third_ne_zero_of_det_ne_zero
      F.base_general_position.det_abd_ne
  have h12 : crossProduct (F.baseLine 1) (F.baseLine 2) ≠ 0 :=
    crossProduct_last_two_ne_zero_of_det_ne_zero
      F.base_general_position.det_abc_ne
  have h13 : crossProduct (F.baseLine 1) (F.baseLine 3) ≠ 0 :=
    crossProduct_last_two_ne_zero_of_det_ne_zero
      F.base_general_position.det_abd_ne
  have h23 : crossProduct (F.baseLine 2) (F.baseLine 3) ≠ 0 :=
    crossProduct_last_two_ne_zero_of_det_ne_zero
      F.base_general_position.det_acd_ne
  have h10 : crossProduct (F.baseLine 1) (F.baseLine 0) ≠ 0 := by
    rw [← cross_anticomm]
    exact neg_ne_zero.mpr h01
  have h20 : crossProduct (F.baseLine 2) (F.baseLine 0) ≠ 0 := by
    rw [← cross_anticomm]
    exact neg_ne_zero.mpr h02
  have h30 : crossProduct (F.baseLine 3) (F.baseLine 0) ≠ 0 := by
    rw [← cross_anticomm]
    exact neg_ne_zero.mpr h03
  have h21 : crossProduct (F.baseLine 2) (F.baseLine 1) ≠ 0 := by
    rw [← cross_anticomm]
    exact neg_ne_zero.mpr h12
  have h31 : crossProduct (F.baseLine 3) (F.baseLine 1) ≠ 0 := by
    rw [← cross_anticomm]
    exact neg_ne_zero.mpr h13
  have h32 : crossProduct (F.baseLine 3) (F.baseLine 2) ≠ 0 := by
    rw [← cross_anticomm]
    exact neg_ne_zero.mpr h23
  fin_cases k <;> fin_cases l <;> simp_all [fourStarOppositeVertex]

private theorem projectiveCovectorNormalLine_ne_zero (i : Fin 4) :
    projectiveCovectorNormalLine i ≠ 0 := by
  fin_cases i <;> simp [projectiveCovectorNormalLine]

private theorem normalOppositeVertex_ne_zero
    (k l : Fin 4) (hkl : k ≠ l) :
    crossProduct (projectiveCovectorNormalLine k)
      (projectiveCovectorNormalLine l) ≠ 0 := by
  fin_cases k <;> fin_cases l <;>
    simp_all [projectiveCovectorNormalLine, cross_apply]

/-- The transformed intersection of two distinct base lines is the
intersection of their two normal covectors, up to homogeneous scale. -/
private theorem FourStarNormalForm.transformed_oppositeVertex_projective_eq
    {F : FourStarProjectiveSkeleton} (N : FourStarNormalForm F)
    (k l : Fin 4)
    (hmapped : projectivePointTransform N.frame.G
      (fourStarOppositeVertex F.baseLine k l) ≠ 0)
    (hnormal : crossProduct (projectiveCovectorNormalLine k)
      (projectiveCovectorNormalLine l) ≠ 0) :
    Projectivization.mk ℝ
        (projectivePointTransform N.frame.G
          (fourStarOppositeVertex F.baseLine k l)) hmapped =
      Projectivization.mk ℝ
        (crossProduct (projectiveCovectorNormalLine k)
          (projectiveCovectorNormalLine l)) hnormal := by
  have hk0 := projectiveCovectorNormalLine_ne_zero k
  have hl0 := projectiveCovectorNormalLine_ne_zero l
  have hlines :
      Projectivization.mk ℝ (projectiveCovectorNormalLine k) hk0 ≠
        Projectivization.mk ℝ (projectiveCovectorNormalLine l) hl0 := by
    intro heq
    apply hnormal
    exact (Projectivization.mk_eq_mk_iff_crossProduct_eq_zero hk0 hl0).1 heq
  have hkInc : projectiveCovectorNormalLine k ⬝ᵥ
      projectivePointTransform N.frame.G
        (fourStarOppositeVertex F.baseLine k l) = 0 := by
    apply (projectiveCovectorFrame_incident_normal_iff N.frame k _).2
    simpa only [fourStarOppositeVertex] using
      dot_self_cross (F.baseLine k) (F.baseLine l)
  have hlInc : projectiveCovectorNormalLine l ⬝ᵥ
      projectivePointTransform N.frame.G
        (fourStarOppositeVertex F.baseLine k l) = 0 := by
    apply (projectiveCovectorFrame_incident_normal_iff N.frame l _).2
    simpa only [fourStarOppositeVertex] using
      dot_cross_self (F.baseLine k) (F.baseLine l)
  have hkOrth : Projectivization.orthogonal
      (Projectivization.mk ℝ (projectiveCovectorNormalLine k) hk0)
      (Projectivization.mk ℝ
        (projectivePointTransform N.frame.G
          (fourStarOppositeVertex F.baseLine k l)) hmapped) :=
    (Projectivization.orthogonal_mk hk0 hmapped).2 hkInc
  have hlOrth : Projectivization.orthogonal
      (Projectivization.mk ℝ (projectiveCovectorNormalLine l) hl0)
      (Projectivization.mk ℝ
        (projectivePointTransform N.frame.G
          (fourStarOppositeVertex F.baseLine k l)) hmapped) :=
    (Projectivization.orthogonal_mk hl0 hmapped).2 hlInc
  calc
    Projectivization.mk ℝ
        (projectivePointTransform N.frame.G
          (fourStarOppositeVertex F.baseLine k l)) hmapped =
        Projectivization.cross
          (Projectivization.mk ℝ (projectiveCovectorNormalLine k) hk0)
          (Projectivization.mk ℝ (projectiveCovectorNormalLine l) hl0) :=
      projectiveCovector_eq_cross_of_orthogonal hlines hkOrth hlOrth
    _ = Projectivization.mk ℝ
        (crossProduct (projectiveCovectorNormalLine k)
          (projectiveCovectorNormalLine l)) hnormal := by
      rw [Projectivization.cross_mk_of_ne hk0 hl0 hlines]

/-- Every mixed `S`-determinant is transported exactly at the level of
vanishing.  Distinctness of the two opposite base lines is the only needed
index condition. -/
theorem FourStarNormalForm.sDet_eq_zero_iff
    {F : FourStarProjectiveSkeleton} (N : FourStarNormalForm F)
    (i j k l : Fin 4) (hkl : k ≠ l) :
    fourStarSDet F i j k l = 0 ↔
      Matrix.det ![
        fourStarNormalPrivatePoint N.determinants i,
        fourStarNormalPrivatePoint N.determinants j,
        crossProduct (projectiveCovectorNormalLine k)
          (projectiveCovectorNormalLine l)] = 0 := by
  let v := fourStarOppositeVertex F.baseLine k l
  let vn := crossProduct (projectiveCovectorNormalLine k)
    (projectiveCovectorNormalLine l)
  have hv : v ≠ 0 := by
    simpa only [v] using F.oppositeVertex_ne_zero k l hkl
  have hvn : vn ≠ 0 := by
    simpa only [vn] using normalOppositeVertex_ne_zero k l hkl
  have hvmapped : projectivePointTransform N.frame.G v ≠ 0 :=
    (smul_ne_zero_iff_ne N.frame.G).mpr hv
  have hsi : N.pointScale i •
      fourStarNormalPrivatePoint N.determinants i ≠ 0 := by
    rw [← N.transformed_privatePoint i]
    exact (smul_ne_zero_iff_ne N.frame.G).mpr (F.private_ne_zero i)
  have hsj : N.pointScale j •
      fourStarNormalPrivatePoint N.determinants j ≠ 0 := by
    rw [← N.transformed_privatePoint j]
    exact (smul_ne_zero_iff_ne N.frame.G).mpr (F.private_ne_zero j)
  have hni : fourStarNormalPrivatePoint N.determinants i ≠ 0 := by
    intro hzero
    apply hsi
    rw [hzero, smul_zero]
  have hnj : fourStarNormalPrivatePoint N.determinants j ≠ 0 := by
    intro hzero
    apply hsj
    rw [hzero, smul_zero]
  have hpi : Projectivization.mk ℝ
      (N.pointScale i • fourStarNormalPrivatePoint N.determinants i) hsi =
      Projectivization.mk ℝ
        (fourStarNormalPrivatePoint N.determinants i) hni :=
    (Projectivization.mk_eq_mk_iff' ℝ _ _ hsi hni).2
      ⟨N.pointScale i, rfl⟩
  have hpj : Projectivization.mk ℝ
      (N.pointScale j • fourStarNormalPrivatePoint N.determinants j) hsj =
      Projectivization.mk ℝ
        (fourStarNormalPrivatePoint N.determinants j) hnj :=
    (Projectivization.mk_eq_mk_iff' ℝ _ _ hsj hnj).2
      ⟨N.pointScale j, rfl⟩
  have hpv : Projectivization.mk ℝ
      (projectivePointTransform N.frame.G v) hvmapped =
      Projectivization.mk ℝ vn hvn := by
    simpa only [v, vn] using
      N.transformed_oppositeVertex_projective_eq k l hvmapped hvn
  have hrepresentatives := det_eq_zero_iff_of_projective_mk_eq
    hsi hsj hvmapped hni hnj hvn hpi hpj hpv
  have htransport := det_eq_zero_iff_generalLinear_smul_three
    N.frame.G (F.privatePoint i) (F.privatePoint j) v
  change Matrix.det ![
      projectivePointTransform N.frame.G (F.privatePoint i),
      projectivePointTransform N.frame.G (F.privatePoint j),
      projectivePointTransform N.frame.G v] = 0 ↔
    Matrix.det ![F.privatePoint i, F.privatePoint j, v] = 0 at htransport
  rw [N.transformed_privatePoint i,
    N.transformed_privatePoint j] at htransport
  change Matrix.det ![F.privatePoint i, F.privatePoint j, v] = 0 ↔ _
  exact htransport.symm.trans hrepresentatives

theorem FourStarNormalForm.s12_eq_zero_iff
    {F : FourStarProjectiveSkeleton} (N : FourStarNormalForm F) :
    fourStarSDet F 0 1 2 3 = 0 ↔
      N.determinants.a - N.determinants.b = 0 := by
  rw [N.sDet_eq_zero_iff 0 1 2 3 (by decide), fourStarNormal_s12]

theorem FourStarNormalForm.s13_eq_zero_iff
    {F : FourStarProjectiveSkeleton} (N : FourStarNormalForm F) :
    fourStarSDet F 0 2 1 3 = 0 ↔
      1 - N.determinants.a * N.determinants.c = 0 := by
  rw [N.sDet_eq_zero_iff 0 2 1 3 (by decide), fourStarNormal_s13]

theorem FourStarNormalForm.s14_eq_zero_iff
    {F : FourStarProjectiveSkeleton} (N : FourStarNormalForm F) :
    fourStarSDet F 0 3 1 2 = 0 ↔
      1 + N.determinants.d * (1 + N.determinants.a) = 0 := by
  rw [N.sDet_eq_zero_iff 0 3 1 2 (by decide), fourStarNormal_s14,
    neg_eq_zero]

theorem FourStarNormalForm.s23_eq_zero_iff
    {F : FourStarProjectiveSkeleton} (N : FourStarNormalForm F) :
    fourStarSDet F 1 2 0 3 = 0 ↔
      N.determinants.c - N.determinants.b = 0 := by
  rw [N.sDet_eq_zero_iff 1 2 0 3 (by decide), fourStarNormal_s23]

theorem FourStarNormalForm.s24_eq_zero_iff
    {F : FourStarProjectiveSkeleton} (N : FourStarNormalForm F) :
    fourStarSDet F 1 3 0 2 = 0 ↔
      1 + N.determinants.d + N.determinants.b = 0 := by
  rw [N.sDet_eq_zero_iff 1 3 0 2 (by decide), fourStarNormal_s24,
    neg_eq_zero]

theorem FourStarNormalForm.s34_eq_zero_iff
    {F : FourStarProjectiveSkeleton} (N : FourStarNormalForm F) :
    fourStarSDet F 2 3 0 1 = 0 ↔
      N.determinants.d - N.determinants.c = 0 := by
  rw [N.sDet_eq_zero_iff 2 3 0 1 (by decide), fourStarNormal_s34]

end Erdos506.Incidence
