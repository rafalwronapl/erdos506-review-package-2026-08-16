import Erdos506.Incidence.RealProjectiveHarmonic

/-!
# At most two harmonic deletions from five real projective points

For a five-element subset `P` of the real projective line, call `p ∈ P`
harmonic when `P.erase p` is an order-free harmonic four-set.  This file
proves that at most two points of `P` are harmonic.

The proof normalizes three fixed points to `0`, `∞`, and `1`.  A fourth
point making a harmonic four-set then has affine coordinate in
`{-1, 1/2, 2}`.  Three harmonic deletions would give two distinct members
of this set which themselves form a harmonic pair relative to `0,∞`; the
three possible harmonic equations rule this out.
-/

namespace Erdos506.Incidence

open Matrix
open scoped LinearAlgebra.Projectivization

/-! ## Representative and symmetry lemmas -/

private theorem realProjectiveBracket_rep_ne_zero_of_ne
    {P Q : RealProjectiveOnePoint} (hPQ : P ≠ Q) :
    realProjectiveBracket P.rep Q.rep ≠ 0 := by
  intro hzero
  apply hPQ
  calc
    P = Projectivization.mk ℝ P.rep P.rep_nonzero :=
      (Projectivization.mk_rep P).symm
    _ = Projectivization.mk ℝ Q.rep Q.rep_nonzero :=
      (realProjective_mk_eq_mk_iff_bracket_eq_zero
        P.rep_nonzero Q.rep_nonzero).mpr hzero
    _ = Q := Projectivization.mk_rep Q

private theorem realProjectiveHarmonic_mk_iff
    {p q r s : RealProjectiveLineVector}
    (hp : p ≠ 0) (hq : q ≠ 0) (hr : r ≠ 0) (hs : s ≠ 0) :
    RealProjectiveHarmonic
        (Projectivization.mk ℝ p hp) (Projectivization.mk ℝ q hq)
        (Projectivization.mk ℝ r hr) (Projectivization.mk ℝ s hs) ↔
      realProjectiveBracket p r * realProjectiveBracket q s +
        realProjectiveBracket p s * realProjectiveBracket q r = 0 := by
  constructor
  · rintro ⟨p', q', r', s', hp', hq', hr', hs',
      hP, hQ, hR, hS, hharmonic⟩
    obtain ⟨ap, hap⟩ :=
      (Projectivization.mk_eq_mk_iff' ℝ p p' hp hp').mp hP
    obtain ⟨aq, haq⟩ :=
      (Projectivization.mk_eq_mk_iff' ℝ q q' hq hq').mp hQ
    obtain ⟨ar, har⟩ :=
      (Projectivization.mk_eq_mk_iff' ℝ r r' hr hr').mp hR
    obtain ⟨as, has⟩ :=
      (Projectivization.mk_eq_mk_iff' ℝ s s' hs hs').mp hS
    rw [← hap, ← haq, ← har, ← has,
      realProjectiveBracket_smul, realProjectiveBracket_smul,
      realProjectiveBracket_smul, realProjectiveBracket_smul]
    calc
      (ap * ar) * realProjectiveBracket p' r' *
            ((aq * as) * realProjectiveBracket q' s') +
          (ap * as) * realProjectiveBracket p' s' *
            ((aq * ar) * realProjectiveBracket q' r') =
          (ap * aq * ar * as) *
            (realProjectiveBracket p' r' * realProjectiveBracket q' s' +
              realProjectiveBracket p' s' * realProjectiveBracket q' r') := by
        ring
      _ = 0 := by rw [hharmonic, mul_zero]
  · exact realProjectiveHarmonic_mk hp hq hr hs

private theorem realProjectiveHarmonic_iff_rep
    (P Q R S : RealProjectiveOnePoint) :
    RealProjectiveHarmonic P Q R S ↔
      realProjectiveBracket P.rep R.rep *
          realProjectiveBracket Q.rep S.rep +
      realProjectiveBracket P.rep S.rep *
          realProjectiveBracket Q.rep R.rep = 0 := by
  constructor
  · intro h
    have h' : RealProjectiveHarmonic
        (Projectivization.mk ℝ P.rep P.rep_nonzero)
        (Projectivization.mk ℝ Q.rep Q.rep_nonzero)
        (Projectivization.mk ℝ R.rep R.rep_nonzero)
        (Projectivization.mk ℝ S.rep S.rep_nonzero) := by
      simpa only [Projectivization.mk_rep] using h
    exact (realProjectiveHarmonic_mk_iff
      P.rep_nonzero Q.rep_nonzero R.rep_nonzero S.rep_nonzero).mp h'
  · intro h
    have h' := (realProjectiveHarmonic_mk_iff
      P.rep_nonzero Q.rep_nonzero R.rep_nonzero S.rep_nonzero).mpr h
    simpa only [Projectivization.mk_rep] using h'

private theorem realProjectiveHarmonic_swap_left
    {P Q R S : RealProjectiveOnePoint}
    (h : RealProjectiveHarmonic P Q R S) :
    RealProjectiveHarmonic Q P R S := by
  rw [realProjectiveHarmonic_iff_rep] at h ⊢
  linear_combination h

private theorem realProjectiveHarmonic_swap_right
    {P Q R S : RealProjectiveOnePoint}
    (h : RealProjectiveHarmonic P Q R S) :
    RealProjectiveHarmonic P Q S R := by
  rw [realProjectiveHarmonic_iff_rep] at h ⊢
  linear_combination h

private theorem realProjectiveHarmonic_swap_pairs
    {P Q R S : RealProjectiveOnePoint}
    (h : RealProjectiveHarmonic P Q R S) :
    RealProjectiveHarmonic R S P Q := by
  rw [realProjectiveHarmonic_iff_rep] at h ⊢
  rw [realProjectiveBracket_swap P.rep R.rep,
    realProjectiveBracket_swap Q.rep S.rep,
    realProjectiveBracket_swap Q.rep R.rep,
    realProjectiveBracket_swap P.rep S.rep]
  linear_combination h

/-! ## A three-point projective frame -/

/-- The explicit matrix which sends `X,Y,A` to `0,∞,1`. -/
noncomputable def realProjectiveTripleFrameMatrix
    (X Y A : RealProjectiveOnePoint) : Matrix (Fin 2) (Fin 2) ℝ :=
  ![![-X.rep 1 / realProjectiveBracket X.rep A.rep,
        X.rep 0 / realProjectiveBracket X.rep A.rep],
    ![Y.rep 1 / realProjectiveBracket A.rep Y.rep,
        -Y.rep 0 / realProjectiveBracket A.rep Y.rep]]

theorem realProjectiveTripleFrameMatrix_det
    (X Y A : RealProjectiveOnePoint)
    (hXY : X ≠ Y) (hXA : X ≠ A) (hAY : A ≠ Y) :
    (realProjectiveTripleFrameMatrix X Y A).det =
      -realProjectiveBracket X.rep Y.rep /
        (realProjectiveBracket X.rep A.rep *
          realProjectiveBracket A.rep Y.rep) := by
  have hxy := realProjectiveBracket_rep_ne_zero_of_ne hXY
  have hxa := realProjectiveBracket_rep_ne_zero_of_ne hXA
  have hay := realProjectiveBracket_rep_ne_zero_of_ne hAY
  simp only [realProjectiveTripleFrameMatrix, Matrix.det_fin_two,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  field_simp [hxy, hxa, hay]
  simp only [realProjectiveBracket]
  ring

/-- The projectivity normalizing three distinct points to `0,∞,1`. -/
noncomputable def realProjectiveTripleFrame
    (X Y A : RealProjectiveOnePoint)
    (hXY : X ≠ Y) (hXA : X ≠ A) (hAY : A ≠ Y) : GL (Fin 2) ℝ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero
    (realProjectiveTripleFrameMatrix X Y A)
    (by
      rw [realProjectiveTripleFrameMatrix_det X Y A hXY hXA hAY]
      exact div_ne_zero
        (neg_ne_zero.mpr (realProjectiveBracket_rep_ne_zero_of_ne hXY))
        (mul_ne_zero
          (realProjectiveBracket_rep_ne_zero_of_ne hXA)
          (realProjectiveBracket_rep_ne_zero_of_ne hAY)))

private theorem realProjectiveTripleFrame_smul_vector
    (X Y A : RealProjectiveOnePoint)
    (hXY : X ≠ Y) (hXA : X ≠ A) (hAY : A ≠ Y)
    (u : RealProjectiveLineVector) :
    realProjectiveTripleFrame X Y A hXY hXA hAY • u =
      ![realProjectiveBracket X.rep u /
          realProjectiveBracket X.rep A.rep,
        realProjectiveBracket u Y.rep /
          realProjectiveBracket A.rep Y.rep] := by
  change realProjectiveTripleFrameMatrix X Y A *ᵥ u = _
  funext i
  fin_cases i
  · simp [realProjectiveTripleFrameMatrix, Matrix.mulVec, dotProduct,
      Fin.sum_univ_two, realProjectiveBracket]
    ring
  · simp [realProjectiveTripleFrameMatrix, Matrix.mulVec, dotProduct,
      Fin.sum_univ_two, realProjectiveBracket]
    ring

theorem realProjectiveTripleFrame_smul_left
    (X Y A : RealProjectiveOnePoint)
    (hXY : X ≠ Y) (hXA : X ≠ A) (hAY : A ≠ Y) :
    realProjectiveTripleFrame X Y A hXY hXA hAY • X =
      realProjectiveLineZero := by
  let g := realProjectiveTripleFrame X Y A hXY hXA hAY
  let hmap : g • X.rep ≠ 0 :=
    (smul_ne_zero_iff_ne g).mpr X.rep_nonzero
  have hraw : Projectivization.mk ℝ (g • X.rep) hmap =
      realProjectiveLineZero := by
    apply (realProjective_mk_eq_mk_iff_bracket_eq_zero
      hmap realProjectiveLineZeroVector_ne_zero).mpr
    change realProjectiveBracket
      (realProjectiveTripleFrame X Y A hXY hXA hAY • X.rep)
      realProjectiveLineZeroVector = 0
    rw [realProjectiveTripleFrame_smul_vector]
    simp [realProjectiveLineZeroVector, realProjectiveBracket]
    left
    ring
  calc
    realProjectiveTripleFrame X Y A hXY hXA hAY • X =
        g • Projectivization.mk ℝ X.rep X.rep_nonzero := by
      rw [Projectivization.mk_rep]
    _ = Projectivization.mk ℝ (g • X.rep) hmap := by
      rw [Projectivization.smul_mk]
    _ = realProjectiveLineZero := hraw

theorem realProjectiveTripleFrame_smul_right
    (X Y A : RealProjectiveOnePoint)
    (hXY : X ≠ Y) (hXA : X ≠ A) (hAY : A ≠ Y) :
    realProjectiveTripleFrame X Y A hXY hXA hAY • Y =
      realProjectiveLineInfinity := by
  let g := realProjectiveTripleFrame X Y A hXY hXA hAY
  let hmap : g • Y.rep ≠ 0 :=
    (smul_ne_zero_iff_ne g).mpr Y.rep_nonzero
  have hraw : Projectivization.mk ℝ (g • Y.rep) hmap =
      realProjectiveLineInfinity := by
    apply (realProjective_mk_eq_mk_iff_bracket_eq_zero
      hmap realProjectiveLineInfinityVector_ne_zero).mpr
    change realProjectiveBracket
      (realProjectiveTripleFrame X Y A hXY hXA hAY • Y.rep)
      realProjectiveLineInfinityVector = 0
    rw [realProjectiveTripleFrame_smul_vector]
    simp [realProjectiveLineInfinityVector, realProjectiveBracket]
    left
    ring
  calc
    realProjectiveTripleFrame X Y A hXY hXA hAY • Y =
        g • Projectivization.mk ℝ Y.rep Y.rep_nonzero := by
      rw [Projectivization.mk_rep]
    _ = Projectivization.mk ℝ (g • Y.rep) hmap := by
      rw [Projectivization.smul_mk]
    _ = realProjectiveLineInfinity := hraw

theorem realProjectiveTripleFrame_smul_one
    (X Y A : RealProjectiveOnePoint)
    (hXY : X ≠ Y) (hXA : X ≠ A) (hAY : A ≠ Y) :
    realProjectiveTripleFrame X Y A hXY hXA hAY • A =
      realProjectiveLineOne := by
  have hxa := realProjectiveBracket_rep_ne_zero_of_ne hXA
  have hay := realProjectiveBracket_rep_ne_zero_of_ne hAY
  have hxa' :
      X.rep 0 * A.rep 1 - X.rep 1 * A.rep 0 ≠ 0 := by
    simpa only [realProjectiveBracket] using hxa
  have hay' :
      A.rep 0 * Y.rep 1 - A.rep 1 * Y.rep 0 ≠ 0 := by
    simpa only [realProjectiveBracket] using hay
  let g := realProjectiveTripleFrame X Y A hXY hXA hAY
  let hmap : g • A.rep ≠ 0 :=
    (smul_ne_zero_iff_ne g).mpr A.rep_nonzero
  have hraw : Projectivization.mk ℝ (g • A.rep) hmap =
      realProjectiveLineOne := by
    apply (realProjective_mk_eq_mk_iff_bracket_eq_zero
      hmap realProjectiveLineOneVector_ne_zero).mpr
    change realProjectiveBracket
      (realProjectiveTripleFrame X Y A hXY hXA hAY • A.rep)
      realProjectiveLineOneVector = 0
    rw [realProjectiveTripleFrame_smul_vector]
    simp only [realProjectiveLineOneVector, realProjectiveBracket,
      Matrix.cons_val_zero, Matrix.cons_val_one]
    field_simp [hxa', hay']
    norm_num
  calc
    realProjectiveTripleFrame X Y A hXY hXA hAY • A =
        g • Projectivization.mk ℝ A.rep A.rep_nonzero := by
      rw [Projectivization.mk_rep]
    _ = Projectivization.mk ℝ (g • A.rep) hmap := by
      rw [Projectivization.smul_mk]
    _ = realProjectiveLineOne := hraw

/-! ## The finite affine chart and harmonic values -/

private def harmonicFiveAffineVector (t : ℝ) : RealProjectiveLineVector :=
  ![t, 1]

private theorem harmonicFiveAffineVector_ne_zero (t : ℝ) :
    harmonicFiveAffineVector t ≠ 0 := by
  intro hzero
  have hone := congrFun hzero (1 : Fin 2)
  simp [harmonicFiveAffineVector] at hone

private noncomputable def harmonicFiveAffinePoint (t : ℝ) :
    RealProjectiveOnePoint :=
  Projectivization.mk ℝ (harmonicFiveAffineVector t)
    (harmonicFiveAffineVector_ne_zero t)

/-- A named four-element presentation, avoiding a global classical
`DecidableEq` instance in theorem signatures. -/
private noncomputable def realProjectiveFourSet
    (A B C D : RealProjectiveOnePoint) : Finset RealProjectiveOnePoint := by
  classical
  exact {A, B, C, D}

private theorem realProjectiveFourSet_rotate
    (A B C D : RealProjectiveOnePoint) :
    realProjectiveFourSet A B C D =
      realProjectiveFourSet C D A B := by
  classical
  ext Z
  simp only [realProjectiveFourSet, Finset.mem_insert,
    Finset.mem_singleton]
  tauto

private theorem image_realProjectiveFourSet
    [DecidableEq RealProjectiveOnePoint]
    (f : RealProjectiveOnePoint → RealProjectiveOnePoint)
    (A B C D : RealProjectiveOnePoint) :
    (realProjectiveFourSet A B C D).image f =
      realProjectiveFourSet (f A) (f B) (f C) (f D) := by
  classical
  simp [realProjectiveFourSet]
  apply Finset.ext
  intro Z
  simp

private theorem realProjectiveThreeSet_card_ne_four
    [DecidableEq RealProjectiveOnePoint]
    (A B C : RealProjectiveOnePoint) :
    ({A, B, C} : Finset RealProjectiveOnePoint).card ≠ 4 := by
  intro hcard
  have hle : ({A, B, C} : Finset RealProjectiveOnePoint).card ≤ 3 :=
    Finset.card_le_three
  omega

private theorem realProjective_eq_harmonicFiveAffinePoint_of_ne_infinity
    (P : RealProjectiveOnePoint) (hP : P ≠ realProjectiveLineInfinity) :
    P = harmonicFiveAffinePoint (P.rep 0 / P.rep 1) := by
  have hrepOne : P.rep 1 ≠ 0 := by
    intro hzero
    apply hP
    calc
      P = Projectivization.mk ℝ P.rep P.rep_nonzero :=
        (Projectivization.mk_rep P).symm
      _ = realProjectiveLineInfinity := by
        unfold realProjectiveLineInfinity
        apply (realProjective_mk_eq_mk_iff_bracket_eq_zero
          P.rep_nonzero realProjectiveLineInfinityVector_ne_zero).mpr
        simp [realProjectiveBracket, realProjectiveLineInfinityVector,
          hzero]
  let t := P.rep 0 / P.rep 1
  have hraw : Projectivization.mk ℝ P.rep P.rep_nonzero =
      harmonicFiveAffinePoint t := by
    unfold harmonicFiveAffinePoint
    apply (realProjective_mk_eq_mk_iff_bracket_eq_zero
      P.rep_nonzero (harmonicFiveAffineVector_ne_zero _)).mpr
    simp only [realProjectiveBracket, harmonicFiveAffineVector,
      Matrix.cons_val_zero, Matrix.cons_val_one]
    dsimp [t]
    field_simp [hrepOne]
    norm_num
  calc
    P = Projectivization.mk ℝ P.rep P.rep_nonzero :=
      (Projectivization.mk_rep P).symm
    _ = harmonicFiveAffinePoint t := hraw

private theorem isRealProjectiveHarmonicFour_four_points_pairings
    {A B C D : RealProjectiveOnePoint}
    (hAB : A ≠ B) (hAC : A ≠ C) (hAD : A ≠ D)
    (hBC : B ≠ C) (hBD : B ≠ D) (hCD : C ≠ D)
    (h : IsRealProjectiveHarmonicFour (realProjectiveFourSet A B C D)) :
    RealProjectiveHarmonic A B C D ∨
      RealProjectiveHarmonic A C B D ∨
      RealProjectiveHarmonic A D B C := by
  classical
  rcases h with ⟨_, P, Q, R, S, hset, hdistinct, hharmonic⟩
  have hP : P = A ∨ P = B ∨ P = C ∨ P = D := by
    have : P ∈ realProjectiveFourSet A B C D := by
      rw [← hset]
      simp
    simpa only [realProjectiveFourSet, Finset.mem_insert,
      Finset.mem_singleton] using this
  have hQ : Q = A ∨ Q = B ∨ Q = C ∨ Q = D := by
    have : Q ∈ realProjectiveFourSet A B C D := by
      rw [← hset]
      simp
    simpa only [realProjectiveFourSet, Finset.mem_insert,
      Finset.mem_singleton] using this
  have hR : R = A ∨ R = B ∨ R = C ∨ R = D := by
    have : R ∈ realProjectiveFourSet A B C D := by
      rw [← hset]
      simp
    simpa only [realProjectiveFourSet, Finset.mem_insert,
      Finset.mem_singleton] using this
  have hS : S = A ∨ S = B ∨ S = C ∨ S = D := by
    have : S ∈ realProjectiveFourSet A B C D := by
      rw [← hset]
      simp
    simpa only [realProjectiveFourSet, Finset.mem_insert,
      Finset.mem_singleton] using this
  rcases hP with rfl | rfl | rfl | rfl <;>
    rcases hQ with rfl | rfl | rfl | rfl <;>
    rcases hR with rfl | rfl | rfl | rfl <;>
    rcases hS with rfl | rfl | rfl | rfl <;>
    simp_all only [RealProjectiveFourDistinct, ne_eq, not_false_eq_true,
      not_true_eq_false, false_and, and_false, true_and]
  all_goals
    aesop (add safe forward [realProjectiveHarmonic_swap_left,
      realProjectiveHarmonic_swap_right,
      realProjectiveHarmonic_swap_pairs])

private theorem harmonicFive_standard_value
    (t : ℝ)
    (h : IsRealProjectiveHarmonicFour
      (realProjectiveFourSet realProjectiveLineZero
        realProjectiveLineInfinity realProjectiveLineOne
        (harmonicFiveAffinePoint t))) :
    t = -1 ∨ 2 * t = 1 ∨ t = 2 := by
  classical
  have hcard := h.1
  have hzeroInfinity := realProjectiveLineZero_ne_infinity
  have hzeroOne := realProjectiveLineZero_ne_one
  have hinfinityOne := realProjectiveLineInfinity_ne_one
  have hzeroT : realProjectiveLineZero ≠ harmonicFiveAffinePoint t := by
    intro heq
    rw [← heq] at hcard
    exact realProjectiveThreeSet_card_ne_four _ _ _
      (by simpa [realProjectiveFourSet] using hcard)
  have hinfinityT :
      realProjectiveLineInfinity ≠ harmonicFiveAffinePoint t := by
    intro heq
    rw [← heq] at hcard
    exact realProjectiveThreeSet_card_ne_four _ _ _
      (by simpa [realProjectiveFourSet] using hcard)
  have honeT : realProjectiveLineOne ≠ harmonicFiveAffinePoint t := by
    intro heq
    rw [← heq] at hcard
    exact realProjectiveThreeSet_card_ne_four _ _ _
      (by simpa [realProjectiveFourSet] using hcard)
  have hpairs := isRealProjectiveHarmonicFour_four_points_pairings
    hzeroInfinity hzeroOne hzeroT hinfinityOne hinfinityT honeT h
  rcases hpairs with hp | hp | hp
  · left
    change RealProjectiveHarmonic
      (Projectivization.mk ℝ realProjectiveLineZeroVector
        realProjectiveLineZeroVector_ne_zero)
      (Projectivization.mk ℝ realProjectiveLineInfinityVector
        realProjectiveLineInfinityVector_ne_zero)
      (Projectivization.mk ℝ realProjectiveLineOneVector
        realProjectiveLineOneVector_ne_zero)
      (Projectivization.mk ℝ (harmonicFiveAffineVector t)
        (harmonicFiveAffineVector_ne_zero t)) at hp
    have heq := (realProjectiveHarmonic_mk_iff
      realProjectiveLineZeroVector_ne_zero
      realProjectiveLineInfinityVector_ne_zero
      realProjectiveLineOneVector_ne_zero
      (harmonicFiveAffineVector_ne_zero t)).mp hp
    norm_num [realProjectiveBracket, realProjectiveLineZeroVector,
      realProjectiveLineInfinityVector, realProjectiveLineOneVector,
      harmonicFiveAffineVector] at heq
    linarith
  · right; left
    change RealProjectiveHarmonic
      (Projectivization.mk ℝ realProjectiveLineZeroVector
        realProjectiveLineZeroVector_ne_zero)
      (Projectivization.mk ℝ realProjectiveLineOneVector
        realProjectiveLineOneVector_ne_zero)
      (Projectivization.mk ℝ realProjectiveLineInfinityVector
        realProjectiveLineInfinityVector_ne_zero)
      (Projectivization.mk ℝ (harmonicFiveAffineVector t)
        (harmonicFiveAffineVector_ne_zero t)) at hp
    have heq := (realProjectiveHarmonic_mk_iff
      realProjectiveLineZeroVector_ne_zero
      realProjectiveLineOneVector_ne_zero
      realProjectiveLineInfinityVector_ne_zero
      (harmonicFiveAffineVector_ne_zero t)).mp hp
    norm_num [realProjectiveBracket, realProjectiveLineZeroVector,
      realProjectiveLineInfinityVector, realProjectiveLineOneVector,
      harmonicFiveAffineVector] at heq
    linarith
  · right; right
    change RealProjectiveHarmonic
      (Projectivization.mk ℝ realProjectiveLineZeroVector
        realProjectiveLineZeroVector_ne_zero)
      (Projectivization.mk ℝ (harmonicFiveAffineVector t)
        (harmonicFiveAffineVector_ne_zero t))
      (Projectivization.mk ℝ realProjectiveLineInfinityVector
        realProjectiveLineInfinityVector_ne_zero)
      (Projectivization.mk ℝ realProjectiveLineOneVector
        realProjectiveLineOneVector_ne_zero) at hp
    have heq := (realProjectiveHarmonic_mk_iff
      realProjectiveLineZeroVector_ne_zero
      (harmonicFiveAffineVector_ne_zero t)
      realProjectiveLineInfinityVector_ne_zero
      realProjectiveLineOneVector_ne_zero).mp hp
    norm_num [realProjectiveBracket, realProjectiveLineZeroVector,
      realProjectiveLineInfinityVector, realProjectiveLineOneVector,
      harmonicFiveAffineVector] at heq
    linarith

private theorem harmonicFive_standard_pair
    (s t : ℝ)
    (h : IsRealProjectiveHarmonicFour
      (realProjectiveFourSet realProjectiveLineZero
        realProjectiveLineInfinity (harmonicFiveAffinePoint s)
        (harmonicFiveAffinePoint t))) :
    s + t = 0 ∨ s = 2 * t ∨ t = 2 * s := by
  classical
  have hcard := h.1
  have hzeroInfinity := realProjectiveLineZero_ne_infinity
  have hzeroS : realProjectiveLineZero ≠ harmonicFiveAffinePoint s := by
    intro heq
    rw [← heq] at hcard
    exact realProjectiveThreeSet_card_ne_four _ _ _
      (by simpa [realProjectiveFourSet] using hcard)
  have hzeroT : realProjectiveLineZero ≠ harmonicFiveAffinePoint t := by
    intro heq
    rw [← heq] at hcard
    exact realProjectiveThreeSet_card_ne_four _ _ _
      (by simpa [realProjectiveFourSet] using hcard)
  have hinfinityS :
      realProjectiveLineInfinity ≠ harmonicFiveAffinePoint s := by
    intro heq
    rw [← heq] at hcard
    exact realProjectiveThreeSet_card_ne_four _ _ _
      (by simpa [realProjectiveFourSet] using hcard)
  have hinfinityT :
      realProjectiveLineInfinity ≠ harmonicFiveAffinePoint t := by
    intro heq
    rw [← heq] at hcard
    exact realProjectiveThreeSet_card_ne_four _ _ _
      (by simpa [realProjectiveFourSet] using hcard)
  have hst : harmonicFiveAffinePoint s ≠ harmonicFiveAffinePoint t := by
    intro heq
    rw [heq] at hcard
    exact realProjectiveThreeSet_card_ne_four _ _ _
      (by simpa [realProjectiveFourSet] using hcard)
  have hpairs := isRealProjectiveHarmonicFour_four_points_pairings
    hzeroInfinity hzeroS hzeroT hinfinityS hinfinityT hst h
  rcases hpairs with hp | hp | hp
  · left
    change RealProjectiveHarmonic
      (Projectivization.mk ℝ realProjectiveLineZeroVector
        realProjectiveLineZeroVector_ne_zero)
      (Projectivization.mk ℝ realProjectiveLineInfinityVector
        realProjectiveLineInfinityVector_ne_zero)
      (Projectivization.mk ℝ (harmonicFiveAffineVector s)
        (harmonicFiveAffineVector_ne_zero s))
      (Projectivization.mk ℝ (harmonicFiveAffineVector t)
        (harmonicFiveAffineVector_ne_zero t)) at hp
    have heq := (realProjectiveHarmonic_mk_iff
      realProjectiveLineZeroVector_ne_zero
      realProjectiveLineInfinityVector_ne_zero
      (harmonicFiveAffineVector_ne_zero s)
      (harmonicFiveAffineVector_ne_zero t)).mp hp
    norm_num [realProjectiveBracket, realProjectiveLineZeroVector,
      realProjectiveLineInfinityVector, harmonicFiveAffineVector] at heq
    linarith
  · right; left
    change RealProjectiveHarmonic
      (Projectivization.mk ℝ realProjectiveLineZeroVector
        realProjectiveLineZeroVector_ne_zero)
      (Projectivization.mk ℝ (harmonicFiveAffineVector s)
        (harmonicFiveAffineVector_ne_zero s))
      (Projectivization.mk ℝ realProjectiveLineInfinityVector
        realProjectiveLineInfinityVector_ne_zero)
      (Projectivization.mk ℝ (harmonicFiveAffineVector t)
        (harmonicFiveAffineVector_ne_zero t)) at hp
    have heq := (realProjectiveHarmonic_mk_iff
      realProjectiveLineZeroVector_ne_zero
      (harmonicFiveAffineVector_ne_zero s)
      realProjectiveLineInfinityVector_ne_zero
      (harmonicFiveAffineVector_ne_zero t)).mp hp
    norm_num [realProjectiveBracket, realProjectiveLineZeroVector,
      realProjectiveLineInfinityVector, harmonicFiveAffineVector] at heq
    linarith
  · right; right
    change RealProjectiveHarmonic
      (Projectivization.mk ℝ realProjectiveLineZeroVector
        realProjectiveLineZeroVector_ne_zero)
      (Projectivization.mk ℝ (harmonicFiveAffineVector t)
        (harmonicFiveAffineVector_ne_zero t))
      (Projectivization.mk ℝ realProjectiveLineInfinityVector
        realProjectiveLineInfinityVector_ne_zero)
      (Projectivization.mk ℝ (harmonicFiveAffineVector s)
        (harmonicFiveAffineVector_ne_zero s)) at hp
    have heq := (realProjectiveHarmonic_mk_iff
      realProjectiveLineZeroVector_ne_zero
      (harmonicFiveAffineVector_ne_zero t)
      realProjectiveLineInfinityVector_ne_zero
      (harmonicFiveAffineVector_ne_zero s)).mp hp
    norm_num [realProjectiveBracket, realProjectiveLineZeroVector,
      realProjectiveLineInfinityVector, harmonicFiveAffineVector] at heq
    linarith

private theorem harmonicFive_values_pair_impossible
    {s t : ℝ}
    (hs : s = -1 ∨ 2 * s = 1 ∨ s = 2)
    (ht : t = -1 ∨ 2 * t = 1 ∨ t = 2)
    (hpair : s + t = 0 ∨ s = 2 * t ∨ t = 2 * s) : False := by
  rcases hs with hs | hs | hs <;>
    rcases ht with ht | ht | ht <;>
    rcases hpair with hpair | hpair | hpair <;> linarith

/-! ## Transport of an order-free harmonic four-set -/

private theorem isRealProjectiveHarmonicFour_image_gl
    [DecidableEq RealProjectiveOnePoint]
    (g : GL (Fin 2) ℝ) (T : Finset RealProjectiveOnePoint)
    (h : IsRealProjectiveHarmonicFour T) :
    IsRealProjectiveHarmonicFour (T.image fun P => g • P) := by
  classical
  rcases h with ⟨hcard, P, Q, R, S, hset, hdistinct, hharmonic⟩
  have hinjective : Function.Injective (fun X : RealProjectiveOnePoint => g • X) := by
    intro X Y hXY
    have hback := congrArg (fun Z : RealProjectiveOnePoint => g⁻¹ • Z) hXY
    simpa [smul_smul] using hback
  refine ⟨?_, g • P, g • Q, g • R, g • S, ?_, ?_,
    realProjectiveHarmonic_gl_smul g hharmonic⟩
  · rw [Finset.card_image_of_injective _ hinjective, hcard]
  · rw [← hset]
    ext Z
    simp
  · rcases hdistinct with ⟨hPQ, hPR, hPS, hQR, hQS, hRS⟩
    exact ⟨fun h => hPQ (hinjective h), fun h => hPR (hinjective h),
      fun h => hPS (hinjective h), fun h => hQR (hinjective h),
      fun h => hQS (hinjective h), fun h => hRS (hinjective h)⟩

/-! ## The five-point cap -/

/-- Points whose deletion leaves an order-free harmonic four-set. -/
noncomputable def realProjectiveHarmonicComplementPoints
    (P : Finset RealProjectiveOnePoint) : Finset RealProjectiveOnePoint := by
  classical
  exact P.filter fun p => IsRealProjectiveHarmonicFour (P.erase p)

/-- Among five distinct real projective points, at most two deletions leave
a harmonic four-set. -/
theorem realProjectiveHarmonicComplementPoints_card_le_two
    (P : Finset RealProjectiveOnePoint) (hPcard : P.card = 5) :
    (realProjectiveHarmonicComplementPoints P).card ≤ 2 := by
  classical
  by_contra hnot
  have hthree : 2 < (realProjectiveHarmonicComplementPoints P).card := by
    omega
  obtain ⟨a, b, c, ha, hb, hc, hab, hac, hbc⟩ :=
    Finset.two_lt_card_iff.mp hthree
  have ha' := ha
  have hb' := hb
  have hc' := hc
  simp only [realProjectiveHarmonicComplementPoints,
    Finset.mem_filter] at ha' hb' hc'
  have haP : a ∈ P := ha'.1
  have hbP : b ∈ P := hb'.1
  have hcP : c ∈ P := hc'.1
  have haH : IsRealProjectiveHarmonicFour (P.erase a) := ha'.2
  have hbH : IsRealProjectiveHarmonicFour (P.erase b) := hb'.2
  have hcH : IsRealProjectiveHarmonicFour (P.erase c) := hc'.2
  let A : Finset RealProjectiveOnePoint := {a, b, c}
  have hAcard : A.card = 3 := by
    simpa [A] using (Finset.card_triple_eq_three_iff.mpr ⟨hab, hac, hbc⟩)
  have hAsub : A ⊆ P := by
    intro x hx
    simp only [A, Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl
    · exact haP
    · exact hbP
    · exact hcP
  let R := P \ A
  have hRcard : R.card = 2 := by
    change (P \ A).card = 2
    rw [Finset.card_sdiff_of_subset hAsub, hPcard, hAcard]
  obtain ⟨x, y, hxy, hR⟩ := Finset.card_eq_two.mp hRcard
  have hxR : x ∈ R := by rw [hR]; simp
  have hyR : y ∈ R := by rw [hR]; simp
  have hxa : x ≠ a := by
    intro h
    subst h
    exact (Finset.mem_sdiff.mp hxR).2 (by simp [A])
  have hxb : x ≠ b := by
    intro h
    subst h
    exact (Finset.mem_sdiff.mp hxR).2 (by simp [A])
  have hxc : x ≠ c := by
    intro h
    subst h
    exact (Finset.mem_sdiff.mp hxR).2 (by simp [A])
  have hya : y ≠ a := by
    intro h
    subst h
    exact (Finset.mem_sdiff.mp hyR).2 (by simp [A])
  have hyb : y ≠ b := by
    intro h
    subst h
    exact (Finset.mem_sdiff.mp hyR).2 (by simp [A])
  have hyc : y ≠ c := by
    intro h
    subst h
    exact (Finset.mem_sdiff.mp hyR).2 (by simp [A])
  have hP : P = {a, b, c, x, y} := by
    calc
      P = A ∪ (P \ A) := (Finset.union_sdiff_of_subset hAsub).symm
      _ = A ∪ R := by rfl
      _ = {a, b, c, x, y} := by
        rw [hR]
        ext z
        simp [A, or_left_comm]
  have haErase : P.erase a = realProjectiveFourSet b c x y := by
    rw [hP]
    simp [realProjectiveFourSet, hab, hac, hxa.symm, hya.symm]
  have hbErase : P.erase b = realProjectiveFourSet a c x y := by
    rw [hP]
    unfold realProjectiveFourSet
    ext z
    simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
    aesop
  have hcErase : P.erase c = realProjectiveFourSet a b x y := by
    rw [hP]
    unfold realProjectiveFourSet
    ext z
    simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
    aesop
  rw [haErase] at haH
  rw [hbErase] at hbH
  rw [hcErase] at hcH
  let g : GL (Fin 2) ℝ :=
    realProjectiveTripleFrame x y a hxy hxa hya.symm
  have hgx : g • x = realProjectiveLineZero := by
    simpa [g] using realProjectiveTripleFrame_smul_left
      x y a hxy hxa hya.symm
  have hgy : g • y = realProjectiveLineInfinity := by
    simpa [g] using realProjectiveTripleFrame_smul_right
      x y a hxy hxa hya.symm
  have hga : g • a = realProjectiveLineOne := by
    simpa [g] using realProjectiveTripleFrame_smul_one
      x y a hxy hxa hya.symm
  let B := g • b
  let C := g • c
  have hBinfinity : B ≠ realProjectiveLineInfinity := by
    intro h
    apply hyb
    have h' : g • b = g • y := by simpa [B, hgy] using h
    have hback := congrArg (fun Z : RealProjectiveOnePoint => g⁻¹ • Z) h'
    have hby : b = y := by simpa [smul_smul] using hback
    exact hby.symm
  have hCinfinity : C ≠ realProjectiveLineInfinity := by
    intro h
    apply hyc
    have h' : g • c = g • y := by simpa [C, hgy] using h
    have hback := congrArg (fun Z : RealProjectiveOnePoint => g⁻¹ • Z) h'
    have hcy : c = y := by simpa [smul_smul] using hback
    exact hcy.symm
  let s : ℝ := B.rep 0 / B.rep 1
  let t : ℝ := C.rep 0 / C.rep 1
  have hB : B = harmonicFiveAffinePoint s := by
    simpa [s] using
      realProjective_eq_harmonicFiveAffinePoint_of_ne_infinity B hBinfinity
  have hC : C = harmonicFiveAffinePoint t := by
    simpa [t] using
      realProjective_eq_harmonicFiveAffinePoint_of_ne_infinity C hCinfinity
  have hgb : g • b = harmonicFiveAffinePoint s := by
    simpa only [B] using hB
  have hgc : g • c = harmonicFiveAffinePoint t := by
    simpa only [C] using hC
  have haImage := isRealProjectiveHarmonicFour_image_gl g _ haH
  have hbImage := isRealProjectiveHarmonicFour_image_gl g _ hbH
  have hcImage := isRealProjectiveHarmonicFour_image_gl g _ hcH
  have haStandard : IsRealProjectiveHarmonicFour
      (realProjectiveFourSet realProjectiveLineZero
        realProjectiveLineInfinity (harmonicFiveAffinePoint s)
        (harmonicFiveAffinePoint t)) := by
    have hset :
        (realProjectiveFourSet b c x y).image (fun Z => g • Z) =
          realProjectiveFourSet realProjectiveLineZero
            realProjectiveLineInfinity (harmonicFiveAffinePoint s)
            (harmonicFiveAffinePoint t) := by
      rw [image_realProjectiveFourSet, hgb, hgc, hgx, hgy]
      exact realProjectiveFourSet_rotate _ _ _ _
    rw [hset] at haImage
    exact haImage
  have hbStandard : IsRealProjectiveHarmonicFour
      (realProjectiveFourSet realProjectiveLineZero
        realProjectiveLineInfinity realProjectiveLineOne
        (harmonicFiveAffinePoint t)) := by
    have hset :
        (realProjectiveFourSet a c x y).image (fun Z => g • Z) =
          realProjectiveFourSet realProjectiveLineZero
            realProjectiveLineInfinity realProjectiveLineOne
            (harmonicFiveAffinePoint t) := by
      rw [image_realProjectiveFourSet, hga, hgc, hgx, hgy]
      exact realProjectiveFourSet_rotate _ _ _ _
    rw [hset] at hbImage
    exact hbImage
  have hcStandard : IsRealProjectiveHarmonicFour
      (realProjectiveFourSet realProjectiveLineZero
        realProjectiveLineInfinity realProjectiveLineOne
        (harmonicFiveAffinePoint s)) := by
    have hset :
        (realProjectiveFourSet a b x y).image (fun Z => g • Z) =
          realProjectiveFourSet realProjectiveLineZero
            realProjectiveLineInfinity realProjectiveLineOne
            (harmonicFiveAffinePoint s) := by
      rw [image_realProjectiveFourSet, hga, hgb, hgx, hgy]
      exact realProjectiveFourSet_rotate _ _ _ _
    rw [hset] at hcImage
    exact hcImage
  exact harmonicFive_values_pair_impossible
    (harmonicFive_standard_value s hcStandard)
    (harmonicFive_standard_value t hbStandard)
    (harmonicFive_standard_pair s t haStandard)

end Erdos506.Incidence
