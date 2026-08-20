import Erdos506.Incidence.RealProjectiveLineCellulation
import Erdos506.Incidence.RealProjectiveLineCyclicOrder
import Mathlib.Data.Finset.Sort
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.Logic.Equiv.Fin.Rotate
import Mathlib.Order.Circular.ZMod
import Mathlib.Tactic

/-!
# Geometric successors on finite subsets of a real projective line

The marked points on an indexed projective line of an arrangement form a
finite subset of a copy of `RP¹`.  This file makes that copy explicit and
then constructs its successor from the intrinsic cyclic orientation, rather
than from an arbitrary permutation of the finite set.

There are two separate ingredients.

* The kernel of the homogeneous covector of a projective line has dimension
  two.  A linear equivalence from `Fin 2 → ℝ` therefore parametrizes its
  projectivization.
* For a finite family of distinct `RP¹` points, an affine chart is cut away
  from all marked points, the resulting real coordinates are sorted, and the
  standard finite rotation is transported back.  The accompanying theorem
  identifies the sorted labels with the intrinsic ternary cyclic relation.

Thus the resulting operation is a genuine circular successor.  It introduces
no face, Euler, or complement-topology assertion.
-/

namespace Erdos506.Incidence

open Matrix
open scoped BigOperators LinearAlgebra.Projectivization

/-! ## A finite cyclic enumeration of marked `RP¹` points -/

/-- A chart coordinate on `RP¹`; its pole is the point represented by
`(1, t)`. -/
noncomputable def arrangementProjectiveChartCoordinate
    (t : ℝ) (P : RealProjectiveOnePoint) : ℝ :=
  P.rep 0 / (P.rep 1 - t * P.rep 0)

private theorem arrangementProjective_eq_of_chartCoordinate_eq
    (t : ℝ) {P Q : RealProjectiveOnePoint}
    (hP : P.rep 1 - t * P.rep 0 ≠ 0)
    (hQ : Q.rep 1 - t * Q.rep 0 ≠ 0)
    (hcoord : arrangementProjectiveChartCoordinate t P =
      arrangementProjectiveChartCoordinate t Q) :
    P = Q := by
  have hbracket : realProjectiveBracket P.rep Q.rep = 0 := by
    unfold arrangementProjectiveChartCoordinate at hcoord
    have hmul := (div_eq_div_iff hP hQ).mp hcoord
    unfold realProjectiveBracket
    linear_combination hmul
  calc
    P = Projectivization.mk ℝ P.rep P.rep_nonzero :=
      (Projectivization.mk_rep P).symm
    _ = Projectivization.mk ℝ Q.rep Q.rep_nonzero :=
      (realProjective_mk_eq_mk_iff_bracket_eq_zero
        P.rep_nonzero Q.rep_nonzero).2 hbracket
    _ = Q := Projectivization.mk_rep Q

/-- The representative form of the intrinsic cyclic relation. -/
private theorem arrangementProjectiveCyclic_iff_rep
    (P Q R : RealProjectiveOnePoint) :
    RealProjectiveCyclic P Q R ↔
      0 < realProjectiveTripleBracket P.rep Q.rep R.rep := by
  constructor
  · rintro ⟨p, q, r, hp, hq, hr, hP, hQ, hR, hpositive⟩
    have hpScale : ∃ a : ℝ, a • p = P.rep := by
      apply (Projectivization.mk_eq_mk_iff' ℝ P.rep p
        P.rep_nonzero hp).1
      rw [Projectivization.mk_rep]
      exact hP
    have hqScale : ∃ b : ℝ, b • q = Q.rep := by
      apply (Projectivization.mk_eq_mk_iff' ℝ Q.rep q
        Q.rep_nonzero hq).1
      rw [Projectivization.mk_rep]
      exact hQ
    have hrScale : ∃ c : ℝ, c • r = R.rep := by
      apply (Projectivization.mk_eq_mk_iff' ℝ R.rep r
        R.rep_nonzero hr).1
      rw [Projectivization.mk_rep]
      exact hR
    obtain ⟨a, ha⟩ := hpScale
    obtain ⟨b, hb⟩ := hqScale
    obtain ⟨c, hc⟩ := hrScale
    have ha0 : a ≠ 0 := by
      intro ha0
      apply P.rep_nonzero
      rw [← ha, ha0, zero_smul]
    have hb0 : b ≠ 0 := by
      intro hb0
      apply Q.rep_nonzero
      rw [← hb, hb0, zero_smul]
    have hc0 : c ≠ 0 := by
      intro hc0
      apply R.rep_nonzero
      rw [← hc, hc0, zero_smul]
    rw [← ha, ← hb, ← hc, realProjectiveTripleBracket_smul]
    exact mul_pos (sq_pos_of_ne_zero (mul_ne_zero (mul_ne_zero ha0 hb0) hc0))
      hpositive
  · intro hpositive
    exact ⟨P.rep, Q.rep, R.rep, P.rep_nonzero, Q.rep_nonzero,
      R.rep_nonzero, (Projectivization.mk_rep P).symm,
      (Projectivization.mk_rep Q).symm,
      (Projectivization.mk_rep R).symm, hpositive⟩

/-- The intrinsic cyclic order of three projective-line points can be read
directly on Mathlib's fixed nonzero representatives.  This public form is
used by the ambient-projective topology layer to parametrize a genuine open
cyclic arc by a convex real interval. -/
theorem realProjectiveCyclic_iff_rep_tripleBracket
    (P Q R : RealProjectiveOnePoint) :
    RealProjectiveCyclic P Q R ↔
      0 < realProjectiveTripleBracket P.rep Q.rep R.rep :=
  arrangementProjectiveCyclic_iff_rep P Q R

private theorem arrangementDiv_mul_pair_cancel_left
    (x a b : ℝ) (ha : a ≠ 0) : x / a * (a * b) = x * b := by
  calc
    x / a * (a * b) = (x / a * a) * b := by ring
    _ = x * b := by rw [div_mul_cancel₀ x ha]

private theorem arrangementDiv_mul_pair_cancel_right
    (x a b : ℝ) (hb : b ≠ 0) : x / b * (a * b) = a * x := by
  calc
    x / b * (a * b) = a * (x / b * b) := by ring
    _ = a * x := by rw [div_mul_cancel₀ x hb]

private theorem arrangementProjectiveChartCoordinate_sub_eq
    (t : ℝ) (P Q : RealProjectiveOnePoint)
    (hP : P.rep 1 - t * P.rep 0 ≠ 0)
    (hQ : Q.rep 1 - t * Q.rep 0 ≠ 0) :
    arrangementProjectiveChartCoordinate t P -
        arrangementProjectiveChartCoordinate t Q =
      realProjectiveBracket P.rep Q.rep /
        ((P.rep 1 - t * P.rep 0) *
          (Q.rep 1 - t * Q.rep 0)) := by
  apply (eq_div_iff (mul_ne_zero hP hQ)).2
  unfold arrangementProjectiveChartCoordinate
  rw [sub_mul,
    arrangementDiv_mul_pair_cancel_left _ _ _ hP,
    arrangementDiv_mul_pair_cancel_right _ _ _ hQ]
  unfold realProjectiveBracket
  ring

private theorem arrangementSquare_three_mul_pairwise_div
    (a b c x y z : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) :
    (a * b * c) ^ 2 *
        ((x / (a * b)) * (y / (b * c)) * (z / (c * a))) =
      x * y * z := by
  field_simp [ha, hb, hc]

private theorem arrangementProjectiveTripleBracket_chart
    (t : ℝ) (P Q R : RealProjectiveOnePoint)
    (hP : P.rep 1 - t * P.rep 0 ≠ 0)
    (hQ : Q.rep 1 - t * Q.rep 0 ≠ 0)
    (hR : R.rep 1 - t * R.rep 0 ≠ 0) :
    realProjectiveTripleBracket P.rep Q.rep R.rep =
      ((P.rep 1 - t * P.rep 0) *
        (Q.rep 1 - t * Q.rep 0) *
        (R.rep 1 - t * R.rep 0)) ^ 2 *
      ((arrangementProjectiveChartCoordinate t P -
          arrangementProjectiveChartCoordinate t Q) *
        (arrangementProjectiveChartCoordinate t Q -
          arrangementProjectiveChartCoordinate t R) *
        (arrangementProjectiveChartCoordinate t R -
          arrangementProjectiveChartCoordinate t P)) := by
  unfold realProjectiveTripleBracket
  rw [arrangementProjectiveChartCoordinate_sub_eq t P Q hP hQ,
    arrangementProjectiveChartCoordinate_sub_eq t Q R hQ hR,
    arrangementProjectiveChartCoordinate_sub_eq t R P hR hP]
  symm
  exact arrangementSquare_three_mul_pairwise_div
    (P.rep 1 - t * P.rep 0)
    (Q.rep 1 - t * Q.rep 0)
    (R.rep 1 - t * R.rep 0)
    (realProjectiveBracket P.rep Q.rep)
    (realProjectiveBracket Q.rep R.rep)
    (realProjectiveBracket R.rep P.rep) hP hQ hR

private theorem arrangementSub_mul_sub_mul_sub_pos_iff_cyclic
    (a b c : ℝ) :
    0 < (a - b) * (b - c) * (c - a) ↔
      (a < b ∧ b < c) ∨ (b < c ∧ c < a) ∨ (c < a ∧ a < b) := by
  constructor
  · intro hprod
    rcases (mul_pos_iff.mp hprod) with ⟨habc, hca⟩ | ⟨habc, hca⟩
    · rcases (mul_pos_iff.mp habc) with ⟨hab, hbc⟩ | ⟨hab, hbc⟩
      · have hba : b < a := sub_pos.mp hab
        have hcb : c < b := sub_pos.mp hbc
        have hac : a < c := sub_pos.mp hca
        exact (lt_irrefl a (lt_trans hac (lt_trans hcb hba))).elim
      · exact Or.inl ⟨sub_neg.mp hab, sub_neg.mp hbc⟩
    · have hca' : c < a := sub_neg.mp hca
      rcases (mul_neg_iff.mp habc) with ⟨hab, hbc⟩ | ⟨hab, hbc⟩
      · exact Or.inr (Or.inl ⟨sub_neg.mp hbc, hca'⟩)
      · exact Or.inr (Or.inr ⟨hca', sub_neg.mp hab⟩)
  · rintro (h | h | h)
    · exact mul_pos
        (mul_pos_of_neg_of_neg (sub_neg.mpr h.1) (sub_neg.mpr h.2))
        (sub_pos.mpr (lt_trans h.1 h.2))
    · exact mul_pos_of_neg_of_neg
        (mul_neg_of_pos_of_neg
          (sub_pos.mpr (lt_trans h.1 h.2)) (sub_neg.mpr h.1))
        (sub_neg.mpr h.2)
    · exact mul_pos_of_neg_of_neg
        (mul_neg_of_neg_of_pos
          (sub_neg.mpr h.2) (sub_pos.mpr (lt_trans h.1 h.2)))
        (sub_neg.mpr h.1)

private theorem arrangementProjectiveCyclic_iff_chart
    (t : ℝ) (P Q R : RealProjectiveOnePoint)
    (hP : P.rep 1 - t * P.rep 0 ≠ 0)
    (hQ : Q.rep 1 - t * Q.rep 0 ≠ 0)
    (hR : R.rep 1 - t * R.rep 0 ≠ 0) :
    RealProjectiveCyclic P Q R ↔
      (arrangementProjectiveChartCoordinate t P <
          arrangementProjectiveChartCoordinate t Q ∧
        arrangementProjectiveChartCoordinate t Q <
          arrangementProjectiveChartCoordinate t R) ∨
      (arrangementProjectiveChartCoordinate t Q <
          arrangementProjectiveChartCoordinate t R ∧
        arrangementProjectiveChartCoordinate t R <
          arrangementProjectiveChartCoordinate t P) ∨
      (arrangementProjectiveChartCoordinate t R <
          arrangementProjectiveChartCoordinate t P ∧
        arrangementProjectiveChartCoordinate t P <
          arrangementProjectiveChartCoordinate t Q) := by
  rw [arrangementProjectiveCyclic_iff_rep,
    arrangementProjectiveTripleBracket_chart t P Q R hP hQ hR]
  have hfactor : 0 < ((P.rep 1 - t * P.rep 0) *
      (Q.rep 1 - t * Q.rep 0) *
      (R.rep 1 - t * R.rep 0)) ^ 2 :=
    sq_pos_of_ne_zero (mul_ne_zero (mul_ne_zero hP hQ) hR)
  rw [mul_pos_iff_of_pos_left hfactor]
  exact arrangementSub_mul_sub_mul_sub_pos_iff_cyclic _ _ _

variable {X : Type*} [Fintype X]

/-- The finite set of forbidden chart poles for a finite family of projective
parameters. -/
noncomputable def projectiveChartForbidden
    (f : X → RealProjectiveOnePoint) : Finset ℝ := by
  classical
  exact (Finset.univ : Finset X).image fun x =>
    let P := f x
    if P.rep 0 = 0 then 0 else P.rep 1 / P.rep 0

/-- A concrete affine chart cut away from all points of the finite family. -/
noncomputable def projectiveChartCut
    (f : X → RealProjectiveOnePoint) : ℝ := by
  classical
  exact if hS : (projectiveChartForbidden f).Nonempty then
    (projectiveChartForbidden f).max' hS + 1 else 0

theorem projectiveChartCut_not_mem
    (f : X → RealProjectiveOnePoint) :
    projectiveChartCut f ∉ projectiveChartForbidden f := by
  classical
  unfold projectiveChartCut
  split_ifs with hS
  · intro hmem
    have hle := Finset.le_max' _ _ hmem
    linarith
  · intro hmem
    exact hS ⟨_, hmem⟩

/-- The chosen chart is finite at every member of the parameter family. -/
theorem projectiveChartDenominator_ne_zero
    (f : X → RealProjectiveOnePoint) (x : X) :
    let P := f x
    P.rep 1 - projectiveChartCut f * P.rep 0 ≠ 0 := by
  classical
  dsimp only
  let P := f x
  by_cases hP0 : P.rep 0 = 0
  · intro hden
    have hP1 : P.rep 1 = 0 := by
      calc
        P.rep 1 = P.rep 1 - projectiveChartCut f * P.rep 0 := by
          rw [hP0, mul_zero, sub_zero]
        _ = 0 := hden
    apply P.rep_nonzero
    funext i
    fin_cases i
    · exact hP0
    · exact hP1
  · intro hden
    have hcut : projectiveChartCut f = P.rep 1 / P.rep 0 := by
      field_simp [hP0]
      linarith
    apply projectiveChartCut_not_mem f
    apply Finset.mem_image.mpr
    refine ⟨x, Finset.mem_univ x, ?_⟩
    change (if P.rep 0 = 0 then 0 else P.rep 1 / P.rep 0) =
      projectiveChartCut f
    rw [if_neg hP0, ← hcut]

/-- The real coordinate of a marked `RP¹` point in the chosen pole-free
chart. -/
noncomputable def projectiveChartCoordinate
    (f : X → RealProjectiveOnePoint) (x : X) : ℝ :=
  arrangementProjectiveChartCoordinate (projectiveChartCut f) (f x)

theorem projectiveChartCoordinate_injective
    (f : X → RealProjectiveOnePoint) (hf : Function.Injective f) :
    Function.Injective (projectiveChartCoordinate f) := by
  intro x y hxy
  apply hf
  apply arrangementProjective_eq_of_chartCoordinate_eq
    (projectiveChartCut f)
    (projectiveChartDenominator_ne_zero f x)
    (projectiveChartDenominator_ne_zero f y)
  exact hxy

/-- The increasing enumeration of a finite family in a chart disjoint from
the family.  The cyclic-order theorem below shows that this is a circular,
rather than arbitrary, enumeration. -/
noncomputable def projectiveCyclicLabel
    (f : X → RealProjectiveOnePoint) (hf : Function.Injective f) :
    Fin (Fintype.card X) ≃ X := by
  classical
  letI : LinearOrder X := LinearOrder.lift'
    (projectiveChartCoordinate f)
    (projectiveChartCoordinate_injective f hf)
  exact (Fintype.orderIsoFinOfCardEq X rfl).toEquiv

theorem projectiveCyclicLabel_coordinate_lt_iff
    (f : X → RealProjectiveOnePoint) (hf : Function.Injective f)
    (i j : Fin (Fintype.card X)) :
    projectiveChartCoordinate f (projectiveCyclicLabel f hf i) <
      projectiveChartCoordinate f (projectiveCyclicLabel f hf j) ↔ i < j := by
  classical
  letI : LinearOrder X := LinearOrder.lift'
    (projectiveChartCoordinate f)
    (projectiveChartCoordinate_injective f hf)
  change ((Fintype.orderIsoFinOfCardEq X rfl i : X) <
      (Fintype.orderIsoFinOfCardEq X rfl j : X)) ↔ i < j
  exact (Fintype.orderIsoFinOfCardEq X rfl).lt_iff_lt

/-- The sorted finite labels agree exactly with the intrinsic orientation of
`RP¹`. -/
theorem projectiveCyclicLabel_cyclic_iff_sbtw
    (f : X → RealProjectiveOnePoint) (hf : Function.Injective f)
    (i j k : Fin (Fintype.card X)) :
    RealProjectiveCyclic
      (f (projectiveCyclicLabel f hf i))
      (f (projectiveCyclicLabel f hf j))
      (f (projectiveCyclicLabel f hf k)) ↔
      sbtw i j k := by
  let t := projectiveChartCut f
  rw [arrangementProjectiveCyclic_iff_chart t]
  · change
      ((projectiveChartCoordinate f (projectiveCyclicLabel f hf i) <
          projectiveChartCoordinate f (projectiveCyclicLabel f hf j) ∧
        projectiveChartCoordinate f (projectiveCyclicLabel f hf j) <
          projectiveChartCoordinate f (projectiveCyclicLabel f hf k)) ∨
      (projectiveChartCoordinate f (projectiveCyclicLabel f hf j) <
          projectiveChartCoordinate f (projectiveCyclicLabel f hf k) ∧
        projectiveChartCoordinate f (projectiveCyclicLabel f hf k) <
          projectiveChartCoordinate f (projectiveCyclicLabel f hf i)) ∨
      (projectiveChartCoordinate f (projectiveCyclicLabel f hf k) <
          projectiveChartCoordinate f (projectiveCyclicLabel f hf i) ∧
        projectiveChartCoordinate f (projectiveCyclicLabel f hf i) <
          projectiveChartCoordinate f (projectiveCyclicLabel f hf j))) ↔
        sbtw i j k
    rw [projectiveCyclicLabel_coordinate_lt_iff f hf i j,
      projectiveCyclicLabel_coordinate_lt_iff f hf j k,
      projectiveCyclicLabel_coordinate_lt_iff f hf k i]
    exact Fin.sbtw_iff.symm
  · exact projectiveChartDenominator_ne_zero f _
  · exact projectiveChartDenominator_ne_zero f _
  · exact projectiveChartDenominator_ne_zero f _

/-- The successor permutation obtained by conjugating the standard rotation
of the cyclic labels. -/
noncomputable def projectiveCyclicSuccessorEquiv
    (f : X → RealProjectiveOnePoint) (hf : Function.Injective f) :
    Equiv.Perm X :=
  ((projectiveCyclicLabel f hf).symm.trans
      (finRotate (Fintype.card X))).trans (projectiveCyclicLabel f hf)

/-- The geometric positive successor in a finite parameter family. -/
noncomputable def projectiveCyclicSuccessor
    (f : X → RealProjectiveOnePoint) (hf : Function.Injective f) : X → X :=
  projectiveCyclicSuccessorEquiv f hf

theorem projectiveCyclicSuccessor_apply_label
    (f : X → RealProjectiveOnePoint) (hf : Function.Injective f)
    (i : Fin (Fintype.card X)) :
    projectiveCyclicSuccessor f hf (projectiveCyclicLabel f hf i) =
      projectiveCyclicLabel f hf (finRotate (Fintype.card X) i) := by
  simp [projectiveCyclicSuccessor, projectiveCyclicSuccessorEquiv]

/-- A one-step rotation of a finite cyclic order has no fixed point as soon
as the marked family has at least two points. -/
private theorem finRotate_ne_self_of_one_lt
    {n : ℕ} (hn : 1 < n) (i : Fin n) : finRotate n i ≠ i := by
  rcases Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt (zero_lt_one.trans hn)) with
    ⟨k, rfl⟩
  by_cases hlast : i = Fin.last k
  · subst i
    intro hfixed
    have hvalue := congrArg Fin.val hfixed
    rw [finRotate_last] at hvalue
    simp only [Fin.val_zero, Fin.val_last] at hvalue
    omega
  · intro hfixed
    have hvalue := congrArg Fin.val hfixed
    rw [coe_finRotate_of_ne_last hlast] at hvalue
    omega

/-- The predecessor of the zero label for the concrete finite rotation.  It
is useful when a point of `RP¹` lies at the pole of a chart, and keeps the
wrap-around case separate from the ordinary affine-order case. -/
private noncomputable def finRotatePredecessorZero (n : ℕ) [NeZero n] : Fin n :=
  (finRotate n).symm 0

private theorem finRotate_apply_predecessorZero (n : ℕ) [NeZero n] :
    finRotate n (finRotatePredecessorZero n) = 0 :=
  (finRotate n).apply_symm_apply 0

private theorem finRotatePredecessorZero_ne_zero {n : ℕ} [NeZero n]
    (hn : 1 < n) : finRotatePredecessorZero n ≠ 0 := by
  intro hzero
  have hfixed : finRotate n 0 = 0 := by
    calc
      finRotate n 0 = finRotate n (finRotatePredecessorZero n) := by rw [hzero]
      _ = 0 := finRotate_apply_predecessorZero n
  exact finRotate_ne_self_of_one_lt hn 0 hfixed

/-- Away from the wrap-around predecessor of zero, one application of the
finite rotation is strictly increasing in the standard `Fin` order. -/
private theorem lt_finRotate_of_ne_predecessorZero {n : ℕ} [NeZero n]
    (i : Fin n) (hi : i ≠ finRotatePredecessorZero n) :
    i < finRotate n i := by
  cases n with
  | zero => exact Fin.elim0 i
  | succ n =>
      by_cases hlast : i = Fin.last n
      · subst i
        exfalso
        apply hi
        dsimp [finRotatePredecessorZero]
        apply (finRotate (n + 1)).injective
        calc
          finRotate (n + 1) (Fin.last n) = 0 := finRotate_last
          _ = finRotate (n + 1) ((finRotate (n + 1)).symm 0) :=
            (finRotate (n + 1)).apply_symm_apply 0 |>.symm
      · exact (lt_finRotate_iff_ne_last i).mpr hlast

/-- A projective point different from a finite marked family and away from
the family's chosen chart pole lies in one of the genuine open cyclic gaps.
The marker on the left is selected by the maximum chart coordinate below the
point; the two wrap-around cases are handled by the actual finite rotation.
This is a coverage theorem for the *geometric* successor, not an arbitrary
finite successor. -/
theorem exists_realProjectiveCyclic_between_projectiveCyclicSuccessor_of_ne
    (f : X → RealProjectiveOnePoint) (hf : Function.Injective f)
    (hcard : 1 < Fintype.card X) (Q : RealProjectiveOnePoint)
    (hQ : ∀ x : X, Q ≠ f x)
    (hQden : Q.rep 1 - projectiveChartCut f * Q.rep 0 ≠ 0) :
    ∃ x : X, RealProjectiveCyclic (f x) Q
      (f (projectiveCyclicSuccessor f hf x)) := by
  classical
  letI : NeZero (Fintype.card X) :=
    ⟨Nat.ne_of_gt (lt_trans zero_lt_one hcard)⟩
  let label := projectiveCyclicLabel f hf
  let last : Fin (Fintype.card X) :=
    finRotatePredecessorZero (Fintype.card X)
  have hlastRotate : finRotate (Fintype.card X) last = 0 := by
    exact finRotate_apply_predecessorZero (Fintype.card X)
  have hlastNeZero : last ≠ 0 := by
    exact finRotatePredecessorZero_ne_zero hcard
  have hzeroLtLast :
      projectiveChartCoordinate f (label 0) <
        projectiveChartCoordinate f (label last) := by
    rw [projectiveCyclicLabel_coordinate_lt_iff]
    exact Fin.pos_iff_ne_zero.mpr hlastNeZero
  have hcoordinate_ne (i : Fin (Fintype.card X)) :
      arrangementProjectiveChartCoordinate (projectiveChartCut f) Q ≠
        projectiveChartCoordinate f (label i) := by
    intro hcoordinate
    apply hQ (label i)
    apply arrangementProjective_eq_of_chartCoordinate_eq
      (projectiveChartCut f) hQden
      (projectiveChartDenominator_ne_zero f (label i))
    simpa only [projectiveChartCoordinate] using hcoordinate
  let S : Finset (Fin (Fintype.card X)) :=
    Finset.univ.filter fun i =>
      projectiveChartCoordinate f (label i) <
        arrangementProjectiveChartCoordinate (projectiveChartCut f) Q
  by_cases hS : S.Nonempty
  · let i : Fin (Fintype.card X) := S.max' hS
    have hiS : i ∈ S := S.max'_mem hS
    have hiLt : projectiveChartCoordinate f (label i) <
        arrangementProjectiveChartCoordinate (projectiveChartCut f) Q :=
      (Finset.mem_filter.mp hiS).2
    by_cases hiLast : i = last
    · have hrightLeft :
          projectiveChartCoordinate f
              (label (finRotate (Fintype.card X) i)) <
            projectiveChartCoordinate f (label i) := by
        rw [hiLast]
        rw [hlastRotate]
        exact hzeroLtLast
      refine ⟨label i, ?_⟩
      rw [projectiveCyclicSuccessor_apply_label]
      rw [arrangementProjectiveCyclic_iff_chart
        (projectiveChartCut f) (f (label i)) Q
          (f (label (finRotate (Fintype.card X) i)))]
      · exact Or.inr (Or.inr
          ⟨by simpa only [projectiveChartCoordinate] using hrightLeft,
            by simpa only [projectiveChartCoordinate] using hiLt⟩)
      · exact projectiveChartDenominator_ne_zero f (label i)
      · exact hQden
      · exact projectiveChartDenominator_ne_zero f
          (label (finRotate (Fintype.card X) i))
    · have hiRotateLt : i < finRotate (Fintype.card X) i :=
        lt_finRotate_of_ne_predecessorZero i (by
          simpa only [last] using hiLast)
      have hiRight : projectiveChartCoordinate f (label i) <
          projectiveChartCoordinate f
            (label (finRotate (Fintype.card X) i)) := by
        rw [projectiveCyclicLabel_coordinate_lt_iff]
        exact hiRotateLt
      have hnotS : finRotate (Fintype.card X) i ∉ S := by
        intro hmem
        have hle : finRotate (Fintype.card X) i ≤ i :=
          S.le_max' _ hmem
        exact (not_le_of_gt hiRotateLt) hle
      have hnotLt : ¬ projectiveChartCoordinate f
          (label (finRotate (Fintype.card X) i)) <
            arrangementProjectiveChartCoordinate (projectiveChartCut f) Q := by
        intro hlt
        apply hnotS
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlt⟩
      have hQLt : arrangementProjectiveChartCoordinate (projectiveChartCut f) Q <
          projectiveChartCoordinate f
            (label (finRotate (Fintype.card X) i)) :=
        lt_of_le_of_ne (le_of_not_gt hnotLt)
          (hcoordinate_ne (finRotate (Fintype.card X) i))
      refine ⟨label i, ?_⟩
      rw [projectiveCyclicSuccessor_apply_label]
      rw [arrangementProjectiveCyclic_iff_chart
        (projectiveChartCut f) (f (label i)) Q
          (f (label (finRotate (Fintype.card X) i)))]
      · exact Or.inl
          ⟨by simpa only [projectiveChartCoordinate] using hiLt,
            by simpa only [projectiveChartCoordinate] using hQLt⟩
      · exact projectiveChartDenominator_ne_zero f (label i)
      · exact hQden
      · exact projectiveChartDenominator_ne_zero f
          (label (finRotate (Fintype.card X) i))
  · have hzeroNotS : (0 : Fin (Fintype.card X)) ∉ S := by
      intro hzeroS
      exact hS ⟨0, hzeroS⟩
    have hnotLt : ¬ projectiveChartCoordinate f (label 0) <
        arrangementProjectiveChartCoordinate (projectiveChartCut f) Q := by
      intro hlt
      apply hzeroNotS
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlt⟩
    have hQLtZero : arrangementProjectiveChartCoordinate (projectiveChartCut f) Q <
        projectiveChartCoordinate f (label 0) :=
      lt_of_le_of_ne (le_of_not_gt hnotLt) (hcoordinate_ne 0)
    refine ⟨label last, ?_⟩
    rw [projectiveCyclicSuccessor_apply_label]
    rw [arrangementProjectiveCyclic_iff_chart
      (projectiveChartCut f) (f (label last)) Q
        (f (label (finRotate (Fintype.card X) last)))]
    · exact Or.inr (Or.inl
        ⟨by simpa only [projectiveChartCoordinate, hlastRotate] using hQLtZero,
          by simpa only [projectiveChartCoordinate, hlastRotate] using hzeroLtLast⟩)
    · exact projectiveChartDenominator_ne_zero f (label last)
    · exact hQden
    · exact projectiveChartDenominator_ne_zero f
        (label (finRotate (Fintype.card X) last))

/-- Coverage of the wrap-around gap when the unmarked point is the pole of
the chosen affine chart. -/
private theorem exists_realProjectiveCyclic_between_successor_of_chartPole
    (f : X → RealProjectiveOnePoint) (hf : Function.Injective f)
    (hcard : 1 < Fintype.card X) (Q : RealProjectiveOnePoint)
    (hQden : Q.rep 1 - projectiveChartCut f * Q.rep 0 = 0) :
    ∃ x : X, RealProjectiveCyclic (f x) Q
      (f (projectiveCyclicSuccessor f hf x)) := by
  classical
  letI : NeZero (Fintype.card X) :=
    ⟨Nat.ne_of_gt (lt_trans zero_lt_one hcard)⟩
  let label := projectiveCyclicLabel f hf
  let last : Fin (Fintype.card X) :=
    finRotatePredecessorZero (Fintype.card X)
  let P := f (label last)
  let R := f (label 0)
  let t := projectiveChartCut f
  let pden := P.rep 1 - t * P.rep 0
  let rden := R.rep 1 - t * R.rep 0
  have hpden : pden ≠ 0 := by
    exact projectiveChartDenominator_ne_zero f (label last)
  have hrden : rden ≠ 0 := by
    exact projectiveChartDenominator_ne_zero f (label 0)
  have hlastRotate : finRotate (Fintype.card X) last = 0 :=
    finRotate_apply_predecessorZero (Fintype.card X)
  have hlastNeZero : last ≠ 0 :=
    finRotatePredecessorZero_ne_zero hcard
  have hcoord : arrangementProjectiveChartCoordinate t R <
      arrangementProjectiveChartCoordinate t P := by
    change projectiveChartCoordinate f (label 0) <
      projectiveChartCoordinate f (label last)
    rw [projectiveCyclicLabel_coordinate_lt_iff]
    exact Fin.pos_iff_ne_zero.mpr hlastNeZero
  have hq0 : Q.rep 0 ≠ 0 := by
    intro hzero
    have hq1 : Q.rep 1 = 0 := by
      rw [hzero, mul_zero, sub_zero] at hQden
      exact hQden
    apply Q.rep_nonzero
    funext i
    fin_cases i
    · exact hzero
    · exact hq1
  have hq1 : Q.rep 1 = t * Q.rep 0 := by
    change Q.rep 1 - t * Q.rep 0 = 0 at hQden
    linarith
  have hPQ : realProjectiveBracket P.rep Q.rep =
      -(Q.rep 0) * pden := by
    unfold realProjectiveBracket
    rw [hq1]
    dsimp only [pden]
    ring
  have hQR : realProjectiveBracket Q.rep R.rep =
      Q.rep 0 * rden := by
    unfold realProjectiveBracket
    rw [hq1]
    dsimp only [rden]
    ring
  have hratio : realProjectiveBracket R.rep P.rep / (rden * pden) < 0 := by
    rw [← arrangementProjectiveChartCoordinate_sub_eq t R P hrden hpden]
    exact sub_neg.mpr hcoord
  have hden : rden * pden ≠ 0 := mul_ne_zero hrden hpden
  have hdenBracket :
      (rden * pden) * realProjectiveBracket R.rep P.rep < 0 := by
    have hid :
        (rden * pden) * realProjectiveBracket R.rep P.rep =
          (rden * pden) ^ 2 *
            (realProjectiveBracket R.rep P.rep / (rden * pden)) := by
      field_simp [hden]
    rw [hid]
    exact mul_neg_of_pos_of_neg (sq_pos_of_ne_zero hden) hratio
  have htriple : 0 < realProjectiveTripleBracket P.rep Q.rep R.rep := by
    rw [realProjectiveTripleBracket, hPQ, hQR]
    have hfactor :
        (-(Q.rep 0) * pden) * (Q.rep 0 * rden) *
            realProjectiveBracket R.rep P.rep =
          (-(Q.rep 0) ^ 2) *
            ((rden * pden) * realProjectiveBracket R.rep P.rep) := by
      ring
    rw [hfactor]
    exact mul_pos_of_neg_of_neg (neg_neg_of_pos (sq_pos_of_ne_zero hq0))
      hdenBracket
  refine ⟨label last, ?_⟩
  rw [projectiveCyclicSuccessor_apply_label, hlastRotate]
  rw [realProjectiveCyclic_iff_rep_tripleBracket]
  exact htriple

/-- Every unmarked point of `RP¹`, including the chosen chart pole, belongs
to one of the genuine cyclic gaps of a finite injective marked family. -/
theorem exists_realProjectiveCyclic_between_projectiveCyclicSuccessor
    (f : X → RealProjectiveOnePoint) (hf : Function.Injective f)
    (hcard : 1 < Fintype.card X) (Q : RealProjectiveOnePoint)
    (hQ : ∀ x : X, Q ≠ f x) :
    ∃ x : X, RealProjectiveCyclic (f x) Q
      (f (projectiveCyclicSuccessor f hf x)) := by
  by_cases hQden :
      Q.rep 1 - projectiveChartCut f * Q.rep 0 ≠ 0
  · exact exists_realProjectiveCyclic_between_projectiveCyclicSuccessor_of_ne
      f hf hcard Q hQ hQden
  · exact exists_realProjectiveCyclic_between_successor_of_chartPole
      f hf hcard Q (not_ne_iff.mp hQden)

/-- The geometrically defined cyclic successor is not a loop whenever the
underlying marked family has another point.  This is the finite fact needed
to rule out degenerate projective-edge loops in a non-pencil arrangement. -/
theorem projectiveCyclicSuccessor_ne_self_of_exists_ne
    (f : X → RealProjectiveOnePoint) (hf : Function.Injective f) (x : X)
    (hother : ∃ y : X, y ≠ x) :
    projectiveCyclicSuccessor f hf x ≠ x := by
  let i : Fin (Fintype.card X) := (projectiveCyclicLabel f hf).symm x
  have hi : projectiveCyclicLabel f hf i = x :=
    (projectiveCyclicLabel f hf).apply_symm_apply x
  obtain ⟨y, hy⟩ := hother
  have hcard : 1 < Fintype.card X :=
    Fintype.one_lt_card_iff.mpr ⟨x, y, hy.symm⟩
  intro hfixed
  have hlabels : projectiveCyclicLabel f hf (finRotate (Fintype.card X) i) =
      projectiveCyclicLabel f hf i := by
    calc
      projectiveCyclicLabel f hf (finRotate (Fintype.card X) i) =
          projectiveCyclicSuccessor f hf
            (projectiveCyclicLabel f hf i) :=
        (projectiveCyclicSuccessor_apply_label f hf i).symm
      _ = projectiveCyclicSuccessor f hf x := by rw [hi]
      _ = x := hfixed
      _ = projectiveCyclicLabel f hf i := hi.symm
  exact finRotate_ne_self_of_one_lt hcard i
    ((projectiveCyclicLabel f hf).injective hlabels)

private theorem not_sbtw_finRotate
    {n : ℕ} (i k : Fin n) :
    ¬ sbtw i k (finRotate n i) := by
  cases n with
  | zero => exact Fin.elim0 i
  | succ n =>
      by_cases hlast : i = Fin.last n
      · subst i
        rw [finRotate_last, Fin.sbtw_iff]
        intro h
        rcases h with h | h | h
        · exact (not_lt_of_ge (Fin.le_last k)) h.1
        · exact (not_lt_of_ge (Fin.zero_le k)) h.1
        · exact (not_lt_of_ge (Fin.le_last k)) h.2
      · have hi : (i : ℕ) < n := Fin.lt_last_iff_ne_last.mpr hlast
        have hrotate : (finRotate (n + 1) i : ℕ) = i + 1 :=
          coe_finRotate_of_ne_last hlast
        rw [Fin.sbtw_iff]
        intro h
        rcases h with h | h | h <;> omega

/-- No marked projective parameter lies strictly between a cyclic label and
its successor.  This is the formal geometric-adjacency certificate for the
successor construction. -/
theorem projectiveCyclicLabel_no_between_successor
    (f : X → RealProjectiveOnePoint) (hf : Function.Injective f)
    (i k : Fin (Fintype.card X)) :
    ¬ RealProjectiveCyclic
      (f (projectiveCyclicLabel f hf i))
      (f (projectiveCyclicLabel f hf k))
      (f (projectiveCyclicLabel f hf
        (finRotate (Fintype.card X) i))) := by
  rw [projectiveCyclicLabel_cyclic_iff_sbtw]
  exact not_sbtw_finRotate i k

/-- No member of the marked family lies in the open cyclic gap beginning at
another marked member. -/
theorem not_realProjectiveCyclic_marked_between_projectiveCyclicSuccessor
    (f : X → RealProjectiveOnePoint) (hf : Function.Injective f)
    (x y : X) :
    ¬ RealProjectiveCyclic (f x) (f y)
      (f (projectiveCyclicSuccessor f hf x)) := by
  let i := (projectiveCyclicLabel f hf).symm x
  let k := (projectiveCyclicLabel f hf).symm y
  have hi : projectiveCyclicLabel f hf i = x :=
    (projectiveCyclicLabel f hf).apply_symm_apply x
  have hk : projectiveCyclicLabel f hf k = y :=
    (projectiveCyclicLabel f hf).apply_symm_apply y
  rw [← hi, ← hk, projectiveCyclicSuccessor_apply_label]
  exact projectiveCyclicLabel_no_between_successor f hf i k

/-- If two open intervals of a strict circular order contain the same point,
one of their starting points lies in the other interval. -/
private theorem sbtw_overlap_startpoint
    {Y : Type*} [CircularOrder Y] {a b c d z : Y}
    (hab : sbtw a z b) (hcd : sbtw c z d) (hac : a ≠ c) :
    sbtw a c b ∨ sbtw c a d := by
  have haz : a ≠ z := by
    intro h
    subst z
    exact sbtw_irrefl_left hab
  have hcz : c ≠ z := by
    intro h
    subst z
    exact sbtw_irrefl_left hcd
  rcases btw_total a c z with hacz | hzca
  · by_cases hreverse : btw z c a
    · rcases hacz.antisymm hreverse with hac' | hcz' | hza'
      · exact (hac hac').elim
      · exact (hcz hcz').elim
      · exact (haz hza'.symm).elim
    · exact Or.inl ((hacz.sbtw_of_not_btw hreverse).trans_right hab)
  · have hcaz : btw c a z := hzca.cyclic_left
    by_cases hreverse : btw z a c
    · rcases hcaz.antisymm hreverse with hca' | haz' | hzc'
      · exact (hac hca'.symm).elim
      · exact (haz haz').elim
      · exact (hcz hzc'.symm).elim
    · exact Or.inr ((hcaz.sbtw_of_not_btw hreverse).trans_right hcd)

/-- An unmarked projective point can lie in at most one successor gap. -/
theorem unique_realProjectiveCyclic_between_projectiveCyclicSuccessor
    (f : X → RealProjectiveOnePoint) (hf : Function.Injective f)
    (Q : RealProjectiveOnePoint) {x y : X}
    (hx : RealProjectiveCyclic (f x) Q
      (f (projectiveCyclicSuccessor f hf x)))
    (hy : RealProjectiveCyclic (f y) Q
      (f (projectiveCyclicSuccessor f hf y))) :
    x = y := by
  classical
  by_contra hxy
  let g : Fin 5 → RealProjectiveOnePoint :=
    ![f x, Q, f (projectiveCyclicSuccessor f hf x),
      f y, f (projectiveCyclicSuccessor f hf y)]
  let t := projectiveChartCut g
  have h0 : (f x).rep 1 - t * (f x).rep 0 ≠ 0 := by
    simpa [g, t] using
      (projectiveChartDenominator_ne_zero g (0 : Fin 5))
  have h1 : Q.rep 1 - t * Q.rep 0 ≠ 0 := by
    simpa [g, t] using
      (projectiveChartDenominator_ne_zero g (1 : Fin 5))
  have h2 : (f (projectiveCyclicSuccessor f hf x)).rep 1 -
      t * (f (projectiveCyclicSuccessor f hf x)).rep 0 ≠ 0 := by
    simpa [g, t] using
      (projectiveChartDenominator_ne_zero g (2 : Fin 5))
  have h3 : (f y).rep 1 - t * (f y).rep 0 ≠ 0 := by
    simpa [g, t] using
      (projectiveChartDenominator_ne_zero g (3 : Fin 5))
  have h4 : (f (projectiveCyclicSuccessor f hf y)).rep 1 -
      t * (f (projectiveCyclicSuccessor f hf y)).rep 0 ≠ 0 := by
    simpa [g, t] using
      (projectiveChartDenominator_ne_zero g (4 : Fin 5))
  letI : CircularOrder ℝ := LinearOrder.toCircularOrder ℝ
  have hxs : sbtw
      (arrangementProjectiveChartCoordinate t (f x))
      (arrangementProjectiveChartCoordinate t Q)
      (arrangementProjectiveChartCoordinate t
        (f (projectiveCyclicSuccessor f hf x))) := by
    rw [sbtw_iff]
    exact (arrangementProjectiveCyclic_iff_chart t _ _ _ h0 h1 h2).mp hx
  have hys : sbtw
      (arrangementProjectiveChartCoordinate t (f y))
      (arrangementProjectiveChartCoordinate t Q)
      (arrangementProjectiveChartCoordinate t
        (f (projectiveCyclicSuccessor f hf y))) := by
    rw [sbtw_iff]
    exact (arrangementProjectiveCyclic_iff_chart t _ _ _ h3 h1 h4).mp hy
  have hstart : arrangementProjectiveChartCoordinate t (f x) ≠
      arrangementProjectiveChartCoordinate t (f y) := by
    intro heq
    apply hxy
    apply hf
    exact arrangementProjective_eq_of_chartCoordinate_eq t h0 h3 heq
  rcases sbtw_overlap_startpoint hxs hys hstart with hxyGap | hyxGap
  · apply not_realProjectiveCyclic_marked_between_projectiveCyclicSuccessor
      f hf x y
    apply (arrangementProjectiveCyclic_iff_chart t _ _ _ h0 h3 h2).mpr
    simpa only [sbtw_iff] using hxyGap
  · apply not_realProjectiveCyclic_marked_between_projectiveCyclicSuccessor
      f hf y x
    apply (arrangementProjectiveCyclic_iff_chart t _ _ _ h3 h0 h4).mpr
    simpa only [sbtw_iff] using hyxGap

/-- Full pointwise partition of the complement of a finite marked family by
its genuine open cyclic successor gaps. -/
theorem existsUnique_realProjectiveCyclic_between_projectiveCyclicSuccessor
    (f : X → RealProjectiveOnePoint) (hf : Function.Injective f)
    (hcard : 1 < Fintype.card X) (Q : RealProjectiveOnePoint)
    (hQ : ∀ x : X, Q ≠ f x) :
    ∃! x : X, RealProjectiveCyclic (f x) Q
      (f (projectiveCyclicSuccessor f hf x)) := by
  obtain ⟨x, hx⟩ :=
    exists_realProjectiveCyclic_between_projectiveCyclicSuccessor
      f hf hcard Q hQ
  refine ⟨x, hx, ?_⟩
  intro y hy
  exact unique_realProjectiveCyclic_between_projectiveCyclicSuccessor
    f hf Q hy hx

/-! ## Parametrizing an `RP²` projective line by `RP¹` -/

namespace FiniteProjectiveLineArrangement

/-- The linear functional whose kernel is the homogeneous carrier of a
projective line. -/
noncomputable def projectiveLineEvaluation (l : RealProjectiveLine) :
    (Fin 3 → ℝ) →ₗ[ℝ] ℝ where
  toFun := fun v => v ⬝ᵥ l.rep
  map_add' := by
    intro v w
    simp [add_dotProduct]
  map_smul' := by
    intro a v
    simp [smul_dotProduct]

theorem projectiveLineKernel_eq_ker
    (l : RealProjectiveLine) :
    projectiveLineKernel l = LinearMap.ker (projectiveLineEvaluation l) := by
  ext v
  change (v ⬝ᵥ l.rep = 0) ↔ (v ⬝ᵥ l.rep = 0)
  rfl

theorem projectiveLineEvaluation_ne_zero
    (l : RealProjectiveLine) : projectiveLineEvaluation l ≠ 0 := by
  intro hzero
  have hself : l.rep ⬝ᵥ l.rep = 0 := by
    have happly := congrArg
      (fun g : (Fin 3 → ℝ) →ₗ[ℝ] ℝ => g l.rep) hzero
    simpa [projectiveLineEvaluation] using happly
  exact l.rep_nonzero (dotProduct_self_eq_zero.mp hself)

/-- Every homogeneous real projective line has a two-dimensional carrier. -/
theorem finrank_projectiveLineKernel
    (l : RealProjectiveLine) :
    Module.finrank ℝ (projectiveLineKernel l) = 2 := by
  rw [projectiveLineKernel_eq_ker]
  have hdim := Module.Dual.finrank_ker_add_one_of_ne_zero
    (projectiveLineEvaluation_ne_zero l)
  rw [Module.finrank_pi] at hdim
  norm_num at hdim
  omega

/-- A linear parametrization of the two-dimensional carrier of a projective
line.  It chooses coordinates only for the construction; the later cyclic
label theorem certifies the resulting order against the intrinsic relation. -/
noncomputable def projectiveLineKernelEquiv
    (l : RealProjectiveLine) :
    RealProjectiveLineVector ≃ₗ[ℝ] projectiveLineKernel l :=
  LinearEquiv.ofFinrankEq _ _ (by
    calc
      Module.finrank ℝ RealProjectiveLineVector = 2 := by
        norm_num [Module.finrank_pi]
      _ = Module.finrank ℝ (projectiveLineKernel l) :=
        (finrank_projectiveLineKernel l).symm)

/-- The ambient homogeneous linear map obtained by including the chosen
kernel parametrization. -/
noncomputable def projectiveLineParameterLinearMap
    (l : RealProjectiveLine) :
    RealProjectiveLineVector →ₗ[ℝ] (Fin 3 → ℝ) :=
  (Submodule.subtype (projectiveLineKernel l)).comp
    (projectiveLineKernelEquiv l).toLinearMap

theorem projectiveLineParameterLinearMap_injective
    (l : RealProjectiveLine) :
    Function.Injective (projectiveLineParameterLinearMap l) :=
  (Submodule.subtype_injective _).comp (projectiveLineKernelEquiv l).injective

theorem projectiveLineParameterLinearMap_mem_kernel
    (l : RealProjectiveLine) (u : RealProjectiveLineVector) :
    projectiveLineParameterLinearMap l u ∈ projectiveLineKernel l := by
  change ((projectiveLineKernelEquiv l) u : Fin 3 → ℝ) ∈
    projectiveLineKernel l
  exact ((projectiveLineKernelEquiv l) u).property

/-- The projective parametrization of the points on an indexed `RP²` line. -/
noncomputable def projectiveLineParameter
    (l : RealProjectiveLine) :
    RealProjectiveOnePoint → RealProjectivePoint :=
  Projectivization.map (projectiveLineParameterLinearMap l)
    (projectiveLineParameterLinearMap_injective l)

theorem projectiveLineParameter_injective
    (l : RealProjectiveLine) :
    Function.Injective (projectiveLineParameter l) :=
  Projectivization.map_injective (projectiveLineParameterLinearMap l)
    (projectiveLineParameterLinearMap_injective l)

theorem projectiveLineParameter_incident
    (l : RealProjectiveLine) (P : RealProjectiveOnePoint) :
    (projectiveLineParameter l P).orthogonal l := by
  induction P using Projectivization.ind with
  | h u hu =>
      have hcore :
          (Projectivization.mk ℝ (projectiveLineParameterLinearMap l u)
            (by
              simpa only [map_zero] using
                Function.Injective.ne
                  (projectiveLineParameterLinearMap_injective l) hu)).orthogonal
            (Projectivization.mk ℝ l.rep l.rep_nonzero) := by
        rw [Projectivization.orthogonal_mk]
        change (projectiveLineParameterLinearMap l u ⬝ᵥ l.rep) = 0
        exact projectiveLineParameterLinearMap_mem_kernel l u
      rw [Projectivization.mk_rep] at hcore
      simpa only [projectiveLineParameter, Projectivization.map_mk] using hcore

/-- The cyclic orientation transported from the `RP¹` parametrization to
points of the specified projective line. -/
def ProjectiveLineCyclic
    (l : RealProjectiveLine)
    (p q r : RealProjectivePoint) : Prop :=
  ∃ P Q R : RealProjectiveOnePoint,
    projectiveLineParameter l P = p ∧
    projectiveLineParameter l Q = q ∧
    projectiveLineParameter l R = r ∧
    RealProjectiveCyclic P Q R

theorem projectiveLineCyclic_parameter_iff
    (l : RealProjectiveLine) (P Q R : RealProjectiveOnePoint) :
    ProjectiveLineCyclic l
      (projectiveLineParameter l P)
      (projectiveLineParameter l Q)
      (projectiveLineParameter l R) ↔
      RealProjectiveCyclic P Q R := by
  constructor
  · rintro ⟨P', Q', R', hP, hQ, hR, hcyclic⟩
    have hP' : P' = P := projectiveLineParameter_injective l hP
    have hQ' : Q' = Q := projectiveLineParameter_injective l hQ
    have hR' : R' = R := projectiveLineParameter_injective l hR
    simpa [hP', hQ', hR'] using hcyclic
  · intro hcyclic
    exact ⟨P, Q, R, rfl, rfl, rfl, hcyclic⟩

theorem projectiveLineCyclic_incident_left
    {l : RealProjectiveLine} {p q r : RealProjectivePoint}
    (h : ProjectiveLineCyclic l p q r) : p.orthogonal l := by
  rcases h with ⟨P, Q, R, hP, hQ, hR, hcyclic⟩
  rw [← hP]
  exact projectiveLineParameter_incident l P

theorem projectiveLineCyclic_incident_middle
    {l : RealProjectiveLine} {p q r : RealProjectivePoint}
    (h : ProjectiveLineCyclic l p q r) : q.orthogonal l := by
  rcases h with ⟨P, Q, R, hP, hQ, hR, hcyclic⟩
  rw [← hQ]
  exact projectiveLineParameter_incident l Q

theorem projectiveLineCyclic_incident_right
    {l : RealProjectiveLine} {p q r : RealProjectivePoint}
    (h : ProjectiveLineCyclic l p q r) : r.orthogonal l := by
  rcases h with ⟨P, Q, R, hP, hQ, hR, hcyclic⟩
  rw [← hR]
  exact projectiveLineParameter_incident l R

/-- Every projective point incident with the line has a parameter in the
chosen `RP¹` model of that line. -/
theorem exists_projectiveLineParameter_of_incident
    (l : RealProjectiveLine) (p : RealProjectivePoint)
    (hp : p.orthogonal l) :
    ∃ P : RealProjectiveOnePoint, projectiveLineParameter l P = p := by
  let q : projectiveLineKernel l :=
    ⟨p.rep, (orthogonal_iff_rep_mem_projectiveLineKernel p l).mp hp⟩
  let u : RealProjectiveLineVector := (projectiveLineKernelEquiv l).symm q
  have hq : q ≠ 0 := by
    intro hzero
    apply p.rep_nonzero
    have hval := congrArg
      (fun z : projectiveLineKernel l => (z : Fin 3 → ℝ)) hzero
    simpa [q] using hval
  have hu : u ≠ 0 := by
    intro hzero
    apply hq
    calc
      q = projectiveLineKernelEquiv l u := by
        dsimp [u]
        exact ((projectiveLineKernelEquiv l).apply_symm_apply q).symm
      _ = projectiveLineKernelEquiv l 0 := by rw [hzero]
      _ = 0 := (projectiveLineKernelEquiv l).map_zero
  have hvalue : projectiveLineParameterLinearMap l u = p.rep := by
    change ↑((projectiveLineKernelEquiv l) u) = p.rep
    change ↑((projectiveLineKernelEquiv l)
      ((projectiveLineKernelEquiv l).symm q)) = p.rep
    rw [(projectiveLineKernelEquiv l).apply_symm_apply]
  refine ⟨Projectivization.mk ℝ u hu, ?_⟩
  rw [projectiveLineParameter, Projectivization.map_mk, ← p.mk_rep]
  apply (Projectivization.mk_eq_mk_iff' ℝ _ _ _ _).mpr
  refine ⟨1, ?_⟩
  simpa using hvalue.symm

/-- The `RP¹` parameter of an incident projective point is unique. -/
theorem existsUnique_projectiveLineParameter_of_incident
    (l : RealProjectiveLine) (p : RealProjectivePoint)
    (hp : p.orthogonal l) :
    ∃! P : RealProjectiveOnePoint, projectiveLineParameter l P = p := by
  rcases exists_projectiveLineParameter_of_incident l p hp with ⟨P, hP⟩
  refine ⟨P, hP, ?_⟩
  intro Q hQ
  exact projectiveLineParameter_injective l (hQ.trans hP.symm)

/-- The inverse parameter selected for an incident point.  Its specification
is proved below; this is choice only of the already uniquely determined
projective parameter, not of a successor. -/
noncomputable def projectiveLineParameterPreimage
    (l : RealProjectiveLine) (p : RealProjectivePoint)
    (hp : p.orthogonal l) : RealProjectiveOnePoint :=
  Classical.choose (exists_projectiveLineParameter_of_incident l p hp)

theorem projectiveLineParameter_preimage_spec
    (l : RealProjectiveLine) (p : RealProjectivePoint)
    (hp : p.orthogonal l) :
    projectiveLineParameter l (projectiveLineParameterPreimage l p hp) = p := by
  unfold projectiveLineParameterPreimage
  exact Classical.choose_spec (exists_projectiveLineParameter_of_incident l p hp)

/-- The points of an actual real projective line are precisely a copy of
`RP¹`.  This packages the kernel parametrization, its injectivity, and its
surjectivity on incident points into one equivalence. -/
noncomputable def projectiveLineParameterEquiv
    (l : RealProjectiveLine) :
    RealProjectiveOnePoint ≃ {p : RealProjectivePoint // p.orthogonal l} where
  toFun P := ⟨projectiveLineParameter l P, projectiveLineParameter_incident l P⟩
  invFun p := projectiveLineParameterPreimage l p.1 p.2
  left_inv P := by
    apply projectiveLineParameter_injective l
    exact projectiveLineParameter_preimage_spec l
      (projectiveLineParameter l P) (projectiveLineParameter_incident l P)
  right_inv p := by
    apply Subtype.ext
    change projectiveLineParameter l
      (projectiveLineParameterPreimage l p.1 p.2) = p.1
    exact projectiveLineParameter_preimage_spec l p.1 p.2

variable {Line : Type*} [Fintype Line] [DecidableEq Line]

/-- The `RP¹` parameter of one marked vertex on an indexed projective line. -/
noncomputable def circularGapSlotParameter
    (A : FiniteProjectiveLineArrangement Line) (l : Line) :
    A.CircularGapSlot l → RealProjectiveOnePoint :=
  fun p => projectiveLineParameterPreimage (A.projectiveLine l) p.1
    (show p.1.orthogonal (A.projectiveLine l) from
      ((A.mem_lineVertexSet l).mp p.2).2)

theorem projectiveLineParameter_circularGapSlotParameter
    (A : FiniteProjectiveLineArrangement Line) (l : Line)
    (p : A.CircularGapSlot l) :
    projectiveLineParameter (A.projectiveLine l)
      (circularGapSlotParameter A l p) = p.1 := by
  unfold circularGapSlotParameter
  exact projectiveLineParameter_preimage_spec (A.projectiveLine l) p.1
    (show p.1.orthogonal (A.projectiveLine l) from
      ((A.mem_lineVertexSet l).mp p.2).2)

theorem circularGapSlotParameter_injective
    (A : FiniteProjectiveLineArrangement Line) (l : Line) :
    Function.Injective (circularGapSlotParameter A l) := by
  intro p q hpq
  apply Subtype.ext
  calc
    p.1 = projectiveLineParameter (A.projectiveLine l)
        (circularGapSlotParameter A l p) :=
      (projectiveLineParameter_circularGapSlotParameter A l p).symm
    _ = projectiveLineParameter (A.projectiveLine l)
        (circularGapSlotParameter A l q) :=
      congrArg (projectiveLineParameter (A.projectiveLine l)) hpq
    _ = q.1 := projectiveLineParameter_circularGapSlotParameter A l q

/-- The cyclic label enumeration of the actual vertices on one arrangement
line. -/
noncomputable def circularGapCyclicLabel
    (A : FiniteProjectiveLineArrangement Line) (l : Line) :
    Fin (Fintype.card (A.CircularGapSlot l)) ≃ A.CircularGapSlot l :=
  projectiveCyclicLabel (circularGapSlotParameter A l)
    (circularGapSlotParameter_injective A l)

/-- The positive cyclic successor on the marked vertices of one arrangement
line. -/
noncomputable def circularGapSuccessorEquiv
    (A : FiniteProjectiveLineArrangement Line) (l : Line) :
    Equiv.Perm (A.CircularGapSlot l) :=
  projectiveCyclicSuccessorEquiv (circularGapSlotParameter A l)
    (circularGapSlotParameter_injective A l)

noncomputable def circularGapSuccessor
    (A : FiniteProjectiveLineArrangement Line) (l : Line) :
    A.CircularGapSlot l → A.CircularGapSlot l :=
  circularGapSuccessorEquiv A l

/-- Synonym emphasizing that `CircularGapSlot` is exactly the finite subtype
of marked vertices on the given arrangement line. -/
noncomputable def lineVertexSuccessor
    (A : FiniteProjectiveLineArrangement Line) (l : Line) :
    A.CircularGapSlot l → A.CircularGapSlot l :=
  circularGapSuccessor A l

theorem circularGapSuccessor_bijective
    (A : FiniteProjectiveLineArrangement Line) (l : Line) :
    Function.Bijective (circularGapSuccessor A l) := by
  simpa [circularGapSuccessor] using (circularGapSuccessorEquiv A l).bijective

theorem circularGapSuccessor_apply_label
    (A : FiniteProjectiveLineArrangement Line) (l : Line)
    (i : Fin (Fintype.card (A.CircularGapSlot l))) :
    circularGapSuccessor A l (circularGapCyclicLabel A l i) =
      circularGapCyclicLabel A l
        (finRotate (Fintype.card (A.CircularGapSlot l)) i) := by
  exact projectiveCyclicSuccessor_apply_label
    (circularGapSlotParameter A l)
    (circularGapSlotParameter_injective A l) i

/-- A cyclic gap successor is a genuinely different marked vertex whenever
the supporting arrangement line has another marked vertex. -/
theorem circularGapSuccessor_ne_self_of_exists_ne
    (A : FiniteProjectiveLineArrangement Line) (l : Line)
    (p : A.CircularGapSlot l) (hother : ∃ q : A.CircularGapSlot l, q ≠ p) :
    circularGapSuccessor A l p ≠ p := by
  exact projectiveCyclicSuccessor_ne_self_of_exists_ne
    (circularGapSlotParameter A l)
    (circularGapSlotParameter_injective A l) p hother

/-- The cyclic labels of an arrangement line are ordered by the transported
projective-line orientation. -/
theorem circularGapCyclicLabel_parameter_cyclic_iff_sbtw
    (A : FiniteProjectiveLineArrangement Line) (l : Line)
    (i j k : Fin (Fintype.card (A.CircularGapSlot l))) :
    RealProjectiveCyclic
      (circularGapSlotParameter A l (circularGapCyclicLabel A l i))
      (circularGapSlotParameter A l (circularGapCyclicLabel A l j))
      (circularGapSlotParameter A l (circularGapCyclicLabel A l k)) ↔
      sbtw i j k :=
  projectiveCyclicLabel_cyclic_iff_sbtw
    (circularGapSlotParameter A l)
    (circularGapSlotParameter_injective A l) i j k

/-- There is no marked parameter strictly between a cyclic label and its
positive successor. -/
theorem circularGapCyclicLabel_no_parameter_between_successor
    (A : FiniteProjectiveLineArrangement Line) (l : Line)
    (i k : Fin (Fintype.card (A.CircularGapSlot l))) :
    ¬ RealProjectiveCyclic
      (circularGapSlotParameter A l (circularGapCyclicLabel A l i))
      (circularGapSlotParameter A l (circularGapCyclicLabel A l k))
      (circularGapSlotParameter A l (circularGapCyclicLabel A l
        (finRotate (Fintype.card (A.CircularGapSlot l)) i))) :=
  projectiveCyclicLabel_no_between_successor
    (circularGapSlotParameter A l)
    (circularGapSlotParameter_injective A l) i k

/-- The same no-between statement, now expressed in the cyclic orientation
transported onto the actual `RP²` points of the arrangement line. -/
theorem circularGapCyclicLabel_no_line_between_successor
    (A : FiniteProjectiveLineArrangement Line) (l : Line)
    (i k : Fin (Fintype.card (A.CircularGapSlot l))) :
    ¬ ProjectiveLineCyclic (A.projectiveLine l)
      (circularGapCyclicLabel A l i).1
      (circularGapCyclicLabel A l k).1
      (circularGapCyclicLabel A l
        (finRotate (Fintype.card (A.CircularGapSlot l)) i)).1 := by
  rw [← projectiveLineParameter_circularGapSlotParameter A l
      (circularGapCyclicLabel A l i),
    ← projectiveLineParameter_circularGapSlotParameter A l
      (circularGapCyclicLabel A l k),
    ← projectiveLineParameter_circularGapSlotParameter A l
      (circularGapCyclicLabel A l
        (finRotate (Fintype.card (A.CircularGapSlot l)) i)),
    projectiveLineCyclic_parameter_iff]
  exact circularGapCyclicLabel_no_parameter_between_successor A l i k

/-- The successor of an arbitrary marked vertex has no other marked vertex
strictly between it and its endpoint in the transported projective cyclic
orientation. -/
theorem circularGapSuccessor_no_line_between
    (A : FiniteProjectiveLineArrangement Line) (l : Line)
    (p q : A.CircularGapSlot l) :
    ¬ ProjectiveLineCyclic (A.projectiveLine l) p.1 q.1
      (circularGapSuccessor A l p).1 := by
  let i := (circularGapCyclicLabel A l).symm p
  let k := (circularGapCyclicLabel A l).symm q
  have hi : circularGapCyclicLabel A l i = p :=
    (circularGapCyclicLabel A l).apply_symm_apply p
  have hk : circularGapCyclicLabel A l k = q :=
    (circularGapCyclicLabel A l).apply_symm_apply q
  rw [← hi, ← hk, circularGapSuccessor_apply_label]
  exact circularGapCyclicLabel_no_line_between_successor A l i k

/-- Regard an edge slot as its initial marked point on the supporting line. -/
noncomputable def edgeSlotAsCircularGapSlot
    (A : FiniteProjectiveLineArrangement Line) (e : A.EdgeSlot) :
    A.CircularGapSlot (A.edgeSlotLine e) :=
  ⟨A.edgeSlotVertex e,
    (A.mem_lineVertexSet (A.edgeSlotLine e)).mpr
      ⟨A.edgeSlotVertex_mem_vertexSet e, A.edgeSlot_incident e⟩⟩

/-- The terminal vertex of the genuine circular gap represented by an edge
slot.  A one-vertex line gives a loop, as it should. -/
noncomputable def edgeSlotEndpoint
    (A : FiniteProjectiveLineArrangement Line) (e : A.EdgeSlot) :
    RealProjectivePoint :=
  (circularGapSuccessor A (A.edgeSlotLine e)
    (edgeSlotAsCircularGapSlot A e)).1

/-- The endpoint of an edge slot is another marked point on the same
supporting projective line. -/
theorem edgeSlotEndpoint_mem_lineVertexSet
    (A : FiniteProjectiveLineArrangement Line) (e : A.EdgeSlot) :
    A.edgeSlotEndpoint e ∈ A.lineVertexSet (A.edgeSlotLine e) := by
  change (circularGapSuccessor A (A.edgeSlotLine e)
    (edgeSlotAsCircularGapSlot A e)).1 ∈
      A.lineVertexSet (A.edgeSlotLine e)
  exact (circularGapSuccessor A (A.edgeSlotLine e)
    (edgeSlotAsCircularGapSlot A e)).2

theorem edgeSlotEndpoint_mem_vertexSet
    (A : FiniteProjectiveLineArrangement Line) (e : A.EdgeSlot) :
    A.edgeSlotEndpoint e ∈ A.vertexSet := by
  exact (A.mem_lineVertexSet (A.edgeSlotLine e)).mp
    (A.edgeSlotEndpoint_mem_lineVertexSet e) |>.1

theorem edgeSlotEndpoint_incident
    (A : FiniteProjectiveLineArrangement Line) (e : A.EdgeSlot) :
    A.Incident (A.edgeSlotEndpoint e) (A.edgeSlotLine e) := by
  exact (A.mem_lineVertexSet (A.edgeSlotLine e)).mp
    (A.edgeSlotEndpoint_mem_lineVertexSet e) |>.2

/-- The terminal endpoint of every edge slot is the actual next marked vertex
on its supporting real projective line: no marked vertex lies in the positive
open arc between them. -/
theorem edgeSlot_no_lineVertex_between_endpoint
    (A : FiniteProjectiveLineArrangement Line) (e : A.EdgeSlot)
    (q : A.CircularGapSlot (A.edgeSlotLine e)) :
    ¬ ProjectiveLineCyclic (A.projectiveLine (A.edgeSlotLine e))
      (A.edgeSlotVertex e) q.1 (A.edgeSlotEndpoint e) := by
  change ¬ ProjectiveLineCyclic (A.projectiveLine (A.edgeSlotLine e))
    (edgeSlotAsCircularGapSlot A e).1 q.1
    (circularGapSuccessor A (A.edgeSlotLine e)
      (edgeSlotAsCircularGapSlot A e)).1
  exact circularGapSuccessor_no_line_between A (A.edgeSlotLine e)
    (edgeSlotAsCircularGapSlot A e) q

/-- The actual oriented arrangement edges: a slot together with its
geometrically determined initial and terminal vertices. -/
abbrev GeometricEdge (A : FiniteProjectiveLineArrangement Line) : Type _ :=
  A.EdgeSlot

def geometricEdgeInitial
    (A : FiniteProjectiveLineArrangement Line) (e : A.GeometricEdge) :
    RealProjectivePoint :=
  A.edgeSlotVertex e

noncomputable def geometricEdgeTerminal
    (A : FiniteProjectiveLineArrangement Line) (e : A.GeometricEdge) :
    RealProjectivePoint :=
  A.edgeSlotEndpoint e

/-- The geometric edge set has exactly the canonical incidence handshake
count.  Adding terminal endpoints changes no edge cardinality. -/
theorem card_geometricEdge_eq_sum_multiplicity
    (A : FiniteProjectiveLineArrangement Line) :
    Fintype.card A.GeometricEdge =
      ∑ p ∈ A.vertexSet, A.multiplicity p :=
  A.card_edgeSlot_eq_sum_multiplicity

/-- The original finite edge census can now be instantiated by genuine
consecutive projective-line gaps.  This supplies exactly the edge-count field
of a future global cellulation, while making no claim yet about faces. -/
noncomputable def geometricEdgeCensus
    (A : FiniteProjectiveLineArrangement Line) : A.EdgeCensus where
  Edge := A.GeometricEdge
  edgeFintype := inferInstance
  edgeCount := A.card_geometricEdge_eq_sum_multiplicity

end FiniteProjectiveLineArrangement

end Erdos506.Incidence
