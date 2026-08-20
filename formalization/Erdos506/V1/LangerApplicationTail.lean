import Erdos506.Incidence.RealPlaneLangerApplicationBypass
import Erdos506.V1.HalfCap

/-!
# The Langer-free V1 tail

For `n ≥ 23`, the rich-block pencil already excludes a block of size
exactly `n / 2` under a counterexample bound.  Thus every nontrivial block
has size at most `n / 2 - 1`.  The cap-sensitive Melchior incidence bound
then supplies enough of row `L` for the large master, without Langer.
-/

namespace Erdos506.V1

open Erdos506.Block
open Erdos506.Block.BlockSystem
open Erdos506.Incidence
open Erdos506.V4
open scoped BigOperators

universe u

private theorem choose_two_even (r : Nat) :
    Nat.choose (2 * r) 2 = r * (2 * r - 1) := by
  have h := Nat.choose_succ_right_eq (2 * r) 1
  simp only [Nat.reduceAdd, Nat.choose_one_right] at h
  have hprod : 2 * r * (2 * r - 1) =
      (r * (2 * r - 1)) * 2 := by ring
  rw [hprod] at h
  omega

private theorem choose_two_odd (r : Nat) :
    Nat.choose (2 * r + 1) 2 = r * (2 * r + 1) := by
  have h := Nat.choose_succ_right_eq (2 * r + 1) 1
  simp only [Nat.reduceAdd, Nat.choose_one_right] at h
  have hprod : (2 * r + 1) * (2 * r + 1 - 1) =
      (r * (2 * r + 1)) * 2 := by
    have hpred : 2 * r + 1 - 1 = 2 * r := by omega
    rw [hpred]
    ring
  rw [hprod] at h
  omega

private theorem six_mul_choose_three (s : Nat) :
    6 * Nat.choose s 3 = s * (s - 1) * (s - 2) := by
  have h3 := Nat.choose_succ_right_eq s 2
  have h2 := Nat.choose_succ_right_eq s 1
  simp only [Nat.reduceAdd, Nat.choose_one_right] at h3 h2
  calc
    6 * Nat.choose s 3 = 2 * (Nat.choose s 3 * 3) := by ring
    _ = 2 * (Nat.choose s 2 * (s - 2)) := by rw [h3]
    _ = (Nat.choose s 2 * 2) * (s - 2) := by ring
    _ = s * (s - 1) * (s - 2) := by rw [h2]

private theorem eighteen_choose_three_int (s : Nat) (hs : 3 ≤ s) :
    18 * (Nat.choose s 3 : Int) =
      3 * (s : Int) * ((s : Int) - 1) * ((s : Int) - 2) := by
  have h := congrArg (fun z : Nat => (z : Int)) (six_mul_choose_three s)
  push_cast [Nat.cast_sub (by omega : 1 ≤ s),
    Nat.cast_sub (by omega : 2 ≤ s)] at h
  nlinarith

private theorem uniformTarget_even (r : Nat) (hr : 1 ≤ r) :
    Erdos506.v1UniformTarget (2 * r) = 1 + 2 * (r - 1) * (r - 1) := by
  have hdiv : (2 * (r - 1) + 1) / 2 = r - 1 := by omega
  have hprod : (r - 1) * (2 * (r - 1) + 1) =
      2 * (r - 1) * (r - 1) + (r - 1) := by
    ring
  unfold Erdos506.v1UniformTarget
  rw [show 2 * r - 1 = 2 * (r - 1) + 1 by omega,
    choose_two_odd (r - 1), hdiv, hprod]
  omega

private theorem uniformTarget_odd (r : Nat) :
    Erdos506.v1UniformTarget (2 * r + 1) = 1 + 2 * r * (r - 1) := by
  by_cases hr : r = 0
  · subst r
    norm_num [Erdos506.v1UniformTarget, Nat.choose]
  have hrPos : 1 ≤ r := Nat.one_le_iff_ne_zero.mpr hr
  have hdiv : (2 * r) / 2 = r := by omega
  have hprod : r * (2 * r - 1) = 2 * r * (r - 1) + r := by
    have hpred : 2 * r - 1 = 2 * (r - 1) + 1 := by omega
    rw [hpred]
    ring
  unfold Erdos506.v1UniformTarget
  rw [show 2 * r + 1 - 1 = 2 * r by omega,
    choose_two_even r, hdiv, hprod]
  omega

/-- At `n ≥ 23`, even a block of size exactly `n / 2` already reaches
the uniform target by the rich-block pencil count. -/
theorem v1UniformTarget_le_richBlockPencilBound_half
    (n : Nat) (hn : 23 ≤ n) :
    Erdos506.v1UniformTarget n ≤ richBlockPencilBound n (n / 2) := by
  rcases n.even_or_odd' with ⟨r, hnEven | hnOdd⟩
  · subst n
    rcases r.even_or_odd' with ⟨a, hrEven | hrOdd⟩
    · subst r
      have ha : 6 ≤ a := by omega
      have hhalfN : 2 * (2 * a) / 2 = 2 * a := by omega
      rw [hhalfN]
      unfold richBlockPencilBound
      apply Nat.le_sub_of_add_le
      rw [uniformTarget_even (2 * a) (by omega),
        show 2 * (2 * a) - 2 * a = 2 * a by omega,
        choose_two_even a,
        show 2 * a / 2 = a by omega]
      have ht : (0 : Int) ≤ (a : Int) - 6 := by omega
      have hpoly :
          0 < 2 * (a : Int)^3 - 11 * (a : Int)^2 +
            8 * (a : Int) - 2 := by
        calc
          2 * (a : Int)^3 - 11 * (a : Int)^2 + 8 * (a : Int) - 2 =
              2 * ((a : Int) - 6)^3 + 25 * ((a : Int) - 6)^2 +
                92 * ((a : Int) - 6) + 82 := by ring
          _ > 0 := by positivity
      have hsub : a ≤ a * (2 * a - 1) :=
        Nat.le_mul_of_pos_right a (by omega)
      have hcast :
          ((1 + 2 * (2 * a - 1) * (2 * a - 1) +
              (a * (2 * a - 1)) * a : Nat) : Int) ≤
            ((1 + 2 * a * (a * (2 * a - 1) - a) : Nat) : Int) := by
        push_cast [Nat.cast_sub hsub, Nat.cast_sub (by omega : 1 ≤ 2 * a)]
        nlinarith
      exact_mod_cast hcast

    · subst r
      have ha : 5 ≤ a := by omega
      have hhalfN : 2 * (2 * a + 1) / 2 = 2 * a + 1 := by omega
      rw [hhalfN]
      unfold richBlockPencilBound
      apply Nat.le_sub_of_add_le
      rw [uniformTarget_even (2 * a + 1) (by omega),
        show 2 * (2 * a + 1) - (2 * a + 1) = 2 * a + 1 by omega,
        choose_two_odd a,
        show (2 * a + 1) / 2 = a by omega]
      have hsub : a ≤ a * (2 * a + 1) := by nlinarith
      have hcore : (8 : Int) ≤ 2 * (a : Int) + 1 := by omega
      have hcast :
          ((1 + 2 * (2 * a) * (2 * a) +
              (a * (2 * a + 1)) * a : Nat) : Int) ≤
            ((1 + (2 * a + 1) *
              (a * (2 * a + 1) - a) : Nat) : Int) := by
        push_cast [Nat.cast_sub hsub]
        have haNonneg : (0 : Int) ≤ (a : Int) := by positivity
        nlinarith [mul_nonneg (sq_nonneg (a : Int)) (sub_nonneg.mpr hcore)]
      exact_mod_cast hcast
  · subst n
    rcases r.even_or_odd' with ⟨a, hrEven | hrOdd⟩
    · subst r
      have ha : 6 ≤ a := by omega
      have hhalfN : (2 * (2 * a) + 1) / 2 = 2 * a := by omega
      rw [hhalfN]
      unfold richBlockPencilBound
      apply Nat.le_sub_of_add_le
      rw [uniformTarget_odd (2 * a),
        show 2 * (2 * a) + 1 - 2 * a = 2 * a + 1 by omega,
        choose_two_even a, choose_two_odd a,
        show 2 * a / 2 = a by omega]
      have ht : (0 : Int) ≤ (a : Int) - 6 := by omega
      have hcore :
          0 < 2 * (a : Int)^2 - 11 * (a : Int) + 2 := by
        calc
          2 * (a : Int)^2 - 11 * (a : Int) + 2 =
              2 * ((a : Int) - 6)^2 + 13 * ((a : Int) - 6) + 8 := by ring
          _ > 0 := by positivity
      have hsub : a ≤ a * (2 * a - 1) :=
        Nat.le_mul_of_pos_right a (by omega)
      have hcast :
          ((1 + 2 * (2 * a) * (2 * a - 1) +
              (a * (2 * a + 1)) * a : Nat) : Int) ≤
            ((1 + (2 * a + 1) *
              (a * (2 * a - 1) - a) : Nat) : Int) := by
        push_cast [Nat.cast_sub hsub,
          Nat.cast_sub (by omega : 1 ≤ 2 * a)]
        have haPos : (0 : Int) < (a : Int) := by omega
        nlinarith [mul_pos haPos hcore]
      exact_mod_cast hcast
    · subst r
      have ha : 5 ≤ a := by omega
      have hhalfN : (2 * (2 * a + 1) + 1) / 2 = 2 * a + 1 := by omega
      rw [hhalfN]
      unfold richBlockPencilBound
      apply Nat.le_sub_of_add_le
      rw [uniformTarget_odd (2 * a + 1),
        show 2 * (2 * a + 1) + 1 - (2 * a + 1) =
          2 * a + 2 by omega,
        show 2 * a + 2 = 2 * (a + 1) by omega,
        choose_two_odd a, choose_two_even (a + 1),
        show (2 * a + 1) / 2 = a by omega]
      have ht : (0 : Int) ≤ (a : Int) - 5 := by omega
      have hcore :
          0 < 2 * (a : Int)^2 - 7 * (a : Int) - 5 := by
        calc
          2 * (a : Int)^2 - 7 * (a : Int) - 5 =
              2 * ((a : Int) - 5)^2 + 13 * ((a : Int) - 5) + 10 := by ring
          _ > 0 := by positivity
      have hsub : a ≤ a * (2 * a + 1) := by nlinarith
      have hcast :
          ((1 + 2 * (2 * a + 1) * (2 * a) +
              ((a + 1) * (2 * a + 1)) * a : Nat) : Int) ≤
            ((1 + (2 * a + 2) *
              (a * (2 * a + 1) - a) : Nat) : Int) := by
        push_cast [Nat.cast_sub hsub]
        have haPos : (0 : Int) < (a : Int) := by omega
        nlinarith [mul_pos haPos hcore]
      exact_mod_cast hcast

/-- Below the uniform target, the rich-block pencil improves the usual
half cap by one throughout the tail `n ≥ 23`. -/
theorem predHalfBlockCap_of_circleCount_lt_v1UniformTarget
    {α : Type u} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (hadm : Admissible cfg)
    (hcard : 23 ≤ Fintype.card α)
    (hcount : Erdos506.V4.circleCount cfg <
      Erdos506.v1UniformTarget (Fintype.card α)) :
    BlockSizeCap (blockSystem cfg) (Fintype.card α / 2 - 1) := by
  have hhalf := halfBlockCap_of_circleCount_lt_v1UniformTarget
    cfg hadm (by omega) hcount
  intro b hbsize
  have hle := hhalf b hbsize
  by_contra hnot
  have heq : ((blockSystem cfg).support b).card = Fintype.card α / 2 := by
    omega
  have hproper : (geometricBlockSupport cfg b).card < Fintype.card α :=
    geometricBlockSupport_card_lt_of_admissible cfg hadm b
  have hpencil := richBlockPencilBound_le_totalCircleCount
    (blockSystem cfg) b hproper hbsize
  have htarget := v1UniformTarget_le_richBlockPencilBound_half
    (Fintype.card α) hcard
  rw [heq] at hpencil
  rw [totalCircleCount_eq_card_determinedCircle,
    ← Erdos506.V3.circleCount_eq_card_determinedCircle] at hpencil
  exact (not_le_of_gt hcount) (htarget.trans hpencil)

/-- The large-master numerator after replacing Langer's row estimate by the
cap-sensitive Melchior estimate and clearing its factor `M + 2`. -/
def capMelchiorMasterNumerator (n M : Nat) : Int :=
  ((M : Int) + 2) *
      (18 * (Nat.choose n 3 : Int) +
        6 * (n : Int) * ((M : Int) + 3) -
        4 * (M : Int) * (n : Int) * ((n : Int) - 4)) +
    3 * ((M : Int) - 2) * (n : Int) *
      (6 * (Nat.choose (n - 1) 2 : Int) +
        6 * ((M - 1 : Nat) : Int))

/-- Geometric cap-sensitive master using Melchior only. -/
theorem capMelchiorMasterNumerator_le_geometricCircleCount
    {α : Type u} [Fintype α] [DecidableEq α]
    (Mel : Erdos506.Incidence.RealPlaneMelchiorPrinciple.{u})
    (cfg : Configuration α) (hadm : Admissible cfg)
    (hcard : 3 ≤ Fintype.card α) (M : Nat) (hM : 3 ≤ M)
    (hcap : BlockSizeCap (blockSystem cfg) M) :
    capMelchiorMasterNumerator (Fintype.card α) M ≤
      ((M : Int) + 2) * 36 * (M : Int) *
        Erdos506.V4.circleCount cfg := by
  have hP : 3 * (Fintype.card α : Int) ≤ rowP cfg :=
    three_n_le_rowP_of_realPlaneMelchior
      (α := α) Mel cfg hadm hcard
  have hD : rowD cfg ≤
      (Fintype.card α : Int) * ((Fintype.card α : Int) - 4) :=
    rowD_le_n_mul_n_sub_four_of_realPlaneMelchior
      (α := α) Mel cfg hadm hcard
  have hL := cap_add_two_mul_rowL_lower_of_realPlaneMelchior
    (α := α) Mel cfg hadm hcard M hM hcap
  unfold rowP at hP
  unfold rowD at hD
  unfold rowL at hL
  have hMplus : 0 ≤ (M : Int) + 2 := by positivity
  have hPcoeff : 0 ≤ ((M : Int) + 2) * (2 * ((M : Int) + 3)) := by
    positivity
  have hDcoeff : 0 ≤ ((M : Int) + 2) * (4 * (M : Int)) := by
    positivity
  have hLcoeff : 0 ≤ 3 * ((M : Int) - 2) := by omega
  have hP' := mul_le_mul_of_nonneg_left hP hPcoeff
  have hD' := mul_le_mul_of_nonneg_left hD hDcoeff
  have hL' := mul_le_mul_of_nonneg_left hL hLcoeff
  have hfun := largeMasterFunctional_le_circleCount
    (blockSystem cfg) M hcap
  rw [largeMasterFunctional_eq_rows] at hfun
  have hfun' := mul_le_mul_of_nonneg_left hfun hMplus
  rw [totalCircleCount_eq_card_determinedCircle,
    ← Erdos506.V3.circleCount_eq_card_determinedCircle] at hfun'
  unfold capMelchiorMasterNumerator
  nlinarith

/-- The cap-sensitive master is already strictly above one less than the
uniform target when `M = n / 2 - 1` and `n ≥ 23`. -/
theorem scaled_predUniformTarget_lt_capMelchiorMasterNumerator
    (n : Nat) (hn : 23 ≤ n) :
    ((((n / 2 - 1 : Nat) : Int) + 2) * 36 *
        ((n / 2 - 1 : Nat) : Int)) *
        ((Erdos506.v1UniformTarget n : Int) - 1) <
      capMelchiorMasterNumerator n (n / 2 - 1) := by
  rcases n.even_or_odd' with ⟨r, hnEven | hnOdd⟩
  · subst n
    have hr : 12 ≤ r := by omega
    have hdiv : 2 * r / 2 = r := by omega
    rw [hdiv, uniformTarget_even r (by omega)]
    unfold capMelchiorMasterNumerator
    rw [eighteen_choose_three_int (2 * r) (by omega),
      show 2 * r - 1 = 2 * (r - 1) + 1 by omega,
      choose_two_odd (r - 1)]
    push_cast [Nat.cast_sub (by omega : 1 ≤ 2 * r),
      Nat.cast_sub (by omega : 1 ≤ r),
      Nat.cast_sub (by omega : 1 ≤ r - 1)]
    have ht : (0 : Int) ≤ (r : Int) - 12 := by omega
    have hpoly :
        0 < (r : Int)^4 - 14 * (r : Int)^3 +
          26 * (r : Int)^2 - 4 * (r : Int) + 9 := by
      calc
        (r : Int)^4 - 14 * (r : Int)^3 +
              26 * (r : Int)^2 - 4 * (r : Int) + 9 =
            ((r : Int) - 12)^4 + 34 * ((r : Int) - 12)^3 +
              386 * ((r : Int) - 12)^2 +
              1484 * ((r : Int) - 12) + 249 := by ring
        _ > 0 := by positivity
    nlinarith
  · subst n
    have hr : 11 ≤ r := by omega
    have hdiv : (2 * r + 1) / 2 = r := by omega
    rw [hdiv, uniformTarget_odd r]
    unfold capMelchiorMasterNumerator
    rw [eighteen_choose_three_int (2 * r + 1) (by omega),
      show 2 * r + 1 - 1 = 2 * r by omega, choose_two_even r]
    push_cast [Nat.cast_sub (by omega : 1 ≤ 2 * r),
      Nat.cast_sub (by omega : 1 ≤ r),
      Nat.cast_sub (by omega : 1 ≤ r - 1)]
    have ht : (0 : Int) ≤ (r : Int) - 11 := by omega
    have hpoly :
        0 < 2 * (r : Int)^4 - 14 * (r : Int)^3 -
          11 * (r : Int)^2 + 32 * (r : Int) + 27 := by
      calc
        2 * (r : Int)^4 - 14 * (r : Int)^3 -
              11 * (r : Int)^2 + 32 * (r : Int) + 27 =
            2 * ((r : Int) - 11)^4 + 74 * ((r : Int) - 11)^3 +
              979 * ((r : Int) - 11)^2 +
              5356 * ((r : Int) - 11) + 9696 := by ring
        _ > 0 := by positivity
    nlinarith

/-- Langer-free V1 lower bound for the entire tail `n ≥ 23`. -/
theorem v1UniformTarget_le_circleCount_tail_without_langer
    {α : Type u} [Fintype α] [DecidableEq α]
    (Mel : Erdos506.Incidence.RealPlaneMelchiorPrinciple.{u})
    (cfg : Configuration α) (hadm : Admissible cfg)
    (hcard : 23 ≤ Fintype.card α) :
    Erdos506.v1UniformTarget (Fintype.card α) ≤
      Erdos506.V4.circleCount cfg := by
  by_contra hnot
  have hcount : Erdos506.V4.circleCount cfg <
      Erdos506.v1UniformTarget (Fintype.card α) := by omega
  have hcap := predHalfBlockCap_of_circleCount_lt_v1UniformTarget
    cfg hadm hcard hcount
  let n := Fintype.card α
  let M := n / 2 - 1
  have hM : 3 ≤ M := by
    dsimp only [M, n]
    omega
  have hmaster := capMelchiorMasterNumerator_le_geometricCircleCount
    Mel cfg hadm (by omega) M hM (by simpa [M, n] using hcap)
  have hgap := scaled_predUniformTarget_lt_capMelchiorMasterNumerator
    n (by simpa only [n] using hcard)
  have htargetPos : 1 ≤ Erdos506.v1UniformTarget n := by
    have hn : 23 ≤ n := by simpa only [n] using hcard
    rcases n.even_or_odd' with ⟨r, hrEven | hrOdd⟩
    · rw [hrEven, uniformTarget_even r (by omega)]
      omega
    · rw [hrOdd, uniformTarget_odd r]
      omega
  have hcountLeNat : Erdos506.V4.circleCount cfg ≤
      Erdos506.v1UniformTarget n - 1 := by
    dsimp only [n] at hcount ⊢
    omega
  have hcountLeCast : (Erdos506.V4.circleCount cfg : Int) ≤
      ((Erdos506.v1UniformTarget n - 1 : Nat) : Int) := by
    exact_mod_cast hcountLeNat
  have hcountLe : (Erdos506.V4.circleCount cfg : Int) ≤
      (Erdos506.v1UniformTarget n : Int) - 1 := by
    simpa only [Nat.cast_sub htargetPos, Nat.cast_one] using hcountLeCast
  have hcoeff : 0 ≤ (((M : Int) + 2) * 36 * (M : Int)) := by
    positivity
  have hscaledLe := mul_le_mul_of_nonneg_left hcountLe hcoeff
  dsimp only [M] at hgap hmaster hscaledLe
  dsimp only [n] at hmaster hscaledLe
  exact (not_lt_of_ge hscaledLe) (hgap.trans_le hmaster)

end Erdos506.V1
