import Mathlib

/-!
# Kernel-checked population counts for finite-set incidence vectors

These lemmas replace native enumeration in the Fano and six-by-five encodings.
They identify the population count of a little-endian membership vector with
the cardinality of the represented finite set.  The proofs use ordinary
recursion and big-operator identities only.
-/

open scoped BigOperators

namespace Erdos506.Finite

theorem cpopNatRec_eq_add_sum_range {w n acc : Nat} (x : BitVec w) :
    x.cpopNatRec n acc = acc + ∑ i ∈ Finset.range n, (x.getLsbD i).toNat := by
  induction n generalizing acc with
  | zero => simp
  | succ n ih =>
      rw [BitVec.cpopNatRec_succ, ih, Finset.sum_range_succ]
      omega

theorem toNat_cpop_eq_sum_getLsb {n : Nat} (x : BitVec n) :
    x.cpop.toNat = ∑ i, (x.getLsb i).toNat := by
  rw [BitVec.toNat_cpop, cpopNatRec_eq_add_sum_range]
  simp only [zero_add]
  rw [← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro i hi
  simp

theorem toNat_cpop_ofFnLE {n : Nat} (f : Fin n → Bool) :
    (BitVec.ofFnLE f).cpop.toNat = ∑ i, (f i).toNat := by
  rw [BitVec.toNat_cpop, cpopNatRec_eq_add_sum_range]
  simp only [zero_add]
  rw [← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro i hi
  simp

theorem toNat_cpop_membership {n : Nat} (S : Finset (Fin n)) :
    (BitVec.ofFnLE fun i : Fin n => decide (i ∈ S)).cpop.toNat = S.card := by
  rw [toNat_cpop_ofFnLE]
  classical
  calc
    (∑ i, (decide (i ∈ S)).toNat) = ∑ i, if i ∈ S then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro i hi
      by_cases h : i ∈ S <;> simp [h]
    _ = S.card := by simp

theorem cpop_membership {n : Nat} (S : Finset (Fin n)) :
    (BitVec.ofFnLE fun i : Fin n => decide (i ∈ S)).cpop =
      BitVec.ofNat n S.card := by
  apply BitVec.eq_of_toNat_eq
  rw [toNat_cpop_membership, BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
  exact lt_of_le_of_lt (Finset.card_le_univ S)
    (by simpa using (Nat.lt_two_pow_self : n < 2 ^ n))

end Erdos506.Finite
