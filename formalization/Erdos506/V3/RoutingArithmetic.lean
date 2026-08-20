import Erdos506.V3.Arithmetic

/-!
# Arithmetic routing for the V3 proof

This module turns the rational identities in `Arithmetic.lean` into the two
integer inequalities used to route a configuration according to the size of
its richest determined circle.
-/

namespace Erdos506.V3

theorem genericTargetQ_natCast (n : ℕ) (hn : 1 ≤ n) :
    genericTargetQ (n : ℚ) = (Erdos506.v3GenericTarget n : ℚ) := by
  rw [genericTargetQ, Erdos506.v3GenericTarget]
  norm_num only [Nat.cast_add, Nat.cast_one]
  have hcast : (n : ℚ) - 1 = ((n - 1 : ℕ) : ℚ) := by
    rw [Nat.cast_sub hn]
    norm_num
  rw [hcast, chooseTwoQ_natCast]

theorem v3GenericTarget_le_choose_three (n : ℕ) (hn : 4 ≤ n) :
    Erdos506.v3GenericTarget n ≤ Nat.choose n 3 := by
  rw [Erdos506.v3GenericTarget]
  have hpos : 1 ≤ Nat.choose (n - 1) 3 :=
    Nat.choose_pos (by omega)
  have hpascal := Nat.choose_succ_succ' (n - 1) 2
  have hnstep : n - 1 + 1 = n := Nat.sub_add_cancel (by omega)
  rw [hnstep] at hpascal
  norm_num at hpascal
  omega

theorem boundedSupportLower_antitone_nat
    (n a b : ℕ) (hn : 5 ≤ n) (ha : 4 ≤ a) (hab : a ≤ b) :
    boundedSupportLowerQ (n : ℚ) (b : ℚ) ≤
      boundedSupportLowerQ (n : ℚ) (a : ℚ) := by
  have hanti : AntitoneOn
      (fun q : ℕ => boundedSupportLowerQ (n : ℚ) (q : ℚ))
      {q : ℕ | 4 ≤ q} :=
    antitoneOn_nat_Ici_of_succ_le (k := 4) (fun q hq => by
      have hstep := boundedSupportLower_antitone (n : ℚ) (q : ℚ)
        (by exact_mod_cast hn) (by exact_mod_cast hq)
      simpa only [Nat.cast_add, Nat.cast_one] using hstep.le)
  exact hanti ha (ha.trans hab) hab

/-- At every bounded-support endpoint needed for `n ≥ 11`, the rational
functional lies strictly above the preceding integer.  This includes the
exceptional endpoint `(n,m)=(12,6)`, whose gap from the target is `-2/3`. -/
theorem genericTarget_sub_one_lt_boundedSupportLower
    (n m : ℕ) (hn : 11 ≤ n) (hm : 4 ≤ m) (hhalf : m ≤ n / 2) :
    (Erdos506.v3GenericTarget n : ℚ) - 1 <
      boundedSupportLowerQ (n : ℚ) (m : ℚ) := by
  rw [← genericTargetQ_natCast n (by omega)]
  rcases n.even_or_odd' with ⟨r, hnEven | hnOdd⟩
  · subst n
    have hr : 6 ≤ r := by omega
    have hmle : m ≤ r := by omega
    have hmono := boundedSupportLower_antitone_nat (2 * r) m r
      (by omega) hm hmle
    norm_num only [Nat.cast_mul, Nat.cast_ofNat] at hmono ⊢
    have hgap := boundedSupport_even_gap (r : ℚ) (by exact_mod_cast (show 4 ≤ r by omega))
    have hgapLower : (-1 : ℚ) <
        boundedSupportLowerQ (2 * (r : ℚ)) (r : ℚ) -
          genericTargetQ (2 * (r : ℚ)) := by
      rw [hgap]
      by_cases hr6 : r = 6
      · subst r
        norm_num
      · have hr7 : 7 ≤ r := by omega
        have hd : 0 ≤ (r : ℚ) - 7 := by
          rw [sub_nonneg]
          exact_mod_cast hr7
        have hpoly : 0 < 2 * (r : ℚ)^2 - 13 * (r : ℚ) + 2 := by
          calc
            2 * (r : ℚ)^2 - 13 * (r : ℚ) + 2 =
                2 * ((r : ℚ) - 7)^2 + 15 * ((r : ℚ) - 7) + 9 := by ring
            _ > 0 := by positivity
        have hr2 : 0 < (r : ℚ) - 2 := by
          rw [sub_pos]
          exact_mod_cast (show 2 < r by omega)
        have hden : 0 < 3 * ((r : ℚ) + 2) := by positivity
        have hpositive : 0 <
            ((r : ℚ) - 2) * (2 * (r : ℚ)^2 - 13 * (r : ℚ) + 2) /
              (3 * ((r : ℚ) + 2)) := by positivity
        linarith
    linarith
  · subst n
    have hr : 5 ≤ r := by omega
    have hmle : m ≤ r := by omega
    have hmono := boundedSupportLower_antitone_nat (2 * r + 1) m r
      (by omega) hm hmle
    norm_num only [Nat.cast_add, Nat.cast_mul, Nat.cast_one, Nat.cast_ofNat] at hmono ⊢
    have hgap := boundedSupport_odd_gap (r : ℚ) (by exact_mod_cast (show 4 ≤ r by omega))
    have hd : 0 ≤ (r : ℚ) - 5 := by
      rw [sub_nonneg]
      exact_mod_cast hr
    have hpoly : 0 < (r : ℚ)^3 - 4 * (r : ℚ)^2 - 4 * (r : ℚ) - 2 := by
      calc
        (r : ℚ)^3 - 4 * (r : ℚ)^2 - 4 * (r : ℚ) - 2 =
            ((r : ℚ) - 5)^3 + 11 * ((r : ℚ) - 5)^2 +
              31 * ((r : ℚ) - 5) + 3 := by ring
        _ > 0 := by positivity
    have hfirst : 0 < 2 * (r : ℚ) - 3 := by
      rw [sub_pos]
      exact_mod_cast (show 3 < 2 * r by omega)
    have hden : 0 < 3 * (r : ℚ) * ((r : ℚ) + 2) := by positivity
    have hgapPositive : 0 <
        boundedSupportLowerQ (2 * (r : ℚ) + 1) (r : ℚ) -
          genericTargetQ (2 * (r : ℚ) + 1) := by
      rw [hgap]
      positivity
    linarith

/-- The rich-circle pencil expression reaches the generic V3 target whenever
the chosen support contains more than half, but not all, of the labels. -/
theorem v3GenericTarget_le_pencilBound
    (n m : ℕ) (hn : 11 ≤ n) (hrich : n / 2 < m) (hproper : m < n) :
    Erdos506.v3GenericTarget n ≤ pencilBound n m := by
  let k := n - m
  have hmn : m ≤ n := hproper.le
  have hkpos : 1 ≤ k := by
    dsimp only [k]
    omega
  have hnmk : n = m + k := by
    dsimp only [k]
    omega
  have hkm : k < m := by omega
  have hNat :
      Erdos506.v3GenericTarget n + Nat.choose k 2 * (m / 2) ≤
        1 + k * Nat.choose m 2 := by
    rcases m.even_or_odd' with ⟨r, hmEven | hmOdd⟩
    · subst m
      have hr3 : 3 ≤ r := by omega
      have hkmax : k ≤ 2 * r - 1 := by omega
      have hgap := pencil_even_gap (k : ℚ) (r : ℚ)
      simp only [pencilEvenQ] at hgap
      have hbase : 0 ≤ ((2 * (r : ℚ) - 1) * ((r : ℚ) - 3)) := by
        apply mul_nonneg
        · have hrnon : (1 : ℚ) ≤ 2 * (r : ℚ) := by
            exact_mod_cast (show 1 ≤ 2 * r by omega)
          linarith
        · rw [sub_nonneg]
          exact_mod_cast hr3
      have hbracket : 0 ≤
          4 * (r : ℚ)^2 - 6 * (r : ℚ) + 2 - (k : ℚ) * ((r : ℚ) + 1) := by
        have hcast : ((2 * r - 1 : ℕ) : ℚ) = 2 * (r : ℚ) - 1 := by
          rw [Nat.cast_sub (show 1 ≤ 2 * r by omega)]
          norm_num
        have hkmaxQ : (k : ℚ) ≤ 2 * (r : ℚ) - 1 := by
          rw [← hcast]
          exact_mod_cast hkmax
        nlinarith
      have hkone : 0 ≤ (k : ℚ) - 1 := by
        rw [sub_nonneg]
        exact_mod_cast hkpos
      have hq :
          genericTargetQ (2 * (r : ℚ) + (k : ℚ)) +
              chooseTwoQ (k : ℚ) * (r : ℚ) ≤
            1 + (k : ℚ) * chooseTwoQ (2 * (r : ℚ)) := by
        nlinarith [mul_nonneg hkone hbracket]
      have hq' :
          (Erdos506.v3GenericTarget n : ℚ) +
              (Nat.choose k 2 : ℚ) * (r : ℚ) ≤
            1 + (k : ℚ) * (Nat.choose (2 * r) 2 : ℚ) := by
        rw [← genericTargetQ_natCast n (by omega),
          ← chooseTwoQ_natCast k, ← chooseTwoQ_natCast (2 * r)]
        rw [hnmk]
        norm_num only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
        exact hq
      have hnat' :
          Erdos506.v3GenericTarget n + Nat.choose k 2 * r ≤
            1 + k * Nat.choose (2 * r) 2 := by
        exact_mod_cast hq'
      simpa using hnat'
    · subst m
      have hr3 : 3 ≤ r := by omega
      have hkmax : k ≤ 2 * r := by omega
      have hgap := pencil_odd_gap (k : ℚ) (r : ℚ)
      simp only [pencilOddQ] at hgap
      have hbase : 0 ≤ 2 * (r : ℚ) * ((r : ℚ) - 2) := by
        apply mul_nonneg
        · positivity
        · rw [sub_nonneg]
          exact_mod_cast (show 2 ≤ r by omega)
      have hbracket : 0 ≤
          4 * (r : ℚ)^2 - 2 * (r : ℚ) - (k : ℚ) * ((r : ℚ) + 1) := by
        have hkmaxQ : (k : ℚ) ≤ 2 * (r : ℚ) := by exact_mod_cast hkmax
        nlinarith
      have hkone : 0 ≤ (k : ℚ) - 1 := by
        rw [sub_nonneg]
        exact_mod_cast hkpos
      have hq :
          genericTargetQ (2 * (r : ℚ) + 1 + (k : ℚ)) +
              chooseTwoQ (k : ℚ) * (r : ℚ) ≤
            1 + (k : ℚ) * chooseTwoQ (2 * (r : ℚ) + 1) := by
        nlinarith [mul_nonneg hkone hbracket]
      have hq' :
          (Erdos506.v3GenericTarget n : ℚ) +
              (Nat.choose k 2 : ℚ) * (r : ℚ) ≤
            1 + (k : ℚ) * (Nat.choose (2 * r + 1) 2 : ℚ) := by
        rw [← genericTargetQ_natCast n (by omega),
          ← chooseTwoQ_natCast k, ← chooseTwoQ_natCast (2 * r + 1)]
        rw [hnmk]
        norm_num only [Nat.cast_add, Nat.cast_mul, Nat.cast_one, Nat.cast_ofNat]
        exact hq
      have hnat' :
          Erdos506.v3GenericTarget n + Nat.choose k 2 * r ≤
            1 + k * Nat.choose (2 * r + 1) 2 := by
        exact_mod_cast hq'
      have hdiv : (2 * r + 1) / 2 = r := by omega
      simpa [hdiv] using hnat'
  unfold pencilBound
  rw [show n - m = k by rfl]
  exact Nat.le_sub_of_add_le hNat

end Erdos506.V3
