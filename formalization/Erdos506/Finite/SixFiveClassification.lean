import Erdos506.Finite.SixFiveBV
import Erdos506.Finite.BitVecCounts

/-!
# Structural classification of the six-by-five design

The proof reduces the `60`-bit incidence matrix to arithmetic count identities,
the block/complement relation, and finite checks on individual `6`-bit rows.
All closed computations are reduced by Lean's kernel.
-/

open scoped BigOperators

namespace Erdos506.Finite

private def probeNatCount10 (p : Fin 10 → Bool) : Nat :=
  (p 0).toNat + (p 1).toNat + (p 2).toNat + (p 3).toNat +
  (p 4).toNat + (p 5).toNat + (p 6).toNat + (p 7).toNat +
  (p 8).toNat + (p 9).toNat

private def probeBVCount10 (p : Fin 10 → Bool) : BitVec 4 :=
  sixFiveBVBit4 (p 0) + sixFiveBVBit4 (p 1) +
  sixFiveBVBit4 (p 2) + sixFiveBVBit4 (p 3) +
  sixFiveBVBit4 (p 4) + sixFiveBVBit4 (p 5) +
  sixFiveBVBit4 (p 6) + sixFiveBVBit4 (p 7) +
  sixFiveBVBit4 (p 8) + sixFiveBVBit4 (p 9)

private theorem probeBVCount10_toNat (p : Fin 10 → Bool) :
    (probeBVCount10 p).toNat = probeNatCount10 p := by
  have h0 := Bool.toNat_le (p 0)
  have h1 := Bool.toNat_le (p 1)
  have h2 := Bool.toNat_le (p 2)
  have h3 := Bool.toNat_le (p 3)
  have h4 := Bool.toNat_le (p 4)
  have h5 := Bool.toNat_le (p 5)
  have h6 := Bool.toNat_le (p 6)
  have h7 := Bool.toNat_le (p 7)
  have h8 := Bool.toNat_le (p 8)
  have h9 := Bool.toNat_le (p 9)
  simp only [probeBVCount10, probeNatCount10, sixFiveBVBit4,
    BitVec.toNat_add, BitVec.toNat_setWidth, BitVec.toNat_ofBool]
  omega

private theorem probeRowWeightNat (r : BitVec 6) (h : r.cpop = 3) :
    (r.getLsb 0).toNat + ((r.getLsb 1).toNat +
      ((r.getLsb 2).toNat + ((r.getLsb 3).toNat +
      ((r.getLsb 4).toNat + ((r.getLsb 5).toNat + 0))))) = 3 := by
  have hn := congrArg BitVec.toNat h
  rw [toNat_cpop_eq_sum_getLsb] at hn
  norm_num only [Fin.sum_univ_succ, BitVec.toNat_ofNat] at hn
  simpa [Fin.succ] using hn

private def probeComplementIndicator
    (x0 x1 x2 y0 y1 y2 : Bool) : Bool :=
  (x0 && x1 && x2) || (y0 && y1 && y2)

private theorem probeComplementIdentity
    (x0 x1 x2 y0 y1 y2 : Bool)
    (hweight : x0.toNat + x1.toNat + x2.toNat +
      y0.toNat + y1.toNat + y2.toNat = 3) :
    (probeComplementIndicator x0 x1 x2 y0 y1 y2).toNat +
        x0.toNat + x1.toNat + x2.toNat =
      1 + (x0 && x1).toNat + (x0 && x2).toNat +
        (x1 && x2).toNat := by
  cases x0 <;> cases x1 <;> cases x2 <;>
    cases y0 <;> cases y1 <;> cases y2 <;>
    simp_all [probeComplementIndicator]

private theorem probeComplementCountCore
    (x0 x1 x2 y0 y1 y2 : Fin 10 → Bool)
    (hweight : ∀ i,
      (x0 i).toNat + ((x1 i).toNat + ((x2 i).toNat +
      ((y0 i).toNat + ((y1 i).toNat + ((y2 i).toNat + 0))))) = 3)
    (hx0 : probeNatCount10 x0 = 5)
    (hx1 : probeNatCount10 x1 = 5)
    (hx2 : probeNatCount10 x2 = 5)
    (hx01 : probeNatCount10 (fun i => x0 i && x1 i) = 2)
    (hx02 : probeNatCount10 (fun i => x0 i && x2 i) = 2)
    (hx12 : probeNatCount10 (fun i => x1 i && x2 i) = 2) :
    probeNatCount10 (fun i =>
      probeComplementIndicator (x0 i) (x1 i) (x2 i)
        (y0 i) (y1 i) (y2 i)) = 1 := by
  have hlocal (i : Fin 10) := probeComplementIdentity
    (x0 i) (x1 i) (x2 i) (y0 i) (y1 i) (y2 i) (by
      have hi := hweight i
      omega)
  have h0 := hlocal 0
  have h1 := hlocal 1
  have h2 := hlocal 2
  have h3 := hlocal 3
  have h4 := hlocal 4
  have h5 := hlocal 5
  have h6 := hlocal 6
  have h7 := hlocal 7
  have h8 := hlocal 8
  have h9 := hlocal 9
  have hsum :
      probeNatCount10 (fun i =>
        probeComplementIndicator (x0 i) (x1 i) (x2 i)
          (y0 i) (y1 i) (y2 i)) +
        probeNatCount10 x0 + probeNatCount10 x1 + probeNatCount10 x2 =
      10 + probeNatCount10 (fun i => x0 i && x1 i) +
        probeNatCount10 (fun i => x0 i && x2 i) +
        probeNatCount10 (fun i => x1 i && x2 i) := by
    simp only [probeNatCount10]
    omega
  clear hweight hlocal h0 h1 h2 h3 h4 h5 h6 h7 h8 h9
  omega

private theorem probeNormalizedRow1Cases :
    ∀ r : BitVec 6, r.cpop = 3 → r &&& 3 = 3 → r ≠ 7 →
      r = 11 ∨ r = 19 ∨ r = 35 := by
  decide_cbv

private theorem probeNormalizedRow2Cases :
    ∀ r : BitVec 6, r.cpop = 3 → r &&& 5 = 5 → r ≠ 7 →
      r = 13 ∨ r = 21 ∨ r = 37 := by
  decide_cbv

private theorem probeNormalizedRow3Cases :
    ∀ r : BitVec 6, r.cpop = 3 → r &&& 6 = 6 → r ≠ 7 →
      r = 14 ∨ r = 22 ∨ r = 38 := by
  decide_cbv

private theorem probeNatCount10_unique (p : Fin 10 → Bool)
    (hcount : probeNatCount10 p = 1) {i k : Fin 10}
    (hi : p i = true) (hk : p k = true) : i = k := by
  classical
  by_contra hne
  have hcount' : (∑ q : Fin 10, (p q).toNat) = 1 := by
    simpa [probeNatCount10, Fin.sum_univ_succ, add_assoc] using hcount
  have hle :
      (∑ q ∈ ({i, k} : Finset (Fin 10)), (p q).toNat) ≤
        ∑ q : Fin 10, (p q).toNat := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · simp
    · intro q hq hnot
      omega
  simp [hne, hi, hk] at hle
  omega

private def probeRowBit (M : BitVec 60) (j : Fin 6) (i : Fin 10) : Bool :=
  (sixFiveBVRow M i).getLsb j

private def probePairBit (r : BitVec 6) (j k : Fin 6) : Bool :=
  r.getLsb j && r.getLsb k

private theorem probeColumnCountNat (M : BitVec 60) (j : Fin 6)
    (h : sixFiveBVColumnCount M j = 5#4) :
    probeNatCount10 (probeRowBit M j) = 5 := by
  have hn := congrArg BitVec.toNat h
  change (probeBVCount10 (probeRowBit M j)).toNat = (5#4).toNat at hn
  rw [probeBVCount10_toNat] at hn
  norm_num at hn
  exact hn

private theorem probePairCountNat (M : BitVec 60) (j k : Fin 6)
    (h : sixFiveBVPairColumnCount M j k = 2#4) :
    probeNatCount10 (fun i => probePairBit (sixFiveBVRow M i) j k) = 2 := by
  have hn := congrArg BitVec.toNat h
  change
    (probeBVCount10 (fun i => probePairBit (sixFiveBVRow M i) j k)).toNat =
      (2#4).toNat at hn
  rw [probeBVCount10_toNat] at hn
  norm_num at hn
  exact hn

private def probeKnownPairNat (r0 r1 r2 r3 : BitVec 6) (j k : Fin 6) : Nat :=
  (probePairBit r0 j k).toNat + (probePairBit r1 j k).toNat +
    (probePairBit r2 j k).toNat + (probePairBit r3 j k).toNat

private def probeAdmissible (r0 r1 r2 r3 r : BitVec 6) : Prop :=
  r.cpop = 3 ∧
  (∀ j k : Fin 6, j ≠ k → probeKnownPairNat r0 r1 r2 r3 j k = 2 →
    probePairBit r j k = true → r = r0 ∨ r = r1 ∨ r = r2 ∨ r = r3) ∧
  r ≠ ~~~r0 ∧ r ≠ ~~~r1 ∧ r ≠ ~~~r2 ∧ r ≠ ~~~r3

private theorem probeComplementCountFor (M : BitVec 60)
    (a b c d e f : Fin 6)
    (hweight : ∀ i,
      (probeRowBit M a i).toNat + ((probeRowBit M b i).toNat +
      ((probeRowBit M c i).toNat + ((probeRowBit M d i).toNat +
      ((probeRowBit M e i).toNat + ((probeRowBit M f i).toNat + 0))))) = 3)
    (hcol : ∀ j, probeNatCount10 (probeRowBit M j) = 5)
    (hpair : ∀ j k, j ≠ k →
      probeNatCount10 (fun i => probePairBit (sixFiveBVRow M i) j k) = 2)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    probeNatCount10 (fun i => probeComplementIndicator
      (probeRowBit M a i) (probeRowBit M b i) (probeRowBit M c i)
      (probeRowBit M d i) (probeRowBit M e i) (probeRowBit M f i)) = 1 := by
  apply probeComplementCountCore
  · exact hweight
  · exact hcol a
  · exact hcol b
  · exact hcol c
  · simpa only [probeRowBit, probePairBit] using hpair a b hab
  · simpa only [probeRowBit, probePairBit] using hpair a c hac
  · simpa only [probeRowBit, probePairBit] using hpair b c hbc

private theorem probeNoOtherValue
    (rows : Fin 10 → BitVec 6) (p : Fin 10 → Bool)
    (hcount : probeNatCount10 p = 1) {s : Fin 10}
    (hs : p s = true) (source target : BitVec 6)
    (hsource : rows s = source) (hne : source ≠ target)
    (hmark : ∀ i, rows i = target → p i = true) :
    ∀ i, rows i ≠ target := by
  intro i hi
  have hpi := hmark i hi
  have his := probeNatCount10_unique p hcount hs hpi
  subst i
  exact hne (hsource.symm.trans hi)

private theorem probeNatCount10_tail_false (p : Fin 10 → Bool)
    (hglobal : probeNatCount10 p = 2)
    (hfirst : (p 0).toNat + (p 1).toNat + (p 2).toNat + (p 3).toNat = 2) :
    p 4 = false ∧ p 5 = false ∧ p 6 = false ∧
      p 7 = false ∧ p 8 = false ∧ p 9 = false := by
  simp only [probeNatCount10] at hglobal
  refine ⟨Bool.toNat_eq_zero.mp ?_, Bool.toNat_eq_zero.mp ?_,
    Bool.toNat_eq_zero.mp ?_, Bool.toNat_eq_zero.mp ?_,
    Bool.toNat_eq_zero.mp ?_, Bool.toNat_eq_zero.mp ?_⟩ <;> omega

private theorem probeRowsAdmissible (M : BitVec 60)
    (hrow : ∀ i, (sixFiveBVRow M i).cpop = 3)
    (hpair : ∀ j k, j ≠ k →
      probeNatCount10 (fun i => probePairBit (sixFiveBVRow M i) j k) = 2)
    (hno0 : ∀ i, sixFiveBVRow M i ≠ ~~~(sixFiveBVRow M 0))
    (hno1 : ∀ i, sixFiveBVRow M i ≠ ~~~(sixFiveBVRow M 1))
    (hno2 : ∀ i, sixFiveBVRow M i ≠ ~~~(sixFiveBVRow M 2))
    (hno3 : ∀ i, sixFiveBVRow M i ≠ ~~~(sixFiveBVRow M 3)) :
    ∀ i, probeAdmissible (sixFiveBVRow M 0) (sixFiveBVRow M 1)
      (sixFiveBVRow M 2) (sixFiveBVRow M 3) (sixFiveBVRow M i) := by
  intro i
  refine ⟨hrow i, ?_, hno0 i, hno1 i, hno2 i, hno3 i⟩
  intro j k hjk hknown hri
  have hglobal := hpair j k hjk
  let p : Fin 10 → Bool := fun q => probePairBit (sixFiveBVRow M q) j k
  have hfirst : (p 0).toNat + (p 1).toNat + (p 2).toNat + (p 3).toNat = 2 := by
    simpa only [p, probeKnownPairNat] using hknown
  have htail := probeNatCount10_tail_false p (by simpa only [p] using hglobal) hfirst
  rcases htail with ⟨hp4, hp5, hp6, hp7, hp8, hp9⟩
  fin_cases i
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr (Or.inl rfl))
  · exact Or.inr (Or.inr (Or.inr rfl))
  · exfalso
    exact Bool.false_ne_true (hp4.symm.trans (by simpa only [p] using hri))
  · exfalso
    exact Bool.false_ne_true (hp5.symm.trans (by simpa only [p] using hri))
  · exfalso
    exact Bool.false_ne_true (hp6.symm.trans (by simpa only [p] using hri))
  · exfalso
    exact Bool.false_ne_true (hp7.symm.trans (by simpa only [p] using hri))
  · exfalso
    exact Bool.false_ne_true (hp8.symm.trans (by simpa only [p] using hri))
  · exfalso
    exact Bool.false_ne_true (hp9.symm.trans (by simpa only [p] using hri))

private instance probeAdmissibleDecidable (r0 r1 r2 r3 r : BitVec 6) :
    Decidable (probeAdmissible r0 r1 r2 r3 r) := by
  unfold probeAdmissible
  infer_instance

private instance probeInSet0Decidable (r : BitVec 6) :
    Decidable (sixFiveBVInSet0 r) := by
  unfold sixFiveBVInSet0
  infer_instance

private instance probeInSet1Decidable (r : BitVec 6) :
    Decidable (sixFiveBVInSet1 r) := by
  unfold sixFiveBVInSet1
  infer_instance

private instance probeInSet2Decidable (r : BitVec 6) :
    Decidable (sixFiveBVInSet2 r) := by
  unfold sixFiveBVInSet2
  infer_instance

private instance probeInSet3Decidable (r : BitVec 6) :
    Decidable (sixFiveBVInSet3 r) := by
  unfold sixFiveBVInSet3
  infer_instance

private instance probeInSet4Decidable (r : BitVec 6) :
    Decidable (sixFiveBVInSet4 r) := by
  unfold sixFiveBVInSet4
  infer_instance

private instance probeInSet5Decidable (r : BitVec 6) :
    Decidable (sixFiveBVInSet5 r) := by
  unfold sixFiveBVInSet5
  infer_instance

private def probeAdmissibleFinset (r0 r1 r2 r3 : BitVec 6) : Finset (BitVec 6) :=
  Finset.univ.filter (probeAdmissible r0 r1 r2 r3)

private theorem probeAdmissible_card_ge_ten
    (rows : Fin 10 → BitVec 6) (hinj : Function.Injective rows)
    (r0 r1 r2 r3 : BitVec 6)
    (hadm : ∀ i, probeAdmissible r0 r1 r2 r3 (rows i)) :
    10 ≤ (probeAdmissibleFinset r0 r1 r2 r3).card := by
  classical
  have hsubset : Finset.univ.image rows ⊆ probeAdmissibleFinset r0 r1 r2 r3 := by
    intro r hr
    rcases Finset.mem_image.mp hr with ⟨i, hi, rfl⟩
    simp [probeAdmissibleFinset, hadm i]
  have hcard : (Finset.univ.image rows).card = 10 := by
    rw [Finset.card_image_of_injective _ hinj]
    simp
  rw [← hcard]
  exact Finset.card_le_card hsubset

private theorem probeAdmissibleInSet0 :
    ∀ r : BitVec 6, probeAdmissible 7 11 21 38 r → sixFiveBVInSet0 r := by
  intro r
  rcases r with ⟨r⟩
  fin_cases r <;> decide +kernel

private theorem probeAdmissibleInSet1 :
    ∀ r : BitVec 6, probeAdmissible 7 11 37 22 r → sixFiveBVInSet1 r := by
  intro r
  rcases r with ⟨r⟩
  fin_cases r <;> decide +kernel

private theorem probeAdmissibleInSet2 :
    ∀ r : BitVec 6, probeAdmissible 7 19 13 38 r → sixFiveBVInSet2 r := by
  intro r
  rcases r with ⟨r⟩
  fin_cases r <;> decide +kernel

private theorem probeAdmissibleInSet3 :
    ∀ r : BitVec 6, probeAdmissible 7 19 37 14 r → sixFiveBVInSet3 r := by
  intro r
  rcases r with ⟨r⟩
  fin_cases r <;> decide +kernel

private theorem probeAdmissibleInSet4 :
    ∀ r : BitVec 6, probeAdmissible 7 35 13 22 r → sixFiveBVInSet4 r := by
  intro r
  rcases r with ⟨r⟩
  fin_cases r <;> decide +kernel

private theorem probeAdmissibleInSet5 :
    ∀ r : BitVec 6, probeAdmissible 7 35 21 14 r → sixFiveBVInSet5 r := by
  intro r
  rcases r with ⟨r⟩
  fin_cases r <;> decide +kernel

private theorem probeLargeAdmissibleCases :
    ∀ r1 r2 r3 : BitVec 6,
      (r1 = 11 ∨ r1 = 19 ∨ r1 = 35) →
      (r2 = 13 ∨ r2 = 21 ∨ r2 = 37) →
      (r3 = 14 ∨ r3 = 22 ∨ r3 = 38) →
      10 ≤ (probeAdmissibleFinset 7 r1 r2 r3).card →
      (r1 = 11 ∧ r2 = 21 ∧ r3 = 38) ∨
      (r1 = 11 ∧ r2 = 37 ∧ r3 = 22) ∨
      (r1 = 19 ∧ r2 = 13 ∧ r3 = 38) ∨
      (r1 = 19 ∧ r2 = 37 ∧ r3 = 14) ∨
      (r1 = 35 ∧ r2 = 13 ∧ r3 = 22) ∨
      (r1 = 35 ∧ r2 = 21 ∧ r3 = 14) := by
  intro r1 r2 r3 h1 h2 h3
  rcases h1 with h1 | h1 | h1 <;> subst r1
  all_goals rcases h2 with h2 | h2 | h2 <;> subst r2
  all_goals rcases h3 with h3 | h3 | h3 <;> subst r3
  all_goals decide +kernel

private theorem probeNoComplementKnown (M : BitVec 60)
    (a b c d e f : Fin 6) (s : Fin 10) (source target : BitVec 6)
    (hweight : ∀ i,
      (probeRowBit M a i).toNat + ((probeRowBit M b i).toNat +
      ((probeRowBit M c i).toNat + ((probeRowBit M d i).toNat +
      ((probeRowBit M e i).toNat + ((probeRowBit M f i).toNat + 0))))) = 3)
    (hcol : ∀ j, probeNatCount10 (probeRowBit M j) = 5)
    (hpair : ∀ j k, j ≠ k →
      probeNatCount10 (fun i => probePairBit (sixFiveBVRow M i) j k) = 2)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hsource : sixFiveBVRow M s = source)
    (hs : probeComplementIndicator
      (source.getLsb a) (source.getLsb b) (source.getLsb c)
      (source.getLsb d) (source.getLsb e) (source.getLsb f) = true)
    (ht : probeComplementIndicator
      (target.getLsb a) (target.getLsb b) (target.getLsb c)
      (target.getLsb d) (target.getLsb e) (target.getLsb f) = true)
    (hne : source ≠ target) :
    ∀ i, sixFiveBVRow M i ≠ target := by
  let p : Fin 10 → Bool := fun i => probeComplementIndicator
    (probeRowBit M a i) (probeRowBit M b i) (probeRowBit M c i)
    (probeRowBit M d i) (probeRowBit M e i) (probeRowBit M f i)
  have hcount : probeNatCount10 p = 1 := by
    apply probeComplementCountFor M a b c d e f hweight hcol hpair hab hac hbc
  apply probeNoOtherValue (fun i => sixFiveBVRow M i) p hcount (s := s)
    (source := source) (target := target)
  · simpa only [p, probeRowBit, hsource] using hs
  · exact hsource
  · exact hne
  · intro i hi
    simpa only [p, probeRowBit, hi] using ht

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem sixFiveBV_classification (M : BitVec 60)
    (hvalid : sixFiveBVValid M) (hnorm : sixFiveBVNormalized M) :
    sixFiveBVClassified M := by
  rcases hvalid with ⟨hrow, hcolBV, hpairBV, hdistinct⟩
  rcases hnorm with ⟨h0, hmask1, hmask2, hmask3⟩
  have hcolNat : ∀ j, probeNatCount10 (probeRowBit M j) = 5 := by
    intro j
    exact probeColumnCountNat M j (hcolBV j)
  have hpairNat : ∀ j k, j ≠ k →
      probeNatCount10 (fun i => probePairBit (sixFiveBVRow M i) j k) = 2 := by
    intro j k hjk
    exact probePairCountNat M j k (hpairBV j k hjk)
  have selectedWeight (a b c d e f : Fin 6)
      (hperm : ∀ r : BitVec 6,
        (r.getLsb a).toNat + ((r.getLsb b).toNat +
        ((r.getLsb c).toNat + ((r.getLsb d).toNat +
        ((r.getLsb e).toNat + ((r.getLsb f).toNat + 0))))) =
        (r.getLsb 0).toNat + ((r.getLsb 1).toNat +
        ((r.getLsb 2).toNat + ((r.getLsb 3).toNat +
        ((r.getLsb 4).toNat + ((r.getLsb 5).toNat + 0)))))) :
      ∀ i,
        (probeRowBit M a i).toNat + ((probeRowBit M b i).toNat +
        ((probeRowBit M c i).toNat + ((probeRowBit M d i).toNat +
        ((probeRowBit M e i).toNat + ((probeRowBit M f i).toNat + 0))))) = 3 := by
    intro i
    have hw := probeRowWeightNat (sixFiveBVRow M i) (hrow i)
    have hp := hperm (sixFiveBVRow M i)
    simp only [probeRowBit]
    omega

  have hne1 : sixFiveBVRow M 1 ≠ 7 := by
    intro h
    apply hdistinct 1 0 (by decide)
    exact h.trans h0.symm
  have hne2 : sixFiveBVRow M 2 ≠ 7 := by
    intro h
    apply hdistinct 2 0 (by decide)
    exact h.trans h0.symm
  have hne3 : sixFiveBVRow M 3 ≠ 7 := by
    intro h
    apply hdistinct 3 0 (by decide)
    exact h.trans h0.symm
  have hcases1 := probeNormalizedRow1Cases (sixFiveBVRow M 1)
    (hrow 1) hmask1 hne1
  have hcases2 := probeNormalizedRow2Cases (sixFiveBVRow M 2)
    (hrow 2) hmask2 hne2
  have hcases3 := probeNormalizedRow3Cases (sixFiveBVRow M 3)
    (hrow 3) hmask3 hne3

  have hno0 : ∀ i, sixFiveBVRow M i ≠ ~~~(sixFiveBVRow M 0) := by
    have hw := selectedWeight 0 1 2 3 4 5 (by intro r; rfl)
    have hn := probeNoComplementKnown M 0 1 2 3 4 5 0 7 56
      hw hcolNat hpairNat (by decide) (by decide) (by decide) h0
      (by decide +kernel) (by decide +kernel) (by decide)
    intro i
    simpa [h0] using hn i
  have hno1 : ∀ i, sixFiveBVRow M i ≠ ~~~(sixFiveBVRow M 1) := by
    rcases hcases1 with h11 | h19 | h35
    · have hw := selectedWeight 0 1 3 2 4 5 (by intro r; omega)
      have hn := probeNoComplementKnown M 0 1 3 2 4 5 1 11 52
        hw hcolNat hpairNat (by decide) (by decide) (by decide) h11
        (by decide +kernel) (by decide +kernel) (by decide)
      intro i
      simpa [h11] using hn i
    · have hw := selectedWeight 0 1 4 2 3 5 (by intro r; omega)
      have hn := probeNoComplementKnown M 0 1 4 2 3 5 1 19 44
        hw hcolNat hpairNat (by decide) (by decide) (by decide) h19
        (by decide +kernel) (by decide +kernel) (by decide)
      intro i
      simpa [h19] using hn i
    · have hw := selectedWeight 0 1 5 2 3 4 (by intro r; omega)
      have hn := probeNoComplementKnown M 0 1 5 2 3 4 1 35 28
        hw hcolNat hpairNat (by decide) (by decide) (by decide) h35
        (by decide +kernel) (by decide +kernel) (by decide)
      intro i
      simpa [h35] using hn i
  have hno2 : ∀ i, sixFiveBVRow M i ≠ ~~~(sixFiveBVRow M 2) := by
    rcases hcases2 with h13 | h21 | h37
    · have hw := selectedWeight 0 2 3 1 4 5 (by intro r; omega)
      have hn := probeNoComplementKnown M 0 2 3 1 4 5 2 13 50
        hw hcolNat hpairNat (by decide) (by decide) (by decide) h13
        (by decide +kernel) (by decide +kernel) (by decide)
      intro i
      simpa [h13] using hn i
    · have hw := selectedWeight 0 2 4 1 3 5 (by intro r; omega)
      have hn := probeNoComplementKnown M 0 2 4 1 3 5 2 21 42
        hw hcolNat hpairNat (by decide) (by decide) (by decide) h21
        (by decide +kernel) (by decide +kernel) (by decide)
      intro i
      simpa [h21] using hn i
    · have hw := selectedWeight 0 2 5 1 3 4 (by intro r; omega)
      have hn := probeNoComplementKnown M 0 2 5 1 3 4 2 37 26
        hw hcolNat hpairNat (by decide) (by decide) (by decide) h37
        (by decide +kernel) (by decide +kernel) (by decide)
      intro i
      simpa [h37] using hn i
  have hno3 : ∀ i, sixFiveBVRow M i ≠ ~~~(sixFiveBVRow M 3) := by
    rcases hcases3 with h14 | h22 | h38
    · have hw := selectedWeight 1 2 3 0 4 5 (by intro r; omega)
      have hn := probeNoComplementKnown M 1 2 3 0 4 5 3 14 49
        hw hcolNat hpairNat (by decide) (by decide) (by decide) h14
        (by decide +kernel) (by decide +kernel) (by decide)
      intro i
      simpa [h14] using hn i
    · have hw := selectedWeight 1 2 4 0 3 5 (by intro r; omega)
      have hn := probeNoComplementKnown M 1 2 4 0 3 5 3 22 41
        hw hcolNat hpairNat (by decide) (by decide) (by decide) h22
        (by decide +kernel) (by decide +kernel) (by decide)
      intro i
      simpa [h22] using hn i
    · have hw := selectedWeight 1 2 5 0 3 4 (by intro r; omega)
      have hn := probeNoComplementKnown M 1 2 5 0 3 4 3 38 25
        hw hcolNat hpairNat (by decide) (by decide) (by decide) h38
        (by decide +kernel) (by decide +kernel) (by decide)
      intro i
      simpa [h38] using hn i

  have hadm := probeRowsAdmissible M hrow hpairNat hno0 hno1 hno2 hno3
  have hinj : Function.Injective (sixFiveBVRow M) := by
    intro i k hik
    by_contra hne
    exact hdistinct i k hne hik
  have hcard := probeAdmissible_card_ge_ten (sixFiveBVRow M) hinj
    (sixFiveBVRow M 0) (sixFiveBVRow M 1) (sixFiveBVRow M 2)
    (sixFiveBVRow M 3) hadm
  have hcard7 : 10 ≤ (probeAdmissibleFinset 7 (sixFiveBVRow M 1)
      (sixFiveBVRow M 2) (sixFiveBVRow M 3)).card := by
    simpa [h0] using hcard
  have hfinal := probeLargeAdmissibleCases
    (sixFiveBVRow M 1) (sixFiveBVRow M 2) (sixFiveBVRow M 3)
    hcases1 hcases2 hcases3 hcard7
  unfold sixFiveBVClassified
  rcases hfinal with hfinal | hfinal | hfinal | hfinal | hfinal | hfinal
  · rcases hfinal with ⟨h1, h2, h3⟩
    left
    intro i
    apply probeAdmissibleInSet0
    simpa [h0, h1, h2, h3] using hadm i
  · rcases hfinal with ⟨h1, h2, h3⟩
    right; left
    intro i
    apply probeAdmissibleInSet1
    simpa [h0, h1, h2, h3] using hadm i
  · rcases hfinal with ⟨h1, h2, h3⟩
    right; right; left
    intro i
    apply probeAdmissibleInSet2
    simpa [h0, h1, h2, h3] using hadm i
  · rcases hfinal with ⟨h1, h2, h3⟩
    right; right; right; left
    intro i
    apply probeAdmissibleInSet3
    simpa [h0, h1, h2, h3] using hadm i
  · rcases hfinal with ⟨h1, h2, h3⟩
    right; right; right; right; left
    intro i
    apply probeAdmissibleInSet4
    simpa [h0, h1, h2, h3] using hadm i
  · rcases hfinal with ⟨h1, h2, h3⟩
    right; right; right; right; right
    intro i
    apply probeAdmissibleInSet5
    simpa [h0, h1, h2, h3] using hadm i

end Erdos506.Finite
