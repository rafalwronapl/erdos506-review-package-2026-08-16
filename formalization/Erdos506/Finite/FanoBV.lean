import Mathlib

/-!
# Checked finite completion of a normalized STS(7)

A `49`-bit matrix stores seven triple columns.  The validity conditions say
that every column has three points and every pair of points occurs in exactly
one column.  Four columns and one defining pair in each remaining column fix
the labels.  The proof below excludes repeated pairs one at a time and then
reconstructs the three remaining columns.  All finite calculations use
ordinary kernel reduction; no native-reflection axiom is involved.
-/

namespace Erdos506.Finite

def fanoBVColumn (M : BitVec 49) (j : Fin 7) : BitVec 7 :=
  BitVec.extractLsb' (7 * j.val) 7 M

def fanoBVBit3 (b : Bool) : BitVec 3 :=
  (BitVec.ofBool b).zeroExtend 3

def fanoBVPairBit (M : BitVec 49) (j i k : Fin 7) : Bool :=
  (fanoBVColumn M j).getLsb i && (fanoBVColumn M j).getLsb k

def fanoBVPairCount (M : BitVec 49) (i k : Fin 7) : BitVec 3 :=
  fanoBVBit3 (fanoBVPairBit M 0 i k) +
  fanoBVBit3 (fanoBVPairBit M 1 i k) +
  fanoBVBit3 (fanoBVPairBit M 2 i k) +
  fanoBVBit3 (fanoBVPairBit M 3 i k) +
  fanoBVBit3 (fanoBVPairBit M 4 i k) +
  fanoBVBit3 (fanoBVPairBit M 5 i k) +
  fanoBVBit3 (fanoBVPairBit M 6 i k)

def fanoBVValid (M : BitVec 49) : Prop :=
  (∀ j : Fin 7, (fanoBVColumn M j).cpop = 3) ∧
  ∀ i k : Fin 7, i ≠ k → fanoBVPairCount M i k = 1#3

def fanoBVNormalized (M : BitVec 49) : Prop :=
  fanoBVColumn M 0 = 7 ∧
  fanoBVColumn M 2 = 97 ∧
  fanoBVColumn M 4 = 82 ∧
  fanoBVColumn M 5 = 76 ∧
  fanoBVColumn M 1 &&& 17 = 17 ∧
  fanoBVColumn M 3 &&& 34 = 34 ∧
  fanoBVColumn M 6 &&& 36 = 36

def fanoBVCanonical (M : BitVec 49) : Prop :=
  fanoBVColumn M 0 = 7 ∧
  fanoBVColumn M 1 = 25 ∧
  fanoBVColumn M 2 = 97 ∧
  fanoBVColumn M 3 = 42 ∧
  fanoBVColumn M 4 = 82 ∧
  fanoBVColumn M 5 = 76 ∧
  fanoBVColumn M 6 = 52

private theorem fanoBVNoRepeatedPair (source target a b c d e : Bool)
    (hsource : source = true)
    (hcount : fanoBVBit3 source + fanoBVBit3 target + fanoBVBit3 a +
      fanoBVBit3 b + fanoBVBit3 c + fanoBVBit3 d + fanoBVBit3 e = 1#3) :
    target = false := by
  subst source
  cases target <;> simp [fanoBVBit3] at hcount ⊢
  bv_omega

private theorem fanoBit17_0 : (17#7).getLsb (0 : Fin 7) = true := by
  decide +kernel

private theorem fanoBit17_4 : (17#7).getLsb (4 : Fin 7) = true := by
  decide +kernel

private theorem fanoBit34_1 : (34#7).getLsb (1 : Fin 7) = true := by
  decide +kernel

private theorem fanoBit34_5 : (34#7).getLsb (5 : Fin 7) = true := by
  decide +kernel

private theorem fanoBit36_2 : (36#7).getLsb (2 : Fin 7) = true := by
  decide +kernel

private theorem fanoBit36_5 : (36#7).getLsb (5 : Fin 7) = true := by
  decide +kernel

private theorem fanoBVColumn25 (r : BitVec 7)
    (hw : r.cpop = 3)
    (h0 : r.getLsb 0 = true) (h1 : r.getLsb 1 = false)
    (h2 : r.getLsb 2 = false) (h4 : r.getLsb 4 = true)
    (h5 : r.getLsb 5 = false) (h6 : r.getLsb 6 = false) :
    r = 25 := by
  have hr : r = 17 ∨ r = 25 := by
    by_cases h3 : r.getLsb 3 = true
    · right
      ext i
      interval_cases i <;> simp_all
    · left
      ext i
      interval_cases i <;> simp_all
  rcases hr with hr | hr
  · subst r
    exfalso
    have hne : (17#7).cpop ≠ 3 := by decide +kernel +revert
    exact hne hw
  · exact hr

private theorem fanoBVColumn42 (r : BitVec 7)
    (hw : r.cpop = 3)
    (h0 : r.getLsb 0 = false) (h1 : r.getLsb 1 = true)
    (h2 : r.getLsb 2 = false) (h4 : r.getLsb 4 = false)
    (h5 : r.getLsb 5 = true) (h6 : r.getLsb 6 = false) :
    r = 42 := by
  have hr : r = 34 ∨ r = 42 := by
    by_cases h3 : r.getLsb 3 = true
    · right
      ext i
      interval_cases i <;> simp_all
    · left
      ext i
      interval_cases i <;> simp_all
  rcases hr with hr | hr
  · subst r
    exfalso
    have hne : (34#7).cpop ≠ 3 := by decide +kernel +revert
    exact hne hw
  · exact hr

private theorem fanoBVColumn52 (r : BitVec 7)
    (hw : r.cpop = 3)
    (h0 : r.getLsb 0 = false) (h1 : r.getLsb 1 = false)
    (h2 : r.getLsb 2 = true) (h3 : r.getLsb 3 = false)
    (h5 : r.getLsb 5 = true) (h6 : r.getLsb 6 = false) :
    r = 52 := by
  have hr : r = 36 ∨ r = 52 := by
    by_cases h4 : r.getLsb 4 = true
    · right
      ext i
      interval_cases i <;> simp_all
    · left
      ext i
      interval_cases i <;> simp_all
  rcases hr with hr | hr
  · subst r
    exfalso
    have hne : (36#7).cpop ≠ 3 := by decide +kernel +revert
    exact hne hw
  · exact hr

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem fanoBV_classification (M : BitVec 49)
    (hvalid : fanoBVValid M) (hnorm : fanoBVNormalized M) :
    fanoBVCanonical M := by
  rcases hvalid with ⟨hweight, hpairs⟩
  rcases hnorm with ⟨h0, h2, h4, h5, h1mask, h3mask, h6mask⟩
  have hw1 := hweight (1 : Fin 7)
  have hw3 := hweight (3 : Fin 7)
  have hw6 := hweight (6 : Fin 7)
  have hp01 := hpairs (0 : Fin 7) (1 : Fin 7) (by decide)
  have hp02 := hpairs (0 : Fin 7) (2 : Fin 7) (by decide)
  have hp05 := hpairs (0 : Fin 7) (5 : Fin 7) (by decide)
  have hp06 := hpairs (0 : Fin 7) (6 : Fin 7) (by decide)
  have hp12 := hpairs (1 : Fin 7) (2 : Fin 7) (by decide)
  have hp14 := hpairs (1 : Fin 7) (4 : Fin 7) (by decide)
  have hp16 := hpairs (1 : Fin 7) (6 : Fin 7) (by decide)
  have hp23 := hpairs (2 : Fin 7) (3 : Fin 7) (by decide)
  have hp26 := hpairs (2 : Fin 7) (6 : Fin 7) (by decide)

  have no01 {i k : Fin 7} (hs : fanoBVPairBit M 0 i k = true)
      (hc : fanoBVPairCount M i k = 1#3) :
      fanoBVPairBit M 1 i k = false := by
    apply fanoBVNoRepeatedPair
      (source := fanoBVPairBit M 0 i k) (target := fanoBVPairBit M 1 i k)
      (a := fanoBVPairBit M 2 i k) (b := fanoBVPairBit M 3 i k)
      (c := fanoBVPairBit M 4 i k) (d := fanoBVPairBit M 5 i k)
      (e := fanoBVPairBit M 6 i k) hs
    simpa only [fanoBVPairCount] using hc
  have no21 {i k : Fin 7} (hs : fanoBVPairBit M 2 i k = true)
      (hc : fanoBVPairCount M i k = 1#3) :
      fanoBVPairBit M 1 i k = false := by
    apply fanoBVNoRepeatedPair
      (source := fanoBVPairBit M 2 i k) (target := fanoBVPairBit M 1 i k)
      (a := fanoBVPairBit M 0 i k) (b := fanoBVPairBit M 3 i k)
      (c := fanoBVPairBit M 4 i k) (d := fanoBVPairBit M 5 i k)
      (e := fanoBVPairBit M 6 i k) hs
    simpa only [fanoBVPairCount, add_assoc, add_comm, add_left_comm] using hc
  have no03 {i k : Fin 7} (hs : fanoBVPairBit M 0 i k = true)
      (hc : fanoBVPairCount M i k = 1#3) :
      fanoBVPairBit M 3 i k = false := by
    apply fanoBVNoRepeatedPair
      (source := fanoBVPairBit M 0 i k) (target := fanoBVPairBit M 3 i k)
      (a := fanoBVPairBit M 1 i k) (b := fanoBVPairBit M 2 i k)
      (c := fanoBVPairBit M 4 i k) (d := fanoBVPairBit M 5 i k)
      (e := fanoBVPairBit M 6 i k) hs
    simpa only [fanoBVPairCount, add_assoc, add_comm, add_left_comm] using hc
  have no43 {i k : Fin 7} (hs : fanoBVPairBit M 4 i k = true)
      (hc : fanoBVPairCount M i k = 1#3) :
      fanoBVPairBit M 3 i k = false := by
    apply fanoBVNoRepeatedPair
      (source := fanoBVPairBit M 4 i k) (target := fanoBVPairBit M 3 i k)
      (a := fanoBVPairBit M 0 i k) (b := fanoBVPairBit M 1 i k)
      (c := fanoBVPairBit M 2 i k) (d := fanoBVPairBit M 5 i k)
      (e := fanoBVPairBit M 6 i k) hs
    simpa only [fanoBVPairCount, add_assoc, add_comm, add_left_comm] using hc
  have no06 {i k : Fin 7} (hs : fanoBVPairBit M 0 i k = true)
      (hc : fanoBVPairCount M i k = 1#3) :
      fanoBVPairBit M 6 i k = false := by
    apply fanoBVNoRepeatedPair
      (source := fanoBVPairBit M 0 i k) (target := fanoBVPairBit M 6 i k)
      (a := fanoBVPairBit M 1 i k) (b := fanoBVPairBit M 2 i k)
      (c := fanoBVPairBit M 3 i k) (d := fanoBVPairBit M 4 i k)
      (e := fanoBVPairBit M 5 i k) hs
    simpa only [fanoBVPairCount, add_assoc, add_comm, add_left_comm] using hc
  have no56 {i k : Fin 7} (hs : fanoBVPairBit M 5 i k = true)
      (hc : fanoBVPairCount M i k = 1#3) :
      fanoBVPairBit M 6 i k = false := by
    apply fanoBVNoRepeatedPair
      (source := fanoBVPairBit M 5 i k) (target := fanoBVPairBit M 6 i k)
      (a := fanoBVPairBit M 0 i k) (b := fanoBVPairBit M 1 i k)
      (c := fanoBVPairBit M 2 i k) (d := fanoBVPairBit M 3 i k)
      (e := fanoBVPairBit M 4 i k) hs
    simpa only [fanoBVPairCount, add_assoc, add_comm, add_left_comm] using hc

  have h10 : (fanoBVColumn M 1).getLsb 0 = true := by
    have hb := congrArg (fun x : BitVec 7 => x.getLsb 0) h1mask
    norm_num at hb ⊢
    exact hb fanoBit17_0
  have h14 : (fanoBVColumn M 1).getLsb 4 = true := by
    have hb := congrArg (fun x : BitVec 7 => x.getLsb 4) h1mask
    norm_num at hb ⊢
    exact hb fanoBit17_4
  have h31 : (fanoBVColumn M 3).getLsb 1 = true := by
    have hb := congrArg (fun x : BitVec 7 => x.getLsb 1) h3mask
    norm_num at hb ⊢
    exact hb fanoBit34_1
  have h35 : (fanoBVColumn M 3).getLsb 5 = true := by
    have hb := congrArg (fun x : BitVec 7 => x.getLsb 5) h3mask
    norm_num at hb ⊢
    exact hb fanoBit34_5
  have h62 : (fanoBVColumn M 6).getLsb 2 = true := by
    have hb := congrArg (fun x : BitVec 7 => x.getLsb 2) h6mask
    norm_num at hb ⊢
    exact hb fanoBit36_2
  have h65 : (fanoBVColumn M 6).getLsb 5 = true := by
    have hb := congrArg (fun x : BitVec 7 => x.getLsb 5) h6mask
    norm_num at hb ⊢
    exact hb fanoBit36_5

  have h11 : (fanoBVColumn M 1).getLsb 1 = false := by
    have ht := no01 (i := 0) (k := 1) (by simp [fanoBVPairBit, h0]) hp01
    simpa only [fanoBVPairBit, h10, Bool.true_and] using ht
  have h12 : (fanoBVColumn M 1).getLsb 2 = false := by
    have ht := no01 (i := 0) (k := 2) (by simp [fanoBVPairBit, h0]) hp02
    simpa only [fanoBVPairBit, h10, Bool.true_and] using ht
  have h15 : (fanoBVColumn M 1).getLsb 5 = false := by
    have ht := no21 (i := 0) (k := 5) (by simp [fanoBVPairBit, h2]) hp05
    simpa only [fanoBVPairBit, h10, Bool.true_and] using ht
  have h16 : (fanoBVColumn M 1).getLsb 6 = false := by
    have ht := no21 (i := 0) (k := 6) (by simp [fanoBVPairBit, h2]) hp06
    simpa only [fanoBVPairBit, h10, Bool.true_and] using ht

  have h30 : (fanoBVColumn M 3).getLsb 0 = false := by
    have ht := no03 (i := 0) (k := 1) (by simp [fanoBVPairBit, h0]) hp01
    simpa only [fanoBVPairBit, h31, Bool.and_true] using ht
  have h32 : (fanoBVColumn M 3).getLsb 2 = false := by
    have ht := no03 (i := 1) (k := 2) (by simp [fanoBVPairBit, h0]) hp12
    simpa only [fanoBVPairBit, h31, Bool.true_and] using ht
  have h34 : (fanoBVColumn M 3).getLsb 4 = false := by
    have ht := no43 (i := 1) (k := 4) (by simp [fanoBVPairBit, h4]) hp14
    simpa only [fanoBVPairBit, h31, Bool.true_and] using ht
  have h36 : (fanoBVColumn M 3).getLsb 6 = false := by
    have ht := no43 (i := 1) (k := 6) (by simp [fanoBVPairBit, h4]) hp16
    simpa only [fanoBVPairBit, h31, Bool.true_and] using ht

  have h60 : (fanoBVColumn M 6).getLsb 0 = false := by
    have ht := no06 (i := 0) (k := 2) (by simp [fanoBVPairBit, h0]) hp02
    simpa only [fanoBVPairBit, h62, Bool.and_true] using ht
  have h61 : (fanoBVColumn M 6).getLsb 1 = false := by
    have ht := no06 (i := 1) (k := 2) (by simp [fanoBVPairBit, h0]) hp12
    simpa only [fanoBVPairBit, h62, Bool.and_true] using ht
  have h63 : (fanoBVColumn M 6).getLsb 3 = false := by
    have ht := no56 (i := 2) (k := 3) (by simp [fanoBVPairBit, h5]) hp23
    simpa only [fanoBVPairBit, h62, Bool.true_and] using ht
  have h66 : (fanoBVColumn M 6).getLsb 6 = false := by
    have ht := no56 (i := 2) (k := 6) (by simp [fanoBVPairBit, h5]) hp26
    simpa only [fanoBVPairBit, h62, Bool.true_and] using ht

  have h1 := fanoBVColumn25 (fanoBVColumn M 1) hw1 h10 h11 h12 h14 h15 h16
  have h3 := fanoBVColumn42 (fanoBVColumn M 3) hw3 h30 h31 h32 h34 h35 h36
  have h6 := fanoBVColumn52 (fanoBVColumn M 6) hw6 h60 h61 h62 h63 h65 h66
  exact ⟨h0, h1, h2, h3, h4, h5, h6⟩

end Erdos506.Finite
