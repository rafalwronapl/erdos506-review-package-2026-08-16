import Mathlib

/-!
# Bit-vector encoding of the six-by-five design

The geometric and counting arguments reduce the only finite classification
used at the ten-point wall to a `60`-bit incidence matrix.  Its structural,
kernel-checked classification is proved in `SixFiveClassification`.
-/

namespace Erdos506.Finite

def sixFiveBVRow (M : BitVec 60) (i : Fin 10) : BitVec 6 :=
  BitVec.extractLsb' (6 * i.val) 6 M

def sixFiveBVBit4 (b : Bool) : BitVec 4 :=
  (BitVec.ofBool b).zeroExtend 4

def sixFiveBVColumnCount (M : BitVec 60) (j : Fin 6) : BitVec 4 :=
  sixFiveBVBit4 ((sixFiveBVRow M 0).getLsb j) +
  sixFiveBVBit4 ((sixFiveBVRow M 1).getLsb j) +
  sixFiveBVBit4 ((sixFiveBVRow M 2).getLsb j) +
  sixFiveBVBit4 ((sixFiveBVRow M 3).getLsb j) +
  sixFiveBVBit4 ((sixFiveBVRow M 4).getLsb j) +
  sixFiveBVBit4 ((sixFiveBVRow M 5).getLsb j) +
  sixFiveBVBit4 ((sixFiveBVRow M 6).getLsb j) +
  sixFiveBVBit4 ((sixFiveBVRow M 7).getLsb j) +
  sixFiveBVBit4 ((sixFiveBVRow M 8).getLsb j) +
  sixFiveBVBit4 ((sixFiveBVRow M 9).getLsb j)

def sixFiveBVPairColumnCount (M : BitVec 60) (j k : Fin 6) : BitVec 4 :=
  sixFiveBVBit4 ((sixFiveBVRow M 0).getLsb j && (sixFiveBVRow M 0).getLsb k) +
  sixFiveBVBit4 ((sixFiveBVRow M 1).getLsb j && (sixFiveBVRow M 1).getLsb k) +
  sixFiveBVBit4 ((sixFiveBVRow M 2).getLsb j && (sixFiveBVRow M 2).getLsb k) +
  sixFiveBVBit4 ((sixFiveBVRow M 3).getLsb j && (sixFiveBVRow M 3).getLsb k) +
  sixFiveBVBit4 ((sixFiveBVRow M 4).getLsb j && (sixFiveBVRow M 4).getLsb k) +
  sixFiveBVBit4 ((sixFiveBVRow M 5).getLsb j && (sixFiveBVRow M 5).getLsb k) +
  sixFiveBVBit4 ((sixFiveBVRow M 6).getLsb j && (sixFiveBVRow M 6).getLsb k) +
  sixFiveBVBit4 ((sixFiveBVRow M 7).getLsb j && (sixFiveBVRow M 7).getLsb k) +
  sixFiveBVBit4 ((sixFiveBVRow M 8).getLsb j && (sixFiveBVRow M 8).getLsb k) +
  sixFiveBVBit4 ((sixFiveBVRow M 9).getLsb j && (sixFiveBVRow M 9).getLsb k)

def sixFiveBVValid (M : BitVec 60) : Prop :=
  (∀ i : Fin 10, (sixFiveBVRow M i).cpop = 3) ∧
  (∀ j : Fin 6, sixFiveBVColumnCount M j = 5#4) ∧
  (∀ j k : Fin 6, j ≠ k → sixFiveBVPairColumnCount M j k = 2#4) ∧
  ∀ i k : Fin 10, i ≠ k → sixFiveBVRow M i ≠ sixFiveBVRow M k

def sixFiveBVNormalized (M : BitVec 60) : Prop :=
  sixFiveBVRow M 0 = 7 ∧
  sixFiveBVRow M 1 &&& 3 = 3 ∧
  sixFiveBVRow M 2 &&& 5 = 5 ∧
  sixFiveBVRow M 3 &&& 6 = 6

def sixFiveBVInSet0 (r : BitVec 6) : Prop :=
  r = 7 ∨ r = 11 ∨ r = 21 ∨ r = 26 ∨ r = 28 ∨
    r = 38 ∨ r = 41 ∨ r = 44 ∨ r = 49 ∨ r = 50

def sixFiveBVInSet1 (r : BitVec 6) : Prop :=
  r = 7 ∨ r = 11 ∨ r = 22 ∨ r = 25 ∨ r = 28 ∨
    r = 37 ∨ r = 42 ∨ r = 44 ∨ r = 49 ∨ r = 50

def sixFiveBVInSet2 (r : BitVec 6) : Prop :=
  r = 7 ∨ r = 13 ∨ r = 19 ∨ r = 26 ∨ r = 28 ∨
    r = 38 ∨ r = 41 ∨ r = 42 ∨ r = 49 ∨ r = 52

def sixFiveBVInSet3 (r : BitVec 6) : Prop :=
  r = 7 ∨ r = 14 ∨ r = 19 ∨ r = 25 ∨ r = 28 ∨
    r = 37 ∨ r = 41 ∨ r = 42 ∨ r = 50 ∨ r = 52

def sixFiveBVInSet4 (r : BitVec 6) : Prop :=
  r = 7 ∨ r = 13 ∨ r = 22 ∨ r = 25 ∨ r = 26 ∨
    r = 35 ∨ r = 42 ∨ r = 44 ∨ r = 49 ∨ r = 52

def sixFiveBVInSet5 (r : BitVec 6) : Prop :=
  r = 7 ∨ r = 14 ∨ r = 21 ∨ r = 25 ∨ r = 26 ∨
    r = 35 ∨ r = 41 ∨ r = 44 ∨ r = 50 ∨ r = 52

def sixFiveBVClassified (M : BitVec 60) : Prop :=
  (∀ i : Fin 10, sixFiveBVInSet0 (sixFiveBVRow M i)) ∨
  (∀ i : Fin 10, sixFiveBVInSet1 (sixFiveBVRow M i)) ∨
  (∀ i : Fin 10, sixFiveBVInSet2 (sixFiveBVRow M i)) ∨
  (∀ i : Fin 10, sixFiveBVInSet3 (sixFiveBVRow M i)) ∨
  (∀ i : Fin 10, sixFiveBVInSet4 (sixFiveBVRow M i)) ∨
  (∀ i : Fin 10, sixFiveBVInSet5 (sixFiveBVRow M i))

end Erdos506.Finite
