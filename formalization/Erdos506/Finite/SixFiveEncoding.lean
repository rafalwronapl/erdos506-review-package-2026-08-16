import Erdos506.Finite.SixFiveClassification
import Erdos506.Finite.BitVecCounts

namespace Erdos506.Finite

def sixFiveProfileRow (R : Fin 10 → Finset (Fin 6)) (i : Fin 10) : BitVec 6 :=
  BitVec.ofFnLE fun j => decide (j ∈ R i)

def sixFiveMatrixRowIndex (q : Fin 60) : Fin 10 :=
  ⟨q.val / 6, by omega⟩

def sixFiveMatrixColumnIndex (q : Fin 60) : Fin 6 :=
  ⟨q.val % 6, Nat.mod_lt _ (by omega)⟩

def sixFiveProfileMatrix (R : Fin 10 → Finset (Fin 6)) : BitVec 60 :=
  BitVec.ofFnLE fun q =>
    decide (sixFiveMatrixColumnIndex q ∈ R (sixFiveMatrixRowIndex q))

theorem sixFiveProfileMatrix_row
    (R : Fin 10 → Finset (Fin 6)) (i : Fin 10) :
    sixFiveBVRow (sixFiveProfileMatrix R) i = sixFiveProfileRow R i := by
  ext j
  have hlt : 6 * i.val + j < 60 := by omega
  let q : Fin 60 := ⟨6 * i.val + j, hlt⟩
  have hrow : sixFiveMatrixRowIndex q = i := by
    apply Fin.ext
    simp [q, sixFiveMatrixRowIndex]
    omega
  have hcol : sixFiveMatrixColumnIndex q = ⟨j, by omega⟩ := by
    apply Fin.ext
    simp [q, sixFiveMatrixColumnIndex]
    omega
  simp [sixFiveBVRow, sixFiveProfileMatrix, sixFiveProfileRow,
    hlt, q, hrow, hcol]

theorem sixFiveProfileRow_getLsb
    (R : Fin 10 → Finset (Fin 6)) (i : Fin 10) (j : Fin 6) :
    (sixFiveProfileRow R i).getLsb j = decide (j ∈ R i) := by
  simp [sixFiveProfileRow]

theorem sixFiveProfileRow_cpop :
    ∀ S : Finset (Fin 6),
      (BitVec.ofFnLE fun j : Fin 6 => decide (j ∈ S)).cpop = S.card := by
  intro S
  simpa using cpop_membership S

def sixFiveFinsetCount4 (S : Finset (Fin 10)) : BitVec 4 :=
  sixFiveBVBit4 (decide ((0 : Fin 10) ∈ S)) +
  sixFiveBVBit4 (decide ((1 : Fin 10) ∈ S)) +
  sixFiveBVBit4 (decide ((2 : Fin 10) ∈ S)) +
  sixFiveBVBit4 (decide ((3 : Fin 10) ∈ S)) +
  sixFiveBVBit4 (decide ((4 : Fin 10) ∈ S)) +
  sixFiveBVBit4 (decide ((5 : Fin 10) ∈ S)) +
  sixFiveBVBit4 (decide ((6 : Fin 10) ∈ S)) +
  sixFiveBVBit4 (decide ((7 : Fin 10) ∈ S)) +
  sixFiveBVBit4 (decide ((8 : Fin 10) ∈ S)) +
  sixFiveBVBit4 (decide ((9 : Fin 10) ∈ S))

theorem sixFiveFinsetCount4_eq_card :
    ∀ S : Finset (Fin 10),
      sixFiveFinsetCount4 S = BitVec.ofNat 4 S.card := by
  intro S
  apply BitVec.eq_of_toNat_eq
  have h := toNat_cpop_membership S
  rw [toNat_cpop_ofFnLE] at h
  simp [Fin.sum_univ_succ] at h
  simp only [sixFiveFinsetCount4, sixFiveBVBit4, BitVec.toNat_add,
    BitVec.toNat_setWidth, BitVec.toNat_ofBool, BitVec.toNat_ofNat]
  simp only [← Nat.add_mod]
  simpa [Nat.add_assoc] using congrArg (fun z : Nat => z % 2 ^ 4) h

theorem sixFiveProfileMatrix_columnCount
    (R : Fin 10 → Finset (Fin 6)) (j : Fin 6) :
    sixFiveBVColumnCount (sixFiveProfileMatrix R) j =
      BitVec.ofNat 4
        ((Finset.univ : Finset (Fin 10)).filter (fun i => j ∈ R i)).card := by
  rw [← sixFiveFinsetCount4_eq_card]
  simp [sixFiveBVColumnCount, sixFiveFinsetCount4,
    sixFiveProfileMatrix_row, sixFiveProfileRow]

theorem sixFiveProfileMatrix_pairColumnCount
    (R : Fin 10 → Finset (Fin 6)) (j k : Fin 6) :
    sixFiveBVPairColumnCount (sixFiveProfileMatrix R) j k =
      BitVec.ofNat 4
        ((Finset.univ : Finset (Fin 10)).filter
          (fun i => j ∈ R i ∧ k ∈ R i)).card := by
  rw [← sixFiveFinsetCount4_eq_card]
  simp [sixFiveBVPairColumnCount, sixFiveFinsetCount4,
    sixFiveProfileMatrix_row, sixFiveProfileRow]

theorem sixFiveProfileRow_injective
    (R : Fin 10 → Finset (Fin 6)) {i k : Fin 10}
    (h : sixFiveProfileRow R i = sixFiveProfileRow R k) : R i = R k := by
  ext j
  have hj := congrArg (fun r : BitVec 6 => r.getLsb j) h
  simpa [sixFiveProfileRow] using hj

def SixFiveProfilesValid (R : Fin 10 → Finset (Fin 6)) : Prop :=
  (∀ i, (R i).card = 3) ∧
  (∀ j, ((Finset.univ : Finset (Fin 10)).filter (fun i => j ∈ R i)).card = 5) ∧
  (∀ j k, j ≠ k →
    ((Finset.univ : Finset (Fin 10)).filter
      (fun i => j ∈ R i ∧ k ∈ R i)).card = 2) ∧
  Function.Injective R

theorem sixFiveProfileMatrix_valid
    (R : Fin 10 → Finset (Fin 6)) (h : SixFiveProfilesValid R) :
    sixFiveBVValid (sixFiveProfileMatrix R) := by
  rcases h with ⟨hrow, hcol, hpair, hinj⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i
    rw [sixFiveProfileMatrix_row]
    rw [sixFiveProfileRow, sixFiveProfileRow_cpop, hrow i]
    norm_num
  · intro j
    rw [sixFiveProfileMatrix_columnCount, hcol j]
  · intro j k hjk
    rw [sixFiveProfileMatrix_pairColumnCount, hpair j k hjk]
  · intro i k hik heq
    apply hik
    apply hinj
    apply sixFiveProfileRow_injective R
    simpa only [sixFiveProfileMatrix_row] using heq

def SixFiveProfilesNormalized (R : Fin 10 → Finset (Fin 6)) : Prop :=
  R 0 = {0, 1, 2} ∧
  (0 : Fin 6) ∈ R 1 ∧ (1 : Fin 6) ∈ R 1 ∧
  (0 : Fin 6) ∈ R 2 ∧ (2 : Fin 6) ∈ R 2 ∧
  (1 : Fin 6) ∈ R 3 ∧ (2 : Fin 6) ∈ R 3

theorem sixFiveProfileRow_and_three :
    ∀ S : Finset (Fin 6),
      (BitVec.ofFnLE fun j : Fin 6 => decide (j ∈ S)) &&& 3 = 3 ↔
        (0 : Fin 6) ∈ S ∧ (1 : Fin 6) ∈ S := by
  decide_cbv

theorem sixFiveProfileRow_and_five :
    ∀ S : Finset (Fin 6),
      (BitVec.ofFnLE fun j : Fin 6 => decide (j ∈ S)) &&& 5 = 5 ↔
        (0 : Fin 6) ∈ S ∧ (2 : Fin 6) ∈ S := by
  decide_cbv

theorem sixFiveProfileRow_and_six :
    ∀ S : Finset (Fin 6),
      (BitVec.ofFnLE fun j : Fin 6 => decide (j ∈ S)) &&& 6 = 6 ↔
        (1 : Fin 6) ∈ S ∧ (2 : Fin 6) ∈ S := by
  decide_cbv

theorem sixFiveProfileMatrix_normalized
    (R : Fin 10 → Finset (Fin 6)) (h : SixFiveProfilesNormalized R) :
    sixFiveBVNormalized (sixFiveProfileMatrix R) := by
  rcases h with ⟨hzero, h10, h11, h20, h22, h31, h32⟩
  simp only [sixFiveBVNormalized, sixFiveProfileMatrix_row]
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [sixFiveProfileRow, hzero]
    decide_cbv
  · exact (sixFiveProfileRow_and_three (R 1)).2 ⟨h10, h11⟩
  · exact (sixFiveProfileRow_and_five (R 2)).2 ⟨h20, h22⟩
  · exact (sixFiveProfileRow_and_six (R 3)).2 ⟨h31, h32⟩

def sixFiveDecodeRow (r : BitVec 6) : Finset (Fin 6) :=
  Finset.univ.filter fun j => r.getLsb j

@[simp] theorem sixFiveDecode_profileRow
    (R : Fin 10 → Finset (Fin 6)) (i : Fin 10) :
    sixFiveDecodeRow (sixFiveProfileRow R i) = R i := by
  ext j
  simp [sixFiveDecodeRow, sixFiveProfileRow]

@[simp] theorem sixFiveProfileRow_decode
    (r : BitVec 6) :
    BitVec.ofFnLE (fun j : Fin 6 => decide (j ∈ sixFiveDecodeRow r)) = r := by
  ext j
  simp [sixFiveDecodeRow]

theorem sixFiveProfileRow_eq_iff
    (R : Fin 10 → Finset (Fin 6)) (i : Fin 10) (r : BitVec 6) :
    sixFiveProfileRow R i = r ↔ R i = sixFiveDecodeRow r := by
  constructor
  · intro h
    rw [← sixFiveDecode_profileRow R i, h]
  · intro h
    rw [sixFiveProfileRow, h, sixFiveProfileRow_decode]

def sixFiveProfileInSet0 (S : Finset (Fin 6)) : Prop :=
  S = sixFiveDecodeRow 7 ∨ S = sixFiveDecodeRow 11 ∨
  S = sixFiveDecodeRow 21 ∨ S = sixFiveDecodeRow 26 ∨
  S = sixFiveDecodeRow 28 ∨ S = sixFiveDecodeRow 38 ∨
  S = sixFiveDecodeRow 41 ∨ S = sixFiveDecodeRow 44 ∨
  S = sixFiveDecodeRow 49 ∨ S = sixFiveDecodeRow 50

def sixFiveProfileInSet1 (S : Finset (Fin 6)) : Prop :=
  S = sixFiveDecodeRow 7 ∨ S = sixFiveDecodeRow 11 ∨
  S = sixFiveDecodeRow 22 ∨ S = sixFiveDecodeRow 25 ∨
  S = sixFiveDecodeRow 28 ∨ S = sixFiveDecodeRow 37 ∨
  S = sixFiveDecodeRow 42 ∨ S = sixFiveDecodeRow 44 ∨
  S = sixFiveDecodeRow 49 ∨ S = sixFiveDecodeRow 50

def sixFiveProfileInSet2 (S : Finset (Fin 6)) : Prop :=
  S = sixFiveDecodeRow 7 ∨ S = sixFiveDecodeRow 13 ∨
  S = sixFiveDecodeRow 19 ∨ S = sixFiveDecodeRow 26 ∨
  S = sixFiveDecodeRow 28 ∨ S = sixFiveDecodeRow 38 ∨
  S = sixFiveDecodeRow 41 ∨ S = sixFiveDecodeRow 42 ∨
  S = sixFiveDecodeRow 49 ∨ S = sixFiveDecodeRow 52

def sixFiveProfileInSet3 (S : Finset (Fin 6)) : Prop :=
  S = sixFiveDecodeRow 7 ∨ S = sixFiveDecodeRow 14 ∨
  S = sixFiveDecodeRow 19 ∨ S = sixFiveDecodeRow 25 ∨
  S = sixFiveDecodeRow 28 ∨ S = sixFiveDecodeRow 37 ∨
  S = sixFiveDecodeRow 41 ∨ S = sixFiveDecodeRow 42 ∨
  S = sixFiveDecodeRow 50 ∨ S = sixFiveDecodeRow 52

def sixFiveProfileInSet4 (S : Finset (Fin 6)) : Prop :=
  S = sixFiveDecodeRow 7 ∨ S = sixFiveDecodeRow 13 ∨
  S = sixFiveDecodeRow 22 ∨ S = sixFiveDecodeRow 25 ∨
  S = sixFiveDecodeRow 26 ∨ S = sixFiveDecodeRow 35 ∨
  S = sixFiveDecodeRow 42 ∨ S = sixFiveDecodeRow 44 ∨
  S = sixFiveDecodeRow 49 ∨ S = sixFiveDecodeRow 52

def sixFiveProfileInSet5 (S : Finset (Fin 6)) : Prop :=
  S = sixFiveDecodeRow 7 ∨ S = sixFiveDecodeRow 14 ∨
  S = sixFiveDecodeRow 21 ∨ S = sixFiveDecodeRow 25 ∨
  S = sixFiveDecodeRow 26 ∨ S = sixFiveDecodeRow 35 ∨
  S = sixFiveDecodeRow 41 ∨ S = sixFiveDecodeRow 44 ∨
  S = sixFiveDecodeRow 50 ∨ S = sixFiveDecodeRow 52

def SixFiveProfilesClassified (R : Fin 10 → Finset (Fin 6)) : Prop :=
  (∀ i, sixFiveProfileInSet0 (R i)) ∨
  (∀ i, sixFiveProfileInSet1 (R i)) ∨
  (∀ i, sixFiveProfileInSet2 (R i)) ∨
  (∀ i, sixFiveProfileInSet3 (R i)) ∨
  (∀ i, sixFiveProfileInSet4 (R i)) ∨
  (∀ i, sixFiveProfileInSet5 (R i))

theorem sixFiveProfiles_classification
    (R : Fin 10 → Finset (Fin 6))
    (hvalid : SixFiveProfilesValid R)
    (hnorm : SixFiveProfilesNormalized R) :
    SixFiveProfilesClassified R := by
  have h := sixFiveBV_classification (sixFiveProfileMatrix R)
    (sixFiveProfileMatrix_valid R hvalid)
    (sixFiveProfileMatrix_normalized R hnorm)
  simpa [sixFiveBVClassified, SixFiveProfilesClassified,
    sixFiveBVInSet0, sixFiveBVInSet1, sixFiveBVInSet2,
    sixFiveBVInSet3, sixFiveBVInSet4, sixFiveBVInSet5,
    sixFiveProfileInSet0, sixFiveProfileInSet1, sixFiveProfileInSet2,
    sixFiveProfileInSet3, sixFiveProfileInSet4, sixFiveProfileInSet5,
    sixFiveProfileMatrix_row, sixFiveProfileRow_eq_iff] using h

end Erdos506.Finite
