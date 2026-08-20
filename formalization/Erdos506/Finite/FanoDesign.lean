import Erdos506.Finite.FanoBV
import Erdos506.Finite.BitVecCounts

/-!
# Abstract STS(7), encoding, and canonical labeling

This file bridges an ordinary finite Steiner triple design to the checked
`49`-bit certificate.  The only search is the isolated theorem in
`FanoBV.lean`; relabeling and all cardinality translations are proved here.
-/

namespace Erdos506.Finite

structure SevenSteinerDesign (Point Block : Type*)
    [Fintype Point] [DecidableEq Point]
    [Fintype Block] [DecidableEq Block] where
  line : Block → Finset Point
  point_card : Fintype.card Point = 7
  block_card : Fintype.card Block = 7
  line_card : ∀ b, (line b).card = 3
  pair_unique : ∀ A ∈ (Finset.univ : Finset Point).powersetCard 2,
    ∃! b, A ⊆ line b

noncomputable def SevenSteinerDesign.relabeledLines
    {Point Block : Type*} [Fintype Point] [DecidableEq Point]
    [Fintype Block] [DecidableEq Block]
    (D : SevenSteinerDesign Point Block)
    (P : Fin 7 ≃ Point) (B : Fin 7 ≃ Block) :
    Fin 7 → Finset (Fin 7) :=
  fun j => (D.line (B j)).preimage P P.injective.injOn

@[simp] theorem SevenSteinerDesign.mem_relabeledLines
    {Point Block : Type*} [Fintype Point] [DecidableEq Point]
    [Fintype Block] [DecidableEq Block]
    (D : SevenSteinerDesign Point Block)
    (P : Fin 7 ≃ Point) (B : Fin 7 ≃ Block) (i j : Fin 7) :
    i ∈ D.relabeledLines P B j ↔ P i ∈ D.line (B j) := by
  simp [SevenSteinerDesign.relabeledLines]

theorem fano_card_preimage_equiv
    {α β : Type*} [Fintype α] [Fintype β]
    (e : α ≃ β) (S : Finset β) :
    (S.preimage e e.injective.injOn).card = S.card := by
  classical
  rw [Finset.card_preimage]
  simp

def fanoEncodeLine (S : Finset (Fin 7)) : BitVec 7 :=
  BitVec.ofFnLE fun i => decide (i ∈ S)

def fanoMatrixRowIndex (q : Fin 49) : Fin 7 :=
  ⟨q.val % 7, Nat.mod_lt _ (by omega)⟩

def fanoMatrixColumnIndex (q : Fin 49) : Fin 7 :=
  ⟨q.val / 7, by omega⟩

def fanoDesignMatrix (L : Fin 7 → Finset (Fin 7)) : BitVec 49 :=
  BitVec.ofFnLE fun q => decide
    (fanoMatrixRowIndex q ∈ L (fanoMatrixColumnIndex q))

theorem fanoDesignMatrix_column
    (L : Fin 7 → Finset (Fin 7)) (j : Fin 7) :
    fanoBVColumn (fanoDesignMatrix L) j = fanoEncodeLine (L j) := by
  ext i
  have hlt : 7 * j.val + i < 49 := by omega
  let q : Fin 49 := ⟨7 * j.val + i, hlt⟩
  have hrow : fanoMatrixRowIndex q = ⟨i, by omega⟩ := by
    apply Fin.ext
    simp [q, fanoMatrixRowIndex]
    omega
  have hcol : fanoMatrixColumnIndex q = j := by
    apply Fin.ext
    simp [q, fanoMatrixColumnIndex]
    omega
  simp [fanoBVColumn, fanoDesignMatrix, fanoEncodeLine,
    hlt, q, hrow, hcol]

theorem fanoEncodeLine_cpop :
    ∀ S : Finset (Fin 7), (fanoEncodeLine S).cpop = S.card := by
  intro S
  simpa [fanoEncodeLine] using cpop_membership S

def fanoFinsetCount3 (S : Finset (Fin 7)) : BitVec 3 :=
  fanoBVBit3 (decide ((0 : Fin 7) ∈ S)) +
  fanoBVBit3 (decide ((1 : Fin 7) ∈ S)) +
  fanoBVBit3 (decide ((2 : Fin 7) ∈ S)) +
  fanoBVBit3 (decide ((3 : Fin 7) ∈ S)) +
  fanoBVBit3 (decide ((4 : Fin 7) ∈ S)) +
  fanoBVBit3 (decide ((5 : Fin 7) ∈ S)) +
  fanoBVBit3 (decide ((6 : Fin 7) ∈ S))

theorem fanoFinsetCount3_eq_card :
    ∀ S : Finset (Fin 7),
      fanoFinsetCount3 S = BitVec.ofNat 3 S.card := by
  intro S
  apply BitVec.eq_of_toNat_eq
  have h := toNat_cpop_membership S
  rw [toNat_cpop_ofFnLE] at h
  simp [Fin.sum_univ_succ] at h
  simp only [fanoFinsetCount3, fanoBVBit3, BitVec.toNat_add,
    BitVec.toNat_setWidth, BitVec.toNat_ofBool, BitVec.toNat_ofNat]
  simp only [← Nat.add_mod]
  simpa [Nat.add_assoc] using congrArg (fun z : Nat => z % 2 ^ 3) h

theorem fanoDesignMatrix_pairCount
    (L : Fin 7 → Finset (Fin 7)) (i k : Fin 7) :
    fanoBVPairCount (fanoDesignMatrix L) i k =
      BitVec.ofNat 3
        ((Finset.univ : Finset (Fin 7)).filter
          (fun j => i ∈ L j ∧ k ∈ L j)).card := by
  rw [← fanoFinsetCount3_eq_card]
  simp [fanoBVPairCount, fanoBVPairBit, fanoFinsetCount3,
    fanoDesignMatrix_column, fanoEncodeLine]

theorem SevenSteinerDesign.relabeled_pair_card
    {Point Block : Type*} [Fintype Point] [DecidableEq Point]
    [Fintype Block] [DecidableEq Block]
    (D : SevenSteinerDesign Point Block)
    (P : Fin 7 ≃ Point) (B : Fin 7 ≃ Block)
    (i k : Fin 7) (hik : i ≠ k) :
    ((Finset.univ : Finset (Fin 7)).filter
      (fun j => i ∈ D.relabeledLines P B j ∧
        k ∈ D.relabeledLines P B j)).card = 1 := by
  classical
  let A : Finset Point := {P i, P k}
  have hAcard : A.card = 2 := by simp [A, P.injective.ne hik]
  have hApow : A ∈ (Finset.univ : Finset Point).powersetCard 2 := by
    simp [A, hAcard]
  obtain ⟨b, hb, huniq⟩ := D.pair_unique A hApow
  have hfilter :
      (Finset.univ : Finset (Fin 7)).filter
        (fun j => i ∈ D.relabeledLines P B j ∧
          k ∈ D.relabeledLines P B j) = {B.symm b} := by
    ext j
    constructor
    · intro hj
      have hj' := (Finset.mem_filter.mp hj).2
      have hsub : A ⊆ D.line (B j) := by
        intro x hx
        simp only [A, Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl
        · exact (D.mem_relabeledLines P B i j).mp hj'.1
        · exact (D.mem_relabeledLines P B k j).mp hj'.2
      have heq : B j = b := huniq (B j) hsub
      have heq' := congrArg B.symm heq
      simpa using heq'
    · intro hj
      have hjB : j = B.symm b := by simpa using hj
      subst j
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_, ?_⟩
      · apply (D.mem_relabeledLines P B i (B.symm b)).mpr
        simpa [A] using hb (by simp [A])
      · apply (D.mem_relabeledLines P B k (B.symm b)).mpr
        simpa [A] using hb (by simp [A])
  rw [hfilter]
  simp

theorem SevenSteinerDesign.matrix_valid
    {Point Block : Type*} [Fintype Point] [DecidableEq Point]
    [Fintype Block] [DecidableEq Block]
    (D : SevenSteinerDesign Point Block)
    (P : Fin 7 ≃ Point) (B : Fin 7 ≃ Block) :
    fanoBVValid (fanoDesignMatrix (D.relabeledLines P B)) := by
  constructor
  · intro j
    rw [fanoDesignMatrix_column, fanoEncodeLine_cpop]
    rw [SevenSteinerDesign.relabeledLines]
    rw [fano_card_preimage_equiv]
    rw [D.line_card]
    norm_num
  · intro i k hik
    rw [fanoDesignMatrix_pairCount, D.relabeled_pair_card P B i k hik]

def fanoCanonicalLine : Fin 7 → Finset (Fin 7) := ![
  {0, 1, 2},
  {0, 3, 4},
  {0, 5, 6},
  {1, 3, 5},
  {1, 4, 6},
  {2, 3, 6},
  {2, 4, 5}
]

def FanoLinesNormalized (L : Fin 7 → Finset (Fin 7)) : Prop :=
  L 0 = {0, 1, 2} ∧
  L 2 = {0, 5, 6} ∧
  L 4 = {1, 4, 6} ∧
  L 5 = {2, 3, 6} ∧
  (0 : Fin 7) ∈ L 1 ∧ (4 : Fin 7) ∈ L 1 ∧
  (1 : Fin 7) ∈ L 3 ∧ (5 : Fin 7) ∈ L 3 ∧
  (2 : Fin 7) ∈ L 6 ∧ (5 : Fin 7) ∈ L 6

theorem fanoBV_and_seventeen_of_getLsb
    (r : BitVec 7) (h0 : r.getLsb 0 = true) (h4 : r.getLsb 4 = true) :
    r &&& 17 = 17 := by
  ext i hi
  interval_cases i <;> simp_all

theorem fanoBV_and_thirtyFour_of_getLsb
    (r : BitVec 7) (h1 : r.getLsb 1 = true) (h5 : r.getLsb 5 = true) :
    r &&& 34 = 34 := by
  ext i hi
  interval_cases i <;> simp_all

theorem fanoBV_and_thirtySix_of_getLsb
    (r : BitVec 7) (h2 : r.getLsb 2 = true) (h5 : r.getLsb 5 = true) :
    r &&& 36 = 36 := by
  ext i hi
  interval_cases i <;> simp_all

theorem fanoDesignMatrix_normalized
    (L : Fin 7 → Finset (Fin 7)) (h : FanoLinesNormalized L) :
    fanoBVNormalized (fanoDesignMatrix L) := by
  rcases h with ⟨h0, h2, h4, h5, h10, h14, h31, h35, h62, h65⟩
  simp only [fanoBVNormalized, fanoDesignMatrix_column]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [h0]
    decide_cbv
  · rw [h2]
    decide_cbv
  · rw [h4]
    decide_cbv
  · rw [h5]
    decide_cbv
  · apply fanoBV_and_seventeen_of_getLsb
    · simpa [fanoEncodeLine] using h10
    · simpa [fanoEncodeLine] using h14
  · apply fanoBV_and_thirtyFour_of_getLsb
    · simpa [fanoEncodeLine] using h31
    · simpa [fanoEncodeLine] using h35
  · apply fanoBV_and_thirtySix_of_getLsb
    · simpa [fanoEncodeLine] using h62
    · simpa [fanoEncodeLine] using h65

theorem fanoEncodeLine_injective : Function.Injective fanoEncodeLine := by
  intro S T h
  ext i
  have hi := congrArg (fun r : BitVec 7 => r.getLsb i) h
  simpa [fanoEncodeLine] using hi

theorem SevenSteinerDesign.canonical_of_normalized
    {Point Block : Type*} [Fintype Point] [DecidableEq Point]
    [Fintype Block] [DecidableEq Block]
    (D : SevenSteinerDesign Point Block)
    (P : Fin 7 ≃ Point) (B : Fin 7 ≃ Block)
    (hnorm : FanoLinesNormalized (D.relabeledLines P B)) :
    ∀ j, D.relabeledLines P B j = fanoCanonicalLine j := by
  have hc := fanoBV_classification
    (fanoDesignMatrix (D.relabeledLines P B))
    (D.matrix_valid P B)
    (fanoDesignMatrix_normalized _ hnorm)
  simp only [fanoBVCanonical, fanoDesignMatrix_column] at hc
  rcases hc with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  intro j
  fin_cases j
  · apply fanoEncodeLine_injective
    calc
      fanoEncodeLine (D.relabeledLines P B 0) = 7 := h0
      _ = fanoEncodeLine (fanoCanonicalLine 0) := by decide_cbv
  · apply fanoEncodeLine_injective
    calc
      fanoEncodeLine (D.relabeledLines P B 1) = 25 := h1
      _ = fanoEncodeLine (fanoCanonicalLine 1) := by decide_cbv
  · apply fanoEncodeLine_injective
    calc
      fanoEncodeLine (D.relabeledLines P B 2) = 97 := h2
      _ = fanoEncodeLine (fanoCanonicalLine 2) := by decide_cbv
  · apply fanoEncodeLine_injective
    calc
      fanoEncodeLine (D.relabeledLines P B 3) = 42 := h3
      _ = fanoEncodeLine (fanoCanonicalLine 3) := by decide_cbv
  · apply fanoEncodeLine_injective
    calc
      fanoEncodeLine (D.relabeledLines P B 4) = 82 := h4
      _ = fanoEncodeLine (fanoCanonicalLine 4) := by decide_cbv
  · apply fanoEncodeLine_injective
    calc
      fanoEncodeLine (D.relabeledLines P B 5) = 76 := h5
      _ = fanoEncodeLine (fanoCanonicalLine 5) := by decide_cbv
  · apply fanoEncodeLine_injective
    calc
      fanoEncodeLine (D.relabeledLines P B 6) = 52 := h6
      _ = fanoEncodeLine (fanoCanonicalLine 6) := by decide_cbv

theorem exists_third_of_pair_subset_card_three
    {α : Type*} [DecidableEq α] (S : Finset α) (x y : α)
    (hxy : x ≠ y) (hcard : S.card = 3)
    (hx : x ∈ S) (hy : y ∈ S) :
    ∃ z, z ≠ x ∧ z ≠ y ∧ S = {x, y, z} := by
  have hexists : ∃ z ∈ S, z ≠ x ∧ z ≠ y := by
    by_contra h
    have hsub : S ⊆ {x, y} := by
      intro z hz
      have hzxy : z = x ∨ z = y := by
        by_contra hne
        apply h
        refine ⟨z, hz, ?_, ?_⟩
        · intro hzx
          exact hne (Or.inl hzx)
        · intro hzy
          exact hne (Or.inr hzy)
      rcases hzxy with hzx | hzy
      · simp [hzx]
      · simp [hzy]
    have hle := Finset.card_le_card hsub
    simp [hxy, hcard] at hle
  obtain ⟨z, hz, hzx, hzy⟩ := hexists
  refine ⟨z, hzx, hzy, ?_⟩
  symm
  apply Finset.eq_of_subset_of_card_le
  · intro q hq
    simp only [Finset.mem_insert, Finset.mem_singleton] at hq
    rcases hq with rfl | rfl | rfl
    · exact hx
    · exact hy
    · exact hz
  · have htrip : ({x, y, z} : Finset α).card = 3 := by
      simp [hxy, hzx.symm, hzy.symm]
    rw [hcard, htrip]

theorem SevenSteinerDesign.block_eq_of_pair_subset
    {Point Block : Type*} [Fintype Point] [DecidableEq Point]
    [Fintype Block] [DecidableEq Block]
    (D : SevenSteinerDesign Point Block)
    {x y : Point} (hxy : x ≠ y) {b c : Block}
    (hb : ({x, y} : Finset Point) ⊆ D.line b)
    (hc : ({x, y} : Finset Point) ⊆ D.line c) : b = c := by
  have hpair : ({x, y} : Finset Point) ∈
      (Finset.univ : Finset Point).powersetCard 2 := by
    simp [hxy]
  obtain ⟨d, hd, huniq⟩ := D.pair_unique {x, y} hpair
  exact (huniq b hb).trans (huniq c hc).symm

theorem SevenSteinerDesign.blocks_ne_of_four_members
    {Point Block : Type*} [Fintype Point] [DecidableEq Point]
    [Fintype Block] [DecidableEq Block]
    (D : SevenSteinerDesign Point Block)
    {b c : Block} {w x y z : Point}
    (hcard : ({w, x, y, z} : Finset Point).card = 4)
    (hw : w ∈ D.line b) (hx : x ∈ D.line b)
    (hy : y ∈ D.line c) (hz : z ∈ D.line c) : b ≠ c := by
  intro hbc
  have hsub : ({w, x, y, z} : Finset Point) ⊆ D.line b := by
    intro q hq
    simp only [Finset.mem_insert, Finset.mem_singleton] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact hw
    · exact hx
    · simpa [hbc] using hy
    · simpa [hbc] using hz
  have hle := Finset.card_le_card hsub
  rw [hcard, D.line_card] at hle
  omega

theorem fano_pair_subset_of_mem
    {α : Type*} [DecidableEq α] {x y : α} {S : Finset α}
    (hx : x ∈ S) (hy : y ∈ S) : ({x, y} : Finset α) ⊆ S := by
  intro z hz
  simp only [Finset.mem_insert, Finset.mem_singleton] at hz
  rcases hz with rfl | rfl
  · exact hx
  · exact hy

theorem fano_not_mem_triple_of_ne
    {α : Type*} [DecidableEq α] {x a b c : α}
    (ha : x ≠ a) (hb : x ≠ b) (hc : x ≠ c) :
    x ∉ ({a, b, c} : Finset α) := by
  intro hx
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with h | h | h
  · exact ha h
  · exact hb h
  · exact hc h

set_option maxHeartbeats 200000 in
theorem SevenSteinerDesign.exists_canonical_labeling
    {Point Block : Type*} [Fintype Point] [DecidableEq Point]
    [Fintype Block] [DecidableEq Block]
    (D : SevenSteinerDesign Point Block) :
    ∃ (P : Fin 7 ≃ Point) (B : Fin 7 ≃ Block),
      ∀ j, D.relabeledLines P B j = fanoCanonicalLine j := by
  classical
  let Bbase : Fin 7 ≃ Block := (Fintype.equivFinOfCardEq D.block_card).symm
  let b₀ : Block := Bbase 0
  obtain ⟨a, b, c, hab, hac, hbc, hline₀⟩ :=
    Finset.card_eq_three.mp (D.line_card b₀)
  have hoexists : ∃ o : Point, o ∉ D.line b₀ := by
    by_contra h
    push Not at h
    have hall : D.line b₀ = (Finset.univ : Finset Point) :=
      Finset.eq_univ_of_forall h
    have hc := D.line_card b₀
    rw [hall, Finset.card_univ, D.point_card] at hc
    omega
  obtain ⟨o, ho⟩ := hoexists
  have hoa : o ≠ a := by
    intro h
    apply ho
    rw [h, hline₀]
    simp
  have hob : o ≠ b := by
    intro h
    apply ho
    rw [h, hline₀]
    simp
  have hoc : o ≠ c := by
    intro h
    apply ho
    rw [h, hline₀]
    simp

  have hpair_oa : ({o, a} : Finset Point) ∈
      (Finset.univ : Finset Point).powersetCard 2 := by simp [hoa]
  obtain ⟨b₂, hb₂pair, hb₂uniq⟩ := D.pair_unique {o, a} hpair_oa
  obtain ⟨d, hdo, hda, hline₂⟩ := exists_third_of_pair_subset_card_three
    (D.line b₂) o a hoa (D.line_card b₂)
    (hb₂pair (by simp)) (hb₂pair (by simp))
  have hpair_ob : ({o, b} : Finset Point) ∈
      (Finset.univ : Finset Point).powersetCard 2 := by simp [hob]
  obtain ⟨b₄, hb₄pair, hb₄uniq⟩ := D.pair_unique {o, b} hpair_ob
  obtain ⟨e, heo, heb, hline₄⟩ := exists_third_of_pair_subset_card_three
    (D.line b₄) o b hob (D.line_card b₄)
    (hb₄pair (by simp)) (hb₄pair (by simp))
  have hpair_oc : ({o, c} : Finset Point) ∈
      (Finset.univ : Finset Point).powersetCard 2 := by simp [hoc]
  obtain ⟨b₅, hb₅pair, hb₅uniq⟩ := D.pair_unique {o, c} hpair_oc
  obtain ⟨f, hfo, hfc, hline₅⟩ := exists_third_of_pair_subset_card_three
    (D.line b₅) o c hoc (D.line_card b₅)
    (hb₅pair (by simp)) (hb₅pair (by simp))

  have hd_ne_b : d ≠ b := by
    intro hdb
    have heq : b₂ = b₀ := D.block_eq_of_pair_subset hab
      (by rw [hline₂, hdb]; simp) (by rw [hline₀]; simp)
    apply ho
    rw [← heq, hline₂]
    simp
  have hd_ne_c : d ≠ c := by
    intro hdc
    have heq : b₂ = b₀ := D.block_eq_of_pair_subset hac
      (by rw [hline₂, hdc]; simp) (by rw [hline₀]; simp)
    apply ho
    rw [← heq, hline₂]
    simp
  have he_ne_a : e ≠ a := by
    intro hea
    have heq : b₄ = b₀ := D.block_eq_of_pair_subset hab
      (fano_pair_subset_of_mem
        (by rw [hline₄]; simp [hea]) (by rw [hline₄]; simp))
      (fano_pair_subset_of_mem
        (by rw [hline₀]; simp) (by rw [hline₀]; simp))
    apply ho
    rw [← heq, hline₄]
    simp
  have he_ne_c : e ≠ c := by
    intro hec
    have heq : b₄ = b₀ := D.block_eq_of_pair_subset hbc
      (by rw [hline₄, hec]; simp) (by rw [hline₀]; simp)
    apply ho
    rw [← heq, hline₄]
    simp
  have hf_ne_a : f ≠ a := by
    intro hfa
    have heq : b₅ = b₀ := D.block_eq_of_pair_subset hac
      (fano_pair_subset_of_mem
        (by rw [hline₅]; simp [hfa]) (by rw [hline₅]; simp))
      (fano_pair_subset_of_mem
        (by rw [hline₀]; simp) (by rw [hline₀]; simp))
    apply ho
    rw [← heq, hline₅]
    simp
  have hf_ne_b : f ≠ b := by
    intro hfb
    have heq : b₅ = b₀ := D.block_eq_of_pair_subset hbc
      (fano_pair_subset_of_mem
        (by rw [hline₅]; simp [hfb]) (by rw [hline₅]; simp))
      (fano_pair_subset_of_mem
        (by rw [hline₀]; simp) (by rw [hline₀]; simp))
    apply ho
    rw [← heq, hline₅]
    simp
  have hd_ne_e : d ≠ e := by
    intro hde
    have heq : b₂ = b₄ := D.block_eq_of_pair_subset hdo
      (fano_pair_subset_of_mem
        (by rw [hline₂]; simp) (by rw [hline₂]; simp))
      (fano_pair_subset_of_mem
        (by rw [hline₄]; simp [hde]) (by rw [hline₄]; simp))
    have ha_mem : a ∈ D.line b₄ := by rw [← heq, hline₂]; simp
    rw [hline₄] at ha_mem
    exact (fano_not_mem_triple_of_ne hoa.symm hab he_ne_a.symm) ha_mem
  have hd_ne_f : d ≠ f := by
    intro hdf
    have heq : b₂ = b₅ := D.block_eq_of_pair_subset hdo
      (fano_pair_subset_of_mem
        (by rw [hline₂]; simp) (by rw [hline₂]; simp))
      (fano_pair_subset_of_mem
        (by rw [hline₅]; simp [hdf]) (by rw [hline₅]; simp))
    have ha_mem : a ∈ D.line b₅ := by rw [← heq, hline₂]; simp
    rw [hline₅] at ha_mem
    exact (fano_not_mem_triple_of_ne hoa.symm hac hf_ne_a.symm) ha_mem
  have he_ne_f : e ≠ f := by
    intro hef
    have heq : b₄ = b₅ := D.block_eq_of_pair_subset heo
      (fano_pair_subset_of_mem
        (by rw [hline₄]; simp) (by rw [hline₄]; simp))
      (fano_pair_subset_of_mem
        (by rw [hline₅]; simp [hef]) (by rw [hline₅]; simp))
    have hb_mem : b ∈ D.line b₅ := by rw [← heq, hline₄]; simp
    rw [hline₅] at hb_mem
    exact (fano_not_mem_triple_of_ne hob.symm hbc hf_ne_b.symm) hb_mem

  have hpoints_nodup : [a, b, c, f, e, d, o].Nodup := by
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil,
      not_false_eq_true, not_or, and_true]
    exact ⟨
      ⟨hab, hac, hf_ne_a.symm, he_ne_a.symm, hda.symm, hoa.symm⟩,
      ⟨hbc, hf_ne_b.symm, heb.symm, hd_ne_b.symm, hob.symm⟩,
      ⟨hfc.symm, he_ne_c.symm, hd_ne_c.symm, hoc.symm⟩,
      ⟨he_ne_f.symm, hd_ne_f.symm, hfo⟩,
      ⟨hd_ne_e.symm, heo⟩,
      ⟨hdo, True.intro, List.nodup_nil⟩⟩
  let g : Fin 7 → Point := fun i => [a, b, c, f, e, d, o].get i
  have hginj : Function.Injective g := by
    simpa [g] using hpoints_nodup.injective_get
  let Pbase : Point ≃ Fin 7 := Fintype.equivFinOfCardEq D.point_card
  have hgsurj : Function.Surjective g := by
    have hcompinj : Function.Injective (Pbase ∘ g) := Pbase.injective.comp hginj
    have hcompsurj := Finite.surjective_of_injective hcompinj
    intro x
    obtain ⟨i, hi⟩ := hcompsurj (Pbase x)
    exact ⟨i, Pbase.injective hi⟩
  let P : Fin 7 ≃ Point := Equiv.ofBijective g ⟨hginj, hgsurj⟩

  have hpair_ae : ({a, e} : Finset Point) ∈
      (Finset.univ : Finset Point).powersetCard 2 := by
    simp [he_ne_a.symm]
  obtain ⟨b₁, hb₁pair, hb₁uniq⟩ := D.pair_unique {a, e} hpair_ae
  have hpair_bd : ({b, d} : Finset Point) ∈
      (Finset.univ : Finset Point).powersetCard 2 := by
    simp [hd_ne_b.symm]
  obtain ⟨b₃, hb₃pair, hb₃uniq⟩ := D.pair_unique {b, d} hpair_bd
  have hpair_cd : ({c, d} : Finset Point) ∈
      (Finset.univ : Finset Point).powersetCard 2 := by
    simp [hd_ne_c.symm]
  obtain ⟨b₆, hb₆pair, hb₆uniq⟩ := D.pair_unique {c, d} hpair_cd

  have hb₀_ne_b₂ : b₀ ≠ b₂ := by
    intro h
    apply ho
    rw [h, hline₂]
    simp
  have hb₀_ne_b₄ : b₀ ≠ b₄ := by
    intro h
    apply ho
    rw [h, hline₄]
    simp
  have hb₀_ne_b₅ : b₀ ≠ b₅ := by
    intro h
    apply ho
    rw [h, hline₅]
    simp
  have hb₂_ne_b₄ : b₂ ≠ b₄ := by
    intro h
    have : a ∈ D.line b₄ := by rw [← h, hline₂]; simp
    rw [hline₄] at this
    exact (fano_not_mem_triple_of_ne hoa.symm hab he_ne_a.symm) this
  have hb₂_ne_b₅ : b₂ ≠ b₅ := by
    intro h
    have : a ∈ D.line b₅ := by rw [← h, hline₂]; simp
    rw [hline₅] at this
    exact (fano_not_mem_triple_of_ne hoa.symm hac hf_ne_a.symm) this
  have hb₄_ne_b₅ : b₄ ≠ b₅ := by
    intro h
    have : b ∈ D.line b₅ := by rw [← h, hline₄]; simp
    rw [hline₅] at this
    exact (fano_not_mem_triple_of_ne hob.symm hbc hf_ne_b.symm) this

  have hb₁_ne_b₀ : b₁ ≠ b₀ := by
    intro h
    have : e ∈ D.line b₀ := by rw [← h]; exact hb₁pair (by simp)
    rw [hline₀] at this
    exact (fano_not_mem_triple_of_ne he_ne_a heb he_ne_c) this
  have hb₁_ne_b₂ : b₁ ≠ b₂ := by
    intro h
    have : e ∈ D.line b₂ := by rw [← h]; exact hb₁pair (by simp)
    rw [hline₂] at this
    exact (fano_not_mem_triple_of_ne heo he_ne_a hd_ne_e.symm) this
  have hb₁_ne_b₄ : b₁ ≠ b₄ := by
    intro h
    have : a ∈ D.line b₄ := by rw [← h]; exact hb₁pair (by simp)
    rw [hline₄] at this
    exact (fano_not_mem_triple_of_ne hoa.symm hab he_ne_a.symm) this
  have hb₁_ne_b₅ : b₁ ≠ b₅ := by
    intro h
    have : a ∈ D.line b₅ := by rw [← h]; exact hb₁pair (by simp)
    rw [hline₅] at this
    exact (fano_not_mem_triple_of_ne hoa.symm hac hf_ne_a.symm) this
  have hb₃_ne_b₀ : b₃ ≠ b₀ := by
    intro h
    have : d ∈ D.line b₀ := by rw [← h]; exact hb₃pair (by simp)
    rw [hline₀] at this
    exact (fano_not_mem_triple_of_ne hda hd_ne_b hd_ne_c) this
  have hb₃_ne_b₂ : b₃ ≠ b₂ := by
    intro h
    have : b ∈ D.line b₂ := by rw [← h]; exact hb₃pair (by simp)
    rw [hline₂] at this
    exact (fano_not_mem_triple_of_ne hob.symm hab.symm hd_ne_b.symm) this
  have hb₃_ne_b₄ : b₃ ≠ b₄ := by
    intro h
    have : d ∈ D.line b₄ := by rw [← h]; exact hb₃pair (by simp)
    rw [hline₄] at this
    exact (fano_not_mem_triple_of_ne hdo hd_ne_b hd_ne_e) this
  have hb₃_ne_b₅ : b₃ ≠ b₅ := by
    intro h
    have : b ∈ D.line b₅ := by rw [← h]; exact hb₃pair (by simp)
    rw [hline₅] at this
    exact (fano_not_mem_triple_of_ne hob.symm hbc hf_ne_b.symm) this
  have hb₆_ne_b₀ : b₆ ≠ b₀ := by
    intro h
    have : d ∈ D.line b₀ := by rw [← h]; exact hb₆pair (by simp)
    rw [hline₀] at this
    exact (fano_not_mem_triple_of_ne hda hd_ne_b hd_ne_c) this
  have hb₆_ne_b₂ : b₆ ≠ b₂ := by
    intro h
    have : c ∈ D.line b₂ := by rw [← h]; exact hb₆pair (by simp)
    rw [hline₂] at this
    exact (fano_not_mem_triple_of_ne hoc.symm hac.symm hd_ne_c.symm) this
  have hb₆_ne_b₄ : b₆ ≠ b₄ := by
    intro h
    have : c ∈ D.line b₄ := by rw [← h]; exact hb₆pair (by simp)
    rw [hline₄] at this
    exact (fano_not_mem_triple_of_ne hoc.symm hbc.symm he_ne_c.symm) this
  have hb₆_ne_b₅ : b₆ ≠ b₅ := by
    intro h
    have : d ∈ D.line b₅ := by rw [← h]; exact hb₆pair (by simp)
    rw [hline₅] at this
    exact (fano_not_mem_triple_of_ne hdo hd_ne_c hd_ne_f) this
  have hb₁_ne_b₃ : b₁ ≠ b₃ := by
    intro h
    have hb_mem : b ∈ D.line b₁ := by
      rw [h]
      exact hb₃pair (by simp)
    have heq : b₁ = b₀ := D.block_eq_of_pair_subset hab
      (fano_pair_subset_of_mem (hb₁pair (by simp)) hb_mem)
      (fano_pair_subset_of_mem
        (by rw [hline₀]; simp) (by rw [hline₀]; simp))
    have he_mem : e ∈ D.line b₀ := by
      rw [← heq]
      exact hb₁pair (by simp)
    rw [hline₀] at he_mem
    exact (fano_not_mem_triple_of_ne he_ne_a heb he_ne_c) he_mem
  have hb₁_ne_b₆ : b₁ ≠ b₆ := by
    intro h
    have hc_mem : c ∈ D.line b₁ := by
      rw [h]
      exact hb₆pair (by simp)
    have heq : b₁ = b₀ := D.block_eq_of_pair_subset hac
      (fano_pair_subset_of_mem (hb₁pair (by simp)) hc_mem)
      (fano_pair_subset_of_mem
        (by rw [hline₀]; simp) (by rw [hline₀]; simp))
    have he_mem : e ∈ D.line b₀ := by
      rw [← heq]
      exact hb₁pair (by simp)
    rw [hline₀] at he_mem
    exact (fano_not_mem_triple_of_ne he_ne_a heb he_ne_c) he_mem
  have hb₃_ne_b₆ : b₃ ≠ b₆ := by
    intro h
    have hb_mem : b ∈ D.line b₆ := by
      rw [← h]
      exact hb₃pair (by simp)
    have heq : b₆ = b₀ := D.block_eq_of_pair_subset hbc
      (by
        intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl
        · exact hb_mem
        · exact hb₆pair (by simp))
      (by rw [hline₀]; simp)
    have hd_mem : d ∈ D.line b₀ := by
      rw [← heq]
      exact hb₆pair (by simp)
    rw [hline₀] at hd_mem
    exact (fano_not_mem_triple_of_ne hda hd_ne_b hd_ne_c) hd_mem

  have hblocks_nodup : [b₀, b₁, b₂, b₃, b₄, b₅, b₆].Nodup := by
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil,
      not_false_eq_true, not_or, and_true]
    exact ⟨
      ⟨hb₁_ne_b₀.symm, hb₀_ne_b₂, hb₃_ne_b₀.symm,
        hb₀_ne_b₄, hb₀_ne_b₅, hb₆_ne_b₀.symm⟩,
      ⟨hb₁_ne_b₂, hb₁_ne_b₃, hb₁_ne_b₄, hb₁_ne_b₅, hb₁_ne_b₆⟩,
      ⟨hb₃_ne_b₂.symm, hb₂_ne_b₄, hb₂_ne_b₅, hb₆_ne_b₂.symm⟩,
      ⟨hb₃_ne_b₄, hb₃_ne_b₅, hb₃_ne_b₆⟩,
      ⟨hb₄_ne_b₅, hb₆_ne_b₄.symm⟩,
      ⟨hb₆_ne_b₅.symm, True.intro, List.nodup_nil⟩⟩
  let q : Fin 7 → Block := fun i => [b₀, b₁, b₂, b₃, b₄, b₅, b₆].get i
  have hqinj : Function.Injective q := by
    simpa [q] using hblocks_nodup.injective_get
  let Qbase : Block ≃ Fin 7 := Fintype.equivFinOfCardEq D.block_card
  have hqsurj : Function.Surjective q := by
    have hcompinj : Function.Injective (Qbase ∘ q) := Qbase.injective.comp hqinj
    have hcompsurj := Finite.surjective_of_injective hcompinj
    intro y
    obtain ⟨i, hi⟩ := hcompsurj (Qbase y)
    exact ⟨i, Qbase.injective hi⟩
  let B : Fin 7 ≃ Block := Equiv.ofBijective q ⟨hqinj, hqsurj⟩
  refine ⟨P, B, D.canonical_of_normalized P B ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · ext i
    fin_cases i <;> simp [SevenSteinerDesign.relabeledLines, P, B, g, q, hline₀,
      hf_ne_a, hf_ne_b, hfc, he_ne_a, heb, he_ne_c,
      hda, hd_ne_b, hd_ne_c, hoa, hob, hoc]
  · ext i
    fin_cases i <;> simp [SevenSteinerDesign.relabeledLines, P, B, g, q, hline₂,
      hob.symm, hab.symm, hd_ne_b.symm, hoc.symm, hac.symm, hd_ne_c.symm,
      hfo, hf_ne_a, hd_ne_f.symm, heo, he_ne_a, hd_ne_e.symm]
  · ext i
    fin_cases i <;> simp [SevenSteinerDesign.relabeledLines, P, B, g, q, hline₄,
      hoa.symm, hab, he_ne_a.symm, hoc.symm, hbc.symm, he_ne_c.symm,
      hfo, hf_ne_b, he_ne_f.symm, hdo, hd_ne_b, hd_ne_e]
  · ext i
    fin_cases i <;> simp [SevenSteinerDesign.relabeledLines, P, B, g, q, hline₅,
      hoa.symm, hac, hf_ne_a.symm, hob.symm, hbc, hf_ne_b.symm,
      heo, he_ne_c, he_ne_f, hdo, hd_ne_c, hd_ne_f]
  · exact (D.mem_relabeledLines P B 0 1).mpr (by
      change a ∈ D.line b₁
      exact hb₁pair (by simp))
  · exact (D.mem_relabeledLines P B 4 1).mpr (by
      change e ∈ D.line b₁
      exact hb₁pair (by simp))
  · exact (D.mem_relabeledLines P B 1 3).mpr (by
      change b ∈ D.line b₃
      exact hb₃pair (by simp))
  · exact (D.mem_relabeledLines P B 5 3).mpr (by
      change d ∈ D.line b₃
      exact hb₃pair (by simp))
  · exact (D.mem_relabeledLines P B 2 6).mpr (by
      change c ∈ D.line b₆
      exact hb₆pair (by simp))
  · exact (D.mem_relabeledLines P B 5 6).mpr (by
      change d ∈ D.line b₆
      exact hb₆pair (by simp))

end Erdos506.Finite
