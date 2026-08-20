import Mathlib.Data.Fintype.Powerset
import Erdos506.Finite.KFiveNearOneFactorizationOrbit

/-!
# Relabelling near-one-factorizations of `K5`

An abstract `KFiveNearOneFactorization` already identifies each colour with
the vertex omitted by its factor.  Consequently a labelling of the vertices
by `Fin 5` also labels the colours; no independent colour labelling or
compatibility hypothesis is needed.

This module transports an abstract factorization to a checked finite code
and then normalizes that code while fixing vertex zero.
-/

namespace Erdos506.Finite

/-! ## Chords transported by a vertex labelling -/

private noncomputable def finFiveSubsetEquivOfVertexLabel
    {α : Type*} [DecidableEq α] {A : Finset α}
    (v : Fin 5 ≃ ↥A) :
    Finset (Fin 5) ≃ {s : Finset α // s ⊆ A} :=
  v.finsetCongr.trans
    (Equiv.finsetSubtypeComm fun x : α => x ∈ A)

@[simp] private theorem finFiveSubsetEquivOfVertexLabel_card
    {α : Type*} [DecidableEq α] {A : Finset α}
    (v : Fin 5 ≃ ↥A) (s : Finset (Fin 5)) :
    ((finFiveSubsetEquivOfVertexLabel v s).1).card = s.card := by
  simp [finFiveSubsetEquivOfVertexLabel, Equiv.finsetSubtypeComm]

/-- Transport unordered pairs from the labelled five-set to an arbitrary
five-set. -/
noncomputable def kFiveChordEquivOfVertexLabel
    {α : Type*} [DecidableEq α] {A : Finset α}
    (v : Fin 5 ≃ ↥A) :
    FinFiveChord ≃ KFiveChord A where
  toFun e :=
    ⟨(finFiveSubsetEquivOfVertexLabel v e.1).1, by
      rw [Finset.mem_powersetCard]
      refine ⟨(finFiveSubsetEquivOfVertexLabel v e.1).2, ?_⟩
      rw [finFiveSubsetEquivOfVertexLabel_card]
      exact (Finset.mem_powersetCard.mp e.2).2⟩
  invFun e := by
    let t : {s : Finset α // s ⊆ A} :=
      ⟨e.1, (Finset.mem_powersetCard.mp e.2).1⟩
    let s := (finFiveSubsetEquivOfVertexLabel v).symm t
    refine ⟨s, ?_⟩
    rw [Finset.mem_powersetCard]
    refine ⟨Finset.subset_univ _, ?_⟩
    have hcard := finFiveSubsetEquivOfVertexLabel_card v s
    have happly :=
      (finFiveSubsetEquivOfVertexLabel v).apply_symm_apply t
    have htcard :
        ((finFiveSubsetEquivOfVertexLabel v s).1).card = e.1.card := by
      exact congrArg (fun r : {s : Finset α // s ⊆ A} => r.1.card)
        happly
    rw [htcard] at hcard
    exact hcard.symm.trans (Finset.mem_powersetCard.mp e.2).2
  left_inv e := by
    apply Subtype.ext
    exact (finFiveSubsetEquivOfVertexLabel v).symm_apply_apply e.1
  right_inv e := by
    apply Subtype.ext
    let t : {s : Finset α // s ⊆ A} :=
      ⟨e.1, (Finset.mem_powersetCard.mp e.2).1⟩
    change (finFiveSubsetEquivOfVertexLabel v
      ((finFiveSubsetEquivOfVertexLabel v).symm t)).1 = t.1
    exact congrArg Subtype.val
      ((finFiveSubsetEquivOfVertexLabel v).apply_symm_apply t)

@[simp] theorem mem_kFiveChordEquivOfVertexLabel
    {α : Type*} [DecidableEq α] {A : Finset α}
    (v : Fin 5 ≃ ↥A) (e : FinFiveChord) (i : Fin 5) :
    (v i).1 ∈ (kFiveChordEquivOfVertexLabel v e).1 ↔ i ∈ e.1 := by
  simp [kFiveChordEquivOfVertexLabel,
    finFiveSubsetEquivOfVertexLabel, Equiv.finsetSubtypeComm]

private theorem disjoint_chords_of_transport_disjoint
    {α : Type*} [DecidableEq α] {A : Finset α}
    (v : Fin 5 ≃ ↥A) (e k : FinFiveChord)
    (hdisj : Disjoint
      (kFiveChordEquivOfVertexLabel v e).1
      (kFiveChordEquivOfVertexLabel v k).1) :
    Disjoint e.1 k.1 := by
  rw [Finset.disjoint_left] at hdisj ⊢
  intro i hie hik
  exact hdisj
    ((mem_kFiveChordEquivOfVertexLabel v e i).2 hie)
    ((mem_kFiveChordEquivOfVertexLabel v k i).2 hik)

/-! ## Pulling an abstract factor family back to `Fin 5` -/

namespace KFiveNearOneFactorization

variable {α Colour : Type*} [DecidableEq α]
  [Fintype Colour] [DecidableEq Colour]
  {A : Finset α}

/-- Relabel the vertices of every factor.  The colour labelled `c` is the
factor which omits the vertex labelled `c`. -/
noncomputable def pullbackFactorFamily
    (F : KFiveNearOneFactorization A Colour)
    (v : Fin 5 ≃ ↥A) :
    Fin 5 → Finset FinFiveChord :=
  fun c =>
    (F.factorAtVertex (v c)).map
      (kFiveChordEquivOfVertexLabel v).symm.toEmbedding

@[simp] theorem mem_pullbackFactorFamily
    (F : KFiveNearOneFactorization A Colour)
    (v : Fin 5 ≃ ↥A) (c : Fin 5) (e : FinFiveChord) :
    e ∈ F.pullbackFactorFamily v c ↔
      kFiveChordEquivOfVertexLabel v e ∈ F.factorAtVertex (v c) := by
  simp [pullbackFactorFamily]

@[simp] theorem pullbackFactorFamily_card_two
    (F : KFiveNearOneFactorization A Colour)
    (v : Fin 5 ≃ ↥A) (c : Fin 5) :
    (F.pullbackFactorFamily v c).card = 2 := by
  rw [pullbackFactorFamily, Finset.card_map]
  exact F.factorAtVertex_card (v c)

theorem pullbackFactorFamily_matching
    (F : KFiveNearOneFactorization A Colour)
    (v : Fin 5 ≃ ↥A) (c : Fin 5)
    (e : FinFiveChord) (he : e ∈ F.pullbackFactorFamily v c)
    (k : FinFiveChord) (hk : k ∈ F.pullbackFactorFamily v c)
    (hek : e ≠ k) :
    Disjoint e.1 k.1 := by
  have he' := (F.mem_pullbackFactorFamily v c e).mp he
  have hk' := (F.mem_pullbackFactorFamily v c k).mp hk
  have hek' : kFiveChordEquivOfVertexLabel v e ≠
      kFiveChordEquivOfVertexLabel v k :=
    (kFiveChordEquivOfVertexLabel v).injective.ne hek
  apply disjoint_chords_of_transport_disjoint v e k
  exact F.factor_matching
    (F.omittedColourEquiv.symm (v c))
      (kFiveChordEquivOfVertexLabel v e) he'
      (kFiveChordEquivOfVertexLabel v k) hk' hek'

theorem pullbackFactorFamily_avoids_colour
    (F : KFiveNearOneFactorization A Colour)
    (v : Fin 5 ≃ ↥A) (c : Fin 5)
    (e : FinFiveChord) (he : e ∈ F.pullbackFactorFamily v c) :
    c ∉ e.1 := by
  intro hce
  have he' := (F.mem_pullbackFactorFamily v c e).mp he
  exact F.factorAtVertex_avoids (v c)
    (kFiveChordEquivOfVertexLabel v e) he'
      ((mem_kFiveChordEquivOfVertexLabel v e c).2 hce)

theorem pullbackFactorFamily_covers_other
    (F : KFiveNearOneFactorization A Colour)
    (v : Fin 5 ≃ ↥A) (c x : Fin 5) (hxc : x ≠ c) :
    ∃ e ∈ F.pullbackFactorFamily v c, x ∈ e.1 := by
  have hvxc : v x ≠ v c := v.injective.ne hxc
  have hvxc' : v x ≠
      F.omittedColourEquiv
        (F.omittedColourEquiv.symm (v c)) := by
    simpa only [Equiv.apply_symm_apply] using hvxc
  obtain ⟨E, hE, hxE⟩ := F.factor_covers_other
    (F.omittedColourEquiv.symm (v c)) (v x) hvxc'
  let e : FinFiveChord := (kFiveChordEquivOfVertexLabel v).symm E
  refine ⟨e, ?_, ?_⟩
  · apply (F.mem_pullbackFactorFamily v c e).mpr
    simpa only [e, Equiv.apply_symm_apply, factorAtVertex] using hE
  · apply (mem_kFiveChordEquivOfVertexLabel v e x).mp
    simpa only [e, Equiv.apply_symm_apply] using hxE

theorem pullbackFactorFamily_chord_unique
    (F : KFiveNearOneFactorization A Colour)
    (v : Fin 5 ≃ ↥A) (e : FinFiveChord) :
    ∃! c : Fin 5, e ∈ F.pullbackFactorFamily v c := by
  obtain ⟨q, hq, hqUnique⟩ :=
    F.chord_unique (kFiveChordEquivOfVertexLabel v e)
  let c : Fin 5 := v.symm (F.omittedColourEquiv q)
  refine ⟨c, ?_, ?_⟩
  · apply (F.mem_pullbackFactorFamily v c e).mpr
    simpa only [c, factorAtVertex, Equiv.apply_symm_apply,
      Equiv.symm_apply_apply] using hq
  · intro d hd
    have hd' := (F.mem_pullbackFactorFamily v d e).mp hd
    have hcolour : F.omittedColourEquiv.symm (v d) = q :=
      hqUnique _ hd'
    apply v.injective
    rw [show v c = F.omittedColourEquiv q by
      simp only [c, Equiv.apply_symm_apply]]
    simpa only [Equiv.apply_symm_apply] using
      congrArg F.omittedColourEquiv hcolour

end KFiveNearOneFactorization

/-! ## From a pulled-back family to a checked code -/

private def RowMatchingExpanded (R : Finset FinFiveChord) : Prop :=
  ∀ e, e ∈ R → ∀ k, k ∈ R → e ≠ k →
    ∀ a : Fin 5, a ∈ e.1 → a ∉ k.1

private instance (R : Finset FinFiveChord) :
    Decidable (RowMatchingExpanded R) :=
  inferInstanceAs (Decidable (
    ∀ e : FinFiveChord, e ∈ R → ∀ k : FinFiveChord, k ∈ R → e ≠ k →
      ∀ a : Fin 5, a ∈ e.1 → a ∉ k.1))

private def RowAvoids (c : Fin 5) (R : Finset FinFiveChord) : Prop :=
  ∀ e, e ∈ R → c ∉ e.1

private instance (c : Fin 5) (R : Finset FinFiveChord) :
    Decidable (RowAvoids c R) :=
  inferInstanceAs (Decidable (
    ∀ e : FinFiveChord, e ∈ R → c ∉ e.1))

private def RowCovers (c : Fin 5) (R : Finset FinFiveChord) : Prop :=
  ∀ x, x ≠ c → ∃ e ∈ R, x ∈ e.1

private instance (c : Fin 5) (R : Finset FinFiveChord) :
    Decidable (RowCovers c R) :=
  inferInstanceAs (Decidable (
    ∀ x : Fin 5, x ≠ c → ∃ e : FinFiveChord, e ∈ R ∧ x ∈ e.1))

private def RowUniqueExpanded (c : Fin 5) (R : Finset FinFiveChord) : Prop :=
  ∃ r : Fin 3, R = kFiveRowOptions c r ∧
    ∀ y : Fin 3, R = kFiveRowOptions c y → y = r

private instance (c : Fin 5) (R : Finset FinFiveChord) :
    Decidable (RowUniqueExpanded c R) :=
  inferInstanceAs (Decidable (
    ∃ r : Fin 3, R = kFiveRowOptions c r ∧
      ∀ y : Fin 3, R = kFiveRowOptions c y → y = r))

private def FinFiveMatchingRowPredicate
    (c : Fin 5) (R : Finset FinFiveChord) : Prop :=
  R.card = 2 →
    (∀ e, e ∈ R → ∀ k, k ∈ R → e ≠ k → Disjoint e.1 k.1) →
    (∀ e, e ∈ R → c ∉ e.1) →
    (∀ x, x ≠ c → ∃ e ∈ R, x ∈ e.1) →
    ∃! r : Fin 3, R = kFiveRowOptions c r

private instance (c : Fin 5) (R : Finset FinFiveChord) :
    Decidable (FinFiveMatchingRowPredicate c R) :=
  decidable_of_decidable_of_iff
    (p := R.card = 2 → RowMatchingExpanded R → RowAvoids c R →
      RowCovers c R → RowUniqueExpanded c R)
    (by
      simp only [FinFiveMatchingRowPredicate, RowMatchingExpanded, RowAvoids,
        RowCovers, RowUniqueExpanded, Finset.disjoint_left, ExistsUnique])

/-- A closed finite certificate: every two-edge matching on the four
vertices other than `c` is exactly one of the three stored row options. -/
theorem finFive_matchingRow_eq_rowOption :
    ∀ (c : Fin 5) (R : Finset FinFiveChord),
      R.card = 2 →
      (∀ e, e ∈ R → ∀ k, k ∈ R → e ≠ k → Disjoint e.1 k.1) →
      (∀ e, e ∈ R → c ∉ e.1) →
      (∀ x, x ≠ c → ∃ e ∈ R, x ∈ e.1) →
      ∃! r : Fin 3, R = kFiveRowOptions c r := by
  change ∀ c R, FinFiveMatchingRowPredicate c R
  decide +kernel

namespace KFiveNearOneFactorization

variable {α Colour : Type*} [DecidableEq α]
  [Fintype Colour] [DecidableEq Colour]
  {A : Finset α}

private theorem pullbackFactorFamily_exists_unique_row
    (F : KFiveNearOneFactorization A Colour)
    (v : Fin 5 ≃ ↥A) (c : Fin 5) :
    ∃! r : Fin 3,
      F.pullbackFactorFamily v c = kFiveRowOptions c r := by
  apply finFive_matchingRow_eq_rowOption
  · exact F.pullbackFactorFamily_card_two v c
  · intro e he k hk hek
    exact F.pullbackFactorFamily_matching v c e he k hk hek
  · intro e he
    exact F.pullbackFactorFamily_avoids_colour v c e he
  · intro x hxc
    exact F.pullbackFactorFamily_covers_other v c x hxc

private noncomputable def rowChoiceAlong
    (F : KFiveNearOneFactorization A Colour)
    (v : Fin 5 ≃ ↥A) (c : Fin 5) : Fin 3 :=
  Classical.choose (F.pullbackFactorFamily_exists_unique_row v c)

private theorem pullbackFactorFamily_eq_rowChoiceAlong
    (F : KFiveNearOneFactorization A Colour)
    (v : Fin 5 ≃ ↥A) (c : Fin 5) :
    F.pullbackFactorFamily v c =
      kFiveRowOptions c (rowChoiceAlong F v c) :=
  (Classical.choose_spec
    (F.pullbackFactorFamily_exists_unique_row v c)).1

/-- Encode an abstract near-one-factorization after labelling its vertices.
The colour labels are induced by the omitted-colour equivalence. -/
noncomputable def toCodeAlong
    (F : KFiveNearOneFactorization A Colour)
    (v : Fin 5 ≃ ↥A) : KFiveNearOneFactorizationCode where
  rowChoice := rowChoiceAlong F v
  valid := by
    intro e
    have hunique := F.pullbackFactorFamily_chord_unique v e
    change ∃! c : Fin 5,
      e ∈ kFiveRowOptions c (rowChoiceAlong F v c)
    simpa only [pullbackFactorFamily_eq_rowChoiceAlong] using hunique

@[simp] theorem toCodeAlong_factor
    (F : KFiveNearOneFactorization A Colour)
    (v : Fin 5 ≃ ↥A) (c : Fin 5) :
    kFiveCodedFactor (F.toCodeAlong v).rowChoice c =
      F.pullbackFactorFamily v c := by
  change kFiveRowOptions c (rowChoiceAlong F v c) =
    F.pullbackFactorFamily v c
  exact (F.pullbackFactorFamily_eq_rowChoiceAlong v c).symm

end KFiveNearOneFactorization

/-! ## Normalizing a checked table while fixing vertex zero -/

private def kFiveCanonicalNormalizer0 : Equiv.Perm (Fin 5) where
  toFun := (![0, 1, 3, 4, 2] : Fin 5 → Fin 5)
  invFun := (![0, 1, 4, 2, 3] : Fin 5 → Fin 5)
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def kFiveCanonicalNormalizer1 : Equiv.Perm (Fin 5) where
  toFun := (![0, 1, 3, 2, 4] : Fin 5 → Fin 5)
  invFun := (![0, 1, 3, 2, 4] : Fin 5 → Fin 5)
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def kFiveCanonicalNormalizer2 : Equiv.Perm (Fin 5) where
  toFun := (![0, 1, 4, 3, 2] : Fin 5 → Fin 5)
  invFun := (![0, 1, 4, 3, 2] : Fin 5 → Fin 5)
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def kFiveCanonicalNormalizer4 : Equiv.Perm (Fin 5) where
  toFun := (![0, 1, 4, 2, 3] : Fin 5 → Fin 5)
  invFun := (![0, 1, 3, 4, 2] : Fin 5 → Fin 5)
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def kFiveCanonicalNormalizer5 : Equiv.Perm (Fin 5) where
  toFun := (![0, 1, 2, 4, 3] : Fin 5 → Fin 5)
  invFun := (![0, 1, 2, 4, 3] : Fin 5 → Fin 5)
  left_inv := by decide +kernel
  right_inv := by decide +kernel

/-- A zero-fixing permutation which sends each of the six checked tables to
the canonical table. -/
def kFiveCanonicalNormalizer : Fin 6 → Equiv.Perm (Fin 5) := ![
  kFiveCanonicalNormalizer0,
  kFiveCanonicalNormalizer1,
  kFiveCanonicalNormalizer2,
  Equiv.refl (Fin 5),
  kFiveCanonicalNormalizer4,
  kFiveCanonicalNormalizer5
]

theorem kFiveCanonicalNormalizer_fixes_zero :
    ∀ i : Fin 6, kFiveCanonicalNormalizer i 0 = 0 := by
  decide +kernel

theorem kFiveCanonicalNormalizer_sends_table_to_canonical :
    ∀ i : Fin 6,
      kFivePermuteFactorFamily (kFiveCanonicalNormalizer i)
        (kFiveCodedFactor (kFiveNearOneFactorizationTable i)) =
        kFiveCanonicalFactorFamily := by
  decide +kernel

/-- Every checked table can be normalized by a permutation fixing vertex
zero. -/
theorem kFiveNearOneFactorizationCode_normalize_fixing_zero
    (C : KFiveNearOneFactorizationCode) :
    ∃ σ : Equiv.Perm (Fin 5),
      σ 0 = 0 ∧
      kFivePermuteFactorFamily σ
          (kFiveCodedFactor C.rowChoice) =
        kFiveCanonicalFactorFamily := by
  obtain ⟨i, hi⟩ :=
    (kFiveNearOneFactorizationCode_complete C.rowChoice).mp C.valid
  refine ⟨kFiveCanonicalNormalizer i,
    kFiveCanonicalNormalizer_fixes_zero i, ?_⟩
  rw [hi]
  exact kFiveCanonicalNormalizer_sends_table_to_canonical i

/-! ## Naturality and canonical vertex labellings -/

@[simp] theorem kFivePermuteChordEquiv_symm
    (σ : Equiv.Perm (Fin 5)) :
    (kFivePermuteChordEquiv σ).symm =
      kFivePermuteChordEquiv σ.symm := by
  apply Equiv.ext
  intro e
  apply Subtype.ext
  rfl

theorem kFiveChordEquivOfVertexLabel_trans_perm
    {α : Type*} [DecidableEq α] {A : Finset α}
    (σ : Equiv.Perm (Fin 5)) (v : Fin 5 ≃ ↥A)
    (e : FinFiveChord) :
    kFiveChordEquivOfVertexLabel (σ.trans v) e =
      kFiveChordEquivOfVertexLabel v
        (kFivePermuteChordEquiv σ e) := by
  apply Subtype.ext
  ext x
  simp [kFiveChordEquivOfVertexLabel,
    finFiveSubsetEquivOfVertexLabel, Equiv.finsetSubtypeComm,
    kFivePermuteChordEquiv, Finset.map_map]

namespace KFiveNearOneFactorization

variable {α Colour : Type*} [DecidableEq α]
  [Fintype Colour] [DecidableEq Colour]
  {A : Finset α}

/-- Pullback commutes with simultaneously permuting vertex and omitted-colour
labels.  The inverse in the new vertex labelling matches the convention in
`kFivePermuteFactorFamily`. -/
theorem pullbackFactorFamily_relabel
    (F : KFiveNearOneFactorization A Colour)
    (v : Fin 5 ≃ ↥A) (σ : Equiv.Perm (Fin 5)) :
    F.pullbackFactorFamily (σ.symm.trans v) =
      kFivePermuteFactorFamily σ (F.pullbackFactorFamily v) := by
  funext c
  ext e
  simp only [mem_pullbackFactorFamily, kFivePermuteFactorFamily,
    Finset.mem_map_equiv, Equiv.trans_apply]
  rw [kFivePermuteChordEquiv_symm,
    kFiveChordEquivOfVertexLabel_trans_perm]

/-- After any initial vertex labelling, the factorization admits a canonical
labelling which keeps the vertex initially labelled zero fixed. -/
theorem exists_canonical_vertexLabel
    (F : KFiveNearOneFactorization A Colour)
    (v : Fin 5 ≃ ↥A) :
    ∃ v' : Fin 5 ≃ ↥A,
      v' 0 = v 0 ∧
      F.pullbackFactorFamily v' = kFiveCanonicalFactorFamily := by
  obtain ⟨σ, hσzero, hσ⟩ :=
    kFiveNearOneFactorizationCode_normalize_fixing_zero
      (F.toCodeAlong v)
  have hσsymm : σ.symm 0 = 0 := by
    apply σ.injective
    simpa only [Equiv.apply_symm_apply] using hσzero.symm
  let v' : Fin 5 ≃ ↥A := σ.symm.trans v
  refine ⟨v', ?_, ?_⟩
  · simp only [v', Equiv.trans_apply, hσsymm]
  · have hfamily :
        kFiveCodedFactor (F.toCodeAlong v).rowChoice =
          F.pullbackFactorFamily v := by
      funext c
      exact F.toCodeAlong_factor v c
    change F.pullbackFactorFamily (σ.symm.trans v) =
      kFiveCanonicalFactorFamily
    rw [F.pullbackFactorFamily_relabel v σ, ← hfamily]
    exact hσ

/-- A data-valued canonical vertex labelling.  Unlike the existential
wrapper above, this definition can be used inside downstream structures:
the finite code equivalence chooses its table index and the explicit
zero-fixing normalizer supplies the relabelling. -/
noncomputable def canonicalVertexLabel
    (F : KFiveNearOneFactorization A Colour)
    (v : Fin 5 ≃ ↑A) : Fin 5 ≃ ↑A :=
  let C := F.toCodeAlong v
  let i := kFiveNearOneFactorizationCodeEquiv.symm C
  (kFiveCanonicalNormalizer i).symm.trans v

@[simp] theorem canonicalVertexLabel_zero
    (F : KFiveNearOneFactorization A Colour)
    (v : Fin 5 ≃ ↑A) :
    F.canonicalVertexLabel v 0 = v 0 := by
  let C := F.toCodeAlong v
  let i := kFiveNearOneFactorizationCodeEquiv.symm C
  let σ := kFiveCanonicalNormalizer i
  have hσzero : σ 0 = 0 :=
    kFiveCanonicalNormalizer_fixes_zero i
  have hσsymm : σ.symm 0 = 0 := by
    apply σ.injective
    simpa only [Equiv.apply_symm_apply] using hσzero.symm
  simp only [canonicalVertexLabel, C, i, σ, Equiv.trans_apply,
    hσsymm]

@[simp] theorem canonicalVertexLabel_factorFamily
    (F : KFiveNearOneFactorization A Colour)
    (v : Fin 5 ≃ ↑A) :
    F.pullbackFactorFamily (F.canonicalVertexLabel v) =
      kFiveCanonicalFactorFamily := by
  let C := F.toCodeAlong v
  let i := kFiveNearOneFactorizationCodeEquiv.symm C
  let σ := kFiveCanonicalNormalizer i
  have hindex :
      kFiveNearOneFactorizationTable i = C.rowChoice := by
    have happly := kFiveNearOneFactorizationCodeEquiv.apply_symm_apply C
    exact congrArg KFiveNearOneFactorizationCode.rowChoice happly
  have hfamily : kFiveCodedFactor C.rowChoice =
      F.pullbackFactorFamily v := by
    funext c
    exact F.toCodeAlong_factor v c
  change F.pullbackFactorFamily (σ.symm.trans v) =
    kFiveCanonicalFactorFamily
  rw [F.pullbackFactorFamily_relabel v σ, ← hfamily, ← hindex]
  exact kFiveCanonicalNormalizer_sends_table_to_canonical i

end KFiveNearOneFactorization

/-- Label a five-set so that a prescribed vertex receives label zero. -/
theorem finFiveVertexLabel_fixed_zero
    {α : Type*} [DecidableEq α] {A : Finset α}
    (hA : A.card = 5) (a : ↥A) :
    ∃ v : Fin 5 ≃ ↥A, v 0 = a := by
  let base : Fin 5 ≃ ↥A := (Finset.equivFinOfCardEq hA).symm
  let σ : Equiv.Perm (Fin 5) := Equiv.swap 0 (base.symm a)
  refine ⟨σ.trans base, ?_⟩
  simp only [Equiv.trans_apply, σ, Equiv.swap_apply_left,
    Equiv.apply_symm_apply]

/-- The data-valued version of `finFiveVertexLabel_fixed_zero`, suitable
for definitions which must return an equivalence rather than merely prove
that one exists. -/
noncomputable def finFiveVertexLabelWithZero
    {α : Type*} [DecidableEq α] {A : Finset α}
    (hA : A.card = 5) (a : ↑A) : Fin 5 ≃ ↑A :=
  let base : Fin 5 ≃ ↑A := (Finset.equivFinOfCardEq hA).symm
  (Equiv.swap 0 (base.symm a)).trans base

@[simp] theorem finFiveVertexLabelWithZero_apply_zero
    {α : Type*} [DecidableEq α] {A : Finset α}
    (hA : A.card = 5) (a : ↑A) :
    finFiveVertexLabelWithZero hA a 0 = a := by
  simp only [finFiveVertexLabelWithZero, Equiv.trans_apply,
    Equiv.swap_apply_left, Equiv.apply_symm_apply]

end Erdos506.Finite
