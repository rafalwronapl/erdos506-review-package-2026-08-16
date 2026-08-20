import Erdos506.Finite.KFiveNearOneFactorization

/-!
# Constructing a `K5` near-one-factorization from a partition

This module is independent of incidence geometry.  A partition of the ten
chords of a five-set into five disjoint two-edge matchings determines, for
each factor, its unique omitted vertex.  Double-counting the four chords
through every vertex shows that these omitted vertices give an equivalence
between factors and vertices.
-/

namespace Erdos506.Finite

private structure KFiveFactorOmission
    {β : Type*} [DecidableEq β]
    (A : Finset β) (F : Finset (KFiveChord A)) where
  vertex : ↥A
  avoids : ∀ e, e ∈ F → vertex.1 ∉ e.1
  covers : ∀ v : ↥A, v ≠ vertex → ∃ e ∈ F, v.1 ∈ e.1

private noncomputable def kFiveFactorOmission
    {β : Type*} [DecidableEq β]
    (A : Finset β) (hA : A.card = 5)
    (F : Finset (KFiveChord A)) (hF : F.card = 2)
    (hmatching : ∀ e, e ∈ F → ∀ k, k ∈ F →
      e ≠ k → Disjoint e.1 k.1) :
    KFiveFactorOmission A F := by
  classical
  let U := F.biUnion fun e => e.1
  have hUsub : U ⊆ A := by
    intro x hx
    obtain ⟨e, heF, hxe⟩ := Finset.mem_biUnion.mp hx
    exact (Finset.mem_powersetCard.mp e.2).1 hxe
  have hpairwise :
      (F : Set (KFiveChord A)).PairwiseDisjoint fun e => e.1 := by
    intro e he k hk hek
    exact hmatching e he k hk hek
  have hUcard : U.card = 4 := by
    change (F.biUnion fun e => e.1).card = 4
    rw [Finset.card_biUnion hpairwise]
    calc
      (∑ e ∈ F, e.1.card) = ∑ _e ∈ F, 2 := by
        apply Finset.sum_congr rfl
        intro e _he
        exact (Finset.mem_powersetCard.mp e.2).2
      _ = 4 := by simp [hF]
  have hdiffCard : (A \ U).card = 1 := by
    rw [Finset.card_sdiff_of_subset hUsub, hA, hUcard]
  have hdiffPos : 0 < (A \ U).card := by omega
  have hdiffNonempty : Nonempty ↥(A \ U) := by
    rw [← Fintype.card_pos_iff, Fintype.card_coe]
    exact hdiffPos
  let x : ↥(A \ U) := Classical.choice hdiffNonempty
  have hxDiff : x.1 ∈ A \ U := x.2
  have hxA : x.1 ∈ A := (Finset.mem_sdiff.mp hxDiff).1
  refine
    { vertex := ⟨x.1, hxA⟩
      avoids := ?_
      covers := ?_ }
  · intro e heF hxe
    exact (Finset.mem_sdiff.mp hxDiff).2
      (Finset.mem_biUnion.mpr ⟨e, heF, hxe⟩)
  · intro v hv
    have hvU : v.1 ∈ U := by
      by_contra hvU
      have hvDiff : v.1 ∈ A \ U :=
        Finset.mem_sdiff.mpr ⟨v.2, hvU⟩
      have hdiffLe : (A \ U).card ≤ 1 := by omega
      have hvx : v.1 = x.1 :=
        Finset.card_le_one_iff.mp hdiffLe hvDiff x.2
      apply hv
      exact Subtype.ext hvx
    exact Finset.mem_biUnion.mp hvU

private theorem card_incident_kFiveChords_eq_four
    {β : Type*} [DecidableEq β]
    (A : Finset β) (hA : A.card = 5) (v : ↥A) :
    ((Finset.univ : Finset (KFiveChord A)).filter
      fun e => v.1 ∈ e.1).card = 4 := by
  classical
  have hattach :
      ((Finset.univ : Finset (KFiveChord A)).filter
        fun e => v.1 ∈ e.1).card =
      ((A.powersetCard 2).filter fun e => v.1 ∈ e).card := by
    rw [Finset.univ_eq_attach, Finset.filter_attach']
    simp only [Finset.card_map, Finset.card_attach]
    congr 1
    ext e
    simp
  rw [hattach]
  have hvsub : ({v.1} : Finset β) ⊆ A := by
    simpa only [Finset.singleton_subset_iff] using v.2
  have hcount := Finset.card_filter_powersetCard_subset
    ({v.1} : Finset β) A 2 hvsub (by simp)
  have hfilter :
      (A.powersetCard 2).filter (fun e => v.1 ∈ e) =
        (A.powersetCard 2).filter
          (fun e => ({v.1} : Finset β) ⊆ e) := by
    ext e
    simp
  rw [hfilter, hcount, hA]
  norm_num [Nat.choose]

private noncomputable def kFiveFactorOmissionAt
    {β Colour : Type*} [DecidableEq β]
    [Fintype Colour] [DecidableEq Colour]
    (A : Finset β) (hA : A.card = 5)
    (factor : Colour → Finset (KFiveChord A))
    (hcard : ∀ c, (factor c).card = 2)
    (hmatching : ∀ c e, e ∈ factor c → ∀ k, k ∈ factor c →
      e ≠ k → Disjoint e.1 k.1)
    (c : Colour) : KFiveFactorOmission A (factor c) :=
  kFiveFactorOmission A hA (factor c) (hcard c)
    (hmatching c)

private theorem kFiveOmittedVertex_fibre_card_eq_one
    {β Colour : Type*} [DecidableEq β]
    [Fintype Colour] [DecidableEq Colour]
    (A : Finset β) (hA : A.card = 5)
    (factor : Colour → Finset (KFiveChord A))
    (hColour : Fintype.card Colour = 5)
    (hcard : ∀ c, (factor c).card = 2)
    (hmatching : ∀ c e, e ∈ factor c → ∀ k, k ∈ factor c →
      e ≠ k → Disjoint e.1 k.1)
    (hunique : ∀ e : KFiveChord A, ∃! c, e ∈ factor c)
    (v : ↥A) :
    ((Finset.univ : Finset Colour).filter fun c =>
      (kFiveFactorOmissionAt A hA factor hcard hmatching c).vertex = v).card = 1 := by
  classical
  let omission := kFiveFactorOmissionAt A hA factor hcard hmatching
  let incident : Colour → Finset (KFiveChord A) := fun c =>
    (factor c).filter fun e => v.1 ∈ e.1
  have hincidentLe (c : Colour) : (incident c).card ≤ 1 := by
    apply Finset.card_le_one_iff.mpr
    intro e k he hk
    have he' := Finset.mem_filter.mp he
    have hk' := Finset.mem_filter.mp hk
    by_contra hek
    have hdisj := hmatching c e he'.1 k hk'.1 hek
    exact (Finset.disjoint_left.mp hdisj) he'.2 hk'.2
  have hdegree (c : Colour) :
      (incident c).card = if (omission c).vertex = v then 0 else 1 := by
    by_cases hcv : (omission c).vertex = v
    · have hempty : incident c = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro e he
        have he' := Finset.mem_filter.mp he
        apply (omission c).avoids e he'.1
        simpa only [hcv] using he'.2
      simp [hempty, hcv]
    · have hpos : 0 < (incident c).card := by
        obtain ⟨e, he, hve⟩ := (omission c).covers v (Ne.symm hcv)
        exact Finset.card_pos.mpr
          ⟨e, Finset.mem_filter.mpr ⟨he, hve⟩⟩
      have hle := hincidentLe c
      simp only [hcv, ↓reduceIte]
      omega
  have hdisjoint :
      ((Finset.univ : Finset Colour) : Set Colour).PairwiseDisjoint
        incident := by
    intro c _hc d _hd hcd
    change Disjoint (incident c) (incident d)
    rw [Finset.disjoint_left]
    intro e hec hed
    have hec' := (Finset.mem_filter.mp hec).1
    have hed' := (Finset.mem_filter.mp hed).1
    obtain ⟨owner, _howner, hownerUnique⟩ := hunique e
    exact hcd ((hownerUnique c hec').trans
      (hownerUnique d hed').symm)
  have hcover :
      (Finset.univ : Finset Colour).biUnion incident =
        (Finset.univ : Finset (KFiveChord A)).filter
          (fun e => v.1 ∈ e.1) := by
    ext e
    constructor
    · intro he
      obtain ⟨c, _hc, hec⟩ := Finset.mem_biUnion.mp he
      have hec' := Finset.mem_filter.mp hec
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ e, hec'.2⟩
    · intro he
      have hve := (Finset.mem_filter.mp he).2
      obtain ⟨c, hec, _hcUnique⟩ := hunique e
      exact Finset.mem_biUnion.mpr
        ⟨c, Finset.mem_univ c,
          Finset.mem_filter.mpr ⟨hec, hve⟩⟩
  have hsum : (∑ c : Colour, (incident c).card) = 4 := by
    rw [← Finset.card_biUnion hdisjoint, hcover]
    exact card_incident_kFiveChords_eq_four A hA v
  have hsumIf :
      (∑ c : Colour, if (omission c).vertex = v then 0 else 1) = 4 := by
    calc
      (∑ c : Colour, if (omission c).vertex = v then 0 else 1) =
          ∑ c : Colour, (incident c).card := by
        apply Finset.sum_congr rfl
        intro c _hc
        exact (hdegree c).symm
      _ = 4 := hsum
  have hnonCard :
      ((Finset.univ : Finset Colour).filter fun c =>
        (omission c).vertex ≠ v).card = 4 := by
    calc
      ((Finset.univ : Finset Colour).filter fun c =>
          (omission c).vertex ≠ v).card =
          ∑ c : Colour, if (omission c).vertex ≠ v then 1 else 0 := by
        rw [← Finset.sum_filter, ← Finset.card_eq_sum_ones]
      _ = ∑ c : Colour,
          if (omission c).vertex = v then 0 else 1 := by
        apply Finset.sum_congr rfl
        intro c _hc
        by_cases hcv : (omission c).vertex = v <;> simp [hcv]
      _ = 4 := hsumIf
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset Colour))
    (fun c => (omission c).vertex = v)
  have hsplit' :
      ((Finset.univ : Finset Colour).filter fun c =>
          (omission c).vertex = v).card +
        ((Finset.univ : Finset Colour).filter fun c =>
          (omission c).vertex ≠ v).card = 5 := by
    simpa only [Finset.card_univ, hColour] using hsplit
  change ((Finset.univ : Finset Colour).filter fun c =>
    (omission c).vertex = v).card = 1
  omega

private noncomputable def kFiveOmittedColourEquiv
    {β Colour : Type*} [DecidableEq β]
    [Fintype Colour] [DecidableEq Colour]
    (A : Finset β) (hA : A.card = 5)
    (factor : Colour → Finset (KFiveChord A))
    (hColour : Fintype.card Colour = 5)
    (hcard : ∀ c, (factor c).card = 2)
    (hmatching : ∀ c e, e ∈ factor c → ∀ k, k ∈ factor c →
      e ≠ k → Disjoint e.1 k.1)
    (hunique : ∀ e : KFiveChord A, ∃! c, e ∈ factor c) :
    Colour ≃ ↥A := by
  classical
  let omitted : Colour → ↥A := fun c =>
    (kFiveFactorOmissionAt A hA factor hcard hmatching c).vertex
  have hfibre (v : ↥A) :
      ((Finset.univ : Finset Colour).filter fun c => omitted c = v).card = 1 := by
    exact kFiveOmittedVertex_fibre_card_eq_one
      A hA factor hColour hcard hmatching hunique v
  have hinjective : Function.Injective omitted := by
    intro c d hcd
    let v := omitted c
    have hc : c ∈ (Finset.univ : Finset Colour).filter
        (fun x => omitted x = v) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ c, rfl⟩
    have hd : d ∈ (Finset.univ : Finset Colour).filter
        (fun x => omitted x = v) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ d, hcd.symm⟩
    exact Finset.card_le_one_iff.mp (by rw [hfibre v]) hc hd
  have hsurjective : Function.Surjective omitted := by
    intro v
    have hpos : 0 < ((Finset.univ : Finset Colour).filter
        fun c => omitted c = v).card := by
      rw [hfibre v]
      omega
    obtain ⟨c, hc⟩ := Finset.card_pos.mp hpos
    exact ⟨c, (Finset.mem_filter.mp hc).2⟩
  exact Equiv.ofBijective omitted ⟨hinjective, hsurjective⟩

@[simp] private theorem kFiveOmittedColourEquiv_apply
    {β Colour : Type*} [DecidableEq β]
    [Fintype Colour] [DecidableEq Colour]
    (A : Finset β) (hA : A.card = 5)
    (factor : Colour → Finset (KFiveChord A))
    (hColour : Fintype.card Colour = 5)
    (hcard : ∀ c, (factor c).card = 2)
    (hmatching : ∀ c e, e ∈ factor c → ∀ k, k ∈ factor c →
      e ≠ k → Disjoint e.1 k.1)
    (hunique : ∀ e : KFiveChord A, ∃! c, e ∈ factor c)
    (c : Colour) :
    kFiveOmittedColourEquiv A hA factor hColour hcard hmatching hunique c =
      (kFiveFactorOmissionAt A hA factor hcard hmatching c).vertex := rfl

namespace KFiveNearOneFactorization

/-- Build a near-one-factorization from a partition of all chords into five
two-edge matchings. -/
noncomputable def ofPartition
    {β Colour : Type*} [DecidableEq β]
    [Fintype Colour] [DecidableEq Colour]
    (A : Finset β) (hA : A.card = 5)
    (factor : Colour → Finset (KFiveChord A))
    (hColour : Fintype.card Colour = 5)
    (hcard : ∀ c, (factor c).card = 2)
    (hmatching : ∀ c e, e ∈ factor c → ∀ k, k ∈ factor c →
      e ≠ k → Disjoint e.1 k.1)
    (hunique : ∀ e : KFiveChord A, ∃! c, e ∈ factor c) :
    KFiveNearOneFactorization A Colour where
  vertex_card := hA
  factor := factor
  factor_card_two := hcard
  factor_matching := hmatching
  omittedColourEquiv :=
    kFiveOmittedColourEquiv A hA factor hColour hcard hmatching hunique
  factor_avoids_omitted := by
    intro c e he
    rw [kFiveOmittedColourEquiv_apply]
    exact (kFiveFactorOmissionAt A hA factor hcard hmatching c).avoids e he
  factor_covers_other := by
    intro c v hv
    rw [kFiveOmittedColourEquiv_apply] at hv
    exact (kFiveFactorOmissionAt A hA factor hcard hmatching c).covers v hv
  chord_unique := hunique

end KFiveNearOneFactorization

end Erdos506.Finite
