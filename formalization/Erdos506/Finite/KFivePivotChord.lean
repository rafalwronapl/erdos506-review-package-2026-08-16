import Erdos506.Finite.KFiveNearOneFactorization

/-!
# Pivot chords in a near-one-factorization of `K₅`

Every factor is a two-edge matching on the four vertices other than its
omitted vertex.  Hence through any non-omitted vertex there is a unique
factor chord, with a unique other endpoint.  The four colours not omitting a
fixed pivot are thereby identified with the four remaining vertices.
-/

namespace Erdos506.Finite

namespace KFiveNearOneFactorization

variable {α Colour : Type*} [DecidableEq α]
  [Fintype Colour] [DecidableEq Colour]
  {A : Finset α}

/-- The unique chord of factor `c` incident with a non-omitted vertex `v`. -/
noncomputable def incidentChord
    (F : KFiveNearOneFactorization A Colour)
    (c : Colour) (v : ↥A)
    (hv : v ≠ F.omittedColourEquiv c) : KFiveChord A := by
  classical
  exact Classical.choose (F.factor_covers_other c v hv)

@[simp] theorem incidentChord_mem_factor
    (F : KFiveNearOneFactorization A Colour)
    (c : Colour) (v : ↥A)
    (hv : v ≠ F.omittedColourEquiv c) :
    F.incidentChord c v hv ∈ F.factor c := by
  exact (Classical.choose_spec (F.factor_covers_other c v hv)).1

@[simp] theorem vertex_mem_incidentChord
    (F : KFiveNearOneFactorization A Colour)
    (c : Colour) (v : ↥A)
    (hv : v ≠ F.omittedColourEquiv c) :
    v.1 ∈ (F.incidentChord c v hv).1 := by
  exact (Classical.choose_spec (F.factor_covers_other c v hv)).2

/-- Matching disjointness makes the chord through `v` unique in its factor. -/
theorem incidentChord_unique
    (F : KFiveNearOneFactorization A Colour)
    (c : Colour) (v : ↥A)
    (hv : v ≠ F.omittedColourEquiv c)
    (e : KFiveChord A) (he : e ∈ F.factor c) (hve : v.1 ∈ e.1) :
    e = F.incidentChord c v hv := by
  by_contra hne
  have hdisj := F.factor_matching c e he
    (F.incidentChord c v hv) (F.incidentChord_mem_factor c v hv) hne
  exact (Finset.disjoint_left.mp hdisj) hve
    (F.vertex_mem_incidentChord c v hv)

/-- The endpoint of the incident chord other than the chosen vertex. -/
noncomputable def otherEndpoint
    (F : KFiveNearOneFactorization A Colour)
    (c : Colour) (v : ↥A)
    (hv : v ≠ F.omittedColourEquiv c) : ↥A := by
  classical
  let e := F.incidentChord c v hv
  have hvMem : v.1 ∈ e.1 := F.vertex_mem_incidentChord c v hv
  have hdiffCard : (e.1 \ {v.1}).card = 1 := by
    rw [Finset.card_sdiff_of_subset]
    · have heCard := (Finset.mem_powersetCard.mp e.2).2
      simp [heCard]
    · simpa only [Finset.singleton_subset_iff] using hvMem
  have hpos : 0 < (e.1 \ {v.1}).card := by omega
  let hnonempty : (e.1 \ {v.1}).Nonempty := Finset.card_pos.mp hpos
  let w := Classical.choose hnonempty
  have hw : w ∈ e.1 \ {v.1} := Classical.choose_spec hnonempty
  exact ⟨w, (Finset.mem_powersetCard.mp e.2).1 (Finset.mem_sdiff.mp hw).1⟩

theorem otherEndpoint_ne
    (F : KFiveNearOneFactorization A Colour)
    (c : Colour) (v : ↥A)
    (hv : v ≠ F.omittedColourEquiv c) :
    F.otherEndpoint c v hv ≠ v := by
  intro h
  have hw := Classical.choose_spec
    (show ((F.incidentChord c v hv).1 \ {v.1}).Nonempty from by
      apply Finset.card_pos.mp
      have heCard := (Finset.mem_powersetCard.mp
        (F.incidentChord c v hv).2).2
      have hvMem := F.vertex_mem_incidentChord c v hv
      rw [Finset.card_sdiff_of_subset]
      · simp [heCard]
      · simpa only [Finset.singleton_subset_iff] using hvMem)
  have hnot := (Finset.mem_sdiff.mp hw).2
  have hval : (F.otherEndpoint c v hv).1 = v.1 := congrArg Subtype.val h
  apply hnot
  simpa [otherEndpoint] using hval

@[simp] theorem otherEndpoint_mem_incidentChord
    (F : KFiveNearOneFactorization A Colour)
    (c : Colour) (v : ↥A)
    (hv : v ≠ F.omittedColourEquiv c) :
    (F.otherEndpoint c v hv).1 ∈ (F.incidentChord c v hv).1 := by
  exact (Finset.mem_sdiff.mp (Classical.choose_spec
    (show ((F.incidentChord c v hv).1 \ {v.1}).Nonempty from by
      apply Finset.card_pos.mp
      have heCard := (Finset.mem_powersetCard.mp
        (F.incidentChord c v hv).2).2
      have hvMem := F.vertex_mem_incidentChord c v hv
      rw [Finset.card_sdiff_of_subset]
      · simp [heCard]
      · simpa only [Finset.singleton_subset_iff] using hvMem))).1

theorem incidentChord_val_eq_pair
    (F : KFiveNearOneFactorization A Colour)
    (c : Colour) (v : ↥A)
    (hv : v ≠ F.omittedColourEquiv c) :
    (F.incidentChord c v hv).1 =
      {v.1, (F.otherEndpoint c v hv).1} := by
  apply Finset.eq_of_subset_of_card_le
  · intro x hx
    have heCard := (Finset.mem_powersetCard.mp
      (F.incidentChord c v hv).2).2
    by_cases hxv : x = v.1
    · simp [hxv]
    · have hdiff : x ∈ (F.incidentChord c v hv).1 \ {v.1} :=
        Finset.mem_sdiff.mpr ⟨hx, by simpa using hxv⟩
      have hwDiff : (F.otherEndpoint c v hv).1 ∈
          (F.incidentChord c v hv).1 \ {v.1} := by
        apply Finset.mem_sdiff.mpr
        exact ⟨F.otherEndpoint_mem_incidentChord c v hv,
          by simpa using F.otherEndpoint_ne c v hv⟩
      have hdiffCard :
          ((F.incidentChord c v hv).1 \ {v.1}).card = 1 := by
        rw [Finset.card_sdiff_of_subset]
        · simp [heCard]
        · simpa only [Finset.singleton_subset_iff] using
            F.vertex_mem_incidentChord c v hv
      have hxw := Finset.card_le_one_iff.mp (by omega) hdiff hwDiff
      simp [hxw]
  · have heCard := (Finset.mem_powersetCard.mp
      (F.incidentChord c v hv).2).2
    rw [Finset.card_pair]
    · omega
    · intro h
      apply F.otherEndpoint_ne c v hv
      apply Subtype.ext
      exact h.symm

/-- Colours not omitting `v` are in bijection with the other four vertices. -/
noncomputable def pivotPartnerEquiv
    (F : KFiveNearOneFactorization A Colour) (v : ↥A) :
    {c : Colour // c ≠ F.omittedColourEquiv.symm v} ≃
      {w : ↥A // w ≠ v} := by
  let partner : {c : Colour // c ≠ F.omittedColourEquiv.symm v} →
      {w : ↥A // w ≠ v} := fun c =>
    ⟨F.otherEndpoint c.1 v (by
      intro h
      apply c.2
      apply F.omittedColourEquiv.injective
      simpa using h.symm),
      F.otherEndpoint_ne c.1 v _⟩
  have hinj : Function.Injective partner := by
    intro c d hcd
    apply Subtype.ext
    have hc : v ≠ F.omittedColourEquiv c.1 := by
      intro h
      apply c.2
      apply F.omittedColourEquiv.injective
      simpa using h.symm
    have hd : v ≠ F.omittedColourEquiv d.1 := by
      intro h
      apply d.2
      apply F.omittedColourEquiv.injective
      simpa using h.symm
    have hpairC := F.incidentChord_val_eq_pair c.1 v hc
    have hpairD := F.incidentChord_val_eq_pair d.1 v hd
    have hchords : F.incidentChord c.1 v hc = F.incidentChord d.1 v hd := by
      apply Subtype.ext
      rw [hpairC, hpairD]
      have hendpoint : F.otherEndpoint c.1 v hc = F.otherEndpoint d.1 v hd := by
        simpa only [partner] using congrArg Subtype.val hcd
      rw [congrArg Subtype.val hendpoint]
    obtain ⟨owner, _howner, hownerUnique⟩ :=
      F.chord_unique (F.incidentChord c.1 v hc)
    exact (hownerUnique c.1 (F.incidentChord_mem_factor c.1 v hc)).trans
      (hownerUnique d.1 (by simpa only [hchords] using
        F.incidentChord_mem_factor d.1 v hd)).symm
  have hcard : Fintype.card {c : Colour //
      c ≠ F.omittedColourEquiv.symm v} =
      Fintype.card {w : ↥A // w ≠ v} := by
    have hAcard : Fintype.card ↥A = 5 := by
      simpa only [Fintype.card_coe] using F.vertex_card
    have hColour : Fintype.card Colour = 5 :=
      (Fintype.card_congr F.omittedColourEquiv).trans hAcard
    simp [Fintype.card_subtype_compl, hColour, hAcard]
  exact Equiv.ofBijective partner
    ((Fintype.bijective_iff_injective_and_card partner).mpr ⟨hinj, hcard⟩)

@[simp] theorem pivotPartnerEquiv_apply_val
    (F : KFiveNearOneFactorization A Colour) (v : ↥A)
    (c : {c : Colour // c ≠ F.omittedColourEquiv.symm v}) :
    (F.pivotPartnerEquiv v c).1 =
      F.otherEndpoint c.1 v (by
        intro h
        apply c.2
        apply F.omittedColourEquiv.injective
        simpa using h.symm) := by
  simp [pivotPartnerEquiv]

end KFiveNearOneFactorization

end Erdos506.Finite
