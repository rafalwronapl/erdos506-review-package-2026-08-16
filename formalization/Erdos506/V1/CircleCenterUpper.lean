import Erdos506.V1.Carrier

/-!
# The circle-and-centre upper-bound certificate

This file proves the counting part once and for all.  Boundary labels lie on
one proper circle and the unique outsider is its centre.  Any further
determined circle meets the base circle in exactly two selected boundary
points.  Explicit collinear diameter pairs can therefore be removed from the
possible pair set.
-/

namespace Erdos506.V1

open Erdos506.Finite Erdos506.V4

theorem mem_determinedCircles_of_three_le_circleTrace
    {α : Type*} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (c : ProperCircle)
    (hthree : 3 ≤ (circleTrace cfg c).card) :
    c ∈ determinedCircles cfg := by
  classical
  obtain ⟨t, hsub, htcard⟩ := Finset.exists_subset_card_eq hthree
  rw [mem_determinedCircles_iff]
  let kt : KSubset α 3 := ⟨t, htcard⟩
  have hnon : IsNoncollinear cfg t := by
    by_contra hcol
    exact not_triple_subset_circle_of_collinear cfg kt hcol c hsub
  let nt : NoncollinearTriple cfg :=
    ⟨t, mem_noncollinearTriples.mpr ⟨htcard, hnon⟩⟩
  refine ⟨nt, ?_⟩
  intro x hx
  exact mem_circleTrace.mp (hsub hx)

theorem circleTrace_inter_card_lt_three_of_ne
    {α : Type*} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (c d : DeterminedCircle cfg) (hcd : c ≠ d) :
    (circleTrace cfg c.1 ∩ circleTrace cfg d.1).card < 3 := by
  classical
  by_contra hnot
  have hge : 3 ≤ (circleTrace cfg c.1 ∩ circleTrace cfg d.1).card := by omega
  obtain ⟨t, htsub, htcard⟩ := Finset.exists_subset_card_eq hge
  have hnon : IsNoncollinear cfg t := by
    by_contra hcol
    exact not_triple_subset_circle_of_collinear cfg ⟨t, htcard⟩ hcol c.1
      (fun x hx => (Finset.mem_inter.mp (htsub hx)).1)
  let nt : NoncollinearTriple cfg :=
    ⟨t, mem_noncollinearTriples.mpr ⟨htcard, hnon⟩⟩
  have hc : c.1 = properCircumcircle cfg nt :=
    properCircle_eq_properCircumcircle_of_support cfg nt c.1 (by
      intro x hx
      exact mem_circleTrace.mp (Finset.mem_inter.mp (htsub hx)).1)
  have hd : d.1 = properCircumcircle cfg nt :=
    properCircle_eq_properCircumcircle_of_support cfg nt d.1 (by
      intro x hx
      exact mem_circleTrace.mp (Finset.mem_inter.mp (htsub hx)).2)
  apply hcd
  apply Subtype.ext
  exact hc.trans hd.symm

section

variable {β : Type*} [Fintype β] [DecidableEq β]
variable {r : ℕ}

abbrev CenterLabels (β : Type*) := β ⊕ Unit

def boundaryLabels : Finset (CenterLabels β) :=
  Finset.univ.image Sum.inl

def centerLabel : CenterLabels β := Sum.inr ()

@[simp] theorem mem_boundaryLabels (x : β) :
    Sum.inl x ∈ boundaryLabels (β := β) := by
  simp [boundaryLabels]

@[simp] theorem center_not_mem_boundaryLabels :
    centerLabel (β := β) ∉ boundaryLabels (β := β) := by
  simp [centerLabel, boundaryLabels]

theorem card_boundaryLabels :
    (boundaryLabels (β := β)).card = Fintype.card β := by
  classical
  rw [boundaryLabels, Finset.card_image_of_injective _ Sum.inl_injective]
  simp

variable (cfg : Configuration (CenterLabels β))
variable (g : DeterminedCircle cfg)
variable (hg : circleTrace cfg g.1 = boundaryLabels (β := β))

include hg in
theorem offBase_inter_card_eq_two (c : DeterminedCircle cfg) (hcg : c ≠ g) :
    (circleTrace cfg c.1 ∩ circleTrace cfg g.1).card = 2 := by
  classical
  have hinter := circleTrace_inter_card_lt_three_of_ne cfg c g hcg
  have hsupport := Erdos506.V3.circleSupport_card_ge_three cfg c
  have houtsub : circleTrace cfg c.1 \ circleTrace cfg g.1 ⊆
      {centerLabel (β := β)} := by
    intro x hx
    have hxnot := (Finset.mem_sdiff.mp hx).2
    rw [hg] at hxnot
    rcases x with x | u
    · exact (hxnot (mem_boundaryLabels x)).elim
    · cases u
      simp [centerLabel]
  have houtle : (circleTrace cfg c.1 \ circleTrace cfg g.1).card ≤ 1 := by
    simpa using Finset.card_le_card houtsub
  have hsplit := Finset.card_sdiff_add_card_inter
    (circleTrace cfg c.1) (circleTrace cfg g.1)
  omega

include hg in
theorem center_mem_offBase (c : DeterminedCircle cfg) (hcg : c ≠ g) :
    centerLabel (β := β) ∈ circleTrace cfg c.1 := by
  classical
  by_contra hcenter
  have hsub : circleTrace cfg c.1 ⊆ circleTrace cfg g.1 := by
    intro x hx
    rw [hg]
    rcases x with x | u
    · exact mem_boundaryLabels x
    · cases u
      exact (hcenter hx).elim
  have hinterEq : circleTrace cfg c.1 ∩ circleTrace cfg g.1 =
      circleTrace cfg c.1 := Finset.inter_eq_left.mpr hsub
  have hinter := offBase_inter_card_eq_two cfg g hg c hcg
  rw [hinterEq] at hinter
  have hsupport := Erdos506.V3.circleSupport_card_ge_three cfg c
  omega

noncomputable def offBasePair (c : {c : DeterminedCircle cfg // c ≠ g}) :
    Finset (CenterLabels β) :=
  circleTrace cfg c.1.1 ∩ circleTrace cfg g.1

include hg in
theorem offBasePair_card (c : {c : DeterminedCircle cfg // c ≠ g}) :
    (offBasePair cfg g c).card = 2 :=
  offBase_inter_card_eq_two cfg g hg c.1 c.2

theorem offBasePair_subset (c : {c : DeterminedCircle cfg // c ≠ g}) :
    offBasePair cfg g c ⊆ circleTrace cfg g.1 :=
  Finset.inter_subset_right

include hg in
theorem offBasePair_injective : Function.Injective (offBasePair cfg g) := by
  classical
  intro c d hpair
  apply Subtype.ext
  by_contra hcd
  have hcCenter := center_mem_offBase cfg g hg c.1 c.2
  have hdCenter := center_mem_offBase cfg g hg d.1 d.2
  have hpCard := offBasePair_card cfg g hg c
  have hsub : insert (centerLabel (β := β)) (offBasePair cfg g c) ⊆
      circleTrace cfg c.1.1 ∩ circleTrace cfg d.1.1 := by
    intro x hx
    rw [Finset.mem_insert] at hx
    rcases hx with rfl | hx
    · exact Finset.mem_inter.mpr ⟨hcCenter, hdCenter⟩
    · have hxc := (Finset.mem_inter.mp hx).1
      have hxdPair : x ∈ offBasePair cfg g d := by simpa [hpair] using hx
      have hxd := (Finset.mem_inter.mp hxdPair).1
      exact Finset.mem_inter.mpr ⟨hxc, hxd⟩
  have hcenterNot : centerLabel (β := β) ∉ offBasePair cfg g c := by
    intro h
    exact center_not_mem_boundaryLabels
      (by rw [← hg]; exact (Finset.mem_inter.mp h).2)
  have hthree : 3 ≤
      (circleTrace cfg c.1.1 ∩ circleTrace cfg d.1.1).card := by
    have hins : (insert (centerLabel (β := β))
        (offBasePair cfg g c)).card = 3 := by simp [hcenterNot, hpCard]
    rw [← hins]
    exact Finset.card_le_card hsub
  exact (not_lt_of_ge hthree)
    (circleTrace_inter_card_lt_three_of_ne cfg c.1 d.1 hcd)

variable (diameterPair : Fin r → Finset (CenterLabels β))
variable (hdiamCard : ∀ i, (diameterPair i).card = 2)
variable (hdiamSubset : ∀ i, diameterPair i ⊆ circleTrace cfg g.1)
variable (hdiamInj : Function.Injective diameterPair)
variable (hdiamCollinear : ∀ i,
  Collinear ℝ (supportPoints cfg (insert (centerLabel (β := β)) (diameterPair i))))

noncomputable def basePairs : Finset (Finset (CenterLabels β)) :=
  (circleTrace cfg g.1).powersetCard 2

noncomputable def badPairs : Finset (Finset (CenterLabels β)) :=
  Finset.univ.image diameterPair

noncomputable def goodPairs : Finset (Finset (CenterLabels β)) :=
  basePairs cfg g \ badPairs diameterPair

include hg hdiamCard hdiamSubset hdiamCollinear in
theorem offBasePair_mem_goodPairs (c : {c : DeterminedCircle cfg // c ≠ g}) :
    offBasePair cfg g c ∈ goodPairs cfg g diameterPair := by
  classical
  rw [goodPairs, Finset.mem_sdiff]
  refine ⟨Finset.mem_powersetCard.mpr
    ⟨offBasePair_subset cfg g c, offBasePair_card cfg g hg c⟩, ?_⟩
  intro hbad
  obtain ⟨i, _hi, hEq⟩ := Finset.mem_image.mp hbad
  have hcCenter := center_mem_offBase cfg g hg c.1 c.2
  have hsub : insert (centerLabel (β := β)) (diameterPair i) ⊆
      circleTrace cfg c.1.1 := by
    intro x hx
    rw [Finset.mem_insert] at hx
    rcases hx with rfl | hx
    · exact hcCenter
    · have : x ∈ offBasePair cfg g c := by simpa [hEq] using hx
      exact (Finset.mem_inter.mp this).1
  let A : KSubset (CenterLabels β) 3 := by
    refine ⟨insert (centerLabel (β := β)) (diameterPair i), ?_⟩
    have hcnot : centerLabel (β := β) ∉ diameterPair i := by
      intro hc
      exact center_not_mem_boundaryLabels
        (by rw [← hg]; exact hdiamSubset i hc)
    simp [hcnot, hdiamCard i]
  have hcol : ¬IsNoncollinear cfg A.1 := by
    simpa [IsNoncollinear, A] using hdiamCollinear i
  exact not_triple_subset_circle_of_collinear cfg A hcol c.1.1 hsub

include hg hdiamCard hdiamSubset hdiamInj in
theorem goodPairs_card :
    (goodPairs cfg g diameterPair).card =
      Nat.choose (Fintype.card β) 2 - r := by
  classical
  have hbadSub : badPairs diameterPair ⊆ basePairs cfg g := by
    intro A hA
    obtain ⟨i, _hi, rfl⟩ := Finset.mem_image.mp hA
    exact Finset.mem_powersetCard.mpr ⟨hdiamSubset i, hdiamCard i⟩
  rw [goodPairs, Finset.card_sdiff_of_subset hbadSub,
    basePairs, Finset.card_powersetCard, hg, card_boundaryLabels,
    badPairs, Finset.card_image_of_injective _ hdiamInj]
  simp

include g hg diameterPair hdiamCard hdiamSubset hdiamInj hdiamCollinear in
theorem circleCount_le_circle_center_target :
    circleCount cfg ≤
      1 + Nat.choose (Fintype.card β) 2 - r := by
  classical
  let offToGood : {c : DeterminedCircle cfg // c ≠ g} →
      {A // A ∈ goodPairs cfg g diameterPair} := fun c =>
    ⟨offBasePair cfg g c, offBasePair_mem_goodPairs cfg g hg diameterPair
      hdiamCard hdiamSubset hdiamCollinear c⟩
  have hinj : Function.Injective offToGood := by
    intro c d h
    apply offBasePair_injective cfg g hg
    exact congrArg Subtype.val h
  have hcard := Fintype.card_le_of_injective offToGood hinj
  have hoff : Fintype.card {c : DeterminedCircle cfg // c ≠ g} + 1 =
      Fintype.card (DeterminedCircle cfg) := by
    rw [Fintype.card_subtype_compl
      (fun c : DeterminedCircle cfg => c = g)]
    rw [Fintype.card_subtype_eq g]
    have hpos : 0 < Fintype.card (DeterminedCircle cfg) := by
      exact Fintype.card_pos_iff.mpr ⟨g⟩
    omega
  have hgood : Fintype.card {A // A ∈ goodPairs cfg g diameterPair} =
      Nat.choose (Fintype.card β) 2 - r := by
    rw [Fintype.card_coe,
      goodPairs_card (cfg := cfg) (g := g) (hg := hg)
        (diameterPair := diameterPair) hdiamCard hdiamSubset hdiamInj]
  rw [hgood] at hcard
  have hbadSub : badPairs diameterPair ⊆ basePairs cfg g := by
    intro A hA
    obtain ⟨i, _hi, rfl⟩ := Finset.mem_image.mp hA
    exact Finset.mem_powersetCard.mpr ⟨hdiamSubset i, hdiamCard i⟩
  have hrle : r ≤ Nat.choose (Fintype.card β) 2 := by
    calc
      r = (badPairs diameterPair).card := by
        symm
        simp [badPairs, Finset.card_image_of_injective _ hdiamInj]
      _ ≤ (basePairs cfg g).card := Finset.card_le_card hbadSub
      _ = Nat.choose (Fintype.card β) 2 := by
        rw [basePairs, Finset.card_powersetCard, hg, card_boundaryLabels]
  have hoff' : Fintype.card {c : DeterminedCircle cfg // c ≠ g} + 1 =
      (determinedCircles cfg).card := by
    simpa [DeterminedCircle] using hoff
  change (determinedCircles cfg).card ≤
    1 + Nat.choose (Fintype.card β) 2 - r
  calc
    (determinedCircles cfg).card =
        Fintype.card {c : DeterminedCircle cfg // c ≠ g} + 1 := hoff'.symm
    _ ≤ (Nat.choose (Fintype.card β) 2 - r) + 1 :=
      Nat.add_le_add_right hcard 1
    _ = 1 + Nat.choose (Fintype.card β) 2 - r := by omega

end

end Erdos506.V1
