import Erdos506.Incidence.RadicalAxisFourFourLedger

/-!
# The finite ten-by-ten radical-axis ledger

This module records the capacity-twenty equality case for compatible pairs
between two ten-element families whose centre fibres have size at most two.
At equality there are exactly five common centres, each used twice on both
sides.
-/

namespace Erdos506.Incidence

open scoped BigOperators

section FibreLedger

variable {X Y Q : Type*} [Fintype X] [Fintype Y]

/-- The equality profile at capacity twenty: five common centres, with
two elements above every centre on both sides. -/
def SaturatedFiveCenterProfile (f : X → Q) (g : Y → Q) : Prop := by
  classical
  exact (Finset.univ.image f).card = 5 ∧
    ∀ q ∈ Finset.univ.image f,
      (fullFibre f q).card = 2 ∧ (fullFibre g q).card = 2

/-- Ten left entries and right fibres of size at most two give the raw
capacity twenty. -/
theorem card_compatiblePairs_le_twenty
    (f : X → Q) (g : Y → Q)
    (hX : Fintype.card X = 10)
    (hg : ∀ q, (fullFibre g q).card ≤ 2) :
    (compatiblePairs f g).card ≤ 20 := by
  classical
  rw [card_compatiblePairs_eq_sum_right_fibres]
  calc
    (∑ x : X, (fullFibre g (f x)).card) ≤ ∑ _x : X, 2 := by
      apply Finset.sum_le_sum
      intro x _hx
      exact hg (f x)
    _ = 20 := by simp [hX]

private theorem all_eq_two_of_card_ten_of_sum_eq_twenty
    (v : X → Nat) (hX : Fintype.card X = 10)
    (hv : ∀ x, v x ≤ 2) (hsum : (∑ x, v x) = 20) :
    ∀ x, v x = 2 := by
  have hsumTwo : (∑ _x : X, 2) = 20 := by simp [hX]
  have heq : (∑ x, v x) = ∑ _x : X, 2 := hsum.trans hsumTwo.symm
  intro x
  exact (Finset.sum_eq_sum_iff_of_le
    (fun y (_hy : y ∈ (Finset.univ : Finset X)) => hv y)).mp
      heq x (Finset.mem_univ x)

/-- Capacity twenty forces the five-centre saturated profile. -/
theorem saturatedFiveCenterProfile_of_card_compatiblePairs_eq_twenty
    (f : X → Q) (g : Y → Q)
    (hX : Fintype.card X = 10) (hY : Fintype.card Y = 10)
    (hf : ∀ q, (fullFibre f q).card ≤ 2)
    (hg : ∀ q, (fullFibre g q).card ≤ 2)
    (hcard : (compatiblePairs f g).card = 20) :
    SaturatedFiveCenterProfile f g := by
  classical
  have hsumRight : (∑ x : X, (fullFibre g (f x)).card) = 20 := by
    rw [← card_compatiblePairs_eq_sum_right_fibres]
    exact hcard
  have hrightAtLeft (x : X) : (fullFibre g (f x)).card = 2 :=
    all_eq_two_of_card_ten_of_sum_eq_twenty
      (fun x => (fullFibre g (f x)).card) hX (fun x => hg (f x))
        hsumRight x
  let C : Finset Q := Finset.univ.image f
  have hCge : 5 ≤ C.card := by
    have hbound := Finset.card_le_mul_card_image
      (Finset.univ : Finset X) 2 (by
        intro q _hq
        simpa only [fullFibre] using hf q)
    have hbound' : 10 ≤ 2 * C.card := by
      simpa only [Finset.card_univ, hX, C] using hbound
    omega
  have hsumG : (∑ q ∈ C, (fullFibre g q).card) = 2 * C.card := by
    calc
      (∑ q ∈ C, (fullFibre g q).card) = ∑ _q ∈ C, 2 := by
        apply Finset.sum_congr rfl
        intro q hq
        obtain ⟨x, _hx, rfl⟩ := Finset.mem_image.mp hq
        exact hrightAtLeft x
      _ = 2 * C.card := by simp [Nat.mul_comm]
  have hsumGle : (∑ q ∈ C, (fullFibre g q).card) ≤ 10 := by
    calc
      (∑ q ∈ C, (fullFibre g q).card) =
          ((Finset.univ : Finset Y).filter fun y => g y ∈ C).card := by
        simpa only [fullFibre] using
          (Finset.sum_card_fiberwise_eq_card_filter
            (Finset.univ : Finset Y) C g)
      _ ≤ 10 := by
        have hfilter := Finset.card_filter_le (Finset.univ : Finset Y)
          (fun y => g y ∈ C)
        simpa only [Finset.card_univ, hY] using hfilter
  have hCcard : C.card = 5 := by omega
  have hsumF : (∑ q ∈ C, (fullFibre f q).card) = 10 := by
    change (∑ q ∈ Finset.univ.image f,
      ((Finset.univ : Finset X).filter fun x => f x = q).card) = 10
    rw [← Finset.card_eq_sum_card_image, Finset.card_univ, hX]
  have hsumFTwo : (∑ _q ∈ C, 2) = 10 := by simp [hCcard]
  have hleftAtCenter : ∀ q ∈ C, (fullFibre f q).card = 2 := by
    intro q hq
    apply (Finset.sum_eq_sum_iff_of_le
      (fun r (_hr : r ∈ C) => hf r)).mp
    · exact hsumF.trans hsumFTwo.symm
    · exact hq
  refine ⟨hCcard, ?_⟩
  intro q hq
  refine ⟨hleftAtCenter q hq, ?_⟩
  obtain ⟨x, _hx, hfx⟩ := Finset.mem_image.mp hq
  simpa only [hfx] using hrightAtLeft x

/-- In the saturated profile, the two maps have exactly the same image. -/
theorem image_eq_of_saturatedFiveCenterProfile
    (f : X → Q) (g : Y → Q)
    (hY : Fintype.card Y = 10)
    (h : SaturatedFiveCenterProfile f g) :
    (by classical exact Finset.univ.image g) =
      (by classical exact Finset.univ.image f) := by
  classical
  let C : Finset Q := Finset.univ.image f
  have hCcard : C.card = 5 := by
    simpa only [C] using h.1
  have hgTwo (q : Q) (hq : q ∈ C) :
      (fullFibre g q).card = 2 := by
    exact (h.2 q (by simpa only [C] using hq)).2
  have hsumG : (∑ q ∈ C, (fullFibre g q).card) = 10 := by
    calc
      (∑ q ∈ C, (fullFibre g q).card) = ∑ _q ∈ C, 2 := by
        apply Finset.sum_congr rfl
        exact hgTwo
      _ = 10 := by simp [hCcard]
  have hfilterCard :
      ((Finset.univ : Finset Y).filter fun y => g y ∈ C).card = 10 := by
    have hfiber :
        (∑ q ∈ C, (fullFibre g q).card) =
          ((Finset.univ : Finset Y).filter fun y => g y ∈ C).card := by
      simpa only [fullFibre] using
        (Finset.sum_card_fiberwise_eq_card_filter
          (Finset.univ : Finset Y) C g)
    omega
  have hfilterEq :
      (Finset.univ : Finset Y).filter (fun y => g y ∈ C) =
        Finset.univ := by
    apply Finset.eq_univ_of_card
    exact hfilterCard.trans hY.symm
  have himageGsubset : Finset.univ.image g ⊆ C := by
    intro q hq
    obtain ⟨y, _hy, rfl⟩ := Finset.mem_image.mp hq
    have hy :
        y ∈ (Finset.univ : Finset Y).filter (fun z => g z ∈ C) := by
      rw [hfilterEq]
      exact Finset.mem_univ y
    exact (Finset.mem_filter.mp hy).2
  have hCsubset : C ⊆ Finset.univ.image g := by
    intro q hq
    have hpos : 0 < (fullFibre g q).card := by
      rw [hgTwo q hq]
      omega
    obtain ⟨y, hy⟩ := Finset.card_pos.mp hpos
    exact Finset.mem_image.mpr
      ⟨y, Finset.mem_univ y, (mem_fullFibre g q y).mp hy⟩
  change Finset.univ.image g = C
  exact Finset.Subset.antisymm himageGsubset hCsubset

end FibreLedger

end Erdos506.Incidence
