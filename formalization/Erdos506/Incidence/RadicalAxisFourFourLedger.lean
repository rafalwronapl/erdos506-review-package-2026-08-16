import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic

/-!
# The finite six-by-six radical-axis ledger

This module is entirely geometry-free.  Two six-element families map to a
set of centres, with every fibre of either map having size at most two.
Compatible pairs have equal centres.  Their number is at most twelve, cannot
be eleven, and equality twelve forces exactly three common fibres of size
two on both sides.
-/

namespace Erdos506.Incidence

open scoped BigOperators

section FibreLedger

variable {X Y Q : Type*} [Fintype X] [Fintype Y]

/-- Fibre of a map on its whole finite domain. -/
noncomputable def fullFibre (f : X → Q) (q : Q) : Finset X := by
  classical
  exact Finset.univ.filter fun x => f x = q

/-- Pairs whose two entries receive the same centre. -/
noncomputable def compatiblePairs (f : X → Q) (g : Y → Q) :
    Finset (X × Y) := by
  classical
  exact Finset.univ.filter fun z => f z.1 = g z.2

@[simp] theorem mem_fullFibre (f : X → Q) (q : Q) (x : X) :
    x ∈ fullFibre f q ↔ f x = q := by
  classical
  simp [fullFibre]

@[simp] theorem mem_compatiblePairs (f : X → Q) (g : Y → Q)
    (x : X) (y : Y) :
    (x, y) ∈ compatiblePairs f g ↔ f x = g y := by
  classical
  simp [compatiblePairs]

/-- Count compatible pairs by first choosing the left entry. -/
theorem card_compatiblePairs_eq_sum_right_fibres
    (f : X → Q) (g : Y → Q) :
    (compatiblePairs f g).card =
      ∑ x : X, (fullFibre g (f x)).card := by
  classical
  simp only [compatiblePairs, fullFibre, Finset.card_eq_sum_ones,
    Finset.sum_filter]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro x _hx
  apply Finset.sum_congr rfl
  intro y _hy
  by_cases hxy : f x = g y
  · simp [hxy]
  · simp [hxy, Ne.symm hxy]

/-- Six left entries and right fibres of size at most two give the raw
capacity twelve. -/
theorem card_compatiblePairs_le_twelve
    (f : X → Q) (g : Y → Q)
    (hX : Fintype.card X = 6)
    (hg : ∀ q, (fullFibre g q).card ≤ 2) :
    (compatiblePairs f g).card ≤ 12 := by
  classical
  rw [card_compatiblePairs_eq_sum_right_fibres]
  calc
    (∑ x : X, (fullFibre g (f x)).card) ≤ ∑ _x : X, 2 := by
      apply Finset.sum_le_sum
      intro x _hx
      exact hg (f x)
    _ = 12 := by simp [hX]

/-- The equality profile forced at capacity twelve. -/
def SaturatedThreeCenterProfile (f : X → Q) (g : Y → Q) : Prop := by
  classical
  exact (Finset.univ.image f).card = 3 ∧
    ∀ q ∈ Finset.univ.image f,
      (fullFibre f q).card = 2 ∧ (fullFibre g q).card = 2

private theorem all_eq_two_of_card_six_of_sum_eq_twelve
    (v : X → Nat) (hX : Fintype.card X = 6)
    (hv : ∀ x, v x ≤ 2) (hsum : (∑ x, v x) = 12) :
    ∀ x, v x = 2 := by
  have hsumTwo : (∑ _x : X, 2) = 12 := by simp [hX]
  have heq : (∑ x, v x) = ∑ _x : X, 2 := hsum.trans hsumTwo.symm
  intro x
  exact (Finset.sum_eq_sum_iff_of_le
    (fun y (_hy : y ∈ (Finset.univ : Finset X)) => hv y)).mp
      heq x (Finset.mem_univ x)

/-- Capacity twelve forces the three-centre saturated profile. -/
theorem saturatedThreeCenterProfile_of_card_compatiblePairs_eq_twelve
    (f : X → Q) (g : Y → Q)
    (hX : Fintype.card X = 6) (hY : Fintype.card Y = 6)
    (hf : ∀ q, (fullFibre f q).card ≤ 2)
    (hg : ∀ q, (fullFibre g q).card ≤ 2)
    (hcard : (compatiblePairs f g).card = 12) :
    SaturatedThreeCenterProfile f g := by
  classical
  have hsumRight : (∑ x : X, (fullFibre g (f x)).card) = 12 := by
    rw [← card_compatiblePairs_eq_sum_right_fibres]
    exact hcard
  have hrightAtLeft (x : X) : (fullFibre g (f x)).card = 2 :=
    all_eq_two_of_card_six_of_sum_eq_twelve
      (fun x => (fullFibre g (f x)).card) hX (fun x => hg (f x))
        hsumRight x
  let C : Finset Q := Finset.univ.image f
  have hCge : 3 ≤ C.card := by
    have hbound := Finset.card_le_mul_card_image
      (Finset.univ : Finset X) 2 (by
        intro q _hq
        simpa only [fullFibre] using hf q)
    have hbound' : 6 ≤ 2 * C.card := by
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
  have hsumGle : (∑ q ∈ C, (fullFibre g q).card) ≤ 6 := by
    calc
      (∑ q ∈ C, (fullFibre g q).card) =
          ((Finset.univ : Finset Y).filter fun y => g y ∈ C).card := by
        simpa only [fullFibre] using
          (Finset.sum_card_fiberwise_eq_card_filter
            (Finset.univ : Finset Y) C g)
      _ ≤ 6 := by
        have hfilter := Finset.card_filter_le (Finset.univ : Finset Y)
          (fun y => g y ∈ C)
        simpa only [Finset.card_univ, hY] using hfilter
  have hCcard : C.card = 3 := by omega
  have hsumF : (∑ q ∈ C, (fullFibre f q).card) = 6 := by
    change (∑ q ∈ Finset.univ.image f,
      ((Finset.univ : Finset X).filter fun x => f x = q).card) = 6
    rw [← Finset.card_eq_sum_card_image, Finset.card_univ, hX]
  have hsumFTwo : (∑ _q ∈ C, 2) = 6 := by simp [hCcard]
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

/-- Capacity eleven is impossible. -/
theorem card_compatiblePairs_ne_eleven
    (f : X → Q) (g : Y → Q)
    (hX : Fintype.card X = 6) (hY : Fintype.card Y = 6)
    (hf : ∀ q, (fullFibre f q).card ≤ 2)
    (hg : ∀ q, (fullFibre g q).card ≤ 2) :
    (compatiblePairs f g).card ≠ 11 := by
  classical
  intro hcard
  have hsum : (∑ x : X, (fullFibre g (f x)).card) = 11 := by
    rw [← card_compatiblePairs_eq_sum_right_fibres]
    exact hcard
  have hexception : ∃ x : X, (fullFibre g (f x)).card < 2 := by
    by_contra hnot
    push Not at hnot
    have hlower : (∑ _x : X, 2) ≤
        ∑ x : X, (fullFibre g (f x)).card := by
      apply Finset.sum_le_sum
      intro x _hx
      exact hnot x
    have htwoSum : (∑ _x : X, 2) = 12 := by simp [hX]
    omega
  obtain ⟨x₀, hx₀lt⟩ := hexception
  have hEraseCard : ((Finset.univ : Finset X).erase x₀).card = 5 := by
    simp [hX]
  have hsplit₀ :
      (∑ x ∈ (Finset.univ : Finset X).erase x₀,
          (fullFibre g (f x)).card) + (fullFibre g (f x₀)).card = 11 := by
    rw [Finset.sum_erase_add (Finset.univ : Finset X)
      (fun x => (fullFibre g (f x)).card) (Finset.mem_univ x₀)]
    exact hsum
  have hEraseLe :
      (∑ x ∈ (Finset.univ : Finset X).erase x₀,
          (fullFibre g (f x)).card) ≤ 10 := by
    calc
      (∑ x ∈ (Finset.univ : Finset X).erase x₀,
          (fullFibre g (f x)).card) ≤
          ∑ _x ∈ (Finset.univ : Finset X).erase x₀, 2 := by
        apply Finset.sum_le_sum
        intro x _hx
        exact hg (f x)
      _ = 10 := by simp [hEraseCard]
  have hx₀one : (fullFibre g (f x₀)).card = 1 := by omega
  have hother (x : X) (hxx₀ : x ≠ x₀) :
      (fullFibre g (f x)).card = 2 := by
    have hxle := hg (f x)
    by_contra hxne
    have hxlt : (fullFibre g (f x)).card < 2 := by omega
    have hxmem : x ∈ (Finset.univ : Finset X).erase x₀ :=
      Finset.mem_erase.mpr ⟨hxx₀, Finset.mem_univ x⟩
    have hEraseEraseCard :
        (((Finset.univ : Finset X).erase x₀).erase x).card = 4 := by
      rw [Finset.card_erase_of_mem hxmem, hEraseCard]
    have hEraseEraseLe :
        (∑ z ∈ ((Finset.univ : Finset X).erase x₀).erase x,
            (fullFibre g (f z)).card) ≤ 8 := by
      calc
        (∑ z ∈ ((Finset.univ : Finset X).erase x₀).erase x,
            (fullFibre g (f z)).card) ≤
            ∑ _z ∈ ((Finset.univ : Finset X).erase x₀).erase x, 2 := by
          apply Finset.sum_le_sum
          intro z _hz
          exact hg (f z)
        _ = 8 := by simp [hEraseEraseCard]
    have hsplitx :
        (∑ z ∈ ((Finset.univ : Finset X).erase x₀).erase x,
            (fullFibre g (f z)).card) + (fullFibre g (f x)).card =
          ∑ z ∈ (Finset.univ : Finset X).erase x₀,
            (fullFibre g (f z)).card := by
      exact Finset.sum_erase_add
        ((Finset.univ : Finset X).erase x₀)
        (fun z => (fullFibre g (f z)).card) hxmem
    omega
  let q₀ : Q := f x₀
  have hgq₀ : (fullFibre g q₀).card = 1 := hx₀one
  have hfUnique (x : X) (hx : f x = q₀) : x = x₀ := by
    by_contra hxx₀
    have hxTwo := hother x hxx₀
    rw [hx] at hxTwo
    omega
  let C : Finset Q := (Finset.univ.image f).erase q₀
  have hq₀notC : q₀ ∉ C := by simp [C]
  have himageErase :
      ((Finset.univ : Finset X).erase x₀).image f = C := by
    ext q
    constructor
    · intro hq
      obtain ⟨x, hxmem, hfx⟩ := Finset.mem_image.mp hq
      have hxx₀ := (Finset.mem_erase.mp hxmem).1
      apply Finset.mem_erase.mpr
      refine ⟨?_, Finset.mem_image.mpr
        ⟨x, Finset.mem_univ x, hfx⟩⟩
      intro hqq₀
      apply hxx₀
      apply hfUnique x
      exact hfx.trans hqq₀
    · intro hq
      have hq' := Finset.mem_erase.mp hq
      obtain ⟨x, _hx, hfx⟩ := Finset.mem_image.mp hq'.2
      apply Finset.mem_image.mpr
      refine ⟨x, Finset.mem_erase.mpr ⟨?_, Finset.mem_univ x⟩, hfx⟩
      intro hxx₀
      subst x
      exact hq'.1 hfx.symm
  have hleftCentres : 5 ≤ 2 * C.card := by
    have hbound := Finset.card_le_mul_card_image
      ((Finset.univ : Finset X).erase x₀) 2 (by
        intro q _hq
        have hsubset :
            (((Finset.univ : Finset X).erase x₀).filter
              fun x => f x = q) ⊆ fullFibre f q := by
          intro x hx
          exact (mem_fullFibre f q x).mpr (Finset.mem_filter.mp hx).2
        exact (Finset.card_le_card hsubset).trans (hf q))
    simpa only [hEraseCard, himageErase] using hbound
  have hgC (q : Q) (hq : q ∈ C) : (fullFibre g q).card = 2 := by
    have hq' := Finset.mem_erase.mp hq
    obtain ⟨x, _hx, hfx⟩ := Finset.mem_image.mp hq'.2
    have hxx₀ : x ≠ x₀ := by
      intro hxx₀
      subst x
      exact hq'.1 hfx.symm
    simpa only [hfx] using hother x hxx₀
  have hselectedSum :
      (∑ q ∈ insert q₀ C, (fullFibre g q).card) =
        1 + 2 * C.card := by
    rw [Finset.sum_insert hq₀notC, hgq₀]
    congr 1
    calc
      (∑ q ∈ C, (fullFibre g q).card) = ∑ _q ∈ C, 2 := by
        apply Finset.sum_congr rfl
        exact hgC
      _ = 2 * C.card := by simp [Nat.mul_comm]
  have hselectedLe :
      (∑ q ∈ insert q₀ C, (fullFibre g q).card) ≤ 6 := by
    calc
      (∑ q ∈ insert q₀ C, (fullFibre g q).card) =
          ((Finset.univ : Finset Y).filter
            fun y => g y ∈ insert q₀ C).card := by
        simpa only [fullFibre] using
          (Finset.sum_card_fiberwise_eq_card_filter
            (Finset.univ : Finset Y) (insert q₀ C) g)
      _ ≤ 6 := by
        have hfilter := Finset.card_filter_le (Finset.univ : Finset Y)
          (fun y => g y ∈ insert q₀ C)
        simpa only [Finset.card_univ, hY] using hfilter
  rw [hselectedSum] at hselectedLe
  omega

/-- Excluding the saturated profile improves capacity twelve to ten. -/
theorem card_compatiblePairs_le_ten_of_not_saturated
    (f : X → Q) (g : Y → Q)
    (hX : Fintype.card X = 6) (hY : Fintype.card Y = 6)
    (hf : ∀ q, (fullFibre f q).card ≤ 2)
    (hg : ∀ q, (fullFibre g q).card ≤ 2)
    (hnot : ¬ SaturatedThreeCenterProfile f g) :
    (compatiblePairs f g).card ≤ 10 := by
  have hle := card_compatiblePairs_le_twelve f g hX hg
  have hne := card_compatiblePairs_ne_eleven f g hX hY hf hg
  by_contra hnotTen
  have hge : 11 ≤ (compatiblePairs f g).card := by omega
  rcases Nat.eq_or_lt_of_le hge with heq | hlt
  · exact hne heq.symm
  · have htwelve : (compatiblePairs f g).card = 12 := by omega
    exact hnot
      (saturatedThreeCenterProfile_of_card_compatiblePairs_eq_twelve
        f g hX hY hf hg htwelve)

end FibreLedger

end Erdos506.Incidence
