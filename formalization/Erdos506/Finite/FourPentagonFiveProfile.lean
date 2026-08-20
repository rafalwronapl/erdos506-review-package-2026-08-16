import Erdos506.Finite.FourPentagonFiveProfileCore
import Erdos506.Finite.FourPentagonFinFourPairLedger

/-!
# The second-moment-twelve five-block normal form

This predecessor module turns the opaque five-block labeling into the
canonical ten-point profile.  The finite pair enumeration and the labeling
construction live behind separate olean boundaries.
-/

namespace Erdos506.Finite

open Erdos506.Block
open Erdos506.Block.BlockSystem
open scoped BigOperators
open FourPentagonProfile

universe u v

namespace FourPentagonFiveProfile

/-- A profile with degrees one, two, or three is one of the nine
canonical profiles once the two empty fibres and the two high profiles have
been identified.  The only finite enumeration is delegated to the pair
ledger. -/
theorem canonical_profile_cases
    {Point : Type*} [Fintype Point] [DecidableEq Point]
    (prof : Point → Finset (Fin 4)) (d : Point → Nat)
    (T T' : Point)
    (hdegreeCases : ∀ p, d p = 1 ∨ d p = 2 ∨ d p = 3)
    (hprofCard : ∀ p, (prof p).card = d p)
    (hfiberSingleton : ∀ j : Fin 4,
      ((Finset.univ : Finset Point).filter fun p => prof p = {j}).card =
        if j = 0 ∨ j = 1 then 1 else 0)
    (hfiberPairZero :
      ((Finset.univ : Finset Point).filter
        fun p => prof p = {0, 1}).card = 0)
    (hhighCases : ∀ {p : Point}, d p = 3 → p = T ∨ p = T')
    (hprofT : prof T = {0, 1, 2})
    (hprofT' : prof T' = {0, 1, 3})
    (p : Point) :
    prof p = {0} ∨ prof p = {1} ∨
    prof p = {0, 1, 2} ∨ prof p = {0, 1, 3} ∨
    prof p = {0, 2} ∨ prof p = {0, 3} ∨
    prof p = {1, 2} ∨ prof p = {1, 3} ∨
    prof p = {2, 3} := by
  rcases hdegreeCases p with h1 | h2 | h3
  · have hcard : (prof p).card = 1 := by rw [hprofCard, h1]
    obtain ⟨j, hj⟩ := Finset.card_eq_one.mp hcard
    fin_cases j
    · exact Or.inl hj
    · exact Or.inr (Or.inl hj)
    · have hzero := hfiberSingleton 2
      have hpMem : p ∈ ((Finset.univ : Finset Point).filter
          fun q => prof q = {2}) := by simp [hj]
      rw [show (if (2 : Fin 4) = 0 ∨ (2 : Fin 4) = 1 then 1 else 0) = 0
        by decide] at hzero
      have hpos := Finset.card_pos.mpr ⟨p, hpMem⟩
      omega
    · have hzero := hfiberSingleton 3
      have hpMem : p ∈ ((Finset.univ : Finset Point).filter
          fun q => prof q = {3}) := by simp [hj]
      rw [show (if (3 : Fin 4) = 0 ∨ (3 : Fin 4) = 1 then 1 else 0) = 0
        by decide] at hzero
      have hpos := Finset.card_pos.mpr ⟨p, hpMem⟩
      omega
  · have hcard : (prof p).card = 2 := by rw [hprofCard, h2]
    obtain ⟨j, k, hjk, hjkEq⟩ := Finset.card_eq_two.mp hcard
    have hnot01 : prof p ≠ {0, 1} := by
      intro hp01
      have hpMem : p ∈ ((Finset.univ : Finset Point).filter
          fun q => prof q = {0, 1}) := by simp [hp01]
      have hpos := Finset.card_pos.mpr ⟨p, hpMem⟩
      omega
    have hledger :=
      FourPentagonFinFourPairLedger.pair_cases hjk
    rw [hjkEq]
    rcases hledger with h01 | h02 | h03 | h12 | h13 | h23
    · exact (hnot01 (hjkEq.trans h01)).elim
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h02))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h03)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr (Or.inr (Or.inl h12))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr (Or.inr (Or.inr (Or.inl h13)))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr (Or.inr (Or.inr (Or.inr h23)))))))
  · rcases hhighCases h3 with rfl | rfl
    · exact Or.inr (Or.inr (Or.inl hprofT))
    · exact Or.inr (Or.inr (Or.inr (Or.inl hprofT')))

noncomputable def fiveProfileNormalForm_of_labeling
    {Point Block : Type*} [Fintype Point] [Fintype Block]
    [DecidableEq Point]
    (S : BlockSystem Point Block) (_hPoint : Fintype.card Point = 10)
    (hfive : S.blockCount 5 = 4)
    (_hlow : ((Finset.univ : Finset Point).filter
      fun p => S.blockDegree 5 p = 1).card = 2)
    (hprofile : ∀ p : Point, S.blockDegree 5 p = 1 ∨
      S.blockDegree 5 p = 2 ∨ S.blockDegree 5 p = 3)
    (hmoment : (∑ p : Point,
      Nat.choose (S.blockDegree 5 p) 2) = 12)
    (L : FourPentagonFiveBlockLabeling S) :
    FourPentagonFiveNormalForm S := by
  classical
  let F := S.blocksOfSize 5
  have hinterFive := fiveBlock_pair_inter_eq_two_of_secondMoment_twelve
    S hfive hmoment
  let T : Point := L.high₀
  let T' : Point := L.high₁
  let B : Fin 4 ≃ {c : Block // c ∈ F} := L.five
  have hTT' : T ≠ T' := L.high_ne
  have hTdegree : S.blockDegree 5 T = 3 := L.high₀_degree
  have hT'degree : S.blockDegree 5 T' = 3 := L.high₁_degree
  have hTmem (j : Fin 4) :
      T ∈ S.support (B j).1 ↔ j ∈ ({0, 1, 2} : Finset (Fin 4)) :=
    L.high₀_mem j
  have hT'mem (j : Fin 4) :
      T' ∈ S.support (B j).1 ↔ j ∈ ({0, 1, 3} : Finset (Fin 4)) :=
    L.high₁_mem j
  have hhighCases {p : Point} (hp : S.blockDegree 5 p = 3) :
      p = T ∨ p = T' := L.high_cases hp
  have hsumSupport (b : Block) (hb : b ∈ F) :
      (∑ p ∈ S.support b, S.blockDegree 5 p) = 11 :=
    fiveBlock_support_degree_sum_eq_eleven S hfive hinterFive b hb
  let prof : Point → Finset (Fin 4) := fun p =>
    Finset.univ.filter fun j => p ∈ S.support (B j).1
  have hprofMem (p : Point) (j : Fin 4) :
      j ∈ prof p ↔ p ∈ S.support (B j).1 := by simp [prof]
  have hprofCard (p : Point) : (prof p).card = S.blockDegree 5 p := by
    change ((Finset.univ : Finset (Fin 4)).filter
      fun j => p ∈ S.support (B j).1).card =
        (F.filter fun c => p ∈ S.support c).card
    exact card_profile_eq_card_filter F B
      (fun c => p ∈ S.support c)
  have hprofT : prof T = {0, 1, 2} := by
    ext j
    rw [hprofMem]
    exact hTmem j
  have hprofT' : prof T' = {0, 1, 3} := by
    ext j
    rw [hprofMem]
    exact hT'mem j
  have hhighSet :
      ((Finset.univ : Finset Point).filter
        fun p => S.blockDegree 5 p = 3) = {T, T'} := L.high_set
  have hbalance (j : Fin 4) :
      ((S.support (B j).1).filter
          fun p => S.blockDegree 5 p = 1).card + 1 =
        ((S.support (B j).1).filter
          fun p => S.blockDegree 5 p = 3).card := by
    have hsum := hsumSupport (B j).1 (B j).2
    have hrow := sum_add_filter_one_eq_two_mul_card_add_filter_three
      (S.support (B j).1) (fun p => S.blockDegree 5 p)
      (fun p _hp => hprofile p)
    change
      (∑ p ∈ S.support (B j).1, S.blockDegree 5 p) +
          ((S.support (B j).1).filter
            fun p => S.blockDegree 5 p = 1).card =
        2 * (S.support (B j).1).card +
          ((S.support (B j).1).filter
            fun p => S.blockDegree 5 p = 3).card at hrow
    rw [hsum, S.mem_blocksOfSize.mp (B j).2] at hrow
    omega
  have hhighOn (j : Fin 4) :
      ((S.support (B j).1).filter
        fun p => S.blockDegree 5 p = 3).card =
        if j = 0 ∨ j = 1 then 2 else 1 := by
    have heq : ((S.support (B j).1).filter
          fun p => S.blockDegree 5 p = 3) =
        ({T, T'} : Finset Point).filter fun p =>
          p ∈ S.support (B j).1 := by
      ext p
      simp only [Finset.mem_filter, Finset.mem_insert,
        Finset.mem_singleton]
      constructor
      · rintro ⟨hp, hd⟩
        have hpHigh : p ∈ ((Finset.univ : Finset Point).filter
            fun z => S.blockDegree 5 z = 3) := by simp [hd]
        rw [hhighSet] at hpHigh
        exact ⟨by simpa using hpHigh, hp⟩
      · rintro ⟨hp, hsupp⟩
        rcases hp with rfl | rfl
        · exact ⟨hsupp, hTdegree⟩
        · exact ⟨hsupp, hT'degree⟩
    rw [heq]
    fin_cases j
    · change (({T, T'} : Finset Point).filter fun p =>
          p ∈ S.support (B 0).1).card = 2
      exact card_filter_pair_of_mem_mem hTT' (S.support (B 0).1)
        ((hTmem 0).2 (by decide)) ((hT'mem 0).2 (by decide))
    · change (({T, T'} : Finset Point).filter fun p =>
          p ∈ S.support (B 1).1).card = 2
      exact card_filter_pair_of_mem_mem hTT' (S.support (B 1).1)
        ((hTmem 1).2 (by decide)) ((hT'mem 1).2 (by decide))
    · change (({T, T'} : Finset Point).filter fun p =>
          p ∈ S.support (B 2).1).card = 1
      have hT'not : T' ∉ S.support (B 2).1 := by
        intro hT'2
        have hfalse := (hT'mem 2).1 hT'2
        exact (by decide : (2 : Fin 4) ∉
          ({0, 1, 3} : Finset (Fin 4))) hfalse
      exact card_filter_pair_of_mem_not_mem (S.support (B 2).1)
        ((hTmem 2).2 (by decide)) hT'not
    · change (({T, T'} : Finset Point).filter fun p =>
          p ∈ S.support (B 3).1).card = 1
      have hTnot : T ∉ S.support (B 3).1 := by
        intro hT3
        have hfalse := (hTmem 3).1 hT3
        exact (by decide : (3 : Fin 4) ∉
          ({0, 1, 2} : Finset (Fin 4))) hfalse
      exact card_filter_pair_of_not_mem_mem (S.support (B 3).1)
        hTnot ((hT'mem 3).2 (by decide))
  have hlowOn (j : Fin 4) :
      ((S.support (B j).1).filter
        fun p => S.blockDegree 5 p = 1).card =
        if j = 0 ∨ j = 1 then 1 else 0 := by
    have hb := hbalance j
    rw [hhighOn j] at hb
    by_cases hj : j = 0 ∨ j = 1
    · rw [if_pos hj] at hb ⊢
      omega
    · rw [if_neg hj] at hb ⊢
      omega
  have hprofSingleton (p : Point) (j : Fin 4) :
      prof p = {j} ↔
        p ∈ S.support (B j).1 ∧ S.blockDegree 5 p = 1 := by
    constructor
    · intro hp
      have hj : j ∈ prof p := by
        rw [hp]
        exact Finset.mem_singleton_self j
      have hdegree : S.blockDegree 5 p = 1 := by
        calc
          S.blockDegree 5 p = (prof p).card := (hprofCard p).symm
          _ = ({j} : Finset (Fin 4)).card := congrArg Finset.card hp
          _ = 1 := Finset.card_singleton j
      exact ⟨(hprofMem p j).mp hj, hdegree⟩
    · rintro ⟨hpj, hd⟩
      symm
      apply Finset.eq_of_subset_of_card_le
      · intro k hk
        have hkj : k = j := Finset.mem_singleton.mp hk
        subst k
        exact (hprofMem p j).mpr hpj
      · rw [hprofCard p, hd]
        simp
  have hprofPair (p : Point) (j k : Fin 4) (hjk : j ≠ k) :
      prof p = {j, k} ↔
        p ∈ S.support (B j).1 ∩ S.support (B k).1 ∧
          S.blockDegree 5 p = 2 := by
    constructor
    · intro hp
      have hj : j ∈ prof p := by rw [hp]; simp
      have hk : k ∈ prof p := by rw [hp]; simp
      exact ⟨Finset.mem_inter.mpr ⟨(hprofMem p j).mp hj,
        (hprofMem p k).mp hk⟩, by rw [← hprofCard p, hp]; simp [hjk]⟩
    · rintro ⟨hpjk, hd⟩
      have hpj : p ∈ S.support (B j).1 :=
        (Finset.mem_inter.mp hpjk).1
      have hpk : p ∈ S.support (B k).1 :=
        (Finset.mem_inter.mp hpjk).2
      symm
      apply Finset.eq_of_subset_of_card_le
      · intro l hl
        simp only [Finset.mem_insert, Finset.mem_singleton] at hl
        rcases hl with hlj | hlk
        · rw [hlj]
          exact (hprofMem p j).mpr hpj
        · rw [hlk]
          exact (hprofMem p k).mpr hpk
      · rw [hprofCard, hd]
        simp [hjk]
  have hdegreeTwoInter (j k : Fin 4) (hjk : j ≠ k) :
      ((S.support (B j).1 ∩ S.support (B k).1).filter
          fun p => S.blockDegree 5 p = 2).card +
        (({T, T'} : Finset Point).filter fun p =>
          p ∈ S.support (B j).1 ∩ S.support (B k).1).card = 2 := by
    let I := S.support (B j).1 ∩ S.support (B k).1
    have hIcard : I.card = 2 :=
      hinterFive (B j).1 (B j).2 (B k).1 (B k).2
        (fun h => hjk (B.injective (Subtype.ext h)))
    have hnotTwo : I.filter (fun p => ¬S.blockDegree 5 p = 2) =
        ({T, T'} : Finset Point).filter fun p => p ∈ I := by
      ext p
      simp only [Finset.mem_filter, Finset.mem_insert,
        Finset.mem_singleton]
      constructor
      · rintro ⟨hpI, hpnot2⟩
        rcases hprofile p with h1 | h2 | h3
        · have hjmem : j ∈ prof p := (hprofMem p j).mpr
              (Finset.mem_inter.mp hpI).1
          have hkmem : k ∈ prof p := (hprofMem p k).mpr
              (Finset.mem_inter.mp hpI).2
          have hcard := hprofCard p
          rw [h1] at hcard
          have hsub : ({j, k} : Finset (Fin 4)) ⊆ prof p := by
            intro l hl
            simp only [Finset.mem_insert, Finset.mem_singleton] at hl
            rcases hl with hlj | hlk
            · rw [hlj]
              exact hjmem
            · rw [hlk]
              exact hkmem
          have hc := Finset.card_le_card hsub
          simp [hjk, hcard] at hc
        · exact (hpnot2 h2).elim
        · exact ⟨hhighCases h3, hpI⟩
      · rintro ⟨hpHigh, hpI⟩
        rcases hpHigh with rfl | rfl
        · exact ⟨hpI, by omega⟩
        · exact ⟨hpI, by omega⟩
    have hsplit := Finset.card_filter_add_card_filter_not
      (s := I) (fun p => S.blockDegree 5 p = 2)
    rw [hnotTwo, hIcard] at hsplit
    exact hsplit
  have hpairCard01 :
      ((S.support (B 0).1 ∩ S.support (B 1).1).filter
        fun p => S.blockDegree 5 p = 2).card = 0 := by
    have h := hdegreeTwoInter 0 1 (by decide)
    have hhigh : (({T, T'} : Finset Point).filter fun p =>
        p ∈ S.support (B 0).1 ∩ S.support (B 1).1).card = 2 :=
      card_filter_pair_of_mem_mem hTT'
        (S.support (B 0).1 ∩ S.support (B 1).1)
        (Finset.mem_inter.mpr
          ⟨(hTmem 0).2 (by decide), (hTmem 1).2 (by decide)⟩)
        (Finset.mem_inter.mpr
          ⟨(hT'mem 0).2 (by decide), (hT'mem 1).2 (by decide)⟩)
    omega
  have hpairCard02 :
      ((S.support (B 0).1 ∩ S.support (B 2).1).filter
        fun p => S.blockDegree 5 p = 2).card = 1 := by
    have h := hdegreeTwoInter 0 2 (by decide)
    have hT'not : T' ∉ S.support (B 0).1 ∩ S.support (B 2).1 := by
      intro hT'
      have hfalse := (hT'mem 2).1 (Finset.mem_inter.mp hT').2
      exact (by decide : (2 : Fin 4) ∉
        ({0, 1, 3} : Finset (Fin 4))) hfalse
    have hhigh : (({T, T'} : Finset Point).filter fun p =>
        p ∈ S.support (B 0).1 ∩ S.support (B 2).1).card = 1 :=
      card_filter_pair_of_mem_not_mem
        (S.support (B 0).1 ∩ S.support (B 2).1)
        (Finset.mem_inter.mpr
          ⟨(hTmem 0).2 (by decide), (hTmem 2).2 (by decide)⟩)
        hT'not
    omega
  have hpairCard03 :
      ((S.support (B 0).1 ∩ S.support (B 3).1).filter
        fun p => S.blockDegree 5 p = 2).card = 1 := by
    have h := hdegreeTwoInter 0 3 (by decide)
    have hTnot : T ∉ S.support (B 0).1 ∩ S.support (B 3).1 := by
      intro hT
      have hfalse := (hTmem 3).1 (Finset.mem_inter.mp hT).2
      exact (by decide : (3 : Fin 4) ∉
        ({0, 1, 2} : Finset (Fin 4))) hfalse
    have hhigh : (({T, T'} : Finset Point).filter fun p =>
        p ∈ S.support (B 0).1 ∩ S.support (B 3).1).card = 1 :=
      card_filter_pair_of_not_mem_mem
        (S.support (B 0).1 ∩ S.support (B 3).1)
        hTnot
        (Finset.mem_inter.mpr
          ⟨(hT'mem 0).2 (by decide), (hT'mem 3).2 (by decide)⟩)
    omega
  have hpairCard12 :
      ((S.support (B 1).1 ∩ S.support (B 2).1).filter
        fun p => S.blockDegree 5 p = 2).card = 1 := by
    have h := hdegreeTwoInter 1 2 (by decide)
    have hT'not : T' ∉ S.support (B 1).1 ∩ S.support (B 2).1 := by
      intro hT'
      have hfalse := (hT'mem 2).1 (Finset.mem_inter.mp hT').2
      exact (by decide : (2 : Fin 4) ∉
        ({0, 1, 3} : Finset (Fin 4))) hfalse
    have hhigh : (({T, T'} : Finset Point).filter fun p =>
        p ∈ S.support (B 1).1 ∩ S.support (B 2).1).card = 1 :=
      card_filter_pair_of_mem_not_mem
        (S.support (B 1).1 ∩ S.support (B 2).1)
        (Finset.mem_inter.mpr
          ⟨(hTmem 1).2 (by decide), (hTmem 2).2 (by decide)⟩)
        hT'not
    omega
  have hpairCard13 :
      ((S.support (B 1).1 ∩ S.support (B 3).1).filter
        fun p => S.blockDegree 5 p = 2).card = 1 := by
    have h := hdegreeTwoInter 1 3 (by decide)
    have hTnot : T ∉ S.support (B 1).1 ∩ S.support (B 3).1 := by
      intro hT
      have hfalse := (hTmem 3).1 (Finset.mem_inter.mp hT).2
      exact (by decide : (3 : Fin 4) ∉
        ({0, 1, 2} : Finset (Fin 4))) hfalse
    have hhigh : (({T, T'} : Finset Point).filter fun p =>
        p ∈ S.support (B 1).1 ∩ S.support (B 3).1).card = 1 :=
      card_filter_pair_of_not_mem_mem
        (S.support (B 1).1 ∩ S.support (B 3).1)
        hTnot
        (Finset.mem_inter.mpr
          ⟨(hT'mem 1).2 (by decide), (hT'mem 3).2 (by decide)⟩)
    omega
  have hpairCard23 :
      ((S.support (B 2).1 ∩ S.support (B 3).1).filter
        fun p => S.blockDegree 5 p = 2).card = 2 := by
    have h := hdegreeTwoInter 2 3 (by decide)
    have hTnot : T ∉ S.support (B 2).1 ∩ S.support (B 3).1 := by
      intro hT
      have hfalse := (hTmem 3).1 (Finset.mem_inter.mp hT).2
      exact (by decide : (3 : Fin 4) ∉
        ({0, 1, 2} : Finset (Fin 4))) hfalse
    have hT'not : T' ∉ S.support (B 2).1 ∩ S.support (B 3).1 := by
      intro hT'
      have hfalse := (hT'mem 2).1 (Finset.mem_inter.mp hT').1
      exact (by decide : (2 : Fin 4) ∉
        ({0, 1, 3} : Finset (Fin 4))) hfalse
    have hhigh : (({T, T'} : Finset Point).filter fun p =>
        p ∈ S.support (B 2).1 ∩ S.support (B 3).1).card = 0 :=
      card_filter_pair_of_not_mem_not_mem
        (S.support (B 2).1 ∩ S.support (B 3).1) hTnot hT'not
    omega
  have hfiberSingleton (j : Fin 4) :
      ((Finset.univ : Finset Point).filter fun p => prof p = {j}).card =
        if j = 0 ∨ j = 1 then 1 else 0 := by
    have heq : ((Finset.univ : Finset Point).filter fun p => prof p = {j}) =
        (S.support (B j).1).filter fun p => S.blockDegree 5 p = 1 := by
      ext p
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact hprofSingleton p j
    rw [heq, hlowOn]
  have hfiberPair (j k : Fin 4) (hjk : j ≠ k) :
      ((Finset.univ : Finset Point).filter fun p => prof p = {j, k}).card =
        ((S.support (B j).1 ∩ S.support (B k).1).filter
          fun p => S.blockDegree 5 p = 2).card := by
    congr 1
    ext p
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact hprofPair p j k hjk
  have hfiberHighT :
      ((Finset.univ : Finset Point).filter
        fun p => prof p = {0, 1, 2}).card = 1 := by
    have heq : ((Finset.univ : Finset Point).filter
          fun p => prof p = {0, 1, 2}) = {T} := by
      ext p
      simp only [Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_singleton]
      constructor
      · intro hp
        have hd : S.blockDegree 5 p = 3 := by
          rw [← hprofCard p, hp]
          decide
        rcases hhighCases hd with rfl | rfl
        · rfl
        · rw [hprofT'] at hp
          have hne : ({0, 1, 3} : Finset (Fin 4)) ≠ {0, 1, 2} := by
            decide
          exact (hne hp).elim
      · rintro rfl
        exact hprofT
    rw [heq]
    simp
  have hfiberHighT' :
      ((Finset.univ : Finset Point).filter
        fun p => prof p = {0, 1, 3}).card = 1 := by
    have heq : ((Finset.univ : Finset Point).filter
          fun p => prof p = {0, 1, 3}) = {T'} := by
      ext p
      simp only [Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_singleton]
      constructor
      · intro hp
        have hd : S.blockDegree 5 p = 3 := by
          rw [← hprofCard p, hp]
          decide
        rcases hhighCases hd with rfl | rfl
        · rw [hprofT] at hp
          have hne : ({0, 1, 2} : Finset (Fin 4)) ≠ {0, 1, 3} := by
            decide
          exact (hne hp).elim
        · rfl
      · rintro rfl
        exact hprofT'
    rw [heq]
    simp
  have hpairFiberZero :
      ((Finset.univ : Finset Point).filter
        fun p => prof p = {0, 1}).card = 0 := by
    rw [hfiberPair 0 1 (by decide), hpairCard01]
  have hprofCases (p : Point) :
      prof p = {0} ∨ prof p = {1} ∨
      prof p = {0, 1, 2} ∨ prof p = {0, 1, 3} ∨
      prof p = {0, 2} ∨ prof p = {0, 3} ∨
      prof p = {1, 2} ∨ prof p = {1, 3} ∨
      prof p = {2, 3} :=
    canonical_profile_cases prof (fun q => S.blockDegree 5 q) T T'
      hprofile hprofCard hfiberSingleton hpairFiberZero
      hhighCases hprofT hprofT' p
  have hactualFiber (Q : Finset (Fin 4)) :
      Fintype.card {p : Point // prof p = Q} =
        fourPentagonProfileMultiplicity Q := by
    rw [Fintype.card_subtype]
    by_cases h0 : Q = {0}
    · subst Q
      simpa [fourPentagonProfileMultiplicity] using hfiberSingleton 0
    by_cases h1 : Q = {1}
    · subst Q
      simpa [fourPentagonProfileMultiplicity] using hfiberSingleton 1
    by_cases hT : Q = {0, 1, 2}
    · subst Q
      simpa [fourPentagonProfileMultiplicity] using hfiberHighT
    by_cases hT' : Q = {0, 1, 3}
    · subst Q
      simpa [fourPentagonProfileMultiplicity] using hfiberHighT'
    by_cases h02 : Q = {0, 2}
    · subst Q
      rw [hfiberPair 0 2 (by decide), hpairCard02]
      decide
    by_cases h03 : Q = {0, 3}
    · subst Q
      rw [hfiberPair 0 3 (by decide), hpairCard03]
      decide
    by_cases h12 : Q = {1, 2}
    · subst Q
      rw [hfiberPair 1 2 (by decide), hpairCard12]
      decide
    by_cases h13 : Q = {1, 3}
    · subst Q
      rw [hfiberPair 1 3 (by decide), hpairCard13]
      decide
    by_cases h23 : Q = {2, 3}
    · subst Q
      rw [hfiberPair 2 3 (by decide), hpairCard23]
      decide
    · have hempty : ((Finset.univ : Finset Point).filter
          fun p => prof p = Q) = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro p hp
        have hpq := (Finset.mem_filter.mp hp).2
        rcases hprofCases p with hp0 | hp1 | hpT | hpT' | hp02 |
          hp03 | hp12 | hp13 | hp23
        · exact h0 (hpq.symm.trans hp0)
        · exact h1 (hpq.symm.trans hp1)
        · exact hT (hpq.symm.trans hpT)
        · exact hT' (hpq.symm.trans hpT')
        · exact h02 (hpq.symm.trans hp02)
        · exact h03 (hpq.symm.trans hp03)
        · exact h12 (hpq.symm.trans hp12)
        · exact h13 (hpq.symm.trans hp13)
        · exact h23 (hpq.symm.trans hp23)
      rw [hempty]
      simp [fourPentagonProfileMultiplicity, h0, h1, hT, hT',
        h02, h03, h12, h13, h23]
  let P : Fin 10 ≃ Point := equivOfFiberCardEq fourPentagonProfile prof
    (fun Q => (canonicalProfile_fiber_card Q).trans (hactualFiber Q).symm)
  have hPprof (i : Fin 10) : prof (P i) = fourPentagonProfile i := by
    exact equivOfFiberCardEq_map fourPentagonProfile prof
      (fun Q => (canonicalProfile_fiber_card Q).trans (hactualFiber Q).symm) i
  refine {
    point := P
    five := fun j => (B j).1
    five_mem := fun j => (B j).2
    mem_five := ?_ }
  intro i j
  rw [← hprofMem, hPprof]
  simp [fourPentagonProfile]

/-- The small entrance adapter deliberately composes the two opaque stages
without unfolding either construction. -/
noncomputable def fiveNormalForm_of_secondMoment_twelve
    {Point Block : Type*} [Fintype Point] [Fintype Block]
    [DecidableEq Point]
    (S : BlockSystem Point Block) (hPoint : Fintype.card Point = 10)
    (hfive : S.blockCount 5 = 4)
    (hlow : ((Finset.univ : Finset Point).filter
      fun p => S.blockDegree 5 p = 1).card = 2)
    (hhigh : ((Finset.univ : Finset Point).filter
      fun p => S.blockDegree 5 p = 3).card = 2)
    (hprofile : ∀ p : Point, S.blockDegree 5 p = 1 ∨
      S.blockDegree 5 p = 2 ∨ S.blockDegree 5 p = 3)
    (hmoment : (∑ p : Point,
      Nat.choose (S.blockDegree 5 p) 2) = 12) :
    FourPentagonFiveNormalForm S :=
  fiveProfileNormalForm_of_labeling S hPoint hfive hlow hprofile hmoment
    (fiveBlockLabeling_of_secondMoment_twelve S hfive hhigh hprofile hmoment)

end FourPentagonFiveProfile

end Erdos506.Finite
