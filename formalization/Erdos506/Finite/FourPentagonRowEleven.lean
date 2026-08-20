import Erdos506.Finite.FourPentagonProfile
import Erdos506.Finite.FourPentagonRowTen

/-!
# Elimination of the second-moment eleven row
-/

namespace Erdos506.Finite

open Erdos506.Block
open Erdos506.Block.BlockSystem
open scoped BigOperators
open FourPentagonProfile

namespace FourPentagonRowEleven

theorem secondMoment_eleven_row_impossible
    {Point Block : Type*} [Fintype Point] [Fintype Block]
    [DecidableEq Point]
    (S : BlockSystem Point Block) (hPoint : Fintype.card Point = 10)
    (hcap : ∀ b : Block, 3 ≤ (S.support b).card →
      (S.support b).card ≤ 5)
    (hd3 : ∀ p : Point, S.blockDegree 3 p = 6 ∨
      S.blockDegree 3 p = 9)
    (hfive : S.blockCount 5 = 4)
    (hlow : ((Finset.univ : Finset Point).filter
      fun p => S.blockDegree 5 p = 1).card = 1)
    (hhigh : ((Finset.univ : Finset Point).filter
      fun p => S.blockDegree 5 p = 3).card = 1)
    (hprofile : ∀ p : Point, S.blockDegree 5 p = 1 ∨
      S.blockDegree 5 p = 2 ∨ S.blockDegree 5 p = 3)
    (hmoment : (∑ p : Point,
      Nat.choose (S.blockDegree 5 p) 2) = 11) : False := by
  classical
  let F := S.blocksOfSize 5
  have hFcard : F.card = 4 := hfive
  obtain ⟨U, hUeq⟩ := Finset.card_eq_one.mp hlow
  obtain ⟨T, hTeq⟩ := Finset.card_eq_one.mp hhigh
  have hUdegree : S.blockDegree 5 U = 1 := by
    have : U ∈ ((Finset.univ : Finset Point).filter
      fun p => S.blockDegree 5 p = 1) := by rw [hUeq]; simp
    exact (Finset.mem_filter.mp this).2
  have hTdegree : S.blockDegree 5 T = 3 := by
    have : T ∈ ((Finset.univ : Finset Point).filter
      fun p => S.blockDegree 5 p = 3) := by rw [hTeq]; simp
    exact (Finset.mem_filter.mp this).2
  have hTU : T ≠ U := by
    intro h
    rw [h] at hTdegree
    omega
  have hdegreeBaseline (p : Point) (hpU : p ≠ U) (hpT : p ≠ T) :
      S.blockDegree 5 p = 2 := by
    rcases hprofile p with h1 | h2 | h3
    · have hp : p ∈ ((Finset.univ : Finset Point).filter
          fun q => S.blockDegree 5 q = 1) := by simp [h1]
      rw [hUeq] at hp
      exact (hpU (by simpa using hp)).elim
    · exact h2
    · have hp : p ∈ ((Finset.univ : Finset Point).filter
          fun q => S.blockDegree 5 q = 3) := by simp [h3]
      rw [hTeq] at hp
      exact (hpT (by simpa using hp)).elim
  have hpairTotal :
      (∑ A ∈ F.powersetCard 2, (S.commonSupport A).card) = 11 := by
    rw [← S.binomial_degree_moment F 2]
    exact hmoment
  have hpairLe (A : Finset Block) (hA : A ∈ F.powersetCard 2) :
      (S.commonSupport A).card ≤ 2 :=
    S.commonSupport_card_le_two (Finset.mem_powersetCard.mp hA).2
  have hpairFamilyCard : (F.powersetCard 2).card = 6 := by
    simp [hFcard, Nat.choose]
  obtain ⟨D, hD, hDone, hDother⟩ := card_six_sum_eleven_le_two
    (F.powersetCard 2) (fun A => (S.commonSupport A).card)
    hpairFamilyCard hpairLe hpairTotal
  obtain ⟨d₀, d₁, hd₀ne₁, hDeq⟩ :=
    Finset.card_eq_two.mp (Finset.mem_powersetCard.mp hD).2
  have hDsub := (Finset.mem_powersetCard.mp hD).1
  have hd₀ : d₀ ∈ F := hDsub (by rw [hDeq]; simp)
  have hd₁ : d₁ ∈ F := hDsub (by rw [hDeq]; simp)
  let HU := F.filter fun b => U ∈ S.support b
  have hHUcard : HU.card = 1 := hUdegree
  obtain ⟨b₀, hb₀eq⟩ := Finset.card_eq_one.mp hHUcard
  have hb₀HU : b₀ ∈ HU := by rw [hb₀eq]; simp
  have hb₀ : b₀ ∈ F := (Finset.mem_filter.mp hb₀HU).1
  have hUb₀ : U ∈ S.support b₀ := (Finset.mem_filter.mp hb₀HU).2
  have hUnot (b : Block) (hb : b ∈ F) (hbne : b ≠ b₀) :
      U ∉ S.support b := by
    intro hUb
    have : b ∈ HU := Finset.mem_filter.mpr ⟨hb, hUb⟩
    rw [hb₀eq] at this
    exact hbne (by simpa using this)
  have hpairRow (b : Block) (hb : b ∈ F) :
      (∑ c ∈ F.erase b, (S.support b ∩ S.support c).card) =
        if b ∈ D then 5 else 6 := by
    have hcardErase : (F.erase b).card = 3 := by
      rw [Finset.card_erase_of_mem hb, hFcard]
    by_cases hbD : b ∈ D
    · obtain ⟨c₀, hc₀D, hc₀ne⟩ :
          ∃ c₀ ∈ D, c₀ ≠ b := by
        have hbD' := hbD
        rw [hDeq] at hbD'
        simp only [Finset.mem_insert, Finset.mem_singleton] at hbD'
        rcases hbD' with hbEq | hbEq
        · refine ⟨d₁, ?_, ?_⟩
          · rw [hDeq]
            exact Finset.mem_insert_of_mem (Finset.mem_singleton_self d₁)
          · intro h
            exact hd₀ne₁ (hbEq.symm.trans h.symm)
        · refine ⟨d₀, ?_, ?_⟩
          · rw [hDeq]
            exact Finset.mem_insert_self d₀ {d₁}
          · intro h
            exact hd₀ne₁ (h.trans hbEq)
      have hc₀F : c₀ ∈ F := hDsub hc₀D
      have hpairD : ({b, c₀} : Finset Block) = D := by
        apply Finset.eq_of_subset_of_card_le
        · intro z hz
          simp only [Finset.mem_insert, Finset.mem_singleton] at hz
          rcases hz with rfl | rfl <;> assumption
        · have hbnot : b ∉ ({c₀} : Finset Block) := by
            simpa only [Finset.mem_singleton] using Ne.symm hc₀ne
          have hpairCard : ({b, c₀} : Finset Block).card = 2 := by
            rw [Finset.card_insert_of_notMem hbnot,
              Finset.card_singleton]
          rw [(Finset.mem_powersetCard.mp hD).2, hpairCard]
      have hone : (S.support b ∩ S.support c₀).card = 1 := by
        rw [← S.commonSupport_pair, hpairD]
        exact hDone
      calc
        (∑ c ∈ F.erase b, (S.support b ∩ S.support c).card) =
            1 + ∑ c ∈ (F.erase b).erase c₀,
              (S.support b ∩ S.support c).card := by
          have hc₀erase : c₀ ∈ F.erase b :=
            Finset.mem_erase.mpr ⟨hc₀ne, hc₀F⟩
          have hsplit := Finset.sum_erase_add (F.erase b)
            (fun c => (S.support b ∩ S.support c).card) hc₀erase
          change (∑ c ∈ (F.erase b).erase c₀,
              (S.support b ∩ S.support c).card) +
              (S.support b ∩ S.support c₀).card =
            ∑ c ∈ F.erase b,
              (S.support b ∩ S.support c).card at hsplit
          rw [hone] at hsplit
          omega
        _ = 1 + ∑ _c ∈ (F.erase b).erase c₀, 2 := by
          congr 1
          apply Finset.sum_congr rfl
          intro c hc
          have hcF := Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hc)
          have hcb := (Finset.mem_erase.mp (Finset.mem_of_mem_erase hc)).1
          have hcc₀ := (Finset.mem_erase.mp hc).1
          have hpairMem : ({b, c} : Finset Block) ∈ F.powersetCard 2 := by
            apply Finset.mem_powersetCard.mpr
            constructor
            · intro z hz
              simp only [Finset.mem_insert, Finset.mem_singleton] at hz
              rcases hz with rfl | rfl
              · exact hb
              · exact hcF
            · have hbnot : b ∉ ({c} : Finset Block) := by
                simpa only [Finset.mem_singleton] using Ne.symm hcb
              rw [Finset.card_insert_of_notMem hbnot,
                Finset.card_singleton]
          have hneD : ({b, c} : Finset Block) ≠ D := by
            intro heq
            have : c = c₀ := by
              have hcD : c ∈ D := by rw [← heq]; simp
              rw [← hpairD] at hcD
              simpa [hcb] using hcD
            exact hcc₀ this
          have := hDother {b, c} hpairMem hneD
          simpa [S.commonSupport_pair] using this
        _ = 5 := by simp [Finset.card_erase_of_mem,
            Finset.card_erase_of_mem, hcardErase,
            (show c₀ ∈ F.erase b from Finset.mem_erase.mpr ⟨hc₀ne, hc₀F⟩)]
        _ = (if b ∈ D then 5 else 6) := by simp [hbD]
    · calc
        (∑ c ∈ F.erase b, (S.support b ∩ S.support c).card) =
            ∑ _c ∈ F.erase b, 2 := by
          apply Finset.sum_congr rfl
          intro c hc
          have hcF := Finset.mem_of_mem_erase hc
          have hcb := (Finset.mem_erase.mp hc).1
          have hpairMem : ({b, c} : Finset Block) ∈ F.powersetCard 2 := by
            apply Finset.mem_powersetCard.mpr
            constructor
            · intro z hz
              simp only [Finset.mem_insert, Finset.mem_singleton] at hz
              rcases hz with rfl | rfl
              · exact hb
              · exact hcF
            · have hbnot : b ∉ ({c} : Finset Block) := by
                simpa only [Finset.mem_singleton] using Ne.symm hcb
              rw [Finset.card_insert_of_notMem hbnot,
                Finset.card_singleton]
          have hneD : ({b, c} : Finset Block) ≠ D := by
            intro heq
            apply hbD
            rw [← heq]
            simp
          have := hDother {b, c} hpairMem hneD
          simpa [S.commonSupport_pair] using this
        _ = 6 := by simp [hcardErase]
        _ = (if b ∈ D then 5 else 6) := by simp [hbD]
  have hsumSupport (b : Block) (hb : b ∈ F) :
      (∑ p ∈ S.support b, S.blockDegree 5 p) =
        5 + (if b ∈ D then 5 else 6) := by
    have hfubini := sum_degreeIn_over_support S F b
    change (∑ p ∈ S.support b, S.blockDegree 5 p) =
      ∑ c ∈ F, (S.support b ∩ S.support c).card at hfubini
    rw [hfubini]
    have hsplit := Finset.sum_erase_add F
      (fun c => (S.support b ∩ S.support c).card) hb
    have hself : (S.support b ∩ S.support b).card = 5 := by
      simp [S.mem_blocksOfSize.mp hb]
    change (∑ c ∈ F.erase b,
      (S.support b ∩ S.support c).card) +
        (S.support b ∩ S.support b).card =
          ∑ c ∈ F, (S.support b ∩ S.support c).card at hsplit
    rw [hpairRow b hb, hself] at hsplit
    omega
  have hTb₀ : T ∈ S.support b₀ := by
    by_contra hTnot
    have hrestCard : ((S.support b₀).erase U).card = 4 := by
      rw [Finset.card_erase_of_mem hUb₀,
        S.mem_blocksOfSize.mp hb₀]
    have hrestDegree (p : Point) (hp : p ∈ (S.support b₀).erase U) :
        S.blockDegree 5 p = 2 := by
      have hp' := Finset.mem_erase.mp hp
      exact hdegreeBaseline p hp'.1
        (fun hpT => hTnot (hpT ▸ hp'.2))
    have hrestSum :
        (∑ p ∈ (S.support b₀).erase U, S.blockDegree 5 p) = 8 := by
      calc
        _ = ∑ _p ∈ (S.support b₀).erase U, 2 := by
          apply Finset.sum_congr rfl
          intro p hp
          exact hrestDegree p hp
        _ = 8 := by simp [hrestCard]
    have hsum9 : (∑ p ∈ S.support b₀, S.blockDegree 5 p) = 9 := by
      have hsplit := Finset.sum_erase_add (S.support b₀)
        (fun p => S.blockDegree 5 p) hUb₀
      change (∑ p ∈ (S.support b₀).erase U,
          S.blockDegree 5 p) + S.blockDegree 5 U =
        ∑ p ∈ S.support b₀, S.blockDegree 5 p at hsplit
      rw [hrestSum, hUdegree] at hsplit
      omega
    have := hsumSupport b₀ hb₀
    by_cases h : b₀ ∈ D <;> simp [h] at this <;> omega
  have hsumB₀ : (∑ p ∈ S.support b₀, S.blockDegree 5 p) = 10 := by
    have hTErase : T ∈ (S.support b₀).erase U :=
      Finset.mem_erase.mpr ⟨hTU, hTb₀⟩
    have hrestCard : (((S.support b₀).erase U).erase T).card = 3 := by
      rw [Finset.card_erase_of_mem hTErase,
        Finset.card_erase_of_mem hUb₀,
        S.mem_blocksOfSize.mp hb₀]
    have hrestDegree (p : Point)
        (hp : p ∈ ((S.support b₀).erase U).erase T) :
        S.blockDegree 5 p = 2 := by
      have hp' := Finset.mem_erase.mp hp
      have hp'' := Finset.mem_erase.mp hp'.2
      exact hdegreeBaseline p hp''.1 hp'.1
    have hrestSum :
        (∑ p ∈ ((S.support b₀).erase U).erase T,
          S.blockDegree 5 p) = 6 := by
      calc
        _ = ∑ _p ∈ ((S.support b₀).erase U).erase T, 2 := by
          apply Finset.sum_congr rfl
          intro p hp
          exact hrestDegree p hp
        _ = 6 := by simp [hrestCard]
    have hsplitT := Finset.sum_erase_add ((S.support b₀).erase U)
      (fun p => S.blockDegree 5 p) hTErase
    have hsplitU := Finset.sum_erase_add (S.support b₀)
      (fun p => S.blockDegree 5 p) hUb₀
    change (∑ p ∈ ((S.support b₀).erase U).erase T,
        S.blockDegree 5 p) + S.blockDegree 5 T =
      ∑ p ∈ (S.support b₀).erase U,
        S.blockDegree 5 p at hsplitT
    change (∑ p ∈ (S.support b₀).erase U,
        S.blockDegree 5 p) + S.blockDegree 5 U =
      ∑ p ∈ S.support b₀, S.blockDegree 5 p at hsplitU
    rw [hrestSum, hTdegree] at hsplitT
    rw [hUdegree] at hsplitU
    omega
  have hb₀D : b₀ ∈ D := by
    have := hsumSupport b₀ hb₀
    by_cases h : b₀ ∈ D <;> simp [h] at this <;> omega
  obtain ⟨b₃, hb₃D, hb₃ne₀⟩ : ∃ b₃ ∈ D, b₃ ≠ b₀ := by
    have hb₀D' := hb₀D
    rw [hDeq] at hb₀D'
    simp only [Finset.mem_insert, Finset.mem_singleton] at hb₀D'
    rcases hb₀D' with hb₀eq | hb₀eq
    · refine ⟨d₁, ?_, ?_⟩
      · rw [hDeq]
        exact Finset.mem_insert_of_mem (Finset.mem_singleton_self d₁)
      · intro h
        exact hd₀ne₁ (hb₀eq.symm.trans h.symm)
    · refine ⟨d₀, ?_, ?_⟩
      · rw [hDeq]
        exact Finset.mem_insert_self d₀ {d₁}
      · intro h
        exact hd₀ne₁ (h.trans hb₀eq)
  have hb₃ : b₃ ∈ F := hDsub hb₃D
  have hDcard : D.card = 2 := (Finset.mem_powersetCard.mp hD).2
  have hD03 : ({b₀, b₃} : Finset Block) = D := by
    apply Finset.eq_of_subset_of_card_le
    · intro b hb
      simp only [Finset.mem_insert, Finset.mem_singleton] at hb
      rcases hb with rfl | rfl
      · exact hb₀D
      · exact hb₃D
    · rw [hDcard]
      have hb₀not : b₀ ∉ ({b₃} : Finset Block) := by
        simpa only [Finset.mem_singleton] using Ne.symm hb₃ne₀
      rw [Finset.card_insert_of_notMem hb₀not,
        Finset.card_singleton]
  have hUb₃ : U ∉ S.support b₃ := hUnot b₃ hb₃ hb₃ne₀
  have hTb₃ : T ∉ S.support b₃ := by
    intro hT
    have hrestCard : ((S.support b₃).erase T).card = 4 := by
      rw [Finset.card_erase_of_mem hT,
        S.mem_blocksOfSize.mp hb₃]
    have hrestDegree (p : Point) (hp : p ∈ (S.support b₃).erase T) :
        S.blockDegree 5 p = 2 := by
      have hp' := Finset.mem_erase.mp hp
      exact hdegreeBaseline p
        (fun hpU => hUb₃ (hpU ▸ hp'.2)) hp'.1
    have hrestSum :
        (∑ p ∈ (S.support b₃).erase T, S.blockDegree 5 p) = 8 := by
      calc
        _ = ∑ _p ∈ (S.support b₃).erase T, 2 := by
          apply Finset.sum_congr rfl
          intro p hp
          exact hrestDegree p hp
        _ = 8 := by simp [hrestCard]
    have hsum11 : (∑ p ∈ S.support b₃, S.blockDegree 5 p) = 11 := by
      have hsplit := Finset.sum_erase_add (S.support b₃)
        (fun p => S.blockDegree 5 p) hT
      change (∑ p ∈ (S.support b₃).erase T,
          S.blockDegree 5 p) + S.blockDegree 5 T =
        ∑ p ∈ S.support b₃, S.blockDegree 5 p at hsplit
      rw [hrestSum, hTdegree] at hsplit
      omega
    have := hsumSupport b₃ hb₃
    simp [hb₃D] at this
    omega
  let R := (F.erase b₀).erase b₃
  have hRcard : R.card = 2 := by
    have hb₃erase : b₃ ∈ F.erase b₀ :=
      Finset.mem_erase.mpr ⟨hb₃ne₀, hb₃⟩
    rw [Finset.card_erase_of_mem hb₃erase,
      Finset.card_erase_of_mem hb₀, hFcard]
  obtain ⟨b₁, b₂, hb₁ne₂, hReq⟩ := Finset.card_eq_two.mp hRcard
  have hb₁R : b₁ ∈ R := by rw [hReq]; simp
  have hb₂R : b₂ ∈ R := by rw [hReq]; simp
  have hb₁ : b₁ ∈ F := Finset.mem_of_mem_erase
    (Finset.mem_of_mem_erase hb₁R)
  have hb₂ : b₂ ∈ F := Finset.mem_of_mem_erase
    (Finset.mem_of_mem_erase hb₂R)
  have hb₁ne₀ : b₁ ≠ b₀ := (Finset.mem_erase.mp
    (Finset.mem_of_mem_erase hb₁R)).1
  have hb₂ne₀ : b₂ ≠ b₀ := (Finset.mem_erase.mp
    (Finset.mem_of_mem_erase hb₂R)).1
  have hb₁ne₃ : b₁ ≠ b₃ := (Finset.mem_erase.mp hb₁R).1
  have hb₂ne₃ : b₂ ≠ b₃ := (Finset.mem_erase.mp hb₂R).1
  have hb₁notD : b₁ ∉ D := by
    intro hbD
    rw [← hD03] at hbD
    simp only [Finset.mem_insert, Finset.mem_singleton] at hbD
    rcases hbD with hb₁eq | hb₁eq
    · exact hb₁ne₀ hb₁eq
    · exact hb₁ne₃ hb₁eq
  have hb₂notD : b₂ ∉ D := by
    intro hbD
    rw [← hD03] at hbD
    simp only [Finset.mem_insert, Finset.mem_singleton] at hbD
    rcases hbD with hb₂eq | hb₂eq
    · exact hb₂ne₀ hb₂eq
    · exact hb₂ne₃ hb₂eq
  have hFcases (b : Block) (hb : b ∈ F) :
      b = b₀ ∨ b = b₁ ∨ b = b₂ ∨ b = b₃ := by
    by_cases hb₀' : b = b₀
    · exact Or.inl hb₀'
    by_cases hb₃' : b = b₃
    · exact Or.inr (Or.inr (Or.inr hb₃'))
    have hbR : b ∈ R := Finset.mem_erase.mpr ⟨hb₃',
      Finset.mem_erase.mpr ⟨hb₀', hb⟩⟩
    rw [hReq] at hbR
    simp only [Finset.mem_insert, Finset.mem_singleton] at hbR
    rcases hbR with hb₁' | hb₂'
    · exact Or.inr (Or.inl hb₁')
    · exact Or.inr (Or.inr (Or.inl hb₂'))
  have hTb (b : Block) (hb : b ∈ F) (hbne₀ : b ≠ b₀)
      (hbnotD : b ∉ D) : T ∈ S.support b := by
    have hUb : U ∉ S.support b := hUnot b hb hbne₀
    by_contra hTnot
    have hpoint (p : Point) (hp : p ∈ S.support b) :
        S.blockDegree 5 p = 2 :=
      hdegreeBaseline p (fun hpU => hUb (hpU ▸ hp))
        (fun hpT => hTnot (hpT ▸ hp))
    have hsum10 : (∑ p ∈ S.support b, S.blockDegree 5 p) = 10 := by
      calc
        _ = ∑ _p ∈ S.support b, 2 := by
          apply Finset.sum_congr rfl
          intro p hp
          exact hpoint p hp
        _ = 10 := by simp [S.mem_blocksOfSize.mp hb]
    have := hsumSupport b hb
    simp [hbnotD] at this
    omega
  have hTb₁ : T ∈ S.support b₁ := hTb b₁ hb₁ hb₁ne₀ hb₁notD
  have hTb₂ : T ∈ S.support b₂ := hTb b₂ hb₂ hb₂ne₀ hb₂notD
  have hinter₁₃ : (S.support b₁ ∩ S.support b₃).card = 2 := by
    have hpairMem : ({b₁, b₃} : Finset Block) ∈ F.powersetCard 2 := by
      apply Finset.mem_powersetCard.mpr
      constructor
      · intro b hb
        simp only [Finset.mem_insert, Finset.mem_singleton] at hb
        rcases hb with rfl | rfl
        · exact hb₁
        · exact hb₃
      · simp [hb₁ne₃]
    have hneD : ({b₁, b₃} : Finset Block) ≠ D := by
      intro h
      apply hb₁notD
      rw [← h]
      simp
    have := hDother {b₁, b₃} hpairMem hneD
    simpa [S.commonSupport_pair] using this
  have hinter₂₃ : (S.support b₂ ∩ S.support b₃).card = 2 := by
    have hpairMem : ({b₂, b₃} : Finset Block) ∈ F.powersetCard 2 := by
      apply Finset.mem_powersetCard.mpr
      constructor
      · intro b hb
        simp only [Finset.mem_insert, Finset.mem_singleton] at hb
        rcases hb with rfl | rfl
        · exact hb₂
        · exact hb₃
      · simp [hb₂ne₃]
    have hneD : ({b₂, b₃} : Finset Block) ≠ D := by
      intro h
      apply hb₂notD
      rw [← h]
      simp
    have := hDother {b₂, b₃} hpairMem hneD
    simpa [S.commonSupport_pair] using this
  let X := S.support b₁ ∩ S.support b₃
  let Y := S.support b₂ ∩ S.support b₃
  have hXcard : X.card = 2 := hinter₁₃
  have hYcard : Y.card = 2 := hinter₂₃
  let H := (S.blocksOfSize 4).filter fun q => T ∈ S.support q
  have hcommon (q : Block) (hq : q ∈ H) : U ∈ S.support q := by
    have hq' := Finset.mem_filter.mp hq
    by_contra hUnotq
    have hsumLower : 9 ≤ ∑ p ∈ S.support q, S.blockDegree 5 p := by
      have hrest : 6 ≤ ∑ p ∈ (S.support q).erase T,
          S.blockDegree 5 p := by
        calc
          6 = ∑ _p ∈ (S.support q).erase T, 2 := by
            simp [Finset.card_erase_of_mem hq'.2,
              S.mem_blocksOfSize.mp hq'.1]
          _ ≤ _ := by
            apply Finset.sum_le_sum
            intro p hp
            have hpneT := (Finset.mem_erase.mp hp).1
            have hpneU : p ≠ U := by
              intro h; subst p
              exact hUnotq (Finset.mem_of_mem_erase hp)
            rcases hprofile p with h1 | h2 | h3
            · have hpLow : p ∈ ((Finset.univ : Finset Point).filter
                  fun z => S.blockDegree 5 z = 1) := by simp [h1]
              rw [hUeq] at hpLow
              exact (hpneU (by simpa using hpLow)).elim
            · omega
            · omega
      have hsplit := Finset.sum_erase_add (S.support q)
        (fun p => S.blockDegree 5 p) hq'.2
      change (∑ p ∈ (S.support q).erase T, S.blockDegree 5 p) +
        S.blockDegree 5 T =
          ∑ p ∈ S.support q, S.blockDegree 5 p at hsplit
      rw [hTdegree] at hsplit
      omega
    have hsumUpper :
        (∑ b ∈ F, (S.support q ∩ S.support b).card) ≤ 8 := by
      calc
        _ ≤ ∑ _b ∈ F, 2 := by
          apply Finset.sum_le_sum
          intro b hb
          have hqb : q ≠ b := by
            intro h
            have hqsize := S.mem_blocksOfSize.mp hq'.1
            have hbsize := S.mem_blocksOfSize.mp hb
            rw [h] at hqsize
            omega
          have hinter := S.distinct_block_inter_card_lt_three hqb
          omega
        _ = 8 := by simp [hFcard]
    have hfubini := sum_degreeIn_over_support S F q
    change (∑ p ∈ S.support q, S.blockDegree 5 p) = _ at hfubini
    omega
  have hawayXY (q : Block) (hq : q ∈ H) :
      ((S.support q \ {T, U}) ∩ X).card = 1 ∧
      ((S.support q \ {T, U}) ∩ Y).card = 1 := by
    have hq' := Finset.mem_filter.mp hq
    have hUq := hcommon q hq
    have hqne (b : Block) (hb : b ∈ F) : q ≠ b := by
      intro h
      have hqsize := S.mem_blocksOfSize.mp hq'.1
      have hbsize := S.mem_blocksOfSize.mp hb
      rw [h] at hqsize
      omega
    have hinterCap (b : Block) (hb : b ∈ F) :
        (S.support q ∩ S.support b).card ≤ 2 := by
      have h := S.distinct_block_inter_card_lt_three (hqne b hb)
      omega
    have hpairSub : ({T, U} : Finset Point) ⊆ S.support q := by
      intro p hp
      simp only [Finset.mem_insert, Finset.mem_singleton] at hp
      rcases hp with rfl | rfl
      · exact hq'.2
      · exact hUq
    have hpairCard : ({T, U} : Finset Point).card = 2 := by
      simp [hTU]
    have hawayCard : (S.support q \ {T, U}).card = 2 := by
      rw [Finset.card_sdiff_of_subset hpairSub,
        S.mem_blocksOfSize.mp hq'.1, hpairCard]
    have hcardTUp (p : Point) (hpT : p ≠ T) (hpU : p ≠ U) :
        ({T, U, p} : Finset Point).card = 3 := by
      have hTnot : T ∉ ({U, p} : Finset Point) := by
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨hTU, Ne.symm hpT⟩
      have hUnot : U ∉ ({p} : Finset Point) := by
        simpa only [Finset.mem_singleton] using Ne.symm hpU
      rw [Finset.card_insert_of_notMem hTnot,
        Finset.card_insert_of_notMem hUnot]
      rfl
    have hcardTpz (p z : Point) (hpT : p ≠ T) (hzT : z ≠ T)
        (hpz : p ≠ z) :
        ({T, p, z} : Finset Point).card = 3 := by
      have hTnot : T ∉ ({p, z} : Finset Point) := by
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨Ne.symm hpT, Ne.symm hzT⟩
      have hpnot : p ∉ ({z} : Finset Point) := by
        simpa only [Finset.mem_singleton] using hpz
      rw [Finset.card_insert_of_notMem hTnot,
        Finset.card_insert_of_notMem hpnot]
      rfl
    have hawayNeT (p : Point) (hp : p ∈ S.support q \ {T, U}) :
        p ≠ T := by
      intro h
      subst p
      exact (Finset.mem_sdiff.mp hp).2
        (Finset.mem_insert_self T {U})
    have hawayNeU (p : Point) (hp : p ∈ S.support q \ {T, U}) :
        p ≠ U := by
      intro h
      subst p
      exact (Finset.mem_sdiff.mp hp).2
        (Finset.mem_insert_of_mem (Finset.mem_singleton_self U))
    have hnotB₀ (p : Point) (hp : p ∈ S.support q \ {T, U}) :
        p ∉ S.support b₀ := by
      intro hpb₀
      have hpq := (Finset.mem_sdiff.mp hp).1
      have hpT := hawayNeT p hp
      have hpU := hawayNeU p hp
      have hsub : ({T, U, p} : Finset Point) ⊆
          S.support q ∩ S.support b₀ := by
        intro z hz
        simp only [Finset.mem_insert, Finset.mem_singleton] at hz
        rcases hz with rfl | rfl | rfl
        · exact Finset.mem_inter.mpr ⟨hq'.2, hTb₀⟩
        · exact Finset.mem_inter.mpr ⟨hUq, hUb₀⟩
        · exact Finset.mem_inter.mpr ⟨hpq, hpb₀⟩
      have hcardLe := Finset.card_le_card hsub
      rw [hcardTUp p hpT hpU] at hcardLe
      have hcap₀ := hinterCap b₀ hb₀
      omega
    have hawayDegree (p : Point) (hp : p ∈ S.support q \ {T, U}) :
        S.blockDegree 5 p = 2 :=
      hdegreeBaseline p (hawayNeU p hp) (hawayNeT p hp)
    have hnotOnlyOne (p : Point) (hp : p ∈ S.support q \ {T, U})
        (a : Block)
        (honly : ∀ b ∈ F, p ∈ S.support b → b = a) : False := by
      have hsub :
          (F.filter fun b => p ∈ S.support b) ⊆ ({a} : Finset Block) := by
        intro b hb
        exact Finset.mem_singleton.mpr
          (honly b (Finset.mem_filter.mp hb).1
            (Finset.mem_filter.mp hb).2)
      have hle := Finset.card_le_card hsub
      have hdegree := hawayDegree p hp
      change (F.filter fun b => p ∈ S.support b).card = 2 at hdegree
      rw [hdegree] at hle
      have hsingle : ({a} : Finset Block).card = 1 := by
        exact Finset.card_singleton a
      rw [hsingle] at hle
      omega
    have hnoTwelve (p : Point) (hp : p ∈ S.support q \ {T, U}) :
        ¬(p ∈ S.support b₁ ∧ p ∈ S.support b₂) := by
      rintro ⟨hpb₁, hpb₂⟩
      have hotherCard : ((S.support q \ {T, U}).erase p).card = 1 := by
        rw [Finset.card_erase_of_mem hp, hawayCard]
      obtain ⟨z, hzEq⟩ := Finset.card_eq_one.mp hotherCard
      have hzOther : z ∈ (S.support q \ {T, U}).erase p := by
        rw [hzEq]
        exact Finset.mem_singleton_self z
      have hzAway : z ∈ S.support q \ {T, U} :=
        Finset.mem_of_mem_erase hzOther
      have hzNeP : z ≠ p := (Finset.mem_erase.mp hzOther).1
      have hpNeZ : p ≠ z := Ne.symm hzNeP
      have hpT := hawayNeT p hp
      have hzT := hawayNeT z hzAway
      have hpq := (Finset.mem_sdiff.mp hp).1
      have hzq := (Finset.mem_sdiff.mp hzAway).1
      have hznot₁ : z ∉ S.support b₁ := by
        intro hzb₁
        have hsub : ({T, p, z} : Finset Point) ⊆
            S.support q ∩ S.support b₁ := by
          intro w hw
          simp only [Finset.mem_insert, Finset.mem_singleton] at hw
          rcases hw with rfl | rfl | rfl
          · exact Finset.mem_inter.mpr ⟨hq'.2, hTb₁⟩
          · exact Finset.mem_inter.mpr ⟨hpq, hpb₁⟩
          · exact Finset.mem_inter.mpr ⟨hzq, hzb₁⟩
        have hcardLe := Finset.card_le_card hsub
        rw [hcardTpz p z hpT hzT hpNeZ] at hcardLe
        have hcap₁ := hinterCap b₁ hb₁
        omega
      have hznot₂ : z ∉ S.support b₂ := by
        intro hzb₂
        have hsub : ({T, p, z} : Finset Point) ⊆
            S.support q ∩ S.support b₂ := by
          intro w hw
          simp only [Finset.mem_insert, Finset.mem_singleton] at hw
          rcases hw with rfl | rfl | rfl
          · exact Finset.mem_inter.mpr ⟨hq'.2, hTb₂⟩
          · exact Finset.mem_inter.mpr ⟨hpq, hpb₂⟩
          · exact Finset.mem_inter.mpr ⟨hzq, hzb₂⟩
        have hcardLe := Finset.card_le_card hsub
        rw [hcardTpz p z hpT hzT hpNeZ] at hcardLe
        have hcap₂ := hinterCap b₂ hb₂
        omega
      apply hnotOnlyOne z hzAway b₃
      intro b hb hzb
      rcases hFcases b hb with hb₀' | hb₁' | hb₂' | hb₃'
      · exact (hnotB₀ z hzAway (hb₀' ▸ hzb)).elim
      · exact (hznot₁ (hb₁' ▸ hzb)).elim
      · exact (hznot₂ (hb₂' ▸ hzb)).elim
      · exact hb₃'
    have hlabels (p : Point) (hp : p ∈ S.support q \ {T, U}) :
        p ∈ X ∪ Y := by
      have hpnot₀ := hnotB₀ p hp
      by_cases hpb₁ : p ∈ S.support b₁
      · have hpnot₂ : p ∉ S.support b₂ :=
          fun hpb₂ => hnoTwelve p hp ⟨hpb₁, hpb₂⟩
        have hpb₃ : p ∈ S.support b₃ := by
          by_contra hpnot₃
          apply hnotOnlyOne p hp b₁
          intro b hb hpb
          rcases hFcases b hb with hb₀' | hb₁' | hb₂' | hb₃'
          · exact (hpnot₀ (hb₀' ▸ hpb)).elim
          · exact hb₁'
          · exact (hpnot₂ (hb₂' ▸ hpb)).elim
          · exact (hpnot₃ (hb₃' ▸ hpb)).elim
        apply Finset.mem_union.mpr
        left
        exact Finset.mem_inter.mpr ⟨hpb₁, hpb₃⟩
      · have hpb₂ : p ∈ S.support b₂ := by
          by_contra hpnot₂
          apply hnotOnlyOne p hp b₃
          intro b hb hpb
          rcases hFcases b hb with hb₀' | hb₁' | hb₂' | hb₃'
          · exact (hpnot₀ (hb₀' ▸ hpb)).elim
          · exact (hpb₁ (hb₁' ▸ hpb)).elim
          · exact (hpnot₂ (hb₂' ▸ hpb)).elim
          · exact hb₃'
        have hpb₃ : p ∈ S.support b₃ := by
          by_contra hpnot₃
          apply hnotOnlyOne p hp b₂
          intro b hb hpb
          rcases hFcases b hb with hb₀' | hb₁' | hb₂' | hb₃'
          · exact (hpnot₀ (hb₀' ▸ hpb)).elim
          · exact (hpb₁ (hb₁' ▸ hpb)).elim
          · exact hb₂'
          · exact (hpnot₃ (hb₃' ▸ hpb)).elim
        apply Finset.mem_union.mpr
        right
        exact Finset.mem_inter.mpr ⟨hpb₂, hpb₃⟩
    have hcover : S.support q \ {T, U} =
        ((S.support q \ {T, U}) ∩ X) ∪
          ((S.support q \ {T, U}) ∩ Y) := by
      ext p
      constructor
      · intro hp
        rcases Finset.mem_union.mp (hlabels p hp) with hpX | hpY
        · exact Finset.mem_union.mpr
            (Or.inl (Finset.mem_inter.mpr ⟨hp, hpX⟩))
        · exact Finset.mem_union.mpr
            (Or.inr (Finset.mem_inter.mpr ⟨hp, hpY⟩))
      · intro hp
        rcases Finset.mem_union.mp hp with hpX | hpY
        · exact (Finset.mem_inter.mp hpX).1
        · exact (Finset.mem_inter.mp hpY).1
    have hparts :
        2 ≤ ((S.support q \ {T, U}) ∩ X).card +
          ((S.support q \ {T, U}) ∩ Y).card := by
      have hle := Finset.card_union_le
        ((S.support q \ {T, U}) ∩ X)
        ((S.support q \ {T, U}) ∩ Y)
      rw [← hcover, hawayCard] at hle
      exact hle
    have hXle : ((S.support q \ {T, U}) ∩ X).card ≤ 1 := by
      by_contra hnot
      have htwo : 2 ≤ ((S.support q \ {T, U}) ∩ X).card := by
        omega
      obtain ⟨A, hAsub, hAcard⟩ := Finset.exists_subset_card_eq htwo
      have hthree : insert T A ⊆ S.support q ∩ S.support b₁ := by
        intro p hp
        simp only [Finset.mem_insert] at hp
        rcases hp with rfl | hp
        · exact Finset.mem_inter.mpr ⟨hq'.2, hTb₁⟩
        · have hp' := hAsub hp
          exact Finset.mem_inter.mpr ⟨
            (Finset.mem_sdiff.mp (Finset.mem_inter.mp hp').1).1,
            (Finset.mem_inter.mp (Finset.mem_inter.mp hp').2).1⟩
      have hTnotA : T ∉ A := by
        intro h
        have h' := hAsub h
        exact (Finset.mem_sdiff.mp (Finset.mem_inter.mp h').1).2
          (Finset.mem_insert_self T {U})
      have hcard3 : (insert T A).card = 3 := by
        rw [Finset.card_insert_of_notMem hTnotA, hAcard]
      have hcardLe := Finset.card_le_card hthree
      rw [hcard3] at hcardLe
      have hcap₁ := hinterCap b₁ hb₁
      omega
    have hYle : ((S.support q \ {T, U}) ∩ Y).card ≤ 1 := by
      by_contra hnot
      have htwo : 2 ≤ ((S.support q \ {T, U}) ∩ Y).card := by
        omega
      obtain ⟨A, hAsub, hAcard⟩ := Finset.exists_subset_card_eq htwo
      have hthree : insert T A ⊆ S.support q ∩ S.support b₂ := by
        intro p hp
        simp only [Finset.mem_insert] at hp
        rcases hp with rfl | hp
        · exact Finset.mem_inter.mpr ⟨hq'.2, hTb₂⟩
        · have hp' := hAsub hp
          exact Finset.mem_inter.mpr ⟨
            (Finset.mem_sdiff.mp (Finset.mem_inter.mp hp').1).1,
            (Finset.mem_inter.mp (Finset.mem_inter.mp hp').2).1⟩
      have hTnotA : T ∉ A := by
        intro h
        have h' := hAsub h
        exact (Finset.mem_sdiff.mp (Finset.mem_inter.mp h').1).2
          (Finset.mem_insert_self T {U})
      have hcard3 : (insert T A).card = 3 := by
        rw [Finset.card_insert_of_notMem hTnotA, hAcard]
      have hcardLe := Finset.card_le_card hthree
      rw [hcard3] at hcardLe
      have hcap₂ := hinterCap b₂ hb₂
      omega
    omega

  let Pick : {q : Block // q ∈ H} → {p : Point // p ∈ X} := fun q => by
    have hcard := (hawayXY q.1 q.2).1
    exact ⟨Classical.choose (Finset.card_pos.mp (by omega :
      0 < ((S.support q.1 \ {T, U}) ∩ X).card)),
      (Finset.mem_inter.mp (Classical.choose_spec
        (Finset.card_pos.mp (by omega :
          0 < ((S.support q.1 \ {T, U}) ∩ X).card)))).2⟩
  have hPickMem (q : {q : Block // q ∈ H}) :
      (Pick q : Point) ∈ (S.support q.1 \ {T, U}) ∩ X := by
    exact Classical.choose_spec (Finset.card_pos.mp
      (by have := (hawayXY q.1 q.2).1; omega :
        0 < ((S.support q.1 \ {T, U}) ∩ X).card))
  have hPickInj : Function.Injective Pick := by
    intro q r hqr
    apply Subtype.ext
    apply support_injOn_blocksOfSize S 4 (by omega)
      (Finset.mem_filter.mp q.2).1 (Finset.mem_filter.mp r.2).1
    by_contra hsupp
    have hqT := (Finset.mem_filter.mp q.2).2
    have hrT := (Finset.mem_filter.mp r.2).2
    have hqU := hcommon q.1 q.2
    have hrU := hcommon r.1 r.2
    have hpq := (Finset.mem_sdiff.mp (Finset.mem_inter.mp
      (hPickMem q)).1).1
    have hpr := (Finset.mem_sdiff.mp (Finset.mem_inter.mp
      (hPickMem r)).1).1
    have hpne := (Finset.mem_sdiff.mp (Finset.mem_inter.mp
      (hPickMem q)).1).2
    have hpneT : (Pick q : Point) ≠ T := by
      intro h
      apply hpne
      rw [h]
      exact Finset.mem_insert_self T {U}
    have hpneU : (Pick q : Point) ≠ U := by
      intro h
      apply hpne
      rw [h]
      exact Finset.mem_insert_of_mem (Finset.mem_singleton_self U)
    have hpr' : (Pick q : Point) ∈ S.support r.1 := by
      rw [hqr]
      exact hpr
    have hsub : ({T, U, (Pick q : Point)} : Finset Point) ⊆
        S.support q.1 ∩ S.support r.1 := by
      intro p hp
      simp only [Finset.mem_insert, Finset.mem_singleton] at hp
      rcases hp with rfl | rfl | rfl
      · exact Finset.mem_inter.mpr ⟨hqT, hrT⟩
      · exact Finset.mem_inter.mpr ⟨hqU, hrU⟩
      · exact Finset.mem_inter.mpr ⟨hpq, hpr'⟩
    have hcard3 : ({T, U, (Pick q : Point)} : Finset Point).card = 3 := by
      have hTnot : T ∉ ({U, (Pick q : Point)} : Finset Point) := by
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨hTU, Ne.symm hpneT⟩
      have hUnot : U ∉ ({(Pick q : Point)} : Finset Point) := by
        simpa only [Finset.mem_singleton] using Ne.symm hpneU
      rw [Finset.card_insert_of_notMem hTnot,
        Finset.card_insert_of_notMem hUnot]
      rfl
    have hcardLe := Finset.card_le_card hsub
    have hinter := S.distinct_block_inter_card_lt_three (by
      intro h; apply hsupp; exact congrArg S.support h)
    omega
  have hcardH : H.card ≤ 2 := by
    have hle := Fintype.card_le_of_injective Pick hPickInj
    simpa only [Fintype.card_coe, hXcard] using hle
  have hpairs := ten_pair_row S hPoint hcap T
  change S.blockDegree 4 T ≤ 2 at hcardH
  rw [hTdegree] at hpairs
  rcases hd3 T with hT3 | hT3 <;> rw [hT3] at hpairs <;> omega


end FourPentagonRowEleven

end Erdos506.Finite
