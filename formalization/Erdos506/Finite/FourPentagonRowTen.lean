import Erdos506.Finite.FourPentagonProfile

/-!
# Elimination of the second-moment ten row
-/

namespace Erdos506.Finite

open Erdos506.Block
open Erdos506.Block.BlockSystem
open scoped BigOperators
open FourPentagonProfile

namespace FourPentagonRowTen

theorem secondMoment_ten_row_impossible
    {Point Block : Type*} [Fintype Point] [Fintype Block]
    [DecidableEq Point]
    (S : BlockSystem Point Block) (hPoint : Fintype.card Point = 10)
    (hcap : ∀ b : Block, 3 ≤ (S.support b).card →
      (S.support b).card ≤ 5)
    (hd3 : ∀ p : Point, S.blockDegree 3 p = 6 ∨
      S.blockDegree 3 p = 9)
    (hfive : S.blockCount 5 = 4)
    (hrow : ∀ p : Point, S.blockDegree 5 p = 2) : False := by
  classical
  let F := S.blocksOfSize 5
  have hFcard : F.card = 4 := hfive
  obtain ⟨b₀, hb₀⟩ : F.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro h
    have := congrArg Finset.card h
    simp [hFcard] at this
  have hinterLe (b : Block) (hb : b ∈ F) (c : Block) (hc : c ∈ F)
      (hbc : b ≠ c) : (S.support b ∩ S.support c).card ≤ 2 := by
    have := S.distinct_block_inter_card_lt_three hbc
    omega
  have hpairRow (b : Block) (hb : b ∈ F) :
      (∑ c ∈ F.erase b, (S.support b ∩ S.support c).card) = 5 := by
    have hleft : (∑ x ∈ S.support b, S.blockDegree 5 x) = 10 := by
      calc
        _ = ∑ _x ∈ S.support b, 2 := by
          apply Finset.sum_congr rfl
          intro x hx
          exact hrow x
        _ = 10 := by simp [S.mem_blocksOfSize.mp hb]
    have hfubini := sum_degreeIn_over_support S F b
    change (∑ x ∈ S.support b, S.blockDegree 5 x) = _ at hfubini
    rw [hleft] at hfubini
    have hsplit := Finset.sum_erase_add F
      (fun c => (S.support b ∩ S.support c).card) hb
    have hself : (S.support b ∩ S.support b).card = 5 := by
      simp [S.mem_blocksOfSize.mp hb]
    change (∑ c ∈ F.erase b,
      (S.support b ∩ S.support c).card) +
        (S.support b ∩ S.support b).card =
          ∑ c ∈ F, (S.support b ∩ S.support c).card at hsplit
    rw [hself] at hsplit
    omega
  have hdeficient (b : Block) (hb : b ∈ F) :
      ∃ c ∈ F.erase b,
        (S.support b ∩ S.support c).card = 1 ∧
        ∀ d ∈ F.erase b, d ≠ c →
          (S.support b ∩ S.support d).card = 2 := by
    have hcard : (F.erase b).card = 3 := by
      rw [Finset.card_erase_of_mem hb, hFcard]
    apply card_three_sum_five_le_two
      (F.erase b) (fun c => (S.support b ∩ S.support c).card)
      hcard
    · intro c hc
      exact hinterLe b hb c (Finset.mem_of_mem_erase hc)
        (Finset.mem_erase.mp hc).1.symm
    · exact hpairRow b hb
  obtain ⟨b₁, hb₁erase, hb₀₁, hb₀other⟩ := hdeficient b₀ hb₀
  have hb₁ : b₁ ∈ F := Finset.mem_of_mem_erase hb₁erase
  have hb₀ne₁ : b₀ ≠ b₁ := (Finset.mem_erase.mp hb₁erase).1.symm
  let R := (F.erase b₀).erase b₁
  have hRcard : R.card = 2 := by
    rw [Finset.card_erase_of_mem hb₁erase,
      Finset.card_erase_of_mem hb₀, hFcard]
  obtain ⟨b₂, b₃, hb₂ne₃, hReq⟩ := Finset.card_eq_two.mp hRcard
  have hb₂R : b₂ ∈ R := by rw [hReq]; simp
  have hb₃R : b₃ ∈ R := by rw [hReq]; simp
  have hb₂ : b₂ ∈ F := Finset.mem_of_mem_erase
    (Finset.mem_of_mem_erase hb₂R)
  have hb₃ : b₃ ∈ F := Finset.mem_of_mem_erase
    (Finset.mem_of_mem_erase hb₃R)
  have hb₂ne₀ : b₂ ≠ b₀ := (Finset.mem_erase.mp
    (Finset.mem_of_mem_erase hb₂R)).1
  have hb₃ne₀ : b₃ ≠ b₀ := (Finset.mem_erase.mp
    (Finset.mem_of_mem_erase hb₃R)).1
  have hb₂ne₁ : b₂ ≠ b₁ := (Finset.mem_erase.mp hb₂R).1
  have hb₃ne₁ : b₃ ≠ b₁ := (Finset.mem_erase.mp hb₃R).1
  have hb₀₂ : (S.support b₀ ∩ S.support b₂).card = 2 :=
    hb₀other b₂ (Finset.mem_of_mem_erase hb₂R) hb₂ne₁
  have hb₀₃ : (S.support b₀ ∩ S.support b₃).card = 2 :=
    hb₀other b₃ (Finset.mem_of_mem_erase hb₃R) hb₃ne₁
  obtain ⟨c₁, hc₁, hb₁c₁, hb₁other⟩ := hdeficient b₁ hb₁
  have hc₁eq : c₁ = b₀ := by
    by_contra hne
    have hb₁₀two := hb₁other b₀
      (Finset.mem_erase.mpr ⟨hb₀ne₁, hb₀⟩) (Ne.symm hne)
    have hb₁₀ : (S.support b₁ ∩ S.support b₀).card = 1 := by
      simpa [Finset.inter_comm] using hb₀₁
    omega
  have hb₁₂ : (S.support b₁ ∩ S.support b₂).card = 2 := by
    apply hb₁other b₂ (Finset.mem_erase.mpr ⟨hb₂ne₁, hb₂⟩)
    simpa [hc₁eq] using hb₂ne₀
  have hb₁₃ : (S.support b₁ ∩ S.support b₃).card = 2 := by
    apply hb₁other b₃ (Finset.mem_erase.mpr ⟨hb₃ne₁, hb₃⟩)
    simpa [hc₁eq] using hb₃ne₀
  have hb₂₃ : (S.support b₂ ∩ S.support b₃).card = 1 := by
    have hFerase : F.erase b₂ = {b₀, b₁, b₃} := by
      ext z
      constructor
      · intro hz
        have hzF := Finset.mem_of_mem_erase hz
        have hzne := (Finset.mem_erase.mp hz).1
        have hzRor : z = b₀ ∨ z = b₁ ∨ z ∈ R := by
          by_cases hz0 : z = b₀
          · exact Or.inl hz0
          by_cases hz1 : z = b₁
          · exact Or.inr (Or.inl hz1)
          · exact Or.inr (Or.inr (Finset.mem_erase.mpr ⟨hz1,
              Finset.mem_erase.mpr ⟨hz0, hzF⟩⟩))
        rcases hzRor with rfl | rfl | hzR
        · simp
        · simp
        · rw [hReq] at hzR
          simp only [Finset.mem_insert, Finset.mem_singleton] at hzR
          rcases hzR with rfl | rfl
          · exact (hzne rfl).elim
          · simp
      · intro hz
        simp only [Finset.mem_insert, Finset.mem_singleton] at hz
        rcases hz with rfl | rfl | rfl
        · exact Finset.mem_erase.mpr ⟨hb₂ne₀.symm, hb₀⟩
        · exact Finset.mem_erase.mpr ⟨hb₂ne₁.symm, hb₁⟩
        · exact Finset.mem_erase.mpr ⟨hb₂ne₃.symm, hb₃⟩
    obtain ⟨c₂, hc₂, hb₂c₂, _hb₂other⟩ := hdeficient b₂ hb₂
    have hc₂' : c₂ ∈ ({b₀, b₁, b₃} : Finset Block) := by
      rw [← hFerase]
      exact hc₂
    simp only [Finset.mem_insert, Finset.mem_singleton] at hc₂'
    rcases hc₂' with hc₂₀ | hc₂₁ | hc₂₃
    · have hb₂₀ : (S.support b₂ ∩ S.support b₀).card = 2 := by
        simpa [Finset.inter_comm] using hb₀₂
      rw [hc₂₀] at hb₂c₂
      omega
    · have hb₂₁ : (S.support b₂ ∩ S.support b₁).card = 2 := by
        simpa [Finset.inter_comm] using hb₁₂
      rw [hc₂₁] at hb₂c₂
      omega
    · simpa [hc₂₃] using hb₂c₂
  obtain ⟨x, hx⟩ := Finset.card_eq_one.mp hb₀₁
  obtain ⟨y, hy⟩ := Finset.card_eq_one.mp hb₂₃
  have hxmem : x ∈ S.support b₀ ∩ S.support b₁ := by
    rw [hx]
    exact Finset.mem_singleton_self x
  have hymem : y ∈ S.support b₂ ∩ S.support b₃ := by
    rw [hy]
    exact Finset.mem_singleton_self y
  have hx₀ : x ∈ S.support b₀ := (Finset.mem_inter.mp hxmem).1
  have hx₁ : x ∈ S.support b₁ := (Finset.mem_inter.mp hxmem).2
  have hy₂ : y ∈ S.support b₂ := (Finset.mem_inter.mp hymem).1
  have hy₃ : y ∈ S.support b₃ := (Finset.mem_inter.mp hymem).2
  have hxnot₂ : x ∉ S.support b₂ := by
    intro hx₂
    have hsub : ({b₀, b₁, b₂} : Finset Block) ⊆
        F.filter fun b => x ∈ S.support b := by
      intro b hb
      simp only [Finset.mem_insert, Finset.mem_singleton] at hb
      rcases hb with rfl | rfl | rfl
      · exact Finset.mem_filter.mpr ⟨hb₀, hx₀⟩
      · exact Finset.mem_filter.mpr ⟨hb₁, hx₁⟩
      · exact Finset.mem_filter.mpr ⟨hb₂, hx₂⟩
    have hle := Finset.card_le_card hsub
    have hdistinct : ({b₀, b₁, b₂} : Finset Block).card = 3 := by
      have h0 : b₀ ∉ ({b₁, b₂} : Finset Block) := by
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨hb₀ne₁, fun h => hb₂ne₀ h.symm⟩
      have h1 : b₁ ∉ ({b₂} : Finset Block) := by
        simpa only [Finset.mem_singleton] using Ne.symm hb₂ne₁
      rw [Finset.card_insert_of_notMem h0,
        Finset.card_insert_of_notMem h1]
      rfl
    rw [hdistinct] at hle
    change 3 ≤ S.blockDegree 5 x at hle
    rw [hrow x] at hle
    omega
  have hxnot₃ : x ∉ S.support b₃ := by
    intro hx₃
    have hsub : ({b₀, b₁, b₃} : Finset Block) ⊆
        F.filter fun b => x ∈ S.support b := by
      intro b hb
      simp only [Finset.mem_insert, Finset.mem_singleton] at hb
      rcases hb with rfl | rfl | rfl
      · exact Finset.mem_filter.mpr ⟨hb₀, hx₀⟩
      · exact Finset.mem_filter.mpr ⟨hb₁, hx₁⟩
      · exact Finset.mem_filter.mpr ⟨hb₃, hx₃⟩
    have hle := Finset.card_le_card hsub
    have hdistinct : ({b₀, b₁, b₃} : Finset Block).card = 3 := by
      have h0 : b₀ ∉ ({b₁, b₃} : Finset Block) := by
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨hb₀ne₁, fun h => hb₃ne₀ h.symm⟩
      have h1 : b₁ ∉ ({b₃} : Finset Block) := by
        simpa only [Finset.mem_singleton] using Ne.symm hb₃ne₁
      rw [Finset.card_insert_of_notMem h0,
        Finset.card_insert_of_notMem h1]
      rfl
    rw [hdistinct] at hle
    change 3 ≤ S.blockDegree 5 x at hle
    rw [hrow x] at hle
    omega
  have hxy : x ≠ y := by
    intro h
    subst y
    exact hxnot₂ hy₂
  have hcommon : ∀ q ∈ S.blocksOfSize 4,
      x ∈ S.support q → y ∈ S.support q := by
    intro q hq hxq
    have hqne (b : Block) (hb : b ∈ F) : q ≠ b := by
      intro h
      have hqsize := S.mem_blocksOfSize.mp hq
      have hbsize := S.mem_blocksOfSize.mp hb
      rw [h] at hqsize
      omega
    have hinterQ (b : Block) (hb : b ∈ F) :
        (S.support q ∩ S.support b).card ≤ 2 := by
      have := S.distinct_block_inter_card_lt_three (hqne b hb)
      omega
    have hqsum :
        (∑ b ∈ F, (S.support q ∩ S.support b).card) = 8 := by
      rw [← sum_degreeIn_over_support S F q]
      change (∑ z ∈ S.support q, S.blockDegree 5 z) = 8
      calc
        _ = ∑ _z ∈ S.support q, 2 := by
          apply Finset.sum_congr rfl
          intro z hz
          exact hrow z
        _ = 8 := by simp [S.mem_blocksOfSize.mp hq]
    have hinter₂ : (S.support q ∩ S.support b₂).card = 2 := by
      have hrest :
          (∑ b ∈ F.erase b₂, (S.support q ∩ S.support b).card) ≤ 6 := by
        calc
          _ ≤ ∑ _b ∈ F.erase b₂, 2 := by
            apply Finset.sum_le_sum
            intro b hb
            exact hinterQ b (Finset.mem_of_mem_erase hb)
          _ = 6 := by simp [Finset.card_erase_of_mem hb₂, hFcard]
      have hsplit := Finset.sum_erase_add F
        (fun b => (S.support q ∩ S.support b).card) hb₂
      have hle := hinterQ b₂ hb₂
      change (∑ b ∈ F.erase b₂,
        (S.support q ∩ S.support b).card) +
          (S.support q ∩ S.support b₂).card =
            ∑ b ∈ F, (S.support q ∩ S.support b).card at hsplit
      rw [hqsum] at hsplit
      omega
    have hinter₃ : (S.support q ∩ S.support b₃).card = 2 := by
      have hrest :
          (∑ b ∈ F.erase b₃, (S.support q ∩ S.support b).card) ≤ 6 := by
        calc
          _ ≤ ∑ _b ∈ F.erase b₃, 2 := by
            apply Finset.sum_le_sum
            intro b hb
            exact hinterQ b (Finset.mem_of_mem_erase hb)
          _ = 6 := by simp [Finset.card_erase_of_mem hb₃, hFcard]
      have hsplit := Finset.sum_erase_add F
        (fun b => (S.support q ∩ S.support b).card) hb₃
      have hle := hinterQ b₃ hb₃
      change (∑ b ∈ F.erase b₃,
        (S.support q ∩ S.support b).card) +
          (S.support q ∩ S.support b₃).card =
            ∑ b ∈ F, (S.support q ∩ S.support b).card at hsplit
      rw [hqsum] at hsplit
      omega
    by_contra hynot
    let A := S.support q ∩ S.support b₂
    let B := S.support q ∩ S.support b₃
    have hABdisj : Disjoint A B := by
      rw [Finset.disjoint_left]
      intro z hzA hzB
      have hz₂ : z ∈ S.support b₂ := (Finset.mem_inter.mp hzA).2
      have hz₃ : z ∈ S.support b₃ := (Finset.mem_inter.mp hzB).2
      have : z = y := by
        have hz : z ∈ S.support b₂ ∩ S.support b₃ :=
          Finset.mem_inter.mpr ⟨hz₂, hz₃⟩
        rw [hy] at hz
        simpa using hz
      subst z
      exact hynot (Finset.mem_inter.mp hzA).1
    have hunionCard : (A ∪ B).card = 4 := by
      rw [Finset.card_union_of_disjoint hABdisj]
      simp [A, B, hinter₂, hinter₃]
    have hunionSub : A ∪ B ⊆ (S.support q).erase x := by
      intro z hz
      apply Finset.mem_erase.mpr
      constructor
      · intro hzx
        subst z
        rcases Finset.mem_union.mp hz with hzA | hzB
        · exact hxnot₂ (Finset.mem_inter.mp hzA).2
        · exact hxnot₃ (Finset.mem_inter.mp hzB).2
      · rcases Finset.mem_union.mp hz with hzA | hzB
        · exact (Finset.mem_inter.mp hzA).1
        · exact (Finset.mem_inter.mp hzB).1
    have hcardLe := Finset.card_le_card hunionSub
    rw [hunionCard, Finset.card_erase_of_mem hxq,
      S.mem_blocksOfSize.mp hq] at hcardLe
    omega
  have hfourCap := blockDegree_four_le_four_of_common_pair
    S hPoint x y hxy hcommon
  have hpairs := ten_pair_row S hPoint hcap x
  rw [hrow x] at hpairs
  rcases hd3 x with hx3 | hx3 <;> rw [hx3] at hpairs <;> omega


end FourPentagonRowTen

end Erdos506.Finite
