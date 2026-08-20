import Erdos506.V1.ElevenFiveC39H28ZeroFibrePageCap

/-!
# The host-27 page cap on a proper five-circle

At host weight `27`, the fifteen outside-pair fibres have total defect
three from the universal fibre cap two.  Thus their defect profile is either
one empty and one singleton fibre, or three singleton fibres.  The existing
all-double page obstruction then bounds the number of relative `(1,3)`
pages by six.
-/

namespace Erdos506.V1

open Erdos506.Block
open Erdos506.Block.BlockSystem
open Erdos506.Incidence
open Erdos506.V4

universe u v

/-- The lossless host-pair-fibre profile at host weight `27`. -/
theorem elevenFiveHostPairFibre_defect_profile_of_hostWeight_eq_twenty_seven
    {Point : Type u} {Block : Type v} [Fintype Point] [Fintype Block]
    [DecidableEq Point]
    (S : BlockSystem Point Block) (D : Finset Point)
    (hpoint : Fintype.card Point = 11) (hD : D.card = 5)
    (hhost : elevenFiveHostWeight S D = 27) :
    (∃ A ∈ (Finset.univ \ D).powersetCard 2,
      ∃ B ∈ (Finset.univ \ D).powersetCard 2, A ≠ B ∧
        (elevenFiveHostPairFibre S D A).card = 0 ∧
        (elevenFiveHostPairFibre S D B).card = 1 ∧
        ∀ C ∈ (Finset.univ \ D).powersetCard 2,
          C ≠ A → C ≠ B →
            (elevenFiveHostPairFibre S D C).card = 2) ∨
    (∃ A ∈ (Finset.univ \ D).powersetCard 2,
      ∃ B ∈ (Finset.univ \ D).powersetCard 2,
      ∃ C ∈ (Finset.univ \ D).powersetCard 2,
        A ≠ B ∧ A ≠ C ∧ B ≠ C ∧
        (elevenFiveHostPairFibre S D A).card = 1 ∧
        (elevenFiveHostPairFibre S D B).card = 1 ∧
        (elevenFiveHostPairFibre S D C).card = 1 ∧
        ∀ E ∈ (Finset.univ \ D).powersetCard 2,
          E ≠ A → E ≠ B → E ≠ C →
            (elevenFiveHostPairFibre S D E).card = 2) := by
  classical
  let Q : Finset (Finset Point) := (Finset.univ \ D).powersetCard 2
  let f : Finset Point → ℕ := fun A =>
    (elevenFiveHostPairFibre S D A).card
  have hsum : (∑ A ∈ Q, f A) = 27 := by
    change (∑ A ∈ (Finset.univ \ D).powersetCard 2,
      (elevenFiveHostPairFibre S D A).card) = 27
    rw [← elevenFiveHostWeight_eq_sum_hostPairFibre_card S D]
    exact hhost
  have hupper (A : Finset Point) (hA : A ∈ Q) : f A ≤ 2 :=
    elevenFiveHostPairFibre_card_le_two S D hD hA
  have hQcard : Q.card = 15 := by
    simp [Q, Finset.card_sdiff_of_subset (Finset.subset_univ D), hpoint,
      hD, Nat.choose]
  by_cases hzero : ∃ A ∈ Q, f A = 0
  · left
    obtain ⟨A, hAQ, hAzero⟩ := hzero
    have hAeraseCard : (Q.erase A).card = 14 := by
      rw [Finset.card_erase_of_mem hAQ, hQcard]
    have hsplitA : (∑ C ∈ Q.erase A, f C) + f A = ∑ C ∈ Q, f C :=
      Finset.sum_erase_add Q f hAQ
    have hrestSum : (∑ C ∈ Q.erase A, f C) = 27 := by omega
    have hpositive (B : Finset Point) (hB : B ∈ Q.erase A) : 1 ≤ f B := by
      by_contra hnot
      have hBzero : f B = 0 := by omega
      have hBmem : B ∈ Q.erase A := hB
      have hrestCard : ((Q.erase A).erase B).card = 13 := by
        rw [Finset.card_erase_of_mem hBmem, hAeraseCard]
      have hrestUpper : (∑ C ∈ (Q.erase A).erase B, f C) ≤ 26 := by
        calc
          (∑ C ∈ (Q.erase A).erase B, f C) ≤
              ∑ _C ∈ (Q.erase A).erase B, 2 := by
            apply Finset.sum_le_sum
            intro C hC
            exact hupper C
              (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hC))
          _ = 26 := by simp [hrestCard]
      have hsplitB :
          (∑ C ∈ (Q.erase A).erase B, f C) + f B =
            ∑ C ∈ Q.erase A, f C :=
        Finset.sum_erase_add (Q.erase A) f hBmem
      omega
    have hsmall : ∃ B ∈ Q.erase A, f B < 2 := by
      by_contra hnone
      push_neg at hnone
      have hlower : (∑ _B ∈ Q.erase A, 2) ≤
          ∑ B ∈ Q.erase A, f B := by
        apply Finset.sum_le_sum
        intro B hB
        exact hnone B hB
      have hconst : (∑ _B ∈ Q.erase A, 2) = 28 := by
        simp [hAeraseCard]
      omega
    obtain ⟨B, hBerase, hBsmall⟩ := hsmall
    have hBQ : B ∈ Q := Finset.mem_of_mem_erase hBerase
    have hBA : B ≠ A := (Finset.mem_erase.mp hBerase).1
    have hBone : f B = 1 := by
      have := hpositive B hBerase
      omega
    refine ⟨A, hAQ, B, hBQ, hBA.symm, hAzero, hBone, ?_⟩
    intro C hCQ hCA hCB
    have hBmem : B ∈ Q.erase A :=
      Finset.mem_erase.mpr ⟨hBA, hBQ⟩
    have hrestCard : ((Q.erase A).erase B).card = 13 := by
      rw [Finset.card_erase_of_mem hBmem, hAeraseCard]
    have hsplitB :
        (∑ E ∈ (Q.erase A).erase B, f E) + f B =
          ∑ E ∈ Q.erase A, f E :=
      Finset.sum_erase_add (Q.erase A) f hBmem
    have hrest : (∑ E ∈ (Q.erase A).erase B, f E) = 26 := by
      omega
    have htermLe (E : Finset Point)
        (hE : E ∈ (Q.erase A).erase B) : f E ≤ 2 :=
      hupper E (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hE))
    have hconst : (∑ _E ∈ (Q.erase A).erase B, 2) = 26 := by
      simp [hrestCard]
    have hall := (Finset.sum_eq_sum_iff_of_le htermLe).mp
      (hrest.trans hconst.symm)
    exact hall C (Finset.mem_erase.mpr
      ⟨hCB, Finset.mem_erase.mpr ⟨hCA, hCQ⟩⟩)
  · right
    have hpositive (A : Finset Point) (hA : A ∈ Q) : 1 ≤ f A := by
      have hne : f A ≠ 0 := by
        intro hA0
        exact hzero ⟨A, hA, hA0⟩
      omega
    have hsmallA : ∃ A ∈ Q, f A < 2 := by
      by_contra hnone
      push_neg at hnone
      have hlower : (∑ _A ∈ Q, 2) ≤ ∑ A ∈ Q, f A := by
        apply Finset.sum_le_sum
        intro A hA
        exact hnone A hA
      have hconst : (∑ _A ∈ Q, 2) = 30 := by simp [hQcard]
      omega
    obtain ⟨A, hAQ, hAsmall⟩ := hsmallA
    have hAone : f A = 1 := by
      have := hpositive A hAQ
      omega
    have hAeraseCard : (Q.erase A).card = 14 := by
      rw [Finset.card_erase_of_mem hAQ, hQcard]
    have hsplitA : (∑ E ∈ Q.erase A, f E) + f A = ∑ E ∈ Q, f E :=
      Finset.sum_erase_add Q f hAQ
    have hrestA : (∑ E ∈ Q.erase A, f E) = 26 := by omega
    have hsmallB : ∃ B ∈ Q.erase A, f B < 2 := by
      by_contra hnone
      push_neg at hnone
      have hlower : (∑ _B ∈ Q.erase A, 2) ≤
          ∑ B ∈ Q.erase A, f B := by
        apply Finset.sum_le_sum
        intro B hB
        exact hnone B hB
      have hconst : (∑ _B ∈ Q.erase A, 2) = 28 := by
        simp [hAeraseCard]
      omega
    obtain ⟨B, hBerase, hBsmall⟩ := hsmallB
    have hBQ : B ∈ Q := Finset.mem_of_mem_erase hBerase
    have hBA : B ≠ A := (Finset.mem_erase.mp hBerase).1
    have hBone : f B = 1 := by
      have := hpositive B hBQ
      omega
    have hBmem : B ∈ Q.erase A := Finset.mem_erase.mpr ⟨hBA, hBQ⟩
    have hABeraseCard : ((Q.erase A).erase B).card = 13 := by
      rw [Finset.card_erase_of_mem hBmem, hAeraseCard]
    have hsplitB :
        (∑ E ∈ (Q.erase A).erase B, f E) + f B =
          ∑ E ∈ Q.erase A, f E :=
      Finset.sum_erase_add (Q.erase A) f hBmem
    have hrestAB : (∑ E ∈ (Q.erase A).erase B, f E) = 25 := by omega
    have hsmallC : ∃ C ∈ (Q.erase A).erase B, f C < 2 := by
      by_contra hnone
      push_neg at hnone
      have hlower : (∑ _C ∈ (Q.erase A).erase B, 2) ≤
          ∑ C ∈ (Q.erase A).erase B, f C := by
        apply Finset.sum_le_sum
        intro C hC
        exact hnone C hC
      have hconst : (∑ _C ∈ (Q.erase A).erase B, 2) = 26 := by
        simp [hABeraseCard]
      omega
    obtain ⟨C, hCerased, hCsmall⟩ := hsmallC
    have hCerasedData := Finset.mem_erase.mp hCerased
    have hCBA : C ≠ B := hCerasedData.1
    have hCAerase := Finset.mem_erase.mp hCerasedData.2
    have hCA : C ≠ A := hCAerase.1
    have hCQ : C ∈ Q := hCAerase.2
    have hCone : f C = 1 := by
      have := hpositive C hCQ
      omega
    refine ⟨A, hAQ, B, hBQ, C, hCQ, hBA.symm, hCA.symm, hCBA.symm,
      hAone, hBone, hCone, ?_⟩
    intro E hEQ hEA hEB hEC
    have hCmem : C ∈ (Q.erase A).erase B := hCerased
    have hrestCard : (((Q.erase A).erase B).erase C).card = 12 := by
      rw [Finset.card_erase_of_mem hCmem, hABeraseCard]
    have hsplitC :
        (∑ F ∈ ((Q.erase A).erase B).erase C, f F) + f C =
          ∑ F ∈ (Q.erase A).erase B, f F :=
      Finset.sum_erase_add ((Q.erase A).erase B) f hCmem
    have hrest : (∑ F ∈ ((Q.erase A).erase B).erase C, f F) = 24 := by
      omega
    have htermLe (F : Finset Point)
        (hF : F ∈ ((Q.erase A).erase B).erase C) : f F ≤ 2 :=
      hupper F (Finset.mem_of_mem_erase
        (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hF)))
    have hconst : (∑ _F ∈ ((Q.erase A).erase B).erase C, 2) = 24 := by
      simp [hrestCard]
    have hall := (Finset.sum_eq_sum_iff_of_le htermLe).mp
      (hrest.trans hconst.symm)
    exact hall E (Finset.mem_erase.mpr
      ⟨hEC, Finset.mem_erase.mpr
        ⟨hEB, Finset.mem_erase.mpr ⟨hEA, hEQ⟩⟩⟩)

/-- Among relative `(1,3)` pages, at most four can contain one fixed
outside pair. -/
private theorem h27_pages_containing_pair_card_le_four
    {Point : Type u} {Block : Type v} [Fintype Point] [Fintype Block]
    [DecidableEq Point]
    (S : BlockSystem Point Block) (D : Finset Point)
    (hpoint : Fintype.card Point = 11) (hD : D.card = 5)
    (A : Finset Point)
    (hA : A ∈ (Finset.univ \ D).powersetCard 2) :
    ((Finset.univ.filter fun P : Block =>
      (S.support P ∩ D).card = 1 ∧ (S.support P \ D).card = 3).filter
        fun P => A ⊆ S.support P).card ≤ 4 := by
  classical
  let R : Finset Block := Finset.univ.filter fun P =>
    (S.support P ∩ D).card = 1 ∧ (S.support P \ D).card = 3
  let RA := R.filter fun P => A ⊆ S.support P
  have hAspec := Finset.mem_powersetCard.mp hA
  have hAoutside : A ⊆ Finset.univ \ D := hAspec.1
  have hAcard : A.card = 2 := hAspec.2
  have hpairwise : ((RA : Finset Block) : Set Block).PairwiseDisjoint
      (fun P => (S.support P \ D) \ A) := by
    intro P hP Q hQ hPQ
    have hPR := (Finset.mem_filter.mp hP).1
    have hQR := (Finset.mem_filter.mp hQ).1
    have hPA := (Finset.mem_filter.mp hP).2
    have hQA := (Finset.mem_filter.mp hQ).2
    change Disjoint ((S.support P \ D) \ A) ((S.support Q \ D) \ A)
    rw [Finset.disjoint_left]
    intro x hxP hxQ
    have hxPout := (Finset.mem_sdiff.mp hxP).1
    have hxQout := (Finset.mem_sdiff.mp hxQ).1
    have hxNotA := (Finset.mem_sdiff.mp hxP).2
    have hsub : insert x A ⊆ S.support P ∩ S.support Q := by
      intro y hy
      rcases Finset.mem_insert.mp hy with rfl | hyA
      · exact Finset.mem_inter.mpr
          ⟨(Finset.mem_sdiff.mp hxPout).1,
            (Finset.mem_sdiff.mp hxQout).1⟩
      · exact Finset.mem_inter.mpr ⟨hPA hyA, hQA hyA⟩
    have hthree : (insert x A).card = 3 := by
      rw [Finset.card_insert_of_notMem hxNotA, hAcard]
    have hle := Finset.card_le_card hsub
    have hlt := S.distinct_block_inter_card_lt_three hPQ
    omega
  have hpieceCard (P : Block) (hP : P ∈ RA) :
      ((S.support P \ D) \ A).card = 1 := by
    have hPR := (Finset.mem_filter.mp hP).1
    have hPspec := (Finset.mem_filter.mp hPR).2
    have hPA := (Finset.mem_filter.mp hP).2
    have hAoutP : A ⊆ S.support P \ D := by
      intro x hxA
      exact Finset.mem_sdiff.mpr
        ⟨hPA hxA, (Finset.mem_sdiff.mp (hAoutside hxA)).2⟩
    rw [Finset.card_sdiff_of_subset hAoutP, hPspec.2, hAcard]
  have hbiCard :
      (RA.biUnion fun P => (S.support P \ D) \ A).card = RA.card := by
    rw [Finset.card_biUnion hpairwise]
    calc
      (∑ P ∈ RA, ((S.support P \ D) \ A).card) =
          ∑ _P ∈ RA, 1 := by
        apply Finset.sum_congr rfl
        intro P hP
        exact hpieceCard P hP
      _ = RA.card := by simp
  have hbisub : RA.biUnion (fun P => (S.support P \ D) \ A) ⊆
      (Finset.univ \ D) \ A := by
    intro x hx
    obtain ⟨P, _hP, hxP⟩ := Finset.mem_biUnion.mp hx
    have hxOut := (Finset.mem_sdiff.mp hxP).1
    exact Finset.mem_sdiff.mpr
      ⟨Finset.mem_sdiff.mpr
        ⟨Finset.mem_univ x, (Finset.mem_sdiff.mp hxOut).2⟩,
       (Finset.mem_sdiff.mp hxP).2⟩
  have hOutsideCard : (Finset.univ \ D).card = 6 := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ D),
      Finset.card_univ, hpoint, hD]
  have hAvailableCard : ((Finset.univ \ D) \ A).card = 4 := by
    rw [Finset.card_sdiff_of_subset hAoutside, hOutsideCard, hAcard]
  have hle := Finset.card_le_card hbisub
  rw [hbiCard, hAvailableCard] at hle
  simpa only [R, RA] using hle

/-- A relative page which contains one singleton exceptional pair and
avoids two other exceptional pairs is unique. -/
private theorem h27_pages_eq_of_single_pair_avoiding_two
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    (cfg : Configuration Point) (Gamma : DeterminedCircle cfg)
    (hD : (circleTrace cfg Gamma.1).card = 5)
    (E F G : Finset Point)
    (hE : E ∈ (Finset.univ \ circleTrace cfg Gamma.1).powersetCard 2)
    (hEone : (elevenFiveHostPairFibre (blockSystem cfg)
      (circleTrace cfg Gamma.1) E).card = 1)
    (hfull : ∀ H ∈
      (Finset.univ \ circleTrace cfg Gamma.1).powersetCard 2,
      H ≠ E → H ≠ F → H ≠ G →
        (elevenFiveHostPairFibre (blockSystem cfg)
          (circleTrace cfg Gamma.1) H).card = 2)
    {P Q : GeometricBlock cfg}
    (hPtrace : (geometricBlockSupport cfg P ∩
      circleTrace cfg Gamma.1).card = 1)
    (hPoutside : (geometricBlockSupport cfg P \
      circleTrace cfg Gamma.1).card = 3)
    (hPE : E ⊆ geometricBlockSupport cfg P)
    (hPF : ¬ F ⊆ geometricBlockSupport cfg P)
    (hPG : ¬ G ⊆ geometricBlockSupport cfg P)
    (hQtrace : (geometricBlockSupport cfg Q ∩
      circleTrace cfg Gamma.1).card = 1)
    (hQoutside : (geometricBlockSupport cfg Q \
      circleTrace cfg Gamma.1).card = 3)
    (hQE : E ⊆ geometricBlockSupport cfg Q)
    (hQF : ¬ F ⊆ geometricBlockSupport cfg Q)
    (hQG : ¬ G ⊆ geometricBlockSupport cfg Q) : P = Q := by
  apply elevenFive_one_single_two_double_pages_eq cfg Gamma hD E hE hEone
  · exact hPtrace
  · exact hPoutside
  · exact hPE
  · intro H hH hHE
    have hHglobal : H ∈
        (Finset.univ \ circleTrace cfg Gamma.1).powersetCard 2 := by
      apply Finset.mem_powersetCard.mpr
      refine ⟨?_, (Finset.mem_powersetCard.mp hH).2⟩
      intro x hx
      have hxOut := (Finset.mem_powersetCard.mp hH).1 hx
      exact Finset.mem_sdiff.mpr
        ⟨Finset.mem_univ x, (Finset.mem_sdiff.mp hxOut).2⟩
    have hHF : H ≠ F := by
      intro hEq
      apply hPF
      intro x hx
      exact (Finset.mem_sdiff.mp
        ((Finset.mem_powersetCard.mp hH).1 (by simpa [hEq] using hx))).1
    have hHG : H ≠ G := by
      intro hEq
      apply hPG
      intro x hx
      exact (Finset.mem_sdiff.mp
        ((Finset.mem_powersetCard.mp hH).1 (by simpa [hEq] using hx))).1
    exact hfull H hHglobal hHE hHF hHG
  · exact hQtrace
  · exact hQoutside
  · exact hQE
  · intro H hH hHE
    have hHglobal : H ∈
        (Finset.univ \ circleTrace cfg Gamma.1).powersetCard 2 := by
      apply Finset.mem_powersetCard.mpr
      refine ⟨?_, (Finset.mem_powersetCard.mp hH).2⟩
      intro x hx
      have hxOut := (Finset.mem_powersetCard.mp hH).1 hx
      exact Finset.mem_sdiff.mpr
        ⟨Finset.mem_univ x, (Finset.mem_sdiff.mp hxOut).2⟩
    have hHF : H ≠ F := by
      intro hEq
      apply hQF
      intro x hx
      exact (Finset.mem_sdiff.mp
        ((Finset.mem_powersetCard.mp hH).1 (by simpa [hEq] using hx))).1
    have hHG : H ≠ G := by
      intro hEq
      apply hQG
      intro x hx
      exact (Finset.mem_sdiff.mp
        ((Finset.mem_powersetCard.mp hH).1 (by simpa [hEq] using hx))).1
    exact hfull H hHglobal hHE hHF hHG

/-- Two pages containing the same two distinct outside pairs coincide. -/
private theorem h27_pages_eq_of_two_pairs
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    (cfg : Configuration Point)
    {A B : Finset Point} (hAcard : A.card = 2) (hBcard : B.card = 2)
    (hAB : A ≠ B) {P Q : GeometricBlock cfg}
    (hPA : A ⊆ geometricBlockSupport cfg P)
    (hPB : B ⊆ geometricBlockSupport cfg P)
    (hQA : A ⊆ geometricBlockSupport cfg Q)
    (hQB : B ⊆ geometricBlockSupport cfg Q) : P = Q := by
  by_contra hPQ
  have hUnionCard : 3 ≤ (A ∪ B).card := by
    by_contra hnot
    have hle : (A ∪ B).card ≤ 2 := by omega
    have hAU : A = A ∪ B := by
      apply Finset.eq_of_subset_of_card_le Finset.subset_union_left
      omega
    have hBU : B = A ∪ B := by
      apply Finset.eq_of_subset_of_card_le Finset.subset_union_right
      omega
    exact hAB (hAU.trans hBU.symm)
  have hsub : A ∪ B ⊆
      geometricBlockSupport cfg P ∩ geometricBlockSupport cfg Q := by
    intro x hx
    rcases Finset.mem_union.mp hx with hxA | hxB
    · exact Finset.mem_inter.mpr ⟨hPA hxA, hQA hxA⟩
    · exact Finset.mem_inter.mpr ⟨hPB hxB, hQB hxB⟩
  have hle := Finset.card_le_card hsub
  have hlt := (blockSystem cfg).distinct_block_inter_card_lt_three hPQ
  change (geometricBlockSupport cfg P ∩
    geometricBlockSupport cfg Q).card < 3 at hlt
  omega

/-- A page with exact pattern `AB¬C` and a page with pattern `ABC` cannot
coexist: both of their three-point outside supports would equal `A ∪ B`. -/
private theorem h27_no_pair_only_and_triple_page
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    (cfg : Configuration Point) (D : Finset Point)
    (A B C : Finset Point)
    (hA : A ∈ (Finset.univ \ D).powersetCard 2)
    (hB : B ∈ (Finset.univ \ D).powersetCard 2)
    (hC : C ∈ (Finset.univ \ D).powersetCard 2)
    (hAB : A ≠ B)
    {P Q : GeometricBlock cfg}
    (hPoutside : (geometricBlockSupport cfg P \ D).card = 3)
    (hPA : A ⊆ geometricBlockSupport cfg P)
    (hPB : B ⊆ geometricBlockSupport cfg P)
    (hPC : ¬ C ⊆ geometricBlockSupport cfg P)
    (hQoutside : (geometricBlockSupport cfg Q \ D).card = 3)
    (hQA : A ⊆ geometricBlockSupport cfg Q)
    (hQB : B ⊆ geometricBlockSupport cfg Q)
    (hQC : C ⊆ geometricBlockSupport cfg Q) : False := by
  have hAspec := Finset.mem_powersetCard.mp hA
  have hBspec := Finset.mem_powersetCard.mp hB
  have hCspec := Finset.mem_powersetCard.mp hC
  have hUnionCard : 3 ≤ (A ∪ B).card := by
    by_contra hnot
    have hle : (A ∪ B).card ≤ 2 := by omega
    have hAU : A = A ∪ B := by
      apply Finset.eq_of_subset_of_card_le Finset.subset_union_left
      omega
    have hBU : B = A ∪ B := by
      apply Finset.eq_of_subset_of_card_le Finset.subset_union_right
      omega
    exact hAB (hAU.trans hBU.symm)
  have hUnionP : A ∪ B ⊆ geometricBlockSupport cfg P \ D := by
    intro x hx
    rcases Finset.mem_union.mp hx with hxA | hxB
    · exact Finset.mem_sdiff.mpr
        ⟨hPA hxA, (Finset.mem_sdiff.mp (hAspec.1 hxA)).2⟩
    · exact Finset.mem_sdiff.mpr
        ⟨hPB hxB, (Finset.mem_sdiff.mp (hBspec.1 hxB)).2⟩
  have hUnionQ : A ∪ B ⊆ geometricBlockSupport cfg Q \ D := by
    intro x hx
    rcases Finset.mem_union.mp hx with hxA | hxB
    · exact Finset.mem_sdiff.mpr
        ⟨hQA hxA, (Finset.mem_sdiff.mp (hAspec.1 hxA)).2⟩
    · exact Finset.mem_sdiff.mpr
        ⟨hQB hxB, (Finset.mem_sdiff.mp (hBspec.1 hxB)).2⟩
  have hPEq : A ∪ B = geometricBlockSupport cfg P \ D := by
    apply Finset.eq_of_subset_of_card_le hUnionP
    omega
  have hQEq : A ∪ B = geometricBlockSupport cfg Q \ D := by
    apply Finset.eq_of_subset_of_card_le hUnionQ
    omega
  apply hPC
  intro x hxC
  have hxQ : x ∈ geometricBlockSupport cfg Q \ D :=
    Finset.mem_sdiff.mpr
      ⟨hQC hxC, (Finset.mem_sdiff.mp (hCspec.1 hxC)).2⟩
  have hxUnion : x ∈ A ∪ B := by simpa only [hQEq] using hxQ
  have hxPout : x ∈ geometricBlockSupport cfg P \ D := by
    simpa only [hPEq] using hxUnion
  exact (Finset.mem_sdiff.mp hxPout).1

/-- The empty-plus-single host-pair profile has at most five pages. -/
private theorem h27_relativeCount_one_three_le_five_of_zero_single
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    (cfg : Configuration Point) (Gamma : DeterminedCircle cfg)
    (hpoint : Fintype.card Point = 11)
    (hD : (circleTrace cfg Gamma.1).card = 5)
    (A : Finset Point)
    (hA : A ∈ (Finset.univ \ circleTrace cfg Gamma.1).powersetCard 2)
    (B : Finset Point)
    (hB : B ∈ (Finset.univ \ circleTrace cfg Gamma.1).powersetCard 2)
    (hAB : A ≠ B)
    (_hAzero : (elevenFiveHostPairFibre (blockSystem cfg)
      (circleTrace cfg Gamma.1) A).card = 0)
    (hBone : (elevenFiveHostPairFibre (blockSystem cfg)
      (circleTrace cfg Gamma.1) B).card = 1)
    (hfull : ∀ C ∈
      (Finset.univ \ circleTrace cfg Gamma.1).powersetCard 2,
      C ≠ A → C ≠ B →
        (elevenFiveHostPairFibre (blockSystem cfg)
          (circleTrace cfg Gamma.1) C).card = 2) :
    elevenFiveRelativeCount (blockSystem cfg)
      (circleTrace cfg Gamma.1) 1 3 ≤ 5 := by
  classical
  let D := circleTrace cfg Gamma.1
  let R : Finset (GeometricBlock cfg) := Finset.univ.filter fun P =>
    (geometricBlockSupport cfg P ∩ D).card = 1 ∧
      (geometricBlockSupport cfg P \ D).card = 3
  let RA := R.filter fun P => A ⊆ geometricBlockSupport cfg P
  let RB := R.filter fun P =>
    ¬ A ⊆ geometricBlockSupport cfg P ∧ B ⊆ geometricBlockSupport cfg P
  have hcontain (P : GeometricBlock cfg) (hPR : P ∈ R) :
      A ⊆ geometricBlockSupport cfg P ∨
        B ⊆ geometricBlockSupport cfg P := by
    have hPspec := (Finset.mem_filter.mp hPR).2
    apply elevenFive_one_trace_contains_one_of_two_exceptionalPairs
      cfg Gamma hD A B
    · simpa only [D] using hfull
    · simpa only [D] using hPspec.1
    · have : 3 ≤ (geometricBlockSupport cfg P \ D).card := by
        rw [hPspec.2]
      simpa only [D] using this
  have hRAcard : RA.card ≤ 4 := by
    have hcap := h27_pages_containing_pair_card_le_four
      (blockSystem cfg) D hpoint (by simpa only [D] using hD)
        A (by simpa only [D] using hA)
    simpa only [RA, R, blockSystem, geometricBlockSystem,
      geometricBlockSupport] using hcap
  have hRBcard : RB.card ≤ 1 := by
    rw [Finset.card_le_one]
    intro P hP Q hQ
    have hPR := (Finset.mem_filter.mp hP).1
    have hQR := (Finset.mem_filter.mp hQ).1
    have hPspec := (Finset.mem_filter.mp hPR).2
    have hQspec := (Finset.mem_filter.mp hQR).2
    have hPside := (Finset.mem_filter.mp hP).2
    have hQside := (Finset.mem_filter.mp hQ).2
    exact h27_pages_eq_of_single_pair_avoiding_two
      cfg Gamma hD B A A hB hBone
        (by
          intro H hH hHB hHA _hHA
          exact hfull H hH hHA hHB)
        (by simpa only [D] using hPspec.1)
        (by simpa only [D] using hPspec.2)
        hPside.2 hPside.1 hPside.1
        (by simpa only [D] using hQspec.1)
        (by simpa only [D] using hQspec.2)
        hQside.2 hQside.1 hQside.1
  have hcover : R ⊆ RA ∪ RB := by
    intro P hPR
    rcases hcontain P hPR with hPA | hPB
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hPR, hPA⟩)
    · by_cases hPA : A ⊆ geometricBlockSupport cfg P
      · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hPR, hPA⟩)
      · exact Finset.mem_union_right _
          (Finset.mem_filter.mpr ⟨hPR, hPA, hPB⟩)
  have hcoverCard := Finset.card_le_card hcover
  have hunionCard := Finset.card_union_le RA RB
  have hRcard : R.card ≤ 5 := by omega
  simpa only [R, D, elevenFiveRelativeCount, blockSystem,
    geometricBlockSystem, geometricBlockSupport] using hRcard

/-- With three exceptional host pairs, every one-trace page through three
outsiders contains at least one of them. -/
private theorem h27_one_trace_contains_one_of_three_exceptionalPairs
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    (cfg : Configuration Point) (Gamma : DeterminedCircle cfg)
    (hD : (circleTrace cfg Gamma.1).card = 5)
    (A B C : Finset Point)
    (hfull : ∀ E ∈
      (Finset.univ \ circleTrace cfg Gamma.1).powersetCard 2,
      E ≠ A → E ≠ B → E ≠ C →
        (elevenFiveHostPairFibre (blockSystem cfg)
          (circleTrace cfg Gamma.1) E).card = 2)
    (P : GeometricBlock cfg)
    (hPtrace : (geometricBlockSupport cfg P ∩
      circleTrace cfg Gamma.1).card = 1)
    (hout : 3 ≤ (geometricBlockSupport cfg P \
      circleTrace cfg Gamma.1).card) :
    A ⊆ geometricBlockSupport cfg P ∨
      B ⊆ geometricBlockSupport cfg P ∨
        C ⊆ geometricBlockSupport cfg P := by
  classical
  by_cases hAP : A ⊆ geometricBlockSupport cfg P
  · exact Or.inl hAP
  by_cases hBP : B ⊆ geometricBlockSupport cfg P
  · exact Or.inr (Or.inl hBP)
  by_cases hCP : C ⊆ geometricBlockSupport cfg P
  · exact Or.inr (Or.inr hCP)
  exfalso
  have hthree : 2 < (geometricBlockSupport cfg P \
      circleTrace cfg Gamma.1).card := by omega
  obtain ⟨x, hx, y, hy, z, hz, hxy, hxz, hyz⟩ :=
    Finset.two_lt_card.mp hthree
  have pair_sub (r s : Point)
      (hr : r ∈ geometricBlockSupport cfg P \
        circleTrace cfg Gamma.1)
      (hs : s ∈ geometricBlockSupport cfg P \
        circleTrace cfg Gamma.1) :
      ({r, s} : Finset Point) ⊆ geometricBlockSupport cfg P := by
    intro q hq
    simp only [Finset.mem_insert, Finset.mem_singleton] at hq
    rcases hq with rfl | rfl
    · exact (Finset.mem_sdiff.mp hr).1
    · exact (Finset.mem_sdiff.mp hs).1
  have pair_ne (E : Finset Point)
      (hE : E ⊆ geometricBlockSupport cfg P) :
      E ≠ A ∧ E ≠ B ∧ E ≠ C := by
    refine ⟨?_, ?_, ?_⟩
    · intro hEq; exact hAP (by simpa [hEq] using hE)
    · intro hEq; exact hBP (by simpa [hEq] using hE)
    · intro hEq; exact hCP (by simpa [hEq] using hE)
  have hxySub := pair_sub x y hx hy
  have hxzSub := pair_sub x z hx hz
  have hyzSub := pair_sub y z hy hz
  have pair_mem (r s : Point)
      (hr : r ∈ geometricBlockSupport cfg P \ circleTrace cfg Gamma.1)
      (hs : s ∈ geometricBlockSupport cfg P \ circleTrace cfg Gamma.1)
      (hrs : r ≠ s) :
      ({r, s} : Finset Point) ∈
        (Finset.univ \ circleTrace cfg Gamma.1).powersetCard 2 := by
    apply Finset.mem_powersetCard.mpr
    refine ⟨?_, by simp [hrs]⟩
    intro q hq
    simp only [Finset.mem_insert, Finset.mem_singleton] at hq
    rcases hq with rfl | rfl
    · exact Finset.mem_sdiff.mpr
        ⟨Finset.mem_univ _, (Finset.mem_sdiff.mp hr).2⟩
    · exact Finset.mem_sdiff.mpr
        ⟨Finset.mem_univ _, (Finset.mem_sdiff.mp hs).2⟩
  apply elevenFive_one_trace_three_outsiders_of_pairwise_double_absurd
    cfg Gamma hD P hPtrace hx hy hz hxy hxz hyz
  · exact hfull {x, y}
      (pair_mem x y hx hy hxy)
      (pair_ne {x, y} hxySub).1
      (pair_ne {x, y} hxySub).2.1
      (pair_ne {x, y} hxySub).2.2
  · exact hfull {x, z}
      (pair_mem x z hx hz hxz)
      (pair_ne {x, z} hxzSub).1
      (pair_ne {x, z} hxzSub).2.1
      (pair_ne {x, z} hxzSub).2.2
  · exact hfull {y, z}
      (pair_mem y z hy hz hyz)
      (pair_ne {y, z} hyzSub).1
      (pair_ne {y, z} hyzSub).2.1
      (pair_ne {y, z} hyzSub).2.2

/-- In the three-single-fibre H27 branch, the `(1,3)` pages are encoded by
the nonempty set of exceptional pairs which they contain.  This encoding is
injective, and the patterns `AB¬C` and `ABC` cannot both occur. -/
private theorem h27_relativeCount_one_three_le_six_of_three_single
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    (cfg : Configuration Point) (Gamma : DeterminedCircle cfg)
    (hD : (circleTrace cfg Gamma.1).card = 5)
    (A B C : Finset Point)
    (hA : A ∈ (Finset.univ \ circleTrace cfg Gamma.1).powersetCard 2)
    (hB : B ∈ (Finset.univ \ circleTrace cfg Gamma.1).powersetCard 2)
    (hC : C ∈ (Finset.univ \ circleTrace cfg Gamma.1).powersetCard 2)
    (hAB : A ≠ B) (hAC : A ≠ C) (hBC : B ≠ C)
    (hAone : (elevenFiveHostPairFibre (blockSystem cfg)
      (circleTrace cfg Gamma.1) A).card = 1)
    (hBone : (elevenFiveHostPairFibre (blockSystem cfg)
      (circleTrace cfg Gamma.1) B).card = 1)
    (hCone : (elevenFiveHostPairFibre (blockSystem cfg)
      (circleTrace cfg Gamma.1) C).card = 1)
    (hfull : ∀ H ∈
      (Finset.univ \ circleTrace cfg Gamma.1).powersetCard 2,
      H ≠ A → H ≠ B → H ≠ C →
        (elevenFiveHostPairFibre (blockSystem cfg)
          (circleTrace cfg Gamma.1) H).card = 2) :
    elevenFiveRelativeCount (blockSystem cfg)
      (circleTrace cfg Gamma.1) 1 3 ≤ 6 := by
  classical
  let D := circleTrace cfg Gamma.1
  let R : Finset (GeometricBlock cfg) := Finset.univ.filter fun P =>
    (geometricBlockSupport cfg P ∩ D).card = 1 ∧
      (geometricBlockSupport cfg P \ D).card = 3
  let E : Finset (Finset Point) := {A, B, C}
  let pattern (P : GeometricBlock cfg) : Finset (Finset Point) :=
    E.filter fun H => H ⊆ geometricBlockSupport cfg P
  let I : Finset (Finset (Finset Point)) := R.image pattern
  let U : Finset (Finset (Finset Point)) := E.powerset.erase ∅
  have hcontain (P : GeometricBlock cfg) (hPR : P ∈ R) :
      A ⊆ geometricBlockSupport cfg P ∨
        B ⊆ geometricBlockSupport cfg P ∨
          C ⊆ geometricBlockSupport cfg P := by
    have hPspec := (Finset.mem_filter.mp hPR).2
    apply h27_one_trace_contains_one_of_three_exceptionalPairs
      cfg Gamma hD A B C hfull P
    · simpa only [D] using hPspec.1
    · have : 3 ≤ (geometricBlockSupport cfg P \ D).card := by
        rw [hPspec.2]
      simpa only [D] using this
  have hpatA (P : GeometricBlock cfg) :
      A ∈ pattern P ↔ A ⊆ geometricBlockSupport cfg P := by
    simp only [pattern, Finset.mem_filter]
    simp only [E, Finset.mem_insert, Finset.mem_singleton, true_or, true_and]
  have hpatB (P : GeometricBlock cfg) :
      B ∈ pattern P ↔ B ⊆ geometricBlockSupport cfg P := by
    simp only [pattern, Finset.mem_filter]
    simp only [E, Finset.mem_insert, Finset.mem_singleton, true_or, or_true,
      true_and]
  have hpatC (P : GeometricBlock cfg) :
      C ∈ pattern P ↔ C ⊆ geometricBlockSupport cfg P := by
    simp only [pattern, Finset.mem_filter]
    simp only [E, Finset.mem_insert, Finset.mem_singleton, true_or, or_true,
      true_and]
  have hinj : Set.InjOn pattern (↑R : Set (GeometricBlock cfg)) := by
    intro P hPR Q hQR hpq
    have hPspec := (Finset.mem_filter.mp hPR).2
    have hQspec := (Finset.mem_filter.mp hQR).2
    have hAiff : A ⊆ geometricBlockSupport cfg P ↔
        A ⊆ geometricBlockSupport cfg Q := by
      rw [← hpatA P, hpq, hpatA Q]
    have hBiff : B ⊆ geometricBlockSupport cfg P ↔
        B ⊆ geometricBlockSupport cfg Q := by
      rw [← hpatB P, hpq, hpatB Q]
    have hCiff : C ⊆ geometricBlockSupport cfg P ↔
        C ⊆ geometricBlockSupport cfg Q := by
      rw [← hpatC P, hpq, hpatC Q]
    by_cases hPA : A ⊆ geometricBlockSupport cfg P
    · have hQA := hAiff.mp hPA
      by_cases hPB : B ⊆ geometricBlockSupport cfg P
      · exact h27_pages_eq_of_two_pairs cfg
          (Finset.mem_powersetCard.mp hA).2
          (Finset.mem_powersetCard.mp hB).2 hAB
          hPA hPB hQA (hBiff.mp hPB)
      · by_cases hPC : C ⊆ geometricBlockSupport cfg P
        · exact h27_pages_eq_of_two_pairs cfg
            (Finset.mem_powersetCard.mp hA).2
            (Finset.mem_powersetCard.mp hC).2 hAC
            hPA hPC hQA (hCiff.mp hPC)
        · exact h27_pages_eq_of_single_pair_avoiding_two
            cfg Gamma hD A B C hA hAone hfull
            hPspec.1 hPspec.2 hPA hPB hPC
            hQspec.1 hQspec.2 hQA
            (fun hQB => hPB (hBiff.mpr hQB))
            (fun hQC => hPC (hCiff.mpr hQC))
    · have hQA : ¬ A ⊆ geometricBlockSupport cfg Q :=
        fun h => hPA (hAiff.mpr h)
      by_cases hPB : B ⊆ geometricBlockSupport cfg P
      · have hQB := hBiff.mp hPB
        by_cases hPC : C ⊆ geometricBlockSupport cfg P
        · exact h27_pages_eq_of_two_pairs cfg
            (Finset.mem_powersetCard.mp hB).2
            (Finset.mem_powersetCard.mp hC).2 hBC
            hPB hPC hQB (hCiff.mp hPC)
        · exact h27_pages_eq_of_single_pair_avoiding_two
            cfg Gamma hD B A C hB hBone
            (by
              intro H hH hHB hHA hHC
              exact hfull H hH hHA hHB hHC)
            hPspec.1 hPspec.2 hPB hPA hPC
            hQspec.1 hQspec.2 hQB hQA
            (fun hQC => hPC (hCiff.mpr hQC))
      · have hQB : ¬ B ⊆ geometricBlockSupport cfg Q :=
          fun h => hPB (hBiff.mpr h)
        have hPC : C ⊆ geometricBlockSupport cfg P := by
          rcases hcontain P hPR with h | h | h
          · exact False.elim (hPA h)
          · exact False.elim (hPB h)
          · exact h
        have hQC := hCiff.mp hPC
        exact h27_pages_eq_of_single_pair_avoiding_two
          cfg Gamma hD C A B hC hCone
          (by
            intro H hH hHC hHA hHB
            exact hfull H hH hHA hHB hHC)
          hPspec.1 hPspec.2 hPC hPA hPB
          hQspec.1 hQspec.2 hQC hQA hQB
  have hIcard : I.card = R.card := by
    exact Finset.card_image_iff.mpr hinj
  have hI_sub_U : I ⊆ U := by
    intro K hKI
    rcases Finset.mem_image.mp hKI with ⟨P, hPR, rfl⟩
    apply Finset.mem_erase.mpr
    refine ⟨?_, Finset.mem_powerset.mpr (Finset.filter_subset _ _)⟩
    intro hempty
    rcases hcontain P hPR with hPA | hPB | hPC
    · have : A ∈ pattern P := (hpatA P).2 hPA
      rw [hempty] at this
      simpa using this
    · have : B ∈ pattern P := (hpatB P).2 hPB
      rw [hempty] at this
      simpa using this
    · have : C ∈ pattern P := (hpatC P).2 hPC
      rw [hempty] at this
      simpa using this
  have hEcard : E.card = 3 := by
    simp [E, hAB, hAC, hBC, Ne.symm hAB, Ne.symm hAC, Ne.symm hBC]
  have hUcard : U.card = 7 := by
    change (E.powerset.erase ∅).card = 7
    rw [Finset.card_erase_of_mem]
    · rw [Finset.card_powerset, hEcard]
      norm_num
    · exact Finset.mem_powerset.mpr (Finset.empty_subset E)
  have hPairMem : ({A, B} : Finset (Finset Point)) ∈ U := by
    change ({A, B} : Finset (Finset Point)) ∈ E.powerset.erase ∅
    apply Finset.mem_erase.mpr
    refine ⟨?_, Finset.mem_powerset.mpr ?_⟩
    · simpa [hAB]
    · intro H hH
      simp only [Finset.mem_insert, Finset.mem_singleton] at hH
      rcases hH with rfl | rfl
      · simp [E]
      · simp [E]
  have hTripleMem : E ∈ U := by
    change E ∈ E.powerset.erase ∅
    apply Finset.mem_erase.mpr
    refine ⟨?_, Finset.mem_powerset.mpr (Finset.Subset.rfl)⟩
    intro hEempty
    have : A ∈ E := by simp [E]
    rw [hEempty] at this
    simpa using this
  by_cases hTripleI : E ∈ I
  · rcases Finset.mem_image.mp hTripleI with
      ⟨Q, hQR, hQpattern⟩
    have hPairNot : ({A, B} : Finset (Finset Point)) ∉ I := by
      intro hPairI
      rcases Finset.mem_image.mp hPairI with
        ⟨P, hPR, hPpattern⟩
      have hPA : A ⊆ geometricBlockSupport cfg P := by
        apply (hpatA P).1
        rw [hPpattern]
        simp
      have hPB : B ⊆ geometricBlockSupport cfg P := by
        apply (hpatB P).1
        rw [hPpattern]
        simp
      have hPC : ¬ C ⊆ geometricBlockSupport cfg P := by
        intro hPC
        have hCPat : C ∈ pattern P := (hpatC P).2 hPC
        rw [hPpattern] at hCPat
        simpa [Ne.symm hAC, Ne.symm hBC] using hCPat
      have hQA : A ⊆ geometricBlockSupport cfg Q := by
        apply (hpatA Q).1
        rw [hQpattern]
        simp [E]
      have hQB : B ⊆ geometricBlockSupport cfg Q := by
        apply (hpatB Q).1
        rw [hQpattern]
        simp [E]
      have hQC : C ⊆ geometricBlockSupport cfg Q := by
        apply (hpatC Q).1
        rw [hQpattern]
        simp [E]
      have hPspec := (Finset.mem_filter.mp hPR).2
      have hQspec := (Finset.mem_filter.mp hQR).2
      exact h27_no_pair_only_and_triple_page cfg D A B C
        (by simpa only [D] using hA)
        (by simpa only [D] using hB)
        (by simpa only [D] using hC) hAB
        hPspec.2 hPA hPB hPC hQspec.2 hQA hQB hQC
    have hsub : I ⊆ U.erase ({A, B} : Finset (Finset Point)) := by
      intro K hKI
      apply Finset.mem_erase.mpr
      refine ⟨?_, hI_sub_U hKI⟩
      intro hK
      apply hPairNot
      simpa only [hK] using hKI
    have hcard := Finset.card_le_card hsub
    have herase :
        (U.erase ({A, B} : Finset (Finset Point))).card = 6 := by
      rw [Finset.card_erase_of_mem hPairMem, hUcard]
    have hRcard : R.card ≤ 6 := by omega
    simpa only [R, D, elevenFiveRelativeCount, blockSystem,
      geometricBlockSystem, geometricBlockSupport] using hRcard
  · have hsub : I ⊆ U.erase E := by
      intro K hKI
      apply Finset.mem_erase.mpr
      refine ⟨?_, hI_sub_U hKI⟩
      intro hK
      apply hTripleI
      simpa only [hK] using hKI
    have hcard := Finset.card_le_card hsub
    have herase : (U.erase E).card = 6 := by
      rw [Finset.card_erase_of_mem hTripleMem, hUcard]
    have hRcard : R.card ≤ 6 := by omega
    simpa only [R, D, elevenFiveRelativeCount, blockSystem,
      geometricBlockSystem, geometricBlockSupport] using hRcard

/-- The exact H27 host-fibre classification gives the six-page cap needed
at the boundary of the C40/L14/B5=7 page argument. -/
theorem elevenFive_relativeCount_one_three_le_six_of_hostWeight_eq_twenty_seven
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    (cfg : Configuration Point) (Gamma : DeterminedCircle cfg)
    (hpoint : Fintype.card Point = 11)
    (hD : (circleTrace cfg Gamma.1).card = 5)
    (hhost : elevenFiveHostWeight (blockSystem cfg)
      (circleTrace cfg Gamma.1) = 27) :
    elevenFiveRelativeCount (blockSystem cfg)
      (circleTrace cfg Gamma.1) 1 3 ≤ 6 := by
  rcases elevenFiveHostPairFibre_defect_profile_of_hostWeight_eq_twenty_seven
      (blockSystem cfg) (circleTrace cfg Gamma.1) hpoint hD hhost with
    hzeroSingle | hthreeSingle
  · rcases hzeroSingle with
      ⟨A, hA, B, hB, hAB, hAzero, hBone, hfull⟩
    have hcap := h27_relativeCount_one_three_le_five_of_zero_single
      cfg Gamma hpoint hD A hA B hB hAB hAzero hBone hfull
    omega
  · rcases hthreeSingle with
      ⟨A, hA, B, hB, C, hC, hAB, hAC, hBC,
        hAone, hBone, hCone, hfull⟩
    exact h27_relativeCount_one_three_le_six_of_three_single
      cfg Gamma hD A B C hA hB hC hAB hAC hBC
        hAone hBone hCone hfull

end Erdos506.V1
