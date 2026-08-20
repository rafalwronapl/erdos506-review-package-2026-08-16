import Erdos506.V1.ElevenFiveC39H28NeighbourRouter

/-!
# The finite four-page cap in the H28 zero-fibre branch

In the zero host-pair fibre branch, every relative `(1,3)` page contains
the exceptional outside pair `A`.  Removing `A` from the three outsiders
of a page leaves one label.  These one-label remainders are disjoint for
different pages: a shared remainder together with `A` would be a three-set
owned by two different blocks.  There are only six outsiders and `A` has
two endpoints, so at most four pages occur.

This is entirely finite.  It uses only the actual host-pair fibres and
triple ownership; no golden-axis or page-normalisation hypothesis enters.
-/

namespace Erdos506.V1

open Erdos506.Block
open Erdos506.Block.BlockSystem
open Erdos506.Incidence
open Erdos506.V4

universe u v

/-- The literal first branch of the H28 pair-fibre defect profile: one
outside pair has no two-trace host, while every other outside pair has two.
-/
def ElevenFiveH28ZeroHostPairFibreProfile
    {α : Type u} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (Gamma : DeterminedCircle cfg) : Prop :=
  ∃ A ∈ (Finset.univ \ circleTrace cfg Gamma.1).powersetCard 2,
    (elevenFiveHostPairFibre (blockSystem cfg)
      (circleTrace cfg Gamma.1) A).card = 0 ∧
    ∀ B ∈ (Finset.univ \ circleTrace cfg Gamma.1).powersetCard 2,
      B ≠ A →
        (elevenFiveHostPairFibre (blockSystem cfg)
          (circleTrace cfg Gamma.1) B).card = 2

/-- Finite pigeonhole lemma behind the H28 page cap.  If every `(1,3)`
block through a selected five-set contains one fixed two-point outside
pair, then there are at most four such blocks. -/
theorem elevenFive_relativeCount_one_three_le_four_of_common_outsidePair
    {Point : Type u} {Block : Type v}
    [Fintype Point] [Fintype Block] [DecidableEq Point]
    (S : BlockSystem Point Block) (D : Finset Point)
    (hpoint : Fintype.card Point = 11) (hD : D.card = 5)
    (A : Finset Point)
    (hA : A ∈ (Finset.univ \ D).powersetCard 2)
    (hcontain : ∀ P : Block,
      (S.support P ∩ D).card = 1 →
      3 ≤ (S.support P \ D).card → A ⊆ S.support P) :
    elevenFiveRelativeCount S D 1 3 ≤ 4 := by
  classical
  let R : Finset Block := Finset.univ.filter fun P =>
    (S.support P ∩ D).card = 1 ∧ (S.support P \ D).card = 3
  have hAspec := Finset.mem_powersetCard.mp hA
  have hAoutside : A ⊆ Finset.univ \ D := hAspec.1
  have hAcard : A.card = 2 := hAspec.2
  have hRpairwise : ((R : Finset Block) : Set Block).PairwiseDisjoint
      (fun P => (S.support P \ D) \ A) := by
    intro P hPR Q hQR hPQ
    have hPRspec := Finset.mem_filter.mp hPR
    have hQRspec := Finset.mem_filter.mp hQR
    have hPA : A ⊆ S.support P :=
      hcontain P hPRspec.2.1 (by omega)
    have hQA : A ⊆ S.support Q :=
      hcontain Q hQRspec.2.1 (by omega)
    change Disjoint ((S.support P \ D) \ A) ((S.support Q \ D) \ A)
    rw [Finset.disjoint_left]
    intro x hxP hxQ
    have hxPout := (Finset.mem_sdiff.mp hxP).1
    have hxQout := (Finset.mem_sdiff.mp hxQ).1
    have hxNotA : x ∉ A := (Finset.mem_sdiff.mp hxP).2
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
  have hpieceCard (P : Block) (hPR : P ∈ R) :
      ((S.support P \ D) \ A).card = 1 := by
    have hPRspec := Finset.mem_filter.mp hPR
    have hPA : A ⊆ S.support P :=
      hcontain P hPRspec.2.1 (by omega)
    have hAoutP : A ⊆ S.support P \ D := by
      intro x hxA
      exact Finset.mem_sdiff.mpr
        ⟨hPA hxA, (Finset.mem_sdiff.mp (hAoutside hxA)).2⟩
    rw [Finset.card_sdiff_of_subset hAoutP, hPRspec.2.2, hAcard]
  have hbiCard :
      (R.biUnion fun P => (S.support P \ D) \ A).card = R.card := by
    rw [Finset.card_biUnion hRpairwise]
    calc
      (∑ P ∈ R, ((S.support P \ D) \ A).card) =
          ∑ _P ∈ R, 1 := by
        apply Finset.sum_congr rfl
        intro P hPR
        exact hpieceCard P hPR
      _ = R.card := by simp
  have hbisub : R.biUnion (fun P => (S.support P \ D) \ A) ⊆
      (Finset.univ \ D) \ A := by
    intro x hx
    obtain ⟨P, _hPR, hxP⟩ := Finset.mem_biUnion.mp hx
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
  simpa [R, elevenFiveRelativeCount] using hle

/-- The sharp finite page cap in the actual H28 zero-fibre branch. -/
theorem elevenFive_c39_h28_relativeCount_one_three_le_four_of_zeroHostPairFibre
    {α : Type u} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (Gamma : DeterminedCircle cfg)
    (hpoint : Fintype.card α = 11)
    (hD : (circleTrace cfg Gamma.1).card = 5)
    (hzeroFibre : ElevenFiveH28ZeroHostPairFibreProfile cfg Gamma) :
    elevenFiveRelativeCount (blockSystem cfg)
      (circleTrace cfg Gamma.1) 1 3 ≤ 4 := by
  obtain ⟨A, hA, _hAzero, hfull⟩ := hzeroFibre
  apply elevenFive_relativeCount_one_three_le_four_of_common_outsidePair
    (blockSystem cfg) (circleTrace cfg Gamma.1) hpoint hD A hA
  intro P hPtrace hout
  exact elevenFive_one_trace_contains_exceptionalPair_of_otherPairs_double
    cfg Gamma hD A hfull P
      (by simpa [blockSystem, geometricBlockSystem,
        geometricBlockSupport] using hPtrace)
      (by simpa [blockSystem, geometricBlockSystem,
        geometricBlockSupport] using hout)

/-- In the other H28 defect branch, the two exceptional outside pairs have
one host each.  Pages containing only the first pair and pages containing
only the second pair form singleton families by the public
one-single/two-double page lemma.  Pages containing both pairs also form a
singleton family by triple ownership.  Hence this branch has at most three
`(1,3)` pages (and in particular satisfies the required four-page cap). -/
theorem elevenFive_c39_h28_relativeCount_one_three_le_three_of_twoSingleFibres
    {α : Type u} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (Gamma : DeterminedCircle cfg)
    (hD : (circleTrace cfg Gamma.1).card = 5)
    (A : Finset α)
    (hA : A ∈ (Finset.univ \ circleTrace cfg Gamma.1).powersetCard 2)
    (B : Finset α)
    (hB : B ∈ (Finset.univ \ circleTrace cfg Gamma.1).powersetCard 2)
    (hAB : A ≠ B)
    (hAone : (elevenFiveHostPairFibre (blockSystem cfg)
      (circleTrace cfg Gamma.1) A).card = 1)
    (hBone : (elevenFiveHostPairFibre (blockSystem cfg)
      (circleTrace cfg Gamma.1) B).card = 1)
    (hfull : ∀ C ∈
        (Finset.univ \ circleTrace cfg Gamma.1).powersetCard 2,
      C ≠ A → C ≠ B →
        (elevenFiveHostPairFibre (blockSystem cfg)
          (circleTrace cfg Gamma.1) C).card = 2) :
    elevenFiveRelativeCount (blockSystem cfg)
      (circleTrace cfg Gamma.1) 1 3 ≤ 3 := by
  classical
  let D := circleTrace cfg Gamma.1
  let R : Finset (GeometricBlock cfg) := Finset.univ.filter fun P =>
    (geometricBlockSupport cfg P ∩ D).card = 1 ∧
      (geometricBlockSupport cfg P \ D).card = 3
  let RA := R.filter fun P =>
    A ⊆ geometricBlockSupport cfg P ∧
      ¬ B ⊆ geometricBlockSupport cfg P
  let RB := R.filter fun P =>
    B ⊆ geometricBlockSupport cfg P ∧
      ¬ A ⊆ geometricBlockSupport cfg P
  let RAB := R.filter fun P =>
    A ⊆ geometricBlockSupport cfg P ∧
      B ⊆ geometricBlockSupport cfg P
  have hpagePairOutside (P : GeometricBlock cfg) (E : Finset α)
      (hE : E ∈ (geometricBlockSupport cfg P \ D).powersetCard 2) :
      E ∈ (Finset.univ \ D).powersetCard 2 := by
    apply Finset.mem_powersetCard.mpr
    refine ⟨?_, (Finset.mem_powersetCard.mp hE).2⟩
    intro x hx
    have hxOut := (Finset.mem_powersetCard.mp hE).1 hx
    exact Finset.mem_sdiff.mpr
      ⟨Finset.mem_univ x, (Finset.mem_sdiff.mp hxOut).2⟩
  have hpagePair_ne_of_not_subset (P : GeometricBlock cfg)
      (F E : Finset α) (hPF : ¬ F ⊆ geometricBlockSupport cfg P)
      (hE : E ∈ (geometricBlockSupport cfg P \ D).powersetCard 2) :
      E ≠ F := by
    intro hEF
    apply hPF
    intro x hxF
    have hxE : x ∈ E := by rw [hEF]; exact hxF
    exact (Finset.mem_sdiff.mp
      ((Finset.mem_powersetCard.mp hE).1 hxE)).1
  have hpageEqOnly (E F : Finset α)
      (hE : E ∈ (Finset.univ \ D).powersetCard 2)
      (hEone : (elevenFiveHostPairFibre (blockSystem cfg) D E).card = 1)
      (hfullEF : ∀ G ∈ (Finset.univ \ D).powersetCard 2,
        G ≠ E → G ≠ F →
          (elevenFiveHostPairFibre (blockSystem cfg) D G).card = 2)
      {P Q : GeometricBlock cfg}
      (hPtrace : (geometricBlockSupport cfg P ∩ D).card = 1)
      (hPoutside : (geometricBlockSupport cfg P \ D).card = 3)
      (hPE : E ⊆ geometricBlockSupport cfg P)
      (hPF : ¬ F ⊆ geometricBlockSupport cfg P)
      (hQtrace : (geometricBlockSupport cfg Q ∩ D).card = 1)
      (hQoutside : (geometricBlockSupport cfg Q \ D).card = 3)
      (hQE : E ⊆ geometricBlockSupport cfg Q)
      (hQF : ¬ F ⊆ geometricBlockSupport cfg Q) : P = Q := by
    apply elevenFive_one_single_two_double_pages_eq
      cfg Gamma hD E (by simpa [D] using hE)
        (by simpa [D] using hEone)
    · simpa [D] using hPtrace
    · simpa [D] using hPoutside
    · exact hPE
    · intro G hG hGE
      exact hfullEF G (hpagePairOutside P G hG) hGE
        (hpagePair_ne_of_not_subset P F G hPF hG)
    · simpa [D] using hQtrace
    · simpa [D] using hQoutside
    · exact hQE
    · intro G hG hGE
      exact hfullEF G (hpagePairOutside Q G hG) hGE
        (hpagePair_ne_of_not_subset Q F G hQF hG)
  have hcontain (P : GeometricBlock cfg) (hPR : P ∈ R) :
      A ⊆ geometricBlockSupport cfg P ∨
        B ⊆ geometricBlockSupport cfg P := by
    have hPspec := Finset.mem_filter.mp hPR
    apply elevenFive_one_trace_contains_one_of_two_exceptionalPairs
      cfg Gamma hD A B
    · simpa [D] using hfull
    · simpa [D] using hPspec.2.1
    · have : 3 ≤ (geometricBlockSupport cfg P \ D).card := by
        rw [hPspec.2.2]
      simpa [D] using this
  have hRAcard : RA.card ≤ 1 := by
    rw [Finset.card_le_one]
    intro P hP Q hQ
    have hPR := (Finset.mem_filter.mp hP).1
    have hQR := (Finset.mem_filter.mp hQ).1
    have hPspec := (Finset.mem_filter.mp hPR).2
    have hQspec := (Finset.mem_filter.mp hQR).2
    have hPside := (Finset.mem_filter.mp hP).2
    have hQside := (Finset.mem_filter.mp hQ).2
    exact hpageEqOnly A B (by simpa [D] using hA)
      (by simpa [D] using hAone) (by simpa [D] using hfull)
        hPspec.1 hPspec.2 hPside.1 hPside.2
          hQspec.1 hQspec.2 hQside.1 hQside.2
  have hRBcard : RB.card ≤ 1 := by
    rw [Finset.card_le_one]
    intro P hP Q hQ
    have hPR := (Finset.mem_filter.mp hP).1
    have hQR := (Finset.mem_filter.mp hQ).1
    have hPspec := (Finset.mem_filter.mp hPR).2
    have hQspec := (Finset.mem_filter.mp hQR).2
    have hPside := (Finset.mem_filter.mp hP).2
    have hQside := (Finset.mem_filter.mp hQ).2
    exact hpageEqOnly B A (by simpa [D] using hB)
      (by simpa [D] using hBone)
        (by
          intro G hG hGB hGA
          exact hfull G (by simpa [D] using hG) hGA hGB)
        hPspec.1 hPspec.2 hPside.1 hPside.2
          hQspec.1 hQspec.2 hQside.1 hQside.2
  have hAcard : A.card = 2 := (Finset.mem_powersetCard.mp hA).2
  have hBcard : B.card = 2 := (Finset.mem_powersetCard.mp hB).2
  have hABcard : 3 ≤ (A ∪ B).card := by
    by_contra hnot
    have hUnionLe : (A ∪ B).card ≤ 2 := by omega
    have hAU : A = A ∪ B := by
      apply Finset.eq_of_subset_of_card_le Finset.subset_union_left
      omega
    have hBU : B = A ∪ B := by
      apply Finset.eq_of_subset_of_card_le Finset.subset_union_right
      omega
    exact hAB (hAU.trans hBU.symm)
  have hRABcard : RAB.card ≤ 1 := by
    rw [Finset.card_le_one]
    intro P hP Q hQ
    by_contra hPQ
    have hPboth := (Finset.mem_filter.mp hP).2
    have hQboth := (Finset.mem_filter.mp hQ).2
    have hsub : A ∪ B ⊆
        geometricBlockSupport cfg P ∩ geometricBlockSupport cfg Q := by
      intro x hx
      rcases Finset.mem_union.mp hx with hxA | hxB
      · exact Finset.mem_inter.mpr ⟨hPboth.1 hxA, hQboth.1 hxA⟩
      · exact Finset.mem_inter.mpr ⟨hPboth.2 hxB, hQboth.2 hxB⟩
    have hle := Finset.card_le_card hsub
    have hlt := (blockSystem cfg).distinct_block_inter_card_lt_three hPQ
    have hlt' :
        (geometricBlockSupport cfg P ∩
          geometricBlockSupport cfg Q).card < 3 := by
      simpa [blockSystem, geometricBlockSystem,
        geometricBlockSupport] using hlt
    omega
  have hcover : R ⊆ (RA ∪ RB) ∪ RAB := by
    intro P hPR
    rcases hcontain P hPR with hPA | hPB
    · by_cases hPB : B ⊆ geometricBlockSupport cfg P
      · simp [RA, RB, RAB, hPR, hPA, hPB]
      · simp [RA, RB, RAB, hPR, hPA, hPB]
    · by_cases hPA : A ⊆ geometricBlockSupport cfg P
      · simp [RA, RB, RAB, hPR, hPA, hPB]
      · simp [RA, RB, RAB, hPR, hPA, hPB]
  have hcoverCard := Finset.card_le_card hcover
  have hleftCard := Finset.card_union_le RA RB
  have hallCard := Finset.card_union_le (RA ∪ RB) RAB
  have hRcard : R.card ≤ 3 := by omega
  simpa [R, D, elevenFiveRelativeCount, blockSystem,
    geometricBlockSystem, geometricBlockSupport] using hRcard

/-- The H28 pair-fibre dichotomy supplies the exact Goodall callback: the
zero-fibre branch has the four-label pigeonhole cap, while the two-single
branch has the stronger three-page cap above. -/
theorem elevenFiveC39H28PageCapInput_of_hostPairFibres
    {α : Type u} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) : ElevenFiveC39H28PageCapInput cfg := by
  intro Gamma hpoint hD hhost _hzero
  rcases elevenFive_c39_h28_hostPairFibre_defect_profile
    cfg Gamma hpoint hD hhost with hzeroFibre | htwoSingle
  · exact
      elevenFive_c39_h28_relativeCount_one_three_le_four_of_zeroHostPairFibre
        cfg Gamma hpoint hD hzeroFibre
  · obtain ⟨A, hA, B, hB, hAB, hAone, hBone, hfull⟩ := htwoSingle
    have hthree :=
      elevenFive_c39_h28_relativeCount_one_three_le_three_of_twoSingleFibres
        cfg Gamma hD A hA B hB hAB hAone hBone hfull
    omega

/-- In the full C39/L12 row, the zero pair-fibre branch now has exactly
four `(1,3)` pages, outside-rich weight three, relative `(0,5)` count one,
and a literal outsider five-block. -/
theorem elevenFive_c39_h28_zeroHostPairFibre_fourPages_and_outsiderFiveBlock
    {α : Type u} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (hpoint : Fintype.card α = 11)
    (hcap : BlockSizeCap (blockSystem cfg) 5)
    (hlocal : ∀ p : α, ElevenFiveLocalRows (blockSystem cfg) p)
    (hglobal : ElevenFiveGlobalRows (blockSystem cfg))
    (hC : (blockSystem cfg).totalCircleCount = 39)
    (hL : elevenFiveLineTotal (blockSystem cfg) = 12)
    (Gamma : DeterminedCircle cfg)
    (hD : (circleTrace cfg Gamma.1).card = 5)
    (hhost : elevenFiveHostWeight (blockSystem cfg)
      (circleTrace cfg Gamma.1) = 28)
    (hzero : elevenFiveRelativeCount (blockSystem cfg)
      (circleTrace cfg Gamma.1) 1 4 = 0)
    (hzeroFibre : ElevenFiveH28ZeroHostPairFibreProfile cfg Gamma) :
    elevenFiveRelativeCount (blockSystem cfg)
        (circleTrace cfg Gamma.1) 1 3 = 4 ∧
      elevenFiveOutsideRichWeight (blockSystem cfg)
        (circleTrace cfg Gamma.1) = 3 ∧
      elevenFiveRelativeCount (blockSystem cfg)
        (circleTrace cfg Gamma.1) 0 5 = 1 ∧
      ∃ B : GeometricBlock cfg,
        (geometricBlockSupport cfg B ∩ circleTrace cfg Gamma.1).card = 0 ∧
        (geometricBlockSupport cfg B \ circleTrace cfg Gamma.1).card = 5 := by
  have hpageCap :=
    elevenFive_c39_h28_relativeCount_one_three_le_four_of_zeroHostPairFibre
      cfg Gamma hpoint hD hzeroFibre
  obtain ⟨hpages, hrich⟩ :=
    elevenFive_c39_h28_front_saturated_of_zero_one_four_and_page_cap
      cfg hpoint hcap hglobal hC hL Gamma hD hhost hzero hpageCap
  have hy :=
    elevenFive_c39_h28_relativeCount_zero_five_eq_one_of_outsideRich_eq_three
      cfg hpoint hcap hlocal hglobal hC hL Gamma hD hhost hzero hrich
  have hB :=
    elevenFive_c39_h28_exists_outsider_fiveBlock_of_relativeCount_zero_five_eq_one
      cfg Gamma hy
  exact ⟨hpages, hrich, hy, hB⟩

/-- Unconditional full-row extraction, with the pair-fibre dichotomy
discharged internally: the H28/A14-zero face has exactly four pages and a
literal outsider five-block. -/
theorem elevenFive_c39_h28_fourPages_and_outsiderFiveBlock_of_hostPairFibres
    {α : Type u} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (hpoint : Fintype.card α = 11)
    (hcap : BlockSizeCap (blockSystem cfg) 5)
    (hlocal : ∀ p : α, ElevenFiveLocalRows (blockSystem cfg) p)
    (hglobal : ElevenFiveGlobalRows (blockSystem cfg))
    (hC : (blockSystem cfg).totalCircleCount = 39)
    (hL : elevenFiveLineTotal (blockSystem cfg) = 12)
    (Gamma : DeterminedCircle cfg)
    (hD : (circleTrace cfg Gamma.1).card = 5)
    (hhost : elevenFiveHostWeight (blockSystem cfg)
      (circleTrace cfg Gamma.1) = 28)
    (hzero : elevenFiveRelativeCount (blockSystem cfg)
      (circleTrace cfg Gamma.1) 1 4 = 0) :
    elevenFiveRelativeCount (blockSystem cfg)
        (circleTrace cfg Gamma.1) 1 3 = 4 ∧
      elevenFiveOutsideRichWeight (blockSystem cfg)
        (circleTrace cfg Gamma.1) = 3 ∧
      elevenFiveRelativeCount (blockSystem cfg)
        (circleTrace cfg Gamma.1) 0 5 = 1 ∧
      ∃ B : GeometricBlock cfg,
        (geometricBlockSupport cfg B ∩ circleTrace cfg Gamma.1).card = 0 ∧
        (geometricBlockSupport cfg B \ circleTrace cfg Gamma.1).card = 5 := by
  have hpageCap :=
    elevenFiveC39H28PageCapInput_of_hostPairFibres cfg
      Gamma hpoint hD hhost hzero
  obtain ⟨hpages, hrich⟩ :=
    elevenFive_c39_h28_front_saturated_of_zero_one_four_and_page_cap
      cfg hpoint hcap hglobal hC hL Gamma hD hhost hzero hpageCap
  have hy :=
    elevenFive_c39_h28_relativeCount_zero_five_eq_one_of_outsideRich_eq_three
      cfg hpoint hcap hlocal hglobal hC hL Gamma hD hhost hzero hrich
  have hB :=
    elevenFive_c39_h28_exists_outsider_fiveBlock_of_relativeCount_zero_five_eq_one
      cfg Gamma hy
  exact ⟨hpages, hrich, hy, hB⟩

end Erdos506.V1
