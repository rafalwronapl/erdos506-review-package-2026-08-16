import Erdos506.V1.NineFive

/-!
# The concyclic-outsider terminal in the nine-point five-circle branch

This file isolates the last genuinely metric case of the selected five-circle
argument.  Four labels outside the selected circle lie on a second determined
circle.  All finite census rows are proved in the tagged block system; the
only metric input is the explicit radical-axis cross-block principle.
-/

namespace Erdos506.V1

open Erdos506.Block
open Erdos506.Block.BlockSystem
open Erdos506.Finite
open Erdos506.Incidence
open Erdos506.V3
open Erdos506.V4
open scoped BigOperators

universe u v

section AbstractCensus

variable {Point : Type u} {Block : Type v}
  [Fintype Point] [Fintype Block] [DecidableEq Point]

private theorem sum_line_indicator_eq_card
    [DecidableEq Block]
    (S : BlockSystem Point Block) (F : Finset Block)
    (hline : ∀ b ∈ F, S.kind b = .line) :
    (∑ L : LineBlock S, if L.1 ∈ F then 1 else 0) = F.card := by
  classical
  calc
    (∑ L : LineBlock S, if L.1 ∈ F then 1 else 0) =
        ((Finset.univ : Finset (LineBlock S)).filter fun L =>
          L.1 ∈ F).card := by
      rw [Finset.card_eq_sum_ones, Finset.sum_filter]
    _ = F.card := by
      apply Finset.card_bij (fun L _hL => L.1)
      · intro L hL
        exact (Finset.mem_filter.mp hL).2
      · intro L hL K hK hLK
        exact Subtype.ext hLK
      · intro b hb
        let L : LineBlock S := ⟨b, hline b hb⟩
        exact ⟨L, Finset.mem_filter.mpr ⟨Finset.mem_univ L, hb⟩, rfl⟩

/-- All finite rows needed after a second circle has been found through the
four outsiders.  The five named classes are the manuscript's
`a,b,u,v,ell`. -/
structure NineFiveConcyclicCensus
    (S : BlockSystem Point Block) (g omega : Block) : Prop where
  omegaOutside_eq :
    S.support omega \ S.support g = nineFiveOutside S g
  delta_le_one :
    (S.support omega ∩ S.support g).card ≤ 1
  twoTwo_avoids_common :
    ∀ c, (c ∈ nineFiveCircleType S g 2 2 ∨
      c ∈ nineFiveLineType S g 2 2) →
      Disjoint (S.support c ∩ S.support g) (S.support omega)
  r_eq :
    nineFiveR S g = (nineFiveLineType S g 2 1).card +
      2 * (nineFiveLineType S g 2 2).card
  circle_linear_row :
    S.totalCircleCount + (nineFiveCircleType S g 2 2).card +
        nineFiveR S g =
      42 + (nineFiveCircleType S g 1 2).card
  circle_formula :
    S.totalCircleCount =
      42 - nineFiveR S g - (nineFiveCircleType S g 2 2).card +
        (nineFiveCircleType S g 1 2).card
  relative_triple_row :
    (nineFiveCircleType S g 1 2).card +
        2 * (nineFiveCircleType S g 2 2).card +
        2 * (nineFiveLineType S g 2 2).card +
        (nineFiveLineType S g 1 2).card +
        6 * (S.support omega ∩ S.support g).card = 30
  global_line_row :
    S.globalLineRow =
      3 * ((nineFiveLineType S g 2 1).card : ℤ) +
        7 * ((nineFiveLineType S g 2 2).card : ℤ) +
        3 * ((nineFiveLineType S g 1 2).card : ℤ)
  b_le_twelve : (nineFiveCircleType S g 2 2).card ≤ 12

/-- Pure block-system census around two circles: the selected base has five
labels and the second circle contains all four labels outside it. -/
theorem nineFive_concyclic_census
    (S : BlockSystem Point Block) (g omega : Block)
    (hpoint : Fintype.card Point = 9)
    (hgkind : S.kind g = .circle)
    (hgcard : (S.support g).card = 5)
    (hcircleCap : ∀ b, S.kind b = .circle → (S.support b).card ≤ 5)
    (homegakind : S.kind omega = .circle)
    (houtsideOmega : nineFiveOutside S g ⊆ S.support omega) :
    NineFiveConcyclicCensus S g omega := by
  classical
  let X := nineFiveOutside S g
  let A := nineFiveCircleType S g 1 2
  let B := nineFiveCircleType S g 2 2
  let Uline := nineFiveLineType S g 2 1
  let Vline := nineFiveLineType S g 2 2
  let Ell := nineFiveLineType S g 1 2
  let U := nineFiveFanUnion S g
  let H := nineFiveTripleFanBlocks S g
  let Low := nineFiveLowCircleBlocks S g
  let delta := (S.support omega ∩ S.support g).card
  have hXcard : X.card = 4 := by
    simpa [X] using nineFiveOutside_card S g hpoint hgcard
  have hOmegaOutsideEq : S.support omega \ S.support g = X := by
    ext p
    constructor
    · intro hp
      exact Finset.mem_sdiff.mpr
        ⟨Finset.mem_univ p, (Finset.mem_sdiff.mp hp).2⟩
    · intro hp
      have hp' := Finset.mem_sdiff.mp (show p ∈ nineFiveOutside S g by
        simpa [X] using hp)
      exact Finset.mem_sdiff.mpr ⟨houtsideOmega (by simpa [X] using hp), hp'.2⟩
  have hOmegaOutsideCard : (S.support omega \ S.support g).card = 4 := by
    rw [hOmegaOutsideEq, hXcard]
  have hdeltaLe : delta ≤ 1 := by
    have hsplit := Finset.card_inter_add_card_sdiff
      (S.support omega) (S.support g)
    have hcap := hcircleCap omega homegakind
    change (S.support omega ∩ S.support g).card ≤ 1
    omega
  have homegaNeG : omega ≠ g := by
    intro heq
    rw [heq, Finset.sdiff_self] at hOmegaOutsideCard
    simp at hOmegaOutsideCard
  have houtSubInter (c : Block) :
      S.support c \ S.support g ⊆ S.support c ∩ S.support omega := by
    intro p hp
    have hpX : p ∈ X := by
      apply Finset.mem_sdiff.mpr
      exact ⟨Finset.mem_univ p, (Finset.mem_sdiff.mp hp).2⟩
    exact Finset.mem_inter.mpr
      ⟨(Finset.mem_sdiff.mp hp).1, houtsideOmega (by simpa [X] using hpX)⟩
  have houtsideLe (c : Block) (hcne : c ≠ omega) :
      (S.support c \ S.support g).card ≤ 2 := by
    have hle := Finset.card_le_card (houtSubInter c)
    have hlt := S.distinct_block_inter_card_lt_three hcne
    omega
  have hinterBaseLe (c : Block) (hcne : c ≠ g) :
      (S.support c ∩ S.support g).card ≤ 2 := by
    have hlt := S.distinct_block_inter_card_lt_three hcne
    omega
  have hTwoTwoAvoid (c : Block)
      (hc : c ∈ B ∨ c ∈ Vline) :
      Disjoint (S.support c ∩ S.support g) (S.support omega) := by
    have hout : (S.support c \ S.support g).card = 2 := by
      rcases hc with hc | hc
      · exact (Finset.mem_filter.mp hc).2.2
      · exact (Finset.mem_filter.mp hc).2.2
    have hcne : c ≠ omega := by
      intro heq
      rw [heq, hOmegaOutsideCard] at hout
      omega
    rw [Finset.disjoint_left]
    intro p hpBase hpOmega
    have hpC : p ∈ S.support c := (Finset.mem_inter.mp hpBase).1
    have hpG : p ∈ S.support g := (Finset.mem_inter.mp hpBase).2
    have hpNotOutside : p ∉ S.support c \ S.support g := by
      intro hp
      exact (Finset.mem_sdiff.mp hp).2 hpG
    have hsub : insert p (S.support c \ S.support g) ⊆
        S.support c ∩ S.support omega := by
      intro q hq
      rcases Finset.mem_insert.mp hq with rfl | hq
      · exact Finset.mem_inter.mpr ⟨hpC, hpOmega⟩
      · exact houtSubInter c hq
    have hcard : (insert p (S.support c \ S.support g)).card = 3 := by
      rw [Finset.card_insert_of_notMem hpNotOutside, hout]
    have hle := Finset.card_le_card hsub
    have hlt := S.distinct_block_inter_card_lt_three hcne
    omega
  have hHzero : H.card = 0 := by
    apply Finset.card_eq_zero.mpr
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro c hc
    have hspec := nineFive_fan_block_spec S g c (Finset.mem_filter.mp hc).1
    have hout := (Finset.mem_filter.mp hc).2
    have hcne : c ≠ omega := by
      intro heq
      rw [heq, hOmegaOutsideCard] at hout
      omega
    have hle := Finset.card_le_card (houtSubInter c)
    have hlt := S.distinct_block_inter_card_lt_three hcne
    omega
  have homegaLow : omega ∈ Low := by
    apply Finset.mem_filter.mpr
    exact ⟨S.mem_blocksOfKind.mpr homegakind, homegaNeG, hdeltaLe⟩
  have homegaNotA : omega ∉ A := by
    intro h
    have hout := (Finset.mem_filter.mp h).2.2
    rw [hOmegaOutsideCard] at hout
    omega
  have hLowEq : Low = insert omega A := by
    ext c
    constructor
    · intro hc
      by_cases hco : c = omega
      · simp [hco]
      · apply Finset.mem_insert_of_mem
        have hspec := Finset.mem_filter.mp hc
        have hcircle := S.mem_blocksOfKind.mp hspec.1
        have houtLe := houtsideLe c hco
        have hsplit := Finset.card_inter_add_card_sdiff
          (S.support c) (S.support g)
        have hmin := S.circle_min c hcircle
        have hinter : (S.support c ∩ S.support g).card = 1 := by omega
        have hout : (S.support c \ S.support g).card = 2 := by omega
        exact Finset.mem_filter.mpr
          ⟨S.mem_blocksOfKind.mpr hcircle, hinter, hout⟩
    · intro hc
      rcases Finset.mem_insert.mp hc with rfl | hc
      · exact homegaLow
      · have hspec := Finset.mem_filter.mp hc
        have hcircle := S.mem_blocksOfKind.mp hspec.1
        have hcne : c ≠ g := by
          intro heq
          rw [heq] at hspec
          simp at hspec
        exact Finset.mem_filter.mpr
          ⟨S.mem_blocksOfKind.mpr hcircle, hcne, by omega⟩
  have hLowCard : Low.card = 1 + A.card := by
    rw [hLowEq, Finset.card_insert_of_notMem homegaNotA]
    omega
  have hUfilterB :
      U.filter (fun c => (S.support c \ S.support g).card = 2) = B := by
    ext c
    constructor
    · intro hc
      have hc' := Finset.mem_filter.mp hc
      have hspec := nineFive_fan_block_spec S g c hc'.1
      exact Finset.mem_filter.mpr
        ⟨S.mem_blocksOfKind.mpr hspec.1, hspec.2.2, hc'.2⟩
    · intro hc
      have hspec := Finset.mem_filter.mp hc
      have hcircle := S.mem_blocksOfKind.mp hspec.1
      obtain ⟨p, hp⟩ := Finset.card_pos.mp (show
        0 < (S.support c \ S.support g).card by omega)
      let x : BlockOutsider S g :=
        ⟨p, mem_blockOutsiders.mpr (Finset.mem_sdiff.mp hp).2⟩
      have hfan := mem_circlePencil_of_circle_of_inter_card_two
        S g c x hcircle hspec.2.1 (Finset.mem_sdiff.mp hp).1
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_biUnion.mpr ⟨x, Finset.mem_univ x, hfan⟩,
          hspec.2.2⟩
  have hPairEqB : nineFivePairMoment S g = B.card := by
    unfold nineFivePairMoment
    calc
      (∑ c ∈ U, Nat.choose (nineFiveFanDegree S g c) 2) =
          ∑ c ∈ U,
            if (S.support c \ S.support g).card = 2 then 1 else 0 := by
        apply Finset.sum_congr rfl
        intro c hc
        have hdegree := nineFiveFanDegree_eq_outside_card S g c hc
        have hcne : c ≠ omega := by
          intro heq
          have hinter := (nineFive_fan_block_spec S g c hc).2.2
          rw [heq] at hinter
          change delta = 2 at hinter
          omega
        have houtLe := houtsideLe c hcne
        have houtPos := (nineFive_fan_degree_bounds S g c hcircleCap hc).1
        rw [hdegree] at houtPos ⊢
        interval_cases hout : (S.support c \ S.support g).card <;>
          norm_num [Nat.choose]
      _ = (U.filter fun c =>
          (S.support c \ S.support g).card = 2).card := by
        rw [Finset.card_eq_sum_ones, Finset.sum_filter]
      _ = B.card := congrArg Finset.card hUfilterB
  have hmoment := nineFive_fan_moment_identity S g hcircleCap
  have hfanR := nineFive_sum_fan_add_R_eq_forty S g hpoint hgcard
  have hURB : U.card + B.card + nineFiveR S g = 40 := by
    have hmoment' : U.card + B.card =
        (∑ x : BlockOutsider S g, (circlePencil S g x).card) + H.card := by
      simpa [U, H, hPairEqB] using hmoment
    rw [hHzero] at hmoment'
    omega
  have hpartition := nineFive_totalCircleCount_partition S g hgkind
  have hCircleLinear :
      S.totalCircleCount + B.card + nineFiveR S g = 42 + A.card := by
    have hpartition' : S.totalCircleCount = 1 + U.card + Low.card := by
      simpa [U, Low] using hpartition
    omega
  have hCircleFormula :
      S.totalCircleCount = 42 - nineFiveR S g - B.card + A.card := by
    omega
  have hBcapRaw := S.relative_two_two_capacity (S.support g) B (by
    intro c hc
    exact (Finset.mem_filter.mp hc).2.1)
  have hBsum :
      (∑ c ∈ B, Nat.choose (S.support c \ S.support g).card 2) =
        B.card := by
    rw [Finset.card_eq_sum_ones]
    apply Finset.sum_congr rfl
    intro c hc
    have hout := (Finset.mem_filter.mp hc).2.2
    norm_num [hout, Nat.choose]
  rw [hBsum, hpoint, hgcard] at hBcapRaw
  norm_num [Nat.choose] at hBcapRaw
  have hChordPoint (L : LineBlock S) :
      (if L ∈ nineFiveChordLines S g then
          (S.support L.1 \ S.support g).card else 0) =
        (if L.1 ∈ Uline then 1 else 0) +
          2 * (if L.1 ∈ Vline then 1 else 0) := by
    by_cases hchord : L ∈ nineFiveChordLines S g
    · have hinter := (Finset.mem_filter.mp hchord).2
      have hLneOmega : L.1 ≠ omega := by
        intro heq
        have hk := L.2
        rw [heq, homegakind] at hk
        cases hk
      have houtLe := houtsideLe L.1 hLneOmega
      interval_cases hout : (S.support L.1 \ S.support g).card <;>
        norm_num [hchord, Uline, Vline, nineFiveLineType,
          BlockSystem.blocksOfKind, L.2, hinter, hout]
    · have hnotU : L.1 ∉ Uline := by
        intro hU
        apply hchord
        apply Finset.mem_filter.mpr
        exact ⟨Finset.mem_univ L, (Finset.mem_filter.mp hU).2.1⟩
      have hnotV : L.1 ∉ Vline := by
        intro hV
        apply hchord
        apply Finset.mem_filter.mpr
        exact ⟨Finset.mem_univ L, (Finset.mem_filter.mp hV).2.1⟩
      simp [hchord, hnotU, hnotV]
  have hUlineKind : ∀ c ∈ Uline, S.kind c = .line := by
    intro c hc
    exact S.mem_blocksOfKind.mp (Finset.mem_filter.mp hc).1
  have hVlineKind : ∀ c ∈ Vline, S.kind c = .line := by
    intro c hc
    exact S.mem_blocksOfKind.mp (Finset.mem_filter.mp hc).1
  have hEllKind : ∀ c ∈ Ell, S.kind c = .line := by
    intro c hc
    exact S.mem_blocksOfKind.mp (Finset.mem_filter.mp hc).1
  have hsumU := sum_line_indicator_eq_card S Uline hUlineKind
  have hsumV := sum_line_indicator_eq_card S Vline hVlineKind
  have hRuv : nineFiveR S g = Uline.card + 2 * Vline.card := by
    rw [nineFiveR_eq_nineFiveChordIncidence S g hgkind hpoint hgcard]
    unfold nineFiveChordIncidence
    calc
      (∑ L ∈ nineFiveChordLines S g,
          (S.support L.1 \ S.support g).card) =
          ∑ L : LineBlock S,
            if L ∈ nineFiveChordLines S g then
              (S.support L.1 \ S.support g).card else 0 := by
        rw [← Finset.sum_filter]
        simp
      _ = ∑ L : LineBlock S,
          ((if L.1 ∈ Uline then 1 else 0) +
            2 * (if L.1 ∈ Vline then 1 else 0)) := by
        apply Fintype.sum_congr
        exact hChordPoint
      _ = Uline.card + 2 * Vline.card := by
        simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
        rw [hsumU, hsumV]
  have hTripleWeight (c : Block) :
      Nat.choose (S.support c ∩ S.support g).card 1 *
          Nat.choose (S.support c \ S.support g).card 2 =
        (if c ∈ A then 1 else 0) +
          2 * (if c ∈ B then 1 else 0) +
          2 * (if c ∈ Vline then 1 else 0) +
          (if c ∈ Ell then 1 else 0) +
          (if c = omega then 6 * delta else 0) := by
    by_cases hco : c = omega
    · subst c
      norm_num [A, B, Vline, Ell, nineFiveCircleType, nineFiveLineType,
        BlockSystem.blocksOfKind, homegakind, hOmegaOutsideCard,
        delta, Nat.choose, Nat.mul_comm]
    · have houtLe := houtsideLe c hco
      by_cases hcg : c = g
      · subst c
        simp [A, B, Vline, Ell, nineFiveCircleType, nineFiveLineType,
          BlockSystem.blocksOfKind, hgkind, Ne.symm homegaNeG]
      · have hinterLe := hinterBaseLe c hcg
        cases hkind : S.kind c with
        | line =>
            interval_cases hinter : (S.support c ∩ S.support g).card <;>
              interval_cases hout : (S.support c \ S.support g).card <;>
              norm_num [A, B, Vline, Ell, nineFiveCircleType,
                nineFiveLineType, BlockSystem.blocksOfKind, hkind,
                hinter, hout, hco] <;> simp
        | circle =>
            interval_cases hinter : (S.support c ∩ S.support g).card <;>
              interval_cases hout : (S.support c \ S.support g).card <;>
              norm_num [A, B, Vline, Ell, nineFiveCircleType,
                nineFiveLineType, BlockSystem.blocksOfKind, hkind,
                hinter, hout, hco] <;> simp
  have hrelative := S.relative_triple_partition (S.support g) 1 (by omega)
  rw [hpoint, hgcard] at hrelative
  norm_num [Nat.choose] at hrelative
  have hrelativeSum :
      (∑ c : Block,
        Nat.choose (S.support c ∩ S.support g).card 1 *
          Nat.choose (S.support c \ S.support g).card 2) =
        A.card + 2 * B.card + 2 * Vline.card + Ell.card +
          6 * delta := by
    calc
      _ = ∑ c : Block,
          ((if c ∈ A then 1 else 0) +
            2 * (if c ∈ B then 1 else 0) +
            2 * (if c ∈ Vline then 1 else 0) +
            (if c ∈ Ell then 1 else 0) +
            (if c = omega then 6 * delta else 0)) := by
        apply Fintype.sum_congr
        exact hTripleWeight
      _ = A.card + 2 * B.card + 2 * Vline.card + Ell.card +
          6 * delta := by
        simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
        simp
  have hrelativeSum' :
      (∑ c : Block,
        (S.support c ∩ S.support g).card *
          Nat.choose (S.support c \ S.support g).card 2) =
        A.card + 2 * B.card + 2 * Vline.card + Ell.card +
          6 * delta := by
    simpa [Nat.choose] using hrelativeSum
  rw [hrelativeSum'] at hrelative
  have hTripleRow :
      A.card + 2 * B.card + 2 * Vline.card + Ell.card +
        6 * delta = 30 := by
    exact hrelative
  have hLineWeight (L : LineBlock S) :
      (if 3 ≤ (S.support L.1).card then
          (Nat.choose (S.support L.1).card 2 : ℤ) +
            ((S.support L.1).card : ℤ) - 3
        else 0) =
        3 * (if L.1 ∈ Uline then (1 : ℤ) else 0) +
          7 * (if L.1 ∈ Vline then (1 : ℤ) else 0) +
          3 * (if L.1 ∈ Ell then (1 : ℤ) else 0) := by
    have hLneG : L.1 ≠ g := by
      intro heq
      have hk := L.2
      rw [heq, hgkind] at hk
      cases hk
    have hLneOmega : L.1 ≠ omega := by
      intro heq
      have hk := L.2
      rw [heq, homegakind] at hk
      cases hk
    have hinterLe := hinterBaseLe L.1 hLneG
    have houtLe := houtsideLe L.1 hLneOmega
    have hsplit := Finset.card_inter_add_card_sdiff
      (S.support L.1) (S.support g)
    have hsize : (S.support L.1).card =
        (S.support L.1 ∩ S.support g).card +
          (S.support L.1 \ S.support g).card := by
      omega
    interval_cases hinter : (S.support L.1 ∩ S.support g).card <;>
      interval_cases hout : (S.support L.1 \ S.support g).card <;>
      norm_num [Uline, Vline, Ell, nineFiveLineType,
        BlockSystem.blocksOfKind, L.2, hinter, hout, hsize, Nat.choose]
  have hsumUZ :
      (∑ L : LineBlock S, if L.1 ∈ Uline then (1 : ℤ) else 0) =
        (Uline.card : ℤ) := by
    exact_mod_cast hsumU
  have hsumVZ :
      (∑ L : LineBlock S, if L.1 ∈ Vline then (1 : ℤ) else 0) =
        (Vline.card : ℤ) := by
    exact_mod_cast hsumV
  have hsumEll := sum_line_indicator_eq_card S Ell hEllKind
  have hsumEllZ :
      (∑ L : LineBlock S, if L.1 ∈ Ell then (1 : ℤ) else 0) =
        (Ell.card : ℤ) := by
    exact_mod_cast hsumEll
  have hGlobalLine : S.globalLineRow =
      3 * (Uline.card : ℤ) + 7 * (Vline.card : ℤ) +
        3 * (Ell.card : ℤ) := by
    unfold BlockSystem.globalLineRow
    calc
      (∑ L : LineBlock S,
        if 3 ≤ (S.support L.1).card then
          (Nat.choose (S.support L.1).card 2 : ℤ) +
            ((S.support L.1).card : ℤ) - 3
        else 0) =
          ∑ L : LineBlock S,
            (3 * (if L.1 ∈ Uline then (1 : ℤ) else 0) +
              7 * (if L.1 ∈ Vline then (1 : ℤ) else 0) +
              3 * (if L.1 ∈ Ell then (1 : ℤ) else 0)) := by
        apply Fintype.sum_congr
        exact hLineWeight
      _ = 3 * (Uline.card : ℤ) + 7 * (Vline.card : ℤ) +
          3 * (Ell.card : ℤ) := by
        simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
        rw [hsumUZ, hsumVZ, hsumEllZ]
  refine
    { omegaOutside_eq := ?_
      delta_le_one := ?_
      twoTwo_avoids_common := ?_
      r_eq := ?_
      circle_linear_row := ?_
      circle_formula := ?_
      relative_triple_row := ?_
      global_line_row := ?_
      b_le_twelve := ?_ }
  · simpa [X] using hOmegaOutsideEq
  · simpa [delta] using hdeltaLe
  · intro c hc
    exact hTwoTwoAvoid c (by simpa [B, Vline] using hc)
  · simpa [Uline, Vline] using hRuv
  · simpa [A, B] using hCircleLinear
  · simpa [A, B] using hCircleFormula
  · simpa [A, B, Vline, Ell, delta] using hTripleRow
  · simpa [Uline, Vline, Ell] using hGlobalLine
  · simpa [B] using hBcapRaw

end AbstractCensus

section GeometricTerminal

/-- Every circle or line of relative type `(2,2)` is a radical-axis
cross-block.  In the one-common-point branch, the avoidance field in the
census removes that common point from the two-point base trace. -/
theorem nineFive_concyclic_two_two_subset_crossBlocks
    {α : Type u} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (Gamma Omega : DeterminedCircle cfg)
    (hcensus : NineFiveConcyclicCensus
      (blockSystem cfg) (Sum.inr Gamma) (Sum.inr Omega)) :
    ∀ c,
      (c ∈ nineFiveCircleType (blockSystem cfg) (Sum.inr Gamma) 2 2 ∨
        c ∈ nineFiveLineType (blockSystem cfg) (Sum.inr Gamma) 2 2) →
      c ∈ circleCrossBlocks cfg Gamma Omega := by
  classical
  let S := blockSystem cfg
  let g : GeometricBlock cfg := Sum.inr Gamma
  let omega : GeometricBlock cfg := Sum.inr Omega
  change NineFiveConcyclicCensus S g omega at hcensus
  change ∀ c,
    (c ∈ nineFiveCircleType S g 2 2 ∨
      c ∈ nineFiveLineType S g 2 2) →
    c ∈ circleCrossBlocks cfg Gamma Omega
  intro c hcases
  have hspec : (S.support c ∩ S.support g).card = 2 ∧
      (S.support c \ S.support g).card = 2 := by
    rcases hcases with hc | hc
    · exact (Finset.mem_filter.mp hc).2
    · exact (Finset.mem_filter.mp hc).2
  have havoid := hcensus.twoTwo_avoids_common c hcases
  have houtsideEq :
      S.support c ∩ (S.support omega \ S.support g) =
        S.support c \ S.support g := by
    rw [hcensus.omegaOutside_eq]
    ext p
    simp [nineFiveOutside]
  have hbaseEq :
      S.support c ∩ (S.support g \ S.support omega) =
        S.support c ∩ S.support g := by
    ext p
    constructor
    · intro hp
      have hp' := Finset.mem_inter.mp hp
      exact Finset.mem_inter.mpr
        ⟨hp'.1, (Finset.mem_sdiff.mp hp'.2).1⟩
    · intro hp
      have hpNotOmega : p ∉ S.support omega := by
        intro hpOmega
        exact (Finset.disjoint_left.mp havoid) hp hpOmega
      exact Finset.mem_inter.mpr
        ⟨(Finset.mem_inter.mp hp).1,
          Finset.mem_sdiff.mpr ⟨(Finset.mem_inter.mp hp).2, hpNotOmega⟩⟩
  unfold circleCrossBlocks
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ c, ?_⟩
  change
    (S.support c ∩ (S.support g \ S.support omega)).card = 2 ∧
      (S.support c ∩ (S.support omega \ S.support g)).card = 2
  rw [hbaseEq, houtsideEq]
  exact hspec

/-- Four outsiders on a second determined circle contradict the hypothetical
`C ≤ 24` nine-point counterexample.  Melchior supplies the direct global
line row; the radical-axis principle is used only for the final `(2,2)`
cross-block capacity. -/
theorem nineFive_concyclic_impossible
    {α : Type u} [Fintype α] [DecidableEq α]
    (Mel : RealPlaneMelchiorPrinciple.{u})
    (Cross : RealPlaneRadicalAxisCrossBlockPrinciple.{u})
    (cfg : Configuration α) (hadm : Admissible cfg)
    (hcard : Fintype.card α = 9)
    (Gamma Omega : DeterminedCircle cfg)
    (hGammaCard : (circleTrace cfg Gamma.1).card = 5)
    (hOutsideOmega :
      nineFiveOutside (blockSystem cfg) (Sum.inr Gamma) ⊆
        circleTrace cfg Omega.1)
    (hcircles : Erdos506.V4.circleCount cfg ≤ 24) :
    False := by
  classical
  let S := blockSystem cfg
  let g : GeometricBlock cfg := Sum.inr Gamma
  let omega : GeometricBlock cfg := Sum.inr Omega
  let A := nineFiveCircleType S g 1 2
  let B := nineFiveCircleType S g 2 2
  let Uline := nineFiveLineType S g 2 1
  let Vline := nineFiveLineType S g 2 2
  let Ell := nineFiveLineType S g 1 2
  let W := B ∪ Vline
  let delta := (S.support omega ∩ S.support g).card
  have hgkind : S.kind g = .circle := by
    rfl
  have homegakind : S.kind omega = .circle := by
    rfl
  have hgcard : (S.support g).card = 5 := by
    simpa [S, g] using hGammaCard
  have houtsideOmega : nineFiveOutside S g ⊆ S.support omega := by
    simpa [S, g, omega] using hOutsideOmega
  have hcircleCap : ∀ b, S.kind b = .circle → (S.support b).card ≤ 5 := by
    intro b hb
    cases b with
    | inl L => cases hb
    | inr c =>
        simpa [S] using
          circleTrace_card_le_five_of_nine_of_circleCount_le
            cfg hadm hcard hcircles c
  have hcensus := nineFive_concyclic_census S g omega hcard hgkind hgcard
    hcircleCap homegakind houtsideOmega
  have hXcard : (nineFiveOutside S g).card = 4 :=
    nineFiveOutside_card S g hcard hgcard
  have homegaOutsideCard : (S.support omega \ S.support g).card = 4 := by
    rw [hcensus.omegaOutside_eq, hXcard]
  have homegaNeG : omega ≠ g := by
    intro heq
    rw [heq, Finset.sdiff_self] at homegaOutsideCard
    simp at homegaOutsideCard
  have hGammaNeOmega : Gamma ≠ Omega := by
    intro heq
    apply homegaNeG
    simp [g, omega, heq]
  have htotal : S.totalCircleCount = Erdos506.V4.circleCount cfg := by
    rw [totalCircleCount_eq_card_determinedCircle,
      ← Erdos506.V3.circleCount_eq_card_determinedCircle]
  have htotalLe : S.totalCircleCount ≤ 24 := by
    rw [htotal]
    exact hcircles
  have hglobalCfg :=
    globalLineRow_le_choose_two_sub_three_of_realPlaneMelchior Mel cfg hadm
  rw [hcard] at hglobalCfg
  norm_num [Nat.choose] at hglobalCfg
  have hglobal : S.globalLineRow ≤ 33 := by
    simpa [S, Erdos506.V1.globalLineRow] using hglobalCfg
  have hRuv : nineFiveR S g = Uline.card + 2 * Vline.card := by
    simpa [Uline, Vline] using hcensus.r_eq
  have hcircleLinear :
      S.totalCircleCount + B.card + nineFiveR S g = 42 + A.card := by
    simpa [A, B] using hcensus.circle_linear_row
  have htripleRaw :
      A.card + 2 * B.card + 2 * Vline.card + Ell.card +
        6 * delta = 30 := by
    simpa [A, B, Vline, Ell, delta] using hcensus.relative_triple_row
  have hglobalEq : S.globalLineRow =
      3 * (Uline.card : ℤ) + 7 * (Vline.card : ℤ) +
        3 * (Ell.card : ℤ) := by
    simpa [Uline, Vline, Ell] using hcensus.global_line_row
  have hBcap : B.card ≤ 12 := by
    simpa [B] using hcensus.b_le_twelve
  let e := 12 - B.card
  have hbe : B.card + e = 12 := by
    dsimp [e]
    omega
  have hmaster : 6 + e + A.card ≤ nineFiveR S g := by
    omega
  have hRcap := nineFiveR_le_eight S g hgkind hcard hgcard
  have hRuvZ : (nineFiveR S g : ℤ) =
      (Uline.card : ℤ) + 2 * (Vline.card : ℤ) := by
    exact_mod_cast hRuv
  have hlineZ :
      3 * (nineFiveR S g : ℤ) + 3 * (Ell.card : ℤ) +
          (Vline.card : ℤ) ≤ 33 := by
    omega
  have hline :
      3 * nineFiveR S g + 3 * Ell.card + Vline.card ≤ 33 := by
    exact_mod_cast hlineZ
  have hBVdisjoint : Disjoint B Vline := by
    rw [Finset.disjoint_left]
    intro c hcB hcV
    have hcircle := S.mem_blocksOfKind.mp (Finset.mem_filter.mp hcB).1
    have hlineKind := S.mem_blocksOfKind.mp (Finset.mem_filter.mp hcV).1
    rw [hcircle] at hlineKind
    cases hlineKind
  have hWcard : W.card = B.card + Vline.card := by
    change (B ∪ Vline).card = B.card + Vline.card
    rw [Finset.card_union_of_disjoint hBVdisjoint]
  have hWsubset : W ⊆ circleCrossBlocks cfg Gamma Omega := by
    intro c hc
    have hcases : c ∈ B ∨ c ∈ Vline := Finset.mem_union.mp hc
    exact nineFive_concyclic_two_two_subset_crossBlocks
      cfg Gamma Omega hcensus c (by simpa [B, Vline, S, g] using hcases)
  have hWleCross : W.card ≤ (circleCrossBlocks cfg Gamma Omega).card :=
    Finset.card_le_card hWsubset
  have hExclusiveOmega :
      (exclusiveCircleTrace cfg Omega Gamma).card = 4 := by
    change (S.support omega \ S.support g).card = 4
    exact homegaOutsideCard
  have hExclusiveGammaAdd :
      (exclusiveCircleTrace cfg Gamma Omega).card + delta = 5 := by
    have hsplit := Finset.card_sdiff_add_card_inter
      (S.support g) (S.support omega)
    change (S.support g \ S.support omega).card + delta = 5
    dsimp only [delta]
    rw [← hgcard]
    calc
      (S.support g \ S.support omega).card +
          (S.support omega ∩ S.support g).card =
          (S.support g \ S.support omega).card +
            (S.support g ∩ S.support omega).card := by
        rw [Finset.inter_comm]
      _ = (S.support g).card := hsplit
  have hdeltaLe : delta ≤ 1 := by
    exact hcensus.delta_le_one
  have hdeltaCases : delta = 0 ∨ delta = 1 := by omega
  rcases hdeltaCases with hdelta | hdelta
  · have hExclusiveGamma :
        (exclusiveCircleTrace cfg Gamma Omega).card = 5 := by omega
    have hcrossCap := Cross.five_four cfg Gamma Omega hGammaNeOmega
      hExclusiveGamma hExclusiveOmega
    have hcross : B.card + Vline.card ≤ 12 := by
      omega
    have htriple : Ell.card + 2 * Vline.card + A.card = 6 + 2 * e := by
      omega
    exact nine_five_concyclic_disjoint_arithmetic
      hbe hcross hmaster htriple hline
  · have hExclusiveGamma :
        (exclusiveCircleTrace cfg Gamma Omega).card = 4 := by omega
    have hcrossCap := Cross.four_four cfg Gamma Omega hGammaNeOmega
      hExclusiveGamma hExclusiveOmega
    have hcross : B.card + Vline.card ≤ 10 := by
      omega
    have hea : e + A.card ≤ 2 := by omega
    have htriple :
        Ell.card + 2 * Vline.card + A.card + 6 = 6 + 2 * e := by
      omega
    exact nine_five_concyclic_one_common_arithmetic
      hbe hcross hmaster hea htriple hline

end GeometricTerminal

end Erdos506.V1
