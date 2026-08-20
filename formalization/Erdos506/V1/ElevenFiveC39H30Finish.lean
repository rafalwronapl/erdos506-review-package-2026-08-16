import Erdos506.V1.ElevenFiveC39MixedPageAdapter
import Erdos506.V1.ElevenFiveC39SignedRowsFinish
import Mathlib.Tactic

/-!
# The all-double `H = 30` face of the C39 host router

At host weight thirty, every one of the fifteen outsider-pair fibres is
full.  This file turns that finite saturation into the actual K2.1 page
contradiction, with line and circle carriers handled by
`ElevenFiveC39MixedPageAdapter`.  The final numerical row is the exposed
C39 size-four/five row: once `A13 = A14 = 0`, it forces the outside rich
weight to be five, contradicting its finite cap three.
-/

namespace Erdos506.V1

open Erdos506.Block
open Erdos506.Block.BlockSystem
open Erdos506.Finite
open Erdos506.Incidence
open Erdos506.V4
open scoped BigOperators LinearAlgebra.Projectivization

universe u v

variable {Point : Type u} {Block : Type v}
  [Fintype Point] [Fintype Block] [DecidableEq Point]

/-! ## Small finite trace facts -/

private theorem elevenFive_hostPairFibre_trace_card
    (S : BlockSystem Point Block) (D A : Finset Point) {B : Block}
    (hB : B ∈ elevenFiveHostPairFibre S D A) :
    (S.support B ∩ D).card = 2 := by
  exact (Finset.mem_filter.mp
    ((mem_elevenFiveHostPairFibre S D A).mp hB).1).2

private theorem elevenFive_host_avoids_page_mark
    (S : BlockSystem Point Block) (D : Finset Point) (P B : Block)
    {i x y : Point}
    (hPtrace : (S.support P ∩ D).card = 1)
    (hiP : i ∈ S.support P) (hiD : i ∈ D)
    (hxP : x ∈ S.support P) (hyP : y ∈ S.support P)
    (hxNotD : x ∉ D) (hyNotD : y ∉ D) (hxy : x ≠ y)
    (hBtrace : (S.support B ∩ D).card = 2)
    (hxB : x ∈ S.support B) (hyB : y ∈ S.support B) :
    i ∉ S.support B := by
  intro hiB
  have hPB : P ≠ B := by
    intro hEq
    subst B
    omega
  have hix : i ≠ x := by
    intro h
    subst x
    exact hxNotD hiD
  have hiy : i ≠ y := by
    intro h
    subst y
    exact hyNotD hiD
  have hsub : ({i, x, y} : Finset Point) ⊆ S.support P ∩ S.support B := by
    intro q hq
    simp only [Finset.mem_insert, Finset.mem_singleton] at hq
    rcases hq with rfl | rfl | rfl
    · exact Finset.mem_inter.mpr ⟨hiP, hiB⟩
    · exact Finset.mem_inter.mpr ⟨hxP, hxB⟩
    · exact Finset.mem_inter.mpr ⟨hyP, hyB⟩
  have hthree : ({i, x, y} : Finset Point).card = 3 := by
    simp [hix, hiy, hxy]
  have hinter := S.distinct_block_inter_card_lt_three hPB
  have hle := Finset.card_le_card hsub
  omega

/-- Two host traces on adjacent outsider edges of one page cannot coincide.
If the hosts differ, they share their common outsider and the two trace
labels; if they agree, that host shares the page's outsider triple. -/
private theorem elevenFive_adjacent_host_traces_ne
    (S : BlockSystem Point Block) (D : Finset Point) (P B C : Block)
    {x y z : Point}
    (hPtrace : (S.support P ∩ D).card = 1)
    (hxP : x ∈ S.support P) (hyP : y ∈ S.support P)
    (hzP : z ∈ S.support P)
    (hxNotD : x ∉ D) (hyNotD : y ∉ D) (hzNotD : z ∉ D)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hBtrace : (S.support B ∩ D).card = 2)
    (hCtrace : (S.support C ∩ D).card = 2)
    (hxB : x ∈ S.support B) (hyB : y ∈ S.support B)
    (hxC : x ∈ S.support C) (hzC : z ∈ S.support C) :
    (S.support B ∩ D) ≠ S.support C ∩ D := by
  intro htrace
  by_cases hBC : B = C
  · subst C
    have hPB : P ≠ B := by
      intro hEq
      subst B
      omega
    have hsub : ({x, y, z} : Finset Point) ⊆ S.support P ∩ S.support B := by
      intro q hq
      simp only [Finset.mem_insert, Finset.mem_singleton] at hq
      rcases hq with rfl | rfl | rfl
      · exact Finset.mem_inter.mpr ⟨hxP, hxB⟩
      · exact Finset.mem_inter.mpr ⟨hyP, hyB⟩
      · exact Finset.mem_inter.mpr ⟨hzP, hzC⟩
    have hthree : ({x, y, z} : Finset Point).card = 3 := by
      simp [hxy, hxz, hyz]
    have hinter := S.distinct_block_inter_card_lt_three hPB
    have hle := Finset.card_le_card hsub
    omega
  · obtain ⟨u, v, huv, hBtraceEq⟩ := Finset.card_eq_two.mp hBtrace
    have huB : u ∈ S.support B := by
      have : u ∈ S.support B ∩ D := by rw [hBtraceEq]; simp
      exact (Finset.mem_inter.mp this).1
    have hvB : v ∈ S.support B := by
      have : v ∈ S.support B ∩ D := by rw [hBtraceEq]; simp
      exact (Finset.mem_inter.mp this).1
    have huD : u ∈ D := by
      have : u ∈ S.support B ∩ D := by rw [hBtraceEq]; simp
      exact (Finset.mem_inter.mp this).2
    have hvD : v ∈ D := by
      have : v ∈ S.support B ∩ D := by rw [hBtraceEq]; simp
      exact (Finset.mem_inter.mp this).2
    have huC : u ∈ S.support C := by
      have : u ∈ S.support C ∩ D := by
        rw [← htrace, hBtraceEq]
        simp
      exact (Finset.mem_inter.mp this).1
    have hvC : v ∈ S.support C := by
      have : v ∈ S.support C ∩ D := by
        rw [← htrace, hBtraceEq]
        simp
      exact (Finset.mem_inter.mp this).1
    have hux : u ≠ x := by
      intro h
      subst x
      exact hxNotD huD
    have hvx : v ≠ x := by
      intro h
      subst x
      exact hxNotD hvD
    have hsub : ({u, v, x} : Finset Point) ⊆ S.support B ∩ S.support C := by
      intro q hq
      simp only [Finset.mem_insert, Finset.mem_singleton] at hq
      rcases hq with rfl | rfl | rfl
      · exact Finset.mem_inter.mpr ⟨huB, huC⟩
      · exact Finset.mem_inter.mpr ⟨hvB, hvC⟩
      · exact Finset.mem_inter.mpr ⟨hxB, hxC⟩
    have hthree : ({u, v, x} : Finset Point).card = 3 := by
      simp [huv, hux, hvx]
    have hinter := S.distinct_block_inter_card_lt_three hBC
    have hle := Finset.card_le_card hsub
    omega

private theorem elevenFive_trace_subset_erase_mark
    (S : BlockSystem Point Block) (D : Finset Point) (B : Block) {i : Point}
    (hiB : i ∉ S.support B) :
    S.support B ∩ D ⊆ D.erase i := by
  intro q hq
  exact Finset.mem_erase.mpr
    ⟨by
      intro hqi
      subst q
      exact hiB (Finset.mem_inter.mp hq).1,
      (Finset.mem_inter.mp hq).2⟩

private theorem elevenFive_two_subset_four_cases
    (U T : Finset Point) {a b c d : Point}
    (hU : U = {a, b, c, d}) (hTsub : T ⊆ U) (hTcard : T.card = 2)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    T = {a, b} ∨ T = {a, c} ∨ T = {a, d} ∨
      T = {b, c} ∨ T = {b, d} ∨ T = {c, d} := by
  obtain ⟨u, v, huv, hT⟩ := Finset.card_eq_two.mp hTcard
  have hu : u ∈ U := hTsub (by rw [hT]; simp)
  have hv : v ∈ U := hTsub (by rw [hT]; simp)
  rw [hU] at hu hv
  simp only [Finset.mem_insert, Finset.mem_singleton] at hu hv
  rcases hu with rfl | rfl | rfl | rfl <;>
    rcases hv with rfl | rfl | rfl | rfl <;>
    simp [hT, Finset.pair_comm, hab, hac, had, hbc, hbd, hcd] at huv ⊢

private theorem elevenFive_disjoint_partner_of_pair
    (U T V : Finset Point) {a b c d : Point}
    (hU : U = {a, b, c, d}) (hVsub : V ⊆ U)
    (hVcard : V.card = 2) (hdis : Disjoint T V)
    (hT : T = {a, b}) (hcd : c ≠ d) :
    V = {c, d} := by
  apply Finset.eq_of_subset_of_card_le
  · intro q hq
    have hqU := hVsub hq
    rw [hU] at hqU
    simp only [Finset.mem_insert, Finset.mem_singleton] at hqU
    rcases hqU with rfl | rfl | rfl | rfl
    · exact False.elim ((Finset.disjoint_left.mp hdis) (by simp [hT]) hq)
    · exact False.elim ((Finset.disjoint_left.mp hdis) (by simp [hT]) hq)
    · simp
    · simp
  · simp [hVcard, hcd]

private theorem elevenFive_partition_two_four_cases
    (U T V : Finset Point) {a b c d : Point}
    (hU : U = {a, b, c, d}) (hTsub : T ⊆ U) (hVsub : V ⊆ U)
    (hTcard : T.card = 2) (hVcard : V.card = 2) (hdis : Disjoint T V)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    (T = {a, b} ∧ V = {c, d}) ∨ (T = {c, d} ∧ V = {a, b}) ∨
      (T = {a, c} ∧ V = {b, d}) ∨ (T = {b, d} ∧ V = {a, c}) ∨
        (T = {a, d} ∧ V = {b, c}) ∨ (T = {b, c} ∧ V = {a, d}) := by
  rcases elevenFive_two_subset_four_cases U T hU hTsub hTcard
    hab hac had hbc hbd hcd with hAB | hAC | hAD | hBC | hBD | hCD
  · exact Or.inl ⟨hAB,
      elevenFive_disjoint_partner_of_pair U T V hU hVsub hVcard hdis hAB hcd⟩
  · have hU' : U = {a, c, b, d} := by
      rw [hU]
      ext q
      simp [or_comm, or_left_comm, or_assoc]
    have hV : V = {b, d} :=
      elevenFive_disjoint_partner_of_pair U T V hU' hVsub hVcard hdis hAC hbd
    exact Or.inr (Or.inr (Or.inl ⟨hAC, hV⟩))
  · have hU' : U = {a, d, b, c} := by
      rw [hU]
      ext q
      simp [or_comm, or_left_comm, or_assoc]
    have hV : V = {b, c} :=
      elevenFive_disjoint_partner_of_pair U T V hU' hVsub hVcard hdis hAD hbc
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hAD, hV⟩))))
  · have hU' : U = {b, c, a, d} := by
      rw [hU]
      ext q
      simp [or_comm, or_left_comm, or_assoc]
    have hV : V = {a, d} :=
      elevenFive_disjoint_partner_of_pair U T V hU' hVsub hVcard hdis hBC had
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨hBC, hV⟩))))
  · have hU' : U = {b, d, a, c} := by
      rw [hU]
      ext q
      simp [or_comm, or_left_comm, or_assoc]
    have hV : V = {a, c} :=
      elevenFive_disjoint_partner_of_pair U T V hU' hVsub hVcard hdis hBD hac
    exact Or.inr (Or.inr (Or.inr (Or.inl ⟨hBD, hV⟩)))
  · have hU' : U = {c, d, a, b} := by
      rw [hU]
      ext q
      simp [or_comm, or_left_comm, or_assoc]
    have hV : V = {a, b} :=
      elevenFive_disjoint_partner_of_pair U T V hU' hVsub hVcard hdis hCD hab
    exact Or.inr (Or.inl ⟨hCD, hV⟩)

/-- Once two partitions of a four-set have been put in the first two
diagonal forms, a third partition disjoint from both is the remaining
diagonal, up to exchanging its two host traces. -/
private theorem elevenFive_third_partition_is_remaining
    (U T V R W : Finset Point) {a b c d : Point}
    (hU : U = {a, b, c, d})
    (hTsub : T ⊆ U) (hVsub : V ⊆ U) (hRsub : R ⊆ U) (hWsub : W ⊆ U)
    (hTcard : T.card = 2) (hVcard : V.card = 2)
    (hRcard : R.card = 2) (hWcard : W.card = 2)
    (hTV : Disjoint T V) (hRW : Disjoint R W)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    (hT : T = {a, b}) (hV : V = {c, d})
    (hTR : T ≠ R) (hVR : V ≠ R) (hRold : {a, c} ≠ R)
    (hWold : {b, d} ≠ R) :
    (R = {a, d} ∧ W = {b, c}) ∨ (R = {b, c} ∧ W = {a, d}) := by
  rcases elevenFive_partition_two_four_cases U R W hU hRsub hWsub
    hRcard hWcard hRW hab hac had hbc hbd hcd with
      hAB | hCD | hAC | hBD | hAD | hBC
  · exact False.elim (hTR (hT.trans hAB.1.symm))
  · exact False.elim (hVR (hV.trans hCD.1.symm))
  · exact False.elim (hRold (hAC.1.symm))
  · exact False.elim (hWold (hBD.1.symm))
  · exact Or.inl hAD
  · exact Or.inr hBC

/-- Three pairwise different two-by-two partitions of a four-set are the
three diagonal pairings.  The labels are chosen from the first two host
traces, so the statement retains the actual orientation of the first two
fibres and permits only the unavoidable final exchange. -/
private theorem elevenFive_three_partitions_of_four_align
    (U Txy Vxy Txz Vxz Tyz Vyz : Finset Point)
    (hUcard : U.card = 4)
    (hTxySub : Txy ⊆ U) (hVxySub : Vxy ⊆ U)
    (hTxzSub : Txz ⊆ U) (hVxzSub : Vxz ⊆ U)
    (hTyzSub : Tyz ⊆ U) (hVyzSub : Vyz ⊆ U)
    (hTxyCard : Txy.card = 2) (hVxyCard : Vxy.card = 2)
    (hTxzCard : Txz.card = 2) (hVxzCard : Vxz.card = 2)
    (hTyzCard : Tyz.card = 2) (hVyzCard : Vyz.card = 2)
    (hxyDis : Disjoint Txy Vxy) (hxzDis : Disjoint Txz Vxz)
    (hyzDis : Disjoint Tyz Vyz)
    (hxyTxz : Txy ≠ Txz) (hxyVTxz : Vxy ≠ Txz)
    (hxyTyz : Txy ≠ Tyz) (hxyVTyz : Vxy ≠ Tyz)
    (hxzTyz : Txz ≠ Tyz) (hxzVTyz : Vxz ≠ Tyz) :
    ∃ a b c d : Point,
      U = {a, b, c, d} ∧
      a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d ∧
      Txy = {a, b} ∧ Vxy = {c, d} ∧
      Txz = {a, c} ∧ Vxz = {b, d} ∧
      ((Tyz = {a, d} ∧ Vyz = {b, c}) ∨
        (Tyz = {b, c} ∧ Vyz = {a, d})) := by
  obtain ⟨a, b, hab, hTxy⟩ := Finset.card_eq_two.mp hTxyCard
  obtain ⟨c, d, hcd, hVxy⟩ := Finset.card_eq_two.mp hVxyCard
  have haTxy : a ∈ Txy := by rw [hTxy]; simp
  have hbTxy : b ∈ Txy := by rw [hTxy]; simp
  have hcVxy : c ∈ Vxy := by rw [hVxy]; simp
  have hdVxy : d ∈ Vxy := by rw [hVxy]; simp
  have hUnionSub : Txy ∪ Vxy ⊆ U := Finset.union_subset hTxySub hVxySub
  have hUnion : Txy ∪ Vxy = U := by
    apply Finset.eq_of_subset_of_card_le hUnionSub
    rw [hUcard, Finset.card_union_of_disjoint hxyDis, hTxyCard, hVxyCard]
  have hU : U = {a, b, c, d} := by
    rw [← hUnion, hTxy, hVxy]
    ext q
    simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
    tauto
  have hac : a ≠ c := by
    intro hac
    subst c
    exact (Finset.disjoint_left.mp hxyDis) haTxy hcVxy
  have had : a ≠ d := by
    intro had
    subst d
    exact (Finset.disjoint_left.mp hxyDis) haTxy hdVxy
  have hbc : b ≠ c := by
    intro hbc
    subst c
    exact (Finset.disjoint_left.mp hxyDis) hbTxy hcVxy
  have hbd : b ≠ d := by
    intro hbd
    subst d
    exact (Finset.disjoint_left.mp hxyDis) hbTxy hdVxy
  rcases elevenFive_partition_two_four_cases U Txz Vxz hU hTxzSub hVxzSub
    hTxzCard hVxzCard hxzDis hab hac had hbc hbd hcd with
      hAB | hCD | hAC | hBD | hAD | hBC
  · exact False.elim (hxyTxz (hTxy.trans hAB.1.symm))
  · exact False.elim (hxyVTxz (hVxy.trans hCD.1.symm))
  · rcases elevenFive_third_partition_is_remaining
      U Txy Vxy Tyz Vyz hU hTxySub hVxySub hTyzSub hVyzSub
      hTxyCard hVxyCard hTyzCard hVyzCard hxyDis hyzDis
      hab hac had hbc hbd hcd hTxy hVxy
      hxyTyz hxyVTyz
      (by intro h; exact hxzTyz (hAC.1.trans h))
      (by intro h; exact hxzVTyz (hAC.2.trans h)) with hthird
    exact ⟨a, b, c, d, hU, hab, hac, had, hbc, hbd, hcd,
      hTxy, hVxy, hAC.1, hAC.2, hthird⟩
  · have hU' : U = {b, a, d, c} := by
      rw [hU]
      ext q
      simp [or_comm, or_left_comm, or_assoc]
    have hab' : b ≠ a := hab.symm
    have hac' : b ≠ d := hbd
    have had' : b ≠ c := hbc
    have hbc' : a ≠ d := had
    have hbd' : a ≠ c := hac
    have hcd' : d ≠ c := hcd.symm
    rcases elevenFive_third_partition_is_remaining
      U Txy Vxy Tyz Vyz hU' hTxySub hVxySub hTyzSub hVyzSub
      hTxyCard hVxyCard hTyzCard hVyzCard hxyDis hyzDis
      hab' hac' had' hbc' hbd' hcd'
      (by simpa [Finset.pair_comm] using hTxy)
      (by simpa [Finset.pair_comm] using hVxy)
      hxyTyz hxyVTyz
      (by intro h; exact hxzTyz (hBD.1.trans h))
      (by intro h; exact hxzVTyz (hBD.2.trans h)) with hthird
    exact ⟨b, a, d, c, hU', hab', hac', had', hbc', hbd', hcd',
      by simpa [Finset.pair_comm] using hTxy,
      by simpa [Finset.pair_comm] using hVxy,
      hBD.1, hBD.2, hthird⟩
  · have hU' : U = {a, b, d, c} := by
      rw [hU]
      ext q
      simp [or_comm, or_left_comm, or_assoc]
    have hac' : a ≠ d := had
    have had' : a ≠ c := hac
    have hbc' : b ≠ d := hbd
    have hbd' : b ≠ c := hbc
    have hcd' : d ≠ c := hcd.symm
    rcases elevenFive_third_partition_is_remaining
      U Txy Vxy Tyz Vyz hU' hTxySub hVxySub hTyzSub hVyzSub
      hTxyCard hVxyCard hTyzCard hVyzCard hxyDis hyzDis
      hab hac' had' hbc' hbd' hcd'
      hTxy (by simpa [Finset.pair_comm] using hVxy)
      hxyTyz hxyVTyz
      (by intro h; exact hxzTyz (hAD.1.trans h))
      (by intro h; exact hxzVTyz (hAD.2.trans h)) with hthird
    exact ⟨a, b, d, c, hU', hab, hac', had', hbc', hbd', hcd',
      hTxy, (by simpa [Finset.pair_comm] using hVxy),
      hAD.1, hAD.2, hthird⟩
  · have hU' : U = {b, a, c, d} := by
      rw [hU]
      ext q
      simp [or_comm, or_left_comm, or_assoc]
    have hab' : b ≠ a := hab.symm
    have hac' : b ≠ c := hbc
    have had' : b ≠ d := hbd
    have hbc' : a ≠ c := hac
    have hbd' : a ≠ d := had
    rcases elevenFive_third_partition_is_remaining
      U Txy Vxy Tyz Vyz hU' hTxySub hVxySub hTyzSub hVyzSub
      hTxyCard hVxyCard hTyzCard hVyzCard hxyDis hyzDis
      hab' hac' had' hbc' hbd' hcd
      (by simpa [Finset.pair_comm] using hTxy) hVxy
      hxyTyz hxyVTyz
      (by intro h; exact hxzTyz (hBC.1.trans h))
      (by intro h; exact hxzVTyz (hBC.2.trans h)) with hthird
    exact ⟨b, a, c, d, hU', hab', hac', had', hbc', hbd', hcd,
      (by simpa [Finset.pair_comm] using hTxy), hVxy,
      hBC.1, hBC.2, hthird⟩

private theorem elevenFive_pair_mem_outside_pairs
    (D : Finset Point) {x y : Point}
    (hx : x ∉ D) (hy : y ∉ D) (hxy : x ≠ y) :
    ({x, y} : Finset Point) ∈ (Finset.univ \ D).powersetCard 2 := by
  apply Finset.mem_powersetCard.mpr
  refine ⟨?_, by simp [hxy]⟩
  intro q hq
  simp only [Finset.mem_insert, Finset.mem_singleton] at hq
  rcases hq with rfl | rfl
  · exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hx⟩
  · exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hy⟩

/-- A one-trace page with three outsiders is impossible when every pair of
its outsiders has a full two-host fibre.  This is the local mixed-carrier
K2.1 router behind both the all-double `H = 30` face and the saturated part
of the `H = 29` face. -/
theorem elevenFive_one_trace_three_outsiders_of_pairwise_double_absurd
    {α : Type u} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (Gamma : DeterminedCircle cfg)
    (hD : (circleTrace cfg Gamma.1).card = 5)
    (P : GeometricBlock cfg)
    (hPtrace : (geometricBlockSupport cfg P ∩ circleTrace cfg Gamma.1).card = 1)
    {x y z : α}
    (hx : x ∈ geometricBlockSupport cfg P \ circleTrace cfg Gamma.1)
    (hy : y ∈ geometricBlockSupport cfg P \ circleTrace cfg Gamma.1)
    (hz : z ∈ geometricBlockSupport cfg P \ circleTrace cfg Gamma.1)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hcardXY : (elevenFiveHostPairFibre (blockSystem cfg)
      (circleTrace cfg Gamma.1) {x, y}).card = 2)
    (hcardXZ : (elevenFiveHostPairFibre (blockSystem cfg)
      (circleTrace cfg Gamma.1) {x, z}).card = 2)
    (hcardYZ : (elevenFiveHostPairFibre (blockSystem cfg)
      (circleTrace cfg Gamma.1) {y, z}).card = 2) :
    False := by
  classical
  let D : Finset α := circleTrace cfg Gamma.1
  let S := blockSystem cfg
  have hPtraceS : (S.support P ∩ D).card = 1 := by
    simpa [S, D, blockSystem, geometricBlockSystem] using hPtrace
  obtain ⟨i, hiEq⟩ := Finset.card_eq_one.mp hPtraceS
  have hiPD : i ∈ S.support P ∩ D := by
    rw [hiEq]
    simp
  have hiP : i ∈ S.support P := (Finset.mem_inter.mp hiPD).1
  have hiD : i ∈ D := (Finset.mem_inter.mp hiPD).2
  have hxP : x ∈ S.support P := (Finset.mem_sdiff.mp hx).1
  have hyP : y ∈ S.support P := (Finset.mem_sdiff.mp hy).1
  have hzP : z ∈ S.support P := (Finset.mem_sdiff.mp hz).1
  have hxNotD : x ∉ D := (Finset.mem_sdiff.mp hx).2
  have hyNotD : y ∉ D := (Finset.mem_sdiff.mp hy).2
  have hzNotD : z ∉ D := (Finset.mem_sdiff.mp hz).2
  have hAxy : ({x, y} : Finset α) ∈ (Finset.univ \ D).powersetCard 2 :=
    elevenFive_pair_mem_outside_pairs D hxNotD hyNotD hxy
  have hAxz : ({x, z} : Finset α) ∈ (Finset.univ \ D).powersetCard 2 :=
    elevenFive_pair_mem_outside_pairs D hxNotD hzNotD hxz
  have hAyz : ({y, z} : Finset α) ∈ (Finset.univ \ D).powersetCard 2 :=
    elevenFive_pair_mem_outside_pairs D hyNotD hzNotD hyz
  have hD' : D.card = 5 := by simpa [D] using hD
  obtain ⟨Bxy, Exy, hBxy, hExy, hBxyE⟩ :=
    elevenFiveHostPairFibre_exists_two_distinct_of_card_eq_two S D {x, y} hcardXY
  obtain ⟨Bxz, Exz, hBxz, hExz, hBxzE⟩ :=
    elevenFiveHostPairFibre_exists_two_distinct_of_card_eq_two S D {x, z} hcardXZ
  obtain ⟨Byz, Eyz, hByz, hEyz, hByzE⟩ :=
    elevenFiveHostPairFibre_exists_two_distinct_of_card_eq_two S D {y, z} hcardYZ
  have hBxyData := (mem_elevenFiveHostPairFibre S D {x, y}).mp hBxy
  have hExyData := (mem_elevenFiveHostPairFibre S D {x, y}).mp hExy
  have hBxzData := (mem_elevenFiveHostPairFibre S D {x, z}).mp hBxz
  have hExzData := (mem_elevenFiveHostPairFibre S D {x, z}).mp hExz
  have hByzData := (mem_elevenFiveHostPairFibre S D {y, z}).mp hByz
  have hEyzData := (mem_elevenFiveHostPairFibre S D {y, z}).mp hEyz
  have hxBxy : x ∈ S.support Bxy := hBxyData.2 (by simp)
  have hyBxy : y ∈ S.support Bxy := hBxyData.2 (by simp)
  have hxExy : x ∈ S.support Exy := hExyData.2 (by simp)
  have hyExy : y ∈ S.support Exy := hExyData.2 (by simp)
  have hxBxz : x ∈ S.support Bxz := hBxzData.2 (by simp)
  have hzBxz : z ∈ S.support Bxz := hBxzData.2 (by simp)
  have hxExz : x ∈ S.support Exz := hExzData.2 (by simp)
  have hzExz : z ∈ S.support Exz := hExzData.2 (by simp)
  have hyByz : y ∈ S.support Byz := hByzData.2 (by simp)
  have hzByz : z ∈ S.support Byz := hByzData.2 (by simp)
  have hyEyz : y ∈ S.support Eyz := hEyzData.2 (by simp)
  have hzEyz : z ∈ S.support Eyz := hEyzData.2 (by simp)
  have hTxyCard : (S.support Bxy ∩ D).card = 2 :=
    elevenFive_hostPairFibre_trace_card S D {x, y} hBxy
  have hVxyCard : (S.support Exy ∩ D).card = 2 :=
    elevenFive_hostPairFibre_trace_card S D {x, y} hExy
  have hTxzCard : (S.support Bxz ∩ D).card = 2 :=
    elevenFive_hostPairFibre_trace_card S D {x, z} hBxz
  have hVxzCard : (S.support Exz ∩ D).card = 2 :=
    elevenFive_hostPairFibre_trace_card S D {x, z} hExz
  have hTyzCard : (S.support Byz ∩ D).card = 2 :=
    elevenFive_hostPairFibre_trace_card S D {y, z} hByz
  have hVyzCard : (S.support Eyz ∩ D).card = 2 :=
    elevenFive_hostPairFibre_trace_card S D {y, z} hEyz
  have hiBxy : i ∉ S.support Bxy :=
    elevenFive_host_avoids_page_mark S D P Bxy hPtraceS hiP hiD
      hxP hyP hxNotD hyNotD hxy hTxyCard
      hxBxy hyBxy
  have hiExy : i ∉ S.support Exy :=
    elevenFive_host_avoids_page_mark S D P Exy hPtraceS hiP hiD
      hxP hyP hxNotD hyNotD hxy hVxyCard
      hxExy hyExy
  have hiBxz : i ∉ S.support Bxz :=
    elevenFive_host_avoids_page_mark S D P Bxz hPtraceS hiP hiD
      hxP hzP hxNotD hzNotD hxz hTxzCard
      hxBxz hzBxz
  have hiExz : i ∉ S.support Exz :=
    elevenFive_host_avoids_page_mark S D P Exz hPtraceS hiP hiD
      hxP hzP hxNotD hzNotD hxz hVxzCard
      hxExz hzExz
  have hiByz : i ∉ S.support Byz :=
    elevenFive_host_avoids_page_mark S D P Byz hPtraceS hiP hiD
      hyP hzP hyNotD hzNotD hyz hTyzCard
      hyByz hzByz
  have hiEyz : i ∉ S.support Eyz :=
    elevenFive_host_avoids_page_mark S D P Eyz hPtraceS hiP hiD
      hyP hzP hyNotD hzNotD hyz hVyzCard
      hyEyz hzEyz
  have hUcard : (D.erase i).card = 4 := by
    rw [Finset.card_erase_of_mem hiD, hD']
  have hTxySub := elevenFive_trace_subset_erase_mark S D Bxy hiBxy
  have hVxySub := elevenFive_trace_subset_erase_mark S D Exy hiExy
  have hTxzSub := elevenFive_trace_subset_erase_mark S D Bxz hiBxz
  have hVxzSub := elevenFive_trace_subset_erase_mark S D Exz hiExz
  have hTyzSub := elevenFive_trace_subset_erase_mark S D Byz hiByz
  have hVyzSub := elevenFive_trace_subset_erase_mark S D Eyz hiEyz
  have hxyDis := elevenFiveHostPairFibre_trace_disjoint S D {x, y}
    hAxy hBxy hExy hBxyE
  have hxzDis := elevenFiveHostPairFibre_trace_disjoint S D {x, z}
    hAxz hBxz hExz hBxzE
  have hyzDis := elevenFiveHostPairFibre_trace_disjoint S D {y, z}
    hAyz hByz hEyz hByzE
  have hneXYXZ (B C : GeometricBlock cfg)
      (hB : B ∈ elevenFiveHostPairFibre S D {x, y})
      (hC : C ∈ elevenFiveHostPairFibre S D {x, z}) :
      S.support B ∩ D ≠ S.support C ∩ D := by
    apply elevenFive_adjacent_host_traces_ne S D P B C hPtraceS
      hxP hyP hzP hxNotD hyNotD hzNotD hxy hxz hyz
    · exact elevenFive_hostPairFibre_trace_card S D {x, y} hB
    · exact elevenFive_hostPairFibre_trace_card S D {x, z} hC
    · exact ((mem_elevenFiveHostPairFibre S D {x, y}).mp hB).2 (by simp)
    · exact ((mem_elevenFiveHostPairFibre S D {x, y}).mp hB).2 (by simp)
    · exact ((mem_elevenFiveHostPairFibre S D {x, z}).mp hC).2 (by simp)
    · exact ((mem_elevenFiveHostPairFibre S D {x, z}).mp hC).2 (by simp)
  have hneXYYZ (B C : GeometricBlock cfg)
      (hB : B ∈ elevenFiveHostPairFibre S D {x, y})
      (hC : C ∈ elevenFiveHostPairFibre S D {y, z}) :
      S.support B ∩ D ≠ S.support C ∩ D := by
    apply elevenFive_adjacent_host_traces_ne S D P B C hPtraceS
      hyP hxP hzP hyNotD hxNotD hzNotD hxy.symm hyz hxz
    · exact elevenFive_hostPairFibre_trace_card S D {x, y} hB
    · exact elevenFive_hostPairFibre_trace_card S D {y, z} hC
    · exact ((mem_elevenFiveHostPairFibre S D {x, y}).mp hB).2 (by simp)
    · exact ((mem_elevenFiveHostPairFibre S D {x, y}).mp hB).2 (by simp)
    · exact ((mem_elevenFiveHostPairFibre S D {y, z}).mp hC).2 (by simp)
    · exact ((mem_elevenFiveHostPairFibre S D {y, z}).mp hC).2 (by simp)
  have hneXZYZ (B C : GeometricBlock cfg)
      (hB : B ∈ elevenFiveHostPairFibre S D {x, z})
      (hC : C ∈ elevenFiveHostPairFibre S D {y, z}) :
      S.support B ∩ D ≠ S.support C ∩ D := by
    apply elevenFive_adjacent_host_traces_ne S D P B C hPtraceS
      hzP hxP hyP hzNotD hxNotD hyNotD hxz.symm hyz.symm hxy
    · exact elevenFive_hostPairFibre_trace_card S D {x, z} hB
    · exact elevenFive_hostPairFibre_trace_card S D {y, z} hC
    · exact ((mem_elevenFiveHostPairFibre S D {x, z}).mp hB).2 (by simp)
    · exact ((mem_elevenFiveHostPairFibre S D {x, z}).mp hB).2 (by simp)
    · exact ((mem_elevenFiveHostPairFibre S D {y, z}).mp hC).2 (by simp)
    · exact ((mem_elevenFiveHostPairFibre S D {y, z}).mp hC).2 (by simp)
  rcases elevenFive_three_partitions_of_four_align (D.erase i)
      (S.support Bxy ∩ D) (S.support Exy ∩ D)
      (S.support Bxz ∩ D) (S.support Exz ∩ D)
      (S.support Byz ∩ D) (S.support Eyz ∩ D)
      hUcard hTxySub hVxySub hTxzSub hVxzSub hTyzSub hVyzSub
      hTxyCard hVxyCard hTxzCard hVxzCard hTyzCard hVyzCard
      hxyDis hxzDis hyzDis
      (hneXYXZ Bxy Bxz hBxy hBxz)
      (hneXYXZ Exy Bxz hExy hBxz)
      (hneXYYZ Bxy Byz hBxy hByz)
      (hneXYYZ Exy Byz hExy hByz)
      (hneXZYZ Bxz Byz hBxz hByz)
      (hneXZYZ Exz Byz hExz hByz) with
      ⟨a, b, c, d, hU, hab, hac, had, hbc, hbd, hcd,
        hTxy, hVxy, hTxz, hVxz, hTyz⟩
  have haU : a ∈ D.erase i := by rw [hU]; simp
  have hbU : b ∈ D.erase i := by rw [hU]; simp
  have hcU : c ∈ D.erase i := by rw [hU]; simp
  have hdU : d ∈ D.erase i := by rw [hU]; simp
  have haD : a ∈ D := (Finset.mem_erase.mp haU).2
  have hbD : b ∈ D := (Finset.mem_erase.mp hbU).2
  have hcD : c ∈ D := (Finset.mem_erase.mp hcU).2
  have hdD : d ∈ D := (Finset.mem_erase.mp hdU).2
  have hnotP (q : α) (hq : q ∈ D.erase i) : q ∉ S.support P := by
    intro hqP
    have hqPD : q ∈ S.support P ∩ D :=
      Finset.mem_inter.mpr ⟨hqP, (Finset.mem_erase.mp hq).2⟩
    rw [hiEq] at hqPD
    have hqi : q = i := by simpa using hqPD
    exact (Finset.mem_erase.mp hq).1 hqi
  have haBxy : a ∈ S.support Bxy :=
    (Finset.mem_inter.mp (by rw [hTxy]; simp)).1
  have hbBxy : b ∈ S.support Bxy :=
    (Finset.mem_inter.mp (by rw [hTxy]; simp)).1
  have hcExy : c ∈ S.support Exy :=
    (Finset.mem_inter.mp (by rw [hVxy]; simp)).1
  have hdExy : d ∈ S.support Exy :=
    (Finset.mem_inter.mp (by rw [hVxy]; simp)).1
  have haBxz : a ∈ S.support Bxz :=
    (Finset.mem_inter.mp (by rw [hTxz]; simp)).1
  have hcBxz : c ∈ S.support Bxz :=
    (Finset.mem_inter.mp (by rw [hTxz]; simp)).1
  have hbExz : b ∈ S.support Exz :=
    (Finset.mem_inter.mp (by rw [hVxz]; simp)).1
  have hdExz : d ∈ S.support Exz :=
    (Finset.mem_inter.mp (by rw [hVxz]; simp)).1
  rcases hTyz with hTyz | hTyz
  · have haByz : a ∈ S.support Byz :=
      (Finset.mem_inter.mp (by rw [hTyz.1]; simp)).1
    have hdByz : d ∈ S.support Byz :=
      (Finset.mem_inter.mp (by rw [hTyz.1]; simp)).1
    have hbEyz : b ∈ S.support Eyz :=
      (Finset.mem_inter.mp (by rw [hTyz.2]; simp)).1
    have hcEyz : c ∈ S.support Eyz :=
      (Finset.mem_inter.mp (by rw [hTyz.2]; simp)).1
    rcases P with L | K
    · exact elevenFive_mixedLinePage_allDoubleTriangle_absurd cfg Gamma L
        (by simpa [D] using haD) (by simpa [D] using hbD)
        (by simpa [D] using hcD) (by simpa [D] using hdD)
        hab hac had hbc hbd hcd
        (by
          apply mem_lineSupport.mpr
          simpa [S, blockSystem, geometricBlockSystem, geometricBlockSupport] using hxP)
        (by
          apply mem_lineSupport.mpr
          simpa [S, blockSystem, geometricBlockSystem, geometricBlockSupport] using hyP)
        (by
          apply mem_lineSupport.mpr
          simpa [S, blockSystem, geometricBlockSystem, geometricBlockSupport] using hzP)
        hxy hxz hyz
        (by intro ha; apply hnotP a haU; simpa [S, blockSystem,
          geometricBlockSystem, geometricBlockSupport] using ha)
        (by intro hb; apply hnotP b hbU; simpa [S, blockSystem,
          geometricBlockSystem, geometricBlockSupport] using hb)
        (by intro hc; apply hnotP c hcU; simpa [S, blockSystem,
          geometricBlockSystem, geometricBlockSupport] using hc)
        (by intro hd; apply hnotP d hdU; simpa [S, blockSystem,
          geometricBlockSystem, geometricBlockSupport] using hd)
        (by simpa [D] using hxNotD) (by simpa [D] using hyNotD)
        (by simpa [D] using hzNotD)
        Bxy Exy Bxz Exz Byz Eyz hBxyE hBxzE hByzE
        (by simpa [S, D] using hBxy) (by simpa [S, D] using hExy)
        (by simpa [S, D] using hBxz) (by simpa [S, D] using hExz)
        (by simpa [S, D] using hByz) (by simpa [S, D] using hEyz)
        (by simpa [S, blockSystem, geometricBlockSystem] using haBxy)
        (by simpa [S, blockSystem, geometricBlockSystem] using hbBxy)
        (by simpa [S, blockSystem, geometricBlockSystem] using hBxyData.2 (by simp))
        (by simpa [S, blockSystem, geometricBlockSystem] using hBxyData.2 (by simp))
        (by simpa [S, blockSystem, geometricBlockSystem] using hcExy)
        (by simpa [S, blockSystem, geometricBlockSystem] using hdExy)
        (by simpa [S, blockSystem, geometricBlockSystem] using hExyData.2 (by simp))
        (by simpa [S, blockSystem, geometricBlockSystem] using hExyData.2 (by simp))
        (by simpa [S, blockSystem, geometricBlockSystem] using haBxz)
        (by simpa [S, blockSystem, geometricBlockSystem] using hcBxz)
        (by simpa [S, blockSystem, geometricBlockSystem] using hBxzData.2 (by simp))
        (by simpa [S, blockSystem, geometricBlockSystem] using hBxzData.2 (by simp))
        (by simpa [S, blockSystem, geometricBlockSystem] using hbExz)
        (by simpa [S, blockSystem, geometricBlockSystem] using hdExz)
        (by simpa [S, blockSystem, geometricBlockSystem] using hExzData.2 (by simp))
        (by simpa [S, blockSystem, geometricBlockSystem] using hExzData.2 (by simp))
        (by simpa [S, blockSystem, geometricBlockSystem] using haByz)
        (by simpa [S, blockSystem, geometricBlockSystem] using hdByz)
        (by simpa [S, blockSystem, geometricBlockSystem] using hByzData.2 (by simp))
        (by simpa [S, blockSystem, geometricBlockSystem] using hByzData.2 (by simp))
        (by simpa [S, blockSystem, geometricBlockSystem] using hbEyz)
        (by simpa [S, blockSystem, geometricBlockSystem] using hcEyz)
        (by simpa [S, blockSystem, geometricBlockSystem] using hEyzData.2 (by simp))
        (by simpa [S, blockSystem, geometricBlockSystem] using hEyzData.2 (by simp))
    · exact elevenFive_mixedCirclePage_allDoubleTriangle_absurd cfg Gamma K
        (by simpa [D] using haD) (by simpa [D] using hbD)
        (by simpa [D] using hcD) (by simpa [D] using hdD)
        hab hac had hbc hbd hcd
        (by
          apply mem_circleTrace.mpr
          simpa [S, blockSystem, geometricBlockSystem, geometricBlockSupport] using hxP)
        (by
          apply mem_circleTrace.mpr
          simpa [S, blockSystem, geometricBlockSystem, geometricBlockSupport] using hyP)
        (by
          apply mem_circleTrace.mpr
          simpa [S, blockSystem, geometricBlockSystem, geometricBlockSupport] using hzP)
        hxy hxz hyz
        (by intro ha; apply hnotP a haU; simpa [S, blockSystem,
          geometricBlockSystem, geometricBlockSupport] using ha)
        (by intro hb; apply hnotP b hbU; simpa [S, blockSystem,
          geometricBlockSystem, geometricBlockSupport] using hb)
        (by intro hc; apply hnotP c hcU; simpa [S, blockSystem,
          geometricBlockSystem, geometricBlockSupport] using hc)
        (by intro hd; apply hnotP d hdU; simpa [S, blockSystem,
          geometricBlockSystem, geometricBlockSupport] using hd)
        (by simpa [D] using hxNotD) (by simpa [D] using hyNotD)
        (by simpa [D] using hzNotD)
        Bxy Exy Bxz Exz Byz Eyz hBxyE hBxzE hByzE
        (by simpa [S, D] using hBxy) (by simpa [S, D] using hExy)
        (by simpa [S, D] using hBxz) (by simpa [S, D] using hExz)
        (by simpa [S, D] using hByz) (by simpa [S, D] using hEyz)
        (by simpa [S, blockSystem, geometricBlockSystem] using haBxy)
        (by simpa [S, blockSystem, geometricBlockSystem] using hbBxy)
        (by simpa [S, blockSystem, geometricBlockSystem] using hBxyData.2 (by simp))
        (by simpa [S, blockSystem, geometricBlockSystem] using hBxyData.2 (by simp))
        (by simpa [S, blockSystem, geometricBlockSystem] using hcExy)
        (by simpa [S, blockSystem, geometricBlockSystem] using hdExy)
        (by simpa [S, blockSystem, geometricBlockSystem] using hExyData.2 (by simp))
        (by simpa [S, blockSystem, geometricBlockSystem] using hExyData.2 (by simp))
        (by simpa [S, blockSystem, geometricBlockSystem] using haBxz)
        (by simpa [S, blockSystem, geometricBlockSystem] using hcBxz)
        (by simpa [S, blockSystem, geometricBlockSystem] using hBxzData.2 (by simp))
        (by simpa [S, blockSystem, geometricBlockSystem] using hBxzData.2 (by simp))
        (by simpa [S, blockSystem, geometricBlockSystem] using hbExz)
        (by simpa [S, blockSystem, geometricBlockSystem] using hdExz)
        (by simpa [S, blockSystem, geometricBlockSystem] using hExzData.2 (by simp))
        (by simpa [S, blockSystem, geometricBlockSystem] using hExzData.2 (by simp))
        (by simpa [S, blockSystem, geometricBlockSystem] using haByz)
        (by simpa [S, blockSystem, geometricBlockSystem] using hdByz)
        (by simpa [S, blockSystem, geometricBlockSystem] using hByzData.2 (by simp))
        (by simpa [S, blockSystem, geometricBlockSystem] using hByzData.2 (by simp))
        (by simpa [S, blockSystem, geometricBlockSystem] using hbEyz)
        (by simpa [S, blockSystem, geometricBlockSystem] using hcEyz)
        (by simpa [S, blockSystem, geometricBlockSystem] using hEyzData.2 (by simp))
        (by simpa [S, blockSystem, geometricBlockSystem] using hEyzData.2 (by simp))
  · have hbByz : b ∈ S.support Byz :=
      (Finset.mem_inter.mp (by rw [hTyz.1]; simp)).1
    have hcByz : c ∈ S.support Byz :=
      (Finset.mem_inter.mp (by rw [hTyz.1]; simp)).1
    have haEyz : a ∈ S.support Eyz :=
      (Finset.mem_inter.mp (by rw [hTyz.2]; simp)).1
    have hdEyz : d ∈ S.support Eyz :=
      (Finset.mem_inter.mp (by rw [hTyz.2]; simp)).1
    rcases P with L | K
    · exact elevenFive_mixedLinePage_allDoubleTriangle_absurd cfg Gamma L
        (by simpa [D] using haD) (by simpa [D] using hbD)
        (by simpa [D] using hcD) (by simpa [D] using hdD)
        hab hac had hbc hbd hcd
        (by
          apply mem_lineSupport.mpr
          simpa [S, blockSystem, geometricBlockSystem, geometricBlockSupport] using hxP)
        (by
          apply mem_lineSupport.mpr
          simpa [S, blockSystem, geometricBlockSystem, geometricBlockSupport] using hyP)
        (by
          apply mem_lineSupport.mpr
          simpa [S, blockSystem, geometricBlockSystem, geometricBlockSupport] using hzP)
        hxy hxz hyz
        (by intro ha; apply hnotP a haU; simpa [S, blockSystem,
          geometricBlockSystem, geometricBlockSupport] using ha)
        (by intro hb; apply hnotP b hbU; simpa [S, blockSystem,
          geometricBlockSystem, geometricBlockSupport] using hb)
        (by intro hc; apply hnotP c hcU; simpa [S, blockSystem,
          geometricBlockSystem, geometricBlockSupport] using hc)
        (by intro hd; apply hnotP d hdU; simpa [S, blockSystem,
          geometricBlockSystem, geometricBlockSupport] using hd)
        (by simpa [D] using hxNotD) (by simpa [D] using hyNotD)
        (by simpa [D] using hzNotD)
        Bxy Exy Bxz Exz Eyz Byz hBxyE hBxzE hByzE.symm
        (by simpa [S, D] using hBxy) (by simpa [S, D] using hExy)
        (by simpa [S, D] using hBxz) (by simpa [S, D] using hExz)
        (by simpa [S, D] using hEyz) (by simpa [S, D] using hByz)
        (by simpa [S, blockSystem, geometricBlockSystem] using haBxy)
        (by simpa [S, blockSystem, geometricBlockSystem] using hbBxy)
        (by simpa [S, blockSystem, geometricBlockSystem] using hBxyData.2 (by simp))
        (by simpa [S, blockSystem, geometricBlockSystem] using hBxyData.2 (by simp))
        (by simpa [S, blockSystem, geometricBlockSystem] using hcExy)
        (by simpa [S, blockSystem, geometricBlockSystem] using hdExy)
        (by simpa [S, blockSystem, geometricBlockSystem] using hExyData.2 (by simp))
        (by simpa [S, blockSystem, geometricBlockSystem] using hExyData.2 (by simp))
        (by simpa [S, blockSystem, geometricBlockSystem] using haBxz)
        (by simpa [S, blockSystem, geometricBlockSystem] using hcBxz)
        (by simpa [S, blockSystem, geometricBlockSystem] using hBxzData.2 (by simp))
        (by simpa [S, blockSystem, geometricBlockSystem] using hBxzData.2 (by simp))
        (by simpa [S, blockSystem, geometricBlockSystem] using hbExz)
        (by simpa [S, blockSystem, geometricBlockSystem] using hdExz)
        (by simpa [S, blockSystem, geometricBlockSystem] using hExzData.2 (by simp))
        (by simpa [S, blockSystem, geometricBlockSystem] using hExzData.2 (by simp))
        (by simpa [S, blockSystem, geometricBlockSystem] using haEyz)
        (by simpa [S, blockSystem, geometricBlockSystem] using hdEyz)
        (by simpa [S, blockSystem, geometricBlockSystem] using hEyzData.2 (by simp))
        (by simpa [S, blockSystem, geometricBlockSystem] using hEyzData.2 (by simp))
        (by simpa [S, blockSystem, geometricBlockSystem] using hbByz)
        (by simpa [S, blockSystem, geometricBlockSystem] using hcByz)
        (by simpa [S, blockSystem, geometricBlockSystem] using hByzData.2 (by simp))
        (by simpa [S, blockSystem, geometricBlockSystem] using hByzData.2 (by simp))

    · exact elevenFive_mixedCirclePage_allDoubleTriangle_absurd cfg Gamma K
        (by simpa [D] using haD) (by simpa [D] using hbD)
        (by simpa [D] using hcD) (by simpa [D] using hdD)
        hab hac had hbc hbd hcd
        (by
          apply mem_circleTrace.mpr
          simpa [S, blockSystem, geometricBlockSystem, geometricBlockSupport] using hxP)
        (by
          apply mem_circleTrace.mpr
          simpa [S, blockSystem, geometricBlockSystem, geometricBlockSupport] using hyP)
        (by
          apply mem_circleTrace.mpr
          simpa [S, blockSystem, geometricBlockSystem, geometricBlockSupport] using hzP)
        hxy hxz hyz
        (by intro ha; apply hnotP a haU; simpa [S, blockSystem,
          geometricBlockSystem, geometricBlockSupport] using ha)
        (by intro hb; apply hnotP b hbU; simpa [S, blockSystem,
          geometricBlockSystem, geometricBlockSupport] using hb)
        (by intro hc; apply hnotP c hcU; simpa [S, blockSystem,
          geometricBlockSystem, geometricBlockSupport] using hc)
        (by intro hd; apply hnotP d hdU; simpa [S, blockSystem,
          geometricBlockSystem, geometricBlockSupport] using hd)
        (by simpa [D] using hxNotD) (by simpa [D] using hyNotD)
        (by simpa [D] using hzNotD)
        Bxy Exy Bxz Exz Eyz Byz hBxyE hBxzE hByzE.symm
        (by simpa [S, D] using hBxy) (by simpa [S, D] using hExy)
        (by simpa [S, D] using hBxz) (by simpa [S, D] using hExz)
        (by simpa [S, D] using hEyz) (by simpa [S, D] using hByz)
        (by simpa [S, blockSystem, geometricBlockSystem] using haBxy)
        (by simpa [S, blockSystem, geometricBlockSystem] using hbBxy)
        (by simpa [S, blockSystem, geometricBlockSystem] using hBxyData.2 (by simp))
        (by simpa [S, blockSystem, geometricBlockSystem] using hBxyData.2 (by simp))
        (by simpa [S, blockSystem, geometricBlockSystem] using hcExy)
        (by simpa [S, blockSystem, geometricBlockSystem] using hdExy)
        (by simpa [S, blockSystem, geometricBlockSystem] using hExyData.2 (by simp))
        (by simpa [S, blockSystem, geometricBlockSystem] using hExyData.2 (by simp))
        (by simpa [S, blockSystem, geometricBlockSystem] using haBxz)
        (by simpa [S, blockSystem, geometricBlockSystem] using hcBxz)
        (by simpa [S, blockSystem, geometricBlockSystem] using hBxzData.2 (by simp))
        (by simpa [S, blockSystem, geometricBlockSystem] using hBxzData.2 (by simp))
        (by simpa [S, blockSystem, geometricBlockSystem] using hbExz)
        (by simpa [S, blockSystem, geometricBlockSystem] using hdExz)
        (by simpa [S, blockSystem, geometricBlockSystem] using hExzData.2 (by simp))
        (by simpa [S, blockSystem, geometricBlockSystem] using hExzData.2 (by simp))
        (by simpa [S, blockSystem, geometricBlockSystem] using haEyz)
        (by simpa [S, blockSystem, geometricBlockSystem] using hdEyz)
        (by simpa [S, blockSystem, geometricBlockSystem] using hEyzData.2 (by simp))
        (by simpa [S, blockSystem, geometricBlockSystem] using hEyzData.2 (by simp))
        (by simpa [S, blockSystem, geometricBlockSystem] using hbByz)
        (by simpa [S, blockSystem, geometricBlockSystem] using hcByz)
        (by simpa [S, blockSystem, geometricBlockSystem] using hByzData.2 (by simp))
        (by simpa [S, blockSystem, geometricBlockSystem] using hByzData.2 (by simp))

/-- At `H = 30`, every outsider pair is full, so the local all-double page
router applies. -/
theorem elevenFive_c39_h30_one_trace_three_outsiders_absurd
    {α : Type u} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (Gamma : DeterminedCircle cfg)
    (hpoint : Fintype.card α = 11)
    (hD : (circleTrace cfg Gamma.1).card = 5)
    (hhost : elevenFiveHostWeight (blockSystem cfg)
      (circleTrace cfg Gamma.1) = 30)
    (P : GeometricBlock cfg)
    (hPtrace : (geometricBlockSupport cfg P ∩ circleTrace cfg Gamma.1).card = 1)
    (hout : 3 ≤ (geometricBlockSupport cfg P \ circleTrace cfg Gamma.1).card) :
    False := by
  have houtsideThree : 2 <
      (geometricBlockSupport cfg P \ circleTrace cfg Gamma.1).card := by
    omega
  obtain ⟨x, hx, y, hy, z, hz, hxy, hxz, hyz⟩ :=
    Finset.two_lt_card.mp houtsideThree
  apply elevenFive_one_trace_three_outsiders_of_pairwise_double_absurd
    cfg Gamma hD P hPtrace hx hy hz hxy hxz hyz
  · apply elevenFiveHostPairFibre_card_eq_two_of_hostWeight_eq_thirty
      (blockSystem cfg) (circleTrace cfg Gamma.1) hpoint hD hhost
    exact elevenFive_pair_mem_outside_pairs (circleTrace cfg Gamma.1)
      (Finset.mem_sdiff.mp hx).2 (Finset.mem_sdiff.mp hy).2 hxy
  · apply elevenFiveHostPairFibre_card_eq_two_of_hostWeight_eq_thirty
      (blockSystem cfg) (circleTrace cfg Gamma.1) hpoint hD hhost
    exact elevenFive_pair_mem_outside_pairs (circleTrace cfg Gamma.1)
      (Finset.mem_sdiff.mp hx).2 (Finset.mem_sdiff.mp hz).2 hxz
  · apply elevenFiveHostPairFibre_card_eq_two_of_hostWeight_eq_thirty
      (blockSystem cfg) (circleTrace cfg Gamma.1) hpoint hD hhost
    exact elevenFive_pair_mem_outside_pairs (circleTrace cfg Gamma.1)
      (Finset.mem_sdiff.mp hy).2 (Finset.mem_sdiff.mp hz).2 hyz

/-- The all-double `H = 30` face has no relative `(1,3)` page. -/
theorem elevenFive_c39_h30_relativeCount_one_three_eq_zero
    {α : Type u} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (Gamma : DeterminedCircle cfg)
    (hpoint : Fintype.card α = 11)
    (hD : (circleTrace cfg Gamma.1).card = 5)
    (hhost : elevenFiveHostWeight (blockSystem cfg)
      (circleTrace cfg Gamma.1) = 30) :
    elevenFiveRelativeCount (blockSystem cfg) (circleTrace cfg Gamma.1) 1 3 = 0 := by
  classical
  by_contra hne
  have hpos : 0 < elevenFiveRelativeCount (blockSystem cfg)
      (circleTrace cfg Gamma.1) 1 3 := by omega
  rw [elevenFiveRelativeCount] at hpos
  obtain ⟨P, hP⟩ := Finset.card_pos.mp hpos
  have hspec := Finset.mem_filter.mp hP
  have hPTrace :
      (geometricBlockSupport cfg P ∩ circleTrace cfg Gamma.1).card = 1 :=
    hspec.2.1
  have hPOutside :
      (geometricBlockSupport cfg P \ circleTrace cfg Gamma.1).card = 3 :=
    hspec.2.2
  exact elevenFive_c39_h30_one_trace_three_outsiders_absurd cfg Gamma hpoint hD hhost
    P hPTrace (by omega)

/-- The all-double `H = 30` face has no relative `(1,4)` page. -/
theorem elevenFive_c39_h30_relativeCount_one_four_eq_zero
    {α : Type u} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (Gamma : DeterminedCircle cfg)
    (hpoint : Fintype.card α = 11)
    (hD : (circleTrace cfg Gamma.1).card = 5)
    (hhost : elevenFiveHostWeight (blockSystem cfg)
      (circleTrace cfg Gamma.1) = 30) :
    elevenFiveRelativeCount (blockSystem cfg) (circleTrace cfg Gamma.1) 1 4 = 0 := by
  classical
  by_contra hne
  have hpos : 0 < elevenFiveRelativeCount (blockSystem cfg)
      (circleTrace cfg Gamma.1) 1 4 := by omega
  rw [elevenFiveRelativeCount] at hpos
  obtain ⟨P, hP⟩ := Finset.card_pos.mp hpos
  have hspec := Finset.mem_filter.mp hP
  have hPTrace :
      (geometricBlockSupport cfg P ∩ circleTrace cfg Gamma.1).card = 1 :=
    hspec.2.1
  have hPOutside :
      (geometricBlockSupport cfg P \ circleTrace cfg Gamma.1).card = 4 :=
    hspec.2.2
  exact elevenFive_c39_h30_one_trace_three_outsiders_absurd cfg Gamma hpoint hD hhost
    P hPTrace (by omega)

/-- The C39/L12 numerical rows exclude the all-double host face.  This is
the direct `H = 30` router: K2.1 first removes the `(1,3)` and `(1,4)`
pages, and the remaining size row forces the capped outside-rich weight to
be five. -/
theorem elevenFive_c39_hostWeight_ne_thirty
    {α : Type u} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (hpoint : Fintype.card α = 11)
    (hcap : BlockSizeCap (blockSystem cfg) 5)
    (hglobal : ElevenFiveGlobalRows (blockSystem cfg))
    (hC : (blockSystem cfg).totalCircleCount = 39)
    (hL : elevenFiveLineTotal (blockSystem cfg) = 12)
    (Gamma : DeterminedCircle cfg)
    (hD : (circleTrace cfg Gamma.1).card = 5) :
    elevenFiveHostWeight (blockSystem cfg) (circleTrace cfg Gamma.1) ≠ 30 := by
  classical
  intro hhost
  let S := blockSystem cfg
  let D := circleTrace cfg Gamma.1
  let b : GeometricBlock cfg := Sum.inr Gamma
  have hb : b ∈ S.blocksOfSize 5 := by
    apply S.mem_blocksOfSize.mpr
    simpa [S, b, D, blockSystem, geometricBlockSystem] using hD
  have hDb : S.support b = D := by
    simp [S, b, D, blockSystem, geometricBlockSystem, geometricBlockSupport]
  have h13 : elevenFiveRelativeCount S D 1 3 = 0 := by
    simpa [S, D] using
      elevenFive_c39_h30_relativeCount_one_three_eq_zero cfg Gamma hpoint hD hhost
  have h14 : elevenFiveRelativeCount S D 1 4 = 0 := by
    simpa [S, D] using
      elevenFive_c39_h30_relativeCount_one_four_eq_zero cfg Gamma hpoint hD hhost
  have hweight := elevenFive_c39_relative_size_weight_row S b hb (by
    simpa [S] using hcap)
  have hweightD :
      S.blockCount 4 + 3 * S.blockCount 5 =
        elevenFiveRelativeCount S D 0 4 + elevenFiveRelativeCount S D 1 3 +
          elevenFiveRelativeCount S D 2 2 +
            3 * elevenFiveRelativeCount S D 0 5 +
              3 * elevenFiveRelativeCount S D 1 4 +
                3 * elevenFiveRelativeCount S D 2 3 + 3 := by
    simpa only [hDb] using hweight
  have hhostRow :=
    elevenFiveHostWeight_eq_relativeCount22_add_three_mul_relativeCount23 S D
      (by simpa [S] using hcap)
  have hglobalWeight : S.blockCount 4 + 3 * S.blockCount 5 = 38 := by
    have htriple : S.blockCount 3 + 4 * S.blockCount 4 +
        10 * S.blockCount 5 = 165 := by
      simpa [S] using hglobal.tripleRow
    have htotal : S.blockCount 3 + S.blockCount 4 + S.blockCount 5 =
        39 + 12 := by
      simpa [S, hC, hL] using hglobal.blockTotal
    omega
  have hq :=
    elevenFiveOutsideRichWeight_eq_relativeCount_zero_four_add_three_mul_zero_five S D
  have hqcap : elevenFiveOutsideRichWeight S D ≤ 3 := by
    apply elevenFiveOutsideRichWeight_le_three S D hpoint
    simpa [D] using hD
  have hhost' : elevenFiveHostWeight S D = 30 := by simpa [S, D] using hhost
  omega

end Erdos506.V1
