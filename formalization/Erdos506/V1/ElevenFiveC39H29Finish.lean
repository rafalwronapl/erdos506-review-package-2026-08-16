import Erdos506.V1.ElevenFiveC39H30Finish
import Erdos506.Incidence.FiveConicRootedCyclicMatchingRealization
import Mathlib.Tactic

/-!
# The one-defect `H = 29` entrance of the C39 host router

At host weight twenty-nine, exactly one outsider-pair fibre has one host and
every other fibre has two.  The local all-double K2.1 router already rules
out a one-trace page whose outsider triangle misses that exceptional pair.
Thus every relative `(1,3)` page contains the same actual exceptional pair.

This is deliberately only the lossless finite-to-geometric entrance.  The
remaining one-single/two-double trace law is a separate K2.1 statement: it
must bound the number of pages through this fixed pair, rather than being
encoded here as a new configuration hypothesis.
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

private theorem elevenFive_hostPairFibre_trace_card
    (S : BlockSystem Point Block) (D A : Finset Point) {B : Block}
    (hB : B ∈ elevenFiveHostPairFibre S D A) :
    (S.support B ∩ D).card = 2 := by
  exact (Finset.mem_filter.mp
    ((mem_elevenFiveHostPairFibre S D A).mp hB).1).2

private theorem elevenFive_h29_pair_mem_outside_pairs
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

/-- Two different blocks carrying the same outside pair cannot share a
selected trace label.  Otherwise that label together with the pair is a
three-set owned by both blocks. -/
private theorem elevenFive_common_outside_pair_trace_disjoint
    (S : BlockSystem Point Block) (D A : Finset Point)
    (hAoutside : A ⊆ Finset.univ \ D) (hAcard : A.card = 2)
    {P Q : Block} (hPA : A ⊆ S.support P) (hQA : A ⊆ S.support Q)
    (hPQ : P ≠ Q) :
    Disjoint (S.support P ∩ D) (S.support Q ∩ D) := by
  obtain ⟨u, v, huv, hAeq⟩ := Finset.card_eq_two.mp hAcard
  have huA : u ∈ A := by rw [hAeq]; simp
  have hvA : v ∈ A := by rw [hAeq]; simp
  have huNotD : u ∉ D := (Finset.mem_sdiff.mp (hAoutside huA)).2
  have hvNotD : v ∉ D := (Finset.mem_sdiff.mp (hAoutside hvA)).2
  rw [Finset.disjoint_left]
  intro i hiP hiQ
  have hiPD : i ∈ D := (Finset.mem_inter.mp hiP).2
  have hui : u ≠ i := by
    intro h
    subst i
    exact huNotD hiPD
  have hvi : v ≠ i := by
    intro h
    subst i
    exact hvNotD hiPD
  have hsub : ({u, v, i} : Finset Point) ⊆ S.support P ∩ S.support Q := by
    intro q hq
    simp only [Finset.mem_insert, Finset.mem_singleton] at hq
    rcases hq with rfl | rfl | rfl
    · exact Finset.mem_inter.mpr ⟨hPA huA, hQA huA⟩
    · exact Finset.mem_inter.mpr ⟨hPA hvA, hQA hvA⟩
    · exact Finset.mem_inter.mpr
        ⟨(Finset.mem_inter.mp hiP).1, (Finset.mem_inter.mp hiQ).1⟩
  have hthree : ({u, v, i} : Finset Point).card = 3 := by
    simp [huv, hui, hvi]
  have hinter := S.distinct_block_inter_card_lt_three hPQ
  have hle := Finset.card_le_card hsub
  omega

/-- The literal two-point selected trace of one actual host block, packaged
as a chord of the selected five-set.  This is the sole finite object passed
to the rooted matching realization. -/
private noncomputable def elevenFive_hostTraceChord
    (S : BlockSystem Point Block) (D : Finset Point) (B : Block)
    (hB : B ∈ elevenFiveHostFamily S D) : KFiveChord D :=
  ⟨S.support B ∩ D, Finset.mem_powersetCard.mpr
    ⟨Finset.inter_subset_right, (Finset.mem_filter.mp hB).2⟩⟩

@[simp] private theorem elevenFive_hostTraceChord_val
    (S : BlockSystem Point Block) (D : Finset Point) (B : Block)
    (hB : B ∈ elevenFiveHostFamily S D) :
    (elevenFive_hostTraceChord S D B hB).1 = S.support B ∩ D :=
  rfl

/-- A two-trace host of an outsider edge of a one-trace page cannot contain
the page mark: otherwise the host and page share the marked triple. -/
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

/-- Adjacent outsider edges of one one-trace page cannot have equal host
traces.  Equal trace pairs would create an actual triple collision. -/
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

/-- Two disjoint finite chords avoiding the rooted vertex are one of the
three perfect matchings on the other four vertices. -/
private theorem elevenFive_finFive_matching_row_of_disjoint_avoids_four
    (e f : FinFiveChord) (hef : e ≠ f)
    (hdis : Disjoint e.1 f.1)
    (he4 : (4 : Fin 5) ∉ e.1) (hf4 : (4 : Fin 5) ∉ f.1) :
    ∃ r : Fin 3, ({e, f} : Finset FinFiveChord) = kFiveRowOptions 4 r := by
  apply ExistsUnique.exists
  apply finFive_matchingRow_eq_rowOption
  · simp [hef]
  · intro a ha b hb hab
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · exact False.elim (hab rfl)
    · exact hdis
    · exact hdis.symm
    · exact False.elim (hab rfl)
  · intro a ha
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl
    · exact he4
    · exact hf4
  · let U : Finset (Fin 5) := e.1 ∪ f.1
    have hecard : e.1.card = 2 := (Finset.mem_powersetCard.mp e.2).2
    have hfcard : f.1.card = 2 := (Finset.mem_powersetCard.mp f.2).2
    have hUcard : U.card = 4 := by
      rw [Finset.card_union_of_disjoint hdis, hecard, hfcard]
    have hUsub : U ⊆ Finset.univ.erase 4 := by
      intro q hq
      apply Finset.mem_erase.mpr
      refine ⟨?_, Finset.mem_univ q⟩
      intro hq4
      subst q
      rcases Finset.mem_union.mp hq with h | h
      · exact he4 h
      · exact hf4 h
    have htargetCard : (Finset.univ.erase (4 : Fin 5)).card = 4 := by
      simp
    have hUeq : U = Finset.univ.erase 4 := by
      apply Finset.eq_of_subset_of_card_le hUsub
      rw [hUcard, htargetCard]
    intro q hq
    have hqU : q ∈ U := by
      rw [hUeq]
      simp [hq]
    rcases Finset.mem_union.mp hqU with hqe | hqf
    · exact ⟨e, by simp, hqe⟩
    · exact ⟨f, by simp, hqf⟩

/-- Pulling two actual disjoint trace chords back through a rooted cyclic
labelling preserves their matching row. -/
private theorem elevenFive_rooted_chords_form_row
    {α : Type u} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (Gamma : DeterminedCircle cfg)
    (hD : (circleTrace cfg Gamma.1).card = 5) (r : Fin 5)
    (e f : KFiveChord (circleTrace cfg Gamma.1))
    (hef : e ≠ f) (hdis : Disjoint e.1 f.1)
    (he4 : (fiveConicRootedCyclicLabel cfg Gamma hD r 4).1 ∉ e.1)
    (hf4 : (fiveConicRootedCyclicLabel cfg Gamma hD r 4).1 ∉ f.1) :
    ∃ j : Fin 3,
      ({fiveConicRootedCyclicChordIndex cfg Gamma hD r e,
          fiveConicRootedCyclicChordIndex cfg Gamma hD r f} :
        Finset FinFiveChord) = kFiveRowOptions 4 j := by
  let E := kFiveChordEquivOfVertexLabel
    (fiveConicRootedCyclicLabel cfg Gamma hD r)
  let e' : FinFiveChord := fiveConicRootedCyclicChordIndex cfg Gamma hD r e
  let f' : FinFiveChord := fiveConicRootedCyclicChordIndex cfg Gamma hD r f
  have hef' : e' ≠ f' := by
    intro h
    apply hef
    apply E.symm.injective
    simpa [E, e', f', fiveConicRootedCyclicChordIndex] using h
  have hdis' : Disjoint e'.1 f'.1 := by
    rw [Finset.disjoint_left]
    intro q hqe hqf
    apply (Finset.disjoint_left.mp hdis)
    · have hmem := (mem_kFiveChordEquivOfVertexLabel
          (fiveConicRootedCyclicLabel cfg Gamma hD r) e' q).mpr hqe
      simpa [E, e', fiveConicRootedCyclicChordIndex] using hmem
    · have hmem := (mem_kFiveChordEquivOfVertexLabel
          (fiveConicRootedCyclicLabel cfg Gamma hD r) f' q).mpr hqf
      simpa [E, f', fiveConicRootedCyclicChordIndex] using hmem
  have he4' : (4 : Fin 5) ∉ e'.1 := by
    intro hfour
    apply he4
    have hmem := (mem_kFiveChordEquivOfVertexLabel
      (fiveConicRootedCyclicLabel cfg Gamma hD r) e' 4).mpr hfour
    simpa [E, e', fiveConicRootedCyclicChordIndex] using hmem
  have hf4' : (4 : Fin 5) ∉ f'.1 := by
    intro hfour
    apply hf4
    have hmem := (mem_kFiveChordEquivOfVertexLabel
      (fiveConicRootedCyclicLabel cfg Gamma hD r) f' 4).mpr hfour
    simpa [E, f', fiveConicRootedCyclicChordIndex] using hmem
  simpa [e', f'] using
    elevenFive_finFive_matching_row_of_disjoint_avoids_four
      e' f' hef' hdis' he4' hf4'

/-- The two selected trace chords of an actual double fibre meet on the
selected/page axis when the page is a proper circle. -/
private theorem elevenFive_double_fibre_chords_on_circlePage_axis
    {α : Type u} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (Gamma K : DeterminedCircle cfg)
    (hGammaK : Gamma.1 ≠ K.1) {x y : α}
    (hxNotGamma : x ∉ circleTrace cfg Gamma.1)
    (hyNotGamma : y ∉ circleTrace cfg Gamma.1)
    (hxK : x ∈ circleTrace cfg K.1) (hyK : y ∈ circleTrace cfg K.1)
    (hxy : x ≠ y) (B E : GeometricBlock cfg)
    (hB : B ∈ elevenFiveHostPairFibre (blockSystem cfg)
      (circleTrace cfg Gamma.1) {x, y})
    (hE : E ∈ elevenFiveHostPairFibre (blockSystem cfg)
      (circleTrace cfg Gamma.1) {x, y})
    (hBE : B ≠ E)
    (hBoff : ∀ q ∈ geometricBlockSupport cfg B ∩ circleTrace cfg Gamma.1,
      q ∉ circleTrace cfg K.1)
    (hEoff : ∀ q ∈ geometricBlockSupport cfg E ∩ circleTrace cfg Gamma.1,
      q ∉ circleTrace cfg K.1) :
    Projectivization.orthogonal
      (Projectivization.cross
        (projectiveChordLine cfg
          (circleChordPair (elevenFive_hostTraceChord (blockSystem cfg)
            (circleTrace cfg Gamma.1) B
            ((mem_elevenFiveHostPairFibre (blockSystem cfg)
              (circleTrace cfg Gamma.1) {x, y}).mp hB).1)))
        (projectiveChordLine cfg
          (circleChordPair (elevenFive_hostTraceChord (blockSystem cfg)
            (circleTrace cfg Gamma.1) E
            ((mem_elevenFiveHostPairFibre (blockSystem cfg)
              (circleTrace cfg Gamma.1) {x, y}).mp hE).1))))
      (projectiveRadicalAxis Gamma.1 K.1 hGammaK) := by
  classical
  let S := blockSystem cfg
  let D := circleTrace cfg Gamma.1
  have hBdata := (mem_elevenFiveHostPairFibre S D {x, y}).mp hB
  have hEdata := (mem_elevenFiveHostPairFibre S D {x, y}).mp hE
  have hBtrace := elevenFive_hostPairFibre_trace_card S D {x, y} hB
  have hEtrace := elevenFive_hostPairFibre_trace_card S D {x, y} hE
  obtain ⟨a, b, hab, hBab⟩ := Finset.card_eq_two.mp hBtrace
  obtain ⟨c, d, hcd, hEcd⟩ := Finset.card_eq_two.mp hEtrace
  have haBD : a ∈ S.support B ∩ D := by rw [hBab]; simp
  have hbBD : b ∈ S.support B ∩ D := by rw [hBab]; simp
  have hcED : c ∈ S.support E ∩ D := by rw [hEcd]; simp
  have hdED : d ∈ S.support E ∩ D := by rw [hEcd]; simp
  have hlineB :
      projectiveChordLine cfg
          (circleChordPair (elevenFive_hostTraceChord S D B hBdata.1)) =
        projectiveLine (cfg a) (cfg b) (cfg.injective.ne hab) := by
    apply projectiveChordLine_eq_projectiveLine_of_mem cfg
    · simpa [circleChordPair, elevenFive_hostTraceChord] using haBD
    · simpa [circleChordPair, elevenFive_hostTraceChord] using hbBD
    · exact hab
  have hlineE :
      projectiveChordLine cfg
          (circleChordPair (elevenFive_hostTraceChord S D E hEdata.1)) =
        projectiveLine (cfg c) (cfg d) (cfg.injective.ne hcd) := by
    apply projectiveChordLine_eq_projectiveLine_of_mem cfg
    · simpa [circleChordPair, elevenFive_hostTraceChord] using hcED
    · simpa [circleChordPair, elevenFive_hostTraceChord] using hdED
    · exact hcd
  rw [hlineB, hlineE]
  apply elevenFive_mixedHostPair_direction_on_circlePage_axis
    cfg Gamma K hGammaK
    (a := a) (b := b) (c := c) (d := d) (x := x) (y := y)
    (B := B) (E := E)
  · simpa [D] using (Finset.mem_inter.mp haBD).2
  · simpa [D] using (Finset.mem_inter.mp hbBD).2
  · simpa [D] using (Finset.mem_inter.mp hcED).2
  · simpa [D] using (Finset.mem_inter.mp hdED).2
  · exact hBoff a (by simpa [S, D, blockSystem, geometricBlockSystem] using haBD)
  · exact hEoff c (by simpa [S, D, blockSystem, geometricBlockSystem] using hcED)
  · exact hxNotGamma
  · exact hyNotGamma
  · exact hxK
  · exact hyK
  · exact hab
  · exact hcd
  · exact hxy
  · simpa [S, D] using hB
  · simpa [S, D] using hE
  · exact hBE
  · simpa [S, blockSystem, geometricBlockSystem] using (Finset.mem_inter.mp haBD).1
  · simpa [S, blockSystem, geometricBlockSystem] using (Finset.mem_inter.mp hbBD).1
  · simpa [S, blockSystem, geometricBlockSystem] using hBdata.2 (by simp)
  · simpa [S, blockSystem, geometricBlockSystem] using hBdata.2 (by simp)
  · simpa [S, blockSystem, geometricBlockSystem] using (Finset.mem_inter.mp hcED).1
  · simpa [S, blockSystem, geometricBlockSystem] using (Finset.mem_inter.mp hdED).1
  · simpa [S, blockSystem, geometricBlockSystem] using hEdata.2 (by simp)
  · simpa [S, blockSystem, geometricBlockSystem] using hEdata.2 (by simp)

/-- The same double-fibre chord statement for a determined-line page. -/
private theorem elevenFive_double_fibre_chords_on_linePage_axis
    {α : Type u} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (Gamma : DeterminedCircle cfg)
    (K : DeterminedLine cfg) {x y : α}
    (hxNotGamma : x ∉ circleTrace cfg Gamma.1)
    (hyNotGamma : y ∉ circleTrace cfg Gamma.1)
    (hxK : x ∈ lineSupport cfg K) (hyK : y ∈ lineSupport cfg K)
    (hxy : x ≠ y) (B E : GeometricBlock cfg)
    (hB : B ∈ elevenFiveHostPairFibre (blockSystem cfg)
      (circleTrace cfg Gamma.1) {x, y})
    (hE : E ∈ elevenFiveHostPairFibre (blockSystem cfg)
      (circleTrace cfg Gamma.1) {x, y})
    (hBE : B ≠ E)
    (hBoff : ∀ q ∈ geometricBlockSupport cfg B ∩ circleTrace cfg Gamma.1,
      q ∉ lineSupport cfg K)
    (hEoff : ∀ q ∈ geometricBlockSupport cfg E ∩ circleTrace cfg Gamma.1,
      q ∉ lineSupport cfg K) :
    Projectivization.orthogonal
      (Projectivization.cross
        (projectiveChordLine cfg
          (circleChordPair (elevenFive_hostTraceChord (blockSystem cfg)
            (circleTrace cfg Gamma.1) B
            ((mem_elevenFiveHostPairFibre (blockSystem cfg)
              (circleTrace cfg Gamma.1) {x, y}).mp hB).1)))
        (projectiveChordLine cfg
          (circleChordPair (elevenFive_hostTraceChord (blockSystem cfg)
            (circleTrace cfg Gamma.1) E
            ((mem_elevenFiveHostPairFibre (blockSystem cfg)
              (circleTrace cfg Gamma.1) {x, y}).mp hE).1))))
      (determinedProjectiveLine cfg K) := by
  classical
  let S := blockSystem cfg
  let D := circleTrace cfg Gamma.1
  have hBdata := (mem_elevenFiveHostPairFibre S D {x, y}).mp hB
  have hEdata := (mem_elevenFiveHostPairFibre S D {x, y}).mp hE
  have hBtrace := elevenFive_hostPairFibre_trace_card S D {x, y} hB
  have hEtrace := elevenFive_hostPairFibre_trace_card S D {x, y} hE
  obtain ⟨a, b, hab, hBab⟩ := Finset.card_eq_two.mp hBtrace
  obtain ⟨c, d, hcd, hEcd⟩ := Finset.card_eq_two.mp hEtrace
  have haBD : a ∈ S.support B ∩ D := by rw [hBab]; simp
  have hbBD : b ∈ S.support B ∩ D := by rw [hBab]; simp
  have hcED : c ∈ S.support E ∩ D := by rw [hEcd]; simp
  have hdED : d ∈ S.support E ∩ D := by rw [hEcd]; simp
  have hlineB :
      projectiveChordLine cfg
          (circleChordPair (elevenFive_hostTraceChord S D B hBdata.1)) =
        projectiveLine (cfg a) (cfg b) (cfg.injective.ne hab) := by
    apply projectiveChordLine_eq_projectiveLine_of_mem cfg
    · simpa [circleChordPair, elevenFive_hostTraceChord] using haBD
    · simpa [circleChordPair, elevenFive_hostTraceChord] using hbBD
    · exact hab
  have hlineE :
      projectiveChordLine cfg
          (circleChordPair (elevenFive_hostTraceChord S D E hEdata.1)) =
        projectiveLine (cfg c) (cfg d) (cfg.injective.ne hcd) := by
    apply projectiveChordLine_eq_projectiveLine_of_mem cfg
    · simpa [circleChordPair, elevenFive_hostTraceChord] using hcED
    · simpa [circleChordPair, elevenFive_hostTraceChord] using hdED
    · exact hcd
  rw [hlineB, hlineE]
  apply elevenFive_mixedHostPair_direction_on_linePage_axis
    cfg Gamma K
    (a := a) (b := b) (c := c) (d := d) (x := x) (y := y)
    (B := B) (E := E)
  · simpa [D] using (Finset.mem_inter.mp haBD).2
  · simpa [D] using (Finset.mem_inter.mp hbBD).2
  · simpa [D] using (Finset.mem_inter.mp hcED).2
  · simpa [D] using (Finset.mem_inter.mp hdED).2
  · exact hBoff a (by simpa [S, D, blockSystem, geometricBlockSystem] using haBD)
  · exact hEoff c (by simpa [S, D, blockSystem, geometricBlockSystem] using hcED)
  · exact hxNotGamma
  · exact hyNotGamma
  · exact hxK
  · exact hyK
  · exact hab
  · exact hcd
  · exact hxy
  · simpa [S, D] using hB
  · simpa [S, D] using hE
  · exact hBE
  · simpa [S, blockSystem, geometricBlockSystem] using (Finset.mem_inter.mp haBD).1
  · simpa [S, blockSystem, geometricBlockSystem] using (Finset.mem_inter.mp hbBD).1
  · simpa [S, blockSystem, geometricBlockSystem] using hBdata.2 (by simp)
  · simpa [S, blockSystem, geometricBlockSystem] using hBdata.2 (by simp)
  · simpa [S, blockSystem, geometricBlockSystem] using (Finset.mem_inter.mp hcED).1
  · simpa [S, blockSystem, geometricBlockSystem] using (Finset.mem_inter.mp hdED).1
  · simpa [S, blockSystem, geometricBlockSystem] using hEdata.2 (by simp)
  · simpa [S, blockSystem, geometricBlockSystem] using hEdata.2 (by simp)

/-- A fixed one-host outsider pair supports at most one one-trace,
three-outsider page once the other two outsider edges of each page are
double-hosted.  This local form is independent of the global `H = 29`
profile and is also reusable at lower host weights. -/
theorem elevenFive_one_single_two_double_pages_eq
    {α : Type u} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (Gamma : DeterminedCircle cfg)
    (hD : (circleTrace cfg Gamma.1).card = 5)
    (A : Finset α)
    (hA : A ∈ (Finset.univ \ circleTrace cfg Gamma.1).powersetCard 2)
    (hAone : (elevenFiveHostPairFibre (blockSystem cfg)
      (circleTrace cfg Gamma.1) A).card = 1)
    {P Q : GeometricBlock cfg}
    (hPtrace : (geometricBlockSupport cfg P ∩
      circleTrace cfg Gamma.1).card = 1)
    (hPoutside : (geometricBlockSupport cfg P \
      circleTrace cfg Gamma.1).card = 3)
    (hPA : A ⊆ geometricBlockSupport cfg P)
    (hPdouble : ∀ E ∈ (geometricBlockSupport cfg P \
        circleTrace cfg Gamma.1).powersetCard 2, E ≠ A →
      (elevenFiveHostPairFibre (blockSystem cfg)
        (circleTrace cfg Gamma.1) E).card = 2)
    (hQtrace : (geometricBlockSupport cfg Q ∩
      circleTrace cfg Gamma.1).card = 1)
    (hQoutside : (geometricBlockSupport cfg Q \
      circleTrace cfg Gamma.1).card = 3)
    (hQA : A ⊆ geometricBlockSupport cfg Q)
    (hQdouble : ∀ E ∈ (geometricBlockSupport cfg Q \
        circleTrace cfg Gamma.1).powersetCard 2, E ≠ A →
      (elevenFiveHostPairFibre (blockSystem cfg)
        (circleTrace cfg Gamma.1) E).card = 2) :
    P = Q := by
  classical
  let S := blockSystem cfg
  let D := circleTrace cfg Gamma.1
  have hAoutside : A ⊆ Finset.univ \ D := by
    simpa [D] using (Finset.mem_powersetCard.mp hA).1
  have hAcard : A.card = 2 := (Finset.mem_powersetCard.mp hA).2
  obtain ⟨x, y, hxy, hAeq⟩ := Finset.card_eq_two.mp hAcard
  have hxA : x ∈ A := by rw [hAeq]; simp
  have hyA : y ∈ A := by rw [hAeq]; simp
  have hxNotD : x ∉ D := (Finset.mem_sdiff.mp (hAoutside hxA)).2
  have hyNotD : y ∉ D := (Finset.mem_sdiff.mp (hAoutside hyA)).2
  have hAone' : (elevenFiveHostPairFibre S D A).card = 1 := by
    simpa [S, D] using hAone
  have hB0pos : 0 < (elevenFiveHostPairFibre S D A).card := by omega
  obtain ⟨B0, hB0⟩ := Finset.card_pos.mp hB0pos
  have hB0data := (mem_elevenFiveHostPairFibre S D A).mp hB0
  let e0 : KFiveChord D := elevenFive_hostTraceChord S D B0 hB0data.1
  have hpageFactor
      (R : GeometricBlock cfg)
      (hRtrace : (geometricBlockSupport cfg R ∩
        circleTrace cfg Gamma.1).card = 1)
      (hRoutside : (geometricBlockSupport cfg R \
        circleTrace cfg Gamma.1).card = 3)
      (hRA : A ⊆ geometricBlockSupport cfg R)
      (hRdouble : ∀ E ∈ (geometricBlockSupport cfg R \
          circleTrace cfg Gamma.1).powersetCard 2, E ≠ A →
        (elevenFiveHostPairFibre (blockSystem cfg)
          (circleTrace cfg Gamma.1) E).card = 2) :
      ∃ (i : α) (r : Fin 5),
        S.support R ∩ D = {i} ∧
        (fiveConicRootedCyclicLabel cfg Gamma hD r 4).1 = i ∧
        e0 ∈ fiveConicCyclicChordFactor cfg Gamma hD r := by
    have hRtraceS : (S.support R ∩ D).card = 1 := by
      simpa [S, D, blockSystem, geometricBlockSystem,
        geometricBlockSupport] using hRtrace
    have hRoutsideS : (S.support R \ D).card = 3 := by
      simpa [S, D, blockSystem, geometricBlockSystem,
        geometricBlockSupport] using hRoutside
    have hRAS : A ⊆ S.support R := by
      simpa [S, blockSystem, geometricBlockSystem,
        geometricBlockSupport] using hRA
    have hRdoubleS : ∀ E ∈ (S.support R \ D).powersetCard 2, E ≠ A →
        (elevenFiveHostPairFibre S D E).card = 2 := by
      intro E hE hEA
      simpa [S, D] using hRdouble E (by
        simpa [S, D, blockSystem, geometricBlockSystem,
          geometricBlockSupport] using hE) hEA
    obtain ⟨i, hiEq⟩ := Finset.card_eq_one.mp hRtraceS
    have hiRD : i ∈ S.support R ∩ D := by rw [hiEq]; simp
    have hiR : i ∈ S.support R := (Finset.mem_inter.mp hiRD).1
    have hiD : i ∈ D := (Finset.mem_inter.mp hiRD).2
    let U : Finset α := S.support R \ D
    have hUcard : U.card = 3 := by simpa [U] using hRoutsideS
    have hAsubU : A ⊆ U := by
      intro q hq
      exact Finset.mem_sdiff.mpr
        ⟨hRAS hq, (Finset.mem_sdiff.mp (hAoutside hq)).2⟩
    have hdiffCard : (U \ A).card = 1 := by
      rw [Finset.card_sdiff_of_subset hAsubU, hUcard, hAcard]
    have hdiffPos : 0 < (U \ A).card := by omega
    obtain ⟨z, hz⟩ := Finset.card_pos.mp hdiffPos
    have hzU : z ∈ U := (Finset.mem_sdiff.mp hz).1
    have hzNotA : z ∉ A := (Finset.mem_sdiff.mp hz).2
    have hxU : x ∈ U := hAsubU hxA
    have hyU : y ∈ U := hAsubU hyA
    have hxR : x ∈ S.support R := (Finset.mem_sdiff.mp hxU).1
    have hyR : y ∈ S.support R := (Finset.mem_sdiff.mp hyU).1
    have hzR : z ∈ S.support R := (Finset.mem_sdiff.mp hzU).1
    have hzNotD : z ∉ D := (Finset.mem_sdiff.mp hzU).2
    have hxz : x ≠ z := by
      intro h
      subst z
      exact hzNotA hxA
    have hyz : y ≠ z := by
      intro h
      subst z
      exact hzNotA hyA
    have hAxzNe : ({x, z} : Finset α) ≠ A := by
      intro hEq
      have hyPair : y ∈ ({x, z} : Finset α) := by rw [hEq]; exact hyA
      simp only [Finset.mem_insert, Finset.mem_singleton] at hyPair
      rcases hyPair with hyx | hyz'
      · exact hxy hyx.symm
      · exact hyz hyz'
    have hAyzNe : ({y, z} : Finset α) ≠ A := by
      intro hEq
      have hxPair : x ∈ ({y, z} : Finset α) := by rw [hEq]; exact hxA
      simp only [Finset.mem_insert, Finset.mem_singleton] at hxPair
      rcases hxPair with hxy' | hxz'
      · exact hxy hxy'
      · exact hxz hxz'
    have hAxzU : ({x, z} : Finset α) ∈ U.powersetCard 2 := by
      apply Finset.mem_powersetCard.mpr
      refine ⟨?_, by simp [hxz]⟩
      intro q hq
      simp only [Finset.mem_insert, Finset.mem_singleton] at hq
      rcases hq with rfl | rfl
      · exact hxU
      · exact hzU
    have hAyzU : ({y, z} : Finset α) ∈ U.powersetCard 2 := by
      apply Finset.mem_powersetCard.mpr
      refine ⟨?_, by simp [hyz]⟩
      intro q hq
      simp only [Finset.mem_insert, Finset.mem_singleton] at hq
      rcases hq with rfl | rfl
      · exact hyU
      · exact hzU
    have hcardXZ : (elevenFiveHostPairFibre S D {x, z}).card = 2 :=
      hRdoubleS {x, z} (by simpa [U] using hAxzU) hAxzNe
    have hcardYZ : (elevenFiveHostPairFibre S D {y, z}).card = 2 :=
      hRdoubleS {y, z} (by simpa [U] using hAyzU) hAyzNe
    obtain ⟨Bx, Ex, hBx, hEx, hBxE⟩ :=
      elevenFiveHostPairFibre_exists_two_distinct_of_card_eq_two
        S D {x, z} hcardXZ
    obtain ⟨By, Ey, hBy, hEy, hByE⟩ :=
      elevenFiveHostPairFibre_exists_two_distinct_of_card_eq_two
        S D {y, z} hcardYZ
    have hBxdata := (mem_elevenFiveHostPairFibre S D {x, z}).mp hBx
    have hExdata := (mem_elevenFiveHostPairFibre S D {x, z}).mp hEx
    have hBydata := (mem_elevenFiveHostPairFibre S D {y, z}).mp hBy
    have hEydata := (mem_elevenFiveHostPairFibre S D {y, z}).mp hEy
    have hB0trace := elevenFive_hostPairFibre_trace_card S D A hB0
    have hBxtrace := elevenFive_hostPairFibre_trace_card S D {x, z} hBx
    have hExtrace := elevenFive_hostPairFibre_trace_card S D {x, z} hEx
    have hBytrace := elevenFive_hostPairFibre_trace_card S D {y, z} hBy
    have hEytrace := elevenFive_hostPairFibre_trace_card S D {y, z} hEy
    have hiB0 : i ∉ S.support B0 :=
      elevenFive_host_avoids_page_mark S D R B0 hRtraceS hiR hiD
        hxR hyR hxNotD hyNotD hxy hB0trace
        (hB0data.2 hxA) (hB0data.2 hyA)
    have hiBx : i ∉ S.support Bx :=
      elevenFive_host_avoids_page_mark S D R Bx hRtraceS hiR hiD
        hxR hzR hxNotD hzNotD hxz hBxtrace
        (hBxdata.2 (by simp)) (hBxdata.2 (by simp))
    have hiEx : i ∉ S.support Ex :=
      elevenFive_host_avoids_page_mark S D R Ex hRtraceS hiR hiD
        hxR hzR hxNotD hzNotD hxz hExtrace
        (hExdata.2 (by simp)) (hExdata.2 (by simp))
    have hiBy : i ∉ S.support By :=
      elevenFive_host_avoids_page_mark S D R By hRtraceS hiR hiD
        hyR hzR hyNotD hzNotD hyz hBytrace
        (hBydata.2 (by simp)) (hBydata.2 (by simp))
    have hiEy : i ∉ S.support Ey :=
      elevenFive_host_avoids_page_mark S D R Ey hRtraceS hiR hiD
        hyR hzR hyNotD hzNotD hyz hEytrace
        (hEydata.2 (by simp)) (hEydata.2 (by simp))
    let ex : KFiveChord D := elevenFive_hostTraceChord S D Bx hBxdata.1
    let fx : KFiveChord D := elevenFive_hostTraceChord S D Ex hExdata.1
    let ey : KFiveChord D := elevenFive_hostTraceChord S D By hBydata.1
    let fy : KFiveChord D := elevenFive_hostTraceChord S D Ey hEydata.1
    have hAxzOutside : ({x, z} : Finset α) ∈
        (Finset.univ \ D).powersetCard 2 :=
      elevenFive_h29_pair_mem_outside_pairs D hxNotD hzNotD hxz
    have hAyzOutside : ({y, z} : Finset α) ∈
        (Finset.univ \ D).powersetCard 2 :=
      elevenFive_h29_pair_mem_outside_pairs D hyNotD hzNotD hyz
    have hdisX := elevenFiveHostPairFibre_trace_disjoint S D {x, z}
      hAxzOutside hBx hEx hBxE
    have hdisY := elevenFiveHostPairFibre_trace_disjoint S D {y, z}
      hAyzOutside hBy hEy hByE
    have hdisX' : Disjoint ex.1 fx.1 := by
      simpa [ex, fx, elevenFive_hostTraceChord] using hdisX
    have hdisY' : Disjoint ey.1 fy.1 := by
      simpa [ey, fy, elevenFive_hostTraceChord] using hdisY
    have hexne : ex ≠ fx := by
      intro hEq
      have htraceEq : S.support Bx ∩ D = S.support Ex ∩ D := by
        simpa [ex, fx, elevenFive_hostTraceChord] using
          congrArg Subtype.val hEq
      have hself := hdisX
      rw [htraceEq] at hself
      have hempty := disjoint_self.mp hself
      rw [hempty] at hExtrace
      simp at hExtrace
    have heyne : ey ≠ fy := by
      intro hEq
      have htraceEq : S.support By ∩ D = S.support Ey ∩ D := by
        simpa [ey, fy, elevenFive_hostTraceChord] using
          congrArg Subtype.val hEq
      have hself := hdisY
      rw [htraceEq] at hself
      have hempty := disjoint_self.mp hself
      rw [hempty] at hEytrace
      simp at hEytrace
    let ri : Fin 5 := (fiveConicCyclicLabel cfg Gamma hD).symm
      ⟨i, by simpa [D] using hiD⟩
    have hroot : (fiveConicRootedCyclicLabel cfg Gamma hD ri 4).1 = i := by
      simp [ri]
    have hrootEx : (fiveConicRootedCyclicLabel cfg Gamma hD ri 4).1 ∉ ex.1 := by
      rw [hroot]
      intro hi
      apply hiBx
      exact (Finset.mem_inter.mp (by
        simpa [ex, elevenFive_hostTraceChord] using hi)).1
    have hrootFx : (fiveConicRootedCyclicLabel cfg Gamma hD ri 4).1 ∉ fx.1 := by
      rw [hroot]
      intro hi
      apply hiEx
      exact (Finset.mem_inter.mp (by
        simpa [fx, elevenFive_hostTraceChord] using hi)).1
    have hrootEy : (fiveConicRootedCyclicLabel cfg Gamma hD ri 4).1 ∉ ey.1 := by
      rw [hroot]
      intro hi
      apply hiBy
      exact (Finset.mem_inter.mp (by
        simpa [ey, elevenFive_hostTraceChord] using hi)).1
    have hrootFy : (fiveConicRootedCyclicLabel cfg Gamma hD ri 4).1 ∉ fy.1 := by
      rw [hroot]
      intro hi
      apply hiEy
      exact (Finset.mem_inter.mp (by
        simpa [fy, elevenFive_hostTraceChord] using hi)).1
    obtain ⟨rx, hrowX⟩ := elevenFive_rooted_chords_form_row
      cfg Gamma hD ri ex fx hexne hdisX' hrootEx hrootFx
    obtain ⟨ry, hrowY⟩ := elevenFive_rooted_chords_form_row
      cfg Gamma hD ri ey fy heyne hdisY' hrootEy hrootFy
    let e0i := fiveConicRootedCyclicChordIndex cfg Gamma hD ri e0
    let exi := fiveConicRootedCyclicChordIndex cfg Gamma hD ri ex
    let fxi := fiveConicRootedCyclicChordIndex cfg Gamma hD ri fx
    let eyi := fiveConicRootedCyclicChordIndex cfg Gamma hD ri ey
    let fyi := fiveConicRootedCyclicChordIndex cfg Gamma hD ri fy
    have hindexInjective : Function.Injective
        (fiveConicRootedCyclicChordIndex cfg Gamma hD ri) := by
      simpa [fiveConicRootedCyclicChordIndex] using
        (kFiveChordEquivOfVertexLabel
          (fiveConicRootedCyclicLabel cfg Gamma hD ri)).symm.injective
    have htrace0X (C : GeometricBlock cfg)
        (hC : C ∈ elevenFiveHostPairFibre S D {x, z}) :
        S.support B0 ∩ D ≠ S.support C ∩ D := by
      apply elevenFive_adjacent_host_traces_ne S D R B0 C hRtraceS
        hxR hyR hzR hxNotD hyNotD hzNotD hxy hxz hyz
      · exact hB0trace
      · exact elevenFive_hostPairFibre_trace_card S D {x, z} hC
      · exact hB0data.2 hxA
      · exact hB0data.2 hyA
      · exact ((mem_elevenFiveHostPairFibre S D {x, z}).mp hC).2 (by simp)
      · exact ((mem_elevenFiveHostPairFibre S D {x, z}).mp hC).2 (by simp)
    have htrace0Y (C : GeometricBlock cfg)
        (hC : C ∈ elevenFiveHostPairFibre S D {y, z}) :
        S.support B0 ∩ D ≠ S.support C ∩ D := by
      apply elevenFive_adjacent_host_traces_ne S D R B0 C hRtraceS
        hyR hxR hzR hyNotD hxNotD hzNotD hxy.symm hyz hxz
      · exact hB0trace
      · exact elevenFive_hostPairFibre_trace_card S D {y, z} hC
      · exact hB0data.2 hyA
      · exact hB0data.2 hxA
      · exact ((mem_elevenFiveHostPairFibre S D {y, z}).mp hC).2 (by simp)
      · exact ((mem_elevenFiveHostPairFibre S D {y, z}).mp hC).2 (by simp)
    have htraceXY (C F : GeometricBlock cfg)
        (hC : C ∈ elevenFiveHostPairFibre S D {x, z})
        (hF : F ∈ elevenFiveHostPairFibre S D {y, z}) :
        S.support C ∩ D ≠ S.support F ∩ D := by
      apply elevenFive_adjacent_host_traces_ne S D R C F hRtraceS
        hzR hxR hyR hzNotD hxNotD hyNotD hxz.symm hyz.symm hxy
      · exact elevenFive_hostPairFibre_trace_card S D {x, z} hC
      · exact elevenFive_hostPairFibre_trace_card S D {y, z} hF
      · exact ((mem_elevenFiveHostPairFibre S D {x, z}).mp hC).2 (by simp)
      · exact ((mem_elevenFiveHostPairFibre S D {x, z}).mp hC).2 (by simp)
      · exact ((mem_elevenFiveHostPairFibre S D {y, z}).mp hF).2 (by simp)
      · exact ((mem_elevenFiveHostPairFibre S D {y, z}).mp hF).2 (by simp)
    have he0ex : e0 ≠ ex := by
      intro hEq
      apply htrace0X Bx hBx
      simpa [e0, ex, elevenFive_hostTraceChord] using
        congrArg Subtype.val hEq
    have he0fx : e0 ≠ fx := by
      intro hEq
      apply htrace0X Ex hEx
      simpa [e0, fx, elevenFive_hostTraceChord] using
        congrArg Subtype.val hEq
    have he0ey : e0 ≠ ey := by
      intro hEq
      apply htrace0Y By hBy
      simpa [e0, ey, elevenFive_hostTraceChord] using
        congrArg Subtype.val hEq
    have he0fy : e0 ≠ fy := by
      intro hEq
      apply htrace0Y Ey hEy
      simpa [e0, fy, elevenFive_hostTraceChord] using
        congrArg Subtype.val hEq
    have hexey : ex ≠ ey := by
      intro hEq
      apply htraceXY Bx By hBx hBy
      simpa [ex, ey, elevenFive_hostTraceChord] using
        congrArg Subtype.val hEq
    have hexfy : ex ≠ fy := by
      intro hEq
      apply htraceXY Bx Ey hBx hEy
      simpa [ex, fy, elevenFive_hostTraceChord] using
        congrArg Subtype.val hEq
    have he0iex : e0i ≠ exi := hindexInjective.ne he0ex
    have he0ifx : e0i ≠ fxi := hindexInjective.ne he0fx
    have he0iey : e0i ≠ eyi := hindexInjective.ne he0ey
    have he0ify : e0i ≠ fyi := hindexInjective.ne he0fy
    have hexiey : exi ≠ eyi := hindexInjective.ne hexey
    have hexify : exi ≠ fyi := hindexInjective.ne hexfy
    have hnotX : e0i ∉ kFiveRowOptions 4 rx := by
      rw [← hrowX]
      simp only [Finset.mem_insert, Finset.mem_singleton]
      intro h
      rcases h with h | h
      · exact he0iex h
      · exact he0ifx h
    have hnotY : e0i ∉ kFiveRowOptions 4 ry := by
      rw [← hrowY]
      simp only [Finset.mem_insert, Finset.mem_singleton]
      intro h
      rcases h with h | h
      · exact he0iey h
      · exact he0ify h
    have hrxy : rx ≠ ry := by
      intro hEq
      have hexRow : exi ∈ kFiveRowOptions 4 rx := by
        rw [← hrowX]
        exact Finset.mem_insert_self _ _
      have hexRow' : exi ∈ kFiveRowOptions 4 ry := by simpa [hEq] using hexRow
      rw [← hrowY] at hexRow'
      simp only [Finset.mem_insert, Finset.mem_singleton] at hexRow'
      rcases hexRow' with h | h
      · exact hexiey h
      · exact hexify h
    have hhostOff (C : GeometricBlock cfg) (hiC : i ∉ S.support C) :
        ∀ q ∈ S.support C ∩ D, q ∉ S.support R := by
      intro q hq hqR
      have hqRD : q ∈ S.support R ∩ D :=
        Finset.mem_inter.mpr ⟨hqR, (Finset.mem_inter.mp hq).2⟩
      rw [hiEq] at hqRD
      have hqi : q = i := by simpa using hqRD
      subst q
      exact hiC (Finset.mem_inter.mp hq).1
    have hrootLine (e : KFiveChord D) :
        fiveConicRootedCyclicProjectiveChord cfg Gamma hD ri
            (fiveConicRootedCyclicChordIndex cfg Gamma hD ri e) =
          projectiveChordLine cfg (circleChordPair e) := by
      simp [fiveConicRootedCyclicProjectiveChord,
        fiveConicRootedCyclicChordIndex]
    have hrows : (rx = 0 ∧ ry = 1) ∨ (rx = 1 ∧ ry = 0) := by
      rcases R with L | K
      · have hiL : i ∈ lineSupport cfg L := by
          simpa [S, blockSystem, geometricBlockSystem,
            geometricBlockSupport] using hiR
        have hmark : Projectivization.orthogonal
            (projectivePoint
              (cfg (fiveConicRootedCyclicLabel cfg Gamma hD ri 4).1))
            (determinedProjectiveLine cfg L) := by
          rw [hroot]
          have hiProjective :=
            (affinePoint_mem_determinedProjectiveLine_iff cfg i L).2
              (mem_lineSupport.mp hiL)
          simpa [affinePointToProjective_eq_projectivePoint] using hiProjective
        have hxL : x ∈ lineSupport cfg L := by
          simpa [S, blockSystem, geometricBlockSystem,
            geometricBlockSupport] using hxR
        have hyL : y ∈ lineSupport cfg L := by
          simpa [S, blockSystem, geometricBlockSystem,
            geometricBlockSupport] using hyR
        have hzL : z ∈ lineSupport cfg L := by
          simpa [S, blockSystem, geometricBlockSystem,
            geometricBlockSupport] using hzR
        have hdirX0 := elevenFive_double_fibre_chords_on_linePage_axis
          cfg Gamma L hxNotD hzNotD hxL hzL hxz Bx Ex
          (by simpa [S, D] using hBx) (by simpa [S, D] using hEx) hBxE
          (by
            intro q hq hqL
            apply hhostOff Bx hiBx q
              (by simpa [S, D, blockSystem, geometricBlockSystem,
                geometricBlockSupport] using hq)
            simpa [S, blockSystem, geometricBlockSystem,
              geometricBlockSupport] using hqL)
          (by
            intro q hq hqL
            apply hhostOff Ex hiEx q
              (by simpa [S, D, blockSystem, geometricBlockSystem,
                geometricBlockSupport] using hq)
            simpa [S, blockSystem, geometricBlockSystem,
              geometricBlockSupport] using hqL)
        have hdirY0 := elevenFive_double_fibre_chords_on_linePage_axis
          cfg Gamma L hyNotD hzNotD hyL hzL hyz By Ey
          (by simpa [S, D] using hBy) (by simpa [S, D] using hEy) hByE
          (by
            intro q hq hqL
            apply hhostOff By hiBy q
              (by simpa [S, D, blockSystem, geometricBlockSystem,
                geometricBlockSupport] using hq)
            simpa [S, blockSystem, geometricBlockSystem,
              geometricBlockSupport] using hqL)
          (by
            intro q hq hqL
            apply hhostOff Ey hiEy q
              (by simpa [S, D, blockSystem, geometricBlockSystem,
                geometricBlockSupport] using hq)
            simpa [S, blockSystem, geometricBlockSystem,
              geometricBlockSupport] using hqL)
        have hdirX : Projectivization.orthogonal
            (Projectivization.cross
              (fiveConicRootedCyclicProjectiveChord cfg Gamma hD ri exi)
              (fiveConicRootedCyclicProjectiveChord cfg Gamma hD ri fxi))
            (determinedProjectiveLine cfg L) := by
          rw [show exi = fiveConicRootedCyclicChordIndex cfg Gamma hD ri ex by rfl,
            show fxi = fiveConicRootedCyclicChordIndex cfg Gamma hD ri fx by rfl,
            hrootLine ex, hrootLine fx]
          simpa [S, D, ex, fx] using hdirX0
        have hdirY : Projectivization.orthogonal
            (Projectivization.cross
              (fiveConicRootedCyclicProjectiveChord cfg Gamma hD ri eyi)
              (fiveConicRootedCyclicProjectiveChord cfg Gamma hD ri fyi))
            (determinedProjectiveLine cfg L) := by
          rw [show eyi = fiveConicRootedCyclicChordIndex cfg Gamma hD ri ey by rfl,
            show fyi = fiveConicRootedCyclicChordIndex cfg Gamma hD ri fy by rfl,
            hrootLine ey, hrootLine fy]
          simpa [S, D, ey, fy] using hdirY0
        exact fiveConicRootedCyclic_two_double_row_indices_eq_zero_one
          cfg Gamma hD ri (determinedProjectiveLine cfg L) hmark
          rx ry hrxy exi fxi eyi fyi hrowX hrowY hdirX hdirY
      · have hGammaKdet : Gamma ≠ K := by
          intro hEq
          subst K
          have hcardOne : D.card = 1 := by
            simpa [S, D, blockSystem, geometricBlockSystem,
              geometricBlockSupport] using hRtraceS
          have hDfive : D.card = 5 := by simpa [D] using hD
          omega
        have hGammaK : Gamma.1 ≠ K.1 :=
          determinedCircle_coe_ne_of_ne hGammaKdet
        have hiK : i ∈ circleTrace cfg K.1 := by
          simpa [S, blockSystem, geometricBlockSystem,
            geometricBlockSupport] using hiR
        have hmark : Projectivization.orthogonal
            (projectivePoint
              (cfg (fiveConicRootedCyclicLabel cfg Gamma hD ri 4).1))
            (projectiveRadicalAxis Gamma.1 K.1 hGammaK) := by
          rw [hroot]
          exact projectivePoint_orthogonal_projectiveRadicalAxis_of_mem
            hGammaK (mem_circleTrace.mp (by simpa [D] using hiD))
            (mem_circleTrace.mp hiK)
        have hxK : x ∈ circleTrace cfg K.1 := by
          simpa [S, blockSystem, geometricBlockSystem,
            geometricBlockSupport] using hxR
        have hyK : y ∈ circleTrace cfg K.1 := by
          simpa [S, blockSystem, geometricBlockSystem,
            geometricBlockSupport] using hyR
        have hzK : z ∈ circleTrace cfg K.1 := by
          simpa [S, blockSystem, geometricBlockSystem,
            geometricBlockSupport] using hzR
        have hdirX0 := elevenFive_double_fibre_chords_on_circlePage_axis
          cfg Gamma K hGammaK hxNotD hzNotD hxK hzK hxz Bx Ex
          (by simpa [S, D] using hBx) (by simpa [S, D] using hEx) hBxE
          (by
            intro q hq hqK
            apply hhostOff Bx hiBx q
              (by simpa [S, D, blockSystem, geometricBlockSystem,
                geometricBlockSupport] using hq)
            simpa [S, blockSystem, geometricBlockSystem,
              geometricBlockSupport] using hqK)
          (by
            intro q hq hqK
            apply hhostOff Ex hiEx q
              (by simpa [S, D, blockSystem, geometricBlockSystem,
                geometricBlockSupport] using hq)
            simpa [S, blockSystem, geometricBlockSystem,
              geometricBlockSupport] using hqK)
        have hdirY0 := elevenFive_double_fibre_chords_on_circlePage_axis
          cfg Gamma K hGammaK hyNotD hzNotD hyK hzK hyz By Ey
          (by simpa [S, D] using hBy) (by simpa [S, D] using hEy) hByE
          (by
            intro q hq hqK
            apply hhostOff By hiBy q
              (by simpa [S, D, blockSystem, geometricBlockSystem,
                geometricBlockSupport] using hq)
            simpa [S, blockSystem, geometricBlockSystem,
              geometricBlockSupport] using hqK)
          (by
            intro q hq hqK
            apply hhostOff Ey hiEy q
              (by simpa [S, D, blockSystem, geometricBlockSystem,
                geometricBlockSupport] using hq)
            simpa [S, blockSystem, geometricBlockSystem,
              geometricBlockSupport] using hqK)
        have hdirX : Projectivization.orthogonal
            (Projectivization.cross
              (fiveConicRootedCyclicProjectiveChord cfg Gamma hD ri exi)
              (fiveConicRootedCyclicProjectiveChord cfg Gamma hD ri fxi))
            (projectiveRadicalAxis Gamma.1 K.1 hGammaK) := by
          rw [show exi = fiveConicRootedCyclicChordIndex cfg Gamma hD ri ex by rfl,
            show fxi = fiveConicRootedCyclicChordIndex cfg Gamma hD ri fx by rfl,
            hrootLine ex, hrootLine fx]
          simpa [S, D, ex, fx] using hdirX0
        have hdirY : Projectivization.orthogonal
            (Projectivization.cross
              (fiveConicRootedCyclicProjectiveChord cfg Gamma hD ri eyi)
              (fiveConicRootedCyclicProjectiveChord cfg Gamma hD ri fyi))
            (projectiveRadicalAxis Gamma.1 K.1 hGammaK) := by
          rw [show eyi = fiveConicRootedCyclicChordIndex cfg Gamma hD ri ey by rfl,
            show fyi = fiveConicRootedCyclicChordIndex cfg Gamma hD ri fy by rfl,
            hrootLine ey, hrootLine fy]
          simpa [S, D, ey, fy] using hdirY0
        exact fiveConicRootedCyclic_two_double_row_indices_eq_zero_one
          cfg Gamma hD ri (projectiveRadicalAxis Gamma.1 K.1 hGammaK) hmark
          rx ry hrxy exi fxi eyi fyi hrowX hrowY hdirX hdirY
    have hrootE0 :
        (fiveConicRootedCyclicLabel cfg Gamma hD ri 4).1 ∉ e0.1 := by
      rw [hroot]
      intro hi
      apply hiB0
      exact (Finset.mem_inter.mp (by
        simpa [e0, elevenFive_hostTraceChord] using hi)).1
    have hfactor : e0 ∈ fiveConicCyclicChordFactor cfg Gamma hD ri := by
      rcases hrows with ⟨hrx, hry⟩ | ⟨hrx, hry⟩
      · apply fiveConicRootedCyclicChord_mem_factor_of_avoids_root_not_rows_zero_one
          cfg Gamma hD ri e0 hrootE0
        · simpa [e0i, hrx] using hnotX
        · simpa [e0i, hry] using hnotY
      · apply fiveConicRootedCyclicChord_mem_factor_of_avoids_root_not_rows_zero_one
          cfg Gamma hD ri e0 hrootE0
        · simpa [e0i, hry] using hnotY
        · simpa [e0i, hrx] using hnotX
    exact ⟨i, ri, hiEq, hroot, hfactor⟩
  obtain ⟨iP, rP, hPi, hrootP, hfactorP⟩ :=
    hpageFactor P hPtrace hPoutside hPA hPdouble
  obtain ⟨iQ, rQ, hQi, hrootQ, hfactorQ⟩ :=
    hpageFactor Q hQtrace hQoutside hQA hQdouble
  obtain ⟨r0, hr0, hr0unique⟩ :=
    fiveConicCyclicChordFactor_unique cfg Gamma hD e0
  have hrP : rP = r0 := hr0unique rP hfactorP
  have hrQ : rQ = r0 := hr0unique rQ hfactorQ
  have hiPQ : iP = iQ := by
    rw [← hrootP, ← hrootQ, hrP, hrQ]
  have hPAS : A ⊆ S.support P := by
    simpa [S, blockSystem, geometricBlockSystem,
      geometricBlockSupport] using hPA
  have hQAS : A ⊆ S.support Q := by
    simpa [S, blockSystem, geometricBlockSystem,
      geometricBlockSupport] using hQA
  by_contra hPQ
  have hdis := elevenFive_common_outside_pair_trace_disjoint
    S D A hAoutside hAcard hPAS hQAS hPQ
  have hiP : iP ∈ S.support P ∩ D := by rw [hPi]; simp
  have hiQ : iQ ∈ S.support Q ∩ D := by rw [hQi]; simp
  exact (Finset.disjoint_left.mp hdis) hiP (by simpa [hiPQ] using hiQ)

/-- At `H = 29`, the unique single-host outsider pair is contained in every
one-trace page with three (or more) outsiders.  Otherwise three outsiders
of that page are pairwise double-hosted, contradicting the already verified
mixed-carrier all-double K2.1 router. -/
theorem elevenFive_c39_h29_one_trace_contains_exceptional_pair
    {α : Type u} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (Gamma : DeterminedCircle cfg)
    (hpoint : Fintype.card α = 11)
    (hD : (circleTrace cfg Gamma.1).card = 5)
    (hhost : elevenFiveHostWeight (blockSystem cfg)
      (circleTrace cfg Gamma.1) = 29) :
    ∃ A ∈ (Finset.univ \ circleTrace cfg Gamma.1).powersetCard 2,
      (elevenFiveHostPairFibre (blockSystem cfg) (circleTrace cfg Gamma.1) A).card = 1 ∧
        (∀ B ∈ (Finset.univ \ circleTrace cfg Gamma.1).powersetCard 2, B ≠ A →
          (elevenFiveHostPairFibre (blockSystem cfg) (circleTrace cfg Gamma.1) B).card = 2) ∧
        ∀ P : GeometricBlock cfg,
          (geometricBlockSupport cfg P ∩ circleTrace cfg Gamma.1).card = 1 →
          3 ≤ (geometricBlockSupport cfg P \ circleTrace cfg Gamma.1).card →
            A ⊆ geometricBlockSupport cfg P := by
  classical
  let S := blockSystem cfg
  let D := circleTrace cfg Gamma.1
  have hD' : D.card = 5 := by
    simpa [D] using hD
  have hhost' : elevenFiveHostWeight S D = 29 := by
    simpa [S, D] using hhost
  obtain ⟨A, hA, hAcard, hfull⟩ :=
    elevenFiveHostPairFibre_defect_profile_of_hostWeight_eq_twenty_nine
      S D hpoint hD' hhost'
  refine ⟨A, ?_, ?_, ?_, ?_⟩
  · simpa [D] using hA
  · simpa [S, D] using hAcard
  · intro B hB hBne
    simpa [S, D] using hfull B (by simpa [D] using hB) hBne
  · intro P hPtrace hout
    by_contra hnot
    have houtsideThree : 2 <
        (geometricBlockSupport cfg P \ circleTrace cfg Gamma.1).card := by
      omega
    obtain ⟨x, hx, y, hy, z, hz, hxy, hxz, hyz⟩ :=
      Finset.two_lt_card.mp houtsideThree
    have hxyNe : ({x, y} : Finset α) ≠ A := by
      intro hEq
      apply hnot
      intro q hq
      rw [← hEq] at hq
      simp only [Finset.mem_insert, Finset.mem_singleton] at hq
      rcases hq with rfl | rfl
      · exact (Finset.mem_sdiff.mp hx).1
      · exact (Finset.mem_sdiff.mp hy).1
    have hxzNe : ({x, z} : Finset α) ≠ A := by
      intro hEq
      apply hnot
      intro q hq
      rw [← hEq] at hq
      simp only [Finset.mem_insert, Finset.mem_singleton] at hq
      rcases hq with rfl | rfl
      · exact (Finset.mem_sdiff.mp hx).1
      · exact (Finset.mem_sdiff.mp hz).1
    have hyzNe : ({y, z} : Finset α) ≠ A := by
      intro hEq
      apply hnot
      intro q hq
      rw [← hEq] at hq
      simp only [Finset.mem_insert, Finset.mem_singleton] at hq
      rcases hq with rfl | rfl
      · exact (Finset.mem_sdiff.mp hy).1
      · exact (Finset.mem_sdiff.mp hz).1
    apply elevenFive_one_trace_three_outsiders_of_pairwise_double_absurd
      cfg Gamma hD P hPtrace hx hy hz hxy hxz hyz
    · have hxyOutside : ({x, y} : Finset α) ∈
          (Finset.univ \ D).powersetCard 2 :=
        elevenFive_h29_pair_mem_outside_pairs D
          (Finset.mem_sdiff.mp hx).2 (Finset.mem_sdiff.mp hy).2 hxy
      simpa [S, D] using hfull {x, y} hxyOutside hxyNe
    · have hxzOutside : ({x, z} : Finset α) ∈
          (Finset.univ \ D).powersetCard 2 :=
        elevenFive_h29_pair_mem_outside_pairs D
          (Finset.mem_sdiff.mp hx).2 (Finset.mem_sdiff.mp hz).2 hxz
      simpa [S, D] using hfull {x, z} hxzOutside hxzNe
    · have hyzOutside : ({y, z} : Finset α) ∈
          (Finset.univ \ D).powersetCard 2 :=
        elevenFive_h29_pair_mem_outside_pairs D
          (Finset.mem_sdiff.mp hy).2 (Finset.mem_sdiff.mp hz).2 hyz
      simpa [S, D] using hfull {y, z} hyzOutside hyzNe

/-- The one-defect `H = 29` face has no relative `(1,4)` page.  Such a page
has four outsiders; after deleting one endpoint of the exceptional pair it
still contains a three-outside all-double triangle, which is excluded by the
local mixed-carrier K2.1 theorem. -/
theorem elevenFive_c39_h29_relativeCount_one_four_eq_zero
    {α : Type u} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (Gamma : DeterminedCircle cfg)
    (hpoint : Fintype.card α = 11)
    (hD : (circleTrace cfg Gamma.1).card = 5)
    (hhost : elevenFiveHostWeight (blockSystem cfg)
      (circleTrace cfg Gamma.1) = 29) :
    elevenFiveRelativeCount (blockSystem cfg) (circleTrace cfg Gamma.1) 1 4 = 0 := by
  classical
  by_contra hne
  have hpos : 0 < elevenFiveRelativeCount (blockSystem cfg)
      (circleTrace cfg Gamma.1) 1 4 := by omega
  rw [elevenFiveRelativeCount] at hpos
  obtain ⟨P, hP⟩ := Finset.card_pos.mp hpos
  have hspec := Finset.mem_filter.mp hP
  have hPtrace :
      (geometricBlockSupport cfg P ∩ circleTrace cfg Gamma.1).card = 1 :=
    hspec.2.1
  have hPoutside :
      (geometricBlockSupport cfg P \ circleTrace cfg Gamma.1).card = 4 :=
    hspec.2.2
  obtain ⟨A, hA, hAone, hfull, hcontain⟩ :=
    elevenFive_c39_h29_one_trace_contains_exceptional_pair
      cfg Gamma hpoint hD hhost
  have hAP : A ⊆ geometricBlockSupport cfg P :=
    hcontain P hPtrace (by omega)
  have hAoutside := (Finset.mem_powersetCard.mp hA).1
  have hAcard : A.card = 2 := (Finset.mem_powersetCard.mp hA).2
  obtain ⟨u, v, huv, hAeq⟩ := Finset.card_eq_two.mp hAcard
  have huA : u ∈ A := by rw [hAeq]; simp
  let U : Finset α := geometricBlockSupport cfg P \ circleTrace cfg Gamma.1
  have hUcard : U.card = 4 := by simpa [U] using hPoutside
  have huU : u ∈ U := by
    apply Finset.mem_sdiff.mpr
    refine ⟨hAP huA, ?_⟩
    exact (Finset.mem_sdiff.mp (hAoutside huA)).2
  have hUerase : 2 < (U.erase u).card := by
    rw [Finset.card_erase_of_mem huU, hUcard]
    norm_num
  obtain ⟨x, hx, y, hy, z, hz, hxy, hxz, hyz⟩ :=
    Finset.two_lt_card.mp hUerase
  have hxU : x ∈ U := (Finset.mem_erase.mp hx).2
  have hyU : y ∈ U := (Finset.mem_erase.mp hy).2
  have hzU : z ∈ U := (Finset.mem_erase.mp hz).2
  have hxyNe : ({x, y} : Finset α) ≠ A := by
    intro hEq
    have huPair : u ∈ ({x, y} : Finset α) := by rw [hEq]; exact huA
    simp only [Finset.mem_insert, Finset.mem_singleton] at huPair
    rcases huPair with hux | huy
    · exact (Finset.mem_erase.mp hx).1 hux.symm
    · exact (Finset.mem_erase.mp hy).1 huy.symm
  have hxzNe : ({x, z} : Finset α) ≠ A := by
    intro hEq
    have huPair : u ∈ ({x, z} : Finset α) := by rw [hEq]; exact huA
    simp only [Finset.mem_insert, Finset.mem_singleton] at huPair
    rcases huPair with hux | huz
    · exact (Finset.mem_erase.mp hx).1 hux.symm
    · exact (Finset.mem_erase.mp hz).1 huz.symm
  have hyzNe : ({y, z} : Finset α) ≠ A := by
    intro hEq
    have huPair : u ∈ ({y, z} : Finset α) := by rw [hEq]; exact huA
    simp only [Finset.mem_insert, Finset.mem_singleton] at huPair
    rcases huPair with huy | huz
    · exact (Finset.mem_erase.mp hy).1 huy.symm
    · exact (Finset.mem_erase.mp hz).1 huz.symm
  apply elevenFive_one_trace_three_outsiders_of_pairwise_double_absurd
    cfg Gamma hD P hPtrace
    (by simpa [U] using hxU) (by simpa [U] using hyU) (by simpa [U] using hzU)
    hxy hxz hyz
  · apply hfull {x, y}
    · apply elevenFive_h29_pair_mem_outside_pairs (circleTrace cfg Gamma.1)
        (by simpa [U] using (Finset.mem_sdiff.mp hxU).2)
        (by simpa [U] using (Finset.mem_sdiff.mp hyU).2) hxy
    · exact hxyNe
  · apply hfull {x, z}
    · apply elevenFive_h29_pair_mem_outside_pairs (circleTrace cfg Gamma.1)
        (by simpa [U] using (Finset.mem_sdiff.mp hxU).2)
        (by simpa [U] using (Finset.mem_sdiff.mp hzU).2) hxz
    · exact hxzNe
  · apply hfull {y, z}
    · apply elevenFive_h29_pair_mem_outside_pairs (circleTrace cfg Gamma.1)
        (by simpa [U] using (Finset.mem_sdiff.mp hyU).2)
        (by simpa [U] using (Finset.mem_sdiff.mp hzU).2) hyz
    · exact hyzNe

/-- The C39 size-four/five row turns the now-vanishing `(1,4)` census into
the exact H29 front equation `A13 + q = 6`. -/
theorem elevenFive_c39_h29_relativeCount_one_three_add_outsideRich_eq_six
    {α : Type u} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (hcap : BlockSizeCap (blockSystem cfg) 5)
    (hglobal : ElevenFiveGlobalRows (blockSystem cfg))
    (hC : (blockSystem cfg).totalCircleCount = 39)
    (hL : elevenFiveLineTotal (blockSystem cfg) = 12)
    (Gamma : DeterminedCircle cfg)
    (hD : (circleTrace cfg Gamma.1).card = 5)
    (hhost : elevenFiveHostWeight (blockSystem cfg)
      (circleTrace cfg Gamma.1) = 29)
    (h14 : elevenFiveRelativeCount (blockSystem cfg) (circleTrace cfg Gamma.1) 1 4 = 0) :
    elevenFiveRelativeCount (blockSystem cfg) (circleTrace cfg Gamma.1) 1 3 +
      elevenFiveOutsideRichWeight (blockSystem cfg) (circleTrace cfg Gamma.1) = 6 := by
  classical
  let S := blockSystem cfg
  let D := circleTrace cfg Gamma.1
  let b : GeometricBlock cfg := Sum.inr Gamma
  have hb : b ∈ S.blocksOfSize 5 := by
    apply S.mem_blocksOfSize.mpr
    simpa [S, b, D, blockSystem, geometricBlockSystem] using hD
  have hDb : S.support b = D := by
    simp [S, b, D, blockSystem, geometricBlockSystem, geometricBlockSupport]
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
  have hhost' : elevenFiveHostWeight S D = 29 := by simpa [S, D] using hhost
  have h14' : elevenFiveRelativeCount S D 1 4 = 0 := by
    simpa [S, D] using h14
  simpa [S, D] using (show
    elevenFiveRelativeCount S D 1 3 + elevenFiveOutsideRichWeight S D = 6 by
      omega)

/-- Before the one-single K2.1 colour law is invoked, pure triple ownership
already bounds the H29 `(1,3)` pages by the three selected labels absent
from the unique host trace of the exceptional pair. -/
theorem elevenFive_c39_h29_relativeCount_one_three_le_three
    {α : Type u} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (Gamma : DeterminedCircle cfg)
    (hpoint : Fintype.card α = 11)
    (hD : (circleTrace cfg Gamma.1).card = 5)
    (hhost : elevenFiveHostWeight (blockSystem cfg)
      (circleTrace cfg Gamma.1) = 29) :
    elevenFiveRelativeCount (blockSystem cfg) (circleTrace cfg Gamma.1) 1 3 ≤ 3 := by
  classical
  let S := blockSystem cfg
  let D := circleTrace cfg Gamma.1
  let R : Finset (GeometricBlock cfg) := Finset.univ.filter fun P =>
    (S.support P ∩ D).card = 1 ∧ (S.support P \ D).card = 3
  obtain ⟨A, hA, hAone, _hfull, hcontain⟩ :=
    elevenFive_c39_h29_one_trace_contains_exceptional_pair
      cfg Gamma hpoint hD hhost
  have hAoutside : A ⊆ Finset.univ \ D := by simpa [D] using
    (Finset.mem_powersetCard.mp hA).1
  have hAcard : A.card = 2 := (Finset.mem_powersetCard.mp hA).2
  have hBpos : 0 < (elevenFiveHostPairFibre S D A).card := by
    have hAone' : (elevenFiveHostPairFibre S D A).card = 1 := by
      simpa [S, D] using hAone
    omega
  obtain ⟨B, hB⟩ := Finset.card_pos.mp hBpos
  have hBdata := (mem_elevenFiveHostPairFibre S D A).mp hB
  have hBtrace : (S.support B ∩ D).card = 2 :=
    (Finset.mem_filter.mp hBdata.1).2
  have hBA : A ⊆ S.support B := hBdata.2
  have hRpairwise : ((R : Finset (GeometricBlock cfg)) :
      Set (GeometricBlock cfg)).PairwiseDisjoint fun P => S.support P ∩ D := by
    intro P hPR Q hQR hPQ
    have hPRspec := Finset.mem_filter.mp hPR
    have hQRspec := Finset.mem_filter.mp hQR
    have hPout :
        (geometricBlockSupport cfg P \ circleTrace cfg Gamma.1).card = 3 := by
      simpa [S, D, blockSystem, geometricBlockSystem, geometricBlockSupport] using
        hPRspec.2.2
    have hQout :
        (geometricBlockSupport cfg Q \ circleTrace cfg Gamma.1).card = 3 := by
      simpa [S, D, blockSystem, geometricBlockSystem, geometricBlockSupport] using
        hQRspec.2.2
    have hPA : A ⊆ S.support P := by
      simpa [S, D, blockSystem, geometricBlockSystem, geometricBlockSupport] using
        hcontain P
          (by simpa [S, D, blockSystem, geometricBlockSystem,
            geometricBlockSupport] using hPRspec.2.1)
          (by omega)
    have hQA : A ⊆ S.support Q := by
      simpa [S, D, blockSystem, geometricBlockSystem, geometricBlockSupport] using
        hcontain Q
          (by simpa [S, D, blockSystem, geometricBlockSystem,
            geometricBlockSupport] using hQRspec.2.1)
          (by omega)
    exact elevenFive_common_outside_pair_trace_disjoint
      S D A hAoutside hAcard hPA hQA hPQ
  have hbiCard :
      (R.biUnion fun P => S.support P ∩ D).card = R.card := by
    rw [Finset.card_biUnion hRpairwise]
    calc
      (∑ P ∈ R, (S.support P ∩ D).card) = ∑ _P ∈ R, 1 := by
        apply Finset.sum_congr rfl
        intro P hPR
        exact (Finset.mem_filter.mp hPR).2.1
      _ = R.card := by simp
  have hbisub : R.biUnion (fun P => S.support P ∩ D) ⊆
      D \ (S.support B ∩ D) := by
    intro i hi
    obtain ⟨P, hPR, hiP⟩ := Finset.mem_biUnion.mp hi
    have hPRspec := Finset.mem_filter.mp hPR
    have hPout :
        (geometricBlockSupport cfg P \ circleTrace cfg Gamma.1).card = 3 := by
      simpa [S, D, blockSystem, geometricBlockSystem, geometricBlockSupport] using
        hPRspec.2.2
    have hPA : A ⊆ S.support P := by
      simpa [S, D, blockSystem, geometricBlockSystem, geometricBlockSupport] using
        hcontain P
          (by simpa [S, D, blockSystem, geometricBlockSystem,
            geometricBlockSupport] using hPRspec.2.1)
          (by omega)
    refine Finset.mem_sdiff.mpr ⟨(Finset.mem_inter.mp hiP).2, ?_⟩
    intro hiB
    have hPB : P ≠ B := by
      intro hEq
      subst P
      rw [hBtrace] at hPRspec
      omega
    have hdis := elevenFive_common_outside_pair_trace_disjoint
      S D A hAoutside hAcard hPA hBA hPB
    exact (Finset.disjoint_left.mp hdis) hiP hiB
  have hcompCard : (D \ (S.support B ∩ D)).card = 3 := by
    rw [Finset.card_sdiff_of_subset Finset.inter_subset_right, hD, hBtrace]
  have hle := Finset.card_le_card hbisub
  rw [hbiCard, hcompCard] at hle
  simpa [R, S, D, elevenFiveRelativeCount] using hle

/-- The finite rich-block cap turns the H29 front equation into the lower
bound `A13 ≥ 3`. -/
theorem elevenFive_c39_h29_relativeCount_one_three_ge_three
    {α : Type u} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (hpoint : Fintype.card α = 11)
    (hcap : BlockSizeCap (blockSystem cfg) 5)
    (hglobal : ElevenFiveGlobalRows (blockSystem cfg))
    (hC : (blockSystem cfg).totalCircleCount = 39)
    (hL : elevenFiveLineTotal (blockSystem cfg) = 12)
    (Gamma : DeterminedCircle cfg)
    (hD : (circleTrace cfg Gamma.1).card = 5)
    (hhost : elevenFiveHostWeight (blockSystem cfg)
      (circleTrace cfg Gamma.1) = 29)
    (h14 : elevenFiveRelativeCount (blockSystem cfg) (circleTrace cfg Gamma.1) 1 4 = 0) :
    3 ≤ elevenFiveRelativeCount (blockSystem cfg) (circleTrace cfg Gamma.1) 1 3 := by
  have hfront := elevenFive_c39_h29_relativeCount_one_three_add_outsideRich_eq_six
    cfg hcap hglobal hC hL Gamma hD hhost h14
  have hqcap := elevenFiveOutsideRichWeight_le_three (blockSystem cfg)
    (circleTrace cfg Gamma.1) hpoint hD
  omega

/-- The entirely finite H29 front is saturated: the all-double router first
removes `A14`, and then the size row together with triple ownership leaves
exactly three `A13` pages and rich weight three. -/
theorem elevenFive_c39_h29_front_saturated
    {α : Type u} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (hpoint : Fintype.card α = 11)
    (hcap : BlockSizeCap (blockSystem cfg) 5)
    (hglobal : ElevenFiveGlobalRows (blockSystem cfg))
    (hC : (blockSystem cfg).totalCircleCount = 39)
    (hL : elevenFiveLineTotal (blockSystem cfg) = 12)
    (Gamma : DeterminedCircle cfg)
    (hD : (circleTrace cfg Gamma.1).card = 5)
    (hhost : elevenFiveHostWeight (blockSystem cfg)
      (circleTrace cfg Gamma.1) = 29) :
    elevenFiveRelativeCount (blockSystem cfg) (circleTrace cfg Gamma.1) 1 4 = 0 ∧
      elevenFiveRelativeCount (blockSystem cfg) (circleTrace cfg Gamma.1) 1 3 = 3 ∧
        elevenFiveOutsideRichWeight (blockSystem cfg) (circleTrace cfg Gamma.1) = 3 := by
  have h14 := elevenFive_c39_h29_relativeCount_one_four_eq_zero
    cfg Gamma hpoint hD hhost
  have hfront := elevenFive_c39_h29_relativeCount_one_three_add_outsideRich_eq_six
    cfg hcap hglobal hC hL Gamma hD hhost h14
  have hlow := elevenFive_c39_h29_relativeCount_one_three_ge_three
    cfg hpoint hcap hglobal hC hL Gamma hD hhost h14
  have hupp := elevenFive_c39_h29_relativeCount_one_three_le_three
    cfg Gamma hpoint hD hhost
  omega

/-- The rooted one-single/two-double page law improves the finite bound
`A13 ≤ 3` to the sharp local bound `A13 ≤ 1`. -/
theorem elevenFive_c39_h29_relativeCount_one_three_le_one
    {α : Type u} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (Gamma : DeterminedCircle cfg)
    (hpoint : Fintype.card α = 11)
    (hD : (circleTrace cfg Gamma.1).card = 5)
    (hhost : elevenFiveHostWeight (blockSystem cfg)
      (circleTrace cfg Gamma.1) = 29) :
    elevenFiveRelativeCount (blockSystem cfg)
      (circleTrace cfg Gamma.1) 1 3 ≤ 1 := by
  classical
  obtain ⟨A, hA, hAone, hfull, hcontain⟩ :=
    elevenFive_c39_h29_one_trace_contains_exceptional_pair
      cfg Gamma hpoint hD hhost
  rw [elevenFiveRelativeCount, Finset.card_le_one]
  intro P hP Q hQ
  have hPspec := Finset.mem_filter.mp hP
  have hQspec := Finset.mem_filter.mp hQ
  have hPdouble : ∀ E ∈ (geometricBlockSupport cfg P \
        circleTrace cfg Gamma.1).powersetCard 2, E ≠ A →
      (elevenFiveHostPairFibre (blockSystem cfg)
        (circleTrace cfg Gamma.1) E).card = 2 := by
    intro E hE hEA
    apply hfull E
    · apply Finset.mem_powersetCard.mpr
      refine ⟨?_, (Finset.mem_powersetCard.mp hE).2⟩
      intro q hq
      have hqout := (Finset.mem_powersetCard.mp hE).1 hq
      exact Finset.mem_sdiff.mpr
        ⟨Finset.mem_univ q, (Finset.mem_sdiff.mp hqout).2⟩
    · exact hEA
  have hQdouble : ∀ E ∈ (geometricBlockSupport cfg Q \
        circleTrace cfg Gamma.1).powersetCard 2, E ≠ A →
      (elevenFiveHostPairFibre (blockSystem cfg)
        (circleTrace cfg Gamma.1) E).card = 2 := by
    intro E hE hEA
    apply hfull E
    · apply Finset.mem_powersetCard.mpr
      refine ⟨?_, (Finset.mem_powersetCard.mp hE).2⟩
      intro q hq
      have hqout := (Finset.mem_powersetCard.mp hE).1 hq
      exact Finset.mem_sdiff.mpr
        ⟨Finset.mem_univ q, (Finset.mem_sdiff.mp hqout).2⟩
    · exact hEA
  apply elevenFive_one_single_two_double_pages_eq cfg Gamma hD A hA hAone
  · exact hPspec.2.1
  · exact hPspec.2.2
  · exact hcontain P hPspec.2.1 (Nat.le_of_eq hPspec.2.2.symm)
  · exact hPdouble
  · exact hQspec.2.1
  · exact hQspec.2.2
  · exact hcontain Q hQspec.2.1 (Nat.le_of_eq hQspec.2.2.symm)
  · exact hQdouble

/-- The saturated H29 front requires three `(1,3)` pages, while the rooted
one-single/two-double law permits at most one. -/
theorem elevenFive_c39_hostWeight_ne_twenty_nine
    {α : Type u} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (hpoint : Fintype.card α = 11)
    (hcap : BlockSizeCap (blockSystem cfg) 5)
    (hglobal : ElevenFiveGlobalRows (blockSystem cfg))
    (hC : (blockSystem cfg).totalCircleCount = 39)
    (hL : elevenFiveLineTotal (blockSystem cfg) = 12)
    (Gamma : DeterminedCircle cfg)
    (hD : (circleTrace cfg Gamma.1).card = 5) :
    elevenFiveHostWeight (blockSystem cfg)
      (circleTrace cfg Gamma.1) ≠ 29 := by
  intro hhost
  have hfront := elevenFive_c39_h29_front_saturated
    cfg hpoint hcap hglobal hC hL Gamma hD hhost
  have hlocal := elevenFive_c39_h29_relativeCount_one_three_le_one
    cfg Gamma hpoint hD hhost
  omega

end Erdos506.V1
