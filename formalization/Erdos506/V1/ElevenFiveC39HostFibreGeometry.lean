import Erdos506.V1.ElevenFiveC39CirclePageAdapter
import Mathlib.Tactic

/-!
# Actual host-fibre extraction for the C39 high-host faces

This module turns the numerical pair fibres into concrete geometric blocks.
For one outsider pair, the selected traces of two distinct hosts are
disjoint; this is exactly unique triple ownership.  In a configuration two
such hosts cannot both be lines, so a saturated fibre always supplies a
proper-circle host.  These facts are the finite/actual input shared by the
H=30 and H=29 K2 page arguments.
-/

namespace Erdos506.V1

open Erdos506.Block
open Erdos506.Block.BlockSystem
open Erdos506.Finite
open Erdos506.Incidence
open Erdos506.V4

universe u v

variable {Point : Type u} {Block : Type v}
  [Fintype Point] [Fintype Block] [DecidableEq Point]

/-- Distinct actual hosts of one outside pair have disjoint two-point traces
on the selected five-set. -/
theorem elevenFiveHostPairFibre_trace_disjoint
    (S : BlockSystem Point Block) (D A : Finset Point)
    (hA : A ∈ (Finset.univ \ D).powersetCard 2)
    {b c : Block}
    (hb : b ∈ elevenFiveHostPairFibre S D A)
    (hc : c ∈ elevenFiveHostPairFibre S D A) (hbc : b ≠ c) :
    Disjoint (S.support b ∩ D) (S.support c ∩ D) := by
  classical
  have hAspec := Finset.mem_powersetCard.mp hA
  have hAoutside : A ⊆ Finset.univ \ D := hAspec.1
  have hAcard : A.card = 2 := hAspec.2
  have hbdata := (mem_elevenFiveHostPairFibre S D A).mp hb
  have hcdata := (mem_elevenFiveHostPairFibre S D A).mp hc
  rw [Finset.disjoint_left]
  intro p hpB hpC
  have hpD : p ∈ D := (Finset.mem_inter.mp hpB).2
  have hpNotA : p ∉ A := by
    intro hpA
    exact (Finset.mem_sdiff.mp (hAoutside hpA)).2 hpD
  have hsub : insert p A ⊆ S.support b ∩ S.support c := by
    intro q hq
    rcases Finset.mem_insert.mp hq with rfl | hqA
    · exact Finset.mem_inter.mpr
        ⟨(Finset.mem_inter.mp hpB).1, (Finset.mem_inter.mp hpC).1⟩
    · exact Finset.mem_inter.mpr ⟨hbdata.2 hqA, hcdata.2 hqA⟩
  have hcard : (insert p A).card = 3 := by
    rw [Finset.card_insert_of_notMem hpNotA, hAcard]
  have hle := Finset.card_le_card hsub
  have hlt := S.distinct_block_inter_card_lt_three hbc
  omega

/-- A saturated pair fibre exposes two named, different host blocks. -/
theorem elevenFiveHostPairFibre_exists_two_distinct_of_card_eq_two
    (S : BlockSystem Point Block) (D A : Finset Point)
    (hcard : (elevenFiveHostPairFibre S D A).card = 2) :
    ∃ b c : Block, b ∈ elevenFiveHostPairFibre S D A ∧
      c ∈ elevenFiveHostPairFibre S D A ∧ b ≠ c := by
  classical
  obtain ⟨b, c, hbc, hset⟩ := Finset.card_eq_two.mp hcard
  refine ⟨b, c, ?_, ?_, hbc⟩
  · rw [hset]
    simp
  · rw [hset]
    simp

/-! ## The configuration-level line exclusion -/

private theorem determinedLine_eq_of_two_common_labels
    {α : Type u} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (L M : DeterminedLine cfg)
    {x y : α} (hxy : x ≠ y)
    (hxL : x ∈ lineSupport cfg L) (hyL : y ∈ lineSupport cfg L)
    (hxM : x ∈ lineSupport cfg M) (hyM : y ∈ lineSupport cfg M) :
    L = M := by
  let A : KSubset α 2 := ⟨{x, y}, by simp [hxy]⟩
  have hlineL : lineOfPair cfg A = L.1 :=
    lineOfPair_eq_of_mem_of_direction_finrank_one cfg A L.1 (by
      intro q hq
      simp only [A, Finset.mem_insert, Finset.mem_singleton] at hq
      rcases hq with rfl | rfl
      · exact mem_lineSupport.mp hxL
      · exact mem_lineSupport.mp hyL) L.direction_finrank
  have hlineM : lineOfPair cfg A = M.1 :=
    lineOfPair_eq_of_mem_of_direction_finrank_one cfg A M.1 (by
      intro q hq
      simp only [A, Finset.mem_insert, Finset.mem_singleton] at hq
      rcases hq with rfl | rfl
      · exact mem_lineSupport.mp hxM
      · exact mem_lineSupport.mp hyM) M.direction_finrank
  apply Subtype.ext
  exact hlineL.symm.trans hlineM

/-- Two distinct blocks in one actual host pair fibre cannot both be
line-tagged.  Hence every double host supplies at least one proper circle,
even before the generalized line/circle trace bridge is completed. -/
theorem elevenFiveHostPairFibre_not_both_lines
    {α : Type u} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (D A : Finset α)
    (hA : A ∈ (Finset.univ \ D).powersetCard 2)
    {b c : GeometricBlock cfg}
    (hb : b ∈ elevenFiveHostPairFibre (blockSystem cfg) D A)
    (hc : c ∈ elevenFiveHostPairFibre (blockSystem cfg) D A)
    (hbc : b ≠ c) :
    ¬ (∃ L M : DeterminedLine cfg, b = Sum.inl L ∧ c = Sum.inl M) := by
  classical
  rintro ⟨L, M, rfl, rfl⟩
  have hAspec := Finset.mem_powersetCard.mp hA
  obtain ⟨x, y, hxy, hAeq⟩ := Finset.card_eq_two.mp hAspec.2
  have hsubL : A ⊆ geometricBlockSupport cfg (Sum.inl L : GeometricBlock cfg) :=
    ((mem_elevenFiveHostPairFibre (blockSystem cfg) D A).mp hb).2
  have hsubM : A ⊆ geometricBlockSupport cfg (Sum.inl M : GeometricBlock cfg) :=
    ((mem_elevenFiveHostPairFibre (blockSystem cfg) D A).mp hc).2
  have hxL : x ∈ lineSupport cfg L := by
    change x ∈ geometricBlockSupport cfg (Sum.inl L : GeometricBlock cfg)
    apply hsubL
    simp [hAeq]
  have hyL : y ∈ lineSupport cfg L := by
    change y ∈ geometricBlockSupport cfg (Sum.inl L : GeometricBlock cfg)
    apply hsubL
    simp [hAeq]
  have hxM : x ∈ lineSupport cfg M := by
    change x ∈ geometricBlockSupport cfg (Sum.inl M : GeometricBlock cfg)
    apply hsubM
    simp [hAeq]
  have hyM : y ∈ lineSupport cfg M := by
    change y ∈ geometricBlockSupport cfg (Sum.inl M : GeometricBlock cfg)
    apply hsubM
    simp [hAeq]
  apply hbc
  congr 1
  exact determinedLine_eq_of_two_common_labels cfg L M hxy hxL hyL hxM hyM

/-- In a double actual pair fibre, at least one named host is a proper
circle.  This is an existential extraction, not a colour assumption. -/
theorem elevenFiveHostPairFibre_exists_circle_of_card_eq_two
    {α : Type u} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (D A : Finset α)
    (hA : A ∈ (Finset.univ \ D).powersetCard 2)
    (hcard : (elevenFiveHostPairFibre (blockSystem cfg) D A).card = 2) :
    ∃ C : DeterminedCircle cfg,
      Sum.inr C ∈ elevenFiveHostPairFibre (blockSystem cfg) D A := by
  classical
  obtain ⟨b, c, hb, hc, hbc⟩ :=
    elevenFiveHostPairFibre_exists_two_distinct_of_card_eq_two
      (blockSystem cfg) D A hcard
  rcases b with L | C
  · rcases c with M | C
    · exact False.elim
        (elevenFiveHostPairFibre_not_both_lines cfg D A hA hb hc hbc
          ⟨L, M, rfl, rfl⟩)
    · exact ⟨C, hc⟩
  · refine ⟨C, ?_⟩
    exact hb

/-- A saturated actual outsider-pair fibre has one of exactly two geometric
forms: it is either genuinely double-circle, or it has one line host and one
circle host.  This is a literal case split on the two actual blocks, with the
line--line branch excluded by pair uniqueness.  In particular, no colour or
page normalisation is being assumed here. -/
theorem elevenFiveHostPairFibre_double_circle_or_line_circle
    {α : Type u} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (D A : Finset α)
    (hA : A ∈ (Finset.univ \ D).powersetCard 2)
    (hcard : (elevenFiveHostPairFibre (blockSystem cfg) D A).card = 2) :
    (∃ C E : DeterminedCircle cfg, C ≠ E ∧
        Sum.inr C ∈ elevenFiveHostPairFibre (blockSystem cfg) D A ∧
          Sum.inr E ∈ elevenFiveHostPairFibre (blockSystem cfg) D A) ∨
      (∃ L : DeterminedLine cfg, ∃ C : DeterminedCircle cfg,
        Sum.inl L ∈ elevenFiveHostPairFibre (blockSystem cfg) D A ∧
          Sum.inr C ∈ elevenFiveHostPairFibre (blockSystem cfg) D A) := by
  classical
  obtain ⟨b, c, hb, hc, hbc⟩ :=
    elevenFiveHostPairFibre_exists_two_distinct_of_card_eq_two
      (blockSystem cfg) D A hcard
  rcases b with L | C
  · rcases c with M | E
    · exact False.elim
        (elevenFiveHostPairFibre_not_both_lines cfg D A hA hb hc hbc
          ⟨L, M, rfl, rfl⟩)
    · exact Or.inr ⟨L, E, hb, hc⟩
  · rcases c with L | E
    · exact Or.inr ⟨L, C, hc, hb⟩
    · left
      refine ⟨C, E, ?_, hb, hc⟩
      intro hCE
      apply hbc
      simpa [hCE]

/-- In the all-double `H = 30` face, every outsider pair has the preceding
actual circle--circle versus line--circle dichotomy.  This only composes the
finite saturation identity with the carrier case split. -/
theorem elevenFiveHostPairFibre_double_circle_or_line_circle_of_hostWeight_eq_thirty
    {α : Type u} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (D : Finset α)
    (hpoint : Fintype.card α = 11) (hD : D.card = 5)
    (hhost : elevenFiveHostWeight (blockSystem cfg) D = 30)
    (A : Finset α) (hA : A ∈ (Finset.univ \ D).powersetCard 2) :
    (∃ C E : DeterminedCircle cfg, C ≠ E ∧
        Sum.inr C ∈ elevenFiveHostPairFibre (blockSystem cfg) D A ∧
          Sum.inr E ∈ elevenFiveHostPairFibre (blockSystem cfg) D A) ∨
      (∃ L : DeterminedLine cfg, ∃ C : DeterminedCircle cfg,
        Sum.inl L ∈ elevenFiveHostPairFibre (blockSystem cfg) D A ∧
          Sum.inr C ∈ elevenFiveHostPairFibre (blockSystem cfg) D A) := by
  apply elevenFiveHostPairFibre_double_circle_or_line_circle cfg D A hA
  exact elevenFiveHostPairFibre_card_eq_two_of_hostWeight_eq_thirty
    (blockSystem cfg) D hpoint hD hhost hA

/-- The two circle hosts in the circle--circle branch carry disjoint marked
two-traces.  This is the literal matching condition needed before their
chords can be fed to a page/trace argument. -/
theorem elevenFiveHostPairFibre_circle_circle_trace_disjoint
    {α : Type u} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (D A : Finset α)
    (hA : A ∈ (Finset.univ \ D).powersetCard 2)
    {C E : DeterminedCircle cfg}
    (hC : Sum.inr C ∈ elevenFiveHostPairFibre (blockSystem cfg) D A)
    (hE : Sum.inr E ∈ elevenFiveHostPairFibre (blockSystem cfg) D A)
    (hCE : C ≠ E) :
    Disjoint (circleTrace cfg C.1 ∩ D) (circleTrace cfg E.1 ∩ D) := by
  have hblock : (Sum.inr C : GeometricBlock cfg) ≠ Sum.inr E := by
    intro hEq
    exact hCE (Sum.inr.inj hEq)
  have hdisjoint := elevenFiveHostPairFibre_trace_disjoint
    (blockSystem cfg) D A hA hC hE hblock
  simpa [blockSystem, geometricBlockSystem, geometricBlockSupport] using
    hdisjoint

/-- If a saturated fibre has no line member, its two actual members are two
different proper circles.  This is the exact extractor consumed by the
circle-page endpoint; the no-line premise is a concrete finite membership
statement, not a replacement geometry assumption. -/
theorem elevenFiveHostPairFibre_exists_two_distinct_circles_of_no_line
    {α : Type u} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (D A : Finset α)
    (hA : A ∈ (Finset.univ \ D).powersetCard 2)
    (hcard : (elevenFiveHostPairFibre (blockSystem cfg) D A).card = 2)
    (hnoLine : ∀ L : DeterminedLine cfg,
      Sum.inl L ∉ elevenFiveHostPairFibre (blockSystem cfg) D A) :
    ∃ C E : DeterminedCircle cfg, C ≠ E ∧
      Sum.inr C ∈ elevenFiveHostPairFibre (blockSystem cfg) D A ∧
        Sum.inr E ∈ elevenFiveHostPairFibre (blockSystem cfg) D A := by
  rcases elevenFiveHostPairFibre_double_circle_or_line_circle
    cfg D A hA hcard with hcircles | hmixed
  · exact hcircles
  · rcases hmixed with ⟨L, C, hL, _hC⟩
    exact False.elim (hnoLine L hL)

end Erdos506.V1
