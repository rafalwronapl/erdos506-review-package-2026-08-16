import Erdos506.V1.ElevenFiveC39H30Finish
import Erdos506.V1.ElevenFiveC39HighHostFinish
import Mathlib.Tactic

/-!
# The two-defect `H = 28` front of the C39 host router

At host weight twenty-eight the outsider-pair fibres have total defect two.
The finite profile is therefore either one empty fibre, or two single fibres.
This file records the lossless passage from that profile to actual one-trace
pages and the exact signed front

`A13 + 3 * A14 + q = 7`.

The only geometric step intentionally not asserted here is the actual-
configuration adapter for the zero-fibre/four-page residual to
`fiveConic_goldenAxis_tangentSeparation_absurd`.  Its precise interface is
`ElevenFiveC39H28GoldenAxisActualAdapter`; it is a proposition passed as a
hypothesis, not an axiom.
-/

namespace Erdos506.V1

open Erdos506.Block
open Erdos506.Block.BlockSystem
open Erdos506.Incidence
open Erdos506.V3
open Erdos506.V4
open scoped BigOperators

universe u

private theorem elevenFive_h28_pair_mem_outsidePairs
    {Point : Type u} [Fintype Point] [DecidableEq Point]
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

/-- If every outsider pair except `A` is double-hosted, every one-trace
page with at least three outsiders contains `A`.  The cardinality of the
exceptional fibre is irrelevant; this covers both the H29 single fibre and
the H28 empty-fibre branch. -/
theorem elevenFive_one_trace_contains_exceptionalPair_of_otherPairs_double
    {α : Type u} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (Gamma : DeterminedCircle cfg)
    (hD : (circleTrace cfg Gamma.1).card = 5)
    (A : Finset α)
    (hfull : ∀ E ∈ (Finset.univ \ circleTrace cfg Gamma.1).powersetCard 2,
      E ≠ A →
        (elevenFiveHostPairFibre (blockSystem cfg)
          (circleTrace cfg Gamma.1) E).card = 2)
    (P : GeometricBlock cfg)
    (hPtrace : (geometricBlockSupport cfg P ∩
      circleTrace cfg Gamma.1).card = 1)
    (hout : 3 ≤ (geometricBlockSupport cfg P \
      circleTrace cfg Gamma.1).card) :
    A ⊆ geometricBlockSupport cfg P := by
  classical
  by_contra hnot
  have hthree : 2 < (geometricBlockSupport cfg P \
      circleTrace cfg Gamma.1).card := by omega
  obtain ⟨x, hx, y, hy, z, hz, hxy, hxz, hyz⟩ :=
    Finset.two_lt_card.mp hthree
  have hxyA : ({x, y} : Finset α) ≠ A := by
    intro hEq
    apply hnot
    intro q hq
    rw [← hEq] at hq
    simp only [Finset.mem_insert, Finset.mem_singleton] at hq
    rcases hq with rfl | rfl
    · exact (Finset.mem_sdiff.mp hx).1
    · exact (Finset.mem_sdiff.mp hy).1
  have hxzA : ({x, z} : Finset α) ≠ A := by
    intro hEq
    apply hnot
    intro q hq
    rw [← hEq] at hq
    simp only [Finset.mem_insert, Finset.mem_singleton] at hq
    rcases hq with rfl | rfl
    · exact (Finset.mem_sdiff.mp hx).1
    · exact (Finset.mem_sdiff.mp hz).1
  have hyzA : ({y, z} : Finset α) ≠ A := by
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
  · apply hfull {x, y}
    · exact elevenFive_h28_pair_mem_outsidePairs _
        (Finset.mem_sdiff.mp hx).2 (Finset.mem_sdiff.mp hy).2 hxy
    · exact hxyA
  · apply hfull {x, z}
    · exact elevenFive_h28_pair_mem_outsidePairs _
        (Finset.mem_sdiff.mp hx).2 (Finset.mem_sdiff.mp hz).2 hxz
    · exact hxzA
  · apply hfull {y, z}
    · exact elevenFive_h28_pair_mem_outsidePairs _
        (Finset.mem_sdiff.mp hy).2 (Finset.mem_sdiff.mp hz).2 hyz
    · exact hyzA

/-- With two exceptional fibres, every one-trace page with at least three
outsiders contains at least one of the two exceptional pairs. -/
theorem elevenFive_one_trace_contains_one_of_two_exceptionalPairs
    {α : Type u} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (Gamma : DeterminedCircle cfg)
    (hD : (circleTrace cfg Gamma.1).card = 5)
    (A B : Finset α)
    (hfull : ∀ E ∈ (Finset.univ \ circleTrace cfg Gamma.1).powersetCard 2,
      E ≠ A → E ≠ B →
        (elevenFiveHostPairFibre (blockSystem cfg)
          (circleTrace cfg Gamma.1) E).card = 2)
    (P : GeometricBlock cfg)
    (hPtrace : (geometricBlockSupport cfg P ∩
      circleTrace cfg Gamma.1).card = 1)
    (hout : 3 ≤ (geometricBlockSupport cfg P \
      circleTrace cfg Gamma.1).card) :
    A ⊆ geometricBlockSupport cfg P ∨
      B ⊆ geometricBlockSupport cfg P := by
  classical
  by_cases hAP : A ⊆ geometricBlockSupport cfg P
  · exact Or.inl hAP
  by_cases hBP : B ⊆ geometricBlockSupport cfg P
  · exact Or.inr hBP
  exfalso
  have hthree : 2 < (geometricBlockSupport cfg P \
      circleTrace cfg Gamma.1).card := by omega
  obtain ⟨x, hx, y, hy, z, hz, hxy, hxz, hyz⟩ :=
    Finset.two_lt_card.mp hthree
  have pair_ne (E : Finset α)
      (hE : E ⊆ geometricBlockSupport cfg P) : E ≠ A ∧ E ≠ B := by
    constructor
    · intro hEq
      exact hAP (by simpa [hEq] using hE)
    · intro hEq
      exact hBP (by simpa [hEq] using hE)
  have hxySub : ({x, y} : Finset α) ⊆ geometricBlockSupport cfg P := by
    intro q hq
    simp only [Finset.mem_insert, Finset.mem_singleton] at hq
    rcases hq with rfl | rfl
    · exact (Finset.mem_sdiff.mp hx).1
    · exact (Finset.mem_sdiff.mp hy).1
  have hxzSub : ({x, z} : Finset α) ⊆ geometricBlockSupport cfg P := by
    intro q hq
    simp only [Finset.mem_insert, Finset.mem_singleton] at hq
    rcases hq with rfl | rfl
    · exact (Finset.mem_sdiff.mp hx).1
    · exact (Finset.mem_sdiff.mp hz).1
  have hyzSub : ({y, z} : Finset α) ⊆ geometricBlockSupport cfg P := by
    intro q hq
    simp only [Finset.mem_insert, Finset.mem_singleton] at hq
    rcases hq with rfl | rfl
    · exact (Finset.mem_sdiff.mp hy).1
    · exact (Finset.mem_sdiff.mp hz).1
  apply elevenFive_one_trace_three_outsiders_of_pairwise_double_absurd
    cfg Gamma hD P hPtrace hx hy hz hxy hxz hyz
  · exact hfull {x, y}
      (elevenFive_h28_pair_mem_outsidePairs _
        (Finset.mem_sdiff.mp hx).2 (Finset.mem_sdiff.mp hy).2 hxy)
      (pair_ne {x, y} hxySub).1 (pair_ne {x, y} hxySub).2
  · exact hfull {x, z}
      (elevenFive_h28_pair_mem_outsidePairs _
        (Finset.mem_sdiff.mp hx).2 (Finset.mem_sdiff.mp hz).2 hxz)
      (pair_ne {x, z} hxzSub).1 (pair_ne {x, z} hxzSub).2
  · exact hfull {y, z}
      (elevenFive_h28_pair_mem_outsidePairs _
        (Finset.mem_sdiff.mp hy).2 (Finset.mem_sdiff.mp hz).2 hyz)
      (pair_ne {y, z} hyzSub).1 (pair_ne {y, z} hyzSub).2

/-- Configuration-level form of the exact H28 fibre-defect dichotomy. -/
theorem elevenFive_c39_h28_hostPairFibre_defect_profile
    {α : Type u} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (Gamma : DeterminedCircle cfg)
    (hpoint : Fintype.card α = 11)
    (hD : (circleTrace cfg Gamma.1).card = 5)
    (hhost : elevenFiveHostWeight (blockSystem cfg)
      (circleTrace cfg Gamma.1) = 28) :
    (∃ A ∈ (Finset.univ \ circleTrace cfg Gamma.1).powersetCard 2,
        (elevenFiveHostPairFibre (blockSystem cfg)
          (circleTrace cfg Gamma.1) A).card = 0 ∧
        ∀ B ∈ (Finset.univ \ circleTrace cfg Gamma.1).powersetCard 2,
          B ≠ A →
            (elevenFiveHostPairFibre (blockSystem cfg)
              (circleTrace cfg Gamma.1) B).card = 2) ∨
      (∃ A ∈ (Finset.univ \ circleTrace cfg Gamma.1).powersetCard 2,
        ∃ B ∈ (Finset.univ \ circleTrace cfg Gamma.1).powersetCard 2,
          A ≠ B ∧
          (elevenFiveHostPairFibre (blockSystem cfg)
            (circleTrace cfg Gamma.1) A).card = 1 ∧
          (elevenFiveHostPairFibre (blockSystem cfg)
            (circleTrace cfg Gamma.1) B).card = 1 ∧
          ∀ C ∈ (Finset.univ \ circleTrace cfg Gamma.1).powersetCard 2,
            C ≠ A → C ≠ B →
              (elevenFiveHostPairFibre (blockSystem cfg)
                (circleTrace cfg Gamma.1) C).card = 2) := by
  exact elevenFiveHostPairFibre_defect_profile_of_hostWeight_eq_twenty_eight
    (blockSystem cfg) (circleTrace cfg Gamma.1) hpoint hD hhost

/-- The C39 global rows determine the weighted size-four/five count.  This
tiny arithmetic lemma keeps Presburger normalization independent of block
systems and configuration data. -/
private theorem elevenFive_c39_h28_globalWeight_arithmetic
    {b3 b4 b5 : Nat}
    (htriple : b3 + 4 * b4 + 10 * b5 = 165)
    (htotal : b3 + b4 + b5 = 51) :
    b4 + 3 * b5 = 38 := by
  omega

/-- Structural wrapper for the C39 weighted size-four/five count. -/
private theorem elevenFive_c39_h28_globalWeight_eq_thirty_eight
    {Point : Type u} {Block : Type*} [Fintype Point] [Fintype Block]
    [DecidableEq Point]
    (S : BlockSystem Point Block)
    (hglobal : ElevenFiveGlobalRows S)
    (hC : S.totalCircleCount = 39)
    (hL : elevenFiveLineTotal S = 12) :
    S.blockCount 4 + 3 * S.blockCount 5 = 38 := by
  have htriple := hglobal.tripleRow
  have htotal := hglobal.blockTotal
  rw [hC, hL] at htotal
  exact elevenFive_c39_h28_globalWeight_arithmetic htriple htotal

/-- Pure arithmetic core of the H28 signed front.  Keeping all seven fibre
counts abstract prevents `omega` from normalizing their large definitions. -/
private theorem elevenFive_c39_h28_front_arithmetic
    {weight host a04 a13 a22 a05 a14 a23 q : Nat}
    (hglobal : weight = 38)
    (hweight : weight =
      a04 + a13 + a22 + 3 * a05 + 3 * a14 + 3 * a23 + 3)
    (hhostValue : host = 28)
    (hhostRow : host = a22 + 3 * a23)
    (hq : q = a04 + 3 * a05) :
    a13 + 3 * a14 + q = 7 := by
  omega

/-- The signed size-four/five row at H28, without making either defect
case or any geometric assumption. -/
theorem elevenFive_c39_h28_front_equation
    {α : Type u} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (hcap : BlockSizeCap (blockSystem cfg) 5)
    (hglobal : ElevenFiveGlobalRows (blockSystem cfg))
    (hC : (blockSystem cfg).totalCircleCount = 39)
    (hL : elevenFiveLineTotal (blockSystem cfg) = 12)
    (Gamma : DeterminedCircle cfg)
    (hD : (circleTrace cfg Gamma.1).card = 5)
    (hhost : elevenFiveHostWeight (blockSystem cfg)
      (circleTrace cfg Gamma.1) = 28) :
    elevenFiveRelativeCount (blockSystem cfg) (circleTrace cfg Gamma.1) 1 3 +
        3 * elevenFiveRelativeCount (blockSystem cfg)
          (circleTrace cfg Gamma.1) 1 4 +
      elevenFiveOutsideRichWeight (blockSystem cfg)
        (circleTrace cfg Gamma.1) = 7 := by
  classical
  let S := blockSystem cfg
  let D := circleTrace cfg Gamma.1
  let b : GeometricBlock cfg := Sum.inr Gamma
  change elevenFiveRelativeCount S D 1 3 +
      3 * elevenFiveRelativeCount S D 1 4 +
        elevenFiveOutsideRichWeight S D = 7
  have hb : b ∈ S.blocksOfSize 5 := by
    apply S.mem_blocksOfSize.mpr
    change (circleTrace cfg Gamma.1).card = 5
    exact hD
  have hDb : S.support b = D := by
    rfl
  have hweightD := elevenFive_c39_relative_size_weight_row S b hb hcap
  rw [hDb] at hweightD
  have hhostRow :=
    elevenFiveHostWeight_eq_relativeCount22_add_three_mul_relativeCount23
      S D hcap
  have hglobalWeight :=
    elevenFive_c39_h28_globalWeight_eq_thirty_eight S hglobal hC hL
  have hq :=
    elevenFiveOutsideRichWeight_eq_relativeCount_zero_four_add_three_mul_zero_five
      S D
  have hhost' : elevenFiveHostWeight S D = 28 := by
    exact hhost
  exact elevenFive_c39_h28_front_arithmetic
    hglobalWeight hweightD hhost' hhostRow hq

/-- The high-host and universal host-cap routers leave only the interval
`28 ≤ H ≤ 30` for their selected proper five-circle. -/
theorem elevenFive_c39_l12_exists_properFiveCircle_host_between_twenty_eight_thirty
    {α : Type u} [Fintype α] [DecidableEq α]
    (Mel : RealPlaneMelchiorPrinciple.{u})
    (Langer : RealPlaneLangerPrinciple.{u})
    (EvenArr : RealPlaneEvenArrangementPrinciple.{u})
    (Cross : RealPlaneRadicalAxisCrossBlockPrinciple.{u})
    (Kelly : RealPlaneKellyMoserPrinciple.{u})
    (U17 : RealPlaneSixCircleU17Principle.{u})
    (TenGeometry : RealPlaneTenFiveGeometry.{u})
    (cfg : Configuration α) (hadm : Admissible cfg)
    (hcard : Fintype.card α = 11)
    (hcap : BlockSizeCap (blockSystem cfg) 5)
    (hCcount : Erdos506.V4.circleCount cfg = 39)
    (hL : elevenFiveLineTotal (blockSystem cfg) = 12) :
    ∃ delta : DeterminedCircle cfg,
      (circleTrace cfg delta.1).card = 5 ∧
        28 ≤ elevenFiveHostWeight (blockSystem cfg)
          (circleTrace cfg delta.1) ∧
        elevenFiveHostWeight (blockSystem cfg)
          (circleTrace cfg delta.1) ≤ 30 := by
  obtain ⟨delta, hdelta, hlower⟩ :=
    elevenFive_c39_l12_exists_properFiveCircle_host_ge_twenty_eight
      Mel Langer EvenArr Cross Kelly U17 TenGeometry cfg hadm hcard hcap
        hCcount hL
  exact ⟨delta, hdelta, hlower,
    elevenFiveHostWeight_le_thirty (blockSystem cfg)
      (circleTrace cfg delta.1) hcard hdelta⟩

/-- Minimal missing K2.4 seam.  It says precisely that the actual H28
zero-fibre residual with no `(1,4)` page is impossible.  A future proof must
construct the five homogeneous conic representatives and four actual
centres, verify the golden-axis incidences and omitted-colour concurrency,
and then invoke `fiveConic_goldenAxis_tangentSeparation_absurd`.

This is a definition of a proposition, not a new principle or axiom. -/
def ElevenFiveC39H28GoldenAxisActualAdapter
    {α : Type u} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) : Prop :=
  ∀ (Gamma : DeterminedCircle cfg)
    (_hpoint : Fintype.card α = 11)
    (_hD : (circleTrace cfg Gamma.1).card = 5)
    (_hhost : elevenFiveHostWeight (blockSystem cfg)
      (circleTrace cfg Gamma.1) = 28),
    elevenFiveRelativeCount (blockSystem cfg)
      (circleTrace cfg Gamma.1) 1 4 = 0 → False

/-- Conditional local closure exposed at exactly the missing adapter seam:
under the actual K2.4 adapter, an H28 circle must have a singleton
five-block neighbour. -/
theorem elevenFive_c39_h28_relativeCount_one_four_pos_of_goldenAxisActualAdapter
    {α : Type u} [Fintype α] [DecidableEq α]
    (cfg : Configuration α)
    (hgolden : ElevenFiveC39H28GoldenAxisActualAdapter cfg)
    (Gamma : DeterminedCircle cfg)
    (hpoint : Fintype.card α = 11)
    (hD : (circleTrace cfg Gamma.1).card = 5)
    (hhost : elevenFiveHostWeight (blockSystem cfg)
      (circleTrace cfg Gamma.1) = 28) :
    0 < elevenFiveRelativeCount (blockSystem cfg)
      (circleTrace cfg Gamma.1) 1 4 := by
  by_contra hnot
  have hzero : elevenFiveRelativeCount (blockSystem cfg)
      (circleTrace cfg Gamma.1) 1 4 = 0 := by omega
  exact hgolden Gamma hpoint hD hhost hzero

end Erdos506.V1
