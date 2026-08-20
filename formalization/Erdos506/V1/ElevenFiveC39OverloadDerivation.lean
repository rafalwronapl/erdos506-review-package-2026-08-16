import Erdos506.V1.ElevenFiveHostOverload

/-!
# The combinatorial C39 host-load interface

The C39 router writes the host load of a selected five-set as
`A22 + 3 * A23`.  This file materializes that identity directly in the
tagged block system.  It is intentionally only the finite interface: the
geometric maximum-host router from the paper is not encoded by the current
`RealPlaneElevenFiveGeometry` hypotheses.
-/

namespace Erdos506.V1

open Erdos506.Block
open Erdos506.Block.BlockSystem
open Erdos506.Incidence
open Erdos506.V4
open scoped BigOperators

universe u v

/-- The untagged relative block census used by the C39 front.  Its value is
the manuscript's `A_{g,x}`: blocks having `g` selected and `x` outside
labels. -/
noncomputable def elevenFiveRelativeCount
    {Point : Type u} {Block : Type v} [Fintype Point] [Fintype Block]
    [DecidableEq Point]
    (S : BlockSystem Point Block) (D : Finset Point) (g x : Nat) : Nat :=
  (Finset.univ.filter fun b =>
    (S.support b ∩ D).card = g /\ (S.support b \ D).card = x).card

/-- Under the five-block cap, the host weight of `D` is exactly the C39
quantity `A22 + 3*A23`.  Blocks with a two-point trace have at most three
outside labels; two and three outside labels contribute respectively one
and three outsider pairs. -/
theorem elevenFiveHostWeight_eq_relativeCount22_add_three_mul_relativeCount23
    {Point : Type u} {Block : Type v} [Fintype Point] [Fintype Block]
    [DecidableEq Point]
    (S : BlockSystem Point Block) (D : Finset Point)
    (hcap : BlockSizeCap S 5) :
    elevenFiveHostWeight S D =
      elevenFiveRelativeCount S D 2 2 +
        3 * elevenFiveRelativeCount S D 2 3 := by
  classical
  have hterm (b : Block) (hinside : (S.support b ∩ D).card = 2) :
      Nat.choose (S.support b \ D).card 2 =
        (if (S.support b \ D).card = 2 then 1 else 0) +
          3 * (if (S.support b \ D).card = 3 then 1 else 0) := by
    have hsplit := Finset.card_inter_add_card_sdiff (S.support b) D
    by_cases hsmall : (S.support b).card <= 2
    · have hout : (S.support b \ D).card = 0 := by omega
      simp [hout]
    · have hthree : 3 <= (S.support b).card := by omega
      have hsize := hcap b hthree
      have hout : (S.support b \ D).card <= 3 := by omega
      interval_cases (S.support b \ D).card <;>
        norm_num [Nat.choose] at *
  unfold elevenFiveHostWeight elevenFiveHostFamily elevenFiveRelativeCount
  rw [Finset.sum_filter]
  simp only [Finset.card_filter]
  change
    (∑ b : Block,
      if (S.support b ∩ D).card = 2 then
        Nat.choose (S.support b \ D).card 2
      else 0) =
      (∑ b : Block,
        if (S.support b ∩ D).card = 2 /\ (S.support b \ D).card = 2 then
          1 else 0) +
        3 * (∑ b : Block,
          if (S.support b ∩ D).card = 2 /\ (S.support b \ D).card = 3 then
            1 else 0)
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro b _hb
  by_cases hinside : (S.support b ∩ D).card = 2
  · simp [hinside, hterm b hinside]
  · simp [hinside]

/-- The overload conclusion required by the C39 geometry slot is impossible
once a concrete selected five-circle is supplied.  This is the reusable
closing half of the C39 route. -/
theorem elevenFive_c39_overload_witness_absurd
    {α : Type u} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (hcard : Fintype.card α = 11)
    (delta : DeterminedCircle cfg)
    (hdelta : (circleTrace cfg delta.1).card = 5)
    (hover : 31 <= elevenFiveHostWeight (blockSystem cfg)
      (circleTrace cfg delta.1)) : False := by
  exact elevenFive_hostOverload_absurd
    (Point := α) (Block := GeometricBlock cfg)
    (blockSystem cfg) (circleTrace cfg delta.1) hcard hdelta hover

/-! ## The `C = 39`, `L = 12` low-host moment -/

/-- The host-load sum taken over the actual size-five blocks, line-tagged
and circle-tagged alike.  Keeping the possible five-line in this finite
sum is what makes the universal capacity `30` directly applicable. -/
noncomputable def elevenFiveFiveBlockHostTotal
    {Point : Type u} {Block : Type v} [Fintype Point] [Fintype Block]
    [DecidableEq Point]
    (S : BlockSystem Point Block) : Nat :=
  ∑ b ∈ S.blocksOfSize 5, elevenFiveHostWeight S (S.support b)

/-- The paper's local `q` term, written without choosing a distinguished
circle: four-blocks and five-blocks disjoint from the selected five-block,
with their respective weights one and three. -/
noncomputable def elevenFiveOutsideRichWeight
    {Point : Type u} {Block : Type v} [Fintype Point] [Fintype Block]
    [DecidableEq Point]
    (S : BlockSystem Point Block) (D : Finset Point) : Nat :=
  ((S.blocksOfSize 4).filter fun b =>
    (S.support b ∩ D).card = 0).card +
    3 * ((S.blocksOfSize 5).filter fun b =>
      (S.support b ∩ D).card = 0).card

/-- Sum of the genuine local `q` terms over the actual size-five blocks. -/
noncomputable def elevenFiveFiveBlockOutsideRichTotal
    {Point : Type u} {Block : Type v} [Fintype Point] [Fintype Block]
    [DecidableEq Point]
    (S : BlockSystem Point Block) : Nat :=
  ∑ b ∈ S.blocksOfSize 5,
    elevenFiveOutsideRichWeight S (S.support b)

/-- At the `C = 39` face the only allowed three-degrees are six and nine.
This indicator records the latter alternative without introducing a new
geometric hypothesis. -/
noncomputable def elevenFiveC39HighIndicator
    {Point : Type u} {Block : Type v} [Fintype Point] [Fintype Block]
    [DecidableEq Point]
    (S : BlockSystem Point Block) (p : Point) : Nat :=
  if S.blockDegree 3 p = 9 then 1 else 0

/-- Number of high (`d₃ = 9`) points in the C39 moment. -/
noncomputable def elevenFiveC39HighCount
    {Point : Type u} {Block : Type v} [Fintype Point] [Fintype Block]
    [DecidableEq Point]
    (S : BlockSystem Point Block) : Nat :=
  ∑ p : Point, elevenFiveC39HighIndicator S p

/-- Five-block incidences carried by high points.  This is the manuscript's
`I_ω`, retained on the natural-number side of the moment identity. -/
noncomputable def elevenFiveC39HighFiveIncidence
    {Point : Type u} {Block : Type v} [Fintype Point] [Fintype Block]
    [DecidableEq Point]
    (S : BlockSystem Point Block) : Nat :=
  ∑ p : Point,
    elevenFiveC39HighIndicator S p * S.blockDegree 5 p

private theorem elevenFiveRelativeCount22_eq_fourIntersectionTwo
    {Point : Type u} {Block : Type v} [Fintype Point] [Fintype Block]
    [DecidableEq Point]
    (S : BlockSystem Point Block) (D : Finset Point) :
    elevenFiveRelativeCount S D 2 2 =
      ((S.blocksOfSize 4).filter fun b =>
        (S.support b ∩ D).card = 2).card := by
  classical
  unfold elevenFiveRelativeCount
  apply congrArg Finset.card
  ext b
  simp only [Finset.mem_filter, Finset.mem_univ, true_and,
    S.mem_blocksOfSize]
  constructor
  · rintro ⟨hinside, houtside⟩
    have hsplit := Finset.card_inter_add_card_sdiff (S.support b) D
    exact ⟨by omega, hinside⟩
  · rintro ⟨hsize, hinside⟩
    have hsplit := Finset.card_inter_add_card_sdiff (S.support b) D
    exact ⟨hinside, by omega⟩

private theorem elevenFiveRelativeCount23_eq_fiveIntersectionTwo
    {Point : Type u} {Block : Type v} [Fintype Point] [Fintype Block]
    [DecidableEq Point]
    (S : BlockSystem Point Block) (D : Finset Point) :
    elevenFiveRelativeCount S D 2 3 =
      ((S.blocksOfSize 5).filter fun b =>
        (S.support b ∩ D).card = 2).card := by
  classical
  unfold elevenFiveRelativeCount
  apply congrArg Finset.card
  ext b
  simp only [Finset.mem_filter, Finset.mem_univ, true_and,
    S.mem_blocksOfSize]
  constructor
  · rintro ⟨hinside, houtside⟩
    have hsplit := Finset.card_inter_add_card_sdiff (S.support b) D
    exact ⟨by omega, hinside⟩
  · rintro ⟨hsize, hinside⟩
    have hsplit := Finset.card_inter_add_card_sdiff (S.support b) D
    exact ⟨hinside, by omega⟩

/-- The host load is the `A₂₂ + 3 A₂₃` sum written directly as counts of
four- and five-blocks meeting the selected set twice. -/
private theorem elevenFiveHostWeight_eq_fourIntersectionTwo_add_three_mul_fiveIntersectionTwo
    {Point : Type u} {Block : Type v} [Fintype Point] [Fintype Block]
    [DecidableEq Point]
    (S : BlockSystem Point Block) (D : Finset Point)
    (hcap : BlockSizeCap S 5) :
    elevenFiveHostWeight S D =
      ((S.blocksOfSize 4).filter fun b =>
        (S.support b ∩ D).card = 2).card +
        3 * ((S.blocksOfSize 5).filter fun b =>
          (S.support b ∩ D).card = 2).card := by
  rw [elevenFiveHostWeight_eq_relativeCount22_add_three_mul_relativeCount23
    S D hcap,
    elevenFiveRelativeCount22_eq_fourIntersectionTwo,
    elevenFiveRelativeCount23_eq_fiveIntersectionTwo]

private theorem elevenFive_fourIncidence_le_blockCount_add_intersectionTwo
    {Point : Type u} {Block : Type v} [Fintype Point] [Fintype Block]
    [DecidableEq Point]
    (S : BlockSystem Point Block) (b : Block)
    (hb : b ∈ S.blocksOfSize 5) :
    (∑ p ∈ S.support b, S.blockDegree 4 p) <=
      S.blockCount 4 +
        ((S.blocksOfSize 4).filter fun c =>
          (S.support c ∩ S.support b).card = 2).card := by
  classical
  have hinc := S.sum_degreeIn_over (S.blocksOfSize 4) (S.support b)
  change (∑ p ∈ S.support b,
      S.degreeIn (S.blocksOfSize 4) p) <= _
  rw [hinc]
  have hpoint (c : Block) (hc : c ∈ S.blocksOfSize 4) :
      (S.support b ∩ S.support c).card <=
        1 + if (S.support b ∩ S.support c).card = 2 then 1 else 0 := by
    have hcb : c ≠ b := by
      intro hcb
      subst c
      have hfour := S.mem_blocksOfSize.mp hc
      have hfive := S.mem_blocksOfSize.mp hb
      omega
    have hbc : b ≠ c := Ne.symm hcb
    have hinter := S.distinct_block_inter_card_lt_three hbc
    have hle : (S.support b ∩ S.support c).card <= 2 := by
      omega
    by_cases htwo : (S.support b ∩ S.support c).card = 2
    · simpa [htwo] using hle
    · simp [htwo]
      omega
  calc
    (∑ c ∈ S.blocksOfSize 4, (S.support b ∩ S.support c).card) <=
        ∑ c ∈ S.blocksOfSize 4,
          (1 + if (S.support b ∩ S.support c).card = 2 then 1 else 0) := by
      exact Finset.sum_le_sum fun c hc => hpoint c hc
    _ = S.blockCount 4 +
        ((S.blocksOfSize 4).filter fun c =>
          (S.support c ∩ S.support b).card = 2).card := by
      have hindicator :
          (∑ c ∈ S.blocksOfSize 4,
            if (S.support b ∩ S.support c).card = 2 then 1 else 0) =
            ((S.blocksOfSize 4).filter fun c =>
              (S.support c ∩ S.support b).card = 2).card := by
        rw [← Finset.sum_filter]
        simp [Finset.inter_comm]
      rw [Finset.sum_add_distrib, hindicator]
      simp [BlockSystem.blockCount, Nat.add_comm]

private theorem elevenFive_fiveIncidence_le_three_mul_blockCount_add_intersectionTwo
    {Point : Type u} {Block : Type v} [Fintype Point] [Fintype Block]
    [DecidableEq Point]
    (S : BlockSystem Point Block) (b : Block)
    (hb : b ∈ S.blocksOfSize 5) :
    3 * (∑ p ∈ S.support b, S.blockDegree 5 p) <=
      3 * S.blockCount 5 +
        3 * ((S.blocksOfSize 5).filter fun c =>
          (S.support c ∩ S.support b).card = 2).card + 12 := by
  classical
  have hinc := S.sum_degreeIn_over (S.blocksOfSize 5) (S.support b)
  change 3 * (∑ p ∈ S.support b,
      S.degreeIn (S.blocksOfSize 5) p) <= _
  rw [hinc]
  have hpoint (c : Block) (hc : c ∈ S.blocksOfSize 5) :
      3 * (S.support b ∩ S.support c).card <=
        3 + 3 * (if (S.support b ∩ S.support c).card = 2 then 1 else 0) +
          12 * (if c = b then 1 else 0) := by
    by_cases hcb : c = b
    · subst c
      have hfive := S.mem_blocksOfSize.mp hb
      simp [hfive]
    · have hbc : b ≠ c := Ne.symm hcb
      have hinter := S.distinct_block_inter_card_lt_three hbc
      have hle : (S.support b ∩ S.support c).card <= 2 := by
        omega
      by_cases htwo : (S.support b ∩ S.support c).card = 2
      · simp [hcb, htwo]
      · simp [hcb, htwo]
        omega
  have htwoIndicator :
      (∑ c ∈ S.blocksOfSize 5,
        if (S.support b ∩ S.support c).card = 2 then 1 else 0) =
        ((S.blocksOfSize 5).filter fun c =>
          (S.support c ∩ S.support b).card = 2).card := by
    rw [← Finset.sum_filter]
    simp [Finset.inter_comm]
  have hselfIndicator :
      (∑ c ∈ S.blocksOfSize 5, if c = b then 1 else 0) = 1 := by
    rw [← Finset.sum_filter]
    have hfilter : (S.blocksOfSize 5).filter (fun c => c = b) = {b} := by
      ext c
      constructor
      · intro hc
        have hcb := (Finset.mem_filter.mp hc).2
        subst c
        simp
      · intro hc
        have hcb : c = b := Finset.mem_singleton.mp hc
        subst c
        exact Finset.mem_filter.mpr ⟨hb, rfl⟩
    rw [hfilter]
    simp
  calc
    3 * (∑ c ∈ S.blocksOfSize 5,
      (S.support b ∩ S.support c).card) =
        ∑ c ∈ S.blocksOfSize 5,
          3 * (S.support b ∩ S.support c).card := by
      rw [Finset.mul_sum]
    _ <= ∑ c ∈ S.blocksOfSize 5,
        (3 + 3 * (if (S.support b ∩ S.support c).card = 2 then 1 else 0) +
          12 * (if c = b then 1 else 0)) := by
      exact Finset.sum_le_sum fun c hc => hpoint c hc
    _ = (∑ c ∈ S.blocksOfSize 5, 3) +
        (∑ c ∈ S.blocksOfSize 5,
          3 * (if (S.support b ∩ S.support c).card = 2 then 1 else 0)) +
          ∑ c ∈ S.blocksOfSize 5, 12 * (if c = b then 1 else 0) := by
      simp only [Finset.sum_add_distrib]
    _ = 3 * S.blockCount 5 +
        3 * ((S.blocksOfSize 5).filter fun c =>
          (S.support c ∩ S.support b).card = 2).card + 12 := by
      have hconstant : (∑ c ∈ S.blocksOfSize 5, 3) =
          3 * S.blockCount 5 := by
        simp [BlockSystem.blockCount, Nat.mul_comm]
      have htwo :
          (∑ c ∈ S.blocksOfSize 5,
            3 * (if (S.support b ∩ S.support c).card = 2 then 1 else 0)) =
            3 * ((S.blocksOfSize 5).filter fun c =>
              (S.support c ∩ S.support b).card = 2).card := by
        rw [← Finset.mul_sum, htwoIndicator]
      have hself :
          (∑ c ∈ S.blocksOfSize 5, 12 * (if c = b then 1 else 0)) = 12 := by
        rw [← Finset.mul_sum, hselfIndicator]
        simp
      rw [hconstant, htwo, hself]

/-- Exact four-block incidence accounting on a selected five-block.  The
zero-intersection term is the four-block contribution to the manuscript's
`q`; this equality is the sharpened form of the preceding capacity bound. -/
private theorem elevenFive_fourIncidence_add_zeroIntersection_eq_blockCount_add_intersectionTwo
    {Point : Type u} {Block : Type v} [Fintype Point] [Fintype Block]
    [DecidableEq Point]
    (S : BlockSystem Point Block) (b : Block)
    (hb : b ∈ S.blocksOfSize 5) :
    (∑ p ∈ S.support b, S.blockDegree 4 p) +
      ((S.blocksOfSize 4).filter fun c =>
        (S.support c ∩ S.support b).card = 0).card =
      S.blockCount 4 +
        ((S.blocksOfSize 4).filter fun c =>
          (S.support c ∩ S.support b).card = 2).card := by
  classical
  have hinc := S.sum_degreeIn_over (S.blocksOfSize 4) (S.support b)
  change (∑ p ∈ S.support b,
      S.degreeIn (S.blocksOfSize 4) p) + _ = _
  rw [hinc]
  have hpoint (c : Block) (hc : c ∈ S.blocksOfSize 4) :
      (S.support b ∩ S.support c).card +
          (if (S.support b ∩ S.support c).card = 0 then 1 else 0) =
        1 + (if (S.support b ∩ S.support c).card = 2 then 1 else 0) := by
    have hcb : c ≠ b := by
      intro hcb
      subst c
      have hfour := S.mem_blocksOfSize.mp hc
      have hfive := S.mem_blocksOfSize.mp hb
      omega
    have hbc : b ≠ c := Ne.symm hcb
    have hinter := S.distinct_block_inter_card_lt_three hbc
    have hle : (S.support b ∩ S.support c).card <= 2 := by omega
    interval_cases hcard : (S.support b ∩ S.support c).card <;>
      norm_num [hcard]
  have hzero :
      (∑ c ∈ S.blocksOfSize 4,
        if (S.support b ∩ S.support c).card = 0 then 1 else 0) =
        ((S.blocksOfSize 4).filter fun c =>
          (S.support c ∩ S.support b).card = 0).card := by
    rw [← Finset.sum_filter]
    simp [Finset.inter_comm]
  have htwo :
      (∑ c ∈ S.blocksOfSize 4,
        if (S.support b ∩ S.support c).card = 2 then 1 else 0) =
        ((S.blocksOfSize 4).filter fun c =>
          (S.support c ∩ S.support b).card = 2).card := by
    rw [← Finset.sum_filter]
    simp [Finset.inter_comm]
  calc
    (∑ c ∈ S.blocksOfSize 4, (S.support b ∩ S.support c).card) +
        ((S.blocksOfSize 4).filter fun c =>
          (S.support c ∩ S.support b).card = 0).card =
        (∑ c ∈ S.blocksOfSize 4, (S.support b ∩ S.support c).card) +
          ∑ c ∈ S.blocksOfSize 4,
            if (S.support b ∩ S.support c).card = 0 then 1 else 0 := by
      rw [hzero]
    _ = ∑ c ∈ S.blocksOfSize 4,
        ((S.support b ∩ S.support c).card +
          if (S.support b ∩ S.support c).card = 0 then 1 else 0) := by
      rw [Finset.sum_add_distrib]
    _ = ∑ c ∈ S.blocksOfSize 4,
        (1 + if (S.support b ∩ S.support c).card = 2 then 1 else 0) := by
      apply Finset.sum_congr rfl
      intro c hc
      exact hpoint c hc
    _ = (∑ c ∈ S.blocksOfSize 4, 1) +
        ∑ c ∈ S.blocksOfSize 4,
          if (S.support b ∩ S.support c).card = 2 then 1 else 0 := by
      rw [Finset.sum_add_distrib]
    _ = S.blockCount 4 +
        ((S.blocksOfSize 4).filter fun c =>
          (S.support c ∩ S.support b).card = 2).card := by
      rw [htwo]
      simp [BlockSystem.blockCount]

/-- Exact five-block incidence accounting on a selected five-block.  The
additive twelve records its self-intersection of size five. -/
private theorem elevenFive_fiveIncidence_add_zeroIntersection_eq_three_mul_blockCount_add_intersectionTwo
    {Point : Type u} {Block : Type v} [Fintype Point] [Fintype Block]
    [DecidableEq Point]
    (S : BlockSystem Point Block) (b : Block)
    (hb : b ∈ S.blocksOfSize 5) :
    3 * (∑ p ∈ S.support b, S.blockDegree 5 p) +
      3 * ((S.blocksOfSize 5).filter fun c =>
        (S.support c ∩ S.support b).card = 0).card =
      3 * S.blockCount 5 +
        3 * ((S.blocksOfSize 5).filter fun c =>
          (S.support c ∩ S.support b).card = 2).card + 12 := by
  classical
  have hinc := S.sum_degreeIn_over (S.blocksOfSize 5) (S.support b)
  change 3 * (∑ p ∈ S.support b,
      S.degreeIn (S.blocksOfSize 5) p) + _ = _
  rw [hinc]
  have hpoint (c : Block) (hc : c ∈ S.blocksOfSize 5) :
      3 * (S.support b ∩ S.support c).card +
          3 * (if (S.support b ∩ S.support c).card = 0 then 1 else 0) =
        3 + 3 * (if (S.support b ∩ S.support c).card = 2 then 1 else 0) +
          12 * (if c = b then 1 else 0) := by
    by_cases hcb : c = b
    · subst c
      have hfive := S.mem_blocksOfSize.mp hb
      simp [hfive]
    · have hbc : b ≠ c := Ne.symm hcb
      have hinter := S.distinct_block_inter_card_lt_three hbc
      have hle : (S.support b ∩ S.support c).card <= 2 := by omega
      interval_cases hcard : (S.support b ∩ S.support c).card <;>
        norm_num [hcard, hcb]
  have hzero :
      (∑ c ∈ S.blocksOfSize 5,
        if (S.support b ∩ S.support c).card = 0 then 1 else 0) =
        ((S.blocksOfSize 5).filter fun c =>
          (S.support c ∩ S.support b).card = 0).card := by
    rw [← Finset.sum_filter]
    simp [Finset.inter_comm]
  have htwo :
      (∑ c ∈ S.blocksOfSize 5,
        if (S.support b ∩ S.support c).card = 2 then 1 else 0) =
        ((S.blocksOfSize 5).filter fun c =>
          (S.support c ∩ S.support b).card = 2).card := by
    rw [← Finset.sum_filter]
    simp [Finset.inter_comm]
  have hself :
      (∑ c ∈ S.blocksOfSize 5, if c = b then 1 else 0) = 1 := by
    rw [← Finset.sum_filter]
    have hfilter : (S.blocksOfSize 5).filter (fun c => c = b) = {b} := by
      ext c
      constructor
      · intro hc
        have hcb := (Finset.mem_filter.mp hc).2
        subst c
        simp
      · intro hc
        have hcb : c = b := Finset.mem_singleton.mp hc
        subst c
        exact Finset.mem_filter.mpr ⟨hb, rfl⟩
    rw [hfilter]
    simp
  calc
    3 * (∑ c ∈ S.blocksOfSize 5,
      (S.support b ∩ S.support c).card) +
        3 * ((S.blocksOfSize 5).filter fun c =>
          (S.support c ∩ S.support b).card = 0).card =
        3 * (∑ c ∈ S.blocksOfSize 5,
          (S.support b ∩ S.support c).card) +
          3 * (∑ c ∈ S.blocksOfSize 5,
            if (S.support b ∩ S.support c).card = 0 then 1 else 0) := by
      rw [hzero]
    _ = ∑ c ∈ S.blocksOfSize 5,
        (3 * (S.support b ∩ S.support c).card +
          3 * (if (S.support b ∩ S.support c).card = 0 then 1 else 0)) := by
      simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
    _ = ∑ c ∈ S.blocksOfSize 5,
        (3 + 3 * (if (S.support b ∩ S.support c).card = 2 then 1 else 0) +
          12 * (if c = b then 1 else 0)) := by
      apply Finset.sum_congr rfl
      intro c hc
      exact hpoint c hc
    _ = (∑ c ∈ S.blocksOfSize 5, 3) +
        (∑ c ∈ S.blocksOfSize 5,
          3 * (if (S.support b ∩ S.support c).card = 2 then 1 else 0)) +
          ∑ c ∈ S.blocksOfSize 5, 12 * (if c = b then 1 else 0) := by
      simp only [Finset.sum_add_distrib]
    _ = 3 * S.blockCount 5 +
        3 * ((S.blocksOfSize 5).filter fun c =>
          (S.support c ∩ S.support b).card = 2).card + 12 := by
      have hconstant : (∑ c ∈ S.blocksOfSize 5, 3) =
          3 * S.blockCount 5 := by
        simp [BlockSystem.blockCount, Nat.mul_comm]
      have htwoScaled :
          (∑ c ∈ S.blocksOfSize 5,
            3 * (if (S.support b ∩ S.support c).card = 2 then 1 else 0)) =
            3 * ((S.blocksOfSize 5).filter fun c =>
              (S.support c ∩ S.support b).card = 2).card := by
        rw [← Finset.mul_sum, htwo]
      have hselfScaled :
          (∑ c ∈ S.blocksOfSize 5, 12 * (if c = b then 1 else 0)) = 12 := by
        rw [← Finset.mul_sum, hself]
        simp
      rw [hconstant, htwoScaled, hselfScaled]

/-- The exact local K1 accounting identity.  It uses only actual blocks:
the extra term is precisely the disjoint four- and five-block weight above. -/
theorem elevenFive_host_incidence_mass_add_outsideRich_eq
    {Point : Type u} {Block : Type v} [Fintype Point] [Fintype Block]
    [DecidableEq Point]
    (S : BlockSystem Point Block) (b : Block)
    (hb : b ∈ S.blocksOfSize 5) (hcap : BlockSizeCap S 5) :
    ((∑ p ∈ S.support b, S.blockDegree 4 p) +
      3 * (∑ p ∈ S.support b, S.blockDegree 5 p)) +
        elevenFiveOutsideRichWeight S (S.support b) =
      elevenFiveHostWeight S (S.support b) + S.blockCount 4 +
        3 * S.blockCount 5 + 12 := by
  have hfour :=
    elevenFive_fourIncidence_add_zeroIntersection_eq_blockCount_add_intersectionTwo
      S b hb
  have hfive :=
    elevenFive_fiveIncidence_add_zeroIntersection_eq_three_mul_blockCount_add_intersectionTwo
      S b hb
  have hhost :=
    elevenFiveHostWeight_eq_fourIntersectionTwo_add_three_mul_fiveIntersectionTwo
      S (S.support b) hcap
  unfold elevenFiveOutsideRichWeight
  omega

/-- A selected size-five block controls its local four/five incidence mass
by its host load.  This is the finite, tag-independent core of the rebased
host moment; the exceptional `12` is exactly the selected block itself. -/
theorem elevenFive_host_incidence_mass_le
    {Point : Type u} {Block : Type v} [Fintype Point] [Fintype Block]
    [DecidableEq Point]
    (S : BlockSystem Point Block) (b : Block)
    (hb : b ∈ S.blocksOfSize 5) (hcap : BlockSizeCap S 5) :
    (∑ p ∈ S.support b, S.blockDegree 4 p) +
      3 * (∑ p ∈ S.support b, S.blockDegree 5 p) <=
      elevenFiveHostWeight S (S.support b) + S.blockCount 4 +
        3 * S.blockCount 5 + 12 := by
  have hfour := elevenFive_fourIncidence_le_blockCount_add_intersectionTwo
    S b hb
  have hfive := elevenFive_fiveIncidence_le_three_mul_blockCount_add_intersectionTwo
    S b hb
  have hhost :=
    elevenFiveHostWeight_eq_fourIntersectionTwo_add_three_mul_fiveIntersectionTwo
      S (S.support b) hcap
  omega

private theorem elevenFive_sum_support_weight_eq
    {Point : Type u} {Block : Type v} [Fintype Point] [Fintype Block]
    [DecidableEq Point]
    (S : BlockSystem Point Block) (F : Finset Block) (f : Point → Nat) :
    (∑ b ∈ F, ∑ p ∈ S.support b, f p) =
      ∑ p : Point, f p * S.degreeIn F p := by
  classical
  calc
    (∑ b ∈ F, ∑ p ∈ S.support b, f p) =
        ∑ b ∈ F, ∑ p : Point,
          if p ∈ S.support b then f p else 0 := by
      apply Finset.sum_congr rfl
      intro b _hb
      rw [← Finset.sum_filter]
      simp
    _ = ∑ p : Point, ∑ b ∈ F,
        if p ∈ S.support b then f p else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ p : Point, f p * S.degreeIn F p := by
      apply Finset.sum_congr rfl
      intro p _hp
      rw [← Finset.sum_filter]
      simp [BlockSystem.degreeIn, Nat.mul_comm]

private theorem elevenFive_sum_fiveBlock_incidence
    {Point : Type u} {Block : Type v} [Fintype Point] [Fintype Block]
    [DecidableEq Point]
    (S : BlockSystem Point Block) (s : Nat) :
    (∑ b ∈ S.blocksOfSize 5,
      ∑ p ∈ S.support b, S.blockDegree s p) =
      ∑ p : Point, S.blockDegree 5 p * S.blockDegree s p := by
  simpa [BlockSystem.blockDegree, Nat.mul_comm] using
    elevenFive_sum_support_weight_eq S (S.blocksOfSize 5)
      (fun p => S.blockDegree s p)

private theorem elevenFive_fiveBlock_incidence_mass_sum_eq
    {Point : Type u} {Block : Type v} [Fintype Point] [Fintype Block]
    [DecidableEq Point]
    (S : BlockSystem Point Block) :
    (∑ b ∈ S.blocksOfSize 5,
      ((∑ p ∈ S.support b, S.blockDegree 4 p) +
        3 * (∑ p ∈ S.support b, S.blockDegree 5 p))) =
      (∑ p : Point,
        (S.blockDegree 4 p * S.blockDegree 5 p +
          3 * (S.blockDegree 5 p * S.blockDegree 5 p))) := by
  classical
  calc
    (∑ b ∈ S.blocksOfSize 5,
      ((∑ p ∈ S.support b, S.blockDegree 4 p) +
        3 * (∑ p ∈ S.support b, S.blockDegree 5 p))) =
        (∑ b ∈ S.blocksOfSize 5,
          ∑ p ∈ S.support b, S.blockDegree 4 p) +
          3 * (∑ b ∈ S.blocksOfSize 5,
            ∑ p ∈ S.support b, S.blockDegree 5 p) := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum]
    _ = (∑ p : Point,
        S.blockDegree 5 p * S.blockDegree 4 p) +
          3 * (∑ p : Point,
            S.blockDegree 5 p * S.blockDegree 5 p) := by
      rw [elevenFive_sum_fiveBlock_incidence S 4,
        elevenFive_sum_fiveBlock_incidence S 5]
    _ = ∑ p : Point,
        (S.blockDegree 4 p * S.blockDegree 5 p +
          3 * (S.blockDegree 5 p * S.blockDegree 5 p)) := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro p _hp
      ring

private theorem elevenFive_host_mass_sum_add_outsideRich_eq
    {Point : Type u} {Block : Type v} [Fintype Point] [Fintype Block]
    [DecidableEq Point]
    (S : BlockSystem Point Block) (hcap : BlockSizeCap S 5) :
    (∑ p : Point,
      (S.blockDegree 4 p * S.blockDegree 5 p +
        3 * (S.blockDegree 5 p * S.blockDegree 5 p))) +
      elevenFiveFiveBlockOutsideRichTotal S =
        elevenFiveFiveBlockHostTotal S + S.blockCount 5 *
          (S.blockCount 4 + 3 * S.blockCount 5 + 12) := by
  classical
  let K := S.blockCount 4 + 3 * S.blockCount 5 + 12
  have hsum :
      (∑ b ∈ S.blocksOfSize 5,
        (((∑ p ∈ S.support b, S.blockDegree 4 p) +
          3 * (∑ p ∈ S.support b, S.blockDegree 5 p)) +
          elevenFiveOutsideRichWeight S (S.support b))) =
        ∑ b ∈ S.blocksOfSize 5,
          (elevenFiveHostWeight S (S.support b) + K) := by
    apply Finset.sum_congr rfl
    intro b hb
    simpa [K, Nat.add_assoc] using
      elevenFive_host_incidence_mass_add_outsideRich_eq S b hb hcap
  have hleft :
      (∑ b ∈ S.blocksOfSize 5,
        (((∑ p ∈ S.support b, S.blockDegree 4 p) +
          3 * (∑ p ∈ S.support b, S.blockDegree 5 p)) +
          elevenFiveOutsideRichWeight S (S.support b))) =
        (∑ p : Point,
          (S.blockDegree 4 p * S.blockDegree 5 p +
            3 * (S.blockDegree 5 p * S.blockDegree 5 p))) +
          elevenFiveFiveBlockOutsideRichTotal S := by
    rw [Finset.sum_add_distrib,
      elevenFive_fiveBlock_incidence_mass_sum_eq]
    simp only [elevenFiveFiveBlockOutsideRichTotal]
  have hright :
      (∑ b ∈ S.blocksOfSize 5,
        (elevenFiveHostWeight S (S.support b) + K)) =
        elevenFiveFiveBlockHostTotal S + S.blockCount 5 * K := by
    rw [Finset.sum_add_distrib]
    simp [elevenFiveFiveBlockHostTotal, BlockSystem.blockCount,
      Nat.mul_comm]
  rw [hleft, hright] at hsum
  simpa [K] using hsum

private theorem elevenFive_c39_threeDegree_eq_six_add_three_mul_indicator
    {Point : Type u} {Block : Type v} [Fintype Point] [Fintype Block]
    [DecidableEq Point]
    (S : BlockSystem Point Block) (p : Point)
    (hlocal : ElevenFiveLocalRows S p)
    (hC : S.totalCircleCount = 39) :
    S.blockDegree 3 p =
      6 + 3 * elevenFiveC39HighIndicator S p := by
  have hpair := hlocal.pairRow
  have harms := hlocal.lineArmRow
  have hdelete := hlocal.deletion
  have hsplit := hlocal.threeSplit
  have hkelly := hlocal.kelly
  have hlineThree : S.lineDegree 3 p <= 5 := by
    omega
  have hcircleThree : S.circleDegree 3 p <= 6 := by
    omega
  have hupper : S.blockDegree 3 p <= 11 := by
    omega
  interval_cases hthree : S.blockDegree 3 p <;>
    simp [elevenFiveC39HighIndicator, hthree] at * <;> omega

private theorem elevenFive_square_eq_self_add_two_choose
    (z : Nat) : z * z = z + 2 * Nat.choose z 2 := by
  by_cases hzero : z = 0
  · simp [hzero]
  · have hpos : 1 <= z := Nat.one_le_iff_ne_zero.mpr hzero
    have hsub : z - 1 + 1 = z := Nat.sub_add_cancel hpos
    have hchoose := Erdos506.V4.two_mul_choose_two z
    calc
      z * z = z * ((z - 1) + 1) := by rw [hsub]
      _ = z + z * (z - 1) := by ring
      _ = z + 2 * Nat.choose z 2 := by rw [← hchoose]

private theorem elevenFive_c39_point_energy_identity
    {Point : Type u} {Block : Type v} [Fintype Point] [Fintype Block]
    [DecidableEq Point]
    (S : BlockSystem Point Block) (p : Point)
    (hlocal : ElevenFiveLocalRows S p)
    (hthree : S.blockDegree 3 p =
      6 + 3 * elevenFiveC39HighIndicator S p) :
    S.blockDegree 4 p * S.blockDegree 5 p +
        3 * (S.blockDegree 5 p * S.blockDegree 5 p) +
        elevenFiveC39HighIndicator S p * S.blockDegree 5 p =
      13 * S.blockDegree 5 p +
        S.blockDegree 5 p * S.blockDegree 5 p := by
  have hpair := hlocal.pairRow
  have hmul := congrArg (fun n : Nat => n * S.blockDegree 5 p) hpair
  rw [hthree] at hmul
  simp only [Nat.add_mul, Nat.mul_assoc] at hmul
  omega

private theorem elevenFive_c39_energy_identity
    {Point : Type u} {Block : Type v} [Fintype Point] [Fintype Block]
    [DecidableEq Point]
    (S : BlockSystem Point Block) (hcard : Fintype.card Point = 11)
    (hlocal : ∀ p : Point, ElevenFiveLocalRows S p)
    (hglobal : ElevenFiveGlobalRows S)
    (hC : S.totalCircleCount = 39) :
    (∑ p : Point,
      (S.blockDegree 4 p * S.blockDegree 5 p +
        3 * (S.blockDegree 5 p * S.blockDegree 5 p))) +
      elevenFiveC39HighFiveIncidence S =
        70 * S.blockCount 5 + 2 * elevenFiveSecondMoment S := by
  have hpoint (p : Point) := elevenFive_c39_point_energy_identity S p
    (hlocal p)
    (elevenFive_c39_threeDegree_eq_six_add_three_mul_indicator
      S p (hlocal p) hC)
  have hsum :
      (∑ p : Point,
        (S.blockDegree 4 p * S.blockDegree 5 p +
          3 * (S.blockDegree 5 p * S.blockDegree 5 p) +
          elevenFiveC39HighIndicator S p * S.blockDegree 5 p)) =
        ∑ p : Point,
          (13 * S.blockDegree 5 p +
            S.blockDegree 5 p * S.blockDegree 5 p) := by
    apply Finset.sum_congr rfl
    intro p _hp
    exact hpoint p
  have hsquare :
      (∑ p : Point, S.blockDegree 5 p * S.blockDegree 5 p) =
        (∑ p : Point, S.blockDegree 5 p) +
          2 * elevenFiveSecondMoment S := by
    calc
      (∑ p : Point, S.blockDegree 5 p * S.blockDegree 5 p) =
          ∑ p : Point,
            (S.blockDegree 5 p + 2 * Nat.choose (S.blockDegree 5 p) 2) := by
        apply Finset.sum_congr rfl
        intro p _hp
        exact elevenFive_square_eq_self_add_two_choose (S.blockDegree 5 p)
      _ = (∑ p : Point, S.blockDegree 5 p) +
          2 * elevenFiveSecondMoment S := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum]
        simp only [elevenFiveSecondMoment]
  have hleft :
      (∑ p : Point,
        (S.blockDegree 4 p * S.blockDegree 5 p +
          3 * (S.blockDegree 5 p * S.blockDegree 5 p))) +
        elevenFiveC39HighFiveIncidence S =
        ∑ p : Point,
          (S.blockDegree 4 p * S.blockDegree 5 p +
            3 * (S.blockDegree 5 p * S.blockDegree 5 p) +
            elevenFiveC39HighIndicator S p * S.blockDegree 5 p) := by
    simp only [elevenFiveC39HighFiveIncidence]
    rw [← Finset.sum_add_distrib]
  have hright :
      (∑ p : Point,
        (13 * S.blockDegree 5 p +
          S.blockDegree 5 p * S.blockDegree 5 p)) =
        70 * S.blockCount 5 + 2 * elevenFiveSecondMoment S := by
    calc
      (∑ p : Point,
        (13 * S.blockDegree 5 p +
          S.blockDegree 5 p * S.blockDegree 5 p)) =
          13 * (∑ p : Point, S.blockDegree 5 p) +
            ∑ p : Point, S.blockDegree 5 p * S.blockDegree 5 p := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum]
      _ = 70 * S.blockCount 5 + 2 * elevenFiveSecondMoment S := by
        rw [hsquare, hglobal.fiveIncidence]
        ring
  exact hleft.trans (hsum.trans hright)

private theorem elevenFive_c39_l12_global_rows
    {Point : Type u} {Block : Type v} [Fintype Point] [Fintype Block]
    [DecidableEq Point]
    (S : BlockSystem Point Block) (hglobal : ElevenFiveGlobalRows S)
    (hC : S.totalCircleCount = 39)
    (hL : elevenFiveLineTotal S = 12) :
    S.blockCount 4 + 3 * S.blockCount 5 = 38 ∧
      elevenFiveSigmaTotal S = S.blockCount 5 + 6 := by
  have htriple := hglobal.tripleRow
  have hblock := hglobal.blockTotal
  have hsigma := hglobal.sigmaRow
  rw [hC, hL] at hblock
  constructor <;> omega

private theorem elevenFive_c39_l12_high_count_row
    {Point : Type u} {Block : Type v} [Fintype Point] [Fintype Block]
    [DecidableEq Point]
    (S : BlockSystem Point Block) (hcard : Fintype.card Point = 11)
    (hlocal : ∀ p : Point, ElevenFiveLocalRows S p)
    (hglobal : ElevenFiveGlobalRows S)
    (hC : S.totalCircleCount = 39)
    (hL : elevenFiveLineTotal S = 12) :
    3 * elevenFiveC39HighCount S + 27 = 6 * S.blockCount 5 := by
  obtain ⟨_hfour, hsigma⟩ :=
    elevenFive_c39_l12_global_rows S hglobal hC hL
  have hpoint (p : Point) :=
    elevenFive_c39_threeDegree_eq_six_add_three_mul_indicator
      S p (hlocal p) hC
  have hsumLocal :
      (∑ p : Point,
        (elevenFiveSigmaAt S p + 3 + S.blockDegree 5 p)) =
        ∑ p : Point, S.blockDegree 3 p := by
    apply Finset.sum_congr rfl
    intro p _hp
    exact (hlocal p).sigmaRow
  have hleft :
      (∑ p : Point,
        (elevenFiveSigmaAt S p + 3 + S.blockDegree 5 p)) =
        elevenFiveSigmaTotal S + 33 + 5 * S.blockCount 5 := by
    simp only [Finset.sum_add_distrib]
    rw [hglobal.fiveIncidence]
    simp [hcard, elevenFiveSigmaTotal]
  have hright :
      (∑ p : Point, S.blockDegree 3 p) =
        66 + 3 * elevenFiveC39HighCount S := by
    calc
      (∑ p : Point, S.blockDegree 3 p) =
          ∑ p : Point,
            (6 + 3 * elevenFiveC39HighIndicator S p) := by
        apply Finset.sum_congr rfl
        intro p _hp
        exact hpoint p
      _ = 66 + 3 * elevenFiveC39HighCount S := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum]
        simp [hcard, elevenFiveC39HighCount]
  have hrow :
      elevenFiveSigmaTotal S + 33 + 5 * S.blockCount 5 =
        66 + 3 * elevenFiveC39HighCount S :=
    hleft.symm.trans (hsumLocal.trans hright)
  omega

/-- The paper's global K1 identity for the `C = 39`, `L = 12` face, now
over the actual tagged size-five blocks.  The final summand is the literal
sum of disjoint four- and five-block weights, rather than an assumed slack. -/
theorem elevenFive_c39_l12_host_moment_identity
    {Point : Type u} {Block : Type v} [Fintype Point] [Fintype Block]
    [DecidableEq Point]
    (S : BlockSystem Point Block) (hcard : Fintype.card Point = 11)
    (hcap : BlockSizeCap S 5)
    (hlocal : ∀ p : Point, ElevenFiveLocalRows S p)
    (hglobal : ElevenFiveGlobalRows S)
    (hC : S.totalCircleCount = 39)
    (hL : elevenFiveLineTotal S = 12) :
    elevenFiveFiveBlockHostTotal S + elevenFiveC39HighFiveIncidence S =
      20 * S.blockCount 5 + 2 * elevenFiveSecondMoment S +
        elevenFiveFiveBlockOutsideRichTotal S := by
  obtain ⟨hfour, _hsigma⟩ :=
    elevenFive_c39_l12_global_rows S hglobal hC hL
  have henergy := elevenFive_c39_energy_identity
    S hcard hlocal hglobal hC
  have hmass := elevenFive_host_mass_sum_add_outsideRich_eq S hcap
  have hconstant :
      S.blockCount 5 *
          (S.blockCount 4 + 3 * S.blockCount 5 + 12) =
        50 * S.blockCount 5 := by
    rw [hfour]
    ring
  rw [hconstant] at hmass
  omega

private theorem elevenFive_c39_point_energy_bound
    {Point : Type u} {Block : Type v} [Fintype Point] [Fintype Block]
    [DecidableEq Point]
    (S : BlockSystem Point Block) (p : Point)
    (hz : S.blockDegree 5 p <= 4) :
    4 * S.blockDegree 5 p +
        elevenFiveC39HighIndicator S p * S.blockDegree 5 p <=
      2 * Nat.choose (S.blockDegree 5 p) 2 + 6 +
        3 * elevenFiveC39HighIndicator S p := by
  have hindicator : elevenFiveC39HighIndicator S p <= 1 := by
    simp only [elevenFiveC39HighIndicator]
    split_ifs <;> omega
  interval_cases hdegree : S.blockDegree 5 p <;>
    norm_num [Nat.choose] at * <;> omega

private theorem elevenFive_c39_energy_lower_bound
    {Point : Type u} {Block : Type v} [Fintype Point] [Fintype Block]
    [DecidableEq Point]
    (S : BlockSystem Point Block) (hcard : Fintype.card Point = 11)
    (hlocal : ∀ p : Point, ElevenFiveLocalRows S p)
    (hglobal : ElevenFiveGlobalRows S) :
    20 * S.blockCount 5 + elevenFiveC39HighFiveIncidence S <=
      2 * elevenFiveSecondMoment S + 66 +
        3 * elevenFiveC39HighCount S := by
  have hsum := Finset.sum_le_sum (s := Finset.univ) fun p _hp =>
    elevenFive_c39_point_energy_bound S p (hlocal p).fiveDegreeCap
  have hleft :
      (∑ p : Point,
        (4 * S.blockDegree 5 p +
          elevenFiveC39HighIndicator S p * S.blockDegree 5 p)) =
        20 * S.blockCount 5 + elevenFiveC39HighFiveIncidence S := by
    rw [Finset.sum_add_distrib, ← Finset.mul_sum,
      hglobal.fiveIncidence]
    simp only [elevenFiveC39HighFiveIncidence]
    ring
  have hright :
      (∑ p : Point,
        (2 * Nat.choose (S.blockDegree 5 p) 2 + 6 +
          3 * elevenFiveC39HighIndicator S p)) =
        2 * elevenFiveSecondMoment S + 66 +
          3 * elevenFiveC39HighCount S := by
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
    simp [hcard, elevenFiveSecondMoment, elevenFiveC39HighCount]
  rw [hleft, hright] at hsum
  exact hsum

private theorem elevenFive_host_mass_sum_le
    {Point : Type u} {Block : Type v} [Fintype Point] [Fintype Block]
    [DecidableEq Point]
    (S : BlockSystem Point Block) (hcap : BlockSizeCap S 5) :
    (∑ p : Point,
      (S.blockDegree 4 p * S.blockDegree 5 p +
        3 * (S.blockDegree 5 p * S.blockDegree 5 p))) <=
      elevenFiveFiveBlockHostTotal S +
        S.blockCount 5 *
          (S.blockCount 4 + 3 * S.blockCount 5 + 12) := by
  have hidentity := elevenFive_host_mass_sum_add_outsideRich_eq S hcap
  omega

/-- The global C39 low-host moment, in a subtraction-free form.  It is the
consequence of summing the actual five-block host loads and the pointwise
pair row; the omitted `q` term from the paper is nonnegative, hence this is
the precise inequality needed by the low-host router. -/
theorem elevenFive_c39_l12_host_moment
    {Point : Type u} {Block : Type v} [Fintype Point] [Fintype Block]
    [DecidableEq Point]
    (S : BlockSystem Point Block) (hcard : Fintype.card Point = 11)
    (hcap : BlockSizeCap S 5)
    (hlocal : ∀ p : Point, ElevenFiveLocalRows S p)
    (hglobal : ElevenFiveGlobalRows S)
    (hC : S.totalCircleCount = 39)
    (hL : elevenFiveLineTotal S = 12) :
    34 * S.blockCount 5 <= elevenFiveFiveBlockHostTotal S + 39 := by
  have hhigh := elevenFive_c39_l12_high_count_row
    S hcard hlocal hglobal hC hL
  have henergyLower := elevenFive_c39_energy_lower_bound
    S hcard hlocal hglobal
  have hidentity := elevenFive_c39_l12_host_moment_identity
    S hcard hcap hlocal hglobal hC hL
  have hmoment :
      20 * S.blockCount 5 + 2 * elevenFiveSecondMoment S <=
        elevenFiveFiveBlockHostTotal S +
          elevenFiveC39HighFiveIncidence S := by
    omega
  omega

private theorem elevenFive_c39_l12_fiveBlock_count_ge_five
    {Point : Type u} {Block : Type v} [Fintype Point] [Fintype Block]
    [DecidableEq Point]
    (S : BlockSystem Point Block) (hcard : Fintype.card Point = 11)
    (hlocal : ∀ p : Point, ElevenFiveLocalRows S p)
    (hglobal : ElevenFiveGlobalRows S)
    (hC : S.totalCircleCount = 39)
    (hL : elevenFiveLineTotal S = 12) :
    5 <= S.blockCount 5 := by
  have hhigh := elevenFive_c39_l12_high_count_row
    S hcard hlocal hglobal hC hL
  omega

private theorem elevenFive_c39_l12_lineFive_count_le_one
    {Point : Type u} {Block : Type v} [Fintype Point] [Fintype Block]
    [DecidableEq Point]
    (S : BlockSystem Point Block) (hglobal : ElevenFiveGlobalRows S)
    (hL : elevenFiveLineTotal S = 12) :
    S.lineCount 5 <= 1 := by
  have hmel := hglobal.lineMelchior
  rw [hL] at hmel
  omega

private theorem elevenFive_lineFive_indicator_sum
    {Point : Type u} {Block : Type v} [Fintype Point] [Fintype Block]
    [DecidableEq Point]
    (S : BlockSystem Point Block) :
    (∑ b ∈ S.blocksOfSize 5,
      if S.kind b = .line then 1 else 0) = S.lineCount 5 := by
  classical
  rw [← Finset.sum_filter]
  have hfilter : (S.blocksOfSize 5).filter
      (fun b => S.kind b = .line) = S.lineBlocksOfSize 5 := by
    ext b
    simp [BlockSystem.blocksOfSize, BlockSystem.blocksOfKindSize,
      BlockSystem.blocksOfKind, and_comm]
  rw [hfilter]
  simp [BlockSystem.lineCount]

private theorem elevenFiveFiveBlockHostTotal_le_twenty_five_mul_blockCount_add_five_mul_lineCount
    {Point : Type u} {Block : Type v} [Fintype Point] [Fintype Block]
    [DecidableEq Point]
    (S : BlockSystem Point Block) (hcard : Fintype.card Point = 11)
    (hcircle : ∀ b ∈ S.circleBlocksOfSize 5,
      elevenFiveHostWeight S (S.support b) <= 25) :
    elevenFiveFiveBlockHostTotal S <=
      25 * S.blockCount 5 + 5 * S.lineCount 5 := by
  classical
  have hpoint (b : Block) (hb : b ∈ S.blocksOfSize 5) :
      elevenFiveHostWeight S (S.support b) <=
        25 + 5 * (if S.kind b = .line then 1 else 0) := by
    have hsize := S.mem_blocksOfSize.mp hb
    cases hkind : S.kind b with
    | line =>
        have hthirty := elevenFiveHostWeight_le_thirty
          S (S.support b) hcard hsize
        simp [hkind]
        omega
    | circle =>
        have hcircleMem : b ∈ S.circleBlocksOfSize 5 :=
          S.mem_blocksOfKindSize.mpr ⟨hkind, hsize⟩
        have htwentyFive := hcircle b hcircleMem
        simp [hkind]
        omega
  have hsum := Finset.sum_le_sum fun b hb => hpoint b hb
  have hindicator := elevenFive_lineFive_indicator_sum S
  have hright :
      (∑ b ∈ S.blocksOfSize 5,
        (25 + 5 * (if S.kind b = .line then 1 else 0))) =
        25 * S.blockCount 5 + 5 * S.lineCount 5 := by
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, hindicator]
    simp [BlockSystem.blockCount, Nat.mul_comm]
  change (∑ b ∈ S.blocksOfSize 5,
    elevenFiveHostWeight S (S.support b)) <= _
  rw [hright] at hsum
  exact hsum

/-- The numerical contradiction at the end of the low-host route.  Keeping
the arithmetic in a closed Nat-only lemma prevents `omega` from traversing
the substantial block-system context of the geometric statement. -/
private theorem elevenFive_c39_l12_low_host_arithmetic
    (m host lineFive : Nat)
    (hupper : host <= 25 * m + 5 * lineFive)
    (hline : lineFive <= 1)
    (hmoment : 34 * m <= host + 39)
    (hfive : 5 <= m) : False := by
  omega

/-- The low-host half of the paper's `C = 39`, `L = 12` router.  It yields
an actual circle-tagged five-block whose host load is at least twenty-six.
The proof uses only the block rows, the finite matching capacity, and the
fact that the possible five-line occurs at most once; it contains no K2
trace-rigidity input. -/
theorem elevenFive_c39_l12_exists_circleBlock_host_ge_twenty_six
    {Point : Type u} {Block : Type v} [Fintype Point] [Fintype Block]
    [DecidableEq Point]
    (S : BlockSystem Point Block) (hcard : Fintype.card Point = 11)
    (hcap : BlockSizeCap S 5)
    (hlocal : ∀ p : Point, ElevenFiveLocalRows S p)
    (hglobal : ElevenFiveGlobalRows S)
    (hC : S.totalCircleCount = 39)
    (hL : elevenFiveLineTotal S = 12) :
    ∃ b ∈ S.circleBlocksOfSize 5,
      26 <= elevenFiveHostWeight S (S.support b) := by
  by_contra hnot
  have hcircle (b : Block) (hb : b ∈ S.circleBlocksOfSize 5) :
      elevenFiveHostWeight S (S.support b) <= 25 := by
    by_contra hlarge
    have htwentySix : 26 <= elevenFiveHostWeight S (S.support b) := by
      omega
    exact hnot ⟨b, hb, htwentySix⟩
  have hupper :=
    elevenFiveFiveBlockHostTotal_le_twenty_five_mul_blockCount_add_five_mul_lineCount
      S hcard hcircle
  have hline := elevenFive_c39_l12_lineFive_count_le_one S hglobal hL
  have hmoment := elevenFive_c39_l12_host_moment
    S hcard hcap hlocal hglobal hC hL
  have hfive := elevenFive_c39_l12_fiveBlock_count_ge_five
    S hcard hlocal hglobal hC hL
  exact elevenFive_c39_l12_low_host_arithmetic
    (S.blockCount 5) (elevenFiveFiveBlockHostTotal S) (S.lineCount 5)
    hupper hline hmoment hfive

/-- Geometric specialization of the low-host moment.  The circle tag is
unpacked into the actual determined proper circle, so the output is already
in the form consumed by the C39 geometric router. -/
theorem elevenFive_c39_l12_exists_properFiveCircle_host_ge_twenty_six_of_rows
    {α : Type u} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (hcard : Fintype.card α = 11)
    (hcap : BlockSizeCap (blockSystem cfg) 5)
    (hlocal : ∀ p : α, ElevenFiveLocalRows (blockSystem cfg) p)
    (hglobal : ElevenFiveGlobalRows (blockSystem cfg))
    (hC : (blockSystem cfg).totalCircleCount = 39)
    (hL : elevenFiveLineTotal (blockSystem cfg) = 12) :
    ∃ delta : DeterminedCircle cfg,
      (circleTrace cfg delta.1).card = 5 /\
        26 <= elevenFiveHostWeight (blockSystem cfg)
          (circleTrace cfg delta.1) := by
  obtain ⟨b, hb, hhost⟩ :=
    elevenFive_c39_l12_exists_circleBlock_host_ge_twenty_six
      (Point := α) (Block := GeometricBlock cfg)
      (blockSystem cfg) hcard hcap hlocal hglobal hC hL
  rcases b with L | delta
  · have hkind := ((blockSystem cfg).mem_blocksOfKindSize.mp hb).1
    change (.line : BlockKind) = .circle at hkind
    cases hkind
  · have hsize := ((blockSystem cfg).mem_blocksOfKindSize.mp hb).2
    change (circleTrace cfg delta.1).card = 5 at hsize
    change 26 <= elevenFiveHostWeight (blockSystem cfg)
      (circleTrace cfg delta.1) at hhost
    exact ⟨delta, hsize, hhost⟩

/-- Configuration-level form of the low-host moment.  Its assumptions are
the existing real-plane principles used to derive the exact local and global
rows; no `RealPlaneElevenFiveGeometry` field is invoked. -/
theorem elevenFive_c39_l12_exists_properFiveCircle_host_ge_twenty_six
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
      (circleTrace cfg delta.1).card = 5 /\
        26 <= elevenFiveHostWeight (blockSystem cfg)
          (circleTrace cfg delta.1) := by
  have hbridge : (blockSystem cfg).totalCircleCount =
      Erdos506.V4.circleCount cfg := by
    rw [totalCircleCount_eq_card_determinedCircle,
      ← Erdos506.V3.circleCount_eq_card_determinedCircle]
  have hC : (blockSystem cfg).totalCircleCount = 39 := by
    omega
  have hCupper : (blockSystem cfg).totalCircleCount <= 40 := by
    omega
  have hlocal : ∀ p : α, ElevenFiveLocalRows (blockSystem cfg) p := by
    intro p
    exact elevenFiveLocalRows_of_configuration
      Mel Langer EvenArr Cross Kelly U17 TenGeometry
        cfg hadm hcard hcap hCupper p
  have hglobal : ElevenFiveGlobalRows (blockSystem cfg) :=
    elevenFiveGlobalRows_of_configuration Mel cfg hadm hcard hcap hlocal
  exact elevenFive_c39_l12_exists_properFiveCircle_host_ge_twenty_six_of_rows
    cfg hcard hcap hlocal hglobal hC hL

end Erdos506.V1
