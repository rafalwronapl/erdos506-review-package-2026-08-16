import Erdos506.V1.ElevenFiveC39SignedRowsFinish
import Erdos506.V1.ElevenFiveC40FinalSingletonDispatcher

/-!
# The first unconditional high-host step in the C39 maximum-host router

The `H <= 27` face has a unique high three-degree point.  The signed-row
front gives every proper five-circle a singleton neighbour.  The shared
singleton dispatcher eliminates every non-high carrier profile, so every
such singleton is carried by that unique high point.  Consequently all five
proper circles would contain it, contradicting the local five-degree cap.

This is deliberately only the honest first high-host threshold.  The later
`H = 28,29,30` faces require the separate K2 trace-rigidity geometry.
-/

namespace Erdos506.V1

open Erdos506.Block
open Erdos506.Block.BlockSystem
open Erdos506.Incidence
open Erdos506.V3
open Erdos506.V4
open scoped BigOperators

universe u v

/-- In the C39 local row the three-degree has only the two values needed by
the singleton dispatcher. -/
private theorem elevenFive_c39_threeDegree_six_or_nine_highHost
    {Point : Type u} {Block : Type v} [Fintype Point] [Fintype Block]
    [DecidableEq Point]
    (S : BlockSystem Point Block) (p : Point)
    (hlocal : ElevenFiveLocalRows S p)
    (hC : S.totalCircleCount = 39) :
    S.blockDegree 3 p = 6 ∨ S.blockDegree 3 p = 9 := by
  have hpair := hlocal.pairRow
  have harms := hlocal.lineArmRow
  have hsplit := hlocal.threeSplit
  have hkelly := hlocal.kelly
  have hdelete := hlocal.deletion
  rw [hC] at hdelete
  have hline : S.lineDegree 3 p ≤ 5 := by omega
  have hcircle : S.circleDegree 3 p ≤ 6 := by omega
  omega

/-- A genuine singleton intersection of two proper five-circles in the C39
face is carried by a high point.  The proof uses only the already verified
common-profile dispatcher; the residual `(9,3)` profile is allowed here and
is still high. -/
private theorem elevenFive_c39_singleton_carrier_is_high
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    (cfg : Configuration Point) (hcard : Fintype.card Point = 11)
    (p : Point)
    (hlocal : ∀ q : Point, ElevenFiveLocalRows (blockSystem cfg) q)
    (hC : (blockSystem cfg).totalCircleCount = 39)
    {b c : GeometricBlock cfg}
    (hb : b ∈ (blockSystem cfg).circleBlocksOfSize 5)
    (hc : c ∈ (blockSystem cfg).circleBlocksOfSize 5)
    (hbp : p ∈ geometricBlockSupport cfg b)
    (hcp : p ∈ geometricBlockSupport cfg c) (hbc : b ≠ c)
    (hinter : (geometricBlockSupport cfg b ∩
      geometricBlockSupport cfg c).card = 1) :
    (blockSystem cfg).blockDegree 3 p = 9 := by
  have hbsize : ((blockSystem cfg).support b).card = 5 :=
    ((blockSystem cfg).mem_blocksOfKindSize.mp hb).2
  have hcsize : ((blockSystem cfg).support c).card = 5 :=
    ((blockSystem cfg).mem_blocksOfKindSize.mp hc).2
  have hbblock : b ∈ (blockSystem cfg).blocksOfSize 5 :=
    (blockSystem cfg).mem_blocksOfSize.mpr hbsize
  have hcblock : c ∈ (blockSystem cfg).blocksOfSize 5 :=
    (blockSystem cfg).mem_blocksOfSize.mpr hcsize
  rcases elevenFive_c39_threeDegree_six_or_nine_highHost
    (blockSystem cfg) p (hlocal p) hC with hsix | hnine
  · have htwo := two_le_blockDegree_five_of_two_blocks
      (blockSystem cfg) p hbblock hcblock hbp hcp hbc
    have hcap := (hlocal p).fiveDegreeCap
    have hfive : (blockSystem cfg).blockDegree 5 p = 2 ∨
        (blockSystem cfg).blockDegree 5 p = 3 ∨
          (blockSystem cfg).blockDegree 5 p = 4 := by
      omega
    rcases hfive with htwo' | hthree | hfour
    · exact False.elim
        (elevenFive_c40_singleton_impossible_of_common_profiles
          cfg hcard p (hlocal p) hbblock hcblock hbp hcp hbc hinter
          (Or.inl ⟨hsix, htwo'⟩))
    · exact False.elim
        (elevenFive_c40_singleton_impossible_of_common_profiles
          cfg hcard p (hlocal p) hbblock hcblock hbp hcp hbc hinter
          (Or.inr (Or.inl ⟨hsix, hthree⟩)))
    · exact False.elim
        (elevenFive_c40_singleton_impossible_of_common_profiles
          cfg hcard p (hlocal p) hbblock hcblock hbp hcp hbc hinter
          (Or.inr (Or.inr hfour)))
  · exact hnine

/-- A C39 high-count of one makes the high point unique. -/
private theorem elevenFive_c39_high_point_unique
    {Point : Type u} {Block : Type v} [Fintype Point] [Fintype Block]
    [DecidableEq Point]
    (S : BlockSystem Point Block)
    (hhigh : elevenFiveC39HighCount S = 1)
    {p q : Point} (hp : S.blockDegree 3 p = 9)
    (hq : S.blockDegree 3 q = 9) : p = q := by
  classical
  by_contra hpq
  have hle :
      ((∑ x ∈ ({p, q} : Finset Point), elevenFiveC39HighIndicator S x) ≤
        (∑ x : Point, elevenFiveC39HighIndicator S x)) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · simp
    · intro x _hx _hnot
      exact Nat.zero_le _
  have hsum : (∑ x : Point, elevenFiveC39HighIndicator S x) = 1 := by
    simpa [elevenFiveC39HighCount] using hhigh
  rw [hsum] at hle
  have hpair :
      (∑ x ∈ ({p, q} : Finset Point), elevenFiveC39HighIndicator S x) = 2 := by
    rw [Finset.sum_insert (by simpa using hpq), Finset.sum_singleton]
    simp [elevenFiveC39HighIndicator, hp, hq]
  omega

/-- The `C39HighCount = 1` row contains an actual high point. -/
private theorem elevenFive_c39_high_point_exists
    {Point : Type u} {Block : Type v} [Fintype Point] [Fintype Block]
    [DecidableEq Point]
    (S : BlockSystem Point Block)
    (hhigh : elevenFiveC39HighCount S = 1) :
    ∃ p : Point, S.blockDegree 3 p = 9 := by
  classical
  by_contra hnone
  have hnot (p : Point) : S.blockDegree 3 p ≠ 9 := by
    intro hp
    exact hnone ⟨p, hp⟩
  have hzero (p : Point) : elevenFiveC39HighIndicator S p = 0 := by
    simp [elevenFiveC39HighIndicator, hnot p]
  have hsum : (∑ p : Point, elevenFiveC39HighIndicator S p) = 1 := by
    simpa [elevenFiveC39HighCount] using hhigh
  have hsumzero : (∑ p : Point, elevenFiveC39HighIndicator S p) = 0 := by
    simp_rw [hzero]
    simp
  omega

/-- The first unconditional C39 maximum-host improvement: a proper
five-circle has host load at least 28. -/
theorem elevenFive_c39_l12_exists_properFiveCircle_host_ge_twenty_eight
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
          (circleTrace cfg delta.1) := by
  classical
  by_contra hnot
  have hcircle (b : GeometricBlock cfg)
      (hb : b ∈ (blockSystem cfg).circleBlocksOfSize 5) :
      elevenFiveHostWeight (blockSystem cfg)
        ((blockSystem cfg).support b) ≤ 27 := by
    by_contra hlarge
    have htwentyEight : 28 ≤ elevenFiveHostWeight (blockSystem cfg)
        ((blockSystem cfg).support b) := by omega
    rcases b with L | c
    · have hkind := ((blockSystem cfg).mem_blocksOfKindSize.mp hb).1
      change (.line : BlockKind) = .circle at hkind
      cases hkind
    · have hsize := ((blockSystem cfg).mem_blocksOfKindSize.mp hb).2
      change (circleTrace cfg c.1).card = 5 at hsize
      exact hnot ⟨c, hsize, htwentyEight⟩
  have hbridge : (blockSystem cfg).totalCircleCount =
      Erdos506.V4.circleCount cfg := by
    rw [totalCircleCount_eq_card_determinedCircle,
      ← Erdos506.V3.circleCount_eq_card_determinedCircle]
  have hC : (blockSystem cfg).totalCircleCount = 39 := by omega
  have hCupper : (blockSystem cfg).totalCircleCount ≤ 40 := by omega
  have hlocal : ∀ p : α, ElevenFiveLocalRows (blockSystem cfg) p := by
    intro p
    exact elevenFiveLocalRows_of_configuration
      Mel Langer EvenArr Cross Kelly U17 TenGeometry
        cfg hadm hcard hcap hCupper p
  have hglobal : ElevenFiveGlobalRows (blockSystem cfg) :=
    elevenFiveGlobalRows_of_configuration Mel cfg hadm hcard hcap hlocal
  obtain ⟨hblockFive, hlineFive, hhigh⟩ :=
    elevenFive_c39_l12_circleHost_le_twenty_seven_residual
      (blockSystem cfg) hcard hcap hlocal hglobal hC hL hcircle
  have hcircleFive : (blockSystem cfg).circleCount 5 = 5 := by
    have hsplit := (blockSystem cfg).blockCount_eq_lineCount_add_circleCount 5
    omega
  obtain ⟨p₀, hp₀⟩ :=
    elevenFive_c39_high_point_exists (blockSystem cfg) hhigh
  have hcontains (b : GeometricBlock cfg)
      (hb : b ∈ (blockSystem cfg).circleBlocksOfSize 5) :
      p₀ ∈ geometricBlockSupport cfg b := by
    obtain ⟨_, _, _, c, hc, hinter⟩ :=
      elevenFive_c39_l12_singleton_front_unconditional_of_rows
        (blockSystem cfg) hcard hcap hlocal hglobal hC hL hcircle b hb
    have hbsize : ((blockSystem cfg).support b).card = 5 :=
      ((blockSystem cfg).mem_blocksOfKindSize.mp hb).2
    have hbc : b ≠ c := by
      intro hbc
      subst c
      rw [Finset.inter_self, hbsize] at hinter
      omega
    obtain ⟨p, hpEq⟩ := Finset.card_eq_one.mp hinter
    have hpinterRev : p ∈ (blockSystem cfg).support c ∩
        (blockSystem cfg).support b := by
      rw [hpEq]
      simp
    have hpinter : p ∈ (blockSystem cfg).support b ∩
        (blockSystem cfg).support c := by
      exact Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp hpinterRev).2,
        (Finset.mem_inter.mp hpinterRev).1⟩
    have hbp : p ∈ geometricBlockSupport cfg b :=
      (Finset.mem_inter.mp hpinter).1
    have hcp : p ∈ geometricBlockSupport cfg c :=
      (Finset.mem_inter.mp hpinter).2
    have hinter' : ((blockSystem cfg).support b ∩
        (blockSystem cfg).support c).card = 1 := by
      simpa [Finset.inter_comm] using hinter
    have hphigh := elevenFive_c39_singleton_carrier_is_high
      cfg hcard p hlocal hC hb hc hbp hcp hbc hinter'
    have hpp₀ : p = p₀ :=
      elevenFive_c39_high_point_unique (blockSystem cfg) hhigh hphigh hp₀
    simpa [hpp₀] using hbp
  have hsub : (blockSystem cfg).circleBlocksOfSize 5 ⊆
      ((blockSystem cfg).blocksOfSize 5).filter fun b =>
        p₀ ∈ (blockSystem cfg).support b := by
    intro b hb
    refine Finset.mem_filter.mpr ⟨?_, hcontains b hb⟩
    exact (blockSystem cfg).mem_blocksOfSize.mpr
      ((blockSystem cfg).mem_blocksOfKindSize.mp hb).2
  have hdegree : (blockSystem cfg).circleCount 5 ≤
      (blockSystem cfg).blockDegree 5 p₀ := by
    change ((blockSystem cfg).circleBlocksOfSize 5).card ≤
      (((blockSystem cfg).blocksOfSize 5).filter fun b =>
        p₀ ∈ (blockSystem cfg).support b).card
    exact Finset.card_le_card hsub
  have hfiveCap := (hlocal p₀).fiveDegreeCap
  omega

end Erdos506.V1
