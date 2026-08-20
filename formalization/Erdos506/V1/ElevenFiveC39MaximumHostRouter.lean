import Erdos506.V1.ElevenFiveC39OverloadDerivation

/-!
# The arithmetic `H = 26` face of the C39 maximum-host router

The low-host moment already supplies an actual proper five-circle of host
load at least 26.  This file closes the first remaining maximum-host value
without a new geometric postulate.  The key extra row is the summed restored
line inequality

`7 l₄ + 16 l₅ ≤ m + 8`.

Together with the K1 moment it excludes the possibility that *all* proper
five-circles have host at most 26.  Thus a C39,L12 configuration has a
proper five-circle of host at least 27.  The genuinely geometric residual is
therefore only `H = 27,28,29,30`.
-/

namespace Erdos506.V1

open Erdos506.Block
open Erdos506.Block.BlockSystem
open Erdos506.Incidence
open Erdos506.V4
open scoped BigOperators

universe u v

/-- In the C39,L12 face the only possible local three-degrees are six and
nine.  This is the part of the old scalar reduction needed to recover the
high-point count; it follows directly from the deletion and line-arm rows. -/
private theorem c39_l12_threeDegree_six_or_nine
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

/-- The C39 high indicator exactly records the `d₃ = 9` alternative. -/
private theorem c39_l12_threeDegree_indicator
    {Point : Type u} {Block : Type v} [Fintype Point] [Fintype Block]
    [DecidableEq Point]
    (S : BlockSystem Point Block) (p : Point)
    (hlocal : ElevenFiveLocalRows S p)
    (hC : S.totalCircleCount = 39) :
    S.blockDegree 3 p = 6 + 3 * elevenFiveC39HighIndicator S p := by
  rcases c39_l12_threeDegree_six_or_nine S p hlocal hC with h | h
  · simp [elevenFiveC39HighIndicator, h]
  · simp [elevenFiveC39HighIndicator, h]

/-- The high-point count row, reproved here because the low-host module
keeps its internal derivation private. -/
private theorem c39_l12_high_count_row
    {Point : Type u} {Block : Type v} [Fintype Point] [Fintype Block]
    [DecidableEq Point]
    (S : BlockSystem Point Block) (hcard : Fintype.card Point = 11)
    (hlocal : ∀ p : Point, ElevenFiveLocalRows S p)
    (hglobal : ElevenFiveGlobalRows S)
    (hC : S.totalCircleCount = 39)
    (hL : elevenFiveLineTotal S = 12) :
    3 * elevenFiveC39HighCount S + 27 = 6 * S.blockCount 5 := by
  have htriple := hglobal.tripleRow
  have hblock := hglobal.blockTotal
  have hsigma := hglobal.sigmaRow
  rw [hC, hL] at hblock
  have hsigmaTotal : elevenFiveSigmaTotal S = S.blockCount 5 + 6 := by
    omega
  have hsumLocal :
      (∑ p : Point, (elevenFiveSigmaAt S p + 3 + S.blockDegree 5 p)) =
        ∑ p : Point, S.blockDegree 3 p := by
    apply Finset.sum_congr rfl
    intro p _
    exact (hlocal p).sigmaRow
  have hleft :
      (∑ p : Point, (elevenFiveSigmaAt S p + 3 + S.blockDegree 5 p)) =
        elevenFiveSigmaTotal S + 33 + 5 * S.blockCount 5 := by
    simp only [Finset.sum_add_distrib]
    rw [hglobal.fiveIncidence]
    simp [hcard, elevenFiveSigmaTotal]
  have hright :
      (∑ p : Point, S.blockDegree 3 p) =
        66 + 3 * elevenFiveC39HighCount S := by
    calc
      (∑ p : Point, S.blockDegree 3 p) =
          ∑ p : Point, (6 + 3 * elevenFiveC39HighIndicator S p) := by
        apply Finset.sum_congr rfl
        intro p _
        exact c39_l12_threeDegree_indicator S p (hlocal p) hC
      _ = 66 + 3 * elevenFiveC39HighCount S := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum]
        simp [hcard, elevenFiveC39HighCount]
  have hrow :
      elevenFiveSigmaTotal S + 33 + 5 * S.blockCount 5 =
        66 + 3 * elevenFiveC39HighCount S :=
    hleft.symm.trans (hsumLocal.trans hright)
  omega

/-- The summed restored-line row in the C39,L12 face. -/
private theorem c39_l12_line_cut
    {Point : Type u} {Block : Type v} [Fintype Point] [Fintype Block]
    [DecidableEq Point]
    (S : BlockSystem Point Block)
    (hglobal : ElevenFiveGlobalRows S)
    (hC : S.totalCircleCount = 39)
    (hL : elevenFiveLineTotal S = 12) :
    7 * S.lineCount 4 + 16 * S.lineCount 5 ≤ S.blockCount 5 + 8 := by
  have hblock := hglobal.blockTotal
  have htriple := hglobal.tripleRow
  have hsigma := hglobal.sigmaRow
  have hkappa := hglobal.kappaRow
  rw [hC, hL] at hblock
  have hsigmaTotal : elevenFiveSigmaTotal S = S.blockCount 5 + 6 := by
    omega
  unfold elevenFiveLineTotal at hL
  omega

/-- Public form of the C39 high-point count row.  Later maximum-host faces
reuse this exact identity without repeating its local-degree derivation. -/
theorem elevenFive_c39_l12_high_count_row
    {Point : Type u} {Block : Type v} [Fintype Point] [Fintype Block]
    [DecidableEq Point]
    (S : BlockSystem Point Block) (hcard : Fintype.card Point = 11)
    (hlocal : ∀ p : Point, ElevenFiveLocalRows S p)
    (hglobal : ElevenFiveGlobalRows S)
    (hC : S.totalCircleCount = 39)
    (hL : elevenFiveLineTotal S = 12) :
    3 * elevenFiveC39HighCount S + 27 = 6 * S.blockCount 5 :=
  c39_l12_high_count_row S hcard hlocal hglobal hC hL

/-- Public form of the restored-line cut used by every C39 maximum-host
face. -/
theorem elevenFive_c39_l12_line_cut
    {Point : Type u} {Block : Type v} [Fintype Point] [Fintype Block]
    [DecidableEq Point]
    (S : BlockSystem Point Block)
    (hglobal : ElevenFiveGlobalRows S)
    (hC : S.totalCircleCount = 39)
    (hL : elevenFiveLineTotal S = 12) :
    7 * S.lineCount 4 + 16 * S.lineCount 5 ≤ S.blockCount 5 + 8 :=
  c39_l12_line_cut S hglobal hC hL

/-- Bounding every circle five-block by 26 bounds the total host mass.  A
possible five-line retains only the universal excess `30 - 26 = 4`. -/
private theorem c39_host_total_le_twenty_six_mul_blockCount_add_four_mul_lineCount
    {Point : Type u} {Block : Type v} [Fintype Point] [Fintype Block]
    [DecidableEq Point]
    (S : BlockSystem Point Block) (hcard : Fintype.card Point = 11)
    (hcircle : ∀ b ∈ S.circleBlocksOfSize 5,
      elevenFiveHostWeight S (S.support b) ≤ 26) :
    elevenFiveFiveBlockHostTotal S ≤
      26 * S.blockCount 5 + 4 * S.lineCount 5 := by
  classical
  have hpoint (b : Block) (hb : b ∈ S.blocksOfSize 5) :
      elevenFiveHostWeight S (S.support b) ≤
        26 + 4 * (if S.kind b = .line then 1 else 0) := by
    have hsize := S.mem_blocksOfSize.mp hb
    cases hkind : S.kind b with
    | line =>
        have hthirty := elevenFiveHostWeight_le_thirty S (S.support b)
          hcard hsize
        simp [hkind]
        omega
    | circle =>
        have hmem : b ∈ S.circleBlocksOfSize 5 :=
          S.mem_blocksOfKindSize.mpr ⟨hkind, hsize⟩
        have htwentySix := hcircle b hmem
        simp [hkind]
        omega
  have hsum := Finset.sum_le_sum fun b hb => hpoint b hb
  have hindicator :
      (∑ b ∈ S.blocksOfSize 5,
        if S.kind b = .line then 1 else 0) = S.lineCount 5 := by
    rw [← Finset.sum_filter]
    have hfilter : (S.blocksOfSize 5).filter
        (fun b => S.kind b = .line) = S.lineBlocksOfSize 5 := by
      ext b
      simp [BlockSystem.blocksOfSize, BlockSystem.blocksOfKindSize,
        BlockSystem.blocksOfKind, and_comm]
    rw [hfilter]
    simp [BlockSystem.lineCount]
  have hright :
      (∑ b ∈ S.blocksOfSize 5,
        (26 + 4 * (if S.kind b = .line then 1 else 0))) =
        26 * S.blockCount 5 + 4 * S.lineCount 5 := by
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, hindicator]
    simp [BlockSystem.blockCount, Nat.mul_comm]
  change (∑ b ∈ S.blocksOfSize 5,
    elevenFiveHostWeight S (S.support b)) ≤ _
  rw [hright] at hsum
  exact hsum

/-- The complete arithmetic exclusion of the `H = 26` maximum-host face:
there cannot be a C39,L12 block system in which every proper five-circle has
host load at most 26. -/
theorem elevenFive_c39_l12_not_all_circleHost_le_twenty_six
    {Point : Type u} {Block : Type v} [Fintype Point] [Fintype Block]
    [DecidableEq Point]
    (S : BlockSystem Point Block) (hcard : Fintype.card Point = 11)
    (hcap : BlockSizeCap S 5)
    (hlocal : ∀ p : Point, ElevenFiveLocalRows S p)
    (hglobal : ElevenFiveGlobalRows S)
    (hC : S.totalCircleCount = 39)
    (hL : elevenFiveLineTotal S = 12)
    (hcircle : ∀ b ∈ S.circleBlocksOfSize 5,
      elevenFiveHostWeight S (S.support b) ≤ 26) : False := by
  have hhigh := c39_l12_high_count_row S hcard hlocal hglobal hC hL
  have hfive : 5 ≤ S.blockCount 5 := by omega
  have hlineCut := c39_l12_line_cut S hglobal hC hL
  have hlineMelchior := hglobal.lineMelchior
  rw [hL] at hlineMelchior
  have hlineFive : S.lineCount 5 ≤ 1 := by omega
  have hupper :=
    c39_host_total_le_twenty_six_mul_blockCount_add_four_mul_lineCount
      S hcard hcircle
  have hmoment := elevenFive_c39_l12_host_moment
    S hcard hcap hlocal hglobal hC hL
  omega

/-- The analogous host-mass estimate at the next level.  It is used only
to identify the sole arithmetic residual at maximum host 27. -/
private theorem c39_host_total_le_twenty_seven_mul_blockCount_add_three_mul_lineCount
    {Point : Type u} {Block : Type v} [Fintype Point] [Fintype Block]
    [DecidableEq Point]
    (S : BlockSystem Point Block) (hcard : Fintype.card Point = 11)
    (hcircle : ∀ b ∈ S.circleBlocksOfSize 5,
      elevenFiveHostWeight S (S.support b) ≤ 27) :
    elevenFiveFiveBlockHostTotal S ≤
      27 * S.blockCount 5 + 3 * S.lineCount 5 := by
  classical
  have hpoint (b : Block) (hb : b ∈ S.blocksOfSize 5) :
      elevenFiveHostWeight S (S.support b) ≤
        27 + 3 * (if S.kind b = .line then 1 else 0) := by
    have hsize := S.mem_blocksOfSize.mp hb
    cases hkind : S.kind b with
    | line =>
        have hthirty := elevenFiveHostWeight_le_thirty S (S.support b)
          hcard hsize
        simp [hkind]
        omega
    | circle =>
        have hmem : b ∈ S.circleBlocksOfSize 5 :=
          S.mem_blocksOfKindSize.mpr ⟨hkind, hsize⟩
        have htwentySeven := hcircle b hmem
        simp [hkind]
        omega
  have hsum := Finset.sum_le_sum fun b hb => hpoint b hb
  have hindicator :
      (∑ b ∈ S.blocksOfSize 5,
        if S.kind b = .line then 1 else 0) = S.lineCount 5 := by
    rw [← Finset.sum_filter]
    have hfilter : (S.blocksOfSize 5).filter
        (fun b => S.kind b = .line) = S.lineBlocksOfSize 5 := by
      ext b
      simp [BlockSystem.blocksOfSize, BlockSystem.blocksOfKindSize,
        BlockSystem.blocksOfKind, and_comm]
    rw [hfilter]
    simp [BlockSystem.lineCount]
  have hright :
      (∑ b ∈ S.blocksOfSize 5,
        (27 + 3 * (if S.kind b = .line then 1 else 0))) =
        27 * S.blockCount 5 + 3 * S.lineCount 5 := by
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, hindicator]
    simp [BlockSystem.blockCount, Nat.mul_comm]
  change (∑ b ∈ S.blocksOfSize 5,
    elevenFiveHostWeight S (S.support b)) ≤ _
  rw [hright] at hsum
  exact hsum

/-- Exact arithmetic residue of the maximum-host-27 face.  The subsequent
singleton-intersection argument has no numerical freedom left: there are
five five-blocks, all proper circles, and exactly one high point. -/
theorem elevenFive_c39_l12_circleHost_le_twenty_seven_residual
    {Point : Type u} {Block : Type v} [Fintype Point] [Fintype Block]
    [DecidableEq Point]
    (S : BlockSystem Point Block) (hcard : Fintype.card Point = 11)
    (hcap : BlockSizeCap S 5)
    (hlocal : ∀ p : Point, ElevenFiveLocalRows S p)
    (hglobal : ElevenFiveGlobalRows S)
    (hC : S.totalCircleCount = 39)
    (hL : elevenFiveLineTotal S = 12)
    (hcircle : ∀ b ∈ S.circleBlocksOfSize 5,
      elevenFiveHostWeight S (S.support b) ≤ 27) :
    S.blockCount 5 = 5 ∧ S.lineCount 5 = 0 ∧
      elevenFiveC39HighCount S = 1 := by
  have hhigh := c39_l12_high_count_row S hcard hlocal hglobal hC hL
  have hfive : 5 ≤ S.blockCount 5 := by omega
  have hlineCut := c39_l12_line_cut S hglobal hC hL
  have hlineMelchior := hglobal.lineMelchior
  rw [hL] at hlineMelchior
  have hlineFive : S.lineCount 5 ≤ 1 := by omega
  have hupper :=
    c39_host_total_le_twenty_seven_mul_blockCount_add_three_mul_lineCount
      S hcard hcircle
  have hmoment := elevenFive_c39_l12_host_moment
    S hcard hcap hlocal hglobal hC hL
  omega

/-- Configuration-level consequence: in the C39,L12 branch the existing
low-host witness can be strengthened from 26 to 27 without using the old
C39 geometry field. -/
theorem elevenFive_c39_l12_exists_properFiveCircle_host_ge_twenty_seven
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
        27 ≤ elevenFiveHostWeight (blockSystem cfg)
          (circleTrace cfg delta.1) := by
  classical
  obtain ⟨delta, hdelta, hhost⟩ :=
    elevenFive_c39_l12_exists_properFiveCircle_host_ge_twenty_six
      Mel Langer EvenArr Cross Kelly U17 TenGeometry cfg hadm hcard hcap
      hCcount hL
  by_contra hnot
  have hcircle (b : GeometricBlock cfg)
      (hb : b ∈ (blockSystem cfg).circleBlocksOfSize 5) :
      elevenFiveHostWeight (blockSystem cfg)
        ((blockSystem cfg).support b) ≤ 26 := by
    by_contra hlarge
    have htwentySeven : 27 ≤ elevenFiveHostWeight (blockSystem cfg)
        ((blockSystem cfg).support b) := by omega
    rcases b with L | c
    · have hkind := ((blockSystem cfg).mem_blocksOfKindSize.mp hb).1
      change (.line : BlockKind) = .circle at hkind
      cases hkind
    · have hsize := ((blockSystem cfg).mem_blocksOfKindSize.mp hb).2
      change (circleTrace cfg c.1).card = 5 at hsize
      exact hnot ⟨c, hsize, htwentySeven⟩
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
  exact elevenFive_c39_l12_not_all_circleHost_le_twenty_six
    (blockSystem cfg) hcard hcap hlocal hglobal hC hL hcircle

end Erdos506.V1
