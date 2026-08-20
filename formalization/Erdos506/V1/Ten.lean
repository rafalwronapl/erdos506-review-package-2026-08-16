import Erdos506.Incidence.OrdinaryPrinciples
import Erdos506.V1.SmallReduction
import Erdos506.V1.TenFiveScalar
import Erdos506.V1.TenGammaSix

/-!
# The ten-point V1 router

Under the contradictory bound `C ≤ 32`, the rich-circle pencil cap leaves
only circle traces of size at most six.  If the cap is not already five, a
six-circle exists and `TenGammaSix` closes the branch using U17.  Consequently
the sole remaining semantic endpoint is the branch in which every determined
circle has trace size at most five.  `TenFiveScalar` records the exact
solver-free arithmetic face table inside that endpoint; it deliberately does
not assert the remaining geometric capacity and golden-link exclusions.
-/

namespace Erdos506.V1

open Erdos506.Incidence
open Erdos506.V4

universe u

/-- Either all determined circles have trace size at most five, or the
ten-point target already follows.  The possible trace-six branch is closed
by U17; traces of size at least seven are excluded by the rich-circle cap
under the contradictory objective bound. -/
theorem circle_cap_five_or_circleCount_ge_thirty_three_of_card_ten
    {α : Type u} [Fintype α] [DecidableEq α]
    (Mel : RealPlaneMelchiorPrinciple.{u})
    (U17 : RealPlaneSixCircleU17Principle.{u})
    (cfg : Configuration α) (hadm : Admissible cfg)
    (hcard : Fintype.card α = 10) :
    (∀ c : DeterminedCircle cfg, (circleTrace cfg c.1).card ≤ 5) ∨
      33 ≤ Erdos506.V4.circleCount cfg := by
  classical
  by_cases htarget : 33 ≤ Erdos506.V4.circleCount cfg
  · exact Or.inr htarget
  · have hcount : Erdos506.V4.circleCount cfg ≤ 32 := by omega
    have hcapSix : ∀ c : DeterminedCircle cfg,
        (circleTrace cfg c.1).card ≤ 6 := by
      intro c
      exact circleTrace_card_le_six_of_ten_of_circleCount_le
        cfg hadm hcard hcount c
    by_cases hcapFive : ∀ c : DeterminedCircle cfg,
        (circleTrace cfg c.1).card ≤ 5
    · exact Or.inl hcapFive
    · push Not at hcapFive
      obtain ⟨gamma, hgammaLarge⟩ := hcapFive
      have hgamma : (circleTrace cfg gamma.1).card = 6 := by
        have := hcapSix gamma
        omega
      have hsix :=
        circleCount_ge_thirty_three_of_ten_of_selected_six_circle
          Mel U17 cfg hadm hcard gamma hgamma hcapSix
      exact (htarget hsix).elim

/-- Callback form of the ten-point reduction.  Its only unresolved geometric
hypothesis is the semantic circle-trace cap `∀ c, trace(c).card ≤ 5`. -/
theorem circleCount_ge_thirty_three_of_card_ten_of_circle_cap_five_endpoint
    {α : Type u} [Fintype α] [DecidableEq α]
    (Mel : RealPlaneMelchiorPrinciple.{u})
    (U17 : RealPlaneSixCircleU17Principle.{u})
    (cfg : Configuration α) (hadm : Admissible cfg)
    (hcard : Fintype.card α = 10)
    (capFiveEndpoint :
      (∀ c : DeterminedCircle cfg, (circleTrace cfg c.1).card ≤ 5) →
        33 ≤ Erdos506.V4.circleCount cfg) :
    33 ≤ Erdos506.V4.circleCount cfg := by
  rcases circle_cap_five_or_circleCount_ge_thirty_three_of_card_ten
      Mel U17 cfg hadm hcard with hcap | htarget
  · exact capFiveEndpoint hcap
  · exact htarget

/-- Target-valued router for use by the finite V1 assembly.  Outside
`SmallHardCase` the existing V3/V4 routes apply; inside it, the only callback
left is the circle-cap-five endpoint. -/
theorem circleCount_ge_target_of_card_ten_of_smallHardCase_cap_five_endpoint
    {α : Type u} [Fintype α] [DecidableEq α]
    (Mel : RealPlaneMelchiorPrinciple.{u})
    (U17 : RealPlaneSixCircleU17Principle.{u})
    (cfg : Configuration α) (hadm : Admissible cfg)
    (hcard : Fintype.card α = 10)
    (hardCapFiveEndpoint :
      SmallHardCase cfg →
      (∀ c : DeterminedCircle cfg, (circleTrace cfg c.1).card ≤ 5) →
      Erdos506.v1Target (Fintype.card α) ≤
        Erdos506.V4.circleCount cfg) :
    Erdos506.v1Target (Fintype.card α) ≤
      Erdos506.V4.circleCount cfg := by
  by_cases hthree : Erdos506.V3.NoThreeCollinear cfg
  · exact circleCount_ge_target_of_noThreeCollinear
      Mel cfg hadm (by omega) hthree
  by_cases hfour : Erdos506.V4.NoFourConcyclic cfg
  · exact circleCount_ge_target_of_noFourConcyclic
      cfg hadm (by omega) hfour
  rw [hcard]
  norm_num [Erdos506.v1Target, Erdos506.v1UniformTarget, Nat.choose]
  apply circleCount_ge_thirty_three_of_card_ten_of_circle_cap_five_endpoint
    Mel U17 cfg hadm hcard
  intro hcap
  have htarget := hardCapFiveEndpoint ⟨hthree, hfour⟩ hcap
  rw [hcard] at htarget
  norm_num [Erdos506.v1Target, Erdos506.v1UniformTarget,
    Nat.choose] at htarget
  exact htarget

section CircleCapFour

open Erdos506.Block
open Erdos506.Block.BlockSystem
open scoped BigOperators

/-- Pure scalar core of the maximum-four branch.  These are exactly the
triple, objective, global-line, and restored-centre rows used in the paper. -/
theorem ten_cap_four_scalar_profile
    {B3 B4 B5 L3 L4 L5 C3 C4 C : ℕ}
    (htriple : B3 + 4 * B4 + 10 * B5 = 120)
    (hsplit3 : B3 = L3 + C3) (hsplit4 : B4 = L4 + C4)
    (hsplit5 : B5 = L5)
    (htotal : C = C3 + C4) (hcount : C ≤ 32) (hB3 : 20 ≤ B3)
    (hline : 3 * (L3 : ℤ) + 7 * (L4 : ℤ) + 12 * (L5 : ℤ) ≤ 42)
    (hdefect : -3 * (C3 : ℤ) + 6 * (L3 : ℤ) +
      16 * (L4 : ℤ) + 30 * (L5 : ℤ) ≤ 60) :
    B3 = 20 ∧ B4 = 25 ∧ B5 = 0 ∧
      L3 = 13 ∧ L4 = 0 ∧ L5 = 0 ∧
      C3 = 7 ∧ C4 = 25 ∧ C = 32 := by
  have hlineNat : 3 * L3 + 7 * L4 + 12 * L5 ≤ 42 := by
    exact_mod_cast hline
  have hdefectZ :
      ((6 * L3 + 16 * L4 + 30 * L5 : ℕ) : ℤ) ≤
        ((60 + 3 * C3 : ℕ) : ℤ) := by
    push_cast
    omega
  have hdefectNat :
      6 * L3 + 16 * L4 + 30 * L5 ≤ 60 + 3 * C3 := by
    exact_mod_cast hdefectZ
  clear hline hdefect hdefectZ
  have hB5zero : B5 = 0 := by omega
  have hL5zero : L5 = 0 := by omega
  have hB3eq : B3 = 20 := by omega
  have hB4eq : B4 = 25 := by omega
  have hL4zero : L4 = 0 := by omega
  have hL3eq : L3 = 13 := by omega
  have hC3eq : C3 = 7 := by omega
  have hC4eq : C4 = 25 := by omega
  have hCeq : C = 32 := by omega
  exact ⟨hB3eq, hB4eq, hB5zero, hL3eq, hL4zero, hL5zero,
    hC3eq, hC4eq, hCeq⟩

private theorem ten_blockCount_eq_zero_of_cap
    {Point Block : Type*} [Fintype Point] [Fintype Block]
    [DecidableEq Point]
    (S : BlockSystem Point Block) {M s : ℕ}
    (hcap : BlockSizeCap S M) (hthree : 3 ≤ s) (hlarge : M < s) :
    S.blockCount s = 0 := by
  classical
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro b hb
  have hsize := S.mem_blocksOfSize.mp hb
  have hle := hcap b (by omega)
  omega

private theorem ten_lineCount_eq_zero_of_cap
    {Point Block : Type*} [Fintype Point] [Fintype Block]
    [DecidableEq Point]
    (S : BlockSystem Point Block) {M s : ℕ}
    (hcap : BlockSizeCap S M) (hthree : 3 ≤ s) (hlarge : M < s) :
    S.lineCount s = 0 := by
  classical
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro b hb
  have hspec := S.mem_blocksOfKindSize.mp hb
  have hle := hcap b (by rw [hspec.2]; exact hthree)
  omega

private theorem ten_circleCount_eq_zero_of_cap
    {Point Block : Type*} [Fintype Point] [Fintype Block]
    [DecidableEq Point]
    (S : BlockSystem Point Block) {M s : ℕ}
    (hcap : ∀ b, S.kind b = .circle → (S.support b).card ≤ M)
    (hlarge : M < s) : S.circleCount s = 0 := by
  classical
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro b hb
  have hspec := S.mem_blocksOfKindSize.mp hb
  have hle := hcap b hspec.1
  omega

private theorem ten_blockDegree_eq_zero_of_blockCount_eq_zero
    {Point Block : Type*} [Fintype Point] [Fintype Block]
    [DecidableEq Point]
    (S : BlockSystem Point Block) (s : ℕ) (p : Point)
    (hzero : S.blockCount s = 0) : S.blockDegree s p = 0 := by
  have hinc := S.block_incidence s
  rw [hzero] at hinc
  have hle : S.blockDegree s p ≤ ∑ q : Point, S.blockDegree s q := by
    exact Finset.single_le_sum
      (fun q _hq => Nat.zero_le (S.blockDegree s q)) (Finset.mem_univ p)
  omega

/-- Under `C ≤ 32`, a circle cap of four and the rich-line pencil give a
cap of five on every nontrivial V1 block. -/
theorem blockSizeCap_five_of_card_ten_of_circleCount_le_of_circle_cap_four
    {α : Type u} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (hadm : Admissible cfg)
    (hcard : Fintype.card α = 10)
    (hcount : Erdos506.V4.circleCount cfg ≤ 32)
    (hcircle : ∀ c : DeterminedCircle cfg,
      (circleTrace cfg c.1).card ≤ 4) :
    BlockSizeCap (blockSystem cfg) 5 := by
  intro b _hthree
  cases b with
  | inl L =>
      simpa [blockSystem, geometricBlockSupport] using
        lineSupport_card_le_five_of_ten_of_circleCount_le
          cfg hadm hcard hcount L
  | inr c =>
      exact (hcircle c).trans (by omega)

/-- At a ten-point pivot, the pair row and the five-block cap reduce to
`d3 + 3 d4 + 6 d5 = 36`; Kelly--Moser and the residue force `d3 ≥ 6`. -/
theorem ten_cap_four_local_pair
    {Point Block : Type*} [Fintype Point] [Fintype Block]
    [DecidableEq Point]
    (S : BlockSystem Point Block) (hcard : Fintype.card Point = 10)
    (hcap : BlockSizeCap S 5) (p : Point)
    (hKelly : 27 ≤ 7 * S.blockDegree 3 p) :
    S.blockDegree 3 p + 3 * S.blockDegree 4 p +
        6 * S.blockDegree 5 p = 36 ∧
      6 ≤ S.blockDegree 3 p := by
  have hb6 : S.blockCount 6 = 0 :=
    ten_blockCount_eq_zero_of_cap S hcap (by omega) (by omega)
  have hb7 : S.blockCount 7 = 0 :=
    ten_blockCount_eq_zero_of_cap S hcap (by omega) (by omega)
  have hb8 : S.blockCount 8 = 0 :=
    ten_blockCount_eq_zero_of_cap S hcap (by omega) (by omega)
  have hb9 : S.blockCount 9 = 0 :=
    ten_blockCount_eq_zero_of_cap S hcap (by omega) (by omega)
  have hb10 : S.blockCount 10 = 0 :=
    ten_blockCount_eq_zero_of_cap S hcap (by omega) (by omega)
  have hd6 := ten_blockDegree_eq_zero_of_blockCount_eq_zero S 6 p hb6
  have hd7 := ten_blockDegree_eq_zero_of_blockCount_eq_zero S 7 p hb7
  have hd8 := ten_blockDegree_eq_zero_of_blockCount_eq_zero S 8 p hb8
  have hd9 := ten_blockDegree_eq_zero_of_blockCount_eq_zero S 9 p hb9
  have hd10 := ten_blockDegree_eq_zero_of_blockCount_eq_zero S 10 p hb10
  have hpairs := S.pivot_pair_partition p
  rw [hcard] at hpairs
  norm_num [Finset.sum_range_succ, Nat.choose,
    hd6, hd7, hd8, hd9, hd10] at hpairs
  exact ⟨hpairs, by omega⟩

private theorem ten_globalLineRow_eq_three_four_five
    {Point Block : Type*} [Fintype Point] [Fintype Block]
    [DecidableEq Point]
    (S : BlockSystem Point Block) (hcard : Fintype.card Point = 10)
    (hcap : BlockSizeCap S 5) :
    S.globalLineRow = 3 * (S.lineCount 3 : ℤ) +
      7 * (S.lineCount 4 : ℤ) + 12 * (S.lineCount 5 : ℤ) := by
  classical
  let w : ℕ → ℕ := fun s =>
    if 3 ≤ s then Nat.choose s 2 + s - 3 else 0
  have hl6 : S.lineCount 6 = 0 :=
    ten_lineCount_eq_zero_of_cap S hcap (by omega) (by omega)
  have hl7 : S.lineCount 7 = 0 :=
    ten_lineCount_eq_zero_of_cap S hcap (by omega) (by omega)
  have hl8 : S.lineCount 8 = 0 :=
    ten_lineCount_eq_zero_of_cap S hcap (by omega) (by omega)
  have hl9 : S.lineCount 9 = 0 :=
    ten_lineCount_eq_zero_of_cap S hcap (by omega) (by omega)
  have hl10 : S.lineCount 10 = 0 :=
    ten_lineCount_eq_zero_of_cap S hcap (by omega) (by omega)
  have hgroup := S.sum_kindCount_weight .line w
  change
    (∑ s ∈ Finset.range (Fintype.card Point + 1),
      w s * S.lineCount s) =
      ∑ b ∈ S.blocksOfKind .line, w (S.support b).card at hgroup
  rw [hcard] at hgroup
  norm_num [Finset.sum_range_succ, w, hl6, hl7, hl8, hl9, hl10,
    Nat.choose] at hgroup
  have hsubtype :
      (∑ b : LineBlock S, w (S.support b.1).card) =
        ∑ b ∈ S.blocksOfKind .line, w (S.support b).card := by
    symm
    simpa [blocksOfKind] using
      (Finset.sum_subtype (S.blocksOfKind .line)
        (fun b => by simp [blocksOfKind])
        (fun b => w (S.support b).card))
  have hpoint (b : LineBlock S) :
      (if 3 ≤ (S.support b.1).card then
          (Nat.choose (S.support b.1).card 2 : ℤ) +
            ((S.support b.1).card : ℤ) - 3
        else 0) = (w (S.support b.1).card : ℤ) := by
    dsimp only [w]
    split_ifs with hthree
    · omega
    · rfl
  unfold BlockSystem.globalLineRow
  calc
    (∑ b : LineBlock S,
        if 3 ≤ (S.support b.1).card then
          (Nat.choose (S.support b.1).card 2 : ℤ) +
            ((S.support b.1).card : ℤ) - 3
        else 0) =
        ∑ b : LineBlock S, (w (S.support b.1).card : ℤ) := by
      apply Fintype.sum_congr
      exact hpoint
    _ = ((∑ b : LineBlock S, w (S.support b.1).card : ℕ) : ℤ) := by
      norm_num
    _ = ((∑ b ∈ S.blocksOfKind .line,
        w (S.support b).card : ℕ) : ℤ) := by rw [hsubtype]
    _ = 3 * (S.lineCount 3 : ℤ) + 7 * (S.lineCount 4 : ℤ) +
        12 * (S.lineCount 5 : ℤ) := by
      exact_mod_cast hgroup.symm

private theorem ten_defectRow_eq_three_four_five
    {Point Block : Type*} [Fintype Point] [Fintype Block]
    [DecidableEq Point]
    (S : BlockSystem Point Block) (hcard : Fintype.card Point = 10)
    (hcap : BlockSizeCap S 5)
    (hcircle : ∀ b, S.kind b = .circle → (S.support b).card ≤ 4) :
    S.defectRow = -3 * (S.circleCount 3 : ℤ) +
      6 * (S.lineCount 3 : ℤ) + 16 * (S.lineCount 4 : ℤ) +
      30 * (S.lineCount 5 : ℤ) := by
  have hl6 : S.lineCount 6 = 0 :=
    ten_lineCount_eq_zero_of_cap S hcap (by omega) (by omega)
  have hl7 : S.lineCount 7 = 0 :=
    ten_lineCount_eq_zero_of_cap S hcap (by omega) (by omega)
  have hl8 : S.lineCount 8 = 0 :=
    ten_lineCount_eq_zero_of_cap S hcap (by omega) (by omega)
  have hl9 : S.lineCount 9 = 0 :=
    ten_lineCount_eq_zero_of_cap S hcap (by omega) (by omega)
  have hl10 : S.lineCount 10 = 0 :=
    ten_lineCount_eq_zero_of_cap S hcap (by omega) (by omega)
  have hc5 : S.circleCount 5 = 0 :=
    ten_circleCount_eq_zero_of_cap S hcircle (by omega)
  have hc6 : S.circleCount 6 = 0 :=
    ten_circleCount_eq_zero_of_cap S hcircle (by omega)
  have hc7 : S.circleCount 7 = 0 :=
    ten_circleCount_eq_zero_of_cap S hcircle (by omega)
  have hc8 : S.circleCount 8 = 0 :=
    ten_circleCount_eq_zero_of_cap S hcircle (by omega)
  have hc9 : S.circleCount 9 = 0 :=
    ten_circleCount_eq_zero_of_cap S hcircle (by omega)
  have hc10 : S.circleCount 10 = 0 :=
    ten_circleCount_eq_zero_of_cap S hcircle (by omega)
  unfold BlockSystem.defectRow BlockSystem.nontrivialSizes
  rw [hcard]
  have hIcc : Finset.Icc 3 10 = {3, 4, 5, 6, 7, 8, 9, 10} := by
    decide
  rw [hIcc]
  norm_num [hc5, hc6, hc7, hc8, hc9, hc10,
    hl6, hl7, hl8, hl9, hl10]
  ring

/-- All incidence rows before the RealNineLink endpoint force the unique
maximum-four aggregate profile printed in the manuscript.  The last field
also records the pointwise degrees forced by equality. -/
theorem ten_circle_cap_four_forced_profile
    {α : Type u} [Fintype α] [DecidableEq α]
    (Mel : RealPlaneMelchiorPrinciple.{u})
    (KM : RealPlaneKellyMoserPrinciple.{u})
    (cfg : Configuration α) (hadm : Admissible cfg)
    (hcard : Fintype.card α = 10)
    (hcount : Erdos506.V4.circleCount cfg ≤ 32)
    (hcircle : ∀ c : DeterminedCircle cfg,
      (circleTrace cfg c.1).card ≤ 4) :
    let S := blockSystem cfg
    S.blockCount 3 = 20 ∧ S.blockCount 4 = 25 ∧
      S.blockCount 5 = 0 ∧ S.lineCount 3 = 13 ∧
      S.lineCount 4 = 0 ∧ S.lineCount 5 = 0 ∧
      S.circleCount 3 = 7 ∧ S.circleCount 4 = 25 ∧
      S.totalCircleCount = 32 ∧
      ∀ p : α, S.blockDegree 3 p = 6 ∧
        S.blockDegree 4 p = 10 ∧ S.blockDegree 5 p = 0 := by
  classical
  dsimp only
  let S := blockSystem cfg
  have hcap : BlockSizeCap S 5 := by
    simpa [S] using
      blockSizeCap_five_of_card_ten_of_circleCount_le_of_circle_cap_four
        cfg hadm hcard hcount hcircle
  have hcircleBlock : ∀ b : GeometricBlock cfg,
      S.kind b = .circle → (S.support b).card ≤ 4 := by
    intro b hb
    cases b with
    | inl L => cases hb
    | inr c => exact hcircle c
  have hb6 : S.blockCount 6 = 0 :=
    ten_blockCount_eq_zero_of_cap S hcap (by omega) (by omega)
  have hb7 : S.blockCount 7 = 0 :=
    ten_blockCount_eq_zero_of_cap S hcap (by omega) (by omega)
  have hb8 : S.blockCount 8 = 0 :=
    ten_blockCount_eq_zero_of_cap S hcap (by omega) (by omega)
  have hb9 : S.blockCount 9 = 0 :=
    ten_blockCount_eq_zero_of_cap S hcap (by omega) (by omega)
  have hb10 : S.blockCount 10 = 0 :=
    ten_blockCount_eq_zero_of_cap S hcap (by omega) (by omega)
  have hc0 : S.circleCount 0 = 0 :=
    S.circleCount_eq_zero_of_lt_three (by omega)
  have hc1 : S.circleCount 1 = 0 :=
    S.circleCount_eq_zero_of_lt_three (by omega)
  have hc2 : S.circleCount 2 = 0 :=
    S.circleCount_eq_zero_of_lt_three (by omega)
  have hc5 : S.circleCount 5 = 0 :=
    ten_circleCount_eq_zero_of_cap S hcircleBlock (by omega)
  have hc6 : S.circleCount 6 = 0 :=
    ten_circleCount_eq_zero_of_cap S hcircleBlock (by omega)
  have hc7 : S.circleCount 7 = 0 :=
    ten_circleCount_eq_zero_of_cap S hcircleBlock (by omega)
  have hc8 : S.circleCount 8 = 0 :=
    ten_circleCount_eq_zero_of_cap S hcircleBlock (by omega)
  have hc9 : S.circleCount 9 = 0 :=
    ten_circleCount_eq_zero_of_cap S hcircleBlock (by omega)
  have hc10 : S.circleCount 10 = 0 :=
    ten_circleCount_eq_zero_of_cap S hcircleBlock (by omega)
  have htriple := S.triple_partition_by_size
  rw [hcard] at htriple
  norm_num [Finset.sum_range_succ, Nat.choose,
    hb6, hb7, hb8, hb9, hb10] at htriple
  have hsplit3 := S.blockCount_eq_lineCount_add_circleCount 3
  have hsplit4 := S.blockCount_eq_lineCount_add_circleCount 4
  have hsplit5 := S.blockCount_eq_lineCount_add_circleCount 5
  rw [hc5, Nat.add_zero] at hsplit5
  have htotal := S.totalCircleCount_eq_sum_circleCount
  rw [hcard] at htotal
  norm_num [Finset.sum_range_succ,
    hc0, hc1, hc2, hc5, hc6, hc7, hc8, hc9, hc10] at htotal
  have htotalBridge : S.totalCircleCount = Erdos506.V4.circleCount cfg := by
    rw [totalCircleCount_eq_card_determinedCircle,
      ← Erdos506.V3.circleCount_eq_card_determinedCircle]
  have hcountS : S.totalCircleCount ≤ 32 := by
    rw [htotalBridge]
    exact hcount
  have hlocal (p : α) :
      S.blockDegree 3 p + 3 * S.blockDegree 4 p +
          6 * S.blockDegree 5 p = 36 ∧
        6 ≤ S.blockDegree 3 p := by
    have hk := KM.pivot_three_block_bound cfg hadm
      (by omega) (by omega) p
    change 3 * (Fintype.card α - 1) ≤
      7 * S.blockDegree 3 p at hk
    rw [hcard] at hk
    norm_num at hk
    exact ten_cap_four_local_pair S hcard hcap p hk
  have hsumLower : 10 * 6 ≤ ∑ p : α, S.blockDegree 3 p := by
    calc
      10 * 6 = ∑ _p : α, 6 := by simp [hcard]
      _ ≤ ∑ p : α, S.blockDegree 3 p :=
        Finset.sum_le_sum fun p _hp => (hlocal p).2
  have hinc3 := S.block_incidence 3
  rw [hinc3] at hsumLower
  have hB3lower : 20 ≤ S.blockCount 3 := by omega
  have hline : 3 * (S.lineCount 3 : ℤ) +
      7 * (S.lineCount 4 : ℤ) + 12 * (S.lineCount 5 : ℤ) ≤ 42 := by
    have hrow :=
      globalLineRow_le_choose_two_sub_three_of_realPlaneMelchior
        Mel cfg hadm
    change S.globalLineRow ≤
      (Nat.choose (Fintype.card α) 2 : ℤ) - 3 at hrow
    rw [ten_globalLineRow_eq_three_four_five S hcard hcap, hcard] at hrow
    norm_num [Nat.choose] at hrow
    exact hrow
  have hdefect : -3 * (S.circleCount 3 : ℤ) +
      6 * (S.lineCount 3 : ℤ) + 16 * (S.lineCount 4 : ℤ) +
      30 * (S.lineCount 5 : ℤ) ≤ 60 := by
    have hrow := rowD_le_n_mul_n_sub_four_of_realPlaneMelchior
      Mel cfg hadm (by omega)
    change S.defectRow ≤
      (Fintype.card α : ℤ) * ((Fintype.card α : ℤ) - 4) at hrow
    rw [ten_defectRow_eq_three_four_five S hcard hcap hcircleBlock,
      hcard] at hrow
    norm_num at hrow
    exact hrow
  obtain ⟨hB3, hB4, hB5, hL3, hL4, hL5, hC3, hC4, hC⟩ :=
    ten_cap_four_scalar_profile htriple hsplit3 hsplit4 hsplit5
      htotal hcountS hB3lower hline hdefect
  have hd5 (p : α) : S.blockDegree 5 p = 0 :=
    ten_blockDegree_eq_zero_of_blockCount_eq_zero S 5 p hB5
  have hinc3Z : (∑ p : α, (S.blockDegree 3 p : ℤ)) = 60 := by
    have hinc := S.block_incidence 3
    rw [hB3] at hinc
    norm_num at hinc
    exact_mod_cast hinc
  have hsumSlack :
      (∑ p : α, ((S.blockDegree 3 p : ℤ) - 6)) = 0 := by
    calc
      (∑ p : α, ((S.blockDegree 3 p : ℤ) - 6)) =
          (∑ p : α, (S.blockDegree 3 p : ℤ)) -
            ∑ _p : α, (6 : ℤ) := by
              rw [Finset.sum_sub_distrib]
      _ = 60 - 60 := by rw [hinc3Z]; simp [hcard]
      _ = 0 := by norm_num
  have hdegrees (p : α) : S.blockDegree 3 p = 6 ∧
      S.blockDegree 4 p = 10 ∧ S.blockDegree 5 p = 0 := by
    have htermNonneg (q : α) :
        0 ≤ (S.blockDegree 3 q : ℤ) - 6 := by
      have := (hlocal q).2
      omega
    have htermLe : (S.blockDegree 3 p : ℤ) - 6 ≤
        ∑ q : α, ((S.blockDegree 3 q : ℤ) - 6) :=
      Finset.single_le_sum (fun q _hq => htermNonneg q) (Finset.mem_univ p)
    rw [hsumSlack] at htermLe
    have hd3 : S.blockDegree 3 p = 6 := by
      have := (hlocal p).2
      omega
    have hpair := (hlocal p).1
    have hd5p := hd5 p
    have hd4 : S.blockDegree 4 p = 10 := by omega
    exact ⟨hd3, hd4, hd5p⟩
  exact ⟨hB3, hB4, hB5, hL3, hL4, hL5, hC3, hC4, hC, hdegrees⟩

end CircleCapFour

end Erdos506.V1
