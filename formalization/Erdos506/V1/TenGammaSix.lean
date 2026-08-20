import Erdos506.Incidence.SixCirclePrinciple
import Erdos506.V1.FiniteCaps
import Erdos506.V1.UniversalRows

/-!
# The ten-point branch with a selected six-circle

The finite core below is the integer Farkas certificate printed in
`02_finite_n10_n12.tex`, lines 784--831.  Its rows come from the abstract
`BlockSystem` API; the nine-entry coefficient table is not assumed.
-/

namespace Erdos506.V1

open Erdos506.Block
open Erdos506.Block.BlockSystem
open Erdos506.Incidence
open Erdos506.V4
open scoped BigOperators

universe u v

section FiniteCertificate

variable {Point : Type u} {Block : Type v}
  [Fintype Point] [Fintype Block] [DecidableEq Point]

/-- Number of labels of a block on the selected six-set. -/
def tenGammaInside (S : BlockSystem Point Block) (D : Finset Point)
    (b : Block) : ℕ :=
  (S.support b ∩ D).card

/-- Number of labels of a block away from the selected six-set. -/
def tenGammaOutside (S : BlockSystem Point Block) (D : Finset Point)
    (b : Block) : ℕ :=
  (S.support b \ D).card

theorem tenGammaInside_add_tenGammaOutside
    (S : BlockSystem Point Block) (D : Finset Point) (b : Block) :
    tenGammaInside S D b + tenGammaOutside S D b =
      (S.support b).card := by
  exact Finset.card_inter_add_card_sdiff (S.support b) D

/-- The U17 left side in abstract tagged-block notation. -/
def tenGammaU17Weight (S : BlockSystem Point Block)
    (D : Finset Point) : ℕ :=
  ∑ b : Block,
    if S.kind b = .circle ∧ tenGammaInside S D b = 2 then
      Nat.choose (tenGammaOutside S D b) 2
    else 0

/-- The cleared integer coefficient of a block in the paper's Farkas sum.
The arguments are its tag, whether it is the selected circle, and its two
relative trace sizes. -/
def tenGammaFarkasCoefficient
    (k : BlockKind) (selected i j : ℕ) : ℤ :=
  (if k = .line then
      24 * ((i * j : ℕ) : ℤ) +
        12 * (if 3 ≤ i + j then
          (Nat.choose (i + j) 2 : ℤ) + ((i + j : ℕ) : ℤ) - 3
        else 0)
    else
      84 + 82 * (if i = 2 then (Nat.choose j 2 : ℤ) else 0)) -
    21 * (Nat.choose j 3 : ℤ) +
    (i : ℤ) * (Nat.choose j 2 : ℤ) -
    84 * (Nat.choose i 2 : ℤ) * (j : ℤ) +
    684 * (Nat.choose i 3 : ℤ) -
    13764 * (selected : ℤ)

/-- The selected circle has coefficient zero. -/
theorem tenGammaFarkasCoefficient_selected :
    tenGammaFarkasCoefficient .circle 1 6 0 = 0 := by
  simp [tenGammaFarkasCoefficient]
  norm_num [Nat.choose]

/-- Pointwise nonnegativity for a nonselected line.  This is checked from
the support bounds and the explicit polynomial, rather than imported as a
coefficient table. -/
theorem tenGammaFarkasCoefficient_line_nonneg
    (i j : ℕ) (hi : i ≤ 2) (hj : j ≤ 4)
    (hmin : 2 ≤ i + j) (hcap : i + j ≤ 6) :
    0 ≤ tenGammaFarkasCoefficient .line 0 i j := by
  simp only [tenGammaFarkasCoefficient]
  interval_cases i <;>
    interval_cases j <;>
    norm_num [Nat.choose] at *

/-- Pointwise nonnegativity for a nonselected circle. -/
theorem tenGammaFarkasCoefficient_circle_nonneg
    (i j : ℕ) (hi : i ≤ 2) (hj : j ≤ 4)
    (hmin : 3 ≤ i + j) (hcap : i + j ≤ 6) :
    0 ≤ tenGammaFarkasCoefficient .circle 0 i j := by
  simp only [tenGammaFarkasCoefficient,
    if_neg (by decide : BlockKind.circle ≠ BlockKind.line)]
  interval_cases i <;>
    interval_cases j <;>
    norm_num [Nat.choose] at *

/-- The actual coefficient attached to a block relative to `D` and the
distinguished block `gamma`. -/
def tenGammaBlockCoefficient [DecidableEq Block]
    (S : BlockSystem Point Block)
    (D : Finset Point) (gamma b : Block) : ℤ :=
  if b = gamma then
    tenGammaFarkasCoefficient (S.kind b) 1
      (tenGammaInside S D b) (tenGammaOutside S D b)
  else
    tenGammaFarkasCoefficient (S.kind b) 0
      (tenGammaInside S D b) (tenGammaOutside S D b)

/-- Every block coefficient in the ten-point certificate is nonnegative.
The proof derives the relative trace ranges from ownership and support caps,
then evaluates the explicit formula over those finite ranges. -/
theorem tenGammaBlockCoefficient_nonneg
    [DecidableEq Block]
    (S : BlockSystem Point Block) (D : Finset Point) (gamma b : Block)
    (hpoint : Fintype.card Point = 10) (hD : D.card = 6)
    (hgammaKind : S.kind gamma = .circle)
    (hgammaSupport : S.support gamma = D)
    (hcircleCap : ∀ c, S.kind c = .circle → (S.support c).card ≤ 6)
    (hlineCap : ∀ L, S.kind L = .line → (S.support L).card ≤ 6) :
    0 ≤ tenGammaBlockCoefficient S D gamma b := by
  by_cases hbgamma : b = gamma
  · subst b
    have hi : tenGammaInside S D gamma = 6 := by
      simp [tenGammaInside, hgammaSupport, hD]
    have hj : tenGammaOutside S D gamma = 0 := by
      simp [tenGammaOutside, hgammaSupport]
    simp [tenGammaBlockCoefficient, hi, hj, hgammaKind,
      tenGammaFarkasCoefficient_selected]
  · have hi : tenGammaInside S D b ≤ 2 := by
      have hinter := S.distinct_block_inter_card_lt_three hbgamma
      rw [hgammaSupport] at hinter
      exact Nat.le_of_lt_succ hinter
    have hcomp : (Finset.univ \ D).card = 4 := by
      rw [Finset.card_sdiff_of_subset (Finset.subset_univ D),
        Finset.card_univ, hpoint, hD]
    have hj : tenGammaOutside S D b ≤ 4 := by
      have hsubset : S.support b \ D ⊆ Finset.univ \ D := by
        intro p hp
        simp only [Finset.mem_sdiff] at hp ⊢
        exact ⟨Finset.mem_univ p, hp.2⟩
      have hle := Finset.card_le_card hsubset
      simpa [tenGammaOutside, hcomp] using hle
    have hsum := tenGammaInside_add_tenGammaOutside S D b
    cases hkind : S.kind b with
    | line =>
        have hmin : 2 ≤ tenGammaInside S D b + tenGammaOutside S D b := by
          rw [hsum]
          exact S.line_min b hkind
        have hcap : tenGammaInside S D b + tenGammaOutside S D b ≤ 6 := by
          rw [hsum]
          exact hlineCap b hkind
        simp only [tenGammaBlockCoefficient, if_neg hbgamma, hkind]
        exact tenGammaFarkasCoefficient_line_nonneg _ _ hi hj hmin hcap
    | circle =>
        have hmin : 3 ≤ tenGammaInside S D b + tenGammaOutside S D b := by
          rw [hsum]
          exact S.circle_min b hkind
        have hcap : tenGammaInside S D b + tenGammaOutside S D b ≤ 6 := by
          rw [hsum]
          exact hcircleCap b hkind
        simp only [tenGammaBlockCoefficient, if_neg hbgamma, hkind]
        exact tenGammaFarkasCoefficient_circle_nonneg _ _ hi hj hmin hcap

/-- The four exact relative triple rows at the six--four split, in the
integer form used by the certificate. -/
theorem tenGamma_relative_triple_rows
    (S : BlockSystem Point Block) (D : Finset Point)
    (hpoint : Fintype.card Point = 10) (hD : D.card = 6) :
    (∑ b : Block, (Nat.choose (tenGammaOutside S D b) 3 : ℤ)) = 4 ∧
    (∑ b : Block, (tenGammaInside S D b : ℤ) *
      (Nat.choose (tenGammaOutside S D b) 2 : ℤ)) = 36 ∧
    (∑ b : Block, (Nat.choose (tenGammaInside S D b) 2 : ℤ) *
      (tenGammaOutside S D b : ℤ)) = 60 ∧
    (∑ b : Block, (Nat.choose (tenGammaInside S D b) 3 : ℤ)) = 20 := by
  have h0 := S.relative_triple_partition D 0 (by omega)
  have h1 := S.relative_triple_partition D 1 (by omega)
  have h2 := S.relative_triple_partition D 2 (by omega)
  have h3 := S.relative_triple_partition D 3 (by omega)
  rw [hpoint, hD] at h0 h1 h2 h3
  norm_num [tenGammaInside, tenGammaOutside, Nat.choose] at h0 h1 h2 h3
  constructor
  · exact_mod_cast h0
  constructor
  · exact_mod_cast h1
  constructor
  · exact_mod_cast h2
  · exact_mod_cast h3

/-- The mixed inside--outside line pairs sum to `6 * 4 = 24`. -/
theorem tenGamma_relative_line_pair_row
    (S : BlockSystem Point Block) (D : Finset Point)
    (hpoint : Fintype.card Point = 10) (hD : D.card = 6) :
    (∑ b : LineBlock S,
      (tenGammaInside S D b.1 : ℤ) *
        (tenGammaOutside S D b.1 : ℤ)) = 24 := by
  have h := S.relative_line_pair_partition D 1 (by omega)
  rw [hpoint, hD] at h
  norm_num [tenGammaInside, tenGammaOutside, Nat.choose] at h
  exact_mod_cast h

/-- The local line expression in the Farkas coefficient sums to the abstract
global Melchior line row. -/
theorem tenGamma_line_row_sum
    (S : BlockSystem Point Block) (D : Finset Point) :
    (∑ b : LineBlock S,
      if 3 ≤ tenGammaInside S D b.1 + tenGammaOutside S D b.1 then
        (Nat.choose
            (tenGammaInside S D b.1 + tenGammaOutside S D b.1) 2 : ℤ) +
          ((tenGammaInside S D b.1 +
            tenGammaOutside S D b.1 : ℕ) : ℤ) - 3
      else 0) = S.globalLineRow := by
  unfold BlockSystem.globalLineRow
  apply Fintype.sum_congr
  intro b
  rw [tenGammaInside_add_tenGammaOutside]

/-- Replace a sum over line-tagged ambient blocks by the corresponding sum
over the line-block subtype. -/
theorem tenGamma_sum_if_line
    (S : BlockSystem Point Block) (f : Block → ℤ) :
    (∑ b : Block, if S.kind b = .line then f b else 0) =
      ∑ b : LineBlock S, f b.1 := by
  classical
  calc
    (∑ b : Block, if S.kind b = .line then f b else 0) =
        ∑ b ∈ S.blocksOfKind .line, f b := by
      simp [BlockSystem.blocksOfKind, Finset.sum_filter]
    _ = ∑ b : LineBlock S, f b.1 := by
      simpa [BlockSystem.blocksOfKind] using
        (Finset.sum_subtype (S.blocksOfKind .line)
          (fun b => by simp [BlockSystem.blocksOfKind]) f)

/-- The indicator of circle-tagged blocks sums to the total circle count. -/
theorem tenGamma_sum_circle_indicator (S : BlockSystem Point Block) :
    (∑ b : Block, if S.kind b = .circle then (1 : ℤ) else 0) =
      (S.totalCircleCount : ℤ) := by
  classical
  rw [← Finset.sum_filter]
  simp [BlockSystem.totalCircleCount, BlockSystem.blocksOfKind]

/-- The distinguished-block Kronecker indicator has total mass one. -/
theorem tenGamma_sum_selected_indicator [DecidableEq Block]
    (gamma : Block) :
    (∑ b : Block, if b = gamma then (1 : ℤ) else 0) = 1 := by
  simp

/-- Cast the natural U17 weight to the integer sum used by Farkas. -/
theorem tenGammaU17Weight_cast
    (S : BlockSystem Point Block) (D : Finset Point) :
    (∑ b : Block,
      if S.kind b = .circle ∧ tenGammaInside S D b = 2 then
        (Nat.choose (tenGammaOutside S D b) 2 : ℤ)
      else 0) = (tenGammaU17Weight S D : ℤ) := by
  rw [tenGammaU17Weight, Nat.cast_sum]
  apply Fintype.sum_congr
  intro b
  by_cases h : S.kind b = .circle ∧ tenGammaInside S D b = 2 <;>
    simp [h]

/-- Expand one actual block coefficient into the eight paper rows and the
distinguished-circle correction. -/
theorem tenGammaBlockCoefficient_eq_rows [DecidableEq Block]
    (S : BlockSystem Point Block) (D : Finset Point) (gamma b : Block) :
    tenGammaBlockCoefficient S D gamma b =
      24 * (if S.kind b = .line then
        ((tenGammaInside S D b * tenGammaOutside S D b : ℕ) : ℤ)
      else 0) +
      12 * (if S.kind b = .line then
        (if 3 ≤ tenGammaInside S D b + tenGammaOutside S D b then
          (Nat.choose
              (tenGammaInside S D b + tenGammaOutside S D b) 2 : ℤ) +
            ((tenGammaInside S D b +
              tenGammaOutside S D b : ℕ) : ℤ) - 3
        else 0)
      else 0) +
      84 * (if S.kind b = .circle then (1 : ℤ) else 0) +
      82 * (if S.kind b = .circle ∧ tenGammaInside S D b = 2 then
        (Nat.choose (tenGammaOutside S D b) 2 : ℤ)
      else 0) -
      21 * (Nat.choose (tenGammaOutside S D b) 3 : ℤ) +
      (tenGammaInside S D b : ℤ) *
        (Nat.choose (tenGammaOutside S D b) 2 : ℤ) -
      84 * (Nat.choose (tenGammaInside S D b) 2 : ℤ) *
        (tenGammaOutside S D b : ℤ) +
      684 * (Nat.choose (tenGammaInside S D b) 3 : ℤ) -
      13764 * (if b = gamma then (1 : ℤ) else 0) := by
  cases hkind : S.kind b with
  | line =>
      by_cases hbgamma : b = gamma
      · subst b
        simp [tenGammaBlockCoefficient, tenGammaFarkasCoefficient, hkind]
      · simp [tenGammaBlockCoefficient, tenGammaFarkasCoefficient,
          hkind, hbgamma]
  | circle =>
      by_cases hbgamma : b = gamma
      · subst b
        simp [tenGammaBlockCoefficient, tenGammaFarkasCoefficient, hkind]
      · simp [tenGammaBlockCoefficient, tenGammaFarkasCoefficient,
          hkind, hbgamma]

/-- Exact evaluation of the summed left side of the Farkas certificate. -/
theorem sum_tenGammaBlockCoefficient_eq
    [DecidableEq Block]
    (S : BlockSystem Point Block) (D : Finset Point) (gamma : Block)
    (hpoint : Fintype.card Point = 10) (hD : D.card = 6) :
    (∑ b : Block, tenGammaBlockCoefficient S D gamma b) =
      24 * 24 + 84 * (S.totalCircleCount : ℤ) +
        12 * S.globalLineRow + 82 * (tenGammaU17Weight S D : ℤ) -
        21 * 4 + 36 - 84 * 60 + 684 * 20 - 13764 := by
  classical
  obtain ⟨hrow0, hrow1, hrow2, hrow3⟩ :=
    tenGamma_relative_triple_rows S D hpoint hD
  have hmixed :
      (∑ b : Block, if S.kind b = .line then
        ((tenGammaInside S D b * tenGammaOutside S D b : ℕ) : ℤ)
      else 0) = 24 := by
    rw [tenGamma_sum_if_line]
    simpa only [Nat.cast_mul] using
      tenGamma_relative_line_pair_row S D hpoint hD
  have hline :
      (∑ b : Block, if S.kind b = .line then
        (if 3 ≤ tenGammaInside S D b + tenGammaOutside S D b then
          (Nat.choose
              (tenGammaInside S D b + tenGammaOutside S D b) 2 : ℤ) +
            ((tenGammaInside S D b +
              tenGammaOutside S D b : ℕ) : ℤ) - 3
        else 0)
      else 0) = S.globalLineRow := by
    rw [tenGamma_sum_if_line]
    exact tenGamma_line_row_sum S D
  have hcircle := tenGamma_sum_circle_indicator S
  have hweight := tenGammaU17Weight_cast S D
  have hselected := tenGamma_sum_selected_indicator gamma
  have hrow2scaled :
      (∑ b : Block,
        84 * (Nat.choose (tenGammaInside S D b) 2 : ℤ) *
          (tenGammaOutside S D b : ℤ)) = 84 * 60 := by
    calc
      (∑ b : Block,
          84 * (Nat.choose (tenGammaInside S D b) 2 : ℤ) *
            (tenGammaOutside S D b : ℤ)) =
          84 * ∑ b : Block,
            (Nat.choose (tenGammaInside S D b) 2 : ℤ) *
              (tenGammaOutside S D b : ℤ) := by
        rw [Finset.mul_sum]
        apply Fintype.sum_congr
        intro b
        ring
      _ = 84 * 60 := by rw [hrow2]
  simp_rw [tenGammaBlockCoefficient_eq_rows]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ← Finset.mul_sum]
  rw [hmixed, hline, hcircle, hweight, hrow0, hrow1, hrow2scaled, hrow3,
    hselected]
  ring

/-- The solver-free ten-point, selected-six-circle Farkas contradiction. -/
theorem tenGammaSix_farkas
    [DecidableEq Block]
    (S : BlockSystem Point Block) (D : Finset Point) (gamma : Block)
    (hpoint : Fintype.card Point = 10) (hD : D.card = 6)
    (hgammaKind : S.kind gamma = .circle)
    (hgammaSupport : S.support gamma = D)
    (hcircleCap : ∀ c, S.kind c = .circle → (S.support c).card ≤ 6)
    (hlineCap : ∀ L, S.kind L = .line → (S.support L).card ≤ 6)
    (hcircles : S.totalCircleCount ≤ 32)
    (hlineRow : S.globalLineRow ≤ 42)
    (hU17 : tenGammaU17Weight S D ≤ 17) : False := by
  have hnonneg :
      0 ≤ ∑ b : Block, tenGammaBlockCoefficient S D gamma b :=
    Finset.sum_nonneg fun b _hb =>
      tenGammaBlockCoefficient_nonneg S D gamma b hpoint hD
        hgammaKind hgammaSupport hcircleCap hlineCap
  have hexact := sum_tenGammaBlockCoefficient_eq
    S D gamma hpoint hD
  have hcirclesZ : (S.totalCircleCount : ℤ) ≤ 32 := by
    exact_mod_cast hcircles
  have hU17Z : (tenGammaU17Weight S D : ℤ) ≤ 17 := by
    exact_mod_cast hU17
  have hupper :
      (∑ b : Block, tenGammaBlockCoefficient S D gamma b) ≤ -10 := by
    rw [hexact]
    omega
  omega

end FiniteCertificate

section GeometricBridge

/-- The geometric U17 principle is exactly the abstract U17 weight for the
geometric block system and the full four-point complement of `gamma`. -/
theorem tenGammaU17Weight_le_of_realPlaneSixCircleU17
    {α : Type u} [Fintype α] [DecidableEq α]
    (U17 : RealPlaneSixCircleU17Principle.{u})
    (cfg : Configuration α) (gamma : DeterminedCircle cfg)
    (hcard : Fintype.card α = 10)
    (hgamma : (circleTrace cfg gamma.1).card = 6) :
    tenGammaU17Weight (blockSystem cfg) (circleTrace cfg gamma.1) ≤ 17 := by
  classical
  let D : Finset α := circleTrace cfg gamma.1
  let Y : Finset α := Finset.univ \ D
  have hY : Y.card = 4 := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ D),
      Finset.card_univ, hcard]
    change D.card = 6 at hgamma
    rw [hgamma]
  have hdisjoint : Disjoint D Y := by
    apply Finset.disjoint_left.mpr
    intro p hpD hpY
    exact (Finset.mem_sdiff.mp hpY).2 hpD
  have hu17 := U17.u17 cfg gamma hgamma Y hY hdisjoint
  have htraceDifference (c : DeterminedCircle cfg) :
      circleTrace cfg c.1 \ circleTrace cfg gamma.1 =
        circleTrace cfg c.1 ∩
          (Finset.univ \ circleTrace cfg gamma.1) := by
    ext p
    simp
  have hweight :
      tenGammaU17Weight (blockSystem cfg) D =
        ∑ c : DeterminedCircle cfg,
          if (circleTrace cfg c.1 ∩ D).card = 2 then
            Nat.choose (circleTrace cfg c.1 ∩ Y).card 2
          else 0 := by
    simp [tenGammaU17Weight, tenGammaInside, tenGammaOutside,
      blockSystem, geometricBlockSystem, geometricBlockKind,
      geometricBlockSupport, D, Y, Fintype.sum_sum_type,
      htraceDifference]
  rw [hweight]
  simpa [D] using hu17

/-- An admissible ten-point configuration with a selected six-circle and no
circle trace larger than six determines at least thirty-three circles. -/
theorem circleCount_ge_thirty_three_of_ten_of_selected_six_circle
    {α : Type u} [Fintype α] [DecidableEq α]
    (Mel : RealPlaneMelchiorPrinciple.{u})
    (U17 : RealPlaneSixCircleU17Principle.{u})
    (cfg : Configuration α) (hadm : Admissible cfg)
    (hcard : Fintype.card α = 10)
    (gamma : DeterminedCircle cfg)
    (hgamma : (circleTrace cfg gamma.1).card = 6)
    (hcircleCap : ∀ c : DeterminedCircle cfg,
      (circleTrace cfg c.1).card ≤ 6) :
    33 ≤ Erdos506.V4.circleCount cfg := by
  classical
  by_contra hnot
  have hcount : Erdos506.V4.circleCount cfg ≤ 32 := by omega
  let D : Finset α := circleTrace cfg gamma.1
  let gammaBlock : GeometricBlock cfg := Sum.inr gamma
  have hD : D.card = 6 := hgamma
  have hgammaKind : (blockSystem cfg).kind gammaBlock = .circle := rfl
  have hgammaSupport : (blockSystem cfg).support gammaBlock = D := rfl
  have hcircles : (blockSystem cfg).totalCircleCount ≤ 32 := by
    rw [totalCircleCount_eq_card_determinedCircle,
      ← Erdos506.V3.circleCount_eq_card_determinedCircle]
    exact hcount
  have hlineRow : (blockSystem cfg).globalLineRow ≤ 42 := by
    have hrow :=
      globalLineRow_le_choose_two_sub_three_of_realPlaneMelchior
        Mel cfg hadm
    change (blockSystem cfg).globalLineRow ≤
      (Nat.choose (Fintype.card α) 2 : ℤ) - 3 at hrow
    rw [hcard] at hrow
    norm_num [Nat.choose] at hrow ⊢
    exact hrow
  have hcircleBlockCap : ∀ b : GeometricBlock cfg,
      (blockSystem cfg).kind b = .circle →
        ((blockSystem cfg).support b).card ≤ 6 := by
    intro b hb
    cases b with
    | inl L => cases hb
    | inr c => exact hcircleCap c
  have hlineBlockCap : ∀ b : GeometricBlock cfg,
      (blockSystem cfg).kind b = .line →
        ((blockSystem cfg).support b).card ≤ 6 := by
    intro b hb
    cases b with
    | inl L =>
        have hfive := lineSupport_card_le_five_of_ten_of_circleCount_le
          cfg hadm hcard hcount L
        exact hfive.trans (by omega)
    | inr c => cases hb
  have hU17 : tenGammaU17Weight (blockSystem cfg) D ≤ 17 := by
    simpa [D] using
      tenGammaU17Weight_le_of_realPlaneSixCircleU17
        U17 cfg gamma hcard hgamma
  exact tenGammaSix_farkas (blockSystem cfg) D gammaBlock
    hcard hD hgammaKind hgammaSupport hcircleBlockCap hlineBlockCap
    hcircles hlineRow hU17

end GeometricBridge

end Erdos506.V1
