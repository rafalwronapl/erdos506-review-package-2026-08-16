import Erdos506.V1.ThirteenSixCore

/-!
# Thirteen-point selected-six conservation, part A

This module materializes the common relative census together with the
circle-count and the first three conservation rows.  The theorem boundaries
keep the finite tables cacheable before the remaining affine moments.
-/

namespace Erdos506.V1

open Erdos506.Block
open Erdos506.Block.BlockSystem
open Erdos506.Incidence
open Erdos506.V4
open scoped BigOperators

universe u v

section RelativeCensus

variable {Point : Type u} {Block : Type v}
  [Fintype Point] [Fintype Block] [DecidableEq Point]

local instance thirteenSixBlockKindFintype : Fintype BlockKind where
  elems := {.line, .circle}
  complete := by
    intro kind
    cases kind <;> simp

theorem thirteenSix_sum_blockKind_int (f : BlockKind → Int) :
    (∑ kind : BlockKind, f kind) = f .line + f .circle := by
  change ∑ kind ∈ ({.line, .circle} : Finset BlockKind), f kind = _
  rw [Finset.sum_insert (by decide), Finset.sum_singleton]

theorem thirteenSix_sum_range_pair_selector
    (f : Nat → Nat → Int) (g x gBound xBound : Nat)
    (hg : g < gBound) (hx : x < xBound) :
    (∑ g' ∈ Finset.range gBound, ∑ x' ∈ Finset.range xBound,
      if g = g' ∧ x = x' then f g' x' else 0) = f g x := by
  classical
  rw [Finset.sum_eq_single g]
  · rw [Finset.sum_eq_single x]
    · simp
    · intro x' _hx' hxne
      have hne : x ≠ x' := Ne.symm hxne
      simp [hne]
    · intro hxnot
      exact (hxnot (Finset.mem_range.mpr hx)).elim
  · intro g' _hg' hgne
    have hne : g ≠ g' := Ne.symm hgne
    simp [hne]
  · intro hgnot
    exact (hgnot (Finset.mem_range.mpr hg)).elim

theorem thirteenSix_relative_selector_sum
    (f : BlockKind → Nat → Nat → Int)
    (kind : BlockKind) (g x gBound xBound : Nat)
    (hg : g < gBound) (hx : x < xBound) :
    (∑ kind' : BlockKind, ∑ g' ∈ Finset.range gBound,
      ∑ x' ∈ Finset.range xBound,
        if kind = kind' ∧ g = g' ∧ x = x' then
          f kind' g' x' else 0) = f kind g x := by
  cases kind with
  | circle =>
      rw [thirteenSix_sum_blockKind_int]
      simpa using (thirteenSix_sum_range_pair_selector
        (fun g' x' => f .circle g' x') g x gBound xBound hg hx)
  | line =>
      rw [thirteenSix_sum_blockKind_int]
      simpa using (thirteenSix_sum_range_pair_selector
        (fun g' x' => f .line g' x') g x gBound xBound hg hx)

theorem thirteenSix_relative_selector_sum_eq_zero_of_g_ge
    (f : BlockKind → Nat → Nat → Int)
    (kind : BlockKind) (g x gBound xBound : Nat)
    (hg : gBound ≤ g) :
    (∑ kind' : BlockKind, ∑ g' ∈ Finset.range gBound,
      ∑ x' ∈ Finset.range xBound,
        if kind = kind' ∧ g = g' ∧ x = x' then
          f kind' g' x' else 0) = 0 := by
  apply Fintype.sum_eq_zero
  intro kind'
  apply Finset.sum_eq_zero
  intro g' hg'
  have hg'lt := Finset.mem_range.mp hg'
  apply Finset.sum_eq_zero
  intro x' _hx'
  rw [if_neg]
  intro hcell
  omega

theorem thirteenSix_circle_relativeCount_eq_zero_of_invalid
    (S : BlockSystem Point Block) (D : Finset Point)
    (hcircleCap : ∀ c, S.kind c = .circle → (S.support c).card ≤ 6)
    (g x : Nat) (hbad : g + x < 3 ∨ 6 < g + x) :
    thirteenSixRelativeCount S D .circle g x = 0 := by
  classical
  unfold thirteenSixRelativeCount
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro b hb
  unfold thirteenSixRelativeBlocks at hb
  have hspec := (Finset.mem_filter.mp hb).2
  have hsum := thirteenSixInside_add_thirteenSixOutside S D b
  have hmin := S.circle_min b hspec.1
  have hcap := hcircleCap b hspec.1
  rw [← hsum, hspec.2.1, hspec.2.2] at hmin hcap
  omega

theorem thirteenSix_line_relativeCount_eq_zero_of_invalid
    (S : BlockSystem Point Block) (D : Finset Point)
    (hlineCap : ∀ L, S.kind L = .line → (S.support L).card ≤ 6)
    (g x : Nat) (hbad : g + x < 2 ∨ 6 < g + x) :
    thirteenSixRelativeCount S D .line g x = 0 := by
  classical
  unfold thirteenSixRelativeCount
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro b hb
  unfold thirteenSixRelativeBlocks at hb
  have hspec := (Finset.mem_filter.mp hb).2
  have hsum := thirteenSixInside_add_thirteenSixOutside S D b
  have hmin := S.line_min b hspec.1
  have hcap := hlineCap b hspec.1
  rw [← hsum, hspec.2.1, hspec.2.2] at hmin hcap
  omega

/-- Every block under the six-cap belongs to exactly one of the finite
relative cells.  This is the common grouping lemma for all eight affine
conservation rows. -/
theorem thirteenSix_sum_by_relativeCount
    (S : BlockSystem Point Block) (D : Finset Point) (hD : D.card = 6)
    (hcircleCap : ∀ c, S.kind c = .circle → (S.support c).card ≤ 6)
    (hlineCap : ∀ L, S.kind L = .line → (S.support L).card ≤ 6)
    (f : BlockKind → Nat → Nat → Int) :
    (∑ b : Block,
      f (S.kind b) (thirteenSixInside S D b) (thirteenSixOutside S D b)) =
      ∑ kind : BlockKind, ∑ g ∈ Finset.range 7, ∑ x ∈ Finset.range 7,
        f kind g x * (thirteenSixRelativeCount S D kind g x : Int) := by
  classical
  have hgBound (b : Block) : thirteenSixInside S D b < 7 := by
    have hle : (S.support b ∩ D).card ≤ D.card :=
      Finset.card_le_card Finset.inter_subset_right
    change (S.support b ∩ D).card < 7
    omega
  have hxBound (b : Block) : thirteenSixOutside S D b < 7 := by
    have hsum := thirteenSixInside_add_thirteenSixOutside S D b
    cases hk : S.kind b with
    | circle =>
        have hcap := hcircleCap b hk
        rw [← hsum] at hcap
        omega
    | line =>
        have hcap := hlineCap b hk
        rw [← hsum] at hcap
        omega
  have hpointwise (b : Block) :
      f (S.kind b) (thirteenSixInside S D b) (thirteenSixOutside S D b) =
        ∑ kind : BlockKind, ∑ g ∈ Finset.range 7, ∑ x ∈ Finset.range 7,
          if S.kind b = kind ∧ thirteenSixInside S D b = g ∧
              thirteenSixOutside S D b = x then f kind g x else 0 := by
    exact (thirteenSix_relative_selector_sum f (S.kind b)
      (thirteenSixInside S D b) (thirteenSixOutside S D b) 7 7
      (hgBound b) (hxBound b)).symm
  calc
    (∑ b : Block,
      f (S.kind b) (thirteenSixInside S D b) (thirteenSixOutside S D b)) =
        ∑ b : Block, ∑ kind : BlockKind,
          ∑ g ∈ Finset.range 7, ∑ x ∈ Finset.range 7,
            if S.kind b = kind ∧ thirteenSixInside S D b = g ∧
                thirteenSixOutside S D b = x then f kind g x else 0 := by
      apply Fintype.sum_congr
      exact hpointwise
    _ = ∑ kind : BlockKind, ∑ g ∈ Finset.range 7,
          ∑ x ∈ Finset.range 7, ∑ b : Block,
            if S.kind b = kind ∧ thirteenSixInside S D b = g ∧
                thirteenSixOutside S D b = x then f kind g x else 0 := by
      rw [Finset.sum_comm]
      apply Fintype.sum_congr
      intro kind
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro g _hg
      rw [Finset.sum_comm]
    _ = _ := by
      apply Fintype.sum_congr
      intro kind
      apply Finset.sum_congr rfl
      intro g _hg
      apply Finset.sum_congr rfl
      intro x _hx
      exact thirteenSix_sum_relative_indicator_int S D kind g x (f kind g x)

theorem thirteenSix_sum_by_relativeCount_selected
    (S : BlockSystem Point Block) (D : Finset Point) (gamma : Block)
    (hD : D.card = 6) (hgammaKind : S.kind gamma = .circle)
    (hgammaSupport : S.support gamma = D)
    (hcircleCap : ∀ c, S.kind c = .circle → (S.support c).card ≤ 6)
    (hlineCap : ∀ L, S.kind L = .line → (S.support L).card ≤ 6)
    (f : BlockKind → Nat → Nat → Int) :
    (∑ b : Block,
      f (S.kind b) (thirteenSixInside S D b) (thirteenSixOutside S D b)) =
      f .circle 6 0 +
      ∑ kind : BlockKind, ∑ g ∈ Finset.range 3, ∑ x ∈ Finset.range 7,
        f kind g x * (thirteenSixRelativeCount S D kind g x : Int) := by
  classical
  have hxBound (b : Block) : thirteenSixOutside S D b < 7 := by
    have hsum := thirteenSixInside_add_thirteenSixOutside S D b
    cases hk : S.kind b with
    | circle =>
        have hcap := hcircleCap b hk
        rw [← hsum] at hcap
        omega
    | line =>
        have hcap := hlineCap b hk
        rw [← hsum] at hcap
        omega
  have hgammaInside : thirteenSixInside S D gamma = 6 := by
    exact (thirteenSixInside_eq_card_of_support_eq
      S D gamma hgammaSupport).trans hD
  have hgammaOutside : thirteenSixOutside S D gamma = 0 :=
    thirteenSixOutside_eq_zero_of_support_eq S D gamma hgammaSupport
  have hpointwise (b : Block) :
      f (S.kind b) (thirteenSixInside S D b) (thirteenSixOutside S D b) =
        (if b = gamma then f .circle 6 0 else 0) +
        ∑ kind : BlockKind, ∑ g ∈ Finset.range 3, ∑ x ∈ Finset.range 7,
          if S.kind b = kind ∧ thirteenSixInside S D b = g ∧
              thirteenSixOutside S D b = x then f kind g x else 0 := by
    by_cases hbgamma : b = gamma
    · subst b
      rw [hgammaKind, hgammaInside, hgammaOutside, if_pos rfl]
      have hzero := thirteenSix_relative_selector_sum_eq_zero_of_g_ge
        f .circle 6 0 3 7 (by omega)
      rw [hzero, add_zero]
    · have hg : thirteenSixInside S D b < 3 := by
        have hinter := S.distinct_block_inter_card_lt_three hbgamma
        rw [hgammaSupport] at hinter
        exact hinter
      rw [if_neg hbgamma, zero_add]
      exact (thirteenSix_relative_selector_sum f (S.kind b)
        (thirteenSixInside S D b) (thirteenSixOutside S D b) 3 7
        hg (hxBound b)).symm
  have hgammaSum :
      (∑ b : Block, if b = gamma then f .circle 6 0 else 0) =
        f .circle 6 0 := by
    simp
  have hreorder :
      (∑ b : Block, ∑ kind : BlockKind,
        ∑ g ∈ Finset.range 3, ∑ x ∈ Finset.range 7,
          if S.kind b = kind ∧ thirteenSixInside S D b = g ∧
              thirteenSixOutside S D b = x then f kind g x else 0) =
      ∑ kind : BlockKind, ∑ g ∈ Finset.range 3,
        ∑ x ∈ Finset.range 7, ∑ b : Block,
          if S.kind b = kind ∧ thirteenSixInside S D b = g ∧
              thirteenSixOutside S D b = x then f kind g x else 0 := by
    rw [Finset.sum_comm]
    apply Fintype.sum_congr
    intro kind
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro g _hg
    rw [Finset.sum_comm]
  calc
    (∑ b : Block,
      f (S.kind b) (thirteenSixInside S D b) (thirteenSixOutside S D b)) =
        ∑ b : Block, ((if b = gamma then f .circle 6 0 else 0) +
          ∑ kind : BlockKind, ∑ g ∈ Finset.range 3,
            ∑ x ∈ Finset.range 7,
              if S.kind b = kind ∧ thirteenSixInside S D b = g ∧
                  thirteenSixOutside S D b = x then f kind g x else 0) := by
      apply Fintype.sum_congr
      exact hpointwise
    _ = f .circle 6 0 +
        ∑ kind : BlockKind, ∑ g ∈ Finset.range 3,
          ∑ x ∈ Finset.range 7, ∑ b : Block,
            if S.kind b = kind ∧ thirteenSixInside S D b = g ∧
                thirteenSixOutside S D b = x then f kind g x else 0 := by
      simp only [Finset.sum_add_distrib]
      rw [hgammaSum, hreorder]
    _ = _ := by
      apply congrArg (fun z => f .circle 6 0 + z)
      apply Fintype.sum_congr
      intro kind
      apply Finset.sum_congr rfl
      intro g _hg
      apply Finset.sum_congr rfl
      intro x _hx
      exact thirteenSix_sum_relative_indicator_int S D kind g x (f kind g x)

theorem thirteenSixOrdinaryIncidence_eq_relative
    (S : BlockSystem Point Block) (D : Finset Point) (gamma : Block)
    (hD : D.card = 6) (hgammaSupport : S.support gamma = D) :
    thirteenSixOrdinaryIncidence S = 3 *
      (thirteenSixRelativeCount S D .circle 0 3 +
       thirteenSixRelativeCount S D .circle 1 2 +
       thirteenSixRelativeCount S D .circle 2 1) := by
  classical
  have hpointwise (b : Block) :
      (if S.kind b = .circle ∧ (S.support b).card = 3 then 3 else 0) =
        (if S.kind b = .circle ∧ thirteenSixInside S D b = 0 ∧
            thirteenSixOutside S D b = 3 then 3 else 0) +
        (if S.kind b = .circle ∧ thirteenSixInside S D b = 1 ∧
            thirteenSixOutside S D b = 2 then 3 else 0) +
        (if S.kind b = .circle ∧ thirteenSixInside S D b = 2 ∧
            thirteenSixOutside S D b = 1 then 3 else 0) := by
    cases hk : S.kind b with
    | line => simp
    | circle =>
        have hsum := thirteenSixInside_add_thirteenSixOutside S D b
        by_cases hs : (S.support b).card = 3
        · have hne : b ≠ gamma := by
            intro h
            subst b
            rw [hgammaSupport, hD] at hs
            omega
          have hg : thirteenSixInside S D b ≤ 2 := by
            have hinter := S.distinct_block_inter_card_lt_three hne
            rw [hgammaSupport] at hinter
            exact Nat.le_of_lt_succ hinter
          rw [hs] at hsum
          have hcases :
              (thirteenSixInside S D b = 0 ∧
                thirteenSixOutside S D b = 3) ∨
              (thirteenSixInside S D b = 1 ∧
                thirteenSixOutside S D b = 2) ∨
              (thirteenSixInside S D b = 2 ∧
                thirteenSixOutside S D b = 1) := by
            omega
          rcases hcases with ⟨hg', hx'⟩ | ⟨hg', hx'⟩ | ⟨hg', hx'⟩ <;>
            simp [hs, hg', hx']
        · have h03 : ¬ (thirteenSixInside S D b = 0 ∧
              thirteenSixOutside S D b = 3) := by
            intro h
            apply hs
            omega
          have h12 : ¬ (thirteenSixInside S D b = 1 ∧
              thirteenSixOutside S D b = 2) := by
            intro h
            apply hs
            omega
          have h21 : ¬ (thirteenSixInside S D b = 2 ∧
              thirteenSixOutside S D b = 1) := by
            intro h
            apply hs
            omega
          simp [hs, h03, h12, h21]
  unfold thirteenSixOrdinaryIncidence
  simp_rw [hpointwise]
  simp only [Finset.sum_add_distrib]
  rw [thirteenSix_sum_relative_indicator,
    thirteenSix_sum_relative_indicator,
    thirteenSix_sum_relative_indicator]
  omega

/-- The relative census, with the five high line cells already known to
vanish, gives exactly the eight affine rows printed in the paper. -/
structure ThirteenSixAffineRows
    (S : BlockSystem Point Block) (D : Finset Point)
    (C C3 W u v d r j : Nat) : Prop where
  circleRow :
    1 + thirteenSixRelativeCount S D .circle 0 3 +
      thirteenSixRelativeCount S D .circle 0 4 +
      thirteenSixRelativeCount S D .circle 0 5 +
      thirteenSixRelativeCount S D .circle 0 6 +
      thirteenSixRelativeCount S D .circle 1 2 +
      thirteenSixRelativeCount S D .circle 1 3 +
      thirteenSixRelativeCount S D .circle 1 4 +
      thirteenSixRelativeCount S D .circle 1 5 +
      thirteenSixRelativeCount S D .circle 2 1 +
      thirteenSixRelativeCount S D .circle 2 2 +
      thirteenSixRelativeCount S D .circle 2 3 +
      thirteenSixRelativeCount S D .circle 2 4 = C
  ordinaryRow :
    thirteenSixRelativeCount S D .circle 0 3 +
      thirteenSixRelativeCount S D .circle 1 2 +
      thirteenSixRelativeCount S D .circle 2 1 = C3
  row0 :
    thirteenSixRelativeCount S D .circle 0 3 +
      4 * thirteenSixRelativeCount S D .circle 0 4 +
      10 * thirteenSixRelativeCount S D .circle 0 5 +
      20 * thirteenSixRelativeCount S D .circle 0 6 +
      thirteenSixRelativeCount S D .circle 1 3 +
      4 * thirteenSixRelativeCount S D .circle 1 4 +
      10 * thirteenSixRelativeCount S D .circle 1 5 +
      thirteenSixRelativeCount S D .circle 2 3 +
      4 * thirteenSixRelativeCount S D .circle 2 4 +
      thirteenSixRelativeCount S D .line 0 3 +
      4 * thirteenSixRelativeCount S D .line 0 4 +
      thirteenSixRelativeCount S D .line 1 3 +
      thirteenSixRelativeCount S D .line 2 3 = 35
  row1 :
    thirteenSixRelativeCount S D .circle 1 2 +
      3 * thirteenSixRelativeCount S D .circle 1 3 +
      6 * thirteenSixRelativeCount S D .circle 1 4 +
      10 * thirteenSixRelativeCount S D .circle 1 5 +
      2 * thirteenSixRelativeCount S D .circle 2 2 +
      6 * thirteenSixRelativeCount S D .circle 2 3 +
      12 * thirteenSixRelativeCount S D .circle 2 4 +
      thirteenSixRelativeCount S D .line 1 2 +
      3 * thirteenSixRelativeCount S D .line 1 3 +
      2 * thirteenSixRelativeCount S D .line 2 2 +
      6 * thirteenSixRelativeCount S D .line 2 3 = 126
  row2 :
    thirteenSixRelativeCount S D .circle 2 1 +
      2 * thirteenSixRelativeCount S D .circle 2 2 +
      3 * thirteenSixRelativeCount S D .circle 2 3 +
      4 * thirteenSixRelativeCount S D .circle 2 4 +
      thirteenSixRelativeCount S D .line 2 1 +
      2 * thirteenSixRelativeCount S D .line 2 2 +
      3 * thirteenSixRelativeCount S D .line 2 3 = 105
  weightRow :
    thirteenSixRelativeCount S D .circle 2 2 +
      3 * thirteenSixRelativeCount S D .circle 2 3 +
      6 * thirteenSixRelativeCount S D .circle 2 4 = W
  momentXRow :
    3 * (thirteenSixRelativeCount S D .circle 0 3 : Int) -
      5 * (thirteenSixRelativeCount S D .circle 0 5 : Int) -
      12 * (thirteenSixRelativeCount S D .circle 0 6 : Int) +
      2 * (thirteenSixRelativeCount S D .circle 1 2 : Int) -
      4 * (thirteenSixRelativeCount S D .circle 1 4 : Int) -
      10 * (thirteenSixRelativeCount S D .circle 1 5 : Int) +
      (thirteenSixRelativeCount S D .circle 2 1 : Int) -
      3 * (thirteenSixRelativeCount S D .circle 2 3 : Int) -
      8 * (thirteenSixRelativeCount S D .circle 2 4 : Int) +
      3 * (thirteenSixRelativeCount S D .line 0 3 : Int) +
      2 * (thirteenSixRelativeCount S D .line 1 2 : Int) +
      (thirteenSixRelativeCount S D .line 2 1 : Int) -
      3 * (thirteenSixRelativeCount S D .line 2 3 : Int) = 21 + u
  momentGammaRow :
    -12 + (thirteenSixRelativeCount S D .circle 1 2 : Int) -
      (thirteenSixRelativeCount S D .circle 1 4 : Int) -
      2 * (thirteenSixRelativeCount S D .circle 1 5 : Int) +
      2 * (thirteenSixRelativeCount S D .circle 2 1 : Int) -
      2 * (thirteenSixRelativeCount S D .circle 2 3 : Int) -
      4 * (thirteenSixRelativeCount S D .circle 2 4 : Int) +
      (thirteenSixRelativeCount S D .line 1 2 : Int) +
      2 * (thirteenSixRelativeCount S D .line 2 1 : Int) -
      2 * (thirteenSixRelativeCount S D .line 2 3 : Int) = 18 + v
  circleSlack : C + d = 60
  ordinarySlack : C3 = 13 + j
  weightSlack : W = 48 + r

structure ThirteenSixInvalidRelativeCells
    (S : BlockSystem Point Block) (D : Finset Point) : Prop where
  c00 : thirteenSixRelativeCount S D .circle 0 0 = 0
  c01 : thirteenSixRelativeCount S D .circle 0 1 = 0
  c02 : thirteenSixRelativeCount S D .circle 0 2 = 0
  c10 : thirteenSixRelativeCount S D .circle 1 0 = 0
  c11 : thirteenSixRelativeCount S D .circle 1 1 = 0
  c16 : thirteenSixRelativeCount S D .circle 1 6 = 0
  c20 : thirteenSixRelativeCount S D .circle 2 0 = 0
  c25 : thirteenSixRelativeCount S D .circle 2 5 = 0
  c26 : thirteenSixRelativeCount S D .circle 2 6 = 0
  l00 : thirteenSixRelativeCount S D .line 0 0 = 0
  l01 : thirteenSixRelativeCount S D .line 0 1 = 0
  l10 : thirteenSixRelativeCount S D .line 1 0 = 0
  l16 : thirteenSixRelativeCount S D .line 1 6 = 0
  l25 : thirteenSixRelativeCount S D .line 2 5 = 0
  l26 : thirteenSixRelativeCount S D .line 2 6 = 0

theorem thirteenSixInvalidRelativeCells_of_caps
    (S : BlockSystem Point Block) (D : Finset Point)
    (hcircleCap : ∀ c, S.kind c = .circle → (S.support c).card ≤ 6)
    (hlineCap : ∀ L, S.kind L = .line → (S.support L).card ≤ 6) :
    ThirteenSixInvalidRelativeCells S D := by
  constructor
  · exact thirteenSix_circle_relativeCount_eq_zero_of_invalid
      S D hcircleCap 0 0 (by omega)
  · exact thirteenSix_circle_relativeCount_eq_zero_of_invalid
      S D hcircleCap 0 1 (by omega)
  · exact thirteenSix_circle_relativeCount_eq_zero_of_invalid
      S D hcircleCap 0 2 (by omega)
  · exact thirteenSix_circle_relativeCount_eq_zero_of_invalid
      S D hcircleCap 1 0 (by omega)
  · exact thirteenSix_circle_relativeCount_eq_zero_of_invalid
      S D hcircleCap 1 1 (by omega)
  · exact thirteenSix_circle_relativeCount_eq_zero_of_invalid
      S D hcircleCap 1 6 (by omega)
  · exact thirteenSix_circle_relativeCount_eq_zero_of_invalid
      S D hcircleCap 2 0 (by omega)
  · exact thirteenSix_circle_relativeCount_eq_zero_of_invalid
      S D hcircleCap 2 5 (by omega)
  · exact thirteenSix_circle_relativeCount_eq_zero_of_invalid
      S D hcircleCap 2 6 (by omega)
  · exact thirteenSix_line_relativeCount_eq_zero_of_invalid
      S D hlineCap 0 0 (by omega)
  · exact thirteenSix_line_relativeCount_eq_zero_of_invalid
      S D hlineCap 0 1 (by omega)
  · exact thirteenSix_line_relativeCount_eq_zero_of_invalid
      S D hlineCap 1 0 (by omega)
  · exact thirteenSix_line_relativeCount_eq_zero_of_invalid
      S D hlineCap 1 6 (by omega)
  · exact thirteenSix_line_relativeCount_eq_zero_of_invalid
      S D hlineCap 2 5 (by omega)
  · exact thirteenSix_line_relativeCount_eq_zero_of_invalid
      S D hlineCap 2 6 (by omega)

theorem thirteenSix_affine_circle_row
    (S : BlockSystem Point Block) (D : Finset Point) (gamma : Block)
    (hD : D.card = 6) (hgammaKind : S.kind gamma = .circle)
    (hgammaSupport : S.support gamma = D)
    (hcircleCap : ∀ c, S.kind c = .circle → (S.support c).card ≤ 6)
    (hlineCap : ∀ L, S.kind L = .line → (S.support L).card ≤ 6) :
    1 + thirteenSixRelativeCount S D .circle 0 3 +
      thirteenSixRelativeCount S D .circle 0 4 +
      thirteenSixRelativeCount S D .circle 0 5 +
      thirteenSixRelativeCount S D .circle 0 6 +
      thirteenSixRelativeCount S D .circle 1 2 +
      thirteenSixRelativeCount S D .circle 1 3 +
      thirteenSixRelativeCount S D .circle 1 4 +
      thirteenSixRelativeCount S D .circle 1 5 +
      thirteenSixRelativeCount S D .circle 2 1 +
      thirteenSixRelativeCount S D .circle 2 2 +
      thirteenSixRelativeCount S D .circle 2 3 +
      thirteenSixRelativeCount S D .circle 2 4 =
        S.totalCircleCount := by
  classical
  obtain ⟨hc00, hc01, hc02, hc10, hc11, hc16, hc20, hc25, hc26,
      hl00, hl01, hl10, hl16, hl25, hl26⟩ :=
    thirteenSixInvalidRelativeCells_of_caps S D hcircleCap hlineCap
  have hrow := thirteenSix_sum_by_relativeCount_selected
    S D gamma hD hgammaKind hgammaSupport hcircleCap hlineCap
      (fun kind g x =>
        if kind = .circle ∧ 3 ≤ g + x then (1 : Int) else 0)
  have hleft :
      (∑ b : Block,
        if S.kind b = .circle ∧
            3 ≤ thirteenSixInside S D b + thirteenSixOutside S D b
        then (1 : Int) else 0) = (S.totalCircleCount : Int) := by
    have hpointwise (b : Block) :
        (if S.kind b = .circle ∧
            3 ≤ thirteenSixInside S D b + thirteenSixOutside S D b
          then (1 : Int) else 0) =
        (if S.kind b = .circle then 1 else 0) := by
      by_cases hk : S.kind b = .circle
      · have hsum := thirteenSixInside_add_thirteenSixOutside S D b
        have hmin := S.circle_min b hk
        rw [← hsum] at hmin
        simp [hk, hmin]
      · simp [hk]
    simp_rw [hpointwise]
    rw [← Finset.sum_filter]
    simp [BlockSystem.totalCircleCount, BlockSystem.blocksOfKind]
  rw [hleft, thirteenSix_sum_blockKind_int] at hrow
  norm_num [Finset.sum_range_succ] at hrow
  omega

theorem thirteenSix_affine_row0
    (S : BlockSystem Point Block) (D : Finset Point) (gamma : Block)
    (hpoint : Fintype.card Point = 13) (hD : D.card = 6)
    (hgammaKind : S.kind gamma = .circle)
    (hgammaSupport : S.support gamma = D)
    (hcircleCap : ∀ c, S.kind c = .circle → (S.support c).card ≤ 6)
    (hlineCap : ∀ L, S.kind L = .line → (S.support L).card ≤ 6)
    (hl05 : thirteenSixRelativeCount S D .line 0 5 = 0)
    (hl06 : thirteenSixRelativeCount S D .line 0 6 = 0)
    (hl14 : thirteenSixRelativeCount S D .line 1 4 = 0)
    (hl15 : thirteenSixRelativeCount S D .line 1 5 = 0)
    (hl24 : thirteenSixRelativeCount S D .line 2 4 = 0) :
    thirteenSixRelativeCount S D .circle 0 3 +
      4 * thirteenSixRelativeCount S D .circle 0 4 +
      10 * thirteenSixRelativeCount S D .circle 0 5 +
      20 * thirteenSixRelativeCount S D .circle 0 6 +
      thirteenSixRelativeCount S D .circle 1 3 +
      4 * thirteenSixRelativeCount S D .circle 1 4 +
      10 * thirteenSixRelativeCount S D .circle 1 5 +
      thirteenSixRelativeCount S D .circle 2 3 +
      4 * thirteenSixRelativeCount S D .circle 2 4 +
      thirteenSixRelativeCount S D .line 0 3 +
      4 * thirteenSixRelativeCount S D .line 0 4 +
      thirteenSixRelativeCount S D .line 1 3 +
      thirteenSixRelativeCount S D .line 2 3 = 35 := by
  classical
  obtain ⟨hc00, hc01, hc02, hc10, hc11, hc16, hc20, hc25, hc26,
      hl00, hl01, hl10, hl16, hl25, hl26⟩ :=
    thirteenSixInvalidRelativeCells_of_caps S D hcircleCap hlineCap
  have hrow := thirteenSix_sum_by_relativeCount_selected
    S D gamma hD hgammaKind hgammaSupport hcircleCap hlineCap
      (fun _kind _g x => (Nat.choose x 3 : Int))
  rw [(thirteenSix_relative_rows S D hpoint hD).1,
    thirteenSix_sum_blockKind_int] at hrow
  norm_num [Finset.sum_range_succ, Nat.choose] at hrow
  omega

theorem thirteenSix_affine_row1
    (S : BlockSystem Point Block) (D : Finset Point) (gamma : Block)
    (hpoint : Fintype.card Point = 13) (hD : D.card = 6)
    (hgammaKind : S.kind gamma = .circle)
    (hgammaSupport : S.support gamma = D)
    (hcircleCap : ∀ c, S.kind c = .circle → (S.support c).card ≤ 6)
    (hlineCap : ∀ L, S.kind L = .line → (S.support L).card ≤ 6)
    (hl14 : thirteenSixRelativeCount S D .line 1 4 = 0)
    (hl15 : thirteenSixRelativeCount S D .line 1 5 = 0)
    (hl24 : thirteenSixRelativeCount S D .line 2 4 = 0) :
    thirteenSixRelativeCount S D .circle 1 2 +
      3 * thirteenSixRelativeCount S D .circle 1 3 +
      6 * thirteenSixRelativeCount S D .circle 1 4 +
      10 * thirteenSixRelativeCount S D .circle 1 5 +
      2 * thirteenSixRelativeCount S D .circle 2 2 +
      6 * thirteenSixRelativeCount S D .circle 2 3 +
      12 * thirteenSixRelativeCount S D .circle 2 4 +
      thirteenSixRelativeCount S D .line 1 2 +
      3 * thirteenSixRelativeCount S D .line 1 3 +
      2 * thirteenSixRelativeCount S D .line 2 2 +
      6 * thirteenSixRelativeCount S D .line 2 3 = 126 := by
  classical
  obtain ⟨hc00, hc01, hc02, hc10, hc11, hc16, hc20, hc25, hc26,
      hl00, hl01, hl10, hl16, hl25, hl26⟩ :=
    thirteenSixInvalidRelativeCells_of_caps S D hcircleCap hlineCap
  have hrow := thirteenSix_sum_by_relativeCount_selected
    S D gamma hD hgammaKind hgammaSupport hcircleCap hlineCap
      (fun _kind g x => (g : Int) * (Nat.choose x 2 : Int))
  rw [(thirteenSix_relative_rows S D hpoint hD).2.1,
    thirteenSix_sum_blockKind_int] at hrow
  norm_num [Finset.sum_range_succ, Nat.choose] at hrow
  omega

theorem thirteenSix_affine_row2
    (S : BlockSystem Point Block) (D : Finset Point) (gamma : Block)
    (hpoint : Fintype.card Point = 13) (hD : D.card = 6)
    (hgammaKind : S.kind gamma = .circle)
    (hgammaSupport : S.support gamma = D)
    (hcircleCap : ∀ c, S.kind c = .circle → (S.support c).card ≤ 6)
    (hlineCap : ∀ L, S.kind L = .line → (S.support L).card ≤ 6)
    (hl24 : thirteenSixRelativeCount S D .line 2 4 = 0) :
    thirteenSixRelativeCount S D .circle 2 1 +
      2 * thirteenSixRelativeCount S D .circle 2 2 +
      3 * thirteenSixRelativeCount S D .circle 2 3 +
      4 * thirteenSixRelativeCount S D .circle 2 4 +
      thirteenSixRelativeCount S D .line 2 1 +
      2 * thirteenSixRelativeCount S D .line 2 2 +
      3 * thirteenSixRelativeCount S D .line 2 3 = 105 := by
  classical
  obtain ⟨hc00, hc01, hc02, hc10, hc11, hc16, hc20, hc25, hc26,
      hl00, hl01, hl10, hl16, hl25, hl26⟩ :=
    thirteenSixInvalidRelativeCells_of_caps S D hcircleCap hlineCap
  have hrow := thirteenSix_sum_by_relativeCount_selected
    S D gamma hD hgammaKind hgammaSupport hcircleCap hlineCap
      (fun _kind g x => (Nat.choose g 2 : Int) * (x : Int))
  rw [(thirteenSix_relative_rows S D hpoint hD).2.2.1,
    thirteenSix_sum_blockKind_int] at hrow
  norm_num [Finset.sum_range_succ, Nat.choose] at hrow
  omega

end RelativeCensus

end Erdos506.V1
