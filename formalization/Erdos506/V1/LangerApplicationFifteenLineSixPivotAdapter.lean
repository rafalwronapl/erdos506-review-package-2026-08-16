import Erdos506.V1.LangerApplicationFifteenLineSixFinish

/-!
# The selected-line fan after pivot inversion

This leaf contains only the lossless incidence adapter left after the
selected line has been turned into a six-circle.  It deliberately keeps the
finite partition arithmetic in `LangerApplicationFifteenLineSixFinish`.
-/

namespace Erdos506.V1

open Erdos506.Block
open Erdos506.Block.BlockSystem
open Erdos506.Incidence
open Erdos506.V3
open Erdos506.V4
open scoped BigOperators

universe u

variable {alpha : Type u} [Fintype alpha] [DecidableEq alpha]

/-- Fan circles at `p` which also contain the surviving inverted label `x`.
The outer subtype remembers that the block belongs to the actual circle
pencil, rather than merely being an arbitrary generalized pivot block. -/
abbrev PivotFanCircleAt
    (cfg : Configuration alpha) (L : DeterminedLine cfg)
    (p : BlockOutsider (blockSystem cfg) (Sum.inl L))
    (x : AwayFrom p.1) :=
  {c : {c : GeometricBlock cfg //
      c ∈ circlePencil (blockSystem cfg) (Sum.inl L) p} //
    x.1 ∈ geometricBlockSupport cfg c.1.1}

/-- A fan circle through `p,x` maps to a marked two-chord line through `x`
in the pivot-inverted configuration. -/
noncomputable def pivotFanCircleAtToMarkedLine
    (cfg : Configuration alpha) (L : DeterminedLine cfg)
    (p : BlockOutsider (blockSystem cfg) (Sum.inl L))
    (hthree : 3 ≤ (lineSupport cfg L).card)
    (x : AwayFrom p.1) :
    PivotFanCircleAt cfg L p x →
      SixConicMarkedLineAt (pivotInversion cfg p.1)
        (pivotInversionDeterminedCircleOfAwayLine cfg p.1 L
          (mem_blockOutsiders.mp p.2) hthree) x := by
  intro c
  refine ⟨pivotFanCircleLine cfg L p c.1,
    pivotFanCircleLine_inter_baseCircle_card cfg L p hthree c.1, ?_⟩
  rw [pivotFanCircleLine, lineSupport_circleToPivotLine,
    mem_awayCircleSupport, circleTrace_pivotFanDeterminedCircle]
  exact c.2

/-- The marked-line encoding loses no fan circle. -/
theorem pivotFanCircleAtToMarkedLine_injective
    (cfg : Configuration alpha) (L : DeterminedLine cfg)
    (p : BlockOutsider (blockSystem cfg) (Sum.inl L))
    (hthree : 3 ≤ (lineSupport cfg L).card)
    (x : AwayFrom p.1) :
    Function.Injective
      (pivotFanCircleAtToMarkedLine cfg L p hthree x) := by
  intro c d hcd
  apply Subtype.ext
  apply pivotFanCircleLine_injective cfg L p
  exact congrArg Subtype.val hcd

/-- Fibrewise form of the fan-circle / marked-line comparison. -/
theorem card_pivotFanCircleAt_le_markedLineAt
    (cfg : Configuration alpha) (L : DeterminedLine cfg)
    (p : BlockOutsider (blockSystem cfg) (Sum.inl L))
    (hthree : 3 ≤ (lineSupport cfg L).card)
    (x : AwayFrom p.1) :
    Fintype.card (PivotFanCircleAt cfg L p x) ≤
      Fintype.card
        (SixConicMarkedLineAt (pivotInversion cfg p.1)
          (pivotInversionDeterminedCircleOfAwayLine cfg p.1 L
            (mem_blockOutsiders.mp p.2) hthree) x) := by
  classical
  exact Fintype.card_le_of_injective
    (pivotFanCircleAtToMarkedLine cfg L p hthree x)
    (pivotFanCircleAtToMarkedLine_injective cfg L p hthree x)

private theorem card_inter_eq_sum_mem_indicator
    {beta : Type*} [DecidableEq beta] (A X : Finset beta) :
    (A ∩ X).card = ∑ x ∈ X, if x ∈ A then 1 else 0 := by
  classical
  calc
    (A ∩ X).card = ∑ _x ∈ A ∩ X, 1 := by
      exact Finset.card_eq_sum_ones (A ∩ X)
    _ = ∑ x ∈ X, if x ∈ A then 1 else 0 := by
      rw [← Finset.sum_filter]
      congr 1
      ext x
      simp [and_comm]

/-- Incidence Fubini for one pivot: count fan circles first through the
surviving outsider, or count surviving outsiders first on each fan line. -/
theorem sum_card_pivotFanCircleAt_eq_sum_line_card
    (cfg : Configuration alpha) (L : DeterminedLine cfg)
    (p : BlockOutsider (blockSystem cfg) (Sum.inl L))
    (X : Finset (AwayFrom p.1)) :
    (∑ x ∈ X, Fintype.card (PivotFanCircleAt cfg L p x)) =
      ∑ c : {c : GeometricBlock cfg //
          c ∈ circlePencil (blockSystem cfg) (Sum.inl L) p},
        (lineSupport (pivotInversion cfg p.1)
          (pivotFanCircleLine cfg L p c) ∩ X).card := by
  classical
  calc
    (∑ x ∈ X, Fintype.card (PivotFanCircleAt cfg L p x)) =
        ∑ x ∈ X, ∑ c : {c : GeometricBlock cfg //
            c ∈ circlePencil (blockSystem cfg) (Sum.inl L) p},
          if x.1 ∈ geometricBlockSupport cfg c.1 then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro x _hx
      rw [Fintype.card_subtype, Finset.card_eq_sum_ones,
        Finset.sum_filter]
    _ = ∑ c : {c : GeometricBlock cfg //
          c ∈ circlePencil (blockSystem cfg) (Sum.inl L) p},
        ∑ x ∈ X,
          if x.1 ∈ geometricBlockSupport cfg c.1 then 1 else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ c : {c : GeometricBlock cfg //
          c ∈ circlePencil (blockSystem cfg) (Sum.inl L) p},
        (lineSupport (pivotInversion cfg p.1)
          (pivotFanCircleLine cfg L p c) ∩ X).card := by
      apply Finset.sum_congr rfl
      intro c _hc
      rw [card_inter_eq_sum_mem_indicator]
      apply Finset.sum_congr rfl
      intro x _hx
      rw [pivotFanCircleLine, lineSupport_circleToPivotLine]
      simp only [mem_awayCircleSupport,
        circleTrace_pivotFanDeterminedCircle]

/-- Summing the fibrewise injections gives the one-pivot comparison with
the six-conic line-incidence functional. -/
theorem sum_card_pivotFanCircleAt_le_sixConicLineIncidence
    (cfg : Configuration alpha) (L : DeterminedLine cfg)
    (p : BlockOutsider (blockSystem cfg) (Sum.inl L))
    (hthree : 3 ≤ (lineSupport cfg L).card)
    (X : Finset (AwayFrom p.1)) :
    (∑ x ∈ X, Fintype.card (PivotFanCircleAt cfg L p x)) ≤
      sixConicLineIncidence (pivotInversion cfg p.1)
        (pivotInversionDeterminedCircleOfAwayLine cfg p.1 L
          (mem_blockOutsiders.mp p.2) hthree) X := by
  rw [sixConicLineIncidence_eq_sum_card_markedLineAt]
  exact Finset.sum_le_sum fun x _hx =>
    card_pivotFanCircleAt_le_markedLineAt cfg L p hthree x

/-- The weighted fan rows at one pivot are bounded by the corresponding
marked-line incidence.  The weight of a fan circle is its number of other
outsider centres. -/
theorem sum_pivotFanCircle_degree_sub_one_le_sixConicLineIncidence
    (cfg : Configuration alpha) (L : DeterminedLine cfg)
    (p : BlockOutsider (blockSystem cfg) (Sum.inl L))
    (hthree : 3 ≤ (lineSupport cfg L).card) :
    (∑ c : {c : GeometricBlock cfg //
        c ∈ circlePencil (blockSystem cfg) (Sum.inl L) p},
      nineFiveFanDegree (blockSystem cfg) (Sum.inl L) c.1 - 1) ≤
      sixConicLineIncidence (pivotInversion cfg p.1)
        (pivotInversionDeterminedCircleOfAwayLine cfg p.1 L
          (mem_blockOutsiders.mp p.2) hthree)
        (awaySupport p.1
          (blockOutsiders (blockSystem cfg) (Sum.inl L))) := by
  let X := awaySupport p.1
    (blockOutsiders (blockSystem cfg) (Sum.inl L))
  calc
    (∑ c : {c : GeometricBlock cfg //
        c ∈ circlePencil (blockSystem cfg) (Sum.inl L) p},
      nineFiveFanDegree (blockSystem cfg) (Sum.inl L) c.1 - 1) =
        ∑ c : {c : GeometricBlock cfg //
            c ∈ circlePencil (blockSystem cfg) (Sum.inl L) p},
          (lineSupport (pivotInversion cfg p.1)
            (pivotFanCircleLine cfg L p c) ∩ X).card := by
      apply Finset.sum_congr rfl
      intro c _hc
      exact (pivotFanCircleLine_outsider_card cfg L p c).symm
    _ = ∑ x ∈ X, Fintype.card (PivotFanCircleAt cfg L p x) :=
      (sum_card_pivotFanCircleAt_eq_sum_line_card cfg L p X).symm
    _ ≤ sixConicLineIncidence (pivotInversion cfg p.1)
        (pivotInversionDeterminedCircleOfAwayLine cfg p.1 L
          (mem_blockOutsiders.mp p.2) hthree) X :=
      sum_card_pivotFanCircleAt_le_sixConicLineIncidence
        cfg L p hthree X

end Erdos506.V1
