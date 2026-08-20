import Erdos506.Incidence.OrdinaryPrinciples
import Erdos506.V1.InversionAugmentation
import Erdos506.V1.RestoredPivot

/-!
# Direct and restored ordinary-line forms of Kelly--Moser

The public Kelly--Moser input is phrased as a guarded three-block bound at a
selected pivot.  Inversion augmentation gives the direct ordinary-line row
for the exact `9..12` window used by V1.  Restricting the restored-pivot
dictionary then identifies ordinary restored lines with original two-lines
and three-circles through the pivot.
-/

namespace Erdos506.Incidence

open Erdos506.V1
open Erdos506.V3
open Erdos506.V4

universe u

/-- Direct Kelly--Moser in the only ordinary-point window used by V1.
Besides the explicit `9 ≤ q ≤ 12` guard, the geometric hypothesis is only
noncollinearity; a configuration lying on one proper circle is allowed. -/
theorem RealPlaneKellyMoserPrinciple.ordinary_line_bound
    (Kelly : RealPlaneKellyMoserPrinciple.{u})
    {α : Type u} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (hnc : Noncollinear cfg)
    (hmin : 9 ≤ Fintype.card α) (hmax : Fintype.card α ≤ 12) :
    3 * Fintype.card α ≤ 7 * (blockSystem cfg).lineCount 2 := by
  classical
  obtain ⟨o, ho⟩ := exists_external_point cfg
  have haug := Kelly.pivot_three_block_bound
    (inversionAugmentation cfg o ho)
    (inversionAugmentation_admissible cfg hnc o ho)
    (by simp; omega) (by simp; omega) none
  change
    3 * (Fintype.card (Option α) - 1) ≤
      7 * (blockSystem (inversionAugmentation cfg o ho)).blockDegree 3 none
    at haug
  rw [blockDegree_three_inversionAugmentation cfg o ho] at haug
  simpa using haug

end Erdos506.Incidence

namespace Erdos506.V1

open Erdos506.Block
open Erdos506.Block.BlockSystem
open Erdos506.Incidence
open Erdos506.V3
open Erdos506.V4

universe u

/-! ## The size-two restored census -/

/-- Line-tagged blocks of size `s` through `p`. -/
abbrev TaggedLineAtSize
    {α : Type u} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (p : α) (s : ℕ) :=
  {b : GeometricBlock cfg //
    geometricBlockKind b = .line ∧
      (geometricBlockSupport cfg b).card = s ∧
        p ∈ geometricBlockSupport cfg b}

/-- Circle-tagged blocks of size `s` through `p`. -/
abbrev TaggedCircleAtSize
    {α : Type u} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (p : α) (s : ℕ) :=
  {b : GeometricBlock cfg //
    geometricBlockKind b = .circle ∧
      (geometricBlockSupport cfg b).card = s ∧
        p ∈ geometricBlockSupport cfg b}

theorem lineDegree_eq_card_taggedLineAtSize
    {α : Type u} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (p : α) (s : ℕ) :
    (blockSystem cfg).lineDegree s p =
      Fintype.card (TaggedLineAtSize cfg p s) := by
  classical
  change
    (((((Finset.univ.filter fun b : GeometricBlock cfg =>
        geometricBlockKind b = .line).filter fun b =>
          (geometricBlockSupport cfg b).card = s).filter fun b =>
            p ∈ geometricBlockSupport cfg b).card)) = _
  rw [Finset.filter_filter, Finset.filter_filter]
  simpa [TaggedLineAtSize, and_assoc] using
    (Fintype.card_subtype
      (fun b : GeometricBlock cfg =>
        geometricBlockKind b = .line ∧
          (geometricBlockSupport cfg b).card = s ∧
            p ∈ geometricBlockSupport cfg b)).symm

theorem circleDegree_eq_card_taggedCircleAtSize
    {α : Type u} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (p : α) (s : ℕ) :
    (blockSystem cfg).circleDegree s p =
      Fintype.card (TaggedCircleAtSize cfg p s) := by
  classical
  change
    (((((Finset.univ.filter fun b : GeometricBlock cfg =>
        geometricBlockKind b = .circle).filter fun b =>
          (geometricBlockSupport cfg b).card = s).filter fun b =>
            p ∈ geometricBlockSupport cfg b).card)) = _
  rw [Finset.filter_filter, Finset.filter_filter]
  simpa [TaggedCircleAtSize, and_assoc] using
    (Fintype.card_subtype
      (fun b : GeometricBlock cfg =>
        geometricBlockKind b = .circle ∧
          (geometricBlockSupport cfg b).card = s ∧
            p ∈ geometricBlockSupport cfg b)).symm

/-- A block through the original pivot produces an ordinary line in the
restored configuration exactly in the indicated line/circle size case. -/
def IsRestoredOrdinaryBlock
    {α : Type u} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (p : α) (b : BlockThrough cfg p) : Prop :=
  match b.1 with
  | .inl L => (lineSupport cfg L).card = 2
  | .inr c => (circleTrace cfg c.1).card = 3

/-- The two disjoint sources of ordinary lines after restoring the centre. -/
abbrev RestoredOrdinarySource
    {α : Type u} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (p : α) :=
  TaggedLineAtSize cfg p 2 ⊕ TaggedCircleAtSize cfg p 3

/-- Split the relevant original blocks according to their line/circle tag. -/
def restoredOrdinarySourceBlockEquiv
    {α : Type u} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (p : α) :
    RestoredOrdinarySource cfg p ≃
      {b : BlockThrough cfg p // IsRestoredOrdinaryBlock cfg p b} where
  toFun b := by
    cases b with
    | inl b =>
        rcases b with ⟨b, hbkind, hbsize, hbp⟩
        cases b with
        | inl L => exact ⟨⟨.inl L, hbp⟩, hbsize⟩
        | inr c => cases hbkind
    | inr b =>
        rcases b with ⟨b, hbkind, hbsize, hbp⟩
        cases b with
        | inl L => cases hbkind
        | inr c => exact ⟨⟨.inr c, hbp⟩, hbsize⟩
  invFun b := by
    rcases b with ⟨⟨b, hbp⟩, hbsize⟩
    cases b with
    | inl L => exact .inl ⟨.inl L, rfl, hbsize, hbp⟩
    | inr c => exact .inr ⟨.inr c, rfl, hbsize, hbp⟩
  left_inv b := by
    cases b with
    | inl b =>
        rcases b with ⟨b, hbkind, hbsize, hbp⟩
        cases b with
        | inl L => rfl
        | inr c => cases hbkind
    | inr b =>
        rcases b with ⟨b, hbkind, hbsize, hbp⟩
        cases b with
        | inl L => cases hbkind
        | inr c => rfl
  right_inv b := by
    rcases b with ⟨⟨b, hbp⟩, hbsize⟩
    cases b <;> rfl

/-- Restrict `blockRestoredLineEquiv` to ordinary restored lines. -/
noncomputable def restoredOrdinaryBlockLineEquiv
    {α : Type u} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (p : α) :
    {b : BlockThrough cfg p // IsRestoredOrdinaryBlock cfg p b} ≃
      DeterminedLineOfSize (restoredPivotConfiguration cfg p) 2 :=
  (blockRestoredLineEquiv cfg p).subtypeEquiv fun b => by
    rcases b with ⟨b, hbp⟩
    cases b with
    | inl L =>
        have hcard := card_lineSupport_blockToRestoredLine cfg p
          (⟨Sum.inl L, hbp⟩ : BlockThrough cfg p)
        change
          (lineSupport (restoredPivotConfiguration cfg p)
            (blockToRestoredLine cfg p
              (⟨Sum.inl L, hbp⟩ : BlockThrough cfg p))).card =
            (lineSupport cfg L).card at hcard
        change
          (lineSupport cfg L).card = 2 ↔
            (lineSupport (restoredPivotConfiguration cfg p)
              (blockToRestoredLine cfg p ⟨.inl L, hbp⟩)).card = 2
        rw [hcard]
    | inr c =>
        have hcard := card_lineSupport_blockToRestoredLine cfg p
          (⟨Sum.inr c, hbp⟩ : BlockThrough cfg p)
        change
          (lineSupport (restoredPivotConfiguration cfg p)
            (blockToRestoredLine cfg p
              (⟨Sum.inr c, hbp⟩ : BlockThrough cfg p))).card =
            (circleTrace cfg c.1).card - 1 at hcard
        change
          (circleTrace cfg c.1).card = 3 ↔
            (lineSupport (restoredPivotConfiguration cfg p)
              (blockToRestoredLine cfg p ⟨.inr c, hbp⟩)).card = 2
        rw [hcard]
        have hmin := Erdos506.V3.circleSupport_card_ge_three cfg c
        omega

/-- Exact equivalence between the two original sources and ordinary lines
in the restored configuration. -/
noncomputable def restoredOrdinarySourceLineEquiv
    {α : Type u} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (p : α) :
    RestoredOrdinarySource cfg p ≃
      DeterminedLineOfSize (restoredPivotConfiguration cfg p) 2 :=
  (restoredOrdinarySourceBlockEquiv cfg p).trans
    (restoredOrdinaryBlockLineEquiv cfg p)

/-- Ordinary lines in the restored pivot configuration are precisely the
original two-lines and three-circles through the pivot. -/
theorem lineCount_two_restoredPivotConfiguration
    {α : Type u} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (p : α) :
    (blockSystem (restoredPivotConfiguration cfg p)).lineCount 2 =
      (blockSystem cfg).lineDegree 2 p +
        (blockSystem cfg).circleDegree 3 p := by
  rw [lineCount_eq_card_determinedLineOfSize]
  calc
    Fintype.card
        (DeterminedLineOfSize (restoredPivotConfiguration cfg p) 2) =
        Fintype.card (RestoredOrdinarySource cfg p) :=
      (Fintype.card_congr (restoredOrdinarySourceLineEquiv cfg p)).symm
    _ = Fintype.card (TaggedLineAtSize cfg p 2) +
        Fintype.card (TaggedCircleAtSize cfg p 3) := by
      simp [RestoredOrdinarySource]
    _ = (blockSystem cfg).lineDegree 2 p +
        (blockSystem cfg).circleDegree 3 p := by
      rw [← lineDegree_eq_card_taggedLineAtSize,
        ← circleDegree_eq_card_taggedCircleAtSize]

end Erdos506.V1

namespace Erdos506.Incidence

open Erdos506.V1
open Erdos506.V3
open Erdos506.V4

universe u

/-- Direct Kelly--Moser applied to the restored pivot configuration. -/
theorem RealPlaneKellyMoserPrinciple.restored_ordinary_line_bound
    (Kelly : RealPlaneKellyMoserPrinciple.{u})
    {α : Type u} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (hadm : Erdos506.V1.Admissible cfg)
    (hcard : 3 ≤ Fintype.card α)
    (hmin : 9 ≤ Fintype.card α) (hmax : Fintype.card α ≤ 12)
    (p : α) :
    3 * Fintype.card α ≤
      7 * ((blockSystem cfg).lineDegree 2 p +
        (blockSystem cfg).circleDegree 3 p) := by
  have hrestCard :
      Fintype.card (Option (AwayFrom p)) = Fintype.card α := by
    rw [Fintype.card_option, card_awayFrom]
    omega
  have hrest := Kelly.ordinary_line_bound
    (restoredPivotConfiguration cfg p)
    (restoredPivotConfiguration_noncollinear cfg hadm hcard p)
    (by rw [hrestCard]; exact hmin)
    (by rw [hrestCard]; exact hmax)
  rw [lineCount_two_restoredPivotConfiguration] at hrest
  rw [hrestCard] at hrest
  exact hrest

/-- Eleven restored points have at least five ordinary lines. -/
theorem RealPlaneKellyMoserPrinciple.five_le_restored_ordinary_line_count_of_card_eleven
    (Kelly : RealPlaneKellyMoserPrinciple.{u})
    {α : Type u} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (hadm : Erdos506.V1.Admissible cfg)
    (hcard : Fintype.card α = 11) (p : α) :
    5 ≤ (blockSystem cfg).lineDegree 2 p +
      (blockSystem cfg).circleDegree 3 p := by
  have h := Kelly.restored_ordinary_line_bound cfg hadm
    (by omega) (by omega) (by omega) p
  rw [hcard] at h
  omega

/-- Summing the restored ordinary-line bound at eleven points gives the
aggregate row used in place of the former Lenchner circle-only estimate. -/
theorem RealPlaneKellyMoserPrinciple.fifty_five_le_restored_three_incidence_of_card_eleven
    (Kelly : RealPlaneKellyMoserPrinciple.{u})
    {α : Type u} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (hadm : Erdos506.V1.Admissible cfg)
    (hcard : Fintype.card α = 11) :
    55 ≤ 2 * (blockSystem cfg).lineCount 2 +
      3 * (blockSystem cfg).circleCount 3 := by
  have hsum :
      (∑ _p : α, 5) ≤
        ∑ p : α, ((blockSystem cfg).lineDegree 2 p +
          (blockSystem cfg).circleDegree 3 p) :=
    Finset.sum_le_sum fun p _hp =>
      Kelly.five_le_restored_ordinary_line_count_of_card_eleven
        cfg hadm hcard p
  rw [Finset.sum_add_distrib, (blockSystem cfg).line_incidence,
    (blockSystem cfg).circle_incidence] at hsum
  simpa [hcard] using hsum

/-- Twelve restored points have at least six ordinary lines. -/
theorem RealPlaneKellyMoserPrinciple.six_le_restored_ordinary_line_count_of_card_twelve
    (Kelly : RealPlaneKellyMoserPrinciple.{u})
    {α : Type u} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (hadm : Erdos506.V1.Admissible cfg)
    (hcard : Fintype.card α = 12) (p : α) :
    6 ≤ (blockSystem cfg).lineDegree 2 p +
      (blockSystem cfg).circleDegree 3 p := by
  have h := Kelly.restored_ordinary_line_bound cfg hadm
    (by omega) (by omega) (by omega) p
  rw [hcard] at h
  omega

/-- Summing the restored ordinary-line bound at twelve points. -/
theorem RealPlaneKellyMoserPrinciple.seventy_two_le_restored_three_incidence_of_card_twelve
    (Kelly : RealPlaneKellyMoserPrinciple.{u})
    {α : Type u} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (hadm : Erdos506.V1.Admissible cfg)
    (hcard : Fintype.card α = 12) :
    72 ≤ 2 * (blockSystem cfg).lineCount 2 +
      3 * (blockSystem cfg).circleCount 3 := by
  have hsum :
      (∑ _p : α, 6) ≤
        ∑ p : α, ((blockSystem cfg).lineDegree 2 p +
          (blockSystem cfg).circleDegree 3 p) :=
    Finset.sum_le_sum fun p _hp =>
      Kelly.six_le_restored_ordinary_line_count_of_card_twelve
        cfg hadm hcard p
  rw [Finset.sum_add_distrib, (blockSystem cfg).line_incidence,
    (blockSystem cfg).circle_incidence] at hsum
  simpa [hcard] using hsum

end Erdos506.Incidence
