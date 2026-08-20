import Erdos506.Block.SignedRows
import Erdos506.V1.Carrier

/-!
# The universal V1 block rows

This file specializes the finite tagged-block calculus to the full geometric
line and circle traces of a V1 configuration.  These are exact identities;
no incidence inequality is assumed here.
-/

namespace Erdos506.V1

open Erdos506.Block
open Erdos506.Block.BlockSystem
open Erdos506.Incidence
open Erdos506.V4
open scoped BigOperators

noncomputable abbrev blockSystem {α : Type*} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) := geometricBlockSystem cfg

noncomputable def blockCount {α : Type*} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (s : ℕ) : ℕ :=
  (blockSystem cfg).blockCount s

noncomputable def lineCount {α : Type*} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (s : ℕ) : ℕ :=
  (blockSystem cfg).lineCount s

noncomputable def circleBlockCount {α : Type*} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (s : ℕ) : ℕ :=
  (blockSystem cfg).circleCount s

noncomputable def blockDegree {α : Type*} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (s : ℕ) (p : α) : ℕ :=
  (blockSystem cfg).blockDegree s p

noncomputable def lineDegree {α : Type*} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (s : ℕ) (p : α) : ℕ :=
  (blockSystem cfg).lineDegree s p

noncomputable def circleDegree {α : Type*} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (s : ℕ) (p : α) : ℕ :=
  (blockSystem cfg).circleDegree s p

noncomputable def sigma {α : Type*} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (p : α) : ℤ :=
  (blockSystem cfg).pivotSigma p

noncomputable def rowP {α : Type*} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) : ℤ :=
  (blockSystem cfg).pivotRow

noncomputable def kappa {α : Type*} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (p : α) : ℤ :=
  (blockSystem cfg).restoredKappa p

noncomputable def rowD {α : Type*} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) : ℤ :=
  (blockSystem cfg).defectRow

noncomputable def rowL {α : Type*} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) : ℤ :=
  (blockSystem cfg).langerRow

noncomputable def globalLineSlack
    {α : Type*} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) : ℤ :=
  (blockSystem cfg).globalLineSlack

noncomputable def globalLineRow
    {α : Type*} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) : ℤ :=
  (blockSystem cfg).globalLineRow

theorem blockCount_eq_lineCount_add_circleBlockCount
    {α : Type*} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (s : ℕ) :
    blockCount cfg s = lineCount cfg s + circleBlockCount cfg s :=
  (blockSystem cfg).blockCount_eq_lineCount_add_circleCount s

theorem block_incidence
    {α : Type*} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (s : ℕ) :
    (∑ p : α, blockDegree cfg s p) = s * blockCount cfg s :=
  (blockSystem cfg).block_incidence s

theorem line_incidence
    {α : Type*} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (s : ℕ) :
    (∑ p : α, lineDegree cfg s p) = s * lineCount cfg s :=
  (blockSystem cfg).line_incidence s

theorem circle_incidence
    {α : Type*} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (s : ℕ) :
    (∑ p : α, circleDegree cfg s p) = s * circleBlockCount cfg s :=
  (blockSystem cfg).circle_incidence s

/-- The manuscript's global triple row `T`. -/
theorem triple_partition_by_size
    {α : Type*} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) :
    (∑ s ∈ Finset.range (Fintype.card α + 1),
        Nat.choose s 3 * blockCount cfg s) =
      Nat.choose (Fintype.card α) 3 :=
  (blockSystem cfg).triple_partition_by_size

/-- Every selected pair is owned by exactly one full line trace. -/
theorem line_pair_partition_by_size
    {α : Type*} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) :
    (∑ s ∈ Finset.range (Fintype.card α + 1),
        Nat.choose s 2 * lineCount cfg s) =
      Nat.choose (Fintype.card α) 2 :=
  (blockSystem cfg).line_pair_partition_by_size

/-- The four selected-set triple rows are instances of one theorem. -/
theorem relative_triple_partition
    {α : Type*} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (D : Finset α) (j : ℕ) (hj : j ≤ 3) :
    (∑ b : GeometricBlock cfg,
        Nat.choose (geometricBlockSupport cfg b ∩ D).card j *
          Nat.choose (geometricBlockSupport cfg b \ D).card (3 - j)) =
      Nat.choose D.card j *
        Nat.choose (Fintype.card α - D.card) (3 - j) :=
  (blockSystem cfg).relative_triple_partition D j hj

/-- Ownership of triples through a pivot point. -/
theorem pivot_pair_partition
    {α : Type*} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (p : α) :
    (∑ s ∈ Finset.range (Fintype.card α + 1),
        Nat.choose (s - 1) 2 * blockDegree cfg s p) =
      Nat.choose (Fintype.card α - 1) 2 :=
  (blockSystem cfg).pivot_pair_partition p

/-- The full line traces through a point partition all other labels into
line arms. -/
theorem line_arms
    {α : Type*} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (p : α) :
    (∑ s ∈ Finset.range (Fintype.card α + 1),
        (s - 1) * lineDegree cfg s p) = Fintype.card α - 1 :=
  (blockSystem cfg).line_arms p

/-- Reusable pair-moment bound for any finite family of V1 geometric
blocks. -/
theorem block_family_second_moment
    {α : Type*} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (F : Finset (GeometricBlock cfg)) :
    (∑ p : α, Nat.choose ((blockSystem cfg).degreeIn F p) 2) ≤
      2 * Nat.choose F.card 2 :=
  (blockSystem cfg).second_moment_le_two_choose F

/-- Exact global pivot-slack row; no sign assumption is used. -/
theorem sum_sigma_eq_rowP_sub_three_n
    {α : Type*} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) :
    (∑ p : α, sigma cfg p) = rowP cfg - 3 * (Fintype.card α : ℤ) :=
  (blockSystem cfg).sum_pivotSigma_eq_pivotRow_sub_three_n

/-- Exact restored-centre defect row; geometric nonnegativity is a separate
input. -/
theorem sum_kappa_eq_n_mul_n_sub_four_sub_rowD
    {α : Type*} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) :
    (∑ p : α, kappa cfg p) =
      (Fintype.card α : ℤ) * ((Fintype.card α : ℤ) - 4) - rowD cfg :=
  (blockSystem cfg).sum_restoredKappa_eq_n_mul_n_sub_four_sub_defectRow

/-- Exact incidence form of the Langer row. -/
theorem rowL_eq_sum_local_weighted_degree
    {α : Type*} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) :
    rowL cfg =
      ∑ p : α, ∑ s ∈ (blockSystem cfg).nontrivialSizes,
        ((s : ℤ) - 1) * (blockDegree cfg s p : ℤ) :=
  (blockSystem cfg).langerRow_eq_sum_local_weighted_degree

theorem choose_two_sub_three_sub_globalLineRow_eq_globalLineSlack
    {α : Type*} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) :
    (Nat.choose (Fintype.card α) 2 : ℤ) - 3 - globalLineRow cfg =
      globalLineSlack cfg :=
  (blockSystem cfg).choose_two_sub_three_sub_globalLineRow_eq_globalLineSlack

/-- Line-tagged geometric blocks are exactly the determined lines. -/
def lineBlockEquiv
    {α : Type*} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) :
    {b : GeometricBlock cfg // geometricBlockKind b = .line} ≃
      DeterminedLine cfg where
  toFun b := by
    rcases b with ⟨b, hb⟩
    cases b with
    | inl L => exact L
    | inr c => cases hb
  invFun L := ⟨.inl L, rfl⟩
  left_inv b := by
    rcases b with ⟨b, hb⟩
    cases b with
    | inl L => rfl
    | inr c => cases hb
  right_inv L := rfl

/-- Direct line-census Melchior gives the sign of the exact global line
slack. -/
theorem globalLineSlack_nonneg_of_lineMelchior
    {α : Type*} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (hmel : LineMelchior cfg) :
    0 ≤ globalLineSlack cfg := by
  unfold LineMelchior at hmel
  have hsum :
      (∑ b : {b : GeometricBlock cfg // geometricBlockKind b = .line},
          (3 - ((geometricBlockSupport cfg b.1).card : ℤ))) =
        ∑ L : DeterminedLine cfg,
          (3 - ((lineSupport cfg L).card : ℤ)) := by
    apply Fintype.sum_equiv (lineBlockEquiv cfg)
    intro b
    rcases b with ⟨b, hb⟩
    cases b with
    | inl L => rfl
    | inr c => cases hb
  change 0 ≤
    (∑ b : {b : GeometricBlock cfg // geometricBlockKind b = .line},
      (3 - ((geometricBlockSupport cfg b.1).card : ℤ))) - 3
  rw [hsum]
  omega

/-- Circle-tagged geometric blocks are exactly the determined circles. -/
def circleBlockEquiv
    {α : Type*} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) :
    {b : GeometricBlock cfg // geometricBlockKind b = .circle} ≃
      DeterminedCircle cfg where
  toFun b := by
    rcases b with ⟨b, hb⟩
    cases b with
    | inl L => cases hb
    | inr c => exact c
  invFun c := ⟨.inr c, rfl⟩
  left_inv b := by
    rcases b with ⟨b, hb⟩
    cases b with
    | inl L => cases hb
    | inr c => rfl
  right_inv c := rfl

theorem totalCircleCount_eq_card_determinedCircle
    {α : Type*} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) :
    (blockSystem cfg).totalCircleCount = Fintype.card (DeterminedCircle cfg) := by
  classical
  calc
    (blockSystem cfg).totalCircleCount =
        Fintype.card
          {b : GeometricBlock cfg // geometricBlockKind b = .circle} := by
      change
        (Finset.univ.filter (fun b : GeometricBlock cfg =>
          geometricBlockKind b = .circle)).card =
            Fintype.card
              {b : GeometricBlock cfg // geometricBlockKind b = .circle}
      exact (Fintype.card_subtype
        (fun b : GeometricBlock cfg => geometricBlockKind b = .circle)).symm
    _ = Fintype.card (DeterminedCircle cfg) :=
      Fintype.card_congr (circleBlockEquiv cfg)

/-- The tagged circle blocks count exactly the distinct proper circumcircles
determined by noncollinear selected triples. -/
theorem circleCount_eq_sum_circleBlockCount
    {α : Type*} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) :
    Erdos506.V4.circleCount cfg =
      ∑ s ∈ Finset.range (Fintype.card α + 1), circleBlockCount cfg s := by
  rw [Erdos506.V3.circleCount_eq_card_determinedCircle]
  rw [← totalCircleCount_eq_card_determinedCircle]
  exact (blockSystem cfg).totalCircleCount_eq_sum_circleCount

end Erdos506.V1
