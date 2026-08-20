import Erdos506.V3.PivotSum

/-!
# Census of determined circles by support size

These lemmas regroup arbitrary finite sums over determined circles by the
cardinality of their selected support.  The specialised rows for caps four
and five are the exact equations used in the small V3 cases.
-/

namespace Erdos506.V3

open Erdos506.V4
open scoped BigOperators

noncomputable def circleCensus {α : Type*} [Fintype α]
    (cfg : Configuration α) (s : ℕ) : ℕ := by
  classical
  exact (Finset.univ.filter fun c : DeterminedCircle cfg =>
    (circleTrace cfg c.1).card = s).card

theorem sum_by_circleSupportCard
    {α M : Type*} [Fintype α] [AddCommMonoid M]
    (cfg : Configuration α) (m : ℕ)
    (hcap : ∀ c : DeterminedCircle cfg, (circleTrace cfg c.1).card ≤ m)
    (w : ℕ → M) :
    (∑ c : DeterminedCircle cfg, w (circleTrace cfg c.1).card) =
      ∑ s ∈ Finset.Icc 3 m, (circleCensus cfg s) • w s := by
  classical
  let size : DeterminedCircle cfg → ℕ :=
    fun c => (circleTrace cfg c.1).card
  have hmaps : ∀ c ∈ (Finset.univ : Finset (DeterminedCircle cfg)),
      size c ∈ Finset.Icc 3 m := by
    intro c hc
    exact Finset.mem_Icc.mpr ⟨circleSupport_card_ge_three cfg c, hcap c⟩
  have hfiber := Finset.sum_fiberwise_of_maps_to hmaps
    (fun c : DeterminedCircle cfg => w (size c))
  have hinner : ∀ s ∈ Finset.Icc 3 m,
      (∑ c ∈ (Finset.univ.filter fun c : DeterminedCircle cfg => size c = s),
        w (size c)) = circleCensus cfg s • w s := by
    intro s hs
    calc
      (∑ c ∈ (Finset.univ.filter fun c : DeterminedCircle cfg => size c = s),
          w (size c)) =
          ∑ _c ∈ (Finset.univ.filter fun c : DeterminedCircle cfg => size c = s),
            w s := by
        apply Finset.sum_congr rfl
        intro c hc
        rw [(Finset.mem_filter.mp hc).2]
      _ = circleCensus cfg s • w s := by
        simp only [Finset.sum_const]
        rfl
  have hleft :
      (∑ s ∈ Finset.Icc 3 m,
          ∑ c ∈ (Finset.univ.filter fun c : DeterminedCircle cfg => size c = s),
            w (size c)) =
        ∑ s ∈ Finset.Icc 3 m, circleCensus cfg s • w s := by
    apply Finset.sum_congr rfl
    intro s hs
    exact hinner s hs
  rw [hleft] at hfiber
  exact hfiber.symm

theorem circleCount_eq_census_sum
    {α : Type*} [Fintype α] (cfg : Configuration α) (m : ℕ)
    (hcap : ∀ c : DeterminedCircle cfg, (circleTrace cfg c.1).card ≤ m) :
    circleCount cfg = ∑ s ∈ Finset.Icc 3 m, circleCensus cfg s := by
  have h := sum_by_circleSupportCard cfg m hcap (fun _ => (1 : ℕ))
  simp only [nsmul_eq_mul, mul_one] at h
  rw [circleCount_eq_card_determinedCircle cfg]
  simpa using h

theorem triplePartition_eq_census_sum
    {α : Type*} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (hthree : NoThreeCollinear cfg) (m : ℕ)
    (hcap : ∀ c : DeterminedCircle cfg, (circleTrace cfg c.1).card ≤ m) :
    Nat.choose (Fintype.card α) 3 =
      ∑ s ∈ Finset.Icc 3 m, circleCensus cfg s * Nat.choose s 3 := by
  have h := sum_by_circleSupportCard cfg m hcap (fun s => Nat.choose s 3)
  simp only [nsmul_eq_mul] at h
  rw [triple_partition cfg hthree] at h
  simpa using h

theorem circleCount_eq_c3_add_c4
    {α : Type*} [Fintype α] (cfg : Configuration α)
    (hcap : ∀ c : DeterminedCircle cfg, (circleTrace cfg c.1).card ≤ 4) :
    circleCount cfg = circleCensus cfg 3 + circleCensus cfg 4 := by
  have h := circleCount_eq_census_sum cfg 4 hcap
  norm_num at h
  exact h

theorem triplePartition_eq_c3_add_four_c4
    {α : Type*} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (hthree : NoThreeCollinear cfg)
    (hcap : ∀ c : DeterminedCircle cfg, (circleTrace cfg c.1).card ≤ 4) :
    Nat.choose (Fintype.card α) 3 =
      circleCensus cfg 3 + 4 * circleCensus cfg 4 := by
  have h := triplePartition_eq_census_sum cfg hthree 4 hcap
  have hi : Finset.Icc 3 4 = {3, 4} := by decide
  rw [hi] at h
  norm_num [Nat.choose] at h
  omega

theorem circleCount_eq_c3_add_c4_add_c5
    {α : Type*} [Fintype α] (cfg : Configuration α)
    (hcap : ∀ c : DeterminedCircle cfg, (circleTrace cfg c.1).card ≤ 5) :
    circleCount cfg =
      circleCensus cfg 3 + circleCensus cfg 4 + circleCensus cfg 5 := by
  have h := circleCount_eq_census_sum cfg 5 hcap
  have hi : Finset.Icc 3 5 = {3, 4, 5} := by decide
  rw [hi] at h
  simp at h
  omega

theorem triplePartition_eq_c3_add_four_c4_add_ten_c5
    {α : Type*} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (hthree : NoThreeCollinear cfg)
    (hcap : ∀ c : DeterminedCircle cfg, (circleTrace cfg c.1).card ≤ 5) :
    Nat.choose (Fintype.card α) 3 =
      circleCensus cfg 3 + 4 * circleCensus cfg 4 +
        10 * circleCensus cfg 5 := by
  have h := triplePartition_eq_census_sum cfg hthree 5 hcap
  have hi : Finset.Icc 3 5 = {3, 4, 5} := by decide
  rw [hi] at h
  norm_num [Nat.choose] at h
  omega

theorem c3_lower_of_summedMelchior_cap_four
    {α : Type*} [Fintype α] (cfg : Configuration α)
    (hmel : SummedMelchior cfg)
    (hcap : ∀ c : DeterminedCircle cfg, (circleTrace cfg c.1).card ≤ 4) :
    Fintype.card α ≤ circleCensus cfg 3 := by
  have hgroup := sum_by_circleSupportCard cfg 4 hcap
    (fun s : ℕ => (s : ℚ) * (4 - (s : ℚ)))
  have hmel' := hmel
  change 3 * (Fintype.card α : ℚ) ≤
    ∑ c : DeterminedCircle cfg,
      (circleTrace cfg c.1).card *
        (4 - (circleTrace cfg c.1).card : ℚ) at hmel'
  rw [hgroup] at hmel'
  have hi : Finset.Icc 3 4 = {3, 4} := by decide
  rw [hi] at hmel'
  norm_num [nsmul_eq_mul] at hmel'
  exact_mod_cast (show (Fintype.card α : ℚ) ≤ circleCensus cfg 3 by linarith)

theorem melchior_c3_c5_row
    {α : Type*} [Fintype α] (cfg : Configuration α)
    (hmel : SummedMelchior cfg)
    (hcap : ∀ c : DeterminedCircle cfg, (circleTrace cfg c.1).card ≤ 5) :
    3 * Fintype.card α + 5 * circleCensus cfg 5 ≤
      3 * circleCensus cfg 3 := by
  have hgroup := sum_by_circleSupportCard cfg 5 hcap
    (fun s : ℕ => (s : ℚ) * (4 - (s : ℚ)))
  have hmel' := hmel
  change 3 * (Fintype.card α : ℚ) ≤
    ∑ c : DeterminedCircle cfg,
      (circleTrace cfg c.1).card *
        (4 - (circleTrace cfg c.1).card : ℚ) at hmel'
  rw [hgroup] at hmel'
  have hi : Finset.Icc 3 5 = {3, 4, 5} := by decide
  rw [hi] at hmel'
  norm_num [nsmul_eq_mul] at hmel'
  exact_mod_cast (show
    3 * (Fintype.card α : ℚ) + 5 * circleCensus cfg 5 ≤
      3 * circleCensus cfg 3 by linarith)

end Erdos506.V3
