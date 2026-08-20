import Erdos506.Incidence.SixConicLineIncidenceGeometry
import Erdos506.Incidence.SixConicU17
import Mathlib.Tactic

/-!
# The six-conic line bound on eight outsiders

The field-free five-outsider theorem can be averaged over all five-subsets
of an eight-set.  Every outsider occurs in exactly `choose 7 4 = 35` such
subsets, while there are `choose 8 5 = 56` subsets in total.  This gives the
sharp integral consequence `J <= 22` for the full eight-set.
-/

namespace Erdos506.Incidence

open Erdos506.V1
open Erdos506.V4
open scoped BigOperators

universe u

/-- Rewrite the line incidence of a subset as an indicator sum over a fixed
ambient outsider set. -/
theorem sixConicLineIncidence_eq_ambient_outsider_sum
    {α : Type u} [Fintype α] [DecidableEq α]
    (cfg : Erdos506.V4.Configuration α)
    (gamma : Erdos506.V1.DeterminedCircle cfg)
    {X Y : Finset α} (hYX : Y ⊆ X) :
    sixConicLineIncidence cfg gamma Y =
      ∑ x ∈ X, if x ∈ Y then
        Fintype.card (SixConicMarkedLineAt cfg gamma x) else 0 := by
  classical
  rw [sixConicLineIncidence_eq_sum_card_markedLineAt]
  rw [← Finset.sum_filter]
  congr 1
  ext x
  simp only [Finset.mem_filter]
  constructor
  · intro hx
    exact ⟨hYX hx, hx⟩
  · exact fun hx => hx.2

/-- Summing `J` over all five-subsets of an eight-set counts each outsider
exactly thirty-five times. -/
theorem sum_sixConicLineIncidence_powersetCard_five_of_card_eight
    {α : Type u} [Fintype α] [DecidableEq α]
    (cfg : Erdos506.V4.Configuration α)
    (gamma : Erdos506.V1.DeterminedCircle cfg)
    (X : Finset α) (hX : X.card = 8) :
    (∑ Y ∈ X.powersetCard 5, sixConicLineIncidence cfg gamma Y) =
      35 * sixConicLineIncidence cfg gamma X := by
  classical
  calc
    (∑ Y ∈ X.powersetCard 5, sixConicLineIncidence cfg gamma Y) =
        ∑ Y ∈ X.powersetCard 5, ∑ x ∈ X,
          if x ∈ Y then
            Fintype.card (SixConicMarkedLineAt cfg gamma x) else 0 := by
      apply Finset.sum_congr rfl
      intro Y hY
      exact sixConicLineIncidence_eq_ambient_outsider_sum
        cfg gamma (Finset.mem_powersetCard.mp hY).1
    _ = ∑ x ∈ X, ∑ Y ∈ X.powersetCard 5,
          if x ∈ Y then
            Fintype.card (SixConicMarkedLineAt cfg gamma x) else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ x ∈ X,
          35 * Fintype.card (SixConicMarkedLineAt cfg gamma x) := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [← Finset.sum_filter]
      have hcount := Finset.card_filter_powersetCard_subset
        ({x} : Finset α) X 5 (by simp [hx]) (by simp)
      have hcount' :
          ((X.powersetCard 5).filter fun Y => x ∈ Y).card = 35 := by
        simpa [Finset.singleton_subset_iff, hX, Nat.choose] using hcount
      simp only [Finset.sum_const, nsmul_eq_mul]
      rw [hcount']
      norm_num
    _ = 35 * sixConicLineIncidence cfg gamma X := by
      rw [sixConicLineIncidence_eq_sum_card_markedLineAt,
        Finset.mul_sum]

/-- Eight outsiders of a selected six-conic carry at most twenty-two
incidences with determined lines meeting the conic in two selected labels. -/
theorem sixConic_line_incidence_le_twenty_two_of_card_eight
    {α : Type u} [Fintype α] [DecidableEq α]
    (cfg : Erdos506.V4.Configuration α)
    (gamma : Erdos506.V1.DeterminedCircle cfg)
    (hgamma : (circleTrace cfg gamma.1).card = 6)
    (X : Finset α) (hX : X.card = 8)
    (hdisjoint : Disjoint (circleTrace cfg gamma.1) X) :
    sixConicLineIncidence cfg gamma X ≤ 22 := by
  classical
  have hlocal (Y : Finset α) (hY : Y ∈ X.powersetCard 5) :
      sixConicLineIncidence cfg gamma Y ≤ 14 := by
    have hYspec := Finset.mem_powersetCard.mp hY
    have hdisjointY : Disjoint (circleTrace cfg gamma.1) Y := by
      rw [Finset.disjoint_left] at hdisjoint ⊢
      intro z hzD hzY
      exact hdisjoint hzD (hYspec.1 hzY)
    exact sixConic_line_incidence_le_fourteen
      cfg gamma hgamma Y hYspec.2 hdisjointY
  have hsumLe :
      (∑ Y ∈ X.powersetCard 5,
        sixConicLineIncidence cfg gamma Y) ≤
      ∑ _Y ∈ X.powersetCard 5, 14 := by
    apply Finset.sum_le_sum
    intro Y hY
    exact hlocal Y hY
  have hright : (∑ _Y ∈ X.powersetCard 5, 14) = 784 := by
    simp only [Finset.sum_const, nsmul_eq_mul,
      Finset.card_powersetCard, hX]
    norm_num [Nat.choose]
  rw [sum_sixConicLineIncidence_powersetCard_five_of_card_eight
      cfg gamma X hX, hright] at hsumLe
  omega

/-- Every outsider pair belongs to exactly fifteen four-subsets of an
eight-set. -/
theorem sum_sixConicTotalWeight_powersetCard_four_of_card_eight
    {α : Type u} [Fintype α] [DecidableEq α]
    (cfg : Erdos506.V4.Configuration α)
    (gamma : Erdos506.V1.DeterminedCircle cfg)
    (X : Finset α) (hX : X.card = 8) :
    (∑ Y ∈ X.powersetCard 4, sixConicTotalWeight cfg gamma Y) =
      15 * sixConicTotalWeight cfg gamma X := by
  classical
  calc
    (∑ Y ∈ X.powersetCard 4, sixConicTotalWeight cfg gamma Y) =
        ∑ Y ∈ X.powersetCard 4, ∑ e ∈ X.powersetCard 2,
          if e ⊆ Y then sixConicPairWeight cfg gamma e else 0 := by
      apply Finset.sum_congr rfl
      intro Y hY
      exact sixConicTotalWeight_eq_ambient_sum cfg gamma
        (Finset.mem_powersetCard.mp hY).1
    _ = ∑ e ∈ X.powersetCard 2, ∑ Y ∈ X.powersetCard 4,
          if e ⊆ Y then sixConicPairWeight cfg gamma e else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ e ∈ X.powersetCard 2,
          15 * sixConicPairWeight cfg gamma e := by
      apply Finset.sum_congr rfl
      intro e he
      have heSpec := Finset.mem_powersetCard.mp he
      rw [← Finset.sum_filter]
      have hcount := Finset.card_filter_powersetCard_subset
        e X 4 heSpec.1 (by omega)
      simp only [Finset.sum_const, nsmul_eq_mul]
      rw [hcount, hX, heSpec.2]
      norm_num [Nat.choose]
    _ = 15 * sixConicTotalWeight cfg gamma X := by
      unfold sixConicTotalWeight
      rw [Finset.mul_sum]

/-- The averaged U17 bound on all outsider pairs of an eight-set. -/
theorem sixConic_weight_le_seventy_nine_of_card_eight
    {α : Type u} [Fintype α] [DecidableEq α]
    (cfg : Erdos506.V4.Configuration α)
    (gamma : Erdos506.V1.DeterminedCircle cfg)
    (hgamma : (circleTrace cfg gamma.1).card = 6)
    (X : Finset α) (hX : X.card = 8)
    (hdisjoint : Disjoint (circleTrace cfg gamma.1) X) :
    sixConicWeight cfg gamma X ≤ 79 := by
  classical
  have hlocal (Y : Finset α) (hY : Y ∈ X.powersetCard 4) :
      sixConicTotalWeight cfg gamma Y ≤ 17 := by
    have hYspec := Finset.mem_powersetCard.mp hY
    have hdisjointY : Disjoint (circleTrace cfg gamma.1) Y := by
      rw [Finset.disjoint_left] at hdisjoint ⊢
      intro z hzD hzY
      exact hdisjoint hzD (hYspec.1 hzY)
    rw [sixConicTotalWeight_eq_sixConicWeight]
    exact sixConicWeight_le_seventeen
      cfg gamma hgamma Y hYspec.2 hdisjointY
  have hsumLe :
      (∑ Y ∈ X.powersetCard 4,
        sixConicTotalWeight cfg gamma Y) ≤
      ∑ _Y ∈ X.powersetCard 4, 17 := by
    apply Finset.sum_le_sum
    intro Y hY
    exact hlocal Y hY
  have hright : (∑ _Y ∈ X.powersetCard 4, 17) = 1190 := by
    simp only [Finset.sum_const, nsmul_eq_mul,
      Finset.card_powersetCard, hX]
    norm_num [Nat.choose]
  rw [sum_sixConicTotalWeight_powersetCard_four_of_card_eight
      cfg gamma X hX, hright] at hsumLe
  rw [← sixConicTotalWeight_eq_sixConicWeight]
  omega

end Erdos506.Incidence
