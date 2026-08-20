import Erdos506.V1.ElevenFiveC40FinalPairDefect

/-!
# Saturation after a two-unit pair-moment defect

For any finite block family, pair intersections are at most two.  If its
pair moment is two below the all-double maximum and one pair is disjoint,
every other pair is forced to be double.  This is the common finite core of
the C40 five-block rows with five, six, or seven members.
-/

namespace Erdos506.V1

open Erdos506.Block
open Erdos506.Block.BlockSystem
open scoped BigOperators

universe u v

/-- A known zero pair exhausts a two-unit deficit from the all-double pair
moment.  Hence every other two-element subfamily has common support of
cardinality two. -/
theorem blockFamily_inter_card_eq_two_of_pairMoment_defect_two_of_disjoint_pair
    {Point : Type u} {Block : Type v} [Fintype Point] [Fintype Block]
    [DecidableEq Point] [DecidableEq Block]
    (S : BlockSystem Point Block) (F : Finset Block)
    (hmoment : ∑ p : Point, Nat.choose (S.degreeIn F p) 2 =
      2 * Nat.choose F.card 2 - 2)
    {f g : Block} (hf : f ∈ F) (hg : g ∈ F) (hfg : f ≠ g)
    (hdisjoint : (S.support f ∩ S.support g).card = 0) :
    ∀ b ∈ F, ∀ c ∈ F, b ≠ c →
      ({b, c} : Finset Block) ≠ ({f, g} : Finset Block) →
      (S.support b ∩ S.support c).card = 2 := by
  classical
  let Q := F.powersetCard 2
  let q : Finset Block → Nat := fun A => (S.commonSupport A).card
  have hQcard : Q.card = Nat.choose F.card 2 := by
    simp [Q]
  have hpairTotal :
      (∑ A ∈ Q, q A) = 2 * Nat.choose F.card 2 - 2 := by
    change (∑ A ∈ F.powersetCard 2, (S.commonSupport A).card) =
      2 * Nat.choose F.card 2 - 2
    rw [← S.binomial_degree_moment F 2]
    exact hmoment
  have hspecial : ({f, g} : Finset Block) ∈ Q := by
    change ({f, g} : Finset Block) ∈ F.powersetCard 2
    refine Finset.mem_powersetCard.mpr ⟨?_, ?_⟩
    · intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact hf
      · exact hg
    · simp [hfg]
  have hzero : q ({f, g} : Finset Block) = 0 := by
    dsimp [q]
    rw [S.commonSupport_pair]
    exact hdisjoint
  have hQpos : 0 < Q.card := Finset.card_pos.mpr ⟨_, hspecial⟩
  have hchoosePos : 0 < Nat.choose F.card 2 := by
    rwa [hQcard] at hQpos
  have hrestCard : (Q.erase ({f, g} : Finset Block)).card =
      Nat.choose F.card 2 - 1 := by
    rw [Finset.card_erase_of_mem hspecial, hQcard]
  have hsplit := Finset.sum_erase_add Q q hspecial
  have hrestSum :
      (∑ A ∈ Q.erase ({f, g} : Finset Block), q A) =
        2 * Nat.choose F.card 2 - 2 := by
    rw [hzero, hpairTotal] at hsplit
    omega
  have htermLe (A : Finset Block)
      (hA : A ∈ Q.erase ({f, g} : Finset Block)) : q A ≤ 2 := by
    dsimp [q]
    apply S.commonSupport_card_le_two
    have hAQ : A ∈ Q := Finset.mem_of_mem_erase hA
    have hAF : A ∈ F.powersetCard 2 := by
      simpa [Q] using hAQ
    exact (Finset.mem_powersetCard.mp hAF).2
  have hrestConst :
      (∑ _A ∈ Q.erase ({f, g} : Finset Block), 2) =
        2 * Nat.choose F.card 2 - 2 := by
    simp only [Finset.sum_const, nsmul_eq_mul]
    rw [hrestCard]
    change (Nat.choose F.card 2 - 1) * 2 =
      2 * Nat.choose F.card 2 - 2
    rw [Nat.sub_mul]
    omega
  have hall := (Finset.sum_eq_sum_iff_of_le htermLe).mp
    (hrestSum.trans hrestConst.symm)
  intro b hb c hc hbc hpairNe
  have hbcMem : ({b, c} : Finset Block) ∈ Q.erase ({f, g} : Finset Block) := by
    refine Finset.mem_erase.mpr ⟨hpairNe, ?_⟩
    change ({b, c} : Finset Block) ∈ F.powersetCard 2
    refine Finset.mem_powersetCard.mpr ⟨?_, ?_⟩
    · intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact hb
      · exact hc
    · simp [hbc]
  have hterm := hall {b, c} hbcMem
  simpa [q, S.commonSupport_pair] using hterm

end Erdos506.V1
