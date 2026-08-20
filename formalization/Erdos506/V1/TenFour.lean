import Erdos506.V1.NineOrdinaryMatchingCap
import Erdos506.V1.Ten

/-!
# The ten-point maximum-four branch

The numerical rows in `Ten` force twenty generalized three-blocks, thirteen
of which are lines, and the pointwise profile `(d3,d4,d5) = (6,10,0)`.
The nine-point deletion and ordinary-matching cap show that every selected
label lies on at most three of the forced three-lines.  Their total incidence
would therefore be at most thirty, contradicting the forced value thirty-nine.
-/

namespace Erdos506.V1

open Erdos506.Block
open Erdos506.Block.BlockSystem
open Erdos506.Finite
open Erdos506.Incidence
open Erdos506.V4
open scoped BigOperators

universe u

/-- The forced maximum-four profile is impossible: the nine-point ordinary
matching cap bounds each local three-line degree by three, whereas thirteen
three-lines require thirty-nine incidences on ten labels. -/
theorem circleCount_ge_thirty_three_of_card_ten_of_circle_cap_four
    {α : Type u} [Fintype α] [DecidableEq α]
    (Mel : RealPlaneMelchiorPrinciple.{u})
    (EvenArr : RealPlaneEvenArrangementPrinciple.{u})
    (KM : RealPlaneKellyMoserPrinciple.{u})
    (cfg : Configuration α) (hadm : Admissible cfg)
    (hcard : Fintype.card α = 10)
    (hcircle : ∀ c : DeterminedCircle cfg,
      (circleTrace cfg c.1).card ≤ 4) :
    33 ≤ Erdos506.V4.circleCount cfg := by
  classical
  by_contra htarget
  have hcount : Erdos506.V4.circleCount cfg ≤ 32 := by omega
  let S := blockSystem cfg
  have hprofile := ten_circle_cap_four_forced_profile
    Mel KM cfg hadm hcard hcount hcircle
  change S.blockCount 3 = 20 ∧ S.blockCount 4 = 25 ∧
      S.blockCount 5 = 0 ∧ S.lineCount 3 = 13 ∧
      S.lineCount 4 = 0 ∧ S.lineCount 5 = 0 ∧
      S.circleCount 3 = 7 ∧ S.circleCount 4 = 25 ∧
      S.totalCircleCount = 32 ∧
      ∀ p : α, S.blockDegree 3 p = 6 ∧
        S.blockDegree 4 p = 10 ∧ S.blockDegree 5 p = 0 at hprofile
  obtain ⟨_hB3, _hB4, _hB5, hL3, _hL4, _hL5,
    _hC3, _hC4, _hC, hdegrees⟩ := hprofile
  have hlocal (p : α) : S.lineDegree 3 p ≤ 3 := by
    have hbound := tenExceptionalPivot_lineDegree_three_le_three
      Mel EvenArr cfg hadm hcard p
        (by simpa [S] using (hdegrees p).1)
        (by simpa [S] using (hdegrees p).2.1)
    simpa [S] using hbound
  have hsumLe : (∑ p : α, S.lineDegree 3 p) ≤ 30 := by
    calc
      (∑ p : α, S.lineDegree 3 p) ≤ ∑ _p : α, 3 :=
        Finset.sum_le_sum fun p _hp => hlocal p
      _ = 30 := by simp [hcard]
  have hinc := S.line_incidence 3
  rw [hL3] at hinc
  norm_num at hinc
  omega

/-- Router leaving only a selected five-point circle.  The six-point branch
is already closed by U17 in `Ten`, while the maximum-four branch is closed
above by the nine-point ordinary-matching cap. -/
theorem circleCount_ge_thirty_three_of_card_ten_of_five_circle_endpoint
    {α : Type u} [Fintype α] [DecidableEq α]
    (Mel : RealPlaneMelchiorPrinciple.{u})
    (EvenArr : RealPlaneEvenArrangementPrinciple.{u})
    (KM : RealPlaneKellyMoserPrinciple.{u})
    (U17 : RealPlaneSixCircleU17Principle.{u})
    (cfg : Configuration α) (hadm : Admissible cfg)
    (hcard : Fintype.card α = 10)
    (fiveCircleEndpoint :
      ∀ c : DeterminedCircle cfg,
        (circleTrace cfg c.1).card = 5 →
          33 ≤ Erdos506.V4.circleCount cfg) :
    33 ≤ Erdos506.V4.circleCount cfg := by
  rcases circle_cap_five_or_circleCount_ge_thirty_three_of_card_ten
      Mel U17 cfg hadm hcard with hcapFive | htarget
  · by_cases hcapFour : ∀ c : DeterminedCircle cfg,
        (circleTrace cfg c.1).card ≤ 4
    · exact circleCount_ge_thirty_three_of_card_ten_of_circle_cap_four
        Mel EvenArr KM cfg hadm hcard hcapFour
    · push Not at hcapFour
      obtain ⟨c, hcLarge⟩ := hcapFour
      have hcFive : (circleTrace cfg c.1).card = 5 := by
        have := hcapFive c
        omega
      exact fiveCircleEndpoint c hcFive
  · exact htarget

end Erdos506.V1
