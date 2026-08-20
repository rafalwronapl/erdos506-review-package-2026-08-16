import Erdos506.V1.Main
import Erdos506.V1.PairedConstruction
import Erdos506.V1.SharpSixConstruction
import Erdos506.V1.SharpSevenConstruction
import Erdos506.V1.SharpEightConstruction

/-!
# Sharp V1 constructions for every cardinality

The three exceptional finite examples are combined with the uniform paired
circle-and-centre family.  This is the upper-bound half needed by the exact
`IsLeast` formulation.
-/

namespace Erdos506.V1

open Erdos506.V4

theorem paired_decomposition (n : ℕ) :
    2 * ((n - 1) / 2) + (n - 1) % 2 = n - 1 := by omega

theorem paired_remainder_le_one (n : ℕ) : (n - 1) % 2 ≤ 1 := by omega

theorem pairedConfiguration_circleCount_eq_v1Target
    (n : ℕ) (hn : 4 ≤ n) (hn6 : n ≠ 6) (hn7 : n ≠ 7) (hn8 : n ≠ 8) :
    circleCount (pairedConfiguration ((n - 1) / 2) ((n - 1) % 2)
      (paired_remainder_le_one n)) = Erdos506.v1Target n := by
  let r := (n - 1) / 2
  let e := (n - 1) % 2
  have he : e ≤ 1 := paired_remainder_le_one n
  have hdecomp : 2 * r + e = n - 1 := by
    simpa [r, e] using paired_decomposition n
  have hboundary : 3 ≤ 2 * r + e := by omega
  let cfg := pairedConfiguration r e he
  have hadm : Admissible cfg := pairedConfiguration_admissible he hboundary
  have hcard : Fintype.card (PairedLabels r e) = n := by
    rw [card_pairedLabels, hdecomp]
    omega
  have hlower : Erdos506.v1Target n ≤ circleCount cfg := by
    have h := circleCount_ge_v1Target cfg hadm (by simpa [hcard] using hn)
    simpa [hcard] using h
  have hupper : circleCount cfg ≤
      1 + Nat.choose (n - 1) 2 - (n - 1) / 2 := by
    have h := pairedConfiguration_circleCount_le he hboundary
    simpa [hdecomp, r] using h
  have htarget : Erdos506.v1Target n =
      1 + Nat.choose (n - 1) 2 - (n - 1) / 2 := by
    simp [Erdos506.v1Target, hn6, hn7, hn8, Erdos506.v1UniformTarget]
  change circleCount cfg = Erdos506.v1Target n
  rw [htarget]
  exact Nat.le_antisymm hupper (by simpa [htarget] using hlower)

theorem exists_v1_extremizer (n : ℕ) (hn : 4 ≤ n) :
    ∃ (alpha : Type) (_ : Fintype alpha) (_ : DecidableEq alpha)
      (cfg : Configuration alpha),
      Fintype.card alpha = n ∧ Admissible cfg ∧
        circleCount cfg = Erdos506.v1Target n := by
  by_cases hn6 : n = 6
  · subst n
    refine ⟨Fin 6, inferInstance, inferInstance, sharpSixConfiguration,
      by simp, sharpSix_admissible, ?_⟩
    simpa [Erdos506.v1Target] using sharpSix_circleCount
  by_cases hn7 : n = 7
  · subst n
    refine ⟨Fin 7, inferInstance, inferInstance, sharpSevenConfiguration,
      by simp, sharpSeven_admissible, ?_⟩
    simpa [Erdos506.v1Target] using sharpSeven_circleCount
  by_cases hn8 : n = 8
  · subst n
    refine ⟨Fin 8, inferInstance, inferInstance, sharpEightConfiguration,
      by simp, sharpEight_admissible, ?_⟩
    simpa [Erdos506.v1Target] using sharpEight_circleCount
  · let r := (n - 1) / 2
    let e := (n - 1) % 2
    let he : e ≤ 1 := by simpa [e] using paired_remainder_le_one n
    let cfg := pairedConfiguration r e he
    have hdecomp : 2 * r + e = n - 1 := by
      simpa [r, e] using paired_decomposition n
    have hboundary : 3 ≤ 2 * r + e := by omega
    refine ⟨PairedLabels r e, inferInstance, inferInstance, cfg, ?_,
      pairedConfiguration_admissible he hboundary, ?_⟩
    · rw [card_pairedLabels, hdecomp]
      omega
    · simpa [cfg, r, e, he] using
        pairedConfiguration_circleCount_eq_v1Target n hn hn6 hn7 hn8

end Erdos506.V1
