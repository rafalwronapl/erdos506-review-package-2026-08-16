import Erdos506.Finite.FourPentagonLedgerCore

/-!
# Local equality ledgers for the four-pentagon normal form

The two computations in this module range only over the powersets of the six
candidates through canonical point zero or canonical point one.  They are
kept separate from the larger residual ledger.
-/

namespace Erdos506.Finite

private theorem zero_local_bad_cases_empty :
    fourPentagonAtZero.powerset.filter (fun H =>
      fourPentagonCompatible H ∧
        ¬(H.card ≤ 3 ∧
          (H.card = 3 →
            ∃ o : Fin 2, H = fourPentagonZeroOrientation o))) = ∅ := by
  decide +kernel

/-- A compatible family through canonical point zero has size at most three;
equality forces one of the two displayed orientations. -/
theorem zero_local_ledger
    (H : Finset (Finset (Fin 10))) (hH : H ⊆ fourPentagonAtZero)
    (hcompat : fourPentagonCompatible H) :
    H.card ≤ 3 ∧
      (H.card = 3 → ∃ o : Fin 2, H = fourPentagonZeroOrientation o) := by
  have hpower : H ∈ fourPentagonAtZero.powerset :=
    Finset.mem_powerset.mpr hH
  by_contra hbad
  have hmem : H ∈ fourPentagonAtZero.powerset.filter (fun G =>
      fourPentagonCompatible G ∧
        ¬(G.card ≤ 3 ∧
          (G.card = 3 →
            ∃ o : Fin 2, G = fourPentagonZeroOrientation o))) :=
    Finset.mem_filter.mpr ⟨hpower, hcompat, hbad⟩
  rw [zero_local_bad_cases_empty] at hmem
  simp at hmem

private theorem one_local_bad_cases_empty :
    fourPentagonAtOne.powerset.filter (fun H =>
      fourPentagonCompatible H ∧
        ¬(H.card ≤ 3 ∧
          (H.card = 3 →
            ∃ o : Fin 2, H = fourPentagonOneOrientation o))) = ∅ := by
  decide +kernel

/-- A compatible family through canonical point one has size at most three;
equality forces one of the two displayed orientations. -/
theorem one_local_ledger
    (H : Finset (Finset (Fin 10))) (hH : H ⊆ fourPentagonAtOne)
    (hcompat : fourPentagonCompatible H) :
    H.card ≤ 3 ∧
      (H.card = 3 → ∃ o : Fin 2, H = fourPentagonOneOrientation o) := by
  have hpower : H ∈ fourPentagonAtOne.powerset :=
    Finset.mem_powerset.mpr hH
  by_contra hbad
  have hmem : H ∈ fourPentagonAtOne.powerset.filter (fun G =>
      fourPentagonCompatible G ∧
        ¬(G.card ≤ 3 ∧
          (G.card = 3 →
            ∃ o : Fin 2, G = fourPentagonOneOrientation o))) :=
    Finset.mem_filter.mpr ⟨hpower, hcompat, hbad⟩
  rw [one_local_bad_cases_empty] at hmem
  simp at hmem

end Erdos506.Finite
