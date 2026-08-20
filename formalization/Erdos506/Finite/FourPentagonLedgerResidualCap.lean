import Erdos506.Finite.FourPentagonLedgerCore

/-!
# The residual cardinality cap in the four-pentagon ledger

The thirteen residual candidates are explicitly coloured with seven colours.
The only computed statement in this module checks pairs of candidates with
the same colour.  A compatible family therefore injects into `Fin 7`.
-/

namespace Erdos506.Finite

def fourPentagonForcedSix : Finset (Finset (Fin 10)) :=
  fourPentagonZeroOrientation 0 ∪ fourPentagonOneOrientation 1

def fourPentagonResidualCandidates : Finset (Finset (Fin 10)) :=
  fourPentagonCandidates.filter fun Q =>
    0 ∉ Q ∧ 1 ∉ Q ∧
      ∀ R ∈ fourPentagonForcedSix, (Q ∩ R).card ≤ 2

def fourPentagonResidualEquality : Finset (Finset (Fin 10)) := {
  {2, 3, 4, 6}, {2, 3, 5, 7}, {2, 4, 7, 8}, {2, 5, 6, 9},
  {3, 4, 7, 9}, {3, 5, 6, 8}, {4, 5, 6, 7}
}

/-- An explicit indexing of all thirteen residual candidates. -/
def fourPentagonResidualCandidate : Fin 13 → Finset (Fin 10) := ![
  {2, 3, 4, 6}, {2, 3, 4, 7}, {2, 3, 5, 6}, {2, 3, 5, 7},
  {2, 4, 6, 7}, {2, 4, 7, 8}, {2, 5, 6, 7}, {2, 5, 6, 9},
  {3, 4, 5, 6}, {3, 4, 5, 7}, {3, 4, 7, 9}, {3, 5, 6, 8},
  {4, 5, 6, 7}
]

private theorem residualCandidates_eq_indexed :
    fourPentagonResidualCandidates =
      (Finset.univ : Finset (Fin 13)).image
        fourPentagonResidualCandidate := by
  decide +kernel

private theorem exists_residualCandidate_of_mem
    {Q : Finset (Fin 10)} (hQ : Q ∈ fourPentagonResidualCandidates) :
    ∃ i : Fin 13, fourPentagonResidualCandidate i = Q := by
  have hlisted : Q ∈ (Finset.univ : Finset (Fin 13)).image
      fourPentagonResidualCandidate := by
    rw [← residualCandidates_eq_indexed]
    exact hQ
  obtain ⟨i, _hi, hQi⟩ := Finset.mem_image.mp hlisted
  exact ⟨i, hQi⟩

/-- A seven-colouring of the residual conflict graph.  Each of the first six
colours pairs one canonical equality candidate with one alternative; the last
colour contains the remaining equality candidate. -/
def fourPentagonResidualColor (Q : Finset (Fin 10)) : Fin 7 :=
  if Q = {2, 3, 4, 6} ∨ Q = {3, 4, 5, 6} then 0 else
  if Q = {2, 3, 5, 7} ∨ Q = {3, 4, 5, 7} then 1 else
  if Q = {2, 4, 7, 8} ∨ Q = {2, 4, 6, 7} then 2 else
  if Q = {2, 5, 6, 9} ∨ Q = {2, 5, 6, 7} then 3 else
  if Q = {3, 4, 7, 9} ∨ Q = {2, 3, 4, 7} then 4 else
  if Q = {3, 5, 6, 8} ∨ Q = {2, 3, 5, 6} then 5 else 6

private theorem residual_index_same_color_conflict
    (i j : Fin 13)
    (hij : fourPentagonResidualCandidate i ≠
      fourPentagonResidualCandidate j)
    (hcolor : fourPentagonResidualColor
        (fourPentagonResidualCandidate i) =
      fourPentagonResidualColor (fourPentagonResidualCandidate j)) :
    3 ≤ (fourPentagonResidualCandidate i ∩
      fourPentagonResidualCandidate j).card := by
  revert i j
  decide +kernel

/-- Distinct residual candidates with the same colour are incompatible. -/
theorem residual_same_color_conflict
    {Q R : Finset (Fin 10)}
    (hQ : Q ∈ fourPentagonResidualCandidates)
    (hR : R ∈ fourPentagonResidualCandidates)
    (hQR : Q ≠ R)
    (hcolor : fourPentagonResidualColor Q =
      fourPentagonResidualColor R) :
    3 ≤ (Q ∩ R).card := by
  obtain ⟨i, rfl⟩ := exists_residualCandidate_of_mem hQ
  obtain ⟨j, rfl⟩ := exists_residualCandidate_of_mem hR
  exact residual_index_same_color_conflict i j hQR hcolor

/-- Every compatible residual family has at most seven members. -/
theorem residual_card_le_seven
    (H : Finset (Finset (Fin 10)))
    (hH : H ⊆ fourPentagonResidualCandidates)
    (hcompat : fourPentagonCompatible H) : H.card ≤ 7 := by
  let color : {Q : Finset (Fin 10) // Q ∈ H} → Fin 7 :=
    fun Q => fourPentagonResidualColor Q.1
  have hcolorInj : Function.Injective color := by
    intro Q R hcolor
    apply Subtype.ext
    by_contra hQR
    change fourPentagonResidualColor Q.1 =
      fourPentagonResidualColor R.1 at hcolor
    have hlow := residual_same_color_conflict
      (hH Q.2) (hH R.2) hQR hcolor
    have hupp := hcompat Q.1 Q.2 R.1 R.2 hQR
    omega
  have hcard := Fintype.card_le_of_injective color hcolorInj
  simpa only [Fintype.card_coe, Fintype.card_fin] using hcard

end Erdos506.Finite
