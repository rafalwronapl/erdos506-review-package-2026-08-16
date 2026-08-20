import Mathlib.Tactic

/-!
# Core finite data for the four-pentagon ledger

This module contains the canonical five-blocks, the four-block candidate
family, its thirteen-colour bound, and the elementary symmetry used by the
local and residual ledgers.  All computed statements are bounded by explicit
finite candidate families.
-/

namespace Erdos506.Finite

/-- The four five-block supports in the forced normal form.  The point order
is `T,T',U₁,U₂,a,b,c,d,e,f`. -/
def fourPentagonFiveSupport : Fin 4 → Finset (Fin 10) := ![
  {0, 1, 2, 4, 5},
  {0, 1, 3, 6, 7},
  {0, 4, 6, 8, 9},
  {1, 5, 7, 8, 9}
]

/-- Four-subsets compatible with the four canonical five-blocks. -/
def fourPentagonCandidates : Finset (Finset (Fin 10)) :=
  ((Finset.univ : Finset (Fin 10)).powersetCard 4).filter fun Q =>
    ∀ j : Fin 4, (Q ∩ fourPentagonFiveSupport j).card ≤ 2

/-- Pairwise compatibility of a family of candidate four-subsets. -/
def fourPentagonCompatible (G : Finset (Finset (Fin 10))) : Prop :=
  ∀ Q ∈ G, ∀ R ∈ G, Q ≠ R → (Q ∩ R).card ≤ 2

instance (G : Finset (Finset (Fin 10))) :
    Decidable (fourPentagonCompatible G) := by
  unfold fourPentagonCompatible
  exact Finset.decidableDforallFinset

private def fourPentagonCoverTriple : Fin 13 → Finset (Fin 10) := ![
  {2, 3, 8}, {2, 3, 9}, {2, 7, 8}, {2, 7, 9},
  {3, 5, 8}, {3, 5, 9}, {1, 2, 6}, {1, 3, 4},
  {3, 4, 6}, {3, 4, 7}, {4, 6, 7}, {2, 5, 6}, {2, 3, 5}
]

private def fourPentagonCandidateColour (Q : Finset (Fin 10)) : Fin 13 :=
  if fourPentagonCoverTriple 0 ⊆ Q then 0 else
  if fourPentagonCoverTriple 1 ⊆ Q then 1 else
  if fourPentagonCoverTriple 2 ⊆ Q then 2 else
  if fourPentagonCoverTriple 3 ⊆ Q then 3 else
  if fourPentagonCoverTriple 4 ⊆ Q then 4 else
  if fourPentagonCoverTriple 5 ⊆ Q then 5 else
  if fourPentagonCoverTriple 6 ⊆ Q then 6 else
  if fourPentagonCoverTriple 7 ⊆ Q then 7 else
  if fourPentagonCoverTriple 8 ⊆ Q then 8 else
  if fourPentagonCoverTriple 9 ⊆ Q then 9 else
  if fourPentagonCoverTriple 10 ⊆ Q then 10 else
  if fourPentagonCoverTriple 11 ⊆ Q then 11 else 12

private theorem coverTriple_bad_cases_empty :
    fourPentagonCandidates.filter (fun Q =>
      ¬fourPentagonCoverTriple (fourPentagonCandidateColour Q) ⊆ Q) = ∅ := by
  decide +kernel

private theorem coverTriple_colour_subset
    (Q : Finset (Fin 10)) (hQ : Q ∈ fourPentagonCandidates) :
    fourPentagonCoverTriple (fourPentagonCandidateColour Q) ⊆ Q := by
  by_contra hbad
  have hmem : Q ∈ fourPentagonCandidates.filter (fun R =>
      ¬fourPentagonCoverTriple (fourPentagonCandidateColour R) ⊆ R) :=
    Finset.mem_filter.mpr ⟨hQ, hbad⟩
  rw [coverTriple_bad_cases_empty] at hmem
  simp at hmem

private theorem coverTriple_card (j : Fin 13) :
    (fourPentagonCoverTriple j).card = 3 := by
  fin_cases j <;> decide

private theorem candidateColour_conflict
    {Q R : Finset (Fin 10)}
    (hQ : Q ∈ fourPentagonCandidates)
    (hR : R ∈ fourPentagonCandidates)
    (hcolour : fourPentagonCandidateColour Q =
      fourPentagonCandidateColour R) :
    3 ≤ (Q ∩ R).card := by
  have hsub : fourPentagonCoverTriple
      (fourPentagonCandidateColour Q) ⊆ Q ∩ R := by
    intro i hi
    exact Finset.mem_inter.mpr ⟨
      coverTriple_colour_subset Q hQ hi,
      coverTriple_colour_subset R hR (by simpa [hcolour] using hi)⟩
  have hcard := Finset.card_le_card hsub
  rw [coverTriple_card] at hcard
  exact hcard

/-- A compatible family of canonical candidates has at most thirteen
members. -/
theorem compatible_candidates_card_le_thirteen
    (G : Finset (Finset (Fin 10))) (hG : G ⊆ fourPentagonCandidates)
    (hcompat : fourPentagonCompatible G) : G.card ≤ 13 := by
  have hcolourInj : Set.InjOn fourPentagonCandidateColour (G : Set _) := by
    intro Q hQ R hR hcolour
    by_contra hne
    have hlow := candidateColour_conflict (hG hQ) (hG hR) hcolour
    have hupp := hcompat Q hQ R hR hne
    omega
  have hcardImage := Finset.card_image_iff.mpr hcolourInj
  have hsubset : G.image fourPentagonCandidateColour ⊆
      (Finset.univ : Finset (Fin 13)) := Finset.subset_univ _
  have hle := Finset.card_le_card hsubset
  rw [hcardImage] at hle
  simpa using hle

def fourPentagonAtZero : Finset (Finset (Fin 10)) :=
  fourPentagonCandidates.filter fun Q => 0 ∈ Q

def fourPentagonAtOne : Finset (Finset (Fin 10)) :=
  fourPentagonCandidates.filter fun Q => 1 ∈ Q

def fourPentagonZeroOrientation : Fin 2 → Finset (Finset (Fin 10)) := ![
  {{0, 2, 3, 8}, {0, 2, 7, 9}, {0, 3, 5, 9}},
  {{0, 2, 3, 9}, {0, 2, 7, 8}, {0, 3, 5, 8}}
]

def fourPentagonOneOrientation : Fin 2 → Finset (Finset (Fin 10)) := ![
  {{1, 2, 3, 8}, {1, 2, 6, 9}, {1, 3, 4, 9}},
  {{1, 2, 3, 9}, {1, 2, 6, 8}, {1, 3, 4, 8}}
]

private theorem zero_one_bad_candidates_empty :
    fourPentagonCandidates.filter (fun Q => 0 ∈ Q ∧ 1 ∈ Q) = ∅ := by
  decide +kernel

/-- A candidate cannot contain both canonical high-degree points. -/
theorem candidate_not_mem_zero_and_one
    (Q : Finset (Fin 10)) (hQ : Q ∈ fourPentagonCandidates) :
    ¬(0 ∈ Q ∧ 1 ∈ Q) := by
  intro hboth
  have hmem : Q ∈ fourPentagonCandidates.filter
      (fun R => 0 ∈ R ∧ 1 ∈ R) := Finset.mem_filter.mpr ⟨hQ, hboth⟩
  rw [zero_one_bad_candidates_empty] at hmem
  simp at hmem

/-- The two local equality families cannot have the same orientation. -/
theorem same_orientations_conflict (o : Fin 2) :
    ¬fourPentagonCompatible
      (fourPentagonZeroOrientation o ∪ fourPentagonOneOrientation o) := by
  fin_cases o
  · intro hcompat
    have hupp := hcompat ({0, 2, 3, 8} : Finset (Fin 10)) (by decide)
      ({1, 2, 3, 8} : Finset (Fin 10)) (by decide) (by decide)
    have hthree : (({0, 2, 3, 8} : Finset (Fin 10)) ∩
        ({1, 2, 3, 8} : Finset (Fin 10))).card = 3 := by
      decide
    omega
  · intro hcompat
    have hupp := hcompat ({0, 2, 3, 9} : Finset (Fin 10)) (by decide)
      ({1, 2, 3, 9} : Finset (Fin 10)) (by decide) (by decide)
    have hthree : (({0, 2, 3, 9} : Finset (Fin 10)) ∩
        ({1, 2, 3, 9} : Finset (Fin 10))).card = 3 := by
      decide
    omega

/-- The residual symmetry exchanging the last two canonical points. -/
def fourPentagonSwapEightNine : Equiv.Perm (Fin 10) := Equiv.swap 8 9

def fourPentagonSwapSupport (Q : Finset (Fin 10)) : Finset (Fin 10) :=
  Q.image fourPentagonSwapEightNine

theorem swap_five_support (j : Fin 4) :
    fourPentagonSwapSupport (fourPentagonFiveSupport j) =
      fourPentagonFiveSupport j := by
  fin_cases j <;> decide

theorem swap_zero_orientation :
    (fourPentagonZeroOrientation 1).image fourPentagonSwapSupport =
      fourPentagonZeroOrientation 0 := by
  decide

theorem swap_one_orientation :
    (fourPentagonOneOrientation 0).image fourPentagonSwapSupport =
      fourPentagonOneOrientation 1 := by
  decide

theorem swapSupport_involutive (Q : Finset (Fin 10)) :
    fourPentagonSwapSupport (fourPentagonSwapSupport Q) = Q := by
  ext i
  simp [fourPentagonSwapSupport, fourPentagonSwapEightNine]

theorem swapSupport_injective :
    Function.Injective fourPentagonSwapSupport := by
  intro Q R h
  have := congrArg fourPentagonSwapSupport h
  simpa [swapSupport_involutive] using this

private theorem mem_zero_swapSupport (Q : Finset (Fin 10)) :
    0 ∈ fourPentagonSwapSupport Q ↔ 0 ∈ Q := by
  revert Q
  decide +kernel

private theorem mem_one_swapSupport (Q : Finset (Fin 10)) :
    1 ∈ fourPentagonSwapSupport Q ↔ 1 ∈ Q := by
  revert Q
  decide +kernel

theorem filter_zero_image_swap (G : Finset (Finset (Fin 10))) :
    (G.image fourPentagonSwapSupport).filter (fun Q => 0 ∈ Q) =
      (G.filter fun Q => 0 ∈ Q).image fourPentagonSwapSupport := by
  ext Q
  simp only [Finset.mem_filter, Finset.mem_image]
  constructor
  · rintro ⟨⟨R, hRG, rfl⟩, hzero⟩
    exact ⟨R, ⟨hRG, (mem_zero_swapSupport R).mp hzero⟩, rfl⟩
  · rintro ⟨R, ⟨hRG, hzero⟩, rfl⟩
    exact ⟨⟨R, hRG, rfl⟩, (mem_zero_swapSupport R).mpr hzero⟩

theorem filter_one_image_swap (G : Finset (Finset (Fin 10))) :
    (G.image fourPentagonSwapSupport).filter (fun Q => 1 ∈ Q) =
      (G.filter fun Q => 1 ∈ Q).image fourPentagonSwapSupport := by
  ext Q
  simp only [Finset.mem_filter, Finset.mem_image]
  constructor
  · rintro ⟨⟨R, hRG, rfl⟩, hone⟩
    exact ⟨R, ⟨hRG, (mem_one_swapSupport R).mp hone⟩, rfl⟩
  · rintro ⟨R, ⟨hRG, hone⟩, rfl⟩
    exact ⟨⟨R, hRG, rfl⟩, (mem_one_swapSupport R).mpr hone⟩

end Erdos506.Finite
