import Mathlib

/-!
# The finite six-label allowable-sequence computation

This file contains the finite core of the even case of Ungar's direction
theorem for six labels.  A row is a permutation of the six labels.  One
allowable move cuts the row into consecutive blocks, each of which is
increasing in the original labelling, and reverses every block.  Singleton
blocks record positions which do not move.

There are only `2^5` ways to cut a six-entry row.  We use those cut masks to
compute the rows reachable from `012345`, pruning after every move.  The
reverse row is reachable in one move (the monochromatic/collinear case), is
not reachable in two through five moves, and is reachable again in six
moves.  The negative statements are the exact finite endpoint needed by the
geometric rotating-line construction.
-/

namespace Erdos506.Finite

/-- A six-label row, represented by the label occupying each of the six
positions. -/
abbrev SixRow := Equiv.Perm (Fin 6)

namespace SixRow

/-- The increasing initial row `012345`. -/
def initial : SixRow := Equiv.refl (Fin 6)

/-- The decreasing final row `543210`. -/
def reversed : SixRow :=
  { toFun := fun i => ⟨5 - i.1, by omega⟩
    invFun := fun i => ⟨5 - i.1, by omega⟩
    left_inv := by
      intro i
      apply Fin.ext
      simp only
      omega
    right_inv := by
      intro i
      apply Fin.ext
      simp only
      omega }

@[simp] theorem initial_apply (i : Fin 6) : initial i = i := rfl

@[simp] theorem reversed_apply (i : Fin 6) :
    reversed i = ⟨5 - i.1, by omega⟩ := rfl

end SixRow

/-! ## Cutting and reversing a row -/

/-- Cut a list at the indicated gaps.  The boolean at position `i` says
that the gap after entry `i` is a cut.  In the intended use the data list
has length six and the cut list has length five. -/
def chunksAtCuts {α : Type*} : List Bool → List α → List (List α)
  | [], xs => [xs]
  | _ :: _, [] => [[]]
  | cut :: cuts, x :: xs =>
      if cut then [x] :: chunksAtCuts cuts xs
      else
        match chunksAtCuts cuts xs with
        | [] => [[x]]
        | block :: blocks => (x :: block) :: blocks

/-- Reverse each consecutive block selected by a cut mask. -/
def reverseCutBlocks {α : Type*} (cuts : List Bool) (xs : List α) : List α :=
  (chunksAtCuts cuts xs).flatMap List.reverse

/-- The left endpoint of the cut block containing position `i`. -/
def cutBlockLeft (cuts : Fin 5 → Bool) : ℕ → ℕ
  | 0 => 0
  | i + 1 =>
      if hi : i < 5 then
        if cuts ⟨i, hi⟩ then i + 1 else cutBlockLeft cuts i
      else i + 1

/-- Reverse the five gaps.  This lets the right endpoint reuse the preceding
left-endpoint computation. -/
def reverseCutMask (cuts : Fin 5 → Bool) : Fin 5 → Bool := fun i =>
  cuts ⟨4 - i.1, by omega⟩

/-- The right endpoint of the cut block containing position `i`. -/
def cutBlockRight (cuts : Fin 5 → Bool) (i : Fin 6) : ℕ :=
  5 - cutBlockLeft (reverseCutMask cuts) (5 - i.1)

/-- Mirror a position inside its selected cut block. -/
def reverseCutIndexNat (cuts : Fin 5 → Bool) (i : Fin 6) : ℕ :=
  cutBlockLeft cuts i.1 + cutBlockRight cuts i - i.1

private theorem reverseCutIndexNat_lt :
    ∀ (cuts : Fin 5 → Bool) (i : Fin 6),
      reverseCutIndexNat cuts i < 6 := by
  native_decide

/-- The position permutation which reverses every selected cut block. -/
def reverseCutIndex (cuts : Fin 5 → Bool) (i : Fin 6) : Fin 6 :=
  ⟨reverseCutIndexNat cuts i, reverseCutIndexNat_lt cuts i⟩

private theorem reverseCutIndex_involutive :
    ∀ (cuts : Fin 5 → Bool) (i : Fin 6),
      reverseCutIndex cuts (reverseCutIndex cuts i) = i := by
  native_decide

/-- Reversing cut blocks is an explicit computable permutation.  Using the
same involution as its inverse is important here: the finite endpoint can be
evaluated by `native_decide` without any classical inverse choice. -/
def cutBlockReversal (cuts : Fin 5 → Bool) : SixRow where
  toFun := reverseCutIndex cuts
  invFun := reverseCutIndex cuts
  left_inv := reverseCutIndex_involutive cuts
  right_inv := reverseCutIndex_involutive cuts

/-- The cut mask is allowable for a row when every resulting block is
strictly increasing in the original label order. -/
def CutMaskAllowable (cuts : Fin 5 → Bool) (p : SixRow) : Prop :=
  (chunksAtCuts (List.ofFn cuts) (List.ofFn p)).all
      (fun block => decide (block.Pairwise (· < ·))) = true

instance (cuts : Fin 5 → Bool) (p : SixRow) :
    Decidable (CutMaskAllowable cuts p) := by
  unfold CutMaskAllowable
  infer_instance

/-- A single nontrivial allowable move.  The existential cut mask is a
finite object (there are only 32 masks), so this relation is decidable. -/
def AllowableMove (p q : SixRow) : Prop :=
  ∃ cuts : Fin 5 → Bool,
    CutMaskAllowable cuts p ∧
      q = (cutBlockReversal cuts).trans p ∧ q ≠ p

instance (p q : SixRow) : Decidable (AllowableMove p q) := by
  unfold AllowableMove CutMaskAllowable
  infer_instance

/-- All rows obtainable by one allowable move. -/
def allowableSuccessors (p : SixRow) : Finset SixRow :=
  (Finset.univ.filter fun cuts : Fin 5 → Bool =>
    CutMaskAllowable cuts p ∧ (cutBlockReversal cuts).trans p ≠ p).image
      fun cuts => (cutBlockReversal cuts).trans p

@[simp] theorem mem_allowableSuccessors {p q : SixRow} :
    q ∈ allowableSuccessors p ↔ AllowableMove p q := by
  simp only [allowableSuccessors, Finset.mem_image, Finset.mem_filter,
    Finset.mem_univ, true_and, AllowableMove]
  constructor
  · rintro ⟨cuts, ⟨hallowable, hne⟩, rfl⟩
    exact ⟨cuts, hallowable, rfl, hne⟩
  · rintro ⟨cuts, hallowable, rfl, hne⟩
    exact ⟨cuts, ⟨hallowable, hne⟩, rfl⟩

/-- Apply one pruned successor step to a finite collection of rows. -/
def allowableStep (rows : Finset SixRow) : Finset SixRow :=
  rows.biUnion allowableSuccessors

/-- Rows obtainable from the increasing row after exactly `moves` nontrivial
allowable moves.  Filtering at every stage is the small checked computation;
it avoids enumerating arbitrary sequences of permutations. -/
def allowableReachable : ℕ → Finset SixRow
  | 0 => {SixRow.initial}
  | moves + 1 => allowableStep (allowableReachable moves)

@[simp] theorem mem_allowableReachable_zero {p : SixRow} :
    p ∈ allowableReachable 0 ↔ p = SixRow.initial := by
  simp [allowableReachable]

theorem mem_allowableReachable_succ {moves : ℕ} {q : SixRow} :
    q ∈ allowableReachable (moves + 1) ↔
      ∃ p ∈ allowableReachable moves, AllowableMove p q := by
  simp [allowableReachable, allowableStep]

/-! ## Checked six-label endpoint -/

/-- Starting from a collection of rows, the reversal stays absent for each
of the next `steps` successor layers.  The recursive `let` shares every
computed layer with the following one, so the four-layer check below makes
one pruned pass rather than four independent reachability computations. -/
def AvoidsReversedForNext : ℕ → Finset SixRow → Bool
  | 0, _ => true
  | steps + 1, rows =>
      let next := allowableStep rows
      decide (SixRow.reversed ∉ next) &&
          AvoidsReversedForNext steps next

/-- One shared native computation checks the layers with exactly two, three,
four, and five nontrivial moves. -/
private theorem reversed_absent_next_four_layers_after_one :
    AvoidsReversedForNext 4 (allowableReachable 1) = true := by
  native_decide

/-- Uniform form of the preceding four checked statements. -/
theorem reversed_not_mem_allowableReachable_of_two_le_of_le_five
    {moves : ℕ} (htwo : 2 ≤ moves) (hfive : moves ≤ 5) :
    SixRow.reversed ∉ allowableReachable moves := by
  have hall :
      SixRow.reversed ∉ allowableReachable 2 ∧
        SixRow.reversed ∉ allowableReachable 3 ∧
        SixRow.reversed ∉ allowableReachable 4 ∧
        SixRow.reversed ∉ allowableReachable 5 ∧ True := by
    simpa only [AvoidsReversedForNext, Bool.and_eq_true_iff,
      decide_eq_true_eq, allowableReachable] using
        reversed_absent_next_four_layers_after_one
  rcases hall with
    ⟨h2, h3, h4, h5, _⟩
  interval_cases moves
  · exact h2
  · exact h3
  · exact h4
  · exact h5

end Erdos506.Finite
