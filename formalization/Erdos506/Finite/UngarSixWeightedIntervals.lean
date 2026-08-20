import Mathlib

/-!
# The five-color weighted-interval obstruction for six labels

For six points whose abscissae are strictly increasing, every secant slope
is the positive weighted average of the slopes on the two pieces obtained by
splitting its interval.  Thus its rank is either the common rank of the two
pieces or lies strictly between their different ranks.

The finite consequence needed for Ungar's theorem is a short ordered
arithmetic fact: if the fifteen intervals of a six-term row have only five
ordered ranks and satisfy that betweenness rule at every split, then all
fifteen ranks coincide.  The proof below exposes the twenty split relations
and discharges their Presburger consequence directly; it performs no search
over colorings.
-/

namespace Erdos506.Finite

/-- A rank assignment to the fifteen nonempty intervals with distinct
endpoints in a six-term row. -/
abbrev SixIntervalColoring := Fin 15 → Fin 5

/-- Left endpoints, with intervals ordered first by length and then by their
left endpoint. -/
def sixIntervalLeft : Fin 15 → Fin 6 :=
  ![0, 1, 2, 3, 4, 0, 1, 2, 3, 0, 1, 2, 0, 1, 0]

/-- Right endpoints in the same interval enumeration. -/
def sixIntervalRight : Fin 15 → Fin 6 :=
  ![1, 2, 3, 4, 5, 2, 3, 4, 5, 3, 4, 5, 4, 5, 5]

/-- The table inverse to `sixIntervalLeft, sixIntervalRight` on pairs
`i < j`.  Entries on and below the diagonal are irrelevant and set to zero. -/
def sixIntervalIndex : Fin 6 → Fin 6 → Fin 15 :=
  ![![0, 0, 5, 9, 12, 14],
    ![0, 0, 1, 6, 10, 13],
    ![0, 0, 0, 2, 7, 11],
    ![0, 0, 0, 0, 3, 8],
    ![0, 0, 0, 0, 0, 4],
    ![0, 0, 0, 0, 0, 0]]

theorem sixIntervalLeft_lt_right (e : Fin 15) :
    sixIntervalLeft e < sixIntervalRight e := by
  revert e
  decide

@[simp] theorem sixIntervalIndex_endpoints (e : Fin 15) :
    sixIntervalIndex (sixIntervalLeft e) (sixIntervalRight e) = e := by
  revert e
  decide

theorem sixInterval_endpoints_index {i j : Fin 6} (hij : i < j) :
    sixIntervalLeft (sixIntervalIndex i j) = i ∧
      sixIntervalRight (sixIntervalIndex i j) = j := by
  revert i j
  decide

/-- Every proper subinterval of interval `e` occurs earlier in the table. -/
theorem sixIntervalIndex_subinterval_lt
    (e : Fin 15) (j : Fin 6)
    (hlj : sixIntervalLeft e < j) (hjr : j < sixIntervalRight e) :
    sixIntervalIndex (sixIntervalLeft e) j < e ∧
      sixIntervalIndex j (sixIntervalRight e) < e := by
  revert e j
  decide

/-- Ordered-rank form of the positive weighted-average rule. -/
def BetweenOrEqual (a b c : Fin 5) : Prop :=
  (a = b ∧ c = a) ∨ (a < c ∧ c < b) ∨ (b < c ∧ c < a)

/-- If the endpoints have the same rank, their weighted-average rank has
that rank as well. -/
theorem betweenOrEqual_middle_eq_of_eq {a b c : Fin 5}
    (hab : a = b) (h : BetweenOrEqual a b c) : c = a := by
  rcases h with ⟨_, hca⟩ | ⟨hac, hcb⟩ | ⟨hbc, hca⟩
  · exact hca
  · omega
  · omega

/-- If the endpoint ranks are increasing, the middle rank is strictly
between them. -/
theorem betweenOrEqual_middle_of_lt {a b c : Fin 5}
    (hab : a < b) (h : BetweenOrEqual a b c) : a < c ∧ c < b := by
  rcases h with ⟨hab', _⟩ | h | h
  · omega
  · exact h
  · omega

/-- The decreasing-endpoint version of `betweenOrEqual_middle_of_lt`. -/
theorem betweenOrEqual_middle_of_gt {a b c : Fin 5}
    (hba : b < a) (h : BetweenOrEqual a b c) : b < c ∧ c < a := by
  rcases h with ⟨hab, _⟩ | h | h
  · omega
  · omega
  · exact h

open Lean Elab Tactic Meta in
/-- Remove the still-unsplit disjunctions before asking `omega` whether the
current branch is already impossible.  This is used transactionally below:
when `omega` cannot close the goal, `first` restores the untouched context. -/
elab "clear_unsplit_between" : tactic => withMainContext do
  let mut goal ← getMainGoal
  for localDecl in ← getLCtx do
    if localDecl.type.isAppOfArity ``Or 2 ||
        localDecl.type.isAppOfArity ``BetweenOrEqual 3 then
      goal ← goal.tryClear localDecl.fvarId
  replaceMainGoal [goal]

open Lean.Parser.Tactic in
/-- Split one specialized betweenness relation.  Each resulting linear branch
is tested without recursively feeding all the other disjunctions to `omega`. -/
local macro "split_between_omega " h:elimTarget : tactic =>
  `(tactic|
    all_goals
      rcases $h with
        ⟨hEq, hMid⟩ | ⟨hLower, hUpper⟩ | ⟨hUpper, hLower⟩ <;>
        first
        | (clear_unsplit_between; omega)
        | skip)

/-- The proposed color of a new interval is compatible with all its splits. -/
def NewIntervalAllowed
    (coloring : SixIntervalColoring) (e : Fin 15) (color : Fin 5) : Prop :=
  ∀ j : Fin 6, sixIntervalLeft e < j → j < sixIntervalRight e →
    BetweenOrEqual
      (coloring (sixIntervalIndex (sixIntervalLeft e) j))
      (coloring (sixIntervalIndex j (sixIntervalRight e))) color

private theorem two_eq_zero_branch011
    (coloring : SixIntervalColoring)
    (b05 : coloring 0 = coloring 1 ∧ coloring 5 = coloring 0)
    (b16 : coloring 1 < coloring 6 ∧ coloring 6 < coloring 2)
    (b09 : coloring 5 < coloring 9 ∧ coloring 9 < coloring 2)
    (h09a : BetweenOrEqual (coloring 0) (coloring 6) (coloring 9))
    (h211a : BetweenOrEqual (coloring 2) (coloring 8) (coloring 11))
    (h014c : BetweenOrEqual (coloring 9) (coloring 8) (coloring 14))
    (h113b : BetweenOrEqual (coloring 6) (coloring 8) (coloring 13))
    (h38 : BetweenOrEqual (coloring 3) (coloring 4) (coloring 8))
    (h012c : BetweenOrEqual (coloring 9) (coloring 3) (coloring 12))
    (h014d : BetweenOrEqual (coloring 12) (coloring 4) (coloring 14))
    (h110b : BetweenOrEqual (coloring 6) (coloring 3) (coloring 10))
    (h113c : BetweenOrEqual (coloring 10) (coloring 4) (coloring 13))
    (h27 : BetweenOrEqual (coloring 2) (coloring 3) (coloring 7)) :
    coloring 2 = coloring 0 := by
  rcases b05 with ⟨b05a, b05b⟩
  rcases b16 with ⟨b16a, b16b⟩
  rcases b09 with ⟨b09a, b09b⟩
  split_between_omega h09a
  split_between_omega h211a
  split_between_omega h014c
  split_between_omega h113b
  split_between_omega h38
  split_between_omega h012c
  split_between_omega h014d
  split_between_omega h110b
  split_between_omega h113c
  split_between_omega h27

private theorem two_eq_zero_branch022
    (coloring : SixIntervalColoring)
    (b05 : coloring 0 = coloring 1 ∧ coloring 5 = coloring 0)
    (b16 : coloring 2 < coloring 6 ∧ coloring 6 < coloring 1)
    (b09 : coloring 2 < coloring 9 ∧ coloring 9 < coloring 5)
    (h09a : BetweenOrEqual (coloring 0) (coloring 6) (coloring 9))
    (h211a : BetweenOrEqual (coloring 2) (coloring 8) (coloring 11))
    (h014c : BetweenOrEqual (coloring 9) (coloring 8) (coloring 14))
    (h113b : BetweenOrEqual (coloring 6) (coloring 8) (coloring 13))
    (h38 : BetweenOrEqual (coloring 3) (coloring 4) (coloring 8))
    (h012c : BetweenOrEqual (coloring 9) (coloring 3) (coloring 12))
    (h014d : BetweenOrEqual (coloring 12) (coloring 4) (coloring 14))
    (h110b : BetweenOrEqual (coloring 6) (coloring 3) (coloring 10))
    (h113c : BetweenOrEqual (coloring 10) (coloring 4) (coloring 13))
    (h27 : BetweenOrEqual (coloring 2) (coloring 3) (coloring 7)) :
    coloring 2 = coloring 0 := by
  rcases b05 with ⟨b05a, b05b⟩
  rcases b16 with ⟨b16a, b16b⟩
  rcases b09 with ⟨b09a, b09b⟩
  split_between_omega h09a
  split_between_omega h211a
  split_between_omega h014c
  split_between_omega h113b
  split_between_omega h38
  split_between_omega h012c
  split_between_omega h014d
  split_between_omega h110b
  split_between_omega h113c
  split_between_omega h27

private theorem two_eq_zero_branch101
    (coloring : SixIntervalColoring)
    (b05 : coloring 0 < coloring 5 ∧ coloring 5 < coloring 1)
    (b16 : coloring 1 = coloring 2 ∧ coloring 6 = coloring 1)
    (b09 : coloring 5 < coloring 9 ∧ coloring 9 < coloring 2)
    (h110a : BetweenOrEqual (coloring 1) (coloring 7) (coloring 10))
    (h27 : BetweenOrEqual (coloring 2) (coloring 3) (coloring 7))
    (h012b : BetweenOrEqual (coloring 5) (coloring 7) (coloring 12))
    (h012c : BetweenOrEqual (coloring 9) (coloring 3) (coloring 12))
    (h113a : BetweenOrEqual (coloring 1) (coloring 11) (coloring 13))
    (h211a : BetweenOrEqual (coloring 2) (coloring 8) (coloring 11))
    (h014b : BetweenOrEqual (coloring 5) (coloring 11) (coloring 14))
    (h014c : BetweenOrEqual (coloring 9) (coloring 8) (coloring 14))
    (h38 : BetweenOrEqual (coloring 3) (coloring 4) (coloring 8))
    (h014d : BetweenOrEqual (coloring 12) (coloring 4) (coloring 14))
    (h113c : BetweenOrEqual (coloring 10) (coloring 4) (coloring 13)) :
    coloring 2 = coloring 0 := by
  rcases b05 with ⟨b05a, b05b⟩
  rcases b16 with ⟨b16a, b16b⟩
  rcases b09 with ⟨b09a, b09b⟩
  split_between_omega h110a
  split_between_omega h27
  split_between_omega h012b
  split_between_omega h012c
  split_between_omega h113a
  split_between_omega h211a
  split_between_omega h014b
  split_between_omega h014c
  split_between_omega h38
  split_between_omega h014d
  split_between_omega h113c

private theorem two_eq_zero_branch111
    (coloring : SixIntervalColoring)
    (b05 : coloring 0 < coloring 5 ∧ coloring 5 < coloring 1)
    (b16 : coloring 1 < coloring 6 ∧ coloring 6 < coloring 2)
    (b09 : coloring 5 < coloring 9 ∧ coloring 9 < coloring 2)
    (h014b : BetweenOrEqual (coloring 5) (coloring 11) (coloring 14))
    (h113a : BetweenOrEqual (coloring 1) (coloring 11) (coloring 13))
    (h113b : BetweenOrEqual (coloring 6) (coloring 8) (coloring 13))
    (h211a : BetweenOrEqual (coloring 2) (coloring 8) (coloring 11)) :
    coloring 2 = coloring 0 := by
  rcases b05 with ⟨b05a, b05b⟩
  rcases b16 with ⟨b16a, b16b⟩
  rcases b09 with ⟨b09a, b09b⟩
  split_between_omega h014b
  split_between_omega h113a
  split_between_omega h113b
  split_between_omega h211a

private theorem two_eq_zero_branch120
    (coloring : SixIntervalColoring)
    (b05 : coloring 0 < coloring 5 ∧ coloring 5 < coloring 1)
    (b16 : coloring 2 < coloring 6 ∧ coloring 6 < coloring 1)
    (b09 : coloring 5 = coloring 2 ∧ coloring 9 = coloring 5)
    (h012b : BetweenOrEqual (coloring 5) (coloring 7) (coloring 12))
    (h27 : BetweenOrEqual (coloring 2) (coloring 3) (coloring 7))
    (h110b : BetweenOrEqual (coloring 6) (coloring 3) (coloring 10))
    (h014b : BetweenOrEqual (coloring 5) (coloring 11) (coloring 14))
    (h211a : BetweenOrEqual (coloring 2) (coloring 8) (coloring 11))
    (h113b : BetweenOrEqual (coloring 6) (coloring 8) (coloring 13))
    (h014d : BetweenOrEqual (coloring 12) (coloring 4) (coloring 14))
    (h113c : BetweenOrEqual (coloring 10) (coloring 4) (coloring 13)) :
    coloring 2 = coloring 0 := by
  rcases b05 with ⟨b05a, b05b⟩
  rcases b16 with ⟨b16a, b16b⟩
  rcases b09 with ⟨b09a, b09b⟩
  split_between_omega h012b
  split_between_omega h27
  split_between_omega h110b
  split_between_omega h014b
  split_between_omega h211a
  split_between_omega h113b
  split_between_omega h014d
  split_between_omega h113c

private theorem two_eq_zero_branch122
    (coloring : SixIntervalColoring)
    (b05 : coloring 0 < coloring 5 ∧ coloring 5 < coloring 1)
    (b16 : coloring 2 < coloring 6 ∧ coloring 6 < coloring 1)
    (b09 : coloring 2 < coloring 9 ∧ coloring 9 < coloring 5)
    (h09a : BetweenOrEqual (coloring 0) (coloring 6) (coloring 9))
    (h211a : BetweenOrEqual (coloring 2) (coloring 8) (coloring 11))
    (h113b : BetweenOrEqual (coloring 6) (coloring 8) (coloring 13))
    (h014c : BetweenOrEqual (coloring 9) (coloring 8) (coloring 14))
    (h014a : BetweenOrEqual (coloring 0) (coloring 13) (coloring 14))
    (h27 : BetweenOrEqual (coloring 2) (coloring 3) (coloring 7))
    (h110b : BetweenOrEqual (coloring 6) (coloring 3) (coloring 10))
    (h012a : BetweenOrEqual (coloring 0) (coloring 10) (coloring 12))
    (h014d : BetweenOrEqual (coloring 12) (coloring 4) (coloring 14))
    (h211b : BetweenOrEqual (coloring 7) (coloring 4) (coloring 11))
    (h113c : BetweenOrEqual (coloring 10) (coloring 4) (coloring 13)) :
    coloring 2 = coloring 0 := by
  rcases b05 with ⟨b05a, b05b⟩
  rcases b16 with ⟨b16a, b16b⟩
  rcases b09 with ⟨b09a, b09b⟩
  split_between_omega h09a
  split_between_omega h211a
  split_between_omega h113b
  split_between_omega h014c
  split_between_omega h014a
  split_between_omega h27
  split_between_omega h110b
  split_between_omega h012a
  split_between_omega h014d
  split_between_omega h211b
  split_between_omega h113c

private theorem two_eq_zero_branch202
    (coloring : SixIntervalColoring)
    (b05 : coloring 1 < coloring 5 ∧ coloring 5 < coloring 0)
    (b16 : coloring 1 = coloring 2 ∧ coloring 6 = coloring 1)
    (b09 : coloring 2 < coloring 9 ∧ coloring 9 < coloring 5)
    (h110a : BetweenOrEqual (coloring 1) (coloring 7) (coloring 10))
    (h27 : BetweenOrEqual (coloring 2) (coloring 3) (coloring 7))
    (h012b : BetweenOrEqual (coloring 5) (coloring 7) (coloring 12))
    (h012c : BetweenOrEqual (coloring 9) (coloring 3) (coloring 12))
    (h113a : BetweenOrEqual (coloring 1) (coloring 11) (coloring 13))
    (h211a : BetweenOrEqual (coloring 2) (coloring 8) (coloring 11))
    (h014b : BetweenOrEqual (coloring 5) (coloring 11) (coloring 14))
    (h014c : BetweenOrEqual (coloring 9) (coloring 8) (coloring 14))
    (h38 : BetweenOrEqual (coloring 3) (coloring 4) (coloring 8))
    (h014d : BetweenOrEqual (coloring 12) (coloring 4) (coloring 14))
    (h113c : BetweenOrEqual (coloring 10) (coloring 4) (coloring 13)) :
    coloring 2 = coloring 0 := by
  rcases b05 with ⟨b05a, b05b⟩
  rcases b16 with ⟨b16a, b16b⟩
  rcases b09 with ⟨b09a, b09b⟩
  split_between_omega h110a
  split_between_omega h27
  split_between_omega h012b
  split_between_omega h012c
  split_between_omega h113a
  split_between_omega h211a
  split_between_omega h014b
  split_between_omega h014c
  split_between_omega h38
  split_between_omega h014d
  split_between_omega h113c

private theorem two_eq_zero_branch210
    (coloring : SixIntervalColoring)
    (b05 : coloring 1 < coloring 5 ∧ coloring 5 < coloring 0)
    (b16 : coloring 1 < coloring 6 ∧ coloring 6 < coloring 2)
    (b09 : coloring 5 = coloring 2 ∧ coloring 9 = coloring 5)
    (h012b : BetweenOrEqual (coloring 5) (coloring 7) (coloring 12))
    (h27 : BetweenOrEqual (coloring 2) (coloring 3) (coloring 7))
    (h110b : BetweenOrEqual (coloring 6) (coloring 3) (coloring 10))
    (h014b : BetweenOrEqual (coloring 5) (coloring 11) (coloring 14))
    (h211a : BetweenOrEqual (coloring 2) (coloring 8) (coloring 11))
    (h113b : BetweenOrEqual (coloring 6) (coloring 8) (coloring 13))
    (h014d : BetweenOrEqual (coloring 12) (coloring 4) (coloring 14))
    (h113c : BetweenOrEqual (coloring 10) (coloring 4) (coloring 13)) :
    coloring 2 = coloring 0 := by
  rcases b05 with ⟨b05a, b05b⟩
  rcases b16 with ⟨b16a, b16b⟩
  rcases b09 with ⟨b09a, b09b⟩
  split_between_omega h012b
  split_between_omega h27
  split_between_omega h110b
  split_between_omega h014b
  split_between_omega h211a
  split_between_omega h113b
  split_between_omega h014d
  split_between_omega h113c

private theorem two_eq_zero_branch211
    (coloring : SixIntervalColoring)
    (b05 : coloring 1 < coloring 5 ∧ coloring 5 < coloring 0)
    (b16 : coloring 1 < coloring 6 ∧ coloring 6 < coloring 2)
    (b09 : coloring 5 < coloring 9 ∧ coloring 9 < coloring 2)
    (h09a : BetweenOrEqual (coloring 0) (coloring 6) (coloring 9))
    (h211a : BetweenOrEqual (coloring 2) (coloring 8) (coloring 11))
    (h113b : BetweenOrEqual (coloring 6) (coloring 8) (coloring 13))
    (h014c : BetweenOrEqual (coloring 9) (coloring 8) (coloring 14))
    (h211b : BetweenOrEqual (coloring 7) (coloring 4) (coloring 11))
    (h27 : BetweenOrEqual (coloring 2) (coloring 3) (coloring 7))
    (h38 : BetweenOrEqual (coloring 3) (coloring 4) (coloring 8))
    (h110b : BetweenOrEqual (coloring 6) (coloring 3) (coloring 10))
    (h012a : BetweenOrEqual (coloring 0) (coloring 10) (coloring 12))
    (h014d : BetweenOrEqual (coloring 12) (coloring 4) (coloring 14))
    (h113c : BetweenOrEqual (coloring 10) (coloring 4) (coloring 13)) :
    coloring 2 = coloring 0 := by
  rcases b05 with ⟨b05a, b05b⟩
  rcases b16 with ⟨b16a, b16b⟩
  rcases b09 with ⟨b09a, b09b⟩
  split_between_omega h09a
  split_between_omega h211a
  split_between_omega h113b
  split_between_omega h014c
  split_between_omega h211b
  split_between_omega h27
  split_between_omega h38
  split_between_omega h110b
  split_between_omega h012a
  split_between_omega h014d
  split_between_omega h113c

private theorem two_eq_zero_branch222
    (coloring : SixIntervalColoring)
    (b05 : coloring 1 < coloring 5 ∧ coloring 5 < coloring 0)
    (b16 : coloring 2 < coloring 6 ∧ coloring 6 < coloring 1)
    (b09 : coloring 2 < coloring 9 ∧ coloring 9 < coloring 5)
    (h012b : BetweenOrEqual (coloring 5) (coloring 7) (coloring 12))
    (h110a : BetweenOrEqual (coloring 1) (coloring 7) (coloring 10))
    (h110b : BetweenOrEqual (coloring 6) (coloring 3) (coloring 10))
    (h27 : BetweenOrEqual (coloring 2) (coloring 3) (coloring 7)) :
    coloring 2 = coloring 0 := by
  rcases b05 with ⟨b05a, b05b⟩
  rcases b16 with ⟨b16a, b16b⟩
  rcases b09 with ⟨b09a, b09b⟩
  split_between_omega h012b
  split_between_omega h110a
  split_between_omega h110b
  split_between_omega h27

/-- Dispatch the twenty-seven endpoint-order cases separately from the main
coloring theorem, so this finite split gets its own heartbeat budget. -/
private theorem two_eq_zero_of_specialized_relations
    (coloring : SixIntervalColoring)
    (h05 : BetweenOrEqual (coloring 0) (coloring 1) (coloring 5))
    (h16 : BetweenOrEqual (coloring 1) (coloring 2) (coloring 6))
    (h27 : BetweenOrEqual (coloring 2) (coloring 3) (coloring 7))
    (h38 : BetweenOrEqual (coloring 3) (coloring 4) (coloring 8))
    (h09a : BetweenOrEqual (coloring 0) (coloring 6) (coloring 9))
    (h09b : BetweenOrEqual (coloring 5) (coloring 2) (coloring 9))
    (h110a : BetweenOrEqual (coloring 1) (coloring 7) (coloring 10))
    (h110b : BetweenOrEqual (coloring 6) (coloring 3) (coloring 10))
    (h211a : BetweenOrEqual (coloring 2) (coloring 8) (coloring 11))
    (h211b : BetweenOrEqual (coloring 7) (coloring 4) (coloring 11))
    (h012a : BetweenOrEqual (coloring 0) (coloring 10) (coloring 12))
    (h012b : BetweenOrEqual (coloring 5) (coloring 7) (coloring 12))
    (h012c : BetweenOrEqual (coloring 9) (coloring 3) (coloring 12))
    (h113a : BetweenOrEqual (coloring 1) (coloring 11) (coloring 13))
    (h113b : BetweenOrEqual (coloring 6) (coloring 8) (coloring 13))
    (h113c : BetweenOrEqual (coloring 10) (coloring 4) (coloring 13))
    (h014a : BetweenOrEqual (coloring 0) (coloring 13) (coloring 14))
    (h014b : BetweenOrEqual (coloring 5) (coloring 11) (coloring 14))
    (h014c : BetweenOrEqual (coloring 9) (coloring 8) (coloring 14))
    (h014d : BetweenOrEqual (coloring 12) (coloring 4) (coloring 14)) :
    coloring 2 = coloring 0 := by
  rcases h05 with h05 | h05 | h05 <;>
    rcases h16 with h16 | h16 | h16 <;>
      rcases h09b with h09b | h09b | h09b
  all_goals
    first
    | (clear_unsplit_between; omega)
    | exact two_eq_zero_branch011 coloring h05 h16 h09b h09a h211a h014c
        h113b h38 h012c h014d h110b h113c h27
    | exact two_eq_zero_branch022 coloring h05 h16 h09b h09a h211a h014c
        h113b h38 h012c h014d h110b h113c h27
    | exact two_eq_zero_branch101 coloring h05 h16 h09b h110a h27 h012b
        h012c h113a h211a h014b h014c h38 h014d h113c
    | exact two_eq_zero_branch111 coloring h05 h16 h09b h014b h113a h113b h211a
    | exact two_eq_zero_branch120 coloring h05 h16 h09b h012b h27 h110b h014b
        h211a h113b h014d h113c
    | exact two_eq_zero_branch122 coloring h05 h16 h09b h09a h211a h113b
        h014c h014a h27 h110b h012a h014d h211b h113c
    | exact two_eq_zero_branch202 coloring h05 h16 h09b h110a h27 h012b
        h012c h113a h211a h014b h014c h38 h014d h113c
    | exact two_eq_zero_branch210 coloring h05 h16 h09b h012b h27 h110b h014b
        h211a h113b h014d h113c
    | exact two_eq_zero_branch211 coloring h05 h16 h09b h09a h211a h113b
        h014c h211b h27 h38 h110b h012a h014d h113c
    | exact two_eq_zero_branch222 coloring h05 h16 h09b h012b h110a h110b h27

/-- Five ordered ranks cannot support a nonconstant compatible coloring of
the fifteen intervals of a six-term row. -/
theorem sixIntervalColoring_constant
    (coloring : SixIntervalColoring)
    (hallowed : ∀ e, NewIntervalAllowed coloring e (coloring e)) :
    ∀ e, coloring e = coloring 0 := by
  have h05 := hallowed 5 1 (by decide) (by decide)
  have h16 := hallowed 6 2 (by decide) (by decide)
  have h27 := hallowed 7 3 (by decide) (by decide)
  have h38 := hallowed 8 4 (by decide) (by decide)
  have h09a := hallowed 9 1 (by decide) (by decide)
  have h09b := hallowed 9 2 (by decide) (by decide)
  have h110a := hallowed 10 2 (by decide) (by decide)
  have h110b := hallowed 10 3 (by decide) (by decide)
  have h211a := hallowed 11 3 (by decide) (by decide)
  have h211b := hallowed 11 4 (by decide) (by decide)
  have h012a := hallowed 12 1 (by decide) (by decide)
  have h012b := hallowed 12 2 (by decide) (by decide)
  have h012c := hallowed 12 3 (by decide) (by decide)
  have h113a := hallowed 13 2 (by decide) (by decide)
  have h113b := hallowed 13 3 (by decide) (by decide)
  have h113c := hallowed 13 4 (by decide) (by decide)
  have h014a := hallowed 14 1 (by decide) (by decide)
  have h014b := hallowed 14 2 (by decide) (by decide)
  have h014c := hallowed 14 3 (by decide) (by decide)
  have h014d := hallowed 14 4 (by decide) (by decide)
  simp [sixIntervalLeft, sixIntervalRight, sixIntervalIndex,
    BetweenOrEqual] at h05 h16 h27 h38 h09a h09b h110a h110b h211a h211b
  simp [sixIntervalLeft, sixIntervalRight, sixIntervalIndex,
    BetweenOrEqual] at h012a h012b h012c h113a h113b h113c
  simp [sixIntervalLeft, sixIntervalRight, sixIntervalIndex,
    BetweenOrEqual] at h014a h014b h014c h014d
  have h2 : coloring 2 = coloring 0 :=
    two_eq_zero_of_specialized_relations coloring h05 h16 h27 h38 h09a h09b
      h110a h110b h211a h211b h012a h012b h012c h113a h113b h113c
      h014a h014b h014c h014d
  have h3 : coloring 3 = coloring 0 := by
    clear h16 h38 h09a h110b h211a h012b h113a h113b h014a h014c hallowed
    have branchInc
        (b27 : coloring 2 < coloring 7 ∧ coloring 7 < coloring 3) :
        coloring 3 = coloring 0 := by
      rcases b27 with ⟨b27a, b27b⟩
      split_between_omega h05
      split_between_omega h09b
      split_between_omega h110a
      split_between_omega h012a
      split_between_omega h012c
      split_between_omega h211b
      split_between_omega h014d
      split_between_omega h113c
      split_between_omega h014b
    have branchDec
        (b27 : coloring 3 < coloring 7 ∧ coloring 7 < coloring 2) :
        coloring 3 = coloring 0 := by
      rcases b27 with ⟨b27a, b27b⟩
      split_between_omega h05
      split_between_omega h09b
      split_between_omega h110a
      split_between_omega h012a
      split_between_omega h012c
      split_between_omega h211b
      split_between_omega h014d
      split_between_omega h113c
      split_between_omega h014b
    rcases h27 with h27 | h27 | h27
    · clear_unsplit_between
      omega
    · exact branchInc h27
    · exact branchDec h27
  have h1 : coloring 1 = coloring 0 := by
    clear h05 h27 h09b h110a h110b h211a h211b h012a h012b h113a h113c
      h014a h014b hallowed
    have branchInc
        (b16 : coloring 1 < coloring 6 ∧ coloring 6 < coloring 2) :
        coloring 1 = coloring 0 := by
      rcases b16 with ⟨b16a, b16b⟩
      split_between_omega h09a
      split_between_omega h012c
      split_between_omega h38
      split_between_omega h014d
      split_between_omega h014c
      split_between_omega h113b
    have branchDec
        (b16 : coloring 2 < coloring 6 ∧ coloring 6 < coloring 1) :
        coloring 1 = coloring 0 := by
      rcases b16 with ⟨b16a, b16b⟩
      split_between_omega h09a
      split_between_omega h012c
      split_between_omega h38
      split_between_omega h014d
      split_between_omega h014c
      split_between_omega h113b
    rcases h16 with h16 | h16 | h16
    · clear_unsplit_between
      omega
    · exact branchInc h16
    · exact branchDec h16
  have h5 : coloring 5 = coloring 0 :=
    betweenOrEqual_middle_eq_of_eq h1.symm h05
  have h6 : coloring 6 = coloring 0 :=
    (betweenOrEqual_middle_eq_of_eq (h1.trans h2.symm) h16).trans h1
  have h7 : coloring 7 = coloring 0 :=
    (betweenOrEqual_middle_eq_of_eq (h2.trans h3.symm) h27).trans h2
  have h9 : coloring 9 = coloring 0 :=
    betweenOrEqual_middle_eq_of_eq h6.symm h09a
  have h10 : coloring 10 = coloring 0 :=
    (betweenOrEqual_middle_eq_of_eq (h6.trans h3.symm) h110b).trans h6
  have h12 : coloring 12 = coloring 0 :=
    betweenOrEqual_middle_eq_of_eq h10.symm h012a
  have h4 : coloring 4 = coloring 0 := by
    clear h05 h16 h27 h09a h09b h110a h110b h211b h012a h012b h012c
      h113b h113c h014b h014c h014d hallowed
    split_between_omega h38
    split_between_omega h211a
    split_between_omega h113a
    split_between_omega h014a
  have h8 : coloring 8 = coloring 0 :=
    (betweenOrEqual_middle_eq_of_eq (h3.trans h4.symm) h38).trans h3
  have h11 : coloring 11 = coloring 0 :=
    (betweenOrEqual_middle_eq_of_eq (h2.trans h8.symm) h211a).trans h2
  have h13 : coloring 13 = coloring 0 :=
    (betweenOrEqual_middle_eq_of_eq (h1.trans h11.symm) h113a).trans h1
  have h14 : coloring 14 = coloring 0 :=
    betweenOrEqual_middle_eq_of_eq h13.symm h014a
  intro e
  fin_cases e <;> simp_all

end Erdos506.Finite
