import Erdos506.V1.Deletion
import Erdos506.V1.DirectKelly

/-!
# Exact line census after deleting one label

This file supplies the line analogue of the circle-deletion bridge in
`Deletion`.  A line of the deleted configuration is the same affine line as
an original determined line having at least two labels away from the deleted
point.  Restricting that equivalence to the two- and three-point layers gives

`t₂' = t₂ - e₂(p) + e₃(p)`

and, under a three-point line cap,

`t₃' = t₃ - e₃(p)`.

The statements are deliberately independent of Melchior and of any endpoint
circle-count hypothesis.
-/

namespace Erdos506.V1

open Erdos506.Block
open Erdos506.Block.BlockSystem
open Erdos506.Finite
open Erdos506.Incidence
open Erdos506.V3
open Erdos506.V4

universe u

/-! ## The surviving-line equivalence -/

/-- Lift a two-subset of `AwayFrom p` to the original label type. -/
noncomputable def liftAwayPair
    {alpha : Type u} [Fintype alpha] [DecidableEq alpha]
    {p : alpha} (A : KSubset (AwayFrom p) 2) : KSubset alpha 2 :=
  ⟨liftAwayFinset A.1, by
    rw [card_liftAwayFinset]
    exact A.2⟩

/-- Taking the affine span of an away-pair commutes with forgetting its
subtype proofs. -/
theorem lineOfPair_deletePointConfiguration
    {alpha : Type u} [Fintype alpha] [DecidableEq alpha]
    (cfg : Configuration alpha) (p : alpha)
    (A : KSubset (AwayFrom p) 2) :
    lineOfPair (deletePointConfiguration cfg p) A =
      lineOfPair cfg (liftAwayPair A) := by
  classical
  unfold lineOfPair
  congr 1
  ext z
  constructor
  · rintro ⟨q, hq, rfl⟩
    exact ⟨q.1, mem_liftAwayFinset.mpr ⟨q, hq, rfl⟩, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨q, hq, rfl⟩ := mem_liftAwayFinset.mp hx
    exact ⟨q, hq, rfl⟩

/-- A determined line after deletion, regarded as the same affine line in
the original configuration. -/
noncomputable def deletionLineToOriginal
    {alpha : Type u} [Fintype alpha] [DecidableEq alpha]
    (cfg : Configuration alpha) (p : alpha)
    (L : DeterminedLine (deletePointConfiguration cfg p)) :
    DeterminedLine cfg := by
  let A : KSubset (AwayFrom p) 2 := Classical.choose L.exists_pair
  have hA : lineOfPair (deletePointConfiguration cfg p) A = L.1 :=
    Classical.choose_spec L.exists_pair
  refine ⟨L.1, ?_⟩
  rw [← hA, lineOfPair_deletePointConfiguration]
  exact lineOfPair_mem_determinedLines cfg (liftAwayPair A)

@[simp] theorem deletionLineToOriginal_val
    {alpha : Type u} [Fintype alpha] [DecidableEq alpha]
    (cfg : Configuration alpha) (p : alpha)
    (L : DeterminedLine (deletePointConfiguration cfg p)) :
    (deletionLineToOriginal cfg p L).1 = L.1 := by
  unfold deletionLineToOriginal
  rfl

/-- The support of a deleted line is the away-support of its original line. -/
theorem lineSupport_deletionLineToOriginal
    {alpha : Type u} [Fintype alpha] [DecidableEq alpha]
    (cfg : Configuration alpha) (p : alpha)
    (L : DeterminedLine (deletePointConfiguration cfg p)) :
    lineSupport (deletePointConfiguration cfg p) L =
      awaySupport p (lineSupport cfg (deletionLineToOriginal cfg p L)) := by
  ext q
  simp only [mem_lineSupport, mem_awaySupport,
    deletePointConfiguration_apply, deletionLineToOriginal_val]

/-- An original line with two labels away from `p` remains determined after
deletion. -/
noncomputable def originalLineToDeletion
    {alpha : Type u} [Fintype alpha] [DecidableEq alpha]
    (cfg : Configuration alpha) (p : alpha) (L : DeterminedLine cfg)
    (haway : 2 ≤ (awaySupport p (lineSupport cfg L)).card) :
    DeterminedLine (deletePointConfiguration cfg p) := by
  classical
  let hexists := Finset.exists_subset_card_eq haway
  let Aset : Finset (AwayFrom p) := Classical.choose hexists
  have hAspec := Classical.choose_spec hexists
  have hAsub : Aset ⊆ awaySupport p (lineSupport cfg L) := hAspec.1
  have hAcard : Aset.card = 2 := hAspec.2
  let A : KSubset (AwayFrom p) 2 := ⟨Aset, hAcard⟩
  have hmem : ∀ q ∈ A.1,
      deletePointConfiguration cfg p q ∈ L.1 := by
    intro q hq
    have hqSupport : q.1 ∈ lineSupport cfg L :=
      mem_awaySupport.mp (hAsub hq)
    simpa using (mem_lineSupport.mp hqSupport)
  have hline :
      lineOfPair (deletePointConfiguration cfg p) A = L.1 :=
    lineOfPair_eq_of_mem_of_direction_finrank_one
      (deletePointConfiguration cfg p) A L.1 hmem L.direction_finrank
  refine ⟨L.1, ?_⟩
  rw [← hline]
  exact lineOfPair_mem_determinedLines
    (deletePointConfiguration cfg p) A

@[simp] theorem originalLineToDeletion_val
    {alpha : Type u} [Fintype alpha] [DecidableEq alpha]
    (cfg : Configuration alpha) (p : alpha) (L : DeterminedLine cfg)
    (haway : 2 ≤ (awaySupport p (lineSupport cfg L)).card) :
    (originalLineToDeletion cfg p L haway).1 = L.1 := by
  unfold originalLineToDeletion
  rfl

theorem lineSupport_originalLineToDeletion
    {alpha : Type u} [Fintype alpha] [DecidableEq alpha]
    (cfg : Configuration alpha) (p : alpha) (L : DeterminedLine cfg)
    (haway : 2 ≤ (awaySupport p (lineSupport cfg L)).card) :
    lineSupport (deletePointConfiguration cfg p)
        (originalLineToDeletion cfg p L haway) =
      awaySupport p (lineSupport cfg L) := by
  ext q
  simp only [mem_lineSupport, mem_awaySupport,
    deletePointConfiguration_apply, originalLineToDeletion_val]

/-- The two line transports preserve the underlying affine line in the
deletion-to-original-to-deletion direction. -/
@[simp] theorem originalLineToDeletion_deletionLineToOriginal_val
    {alpha : Type u} [Fintype alpha] [DecidableEq alpha]
    (cfg : Configuration alpha) (p : alpha)
    (L : DeterminedLine (deletePointConfiguration cfg p))
    (haway : 2 ≤
      (awaySupport p
        (lineSupport cfg (deletionLineToOriginal cfg p L))).card) :
    (originalLineToDeletion cfg p
      (deletionLineToOriginal cfg p L) haway).1 = L.1 := by
  rw [originalLineToDeletion_val, deletionLineToOriginal_val]

/-- The two line transports preserve the underlying affine line in the
original-to-deletion-to-original direction. -/
@[simp] theorem deletionLineToOriginal_originalLineToDeletion_val
    {alpha : Type u} [Fintype alpha] [DecidableEq alpha]
    (cfg : Configuration alpha) (p : alpha) (L : DeterminedLine cfg)
    (haway : 2 ≤ (awaySupport p (lineSupport cfg L)).card) :
    (deletionLineToOriginal cfg p
      (originalLineToDeletion cfg p L haway)).1 = L.1 := by
  rw [deletionLineToOriginal_val, originalLineToDeletion_val]

/-- Transporting an original surviving line to the deletion and back does
not change its original support. -/
@[simp] theorem lineSupport_deletionLineToOriginal_originalLineToDeletion
    {alpha : Type u} [Fintype alpha] [DecidableEq alpha]
    (cfg : Configuration alpha) (p : alpha) (L : DeterminedLine cfg)
    (haway : 2 ≤ (awaySupport p (lineSupport cfg L)).card) :
    lineSupport cfg
        (deletionLineToOriginal cfg p
          (originalLineToDeletion cfg p L haway)) =
      lineSupport cfg L := by
  ext q
  simp only [mem_lineSupport,
    deletionLineToOriginal_originalLineToDeletion_val]

/-- Transporting a deleted line to the original configuration and back does
not change its deleted support. -/
@[simp] theorem lineSupport_originalLineToDeletion_deletionLineToOriginal
    {alpha : Type u} [Fintype alpha] [DecidableEq alpha]
    (cfg : Configuration alpha) (p : alpha)
    (L : DeterminedLine (deletePointConfiguration cfg p))
    (haway : 2 ≤
      (awaySupport p
        (lineSupport cfg (deletionLineToOriginal cfg p L))).card) :
    lineSupport (deletePointConfiguration cfg p)
        (originalLineToDeletion cfg p
          (deletionLineToOriginal cfg p L) haway) =
      lineSupport (deletePointConfiguration cfg p) L := by
  ext q
  simp only [mem_lineSupport, deletePointConfiguration_apply,
    originalLineToDeletion_deletionLineToOriginal_val]

/-- Original lines which survive deletion. -/
abbrev DeletionSurvivingLine
    {alpha : Type u} [Fintype alpha] [DecidableEq alpha]
    (cfg : Configuration alpha) (p : alpha) :=
  {L : DeterminedLine cfg //
    2 ≤ (awaySupport p (lineSupport cfg L)).card}

/-- Determined lines after deletion are exactly the surviving original
determined lines. -/
noncomputable def deletionLineEquivSurvivingLine
    {alpha : Type u} [Fintype alpha] [DecidableEq alpha]
    (cfg : Configuration alpha) (p : alpha) :
    DeterminedLine (deletePointConfiguration cfg p) ≃
      DeletionSurvivingLine cfg p where
  toFun L := ⟨deletionLineToOriginal cfg p L, by
    have hmin := two_le_lineSupport_card
      (deletePointConfiguration cfg p) L
    rw [lineSupport_deletionLineToOriginal] at hmin
    exact hmin⟩
  invFun L := originalLineToDeletion cfg p L.1 L.2
  left_inv L := by
    apply Subtype.ext
    exact originalLineToDeletion_deletionLineToOriginal_val cfg p L _
  right_inv L := by
    apply Subtype.ext
    apply Subtype.ext
    exact deletionLineToOriginal_originalLineToDeletion_val cfg p L.1 L.2

/-! ## Size and incidence subtypes -/

theorem card_awaySupport_of_not_mem
    {alpha : Type u} [Fintype alpha] [DecidableEq alpha]
    (p : alpha) (T : Finset alpha) (hp : p ∉ T) :
    (awaySupport p T).card = T.card := by
  calc
    (awaySupport p T).card = Fintype.card ↥(awaySupport p T) :=
      (Fintype.card_coe _).symm
    _ = Fintype.card ↥(T.erase p) :=
      Fintype.card_congr (awaySupportEquivErase p T)
    _ = (T.erase p).card := Fintype.card_coe _
    _ = T.card := by rw [Finset.erase_eq_of_notMem hp]

theorem card_awaySupport_le
    {alpha : Type u} [Fintype alpha] [DecidableEq alpha]
    (p : alpha) (T : Finset alpha) :
    (awaySupport p T).card ≤ T.card := by
  by_cases hp : p ∈ T
  · rw [card_awaySupport p T hp]
    omega
  · rw [card_awaySupport_of_not_mem p T hp]

/-- Size-`s` lines through a fixed label. -/
abbrev DeterminedLineOfSizeThrough
    {alpha : Type u} [Fintype alpha] [DecidableEq alpha]
    (cfg : Configuration alpha) (p : alpha) (s : Nat) :=
  {L : DeterminedLineOfSize cfg s // p ∈ lineSupport cfg L.1}

/-- Size-`s` lines avoiding a fixed label. -/
abbrev DeterminedLineOfSizeAway
    {alpha : Type u} [Fintype alpha] [DecidableEq alpha]
    (cfg : Configuration alpha) (p : alpha) (s : Nat) :=
  {L : DeterminedLineOfSize cfg s // p ∉ lineSupport cfg L.1}

/-- The block-system line degree is the concrete cardinality of the
corresponding determined-line subtype. -/
noncomputable def taggedLineAtSizeEquivDeterminedLineOfSizeThrough
    {alpha : Type u} [Fintype alpha] [DecidableEq alpha]
    (cfg : Configuration alpha) (p : alpha) (s : Nat) :
    TaggedLineAtSize cfg p s ≃
      DeterminedLineOfSizeThrough cfg p s where
  toFun b := by
    rcases b with ⟨b, hbkind, hbsize, hbp⟩
    cases b with
    | inl L => exact ⟨⟨L, hbsize⟩, hbp⟩
    | inr c => cases hbkind
  invFun L := ⟨.inl L.1.1, rfl, L.1.2, L.2⟩
  left_inv b := by
    rcases b with ⟨b, hbkind, hbsize, hbp⟩
    cases b with
    | inl L => rfl
    | inr c => cases hbkind
  right_inv L := rfl

theorem lineDegree_eq_card_determinedLineOfSizeThrough
    {alpha : Type u} [Fintype alpha] [DecidableEq alpha]
    (cfg : Configuration alpha) (p : alpha) (s : Nat) :
    (blockSystem cfg).lineDegree s p =
      Fintype.card (DeterminedLineOfSizeThrough cfg p s) := by
  rw [lineDegree_eq_card_taggedLineAtSize]
  exact Fintype.card_congr
    (taggedLineAtSizeEquivDeterminedLineOfSizeThrough cfg p s)

/-- Split a fixed line-size layer according to incidence with `p`. -/
noncomputable def determinedLineOfSizeEquivThroughOrAway
    {alpha : Type u} [Fintype alpha] [DecidableEq alpha]
    (cfg : Configuration alpha) (p : alpha) (s : Nat) :
    DeterminedLineOfSize cfg s ≃
      DeterminedLineOfSizeThrough cfg p s ⊕
        DeterminedLineOfSizeAway cfg p s where
  toFun L := if hp : p ∈ lineSupport cfg L.1 then
      .inl ⟨L, hp⟩
    else .inr ⟨L, hp⟩
  invFun
    | .inl L => L.1
    | .inr L => L.1
  left_inv L := by
    by_cases hp : p ∈ lineSupport cfg L.1
    · simp only [dif_pos hp]
    · simp only [dif_neg hp]
  right_inv L := by
    cases L with
    | inl L => simp [L.2]
    | inr L => simp [L.2]

theorem lineCount_eq_lineDegree_add_card_away
    {alpha : Type u} [Fintype alpha] [DecidableEq alpha]
    (cfg : Configuration alpha) (p : alpha) (s : Nat) :
    (blockSystem cfg).lineCount s =
      (blockSystem cfg).lineDegree s p +
        Fintype.card (DeterminedLineOfSizeAway cfg p s) := by
  rw [lineCount_eq_card_determinedLineOfSize,
    Fintype.card_congr (determinedLineOfSizeEquivThroughOrAway cfg p s),
    Fintype.card_sum,
    ← lineDegree_eq_card_determinedLineOfSizeThrough]

/-! ## The exact two- and three-line deletion census -/

/-- Classify a deleted ordinary line by whether its original carrier avoids
the deleted label or contains it. -/
noncomputable def deletionLineOfSizeTwoTo
    {alpha : Type u} [Fintype alpha] [DecidableEq alpha]
    (cfg : Configuration alpha) (p : alpha)
    (L : DeterminedLineOfSize (deletePointConfiguration cfg p) 2) :
    DeterminedLineOfSizeAway cfg p 2 ⊕
      DeterminedLineOfSizeThrough cfg p 3 := by
  let O := deletionLineToOriginal cfg p L.1
  have haway : (awaySupport p (lineSupport cfg O)).card = 2 := by
    rw [← lineSupport_deletionLineToOriginal cfg p L.1]
    exact L.2
  by_cases hp : p ∈ lineSupport cfg O
  · have hcard := card_awaySupport p (lineSupport cfg O) hp
    have hmin := two_le_lineSupport_card cfg O
    refine .inr ⟨⟨O, ?_⟩, hp⟩
    omega
  · have hcard := card_awaySupport_of_not_mem
      p (lineSupport cfg O) hp
    refine .inl ⟨⟨O, ?_⟩, hp⟩
    omega

/-- Restore an original ordinary line avoiding the deleted label. -/
theorem two_le_awaySupport_of_sizeTwoAway
    {alpha : Type u} [Fintype alpha] [DecidableEq alpha]
    (cfg : Configuration alpha) (p : alpha)
    (L : DeterminedLineOfSizeAway cfg p 2) :
    2 ≤ (awaySupport p (lineSupport cfg L.1.1)).card := by
  have hcard := card_awaySupport_of_not_mem p
    (lineSupport cfg L.1.1) L.2
  have hsize := L.1.2
  omega

noncomputable def deletionLineOfSizeTwoFromAway
    {alpha : Type u} [Fintype alpha] [DecidableEq alpha]
    (cfg : Configuration alpha) (p : alpha)
    (L : DeterminedLineOfSizeAway cfg p 2) :
    DeterminedLineOfSize (deletePointConfiguration cfg p) 2 :=
  ⟨originalLineToDeletion cfg p L.1.1
      (two_le_awaySupport_of_sizeTwoAway cfg p L), by
    rw [lineSupport_originalLineToDeletion,
      card_awaySupport_of_not_mem p (lineSupport cfg L.1.1) L.2,
      L.1.2]⟩

@[simp] theorem deletionLineOfSizeTwoFromAway_val
    {alpha : Type u} [Fintype alpha] [DecidableEq alpha]
    (cfg : Configuration alpha) (p : alpha)
    (L : DeterminedLineOfSizeAway cfg p 2) :
    (deletionLineOfSizeTwoFromAway cfg p L).1.1 = L.1.1.1 := by
  change
    (originalLineToDeletion cfg p L.1.1
      (two_le_awaySupport_of_sizeTwoAway cfg p L)).1 = L.1.1.1
  exact originalLineToDeletion_val cfg p L.1.1
    (two_le_awaySupport_of_sizeTwoAway cfg p L)

@[simp] theorem deletionLineToOriginal_deletionLineOfSizeTwoFromAway_val
    {alpha : Type u} [Fintype alpha] [DecidableEq alpha]
    (cfg : Configuration alpha) (p : alpha)
    (L : DeterminedLineOfSizeAway cfg p 2) :
    (deletionLineToOriginal cfg p
      (deletionLineOfSizeTwoFromAway cfg p L).1).1 = L.1.1.1 := by
  rw [deletionLineToOriginal_val, deletionLineOfSizeTwoFromAway_val]

@[simp] theorem lineSupport_deletionLineToOriginal_deletionLineOfSizeTwoFromAway
    {alpha : Type u} [Fintype alpha] [DecidableEq alpha]
    (cfg : Configuration alpha) (p : alpha)
    (L : DeterminedLineOfSizeAway cfg p 2) :
    lineSupport cfg
        (deletionLineToOriginal cfg p
          (deletionLineOfSizeTwoFromAway cfg p L).1) =
      lineSupport cfg L.1.1 := by
  ext q
  simp only [mem_lineSupport,
    deletionLineToOriginal_deletionLineOfSizeTwoFromAway_val]

/-- Restore an original three-line through the deleted label. -/
theorem two_le_awaySupport_of_sizeThreeThrough
    {alpha : Type u} [Fintype alpha] [DecidableEq alpha]
    (cfg : Configuration alpha) (p : alpha)
    (L : DeterminedLineOfSizeThrough cfg p 3) :
    2 ≤ (awaySupport p (lineSupport cfg L.1.1)).card := by
  have hcard := card_awaySupport p (lineSupport cfg L.1.1) L.2
  have hsize := L.1.2
  omega

noncomputable def deletionLineOfSizeTwoFromThrough
    {alpha : Type u} [Fintype alpha] [DecidableEq alpha]
    (cfg : Configuration alpha) (p : alpha)
    (L : DeterminedLineOfSizeThrough cfg p 3) :
    DeterminedLineOfSize (deletePointConfiguration cfg p) 2 :=
  ⟨originalLineToDeletion cfg p L.1.1
      (two_le_awaySupport_of_sizeThreeThrough cfg p L), by
    rw [lineSupport_originalLineToDeletion,
      card_awaySupport p (lineSupport cfg L.1.1) L.2, L.1.2]⟩

@[simp] theorem deletionLineOfSizeTwoFromThrough_val
    {alpha : Type u} [Fintype alpha] [DecidableEq alpha]
    (cfg : Configuration alpha) (p : alpha)
    (L : DeterminedLineOfSizeThrough cfg p 3) :
    (deletionLineOfSizeTwoFromThrough cfg p L).1.1 = L.1.1.1 := by
  change
    (originalLineToDeletion cfg p L.1.1
      (two_le_awaySupport_of_sizeThreeThrough cfg p L)).1 = L.1.1.1
  exact originalLineToDeletion_val cfg p L.1.1
    (two_le_awaySupport_of_sizeThreeThrough cfg p L)

@[simp] theorem deletionLineToOriginal_deletionLineOfSizeTwoFromThrough_val
    {alpha : Type u} [Fintype alpha] [DecidableEq alpha]
    (cfg : Configuration alpha) (p : alpha)
    (L : DeterminedLineOfSizeThrough cfg p 3) :
    (deletionLineToOriginal cfg p
      (deletionLineOfSizeTwoFromThrough cfg p L).1).1 = L.1.1.1 := by
  rw [deletionLineToOriginal_val, deletionLineOfSizeTwoFromThrough_val]

@[simp] theorem lineSupport_deletionLineToOriginal_deletionLineOfSizeTwoFromThrough
    {alpha : Type u} [Fintype alpha] [DecidableEq alpha]
    (cfg : Configuration alpha) (p : alpha)
    (L : DeterminedLineOfSizeThrough cfg p 3) :
    lineSupport cfg
        (deletionLineToOriginal cfg p
          (deletionLineOfSizeTwoFromThrough cfg p L).1) =
      lineSupport cfg L.1.1 := by
  ext q
  simp only [mem_lineSupport,
    deletionLineToOriginal_deletionLineOfSizeTwoFromThrough_val]

/-- Restore either source of a deleted ordinary line. -/
noncomputable def deletionLineOfSizeTwoFrom
    {alpha : Type u} [Fintype alpha] [DecidableEq alpha]
    (cfg : Configuration alpha) (p : alpha)
    (L : DeterminedLineOfSizeAway cfg p 2 ⊕
      DeterminedLineOfSizeThrough cfg p 3) :
    DeterminedLineOfSize (deletePointConfiguration cfg p) 2 :=
  Sum.elim (deletionLineOfSizeTwoFromAway cfg p)
    (deletionLineOfSizeTwoFromThrough cfg p) L

/-- Deleted ordinary lines are precisely original ordinary lines avoiding
`p`, together with original three-lines through `p`. -/
noncomputable def deletionLineOfSizeTwoEquiv
    {alpha : Type u} [Fintype alpha] [DecidableEq alpha]
    (cfg : Configuration alpha) (p : alpha) :
    DeterminedLineOfSize (deletePointConfiguration cfg p) 2 ≃
      DeterminedLineOfSizeAway cfg p 2 ⊕
        DeterminedLineOfSizeThrough cfg p 3 where
  toFun := deletionLineOfSizeTwoTo cfg p
  invFun := deletionLineOfSizeTwoFrom cfg p
  left_inv L := by
    apply Subtype.ext
    apply Subtype.ext
    change
      (deletionLineOfSizeTwoFrom cfg p
        (deletionLineOfSizeTwoTo cfg p L)).1.1 = L.1.1
    unfold deletionLineOfSizeTwoTo
    by_cases hp :
        p ∈ lineSupport cfg (deletionLineToOriginal cfg p L.1)
    · rw [dif_pos hp]
      unfold deletionLineOfSizeTwoFrom
      dsimp only [Sum.elim]
      rw [deletionLineOfSizeTwoFromThrough_val,
        deletionLineToOriginal_val]
    · rw [dif_neg hp]
      unfold deletionLineOfSizeTwoFrom
      dsimp only [Sum.elim]
      rw [deletionLineOfSizeTwoFromAway_val,
        deletionLineToOriginal_val]
  right_inv L := by
    cases L with
    | inl L =>
        have hp : p ∉ lineSupport cfg
            (deletionLineToOriginal cfg p
              (deletionLineOfSizeTwoFromAway cfg p L).1) := by
          rw [lineSupport_deletionLineToOriginal_deletionLineOfSizeTwoFromAway]
          exact L.2
        change deletionLineOfSizeTwoTo cfg p
          (deletionLineOfSizeTwoFromAway cfg p L) = Sum.inl L
        unfold deletionLineOfSizeTwoTo
        simp only [dif_neg hp]
        apply congrArg Sum.inl
        apply Subtype.ext
        apply Subtype.ext
        apply Subtype.ext
        exact deletionLineToOriginal_deletionLineOfSizeTwoFromAway_val
          cfg p L
    | inr L =>
        have hp : p ∈ lineSupport cfg
            (deletionLineToOriginal cfg p
              (deletionLineOfSizeTwoFromThrough cfg p L).1) := by
          rw [lineSupport_deletionLineToOriginal_deletionLineOfSizeTwoFromThrough]
          exact L.2
        change deletionLineOfSizeTwoTo cfg p
          (deletionLineOfSizeTwoFromThrough cfg p L) = Sum.inr L
        unfold deletionLineOfSizeTwoTo
        simp only [dif_pos hp]
        apply congrArg Sum.inr
        apply Subtype.ext
        apply Subtype.ext
        apply Subtype.ext
        exact deletionLineToOriginal_deletionLineOfSizeTwoFromThrough_val
          cfg p L

/-- Send a deleted three-line to its original carrier.  Under the cap the
carrier cannot contain the deleted label. -/
noncomputable def deletionLineOfSizeThreeTo
    {alpha : Type u} [Fintype alpha] [DecidableEq alpha]
    (cfg : Configuration alpha) (p : alpha)
    (hcap : ∀ L : DeterminedLine cfg, (lineSupport cfg L).card ≤ 3)
    (L : DeterminedLineOfSize (deletePointConfiguration cfg p) 3) :
    DeterminedLineOfSizeAway cfg p 3 := by
  let O := deletionLineToOriginal cfg p L.1
  have haway : (awaySupport p (lineSupport cfg O)).card = 3 := by
    rw [← lineSupport_deletionLineToOriginal cfg p L.1]
    exact L.2
  have hp : p ∉ lineSupport cfg O := by
    intro hp
    have hcard := card_awaySupport p (lineSupport cfg O) hp
    have hupper := hcap O
    omega
  have hcard := card_awaySupport_of_not_mem
    p (lineSupport cfg O) hp
  exact ⟨⟨O, by omega⟩, hp⟩

@[simp] theorem deletionLineOfSizeThreeTo_val
    {alpha : Type u} [Fintype alpha] [DecidableEq alpha]
    (cfg : Configuration alpha) (p : alpha)
    (hcap : ∀ L : DeterminedLine cfg, (lineSupport cfg L).card ≤ 3)
    (L : DeterminedLineOfSize (deletePointConfiguration cfg p) 3) :
    (deletionLineOfSizeThreeTo cfg p hcap L).1.1.1 =
      (deletionLineToOriginal cfg p L.1).1 := by
  unfold deletionLineOfSizeThreeTo
  rfl

/-- Restore an original three-line avoiding the deleted label. -/
theorem two_le_awaySupport_of_sizeThreeAway
    {alpha : Type u} [Fintype alpha] [DecidableEq alpha]
    (cfg : Configuration alpha) (p : alpha)
    (L : DeterminedLineOfSizeAway cfg p 3) :
    2 ≤ (awaySupport p (lineSupport cfg L.1.1)).card := by
  have hcard := card_awaySupport_of_not_mem p
    (lineSupport cfg L.1.1) L.2
  have hsize := L.1.2
  omega

noncomputable def deletionLineOfSizeThreeFrom
    {alpha : Type u} [Fintype alpha] [DecidableEq alpha]
    (cfg : Configuration alpha) (p : alpha)
    (L : DeterminedLineOfSizeAway cfg p 3) :
    DeterminedLineOfSize (deletePointConfiguration cfg p) 3 :=
  ⟨originalLineToDeletion cfg p L.1.1
      (two_le_awaySupport_of_sizeThreeAway cfg p L), by
    rw [lineSupport_originalLineToDeletion,
      card_awaySupport_of_not_mem p (lineSupport cfg L.1.1) L.2,
      L.1.2]⟩

@[simp] theorem deletionLineOfSizeThreeFrom_val
    {alpha : Type u} [Fintype alpha] [DecidableEq alpha]
    (cfg : Configuration alpha) (p : alpha)
    (L : DeterminedLineOfSizeAway cfg p 3) :
    (deletionLineOfSizeThreeFrom cfg p L).1.1 = L.1.1.1 := by
  change
    (originalLineToDeletion cfg p L.1.1
      (two_le_awaySupport_of_sizeThreeAway cfg p L)).1 = L.1.1.1
  exact originalLineToDeletion_val cfg p L.1.1
    (two_le_awaySupport_of_sizeThreeAway cfg p L)

@[simp] theorem deletionLineToOriginal_deletionLineOfSizeThreeFrom_val
    {alpha : Type u} [Fintype alpha] [DecidableEq alpha]
    (cfg : Configuration alpha) (p : alpha)
    (L : DeterminedLineOfSizeAway cfg p 3) :
    (deletionLineToOriginal cfg p
      (deletionLineOfSizeThreeFrom cfg p L).1).1 = L.1.1.1 := by
  rw [deletionLineToOriginal_val, deletionLineOfSizeThreeFrom_val]

/-- Under a three-point line cap, deleted three-lines are precisely original
three-lines avoiding the deleted label. -/
noncomputable def deletionLineOfSizeThreeEquiv
    {alpha : Type u} [Fintype alpha] [DecidableEq alpha]
    (cfg : Configuration alpha) (p : alpha)
    (hcap : ∀ L : DeterminedLine cfg, (lineSupport cfg L).card ≤ 3) :
    DeterminedLineOfSize (deletePointConfiguration cfg p) 3 ≃
      DeterminedLineOfSizeAway cfg p 3 where
  toFun := deletionLineOfSizeThreeTo cfg p hcap
  invFun := deletionLineOfSizeThreeFrom cfg p
  left_inv L := by
    apply Subtype.ext
    apply Subtype.ext
    change
      (deletionLineOfSizeThreeFrom cfg p
        (deletionLineOfSizeThreeTo cfg p hcap L)).1.1 = L.1.1
    rw [deletionLineOfSizeThreeFrom_val,
      deletionLineOfSizeThreeTo_val, deletionLineToOriginal_val]
  right_inv L := by
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    change
      (deletionLineOfSizeThreeTo cfg p hcap
        (deletionLineOfSizeThreeFrom cfg p L)).1.1.1 = L.1.1.1
    rw [deletionLineOfSizeThreeTo_val,
      deletionLineToOriginal_deletionLineOfSizeThreeFrom_val]

/-- Exact ordinary-line deletion census. -/
theorem lineCount_two_deletePointConfiguration
    {alpha : Type u} [Fintype alpha] [DecidableEq alpha]
    (cfg : Configuration alpha) (p : alpha) :
    (blockSystem (deletePointConfiguration cfg p)).lineCount 2 =
      (blockSystem cfg).lineCount 2 -
        (blockSystem cfg).lineDegree 2 p +
          (blockSystem cfg).lineDegree 3 p := by
  have hdeleted :
      (blockSystem (deletePointConfiguration cfg p)).lineCount 2 =
        Fintype.card (DeterminedLineOfSizeAway cfg p 2) +
          Fintype.card (DeterminedLineOfSizeThrough cfg p 3) := by
    rw [lineCount_eq_card_determinedLineOfSize,
      Fintype.card_congr (deletionLineOfSizeTwoEquiv cfg p),
      Fintype.card_sum]
  have hsplit := lineCount_eq_lineDegree_add_card_away cfg p 2
  have hthrough :=
    lineDegree_eq_card_determinedLineOfSizeThrough cfg p 3
  omega

/-- Exact three-line deletion census under a three-point line cap. -/
theorem lineCount_three_deletePointConfiguration_of_line_cap_three
    {alpha : Type u} [Fintype alpha] [DecidableEq alpha]
    (cfg : Configuration alpha) (p : alpha)
    (hcap : ∀ L : DeterminedLine cfg, (lineSupport cfg L).card ≤ 3) :
    (blockSystem (deletePointConfiguration cfg p)).lineCount 3 =
      (blockSystem cfg).lineCount 3 -
        (blockSystem cfg).lineDegree 3 p := by
  have hdeleted :
      (blockSystem (deletePointConfiguration cfg p)).lineCount 3 =
        Fintype.card (DeterminedLineOfSizeAway cfg p 3) := by
    rw [lineCount_eq_card_determinedLineOfSize,
      Fintype.card_congr (deletionLineOfSizeThreeEquiv cfg p hcap)]
  have hsplit := lineCount_eq_lineDegree_add_card_away cfg p 3
  omega

/-- A three-point line cap is inherited by deletion. -/
theorem line_cap_three_deletePointConfiguration
    {alpha : Type u} [Fintype alpha] [DecidableEq alpha]
    (cfg : Configuration alpha) (p : alpha)
    (hcap : ∀ L : DeterminedLine cfg, (lineSupport cfg L).card ≤ 3) :
    ∀ L : DeterminedLine (deletePointConfiguration cfg p),
      (lineSupport (deletePointConfiguration cfg p) L).card ≤ 3 := by
  intro L
  rw [lineSupport_deletionLineToOriginal]
  exact (card_awaySupport_le p
    (lineSupport cfg (deletionLineToOriginal cfg p L))).trans
      (hcap (deletionLineToOriginal cfg p L))

end Erdos506.V1
