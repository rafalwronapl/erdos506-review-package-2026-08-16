import Erdos506.V1.Carrier
import Erdos506.V3.PivotGeometry
import Erdos506.Block.SignedRows
import Erdos506.Incidence.MelchiorPrinciple

/-!
# The V1 pivot-inversion block dictionary

Unlike V3, V1 allows collinear triples.  Under inversion at a selected
pivot, a generalized block through the pivot becomes a line in two ways:
a circle becomes its perpendicular-bisector line, while an original line
through the pivot is preserved by inversion.  This file combines both cases.
-/

namespace Erdos506.V1

open Erdos506.Block
open Erdos506.Finite
open Erdos506.Incidence
open Erdos506.V3
open Erdos506.V4

/-- Labels away from `p` whose original labels lie in `T`. -/
noncomputable def awaySupport
    {α : Type*} [Fintype α] (p : α) (T : Finset α) :
    Finset (AwayFrom p) := by
  classical
  exact Finset.univ.filter fun q => q.1 ∈ T

@[simp] theorem mem_awaySupport
    {α : Type*} [Fintype α] {p : α} {T : Finset α} {q : AwayFrom p} :
    q ∈ awaySupport p T ↔ q.1 ∈ T := by
  classical
  simp [awaySupport]

noncomputable def awaySupportEquivErase
    {α : Type*} [Fintype α] [DecidableEq α]
    (p : α) (T : Finset α) :
    ↥(awaySupport p T) ≃ ↥(T.erase p) where
  toFun q := ⟨q.1.1, Finset.mem_erase.mpr ⟨q.1.2, mem_awaySupport.mp q.2⟩⟩
  invFun x :=
    ⟨⟨x.1, (Finset.mem_erase.mp x.2).1⟩,
      mem_awaySupport.mpr (Finset.mem_erase.mp x.2).2⟩
  left_inv q := by ext; rfl
  right_inv x := by ext; rfl

theorem card_awaySupport
    {α : Type*} [Fintype α] [DecidableEq α]
    (p : α) (T : Finset α) (hp : p ∈ T) :
    (awaySupport p T).card = T.card - 1 := by
  calc
    (awaySupport p T).card = Fintype.card ↥(awaySupport p T) :=
      (Fintype.card_coe _).symm
    _ = Fintype.card ↥(T.erase p) :=
      Fintype.card_congr (awaySupportEquivErase p T)
    _ = (T.erase p).card := Fintype.card_coe _
    _ = T.card - 1 := Finset.card_erase_of_mem hp

/-- A V1 generalized block through `p` with at least three selected labels. -/
abbrev PivotBlock
    {α : Type*} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (p : α) :=
  {b : GeometricBlock cfg //
    p ∈ geometricBlockSupport cfg b ∧
      3 ≤ (geometricBlockSupport cfg b).card}

/-- Inversion at a point of an affine line preserves that line. -/
theorem pivotInversion_mem_line_iff
    {α : Type*} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (p : α) (L : DeterminedLine cfg)
    (hp : p ∈ lineSupport cfg L) (q : AwayFrom p) :
    pivotInversion cfg p q ∈ L.1 ↔ q.1 ∈ lineSupport cfg L := by
  rw [mem_lineSupport]
  have hcenter : cfg p ∈ L.1 := mem_lineSupport.mp hp
  constructor
  · intro hq
    have hback := EuclideanGeometry.mapsTo_inversion_affineSubspace_of_mem
      (R := (1 : ℝ)) hcenter hq
    simpa [pivotInversion] using hback
  · intro hq
    exact EuclideanGeometry.mapsTo_inversion_affineSubspace_of_mem
      (R := (1 : ℝ)) hcenter hq

/-- A full original line block of size at least three through the pivot is a
determined line of the inverted configuration. -/
theorem originalLine_mem_pivotDeterminedLines
    {α : Type*} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (p : α) (L : DeterminedLine cfg)
    (hp : p ∈ lineSupport cfg L)
    (hcard : 3 ≤ (lineSupport cfg L).card) :
    L.1 ∈ determinedLines (pivotInversion cfg p) := by
  classical
  have haway : 2 ≤ (awaySupport p (lineSupport cfg L)).card := by
    rw [card_awaySupport p (lineSupport cfg L) hp]
    omega
  obtain ⟨Aset, hAsub, hAcard⟩ := Finset.exists_subset_card_eq haway
  let A : KSubset (AwayFrom p) 2 := ⟨Aset, hAcard⟩
  have hmem : ∀ q ∈ A.1, pivotInversion cfg p q ∈ L.1 := by
    intro q hq
    exact (pivotInversion_mem_line_iff cfg p L hp q).2
      (mem_awaySupport.mp (hAsub hq))
  have hline : lineOfPair (pivotInversion cfg p) A = L.1 :=
    lineOfPair_eq_of_mem_of_direction_finrank_one
      (pivotInversion cfg p) A L.1 hmem L.direction_finrank
  rw [← hline]
  exact lineOfPair_mem_determinedLines (pivotInversion cfg p) A

/-- The inverted line carried by a V1 generalized block through the pivot. -/
noncomputable def blockToPivotLine
    {α : Type*} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (p : α) (b : PivotBlock cfg p) :
    DeterminedLine (pivotInversion cfg p) := by
  rcases b with ⟨b, hp, hcard⟩
  cases b with
  | inl L =>
      exact ⟨L.1, originalLine_mem_pivotDeterminedLines cfg p L hp hcard⟩
  | inr c =>
      exact ⟨circlePivotLine cfg p c.1,
        circlePivotLine_mem_determinedLines cfg p c hp⟩

/-- The support of the inverted line is exactly the original generalized
block support with the pivot removed. -/
theorem lineSupport_blockToPivotLine
    {α : Type*} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (p : α) (b : PivotBlock cfg p) :
    lineSupport (pivotInversion cfg p) (blockToPivotLine cfg p b) =
      awaySupport p (geometricBlockSupport cfg b.1) := by
  rcases b with ⟨b, hp, hcard⟩
  cases b with
  | inl L =>
      ext q
      rw [mem_lineSupport, mem_awaySupport]
      exact pivotInversion_mem_line_iff cfg p L hp q
  | inr c =>
      ext q
      rw [mem_lineSupport, mem_awaySupport]
      exact pivotInversion_mem_circlePivotLine_iff cfg p c.1 hp q

theorem card_lineSupport_blockToPivotLine
    {α : Type*} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (p : α) (b : PivotBlock cfg p) :
    (lineSupport (pivotInversion cfg p) (blockToPivotLine cfg p b)).card =
      (geometricBlockSupport cfg b.1).card - 1 := by
  rw [lineSupport_blockToPivotLine]
  exact card_awaySupport p (geometricBlockSupport cfg b.1) b.2.1

theorem blockToPivotLine_injective
    {α : Type*} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (p : α) :
    Function.Injective (blockToPivotLine cfg p) := by
  classical
  intro b c hline
  have haway :
      awaySupport p (geometricBlockSupport cfg b.1) =
        awaySupport p (geometricBlockSupport cfg c.1) := by
    rw [← lineSupport_blockToPivotLine cfg p b,
      ← lineSupport_blockToPivotLine cfg p c, hline]
  have hsupp :
      geometricBlockSupport cfg b.1 = geometricBlockSupport cfg c.1 := by
    ext x
    by_cases hxp : x = p
    · subst x
      exact iff_of_true b.2.1 c.2.1
    · let q : AwayFrom p := ⟨x, hxp⟩
      constructor
      · intro hx
        have hq : q ∈ awaySupport p (geometricBlockSupport cfg b.1) :=
          mem_awaySupport.mpr hx
        rw [haway] at hq
        exact mem_awaySupport.mp hq
      · intro hx
        have hq : q ∈ awaySupport p (geometricBlockSupport cfg c.1) :=
          mem_awaySupport.mpr hx
        rw [← haway] at hq
        exact mem_awaySupport.mp hq
  obtain ⟨Aset, hAsub, hAcard⟩ :=
    Finset.exists_subset_card_eq b.2.2
  let A : KSubset α 3 := ⟨Aset, hAcard⟩
  have hbOwner : b.1 = geometricTripleOwner cfg A :=
    geometricTripleOwner_unique cfg A b.1 hAsub
  have hcOwner : c.1 = geometricTripleOwner cfg A :=
    geometricTripleOwner_unique cfg A c.1 (by
      intro x hx
      rw [← hsupp]
      exact hAsub hx)
  apply Subtype.ext
  exact hbOwner.trans hcOwner.symm

theorem blockToPivotLine_surjective
    {α : Type*} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (p : α) :
    Function.Surjective (blockToPivotLine cfg p) := by
  classical
  intro L
  obtain ⟨A, hAline⟩ := L.exists_pair
  obtain ⟨a, b, hab, hAeq⟩ := Finset.card_eq_two.mp A.2
  have hab' : a.1 ≠ b.1 := by
    intro h
    exact hab (Subtype.ext h)
  let Tset : Finset α := {p, a.1, b.1}
  have hTcard : Tset.card = 3 := by
    apply Finset.card_eq_three.mpr
    exact ⟨p, a.1, b.1, a.2.symm, b.2.symm, hab', rfl⟩
  let T : KSubset α 3 := ⟨Tset, hTcard⟩
  let owner : GeometricBlock cfg := geometricTripleOwner cfg T
  have hTsub : T.1 ⊆ geometricBlockSupport cfg owner :=
    geometricTripleOwner_contains cfg T
  have hpOwner : p ∈ geometricBlockSupport cfg owner :=
    hTsub (by simp [T, Tset])
  have hownerCard : 3 ≤ (geometricBlockSupport cfg owner).card := by
    rw [← hTcard]
    exact Finset.card_le_card hTsub
  let pb : PivotBlock cfg p := ⟨owner, hpOwner, hownerCard⟩
  refine ⟨pb, ?_⟩
  have hmem : ∀ q ∈ A.1,
      pivotInversion cfg p q ∈ (blockToPivotLine cfg p pb).1 := by
    intro q hq
    have hqab : q = a ∨ q = b := by
      rw [hAeq] at hq
      simpa using hq
    have hqT : q.1 ∈ T.1 := by
      rcases hqab with rfl | rfl <;> simp [T, Tset]
    have hqOwner : q.1 ∈ geometricBlockSupport cfg owner := hTsub hqT
    have hqAway : q ∈ awaySupport p (geometricBlockSupport cfg pb.1) :=
      mem_awaySupport.mpr hqOwner
    rw [← lineSupport_blockToPivotLine cfg p pb] at hqAway
    exact mem_lineSupport.mp hqAway
  have hpairMap :
      lineOfPair (pivotInversion cfg p) A = (blockToPivotLine cfg p pb).1 :=
    lineOfPair_eq_of_mem_of_direction_finrank_one
      (pivotInversion cfg p) A (blockToPivotLine cfg p pb).1 hmem
      (blockToPivotLine cfg p pb).direction_finrank
  apply Subtype.ext
  exact hpairMap.symm.trans hAline

/-- Exact finite equivalence between V1 generalized blocks through the pivot
and lines spanned after inversion. -/
noncomputable def blockPivotLineEquiv
    {α : Type*} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (p : α) :
    PivotBlock cfg p ≃ DeterminedLine (pivotInversion cfg p) :=
  Equiv.ofBijective (blockToPivotLine cfg p)
    ⟨blockToPivotLine_injective cfg p,
      blockToPivotLine_surjective cfg p⟩

theorem pivotWeight_blockToPivotLine
    {α : Type*} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (p : α) (b : PivotBlock cfg p) :
    (3 - ((lineSupport (pivotInversion cfg p)
      (blockToPivotLine cfg p b)).card : ℤ)) =
      4 - ((geometricBlockSupport cfg b.1).card : ℤ) := by
  have hcard := card_lineSupport_blockToPivotLine cfg p b
  omega

/-- Melchior for the line arrangement after inversion proves nonnegativity
of the exact V1 local pivot expression. -/
theorem pivotSigma_nonneg_of_lineMelchior
    {α : Type*} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (p : α)
    (hmel : LineMelchior (pivotInversion cfg p)) :
    0 ≤ (geometricBlockSystem cfg).pivotSigma p := by
  unfold LineMelchior at hmel
  have hsum :
      (∑ b : PivotBlock cfg p,
          (4 - ((geometricBlockSupport cfg b.1).card : ℤ))) =
        ∑ L : DeterminedLine (pivotInversion cfg p),
          (3 - ((lineSupport (pivotInversion cfg p) L).card : ℤ)) := by
    apply Fintype.sum_equiv (blockPivotLineEquiv cfg p)
    intro b
    exact (pivotWeight_blockToPivotLine cfg p b).symm
  rw [(geometricBlockSystem cfg).pivotSigma_eq_sum_nontrivialBlockAt_sub_three]
  change 0 ≤
    (∑ b : PivotBlock cfg p,
      (4 - ((geometricBlockSupport cfg b.1).card : ℤ))) - 3
  rw [hsum]
  omega

/-- V1 admissibility guarantees that the inverted configuration at every
pivot is noncollinear.  If all inverted points lay on one line, the unique
V1 block owned by the pivot and two points on that line would contain the
entire original configuration, hence would be either a forbidden global
line or a forbidden global circle. -/
theorem pivotInversion_noncollinear
    {α : Type*} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (hadm : Admissible cfg)
    (hcard : 3 ≤ Fintype.card α) (p : α) :
    Noncollinear (pivotInversion cfg p) := by
  classical
  intro hcol
  have hAway : 1 < Fintype.card (AwayFrom p) := by
    rw [card_awayFrom]
    omega
  obtain ⟨a, b, hab⟩ := Fintype.exists_pair_of_one_lt_card hAway
  have hab' : a.1 ≠ b.1 := by
    intro h
    exact hab (Subtype.ext h)
  let A : KSubset (AwayFrom p) 2 := ⟨{a, b}, by simp [hab]⟩
  let Tset : Finset α := {p, a.1, b.1}
  have hTcard : Tset.card = 3 := by
    apply Finset.card_eq_three.mpr
    exact ⟨p, a.1, b.1, a.2.symm, b.2.symm, hab', rfl⟩
  let T : KSubset α 3 := ⟨Tset, hTcard⟩
  let owner : GeometricBlock cfg := geometricTripleOwner cfg T
  have hTsub : T.1 ⊆ geometricBlockSupport cfg owner :=
    geometricTripleOwner_contains cfg T
  have hpOwner : p ∈ geometricBlockSupport cfg owner :=
    hTsub (by simp [T, Tset])
  have hownerCard : 3 ≤ (geometricBlockSupport cfg owner).card := by
    rw [← hTcard]
    exact Finset.card_le_card hTsub
  let pb : PivotBlock cfg p := ⟨owner, hpOwner, hownerCard⟩
  have haOwner : a.1 ∈ geometricBlockSupport cfg owner :=
    hTsub (by simp [T, Tset])
  have hbOwner : b.1 ∈ geometricBlockSupport cfg owner :=
    hTsub (by simp [T, Tset])
  have haMap : pivotInversion cfg p a ∈ (blockToPivotLine cfg p pb).1 := by
    apply mem_lineSupport.mp
    rw [lineSupport_blockToPivotLine cfg p pb]
    exact mem_awaySupport.mpr haOwner
  have hbMap : pivotInversion cfg p b ∈ (blockToPivotLine cfg p pb).1 := by
    apply mem_lineSupport.mp
    rw [lineSupport_blockToPivotLine cfg p pb]
    exact mem_awaySupport.mpr hbOwner
  have hpairMap :
      lineOfPair (pivotInversion cfg p) A = (blockToPivotLine cfg p pb).1 :=
    lineOfPair_eq_of_mem_of_direction_finrank_one
      (pivotInversion cfg p) A (blockToPivotLine cfg p pb).1
      (by
        intro q hq
        have hqab : q = a ∨ q = b := by simpa [A] using hq
        rcases hqab with rfl | rfl
        · exact haMap
        · exact hbMap)
      (blockToPivotLine cfg p pb).direction_finrank
  have hpairExplicit :
      lineOfPair (pivotInversion cfg p) A =
        affineSpan ℝ
          ({pivotInversion cfg p a, pivotInversion cfg p b} : Set Point2) := by
    simpa [A] using lineOfPair_pair (pivotInversion cfg p) hab
  have hmapSpan :
      (blockToPivotLine cfg p pb).1 =
        affineSpan ℝ
          ({pivotInversion cfg p a, pivotInversion cfg p b} : Set Point2) :=
    hpairMap.symm.trans hpairExplicit
  have haRange : pivotInversion cfg p a ∈ pointSet (pivotInversion cfg p) :=
    ⟨a, rfl⟩
  have hbRange : pivotInversion cfg p b ∈ pointSet (pivotInversion cfg p) :=
    ⟨b, rfl⟩
  have habInv : pivotInversion cfg p a ≠ pivotInversion cfg p b :=
    (pivotInversion cfg p).injective.ne hab
  have hall : ∀ x : α, x ∈ geometricBlockSupport cfg owner := by
    intro x
    by_cases hxp : x = p
    · simpa [hxp] using hpOwner
    · let q : AwayFrom p := ⟨x, hxp⟩
      have hqRange : pivotInversion cfg p q ∈ pointSet (pivotInversion cfg p) :=
        ⟨q, rfl⟩
      have hqSpan :
          pivotInversion cfg p q ∈
            affineSpan ℝ
              ({pivotInversion cfg p a, pivotInversion cfg p b} : Set Point2) :=
        hcol.mem_affineSpan_of_mem_of_ne haRange hbRange hqRange habInv
      have hqMap : pivotInversion cfg p q ∈ (blockToPivotLine cfg p pb).1 := by
        rw [hmapSpan]
        exact hqSpan
      have hqLineSupport :
          q ∈ lineSupport (pivotInversion cfg p) (blockToPivotLine cfg p pb) :=
        mem_lineSupport.mpr hqMap
      rw [lineSupport_blockToPivotLine cfg p pb] at hqLineSupport
      exact mem_awaySupport.mp hqLineSupport
  cases howner : owner with
  | inl L =>
      have hallLine : ∀ x : α, x ∈ lineSupport cfg L := by
        intro x
        simpa [howner, geometricBlockSupport] using hall x
      have hsubset : pointSet cfg ⊆ (L.1 : Set Point2) := by
        rintro y ⟨x, rfl⟩
        exact mem_lineSupport.mp (hallLine x)
      have hLcol : Collinear ℝ (L.1 : Set Point2) := by
        rw [collinear_iff_finrank_le_one,
          ← AffineSubspace.direction_eq_vectorSpan]
        rw [L.direction_finrank]
      exact hadm.1 (hLcol.subset hsubset)
  | inr c =>
      have hallCircle : ∀ x : α, x ∈ circleTrace cfg c.1 := by
        intro x
        simpa [howner, geometricBlockSupport] using hall x
      have htrace : circleTrace cfg c.1 = Finset.univ :=
        Finset.eq_univ_of_forall hallCircle
      have hcNot := hadm.2 c.1
      rw [htrace] at hcNot
      simp at hcNot

end Erdos506.V1
