import Erdos506.Incidence.SpannedLines
import Erdos506.V3.InversionLine
import Erdos506.V3.PivotSum

/-!
# The geometric dictionary at one inversion pivot

Fix a selected point `p`, remove its label, and invert every remaining point
about `cfg p`.  This module proves the exact support dictionary from a circle
through `p` to the corresponding affine line after inversion.
-/

namespace Erdos506.V3

open Erdos506.Finite
open Erdos506.Incidence
open Erdos506.V4
open AffineSubspace
open scoped EuclideanSpace

/-- Labels different from the inversion pivot. -/
abbrev AwayFrom {α : Type*} (p : α) := {q : α // q ≠ p}

/-- The labelled configuration obtained by deleting `p` and applying unit
inversion about `cfg p`. -/
noncomputable def pivotInversion {α : Type*} [Fintype α]
    (cfg : Configuration α) (p : α) : Configuration (AwayFrom p) where
  toFun q := EuclideanGeometry.inversion (cfg p) 1 (cfg q.1)
  inj' := by
    intro q r hqr
    apply Subtype.ext
    apply cfg.injective
    exact EuclideanGeometry.inversion_injective (cfg p) one_ne_zero hqr

@[simp] theorem card_awayFrom {α : Type*} [Fintype α] [DecidableEq α]
    (p : α) : Fintype.card (AwayFrom p) = Fintype.card α - 1 := by
  simp [AwayFrom, Fintype.card_subtype_compl (fun q : α => q = p)]

/-- Labels on `c` other than the pivot, represented in `AwayFrom p`. -/
noncomputable def awayCircleSupport {α : Type*} [Fintype α]
    (cfg : Configuration α) (p : α) (c : ProperCircle) :
    Finset (AwayFrom p) := by
  classical
  exact Finset.univ.filter fun q => q.1 ∈ circleTrace cfg c

@[simp] theorem mem_awayCircleSupport {α : Type*} [Fintype α]
    {cfg : Configuration α} {p : α} {c : ProperCircle} {q : AwayFrom p} :
    q ∈ awayCircleSupport cfg p c ↔ q.1 ∈ circleTrace cfg c := by
  classical
  simp [awayCircleSupport]

/-- The support away from `p` is canonically equivalent to erasing `p` from
the original circle trace. -/
noncomputable def awayCircleSupportEquivErase
    {α : Type*} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (p : α) (c : ProperCircle) :
    ↥(awayCircleSupport cfg p c) ≃ ↥((circleTrace cfg c).erase p) where
  toFun q :=
    ⟨q.1.1, Finset.mem_erase.mpr ⟨q.1.2, mem_awayCircleSupport.mp q.2⟩⟩
  invFun x :=
    ⟨⟨x.1, (Finset.mem_erase.mp x.2).1⟩,
      mem_awayCircleSupport.mpr (Finset.mem_erase.mp x.2).2⟩
  left_inv q := by ext; rfl
  right_inv x := by ext; rfl

theorem card_awayCircleSupport {α : Type*} [Fintype α]
    [DecidableEq α] (cfg : Configuration α) (p : α) (c : ProperCircle)
    (hp : p ∈ circleTrace cfg c) :
    (awayCircleSupport cfg p c).card = (circleTrace cfg c).card - 1 := by
  calc
    (awayCircleSupport cfg p c).card =
        Fintype.card ↥(awayCircleSupport cfg p c) :=
      (Fintype.card_coe _).symm
    _ = Fintype.card ↥((circleTrace cfg c).erase p) :=
      Fintype.card_congr (awayCircleSupportEquivErase cfg p c)
    _ = ((circleTrace cfg c).erase p).card := Fintype.card_coe _
    _ = (circleTrace cfg c).card - 1 := Finset.card_erase_of_mem hp

/-- The affine hyperplane corresponding to a proper circle through `p`. -/
noncomputable def circlePivotLine {α : Type*} [Fintype α]
    (cfg : Configuration α) (p : α) (c : ProperCircle) :
    AffineSubspace ℝ Point2 :=
  perpBisector (cfg p)
    (EuclideanGeometry.inversion (cfg p) 1 c.1.center)

theorem pivot_ne_inverted_circle_center {α : Type*} [Fintype α]
    (cfg : Configuration α) (p : α) (c : ProperCircle)
    (hp : p ∈ circleTrace cfg c) :
    cfg p ≠ EuclideanGeometry.inversion (cfg p) 1 c.1.center := by
  have hcenter : c.1.center ≠ cfg p :=
    properCircle_center_ne_of_mem (cfg p) c (mem_circleTrace.mp hp)
  intro h
  have : c.1.center = cfg p :=
    (EuclideanGeometry.center_eq_inversion one_ne_zero).mp h
  exact hcenter this

theorem circlePivotLine_direction_finrank {α : Type*} [Fintype α]
    (cfg : Configuration α) (p : α) (c : ProperCircle)
    (hp : p ∈ circleTrace cfg c) :
    Module.finrank ℝ (circlePivotLine cfg p c).direction = 1 := by
  rw [circlePivotLine, direction_perpBisector]
  exact Submodule.finrank_orthogonal_span_singleton
    (sub_ne_zero.mpr (pivot_ne_inverted_circle_center cfg p c hp).symm)

/-- Exact pointwise circle-line dictionary away from the pivot. -/
theorem pivotInversion_mem_circlePivotLine_iff
    {α : Type*} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (p : α) (c : ProperCircle)
    (hp : p ∈ circleTrace cfg c) (q : AwayFrom p) :
    pivotInversion cfg p q ∈ circlePivotLine cfg p c ↔
      q.1 ∈ circleTrace cfg c := by
  have hqp : cfg q.1 ≠ cfg p := cfg.injective.ne q.2
  change
    EuclideanGeometry.inversion (cfg p) 1 (cfg q.1) ∈
        perpBisector (cfg p)
          (EuclideanGeometry.inversion (cfg p) 1 c.1.center) ↔
      q.1 ∈ circleTrace cfg c
  rw [mem_circleTrace]
  exact (mem_circle_through_center_iff_inversion_mem_perpBisector
    (cfg p) (cfg q.1) c hqp (mem_circleTrace.mp hp)).symm

theorem circlePivotLine_mem_determinedLines
    {α : Type*} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (p : α) (c : DeterminedCircle cfg)
    (hp : p ∈ circleTrace cfg c.1) :
    circlePivotLine cfg p c.1 ∈ determinedLines (pivotInversion cfg p) := by
  classical
  have haway : 2 ≤ (awayCircleSupport cfg p c.1).card := by
    rw [card_awayCircleSupport cfg p c.1 hp]
    have hc := circleSupport_card_ge_three cfg c
    omega
  obtain ⟨Aset, hAsub, hAcard⟩ := Finset.exists_subset_card_eq haway
  let A : KSubset (AwayFrom p) 2 := ⟨Aset, hAcard⟩
  have hmem : ∀ q ∈ A.1,
      pivotInversion cfg p q ∈ circlePivotLine cfg p c.1 := by
    intro q hq
    apply (pivotInversion_mem_circlePivotLine_iff cfg p c.1 hp q).2
    exact mem_awayCircleSupport.mp (hAsub hq)
  have hline :
      lineOfPair (pivotInversion cfg p) A = circlePivotLine cfg p c.1 :=
    lineOfPair_eq_of_mem_of_direction_finrank_one
      (pivotInversion cfg p) A (circlePivotLine cfg p c.1) hmem
      (circlePivotLine_direction_finrank cfg p c.1 hp)
  rw [← hline]
  exact lineOfPair_mem_determinedLines (pivotInversion cfg p) A

/-- A determined circle through `p`, regarded as a determined line after
inversion. -/
noncomputable def circleToPivotLine
    {α : Type*} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (p : α) (c : ↥(circlesThrough cfg p)) :
    DeterminedLine (pivotInversion cfg p) :=
  ⟨circlePivotLine cfg p c.1.1,
    circlePivotLine_mem_determinedLines cfg p c.1
      (mem_circlesThrough.mp c.2)⟩

/-- The support on the inverted line is exactly the original circle support
with the pivot removed. -/
theorem lineSupport_circleToPivotLine
    {α : Type*} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (p : α) (c : ↥(circlesThrough cfg p)) :
    lineSupport (pivotInversion cfg p) (circleToPivotLine cfg p c) =
      awayCircleSupport cfg p c.1.1 := by
  ext q
  rw [mem_lineSupport, mem_awayCircleSupport]
  exact pivotInversion_mem_circlePivotLine_iff cfg p c.1.1
    (mem_circlesThrough.mp c.2) q

theorem card_lineSupport_circleToPivotLine
    {α : Type*} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (p : α) (c : ↥(circlesThrough cfg p)) :
    (lineSupport (pivotInversion cfg p) (circleToPivotLine cfg p c)).card =
      (circleTrace cfg c.1.1).card - 1 := by
  rw [lineSupport_circleToPivotLine]
  exact card_awayCircleSupport cfg p c.1.1 (mem_circlesThrough.mp c.2)

/-- Different determined circles through the pivot give different inverted
lines. -/
theorem circleToPivotLine_injective
    {α : Type*} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (p : α) :
    Function.Injective (circleToPivotLine cfg p) := by
  intro c d hline
  apply Subtype.ext
  apply Subtype.ext
  have hpC : p ∈ circleTrace cfg c.1.1 := mem_circlesThrough.mp c.2
  have hpD : p ∈ circleTrace cfg d.1.1 := mem_circlesThrough.mp d.2
  have hline' : circlePivotLine cfg p c.1.1 = circlePivotLine cfg p d.1.1 :=
    congrArg Subtype.val hline
  obtain ⟨t, htC⟩ := (mem_determinedCircles_iff cfg c.1.1).mp c.1.2
  have htD : ∀ x ∈ t.1, cfg x ∈ (d.1.1.1 : Set Point2) := by
    intro x hx
    by_cases hxp : x = p
    · subst x
      exact mem_circleTrace.mp hpD
    · let q : AwayFrom p := ⟨x, hxp⟩
      have hqC :
          pivotInversion cfg p q ∈ circlePivotLine cfg p c.1.1 :=
        (pivotInversion_mem_circlePivotLine_iff cfg p c.1.1 hpC q).2
          (mem_circleTrace.mpr (htC x hx))
      have hqD :
          pivotInversion cfg p q ∈ circlePivotLine cfg p d.1.1 := by
        rw [← hline']
        exact hqC
      exact mem_circleTrace.mp
        ((pivotInversion_mem_circlePivotLine_iff cfg p d.1.1 hpD q).1 hqD)
  have hcircC : c.1.1 = properCircumcircle cfg t :=
    properCircle_eq_properCircumcircle_of_support cfg t c.1.1 htC
  have hcircD : d.1.1 = properCircumcircle cfg t :=
    properCircle_eq_properCircumcircle_of_support cfg t d.1.1 htD
  exact hcircC.trans hcircD.symm

/-- Every line spanned after inversion comes from the circumcircle through
the pivot and any spanning pair. -/
theorem circleToPivotLine_surjective
    {α : Type*} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (hthree : NoThreeCollinear cfg) (p : α) :
    Function.Surjective (circleToPivotLine cfg p) := by
  classical
  intro L
  obtain ⟨A, hAline⟩ := L.exists_pair
  obtain ⟨a, b, hab, hAeq⟩ := Finset.card_eq_two.mp A.2
  have hab' : a.1 ≠ b.1 := by
    intro h
    exact hab (Subtype.ext h)
  let t : Finset α := {p, a.1, b.1}
  have htcard : t.card = 3 := by
    apply Finset.card_eq_three.mpr
    exact ⟨p, a.1, b.1, a.2.symm, b.2.symm, hab', rfl⟩
  have htNoncol : IsNoncollinear cfg t := hthree t htcard
  let nt : NoncollinearTriple cfg :=
    ⟨t, mem_noncollinearTriples.mpr ⟨htcard, htNoncol⟩⟩
  let c₀ : ProperCircle := properCircumcircle cfg nt
  have hc₀det : c₀ ∈ determinedCircles cfg := by
    apply (mem_determinedCircles_iff cfg c₀).2
    refine ⟨nt, ?_⟩
    intro x hx
    exact support_mem_properCircumcircle cfg nt hx
  let c : DeterminedCircle cfg := ⟨c₀, hc₀det⟩
  have hp : p ∈ circleTrace cfg c.1 := by
    apply mem_circleTrace.mpr
    apply support_mem_properCircumcircle cfg nt
    simp [nt, t]
  let cp : ↥(circlesThrough cfg p) := ⟨c, mem_circlesThrough.mpr hp⟩
  refine ⟨cp, ?_⟩
  have hmem : ∀ q ∈ A.1,
      pivotInversion cfg p q ∈ circlePivotLine cfg p c.1 := by
    intro q hq
    have hqab : q = a ∨ q = b := by
      rw [hAeq] at hq
      simpa using hq
    apply (pivotInversion_mem_circlePivotLine_iff cfg p c.1 hp q).2
    apply mem_circleTrace.mpr
    apply support_mem_properCircumcircle cfg nt
    rcases hqab with rfl | rfl <;> simp [nt, t]
  have hpairCircle :
      lineOfPair (pivotInversion cfg p) A = circlePivotLine cfg p c.1 :=
    lineOfPair_eq_of_mem_of_direction_finrank_one
      (pivotInversion cfg p) A (circlePivotLine cfg p c.1) hmem
      (circlePivotLine_direction_finrank cfg p c.1 hp)
  apply Subtype.ext
  exact hpairCircle.symm.trans hAline

/-- The finite equivalence between circles through a pivot and spanned lines
of the inverted configuration. -/
noncomputable def circlePivotLineEquiv
    {α : Type*} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (hthree : NoThreeCollinear cfg) (p : α) :
    ↥(circlesThrough cfg p) ≃ DeterminedLine (pivotInversion cfg p) :=
  Equiv.ofBijective (circleToPivotLine cfg p)
    ⟨circleToPivotLine_injective cfg p,
      circleToPivotLine_surjective cfg hthree p⟩

/-- The coefficient `3-r` of an inverted line is exactly the coefficient
`4-s` of its circle through the pivot. -/
theorem pivotWeight_circleToPivotLine
    {α : Type*} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (p : α) (c : ↥(circlesThrough cfg p)) :
    (3 - ((lineSupport (pivotInversion cfg p)
      (circleToPivotLine cfg p c)).card : ℤ)) =
      4 - ((circleTrace cfg c.1.1).card : ℤ) := by
  have hcard := card_lineSupport_circleToPivotLine cfg p c
  have hthree := circleSupport_card_ge_three cfg c.1
  omega

/-- The ordinary line-census form of Melchior for the inverted configuration
implies the exact pivot row used by V3. -/
theorem pivotMelchior_of_lineMelchior
    {α : Type*} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (hthree : NoThreeCollinear cfg) (p : α)
    (hmel : LineMelchior (pivotInversion cfg p)) :
    PivotMelchior cfg p := by
  unfold LineMelchior at hmel
  unfold PivotMelchior
  rw [← Finset.sum_attach, Finset.attach_eq_univ]
  have hsum :
      (∑ c : ↥(circlesThrough cfg p),
          (4 - ((circleTrace cfg c.1.1).card : ℤ))) =
        ∑ L : DeterminedLine (pivotInversion cfg p),
          (3 - ((lineSupport (pivotInversion cfg p) L).card : ℤ)) := by
    apply Fintype.sum_equiv (circlePivotLineEquiv cfg hthree p)
    intro c
    exact (pivotWeight_circleToPivotLine cfg p c).symm
  rw [hsum]
  exact hmel

/-- V3 admissibility guarantees that every pivot inversion is a genuinely
noncollinear point set.  If all inverted points lay on one line, the circle
through the pivot and any two of them would contain the entire original
configuration. -/
theorem pivotInversion_noncollinear
    {α : Type*} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (hthree : NoThreeCollinear cfg)
    (hnot : NotConcyclic cfg) (hcard : 3 ≤ Fintype.card α) (p : α) :
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
  let t : Finset α := {p, a.1, b.1}
  have htcard : t.card = 3 := by
    apply Finset.card_eq_three.mpr
    exact ⟨p, a.1, b.1, a.2.symm, b.2.symm, hab', rfl⟩
  have htNoncol : IsNoncollinear cfg t := hthree t htcard
  let nt : NoncollinearTriple cfg :=
    ⟨t, mem_noncollinearTriples.mpr ⟨htcard, htNoncol⟩⟩
  let c : ProperCircle := properCircumcircle cfg nt
  have hp : p ∈ circleTrace cfg c := by
    apply mem_circleTrace.mpr
    apply support_mem_properCircumcircle cfg nt
    simp [nt, t]
  have haC : a.1 ∈ circleTrace cfg c := by
    apply mem_circleTrace.mpr
    apply support_mem_properCircumcircle cfg nt
    simp [nt, t]
  have hbC : b.1 ∈ circleTrace cfg c := by
    apply mem_circleTrace.mpr
    apply support_mem_properCircumcircle cfg nt
    simp [nt, t]
  let L : AffineSubspace ℝ Point2 :=
    affineSpan ℝ
      ({pivotInversion cfg p a, pivotInversion cfg p b} : Set Point2)
  have hpairL : lineOfPair (pivotInversion cfg p) A = L := by
    simpa [A, L] using
      (lineOfPair_pair (pivotInversion cfg p) hab)
  have hmemPair : ∀ q ∈ A.1,
      pivotInversion cfg p q ∈ circlePivotLine cfg p c := by
    intro q hq
    have hqab : q = a ∨ q = b := by
      simpa [A] using hq
    apply (pivotInversion_mem_circlePivotLine_iff cfg p c hp q).2
    rcases hqab with rfl | rfl
    · exact haC
    · exact hbC
  have hpairCircle :
      lineOfPair (pivotInversion cfg p) A = circlePivotLine cfg p c :=
    lineOfPair_eq_of_mem_of_direction_finrank_one
      (pivotInversion cfg p) A (circlePivotLine cfg p c) hmemPair
      (circlePivotLine_direction_finrank cfg p c hp)
  have hcircleL : circlePivotLine cfg p c = L :=
    hpairCircle.symm.trans hpairL
  have haRange : pivotInversion cfg p a ∈ pointSet (pivotInversion cfg p) :=
    ⟨a, rfl⟩
  have hbRange : pivotInversion cfg p b ∈ pointSet (pivotInversion cfg p) :=
    ⟨b, rfl⟩
  have habInv : pivotInversion cfg p a ≠ pivotInversion cfg p b :=
    (pivotInversion cfg p).injective.ne hab
  have hall : ∀ x : α, x ∈ circleTrace cfg c := by
    intro x
    by_cases hxp : x = p
    · simpa [hxp] using hp
    · let q : AwayFrom p := ⟨x, hxp⟩
      have hqRange : pivotInversion cfg p q ∈ pointSet (pivotInversion cfg p) :=
        ⟨q, rfl⟩
      have hqL : pivotInversion cfg p q ∈ L :=
        hcol.mem_affineSpan_of_mem_of_ne haRange hbRange hqRange habInv
      have hqCircleLine :
          pivotInversion cfg p q ∈ circlePivotLine cfg p c := by
        rw [hcircleL]
        exact hqL
      exact (pivotInversion_mem_circlePivotLine_iff cfg p c hp q).1
        hqCircleLine
  have htrace : circleTrace cfg c = Finset.univ :=
    Finset.eq_univ_of_forall hall
  have hcNot := hnot c
  rw [htrace] at hcNot
  simp at hcNot

end Erdos506.V3
