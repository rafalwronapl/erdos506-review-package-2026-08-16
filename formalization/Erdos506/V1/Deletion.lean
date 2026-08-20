import Erdos506.V1.FiniteCaps
import Erdos506.V1.NineComplete

/-!
# Deleting one label from a V1 configuration

This module constructs the literal restriction of a configuration to
`AwayFrom p`.  It proves that every circle determined after deletion was
already determined before deletion, and that the only additional family
needed for the sharp counting inequality consists of three-point circles
through the deleted label.

For ten points under the contradictory bound `C <= 32`, the existing rich
line and rich circle pencils make the nine-point deletion admissible.  The
complete nine-point endpoint then gives the local deletion bound
`circleDegree 3 p <= 7`, and the line-arm row upgrades it to
`blockDegree 3 p <= 11`.
-/

namespace Erdos506.V1

open Erdos506.Block
open Erdos506.Block.BlockSystem
open Erdos506.Finite
open Erdos506.Incidence
open Erdos506.V3
open Erdos506.V4

universe u

/-- The raw configuration obtained by forgetting the label `p`.  Unlike
`pivotInversion`, this does not change the remaining point coordinates. -/
noncomputable def deletePointConfiguration
    {α : Type u} [Fintype α]
    (cfg : Configuration α) (p : α) : Configuration (AwayFrom p) where
  toFun q := cfg q.1
  inj' := by
    intro q r hqr
    exact Subtype.ext (cfg.injective hqr)

@[simp] theorem deletePointConfiguration_apply
    {α : Type u} [Fintype α]
    (cfg : Configuration α) (p : α) (q : AwayFrom p) :
    deletePointConfiguration cfg p q = cfg q.1 := rfl

/-- Deletion removes exactly one label. -/
theorem card_deletePointConfiguration
    {α : Type u} [Fintype α] [DecidableEq α]
    (p : α) : Fintype.card (AwayFrom p) = Fintype.card α - 1 :=
  card_awayFrom p

/-- Forget the subtype proof on a finite set of labels away from `p`. -/
noncomputable def liftAwayFinset
    {α : Type u} [DecidableEq α] {p : α}
    (s : Finset (AwayFrom p)) : Finset α :=
  s.image Subtype.val

@[simp] theorem mem_liftAwayFinset
    {α : Type u} [DecidableEq α] {p x : α}
    {s : Finset (AwayFrom p)} :
    x ∈ liftAwayFinset s ↔ ∃ q ∈ s, q.1 = x := by
  simp [liftAwayFinset]

theorem card_liftAwayFinset
    {α : Type u} [DecidableEq α] {p : α}
    (s : Finset (AwayFrom p)) :
    (liftAwayFinset s).card = s.card := by
  rw [liftAwayFinset,
    Finset.card_image_of_injective _ Subtype.val_injective]

@[simp] theorem pivot_not_mem_liftAwayFinset
    {α : Type u} [DecidableEq α] {p : α}
    (s : Finset (AwayFrom p)) :
    p ∉ liftAwayFinset s := by
  simp [liftAwayFinset]

/-- The point set carried by a finite support is unchanged by deletion. -/
theorem supportPoints_deletePointConfiguration
    {α : Type u} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (p : α) (s : Finset (AwayFrom p)) :
    supportPoints (deletePointConfiguration cfg p) s =
      supportPoints cfg (liftAwayFinset s) := by
  ext z
  constructor
  · rintro ⟨q, hq, rfl⟩
    exact ⟨q.1, mem_liftAwayFinset.mpr ⟨q, hq, rfl⟩, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨q, hq, rfl⟩ := mem_liftAwayFinset.mp hx
    exact ⟨q, hq, rfl⟩

/-- Noncollinearity of a finite support is preserved by forgetting the
subtype proof. -/
theorem isNoncollinear_liftAwayFinset_iff
    {α : Type u} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (p : α) (s : Finset (AwayFrom p)) :
    IsNoncollinear cfg (liftAwayFinset s) ↔
      IsNoncollinear (deletePointConfiguration cfg p) s := by
  unfold IsNoncollinear
  rw [supportPoints_deletePointConfiguration]

/-- Circle traces after deletion are the original traces with their labels
viewed in `AwayFrom p`. -/
theorem circleTrace_deletePointConfiguration
    {α : Type u} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (p : α) (c : ProperCircle) :
    circleTrace (deletePointConfiguration cfg p) c =
      awayCircleSupport cfg p c := by
  ext q
  simp [mem_awayCircleSupport]

/-- Lift an attached noncollinear triple from the deleted configuration. -/
noncomputable def liftAwayNoncollinearTriple
    {α : Type u} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (p : α)
    (t : NoncollinearTriple (deletePointConfiguration cfg p)) :
    NoncollinearTriple cfg := by
  refine ⟨liftAwayFinset t.1, mem_noncollinearTriples.mpr ⟨?_, ?_⟩⟩
  · rw [card_liftAwayFinset]
    exact (mem_noncollinearTriples.mp t.2).1
  · exact (isNoncollinear_liftAwayFinset_iff cfg p t.1).2
      (mem_noncollinearTriples.mp t.2).2

/-- A circle determined after deletion, regarded as an original determined
circle.  Its underlying Euclidean circle is unchanged. -/
noncomputable def deletionCircleToOriginal
    {α : Type u} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (p : α)
    (c : DeterminedCircle (deletePointConfiguration cfg p)) :
    DeterminedCircle cfg := by
  refine ⟨c.1, (mem_determinedCircles_iff cfg c.1).2 ?_⟩
  obtain ⟨t, ht⟩ :=
    (mem_determinedCircles_iff (deletePointConfiguration cfg p) c.1).1 c.2
  refine ⟨liftAwayNoncollinearTriple cfg p t, ?_⟩
  intro x hx
  obtain ⟨q, hq, rfl⟩ := mem_liftAwayFinset.mp hx
  simpa using ht q hq

/-- The deletion-to-original circle map is injective because it is the
identity on the underlying proper circle. -/
theorem deletionCircleToOriginal_injective
    {α : Type u} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (p : α) :
    Function.Injective (deletionCircleToOriginal cfg p) := by
  intro c d hcd
  apply Subtype.ext
  exact congrArg (fun z : DeterminedCircle cfg => z.1) hcd

/-- Every deleted trace, lifted to original labels, is contained in the
same original Euclidean circle trace. -/
theorem lift_circleTrace_delete_subset_circleTrace
    {α : Type u} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (p : α) (c : ProperCircle) :
    liftAwayFinset (circleTrace (deletePointConfiguration cfg p) c) ⊆
      circleTrace cfg c := by
  intro x hx
  obtain ⟨q, hq, rfl⟩ := mem_liftAwayFinset.mp hx
  have hpoint : deletePointConfiguration cfg p q ∈ (c : Set Point2) :=
    mem_circleTrace.mp hq
  apply mem_circleTrace.mpr
  simpa using hpoint

/-- Plain monotonicity: deleting a point cannot create a new determined
Euclidean circle. -/
theorem circleCount_deletePointConfiguration_le
    {α : Type u} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (p : α) :
    Erdos506.V4.circleCount (deletePointConfiguration cfg p) ≤
      Erdos506.V4.circleCount cfg := by
  rw [Erdos506.V3.circleCount_eq_card_determinedCircle,
    Erdos506.V3.circleCount_eq_card_determinedCircle]
  exact Fintype.card_le_of_injective
    (deletionCircleToOriginal cfg p)
    (deletionCircleToOriginal_injective cfg p)

/-- Semantic family counted by `circleDegree cfg 3 p`. -/
abbrev ThreeCircleThrough
    {α : Type u} [Fintype α]
    (cfg : Configuration α) (p : α) :=
  {c : DeterminedCircle cfg //
    (circleTrace cfg c.1).card = 3 ∧ p ∈ circleTrace cfg c.1}

/-- The semantic three-circles through `p` are exactly the corresponding
filtered geometric circle blocks. -/
noncomputable def threeCircleThroughBlockEquiv
    {α : Type u} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (p : α) :
    ThreeCircleThrough cfg p ≃
      {b : GeometricBlock cfg //
        b ∈ ((blockSystem cfg).circleBlocksOfSize 3).filter fun b =>
          p ∈ (blockSystem cfg).support b} :=
  Equiv.ofBijective
    (fun c => by
      refine ⟨Sum.inr c.1, Finset.mem_filter.mpr ⟨?_, ?_⟩⟩
      · apply (blockSystem cfg).mem_blocksOfKindSize.mpr
        exact ⟨rfl, c.2.1⟩
      · exact c.2.2)
    (by
      constructor
      · intro c d hcd
        apply Subtype.ext
        exact Sum.inr.inj (congrArg Subtype.val hcd)
      · rintro ⟨b, hb⟩
        have hb' := Finset.mem_filter.mp hb
        have hspec := (blockSystem cfg).mem_blocksOfKindSize.mp hb'.1
        cases b with
        | inl L =>
            cases hspec.1
        | inr c =>
            refine ⟨⟨c, hspec.2, hb'.2⟩, ?_⟩
            apply Subtype.ext
            rfl)

/-- `circleDegree 3 p` is the cardinality of the semantic family above. -/
theorem circleDegree_three_eq_card_threeCircleThrough
    {α : Type u} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (p : α) :
    (blockSystem cfg).circleDegree 3 p =
      Fintype.card (ThreeCircleThrough cfg p) := by
  calc
    (blockSystem cfg).circleDegree 3 p =
        (((blockSystem cfg).circleBlocksOfSize 3).filter fun b =>
          p ∈ (blockSystem cfg).support b).card := rfl
    _ = Fintype.card
        {b : GeometricBlock cfg //
          b ∈ ((blockSystem cfg).circleBlocksOfSize 3).filter fun b =>
            p ∈ (blockSystem cfg).support b} :=
      (Fintype.card_coe _).symm
    _ = Fintype.card (ThreeCircleThrough cfg p) :=
      (Fintype.card_congr (threeCircleThroughBlockEquiv cfg p)).symm

/-- A three-circle through `p` cannot also be determined after deleting
`p`: the latter circle contains three remaining labels, so equality would
put at least four original labels on the former trace. -/
theorem threeCircleThrough_ne_deletionCircle
    {α : Type u} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (p : α)
    (c : ThreeCircleThrough cfg p)
    (d : DeterminedCircle (deletePointConfiguration cfg p)) :
    c.1 ≠ deletionCircleToOriginal cfg p d := by
  intro hcd
  let T : Finset α :=
    liftAwayFinset (circleTrace (deletePointConfiguration cfg p) d.1)
  have hTcard : 3 ≤ T.card := by
    rw [show T.card =
      (circleTrace (deletePointConfiguration cfg p) d.1).card by
        exact card_liftAwayFinset _]
    exact circleSupport_card_ge_three (deletePointConfiguration cfg p) d
  have hpT : p ∉ T := pivot_not_mem_liftAwayFinset _
  have hinsertCard : 4 ≤ (insert p T).card := by
    rw [Finset.card_insert_of_notMem hpT]
    omega
  have hcircleEq : c.1.1 = d.1 := by
    exact congrArg (fun z : DeterminedCircle cfg => z.1) hcd
  have hsub : insert p T ⊆ circleTrace cfg c.1.1 := by
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hxT
    · exact c.2.2
    · have hxOrig :=
        lift_circleTrace_delete_subset_circleTrace cfg p d.1 hxT
      simpa only [hcircleEq] using hxOrig
  have hle := Finset.card_le_card hsub
  rw [c.2.1] at hle
  omega

/-- Combine surviving deleted circles with the disjoint family of lost
three-circles through `p`. -/
noncomputable def deletionCircleSumToOriginal
    {α : Type u} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (p : α) :
    ThreeCircleThrough cfg p ⊕
        DeterminedCircle (deletePointConfiguration cfg p) →
      DeterminedCircle cfg
  | .inl c => c.1
  | .inr d => deletionCircleToOriginal cfg p d

theorem deletionCircleSumToOriginal_injective
    {α : Type u} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (p : α) :
    Function.Injective (deletionCircleSumToOriginal cfg p) := by
  intro x y hxy
  cases x with
  | inl c =>
      cases y with
      | inl d =>
          apply congrArg Sum.inl
          exact Subtype.ext hxy
      | inr d =>
          exact (threeCircleThrough_ne_deletionCircle cfg p c d hxy).elim
  | inr c =>
      cases y with
      | inl d =>
          exact (threeCircleThrough_ne_deletionCircle cfg p d c hxy.symm).elim
      | inr d =>
          apply congrArg Sum.inr
          exact deletionCircleToOriginal_injective cfg p hxy

/-- Sharp deletion inequality: only original three-circles through the
deleted label are guaranteed to disappear. -/
theorem circleDegree_three_add_circleCount_delete_le_circleCount
    {α : Type u} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (p : α) :
    (blockSystem cfg).circleDegree 3 p +
        Erdos506.V4.circleCount (deletePointConfiguration cfg p) ≤
      Erdos506.V4.circleCount cfg := by
  have hcard := Fintype.card_le_of_injective
    (deletionCircleSumToOriginal cfg p)
    (deletionCircleSumToOriginal_injective cfg p)
  simpa [Fintype.card_sum,
    circleDegree_three_eq_card_threeCircleThrough,
    Erdos506.V3.circleCount_eq_card_determinedCircle] using hcard

/-- A line-support cap smaller than the deletion size prevents the remaining
labels from becoming collinear. -/
theorem deletePointConfiguration_noncollinear_of_line_cap
    {α : Type u} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (p : α)
    (hAway : 6 ≤ Fintype.card (AwayFrom p))
    (hlineCap : ∀ L : DeterminedLine cfg,
      (lineSupport cfg L).card ≤ 5) :
    Noncollinear (deletePointConfiguration cfg p) := by
  classical
  intro hcol
  have hpair : 1 < Fintype.card (AwayFrom p) := by omega
  obtain ⟨a, b, hab⟩ := Fintype.exists_pair_of_one_lt_card hpair
  have hab' : a.1 ≠ b.1 := by
    intro heq
    exact hab (Subtype.ext heq)
  let A : KSubset α 2 := ⟨{a.1, b.1}, by simp [hab']⟩
  let L : DeterminedLine cfg :=
    ⟨lineOfPair cfg A, lineOfPair_mem_determinedLines cfg A⟩
  have haRange : deletePointConfiguration cfg p a ∈
      pointSet (deletePointConfiguration cfg p) := ⟨a, rfl⟩
  have hbRange : deletePointConfiguration cfg p b ∈
      pointSet (deletePointConfiguration cfg p) := ⟨b, rfl⟩
  have habCfg : deletePointConfiguration cfg p a ≠
      deletePointConfiguration cfg p b :=
    (deletePointConfiguration cfg p).injective.ne hab
  have hall (q : AwayFrom p) : q.1 ∈ lineSupport cfg L := by
    apply mem_lineSupport.mpr
    change cfg q.1 ∈ lineOfPair cfg A
    have hqRange : deletePointConfiguration cfg p q ∈
        pointSet (deletePointConfiguration cfg p) := ⟨q, rfl⟩
    have hspan := hcol.mem_affineSpan_of_mem_of_ne
      haRange hbRange hqRange habCfg
    have hlinePair : lineOfPair cfg A =
        affineSpan ℝ ({cfg a.1, cfg b.1} : Set Point2) := by
      simpa [A] using lineOfPair_pair cfg hab'
    rw [hlinePair]
    simpa using hspan
  let U : Finset α := liftAwayFinset (Finset.univ : Finset (AwayFrom p))
  have hUcard : U.card = Fintype.card (AwayFrom p) := by
    rw [show U.card = (Finset.univ : Finset (AwayFrom p)).card by
      exact card_liftAwayFinset _]
    simp
  have hUsub : U ⊆ lineSupport cfg L := by
    intro x hx
    obtain ⟨q, _hq, rfl⟩ := mem_liftAwayFinset.mp hx
    exact hall q
  have hle := Finset.card_le_card hUsub
  have hcap := hlineCap L
  omega

/-- A circle-trace cap smaller than the deletion size prevents the remaining
labels from becoming concyclic. -/
theorem deletePointConfiguration_notConcyclic_of_circle_cap
    {α : Type u} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (p : α)
    (hAway : 7 ≤ Fintype.card (AwayFrom p))
    (hcircleCap : ∀ c : DeterminedCircle cfg,
      (circleTrace cfg c.1).card ≤ 6) :
    NotConcyclic (deletePointConfiguration cfg p) := by
  classical
  intro c
  by_contra hnot
  have hdelLarge : 7 ≤
      (circleTrace (deletePointConfiguration cfg p) c).card := by
    omega
  let T : Finset α :=
    liftAwayFinset (circleTrace (deletePointConfiguration cfg p) c)
  have hTcard : 7 ≤ T.card := by
    rw [show T.card =
      (circleTrace (deletePointConfiguration cfg p) c).card by
        exact card_liftAwayFinset _]
    exact hdelLarge
  obtain ⟨Aset, hAT, hAcard⟩ := Finset.exists_subset_card_eq
    (show 3 ≤ T.card by omega)
  let A : KSubset α 3 := ⟨Aset, hAcard⟩
  have hAcircle : A.1 ⊆ circleTrace cfg c := by
    exact hAT.trans (lift_circleTrace_delete_subset_circleTrace cfg p c)
  have hAnoncol : IsNoncollinear cfg A.1 := by
    by_contra hcol
    exact not_triple_subset_circle_of_collinear cfg A hcol c hAcircle
  let t : NoncollinearTriple cfg :=
    ⟨A.1, mem_noncollinearTriples.mpr ⟨A.2, hAnoncol⟩⟩
  have hcDet : c ∈ determinedCircles cfg := by
    apply (mem_determinedCircles_iff cfg c).2
    refine ⟨t, ?_⟩
    intro x hx
    exact mem_circleTrace.mp (hAcircle hx)
  let dc : DeterminedCircle cfg := ⟨c, hcDet⟩
  have hcap := hcircleCap dc
  have hTsub : T ⊆ circleTrace cfg c :=
    lift_circleTrace_delete_subset_circleTrace cfg p c
  have hle := Finset.card_le_card hTsub
  have hcap' : (circleTrace cfg c).card ≤ 6 := by
    simpa [dc] using hcap
  omega

/-- Under the ten-point contradiction bound, every one-point deletion is an
admissible nine-point V1 configuration. -/
theorem deletePointConfiguration_admissible_of_ten
    {α : Type u} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (hadm : Admissible cfg)
    (hcard : Fintype.card α = 10)
    (hcount : Erdos506.V4.circleCount cfg ≤ 32)
    (p : α) :
    Admissible (deletePointConfiguration cfg p) := by
  have hAway : Fintype.card (AwayFrom p) = 9 := by
    rw [card_awayFrom, hcard]
  have hlineCap : ∀ L : DeterminedLine cfg,
      (lineSupport cfg L).card ≤ 5 :=
    lineSupport_card_le_five_of_ten_of_circleCount_le
      cfg hadm hcard hcount
  have hcircleCap : ∀ c : DeterminedCircle cfg,
      (circleTrace cfg c.1).card ≤ 6 :=
    circleTrace_card_le_six_of_ten_of_circleCount_le
      cfg hadm hcard hcount
  constructor
  · apply deletePointConfiguration_noncollinear_of_line_cap
      cfg p (by omega) hlineCap
  · apply deletePointConfiguration_notConcyclic_of_circle_cap
      cfg p (by omega) hcircleCap

/-- The complete nine-point endpoint and the sharp deletion inequality give
the missing local circle-degree bound at ten points. -/
theorem ten_circleDegree_three_le_seven_of_deletion
    {α : Type u} [Fintype α] [DecidableEq α]
    (Mel : RealPlaneMelchiorPrinciple.{u})
    (EvenArr : RealPlaneEvenArrangementPrinciple.{u})
    (Cross : RealPlaneRadicalAxisCrossBlockPrinciple.{u})
    (cfg : Configuration α) (hadm : Admissible cfg)
    (hcard : Fintype.card α = 10)
    (hcount : Erdos506.V4.circleCount cfg ≤ 32)
    (p : α) :
    (blockSystem cfg).circleDegree 3 p ≤ 7 := by
  have hdelCard : Fintype.card (AwayFrom p) = 9 := by
    rw [card_awayFrom, hcard]
  have hdelAdm := deletePointConfiguration_admissible_of_ten
    cfg hadm hcard hcount p
  have hnine := circleCount_ge_twenty_five_of_card_nine
    Mel EvenArr Cross (deletePointConfiguration cfg p) hdelAdm hdelCard
  have hdelete := circleDegree_three_add_circleCount_delete_le_circleCount
    cfg p
  omega

/-- The local block degree splits into its line and circle parts. -/
theorem blockDegree_eq_lineDegree_add_circleDegree
    {Point Block : Type*} [Fintype Point] [Fintype Block]
    [DecidableEq Point]
    (S : BlockSystem Point Block) (s : Nat) (p : Point) :
    S.blockDegree s p = S.lineDegree s p + S.circleDegree s p := by
  classical
  let F := (S.blocksOfSize s).filter fun b => p ∈ S.support b
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := F) (p := fun b => S.kind b = .line)
  have hline : F.filter (fun b => S.kind b = .line) =
      (S.lineBlocksOfSize s).filter fun b => p ∈ S.support b := by
    ext b
    simp [F, BlockSystem.blocksOfSize, BlockSystem.blocksOfKindSize,
      BlockSystem.blocksOfKind, and_assoc, and_comm]
  have hcircle : F.filter (fun b => ¬S.kind b = .line) =
      (S.circleBlocksOfSize s).filter fun b => p ∈ S.support b := by
    ext b
    cases hkind : S.kind b <;>
      simp [F, BlockSystem.blocksOfSize, BlockSystem.blocksOfKindSize,
        BlockSystem.blocksOfKind, hkind, and_comm]
  rw [hline, hcircle] at hsplit
  exact hsplit.symm

/-- The line-arm row gives at most four three-lines through a ten-point
pivot. -/
theorem ten_lineDegree_three_le_four_of_line_arms
    {Point Block : Type*} [Fintype Point] [Fintype Block]
    [DecidableEq Point]
    (S : BlockSystem Point Block)
    (hcard : Fintype.card Point = 10) (p : Point) :
    S.lineDegree 3 p ≤ 4 := by
  have harms := S.line_arms p
  have hterm :
      (3 - 1) * S.lineDegree 3 p ≤
        ∑ s ∈ Finset.range (Fintype.card Point + 1),
          (s - 1) * S.lineDegree s p := by
    exact Finset.single_le_sum
      (fun s _hs => Nat.zero_le ((s - 1) * S.lineDegree s p))
      (by simp [hcard])
  rw [harms, hcard] at hterm
  norm_num at hterm
  omega

/-- The deletion circle bound plus the four-ray line bound supplies the
exact local hypothesis required by `TenLocalParity`. -/
theorem ten_blockDegree_three_le_eleven_of_deletion
    {α : Type u} [Fintype α] [DecidableEq α]
    (Mel : RealPlaneMelchiorPrinciple.{u})
    (EvenArr : RealPlaneEvenArrangementPrinciple.{u})
    (Cross : RealPlaneRadicalAxisCrossBlockPrinciple.{u})
    (cfg : Configuration α) (hadm : Admissible cfg)
    (hcard : Fintype.card α = 10)
    (hcount : Erdos506.V4.circleCount cfg ≤ 32)
    (p : α) :
    (blockSystem cfg).blockDegree 3 p ≤ 11 := by
  have hcircle := ten_circleDegree_three_le_seven_of_deletion
    Mel EvenArr Cross cfg hadm hcard hcount p
  have hline := ten_lineDegree_three_le_four_of_line_arms
    (blockSystem cfg) hcard p
  rw [blockDegree_eq_lineDegree_add_circleDegree]
  omega

end Erdos506.V1
