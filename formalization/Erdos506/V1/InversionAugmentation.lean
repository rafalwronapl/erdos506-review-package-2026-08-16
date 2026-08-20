import Erdos506.V1.BlockRows
import Erdos506.V1.PivotGeometry
import Mathlib.Tactic

/-!
# Inversion augmentation and the ordinary-line census

Given a finite noncollinear configuration `cfg`, choose a new point `o`,
invert `cfg` about `o`, and restore `o` as a new label.  Inverting once more
at the restored label recovers `cfg`, up to the canonical relabelling
`AwayFrom none ≃ α`.

The V1 pivot dictionary counts both radial line blocks and circle blocks.
Consequently the new point only has to avoid the selected point set; it does
not have to avoid every line spanned by the configuration.
-/

namespace Erdos506.V1

open Erdos506.Block
open Erdos506.Block.BlockSystem
open Erdos506.Finite
open Erdos506.Incidence
open Erdos506.V3
open Erdos506.V4
open AffineSubspace

universe u v

/-! ## Relabelling finite configurations -/

/-- Relabel a configuration along an equivalence of its label types. -/
noncomputable def relabelConfiguration
    {α : Type u} {β : Type v}
    (cfg : Configuration α) (e : β ≃ α) : Configuration β where
  toFun x := cfg (e x)
  inj' := cfg.injective.comp e.injective

@[simp] theorem relabelConfiguration_apply
    {α : Type u} {β : Type v}
    (cfg : Configuration α) (e : β ≃ α) (x : β) :
    relabelConfiguration cfg e x = cfg (e x) := rfl

/-- Relabelling an unordered finite support along an equivalence. -/
noncomputable def kSubsetRelabelEquiv
    {α : Type u} {β : Type v} [DecidableEq α] [DecidableEq β]
    (e : β ≃ α) (k : ℕ) : KSubset β k ≃ KSubset α k where
  toFun A := ⟨A.1.map e.toEmbedding, by simp [A.2]⟩
  invFun A := ⟨A.1.map e.symm.toEmbedding, by simp [A.2]⟩
  left_inv A := by
    apply Subtype.ext
    ext x
    simp
  right_inv A := by
    apply Subtype.ext
    ext x
    simp

theorem lineOfPair_relabel
    {α : Type u} {β : Type v}
    [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    (cfg : Configuration α) (e : β ≃ α) (A : KSubset β 2) :
    lineOfPair (relabelConfiguration cfg e) A =
      lineOfPair cfg (kSubsetRelabelEquiv e 2 A) := by
  unfold lineOfPair
  congr 1
  ext y
  simp [relabelConfiguration, kSubsetRelabelEquiv]
  constructor
  · rintro ⟨x, hx, hxy⟩
    refine ⟨e x, ?_, hxy⟩
    rw [e.symm_apply_apply]
    exact hx
  · rintro ⟨x, hx, hxy⟩
    refine ⟨e.symm x, hx, ?_⟩
    rw [e.apply_symm_apply]
    exact hxy

/-- The physical affine lines spanned by a configuration do not depend on
the names of its labels. -/
theorem determinedLines_relabel
    {α : Type u} {β : Type v}
    [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    (cfg : Configuration α) (e : β ≃ α) :
    determinedLines (relabelConfiguration cfg e) = determinedLines cfg := by
  classical
  ext L
  constructor
  · intro hL
    change L ∈ Finset.univ.image (lineOfPair (relabelConfiguration cfg e)) at hL
    obtain ⟨A, _hA, hAL⟩ := Finset.mem_image.mp hL
    apply Finset.mem_image.mpr
    refine ⟨kSubsetRelabelEquiv e 2 A, Finset.mem_univ _, ?_⟩
    rw [← hAL, lineOfPair_relabel]
  · intro hL
    change L ∈ Finset.univ.image (lineOfPair cfg) at hL
    obtain ⟨A, _hA, hAL⟩ := Finset.mem_image.mp hL
    apply Finset.mem_image.mpr
    refine ⟨(kSubsetRelabelEquiv e 2).symm A, Finset.mem_univ _, ?_⟩
    rw [lineOfPair_relabel, Equiv.apply_symm_apply, hAL]

/-- Canonical equivalence of determined lines under relabelling. -/
noncomputable def determinedLineRelabelEquiv
    {α : Type u} {β : Type v}
    [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    (cfg : Configuration α) (e : β ≃ α) :
    DeterminedLine (relabelConfiguration cfg e) ≃ DeterminedLine cfg where
  toFun L := ⟨L.1, by
    rw [← determinedLines_relabel cfg e]
    exact L.2⟩
  invFun L := ⟨L.1, by
    rw [determinedLines_relabel cfg e]
    exact L.2⟩
  left_inv L := by ext; rfl
  right_inv L := by ext; rfl

/-- Relabelling maps the label support of a physical line bijectively onto
its old support. -/
theorem lineSupport_map_relabel
    {α : Type u} {β : Type v}
    [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    (cfg : Configuration α) (e : β ≃ α)
    (L : DeterminedLine (relabelConfiguration cfg e)) :
    (lineSupport (relabelConfiguration cfg e) L).map e.toEmbedding =
      lineSupport cfg (determinedLineRelabelEquiv cfg e L) := by
  classical
  ext x
  constructor
  · intro hx
    obtain ⟨y, hy, hyx⟩ := Finset.mem_map.mp hx
    rw [mem_lineSupport] at hy ⊢
    change cfg (e y) ∈ L.1 at hy
    change cfg x ∈ L.1
    rw [← hyx]
    exact hy
  · intro hx
    apply Finset.mem_map.mpr
    refine ⟨e.symm x, ?_, by simp⟩
    rw [mem_lineSupport] at hx ⊢
    change cfg x ∈ L.1 at hx
    change cfg (e (e.symm x)) ∈ L.1
    rw [e.apply_symm_apply]
    exact hx

theorem card_lineSupport_relabel
    {α : Type u} {β : Type v}
    [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    (cfg : Configuration α) (e : β ≃ α)
    (L : DeterminedLine (relabelConfiguration cfg e)) :
    (lineSupport (relabelConfiguration cfg e) L).card =
      (lineSupport cfg (determinedLineRelabelEquiv cfg e L)).card := by
  calc
    (lineSupport (relabelConfiguration cfg e) L).card =
        ((lineSupport (relabelConfiguration cfg e) L).map e.toEmbedding).card := by
          rw [Finset.card_map]
    _ = (lineSupport cfg (determinedLineRelabelEquiv cfg e L)).card := by
      rw [lineSupport_map_relabel]

/-! ## Size-restricted line and pivot equivalences -/

/-- Determined affine lines carrying exactly `s` selected labels. -/
abbrev DeterminedLineOfSize
    {α : Type u} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (s : ℕ) :=
  {L : DeterminedLine cfg // (lineSupport cfg L).card = s}

/-- Tagged line blocks carrying exactly `s` selected labels. -/
abbrev TaggedLineBlockOfSize
    {α : Type u} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (s : ℕ) :=
  {b : GeometricBlock cfg //
    geometricBlockKind b = .line ∧
      (geometricBlockSupport cfg b).card = s}

/-- A size-restricted form of `lineBlockEquiv`. -/
def taggedLineBlockOfSizeEquiv
    {α : Type u} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (s : ℕ) :
    TaggedLineBlockOfSize cfg s ≃ DeterminedLineOfSize cfg s where
  toFun b := by
    rcases b with ⟨b, hbkind, hbsize⟩
    cases b with
    | inl L => exact ⟨L, hbsize⟩
    | inr c => cases hbkind
  invFun L := ⟨.inl L.1, rfl, L.2⟩
  left_inv b := by
    rcases b with ⟨b, hbkind, hbsize⟩
    cases b with
    | inl L => rfl
    | inr c => cases hbkind
  right_inv L := rfl

/-- The abstract line count is the cardinality of the concrete determined
lines having the requested support size. -/
theorem lineCount_eq_card_determinedLineOfSize
    {α : Type u} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (s : ℕ) :
    (blockSystem cfg).lineCount s = Fintype.card (DeterminedLineOfSize cfg s) := by
  classical
  calc
    (blockSystem cfg).lineCount s =
        Fintype.card (TaggedLineBlockOfSize cfg s) := by
      change
        (((Finset.univ.filter fun b : GeometricBlock cfg =>
            geometricBlockKind b = .line).filter fun b =>
              (geometricBlockSupport cfg b).card = s).card) = _
      rw [Finset.filter_filter]
      simpa [TaggedLineBlockOfSize, and_assoc] using
        (Fintype.card_subtype
          (fun b : GeometricBlock cfg =>
            geometricBlockKind b = .line ∧
              (geometricBlockSupport cfg b).card = s)).symm
    _ = Fintype.card (DeterminedLineOfSize cfg s) :=
      Fintype.card_congr (taggedLineBlockOfSizeEquiv cfg s)

/-- The exact line-size census is invariant under relabelling. -/
theorem lineCount_relabel
    {α : Type u} {β : Type v}
    [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    (cfg : Configuration α) (e : β ≃ α) (s : ℕ) :
    (blockSystem (relabelConfiguration cfg e)).lineCount s =
      (blockSystem cfg).lineCount s := by
  classical
  let lineEquiv :
      DeterminedLineOfSize (relabelConfiguration cfg e) s ≃
        DeterminedLineOfSize cfg s :=
    (determinedLineRelabelEquiv cfg e).subtypeEquiv fun L => by
      rw [card_lineSupport_relabel]
  rw [lineCount_eq_card_determinedLineOfSize,
    lineCount_eq_card_determinedLineOfSize]
  exact Fintype.card_congr lineEquiv

/-- Geometric blocks of a fixed size through a fixed pivot. -/
abbrev TaggedBlockAtSize
    {α : Type u} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (p : α) (s : ℕ) :=
  {b : GeometricBlock cfg //
    (geometricBlockSupport cfg b).card = s ∧
      p ∈ geometricBlockSupport cfg b}

theorem blockDegree_eq_card_taggedBlockAtSize
    {α : Type u} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (p : α) (s : ℕ) :
    (blockSystem cfg).blockDegree s p =
      Fintype.card (TaggedBlockAtSize cfg p s) := by
  classical
  change
    (((Finset.univ.filter fun b : GeometricBlock cfg =>
        (geometricBlockSupport cfg b).card = s).filter fun b =>
          p ∈ geometricBlockSupport cfg b).card) = _
  rw [Finset.filter_filter]
  simpa [TaggedBlockAtSize, and_assoc] using
    (Fintype.card_subtype
      (fun b : GeometricBlock cfg =>
        (geometricBlockSupport cfg b).card = s ∧
          p ∈ geometricBlockSupport cfg b)).symm

/-- Restrict pivot blocks to an arbitrary fixed support size. -/
def taggedBlockAtSizePivotBlockEquiv
    {α : Type u} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (p : α) (s : Nat) (hs : 3 ≤ s) :
    TaggedBlockAtSize cfg p s ≃
      {b : PivotBlock cfg p //
        (geometricBlockSupport cfg b.1).card = s} where
  toFun b := ⟨⟨b.1, b.2.2, by rw [b.2.1]; exact hs⟩, b.2.1⟩
  invFun b := ⟨b.1.1, b.2, b.1.2.1⟩
  left_inv b := by ext; rfl
  right_inv b := by ext; rfl

/-- Fixed-size generalized blocks through a pivot are the one-smaller lines
of the pivot inversion. -/
noncomputable def taggedBlockAtSizePivotLineEquiv
    {α : Type u} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (p : α) (s : Nat) (hs : 3 ≤ s) :
    TaggedBlockAtSize cfg p s ≃
      DeterminedLineOfSize (pivotInversion cfg p) (s - 1) :=
  (taggedBlockAtSizePivotBlockEquiv cfg p s hs).trans <|
    (blockPivotLineEquiv cfg p).subtypeEquiv fun b => by
      change (geometricBlockSupport cfg b.1).card = s ↔
        (lineSupport (pivotInversion cfg p)
          (blockToPivotLine cfg p b)).card = s - 1
      rw [card_lineSupport_blockToPivotLine]
      have hb := b.2.2
      omega

/-- Census form of the fixed-size pivot dictionary. -/
theorem blockDegree_eq_lineCount_pivotInversion
    {α : Type u} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (p : α) (s : Nat) (hs : 3 ≤ s) :
    (blockSystem cfg).blockDegree s p =
      (blockSystem (pivotInversion cfg p)).lineCount (s - 1) := by
  rw [blockDegree_eq_card_taggedBlockAtSize,
    lineCount_eq_card_determinedLineOfSize]
  exact Fintype.card_congr (taggedBlockAtSizePivotLineEquiv cfg p s hs)

/-- A literal three-block through `p` is the same datum as a `PivotBlock`
whose support has size three. -/
def taggedThreeBlockPivotEquiv
    {α : Type u} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (p : α) :
    TaggedBlockAtSize cfg p 3 ≃
      {b : PivotBlock cfg p //
        (geometricBlockSupport cfg b.1).card = 3} where
  toFun b := ⟨⟨b.1, b.2.2, by omega⟩, b.2.1⟩
  invFun b := ⟨b.1.1, b.2, b.1.2.1⟩
  left_inv b := by ext; rfl
  right_inv b := by ext; rfl

/-- Restrict the checked pivot dictionary to three-blocks and ordinary
lines. -/
noncomputable def pivotThreeBlockOrdinaryLineEquiv
    {α : Type u} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (p : α) :
    TaggedBlockAtSize cfg p 3 ≃
      DeterminedLineOfSize (pivotInversion cfg p) 2 :=
  (taggedThreeBlockPivotEquiv cfg p).trans <|
    (blockPivotLineEquiv cfg p).subtypeEquiv fun b => by
      change
        (geometricBlockSupport cfg b.1).card = 3 ↔
          (lineSupport (pivotInversion cfg p)
            (blockToPivotLine cfg p b)).card = 2
      rw [card_lineSupport_blockToPivotLine]
      omega

/-- Exact census form of the checked V1 pivot dictionary: three-blocks
through the pivot are ordinary lines after inversion. -/
theorem blockDegree_three_eq_lineCount_two_pivotInversion
    {α : Type u} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (p : α) :
    (blockSystem cfg).blockDegree 3 p =
      (blockSystem (pivotInversion cfg p)).lineCount 2 := by
  rw [blockDegree_eq_card_taggedBlockAtSize,
    lineCount_eq_card_determinedLineOfSize]
  exact Fintype.card_congr (pivotThreeBlockOrdinaryLineEquiv cfg p)

/-! ## Adding an external inversion centre -/

/-- A finite labelled point set does not exhaust the real plane. -/
theorem exists_external_point
    {α : Type u} [Fintype α] (cfg : Configuration α) :
    ∃ o : Point2, o ∉ pointSet cfg := by
  classical
  let selected : Finset Point2 := Finset.univ.image cfg
  obtain ⟨o, ho⟩ := Infinite.exists_notMem_finset selected
  refine ⟨o, ?_⟩
  rintro ⟨x, rfl⟩
  apply ho
  exact Finset.mem_image.mpr ⟨x, Finset.mem_univ x, rfl⟩

/-- Add an external point `o`, and invert every old point about `o`. -/
noncomputable def inversionAugmentation
    {α : Type u} [Fintype α]
    (cfg : Configuration α) (o : Point2) (ho : o ∉ pointSet cfg) :
    Configuration (Option α) where
  toFun
    | none => o
    | some x => EuclideanGeometry.inversion o 1 (cfg x)
  inj' := by
    intro x y hxy
    cases x with
    | none =>
        cases y with
        | none => rfl
        | some y =>
            exfalso
            have hy : cfg y = o :=
              (EuclideanGeometry.center_eq_inversion one_ne_zero).mp hxy
            exact ho ⟨y, hy⟩
    | some x =>
        cases y with
        | none =>
            exfalso
            have hx : cfg x = o :=
              (EuclideanGeometry.inversion_eq_center one_ne_zero).mp hxy
            exact ho ⟨x, hx⟩
        | some y =>
            apply congrArg some
            apply cfg.injective
            exact EuclideanGeometry.inversion_injective o one_ne_zero hxy

@[simp] theorem inversionAugmentation_none
    {α : Type u} [Fintype α]
    (cfg : Configuration α) (o : Point2) (ho : o ∉ pointSet cfg) :
    inversionAugmentation cfg o ho none = o := rfl

@[simp] theorem inversionAugmentation_some
    {α : Type u} [Fintype α]
    (cfg : Configuration α) (o : Point2) (ho : o ∉ pointSet cfg) (x : α) :
    inversionAugmentation cfg o ho (some x) =
      EuclideanGeometry.inversion o 1 (cfg x) := rfl

/-- Removing `none` from `Option α` leaves exactly `α`. -/
def awayFromNoneEquiv (α : Type u) :
    AwayFrom (none : Option α) ≃ α where
  toFun q := q.1.get (Option.ne_none_iff_isSome.mp q.2)
  invFun x := ⟨some x, Option.some_ne_none x⟩
  left_inv q := by
    apply Subtype.ext
    exact Option.some_get _
  right_inv x := Option.get_some _ _

/-- Double inversion recovers the original configuration, modulo the
canonical equivalence of label types. -/
theorem pivotInversion_inversionAugmentation_eq_relabel
    {α : Type u} [Fintype α]
    (cfg : Configuration α) (o : Point2) (ho : o ∉ pointSet cfg) :
    pivotInversion (inversionAugmentation cfg o ho) none =
      relabelConfiguration cfg (awayFromNoneEquiv α) := by
  ext q
  rcases q with ⟨q, hq⟩
  cases q with
  | none => exact (hq rfl).elim
  | some x =>
      simp [pivotInversion, inversionAugmentation, relabelConfiguration,
        awayFromNoneEquiv, EuclideanGeometry.inversion_inversion]

/-- The inversion augmentation of a noncollinear configuration is V1
admissible. -/
theorem inversionAugmentation_admissible
    {α : Type u} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (hnc : Noncollinear cfg)
    (o : Point2) (ho : o ∉ pointSet cfg) :
    Admissible (inversionAugmentation cfg o ho) := by
  classical
  let aug := inversionAugmentation cfg o ho
  have hα : Nonempty α := by
    by_contra hempty
    haveI : IsEmpty α := not_nonempty_iff.mp hempty
    apply hnc
    have hrange : pointSet cfg = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      rintro _ ⟨x, rfl⟩
      exact isEmptyElim x
    rw [hrange]
    exact collinear_empty ℝ Point2
  let a : α := Classical.choice hα
  have hnoncol : Noncollinear aug := by
    intro hcol
    let z : Option α := none
    let ia : Option α := some a
    have hzRange : aug z ∈ pointSet aug := ⟨z, rfl⟩
    have haRange : aug ia ∈ pointSet aug := ⟨ia, rfl⟩
    have hza : aug z ≠ aug ia := aug.injective.ne (by simp [z, ia])
    let L : AffineSubspace ℝ Point2 :=
      affineSpan ℝ ({aug z, aug ia} : Set Point2)
    have hsubset : pointSet cfg ⊆ (L : Set Point2) := by
      rintro _ ⟨x, rfl⟩
      let ix : Option α := some x
      have hxRange : aug ix ∈ pointSet aug := ⟨ix, rfl⟩
      have hxL : aug ix ∈ L :=
        hcol.mem_affineSpan_of_mem_of_ne hzRange haRange hxRange hza
      have hoL : o ∈ L := by
        change aug z ∈ L
        exact left_mem_affineSpan_pair ℝ _ _
      have hback := EuclideanGeometry.mapsTo_inversion_affineSubspace_of_mem
        (R := (1 : ℝ)) hoL hxL
      simpa [L, z, ia, ix, aug, inversionAugmentation] using hback
    have hLcol : Collinear ℝ (L : Set Point2) := by
      rw [collinear_iff_finrank_le_one,
        ← AffineSubspace.direction_eq_vectorSpan]
      change Module.finrank ℝ
        (affineSpan ℝ ({aug z, aug ia} : Set Point2)).direction ≤ 1
      rw [direction_affineSpan, vectorSpan_pair_rev]
      rw [finrank_span_singleton (vsub_ne_zero.mpr hza.symm)]
    exact hnc (hLcol.subset hsubset)
  refine ⟨hnoncol, ?_⟩
  intro c
  have hle :
      (circleTrace aug c).card ≤ Fintype.card (Option α) := by
    simpa using Finset.card_le_univ (circleTrace aug c)
  apply lt_of_le_of_ne hle
  intro heq
  have hall : circleTrace aug c = Finset.univ :=
    Finset.eq_univ_of_card _ heq
  have hnone : none ∈ circleTrace aug c := by
    rw [hall]
    exact Finset.mem_univ none
  have hcenter : o ∈ (c.1 : Set Point2) := by
    simpa [aug] using (mem_circleTrace.mp hnone)
  let P : AffineSubspace ℝ Point2 :=
    perpBisector o (EuclideanGeometry.inversion o 1 c.1.center)
  have hPfin : Module.finrank ℝ P.direction = 1 := by
    simpa [P, circlePivotLine, aug] using
      (circlePivotLine_direction_finrank aug none c hnone)
  have hsubset : pointSet cfg ⊆ (P : Set Point2) := by
    rintro _ ⟨x, rfl⟩
    have hsome : some x ∈ circleTrace aug c := by
      rw [hall]
      exact Finset.mem_univ (some x)
    have hinCircle : EuclideanGeometry.inversion o 1 (cfg x) ∈
        (c.1 : Set Point2) := by
      simpa [aug, inversionAugmentation] using (mem_circleTrace.mp hsome)
    have hinNe : EuclideanGeometry.inversion o 1 (cfg x) ≠ o := by
      intro h
      have hx : cfg x = o :=
        (EuclideanGeometry.inversion_eq_center one_ne_zero).mp h
      exact ho ⟨x, hx⟩
    have hinP :=
      (mem_circle_through_center_iff_inversion_mem_perpBisector
        o (EuclideanGeometry.inversion o 1 (cfg x)) c hinNe hcenter).mp
          hinCircle
    change cfg x ∈ P
    simpa [P] using hinP
  have hPcol : Collinear ℝ (P : Set Point2) := by
    rw [collinear_iff_finrank_le_one,
      ← AffineSubspace.direction_eq_vectorSpan, hPfin]
  exact hnc (hPcol.subset hsubset)

/-- At the added centre, three-blocks count exactly the ordinary affine
lines of the original configuration. -/
theorem blockDegree_three_inversionAugmentation
    {α : Type u} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (o : Point2) (ho : o ∉ pointSet cfg) :
    (blockSystem (inversionAugmentation cfg o ho)).blockDegree 3 none =
      (blockSystem cfg).lineCount 2 := by
  rw [blockDegree_three_eq_lineCount_two_pivotInversion,
    pivotInversion_inversionAugmentation_eq_relabel,
    lineCount_relabel]

end Erdos506.V1
