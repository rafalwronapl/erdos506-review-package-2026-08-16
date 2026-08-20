import Erdos506.V1.PivotGeometry

/-!
# Restoring the inversion centre

For the second universal Melchior row, the inversion centre is added back to
the inverted configuration.  Radial image lines then regain the pivot label,
while image lines of circles do not.  This file starts with the labelled
configuration and its noncollinearity.
-/

namespace Erdos506.V1

open Erdos506.Block
open Erdos506.Finite
open Erdos506.Incidence
open Erdos506.V3
open Erdos506.V4
open AffineSubspace

/-- The pivot inversion with the inversion centre restored as a new label. -/
noncomputable def restoredPivotConfiguration
    {α : Type*} [Fintype α]
    (cfg : Configuration α) (p : α) :
    Configuration (Option (AwayFrom p)) where
  toFun
    | none => cfg p
    | some q => pivotInversion cfg p q
  inj' := by
    intro x y hxy
    cases x with
    | none =>
        cases y with
        | none => rfl
        | some q =>
            exfalso
            have hcenter : cfg p =
                EuclideanGeometry.inversion (cfg p) 1 (cfg q.1) := hxy
            have hqp : cfg q.1 = cfg p :=
              (EuclideanGeometry.center_eq_inversion one_ne_zero).mp hcenter
            exact q.2 (cfg.injective hqp)
    | some q =>
        cases y with
        | none =>
            exfalso
            have hcenter :
                EuclideanGeometry.inversion (cfg p) 1 (cfg q.1) = cfg p := hxy
            have hqp : cfg q.1 = cfg p :=
              (EuclideanGeometry.inversion_eq_center one_ne_zero).mp hcenter
            exact q.2 (cfg.injective hqp)
        | some r =>
            apply congrArg some
            apply Subtype.ext
            apply cfg.injective
            exact EuclideanGeometry.inversion_injective (cfg p) one_ne_zero hxy

@[simp] theorem restoredPivotConfiguration_none
    {α : Type*} [Fintype α]
    (cfg : Configuration α) (p : α) :
    restoredPivotConfiguration cfg p none = cfg p := rfl

@[simp] theorem restoredPivotConfiguration_some
    {α : Type*} [Fintype α]
    (cfg : Configuration α) (p : α) (q : AwayFrom p) :
    restoredPivotConfiguration cfg p (some q) = pivotInversion cfg p q := rfl

/-- Restoring the centre cannot make an admissible V1 configuration
collinear.  A line containing the centre is invariant under inversion, so a
collinear restored image would put every original point on one line. -/
theorem restoredPivotConfiguration_noncollinear
    {α : Type*} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (hadm : Admissible cfg)
    (hcard : 3 ≤ Fintype.card α) (p : α) :
    Noncollinear (restoredPivotConfiguration cfg p) := by
  classical
  intro hcol
  have hAwayPos : 0 < Fintype.card (AwayFrom p) := by
    rw [card_awayFrom]
    omega
  obtain ⟨a⟩ := Fintype.card_pos_iff.mp hAwayPos
  let o : Option (AwayFrom p) := none
  let ia : Option (AwayFrom p) := some a
  have hoRange : restoredPivotConfiguration cfg p o ∈
      pointSet (restoredPivotConfiguration cfg p) := ⟨o, rfl⟩
  have haRange : restoredPivotConfiguration cfg p ia ∈
      pointSet (restoredPivotConfiguration cfg p) := ⟨ia, rfl⟩
  have hoa : restoredPivotConfiguration cfg p o ≠
      restoredPivotConfiguration cfg p ia :=
    (restoredPivotConfiguration cfg p).injective.ne (by simp [o, ia])
  let L : AffineSubspace ℝ Point2 :=
    affineSpan ℝ
      ({restoredPivotConfiguration cfg p o,
        restoredPivotConfiguration cfg p ia} : Set Point2)
  have hsubset : pointSet cfg ⊆ (L : Set Point2) := by
    rintro _y ⟨x, rfl⟩
    by_cases hxp : x = p
    · subst x
      exact left_mem_affineSpan_pair ℝ _ _
    · let q : AwayFrom p := ⟨x, hxp⟩
      let iq : Option (AwayFrom p) := some q
      have hqRange : restoredPivotConfiguration cfg p iq ∈
          pointSet (restoredPivotConfiguration cfg p) := ⟨iq, rfl⟩
      have hqL : restoredPivotConfiguration cfg p iq ∈ L :=
        hcol.mem_affineSpan_of_mem_of_ne hoRange haRange hqRange hoa
      have hcenterL : cfg p ∈ L := by
        exact left_mem_affineSpan_pair ℝ _ _
      have hback := EuclideanGeometry.mapsTo_inversion_affineSubspace_of_mem
        (R := (1 : ℝ)) hcenterL hqL
      simpa [L, o, ia, iq, q, restoredPivotConfiguration,
        pivotInversion] using hback
  have hLcol : Collinear ℝ (L : Set Point2) := by
    rw [collinear_iff_finrank_le_one,
      ← AffineSubspace.direction_eq_vectorSpan]
    change Module.finrank ℝ
      (affineSpan ℝ
        ({restoredPivotConfiguration cfg p o,
          restoredPivotConfiguration cfg p ia} : Set Point2)).direction ≤ 1
    rw [direction_affineSpan, vectorSpan_pair_rev]
    rw [finrank_span_singleton (vsub_ne_zero.mpr hoa.symm)]
  exact hadm.1 (hLcol.subset hsubset)

/-- All geometric V1 blocks through the pivot.  The minimum-size fields of
`BlockSystem` imply size at least two for line blocks and at least three for
circle blocks. -/
abbrev BlockThrough
    {α : Type*} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (p : α) :=
  {b : GeometricBlock cfg // p ∈ geometricBlockSupport cfg b}

noncomputable def someAwaySupport
    {α : Type*} [Fintype α]
    (p : α) (T : Finset α) : Finset (Option (AwayFrom p)) :=
  (awaySupport p T).map Function.Embedding.some

@[simp] theorem mem_someAwaySupport
    {α : Type*} [Fintype α]
    {p : α} {T : Finset α} {q : AwayFrom p} :
    some q ∈ someAwaySupport p T ↔ q.1 ∈ T := by
  classical
  simp [someAwaySupport]

@[simp] theorem none_not_mem_someAwaySupport
    {α : Type*} [Fintype α]
    {p : α} {T : Finset α} :
    none ∉ someAwaySupport p T := by
  classical
  simp [someAwaySupport]

/-- Expected label support of a restored image line, split by the original
carrier kind. -/
noncomputable def restoredCarrierSupport
    {α : Type*} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (p : α) :
    GeometricBlock cfg → Finset (Option (AwayFrom p))
  | .inl L => insert none (someAwaySupport p (lineSupport cfg L))
  | .inr c => someAwaySupport p (circleTrace cfg c.1)

@[simp] theorem some_mem_restoredCarrierSupport
    {α : Type*} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (p : α) (b : GeometricBlock cfg)
    (q : AwayFrom p) :
    some q ∈ restoredCarrierSupport cfg p b ↔
      q.1 ∈ geometricBlockSupport cfg b := by
  cases b with
  | inl L => simp [restoredCarrierSupport, geometricBlockSupport]
  | inr c => simp [restoredCarrierSupport, geometricBlockSupport]

theorem originalLine_mem_restoredDeterminedLines
    {α : Type*} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (p : α) (L : DeterminedLine cfg)
    (hp : p ∈ lineSupport cfg L) :
    L.1 ∈ determinedLines (restoredPivotConfiguration cfg p) := by
  classical
  have haway : 0 < (awaySupport p (lineSupport cfg L)).card := by
    rw [card_awaySupport p (lineSupport cfg L) hp]
    have hmin := two_le_lineSupport_card cfg L
    omega
  obtain ⟨q, hq⟩ := Finset.card_pos.mp haway
  let A : KSubset (Option (AwayFrom p)) 2 :=
    ⟨{none, some q}, by simp⟩
  have hmem : ∀ z ∈ A.1, restoredPivotConfiguration cfg p z ∈ L.1 := by
    intro z hz
    have hz' : z = none ∨ z = some q := by simpa [A] using hz
    rcases hz' with rfl | rfl
    · exact mem_lineSupport.mp hp
    · exact (pivotInversion_mem_line_iff cfg p L hp q).2
        (mem_awaySupport.mp hq)
  have hline : lineOfPair (restoredPivotConfiguration cfg p) A = L.1 :=
    lineOfPair_eq_of_mem_of_direction_finrank_one
      (restoredPivotConfiguration cfg p) A L.1 hmem L.direction_finrank
  rw [← hline]
  exact lineOfPair_mem_determinedLines (restoredPivotConfiguration cfg p) A

theorem circlePivotLine_mem_restoredDeterminedLines
    {α : Type*} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (p : α) (c : DeterminedCircle cfg)
    (hp : p ∈ circleTrace cfg c.1) :
    circlePivotLine cfg p c.1 ∈
      determinedLines (restoredPivotConfiguration cfg p) := by
  classical
  have haway : 2 ≤ (awaySupport p (circleTrace cfg c.1)).card := by
    rw [card_awaySupport p (circleTrace cfg c.1) hp]
    have hmin := Erdos506.V3.circleSupport_card_ge_three cfg c
    omega
  obtain ⟨Aset, hAsub, hAcard⟩ := Finset.exists_subset_card_eq haway
  let Aaway : KSubset (AwayFrom p) 2 := ⟨Aset, hAcard⟩
  let Arest : KSubset (Option (AwayFrom p)) 2 :=
    ⟨Aset.map Function.Embedding.some, by simp [hAcard]⟩
  have hmem : ∀ z ∈ Arest.1,
      restoredPivotConfiguration cfg p z ∈ circlePivotLine cfg p c.1 := by
    intro z hz
    obtain ⟨q, hq, rfl⟩ := Finset.mem_map.mp hz
    exact (pivotInversion_mem_circlePivotLine_iff cfg p c.1 hp q).2
      (mem_awaySupport.mp (hAsub hq))
  have hline :
      lineOfPair (restoredPivotConfiguration cfg p) Arest =
        circlePivotLine cfg p c.1 :=
    lineOfPair_eq_of_mem_of_direction_finrank_one
      (restoredPivotConfiguration cfg p) Arest
      (circlePivotLine cfg p c.1) hmem
      (circlePivotLine_direction_finrank cfg p c.1 hp)
  rw [← hline]
  exact lineOfPair_mem_determinedLines (restoredPivotConfiguration cfg p) Arest

/-- A block through the pivot regarded as a determined line of the restored
inversion. -/
noncomputable def blockToRestoredLine
    {α : Type*} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (p : α) (b : BlockThrough cfg p) :
    DeterminedLine (restoredPivotConfiguration cfg p) := by
  rcases b with ⟨b, hp⟩
  cases b with
  | inl L =>
      exact ⟨L.1, originalLine_mem_restoredDeterminedLines cfg p L hp⟩
  | inr c =>
      exact ⟨circlePivotLine cfg p c.1,
        circlePivotLine_mem_restoredDeterminedLines cfg p c hp⟩

theorem lineSupport_blockToRestoredLine
    {α : Type*} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (p : α) (b : BlockThrough cfg p) :
    lineSupport (restoredPivotConfiguration cfg p)
      (blockToRestoredLine cfg p b) = restoredCarrierSupport cfg p b.1 := by
  rcases b with ⟨b, hp⟩
  cases b with
  | inl L =>
      ext z
      cases z with
      | none =>
          simp only [mem_lineSupport, restoredPivotConfiguration_none,
            restoredCarrierSupport, Finset.mem_insert, true_or]
          constructor
          · intro _h
            trivial
          · intro _h
            change cfg p ∈ L.1
            exact mem_lineSupport.mp hp
      | some q =>
          rw [mem_lineSupport]
          simp only [restoredPivotConfiguration_some, restoredCarrierSupport,
            Finset.mem_insert, Option.some_ne_none,
            false_or, mem_someAwaySupport]
          exact pivotInversion_mem_line_iff cfg p L hp q
  | inr c =>
      ext z
      cases z with
      | none =>
          rw [mem_lineSupport]
          simp only [restoredPivotConfiguration_none, restoredCarrierSupport,
            none_not_mem_someAwaySupport]
          constructor
          · intro hmem
            change cfg p ∈ circlePivotLine cfg p c.1 at hmem
            rw [circlePivotLine, left_mem_perpBisector] at hmem
            exact (pivot_ne_inverted_circle_center cfg p c.1 hp hmem).elim
          · intro hfalse
            exact hfalse.elim
      | some q =>
          rw [mem_lineSupport]
          simp only [restoredPivotConfiguration_some, restoredCarrierSupport,
            mem_someAwaySupport]
          exact pivotInversion_mem_circlePivotLine_iff cfg p c.1 hp q

theorem card_lineSupport_blockToRestoredLine
    {α : Type*} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (p : α) (b : BlockThrough cfg p) :
    (lineSupport (restoredPivotConfiguration cfg p)
      (blockToRestoredLine cfg p b)).card =
      match b.1 with
      | .inl _ => (geometricBlockSupport cfg b.1).card
      | .inr _ => (geometricBlockSupport cfg b.1).card - 1 := by
  rw [lineSupport_blockToRestoredLine]
  rcases b with ⟨b, hp⟩
  cases b with
  | inl L =>
      change (insert none (someAwaySupport p (lineSupport cfg L))).card =
        (lineSupport cfg L).card
      rw [Finset.card_insert_of_notMem none_not_mem_someAwaySupport]
      rw [someAwaySupport, Finset.card_map]
      rw [card_awaySupport p (lineSupport cfg L) hp]
      have hmin := two_le_lineSupport_card cfg L
      omega
  | inr c =>
      change (someAwaySupport p (circleTrace cfg c.1)).card =
        (circleTrace cfg c.1).card - 1
      rw [someAwaySupport, Finset.card_map]
      exact card_awaySupport p (circleTrace cfg c.1) hp

theorem blockToRestoredLine_injective
    {α : Type*} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (p : α) :
    Function.Injective (blockToRestoredLine cfg p) := by
  classical
  intro b c hline
  have hrest : restoredCarrierSupport cfg p b.1 =
      restoredCarrierSupport cfg p c.1 := by
    rw [← lineSupport_blockToRestoredLine cfg p b,
      ← lineSupport_blockToRestoredLine cfg p c, hline]
  have hsupp : geometricBlockSupport cfg b.1 =
      geometricBlockSupport cfg c.1 := by
    ext x
    by_cases hxp : x = p
    · subst x
      exact iff_of_true b.2 c.2
    · let q : AwayFrom p := ⟨x, hxp⟩
      constructor
      · intro hx
        have hq : some q ∈ restoredCarrierSupport cfg p b.1 :=
          (some_mem_restoredCarrierSupport cfg p b.1 q).2 hx
        rw [hrest] at hq
        exact (some_mem_restoredCarrierSupport cfg p c.1 q).1 hq
      · intro hx
        have hq : some q ∈ restoredCarrierSupport cfg p c.1 :=
          (some_mem_restoredCarrierSupport cfg p c.1 q).2 hx
        rw [← hrest] at hq
        exact (some_mem_restoredCarrierSupport cfg p b.1 q).1 hq
  apply Subtype.ext
  by_cases hthree : 3 ≤ (geometricBlockSupport cfg b.1).card
  · obtain ⟨Aset, hAsub, hAcard⟩ :=
      Finset.exists_subset_card_eq hthree
    let A : KSubset α 3 := ⟨Aset, hAcard⟩
    have hbOwner : b.1 = geometricTripleOwner cfg A :=
      geometricTripleOwner_unique cfg A b.1 hAsub
    have hcOwner : c.1 = geometricTripleOwner cfg A :=
      geometricTripleOwner_unique cfg A c.1 (by
        intro x hx
        rw [← hsupp]
        exact hAsub hx)
    exact hbOwner.trans hcOwner.symm
  · cases hb : b.1 with
    | inl L =>
        cases hc : c.1 with
        | inl M =>
            have hLM : lineSupport cfg L = lineSupport cfg M := by
              simpa [hb, hc, geometricBlockSupport] using hsupp
            have hLcard : (lineSupport cfg L).card = 2 := by
              have hmin := two_le_lineSupport_card cfg L
              have hnot : ¬3 ≤ (lineSupport cfg L).card := by
                simpa [hb, geometricBlockSupport] using hthree
              omega
            let A : KSubset α 2 := ⟨lineSupport cfg L, hLcard⟩
            let lb : {d : GeometricBlock cfg // geometricBlockKind d = .line} :=
              ⟨.inl L, rfl⟩
            let lc : {d : GeometricBlock cfg // geometricBlockKind d = .line} :=
              ⟨.inl M, rfl⟩
            have hbLine : lb = geometricLineOwner cfg A :=
              geometricLineOwner_unique cfg A lb (by
                intro x hx
                exact hx)
            have hcLine : lc = geometricLineOwner cfg A :=
              geometricLineOwner_unique cfg A lc (by
                intro x hx
                change x ∈ lineSupport cfg M
                rw [← hLM]
                exact hx)
            exact congrArg Subtype.val (hbLine.trans hcLine.symm)
        | inr d =>
            have hdmin := Erdos506.V3.circleSupport_card_ge_three cfg d
            have heq : lineSupport cfg L = circleTrace cfg d.1 := by
              simpa [hb, hc, geometricBlockSupport] using hsupp
            rw [← heq] at hdmin
            have hLcard : ¬3 ≤ (lineSupport cfg L).card := by
              simpa [hb, geometricBlockSupport] using hthree
            exact (hLcard hdmin).elim
    | inr d =>
        have hdmin := Erdos506.V3.circleSupport_card_ge_three cfg d
        have hnot : ¬3 ≤ (circleTrace cfg d.1).card := by
          simpa [hb, geometricBlockSupport] using hthree
        exact (hnot hdmin).elim

theorem blockToRestoredLine_surjective
    {α : Type*} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (p : α) :
    Function.Surjective (blockToRestoredLine cfg p) := by
  classical
  intro D
  obtain ⟨A, hAD⟩ := D.exists_pair
  obtain ⟨z, w, hzw, hAeq⟩ := Finset.card_eq_two.mp A.2
  have lineCase (q : AwayFrom p)
      (hAq : A.1 = {none, some q}) :
      ∃ b : BlockThrough cfg p, blockToRestoredLine cfg p b = D := by
    let B : KSubset α 2 := ⟨{p, q.1}, by simp [q.2.symm]⟩
    let L : DeterminedLine cfg :=
      ⟨lineOfPair cfg B, lineOfPair_mem_determinedLines cfg B⟩
    have hpL : p ∈ lineSupport cfg L := by
      apply pair_subset_lineSupport cfg B
      simp [B]
    have hqL : q.1 ∈ lineSupport cfg L := by
      apply pair_subset_lineSupport cfg B
      simp [B]
    let bt : BlockThrough cfg p := ⟨.inl L, hpL⟩
    have hmem : ∀ u ∈ A.1,
        restoredPivotConfiguration cfg p u ∈
          (blockToRestoredLine cfg p bt).1 := by
      intro u hu
      have hu' : u = none ∨ u = some q := by
        rw [hAq] at hu
        simpa using hu
      rcases hu' with rfl | rfl
      · change cfg p ∈ L.1
        exact mem_lineSupport.mp hpL
      · change pivotInversion cfg p q ∈ L.1
        exact (pivotInversion_mem_line_iff cfg p L hpL q).2 hqL
    have hpairMap :
        lineOfPair (restoredPivotConfiguration cfg p) A =
          (blockToRestoredLine cfg p bt).1 :=
      lineOfPair_eq_of_mem_of_direction_finrank_one
        (restoredPivotConfiguration cfg p) A
        (blockToRestoredLine cfg p bt).1 hmem
        (blockToRestoredLine cfg p bt).direction_finrank
    refine ⟨bt, ?_⟩
    apply Subtype.ext
    exact hpairMap.symm.trans hAD
  have tripleCase (q r : AwayFrom p) (hqr : q.1 ≠ r.1)
      (hAqr : A.1 = {some q, some r}) :
      ∃ b : BlockThrough cfg p, blockToRestoredLine cfg p b = D := by
    let Tset : Finset α := {p, q.1, r.1}
    have hTcard : Tset.card = 3 := by
      apply Finset.card_eq_three.mpr
      exact ⟨p, q.1, r.1, q.2.symm, r.2.symm, hqr, rfl⟩
    let T : KSubset α 3 := ⟨Tset, hTcard⟩
    let owner : GeometricBlock cfg := geometricTripleOwner cfg T
    have hTsub : T.1 ⊆ geometricBlockSupport cfg owner :=
      geometricTripleOwner_contains cfg T
    have hpOwner : p ∈ geometricBlockSupport cfg owner :=
      hTsub (by simp [T, Tset])
    have hqOwner : q.1 ∈ geometricBlockSupport cfg owner :=
      hTsub (by simp [T, Tset])
    have hrOwner : r.1 ∈ geometricBlockSupport cfg owner :=
      hTsub (by simp [T, Tset])
    let bt : BlockThrough cfg p := ⟨owner, hpOwner⟩
    have hmem : ∀ u ∈ A.1,
        restoredPivotConfiguration cfg p u ∈
          (blockToRestoredLine cfg p bt).1 := by
      intro u hu
      have hu' : u = some q ∨ u = some r := by
        rw [hAqr] at hu
        simpa using hu
      apply mem_lineSupport.mp
      rw [lineSupport_blockToRestoredLine cfg p bt]
      rcases hu' with rfl | rfl
      · exact (some_mem_restoredCarrierSupport cfg p owner q).2 hqOwner
      · exact (some_mem_restoredCarrierSupport cfg p owner r).2 hrOwner
    have hpairMap :
        lineOfPair (restoredPivotConfiguration cfg p) A =
          (blockToRestoredLine cfg p bt).1 :=
      lineOfPair_eq_of_mem_of_direction_finrank_one
        (restoredPivotConfiguration cfg p) A
        (blockToRestoredLine cfg p bt).1 hmem
        (blockToRestoredLine cfg p bt).direction_finrank
    refine ⟨bt, ?_⟩
    apply Subtype.ext
    exact hpairMap.symm.trans hAD
  cases z with
  | none =>
      cases w with
      | none => exact (hzw rfl).elim
      | some q => exact lineCase q hAeq
  | some q =>
      cases w with
      | none =>
          apply lineCase q
          simpa [Finset.pair_comm] using hAeq
      | some r =>
          apply tripleCase q r
          · intro hqr
            exact hzw (congrArg some (Subtype.ext hqr))
          · exact hAeq

/-- Exact equivalence between all original blocks through the pivot and all
spanned lines after restoring the inversion centre. -/
noncomputable def blockRestoredLineEquiv
    {α : Type*} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (p : α) :
    BlockThrough cfg p ≃
      DeterminedLine (restoredPivotConfiguration cfg p) :=
  Equiv.ofBijective (blockToRestoredLine cfg p)
    ⟨blockToRestoredLine_injective cfg p,
      blockToRestoredLine_surjective cfg p⟩

/-- The block coefficient is exactly the Melchior coefficient of its line in
the restored configuration. -/
theorem restoredWeight_blockToRestoredLine
    {α : Type*} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (p : α) (b : BlockThrough cfg p) :
    (3 - ((lineSupport (restoredPivotConfiguration cfg p)
      (blockToRestoredLine cfg p b)).card : ℤ)) =
      (geometricBlockSystem cfg).restoredBlockWeight b.1 := by
  rw [card_lineSupport_blockToRestoredLine]
  rcases b with ⟨b, hp⟩
  cases b with
  | inl L =>
      rfl
  | inr c =>
      have hmin := Erdos506.V3.circleSupport_card_ge_three cfg c
      change 3 - (((circleTrace cfg c.1).card - 1 : ℕ) : ℤ) =
        4 - ((circleTrace cfg c.1).card : ℤ)
      omega

/-- Melchior for the restored inverted configuration proves nonnegativity of
the exact local `kappa` expression. -/
theorem restoredKappa_nonneg_of_lineMelchior
    {α : Type*} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (p : α)
    (hmel : LineMelchior (restoredPivotConfiguration cfg p)) :
    0 ≤ (geometricBlockSystem cfg).restoredKappa p := by
  unfold LineMelchior at hmel
  have hsum :
      (∑ b : BlockThrough cfg p,
          (geometricBlockSystem cfg).restoredBlockWeight b.1) =
        ∑ L : DeterminedLine (restoredPivotConfiguration cfg p),
          (3 - ((lineSupport (restoredPivotConfiguration cfg p) L).card : ℤ)) := by
    apply Fintype.sum_equiv (blockRestoredLineEquiv cfg p)
    intro b
    exact (restoredWeight_blockToRestoredLine cfg p b).symm
  rw [(geometricBlockSystem cfg).restoredKappa_eq_sum_blockAt_weight_sub_three]
  change 0 ≤
    (∑ b : BlockThrough cfg p,
      (geometricBlockSystem cfg).restoredBlockWeight b.1) - 3
  rw [hsum]
  omega

end Erdos506.V1
