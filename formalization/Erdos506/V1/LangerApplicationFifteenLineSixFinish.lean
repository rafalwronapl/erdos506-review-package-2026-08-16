import Erdos506.Incidence.SixConicEightOutsiderLineIncidence
import Erdos506.Incidence.RealProjectiveArrangementWeakKellyFinish
import Erdos506.V1.DeletionLineCensus
import Erdos506.V1.LangerApplicationFifteenSixCircleFinish
import Erdos506.V1.LangerApplicationFifteenLineSevenFinish
import Erdos506.V1.LangerApplicationFourteenSixLineEndpoint
import Erdos506.V1.LangerApplicationLineSixResidual
import Erdos506.V1.TenFiveSixPower

/-!
# The fifteen-point selected six-line: finite endpoint

This file closes the remaining `(15,6)` rich-line case.  It records the sharp
pivot-inversion dictionary and the resulting fan pair-moment bound `W <= 90`.
The final endpoint uses a shorter independent route: eliminate all size-seven
blocks, retain the selected line's functional slack `108`, and combine the
fifteen-point moment expansion with the universal two--two capacity.
-/

namespace Erdos506.V1

open Erdos506.Block
open Erdos506.Block.BlockSystem
open Erdos506.Finite
open Erdos506.Incidence
open Erdos506.V3
open Erdos506.V4
open AffineSubspace
open scoped BigOperators
open scoped EuclideanSpace

universe u

variable {alpha : Type u} [Fintype alpha] [DecidableEq alpha]

/-! ## A selected line becomes an exact determined circle -/

/-- A determined affine line is the perpendicular bisector of a point and
its reflection in that line. -/
theorem determinedLine_eq_perpBisector_reflection_of_not_mem
    (cfg : Configuration alpha) (p : alpha) (L : DeterminedLine cfg)
    [Nonempty L.1]
    (hp : p ∉ lineSupport cfg L) :
    L.1 = perpBisector (cfg p) (EuclideanGeometry.reflection L.1 (cfg p)) := by
  classical
  let y : Point2 := EuclideanGeometry.reflection L.1 (cfg p)
  have hpGeom : cfg p ∉ L.1 := by
    intro h
    exact hp (mem_lineSupport.mpr h)
  have hy : y ≠ cfg p := by
    intro h
    exact hpGeom ((EuclideanGeometry.reflection_eq_self_iff
      (s := L.1) (cfg p)).mp h)
  let P : AffineSubspace ℝ Point2 := perpBisector (cfg p) y
  have hPfin : Module.finrank ℝ P.direction = 1 := by
    dsimp only [P]
    rw [direction_perpBisector]
    exact Submodule.finrank_orthogonal_span_singleton
      (sub_ne_zero.mpr hy)
  obtain ⟨A, hA⟩ := L.exists_pair
  have hpair : lineOfPair cfg A = P := by
    apply lineOfPair_eq_of_mem_of_direction_finrank_one cfg A P
    · intro x hx
      have hxGeom : cfg x ∈ lineOfPair cfg A :=
        mem_lineSupport.mp (pair_subset_lineSupport cfg A hx)
      rw [hA] at hxGeom
      apply mem_perpBisector_iff_dist_eq.mpr
      exact (EuclideanGeometry.dist_reflection_eq_of_mem
        L.1 hxGeom (cfg p)).symm
    · exact hPfin
  exact hA.symm.trans hpair

/-- Exact pointwise dictionary for a line missing the inversion pivot. -/
theorem pivotInversion_mem_invertedDeterminedLineCircle_iff
    (cfg : Configuration alpha) (p : alpha) (L : DeterminedLine cfg)
    (hp : p ∉ lineSupport cfg L) (q : AwayFrom p) :
    pivotInversion cfg p q ∈
        ((invertedDeterminedLineCircle cfg p L hp).1 : Set Point2) ↔
      q.1 ∈ lineSupport cfg L := by
  classical
  letI : Nonempty L.1 := determinedLineNonempty cfg L
  let y : Point2 := EuclideanGeometry.reflection L.1 (cfg p)
  have hpGeom : cfg p ∉ L.1 := by
    intro h
    exact hp (mem_lineSupport.mpr h)
  have hy : y ≠ cfg p := by
    intro h
    exact hpGeom ((EuclideanGeometry.reflection_eq_self_iff
      (s := L.1) (cfg p)).mp h)
  have hline := determinedLine_eq_perpBisector_reflection_of_not_mem
    cfg p L hp
  have himage :
      EuclideanGeometry.inversion (cfg p) 1 '' (L.1 : Set Point2) =
        (((invertedDeterminedLineCircle cfg p L hp).1 : Set Point2) \
          {cfg p}) := by
    rw [hline]
    simpa [invertedDeterminedLineCircle, y] using
      (EuclideanGeometry.image_inversion_perpBisector
        (c := cfg p) (R := (1 : ℝ)) one_ne_zero hy)
  have hqne : pivotInversion cfg p q ≠ cfg p := by
    intro h
    have hqp : cfg q.1 = cfg p :=
      (EuclideanGeometry.inversion_eq_center one_ne_zero).mp (by
        simpa [pivotInversion] using h)
    exact q.2 (cfg.injective hqp)
  constructor
  · intro hq
    have hdiff : pivotInversion cfg p q ∈
        (((invertedDeterminedLineCircle cfg p L hp).1 : Set Point2) \
          {cfg p}) := ⟨hq, by simpa using hqne⟩
    rw [← himage] at hdiff
    obtain ⟨z, hzL, hz⟩ := hdiff
    have hzq : z = cfg q.1 := by
      apply EuclideanGeometry.inversion_injective (cfg p) one_ne_zero
      simpa [pivotInversion] using hz
    apply mem_lineSupport.mpr
    simpa [hzq] using hzL
  · intro hq
    exact inversion_mem_invertedDeterminedLineCircle cfg p L hp q.1 hq

/-- The actual determined circle obtained by inverting a determined line
which misses the pivot. -/
noncomputable def pivotInversionDeterminedCircleOfAwayLine
    (cfg : Configuration alpha) (p : alpha) (L : DeterminedLine cfg)
    (hp : p ∉ lineSupport cfg L)
    (hthree : 3 ≤ (lineSupport cfg L).card) :
    DeterminedCircle (pivotInversion cfg p) := by
  have haway : 3 ≤ (awaySupport p (lineSupport cfg L)).card := by
    rw [card_awaySupport_of_not_mem p (lineSupport cfg L) hp]
    exact hthree
  let Aset := Classical.choose (Finset.exists_subset_card_eq haway)
  have hAspec := Classical.choose_spec (Finset.exists_subset_card_eq haway)
  have hAsub : Aset ⊆ awaySupport p (lineSupport cfg L) := hAspec.1
  have hAcard : Aset.card = 3 := hAspec.2
  let A : KSubset (AwayFrom p) 3 := ⟨Aset, hAcard⟩
  have hAnoncol : IsNoncollinear (pivotInversion cfg p) A.1 := by
    by_contra hcol
    apply not_triple_subset_circle_of_collinear
      (pivotInversion cfg p) A hcol
      (invertedDeterminedLineCircle cfg p L hp)
    intro q hq
    apply mem_circleTrace.mpr
    exact (pivotInversion_mem_invertedDeterminedLineCircle_iff
      cfg p L hp q).2 (mem_awaySupport.mp (hAsub hq))
  let t := attachedNoncollinearTriple (pivotInversion cfg p) A hAnoncol
  refine ⟨invertedDeterminedLineCircle cfg p L hp, ?_⟩
  apply (mem_determinedCircles_iff (pivotInversion cfg p)
    (invertedDeterminedLineCircle cfg p L hp)).2
  refine ⟨t, ?_⟩
  intro q hq
  exact (pivotInversion_mem_invertedDeterminedLineCircle_iff
    cfg p L hp q).2 (mem_awaySupport.mp (hAsub hq))

/-- The selected trace of the inverted line-circle is exactly the original
line support, with the pivot proof removed. -/
theorem circleTrace_pivotInversionDeterminedCircleOfAwayLine
    (cfg : Configuration alpha) (p : alpha) (L : DeterminedLine cfg)
    (hp : p ∉ lineSupport cfg L)
    (hthree : 3 ≤ (lineSupport cfg L).card) :
    circleTrace (pivotInversion cfg p)
        (pivotInversionDeterminedCircleOfAwayLine cfg p L hp hthree).1 =
      awaySupport p (lineSupport cfg L) := by
  ext q
  rw [mem_circleTrace, mem_awaySupport]
  change pivotInversion cfg p q ∈
      ((invertedDeterminedLineCircle cfg p L hp).1 : Set Point2) ↔ _
  exact pivotInversion_mem_invertedDeterminedLineCircle_iff cfg p L hp q

/-- In particular a selected six-line becomes a selected six-circle. -/
theorem card_circleTrace_pivotInversionDeterminedCircleOfAwayLine
    (cfg : Configuration alpha) (p : alpha) (L : DeterminedLine cfg)
    (hp : p ∉ lineSupport cfg L)
    (hthree : 3 ≤ (lineSupport cfg L).card) :
    (circleTrace (pivotInversion cfg p)
      (pivotInversionDeterminedCircleOfAwayLine cfg p L hp hthree).1).card =
        (lineSupport cfg L).card := by
  rw [circleTrace_pivotInversionDeterminedCircleOfAwayLine,
    card_awaySupport_of_not_mem p (lineSupport cfg L) hp]

/-! ## The fan-circle / marked-line dictionary -/

private theorem circleTrace_circleBlockEquiv_eq_support
    (cfg : Configuration alpha)
    (b : {b : GeometricBlock cfg // geometricBlockKind b = .circle}) :
    circleTrace cfg ((circleBlockEquiv cfg) b).1 =
      geometricBlockSupport cfg b.1 := by
  rcases b with ⟨b, hb⟩
  cases b with
  | inl L => cases hb
  | inr c => rfl

/-- A circle in the rich-line fan, retained as an actual determined circle. -/
noncomputable def pivotFanDeterminedCircle
    (cfg : Configuration alpha) (L : DeterminedLine cfg)
    (p : BlockOutsider (blockSystem cfg) (Sum.inl L))
    (c : {c : GeometricBlock cfg //
      c ∈ circlePencil (blockSystem cfg) (Sum.inl L) p}) :
    DeterminedCircle cfg :=
  circleBlockEquiv cfg
    ⟨c.1, circlePencil_kind (blockSystem cfg) (Sum.inl L) p c.2⟩

@[simp] theorem circleTrace_pivotFanDeterminedCircle
    (cfg : Configuration alpha) (L : DeterminedLine cfg)
    (p : BlockOutsider (blockSystem cfg) (Sum.inl L))
    (c : {c : GeometricBlock cfg //
      c ∈ circlePencil (blockSystem cfg) (Sum.inl L) p}) :
    circleTrace cfg (pivotFanDeterminedCircle cfg L p c).1 =
      geometricBlockSupport cfg c.1 := by
  exact circleTrace_circleBlockEquiv_eq_support cfg _

/-- The same fan circle, bundled with its incidence at the pivot. -/
noncomputable def pivotFanCircleThrough
    (cfg : Configuration alpha) (L : DeterminedLine cfg)
    (p : BlockOutsider (blockSystem cfg) (Sum.inl L))
    (c : {c : GeometricBlock cfg //
      c ∈ circlePencil (blockSystem cfg) (Sum.inl L) p}) :
    ↥(circlesThrough cfg p.1) := by
  refine ⟨pivotFanDeterminedCircle cfg L p c, ?_⟩
  apply mem_circlesThrough.mpr
  rw [circleTrace_pivotFanDeterminedCircle]
  exact outsider_mem_support_of_mem_circlePencil
    (blockSystem cfg) (Sum.inl L) p c.2

/-- Invert a fan circle through `p` to its determined line. -/
noncomputable def pivotFanCircleLine
    (cfg : Configuration alpha) (L : DeterminedLine cfg)
    (p : BlockOutsider (blockSystem cfg) (Sum.inl L))
    (c : {c : GeometricBlock cfg //
      c ∈ circlePencil (blockSystem cfg) (Sum.inl L) p}) :
    DeterminedLine (pivotInversion cfg p.1) :=
  circleToPivotLine cfg p.1 (pivotFanCircleThrough cfg L p c)

/-- Every inverted fan circle is a marked two-chord line of the inverted
base circle. -/
theorem pivotFanCircleLine_inter_baseCircle_card
    (cfg : Configuration alpha) (L : DeterminedLine cfg)
    (p : BlockOutsider (blockSystem cfg) (Sum.inl L))
    (hthree : 3 ≤ (lineSupport cfg L).card)
    (c : {c : GeometricBlock cfg //
      c ∈ circlePencil (blockSystem cfg) (Sum.inl L) p}) :
    (lineSupport (pivotInversion cfg p.1)
        (pivotFanCircleLine cfg L p c) ∩
      circleTrace (pivotInversion cfg p.1)
        (pivotInversionDeterminedCircleOfAwayLine cfg p.1 L
          (mem_blockOutsiders.mp p.2) hthree).1).card = 2 := by
  classical
  let S := blockSystem cfg
  have hp : p.1 ∉ lineSupport cfg L := mem_blockOutsiders.mp p.2
  have hfan :
      circleTrace cfg (pivotFanCircleThrough cfg L p c).1.1 =
        geometricBlockSupport cfg c.1 := by
    change circleTrace cfg (pivotFanDeterminedCircle cfg L p c).1 = _
    exact circleTrace_pivotFanDeterminedCircle cfg L p c
  have heq :
      lineSupport (pivotInversion cfg p.1)
          (pivotFanCircleLine cfg L p c) ∩
        circleTrace (pivotInversion cfg p.1)
          (pivotInversionDeterminedCircleOfAwayLine cfg p.1 L hp hthree).1 =
        awaySupport p.1
          (geometricBlockSupport cfg c.1 ∩ lineSupport cfg L) := by
    ext q
    rw [pivotFanCircleLine, lineSupport_circleToPivotLine,
      circleTrace_pivotInversionDeterminedCircleOfAwayLine]
    simp only [Finset.mem_inter, mem_awayCircleSupport, mem_awaySupport,
      hfan]
  rw [heq, card_awaySupport_of_not_mem]
  · obtain ⟨u, _hu, howner⟩ := mem_circlePencil.mp c.2
    change (S.support c.1 ∩ S.support (Sum.inl L)).card = 2
    rw [← howner, pencilOwner_inter_base]
    exact (Finset.mem_powersetCard.mp u.2).2
  · intro hpInter
    exact hp (Finset.mem_inter.mp hpInter).2

/-- The remaining outsider labels on an inverted fan line are counted by
the fan degree minus the pivot itself. -/
theorem pivotFanCircleLine_outsider_card
    (cfg : Configuration alpha) (L : DeterminedLine cfg)
    (p : BlockOutsider (blockSystem cfg) (Sum.inl L))
    (c : {c : GeometricBlock cfg //
      c ∈ circlePencil (blockSystem cfg) (Sum.inl L) p}) :
    (lineSupport (pivotInversion cfg p.1)
        (pivotFanCircleLine cfg L p c) ∩
      awaySupport p.1
        (blockOutsiders (blockSystem cfg) (Sum.inl L))).card =
      nineFiveFanDegree (blockSystem cfg) (Sum.inl L) c.1 - 1 := by
  classical
  let S := blockSystem cfg
  let O := blockOutsiders S (Sum.inl L)
  have hfan :
      circleTrace cfg (pivotFanCircleThrough cfg L p c).1.1 =
        geometricBlockSupport cfg c.1 := by
    change circleTrace cfg (pivotFanDeterminedCircle cfg L p c).1 = _
    exact circleTrace_pivotFanDeterminedCircle cfg L p c
  have heq :
      lineSupport (pivotInversion cfg p.1)
          (pivotFanCircleLine cfg L p c) ∩ awaySupport p.1 O =
        awaySupport p.1 (S.support c.1 \ S.support (Sum.inl L)) := by
    ext q
    rw [pivotFanCircleLine, lineSupport_circleToPivotLine]
    simp only [Finset.mem_inter, mem_awayCircleSupport, mem_awaySupport,
      hfan, O, mem_blockOutsiders,
      Finset.mem_sdiff, Finset.mem_univ, true_and]
    simpa [S, blockSystem, geometricBlockSystem]
  have hpOutside : p.1 ∈ S.support c.1 \ S.support (Sum.inl L) := by
    exact Finset.mem_sdiff.mpr
      ⟨outsider_mem_support_of_mem_circlePencil S (Sum.inl L) p c.2,
        mem_blockOutsiders.mp p.2⟩
  have hcU : c.1 ∈ nineFiveFanUnion S (Sum.inl L) := by
    letI : DecidableEq (GeometricBlock cfg) := Classical.decEq _
    rw [nineFiveFanUnion]
    exact Finset.mem_biUnion.mpr ⟨p, Finset.mem_univ p, c.2⟩
  rw [heq, card_awaySupport p.1 _ hpOutside,
    nineFiveFanDegree_eq_outside_card S (Sum.inl L) c.1 hcU]

/-- Distinct fan circles remain distinct after pivot inversion. -/
theorem pivotFanCircleLine_injective
    (cfg : Configuration alpha) (L : DeterminedLine cfg)
    (p : BlockOutsider (blockSystem cfg) (Sum.inl L)) :
    Function.Injective (pivotFanCircleLine cfg L p) := by
  intro c d hcd
  have hthrough : pivotFanCircleThrough cfg L p c =
      pivotFanCircleThrough cfg L p d :=
    circleToPivotLine_injective cfg p.1 hcd
  have hcircles : pivotFanDeterminedCircle cfg L p c =
      pivotFanDeterminedCircle cfg L p d := congrArg Subtype.val hthrough
  have htagged := (circleBlockEquiv cfg).injective hcircles
  apply Subtype.ext
  exact congrArg
    (fun z : {b : GeometricBlock cfg // geometricBlockKind b = .circle} => z.1)
    htagged

/-- The excess fan incidence at one outsider pivot.  A fan circle counted
with `d` outsiders contributes the `d - 1` labels different from the pivot. -/
noncomputable def fifteenSixLinePivotFanExcess
    (cfg : Configuration alpha) (L : DeterminedLine cfg)
    (p : BlockOutsider (blockSystem cfg) (Sum.inl L)) : Nat :=
  ∑ c : {c : GeometricBlock cfg //
      c ∈ circlePencil (blockSystem cfg) (Sum.inl L) p},
    (nineFiveFanDegree (blockSystem cfg) (Sum.inl L) c.1 - 1)

/-- Pivot inversion injects the complete local fan excess into the marked
line incidence of the inverted selected line-circle. -/
theorem fifteenSixLinePivotFanExcess_le_sixConicLineIncidence
    (cfg : Configuration alpha) (L : DeterminedLine cfg)
    (p : BlockOutsider (blockSystem cfg) (Sum.inl L))
    (hthree : 3 ≤ (lineSupport cfg L).card) :
    fifteenSixLinePivotFanExcess cfg L p ≤
      sixConicLineIncidence (pivotInversion cfg p.1)
        (pivotInversionDeterminedCircleOfAwayLine cfg p.1 L
          (mem_blockOutsiders.mp p.2) hthree)
        (awaySupport p.1
          (blockOutsiders (blockSystem cfg) (Sum.inl L))) := by
  classical
  let C := {c : GeometricBlock cfg //
    c ∈ circlePencil (blockSystem cfg) (Sum.inl L) p}
  let f : C → DeterminedLine (pivotInversion cfg p.1) :=
    pivotFanCircleLine cfg L p
  let X := awaySupport p.1
    (blockOutsiders (blockSystem cfg) (Sum.inl L))
  let gamma := pivotInversionDeterminedCircleOfAwayLine cfg p.1 L
    (mem_blockOutsiders.mp p.2) hthree
  let row : DeterminedLine (pivotInversion cfg p.1) → Nat := fun K =>
    (lineSupport (pivotInversion cfg p.1) K ∩ X).card
  let markedRow : DeterminedLine (pivotInversion cfg p.1) → Nat := fun K =>
    if (lineSupport (pivotInversion cfg p.1) K ∩
          circleTrace (pivotInversion cfg p.1) gamma.1).card = 2 then
      row K else 0
  let T := (Finset.univ : Finset C).image f
  have himage : (∑ K ∈ T, row K) = ∑ c : C, row (f c) := by
    dsimp only [T]
    rw [Finset.sum_image]
    intro c _hc d _hd hcd
    exact pivotFanCircleLine_injective cfg L p hcd
  have hmarked (K : DeterminedLine (pivotInversion cfg p.1)) (hKT : K ∈ T) :
      markedRow K = row K := by
    obtain ⟨c, _hc, rfl⟩ := Finset.mem_image.mp hKT
    rw [show markedRow (f c) =
        if (lineSupport (pivotInversion cfg p.1) (f c) ∩
            circleTrace (pivotInversion cfg p.1) gamma.1).card = 2 then
          row (f c) else 0 by rfl,
      if_pos]
    exact pivotFanCircleLine_inter_baseCircle_card cfg L p hthree c
  change (∑ c : C,
      (nineFiveFanDegree (blockSystem cfg) (Sum.inl L) c.1 - 1)) ≤ _
  change _ ≤ ∑ K : DeterminedLine (pivotInversion cfg p.1), markedRow K
  calc
    (∑ c : C,
        (nineFiveFanDegree (blockSystem cfg) (Sum.inl L) c.1 - 1)) =
        ∑ c : C, row (f c) := by
      apply Fintype.sum_congr
        (fun c : C =>
          nineFiveFanDegree (blockSystem cfg) (Sum.inl L) c.1 - 1)
        (fun c : C => row (f c))
      intro c
      exact (pivotFanCircleLine_outsider_card cfg L p c).symm
    _ = ∑ K ∈ T, row K := himage.symm
    _ = ∑ K ∈ T, markedRow K := by
      apply Finset.sum_congr rfl
      intro K hKT
      exact (hmarked K hKT).symm
    _ ≤ ∑ K ∈ (Finset.univ :
        Finset (DeterminedLine (pivotInversion cfg p.1))), markedRow K :=
      Finset.sum_le_sum_of_subset (Finset.subset_univ T)
    _ = ∑ K : DeterminedLine (pivotInversion cfg p.1), markedRow K := by
      simp

/-- A single outsider of a selected six-circle lies on at most three
determined lines which meet the circle in exactly two selected labels. -/
theorem sixConic_markedLineAt_card_le_three
    (cfg : Configuration alpha) (gamma : DeterminedCircle cfg)
    (hgamma : (circleTrace cfg gamma.1).card = 6)
    (x : alpha) (hx : x ∉ circleTrace cfg gamma.1) :
    Fintype.card (SixConicMarkedLineAt cfg gamma x) ≤ 3 := by
  obtain ⟨o, hoPoint, hoGamma, hoLines⟩ :=
    exists_external_point_avoiding_circle_and_determinedLines cfg gamma
  rw [card_sixConicMarkedLineAt_eq_radialPairWeight
    cfg gamma hgamma o hoPoint hoGamma hoLines x]
  apply sixConicPairWeight_le_three
    (card_circleTrace_inversionAugmentationGamma
      cfg gamma hgamma o hoPoint hoGamma)
    (by simp)
  rw [circleTrace_inversionAugmentationGamma, Finset.disjoint_left]
  intro z hzEdge hzGamma
  simp only [Finset.mem_insert, Finset.mem_singleton] at hzEdge
  rcases hzEdge with rfl | rfl
  · simp at hzGamma
  · have hxGamma : x ∈ circleTrace cfg gamma.1 := by
      simpa using hzGamma
    exact hx hxGamma

/-- Eight labels disjoint from a selected six-circle carry at most twenty
incidences with determined two-chord lines.  Indeed a fibre has size at most
three, while five fibres of size three would have incidence fifteen on a
five-subset, contradicting `sixConic_line_incidence_le_fourteen`. -/
theorem sixConic_line_incidence_le_twenty_of_card_eight
    (cfg : Configuration alpha) (gamma : DeterminedCircle cfg)
    (hgamma : (circleTrace cfg gamma.1).card = 6)
    (X : Finset alpha) (hX : X.card = 8)
    (hdisjoint : Disjoint (circleTrace cfg gamma.1) X) :
    sixConicLineIncidence cfg gamma X ≤ 20 := by
  classical
  let q : alpha → Nat := fun x =>
    Fintype.card (SixConicMarkedLineAt cfg gamma x)
  let F : Finset alpha := X.filter fun x => q x = 3
  have hq (x : alpha) (hxX : x ∈ X) : q x ≤ 3 := by
    apply sixConic_markedLineAt_card_le_three cfg gamma hgamma x
    intro hxGamma
    exact (Finset.disjoint_left.mp hdisjoint) hxGamma hxX
  have hFcard : F.card ≤ 4 := by
    by_contra hnot
    have hfive : 5 ≤ F.card := by omega
    obtain ⟨Y, hYF, hYcard⟩ := Finset.exists_subset_card_eq hfive
    have hYX : Y ⊆ X := hYF.trans (Finset.filter_subset _ _)
    have hdisjointY : Disjoint (circleTrace cfg gamma.1) Y := by
      rw [Finset.disjoint_left] at hdisjoint ⊢
      intro z hzGamma hzY
      exact hdisjoint hzGamma (hYX hzY)
    have hlocal := sixConic_line_incidence_le_fourteen
      cfg gamma hgamma Y hYcard hdisjointY
    rw [sixConicLineIncidence_eq_sum_card_markedLineAt] at hlocal
    have hsum : (∑ x ∈ Y, q x) = 15 := by
      calc
        (∑ x ∈ Y, q x) = ∑ _x ∈ Y, 3 := by
          apply Finset.sum_congr rfl
          intro x hxY
          exact (Finset.mem_filter.mp (hYF hxY)).2
        _ = 15 := by simp [hYcard]
    change (∑ x ∈ Y, q x) ≤ 14 at hlocal
    omega
  have hpoint (x : alpha) (hxX : x ∈ X) :
      q x ≤ 2 + if q x = 3 then 1 else 0 := by
    have hxq := hq x hxX
    by_cases hfull : q x = 3
    · simp [hfull]
    · simp [hfull]
      omega
  have hsumLe :
      (∑ x ∈ X, q x) ≤
        ∑ x ∈ X, (2 + if q x = 3 then 1 else 0) := by
    exact Finset.sum_le_sum fun x hxX => hpoint x hxX
  have hindicator :
      (∑ x ∈ X, if q x = 3 then 1 else 0) = F.card := by
    rw [← Finset.sum_filter]
    simp [F]
  rw [sixConicLineIncidence_eq_sum_card_markedLineAt]
  change (∑ x ∈ X, q x) ≤ 20
  simp only [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul] at hsumLe
  rw [hindicator, hX] at hsumLe
  omega

/-- For a six-line in a fifteen-point configuration, each outsider-pivot fan
has excess at most twenty. -/
theorem fifteenSixLinePivotFanExcess_le_twenty
    (cfg : Configuration alpha) (h15 : Fintype.card alpha = 15)
    (L : DeterminedLine cfg) (hLcard : (lineSupport cfg L).card = 6)
    (p : BlockOutsider (blockSystem cfg) (Sum.inl L)) :
    fifteenSixLinePivotFanExcess cfg L p ≤ 20 := by
  let gamma := pivotInversionDeterminedCircleOfAwayLine cfg p.1 L
    (mem_blockOutsiders.mp p.2) (by omega)
  let X := awaySupport p.1
    (blockOutsiders (blockSystem cfg) (Sum.inl L))
  have hgamma :
      (circleTrace (pivotInversion cfg p.1) gamma.1).card = 6 := by
    rw [card_circleTrace_pivotInversionDeterminedCircleOfAwayLine]
    exact hLcard
  have hOcard :
      (blockOutsiders (blockSystem cfg) (Sum.inl L)).card = 9 := by
    rw [card_blockOutsiders, h15]
    change 15 - (lineSupport cfg L).card = 9
    omega
  have hX : X.card = 8 := by
    rw [card_awaySupport p.1 _ p.2, hOcard]
  have hdisjoint :
      Disjoint (circleTrace (pivotInversion cfg p.1) gamma.1) X := by
    rw [circleTrace_pivotInversionDeterminedCircleOfAwayLine]
    rw [Finset.disjoint_left]
    intro q hqBase hqOutside
    have hbase : q.1 ∈ lineSupport cfg L := mem_awaySupport.mp hqBase
    have hout : q.1 ∈
        blockOutsiders (blockSystem cfg) (Sum.inl L) :=
      mem_awaySupport.mp hqOutside
    exact (mem_blockOutsiders.mp hout) hbase
  exact (fifteenSixLinePivotFanExcess_le_sixConicLineIncidence
    cfg L p (by omega)).trans
      (sixConic_line_incidence_le_twenty_of_card_eight
        (pivotInversion cfg p.1) gamma hgamma X hX hdisjoint)

/-- Fubini for the pivot excess: a fan block of degree `d` contributes
`d - 1` at each of its `d` pivots, hence twice its pair weight. -/
theorem sum_fifteenSixLinePivotFanExcess_eq_two_mul_pairMoment
    (cfg : Configuration alpha) (L : DeterminedLine cfg) :
    (∑ p : BlockOutsider (blockSystem cfg) (Sum.inl L),
        fifteenSixLinePivotFanExcess cfg L p) =
      2 * nineFivePairMoment (blockSystem cfg) (Sum.inl L) := by
  classical
  letI : DecidableEq (GeometricBlock cfg) := Classical.decEq _
  let S := blockSystem cfg
  let g : GeometricBlock cfg := Sum.inl L
  let I : Finset (BlockOutsider S g) := Finset.univ
  let F : BlockOutsider S g → Finset (GeometricBlock cfg) :=
    circlePencil S g
  let U : Finset (GeometricBlock cfg) := I.biUnion F
  let d : GeometricBlock cfg → Nat := nineFiveFanDegree S g
  unfold fifteenSixLinePivotFanExcess nineFivePairMoment
  suffices hcore : (∑ p ∈ I, ∑ c : ↥(F p), (d c.1 - 1)) =
      2 * ∑ c ∈ U, Nat.choose (d c) 2 by
    simpa [S, g, I, F, U, d, nineFiveFanUnion] using hcore
  calc
    (∑ p ∈ I, ∑ c : ↥(F p), (d c.1 - 1)) =
        ∑ p ∈ I, ∑ c ∈ U,
          if c ∈ F p then (d c - 1) else 0 := by
      apply Finset.sum_congr rfl
      intro p hp
      have hfilter : U.filter (fun c => c ∈ F p) = F p := by
        ext c
        constructor
        · intro hc
          exact (Finset.mem_filter.mp hc).2
        · intro hc
          apply Finset.mem_filter.mpr
          exact ⟨Finset.mem_biUnion.mpr ⟨p, hp, hc⟩, hc⟩
      calc
        (∑ c : ↥(F p), (d c.1 - 1)) =
            ∑ c ∈ F p, (d c - 1) := by
          exact Finset.sum_coe_sort (F p) (fun c => d c - 1)
        _ = ∑ c ∈ U, if c ∈ F p then (d c - 1) else 0 := by
          rw [← Finset.sum_filter, hfilter]
    _ = ∑ c ∈ U, ∑ p ∈ I,
          if c ∈ F p then (d c - 1) else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ c ∈ U, d c * (d c - 1) := by
      apply Finset.sum_congr rfl
      intro c _hc
      calc
        (∑ p ∈ I, if c ∈ F p then (d c - 1) else 0) =
            ∑ p ∈ I.filter (fun p => c ∈ F p), (d c - 1) := by
          rw [Finset.sum_filter]
        _ = (I.filter (fun p => c ∈ F p)).card * (d c - 1) := by
          simp
        _ = d c * (d c - 1) := by rfl
    _ = ∑ c ∈ U, 2 * Nat.choose (d c) 2 := by
      apply Finset.sum_congr rfl
      intro c _hc
      exact (two_mul_choose_two (d c)).symm
    _ = 2 * ∑ c ∈ U, Nat.choose (d c) 2 := by
      rw [Finset.mul_sum]

/-- The nine pivot bounds `J <= 20` give the sharp fan pair-moment bound
needed in the fifteen-point six-line case. -/
theorem nineFivePairMoment_le_ninety_of_fifteen_six_line
    (cfg : Configuration alpha) (h15 : Fintype.card alpha = 15)
    (L : DeterminedLine cfg) (hLcard : (lineSupport cfg L).card = 6) :
    nineFivePairMoment (blockSystem cfg) (Sum.inl L) ≤ 90 := by
  have hOcard :
      (blockOutsiders (blockSystem cfg) (Sum.inl L)).card = 9 := by
    rw [card_blockOutsiders, h15]
    change 15 - (lineSupport cfg L).card = 9
    omega
  have hsumLe :
      (∑ p : BlockOutsider (blockSystem cfg) (Sum.inl L),
          fifteenSixLinePivotFanExcess cfg L p) ≤
        ∑ _p : BlockOutsider (blockSystem cfg) (Sum.inl L), 20 := by
    exact Finset.sum_le_sum fun p _hp =>
      fifteenSixLinePivotFanExcess_le_twenty cfg h15 L hLcard p
  rw [sum_fifteenSixLinePivotFanExcess_eq_two_mul_pairMoment] at hsumLe
  simp only [Finset.sum_const, nsmul_eq_mul, Finset.card_univ] at hsumLe
  rw [Fintype.card_coe, hOcard] at hsumLe
  omega

/-! ## A shorter functional endpoint -/

/-- In a fifteen-point finite-window counterexample every nontrivial block
has size at most six: a size-seven block is eliminated by the already closed
line and circle endpoints. -/
private theorem blockSizeCap_six_of_fifteen_finiteWindow
    (Mel : RealPlaneMelchiorPrinciple.{u})
    {cfg : Configuration alpha} (R : FiniteWindowRichBlockResidual cfg)
    (hadm : Admissible cfg)
    (h15 : Fintype.card alpha = 15)
    (hcount : Erdos506.V4.circleCount cfg <
      Erdos506.v1UniformTarget (Fintype.card alpha)) :
    BlockSizeCap (blockSystem cfg) 6 := by
  let S := blockSystem cfg
  have hhalf := halfBlockCap_of_circleCount_lt_v1UniformTarget
    cfg hadm (by omega) hcount
  have hcapSeven : BlockSizeCap S 7 := by
    rw [h15] at hhalf
    norm_num at hhalf
    exact hhalf
  intro b hbThree
  have hbLe : (S.support b).card ≤ 7 := hcapSeven b hbThree
  by_contra hbNot
  have hbNot' : ¬ (S.support b).card ≤ 6 := by
    simpa only [S] using hbNot
  have hbSeven : (S.support b).card = 7 := by omega
  have hbSevenGeom : (geometricBlockSupport cfg b).card = 7 := by
    simpa [S, blockSystem, geometricBlockSystem] using hbSeven
  let R7 : FiniteWindowRichBlockResidual cfg :=
    { window_lower := R.window_lower
      window_upper := R.window_upper
      block := b
      nontrivial := by omega
      aboveThreshold := by
        rw [h15, hbSevenGeom]
        norm_num [finiteWindowCapThreshold]
      atMostHalf := by
        rw [h15, hbSevenGeom]
      strictAtLargeEven := by
        intro hlarge
        rcases hlarge with h18 | h20 | h22 <;> omega
      fourteen_size := by intro h14; omega }
  cases hkind : S.kind b with
  | line =>
      exact (R7.line_impossible_of_fifteen_seven hadm
        (by simpa [R7, S] using hkind) h15
        (by simpa [R7] using hbSevenGeom) hcount).elim
  | circle =>
      exact (R7.circle_impossible_of_fifteen_seven Mel hadm
        (by simpa [R7, S] using hkind) h15
        (by simpa [R7] using hbSevenGeom) hcount).elim

/-- The last rich-line residual in the finite Langer window is impossible.

The selected line contributes the strict local functional slack `108`.
Together with the fifteen-point moment rows this forces
`fourteenWeight S D ≥ 138`, whereas the universal two--two capacity is
only `108`. -/
theorem FiniteWindowRichBlockResidual.line_impossible_of_fifteen_six
    (Mel : RealPlaneMelchiorPrinciple.{u})
    {cfg : Configuration alpha} (R : FiniteWindowRichBlockResidual cfg)
    (hadm : Admissible cfg)
    (hline : (blockSystem cfg).kind R.block = .line)
    (h15 : Fintype.card alpha = 15)
    (hsix : (geometricBlockSupport cfg R.block).card = 6)
    (hcount : Erdos506.V4.circleCount cfg <
      Erdos506.v1UniformTarget (Fintype.card alpha)) : False := by
  classical
  let S := blockSystem cfg
  let D := geometricBlockSupport cfg R.block
  let gamma := R.block
  have hcap : BlockSizeCap S 6 := by
    simpa [S] using blockSizeCap_six_of_fifteen_finiteWindow
      Mel R hadm h15 hcount
  have hthree : 3 ≤ Fintype.card alpha := by omega
  have hpivot : ∀ p : alpha, 0 ≤ S.pivotSigma p := by
    intro p
    change 0 ≤ sigma cfg p
    exact sigma_nonneg_of_realPlaneMelchior Mel cfg hadm hthree p
  have hDcard : D.card = 6 := by
    simpa [D, S] using hsix
  have hXcard : (Finset.univ \ D).card = 9 := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ D),
      Finset.card_univ, h15, hDcard]
  have hmomentD : 18 ≤ S.subsetPivotMoment D := by
    have hmoment := S.three_mul_card_le_subsetPivotMoment D
      (fun p _hp => hpivot p)
    rw [hDcard] at hmoment
    norm_num at hmoment ⊢
    exact hmoment
  have hmomentX : 27 ≤ S.subsetPivotMoment (Finset.univ \ D) := by
    have hmoment := S.three_mul_card_le_subsetPivotMoment
      (Finset.univ \ D) (fun p _hp => hpivot p)
    rw [hXcard] at hmoment
    norm_num at hmoment ⊢
    exact hmoment
  have hdefect : S.defectRow ≤ 165 := by
    have hrow := rowD_le_n_mul_n_sub_four_of_realPlaneMelchior
      Mel cfg hadm hthree
    change S.defectRow ≤
      (Fintype.card alpha : Int) * ((Fintype.card alpha : Int) - 4) at hrow
    rw [h15] at hrow
    norm_num at hrow ⊢
    exact hrow
  have hcount84 : Erdos506.V4.circleCount cfg ≤ 84 := by
    rw [h15] at hcount
    norm_num [Erdos506.v1UniformTarget, Nat.choose] at hcount
    omega
  have htotal : S.totalCircleCount ≤ 84 := by
    dsimp only [S]
    rw [totalCircleCount_eq_card_determinedCircle,
      ← Erdos506.V3.circleCount_eq_card_determinedCircle]
    exact hcount84
  have hexpand := sum_fifteenSixBlockFunctional_eq S D h15 hDcard
  have hupper := sum_fourteenSixLineBlockFunctional_add_108_le
    S D gamma hDcard
      (by simpa [gamma, S] using hline) rfl hcap
  have hupper' :
      (∑ b : GeometricBlock cfg,
        fourteenBlockFunctional (S.kind b)
          (fourteenInside S D b) (fourteenOutside S D b)) ≤ 552 := by
    omega
  rw [hexpand] at hupper'
  have hlower : 138 ≤ fourteenWeight S D := by omega
  have hcapacity := fourteenWeight_le_capacity S D
  rw [h15, hDcard] at hcapacity
  norm_num [Nat.choose] at hcapacity ⊢
  omega

/-- Pure arithmetic finish for the `(15,6)` rich-line partition.

`N3,N2,N1` count two-base fan circles with respectively three, two and one
outsider labels; `D` counts outsider-only circles and `E` one-base circles.
The first row is the nine outsider pencils, the second is the strengthened
pair moment supplied by pivot inversion and the preceding `J <= 20` theorem,
and the last two inequalities are the induced nine-point and ordinary-circle
corrections. -/
theorem fifteenSixLine_partition_arithmetic
    (C N3 N2 N1 D E : Nat)
    (hfan : 3 * N3 + 2 * N2 + N1 = 135)
    (hpair : 3 * N3 + N2 ≤ 90)
    (hD : 25 ≤ D)
    (hordinary : 12 ≤ 2 * N1 + E)
    (hpartition : N3 + N2 + N1 + D + E ≤ C) :
    87 ≤ C := by
  omega

end Erdos506.V1
