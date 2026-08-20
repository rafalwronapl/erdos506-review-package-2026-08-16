import Erdos506.Incidence.SixConicActiveSignatureGeometry
import Erdos506.V1.InversionAugmentation
import Erdos506.V3.Construction
import Mathlib.Tactic

/-!
# The six-conic line-incidence bound

This file derives the field-free bound `J ≤ 14`.  The construction adds an
external inversion centre which misses every determined line, inverts the
old configuration, and regards every old two-marked line through an
outsider as a pair-circle through the added point.  Five incidences of
weight three would then give five distinct active signatures, contradicting
`sixConic_activeSignatures_card_le_four`.

The intermediate statements deliberately retain the positive geometric
data: the avoiding centre, the exact augmented trace, and the restricted
line/pair-circle equivalence.  They are useful independently of the final
cardinality argument.
-/

namespace Erdos506.Incidence

open Erdos506.Block
open Erdos506.Block.BlockSystem
open Erdos506.Finite
open Erdos506.V1
open Erdos506.V4
open AffineSubspace
open scoped BigOperators

universe u

/-! ## An external centre avoiding all determined lines -/

private theorem realProjectiveAffineVector_ne_zero (t : ℝ) :
    (![1, t] : RealProjectiveLineVector) ≠ 0 := by
  intro hzero
  have hfirst := congrFun hzero (0 : Fin 2)
  norm_num at hfirst

/-- The ordinary affine chart supplies an explicit infinite family in
`RP¹`. -/
private noncomputable def realProjectiveAffinePoint
    (t : ℝ) : RealProjectiveOnePoint :=
  Projectivization.mk ℝ (![1, t] : RealProjectiveLineVector)
    (realProjectiveAffineVector_ne_zero t)

private theorem realProjectiveAffinePoint_injective :
    Function.Injective realProjectiveAffinePoint := by
  intro s t hst
  have hbracket :=
    (realProjective_mk_eq_mk_iff_bracket_eq_zero
      (realProjectiveAffineVector_ne_zero s)
      (realProjectiveAffineVector_ne_zero t)).mp hst
  simp [realProjectiveBracket] at hbracket
  linarith

private noncomputable instance : Infinite RealProjectiveOnePoint :=
  Infinite.of_injective realProjectiveAffinePoint
    realProjectiveAffinePoint_injective

private theorem properCircleProjectiveParam_preimage_affineLine_finite
    (c : ProperCircle) (L : AffineSubspace ℝ Point2)
    (hL : Module.finrank ℝ L.direction = 1) :
    {P : RealProjectiveOnePoint | properCircleProjectiveParam c P ∈ L}.Finite := by
  classical
  let S : Set RealProjectiveOnePoint :=
    {P | properCircleProjectiveParam c P ∈ L}
  by_contra hfinite
  have hinfinite : S.Infinite := by simpa [S] using hfinite
  obtain ⟨P, hP⟩ := hinfinite.nonempty
  obtain ⟨Q, hQ, hQP⟩ := hinfinite.exists_notMem_finset {P}
  obtain ⟨R, hR, hRPQ⟩ := hinfinite.exists_notMem_finset {P, Q}
  have hQP' : Q ≠ P := by simpa using hQP
  have hRne : R ≠ P ∧ R ≠ Q := by
    simpa only [Finset.mem_insert, Finset.mem_singleton, not_or] using hRPQ
  have hPQ : P ≠ Q := hQP'.symm
  have hPR : P ≠ R := by
    exact hRne.1.symm
  have hQR : Q ≠ R := by
    exact hRne.2.symm
  have hPmem : properCircleProjectiveParam c P ∈ L := hP
  have hQmem : properCircleProjectiveParam c Q ∈ L := hQ
  have hRmem : properCircleProjectiveParam c R ∈ L := hR
  have hcollinearL : Collinear ℝ (L : Set Point2) := by
    rw [collinear_iff_finrank_le_one,
      ← AffineSubspace.direction_eq_vectorSpan, hL]
  have hsubset :
      ({properCircleProjectiveParam c P,
          properCircleProjectiveParam c Q,
          properCircleProjectiveParam c R} : Set Point2) ⊆ L := by
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl | rfl
    · exact hPmem
    · exact hQmem
    · exact hRmem
  exact Erdos506.V3.not_collinear_three_distinct_on_sphere
    (properCircleProjectiveParam_mem c P)
    (properCircleProjectiveParam_mem c Q)
    (properCircleProjectiveParam_mem c R)
    ((properCircleProjectiveParam_injective c).ne hPQ)
    ((properCircleProjectiveParam_injective c).ne hPR)
    ((properCircleProjectiveParam_injective c).ne hQR)
    (hcollinearL.subset hsubset)

/-- There is an external inversion centre which misses the selected circle
and every determined affine line.  The auxiliary concentric circle makes
the avoidance set a finite subset of `RP¹`. -/
theorem exists_external_point_avoiding_circle_and_determinedLines
    {α : Type u} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (gamma : Erdos506.V1.DeterminedCircle cfg) :
    ∃ o : Point2,
      o ∉ pointSet cfg ∧
      o ∉ (gamma.1.1 : Set Point2) ∧
      ∀ L : DeterminedLine cfg, o ∉ (L.1 : Set Point2) := by
  classical
  let aux : ProperCircle :=
    ⟨⟨gamma.1.1.center, gamma.1.1.radius / 2⟩,
      div_pos gamma.1.2 (by norm_num)⟩
  let param : RealProjectiveOnePoint → Point2 :=
    properCircleProjectiveParam aux
  let selected : Finset Point2 := Finset.univ.image cfg
  have hselected : ((selected : Finset Point2) : Set Point2) = pointSet cfg := by
    ext z
    simp [selected, pointSet]
  have hselectedFinite : (pointSet cfg).Finite := by
    rw [← hselected]
    exact selected.finite_toSet
  have hpointBad : (param ⁻¹' pointSet cfg).Finite := by
    exact Set.Finite.preimage
      (properCircleProjectiveParam_injective aux).injOn hselectedFinite
  have hlineBad :
      (⋃ L : DeterminedLine cfg,
        param ⁻¹' (L.1 : Set Point2)).Finite := by
    apply Set.finite_iUnion
    intro L
    exact properCircleProjectiveParam_preimage_affineLine_finite
      aux L.1 L.direction_finrank
  have hbad :
      (param ⁻¹' pointSet cfg ∪
        ⋃ L : DeterminedLine cfg,
          param ⁻¹' (L.1 : Set Point2)).Finite :=
    hpointBad.union hlineBad
  obtain ⟨P, hP⟩ := hbad.exists_notMem
  let o : Point2 := param P
  have hoPoint : o ∉ pointSet cfg := by
    intro ho
    apply hP
    exact Set.mem_union_left _ ho
  have hoLines : ∀ L : DeterminedLine cfg, o ∉ (L.1 : Set Point2) := by
    intro L hoL
    apply hP
    apply Set.mem_union_right
    exact Set.mem_iUnion.mpr ⟨L, hoL⟩
  have hoGamma : o ∉ (gamma.1.1 : Set Point2) := by
    intro ho
    have haux := properCircleProjectiveParam_mem aux P
    have hauxDist := EuclideanGeometry.mem_sphere'.mp haux
    have hgammaDist := EuclideanGeometry.mem_sphere'.mp ho
    change dist gamma.1.1.center o = gamma.1.1.radius / 2 at hauxDist
    change dist gamma.1.1.center o = gamma.1.1.radius at hgammaDist
    nlinarith [gamma.1.2]
  exact ⟨o, hoPoint, hoGamma, hoLines⟩

/-! ## The augmented six-circle and its exact trace -/

private theorem isNoncollinear_of_card_three_subset_circle
    {α : Type*} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (c : ProperCircle) (T : Finset α)
    (hT : T.card = 3) (hTc : T ⊆ circleTrace cfg c) :
    IsNoncollinear cfg T := by
  classical
  obtain ⟨a, b, d, hab, had, hbd, rfl⟩ := Finset.card_eq_three.mp hT
  have ha : cfg a ∈ (c.1 : Set Point2) :=
    mem_circleTrace.mp (hTc (by simp))
  have hb : cfg b ∈ (c.1 : Set Point2) :=
    mem_circleTrace.mp (hTc (by simp))
  have hd : cfg d ∈ (c.1 : Set Point2) :=
    mem_circleTrace.mp (hTc (by simp))
  have himage :
      cfg '' (↑({a, b, d} : Finset α) : Set α) =
        ({cfg a, cfg b, cfg d} : Set Point2) := by
    ext z
    simp [eq_comm]
  rw [IsNoncollinear, supportPoints, himage]
  exact Erdos506.V3.not_collinear_three_distinct_on_sphere ha hb hd
    (cfg.injective.ne hab) (cfg.injective.ne had) (cfg.injective.ne hbd)

/-- A fixed three-subset of the selected six-circle. -/
noncomputable def sixConicTraceTriple
    {α : Type u} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (gamma : Erdos506.V1.DeterminedCircle cfg)
    (hgamma : (circleTrace cfg gamma.1).card = 6) : KSubset α 3 := by
  have hthree : 3 ≤ (circleTrace cfg gamma.1).card := by omega
  let T := Classical.choose (Finset.exists_subset_card_eq hthree)
  have hspec := Classical.choose_spec (Finset.exists_subset_card_eq hthree)
  exact ⟨T, hspec.2⟩

theorem sixConicTraceTriple_subset
    {α : Type u} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (gamma : Erdos506.V1.DeterminedCircle cfg)
    (hgamma : (circleTrace cfg gamma.1).card = 6) :
    (sixConicTraceTriple cfg gamma hgamma).1 ⊆ circleTrace cfg gamma.1 := by
  unfold sixConicTraceTriple
  exact (Classical.choose_spec
    (Finset.exists_subset_card_eq (show 3 ≤ (circleTrace cfg gamma.1).card by omega))).1

/-- Relabel a `k`-set by the `some` embedding. -/
def optionSomeKSubset
    {α : Type*} [DecidableEq α] {k : ℕ} (A : KSubset α k) :
    KSubset (Option α) k :=
  ⟨A.1.map Function.Embedding.some, by simp [A.2]⟩

private theorem inversionAugmentation_mem_invertedGamma
    {α : Type u} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (gamma : Erdos506.V1.DeterminedCircle cfg)
    (o : Point2) (hoPoint : o ∉ pointSet cfg)
    (hoGamma : o ∉ (gamma.1.1 : Set Point2))
    {x : α} (hx : x ∈ circleTrace cfg gamma.1) :
    some x ∈ circleTrace (inversionAugmentation cfg o hoPoint)
      (Erdos506.V3.invertedProperCircle o gamma.1 hoGamma) := by
  rw [mem_circleTrace]
  simpa using Erdos506.V3.inversion_mem_invertedProperCircle
    o (cfg x) gamma.1 hoGamma (mem_circleTrace.mp hx)

private theorem inversionAugmentation_traceTriple_noncollinear
    {α : Type u} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (gamma : Erdos506.V1.DeterminedCircle cfg)
    (hgamma : (circleTrace cfg gamma.1).card = 6)
    (o : Point2) (hoPoint : o ∉ pointSet cfg)
    (hoGamma : o ∉ (gamma.1.1 : Set Point2)) :
    IsNoncollinear (inversionAugmentation cfg o hoPoint)
      (optionSomeKSubset (sixConicTraceTriple cfg gamma hgamma)).1 := by
  apply isNoncollinear_of_card_three_subset_circle
    (inversionAugmentation cfg o hoPoint)
    (Erdos506.V3.invertedProperCircle o gamma.1 hoGamma)
    (optionSomeKSubset (sixConicTraceTriple cfg gamma hgamma)).1
    (optionSomeKSubset (sixConicTraceTriple cfg gamma hgamma)).2
  intro z hz
  obtain ⟨x, hx, rfl⟩ := Finset.mem_map.mp hz
  exact inversionAugmentation_mem_invertedGamma
    cfg gamma o hoPoint hoGamma (sixConicTraceTriple_subset cfg gamma hgamma hx)

/-- The determined proper circle in the augmented configuration obtained by
inverting `gamma`. -/
noncomputable def inversionAugmentationGamma
    {α : Type u} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (gamma : Erdos506.V1.DeterminedCircle cfg)
    (hgamma : (circleTrace cfg gamma.1).card = 6)
    (o : Point2) (hoPoint : o ∉ pointSet cfg)
    (hoGamma : o ∉ (gamma.1.1 : Set Point2)) :
    Erdos506.V1.DeterminedCircle (inversionAugmentation cfg o hoPoint) := by
  let aug := inversionAugmentation cfg o hoPoint
  let A := optionSomeKSubset (sixConicTraceTriple cfg gamma hgamma)
  let t := attachedNoncollinearTriple aug A
    (inversionAugmentation_traceTriple_noncollinear
      cfg gamma hgamma o hoPoint hoGamma)
  refine ⟨Erdos506.V3.invertedProperCircle o gamma.1 hoGamma, ?_⟩
  refine (mem_determinedCircles_iff aug
    (Erdos506.V3.invertedProperCircle o gamma.1 hoGamma)).2 ⟨t, ?_⟩
  intro z hz
  obtain ⟨x, hx, rfl⟩ := Finset.mem_map.mp hz
  exact mem_circleTrace.mp
    (inversionAugmentation_mem_invertedGamma
      cfg gamma o hoPoint hoGamma
      (sixConicTraceTriple_subset cfg gamma hgamma hx))

@[simp] theorem inversionAugmentationGamma_coe
    {α : Type u} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (gamma : Erdos506.V1.DeterminedCircle cfg)
    (hgamma : (circleTrace cfg gamma.1).card = 6)
    (o : Point2) (hoPoint : o ∉ pointSet cfg)
    (hoGamma : o ∉ (gamma.1.1 : Set Point2)) :
    (inversionAugmentationGamma cfg gamma hgamma o hoPoint hoGamma).1 =
      Erdos506.V3.invertedProperCircle o gamma.1 hoGamma := rfl

private theorem pivotInversion_inversionAugmentation_some
    {α : Type u} [Fintype α]
    (cfg : Configuration α) (o : Point2) (hoPoint : o ∉ pointSet cfg)
    (x : α) :
    Erdos506.V3.pivotInversion (inversionAugmentation cfg o hoPoint) none
      ⟨some x, Option.some_ne_none x⟩ = cfg x := by
  have hcfg := congrArg
    (fun C : Configuration (Erdos506.V3.AwayFrom (none : Option α)) =>
      C ⟨some x, Option.some_ne_none x⟩)
    (pivotInversion_inversionAugmentation_eq_relabel cfg o hoPoint)
  simpa [relabelConfiguration, awayFromNoneEquiv] using hcfg

private theorem inversionAugmentationGamma_none_not_mem
    {α : Type u} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (gamma : Erdos506.V1.DeterminedCircle cfg)
    (hgamma : (circleTrace cfg gamma.1).card = 6)
    (o : Point2) (hoPoint : o ∉ pointSet cfg)
    (hoGamma : o ∉ (gamma.1.1 : Set Point2)) :
    none ∉ circleTrace (inversionAugmentation cfg o hoPoint)
      (inversionAugmentationGamma cfg gamma hgamma o hoPoint hoGamma).1 := by
  classical
  let aug := inversionAugmentation cfg o hoPoint
  let gammaAug :=
    inversionAugmentationGamma cfg gamma hgamma o hoPoint hoGamma
  let T := sixConicTraceTriple cfg gamma hgamma
  have hTcircle : T.1 ⊆ circleTrace cfg gamma.1 :=
    sixConicTraceTriple_subset cfg gamma hgamma
  have hTnoncol : IsNoncollinear cfg T.1 :=
    isNoncollinear_of_card_three_subset_circle
      cfg gamma.1 T.1 T.2 hTcircle
  intro hnone
  let L : AffineSubspace ℝ Point2 :=
    Erdos506.V3.circlePivotLine aug none gammaAug.1
  have hLfin : Module.finrank ℝ L.direction = 1 := by
    simpa [L] using Erdos506.V3.circlePivotLine_direction_finrank
      aug none gammaAug.1 hnone
  have hTline : supportPoints cfg T.1 ⊆ (L : Set Point2) := by
    rintro z ⟨x, hxT, rfl⟩
    let q : Erdos506.V3.AwayFrom (none : Option α) :=
      ⟨some x, Option.some_ne_none x⟩
    have hxGamma : x ∈ circleTrace cfg gamma.1 := hTcircle hxT
    have hxAug : some x ∈ circleTrace aug gammaAug.1 := by
      exact inversionAugmentation_mem_invertedGamma
        cfg gamma o hoPoint hoGamma hxGamma
    have hqLine : Erdos506.V3.pivotInversion aug none q ∈ L := by
      exact (Erdos506.V3.pivotInversion_mem_circlePivotLine_iff
        aug none gammaAug.1 hnone q).2 hxAug
    have hdouble : Erdos506.V3.pivotInversion aug none q = cfg x :=
      pivotInversion_inversionAugmentation_some cfg o hoPoint x
    rw [hdouble] at hqLine
    exact hqLine
  have hcollinearL : Collinear ℝ (L : Set Point2) := by
    rw [collinear_iff_finrank_le_one,
      ← AffineSubspace.direction_eq_vectorSpan, hLfin]
  exact hTnoncol (hcollinearL.subset hTline)

private theorem inversionAugmentationGamma_some_mem_iff
    {α : Type u} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (gamma : Erdos506.V1.DeterminedCircle cfg)
    (hgamma : (circleTrace cfg gamma.1).card = 6)
    (o : Point2) (hoPoint : o ∉ pointSet cfg)
    (hoGamma : o ∉ (gamma.1.1 : Set Point2)) (x : α) :
    some x ∈ circleTrace (inversionAugmentation cfg o hoPoint)
        (inversionAugmentationGamma cfg gamma hgamma o hoPoint hoGamma).1 ↔
      x ∈ circleTrace cfg gamma.1 := by
  classical
  let aug := inversionAugmentation cfg o hoPoint
  let gammaAug :=
    inversionAugmentationGamma cfg gamma hgamma o hoPoint hoGamma
  constructor
  · intro hxAug
    have hnone := inversionAugmentationGamma_none_not_mem
      cfg gamma hgamma o hoPoint hoGamma
    have hoGammaAug : o ∉ (gammaAug.1.1 : Set Point2) := by
      intro ho
      apply hnone
      exact mem_circleTrace.mpr (by simpa [aug, gammaAug] using ho)
    let gammaBack : ProperCircle :=
      Erdos506.V3.invertedProperCircle o gammaAug.1 hoGammaAug
    have hxBackRaw := Erdos506.V3.inversion_mem_invertedProperCircle
      o (EuclideanGeometry.inversion o 1 (cfg x)) gammaAug.1
      hoGammaAug (by
        simpa [aug, gammaAug] using mem_circleTrace.mp hxAug)
    have hxBack : cfg x ∈ (gammaBack.1 : Set Point2) := by
      simpa [gammaBack] using hxBackRaw
    let T := sixConicTraceTriple cfg gamma hgamma
    have hTcircle : T.1 ⊆ circleTrace cfg gamma.1 :=
      sixConicTraceTriple_subset cfg gamma hgamma
    have hTnoncol : IsNoncollinear cfg T.1 :=
      isNoncollinear_of_card_three_subset_circle
        cfg gamma.1 T.1 T.2 hTcircle
    let t := attachedNoncollinearTriple cfg T hTnoncol
    have hTback : ∀ y ∈ T.1, cfg y ∈ (gammaBack.1 : Set Point2) := by
      intro y hy
      have hyAug : some y ∈ circleTrace aug gammaAug.1 :=
        inversionAugmentation_mem_invertedGamma
          cfg gamma o hoPoint hoGamma (hTcircle hy)
      have hyBackRaw := Erdos506.V3.inversion_mem_invertedProperCircle
        o (EuclideanGeometry.inversion o 1 (cfg y)) gammaAug.1
        hoGammaAug (by
          simpa [aug, gammaAug] using mem_circleTrace.mp hyAug)
      simpa [gammaBack] using hyBackRaw
    have hbackCircum : gammaBack = properCircumcircle cfg t :=
      properCircle_eq_properCircumcircle_of_support cfg t gammaBack hTback
    have hgammaCircum : gamma.1 = properCircumcircle cfg t :=
      properCircle_eq_properCircumcircle_of_support cfg t gamma.1
        (fun y hy => mem_circleTrace.mp (hTcircle hy))
    have hbackGamma : gammaBack = gamma.1 :=
      hbackCircum.trans hgammaCircum.symm
    apply mem_circleTrace.mpr
    simpa [hbackGamma] using hxBack
  · intro hx
    exact inversionAugmentation_mem_invertedGamma
      cfg gamma o hoPoint hoGamma hx

/-- Exact positive trace dictionary for the inverted selected circle. -/
theorem circleTrace_inversionAugmentationGamma
    {α : Type u} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (gamma : Erdos506.V1.DeterminedCircle cfg)
    (hgamma : (circleTrace cfg gamma.1).card = 6)
    (o : Point2) (hoPoint : o ∉ pointSet cfg)
    (hoGamma : o ∉ (gamma.1.1 : Set Point2)) :
    circleTrace (inversionAugmentation cfg o hoPoint)
        (inversionAugmentationGamma cfg gamma hgamma o hoPoint hoGamma).1 =
      (circleTrace cfg gamma.1).map Function.Embedding.some := by
  classical
  ext z
  cases z with
  | none =>
      constructor
      · intro hnone
        exact (inversionAugmentationGamma_none_not_mem
          cfg gamma hgamma o hoPoint hoGamma hnone).elim
      · intro hnone
        simp at hnone
  | some x =>
      simpa using inversionAugmentationGamma_some_mem_iff
        cfg gamma hgamma o hoPoint hoGamma x

theorem card_circleTrace_inversionAugmentationGamma
    {α : Type u} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (gamma : Erdos506.V1.DeterminedCircle cfg)
    (hgamma : (circleTrace cfg gamma.1).card = 6)
    (o : Point2) (hoPoint : o ∉ pointSet cfg)
    (hoGamma : o ∉ (gamma.1.1 : Set Point2)) :
    (circleTrace (inversionAugmentation cfg o hoPoint)
      (inversionAugmentationGamma cfg gamma hgamma o hoPoint hoGamma).1).card = 6 := by
  rw [circleTrace_inversionAugmentationGamma, Finset.card_map, hgamma]

/-! ## The pivot dictionary, with the physical original line retained -/

/-- Transport determined lines along an equality of configurations.  Keeping
this transport opaque prevents dependent rewriting inside the subtype proof. -/
private noncomputable def determinedLineCastEquiv
    {β : Type u} [Fintype β] [DecidableEq β]
    {C D : Configuration β} (hCD : C = D) :
    DeterminedLine C ≃ DeterminedLine D := by
  cases hCD
  exact Equiv.refl _

@[simp] private theorem determinedLineCastEquiv_coe
    {β : Type u} [Fintype β] [DecidableEq β]
    {C D : Configuration β} (hCD : C = D) (L : DeterminedLine C) :
    ((determinedLineCastEquiv hCD) L).1 = L.1 := by
  cases hCD
  rfl

@[simp] private theorem determinedLineRelabelEquiv_coe
    {β : Type u} {δ : Type u}
    [Fintype β] [Fintype δ] [DecidableEq β] [DecidableEq δ]
    (cfg : Configuration β) (e : δ ≃ β)
    (L : DeterminedLine (relabelConfiguration cfg e)) :
    ((determinedLineRelabelEquiv cfg e) L).1 = L.1 := rfl

/-- The V1 pivot-block/line bijection, bundled before any configuration
transport. -/
private noncomputable def pivotBlockToPivotLineEquiv
    {β : Type u} [Fintype β] [DecidableEq β]
    (cfg : Configuration β) (p : β) :
    PivotBlock cfg p ≃ DeterminedLine (Erdos506.V3.pivotInversion cfg p) :=
  Equiv.ofBijective (blockToPivotLine cfg p)
    ⟨blockToPivotLine_injective cfg p, blockToPivotLine_surjective cfg p⟩

/-- Double inversion followed by the canonical relabelling transports a
pivot-inverted determined line to the corresponding old determined line. -/
private noncomputable def inversionAugmentationPivotLineEquiv
    {α : Type u} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (o : Point2) (hoPoint : o ∉ pointSet cfg) :
    DeterminedLine
        (Erdos506.V3.pivotInversion
          (inversionAugmentation cfg o hoPoint) none) ≃
      DeterminedLine cfg :=
  (determinedLineCastEquiv
      (pivotInversion_inversionAugmentation_eq_relabel cfg o hoPoint)).trans
    (determinedLineRelabelEquiv cfg (awayFromNoneEquiv α))

@[simp] private theorem inversionAugmentationPivotLineEquiv_coe
    {α : Type u} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (o : Point2) (hoPoint : o ∉ pointSet cfg)
    (L : DeterminedLine
      (Erdos506.V3.pivotInversion
        (inversionAugmentation cfg o hoPoint) none)) :
    ((inversionAugmentationPivotLineEquiv cfg o hoPoint) L).1 = L.1 := by
  simp [inversionAugmentationPivotLineEquiv]

/-- Augmented generalized blocks through the new point are canonically the
old determined affine lines. -/
noncomputable def inversionAugmentationPivotBlockEquiv
    {α : Type u} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (o : Point2) (hoPoint : o ∉ pointSet cfg) :
    PivotBlock (inversionAugmentation cfg o hoPoint) none ≃
      DeterminedLine cfg :=
  (pivotBlockToPivotLineEquiv
      (inversionAugmentation cfg o hoPoint) none).trans
    (inversionAugmentationPivotLineEquiv cfg o hoPoint)

@[simp] theorem inversionAugmentationPivotBlockEquiv_coe
    {α : Type u} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (o : Point2) (hoPoint : o ∉ pointSet cfg)
    (b : PivotBlock (inversionAugmentation cfg o hoPoint) none) :
    (inversionAugmentationPivotBlockEquiv cfg o hoPoint b).1 =
      (blockToPivotLine (inversionAugmentation cfg o hoPoint) none b).1 := by
  change
    ((inversionAugmentationPivotLineEquiv cfg o hoPoint)
      (blockToPivotLine (inversionAugmentation cfg o hoPoint) none b)).1 = _
  exact inversionAugmentationPivotLineEquiv_coe cfg o hoPoint _

/-- The old determined line attached to an augmented block through `none`. -/
noncomputable def inversionAugmentationBlockToLine
    {α : Type u} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (o : Point2) (hoPoint : o ∉ pointSet cfg)
    (b : PivotBlock (inversionAugmentation cfg o hoPoint) none) :
    DeterminedLine cfg :=
  inversionAugmentationPivotBlockEquiv cfg o hoPoint b

@[simp] theorem inversionAugmentationBlockToLine_coe
    {α : Type u} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (o : Point2) (hoPoint : o ∉ pointSet cfg)
    (b : PivotBlock (inversionAugmentation cfg o hoPoint) none) :
    (inversionAugmentationBlockToLine cfg o hoPoint b).1 =
      (blockToPivotLine (inversionAugmentation cfg o hoPoint) none b).1 := by
  exact inversionAugmentationPivotBlockEquiv_coe cfg o hoPoint b

@[simp] theorem inversionAugmentationPivotBlockEquiv_apply
    {α : Type u} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (o : Point2) (hoPoint : o ∉ pointSet cfg)
    (b : PivotBlock (inversionAugmentation cfg o hoPoint) none) :
    inversionAugmentationPivotBlockEquiv cfg o hoPoint b =
      inversionAugmentationBlockToLine cfg o hoPoint b := rfl

/-- Exact support dictionary for the old labels: an old label lies on the
old line precisely when its `some`-label lies on the corresponding
augmented block. -/
theorem inversionAugmentationPivotBlock_some_mem_iff
    {α : Type u} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (o : Point2) (hoPoint : o ∉ pointSet cfg)
    (b : PivotBlock (inversionAugmentation cfg o hoPoint) none) (x : α) :
    some x ∈ geometricBlockSupport
        (inversionAugmentation cfg o hoPoint) b.1 ↔
      x ∈ lineSupport cfg
        (inversionAugmentationPivotBlockEquiv cfg o hoPoint b) := by
  let aug := inversionAugmentation cfg o hoPoint
  let q : Erdos506.V3.AwayFrom (none : Option α) :=
    ⟨some x, Option.some_ne_none x⟩
  calc
    some x ∈ geometricBlockSupport aug b.1 ↔
        q ∈ awaySupport none (geometricBlockSupport aug b.1) := by
      exact (mem_awaySupport (p := none)
        (T := geometricBlockSupport aug b.1) (q := q)).symm
    _ ↔ q ∈ lineSupport (Erdos506.V3.pivotInversion aug none)
        (blockToPivotLine aug none b) := by
      rw [lineSupport_blockToPivotLine]
    _ ↔ Erdos506.V3.pivotInversion aug none q ∈
        (blockToPivotLine aug none b).1 :=
      mem_lineSupport
    _ ↔ cfg x ∈ (blockToPivotLine aug none b).1 := by
      rw [pivotInversion_inversionAugmentation_some cfg o hoPoint x]
    _ ↔ x ∈ lineSupport cfg
        (inversionAugmentationPivotBlockEquiv cfg o hoPoint b) := by
      rw [mem_lineSupport, inversionAugmentationPivotBlockEquiv_coe]

private theorem inversionAugmentation_inverseLineBlock_is_circle
    {α : Type u} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (o : Point2) (hoPoint : o ∉ pointSet cfg)
    (hoLines : ∀ L : DeterminedLine cfg, o ∉ (L.1 : Set Point2))
    (L : DeterminedLine cfg) :
    ∃ c : Erdos506.V1.DeterminedCircle (inversionAugmentation cfg o hoPoint),
      ((inversionAugmentationPivotBlockEquiv cfg o hoPoint).symm L).1 =
        Sum.inr c := by
  let aug := inversionAugmentation cfg o hoPoint
  let E := inversionAugmentationPivotBlockEquiv cfg o hoPoint
  let b := E.symm L
  have hbL0 : E b = L := E.apply_symm_apply L
  change ∃ c : Erdos506.V1.DeterminedCircle aug, b.1 = Sum.inr c
  rcases b with ⟨b, hp, hcard⟩
  cases b with
  | inr c => exact ⟨c, rfl⟩
  | inl K =>
      exfalso
      have hnone : none ∈ lineSupport aug K := by
        exact hp
      have hoK : o ∈ (K.1 : Set Point2) := by
        simpa [aug] using mem_lineSupport.mp hnone
      have hbL : E (⟨Sum.inl K, hp, hcard⟩ : PivotBlock aug none) = L :=
        hbL0
      have hKL : K.1 = L.1 := by
        have hphysical := congrArg
          (fun M : DeterminedLine cfg => M.1) hbL
        dsimp only [E] at hphysical
        rw [inversionAugmentationPivotBlockEquiv_coe] at hphysical
        change K.1 = L.1 at hphysical
        exact hphysical
      exact hoLines L (hKL ▸ hoK)

/-- The determined circle through the added point corresponding to an old
determined affine line.  Avoidance of all old lines is exactly what rules
out the line branch of the generalized pivot block. -/
noncomputable def inversionAugmentationLineCircle
    {α : Type u} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (o : Point2) (hoPoint : o ∉ pointSet cfg)
    (hoLines : ∀ L : DeterminedLine cfg, o ∉ (L.1 : Set Point2))
    (L : DeterminedLine cfg) :
    Erdos506.V1.DeterminedCircle (inversionAugmentation cfg o hoPoint) :=
  Classical.choose
    (inversionAugmentation_inverseLineBlock_is_circle
      cfg o hoPoint hoLines L)

theorem inversionAugmentationLineCircle_spec
    {α : Type u} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (o : Point2) (hoPoint : o ∉ pointSet cfg)
    (hoLines : ∀ L : DeterminedLine cfg, o ∉ (L.1 : Set Point2))
    (L : DeterminedLine cfg) :
    ((inversionAugmentationPivotBlockEquiv cfg o hoPoint).symm L).1 =
      Sum.inr (inversionAugmentationLineCircle cfg o hoPoint hoLines L) :=
  Classical.choose_spec
    (inversionAugmentation_inverseLineBlock_is_circle
      cfg o hoPoint hoLines L)

theorem inversionAugmentationLineCircle_none_mem
    {α : Type u} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (o : Point2) (hoPoint : o ∉ pointSet cfg)
    (hoLines : ∀ L : DeterminedLine cfg, o ∉ (L.1 : Set Point2))
    (L : DeterminedLine cfg) :
    none ∈ circleTrace (inversionAugmentation cfg o hoPoint)
      (inversionAugmentationLineCircle cfg o hoPoint hoLines L).1 := by
  let b := (inversionAugmentationPivotBlockEquiv cfg o hoPoint).symm L
  have hnone := b.2.1
  rw [inversionAugmentationLineCircle_spec
    cfg o hoPoint hoLines L] at hnone
  exact hnone

theorem inversionAugmentationLineCircle_some_mem_iff
    {α : Type u} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (o : Point2) (hoPoint : o ∉ pointSet cfg)
    (hoLines : ∀ L : DeterminedLine cfg, o ∉ (L.1 : Set Point2))
    (L : DeterminedLine cfg) (x : α) :
    some x ∈ circleTrace (inversionAugmentation cfg o hoPoint)
        (inversionAugmentationLineCircle cfg o hoPoint hoLines L).1 ↔
      x ∈ lineSupport cfg L := by
  let b := (inversionAugmentationPivotBlockEquiv cfg o hoPoint).symm L
  have hsupport := inversionAugmentationPivotBlock_some_mem_iff
    cfg o hoPoint b x
  rw [inversionAugmentationLineCircle_spec
    cfg o hoPoint hoLines L] at hsupport
  have hb :
      inversionAugmentationPivotBlockEquiv cfg o hoPoint b = L :=
    (inversionAugmentationPivotBlockEquiv cfg o hoPoint).apply_symm_apply L
  rw [hb] at hsupport
  change
    (some x ∈ circleTrace (inversionAugmentation cfg o hoPoint)
        (inversionAugmentationLineCircle cfg o hoPoint hoLines L).1 ↔
      x ∈ lineSupport cfg L) at hsupport
  exact hsupport

/-- Exact positive trace dictionary for the circle representing an old
line. -/
theorem circleTrace_inversionAugmentationLineCircle
    {α : Type u} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (o : Point2) (hoPoint : o ∉ pointSet cfg)
    (hoLines : ∀ L : DeterminedLine cfg, o ∉ (L.1 : Set Point2))
    (L : DeterminedLine cfg) :
    circleTrace (inversionAugmentation cfg o hoPoint)
        (inversionAugmentationLineCircle cfg o hoPoint hoLines L).1 =
      insert none ((lineSupport cfg L).map Function.Embedding.some) := by
  classical
  ext z
  cases z with
  | none =>
      simp [inversionAugmentationLineCircle_none_mem
        cfg o hoPoint hoLines L]
  | some x =>
      simpa using inversionAugmentationLineCircle_some_mem_iff
        cfg o hoPoint hoLines L x

private theorem insert_none_map_some_inter_map_some
    {α : Type*} [DecidableEq α] (A B : Finset α) :
    insert none (A.map Function.Embedding.some) ∩
        B.map Function.Embedding.some =
      (A ∩ B).map Function.Embedding.some := by
  ext z
  cases z <;> simp

/-! ## Restricted old-line / augmented pair-circle equivalence -/

/-- Old determined lines which contain `x` and meet the selected
six-circle in exactly two selected labels. -/
abbrev SixConicMarkedLineAt
    {α : Type u} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (gamma : Erdos506.V1.DeterminedCircle cfg) (x : α) :=
  {L : DeterminedLine cfg //
    (lineSupport cfg L ∩ circleTrace cfg gamma.1).card = 2 ∧
      x ∈ lineSupport cfg L}

/-- Pair-circles on the radial augmented edge `{none, some x}`. -/
abbrev SixConicAugmentedRadialPairCircle
    {α : Type u} [Fintype α] [DecidableEq α]
    (aug : Configuration (Option α))
    (gammaAug : Erdos506.V1.DeterminedCircle aug)
    (x : α) :=
  {c : Erdos506.V1.DeterminedCircle aug //
    c ∈ sixConicPairCircles aug gammaAug {none, some x}}

private theorem inversionAugmentationLineCircle_pair
    {α : Type u} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (gamma : Erdos506.V1.DeterminedCircle cfg)
    (hgamma : (circleTrace cfg gamma.1).card = 6)
    (o : Point2) (hoPoint : o ∉ pointSet cfg)
    (hoGamma : o ∉ (gamma.1.1 : Set Point2))
    (hoLines : ∀ L : DeterminedLine cfg, o ∉ (L.1 : Set Point2))
    (x : α) (L : SixConicMarkedLineAt cfg gamma x) :
    inversionAugmentationLineCircle cfg o hoPoint hoLines L.1 ∈
      sixConicPairCircles (inversionAugmentation cfg o hoPoint)
        (inversionAugmentationGamma cfg gamma hgamma o hoPoint hoGamma)
        {none, some x} := by
  classical
  let aug := inversionAugmentation cfg o hoPoint
  let gammaAug :=
    inversionAugmentationGamma cfg gamma hgamma o hoPoint hoGamma
  let c := inversionAugmentationLineCircle cfg o hoPoint hoLines L.1
  apply mem_sixConicPairCircles.mpr
  constructor
  · intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl
    · exact inversionAugmentationLineCircle_none_mem
        cfg o hoPoint hoLines L.1
    · exact (inversionAugmentationLineCircle_some_mem_iff
        cfg o hoPoint hoLines L.1 x).2 L.2.2
  · have hinter :
        circleTrace aug c.1 ∩ circleTrace aug gammaAug.1 =
          ((lineSupport cfg L.1 ∩ circleTrace cfg gamma.1).map
            Function.Embedding.some) := by
      rw [circleTrace_inversionAugmentationLineCircle,
        circleTrace_inversionAugmentationGamma,
        insert_none_map_some_inter_map_some]
    rw [hinter, Finset.card_map]
    exact L.2.1

private theorem inversionAugmentation_pairCircle_trace
    {α : Type u} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (o : Point2) (hoPoint : o ∉ pointSet cfg)
    (b : PivotBlock (inversionAugmentation cfg o hoPoint) none)
    (c : Erdos506.V1.DeterminedCircle (inversionAugmentation cfg o hoPoint))
    (hbc : b.1 = Sum.inr c) :
    circleTrace (inversionAugmentation cfg o hoPoint) c.1 =
      insert none
        ((lineSupport cfg
          (inversionAugmentationPivotBlockEquiv cfg o hoPoint b)).map
            Function.Embedding.some) := by
  classical
  ext z
  cases z with
  | none =>
      have hnone := b.2.1
      rw [hbc] at hnone
      change none ∈ circleTrace (inversionAugmentation cfg o hoPoint) c.1 at hnone
      change
        (none ∈ circleTrace (inversionAugmentation cfg o hoPoint) c.1) ↔
          none ∈ insert none
            ((lineSupport cfg
              (inversionAugmentationPivotBlockEquiv cfg o hoPoint b)).map
                Function.Embedding.some)
      exact iff_of_true hnone (by simp)
  | some x =>
      have hx := inversionAugmentationPivotBlock_some_mem_iff
        cfg o hoPoint b x
      rw [hbc] at hx
      change
        (some x ∈ circleTrace (inversionAugmentation cfg o hoPoint) c.1 ↔
          x ∈ lineSupport cfg
            (inversionAugmentationPivotBlockEquiv cfg o hoPoint b)) at hx
      change
        (some x ∈ circleTrace (inversionAugmentation cfg o hoPoint) c.1) ↔
          some x ∈ insert none
            ((lineSupport cfg
              (inversionAugmentationPivotBlockEquiv cfg o hoPoint b)).map
                Function.Embedding.some)
      exact hx.trans (by simp)

/-- Forward half of the restricted equivalence. -/
noncomputable def inversionAugmentationMarkedLineToPairCircle
    {α : Type u} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (gamma : Erdos506.V1.DeterminedCircle cfg)
    (hgamma : (circleTrace cfg gamma.1).card = 6)
    (o : Point2) (hoPoint : o ∉ pointSet cfg)
    (hoGamma : o ∉ (gamma.1.1 : Set Point2))
    (hoLines : ∀ L : DeterminedLine cfg, o ∉ (L.1 : Set Point2))
    (x : α) :
    SixConicMarkedLineAt cfg gamma x →
      SixConicAugmentedRadialPairCircle
        (inversionAugmentation cfg o hoPoint)
        (inversionAugmentationGamma cfg gamma hgamma o hoPoint hoGamma) x :=
  fun L =>
    ⟨inversionAugmentationLineCircle cfg o hoPoint hoLines L.1,
      inversionAugmentationLineCircle_pair
        cfg gamma hgamma o hoPoint hoGamma hoLines x L⟩

/-- Reverse half of the restricted equivalence. -/
noncomputable def inversionAugmentationPairCircleToMarkedLine
    {α : Type u} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (gamma : Erdos506.V1.DeterminedCircle cfg)
    (hgamma : (circleTrace cfg gamma.1).card = 6)
    (o : Point2) (hoPoint : o ∉ pointSet cfg)
    (hoGamma : o ∉ (gamma.1.1 : Set Point2))
    (x : α) :
    SixConicAugmentedRadialPairCircle
        (inversionAugmentation cfg o hoPoint)
        (inversionAugmentationGamma cfg gamma hgamma o hoPoint hoGamma) x →
      SixConicMarkedLineAt cfg gamma x := by
  classical
  intro c
  let aug := inversionAugmentation cfg o hoPoint
  let gammaAug :=
    inversionAugmentationGamma cfg gamma hgamma o hoPoint hoGamma
  have hpair := mem_sixConicPairCircles.mp c.2
  have hnone : none ∈ circleTrace aug c.1.1 := hpair.1 (by simp)
  let b : PivotBlock aug none :=
    ⟨Sum.inr c.1, hnone, by
      simpa [geometricBlockSupport] using
        (Erdos506.V3.circleSupport_card_ge_three aug c.1)⟩
  let L := inversionAugmentationPivotBlockEquiv cfg o hoPoint b
  refine ⟨L, ?_, ?_⟩
  · have htrace := inversionAugmentation_pairCircle_trace
      cfg o hoPoint b c.1 rfl
    have hinter :
        circleTrace aug c.1.1 ∩ circleTrace aug gammaAug.1 =
          ((lineSupport cfg L ∩ circleTrace cfg gamma.1).map
            Function.Embedding.some) := by
      rw [htrace, circleTrace_inversionAugmentationGamma,
        insert_none_map_some_inter_map_some]
    rw [hinter, Finset.card_map] at hpair
    exact hpair.2
  · have hsome : some x ∈ circleTrace aug c.1.1 := hpair.1 (by simp)
    have hsupport := inversionAugmentationPivotBlock_some_mem_iff
      cfg o hoPoint b x
    exact hsupport.mp (by simpa [b, geometricBlockSupport] using hsome)

private theorem inversionAugmentationMarkedLineToPairCircle_left_inv
    {α : Type u} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (gamma : Erdos506.V1.DeterminedCircle cfg)
    (hgamma : (circleTrace cfg gamma.1).card = 6)
    (o : Point2) (hoPoint : o ∉ pointSet cfg)
    (hoGamma : o ∉ (gamma.1.1 : Set Point2))
    (hoLines : ∀ L : DeterminedLine cfg, o ∉ (L.1 : Set Point2))
    (x : α) (L : SixConicMarkedLineAt cfg gamma x) :
    inversionAugmentationPairCircleToMarkedLine
        cfg gamma hgamma o hoPoint hoGamma x
        (inversionAugmentationMarkedLineToPairCircle
          cfg gamma hgamma o hoPoint hoGamma hoLines x L) = L := by
  apply Subtype.ext
  let E := inversionAugmentationPivotBlockEquiv cfg o hoPoint
  let b := E.symm L.1
  let c := inversionAugmentationLineCircle cfg o hoPoint hoLines L.1
  have hbc : b.1 = Sum.inr c :=
    inversionAugmentationLineCircle_spec cfg o hoPoint hoLines L.1
  let pb : PivotBlock (inversionAugmentation cfg o hoPoint) none :=
    ⟨Sum.inr c,
      inversionAugmentationLineCircle_none_mem
        cfg o hoPoint hoLines L.1,
      by
        simpa [geometricBlockSupport] using
          (Erdos506.V3.circleSupport_card_ge_three
            (inversionAugmentation cfg o hoPoint) c)⟩
  have hb : pb = b := by
    apply Subtype.ext
    exact hbc.symm
  change E pb = L.1
  rw [hb]
  exact E.apply_symm_apply L.1

private theorem inversionAugmentationMarkedLineToPairCircle_right_inv
    {α : Type u} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (gamma : Erdos506.V1.DeterminedCircle cfg)
    (hgamma : (circleTrace cfg gamma.1).card = 6)
    (o : Point2) (hoPoint : o ∉ pointSet cfg)
    (hoGamma : o ∉ (gamma.1.1 : Set Point2))
    (hoLines : ∀ L : DeterminedLine cfg, o ∉ (L.1 : Set Point2))
    (x : α)
    (c : SixConicAugmentedRadialPairCircle
      (inversionAugmentation cfg o hoPoint)
      (inversionAugmentationGamma cfg gamma hgamma o hoPoint hoGamma) x) :
    inversionAugmentationMarkedLineToPairCircle
        cfg gamma hgamma o hoPoint hoGamma hoLines x
        (inversionAugmentationPairCircleToMarkedLine
          cfg gamma hgamma o hoPoint hoGamma x c) = c := by
  apply Subtype.ext
  let aug := inversionAugmentation cfg o hoPoint
  let gammaAug :=
    inversionAugmentationGamma cfg gamma hgamma o hoPoint hoGamma
  have hpair := mem_sixConicPairCircles.mp c.2
  have hnone : none ∈ circleTrace aug c.1.1 := hpair.1 (by simp)
  let b : PivotBlock aug none :=
    ⟨Sum.inr c.1, hnone, by
      simpa [geometricBlockSupport] using
        (Erdos506.V3.circleSupport_card_ge_three aug c.1)⟩
  let E := inversionAugmentationPivotBlockEquiv cfg o hoPoint
  have hspec := inversionAugmentationLineCircle_spec
    cfg o hoPoint hoLines (E b)
  have hinv : E.symm (E b) = b := E.symm_apply_apply b
  rw [hinv] at hspec
  change inversionAugmentationLineCircle cfg o hoPoint hoLines (E b) = c.1
  exact (Sum.inr.inj hspec).symm

/-- Exact finite equivalence between the old marked lines through `x` and
the augmented pair-circles on `{none, some x}`. -/
noncomputable def inversionAugmentationMarkedLinePairCircleEquiv
    {α : Type u} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (gamma : Erdos506.V1.DeterminedCircle cfg)
    (hgamma : (circleTrace cfg gamma.1).card = 6)
    (o : Point2) (hoPoint : o ∉ pointSet cfg)
    (hoGamma : o ∉ (gamma.1.1 : Set Point2))
    (hoLines : ∀ L : DeterminedLine cfg, o ∉ (L.1 : Set Point2))
    (x : α) :
    SixConicMarkedLineAt cfg gamma x ≃
      SixConicAugmentedRadialPairCircle
        (inversionAugmentation cfg o hoPoint)
        (inversionAugmentationGamma cfg gamma hgamma o hoPoint hoGamma) x where
  toFun := inversionAugmentationMarkedLineToPairCircle
    cfg gamma hgamma o hoPoint hoGamma hoLines x
  invFun := inversionAugmentationPairCircleToMarkedLine
    cfg gamma hgamma o hoPoint hoGamma x
  left_inv := inversionAugmentationMarkedLineToPairCircle_left_inv
    cfg gamma hgamma o hoPoint hoGamma hoLines x
  right_inv := inversionAugmentationMarkedLineToPairCircle_right_inv
    cfg gamma hgamma o hoPoint hoGamma hoLines x

theorem card_sixConicMarkedLineAt_eq_radialPairWeight
    {α : Type u} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (gamma : Erdos506.V1.DeterminedCircle cfg)
    (hgamma : (circleTrace cfg gamma.1).card = 6)
    (o : Point2) (hoPoint : o ∉ pointSet cfg)
    (hoGamma : o ∉ (gamma.1.1 : Set Point2))
    (hoLines : ∀ L : DeterminedLine cfg, o ∉ (L.1 : Set Point2))
    (x : α) :
    Fintype.card (SixConicMarkedLineAt cfg gamma x) =
      sixConicPairWeight (inversionAugmentation cfg o hoPoint)
        (inversionAugmentationGamma cfg gamma hgamma o hoPoint hoGamma)
        {none, some x} := by
  classical
  letI : Fintype
      (SixConicAugmentedRadialPairCircle
        (inversionAugmentation cfg o hoPoint)
        (inversionAugmentationGamma cfg gamma hgamma o hoPoint hoGamma) x) :=
    Finset.fintypeCoeSort _
  rw [sixConicPairWeight]
  calc
    Fintype.card (SixConicMarkedLineAt cfg gamma x) =
        Fintype.card
          (SixConicAugmentedRadialPairCircle
            (inversionAugmentation cfg o hoPoint)
            (inversionAugmentationGamma
              cfg gamma hgamma o hoPoint hoGamma) x) :=
      Fintype.card_congr
        (inversionAugmentationMarkedLinePairCircleEquiv
          cfg gamma hgamma o hoPoint hoGamma hoLines x)
    _ = (sixConicPairCircles
          (inversionAugmentation cfg o hoPoint)
          (inversionAugmentationGamma cfg gamma hgamma o hoPoint hoGamma)
          {none, some x}).card := by
      exact Fintype.card_coe _

/-! ## Double-counting the old line incidences -/

private theorem card_inter_eq_sum_mem_indicator
    {α : Type*} [DecidableEq α] (A X : Finset α) :
    (A ∩ X).card = ∑ x ∈ X, if x ∈ A then 1 else 0 := by
  classical
  calc
    (A ∩ X).card = ∑ _x ∈ A ∩ X, 1 := by
      exact Finset.card_eq_sum_ones (A ∩ X)
    _ = ∑ x ∈ X, if x ∈ A then 1 else 0 := by
      rw [← Finset.sum_filter]
      congr 1
      ext x
      simp [and_comm]

private theorem sixConicLineIncidence_row_eq_indicator_sum
    {α : Type u} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (gamma : Erdos506.V1.DeterminedCircle cfg)
    (X : Finset α) (L : DeterminedLine cfg) :
    (if (lineSupport cfg L ∩ circleTrace cfg gamma.1).card = 2 then
        (lineSupport cfg L ∩ X).card
      else 0) =
      ∑ x ∈ X,
        if (lineSupport cfg L ∩ circleTrace cfg gamma.1).card = 2 ∧
            x ∈ lineSupport cfg L then 1 else 0 := by
  classical
  by_cases hmarked :
      (lineSupport cfg L ∩ circleTrace cfg gamma.1).card = 2
  · rw [if_pos hmarked,
      card_inter_eq_sum_mem_indicator (lineSupport cfg L) X]
    apply Finset.sum_congr rfl
    intro x _hx
    simp [hmarked]
  · simp [hmarked]

private theorem sixConicMarkedLineAt_indicator_sum_eq_card
    {α : Type u} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (gamma : Erdos506.V1.DeterminedCircle cfg)
    (x : α) :
    (∑ L : DeterminedLine cfg,
      if (lineSupport cfg L ∩ circleTrace cfg gamma.1).card = 2 ∧
          x ∈ lineSupport cfg L then 1 else 0) =
      Fintype.card (SixConicMarkedLineAt cfg gamma x) := by
  classical
  rw [← Finset.sum_filter, ← Finset.card_eq_sum_ones]
  exact (Fintype.card_subtype (fun L : DeterminedLine cfg =>
    (lineSupport cfg L ∩ circleTrace cfg gamma.1).card = 2 ∧
      x ∈ lineSupport cfg L)).symm

/-- `J` is the sum, over outsider labels, of the finite marked-line
fibres through that label. -/
theorem sixConicLineIncidence_eq_sum_card_markedLineAt
    {α : Type u} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (gamma : Erdos506.V1.DeterminedCircle cfg)
    (X : Finset α) :
    sixConicLineIncidence cfg gamma X =
      ∑ x ∈ X, Fintype.card (SixConicMarkedLineAt cfg gamma x) := by
  classical
  unfold sixConicLineIncidence
  calc
    (∑ L : DeterminedLine cfg,
        if (lineSupport cfg L ∩ circleTrace cfg gamma.1).card = 2 then
          (lineSupport cfg L ∩ X).card
        else 0) =
        ∑ L : DeterminedLine cfg, ∑ x ∈ X,
          if (lineSupport cfg L ∩ circleTrace cfg gamma.1).card = 2 ∧
              x ∈ lineSupport cfg L then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro L _hL
      exact sixConicLineIncidence_row_eq_indicator_sum cfg gamma X L
    _ = ∑ x ∈ X, ∑ L : DeterminedLine cfg,
          if (lineSupport cfg L ∩ circleTrace cfg gamma.1).card = 2 ∧
              x ∈ lineSupport cfg L then 1 else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ x ∈ X,
          Fintype.card (SixConicMarkedLineAt cfg gamma x) := by
      apply Finset.sum_congr rfl
      intro x _hx
      exact sixConicMarkedLineAt_indicator_sum_eq_card cfg gamma x

/-- The inversion augmentation identifies the complete old line-incidence
sum with the five radial pair weights in the augmented configuration. -/
theorem sixConicLineIncidence_eq_sum_radialPairWeight
    {α : Type u} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (gamma : Erdos506.V1.DeterminedCircle cfg)
    (hgamma : (circleTrace cfg gamma.1).card = 6)
    (X : Finset α)
    (o : Point2) (hoPoint : o ∉ pointSet cfg)
    (hoGamma : o ∉ (gamma.1.1 : Set Point2))
    (hoLines : ∀ L : DeterminedLine cfg, o ∉ (L.1 : Set Point2)) :
    sixConicLineIncidence cfg gamma X =
      ∑ x ∈ X,
        sixConicPairWeight (inversionAugmentation cfg o hoPoint)
          (inversionAugmentationGamma cfg gamma hgamma o hoPoint hoGamma)
          {none, some x} := by
  rw [sixConicLineIncidence_eq_sum_card_markedLineAt]
  apply Finset.sum_congr rfl
  intro x _hx
  exact card_sixConicMarkedLineAt_eq_radialPairWeight
    cfg gamma hgamma o hoPoint hoGamma hoLines x

/-! ## The radial-star capacity argument -/

private theorem inversionAugmentation_radialEdge_disjoint_gamma
    {α : Type u} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (gamma : Erdos506.V1.DeterminedCircle cfg)
    (hgamma : (circleTrace cfg gamma.1).card = 6)
    (X : Finset α) (hdisjoint : Disjoint (circleTrace cfg gamma.1) X)
    (o : Point2) (hoPoint : o ∉ pointSet cfg)
    (hoGamma : o ∉ (gamma.1.1 : Set Point2))
    {x : α} (hx : x ∈ X) :
    Disjoint ({none, some x} : Finset (Option α))
      (circleTrace (inversionAugmentation cfg o hoPoint)
        (inversionAugmentationGamma cfg gamma hgamma o hoPoint hoGamma).1) := by
  rw [circleTrace_inversionAugmentationGamma, Finset.disjoint_left]
  intro z hzEdge hzGamma
  simp only [Finset.mem_insert, Finset.mem_singleton] at hzEdge
  rcases hzEdge with rfl | rfl
  · simp at hzGamma
  · have hxGamma : x ∈ circleTrace cfg gamma.1 := by
      simpa using hzGamma
    exact Finset.disjoint_left.mp hdisjoint hxGamma hx

private theorem circleTrace_inversionAugmentationGamma_disjoint_insertMap
    {α : Type u} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (gamma : Erdos506.V1.DeterminedCircle cfg)
    (hgamma : (circleTrace cfg gamma.1).card = 6)
    (X : Finset α) (hdisjoint : Disjoint (circleTrace cfg gamma.1) X)
    (o : Point2) (hoPoint : o ∉ pointSet cfg)
    (hoGamma : o ∉ (gamma.1.1 : Set Point2)) :
    Disjoint
      (circleTrace (inversionAugmentation cfg o hoPoint)
        (inversionAugmentationGamma cfg gamma hgamma o hoPoint hoGamma).1)
      (insert none (X.map Function.Embedding.some)) := by
  rw [circleTrace_inversionAugmentationGamma, Finset.disjoint_left]
  intro z hzGamma hzX
  cases z with
  | none => simp at hzGamma
  | some x =>
      have hxGamma : x ∈ circleTrace cfg gamma.1 := by
        simpa using hzGamma
      have hxX : x ∈ X := by
        simpa using hzX
      exact Finset.disjoint_left.mp hdisjoint hxGamma hxX

private theorem finset_all_eq_three_of_card_five_of_sum_not_le_fourteen
    {α : Type u} [DecidableEq α]
    (X : Finset α) (hX : X.card = 5) (q : α → Nat)
    (hq : ∀ x ∈ X, q x ≤ 3)
    (hnot : ¬ ((∑ x ∈ X, q x) ≤ 14)) :
    ∀ x ∈ X, q x = 3 := by
  have hsumUpper : (∑ x ∈ X, q x) ≤ 15 := by
    calc
      (∑ x ∈ X, q x) ≤ ∑ _x ∈ X, 3 := by
        exact Finset.sum_le_sum fun x hx => hq x hx
      _ = 15 := by simp [hX]
  have hsumFifteen : (∑ x ∈ X, q x) = 15 := by omega
  have hsumThree : (∑ _x ∈ X, 3) = 15 := by simp [hX]
  intro x hx
  exact (Finset.sum_eq_sum_iff_of_le
    (fun y hy => hq y hy)).mp
      (hsumFifteen.trans hsumThree.symm) x hx

private theorem optionRadialEdge_injective
    {α : Type u} [DecidableEq α] :
    Function.Injective
      (fun x : α => ({none, some x} : Finset (Option α))) := by
  intro x y hxy
  change
    ({none, some x} : Finset (Option α)) = {none, some y} at hxy
  have hxmem : some x ∈ ({none, some x} : Finset (Option α)) := by simp
  rw [hxy] at hxmem
  simpa using hxmem

private theorem sixConic_radialSignature_injective
    {α : Type u} [Fintype α] [DecidableEq α]
    (aug : Configuration (Option α))
    (gammaAug : Erdos506.V1.DeterminedCircle aug)
    (hgammaAug : (circleTrace aug gammaAug.1).card = 6)
    (Xaug : Finset (Option α))
    (hdisjointAug : Disjoint (circleTrace aug gammaAug.1) Xaug)
    (X : Finset α)
    (hfull : ∀ x ∈ X,
      ({none, some x} : Finset (Option α)) ∈
        sixConicFullEdges aug gammaAug Xaug) :
    Set.InjOn
      (fun x : α => sixConicSignature aug gammaAug {none, some x})
      (X : Set α) := by
  intro x hx y hy hsignature
  by_contra hxy
  have hedgeNe :
      ({none, some x} : Finset (Option α)) ≠ {none, some y} :=
    optionRadialEdge_injective.ne hxy
  have hEdgesDisjoint :
      Disjoint ({none, some x} : Finset (Option α)) {none, some y} :=
    sixConic_equal_full_signatures_disjoint
      aug gammaAug hgammaAug Xaug hdisjointAug
      (hfull x hx) (hfull y hy) hedgeNe hsignature
  have hnoneLeft : none ∈ ({none, some x} : Finset (Option α)) := by simp
  have hnoneRight : none ∈ ({none, some y} : Finset (Option α)) := by simp
  exact Finset.disjoint_left.mp hEdgesDisjoint hnoneLeft hnoneRight

private theorem sixConic_activeSignatures_card_ge_five_of_radialFull
    {α : Type u} [Fintype α] [DecidableEq α]
    (aug : Configuration (Option α))
    (gammaAug : Erdos506.V1.DeterminedCircle aug)
    (hgammaAug : (circleTrace aug gammaAug.1).card = 6)
    (Xaug : Finset (Option α))
    (hdisjointAug : Disjoint (circleTrace aug gammaAug.1) Xaug)
    (X : Finset α) (hX : X.card = 5)
    (hfull : ∀ x ∈ X,
      ({none, some x} : Finset (Option α)) ∈
        sixConicFullEdges aug gammaAug Xaug) :
    5 ≤ (sixConicActiveSignatures aug gammaAug Xaug).card := by
  classical
  let signature : α → Finset (Finset (Option α)) := fun x =>
    sixConicSignature aug gammaAug {none, some x}
  have hsignatureInj : Set.InjOn signature (X : Set α) := by
    simpa [signature] using
      sixConic_radialSignature_injective
        aug gammaAug hgammaAug Xaug hdisjointAug X hfull
  let activeRadial : Finset (Finset (Finset (Option α))) :=
    X.image signature
  have hactiveRadialCard : activeRadial.card = 5 := by
    calc
      activeRadial.card = X.card := by
        exact Finset.card_image_iff.mpr hsignatureInj
      _ = 5 := hX
  have hactiveRadialSubset :
      activeRadial ⊆ sixConicActiveSignatures aug gammaAug Xaug := by
    intro s hs
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hs
    rw [sixConicActiveSignatures]
    exact Finset.mem_image.mpr
      ⟨({none, some x} : Finset (Option α)), hfull x hx, rfl⟩
  rw [← hactiveRadialCard]
  exact Finset.card_le_card hactiveRadialSubset

/-- A five-leaf star disjoint from a selected six-circle has total pair
weight at most fourteen.  Equality fifteen would make all five radial
edges full.  Equal full signatures would force two such edges disjoint,
impossible because they share the hub, so this would produce five active
signatures against the geometric cap four. -/
theorem sixConic_augmentedRadialPairWeight_sum_le_fourteen
    {α : Type u} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (gamma : Erdos506.V1.DeterminedCircle cfg)
    (hgamma : (circleTrace cfg gamma.1).card = 6)
    (X : Finset α) (hX : X.card = 5)
    (hdisjoint : Disjoint (circleTrace cfg gamma.1) X)
    (o : Point2) (hoPoint : o ∉ pointSet cfg)
    (hoGamma : o ∉ (gamma.1.1 : Set Point2)) :
    (∑ x ∈ X,
      sixConicPairWeight (inversionAugmentation cfg o hoPoint)
        (inversionAugmentationGamma cfg gamma hgamma o hoPoint hoGamma)
        {none, some x}) ≤ 14 := by
  classical
  let aug := inversionAugmentation cfg o hoPoint
  let gammaAug :=
    inversionAugmentationGamma cfg gamma hgamma o hoPoint hoGamma
  let Xaug : Finset (Option α) :=
    insert none (X.map Function.Embedding.some)
  let edge : α → Finset (Option α) := fun x => {none, some x}
  let q : α → Nat := fun x => sixConicPairWeight aug gammaAug (edge x)
  change (∑ x ∈ X, q x) ≤ 14
  have hgammaAug : (circleTrace aug gammaAug.1).card = 6 :=
    card_circleTrace_inversionAugmentationGamma
      cfg gamma hgamma o hoPoint hoGamma
  have hdisjointAug : Disjoint (circleTrace aug gammaAug.1) Xaug := by
    exact circleTrace_inversionAugmentationGamma_disjoint_insertMap
      cfg gamma hgamma X hdisjoint o hoPoint hoGamma
  have hedgeCard (x : α) : (edge x).card = 2 := by
    simp [edge]
  have hedgeSubset (x : α) (hx : x ∈ X) : edge x ⊆ Xaug := by
    intro z hz
    simp only [edge, Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl
    · simp [Xaug]
    · simp [Xaug, hx]
  have hedgeDisjoint (x : α) (hx : x ∈ X) :
      Disjoint (edge x) (circleTrace aug gammaAug.1) := by
    exact inversionAugmentation_radialEdge_disjoint_gamma
      cfg gamma hgamma X hdisjoint o hoPoint hoGamma hx
  have hq (x : α) (hx : x ∈ X) : q x ≤ 3 := by
    exact sixConicPairWeight_le_three hgammaAug
      (hedgeCard x) (hedgeDisjoint x hx)
  by_contra hnot
  have hqFull (x : α) (hx : x ∈ X) : q x = 3 := by
    exact finset_all_eq_three_of_card_five_of_sum_not_le_fourteen
      X hX q hq hnot x hx
  have hedgeFull (x : α) (hx : x ∈ X) :
      edge x ∈ sixConicFullEdges aug gammaAug Xaug := by
    apply mem_sixConicFullEdges.mpr
    exact ⟨Finset.mem_powersetCard.mpr
      ⟨hedgeSubset x hx, hedgeCard x⟩, hqFull x hx⟩
  have hradialFull (x : α) (hx : x ∈ X) :
      ({none, some x} : Finset (Option α)) ∈
        sixConicFullEdges aug gammaAug Xaug := by
    simpa [edge] using hedgeFull x hx
  have hfiveLeActive :
      5 ≤ (sixConicActiveSignatures aug gammaAug Xaug).card :=
    sixConic_activeSignatures_card_ge_five_of_radialFull
      aug gammaAug hgammaAug Xaug hdisjointAug X hX hradialFull
  have hactiveCap :
      (sixConicActiveSignatures aug gammaAug Xaug).card ≤ 4 :=
    sixConic_activeSignatures_card_le_four
      aug gammaAug hgammaAug Xaug hdisjointAug
  omega

/-! ## The field-free global bound -/

/-- Field-free global six-conic line-incidence bound. -/
theorem sixConic_line_incidence_le_fourteen
    {α : Type u} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (gamma : Erdos506.V1.DeterminedCircle cfg)
    (hgamma : (circleTrace cfg gamma.1).card = 6)
    (X : Finset α) (hX : X.card = 5)
    (hdisjoint : Disjoint (circleTrace cfg gamma.1) X) :
    sixConicLineIncidence cfg gamma X ≤ 14 := by
  obtain ⟨o, hoPoint, hoGamma, hoLines⟩ :=
    exists_external_point_avoiding_circle_and_determinedLines cfg gamma
  rw [sixConicLineIncidence_eq_sum_radialPairWeight
    cfg gamma hgamma X o hoPoint hoGamma hoLines]
  exact sixConic_augmentedRadialPairWeight_sum_le_fourteen
    cfg gamma hgamma X hX hdisjoint o hoPoint hoGamma

end Erdos506.Incidence
