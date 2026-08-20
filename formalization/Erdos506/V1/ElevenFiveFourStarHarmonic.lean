import Erdos506.V1.ElevenFiveFourStarRealization
import Erdos506.Incidence.InversionHarmonicTransport
import Erdos506.Incidence.ProjectiveLineParamTransport
import Erdos506.Incidence.ProjectiveThreeLineConcurrency
import Erdos506.Incidence.FourStarNormalForm
import Erdos506.Incidence.FourStarMotifRelabel
import Erdos506.Finite.FourStarDegreeProfile

/-!
# The residual four-star harmonic bridge

This module separates the finite four-star link from its real projective
endpoint.  In particular, the `2^6 1^4` profile canonically labels the four
private points; it is not treated as an unnamed choice.  The four actual
size-three lines now give the finite `T`/four-cycle/triangle-pendant
trichotomy without an additional catalogue hypothesis.

The remaining work is geometric: turn the affine line-owner data into a
complete projective covector frame, and identify the surviving finite motif
with the four determinant equations of `FourStarRigidity`.
-/

namespace Erdos506.V1

open Erdos506.Finite
open Erdos506.Incidence
open Erdos506.V3
open Erdos506.V4

universe u

/-- Number of base-line supports through a selected point. -/
noncomputable def fourStarBaseDegree {Point : Type u} [DecidableEq Point]
    (B : Fin 4 → Finset Point) (x : Point) : ℕ :=
  ((Finset.univ : Finset (Fin 4)).filter fun i => x ∈ B i).card

/-- The selected points used by the four base supports. -/
noncomputable def fourStarBaseCarrier {Point : Type u} [DecidableEq Point]
    (B : Fin 4 → Finset Point) : Finset Point :=
  (Finset.univ : Finset (Fin 4)).biUnion B

/-- The degree-one points of a four-star base family. -/
noncomputable def fourStarPrivateSet {Point : Type u} [DecidableEq Point]
    (B : Fin 4 → Finset Point) : Finset Point :=
  (fourStarBaseCarrier B).filter fun x => fourStarBaseDegree B x = 1

/-- The degree-two (base-line intersection) points of a four-star family. -/
noncomputable def fourStarCrossSet {Point : Type u} [DecidableEq Point]
    (B : Fin 4 → Finset Point) : Finset Point :=
  (fourStarBaseCarrier B).filter fun x => fourStarBaseDegree B x = 2

/-- The labelled `2^6 1^4` incidence profile.  The finite saturation theorem
already derives the pairwise-one part for the canonical size-four lines; this
structure isolates the remaining assertion that the six pair intersections
are distinct and that no other base incidences occur. -/
structure FourStarTwoSixOneFourProfile {Point : Type u} [DecidableEq Point]
    (B : Fin 4 → Finset Point) : Prop where
  base_card : ∀ i, (B i).card = 4
  pair_inter_one : ∀ i j, i ≠ j → (B i ∩ B j).card = 1
  carrier_card : (fourStarBaseCarrier B).card = 10
  degree_one_or_two : ∀ x, x ∈ fourStarBaseCarrier B →
    fourStarBaseDegree B x = 1 ∨ fourStarBaseDegree B x = 2
  private_card : (fourStarPrivateSet B).card = 4
  cross_card : (fourStarCrossSet B).card = 6

/-- Adapt the geometry-free saturated four-star profile to the V1 private
label interface.  This is the exact finite bridge used by the pivot's four
canonically indexed size-four line supports. -/
theorem FourStarTwoSixOneFourProfile.ofSaturated
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {B : Fin 4 → Finset Point} (H : IsSaturatedFourStar B) :
    FourStarTwoSixOneFourProfile B where
  base_card := H.base_card
  pair_inter_one := H.pair_inter_one
  carrier_card := by
    simpa [fourStarBaseCarrier, fourStarCarrier] using
      (saturated_fourStar_degree_profile H).carrier_card
  degree_one_or_two := by
    intro x hx
    simpa [fourStarBaseCarrier, fourStarCarrier, fourStarBaseDegree,
      fourStarDegree] using
      (saturated_fourStar_degree_profile H).degree_one_or_two x (by
        simpa [fourStarBaseCarrier, fourStarCarrier] using hx)
  private_card := by
    simpa [fourStarPrivateSet, fourStarDegreeOne, fourStarBaseCarrier,
      fourStarCarrier, fourStarBaseDegree, fourStarDegree] using
      (saturated_fourStar_degree_profile H).degree_one_card
  cross_card := by
    simpa [fourStarCrossSet, fourStarDegreeTwo, fourStarBaseCarrier,
      fourStarCarrier, fourStarBaseDegree, fourStarDegree] using
      (saturated_fourStar_degree_profile H).degree_two_card

/-- The canonical `Fin 4` labelling of degree-one points supplied by the
`2^6 1^4` profile. -/
noncomputable def fourStarPrivateLabelEquiv {Point : Type u} [DecidableEq Point]
    {B : Fin 4 → Finset Point} (P : FourStarTwoSixOneFourProfile B) :
    Fin 4 ≃ ↥(fourStarPrivateSet B) :=
  (Fintype.equivFinOfCardEq (by simpa using P.private_card)).symm

/-- The private point bearing a given canonical four-star vertex label. -/
noncomputable def fourStarPrivateLabel {Point : Type u} [DecidableEq Point]
    {B : Fin 4 → Finset Point} (P : FourStarTwoSixOneFourProfile B) :
    Fin 4 → Point :=
  fun i => (fourStarPrivateLabelEquiv P i).1

theorem fourStarPrivateLabel_mem {Point : Type u} [DecidableEq Point]
    {B : Fin 4 → Finset Point} (P : FourStarTwoSixOneFourProfile B)
    (i : Fin 4) : fourStarPrivateLabel P i ∈ fourStarPrivateSet B :=
  (fourStarPrivateLabelEquiv P i).2

theorem fourStarPrivateLabel_injective {Point : Type u} [DecidableEq Point]
    {B : Fin 4 → Finset Point} (P : FourStarTwoSixOneFourProfile B) :
    Function.Injective (fourStarPrivateLabel P) := by
  intro i j hij
  apply (fourStarPrivateLabelEquiv P).injective
  apply Subtype.ext
  exact hij

/-- Degree-one points lying on a particular base line.  The desired profile
extraction theorem says this finite set has cardinality one for every `i`;
that fact is deliberately kept separate from merely enumerating all four
degree-one points. -/
noncomputable def fourStarPrivateOnBase {Point : Type u} [DecidableEq Point]
    (B : Fin 4 → Finset Point) (i : Fin 4) : Finset Point :=
  B i ∩ fourStarPrivateSet B

/-- The finite degree-profile theorem supplies the local one-private-point
fact needed to choose private labels compatibly with the four base lines. -/
theorem fourStarPrivateOnBase_card_eq_one_of_saturated
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {B : Fin 4 → Finset Point} (H : IsSaturatedFourStar B) (i : Fin 4) :
    (fourStarPrivateOnBase B i).card = 1 := by
  simpa [fourStarPrivateOnBase, fourStarDegreeOneOnBase, fourStarPrivateSet,
    fourStarDegreeOne, fourStarBaseCarrier, fourStarCarrier,
    fourStarBaseDegree, fourStarDegree] using
      fourStar_degreeOneOnBase_card_eq_one H i

/-- An incidence-compatible labelling of the four private points.  Once the
one-private-point-per-base consequence of the `2^6 1^4` profile is proved,
this record is constructible by choosing the unique member of each
`fourStarPrivateOnBase`. -/
structure FourStarPrivateBaseLabelling {Point : Type u} [DecidableEq Point]
    {B : Fin 4 → Finset Point} (P : FourStarTwoSixOneFourProfile B) where
  label : Fin 4 → Point
  label_mem_private : ∀ i, label i ∈ fourStarPrivateSet B
  label_on_base : ∀ i, label i ∈ B i
  label_injective : Function.Injective label

/-- An incidence-compatible labelling exhausts the four private points, so
it canonically upgrades to an equivalence. -/
noncomputable def FourStarPrivateBaseLabelling.toEquiv
    {Point : Type u} [DecidableEq Point]
    {B : Fin 4 → Finset Point} {P : FourStarTwoSixOneFourProfile B}
    (L : FourStarPrivateBaseLabelling P) :
    Fin 4 ≃ ↥(fourStarPrivateSet B) := by
  let f : Fin 4 → ↥(fourStarPrivateSet B) := fun i =>
    ⟨L.label i, L.label_mem_private i⟩
  apply Equiv.ofBijective f
  apply (Fintype.bijective_iff_injective_and_card f).mpr
  constructor
  · intro i j hij
    apply L.label_injective
    exact congrArg Subtype.val hij
  · simp [P.private_card]

@[simp] theorem FourStarPrivateBaseLabelling.toEquiv_apply_val
    {Point : Type u} [DecidableEq Point]
    {B : Fin 4 → Finset Point} {P : FourStarTwoSixOneFourProfile B}
    (L : FourStarPrivateBaseLabelling P) (i : Fin 4) :
    (L.toEquiv i).1 = L.label i := rfl

/-- The trace of a support through an incidence-compatible private-point
labelling.  Unlike `fourStarPrivateTrace`, the vertex index here records the
base line carrying the private point. -/
noncomputable def fourStarPrivateBaseTrace
    {Point : Type u} [DecidableEq Point]
    {B : Fin 4 → Finset Point} {P : FourStarTwoSixOneFourProfile B}
    (L : FourStarPrivateBaseLabelling P) (C : Finset Point) :
    Finset FourStarVertex :=
  (Finset.univ : Finset FourStarVertex).filter fun i => L.label i ∈ C

/-- The incidence-compatible private trace is the pullback of the
intersection with the four private points along `L.toEquiv`. -/
theorem fourStarPrivateBaseTrace_card
    {Point : Type u} [DecidableEq Point]
    {B : Fin 4 → Finset Point} {P : FourStarTwoSixOneFourProfile B}
    (L : FourStarPrivateBaseLabelling P) (C : Finset Point) :
    (fourStarPrivateBaseTrace L C).card =
      (C ∩ fourStarPrivateSet B).card := by
  classical
  let e := L.toEquiv
  let X := ↥(fourStarPrivateBaseTrace L C)
  let Y := ↥(C ∩ fourStarPrivateSet B)
  let f : X → Y := fun i => ⟨L.label i.1, by
    have hi : L.label i.1 ∈ C := by
      simpa [fourStarPrivateBaseTrace] using
        (Finset.mem_filter.mp i.2).2
    exact Finset.mem_inter.mpr ⟨hi, L.label_mem_private i.1⟩⟩
  have hf : Function.Injective f := by
    intro i j hij
    apply Subtype.ext
    apply L.label_injective
    exact congrArg (fun y : Y => y.1) hij
  let g : Y → X := fun (x : Y) => by
    have hx := Finset.mem_inter.mp x.2
    refine ⟨e.symm ⟨x.1, hx.2⟩, ?_⟩
    have hlabel : L.label (e.symm ⟨x.1, hx.2⟩) = x.1 := by
      rw [← L.toEquiv_apply_val]
      change (e (e.symm ⟨x.1, hx.2⟩)).1 = x.1
      simp
    simp only [fourStarPrivateBaseTrace, Finset.mem_filter,
      Finset.mem_univ, true_and]
    simpa [hlabel] using hx.1
  have hg : Function.Injective g := by
    intro (x : Y) (y : Y) hxy
    apply Subtype.ext
    have hx := Finset.mem_inter.mp x.2
    have hy := Finset.mem_inter.mp y.2
    have hindex : e.symm ⟨x.1, hx.2⟩ = e.symm ⟨y.1, hy.2⟩ :=
      congrArg (fun z : X => z.1) hxy
    have hsub : (⟨x.1, hx.2⟩ : ↥(fourStarPrivateSet B)) =
        ⟨y.1, hy.2⟩ := e.symm.injective hindex
    exact congrArg (fun z : ↥(fourStarPrivateSet B) => z.1) hsub
  have hXY := Fintype.card_le_of_injective f hf
  have hYX := Fintype.card_le_of_injective g hg
  have hXcard : Fintype.card X = (fourStarPrivateBaseTrace L C).card := by
    exact Fintype.card_coe _
  have hYcard : Fintype.card Y = (C ∩ fourStarPrivateSet B).card := by
    exact Fintype.card_coe _
  omega

/-- Choose the unique private point on every base line, assuming the local
one-point conclusion of the `2^6 1^4` profile.  This construction is useful
independently of the still-missing double-count proof of that conclusion. -/
noncomputable def fourStarPrivateBaseChoice {Point : Type u} [DecidableEq Point]
    (B : Fin 4 → Finset Point)
    (hprivate : ∀ i, (fourStarPrivateOnBase B i).card = 1) : Fin 4 → Point :=
  fun i => (Finset.card_eq_one.mp (hprivate i)).choose

theorem fourStarPrivateBaseChoice_mem {Point : Type u} [DecidableEq Point]
    (B : Fin 4 → Finset Point)
    (hprivate : ∀ i, (fourStarPrivateOnBase B i).card = 1) (i : Fin 4) :
    fourStarPrivateBaseChoice B hprivate i ∈ fourStarPrivateOnBase B i := by
  rw [(Finset.card_eq_one.mp (hprivate i)).choose_spec]
  simp [fourStarPrivateBaseChoice]

theorem fourStarPrivateBaseChoice_private {Point : Type u} [DecidableEq Point]
    (B : Fin 4 → Finset Point)
    (hprivate : ∀ i, (fourStarPrivateOnBase B i).card = 1) (i : Fin 4) :
    fourStarPrivateBaseChoice B hprivate i ∈ fourStarPrivateSet B :=
  (Finset.mem_inter.mp (fourStarPrivateBaseChoice_mem B hprivate i)).2

theorem fourStarPrivateBaseChoice_on_base {Point : Type u} [DecidableEq Point]
    (B : Fin 4 → Finset Point)
    (hprivate : ∀ i, (fourStarPrivateOnBase B i).card = 1) (i : Fin 4) :
    fourStarPrivateBaseChoice B hprivate i ∈ B i :=
  (Finset.mem_inter.mp (fourStarPrivateBaseChoice_mem B hprivate i)).1

/-- Package the local one-private-point-per-base fact as the labelled
private four-star interface.  Injectivity is kept as a separate field in
the resulting structure because its proof is exactly where the degree-one
predicate must be expanded in the profile extraction. -/
noncomputable def fourStarPrivateBaseLabelling_of_choice
    {Point : Type u} [DecidableEq Point] {B : Fin 4 → Finset Point}
    (P : FourStarTwoSixOneFourProfile B)
    (hprivate : ∀ i, (fourStarPrivateOnBase B i).card = 1)
    (hinjective : Function.Injective (fourStarPrivateBaseChoice B hprivate)) :
    FourStarPrivateBaseLabelling P where
  label := fourStarPrivateBaseChoice B hprivate
  label_mem_private := fourStarPrivateBaseChoice_private B hprivate
  label_on_base := fourStarPrivateBaseChoice_on_base B hprivate
  label_injective := hinjective

/-- The private-label trace of an additional line. -/
noncomputable def fourStarPrivateTrace {Point : Type u} [DecidableEq Point]
    {B : Fin 4 → Finset Point} (P : FourStarTwoSixOneFourProfile B)
    (C : Finset Point) : Finset FourStarVertex :=
  (Finset.univ : Finset FourStarVertex).filter fun i =>
    fourStarPrivateLabel P i ∈ C

/-- Taking the trace through the private-label equivalence is cardinality
preserving: it is simply the intersection of the line support with the four
degree-one points. -/
theorem fourStarPrivateTrace_card
    {Point : Type u} [DecidableEq Point]
    {B : Fin 4 → Finset Point} (P : FourStarTwoSixOneFourProfile B)
    (C : Finset Point) :
    (fourStarPrivateTrace P C).card = (C ∩ fourStarPrivateSet B).card := by
  classical
  let e := fourStarPrivateLabelEquiv P
  let X := ↥(fourStarPrivateTrace P C)
  let Y := ↥(C ∩ fourStarPrivateSet B)
  let f : X → Y := fun i => ⟨fourStarPrivateLabel P i.1, by
    have hi : fourStarPrivateLabel P i.1 ∈ C := by
      simpa [fourStarPrivateTrace] using
        (Finset.mem_filter.mp i.2).2
    exact Finset.mem_inter.mpr ⟨hi, fourStarPrivateLabel_mem P i.1⟩⟩
  have hf : Function.Injective f := by
    intro i j hij
    apply Subtype.ext
    apply fourStarPrivateLabel_injective P
    exact congrArg (fun y : Y => y.1) hij
  let g : Y → X := fun (x : Y) => by
    have hx := Finset.mem_inter.mp x.2
    refine ⟨e.symm ⟨x.1, hx.2⟩, ?_⟩
    have hlabel : fourStarPrivateLabel P (e.symm ⟨x.1, hx.2⟩) = x.1 := by
      change (e (e.symm ⟨x.1, hx.2⟩)).1 = x.1
      simp
    simp only [fourStarPrivateTrace, Finset.mem_filter, Finset.mem_univ,
      true_and]
    simpa [hlabel] using hx.1
  have hg : Function.Injective g := by
    intro (x : Y) (y : Y) hxy
    apply Subtype.ext
    have hx := Finset.mem_inter.mp x.2
    have hy := Finset.mem_inter.mp y.2
    have hindex : e.symm ⟨x.1, hx.2⟩ = e.symm ⟨y.1, hy.2⟩ :=
      congrArg (fun z : X => z.1) hxy
    have hsub : (⟨x.1, hx.2⟩ : ↥(fourStarPrivateSet B)) =
        ⟨y.1, hy.2⟩ := e.symm.injective hindex
    exact congrArg
      (fun z : ↥(fourStarPrivateSet B) => z.1) hsub
  have hXY := Fintype.card_le_of_injective f hf
  have hYX := Fintype.card_le_of_injective g hg
  have hXcard : Fintype.card X = (fourStarPrivateTrace P C).card := by
    exact Fintype.card_coe _
  have hYcard : Fintype.card Y = (C ∩ fourStarPrivateSet B).card := by
    exact Fintype.card_coe _
  omega

/-- Four additional three-lines, represented only by their private-point
traces.  A `T`-star is precisely a trace of size three.  In the complementary
case every trace is a private pair, and their image is the four-edge graph
already classified in `FourStarLink`. -/
structure FourStarAdditionalThreeLineLink {Point : Type u} [DecidableEq Point]
    {B : Fin 4 → Finset Point} (P : FourStarTwoSixOneFourProfile B) where
  privateLabelling : FourStarPrivateBaseLabelling P
  line : Finset (Finset Point)
  line_card : line.card = 4
  line_size : ∀ C ∈ line, C.card = 3

/-- The exceptional `T`-star alternative. -/
def FourStarAdditionalThreeLineLink.IsTStar
    {Point : Type u} [DecidableEq Point] {B : Fin 4 → Finset Point}
    {P : FourStarTwoSixOneFourProfile B}
    (A : FourStarAdditionalThreeLineLink P) : Prop :=
  ∃ C ∈ A.line, (fourStarPrivateBaseTrace A.privateLabelling C).card = 3

/-- The private-pair graph extracted when all four additional lines have
two private labels. -/
noncomputable def FourStarAdditionalThreeLineLink.privatePairFamily
    {Point : Type u} [DecidableEq Point] {B : Fin 4 → Finset Point}
    {P : FourStarTwoSixOneFourProfile B}
    (A : FourStarAdditionalThreeLineLink P) : Finset (Finset FourStarVertex) :=
  A.line.image (fourStarPrivateBaseTrace A.privateLabelling)

/-- The finite trichotomy interface.  Its pair-family hypothesis is the
exact bookkeeping statement still needed from the four size-three line
supports: they must give four distinct two-private-point traces. -/
structure FourStarAdditionalThreeLineClassification
    {Point : Type u} [DecidableEq Point] {B : Fin 4 → Finset Point}
    {P : FourStarTwoSixOneFourProfile B}
    (A : FourStarAdditionalThreeLineLink P) : Prop where
  tStar_or_privatePairs : A.IsTStar ∨
    IsFourStarPrivatePairFamily A.privatePairFamily

/-- Once the finite incidence ledger excludes a `T`-star, the existing
four-edge complement argument gives exactly the cycle/triangle-pendant
dichotomy. -/
theorem fourStar_privatePair_cycle_or_trianglePendant_of_no_tStar
    {Point : Type u} [DecidableEq Point] {B : Fin 4 → Finset Point}
    {P : FourStarTwoSixOneFourProfile B}
    (A : FourStarAdditionalThreeLineLink P)
    (K : FourStarAdditionalThreeLineClassification A)
    (hnoT : ¬ A.IsTStar) :
    IsFourStarFourCycle A.privatePairFamily ∨
      IsFourStarTrianglePendant A.privatePairFamily := by
  rcases K.tStar_or_privatePairs with hT | hpair
  · exact (hnoT hT).elim
  · exact fourStar_privatePair_cycle_or_trianglePendant _ hpair

/-- Determinant-level names for the two real exclusions.  They deliberately
refer to the existing homogeneous skeleton, rather than encoding coordinate
equalities in the finite graph layer. -/
def IsFourStarTStarDeterminantal (F : FourStarProjectiveSkeleton) : Prop :=
  ∃ i j k : Fin 4, i ≠ j ∧ i ≠ k ∧ j ≠ k ∧ fourStarTDet F i j k = 0

/-- The real determinant bridge still required by the finite trichotomy.
The two equivalences are the exact statements that turn finite motifs into
their coordinate obstructions; keeping them together prevents either
exclusion from being accidentally applied to an unrelated labelling. -/
structure FourStarRealMotifBridge {Point : Type u} [DecidableEq Point]
    {B : Fin 4 → Finset Point} {P : FourStarTwoSixOneFourProfile B}
    (A : FourStarAdditionalThreeLineLink P) (F : FourStarProjectiveSkeleton)
    (E : Finset (Finset FourStarVertex)) : Prop where
  tStar_iff_determinantal : A.IsTStar ↔ IsFourStarTStarDeterminantal F
  fourCycle_iff_determinantal : IsFourStarFourCycle A.privatePairFamily ↔
    IsFourStarFourCycle E

/-- If the determinant calculation has excluded both displayed real motifs,
the finite graph classification leaves only triangle-pendant.  This is the
precise gluing lemma to use once the two determinant identities exist. -/
theorem fourStar_trianglePendant_of_real_motif_exclusions
    {Point : Type u} [DecidableEq Point] {B : Fin 4 → Finset Point}
    {P : FourStarTwoSixOneFourProfile B}
    (A : FourStarAdditionalThreeLineLink P)
    (K : FourStarAdditionalThreeLineClassification A)
    (F : FourStarProjectiveSkeleton) (E : Finset (Finset FourStarVertex))
    (R : FourStarRealMotifBridge A F E)
    (hnoT : ¬ IsFourStarTStarDeterminantal F)
    (hnoCycle : ¬ IsFourStarFourCycle E) :
    IsFourStarTrianglePendant A.privatePairFamily := by
  have hnoT' : ¬ A.IsTStar := by
    intro h
    exact hnoT (R.tStar_iff_determinantal.mp h)
  rcases fourStar_privatePair_cycle_or_trianglePendant_of_no_tStar A K hnoT'
    with hcycle | hpendant
  · exact (hnoCycle (R.fourCycle_iff_determinantal.mp hcycle)).elim
  · exact hpendant

/-- A linewise projective parametrisation of a four-point affine support.
This is the smallest honest endpoint for saying that an inverted size-four
line is harmonic: it does not assert a non-existent canonical map from an
arbitrary affine line to `RP¹`. -/
structure FourPointLineHarmonicParameter {Point : Type u} [DecidableEq Point]
    (T : Finset Point) where
  parameter : Point → RealProjectiveOnePoint
  support_card : T.card = 4
  p0 : Point
  p1 : Point
  p2 : Point
  p3 : Point
  support_eq : ({p0, p1, p2, p3} : Finset Point) = T
  distinct : p0 ≠ p1 ∧ p0 ≠ p2 ∧ p0 ≠ p3 ∧ p1 ≠ p2 ∧ p1 ≠ p3 ∧ p2 ≠ p3
  harmonic : RealProjectiveHarmonic
    (parameter p0) (parameter p1) (parameter p2) (parameter p3)

/-- The semantic linewise endpoint: an affine four-support is harmonic after
one specified projective parametrisation.  The structure exposes the
ordering and the bracket theorem rather than silently assuming a canonical
coordinate on every affine line. -/
def IsParametricallyHarmonicFour {Point : Type u} [DecidableEq Point]
    (T : Finset Point) : Prop :=
  Nonempty (FourPointLineHarmonicParameter T)

/-- The four concrete base supports attached to the pivot's canonical
size-four line enumeration. -/
noncomputable def ElevenFivePivotInvertedFourStar.baseSupport
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (H : ElevenFivePivotInvertedFourStar cfg p) : Fin 4 → Finset (AwayFrom p) :=
  fun i => lineSupport (pivotInversion cfg p) (H.sizeFourLine i)

theorem ElevenFivePivotInvertedFourStar.baseSupport_card
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (H : ElevenFivePivotInvertedFourStar cfg p) (i : Fin 4) :
    (H.baseSupport i).card = 4 :=
  H.sizeFourLine_support_card i

theorem ElevenFivePivotInvertedFourStar.baseSupport_inter_card_one
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (H : ElevenFivePivotInvertedFourStar cfg p) {i j : Fin 4} (hij : i ≠ j) :
    (H.baseSupport i ∩ H.baseSupport j).card = 1 :=
  H.sizeFourLine_inter_card_one hij

/-- The four size-four supports use all ten inverted labels.  This is the
finite saturation equality needed to invoke the neutral degree-profile
theorem, obtained from the explicit four-set Bonferroni bound. -/
theorem ElevenFivePivotInvertedFourStar.baseSupport_carrier_card
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (H : ElevenFivePivotInvertedFourStar cfg p) :
    (fourStarBaseCarrier H.baseSupport).card = 10 := by
  let B := H.baseSupport
  have hbound := card_union_four_le_card_union_add_pair_intersections
    (B 0) (B 1) (B 2) (B 3)
  have h0 := H.baseSupport_card 0
  have h1 := H.baseSupport_card 1
  have h2 := H.baseSupport_card 2
  have h3 := H.baseSupport_card 3
  have h01 := H.baseSupport_inter_card_one (i := 0) (j := 1) (by decide)
  have h02 := H.baseSupport_inter_card_one (i := 0) (j := 2) (by decide)
  have h03 := H.baseSupport_inter_card_one (i := 0) (j := 3) (by decide)
  have h12 := H.baseSupport_inter_card_one (i := 1) (j := 2) (by decide)
  have h13 := H.baseSupport_inter_card_one (i := 1) (j := 3) (by decide)
  have h23 := H.baseSupport_inter_card_one (i := 2) (j := 3) (by decide)
  have hcarrier : fourStarBaseCarrier B = fourStarCarrierUnion B := by
    simpa [fourStarBaseCarrier, fourStarCarrier, fourStarCarrierUnion] using
      fourStarCarrier_eq_union B
  rw [h0, h1, h2, h3, h01, h02, h03, h12, h13, h23] at hbound
  change 4 + 4 + 4 + 4 ≤ (fourStarCarrierUnion B).card +
    1 + 1 + 1 + 1 + 1 + 1 at hbound
  rw [← hcarrier] at hbound
  change 4 + 4 + 4 + 4 ≤ (fourStarBaseCarrier H.baseSupport).card +
    1 + 1 + 1 + 1 + 1 + 1 at hbound
  have hupper : (fourStarBaseCarrier B).card ≤ 10 := by
    calc
      (fourStarBaseCarrier B).card ≤ (Finset.univ : Finset (AwayFrom p)).card :=
        Finset.card_le_card (Finset.subset_univ _)
      _ = 10 := by simp [H.inverted_card]
  exact le_antisymm hupper (by omega)

/-- The pivot's canonical base-support family is a neutral saturated
four-star, with no residual cardinality assumption. -/
noncomputable def ElevenFivePivotInvertedFourStar.baseSupportSaturated
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
  (H : ElevenFivePivotInvertedFourStar cfg p) :
    IsSaturatedFourStar H.baseSupport where
  point_card := H.inverted_card
  base_card := H.baseSupport_card
  pair_inter_one := fun _ _ hij => H.baseSupport_inter_card_one hij
  carrier_card := H.baseSupport_carrier_card

/-- Full `2^6 1^4` profile of the actual four size-four inverted supports. -/
noncomputable def ElevenFivePivotInvertedFourStar.baseSupportProfile
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (H : ElevenFivePivotInvertedFourStar cfg p) :
    FourStarTwoSixOneFourProfile H.baseSupport :=
  FourStarTwoSixOneFourProfile.ofSaturated H.baseSupportSaturated

theorem ElevenFivePivotInvertedFourStar.privateOnBase_card_eq_one
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (H : ElevenFivePivotInvertedFourStar cfg p) (i : Fin 4) :
    (fourStarPrivateOnBase H.baseSupport i).card = 1 :=
  fourStarPrivateOnBase_card_eq_one_of_saturated H.baseSupportSaturated i

/-- The private labels are now constructed from the pivot data, rather than
being an independent geometric boundary field. -/
noncomputable def ElevenFivePivotInvertedFourStar.privateBaseLabelling
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (H : ElevenFivePivotInvertedFourStar cfg p) :
    FourStarPrivateBaseLabelling H.baseSupportProfile :=
  fourStarPrivateBaseLabelling_of_choice H.baseSupportProfile
    H.privateOnBase_card_eq_one (by
      intro i j hij
      by_contra hne
      have hmemI := fourStarPrivateBaseChoice_on_base H.baseSupport
        H.privateOnBase_card_eq_one i
      have hmemJ := fourStarPrivateBaseChoice_on_base H.baseSupport
        H.privateOnBase_card_eq_one j
      have hmemJ' : fourStarPrivateBaseChoice H.baseSupport
          H.privateOnBase_card_eq_one i ∈ H.baseSupport j := by
        rw [hij]
        exact hmemJ
      have hprivate := fourStarPrivateBaseChoice_private H.baseSupport
        H.privateOnBase_card_eq_one i
      have hdegree : fourStarBaseDegree H.baseSupport
          (fourStarPrivateBaseChoice H.baseSupport H.privateOnBase_card_eq_one i) = 1 := by
        simpa [fourStarPrivateSet] using (Finset.mem_filter.mp hprivate).2
      have hsub : ({i, j} : Finset (Fin 4)) ⊆
          (Finset.univ.filter fun k =>
            fourStarPrivateBaseChoice H.baseSupport H.privateOnBase_card_eq_one i ∈
              H.baseSupport k) := by
        intro k hk
        rcases Finset.mem_insert.mp hk with rfl | hk
        · simp [hmemI]
        · have hkj : k = j := Finset.mem_singleton.mp hk
          subst k
          simp [hmemJ']
      have hcard : ({i, j} : Finset (Fin 4)).card = 2 := by simp [hne]
      have hle := Finset.card_le_card hsub
      rw [hcard] at hle
      change 2 ≤ fourStarBaseDegree H.baseSupport
        (fourStarPrivateBaseChoice H.baseSupport H.privateOnBase_card_eq_one i) at hle
      omega)

/-- The four size-three inverted lines, enumerated directly from the
`d₄ = 4` pivot row.  This is the concrete source of the four additional
three-line supports required by `FourStarAdditionalThreeLineLink`. -/
noncomputable def ElevenFivePivotInvertedFourStar.sizeThreeLineEquiv
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (H : ElevenFivePivotInvertedFourStar cfg p) :
    Fin 4 ≃ DeterminedLineOfSize (pivotInversion cfg p) 3 := by
  apply (Fintype.equivFinOfCardEq ?_).symm
  rw [← lineCount_eq_card_determinedLineOfSize]
  exact H.inverted_line_profile.2.1

noncomputable def ElevenFivePivotInvertedFourStar.sizeThreeLine
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (H : ElevenFivePivotInvertedFourStar cfg p) :
    Fin 4 → DeterminedLine (pivotInversion cfg p) :=
  fun i => (H.sizeThreeLineEquiv i).1

theorem ElevenFivePivotInvertedFourStar.sizeThreeLine_support_card
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (H : ElevenFivePivotInvertedFourStar cfg p) (i : Fin 4) :
    (lineSupport (pivotInversion cfg p) (H.sizeThreeLine i)).card = 3 :=
  (H.sizeThreeLineEquiv i).2

theorem ElevenFivePivotInvertedFourStar.sizeThreeLine_injective
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (H : ElevenFivePivotInvertedFourStar cfg p) :
    Function.Injective H.sizeThreeLine := by
  intro i j hij
  apply H.sizeThreeLineEquiv.injective
  apply Subtype.ext
  exact hij

/-- The four actual three-line supports adjacent to the saturated four-star. -/
noncomputable def ElevenFivePivotInvertedFourStar.sizeThreeSupportFamily
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (H : ElevenFivePivotInvertedFourStar cfg p) : Finset (Finset (AwayFrom p)) :=
  (Finset.univ : Finset (Fin 4)).image fun i =>
    lineSupport (pivotInversion cfg p) (H.sizeThreeLine i)

theorem ElevenFivePivotInvertedFourStar.sizeThreeSupport_injective
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (H : ElevenFivePivotInvertedFourStar cfg p) : Function.Injective
      (fun i => lineSupport (pivotInversion cfg p) (H.sizeThreeLine i)) := by
  intro i j hij
  by_contra hne
  have hlineNe : H.sizeThreeLine i ≠ H.sizeThreeLine j :=
    H.sizeThreeLine_injective.ne hne
  let Q := pivotInversion cfg p
  let bi : GeometricBlock Q := Sum.inl (H.sizeThreeLine i)
  let bj : GeometricBlock Q := Sum.inl (H.sizeThreeLine j)
  let Li : (blockSystem Q).LineBlock := ⟨bi, rfl⟩
  let Lj : (blockSystem Q).LineBlock := ⟨bj, rfl⟩
  have hLiNe : Li ≠ Lj := by
    intro h
    apply hlineNe
    simpa [Li, Lj, bi, bj] using h
  have hinter := (blockSystem Q).distinct_line_inter_card_lt_two hLiNe
  change (lineSupport Q (H.sizeThreeLine i) ∩
    lineSupport Q (H.sizeThreeLine j)).card < 2 at hinter
  have hijQ : lineSupport Q (H.sizeThreeLine i) =
      lineSupport Q (H.sizeThreeLine j) := by
    simpa [Q] using hij
  rw [hijQ] at hinter
  have hthree := H.sizeThreeLine_support_card j
  change (lineSupport Q (H.sizeThreeLine j)).card = 3 at hthree
  rw [Finset.inter_self, hthree] at hinter
  omega

theorem ElevenFivePivotInvertedFourStar.sizeThreeSupportFamily_card
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (H : ElevenFivePivotInvertedFourStar cfg p) :
    H.sizeThreeSupportFamily.card = 4 := by
  unfold sizeThreeSupportFamily
  rw [Finset.card_image_of_injective _ H.sizeThreeSupport_injective]
  norm_num

/-- The four inverted size-three supports form the finite additional-line
object for the private-point motif classification. -/
noncomputable def ElevenFivePivotInvertedFourStar.additionalThreeLineLink
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (H : ElevenFivePivotInvertedFourStar cfg p) :
    FourStarAdditionalThreeLineLink H.baseSupportProfile where
  privateLabelling := H.privateBaseLabelling
  line := H.sizeThreeSupportFamily
  line_card := H.sizeThreeSupportFamily_card
  line_size := by
    intro C hC
    rcases Finset.mem_image.mp hC with ⟨i, _hi, rfl⟩
    exact H.sizeThreeLine_support_card i

/-- The saturated four base supports cover the full inverted ten-point
universe.  This is the concrete coverage input for the later private-trace
count, rather than an extra hypothesis on the additional three-lines. -/
theorem ElevenFivePivotInvertedFourStar.baseSupport_carrier_eq_univ
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (H : ElevenFivePivotInvertedFourStar cfg p) :
    fourStarBaseCarrier H.baseSupport = Finset.univ := by
  simpa [fourStarBaseCarrier, fourStarCarrier] using
    fourStarCarrier_eq_univ H.baseSupportSaturated

/-- The canonical selected intersection of two distinct size-four base
supports.  This turns the pairwise-one conclusion into concrete labels while
retaining the proof of distinctness in the argument. -/
noncomputable def ElevenFivePivotInvertedFourStar.basePairIntersection
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (H : ElevenFivePivotInvertedFourStar cfg p) (i j : Fin 4) (hij : i ≠ j) :
    AwayFrom p :=
  (Finset.card_eq_one.mp (H.sizeFourLine_inter_card_one hij)).choose

theorem ElevenFivePivotInvertedFourStar.basePairIntersection_mem_left
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (H : ElevenFivePivotInvertedFourStar cfg p) (i j : Fin 4) (hij : i ≠ j) :
    H.basePairIntersection i j hij ∈ H.baseSupport i := by
  have hmem := (Finset.card_eq_one.mp (H.sizeFourLine_inter_card_one hij)).choose_spec
  have hchosen :
      (Finset.card_eq_one.mp (H.sizeFourLine_inter_card_one hij)).choose ∈
        H.baseSupport i ∩ H.baseSupport j := by
    have hsingle := Finset.mem_singleton_self
      (Finset.card_eq_one.mp (H.sizeFourLine_inter_card_one hij)).choose
    rw [← hmem] at hsingle
    exact hsingle
  simpa only [ElevenFivePivotInvertedFourStar.basePairIntersection] using
    (Finset.mem_inter.mp hchosen).1

theorem ElevenFivePivotInvertedFourStar.basePairIntersection_mem_right
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (H : ElevenFivePivotInvertedFourStar cfg p) (i j : Fin 4) (hij : i ≠ j) :
    H.basePairIntersection i j hij ∈ H.baseSupport j := by
  have hmem := (Finset.card_eq_one.mp (H.sizeFourLine_inter_card_one hij)).choose_spec
  have hchosen :
      (Finset.card_eq_one.mp (H.sizeFourLine_inter_card_one hij)).choose ∈
        H.baseSupport i ∩ H.baseSupport j := by
    have hsingle := Finset.mem_singleton_self
      (Finset.card_eq_one.mp (H.sizeFourLine_inter_card_one hij)).choose
    rw [← hmem] at hsingle
    exact hsingle
  simpa only [ElevenFivePivotInvertedFourStar.basePairIntersection] using
    (Finset.mem_inter.mp hchosen).2

/-- No selected inverted point is incident with three distinct base supports.
This is the local incidence form of the saturated degree bound. -/
theorem ElevenFivePivotInvertedFourStar.not_mem_three_baseSupports
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (H : ElevenFivePivotInvertedFourStar cfg p) {i j k : Fin 4}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (x : AwayFrom p) :
    ¬ (x ∈ H.baseSupport i ∧ x ∈ H.baseSupport j ∧ x ∈ H.baseSupport k) := by
  intro hmem
  have hsub : ({i, j, k} : Finset (Fin 4)) ⊆
      (Finset.univ : Finset (Fin 4)).filter fun l => x ∈ H.baseSupport l := by
    intro l hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hl
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rcases hl with rfl | rfl | rfl
    · exact hmem.1
    · exact hmem.2.1
    · exact hmem.2.2
  have hcard : ({i, j, k} : Finset (Fin 4)).card = 3 := by
    simp [hij, hik, hjk]
  have hle := Finset.card_le_card hsub
  rw [hcard] at hle
  have hdegree : fourStarBaseDegree H.baseSupport x ≤ 2 := by
    simpa [fourStarBaseDegree, fourStarDegree] using
      fourStarDegree_le_two H.baseSupportSaturated x
  change 3 ≤ fourStarBaseDegree H.baseSupport x at hle
  omega

/-- The intersections made with two different other bases are distinct on a
fixed base.  In particular these are valid canonical endpoint choices. -/
theorem ElevenFivePivotInvertedFourStar.basePairIntersection_ne_of_three_distinct
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (H : ElevenFivePivotInvertedFourStar cfg p) {i j k : Fin 4}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    H.basePairIntersection i j hij ≠ H.basePairIntersection i k hik := by
  intro heq
  apply H.not_mem_three_baseSupports hij hik hjk
    (H.basePairIntersection i j hij)
  refine ⟨H.basePairIntersection_mem_left i j hij,
    H.basePairIntersection_mem_right i j hij, ?_⟩
  rw [heq]
  exact H.basePairIntersection_mem_right i k hik

/-- Two explicit, distinct partner bases used to select endpoints on every
base support.  The final row is arbitrary; it merely avoids a hidden choice
in the endpoint extraction. -/
def fourStarEndpointMate : Fin 4 → Fin 2 → Fin 4 :=
  ![![1, 2], ![0, 2], ![0, 1], ![0, 1]]

theorem fourStarEndpointMate_ne (i : Fin 4) (r : Fin 2) :
    i ≠ fourStarEndpointMate i r := by
  fin_cases i <;> fin_cases r <;> decide

theorem fourStarEndpointMate_distinct (i : Fin 4) :
    fourStarEndpointMate i 0 ≠ fourStarEndpointMate i 1 := by
  fin_cases i <;> decide

/-- Canonical two selected endpoints on each actual base line, obtained from
two of its labelled base intersections. -/
noncomputable def ElevenFivePivotInvertedFourStar.canonicalEndpoint
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (H : ElevenFivePivotInvertedFourStar cfg p) (i : Fin 4) (r : Fin 2) :
    AwayFrom p :=
  H.basePairIntersection i (fourStarEndpointMate i r)
    (fourStarEndpointMate_ne i r)

theorem ElevenFivePivotInvertedFourStar.canonicalEndpoint_mem
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (H : ElevenFivePivotInvertedFourStar cfg p) (i : Fin 4) (r : Fin 2) :
    H.canonicalEndpoint i r ∈ H.baseSupport i :=
  H.basePairIntersection_mem_left i (fourStarEndpointMate i r)
    (fourStarEndpointMate_ne i r)

theorem ElevenFivePivotInvertedFourStar.canonicalEndpoint_ne
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (H : ElevenFivePivotInvertedFourStar cfg p) (i : Fin 4) :
    H.canonicalEndpoint i 0 ≠ H.canonicalEndpoint i 1 := by
  apply H.basePairIntersection_ne_of_three_distinct
    (fourStarEndpointMate_ne i 0) (fourStarEndpointMate_ne i 1)
    (fourStarEndpointMate_distinct i)

/-- All endpoint and private-label data of the projective boundary are
already forced by the finite `(9,4,4)` pivot row.  The sole omitted field of
`ElevenFiveFourStarGeometricBoundary` is its covector general-position proof. -/
structure ElevenFiveFourStarFiniteEndpointData {Point : Type u} [Fintype Point]
    [DecidableEq Point] {cfg : Configuration Point} {p : Point}
    (H : ElevenFivePivotInvertedFourStar cfg p) where
  endpoint : Fin 4 → Fin 2 → AwayFrom p
  endpoint_mem : ∀ i j, endpoint i j ∈ H.baseSupport i
  endpoint_ne : ∀ i, endpoint i 0 ≠ endpoint i 1
  privateLabel : Fin 4 → AwayFrom p
  private_on : ∀ i, privateLabel i ∈ H.baseSupport i
  private_off : ∀ i j, i ≠ j → privateLabel i ∉ H.baseSupport j
  private_injective : Function.Injective privateLabel

/-- The actual finite boundary data, with no choice of external geometric
labels.  Private labels are the degree-one labels chosen on their own base
supports. -/
noncomputable def ElevenFivePivotInvertedFourStar.finiteEndpointData
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (H : ElevenFivePivotInvertedFourStar cfg p) :
    ElevenFiveFourStarFiniteEndpointData H where
  endpoint := H.canonicalEndpoint
  endpoint_mem := H.canonicalEndpoint_mem
  endpoint_ne := H.canonicalEndpoint_ne
  privateLabel := H.privateBaseLabelling.label
  private_on := H.privateBaseLabelling.label_on_base
  private_off := by
    intro i j hij hmem
    have hprivate := H.privateBaseLabelling.label_mem_private i
    have hdegree : fourStarBaseDegree H.baseSupport
        (H.privateBaseLabelling.label i) = 1 := by
      exact (Finset.mem_filter.mp hprivate).2
    have hmemI := H.privateBaseLabelling.label_on_base i
    have hsub : ({i, j} : Finset (Fin 4)) ⊆
        (Finset.univ : Finset (Fin 4)).filter fun k =>
          H.privateBaseLabelling.label i ∈ H.baseSupport k := by
      intro k hk
      simp only [Finset.mem_insert, Finset.mem_singleton] at hk
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rcases hk with rfl | rfl
      · exact hmemI
      · exact hmem
    have hcard : ({i, j} : Finset (Fin 4)).card = 2 := by simp [hij]
    have hle := Finset.card_le_card hsub
    rw [hcard] at hle
    change 2 ≤ fourStarBaseDegree H.baseSupport
      (H.privateBaseLabelling.label i) at hle
    omega
  private_injective := H.privateBaseLabelling.label_injective

/-- The projective covector of a canonical base line. -/
noncomputable def ElevenFivePivotInvertedFourStar.canonicalBaseCovector
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (H : ElevenFivePivotInvertedFourStar cfg p) (i : Fin 4) : Homogeneous3 :=
  fourStarConcreteCovector (pivotInversion cfg p)
    (H.canonicalEndpoint i 0) (H.canonicalEndpoint i 1)

theorem ElevenFivePivotInvertedFourStar.canonicalBaseCovector_ne_zero
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (H : ElevenFivePivotInvertedFourStar cfg p) (i : Fin 4) :
    H.canonicalBaseCovector i ≠ 0 := by
  apply lineCovector_ne_zero
  exact (pivotInversion cfg p).injective.ne (H.canonicalEndpoint_ne i)

/-- The canonical covector has exactly the finite support incidence of its
base line.  This is the endpoint-specialized version of the concrete
quadrangle incidence lemma, available before general position is known. -/
theorem ElevenFivePivotInvertedFourStar.mem_baseSupport_iff_canonicalIncident
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (H : ElevenFivePivotInvertedFourStar cfg p) (i : Fin 4) (x : AwayFrom p) :
    x ∈ H.baseSupport i ↔ homogeneousIncident (pivotInversion cfg p x)
      (H.canonicalBaseCovector i) := by
  let Q := pivotInversion cfg p
  let A : Erdos506.Finite.KSubset (AwayFrom p) 2 :=
    ⟨{H.canonicalEndpoint i 0, H.canonicalEndpoint i 1}, by
      simp [H.canonicalEndpoint_ne i]⟩
  have hmem : ∀ z ∈ A.1, Q z ∈ (H.sizeFourLine i).1 := by
    intro z hz
    have hz' : z = H.canonicalEndpoint i 0 ∨
        z = H.canonicalEndpoint i 1 := by simpa [A] using hz
    rcases hz' with rfl | rfl
    · exact mem_lineSupport.mp (H.canonicalEndpoint_mem i 0)
    · exact mem_lineSupport.mp (H.canonicalEndpoint_mem i 1)
  have hpair : lineOfPair Q A = (H.sizeFourLine i).1 :=
    lineOfPair_eq_of_mem_of_direction_finrank_one Q A (H.sizeFourLine i).1
      hmem (H.sizeFourLine i).direction_finrank
  have hspan : affineSpan ℝ ({Q (H.canonicalEndpoint i 0),
      Q (H.canonicalEndpoint i 1)} : Set Point2) = (H.sizeFourLine i).1 := by
    calc
      affineSpan ℝ ({Q (H.canonicalEndpoint i 0),
          Q (H.canonicalEndpoint i 1)} : Set Point2) = lineOfPair Q A := by
        simpa [A] using (lineOfPair_pair Q (H.canonicalEndpoint_ne i)).symm
      _ = (H.sizeFourLine i).1 := hpair
  change x ∈ lineSupport Q (H.sizeFourLine i) ↔ _
  rw [mem_lineSupport, ← hspan]
  exact (homogeneousIncident_lineCovector_iff_mem_affineSpan
    (Q.injective.ne (H.canonicalEndpoint_ne i))).symm

/-- The projectivized canonical covector of an actual base line. -/
noncomputable def ElevenFivePivotInvertedFourStar.canonicalProjectiveBaseLine
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (H : ElevenFivePivotInvertedFourStar cfg p) (i : Fin 4) :
    RealProjectivePlane :=
  Projectivization.mk ℝ (H.canonicalBaseCovector i)
    (H.canonicalBaseCovector_ne_zero i)

/-- Different indexed finite base supports yield different projective line
covectors.  Equality of their projective covectors transports both canonical
endpoints from one support onto the other, and the affine pair-spanning API
then identifies the two determined lines. -/
theorem ElevenFivePivotInvertedFourStar.canonicalProjectiveBaseLine_ne
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (H : ElevenFivePivotInvertedFourStar cfg p) {i j : Fin 4} (hij : i ≠ j) :
    H.canonicalProjectiveBaseLine i ≠ H.canonicalProjectiveBaseLine j := by
  intro hprojective
  apply hij
  apply H.sizeFourLine_injective
  let Q := pivotInversion cfg p
  let A : Erdos506.Finite.KSubset (AwayFrom p) 2 :=
    ⟨{H.canonicalEndpoint i 0, H.canonicalEndpoint i 1}, by
      simp [H.canonicalEndpoint_ne i]⟩
  have hmemOwn : ∀ z ∈ A.1, Q z ∈ (H.sizeFourLine i).1 := by
    intro z hz
    have hz' : z = H.canonicalEndpoint i 0 ∨
        z = H.canonicalEndpoint i 1 := by simpa [A] using hz
    rcases hz' with rfl | rfl
    · exact mem_lineSupport.mp (H.canonicalEndpoint_mem i 0)
    · exact mem_lineSupport.mp (H.canonicalEndpoint_mem i 1)
  have hmemOther : ∀ z ∈ A.1, Q z ∈ (H.sizeFourLine j).1 := by
    intro z hz
    have hz' : z = H.canonicalEndpoint i 0 ∨
        z = H.canonicalEndpoint i 1 := by simpa [A] using hz
    rcases hz' with rfl | rfl
    · apply mem_lineSupport.mp
      apply (H.mem_baseSupport_iff_canonicalIncident j _).mpr
      have horth : Projectivization.orthogonal
          (projectivePoint (Q (H.canonicalEndpoint i 0)))
          (H.canonicalProjectiveBaseLine j) := by
        rw [← hprojective]
        change Projectivization.orthogonal
          (projectivePoint (Q (H.canonicalEndpoint i 0)))
          (projectiveLine (Q (H.canonicalEndpoint i 0))
            (Q (H.canonicalEndpoint i 1))
            (Q.injective.ne (H.canonicalEndpoint_ne i)))
        exact Projectivization.orthogonal_comm.mp
          (projectiveLine_orthogonal_left
            (Q.injective.ne (H.canonicalEndpoint_ne i)))
      change homogeneousIncident (Q (H.canonicalEndpoint i 0))
        (H.canonicalBaseCovector j)
      exact (Projectivization.orthogonal_mk
        (homogeneousLift_ne_zero _) (H.canonicalBaseCovector_ne_zero j)).mp horth
    · apply mem_lineSupport.mp
      apply (H.mem_baseSupport_iff_canonicalIncident j _).mpr
      have horth : Projectivization.orthogonal
          (projectivePoint (Q (H.canonicalEndpoint i 1)))
          (H.canonicalProjectiveBaseLine j) := by
        rw [← hprojective]
        change Projectivization.orthogonal
          (projectivePoint (Q (H.canonicalEndpoint i 1)))
          (projectiveLine (Q (H.canonicalEndpoint i 0))
            (Q (H.canonicalEndpoint i 1))
            (Q.injective.ne (H.canonicalEndpoint_ne i)))
        exact Projectivization.orthogonal_comm.mp
          (projectiveLine_orthogonal_right
            (Q.injective.ne (H.canonicalEndpoint_ne i)))
      change homogeneousIncident (Q (H.canonicalEndpoint i 1))
        (H.canonicalBaseCovector j)
      exact (Projectivization.orthogonal_mk
        (homogeneousLift_ne_zero _) (H.canonicalBaseCovector_ne_zero j)).mp horth
  apply Subtype.ext
  exact (lineOfPair_eq_of_mem_of_direction_finrank_one Q A
    (H.sizeFourLine i).1 hmemOwn (H.sizeFourLine i).direction_finrank).symm.trans
      (lineOfPair_eq_of_mem_of_direction_finrank_one Q A
        (H.sizeFourLine j).1 hmemOther (H.sizeFourLine j).direction_finrank)

/-- No three distinct canonical base covectors are dependent.  A vanishing
determinant would give a common projective representative; uniqueness of the
intersection of the first two projective lines identifies it with their
actual selected finite intersection, which would then belong to all three
base supports against the saturated degree profile. -/
theorem ElevenFivePivotInvertedFourStar.canonicalBaseCovector_det_ne_zero
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (H : ElevenFivePivotInvertedFourStar cfg p) {i j k : Fin 4}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    Matrix.det ![H.canonicalBaseCovector i, H.canonicalBaseCovector j,
      H.canonicalBaseCovector k] ≠ 0 := by
  intro hdet
  obtain ⟨r, hrne, hrI, hrJ, hrK⟩ :=
    (det_eq_zero_iff_exists_common_nonzero_homogeneous
      (H.canonicalBaseCovector i) (H.canonicalBaseCovector j)
      (H.canonicalBaseCovector k)).mp hdet
  let Q := pivotInversion cfg p
  let x := H.basePairIntersection i j hij
  have hxI_mem : x ∈ H.baseSupport i :=
    H.basePairIntersection_mem_left i j hij
  have hxJ_mem : x ∈ H.baseSupport j :=
    H.basePairIntersection_mem_right i j hij
  have hxI : H.canonicalBaseCovector i ⬝ᵥ homogeneousLift (Q x) = 0 := by
    rw [dotProduct_comm]
    exact (H.mem_baseSupport_iff_canonicalIncident i x).mp hxI_mem
  have hxJ : H.canonicalBaseCovector j ⬝ᵥ homogeneousLift (Q x) = 0 := by
    rw [dotProduct_comm]
    exact (H.mem_baseSupport_iff_canonicalIncident j x).mp hxJ_mem
  have hprojective : Projectivization.mk ℝ r hrne =
      Projectivization.mk ℝ (homogeneousLift (Q x))
        (homogeneousLift_ne_zero (Q x)) :=
    projectiveCommonPoint_eq_of_two_distinct_covectors
      (H.canonicalBaseCovector_ne_zero i)
      (H.canonicalBaseCovector_ne_zero j) hrne
      (homogeneousLift_ne_zero (Q x))
      (H.canonicalProjectiveBaseLine_ne hij) hrI hrJ hxI hxJ
  have hxK : H.canonicalBaseCovector k ⬝ᵥ homogeneousLift (Q x) = 0 := by
    have horth : Projectivization.orthogonal
        (H.canonicalProjectiveBaseLine k)
        (Projectivization.mk ℝ r hrne) :=
      (Projectivization.orthogonal_mk (H.canonicalBaseCovector_ne_zero k) hrne).mpr hrK
    rw [hprojective] at horth
    exact (Projectivization.orthogonal_mk
      (H.canonicalBaseCovector_ne_zero k) (homogeneousLift_ne_zero (Q x))).mp horth
  have hxK_mem : x ∈ H.baseSupport k :=
    (H.mem_baseSupport_iff_canonicalIncident k x).mpr (by
      change homogeneousLift (Q x) ⬝ᵥ H.canonicalBaseCovector k = 0
      rw [dotProduct_comm]
      exact hxK)
  exact H.not_mem_three_baseSupports hij hik hjk x ⟨hxI_mem, hxJ_mem, hxK_mem⟩

/-- The four actual canonical base covectors form a complete projective
quadrangle.  This is the geometric boundary field formerly left external:
its proof is now reduced to the finite no-three-base-incidence theorem and
projective common-point uniqueness. -/
theorem ElevenFivePivotInvertedFourStar.canonicalBase_general_position
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (H : ElevenFivePivotInvertedFourStar cfg p) :
    CompleteQuadrangleGeneralPosition
      (H.canonicalBaseCovector 0) (H.canonicalBaseCovector 1)
      (H.canonicalBaseCovector 2) (H.canonicalBaseCovector 3) where
  det_abc_ne := H.canonicalBaseCovector_det_ne_zero (by decide) (by decide) (by decide)
  det_abd_ne := H.canonicalBaseCovector_det_ne_zero (by decide) (by decide) (by decide)
  det_acd_ne := H.canonicalBaseCovector_det_ne_zero (by decide) (by decide) (by decide)
  det_bcd_ne := H.canonicalBaseCovector_det_ne_zero (by decide) (by decide) (by decide)

/-- The finite pivot data constructs the full projective boundary, including
general position of the actual line covectors.  No geometric boundary field
remains to be supplied externally. -/
noncomputable def ElevenFivePivotInvertedFourStar.geometricBoundary
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (H : ElevenFivePivotInvertedFourStar cfg p) :
    ElevenFiveFourStarGeometricBoundary H where
  endpoint := H.canonicalEndpoint
  endpoint_mem := H.canonicalEndpoint_mem
  endpoint_ne := H.canonicalEndpoint_ne
  privateLabel := H.privateBaseLabelling.label
  private_on := H.privateBaseLabelling.label_on_base
  private_off := H.finiteEndpointData.private_off
  base_general_position := by
    simpa [ElevenFivePivotInvertedFourStar.canonicalBaseCovector,
      fourStarConcreteCovector] using H.canonicalBase_general_position

/-- Every actual size-three line is contained in the saturated four-star
carrier.  It follows from the ten-point carrier equality, so this statement
does not assume a separate support restriction. -/
theorem ElevenFivePivotInvertedFourStar.sizeThreeSupport_subset_baseCarrier
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (H : ElevenFivePivotInvertedFourStar cfg p) (i : Fin 4) :
    lineSupport (pivotInversion cfg p) (H.sizeThreeLine i) ⊆
      fourStarBaseCarrier H.baseSupport := by
  rw [H.baseSupport_carrier_eq_univ]
  exact Finset.subset_univ _

/-- A size-three line and a size-four base line have at most one selected
point in common.  The proof uses the line owner uniqueness in the block
system; the unequal support sizes rule out equality of the two line owners. -/
theorem ElevenFivePivotInvertedFourStar.sizeThreeSupport_inter_base_lt_two
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (H : ElevenFivePivotInvertedFourStar cfg p) (i j : Fin 4) :
    (lineSupport (pivotInversion cfg p) (H.sizeThreeLine i) ∩
      H.baseSupport j).card < 2 := by
  let Q := pivotInversion cfg p
  have hlineNe : H.sizeThreeLine i ≠ H.sizeFourLine j := by
    intro h
    have hthree := H.sizeThreeLine_support_card i
    rw [h, H.sizeFourLine_support_card j] at hthree
    omega
  let bi : GeometricBlock Q := Sum.inl (H.sizeThreeLine i)
  let bj : GeometricBlock Q := Sum.inl (H.sizeFourLine j)
  let Li : (blockSystem Q).LineBlock := ⟨bi, rfl⟩
  let Lj : (blockSystem Q).LineBlock := ⟨bj, rfl⟩
  have hLiNe : Li ≠ Lj := by
    intro h
    apply hlineNe
    simpa [Li, Lj, bi, bj] using h
  have hinter := (blockSystem Q).distinct_line_inter_card_lt_two hLiNe
  simpa [Q, Li, Lj, bi, bj, geometricBlockSupport,
    ElevenFivePivotInvertedFourStar.baseSupport] using hinter

/-- The private-label trace of the `i`th actual size-three line. -/
noncomputable def ElevenFivePivotInvertedFourStar.sizeThreePrivateTrace
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (H : ElevenFivePivotInvertedFourStar cfg p) (i : Fin 4) :
    Finset FourStarVertex :=
  fourStarPrivateBaseTrace H.privateBaseLabelling
    (lineSupport (pivotInversion cfg p) (H.sizeThreeLine i))

/-- Unfolding the concrete trace records exactly the finite incidence of its
labelled private point with the actual size-three line support. -/
theorem ElevenFivePivotInvertedFourStar.mem_sizeThreePrivateTrace_iff
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (H : ElevenFivePivotInvertedFourStar cfg p) (r i : Fin 4) :
    i ∈ H.sizeThreePrivateTrace r ↔ H.privateBaseLabelling.label i ∈
      lineSupport (pivotInversion cfg p) (H.sizeThreeLine r) := by
  simp [ElevenFivePivotInvertedFourStar.sizeThreePrivateTrace,
    fourStarPrivateBaseTrace]

/-- Every actual size-three line contains at least two of the four private
points.  This is the concrete incidence-count endpoint: coverage gives three
positive base incidences, and the four one-point base intersections leave
room for at most one degree-two point. -/
theorem ElevenFivePivotInvertedFourStar.two_le_sizeThreePrivateTrace_card
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (H : ElevenFivePivotInvertedFourStar cfg p) (i : Fin 4) :
    2 ≤ (H.sizeThreePrivateTrace i).card := by
  let C := lineSupport (pivotInversion cfg p) (H.sizeThreeLine i)
  have hdegree := fourStar_degreeOne_inter_card_ge_two_of_card_three
    H.baseSupportSaturated C (H.sizeThreeLine_support_card i) (fun j => by
      have hlt := H.sizeThreeSupport_inter_base_lt_two i j
      change (C ∩ H.baseSupport j).card < 2 at hlt
      omega)
  have htrace := fourStarPrivateBaseTrace_card H.privateBaseLabelling C
  change 2 ≤ (fourStarPrivateBaseTrace H.privateBaseLabelling C).card
  rw [htrace]
  simpa [fourStarPrivateSet, fourStarDegreeOne, fourStarBaseCarrier,
    fourStarCarrier, fourStarBaseDegree, fourStarDegree] using hdegree

/-- A size-three private trace has at most three labels, because the private
label map is injective into the three-point line support. -/
theorem ElevenFivePivotInvertedFourStar.sizeThreePrivateTrace_card_le_three
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (H : ElevenFivePivotInvertedFourStar cfg p) (i : Fin 4) :
    (H.sizeThreePrivateTrace i).card ≤ 3 := by
  let C := lineSupport (pivotInversion cfg p) (H.sizeThreeLine i)
  have htrace := fourStarPrivateBaseTrace_card H.privateBaseLabelling C
  change (fourStarPrivateBaseTrace H.privateBaseLabelling C).card ≤ 3
  rw [htrace]
  calc
    (C ∩ fourStarPrivateSet H.baseSupport).card ≤ C.card :=
      Finset.card_le_card (Finset.inter_subset_left)
    _ = 3 := H.sizeThreeLine_support_card i

/-- Thus every size-three line has a two- or three-private-point trace. -/
theorem ElevenFivePivotInvertedFourStar.sizeThreePrivateTrace_card_two_or_three
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (H : ElevenFivePivotInvertedFourStar cfg p) (i : Fin 4) :
    (H.sizeThreePrivateTrace i).card = 2 ∨
      (H.sizeThreePrivateTrace i).card = 3 := by
  have hlow := H.two_le_sizeThreePrivateTrace_card i
  have hupp := H.sizeThreePrivateTrace_card_le_three i
  omega

/-- Distinct actual size-three lines meet in fewer than two selected points.
This is the direct line-owner form of the pair-uniqueness constraint used to
separate their private traces. -/
theorem ElevenFivePivotInvertedFourStar.sizeThreeSupport_inter_lt_two
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (H : ElevenFivePivotInvertedFourStar cfg p) {i j : Fin 4} (hij : i ≠ j) :
    (lineSupport (pivotInversion cfg p) (H.sizeThreeLine i) ∩
      lineSupport (pivotInversion cfg p) (H.sizeThreeLine j)).card < 2 := by
  let Q := pivotInversion cfg p
  let bi : GeometricBlock Q := Sum.inl (H.sizeThreeLine i)
  let bj : GeometricBlock Q := Sum.inl (H.sizeThreeLine j)
  let Li : (blockSystem Q).LineBlock := ⟨bi, rfl⟩
  let Lj : (blockSystem Q).LineBlock := ⟨bj, rfl⟩
  have hLiNe : Li ≠ Lj := by
    intro h
    apply hij
    apply H.sizeThreeLine_injective
    simpa [Li, Lj, bi, bj] using h
  have hinter := (blockSystem Q).distinct_line_inter_card_lt_two hLiNe
  simpa [Q, Li, Lj, bi, bj, geometricBlockSupport] using hinter

/-- If no three-line has a three-private-point trace, distinct three-lines
give distinct private pairs.  Two coincident traces would place two distinct
private labels on both geometric lines, contradicting unique line ownership. -/
theorem ElevenFivePivotInvertedFourStar.sizeThreePrivateTrace_injective_of_no_tStar
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (H : ElevenFivePivotInvertedFourStar cfg p)
    (hnoT : ¬ H.additionalThreeLineLink.IsTStar) :
    Function.Injective H.sizeThreePrivateTrace := by
  classical
  intro i j htrace
  by_contra hij
  have hcard : (H.sizeThreePrivateTrace i).card = 2 := by
    rcases H.sizeThreePrivateTrace_card_two_or_three i with htwo | hthree
    · exact htwo
    · apply False.elim
      apply hnoT
      refine ⟨lineSupport (pivotInversion cfg p) (H.sizeThreeLine i), ?_, ?_⟩
      · exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
      · exact hthree
  obtain ⟨v, w, hvw, htraceEq⟩ := Finset.card_eq_two.mp hcard
  have hvI : H.privateBaseLabelling.label v ∈
      lineSupport (pivotInversion cfg p) (H.sizeThreeLine i) := by
    have hv : v ∈ H.sizeThreePrivateTrace i := by rw [htraceEq]; simp
    exact (Finset.mem_filter.mp hv).2
  have hwI : H.privateBaseLabelling.label w ∈
      lineSupport (pivotInversion cfg p) (H.sizeThreeLine i) := by
    have hw : w ∈ H.sizeThreePrivateTrace i := by rw [htraceEq]; simp
    exact (Finset.mem_filter.mp hw).2
  have hvJ : H.privateBaseLabelling.label v ∈
      lineSupport (pivotInversion cfg p) (H.sizeThreeLine j) := by
    have hv : v ∈ H.sizeThreePrivateTrace j := by rw [← htrace]; exact (by rw [htraceEq]; simp)
    exact (Finset.mem_filter.mp hv).2
  have hwJ : H.privateBaseLabelling.label w ∈
      lineSupport (pivotInversion cfg p) (H.sizeThreeLine j) := by
    have hw : w ∈ H.sizeThreePrivateTrace j := by rw [← htrace]; exact (by rw [htraceEq]; simp)
    exact (Finset.mem_filter.mp hw).2
  have hlabelNe : H.privateBaseLabelling.label v ≠
      H.privateBaseLabelling.label w :=
    H.privateBaseLabelling.label_injective.ne hvw
  have hsub : {H.privateBaseLabelling.label v,
      H.privateBaseLabelling.label w} ⊆
      lineSupport (pivotInversion cfg p) (H.sizeThreeLine i) ∩
        lineSupport (pivotInversion cfg p) (H.sizeThreeLine j) := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact Finset.mem_inter.mpr ⟨hvI, hvJ⟩
    · exact Finset.mem_inter.mpr ⟨hwI, hwJ⟩
  have hle := Finset.card_le_card hsub
  have htwo : ({H.privateBaseLabelling.label v,
      H.privateBaseLabelling.label w} : Finset (AwayFrom p)).card = 2 := by
    simp [hlabelNe]
  rw [htwo] at hle
  have hlt := H.sizeThreeSupport_inter_lt_two hij
  omega

/-- Distinct actual size-three supports have distinct private traces even
without excluding a `T` trace: every trace has at least two labels, so two
equal traces would put two distinct private points on both supports. -/
theorem ElevenFivePivotInvertedFourStar.sizeThreePrivateTrace_injective
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (H : ElevenFivePivotInvertedFourStar cfg p) :
    Function.Injective H.sizeThreePrivateTrace := by
  classical
  intro i j htrace
  by_contra hij
  obtain ⟨T, hTsub, hTcard⟩ :=
    Finset.exists_subset_card_eq (H.two_le_sizeThreePrivateTrace_card i)
  obtain ⟨v, w, hvw, hT⟩ := Finset.card_eq_two.mp hTcard
  have hvI : H.privateBaseLabelling.label v ∈
      lineSupport (pivotInversion cfg p) (H.sizeThreeLine i) := by
    apply (H.mem_sizeThreePrivateTrace_iff i v).mp
    apply hTsub
    rw [hT]
    simp
  have hwI : H.privateBaseLabelling.label w ∈
      lineSupport (pivotInversion cfg p) (H.sizeThreeLine i) := by
    apply (H.mem_sizeThreePrivateTrace_iff i w).mp
    apply hTsub
    rw [hT]
    simp
  have hvJ : H.privateBaseLabelling.label v ∈
      lineSupport (pivotInversion cfg p) (H.sizeThreeLine j) := by
    apply (H.mem_sizeThreePrivateTrace_iff j v).mp
    rw [← htrace]
    apply hTsub
    rw [hT]
    simp
  have hwJ : H.privateBaseLabelling.label w ∈
      lineSupport (pivotInversion cfg p) (H.sizeThreeLine j) := by
    apply (H.mem_sizeThreePrivateTrace_iff j w).mp
    rw [← htrace]
    apply hTsub
    rw [hT]
    simp
  have hlabelNe : H.privateBaseLabelling.label v ≠
      H.privateBaseLabelling.label w :=
    H.privateBaseLabelling.label_injective.ne hvw
  have hsub : {H.privateBaseLabelling.label v,
      H.privateBaseLabelling.label w} ⊆
      lineSupport (pivotInversion cfg p) (H.sizeThreeLine i) ∩
        lineSupport (pivotInversion cfg p) (H.sizeThreeLine j) := by
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact Finset.mem_inter.mpr ⟨hvI, hvJ⟩
    · have hx' : x = H.privateBaseLabelling.label w := Finset.mem_singleton.mp hx
      subst x
      exact Finset.mem_inter.mpr ⟨hwI, hwJ⟩
  have htwo : ({H.privateBaseLabelling.label v,
      H.privateBaseLabelling.label w} : Finset (AwayFrom p)).card = 2 := by
    simp [hlabelNe]
  have hle := Finset.card_le_card hsub
  rw [htwo] at hle
  have hlt := H.sizeThreeSupport_inter_lt_two hij
  omega

/-- The actual private-trace family is a four-element image of the four
size-three lines. -/
noncomputable def ElevenFivePivotInvertedFourStar.sizeThreePrivateTraceFamily
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (H : ElevenFivePivotInvertedFourStar cfg p) : Finset (Finset FourStarVertex) :=
  (Finset.univ : Finset (Fin 4)).image H.sizeThreePrivateTrace

/-- The intersection of two private traces is no larger than the
intersection of their actual size-three supports. -/
theorem ElevenFivePivotInvertedFourStar.sizeThreePrivateTrace_inter_card_le_one
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (H : ElevenFivePivotInvertedFourStar cfg p) {r s : Fin 4} (hrs : r ≠ s) :
    (H.sizeThreePrivateTrace r ∩ H.sizeThreePrivateTrace s).card ≤ 1 := by
  classical
  let X := ↑(H.sizeThreePrivateTrace r ∩ H.sizeThreePrivateTrace s)
  let Y := ↑(lineSupport (pivotInversion cfg p) (H.sizeThreeLine r) ∩
    lineSupport (pivotInversion cfg p) (H.sizeThreeLine s))
  let f : X → Y := fun v => ⟨H.privateBaseLabelling.label v.1, by
    rcases Finset.mem_inter.mp v.2 with ⟨hvr, hvs⟩
    exact Finset.mem_inter.mpr ⟨(H.mem_sizeThreePrivateTrace_iff r v).mp hvr,
      (H.mem_sizeThreePrivateTrace_iff s v).mp hvs⟩⟩
  have hf : Function.Injective f := by
    intro a b hab
    apply Subtype.ext
    apply H.privateBaseLabelling.label_injective
    exact congrArg (fun z : Y => z.1) hab
  have hle := Fintype.card_le_of_injective f hf
  have hX : Fintype.card X =
      (H.sizeThreePrivateTrace r ∩ H.sizeThreePrivateTrace s).card :=
    Fintype.card_coe _
  have hY : Fintype.card Y =
      (lineSupport (pivotInversion cfg p) (H.sizeThreeLine r) ∩
        lineSupport (pivotInversion cfg p) (H.sizeThreeLine s)).card :=
    Fintype.card_coe _
  rw [hX, hY] at hle
  have hlt := H.sizeThreeSupport_inter_lt_two hrs
  omega

/-- An actual `T` alternative supplies the full finite trace-family
certificate used by `FourStarMotifRelabel`.  Its four traces are distinct by
the two-private-point lower bound, and distinct supports have trace
intersection at most one. -/
theorem ElevenFivePivotInvertedFourStar.sizeThreePrivateTraceFamily_isTStarTraceFamily_of_tStar
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (H : ElevenFivePivotInvertedFourStar cfg p)
    (hT : H.additionalThreeLineLink.IsTStar) :
    IsFourStarTStarTraceFamily H.sizeThreePrivateTraceFamily := by
  classical
  constructor
  · unfold ElevenFivePivotInvertedFourStar.sizeThreePrivateTraceFamily
    rw [Finset.card_image_of_injective _ H.sizeThreePrivateTrace_injective]
    norm_num
  constructor
  · intro T hTmem
    rcases Finset.mem_image.mp hTmem with ⟨r, _hr, rfl⟩
    exact H.sizeThreePrivateTrace_card_two_or_three r
  constructor
  · intro T hTmem U hUmem hne
    rcases Finset.mem_image.mp hTmem with ⟨r, _hr, rfl⟩
    rcases Finset.mem_image.mp hUmem with ⟨s, _hs, rfl⟩
    apply H.sizeThreePrivateTrace_inter_card_le_one
    intro hrs
    subst s
    exact hne rfl
  · rcases hT with ⟨C, hC, hCcard⟩
    rcases Finset.mem_image.mp hC with ⟨r, _hr, hCr⟩
    refine ⟨H.sizeThreePrivateTrace r,
      Finset.mem_image.mpr ⟨r, Finset.mem_univ _, rfl⟩, ?_⟩
    subst C
    change (H.sizeThreePrivateTrace r).card = 3 at hCcard
    exact hCcard

theorem ElevenFivePivotInvertedFourStar.additionalThreeLine_privatePairFamily_eq
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (H : ElevenFivePivotInvertedFourStar cfg p) :
    H.additionalThreeLineLink.privatePairFamily = H.sizeThreePrivateTraceFamily := by
  classical
  simp only [FourStarAdditionalThreeLineLink.privatePairFamily,
    ElevenFivePivotInvertedFourStar.additionalThreeLineLink,
    ElevenFivePivotInvertedFourStar.sizeThreeSupportFamily,
    ElevenFivePivotInvertedFourStar.sizeThreePrivateTraceFamily,
    Finset.image_image]
  apply Finset.image_congr
  intro i hi
  rfl

/-- The four size-three lines yield the concrete finite trichotomy: either a
`T`-trace occurs, or their four distinct traces form a four-edge graph on the
private labels. -/
theorem ElevenFivePivotInvertedFourStar.additionalThreeLineClassification
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (H : ElevenFivePivotInvertedFourStar cfg p) :
    FourStarAdditionalThreeLineClassification H.additionalThreeLineLink := by
  classical
  by_cases hT : H.additionalThreeLineLink.IsTStar
  · exact ⟨Or.inl hT⟩
  · refine ⟨Or.inr ?_⟩
    rw [H.additionalThreeLine_privatePairFamily_eq]
    constructor
    · unfold ElevenFivePivotInvertedFourStar.sizeThreePrivateTraceFamily
      rw [Finset.card_image_of_injective _
        (H.sizeThreePrivateTrace_injective_of_no_tStar hT)]
      norm_num
    · intro e he
      rcases Finset.mem_image.mp he with ⟨i, _hi, rfl⟩
      apply Finset.mem_powersetCard.mpr
      refine ⟨Finset.subset_univ _, ?_⟩
      rcases H.sizeThreePrivateTrace_card_two_or_three i with htwo | hthree
      · exact htwo
      · exact False.elim (hT ⟨lineSupport (pivotInversion cfg p)
          (H.sizeThreeLine i), Finset.mem_image.mpr
            ⟨i, Finset.mem_univ _, rfl⟩, hthree⟩)

/-- Fully unconditional finite motif trichotomy for the pivot's four
additional lines.  The `T` alternative is a genuine three-private-point
line; otherwise the four-edge graph is exactly a four-cycle or a
triangle-pendant. -/
theorem ElevenFivePivotInvertedFourStar.additionalThreeLine_tStar_or_cycle_or_trianglePendant
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (H : ElevenFivePivotInvertedFourStar cfg p) :
    H.additionalThreeLineLink.IsTStar ∨
      IsFourStarFourCycle H.additionalThreeLineLink.privatePairFamily ∨
        IsFourStarTrianglePendant H.additionalThreeLineLink.privatePairFamily := by
  by_cases hT : H.additionalThreeLineLink.IsTStar
  · exact Or.inl hT
  · right
    exact fourStar_privatePair_cycle_or_trianglePendant_of_no_tStar
      H.additionalThreeLineLink H.additionalThreeLineClassification hT

/-- Three selected points on one actual determined affine line have vanishing
homogeneous collinearity determinant.  Keeping this elementary conversion
local makes the `T` part of the trace-to-determinant bridge use the genuine
size-three line owner, rather than a separately postulated projective line. -/
theorem determinant_zero_of_three_mem_determinedLine
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {Q : Configuration Point} (L : DeterminedLine Q) (a b c : Point)
    (hab : a ≠ b) (ha : a ∈ lineSupport Q L)
    (hb : b ∈ lineSupport Q L) (hc : c ∈ lineSupport Q L) :
    Matrix.det ![homogeneousLift (Q a), homogeneousLift (Q b),
      homogeneousLift (Q c)] = 0 := by
  let A : Erdos506.Finite.KSubset Point 2 :=
    ⟨{a, b}, by simp [hab]⟩
  have hmem : ∀ z ∈ A.1, Q z ∈ L.1 := by
    intro z hz
    have hz' : z = a ∨ z = b := by simpa [A] using hz
    rcases hz' with rfl | rfl
    · exact mem_lineSupport.mp ha
    · exact mem_lineSupport.mp hb
  have hpair : lineOfPair Q A = L.1 :=
    lineOfPair_eq_of_mem_of_direction_finrank_one Q A L.1 hmem
      L.direction_finrank
  have hspan : affineSpan ℝ ({Q a, Q b} : Set Point2) = L.1 := by
    calc
      affineSpan ℝ ({Q a, Q b} : Set Point2) = lineOfPair Q A := by
        simpa [A] using (lineOfPair_pair Q hab).symm
      _ = L.1 := hpair
  apply (homogeneousIncident_lineCovector_iff_det_eq_zero (Q a) (Q b) (Q c)).mp
  apply (homogeneousIncident_lineCovector_iff_mem_affineSpan
    (Q.injective.ne hab)).mpr
  rw [hspan]
  exact mem_lineSupport.mp hc

/-- A three-private-point trace of an actual size-three support gives the
corresponding `T` determinant equation in the concrete projective skeleton.
This is the `t_zero` field of `FourStarTraceDeterminantData`; the remaining
`s_zero` field additionally has to identify the third selected point of a
private-pair trace with the opposite base intersection. -/
theorem ElevenFivePivotInvertedFourStar.sizeThreePrivateTrace_tDet_zero
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (H : ElevenFivePivotInvertedFourStar cfg p)
    {r i j k : Fin 4}
    (htrace : H.sizeThreePrivateTrace r = ({i, j, k} : Finset FourStarVertex)) :
    fourStarTDet (H.toProjectiveSkeleton H.geometricBoundary) i j k = 0 := by
  classical
  by_cases hij : i = j
  · subst j
    unfold fourStarTDet
    apply Matrix.det_zero_of_row_eq (i := (0 : Fin 3)) (j := (1 : Fin 3))
    · decide
    · rfl
  · have hi : i ∈ H.sizeThreePrivateTrace r := by
      rw [htrace]
      simp
    have hj : j ∈ H.sizeThreePrivateTrace r := by
      rw [htrace]
      simp
    have hk : k ∈ H.sizeThreePrivateTrace r := by
      rw [htrace]
      simp
    have hi' : H.privateBaseLabelling.label i ∈
        lineSupport (pivotInversion cfg p) (H.sizeThreeLine r) := by
      simpa [ElevenFivePivotInvertedFourStar.sizeThreePrivateTrace] using
        (Finset.mem_filter.mp hi).2
    have hj' : H.privateBaseLabelling.label j ∈
        lineSupport (pivotInversion cfg p) (H.sizeThreeLine r) := by
      simpa [ElevenFivePivotInvertedFourStar.sizeThreePrivateTrace] using
        (Finset.mem_filter.mp hj).2
    have hk' : H.privateBaseLabelling.label k ∈
        lineSupport (pivotInversion cfg p) (H.sizeThreeLine r) := by
      simpa [ElevenFivePivotInvertedFourStar.sizeThreePrivateTrace] using
        (Finset.mem_filter.mp hk).2
    have hlabel : H.privateBaseLabelling.label i ≠
        H.privateBaseLabelling.label j :=
      H.privateBaseLabelling.label_injective.ne hij
    change Matrix.det ![
      homogeneousLift (pivotInversion cfg p (H.privateBaseLabelling.label i)),
      homogeneousLift (pivotInversion cfg p (H.privateBaseLabelling.label j)),
      homogeneousLift (pivotInversion cfg p (H.privateBaseLabelling.label k))] = 0
    exact determinant_zero_of_three_mem_determinedLine
      (H.sizeThreeLine r) _ _ _ hlabel hi' hj' hk'

/-- The actual trace-family version of the preceding `T` conversion. -/
theorem ElevenFivePivotInvertedFourStar.sizeThreePrivateTraceFamily_tDet_zero
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (H : ElevenFivePivotInvertedFourStar cfg p)
    {i j k : Fin 4}
    (hmem : ({i, j, k} : Finset FourStarVertex) ∈
      H.sizeThreePrivateTraceFamily) :
    fourStarTDet (H.toProjectiveSkeleton H.geometricBoundary) i j k = 0 := by
  rcases Finset.mem_image.mp hmem with ⟨r, _hr, htrace⟩
  exact H.sizeThreePrivateTrace_tDet_zero htrace

/-- The two elements complementary to a genuine private pair are distinct. -/
theorem fourStar_complement_pair_ne
    {i j k l : FourStarVertex}
    (hijcard : ({i, j} : Finset FourStarVertex).card = 2)
    (hcomp : ({k, l} : Finset FourStarVertex) =
      (Finset.univ : Finset FourStarVertex) \ {i, j}) :
    k ≠ l := by
  intro hkl
  subst l
  have hright : ((Finset.univ : Finset FourStarVertex) \ {i, j}).card = 2 := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _)]
    norm_num [hijcard]
  have hleft : ({k, k} : Finset FourStarVertex).card = 1 := by simp
  have hcard := congrArg Finset.card hcomp
  rw [hleft, hright] at hcard
  omega

/-- A private-pair trace on an actual size-three line contains the selected
intersection of the two complementary bases.  The proof is entirely finite:
the third point is non-private, hence has base degree two; the line already
meets the two private bases once, so its two bases are precisely the two
complementary ones. -/
theorem ElevenFivePivotInvertedFourStar.basePairIntersection_mem_sizeThreeSupport_of_trace_pair
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (H : ElevenFivePivotInvertedFourStar cfg p)
    (r i j k l : Fin 4)
    (hijcard : ({i, j} : Finset FourStarVertex).card = 2)
    (htrace : H.sizeThreePrivateTrace r = ({i, j} : Finset FourStarVertex))
    (hkl : k ≠ l)
    (hcomp : ({k, l} : Finset FourStarVertex) =
      (Finset.univ : Finset FourStarVertex) \ {i, j}) :
    H.basePairIntersection k l hkl ∈
      lineSupport (pivotInversion cfg p) (H.sizeThreeLine r) := by
  classical
  let C := lineSupport (pivotInversion cfg p) (H.sizeThreeLine r)
  have hCcard : C.card = 3 := H.sizeThreeLine_support_card r
  have hij : i ≠ j := by
    intro heq
    subst j
    simp at hijcard
  have htraceCard : (H.sizeThreePrivateTrace r).card = 2 := by
    rw [htrace]
    exact hijcard
  have hprivateCard : (C ∩ fourStarPrivateSet H.baseSupport).card = 2 := by
    rw [← fourStarPrivateBaseTrace_card H.privateBaseLabelling C]
    simpa [C, ElevenFivePivotInvertedFourStar.sizeThreePrivateTrace] using
      htraceCard
  obtain ⟨x, hxC, hxprivate⟩ : ∃ x ∈ C, x ∉ fourStarPrivateSet H.baseSupport := by
    by_contra h
    push_neg at h
    have hsub : C ⊆ fourStarPrivateSet H.baseSupport := by
      intro x hx
      exact h x hx
    have hinter : C ∩ fourStarPrivateSet H.baseSupport = C :=
      Finset.inter_eq_left.mpr hsub
    rw [hinter, hCcard] at hprivateCard
    omega
  have hxcarrier : x ∈ fourStarBaseCarrier H.baseSupport :=
    H.sizeThreeSupport_subset_baseCarrier r hxC
  have hxdegree : fourStarBaseDegree H.baseSupport x = 2 := by
    rcases H.baseSupportProfile.degree_one_or_two x hxcarrier with hdeg | hdeg
    · exfalso
      apply hxprivate
      exact Finset.mem_filter.mpr ⟨hxcarrier, hdeg⟩
    · exact hdeg
  have hiC : H.privateBaseLabelling.label i ∈ C := by
    apply (H.mem_sizeThreePrivateTrace_iff r i).mp
    rw [htrace]
    simp
  have hjC : H.privateBaseLabelling.label j ∈ C := by
    apply (H.mem_sizeThreePrivateTrace_iff r j).mp
    rw [htrace]
    simp
  have hxne_i : x ≠ H.privateBaseLabelling.label i := by
    intro hxi
    apply hxprivate
    rw [hxi]
    exact H.privateBaseLabelling.label_mem_private i
  have hxne_j : x ≠ H.privateBaseLabelling.label j := by
    intro hxj
    apply hxprivate
    rw [hxj]
    exact H.privateBaseLabelling.label_mem_private j
  have hxnot_i : x ∉ H.baseSupport i := by
    intro hxi
    have hsub : ({H.privateBaseLabelling.label i, x} : Finset (AwayFrom p)) ⊆
        C ∩ H.baseSupport i := by
      intro y hy
      rcases (Finset.mem_insert.mp hy) with hy | hy
      · subst y
        exact Finset.mem_inter.mpr ⟨hiC,
          H.privateBaseLabelling.label_on_base i⟩
      · have hy' : y = x := Finset.mem_singleton.mp hy
        subst y
        exact Finset.mem_inter.mpr ⟨hxC, hxi⟩
    have hcard : ({H.privateBaseLabelling.label i, x} : Finset (AwayFrom p)).card = 2 :=
      Finset.card_pair_eq_two_iff.mpr hxne_i.symm
    have hle := Finset.card_le_card hsub
    rw [hcard] at hle
    have hlt := H.sizeThreeSupport_inter_base_lt_two r i
    change (C ∩ H.baseSupport i).card < 2 at hlt
    omega
  have hxnot_j : x ∉ H.baseSupport j := by
    intro hxj
    have hsub : ({H.privateBaseLabelling.label j, x} : Finset (AwayFrom p)) ⊆
        C ∩ H.baseSupport j := by
      intro y hy
      rcases (Finset.mem_insert.mp hy) with hy | hy
      · subst y
        exact Finset.mem_inter.mpr ⟨hjC,
          H.privateBaseLabelling.label_on_base j⟩
      · have hy' : y = x := Finset.mem_singleton.mp hy
        subst y
        exact Finset.mem_inter.mpr ⟨hxC, hxj⟩
    have hcard : ({H.privateBaseLabelling.label j, x} : Finset (AwayFrom p)).card = 2 :=
      Finset.card_pair_eq_two_iff.mpr hxne_j.symm
    have hle := Finset.card_le_card hsub
    rw [hcard] at hle
    have hlt := H.sizeThreeSupport_inter_base_lt_two r j
    change (C ∩ H.baseSupport j).card < 2 at hlt
    omega
  let I : Finset (Fin 4) :=
    (Finset.univ : Finset (Fin 4)).filter fun a => x ∈ H.baseSupport a
  have hIcard : I.card = 2 := by
    simpa [I, fourStarBaseDegree] using hxdegree
  have hIsub : I ⊆ ({k, l} : Finset FourStarVertex) := by
    intro a ha
    rw [hcomp]
    refine Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, ?_⟩
    intro haij
    rcases Finset.mem_insert.mp haij with hai | haj
    · subst a
      exact hxnot_i (Finset.mem_filter.mp ha).2
    · have haj' : a = j := Finset.mem_singleton.mp haj
      subst a
      exact hxnot_j (Finset.mem_filter.mp ha).2
  have hxk : x ∈ H.baseSupport k := by
    by_contra hxk
    have hIsub' : I ⊆ ({l} : Finset FourStarVertex) := by
      intro a ha
      rcases (Finset.mem_insert.mp (hIsub ha)) with hak | hal
      · subst a
        exact False.elim (hxk (Finset.mem_filter.mp ha).2)
      · have hal' : a = l := Finset.mem_singleton.mp hal
        subst a
        simp
    have hle := Finset.card_le_card hIsub'
    rw [hIcard] at hle
    norm_num at hle
  have hxl : x ∈ H.baseSupport l := by
    by_contra hxl
    have hIsub' : I ⊆ ({k} : Finset FourStarVertex) := by
      intro a ha
      rcases (Finset.mem_insert.mp (hIsub ha)) with hak | hal
      · subst a
        simp
      · have hal' : a = l := Finset.mem_singleton.mp hal
        subst a
        exact False.elim (hxl (Finset.mem_filter.mp ha).2)
    have hle := Finset.card_le_card hIsub'
    rw [hIcard] at hle
    norm_num at hle
  have hsingle : H.baseSupport k ∩ H.baseSupport l =
      {H.basePairIntersection k l hkl} := by
    simpa only [ElevenFivePivotInvertedFourStar.basePairIntersection] using
      (Finset.card_eq_one.mp (H.sizeFourLine_inter_card_one hkl)).choose_spec
  have hxsingle : x ∈
      ({H.basePairIntersection k l hkl} : Finset (AwayFrom p)) := by
    rw [← hsingle]
    exact Finset.mem_inter.mpr ⟨hxk, hxl⟩
  have hxeq : x = H.basePairIntersection k l hkl :=
    Finset.mem_singleton.mp hxsingle
  change H.basePairIntersection k l hkl ∈ C
  rw [← hxeq]
  exact hxC

/-- The same finite bridge with the complementary-pair distinctness inferred
from the trace's two-element cardinality. -/
theorem ElevenFivePivotInvertedFourStar.basePairIntersection_mem_sizeThreeSupport_of_trace_pair'
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (H : ElevenFivePivotInvertedFourStar cfg p)
    (r i j k l : Fin 4)
    (hijcard : ({i, j} : Finset FourStarVertex).card = 2)
    (htrace : H.sizeThreePrivateTrace r = ({i, j} : Finset FourStarVertex))
    (hcomp : ({k, l} : Finset FourStarVertex) =
      (Finset.univ : Finset FourStarVertex) \ {i, j}) :
    H.basePairIntersection k l (fourStar_complement_pair_ne hijcard hcomp) ∈
      lineSupport (pivotInversion cfg p) (H.sizeThreeLine r) :=
  H.basePairIntersection_mem_sizeThreeSupport_of_trace_pair r i j k l
    hijcard htrace (fourStar_complement_pair_ne hijcard hcomp) hcomp

/-- The homogeneous lift of an actual selected intersection of two base
supports is the projective opposite vertex of their two canonical covectors.
This is a genuine uniqueness-of-intersection statement, not a coordinate
choice. -/
theorem ElevenFivePivotInvertedFourStar.basePairIntersection_projective_eq_oppositeVertex
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (H : ElevenFivePivotInvertedFourStar cfg p)
    (k l : Fin 4) (hkl : k ≠ l) :
    Projectivization.mk ℝ
      (homogeneousLift (pivotInversion cfg p
        (H.basePairIntersection k l hkl)))
      (homogeneousLift_ne_zero _) =
    Projectivization.mk ℝ
      (fourStarOppositeVertex
        (H.toProjectiveSkeleton H.geometricBoundary).baseLine k l) (by
          change crossProduct (H.canonicalBaseCovector k)
            (H.canonicalBaseCovector l) ≠ 0
          intro hcross
          apply H.canonicalProjectiveBaseLine_ne hkl
          exact (Projectivization.mk_eq_mk_iff_crossProduct_eq_zero
            (H.canonicalBaseCovector_ne_zero k)
            (H.canonicalBaseCovector_ne_zero l)).2 hcross) := by
  let x := H.basePairIntersection k l hkl
  let F := H.toProjectiveSkeleton H.geometricBoundary
  have hxk : x ∈ H.baseSupport k :=
    H.basePairIntersection_mem_left k l hkl
  have hxl : x ∈ H.baseSupport l :=
    H.basePairIntersection_mem_right k l hkl
  have hk : F.baseLine k ⬝ᵥ homogeneousLift (pivotInversion cfg p x) = 0 := by
    change H.canonicalBaseCovector k ⬝ᵥ homogeneousLift (pivotInversion cfg p x) = 0
    rw [dotProduct_comm]
    exact (H.mem_baseSupport_iff_canonicalIncident k x).mp hxk
  have hl : F.baseLine l ⬝ᵥ homogeneousLift (pivotInversion cfg p x) = 0 := by
    change H.canonicalBaseCovector l ⬝ᵥ homogeneousLift (pivotInversion cfg p x) = 0
    rw [dotProduct_comm]
    exact (H.mem_baseSupport_iff_canonicalIncident l x).mp hxl
  have hline : Projectivization.mk ℝ (F.baseLine k) (by
      change H.canonicalBaseCovector k ≠ 0
      exact H.canonicalBaseCovector_ne_zero k) ≠
      Projectivization.mk ℝ (F.baseLine l) (by
      change H.canonicalBaseCovector l ≠ 0
      exact H.canonicalBaseCovector_ne_zero l) := by
    change H.canonicalProjectiveBaseLine k ≠ H.canonicalProjectiveBaseLine l
    exact H.canonicalProjectiveBaseLine_ne hkl
  have hok : F.baseLine k ⬝ᵥ fourStarOppositeVertex F.baseLine k l = 0 := by
    exact dot_self_cross _ _
  have hol : F.baseLine l ⬝ᵥ fourStarOppositeVertex F.baseLine k l = 0 := by
    exact dot_cross_self _ _
  have hopp : fourStarOppositeVertex F.baseLine k l ≠ 0 := by
    change crossProduct (H.canonicalBaseCovector k)
      (H.canonicalBaseCovector l) ≠ 0
    intro hcross
    apply H.canonicalProjectiveBaseLine_ne hkl
    exact (Projectivization.mk_eq_mk_iff_crossProduct_eq_zero
      (H.canonicalBaseCovector_ne_zero k)
      (H.canonicalBaseCovector_ne_zero l)).2 hcross
  change Projectivization.mk ℝ (homogeneousLift (pivotInversion cfg p x))
      (homogeneousLift_ne_zero _) =
    Projectivization.mk ℝ (fourStarOppositeVertex F.baseLine k l) _
  exact projectiveCommonPoint_eq_of_two_distinct_covectors
    (by
      change H.canonicalBaseCovector k ≠ 0
      exact H.canonicalBaseCovector_ne_zero k)
    (by
      change H.canonicalBaseCovector l ≠ 0
      exact H.canonicalBaseCovector_ne_zero l)
    (homogeneousLift_ne_zero _) hopp hline hk hl hok hol

/-- A private-pair trace of an actual size-three line gives the corresponding
opposite-vertex `S` determinant equation. -/
theorem ElevenFivePivotInvertedFourStar.sizeThreePrivateTrace_sDet_zero
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (H : ElevenFivePivotInvertedFourStar cfg p)
    {r i j k l : Fin 4}
    (hijcard : ({i, j} : Finset FourStarVertex).card = 2)
    (htrace : H.sizeThreePrivateTrace r = ({i, j} : Finset FourStarVertex))
    (hcomp : ({k, l} : Finset FourStarVertex) =
      (Finset.univ : Finset FourStarVertex) \ {i, j}) :
    fourStarSDet (H.toProjectiveSkeleton H.geometricBoundary) i j k l = 0 := by
  classical
  have hij : i ≠ j := by
    intro heq
    subst j
    simp at hijcard
  have hkl := fourStar_complement_pair_ne hijcard hcomp
  have hthird := H.basePairIntersection_mem_sizeThreeSupport_of_trace_pair
    r i j k l hijcard htrace hkl hcomp
  have hi : H.privateBaseLabelling.label i ∈
      lineSupport (pivotInversion cfg p) (H.sizeThreeLine r) := by
    apply (H.mem_sizeThreePrivateTrace_iff r i).mp
    rw [htrace]
    simp
  have hj : H.privateBaseLabelling.label j ∈
      lineSupport (pivotInversion cfg p) (H.sizeThreeLine r) := by
    apply (H.mem_sizeThreePrivateTrace_iff r j).mp
    rw [htrace]
    simp
  have hlabel : H.privateBaseLabelling.label i ≠
      H.privateBaseLabelling.label j :=
    H.privateBaseLabelling.label_injective.ne hij
  have hcol : Matrix.det ![
      homogeneousLift (pivotInversion cfg p (H.privateBaseLabelling.label i)),
      homogeneousLift (pivotInversion cfg p (H.privateBaseLabelling.label j)),
      homogeneousLift (pivotInversion cfg p
        (H.basePairIntersection k l hkl))] = 0 :=
    determinant_zero_of_three_mem_determinedLine (H.sizeThreeLine r) _ _ _
      hlabel hi hj hthird
  let F := H.toProjectiveSkeleton H.geometricBoundary
  have hprojective := H.basePairIntersection_projective_eq_oppositeVertex k l hkl
  have htransport := det_eq_zero_iff_of_projective_mk_eq
    (homogeneousLift_ne_zero _)
    (homogeneousLift_ne_zero _)
    (homogeneousLift_ne_zero _)
    (F.private_ne_zero i)
    (F.private_ne_zero j)
    (by
      change crossProduct (H.canonicalBaseCovector k)
        (H.canonicalBaseCovector l) ≠ 0
      intro hcross
      apply H.canonicalProjectiveBaseLine_ne hkl
      exact (Projectivization.mk_eq_mk_iff_crossProduct_eq_zero
        (H.canonicalBaseCovector_ne_zero k)
        (H.canonicalBaseCovector_ne_zero l)).2 hcross)
    (by rfl) (by rfl) hprojective
  change Matrix.det ![
    homogeneousLift (pivotInversion cfg p (H.privateBaseLabelling.label i)),
    homogeneousLift (pivotInversion cfg p (H.privateBaseLabelling.label j)),
    homogeneousLift (pivotInversion cfg p
      (H.basePairIntersection k l hkl))] = 0 at hcol
  change fourStarSDet F i j k l = 0
  exact htransport.mp hcol

/-- The family-level `S` conversion used by the determinant record. -/
theorem ElevenFivePivotInvertedFourStar.sizeThreePrivateTraceFamily_sDet_zero
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (H : ElevenFivePivotInvertedFourStar cfg p)
    {i j k l : Fin 4}
    (hijcard : ({i, j} : Finset FourStarVertex).card = 2)
    (hmem : ({i, j} : Finset FourStarVertex) ∈ H.sizeThreePrivateTraceFamily)
    (hcomp : ({k, l} : Finset FourStarVertex) =
      (Finset.univ : Finset FourStarVertex) \ {i, j}) :
    fourStarSDet (H.toProjectiveSkeleton H.geometricBoundary) i j k l = 0 := by
  rcases Finset.mem_image.mp hmem with ⟨r, _hr, htrace⟩
  exact H.sizeThreePrivateTrace_sDet_zero hijcard htrace hcomp

/-- Both determinant fields are now obtained from the actual four
size-three supports of the inverted pivot. -/
noncomputable def ElevenFivePivotInvertedFourStar.sizeThreePrivateTraceDeterminantData
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (H : ElevenFivePivotInvertedFourStar cfg p) :
    FourStarTraceDeterminantData
      (H.toProjectiveSkeleton H.geometricBoundary)
      H.sizeThreePrivateTraceFamily where
  t_zero := by
    intro i j k _hcard hmem
    exact H.sizeThreePrivateTraceFamily_tDet_zero hmem
  s_zero := by
    intro i j k l hijcard hmem hcomp
    exact H.sizeThreePrivateTraceFamily_sDet_zero hijcard hmem hcomp

/-- The four canonical determinant equations attached to a relabelled
`T`-star are inconsistent over the reals. -/
theorem fourStarCanonicalTStarDeterminants_impossible
    (F : FourStarProjectiveSkeleton)
    (D : FourStarCanonicalTStarDeterminants F) : False := by
  let N := F.toNormalForm
  have hT : N.determinants.b + N.determinants.a * N.determinants.c = 0 :=
    (N.t123_eq_zero_iff).mp D.t012
  have hS14 : 1 + N.determinants.d * (1 + N.determinants.a) = 0 :=
    (N.s14_eq_zero_iff).mp D.s03
  have hS24 : 1 + N.determinants.d + N.determinants.b = 0 :=
    (N.s24_eq_zero_iff).mp D.s13
  have hS34 : N.determinants.d - N.determinants.c = 0 :=
    (N.s34_eq_zero_iff).mp D.s23
  exact fourStarNormal_tStar_impossible N.determinants hT hS14 hS24 hS34

/-- The four canonical determinant equations attached to a relabelled
four-cycle are inconsistent over the reals. -/
theorem fourStarCanonicalFourCycleDeterminants_impossible
    (F : FourStarProjectiveSkeleton)
    (D : FourStarCanonicalFourCycleDeterminants F) : False := by
  let N := F.toNormalForm
  have hS12raw : N.determinants.a - N.determinants.b = 0 :=
    (N.s12_eq_zero_iff).mp D.s01
  have hS12 : N.determinants.b - N.determinants.a = 0 := by linarith
  have hS23raw : N.determinants.c - N.determinants.b = 0 :=
    (N.s23_eq_zero_iff).mp D.s12
  have hS23 : N.determinants.b - N.determinants.c = 0 := by linarith
  have hS34 : N.determinants.d - N.determinants.c = 0 :=
    (N.s34_eq_zero_iff).mp D.s23
  have hS14 : 1 + N.determinants.d * (1 + N.determinants.a) = 0 :=
    (N.s14_eq_zero_iff).mp D.s03
  exact fourStarNormal_fourCycle_impossible N.determinants hS12 hS23 hS34 hS14

/-- The relabelled triangle-pendant survivor has its forced normal
coordinates.  This is intentionally stated for an arbitrary skeleton, so
the finite relabelling is retained rather than silently discarded. -/
theorem fourStarCanonicalTrianglePendantDeterminants_normal_coordinates
    (F : FourStarProjectiveSkeleton)
    (D : FourStarCanonicalTrianglePendantDeterminants F) :
    let N := F.toNormalForm
    N.determinants.a = 1 ∧ N.determinants.b = 1 ∧
      N.determinants.c = 1 ∧ N.determinants.d = -1 / 2 := by
  dsimp only
  let N := F.toNormalForm
  have hS12raw : N.determinants.a - N.determinants.b = 0 :=
    (N.s12_eq_zero_iff).mp D.s01
  have hS12 : N.determinants.b - N.determinants.a = 0 := by linarith
  have hS13 : 1 - N.determinants.a * N.determinants.c = 0 :=
    (N.s13_eq_zero_iff).mp D.s02
  have hS23raw : N.determinants.c - N.determinants.b = 0 :=
    (N.s23_eq_zero_iff).mp D.s12
  have hS23 : N.determinants.b - N.determinants.c = 0 := by linarith
  have hS14 : 1 + N.determinants.d * (1 + N.determinants.a) = 0 :=
    (N.s14_eq_zero_iff).mp D.s03
  exact fourStarNormal_trianglePendant_unique N.determinants hS12 hS13 hS23 hS14

/-- Determinant data forbids the label-free `T` trace-family alternative;
the contradiction is taken only after relabelling both the traces and the
projective skeleton into the shared canonical convention. -/
theorem not_isFourStarTStarTraceFamily_of_traceDeterminantData
    (F : FourStarProjectiveSkeleton)
    (E : Finset (Finset FourStarVertex))
    (D : FourStarTraceDeterminantData F E) :
    ¬ IsFourStarTStarTraceFamily E := by
  intro hT
  obtain ⟨σ, _hσ, hdet⟩ :=
    exists_fourStarCanonicalTStarDeterminants F E hT D
  exact fourStarCanonicalTStarDeterminants_impossible (F.relabel σ) hdet

/-- Determinant data likewise forbids the label-free four-cycle alternative.
Again, the contradiction occurs in the relabelled skeleton. -/
theorem not_isFourStarFourCycle_of_traceDeterminantData
    (F : FourStarProjectiveSkeleton)
    (E : Finset (Finset FourStarVertex))
    (hfamily : IsFourStarPrivatePairFamily E)
    (D : FourStarTraceDeterminantData F E) :
    ¬ IsFourStarFourCycle E := by
  intro hcycle
  obtain ⟨σ, _hσ, hdet⟩ :=
    exists_fourStarCanonicalFourCycleDeterminants F E hfamily hcycle D
  exact fourStarCanonicalFourCycleDeterminants_impossible (F.relabel σ) hdet

/-- Once the finite dispatch has reached triangle-pendant, determinant data
produces a relabelled canonical survivor and its forced coordinates. -/
theorem exists_relabelled_fourStarTrianglePendant_survivor
    (F : FourStarProjectiveSkeleton)
    (E : Finset (Finset FourStarVertex))
    (hfamily : IsFourStarPrivatePairFamily E)
    (hpendant : IsFourStarTrianglePendant E)
    (D : FourStarTraceDeterminantData F E) :
    ∃ σ : Equiv.Perm FourStarVertex,
      fourStarRelabelTraceFamily σ E = fourStarCanonicalTrianglePendant ∧
      ∃ hdet : FourStarCanonicalTrianglePendantDeterminants (F.relabel σ),
        let N := (F.relabel σ).toNormalForm
        N.determinants.a = 1 ∧ N.determinants.b = 1 ∧
          N.determinants.c = 1 ∧ N.determinants.d = -1 / 2 := by
  obtain ⟨σ, hσ, hdet⟩ :=
    exists_fourStarCanonicalTrianglePendantDeterminants F E hfamily hpendant D
  refine ⟨σ, hσ, hdet, ?_⟩
  exact fourStarCanonicalTrianglePendantDeterminants_normal_coordinates
    (F.relabel σ) hdet

/-- The pivot-level dispatch after the `T` branch has been excluded: the
four-cycle contradiction leaves a relabelled triangle-pendant survivor with
its normal coordinates.  The conclusion deliberately keeps `σ`, since the
canonical normal coordinates belong to the relabelled skeleton. -/
theorem ElevenFivePivotInvertedFourStar.exists_relabelled_trianglePendant_survivor_of_no_tStar
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (H : ElevenFivePivotInvertedFourStar cfg p)
    (hnoT : ¬ H.additionalThreeLineLink.IsTStar) :
    ∃ σ : Equiv.Perm FourStarVertex,
      fourStarRelabelTraceFamily σ H.sizeThreePrivateTraceFamily =
        fourStarCanonicalTrianglePendant ∧
      ∃ hdet : FourStarCanonicalTrianglePendantDeterminants
          ((H.toProjectiveSkeleton H.geometricBoundary).relabel σ),
        let N := ((H.toProjectiveSkeleton H.geometricBoundary).relabel σ).toNormalForm
        N.determinants.a = 1 ∧ N.determinants.b = 1 ∧
          N.determinants.c = 1 ∧ N.determinants.d = -1 / 2 := by
  let F := H.toProjectiveSkeleton H.geometricBoundary
  let E := H.sizeThreePrivateTraceFamily
  have hfamily : IsFourStarPrivatePairFamily E := by
    rcases H.additionalThreeLineClassification.tStar_or_privatePairs with hT | hpair
    · exact False.elim (hnoT hT)
    · simpa [E, H.additionalThreeLine_privatePairFamily_eq] using hpair
  have hpendant : IsFourStarTrianglePendant E := by
    rcases fourStar_privatePair_cycle_or_trianglePendant_of_no_tStar
      H.additionalThreeLineLink H.additionalThreeLineClassification hnoT
      with hcycle | hpendant
    · have hcycleE : IsFourStarFourCycle E := by
        simpa [E, H.additionalThreeLine_privatePairFamily_eq] using hcycle
      exact False.elim
        ((not_isFourStarFourCycle_of_traceDeterminantData F E hfamily
          H.sizeThreePrivateTraceDeterminantData) hcycleE)
    · simpa [E, H.additionalThreeLine_privatePairFamily_eq] using hpendant
  simpa [F, E] using
    (exists_relabelled_fourStarTrianglePendant_survivor F E hfamily hpendant
      H.sizeThreePrivateTraceDeterminantData)

/-- The actual `T` branch is impossible: if it occurred, its four concrete
traces would form the finite `T` certificate, which the relabelled normal
determinant calculation has already ruled out. -/
theorem ElevenFivePivotInvertedFourStar.not_additionalThreeLine_tStar
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (H : ElevenFivePivotInvertedFourStar cfg p) :
    ¬ H.additionalThreeLineLink.IsTStar := by
  intro hT
  exact (not_isFourStarTStarTraceFamily_of_traceDeterminantData
    (H.toProjectiveSkeleton H.geometricBoundary)
    H.sizeThreePrivateTraceFamily H.sizeThreePrivateTraceDeterminantData)
      (H.sizeThreePrivateTraceFamily_isTStarTraceFamily_of_tStar hT)

/-- Unconditional determinant dispatch for the actual pivot: only the
triangle-pendant survivor remains, in a correctly relabelled skeleton. -/
theorem ElevenFivePivotInvertedFourStar.exists_relabelled_trianglePendant_survivor
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (H : ElevenFivePivotInvertedFourStar cfg p) :
    ∃ σ : Equiv.Perm FourStarVertex,
      fourStarRelabelTraceFamily σ H.sizeThreePrivateTraceFamily =
        fourStarCanonicalTrianglePendant ∧
      ∃ hdet : FourStarCanonicalTrianglePendantDeterminants
          ((H.toProjectiveSkeleton H.geometricBoundary).relabel σ),
        let N := ((H.toProjectiveSkeleton H.geometricBoundary).relabel σ).toNormalForm
        N.determinants.a = 1 ∧ N.determinants.b = 1 ∧
          N.determinants.c = 1 ∧ N.determinants.d = -1 / 2 :=
  H.exists_relabelled_trianglePendant_survivor_of_no_tStar
    H.not_additionalThreeLine_tStar

/-- The precise desired endpoint of the four-star rigidity calculation. -/
def ElevenFivePivotInvertedFourStar.HasHarmonicBaseSupports
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (H : ElevenFivePivotInvertedFourStar cfg p) : Prop :=
  ∀ i : Fin 4, IsParametricallyHarmonicFour (H.baseSupport i)

/-- A finite triangle-pendant conclusion plus a determinant-to-line-harmonic
bridge yields the four harmonic base supports.  The latter bridge is stated
as an explicit local implication because it is exactly the missing real
calculation, not a combinatorial consequence. -/
theorem elevenFive_harmonic_baseSupports_of_trianglePendant_bridge
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (H : ElevenFivePivotInvertedFourStar cfg p)
    {E : Finset (Finset FourStarVertex)}
    (hpendant : IsFourStarTrianglePendant E)
    (hbridge : IsFourStarTrianglePendant E →
      ∀ i : Fin 4, IsParametricallyHarmonicFour (H.baseSupport i)) :
    H.HasHarmonicBaseSupports :=
  hbridge hpendant

/-- The determinant survivor has the unique normal coordinates
`(a,b,c,d) = (1,1,1,-1/2)`.  This is the exact coordinate endpoint after
the finite triangle-pendant motif has been attached to the four displayed
`S`-determinants of the concrete projective skeleton. -/
theorem elevenFive_trianglePendant_normal_coordinates_of_determinantal
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    {cfg : Configuration Point} {p : Point}
    (H : ElevenFivePivotInvertedFourStar cfg p)
    (hdet : IsFourStarTrianglePendantDeterminantal
      (H.toProjectiveSkeleton H.geometricBoundary)) :
    let N := (H.toProjectiveSkeleton H.geometricBoundary).toNormalForm
    N.determinants.a = 1 ∧ N.determinants.b = 1 ∧
      N.determinants.c = 1 ∧ N.determinants.d = -1 / 2 := by
  dsimp only
  let F : FourStarProjectiveSkeleton :=
    H.toProjectiveSkeleton H.geometricBoundary
  have hF : F = H.toProjectiveSkeleton H.geometricBoundary := rfl
  rw [← hF] at hdet
  let N := F.toNormalForm
  have hN : N =
      (H.toProjectiveSkeleton H.geometricBoundary).toNormalForm := rfl
  rw [← hN]
  have hS12Raw : N.determinants.a - N.determinants.b = 0 :=
    (N.s12_eq_zero_iff).mp hdet.1
  have hS12 : N.determinants.b - N.determinants.a = 0 := by
    linarith
  have hS13 : 1 - N.determinants.a * N.determinants.c = 0 :=
    (N.s13_eq_zero_iff).mp hdet.2.1
  have hS23Raw : N.determinants.c - N.determinants.b = 0 :=
    (N.s23_eq_zero_iff).mp hdet.2.2.1
  have hS23 : N.determinants.b - N.determinants.c = 0 := by
    linarith
  have hS14 : 1 + N.determinants.d * (1 + N.determinants.a) = 0 :=
    (N.s14_eq_zero_iff).mp hdet.2.2.2
  exact fourStarNormal_trianglePendant_unique N.determinants
    hS12 hS13 hS23 hS14

/-!
## Exact remaining geometric bridge

The finite prerequisites have now been constructed from a pivot `(9,4,4)`:
the saturated base profile, private base labels, and unconditional additional
line trichotomy.  The next theorem must derive projective general position
for the actual four covectors and identify the three finite motifs with the
normal-coordinate determinant equations.  The existing
`FourStarRigidity` scalar exclusions then leave triangle-pendant, which must
be converted to four instances of `FourPointLineHarmonicParameter` and
transported to proper circles by `InversionHarmonicTransport`.
-/

end Erdos506.V1
