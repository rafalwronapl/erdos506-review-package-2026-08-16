import Erdos506.Incidence.RealProjectiveArrangementGlobalFinish
import Erdos506.Incidence.RealProjectiveArrangementFaceThreeMinimalFinish
import Erdos506.Incidence.RealProjectiveLineParameterTopology
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Logic.Equiv.Option
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Tactic

/-!
# The exact Euler boundary for real projective arrangements

The existing arrangement development already identifies the genuine faces
with the realized homogeneous sign patterns and proves the exact edge census

`|E| = ∑ p ∈ vertexSet, multiplicity p`.

Consequently Euler is equivalent to one, and only one, remaining region-count
identity:

`|faces| = 1 + ∑ p ∈ vertexSet, (multiplicity p - 1)`.

This file proves that reduction, specializes it to `labelDualArrangement`,
and gives the corresponding constructor for
`RealProjectiveArrangementGlobalInput`.  It also materializes deletion of the
distinguished line from an arrangement indexed by `Option Line` and records
the exact insertion arithmetic.

The face part of the insertion arithmetic has the exact form

```lean
Fintype.card A.ArrangementFace =
  Fintype.card A.deleteNone.ArrangementFace +
    (A.insertionCutSet).card
```

for `A : FiniteProjectiveLineArrangement (Option Line)`, where the old
arrangement is `A.deleteNone` and `insertionCutSet` is the actual set of
marked vertices on the inserted projective line.  The proof below identifies
the open cyclic gaps with the crossed old faces and then uses this recurrence
in a strong-cardinality induction which retains a nonconcurrent triple.
-/

namespace Erdos506.Incidence

open Matrix
open Erdos506.V4
open scoped BigOperators

universe u v

namespace FiniteProjectiveLineArrangement

variable {Line : Type u} [Fintype Line] [DecidableEq Line]

@[reducible] noncomputable def realProjectiveOnePointQuotientTopologyEulerFinish :
    TopologicalSpace RealProjectiveOnePoint :=
  @instTopologicalSpaceQuotient
    {v : RealProjectiveLineVector // v ≠ 0}
    (projectivizationSetoid ℝ RealProjectiveLineVector)
    (by infer_instance)

noncomputable local instance realProjectiveOnePointTopologicalSpaceForEulerFinish :
    TopologicalSpace RealProjectiveOnePoint :=
  realProjectiveOnePointQuotientTopologyEulerFinish

noncomputable local instance realProjectivePointTopologicalSpaceForEulerFinish :
    TopologicalSpace RealProjectivePoint :=
  realProjectivePointQuotientTopology

noncomputable local instance realProjectivePointDecidableEqForEulerFinish :
    DecidableEq RealProjectivePoint :=
  Classical.decEq _

noncomputable local instance incidentDecidableForEulerFinish
    (A : FiniteProjectiveLineArrangement Line)
    (p : RealProjectivePoint) (l : Line) :
    Decidable (A.Incident p l) :=
  Classical.propDecidable _

/-- The nonzero-vector quotient map for the chosen model of `RP¹`. -/
theorem isQuotientMap_realProjectiveOnePoint_mk :
    Topology.IsQuotientMap
      (Projectivization.mk' ℝ :
        {v : RealProjectiveLineVector // v ≠ 0} → RealProjectiveOnePoint) :=
  isQuotientMap_quotient_mk'

noncomputable local instance lineRegularLocusTopologicalSpaceForEulerFinish
    (A : FiniteProjectiveLineArrangement Line) (l : Line) :
    TopologicalSpace (A.lineRegularLocus l) :=
  TopologicalSpace.induced
    (fun q : A.lineRegularLocus l => q.1)
    realProjectivePointQuotientTopology

/-- The cyclic predicate can be tested on any chosen nonzero homogeneous
representatives, not only Mathlib's canonical `rep`s. -/
theorem realProjectiveCyclic_mk_iff
    {p q r : RealProjectiveLineVector}
    (hp : p ≠ 0) (hq : q ≠ 0) (hr : r ≠ 0) :
    RealProjectiveCyclic
      (Projectivization.mk ℝ p hp)
      (Projectivization.mk ℝ q hq)
      (Projectivization.mk ℝ r hr) ↔
      0 < realProjectiveTripleBracket p q r := by
  constructor
  · rintro ⟨p', q', r', hp', hq', hr', hP, hQ, hR, hpositive⟩
    obtain ⟨a, ha⟩ :=
      (Projectivization.mk_eq_mk_iff' ℝ p p' hp hp').mp hP
    obtain ⟨b, hb⟩ :=
      (Projectivization.mk_eq_mk_iff' ℝ q q' hq hq').mp hQ
    obtain ⟨c, hc⟩ :=
      (Projectivization.mk_eq_mk_iff' ℝ r r' hr hr').mp hR
    have ha0 : a ≠ 0 := by
      intro ha0
      apply hp
      rw [← ha, ha0, zero_smul]
    have hb0 : b ≠ 0 := by
      intro hb0
      apply hq
      rw [← hb, hb0, zero_smul]
    have hc0 : c ≠ 0 := by
      intro hc0
      apply hr
      rw [← hc, hc0, zero_smul]
    rw [← ha, ← hb, ← hc, realProjectiveTripleBracket_smul]
    exact mul_pos
      (sq_pos_of_ne_zero (mul_ne_zero (mul_ne_zero ha0 hb0) hc0))
      hpositive
  · exact realProjectiveCyclic_mk hp hq hr

/-- For fixed endpoints, the positive cyclic interval is open in `RP¹`. -/
theorem isOpen_realProjectiveCyclic_middle
    (P R : RealProjectiveOnePoint) :
    IsOpen {Q : RealProjectiveOnePoint | RealProjectiveCyclic P Q R} := by
  have hcontinuous : Continuous
      (fun q : {v : RealProjectiveLineVector // v ≠ 0} =>
        realProjectiveTripleBracket P.rep q.1 R.rep) := by
    have hq0 : Continuous
        (fun q : {v : RealProjectiveLineVector // v ≠ 0} => q.1 0) :=
      (continuous_apply 0).comp continuous_subtype_val
    have hq1 : Continuous
        (fun q : {v : RealProjectiveLineVector // v ≠ 0} => q.1 1) :=
      (continuous_apply 1).comp continuous_subtype_val
    simpa only [realProjectiveTripleBracket, realProjectiveBracket] using
      (((continuous_const.mul hq1).sub (continuous_const.mul hq0)).mul
        ((hq0.mul continuous_const).sub (hq1.mul continuous_const))).mul
          continuous_const
  have hopen : IsOpen
      {q : {v : RealProjectiveLineVector // v ≠ 0} |
        0 < realProjectiveTripleBracket P.rep q.1 R.rep} :=
    isOpen_lt continuous_const hcontinuous
  apply isQuotientMap_realProjectiveOnePoint_mk.isOpen_preimage.mp
  convert hopen using 1
  ext q
  change RealProjectiveCyclic P (Projectivization.mk' ℝ q) R ↔ _
  simpa only [Projectivization.mk_rep, Projectivization.mk'_eq_mk] using
    (realProjectiveCyclic_mk_iff P.rep_nonzero q.2 R.rep_nonzero)

/-- The linear parametrization of a projective line is continuous. -/
theorem continuous_projectiveLineParameter_eulerFinish
    (L : RealProjectiveLine) :
    Continuous (projectiveLineParameter L) := by
  apply isQuotientMap_realProjectiveOnePoint_mk.continuous_iff.mpr
  have hlinear : Continuous
      (fun v : {v : RealProjectiveLineVector // v ≠ 0} =>
        projectiveLineParameterLinearMap L v.1) :=
    (projectiveLineParameterLinearMap L).continuous_of_finiteDimensional.comp
      continuous_subtype_val
  have hne (v : {v : RealProjectiveLineVector // v ≠ 0}) :
      projectiveLineParameterLinearMap L v.1 ≠ 0 :=
    by
      simpa only [map_zero] using
        Function.Injective.ne (projectiveLineParameterLinearMap_injective L) v.2
  have hquotient : Continuous (fun v : {v : RealProjectiveLineVector // v ≠ 0} =>
      Projectivization.mk' ℝ
        ⟨projectiveLineParameterLinearMap L v.1, hne v⟩) :=
    continuous_quotient_mk'.comp (hlinear.subtype_mk hne)
  simpa only [Function.comp_apply, projectiveLineParameter,
    Projectivization.map_mk, Projectivization.mk'_eq_mk] using hquotient

/-- The chosen `RP¹` parametrization is a homeomorphism onto the incident
point subtype of its projective line. -/
noncomputable def projectiveLineParameterHomeomorph_eulerFinish
    (L : RealProjectiveLine) :
    RealProjectiveOnePoint ≃ₜ {p : RealProjectivePoint // p.orthogonal L} := by
  exact projectiveLineParameterHomeomorph L

/-! ## Reindexing invariance -/

/-- Pull an arrangement back along an equivalence of finite index types. -/
def reindex {Line' : Type v}
    (A : FiniteProjectiveLineArrangement Line) (e : Line' ≃ Line) :
    FiniteProjectiveLineArrangement Line' where
  projectiveLine l := A.projectiveLine (e l)
  projectiveLine_injective := A.projectiveLine_injective.comp e.injective

@[simp] theorem reindex_projectiveLine {Line' : Type v}
    (A : FiniteProjectiveLineArrangement Line) (e : Line' ≃ Line)
    (l : Line') :
    (A.reindex e).projectiveLine l = A.projectiveLine (e l) :=
  rfl

@[simp] theorem reindex_incident {Line' : Type v}
    (A : FiniteProjectiveLineArrangement Line) (e : Line' ≃ Line)
    (p : RealProjectivePoint) (l : Line') :
    (A.reindex e).Incident p l ↔ A.Incident p (e l) :=
  Iff.rfl

/-- Reindexing bijects the indexed lines incident with any fixed point. -/
def reindexIncidentLineEquiv {Line' : Type v}
    (A : FiniteProjectiveLineArrangement Line) (e : Line' ≃ Line)
    (p : RealProjectivePoint) :
    {l : Line' // (A.reindex e).Incident p l} ≃
      {l : Line // A.Incident p l} where
  toFun l := ⟨e l.1, l.2⟩
  invFun l := ⟨e.symm l.1, by simpa using l.2⟩
  left_inv l := by apply Subtype.ext; exact e.symm_apply_apply l.1
  right_inv l := by apply Subtype.ext; exact e.apply_symm_apply l.1

/-- Multiplicity is the cardinality of the subtype of incident indices. -/
theorem multiplicity_eq_card_incidentLines
    (A : FiniteProjectiveLineArrangement Line) (p : RealProjectivePoint) :
    A.multiplicity p = Fintype.card {l : Line // A.Incident p l} := by
  classical
  unfold multiplicity
  simpa using (Fintype.card_coe
    ((Finset.univ : Finset Line).filter fun l => A.Incident p l)).symm

theorem reindex_multiplicity {Line' : Type v}
    [Fintype Line'] [DecidableEq Line']
    (A : FiniteProjectiveLineArrangement Line) (e : Line' ≃ Line)
    (p : RealProjectivePoint) :
    (A.reindex e).multiplicity p = A.multiplicity p := by
  rw [(A.reindex e).multiplicity_eq_card_incidentLines,
    A.multiplicity_eq_card_incidentLines]
  exact Fintype.card_congr (A.reindexIncidentLineEquiv e p)

noncomputable local instance arrangementFaceFintypeForEulerFinish
    (A : FiniteProjectiveLineArrangement Line) : Fintype A.ArrangementFace :=
  A.arrangementFaceFintype

noncomputable local instance geometricEdgeDecidableEqForEulerFinish
    (A : FiniteProjectiveLineArrangement Line) : DecidableEq A.GeometricEdge :=
  Classical.decEq _

/-- The contribution `multiplicity - 1` of the actual arrangement vertices.
This is the projective region-count side of the deletion--restriction
formula, defined without any cellulation assumption. -/
noncomputable def arrangementVertexExcess
    (A : FiniteProjectiveLineArrangement Line) : ℕ :=
  ∑ p ∈ A.vertexSet, (A.multiplicity p - 1)

/-- Every member of the actual vertex set is incident with at least the two
distinct indexed lines which produce it. -/
theorem two_le_multiplicity_of_mem_vertexSet
    (A : FiniteProjectiveLineArrangement Line)
    {p : RealProjectivePoint} (hp : p ∈ A.vertexSet) :
    2 ≤ A.multiplicity p := by
  obtain ⟨l, m, hlm, rfl⟩ := A.exists_lines_of_mem_vertexSet hp
  exact A.two_le_multiplicity_intersection hlm

/-- Membership in the actual vertex set is equivalent to having at least
two incident indexed lines.  The reverse direction is useful when comparing
an arrangement with a deletion. -/
theorem mem_vertexSet_iff_two_le_multiplicity
    (A : FiniteProjectiveLineArrangement Line) (p : RealProjectivePoint) :
    p ∈ A.vertexSet ↔ 2 ≤ A.multiplicity p := by
  classical
  constructor
  · exact A.two_le_multiplicity_of_mem_vertexSet
  · intro htwo
    unfold multiplicity at htwo
    obtain ⟨l, hl, m, hm, hlm⟩ := Finset.one_lt_card.mp (by omega :
      1 < ((Finset.univ : Finset Line).filter fun l => A.Incident p l).card)
    have hpl : A.Incident p l := (Finset.mem_filter.mp hl).2
    have hpm : A.Incident p m := (Finset.mem_filter.mp hm).2
    have hpEq : p = A.intersection l m :=
      A.eq_intersection_of_incident hlm hpl hpm
    rw [hpEq]
    exact A.intersection_mem_vertexSet hlm

theorem reindex_vertexSet {Line' : Type v}
    [Fintype Line'] [DecidableEq Line']
    (A : FiniteProjectiveLineArrangement Line) (e : Line' ≃ Line) :
    (A.reindex e).vertexSet = A.vertexSet := by
  classical
  ext p
  rw [(A.reindex e).mem_vertexSet_iff_two_le_multiplicity,
    A.mem_vertexSet_iff_two_le_multiplicity,
    A.reindex_multiplicity e p]

theorem reindex_arrangementVertexExcess {Line' : Type v}
    [Fintype Line'] [DecidableEq Line']
    (A : FiniteProjectiveLineArrangement Line) (e : Line' ≃ Line) :
    (A.reindex e).arrangementVertexExcess = A.arrangementVertexExcess := by
  classical
  unfold arrangementVertexExcess
  rw [A.reindex_vertexSet e]
  apply Finset.sum_congr rfl
  intro p _hp
  rw [A.reindex_multiplicity e p]

/-- Reindexing does not change the actual complement as a topological
subspace of the real projective plane. -/
def reindexArrangementComplementHomeomorph {Line' : Type v}
    [Fintype Line'] [DecidableEq Line']
    (A : FiniteProjectiveLineArrangement Line) (e : Line' ≃ Line) :
    (A.reindex e).ArrangementComplement ≃ₜ A.ArrangementComplement where
  toFun p :=
    ⟨p.1, fun l hl => p.2 (e.symm l) (by simpa using hl)⟩
  invFun p :=
    ⟨p.1, fun l hl => p.2 (e l) (by simpa using hl)⟩
  left_inv p := by apply Subtype.ext; rfl
  right_inv p := by apply Subtype.ext; rfl
  continuous_toFun := continuous_subtype_val.subtype_mk _
  continuous_invFun := continuous_subtype_val.subtype_mk _

/-- The complement homeomorphism induces an equivalence of genuine faces. -/
noncomputable def reindexArrangementFaceEquiv {Line' : Type v}
    [Fintype Line'] [DecidableEq Line']
    (A : FiniteProjectiveLineArrangement Line) (e : Line' ≃ Line) :
    (A.reindex e).ArrangementFace ≃ A.ArrangementFace where
  toFun :=
    Continuous.connectedComponentsMap
      (A.reindexArrangementComplementHomeomorph e).continuous
  invFun :=
    Continuous.connectedComponentsMap
      (A.reindexArrangementComplementHomeomorph e).symm.continuous
  left_inv F := by
    obtain ⟨p, rfl⟩ := ConnectedComponents.surjective_coe F
    rfl
  right_inv F := by
    obtain ⟨p, rfl⟩ := ConnectedComponents.surjective_coe F
    rfl

theorem reindex_card_arrangementFace {Line' : Type v}
    [Fintype Line'] [DecidableEq Line']
    (A : FiniteProjectiveLineArrangement Line) (e : Line' ≃ Line) :
    Fintype.card (A.reindex e).ArrangementFace =
      Fintype.card A.ArrangementFace :=
  Fintype.card_congr (A.reindexArrangementFaceEquiv e)

theorem reindex_nonPencil {Line' : Type v}
    [Fintype Line'] [DecidableEq Line']
    (A : FiniteProjectiveLineArrangement Line) (e : Line' ≃ Line)
    (hA : A.NonPencil) : (A.reindex e).NonPencil := by
  intro hPencil
  apply hA
  rcases hPencil with ⟨p, hp⟩
  refine ⟨p, fun l => ?_⟩
  simpa using hp (e.symm l)

theorem regionCount_of_reindex {Line' : Type v}
    [Fintype Line'] [DecidableEq Line']
    (A : FiniteProjectiveLineArrangement Line) (e : Line' ≃ Line)
    (hregion : Fintype.card (A.reindex e).ArrangementFace =
      (A.reindex e).arrangementVertexExcess + 1) :
    Fintype.card A.ArrangementFace = A.arrangementVertexExcess + 1 := by
  rw [A.reindex_card_arrangementFace e,
    A.reindex_arrangementVertexExcess e] at hregion
  exact hregion

/-- The existing exact edge census splits into one edge contribution per
actual vertex and the vertex excess.  This is all of the non-topological
arithmetic in Euler's relation. -/
theorem card_geometricEdge_eq_card_vertexSet_add_vertexExcess
    (A : FiniteProjectiveLineArrangement Line) :
    Fintype.card A.GeometricEdge =
      A.vertexSet.card + A.arrangementVertexExcess := by
  rw [A.card_geometricEdge_eq_sum_multiplicity]
  calc
    (∑ p ∈ A.vertexSet, A.multiplicity p) =
        ∑ p ∈ A.vertexSet, (1 + (A.multiplicity p - 1)) := by
      apply Finset.sum_congr rfl
      intro p hp
      have htwo := A.two_le_multiplicity_of_mem_vertexSet hp
      omega
    _ = A.vertexSet.card + A.arrangementVertexExcess := by
      rw [Finset.sum_add_distrib]
      simp [arrangementVertexExcess]

/-- Euler for the genuine vertices, cyclic edges, and complement components
is exactly the projective region-count formula.  No topology beyond the
already-proved finiteness of the face type is used in this equivalence. -/
theorem euler_iff_card_arrangementFace_eq_vertexExcess_add_one
    (A : FiniteProjectiveLineArrangement Line) :
    (Fintype.card {p // p ∈ A.vertexSet} +
          Fintype.card A.ArrangementFace =
        Fintype.card A.GeometricEdge + 1) ↔
      Fintype.card A.ArrangementFace =
        A.arrangementVertexExcess + 1 := by
  have hedge := A.card_geometricEdge_eq_card_vertexSet_add_vertexExcess
  have hvertex : Fintype.card {p // p ∈ A.vertexSet} = A.vertexSet.card := by
    simp
  rw [hvertex, hedge]
  omega

noncomputable local instance realizedArrangementSignPatternFintypeForEulerFinish
    (A : FiniteProjectiveLineArrangement Line) (base : Line) :
    Fintype (A.RealizedArrangementSignPattern base) :=
  Fintype.ofEquiv A.ArrangementFace
    (A.arrangementFaceSignPatternEquivRealized base)

/-- The existing sign-pattern classification is cardinality-exact: it loses
neither a genuine component nor an unrealizable formal Boolean word. -/
theorem card_arrangementFace_eq_card_realizedArrangementSignPattern
    (A : FiniteProjectiveLineArrangement Line) (base : Line) :
    Fintype.card A.ArrangementFace =
      Fintype.card (A.RealizedArrangementSignPattern base) :=
  Fintype.card_congr (A.arrangementFaceSignPatternEquivRealized base)

/-- Sign-pattern form of the exact remaining Euler boundary.  Thus a
deletion--restriction proof may work entirely with realized strict sign
words; no further comparison with connected components is needed. -/
theorem euler_iff_card_realizedArrangementSignPattern_eq_vertexExcess_add_one
    (A : FiniteProjectiveLineArrangement Line) (base : Line) :
    (Fintype.card {p // p ∈ A.vertexSet} +
          Fintype.card A.ArrangementFace =
        Fintype.card A.GeometricEdge + 1) ↔
      Fintype.card (A.RealizedArrangementSignPattern base) =
        A.arrangementVertexExcess + 1 := by
  rw [A.euler_iff_card_arrangementFace_eq_vertexExcess_add_one,
    A.card_arrangementFace_eq_card_realizedArrangementSignPattern base]

/-- Euler starts with the empty indexed family: there are no vertices or
edges and the real projective plane has one complement component. -/
theorem euler_of_isEmpty
    (A : FiniteProjectiveLineArrangement Line) [IsEmpty Line] :
    Fintype.card {p // p ∈ A.vertexSet} +
          Fintype.card A.ArrangementFace =
        Fintype.card A.GeometricEdge + 1 := by
  classical
  have hvertex : A.vertexSet = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro p hp
    obtain ⟨l, _m, _hlm, _hp⟩ := A.exists_lines_of_mem_vertexSet hp
    exact isEmptyElim l
  have hface : Fintype.card A.ArrangementFace = 1 := by
    have hsub : Subsingleton A.ArrangementFace :=
      A.arrangementFace_subsingleton_of_isEmpty
    let F : A.ArrangementFace := Classical.choice A.nonempty_arrangementFace
    exact Fintype.card_eq_one_iff.mpr ⟨F, fun G => hsub.elim G F⟩
  have hexcess : A.arrangementVertexExcess = 0 := by
    simp [arrangementVertexExcess, hvertex]
  apply (A.euler_iff_card_arrangementFace_eq_vertexExcess_add_one).mpr
  omega

/-- Normal perturbation at a regular point yields two different faces as
soon as one transverse indexed line is specified; non-pencilness is not
needed for this local form. -/
theorem exists_two_distinct_arrangementFaces_of_regular_of_ne
    (A : FiniteProjectiveLineArrangement Line)
    (q : RealProjectivePoint) (l b : Line)
    (hregular : ∀ m : Line, A.Incident q m ↔ m = l) (hbl : b ≠ l) :
    ∃ F G : A.ArrangementFace, F ≠ G := by
  rcases A.exists_pos_sign_perturbation_radius_of_regular q l hregular with
    ⟨ε, hεpos, hε⟩
  let t : ℝ := ε / 2
  have ht : 0 < t := half_pos hεpos
  have htsmall : |t| < ε := by
    rw [abs_of_pos ht]
    exact half_lt_self hεpos
  have hneg : -t < 0 := neg_lt_zero.mpr ht
  have hnegsmall : |-t| < ε := by simpa using htsmall
  let ppos : A.ArrangementComplement :=
    A.normalPerturbationComplementOfRegular q l hregular hε
      (ne_of_gt ht) htsmall
  let pneg : A.ArrangementComplement :=
    A.normalPerturbationComplementOfRegular q l hregular hε
      (ne_of_lt hneg) hnegsmall
  refine ⟨A.arrangementFaceOf ppos, A.arrangementFaceOf pneg, ?_⟩
  intro hface
  have hpattern : A.arrangementPointSignPattern b ppos =
      A.arrangementPointSignPattern b pneg :=
    (A.arrangementFaceOf_eq_iff_arrangementPointSignPattern_eq b ppos pneg).mp
      hface
  exact A.arrangementPointSignPattern_normalPerturbation_pos_ne_neg q l b
    hregular hbl hε ht htsmall (by simpa only [ppos, pneg] using hpattern)

private theorem eulerAffineVector_ne_zero (t : ℝ) :
    (![1, t] : RealProjectiveLineVector) ≠ 0 := by
  intro hzero
  have hfirst := congrFun hzero (0 : Fin 2)
  norm_num at hfirst

private noncomputable def eulerAffinePoint
    (t : ℝ) : RealProjectiveOnePoint :=
  Projectivization.mk ℝ (![1, t] : RealProjectiveLineVector)
    (eulerAffineVector_ne_zero t)

private theorem eulerAffinePoint_injective :
    Function.Injective eulerAffinePoint := by
  intro s t hst
  have hbracket :=
    (realProjective_mk_eq_mk_iff_bracket_eq_zero
      (eulerAffineVector_ne_zero s) (eulerAffineVector_ne_zero t)).mp hst
  simp [realProjectiveBracket] at hbracket
  linarith

private noncomputable instance eulerInfiniteRealProjectiveOnePoint :
    Infinite RealProjectiveOnePoint :=
  Infinite.of_injective eulerAffinePoint eulerAffinePoint_injective

/-- Two distinct indexed projective lines have exactly two complement
components. -/
theorem card_arrangementFace_bool
    (A : FiniteProjectiveLineArrangement Bool) :
    Fintype.card A.ArrangementFace = 2 := by
  classical
  let x := A.intersection false true
  have hxtrue : A.Incident x true :=
    A.intersection_incident_right (by decide)
  let P := projectiveLineParameterPreimage (A.projectiveLine true) x hxtrue
  obtain ⟨Q, hQ⟩ :=
    Infinite.exists_notMem_finset ({P} : Finset RealProjectiveOnePoint)
  have hQP : Q ≠ P := by simpa using hQ
  let q := projectiveLineParameter (A.projectiveLine true) Q
  have hqtrue : A.Incident q true :=
    projectiveLineParameter_incident (A.projectiveLine true) Q
  have hqfalse : ¬ A.Incident q false := by
    intro hqfalse
    have hqx : q = x :=
      A.eq_intersection_of_incident (by decide) hqfalse hqtrue
    apply hQP
    apply projectiveLineParameter_injective (A.projectiveLine true)
    calc
      projectiveLineParameter (A.projectiveLine true) Q = q := rfl
      _ = x := hqx
      _ = projectiveLineParameter (A.projectiveLine true) P :=
        (projectiveLineParameter_preimage_spec
          (A.projectiveLine true) x hxtrue).symm
  have hregular : ∀ m : Bool, A.Incident q m ↔ m = true := by
    intro m
    cases m <;> simp [hqfalse, hqtrue]
  obtain ⟨F, G, hFG⟩ :=
    A.exists_two_distinct_arrangementFaces_of_regular_of_ne
      q true false hregular (by decide)
  have hlower : 2 ≤ Fintype.card A.ArrangementFace := by
    calc
      2 = ({F, G} : Finset A.ArrangementFace).card :=
        (Finset.card_pair hFG).symm
      _ ≤ Fintype.card A.ArrangementFace := by
        simpa using Finset.card_le_card (Finset.subset_univ {F, G})
  let side : A.ArrangementFace → Bool :=
    fun H => A.arrangementFaceSignPattern false H true
  have hside : Function.Injective side := by
    intro H K hHK
    apply A.arrangementFaceSignPattern_injective false
    funext b
    cases b with
    | false =>
        simp only [arrangementFaceSignPattern, arrangementPointSignPattern,
          A.projectiveLineEvaluation_arrangementNormalizedRepresentative_base]
    | true => simpa only [side] using hHK
  have hupper : Fintype.card A.ArrangementFace ≤ 2 := by
    simpa using Fintype.card_le_of_injective side hside
  omega

theorem vertexSet_bool
    (A : FiniteProjectiveLineArrangement Bool) :
    A.vertexSet = {A.intersection false true} := by
  classical
  apply Finset.eq_singleton_iff_unique_mem.mpr
  refine ⟨A.intersection_mem_vertexSet (by decide), ?_⟩
  intro p hp
  obtain ⟨l, m, hlm, rfl⟩ := A.exists_lines_of_mem_vertexSet hp
  cases l <;> cases m
  · exact (hlm rfl).elim
  · rfl
  · apply A.eq_intersection_of_incident (by decide)
    · exact A.intersection_incident_right hlm
    · exact A.intersection_incident_left hlm
  · exact (hlm rfl).elim

theorem multiplicity_intersection_bool
    (A : FiniteProjectiveLineArrangement Bool) :
    A.multiplicity (A.intersection false true) = 2 := by
  classical
  have hlower := A.two_le_multiplicity_intersection (show false ≠ true by decide)
  have hupper : A.multiplicity (A.intersection false true) ≤ 2 := by
    unfold multiplicity
    simpa using Finset.card_filter_le (Finset.univ : Finset Bool)
      (fun l => A.Incident (A.intersection false true) l)
  omega

theorem arrangementVertexExcess_bool
    (A : FiniteProjectiveLineArrangement Bool) :
    A.arrangementVertexExcess = 1 := by
  classical
  unfold arrangementVertexExcess
  rw [A.vertexSet_bool]
  simp [A.multiplicity_intersection_bool]

theorem regionCount_bool
    (A : FiniteProjectiveLineArrangement Bool) :
    Fintype.card A.ArrangementFace = A.arrangementVertexExcess + 1 := by
  rw [A.card_arrangementFace_bool, A.arrangementVertexExcess_bool]

theorem regionCount_of_card_eq_two
    (A : FiniteProjectiveLineArrangement Line)
    (hcard : Fintype.card Line = 2) :
    Fintype.card A.ArrangementFace = A.arrangementVertexExcess + 1 := by
  let eBool : Bool ≃ Fin 2 := finTwoEquiv.symm
  let e : Bool ≃ Line :=
    eBool.trans (Fintype.equivFinOfCardEq hcard).symm
  exact A.regionCount_of_reindex e ((A.reindex e).regionCount_bool)

/-! ## The precise deletion/insertion interface -/

/-- Delete the distinguished `none` line.  This is an actual subarrangement,
not a formal incidence proxy: all remaining projective covectors are reused
unchanged. -/
def deleteNone
    (A : FiniteProjectiveLineArrangement (Option Line)) :
    FiniteProjectiveLineArrangement Line where
  projectiveLine l := A.projectiveLine (some l)
  projectiveLine_injective := by
    intro l m hlm
    have hsome : (some l : Option Line) = some m :=
      A.projectiveLine_injective hlm
    exact Option.some.inj hsome

@[simp] theorem deleteNone_incident
    (A : FiniteProjectiveLineArrangement (Option Line))
    (p : RealProjectivePoint) (l : Line) :
    A.deleteNone.Incident p l ↔ A.Incident p (some l) :=
  Iff.rfl

/-- Delete one chosen index by first presenting the original finite type as
an `Option` type. -/
def eraseLine
    (A : FiniteProjectiveLineArrangement Line) (r : Line) :
    FiniteProjectiveLineArrangement {l : Line // l ≠ r} :=
  (A.reindex (Equiv.optionSubtypeNe r)).deleteNone

@[simp] theorem eraseLine_projectiveLine
    (A : FiniteProjectiveLineArrangement Line) (r : Line)
    (l : {l : Line // l ≠ r}) :
    (A.eraseLine r).projectiveLine l = A.projectiveLine l.1 :=
  rfl

/-- The distinct cut points of the newly inserted line.  Since
`lineVertexSet` is a finset of actual projective points, concurrent old lines
through one cut are automatically identified. -/
noncomputable def insertionCutSet
    (A : FiniteProjectiveLineArrangement (Option Line)) :
    Finset RealProjectivePoint :=
  A.lineVertexSet none

/-- A point avoiding every line of the full arrangement also avoids every
old line after deleting `none`.  This is the canonical inclusion of the new
complement into the old one. -/
def forgetNoneComplement
    (A : FiniteProjectiveLineArrangement (Option Line)) :
    A.ArrangementComplement → A.deleteNone.ArrangementComplement :=
  fun p => ⟨p.1, fun l => p.2 (some l)⟩

/-- Deletion does not change the normalized homogeneous representative when
the base is an old line. -/
@[simp] theorem deleteNone_arrangementNormalizedRepresentative_forgetNone
    (A : FiniteProjectiveLineArrangement (Option Line))
    (base : Line) (p : A.ArrangementComplement) :
    A.deleteNone.arrangementNormalizedRepresentative base
        (A.forgetNoneComplement p) =
      A.arrangementNormalizedRepresentative (some base) p :=
  rfl

/-- Point sign words commute with deleting `none`: the old word is exactly
the restriction of the full word to `some`. -/
@[simp] theorem deleteNone_arrangementPointSignPattern_forgetNone
    (A : FiniteProjectiveLineArrangement (Option Line))
    (base : Line) (p : A.ArrangementComplement) (l : Line) :
    A.deleteNone.arrangementPointSignPattern base
        (A.forgetNoneComplement p) l =
      A.arrangementPointSignPattern (some base) p (some l) :=
  rfl

/-- Forget the newly inserted line at face level.  A representative of the
full face is regarded as an old complement point and then sent to its old
connected component. -/
noncomputable def forgetNoneFace
    (A : FiniteProjectiveLineArrangement (Option Line)) :
    A.ArrangementFace → A.deleteNone.ArrangementFace :=
  fun F => A.deleteNone.arrangementFaceOf
    (A.forgetNoneComplement (A.arrangementFaceRepresentative F))

/-- The face map agrees with the pointwise complement inclusion.  The base
line is used only to invoke the existing exact sign-pattern classification.
-/
theorem forgetNoneFace_arrangementFaceOf
    (A : FiniteProjectiveLineArrangement (Option Line))
    (base : Line) (p : A.ArrangementComplement) :
    A.forgetNoneFace (A.arrangementFaceOf p) =
      A.deleteNone.arrangementFaceOf (A.forgetNoneComplement p) := by
  unfold forgetNoneFace
  apply (A.deleteNone.arrangementFaceOf_eq_iff_arrangementPointSignPattern_eq
    base _ _).mpr
  funext l
  rw [A.deleteNone_arrangementPointSignPattern_forgetNone,
    A.deleteNone_arrangementPointSignPattern_forgetNone]
  exact congrFun
    (A.arrangementPointSignPattern_eq_of_arrangementFaceOf_eq
      (some base) _ p
      (A.arrangementFaceRepresentative_faceOf (A.arrangementFaceOf p)))
    (some l)

/-- Face sign words commute with deletion.  This is the useful, choice-free
description of `forgetNoneFace`: all old coordinates are preserved. -/
theorem arrangementFaceSignPattern_forgetNoneFace
    (A : FiniteProjectiveLineArrangement (Option Line))
    (base : Line) (F : A.ArrangementFace) (l : Line) :
    A.deleteNone.arrangementFaceSignPattern base (A.forgetNoneFace F) l =
      A.arrangementFaceSignPattern (some base) F (some l) := by
  let p : A.ArrangementComplement := A.arrangementFaceRepresentative F
  let pOld : A.deleteNone.ArrangementComplement := A.forgetNoneComplement p
  have hface :
      A.deleteNone.arrangementFaceOf
          (A.deleteNone.arrangementFaceRepresentative
            (A.deleteNone.arrangementFaceOf pOld)) =
        A.deleteNone.arrangementFaceOf pOld :=
    A.deleteNone.arrangementFaceRepresentative_faceOf
      (A.deleteNone.arrangementFaceOf pOld)
  have hpattern :=
    A.deleteNone.arrangementPointSignPattern_eq_of_arrangementFaceOf_eq
      base _ pOld hface
  change A.deleteNone.arrangementPointSignPattern base
      (A.deleteNone.arrangementFaceRepresentative
        (A.deleteNone.arrangementFaceOf pOld)) l =
    A.arrangementPointSignPattern (some base) p (some l)
  rw [congrFun hpattern l]
  exact A.deleteNone_arrangementPointSignPattern_forgetNone base p l

/-- A full face is determined by its old face together with the one Boolean
side of the inserted line. -/
theorem forgetNoneFace_with_side_injective
    (A : FiniteProjectiveLineArrangement (Option Line)) (base : Line) :
    Function.Injective (fun F : A.ArrangementFace =>
      (A.forgetNoneFace F,
        A.arrangementFaceSignPattern (some base) F none)) := by
  intro F G hFG
  apply A.arrangementFaceSignPattern_injective (some base)
  funext i
  cases i with
  | none =>
      exact congrArg Prod.snd hFG
  | some l =>
      have hold : A.forgetNoneFace F = A.forgetNoneFace G :=
        congrArg Prod.fst hFG
      have hcoordinate := congrArg
        (fun H : A.deleteNone.ArrangementFace =>
          A.deleteNone.arrangementFaceSignPattern base H l) hold
      simpa only [A.arrangementFaceSignPattern_forgetNoneFace] using hcoordinate

/-- The finite fibre of the deletion map over one old face. -/
noncomputable def forgetNoneFaceFibre
    (A : FiniteProjectiveLineArrangement (Option Line))
    (F : A.deleteNone.ArrangementFace) : Finset A.ArrangementFace := by
  classical
  exact Finset.univ.filter fun G => A.forgetNoneFace G = F

@[simp] theorem mem_forgetNoneFaceFibre_iff
    (A : FiniteProjectiveLineArrangement (Option Line))
    (F : A.deleteNone.ArrangementFace) (G : A.ArrangementFace) :
    G ∈ A.forgetNoneFaceFibre F ↔ A.forgetNoneFace G = F := by
  classical
  simp [forgetNoneFaceFibre]

/-- Every deletion fibre has at most the two possible signs of the forgotten
coordinate. -/
theorem card_forgetNoneFaceFibre_le_two
    (A : FiniteProjectiveLineArrangement (Option Line))
    (base : Line) (F : A.deleteNone.ArrangementFace) :
    (A.forgetNoneFaceFibre F).card ≤ 2 := by
  classical
  let side : {G : A.ArrangementFace // G ∈ A.forgetNoneFaceFibre F} → Bool :=
    fun G => A.arrangementFaceSignPattern (some base) G.1 none
  have hside : Function.Injective side := by
    intro G H hGH
    apply Subtype.ext
    apply A.forgetNoneFace_with_side_injective base
    apply Prod.ext
    · exact (A.mem_forgetNoneFaceFibre_iff F G.1).mp G.2 |>.trans
        ((A.mem_forgetNoneFaceFibre_iff F H.1).mp H.2).symm
    · exact hGH
  have hcard := Fintype.card_le_of_injective side hside
  rw [Fintype.card_coe] at hcard
  exact hcard

/-- An old face is crossed by the inserted line when it contains a point of
that line.  Such a point avoids every old line, so in the full arrangement
it is automatically a regular point of the unique line `none`. -/
def insertionCrossedFace
    (A : FiniteProjectiveLineArrangement (Option Line))
    (F : A.deleteNone.ArrangementFace) : Prop :=
  ∃ q : A.deleteNone.ArrangementComplement,
    A.deleteNone.arrangementFaceOf q = F ∧ A.Incident q.1 none

/-- A point in the deleted complement which lies on `none` is incident with
exactly that one line in the full arrangement. -/
theorem incident_iff_eq_none_of_mem_deleteNoneComplement
    (A : FiniteProjectiveLineArrangement (Option Line))
    (q : A.deleteNone.ArrangementComplement)
    (hq : A.Incident q.1 none) :
    ∀ m : Option Line, A.Incident q.1 m ↔ m = none := by
  intro m
  cases m with
  | none => simp [hq]
  | some l =>
      constructor
      · intro h
        exact (q.2 l h).elim
      · intro h
        exact (Option.some_ne_none l h).elim

/-- If an old face meets the regular part of the inserted line, its positive
and negative normal perturbations give the two distinct full faces above it.
-/
theorem card_forgetNoneFaceFibre_eq_two_of_insertionCrossedFace
    (A : FiniteProjectiveLineArrangement (Option Line))
    (base : Line) (F : A.deleteNone.ArrangementFace)
    (hcross : A.insertionCrossedFace F) :
    (A.forgetNoneFaceFibre F).card = 2 := by
  classical
  rcases hcross with ⟨q, hqF, hqnone⟩
  let hregular : ∀ m : Option Line, A.Incident q.1 m ↔ m = none :=
    A.incident_iff_eq_none_of_mem_deleteNoneComplement q hqnone
  rcases A.exists_pos_sign_perturbation_radius_of_regular q.1 none hregular with
    ⟨ε, hεpos, hε⟩
  let t : ℝ := ε / 2
  have ht : 0 < t := by
    dsimp [t]
    exact half_pos hεpos
  have htsmall : |t| < ε := by
    rw [abs_of_pos ht]
    dsimp [t]
    linarith
  have hnegsmall : |-t| < ε := by simpa using htsmall
  let ppos : A.ArrangementComplement :=
    A.normalPerturbationComplementOfRegular q.1 none hregular hε
      (ne_of_gt ht) htsmall
  let pneg : A.ArrangementComplement :=
    A.normalPerturbationComplementOfRegular q.1 none hregular hε
      (neg_ne_zero.mpr (ne_of_gt ht)) hnegsmall
  have hforgetPattern :
      ∀ {s : ℝ} (hs : s ≠ 0) (hssmall : |s| < ε),
        A.deleteNone.arrangementPointSignPattern base
            (A.forgetNoneComplement
              (A.normalPerturbationComplementOfRegular q.1 none hregular hε
                hs hssmall)) =
          A.deleteNone.arrangementPointSignPattern base q := by
    intro s hs hssmall
    rw [A.deleteNone.arrangementPointSignPattern_eq_relativeSign base,
      A.deleteNone.arrangementPointSignPattern_eq_relativeSign base]
    funext m
    apply Bool.decide_congr
    change A.arrangementRelativeSign (some base) (some m)
        (A.projectiveNormalPerturbation q.1 none
          ((hregular none).mpr rfl) s) = 1 ↔
      A.arrangementRelativeSign (some base) (some m) q.1 = 1
    rw [A.arrangementRelativeSign_projectiveNormalPerturbation q.1 none
        (some base) (some m) ((hregular none).mpr rfl) s,
      A.arrangementRelativeSign_apply_rep, sign_mul, sign_mul,
      hε hssmall (some base) (by simp),
      hε hssmall (some m) (by simp)]
  have hpatternNe :
      A.arrangementPointSignPattern (some base) ppos ≠
        A.arrangementPointSignPattern (some base) pneg := by
    simpa only [ppos, pneg] using
      (A.arrangementPointSignPattern_normalPerturbation_pos_ne_neg
        q.1 none (some base) hregular (by simp) hε ht htsmall)
  have hfacesNe : A.arrangementFaceOf ppos ≠ A.arrangementFaceOf pneg := by
    intro hfaces
    apply hpatternNe
    exact A.arrangementPointSignPattern_eq_of_arrangementFaceOf_eq
      (some base) ppos pneg hfaces
  have holdPos :
      A.deleteNone.arrangementFaceOf (A.forgetNoneComplement ppos) =
        A.deleteNone.arrangementFaceOf q := by
    apply (A.deleteNone.arrangementFaceOf_eq_iff_arrangementPointSignPattern_eq
      base _ _).mpr
    simpa only [ppos] using hforgetPattern (ne_of_gt ht) htsmall
  have holdNeg :
      A.deleteNone.arrangementFaceOf (A.forgetNoneComplement pneg) =
        A.deleteNone.arrangementFaceOf q := by
    apply (A.deleteNone.arrangementFaceOf_eq_iff_arrangementPointSignPattern_eq
      base _ _).mpr
    simpa only [pneg] using
      hforgetPattern (neg_ne_zero.mpr (ne_of_gt ht)) hnegsmall
  have hforgetPos : A.forgetNoneFace (A.arrangementFaceOf ppos) = F := by
    rw [A.forgetNoneFace_arrangementFaceOf base ppos, holdPos, hqF]
  have hforgetNeg : A.forgetNoneFace (A.arrangementFaceOf pneg) = F := by
    rw [A.forgetNoneFace_arrangementFaceOf base pneg, holdNeg, hqF]
  have hpairSubset :
      ({A.arrangementFaceOf ppos, A.arrangementFaceOf pneg} :
          Finset A.ArrangementFace) ⊆ A.forgetNoneFaceFibre F := by
    intro G hG
    simp only [Finset.mem_insert, Finset.mem_singleton] at hG
    rcases hG with rfl | rfl
    · exact (A.mem_forgetNoneFaceFibre_iff F _).mpr hforgetPos
    · exact (A.mem_forgetNoneFaceFibre_iff F _).mpr hforgetNeg
  have hlower : 2 ≤ (A.forgetNoneFaceFibre F).card := by
    have hcard := Finset.card_le_card hpairSubset
    rw [Finset.card_pair hfacesNe] at hcard
    exact hcard
  have hupper := A.card_forgetNoneFaceFibre_le_two base F
  omega

/-- Conversely, two full faces over one old face force that old face to meet
the inserted line.  The two face words agree on every old coordinate and
differ at `none`; a positive combination of normalized representatives with
opposite `none` evaluations stays in the common old strict cone and has
`none` evaluation zero. -/
theorem insertionCrossedFace_of_card_forgetNoneFaceFibre_eq_two
    (A : FiniteProjectiveLineArrangement (Option Line))
    (base : Line) (F : A.deleteNone.ArrangementFace)
    (hcard : (A.forgetNoneFaceFibre F).card = 2) :
    A.insertionCrossedFace F := by
  classical
  obtain ⟨G, H, hGH, hfibre⟩ := Finset.card_eq_two.mp hcard
  have hGmem : G ∈ A.forgetNoneFaceFibre F := by
    rw [hfibre]
    simp
  have hHmem : H ∈ A.forgetNoneFaceFibre F := by
    rw [hfibre]
    simp
  have hforgetG : A.forgetNoneFace G = F :=
    (A.mem_forgetNoneFaceFibre_iff F G).mp hGmem
  have hforgetH : A.forgetNoneFace H = F :=
    (A.mem_forgetNoneFaceFibre_iff F H).mp hHmem
  let p : A.ArrangementComplement := A.arrangementFaceRepresentative G
  let q : A.ArrangementComplement := A.arrangementFaceRepresentative H
  let pOld : A.deleteNone.ArrangementComplement := A.forgetNoneComplement p
  let qOld : A.deleteNone.ArrangementComplement := A.forgetNoneComplement q
  have hpOldFace : A.deleteNone.arrangementFaceOf pOld = F := by
    calc
      A.deleteNone.arrangementFaceOf pOld =
          A.forgetNoneFace (A.arrangementFaceOf p) :=
        (A.forgetNoneFace_arrangementFaceOf base p).symm
      _ = A.forgetNoneFace G := by
        rw [A.arrangementFaceRepresentative_faceOf G]
      _ = F := hforgetG
  have hqOldFace : A.deleteNone.arrangementFaceOf qOld = F := by
    calc
      A.deleteNone.arrangementFaceOf qOld =
          A.forgetNoneFace (A.arrangementFaceOf q) :=
        (A.forgetNoneFace_arrangementFaceOf base q).symm
      _ = A.forgetNoneFace H := by
        rw [A.arrangementFaceRepresentative_faceOf H]
      _ = F := hforgetH
  have holdPattern :
      A.deleteNone.arrangementPointSignPattern base pOld =
        A.deleteNone.arrangementPointSignPattern base qOld :=
    A.deleteNone.arrangementPointSignPattern_eq_of_arrangementFaceOf_eq
      base pOld qOld (hpOldFace.trans hqOldFace.symm)
  let sigma : Line → Bool :=
    A.deleteNone.arrangementPointSignPattern base pOld
  let u : Fin 3 → ℝ := A.arrangementNormalizedRepresentative (some base) p
  let v : Fin 3 → ℝ := A.arrangementNormalizedRepresentative (some base) q
  have hu : u ∈ A.deleteNone.arrangementSignCone sigma := by
    simpa only [u, sigma, pOld,
      A.deleteNone_arrangementNormalizedRepresentative_forgetNone] using
      (A.deleteNone.arrangementNormalizedRepresentative_mem_arrangementSignCone
        base pOld)
  have hv : v ∈ A.deleteNone.arrangementSignCone sigma := by
    have hv' :=
      A.deleteNone.arrangementNormalizedRepresentative_mem_arrangementSignCone
        base qOld
    rw [← holdPattern] at hv'
    simpa only [v, sigma, qOld,
      A.deleteNone_arrangementNormalizedRepresentative_forgetNone] using hv'
  have hsideNe :
      A.arrangementFaceSignPattern (some base) G none ≠
        A.arrangementFaceSignPattern (some base) H none := by
    intro hside
    apply hGH
    apply A.forgetNoneFace_with_side_injective base
    apply Prod.ext
    · exact hforgetG.trans hforgetH.symm
    · exact hside
  let fu : ℝ := projectiveLineEvaluation (A.projectiveLine none) u
  let fv : ℝ := projectiveLineEvaluation (A.projectiveLine none) v
  have hsideCodeG :
      A.arrangementFaceSignPattern (some base) G none = decide (0 < fu) := by
    rfl
  have hsideCodeH :
      A.arrangementFaceSignPattern (some base) H none = decide (0 < fv) := by
    rfl
  rw [hsideCodeG, hsideCodeH] at hsideNe
  have hfuNe : fu ≠ 0 := by
    dsimp [fu, u]
    unfold arrangementNormalizedRepresentative
    rw [LinearMap.map_smul]
    simp only [smul_eq_mul]
    exact mul_ne_zero
      (inv_ne_zero (A.projectiveLineEvaluation_rep_ne_zero p (some base)))
      (A.projectiveLineEvaluation_rep_ne_zero p none)
  have hfvNe : fv ≠ 0 := by
    dsimp [fv, v]
    unfold arrangementNormalizedRepresentative
    rw [LinearMap.map_smul]
    simp only [smul_eq_mul]
    exact mul_ne_zero
      (inv_ne_zero (A.projectiveLineEvaluation_rep_ne_zero q (some base)))
      (A.projectiveLineEvaluation_rep_ne_zero q none)
  have hopposite : (0 < fu ∧ fv < 0) ∨ (fu < 0 ∧ 0 < fv) := by
    by_cases hfu : 0 < fu
    · left
      refine ⟨hfu, ?_⟩
      have hnot : ¬ 0 < fv := by
        intro hfv
        exact hsideNe (by simp [hfu, hfv])
      exact lt_of_le_of_ne (le_of_not_gt hnot) hfvNe
    · right
      have hfuNeg : fu < 0 :=
        lt_of_le_of_ne (le_of_not_gt hfu) hfuNe
      refine ⟨hfuNeg, ?_⟩
      by_contra hfv
      exact hsideNe (by simp [hfu, hfv])
  let z : Fin 3 → ℝ := |fv| • u + |fu| • v
  have hzzero :
      projectiveLineEvaluation (A.projectiveLine none) z = 0 := by
    dsimp [z]
    rw [LinearMap.map_add, LinearMap.map_smul, LinearMap.map_smul]
    simp only [smul_eq_mul]
    change |fv| * fu + |fu| * fv = 0
    rcases hopposite with hsign | hsign
    · rw [abs_of_neg hsign.2, abs_of_pos hsign.1]
      ring
    · rw [abs_of_pos hsign.2, abs_of_neg hsign.1]
      ring
  have hz : z ∈ A.deleteNone.arrangementSignCone sigma := by
    simp only [arrangementSignCone, Set.mem_iInter] at hu hv ⊢
    intro l
    have hul := hu l
    have hvl := hv l
    by_cases hsigma : sigma l
    · simp only [hsigma, if_true] at hul hvl ⊢
      dsimp [z]
      rw [LinearMap.map_add, LinearMap.map_smul, LinearMap.map_smul]
      simp only [smul_eq_mul]
      exact add_pos
        (mul_pos (abs_pos.mpr hfvNe) hul)
        (mul_pos (abs_pos.mpr hfuNe) hvl)
    · simp only [hsigma, if_false] at hul hvl ⊢
      dsimp [z]
      rw [LinearMap.map_add, LinearMap.map_smul, LinearMap.map_smul]
      simp only [smul_eq_mul]
      exact add_neg
        (mul_neg_of_pos_of_neg (abs_pos.mpr hfvNe) hul)
        (mul_neg_of_pos_of_neg (abs_pos.mpr hfuNe) hvl)
  let qCross : A.deleteNone.ArrangementComplement :=
    A.deleteNone.arrangementSignConeToComplement base sigma ⟨z, hz⟩
  have huMap :
      A.deleteNone.arrangementSignConeToComplement base sigma ⟨u, hu⟩ =
        pOld := by
    simpa only [sigma, u, pOld,
      A.deleteNone_arrangementNormalizedRepresentative_forgetNone] using
      (A.deleteNone.arrangementSignConeToComplement_normalizedRepresentative
        base pOld)
  have hjoinedCone :
      Joined
        (⟨u, hu⟩ :
          {w : Fin 3 → ℝ // w ∈ A.deleteNone.arrangementSignCone sigma})
        ⟨z, hz⟩ := by
    exact
      ((A.deleteNone.convex_arrangementSignCone sigma).isPathConnected
        ⟨u, hu⟩).joinedIn u hu z hz |>.joined_subtype
  have hjoinedOld : Joined pOld qCross := by
    refine ⟨(hjoinedCone.somePath.map
      (A.deleteNone.continuous_arrangementSignConeToComplement base sigma)).cast
        huMap.symm ?_⟩
    rfl
  have hqCrossFace : A.deleteNone.arrangementFaceOf qCross = F := by
    have hface : A.deleteNone.arrangementFaceOf pOld =
        A.deleteNone.arrangementFaceOf qCross :=
      (A.deleteNone.arrangementFaceOf_eq_iff_joined pOld qCross).mpr hjoinedOld
    rw [← hface]
    exact hpOldFace
  have hqCrossNone : A.Incident qCross.1 none := by
    change (Projectivization.mk' ℝ
      ⟨z, A.deleteNone.arrangementSignCone_ne_zero base sigma hz⟩).orthogonal
        (A.projectiveLine none)
    rw [Projectivization.mk'_eq_mk,
      ← (A.projectiveLine none).mk_rep,
      Projectivization.orthogonal_mk]
    simpa [projectiveLineEvaluation] using hzzero
  exact ⟨qCross, hqCrossFace, hqCrossNone⟩

/-- Exact local deletion theorem: an old face has two lifts precisely when
the inserted line crosses it. -/
theorem card_forgetNoneFaceFibre_eq_two_iff_insertionCrossedFace
    (A : FiniteProjectiveLineArrangement (Option Line))
    (base : Line) (F : A.deleteNone.ArrangementFace) :
    (A.forgetNoneFaceFibre F).card = 2 ↔ A.insertionCrossedFace F := by
  constructor
  · exact A.insertionCrossedFace_of_card_forgetNoneFaceFibre_eq_two base F
  · exact A.card_forgetNoneFaceFibre_eq_two_of_insertionCrossedFace base F

/-- Every old face has at least one full face above it.  If its chosen point
misses `none` it is already a full complement point; if it lies on `none`,
the positive/negative perturbation theorem supplies two lifts. -/
theorem forgetNoneFace_surjective
    (A : FiniteProjectiveLineArrangement (Option Line)) (base : Line) :
    Function.Surjective A.forgetNoneFace := by
  classical
  intro F
  let q : A.deleteNone.ArrangementComplement :=
    A.deleteNone.arrangementFaceRepresentative F
  by_cases hnone : A.Incident q.1 none
  · have hcross : A.insertionCrossedFace F :=
      ⟨q, A.deleteNone.arrangementFaceRepresentative_faceOf F, hnone⟩
    have hcard :=
      A.card_forgetNoneFaceFibre_eq_two_of_insertionCrossedFace base F hcross
    have hnonempty : (A.forgetNoneFaceFibre F).Nonempty :=
      Finset.card_pos.mp (by omega)
    rcases hnonempty with ⟨G, hG⟩
    exact ⟨G, (A.mem_forgetNoneFaceFibre_iff F G).mp hG⟩
  · let p : A.ArrangementComplement :=
      ⟨q.1, by
        intro m
        cases m with
        | none => exact hnone
        | some l => exact q.2 l⟩
    refine ⟨A.arrangementFaceOf p, ?_⟩
    rw [A.forgetNoneFace_arrangementFaceOf base p]
    have hpOld : A.forgetNoneComplement p = q := by
      apply Subtype.ext
      rfl
    rw [hpOld]
    exact A.deleteNone.arrangementFaceRepresentative_faceOf F

/-- The finite set of old faces actually crossed by the inserted line. -/
noncomputable def insertionCrossedFaces
    (A : FiniteProjectiveLineArrangement (Option Line)) :
    Finset A.deleteNone.ArrangementFace := by
  classical
  exact Finset.univ.filter A.insertionCrossedFace

@[simp] theorem mem_insertionCrossedFaces_iff
    (A : FiniteProjectiveLineArrangement (Option Line))
    (F : A.deleteNone.ArrangementFace) :
    F ∈ A.insertionCrossedFaces ↔ A.insertionCrossedFace F := by
  classical
  simp [insertionCrossedFaces]

/-- Fibrewise counting now gives the exact face increment in terms of the
geometrically crossed old faces.  No cyclic-coverage statement is used. -/
theorem card_arrangementFace_eq_deleteNone_add_card_insertionCrossedFaces
    (A : FiniteProjectiveLineArrangement (Option Line)) (base : Line) :
    Fintype.card A.ArrangementFace =
      Fintype.card A.deleteNone.ArrangementFace +
        A.insertionCrossedFaces.card := by
  classical
  have hsurj := A.forgetNoneFace_surjective base
  have hfibre : ∀ F : A.deleteNone.ArrangementFace,
      (A.forgetNoneFaceFibre F).card =
        1 + if A.insertionCrossedFace F then 1 else 0 := by
    intro F
    have hpos : 1 ≤ (A.forgetNoneFaceFibre F).card := by
      rcases hsurj F with ⟨G, hG⟩
      exact Finset.one_le_card.mpr
        ⟨G, (A.mem_forgetNoneFaceFibre_iff F G).mpr hG⟩
    have hle := A.card_forgetNoneFaceFibre_le_two base F
    by_cases hcross : A.insertionCrossedFace F
    · have heq :=
        A.card_forgetNoneFaceFibre_eq_two_of_insertionCrossedFace
          base F hcross
      simp [hcross, heq]
    · have hne : (A.forgetNoneFaceFibre F).card ≠ 2 := by
        intro heq
        exact hcross
          ((A.card_forgetNoneFaceFibre_eq_two_iff_insertionCrossedFace
            base F).mp heq)
      have heq : (A.forgetNoneFaceFibre F).card = 1 := by omega
      simp [hcross, heq]
  have hsum :
      Fintype.card A.ArrangementFace =
        ∑ F : A.deleteNone.ArrangementFace,
          (A.forgetNoneFaceFibre F).card := by
    simp only [← Finset.card_univ, forgetNoneFaceFibre]
    exact Finset.card_eq_sum_card_fiberwise (by simp)
  rw [hsum]
  calc
    (∑ F : A.deleteNone.ArrangementFace,
        (A.forgetNoneFaceFibre F).card) =
        ∑ F : A.deleteNone.ArrangementFace,
          (1 + if A.insertionCrossedFace F then 1 else 0) := by
      apply Finset.sum_congr rfl
      intro F _hF
      exact hfibre F
    _ = (∑ _F : A.deleteNone.ArrangementFace, 1) +
          ∑ F : A.deleteNone.ArrangementFace,
            (if A.insertionCrossedFace F then 1 else 0) := by
      rw [Finset.sum_add_distrib]
    _ = Fintype.card A.deleteNone.ArrangementFace +
          A.insertionCrossedFaces.card := by
      congr 1
      · simp
      · rw [← Finset.sum_filter]
        simp [insertionCrossedFaces]

/-- Once crossed old faces are identified with the cyclic gaps of `none`,
the standard deletion/insertion face count follows immediately. -/
theorem card_arrangementFace_eq_deleteNone_add_card_insertionCutSet_of_crossed
    (A : FiniteProjectiveLineArrangement (Option Line)) (base : Line)
    (hcrossed : A.insertionCrossedFaces.card = A.insertionCutSet.card) :
    Fintype.card A.ArrangementFace =
      Fintype.card A.deleteNone.ArrangementFace +
        A.insertionCutSet.card := by
  rw [A.card_arrangementFace_eq_deleteNone_add_card_insertionCrossedFaces base,
    hcrossed]

/-! ## Cyclic gaps on the inserted line -/

/-- Circular gap slots on `none` are literally the points of the insertion
cut set, so their cardinality is the required face increment. -/
theorem card_insertionCircularGapSlot_eq_card_insertionCutSet
    (A : FiniteProjectiveLineArrangement (Option Line)) :
    Fintype.card (A.CircularGapSlot none) = A.insertionCutSet.card := by
  simpa [insertionCutSet] using Fintype.card_coe (A.lineVertexSet none)

/-- Two distinct cut points on one arrangement line rule out a pencil. -/
theorem nonPencil_of_one_lt_card_insertionCutSet
    (A : FiniteProjectiveLineArrangement (Option Line))
    (hcard : 1 < A.insertionCutSet.card) : A.NonPencil := by
  classical
  have hgapCard : 1 < Fintype.card (A.CircularGapSlot none) := by
    rw [A.card_insertionCircularGapSlot_eq_card_insertionCutSet]
    exact hcard
  obtain ⟨g, r, hgr⟩ := Fintype.one_lt_card_iff.mp hgapCard
  intro hpencil
  rcases hpencil with ⟨P, hP⟩
  have hpoint (s : A.CircularGapSlot none) : s.1 = P := by
    have hsVertex : s.1 ∈ A.vertexSet :=
      ((A.mem_lineVertexSet none).mp s.2).1
    obtain ⟨l, m, hlm, hintersection⟩ :=
      A.exists_lines_of_mem_vertexSet hsVertex
    have hPintersection : P = A.intersection l m :=
      A.eq_intersection_of_incident hlm (hP l) (hP m)
    exact hintersection.symm.trans hPintersection.symm
  apply hgr
  apply Subtype.ext
  exact (hpoint g).trans (hpoint r).symm

/-- The geometric edge represented by one cyclic gap of the inserted line.
Its underlying edge slot is obtained from the existing exact sigma
equivalence. -/
noncomputable def insertionGapEdge
    (A : FiniteProjectiveLineArrangement (Option Line))
    (g : A.CircularGapSlot none) : A.GeometricEdge :=
  A.edgeSlotEquivCircularGap.symm ⟨none, g⟩

@[simp] theorem insertionGapEdge_line
    (A : FiniteProjectiveLineArrangement (Option Line))
    (g : A.CircularGapSlot none) :
    A.edgeSlotLine (A.insertionGapEdge g) = none :=
  rfl

/-- A point on `none` which misses every old line is not one of the marked
vertices defining its cyclic gaps. -/
theorem insertionRegularPoint_ne_gapVertex
    (A : FiniteProjectiveLineArrangement (Option Line))
    (q : RealProjectivePoint) (hqnone : A.Incident q none)
    (hqOld : ∀ l : Line, ¬ A.Incident q (some l))
    (g : A.CircularGapSlot none) : q ≠ g.1 := by
  intro hqg
  have hqVertex : q ∈ A.vertexSet := by
    rw [hqg]
    exact ((A.mem_lineVertexSet none).mp g.2).1
  obtain ⟨l, m, hlm, hintersection⟩ :=
    A.exists_lines_of_mem_vertexSet hqVertex
  have hql : A.Incident q l := by
    rw [← hintersection]
    exact A.intersection_incident_left hlm
  have hqm : A.Incident q m := by
    rw [← hintersection]
    exact A.intersection_incident_right hlm
  have hregular : ∀ n : Option Line, A.Incident q n ↔ n = none :=
    A.incident_iff_eq_none_of_mem_deleteNoneComplement
      ⟨q, hqOld⟩ hqnone
  exact hlm (((hregular l).mp hql).trans ((hregular m).mp hqm).symm)

/-- Full cyclic coverage, including the chart-pole point: every regular
point of `none` lies in one of its genuine geometric gap arcs. -/
theorem exists_insertionGap_mem_openArc_of_regular
    (A : FiniteProjectiveLineArrangement (Option Line))
    (hcard : 1 < A.insertionCutSet.card)
    (q : RealProjectivePoint) (hqnone : A.Incident q none)
    (hqOld : ∀ l : Line, ¬ A.Incident q (some l)) :
    ∃ g : A.CircularGapSlot none,
      q ∈ A.geometricEdgeOpenArc (A.insertionGapEdge g) := by
  classical
  let Q : RealProjectiveOnePoint :=
    projectiveLineParameterPreimage (A.projectiveLine none) q hqnone
  have hQmap : projectiveLineParameter (A.projectiveLine none) Q = q :=
    projectiveLineParameter_preimage_spec (A.projectiveLine none) q hqnone
  have hQne (g : A.CircularGapSlot none) :
      Q ≠ circularGapSlotParameter A none g := by
    intro heq
    apply A.insertionRegularPoint_ne_gapVertex q hqnone hqOld g
    calc
      q = projectiveLineParameter (A.projectiveLine none) Q := hQmap.symm
      _ = projectiveLineParameter (A.projectiveLine none)
          (circularGapSlotParameter A none g) := congrArg _ heq
      _ = g.1 := A.projectiveLineParameter_circularGapSlotParameter none g
  have hgapCard : 1 < Fintype.card (A.CircularGapSlot none) := by
    rw [A.card_insertionCircularGapSlot_eq_card_insertionCutSet]
    exact hcard
  rcases exists_realProjectiveCyclic_between_projectiveCyclicSuccessor
      (circularGapSlotParameter A none)
      (A.circularGapSlotParameter_injective none) hgapCard Q hQne with
    ⟨g, hcyclic⟩
  refine ⟨g, ?_⟩
  change ProjectiveLineCyclic (A.projectiveLine none) g.1 q
    (A.circularGapSuccessor none g).1
  rw [← hQmap,
    ← A.projectiveLineParameter_circularGapSlotParameter none g,
    ← A.projectiveLineParameter_circularGapSlotParameter none
      (A.circularGapSuccessor none g),
    projectiveLineCyclic_parameter_iff]
  simpa only [circularGapSuccessor, circularGapSuccessorEquiv,
    projectiveCyclicSuccessor] using hcyclic

/-- Membership in an inserted-line geometric gap gives the corresponding
intrinsic `RP¹` cyclic relation. -/
theorem realProjectiveCyclic_of_mem_insertionGapOpenArc
    (A : FiniteProjectiveLineArrangement (Option Line))
    (q : RealProjectivePoint) (hqnone : A.Incident q none)
    (g : A.CircularGapSlot none)
    (hq : q ∈ A.geometricEdgeOpenArc (A.insertionGapEdge g)) :
    RealProjectiveCyclic
      (circularGapSlotParameter A none g)
      (projectiveLineParameterPreimage (A.projectiveLine none) q hqnone)
      (circularGapSlotParameter A none (A.circularGapSuccessor none g)) := by
  rw [← projectiveLineCyclic_parameter_iff,
    A.projectiveLineParameter_circularGapSlotParameter none g,
    projectiveLineParameter_preimage_spec,
    A.projectiveLineParameter_circularGapSlotParameter none
      (A.circularGapSuccessor none g)]
  change ProjectiveLineCyclic (A.projectiveLine none) g.1 q
    (A.circularGapSuccessor none g).1
  exact hq

/-- A regular point cannot belong to two different cyclic gap arcs. -/
theorem insertionGap_eq_of_mem_openArc
    (A : FiniteProjectiveLineArrangement (Option Line))
    (q : RealProjectivePoint) (g h : A.CircularGapSlot none)
    (hqg : q ∈ A.geometricEdgeOpenArc (A.insertionGapEdge g))
    (hqh : q ∈ A.geometricEdgeOpenArc (A.insertionGapEdge h)) :
    g = h := by
  have hqnone : A.Incident q none :=
    (A.geometricEdgeOpenArc_incident_iff (A.insertionGapEdge g) hqg none).mpr
      (by simp)
  apply unique_realProjectiveCyclic_between_projectiveCyclicSuccessor
    (circularGapSlotParameter A none)
    (A.circularGapSlotParameter_injective none)
    (projectiveLineParameterPreimage (A.projectiveLine none) q hqnone)
  · simpa only [circularGapSuccessor, circularGapSuccessorEquiv,
      projectiveCyclicSuccessor] using
      A.realProjectiveCyclic_of_mem_insertionGapOpenArc q hqnone g hqg
  · simpa only [circularGapSuccessor, circularGapSuccessorEquiv,
      projectiveCyclicSuccessor] using
      A.realProjectiveCyclic_of_mem_insertionGapOpenArc q hqnone h hqh

/-- Arrangement-level full partition of the regular part of `none` by its
cyclic geometric gaps. -/
theorem existsUnique_insertionGap_mem_openArc_of_regular
    (A : FiniteProjectiveLineArrangement (Option Line))
    (hcard : 1 < A.insertionCutSet.card)
    (q : RealProjectivePoint) (hqnone : A.Incident q none)
    (hqOld : ∀ l : Line, ¬ A.Incident q (some l)) :
    ∃! g : A.CircularGapSlot none,
      q ∈ A.geometricEdgeOpenArc (A.insertionGapEdge g) := by
  have hregular : ∀ m : Option Line, A.Incident q m ↔ m = none :=
    A.incident_iff_eq_none_of_mem_deleteNoneComplement ⟨q, hqOld⟩ hqnone
  simpa only [insertionGapEdge, circularGapEdge] using
    A.existsUnique_circularGap_mem_geometricEdgeOpenArc_of_regular
      (A.nonPencil_of_one_lt_card_insertionCutSet hcard) q none hregular

/-- With at least two cuts, every inserted-line gap is a genuine nonempty
open cyclic arc. -/
theorem insertionGapOpenArc_nonempty
    (A : FiniteProjectiveLineArrangement (Option Line))
    (hcard : 1 < A.insertionCutSet.card)
    (g : A.CircularGapSlot none) :
    (A.geometricEdgeOpenArc (A.insertionGapEdge g)).Nonempty :=
  (A.isPathConnected_geometricEdgeOpenArc
    (A.nonPencil_of_one_lt_card_insertionCutSet hcard)
    (A.insertionGapEdge g)).nonempty

/-- A selected regular point in each nondegenerate cyclic gap.  Subsequent
lemmas prove that the resulting old face is independent of all choices. -/
noncomputable def insertionGapPoint
    (A : FiniteProjectiveLineArrangement (Option Line))
    (hcard : 1 < A.insertionCutSet.card)
    (g : A.CircularGapSlot none) : RealProjectivePoint :=
  Classical.choose (A.insertionGapOpenArc_nonempty hcard g)

theorem insertionGapPoint_mem_openArc
    (A : FiniteProjectiveLineArrangement (Option Line))
    (hcard : 1 < A.insertionCutSet.card)
    (g : A.CircularGapSlot none) :
    A.insertionGapPoint hcard g ∈
      A.geometricEdgeOpenArc (A.insertionGapEdge g) :=
  Classical.choose_spec (A.insertionGapOpenArc_nonempty hcard g)

/-- A gap point misses every old line and therefore is an old complement
point. -/
noncomputable def insertionGapOldComplement
    (A : FiniteProjectiveLineArrangement (Option Line))
    (hcard : 1 < A.insertionCutSet.card)
    (g : A.CircularGapSlot none) : A.deleteNone.ArrangementComplement :=
  ⟨A.insertionGapPoint hcard g, by
    intro l hincident
    have heq :=
      (A.geometricEdgeOpenArc_incident_iff (A.insertionGapEdge g)
        (A.insertionGapPoint_mem_openArc hcard g) (some l)).mp hincident
    have : (some l : Option Line) = none := by simpa using heq
    exact Option.some_ne_none l this⟩

/-- The regular part of the inserted line, viewed inside the complement of
the deleted arrangement. -/
def insertionRegularLocus
    (A : FiniteProjectiveLineArrangement (Option Line)) :=
  {q : A.deleteNone.ArrangementComplement // A.Incident q.1 none}

noncomputable local instance insertionRegularLocusTopologicalSpaceForEulerFinish
    (A : FiniteProjectiveLineArrangement (Option Line)) :
    TopologicalSpace A.insertionRegularLocus :=
  TopologicalSpace.induced
    (fun q : A.insertionRegularLocus => q.1)
    (inferInstance : TopologicalSpace A.deleteNone.ArrangementComplement)

/-- The two natural presentations of the regular part of the inserted line
are canonically homeomorphic. -/
def insertionRegularLocusHomeomorphLineRegular
    (A : FiniteProjectiveLineArrangement (Option Line)) :
    A.insertionRegularLocus ≃ₜ A.lineRegularLocus none where
  toFun q :=
    ⟨q.1.1, A.incident_iff_eq_none_of_mem_deleteNoneComplement q.1 q.2⟩
  invFun q :=
    ⟨⟨q.1, fun l hl =>
        Option.some_ne_none l ((q.2 (some l)).mp hl)⟩,
      (q.2 none).mpr rfl⟩
  left_inv q := by
    rfl
  right_inv q := by
    rfl
  continuous_toFun :=
    (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  continuous_invFun :=
    (continuous_subtype_val.subtype_mk _).subtype_mk _

/-- The selected point of a genuine cyclic gap, regarded as a point of the
regular inserted-line locus. -/
noncomputable def insertionGapRegularPoint
    (A : FiniteProjectiveLineArrangement (Option Line))
    (hcard : 1 < A.insertionCutSet.card)
    (g : A.CircularGapSlot none) : A.insertionRegularLocus :=
  ⟨A.insertionGapOldComplement hcard g,
    (A.geometricEdgeOpenArc_incident_iff (A.insertionGapEdge g)
      (A.insertionGapPoint_mem_openArc hcard g) none).mpr (by simp)⟩

/-- The `RP¹` parameter of a regular point on the inserted line. -/
noncomputable def insertionRegularParameter
    (A : FiniteProjectiveLineArrangement (Option Line)) :
    A.insertionRegularLocus → RealProjectiveOnePoint :=
  fun q => (projectiveLineParameterHomeomorph_eulerFinish
    (A.projectiveLine none)).symm ⟨q.1.1, q.2⟩

theorem continuous_insertionRegularParameter
    (A : FiniteProjectiveLineArrangement (Option Line)) :
    Continuous A.insertionRegularParameter := by
  apply (projectiveLineParameterHomeomorph_eulerFinish
    (A.projectiveLine none)).symm.continuous.comp
  exact (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _

theorem projectiveLineParameter_insertionRegularParameter
    (A : FiniteProjectiveLineArrangement (Option Line))
    (q : A.insertionRegularLocus) :
    projectiveLineParameter (A.projectiveLine none)
      (A.insertionRegularParameter q) = q.1.1 := by
  have h := (projectiveLineParameterHomeomorph_eulerFinish
    (A.projectiveLine none)).apply_symm_apply ⟨q.1.1, q.2⟩
  simpa only [insertionRegularParameter] using congrArg Subtype.val h

/-- One cyclic gap, regarded as a subset of the regular inserted-line
locus. -/
def insertionGapRegularSet
    (A : FiniteProjectiveLineArrangement (Option Line))
    (g : A.CircularGapSlot none) : Set A.insertionRegularLocus :=
  {q | q.1.1 ∈ A.geometricEdgeOpenArc (A.insertionGapEdge g)}

theorem isOpen_insertionGapRegularSet
    (A : FiniteProjectiveLineArrangement (Option Line))
    (g : A.CircularGapSlot none) :
    IsOpen (A.insertionGapRegularSet g) := by
  let P := circularGapSlotParameter A none g
  let R := circularGapSlotParameter A none (A.circularGapSuccessor none g)
  have hopen : IsOpen
      (A.insertionRegularParameter ⁻¹'
        {Q : RealProjectiveOnePoint | RealProjectiveCyclic P Q R}) :=
    (isOpen_realProjectiveCyclic_middle P R).preimage
      A.continuous_insertionRegularParameter
  have hset :
      (A.insertionRegularParameter ⁻¹'
        {Q : RealProjectiveOnePoint | RealProjectiveCyclic P Q R}) =
        A.insertionGapRegularSet g := by
    ext q
    change RealProjectiveCyclic P (A.insertionRegularParameter q) R ↔
      q.1.1 ∈ A.geometricEdgeOpenArc (A.insertionGapEdge g)
    rw [← projectiveLineCyclic_parameter_iff,
      A.projectiveLineParameter_circularGapSlotParameter none g,
      A.projectiveLineParameter_insertionRegularParameter q,
      A.projectiveLineParameter_circularGapSlotParameter none
        (A.circularGapSuccessor none g)]
    rfl
  rw [hset] at hopen
  exact hopen

/-- Openness of cyclic-gap fibres in the regular-line presentation used by
the general clopen/path-separation router. -/
theorem isOpen_circularGapRegularFiber_none
    (A : FiniteProjectiveLineArrangement (Option Line))
    (g : A.CircularGapSlot none) :
    IsOpen (A.circularGapRegularFiber none g) := by
  change IsOpen
    ((A.insertionRegularLocusHomeomorphLineRegular).symm ⁻¹'
      A.insertionGapRegularSet g)
  exact
    (A.insertionRegularLocusHomeomorphLineRegular).symm.continuous.isOpen_preimage
      _ (A.isOpen_insertionGapRegularSet g)

/-- Distinct cyclic gaps give distinct path components of the regular part
of the inserted line. -/
theorem insertionGap_eq_of_joined_regular
    (A : FiniteProjectiveLineArrangement (Option Line))
    (hcard : 1 < A.insertionCutSet.card)
    (g h : A.CircularGapSlot none)
    (hjoined : Joined (A.insertionGapRegularPoint hcard g)
      (A.insertionGapRegularPoint hcard h)) :
    g = h := by
  let e := A.insertionRegularLocusHomeomorphLineRegular
  refine A.circularGap_eq_of_joined_regular_of_isOpen
    (A.nonPencil_of_one_lt_card_insertionCutSet hcard) none
    (fun k => A.isOpen_circularGapRegularFiber_none k)
    (e (A.insertionGapRegularPoint hcard g))
    (e (A.insertionGapRegularPoint hcard h)) g h ?_ ?_ ?_
  · change A.insertionGapPoint hcard g ∈
      A.geometricEdgeOpenArc (A.insertionGapEdge g)
    exact A.insertionGapPoint_mem_openArc hcard g
  · change A.insertionGapPoint hcard h ∈
      A.geometricEdgeOpenArc (A.insertionGapEdge h)
    exact A.insertionGapPoint_mem_openArc hcard h
  · exact ⟨hjoined.somePath.map e.continuous⟩

/-- The homogeneous slice of one old strict sign cone by the kernel of the
inserted covector.  Its projectivization is the part of one old face lying
on the regular locus of `none`. -/
def insertionFaceSliceCone
    (A : FiniteProjectiveLineArrangement (Option Line))
    (sigma : Line → Bool) : Set (Fin 3 → ℝ) :=
  A.deleteNone.arrangementSignCone sigma ∩
    (projectiveLineEvaluation (A.projectiveLine none)).ker

theorem convex_insertionFaceSliceCone
    (A : FiniteProjectiveLineArrangement (Option Line))
    (sigma : Line → Bool) :
    Convex ℝ (A.insertionFaceSliceCone sigma) := by
  unfold insertionFaceSliceCone
  apply (A.deleteNone.convex_arrangementSignCone sigma).inter
  simpa only [LinearMap.mem_ker] using
    (convex_hyperplane
      (IsLinearMap.mk
        (projectiveLineEvaluation (A.projectiveLine none)).map_add
        (projectiveLineEvaluation (A.projectiveLine none)).map_smul) 0)

/-- Projectivization of a sliced old sign cone lands in the regular locus of
the inserted line. -/
noncomputable def insertionFaceSliceToRegular
    (A : FiniteProjectiveLineArrangement (Option Line))
    (base : Line) (sigma : Line → Bool) :
    {v : Fin 3 → ℝ // v ∈ A.insertionFaceSliceCone sigma} →
      A.insertionRegularLocus :=
  fun v =>
    ⟨A.deleteNone.arrangementSignConeToComplement base sigma
        ⟨v.1, v.2.1⟩,
      by
        have hzero :
            projectiveLineEvaluation (A.projectiveLine none) v.1 = 0 :=
          v.2.2
        change (Projectivization.mk' ℝ
          ⟨v.1,
            A.deleteNone.arrangementSignCone_ne_zero base sigma v.2.1⟩).orthogonal
              (A.projectiveLine none)
        rw [Projectivization.mk'_eq_mk]
        have horth :
            (Projectivization.mk ℝ v.1
              (A.deleteNone.arrangementSignCone_ne_zero base sigma v.2.1)).orthogonal
              (Projectivization.mk ℝ (A.projectiveLine none).rep
                (A.projectiveLine none).rep_nonzero) := by
          apply (Projectivization.orthogonal_mk
            (A.deleteNone.arrangementSignCone_ne_zero base sigma v.2.1)
            (A.projectiveLine none).rep_nonzero).2
          simpa [projectiveLineEvaluation] using hzero
        simpa only [Projectivization.mk_rep] using horth⟩

theorem continuous_insertionFaceSliceToRegular
    (A : FiniteProjectiveLineArrangement (Option Line))
    (base : Line) (sigma : Line → Bool) :
    Continuous (A.insertionFaceSliceToRegular base sigma) := by
  unfold insertionFaceSliceToRegular
  exact
    ((A.deleteNone.continuous_arrangementSignConeToComplement base sigma).comp
      (continuous_subtype_val.subtype_mk fun v => v.2.1)).subtype_mk _

/-- Normalizing an old-complement point does not change the fact that it lies
in the kernel of the inserted covector. -/
theorem projectiveLineEvaluation_deleteNone_normalized_eq_zero
    (A : FiniteProjectiveLineArrangement (Option Line))
    (base : Line) (q : A.insertionRegularLocus) :
    projectiveLineEvaluation (A.projectiveLine none)
      (A.deleteNone.arrangementNormalizedRepresentative base q.1) = 0 := by
  unfold arrangementNormalizedRepresentative
  rw [LinearMap.map_smul]
  simp only [smul_eq_mul]
  rw [(A.projectiveLineEvaluation_rep_eq_zero_iff_incident q.1.1 none).mpr q.2,
    mul_zero]

theorem deleteNone_normalized_mem_insertionFaceSliceCone
    (A : FiniteProjectiveLineArrangement (Option Line))
    (base : Line) (q : A.insertionRegularLocus) :
    A.deleteNone.arrangementNormalizedRepresentative base q.1 ∈
      A.insertionFaceSliceCone
        (A.deleteNone.arrangementPointSignPattern base q.1) := by
  constructor
  · exact
      A.deleteNone.arrangementNormalizedRepresentative_mem_arrangementSignCone
        base q.1
  · exact A.projectiveLineEvaluation_deleteNone_normalized_eq_zero base q

theorem insertionFaceSliceToRegular_normalized
    (A : FiniteProjectiveLineArrangement (Option Line))
    (base : Line) (q : A.insertionRegularLocus) :
    A.insertionFaceSliceToRegular base
        (A.deleteNone.arrangementPointSignPattern base q.1)
        ⟨A.deleteNone.arrangementNormalizedRepresentative base q.1,
          A.deleteNone_normalized_mem_insertionFaceSliceCone base q⟩ = q := by
  apply Subtype.ext
  exact
    A.deleteNone.arrangementSignConeToComplement_normalizedRepresentative
      base q.1

theorem deleteNone_normalized_mem_insertionFaceSliceCone_of_pattern_eq
    (A : FiniteProjectiveLineArrangement (Option Line))
    (base : Line) (q r : A.insertionRegularLocus)
    (hpattern : A.deleteNone.arrangementPointSignPattern base q.1 =
      A.deleteNone.arrangementPointSignPattern base r.1) :
    A.deleteNone.arrangementNormalizedRepresentative base r.1 ∈
      A.insertionFaceSliceCone
        (A.deleteNone.arrangementPointSignPattern base q.1) := by
  rw [hpattern]
  exact A.deleteNone_normalized_mem_insertionFaceSliceCone base r

theorem insertionFaceSliceToRegular_normalized_of_pattern_eq
    (A : FiniteProjectiveLineArrangement (Option Line))
    (base : Line) (q r : A.insertionRegularLocus)
    (hpattern : A.deleteNone.arrangementPointSignPattern base q.1 =
      A.deleteNone.arrangementPointSignPattern base r.1) :
    A.insertionFaceSliceToRegular base
        (A.deleteNone.arrangementPointSignPattern base q.1)
        ⟨A.deleteNone.arrangementNormalizedRepresentative base r.1,
          A.deleteNone_normalized_mem_insertionFaceSliceCone_of_pattern_eq
            base q r hpattern⟩ = r := by
  have hrcone :
      A.deleteNone.arrangementNormalizedRepresentative base r.1 ∈
        A.deleteNone.arrangementSignCone
          (A.deleteNone.arrangementPointSignPattern base q.1) := by
    rw [hpattern]
    exact
      A.deleteNone.arrangementNormalizedRepresentative_mem_arrangementSignCone
        base r.1
  apply Subtype.ext
  exact
    A.deleteNone.arrangementSignConeToComplement_normalizedRepresentative_of_eq
      base (A.deleteNone.arrangementPointSignPattern base q.1) r.1
      hpattern hrcone

/-- Points where the inserted line crosses one fixed old face are joined
inside the regular part of that line.  This is the convex sign-cone part of
the gap-component classification; no cyclic coverage theorem is used. -/
theorem joined_insertionRegularLocus_of_same_oldFace
    (A : FiniteProjectiveLineArrangement (Option Line))
    (base : Line) (q r : A.insertionRegularLocus)
    (hface : A.deleteNone.arrangementFaceOf q.1 =
      A.deleteNone.arrangementFaceOf r.1) :
    Joined q r := by
  have hpattern :
      A.deleteNone.arrangementPointSignPattern base q.1 =
        A.deleteNone.arrangementPointSignPattern base r.1 :=
    A.deleteNone.arrangementPointSignPattern_eq_of_arrangementFaceOf_eq
      base q.1 r.1 hface
  let sigma : Line → Bool :=
    A.deleteNone.arrangementPointSignPattern base q.1
  let u : Fin 3 → ℝ :=
    A.deleteNone.arrangementNormalizedRepresentative base q.1
  let v : Fin 3 → ℝ :=
    A.deleteNone.arrangementNormalizedRepresentative base r.1
  have hu : u ∈ A.insertionFaceSliceCone sigma := by
    simpa only [u, sigma] using
      A.deleteNone_normalized_mem_insertionFaceSliceCone base q
  have hv : v ∈ A.insertionFaceSliceCone sigma := by
    simpa only [v, sigma] using
      A.deleteNone_normalized_mem_insertionFaceSliceCone_of_pattern_eq
        base q r hpattern
  have hjoinedSlice :
      Joined
        (⟨u, hu⟩ : {w : Fin 3 → ℝ //
          w ∈ A.insertionFaceSliceCone sigma})
        ⟨v, hv⟩ := by
    exact
      (((A.convex_insertionFaceSliceCone sigma).isPathConnected ⟨u, hu⟩).joinedIn
        u hu v hv).joined_subtype
  have huMap :
      A.insertionFaceSliceToRegular base sigma ⟨u, hu⟩ = q := by
    simpa only [u, sigma] using
      A.insertionFaceSliceToRegular_normalized base q
  have hvMap :
      A.insertionFaceSliceToRegular base sigma ⟨v, hv⟩ = r := by
    simpa only [v, sigma] using
      A.insertionFaceSliceToRegular_normalized_of_pattern_eq
        base q r hpattern
  exact ⟨(hjoinedSlice.somePath.map
    (A.continuous_insertionFaceSliceToRegular base sigma)).cast
      huMap.symm hvMap.symm⟩

/-- The old face met by a cyclic gap of the newly inserted line. -/
noncomputable def insertionGapOldFace
    (A : FiniteProjectiveLineArrangement (Option Line))
    (hcard : 1 < A.insertionCutSet.card)
    (g : A.CircularGapSlot none) : A.deleteNone.ArrangementFace :=
  A.deleteNone.arrangementFaceOf (A.insertionGapOldComplement hcard g)

/-- Every cyclic gap produces an actually crossed old face. -/
theorem insertionCrossedFace_insertionGapOldFace
    (A : FiniteProjectiveLineArrangement (Option Line))
    (hcard : 1 < A.insertionCutSet.card)
    (g : A.CircularGapSlot none) :
    A.insertionCrossedFace (A.insertionGapOldFace hcard g) := by
  refine ⟨A.insertionGapOldComplement hcard g, rfl, ?_⟩
  exact
    (A.geometricEdgeOpenArc_incident_iff (A.insertionGapEdge g)
      (A.insertionGapPoint_mem_openArc hcard g) none).mpr (by simp)

/-- The concrete map whose bijectivity is the remaining one-dimensional
coverage/separation theorem. -/
noncomputable def insertionGapToCrossedFace
    (A : FiniteProjectiveLineArrangement (Option Line))
    (hcard : 1 < A.insertionCutSet.card) :
    A.CircularGapSlot none → {F : A.deleteNone.ArrangementFace //
      A.insertionCrossedFace F} :=
  fun g => ⟨A.insertionGapOldFace hcard g,
    A.insertionCrossedFace_insertionGapOldFace hcard g⟩

/-- Once distinct cyclic gaps are known to be distinct path components of
the regular inserted-line locus, convexity of old sign cones gives
injectivity of the concrete gap-to-crossed-face map. -/
theorem insertionGapToCrossedFace_injective_of_joined_separation
    (A : FiniteProjectiveLineArrangement (Option Line))
    (base : Line) (hcard : 1 < A.insertionCutSet.card)
    (hseparation : ∀ g h : A.CircularGapSlot none,
      Joined (A.insertionGapRegularPoint hcard g)
        (A.insertionGapRegularPoint hcard h) → g = h) :
    Function.Injective (A.insertionGapToCrossedFace hcard) := by
  intro g h heq
  apply hseparation g h
  apply A.joined_insertionRegularLocus_of_same_oldFace base
  have hfaces : A.insertionGapOldFace hcard g =
      A.insertionGapOldFace hcard h :=
    congrArg Subtype.val heq
  simpa only [insertionGapRegularPoint, insertionGapOldFace] using hfaces

/-- Pointwise cyclic coverage is already enough for surjectivity of the gap
map.  Constancy of all old relative signs on one open arc identifies the
selected gap point with any crossed-face witness lying in that arc. -/
theorem insertionGapToCrossedFace_surjective_of_regular_coverage
    (A : FiniteProjectiveLineArrangement (Option Line))
    (base : Line) (hcard : 1 < A.insertionCutSet.card)
    (hcoverage : ∀ q : RealProjectivePoint,
      A.Incident q none →
      (∀ l : Line, ¬ A.Incident q (some l)) →
      ∃ g : A.CircularGapSlot none,
        q ∈ A.geometricEdgeOpenArc (A.insertionGapEdge g)) :
    Function.Surjective (A.insertionGapToCrossedFace hcard) := by
  classical
  rintro ⟨F, hcross⟩
  rcases hcross with ⟨q, hqF, hqnone⟩
  have hqOld : ∀ l : Line, ¬ A.Incident q.1 (some l) := fun l => q.2 l
  rcases hcoverage q.1 hqnone hqOld with ⟨g, hqArc⟩
  refine ⟨g, ?_⟩
  apply Subtype.ext
  change A.deleteNone.arrangementFaceOf
      (A.insertionGapOldComplement hcard g) = F
  rw [← hqF]
  apply
    (A.deleteNone.arrangementFaceOf_eq_iff_arrangementPointSignPattern_eq
      base _ _).mpr
  rw [A.deleteNone.arrangementPointSignPattern_eq_relativeSign base,
    A.deleteNone.arrangementPointSignPattern_eq_relativeSign base]
  funext l
  apply Bool.decide_congr
  change A.arrangementRelativeSign (some base) (some l)
      (A.insertionGapPoint hcard g) = 1 ↔
    A.arrangementRelativeSign (some base) (some l) q.1 = 1
  rw [A.arrangementRelativeSign_eq_of_mem_geometricEdgeOpenArc
    (A.nonPencil_of_one_lt_card_insertionCutSet hcard)
    (A.insertionGapEdge g) (some base) (some l)
    (by simp) (by simp)
    (A.insertionGapPoint_mem_openArc hcard g) hqArc]

/-- The public chart-pole-inclusive successor coverage discharges the
surjectivity side with no additional assumption. -/
theorem insertionGapToCrossedFace_surjective
    (A : FiniteProjectiveLineArrangement (Option Line))
    (base : Line) (hcard : 1 < A.insertionCutSet.card) :
    Function.Surjective (A.insertionGapToCrossedFace hcard) := by
  apply A.insertionGapToCrossedFace_surjective_of_regular_coverage base hcard
  intro q hqnone hqOld
  exact A.exists_insertionGap_mem_openArc_of_regular hcard q hqnone hqOld

/-- Exact topological seam for the nondegenerate insertion step: pointwise
coverage supplies surjectivity, while the statement that distinct gaps are
distinct path components supplies injectivity. -/
theorem insertionGapToCrossedFace_bijective_of_coverage_of_separation
    (A : FiniteProjectiveLineArrangement (Option Line))
    (base : Line) (hcard : 1 < A.insertionCutSet.card)
    (hcoverage : ∀ q : RealProjectivePoint,
      A.Incident q none →
      (∀ l : Line, ¬ A.Incident q (some l)) →
      ∃ g : A.CircularGapSlot none,
        q ∈ A.geometricEdgeOpenArc (A.insertionGapEdge g))
    (hseparation : ∀ g h : A.CircularGapSlot none,
      Joined (A.insertionGapRegularPoint hcard g)
        (A.insertionGapRegularPoint hcard h) → g = h) :
    Function.Bijective (A.insertionGapToCrossedFace hcard) := by
  constructor
  · exact A.insertionGapToCrossedFace_injective_of_joined_separation
      base hcard hseparation
  · exact A.insertionGapToCrossedFace_surjective_of_regular_coverage
      base hcard hcoverage

/-- After full cyclic coverage, only separation of distinct gap components
remains for bijectivity. -/
theorem insertionGapToCrossedFace_bijective_of_joined_separation
    (A : FiniteProjectiveLineArrangement (Option Line))
    (base : Line) (hcard : 1 < A.insertionCutSet.card)
    (hseparation : ∀ g h : A.CircularGapSlot none,
      Joined (A.insertionGapRegularPoint hcard g)
        (A.insertionGapRegularPoint hcard h) → g = h) :
    Function.Bijective (A.insertionGapToCrossedFace hcard) :=
  ⟨A.insertionGapToCrossedFace_injective_of_joined_separation
      base hcard hseparation,
    A.insertionGapToCrossedFace_surjective base hcard⟩

/-- A bijective gap-to-crossed-face classification immediately supplies the
last cardinal equality, with no further topology or incidence arithmetic. -/
theorem card_insertionCrossedFaces_eq_card_insertionCutSet_of_gap_bijective
    (A : FiniteProjectiveLineArrangement (Option Line))
    (hcard : 1 < A.insertionCutSet.card)
    (hbij : Function.Bijective (A.insertionGapToCrossedFace hcard)) :
    A.insertionCrossedFaces.card = A.insertionCutSet.card := by
  classical
  have hcrossedType :
      Fintype.card {F : A.deleteNone.ArrangementFace //
          A.insertionCrossedFace F} = A.insertionCrossedFaces.card := by
    simpa [insertionCrossedFaces] using
      Fintype.card_coe A.insertionCrossedFaces
  have hgapType := A.card_insertionCircularGapSlot_eq_card_insertionCutSet
  have hcardEq := Fintype.card_congr (Equiv.ofBijective _ hbij)
  omega

/-- Nondegenerate insertion endpoint: once the concrete gap map above is
bijective, the exact face recurrence follows. -/
theorem card_arrangementFace_eq_deleteNone_add_card_insertionCutSet_of_gap_bijective
    (A : FiniteProjectiveLineArrangement (Option Line)) (base : Line)
    (hcard : 1 < A.insertionCutSet.card)
    (hbij : Function.Bijective (A.insertionGapToCrossedFace hcard)) :
    Fintype.card A.ArrangementFace =
      Fintype.card A.deleteNone.ArrangementFace +
        A.insertionCutSet.card := by
  apply A.card_arrangementFace_eq_deleteNone_add_card_insertionCutSet_of_crossed
    base
  exact A.card_insertionCrossedFaces_eq_card_insertionCutSet_of_gap_bijective
    hcard hbij

/-- Nondegenerate face insertion, reduced to the two precise
one-dimensional facts still missing from the cyclic-line API. -/
theorem card_arrangementFace_eq_deleteNone_add_card_insertionCutSet_of_coverage_of_separation
    (A : FiniteProjectiveLineArrangement (Option Line))
    (base : Line) (hcard : 1 < A.insertionCutSet.card)
    (hcoverage : ∀ q : RealProjectivePoint,
      A.Incident q none →
      (∀ l : Line, ¬ A.Incident q (some l)) →
      ∃ g : A.CircularGapSlot none,
        q ∈ A.geometricEdgeOpenArc (A.insertionGapEdge g))
    (hseparation : ∀ g h : A.CircularGapSlot none,
      Joined (A.insertionGapRegularPoint hcard g)
        (A.insertionGapRegularPoint hcard h) → g = h) :
    Fintype.card A.ArrangementFace =
      Fintype.card A.deleteNone.ArrangementFace + A.insertionCutSet.card := by
  apply A.card_arrangementFace_eq_deleteNone_add_card_insertionCutSet_of_gap_bijective
    base hcard
  exact A.insertionGapToCrossedFace_bijective_of_coverage_of_separation
    base hcard hcoverage hseparation

theorem card_arrangementFace_eq_deleteNone_add_card_insertionCutSet_of_joined_separation
    (A : FiniteProjectiveLineArrangement (Option Line))
    (base : Line) (hcard : 1 < A.insertionCutSet.card)
    (hseparation : ∀ g h : A.CircularGapSlot none,
      Joined (A.insertionGapRegularPoint hcard g)
        (A.insertionGapRegularPoint hcard h) → g = h) :
    Fintype.card A.ArrangementFace =
      Fintype.card A.deleteNone.ArrangementFace + A.insertionCutSet.card := by
  apply A.card_arrangementFace_eq_deleteNone_add_card_insertionCutSet_of_gap_bijective
    base hcard
  exact A.insertionGapToCrossedFace_bijective_of_joined_separation
    base hcard hseparation

/-- Exact face insertion whenever the new line has at least two distinct
cut vertices. -/
theorem card_arrangementFace_eq_deleteNone_add_card_insertionCutSet_of_one_lt
    (A : FiniteProjectiveLineArrangement (Option Line))
    (base : Line) (hcard : 1 < A.insertionCutSet.card) :
    Fintype.card A.ArrangementFace =
      Fintype.card A.deleteNone.ArrangementFace + A.insertionCutSet.card := by
  apply A.card_arrangementFace_eq_deleteNone_add_card_insertionCutSet_of_joined_separation
    base hcard
  intro g h hjoined
  exact A.insertionGap_eq_of_joined_regular hcard g h hjoined

/-- Deleting `none` simply removes its one incidence indicator from every
point multiplicity. -/
theorem multiplicity_eq_deleteNone_add_indicator
    (A : FiniteProjectiveLineArrangement (Option Line))
    (p : RealProjectivePoint) :
    A.multiplicity p = A.deleteNone.multiplicity p +
      (if A.Incident p none then 1 else 0) := by
  classical
  unfold multiplicity
  rw [Finset.card_eq_sum_ones, Finset.sum_filter,
    Finset.card_eq_sum_ones, Finset.sum_filter]
  change (∑ l : Option Line, if A.Incident p l then 1 else 0) =
    (∑ l : Line, if A.Incident p (some l) then 1 else 0) +
      (if A.Incident p none then 1 else 0)
  rw [Fintype.sum_option]
  omega

/-- Every old vertex remains an actual vertex after inserting `none`. -/
theorem deleteNone_vertexSet_subset_vertexSet
    (A : FiniteProjectiveLineArrangement (Option Line)) :
    (↑A.deleteNone.vertexSet : Set RealProjectivePoint) ⊆
      (↑A.vertexSet : Set RealProjectivePoint) := by
  intro p hp
  have htwoOld : 2 ≤ A.deleteNone.multiplicity p :=
    (A.deleteNone.mem_vertexSet_iff_two_le_multiplicity p).mp hp
  have hmult := A.multiplicity_eq_deleteNone_add_indicator p
  apply (A.mem_vertexSet_iff_two_le_multiplicity p).mpr
  omega

/-- The full vertex set is the union of the old vertices and the distinct
cut points of the inserted line. -/
theorem vertexSet_eq_deleteNone_union_insertionCutSet
    (A : FiniteProjectiveLineArrangement (Option Line)) :
    A.vertexSet = A.deleteNone.vertexSet ∪ A.insertionCutSet := by
  classical
  ext p
  constructor
  · intro hp
    by_cases hpOld : p ∈ A.deleteNone.vertexSet
    · exact Finset.mem_union_left _ hpOld
    · have hmultOld : A.deleteNone.multiplicity p ≤ 1 := by
        by_contra hnot
        apply hpOld
        apply (A.deleteNone.mem_vertexSet_iff_two_le_multiplicity p).mpr
        omega
      have hmult := A.multiplicity_eq_deleteNone_add_indicator p
      have htwo := (A.mem_vertexSet_iff_two_le_multiplicity p).mp hp
      have hpNone : A.Incident p none := by
        by_contra hnot
        simp [hnot] at hmult
        omega
      apply Finset.mem_union_right
      rw [insertionCutSet, A.mem_lineVertexSet]
      exact ⟨hp, hpNone⟩
  · intro hp
    rcases Finset.mem_union.mp hp with hpOld | hpCut
    · exact A.deleteNone_vertexSet_subset_vertexSet hpOld
    · have hpCut' : p ∈ A.lineVertexSet none := by
        simpa [insertionCutSet] using hpCut
      exact ((A.mem_lineVertexSet none).mp hpCut').1

/-- The algebraic deletion--restriction recurrence for vertex excess.  Each
distinct cut point contributes exactly one: an old vertex on the new line
has its multiplicity raised by one, while a genuinely new vertex has
multiplicity two. -/
theorem arrangementVertexExcess_eq_deleteNone_add_card_insertionCutSet
    (A : FiniteProjectiveLineArrangement (Option Line)) :
    A.arrangementVertexExcess =
      A.deleteNone.arrangementVertexExcess + A.insertionCutSet.card := by
  classical
  have hfilter :
      A.deleteNone.vertexSet.filter (fun p => A.Incident p none) =
        A.deleteNone.vertexSet ∩ A.insertionCutSet := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_inter]
    constructor
    · rintro ⟨hpOld, hpNone⟩
      refine ⟨hpOld, ?_⟩
      rw [insertionCutSet, A.mem_lineVertexSet]
      exact ⟨A.deleteNone_vertexSet_subset_vertexSet hpOld, hpNone⟩
    · rintro ⟨hpOld, hpCut⟩
      refine ⟨hpOld, ?_⟩
      have hpCut' : p ∈ A.lineVertexSet none := by
        simpa [insertionCutSet] using hpCut
      exact ((A.mem_lineVertexSet none).mp hpCut').2
  have hindicator :
      (∑ p ∈ A.deleteNone.vertexSet,
          if A.Incident p none then 1 else 0) =
        (A.deleteNone.vertexSet ∩ A.insertionCutSet).card := by
    rw [← Finset.sum_filter, hfilter]
    simp
  have hOldSum :
      (∑ p ∈ A.deleteNone.vertexSet, (A.multiplicity p - 1)) =
        (∑ p ∈ A.deleteNone.vertexSet,
            (A.deleteNone.multiplicity p - 1)) +
          (A.deleteNone.vertexSet ∩ A.insertionCutSet).card := by
    calc
      (∑ p ∈ A.deleteNone.vertexSet, (A.multiplicity p - 1)) =
          ∑ p ∈ A.deleteNone.vertexSet,
            ((A.deleteNone.multiplicity p - 1) +
              (if A.Incident p none then 1 else 0)) := by
        apply Finset.sum_congr rfl
        intro p hp
        have htwoOld :=
          (A.deleteNone.mem_vertexSet_iff_two_le_multiplicity p).mp hp
        have hmult := A.multiplicity_eq_deleteNone_add_indicator p
        by_cases hpNone : A.Incident p none
        · simp [hpNone] at hmult ⊢
          omega
        · simp [hpNone] at hmult ⊢
          omega
      _ = (∑ p ∈ A.deleteNone.vertexSet,
              (A.deleteNone.multiplicity p - 1)) +
            (∑ p ∈ A.deleteNone.vertexSet,
              if A.Incident p none then 1 else 0) := by
        rw [Finset.sum_add_distrib]
      _ = (∑ p ∈ A.deleteNone.vertexSet,
              (A.deleteNone.multiplicity p - 1)) +
            (A.deleteNone.vertexSet ∩ A.insertionCutSet).card := by
        rw [hindicator]
  have hNewSum :
      (∑ p ∈ A.insertionCutSet \ A.deleteNone.vertexSet,
          (A.multiplicity p - 1)) =
        (A.insertionCutSet \ A.deleteNone.vertexSet).card := by
    calc
      (∑ p ∈ A.insertionCutSet \ A.deleteNone.vertexSet,
          (A.multiplicity p - 1)) =
          ∑ _p ∈ A.insertionCutSet \ A.deleteNone.vertexSet, 1 := by
        apply Finset.sum_congr rfl
        intro p hp
        have hpDiff := Finset.mem_sdiff.mp hp
        have hpCut' : p ∈ A.lineVertexSet none := by
          simpa [insertionCutSet] using hpDiff.1
        have hpCutSpec := (A.mem_lineVertexSet none).mp hpCut'
        have hOldLe : A.deleteNone.multiplicity p ≤ 1 := by
          by_contra hnot
          apply hpDiff.2
          apply (A.deleteNone.mem_vertexSet_iff_two_le_multiplicity p).mpr
          omega
        have hmult := A.multiplicity_eq_deleteNone_add_indicator p
        have htwo := (A.mem_vertexSet_iff_two_le_multiplicity p).mp hpCutSpec.1
        simp [hpCutSpec.2] at hmult
        omega
      _ = (A.insertionCutSet \ A.deleteNone.vertexSet).card := by simp
  have hvertexSplit :
      A.vertexSet = A.deleteNone.vertexSet ∪
        (A.insertionCutSet \ A.deleteNone.vertexSet) := by
    rw [A.vertexSet_eq_deleteNone_union_insertionCutSet]
    ext p
    simp only [Finset.mem_union, Finset.mem_sdiff]
    constructor
    · intro hp
      rcases hp with hpOld | hpCut
      · exact Or.inl hpOld
      · by_cases hpOld : p ∈ A.deleteNone.vertexSet
        · exact Or.inl hpOld
        · exact Or.inr ⟨hpCut, hpOld⟩
    · rintro (hpOld | ⟨hpCut, _⟩)
      · exact Or.inl hpOld
      · exact Or.inr hpCut
  have hdisjoint : Disjoint A.deleteNone.vertexSet
      (A.insertionCutSet \ A.deleteNone.vertexSet) := by
    rw [Finset.disjoint_left]
    intro p hpOld hpDiff
    exact (Finset.mem_sdiff.mp hpDiff).2 hpOld
  have hcutSplit := Finset.card_sdiff_add_card_inter
    A.insertionCutSet A.deleteNone.vertexSet
  have hinterCard :
      (A.deleteNone.vertexSet ∩ A.insertionCutSet).card =
        (A.insertionCutSet ∩ A.deleteNone.vertexSet).card := by
    rw [Finset.inter_comm]
  unfold arrangementVertexExcess
  rw [hvertexSplit, Finset.sum_union hdisjoint, hOldSum, hNewSum]
  omega

/-- The geometric face recurrence is sufficient to transport Euler from the
deleted arrangement to the full arrangement; the required vertex-excess
recurrence has been proved algebraically above. -/
theorem euler_of_deleteNone_of_face_insertion
    (A : FiniteProjectiveLineArrangement (Option Line))
    (hOld :
      Fintype.card {p // p ∈ A.deleteNone.vertexSet} +
            Fintype.card A.deleteNone.ArrangementFace =
          Fintype.card A.deleteNone.GeometricEdge + 1)
    (hface :
      Fintype.card A.ArrangementFace =
        Fintype.card A.deleteNone.ArrangementFace +
          A.insertionCutSet.card) :
    Fintype.card {p // p ∈ A.vertexSet} +
          Fintype.card A.ArrangementFace =
        Fintype.card A.GeometricEdge + 1 := by
  have hOldRegions :
      Fintype.card A.deleteNone.ArrangementFace =
        A.deleteNone.arrangementVertexExcess + 1 :=
    (A.deleteNone.euler_iff_card_arrangementFace_eq_vertexExcess_add_one).mp hOld
  have hvertexExcess :=
    A.arrangementVertexExcess_eq_deleteNone_add_card_insertionCutSet
  apply (A.euler_iff_card_arrangementFace_eq_vertexExcess_add_one).mpr
  omega

/-- A non-pencil contains three lines whose first two meet off the third. -/
theorem exists_nonconcurrent_triple
    (A : FiniteProjectiveLineArrangement Line) (hA : A.NonPencil) :
    ∃ l m k : Line, l ≠ m ∧
      ¬ A.Incident (A.intersection l m) k := by
  have hLine : Nonempty Line := by
    rcases isEmpty_or_nonempty Line with hEmpty | hNonempty
    · letI : IsEmpty Line := hEmpty
      exfalso
      apply hA
      obtain ⟨p, _⟩ := A.arrangementComplement_nonempty
      exact ⟨p, fun l => isEmptyElim l⟩
    · exact hNonempty
  let l : Line := Classical.choice hLine
  obtain ⟨m, hml⟩ := A.exists_ne_line_of_nonPencil hA l
  obtain ⟨k, hk⟩ :=
    A.exists_not_incident_line_of_nonPencil hA (A.intersection l m)
  exact ⟨l, m, k, hml.symm, hk⟩

theorem three_le_card_of_nonPencil
    (A : FiniteProjectiveLineArrangement Line) (hA : A.NonPencil) :
    3 ≤ Fintype.card Line := by
  classical
  obtain ⟨l, m, k, hlm, hk⟩ := A.exists_nonconcurrent_triple hA
  have hkl : k ≠ l := by
    intro h
    subst k
    exact hk (A.intersection_incident_left hlm)
  have hkm : k ≠ m := by
    intro h
    subst k
    exact hk (A.intersection_incident_right hlm)
  calc
    3 = ({l, m, k} : Finset Line).card := by
      simp [hlm, hkl, hkm, hkl.symm, hkm.symm]
    _ ≤ Fintype.card Line := by
      simpa using Finset.card_le_card (Finset.subset_univ {l, m, k})

/-- One nondegenerate deletion step, expressed on an arbitrary finite index
type via `Equiv.optionSubtypeNe`. -/
theorem regionCount_of_eraseLine
    (A : FiniteProjectiveLineArrangement Line) (hA : A.NonPencil)
    (r : Line) (base : {l : Line // l ≠ r})
    (hOld : Fintype.card (A.eraseLine r).ArrangementFace =
      (A.eraseLine r).arrangementVertexExcess + 1) :
    Fintype.card A.ArrangementFace = A.arrangementVertexExcess + 1 := by
  let e := Equiv.optionSubtypeNe r
  let B := A.reindex e
  have hB : B.NonPencil := A.reindex_nonPencil e hA
  have hcut : 1 < B.insertionCutSet.card := by
    rw [← B.card_insertionCircularGapSlot_eq_card_insertionCutSet]
    exact B.one_lt_card_circularGapSlot_of_nonPencil hB none
  have hface :=
    B.card_arrangementFace_eq_deleteNone_add_card_insertionCutSet_of_one_lt
      base hcut
  have hexcess :=
    B.arrangementVertexExcess_eq_deleteNone_add_card_insertionCutSet
  have hOld' : Fintype.card B.deleteNone.ArrangementFace =
      B.deleteNone.arrangementVertexExcess + 1 := by
    simpa only [B, e, eraseLine] using hOld
  have hregionB : Fintype.card B.ArrangementFace =
      B.arrangementVertexExcess + 1 := by
    omega
  exact A.regionCount_of_reindex e hregionB

/-- A retained nonconcurrent triple certifies that deleting any other index
leaves a non-pencil. -/
theorem eraseLine_nonPencil_of_nonconcurrent_triple
    (A : FiniteProjectiveLineArrangement Line)
    {l m k r : Line} (hlm : l ≠ m)
    (hk : ¬ A.Incident (A.intersection l m) k)
    (hlr : l ≠ r) (hmr : m ≠ r) (hkr : k ≠ r) :
    (A.eraseLine r).NonPencil := by
  intro hPencil
  rcases hPencil with ⟨p, hp⟩
  have hpl : A.Incident p l := by
    simpa using hp ⟨l, hlr⟩
  have hpm : A.Incident p m := by
    simpa using hp ⟨m, hmr⟩
  have hpk : A.Incident p k := by
    simpa using hp ⟨k, hkr⟩
  have hpEq : p = A.intersection l m :=
    A.eq_intersection_of_incident hlm hpl hpm
  exact hk (hpEq ▸ hpk)

/-- Strong-cardinality induction for the projective region count.  The
two-line arrangement is the base.  Above it we retain a nonconcurrent triple,
so every recursive insertion has at least two cut vertices. -/
theorem regionCount_of_nonPencil_aux (n : ℕ) :
    ∀ {Line : Type u} [Fintype Line] [DecidableEq Line]
      (A : FiniteProjectiveLineArrangement Line),
      Fintype.card Line = n → A.NonPencil →
        Fintype.card A.ArrangementFace = A.arrangementVertexExcess + 1 := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      intro Line _ _ A hcard hA
      classical
      have hnthree : 3 ≤ n := by
        rw [← hcard]
        exact A.three_le_card_of_nonPencil hA
      obtain ⟨l, m, k, hlm, hk⟩ := A.exists_nonconcurrent_triple hA
      have hkl : k ≠ l := by
        intro h
        subst k
        exact hk (A.intersection_incident_left hlm)
      have hkm : k ≠ m := by
        intro h
        subst k
        exact hk (A.intersection_incident_right hlm)
      by_cases hn : n = 3
      · have hcardErase : Fintype.card {x : Line // x ≠ k} = 2 := by
          have he := Fintype.card_congr (Equiv.optionSubtypeNe k)
          have he' : Fintype.card {x : Line // x ≠ k} + 1 = n := by
            simpa [hcard] using he
          omega
        apply A.regionCount_of_eraseLine hA k ⟨l, hkl.symm⟩
        exact (A.eraseLine k).regionCount_of_card_eq_two hcardErase
      · have hnlt : 3 < n := by omega
        have htripleCard : ({l, m, k} : Finset Line).card = 3 := by
          simp [hlm, hkl, hkm, hkl.symm, hkm.symm]
        have hsmall : ({l, m, k} : Finset Line).card <
            (Finset.univ : Finset Line).card := by
          rw [htripleCard]
          simpa [hcard] using hnlt
        obtain ⟨r, _hrUniv, hr⟩ :=
          Finset.exists_mem_notMem_of_card_lt_card hsmall
        have hlr : l ≠ r := by
          intro h
          subst r
          exact hr (by simp)
        have hmr : m ≠ r := by
          intro h
          subst r
          exact hr (by simp)
        have hkr : k ≠ r := by
          intro h
          subst r
          exact hr (by simp)
        have hOldNonPencil : (A.eraseLine r).NonPencil :=
          A.eraseLine_nonPencil_of_nonconcurrent_triple
            hlm hk hlr hmr hkr
        have hcardErase : Fintype.card {x : Line // x ≠ r} + 1 = n := by
          have he := Fintype.card_congr (Equiv.optionSubtypeNe r)
          simpa [hcard] using he
        have hcardEraseLt : Fintype.card {x : Line // x ≠ r} < n := by
          omega
        apply A.regionCount_of_eraseLine hA r ⟨l, hlr⟩
        exact ih (Fintype.card {x : Line // x ≠ r}) hcardEraseLt
          (A.eraseLine r) rfl hOldNonPencil

theorem regionCount_of_nonPencil
    (A : FiniteProjectiveLineArrangement Line) (hA : A.NonPencil) :
    Fintype.card A.ArrangementFace = A.arrangementVertexExcess + 1 :=
  regionCount_of_nonPencil_aux (Fintype.card Line) A rfl hA

theorem euler_of_nonPencil
    (A : FiniteProjectiveLineArrangement Line) (hA : A.NonPencil) :
    Fintype.card {p // p ∈ A.vertexSet} +
          Fintype.card A.ArrangementFace =
        Fintype.card A.GeometricEdge + 1 :=
  (A.euler_iff_card_arrangementFace_eq_vertexExcess_add_one).mpr
    (A.regionCount_of_nonPencil hA)

/-! ## Specialization and the global-input handoff -/

/-- Exact Euler reduction for the labelled dual arrangement used by the
configuration development. -/
theorem labelDualArrangement_euler_iff_regionCount
    {alpha : Type u} [Fintype alpha] [DecidableEq alpha]
    (cfg : Configuration alpha) :
    (Fintype.card
          {p // p ∈ (labelDualArrangement cfg).vertexSet} +
            Fintype.card (labelDualArrangement cfg).ArrangementFace =
        Fintype.card (labelDualArrangement cfg).GeometricEdge + 1) ↔
      Fintype.card (labelDualArrangement cfg).ArrangementFace =
        (labelDualArrangement cfg).arrangementVertexExcess + 1 :=
  (labelDualArrangement cfg).euler_iff_card_arrangementFace_eq_vertexExcess_add_one

/-- One-way labelled-dual endpoint for a deletion--restriction or
sign-pattern region-count proof. -/
theorem labelDualArrangement_euler_of_regionCount
    {alpha : Type u} [Fintype alpha] [DecidableEq alpha]
    (cfg : Configuration alpha)
    (hregion :
      Fintype.card (labelDualArrangement cfg).ArrangementFace =
        (labelDualArrangement cfg).arrangementVertexExcess + 1) :
    Fintype.card
          {p // p ∈ (labelDualArrangement cfg).vertexSet} +
            Fintype.card (labelDualArrangement cfg).ArrangementFace =
        Fintype.card (labelDualArrangement cfg).GeometricEdge + 1 :=
  (labelDualArrangement_euler_iff_regionCount cfg).mpr hregion

/-- The same labelled-dual reduction expressed only through realized strict
sign patterns. -/
theorem labelDualArrangement_euler_iff_realizedSignPatternCount
    {alpha : Type u} [Fintype alpha] [DecidableEq alpha]
    (cfg : Configuration alpha) (base : alpha) :
    (Fintype.card
          {p // p ∈ (labelDualArrangement cfg).vertexSet} +
            Fintype.card (labelDualArrangement cfg).ArrangementFace =
        Fintype.card (labelDualArrangement cfg).GeometricEdge + 1) ↔
      Fintype.card
          ((labelDualArrangement cfg).RealizedArrangementSignPattern base) =
        (labelDualArrangement cfg).arrangementVertexExcess + 1 :=
  euler_iff_card_realizedArrangementSignPattern_eq_vertexExcess_add_one
    (labelDualArrangement cfg) base

/-- Assemble the existing global input from the exact Zaslavsky region-count
statement and the independent three-boundary-edge theorem.  This constructor
contains no hidden Euler assumption: its first argument is precisely the
realized-region count isolated above. -/
noncomputable def realProjectiveArrangementGlobalInputOfRegionCount
    (hregion :
      ∀ {Line : Type u} [Fintype Line] [DecidableEq Line]
        (A : FiniteProjectiveLineArrangement Line), A.NonPencil →
          Fintype.card A.ArrangementFace =
            A.arrangementVertexExcess + 1)
    (hthree :
      ∀ {Line : Type u} [Fintype Line] [DecidableEq Line]
        (A : FiniteProjectiveLineArrangement Line), A.NonPencil →
          ∀ F : A.ArrangementFace,
            3 ≤ (A.arrangementFaceBoundary F).card) :
    RealProjectiveArrangementGlobalInput.{u} where
  euler := by
    intro Line _hFintype _hDecidableEq A hA
    exact
      (A.euler_iff_card_arrangementFace_eq_vertexExcess_add_one).mpr
        (hregion A hA)
  faceHasThreeEdges := hthree

/-- Equivalent handoff whose first input is stated directly for the realized
strict sign patterns already constructed by the topology module. -/
noncomputable def realProjectiveArrangementGlobalInputOfRealizedSignPatternCount
    (hpattern :
      ∀ {Line : Type u} [Fintype Line] [DecidableEq Line]
        (A : FiniteProjectiveLineArrangement Line), A.NonPencil →
          ∀ base : Line,
            Fintype.card (A.RealizedArrangementSignPattern base) =
              A.arrangementVertexExcess + 1)
    (hthree :
      ∀ {Line : Type u} [Fintype Line] [DecidableEq Line]
        (A : FiniteProjectiveLineArrangement Line), A.NonPencil →
          ∀ F : A.ArrangementFace,
            3 ≤ (A.arrangementFaceBoundary F).card) :
    RealProjectiveArrangementGlobalInput.{u} := by
  apply realProjectiveArrangementGlobalInputOfRegionCount
  · intro Line _hFintype _hDecidableEq A hA
    have hLine : Nonempty Line := by
      rcases isEmpty_or_nonempty Line with hEmpty | hNonempty
      · letI : IsEmpty Line := hEmpty
        exfalso
        apply hA
        obtain ⟨p, _hp⟩ := A.arrangementComplement_nonempty
        exact ⟨p, fun l => isEmptyElim l⟩
      · exact hNonempty
    let base : Line := Classical.choice hLine
    rw [A.card_arrangementFace_eq_card_realizedArrangementSignPattern base]
    exact hpattern A hA base
  · exact hthree

/-- The unconditional global input: Euler is the insertion induction above,
and the three-edge field is the independent facet theorem. -/
noncomputable def realProjectiveArrangementGlobalInput :
    RealProjectiveArrangementGlobalInput.{u} := by
  apply realProjectiveArrangementGlobalInputOfRegionCount
  · intro Line _ _ A hA
    exact A.regionCount_of_nonPencil hA
  · intro Line _ _ A hA F
    obtain ⟨base, _m, _k, _hbm, _hk⟩ :=
      A.exists_nonconcurrent_triple hA
    exact A.three_le_arrangementFaceBoundary_card hA base F

end FiniteProjectiveLineArrangement

end Erdos506.Incidence
