import Erdos506.Incidence.RealProjectiveArrangementFaceThreeFinish

/-!
# Minimal half-space data for real projective arrangement faces

This file isolates the finite-dimensional part of the three-side argument.
For a realized face sign word, choose a smallest subfamily of the oriented
weak inequalities which still defines the full closed sign cone.  Pointedness
of that cone forces the subfamily to contain at least three inequalities.
Moreover, deleting any member of a smallest subfamily produces a vector which
satisfies all remaining inequalities and strictly violates the deleted one.

The final theorem is an honest hand-off to the geometric part: if the active
inequalities are realized by distinct literal geometric open arcs in the
closure of the face, then the face boundary has cardinality at least three.
No facet-to-arc realization is assumed implicitly.
-/

namespace Erdos506.Incidence

open scoped Convex LinearAlgebra.Projectivization

universe u

namespace FiniteProjectiveLineArrangement

variable {Line : Type u} [Fintype Line] [DecidableEq Line]

noncomputable local instance realProjectivePointTopologicalSpaceForFaceThreeMinimal :
    TopologicalSpace RealProjectivePoint :=
  realProjectivePointQuotientTopology

/-- The geometric edge represented by a particular cyclic gap on `l`. -/
noncomputable def circularGapEdge
    (A : FiniteProjectiveLineArrangement Line) (l : Line)
    (g : A.CircularGapSlot l) : A.GeometricEdge :=
  A.edgeSlotEquivCircularGap.symm ⟨l, g⟩

@[simp]
theorem circularGapEdge_line
    (A : FiniteProjectiveLineArrangement Line) (l : Line)
    (g : A.CircularGapSlot l) :
    A.edgeSlotLine (A.circularGapEdge l g) = l :=
  rfl

/-- Every line of a non-pencil arrangement has at least two marked vertices,
hence at least two cyclic gaps. -/
theorem one_lt_card_circularGapSlot_of_nonPencil
    (A : FiniteProjectiveLineArrangement Line) (hA : A.NonPencil)
    (l : Line) :
    1 < Fintype.card (A.CircularGapSlot l) := by
  classical
  let z : Fin 2 -> ℝ := fun i => if i = 0 then 1 else 0
  have hz : z ≠ 0 := by
    intro hzero
    have hcoord := congrFun hzero (0 : Fin 2)
    norm_num [z] at hcoord
  let P : RealProjectiveOnePoint := Projectivization.mk ℝ z hz
  let p := projectiveLineParameter (A.projectiveLine l) P
  have hpl : A.Incident p l :=
    projectiveLineParameter_incident (A.projectiveLine l) P
  obtain ⟨m, hpm⟩ := A.exists_not_incident_line_of_nonPencil hA p
  have hlm : l ≠ m := by
    intro hlm
    subst m
    exact hpm hpl
  let g0 : A.CircularGapSlot l :=
    ⟨A.intersection l m, A.intersection_mem_lineVertexSet_left hlm⟩
  obtain ⟨n, hgn⟩ :=
    A.exists_not_incident_line_of_nonPencil hA g0.1
  have hln : l ≠ n := by
    intro hln
    subst n
    apply hgn
    exact ((A.mem_lineVertexSet l).mp g0.2).2
  let g1 : A.CircularGapSlot l :=
    ⟨A.intersection l n, A.intersection_mem_lineVertexSet_left hln⟩
  have hg01 : g0 ≠ g1 := by
    intro heq
    apply hgn
    have hpoints := congrArg Subtype.val heq
    change A.intersection l m = A.intersection l n at hpoints
    change A.Incident (A.intersection l m) n
    rw [hpoints]
    exact A.intersection_incident_right hln
  exact Fintype.one_lt_card_iff.mpr ⟨g0, g1, hg01⟩

/-- Every regular point of an indexed line belongs to exactly one literal
geometric open gap on that line. -/
theorem existsUnique_circularGap_mem_geometricEdgeOpenArc_of_regular
    (A : FiniteProjectiveLineArrangement Line) (hA : A.NonPencil)
    (q : RealProjectivePoint) (l : Line)
    (hregular : ∀ m : Line, A.Incident q m ↔ m = l) :
    ∃! g : A.CircularGapSlot l,
      q ∈ A.geometricEdgeOpenArc (A.circularGapEdge l g) := by
  classical
  have hql : A.Incident q l := (hregular l).mpr rfl
  let Q : RealProjectiveOnePoint :=
    projectiveLineParameterPreimage (A.projectiveLine l) q hql
  have hQmap : projectiveLineParameter (A.projectiveLine l) Q = q :=
    projectiveLineParameter_preimage_spec (A.projectiveLine l) q hql
  have hQne (g : A.CircularGapSlot l) :
      Q ≠ circularGapSlotParameter A l g := by
    intro heq
    have hqg : q = g.1 := by
      calc
        q = projectiveLineParameter (A.projectiveLine l) Q := hQmap.symm
        _ = projectiveLineParameter (A.projectiveLine l)
            (circularGapSlotParameter A l g) := congrArg _ heq
        _ = g.1 := A.projectiveLineParameter_circularGapSlotParameter l g
    have hqVertex : q ∈ A.vertexSet := by
      rw [hqg]
      exact ((A.mem_lineVertexSet l).mp g.2).1
    obtain ⟨a, b, hab, hintersection⟩ :=
      A.exists_lines_of_mem_vertexSet hqVertex
    have hqa : A.Incident q a := by
      rw [← hintersection]
      exact A.intersection_incident_left hab
    have hqb : A.Incident q b := by
      rw [← hintersection]
      exact A.intersection_incident_right hab
    exact hab (((hregular a).mp hqa).trans ((hregular b).mp hqb).symm)
  have hcard : 1 < Fintype.card (A.CircularGapSlot l) :=
    A.one_lt_card_circularGapSlot_of_nonPencil hA l
  obtain ⟨g, hg, hunique⟩ :=
    existsUnique_realProjectiveCyclic_between_projectiveCyclicSuccessor
      (circularGapSlotParameter A l)
      (A.circularGapSlotParameter_injective l) hcard Q hQne
  have hiff (r : A.CircularGapSlot l) :
      q ∈ A.geometricEdgeOpenArc (A.circularGapEdge l r) ↔
        RealProjectiveCyclic
          (circularGapSlotParameter A l r) Q
          (circularGapSlotParameter A l (A.circularGapSuccessor l r)) := by
    change ProjectiveLineCyclic (A.projectiveLine l) r.1 q
      (A.circularGapSuccessor l r).1 ↔ _
    rw [← hQmap,
      ← A.projectiveLineParameter_circularGapSlotParameter l r,
      ← A.projectiveLineParameter_circularGapSlotParameter l
        (A.circularGapSuccessor l r),
      projectiveLineCyclic_parameter_iff]
  refine ⟨g, (hiff g).mpr ?_, ?_⟩
  · simpa only [circularGapSuccessor, circularGapSuccessorEquiv,
      projectiveCyclicSuccessor] using hg
  · intro r hr
    apply hunique r
    have := (hiff r).mp hr
    simpa only [circularGapSuccessor, circularGapSuccessorEquiv,
      projectiveCyclicSuccessor] using this

/-- The regular part of one indexed projective line.  This is the natural
ambient space in which the cyclic open gaps are the connected components. -/
def lineRegularLocus
    (A : FiniteProjectiveLineArrangement Line) (l : Line) :=
  {q : RealProjectivePoint // ∀ m : Line, A.Incident q m ↔ m = l}

noncomputable local instance lineRegularLocusTopologicalSpace
    (A : FiniteProjectiveLineArrangement Line) (l : Line) :
    TopologicalSpace (A.lineRegularLocus l) :=
  TopologicalSpace.induced
    (fun q : A.lineRegularLocus l => q.1)
    realProjectivePointQuotientTopology

/-- The fibre of one cyclic gap in the regular locus of its supporting
line. -/
def circularGapRegularFiber
    (A : FiniteProjectiveLineArrangement Line) (l : Line)
    (g : A.CircularGapSlot l) : Set (A.lineRegularLocus l) :=
  {q | q.1 ∈ A.geometricEdgeOpenArc (A.circularGapEdge l g)}

/-- Pointwise unique cyclic-gap coverage turns relative openness of all gap
fibres into relative clopenness.  Thus the only remaining topological seam
for path-component separation is openness of a cyclic interval in the
punctured projective line. -/
theorem isClopen_circularGapRegularFiber_of_isOpen
    (A : FiniteProjectiveLineArrangement Line) (hA : A.NonPencil)
    (l : Line)
    (hopen : ∀ g : A.CircularGapSlot l,
      IsOpen (A.circularGapRegularFiber l g))
    (g : A.CircularGapSlot l) :
    IsClopen (A.circularGapRegularFiber l g) := by
  have hcompl : (A.circularGapRegularFiber l g)ᶜ =
      ⋃ h : {h : A.CircularGapSlot l // h ≠ g},
        A.circularGapRegularFiber l h.1 := by
    ext q
    constructor
    · intro hq
      obtain ⟨h, hqh, _⟩ :=
        A.existsUnique_circularGap_mem_geometricEdgeOpenArc_of_regular
          hA q.1 l q.2
      have hhg : h ≠ g := by
        intro heq
        subst h
        exact hq hqh
      exact Set.mem_iUnion.mpr ⟨⟨h, hhg⟩, hqh⟩
    · intro hq hqg
      rcases Set.mem_iUnion.mp hq with ⟨h, hqh⟩
      obtain ⟨k, hk, hunique⟩ :=
        A.existsUnique_circularGap_mem_geometricEdgeOpenArc_of_regular
          hA q.1 l q.2
      apply h.2
      exact (hunique h.1 hqh).trans (hunique g hqg).symm
  constructor
  · rw [← isOpen_compl_iff, hcompl]
    exact isOpen_iUnion fun h => hopen h.1
  · exact hopen g

/-- General path-separation router for cyclic gaps.  The explicit openness
hypothesis isolates the sole missing topology lemma; coverage and uniqueness
are supplied by the arrangement API above. -/
theorem circularGap_eq_of_joined_regular_of_isOpen
    (A : FiniteProjectiveLineArrangement Line) (hA : A.NonPencil)
    (l : Line)
    (hopen : ∀ g : A.CircularGapSlot l,
      IsOpen (A.circularGapRegularFiber l g))
    (q r : A.lineRegularLocus l) (g h : A.CircularGapSlot l)
    (hq : q ∈ A.circularGapRegularFiber l g)
    (hr : r ∈ A.circularGapRegularFiber l h)
    (hjoined : Joined q r) :
    g = h := by
  have hclopen : IsClopen (A.circularGapRegularFiber l g) :=
    A.isClopen_circularGapRegularFiber_of_isOpen hA l hopen g
  have hpathConnected : IsPreconnected (Set.range hjoined.somePath) :=
    isPreconnected_range hjoined.somePath.continuous
  have hmeet :
      (Set.range hjoined.somePath ∩ A.circularGapRegularFiber l g).Nonempty := by
    refine ⟨q, ⟨⟨0, by simp⟩, hq⟩⟩
  have hpathSubset :
      Set.range hjoined.somePath ⊆ A.circularGapRegularFiber l g :=
    hpathConnected.subset_isClopen hclopen hmeet
  have hrg : r ∈ A.circularGapRegularFiber l g :=
    hpathSubset ⟨1, by simp⟩
  obtain ⟨k, hk, hunique⟩ :=
    A.existsUnique_circularGap_mem_geometricEdgeOpenArc_of_regular
      hA r.1 l r.2
  exact (hunique g hrg).trans (hunique h hr).symm

/-- The evaluation defining the `l`-th half-space, oriented so that the
closed sign cone is always given by a nonnegative inequality. -/
noncomputable def arrangementOrientedEvaluation
    (A : FiniteProjectiveLineArrangement Line) (sigma : Line -> Bool)
    (l : Line) : (Fin 3 -> ℝ) →ₗ[ℝ] ℝ :=
  if sigma l then
    projectiveLineEvaluation (A.projectiveLine l)
  else
    -(projectiveLineEvaluation (A.projectiveLine l))

/-- Incidence of a projectivized vector is exactly vanishing of any chosen
orientation of the corresponding line covector. -/
theorem incident_projectivization_mk_iff_orientedEvaluation_eq_zero
    (A : FiniteProjectiveLineArrangement Line) (sigma : Line -> Bool)
    (l : Line) (q : Fin 3 -> ℝ) (hq0 : q ≠ 0) :
    A.Incident (Projectivization.mk ℝ q hq0) l ↔
      A.arrangementOrientedEvaluation sigma l q = 0 := by
  change (Projectivization.mk ℝ q hq0).orthogonal (A.projectiveLine l) ↔ _
  rw [← (A.projectiveLine l).mk_rep, Projectivization.orthogonal_mk]
  by_cases hs : sigma l <;>
    simp [arrangementOrientedEvaluation, projectiveLineEvaluation, hs]

/-- Proportional evaluation covectors define the same projective line. -/
theorem projectiveLine_eq_of_evaluation_eq_smul
    (L M : RealProjectiveLine) (a : ℝ)
    (h : projectiveLineEvaluation M = a • projectiveLineEvaluation L) :
    M = L := by
  have hrep : M.rep = a • L.rep := by
    funext i
    have hi := LinearMap.congr_fun h (Pi.single i 1)
    simpa [projectiveLineEvaluation, single_one_dotProduct,
      smul_eq_mul] using hi
  calc
    M = Projectivization.mk ℝ M.rep M.rep_nonzero :=
      (Projectivization.mk_rep M).symm
    _ = Projectivization.mk ℝ L.rep L.rep_nonzero :=
      (Projectivization.mk_eq_mk_iff' ℝ M.rep L.rep
        M.rep_nonzero L.rep_nonzero).mpr ⟨a, hrep.symm⟩
    _ = L := Projectivization.mk_rep L

/-- Proportional oriented covectors can occur only for the same indexed
arrangement line. -/
theorem eq_of_orientedEvaluation_eq_smul
    (A : FiniteProjectiveLineArrangement Line) (sigma : Line -> Bool)
    {l m : Line} (a : ℝ)
    (h : A.arrangementOrientedEvaluation sigma m =
      a • A.arrangementOrientedEvaluation sigma l) :
    m = l := by
  apply A.projectiveLine_injective
  by_cases hl : sigma l
  · by_cases hm : sigma m
    · exact projectiveLine_eq_of_evaluation_eq_smul _ _ a (by
        simpa [arrangementOrientedEvaluation, hl, hm] using h)
    · exact projectiveLine_eq_of_evaluation_eq_smul _ _ (-a) (by
        have hn := congrArg Neg.neg h
        calc
          projectiveLineEvaluation (A.projectiveLine m) =
              -(a • projectiveLineEvaluation (A.projectiveLine l)) := by
            simpa [arrangementOrientedEvaluation, hl, hm] using hn
          _ = (-a) • projectiveLineEvaluation (A.projectiveLine l) :=
            (neg_smul a _).symm)
  · by_cases hm : sigma m
    · exact projectiveLine_eq_of_evaluation_eq_smul _ _ (-a) (by
        calc
          projectiveLineEvaluation (A.projectiveLine m) =
              -(a • projectiveLineEvaluation (A.projectiveLine l)) := by
            simpa [arrangementOrientedEvaluation, hl, hm] using h
          _ = (-a) • projectiveLineEvaluation (A.projectiveLine l) :=
            (neg_smul a _).symm)
    · exact projectiveLine_eq_of_evaluation_eq_smul _ _ a (by
        simpa [arrangementOrientedEvaluation, hl, hm, smul_neg] using h)

/-- Two distinct arrangement covectors remain independent after restricting
the second one to the kernel of the first. -/
theorem exists_orientedEvaluation_ne_zero_on_kernel_of_ne
    (A : FiniteProjectiveLineArrangement Line) (sigma : Line -> Bool)
    {l m : Line} (hlm : l ≠ m) :
    ∃ w : Fin 3 -> ℝ,
      A.arrangementOrientedEvaluation sigma l w = 0 ∧
        A.arrangementOrientedEvaluation sigma m w ≠ 0 := by
  classical
  let fl := A.arrangementOrientedEvaluation sigma l
  let fm := A.arrangementOrientedEvaluation sigma m
  by_contra hex
  have hker : LinearMap.ker fl ≤ LinearMap.ker fm := by
    intro w hw
    change fl w = 0 at hw
    change fm w = 0
    by_contra hmw
    apply hex
    exact ⟨w, hw, hmw⟩
  let forms : Unit -> (Fin 3 -> ℝ) →ₗ[ℝ] ℝ := fun _ => fl
  have hiInf : (⨅ i : Unit, LinearMap.ker (forms i)) ≤
      LinearMap.ker fm := by
    simpa [forms] using hker
  have hspan : fm ∈ Submodule.span ℝ ({fl} : Set ((Fin 3 -> ℝ) →ₗ[ℝ] ℝ)) := by
    simpa [forms] using
      (mem_span_of_iInf_ker_le_ker (L := forms) (K := fm) hiInf)
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hspan
  have hml : m = l := A.eq_of_orientedEvaluation_eq_smul sigma a (by
    simpa only [fl, fm] using ha.symm)
  exact hlm hml.symm

/-- The preceding kernel witness can be oriented to point strictly against
the `m`-th half-space. -/
theorem exists_orientedEvaluation_neg_on_kernel_of_ne
    (A : FiniteProjectiveLineArrangement Line) (sigma : Line -> Bool)
    {l m : Line} (hlm : l ≠ m) :
    ∃ w : Fin 3 -> ℝ,
      A.arrangementOrientedEvaluation sigma l w = 0 ∧
        A.arrangementOrientedEvaluation sigma m w < 0 := by
  obtain ⟨w, hlw, hmw⟩ :=
    A.exists_orientedEvaluation_ne_zero_on_kernel_of_ne sigma hlm
  rcases lt_or_gt_of_ne hmw with hneg | hpos
  · exact ⟨w, hlw, hneg⟩
  · refine ⟨-w, ?_, ?_⟩
    · rw [LinearMap.map_neg, hlw, neg_zero]
    · rw [LinearMap.map_neg]
      exact neg_neg_of_pos hpos

/-- The weak cone cut out by only the inequalities indexed by `K`. -/
def arrangementClosedSignConeOn
    (A : FiniteProjectiveLineArrangement Line) (sigma : Line -> Bool)
    (K : Finset Line) : Set (Fin 3 -> ℝ) :=
  {v | ∀ l ∈ K, 0 ≤ A.arrangementOrientedEvaluation sigma l v}

/-- The strict inequalities indexed by a finite subfamily. -/
def arrangementSignConeOn
    (A : FiniteProjectiveLineArrangement Line) (sigma : Line -> Bool)
    (K : Finset Line) : Set (Fin 3 -> ℝ) :=
  {v | ∀ l ∈ K, 0 < A.arrangementOrientedEvaluation sigma l v}

@[simp]
theorem mem_arrangementSignConeOn
    (A : FiniteProjectiveLineArrangement Line) (sigma : Line -> Bool)
    (K : Finset Line) (v : Fin 3 -> ℝ) :
    v ∈ A.arrangementSignConeOn sigma K ↔
      ∀ l ∈ K, 0 < A.arrangementOrientedEvaluation sigma l v :=
  Iff.rfl

theorem isOpen_arrangementSignConeOn
    (A : FiniteProjectiveLineArrangement Line) (sigma : Line -> Bool)
    (K : Finset Line) :
    IsOpen (A.arrangementSignConeOn sigma K) := by
  have heq : A.arrangementSignConeOn sigma K =
      ⋂ l ∈ K, {v | 0 < A.arrangementOrientedEvaluation sigma l v} := by
    ext v
    simp [arrangementSignConeOn]
  rw [heq]
  apply isOpen_biInter_finset
  intro l _hl
  exact isOpen_lt continuous_const
    (A.arrangementOrientedEvaluation sigma l).continuous_of_finiteDimensional

@[simp]
theorem mem_arrangementClosedSignConeOn
    (A : FiniteProjectiveLineArrangement Line) (sigma : Line -> Bool)
    (K : Finset Line) (v : Fin 3 -> ℝ) :
    v ∈ A.arrangementClosedSignConeOn sigma K ↔
      ∀ l ∈ K, 0 ≤ A.arrangementOrientedEvaluation sigma l v :=
  Iff.rfl

/-- Strict sign-cone membership expressed uniformly with the oriented
evaluations. -/
theorem mem_arrangementSignCone_iff_orientedEvaluation_pos
    (A : FiniteProjectiveLineArrangement Line) (sigma : Line -> Bool)
    (v : Fin 3 -> ℝ) :
    v ∈ A.arrangementSignCone sigma ↔
      ∀ l, 0 < A.arrangementOrientedEvaluation sigma l v := by
  simp only [arrangementSignCone, Set.mem_iInter]
  constructor <;> intro hv l
  · specialize hv l
    by_cases hs : sigma l <;>
      simpa [arrangementOrientedEvaluation, hs] using hv
  · specialize hv l
    by_cases hs : sigma l <;>
      simpa [arrangementOrientedEvaluation, hs] using hv

/-- Closed sign-cone membership expressed uniformly with the oriented
evaluations. -/
theorem mem_arrangementClosedSignCone_iff_orientedEvaluation_nonneg
    (A : FiniteProjectiveLineArrangement Line) (sigma : Line -> Bool)
    (v : Fin 3 -> ℝ) :
    v ∈ A.arrangementClosedSignCone sigma ↔
      ∀ l, 0 ≤ A.arrangementOrientedEvaluation sigma l v := by
  simp only [arrangementClosedSignCone, Set.mem_iInter]
  constructor <;> intro hv l
  · specialize hv l
    by_cases hs : sigma l <;>
      simpa [arrangementOrientedEvaluation, hs] using hv
  · specialize hv l
    by_cases hs : sigma l <;>
      simpa [arrangementOrientedEvaluation, hs] using hv

/-- Restricting the index set weakens the system of inequalities. -/
theorem arrangementClosedSignConeOn_mono
    (A : FiniteProjectiveLineArrangement Line) (sigma : Line -> Bool)
    {K L : Finset Line} (hKL : K ⊆ L) :
    A.arrangementClosedSignConeOn sigma L ⊆
      A.arrangementClosedSignConeOn sigma K := by
  intro v hv
  rw [A.mem_arrangementClosedSignConeOn] at hv ⊢
  intro l hl
  exact hv l (hKL hl)

/-- Taking all oriented inequalities recovers the existing closed sign cone. -/
theorem arrangementClosedSignConeOn_univ
    (A : FiniteProjectiveLineArrangement Line) (sigma : Line -> Bool) :
    A.arrangementClosedSignConeOn sigma Finset.univ =
      A.arrangementClosedSignCone sigma := by
  ext v
  simp only [A.mem_arrangementClosedSignConeOn, Finset.mem_univ,
    forall_const, arrangementClosedSignCone, Set.mem_iInter]
  constructor
  · intro hv l
    specialize hv l
    by_cases hs : sigma l
    · simpa [arrangementOrientedEvaluation, hs] using hv
    · simpa [arrangementOrientedEvaluation, hs] using hv
  · intro hv l
    specialize hv l
    by_cases hs : sigma l
    · simpa [arrangementOrientedEvaluation, hs] using hv
    · simpa [arrangementOrientedEvaluation, hs] using hv

/-- Every vector in the strict cone of an actual face projects into that
literal ambient face carrier. -/
theorem arrangementSignConeToComplement_mem_arrangementFaceCarrier
    (A : FiniteProjectiveLineArrangement Line) (base : Line)
    (F : A.ArrangementFace) {v : Fin 3 -> ℝ}
    (hv : v ∈ A.arrangementSignCone
      (A.arrangementFaceSignPattern base F)) :
    (A.arrangementSignConeToComplement base
      (A.arrangementFaceSignPattern base F) ⟨v, hv⟩).1 ∈
        A.arrangementFaceCarrier F := by
  let p := A.arrangementSignConeToComplement base
    (A.arrangementFaceSignPattern base F) ⟨v, hv⟩
  let r := A.arrangementFaceRepresentative F
  have hr : A.arrangementNormalizedRepresentative base r ∈
      A.arrangementSignCone (A.arrangementFaceSignPattern base F) := by
    exact A.arrangementNormalizedRepresentative_mem_arrangementSignCone base r
  have hconnected : IsPathConnected
      (A.arrangementSignCone (A.arrangementFaceSignPattern base F)) :=
    (A.convex_arrangementSignCone _).isPathConnected ⟨v, hv⟩
  have hjoinedCone : Joined
      (⟨v, hv⟩ : {w // w ∈ A.arrangementSignCone
        (A.arrangementFaceSignPattern base F)})
      ⟨A.arrangementNormalizedRepresentative base r, hr⟩ :=
    (hconnected.joinedIn v hv
      (A.arrangementNormalizedRepresentative base r) hr).joined_subtype
  have hjoined : Joined p r := by
    refine ⟨(hjoinedCone.somePath.map
      (A.continuous_arrangementSignConeToComplement base
        (A.arrangementFaceSignPattern base F))).cast rfl ?_⟩
    exact (A.arrangementSignConeToComplement_normalizedRepresentative base r).symm
  have hface : A.arrangementFaceOf p = F := by
    calc
      A.arrangementFaceOf p = A.arrangementFaceOf r :=
        (A.arrangementFaceOf_eq_iff_joined p r).mpr hjoined
      _ = F := A.arrangementFaceRepresentative_faceOf F
  simpa only [hface] using A.mem_arrangementFaceCarrier_faceOf p

/-- A quadratic ray from a closed-cone vector towards a strict-cone vector.
The square makes the coefficient positive on the punctured real line. -/
def arrangementClosedConeQuadraticRay
    (q u : Fin 3 -> ℝ) (t : ℝ) : Fin 3 -> ℝ :=
  q + t ^ 2 • u

/-- Away from its endpoint, the quadratic ray lies in the strict cone. -/
theorem arrangementClosedConeQuadraticRay_mem_arrangementSignCone
    (A : FiniteProjectiveLineArrangement Line) (sigma : Line -> Bool)
    {q u : Fin 3 -> ℝ}
    (hq : q ∈ A.arrangementClosedSignCone sigma)
    (hu : u ∈ A.arrangementSignCone sigma)
    {t : ℝ} (ht : t ≠ 0) :
    arrangementClosedConeQuadraticRay q u t ∈
      A.arrangementSignCone sigma := by
  rw [A.mem_arrangementSignCone_iff_orientedEvaluation_pos]
  intro l
  have hql :=
    (A.mem_arrangementClosedSignCone_iff_orientedEvaluation_nonneg
      sigma q).mp hq l
  have hul :=
    (A.mem_arrangementSignCone_iff_orientedEvaluation_pos sigma u).mp hu l
  change 0 < A.arrangementOrientedEvaluation sigma l (q + t ^ 2 • u)
  rw [LinearMap.map_add,
    LinearMap.map_smul, smul_eq_mul]
  exact add_pos_of_nonneg_of_pos hql (mul_pos (sq_pos_of_ne_zero ht) hul)

/-- The quadratic ray never reaches the zero vector when its endpoint is
nonzero. -/
theorem arrangementClosedConeQuadraticRay_ne_zero
    (A : FiniteProjectiveLineArrangement Line) (base : Line)
    (sigma : Line -> Bool) {q u : Fin 3 -> ℝ}
    (hq0 : q ≠ 0)
    (hq : q ∈ A.arrangementClosedSignCone sigma)
    (hu : u ∈ A.arrangementSignCone sigma) (t : ℝ) :
    arrangementClosedConeQuadraticRay q u t ≠ 0 := by
  by_cases ht : t = 0
  · subst t
    simpa [arrangementClosedConeQuadraticRay] using hq0
  · exact A.arrangementSignCone_ne_zero base sigma
      (A.arrangementClosedConeQuadraticRay_mem_arrangementSignCone
        sigma hq hu ht)

/-- Projectivization of the quadratic closed-to-strict ray. -/
noncomputable def arrangementClosedConeProjectiveRay
    (A : FiniteProjectiveLineArrangement Line) (base : Line)
    (sigma : Line -> Bool) {q u : Fin 3 -> ℝ}
    (hq0 : q ≠ 0)
    (hq : q ∈ A.arrangementClosedSignCone sigma)
    (hu : u ∈ A.arrangementSignCone sigma) (t : ℝ) :
    RealProjectivePoint :=
  Projectivization.mk ℝ (arrangementClosedConeQuadraticRay q u t)
    (A.arrangementClosedConeQuadraticRay_ne_zero base sigma hq0 hq hu t)

theorem arrangementClosedConeProjectiveRay_zero
    (A : FiniteProjectiveLineArrangement Line) (base : Line)
    (sigma : Line -> Bool) {q u : Fin 3 -> ℝ}
    (hq0 : q ≠ 0)
    (hq : q ∈ A.arrangementClosedSignCone sigma)
    (hu : u ∈ A.arrangementSignCone sigma) :
    A.arrangementClosedConeProjectiveRay base sigma hq0 hq hu 0 =
      Projectivization.mk ℝ q hq0 := by
  simp [arrangementClosedConeProjectiveRay,
    arrangementClosedConeQuadraticRay, pow_two]

theorem continuous_arrangementClosedConeProjectiveRay
    (A : FiniteProjectiveLineArrangement Line) (base : Line)
    (sigma : Line -> Bool) {q u : Fin 3 -> ℝ}
    (hq0 : q ≠ 0)
    (hq : q ∈ A.arrangementClosedSignCone sigma)
    (hu : u ∈ A.arrangementSignCone sigma) :
    Continuous (A.arrangementClosedConeProjectiveRay
      base sigma hq0 hq hu) := by
  have hvector : Continuous (fun t : ℝ =>
      arrangementClosedConeQuadraticRay q u t) := by
    exact continuous_const.add ((continuous_id.pow 2).smul continuous_const)
  simpa only [arrangementClosedConeProjectiveRay,
    Projectivization.mk'_eq_mk] using
      continuous_quotient_mk'.comp
        (hvector.subtype_mk fun t =>
          A.arrangementClosedConeQuadraticRay_ne_zero
            base sigma hq0 hq hu t)

/-- A nonzero vector in the closed homogeneous cone of an actual face
projects to the ambient closure of that face. -/
theorem projectivization_mem_closure_arrangementFaceCarrier_of_mem_closedSignCone
    (A : FiniteProjectiveLineArrangement Line) (base : Line)
    (F : A.ArrangementFace) {q : Fin 3 -> ℝ} (hq0 : q ≠ 0)
    (hq : q ∈ A.arrangementClosedSignCone
      (A.arrangementFaceSignPattern base F)) :
    Projectivization.mk ℝ q hq0 ∈
      closure (A.arrangementFaceCarrier F) := by
  let u := A.arrangementNormalizedRepresentative base
    (A.arrangementFaceRepresentative F)
  have hu : u ∈ A.arrangementSignCone
      (A.arrangementFaceSignPattern base F) := by
    exact A.arrangementNormalizedRepresentative_mem_arrangementSignCone
      base (A.arrangementFaceRepresentative F)
  have hmaps : Set.MapsTo
      (A.arrangementClosedConeProjectiveRay base
        (A.arrangementFaceSignPattern base F) hq0 hq hu)
      ({0}ᶜ : Set ℝ) (A.arrangementFaceCarrier F) := by
    intro t ht
    have ht0 : t ≠ 0 := by
      simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using ht
    have hstrict :=
      A.arrangementClosedConeQuadraticRay_mem_arrangementSignCone
        (A.arrangementFaceSignPattern base F) hq hu ht0
    have hcarrier :=
      A.arrangementSignConeToComplement_mem_arrangementFaceCarrier
        base F hstrict
    simpa only [arrangementClosedConeProjectiveRay,
      arrangementSignConeToComplement, Projectivization.mk'_eq_mk] using hcarrier
  have hzero : (0 : ℝ) ∈ closure ({0}ᶜ : Set ℝ) := by
    rw [closure_compl_singleton]
    exact Set.mem_univ 0
  have hcontinuousAt : ContinuousAt
      (A.arrangementClosedConeProjectiveRay base
        (A.arrangementFaceSignPattern base F) hq0 hq hu) 0 :=
    (A.continuous_arrangementClosedConeProjectiveRay base
      (A.arrangementFaceSignPattern base F) hq0 hq hu).continuousAt
  have hcontinuousWithinAt : ContinuousWithinAt
      (A.arrangementClosedConeProjectiveRay base
        (A.arrangementFaceSignPattern base F) hq0 hq hu) ({0}ᶜ : Set ℝ) 0 :=
    hcontinuousAt.continuousWithinAt
  have hclosure := hcontinuousWithinAt.mem_closure hzero hmaps
  simpa only [A.arrangementClosedConeProjectiveRay_zero] using hclosure

/-- A finite family of oriented evaluations, packaged as one linear map. -/
noncomputable def arrangementOrientedEvaluationMap
    (A : FiniteProjectiveLineArrangement Line) (sigma : Line -> Bool)
    (K : Finset Line) :
    (Fin 3 -> ℝ) →ₗ[ℝ] ({l // l ∈ K} -> ℝ) :=
  LinearMap.pi fun l => A.arrangementOrientedEvaluation sigma l.1

@[simp]
theorem arrangementOrientedEvaluationMap_apply
    (A : FiniteProjectiveLineArrangement Line) (sigma : Line -> Bool)
    (K : Finset Line) (v : Fin 3 -> ℝ) (l : {l // l ∈ K}) :
    A.arrangementOrientedEvaluationMap sigma K v l =
      A.arrangementOrientedEvaluation sigma l.1 v :=
  rfl

/-- Any subfamily which still defines the pointed full cone has at least
three members.  This is the dimension-three kernel argument. -/
theorem three_le_card_of_arrangementClosedSignConeOn_eq
    (A : FiniteProjectiveLineArrangement Line) (hA : A.NonPencil)
    (sigma : Line -> Bool) (K : Finset Line)
    (hK : A.arrangementClosedSignConeOn sigma K =
      A.arrangementClosedSignCone sigma) :
    3 ≤ K.card := by
  classical
  by_contra hthree
  have hcard : K.card < 3 := Nat.lt_of_not_ge hthree
  have hdim :
      Module.finrank ℝ ({l // l ∈ K} -> ℝ) <
        Module.finrank ℝ (Fin 3 -> ℝ) := by
    simpa [Module.finrank_pi] using hcard
  have hker :
      LinearMap.ker (A.arrangementOrientedEvaluationMap sigma K) ≠ ⊥ :=
    (A.arrangementOrientedEvaluationMap sigma K).ker_ne_bot_of_finrank_lt hdim
  obtain ⟨v, hvker, hvne⟩ := (Submodule.ne_bot_iff _).mp hker
  change A.arrangementOrientedEvaluationMap sigma K v = 0 at hvker
  have hvzero : ∀ l ∈ K,
      A.arrangementOrientedEvaluation sigma l v = 0 := by
    intro l hl
    have happly := congrFun hvker (⟨l, hl⟩ : {l // l ∈ K})
    simpa only [A.arrangementOrientedEvaluationMap_apply, Pi.zero_apply] using happly
  have hvCone : v ∈ A.arrangementClosedSignConeOn sigma K := by
    rw [A.mem_arrangementClosedSignConeOn]
    intro l hl
    rw [hvzero l hl]
  have hnegCone : -v ∈ A.arrangementClosedSignConeOn sigma K := by
    rw [A.mem_arrangementClosedSignConeOn]
    intro l hl
    rw [LinearMap.map_neg, hvzero l hl, neg_zero]
  have hvFull : v ∈ A.arrangementClosedSignCone sigma := by
    rw [← hK]
    exact hvCone
  have hnegFull : -v ∈ A.arrangementClosedSignCone sigma := by
    rw [← hK]
    exact hnegCone
  exact hvne
    (A.eq_zero_of_mem_arrangementClosedSignCone_of_neg_mem_of_nonPencil
      hA sigma hvFull hnegFull)

/-- There is a cardinality-minimal subfamily of the finitely many inequalities
which still defines the full closed sign cone. -/
theorem exists_cardMinimal_arrangementClosedSignCone_indexSet
    (A : FiniteProjectiveLineArrangement Line) (sigma : Line -> Bool) :
    ∃ K : Finset Line,
      A.arrangementClosedSignConeOn sigma K =
          A.arrangementClosedSignCone sigma ∧
        ∀ L : Finset Line,
          A.arrangementClosedSignConeOn sigma L =
            A.arrangementClosedSignCone sigma →
          K.card ≤ L.card := by
  classical
  let candidates : Finset (Finset Line) :=
    Finset.univ.powerset.filter fun K =>
      A.arrangementClosedSignConeOn sigma K =
        A.arrangementClosedSignCone sigma
  have hcandidates : candidates.Nonempty := by
    refine ⟨Finset.univ, ?_⟩
    simp only [candidates, Finset.mem_filter, Finset.mem_powerset]
    exact ⟨Finset.Subset.rfl,
      A.arrangementClosedSignConeOn_univ sigma⟩
  obtain ⟨K, hKmem, hKmin⟩ :=
    candidates.exists_min_image Finset.card hcandidates
  have hK : A.arrangementClosedSignConeOn sigma K =
      A.arrangementClosedSignCone sigma := by
    have h := hKmem
    simp only [candidates, Finset.mem_filter] at h
    exact h.2
  refine ⟨K, hK, ?_⟩
  intro L hL
  apply hKmin L
  simp only [candidates, Finset.mem_filter, Finset.mem_powerset]
  exact ⟨Finset.subset_univ L, hL⟩

/-- Deleting an inequality from a cardinality-minimal defining family exposes
it: some vector satisfies every retained inequality and strictly violates the
deleted one. -/
theorem exists_eraseFacetWitness_of_cardMinimal
    (A : FiniteProjectiveLineArrangement Line) (sigma : Line -> Bool)
    (K : Finset Line)
    (hK : A.arrangementClosedSignConeOn sigma K =
      A.arrangementClosedSignCone sigma)
    (hminimal : ∀ L : Finset Line,
      A.arrangementClosedSignConeOn sigma L =
          A.arrangementClosedSignCone sigma →
        K.card ≤ L.card)
    {l : Line} (hl : l ∈ K) :
    ∃ x : Fin 3 -> ℝ,
      x ∈ A.arrangementClosedSignConeOn sigma (K.erase l) ∧
        A.arrangementOrientedEvaluation sigma l x < 0 := by
  classical
  have heraseNe :
      A.arrangementClosedSignConeOn sigma (K.erase l) ≠
        A.arrangementClosedSignCone sigma := by
    intro herase
    have hcard := hminimal (K.erase l) herase
    rw [Finset.card_erase_of_mem hl] at hcard
    have hKpos : 0 < K.card := Finset.card_pos.mpr ⟨l, hl⟩
    omega
  have hfullSubset :
      A.arrangementClosedSignCone sigma ⊆
        A.arrangementClosedSignConeOn sigma (K.erase l) := by
    intro x hx
    have hxK : x ∈ A.arrangementClosedSignConeOn sigma K := by
      rw [hK]
      exact hx
    exact A.arrangementClosedSignConeOn_mono sigma
      (Finset.erase_subset l K) hxK
  have hproper : ∃ x : Fin 3 -> ℝ,
      x ∈ A.arrangementClosedSignConeOn sigma (K.erase l) ∧
        x ∉ A.arrangementClosedSignCone sigma := by
    by_contra h
    have heraseSubset :
        A.arrangementClosedSignConeOn sigma (K.erase l) ⊆
          A.arrangementClosedSignCone sigma := by
      intro x hx
      by_contra hxfull
      exact h ⟨x, hx, hxfull⟩
    exact heraseNe (Set.Subset.antisymm heraseSubset hfullSubset)
  obtain ⟨x, hxerase, hxnot⟩ := hproper
  refine ⟨x, hxerase, ?_⟩
  have hnotnonneg : ¬ 0 ≤ A.arrangementOrientedEvaluation sigma l x := by
    intro hlx
    have hxK : x ∈ A.arrangementClosedSignConeOn sigma K := by
      rw [A.mem_arrangementClosedSignConeOn]
      intro m hm
      by_cases hml : m = l
      · subst m
        exact hlx
      · exact (A.mem_arrangementClosedSignConeOn sigma (K.erase l) x).mp
          hxerase m (Finset.mem_erase.mpr ⟨hml, hm⟩)
    apply hxnot
    rw [← hK]
    exact hxK
  exact lt_of_not_ge hnotnonneg

/-- The explicit intersection of the segment from a strict point to an
erase-witness with the supporting kernel. -/
noncomputable def arrangementFacetVector
    (A : FiniteProjectiveLineArrangement Line) (sigma : Line -> Bool)
    (l : Line) (x u : Fin 3 -> ℝ) : Fin 3 -> ℝ :=
  (-A.arrangementOrientedEvaluation sigma l x) • u +
    (A.arrangementOrientedEvaluation sigma l u) • x

theorem arrangementOrientedEvaluation_arrangementFacetVector_self
    (A : FiniteProjectiveLineArrangement Line) (sigma : Line -> Bool)
    (l : Line) (x u : Fin 3 -> ℝ) :
    A.arrangementOrientedEvaluation sigma l
      (A.arrangementFacetVector sigma l x u) = 0 := by
  change A.arrangementOrientedEvaluation sigma l
    ((-A.arrangementOrientedEvaluation sigma l x) • u +
      (A.arrangementOrientedEvaluation sigma l u) • x) = 0
  rw [LinearMap.map_add, LinearMap.map_smul,
    LinearMap.map_smul, smul_eq_mul, smul_eq_mul]
  ring

/-- Every retained inequality other than the supporting one is strict on
the explicit facet vector. -/
theorem arrangementOrientedEvaluation_arrangementFacetVector_pos
    (A : FiniteProjectiveLineArrangement Line) (sigma : Line -> Bool)
    (K : Finset Line) {l m : Line} (hl : l ∈ K) (hm : m ∈ K)
    (hml : m ≠ l) {x u : Fin 3 -> ℝ}
    (hx : x ∈ A.arrangementClosedSignConeOn sigma (K.erase l))
    (hxl : A.arrangementOrientedEvaluation sigma l x < 0)
    (hu : u ∈ A.arrangementSignCone sigma) :
    0 < A.arrangementOrientedEvaluation sigma m
      (A.arrangementFacetVector sigma l x u) := by
  have hxm : 0 ≤ A.arrangementOrientedEvaluation sigma m x :=
    (A.mem_arrangementClosedSignConeOn sigma (K.erase l) x).mp
      hx m (Finset.mem_erase.mpr ⟨hml, hm⟩)
  have hum : 0 < A.arrangementOrientedEvaluation sigma m u :=
    (A.mem_arrangementSignCone_iff_orientedEvaluation_pos sigma u).mp hu m
  have hul : 0 < A.arrangementOrientedEvaluation sigma l u :=
    (A.mem_arrangementSignCone_iff_orientedEvaluation_pos sigma u).mp hu l
  change 0 < A.arrangementOrientedEvaluation sigma m
    ((-A.arrangementOrientedEvaluation sigma l x) • u +
      (A.arrangementOrientedEvaluation sigma l u) • x)
  rw [LinearMap.map_add, LinearMap.map_smul,
    LinearMap.map_smul, smul_eq_mul, smul_eq_mul]
  exact add_pos_of_pos_of_nonneg (mul_pos (neg_pos.mpr hxl) hum)
    (mul_nonneg hul.le hxm)

/-- A minimal defining family supplies, for each of its members, a nonzero
closed-cone vector which vanishes there and is strict on every other member
of the defining family. -/
theorem exists_facetVector_strict_on_minimalIndexSet
    (A : FiniteProjectiveLineArrangement Line) (hA : A.NonPencil)
    (sigma : Line -> Bool) (K : Finset Line)
    (hK : A.arrangementClosedSignConeOn sigma K =
      A.arrangementClosedSignCone sigma)
    (hminimal : ∀ L : Finset Line,
      A.arrangementClosedSignConeOn sigma L =
          A.arrangementClosedSignCone sigma →
        K.card ≤ L.card)
    {u : Fin 3 -> ℝ} (hu : u ∈ A.arrangementSignCone sigma)
    {l : Line} (hl : l ∈ K) :
    ∃ q : Fin 3 -> ℝ,
      q ≠ 0 ∧ q ∈ A.arrangementClosedSignCone sigma ∧
        A.arrangementOrientedEvaluation sigma l q = 0 ∧
        ∀ m ∈ K, m ≠ l →
          0 < A.arrangementOrientedEvaluation sigma m q := by
  obtain ⟨x, hx, hxl⟩ :=
    A.exists_eraseFacetWitness_of_cardMinimal sigma K hK hminimal hl
  let q := A.arrangementFacetVector sigma l x u
  have hqself : A.arrangementOrientedEvaluation sigma l q = 0 := by
    exact A.arrangementOrientedEvaluation_arrangementFacetVector_self
      sigma l x u
  have hqpos : ∀ m ∈ K, m ≠ l →
      0 < A.arrangementOrientedEvaluation sigma m q := by
    intro m hm hml
    exact A.arrangementOrientedEvaluation_arrangementFacetVector_pos
      sigma K hl hm hml hx hxl hu
  have hqK : q ∈ A.arrangementClosedSignConeOn sigma K := by
    rw [A.mem_arrangementClosedSignConeOn]
    intro m hm
    by_cases hml : m = l
    · subst m
      exact hqself.symm.le
    · exact (hqpos m hm hml).le
  have hqFull : q ∈ A.arrangementClosedSignCone sigma := by
    rw [← hK]
    exact hqK
  have hthree : 3 ≤ K.card :=
    A.three_le_card_of_arrangementClosedSignConeOn_eq hA sigma K hK
  have herasePos : 0 < (K.erase l).card := by
    rw [Finset.card_erase_of_mem hl]
    omega
  obtain ⟨m, hm⟩ := Finset.card_pos.mp herasePos
  have hm' := Finset.mem_erase.mp hm
  have hq0 : q ≠ 0 := by
    intro hzero
    have := hqpos m hm'.2 hm'.1
    rw [hzero, LinearMap.map_zero] at this
    exact (lt_irrefl 0 this)
  exact ⟨q, hq0, hqFull, hqself, hqpos⟩

/-- A facet vector which is strict on the other members of a defining
subfamily is automatically strict on every other arrangement inequality.
Otherwise a small motion inside the supporting kernel preserves the finite
strict inequalities but violates the additional weak inequality. -/
theorem strict_orientedEvaluation_of_facetVector
    (A : FiniteProjectiveLineArrangement Line) (sigma : Line -> Bool)
    (K : Finset Line)
    (hK : A.arrangementClosedSignConeOn sigma K =
      A.arrangementClosedSignCone sigma)
    {l : Line} (hl : l ∈ K) {q : Fin 3 -> ℝ}
    (hqFull : q ∈ A.arrangementClosedSignCone sigma)
    (hqself : A.arrangementOrientedEvaluation sigma l q = 0)
    (hqpos : ∀ k ∈ K, k ≠ l →
      0 < A.arrangementOrientedEvaluation sigma k q) :
    ∀ m, m ≠ l →
      0 < A.arrangementOrientedEvaluation sigma m q := by
  intro m hml
  have hqmNonneg : 0 ≤ A.arrangementOrientedEvaluation sigma m q :=
    (A.mem_arrangementClosedSignCone_iff_orientedEvaluation_nonneg
      sigma q).mp hqFull m
  rcases hqmNonneg.eq_or_lt with hqmZero | hqmPos
  · obtain ⟨w, hlw, hmw⟩ :=
      A.exists_orientedEvaluation_neg_on_kernel_of_ne sigma hml.symm
    have hqOpen : q ∈ A.arrangementSignConeOn sigma (K.erase l) := by
      rw [A.mem_arrangementSignConeOn]
      intro k hk
      exact hqpos k (Finset.mem_of_mem_erase hk)
        (Finset.ne_of_mem_erase hk)
    let curve : ℝ -> (Fin 3 -> ℝ) := fun t => q + t • w
    have hcurve : Continuous curve := by
      exact continuous_const.add (continuous_id.smul continuous_const)
    have htendsto : Filter.Tendsto curve (nhds 0) (nhds q) := by
      have hcurveAtZero : ContinuousAt curve 0 := hcurve.continuousAt
      change Filter.Tendsto curve (nhds 0) (nhds (curve 0)) at hcurveAtZero
      have hcurveZero : curve 0 = q := by simp [curve]
      rw [hcurveZero] at hcurveAtZero
      exact hcurveAtZero
    have hevent : ∀ᶠ t in nhds (0 : ℝ),
        curve t ∈ A.arrangementSignConeOn sigma (K.erase l) :=
      htendsto.eventually
        ((A.isOpen_arrangementSignConeOn sigma (K.erase l)).mem_nhds hqOpen)
    obtain ⟨epsilon, hepsilon, hstable⟩ :=
      Metric.eventually_nhds_iff.mp hevent
    let delta : ℝ := epsilon / 2
    have hdelta : 0 < delta := by
      exact div_pos hepsilon (by norm_num)
    have hdist : dist delta (0 : ℝ) < epsilon := by
      rw [Real.dist_eq, sub_zero, abs_of_pos hdelta]
      dsimp only [delta]
      linarith
    have hpertOpen := hstable hdist
    have hpertSelf : A.arrangementOrientedEvaluation sigma l (curve delta) = 0 := by
      change A.arrangementOrientedEvaluation sigma l (q + delta • w) = 0
      rw [LinearMap.map_add, LinearMap.map_smul, hqself, hlw,
        smul_eq_mul]
      ring
    have hpertK : curve delta ∈ A.arrangementClosedSignConeOn sigma K := by
      rw [A.mem_arrangementClosedSignConeOn]
      intro k hk
      by_cases hkl : k = l
      · subst k
        exact hpertSelf.symm.le
      · exact ((A.mem_arrangementSignConeOn sigma (K.erase l)
          (curve delta)).mp hpertOpen k
            (Finset.mem_erase.mpr ⟨hkl, hk⟩)).le
    have hpertFull : curve delta ∈ A.arrangementClosedSignCone sigma := by
      rw [← hK]
      exact hpertK
    have hpertMNeg :
        A.arrangementOrientedEvaluation sigma m (curve delta) < 0 := by
      change A.arrangementOrientedEvaluation sigma m (q + delta • w) < 0
      rw [LinearMap.map_add, LinearMap.map_smul, hqmZero.symm,
        smul_eq_mul, zero_add]
      exact mul_neg_of_pos_of_neg hdelta hmw
    have hpertMNonneg :
        0 ≤ A.arrangementOrientedEvaluation sigma m (curve delta) :=
      (A.mem_arrangementClosedSignCone_iff_orientedEvaluation_nonneg
        sigma (curve delta)).mp hpertFull m
    exact (not_lt_of_ge hpertMNonneg hpertMNeg).elim
  · exact hqmPos

/-- Exact-one-zero facet extraction from a cardinality-minimal defining
subfamily. -/
theorem exists_exactOneZero_facetVector_of_cardMinimal
    (A : FiniteProjectiveLineArrangement Line) (hA : A.NonPencil)
    (sigma : Line -> Bool) (K : Finset Line)
    (hK : A.arrangementClosedSignConeOn sigma K =
      A.arrangementClosedSignCone sigma)
    (hminimal : ∀ L : Finset Line,
      A.arrangementClosedSignConeOn sigma L =
          A.arrangementClosedSignCone sigma →
        K.card ≤ L.card)
    {u : Fin 3 -> ℝ} (hu : u ∈ A.arrangementSignCone sigma)
    {l : Line} (hl : l ∈ K) :
    ∃ q : Fin 3 -> ℝ,
      q ≠ 0 ∧ q ∈ A.arrangementClosedSignCone sigma ∧
        A.arrangementOrientedEvaluation sigma l q = 0 ∧
        ∀ m, m ≠ l →
          0 < A.arrangementOrientedEvaluation sigma m q := by
  obtain ⟨q, hq0, hqFull, hqself, hqpos⟩ :=
    A.exists_facetVector_strict_on_minimalIndexSet
      hA sigma K hK hminimal hu hl
  refine ⟨q, hq0, hqFull, hqself, ?_⟩
  exact A.strict_orientedEvaluation_of_facetVector
    sigma K hK hl hqFull hqself hqpos

/-- Combined unconditional finite-dimensional output for an actual face. -/
theorem exists_minimal_arrangementFaceClosedSignCone_indexSet
    (A : FiniteProjectiveLineArrangement Line) (hA : A.NonPencil)
    (base : Line) (F : A.ArrangementFace) :
    ∃ K : Finset Line,
      A.arrangementClosedSignConeOn
          (A.arrangementFaceSignPattern base F) K =
          A.arrangementClosedSignCone
            (A.arrangementFaceSignPattern base F) ∧
        3 ≤ K.card ∧
        ∀ l ∈ K, ∃ x : Fin 3 -> ℝ,
          x ∈ A.arrangementClosedSignConeOn
              (A.arrangementFaceSignPattern base F) (K.erase l) ∧
            A.arrangementOrientedEvaluation
              (A.arrangementFaceSignPattern base F) l x < 0 := by
  obtain ⟨K, hK, hminimal⟩ :=
    A.exists_cardMinimal_arrangementClosedSignCone_indexSet
      (A.arrangementFaceSignPattern base F)
  refine ⟨K, hK,
    A.three_le_card_of_arrangementClosedSignConeOn_eq hA _ K hK, ?_⟩
  intro l hl
  exact A.exists_eraseFacetWitness_of_cardMinimal _ K hK hminimal hl

/-- Literal geometric hand-off.  A defining subfamily of size at least three
whose members are injectively realized by open boundary arcs forces the face
degree bound. -/
theorem three_le_arrangementFaceBoundary_card_of_indexSet_facetArcs
    (A : FiniteProjectiveLineArrangement Line) (hA : A.NonPencil)
    (base : Line) (F : A.ArrangementFace) (K : Finset Line)
    (hK : A.arrangementClosedSignConeOn
        (A.arrangementFaceSignPattern base F) K =
      A.arrangementClosedSignCone (A.arrangementFaceSignPattern base F))
    (edge : {l // l ∈ K} -> A.GeometricEdge)
    (q : {l // l ∈ K} -> RealProjectivePoint)
    (harc : ∀ l, q l ∈ A.geometricEdgeOpenArc (edge l))
    (hclosure : ∀ l, q l ∈ closure (A.arrangementFaceCarrier F))
    (hinj : Function.Injective edge) :
    3 ≤ (A.arrangementFaceBoundary F).card := by
  classical
  have hthree : 3 ≤ K.card :=
    A.three_le_card_of_arrangementClosedSignConeOn_eq hA _ K hK
  let edge' : {l // l ∈ K} ->
      {e // e ∈ A.arrangementFaceBoundary F} := fun l =>
    ⟨edge l, (A.mem_arrangementFaceBoundary_iff F (edge l)).mpr
      ⟨q l, harc l, hclosure l⟩⟩
  have hedge' : Function.Injective edge' := by
    intro l m hlm
    apply hinj
    exact congrArg Subtype.val hlm
  have hcard := Fintype.card_le_of_injective edge' hedge'
  have hKcard : K.card ≤ (A.arrangementFaceBoundary F).card := by
    simpa only [Fintype.card_coe] using hcard
  exact hthree.trans hKcard

/-- Every genuine face of a non-pencil real projective line arrangement has
at least three literal geometric boundary edges. -/
theorem three_le_arrangementFaceBoundary_card
    (A : FiniteProjectiveLineArrangement Line) (hA : A.NonPencil)
    (base : Line) (F : A.ArrangementFace) :
    3 ≤ (A.arrangementFaceBoundary F).card := by
  classical
  let sigma := A.arrangementFaceSignPattern base F
  obtain ⟨K, hK, hminimal⟩ :=
    A.exists_cardMinimal_arrangementClosedSignCone_indexSet sigma
  let u := A.arrangementNormalizedRepresentative base
    (A.arrangementFaceRepresentative F)
  have hu : u ∈ A.arrangementSignCone sigma := by
    exact A.arrangementNormalizedRepresentative_mem_arrangementSignCone
      base (A.arrangementFaceRepresentative F)
  have hfacet (l : {l // l ∈ K}) :
      ∃ q : Fin 3 -> ℝ,
        q ≠ 0 ∧ q ∈ A.arrangementClosedSignCone sigma ∧
          A.arrangementOrientedEvaluation sigma l.1 q = 0 ∧
          ∀ m, m ≠ l.1 →
            0 < A.arrangementOrientedEvaluation sigma m q :=
    A.exists_exactOneZero_facetVector_of_cardMinimal
      hA sigma K hK hminimal hu l.2
  let v : {l // l ∈ K} -> (Fin 3 -> ℝ) := fun l =>
    Classical.choose (hfacet l)
  have hv (l : {l // l ∈ K}) :
      v l ≠ 0 ∧ v l ∈ A.arrangementClosedSignCone sigma ∧
        A.arrangementOrientedEvaluation sigma l.1 (v l) = 0 ∧
        ∀ m, m ≠ l.1 →
          0 < A.arrangementOrientedEvaluation sigma m (v l) :=
    Classical.choose_spec (hfacet l)
  let point : {l // l ∈ K} -> RealProjectivePoint := fun l =>
    Projectivization.mk ℝ (v l) (hv l).1
  have hregular (l : {l // l ∈ K}) (m : Line) :
      A.Incident (point l) m ↔ m = l.1 := by
    change A.Incident (Projectivization.mk ℝ (v l) (hv l).1) m ↔ _
    rw [A.incident_projectivization_mk_iff_orientedEvaluation_eq_zero
      sigma m (v l) (hv l).1]
    constructor
    · intro hmzero
      by_contra hml
      exact (ne_of_gt ((hv l).2.2.2 m hml)) hmzero
    · intro hml
      subst m
      exact (hv l).2.2.1
  have hgap (l : {l // l ∈ K}) :
      ∃! g : A.CircularGapSlot l.1,
        point l ∈ A.geometricEdgeOpenArc (A.circularGapEdge l.1 g) :=
    A.existsUnique_circularGap_mem_geometricEdgeOpenArc_of_regular
      hA (point l) l.1 (hregular l)
  let gap : (l : {l // l ∈ K}) -> A.CircularGapSlot l.1 := fun l =>
    Classical.choose (ExistsUnique.exists (hgap l))
  have hgapmem (l : {l // l ∈ K}) :
      point l ∈ A.geometricEdgeOpenArc
        (A.circularGapEdge l.1 (gap l)) :=
    Classical.choose_spec (ExistsUnique.exists (hgap l))
  let edge : {l // l ∈ K} -> A.GeometricEdge := fun l =>
    A.circularGapEdge l.1 (gap l)
  have harc (l : {l // l ∈ K}) :
      point l ∈ A.geometricEdgeOpenArc (edge l) := by
    exact hgapmem l
  have hclosure (l : {l // l ∈ K}) :
      point l ∈ closure (A.arrangementFaceCarrier F) := by
    change Projectivization.mk ℝ (v l) (hv l).1 ∈
      closure (A.arrangementFaceCarrier F)
    apply A.projectivization_mem_closure_arrangementFaceCarrier_of_mem_closedSignCone
      base F (hv l).1
    simpa only [sigma] using (hv l).2.1
  have hedge : Function.Injective edge := by
    intro l m hlm
    apply Subtype.ext
    have hline := congrArg A.edgeSlotLine hlm
    simpa only [edge, A.circularGapEdge_line] using hline
  have hK' : A.arrangementClosedSignConeOn
        (A.arrangementFaceSignPattern base F) K =
      A.arrangementClosedSignCone
        (A.arrangementFaceSignPattern base F) := by
    simpa only [sigma] using hK
  exact A.three_le_arrangementFaceBoundary_card_of_indexSet_facetArcs
    hA base F K hK' edge point harc hclosure hedge

end FiniteProjectiveLineArrangement

end Erdos506.Incidence
