import Erdos506.Incidence.RealProjectiveArrangementFaceThreeMinimalFinish

/-!
# The ordinary-edge entrance to the Type-A near-pencil argument

This file extracts the two literal transverse supporting lines at the
ordinary endpoints of an actual cyclic arrangement edge.  It is the finite
incidence entrance to the geometric `DD`-edge lemma.
-/

namespace Erdos506.Incidence

open scoped LinearAlgebra.Projectivization

universe u

namespace FiniteProjectiveLineArrangement

variable {Line : Type u} [Fintype Line] [DecidableEq Line]

noncomputable local instance realProjectiveOnePointTopologicalSpaceForOrdinaryEdgeTriangle :
    TopologicalSpace RealProjectiveOnePoint :=
  @instTopologicalSpaceQuotient
    {v : RealProjectiveLineVector // v ≠ 0}
    (projectivizationSetoid ℝ RealProjectiveLineVector)
    (by infer_instance)

noncomputable local instance realProjectivePointTopologicalSpaceForOrdinaryEdgeTriangle :
    TopologicalSpace RealProjectivePoint :=
  realProjectivePointQuotientTopology

noncomputable local instance realProjectivePointDecidableEqForOrdinaryEdgeTriangle :
    DecidableEq RealProjectivePoint :=
  Classical.decEq _

noncomputable local instance geometricEdgeDecidableEqForOrdinaryEdgeTriangle
    (A : FiniteProjectiveLineArrangement Line) : DecidableEq A.GeometricEdge :=
  Classical.decEq _

noncomputable local instance incidentDecidableForOrdinaryEdgeTriangle
    (A : FiniteProjectiveLineArrangement Line)
    (p : RealProjectivePoint) (l : Line) :
    Decidable (A.Incident p l) :=
  Classical.propDecidable _

/-- The eleven named supports of a four-strip gallery: two four-line rails
and three singleton cross-lines. -/
abbrev GalleryLineLabel := (Fin 4 ⊕ Fin 4) ⊕ Fin 3

def galleryStripLeft (i : Fin 3) : Fin 4 :=
  ⟨i.1, lt_trans i.2 (by decide)⟩

def galleryStripRight (i : Fin 3) : Fin 4 :=
  ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩

noncomputable def circularGapPredecessor
    (A : FiniteProjectiveLineArrangement Line) (l : Line) :
    A.CircularGapSlot l → A.CircularGapSlot l :=
  (A.circularGapSuccessorEquiv l).symm

@[simp]
theorem circularGapSuccessor_predecessor
    (A : FiniteProjectiveLineArrangement Line) (l : Line)
    (p : A.CircularGapSlot l) :
    A.circularGapSuccessor l (A.circularGapPredecessor l p) = p :=
  (A.circularGapSuccessorEquiv l).apply_symm_apply p

@[simp]
theorem circularGapPredecessor_successor
    (A : FiniteProjectiveLineArrangement Line) (l : Line)
    (p : A.CircularGapSlot l) :
    A.circularGapPredecessor l (A.circularGapSuccessor l p) = p :=
  (A.circularGapSuccessorEquiv l).symm_apply_apply p

private theorem finRotate_symm_ne_finRotate_of_three_le
    {n : ℕ} (hn : 3 ≤ n) (i : Fin n) :
    (finRotate n).symm i ≠ finRotate n i := by
  intro h
  have hsq : finRotate n (finRotate n i) = i := by
    calc
      finRotate n (finRotate n i) =
          finRotate n ((finRotate n).symm i) := congrArg _ h.symm
      _ = i := (finRotate n).apply_symm_apply i
  cases n with
  | zero => omega
  | succ k =>
      by_cases hi : i = Fin.last k
      · subst i
        have hzero : (0 : Fin (k + 1)) ≠ Fin.last k := by
          intro h
          have hv := congrArg Fin.val h
          simp only [Fin.val_zero, Fin.val_last] at hv
          omega
        have hv := congrArg Fin.val hsq
        rw [finRotate_last, coe_finRotate_of_ne_last hzero] at hv
        simp only [Fin.val_zero, Fin.val_last] at hv
        omega
      · by_cases hri : finRotate (k + 1) i = Fin.last k
        · have hv := congrArg Fin.val hsq
          rw [hri, finRotate_last] at hv
          have hriv := congrArg Fin.val hri
          rw [coe_finRotate_of_ne_last hi] at hriv
          simp only [Fin.val_zero, Fin.val_last] at hv hriv
          omega
        · have hv := congrArg Fin.val hsq
          rw [coe_finRotate_of_ne_last hri,
            coe_finRotate_of_ne_last hi] at hv
          omega

/-- On a line with at least three marked vertices, the two cyclic neighbours
of a marked vertex are different even as projective points. -/
theorem circularGapPredecessor_val_ne_successor_val_of_three_le
    (A : FiniteProjectiveLineArrangement Line) (l : Line)
    (p : A.CircularGapSlot l)
    (hcard : 3 ≤ Fintype.card (A.CircularGapSlot l)) :
    (A.circularGapPredecessor l p).1 ≠
      (A.circularGapSuccessor l p).1 := by
  let E := A.circularGapCyclicLabel l
  let i := E.symm p
  have hp : E i = p := E.apply_symm_apply p
  have hpred : A.circularGapPredecessor l p =
      E ((finRotate (Fintype.card (A.CircularGapSlot l))).symm i) := by
    apply (A.circularGapSuccessorEquiv l).injective
    change A.circularGapSuccessor l (A.circularGapPredecessor l p) =
      A.circularGapSuccessor l
        (E ((finRotate (Fintype.card (A.CircularGapSlot l))).symm i))
    rw [A.circularGapSuccessor_predecessor]
    rw [A.circularGapSuccessor_apply_label]
    rw [(finRotate (Fintype.card (A.CircularGapSlot l))).apply_symm_apply]
    exact hp.symm
  have hsucc : A.circularGapSuccessor l p =
      E (finRotate (Fintype.card (A.CircularGapSlot l)) i) := by
    rw [← hp]
    exact A.circularGapSuccessor_apply_label l i
  intro hval
  have hslots : A.circularGapPredecessor l p =
      A.circularGapSuccessor l p := Subtype.ext hval
  have hlabels :
      E ((finRotate (Fintype.card (A.CircularGapSlot l))).symm i) =
        E (finRotate (Fintype.card (A.CircularGapSlot l)) i) :=
    hpred.symm.trans (hslots.trans hsucc)
  exact finRotate_symm_ne_finRotate_of_three_le hcard i
    (E.injective hlabels)

private theorem finRotate_finCongr
    {n m : ℕ} (h : n = m) (i : Fin n) :
    finRotate m (finCongr h i) = finCongr h (finRotate n i) := by
  subst m
  rfl

/-- The canonical cyclic labelling specialized to a seven-vertex line. -/
noncomputable def circularGapCyclicLabelSeven
    (A : FiniteProjectiveLineArrangement Line) (l : Line)
    (hcard : Fintype.card (A.CircularGapSlot l) = 7) :
    Fin 7 ≃ A.CircularGapSlot l :=
  (finCongr hcard.symm).trans (A.circularGapCyclicLabel l)

theorem circularGapSuccessor_apply_labelSeven
    (A : FiniteProjectiveLineArrangement Line) (l : Line)
    (hcard : Fintype.card (A.CircularGapSlot l) = 7) (i : Fin 7) :
    A.circularGapSuccessor l (A.circularGapCyclicLabelSeven l hcard i) =
      A.circularGapCyclicLabelSeven l hcard (finRotate 7 i) := by
  unfold circularGapCyclicLabelSeven
  change A.circularGapSuccessor l
      (A.circularGapCyclicLabel l (finCongr hcard.symm i)) = _
  rw [A.circularGapSuccessor_apply_label]
  exact congrArg (A.circularGapCyclicLabel l)
    (finRotate_finCongr hcard.symm i)

/-- Lossless finite payload of the labelled four-strip entrance.  The six
base vertices are only required to contain their displayed triples, so a
consumer retains every possible triple-to-quadruple upgrade.  The four
rungs are exact after adjoining the distinguished support `ell`. -/
structure LabelledFourStripGalleryEntrance
    (A : FiniteProjectiveLineArrangement Line) (ell : Line) where
  lineEquiv : GalleryLineLabel ≃ {m : Line // m ≠ ell}
  rungVertex : Fin 4 → RealProjectivePoint
  singletonVertex : Fin 3 → RealProjectivePoint
  upperVertex : Fin 3 → RealProjectivePoint
  lowerVertex : Fin 3 → RealProjectivePoint
  rungIncident_iff : ∀ i m, A.Incident (rungVertex i) m ↔
      m = ell ∨
      m = (lineEquiv (.inl (.inl i))).1 ∨
      m = (lineEquiv (.inl (.inr i))).1
  singletonIncident_iff : ∀ i m,
    A.Incident (singletonVertex i) m ↔
      m = ell ∨ m = (lineEquiv (.inr i)).1
  upperIncidence : ∀ i,
    A.Incident (upperVertex i)
        (lineEquiv (.inl (.inl (galleryStripLeft i)))).1 ∧
    A.Incident (upperVertex i)
        (lineEquiv (.inl (.inl (galleryStripRight i)))).1 ∧
    A.Incident (upperVertex i) (lineEquiv (.inr i)).1
  lowerIncidence : ∀ i,
    A.Incident (lowerVertex i)
        (lineEquiv (.inl (.inr (galleryStripLeft i)))).1 ∧
    A.Incident (lowerVertex i)
        (lineEquiv (.inl (.inr (galleryStripRight i)))).1 ∧
    A.Incident (lowerVertex i) (lineEquiv (.inr i)).1

/-- One lossless `T-D-T` strip step.  The two remote endpoints of the two
rays on `c` give the upper and lower base vertices, while their third
supports land bijectively at the predecessor and successor of `d`. -/
structure OrdinaryTDTGalleryStep
    (A : FiniteProjectiveLineArrangement Line) (ell : Line)
    (d : A.CircularGapSlot ell) where
  c : Line
  c_ne_ell : c ≠ ell
  singletonIncident_iff : ∀ m, A.Incident d.1 m ↔ m = ell ∨ m = c
  upperVertex : RealProjectivePoint
  lowerVertex : RealProjectivePoint
  predecessorUpper : Line
  predecessorLower : Line
  successorUpper : Line
  successorLower : Line
  predecessorUpper_ne_c : predecessorUpper ≠ c
  predecessorLower_ne_c : predecessorLower ≠ c
  successorUpper_ne_c : successorUpper ≠ c
  successorLower_ne_c : successorLower ≠ c
  predecessorUpper_ne_ell : predecessorUpper ≠ ell
  predecessorLower_ne_ell : predecessorLower ≠ ell
  successorUpper_ne_ell : successorUpper ≠ ell
  successorLower_ne_ell : successorLower ≠ ell
  predecessor_ne : predecessorUpper ≠ predecessorLower
  successor_ne : successorUpper ≠ successorLower
  upperIncidence : A.Incident upperVertex c ∧
    A.Incident upperVertex predecessorUpper ∧
    A.Incident upperVertex successorUpper
  lowerIncidence : A.Incident lowerVertex c ∧
    A.Incident lowerVertex predecessorLower ∧
    A.Incident lowerVertex successorLower
  predecessorUpper_point : A.intersection ell predecessorUpper =
    (A.circularGapPredecessor ell d).1
  predecessorLower_point : A.intersection ell predecessorLower =
    (A.circularGapPredecessor ell d).1
  successorUpper_point : A.intersection ell successorUpper =
    (A.circularGapSuccessor ell d).1
  successorLower_point : A.intersection ell successorLower =
    (A.circularGapSuccessor ell d).1

/-- Exchange the two sides of a strip step without changing its cyclic
endpoints. -/
def OrdinaryTDTGalleryStep.swap
    {A : FiniteProjectiveLineArrangement Line} {ell : Line}
    {d : A.CircularGapSlot ell} (S : A.OrdinaryTDTGalleryStep ell d) :
    A.OrdinaryTDTGalleryStep ell d where
  c := S.c
  c_ne_ell := S.c_ne_ell
  singletonIncident_iff := S.singletonIncident_iff
  upperVertex := S.lowerVertex
  lowerVertex := S.upperVertex
  predecessorUpper := S.predecessorLower
  predecessorLower := S.predecessorUpper
  successorUpper := S.successorLower
  successorLower := S.successorUpper
  predecessorUpper_ne_c := S.predecessorLower_ne_c
  predecessorLower_ne_c := S.predecessorUpper_ne_c
  successorUpper_ne_c := S.successorLower_ne_c
  successorLower_ne_c := S.successorUpper_ne_c
  predecessorUpper_ne_ell := S.predecessorLower_ne_ell
  predecessorLower_ne_ell := S.predecessorUpper_ne_ell
  successorUpper_ne_ell := S.successorLower_ne_ell
  successorLower_ne_ell := S.successorUpper_ne_ell
  predecessor_ne := S.predecessor_ne.symm
  successor_ne := S.successor_ne.symm
  upperIncidence := S.lowerIncidence
  lowerIncidence := S.upperIncidence
  predecessorUpper_point := S.predecessorLower_point
  predecessorLower_point := S.predecessorUpper_point
  successorUpper_point := S.successorLower_point
  successorLower_point := S.successorUpper_point

def LabelledFourStripGalleryEntrance.a
    {A : FiniteProjectiveLineArrangement Line} {ell : Line}
    (G : A.LabelledFourStripGalleryEntrance ell) (i : Fin 4) : Line :=
  (G.lineEquiv (.inl (.inl i))).1

def LabelledFourStripGalleryEntrance.b
    {A : FiniteProjectiveLineArrangement Line} {ell : Line}
    (G : A.LabelledFourStripGalleryEntrance ell) (i : Fin 4) : Line :=
  (G.lineEquiv (.inl (.inr i))).1

def LabelledFourStripGalleryEntrance.c
    {A : FiniteProjectiveLineArrangement Line} {ell : Line}
    (G : A.LabelledFourStripGalleryEntrance ell) (i : Fin 3) : Line :=
  (G.lineEquiv (.inr i)).1

theorem LabelledFourStripGalleryEntrance.line_injective
    {A : FiniteProjectiveLineArrangement Line} {ell : Line}
    (G : A.LabelledFourStripGalleryEntrance ell) :
    Function.Injective (fun s : GalleryLineLabel => (G.lineEquiv s).1) :=
  Subtype.val_injective.comp G.lineEquiv.injective

@[simp]
theorem LabelledFourStripGalleryEntrance.a_ne_ell
    {A : FiniteProjectiveLineArrangement Line} {ell : Line}
    (G : A.LabelledFourStripGalleryEntrance ell) (i : Fin 4) :
    G.a i ≠ ell :=
  (G.lineEquiv (.inl (.inl i))).2

@[simp]
theorem LabelledFourStripGalleryEntrance.b_ne_ell
    {A : FiniteProjectiveLineArrangement Line} {ell : Line}
    (G : A.LabelledFourStripGalleryEntrance ell) (i : Fin 4) :
    G.b i ≠ ell :=
  (G.lineEquiv (.inl (.inr i))).2

@[simp]
theorem LabelledFourStripGalleryEntrance.c_ne_ell
    {A : FiniteProjectiveLineArrangement Line} {ell : Line}
    (G : A.LabelledFourStripGalleryEntrance ell) (i : Fin 3) :
    G.c i ≠ ell :=
  (G.lineEquiv (.inr i)).2

theorem LabelledFourStripGalleryEntrance.rungVertex_eq_intersection
    {A : FiniteProjectiveLineArrangement Line} {ell : Line}
    (G : A.LabelledFourStripGalleryEntrance ell) (i : Fin 4) :
    G.rungVertex i = A.intersection ell (G.a i) := by
  apply A.eq_intersection_of_incident (G.a_ne_ell i).symm
  · exact (G.rungIncident_iff i ell).2 (Or.inl rfl)
  · exact (G.rungIncident_iff i (G.a i)).2 (Or.inr (Or.inl rfl))

theorem LabelledFourStripGalleryEntrance.rungSupport
    {A : FiniteProjectiveLineArrangement Line} {ell : Line}
    (G : A.LabelledFourStripGalleryEntrance ell) (i : Fin 4) (m : Line) :
    A.Incident (A.intersection ell (G.a i)) m ↔
      m = ell ∨ m = G.a i ∨ m = G.b i := by
  rw [← G.rungVertex_eq_intersection i]
  exact G.rungIncident_iff i m

theorem LabelledFourStripGalleryEntrance.singletonVertex_eq_intersection
    {A : FiniteProjectiveLineArrangement Line} {ell : Line}
    (G : A.LabelledFourStripGalleryEntrance ell) (i : Fin 3) :
    G.singletonVertex i = A.intersection ell (G.c i) := by
  apply A.eq_intersection_of_incident (G.c_ne_ell i).symm
  · exact (G.singletonIncident_iff i ell).2 (Or.inl rfl)
  · exact (G.singletonIncident_iff i (G.c i)).2 (Or.inr rfl)

theorem LabelledFourStripGalleryEntrance.singletonSupport
    {A : FiniteProjectiveLineArrangement Line} {ell : Line}
    (G : A.LabelledFourStripGalleryEntrance ell) (i : Fin 3) (m : Line) :
    A.Incident (A.intersection ell (G.c i)) m ↔
      m = ell ∨ m = G.c i := by
  rw [← G.singletonVertex_eq_intersection i]
  exact G.singletonIncident_iff i m

theorem LabelledFourStripGalleryEntrance.upperBase
    {A : FiniteProjectiveLineArrangement Line} {ell : Line}
    (G : A.LabelledFourStripGalleryEntrance ell) (i : Fin 3) :
    A.Incident
      (A.intersection (G.a (galleryStripLeft i))
        (G.a (galleryStripRight i))) (G.c i) := by
  have hne : G.a (galleryStripLeft i) ≠ G.a (galleryStripRight i) := by
    intro h
    have hslot := G.line_injective h
    simp [LabelledFourStripGalleryEntrance.a, galleryStripLeft,
      galleryStripRight] at hslot
  have hvertex : G.upperVertex i =
      A.intersection (G.a (galleryStripLeft i))
        (G.a (galleryStripRight i)) := by
    apply A.eq_intersection_of_incident hne
    · exact (G.upperIncidence i).1
    · exact (G.upperIncidence i).2.1
  rw [← hvertex]
  exact (G.upperIncidence i).2.2

theorem LabelledFourStripGalleryEntrance.lowerBase
    {A : FiniteProjectiveLineArrangement Line} {ell : Line}
    (G : A.LabelledFourStripGalleryEntrance ell) (i : Fin 3) :
    A.Incident
      (A.intersection (G.b (galleryStripLeft i))
        (G.b (galleryStripRight i))) (G.c i) := by
  have hne : G.b (galleryStripLeft i) ≠ G.b (galleryStripRight i) := by
    intro h
    have hslot := G.line_injective h
    simp [LabelledFourStripGalleryEntrance.b, galleryStripLeft,
      galleryStripRight] at hslot
  have hvertex : G.lowerVertex i =
      A.intersection (G.b (galleryStripLeft i))
        (G.b (galleryStripRight i)) := by
    apply A.eq_intersection_of_incident hne
    · exact (G.lowerIncidence i).1
    · exact (G.lowerIncidence i).2.1
  rw [← hvertex]
  exact (G.lowerIncidence i).2.2

@[simp]
theorem circularGapEdge_initial
    (A : FiniteProjectiveLineArrangement Line) (l : Line)
    (p : A.CircularGapSlot l) :
    A.geometricEdgeInitial (A.circularGapEdge l p) = p.1 :=
  rfl

@[simp]
theorem circularGapEdge_terminal
    (A : FiniteProjectiveLineArrangement Line) (l : Line)
    (p : A.CircularGapSlot l) :
    A.geometricEdgeTerminal (A.circularGapEdge l p) =
      (A.circularGapSuccessor l p).1 :=
  rfl

/-- Every edge whose support has been identified with `l` is the literal
cyclic-gap edge of a unique slot on `l`. -/
theorem exists_circularGapEdge_eq_of_edgeSlotLine_eq
    (A : FiniteProjectiveLineArrangement Line) (e : A.GeometricEdge)
    (l : Line) (he : A.edgeSlotLine e = l) :
    ∃ g : A.CircularGapSlot l, A.circularGapEdge l g = e := by
  rcases e with ⟨⟨q, hq⟩, ⟨m, hqm⟩⟩
  change m = l at he
  subst m
  let g : A.CircularGapSlot l :=
    ⟨q, (A.mem_lineVertexSet l).2 ⟨hq, hqm⟩⟩
  refine ⟨g, ?_⟩
  rfl

/-- If a cyclic edge on `l` has `d` as one endpoint, its other endpoint is
the predecessor or successor of `d`. -/
theorem other_endpoint_eq_predecessor_or_successor
    (A : FiniteProjectiveLineArrangement Line)
    (l : Line) (d : A.CircularGapSlot l) (e : A.GeometricEdge)
    (T : RealProjectivePoint) (he : A.edgeSlotLine e = l)
    (hpair : ({A.geometricEdgeInitial e, A.geometricEdgeTerminal e} :
        Finset RealProjectivePoint) = {d.1, T})
    (hdT : d.1 ≠ T) :
    T = (A.circularGapPredecessor l d).1 ∨
      T = (A.circularGapSuccessor l d).1 := by
  classical
  obtain ⟨g, rfl⟩ := A.exists_circularGapEdge_eq_of_edgeSlotLine_eq e l he
  have hpair' :
      ({g.1, (A.circularGapSuccessor l g).1} : Finset RealProjectivePoint) =
        {d.1, T} := by
    simpa only [A.circularGapEdge_initial, A.circularGapEdge_terminal] using hpair
  have hdMem : d.1 ∈
      ({g.1, (A.circularGapSuccessor l g).1} :
        Finset RealProjectivePoint) := by
    rw [hpair']
    simp
  have hTMem : T ∈
      ({g.1, (A.circularGapSuccessor l g).1} :
        Finset RealProjectivePoint) := by
    rw [hpair']
    simp
  simp only [Finset.mem_insert, Finset.mem_singleton] at hdMem hTMem
  rcases hdMem with hdg | hdsg
  · have hdg' : d = g := Subtype.ext hdg
    subst d
    rcases hTMem with hTg | hTg
    · exact (hdT hTg.symm).elim
    · exact Or.inr hTg
  · have hdsg' : d = A.circularGapSuccessor l g := Subtype.ext hdsg
    rcases hTMem with hTg | hTg
    · left
      rw [hdsg', A.circularGapPredecessor_successor]
      exact hTg
    · exact (hdT (hdsg.trans hTg.symm)).elim

private theorem ddBracket_add_smul_right
    (p q r : RealProjectiveLineVector) (t : ℝ) :
    realProjectiveBracket p (q + t • r) =
      realProjectiveBracket p q + t * realProjectiveBracket p r := by
  simp [realProjectiveBracket]
  ring

private theorem ddBracket_smul_add_left
    (p q r : RealProjectiveLineVector) (t : ℝ) :
    realProjectiveBracket (t • p + q) r =
      t * realProjectiveBracket p r + realProjectiveBracket q r := by
  simp [realProjectiveBracket]
  ring

/-- The initial endpoint belongs to the closure of its open oriented cyclic
arc.  This is the endpoint-continuity fact absent from the earlier
same-open-edge closure transport. -/
theorem left_mem_closure_projectiveLineCyclicArc
    (L : RealProjectiveLine) (p r : RealProjectivePoint)
    (hp : p.orthogonal L) (hr : r.orthogonal L) (hpr : p ≠ r) :
    p ∈ closure
      {q : RealProjectivePoint | ProjectiveLineCyclic L p q r} := by
  classical
  let P : RealProjectiveOnePoint := projectiveLineParameterPreimage L p hp
  let R : RealProjectiveOnePoint := projectiveLineParameterPreimage L r hr
  have hP : projectiveLineParameter L P = p :=
    projectiveLineParameter_preimage_spec L p hp
  have hR : projectiveLineParameter L R = r :=
    projectiveLineParameter_preimage_spec L r hr
  have hPR : P ≠ R := by
    intro h
    apply hpr
    exact hP.symm.trans ((congrArg (projectiveLineParameter L) h).trans hR)
  let d₀ : ℝ := realProjectiveBracket P.rep R.rep
  have hd₀ : d₀ ≠ 0 := by
    intro hzero
    apply hPR
    calc
      P = Projectivization.mk ℝ P.rep P.rep_nonzero :=
        (Projectivization.mk_rep P).symm
      _ = Projectivization.mk ℝ R.rep R.rep_nonzero :=
        (realProjective_mk_eq_mk_iff_bracket_eq_zero
          P.rep_nonzero R.rep_nonzero).mpr hzero
      _ = R := Projectivization.mk_rep R
  let D : RealProjectiveLineVector := if 0 < d₀ then -R.rep else R.rep
  have hDne : D ≠ 0 := by
    dsimp [D]
    split_ifs
    · exact neg_ne_zero.mpr R.rep_nonzero
    · exact R.rep_nonzero
  have hd : realProjectiveBracket P.rep D < 0 := by
    dsimp [D]
    split_ifs with hdpos
    · rw [show realProjectiveBracket P.rep (-R.rep) = -d₀ by
        simp [d₀, realProjectiveBracket]
        ring]
      exact neg_neg_of_pos hdpos
    · exact lt_of_le_of_ne (le_of_not_gt hdpos) hd₀
  have hD : Projectivization.mk ℝ D hDne = R := by
    rw [← Projectivization.mk_rep R]
    apply (Projectivization.mk_eq_mk_iff' ℝ D R.rep
      hDne R.rep_nonzero).mpr
    dsimp [D]
    split_ifs
    · exact ⟨-1, by simp⟩
    · exact ⟨1, by simp⟩
  let v : ℝ → RealProjectiveLineVector := fun t => P.rep + t • D
  have hvne (t : ℝ) : v t ≠ 0 := by
    by_cases ht : t = 0
    · subst t
      simpa [v] using P.rep_nonzero
    · intro hzero
      have hbracket : realProjectiveBracket P.rep (v t) = 0 := by
        rw [hzero]
        simp [realProjectiveBracket]
      simp only [v] at hbracket
      rw [ddBracket_add_smul_right,
        realProjectiveBracket_self, zero_add] at hbracket
      exact (mul_ne_zero ht (ne_of_lt hd)) hbracket
  let gamma : ℝ → RealProjectivePoint := fun t =>
    projectiveLineParameter L (Projectivization.mk ℝ (v t) (hvne t))
  have hvContinuous : Continuous v := by
    dsimp [v]
    exact continuous_const.add (continuous_id.smul continuous_const)
  have hMContinuous : Continuous (fun t : ℝ =>
      projectiveLineParameterLinearMap L (v t)) :=
    (projectiveLineParameterLinearMap L).continuous_of_finiteDimensional.comp
      hvContinuous
  have hMne (t : ℝ) : projectiveLineParameterLinearMap L (v t) ≠ 0 := by
    simpa only [map_zero] using
      Function.Injective.ne (projectiveLineParameterLinearMap_injective L) (hvne t)
  have hgammaContinuous : Continuous gamma := by
    have hquotient : Continuous (fun t : ℝ =>
        Projectivization.mk ℝ (projectiveLineParameterLinearMap L (v t))
          (hMne t)) := by
      simpa only [Projectivization.mk'_eq_mk] using
        continuous_quotient_mk'.comp (hMContinuous.subtype_mk fun t => hMne t)
    simpa only [gamma, projectiveLineParameter, Projectivization.map_mk] using hquotient
  have hgamma0 : gamma 0 = p := by
    change projectiveLineParameter L
      (Projectivization.mk ℝ (v 0) (hvne 0)) = p
    have hv0 : v 0 = P.rep := by simp [v]
    have hmk0 : Projectivization.mk ℝ (v 0) (hvne 0) = P := by
      simpa only [hv0] using Projectivization.mk_rep P
    rw [hmk0]
    exact hP
  have hgamma_mem : Set.MapsTo gamma (Set.Ioi 0)
      {q : RealProjectivePoint | ProjectiveLineCyclic L p q r} := by
    intro t ht
    change ProjectiveLineCyclic L p
      (projectiveLineParameter L
        (Projectivization.mk ℝ (v t) (hvne t))) r
    refine ⟨P, Projectivization.mk ℝ (v t) (hvne t),
      Projectivization.mk ℝ D hDne, hP, rfl, ?_, ?_⟩
    · exact (congrArg (projectiveLineParameter L) hD).trans hR
    · have hpositive : 0 < realProjectiveTripleBracket P.rep (v t) D := by
        unfold realProjectiveTripleBracket
        rw [ddBracket_add_smul_right,
          realProjectiveBracket_self, zero_add]
        have hsecond : realProjectiveBracket (v t) D =
            realProjectiveBracket P.rep D := by
          simp [v, realProjectiveBracket]
          ring
        rw [hsecond, realProjectiveBracket_swap P.rep D]
        exact mul_pos
          (mul_pos_of_neg_of_neg (mul_neg_of_pos_of_neg ht hd) hd)
          (neg_pos.mpr hd)
      simpa only [Projectivization.mk_rep] using
        (realProjectiveCyclic_mk P.rep_nonzero (hvne t) hDne hpositive)
  rw [← hgamma0]
  apply map_mem_closure hgammaContinuous
  · rw [closure_Ioi]
    exact Set.self_mem_Ici
  · simpa only [hgamma0] using hgamma_mem

/-- The terminal endpoint is also a limit point of the same oriented open
cyclic arc.  The parametrization `t • P + D`, `t > 0`, approaches the
terminal representative `D` at `t = 0`. -/
theorem right_mem_closure_projectiveLineCyclicArc
    (L : RealProjectiveLine) (p r : RealProjectivePoint)
    (hp : p.orthogonal L) (hr : r.orthogonal L) (hpr : p ≠ r) :
    r ∈ closure
      {q : RealProjectivePoint | ProjectiveLineCyclic L p q r} := by
  classical
  let P : RealProjectiveOnePoint := projectiveLineParameterPreimage L p hp
  let R : RealProjectiveOnePoint := projectiveLineParameterPreimage L r hr
  have hP : projectiveLineParameter L P = p :=
    projectiveLineParameter_preimage_spec L p hp
  have hR : projectiveLineParameter L R = r :=
    projectiveLineParameter_preimage_spec L r hr
  have hPR : P ≠ R := by
    intro h
    apply hpr
    exact hP.symm.trans ((congrArg (projectiveLineParameter L) h).trans hR)
  let d₀ : ℝ := realProjectiveBracket P.rep R.rep
  have hd₀ : d₀ ≠ 0 := by
    intro hzero
    apply hPR
    calc
      P = Projectivization.mk ℝ P.rep P.rep_nonzero :=
        (Projectivization.mk_rep P).symm
      _ = Projectivization.mk ℝ R.rep R.rep_nonzero :=
        (realProjective_mk_eq_mk_iff_bracket_eq_zero
          P.rep_nonzero R.rep_nonzero).mpr hzero
      _ = R := Projectivization.mk_rep R
  let D : RealProjectiveLineVector := if 0 < d₀ then -R.rep else R.rep
  have hDne : D ≠ 0 := by
    dsimp [D]
    split_ifs
    · exact neg_ne_zero.mpr R.rep_nonzero
    · exact R.rep_nonzero
  have hd : realProjectiveBracket P.rep D < 0 := by
    dsimp [D]
    split_ifs with hdpos
    · rw [show realProjectiveBracket P.rep (-R.rep) = -d₀ by
        simp [d₀, realProjectiveBracket]
        ring]
      exact neg_neg_of_pos hdpos
    · exact lt_of_le_of_ne (le_of_not_gt hdpos) hd₀
  have hD : Projectivization.mk ℝ D hDne = R := by
    rw [← Projectivization.mk_rep R]
    apply (Projectivization.mk_eq_mk_iff' ℝ D R.rep
      hDne R.rep_nonzero).mpr
    dsimp [D]
    split_ifs
    · exact ⟨-1, by simp⟩
    · exact ⟨1, by simp⟩
  let w : ℝ → RealProjectiveLineVector := fun t => t • P.rep + D
  have hwne (t : ℝ) : w t ≠ 0 := by
    by_cases ht : t = 0
    · subst t
      simpa [w] using hDne
    · intro hzero
      have hbracket : realProjectiveBracket (w t) D = 0 := by
        rw [hzero]
        simp [realProjectiveBracket]
      simp only [w] at hbracket
      rw [ddBracket_smul_add_left,
        realProjectiveBracket_self, add_zero] at hbracket
      exact (mul_ne_zero ht (ne_of_lt hd)) hbracket
  let delta : ℝ → RealProjectivePoint := fun t =>
    projectiveLineParameter L (Projectivization.mk ℝ (w t) (hwne t))
  have hwContinuous : Continuous w := by
    dsimp [w]
    exact (continuous_id.smul continuous_const).add continuous_const
  have hMContinuous : Continuous (fun t : ℝ =>
      projectiveLineParameterLinearMap L (w t)) :=
    (projectiveLineParameterLinearMap L).continuous_of_finiteDimensional.comp
      hwContinuous
  have hMne (t : ℝ) : projectiveLineParameterLinearMap L (w t) ≠ 0 := by
    simpa only [map_zero] using
      Function.Injective.ne (projectiveLineParameterLinearMap_injective L) (hwne t)
  have hdeltaContinuous : Continuous delta := by
    have hquotient : Continuous (fun t : ℝ =>
        Projectivization.mk ℝ (projectiveLineParameterLinearMap L (w t))
          (hMne t)) := by
      simpa only [Projectivization.mk'_eq_mk] using
        continuous_quotient_mk'.comp (hMContinuous.subtype_mk fun t => hMne t)
    simpa only [delta, projectiveLineParameter, Projectivization.map_mk] using hquotient
  have hdelta0 : delta 0 = r := by
    change projectiveLineParameter L
      (Projectivization.mk ℝ (w 0) (hwne 0)) = r
    have hw0 : w 0 = D := by simp [w]
    have hmk0 : Projectivization.mk ℝ (w 0) (hwne 0) = R := by
      simpa only [hw0] using hD
    rw [hmk0]
    exact hR
  have hdelta_mem : Set.MapsTo delta (Set.Ioi 0)
      {q : RealProjectivePoint | ProjectiveLineCyclic L p q r} := by
    intro t ht
    change ProjectiveLineCyclic L p
      (projectiveLineParameter L
        (Projectivization.mk ℝ (w t) (hwne t))) r
    refine ⟨P, Projectivization.mk ℝ (w t) (hwne t),
      Projectivization.mk ℝ D hDne, hP, rfl, ?_, ?_⟩
    · exact (congrArg (projectiveLineParameter L) hD).trans hR
    · have hpositive : 0 < realProjectiveTripleBracket P.rep (w t) D := by
        unfold realProjectiveTripleBracket
        have hfirst : realProjectiveBracket P.rep (w t) =
            realProjectiveBracket P.rep D := by
          simp [w, realProjectiveBracket]
          ring
        rw [hfirst]
        simp only [w]
        rw [ddBracket_smul_add_left,
          realProjectiveBracket_self, add_zero,
          realProjectiveBracket_swap P.rep D]
        exact mul_pos
          (mul_pos_of_neg_of_neg hd (mul_neg_of_pos_of_neg ht hd))
          (neg_pos.mpr hd)
      simpa only [Projectivization.mk_rep] using
        (realProjectiveCyclic_mk P.rep_nonzero (hwne t) hDne hpositive)
  rw [← hdelta0]
  apply map_mem_closure hdeltaContinuous
  · rw [closure_Ioi]
    exact Set.self_mem_Ici
  · simpa only [hdelta0] using hdelta_mem

/-- The initial vertex of every genuine non-loop geometric edge is a limit
point of its open cyclic arc. -/
theorem geometricEdgeInitial_mem_closure_openArc
    (A : FiniteProjectiveLineArrangement Line) (hA : A.NonPencil)
    (e : A.GeometricEdge) :
    A.geometricEdgeInitial e ∈ closure (A.geometricEdgeOpenArc e) := by
  apply left_mem_closure_projectiveLineCyclicArc
  · exact A.geometricEdge_initial_incident e
  · exact A.geometricEdge_endpoint_incident e
  · exact A.geometricEdge_initial_ne_terminal_of_nonPencil hA e

/-- The terminal vertex is likewise a limit point of the same open edge. -/
theorem geometricEdgeTerminal_mem_closure_openArc
    (A : FiniteProjectiveLineArrangement Line) (hA : A.NonPencil)
    (e : A.GeometricEdge) :
    A.geometricEdgeTerminal e ∈ closure (A.geometricEdgeOpenArc e) := by
  apply right_mem_closure_projectiveLineCyclicArc
  · exact A.geometricEdge_initial_incident e
  · exact A.geometricEdge_endpoint_incident e
  · exact A.geometricEdge_initial_ne_terminal_of_nonPencil hA e

/-- Closure incidence with an open edge extends to its initial endpoint.
This is the first generic endpoint bridge needed both by the gallery `DD`
argument and by ordinary-line attachment bounds. -/
theorem geometricEdgeInitial_mem_closure_arrangementFaceCarrier_of_adjacent
    (A : FiniteProjectiveLineArrangement Line) (hA : A.NonPencil)
    (e : A.GeometricEdge) (F : A.ArrangementFace)
    (hF : A.geometricEdgeAdjacentFace e F) :
    A.geometricEdgeInitial e ∈ closure (A.arrangementFaceCarrier F) := by
  rcases hF with ⟨q, hq, hqF⟩
  have harc : A.geometricEdgeOpenArc e ⊆
      closure (A.arrangementFaceCarrier F) := by
    intro q' hq'
    exact A.mem_closure_arrangementFaceCarrier_of_mem_closure_of_geometricEdgeOpenArc
      hA e hq hq' F hqF
  exact closure_minimal harc isClosed_closure
    (A.geometricEdgeInitial_mem_closure_openArc hA e)

/-- Closure incidence with an open edge also extends to its terminal
endpoint. -/
theorem geometricEdgeTerminal_mem_closure_arrangementFaceCarrier_of_adjacent
    (A : FiniteProjectiveLineArrangement Line) (hA : A.NonPencil)
    (e : A.GeometricEdge) (F : A.ArrangementFace)
    (hF : A.geometricEdgeAdjacentFace e F) :
    A.geometricEdgeTerminal e ∈ closure (A.arrangementFaceCarrier F) := by
  rcases hF with ⟨q, hq, hqF⟩
  have harc : A.geometricEdgeOpenArc e ⊆
      closure (A.arrangementFaceCarrier F) := by
    intro q' hq'
    exact A.mem_closure_arrangementFaceCarrier_of_mem_closure_of_geometricEdgeOpenArc
      hA e hq hq' F hqF
  exact closure_minimal harc isClosed_closure
    (A.geometricEdgeTerminal_mem_closure_openArc hA e)

private theorem ddInv_mul_pos_iff_mul_pos (a b : ℝ) :
    0 < a⁻¹ * b ↔ 0 < a * b := by
  rw [show a⁻¹ * b = b / a by rw [div_eq_mul_inv, mul_comm],
    div_pos_iff, mul_pos_iff]
  constructor
  · rintro (h | h)
    · exact Or.inl ⟨h.2, h.1⟩
    · exact Or.inr ⟨h.2, h.1⟩
  · rintro (h | h)
    · exact Or.inl ⟨h.2, h.1⟩
    · exact Or.inr ⟨h.2, h.1⟩

private theorem ddInv_mul_neg_iff_mul_neg (a b : ℝ) :
    a⁻¹ * b < 0 ↔ a * b < 0 := by
  rw [show a⁻¹ * b = b / a by rw [div_eq_mul_inv, mul_comm],
    div_neg_iff, mul_neg_iff]
  constructor
  · rintro (h | h)
    · exact Or.inr ⟨h.2, h.1⟩
    · exact Or.inl ⟨h.2, h.1⟩
  · rintro (h | h)
    · exact Or.inr ⟨h.2, h.1⟩
    · exact Or.inl ⟨h.2, h.1⟩

/-- Normalize an arbitrary projective point in the affine chart selected by
`base`.  Unlike `arrangementNormalizedRepresentative`, the point may lie on
other arrangement lines. -/
noncomputable def arrangementPointNormalizedRepresentativeAt
    (A : FiniteProjectiveLineArrangement Line) (base : Line)
    (q : RealProjectivePoint) : Fin 3 → ℝ :=
  (projectiveLineEvaluation (A.projectiveLine base) q.rep)⁻¹ • q.rep

theorem projectiveLineEvaluation_arrangementPointNormalizedRepresentativeAt_base
    (A : FiniteProjectiveLineArrangement Line) (base : Line)
    (q : RealProjectivePoint) (hbase : ¬ A.Incident q base) :
    projectiveLineEvaluation (A.projectiveLine base)
      (A.arrangementPointNormalizedRepresentativeAt base q) = 1 := by
  have hne : projectiveLineEvaluation (A.projectiveLine base) q.rep ≠ 0 := by
    intro hzero
    exact hbase ((A.projectiveLineEvaluation_rep_eq_zero_iff_incident q base).mp hzero)
  simp [arrangementPointNormalizedRepresentativeAt, hne]

theorem arrangementPointNormalizedRepresentativeAt_ne_zero
    (A : FiniteProjectiveLineArrangement Line) (base : Line)
    (q : RealProjectivePoint) (hbase : ¬ A.Incident q base) :
    A.arrangementPointNormalizedRepresentativeAt base q ≠ 0 := by
  intro hzero
  have hvalue :=
    A.projectiveLineEvaluation_arrangementPointNormalizedRepresentativeAt_base
      base q hbase
  rw [hzero, LinearMap.map_zero] at hvalue
  norm_num at hvalue

theorem projectivization_mk_arrangementPointNormalizedRepresentativeAt
    (A : FiniteProjectiveLineArrangement Line) (base : Line)
    (q : RealProjectivePoint) (hbase : ¬ A.Incident q base) :
    Projectivization.mk ℝ (A.arrangementPointNormalizedRepresentativeAt base q)
      (A.arrangementPointNormalizedRepresentativeAt_ne_zero base q hbase) = q := by
  calc
    Projectivization.mk ℝ (A.arrangementPointNormalizedRepresentativeAt base q)
        (A.arrangementPointNormalizedRepresentativeAt_ne_zero base q hbase) =
        Projectivization.mk ℝ q.rep q.rep_nonzero := by
      apply (Projectivization.mk_eq_mk_iff' ℝ _ _ _ _).mpr
      exact ⟨(projectiveLineEvaluation (A.projectiveLine base) q.rep)⁻¹, rfl⟩
    _ = q := q.mk_rep

/-- A projective closure point, normalized in any chart not vanishing there,
lies in the literal closed homogeneous sign cone of the face.  This is the
reverse bridge complementary to
`projectivization_mem_closure_arrangementFaceCarrier_of_mem_closedSignCone`. -/
theorem arrangementPointNormalizedRepresentativeAt_mem_closedSignCone_of_mem_closure
    (A : FiniteProjectiveLineArrangement Line)
    (q : RealProjectivePoint) (base : Line) (F : A.ArrangementFace)
    (hbase : ¬ A.Incident q base)
    (hF : q ∈ closure (A.arrangementFaceCarrier F)) :
    A.arrangementPointNormalizedRepresentativeAt base q ∈
      A.arrangementClosedSignCone (A.arrangementFaceSignPattern base F) := by
  rw [A.mem_arrangementClosedSignCone_iff_orientedEvaluation_nonneg]
  intro m
  by_cases hqm : A.Incident q m
  · have hzRep : projectiveLineEvaluation (A.projectiveLine m) q.rep = 0 :=
      (A.projectiveLineEvaluation_rep_eq_zero_iff_incident q m).2 hqm
    have hz : projectiveLineEvaluation (A.projectiveLine m)
        (A.arrangementPointNormalizedRepresentativeAt base q) = 0 := by
      rw [arrangementPointNormalizedRepresentativeAt, LinearMap.map_smul,
        hzRep, smul_zero]
    by_cases hs : A.arrangementFaceSignPattern base F m <;>
      simp [arrangementOrientedEvaluation, hs, hz]
  · have hbaseEval :
        projectiveLineEvaluation (A.projectiveLine base) q.rep ≠ 0 := by
      intro hzero
      exact hbase
        ((A.projectiveLineEvaluation_rep_eq_zero_iff_incident q base).1 hzero)
    have hmEval : projectiveLineEvaluation (A.projectiveLine m) q.rep ≠ 0 := by
      intro hzero
      exact hqm
        ((A.projectiveLineEvaluation_rep_eq_zero_iff_incident q m).1 hzero)
    have hsign :=
      A.arrangementRelativeSign_arrangementFaceRepresentative_eq_of_mem_closure
        q base m F hbase hqm hF
    by_cases hpos : 0 <
        projectiveLineEvaluation (A.projectiveLine base) q.rep *
          projectiveLineEvaluation (A.projectiveLine m) q.rep
    · have hrelq : A.arrangementRelativeSign base m q = 1 := by
        rw [A.arrangementRelativeSign_apply_rep, sign_eq_one_iff]
        exact hpos
      have hrelF : A.arrangementRelativeSign base m
          (A.arrangementFaceRepresentative F).1 = 1 := hsign.trans hrelq
      have hsigma : A.arrangementFaceSignPattern base F m = true := by
        unfold arrangementFaceSignPattern
        rw [A.arrangementPointSignPattern_eq_relativeSign base
          (A.arrangementFaceRepresentative F)]
        simp [hrelF]
      simp only [arrangementOrientedEvaluation, hsigma, if_true]
      rw [arrangementPointNormalizedRepresentativeAt, LinearMap.map_smul]
      simpa only [smul_eq_mul] using
        (ddInv_mul_pos_iff_mul_pos
          (projectiveLineEvaluation (A.projectiveLine base) q.rep)
          (projectiveLineEvaluation (A.projectiveLine m) q.rep)).2 hpos |>.le
    · have hprodNe :
          projectiveLineEvaluation (A.projectiveLine base) q.rep *
            projectiveLineEvaluation (A.projectiveLine m) q.rep ≠ 0 :=
        mul_ne_zero hbaseEval hmEval
      have hneg :
          projectiveLineEvaluation (A.projectiveLine base) q.rep *
            projectiveLineEvaluation (A.projectiveLine m) q.rep < 0 :=
        lt_of_le_of_ne (le_of_not_gt hpos) hprodNe
      have hrelq : A.arrangementRelativeSign base m q = -1 := by
        rw [A.arrangementRelativeSign_apply_rep, sign_eq_neg_one_iff]
        exact hneg
      have hrelF : A.arrangementRelativeSign base m
          (A.arrangementFaceRepresentative F).1 = -1 := hsign.trans hrelq
      have hsigma : A.arrangementFaceSignPattern base F m = false := by
        unfold arrangementFaceSignPattern
        rw [A.arrangementPointSignPattern_eq_relativeSign base
          (A.arrangementFaceRepresentative F)]
        simp [hrelF]
      simp only [arrangementOrientedEvaluation, hsigma, if_false,
        ContinuousLinearMap.neg_apply]
      rw [arrangementPointNormalizedRepresentativeAt, LinearMap.map_smul]
      have hnormNeg :
          (projectiveLineEvaluation (A.projectiveLine base) q.rep)⁻¹ *
            projectiveLineEvaluation (A.projectiveLine m) q.rep < 0 :=
        (ddInv_mul_neg_iff_mul_neg _ _).2 hneg
      simpa [smul_eq_mul, mul_neg] using (neg_nonneg.mpr hnormNeg.le)

/-- At a closure point, every nonvanishing line inequality is in fact
strict after chart normalization. -/
theorem arrangementOrientedEvaluation_normalized_pos_of_mem_closure_of_not_incident
    (A : FiniteProjectiveLineArrangement Line)
    (q : RealProjectivePoint) (base : Line) (F : A.ArrangementFace)
    (hbase : ¬ A.Incident q base)
    (hF : q ∈ closure (A.arrangementFaceCarrier F))
    (m : Line) (hqm : ¬ A.Incident q m) :
    0 < A.arrangementOrientedEvaluation
      (A.arrangementFaceSignPattern base F) m
      (A.arrangementPointNormalizedRepresentativeAt base q) := by
  let v := A.arrangementPointNormalizedRepresentativeAt base q
  have hv :=
    A.arrangementPointNormalizedRepresentativeAt_mem_closedSignCone_of_mem_closure
      q base F hbase hF
  have hnonneg :=
    (A.mem_arrangementClosedSignCone_iff_orientedEvaluation_nonneg
      (A.arrangementFaceSignPattern base F) v).mp hv m
  have hne : A.arrangementOrientedEvaluation
      (A.arrangementFaceSignPattern base F) m v ≠ 0 := by
    intro hzero
    apply hqm
    rw [← A.projectivization_mk_arrangementPointNormalizedRepresentativeAt
      base q hbase]
    exact (A.incident_projectivization_mk_iff_orientedEvaluation_eq_zero
      (A.arrangementFaceSignPattern base F) m v
      (A.arrangementPointNormalizedRepresentativeAt_ne_zero base q hbase)).2 hzero
  exact lt_of_le_of_ne hnonneg (Ne.symm hne)

/-- Finitely many strict oriented inequalities remain strict under one
common sufficiently small linear perturbation. -/
theorem eventually_orientedEvaluation_pos_add_smul_except_two
    (A : FiniteProjectiveLineArrangement Line) (sigma : Line → Bool)
    (v d : Fin 3 → ℝ) (l a : Line)
    (hpos : ∀ m, m ≠ l → m ≠ a →
      0 < A.arrangementOrientedEvaluation sigma m v) :
    ∀ᶠ t in nhds (0 : ℝ), ∀ m, m ≠ l → m ≠ a →
      0 < A.arrangementOrientedEvaluation sigma m (v + t • d) := by
  apply Filter.eventually_all.2
  intro m
  by_cases hml : m = l
  · exact Filter.Eventually.of_forall fun _ hne => (hne hml).elim
  by_cases hma : m = a
  · exact Filter.Eventually.of_forall fun _ _ hne => (hne hma).elim
  have hcontinuous : Continuous (fun t : ℝ =>
      A.arrangementOrientedEvaluation sigma m (v + t • d)) :=
    (A.arrangementOrientedEvaluation sigma m).continuous_of_finiteDimensional.comp
      (continuous_const.add (continuous_id.smul continuous_const))
  have hzero : A.arrangementOrientedEvaluation sigma m (v + (0 : ℝ) • d) =
      A.arrangementOrientedEvaluation sigma m v := by simp
  have heventually : ∀ᶠ t in nhds (0 : ℝ),
      A.arrangementOrientedEvaluation sigma m (v + t • d) ∈ Set.Ioi 0 :=
    hcontinuous.continuousAt
      (isOpen_Ioi.mem_nhds (by simpa only [Set.mem_Ioi, hzero] using hpos m hml hma))
  exact heventually.mono fun t ht _ _ => ht

/-- Turning at an ordinary endpoint: if a face accumulates at a point whose
only supporting lines are `l` and `a`, then an actual open edge supported by
`a` also belongs to that face boundary.  This is the generic local extractor
shared by simplicial galleries and ordinary-line attachment arguments. -/
theorem exists_transverse_boundaryEdge_of_mem_closure_of_ordinary_intersection
    (A : FiniteProjectiveLineArrangement Line) (hA : A.NonPencil)
    (F : A.ArrangementFace) (q : RealProjectivePoint) (l a : Line)
    (hal : a ≠ l)
    (hql : A.Incident q l) (hqa : A.Incident q a)
    (hordinary : ∀ m : Line, A.Incident q m ↔ m = l ∨ m = a)
    (hF : q ∈ closure (A.arrangementFaceCarrier F)) :
    ∃ e : A.GeometricEdge,
      A.edgeSlotLine e = a ∧ e ∈ A.arrangementFaceBoundary F := by
  classical
  let base : Line := (A.exists_not_incident_line_of_nonPencil hA q).choose
  have hbase : ¬ A.Incident q base :=
    (A.exists_not_incident_line_of_nonPencil hA q).choose_spec
  let sigma := A.arrangementFaceSignPattern base F
  let v := A.arrangementPointNormalizedRepresentativeAt base q
  have hv0 : v ≠ 0 :=
    A.arrangementPointNormalizedRepresentativeAt_ne_zero base q hbase
  have hvProjective : Projectivization.mk ℝ v hv0 = q := by
    simpa only [v] using
      A.projectivization_mk_arrangementPointNormalizedRepresentativeAt
        base q hbase
  have hvCone : v ∈ A.arrangementClosedSignCone sigma := by
    simpa only [v, sigma] using
      A.arrangementPointNormalizedRepresentativeAt_mem_closedSignCone_of_mem_closure
        q base F hbase hF
  have hva : A.arrangementOrientedEvaluation sigma a v = 0 := by
    apply (A.incident_projectivization_mk_iff_orientedEvaluation_eq_zero
      sigma a v hv0).1
    rw [hvProjective]
    exact hqa
  have hvl : A.arrangementOrientedEvaluation sigma l v = 0 := by
    apply (A.incident_projectivization_mk_iff_orientedEvaluation_eq_zero
      sigma l v hv0).1
    rw [hvProjective]
    exact hql
  obtain ⟨w, hwa, hwl⟩ :=
    A.exists_orientedEvaluation_neg_on_kernel_of_ne sigma hal
  let d : Fin 3 → ℝ := -w
  have hda : A.arrangementOrientedEvaluation sigma a d = 0 := by
    simpa only [d, LinearMap.map_neg, hwa, neg_zero]
  have hdl : 0 < A.arrangementOrientedEvaluation sigma l d := by
    simpa only [d, LinearMap.map_neg] using neg_pos.mpr hwl
  have hstrict : ∀ m, m ≠ l → m ≠ a →
      0 < A.arrangementOrientedEvaluation sigma m v := by
    intro m hml hma
    apply A.arrangementOrientedEvaluation_normalized_pos_of_mem_closure_of_not_incident
      q base F hbase hF m
    intro hqm
    rcases (hordinary m).1 hqm with h | h
    · exact hml h
    · exact hma h
  have hstable :=
    A.eventually_orientedEvaluation_pos_add_smul_except_two
      sigma v d l a hstrict
  obtain ⟨eps, heps, hball⟩ := Metric.eventually_nhds_iff.mp hstable
  let t : ℝ := eps / 2
  have ht : 0 < t := by dsimp [t]; linarith
  have htSmall : dist t (0 : ℝ) < eps := by
    rw [Real.dist_0_eq_abs, abs_of_pos ht]
    dsimp [t]
    linarith
  have hstableT : ∀ m, m ≠ l → m ≠ a →
      0 < A.arrangementOrientedEvaluation sigma m (v + t • d) :=
    hball (y := t) htSmall
  let z : Fin 3 → ℝ := v + t • d
  have hza : A.arrangementOrientedEvaluation sigma a z = 0 := by
    simpa only [z, LinearMap.map_add, LinearMap.map_smul, hva, hda,
      smul_eq_mul, mul_zero, add_zero]
  have hzl : 0 < A.arrangementOrientedEvaluation sigma l z := by
    simpa only [z, LinearMap.map_add, LinearMap.map_smul, hvl,
      smul_eq_mul, zero_add] using mul_pos ht hdl
  have hzOther : ∀ m, m ≠ l → m ≠ a →
      0 < A.arrangementOrientedEvaluation sigma m z := by
    intro m hml hma
    exact hstableT m hml hma
  have hz0 : z ≠ 0 := by
    intro hzero
    have hzEval := congrArg (A.arrangementOrientedEvaluation sigma l) hzero
    rw [LinearMap.map_zero] at hzEval
    exact (ne_of_gt hzl) hzEval
  have hzCone : z ∈ A.arrangementClosedSignCone sigma := by
    rw [A.mem_arrangementClosedSignCone_iff_orientedEvaluation_nonneg]
    intro m
    by_cases hma : m = a
    · subst m
      exact hza.symm.le
    by_cases hml : m = l
    · subst m
      exact hzl.le
    exact (hzOther m hml hma).le
  let q' : RealProjectivePoint := Projectivization.mk ℝ z hz0
  have hq'Regular : ∀ m : Line, A.Incident q' m ↔ m = a := by
    intro m
    change A.Incident (Projectivization.mk ℝ z hz0) m ↔ m = a
    rw [A.incident_projectivization_mk_iff_orientedEvaluation_eq_zero
      sigma m z hz0]
    constructor
    · intro hmzero
      by_cases hma : m = a
      · exact hma
      by_cases hml : m = l
      · subst m
        exact (ne_of_gt hzl hmzero).elim
      · exact (ne_of_gt (hzOther m hml hma) hmzero).elim
    · intro hma
      subst m
      exact hza
  have hq'F : q' ∈ closure (A.arrangementFaceCarrier F) := by
    simpa only [q', sigma] using
      A.projectivization_mem_closure_arrangementFaceCarrier_of_mem_closedSignCone
        base F hz0 hzCone
  obtain ⟨g, hg, _hunique⟩ :=
    A.existsUnique_circularGap_mem_geometricEdgeOpenArc_of_regular
      hA q' a hq'Regular
  refine ⟨A.circularGapEdge a g, A.circularGapEdge_line a g, ?_⟩
  rw [A.mem_arrangementFaceBoundary_iff]
  exact ⟨q', hg, hq'F⟩

/-- Every member of a cardinality-minimal defining family for an actual
face is the support of a literal geometric boundary edge. -/
theorem exists_boundaryEdge_supported_by_cardMinimal_index
    (A : FiniteProjectiveLineArrangement Line) (hA : A.NonPencil)
    (base : Line) (F : A.ArrangementFace) (K : Finset Line)
    (hK : A.arrangementClosedSignConeOn
        (A.arrangementFaceSignPattern base F) K =
      A.arrangementClosedSignCone (A.arrangementFaceSignPattern base F))
    (hminimal : ∀ L : Finset Line,
      A.arrangementClosedSignConeOn
          (A.arrangementFaceSignPattern base F) L =
        A.arrangementClosedSignCone (A.arrangementFaceSignPattern base F) →
      K.card ≤ L.card)
    {l : Line} (hl : l ∈ K) :
    ∃ e : A.GeometricEdge,
      A.edgeSlotLine e = l ∧ e ∈ A.arrangementFaceBoundary F := by
  classical
  let sigma := A.arrangementFaceSignPattern base F
  let u := A.arrangementNormalizedRepresentative base
    (A.arrangementFaceRepresentative F)
  have hu : u ∈ A.arrangementSignCone sigma :=
    A.arrangementNormalizedRepresentative_mem_arrangementSignCone
      base (A.arrangementFaceRepresentative F)
  obtain ⟨v, hv0, hvCone, hvl, hvOther⟩ :=
    A.exists_exactOneZero_facetVector_of_cardMinimal
      hA sigma K hK hminimal hu hl
  let q : RealProjectivePoint := Projectivization.mk ℝ v hv0
  have hregular : ∀ m : Line, A.Incident q m ↔ m = l := by
    intro m
    change A.Incident (Projectivization.mk ℝ v hv0) m ↔ m = l
    rw [A.incident_projectivization_mk_iff_orientedEvaluation_eq_zero
      sigma m v hv0]
    constructor
    · intro hm
      by_contra hml
      exact (ne_of_gt (hvOther m hml)) hm
    · rintro rfl
      exact hvl
  obtain ⟨g, hg, _hunique⟩ :=
    A.existsUnique_circularGap_mem_geometricEdgeOpenArc_of_regular
      hA q l hregular
  refine ⟨A.circularGapEdge l g, A.circularGapEdge_line l g, ?_⟩
  rw [A.mem_arrangementFaceBoundary_iff]
  refine ⟨q, hg, ?_⟩
  change Projectivization.mk ℝ v hv0 ∈
    closure (A.arrangementFaceCarrier F)
  apply A.projectivization_mem_closure_arrangementFaceCarrier_of_mem_closedSignCone
    base F hv0
  simpa only [sigma] using hvCone

/-- The three literal edges of a three-sided face necessarily have three
different supporting arrangement lines. -/
theorem card_edgeSupport_of_exact_triangle_boundary
    (A : FiniteProjectiveLineArrangement Line) (hA : A.NonPencil)
    (base : Line) (F : A.ArrangementFace)
    (e0 e1 e2 : A.GeometricEdge)
    (hboundary : A.arrangementFaceBoundary F = {e0, e1, e2})
    (htri : (A.arrangementFaceBoundary F).card = 3) :
    ({A.edgeSlotLine e0, A.edgeSlotLine e1, A.edgeSlotLine e2} :
      Finset Line).card = 3 := by
  classical
  let sigma := A.arrangementFaceSignPattern base F
  obtain ⟨K, hK, hminimal⟩ :=
    A.exists_cardMinimal_arrangementClosedSignCone_indexSet sigma
  have hKsub : K ⊆
      {A.edgeSlotLine e0, A.edgeSlotLine e1, A.edgeSlotLine e2} := by
    intro k hk
    obtain ⟨e, heLine, heMem⟩ :=
      A.exists_boundaryEdge_supported_by_cardMinimal_index
        hA base F K hK hminimal hk
    rw [hboundary] at heMem
    simp only [Finset.mem_insert, Finset.mem_singleton] at heMem ⊢
    rcases heMem with rfl | rfl | rfl
    · exact Or.inl heLine.symm
    · exact Or.inr (Or.inl heLine.symm)
    · exact Or.inr (Or.inr heLine.symm)
  have hthree : 3 ≤ K.card :=
    A.three_le_card_of_arrangementClosedSignConeOn_eq hA sigma K hK
  have hle := Finset.card_le_card hKsub
  have hupper :
      ({A.edgeSlotLine e0, A.edgeSlotLine e1, A.edgeSlotLine e2} :
        Finset Line).card ≤ 3 := by
    calc
      ({A.edgeSlotLine e0, A.edgeSlotLine e1, A.edgeSlotLine e2} :
          Finset Line).card ≤
          ({A.edgeSlotLine e1, A.edgeSlotLine e2} : Finset Line).card + 1 :=
        Finset.card_insert_le _ _
      _ ≤ ({A.edgeSlotLine e2} : Finset Line).card + 1 + 1 := by
        exact Nat.add_le_add_right (Finset.card_insert_le _ _) 1
      _ = 3 := by simp
  omega

theorem edgeSupport_pairwise_ne_of_exact_triangle_boundary
    (A : FiniteProjectiveLineArrangement Line) (hA : A.NonPencil)
    (base : Line) (F : A.ArrangementFace)
    (e0 e1 e2 : A.GeometricEdge)
    (hboundary : A.arrangementFaceBoundary F = {e0, e1, e2})
    (htri : (A.arrangementFaceBoundary F).card = 3) :
    A.edgeSlotLine e0 ≠ A.edgeSlotLine e1 ∧
      A.edgeSlotLine e0 ≠ A.edgeSlotLine e2 ∧
      A.edgeSlotLine e1 ≠ A.edgeSlotLine e2 := by
  have hcard := A.card_edgeSupport_of_exact_triangle_boundary
    hA base F e0 e1 e2 hboundary htri
  constructor
  · intro h
    have hle :
        ({A.edgeSlotLine e0, A.edgeSlotLine e1, A.edgeSlotLine e2} :
          Finset Line).card ≤ 2 := by
      rw [h]
      simpa using Finset.card_insert_le (A.edgeSlotLine e1)
        ({A.edgeSlotLine e2} : Finset Line)
    omega
  constructor
  · intro h
    have hle :
        ({A.edgeSlotLine e0, A.edgeSlotLine e1, A.edgeSlotLine e2} :
          Finset Line).card ≤ 2 := by
      simpa [h] using
        (Finset.card_le_two (a := A.edgeSlotLine e1)
          (b := A.edgeSlotLine e2))
    omega
  · intro h
    have hle :
        ({A.edgeSlotLine e0, A.edgeSlotLine e1, A.edgeSlotLine e2} :
          Finset Line).card ≤ 2 := by
      rw [h]
      simpa using Finset.card_insert_le (A.edgeSlotLine e0)
        ({A.edgeSlotLine e2} : Finset Line)
    omega

/-- The literal third member of a three-element finite set after two
different members have been fixed. -/
theorem exists_third_of_card_eq_three
    {X : Type*} [DecidableEq X] (S : Finset X) (x y : X)
    (hx : x ∈ S) (hy : y ∈ S) (hxy : x ≠ y)
    (hcard : S.card = 3) :
    ∃ z : X, z ≠ x ∧ z ≠ y ∧ S = {x, y, z} := by
  have hyErase : y ∈ S.erase x := Finset.mem_erase.mpr ⟨hxy.symm, hy⟩
  have hEraseX : (S.erase x).card = 2 := by
    rw [Finset.card_erase_of_mem hx, hcard]
  have hEraseXY : ((S.erase x).erase y).card = 1 := by
    rw [Finset.card_erase_of_mem hyErase, hEraseX]
  obtain ⟨z, hz⟩ := Finset.card_eq_one.mp hEraseXY
  have hzErase : z ∈ (S.erase x).erase y := by
    rw [hz]
    simp
  have hzY := (Finset.mem_erase.mp hzErase).1
  have hzEraseX := (Finset.mem_erase.mp hzErase).2
  have hzX := (Finset.mem_erase.mp hzEraseX).1
  have hzS := (Finset.mem_erase.mp hzEraseX).2
  refine ⟨z, hzX, hzY, ?_⟩
  symm
  apply Finset.eq_of_subset_of_card_le
  · intro w hw
    simp only [Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with rfl | rfl | rfl
    · exact hx
    · exact hy
    · exact hzS
  · have htriple : ({x, y, z} : Finset X).card = 3 := by
      simp [hxy, hzX, hzY, Ne.symm hzX, Ne.symm hzY]
    rw [hcard, htriple]

/-- At an ordinary vertex in the closure of a triangular face, a named
boundary edge on one support determines a boundary edge on the transverse
support and a unique third boundary support. -/
theorem exists_exact_triangle_boundary_at_ordinary_vertex
    (A : FiniteProjectiveLineArrangement Line) (hA : A.NonPencil)
    (F : A.ArrangementFace) (e : A.GeometricEdge)
    (q : RealProjectivePoint) (l a : Line)
    (he : A.edgeSlotLine e = l) (hal : a ≠ l)
    (hql : A.Incident q l) (hqa : A.Incident q a)
    (hordinary : ∀ m : Line, A.Incident q m ↔ m = l ∨ m = a)
    (hqF : q ∈ closure (A.arrangementFaceCarrier F))
    (heF : e ∈ A.arrangementFaceBoundary F)
    (htri : (A.arrangementFaceBoundary F).card = 3) :
    ∃ eA eX : A.GeometricEdge,
      A.edgeSlotLine eA = a ∧
      A.arrangementFaceBoundary F = {e, eA, eX} ∧
      A.edgeSlotLine eX ≠ l ∧ A.edgeSlotLine eX ≠ a := by
  classical
  obtain ⟨eA, heA, heAF⟩ :=
    A.exists_transverse_boundaryEdge_of_mem_closure_of_ordinary_intersection
      hA F q l a hal hql hqa hordinary hqF
  have heAne : eA ≠ e := by
    intro h
    apply hal
    calc
      a = A.edgeSlotLine eA := heA.symm
      _ = A.edgeSlotLine e := congrArg A.edgeSlotLine h
      _ = l := he
  obtain ⟨eX, heXne, heXAne, hboundary⟩ :=
    exists_third_of_card_eq_three (A.arrangementFaceBoundary F) e eA
      heF heAF heAne.symm htri
  have hlines := A.edgeSupport_pairwise_ne_of_exact_triangle_boundary
    hA a F e eA eX hboundary htri
  refine ⟨eA, eX, heA, hboundary, ?_, ?_⟩
  · intro hXl
    apply hlines.2.1
    rw [he, hXl]
  · intro hXa
    apply hlines.2.2
    rw [heA, hXa]

/-- If a face has precisely three boundary edges on three distinct supports,
then those three oriented inequalities already define its full closed sign
cone.  This converts the literal triangular boundary into the affine-sector
description needed by straight-line crossing arguments. -/
theorem arrangementClosedSignConeOn_eq_of_exact_triangle_boundary
    (A : FiniteProjectiveLineArrangement Line) (hA : A.NonPencil)
    (base : Line) (F : A.ArrangementFace)
    (e0 e1 e2 : A.GeometricEdge) (l a b : Line)
    (hboundary : A.arrangementFaceBoundary F = {e0, e1, e2})
    (he0 : A.edgeSlotLine e0 = l)
    (he1 : A.edgeSlotLine e1 = a)
    (he2 : A.edgeSlotLine e2 = b)
    (hal : a ≠ l) (hbl : b ≠ l) (hab : a ≠ b) :
    A.arrangementClosedSignConeOn
        (A.arrangementFaceSignPattern base F) {l, a, b} =
      A.arrangementClosedSignCone (A.arrangementFaceSignPattern base F) := by
  classical
  let sigma := A.arrangementFaceSignPattern base F
  obtain ⟨K, hK, hminimal⟩ :=
    A.exists_cardMinimal_arrangementClosedSignCone_indexSet sigma
  have hKsub : K ⊆ {l, a, b} := by
    intro k hk
    obtain ⟨e, heLine, heMem⟩ :=
      A.exists_boundaryEdge_supported_by_cardMinimal_index
        hA base F K hK hminimal hk
    rw [hboundary] at heMem
    simp only [Finset.mem_insert, Finset.mem_singleton] at heMem ⊢
    rcases heMem with he | he | he
    · left
      calc
        k = A.edgeSlotLine e := heLine.symm
        _ = A.edgeSlotLine e0 := congrArg A.edgeSlotLine he
        _ = l := he0
    · right; left
      calc
        k = A.edgeSlotLine e := heLine.symm
        _ = A.edgeSlotLine e1 := congrArg A.edgeSlotLine he
        _ = a := he1
    · right; right
      calc
        k = A.edgeSlotLine e := heLine.symm
        _ = A.edgeSlotLine e2 := congrArg A.edgeSlotLine he
        _ = b := he2
  have hthree : 3 ≤ K.card :=
    A.three_le_card_of_arrangementClosedSignConeOn_eq hA sigma K hK
  have hsupportCard : ({l, a, b} : Finset Line).card = 3 := by
    simp [hal, hbl, hab, Ne.symm hal, Ne.symm hbl]
  have hKeq : K = {l, a, b} := by
    apply Finset.eq_of_subset_of_card_le hKsub
    rw [hsupportCard]
    exact hthree
  rw [← hKeq]
  simpa only [sigma] using hK

/-- Endpoint reader for an exact triangular face.  A genuine arrangement
vertex in the face closure which lies on one triangle support but misses a
second one must lie on the third support. -/
theorem incident_third_support_of_vertex_mem_closure_exact_triangle
    (A : FiniteProjectiveLineArrangement Line) (hA : A.NonPencil)
    (F : A.ArrangementFace) (e0 e1 e2 : A.GeometricEdge)
    (l a b : Line) (q : RealProjectivePoint)
    (hboundary : A.arrangementFaceBoundary F = {e0, e1, e2})
    (he0 : A.edgeSlotLine e0 = l)
    (he1 : A.edgeSlotLine e1 = a)
    (he2 : A.edgeSlotLine e2 = b)
    (hal : a ≠ l) (hbl : b ≠ l) (hab : a ≠ b)
    (hqVertex : q ∈ A.vertexSet)
    (hqF : q ∈ closure (A.arrangementFaceCarrier F))
    (hql : A.Incident q l) (hqa : ¬ A.Incident q a) :
    A.Incident q b := by
  classical
  by_contra hqb
  let base : Line := (A.exists_not_incident_line_of_nonPencil hA q).choose
  have hbase : ¬ A.Incident q base :=
    (A.exists_not_incident_line_of_nonPencil hA q).choose_spec
  let sigma := A.arrangementFaceSignPattern base F
  let v := A.arrangementPointNormalizedRepresentativeAt base q
  have hv0 : v ≠ 0 :=
    A.arrangementPointNormalizedRepresentativeAt_ne_zero base q hbase
  have hvProjective : Projectivization.mk ℝ v hv0 = q := by
    simpa only [v] using
      A.projectivization_mk_arrangementPointNormalizedRepresentativeAt
        base q hbase
  have hvFull : v ∈ A.arrangementClosedSignCone sigma := by
    simpa only [v, sigma] using
      A.arrangementPointNormalizedRepresentativeAt_mem_closedSignCone_of_mem_closure
        q base F hbase hqF
  have hvl : A.arrangementOrientedEvaluation sigma l v = 0 := by
    apply (A.incident_projectivization_mk_iff_orientedEvaluation_eq_zero
      sigma l v hv0).1
    rw [hvProjective]
    exact hql
  have hva : 0 < A.arrangementOrientedEvaluation sigma a v :=
    A.arrangementOrientedEvaluation_normalized_pos_of_mem_closure_of_not_incident
      q base F hbase hqF a hqa
  have hvb : 0 < A.arrangementOrientedEvaluation sigma b v :=
    A.arrangementOrientedEvaluation_normalized_pos_of_mem_closure_of_not_incident
      q base F hbase hqF b hqb
  have hcone :=
    A.arrangementClosedSignConeOn_eq_of_exact_triangle_boundary
      hA base F e0 e1 e2 l a b hboundary he0 he1 he2 hal hbl hab
  have hother : ∀ m, m ≠ l →
      0 < A.arrangementOrientedEvaluation sigma m v := by
    apply A.strict_orientedEvaluation_of_facetVector
      sigma {l, a, b} hcone (by simp) hvFull hvl
    intro k hk hkl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hk
    rcases hk with rfl | rfl | rfl
    · exact (hkl rfl).elim
    · exact hva
    · exact hvb
  have hregular : ∀ m : Line, A.Incident q m ↔ m = l := by
    intro m
    constructor
    · intro hqm
      by_contra hml
      have hmzero : A.arrangementOrientedEvaluation sigma m v = 0 := by
        apply (A.incident_projectivization_mk_iff_orientedEvaluation_eq_zero
          sigma m v hv0).1
        rw [hvProjective]
        exact hqm
      exact (ne_of_gt (hother m hml)) hmzero
    · rintro rfl
      exact hql
  obtain ⟨m, n, hmn, hintersection⟩ :=
    A.exists_lines_of_mem_vertexSet hqVertex
  have hqm : A.Incident q m := by
    rw [← hintersection]
    exact A.intersection_incident_left hmn
  have hqn : A.Incident q n := by
    rw [← hintersection]
    exact A.intersection_incident_right hmn
  exact hmn (((hregular m).mp hqm).trans ((hregular n).mp hqn).symm)

/-- The endpoints of one boundary edge of an exact triangular face are the
two pairwise intersections of its support with the other two supports. -/
theorem geometricEdge_endpoint_pair_eq_of_exact_triangle_boundary
    (A : FiniteProjectiveLineArrangement Line) (hA : A.NonPencil)
    (F : A.ArrangementFace) (e0 e1 e2 : A.GeometricEdge)
    (l a b : Line)
    (hboundary : A.arrangementFaceBoundary F = {e0, e1, e2})
    (he0 : A.edgeSlotLine e0 = l)
    (he1 : A.edgeSlotLine e1 = a)
    (he2 : A.edgeSlotLine e2 = b)
    (hal : a ≠ l) (hbl : b ≠ l) (hab : a ≠ b) :
    ({A.geometricEdgeInitial e0, A.geometricEdgeTerminal e0} :
        Finset RealProjectivePoint) =
      {A.intersection l a, A.intersection l b} := by
  classical
  have he0F : e0 ∈ A.arrangementFaceBoundary F := by
    rw [hboundary]
    simp
  have hF : A.geometricEdgeAdjacentFace e0 F :=
    (A.mem_arrangementFaceBoundary_iff F e0).1 he0F
  have hclassify (q : RealProjectivePoint)
      (hqVertex : q ∈ A.vertexSet)
      (hqF : q ∈ closure (A.arrangementFaceCarrier F))
      (hql : A.Incident q l) :
      q = A.intersection l a ∨ q = A.intersection l b := by
    by_cases hqa : A.Incident q a
    · exact Or.inl (A.eq_intersection_of_incident hal.symm hql hqa)
    · right
      have hqb :=
        A.incident_third_support_of_vertex_mem_closure_exact_triangle
          hA F e0 e1 e2 l a b q hboundary he0 he1 he2
            hal hbl hab hqVertex hqF hql hqa
      exact A.eq_intersection_of_incident hbl.symm hql hqb
  have hinitial := hclassify (A.geometricEdgeInitial e0)
    (A.geometricEdge_initial_mem_vertexSet e0)
    (A.geometricEdgeInitial_mem_closure_arrangementFaceCarrier_of_adjacent
      hA e0 F hF)
    (by simpa only [he0] using A.geometricEdge_initial_incident e0)
  have hterminal := hclassify (A.geometricEdgeTerminal e0)
    (A.geometricEdge_terminal_mem_vertexSet e0)
    (A.geometricEdgeTerminal_mem_closure_arrangementFaceCarrier_of_adjacent
      hA e0 F hF)
    (by simpa only [he0] using A.geometricEdge_endpoint_incident e0)
  apply Finset.eq_of_subset_of_card_le
  · intro q hq
    simp only [Finset.mem_insert, Finset.mem_singleton] at hq ⊢
    rcases hq with rfl | rfl
    · exact hinitial
    · exact hterminal
  · rw [Finset.card_pair
      (A.geometricEdge_initial_ne_terminal_of_nonPencil hA e0)]
    exact Finset.card_le_two

/-- One oriented ray from an ordinary intersection in a triangular
arrangement has an actual opposite endpoint supported by the third side of
each adjacent triangle. -/
theorem exists_terminal_support_of_triangle_at_ordinary_initial
    (A : FiniteProjectiveLineArrangement Line) (hA : A.NonPencil)
    (F : A.ArrangementFace) (e : A.GeometricEdge) (c ell : Line)
    (he : A.edgeSlotLine e = c) (hellc : ell ≠ c)
    (hinitial : ∀ m : Line,
      A.Incident (A.geometricEdgeInitial e) m ↔ m = c ∨ m = ell)
    (hF : A.geometricEdgeAdjacentFace e F)
    (htri : (A.arrangementFaceBoundary F).card = 3) :
    ∃ eEll eX : A.GeometricEdge,
      A.edgeSlotLine eEll = ell ∧
      A.arrangementFaceBoundary F = {e, eEll, eX} ∧
      A.edgeSlotLine eX ≠ c ∧ A.edgeSlotLine eX ≠ ell ∧
      A.Incident (A.geometricEdgeTerminal e) (A.edgeSlotLine eX) := by
  have hqF : A.geometricEdgeInitial e ∈
      closure (A.arrangementFaceCarrier F) :=
    A.geometricEdgeInitial_mem_closure_arrangementFaceCarrier_of_adjacent
      hA e F hF
  have heF : e ∈ A.arrangementFaceBoundary F :=
    (A.mem_arrangementFaceBoundary_iff F e).2 hF
  have hqc : A.Incident (A.geometricEdgeInitial e) c :=
    (hinitial c).2 (Or.inl rfl)
  have hqell : A.Incident (A.geometricEdgeInitial e) ell :=
    (hinitial ell).2 (Or.inr rfl)
  obtain ⟨eEll, eX, heEll, hboundary, heXc, heXell⟩ :=
    A.exists_exact_triangle_boundary_at_ordinary_vertex
      hA F e (A.geometricEdgeInitial e) c ell he hellc hqc hqell
        hinitial hqF heF htri
  have hpairs := A.geometricEdge_endpoint_pair_eq_of_exact_triangle_boundary
    hA F e eEll eX c ell (A.edgeSlotLine eX) hboundary
      he heEll rfl hellc heXc heXell.symm
  have hinitialEq : A.geometricEdgeInitial e = A.intersection c ell :=
    A.eq_intersection_of_incident hellc.symm hqc hqell
  have hterminalMem : A.geometricEdgeTerminal e ∈
      ({A.intersection c ell, A.intersection c (A.edgeSlotLine eX)} :
        Finset RealProjectivePoint) := by
    rw [← hpairs]
    simp
  have hterminalEq : A.geometricEdgeTerminal e =
      A.intersection c (A.edgeSlotLine eX) := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hterminalMem
    rcases hterminalMem with hbad | hgood
    · exfalso
      apply A.geometricEdge_initial_ne_terminal_of_nonPencil hA e
      rw [hinitialEq, hbad]
    · exact hgood
  have hterminalX :
      A.Incident (A.geometricEdgeTerminal e) (A.edgeSlotLine eX) := by
    rw [hterminalEq]
    exact A.intersection_incident_right heXc.symm
  exact ⟨eEll, eX, heEll, hboundary, heXc, heXell, hterminalX⟩

/-- Incoming-ray version of `exists_terminal_support...`. -/
theorem exists_initial_support_of_triangle_at_ordinary_terminal
    (A : FiniteProjectiveLineArrangement Line) (hA : A.NonPencil)
    (F : A.ArrangementFace) (e : A.GeometricEdge) (c ell : Line)
    (he : A.edgeSlotLine e = c) (hellc : ell ≠ c)
    (hterminal : ∀ m : Line,
      A.Incident (A.geometricEdgeTerminal e) m ↔ m = c ∨ m = ell)
    (hF : A.geometricEdgeAdjacentFace e F)
    (htri : (A.arrangementFaceBoundary F).card = 3) :
    ∃ eEll eX : A.GeometricEdge,
      A.edgeSlotLine eEll = ell ∧
      A.arrangementFaceBoundary F = {e, eEll, eX} ∧
      A.edgeSlotLine eX ≠ c ∧ A.edgeSlotLine eX ≠ ell ∧
      A.Incident (A.geometricEdgeInitial e) (A.edgeSlotLine eX) := by
  have hqF : A.geometricEdgeTerminal e ∈
      closure (A.arrangementFaceCarrier F) :=
    A.geometricEdgeTerminal_mem_closure_arrangementFaceCarrier_of_adjacent
      hA e F hF
  have heF : e ∈ A.arrangementFaceBoundary F :=
    (A.mem_arrangementFaceBoundary_iff F e).2 hF
  have hqc : A.Incident (A.geometricEdgeTerminal e) c :=
    (hterminal c).2 (Or.inl rfl)
  have hqell : A.Incident (A.geometricEdgeTerminal e) ell :=
    (hterminal ell).2 (Or.inr rfl)
  obtain ⟨eEll, eX, heEll, hboundary, heXc, heXell⟩ :=
    A.exists_exact_triangle_boundary_at_ordinary_vertex
      hA F e (A.geometricEdgeTerminal e) c ell he hellc hqc hqell
        hterminal hqF heF htri
  have hpairs := A.geometricEdge_endpoint_pair_eq_of_exact_triangle_boundary
    hA F e eEll eX c ell (A.edgeSlotLine eX) hboundary
      he heEll rfl hellc heXc heXell.symm
  have hterminalEq : A.geometricEdgeTerminal e = A.intersection c ell :=
    A.eq_intersection_of_incident hellc.symm hqc hqell
  have hinitialMem : A.geometricEdgeInitial e ∈
      ({A.intersection c ell, A.intersection c (A.edgeSlotLine eX)} :
        Finset RealProjectivePoint) := by
    rw [← hpairs]
    simp
  have hinitialEq : A.geometricEdgeInitial e =
      A.intersection c (A.edgeSlotLine eX) := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hinitialMem
    rcases hinitialMem with hbad | hgood
    · exfalso
      apply A.geometricEdge_initial_ne_terminal_of_nonPencil hA e
      rw [hbad, hterminalEq]
    · exact hgood
  have hinitialX :
      A.Incident (A.geometricEdgeInitial e) (A.edgeSlotLine eX) := by
    rw [hinitialEq]
    exact A.intersection_incident_right heXc.symm
  exact ⟨eEll, eX, heEll, hboundary, heXc, heXell, hinitialX⟩

/-- The third support extracted from a triangular face at the marked vertex
`d` meets `ell` at one of the two cyclic neighbours of `d`. -/
theorem triangle_third_support_meets_ell_at_neighbor
    (A : FiniteProjectiveLineArrangement Line) (hA : A.NonPencil)
    (ell : Line) (d : A.CircularGapSlot ell)
    (F : A.ArrangementFace) (e eEll eX : A.GeometricEdge) (c : Line)
    (hellc : ell ≠ c)
    (hdc : A.Incident d.1 c)
    (hdordinary : ∀ m : Line, A.Incident d.1 m ↔ m = c ∨ m = ell)
    (hboundary : A.arrangementFaceBoundary F = {e, eEll, eX})
    (he : A.edgeSlotLine e = c)
    (heEll : A.edgeSlotLine eEll = ell)
    (heXc : A.edgeSlotLine eX ≠ c)
    (heXell : A.edgeSlotLine eX ≠ ell) :
    A.intersection ell (A.edgeSlotLine eX) =
        (A.circularGapPredecessor ell d).1 ∨
      A.intersection ell (A.edgeSlotLine eX) =
        (A.circularGapSuccessor ell d).1 := by
  have hboundary' : A.arrangementFaceBoundary F = {eEll, e, eX} := by
    simpa [Finset.insert_comm] using hboundary
  have hpairs := A.geometricEdge_endpoint_pair_eq_of_exact_triangle_boundary
    hA F eEll e eX ell c (A.edgeSlotLine eX) hboundary'
      heEll he rfl hellc.symm heXell heXc.symm
  have hdEll : A.Incident d.1 ell := ((A.mem_lineVertexSet ell).1 d.2).2
  have hdEq : d.1 = A.intersection ell c :=
    A.eq_intersection_of_incident hellc hdEll hdc
  have hdX : d.1 ≠ A.intersection ell (A.edgeSlotLine eX) := by
    intro h
    have hdx : A.Incident d.1 (A.edgeSlotLine eX) := by
      rw [h]
      exact A.intersection_incident_right heXell.symm
    rcases (hdordinary (A.edgeSlotLine eX)).1 hdx with hxc | hxe
    · exact heXc hxc
    · exact heXell hxe
  apply A.other_endpoint_eq_predecessor_or_successor ell d eEll
    (A.intersection ell (A.edgeSlotLine eX)) heEll
  · simpa only [hdEq] using hpairs
  · exact hdX

/-- Private sector core, placed before the ray extractors that use it. -/
private theorem incident_intersection_of_two_exact_opposite_triangles_core
    (A : FiniteProjectiveLineArrangement Line) (hA : A.NonPencil)
    (e eP eQ eP' eQ' : A.GeometricEdge)
    (l a b m : Line) (F G : A.ArrangementFace)
    (he : A.edgeSlotLine e = l)
    (heP : A.edgeSlotLine eP = a) (heQ : A.edgeSlotLine eQ = b)
    (heP' : A.edgeSlotLine eP' = a) (heQ' : A.edgeSlotLine eQ' = b)
    (hal : a ≠ l) (hbl : b ≠ l) (hab : a ≠ b)
    (hF : A.geometricEdgeAdjacentFace e F)
    (hG : A.geometricEdgeAdjacentFace e G) (hFG : F ≠ G)
    (hboundaryF : A.arrangementFaceBoundary F = {e, eP, eQ})
    (hboundaryG : A.arrangementFaceBoundary G = {e, eP', eQ'})
    (hml : m ≠ l) :
    A.Incident (A.intersection a b) m := by
  classical
  obtain ⟨q, hq⟩ := (A.isPathConnected_geometricEdgeOpenArc hA e).nonempty
  have hregular : ∀ k : Line, A.Incident q k ↔ k = l := by
    intro k
    simpa only [he] using A.geometricEdgeOpenArc_incident_iff e hq k
  have hqF : q ∈ closure (A.arrangementFaceCarrier F) := by
    rcases hF with ⟨qF, hqFarc, hqFclosure⟩
    exact A.mem_closure_arrangementFaceCarrier_of_mem_closure_of_geometricEdgeOpenArc
      hA e hqFarc hq F hqFclosure
  have hqG : q ∈ closure (A.arrangementFaceCarrier G) := by
    rcases hG with ⟨qG, hqGarc, hqGclosure⟩
    exact A.mem_closure_arrangementFaceCarrier_of_mem_closure_of_geometricEdgeOpenArc
      hA e hqGarc hq G hqGclosure
  let sigmaF := A.arrangementFaceSignPattern a F
  let sigmaG := A.arrangementFaceSignPattern a G
  have hsigmaTrans : ∀ k : Line, k ≠ l → sigmaF k = sigmaG k := by
    intro k hkl
    have hqa : ¬ A.Incident q a := by
      intro h
      exact hal ((hregular a).mp h)
    have hqk : ¬ A.Incident q k := by
      intro h
      exact hkl ((hregular k).mp h)
    have hrelF :=
      A.arrangementRelativeSign_arrangementFaceRepresentative_eq_of_mem_closure
        q a k F hqa hqk hqF
    have hrelG :=
      A.arrangementRelativeSign_arrangementFaceRepresentative_eq_of_mem_closure
        q a k G hqa hqk hqG
    dsimp only [sigmaF, sigmaG, arrangementFaceSignPattern]
    rw [A.arrangementPointSignPattern_eq_relativeSign a
        (A.arrangementFaceRepresentative F),
      A.arrangementPointSignPattern_eq_relativeSign a
        (A.arrangementFaceRepresentative G)]
    apply Bool.decide_congr
    rw [hrelF, hrelG]
  have hsigmaNe : sigmaF ≠ sigmaG := by
    intro h
    apply hFG
    exact A.arrangementFaceSignPattern_injective a h
  have hsigmaL : sigmaF l ≠ sigmaG l := by
    intro hl
    apply hsigmaNe
    funext k
    by_cases hkl : k = l
    · simpa only [hkl] using hl
    · exact hsigmaTrans k hkl
  have hEvalTrans : ∀ k : Line, k ≠ l →
      A.arrangementOrientedEvaluation sigmaG k =
        A.arrangementOrientedEvaluation sigmaF k := by
    intro k hkl
    unfold arrangementOrientedEvaluation
    rw [hsigmaTrans k hkl]
  have hEvalLOpp : A.arrangementOrientedEvaluation sigmaG l =
      -A.arrangementOrientedEvaluation sigmaF l := by
    unfold arrangementOrientedEvaluation
    cases hFbit : sigmaF l <;> cases hGbit : sigmaG l <;> simp_all
  have hconeF :=
    A.arrangementClosedSignConeOn_eq_of_exact_triangle_boundary
      hA a F e eP eQ l a b hboundaryF he heP heQ hal hbl hab
  have hconeG :=
    A.arrangementClosedSignConeOn_eq_of_exact_triangle_boundary
      hA a G e eP' eQ' l a b hboundaryG he heP' heQ' hal hbl hab
  have hmNonneg : ∀ v : Fin 3 → ℝ,
      0 ≤ A.arrangementOrientedEvaluation sigmaF a v →
      0 ≤ A.arrangementOrientedEvaluation sigmaF b v →
      0 ≤ A.arrangementOrientedEvaluation sigmaF m v := by
    intro v hva hvb
    by_cases hvl : 0 ≤ A.arrangementOrientedEvaluation sigmaF l v
    · have hvOn : v ∈ A.arrangementClosedSignConeOn sigmaF {l, a, b} := by
        rw [A.mem_arrangementClosedSignConeOn]
        intro k hk
        simp only [Finset.mem_insert, Finset.mem_singleton] at hk
        rcases hk with rfl | rfl | rfl
        · exact hvl
        · exact hva
        · exact hvb
      have hvFull : v ∈ A.arrangementClosedSignCone sigmaF := by
        rw [← hconeF]
        exact hvOn
      exact (A.mem_arrangementClosedSignCone_iff_orientedEvaluation_nonneg
        sigmaF v).mp hvFull m
    · have hvlG : 0 ≤ A.arrangementOrientedEvaluation sigmaG l v := by
        rw [hEvalLOpp, LinearMap.neg_apply]
        exact neg_nonneg.mpr (le_of_lt (lt_of_not_ge hvl))
      have hvOn : v ∈ A.arrangementClosedSignConeOn sigmaG {l, a, b} := by
        rw [A.mem_arrangementClosedSignConeOn]
        intro k hk
        simp only [Finset.mem_insert, Finset.mem_singleton] at hk
        rcases hk with hkl | hka | hkb
        · subst k
          exact hvlG
        · subst k
          rw [hEvalTrans a hal]
          exact hva
        · subst k
          rw [hEvalTrans b hbl]
          exact hvb
      have hvFull : v ∈ A.arrangementClosedSignCone sigmaG := by
        rw [← hconeG]
        exact hvOn
      have hmG :=
        (A.mem_arrangementClosedSignCone_iff_orientedEvaluation_nonneg
          sigmaG v).mp hvFull m
      simpa only [hEvalTrans m hml] using hmG
  have hcommonKernel : ∀ v : Fin 3 → ℝ,
      A.arrangementOrientedEvaluation sigmaF a v = 0 →
      A.arrangementOrientedEvaluation sigmaF b v = 0 →
      A.arrangementOrientedEvaluation sigmaF m v = 0 := by
    intro v hva hvb
    have hmPos := hmNonneg v hva.symm.le hvb.symm.le
    have hmNeg := hmNonneg (-v) (by
      rw [LinearMap.map_neg, hva, neg_zero]) (by
      rw [LinearMap.map_neg, hvb, neg_zero])
    rw [LinearMap.map_neg] at hmNeg
    exact le_antisymm (neg_nonneg.mp hmNeg) hmPos
  let r := A.intersection a b
  have hra : A.Incident r a := A.intersection_incident_left hab
  have hrb : A.Incident r b := A.intersection_incident_right hab
  have hraEval : A.arrangementOrientedEvaluation sigmaF a r.rep = 0 := by
    apply (A.incident_projectivization_mk_iff_orientedEvaluation_eq_zero
      sigmaF a r.rep r.rep_nonzero).1
    simpa only [Projectivization.mk_rep] using hra
  have hrbEval : A.arrangementOrientedEvaluation sigmaF b r.rep = 0 := by
    apply (A.incident_projectivization_mk_iff_orientedEvaluation_eq_zero
      sigmaF b r.rep r.rep_nonzero).1
    simpa only [Projectivization.mk_rep] using hrb
  have hrmEval := hcommonKernel r.rep hraEval hrbEval
  have hrm : A.Incident (Projectivization.mk ℝ r.rep r.rep_nonzero) m :=
    (A.incident_projectivization_mk_iff_orientedEvaluation_eq_zero
      sigmaF m r.rep r.rep_nonzero).2 hrmEval
  simpa only [r, Projectivization.mk_rep] using hrm

/-- The two sides of one ray from an ordinary vertex produce two different
third supports through its other endpoint.  Equality of those supports
would make the arrangement concurrent away from the ray support. -/
theorem exists_two_distinct_terminal_supports_of_ordinary_initial
    (A : FiniteProjectiveLineArrangement Line) (hA : A.NonPencil)
    (e : A.GeometricEdge) (c ell : Line)
    (he : A.edgeSlotLine e = c) (hellc : ell ≠ c)
    (hinitial : ∀ m : Line,
      A.Incident (A.geometricEdgeInitial e) m ↔ m = c ∨ m = ell)
    (htri : ∀ F : A.ArrangementFace,
      (A.arrangementFaceBoundary F).card = 3)
    (hnoConcurrent : ¬ ∃ r : RealProjectivePoint,
      ∀ m : Line, m ≠ c → A.Incident r m) :
    ∃ x y : Line,
      x ≠ c ∧ x ≠ ell ∧ y ≠ c ∧ y ≠ ell ∧ x ≠ y ∧
      A.Incident (A.geometricEdgeTerminal e) x ∧
      A.Incident (A.geometricEdgeTerminal e) y := by
  obtain ⟨q, hq⟩ := (A.isPathConnected_geometricEdgeOpenArc hA e).nonempty
  obtain ⟨F, G, hFG, hF, hG⟩ :=
    A.exists_two_distinct_geometricEdgeAdjacentFaces_at hA e hq
  obtain ⟨eEll, eX, heEll, hboundaryF, heXc, heXell, hterminalX⟩ :=
    A.exists_terminal_support_of_triangle_at_ordinary_initial
      hA F e c ell he hellc hinitial hF (htri F)
  obtain ⟨eEll', eY, heEll', hboundaryG, heYc, heYell, hterminalY⟩ :=
    A.exists_terminal_support_of_triangle_at_ordinary_initial
      hA G e c ell he hellc hinitial hG (htri G)
  have hXY : A.edgeSlotLine eX ≠ A.edgeSlotLine eY := by
    intro hXY
    apply hnoConcurrent
    refine ⟨A.intersection ell (A.edgeSlotLine eX), ?_⟩
    intro m hmc
    apply incident_intersection_of_two_exact_opposite_triangles_core
      A hA e eEll eX eEll' eY c ell (A.edgeSlotLine eX) m F G
    · exact he
    · exact heEll
    · rfl
    · exact heEll'
    · exact hXY.symm
    · exact hellc
    · exact heXc
    · exact heXell.symm
    · exact hF
    · exact hG
    · exact hFG
    · exact hboundaryF
    · exact hboundaryG
    · exact hmc
  exact ⟨A.edgeSlotLine eX, A.edgeSlotLine eY,
    heXc, heXell, heYc, heYell, hXY, hterminalX, hterminalY⟩

/-- Strengthened outgoing-ray extractor retaining the cyclic-neighbour
location of both selected supports on `ell`. -/
theorem exists_two_distinct_terminal_supports_at_ell_neighbors
    (A : FiniteProjectiveLineArrangement Line) (hA : A.NonPencil)
    (ell : Line) (d : A.CircularGapSlot ell)
    (e : A.GeometricEdge) (c : Line)
    (he : A.edgeSlotLine e = c) (hellc : ell ≠ c)
    (hdinitial : A.geometricEdgeInitial e = d.1)
    (hdordinary : ∀ m : Line, A.Incident d.1 m ↔ m = c ∨ m = ell)
    (htri : ∀ F : A.ArrangementFace,
      (A.arrangementFaceBoundary F).card = 3)
    (hnoConcurrent : ¬ ∃ r : RealProjectivePoint,
      ∀ m : Line, m ≠ c → A.Incident r m) :
    ∃ x y : Line,
      x ≠ c ∧ x ≠ ell ∧ y ≠ c ∧ y ≠ ell ∧ x ≠ y ∧
      A.Incident (A.geometricEdgeTerminal e) x ∧
      A.Incident (A.geometricEdgeTerminal e) y ∧
      (A.intersection ell x = (A.circularGapPredecessor ell d).1 ∨
        A.intersection ell x = (A.circularGapSuccessor ell d).1) ∧
      (A.intersection ell y = (A.circularGapPredecessor ell d).1 ∨
        A.intersection ell y = (A.circularGapSuccessor ell d).1) := by
  have hinitial : ∀ m : Line,
      A.Incident (A.geometricEdgeInitial e) m ↔ m = c ∨ m = ell := by
    intro m
    rw [hdinitial]
    exact hdordinary m
  obtain ⟨q, hq⟩ := (A.isPathConnected_geometricEdgeOpenArc hA e).nonempty
  obtain ⟨F, G, hFG, hF, hG⟩ :=
    A.exists_two_distinct_geometricEdgeAdjacentFaces_at hA e hq
  obtain ⟨eEll, eX, heEll, hboundaryF, heXc, heXell, hterminalX⟩ :=
    A.exists_terminal_support_of_triangle_at_ordinary_initial
      hA F e c ell he hellc hinitial hF (htri F)
  obtain ⟨eEll', eY, heEll', hboundaryG, heYc, heYell, hterminalY⟩ :=
    A.exists_terminal_support_of_triangle_at_ordinary_initial
      hA G e c ell he hellc hinitial hG (htri G)
  have hXY : A.edgeSlotLine eX ≠ A.edgeSlotLine eY := by
    intro hXY
    apply hnoConcurrent
    refine ⟨A.intersection ell (A.edgeSlotLine eX), ?_⟩
    intro m hmc
    apply incident_intersection_of_two_exact_opposite_triangles_core
      A hA e eEll eX eEll' eY c ell (A.edgeSlotLine eX) m F G
      he heEll rfl heEll' hXY.symm hellc heXc heXell.symm
        hF hG hFG hboundaryF hboundaryG hmc
  have hdc : A.Incident d.1 c := (hdordinary c).2 (Or.inl rfl)
  have hneighborX := A.triangle_third_support_meets_ell_at_neighbor
    hA ell d F e eEll eX c hellc hdc hdordinary hboundaryF
      he heEll heXc heXell
  have hneighborY := A.triangle_third_support_meets_ell_at_neighbor
    hA ell d G e eEll' eY c hellc hdc hdordinary hboundaryG
      he heEll' heYc heYell
  exact ⟨A.edgeSlotLine eX, A.edgeSlotLine eY,
    heXc, heXell, heYc, heYell, hXY, hterminalX, hterminalY,
      hneighborX, hneighborY⟩

/-- Incoming-ray companion: its two incident faces give two different
supports through the initial endpoint. -/
theorem exists_two_distinct_initial_supports_of_ordinary_terminal
    (A : FiniteProjectiveLineArrangement Line) (hA : A.NonPencil)
    (e : A.GeometricEdge) (c ell : Line)
    (he : A.edgeSlotLine e = c) (hellc : ell ≠ c)
    (hterminal : ∀ m : Line,
      A.Incident (A.geometricEdgeTerminal e) m ↔ m = c ∨ m = ell)
    (htri : ∀ F : A.ArrangementFace,
      (A.arrangementFaceBoundary F).card = 3)
    (hnoConcurrent : ¬ ∃ r : RealProjectivePoint,
      ∀ m : Line, m ≠ c → A.Incident r m) :
    ∃ x y : Line,
      x ≠ c ∧ x ≠ ell ∧ y ≠ c ∧ y ≠ ell ∧ x ≠ y ∧
      A.Incident (A.geometricEdgeInitial e) x ∧
      A.Incident (A.geometricEdgeInitial e) y := by
  obtain ⟨q, hq⟩ := (A.isPathConnected_geometricEdgeOpenArc hA e).nonempty
  obtain ⟨F, G, hFG, hF, hG⟩ :=
    A.exists_two_distinct_geometricEdgeAdjacentFaces_at hA e hq
  obtain ⟨eEll, eX, heEll, hboundaryF, heXc, heXell, hinitialX⟩ :=
    A.exists_initial_support_of_triangle_at_ordinary_terminal
      hA F e c ell he hellc hterminal hF (htri F)
  obtain ⟨eEll', eY, heEll', hboundaryG, heYc, heYell, hinitialY⟩ :=
    A.exists_initial_support_of_triangle_at_ordinary_terminal
      hA G e c ell he hellc hterminal hG (htri G)
  have hXY : A.edgeSlotLine eX ≠ A.edgeSlotLine eY := by
    intro hXY
    apply hnoConcurrent
    refine ⟨A.intersection ell (A.edgeSlotLine eX), ?_⟩
    intro m hmc
    apply incident_intersection_of_two_exact_opposite_triangles_core
      A hA e eEll eX eEll' eY c ell (A.edgeSlotLine eX) m F G
    · exact he
    · exact heEll
    · rfl
    · exact heEll'
    · exact hXY.symm
    · exact hellc
    · exact heXc
    · exact heXell.symm
    · exact hF
    · exact hG
    · exact hFG
    · exact hboundaryF
    · exact hboundaryG
    · exact hmc
  exact ⟨A.edgeSlotLine eX, A.edgeSlotLine eY,
    heXc, heXell, heYc, heYell, hXY, hinitialX, hinitialY⟩

/-- Strengthened incoming-ray extractor retaining the cyclic-neighbour
location of both selected supports on `ell`. -/
theorem exists_two_distinct_initial_supports_at_ell_neighbors
    (A : FiniteProjectiveLineArrangement Line) (hA : A.NonPencil)
    (ell : Line) (d : A.CircularGapSlot ell)
    (e : A.GeometricEdge) (c : Line)
    (he : A.edgeSlotLine e = c) (hellc : ell ≠ c)
    (hdterminal : A.geometricEdgeTerminal e = d.1)
    (hdordinary : ∀ m : Line, A.Incident d.1 m ↔ m = c ∨ m = ell)
    (htri : ∀ F : A.ArrangementFace,
      (A.arrangementFaceBoundary F).card = 3)
    (hnoConcurrent : ¬ ∃ r : RealProjectivePoint,
      ∀ m : Line, m ≠ c → A.Incident r m) :
    ∃ x y : Line,
      x ≠ c ∧ x ≠ ell ∧ y ≠ c ∧ y ≠ ell ∧ x ≠ y ∧
      A.Incident (A.geometricEdgeInitial e) x ∧
      A.Incident (A.geometricEdgeInitial e) y ∧
      (A.intersection ell x = (A.circularGapPredecessor ell d).1 ∨
        A.intersection ell x = (A.circularGapSuccessor ell d).1) ∧
      (A.intersection ell y = (A.circularGapPredecessor ell d).1 ∨
        A.intersection ell y = (A.circularGapSuccessor ell d).1) := by
  have hterminal : ∀ m : Line,
      A.Incident (A.geometricEdgeTerminal e) m ↔ m = c ∨ m = ell := by
    intro m
    rw [hdterminal]
    exact hdordinary m
  obtain ⟨q, hq⟩ := (A.isPathConnected_geometricEdgeOpenArc hA e).nonempty
  obtain ⟨F, G, hFG, hF, hG⟩ :=
    A.exists_two_distinct_geometricEdgeAdjacentFaces_at hA e hq
  obtain ⟨eEll, eX, heEll, hboundaryF, heXc, heXell, hinitialX⟩ :=
    A.exists_initial_support_of_triangle_at_ordinary_terminal
      hA F e c ell he hellc hterminal hF (htri F)
  obtain ⟨eEll', eY, heEll', hboundaryG, heYc, heYell, hinitialY⟩ :=
    A.exists_initial_support_of_triangle_at_ordinary_terminal
      hA G e c ell he hellc hterminal hG (htri G)
  have hXY : A.edgeSlotLine eX ≠ A.edgeSlotLine eY := by
    intro hXY
    apply hnoConcurrent
    refine ⟨A.intersection ell (A.edgeSlotLine eX), ?_⟩
    intro m hmc
    apply incident_intersection_of_two_exact_opposite_triangles_core
      A hA e eEll eX eEll' eY c ell (A.edgeSlotLine eX) m F G
      he heEll rfl heEll' hXY.symm hellc heXc heXell.symm
        hF hG hFG hboundaryF hboundaryG hmc
  have hdc : A.Incident d.1 c := (hdordinary c).2 (Or.inl rfl)
  have hneighborX := A.triangle_third_support_meets_ell_at_neighbor
    hA ell d F e eEll eX c hellc hdc hdordinary hboundaryF
      he heEll heXc heXell
  have hneighborY := A.triangle_third_support_meets_ell_at_neighbor
    hA ell d G e eEll' eY c hellc hdc hdordinary hboundaryG
      he heEll' heYc heYell
  exact ⟨A.edgeSlotLine eX, A.edgeSlotLine eY,
    heXc, heXell, heYc, heYell, hXY, hinitialX, hinitialY,
      hneighborX, hneighborY⟩

/-- Two different supports through the remote endpoint of an ordinary ray
cannot both return to the same neighbouring vertex on `ell`; hence they
match the predecessor and successor bijectively. -/
theorem two_distinct_neighbor_supports_split
    (A : FiniteProjectiveLineArrangement Line)
    (ell : Line) (d : A.CircularGapSlot ell)
    (v : RealProjectivePoint) (c x y : Line)
    (hellc : ell ≠ c)
    (hd : d.1 = A.intersection ell c)
    (hvc : A.Incident v c) (hvd : v ≠ d.1)
    (hxell : x ≠ ell) (hyell : y ≠ ell) (hxy : x ≠ y)
    (hvx : A.Incident v x) (hvy : A.Incident v y)
    (hx : A.intersection ell x = (A.circularGapPredecessor ell d).1 ∨
      A.intersection ell x = (A.circularGapSuccessor ell d).1)
    (hy : A.intersection ell y = (A.circularGapPredecessor ell d).1 ∨
      A.intersection ell y = (A.circularGapSuccessor ell d).1) :
    (A.intersection ell x = (A.circularGapPredecessor ell d).1 ∧
        A.intersection ell y = (A.circularGapSuccessor ell d).1) ∨
      (A.intersection ell x = (A.circularGapSuccessor ell d).1 ∧
        A.intersection ell y = (A.circularGapPredecessor ell d).1) := by
  have hnotSame (t : A.CircularGapSlot ell)
      (hxt : A.intersection ell x = t.1)
      (hyt : A.intersection ell y = t.1) : False := by
    have htell : A.Incident t.1 ell := ((A.mem_lineVertexSet ell).1 t.2).2
    have htx : A.Incident t.1 x := by
      rw [← hxt]
      exact A.intersection_incident_right hxell.symm
    have hty : A.Incident t.1 y := by
      rw [← hyt]
      exact A.intersection_incident_right hyell.symm
    have hvEq : v = A.intersection x y :=
      A.eq_intersection_of_incident hxy hvx hvy
    have htEq : t.1 = A.intersection x y :=
      A.eq_intersection_of_incident hxy htx hty
    have hvt : v = t.1 := hvEq.trans htEq.symm
    apply hvd
    calc
      v = A.intersection ell c :=
        A.eq_intersection_of_incident hellc (hvt.symm ▸ htell) hvc
      _ = d.1 := hd.symm
  rcases hx with hxP | hxS <;> rcases hy with hyP | hyS
  · exact (hnotSame (A.circularGapPredecessor ell d) hxP hyP).elim
  · exact Or.inl ⟨hxP, hyS⟩
  · exact Or.inr ⟨hxS, hyP⟩
  · exact (hnotSame (A.circularGapSuccessor ell d) hxS hyS).elim

private theorem existsUnique_other_line_at_circularGap_of_multiplicity_eq_two_early
    (A : FiniteProjectiveLineArrangement Line) (l : Line)
    (p : A.CircularGapSlot l) (hp2 : A.multiplicity p.1 = 2) :
    ∃! a : Line,
      a ≠ l ∧ A.Incident p.1 a ∧ p.1 = A.intersection l a := by
  classical
  let I : Finset Line := Finset.univ.filter fun a => A.Incident p.1 a
  have hpl : A.Incident p.1 l := ((A.mem_lineVertexSet l).mp p.2).2
  have hlI : l ∈ I := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hpl⟩
  have hIcard : I.card = 2 := by
    simpa only [I, multiplicity] using hp2
  have hErase : (I.erase l).card = 1 := by
    rw [Finset.card_erase_of_mem hlI, hIcard]
  obtain ⟨a, ha⟩ := Finset.card_eq_one.mp hErase
  have haErase : a ∈ I.erase l := by
    rw [ha]
    exact Finset.mem_singleton_self a
  have ha' := Finset.mem_erase.mp haErase
  have hpa : A.Incident p.1 a := (Finset.mem_filter.mp ha'.2).2
  refine ⟨a, ⟨ha'.1, hpa,
    A.eq_intersection_of_incident (Ne.symm ha'.1) hpl hpa⟩, ?_⟩
  intro b hb
  have hbErase : b ∈ I.erase l := Finset.mem_erase.mpr
    ⟨hb.1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hb.2.1⟩⟩
  rw [ha] at hbErase
  exact Finset.mem_singleton.mp hbErase

/-- If `d = ell ∩ c` is ordinary and the arrangement is not concurrent
away from `ell`, then `c` has a third marked vertex. -/
theorem three_le_card_circularGapSlot_of_ordinary_of_no_concurrent_away
    (A : FiniteProjectiveLineArrangement Line) (hA : A.NonPencil)
    (ell : Line) (d : A.CircularGapSlot ell) (c : Line)
    (hellc : ell ≠ c)
    (hdordinary : ∀ m : Line, A.Incident d.1 m ↔ m = c ∨ m = ell)
    (hnoConcurrentEll : ¬ ∃ r : RealProjectivePoint,
      ∀ m : Line, m ≠ ell → A.Incident r m) :
    3 ≤ Fintype.card (A.CircularGapSlot c) := by
  classical
  rw [Fintype.card_coe]
  have hdVertex : d.1 ∈ A.vertexSet :=
    ((A.mem_lineVertexSet ell).1 d.2).1
  have hdc : A.Incident d.1 c := (hdordinary c).2 (Or.inl rfl)
  have hdC : d.1 ∈ A.lineVertexSet c :=
    (A.mem_lineVertexSet c).2 ⟨hdVertex, hdc⟩
  by_contra hnot
  have hlow : 1 < (A.lineVertexSet c).card := by
    simpa only [Fintype.card_coe] using
      A.one_lt_card_circularGapSlot_of_nonPencil hA c
  have hcard : (A.lineVertexSet c).card = 2 := by omega
  have heraseCard : ((A.lineVertexSet c).erase d.1).card = 1 := by
    rw [Finset.card_erase_of_mem hdC, hcard]
  obtain ⟨v, herase⟩ := Finset.card_eq_one.mp heraseCard
  have hvErase : v ∈ (A.lineVertexSet c).erase d.1 := by
    rw [herase]
    exact Finset.mem_singleton_self v
  have hvC : A.Incident v c :=
    ((A.mem_lineVertexSet c).1 (Finset.mem_erase.mp hvErase).2).2
  apply hnoConcurrentEll
  refine ⟨v, ?_⟩
  intro m hmell
  by_cases hmc : m = c
  · simpa only [hmc] using hvC
  · have hcm : c ≠ m := Ne.symm hmc
    have hqC : A.intersection c m ∈ A.lineVertexSet c :=
      A.intersection_mem_lineVertexSet_left hcm
    have hqd : A.intersection c m ≠ d.1 := by
      intro hq
      have hdm : A.Incident d.1 m := by
        rw [← hq]
        exact A.intersection_incident_right hcm
      rcases (hdordinary m).1 hdm with hmc' | hmell'
      · exact hmc hmc'
      · exact hmell hmell'
    have hqErase : A.intersection c m ∈
        (A.lineVertexSet c).erase d.1 :=
      Finset.mem_erase.mpr ⟨hqd, hqC⟩
    rw [herase] at hqErase
    have hqv : A.intersection c m = v :=
      Finset.mem_singleton.mp hqErase
    rw [← hqv]
    exact A.intersection_incident_right hcm

/-- Every actual ordinary vertex on `ell` produces a complete geometric
`T-D-T` step when all faces are triangular and no deleted-line near-pencil
is present. -/
theorem exists_ordinaryTDTGalleryStep
    (A : FiniteProjectiveLineArrangement Line) (hA : A.NonPencil)
    (ell : Line) (d : A.CircularGapSlot ell)
    (hd2 : A.multiplicity d.1 = 2)
    (htri : ∀ F : A.ArrangementFace,
      (A.arrangementFaceBoundary F).card = 3)
    (hnoConcurrent : ∀ l : Line, ¬ ∃ r : RealProjectivePoint,
      ∀ m : Line, m ≠ l → A.Incident r m) :
    Nonempty (A.OrdinaryTDTGalleryStep ell d) := by
  have hdell : A.Incident d.1 ell := ((A.mem_lineVertexSet ell).1 d.2).2
  obtain ⟨c, hc, hcUnique⟩ :=
    A.existsUnique_other_line_at_circularGap_of_multiplicity_eq_two_early ell d hd2
  have hc_ne_ell : c ≠ ell := hc.1
  have hellc : ell ≠ c := hc_ne_ell.symm
  have hdc : A.Incident d.1 c := hc.2.1
  have hdEq : d.1 = A.intersection ell c := hc.2.2
  have hdordinary : ∀ m : Line,
      A.Incident d.1 m ↔ m = c ∨ m = ell :=
    fun m => by
      constructor
      · intro hm
        by_cases hmell : m = ell
        · exact Or.inr hmell
        · exact Or.inl (hcUnique m ⟨hmell, hm,
            A.eq_intersection_of_incident (Ne.symm hmell) hdell hm⟩)
      · rintro (rfl | rfl)
        · exact hdc
        · exact hdell
  let dc : A.CircularGapSlot c :=
    ⟨d.1, (A.mem_lineVertexSet c).2
      ⟨((A.mem_lineVertexSet ell).1 d.2).1, hdc⟩⟩
  let eOut : A.GeometricEdge := A.circularGapEdge c dc
  let eIn : A.GeometricEdge :=
    A.circularGapEdge c (A.circularGapPredecessor c dc)
  have heOut : A.edgeSlotLine eOut = c := by
    exact A.circularGapEdge_line c dc
  have heIn : A.edgeSlotLine eIn = c := by
    exact A.circularGapEdge_line c (A.circularGapPredecessor c dc)
  have hdinitial : A.geometricEdgeInitial eOut = d.1 := by
    rfl
  have hdterminal : A.geometricEdgeTerminal eIn = d.1 := by
    simp only [eIn, A.circularGapEdge_terminal,
      A.circularGapSuccessor_predecessor, dc]
  obtain ⟨ox, oy, hoxc, hoxell, hoyc, hoyell, hoxy,
      hvOutX, hvOutY, hoxNeighbor, hoyNeighbor⟩ :=
    A.exists_two_distinct_terminal_supports_at_ell_neighbors
      hA ell d eOut c heOut hellc hdinitial hdordinary htri
        (hnoConcurrent c)
  obtain ⟨ix, iy, hixc, hixell, hiyc, hiyell, hixy,
      hvInX, hvInY, hixNeighbor, hiyNeighbor⟩ :=
    A.exists_two_distinct_initial_supports_at_ell_neighbors
      hA ell d eIn c heIn hellc hdterminal hdordinary htri
        (hnoConcurrent c)
  have hvOutC : A.Incident (A.geometricEdgeTerminal eOut) c := by
    simpa only [eOut, A.circularGapEdge_terminal] using
      ((A.mem_lineVertexSet c).1 (A.circularGapSuccessor c dc).2).2
  have hvInC : A.Incident (A.geometricEdgeInitial eIn) c := by
    simpa only [heIn] using A.geometricEdge_initial_incident eIn
  have hvOutD : A.geometricEdgeTerminal eOut ≠ d.1 := by
    intro h
    exact A.geometricEdge_initial_ne_terminal_of_nonPencil hA eOut
      (hdinitial.trans h.symm)
  have hvInD : A.geometricEdgeInitial eIn ≠ d.1 := by
    intro h
    exact A.geometricEdge_initial_ne_terminal_of_nonPencil hA eIn
      (h.trans hdterminal.symm)
  have houtSplit := A.two_distinct_neighbor_supports_split
    ell d (A.geometricEdgeTerminal eOut) c ox oy hellc hdEq
      hvOutC hvOutD hoxell hoyell hoxy hvOutX hvOutY
        hoxNeighbor hoyNeighbor
  have hinSplit := A.two_distinct_neighbor_supports_split
    ell d (A.geometricEdgeInitial eIn) c ix iy hellc hdEq
      hvInC hvInD hixell hiyell hixy hvInX hvInY
        hixNeighbor hiyNeighbor
  obtain ⟨upperP, upperS, hupperPc, hupperPell, hupperSc,
      hupperSell, hupperPS, hvUpperP, hvUpperS,
      hupperPpoint, hupperSpoint⟩ :
      ∃ p s : Line,
        p ≠ c ∧ p ≠ ell ∧ s ≠ c ∧ s ≠ ell ∧ p ≠ s ∧
        A.Incident (A.geometricEdgeTerminal eOut) p ∧
        A.Incident (A.geometricEdgeTerminal eOut) s ∧
        A.intersection ell p = (A.circularGapPredecessor ell d).1 ∧
        A.intersection ell s = (A.circularGapSuccessor ell d).1 := by
    rcases houtSplit with hout | hout
    · exact ⟨ox, oy, hoxc, hoxell, hoyc, hoyell, hoxy,
        hvOutX, hvOutY, hout.1, hout.2⟩
    · exact ⟨oy, ox, hoyc, hoyell, hoxc, hoxell, hoxy.symm,
        hvOutY, hvOutX, hout.2, hout.1⟩
  obtain ⟨lowerP, lowerS, hlowerPc, hlowerPell, hlowerSc,
      hlowerSell, hlowerPS, hvLowerP, hvLowerS,
      hlowerPpoint, hlowerSpoint⟩ :
      ∃ p s : Line,
        p ≠ c ∧ p ≠ ell ∧ s ≠ c ∧ s ≠ ell ∧ p ≠ s ∧
        A.Incident (A.geometricEdgeInitial eIn) p ∧
        A.Incident (A.geometricEdgeInitial eIn) s ∧
        A.intersection ell p = (A.circularGapPredecessor ell d).1 ∧
        A.intersection ell s = (A.circularGapSuccessor ell d).1 := by
    rcases hinSplit with hin | hin
    · exact ⟨ix, iy, hixc, hixell, hiyc, hiyell, hixy,
        hvInX, hvInY, hin.1, hin.2⟩
    · exact ⟨iy, ix, hiyc, hiyell, hixc, hixell, hixy.symm,
        hvInY, hvInX, hin.2, hin.1⟩
  have hcardC : 3 ≤ Fintype.card (A.CircularGapSlot c) :=
    A.three_le_card_circularGapSlot_of_ordinary_of_no_concurrent_away
      hA ell d c hellc hdordinary (hnoConcurrent ell)
  have hvOutIn : A.geometricEdgeTerminal eOut ≠
      A.geometricEdgeInitial eIn := by
    simpa only [eOut, eIn, A.circularGapEdge_terminal,
      A.circularGapEdge_initial] using
      (A.circularGapPredecessor_val_ne_successor_val_of_three_le
        c dc hcardC).symm
  have hpredNe : upperP ≠ lowerP := by
    intro hline
    apply hvOutIn
    have hOut := A.eq_intersection_of_incident hupperPc.symm
      hvOutC hvUpperP
    have hIn := A.eq_intersection_of_incident hlowerPc.symm
      hvInC hvLowerP
    rw [hline] at hOut
    exact hOut.trans hIn.symm
  have hsuccNe : upperS ≠ lowerS := by
    intro hline
    apply hvOutIn
    have hOut := A.eq_intersection_of_incident hupperSc.symm
      hvOutC hvUpperS
    have hIn := A.eq_intersection_of_incident hlowerSc.symm
      hvInC hvLowerS
    rw [hline] at hOut
    exact hOut.trans hIn.symm
  exact ⟨{
    c := c
    c_ne_ell := hc_ne_ell
    singletonIncident_iff := fun m => by
      simpa only [or_comm] using hdordinary m
    upperVertex := A.geometricEdgeTerminal eOut
    lowerVertex := A.geometricEdgeInitial eIn
    predecessorUpper := upperP
    predecessorLower := lowerP
    successorUpper := upperS
    successorLower := lowerS
    predecessorUpper_ne_c := hupperPc
    predecessorLower_ne_c := hlowerPc
    successorUpper_ne_c := hupperSc
    successorLower_ne_c := hlowerSc
    predecessorUpper_ne_ell := hupperPell
    predecessorLower_ne_ell := hlowerPell
    successorUpper_ne_ell := hupperSell
    successorLower_ne_ell := hlowerSell
    predecessor_ne := hpredNe
    successor_ne := hsuccNe
    upperIncidence := ⟨hvOutC, hvUpperP, hvUpperS⟩
    lowerIncidence := ⟨hvInC, hvLowerP, hvLowerS⟩
    predecessorUpper_point := hupperPpoint
    predecessorLower_point := hlowerPpoint
    successorUpper_point := hupperSpoint
    successorLower_point := hlowerSpoint
  }⟩

private theorem incident_three_core
    (A : FiniteProjectiveLineArrangement Line)
    (p : RealProjectivePoint) (l a b : Line)
    (hpl : A.Incident p l) (hpa : A.Incident p a)
    (hpb : A.Incident p b)
    (hla : l ≠ a) (hlb : l ≠ b) (hab : a ≠ b)
    (hp3 : A.multiplicity p = 3) :
    ∀ m : Line, A.Incident p m ↔ m = l ∨ m = a ∨ m = b := by
  classical
  let I : Finset Line := Finset.univ.filter fun m => A.Incident p m
  have hIcard : I.card = 3 := by
    simpa only [I, multiplicity] using hp3
  have hsub : ({l, a, b} : Finset Line) ⊆ I := by
    intro m hm
    simp only [Finset.mem_insert, Finset.mem_singleton] at hm
    rcases hm with rfl | rfl | rfl
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hpl⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hpa⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hpb⟩
  have hsetCard : ({l, a, b} : Finset Line).card = 3 := by
    simp [hla, hlb, hab, Ne.symm hla, Ne.symm hlb, Ne.symm hab]
  have hset : ({l, a, b} : Finset Line) = I :=
    Finset.eq_of_subset_of_card_le hsub (by rw [hsetCard, hIcard])
  intro m
  have hmI : A.Incident p m ↔ m ∈ I := by
    simp only [I, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [hmI, ← hset]
  simp only [Finset.mem_insert, Finset.mem_singleton]

/-- At a shared triple vertex, the successor pair of one strip step and the
predecessor pair of the next are the same unordered pair. -/
theorem OrdinaryTDTGalleryStep.shared_triple_matching
    (A : FiniteProjectiveLineArrangement Line)
    (ell : Line) (d e : A.CircularGapSlot ell)
    (S : A.OrdinaryTDTGalleryStep ell d)
    (T : A.OrdinaryTDTGalleryStep ell e)
    (hshared : (A.circularGapSuccessor ell d).1 =
      (A.circularGapPredecessor ell e).1)
    (htriple : A.multiplicity (A.circularGapSuccessor ell d).1 = 3) :
    (S.successorUpper = T.predecessorUpper ∧
        S.successorLower = T.predecessorLower) ∨
      (S.successorUpper = T.predecessorLower ∧
        S.successorLower = T.predecessorUpper) := by
  let t := (A.circularGapSuccessor ell d).1
  have htell : A.Incident t ell :=
    ((A.mem_lineVertexSet ell).1 (A.circularGapSuccessor ell d).2).2
  have hsU : A.Incident t S.successorUpper := by
    dsimp only [t]
    rw [← S.successorUpper_point]
    exact A.intersection_incident_right S.successorUpper_ne_ell.symm
  have hsL : A.Incident t S.successorLower := by
    dsimp only [t]
    rw [← S.successorLower_point]
    exact A.intersection_incident_right S.successorLower_ne_ell.symm
  have htU : A.Incident t T.predecessorUpper := by
    dsimp only [t]
    rw [hshared, ← T.predecessorUpper_point]
    exact A.intersection_incident_right T.predecessorUpper_ne_ell.symm
  have htL : A.Incident t T.predecessorLower := by
    dsimp only [t]
    rw [hshared, ← T.predecessorLower_point]
    exact A.intersection_incident_right T.predecessorLower_ne_ell.symm
  have hexact := incident_three_core
    A t ell S.successorUpper S.successorLower htell hsU hsL
      S.successorUpper_ne_ell.symm S.successorLower_ne_ell.symm
        S.successor_ne htriple
  rcases (hexact T.predecessorUpper).1 htU with htUEll | htUU | htUL
  · exact (T.predecessorUpper_ne_ell htUEll).elim
  · rcases (hexact T.predecessorLower).1 htL with htLEll | htLU | htLL
    · exact (T.predecessorLower_ne_ell htLEll).elim
    · exact (T.predecessor_ne (htUU.trans htLU.symm)).elim
    · exact Or.inl ⟨htUU.symm, htLL.symm⟩
  · rcases (hexact T.predecessorLower).1 htL with htLEll | htLU | htLL
    · exact (T.predecessorLower_ne_ell htLEll).elim
    · exact Or.inr ⟨htLU.symm, htUL.symm⟩
    · exact (T.predecessor_ne (htUL.trans htLL.symm)).elim

/-- Sector crossing in dual form.  If the two distinct faces on an edge
have the same three supporting lines `l,a,b`, then every other arrangement
line passes through `a ∩ b`.  The proof uses the two opposite `l` signs:
the oriented evaluation of any further line is nonnegative on both
half-cones, hence vanishes on the common kernel of `a` and `b`. -/
theorem incident_intersection_of_two_exact_opposite_triangles
    (A : FiniteProjectiveLineArrangement Line) (hA : A.NonPencil)
    (e eP eQ eP' eQ' : A.GeometricEdge)
    (l a b m : Line) (F G : A.ArrangementFace)
    (he : A.edgeSlotLine e = l)
    (heP : A.edgeSlotLine eP = a) (heQ : A.edgeSlotLine eQ = b)
    (heP' : A.edgeSlotLine eP' = a) (heQ' : A.edgeSlotLine eQ' = b)
    (hal : a ≠ l) (hbl : b ≠ l) (hab : a ≠ b)
    (hF : A.geometricEdgeAdjacentFace e F)
    (hG : A.geometricEdgeAdjacentFace e G) (hFG : F ≠ G)
    (hboundaryF : A.arrangementFaceBoundary F = {e, eP, eQ})
    (hboundaryG : A.arrangementFaceBoundary G = {e, eP', eQ'})
    (hml : m ≠ l) :
    A.Incident (A.intersection a b) m := by
  exact incident_intersection_of_two_exact_opposite_triangles_core
    A hA e eP eQ eP' eQ' l a b m F G he heP heQ heP' heQ'
      hal hbl hab hF hG hFG hboundaryF hboundaryG hml
/-
  classical
  obtain ⟨q, hq⟩ := (A.isPathConnected_geometricEdgeOpenArc hA e).nonempty
  have hregular : ∀ k : Line, A.Incident q k ↔ k = l := by
    intro k
    simpa only [he] using A.geometricEdgeOpenArc_incident_iff e hq k
  have hqF : q ∈ closure (A.arrangementFaceCarrier F) := by
    rcases hF with ⟨qF, hqFarc, hqFclosure⟩
    exact A.mem_closure_arrangementFaceCarrier_of_mem_closure_of_geometricEdgeOpenArc
      hA e hqFarc hq F hqFclosure
  have hqG : q ∈ closure (A.arrangementFaceCarrier G) := by
    rcases hG with ⟨qG, hqGarc, hqGclosure⟩
    exact A.mem_closure_arrangementFaceCarrier_of_mem_closure_of_geometricEdgeOpenArc
      hA e hqGarc hq G hqGclosure
  let sigmaF := A.arrangementFaceSignPattern a F
  let sigmaG := A.arrangementFaceSignPattern a G
  have hsigmaTrans : ∀ k : Line, k ≠ l → sigmaF k = sigmaG k := by
    intro k hkl
    have hqa : ¬ A.Incident q a := by
      intro h
      exact hal ((hregular a).mp h)
    have hqk : ¬ A.Incident q k := by
      intro h
      exact hkl ((hregular k).mp h)
    have hrelF :=
      A.arrangementRelativeSign_arrangementFaceRepresentative_eq_of_mem_closure
        q a k F hqa hqk hqF
    have hrelG :=
      A.arrangementRelativeSign_arrangementFaceRepresentative_eq_of_mem_closure
        q a k G hqa hqk hqG
    dsimp only [sigmaF, sigmaG, arrangementFaceSignPattern]
    rw [A.arrangementPointSignPattern_eq_relativeSign a
        (A.arrangementFaceRepresentative F),
      A.arrangementPointSignPattern_eq_relativeSign a
        (A.arrangementFaceRepresentative G)]
    rw [hrelF, hrelG]
  have hsigmaNe : sigmaF ≠ sigmaG := by
    intro h
    apply hFG
    exact A.arrangementFaceSignPattern_injective a h
  have hsigmaL : sigmaF l ≠ sigmaG l := by
    intro hl
    apply hsigmaNe
    funext k
    by_cases hkl : k = l
    · simpa only [hkl] using hl
    · exact hsigmaTrans k hkl
  have hEvalTrans : ∀ k : Line, k ≠ l →
      A.arrangementOrientedEvaluation sigmaG k =
        A.arrangementOrientedEvaluation sigmaF k := by
    intro k hkl
    unfold arrangementOrientedEvaluation
    rw [hsigmaTrans k hkl]
  have hEvalLOpp : A.arrangementOrientedEvaluation sigmaG l =
      -A.arrangementOrientedEvaluation sigmaF l := by
    unfold arrangementOrientedEvaluation
    cases hFbit : sigmaF l <;> cases hGbit : sigmaG l <;> simp_all
  have hconeF :=
    A.arrangementClosedSignConeOn_eq_of_exact_triangle_boundary
      hA a F e eP eQ l a b hboundaryF he heP heQ hal hbl hab
  have hconeG :=
    A.arrangementClosedSignConeOn_eq_of_exact_triangle_boundary
      hA a G e eP' eQ' l a b hboundaryG he heP' heQ' hal hbl hab
  have hmNonneg : ∀ v : Fin 3 → ℝ,
      0 ≤ A.arrangementOrientedEvaluation sigmaF a v →
      0 ≤ A.arrangementOrientedEvaluation sigmaF b v →
      0 ≤ A.arrangementOrientedEvaluation sigmaF m v := by
    intro v hva hvb
    by_cases hvl : 0 ≤ A.arrangementOrientedEvaluation sigmaF l v
    · have hvOn : v ∈ A.arrangementClosedSignConeOn sigmaF {l, a, b} := by
        rw [A.mem_arrangementClosedSignConeOn]
        intro k hk
        simp only [Finset.mem_insert, Finset.mem_singleton] at hk
        rcases hk with rfl | rfl | rfl
        · exact hvl
        · exact hva
        · exact hvb
      have hvFull : v ∈ A.arrangementClosedSignCone sigmaF := by
        rw [← hconeF]
        exact hvOn
      exact (A.mem_arrangementClosedSignCone_iff_orientedEvaluation_nonneg
        sigmaF v).mp hvFull m
    · have hvlG : 0 ≤ A.arrangementOrientedEvaluation sigmaG l v := by
        rw [hEvalLOpp, LinearMap.neg_apply]
        exact neg_nonneg.mpr (le_of_lt (lt_of_not_ge hvl))
      have hvOn : v ∈ A.arrangementClosedSignConeOn sigmaG {l, a, b} := by
        rw [A.mem_arrangementClosedSignConeOn]
        intro k hk
        simp only [Finset.mem_insert, Finset.mem_singleton] at hk
        rcases hk with rfl | rfl | rfl
        · exact hvlG
        · simpa only [hEvalTrans a hal] using hva
        · simpa only [hEvalTrans b hbl] using hvb
      have hvFull : v ∈ A.arrangementClosedSignCone sigmaG := by
        rw [← hconeG]
        exact hvOn
      have hmG :=
        (A.mem_arrangementClosedSignCone_iff_orientedEvaluation_nonneg
          sigmaG v).mp hvFull m
      simpa only [hEvalTrans m hml] using hmG
  have hcommonKernel : ∀ v : Fin 3 → ℝ,
      A.arrangementOrientedEvaluation sigmaF a v = 0 →
      A.arrangementOrientedEvaluation sigmaF b v = 0 →
      A.arrangementOrientedEvaluation sigmaF m v = 0 := by
    intro v hva hvb
    have hmPos := hmNonneg v hva.le hvb.le
    have hmNeg := hmNonneg (-v) (by
      rw [LinearMap.map_neg, hva, neg_zero]) (by
      rw [LinearMap.map_neg, hvb, neg_zero])
    rw [LinearMap.map_neg] at hmNeg
    exact le_antisymm (neg_nonneg.mp hmNeg) hmPos
  let r := A.intersection a b
  have hra : A.Incident r a := A.intersection_incident_left hab
  have hrb : A.Incident r b := A.intersection_incident_right hab
  have hraEval : A.arrangementOrientedEvaluation sigmaF a r.rep = 0 := by
    apply (A.incident_projectivization_mk_iff_orientedEvaluation_eq_zero
      sigmaF a r.rep r.rep_nonzero).1
    simpa only [Projectivization.mk_rep] using hra
  have hrbEval : A.arrangementOrientedEvaluation sigmaF b r.rep = 0 := by
    apply (A.incident_projectivization_mk_iff_orientedEvaluation_eq_zero
      sigmaF b r.rep r.rep_nonzero).1
    simpa only [Projectivization.mk_rep] using hrb
  have hrmEval := hcommonKernel r.rep hraEval hrbEval
  have hrm : A.Incident (Projectivization.mk ℝ r.rep r.rep_nonzero) m :=
    (A.incident_projectivization_mk_iff_orientedEvaluation_eq_zero
      sigmaF m r.rep r.rep_nonzero).2 hrmEval
  simpa only [r, Projectivization.mk_rep] using hrm
-/

/-- A multiplicity-two point on `l` lies on a unique other indexed line. -/
theorem existsUnique_other_incident_line_of_multiplicity_eq_two
    (A : FiniteProjectiveLineArrangement Line)
    (p : RealProjectivePoint) (l : Line)
    (hpl : A.Incident p l) (hp2 : A.multiplicity p = 2) :
    ∃! a : Line, a ≠ l ∧ A.Incident p a := by
  classical
  let I : Finset Line := Finset.univ.filter fun a => A.Incident p a
  have hlI : l ∈ I := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hpl⟩
  have hIcard : I.card = 2 := by
    simpa only [I, multiplicity] using hp2
  have hErase : (I.erase l).card = 1 := by
    rw [Finset.card_erase_of_mem hlI, hIcard]
  obtain ⟨a, ha⟩ := Finset.card_eq_one.mp hErase
  have haErase : a ∈ I.erase l := by simp only [ha, Finset.mem_singleton]
  have ha' := Finset.mem_erase.mp haErase
  refine ⟨a, ⟨ha'.1, (Finset.mem_filter.mp ha'.2).2⟩, ?_⟩
  intro b hb
  have hbErase : b ∈ I.erase l := Finset.mem_erase.mpr
    ⟨hb.1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hb.2⟩⟩
  rw [ha] at hbErase
  exact Finset.mem_singleton.mp hbErase

/-- Once the transverse support at a multiplicity-two point is named, these
are exactly the two indexed lines through the point. -/
theorem incident_iff_eq_or_eq_of_multiplicity_eq_two
    (A : FiniteProjectiveLineArrangement Line)
    (p : RealProjectivePoint) (l a : Line)
    (hpl : A.Incident p l) (hpa : A.Incident p a)
    (hal : a ≠ l) (hp2 : A.multiplicity p = 2) :
    ∀ m : Line, A.Incident p m ↔ m = l ∨ m = a := by
  obtain ⟨b, hb, hub⟩ :=
    A.existsUnique_other_incident_line_of_multiplicity_eq_two p l hpl hp2
  have hab : a = b := hub a ⟨hal, hpa⟩
  intro m
  constructor
  . intro hm
    by_cases hml : m = l
    . exact Or.inl hml
    . exact Or.inr ((hub m ⟨hml, hm⟩).trans hab.symm)
  . rintro (rfl | rfl)
    . exact hpl
    . exact hpa

/-- Three named distinct supports through a multiplicity-three vertex are
all the indexed supports through that vertex. -/
theorem incident_iff_eq_or_eq_or_eq_of_multiplicity_eq_three
    (A : FiniteProjectiveLineArrangement Line)
    (p : RealProjectivePoint) (l a b : Line)
    (hpl : A.Incident p l) (hpa : A.Incident p a)
    (hpb : A.Incident p b)
    (hla : l ≠ a) (hlb : l ≠ b) (hab : a ≠ b)
    (hp3 : A.multiplicity p = 3) :
    ∀ m : Line, A.Incident p m ↔ m = l ∨ m = a ∨ m = b := by
  classical
  let I : Finset Line := Finset.univ.filter fun m => A.Incident p m
  have hIcard : I.card = 3 := by
    simpa only [I, multiplicity] using hp3
  have hsub : ({l, a, b} : Finset Line) ⊆ I := by
    intro m hm
    simp only [Finset.mem_insert, Finset.mem_singleton] at hm
    rcases hm with rfl | rfl | rfl
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hpl⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hpa⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hpb⟩
  have hsetCard : ({l, a, b} : Finset Line).card = 3 := by
    simp [hla, hlb, hab, Ne.symm hla, Ne.symm hlb, Ne.symm hab]
  have hset : ({l, a, b} : Finset Line) = I :=
    Finset.eq_of_subset_of_card_le hsub (by rw [hsetCard, hIcard])
  intro m
  have hmI : A.Incident p m ↔ m ∈ I := by
    simp only [I, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [hmI, ← hset]
  simp only [Finset.mem_insert, Finset.mem_singleton]

/-- Specialized to a marked point on `l`, the unique transverse line also
identifies that point with the literal intersection of the two supports. -/
theorem existsUnique_other_line_at_circularGap_of_multiplicity_eq_two
    (A : FiniteProjectiveLineArrangement Line) (l : Line)
    (p : A.CircularGapSlot l) (hp2 : A.multiplicity p.1 = 2) :
    ∃! a : Line,
      a ≠ l ∧ A.Incident p.1 a ∧ p.1 = A.intersection l a := by
  have hpl : A.Incident p.1 l := ((A.mem_lineVertexSet l).mp p.2).2
  obtain ⟨a, ha, hua⟩ :=
    A.existsUnique_other_incident_line_of_multiplicity_eq_two p.1 l hpl hp2
  refine ⟨a, ⟨ha.1, ha.2, ?_⟩, ?_⟩
  · exact A.eq_intersection_of_incident (Ne.symm ha.1) hpl ha.2
  · intro b hb
    exact hua b ⟨hb.1, hb.2.1⟩

/-- An actual `DD` cyclic gap has two distinct transverse supports `a,b`;
its endpoints are exactly `l ∩ a` and `l ∩ b`. -/
theorem exists_distinct_endpoint_supports_of_circularGap_dd
    (A : FiniteProjectiveLineArrangement Line) (hA : A.NonPencil)
    (l : Line) (p : A.CircularGapSlot l)
    (hp2 : A.multiplicity p.1 = 2)
    (hq2 : A.multiplicity (A.circularGapSuccessor l p).1 = 2) :
    ∃ a b : Line,
      a ≠ l ∧ b ≠ l ∧ a ≠ b ∧
      p.1 = A.intersection l a ∧
      (A.circularGapSuccessor l p).1 = A.intersection l b := by
  obtain ⟨a, ha, _hua⟩ :=
    A.existsUnique_other_line_at_circularGap_of_multiplicity_eq_two l p hp2
  obtain ⟨b, hb, _hub⟩ :=
    A.existsUnique_other_line_at_circularGap_of_multiplicity_eq_two
      l (A.circularGapSuccessor l p) hq2
  refine ⟨a, b, ha.1, hb.1, ?_, ha.2.2, hb.2.2⟩
  intro hab
  apply A.geometricEdge_initial_ne_terminal_of_nonPencil hA
    (A.circularGapEdge l p)
  change p.1 = (A.circularGapSuccessor l p).1
  rw [ha.2.2, hb.2.2, hab]

/-- A triangular face adjacent to an ordinary--ordinary (`DD`) gap has
exactly the gap itself and the two transverse endpoint supports as its three
literal boundary edges.  This is independent of any gallery census and is
the shared local support extractor for Gallery A and Kelly--Rottenberg. -/
theorem exists_exact_triangle_boundary_of_adjacent_circularGap_dd
    (A : FiniteProjectiveLineArrangement Line) (hA : A.NonPencil)
    (l : Line) (p : A.CircularGapSlot l) (F : A.ArrangementFace)
    (hp2 : A.multiplicity p.1 = 2)
    (hq2 : A.multiplicity (A.circularGapSuccessor l p).1 = 2)
    (hF : A.geometricEdgeAdjacentFace (A.circularGapEdge l p) F)
    (htri : (A.arrangementFaceBoundary F).card = 3) :
    ∃ a b : Line, ∃ eP eQ : A.GeometricEdge,
      a ≠ l ∧ b ≠ l ∧ a ≠ b ∧
      p.1 = A.intersection l a ∧
      (A.circularGapSuccessor l p).1 = A.intersection l b ∧
      A.edgeSlotLine eP = a ∧ A.edgeSlotLine eQ = b ∧
      eP ≠ A.circularGapEdge l p ∧
      eQ ≠ A.circularGapEdge l p ∧ eP ≠ eQ ∧
      A.arrangementFaceBoundary F = {A.circularGapEdge l p, eP, eQ} := by
  classical
  let e := A.circularGapEdge l p
  have hpl : A.Incident p.1 l := ((A.mem_lineVertexSet l).mp p.2).2
  have hql : A.Incident (A.circularGapSuccessor l p).1 l :=
    ((A.mem_lineVertexSet l).mp (A.circularGapSuccessor l p).2).2
  obtain ⟨a, ha, _hua⟩ :=
    A.existsUnique_other_line_at_circularGap_of_multiplicity_eq_two l p hp2
  obtain ⟨b, hb, _hub⟩ :=
    A.existsUnique_other_line_at_circularGap_of_multiplicity_eq_two
      l (A.circularGapSuccessor l p) hq2
  have hab : a ≠ b := by
    intro hab
    apply A.geometricEdge_initial_ne_terminal_of_nonPencil hA e
    change p.1 = (A.circularGapSuccessor l p).1
    rw [ha.2.2, hb.2.2, hab]
  have hordinaryP : ∀ m : Line, A.Incident p.1 m ↔ m = l ∨ m = a :=
    A.incident_iff_eq_or_eq_of_multiplicity_eq_two
      p.1 l a hpl ha.2.1 ha.1 hp2
  have hordinaryQ : ∀ m : Line,
      A.Incident (A.circularGapSuccessor l p).1 m ↔ m = l ∨ m = b :=
    A.incident_iff_eq_or_eq_of_multiplicity_eq_two
      (A.circularGapSuccessor l p).1 l b hql hb.2.1 hb.1 hq2
  have hPF : p.1 ∈ closure (A.arrangementFaceCarrier F) := by
    simpa only [e, A.circularGapEdge_initial] using
      A.geometricEdgeInitial_mem_closure_arrangementFaceCarrier_of_adjacent
        hA e F hF
  have hQF : (A.circularGapSuccessor l p).1 ∈
      closure (A.arrangementFaceCarrier F) := by
    simpa only [e, A.circularGapEdge_terminal] using
      A.geometricEdgeTerminal_mem_closure_arrangementFaceCarrier_of_adjacent
        hA e F hF
  obtain ⟨eP, hePline, hePF⟩ :=
    A.exists_transverse_boundaryEdge_of_mem_closure_of_ordinary_intersection
      hA F p.1 l a ha.1 hpl ha.2.1 hordinaryP hPF
  obtain ⟨eQ, heQline, heQF⟩ :=
    A.exists_transverse_boundaryEdge_of_mem_closure_of_ordinary_intersection
      hA F (A.circularGapSuccessor l p).1 l b hb.1 hql hb.2.1
        hordinaryQ hQF
  have hePF' : eP ∈ A.arrangementFaceBoundary F := hePF
  have heQF' : eQ ∈ A.arrangementFaceBoundary F := heQF
  have heF : e ∈ A.arrangementFaceBoundary F :=
    (A.mem_arrangementFaceBoundary_iff F e).2 hF
  have hePne : eP ≠ e := by
    intro hEq
    apply ha.1
    calc
      a = A.edgeSlotLine eP := hePline.symm
      _ = A.edgeSlotLine e := congrArg A.edgeSlotLine hEq
      _ = l := A.circularGapEdge_line l p
  have heQne : eQ ≠ e := by
    intro hEq
    apply hb.1
    calc
      b = A.edgeSlotLine eQ := heQline.symm
      _ = A.edgeSlotLine e := congrArg A.edgeSlotLine hEq
      _ = l := A.circularGapEdge_line l p
  have hePQ : eP ≠ eQ := by
    intro hEq
    apply hab
    calc
      a = A.edgeSlotLine eP := hePline.symm
      _ = A.edgeSlotLine eQ := congrArg A.edgeSlotLine hEq
      _ = b := heQline
  have hsub : ({e, eP, eQ} : Finset A.GeometricEdge) ⊆
      A.arrangementFaceBoundary F := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl
    · exact heF
    · exact hePF'
    · exact heQF'
  have htriple : ({e, eP, eQ} : Finset A.GeometricEdge).card = 3 := by
    simp [hePne, heQne, hePQ, Ne.symm hePne, Ne.symm heQne]
  have hboundary : A.arrangementFaceBoundary F = {e, eP, eQ} := by
    symm
    apply Finset.eq_of_subset_of_card_le hsub
    rw [htri, htriple]
  refine ⟨a, b, eP, eQ, ha.1, hb.1, hab, ha.2.2, hb.2.2,
    hePline, heQline, ?_, ?_, hePQ, ?_⟩
  · simpa only [e] using hePne
  · simpa only [e] using heQne
  · simpa only [e] using hboundary

/-- Unconditional ordinary--ordinary edge lemma for an actual simplicial
real projective arrangement: a `DD` cyclic gap forces every line away from
its support to pass through the opposite vertex of either adjacent
triangle. -/
theorem exists_concurrent_away_of_circularGap_dd_of_all_faces_triangular
    (A : FiniteProjectiveLineArrangement Line) (hA : A.NonPencil)
    (l : Line) (p : A.CircularGapSlot l)
    (hp2 : A.multiplicity p.1 = 2)
    (hq2 : A.multiplicity (A.circularGapSuccessor l p).1 = 2)
    (htri : ∀ F : A.ArrangementFace,
      (A.arrangementFaceBoundary F).card = 3) :
    ∃ r : RealProjectivePoint,
      ∀ m : Line, m ≠ l → A.Incident r m := by
  classical
  let e := A.circularGapEdge l p
  obtain ⟨q, hq⟩ := (A.isPathConnected_geometricEdgeOpenArc hA e).nonempty
  obtain ⟨F, G, hFG, hF, hG⟩ :=
    A.exists_two_distinct_geometricEdgeAdjacentFaces_at hA e hq
  obtain ⟨a, b, eP, eQ, hal, hbl, hab, hp, hq', heP, heQ,
      _hePne, _heQne, _hePQ, hboundaryF⟩ :=
    A.exists_exact_triangle_boundary_of_adjacent_circularGap_dd
      hA l p F hp2 hq2 hF (htri F)
  obtain ⟨c, d, eP', eQ', hcl, hdl, _hcd, hp', hq'', heP', heQ',
      _hePne', _heQne', _hePQ', hboundaryG⟩ :=
    A.exists_exact_triangle_boundary_of_adjacent_circularGap_dd
      hA l p G hp2 hq2 hG (htri G)
  have hpl : A.Incident p.1 l := ((A.mem_lineVertexSet l).mp p.2).2
  have hpa : A.Incident p.1 a := by
    rw [hp]
    exact A.intersection_incident_right hal.symm
  have hpc : A.Incident p.1 c := by
    rw [hp']
    exact A.intersection_incident_right hcl.symm
  have hca : c = a := by
    have hord := A.incident_iff_eq_or_eq_of_multiplicity_eq_two
      p.1 l a hpl hpa hal hp2
    exact Or.resolve_left ((hord c).mp hpc) hcl
  have hql : A.Incident (A.circularGapSuccessor l p).1 l :=
    ((A.mem_lineVertexSet l).mp (A.circularGapSuccessor l p).2).2
  have hqb : A.Incident (A.circularGapSuccessor l p).1 b := by
    rw [hq']
    exact A.intersection_incident_right hbl.symm
  have hqd : A.Incident (A.circularGapSuccessor l p).1 d := by
    rw [hq'']
    exact A.intersection_incident_right hdl.symm
  have hdb : d = b := by
    have hord := A.incident_iff_eq_or_eq_of_multiplicity_eq_two
      (A.circularGapSuccessor l p).1 l b hql hqb hbl hq2
    exact Or.resolve_left ((hord d).mp hqd) hdl
  have heP'a : A.edgeSlotLine eP' = a := heP'.trans hca
  have heQ'b : A.edgeSlotLine eQ' = b := heQ'.trans hdb
  refine ⟨A.intersection a b, ?_⟩
  intro m hml
  apply A.incident_intersection_of_two_exact_opposite_triangles
    hA e eP eQ eP' eQ' l a b m F G
  · exact A.circularGapEdge_line l p
  · exact heP
  · exact heQ
  · exact heP'a
  · exact heQ'b
  · exact hal
  · exact hbl
  · exact hab
  · exact hF
  · exact hG
  · exact hFG
  · simpa only [e] using hboundaryF
  · simpa only [e] using hboundaryG
  · exact hml

end FiniteProjectiveLineArrangement

end Erdos506.Incidence
