import Erdos506.Incidence.RealProjectiveArrangementKellyMoserFinish

/-!
# The two-vertex-line branch of Kelly--Moser

If one line of a non-pencil arrangement has only two actual vertices, every
other indexed line belongs to one of the two pencils based at those vertices.
Every cross-pair of pencil lines then produces a different ordinary vertex.
This is the elementary low-line branch complementary to the triangular-face
attachment argument.
-/

namespace Erdos506.Incidence

namespace FiniteProjectiveLineArrangement

variable {Line : Type*} [Fintype Line] [DecidableEq Line]

noncomputable local instance realProjectivePointDecidableEqForKellyMoserLowLine :
    DecidableEq RealProjectivePoint :=
  Classical.decEq _

/-- Lines other than `l` passing through the selected vertex `p` of `l`. -/
noncomputable def lowLineClassAt
    (A : FiniteProjectiveLineArrangement Line)
    (l : Line) (p : RealProjectivePoint) : Finset Line := by
  classical
  exact (Finset.univ.erase l).filter fun m => A.Incident p m

@[simp]
theorem mem_lowLineClassAt
    (A : FiniteProjectiveLineArrangement Line)
    (l m : Line) (p : RealProjectivePoint) :
    m ∈ A.lowLineClassAt l p ↔ m ≠ l ∧ A.Incident p m := by
  classical
  simp [lowLineClassAt]

/-- Two different vertices on `l` define disjoint classes of transverse
lines. -/
theorem disjoint_lowLineClassAt
    (A : FiniteProjectiveLineArrangement Line)
    (l : Line) {p q : RealProjectivePoint}
    (hpq : p ≠ q) (hpl : A.Incident p l) (hql : A.Incident q l) :
    Disjoint (A.lowLineClassAt l p) (A.lowLineClassAt l q) := by
  classical
  rw [Finset.disjoint_left]
  intro m hmp hmq
  have hp := (A.mem_lowLineClassAt l m p).mp hmp
  have hq := (A.mem_lowLineClassAt l m q).mp hmq
  have hlm : l ≠ m := hp.1.symm
  have hpI : p = A.intersection l m :=
    A.eq_intersection_of_incident hlm hpl hp.2
  have hqI : q = A.intersection l m :=
    A.eq_intersection_of_incident hlm hql hq.2
  exact hpq (hpI.trans hqI.symm)

/-- If `p,q` are all the marked vertices on `l`, their two transverse
classes partition every indexed line except `l`. -/
theorem union_lowLineClassAt_eq_erase
    (A : FiniteProjectiveLineArrangement Line)
    (l : Line) {p q : RealProjectivePoint}
    (hvertices : A.lineVertexSet l = {p, q}) :
    A.lowLineClassAt l p ∪ A.lowLineClassAt l q = Finset.univ.erase l := by
  classical
  apply Finset.Subset.antisymm
  · intro m hm
    simp only [Finset.mem_union] at hm
    rcases hm with hm | hm
    · exact Finset.mem_erase.mpr
        ⟨((A.mem_lowLineClassAt l m p).mp hm).1, Finset.mem_univ _⟩
    · exact Finset.mem_erase.mpr
        ⟨((A.mem_lowLineClassAt l m q).mp hm).1, Finset.mem_univ _⟩
  · intro m hm
    have hml : m ≠ l := (Finset.mem_erase.mp hm).1
    have hvertex : A.intersection l m ∈ A.lineVertexSet l :=
      A.intersection_mem_lineVertexSet_left hml.symm
    rw [hvertices] at hvertex
    simp only [Finset.mem_insert, Finset.mem_singleton] at hvertex
    simp only [Finset.mem_union]
    rcases hvertex with hI | hI
    · left
      apply (A.mem_lowLineClassAt l m p).mpr
      refine ⟨hml, ?_⟩
      rw [← hI]
      exact A.intersection_incident_right hml.symm
    · right
      apply (A.mem_lowLineClassAt l m q).mpr
      refine ⟨hml, ?_⟩
      rw [← hI]
      exact A.intersection_incident_right hml.symm

/-- Each of the two transverse classes at an actual vertex of `l` is
nonempty. -/
theorem lowLineClassAt_nonempty_of_mem_lineVertexSet
    (A : FiniteProjectiveLineArrangement Line)
    (l : Line) {p : RealProjectivePoint}
    (hp : p ∈ A.lineVertexSet l) :
    (A.lowLineClassAt l p).Nonempty := by
  classical
  have hpVertex := ((A.mem_lineVertexSet l).mp hp).1
  obtain ⟨a, b, hab, hI⟩ := A.exists_lines_of_mem_vertexSet hpVertex
  have hpa : A.Incident p a := by
    rw [← hI]
    exact A.intersection_incident_left hab
  have hpb : A.Incident p b := by
    rw [← hI]
    exact A.intersection_incident_right hab
  by_cases hal : a = l
  · have hbl : b ≠ l := by
      intro hbl
      apply hab
      exact hal.trans hbl.symm
    exact ⟨b, (A.mem_lowLineClassAt l b p).mpr ⟨hbl, hpb⟩⟩
  · exact ⟨a, (A.mem_lowLineClassAt l a p).mpr ⟨hal, hpa⟩⟩

/-- A line from the `p`-class and a line from the `q`-class are different. -/
theorem lowLine_cross_lines_ne
    (A : FiniteProjectiveLineArrangement Line)
    (l : Line) {p q : RealProjectivePoint}
    (hpq : p ≠ q) (hpl : A.Incident p l) (hql : A.Incident q l)
    {a b : Line}
    (ha : a ∈ A.lowLineClassAt l p)
    (hb : b ∈ A.lowLineClassAt l q) :
    a ≠ b := by
  intro hab
  subst b
  have hdisj := A.disjoint_lowLineClassAt l hpq hpl hql
  exact (Finset.disjoint_left.mp hdisj ha hb)

/-- A cross-intersection of the two transverse classes does not lie back on
the distinguished line. -/
theorem not_incident_lowLine_cross
    (A : FiniteProjectiveLineArrangement Line)
    (l : Line) {p q : RealProjectivePoint}
    (hpq : p ≠ q) (hpl : A.Incident p l) (hql : A.Incident q l)
    {a b : Line}
    (ha : a ∈ A.lowLineClassAt l p)
    (hb : b ∈ A.lowLineClassAt l q) :
    ¬ A.Incident (A.intersection a b) l := by
  intro hrl
  have ha' := (A.mem_lowLineClassAt l a p).mp ha
  have hb' := (A.mem_lowLineClassAt l b q).mp hb
  have hab : a ≠ b := A.lowLine_cross_lines_ne l hpq hpl hql ha hb
  have hla : l ≠ a := ha'.1.symm
  have hlb : l ≠ b := hb'.1.symm
  have hpI : p = A.intersection l a :=
    A.eq_intersection_of_incident hla hpl ha'.2
  have hrIa : A.intersection a b = A.intersection l a :=
    A.eq_intersection_of_incident hla hrl
      (A.intersection_incident_left hab)
  have hqI : q = A.intersection l b :=
    A.eq_intersection_of_incident hlb hql hb'.2
  have hrIb : A.intersection a b = A.intersection l b :=
    A.eq_intersection_of_incident hlb hrl
      (A.intersection_incident_right hab)
  apply hpq
  exact hpI.trans (hrIa.symm.trans (hrIb.trans hqI.symm))

/-- The cross-intersection of the two pencil classes is ordinary: its only
incident indexed lines are the two defining cross-lines. -/
theorem incident_lowLine_cross_iff
    (A : FiniteProjectiveLineArrangement Line)
    (l : Line) {p q : RealProjectivePoint}
    (hpq : p ≠ q) (hpl : A.Incident p l) (hql : A.Incident q l)
    (hvertices : A.lineVertexSet l = {p, q})
    {a b : Line}
    (ha : a ∈ A.lowLineClassAt l p)
    (hb : b ∈ A.lowLineClassAt l q) :
    ∀ c : Line, A.Incident (A.intersection a b) c ↔ c = a ∨ c = b := by
  have ha' := (A.mem_lowLineClassAt l a p).mp ha
  have hb' := (A.mem_lowLineClassAt l b q).mp hb
  have hab : a ≠ b := A.lowLine_cross_lines_ne l hpq hpl hql ha hb
  have hrl : ¬ A.Incident (A.intersection a b) l :=
    A.not_incident_lowLine_cross l hpq hpl hql ha hb
  intro c
  constructor
  · intro hrc
    have hcl : c ≠ l := by
      intro hcl
      subst c
      exact hrl hrc
    have hcErase : c ∈ (Finset.univ : Finset Line).erase l :=
      Finset.mem_erase.mpr ⟨hcl, Finset.mem_univ _⟩
    have hcUnion : c ∈ A.lowLineClassAt l p ∪ A.lowLineClassAt l q := by
      rw [A.union_lowLineClassAt_eq_erase l hvertices]
      exact hcErase
    simp only [Finset.mem_union] at hcUnion
    rcases hcUnion with hcP | hcQ
    · left
      by_contra hca
      have hc' := (A.mem_lowLineClassAt l c p).mp hcP
      have hpI : p = A.intersection c a :=
        A.eq_intersection_of_incident hca hc'.2 ha'.2
      have hrI : A.intersection a b = A.intersection c a :=
        A.eq_intersection_of_incident hca hrc
          (A.intersection_incident_left hab)
      have hpr : p = A.intersection a b := hpI.trans hrI.symm
      exact hrl (hpr ▸ hpl)
    · right
      by_contra hcb
      have hc' := (A.mem_lowLineClassAt l c q).mp hcQ
      have hqI : q = A.intersection c b :=
        A.eq_intersection_of_incident hcb hc'.2 hb'.2
      have hrI : A.intersection a b = A.intersection c b :=
        A.eq_intersection_of_incident hcb hrc
          (A.intersection_incident_right hab)
      have hqr : q = A.intersection a b := hqI.trans hrI.symm
      exact hrl (hqr ▸ hql)
  · rintro (rfl | rfl)
    · exact A.intersection_incident_left hab
    · exact A.intersection_incident_right hab

/-- Every cross-intersection belongs to the actual ordinary-vertex set. -/
theorem lowLine_cross_mem_ordinaryVertexSet
    (A : FiniteProjectiveLineArrangement Line)
    (l : Line) {p q : RealProjectivePoint}
    (hpq : p ≠ q) (hpl : A.Incident p l) (hql : A.Incident q l)
    (hvertices : A.lineVertexSet l = {p, q})
    {a b : Line}
    (ha : a ∈ A.lowLineClassAt l p)
    (hb : b ∈ A.lowLineClassAt l q) :
    A.intersection a b ∈ A.ordinaryVertexSet := by
  classical
  have hab : a ≠ b := A.lowLine_cross_lines_ne l hpq hpl hql ha hb
  have hincident :=
    A.incident_lowLine_cross_iff l hpq hpl hql hvertices ha hb
  apply Finset.mem_filter.mpr
  refine ⟨A.intersection_mem_vertexSet hab, ?_⟩
  unfold multiplicity
  have hset :
      (Finset.univ.filter fun c : Line =>
        A.Incident (A.intersection a b) c) = {a, b} := by
    ext c
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_insert, Finset.mem_singleton]
    exact hincident c
  rw [hset]
  simp [hab]

/-- Bundle the cross-intersection as an ordinary vertex. -/
noncomputable def lowLineCrossOrdinaryVertex
    (A : FiniteProjectiveLineArrangement Line)
    (l : Line) {p q : RealProjectivePoint}
    (hpq : p ≠ q) (hpl : A.Incident p l) (hql : A.Incident q l)
    (hvertices : A.lineVertexSet l = {p, q})
    (ab : {a // a ∈ A.lowLineClassAt l p} ×
      {b // b ∈ A.lowLineClassAt l q}) : A.OrdinaryVertex :=
  ⟨A.intersection ab.1.1 ab.2.1,
    A.lowLine_cross_mem_ordinaryVertexSet l hpq hpl hql hvertices
      ab.1.2 ab.2.2⟩

@[simp]
theorem lowLineCrossOrdinaryVertex_val
    (A : FiniteProjectiveLineArrangement Line)
    (l : Line) {p q : RealProjectivePoint}
    (hpq : p ≠ q) (hpl : A.Incident p l) (hql : A.Incident q l)
    (hvertices : A.lineVertexSet l = {p, q})
    (ab : {a // a ∈ A.lowLineClassAt l p} ×
      {b // b ∈ A.lowLineClassAt l q}) :
    (A.lowLineCrossOrdinaryVertex l hpq hpl hql hvertices ab).1 =
      A.intersection ab.1.1 ab.2.1 :=
  rfl

/-- Different cross-pairs give different ordinary vertices. -/
theorem lowLineCrossOrdinaryVertex_injective
    (A : FiniteProjectiveLineArrangement Line)
    (l : Line) {p q : RealProjectivePoint}
    (hpq : p ≠ q) (hpl : A.Incident p l) (hql : A.Incident q l)
    (hvertices : A.lineVertexSet l = {p, q}) :
    Function.Injective
      (A.lowLineCrossOrdinaryVertex l hpq hpl hql hvertices) := by
  classical
  intro x y hxy
  have hval := congrArg Subtype.val hxy
  change A.intersection x.1.1 x.2.1 =
    A.intersection y.1.1 y.2.1 at hval
  have hxab : x.1.1 ≠ x.2.1 :=
    A.lowLine_cross_lines_ne l hpq hpl hql x.1.2 x.2.2
  have hyab : y.1.1 ≠ y.2.1 :=
    A.lowLine_cross_lines_ne l hpq hpl hql y.1.2 y.2.2
  have hxSupport := A.incident_lowLine_cross_iff l hpq hpl hql
    hvertices x.1.2 x.2.2
  have hySupport := A.incident_lowLine_cross_iff l hpq hpl hql
    hvertices y.1.2 y.2.2
  have hyLeftAtX : A.Incident (A.intersection x.1.1 x.2.1) y.1.1 := by
    rw [hval]
    exact A.intersection_incident_left hyab
  have hyRightAtX : A.Incident (A.intersection x.1.1 x.2.1) y.2.1 := by
    rw [hval]
    exact A.intersection_incident_right hyab
  have hleft : y.1.1 = x.1.1 := by
    rcases (hxSupport y.1.1).mp hyLeftAtX with h | h
    · exact h
    · exfalso
      have hdisj := A.disjoint_lowLineClassAt l hpq hpl hql
      exact Finset.disjoint_left.mp hdisj y.1.2 (h.symm ▸ x.2.2)
  have hright : y.2.1 = x.2.1 := by
    rcases (hxSupport y.2.1).mp hyRightAtX with h | h
    · exfalso
      have hdisj := A.disjoint_lowLineClassAt l hpq hpl hql
      exact Finset.disjoint_left.mp hdisj x.1.2 (h ▸ y.2.2)
    · exact h
  apply Prod.ext
  · exact Subtype.ext hleft.symm
  · exact Subtype.ext hright.symm

/-- The two transverse classes have total size `#Line - 1`. -/
theorem card_lowLineClassAt_add_card
    (A : FiniteProjectiveLineArrangement Line)
    (l : Line) {p q : RealProjectivePoint}
    (hpq : p ≠ q) (hpl : A.Incident p l) (hql : A.Incident q l)
    (hvertices : A.lineVertexSet l = {p, q}) :
    (A.lowLineClassAt l p).card + (A.lowLineClassAt l q).card =
      Fintype.card Line - 1 := by
  classical
  have hdisj := A.disjoint_lowLineClassAt l hpq hpl hql
  have hunion := A.union_lowLineClassAt_eq_erase l hvertices
  calc
    (A.lowLineClassAt l p).card + (A.lowLineClassAt l q).card =
        (A.lowLineClassAt l p ∪ A.lowLineClassAt l q).card := by
          exact (Finset.card_union_of_disjoint hdisj).symm
    _ = ((Finset.univ : Finset Line).erase l).card := congrArg Finset.card hunion
    _ = Fintype.card Line - 1 := by simp

/-- The product of the two class sizes is at least `#Line - 2`. -/
theorem card_sub_two_le_lowLineClassAt_mul_card
    (A : FiniteProjectiveLineArrangement Line)
    (l : Line) {p q : RealProjectivePoint}
    (hpq : p ≠ q) (hpl : A.Incident p l) (hql : A.Incident q l)
    (hpp : p ∈ A.lineVertexSet l) (hqq : q ∈ A.lineVertexSet l)
    (hvertices : A.lineVertexSet l = {p, q}) :
    Fintype.card Line - 2 ≤
      (A.lowLineClassAt l p).card * (A.lowLineClassAt l q).card := by
  classical
  let P := A.lowLineClassAt l p
  let Q := A.lowLineClassAt l q
  have hPpos : 0 < P.card :=
    Finset.card_pos.mpr (A.lowLineClassAt_nonempty_of_mem_lineVertexSet l hpp)
  have hQpos : 0 < Q.card :=
    Finset.card_pos.mpr (A.lowLineClassAt_nonempty_of_mem_lineVertexSet l hqq)
  have hsum : P.card + Q.card = Fintype.card Line - 1 := by
    simpa only [P, Q] using
      A.card_lowLineClassAt_add_card l hpq hpl hql hvertices
  obtain ⟨u, hu⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : P.card ≠ 0)
  obtain ⟨v, hv⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : Q.card ≠ 0)
  rw [hu, hv] at hsum ⊢
  have hnonneg : u + v + 1 ≤ u * v + (u + v + 1) :=
    Nat.le_add_left _ _
  have hmul : (u + 1) * (v + 1) = u * v + (u + v + 1) := by
    ring
  have hcard : Fintype.card Line - 2 = u + v + 1 := by omega
  rw [hcard, hmul]
  omega

/-- Cross-pair counting injects the product of the two pencil classes into
the set of ordinary vertices. -/
theorem lowLineClassAt_mul_card_le_card_ordinaryVertex
    (A : FiniteProjectiveLineArrangement Line)
    (l : Line) {p q : RealProjectivePoint}
    (hpq : p ≠ q) (hpl : A.Incident p l) (hql : A.Incident q l)
    (hvertices : A.lineVertexSet l = {p, q}) :
    (A.lowLineClassAt l p).card * (A.lowLineClassAt l q).card ≤
      Fintype.card A.OrdinaryVertex := by
  classical
  let f := A.lowLineCrossOrdinaryVertex l hpq hpl hql hvertices
  have hinj : Function.Injective f := by
    simpa only [f] using
      A.lowLineCrossOrdinaryVertex_injective l hpq hpl hql hvertices
  have hcard := Fintype.card_le_of_injective f hinj
  simpa only [Fintype.card_prod, Fintype.card_coe] using hcard

/-- The Kelly--Moser inequality in the low-line branch. -/
theorem three_mul_card_le_seven_mul_card_ordinaryVertex_of_lineVertexSet_card_le_two
    (A : FiniteProjectiveLineArrangement Line) (hA : A.NonPencil)
    (hfour : 4 ≤ Fintype.card Line)
    (l : Line) (hlow : (A.lineVertexSet l).card ≤ 2) :
    3 * Fintype.card Line ≤ 7 * Fintype.card A.OrdinaryVertex := by
  classical
  have hslot : 1 < Fintype.card (A.CircularGapSlot l) :=
    A.one_lt_card_circularGapSlot_of_nonPencil hA l
  have hslotCard :
      Fintype.card (A.CircularGapSlot l) = (A.lineVertexSet l).card := by
    exact Fintype.card_coe (A.lineVertexSet l)
  have hlineCard : (A.lineVertexSet l).card = 2 := by omega
  obtain ⟨p, q, hpq, hvertices⟩ := Finset.card_eq_two.mp hlineCard
  have hpp : p ∈ A.lineVertexSet l := by
    rw [hvertices]
    simp
  have hqq : q ∈ A.lineVertexSet l := by
    rw [hvertices]
    simp
  have hpl : A.Incident p l := ((A.mem_lineVertexSet l).mp hpp).2
  have hql : A.Incident q l := ((A.mem_lineVertexSet l).mp hqq).2
  have hproductLower :=
    A.card_sub_two_le_lowLineClassAt_mul_card l hpq hpl hql
      hpp hqq hvertices
  have hproductUpper :=
    A.lowLineClassAt_mul_card_le_card_ordinaryVertex l hpq hpl hql
      hvertices
  have hord : Fintype.card Line - 2 ≤ Fintype.card A.OrdinaryVertex :=
    le_trans hproductLower hproductUpper
  have hscaled :
      7 * (Fintype.card Line - 2) ≤
        7 * Fintype.card A.OrdinaryVertex :=
    Nat.mul_le_mul_left 7 hord
  omega

end FiniteProjectiveLineArrangement

end Erdos506.Incidence
