import Erdos506.Incidence.RealProjectiveArrangementTopology
import Erdos506.Incidence.CellulationTwoColorExcess
import Mathlib.Algebra.Group.Nat.Even

/-!
# The parity colouring of an even real projective arrangement

For a chosen base line, a genuine complement face has a finite normalized
Boolean sign word.  We colour it by the parity of the number of `true`
coordinates.  Changing the base either leaves the whole word fixed or
negates every coordinate.  Hence, when the number of indexed lines is even,
the colour is independent of the base.

At a regular point of a geometric edge and with a transverse base, closure
continuity fixes every coordinate except the supporting-line coordinate.
The two incident faces are distinct, so injectivity of the sign word forces
that last coordinate to flip.  This gives exactly one incident face of each
colour at every geometric edge.
-/

namespace Erdos506.Incidence

namespace FiniteProjectiveLineArrangement

universe u

variable {Line : Type u} [Fintype Line] [DecidableEq Line]

noncomputable local instance realProjectivePointTopologicalSpaceForEvenColor :
    TopologicalSpace RealProjectivePoint :=
  realProjectivePointQuotientTopology

private def boolTrueCount (sigma : Line -> Bool) : Nat :=
  (Finset.univ.filter fun l : Line => sigma l = true).card

/-- The number of positive coordinates in the normalized sign word of an
actual arrangement face. -/
noncomputable def arrangementFaceSignTrueCount
    (A : FiniteProjectiveLineArrangement Line) (base : Line)
    (F : A.ArrangementFace) : Nat :=
  boolTrueCount (A.arrangementFaceSignPattern base F)

/-- The face colour supplied by the parity of its normalized sign word.
The choice of `Even` rather than `Odd` only names the two Boolean colours;
the edge theorem below is insensitive to that convention. -/
noncomputable def arrangementFaceParityColor
    (A : FiniteProjectiveLineArrangement Line) (base : Line)
    (F : A.ArrangementFace) : Bool :=
  decide (Even (A.arrangementFaceSignTrueCount base F))

private theorem signCode_base_change
    (a b c : SignType) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) :
    decide (b * c = 1) =
      if decide (a * b = 1) then
        decide (a * c = 1)
      else
        !(decide (a * c = 1)) := by
  cases a <;> cases b <;> cases c <;> simp_all

/-- Pointwise change-of-base formula for normalized sign words.  According
to the sign relating the two bases, every coordinate is either retained or
every coordinate is negated. -/
theorem arrangementPointSignPattern_base_change_apply
    (A : FiniteProjectiveLineArrangement Line)
    (base other : Line) (p : A.ArrangementComplement) (l : Line) :
    A.arrangementPointSignPattern other p l =
      if A.arrangementPointSignPattern base p other then
        A.arrangementPointSignPattern base p l
      else
        !(A.arrangementPointSignPattern base p l) := by
  rw [A.arrangementPointSignPattern_eq_relativeSign other p,
    A.arrangementPointSignPattern_eq_relativeSign base p]
  simp only [A.arrangementRelativeSign_apply_rep, sign_mul]
  apply signCode_base_change
  · exact sign_ne_zero.mpr
      (A.projectiveLineEvaluation_rep_ne_zero p base)
  · exact sign_ne_zero.mpr
      (A.projectiveLineEvaluation_rep_ne_zero p other)
  · exact sign_ne_zero.mpr
      (A.projectiveLineEvaluation_rep_ne_zero p l)

/-- Face-level form of the pointwise change-of-base formula. -/
theorem arrangementFaceSignPattern_base_change_apply
    (A : FiniteProjectiveLineArrangement Line)
    (base other : Line) (F : A.ArrangementFace) (l : Line) :
    A.arrangementFaceSignPattern other F l =
      if A.arrangementFaceSignPattern base F other then
        A.arrangementFaceSignPattern base F l
      else
        !(A.arrangementFaceSignPattern base F l) := by
  exact A.arrangementPointSignPattern_base_change_apply base other
    (A.arrangementFaceRepresentative F) l

private theorem boolTrueCount_add_boolTrueCount_not
    (sigma : Line -> Bool) :
    boolTrueCount sigma + boolTrueCount (fun l => !(sigma l)) =
      Fintype.card Line := by
  classical
  simpa [boolTrueCount] using
    (Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset Line))
      (p := fun l : Line => sigma l = true))

private theorem boolEvenColor_eq_boolEvenColor_not
    (heven : Even (Fintype.card Line)) (sigma : Line -> Bool) :
    decide (Even (boolTrueCount sigma)) =
      decide (Even (boolTrueCount (fun l => !(sigma l)))) := by
  have hsum : Even
      (boolTrueCount sigma + boolTrueCount (fun l => !(sigma l))) := by
    rw [boolTrueCount_add_boolTrueCount_not sigma]
    exact heven
  exact Bool.decide_congr (Nat.even_add.mp hsum)

/-- For an even number of indexed lines, the parity colour is independent
of the base used to normalize the homogeneous sign word. -/
theorem arrangementFaceParityColor_base_independent
    (A : FiniteProjectiveLineArrangement Line)
    (heven : Even (Fintype.card Line))
    (base other : Line) (F : A.ArrangementFace) :
    A.arrangementFaceParityColor base F =
      A.arrangementFaceParityColor other F := by
  classical
  by_cases hbaseOther : A.arrangementFaceSignPattern base F other = true
  · have hpatterns : A.arrangementFaceSignPattern other F =
        A.arrangementFaceSignPattern base F := by
      funext l
      rw [A.arrangementFaceSignPattern_base_change_apply base other F l]
      simp [hbaseOther]
    simp only [arrangementFaceParityColor, arrangementFaceSignTrueCount,
      hpatterns]
    exact Bool.decide_congr Iff.rfl
  · have hbaseOtherFalse :
        A.arrangementFaceSignPattern base F other = false :=
      Bool.eq_false_of_not_eq_true hbaseOther
    have hpatterns : A.arrangementFaceSignPattern other F =
        fun l => !(A.arrangementFaceSignPattern base F l) := by
      funext l
      rw [A.arrangementFaceSignPattern_base_change_apply base other F l]
      simp [hbaseOtherFalse]
    simp only [arrangementFaceParityColor, arrangementFaceSignTrueCount,
      hpatterns]
    exact boolEvenColor_eq_boolEvenColor_not heven
      (A.arrangementFaceSignPattern base F)

private theorem boolEvenColor_ne_of_single_flip
    (sigma tau : Line -> Bool) (x : Line)
    (hoff : forall y : Line, y ≠ x -> sigma y = tau y)
    (hx : sigma x ≠ tau x) :
    decide (Even (boolTrueCount sigma)) ≠
      decide (Even (boolTrueCount tau)) := by
  classical
  let rest : Finset Line := Finset.univ.erase x
  have hxrest : x ∉ rest := by simp [rest]
  have huniv : (Finset.univ : Finset Line) = insert x rest := by
    exact (Finset.insert_erase (Finset.mem_univ x)).symm
  have hrest :
      (rest.filter fun y : Line => sigma y = true) =
        rest.filter fun y : Line => tau y = true := by
    ext y
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hy, hsig⟩
      have hyx : y ≠ x := (Finset.mem_erase.mp hy).1
      exact ⟨hy, by simpa only [hoff y hyx] using hsig⟩
    · rintro ⟨hy, htau⟩
      have hyx : y ≠ x := (Finset.mem_erase.mp hy).1
      exact ⟨hy, by simpa only [hoff y hyx] using htau⟩
  have hxfilter (rho : Line → Bool) :
      x ∉ rest.filter (fun y : Line => rho y = true) := by
    intro hxmem
    exact hxrest (Finset.mem_filter.mp hxmem).1
  have hcounts :
      boolTrueCount sigma = boolTrueCount tau + 1 ∨
        boolTrueCount tau = boolTrueCount sigma + 1 := by
    cases hsx : sigma x <;> cases htx : tau x
    · exfalso
      exact hx (by rw [hsx, htx])
    · right
      unfold boolTrueCount
      rw [huniv, Finset.filter_insert, Finset.filter_insert]
      rw [if_pos (by simp [htx]), if_neg (by simp [hsx])]
      rw [← hrest, Finset.card_insert_of_notMem (hxfilter sigma)]
    · left
      unfold boolTrueCount
      rw [huniv, Finset.filter_insert, Finset.filter_insert]
      rw [if_pos (by simp [hsx]), if_neg (by simp [htx])]
      rw [hrest, Finset.card_insert_of_notMem (hxfilter tau)]
    · exfalso
      exact hx (by rw [hsx, htx])
  rcases hcounts with hcount | hcount
  · have hparity : Even (boolTrueCount sigma) ↔
        ¬ Even (boolTrueCount tau) := by
      rw [hcount, Nat.even_add_one]
    by_cases htau : Even (boolTrueCount tau)
    · have hsigma : ¬ Even (boolTrueCount sigma) := by
        intro hsigma
        exact (hparity.mp hsigma) htau
      simp [htau, hsigma]
    · have hsigma : Even (boolTrueCount sigma) := hparity.mpr htau
      simp [htau, hsigma]
  · have hparity : Even (boolTrueCount tau) ↔
        ¬ Even (boolTrueCount sigma) := by
      rw [hcount, Nat.even_add_one]
    by_cases hsigma : Even (boolTrueCount sigma)
    · have htau : ¬ Even (boolTrueCount tau) := by
        intro htau
        exact (hparity.mp htau) hsigma
      simp [hsigma, htau]
    · have htau : Even (boolTrueCount tau) := hparity.mpr hsigma
      simp [hsigma, htau]

/-- With a base transverse to a regular line point, two distinct faces in
the point closure receive opposite parity colours. -/
theorem arrangementFaceParityColor_ne_of_mem_closure_of_regular
    (A : FiniteProjectiveLineArrangement Line)
    (q : RealProjectivePoint) (support base : Line)
    (hregular : forall m : Line, A.Incident q m ↔ m = support)
    (hbase : base ≠ support)
    (F G : A.ArrangementFace)
    (hF : q ∈ closure (A.arrangementFaceCarrier F))
    (hG : q ∈ closure (A.arrangementFaceCarrier G))
    (hFG : F ≠ G) :
    A.arrangementFaceParityColor base F ≠
      A.arrangementFaceParityColor base G := by
  have hoff (m : Line) (hm : m ≠ support) :
      A.arrangementFaceSignPattern base F m =
        A.arrangementFaceSignPattern base G m := by
    change A.arrangementPointSignPattern base
        (A.arrangementFaceRepresentative F) m =
      A.arrangementPointSignPattern base
        (A.arrangementFaceRepresentative G) m
    rw [A.arrangementPointSignPattern_eq_relativeSign base
        (A.arrangementFaceRepresentative F),
      A.arrangementPointSignPattern_eq_relativeSign base
        (A.arrangementFaceRepresentative G)]
    apply Bool.decide_congr
    have hqbase : ¬ A.Incident q base := by
      intro hqb
      exact hbase ((hregular base).mp hqb)
    have hqm : ¬ A.Incident q m := by
      intro hq
      exact hm ((hregular m).mp hq)
    rw [A.arrangementRelativeSign_arrangementFaceRepresentative_eq_of_mem_closure
        q base m F hqbase hqm hF,
      A.arrangementRelativeSign_arrangementFaceRepresentative_eq_of_mem_closure
        q base m G hqbase hqm hG]
  have hsupport :
      A.arrangementFaceSignPattern base F support ≠
        A.arrangementFaceSignPattern base G support := by
    intro heq
    apply hFG
    apply A.arrangementFaceSignPattern_injective base
    funext m
    by_cases hm : m = support
    · simpa only [hm] using heq
    · exact hoff m hm
  simpa only [arrangementFaceParityColor, arrangementFaceSignTrueCount] using
    (boolEvenColor_ne_of_single_flip
      (A.arrangementFaceSignPattern base F)
      (A.arrangementFaceSignPattern base G) support hoff hsupport)

private theorem card_filter_color_eq_one_of_card_eq_two
    {Face : Type*} [DecidableEq Face]
    (S : Finset Face) (color : Face -> Bool)
    (hcard : S.card = 2)
    (hopposite : ∀ (F : Face), F ∈ S → ∀ (G : Face), G ∈ S →
      F ≠ G → color F ≠ color G)
    (b : Bool) :
    (S.filter fun F => color F = b).card = 1 := by
  obtain ⟨F, G, hFG, rfl⟩ := Finset.card_eq_two.mp hcard
  have hcolor := hopposite F (by simp) G (by simp) hFG
  cases hF : color F <;> cases hG : color G <;> cases b <;>
    simp_all [Finset.filter_insert, Finset.filter_singleton]

noncomputable local instance arrangementFaceFintypeForEvenColor
    (A : FiniteProjectiveLineArrangement Line) : Fintype A.ArrangementFace :=
  A.arrangementFaceFintype

noncomputable local instance arrangementFaceDecidableEqForEvenColor
    (A : FiniteProjectiveLineArrangement Line) : DecidableEq A.ArrangementFace :=
  Classical.decEq _

noncomputable local instance geometricEdgeDecidableEqForEvenColor
    (A : FiniteProjectiveLineArrangement Line) : DecidableEq A.GeometricEdge :=
  Classical.decEq _

/-- Every genuine geometric edge of an even non-pencil arrangement has
exactly one incident face of either parity colour. -/
theorem card_geometricEdgeIncidentFaces_filter_parityColor_eq_one
    (A : FiniteProjectiveLineArrangement Line)
    (hA : A.NonPencil) (heven : Even (Fintype.card Line))
    (base : Line) (e : A.GeometricEdge) (b : Bool) :
    ((A.geometricEdgeIncidentFaces e).filter fun F =>
      A.arrangementFaceParityColor base F = b).card = 1 := by
  classical
  obtain ⟨q, hq⟩ := (A.isPathConnected_geometricEdgeOpenArc hA e).nonempty
  let support : Line := A.edgeSlotLine e
  let transverse : Line :=
    (A.exists_ne_line_of_nonPencil hA support).choose
  have htransverse : transverse ≠ support :=
    (A.exists_ne_line_of_nonPencil hA support).choose_spec
  have hpointFaces : A.geometricEdgeIncidentFaces e =
      A.arrangementPointIncidentFaces q :=
    A.geometricEdgeIncidentFaces_eq_arrangementPointIncidentFaces hA e hq
  have hcard : (A.geometricEdgeIncidentFaces e).card = 2 :=
    A.card_geometricEdgeIncidentFaces_eq_two hA e hq
  apply card_filter_color_eq_one_of_card_eq_two
    (A.geometricEdgeIncidentFaces e)
    (A.arrangementFaceParityColor base) hcard
  intro F hF G hG hFG
  have hFq : q ∈ closure (A.arrangementFaceCarrier F) :=
    (A.mem_arrangementPointIncidentFaces_iff q F).mp (by
      rw [← hpointFaces]
      exact hF)
  have hGq : q ∈ closure (A.arrangementFaceCarrier G) :=
    (A.mem_arrangementPointIncidentFaces_iff q G).mp (by
      rw [← hpointFaces]
      exact hG)
  have hregular : forall m : Line, A.Incident q m ↔ m = support := by
    intro m
    simpa only [support] using A.geometricEdgeOpenArc_incident_iff e hq m
  have htransverseColor :
      A.arrangementFaceParityColor transverse F ≠
        A.arrangementFaceParityColor transverse G :=
    A.arrangementFaceParityColor_ne_of_mem_closure_of_regular
      q support transverse hregular htransverse F G hFq hGq hFG
  rw [A.arrangementFaceParityColor_base_independent heven base transverse F,
    A.arrangementFaceParityColor_base_independent heven base transverse G]
  exact htransverseColor

/-- Boundary-incidence form of the preceding theorem, matching the input of
`colorHandshake_of_oneFacePerEdge`. -/
theorem card_filter_parityColor_and_mem_arrangementFaceBoundary_eq_one
    (A : FiniteProjectiveLineArrangement Line)
    (hA : A.NonPencil) (heven : Even (Fintype.card Line))
    (base : Line) (e : A.GeometricEdge) (b : Bool) :
    (Finset.univ.filter fun F : A.ArrangementFace =>
      A.arrangementFaceParityColor base F = b ∧
        e ∈ A.arrangementFaceBoundary F).card = 1 := by
  classical
  have hsets :
      (Finset.univ.filter fun F : A.ArrangementFace =>
        A.arrangementFaceParityColor base F = b ∧
          e ∈ A.arrangementFaceBoundary F) =
        (A.geometricEdgeIncidentFaces e).filter fun F =>
          A.arrangementFaceParityColor base F = b := by
    ext F
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      A.mem_arrangementFaceBoundary_iff,
      A.mem_geometricEdgeIncidentFaces_iff, and_comm]
  rw [hsets]
  exact A.card_geometricEdgeIncidentFaces_filter_parityColor_eq_one
    hA heven base e b

/-- Bundled quantifier form, directly consumable as the `hone` argument of
the finite two-colour handshake once a global cellulation is available. -/
theorem arrangementFaceParityColor_oneFacePerColorAtEveryGeometricEdge
    (A : FiniteProjectiveLineArrangement Line)
    (hA : A.NonPencil) (heven : Even (Fintype.card Line))
    (base : Line) :
    forall (e : A.GeometricEdge) (b : Bool),
      (Finset.univ.filter fun F : A.ArrangementFace =>
        A.arrangementFaceParityColor base F = b ∧
          e ∈ A.arrangementFaceBoundary F).card = 1 := by
  intro e b
  exact A.card_filter_parityColor_and_mem_arrangementFaceBoundary_eq_one
    hA heven base e b

end FiniteProjectiveLineArrangement

end Erdos506.Incidence
