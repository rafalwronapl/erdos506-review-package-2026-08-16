import Erdos506.Incidence.RealProjectiveArrangementKellyMoserFixedChartExit

/-!
# The empty-triangle attachment bridge for Kelly--Moser

This leaf separates the last chamber-topology seam from the affine
closest-vertex argument.  A three-sided strict sign sector which is crossed
by no other arrangement line already cuts out the full closed face cone.
Once boundary supports are known to be injective on a face, the existing
minimal-facet machinery turns that cone into a literal triangular-face
attachment witness.
-/

namespace Erdos506.Incidence

open scoped LinearAlgebra.Projectivization

namespace FiniteProjectiveLineArrangement

variable {Line : Type*} [Fintype Line] [DecidableEq Line]

noncomputable local instance realProjectivePointTopologicalSpaceForKellyAttachment :
    TopologicalSpace RealProjectivePoint :=
  realProjectivePointQuotientTopology

/-- A positive weighted zero with a nonzero distinguished value forces one
of the other two values to have the opposite strict sign. -/
theorem weightedThree_zero_has_opposite_endpoint
    {c0 c1 c2 a0 a1 a2 : Real}
    (hc0 : 0 < c0) (hc1 : 0 < c1) (hc2 : 0 < c2)
    (ha0 : a0 ≠ 0)
    (hsum : c0 * a0 + c1 * a1 + c2 * a2 = 0) :
    a0 * a1 < 0 ∨ a0 * a2 < 0 := by
  rcases lt_or_gt_of_ne ha0 with ha0neg | ha0pos
  · by_cases ha1pos : 0 < a1
    · exact Or.inl (mul_neg_of_neg_of_pos ha0neg ha1pos)
    by_cases ha2pos : 0 < a2
    · exact Or.inr (mul_neg_of_neg_of_pos ha0neg ha2pos)
    have h0 : c0 * a0 < 0 := mul_neg_of_pos_of_neg hc0 ha0neg
    have h1 : c1 * a1 ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hc1.le
      (le_of_not_gt ha1pos)
    have h2 : c2 * a2 ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hc2.le
      (le_of_not_gt ha2pos)
    have : c0 * a0 + c1 * a1 + c2 * a2 < 0 := by linarith
    exfalso
    exact (ne_of_lt this) hsum
  · by_cases ha1neg : a1 < 0
    · exact Or.inl (mul_neg_of_pos_of_neg ha0pos ha1neg)
    by_cases ha2neg : a2 < 0
    · exact Or.inr (mul_neg_of_pos_of_neg ha0pos ha2neg)
    have h0 : 0 < c0 * a0 := mul_pos hc0 ha0pos
    have h1 : 0 ≤ c1 * a1 := mul_nonneg hc1.le (le_of_not_gt ha1neg)
    have h2 : 0 ≤ c2 * a2 := mul_nonneg hc2.le (le_of_not_gt ha2neg)
    have : 0 < c0 * a0 + c1 * a1 + c2 * a2 := by linarith
    exfalso
    exact (ne_of_gt this) hsum

/-- Two opposite endpoint values have a unique zero at a strict affine
barycentric parameter.  Only existence is needed by the triangle exit. -/
theorem exists_strictBarycentric_zero_of_mul_neg
    {a b : Real} (hab : a * b < 0) :
    ∃ h : Real, 0 < h ∧ h < 1 ∧ (1 - h) * b + h * a = 0 := by
  rcases (mul_neg_iff.mp hab) with ⟨ha, hb⟩ | ⟨ha, hb⟩
  · have hden : 0 < a - b := by linarith
    let h := (-b) / (a - b)
    have hh0 : 0 < h := by
      exact div_pos (neg_pos.mpr hb) hden
    have hh1 : h < 1 := by
      exact (div_lt_one hden).mpr (by linarith)
    refine ⟨h, hh0, hh1, ?_⟩
    dsimp only [h]
    field_simp [ne_of_gt hden]
    ring
  · have hden : 0 < b - a := by linarith
    let h := b / (b - a)
    have hh0 : 0 < h := by
      exact div_pos hb hden
    have hh1 : h < 1 := by
      exact (div_lt_one hden).mpr (by linarith)
    refine ⟨h, hh0, hh1, ?_⟩
    dsimp only [h]
    field_simp [ne_of_gt hden]
    ring

/-- In homogeneous triangle coordinates, a transverse form which vanishes
at a strict interior point must vanish on one of the two non-base sides at
a strict lower height.  `X` is the top vertex, while `Vleft` and `Vright`
are the two base vertices. -/
theorem strictThreeCone_zero_exits_lower_side
    (base left right middle : (Fin 3 → Real) →ₗ[Real] Real)
    (X Vleft Vright W : Fin 3 -> Real)
    (hkernel : ∀ Z : Fin 3 -> Real,
      base Z = 0 -> left Z = 0 -> right Z = 0 -> Z = 0)
    (hbaseX : 0 < base X) (hleftX : left X = 0)
    (hrightX : right X = 0)
    (hbaseVleft : base Vleft = 0) (hleftVleft : left Vleft = 0)
    (hrightVleft : 0 < right Vleft)
    (hbaseVright : base Vright = 0)
    (hrightVright : right Vright = 0)
    (hleftVright : 0 < left Vright)
    (hbaseW : 0 < base W) (hleftW : 0 < left W)
    (hrightW : 0 < right W)
    (hmiddleW : middle W = 0) (hmiddleX : middle X ≠ 0) :
    (∃ h : Real, 0 < h ∧ h < 1 ∧
      let Y := (1 - h) • Vleft + h • X
      Y ≠ 0 ∧ middle Y = 0 ∧ left Y = 0 ∧ 0 < base Y) ∨
    (∃ h : Real, 0 < h ∧ h < 1 ∧
      let Y := (1 - h) • Vright + h • X
      Y ≠ 0 ∧ middle Y = 0 ∧ right Y = 0 ∧ 0 < base Y) := by
  let c0 := base W / base X
  let c1 := right W / right Vleft
  let c2 := left W / left Vright
  have hc0 : 0 < c0 := div_pos hbaseW hbaseX
  have hc1 : 0 < c1 := div_pos hrightW hrightVleft
  have hc2 : 0 < c2 := div_pos hleftW hleftVright
  let D := c0 • X + c1 • Vleft + c2 • Vright
  have hbaseD : base D = base W := by
    dsimp only [D]
    simp only [LinearMap.map_add, LinearMap.map_smul,
      LinearMap.map_smul, LinearMap.map_smul, LinearMap.map_smul,
      hbaseVleft, hbaseVright, smul_eq_mul, smul_eq_mul, smul_eq_mul,
      mul_zero, add_zero]
    dsimp only [c0]
    exact div_mul_cancel₀ (base W) (ne_of_gt hbaseX)
  have hleftD : left D = left W := by
    dsimp only [D]
    simp only [LinearMap.map_add,
      LinearMap.map_smul, LinearMap.map_smul, LinearMap.map_smul,
      hleftX, hleftVleft, smul_eq_mul, smul_eq_mul, smul_eq_mul,
      mul_zero, add_zero, zero_add]
    dsimp only [c2]
    exact div_mul_cancel₀ (left W) (ne_of_gt hleftVright)
  have hrightD : right D = right W := by
    dsimp only [D]
    simp only [LinearMap.map_add,
      LinearMap.map_smul, LinearMap.map_smul, LinearMap.map_smul,
      hrightX, hrightVright, smul_eq_mul, smul_eq_mul, smul_eq_mul,
      mul_zero, zero_add, add_zero]
    dsimp only [c1]
    exact div_mul_cancel₀ (right W) (ne_of_gt hrightVleft)
  have hWD : W = D := by
    apply sub_eq_zero.mp
    apply hkernel (W - D)
    · rw [LinearMap.map_sub, hbaseD, sub_self]
    · rw [LinearMap.map_sub, hleftD, sub_self]
    · rw [LinearMap.map_sub, hrightD, sub_self]
  have hweighted :
      c0 * middle X + c1 * middle Vleft + c2 * middle Vright = 0 := by
    have h := congrArg middle hWD
    rw [hmiddleW] at h
    simpa only [D, LinearMap.map_add, LinearMap.map_smul, smul_eq_mul]
      using h.symm
  rcases weightedThree_zero_has_opposite_endpoint
      hc0 hc1 hc2 hmiddleX hweighted with hleftOpp | hrightOpp
  · left
    obtain ⟨h, hh0, hh1, hzero⟩ :=
      exists_strictBarycentric_zero_of_mul_neg hleftOpp
    refine ⟨h, hh0, hh1, ?_⟩
    dsimp only
    have hbaseY : 0 < base ((1 - h) • Vleft + h • X) := by
      rw [LinearMap.map_add, LinearMap.map_smul, LinearMap.map_smul,
        hbaseVleft, smul_eq_mul, smul_eq_mul, mul_zero, zero_add]
      exact mul_pos hh0 hbaseX
    refine ⟨?_, ?_, ?_, hbaseY⟩
    · intro hY
      have := congrArg base hY
      rw [LinearMap.map_zero] at this
      exact (ne_of_gt hbaseY) this
    · simpa only [LinearMap.map_add, LinearMap.map_smul, smul_eq_mul]
        using hzero
    · simp only [LinearMap.map_add, LinearMap.map_smul,
        hleftVleft, hleftX, smul_eq_mul, smul_eq_mul, mul_zero, add_zero]
  · right
    obtain ⟨h, hh0, hh1, hzero⟩ :=
      exists_strictBarycentric_zero_of_mul_neg hrightOpp
    refine ⟨h, hh0, hh1, ?_⟩
    dsimp only
    have hbaseY : 0 < base ((1 - h) • Vright + h • X) := by
      rw [LinearMap.map_add, LinearMap.map_smul, LinearMap.map_smul,
        hbaseVright, smul_eq_mul, smul_eq_mul, mul_zero, zero_add]
      exact mul_pos hh0 hbaseX
    refine ⟨?_, ?_, ?_, hbaseY⟩
    · intro hY
      have := congrArg base hY
      rw [LinearMap.map_zero] at this
      exact (ne_of_gt hbaseY) this
    · simpa only [LinearMap.map_add, LinearMap.map_smul, smul_eq_mul]
        using hzero
    · simp only [LinearMap.map_add, LinearMap.map_smul,
        hrightVright, hrightX, smul_eq_mul, smul_eq_mul, mul_zero, add_zero]

/-- If a strict sector cut out by `K` contains a point of the full chamber
and no line outside `K` vanishes anywhere in that strict sector, then the
weak `K`-sector is exactly the full closed sign cone. -/
theorem arrangementClosedSignConeOn_eq_of_no_transverse_zero
    (A : FiniteProjectiveLineArrangement Line) (sigma : Line -> Bool)
    (K : Finset Line) (hK : K.Nonempty) (p : Fin 3 -> Real)
    (hp : p ∈ A.arrangementSignCone sigma)
    (hnozero : ∀ v : Fin 3 -> Real, v ≠ 0 ->
      v ∈ A.arrangementSignConeOn sigma K ->
      ∀ m : Line, m ∉ K ->
        A.arrangementOrientedEvaluation sigma m v ≠ 0) :
    A.arrangementClosedSignConeOn sigma K =
      A.arrangementClosedSignCone sigma := by
  apply Set.Subset.antisymm
  · intro v hv
    rw [A.mem_arrangementClosedSignCone_iff_orientedEvaluation_nonneg]
    intro m
    by_cases hmK : m ∈ K
    · exact hv m hmK
    · by_contra hmNonneg
      have hvm : A.arrangementOrientedEvaluation sigma m v < 0 :=
        lt_of_not_ge hmNonneg
      have hpm : 0 < A.arrangementOrientedEvaluation sigma m p :=
        (A.mem_arrangementSignCone_iff_orientedEvaluation_pos sigma p).mp hp m
      let w :=
        (-A.arrangementOrientedEvaluation sigma m v) • p +
          A.arrangementOrientedEvaluation sigma m p • v
      have hwStrict : w ∈ A.arrangementSignConeOn sigma K := by
        intro k hk
        have hpk : 0 < A.arrangementOrientedEvaluation sigma k p :=
          (A.mem_arrangementSignCone_iff_orientedEvaluation_pos sigma p).mp hp k
        have hvk : 0 <= A.arrangementOrientedEvaluation sigma k v := hv k hk
        dsimp only [w]
        rw [LinearMap.map_add, LinearMap.map_smul, LinearMap.map_smul,
          smul_eq_mul, smul_eq_mul]
        exact add_pos_of_pos_of_nonneg
          (mul_pos (neg_pos.mpr hvm) hpk) (mul_nonneg hpm.le hvk)
      obtain ⟨k, hk⟩ := hK
      have hw0 : w ≠ 0 := by
        intro hw
        have hkw := congrArg (A.arrangementOrientedEvaluation sigma k) hw
        rw [LinearMap.map_zero] at hkw
        exact (ne_of_gt (hwStrict k hk)) hkw
      have hwm0 : A.arrangementOrientedEvaluation sigma m w = 0 := by
        dsimp only [w]
        rw [LinearMap.map_add, LinearMap.map_smul, LinearMap.map_smul,
          smul_eq_mul, smul_eq_mul]
        ring
      exact (hnozero w hw0 hwStrict m hmK) hwm0
  · intro v hv
    intro k _hk
    exact (A.mem_arrangementClosedSignCone_iff_orientedEvaluation_nonneg
      sigma v).mp hv k

/-- Every literal boundary edge of a face whose closed cone is already cut
out by `K` is supported by a member of `K`.  The proof perturbs a regular
point of the edge through the allegedly redundant supporting hyperplane. -/
theorem edgeSlotLine_mem_of_mem_boundary_of_closedSignConeOn_eq
    (A : FiniteProjectiveLineArrangement Line) (hA : A.NonPencil)
    (base : Line) (F : A.ArrangementFace) (K : Finset Line)
    (hbaseK : base ∈ K)
    (hcone : A.arrangementClosedSignConeOn
        (A.arrangementFaceSignPattern base F) K =
      A.arrangementClosedSignCone (A.arrangementFaceSignPattern base F))
    {e : A.GeometricEdge} (heF : e ∈ A.arrangementFaceBoundary F) :
    A.edgeSlotLine e ∈ K := by
  classical
  let sigma := A.arrangementFaceSignPattern base F
  let m := A.edgeSlotLine e
  by_contra hmK
  have hbaseNe : base ≠ m := by
    intro h
    apply hmK
    simpa only [h] using hbaseK
  obtain ⟨q, hqArc⟩ := (A.isPathConnected_geometricEdgeOpenArc hA e).nonempty
  have hqClosure : q ∈ closure (A.arrangementFaceCarrier F) := by
    obtain ⟨r, hrArc, hrClosure⟩ :=
      (A.mem_arrangementFaceBoundary_iff F e).mp heF
    exact
      A.mem_closure_arrangementFaceCarrier_of_mem_closure_of_geometricEdgeOpenArc
        hA e hrArc hqArc F hrClosure
  have hregular : ∀ k : Line, A.Incident q k ↔ k = m := by
    intro k
    simpa only [m] using A.geometricEdgeOpenArc_incident_iff e hqArc k
  have hqbase : ¬ A.Incident q base := by
    intro hqb
    exact hbaseNe ((hregular base).mp hqb)
  let v := A.arrangementPointNormalizedRepresentativeAt base q
  have hv0 : v ≠ 0 := by
    simpa only [v] using
      A.arrangementPointNormalizedRepresentativeAt_ne_zero base q hqbase
  have hvClosed : v ∈ A.arrangementClosedSignCone sigma := by
    simpa only [v, sigma] using
      A.arrangementPointNormalizedRepresentativeAt_mem_closedSignCone_of_mem_closure
        q base F hqbase hqClosure
  have hvStrict : v ∈ A.arrangementSignConeOn sigma K := by
    intro k hk
    apply
      A.arrangementOrientedEvaluation_normalized_pos_of_mem_closure_of_not_incident
        q base F hqbase hqClosure k
    intro hqk
    have hkm : k = m := (hregular k).mp hqk
    subst k
    exact hmK hk
  obtain ⟨d, _hdbase, hdm⟩ :=
    A.exists_orientedEvaluation_neg_on_kernel_of_ne sigma
      (l := base) (m := m) hbaseNe
  let phi : Real -> (Fin 3 -> Real) := fun t => v + t • d
  have hphiContinuous : Continuous phi := by
    exact continuous_const.add (continuous_id.smul continuous_const)
  have heventually : ∀ᶠ t in nhds (0 : Real),
      phi t ∈ A.arrangementSignConeOn sigma K := by
    apply hphiContinuous.continuousAt
    apply (A.isOpen_arrangementSignConeOn sigma K).mem_nhds
    simpa only [phi, zero_smul, add_zero] using hvStrict
  obtain ⟨eps, heps, hball⟩ := Metric.eventually_nhds_iff.mp heventually
  let t : Real := eps / 2
  have ht : 0 < t := by
    dsimp only [t]
    linarith
  have htSmall : dist t (0 : Real) < eps := by
    rw [Real.dist_0_eq_abs, abs_of_pos ht]
    dsimp only [t]
    linarith
  have hphiStrict : phi t ∈ A.arrangementSignConeOn sigma K :=
    hball (y := t) htSmall
  have hphiClosedK : phi t ∈ A.arrangementClosedSignConeOn sigma K := by
    intro k hk
    exact (hphiStrict k hk).le
  have hphiClosed : phi t ∈ A.arrangementClosedSignCone sigma := by
    rw [← hcone]
    exact hphiClosedK
  have hphiNonneg :
      0 ≤ A.arrangementOrientedEvaluation sigma m (phi t) :=
    (A.mem_arrangementClosedSignCone_iff_orientedEvaluation_nonneg
      sigma (phi t)).mp hphiClosed m
  have hvm0 : A.arrangementOrientedEvaluation sigma m v = 0 := by
    apply (A.incident_projectivization_mk_iff_orientedEvaluation_eq_zero
      sigma m v hv0).mp
    rw [show Projectivization.mk Real v hv0 = q by
      simpa only [v] using
        A.projectivization_mk_arrangementPointNormalizedRepresentativeAt
          base q hqbase]
    exact (hregular m).mpr rfl
  have hphiNeg : A.arrangementOrientedEvaluation sigma m (phi t) < 0 := by
    dsimp only [phi]
    rw [LinearMap.map_add, LinearMap.map_smul, hvm0, smul_eq_mul, zero_add]
    exact mul_neg_of_pos_of_neg ht hdm
  exact (not_lt_of_ge hphiNonneg) hphiNeg

/-- A three-half-space description of a face, together with the standard
fact that one face has at most one boundary edge on each support, produces
the literal attachment witness used by the Kelly--Rottenberg count. -/
theorem ordinaryVertexAttachedToLine_of_three_side_sign_sector
    (A : FiniteProjectiveLineArrangement Line) (hA : A.NonPencil)
    (q : A.OrdinaryVertex) (l a b : Line) (F : A.ArrangementFace)
    (hla : l ≠ a) (hlb : l ≠ b) (hab : a ≠ b)
    (hqaway : ¬ A.Incident q.1 l)
    (hqF : q.1 ∈ closure (A.arrangementFaceCarrier F))
    (hcone : A.arrangementClosedSignConeOn
        (A.arrangementFaceSignPattern l F) {l, a, b} =
      A.arrangementClosedSignCone (A.arrangementFaceSignPattern l F))
    (hsupportInj : ∀ e₁ : A.GeometricEdge,
      e₁ ∈ A.arrangementFaceBoundary F ->
      ∀ e₂ : A.GeometricEdge, e₂ ∈ A.arrangementFaceBoundary F ->
        A.edgeSlotLine e₁ = A.edgeSlotLine e₂ -> e₁ = e₂) :
    A.OrdinaryVertexAttachedToLine q l := by
  classical
  let K : Finset Line := {l, a, b}
  have hKcard : K.card = 3 := by
    simp [K, hla, hlb, hab]
  have hminimal : ∀ L : Finset Line,
      A.arrangementClosedSignConeOn
          (A.arrangementFaceSignPattern l F) L =
        A.arrangementClosedSignCone (A.arrangementFaceSignPattern l F) ->
      K.card ≤ L.card := by
    intro L hL
    rw [hKcard]
    exact A.three_le_card_of_arrangementClosedSignConeOn_eq hA _ L hL
  obtain ⟨e, heLine, heF⟩ :=
    A.exists_boundaryEdge_supported_by_cardMinimal_index
      hA l F K (by simpa only [K] using hcone) hminimal (l := l)
        (by simp [K])
  let support :
      {e : A.GeometricEdge // e ∈ A.arrangementFaceBoundary F} ->
        {m : Line // m ∈ K} := fun e' =>
      ⟨A.edgeSlotLine e',
      A.edgeSlotLine_mem_of_mem_boundary_of_closedSignConeOn_eq
        hA l F K (by simp [K])
          (by simpa only [K] using hcone) e'.2⟩
  have hsupport : Function.Injective support := by
    intro e₁ e₂ h
    apply Subtype.ext
    exact hsupportInj e₁.1 e₁.2 e₂.1 e₂.2
      (congrArg Subtype.val h)
  have hcardLe : (A.arrangementFaceBoundary F).card ≤ K.card := by
    have h := Fintype.card_le_of_injective support hsupport
    simpa only [Fintype.card_coe] using h
  have hupper : (A.arrangementFaceBoundary F).card ≤ 3 := by
    simpa only [hKcard] using hcardLe
  have hlower : 3 ≤ (A.arrangementFaceBoundary F).card :=
    A.three_le_arrangementFaceBoundary_card hA l F
  have htri : (A.arrangementFaceBoundary F).card = 3 :=
    Nat.le_antisymm hupper hlower
  refine ⟨{
    face := F
    base := e
    away := hqaway
    triangular := htri
    base_mem := heF
    base_line := heLine
    opposite := hqF
  }⟩

end FiniteProjectiveLineArrangement

end Erdos506.Incidence
