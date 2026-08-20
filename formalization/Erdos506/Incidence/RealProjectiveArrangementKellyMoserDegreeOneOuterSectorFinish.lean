import Erdos506.Incidence.RealProjectiveArrangementKellyMoserOuterReturnClosure

/-!
# Canonical clean-edge sectors for Felsner's degree-one branch

This leaf sits above the generic return-closure API.  It orients the two
triangle chambers adjacent to the actual clean edge `p--r` by a single
interior reference point, and relates that orientation to the intrinsic
Menelaus sign classes from `RealProjectiveArrangementKellyMoserOuterSector`.
-/

namespace Erdos506.Incidence

open scoped LinearAlgebra.Projectivization

namespace FiniteProjectiveLineArrangement

variable {Line : Type*} [Fintype Line] [DecidableEq Line]

noncomputable local instance realProjectivePointTopologicalSpaceForKellyMoserDegreeOneOuterSectorFinish :
    TopologicalSpace RealProjectivePoint :=
  realProjectivePointQuotientTopology

noncomputable local instance realProjectivePointDecidableEqForKellyMoserDegreeOneOuterSectorFinish :
    DecidableEq RealProjectivePoint :=
  Classical.decEq _

noncomputable local instance geometricEdgeDecidableEqForKellyMoserDegreeOneOuterSectorFinish
    (A : FiniteProjectiveLineArrangement Line) : DecidableEq A.GeometricEdge :=
  A.geometricEdgeDecidableEqForOrdinaryEdgeTriangle

noncomputable local instance incidentDecidableForKellyMoserDegreeOneOuterSectorFinish
    (A : FiniteProjectiveLineArrangement Line)
    (p : RealProjectivePoint) (l : Line) : Decidable (A.Incident p l) :=
  Classical.propDecidable _

namespace OrdinaryAttachmentOuterSectorFront

namespace FelsnerOneLineCleanFrame

variable {A : FiniteProjectiveLineArrangement Line} {l : Line}

/-- A concrete orientation reference in the clean open edge. -/
structure CleanEdgeSectorReference
    (F : FelsnerOneLineCleanFrame A l) where
  point : RealProjectivePoint
  point_mem : point ∈ A.geometricEdgeOpenArc F.cleanEdge

theorem exists_cleanEdgeSectorReference
    (F : FelsnerOneLineCleanFrame A l) (hA : A.NonPencil) :
    Nonempty F.CleanEdgeSectorReference := by
  obtain ⟨z, hz⟩ := F.exists_cleanEdgeReference hA
  exact ⟨⟨z, hz⟩⟩

namespace CleanEdgeSectorReference

variable {F : FelsnerOneLineCleanFrame A l}

/-- The canonical chamber orientation along the clean edge. -/
noncomputable def sigma (G : F.CleanEdgeSectorReference) : Line → Bool :=
  A.closedSectorSignPatternAt G.point

/-- The chamber on the other side of the same clean edge. -/
noncomputable def flipSigma (G : F.CleanEdgeSectorReference) : Line → Bool :=
  flipSignAt G.sigma F.m

/-- Intrinsic base-class value expressed in the clean-edge orientation. -/
noncomputable def orientedBaseSideProduct
    (G : F.CleanEdgeSectorReference) (v : A.CircularGapSlot l) : ℝ :=
  A.arrangementOrientedEvaluation G.sigma F.m v.1.rep *
    A.arrangementOrientedEvaluation G.sigma F.n v.1.rep

theorem orientedBaseSideProduct_ne_zero
    (G : F.CleanEdgeSectorReference) (v : A.CircularGapSlot l)
    (hvp : v ≠ F.pSlot) (hvq : v ≠ F.q) :
    G.orientedBaseSideProduct v ≠ 0 := by
  have hraw := F.baseSideProduct_ne_zero v hvp hvq
  by_cases hm : G.sigma F.m <;> by_cases hn : G.sigma F.n <;>
    simpa [orientedBaseSideProduct, baseSideProduct,
      arrangementOrientedEvaluation, hm, hn] using hraw

theorem orientedBaseSideProduct_pos_or_neg
    (G : F.CleanEdgeSectorReference) (v : A.CircularGapSlot l)
    (hvp : v ≠ F.pSlot) (hvq : v ≠ F.q) :
    0 < G.orientedBaseSideProduct v ∨ G.orientedBaseSideProduct v < 0 := by
  rcases lt_or_gt_of_ne
      (G.orientedBaseSideProduct_ne_zero v hvp hvq) with h | h
  · exact Or.inr h
  · exact Or.inl h

theorem point_on_m (G : F.CleanEdgeSectorReference) :
    A.Incident G.point F.m := by
  exact (A.geometricEdgeOpenArc_incident_iff F.cleanEdge G.point_mem F.m).2
    F.cleanEdge_line.symm

theorem point_away_l (G : F.CleanEdgeSectorReference) :
    ¬ A.Incident G.point l := by
  intro h
  have heq :=
    (A.geometricEdgeOpenArc_incident_iff F.cleanEdge G.point_mem l).mp h
  exact F.m_ne_base (heq.trans F.cleanEdge_line).symm

theorem point_away_n (G : F.CleanEdgeSectorReference) :
    ¬ A.Incident G.point F.n := by
  intro h
  have heq :=
    (A.geometricEdgeOpenArc_incident_iff F.cleanEdge G.point_mem F.n).mp h
  exact F.n_ne_m (heq.trans F.cleanEdge_line)

theorem point_oriented_l_pos (G : F.CleanEdgeSectorReference) :
    0 < A.arrangementOrientedEvaluation G.sigma l G.point.rep :=
  A.arrangementOrientedEvaluation_closedSectorSignPatternAt_pos
    G.point l G.point_away_l

theorem point_oriented_n_pos (G : F.CleanEdgeSectorReference) :
    0 < A.arrangementOrientedEvaluation G.sigma F.n G.point.rep :=
  A.arrangementOrientedEvaluation_closedSectorSignPatternAt_pos
    G.point F.n G.point_away_n

theorem point_orientedPair_pos (G : F.CleanEdgeSectorReference) :
    0 < A.arrangementOrientedEvaluation G.sigma l G.point.rep *
      A.arrangementOrientedEvaluation G.sigma F.n G.point.rep :=
  mul_pos G.point_oriented_l_pos G.point_oriented_n_pos

/-- A positive `(l,n)` pair in the clean-edge orientation is the intrinsic
relative-sign class of the clean edge.  This is the quotient-safe bridge
from an oriented cone calculation back to the cyclic invariant. -/
theorem arrangementRelativeSign_eq_point_of_orientedPair_pos
    (G : F.CleanEdgeSectorReference) (u : RealProjectivePoint)
    (huL : ¬ A.Incident u l) (huN : ¬ A.Incident u F.n)
    (hpos : 0 < A.arrangementOrientedEvaluation G.sigma l u.rep *
      A.arrangementOrientedEvaluation G.sigma F.n u.rep) :
    A.arrangementRelativeSign l F.n u =
      A.arrangementRelativeSign l F.n G.point := by
  have hulRaw : projectiveLineEvaluation (A.projectiveLine l) u.rep ≠ 0 :=
    (A.projectiveLineEvaluation_rep_eq_zero_iff_incident u l).not.mpr huL
  have hunRaw : projectiveLineEvaluation
      (A.projectiveLine F.n) u.rep ≠ 0 :=
    (A.projectiveLineEvaluation_rep_eq_zero_iff_incident u F.n).not.mpr huN
  have hzlRaw : projectiveLineEvaluation
      (A.projectiveLine l) G.point.rep ≠ 0 :=
    (A.projectiveLineEvaluation_rep_eq_zero_iff_incident G.point l).not.mpr
      G.point_away_l
  have hznRaw : projectiveLineEvaluation
      (A.projectiveLine F.n) G.point.rep ≠ 0 :=
    (A.projectiveLineEvaluation_rep_eq_zero_iff_incident G.point F.n).not.mpr
      G.point_away_n
  have heq :
      (A.arrangementOrientedEvaluation G.sigma l u.rep *
          A.arrangementOrientedEvaluation G.sigma F.n u.rep) *
        (A.arrangementOrientedEvaluation G.sigma l G.point.rep *
          A.arrangementOrientedEvaluation G.sigma F.n G.point.rep) =
      (projectiveLineEvaluation (A.projectiveLine l) u.rep *
          projectiveLineEvaluation (A.projectiveLine F.n) u.rep) *
        (projectiveLineEvaluation (A.projectiveLine l) G.point.rep *
          projectiveLineEvaluation (A.projectiveLine F.n) G.point.rep) := by
    by_cases hl : G.sigma l <;> by_cases hn : G.sigma F.n <;>
      simp [arrangementOrientedEvaluation, hl, hn] <;> ring
  have hrawPos : 0 <
      (projectiveLineEvaluation (A.projectiveLine l) u.rep *
          projectiveLineEvaluation (A.projectiveLine F.n) u.rep) *
        (projectiveLineEvaluation (A.projectiveLine l) G.point.rep *
          projectiveLineEvaluation (A.projectiveLine F.n) G.point.rep) := by
    rw [← heq]
    exact mul_pos hpos G.point_orientedPair_pos
  rw [A.arrangementRelativeSign_apply_rep,
    A.arrangementRelativeSign_apply_rep]
  exact (sign_eq_sign_iff_mul_pos
    (mul_ne_zero hulRaw hunRaw) (mul_ne_zero hzlRaw hznRaw)).2 hrawPos

/-- Vector-level form of the same bridge, avoiding any dependence on the
canonical representative selected for the resulting projective point. -/
theorem arrangementRelativeSign_mk_eq_point_of_orientedPair_pos
    (G : F.CleanEdgeSectorReference) (U : Homogeneous3) (hU0 : U ≠ 0)
    (hpos : 0 < A.arrangementOrientedEvaluation G.sigma l U *
      A.arrangementOrientedEvaluation G.sigma F.n U) :
    A.arrangementRelativeSign l F.n (Projectivization.mk ℝ U hU0) =
      A.arrangementRelativeSign l F.n G.point := by
  have horNe :
      A.arrangementOrientedEvaluation G.sigma l U *
        A.arrangementOrientedEvaluation G.sigma F.n U ≠ 0 :=
    ne_of_gt hpos
  have horLNe : A.arrangementOrientedEvaluation G.sigma l U ≠ 0 := by
    intro hzero
    apply horNe
    rw [hzero, zero_mul]
  have horNNe : A.arrangementOrientedEvaluation G.sigma F.n U ≠ 0 := by
    intro hzero
    apply horNe
    rw [hzero, mul_zero]
  have hulRaw : projectiveLineEvaluation (A.projectiveLine l) U ≠ 0 := by
    by_cases hl : G.sigma l <;>
      simpa [arrangementOrientedEvaluation, hl] using horLNe
  have hunRaw : projectiveLineEvaluation (A.projectiveLine F.n) U ≠ 0 := by
    by_cases hn : G.sigma F.n <;>
      simpa [arrangementOrientedEvaluation, hn] using horNNe
  have hzlRaw : projectiveLineEvaluation
      (A.projectiveLine l) G.point.rep ≠ 0 :=
    (A.projectiveLineEvaluation_rep_eq_zero_iff_incident G.point l).not.mpr
      G.point_away_l
  have hznRaw : projectiveLineEvaluation
      (A.projectiveLine F.n) G.point.rep ≠ 0 :=
    (A.projectiveLineEvaluation_rep_eq_zero_iff_incident G.point F.n).not.mpr
      G.point_away_n
  have heq :
      (A.arrangementOrientedEvaluation G.sigma l U *
          A.arrangementOrientedEvaluation G.sigma F.n U) *
        (A.arrangementOrientedEvaluation G.sigma l G.point.rep *
          A.arrangementOrientedEvaluation G.sigma F.n G.point.rep) =
      (projectiveLineEvaluation (A.projectiveLine l) U *
          projectiveLineEvaluation (A.projectiveLine F.n) U) *
        (projectiveLineEvaluation (A.projectiveLine l) G.point.rep *
          projectiveLineEvaluation (A.projectiveLine F.n) G.point.rep) := by
    by_cases hl : G.sigma l <;> by_cases hn : G.sigma F.n <;>
      simp [arrangementOrientedEvaluation, hl, hn] <;> ring
  have hrawPos : 0 <
      (projectiveLineEvaluation (A.projectiveLine l) U *
          projectiveLineEvaluation (A.projectiveLine F.n) U) *
        (projectiveLineEvaluation (A.projectiveLine l) G.point.rep *
          projectiveLineEvaluation (A.projectiveLine F.n) G.point.rep) := by
    rw [← heq]
    exact mul_pos hpos G.point_orientedPair_pos
  rw [A.arrangementRelativeSign_mk,
    A.arrangementRelativeSign_apply_rep]
  exact (sign_eq_sign_iff_mul_pos
    (mul_ne_zero hulRaw hunRaw) (mul_ne_zero hzlRaw hznRaw)).2 hrawPos

/-- A base point outside a closed triangle sector belongs to the sector
obtained by flipping either one of the two side signs.  The endpoint cases
are excluded explicitly so that the two remaining evaluations are strict. -/
theorem mem_flip_middle_of_incident_base_of_not_mem
    (G : F.CleanEdgeSectorReference) (tau : Line → Bool)
    (y : RealProjectivePoint) (hyl : A.Incident y l)
    (hym : ¬ A.Incident y F.m) (hyn : ¬ A.Incident y F.n)
    (hout : ¬ A.projectivePointMemTriangleSector tau l F.m F.n y) :
    A.projectivePointMemTriangleSector (flipSignAt tau F.m)
      l F.m F.n y := by
  have hmNe : A.arrangementOrientedEvaluation tau F.m y.rep ≠ 0 := by
    by_cases hs : tau F.m <;>
      simpa [arrangementOrientedEvaluation, hs] using
        (A.projectiveLineEvaluation_rep_eq_zero_iff_incident y F.m).not.mpr hym
  have hnNe : A.arrangementOrientedEvaluation tau F.n y.rep ≠ 0 := by
    by_cases hs : tau F.n <;>
      simpa [arrangementOrientedEvaluation, hs] using
        (A.projectiveLineEvaluation_rep_eq_zero_iff_incident y F.n).not.mpr hyn
  have hpairNe :
      A.arrangementOrientedEvaluation tau F.m y.rep *
        A.arrangementOrientedEvaluation tau F.n y.rep ≠ 0 :=
    mul_ne_zero hmNe hnNe
  have hpairNotPos : ¬ 0 <
      A.arrangementOrientedEvaluation tau F.m y.rep *
        A.arrangementOrientedEvaluation tau F.n y.rep := by
    intro hpair
    apply hout
    have hmem :=
      A.projectivePointMemTriangleSector_of_incident_middle_of_pair_pos
        tau F.m l F.n y hyl hpair
    unfold projectivePointMemTriangleSector at hmem ⊢
    have hset : ({F.m, l, F.n} : Finset Line) = {l, F.m, F.n} := by
      ext k
      simp [or_comm, or_left_comm, or_assoc]
    simpa only [hset] using hmem
  have hpairNeg :
      A.arrangementOrientedEvaluation tau F.m y.rep *
        A.arrangementOrientedEvaluation tau F.n y.rep < 0 :=
    lt_of_le_of_ne (le_of_not_gt hpairNotPos) hpairNe
  have hflipPair : 0 <
      A.arrangementOrientedEvaluation (flipSignAt tau F.m) F.m y.rep *
        A.arrangementOrientedEvaluation (flipSignAt tau F.m) F.n y.rep := by
    rw [A.arrangementOrientedEvaluation_flipSignAt_self_apply,
      A.arrangementOrientedEvaluation_flipSignAt_of_ne_apply tau F.n_ne_m]
    simpa only [neg_mul] using neg_pos.mpr hpairNeg
  have hmem :=
    A.projectivePointMemTriangleSector_of_incident_middle_of_pair_pos
      (flipSignAt tau F.m) F.m l F.n y hyl hflipPair
  unfold projectivePointMemTriangleSector at hmem ⊢
  have hset : ({F.m, l, F.n} : Finset Line) = {l, F.m, F.n} := by
    ext k
    simp [or_comm, or_left_comm, or_assoc]
  simpa only [hset] using hmem

/-- A marked off-base point of either clean-edge-oriented chamber cannot
lie on the clean side `m`, unless it is the far apex `r`. -/
theorem not_incident_m_of_mem_sector_of_ne_r
    (G : F.CleanEdgeSectorReference) (tau : Line → Bool)
    (htauL : A.arrangementOrientedEvaluation tau l =
      A.arrangementOrientedEvaluation G.sigma l)
    (htauN : A.arrangementOrientedEvaluation tau F.n =
      A.arrangementOrientedEvaluation G.sigma F.n)
    (x : RealProjectivePoint) (hxVertex : x ∈ A.vertexSet)
    (hxSector : A.projectivePointMemTriangleSector tau l F.m F.n x)
    (hxl : ¬ A.Incident x l) (hxNeR : x ≠ F.r) :
    ¬ A.Incident x F.m := by
  intro hxm
  have hxNeP : x ≠ F.p.1 := by
    intro hxp
    apply hxl
    rw [hxp]
    exact F.p_on_base
  have hxn : ¬ A.Incident x F.n := by
    intro hxn
    apply hxNeR
    calc
      x = A.intersection F.m F.n :=
        A.eq_intersection_of_incident F.n_ne_m.symm hxm hxn
      _ = F.r := F.r_eq_intersection.symm
  have hpairNonneg : 0 ≤
      A.arrangementOrientedEvaluation tau l x.rep *
        A.arrangementOrientedEvaluation tau F.n x.rep :=
    A.orientedPair_nonneg_of_memTriangleSector_of_incident_middle
      tau l F.m F.n x hxm hxSector
  have hlNe : A.arrangementOrientedEvaluation tau l x.rep ≠ 0 := by
    by_cases hs : tau l <;>
      simpa [arrangementOrientedEvaluation, hs] using
        (A.projectiveLineEvaluation_rep_eq_zero_iff_incident x l).not.mpr hxl
  have hnNe : A.arrangementOrientedEvaluation tau F.n x.rep ≠ 0 := by
    by_cases hs : tau F.n <;>
      simpa [arrangementOrientedEvaluation, hs] using
        (A.projectiveLineEvaluation_rep_eq_zero_iff_incident x F.n).not.mpr hxn
  have hpairPos : 0 <
      A.arrangementOrientedEvaluation tau l x.rep *
        A.arrangementOrientedEvaluation tau F.n x.rep :=
    lt_of_le_of_ne hpairNonneg (mul_ne_zero hlNe hnNe).symm
  have hcleanPos : 0 <
      A.arrangementOrientedEvaluation G.sigma l x.rep *
        A.arrangementOrientedEvaluation G.sigma F.n x.rep := by
    simpa only [← htauL, ← htauN] using hpairPos
  have hsame :=
    G.arrangementRelativeSign_eq_point_of_orientedPair_pos
      x hxl hxn hcleanPos
  exact (F.arrangementRelativeSign_ne_cleanEdgeReference
    G.point x G.point_mem hxVertex hxm hxNeP hxNeR) hsame

/-- Clean-edge return closure away from the far apex.  If a support through
`x` returned outside the same base sector, its intersection with `m` would
be a new marked point in the open clean edge `p--r`. -/
theorem return_mem_of_mem_sector_of_ne_r
    (G : F.CleanEdgeSectorReference) (tau : Line → Bool)
    (htauL : A.arrangementOrientedEvaluation tau l =
      A.arrangementOrientedEvaluation G.sigma l)
    (htauN : A.arrangementOrientedEvaluation tau F.n =
      A.arrangementOrientedEvaluation G.sigma F.n)
    (x : RealProjectivePoint) (hxVertex : x ∈ A.vertexSet)
    (hxSector : A.projectivePointMemTriangleSector tau l F.m F.n x)
    (hxl : ¬ A.Incident x l) (hxNeR : x ≠ F.r)
    (c : Line) (hxc : A.Incident x c) (hlc : l ≠ c) :
    A.projectivePointMemTriangleSector tau l F.m F.n
      (A.intersection l c) := by
  classical
  by_contra hout
  let y := A.intersection l c
  have hout' : ¬ A.projectivePointMemTriangleSector tau l F.m F.n y := by
    simpa only [y] using hout
  have hyl : A.Incident y l := by
    exact A.intersection_incident_left hlc
  have hyc : A.Incident y c := by
    exact A.intersection_incident_right hlc
  have hym : ¬ A.Incident y F.m := by
    intro hym
    apply hout'
    exact A.projectivePointMemTriangleSector_of_incident_base_left
      tau l F.m F.n y hyl hym
  have hyn : ¬ A.Incident y F.n := by
    intro hyn
    apply hout'
    exact A.projectivePointMemTriangleSector_of_incident_base_right
      tau l F.m F.n y hyl hyn
  have hxm : ¬ A.Incident x F.m :=
    G.not_incident_m_of_mem_sector_of_ne_r tau htauL htauN
      x hxVertex hxSector hxl hxNeR
  have hcm : c ≠ F.m := by
    intro h
    apply hxm
    rw [← h]
    exact hxc
  let rho := flipSignAt tau F.m
  have hyRho : A.projectivePointMemTriangleSector rho l F.m F.n y := by
    simpa only [rho] using
      G.mem_flip_middle_of_incident_base_of_not_mem
        tau y hyl hym hyn hout'
  let X := A.sectorExitNormalizedPoint tau l F.m F.n x
  let R := A.sectorExitNormalizedPoint rho l F.m F.n y
  obtain ⟨hX0, _hXgauge, hmkX, hXcone⟩ :=
    A.sectorExitNormalizedPoint_facts
      tau l F.m F.n F.boundary_nonconcurrent x hxSector
  obtain ⟨hR0, _hRgauge, hmkR, hRcone⟩ :=
    A.sectorExitNormalizedPoint_facts
      rho l F.m F.n F.boundary_nonconcurrent y hyRho
  have hXlPos : 0 < A.arrangementOrientedEvaluation tau l X := by
    exact A.arrangementOrientedEvaluation_sectorExitNormalizedPoint_pos
      tau l F.m F.n F.boundary_nonconcurrent x hxSector hxl
  have hXmNonneg : 0 ≤ A.arrangementOrientedEvaluation tau F.m X :=
    hXcone F.m (by simp)
  have hXmNe : A.arrangementOrientedEvaluation tau F.m X ≠ 0 := by
    intro hzero
    apply hxm
    rw [← hmkX]
    exact (A.incident_projectivization_mk_iff_orientedEvaluation_eq_zero
      tau F.m X hX0).2 hzero
  have hXmPos : 0 < A.arrangementOrientedEvaluation tau F.m X :=
    lt_of_le_of_ne hXmNonneg hXmNe.symm
  have hXnNonneg : 0 ≤ A.arrangementOrientedEvaluation tau F.n X :=
    hXcone F.n (by simp)
  have hRlRho : A.arrangementOrientedEvaluation rho l R = 0 :=
    A.arrangementOrientedEvaluation_sectorExitNormalizedPoint_eq_zero
      rho l F.m F.n l F.boundary_nonconcurrent y hyRho hyl
  have hRl : A.arrangementOrientedEvaluation tau l R = 0 := by
    simpa only [rho,
      A.arrangementOrientedEvaluation_flipSignAt_of_ne_apply
        tau F.m_ne_base.symm] using hRlRho
  have hRmRhoNonneg :
      0 ≤ A.arrangementOrientedEvaluation rho F.m R :=
    hRcone F.m (by simp)
  have hRmRhoNe : A.arrangementOrientedEvaluation rho F.m R ≠ 0 := by
    intro hzero
    apply hym
    rw [← hmkR]
    exact (A.incident_projectivization_mk_iff_orientedEvaluation_eq_zero
      rho F.m R hR0).2 hzero
  have hRmRhoPos : 0 < A.arrangementOrientedEvaluation rho F.m R :=
    lt_of_le_of_ne hRmRhoNonneg hRmRhoNe.symm
  have hRmNeg : A.arrangementOrientedEvaluation tau F.m R < 0 := by
    have h := hRmRhoPos
    simpa only [rho,
      A.arrangementOrientedEvaluation_flipSignAt_self_apply,
      neg_pos] using h
  have hRnRhoNonneg :
      0 ≤ A.arrangementOrientedEvaluation rho F.n R :=
    hRcone F.n (by simp)
  have hRnRhoNe : A.arrangementOrientedEvaluation rho F.n R ≠ 0 := by
    intro hzero
    apply hyn
    rw [← hmkR]
    exact (A.incident_projectivization_mk_iff_orientedEvaluation_eq_zero
      rho F.n R hR0).2 hzero
  have hRnRhoPos : 0 < A.arrangementOrientedEvaluation rho F.n R :=
    lt_of_le_of_ne hRnRhoNonneg hRnRhoNe.symm
  have hRnPos : 0 < A.arrangementOrientedEvaluation tau F.n R := by
    simpa only [rho,
      A.arrangementOrientedEvaluation_flipSignAt_of_ne_apply tau F.n_ne_m]
      using hRnRhoPos
  have hXc : A.arrangementOrientedEvaluation tau c X = 0 :=
    A.arrangementOrientedEvaluation_sectorExitNormalizedPoint_eq_zero
      tau l F.m F.n c F.boundary_nonconcurrent x hxSector hxc
  have hRcRho : A.arrangementOrientedEvaluation rho c R = 0 :=
    A.arrangementOrientedEvaluation_sectorExitNormalizedPoint_eq_zero
      rho l F.m F.n c F.boundary_nonconcurrent y hyRho hyc
  have hRc : A.arrangementOrientedEvaluation tau c R = 0 := by
    simpa only [rho,
      A.arrangementOrientedEvaluation_flipSignAt_of_ne_apply tau hcm]
      using hRcRho
  obtain ⟨h, hh0, hh1, hmzero⟩ :=
    exists_strict_barycentric_zero_of_mul_neg
      (mul_neg_of_pos_of_neg hXmPos hRmNeg)
  let Y : Homogeneous3 := (1 - h) • X + h • R
  have hYm : A.arrangementOrientedEvaluation tau F.m Y = 0 := by
    simpa only [Y, LinearMap.map_add, LinearMap.map_smul, smul_eq_mul]
      using hmzero
  have hYc : A.arrangementOrientedEvaluation tau c Y = 0 := by
    simp only [Y, LinearMap.map_add, LinearMap.map_smul, smul_eq_mul,
      hXc, hRc, mul_zero, add_zero]
  have hYl : 0 < A.arrangementOrientedEvaluation tau l Y := by
    simp only [Y, LinearMap.map_add, LinearMap.map_smul, smul_eq_mul,
      hRl, mul_zero, add_zero]
    exact mul_pos (sub_pos.mpr hh1) hXlPos
  have hYn : 0 < A.arrangementOrientedEvaluation tau F.n Y := by
    simp only [Y, LinearMap.map_add, LinearMap.map_smul, smul_eq_mul]
    exact add_pos_of_nonneg_of_pos
      (mul_nonneg (sub_nonneg.mpr hh1.le) hXnNonneg)
      (mul_pos hh0 hRnPos)
  have hY0 : Y ≠ 0 := by
    intro hzero
    rw [hzero, LinearMap.map_zero] at hYl
    exact (lt_irrefl 0 hYl)
  let u : RealProjectivePoint := Projectivization.mk ℝ Y hY0
  have hum : A.Incident u F.m :=
    (A.incident_projectivization_mk_iff_orientedEvaluation_eq_zero
      tau F.m Y hY0).2 hYm
  have huc : A.Incident u c :=
    (A.incident_projectivization_mk_iff_orientedEvaluation_eq_zero
      tau c Y hY0).2 hYc
  have hmc : F.m ≠ c := hcm.symm
  have huEq : u = A.intersection F.m c :=
    A.eq_intersection_of_incident hmc hum huc
  have huVertex : u ∈ A.vertexSet := by
    rw [huEq]
    exact A.intersection_mem_vertexSet hmc
  have huL : ¬ A.Incident u l := by
    intro hul
    have hzero :=
      (A.incident_projectivization_mk_iff_orientedEvaluation_eq_zero
        tau l Y hY0).1 hul
    exact (ne_of_gt hYl) hzero
  have huN : ¬ A.Incident u F.n := by
    intro hun
    have hzero :=
      (A.incident_projectivization_mk_iff_orientedEvaluation_eq_zero
        tau F.n Y hY0).1 hun
    exact (ne_of_gt hYn) hzero
  have huNeP : u ≠ F.p.1 := by
    intro hup
    apply huL
    rw [hup]
    exact F.p_on_base
  have huNeR : u ≠ F.r := by
    intro hur
    apply huN
    rw [hur]
    exact F.r_on_n
  have hcleanPair : 0 <
      A.arrangementOrientedEvaluation G.sigma l Y *
        A.arrangementOrientedEvaluation G.sigma F.n Y := by
    simpa only [← htauL, ← htauN] using mul_pos hYl hYn
  have hsame :=
    G.arrangementRelativeSign_mk_eq_point_of_orientedPair_pos Y hY0 hcleanPair
  exact (F.arrangementRelativeSign_ne_cleanEdgeReference
    G.point u G.point_mem huVertex hum huNeP huNeR) hsame

theorem sigma_return_mem_of_ne_r
    (G : F.CleanEdgeSectorReference)
    (x : RealProjectivePoint) (hxVertex : x ∈ A.vertexSet)
    (hxSector : A.projectivePointMemTriangleSector G.sigma l F.m F.n x)
    (hxl : ¬ A.Incident x l) (hxNeR : x ≠ F.r)
    (c : Line) (hxc : A.Incident x c) (hlc : l ≠ c) :
    A.projectivePointMemTriangleSector G.sigma l F.m F.n
      (A.intersection l c) := by
  exact G.return_mem_of_mem_sector_of_ne_r G.sigma rfl rfl
    x hxVertex hxSector hxl hxNeR c hxc hlc

theorem flipSigma_return_mem_of_ne_r
    (G : F.CleanEdgeSectorReference)
    (x : RealProjectivePoint) (hxVertex : x ∈ A.vertexSet)
    (hxSector : A.projectivePointMemTriangleSector G.flipSigma l F.m F.n x)
    (hxl : ¬ A.Incident x l) (hxNeR : x ≠ F.r)
    (c : Line) (hxc : A.Incident x c) (hlc : l ≠ c) :
    A.projectivePointMemTriangleSector G.flipSigma l F.m F.n
      (A.intersection l c) := by
  exact G.return_mem_of_mem_sector_of_ne_r G.flipSigma
    (A.arrangementOrientedEvaluation_flipSignAt_of_ne
      G.sigma F.m_ne_base.symm)
    (A.arrangementOrientedEvaluation_flipSignAt_of_ne
      G.sigma F.n_ne_m)
    x hxVertex hxSector hxl hxNeR c hxc hlc

/-- Every other marked point of the supporting line has strictly negative
oriented `(l,n)` pair in the clean-edge orientation. -/
theorem orientedPair_neg_of_other_vertex_on_m
    (G : F.CleanEdgeSectorReference) (u : RealProjectivePoint)
    (huVertex : u ∈ A.vertexSet) (huM : A.Incident u F.m)
    (huNeP : u ≠ F.p.1) (huNeR : u ≠ F.r) :
    A.arrangementOrientedEvaluation G.sigma l u.rep *
      A.arrangementOrientedEvaluation G.sigma F.n u.rep < 0 := by
  have huL : ¬ A.Incident u l := by
    intro huL
    apply huNeP
    calc
      u = A.intersection l F.m :=
        A.eq_intersection_of_incident F.m_ne_base.symm huL huM
      _ = F.p.1 := F.p_eq_intersection.symm
  have huN : ¬ A.Incident u F.n := by
    intro huN
    apply huNeR
    calc
      u = A.intersection F.m F.n :=
        A.eq_intersection_of_incident F.n_ne_m.symm huM huN
      _ = F.r := F.r_eq_intersection.symm
  have hulRaw : projectiveLineEvaluation (A.projectiveLine l) u.rep ≠ 0 :=
    (A.projectiveLineEvaluation_rep_eq_zero_iff_incident u l).not.mpr huL
  have hunRaw : projectiveLineEvaluation (A.projectiveLine F.n) u.rep ≠ 0 :=
    (A.projectiveLineEvaluation_rep_eq_zero_iff_incident u F.n).not.mpr huN
  have hzlRaw : projectiveLineEvaluation
      (A.projectiveLine l) G.point.rep ≠ 0 :=
    (A.projectiveLineEvaluation_rep_eq_zero_iff_incident G.point l).not.mpr
      G.point_away_l
  have hznRaw : projectiveLineEvaluation
      (A.projectiveLine F.n) G.point.rep ≠ 0 :=
    (A.projectiveLineEvaluation_rep_eq_zero_iff_incident G.point F.n).not.mpr
      G.point_away_n
  have hulOriented : A.arrangementOrientedEvaluation G.sigma l u.rep ≠ 0 := by
    by_cases hs : G.sigma l <;>
      simp [arrangementOrientedEvaluation, hs, hulRaw]
  have hunOriented :
      A.arrangementOrientedEvaluation G.sigma F.n u.rep ≠ 0 := by
    by_cases hs : G.sigma F.n <;>
      simp [arrangementOrientedEvaluation, hs, hunRaw]
  have horientedNe :
      A.arrangementOrientedEvaluation G.sigma l u.rep *
        A.arrangementOrientedEvaluation G.sigma F.n u.rep ≠ 0 :=
    mul_ne_zero hulOriented hunOriented
  have hsignNe := F.arrangementRelativeSign_ne_cleanEdgeReference
    G.point u G.point_mem huVertex huM huNeP huNeR
  by_contra hneg
  have horientedPos : 0 <
      A.arrangementOrientedEvaluation G.sigma l u.rep *
        A.arrangementOrientedEvaluation G.sigma F.n u.rep :=
    lt_of_le_of_ne (le_of_not_gt hneg) horientedNe.symm
  have heq :
      (A.arrangementOrientedEvaluation G.sigma l u.rep *
          A.arrangementOrientedEvaluation G.sigma F.n u.rep) *
        (A.arrangementOrientedEvaluation G.sigma l G.point.rep *
          A.arrangementOrientedEvaluation G.sigma F.n G.point.rep) =
      (projectiveLineEvaluation (A.projectiveLine l) u.rep *
          projectiveLineEvaluation (A.projectiveLine F.n) u.rep) *
        (projectiveLineEvaluation (A.projectiveLine l) G.point.rep *
          projectiveLineEvaluation (A.projectiveLine F.n) G.point.rep) := by
    by_cases hl : G.sigma l <;> by_cases hn : G.sigma F.n <;>
      simp [arrangementOrientedEvaluation, hl, hn] <;> ring
  have hrawPos : 0 <
      (projectiveLineEvaluation (A.projectiveLine l) u.rep *
          projectiveLineEvaluation (A.projectiveLine F.n) u.rep) *
        (projectiveLineEvaluation (A.projectiveLine l) G.point.rep *
          projectiveLineEvaluation (A.projectiveLine F.n) G.point.rep) := by
    rw [← heq]
    exact mul_pos horientedPos G.point_orientedPair_pos
  apply hsignNe
  rw [A.arrangementRelativeSign_apply_rep,
    A.arrangementRelativeSign_apply_rep]
  exact (sign_eq_sign_iff_mul_pos
    (mul_ne_zero hulRaw hunRaw) (mul_ne_zero hzlRaw hznRaw)).2 hrawPos

/-- The `m`-side crossing of every nondegenerate transversal is on the
non-clean component. -/
theorem leftWitness_orientedPair_neg
    (G : F.CleanEdgeSectorReference)
    {v : A.CircularGapSlot l}
    (T : F.NondegenerateTransverseFront v) :
    A.orientedIntersectionPairEvaluation G.sigma F.m T.cross l F.n < 0 := by
  simpa only [orientedIntersectionPairEvaluation,
    TransverseFront.leftWitness] using
    G.orientedPair_neg_of_other_vertex_on_m
      T.toTransverseFront.leftWitness
      T.toTransverseFront.leftWitness_mem_vertexSet
      T.toTransverseFront.leftWitness_incident_m
      T.toTransverseFront.leftWitness_ne_p T.leftWitness_ne_r

theorem orientedIntersectionPairEvaluation_base_eq
    (G : F.CleanEdgeSectorReference)
    {v : A.CircularGapSlot l}
    (T : F.NondegenerateTransverseFront v) :
    A.orientedIntersectionPairEvaluation G.sigma l T.cross F.m F.n =
      G.orientedBaseSideProduct v := by
  have hvBase : A.Incident v.1 l :=
    ((A.mem_lineVertexSet l).mp v.2).2
  have hvEq : v.1 = A.intersection l T.cross :=
    A.eq_intersection_of_incident T.cross_ne_base.symm
      hvBase T.v_on_cross
  unfold orientedIntersectionPairEvaluation orientedBaseSideProduct
  rw [← hvEq]

/-- With the clean-edge orientation fixed, Menelaus says that the right
witness has negative side sign exactly in the negative base class. -/
theorem rightWitnessSide_neg_iff_baseSide_neg
    (G : F.CleanEdgeSectorReference)
    {v : A.CircularGapSlot l}
    (T : F.NondegenerateTransverseFront v) :
    A.orientedIntersectionPairEvaluation G.sigma F.n T.cross l F.m < 0 ↔
      A.orientedIntersectionPairEvaluation G.sigma l T.cross F.m F.n < 0 := by
  rw [T.orientedNSide_neg_iff_orientedBase_mul_mSide_pos]
  have hm := G.leftWitness_orientedPair_neg T
  constructor
  · intro h
    rcases mul_pos_iff.mp h with h | h
    · exact (not_lt_of_ge hm.le h.2).elim
    · exact h.1
  · intro h
    exact mul_pos_of_neg_of_neg h hm

theorem rightWitnessSide_neg_iff_orientedBase_neg
    (G : F.CleanEdgeSectorReference)
    {v : A.CircularGapSlot l}
    (T : F.NondegenerateTransverseFront v) :
    A.orientedIntersectionPairEvaluation G.sigma F.n T.cross l F.m < 0 ↔
      G.orientedBaseSideProduct v < 0 := by
  rw [G.rightWitnessSide_neg_iff_baseSide_neg T,
    G.orientedIntersectionPairEvaluation_base_eq T]

theorem rightWitnessSide_ne_zero
    (G : F.CleanEdgeSectorReference)
    {v : A.CircularGapSlot l}
    (T : F.NondegenerateTransverseFront v) :
    A.orientedIntersectionPairEvaluation G.sigma F.n T.cross l F.m ≠ 0 := by
  intro hzero
  have hneg := T.orientedIntersectionSideProducts_mul_neg G.sigma
  rw [hzero, mul_zero] at hneg
  exact (lt_irrefl 0 hneg)

theorem rightWitness_mem_sigma_of_orientedBase_pos
    (G : F.CleanEdgeSectorReference)
    {v : A.CircularGapSlot l}
    (T : F.NondegenerateTransverseFront v)
    (hbase : 0 < G.orientedBaseSideProduct v) :
    A.projectivePointMemTriangleSector G.sigma l F.m F.n
      T.toTransverseFront.rightWitness := by
  have hnotNeg : ¬
      A.orientedIntersectionPairEvaluation G.sigma F.n T.cross l F.m < 0 := by
    intro hneg
    exact (not_lt_of_ge hbase.le)
      ((G.rightWitnessSide_neg_iff_orientedBase_neg T).mp hneg)
  have hside : 0 <
      A.orientedIntersectionPairEvaluation G.sigma F.n T.cross l F.m :=
    lt_of_le_of_ne (le_of_not_gt hnotNeg) (G.rightWitnessSide_ne_zero T).symm
  have hpair : 0 <
      A.arrangementOrientedEvaluation G.sigma l
          T.toTransverseFront.rightWitness.rep *
        A.arrangementOrientedEvaluation G.sigma F.m
          T.toTransverseFront.rightWitness.rep := by
    simpa only [orientedIntersectionPairEvaluation,
      ← T.toTransverseFront.rightWitness_eq_intersection_n_cross] using hside
  have hmem :=
    A.projectivePointMemTriangleSector_of_incident_middle_of_pair_pos
      G.sigma l F.n F.m T.toTransverseFront.rightWitness
        T.toTransverseFront.rightWitness_incident_n hpair
  unfold projectivePointMemTriangleSector at hmem ⊢
  have hset : ({l, F.n, F.m} : Finset Line) = {l, F.m, F.n} := by
    ext k
    simp [or_comm, or_left_comm, or_assoc]
  simpa only [hset] using hmem

theorem rightWitness_mem_flipSigma_of_orientedBase_neg
    (G : F.CleanEdgeSectorReference)
    {v : A.CircularGapSlot l}
    (T : F.NondegenerateTransverseFront v)
    (hbase : G.orientedBaseSideProduct v < 0) :
    A.projectivePointMemTriangleSector G.flipSigma l F.m F.n
      T.toTransverseFront.rightWitness := by
  have hside :
      A.orientedIntersectionPairEvaluation G.sigma F.n T.cross l F.m < 0 :=
    (G.rightWitnessSide_neg_iff_orientedBase_neg T).2 hbase
  have hpairSigma :
      A.arrangementOrientedEvaluation G.sigma l
          T.toTransverseFront.rightWitness.rep *
        A.arrangementOrientedEvaluation G.sigma F.m
          T.toTransverseFront.rightWitness.rep < 0 := by
    simpa only [orientedIntersectionPairEvaluation,
      ← T.toTransverseFront.rightWitness_eq_intersection_n_cross] using hside
  have hpairFlip : 0 <
      A.arrangementOrientedEvaluation G.flipSigma l
          T.toTransverseFront.rightWitness.rep *
        A.arrangementOrientedEvaluation G.flipSigma F.m
          T.toTransverseFront.rightWitness.rep := by
    rw [flipSigma,
      A.arrangementOrientedEvaluation_flipSignAt_of_ne_apply
        G.sigma F.m_ne_base.symm,
      A.arrangementOrientedEvaluation_flipSignAt_self_apply]
    simpa only [mul_neg] using (neg_pos.mpr hpairSigma)
  have hmem :=
    A.projectivePointMemTriangleSector_of_incident_middle_of_pair_pos
      G.flipSigma l F.n F.m T.toTransverseFront.rightWitness
        T.toTransverseFront.rightWitness_incident_n hpairFlip
  unfold projectivePointMemTriangleSector at hmem ⊢
  have hset : ({l, F.n, F.m} : Finset Line) = {l, F.m, F.n} := by
    ext k
    simp [or_comm, or_left_comm, or_assoc]
  simpa only [hset] using hmem

theorem sigmaSector_nonempty_of_orientedBase_pos
    (G : F.CleanEdgeSectorReference)
    {v : A.CircularGapSlot l}
    (T : F.NondegenerateTransverseFront v)
    (hbase : 0 < G.orientedBaseSideProduct v) :
    (A.triangleSectorOffBaseVertexSet G.sigma l F.m F.n).Nonempty := by
  classical
  refine ⟨T.toTransverseFront.rightWitness, Finset.mem_filter.mpr ?_⟩
  exact ⟨T.toTransverseFront.rightWitness_mem_vertexSet,
    G.rightWitness_mem_sigma_of_orientedBase_pos T hbase,
    T.toTransverseFront.rightWitness_away⟩

theorem flipSector_nonempty_of_orientedBase_neg
    (G : F.CleanEdgeSectorReference)
    {v : A.CircularGapSlot l}
    (T : F.NondegenerateTransverseFront v)
    (hbase : G.orientedBaseSideProduct v < 0) :
    (A.triangleSectorOffBaseVertexSet G.flipSigma l F.m F.n).Nonempty := by
  classical
  refine ⟨T.toTransverseFront.rightWitness, Finset.mem_filter.mpr ?_⟩
  exact ⟨T.toTransverseFront.rightWitness_mem_vertexSet,
    G.rightWitness_mem_flipSigma_of_orientedBase_neg T hbase,
    T.toTransverseFront.rightWitness_away⟩

/-- Lossless one-sector output sufficient for the finite Kelly fallback:
it retains the transverse witness used to separate a local minimizer from
the far apex, and return closure everywhere else. -/
structure OneCanonicalSectorFront (G : F.CleanEdgeSectorReference) where
  v : A.CircularGapSlot l
  transverse : F.NondegenerateTransverseFront v
  sectorSigma : Line → Bool
  sectorSigma_on_base :
    A.arrangementOrientedEvaluation sectorSigma l =
      A.arrangementOrientedEvaluation G.sigma l
  sectorSigma_on_far :
    A.arrangementOrientedEvaluation sectorSigma F.n =
      A.arrangementOrientedEvaluation G.sigma F.n
  witness_mem : A.projectivePointMemTriangleSector
    sectorSigma l F.m F.n transverse.toTransverseFront.rightWitness
  sector_nonempty :
    (A.triangleSectorOffBaseVertexSet sectorSigma l F.m F.n).Nonempty
  return_mem_of_ne_r : ∀ x : RealProjectivePoint, x ∈ A.vertexSet →
    A.projectivePointMemTriangleSector sectorSigma l F.m F.n x →
    ¬ A.Incident x l → x ≠ F.r →
    ∀ c : Line, A.Incident x c → l ≠ c →
      A.projectivePointMemTriangleSector sectorSigma l F.m F.n
        (A.intersection l c)

theorem OneCanonicalSectorFront.witness_not_incident_m
    (G : F.CleanEdgeSectorReference)
    (S : OneCanonicalSectorFront G) :
    ¬ A.Incident S.transverse.toTransverseFront.rightWitness F.m := by
  intro hwm
  apply S.transverse.r_not_on_cross
  have hwr : S.transverse.toTransverseFront.rightWitness = F.r := by
    calc
      S.transverse.toTransverseFront.rightWitness =
          A.intersection F.m F.n :=
        A.eq_intersection_of_incident F.n_ne_m.symm hwm
          S.transverse.toTransverseFront.rightWitness_incident_n
      _ = F.r := F.r_eq_intersection.symm
  rw [← hwr]
  exact S.transverse.toTransverseFront.rightWitness_incident_cross

/-- Any third marked base point chooses one of the two clean-edge-oriented
sectors according to its intrinsic Menelaus sign class. -/
theorem exists_oneCanonicalSectorFront
    (G : F.CleanEdgeSectorReference)
    (hone : A.lineOrdinaryVertexDegree l = 1)
    (hthree : 3 ≤ Fintype.card (A.CircularGapSlot l)) :
    Nonempty (OneCanonicalSectorFront G) := by
  obtain ⟨v, hvp, hvq⟩ :=
    A.exists_circularGapSlot_val_ne_pair_of_three_le
      l hthree F.pSlot F.q F.q_ne_p.symm
  have hvpSlot : v ≠ F.pSlot := by
    intro h
    exact hvp (congrArg Subtype.val h)
  have hvqSlot : v ≠ F.q := by
    intro h
    exact hvq (congrArg Subtype.val h)
  obtain ⟨T⟩ := F.exists_nondegenerateTransverseFront
    hone v hvpSlot hvqSlot
  rcases G.orientedBaseSideProduct_pos_or_neg v hvpSlot hvqSlot with
      hpos | hneg
  · exact ⟨{
      v := v
      transverse := T
      sectorSigma := G.sigma
      sectorSigma_on_base := rfl
      sectorSigma_on_far := rfl
      witness_mem := G.rightWitness_mem_sigma_of_orientedBase_pos T hpos
      sector_nonempty := G.sigmaSector_nonempty_of_orientedBase_pos T hpos
      return_mem_of_ne_r := by
        intro x hxVertex hxSector hxl hxNeR c hxc hlc
        exact G.sigma_return_mem_of_ne_r
          x hxVertex hxSector hxl hxNeR c hxc hlc
    }⟩
  · exact ⟨{
      v := v
      transverse := T
      sectorSigma := G.flipSigma
      sectorSigma_on_base :=
        A.arrangementOrientedEvaluation_flipSignAt_of_ne
          G.sigma F.m_ne_base.symm
      sectorSigma_on_far :=
        A.arrangementOrientedEvaluation_flipSignAt_of_ne
          G.sigma F.n_ne_m
      witness_mem := G.rightWitness_mem_flipSigma_of_orientedBase_neg T hneg
      sector_nonempty := G.flipSector_nonempty_of_orientedBase_neg T hneg
      return_mem_of_ne_r := by
        intro x hxVertex hxSector hxl hxNeR c hxc hlc
        exact G.flipSigma_return_mem_of_ne_r
          x hxVertex hxSector hxl hxNeR c hxc hlc
    }⟩

end CleanEdgeSectorReference

end FelsnerOneLineCleanFrame

end OrdinaryAttachmentOuterSectorFront

end FiniteProjectiveLineArrangement

end Erdos506.Incidence
