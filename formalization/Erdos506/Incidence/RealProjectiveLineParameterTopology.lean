import Erdos506.Incidence.RealProjectiveArrangementTopology
import Mathlib.LinearAlgebra.Projectivization.Cardinality
import Mathlib.Topology.Algebra.ConstMulAction
import Mathlib.Topology.Homeomorph.Quotient
import Mathlib.Topology.LocalAtTarget

/-!
# Topology of the projective-line parametrization

This file packages the algebraic equivalence between `RP¹` and the points of
one line in `RP²` as a homeomorphism.  The proof uses the open quotient maps
from nonzero homogeneous vectors, rather than compactness or a separately
postulated Hausdorff structure on projective space.
-/

namespace Erdos506.Incidence

open Topology
open scoped LinearAlgebra.Projectivization

namespace FiniteProjectiveLineArrangement

/-- The quotient topology on the real projective line. -/
@[reducible] noncomputable def realProjectiveOnePointQuotientTopology :
    TopologicalSpace RealProjectiveOnePoint :=
  @instTopologicalSpaceQuotient
    {v : RealProjectiveLineVector // v ≠ 0}
    (projectivizationSetoid ℝ RealProjectiveLineVector)
    (by infer_instance)

noncomputable local instance realProjectiveOnePointTopologyForLineParameter :
    TopologicalSpace RealProjectiveOnePoint :=
  realProjectiveOnePointQuotientTopology

noncomputable local instance realProjectivePointTopologyForLineParameter :
    TopologicalSpace RealProjectivePoint :=
  realProjectivePointQuotientTopology

local instance nonzeroHomogeneousContinuousConstSmul :
    ContinuousConstSMul ℝˣ {v : Homogeneous3 // v ≠ 0} where
  continuous_const_smul a := by
    exact ((continuous_const_smul (a : ℝ)).comp
      continuous_subtype_val).subtype_mk _

/-- Replace the defining projectivization relation on nonzero homogeneous
vectors by the equivalent orbit relation of the unit group. -/
noncomputable def realProjectivePointOrbitHomeomorph :
    RealProjectivePoint ≃ₜ
      Quotient (MulAction.orbitRel ℝˣ
        {v : Homogeneous3 // v ≠ 0}) :=
  Homeomorph.Quotient.congrRight fun x y =>
    (Units.orbitRel_nonZero_iff ℝ Homogeneous3 x y).symm

/-- The quotient map from nonzero homogeneous vectors to `RP²` is an open
quotient map. -/
theorem isOpenQuotientMap_realProjectivePoint_mk :
    IsOpenQuotientMap
      (Projectivization.mk' ℝ :
        {v : Homogeneous3 // v ≠ 0} → RealProjectivePoint) := by
  have h := realProjectivePointOrbitHomeomorph.symm.isOpenQuotientMap.comp
    (MulAction.isOpenQuotientMap_quotientMk
      (Γ := ℝˣ) (T := {v : Homogeneous3 // v ≠ 0}))
  simpa only [Function.comp_apply] using h

/-- The homogeneous linear parametrization restricted to nonzero vectors. -/
noncomputable def projectiveLineParameterNonzeroMap
    (L : RealProjectiveLine) :
    {u : RealProjectiveLineVector // u ≠ 0} →
      {v : Homogeneous3 // v ≠ 0} :=
  fun u =>
    ⟨projectiveLineParameterLinearMap L u.1,
      by
        simpa only [map_zero] using
          Function.Injective.ne
            (projectiveLineParameterLinearMap_injective L) u.2⟩

/-- The nonzero homogeneous parametrization is a topological embedding. -/
theorem isEmbedding_projectiveLineParameterNonzeroMap
    (L : RealProjectiveLine) :
    IsEmbedding (projectiveLineParameterNonzeroMap L) := by
  have hambient : IsEmbedding (projectiveLineParameterLinearMap L) :=
    ((projectiveLineParameterLinearMap L).isClosedEmbedding_of_injective
      (LinearMap.ker_eq_bot.mpr
        (projectiveLineParameterLinearMap_injective L))).isEmbedding
  apply IsEmbedding.subtypeVal.of_comp_iff.mp
  simpa only [Function.comp_apply, projectiveLineParameterNonzeroMap] using
    hambient.comp IsEmbedding.subtypeVal

@[simp]
theorem projectiveLineParameter_mk_nonzeroMap
    (L : RealProjectiveLine)
    (u : {u : RealProjectiveLineVector // u ≠ 0}) :
    projectiveLineParameter L (Projectivization.mk' ℝ u) =
      Projectivization.mk' ℝ (projectiveLineParameterNonzeroMap L u) := by
  simp only [projectiveLineParameter, Projectivization.mk'_eq_mk,
    Projectivization.map_mk, projectiveLineParameterNonzeroMap]

/-- The projective parametrization embeds `RP¹` with exactly the topology
induced from the ambient real projective plane. -/
theorem isEmbedding_projectiveLineParameter
    (L : RealProjectiveLine) :
    IsEmbedding (projectiveLineParameter L) := by
  let f := projectiveLineParameterNonzeroMap L
  let p := (Projectivization.mk' ℝ :
    {u : RealProjectiveLineVector // u ≠ 0} → RealProjectiveOnePoint)
  let q := (Projectivization.mk' ℝ :
    {v : Homogeneous3 // v ≠ 0} → RealProjectivePoint)
  let g := projectiveLineParameter L
  have hcomm : g ∘ p = q ∘ f := by
    funext u
    exact projectiveLineParameter_mk_nonzeroMap L u
  have hp : IsQuotientMap p := by
    change IsQuotientMap
      (@Quotient.mk'
        {u : RealProjectiveLineVector // u ≠ 0}
        (projectivizationSetoid ℝ RealProjectiveLineVector))
    exact isQuotientMap_quotient_mk'
  have hsat : q ⁻¹' (q '' Set.range f) ⊆ Set.range f := by
    rintro y ⟨z, ⟨x, rfl⟩, hz⟩
    change Projectivization.mk ℝ
        (projectiveLineParameterNonzeroMap L x).1
          (projectiveLineParameterNonzeroMap L x).2 =
      Projectivization.mk ℝ y.1 y.2 at hz
    obtain ⟨a, ha⟩ :=
      (Projectivization.mk_eq_mk_iff ℝ y.1
        (projectiveLineParameterNonzeroMap L x).1 y.2
        (projectiveLineParameterNonzeroMap L x).2).mp hz.symm
    let u : RealProjectiveLineVector := (a : ℝ) • x.1
    have hu : u ≠ 0 := smul_ne_zero (Units.ne_zero a) x.2
    refine ⟨⟨u, hu⟩, ?_⟩
    apply Subtype.ext
    change projectiveLineParameterLinearMap L u = y.1
    rw [show u = (a : ℝ) • x.1 by rfl, map_smul]
    simpa only [Units.smul_def] using ha
  exact isEmbedding_of_isOpenQuotientMap_of_isInducing f g p q hcomm
    (isEmbedding_projectiveLineParameterNonzeroMap L).toIsInducing hp
    isOpenQuotientMap_realProjectivePoint_mk
    (projectiveLineParameter_injective L) hsat

/-- The chosen algebraic parametrization identifies `RP¹` homeomorphically
with the incident-point subtype of the corresponding line in `RP²`. -/
noncomputable def projectiveLineParameterHomeomorph
    (L : RealProjectiveLine) :
    RealProjectiveOnePoint ≃ₜ
      {p : RealProjectivePoint // p.orthogonal L} :=
  (projectiveLineParameterEquiv L).toHomeomorphOfIsInducing (by
    apply IsInducing.subtypeVal.of_comp_iff.mp
    simpa only [Function.comp_apply, projectiveLineParameterEquiv] using
      (isEmbedding_projectiveLineParameter L).toIsInducing)

@[simp]
theorem projectiveLineParameterHomeomorph_apply
    (L : RealProjectiveLine) (P : RealProjectiveOnePoint) :
    (projectiveLineParameterHomeomorph L P).1 =
      projectiveLineParameter L P :=
  rfl

end FiniteProjectiveLineArrangement

end Erdos506.Incidence
