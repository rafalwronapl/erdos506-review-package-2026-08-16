import Erdos506.Incidence.ProjectiveLineArrangement
import Erdos506.Incidence.RadicalAxisFourFourGeometry

/-!
# Projective realization of determined affine lines

Every determined affine line is represented by the homogeneous cross-product
covector of a canonically selected spanning pair.  The construction is
lossless: its projective incidence with the labelled affine chart is exactly
the original affine-line incidence.
-/

namespace Erdos506.Incidence

open Erdos506.Finite
open Erdos506.V4
open scoped LinearAlgebra.Projectivization

variable {alpha : Type*} [Fintype alpha] [DecidableEq alpha]

/-- A canonical pair of labels which spans a determined line. -/
noncomputable def DeterminedLine.spanningPair
    {cfg : Configuration alpha} (L : DeterminedLine cfg) : KSubset alpha 2 :=
  Classical.choose L.exists_pair

/-- The canonical pair chosen for a determined line has precisely that line
as its affine span. -/
theorem DeterminedLine.spanningPair_spec
    {cfg : Configuration alpha} (L : DeterminedLine cfg) :
    lineOfPair cfg L.spanningPair = L.1 :=
  Classical.choose_spec L.exists_pair

/-- The projective covector assigned to a determined line.  Concretely this
is the homogeneous cross product of the affine lifts of the two labels in
`L.spanningPair`. -/
noncomputable def determinedProjectiveLine
    (cfg : Configuration alpha) (L : DeterminedLine cfg) : RealProjectiveLine :=
  projectiveChordLine cfg L.spanningPair

/-- The affine-chart embedding used by the arrangement agrees with the
coordinate embedding used by the homogeneous chord lemmas. -/
theorem affinePointToProjective_eq_projectivePoint (p : Point2) :
    affinePointToProjective p = projectivePoint p := by
  rfl

/-- Incidence with a homogeneous chord covector is exactly membership in the
affine line spanned by its two labels. -/
theorem affinePoint_mem_projectiveChordLine_iff
    (cfg : Configuration alpha) (e : KSubset alpha 2) (r : Point2) :
    affinePointToProjective r ∈ projectiveChordLine cfg e ↔ r ∈ lineOfPair cfg e := by
  rw [lineOfPair_eq_affineSpan_chordPoints]
  rw [affinePointToProjective_eq_projectivePoint]
  simpa only [projectiveChordLine, projectiveLine, projectivePoint,
    Projectivization.orthogonal_mk, homogeneousIncident] using
    (homogeneousIncident_lineCovector_iff_mem_affineSpan
      (chordPoint_zero_ne_one cfg e))

/-- Projective incidence of a label with its assigned determined line is
equivalent to the original affine incidence. -/
theorem affinePoint_mem_determinedProjectiveLine_iff
    (cfg : Configuration alpha) (a : alpha) (L : DeterminedLine cfg) :
    affinePointToProjective (cfg a) ∈ determinedProjectiveLine cfg L ↔
      cfg a ∈ L.1 := by
  change affinePointToProjective (cfg a) ∈ projectiveChordLine cfg L.spanningPair ↔
    cfg a ∈ L.1
  rw [affinePoint_mem_projectiveChordLine_iff, L.spanningPair_spec]

/-- Different determined affine lines receive different homogeneous
covectors. -/
theorem determinedProjectiveLine_injective
    (cfg : Configuration alpha) :
    Function.Injective (determinedProjectiveLine cfg) := by
  intro L M hLM
  apply Subtype.ext
  have hline : lineOfPair cfg L.spanningPair = M.1 := by
    apply lineOfPair_eq_of_mem_of_direction_finrank_one cfg L.spanningPair M.1
    · intro x hx
      have hxPair : cfg x ∈ lineOfPair cfg L.spanningPair := by
        apply subset_affineSpan ℝ (cfg '' (L.spanningPair.1 : Set alpha))
        exact ⟨x, hx, rfl⟩
      have hxProjective :
          affinePointToProjective (cfg x) ∈ determinedProjectiveLine cfg L :=
        (affinePoint_mem_determinedProjectiveLine_iff cfg x L).2
          (by simpa only [L.spanningPair_spec] using hxPair)
      have hxProjective' :
          affinePointToProjective (cfg x) ∈ determinedProjectiveLine cfg M := by
        rw [← hLM]
        exact hxProjective
      exact (affinePoint_mem_determinedProjectiveLine_iff cfg x M).1 hxProjective'
    · exact M.direction_finrank
  exact L.spanningPair_spec.symm.trans hline

/-- The canonical lossless projective realization of every finite injective
real configuration. -/
noncomputable def determinedLineProjectiveRealization
    (cfg : Configuration alpha) : DeterminedLineProjectiveRealization cfg where
  projectiveLine := determinedProjectiveLine cfg
  projectiveLine_injective := determinedProjectiveLine_injective cfg
  label_incident_iff := affinePoint_mem_determinedProjectiveLine_iff cfg

/-- For the canonical realization, the original support finset is exactly
the finset of labels incident with the corresponding homogeneous covector. -/
theorem lineSupport_eq_determinedLineLabelIncidence
    (cfg : Configuration alpha) (L : DeterminedLine cfg) :
    lineSupport cfg L =
      (determinedLineProjectiveRealization cfg).labelIncidence L :=
  DeterminedLineProjectiveRealization.lineSupport_eq_labelIncidence
    (determinedLineProjectiveRealization cfg) L

end Erdos506.Incidence
