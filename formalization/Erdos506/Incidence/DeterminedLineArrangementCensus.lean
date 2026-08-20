import Erdos506.Incidence.DeterminedLineProjectiveRealization
import Erdos506.Incidence.EvenArrangementPrinciple

/-!
# The dual arrangement census of a determined-line configuration

The projective realization of determined affine lines has a useful dual
reading.  Regard every embedded labelled point as a projective *line* (using
the standard self-duality of the real projective plane).  Then the projective
covector of a determined affine line is a vertex of this labelled-line
arrangement, and its vertex multiplicity is exactly the original line
support cardinality.

All constructions below are finite and algebraic.  Faces, Euler's relation,
and the face-edge handshake are deliberately not manufactured here.
-/

namespace Erdos506.Incidence

open Erdos506.V4
open scoped BigOperators LinearAlgebra.Projectivization

variable {alpha : Type*} [Fintype alpha] [DecidableEq alpha]

/-- The dual projective arrangement: its indexed lines are the homogeneous
covectors of the labelled affine points. -/
noncomputable def labelDualArrangement
    (cfg : Configuration alpha) : FiniteProjectiveLineArrangement alpha where
  projectiveLine := fun a => affinePointToProjective (cfg a)
  projectiveLine_injective := affinePointToProjective_injective.comp cfg.injective

/-- Actual projective vertices of the labelled-line arrangement. -/
noncomputable def labelDualVertexSet
    (cfg : Configuration alpha) : Finset RealProjectivePoint :=
  (labelDualArrangement cfg).vertexSet

/-- The dual point representing a determined affine line. -/
noncomputable def determinedLineDualVertex
    (cfg : Configuration alpha) (L : DeterminedLine cfg) : RealProjectivePoint :=
  (determinedLineProjectiveRealization cfg).projectiveLine L

/-- A label is incident with the dual line of a determined line exactly when
it belongs to that affine line's support. -/
theorem labelDual_incident_determinedLine_iff
    (cfg : Configuration alpha) (a : alpha) (L : DeterminedLine cfg) :
    (labelDualArrangement cfg).Incident (determinedLineDualVertex cfg L) a ↔
      cfg a ∈ L.1 := by
  change Projectivization.orthogonal (determinedLineDualVertex cfg L)
    (affinePointToProjective (cfg a)) ↔ cfg a ∈ L.1
  rw [Projectivization.orthogonal_comm]
  exact affinePoint_mem_determinedProjectiveLine_iff cfg a L

/-- The dual vertex multiplicity at a determined line is exactly its labelled
affine support size. -/
theorem labelDual_multiplicity_determinedLine
    (cfg : Configuration alpha) (L : DeterminedLine cfg) :
    (labelDualArrangement cfg).multiplicity (determinedLineDualVertex cfg L) =
      (lineSupport cfg L).card := by
  classical
  unfold FiniteProjectiveLineArrangement.multiplicity
  congr 1
  ext a
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact (labelDual_incident_determinedLine_iff cfg a L).trans mem_lineSupport.symm

/-- The projective intersection of any two distinct labelled dual lines is
an actual vertex of the census. -/
theorem labelDualIntersection_mem_vertexSet
    (cfg : Configuration alpha) {a b : alpha} (hab : a ≠ b) :
    (labelDualArrangement cfg).intersection a b ∈ labelDualVertexSet cfg :=
  (labelDualArrangement cfg).intersection_mem_vertexSet hab

/-- Each of the two labels defining a dual intersection is incident with its
actual projective vertex. -/
theorem labelDualIntersection_incident_left
    (cfg : Configuration alpha) {a b : alpha} (hab : a ≠ b) :
    (labelDualArrangement cfg).Incident
      ((labelDualArrangement cfg).intersection a b) a :=
  (labelDualArrangement cfg).intersection_incident_left hab

theorem labelDualIntersection_incident_right
    (cfg : Configuration alpha) {a b : alpha} (hab : a ≠ b) :
    (labelDualArrangement cfg).Incident
      ((labelDualArrangement cfg).intersection a b) b :=
  (labelDualArrangement cfg).intersection_incident_right hab

/-- Every actual dual vertex arises from a pair of distinct labels. -/
theorem exists_label_pair_of_mem_labelDualVertexSet
    (cfg : Configuration alpha) {p : RealProjectivePoint}
    (hp : p ∈ labelDualVertexSet cfg) :
    ∃ a b : alpha, a ≠ b ∧ (labelDualArrangement cfg).intersection a b = p :=
  (labelDualArrangement cfg).exists_lines_of_mem_vertexSet hp

/-- A dual vertex defined by two different labels has multiplicity at least
two. -/
theorem two_le_labelDualMultiplicity_intersection
    (cfg : Configuration alpha) {a b : alpha} (hab : a ≠ b) :
    2 ≤ (labelDualArrangement cfg).multiplicity
      ((labelDualArrangement cfg).intersection a b) :=
  (labelDualArrangement cfg).two_le_multiplicity_intersection hab

/-- The canonical spanning pair of a determined line produces exactly its
dual vertex as an actual intersection of two labelled dual lines.  This is
the promised pair-level identity: no formal pair-vertex is retained. -/
theorem determinedLineDualVertex_eq_labelDualIntersection
    (cfg : Configuration alpha) (L : DeterminedLine cfg) :
    determinedLineDualVertex cfg L =
      (labelDualArrangement cfg).intersection
        (chordLabel L.spanningPair 0) (chordLabel L.spanningPair 1) := by
  classical
  let e := L.spanningPair
  have hne : chordLabel e 0 ≠ chordLabel e 1 := chordLabel_zero_ne_one e
  unfold determinedLineDualVertex determinedLineProjectiveRealization
    determinedProjectiveLine labelDualArrangement
    FiniteProjectiveLineArrangement.intersection
  rw [dif_neg hne]
  change projectiveChordLine cfg e =
    projectiveLineIntersection
      (affinePointToProjective (cfg (chordLabel e 0)))
      (affinePointToProjective (cfg (chordLabel e 1))) _
  have hP : Projectivization.orthogonal
      (affinePointToProjective (cfg (chordLabel e 0)))
      (projectiveChordLine cfg e) := by
    rw [affinePointToProjective_eq_projectivePoint]
    simpa only [chordPoint] using
      (projectivePoint_orthogonal_projectiveChordLine cfg e
        (chordLabel_mem e 0))
  have hQ : Projectivization.orthogonal
      (affinePointToProjective (cfg (chordLabel e 1)))
      (projectiveChordLine cfg e) := by
    rw [affinePointToProjective_eq_projectivePoint]
    simpa only [chordPoint] using
      (projectivePoint_orthogonal_projectiveChordLine cfg e
        (chordLabel_mem e 1))
  have hPQ :
      affinePointToProjective (cfg (chordLabel e 0)) ≠
        affinePointToProjective (cfg (chordLabel e 1)) :=
    affinePointToProjective_ne
      (cfg.injective.ne (chordLabel_zero_ne_one e))
  simpa only [projectiveLineIntersection] using
    (projectiveCovector_eq_cross_of_orthogonal hPQ hP hQ)

/-- Hence every determined affine line is represented by an actual (rather
than formal) vertex of the labelled dual arrangement. -/
theorem determinedLineDualVertex_mem_labelDualVertexSet
    (cfg : Configuration alpha) (L : DeterminedLine cfg) :
    determinedLineDualVertex cfg L ∈ labelDualVertexSet cfg := by
  rw [determinedLineDualVertex_eq_labelDualIntersection]
  exact labelDualIntersection_mem_vertexSet cfg (chordLabel_zero_ne_one L.spanningPair)

/-- Incidence with two distinct labelled dual lines determines their actual
intersection point, so concurrent pairs are identified in the vertex census. -/
theorem labelDual_eq_intersection_of_incident
    (cfg : Configuration alpha) {a b : alpha} (hab : a ≠ b)
    {p : RealProjectivePoint}
    (hpa : (labelDualArrangement cfg).Incident p a)
    (hpb : (labelDualArrangement cfg).Incident p b) :
    p = (labelDualArrangement cfg).intersection a b :=
  (labelDualArrangement cfg).eq_intersection_of_incident hab hpa hpb

/-! ## Adapter to the finite cellulation interface -/

/-- If a projective cellulation is supplied with determined lines as its
dual vertices, its prescribed multiplicity agrees with the concrete
labelled-line census precisely when it agrees with this formula. -/
theorem lineMelchior_of_dualCellulation
    {Edge Face : Type*} [Fintype Edge] [Fintype Face] [DecidableEq Edge]
    (cfg : Configuration alpha)
    (C : ProjectiveArrangementCellulation (DeterminedLine cfg) Edge Face)
    (hmult : ∀ L : DeterminedLine cfg,
      C.multiplicity L =
        (labelDualArrangement cfg).multiplicity (determinedLineDualVertex cfg L)) :
    LineMelchior cfg := by
  apply lineMelchior_of_cellulation cfg C
  intro L
  rw [hmult L, labelDual_multiplicity_determinedLine]

/-- The configuration's combinatorial Melchior slack is exactly the slack of
any dual cellulation whose vertex multiplicities are the concrete census
multiplicities above. -/
theorem lineMelchiorSlack_eq_dualCellulationSlack
    {Edge Face : Type*} [Fintype Edge] [Fintype Face] [DecidableEq Edge]
    (cfg : Configuration alpha)
    (C : ProjectiveArrangementCellulation (DeterminedLine cfg) Edge Face)
    (hmult : ∀ L : DeterminedLine cfg,
      C.multiplicity L =
        (labelDualArrangement cfg).multiplicity (determinedLineDualVertex cfg L)) :
    lineMelchiorSlack cfg = C.melchiorSlack := by
  unfold lineMelchiorSlack ProjectiveArrangementCellulation.melchiorSlack
  congr 1
  apply Finset.sum_congr rfl
  intro L _
  rw [hmult L, labelDual_multiplicity_determinedLine]

/-- After the exact dual census and the Euler/edge-count identities, the
entire Melchior slack is the single face-edge defect `2E - 3F`.  Thus the
only remaining inequality for Melchior is the face-edge handshake. -/
theorem lineMelchiorSlack_eq_dualFaceDefect
    {Edge Face : Type*} [Fintype Edge] [Fintype Face] [DecidableEq Edge]
    (cfg : Configuration alpha)
    (C : ProjectiveArrangementCellulation (DeterminedLine cfg) Edge Face)
    (hmult : ∀ L : DeterminedLine cfg,
      C.multiplicity L =
        (labelDualArrangement cfg).multiplicity (determinedLineDualVertex cfg L)) :
    lineMelchiorSlack cfg =
      2 * (Fintype.card Edge : ℤ) - 3 * (Fintype.card Face : ℤ) := by
  calc
    lineMelchiorSlack cfg = C.melchiorSlack :=
      lineMelchiorSlack_eq_dualCellulationSlack cfg C hmult
    _ = 3 * (Fintype.card (DeterminedLine cfg) : ℤ) -
          Fintype.card Edge - 3 := C.melchiorSlack_eq
    _ = 2 * (Fintype.card Edge : ℤ) - 3 * (Fintype.card Face : ℤ) := by
      have heuler :
          (Fintype.card (DeterminedLine cfg) : ℤ) + Fintype.card Face =
            Fintype.card Edge + 1 := by
        exact_mod_cast C.euler
      omega

/-- In the dual-cellulation adapter, Melchior's line inequality is
equivalent to one numerical topological inequality, the face-edge handshake. -/
theorem lineMelchior_iff_dualFaceHandshake
    {Edge Face : Type*} [Fintype Edge] [Fintype Face] [DecidableEq Edge]
    (cfg : Configuration alpha)
    (C : ProjectiveArrangementCellulation (DeterminedLine cfg) Edge Face)
    (hmult : ∀ L : DeterminedLine cfg,
      C.multiplicity L =
        (labelDualArrangement cfg).multiplicity (determinedLineDualVertex cfg L)) :
    LineMelchior cfg ↔
      3 * (Fintype.card Face : ℤ) ≤ 2 * (Fintype.card Edge : ℤ) := by
  rw [lineMelchior_iff_slack_nonneg,
    lineMelchiorSlack_eq_dualFaceDefect cfg C hmult]
  omega

/-- The same adapter reduces the even-arrangement exclusion of slack one to
the two parity facts supplied by a future face-colouring construction. -/
theorem lineMelchiorSlack_ne_one_of_dualCellulation
    {Edge Face : Type*} [Fintype Edge] [Fintype Face] [DecidableEq Edge]
    (cfg : Configuration alpha)
    (C : ProjectiveArrangementCellulation (DeterminedLine cfg) Edge Face)
    (hmult : ∀ L : DeterminedLine cfg,
      C.multiplicity L =
        (labelDualArrangement cfg).multiplicity (determinedLineDualVertex cfg L))
    (hedge : Even (Fintype.card Edge)) (hface : Even (Fintype.card Face)) :
    lineMelchiorSlack cfg ≠ 1 := by
  rw [lineMelchiorSlack_eq_dualCellulationSlack cfg C hmult]
  exact C.melchiorSlack_ne_one_of_edge_even_of_face_even hedge hface

end Erdos506.Incidence
