import Erdos506.Incidence.RealProjectiveArrangementKellyMoserDegreeOneExtra
import Erdos506.Incidence.RealProjectiveArrangementKellyMoserOuterReturnClosure

/-!
# The median return avoids the ordinary endpoint

The intrinsic affine parameter of a base point in a closed triangle sector
is nonnegative.  Its left endpoint has parameter zero.  Thus the strictly
middle return selected by the Three-Clause sorting step cannot be that
endpoint.  Combined with the degree-one return router, this supplies the
only `hextra` instance used by the local minimizer proof.
-/

namespace Erdos506.Incidence

open Erdos506.V4

namespace FiniteProjectiveLineArrangement

variable {Line : Type*} [Fintype Line] [DecidableEq Line]

/-- Every base point belonging to the selected closed sector has
nonnegative intrinsic affine parameter. -/
theorem sectorExitBaseParameter_nonneg_of_mem
    (A : FiniteProjectiveLineArrangement Line) (sigma : Line → Bool)
    (l a b : Line)
    (htriangle : ¬ ∃ r : RealProjectivePoint,
      A.Incident r l ∧ A.Incident r a ∧ A.Incident r b)
    (x : RealProjectivePoint)
    (hx : A.projectivePointMemTriangleSector sigma l a b x) :
    0 ≤ A.sectorExitBaseParameter sigma l a b x := by
  obtain ⟨_hX0, _hXgauge, _hmkX, hXcone⟩ :=
    A.sectorExitNormalizedPoint_facts sigma l a b htriangle x hx
  exact hXcone a (by simp)

/-- The left endpoint of the sector's base interval has affine parameter
zero. -/
theorem sectorExitBaseParameter_leftEndpoint_eq_zero
    (A : FiniteProjectiveLineArrangement Line) (sigma : Line → Bool)
    (l a b : Line) (hla : l ≠ a)
    (htriangle : ¬ ∃ r : RealProjectivePoint,
      A.Incident r l ∧ A.Incident r a ∧ A.Incident r b) :
    A.sectorExitBaseParameter sigma l a b (A.intersection l a) = 0 := by
  have hsector :=
    A.projectivePointMemTriangleSector_of_incident_base_left
      sigma l a b (A.intersection l a)
        (A.intersection_incident_left hla)
        (A.intersection_incident_right hla)
  have hzero :=
    A.arrangementOrientedEvaluation_sectorExitNormalizedPoint_eq_zero
      sigma l a b a htriangle (A.intersection l a) hsector
        (A.intersection_incident_right hla)
  simpa only [sectorExitBaseParameter] using hzero

/-- A strictly middle base return in the sector differs from its left
endpoint. -/
theorem sectorExit_middleReturn_ne_leftEndpoint
    (A : FiniteProjectiveLineArrangement Line) (sigma : Line → Bool)
    (l a b left middle : Line) (hla : l ≠ a)
    (htriangle : ¬ ∃ r : RealProjectivePoint,
      A.Incident r l ∧ A.Incident r a ∧ A.Incident r b)
    (hleftSector : A.projectivePointMemTriangleSector sigma l a b
      (A.intersection l left))
    (hlt : A.sectorExitBaseParameter sigma l a b
        (A.intersection l left) <
      A.sectorExitBaseParameter sigma l a b
        (A.intersection l middle)) :
    A.intersection l middle ≠ A.intersection l a := by
  intro heq
  have hnonneg := A.sectorExitBaseParameter_nonneg_of_mem
    sigma l a b htriangle (A.intersection l left) hleftSector
  have hendpoint := A.sectorExitBaseParameter_leftEndpoint_eq_zero
    sigma l a b hla htriangle
  rw [heq, hendpoint] at hlt
  linarith

/-- Combined degree-one callback for the single median return used by the
local Three-Clause contradiction. -/
theorem exists_extra_line_at_sector_middle_of_lineDegree_eq_one
    (A : FiniteProjectiveLineArrangement Line) (sigma : Line → Bool)
    (l a b left middle : Line)
    (hone : A.lineOrdinaryVertexDegree l = 1)
    (hla : l ≠ a) (hlmiddle : l ≠ middle)
    (p : A.OrdinaryVertex) (hpl : A.Incident p.1 l)
    (hpEndpoint : p.1 = A.intersection l a)
    (htriangle : ¬ ∃ r : RealProjectivePoint,
      A.Incident r l ∧ A.Incident r a ∧ A.Incident r b)
    (hleftSector : A.projectivePointMemTriangleSector sigma l a b
      (A.intersection l left))
    (hlt : A.sectorExitBaseParameter sigma l a b
        (A.intersection l left) <
      A.sectorExitBaseParameter sigma l a b
        (A.intersection l middle)) :
    ∃ m : Line, m ≠ l ∧ m ≠ middle ∧
      A.Incident (A.intersection l middle) m := by
  have hneEndpoint := A.sectorExit_middleReturn_ne_leftEndpoint
    sigma l a b left middle hla htriangle hleftSector hlt
  have hneP : A.intersection l middle ≠ p.1 := by
    rw [hpEndpoint]
    exact hneEndpoint
  exact A.exists_extra_line_at_base_return_of_lineDegree_eq_one_of_ne
    l middle hone hlmiddle p hpl hneP

end FiniteProjectiveLineArrangement

end Erdos506.Incidence
