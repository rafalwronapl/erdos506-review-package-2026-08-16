import Erdos506.Incidence.RealProjectiveArrangementKellyMoserFinish

/-!
# The unique-ordinary-return router for Kelly--Moser

On a line containing exactly one ordinary vertex, every other marked return
has multiplicity at least three.  Consequently it has a support besides the
base and the line which produced the return.  This is the finite incidence
part of the `(1,2+)` Three-Clause branch; the outer-sector argument only has
to show that its median return differs from the unique ordinary endpoint.
-/

namespace Erdos506.Incidence

open Erdos506.V4

namespace FiniteProjectiveLineArrangement

variable {Line : Type*} [Fintype Line] [DecidableEq Line]

/-- A transverse return different from the unique ordinary point of a
degree-one base has multiplicity at least three. -/
theorem three_le_multiplicity_base_return_of_lineDegree_eq_one_of_ne
    (A : FiniteProjectiveLineArrangement Line)
    (l c : Line) (hone : A.lineOrdinaryVertexDegree l = 1)
    (hlc : l ≠ c) (p : A.OrdinaryVertex) (hpl : A.Incident p.1 l)
    (hne : A.intersection l c ≠ p.1) :
    3 ≤ A.multiplicity (A.intersection l c) := by
  classical
  obtain ⟨p₀, hp₀, hp₀Unique⟩ :=
    A.existsUnique_ordinaryVertex_incident_of_lineDegree_eq_one l hone
  have hpEq : p = p₀ := hp₀Unique p hpl
  have htwo : 2 ≤ A.multiplicity (A.intersection l c) :=
    A.two_le_multiplicity_intersection hlc
  by_contra hthree
  have heqTwo : A.multiplicity (A.intersection l c) = 2 := by omega
  let r : A.OrdinaryVertex :=
    ⟨A.intersection l c, Finset.mem_filter.mpr
      ⟨A.intersection_mem_vertexSet hlc, heqTwo⟩⟩
  have hrl : A.Incident r.1 l := by
    exact A.intersection_incident_left hlc
  have hrEq : r = p₀ := hp₀Unique r hrl
  apply hne
  exact congrArg Subtype.val (hrEq.trans hpEq.symm)

/-- Therefore a nonordinary return on a degree-one base has a third indexed
support besides the base and the returning line. -/
theorem exists_extra_line_at_base_return_of_lineDegree_eq_one_of_ne
    (A : FiniteProjectiveLineArrangement Line)
    (l c : Line) (hone : A.lineOrdinaryVertexDegree l = 1)
    (hlc : l ≠ c) (p : A.OrdinaryVertex) (hpl : A.Incident p.1 l)
    (hne : A.intersection l c ≠ p.1) :
    ∃ m : Line, m ≠ l ∧ m ≠ c ∧
      A.Incident (A.intersection l c) m := by
  have hthree :=
    A.three_le_multiplicity_base_return_of_lineDegree_eq_one_of_ne
      l c hone hlc p hpl hne
  exact A.exists_third_incident_line_of_three_le_multiplicity
    (A.intersection l c) l c hlc
      (A.intersection_incident_left hlc)
      (A.intersection_incident_right hlc) hthree

end FiniteProjectiveLineArrangement

end Erdos506.Incidence
