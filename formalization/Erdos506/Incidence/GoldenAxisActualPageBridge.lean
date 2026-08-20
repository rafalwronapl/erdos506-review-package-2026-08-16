import Erdos506.Incidence.FiveConicTraceRigidity
import Erdos506.Incidence.ProjectiveRepresentativeThreeCollinearity

/-!
# Actual-page input for the golden-axis obstruction

The raw golden-axis endpoint asks for two determinant statements: the four
chord-pair centres are collinear, and three displayed lines are concurrent.
In an actual configuration both statements normally arrive as incidences
with nonzero line covectors.  This file records that smaller geometric
interface and converts it to `GoldenAxisCollinear` and the two concurrency
predicates.

No page or host is asserted to exist here.  Callers still have to extract the
common centre axis and the three indexed page axes from their block family.
-/

namespace Erdos506.Incidence

open Matrix

/-- Three marked homogeneous points incident with one nonzero actual page
covector. -/
structure GoldenAxisActualPage
    (u v r : Homogeneous3) where
  axis : Homogeneous3
  axis_ne_zero : axis ≠ 0
  first_on_axis : u ⋝ᵥ axis = 0
  second_on_axis : v ⋝ᵥ axis = 0
  common_on_axis : r ⋝ᵥ axis = 0

namespace GoldenAxisActualPage

/-- Three points carried by one actual page have vanishing homogeneous
determinant. -/
theorem det_eq_zero {u v r : Homogeneous3}
    (page : GoldenAxisActualPage u v r) :
    Matrix.det ![u, v, r] = 0 := by
  exact homogeneous_det_eq_zero_of_common_covector
    u v r page.axis page.axis_ne_zero page.first_on_axis
      page.second_on_axis page.common_on_axis

end GoldenAxisActualPage

/-- The three actual pages in the end-edge concurrency orbit. -/
structure GoldenAxisActualEndPages
    (g : Fin 5 → Homogeneous3) (q : Fin 4 → Homogeneous3)
    (r : Homogeneous3) where
  first : GoldenAxisActualPage (q 0) (g 1) r
  second : GoldenAxisActualPage (q 2) (g 3) r
  third : GoldenAxisActualPage (q 1) (g 2) r

/-- The three actual pages in the middle-edge concurrency orbit. -/
structure GoldenAxisActualMiddlePages
    (g : Fin 5 → Homogeneous3) (q : Fin 4 → Homogeneous3)
    (r : Homogeneous3) where
  first : GoldenAxisActualPage (q 0) (g 1) r
  second : GoldenAxisActualPage (q 2) (g 3) r
  third : GoldenAxisActualPage (g 2) (g 4) r

/-- Minimal actual page/host-chord output shared by the C39 H28 and C40
K2.4 routes.  The host-chord calculation supplies one nonzero covector
through all four canonical centres.  Three indexed actual pages share the
nonzero point `commonPoint` and have one of the two finite matching types. -/
structure GoldenAxisActualPageHostData
    (g : Fin 5 → Homogeneous3) (q : Fin 4 → Homogeneous3) where
  centerAxis : Homogeneous3
  centerAxis_ne_zero : centerAxis ≠ 0
  center_on_axis : ∀ i, q i ⋝ᵥ centerAxis = 0
  commonPoint : Homogeneous3
  commonPoint_ne_zero : commonPoint ≠ 0
  pages :
    GoldenAxisActualEndPages g q commonPoint ∨
      GoldenAxisActualMiddlePages g q commonPoint

namespace GoldenAxisActualPageHostData

/-- A single nonzero host/page axis through the four chord-pair centres is
exactly the raw golden-axis collinearity input. -/
theorem axisCollinear
    {g : Fin 5 → Homogeneous3} {q : Fin 4 → Homogeneous3}
    (data : GoldenAxisActualPageHostData g q) :
    GoldenAxisCollinear q := by
  intro i j k
  exact homogeneous_det_eq_zero_of_common_covector
    (q i) (q j) (q k) data.centerAxis data.centerAxis_ne_zero
      (data.center_on_axis i) (data.center_on_axis j)
        (data.center_on_axis k)

/-- The common point of the three indexed actual pages gives precisely one
of the two concurrency predicates used by the golden-axis certificate. -/
theorem concurrency
    {g : Fin 5 → Homogeneous3} {q : Fin 4 → Homogeneous3}
    (data : GoldenAxisActualPageHostData g q) :
    GoldenAxisEndConcurrent g q ∨ GoldenAxisMiddleConcurrent g q := by
  rcases data.pages with pages | pages
  · exact Or.inl ⟨data.commonPoint, data.commonPoint_ne_zero,
      pages.first.det_eq_zero, pages.second.det_eq_zero,
        pages.third.det_eq_zero⟩
  · exact Or.inr ⟨data.commonPoint, data.commonPoint_ne_zero,
      pages.first.det_eq_zero, pages.second.det_eq_zero,
        pages.third.det_eq_zero⟩

/-- The reusable K2.4 endpoint: once the ordinary five-conic data and the
actual page/host-chord output have been constructed, the existing bounded
golden-axis certificate closes the configuration. -/
theorem absurd
    {g : Fin 5 → Homogeneous3} {q : Fin 4 → Homogeneous3}
    (hgeneral : HomogeneousFiveGeneralPosition g)
    (hq : ∀ i, q i ≠ 0)
    (hcenters : GoldenAxisCenterIncidence g q)
    (data : GoldenAxisActualPageHostData g q) : False := by
  exact fiveConic_goldenAxis_tangentSeparation_absurd g q
    hgeneral hq hcenters data.axisCollinear data.concurrency

end GoldenAxisActualPageHostData

end Erdos506.Incidence
