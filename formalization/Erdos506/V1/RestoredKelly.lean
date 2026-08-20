import Erdos506.V1.Deletion
import Erdos506.V1.RestoredPivot

/-!
# Admissibility of the restored pivot configuration

The restored inversion has the original number of labels.  Under the
five-block cap at eleven points it is again admissible: if all restored
points lay on a proper circle, that circle would pass through the inversion
centre, and inversion would put the ten remaining original points on one
line.  This file packages that elementary bridge.  A direct ordinary-line
form of Kelly--Moser is deliberately not claimed here: the existing public
Kelly interface is a pivot form and requires a separate transport theorem.
-/

namespace Erdos506.V1

open Erdos506.Block
open Erdos506.Finite
open Erdos506.Incidence
open Erdos506.V3
open Erdos506.V4
open AffineSubspace

universe u

/-- A five-block cap at eleven points prevents the restored pivot
configuration from being concyclic. -/
theorem restoredPivotConfiguration_notConcyclic_of_blockSizeCap_five
    {alpha : Type u} [Fintype alpha] [DecidableEq alpha]
    (cfg : Configuration alpha) (hcard : Fintype.card alpha = 11)
    (hcap : BlockSizeCap (blockSystem cfg) 5) (p : alpha) :
    NotConcyclic (restoredPivotConfiguration cfg p) := by
  classical
  intro c
  have hle :
      (circleTrace (restoredPivotConfiguration cfg p) c).card <=
        Fintype.card (Option (AwayFrom p)) := by
    simpa using Finset.card_le_univ
      (circleTrace (restoredPivotConfiguration cfg p) c)
  apply lt_of_le_of_ne hle
  intro heq
  have hall :
      circleTrace (restoredPivotConfiguration cfg p) c = Finset.univ :=
    Finset.eq_univ_of_card _ heq
  have hnone : none ∈
      circleTrace (restoredPivotConfiguration cfg p) c := by
    rw [hall]
    exact Finset.mem_univ none
  have hcenter : cfg p ∈ (c.1 : Set Point2) := by
    simpa using (mem_circleTrace.mp hnone)
  let P : AffineSubspace ℝ Point2 :=
    perpBisector (cfg p)
      (EuclideanGeometry.inversion (cfg p) 1 c.1.center)
  have hPfin : Module.finrank ℝ P.direction = 1 := by
    simpa [P, circlePivotLine] using
      (circlePivotLine_direction_finrank
        (restoredPivotConfiguration cfg p) none c hnone)
  let U : Finset alpha :=
    liftAwayFinset (Finset.univ : Finset (AwayFrom p))
  have hUcard : U.card = 10 := by
    rw [show U.card = (Finset.univ : Finset (AwayFrom p)).card by
      exact card_liftAwayFinset _]
    simp [hcard]
  have hUP : ∀ x ∈ U, cfg x ∈ P := by
    intro x hx
    obtain ⟨q, _hq, rfl⟩ := mem_liftAwayFinset.mp hx
    have hsome : some q ∈
        circleTrace (restoredPivotConfiguration cfg p) c := by
      rw [hall]
      exact Finset.mem_univ (some q)
    have hinCircle : pivotInversion cfg p q ∈ (c.1 : Set Point2) := by
      simpa using (mem_circleTrace.mp hsome)
    have hinNe : pivotInversion cfg p q ≠ cfg p := by
      intro h
      have hqp : cfg q.1 = cfg p :=
        (EuclideanGeometry.inversion_eq_center one_ne_zero).mp h
      exact q.2 (cfg.injective hqp)
    have hinP :=
      (mem_circle_through_center_iff_inversion_mem_perpBisector
        (cfg p) (pivotInversion cfg p q) c hinNe hcenter).mp hinCircle
    change cfg q.1 ∈ P
    simpa [P, pivotInversion] using hinP
  have hUtwo : 2 <= U.card := by omega
  obtain ⟨Aset, hAU, hAcard⟩ := Finset.exists_subset_card_eq hUtwo
  let A : KSubset alpha 2 := ⟨Aset, hAcard⟩
  let L : DeterminedLine cfg :=
    ⟨lineOfPair cfg A, lineOfPair_mem_determinedLines cfg A⟩
  have hpair : lineOfPair cfg A = P := by
    apply lineOfPair_eq_of_mem_of_direction_finrank_one cfg A P
    · intro x hx
      exact hUP x (hAU hx)
    · exact hPfin
  have hUsub : U ⊆ lineSupport cfg L := by
    intro x hx
    apply mem_lineSupport.mpr
    change cfg x ∈ lineOfPair cfg A
    rw [hpair]
    exact hUP x hx
  have hten : 10 <= (lineSupport cfg L).card := by
    rw [← hUcard]
    exact Finset.card_le_card hUsub
  have hfive : (lineSupport cfg L).card <= 5 := by
    have hthree : 3 <=
        ((blockSystem cfg).support (Sum.inl L)).card := by
      simpa [blockSystem, geometricBlockSystem, geometricBlockSupport] using
        (show 3 <= (lineSupport cfg L).card by omega)
    simpa [blockSystem, geometricBlockSystem, geometricBlockSupport] using
      hcap (Sum.inl L) hthree
  omega

/-- The restored pivot configuration is an admissible eleven-point
configuration under the five-block cap. -/
theorem restoredPivotConfiguration_admissible_of_blockSizeCap_five
    {alpha : Type u} [Fintype alpha] [DecidableEq alpha]
    (cfg : Configuration alpha) (hadm : Admissible cfg)
    (hcard : Fintype.card alpha = 11)
    (hcap : BlockSizeCap (blockSystem cfg) 5) (p : alpha) :
    Admissible (restoredPivotConfiguration cfg p) := by
  exact ⟨restoredPivotConfiguration_noncollinear cfg hadm (by omega) p,
    restoredPivotConfiguration_notConcyclic_of_blockSizeCap_five
      cfg hcard hcap p⟩

end Erdos506.V1
