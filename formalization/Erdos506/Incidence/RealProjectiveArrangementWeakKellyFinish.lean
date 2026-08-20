import Erdos506.Incidence.RealProjectiveArrangementKellyMoserDegreeOneAttachmentFinish
import Erdos506.Incidence.RealPlaneKellyMoserDualCensus
import Erdos506.V1.PivotGeometry

/-!
# A callback-free weak Kelly count

The completed degree-zero clause gives three attachments and the finite-size
degree-one construction gives one attachment.  Those two facts already imply
the universal integral estimate `3 q <= 8 t_2`.  At fourteen arrangement
lines its rounding is as strong as the usual Kelly--Moser estimate: there are
at least six ordinary vertices.  The final theorem transports this fact to
fifteen-label pivot inversions.
-/

namespace Erdos506.Incidence

open Erdos506.V1
open Erdos506.V4
open Erdos506.V3
open scoped BigOperators

universe u v

/-- Pure finite count using the local clauses `0 -> 3` and `1 -> 1`.
Lines of ordinary degree one or two consume at least one of the total
ordinary incidences, which supplies the last two units in the coefficient
eight. -/
theorem kellyMoser_eight_count_of_weak_local_associations
    {Vertex : Type u} {Line : Type v} [Fintype Vertex] [Fintype Line]
    (ordinary attached : Vertex -> Line -> Prop)
    (hordinary : forall x : Vertex,
      finiteRelationLeftDegree ordinary x = 2)
    (hattached : forall x : Vertex,
      finiteRelationLeftDegree attached x <= 4)
    (hzero : forall l : Line,
      finiteRelationRightDegree ordinary l = 0 ->
        3 <= finiteRelationRightDegree attached l)
    (hone : forall l : Line,
      finiteRelationRightDegree ordinary l = 1 ->
        1 <= finiteRelationRightDegree attached l) :
    3 * Fintype.card Line <= 8 * Fintype.card Vertex := by
  classical
  let small : Finset Line := Finset.univ.filter fun l =>
    finiteRelationRightDegree ordinary l = 1 ∨
      finiteRelationRightDegree ordinary l = 2
  have hordinarySum :
      (∑ l : Line, finiteRelationRightDegree ordinary l) =
        2 * Fintype.card Vertex := by
    rw [sum_finiteRelationRightDegree_eq_sum_finiteRelationLeftDegree]
    calc
      (∑ x : Vertex, finiteRelationLeftDegree ordinary x) =
          ∑ _x : Vertex, 2 := by
        apply Finset.sum_congr rfl
        intro x _hx
        exact hordinary x
      _ = 2 * Fintype.card Vertex := by simp [mul_comm]
  have hattachedSum :
      (∑ l : Line, finiteRelationRightDegree attached l) <=
        4 * Fintype.card Vertex := by
    rw [sum_finiteRelationRightDegree_eq_sum_finiteRelationLeftDegree]
    calc
      (∑ x : Vertex, finiteRelationLeftDegree attached x) <=
          ∑ _x : Vertex, 4 := by
        exact Finset.sum_le_sum fun x _hx => hattached x
      _ = 4 * Fintype.card Vertex := by simp [mul_comm]
  have hsmallCard : small.card <= 2 * Fintype.card Vertex := by
    calc
      small.card = ∑ _l ∈ small, 1 := by simp
      _ <= ∑ l ∈ small, finiteRelationRightDegree ordinary l := by
        apply Finset.sum_le_sum
        intro l hl
        have hl' := (Finset.mem_filter.mp hl).2
        omega
      _ <= ∑ l : Line, finiteRelationRightDegree ordinary l := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · exact Finset.filter_subset _ _
        · intro l _hl _hnot
          exact Nat.zero_le _
      _ = 2 * Fintype.card Vertex := hordinarySum
  have hline (l : Line) :
      3 <= finiteRelationRightDegree ordinary l +
        finiteRelationRightDegree attached l +
          (if finiteRelationRightDegree ordinary l = 1 ∨
              finiteRelationRightDegree ordinary l = 2 then 1 else 0) := by
    by_cases h0 : finiteRelationRightDegree ordinary l = 0
    · have ha := hzero l h0
      simp [h0]
      omega
    by_cases h1 : finiteRelationRightDegree ordinary l = 1
    · have ha := hone l h1
      simp [h1]
      omega
    by_cases h2 : finiteRelationRightDegree ordinary l = 2
    · simp [h1, h2]
    · simp [h1, h2]
      omega
  have htotal :
      3 * Fintype.card Line <=
        (∑ l : Line, finiteRelationRightDegree ordinary l) +
          (∑ l : Line, finiteRelationRightDegree attached l) +
            small.card := by
    calc
      3 * Fintype.card Line = ∑ _l : Line, 3 := by simp [mul_comm]
      _ <= ∑ l : Line,
          (finiteRelationRightDegree ordinary l +
            finiteRelationRightDegree attached l +
              (if finiteRelationRightDegree ordinary l = 1 ∨
                  finiteRelationRightDegree ordinary l = 2 then 1 else 0)) := by
        exact Finset.sum_le_sum fun l _hl => hline l
      _ = (∑ l : Line, finiteRelationRightDegree ordinary l) +
          (∑ l : Line, finiteRelationRightDegree attached l) +
            small.card := by
        simp only [Finset.sum_add_distrib]
        simp [small]
  omega

namespace FiniteProjectiveLineArrangement

variable {Line : Type u} [Fintype Line] [DecidableEq Line]

/-- The weak Kelly count on the branch where every arrangement line has at
least three marked vertices. -/
theorem three_mul_card_le_eight_mul_card_ordinaryVertex_of_highLines
    (A : FiniteProjectiveLineArrangement Line) (hA : A.NonPencil)
    (hhigh : forall l : Line, 3 <= (A.lineVertexSet l).card) :
    3 * Fintype.card Line <= 8 * Fintype.card A.OrdinaryVertex := by
  apply kellyMoser_eight_count_of_weak_local_associations
    (fun q : A.OrdinaryVertex => A.Incident q.1)
    A.OrdinaryVertexAttachedToLine
  · exact A.ordinaryVertexLineDegree_eq_two
  · exact A.ordinaryVertexAttachmentDegree_le_four hA
  · intro l hzero
    exact A.three_le_lineOrdinaryAttachmentDegree_of_degree_zero
      hA l (hhigh l) hzero
  · intro l hone
    exact A.one_le_lineOrdinaryAttachmentDegree_of_degree_one_highLine
      hA l (hhigh l) hone

/-- Unconditional weak Kelly bound for every non-pencil real projective
arrangement.  A line with at most two marked vertices is handled by the
strong low-line theorem; otherwise the preceding attachment count applies. -/
theorem three_mul_card_le_eight_mul_card_ordinaryVertex
    (A : FiniteProjectiveLineArrangement Line) (hA : A.NonPencil) :
    3 * Fintype.card Line <= 8 * Fintype.card A.OrdinaryVertex := by
  have hthreeCard := A.three_le_card_of_nonPencil hA
  by_cases hfour : 4 <= Fintype.card Line
  · by_cases hhigh : forall l : Line, 3 <= (A.lineVertexSet l).card
    · exact A.three_mul_card_le_eight_mul_card_ordinaryVertex_of_highLines
        hA hhigh
    · push_neg at hhigh
      obtain ⟨l, hlow⟩ := hhigh
      have hstrong :=
        A.three_mul_card_le_seven_mul_card_ordinaryVertex_of_lineVertexSet_card_le_two
          hA hfour l (by omega)
      omega
  · have hcard : Fintype.card Line = 3 := by omega
    have hstrong :=
      A.three_mul_card_le_seven_mul_card_ordinaryVertex_of_card_eq_three
        hA hcard
    omega

end FiniteProjectiveLineArrangement

/-- Fourteen noncollinear points determine at least six ordinary lines.
This is the integral rounding of `3*14 <= 8*t_2`. -/
theorem six_le_lineCount_two_of_card_fourteen_weakKelly
    {alpha : Type u} [Fintype alpha] [DecidableEq alpha]
    (cfg : Configuration alpha) (hnon : Noncollinear cfg)
    (hcard : Fintype.card alpha = 14) :
    6 <= (blockSystem cfg).lineCount 2 := by
  have hweak :=
    (labelDualArrangement cfg).three_mul_card_le_eight_mul_card_ordinaryVertex
      (labelDualArrangement_nonPencil_of_noncollinear cfg hnon)
  rw [← lineCount_two_eq_card_labelDualOrdinaryVertex cfg] at hweak
  rw [hcard] at hweak
  omega

/-- Pivot form of the universal weak Kelly count. -/
theorem three_mul_pred_le_eight_mul_blockDegree_three_weakKelly
    {alpha : Type u} [Fintype alpha] [DecidableEq alpha]
    (cfg : Configuration alpha) (hadm : Erdos506.V1.Admissible cfg)
    (hcard : 4 <= Fintype.card alpha) (p : alpha) :
    3 * (Fintype.card alpha - 1) <= 8 * blockDegree cfg 3 p := by
  have hnon : Noncollinear (pivotInversion cfg p) :=
    pivotInversion_noncollinear cfg hadm (by omega) p
  have hweak :=
    (labelDualArrangement (pivotInversion cfg p)).three_mul_card_le_eight_mul_card_ordinaryVertex
        (labelDualArrangement_nonPencil_of_noncollinear
          (pivotInversion cfg p) hnon)
  rw [← lineCount_two_eq_card_labelDualOrdinaryVertex,
    card_awayFrom,
    ← blockDegree_three_eq_lineCount_two_pivotInversion] at hweak
  exact hweak

/-- Every pivot of an admissible fifteen-label configuration lies on at
least six three-blocks. -/
theorem six_le_blockDegree_three_of_card_fifteen_weakKelly
    {alpha : Type u} [Fintype alpha] [DecidableEq alpha]
    (cfg : Configuration alpha) (hadm : Erdos506.V1.Admissible cfg)
    (hcard : Fintype.card alpha = 15) (p : alpha) :
    6 <= blockDegree cfg 3 p := by
  have hweak := three_mul_pred_le_eight_mul_blockDegree_three_weakKelly
    cfg hadm (by omega) p
  rw [hcard] at hweak
  norm_num at hweak
  omega

end Erdos506.Incidence
