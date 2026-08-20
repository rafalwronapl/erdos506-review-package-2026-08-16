import Erdos506.Incidence.RealPlaneMelchiorDerivation
import Erdos506.Incidence.OrdinaryPrinciples
import Erdos506.Incidence.RealProjectiveArrangementKellyMoserFinish
import Erdos506.V1.InversionAugmentation

/-!
# The ordinary-line / dual ordinary-vertex dictionary

This small leaf transports the exact multiplicity dictionary of the labelled
dual arrangement to the size-two determined-line census.  It is the final
finite adapter needed after proving the Kelly--Moser inequality for a genuine
finite projective line arrangement.
-/

namespace Erdos506.Incidence

open Erdos506.V1
open Erdos506.V3
open Erdos506.V4

universe u

variable {alpha : Type u} [Fintype alpha] [DecidableEq alpha]

/-- A globally noncollinear finite configuration has at least three labels. -/
theorem three_le_card_of_noncollinear_configuration
    (cfg : Configuration alpha) (hnon : Noncollinear cfg) :
    3 ≤ Fintype.card alpha := by
  classical
  by_contra hthree
  have hcard : Fintype.card alpha ≤ 2 := by omega
  let S : Finset Point2 := Finset.univ.image cfg
  have hScard : S.card = Fintype.card alpha := by
    simpa only [S, Finset.card_univ] using
      Finset.card_image_of_injective (Finset.univ : Finset alpha) cfg.injective
  have hSle : S.card ≤ 2 := by omega
  have hpoint : (↑S : Set Point2) = pointSet cfg := by
    ext x
    simp only [S, Finset.coe_image, Finset.coe_univ, Set.image_univ]
    rfl
  apply hnon
  rw [← hpoint]
  have hcases : S.card = 0 ∨ S.card = 1 ∨ S.card = 2 := by omega
  rcases hcases with hzero | hone | htwo
  · have hS : S = ∅ := Finset.card_eq_zero.mp hzero
    rw [hS]
    simpa using (collinear_empty ℝ Point2)
  · obtain ⟨x, hS⟩ := Finset.card_eq_one.mp hone
    rw [hS]
    simpa using (collinear_singleton (k := ℝ) x)
  · obtain ⟨x, y, _hxy, hS⟩ := Finset.card_eq_two.mp htwo
    rw [hS]
    simpa using (collinear_pair ℝ x y)

/-- A size-two determined affine line gives the corresponding actual
multiplicity-two vertex of the labelled dual arrangement. -/
noncomputable def determinedLineOfSizeTwoToLabelDualOrdinaryVertex
    (cfg : Configuration alpha) :
    DeterminedLineOfSize cfg 2 -> (labelDualArrangement cfg).OrdinaryVertex :=
  fun L => by
    classical
    refine ⟨determinedLineDualVertex cfg L.1, Finset.mem_filter.mpr ⟨?_, ?_⟩⟩
    · exact determinedLineDualVertex_mem_labelDualVertexSet cfg L.1
    · simpa only [labelDual_multiplicity_determinedLine] using L.2

/-- The size-two dual dictionary is injective. -/
theorem determinedLineOfSizeTwoToLabelDualOrdinaryVertex_injective
    (cfg : Configuration alpha) :
    Function.Injective
      (determinedLineOfSizeTwoToLabelDualOrdinaryVertex cfg) := by
  intro L M hLM
  apply Subtype.ext
  apply determinedProjectiveLine_injective cfg
  exact congrArg Subtype.val hLM

/-- Every actual multiplicity-two vertex of the labelled dual arrangement is
the dual of one size-two determined affine line. -/
theorem determinedLineOfSizeTwoToLabelDualOrdinaryVertex_surjective
    (cfg : Configuration alpha) :
    Function.Surjective
      (determinedLineOfSizeTwoToLabelDualOrdinaryVertex cfg) := by
  classical
  intro q
  have hq := Finset.mem_filter.mp q.2
  obtain ⟨L, hL⟩ :=
    determinedLineToLabelDualVertexSet_surjective cfg ⟨q.1, hq.1⟩
  have hdual : determinedLineDualVertex cfg L = q.1 :=
    congrArg Subtype.val hL
  have hsize : (lineSupport cfg L).card = 2 := by
    calc
      (lineSupport cfg L).card =
          (labelDualArrangement cfg).multiplicity
            (determinedLineDualVertex cfg L) :=
        (labelDual_multiplicity_determinedLine cfg L).symm
      _ = (labelDualArrangement cfg).multiplicity q.1 :=
        congrArg (labelDualArrangement cfg).multiplicity hdual
      _ = 2 := hq.2
  refine ⟨⟨L, hsize⟩, ?_⟩
  apply Subtype.ext
  exact hdual

/-- Exact equivalence between ordinary affine lines and actual ordinary
vertices of the labelled dual arrangement. -/
noncomputable def determinedLineOfSizeTwoEquivLabelDualOrdinaryVertex
    (cfg : Configuration alpha) :
    DeterminedLineOfSize cfg 2 ≃ (labelDualArrangement cfg).OrdinaryVertex :=
  Equiv.ofBijective
    (determinedLineOfSizeTwoToLabelDualOrdinaryVertex cfg)
    ⟨determinedLineOfSizeTwoToLabelDualOrdinaryVertex_injective cfg,
      determinedLineOfSizeTwoToLabelDualOrdinaryVertex_surjective cfg⟩

/-- Cardinality form of the ordinary-line / ordinary-vertex dictionary. -/
theorem lineCount_two_eq_card_labelDualOrdinaryVertex
    (cfg : Configuration alpha) :
    (blockSystem cfg).lineCount 2 =
      Fintype.card (labelDualArrangement cfg).OrdinaryVertex := by
  rw [lineCount_eq_card_determinedLineOfSize]
  exact Fintype.card_congr
    (determinedLineOfSizeTwoEquivLabelDualOrdinaryVertex cfg)

/-- A projective-arrangement Kelly--Moser bound on `9..12` lines becomes
the direct ordinary-line bound in the same finite window. -/
theorem ordinary_line_bound_of_projective_arrangement
    (H : ∀ {Line : Type u} [Fintype Line] [DecidableEq Line]
      (A : FiniteProjectiveLineArrangement Line),
      9 ≤ Fintype.card Line → Fintype.card Line ≤ 12 → A.NonPencil →
        3 * Fintype.card Line ≤ 7 * Fintype.card A.OrdinaryVertex)
    (cfg : Configuration alpha) (hnon : Noncollinear cfg)
    (hmin : 9 ≤ Fintype.card alpha) (hmax : Fintype.card alpha ≤ 12) :
    3 * Fintype.card alpha ≤ 7 * (blockSystem cfg).lineCount 2 := by
  have h := H (labelDualArrangement cfg) hmin hmax
    (labelDualArrangement_nonPencil_of_noncollinear cfg hnon)
  rwa [lineCount_two_eq_card_labelDualOrdinaryVertex] 

/-- Assembly of the guarded V1 pivot form from the corresponding guarded
projective-arrangement theorem. -/
noncomputable def realPlaneKellyMoserPrincipleOfProjectiveArrangement
    (H : ∀ {Line : Type u} [Fintype Line] [DecidableEq Line]
      (A : FiniteProjectiveLineArrangement Line),
      9 ≤ Fintype.card Line → Fintype.card Line ≤ 12 → A.NonPencil →
        3 * Fintype.card Line ≤ 7 * Fintype.card A.OrdinaryVertex) :
    RealPlaneKellyMoserPrinciple.{u} where
  pivot_three_block_bound := by
    intro alpha _ _ cfg hadm hmin hmax p
    have hcard : 3 ≤ Fintype.card alpha :=
      three_le_card_of_noncollinear_configuration cfg hadm.1
    have hnon : Noncollinear (pivotInversion cfg p) :=
      pivotInversion_noncollinear cfg hadm hcard p
    have hdirect := ordinary_line_bound_of_projective_arrangement
      H (pivotInversion cfg p) hnon
        (by rw [card_awayFrom]; omega)
        (by rw [card_awayFrom]; omega)
    rw [card_awayFrom,
      ← blockDegree_three_eq_lineCount_two_pivotInversion] at hdirect
    exact hdirect

end Erdos506.Incidence
