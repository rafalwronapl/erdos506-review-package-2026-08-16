import Erdos506.V1.TenFiveTwoPentagonGoldenLabelling
import Erdos506.V1.TenTwoPentagonCrossBlockPivot
import Erdos506.V1.TenFiveSixPower
import Erdos506.Incidence.GoldenAxisProjective

/-!
# The projective golden-axis core of the two-pentagon endpoint

The second five-block is inverted away from a pivot on the first one.  Its
five points supply the projective five-frame.  Saturated cross-blocks put the
four remaining first-block points on the four prescribed pairs of chords,
while inversion sends those four points to one affine line.
-/

namespace Erdos506.V1

open Erdos506.Finite
open Erdos506.Incidence
open Erdos506.V3
open Erdos506.V4

universe u

namespace TenTwoPentagonSaturationData

variable {α : Type u} [Fintype α] [DecidableEq α]
  {cfg : Configuration α}

/-- The second base block misses the selected first-block pivot. -/
theorem pivot_not_mem_secondSupport
    (d : TenTwoPentagonSaturationData cfg) :
    d.pivot.1 ∉ geometricBlockSupport cfg d.base.second := by
  intro h
  exact Finset.disjoint_left.mp d.base.supports_disjoint
    (by simpa only [d.base.exclusiveTrace_Γ_Ω] using d.pivot.2) h

/-- The inverted five points of the second pentagon. -/
noncomputable def goldenSecondPoint
    (d : TenTwoPentagonSaturationData cfg) (i : Fin 5) : Point2 :=
  pivotInversion cfg d.pivot.1
    ⟨(d.secondLabel i).1, by
      intro h
      apply d.pivot_not_mem_secondSupport
      rw [← h]
      simpa only [d.base.exclusiveTrace_Ω_Γ] using (d.secondLabel i).2⟩

/-- The four inverted first-pentagon points away from the pivot. -/
noncomputable def goldenFirstPoint
    (d : TenTwoPentagonSaturationData cfg) (i : Fin 4) : Point2 :=
  pivotInversion cfg d.pivot.1
    ⟨(d.qLabel i).1.1, by
      intro h
      exact (d.qLabel i).2 (Subtype.ext h)⟩

/-- Homogeneous representatives for the normalized second pentagon. -/
noncomputable def goldenSecondRaw
    (d : TenTwoPentagonSaturationData cfg) (i : Fin 5) : Homogeneous3 :=
  homogeneousLift (d.goldenSecondPoint i)

/-- Homogeneous representatives for the four collinear first-pentagon
points after inversion. -/
noncomputable def goldenFirstRaw
    (d : TenTwoPentagonSaturationData cfg) (i : Fin 4) : Homogeneous3 :=
  homogeneousLift (d.goldenFirstPoint i)

theorem secondLabel_mem_secondSupport
    (d : TenTwoPentagonSaturationData cfg) (i : Fin 5) :
    (d.secondLabel i).1 ∈ geometricBlockSupport cfg d.base.second := by
  simpa only [d.base.exclusiveTrace_Ω_Γ] using (d.secondLabel i).2

theorem qLabel_mem_firstSupport
    (d : TenTwoPentagonSaturationData cfg) (i : Fin 4) :
    (d.qLabel i).1.1 ∈ geometricBlockSupport cfg d.base.first := by
  simpa only [d.base.exclusiveTrace_Γ_Ω] using (d.qLabel i).1.2

/-- The underlying selected label of a non-pivot first-trace vertex is not
the underlying selected pivot. -/
theorem qLabel_val_ne_pivot
    (d : TenTwoPentagonSaturationData cfg) (i : Fin 4) :
    (d.qLabel i).1.1 ≠ d.pivot.1 := by
  intro h
  exact (d.qLabel i).2 (Subtype.ext h)

private theorem goldenSecondPoint_mem_circle
    (d : TenTwoPentagonSaturationData cfg) (i : Fin 5) :
    d.goldenSecondPoint i ∈
      ((invertedAwayGeometricBlockCircle cfg d.pivot.1 d.base.second
        d.pivot_not_mem_secondSupport).1 : Set Point2) := by
  exact inversion_mem_invertedAwayGeometricBlockCircle cfg d.pivot.1
    d.base.second d.pivot_not_mem_secondSupport
      (d.secondLabel i).1 (d.secondLabel_mem_secondSupport i)

private theorem goldenSecondPoint_injective
    (d : TenTwoPentagonSaturationData cfg) :
    Function.Injective d.goldenSecondPoint := by
  intro i j hij
  have haway :
      (⟨(d.secondLabel i).1, by
        intro h
        exact d.pivot_not_mem_secondSupport
          (h ▸ d.secondLabel_mem_secondSupport i)⟩ : AwayFrom d.pivot.1) =
      ⟨(d.secondLabel j).1, by
        intro h
        exact d.pivot_not_mem_secondSupport
          (h ▸ d.secondLabel_mem_secondSupport j)⟩ :=
    (pivotInversion cfg d.pivot.1).injective hij
  apply d.secondLabel.injective
  apply Subtype.ext
  exact congrArg (fun x : AwayFrom d.pivot.1 => x.1) haway

/-- The five inverted second-pentagon points are in general position. -/
theorem goldenSecondRaw_generalPosition
    (d : TenTwoPentagonSaturationData cfg) :
    HomogeneousFiveGeneralPosition d.goldenSecondRaw := by
  refine ⟨fun i => homogeneousLift_ne_zero _, ?_⟩
  intro i j k hij hik hjk
  exact homogeneousLift_det_ne_zero_of_mem_properCircle
    (invertedAwayGeometricBlockCircle cfg d.pivot.1 d.base.second
      d.pivot_not_mem_secondSupport)
    (d.goldenSecondPoint_mem_circle i)
    (d.goldenSecondPoint_mem_circle j)
    (d.goldenSecondPoint_mem_circle k)
    (d.goldenSecondPoint_injective.ne hij)
    (d.goldenSecondPoint_injective.ne hik)
    (d.goldenSecondPoint_injective.ne hjk)

private theorem first_center_eq_second_center
    (d : TenTwoPentagonSaturationData cfg)
    (i : Fin 4) (j : Fin 2) :
    firstExclusiveChordCenter cfg d.base.Γ d.base.Ω d.base.circles_ne
        (d.firstGoldenChord i) =
      secondExclusiveChordCenter cfg d.base.Γ d.base.Ω d.base.circles_ne
        (goldenLabelledChord d.secondLabel i j) := by
  have hfirst := d.firstGoldenChord_mem_factor i
  have hsecond := d.secondGoldenChord_mem_factor i j
  dsimp only [toNearOneFactorizationData] at hfirst hsecond
  rw [firstNearOneFactorization_factor] at hfirst
  rw [secondNearOneFactorization_factor] at hsecond
  exact ((mem_fullFibre _ _ _).mp hfirst).trans
    ((mem_fullFibre _ _ _).mp hsecond).symm

private noncomputable def goldenCompatiblePair
    (d : TenTwoPentagonSaturationData cfg)
    (i : Fin 4) (j : Fin 2) : d.CompatibleChordPair :=
  d.compatibleChordPairOfEq (d.firstGoldenChord i)
    (goldenLabelledChord d.secondLabel i j)
      (d.first_center_eq_second_center i j)

private theorem pivot_mem_goldenCrossBlock
    (d : TenTwoPentagonSaturationData cfg)
    (i : Fin 4) (j : Fin 2) :
    d.pivot.1 ∈ geometricBlockSupport cfg
      (d.crossBlockOfCompatiblePair (d.goldenCompatiblePair i j)).1 := by
  apply crossBlockFirstChord_subset_support cfg d.base.Γ d.base.Ω
    (d.crossBlockOfCompatiblePair (d.goldenCompatiblePair i j))
  simpa only [crossBlockFirstChord_crossBlockOfCompatiblePair,
    goldenCompatiblePair, compatibleChordPairOfEq_fst] using
      d.pivot_mem_firstGoldenChord i

private theorem secondEndpoint_ne_pivot
    (d : TenTwoPentagonSaturationData cfg)
    (i : Fin 4) (j k : Fin 2) :
    (d.secondLabel (goldenCenterChordEndpoint i j k)).1 ≠ d.pivot.1 := by
  intro h
  apply d.pivot_not_mem_secondSupport
  rw [← h]
  exact d.secondLabel_mem_secondSupport _

/-- The named pivot-inverted line carried by one saturated golden row.  This
public name lets the matching layer place the marked first point and both
second-chord endpoints on the same line without exposing the dependent
compatible-pair witness. -/
noncomputable def goldenRowPivotLine
    (d : TenTwoPentagonSaturationData cfg)
    (i : Fin 4) (j : Fin 2) :
    DeterminedLine (pivotInversion cfg d.pivot.1) :=
  blockToPivotLine cfg d.pivot.1
    (d.compatiblePairPivotBlock d.pivot.1
      (d.goldenCompatiblePair i j) (d.pivot_mem_goldenCrossBlock i j))

theorem golden_row_endpoint_mem_pivotLine
    (d : TenTwoPentagonSaturationData cfg)
    (i : Fin 4) (j k : Fin 2) :
    (⟨(d.secondLabel (goldenCenterChordEndpoint i j k)).1,
      d.secondEndpoint_ne_pivot i j k⟩ : AwayFrom d.pivot.1) ∈
      lineSupport (pivotInversion cfg d.pivot.1)
        (blockToPivotLine cfg d.pivot.1
          (d.compatiblePairPivotBlock d.pivot.1
            (d.goldenCompatiblePair i j)
              (d.pivot_mem_goldenCrossBlock i j))) := by
  apply d.secondChordEndpoint_mem_compatiblePairPivotLine
  simpa only [goldenCompatiblePair, compatibleChordPairOfEq_snd] using
    mem_goldenLabelledChord d.secondLabel i j k

theorem qLabel_mem_goldenPivotLine
    (d : TenTwoPentagonSaturationData cfg)
    (i : Fin 4) (j : Fin 2) :
    (⟨(d.qLabel i).1.1, d.qLabel_val_ne_pivot i⟩ : AwayFrom d.pivot.1) ∈
      lineSupport (pivotInversion cfg d.pivot.1)
        (blockToPivotLine cfg d.pivot.1
          (d.compatiblePairPivotBlock d.pivot.1
            (d.goldenCompatiblePair i j)
              (d.pivot_mem_goldenCrossBlock i j))) := by
  apply d.firstChordEndpoint_mem_compatiblePairPivotLine
  simpa only [goldenCompatiblePair, compatibleChordPairOfEq_fst] using
    d.qLabel_mem_firstGoldenChord i

/-- A displayed second-pentagon endpoint lies on the named golden row line. -/
theorem golden_row_endpoint_mem_goldenRowPivotLine
    (d : TenTwoPentagonSaturationData cfg)
    (i : Fin 4) (j k : Fin 2) :
    (⟨(d.secondLabel (goldenCenterChordEndpoint i j k)).1,
      d.secondEndpoint_ne_pivot i j k⟩ : AwayFrom d.pivot.1) ∈
      lineSupport (pivotInversion cfg d.pivot.1)
        (d.goldenRowPivotLine i j) := by
  unfold goldenRowPivotLine
  exact d.golden_row_endpoint_mem_pivotLine i j k

/-- The marked first-pentagon partner lies on the named golden row line. -/
theorem qLabel_mem_goldenRowPivotLine
    (d : TenTwoPentagonSaturationData cfg)
    (i : Fin 4) (j : Fin 2) :
    (⟨(d.qLabel i).1.1, d.qLabel_val_ne_pivot i⟩ : AwayFrom d.pivot.1) ∈
      lineSupport (pivotInversion cfg d.pivot.1)
        (d.goldenRowPivotLine i j) := by
  unfold goldenRowPivotLine
  exact d.qLabel_mem_goldenPivotLine i j

private theorem goldenSecondPoint_ne
    (d : TenTwoPentagonSaturationData cfg)
    {a b : Fin 5} (hab : a ≠ b) :
    d.goldenSecondPoint a ≠ d.goldenSecondPoint b :=
  d.goldenSecondPoint_injective.ne hab

/-- Every marked first point lies on both normalized second-pentagon chords
in its golden row. -/
theorem golden_centerIncidence
    (d : TenTwoPentagonSaturationData cfg) :
    GoldenAxisCenterIncidence d.goldenSecondRaw d.goldenFirstRaw := by
  intro i j
  let L := blockToPivotLine cfg d.pivot.1
    (d.compatiblePairPivotBlock d.pivot.1
      (d.goldenCompatiblePair i j) (d.pivot_mem_goldenCrossBlock i j))
  let a := goldenCenterChordEndpoint i j 0
  let b := goldenCenterChordEndpoint i j 1
  have hab : a ≠ b := by fin_cases i <;> fin_cases j <;> decide
  have ha : d.goldenSecondPoint a ∈ L.1 := by
    exact mem_lineSupport.mp (d.golden_row_endpoint_mem_pivotLine i j 0)
  have hb : d.goldenSecondPoint b ∈ L.1 := by
    exact mem_lineSupport.mp (d.golden_row_endpoint_mem_pivotLine i j 1)
  have hq : d.goldenFirstPoint i ∈ L.1 := by
    exact mem_lineSupport.mp (d.qLabel_mem_goldenPivotLine i j)
  have hline :
      affineSpan ℝ ({d.goldenSecondPoint a, d.goldenSecondPoint b} : Set Point2) =
        L.1 := by
    have habAway :
        (⟨(d.secondLabel a).1, d.secondEndpoint_ne_pivot i j 0⟩ :
            AwayFrom d.pivot.1) ≠
          ⟨(d.secondLabel b).1, d.secondEndpoint_ne_pivot i j 1⟩ := by
      intro h
      apply hab
      apply d.secondLabel.injective
      apply Subtype.ext
      exact congrArg (fun x : AwayFrom d.pivot.1 => x.1) h
    let A : KSubset (AwayFrom d.pivot.1) 2 :=
      ⟨{⟨(d.secondLabel a).1, d.secondEndpoint_ne_pivot i j 0⟩,
         ⟨(d.secondLabel b).1, d.secondEndpoint_ne_pivot i j 1⟩}, by
        exact Finset.card_pair habAway⟩
    have hmem : ∀ x ∈ A.1, (pivotInversion cfg d.pivot.1) x ∈ L.1 := by
      intro x hx
      simp only [A, Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact ha
      · exact hb
    have hpair := lineOfPair_eq_of_mem_of_direction_finrank_one
      (pivotInversion cfg d.pivot.1) A L.1 hmem L.direction_finrank
    have hpairExplicit :
        lineOfPair (pivotInversion cfg d.pivot.1) A =
          affineSpan ℝ
            ({d.goldenSecondPoint a, d.goldenSecondPoint b} : Set Point2) := by
      simpa only [A, goldenSecondPoint] using
        lineOfPair_pair (pivotInversion cfg d.pivot.1) habAway
    exact hpairExplicit.symm.trans hpair
  apply (homogeneousIncident_lineCovector_iff_det_eq_zero
    (d.goldenSecondPoint a) (d.goldenSecondPoint b)
      (d.goldenFirstPoint i)).1
  apply (homogeneousIncident_lineCovector_iff_mem_affineSpan
    (d.goldenSecondPoint_ne hab)).2
  rw [hline]
  exact hq

private theorem pivot_mem_firstCircle
    (d : TenTwoPentagonSaturationData cfg) :
    d.pivot.1 ∈ circleTrace cfg d.base.Γ.1 := by
  rw [d.base.circleTrace_Γ]
  simpa only [d.base.exclusiveTrace_Γ_Ω] using d.pivot.2

private theorem qLabel_mem_firstCircle
    (d : TenTwoPentagonSaturationData cfg) (i : Fin 4) :
    (d.qLabel i).1.1 ∈ circleTrace cfg d.base.Γ.1 := by
  rw [d.base.circleTrace_Γ]
  exact d.qLabel_mem_firstSupport i

/-- Inversion sends the four remaining first-pentagon points to one affine
line, hence every three of their homogeneous lifts have zero determinant. -/
theorem golden_axisCollinear
    (d : TenTwoPentagonSaturationData cfg) :
    GoldenAxisCollinear d.goldenFirstRaw := by
  intro i j k
  by_cases hij : i = j
  · subst j
    apply Matrix.det_zero_of_row_eq (i := (0 : Fin 3)) (j := (1 : Fin 3))
    · decide
    · rfl
  have hp : d.pivot.1 ∈ circleTrace cfg d.base.Γ.1 :=
    d.pivot_mem_firstCircle
  have hi : d.goldenFirstPoint i ∈
      circlePivotLine cfg d.pivot.1 d.base.Γ.1 :=
    (pivotInversion_mem_circlePivotLine_iff cfg d.pivot.1 d.base.Γ.1 hp
      ⟨(d.qLabel i).1.1, d.qLabel_val_ne_pivot i⟩).2
        (d.qLabel_mem_firstCircle i)
  have hj : d.goldenFirstPoint j ∈
      circlePivotLine cfg d.pivot.1 d.base.Γ.1 :=
    (pivotInversion_mem_circlePivotLine_iff cfg d.pivot.1 d.base.Γ.1 hp
      ⟨(d.qLabel j).1.1, d.qLabel_val_ne_pivot j⟩).2
        (d.qLabel_mem_firstCircle j)
  have hk : d.goldenFirstPoint k ∈
      circlePivotLine cfg d.pivot.1 d.base.Γ.1 :=
    (pivotInversion_mem_circlePivotLine_iff cfg d.pivot.1 d.base.Γ.1 hp
      ⟨(d.qLabel k).1.1, d.qLabel_val_ne_pivot k⟩).2
        (d.qLabel_mem_firstCircle k)
  have hline :
      affineSpan ℝ ({d.goldenFirstPoint i, d.goldenFirstPoint j} : Set Point2) =
        circlePivotLine cfg d.pivot.1 d.base.Γ.1 := by
    have hijAway :
        (⟨(d.qLabel i).1.1, d.qLabel_val_ne_pivot i⟩ :
            AwayFrom d.pivot.1) ≠
          ⟨(d.qLabel j).1.1, d.qLabel_val_ne_pivot j⟩ := by
      intro h
      apply hij
      apply d.qLabel.injective
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun x : AwayFrom d.pivot.1 => x.1) h
    let A : KSubset (AwayFrom d.pivot.1) 2 :=
      ⟨{⟨(d.qLabel i).1.1, d.qLabel_val_ne_pivot i⟩,
         ⟨(d.qLabel j).1.1, d.qLabel_val_ne_pivot j⟩}, by
        exact Finset.card_pair hijAway⟩
    have hmem : ∀ x ∈ A.1,
        (pivotInversion cfg d.pivot.1) x ∈
          circlePivotLine cfg d.pivot.1 d.base.Γ.1 := by
      intro x hx
      simp only [A, Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact hi
      · exact hj
    have hpair := lineOfPair_eq_of_mem_of_direction_finrank_one
      (pivotInversion cfg d.pivot.1) A
      (circlePivotLine cfg d.pivot.1 d.base.Γ.1) hmem
      (circlePivotLine_direction_finrank cfg d.pivot.1 d.base.Γ.1 hp)
    have hpairExplicit :
        lineOfPair (pivotInversion cfg d.pivot.1) A =
          affineSpan ℝ
            ({d.goldenFirstPoint i, d.goldenFirstPoint j} : Set Point2) := by
      simpa only [A, goldenFirstPoint] using
        lineOfPair_pair (pivotInversion cfg d.pivot.1) hijAway
    exact hpairExplicit.symm.trans hpair
  apply (homogeneousIncident_lineCovector_iff_det_eq_zero
    (d.goldenFirstPoint i) (d.goldenFirstPoint j)
      (d.goldenFirstPoint k)).1
  have hpointNe : d.goldenFirstPoint i ≠ d.goldenFirstPoint j := by
    intro h
    have haway := (pivotInversion cfg d.pivot.1).injective h
    apply hij
    apply d.qLabel.injective
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun x : AwayFrom d.pivot.1 => x.1) haway
  apply (homogeneousIncident_lineCovector_iff_mem_affineSpan hpointNe).2
  rw [hline]
  exact hk

/-- The complete neutral projective core attached to saturated two-pentagon
data. -/
noncomputable def goldenProjectiveCore
    (d : TenTwoPentagonSaturationData cfg) : GoldenAxisProjectiveCore where
  g := d.goldenSecondRaw
  q := d.goldenFirstRaw
  g_generalPosition := d.goldenSecondRaw_generalPosition
  q_ne_zero := fun i => homogeneousLift_ne_zero (d.goldenFirstPoint i)
  centerIncidence := d.golden_centerIncidence
  axisCollinear := d.golden_axisCollinear

end TenTwoPentagonSaturationData

end Erdos506.V1
