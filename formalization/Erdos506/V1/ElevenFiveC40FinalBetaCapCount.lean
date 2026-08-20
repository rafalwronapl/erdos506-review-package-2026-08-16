import Erdos506.V1.ElevenFiveC40FinalBetaCap
import Erdos506.V1.TenFive

/-!
# Counting the C40 pivot-inversion dictionary

The semantic injection from determined circles after a pivot inversion to
away nontrivial original blocks is supplied by `ElevenFiveC40FinalBetaCap`.
Here the five-block cap makes the latter family exactly the size-three,
size-four, and size-five layers.  The global C40/L11 row has 51 such blocks,
and filtering at a pivot removes precisely its three-layer block degree.
-/

namespace Erdos506.V1

open Erdos506.Block
open Erdos506.Block.BlockSystem
open Erdos506.Finite
open Erdos506.Incidence
open Erdos506.V3
open Erdos506.V4
open scoped BigOperators EuclideanSpace

universe u

/-- Distinct exact support-size layers are disjoint. -/
private theorem c40_blocksOfSize_disjoint
    {Point Block : Type*} [Fintype Point] [Fintype Block]
    [DecidableEq Point]
    (S : BlockSystem Point Block) {s t : ℕ} (hst : s ≠ t) :
    Disjoint (S.blocksOfSize s) (S.blocksOfSize t) := by
  classical
  apply Finset.disjoint_left.mpr
  intro b hbs hbt
  have hs := S.mem_blocksOfSize.mp hbs
  have ht := S.mem_blocksOfSize.mp hbt
  omega

/-- Under the size-five cap, the away nontrivial original blocks have
cardinality equal to the total nontrivial block count minus the three-layer
block degree at the pivot. -/
theorem elevenFive_pivotAwayBlock_card_eq_totalCircleCount_add_lineTotal_sub_beta
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    (cfg : Configuration Point)
    (hcap : BlockSizeCap (blockSystem cfg) 5)
    (hglobal : ElevenFiveGlobalRows (blockSystem cfg))
    (p : Point) :
    Fintype.card (PivotInversionAwayBlock cfg p) =
      (blockSystem cfg).totalCircleCount +
        elevenFiveLineTotal (blockSystem cfg) -
      ((blockSystem cfg).blockDegree 3 p +
        (blockSystem cfg).blockDegree 4 p +
          (blockSystem cfg).blockDegree 5 p) := by
  classical
  let S := blockSystem cfg
  let F : Finset (GeometricBlock cfg) :=
    Finset.univ.filter fun b => 3 ≤ (S.support b).card
  have hcapS : BlockSizeCap S 5 := by
    simpa only [S] using hcap
  have hglobalS : ElevenFiveGlobalRows S := by
    simpa only [S] using hglobal
  have hF : F =
      (S.blocksOfSize 3 ∪ S.blocksOfSize 4) ∪ S.blocksOfSize 5 := by
    ext b
    simp only [F, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_union]
    constructor
    · intro hb
      have hle : (S.support b).card ≤ 5 := hcapS b hb
      have hcases : (S.support b).card = 3 ∨
          (S.support b).card = 4 ∨ (S.support b).card = 5 := by
        omega
      rcases hcases with h3 | h4 | h5
      · exact Or.inl (Or.inl (S.mem_blocksOfSize.mpr h3))
      · exact Or.inl (Or.inr (S.mem_blocksOfSize.mpr h4))
      · exact Or.inr (S.mem_blocksOfSize.mpr h5)
    · intro hb
      rcases hb with (hb3 | hb4) | hb5
      · have h3 := S.mem_blocksOfSize.mp hb3
        omega
      · have h4 := S.mem_blocksOfSize.mp hb4
        omega
      · have h5 := S.mem_blocksOfSize.mp hb5
        omega
  have h34 : Disjoint (S.blocksOfSize 3) (S.blocksOfSize 4) :=
    c40_blocksOfSize_disjoint S (by omega)
  have h35 : Disjoint (S.blocksOfSize 3) (S.blocksOfSize 5) :=
    c40_blocksOfSize_disjoint S (by omega)
  have h45 : Disjoint (S.blocksOfSize 4) (S.blocksOfSize 5) :=
    c40_blocksOfSize_disjoint S (by omega)
  have h345 : Disjoint (S.blocksOfSize 3 ∪ S.blocksOfSize 4)
      (S.blocksOfSize 5) :=
    Finset.disjoint_union_left.mpr ⟨h35, h45⟩
  have hFcardRaw : F.card =
      S.blockCount 3 + S.blockCount 4 + S.blockCount 5 := by
    rw [hF, Finset.card_union_of_disjoint h345,
      Finset.card_union_of_disjoint h34]
    rfl
  have hFcard : F.card = S.totalCircleCount + elevenFiveLineTotal S :=
    hFcardRaw.trans hglobalS.blockTotal
  have h34p : Disjoint
      ((S.blocksOfSize 3).filter fun b => p ∈ S.support b)
      ((S.blocksOfSize 4).filter fun b => p ∈ S.support b) :=
    h34.mono
      (Finset.filter_subset (fun b => p ∈ S.support b) (S.blocksOfSize 3))
      (Finset.filter_subset (fun b => p ∈ S.support b) (S.blocksOfSize 4))
  have h35p : Disjoint
      ((S.blocksOfSize 3).filter fun b => p ∈ S.support b)
      ((S.blocksOfSize 5).filter fun b => p ∈ S.support b) :=
    h35.mono
      (Finset.filter_subset (fun b => p ∈ S.support b) (S.blocksOfSize 3))
      (Finset.filter_subset (fun b => p ∈ S.support b) (S.blocksOfSize 5))
  have h45p : Disjoint
      ((S.blocksOfSize 4).filter fun b => p ∈ S.support b)
      ((S.blocksOfSize 5).filter fun b => p ∈ S.support b) :=
    h45.mono
      (Finset.filter_subset (fun b => p ∈ S.support b) (S.blocksOfSize 4))
      (Finset.filter_subset (fun b => p ∈ S.support b) (S.blocksOfSize 5))
  have h345p : Disjoint
      (((S.blocksOfSize 3).filter fun b => p ∈ S.support b) ∪
        ((S.blocksOfSize 4).filter fun b => p ∈ S.support b))
      ((S.blocksOfSize 5).filter fun b => p ∈ S.support b) :=
    Finset.disjoint_union_left.mpr ⟨h35p, h45p⟩
  have hthrough : (F.filter fun b => p ∈ S.support b).card =
      S.blockDegree 3 p + S.blockDegree 4 p + S.blockDegree 5 p := by
    rw [hF, Finset.filter_union, Finset.filter_union,
      Finset.card_union_of_disjoint h345p,
      Finset.card_union_of_disjoint h34p]
    rfl
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := F) (p := fun b => p ∈ S.support b)
  have haway : (F.filter fun b => p ∉ S.support b).card =
      S.totalCircleCount + elevenFiveLineTotal S -
        (S.blockDegree 3 p + S.blockDegree 4 p + S.blockDegree 5 p) := by
    rw [hthrough, hFcard] at hsplit
    omega
  have hpivot : Fintype.card (PivotInversionAwayBlock cfg p) =
      (F.filter fun b => p ∉ S.support b).card := by
    change Fintype.card {b : GeometricBlock cfg //
      3 ≤ (S.support b).card ∧ p ∉ S.support b} = _
    change Fintype.card {b : GeometricBlock cfg //
      3 ≤ (S.support b).card ∧ p ∉ S.support b} =
      ((Finset.univ.filter fun b : GeometricBlock cfg =>
        3 ≤ (S.support b).card).filter fun b => p ∉ S.support b).card
    rw [Finset.filter_filter]
    simpa [and_assoc] using
      (Fintype.card_subtype (fun b : GeometricBlock cfg =>
        3 ≤ (S.support b).card ∧ p ∉ S.support b))
  simpa only [S] using hpivot.trans haway

/-- The `C = 40, L = 11` numerical specialization of the generic away-block
count. -/
theorem elevenFive_c40_l11_pivotAwayBlock_card_eq_fifty_one_sub_beta
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    (cfg : Configuration Point)
    (hcap : BlockSizeCap (blockSystem cfg) 5)
    (hglobal : ElevenFiveGlobalRows (blockSystem cfg))
    (hC : (blockSystem cfg).totalCircleCount = 40)
    (hL : elevenFiveLineTotal (blockSystem cfg) = 11)
    (p : Point) :
    Fintype.card (PivotInversionAwayBlock cfg p) =
      51 - ((blockSystem cfg).blockDegree 3 p +
        (blockSystem cfg).blockDegree 4 p +
          (blockSystem cfg).blockDegree 5 p) := by
  have h := elevenFive_pivotAwayBlock_card_eq_totalCircleCount_add_lineTotal_sub_beta
    cfg hcap hglobal p
  simpa [hC, hL] using h

/-- The `C = 40, L = 14` numerical specialization of the generic away-block
count. -/
theorem elevenFive_c40_l14_pivotAwayBlock_card_eq_fifty_four_sub_beta
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    (cfg : Configuration Point)
    (hcap : BlockSizeCap (blockSystem cfg) 5)
    (hglobal : ElevenFiveGlobalRows (blockSystem cfg))
    (hC : (blockSystem cfg).totalCircleCount = 40)
    (hL : elevenFiveLineTotal (blockSystem cfg) = 14)
    (p : Point) :
    Fintype.card (PivotInversionAwayBlock cfg p) =
      54 - ((blockSystem cfg).blockDegree 3 p +
        (blockSystem cfg).blockDegree 4 p +
          (blockSystem cfg).blockDegree 5 p) := by
  have h := elevenFive_pivotAwayBlock_card_eq_totalCircleCount_add_lineTotal_sub_beta
    cfg hcap hglobal p
  simpa [hC, hL] using h

/-- The semantic reverse dictionary bounds the number of determined circles
after pivot inversion by the away nontrivial original blocks. -/
theorem elevenFive_pivotInversion_circleCount_le_totalCircleCount_add_lineTotal_sub_beta
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    (cfg : Configuration Point)
    (hcap : BlockSizeCap (blockSystem cfg) 5)
    (hglobal : ElevenFiveGlobalRows (blockSystem cfg))
    (p : Point) :
    Erdos506.V4.circleCount (pivotInversion cfg p) ≤
      (blockSystem cfg).totalCircleCount +
        elevenFiveLineTotal (blockSystem cfg) -
      ((blockSystem cfg).blockDegree 3 p +
        (blockSystem cfg).blockDegree 4 p +
          (blockSystem cfg).blockDegree 5 p) := by
  rw [Erdos506.V3.circleCount_eq_card_determinedCircle]
  calc
    Fintype.card (DeterminedCircle (pivotInversion cfg p)) ≤
        Fintype.card (PivotInversionAwayBlock cfg p) :=
      Fintype.card_le_of_injective
        (pivotInversionCircleToAwayBlock cfg p)
        (pivotInversionCircleToAwayBlock_injective cfg p)
    _ = (blockSystem cfg).totalCircleCount +
        elevenFiveLineTotal (blockSystem cfg) -
      ((blockSystem cfg).blockDegree 3 p +
        (blockSystem cfg).blockDegree 4 p +
          (blockSystem cfg).blockDegree 5 p) :=
      elevenFive_pivotAwayBlock_card_eq_totalCircleCount_add_lineTotal_sub_beta
        cfg hcap hglobal p

/-- The semantic reverse dictionary in the `C = 40, L = 11` row. -/
theorem elevenFive_c40_l11_pivotInversion_circleCount_le_fifty_one_sub_beta
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    (cfg : Configuration Point)
    (hcap : BlockSizeCap (blockSystem cfg) 5)
    (hglobal : ElevenFiveGlobalRows (blockSystem cfg))
    (hC : (blockSystem cfg).totalCircleCount = 40)
    (hL : elevenFiveLineTotal (blockSystem cfg) = 11)
    (p : Point) :
    Erdos506.V4.circleCount (pivotInversion cfg p) ≤
      51 - ((blockSystem cfg).blockDegree 3 p +
        (blockSystem cfg).blockDegree 4 p +
          (blockSystem cfg).blockDegree 5 p) := by
  have h := elevenFive_pivotInversion_circleCount_le_totalCircleCount_add_lineTotal_sub_beta
    cfg hcap hglobal p
  simpa [hC, hL] using h

/-- The semantic reverse dictionary in the `C = 40, L = 14` row. -/
theorem elevenFive_c40_l14_pivotInversion_circleCount_le_fifty_four_sub_beta
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    (cfg : Configuration Point)
    (hcap : BlockSizeCap (blockSystem cfg) 5)
    (hglobal : ElevenFiveGlobalRows (blockSystem cfg))
    (hC : (blockSystem cfg).totalCircleCount = 40)
    (hL : elevenFiveLineTotal (blockSystem cfg) = 14)
    (p : Point) :
    Erdos506.V4.circleCount (pivotInversion cfg p) ≤
      54 - ((blockSystem cfg).blockDegree 3 p +
        (blockSystem cfg).blockDegree 4 p +
          (blockSystem cfg).blockDegree 5 p) := by
  have h := elevenFive_pivotInversion_circleCount_le_totalCircleCount_add_lineTotal_sub_beta
    cfg hcap hglobal p
  simpa [hC, hL] using h

/-- The ten-point lower bound after each pivot inversion forces the C40/L11
three-layer block degree cap `d₃ + d₄ + d₅ ≤ 18`. -/
theorem elevenFive_c40_l11_beta_cap
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    (Mel : RealPlaneMelchiorPrinciple.{u})
    (EvenArr : RealPlaneEvenArrangementPrinciple.{u})
    (Cross : RealPlaneRadicalAxisCrossBlockPrinciple.{u})
    (Kelly : RealPlaneKellyMoserPrinciple.{u})
    (U17 : RealPlaneSixCircleU17Principle.{u})
    (TenGeometry : RealPlaneTenFiveGeometry.{u})
    (cfg : Configuration Point) (hadm : Admissible cfg)
    (hcard : Fintype.card Point = 11)
    (hcap : BlockSizeCap (blockSystem cfg) 5)
    (hglobal : ElevenFiveGlobalRows (blockSystem cfg))
    (hC : (blockSystem cfg).totalCircleCount = 40)
    (hL : elevenFiveLineTotal (blockSystem cfg) = 11) :
    ∀ p : Point, (blockSystem cfg).blockDegree 3 p +
      (blockSystem cfg).blockDegree 4 p +
        (blockSystem cfg).blockDegree 5 p ≤ 18 := by
  intro p
  have hadmInv := pivotInversion_admissible_of_blockSizeCap_five
    cfg hadm hcard hcap p
  have hcardInv : Fintype.card (AwayFrom p) = 10 := by
    rw [card_awayFrom, hcard]
  have hlower := circleCount_ge_thirty_three_of_card_ten
    Mel EvenArr Cross Kelly U17 TenGeometry
      (pivotInversion cfg p) hadmInv hcardInv
  have hupper :=
    elevenFive_c40_l11_pivotInversion_circleCount_le_fifty_one_sub_beta
      cfg hcap hglobal hC hL p
  omega

/-- The same pivot-inversion count in the `C = 40, L = 14` layer gives the
three-layer block-degree cap `d₃ + d₄ + d₅ ≤ 21`. -/
theorem elevenFive_c40_l14_beta_cap
    {Point : Type u} [Fintype Point] [DecidableEq Point]
    (Mel : RealPlaneMelchiorPrinciple.{u})
    (EvenArr : RealPlaneEvenArrangementPrinciple.{u})
    (Cross : RealPlaneRadicalAxisCrossBlockPrinciple.{u})
    (Kelly : RealPlaneKellyMoserPrinciple.{u})
    (U17 : RealPlaneSixCircleU17Principle.{u})
    (TenGeometry : RealPlaneTenFiveGeometry.{u})
    (cfg : Configuration Point) (hadm : Admissible cfg)
    (hcard : Fintype.card Point = 11)
    (hcap : BlockSizeCap (blockSystem cfg) 5)
    (hglobal : ElevenFiveGlobalRows (blockSystem cfg))
    (hC : (blockSystem cfg).totalCircleCount = 40)
    (hL : elevenFiveLineTotal (blockSystem cfg) = 14) :
    ∀ p : Point, (blockSystem cfg).blockDegree 3 p +
      (blockSystem cfg).blockDegree 4 p +
        (blockSystem cfg).blockDegree 5 p ≤ 21 := by
  intro p
  have hadmInv := pivotInversion_admissible_of_blockSizeCap_five
    cfg hadm hcard hcap p
  have hcardInv : Fintype.card (AwayFrom p) = 10 := by
    rw [card_awayFrom, hcard]
  have hlower := circleCount_ge_thirty_three_of_card_ten
    Mel EvenArr Cross Kelly U17 TenGeometry
      (pivotInversion cfg p) hadmInv hcardInv
  have hupper :=
    elevenFive_c40_l14_pivotInversion_circleCount_le_fifty_four_sub_beta
      cfg hcap hglobal hC hL p
  omega

end Erdos506.V1
