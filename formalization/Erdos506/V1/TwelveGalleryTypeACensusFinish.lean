import Erdos506.V1.TwelveGalleryTypeATriangulationFinish

/-!
# The exact restored-dual census in the Type-A gallery row

This module is the numerical adapter between the local Type-A pivot data
and the arrangement-level gallery completion.  It contains no topology:
the four multiplicity fibres are the actual finite vertex sets of the
restored labelled-dual arrangement.
-/

namespace Erdos506.V1

open Erdos506.Block.BlockSystem
open Erdos506.Incidence
open Erdos506.V4

universe u

/-- Exact actual-vertex census needed by the finite Type-A cut saturation. -/
structure TwelveGalleryTypeARestoredDualCensus
    {alpha : Type u} [Fintype alpha] [DecidableEq alpha]
    (cfg : Configuration alpha) (p : alpha) : Prop where
  lineDegree_two : (blockSystem cfg).lineDegree 2 p = 3
  multiplicity_two :
    (twelveDirectionDualMultiplicityVertices
      (restoredPivotConfiguration cfg p) 2).card = 6
  multiplicity_three :
    (twelveDirectionDualMultiplicityVertices
      (restoredPivotConfiguration cfg p) 3).card = 14
  multiplicity_four :
    (twelveDirectionDualMultiplicityVertices
      (restoredPivotConfiguration cfg p) 4).card = 3
  multiplicity_five :
    (twelveDirectionDualMultiplicityVertices
      (restoredPivotConfiguration cfg p) 5).card = 0
  multiplicity_le_four :
    ∀ q ∈ labelDualVertexSet (restoredPivotConfiguration cfg p),
      (labelDualArrangement
        (restoredPivotConfiguration cfg p)).multiplicity q ≤ 4

/-- The literal Type-A row gives `(t₂,t₃,t₄,t₅)=(6,14,3,0)` in
the concrete restored labelled-dual arrangement. -/
theorem twelveGallery_typeA_restoredDualCensus
    {alpha : Type u} [Fintype alpha] [DecidableEq alpha]
    (cfg : Configuration alpha)
    (hcap : BlockSizeCap (blockSystem cfg) 6)
    (p : alpha)
    (hrows : TwelveFiveLocalRows (blockSystem cfg) p)
    (hd3 : (blockSystem cfg).blockDegree 3 p = 7)
    (hd4 : (blockSystem cfg).blockDegree 4 p = 10)
    (hd5 : (blockSystem cfg).blockDegree 5 p = 3)
    (hd6 : (blockSystem cfg).blockDegree 6 p = 0)
    (hl3 : (blockSystem cfg).lineDegree 3 p = 4)
    (hl4 : (blockSystem cfg).lineDegree 4 p = 0)
    (hl5 : (blockSystem cfg).lineDegree 5 p = 0)
    (hl6 : (blockSystem cfg).lineDegree 6 p = 0) :
    TwelveGalleryTypeARestoredDualCensus cfg p := by
  classical
  let S := blockSystem cfg
  let restored := restoredPivotConfiguration cfg p
  let A := labelDualArrangement restored
  have hl2 : S.lineDegree 2 p = 3 := by
    have hline : S.lineDegree 2 p + 2 * S.lineDegree 3 p +
        3 * S.lineDegree 4 p + 4 * S.lineDegree 5 p +
        5 * S.lineDegree 6 p = 11 := by
      simpa only [S] using hrows.lineArmRow
    have hl3' : S.lineDegree 3 p = 4 := by simpa only [S] using hl3
    have hl4' : S.lineDegree 4 p = 0 := by simpa only [S] using hl4
    have hl5' : S.lineDegree 5 p = 0 := by simpa only [S] using hl5
    have hl6' : S.lineDegree 6 p = 0 := by simpa only [S] using hl6
    rw [hl3', hl4', hl5', hl6'] at hline
    omega
  have ht2 : twelveDirectionT2 S p = 6 := by
    simp only [twelveDirectionT2]
    rw [hd3, hl3, hl2]
    norm_num
  have ht3 : twelveDirectionT3 S p = 14 := by
    simp only [twelveDirectionT3]
    rw [hd4, hl4, hl3]
    norm_num
  have ht4 : twelveDirectionT4 S p = 3 := by
    simp only [twelveDirectionT4]
    rw [hd5, hl5, hl4]
    norm_num
  have ht5 : twelveDirectionT5 S p = 0 := by
    simp only [twelveDirectionT5]
    rw [hd6, hl5]
    norm_num
  have htwoRaw :=
    card_twelveDirectionDualMultiplicityVertices_restored_eq_twelveDirectionT2
      cfg p
  have hthreeRaw :=
    card_twelveDirectionDualMultiplicityVertices_restored_eq_twelveDirectionT3
      cfg p
  have hfourRaw :=
    card_twelveDirectionDualMultiplicityVertices_restored_eq_twelveDirectionT4
      cfg p
  have hfiveRaw :=
    card_twelveDirectionDualMultiplicityVertices_restored_eq_twelveDirectionT5
      cfg p hl6
  rw [ht2] at htwoRaw
  rw [ht3] at hthreeRaw
  rw [ht4] at hfourRaw
  rw [ht5] at hfiveRaw
  have htwo :
      (twelveDirectionDualMultiplicityVertices restored 2).card = 6 := by
    exact_mod_cast htwoRaw
  have hthree :
      (twelveDirectionDualMultiplicityVertices restored 3).card = 14 := by
    exact_mod_cast hthreeRaw
  have hfour :
      (twelveDirectionDualMultiplicityVertices restored 4).card = 3 := by
    exact_mod_cast hfourRaw
  have hfive :
      (twelveDirectionDualMultiplicityVertices restored 5).card = 0 := by
    exact_mod_cast hfiveRaw
  have hfiveEmpty :
      twelveDirectionDualMultiplicityVertices restored 5 = ∅ :=
    Finset.card_eq_zero.mp hfive
  have hleFour : ∀ q ∈ labelDualVertexSet restored,
      A.multiplicity q ≤ 4 := by
    intro q hq
    have hleFive : A.multiplicity q ≤ 5 := by
      apply
        labelDualMultiplicity_restored_le_five_of_blockSizeCap_of_lineDegree_six_eq_zero
          cfg p hcap hl6
      simpa only [A, restored, labelDualVertexSet] using hq
    have hneFive : A.multiplicity q ≠ 5 := by
      intro hqFive
      have hmem : q ∈ twelveDirectionDualMultiplicityVertices restored 5 :=
        (mem_twelveDirectionDualMultiplicityVertices_iff restored 5 q).2
          ⟨hq, by simpa only [A] using hqFive⟩
      rw [hfiveEmpty] at hmem
      simpa using hmem
    omega
  exact
    { lineDegree_two := by simpa only [S] using hl2
      multiplicity_two := by simpa only [restored] using htwo
      multiplicity_three := by simpa only [restored] using hthree
      multiplicity_four := by simpa only [restored] using hfour
      multiplicity_five := by simpa only [restored] using hfive
      multiplicity_le_four := by simpa only [A, restored] using hleFour }

end Erdos506.V1
