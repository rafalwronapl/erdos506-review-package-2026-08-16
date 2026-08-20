import Erdos506.V1.ElevenGammaSix
import Erdos506.V1.ElevenGammaSixLowOrdinary

/-!
# Configuration-level eleven-point selected-six endpoint

The materialized relative census lives in `ElevenGammaSix`.  This module
keeps the configuration bridges and the low-ordinary case split in separate
declarations, so the pure arithmetic certificates remain independently
cacheable.
-/

namespace Erdos506.V1

open Erdos506.Block
open Erdos506.Block.BlockSystem
open Erdos506.Incidence
open Erdos506.V4

universe u

/-- Named materialized rows used by the low-ordinary reducer. -/
structure ElevenGammaSixLowOrdinaryEventRows
    {Point Block : Type*} [Fintype Point] [Fintype Block]
    [DecidableEq Point] (S : BlockSystem Point Block) (D : Finset Point) : Prop where
  circle_le_forty : S.totalCircleCount <= 40
  circle_census : S.totalCircleCount = elevenGammaSixCircleTotalCensus S D
  footprint_three : elevenGammaSixFootprintCount S D 3 =
    elevenGammaSixFootprintThreeCensus S D
  footprint_four : elevenGammaSixFootprintCount S D 4 =
    elevenGammaSixFootprintFourCensus S D
  footprint_five : elevenGammaSixFootprintCount S D 5 =
    elevenGammaSixFootprintFiveCensus S D
  footprint_row : elevenGammaSixFootprintCount S D 3 +
    4 * elevenGammaSixFootprintCount S D 4 +
    10 * elevenGammaSixFootprintCount S D 5 = 10
  footprint_four_le_one : elevenGammaSixFootprintCount S D 4 <= 1
  footprint_five_le_one : elevenGammaSixFootprintCount S D 5 <= 1
  triple_one : elevenGammaSixTripleOneCensus S D = 60
  triple_two : elevenGammaSixTripleTwoCensus S D = 75
  line_capacity : elevenGammaSixLineCapacityUsed S D <= 30
  ordinary_small : elevenGammaSixOrdinaryCircleIncidence S D <= 14
  melchior : elevenGammaSixLineMelchiorUsed S D <= 52
  large_lines : elevenGammaSixLargeLineFootprintWeight S D <= 2
  kelly : 25 <= elevenGammaSixOutsiderThreeBlockIncidence S D
  line_incidence : elevenGammaSixLineIncidence S D <= 14
  profileB_weight :
    elevenGammaSixFootprintCount S D 3 = 6 ->
    elevenGammaSixFootprintCount S D 4 = 1 ->
    elevenGammaSixFootprintCount S D 5 = 0 ->
    elevenGammaSixWeight S D <= 26
  meeting_weight : elevenGammaSixRelativeCount S D .circle 1 5 = 1 ->
    elevenGammaSixWeight S D <= 20
  outsider_line_weight : elevenGammaSixRelativeCount S D .line 0 5 = 1 ->
    elevenGammaSixWeight S D <= 26
  outsider_circle_weight : elevenGammaSixRelativeCount S D .circle 0 5 = 1 ->
    elevenGammaSixWeight S D <= 26

/-- Configuration geometry supplies every named row needed by the pure
low-ordinary reducer. -/
theorem elevenGammaSixLowOrdinaryEventRows_of_configuration
    {alpha : Type u} [Fintype alpha] [DecidableEq alpha]
    (Mel : RealPlaneMelchiorPrinciple.{u})
    (Kelly : RealPlaneKellyMoserPrinciple.{u})
    (cfg : Configuration alpha) (hadm : Admissible cfg)
    (hpoint : Fintype.card alpha = 11)
    (gamma : DeterminedCircle cfg)
    (hgamma : (circleTrace cfg gamma.1).card = 6)
    (hcount : Erdos506.V4.circleCount cfg <= 40)
    (hO : elevenGammaSixOrdinaryCircleIncidence (blockSystem cfg)
      (circleTrace cfg gamma.1) <= 14) :
    ElevenGammaSixLowOrdinaryEventRows (blockSystem cfg)
      (circleTrace cfg gamma.1) := by
  classical
  let S := blockSystem cfg
  let D : Finset alpha := circleTrace cfg gamma.1
  let X : Finset alpha := Finset.univ \ D
  let gammaBlock : GeometricBlock cfg := Sum.inr gamma
  have hcircleCapGeom : forall c : DeterminedCircle cfg,
      (circleTrace cfg c.1).card <= 6 := by
    intro c
    exact circleTrace_card_le_six_of_eleven_of_circleCount_le
      cfg hadm hpoint hcount c
  have hlineCapGeom : forall L : DeterminedLine cfg,
      (lineSupport cfg L).card <= 6 := by
    intro L
    have hfive := lineSupport_card_le_five_of_eleven_of_circleCount_le
      cfg hadm hpoint hcount L
    omega
  have hcircleCap : forall b : GeometricBlock cfg,
      S.kind b = .circle -> (S.support b).card <= 6 := by
    intro b hb
    cases b with
    | inl L => cases hb
    | inr c => exact hcircleCapGeom c
  have hlineCap : forall b : GeometricBlock cfg,
      S.kind b = .line -> (S.support b).card <= 6 := by
    intro b hb
    cases b with
    | inl L => exact hlineCapGeom L
    | inr c => cases hb
  have hCbridge : S.totalCircleCount = Erdos506.V4.circleCount cfg := by
    dsimp only [S]
    rw [totalCircleCount_eq_card_determinedCircle,
      ← Erdos506.V3.circleCount_eq_card_determinedCircle]
  have hC : S.totalCircleCount <= 40 := by omega
  have hmel : elevenGammaSixLineMelchiorUsed S D <= 52 := by
    simpa [S, D] using elevenGammaSixLineMelchiorUsed_le_fifty_two
      Mel cfg hadm hpoint gamma hgamma hlineCapGeom
  have hkelly : 25 <= elevenGammaSixOutsiderThreeBlockIncidence S D := by
    simpa [S, D] using
      twenty_five_le_elevenGammaSixOutsiderThreeBlockIncidence
        Kelly cfg hadm hpoint gamma hgamma
  have hweightSemantic : elevenGammaSixWeight S D =
      sixConicWeight cfg gamma X := by
    simpa [S, D, X] using elevenGammaSixWeight_eq_sixConicWeight
      cfg gamma hpoint hgamma hcircleCapGeom
  have hlineSemantic : elevenGammaSixLineIncidence S D =
      sixConicLineIncidence cfg gamma X := by
    simpa [S, D, X] using elevenGammaSixLineIncidence_eq_sixConicLineIncidence
      cfg gamma hpoint hgamma hlineCapGeom
  have hX : X.card = 5 := by
    simp [X, D, Finset.card_sdiff_of_subset
      (Finset.subset_univ (circleTrace cfg gamma.1)), hpoint, hgamma]
  have hdisjoint : Disjoint (circleTrace cfg gamma.1) X := by
    simp [X, D, Finset.disjoint_left]
  have hJ : elevenGammaSixLineIncidence S D <= 14 := by
    rw [hlineSemantic]
    exact sixConic_line_incidence_le_fourteen
      cfg gamma hgamma X hX hdisjoint
  have hB :
      elevenGammaSixFootprintCount S D 3 = 6 ->
      elevenGammaSixFootprintCount S D 4 = 1 ->
      elevenGammaSixFootprintCount S D 5 = 0 ->
      elevenGammaSixWeight S D <= 26 := by
    intro _hthree hfour _hfive
    obtain ⟨b, hb⟩ := elevenGammaSix_exists_four_outsider_block S D hfour
    have hhost : HasFourOutsiderHost cfg X :=
      ⟨b, by simpa [S, D, X, geometricBlockSupport] using hb⟩
    rw [hweightSemantic]
    exact sixConic_four_outsider_host_weight_le
      cfg gamma hgamma X hX hdisjoint hhost
  have hc15 : elevenGammaSixRelativeCount S D .circle 1 5 = 1 ->
      elevenGammaSixWeight S D <= 20 := by
    intro hc15
    obtain ⟨b, _hbKind, hbInside, hbOutside⟩ :=
      elevenGammaSix_exists_relative_block_of_count_eq_one
        S D .circle 1 5 hc15
    have hhost : HasFiveOutsiderHostMeeting cfg gamma X := by
      refine ⟨b, ?_, ?_⟩
      · exact elevenGammaSix_complement_subset_support_of_outside_five
          S D hpoint hgamma b hbOutside
      · exact elevenGammaSix_support_not_disjoint_of_inside_pos
          S D b (by omega)
    rw [hweightSemantic]
    exact sixConic_five_outsider_host_meeting_weight_le_of_blockCap
      cfg gamma hgamma X hX hdisjoint
        (fun H => by cases H with
          | inl L => exact hlineCapGeom L
          | inr c => exact hcircleCapGeom c) hhost
  have hdisjointWeight (kind : BlockKind) :
      elevenGammaSixRelativeCount S D kind 0 5 = 1 ->
      elevenGammaSixWeight S D <= 26 := by
    intro hhostCount
    obtain ⟨b, _hbKind, hbInside, hbOutside⟩ :=
      elevenGammaSix_exists_relative_block_of_count_eq_one
        S D kind 0 5 hhostCount
    have hhost : HasFiveOutsiderHostDisjoint cfg gamma X := by
      refine ⟨b, ?_, ?_⟩
      · exact elevenGammaSix_complement_subset_support_of_outside_five
          S D hpoint hgamma b hbOutside
      · exact elevenGammaSix_support_disjoint_of_inside_zero S D b hbInside
    rw [hweightSemantic]
    exact sixConic_five_outsider_host_disjoint_weight_le
      cfg gamma hgamma X hX hdisjoint hhost
  constructor
  · exact hC
  · exact elevenGammaSix_circleTotalCensus_eq
      S D gammaBlock hpoint hgamma rfl rfl hcircleCap
  · exact elevenGammaSix_footprintThreeCensus_eq S D gammaBlock rfl
  · exact elevenGammaSix_footprintFourCensus_eq S D gammaBlock rfl
  · exact elevenGammaSix_footprintFiveCensus_eq
      S D gammaBlock rfl hcircleCap hlineCap
  · exact elevenGammaSix_footprint_row_of_blockSystem S D hpoint hgamma
  · exact elevenGammaSix_footprintCount_le_one S D hpoint hgamma 4 (by omega)
  · exact elevenGammaSix_footprintCount_le_one S D hpoint hgamma 5 (by omega)
  · exact elevenGammaSix_tripleOneCensus_eq_sixty
      S D gammaBlock hpoint hgamma rfl rfl hcircleCap hlineCap
  · exact elevenGammaSix_tripleTwoCensus_eq_seventy_five
      S D gammaBlock hpoint hgamma rfl rfl hcircleCap hlineCap
  · exact elevenGammaSixLineCapacityUsed_le_thirty
      S D gammaBlock hpoint hgamma rfl rfl hlineCap
  · simpa [S, D] using hO
  · exact hmel
  · exact elevenGammaSixLargeLineFootprintWeight_le_two
      S D gammaBlock hpoint hgamma rfl rfl hlineCap
  · exact hkelly
  · exact hJ
  · exact hB
  · exact hc15
  · exact hdisjointWeight .line
  · exact hdisjointWeight .circle

/-- The named rows reduce the low-ordinary branch to either the rich
six-line marker or an outsider five-circle with total outsider three-block
incidence exactly twenty-seven. -/
theorem elevenGammaSix_lowOrdinary_endpoint_of_rows
    {Point Block : Type*} [Fintype Point] [Fintype Block]
    [DecidableEq Point]
    (S : BlockSystem Point Block) (D : Finset Point)
    (rows : ElevenGammaSixLowOrdinaryEventRows S D) :
    elevenGammaSixRelativeCount S D .line 1 5 = 1 \/
      (elevenGammaSixRelativeCount S D .circle 0 5 = 1 /\
        elevenGammaSixOutsiderThreeBlockIncidence S D = 27) := by
  have hprofiles := elevenGammaSix_lowOrdinary_footprint_trichotomy
    (elevenGammaSixFootprintCount S D 3)
    (elevenGammaSixFootprintCount S D 4)
    (elevenGammaSixFootprintCount S D 5)
    rows.footprint_row rows.footprint_four_le_one rows.footprint_five_le_one
  rcases hprofiles with hA | hB | hC
  · rcases hA with ⟨hN3, hN4, hN5⟩
    have hN3raw := rows.footprint_three.symm.trans hN3
    have hN4raw := rows.footprint_four.symm.trans hN4
    have hN5raw := rows.footprint_five.symm.trans hN5
    simp only [elevenGammaSixFootprintThreeCensus] at hN3raw
    simp only [elevenGammaSixFootprintFourCensus] at hN4raw
    simp only [elevenGammaSixFootprintFiveCensus] at hN5raw
    have hc04 : elevenGammaSixRelativeCount S D .circle 0 4 = 0 := by omega
    have hl04 : elevenGammaSixRelativeCount S D .line 0 4 = 0 := by omega
    have hc14 : elevenGammaSixRelativeCount S D .circle 1 4 = 0 := by omega
    have hl14 : elevenGammaSixRelativeCount S D .line 1 4 = 0 := by omega
    have hc24 : elevenGammaSixRelativeCount S D .circle 2 4 = 0 := by omega
    have hl24 : elevenGammaSixRelativeCount S D .line 2 4 = 0 := by omega
    have hc05 : elevenGammaSixRelativeCount S D .circle 0 5 = 0 := by omega
    have hl05 : elevenGammaSixRelativeCount S D .line 0 5 = 0 := by omega
    have hc15 : elevenGammaSixRelativeCount S D .circle 1 5 = 0 := by omega
    have hl15 : elevenGammaSixRelativeCount S D .line 1 5 = 0 := by omega
    have hT1 := rows.triple_one
    have hT2 := rows.triple_two
    have hLC := rows.line_capacity
    have hO := rows.ordinary_small
    have hLarge := rows.large_lines
    simp only [elevenGammaSixTripleOneCensus, hc14, hl14,
      hc24, hl24, hc15, hl15, mul_zero, add_zero] at hT1
    simp only [elevenGammaSixTripleTwoCensus, hc24, hl24, mul_zero,
      add_zero] at hT2
    simp only [elevenGammaSixLineCapacityUsed, hl14, hl24, hl15,
      mul_zero, add_zero] at hLC
    simp only [elevenGammaSixOrdinaryCircleIncidence] at hO
    simp only [elevenGammaSixLargeLineFootprintWeight, hl04, hl05, hl14,
      hl15, hl24, mul_zero, add_zero] at hLarge
    have hT1Grouped :
        elevenGammaSixRelativeCount S D .circle 1 2 +
          elevenGammaSixRelativeCount S D .line 1 2 +
          3 * (elevenGammaSixRelativeCount S D .circle 1 3 +
            elevenGammaSixRelativeCount S D .line 1 3) +
          2 * (elevenGammaSixRelativeCount S D .circle 2 2 +
            elevenGammaSixRelativeCount S D .line 2 2) +
          6 * (elevenGammaSixRelativeCount S D .circle 2 3 +
            elevenGammaSixRelativeCount S D .line 2 3) = 60 := by
      omega
    have hT2Grouped :
        elevenGammaSixRelativeCount S D .circle 2 1 +
          elevenGammaSixRelativeCount S D .line 2 1 +
          2 * (elevenGammaSixRelativeCount S D .circle 2 2 +
            elevenGammaSixRelativeCount S D .line 2 2) +
          3 * (elevenGammaSixRelativeCount S D .circle 2 3 +
            elevenGammaSixRelativeCount S D .line 2 3) = 75 := by
      omega
    exact False.elim (elevenGammaSix_lowOrdinary_n3_ten_impossible
      (elevenGammaSixRelativeCount S D .circle 0 3)
      (elevenGammaSixRelativeCount S D .circle 1 2)
      (elevenGammaSixRelativeCount S D .circle 1 3)
      (elevenGammaSixRelativeCount S D .circle 2 1)
      (elevenGammaSixRelativeCount S D .circle 2 2)
      (elevenGammaSixRelativeCount S D .circle 2 3)
      (elevenGammaSixRelativeCount S D .line 0 3)
      (elevenGammaSixRelativeCount S D .line 1 2)
      (elevenGammaSixRelativeCount S D .line 1 3)
      (elevenGammaSixRelativeCount S D .line 2 1)
      (elevenGammaSixRelativeCount S D .line 2 2)
      (elevenGammaSixRelativeCount S D .line 2 3)
      hN3raw hT1Grouped hT2Grouped hLC hO hLarge)
  · rcases hB with ⟨hN3, hN4, hN5⟩
    have hN3raw := rows.footprint_three.symm.trans hN3
    have hN4raw := rows.footprint_four.symm.trans hN4
    have hN5raw := rows.footprint_five.symm.trans hN5
    simp only [elevenGammaSixFootprintThreeCensus] at hN3raw
    simp only [elevenGammaSixFootprintFourCensus] at hN4raw
    simp only [elevenGammaSixFootprintFiveCensus] at hN5raw
    have hc05zero : elevenGammaSixRelativeCount S D .circle 0 5 = 0 := by
      omega
    have hc15zero : elevenGammaSixRelativeCount S D .circle 1 5 = 0 := by
      omega
    have hcircle := rows.circle_census
    have hCle := rows.circle_le_forty
    simp only [elevenGammaSixCircleTotalCensus] at hcircle
    have hlarge := rows.large_lines
    simp only [elevenGammaSixLargeLineFootprintWeight] at hlarge
    have hA : 5 <=
        elevenGammaSixRelativeCount S D .circle 0 3 +
        elevenGammaSixRelativeCount S D .circle 1 3 +
        elevenGammaSixRelativeCount S D .circle 2 3 +
        elevenGammaSixRelativeCount S D .circle 0 4 +
        elevenGammaSixRelativeCount S D .circle 1 4 +
        elevenGammaSixRelativeCount S D .circle 2 4 := by omega
    have hcircleSmall :
        (elevenGammaSixRelativeCount S D .circle 0 3 +
          elevenGammaSixRelativeCount S D .circle 1 3 +
          elevenGammaSixRelativeCount S D .circle 2 3 +
          elevenGammaSixRelativeCount S D .circle 0 4 +
          elevenGammaSixRelativeCount S D .circle 1 4 +
          elevenGammaSixRelativeCount S D .circle 2 4) +
          elevenGammaSixRelativeCount S D .circle 1 2 +
          elevenGammaSixRelativeCount S D .circle 2 1 +
          elevenGammaSixRelativeCount S D .circle 2 2 <= 39 := by
      omega
    have hT2 := rows.triple_two
    simp only [elevenGammaSixTripleTwoCensus] at hT2
    have hW := rows.profileB_weight hN3 hN4 hN5
    simp only [elevenGammaSixWeight] at hW
    have hJ := rows.line_incidence
    simp only [elevenGammaSixLineIncidence] at hJ
    exact False.elim
      (elevenGammaSix_lowOrdinary_n3_six_n4_one_impossible
        (elevenGammaSixRelativeCount S D .circle 0 3 +
          elevenGammaSixRelativeCount S D .circle 1 3 +
          elevenGammaSixRelativeCount S D .circle 2 3 +
          elevenGammaSixRelativeCount S D .circle 0 4 +
          elevenGammaSixRelativeCount S D .circle 1 4 +
          elevenGammaSixRelativeCount S D .circle 2 4)
        (elevenGammaSixRelativeCount S D .circle 1 2)
        (elevenGammaSixRelativeCount S D .circle 2 1)
        (elevenGammaSixRelativeCount S D .circle 2 2)
        (elevenGammaSixRelativeCount S D .circle 2 3)
        (elevenGammaSixRelativeCount S D .circle 2 4)
        (elevenGammaSixLineIncidence S D)
        hA hcircleSmall (by omega) hW hJ)
  · rcases hC with ⟨hN3, hN4, hN5⟩
    have hN3raw := rows.footprint_three.symm.trans hN3
    have hN4raw := rows.footprint_four.symm.trans hN4
    simp only [elevenGammaSixFootprintThreeCensus] at hN3raw
    simp only [elevenGammaSixFootprintFourCensus] at hN4raw
    have hc03 : elevenGammaSixRelativeCount S D .circle 0 3 = 0 := by omega
    have hl03 : elevenGammaSixRelativeCount S D .line 0 3 = 0 := by omega
    have hc13 : elevenGammaSixRelativeCount S D .circle 1 3 = 0 := by omega
    have hl13 : elevenGammaSixRelativeCount S D .line 1 3 = 0 := by omega
    have hc23 : elevenGammaSixRelativeCount S D .circle 2 3 = 0 := by omega
    have hl23 : elevenGammaSixRelativeCount S D .line 2 3 = 0 := by omega
    have hc04 : elevenGammaSixRelativeCount S D .circle 0 4 = 0 := by omega
    have hl04 : elevenGammaSixRelativeCount S D .line 0 4 = 0 := by omega
    have hc14 : elevenGammaSixRelativeCount S D .circle 1 4 = 0 := by omega
    have hl14 : elevenGammaSixRelativeCount S D .line 1 4 = 0 := by omega
    have hc24 : elevenGammaSixRelativeCount S D .circle 2 4 = 0 := by omega
    have hl24 : elevenGammaSixRelativeCount S D .line 2 4 = 0 := by omega
    have hcircle := rows.circle_census
    have hN5raw := rows.footprint_five.symm.trans hN5
    have hT1 := rows.triple_one
    have hT2 := rows.triple_two
    have hLC := rows.line_capacity
    have hO := rows.ordinary_small
    have hMel := rows.melchior
    have hK := rows.kelly
    have hJ := rows.line_incidence
    simp only [elevenGammaSixCircleTotalCensus, hc03, hc04, hc13, hc14,
      hc23, hc24, add_zero] at hcircle
    simp only [elevenGammaSixFootprintFiveCensus] at hN5raw
    simp only [elevenGammaSixTripleOneCensus, hc13, hl13, hc14, hl14,
      hc23, hl23, hc24, hl24, mul_zero, add_zero] at hT1
    simp only [elevenGammaSixTripleTwoCensus, hc23, hl23, hc24, hl24,
      mul_zero, add_zero] at hT2
    simp only [elevenGammaSixLineCapacityUsed, hl13, hl14, hl23, hl24,
      mul_zero, add_zero] at hLC
    simp only [elevenGammaSixOrdinaryCircleIncidence, hc03, mul_zero,
      zero_add] at hO
    simp only [elevenGammaSixLineMelchiorUsed, hl03, hl04, hl13, hl14,
      hl23, hl24, mul_zero, add_zero] at hMel
    simp only [elevenGammaSixOutsiderThreeBlockIncidence, hc03, hl03,
      mul_zero, zero_add] at hK
    simp only [elevenGammaSixLineIncidence, hl23, hl24, mul_zero,
      add_zero] at hJ
    have hc15 := rows.meeting_weight
    have hl05 := rows.outsider_line_weight
    have hc05 := rows.outsider_circle_weight
    simp only [elevenGammaSixWeight, hc23, hc24, mul_zero, add_zero]
      at hc15 hl05 hc05
    have hT1Grouped :
        elevenGammaSixRelativeCount S D .circle 1 2 +
          elevenGammaSixRelativeCount S D .line 1 2 +
          10 * (elevenGammaSixRelativeCount S D .circle 1 5 +
            elevenGammaSixRelativeCount S D .line 1 5) +
          2 * (elevenGammaSixRelativeCount S D .circle 2 2 +
            elevenGammaSixRelativeCount S D .line 2 2) = 60 := by
      omega
    have hT2Grouped :
        elevenGammaSixRelativeCount S D .circle 2 1 +
          elevenGammaSixRelativeCount S D .line 2 1 +
          2 * (elevenGammaSixRelativeCount S D .circle 2 2 +
            elevenGammaSixRelativeCount S D .line 2 2) = 75 := by
      omega
    have hMelNormalized :
        12 * elevenGammaSixRelativeCount S D .line 0 5 +
          3 * elevenGammaSixRelativeCount S D .line 1 2 +
          18 * elevenGammaSixRelativeCount S D .line 1 5 +
          3 * elevenGammaSixRelativeCount S D .line 2 1 +
          7 * elevenGammaSixRelativeCount S D .line 2 2 <= 52 := by
      omega
    have hendpoint := elevenGammaSix_lowOrdinary_unique_five_endpoint
      S.totalCircleCount
      (elevenGammaSixRelativeCount S D .circle 0 5)
      (elevenGammaSixRelativeCount S D .circle 1 2)
      (elevenGammaSixRelativeCount S D .circle 1 5)
      (elevenGammaSixRelativeCount S D .circle 2 1)
      (elevenGammaSixRelativeCount S D .circle 2 2)
      (elevenGammaSixRelativeCount S D .line 0 5)
      (elevenGammaSixRelativeCount S D .line 1 2)
      (elevenGammaSixRelativeCount S D .line 1 5)
      (elevenGammaSixRelativeCount S D .line 2 1)
      (elevenGammaSixRelativeCount S D .line 2 2)
      rows.circle_le_forty hcircle hN5raw hT1Grouped hT2Grouped hLC hO
        hMelNormalized hK hJ
        hc15 hl05 hc05
    rcases hendpoint with hl15 | hc05
    · exact Or.inl hl15.1
    · rcases hc05 with
        ⟨hc05, _hc15, _hl05, _hl15, _hC, hK27, _hW, _hJlo, _hJhi⟩
      refine Or.inr ⟨hc05, ?_⟩
      simpa only [elevenGammaSixOutsiderThreeBlockIncidence, hc03, hl03,
        mul_zero, zero_add] using hK27

/-- The rich six-line endpoint is impossible below forty-one circles. -/
theorem elevenGammaSix_lowOrdinary_l15_impossible
    {alpha : Type u} [Fintype alpha] [DecidableEq alpha]
    (cfg : Configuration alpha) (hpoint : Fintype.card alpha = 11)
    (gamma : DeterminedCircle cfg)
    (hcount : Erdos506.V4.circleCount cfg <= 40)
    (hl15 : elevenGammaSixRelativeCount (blockSystem cfg)
      (circleTrace cfg gamma.1) .line 1 5 = 1) : False := by
  have hC : (blockSystem cfg).totalCircleCount <= 40 := by
    have hbridge : (blockSystem cfg).totalCircleCount =
        Erdos506.V4.circleCount cfg := by
      rw [totalCircleCount_eq_card_determinedCircle,
        ← Erdos506.V3.circleCount_eq_card_determinedCircle]
    omega
  have hzero := elevenGammaSix_l15_eq_zero_of_circleCount_le_forty
    (blockSystem cfg) (circleTrace cfg gamma.1) hpoint hC
  omega

/-- The outsider five-circle endpoint with total outsider three-block
incidence twenty-seven is excluded by the localized even-arrangement core. -/
theorem elevenGammaSix_lowOrdinary_c05_impossible
    {alpha : Type u} [Fintype alpha] [DecidableEq alpha]
    (EvenArr : RealPlaneEvenArrangementPrinciple.{u})
    (Kelly : RealPlaneKellyMoserPrinciple.{u})
    (cfg : Configuration alpha) (hadm : Admissible cfg)
    (hpoint : Fintype.card alpha = 11)
    (gamma : DeterminedCircle cfg)
    (hgamma : (circleTrace cfg gamma.1).card = 6)
    (hcount : Erdos506.V4.circleCount cfg <= 40)
    (hc05 : elevenGammaSixRelativeCount (blockSystem cfg)
      (circleTrace cfg gamma.1) .circle 0 5 = 1)
    (hK : elevenGammaSixOutsiderThreeBlockIncidence (blockSystem cfg)
      (circleTrace cfg gamma.1) = 27) : False := by
  classical
  let S := blockSystem cfg
  let D : Finset alpha := circleTrace cfg gamma.1
  let X : Finset alpha := Finset.univ \ D
  let gammaBlock : GeometricBlock cfg := Sum.inr gamma
  have hcircleCapGeom : forall c : DeterminedCircle cfg,
      (circleTrace cfg c.1).card <= 6 := by
    intro c
    exact circleTrace_card_le_six_of_eleven_of_circleCount_le
      cfg hadm hpoint hcount c
  have hlineCapGeom : forall L : DeterminedLine cfg,
      (lineSupport cfg L).card <= 6 := by
    intro L
    have hfive := lineSupport_card_le_five_of_eleven_of_circleCount_le
      cfg hadm hpoint hcount L
    omega
  have hX : X.card = 5 := by
    simp [X, D, Finset.card_sdiff_of_subset
      (Finset.subset_univ (circleTrace cfg gamma.1)), hpoint, hgamma]
  have hdisjoint : Disjoint (circleTrace cfg gamma.1) X := by
    simp [X, D, Finset.disjoint_left]
  have hc05' : elevenGammaSixRelativeCount S D .circle 0 5 = 1 := by
    simpa [S, D] using hc05
  obtain ⟨b, _hbKind, hbInside, hbOutside⟩ :=
    elevenGammaSix_exists_relative_block_of_count_eq_one
      S D .circle 0 5 hc05'
  have hsum :=
    elevenGammaSixTotalOutsiderThreeBlockIncidence_eq_sum_complement S D
  have hgrouped :=
    elevenGammaSixTotalOutsiderThreeBlockIncidence_eq_grouped
      S D gammaBlock hgamma rfl
  have hthreeSum : (∑ p ∈ X, S.blockDegree 3 p) = 27 := by
    rw [← hsum, hgrouped]
    simpa [S, D] using hK
  let H : GeometricBlock cfg := b
  have hXsub : X ⊆ S.support b :=
    elevenGammaSix_complement_subset_support_of_outside_five
      S D hpoint hgamma b hbOutside
  have hbCard : (S.support b).card = 5 := by
    have hsplit := elevenGammaSixInside_add_outside S D b
    omega
  have hH : geometricBlockSupport cfg H = X := by
    change S.support b = X
    exact (Finset.eq_of_subset_of_card_le hXsub (by
      rw [hbCard, hX])).symm
  have hblockCap : BlockSizeCap S 6 := by
    intro B _hB
    cases B with
    | inl L => exact hlineCapGeom L
    | inr c => exact hcircleCapGeom c
  exact elevenGammaSix_localized_even_contradiction
    EvenArr Kelly cfg hadm hpoint gamma hgamma X hX hdisjoint H hH
      hblockCap hthreeSum

/-- The low-ordinary branch is impossible. -/
theorem elevenGammaSix_low_ordinary_impossible
    {alpha : Type u} [Fintype alpha] [DecidableEq alpha]
    (Mel : RealPlaneMelchiorPrinciple.{u})
    (EvenArr : RealPlaneEvenArrangementPrinciple.{u})
    (Kelly : RealPlaneKellyMoserPrinciple.{u})
    (cfg : Configuration alpha) (hadm : Admissible cfg)
    (hpoint : Fintype.card alpha = 11)
    (gamma : DeterminedCircle cfg)
    (hgamma : (circleTrace cfg gamma.1).card = 6)
    (hcount : Erdos506.V4.circleCount cfg <= 40)
    (hO : elevenGammaSixOrdinaryCircleIncidence (blockSystem cfg)
      (circleTrace cfg gamma.1) <= 14) : False := by
  have rows := elevenGammaSixLowOrdinaryEventRows_of_configuration
    Mel Kelly cfg hadm hpoint gamma hgamma hcount hO
  rcases elevenGammaSix_lowOrdinary_endpoint_of_rows
      (blockSystem cfg) (circleTrace cfg gamma.1) rows with hl15 | hc05
  · exact elevenGammaSix_lowOrdinary_l15_impossible
      cfg hpoint gamma hcount hl15
  · exact elevenGammaSix_lowOrdinary_c05_impossible
      EvenArr Kelly cfg hadm hpoint gamma hgamma hcount hc05.1 hc05.2

/-- Full configuration-level selected-six-circle branch at eleven points. -/
theorem elevenGammaSix_circleCount_ge_forty_one_of_configuration
    {alpha : Type u} [Fintype alpha] [DecidableEq alpha]
    (Mel : RealPlaneMelchiorPrinciple.{u})
    (EvenArr : RealPlaneEvenArrangementPrinciple.{u})
    (Kelly : RealPlaneKellyMoserPrinciple.{u})
    (cfg : Configuration alpha) (hadm : Admissible cfg)
    (hpoint : Fintype.card alpha = 11)
    (gamma : DeterminedCircle cfg)
    (hgamma : (circleTrace cfg gamma.1).card = 6) :
    41 <= Erdos506.V4.circleCount cfg := by
  by_contra hnot
  have hcount : Erdos506.V4.circleCount cfg <= 40 := by omega
  let S := blockSystem cfg
  let D : Finset alpha := circleTrace cfg gamma.1
  let X : Finset alpha := Finset.univ \ D
  let gammaBlock : GeometricBlock cfg := Sum.inr gamma
  let d : ElevenGammaSixBoundaryData :=
    elevenGammaSixBoundaryDataOfBlockSystem S D
  have hcircleCapGeom : forall c : DeterminedCircle cfg,
      (circleTrace cfg c.1).card <= 6 := by
    intro c
    exact circleTrace_card_le_six_of_eleven_of_circleCount_le
      cfg hadm hpoint hcount c
  have hlineCapGeom : forall L : DeterminedLine cfg,
      (lineSupport cfg L).card <= 6 := by
    intro L
    have hfive := lineSupport_card_le_five_of_eleven_of_circleCount_le
      cfg hadm hpoint hcount L
    omega
  have hblockCapGeom : forall H : GeometricBlock cfg,
      (geometricBlockSupport cfg H).card <= 6 := by
    intro H
    cases H with
    | inl L => exact hlineCapGeom L
    | inr c => exact hcircleCapGeom c
  have hcircleCap : forall b : GeometricBlock cfg,
      S.kind b = .circle -> (S.support b).card <= 6 := by
    intro b hb
    cases b with
    | inl L => cases hb
    | inr c => exact hcircleCapGeom c
  have hlineCap : forall b : GeometricBlock cfg,
      S.kind b = .line -> (S.support b).card <= 6 := by
    intro b hb
    cases b with
    | inl L => exact hlineCapGeom L
    | inr c => cases hb
  have hordinary : 15 <= elevenGammaSixOrdinaryCircleIncidence S D := by
    by_contra hsmallNot
    have hsmall : elevenGammaSixOrdinaryCircleIncidence S D <= 14 := by omega
    exact elevenGammaSix_low_ordinary_impossible
      Mel EvenArr Kelly cfg hadm hpoint gamma hgamma hcount
        (by simpa [S, D] using hsmall)
  have hmelchior : elevenGammaSixLineMelchiorUsed S D <= 52 := by
    simpa [S, D] using
      elevenGammaSixLineMelchiorUsed_le_fifty_two
        Mel cfg hadm hpoint gamma hgamma hlineCapGeom
  have hweight : elevenGammaSixWeight S D <= 28 := by
    simpa [S, D] using
      elevenGammaSixWeight_le_twenty_eight
        cfg gamma hpoint hgamma hcircleCapGeom
  have hlargeLines : elevenGammaSixLargeLineFootprintWeight S D <= 2 :=
    elevenGammaSixLargeLineFootprintWeight_le_two
      S D gammaBlock hpoint hgamma rfl rfl hlineCap
  have hfront : ElevenGammaSixFrontConditions
      (elevenGammaSixFrontDataOfBlockSystem S D) :=
    elevenGammaSixFrontConditions_of_blockSystem
      S D gammaBlock hpoint hgamma rfl rfl hcircleCap hlineCap
        hordinary hmelchior hweight hlargeLines
  have hkelly :
      25 <= elevenGammaSixOutsiderThreeBlockIncidence S D := by
    simpa [S, D] using
      twenty_five_le_elevenGammaSixOutsiderThreeBlockIncidence
        Kelly cfg hadm hpoint gamma hgamma
  have hhosts : ElevenGammaSixHostClassification d := by
    change ElevenGammaSixHostClassification
      (elevenGammaSixBoundaryDataOfBlockSystem S D)
    exact elevenGammaSixHostClassification_of_materializedCensus
      S D gammaBlock hpoint hgamma rfl rfl hcircleCap hlineCap
        hordinary hkelly hfront
  have hlineCapacity : elevenGammaSixLineCapacityUsed S D <= 30 :=
    elevenGammaSixLineCapacityUsed_le_thirty
      S D gammaBlock hpoint hgamma rfl rfl hlineCap
  have hrows : ElevenGammaSixBoundaryRows d := by
    change ElevenGammaSixBoundaryRows
      (elevenGammaSixBoundaryDataOfBlockSystem S D)
    exact elevenGammaSixBoundaryRows_of_materializedCensus
      S D hlineCapacity hmelchior hweight hhosts
  have hgeo : ElevenGammaSixGeometricEventWitness cfg gamma X d := by
    simpa [S, D, X, d] using
      elevenGammaSixGeometricEventWitness_of_configuration
        cfg gamma hpoint hgamma hcircleCapGeom hlineCapGeom
  have hcanonical : d = elevenGammaSixBoundaryDataOfBlockSystem
      (blockSystem cfg) (circleTrace cfg gamma.1) := by
    rfl
  have hevents : ElevenGammaSixEventBounds d := by
    exact elevenGammaSixEventBounds_of_geometry
      cfg gamma X d hblockCapGeom hgeo
  have hresult : 41 <= d.front.C :=
    elevenGammaSix_circleCount_ge_forty_one
      EvenArr Kelly cfg hadm hpoint gamma hgamma hcircleCapGeom hlineCapGeom
        d hcanonical hgeo hfront hrows hevents
  change 41 <= S.totalCircleCount at hresult
  have hbridge : S.totalCircleCount = Erdos506.V4.circleCount cfg := by
    dsimp only [S]
    rw [totalCircleCount_eq_card_determinedCircle,
      ← Erdos506.V3.circleCount_eq_card_determinedCircle]
  rw [hbridge] at hresult
  exact hnot hresult

end Erdos506.V1
