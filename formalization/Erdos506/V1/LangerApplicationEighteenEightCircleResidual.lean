import Erdos506.V1.LangerApplicationSeventeenEightCircleResidual

/-!
# The lossless eighteen--eight rich-circle residual

Deleting two outsiders preserves the selected eight-circle, but the present
deletion API only gives monotonicity of the circle count.  In particular the
checked `(16,8)` endpoint yields `99 ≤ C` after a double deletion, with no
available averaging identity that recovers the missing thirty circles.

This file instead records every loss in the corrected ten-centre pencil.
The resulting seam is the exact simultaneous chord/centre inequality needed
at `(18,8)`; no deletion loss is hidden in a callback.
-/

namespace Erdos506.V1

open Erdos506.Block
open Erdos506.Block.BlockSystem
open Erdos506.Finite
open Erdos506.Incidence
open Erdos506.V4
open scoped BigOperators

universe u

variable {alpha : Type u} [Fintype alpha] [DecidableEq alpha]

noncomputable def eighteenEightFanSum
    (cfg : Configuration alpha) (b : GeometricBlock cfg) : Nat :=
  ∑ x : BlockOutsider (blockSystem cfg) b,
    (circlePencil (blockSystem cfg) b x).card

noncomputable def eighteenEightLinePairSum
    (cfg : Configuration alpha) (b : GeometricBlock cfg) : Nat :=
  ∑ x : BlockOutsider (blockSystem cfg) b,
    (lineBasePairs (blockSystem cfg) b x).card

noncomputable def eighteenEightPairMoment
    (cfg : Configuration alpha) (b : GeometricBlock cfg) : Nat :=
  distinguishedPairMoment
    (Finset.univ : Finset (BlockOutsider (blockSystem cfg) b))
    (circlePencil (blockSystem cfg) b)

noncomputable def eighteenEightOutsiderCircleBlocks
    (cfg : Configuration alpha) (b : GeometricBlock cfg) :
    Finset (GeometricBlock cfg) :=
  finsetRestrictionCircleBlocks cfg
    (blockOutsiders (blockSystem cfg) b)

noncomputable def eighteenEightCoveredCircles
    (cfg : Configuration alpha) (b : GeometricBlock cfg) :
    Finset (GeometricBlock cfg) :=
  (Finset.univ.biUnion (circlePencil (blockSystem cfg) b)) ∪
    eighteenEightOutsiderCircleBlocks cfg b

/-- Every literal loss in the corrected `(18,8)` pencil. -/
structure EighteenEightCirclePencilResidualData
    (cfg : Configuration alpha) (b : GeometricBlock cfg) : Prop where
  outsider_admissible :
    Admissible (finsetRestrictionConfiguration cfg
      (blockOutsiders (blockSystem cfg) b))
  fan_sum_lower : 240 ≤ eighteenEightFanSum cfg b
  outsider_count_lower :
    33 ≤ (eighteenEightOutsiderCircleBlocks cfg b).card
  pair_moment_upper : eighteenEightPairMoment cfg b ≤ 180
  covered_add_one_le :
    (eighteenEightCoveredCircles cfg b).card + 1 ≤
      (blockSystem cfg).totalCircleCount
  total_count_upper : (blockSystem cfg).totalCircleCount ≤ 128
  slack_le_thirty_four :
    (eighteenEightFanSum cfg b - 240) +
      ((eighteenEightOutsiderCircleBlocks cfg b).card - 33) +
      (180 - eighteenEightPairMoment cfg b) +
      ((blockSystem cfg).totalCircleCount - 1 -
        (eighteenEightCoveredCircles cfg b).card) +
      (128 - (blockSystem cfg).totalCircleCount) ≤ 34

theorem EighteenEightCirclePencilResidualData.outsider_chord_slack_le_thirty_four
    {cfg : Configuration alpha} {b : GeometricBlock cfg}
    (R : EighteenEightCirclePencilResidualData cfg b) :
    (eighteenEightFanSum cfg b - 240) +
      ((eighteenEightOutsiderCircleBlocks cfg b).card - 33) +
      (180 - eighteenEightPairMoment cfg b) ≤ 34 := by
  omega

theorem eighteenEight_linePairMoment_add_circlePairMoment_le
    (cfg : Configuration alpha) (b : GeometricBlock cfg)
    (h18 : Fintype.card alpha = 18)
    (height : (geometricBlockSupport cfg b).card = 8) :
    distinguishedPairMoment
        (Finset.univ : Finset (BlockOutsider (blockSystem cfg) b))
        (lineBasePairs (blockSystem cfg) b) +
      eighteenEightPairMoment cfg b ≤ 180 := by
  classical
  let S := blockSystem cfg
  let I : Finset (BlockOutsider S b) := Finset.univ
  have hpair := add_distinguishedPairMoment_le_of_pair_cap I
    (lineBasePairs S b) (circlePencil S b) 4 (by
      intro x _hx y _hy hxy
      simpa [commonPencils, Nat.add_comm] using
        (card_commonPencils_add_inter_lineBasePairs_le_four
          S b height x y hxy))
  have hIcard : I.card = 10 := by
    dsimp only [I]
    rw [Finset.card_univ, Fintype.card_coe, card_blockOutsiders,
      h18, height]
  change distinguishedPairMoment I (lineBasePairs S b) +
    distinguishedPairMoment I (circlePencil S b) ≤ 180
  rw [hIcard] at hpair
  norm_num [Nat.choose] at hpair ⊢
  exact hpair

theorem eighteenEightLinePairSum_add_fanSum
    (cfg : Configuration alpha) (b : GeometricBlock cfg)
    (h18 : Fintype.card alpha = 18)
    (height : (geometricBlockSupport cfg b).card = 8) :
    eighteenEightLinePairSum cfg b + eighteenEightFanSum cfg b = 280 := by
  let S := blockSystem cfg
  have hpoint (x : BlockOutsider S b) :
      (lineBasePairs S b x).card + (circlePencil S b x).card = 28 := by
    rw [card_circlePencil]
    have hpart := card_circleBasePairs_add_card_lineBasePairs S b x
    change (S.support b).card = 8 at height
    rw [height] at hpart
    norm_num [Nat.choose] at hpart ⊢
    omega
  unfold eighteenEightLinePairSum eighteenEightFanSum
  rw [← Finset.sum_add_distrib]
  calc
    (∑ x : BlockOutsider S b,
        ((lineBasePairs S b x).card + (circlePencil S b x).card)) =
        ∑ _x : BlockOutsider S b, 28 := by
      apply Fintype.sum_congr
      exact hpoint
    _ = 280 := by
      rw [Fintype.sum_const, Fintype.card_coe, card_blockOutsiders]
      rw [h18, height]
      norm_num

/-- The line-pair complement consumes twelve units before any real-circle
geometry is used. -/
theorem EighteenEightCirclePencilResidualData.core_slack_lower_twelve
    {cfg : Configuration alpha} {b : GeometricBlock cfg}
    (_R : EighteenEightCirclePencilResidualData cfg b)
    (h18 : Fintype.card alpha = 18)
    (height : (geometricBlockSupport cfg b).card = 8) :
    12 ≤ (eighteenEightFanSum cfg b - 240) +
      (180 - eighteenEightPairMoment cfg b) := by
  classical
  let S := blockSystem cfg
  let I : Finset (BlockOutsider S b) := Finset.univ
  let L := lineBasePairs S b
  have hbon : (∑ x ∈ I, (L x).card) ≤
      (I.biUnion L).card + distinguishedPairMoment I L := by
    have h := sum_family_card_add_distinguished_le I L
      (∅ : Finset (BlockBasePair S b)) (by simp)
    simpa using h
  have hunion : (I.biUnion L).card ≤ 28 := by
    have hsub := Finset.card_le_card
      (show I.biUnion L ⊆
        (Finset.univ : Finset (BlockBasePair S b)) from
          Finset.subset_univ _)
    have huniv :
        (Finset.univ : Finset (BlockBasePair S b)).card = 28 := by
      rw [Finset.card_univ, Fintype.card_coe,
        Finset.card_powersetCard, height]
      norm_num [Nat.choose]
    rw [huniv] at hsub
    exact hsub
  have hpartition := eighteenEightLinePairSum_add_fanSum
    cfg b h18 height
  change (∑ x ∈ I, (L x).card) + eighteenEightFanSum cfg b = 280
    at hpartition
  have hpairs := eighteenEight_linePairMoment_add_circlePairMoment_le
    cfg b h18 height
  change distinguishedPairMoment I L +
    eighteenEightPairMoment cfg b ≤ 180 at hpairs
  omega

private theorem eighteenEight_restrictionCircle_degree_ge_three
    (cfg : Configuration alpha) (b d : GeometricBlock cfg)
    (hdD : d ∈ eighteenEightOutsiderCircleBlocks cfg b)
    (hdU : d ∈ (Finset.univ :
      Finset (BlockOutsider (blockSystem cfg) b)).biUnion
        (circlePencil (blockSystem cfg) b)) :
    3 ≤ ((Finset.univ : Finset (BlockOutsider (blockSystem cfg) b)).filter
      fun x => d ∈ circlePencil (blockSystem cfg) b x).card := by
  classical
  let S := blockSystem cfg
  let O := blockOutsiders S b
  dsimp only [eighteenEightOutsiderCircleBlocks,
    finsetRestrictionCircleBlocks] at hdD
  obtain ⟨c, _hc, rfl⟩ := Finset.mem_image.mp hdD
  let C := liftFinsetRestrictionDeterminedCircle cfg O c
  have hinterBase :
      (S.support (Sum.inr C) ∩ S.support b).card = 2 := by
    rcases Finset.mem_biUnion.mp hdU with ⟨x, _hx, hxFan⟩
    obtain ⟨p, _hp, howner⟩ := mem_circlePencil.mp hxFan
    rw [← howner, pencilOwner_inter_base S b x p]
    exact (Finset.mem_powersetCard.mp p.2).2
  have htraceSub :
      circleTrace (finsetRestrictionConfiguration cfg O) c.1 ⊆
        (Finset.univ : Finset (BlockOutsider S b)).filter
          fun x => (Sum.inr C : GeometricBlock cfg) ∈ circlePencil S b x := by
    intro x hx
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ x, ?_⟩
    apply mem_circlePencil_of_kind_circle_of_inter_card_two
      S b x (Sum.inr C)
    · rfl
    · change x.1 ∈ circleTrace cfg C.1
      exact (mem_circleTrace_finsetRestriction_iff cfg O c.1 x).mp hx
    · exact hinterBase
  have hthree := Erdos506.V3.circleSupport_card_ge_three
    (finsetRestrictionConfiguration cfg O) c
  exact hthree.trans (Finset.card_le_card htraceSub)

private theorem eighteenEight_base_not_mem_circlePencil_union
    (cfg : Configuration alpha) (b : GeometricBlock cfg) :
    b ∉ (Finset.univ :
      Finset (BlockOutsider (blockSystem cfg) b)).biUnion
        (circlePencil (blockSystem cfg) b) := by
  classical
  intro hbU
  rcases Finset.mem_biUnion.mp hbU with ⟨x, _hx, hbFan⟩
  obtain ⟨p, _hp, howner⟩ := mem_circlePencil.mp hbFan
  exact pencilOwner_ne_base (blockSystem cfg) b x p howner

private theorem eighteenEight_base_not_mem_outsiderCircleBlocks
    (cfg : Configuration alpha) (b : GeometricBlock cfg) :
    b ∉ eighteenEightOutsiderCircleBlocks cfg b := by
  classical
  let S := blockSystem cfg
  let O := blockOutsiders S b
  intro hbD
  dsimp only [eighteenEightOutsiderCircleBlocks,
    finsetRestrictionCircleBlocks] at hbD
  obtain ⟨c, _hc, hcb⟩ := Finset.mem_image.mp hbD
  have htraceThree := Erdos506.V3.circleSupport_card_ge_three
    (finsetRestrictionConfiguration cfg O) c
  obtain ⟨x, hx⟩ := Finset.exists_mem_of_ne_empty (by
    intro hempty
    rw [hempty] at htraceThree
    simp at htraceThree)
  have hxAmbient :=
    (mem_circleTrace_finsetRestriction_iff cfg O c.1 x).mp hx
  let C := liftFinsetRestrictionDeterminedCircle cfg O c
  have hsupportEq : S.support (Sum.inr C) = S.support b :=
    congrArg S.support hcb
  apply (mem_blockOutsiders.mp x.2)
  rw [← hsupportEq]
  change x.1 ∈ circleTrace cfg C.1
  exact hxAmbient

theorem eighteenEight_exact_cover
    (cfg : Configuration alpha) (b : GeometricBlock cfg)
    (hcircle : (blockSystem cfg).kind b = .circle) :
    eighteenEightFanSum cfg b +
        (eighteenEightOutsiderCircleBlocks cfg b).card ≤
      (eighteenEightCoveredCircles cfg b).card +
        eighteenEightPairMoment cfg b ∧
    (eighteenEightCoveredCircles cfg b).card + 1 ≤
      (blockSystem cfg).totalCircleCount := by
  classical
  let S := blockSystem cfg
  let I : Finset (BlockOutsider S b) := Finset.univ
  let F := circlePencil S b
  let D := eighteenEightOutsiderCircleBlocks cfg b
  let U := I.biUnion F
  have hmaster := sum_family_card_add_distinguished_le I F D (by
    intro d hdD hdU
    exact eighteenEight_restrictionCircle_degree_ge_three
      cfg b d hdD hdU)
  have hcoveredSub : insert b (U ∪ D) ⊆ S.blocksOfKind .circle := by
    intro e he
    rcases Finset.mem_insert.mp he with rfl | he
    · exact S.mem_blocksOfKind.mpr hcircle
    · rcases Finset.mem_union.mp he with heU | heD
      · rcases Finset.mem_biUnion.mp heU with ⟨x, _hx, hxFan⟩
        exact S.mem_blocksOfKind.mpr (circlePencil_kind S b x hxFan)
      · dsimp only [D, eighteenEightOutsiderCircleBlocks,
          finsetRestrictionCircleBlocks] at heD
        obtain ⟨c, _hc, rfl⟩ := Finset.mem_image.mp heD
        exact S.mem_blocksOfKind.mpr rfl
  have hbnot : b ∉ U ∪ D := by
    rw [Finset.mem_union, not_or]
    exact ⟨eighteenEight_base_not_mem_circlePencil_union cfg b,
      eighteenEight_base_not_mem_outsiderCircleBlocks cfg b⟩
  have hcardSub := Finset.card_le_card hcoveredSub
  rw [Finset.card_insert_of_notMem hbnot] at hcardSub
  change (U ∪ D).card + 1 ≤ S.totalCircleCount at hcardSub
  change (∑ x ∈ I, (F x).card) + D.card ≤
    (U ∪ D).card + distinguishedPairMoment I F at hmaster
  exact ⟨hmaster, hcardSub⟩

private theorem eighteenEight_fan_moment_bounds
    (cfg : Configuration alpha) (b : GeometricBlock cfg)
    (h18 : Fintype.card alpha = 18)
    (height : (geometricBlockSupport cfg b).card = 8) :
    240 ≤ eighteenEightFanSum cfg b ∧
      eighteenEightPairMoment cfg b ≤ 180 := by
  classical
  let S := blockSystem cfg
  let I : Finset (BlockOutsider S b) := Finset.univ
  let F := circlePencil S b
  have hIcard : I.card = 10 := by
    dsimp only [I]
    rw [Finset.card_univ, Fintype.card_coe, card_blockOutsiders,
      h18, height]
  have hFcard : ∀ x ∈ I, 24 ≤ (F x).card := by
    intro x _hx
    dsimp only [F]
    rw [card_circlePencil]
    have h := card_circleBasePairs_lower S b x
    change (S.support b).card = 8 at height
    rw [height] at h
    norm_num [Nat.choose] at h ⊢
    exact h
  have hfan : 240 ≤ ∑ x ∈ I, (F x).card := by
    calc
      240 = ∑ _x ∈ I, 24 := by simp [hIcard]
      _ ≤ _ := Finset.sum_le_sum hFcard
  have hinter : ∀ x ∈ I, ∀ y ∈ I, x ≠ y →
      (F x ∩ F y).card ≤ 4 := by
    intro x _hx y _hy hxy
    dsimp only [F]
    have h := card_commonPencils_le_half S b x y hxy
    rw [height] at h
    norm_num at h ⊢
    exact h
  have hmoment := distinguishedPairMoment_le I F 4 hinter
  rw [hIcard] at hmoment
  norm_num [Nat.choose] at hmoment
  exact ⟨hfan, hmoment⟩

private theorem eighteenEight_outsider_data
    (Mel : RealPlaneMelchiorPrinciple.{u})
    (EvenArr : RealPlaneEvenArrangementPrinciple.{u})
    (Cross : RealPlaneRadicalAxisCrossBlockPrinciple.{u})
    (Kelly : RealPlaneKellyMoserPrinciple.{u})
    (U17 : RealPlaneSixCircleU17Principle.{u})
    (Geometry : RealPlaneTenFiveGeometry.{u})
    (cfg : Configuration alpha) (hadm : Admissible cfg)
    (b : GeometricBlock cfg)
    (h18 : Fintype.card alpha = 18)
    (height : (geometricBlockSupport cfg b).card = 8)
    (hcount : Erdos506.V4.circleCount cfg <
      Erdos506.v1UniformTarget (Fintype.card alpha)) :
    Admissible (finsetRestrictionConfiguration cfg
      (blockOutsiders (blockSystem cfg) b)) ∧
    33 ≤ (eighteenEightOutsiderCircleBlocks cfg b).card := by
  classical
  let S := blockSystem cfg
  let O := blockOutsiders S b
  let Q := finsetRestrictionConfiguration cfg O
  have hOcard : O.card = 10 := by
    dsimp only [O]
    rw [card_blockOutsiders, h18, height]
  have hQcard : Fintype.card (BlockOutsider S b) = 10 := by
    rw [Fintype.card_coe, hOcard]
  have hcap : BlockSizeCap S 9 := by
    have hhalf := halfBlockCap_of_circleCount_lt_v1UniformTarget
      cfg hadm (by omega) hcount
    rw [h18] at hhalf
    norm_num at hhalf
    exact hhalf
  have hQadm : Admissible Q := by
    exact admissible_finsetRestriction_blockOutsiders_of_cap
      cfg b 9 (by omega) hcap (by
        change 9 < O.card
        omega)
  have hQlower : 33 ≤ Erdos506.V4.circleCount Q :=
    circleCount_ge_thirty_three_of_card_ten
      Mel EvenArr Cross Kelly U17 Geometry Q hQadm hQcard
  have hDcard : (eighteenEightOutsiderCircleBlocks cfg b).card =
      Erdos506.V4.circleCount Q := by
    dsimp only [eighteenEightOutsiderCircleBlocks, Q, O]
    exact card_finsetRestrictionCircleBlocks cfg _
  exact ⟨hQadm, by rw [hDcard]; exact hQlower⟩

/-- Configuration-level extraction of the complete thirty-four-unit
`(18,8)` residual. -/
theorem FiniteWindowRichBlockResidual.eighteen_eight_circle_residual
    (Mel : RealPlaneMelchiorPrinciple.{u})
    (EvenArr : RealPlaneEvenArrangementPrinciple.{u})
    (Cross : RealPlaneRadicalAxisCrossBlockPrinciple.{u})
    (Kelly : RealPlaneKellyMoserPrinciple.{u})
    (U17 : RealPlaneSixCircleU17Principle.{u})
    (Geometry : RealPlaneTenFiveGeometry.{u})
    {cfg : Configuration alpha} (R : FiniteWindowRichBlockResidual cfg)
    (hadm : Admissible cfg)
    (hcircle : (blockSystem cfg).kind R.block = .circle)
    (h18 : Fintype.card alpha = 18)
    (height : (geometricBlockSupport cfg R.block).card = 8)
    (hcount : Erdos506.V4.circleCount cfg <
      Erdos506.v1UniformTarget (Fintype.card alpha)) :
    EighteenEightCirclePencilResidualData cfg R.block := by
  let S := blockSystem cfg
  let D := eighteenEightOutsiderCircleBlocks cfg R.block
  let U := eighteenEightCoveredCircles cfg R.block
  obtain ⟨hQadm, hDlower⟩ := eighteenEight_outsider_data
    Mel EvenArr Cross Kelly U17 Geometry cfg hadm R.block
      h18 height hcount
  obtain ⟨hfan, hmoment⟩ :=
    eighteenEight_fan_moment_bounds cfg R.block h18 height
  obtain ⟨hmaster, hcovered⟩ :=
    eighteenEight_exact_cover cfg R.block hcircle
  have htotal : S.totalCircleCount ≤ 128 := by
    rw [totalCircleCount_eq_card_determinedCircle,
      ← Erdos506.V3.circleCount_eq_card_determinedCircle]
    rw [h18] at hcount
    norm_num [Erdos506.v1UniformTarget, Nat.choose] at hcount ⊢
    omega
  have hslack :
      (eighteenEightFanSum cfg R.block - 240) +
        (D.card - 33) +
        (180 - eighteenEightPairMoment cfg R.block) +
        (S.totalCircleCount - 1 - U.card) +
        (128 - S.totalCircleCount) ≤ 34 := by
    dsimp only [D, U] at hmaster hcovered hDlower ⊢
    omega
  refine ⟨hQadm, hfan, ?_, hmoment, ?_, htotal, ?_⟩
  · change 33 ≤ D.card
    exact hDlower
  · change U.card + 1 ≤ S.totalCircleCount
    exact hcovered
  · change
      (eighteenEightFanSum cfg R.block - 240) +
        (D.card - 33) +
        (180 - eighteenEightPairMoment cfg R.block) +
        (S.totalCircleCount - 1 - U.card) +
        (128 - S.totalCircleCount) ≤ 34
    exact hslack

/-- The exact remaining `(18,8)` seam.  Pure finite pair packing supplies
twelve of the required thirty-five units; a real simultaneous-centre theorem
must supply the remaining twenty-three units among these same literal
defects. -/
theorem FiniteWindowRichBlockResidual.circle_impossible_of_eighteen_eight_of_outsiderChordGap
    (Mel : RealPlaneMelchiorPrinciple.{u})
    (EvenArr : RealPlaneEvenArrangementPrinciple.{u})
    (Cross : RealPlaneRadicalAxisCrossBlockPrinciple.{u})
    (Kelly : RealPlaneKellyMoserPrinciple.{u})
    (U17 : RealPlaneSixCircleU17Principle.{u})
    (Geometry : RealPlaneTenFiveGeometry.{u})
    {cfg : Configuration alpha} (R : FiniteWindowRichBlockResidual cfg)
    (hadm : Admissible cfg)
    (hcircle : (blockSystem cfg).kind R.block = .circle)
    (h18 : Fintype.card alpha = 18)
    (height : (geometricBlockSupport cfg R.block).card = 8)
    (hcount : Erdos506.V4.circleCount cfg <
      Erdos506.v1UniformTarget (Fintype.card alpha))
    (hgap :
      35 ≤ (eighteenEightFanSum cfg R.block - 240) +
        ((eighteenEightOutsiderCircleBlocks cfg R.block).card - 33) +
        (180 - eighteenEightPairMoment cfg R.block)) : False := by
  have E := R.eighteen_eight_circle_residual
    Mel EvenArr Cross Kelly U17 Geometry hadm hcircle h18 height hcount
  have := E.outsider_chord_slack_le_thirty_four
  omega

end Erdos506.V1
