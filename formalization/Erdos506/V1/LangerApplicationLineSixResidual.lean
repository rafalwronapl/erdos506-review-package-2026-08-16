import Erdos506.V1.LangerApplicationOutsiderCirclePencilFinish
import Erdos506.V1.Eight

/-!
# The two rich-line size-six residuals

The induced outsider configurations give a genuine additive correction to
the rich-line pencil, but do not by themselves reach the V1 target.  This
module records the resulting lossless numerical intervals rather than
claiming a false endpoint.
-/

namespace Erdos506.V1

open Erdos506.Block
open Erdos506.Block.BlockSystem
open Erdos506.Incidence
open Erdos506.V4

universe u

variable {alpha : Type u} [Fintype alpha] [DecidableEq alpha]

/-- A fifteen-point counterexample with a selected six-line still has at
least fifty-two circles: twenty-seven from the corrected rich-line pencil
and twenty-five from the induced nine-outsider configuration. -/
theorem FiniteWindowRichBlockResidual.fifteen_six_line_circleCount_ge_fifty_two
    (Mel : RealPlaneMelchiorPrinciple.{u})
    (EvenArr : RealPlaneEvenArrangementPrinciple.{u})
    (Cross : RealPlaneRadicalAxisCrossBlockPrinciple.{u})
    {cfg : Configuration alpha} (R : FiniteWindowRichBlockResidual cfg)
    (hadm : Admissible cfg)
    (hline : (blockSystem cfg).kind R.block = .line)
    (h15 : Fintype.card alpha = 15)
    (hsix : (geometricBlockSupport cfg R.block).card = 6)
    (hcount : Erdos506.V4.circleCount cfg <
      Erdos506.v1UniformTarget (Fintype.card alpha)) :
    52 <= Erdos506.V4.circleCount cfg := by
  let S := blockSystem cfg
  let O := blockOutsiders S R.block
  let Q := finsetRestrictionConfiguration cfg O
  change (S.support R.block).card = 6 at hsix
  have hcap := halfBlockCap_of_circleCount_lt_v1UniformTarget
    cfg hadm (by omega) hcount
  have hcapSeven : BlockSizeCap S 7 := by
    rw [h15] at hcap
    norm_num at hcap
    exact hcap
  have hOcard : O.card = 9 := by
    dsimp only [O]
    rw [card_blockOutsiders, h15, hsix]
  have hQcard : Fintype.card (BlockOutsider S R.block) = 9 := by
    rw [Fintype.card_coe, hOcard]
  have hQadm : Admissible Q := by
    have hlargeO : 7 < O.card := by
      rw [hOcard]
      omega
    exact admissible_finsetRestriction_blockOutsiders_of_cap
      cfg R.block 7 (by omega) hcapSeven (by simpa [O] using hlargeO)
  have hQcount : 25 <= Erdos506.V4.circleCount Q :=
    circleCount_ge_twenty_five_of_card_nine
      Mel EvenArr Cross Q hQadm hQcard
  have hcorrect := richLinePencilNumerator_add_outsiderCircleCount_le
    cfg R.block hline
  rw [totalCircleCount_eq_card_determinedCircle,
    ← Erdos506.V3.circleCount_eq_card_determinedCircle] at hcorrect
  have hgsix : (geometricBlockSupport cfg R.block).card = 6 := by
    simpa [S] using hsix
  rw [h15, hgsix] at hcorrect
  change 9 * Nat.choose 6 2 + Erdos506.V4.circleCount Q ≤
      Erdos506.V4.circleCount cfg + Nat.choose 9 2 * 3 at hcorrect
  norm_num [Nat.choose] at hcorrect
  omega

/-- Exact honest numerical residue left by the outsider correction in the
`(15,6)` line case.  Reaching the target `85` requires thirty-three further
units beyond the certified lower bound `52`. -/
theorem FiniteWindowRichBlockResidual.fifteen_six_line_residual_interval
    (Mel : RealPlaneMelchiorPrinciple.{u})
    (EvenArr : RealPlaneEvenArrangementPrinciple.{u})
    (Cross : RealPlaneRadicalAxisCrossBlockPrinciple.{u})
    {cfg : Configuration alpha} (R : FiniteWindowRichBlockResidual cfg)
    (hadm : Admissible cfg)
    (hline : (blockSystem cfg).kind R.block = .line)
    (h15 : Fintype.card alpha = 15)
    (hsix : (geometricBlockSupport cfg R.block).card = 6)
    (hcount : Erdos506.V4.circleCount cfg <
      Erdos506.v1UniformTarget (Fintype.card alpha)) :
    52 <= Erdos506.V4.circleCount cfg ∧
      Erdos506.V4.circleCount cfg <= 84 := by
  refine ⟨R.fifteen_six_line_circleCount_ge_fifty_two
    Mel EvenArr Cross hadm hline h15 hsix hcount, ?_⟩
  rw [h15] at hcount
  norm_num [Erdos506.v1UniformTarget, Nat.choose] at hcount
  omega

/-- For a fourteen-point counterexample with a selected six-line, the
eight-outsider configuration contributes its seventeen circles to the
rich-line pencil bound, giving the unconditional lower bound fifty-three. -/
theorem FiniteWindowRichBlockResidual.fourteen_six_line_circleCount_ge_fifty_three
    (Mel : RealPlaneMelchiorPrinciple.{u})
    (EvenArr : RealPlaneEvenArrangementPrinciple.{u})
    {cfg : Configuration alpha} (R : FiniteWindowRichBlockResidual cfg)
    (hadm : Admissible cfg)
    (hline : (blockSystem cfg).kind R.block = .line)
    (h14 : Fintype.card alpha = 14)
    (hsix : (geometricBlockSupport cfg R.block).card = 6)
    (hcount : Erdos506.V4.circleCount cfg <
      Erdos506.v1UniformTarget (Fintype.card alpha)) :
    53 <= Erdos506.V4.circleCount cfg := by
  let S := blockSystem cfg
  let O := blockOutsiders S R.block
  let Q := finsetRestrictionConfiguration cfg O
  change (S.support R.block).card = 6 at hsix
  have hcount72 : Erdos506.V4.circleCount cfg <= 72 := by
    rw [h14] at hcount
    norm_num [Erdos506.v1UniformTarget, Nat.choose] at hcount
    omega
  have hnoSeven : NoSevenCircle cfg := by
    intro c hc
    exact no_seven_circle_of_fourteen_of_circleCount_le
      Mel cfg hadm h14 hcount72 c hc
  have hcapSix : BlockSizeCap S 6 := by
    exact blockSizeCap_six_of_fourteen_of_circleCount_le
      cfg hadm h14 hcount72 hnoSeven
  have hOcard : O.card = 8 := by
    dsimp only [O]
    rw [card_blockOutsiders, h14, hsix]
  have hQcard : Fintype.card (BlockOutsider S R.block) = 8 := by
    rw [Fintype.card_coe, hOcard]
  have hQadm : Admissible Q := by
    have hlargeO : 6 < O.card := by
      rw [hOcard]
      omega
    exact admissible_finsetRestriction_blockOutsiders_of_cap
      cfg R.block 6 (by omega) hcapSix (by simpa [O] using hlargeO)
  have hQcount : 17 <= Erdos506.V4.circleCount Q :=
    circleCount_ge_target_of_card_eight
      Mel EvenArr Q hQadm hQcard
  have hcorrect := richLinePencilNumerator_add_outsiderCircleCount_le
    cfg R.block hline
  rw [totalCircleCount_eq_card_determinedCircle,
    ← Erdos506.V3.circleCount_eq_card_determinedCircle] at hcorrect
  have hgsix : (geometricBlockSupport cfg R.block).card = 6 := by
    simpa [S] using hsix
  rw [h14, hgsix] at hcorrect
  change 8 * Nat.choose 6 2 + Erdos506.V4.circleCount Q ≤
      Erdos506.V4.circleCount cfg + Nat.choose 8 2 * 3 at hcorrect
  norm_num [Nat.choose] at hcorrect
  omega

/-- Exact numerical residue left by this method in the `(14,6)` line case.
The V1 target is `73`, twenty units above the certified lower bound `53`. -/
theorem FiniteWindowRichBlockResidual.fourteen_six_line_residual_interval
    (Mel : RealPlaneMelchiorPrinciple.{u})
    (EvenArr : RealPlaneEvenArrangementPrinciple.{u})
    {cfg : Configuration alpha} (R : FiniteWindowRichBlockResidual cfg)
    (hadm : Admissible cfg)
    (hline : (blockSystem cfg).kind R.block = .line)
    (h14 : Fintype.card alpha = 14)
    (hsix : (geometricBlockSupport cfg R.block).card = 6)
    (hcount : Erdos506.V4.circleCount cfg <
      Erdos506.v1UniformTarget (Fintype.card alpha)) :
    53 <= Erdos506.V4.circleCount cfg ∧
      Erdos506.V4.circleCount cfg <= 72 := by
  refine ⟨R.fourteen_six_line_circleCount_ge_fifty_three
    Mel EvenArr hadm hline h14 hsix hcount, ?_⟩
  rw [h14] at hcount
  norm_num [Erdos506.v1UniformTarget, Nat.choose] at hcount
  omega

end Erdos506.V1
