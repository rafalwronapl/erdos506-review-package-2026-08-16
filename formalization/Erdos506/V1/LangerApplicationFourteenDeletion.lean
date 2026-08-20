import Erdos506.V1.LangerApplicationFourteenSixResidual
import Erdos506.V1.Deletion
import Erdos506.V1.ThirteenFull

/-!
# A deletion row for the fourteen-point Langer residual

The completed thirteen-point theorem can be applied after deleting any
label once the residual block cap is retained.  This file isolates that
transfer from the lighter finite-window router.
-/

namespace Erdos506.V1

open Erdos506.Block
open Erdos506.Block.BlockSystem
open Erdos506.Incidence
open Erdos506.V4

universe u

/-- A line cap strictly below the deletion cardinality prevents the
remaining configuration from becoming collinear. -/
theorem deletePointConfiguration_noncollinear_of_line_cap_lt
    {α : Type u} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (p : α)
    (hAway : 1 < Fintype.card (AwayFrom p))
    (hlineCap : ∀ L : DeterminedLine cfg,
      (lineSupport cfg L).card < Fintype.card (AwayFrom p)) :
    Noncollinear (deletePointConfiguration cfg p) := by
  classical
  intro hcol
  obtain ⟨a, b, hab⟩ := Fintype.exists_pair_of_one_lt_card hAway
  have hab' : a.1 ≠ b.1 := by
    intro heq
    exact hab (Subtype.ext heq)
  let A : KSubset α 2 := ⟨{a.1, b.1}, by simp [hab']⟩
  let L : DeterminedLine cfg :=
    ⟨lineOfPair cfg A, lineOfPair_mem_determinedLines cfg A⟩
  have haRange : deletePointConfiguration cfg p a ∈
      pointSet (deletePointConfiguration cfg p) := ⟨a, rfl⟩
  have hbRange : deletePointConfiguration cfg p b ∈
      pointSet (deletePointConfiguration cfg p) := ⟨b, rfl⟩
  have habCfg : deletePointConfiguration cfg p a ≠
      deletePointConfiguration cfg p b :=
    (deletePointConfiguration cfg p).injective.ne hab
  have hall (q : AwayFrom p) : q.1 ∈ lineSupport cfg L := by
    apply mem_lineSupport.mpr
    change cfg q.1 ∈ lineOfPair cfg A
    have hqRange : deletePointConfiguration cfg p q ∈
        pointSet (deletePointConfiguration cfg p) := ⟨q, rfl⟩
    have hspan := hcol.mem_affineSpan_of_mem_of_ne
      haRange hbRange hqRange habCfg
    have hlinePair : lineOfPair cfg A =
        affineSpan ℝ ({cfg a.1, cfg b.1} : Set Point2) := by
      simpa [A] using lineOfPair_pair cfg hab'
    rw [hlinePair]
    simpa using hspan
  let U : Finset α := liftAwayFinset (Finset.univ : Finset (AwayFrom p))
  have hUcard : U.card = Fintype.card (AwayFrom p) := by
    rw [show U.card = (Finset.univ : Finset (AwayFrom p)).card by
      exact card_liftAwayFinset _]
    simp
  have hUsub : U ⊆ lineSupport cfg L := by
    intro x hx
    obtain ⟨q, _hq, rfl⟩ := mem_liftAwayFinset.mp hx
    exact hall q
  have hle := Finset.card_le_card hUsub
  have hcap := hlineCap L
  omega

/-- Every deletion of an actual fourteen-point selected-six residual is an
admissible thirteen-point configuration. -/
theorem FourteenSixCircleResidualData.deletion_admissible
    {α : Type u} [Fintype α] [DecidableEq α]
    {cfg : Configuration α} {c : DeterminedCircle cfg}
    (R : FourteenSixCircleResidualData cfg c)
    (hadm : Admissible cfg) (p : α) :
    Admissible (deletePointConfiguration cfg p) := by
  let S := blockSystem cfg
  have hAway : Fintype.card (AwayFrom p) = 13 := by
    rw [card_awayFrom, R.point_card]
  have hlineCap : ∀ L : DeterminedLine cfg,
      (lineSupport cfg L).card ≤ 6 := by
    intro L
    by_cases hthree : 3 ≤ (lineSupport cfg L).card
    · exact R.block_cap (Sum.inl L) hthree
    · omega
  have hcircleCap : ∀ d : DeterminedCircle cfg,
      (circleTrace cfg d.1).card ≤ 6 := by
    intro d
    exact R.block_cap (Sum.inr d) (S.circle_min (Sum.inr d) rfl)
  constructor
  · apply deletePointConfiguration_noncollinear_of_line_cap_lt
      cfg p (by omega)
    intro L
    have hle := hlineCap L
    omega
  · apply deletePointConfiguration_notConcyclic_of_circle_cap
      cfg p (by omega) hcircleCap

/-- The sharp deletion injection and the completed thirteen-point endpoint
bound every ordinary-circle degree in the fourteen-point residual. -/
theorem FourteenSixCircleResidualData.circleDegree_three_le_eleven
    {α : Type u} [Fintype α] [DecidableEq α]
    {cfg : Configuration α} {c : DeterminedCircle cfg}
    (R : FourteenSixCircleResidualData cfg c)
    (Mel : RealPlaneMelchiorPrinciple.{u})
    (hadm : Admissible cfg) (p : α) :
    (blockSystem cfg).circleDegree 3 p ≤ 11 := by
  have hdelCard : Fintype.card (AwayFrom p) = 13 := by
    rw [card_awayFrom, R.point_card]
  have hdelAdm := R.deletion_admissible hadm p
  have hthirteen := circleCount_ge_sixty_one_of_card_thirteen
    Mel (deletePointConfiguration cfg p) hdelAdm hdelCard
  have hdelete := circleDegree_three_add_circleCount_delete_le_circleCount
    cfg p
  have hcount := R.circle_count_le
  omega

end Erdos506.V1
