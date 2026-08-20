import Erdos506.V1.TwelveSixSpine
import Erdos506.V1.TenFive
import Erdos506.V1.DirectKelly

/-!
# Branch context for the twelve-point selected-six-circle branch

This module adds the rich-layer moments, direction rows, ordinary-vertex
bound, and literal gallery exclusions to the normalized spine.  It contains
no complete branch exclusion and no circle-count endpoint.
-/

namespace Erdos506.V1

open Erdos506.Block
open Erdos506.Block.BlockSystem
open Erdos506.Incidence
open Erdos506.V4
open scoped BigOperators

universe u

/-- The size-five and size-six layers are disjoint. -/
private theorem twelveSix_five_six_disjoint
    {Point Block : Type*} [Fintype Point] [Fintype Block]
    [DecidableEq Point]
    (S : BlockSystem Point Block) :
    Disjoint (S.blocksOfSize 5) (S.blocksOfSize 6) := by
  classical
  apply Finset.disjoint_left.mpr
  intro b hb5 hb6
  have h5 := S.mem_blocksOfSize.mp hb5
  have h6 := S.mem_blocksOfSize.mp hb6
  omega

/-- The local degree in the union of the two rich layers is `d5 + d6`. -/
private theorem twelveSix_degreeIn_rich_union
    {Point Block : Type*} [Fintype Point] [Fintype Block]
    [DecidableEq Point] [DecidableEq Block]
    (S : BlockSystem Point Block) (p : Point) :
    S.degreeIn (S.blocksOfSize 5 ∪ S.blocksOfSize 6) p =
      S.blockDegree 5 p + S.blockDegree 6 p := by
  classical
  unfold BlockSystem.blockDegree BlockSystem.degreeIn
  have hdis := (twelveSix_five_six_disjoint S).mono
    (Finset.filter_subset (fun b => p ∈ S.support b) (S.blocksOfSize 5))
    (Finset.filter_subset (fun b => p ∈ S.support b) (S.blocksOfSize 6))
  rw [Finset.filter_union]
  rw [Finset.card_union_of_disjoint hdis]

/-- The rich-layer union has the expected cardinality. -/
private theorem twelveSix_rich_union_card
    {Point Block : Type*} [Fintype Point] [Fintype Block]
    [DecidableEq Point] [DecidableEq Block]
    (S : BlockSystem Point Block) :
    (S.blocksOfSize 5 ∪ S.blocksOfSize 6).card =
      S.blockCount 5 + S.blockCount 6 := by
  classical
  rw [Finset.card_union_of_disjoint (twelveSix_five_six_disjoint S)]
  rfl

/-- The mixed five/six degree moment.  This is just cross-family Fubini;
the two size layers are disjoint, so every cross-pair consists of distinct
blocks and has at most two common points. -/
private theorem twelveSix_cross_moment
    {Point Block : Type*} [Fintype Point] [Fintype Block]
    [DecidableEq Point]
    (S : BlockSystem Point Block) :
    (∑ p : Point, S.blockDegree 5 p * S.blockDegree 6 p) ≤
      2 * S.blockCount 5 * S.blockCount 6 := by
  classical
  have hne : ∀ b ∈ S.blocksOfSize 5, ∀ c ∈ S.blocksOfSize 6, b ≠ c := by
    intro b hb c hc hbc
    subst c
    have h5 := S.mem_blocksOfSize.mp hb
    have h6 := S.mem_blocksOfSize.mp hc
    omega
  simpa only [BlockSystem.blockDegree, BlockSystem.blockCount] using
    sum_degreeIn_mul_degreeIn_le_two_mul
      S (S.blocksOfSize 5) (S.blocksOfSize 6) hne

/-- All exact rows, incidence moments, and local real-plane consequences
needed by the four scalar branches.  This record contains no branch
exclusion and no circle-count endpoint. -/
structure TwelveSixBranchContext
    {Point Block : Type*} [Fintype Point] [Fintype Block]
    [DecidableEq Point] (S : BlockSystem Point Block) : Type where
  pointCard : Fintype.card Point = 12
  spine : TwelveSixSpine S
  localRows : ∀ p : Point, TwelveSixLocalRows S p
  fiveMoment :
    (∑ p : Point, Nat.choose (S.blockDegree 5 p) 2) ≤
      2 * Nat.choose (S.blockCount 5) 2
  sixMoment :
    (∑ p : Point, Nat.choose (S.blockDegree 6 p) 2) ≤
      2 * Nat.choose (S.blockCount 6) 2
  richMoment :
    (∑ p : Point,
      Nat.choose (S.blockDegree 5 p + S.blockDegree 6 p) 2) ≤
      2 * Nat.choose (S.blockCount 5 + S.blockCount 6) 2
  crossMoment :
    (∑ p : Point, S.blockDegree 5 p * S.blockDegree 6 p) ≤
      2 * S.blockCount 5 * S.blockCount 6
  direction : S.lineCount 6 = 0 -> ∀ p : Point,
    0 < S.blockDegree 6 p ->
      2 * S.blockDegree 5 p + 6 * S.blockDegree 6 p ≤
        twelveSixSigmaAt S p + 8
  ordinaryVertex : S.lineCount 6 = 0 -> ∀ p : Point,
    6 ≤ 3 + S.blockDegree 5 p + 2 * S.blockDegree 6 p +
      twelveSixKappaAt S p + S.lineDegree 4 p + S.lineDegree 5 p
  noTypeA : Not (exists p : Point,
    S.blockDegree 3 p = 7 /\
    S.blockDegree 4 p = 10 /\
    S.blockDegree 5 p = 3 /\
    S.blockDegree 6 p = 0 /\
    S.lineDegree 3 p = 4 /\
    S.lineDegree 4 p = 0 /\
    S.lineDegree 5 p = 0 /\
    S.lineDegree 6 p = 0)
  noTypeB : Not (exists p : Point,
    S.blockDegree 3 p = 8 /\
    S.blockDegree 4 p = 9 /\
    S.blockDegree 5 p = 0 /\
    S.blockDegree 6 p = 2 /\
    S.lineDegree 3 p = 4 /\
    S.lineDegree 4 p = 0 /\
    S.lineDegree 5 p = 0 /\
    S.lineDegree 6 p = 0)

/-- Materialize the branch context from the named literal real-plane
principles. -/
noncomputable def twelveSixBranchContext_of_configuration
    {alpha : Type u} [Fintype alpha] [DecidableEq alpha]
    (Mel : RealPlaneMelchiorPrinciple.{u})
    (EvenArr : RealPlaneEvenArrangementPrinciple.{u})
    (Kelly : RealPlaneKellyMoserPrinciple.{u})
    (Gram : RealPlaneTwelveGramPrinciple.{u})
    (Gallery : RealPlaneTwelveGalleryPrinciple.{u})
    (Direction : RealPlaneTwelveDirectionPrinciple.{u})
    (cfg : Configuration alpha) (hadm : Admissible cfg)
    (hcard : Fintype.card alpha = 12)
    (hcount : Erdos506.V4.circleCount cfg <= 50)
    (gamma : DeterminedCircle cfg)
    (hgamma : (circleTrace cfg gamma.1).card = 6)
    (hcircle : forall c : DeterminedCircle cfg,
      (circleTrace cfg c.1).card <= 6) :
    TwelveSixBranchContext (blockSystem cfg) := by
  classical
  let S := blockSystem cfg
  have hcap : BlockSizeCap S 6 := by
    simpa [S] using blockSizeCap_six_of_twelve_six_branch
      cfg hadm hcard hcount hcircle
  have hspine : TwelveSixSpine S := by
    simpa [S] using twelveSixSpine_of_configuration
      Mel EvenArr Kelly Gram cfg hadm hcard hcount gamma hgamma hcircle
  have hlocal (p : alpha) : TwelveSixLocalRows S p := by
    simpa [S] using twelveSixLocalRows_of_configuration
      Mel EvenArr Kelly Gram cfg hadm hcard hcap p
  have hfive := S.second_moment_le_two_choose (S.blocksOfSize 5)
  change (∑ p : alpha, Nat.choose (S.blockDegree 5 p) 2) ≤
    2 * Nat.choose (S.blockCount 5) 2 at hfive
  have hsix := S.second_moment_le_two_choose (S.blocksOfSize 6)
  change (∑ p : alpha, Nat.choose (S.blockDegree 6 p) 2) ≤
    2 * Nat.choose (S.blockCount 6) 2 at hsix
  have hrich :=
    S.second_moment_le_two_choose
      (S.blocksOfSize 5 ∪ S.blocksOfSize 6)
  rw [twelveSix_rich_union_card S] at hrich
  simp_rw [twelveSix_degreeIn_rich_union S] at hrich
  have hcross := twelveSix_cross_moment S
  have hsigmaNonneg (p : alpha) : 0 ≤ S.pivotSigma p := by
    have hraw : TwelveFiveLocalRows S p := by
      simpa [S] using twelveFiveLocalRows_of_configuration
        Mel EvenArr Kelly Gram cfg hadm hcard hcap p
    exact hraw.sigmaNonneg
  have hdir : S.lineCount 6 = 0 -> ∀ p : alpha,
      0 < S.blockDegree 6 p ->
        2 * S.blockDegree 5 p + 6 * S.blockDegree 6 p ≤
          twelveSixSigmaAt S p + 8 := by
    intro hL6 p hp
    have hz := Direction.directionBound cfg hadm hcard hcap
      (Sum.inr gamma) rfl (by
        simpa [geometricBlockSupport] using hgamma) (by simpa [S] using hL6)
      p (by simpa [S] using hp)
    have hsCast : (twelveSixSigmaAt S p : Int) = S.pivotSigma p := by
      simpa [twelveSixSigmaAt] using Int.toNat_of_nonneg (hsigmaNonneg p)
    rw [← hsCast] at hz
    exact_mod_cast hz
  have hord : S.lineCount 6 = 0 -> ∀ p : alpha,
      6 ≤ 3 + S.blockDegree 5 p + 2 * S.blockDegree 6 p +
        twelveSixKappaAt S p + S.lineDegree 4 p + S.lineDegree 5 p := by
    intro hL6 p
    have hordinary :
        6 ≤ S.lineDegree 2 p + S.circleDegree 3 p := by
      simpa [S] using
        Kelly.six_le_restored_ordinary_line_count_of_card_twelve
          cfg hadm hcard p
    have hld6 : S.lineDegree 6 p = 0 := by
      have hle := lineDegree_le_lineCount S 6 p
      omega
    have harms := (hlocal p).lineArmRow
    have hsigma := (hlocal p).sigmaRow
    have hkappa := (hlocal p).kappaRow
    have hsplit := blockDegree_eq_lineDegree_add_circleDegree S 3 p
    omega
  have hA : Not (exists p : alpha,
      S.blockDegree 3 p = 7 /\ S.blockDegree 4 p = 10 /\
      S.blockDegree 5 p = 3 /\ S.blockDegree 6 p = 0 /\
      S.lineDegree 3 p = 4 /\ S.lineDegree 4 p = 0 /\
      S.lineDegree 5 p = 0 /\ S.lineDegree 6 p = 0) := by
    simpa [S] using Gallery.typeAForbidden cfg hadm hcard hcap
  have hB : Not (exists p : alpha,
      S.blockDegree 3 p = 8 /\ S.blockDegree 4 p = 9 /\
      S.blockDegree 5 p = 0 /\ S.blockDegree 6 p = 2 /\
      S.lineDegree 3 p = 4 /\ S.lineDegree 4 p = 0 /\
      S.lineDegree 5 p = 0 /\ S.lineDegree 6 p = 0) := by
    simpa [S] using Gallery.typeBForbidden cfg hadm hcard hcap
  exact ⟨hcard, hspine, hlocal, hfive, hsix, hrich, hcross,
    hdir, hord, hA, hB⟩

end Erdos506.V1
