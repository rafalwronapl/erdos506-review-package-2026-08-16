import Erdos506.V1.Nine
import Erdos506.V1.NineFiveConcyclic

/-!
# The complete nine-point V1 endpoint

This file classifies the four points outside a selected five-circle and
routes the resulting four cases to the terminal contradictions proved in
`NineFive` and `NineFiveConcyclic`.  It then combines the selected-circle
endpoint with the cap-four branch from `Nine`.
-/

namespace Erdos506.V1

open Erdos506.Block
open Erdos506.Block.BlockSystem
open Erdos506.Finite
open Erdos506.Incidence
open Erdos506.V3
open Erdos506.V4

universe u v

section OutsiderClassifier

variable {Point : Type u} {Block : Type v}
  [Fintype Point] [Fintype Block] [DecidableEq Point]

/-- The four points outside a selected five-block fall into the four
incidence cases used by the nine-point argument: all four are collinear,
exactly one outsider triple is line-owned, all four are concyclic, or every
outsider triple is circle-owned and no circle contains all four.

The alternatives need not be disjoint: the statement is a routing lemma,
not a uniqueness assertion. -/
theorem nineFive_outsider_cases
    (S : BlockSystem Point Block) (g : Block)
    (hpoint : Fintype.card Point = 9)
    (hgcard : (S.support g).card = 5) :
    (∃ ell, S.kind ell = .line ∧
      nineFiveOutside S g ⊆ S.support ell) ∨
    (∃ Y, NineFiveExactlyThreeOutsiders S g Y) ∨
    (∃ omega, S.kind omega = .circle ∧
      nineFiveOutside S g ⊆ S.support omega) ∨
    ((∀ A ∈ nineFiveOutsiderTriples S g,
        S.kind (S.tripleOwner A) = .circle) ∧
      ∀ omega, S.kind omega = .circle →
        ¬ nineFiveOutside S g ⊆ S.support omega) := by
  classical
  let X := nineFiveOutside S g
  let T := nineFiveOutsiderTriples S g
  have hXcard : X.card = 4 := by
    simpa [X] using nineFiveOutside_card S g hpoint hgcard
  by_cases hconcyclic : ∃ omega, S.kind omega = .circle ∧
      X ⊆ S.support omega
  · exact Or.inr (Or.inr (Or.inl (by simpa [X] using hconcyclic)))
  have hnotConcyclic : ∀ omega, S.kind omega = .circle →
      ¬ X ⊆ S.support omega := by
    intro omega homega hsub
    exact hconcyclic ⟨omega, homega, hsub⟩
  by_cases hallCircle : ∀ A ∈ T,
      S.kind (S.tripleOwner A) = .circle
  · apply Or.inr
    apply Or.inr
    apply Or.inr
    constructor
    · simpa [T] using hallCircle
    · simpa [X] using hnotConcyclic
  push Not at hallCircle
  obtain ⟨Y, hYT, hYnotCircle⟩ := hallCircle
  have hYline : S.kind (S.tripleOwner Y) = .line := by
    cases hkind : S.kind (S.tripleOwner Y) with
    | line => rfl
    | circle => exact (hYnotCircle hkind).elim
  by_cases hotherCircle : ∀ A ∈ T, A ≠ Y →
      S.kind (S.tripleOwner A) = .circle
  · apply Or.inr
    apply Or.inl
    refine ⟨Y, ?_⟩
    refine
      { mem_outsiders := by simpa [T] using hYT
        owner_line := hYline
        other_owner_circle := ?_ }
    intro A hA hAY
    exact hotherCircle A (by simpa [T] using hA) hAY
  push Not at hotherCircle
  obtain ⟨Z, hZT, hZY, hZnotCircle⟩ := hotherCircle
  have hZline : S.kind (S.tripleOwner Z) = .line := by
    cases hkind : S.kind (S.tripleOwner Z) with
    | line => rfl
    | circle => exact (hZnotCircle hkind).elim
  have hYX : Y.1 ⊆ X := by
    simpa [T, X, nineFiveOutsiderTriples] using
      (Finset.mem_filter.mp (show Y ∈ T from hYT)).2
  have hZX : Z.1 ⊆ X := by
    simpa [T, X, nineFiveOutsiderTriples] using
      (Finset.mem_filter.mp (show Z ∈ T from hZT)).2
  have hUnionSub : Y.1 ∪ Z.1 ⊆ X :=
    Finset.union_subset hYX hZX
  have hUnionCard : (Y.1 ∪ Z.1).card = 4 := by
    have hUnionLe := Finset.card_le_card hUnionSub
    by_contra hne
    have hUnionAtMostThree : (Y.1 ∪ Z.1).card ≤ 3 := by omega
    have hYUnion : Y.1 = Y.1 ∪ Z.1 :=
      Finset.eq_of_subset_of_card_le Finset.subset_union_left (by
        rw [Y.2]
        exact hUnionAtMostThree)
    have hZSubY : Z.1 ⊆ Y.1 := by
      rw [hYUnion]
      exact Finset.subset_union_right
    have hZYeq : Z.1 = Y.1 :=
      Finset.eq_of_subset_of_card_le hZSubY (by rw [Y.2, Z.2])
    exact hZY (Subtype.ext hZYeq)
  have hUnionEq : Y.1 ∪ Z.1 = X :=
    Finset.eq_of_subset_of_card_le hUnionSub (by
      rw [hXcard, hUnionCard])
  have hInterCard : 2 ≤ (Y.1 ∩ Z.1).card := by
    have hcount := Finset.card_union_add_card_inter Y.1 Z.1
    rw [Y.2, Z.2, hUnionCard] at hcount
    omega
  have hInterSub : Y.1 ∩ Z.1 ⊆
      S.support (S.tripleOwner Y) ∩ S.support (S.tripleOwner Z) := by
    intro p hp
    exact Finset.mem_inter.mpr
      ⟨S.triple_contains Y (Finset.mem_inter.mp hp).1,
        S.triple_contains Z (Finset.mem_inter.mp hp).2⟩
  have hSupportInter :
      2 ≤ (S.support (S.tripleOwner Y) ∩
        S.support (S.tripleOwner Z)).card :=
    hInterCard.trans (Finset.card_le_card hInterSub)
  have hOwnerEq : S.tripleOwner Y = S.tripleOwner Z := by
    by_contra hne
    let ellY : LineBlock S := ⟨S.tripleOwner Y, hYline⟩
    let ellZ : LineBlock S := ⟨S.tripleOwner Z, hZline⟩
    have hne' : ellY ≠ ellZ := by
      intro heq
      exact hne (congrArg Subtype.val heq)
    have hinter := S.distinct_line_inter_card_lt_two hne'
    change (S.support (S.tripleOwner Y) ∩
      S.support (S.tripleOwner Z)).card < 2 at hinter
    omega
  have hXOwner : X ⊆ S.support (S.tripleOwner Y) := by
    rw [← hUnionEq]
    apply Finset.union_subset
    · exact S.triple_contains Y
    · rw [hOwnerEq]
      exact S.triple_contains Z
  apply Or.inl
  refine ⟨S.tripleOwner Y, hYline, ?_⟩
  simpa [X] using hXOwner

end OutsiderClassifier

section GeometricEndpoint

/-- A selected five-point circle closes the nine-point counterexample.  The
four outsider cases are discharged respectively by the collinear,
exactly-three, concyclic, and general-position terminal lemmas. -/
theorem circleCount_ge_twenty_five_of_card_nine_of_selected_five_circle
    {α : Type u} [Fintype α] [DecidableEq α]
    (Mel : RealPlaneMelchiorPrinciple.{u})
    (Cross : RealPlaneRadicalAxisCrossBlockPrinciple.{u})
    (cfg : Configuration α) (hadm : Admissible cfg)
    (hcard : Fintype.card α = 9)
    (Gamma : DeterminedCircle cfg)
    (hGammaCard : (circleTrace cfg Gamma.1).card = 5) :
    25 ≤ Erdos506.V4.circleCount cfg := by
  classical
  by_contra hnot
  have hcount : Erdos506.V4.circleCount cfg ≤ 24 := by omega
  let S := blockSystem cfg
  let g : GeometricBlock cfg := Sum.inr Gamma
  have hgkind : S.kind g = .circle := by
    rfl
  have hgcard : (S.support g).card = 5 := by
    simpa [S, g] using hGammaCard
  have hlineCap : ∀ b, S.kind b = .line →
      (S.support b).card ≤ 4 := by
    intro b hb
    cases b with
    | inl L =>
        simpa [S] using
          lineSupport_card_le_four_of_nine_of_circleCount_le
            cfg hadm hcard hcount L
    | inr c => cases hb
  have hcircleCap : ∀ b, S.kind b = .circle →
      (S.support b).card ≤ 5 := by
    intro b hb
    cases b with
    | inl L => cases hb
    | inr c =>
        simpa [S] using
          circleTrace_card_le_five_of_nine_of_circleCount_le
            cfg hadm hcard hcount c
  have htotal : S.totalCircleCount = Erdos506.V4.circleCount cfg := by
    rw [totalCircleCount_eq_card_determinedCircle,
      ← Erdos506.V3.circleCount_eq_card_determinedCircle]
  have hcircles : S.totalCircleCount ≤ 24 := by
    rw [htotal]
    exact hcount
  have hglobalCfg :=
    globalLineRow_le_choose_two_sub_three_of_realPlaneMelchior Mel cfg hadm
  rw [hcard] at hglobalCfg
  norm_num [Nat.choose] at hglobalCfg
  have hglobal : S.globalLineRow ≤ 33 := by
    simpa [S, Erdos506.V1.globalLineRow] using hglobalCfg
  rcases nineFive_outsider_cases S g hcard hgcard with
      hfour | hexact | hconcyclic | hgeneral
  · obtain ⟨ell, hellkind, hXell⟩ := hfour
    exact nineFive_four_collinear_impossible S g ell hcard hgkind hgcard
      hcircleCap hcircles hellkind hXell (hlineCap ell hellkind)
  · obtain ⟨Y, hY⟩ := hexact
    exact nineFive_exactlyThree_impossible S g Y hcard hgkind hgcard
      hlineCap hcircleCap hcircles hglobal hY
  · obtain ⟨omega, homegakind, hXomega⟩ := hconcyclic
    cases omega with
    | inl L => cases homegakind
    | inr Omega =>
        apply nineFive_concyclic_impossible Mel Cross cfg hadm hcard
          Gamma Omega hGammaCard
        · simpa [S, g] using hXomega
        · exact hcount
  · exact nineFive_general_position_impossible S g hcard hgkind hgcard
      hcircleCap hcircles hgeneral.1 hgeneral.2

/-- Every admissible nine-point configuration determines at least twenty-five
proper circles.  Under a contradictory bound, rich-circle pencils leave a
cap of five; the cap-four branch is `Nine`, while a selected five-circle is
handled by the complete outsider classification above. -/
theorem circleCount_ge_twenty_five_of_card_nine
    {α : Type u} [Fintype α] [DecidableEq α]
    (Mel : RealPlaneMelchiorPrinciple.{u})
    (EvenArr : RealPlaneEvenArrangementPrinciple.{u})
    (Cross : RealPlaneRadicalAxisCrossBlockPrinciple.{u})
    (cfg : Configuration α) (hadm : Admissible cfg)
    (hcard : Fintype.card α = 9) :
    25 ≤ Erdos506.V4.circleCount cfg := by
  by_contra hnot
  have hcount : Erdos506.V4.circleCount cfg ≤ 24 := by omega
  have hcapFive : ∀ c : DeterminedCircle cfg,
      (circleTrace cfg c.1).card ≤ 5 :=
    circleTrace_card_le_five_of_nine_of_circleCount_le
      cfg hadm hcard hcount
  by_cases hcapFour : ∀ c : DeterminedCircle cfg,
      (circleTrace cfg c.1).card ≤ 4
  · exact hnot
      (circleCount_ge_twenty_five_of_card_nine_of_circle_cap_four
        Mel EvenArr cfg hadm hcard hcapFour)
  · push Not at hcapFour
    obtain ⟨Gamma, hGammaLarge⟩ := hcapFour
    have hGammaCard : (circleTrace cfg Gamma.1).card = 5 := by
      have := hcapFive Gamma
      omega
    exact hnot
      (circleCount_ge_twenty_five_of_card_nine_of_selected_five_circle
        Mel Cross cfg hadm hcard Gamma hGammaCard)

end GeometricEndpoint

end Erdos506.V1
