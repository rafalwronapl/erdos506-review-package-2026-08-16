import Erdos506.Finite.Bonferroni
import Erdos506.V3.Arithmetic
import Erdos506.V3.Model

/-!
# The rich-circle pencil bound

For a fixed determined circle `g`, each outsider and each pair on `g`
determine a fan circle.  A pair of outsider fans has at most half as many
common circles as there are labels on `g`; the proof recovers disjoint base
pairs and then applies the finite matching bound.
-/

namespace Erdos506.V3

open Erdos506.Finite
open Erdos506.V4

variable {α : Type*} [Fintype α] [DecidableEq α]

noncomputable def outsiderLabels (cfg : Configuration α)
    (g : DeterminedCircle cfg) : Finset α :=
  Finset.univ \ circleTrace cfg g.1

@[simp] theorem mem_outsiderLabels {cfg : Configuration α}
    {g : DeterminedCircle cfg} {x : α} :
    x ∈ outsiderLabels cfg g ↔ x ∉ circleTrace cfg g.1 := by
  classical
  simp [outsiderLabels]

theorem card_outsiderLabels (cfg : Configuration α)
    (g : DeterminedCircle cfg) :
    (outsiderLabels cfg g).card =
      Fintype.card α - (circleTrace cfg g.1).card := by
  classical
  rw [outsiderLabels, Finset.card_sdiff_of_subset (Finset.subset_univ _)]
  simp

abbrev BasePair (cfg : Configuration α) (g : DeterminedCircle cfg) :=
  {u : Finset α // u ∈ (circleTrace cfg g.1).powersetCard 2}

abbrev Outsider (cfg : Configuration α) (g : DeterminedCircle cfg) :=
  {x : α // x ∈ outsiderLabels cfg g}

noncomputable def fanTriple (cfg : Configuration α)
    (g : DeterminedCircle cfg) (x : Outsider cfg g) (u : BasePair cfg g) :
    KSubset α 3 := by
  refine ⟨insert x.1 u.1, ?_⟩
  have hu := Finset.mem_powersetCard.mp u.2
  have hxnot : x.1 ∉ u.1 := by
    intro hx
    exact (mem_outsiderLabels.mp x.2) (hu.1 hx)
  simp [hxnot, hu.2]

noncomputable def fanCircle (cfg : Configuration α)
    (hthree : NoThreeCollinear cfg) (g : DeterminedCircle cfg)
    (x : Outsider cfg g) (u : BasePair cfg g) : DeterminedCircle cfg :=
  circleOwner cfg hthree (fanTriple cfg g x u)

noncomputable def circleFan (cfg : Configuration α)
    (hthree : NoThreeCollinear cfg) (g : DeterminedCircle cfg)
    (x : Outsider cfg g) : Finset (DeterminedCircle cfg) := by
  classical
  exact Finset.univ.image (fanCircle cfg hthree g x)

@[simp] theorem mem_circleFan {cfg : Configuration α}
    {hthree : NoThreeCollinear cfg} {g : DeterminedCircle cfg}
    {x : Outsider cfg g} {c : DeterminedCircle cfg} :
    c ∈ circleFan cfg hthree g x ↔
      ∃ u : BasePair cfg g, fanCircle cfg hthree g x u = c := by
  classical
  simp [circleFan]

theorem fanCircle_contains_outsider (cfg : Configuration α)
    (hthree : NoThreeCollinear cfg) (g : DeterminedCircle cfg)
    (x : Outsider cfg g) (u : BasePair cfg g) :
    x.1 ∈ circleTrace cfg (fanCircle cfg hthree g x u).1 := by
  exact circleOwner_contains cfg hthree (fanTriple cfg g x u) (by
    simp [fanTriple])

theorem fanCircle_contains_pair (cfg : Configuration α)
    (hthree : NoThreeCollinear cfg) (g : DeterminedCircle cfg)
    (x : Outsider cfg g) (u : BasePair cfg g) :
    u.1 ⊆ circleTrace cfg (fanCircle cfg hthree g x u).1 := by
  intro z hz
  exact circleOwner_contains cfg hthree (fanTriple cfg g x u) (by
    simp [fanTriple, hz])

theorem fanCircle_ne_base (cfg : Configuration α)
    (hthree : NoThreeCollinear cfg) (g : DeterminedCircle cfg)
    (x : Outsider cfg g) (u : BasePair cfg g) :
    fanCircle cfg hthree g x u ≠ g := by
  intro h
  have hxmem := fanCircle_contains_outsider cfg hthree g x u
  rw [h] at hxmem
  exact (mem_outsiderLabels.mp x.2) hxmem

theorem fanCircle_inter_base (cfg : Configuration α)
    (hthree : NoThreeCollinear cfg) (g : DeterminedCircle cfg)
    (x : Outsider cfg g) (u : BasePair cfg g) :
    circleTrace cfg (fanCircle cfg hthree g x u).1 ∩ circleTrace cfg g.1 = u.1 := by
  classical
  symm
  apply Finset.eq_of_subset_of_card_le
  · intro z hz
    exact Finset.mem_inter.mpr
      ⟨fanCircle_contains_pair cfg hthree g x u hz,
        (Finset.mem_powersetCard.mp u.2).1 hz⟩
  · have hlt := (circleOwnership cfg hthree).card_inter_lt_of_ne
      (fanCircle_ne_base cfg hthree g x u)
    change (circleTrace cfg (fanCircle cfg hthree g x u).1 ∩
      circleTrace cfg g.1).card < 3 at hlt
    have huCard := (Finset.mem_powersetCard.mp u.2).2
    omega

theorem fanCircle_injective (cfg : Configuration α)
    (hthree : NoThreeCollinear cfg) (g : DeterminedCircle cfg)
    (x : Outsider cfg g) :
    Function.Injective (fanCircle cfg hthree g x) := by
  intro u v huv
  apply Subtype.ext
  have h := congrArg
    (fun c : DeterminedCircle cfg => circleTrace cfg c.1 ∩ circleTrace cfg g.1) huv
  simpa [fanCircle_inter_base cfg hthree g x u,
    fanCircle_inter_base cfg hthree g x v] using h

theorem card_circleFan (cfg : Configuration α)
    (hthree : NoThreeCollinear cfg) (g : DeterminedCircle cfg)
    (x : Outsider cfg g) :
    (circleFan cfg hthree g x).card =
      Nat.choose (circleTrace cfg g.1).card 2 := by
  classical
  rw [circleFan, Finset.card_image_of_injective _
    (fanCircle_injective cfg hthree g x)]
  rw [Finset.card_univ, Fintype.card_coe]
  simp

theorem outsider_mem_support_of_mem_fan (cfg : Configuration α)
    (hthree : NoThreeCollinear cfg) (g : DeterminedCircle cfg)
    (x : Outsider cfg g) {c : DeterminedCircle cfg}
    (hc : c ∈ circleFan cfg hthree g x) :
    x.1 ∈ circleTrace cfg c.1 := by
  obtain ⟨u, rfl⟩ := mem_circleFan.mp hc
  exact fanCircle_contains_outsider cfg hthree g x u

noncomputable def commonFans (cfg : Configuration α)
    (hthree : NoThreeCollinear cfg) (g : DeterminedCircle cfg)
    (x y : Outsider cfg g) : Finset (DeterminedCircle cfg) := by
  classical
  exact circleFan cfg hthree g x ∩ circleFan cfg hthree g y

abbrev CommonCircle (cfg : Configuration α)
    (hthree : NoThreeCollinear cfg) (g : DeterminedCircle cfg)
    (x y : Outsider cfg g) :=
  {c : DeterminedCircle cfg // c ∈ commonFans cfg hthree g x y}

noncomputable def commonBasePair (cfg : Configuration α)
    (g : DeterminedCircle cfg) {hthree : NoThreeCollinear cfg}
    {x y : Outsider cfg g} (c : CommonCircle cfg hthree g x y) : Finset α :=
  circleTrace cfg c.1.1 ∩ circleTrace cfg g.1

theorem commonBasePair_card (cfg : Configuration α)
    (hthree : NoThreeCollinear cfg) (g : DeterminedCircle cfg)
    (x y : Outsider cfg g) (c : CommonCircle cfg hthree g x y) :
    (commonBasePair cfg g c).card = 2 := by
  classical
  have hcFan : c.1 ∈ circleFan cfg hthree g x :=
    (Finset.mem_inter.mp c.2).1
  obtain ⟨u, hu⟩ := mem_circleFan.mp hcFan
  unfold commonBasePair
  rw [← hu, fanCircle_inter_base cfg hthree g x u]
  exact (Finset.mem_powersetCard.mp u.2).2

theorem commonBasePair_injective (cfg : Configuration α)
    (hthree : NoThreeCollinear cfg) (g : DeterminedCircle cfg)
    (x y : Outsider cfg g) :
    Function.Injective (commonBasePair cfg g :
      CommonCircle cfg hthree g x y → Finset α) := by
  classical
  intro c d hpair
  apply Subtype.ext
  have hcFan : c.1 ∈ circleFan cfg hthree g x :=
    (Finset.mem_inter.mp c.2).1
  have hdFan : d.1 ∈ circleFan cfg hthree g x :=
    (Finset.mem_inter.mp d.2).1
  obtain ⟨u, hu⟩ := mem_circleFan.mp hcFan
  obtain ⟨v, hv⟩ := mem_circleFan.mp hdFan
  have hpair' := hpair
  unfold commonBasePair at hpair'
  rw [← hu, ← hv, fanCircle_inter_base cfg hthree g x u,
    fanCircle_inter_base cfg hthree g x v] at hpair'
  have huv : u = v := Subtype.ext hpair'
  exact hu.symm.trans ((congrArg (fanCircle cfg hthree g x) huv).trans hv)

noncomputable def commonBasePairs (cfg : Configuration α)
    (hthree : NoThreeCollinear cfg) (g : DeterminedCircle cfg)
    (x y : Outsider cfg g) : Finset (Finset α) := by
  classical
  exact Finset.univ.image (commonBasePair cfg g :
    CommonCircle cfg hthree g x y → Finset α)

theorem card_commonBasePairs (cfg : Configuration α)
    (hthree : NoThreeCollinear cfg) (g : DeterminedCircle cfg)
    (x y : Outsider cfg g) :
    (commonBasePairs cfg hthree g x y).card =
      (commonFans cfg hthree g x y).card := by
  classical
  rw [commonBasePairs, Finset.card_image_of_injective _
    (commonBasePair_injective cfg hthree g x y)]
  simp

theorem commonBasePairs_pairwiseDisjoint (cfg : Configuration α)
    (hthree : NoThreeCollinear cfg) (g : DeterminedCircle cfg)
    (x y : Outsider cfg g) (hxy : x ≠ y) :
    ((commonBasePairs cfg hthree g x y : Finset (Finset α)) : Set (Finset α)).PairwiseDisjoint id := by
  classical
  intro p hp q hq hpq
  change Disjoint p q
  rw [Finset.disjoint_left]
  intro z hzp hzq
  rw [commonBasePairs] at hp hq
  obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hp
  obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hq
  have hcd : c.1 ≠ d.1 := by
    intro h
    apply hpq
    have hcd' : c = d := Subtype.ext h
    subst d
    rfl
  have hcBoth := Finset.mem_inter.mp c.2
  have hdBoth := Finset.mem_inter.mp d.2
  have hxc := outsider_mem_support_of_mem_fan cfg hthree g x hcBoth.1
  have hxd := outsider_mem_support_of_mem_fan cfg hthree g x hdBoth.1
  have hyc := outsider_mem_support_of_mem_fan cfg hthree g y hcBoth.2
  have hyd := outsider_mem_support_of_mem_fan cfg hthree g y hdBoth.2
  have hzc : z ∈ circleTrace cfg c.1.1 := (Finset.mem_inter.mp hzp).1
  have hzd : z ∈ circleTrace cfg d.1.1 := (Finset.mem_inter.mp hzq).1
  have hzG : z ∈ circleTrace cfg g.1 := (Finset.mem_inter.mp hzp).2
  have hxy' : x.1 ≠ y.1 := Subtype.coe_injective.ne hxy
  have hxz : x.1 ≠ z := by
    intro hxz
    subst z
    exact (mem_outsiderLabels.mp x.2) hzG
  have hyz : y.1 ≠ z := by
    intro hyz
    subst z
    exact (mem_outsiderLabels.mp y.2) hzG
  have hsub : ({x.1, y.1, z} : Finset α) ⊆
      circleTrace cfg c.1.1 ∩ circleTrace cfg d.1.1 := by
    intro w hw
    simp only [Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with rfl | rfl | rfl
    · exact Finset.mem_inter.mpr ⟨hxc, hxd⟩
    · exact Finset.mem_inter.mpr ⟨hyc, hyd⟩
    · exact Finset.mem_inter.mpr ⟨hzc, hzd⟩
  have hthreeCard : ({x.1, y.1, z} : Finset α).card = 3 := by
    simp [hxy', hxz, hyz]
  have hle := Finset.card_le_card hsub
  have hlt := (circleOwnership cfg hthree).card_inter_lt_of_ne hcd
  change (circleTrace cfg c.1.1 ∩ circleTrace cfg d.1.1).card < 3 at hlt
  omega

theorem card_commonFans_le_half (cfg : Configuration α)
    (hthree : NoThreeCollinear cfg) (g : DeterminedCircle cfg)
    (x y : Outsider cfg g) (hxy : x ≠ y) :
    (commonFans cfg hthree g x y).card ≤
      (circleTrace cfg g.1).card / 2 := by
  classical
  let P := commonBasePairs cfg hthree g x y
  have hsub : ∀ p ∈ P, p ⊆ circleTrace cfg g.1 := by
    intro p hp z hzp
    change p ∈ commonBasePairs cfg hthree g x y at hp
    rw [commonBasePairs] at hp
    obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hp
    exact (Finset.mem_inter.mp hzp).2
  have hpair : ∀ p ∈ P, p.card = 2 := by
    intro p hp
    change p ∈ commonBasePairs cfg hthree g x y at hp
    rw [commonBasePairs] at hp
    obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hp
    exact commonBasePair_card cfg hthree g x y c
  have hmatch := card_le_half_of_pairwiseDisjoint_pairs
    (circleTrace cfg g.1) P hsub hpair
    (by simpa [P] using commonBasePairs_pairwiseDisjoint cfg hthree g x y hxy)
  rw [card_commonBasePairs cfg hthree g x y] at hmatch
  exact hmatch

noncomputable def circleFanForLabel (cfg : Configuration α)
    (hthree : NoThreeCollinear cfg) (g : DeterminedCircle cfg)
    (x : α) : Finset (DeterminedCircle cfg) := by
  classical
  by_cases hx : x ∈ outsiderLabels cfg g
  · exact circleFan cfg hthree g ⟨x, hx⟩
  · exact ∅

theorem circleFanForLabel_eq (cfg : Configuration α)
    (hthree : NoThreeCollinear cfg) (g : DeterminedCircle cfg)
    {x : α} (hx : x ∈ outsiderLabels cfg g) :
    circleFanForLabel cfg hthree g x = circleFan cfg hthree g ⟨x, hx⟩ := by
  classical
  simp [circleFanForLabel, hx]

theorem base_not_mem_circleFanForLabel (cfg : Configuration α)
    (hthree : NoThreeCollinear cfg) (g : DeterminedCircle cfg)
    {x : α} (hx : x ∈ outsiderLabels cfg g) :
    g ∉ circleFanForLabel cfg hthree g x := by
  rw [circleFanForLabel_eq cfg hthree g hx]
  intro hg
  obtain ⟨u, hu⟩ := mem_circleFan.mp hg
  exact fanCircle_ne_base cfg hthree g ⟨x, hx⟩ u hu

/-- The rich-circle pencil lower bound for an arbitrary selected determined
circle. -/
theorem pencilBound_le_circleCount (cfg : Configuration α)
    (hthree : NoThreeCollinear cfg) (g : DeterminedCircle cfg) :
    pencilBound (Fintype.card α) (circleTrace cfg g.1).card ≤ circleCount cfg := by
  classical
  let I := outsiderLabels cfg g
  let F := circleFanForLabel cfg hthree g
  let a := Nat.choose (circleTrace cfg g.1).card 2
  let h := (circleTrace cfg g.1).card / 2
  have hcard : ∀ x ∈ I, (F x).card = a := by
    intro x hx
    dsimp only [F, a]
    rw [circleFanForLabel_eq cfg hthree g hx,
      card_circleFan cfg hthree g ⟨x, hx⟩]
  have hinter : ∀ x ∈ I, ∀ y ∈ I, x ≠ y → (F x ∩ F y).card ≤ h := by
    intro x hx y hy hxy
    dsimp only [F, h]
    rw [circleFanForLabel_eq cfg hthree g hx,
      circleFanForLabel_eq cfg hthree g hy]
    exact card_commonFans_le_half cfg hthree g ⟨x, hx⟩ ⟨y, hy⟩
      (by
        intro heq
        exact hxy (congrArg Subtype.val heq))
  have hbon := card_biUnion_lower_of_card_inter_le I F a h hcard hinter
  let U := I.biUnion F
  change I.card * a ≤ U.card + Nat.choose I.card 2 * h at hbon
  have hgnot : g ∉ U := by
    intro hg
    rcases Finset.mem_biUnion.mp hg with ⟨x, hx, hgFan⟩
    exact base_not_mem_circleFanForLabel cfg hthree g hx hgFan
  have htotal : U.card + 1 ≤ circleCount cfg := by
    have hsub : insert g U ⊆ Finset.univ := Finset.subset_univ _
    have hle := Finset.card_le_card hsub
    rw [Finset.card_insert_of_notMem hgnot, Finset.card_univ] at hle
    rw [circleCount_eq_card_determinedCircle cfg]
    exact hle
  have hIcard : I.card = Fintype.card α - (circleTrace cfg g.1).card :=
    card_outsiderLabels cfg g
  unfold pencilBound
  rw [← hIcard]
  change 1 + I.card * a - Nat.choose I.card 2 * h ≤ circleCount cfg
  omega

end Erdos506.V3
