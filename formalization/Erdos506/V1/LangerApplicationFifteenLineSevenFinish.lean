import Erdos506.V1.LangerApplicationRichBlockResidual

/-!
# The fifteen-point rich-seven-line endpoint

For a rich line, the ordinary two-term pencil estimate can miss the V1
target by one.  The missing unit is forced as soon as the outsider set has a
circle-owned triple: its circle is either outside the pencil union, or is a
genuine triple overlap of three outsider fans.  A block cap smaller than the
outsider set forces such a triple.
-/

namespace Erdos506.V1

open Erdos506.Block
open Erdos506.Block.BlockSystem
open Erdos506.Finite
open Erdos506.V4

open scoped BigOperators

universe u v

section FiniteSlack

variable {Iota Beta : Type*} [DecidableEq Iota] [DecidableEq Beta]

/-- A repeated element saves one unit in the union-versus-sum bound. -/
private theorem card_biUnion_add_one_le_sum_of_common
    (S : Finset Iota) (G : Iota → Finset Beta)
    {j k : Iota} (hj : j ∈ S) (hk : k ∈ S) (hjk : j ≠ k)
    {x : Beta} (hxj : x ∈ G j) (hxk : x ∈ G k) :
    (S.biUnion G).card + 1 ≤ ∑ i ∈ S, (G i).card := by
  let T := S.erase j
  have hkT : k ∈ T := Finset.mem_erase.mpr ⟨hjk.symm, hk⟩
  have hxU : x ∈ T.biUnion G :=
    Finset.mem_biUnion.mpr ⟨k, hkT, hxk⟩
  have hinter : 1 ≤ (G j ∩ T.biUnion G).card := by
    apply Finset.one_le_card.mpr
    exact ⟨x, Finset.mem_inter.mpr ⟨hxj, hxU⟩⟩
  have hrest : (T.biUnion G).card ≤ ∑ i ∈ T, (G i).card :=
    Finset.card_biUnion_le
  have hunion := Finset.card_union_add_card_inter (G j) (T.biUnion G)
  have hS : S = insert j T := by
    simp [T, hj]
  have hUnionEq : S.biUnion G = G j ∪ T.biUnion G := by
    rw [hS, Finset.biUnion_insert]
  have hSumEq : (∑ i ∈ S, (G i).card) =
      (G j).card + ∑ i ∈ T, (G i).card := by
    rw [hS, Finset.sum_insert (Finset.notMem_erase j S)]
  rw [hUnionEq, hSumEq]
  omega

/-- Bonferroni improves by one when one element belongs to three distinct
members of the family. -/
private theorem card_biUnion_lower_add_one_of_mem_three
    (I : Finset Iota) (F : Iota → Finset Beta) (a h : ℕ)
    (hcard : ∀ i ∈ I, (F i).card = a)
    (hinter : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → (F i ∩ F j).card ≤ h)
    {i j k : Iota} (hi : i ∈ I) (hj : j ∈ I) (hk : k ∈ I)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    {x : Beta} (hxi : x ∈ F i) (hxj : x ∈ F j) (hxk : x ∈ F k) :
    I.card * a + 1 ≤ (I.biUnion F).card + Nat.choose I.card 2 * h := by
  let S := I.erase i
  have hjS : j ∈ S := Finset.mem_erase.mpr ⟨hij.symm, hj⟩
  have hkS : k ∈ S := Finset.mem_erase.mpr ⟨hik.symm, hk⟩
  have ih := card_biUnion_lower_of_card_inter_le S F a h
    (fun t ht => hcard t (Finset.mem_of_mem_erase ht))
    (fun t ht r hr htr => hinter t (Finset.mem_of_mem_erase ht)
      r (Finset.mem_of_mem_erase hr) htr)
  let G := fun t => F t ∩ F i
  have hdup : (S.biUnion G).card + 1 ≤ ∑ t ∈ S, (G t).card :=
    card_biUnion_add_one_le_sum_of_common S G hjS hkS hjk
      (Finset.mem_inter.mpr ⟨hxj, hxi⟩)
      (Finset.mem_inter.mpr ⟨hxk, hxi⟩)
  have hsum : (∑ t ∈ S, (G t).card) ≤ S.card * h := by
    calc
      _ ≤ ∑ _t ∈ S, h := by
        apply Finset.sum_le_sum
        intro t ht
        exact hinter t (Finset.mem_of_mem_erase ht) i hi
          (fun hti => (Finset.ne_of_mem_erase ht) hti)
      _ = S.card * h := by simp
  have hinterUnion : ((S.biUnion F) ∩ F i).card + 1 ≤ S.card * h := by
    have heq : (S.biUnion F) ∩ F i = S.biUnion G := by
      ext y
      simp only [Finset.mem_inter, Finset.mem_biUnion, G]
      aesop
    rw [heq]
    exact hdup.trans hsum
  have hinterUnion' : (F i ∩ S.biUnion F).card + 1 ≤ S.card * h := by
    simpa [Finset.inter_comm] using hinterUnion
  have hunion := Finset.card_union_add_card_inter (F i) (S.biUnion F)
  have hI : I = insert i S := by
    simp [S, hi]
  have hchoose : Nat.choose (S.card + 1) 2 =
      S.card + Nat.choose S.card 2 := by
    simpa using Nat.choose_succ_succ S.card 1
  have hiCard : (F i).card = a := hcard i hi
  rw [hI, Finset.biUnion_insert, Finset.card_insert_of_notMem
    (Finset.notMem_erase i I), hchoose]
  have hmulA : (S.card + 1) * a = S.card * a + a := by ring
  have hmulH : (S.card + S.card.choose 2) * h =
      S.card * h + S.card.choose 2 * h := by ring
  rw [hmulA, hmulH]
  dsimp only [S] at *
  omega

end FiniteSlack

section OutsiderTriple

variable {Point : Type u} {Block : Type v}
  [Fintype Point] [Fintype Block] [DecidableEq Point]

/-- If the outsider set is larger than the global block cap, some outsider
triple is circle-owned.  Otherwise the line-owner of one outsider pair would
contain the entire outsider set. -/
theorem exists_circle_owned_triple_in_blockOutsiders_of_cap
    (S : BlockSystem Point Block) (b : Block) (M : ℕ)
    (hM : 2 ≤ M) (hcap : BlockSizeCap S M)
    (hlarge : M < (blockOutsiders S b).card) :
    ∃ A : KSubset Point 3,
      A.1 ⊆ blockOutsiders S b ∧ S.kind (S.tripleOwner A) = .circle := by
  classical
  by_contra hnot
  push_neg at hnot
  have htwo : 1 < Fintype.card (BlockOutsider S b) := by
    rw [Fintype.card_coe]
    omega
  obtain ⟨x, y, hxy⟩ := Fintype.exists_pair_of_one_lt_card htwo
  let P : KSubset Point 2 :=
    ⟨{x.1, y.1}, by simp [Subtype.coe_injective.ne hxy]⟩
  let L : LineBlock S := S.lineOwner P
  have houtSub : blockOutsiders S b ⊆ S.support L.1 := by
    intro z hz
    let z' : BlockOutsider S b := ⟨z, hz⟩
    by_cases hzx : z' = x
    · have hzval : z = x.1 := by
        simpa [z'] using congrArg Subtype.val hzx
      subst z
      exact S.line_contains P (by simp [P])
    by_cases hzy : z' = y
    · have hzval : z = y.1 := by
        simpa [z'] using congrArg Subtype.val hzy
      subst z
      exact S.line_contains P (by simp [P])
    have hxz : x.1 ≠ z'.1 := Subtype.coe_injective.ne (Ne.symm hzx)
    have hyz : y.1 ≠ z'.1 := Subtype.coe_injective.ne (Ne.symm hzy)
    let A : KSubset Point 3 :=
      ⟨{x.1, y.1, z'.1}, by
        simp [Subtype.coe_injective.ne hxy, hxz, hyz]⟩
    have hAout : A.1 ⊆ blockOutsiders S b := by
      intro w hw
      simp only [A, Finset.mem_insert, Finset.mem_singleton] at hw
      rcases hw with rfl | rfl | rfl
      · exact x.2
      · exact y.2
      · exact z'.2
    have hkind : S.kind (S.tripleOwner A) = .line := by
      cases hk : S.kind (S.tripleOwner A) with
      | line => rfl
      | circle => exact (hnot A hAout hk).elim
    let L' : LineBlock S := ⟨S.tripleOwner A, hkind⟩
    have hPsub : P.1 ⊆ S.support L'.1 := by
      intro w hw
      apply S.triple_contains A
      simp only [P, Finset.mem_insert, Finset.mem_singleton] at hw
      simp only [A, Finset.mem_insert, Finset.mem_singleton]
      exact hw.elim Or.inl (fun h => Or.inr (Or.inl h))
    have hL' : L' = L := by
      exact S.line_owner_unique P L' hPsub
    have hzOwner : z'.1 ∈ S.support L'.1 := by
      apply S.triple_contains A
      simp [A]
    rw [hL'] at hzOwner
    exact hzOwner
  have hcardSub := Finset.card_le_card houtSub
  have hthree : 3 ≤ (S.support L.1).card := by
    have hout : 3 ≤ (blockOutsiders S b).card := by omega
    omega
  have hle := hcap L.1 hthree
  omega

end OutsiderTriple

section StrengthenedPencil

variable {Point : Type u} {Block : Type v}
  [Fintype Point] [Fintype Block] [DecidableEq Point]

/-- A circle block through an outsider and exactly two base labels belongs
to that outsider's rich-line fan. -/
theorem mem_circlePencil_of_kind_circle_of_inter_card_two
    (S : BlockSystem Point Block) (b : Block)
    (x : BlockOutsider S b) (c : Block)
    (hcKind : S.kind c = .circle) (hxc : x.1 ∈ S.support c)
    (hinter : (S.support c ∩ S.support b).card = 2) :
    c ∈ circlePencil S b x := by
  classical
  let u : BlockBasePair S b :=
    ⟨S.support c ∩ S.support b,
      Finset.mem_powersetCard.mpr ⟨Finset.inter_subset_right, hinter⟩⟩
  have hsub : (pencilTriple S b x u).1 ⊆ S.support c := by
    intro z hz
    change z ∈ insert x.1 u.1 at hz
    rcases Finset.mem_insert.mp hz with rfl | hz
    · exact hxc
    · exact Finset.inter_subset_left hz
  have howner : pencilOwner S b x u = c := by
    exact (S.triple_unique (pencilTriple S b x u) c hsub).symm
  apply mem_circlePencil.mpr
  refine ⟨u, mem_circleBasePairs.mpr ?_, howner⟩
  rw [howner]
  exact hcKind

/-- A circle-owned outsider triple supplies the unit missing from the plain
two-term rich-line pencil estimate.  The statement is kept before natural
subtraction, which is the lossless form used by the finite dispatcher. -/
theorem richLinePencilNumerator_add_one_le_of_circle_owned_outsider_triple
    (S : BlockSystem Point Block) (b : Block) (hb : S.kind b = .line)
    (A : KSubset Point 3) (hAout : A.1 ⊆ blockOutsiders S b)
    (hAcircle : S.kind (S.tripleOwner A) = .circle) :
    (Fintype.card Point - (S.support b).card) *
          Nat.choose (S.support b).card 2 + 1 ≤
      S.totalCircleCount +
        Nat.choose (Fintype.card Point - (S.support b).card) 2 *
          ((S.support b).card / 2) := by
  classical
  obtain ⟨x, y, z, hxy, hxz, hyz, hAeq⟩ := Finset.card_eq_three.mp A.2
  let X : BlockOutsider S b := ⟨x, hAout (by simp [hAeq])⟩
  let Y : BlockOutsider S b := ⟨y, hAout (by simp [hAeq])⟩
  let Z : BlockOutsider S b := ⟨z, hAout (by simp [hAeq])⟩
  have hXY : X ≠ Y := by
    intro h
    exact hxy (congrArg Subtype.val h)
  have hXZ : X ≠ Z := by
    intro h
    exact hxz (congrArg Subtype.val h)
  have hYZ : Y ≠ Z := by
    intro h
    exact hyz (congrArg Subtype.val h)
  let c := S.tripleOwner A
  have hxc : X.1 ∈ S.support c := by
    apply S.triple_contains A
    simp [X, hAeq]
  have hyc : Y.1 ∈ S.support c := by
    apply S.triple_contains A
    simp [Y, hAeq]
  have hzc : Z.1 ∈ S.support c := by
    apply S.triple_contains A
    simp [Z, hAeq]
  let I : Finset (BlockOutsider S b) := Finset.univ
  let F : BlockOutsider S b → Finset Block := circlePencil S b
  let a := Nat.choose (S.support b).card 2
  let h := (S.support b).card / 2
  let U := I.biUnion F
  have hcard : ∀ w ∈ I, (F w).card = a := by
    intro w _hw
    dsimp only [F, a]
    rw [card_circlePencil]
    have hall : circleBasePairs S b w = Finset.univ := by
      apply Finset.eq_univ_of_forall
      intro u
      exact mem_circleBasePairs.mpr
        (pencilOwner_kind_circle_of_base_line S b hb w u)
    rw [hall, Finset.card_univ, Fintype.card_coe]
    simp
  have hinter : ∀ p ∈ I, ∀ q ∈ I, p ≠ q →
      (F p ∩ F q).card ≤ h := by
    intro p _hp q _hq hpq
    dsimp only [F, h]
    exact card_commonPencils_le_half S b p q hpq
  have hsub : U ⊆ S.blocksOfKind .circle := by
    intro d hd
    rcases Finset.mem_biUnion.mp hd with ⟨w, _hw, hdFan⟩
    exact S.mem_blocksOfKind.mpr (circlePencil_kind S b w hdFan)
  have hUcard : U.card ≤ S.totalCircleCount :=
    Finset.card_le_card hsub
  have hIcard : I.card =
      Fintype.card Point - (S.support b).card := by
    dsimp only [I]
    rw [Finset.card_univ, Fintype.card_coe, card_blockOutsiders]
  by_cases htwo : (S.support c ∩ S.support b).card = 2
  · have hcX : c ∈ F X := by
      exact mem_circlePencil_of_kind_circle_of_inter_card_two
        S b X c hAcircle hxc htwo
    have hcY : c ∈ F Y := by
      exact mem_circlePencil_of_kind_circle_of_inter_card_two
        S b Y c hAcircle hyc htwo
    have hcZ : c ∈ F Z := by
      exact mem_circlePencil_of_kind_circle_of_inter_card_two
        S b Z c hAcircle hzc htwo
    have hbon := card_biUnion_lower_add_one_of_mem_three
      I F a h hcard hinter
      (i := X) (j := Y) (k := Z)
      (by simp [I]) (by simp [I]) (by simp [I])
      hXY hXZ hYZ hcX hcY hcZ
    dsimp only [U] at hUcard
    rw [hIcard] at hbon
    dsimp only [a, h] at hbon
    omega
  · have hcNotU : c ∉ U := by
      intro hcU
      rcases Finset.mem_biUnion.mp hcU with ⟨w, _hw, hcw⟩
      obtain ⟨u, _hu, howner⟩ := mem_circlePencil.mp hcw
      apply htwo
      rw [← howner, pencilOwner_inter_base S b w u]
      exact (Finset.mem_powersetCard.mp u.2).2
    have hinsert : insert c U ⊆ S.blocksOfKind .circle := by
      intro d hd
      rcases Finset.mem_insert.mp hd with rfl | hdU
      · exact S.mem_blocksOfKind.mpr hAcircle
      · exact hsub hdU
    have htotal : U.card + 1 ≤ S.totalCircleCount := by
      have hle := Finset.card_le_card hinsert
      rw [Finset.card_insert_of_notMem hcNotU] at hle
      simpa [Nat.add_comm] using hle
    have hbon := card_biUnion_lower_of_card_inter_le I F a h hcard hinter
    rw [hIcard] at hbon
    dsimp only [U] at htotal
    dsimp only [a, h] at hbon
    omega

end StrengthenedPencil

section FifteenEndpoint

variable {α : Type u} [Fintype α] [DecidableEq α]

/-- The strengthened pencil closes the unique line residual where the plain
rich-line bound is one below the V1 target. -/
theorem FiniteWindowRichBlockResidual.line_impossible_of_fifteen_seven
    {cfg : Configuration α} (R : FiniteWindowRichBlockResidual cfg)
    (hadm : Admissible cfg)
    (hline : (blockSystem cfg).kind R.block = .line)
    (h15 : Fintype.card α = 15)
    (hseven : (geometricBlockSupport cfg R.block).card = 7)
    (hcount : Erdos506.V4.circleCount cfg <
      Erdos506.v1UniformTarget (Fintype.card α)) : False := by
  let S := blockSystem cfg
  change S.kind R.block = .line at hline
  change (S.support R.block).card = 7 at hseven
  have hcap := halfBlockCap_of_circleCount_lt_v1UniformTarget
    cfg hadm (by omega) hcount
  have hcapSeven : BlockSizeCap S 7 := by
    rw [h15] at hcap
    norm_num at hcap
    exact hcap
  have hout : (blockOutsiders S R.block).card = 8 := by
    rw [card_blockOutsiders, h15, hseven]
  obtain ⟨A, hAout, hAcircle⟩ :=
    exists_circle_owned_triple_in_blockOutsiders_of_cap
      S R.block 7 (by omega) hcapSeven (by omega)
  have hstrong :=
    richLinePencilNumerator_add_one_le_of_circle_owned_outsider_triple
      S R.block hline A hAout hAcircle
  rw [totalCircleCount_eq_card_determinedCircle,
    ← Erdos506.V3.circleCount_eq_card_determinedCircle] at hstrong
  rw [h15, hseven] at hstrong
  norm_num [Nat.choose] at hstrong
  rw [h15] at hcount
  norm_num [Erdos506.v1UniformTarget, Nat.choose] at hcount
  omega

end FifteenEndpoint

end Erdos506.V1
