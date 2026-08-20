import Erdos506.V4.Arithmetic
import Erdos506.V4.Model
import Mathlib.Tactic

/-!
# Richest-line selection and exact natural-number arithmetic

This module formalizes the finite maximum used by the V4 proof and the
division-free arithmetic identity behind the two-family count.  The geometric
injections of the two triple families are kept separate from these reusable
facts.
-/

namespace Erdos506.V4

/-- Ordered pairs of distinct labels.  Ordering is harmless here and avoids a
choice of endpoints from a two-element support. -/
noncomputable def distinctPairs (α : Type*) [Fintype α] : Finset (α × α) := by
  classical
  exact (Finset.univ ×ˢ Finset.univ).filter fun p => p.1 ≠ p.2

@[simp] theorem mem_distinctPairs {α : Type*} [Fintype α] {p : α × α} :
    p ∈ distinctPairs α ↔ p.1 ≠ p.2 := by
  classical
  simp [distinctPairs]

theorem distinctPairs_nonempty {α : Type*} [Fintype α]
    (hcard : 2 ≤ Fintype.card α) : (distinctPairs α).Nonempty := by
  classical
  have hpos : 0 < Fintype.card α := by omega
  let a : α := Classical.choice (Fintype.card_pos_iff.mp hpos)
  obtain ⟨b, hba⟩ := Fintype.exists_ne_of_one_lt_card (by omega) a
  exact ⟨(a, b), by simp [hba.symm]⟩

/-- A finite configuration with at least two labels has a selected pair-line
whose trace is at least as rich as every other selected pair-line. -/
theorem exists_richest_pair {α : Type*} [Fintype α]
    (cfg : Configuration α) (hcard : 2 ≤ Fintype.card α) :
    ∃ a b, a ≠ b ∧
      ∀ x y, x ≠ y →
        (lineTrace cfg x y).card ≤ (lineTrace cfg a b).card := by
  classical
  obtain ⟨p, hp, hmax⟩ := Finset.exists_max_image
    (distinctPairs α) (fun q => (lineTrace cfg q.1 q.2).card)
    (distinctPairs_nonempty hcard)
  refine ⟨p.1, p.2, (mem_distinctPairs.mp hp), ?_⟩
  intro x y hxy
  exact hmax (x, y) (mem_distinctPairs.mpr hxy)

/-- Labels outside a selected pair-line. -/
noncomputable def outsiders {α : Type*} [Fintype α]
    (cfg : Configuration α) (a b : α) : Finset α := by
  classical
  exact Finset.univ \ lineTrace cfg a b

@[simp] theorem mem_outsiders {α : Type*} [Fintype α]
    {cfg : Configuration α} {a b x : α} :
    x ∈ outsiders cfg a b ↔ x ∉ lineTrace cfg a b := by
  classical
  simp [outsiders]

theorem card_lineTrace_add_card_outsiders {α : Type*} [Fintype α]
    (cfg : Configuration α) (a b : α) :
    (lineTrace cfg a b).card + (outsiders cfg a b).card = Fintype.card α := by
  classical
  have hle : (lineTrace cfg a b).card ≤ Fintype.card α := by
    simpa using Finset.card_le_card (Finset.subset_univ (lineTrace cfg a b))
  rw [outsiders, Finset.card_sdiff_of_subset (Finset.subset_univ _)]
  simp only [Finset.card_univ]
  omega

/-- Two distinct points lying on a selected pair-line determine that same
affine line. -/
theorem affineSpan_pair_eq_of_mem_of_mem {p q a b : Point2}
    (hp : p ∈ affineSpan ℝ ({a, b} : Set Point2))
    (hq : q ∈ affineSpan ℝ ({a, b} : Set Point2))
    (hpq : p ≠ q) (hab : a ≠ b) :
    affineSpan ℝ ({p, q} : Set Point2) =
      affineSpan ℝ ({a, b} : Set Point2) := by
  have hcol : Collinear ℝ ({p, q, a, b} : Set Point2) :=
    collinear_insert_insert_of_mem_affineSpan_pair hp hq
  calc
    affineSpan ℝ ({p, q} : Set Point2) =
        affineSpan ℝ ({p, q, a, b} : Set Point2) :=
      hcol.affineSpan_eq_of_ne (by simp) (by simp) hpq
    _ = affineSpan ℝ ({a, b} : Set Point2) :=
      (hcol.affineSpan_eq_of_ne (by simp) (by simp) hab).symm

/-- Points of the base line that are collinear with one fixed outsider pair. -/
noncomputable def badLinePoints {α : Type*} [Fintype α]
    (cfg : Configuration α) (a b p q : α) : Finset α := by
  classical
  exact (lineTrace cfg a b).filter fun x =>
    Collinear ℝ ({cfg x, cfg p, cfg q} : Set Point2)

/-- A fixed distinct outsider pair has at most one bad point on the base
line.  This is the sole geometric input in the second-family cardinality
bound. -/
theorem badLinePoints_card_le_one {α : Type*} [Fintype α]
    (cfg : Configuration α) {a b p q : α}
    (hab : a ≠ b) (hpq : p ≠ q)
    (hp : p ∉ lineTrace cfg a b) :
    (badLinePoints cfg a b p q).card ≤ 1 := by
  classical
  rw [Finset.card_le_one]
  intro x hx y hy
  simp only [badLinePoints, Finset.mem_filter] at hx hy
  rcases hx with ⟨hxL, hcolx⟩
  rcases hy with ⟨hyL, hcoly⟩
  by_contra hxy
  have hpq' : cfg p ≠ cfg q := cfg.injective.ne hpq
  have hxy' : cfg x ≠ cfg y := cfg.injective.ne hxy
  have hxPQ : cfg x ∈ affineSpan ℝ ({cfg p, cfg q} : Set Point2) :=
    hcolx.mem_affineSpan_of_mem_of_ne (by simp) (by simp) (by simp) hpq'
  have hyPQ : cfg y ∈ affineSpan ℝ ({cfg p, cfg q} : Set Point2) :=
    hcoly.mem_affineSpan_of_mem_of_ne (by simp) (by simp) (by simp) hpq'
  have hall : Collinear ℝ ({cfg x, cfg y, cfg p, cfg q} : Set Point2) :=
    collinear_insert_insert_of_mem_affineSpan_pair hxPQ hyPQ
  have hpXY : cfg p ∈ affineSpan ℝ ({cfg x, cfg y} : Set Point2) :=
    hall.mem_affineSpan_of_mem_of_ne (by simp) (by simp) (by simp) hxy'
  have hline :
      affineSpan ℝ ({cfg x, cfg y} : Set Point2) =
        affineSpan ℝ ({cfg a, cfg b} : Set Point2) :=
    affineSpan_pair_eq_of_mem_of_mem
      (mem_lineTrace.mp hxL) (mem_lineTrace.mp hyL) hxy' (cfg.injective.ne hab)
  rw [hline] at hpXY
  exact hp (mem_lineTrace.mpr hpXY)

/-- Two distinct selected points on the base line and one selected point
outside it form a noncollinear triple. -/
theorem noncollinear_of_two_mem_line_one_outside {α : Type*} [Fintype α]
    (cfg : Configuration α) {a b x y z : α}
    (hab : a ≠ b) (hyz : y ≠ z)
    (hy : y ∈ lineTrace cfg a b) (hz : z ∈ lineTrace cfg a b)
    (hx : x ∉ lineTrace cfg a b) :
    ¬Collinear ℝ ({cfg x, cfg y, cfg z} : Set Point2) := by
  intro hcol
  have hyz' : cfg y ≠ cfg z := cfg.injective.ne hyz
  have hxYZ : cfg x ∈ affineSpan ℝ ({cfg y, cfg z} : Set Point2) :=
    hcol.mem_affineSpan_of_mem_of_ne (by simp) (by simp) (by simp) hyz'
  have hline :
      affineSpan ℝ ({cfg y, cfg z} : Set Point2) =
        affineSpan ℝ ({cfg a, cfg b} : Set Point2) :=
    affineSpan_pair_eq_of_mem_of_mem
      (mem_lineTrace.mp hy) (mem_lineTrace.mp hz) hyz' (cfg.injective.ne hab)
  rw [hline] at hxYZ
  exact hx (mem_lineTrace.mpr hxYZ)

/-- The unordered triple represented by a pair support and one extra label. -/
noncomputable def tripleOfIndex {α : Type*} (p : Finset α × α) : Finset α := by
  classical
  exact insert p.2 p.1

/-- Indices for triples with two base-line labels and one outsider. -/
noncomputable def familyAIndices {α : Type*} [Fintype α]
    (cfg : Configuration α) (a b : α) : Finset (Finset α × α) := by
  classical
  exact (lineTrace cfg a b).powersetCard 2 ×ˢ outsiders cfg a b

/-- All indices with two outsider labels and one base-line label. -/
noncomputable def familyBAllIndices {α : Type*} [Fintype α]
    (cfg : Configuration α) (a b : α) : Finset (Finset α × α) := by
  classical
  exact (outsiders cfg a b).powersetCard 2 ×ˢ lineTrace cfg a b

/-- The noncollinear indices in the second family. -/
noncomputable def familyBIndices {α : Type*} [Fintype α]
    (cfg : Configuration α) (a b : α) : Finset (Finset α × α) := by
  classical
  exact (familyBAllIndices cfg a b).filter fun p =>
    IsNoncollinear cfg (tripleOfIndex p)

/-- The complementary, collinear indices in the second family. -/
noncomputable def familyBBadIndices {α : Type*} [Fintype α]
    (cfg : Configuration α) (a b : α) : Finset (Finset α × α) := by
  classical
  exact (familyBAllIndices cfg a b).filter fun p =>
    ¬IsNoncollinear cfg (tripleOfIndex p)

/-- First-family triples. -/
noncomputable def familyA {α : Type*} [Fintype α]
    (cfg : Configuration α) (a b : α) : Finset (Finset α) := by
  classical
  exact (familyAIndices cfg a b).image tripleOfIndex

/-- Second-family noncollinear triples. -/
noncomputable def familyB {α : Type*} [Fintype α]
    (cfg : Configuration α) (a b : α) : Finset (Finset α) := by
  classical
  exact (familyBIndices cfg a b).image tripleOfIndex

/-- Inserting a point from one side of a disjoint partition into a
two-support from the other side is injective on the product index set. -/
theorem tripleOfIndex_injOn_product {α : Type*} {s t : Finset α}
    (hst : Disjoint s t) :
    Set.InjOn tripleOfIndex
      ((s.powersetCard 2 ×ˢ t : Finset (Finset α × α)) : Set (Finset α × α)) := by
  classical
  rintro ⟨u, x⟩ hp ⟨v, y⟩ hq heq
  change (u, x) ∈ s.powersetCard 2 ×ˢ t at hp
  change (v, y) ∈ s.powersetCard 2 ×ˢ t at hq
  rcases Finset.mem_product.mp hp with ⟨hps, hpt⟩
  rcases Finset.mem_product.mp hq with ⟨hqs, hqt⟩
  have hpsub := (Finset.mem_powersetCard.mp hps).1
  have hqsub := (Finset.mem_powersetCard.mp hqs).1
  have hxnot : x ∉ u := by
    intro hxu
    exact (Finset.disjoint_left.mp hst) (hpsub hxu) hpt
  have hynot : y ∉ v := by
    intro hyv
    exact (Finset.disjoint_left.mp hst) (hqsub hyv) hqt
  change insert x u = insert y v at heq
  have hpoint : x = y := by
    have hx : x ∈ insert y v := by
      rw [← heq]
      exact Finset.mem_insert_self _ _
    rcases Finset.mem_insert.mp hx with hxy | hxv
    · exact hxy
    · exact False.elim ((Finset.disjoint_left.mp hst) (hqsub hxv) hpt)
  subst y
  have herase := congrArg (fun w : Finset α => w.erase x) heq
  change (insert x u).erase x = (insert x v).erase x at herase
  rw [Finset.erase_insert hxnot, Finset.erase_insert hynot] at herase
  subst v
  rfl

theorem card_familyA {α : Type*} [Fintype α]
    (cfg : Configuration α) (a b : α) :
    (familyA cfg a b).card =
      Nat.choose (lineTrace cfg a b).card 2 * (outsiders cfg a b).card := by
  classical
  rw [familyA, Finset.card_image_of_injOn]
  · simp [familyAIndices, Finset.card_product]
  · exact tripleOfIndex_injOn_product Finset.disjoint_sdiff

theorem card_familyB_eq_indices {α : Type*} [Fintype α]
    (cfg : Configuration α) (a b : α) :
    (familyB cfg a b).card = (familyBIndices cfg a b).card := by
  classical
  rw [familyB, Finset.card_image_of_injOn]
  refine (tripleOfIndex_injOn_product
    (s := outsiders cfg a b) (t := lineTrace cfg a b) Finset.sdiff_disjoint).mono ?_
  intro p hp
  change p ∈ familyBIndices cfg a b at hp
  change p ∈ (outsiders cfg a b).powersetCard 2 ×ˢ lineTrace cfg a b
  have hpall : p ∈ familyBAllIndices cfg a b := by
    rw [familyBIndices] at hp
    exact (Finset.mem_filter.mp hp).1
  simpa [familyBAllIndices] using hpall

theorem familyA_subset_noncollinearTriples {α : Type*} [Fintype α]
    (cfg : Configuration α) {a b : α} (hab : a ≠ b) :
    familyA cfg a b ⊆ noncollinearTriples cfg := by
  classical
  intro t ht
  rw [familyA] at ht
  rcases Finset.mem_image.mp ht with ⟨⟨u, x⟩, hindex, rfl⟩
  rw [familyAIndices] at hindex
  rcases Finset.mem_product.mp hindex with ⟨hu, hxO⟩
  change u ∈ (lineTrace cfg a b).powersetCard 2 at hu
  change x ∈ outsiders cfg a b at hxO
  rcases Finset.mem_powersetCard.mp hu with ⟨huL, hucard⟩
  have hxnotL : x ∉ lineTrace cfg a b := mem_outsiders.mp hxO
  have hxnotu : x ∉ u := by
    intro hxu
    exact hxnotL (huL hxu)
  rw [mem_noncollinearTriples]
  constructor
  · simp [tripleOfIndex, Finset.card_insert_of_notMem hxnotu, hucard]
  · obtain ⟨y, z, hyz, hu_eq⟩ := Finset.card_eq_two.mp hucard
    have hyL : y ∈ lineTrace cfg a b := huL (by simp [hu_eq])
    have hzL : z ∈ lineTrace cfg a b := huL (by simp [hu_eq])
    rw [hu_eq]
    unfold IsNoncollinear supportPoints
    rw [show tripleOfIndex ({y, z}, x) = {x, y, z} by simp [tripleOfIndex]]
    have himage :
        cfg '' (↑({x, y, z} : Finset α) : Set α) = {cfg x, cfg y, cfg z} := by
      ext p
      simp [eq_comm]
    rw [himage]
    exact noncollinear_of_two_mem_line_one_outside cfg hab hyz hyL hzL hxnotL

theorem familyB_subset_noncollinearTriples {α : Type*} [Fintype α]
    (cfg : Configuration α) (a b : α) :
    familyB cfg a b ⊆ noncollinearTriples cfg := by
  classical
  intro t ht
  rw [familyB] at ht
  rcases Finset.mem_image.mp ht with ⟨⟨u, x⟩, hindex, rfl⟩
  rw [familyBIndices] at hindex
  rcases Finset.mem_filter.mp hindex with ⟨hall, hgood⟩
  rw [familyBAllIndices] at hall
  rcases Finset.mem_product.mp hall with ⟨hu, hxL⟩
  change u ∈ (outsiders cfg a b).powersetCard 2 at hu
  change x ∈ lineTrace cfg a b at hxL
  rcases Finset.mem_powersetCard.mp hu with ⟨huO, hucard⟩
  have hxnotu : x ∉ u := by
    intro hxu
    exact (mem_outsiders.mp (huO hxu)) hxL
  rw [mem_noncollinearTriples]
  exact ⟨by simp [tripleOfIndex, Finset.card_insert_of_notMem hxnotu, hucard], hgood⟩

theorem tripleOfIndex_inter_line_of_A {α : Type*} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) {a b x : α} {u : Finset α}
    (hu : u ⊆ lineTrace cfg a b) (hx : x ∉ lineTrace cfg a b) :
    tripleOfIndex (u, x) ∩ lineTrace cfg a b = u := by
  classical
  ext z
  constructor
  · intro hz
    rcases Finset.mem_inter.mp hz with ⟨hzi, hzL⟩
    rcases Finset.mem_insert.mp (by simpa [tripleOfIndex] using hzi) with hzx | hzu
    · subst z
      exact False.elim (hx hzL)
    · exact hzu
  · intro hzu
    apply Finset.mem_inter.mpr
    exact ⟨by simp [tripleOfIndex, hzu], hu hzu⟩

theorem tripleOfIndex_inter_line_of_B {α : Type*} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) {a b x : α} {u : Finset α}
    (hu : u ⊆ outsiders cfg a b) (hx : x ∈ lineTrace cfg a b) :
    tripleOfIndex (u, x) ∩ lineTrace cfg a b = {x} := by
  classical
  ext z
  constructor
  · intro hz
    rcases Finset.mem_inter.mp hz with ⟨hzi, hzL⟩
    rcases Finset.mem_insert.mp (by simpa [tripleOfIndex] using hzi) with hzx | hzu
    · simp [hzx]
    · exact False.elim ((mem_outsiders.mp (hu hzu)) hzL)
  · intro hz
    have hzx : z = x := by simpa using hz
    subst z
    simp [tripleOfIndex, hx]

theorem familyA_disjoint_familyB {α : Type*} [Fintype α]
    (cfg : Configuration α) (a b : α) :
    Disjoint (familyA cfg a b) (familyB cfg a b) := by
  classical
  rw [Finset.disjoint_left]
  intro t htA htB
  rw [familyA] at htA
  rcases Finset.mem_image.mp htA with ⟨⟨u, x⟩, hAindex, hAt⟩
  rw [familyAIndices] at hAindex
  rcases Finset.mem_product.mp hAindex with ⟨huA, hxO⟩
  change u ∈ (lineTrace cfg a b).powersetCard 2 at huA
  change x ∈ outsiders cfg a b at hxO
  rcases Finset.mem_powersetCard.mp huA with ⟨huL, hucard⟩
  rw [familyB] at htB
  rcases Finset.mem_image.mp htB with ⟨⟨v, y⟩, hBindex, hBt⟩
  rw [familyBIndices] at hBindex
  have hBall := (Finset.mem_filter.mp hBindex).1
  rw [familyBAllIndices] at hBall
  rcases Finset.mem_product.mp hBall with ⟨hvB, hyL⟩
  change v ∈ (outsiders cfg a b).powersetCard 2 at hvB
  change y ∈ lineTrace cfg a b at hyL
  have hvO := (Finset.mem_powersetCard.mp hvB).1
  have hAinter := tripleOfIndex_inter_line_of_A cfg huL (mem_outsiders.mp hxO)
  have hBinter := tripleOfIndex_inter_line_of_B cfg hvO hyL
  have hueq : u = {y} := by
    calc
      u = tripleOfIndex (u, x) ∩ lineTrace cfg a b := hAinter.symm
      _ = t ∩ lineTrace cfg a b := by rw [hAt]
      _ = tripleOfIndex (v, y) ∩ lineTrace cfg a b := by rw [hBt]
      _ = {y} := hBinter
  have : u.card = 1 := by simp [hueq]
  omega

/-- Number of triples supplied by the two disjoint richest-line families. -/
def twoFamilyCount (m k : ℕ) : ℕ :=
  k * Nat.choose m 2 + Nat.choose k 2 * (m - 1)

theorem isNoncollinear_tripleOf_pair_iff {α : Type*} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (x p q : α) :
    IsNoncollinear cfg (tripleOfIndex ({p, q}, x)) ↔
      ¬Collinear ℝ ({cfg x, cfg p, cfg q} : Set Point2) := by
  classical
  unfold IsNoncollinear supportPoints
  have htriple : tripleOfIndex ({p, q}, x) = {x, p, q} := by
    ext z
    simp [tripleOfIndex]
  rw [htriple]
  have himage :
      cfg '' (↑({x, p, q} : Finset α) : Set α) = {cfg x, cfg p, cfg q} := by
    ext z
    simp [eq_comm]
  rw [himage]

theorem card_familyBBadIndices_le {α : Type*} [Fintype α]
    (cfg : Configuration α) {a b : α} (hab : a ≠ b) :
    (familyBBadIndices cfg a b).card ≤
      Nat.choose (outsiders cfg a b).card 2 := by
  classical
  rw [← Finset.card_powersetCard]
  apply Finset.card_le_card_of_injOn Prod.fst
  · intro r hr
    change r ∈ familyBBadIndices cfg a b at hr
    rw [familyBBadIndices] at hr
    have hall := (Finset.mem_filter.mp hr).1
    rw [familyBAllIndices] at hall
    exact (Finset.mem_product.mp hall).1
  · rintro ⟨u, x⟩ hxmem ⟨v, y⟩ hymem huv
    change u = v at huv
    subst v
    change (u, x) ∈ familyBBadIndices cfg a b at hxmem
    change (u, y) ∈ familyBBadIndices cfg a b at hymem
    rw [familyBBadIndices] at hxmem hymem
    rcases Finset.mem_filter.mp hxmem with ⟨hxall, hxbad⟩
    rcases Finset.mem_filter.mp hymem with ⟨hyall, hybad⟩
    rw [familyBAllIndices] at hxall hyall
    rcases Finset.mem_product.mp hxall with ⟨huPair, hxL⟩
    rcases Finset.mem_product.mp hyall with ⟨_, hyL⟩
    change u ∈ (outsiders cfg a b).powersetCard 2 at huPair
    change x ∈ lineTrace cfg a b at hxL
    change y ∈ lineTrace cfg a b at hyL
    rcases Finset.mem_powersetCard.mp huPair with ⟨huO, hucard⟩
    obtain ⟨p, q, hpq, hu_eq⟩ := Finset.card_eq_two.mp hucard
    rw [hu_eq] at hxbad hybad huO
    have hcolx : Collinear ℝ ({cfg x, cfg p, cfg q} : Set Point2) := by
      by_contra hnot
      exact hxbad ((isNoncollinear_tripleOf_pair_iff cfg x p q).2 hnot)
    have hcoly : Collinear ℝ ({cfg y, cfg p, cfg q} : Set Point2) := by
      by_contra hnot
      exact hybad ((isNoncollinear_tripleOf_pair_iff cfg y p q).2 hnot)
    have hpO : p ∈ outsiders cfg a b := huO (by simp)
    have hpx : p ∉ lineTrace cfg a b := mem_outsiders.mp hpO
    have hxBad : x ∈ badLinePoints cfg a b p q := by
      simp [badLinePoints, hxL, hcolx]
    have hyBad : y ∈ badLinePoints cfg a b p q := by
      simp [badLinePoints, hyL, hcoly]
    have hxy := (Finset.card_le_one.mp
      (badLinePoints_card_le_one cfg hab hpq hpx)) x hxBad y hyBad
    simp [hxy]

theorem card_familyBIndices_lower {α : Type*} [Fintype α]
    (cfg : Configuration α) {a b : α} (hab : a ≠ b) :
    Nat.choose (outsiders cfg a b).card 2 *
        ((lineTrace cfg a b).card - 1) ≤
      (familyBIndices cfg a b).card := by
  classical
  have hpartition :
      (familyBIndices cfg a b).card + (familyBBadIndices cfg a b).card =
        (familyBAllIndices cfg a b).card := by
    simpa [familyBIndices, familyBBadIndices] using
      (Finset.card_filter_add_card_filter_not
        (s := familyBAllIndices cfg a b)
        (p := fun r => IsNoncollinear cfg (tripleOfIndex r)))
  have hallcard :
      (familyBAllIndices cfg a b).card =
        Nat.choose (outsiders cfg a b).card 2 * (lineTrace cfg a b).card := by
    simp [familyBAllIndices, Finset.card_product]
  have hbad := card_familyBBadIndices_le cfg hab
  have hm : 1 ≤ (lineTrace cfg a b).card :=
    le_trans (by omega) (two_le_card_lineTrace cfg hab)
  have hsplit :
      Nat.choose (outsiders cfg a b).card 2 * (lineTrace cfg a b).card =
        Nat.choose (outsiders cfg a b).card 2 * ((lineTrace cfg a b).card - 1) +
          Nat.choose (outsiders cfg a b).card 2 := by
    have hm' : (lineTrace cfg a b).card = (lineTrace cfg a b).card - 1 + 1 := by
      omega
    calc
      Nat.choose (outsiders cfg a b).card 2 * (lineTrace cfg a b).card =
          Nat.choose (outsiders cfg a b).card 2 *
            ((lineTrace cfg a b).card - 1 + 1) := by rw [← hm']
      _ = Nat.choose (outsiders cfg a b).card 2 * ((lineTrace cfg a b).card - 1) +
          Nat.choose (outsiders cfg a b).card 2 := by ring
  rw [hallcard, hsplit] at hpartition
  omega

theorem card_familyB_lower {α : Type*} [Fintype α]
    (cfg : Configuration α) {a b : α} (hab : a ≠ b) :
    Nat.choose (outsiders cfg a b).card 2 *
        ((lineTrace cfg a b).card - 1) ≤
      (familyB cfg a b).card := by
  rw [card_familyB_eq_indices]
  exact card_familyBIndices_lower cfg hab

theorem twoFamilyCount_le_tau {α : Type*} [Fintype α]
    (cfg : Configuration α) {a b : α} (hab : a ≠ b) :
    twoFamilyCount (lineTrace cfg a b).card (outsiders cfg a b).card ≤ tau cfg := by
  classical
  have hB := card_familyB_lower cfg hab
  have hsum :
      (familyA cfg a b).card + (familyB cfg a b).card ≤ tau cfg := by
    calc
      (familyA cfg a b).card + (familyB cfg a b).card =
          (familyA cfg a b ∪ familyB cfg a b).card := by
        rw [Finset.card_union_of_disjoint (familyA_disjoint_familyB cfg a b)]
      _ ≤ (noncollinearTriples cfg).card := Finset.card_le_card <|
        Finset.union_subset (familyA_subset_noncollinearTriples cfg hab)
          (familyB_subset_noncollinearTriples cfg a b)
      _ = tau cfg := rfl
  calc
    twoFamilyCount (lineTrace cfg a b).card (outsiders cfg a b).card =
        (familyA cfg a b).card +
          Nat.choose (outsiders cfg a b).card 2 * ((lineTrace cfg a b).card - 1) := by
      rw [card_familyA]
      simp [twoFamilyCount, Nat.mul_comm]
    _ ≤ (familyA cfg a b).card + (familyB cfg a b).card :=
      Nat.add_le_add_left hB _
    _ ≤ tau cfg := hsum

/-- A division-free form of `choose n 2`. -/
theorem two_mul_choose_two (n : ℕ) :
    2 * Nat.choose n 2 = n * (n - 1) := by
  have h := Nat.choose_succ_right_eq n 1
  simpa [Nat.choose_one_right, Nat.mul_comm] using h

/-- Exact doubled polynomial form of the two-family count. -/
theorem two_mul_twoFamilyCount (m k : ℕ) :
    2 * twoFamilyCount m k =
      k * (m * (m - 1)) + (k * (k - 1)) * (m - 1) := by
  calc
    2 * twoFamilyCount m k =
        k * (2 * Nat.choose m 2) +
          (2 * Nat.choose k 2) * (m - 1) := by
            simp only [twoFamilyCount]
            ring
    _ = k * (m * (m - 1)) + (k * (k - 1)) * (m - 1) := by
      rw [two_mul_choose_two, two_mul_choose_two]

/-- The doubled gap identity, stated in naturals so no truncated division is
hidden in the formal lower bound. -/
theorem twoFamily_gap_identity (m k : ℕ) (hm : 2 ≤ m) (hk : 1 ≤ k) :
    2 * twoFamilyCount m k =
      2 * Nat.choose (m + k - 1) 2 +
        (m + k - 1) * (k - 1) * (m - 2) := by
  let m₀ := m - 2
  let k₀ := k - 1
  have hm0 : m = m₀ + 2 := by
    dsimp [m₀]
    omega
  have hk0 : k = k₀ + 1 := by
    dsimp [k₀]
    omega
  have hm1 : m - 1 = m₀ + 1 := by
    dsimp [m₀]
    omega
  have hk1 : k - 1 = k₀ := by rfl
  have hm2 : m - 2 = m₀ := by rfl
  have hn1 : m + k - 1 = m₀ + k₀ + 2 := by omega
  have hn2 : m + k - 1 - 1 = m₀ + k₀ + 1 := by omega
  rw [two_mul_twoFamilyCount, two_mul_choose_two]
  rw [hn2, hn1, hm1, hk1, hm2, hm0, hk0]
  ring

/-- The arithmetic lower bound used after constructing the two disjoint
families of noncollinear triples. -/
theorem target_le_twoFamilyCount (m k : ℕ) (hm : 2 ≤ m) (hk : 1 ≤ k) :
    Nat.choose (m + k - 1) 2 ≤ twoFamilyCount m k := by
  have hdouble :
      2 * Nat.choose (m + k - 1) 2 ≤ 2 * twoFamilyCount m k := by
    rw [twoFamily_gap_identity m k hm hk]
    exact Nat.le_add_right _ _
  omega

/-- Equality in the arithmetic sandwich forces the near-pencil branch
`k = 1` or the general-position branch `m = 2`. -/
theorem twoFamilyCount_eq_target_forces (m k : ℕ)
    (hm : 2 ≤ m) (hk : 1 ≤ k)
    (heq : twoFamilyCount m k = Nat.choose (m + k - 1) 2) :
    k = 1 ∨ m = 2 := by
  have hgap := twoFamily_gap_identity m k hm hk
  rw [heq] at hgap
  have hzero : (m + k - 1) * (k - 1) * (m - 2) = 0 := by omega
  rcases Nat.mul_eq_zero.mp hzero with hleft | hm2
  · rcases Nat.mul_eq_zero.mp hleft with hmk | hk1
    · exfalso
      omega
    · left
      omega
  · right
    omega

/-- The richest-line lower bound once the chosen pair-line has at least one
outsider. -/
theorem target_le_tau_of_pair {α : Type*} [Fintype α]
    (cfg : Configuration α) {a b : α} (hab : a ≠ b)
    (hk : 1 ≤ (outsiders cfg a b).card) :
    Nat.choose (Fintype.card α - 1) 2 ≤ tau cfg := by
  let m := (lineTrace cfg a b).card
  let k := (outsiders cfg a b).card
  have hm : 2 ≤ m := two_le_card_lineTrace cfg hab
  have hmk : m + k = Fintype.card α := card_lineTrace_add_card_outsiders cfg a b
  calc
    Nat.choose (Fintype.card α - 1) 2 = Nat.choose (m + k - 1) 2 := by rw [hmk]
    _ ≤ twoFamilyCount m k := target_le_twoFamilyCount m k hm hk
    _ ≤ tau cfg := twoFamilyCount_le_tau cfg hab

theorem outsiders_nonempty_of_noncollinear {α : Type*} [Fintype α]
    (cfg : Configuration α) {a b : α} (hnon : Noncollinear cfg) :
    (outsiders cfg a b).Nonempty := by
  classical
  by_contra hO
  have hOempty : outsiders cfg a b = ∅ := Finset.not_nonempty_iff_eq_empty.mp hO
  apply hnon
  rw [collinear_iff_exists_forall_eq_smul_vadd]
  refine ⟨cfg a, cfg b -ᵥ cfg a, ?_⟩
  intro p hp
  rcases hp with ⟨x, rfl⟩
  have hxline : x ∈ lineTrace cfg a b := by
    by_contra hx
    have hxO : x ∈ outsiders cfg a b := mem_outsiders.mpr hx
    rw [hOempty] at hxO
    simp at hxO
  obtain ⟨r, hr⟩ := mem_affineSpan_pair_iff_exists_lineMap_eq.mp
    (mem_lineTrace.mp hxline)
  refine ⟨r, ?_⟩
  rw [← hr, AffineMap.lineMap_apply]

/-- Every finite noncollinear labelled configuration satisfies the complete
richest-line lower bound for noncollinear triples. -/
theorem tau_ge_target {α : Type*} [Fintype α]
    (cfg : Configuration α) (hcard : 2 ≤ Fintype.card α)
    (hnon : Noncollinear cfg) :
    Nat.choose (Fintype.card α - 1) 2 ≤ tau cfg := by
  obtain ⟨a, b, hab, _⟩ := exists_richest_pair cfg hcard
  exact target_le_tau_of_pair cfg hab
    (Finset.card_pos.mpr (outsiders_nonempty_of_noncollinear cfg hnon))

theorem support_noncollinear_of_all_pair_traces_le_two
    {α : Type*} [Fintype α] (cfg : Configuration α)
    (hsmall : ∀ x y, x ≠ y → (lineTrace cfg x y).card ≤ 2)
    {t : Finset α} (ht : t.card = 3) : IsNoncollinear cfg t := by
  classical
  obtain ⟨x, y, z, hxy, hxz, hyz, ht_eq⟩ := Finset.card_eq_three.mp ht
  rw [ht_eq]
  intro hcol
  unfold supportPoints at hcol
  have himage :
      cfg '' (↑({x, y, z} : Finset α) : Set α) = {cfg x, cfg y, cfg z} := by
    ext p
    simp [eq_comm]
  rw [himage] at hcol
  have hzline : z ∈ lineTrace cfg x y := by
    rw [mem_lineTrace]
    exact hcol.mem_affineSpan_of_mem_of_ne
      (by simp) (by simp) (by simp) (cfg.injective.ne hxy)
  have hsub : ({x, y, z} : Finset α) ⊆ lineTrace cfg x y := by
    intro p hp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with hp | hp | hp
    · simpa [hp] using left_mem_lineTrace cfg x y
    · simpa [hp] using right_mem_lineTrace cfg x y
    · simpa [hp] using hzline
  have hthree : 3 ≤ (lineTrace cfg x y).card := by
    have hcard : ({x, y, z} : Finset α).card = 3 := by
      rw [← ht_eq]
      exact ht
    rw [← hcard]
    exact Finset.card_le_card hsub
  have htwo := hsmall x y hxy
  omega

theorem tau_eq_choose_three_of_all_pair_traces_le_two
    {α : Type*} [Fintype α] (cfg : Configuration α)
    (hsmall : ∀ x y, x ≠ y → (lineTrace cfg x y).card ≤ 2) :
    tau cfg = Nat.choose (Fintype.card α) 3 := by
  classical
  have hsub : tripleSupports α ⊆ noncollinearTriples cfg := by
    intro t ht
    rw [mem_noncollinearTriples]
    have ht3 := mem_tripleSupports.mp ht
    exact ⟨ht3, support_noncollinear_of_all_pair_traces_le_two cfg hsmall ht3⟩
  have heq : noncollinearTriples cfg = tripleSupports α :=
    Finset.Subset.antisymm (Finset.filter_subset _ _) hsub
  rw [tau, heq, card_tripleSupports]

theorem choose_two_lt_choose_three (n : ℕ) (hn : 4 ≤ n) :
    Nat.choose (n - 1) 2 < Nat.choose n 3 := by
  have hpos : 0 < Nat.choose (n - 1) 3 := Nat.choose_pos (by omega)
  have hpascal :
      Nat.choose n 3 = Nat.choose (n - 1) 2 + Nat.choose (n - 1) 3 := by
    simpa [show n - 1 + 1 = n by omega] using Nat.choose_succ_succ (n - 1) 2
  omega

/-- Equality in the richest-line triple bound is possible only for a
near-pencil. -/
theorem tau_eq_target_implies_nearPencil {α : Type*} [Fintype α]
    (cfg : Configuration α) (hcard : 4 ≤ Fintype.card α)
    (hnon : Noncollinear cfg)
    (heq : tau cfg = Nat.choose (Fintype.card α - 1) 2) :
    NearPencil cfg := by
  obtain ⟨a, b, hab, hmax⟩ := exists_richest_pair cfg (by omega)
  let m := (lineTrace cfg a b).card
  let k := (outsiders cfg a b).card
  have hm : 2 ≤ m := two_le_card_lineTrace cfg hab
  have hk : 1 ≤ k := Finset.card_pos.mpr (outsiders_nonempty_of_noncollinear cfg hnon)
  have hmk : m + k = Fintype.card α := card_lineTrace_add_card_outsiders cfg a b
  have hlow := target_le_twoFamilyCount m k hm hk
  have hupp := twoFamilyCount_le_tau cfg hab
  change twoFamilyCount m k ≤ tau cfg at hupp
  have htarget : Nat.choose (m + k - 1) 2 = tau cfg := by
    rw [hmk, heq]
  have htwoEq : twoFamilyCount m k = Nat.choose (m + k - 1) 2 := by
    omega
  rcases twoFamilyCount_eq_target_forces m k hm hk htwoEq with hk1 | hm2
  · refine ⟨a, b, hab, ?_⟩
    dsimp [m, k] at hmk hk1 ⊢
    omega
  · have hsmall : ∀ x y, x ≠ y → (lineTrace cfg x y).card ≤ 2 := by
      intro x y hxy
      have hxymax := hmax x y hxy
      dsimp [m] at hm2
      omega
    have htau := tau_eq_choose_three_of_all_pair_traces_le_two cfg hsmall
    have hstrict := choose_two_lt_choose_three (Fintype.card α) hcard
    omega

theorem noncollinearTriples_subset_familyA_of_outsiders_singleton
    {α : Type*} [Fintype α] (cfg : Configuration α)
    {a b o : α} (ho : outsiders cfg a b = {o}) :
    noncollinearTriples cfg ⊆ familyA cfg a b := by
  classical
  intro t ht
  have ht3 := (mem_noncollinearTriples.mp ht).1
  have hot : o ∈ t := by
    by_contra hnot
    have htL : t ⊆ lineTrace cfg a b := by
      intro x hx
      by_contra hxL
      have hxO : x ∈ outsiders cfg a b := mem_outsiders.mpr hxL
      rw [ho] at hxO
      have hxo : x = o := by simpa using hxO
      exact hnot (hxo ▸ hx)
    have hcol : Collinear ℝ (supportPoints cfg t) := by
      rw [collinear_iff_exists_forall_eq_smul_vadd]
      refine ⟨cfg a, cfg b -ᵥ cfg a, ?_⟩
      intro p hp
      rcases hp with ⟨x, hx, rfl⟩
      obtain ⟨r, hr⟩ := mem_affineSpan_pair_iff_exists_lineMap_eq.mp
        (mem_lineTrace.mp (htL hx))
      exact ⟨r, by rw [← hr, AffineMap.lineMap_apply]⟩
    exact (mem_noncollinearTriples.mp ht).2 hcol
  let u := t.erase o
  have hucard : u.card = 2 := by
    dsimp [u]
    rw [Finset.card_erase_of_mem hot, ht3]
  have huL : u ⊆ lineTrace cfg a b := by
    intro x hxu
    have hxt : x ∈ t := Finset.mem_of_mem_erase hxu
    have hxo : x ≠ o := Finset.ne_of_mem_erase hxu
    by_contra hxL
    have hxO : x ∈ outsiders cfg a b := mem_outsiders.mpr hxL
    rw [ho] at hxO
    exact hxo (by simpa using hxO)
  have hoO : o ∈ outsiders cfg a b := by simp [ho]
  have hindex : (u, o) ∈ familyAIndices cfg a b := by
    rw [familyAIndices, Finset.mem_product]
    exact ⟨Finset.mem_powersetCard.mpr ⟨huL, hucard⟩, hoO⟩
  rw [familyA]
  apply Finset.mem_image.mpr
  refine ⟨(u, o), hindex, ?_⟩
  dsimp [u]
  ext x
  simp [tripleOfIndex, hot]

theorem tau_eq_target_of_nearPencil {α : Type*} [Fintype α]
    (cfg : Configuration α) (hcard : 4 ≤ Fintype.card α)
    (hnear : NearPencil cfg) :
    tau cfg = Nat.choose (Fintype.card α - 1) 2 := by
  classical
  rcases hnear with ⟨a, b, hab, hline⟩
  have hsum := card_lineTrace_add_card_outsiders cfg a b
  have hOcard : (outsiders cfg a b).card = 1 := by omega
  obtain ⟨o, ho⟩ := Finset.card_eq_one.mp hOcard
  have heq : noncollinearTriples cfg = familyA cfg a b :=
    Finset.Subset.antisymm
      (noncollinearTriples_subset_familyA_of_outsiders_singleton cfg ho)
      (familyA_subset_noncollinearTriples cfg hab)
  rw [tau, heq, card_familyA, hline, hOcard]
  simp

theorem noncollinear_of_nearPencil {α : Type*} [Fintype α]
    (cfg : Configuration α) (hcard : 4 ≤ Fintype.card α)
    (hnear : NearPencil cfg) : Noncollinear cfg := by
  classical
  rcases hnear with ⟨a, b, hab, hline⟩
  have hsum := card_lineTrace_add_card_outsiders cfg a b
  have hOcard : (outsiders cfg a b).card = 1 := by omega
  obtain ⟨o, ho⟩ := Finset.card_eq_one.mp hOcard
  have hoO : o ∈ outsiders cfg a b := by simp [ho]
  intro hcol
  have homem : cfg o ∈ affineSpan ℝ ({cfg a, cfg b} : Set Point2) :=
    hcol.mem_affineSpan_of_mem_of_ne
      ⟨a, rfl⟩ ⟨b, rfl⟩ ⟨o, rfl⟩ (cfg.injective.ne hab)
  exact (mem_outsiders.mp hoO) (mem_lineTrace.mpr homem)

end Erdos506.V4
