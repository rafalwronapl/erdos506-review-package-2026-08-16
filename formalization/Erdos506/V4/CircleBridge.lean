import Erdos506.V4.RichestLine

/-!
# From noncollinear triples to proper circumcircles

Every unordered noncollinear triple is reindexed by `Fin 3` and bundled as an
affine 2-simplex.  Its circumsphere is a proper Euclidean circle.  Under the
V4 no-four-concyclic hypothesis, two different supports cannot have the same
circumcircle, so the determined-circle count equals `tau`.
-/

namespace Erdos506.V4

/-- An attached unordered noncollinear triple. -/
abbrev NoncollinearTriple {α : Type*} [Fintype α] (cfg : Configuration α) :=
  {t : Finset α // t ∈ noncollinearTriples cfg}

/-- Canonical finite reindexing of an attached three-support. -/
noncomputable def tripleEquiv {α : Type*} [Fintype α]
    {cfg : Configuration α} (t : NoncollinearTriple cfg) : ↥t.1 ≃ Fin 3 := by
  classical
  exact Finset.equivFinOfCardEq (mem_noncollinearTriples.mp t.2).1

/-- The three selected points in the canonical `Fin 3` order. -/
noncomputable def triplePoints {α : Type*} [Fintype α]
    (cfg : Configuration α) (t : NoncollinearTriple cfg) : Fin 3 → Point2 :=
  fun i => cfg ((tripleEquiv t).symm i).1

theorem range_triplePoints {α : Type*} [Fintype α]
    (cfg : Configuration α) (t : NoncollinearTriple cfg) :
    Set.range (triplePoints cfg t) = supportPoints cfg t.1 := by
  classical
  ext p
  constructor
  · rintro ⟨i, rfl⟩
    refine ⟨((tripleEquiv t).symm i).1, ((tripleEquiv t).symm i).2, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    let xt : ↥t.1 := ⟨x, hx⟩
    refine ⟨tripleEquiv t xt, ?_⟩
    simp [triplePoints, xt]

theorem triplePoints_affineIndependent {α : Type*} [Fintype α]
    (cfg : Configuration α) (t : NoncollinearTriple cfg) :
    AffineIndependent ℝ (triplePoints cfg t) := by
  rw [affineIndependent_iff_not_collinear, range_triplePoints]
  exact (mem_noncollinearTriples.mp t.2).2

/-- The affine triangle carried by an unordered noncollinear support. -/
noncomputable def tripleSimplex {α : Type*} [Fintype α]
    (cfg : Configuration α) (t : NoncollinearTriple cfg) :
    Affine.Simplex ℝ Point2 2 :=
  Affine.Simplex.mk (triplePoints cfg t) (triplePoints_affineIndependent cfg t)

/-- The proper Euclidean circumcircle of an unordered noncollinear support. -/
noncomputable def properCircumcircle {α : Type*} [Fintype α]
    (cfg : Configuration α) (t : NoncollinearTriple cfg) : ProperCircle := by
  refine ⟨(tripleSimplex cfg t).circumsphere, ?_⟩
  change 0 < (tripleSimplex cfg t).circumradius
  exact Affine.Simplex.circumradius_pos (tripleSimplex cfg t)

theorem support_mem_properCircumcircle {α : Type*} [Fintype α]
    (cfg : Configuration α) (t : NoncollinearTriple cfg) {x : α}
    (hx : x ∈ t.1) :
    cfg x ∈ ((properCircumcircle cfg t).1 : Set Point2) := by
  classical
  let xt : ↥t.1 := ⟨x, hx⟩
  let i : Fin 3 := tripleEquiv t xt
  have hi := Affine.Simplex.mem_circumsphere (tripleSimplex cfg t) i
  change triplePoints cfg t i ∈ (tripleSimplex cfg t).circumsphere at hi
  simpa [triplePoints, i, xt] using hi

/-- Reindexing the vertices of the attached triangle does not change its
circumcircle. -/
theorem properCircumcircle_reindex {α : Type*} [Fintype α]
    (cfg : Configuration α) (t : NoncollinearTriple cfg) (e : Fin 3 ≃ Fin 3) :
    ((tripleSimplex cfg t).reindex e).circumsphere =
      (properCircumcircle cfg t).1 := by
  simp [properCircumcircle]

/-- Finite image of the proper circumcircle map. -/
noncomputable def determinedCircles {α : Type*} [Fintype α]
    (cfg : Configuration α) : Finset ProperCircle := by
  classical
  exact (noncollinearTriples cfg).attach.image (properCircumcircle cfg)

/-- A proper circle containing an attached noncollinear triple is its unique
circumcircle. -/
theorem properCircle_eq_properCircumcircle_of_support {α : Type*} [Fintype α]
    (cfg : Configuration α) (t : NoncollinearTriple cfg) (c : ProperCircle)
    (ht : ∀ x ∈ t.1, cfg x ∈ (c.1 : Set Point2)) :
    c = properCircumcircle cfg t := by
  have hpoints :
      Set.range (tripleSimplex cfg t).points ⊆ (c.1 : Set Point2) := by
    intro p hp
    obtain ⟨i, rfl⟩ := hp
    simpa [tripleSimplex, triplePoints] using
      ht ((tripleEquiv t).symm i).1 ((tripleEquiv t).symm i).2
  have hspan :
      affineSpan ℝ (Set.range (tripleSimplex cfg t).points) = ⊤ :=
    (tripleSimplex cfg t).span_eq_top (by simp [Point2])
  have hcenter :
      c.1.center ∈ affineSpan ℝ (Set.range (tripleSimplex cfg t).points) := by
    rw [hspan]
    exact Set.mem_univ _
  have hsphere : c.1 = (tripleSimplex cfg t).circumsphere :=
    (tripleSimplex cfg t).circumsphere_unique_dist_eq.2 c.1 ⟨hcenter, hpoints⟩
  apply Subtype.ext
  exact hsphere

/-- Semantic characterization of the finite image: a proper circle is
counted exactly when it contains a selected noncollinear triple. -/
theorem mem_determinedCircles_iff {α : Type*} [Fintype α]
    (cfg : Configuration α) (c : ProperCircle) :
    c ∈ determinedCircles cfg ↔
      ∃ t : NoncollinearTriple cfg, ∀ x ∈ t.1, cfg x ∈ (c.1 : Set Point2) := by
  classical
  constructor
  · intro hc
    rw [determinedCircles] at hc
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hc
    refine ⟨t, ?_⟩
    intro x hx
    exact support_mem_properCircumcircle cfg t hx
  · rintro ⟨t, ht⟩
    have hcirc : c = properCircumcircle cfg t :=
      properCircle_eq_properCircumcircle_of_support cfg t c ht
    rw [hcirc, determinedCircles]
    exact Finset.mem_image.mpr ⟨t, by simp, rfl⟩

/-- Number of distinct proper circumcircles determined by selected
noncollinear triples. -/
noncomputable def circleCount {α : Type*} [Fintype α]
    (cfg : Configuration α) : ℕ :=
  (determinedCircles cfg).card

theorem four_le_card_union_of_distinct_triples {α : Type*} [DecidableEq α]
    {s t : Finset α} (hs : s.card = 3) (ht : t.card = 3) (hne : s ≠ t) :
    4 ≤ (s ∪ t).card := by
  classical
  have hinter : (s ∩ t).card ≤ 2 := by
    by_contra hnot
    have hthree : (s ∩ t).card = 3 := by
      have hle : (s ∩ t).card ≤ s.card := Finset.card_le_card Finset.inter_subset_left
      omega
    have hinter_s : s ∩ t = s :=
      Finset.eq_of_subset_of_card_le Finset.inter_subset_left (by omega)
    have hst : s ⊆ t := by
      intro x hx
      have hx' : x ∈ s ∩ t := by simpa [hinter_s] using hx
      exact (Finset.mem_inter.mp hx').2
    have hst_eq : s = t :=
      Finset.eq_of_subset_of_card_le hst (by omega)
    exact hne hst_eq
  have hunion := Finset.card_union_add_card_inter s t
  omega

theorem properCircumcircle_injective {α : Type*} [Fintype α]
    (cfg : Configuration α) (hfour : NoFourConcyclic cfg) :
    Function.Injective (properCircumcircle cfg) := by
  classical
  intro s t hcirc
  apply Subtype.ext
  by_contra hst
  have hs3 := (mem_noncollinearTriples.mp s.2).1
  have ht3 := (mem_noncollinearTriples.mp t.2).1
  have hfourUnion : 4 ≤ (s.1 ∪ t.1).card :=
    four_le_card_union_of_distinct_triples hs3 ht3 hst
  have hunion_sub : s.1 ∪ t.1 ⊆ circleTrace cfg (properCircumcircle cfg s) := by
    intro x hx
    rcases Finset.mem_union.mp hx with hxs | hxt
    · exact mem_circleTrace.mpr (support_mem_properCircumcircle cfg s hxs)
    · apply mem_circleTrace.mpr
      have hxmem := support_mem_properCircumcircle cfg t hxt
      rw [hcirc]
      exact hxmem
  have hunion_le : (s.1 ∪ t.1).card ≤
      (circleTrace cfg (properCircumcircle cfg s)).card :=
    Finset.card_le_card hunion_sub
  have htrace := hfour (properCircumcircle cfg s)
  omega

/-- Under the V4 cap, determined circles and noncollinear triples are in
bijection. -/
theorem circleCount_eq_tau {α : Type*} [Fintype α]
    (cfg : Configuration α) (hfour : NoFourConcyclic cfg) :
    circleCount cfg = tau cfg := by
  classical
  rw [circleCount, determinedCircles,
    Finset.card_image_of_injective _ (properCircumcircle_injective cfg hfour),
    Finset.card_attach]
  rfl

/-- Every near-pencil on at least four labels satisfies the no-four-
concyclic cap.  Three distinct points of its long line cannot lie on one
Euclidean sphere because cospherical triples are affinely independent. -/
theorem noFourConcyclic_of_nearPencil {α : Type*} [Fintype α]
    (cfg : Configuration α) (hcard : 4 ≤ Fintype.card α)
    (hnear : NearPencil cfg) : NoFourConcyclic cfg := by
  classical
  rcases hnear with ⟨a, b, hab, hline⟩
  have hsum := card_lineTrace_add_card_outsiders cfg a b
  have hOcard : (outsiders cfg a b).card = 1 := by omega
  intro c
  by_contra hnot
  have htrace4 : 4 ≤ (circleTrace cfg c).card := by omega
  have hsdiff_sub :
      circleTrace cfg c \ lineTrace cfg a b ⊆ outsiders cfg a b := by
    intro x hx
    exact mem_outsiders.mpr (Finset.mem_sdiff.mp hx).2
  have hsdiff_le :
      (circleTrace cfg c \ lineTrace cfg a b).card ≤ 1 := by
    have := Finset.card_le_card hsdiff_sub
    omega
  have hsplit := Finset.card_inter_add_card_sdiff
    (circleTrace cfg c) (lineTrace cfg a b)
  have hinter3 : 3 ≤ (circleTrace cfg c ∩ lineTrace cfg a b).card := by omega
  obtain ⟨u, hu, hucard⟩ := Finset.exists_subset_card_eq hinter3
  obtain ⟨x, y, z, hxy, hxz, hyz, hu_eq⟩ := Finset.card_eq_three.mp hucard
  have hxBoth : x ∈ circleTrace cfg c ∩ lineTrace cfg a b := hu (by simp [hu_eq])
  have hyBoth : y ∈ circleTrace cfg c ∩ lineTrace cfg a b := hu (by simp [hu_eq])
  have hzBoth : z ∈ circleTrace cfg c ∩ lineTrace cfg a b := hu (by simp [hu_eq])
  have hxC := mem_circleTrace.mp (Finset.mem_inter.mp hxBoth).1
  have hyC := mem_circleTrace.mp (Finset.mem_inter.mp hyBoth).1
  have hzC := mem_circleTrace.mp (Finset.mem_inter.mp hzBoth).1
  have hxL := mem_lineTrace.mp (Finset.mem_inter.mp hxBoth).2
  have hyL := mem_lineTrace.mp (Finset.mem_inter.mp hyBoth).2
  have hzL := mem_lineTrace.mp (Finset.mem_inter.mp hzBoth).2
  have hcol : Collinear ℝ ({cfg x, cfg y, cfg z} : Set Point2) :=
    collinear_triple_of_mem_affineSpan_pair hxL hyL hzL
  have hind : AffineIndependent ℝ ![cfg x, cfg y, cfg z] :=
    (EuclideanGeometry.Sphere.cospherical c.1).affineIndependent_of_mem_of_ne
      hxC hyC hzC (cfg.injective.ne hxy) (cfg.injective.ne hxz) (cfg.injective.ne hyz)
  exact (affineIndependent_iff_not_collinear_set.mp hind) hcol

/-- Near-pencils are V4-admissible, independently of their metric spacing. -/
theorem admissible_of_nearPencil {α : Type*} [Fintype α]
    (cfg : Configuration α) (hcard : 4 ≤ Fintype.card α)
    (hnear : NearPencil cfg) : Admissible cfg :=
  ⟨noncollinear_of_nearPencil cfg hcard hnear,
    noFourConcyclic_of_nearPencil cfg hcard hnear⟩

end Erdos506.V4
