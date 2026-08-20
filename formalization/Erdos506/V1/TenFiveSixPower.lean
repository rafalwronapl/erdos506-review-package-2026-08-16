import Erdos506.Finite.SixFiveCanonical
import Erdos506.V1.PivotGeometry
import Erdos506.V1.TenFiveGeometry
import Erdos506.V3.TrianglePower
import Mathlib.Geometry.Euclidean.Projection

/-!
# The six-five power coordinates at the ten-point wall

Equality in the abstract five-block packing bound first gives the classified
six-by-five incidence design.  Inversion at its canonical `012` point turns
the three incident generalized blocks into the sides of a triangle.  Each
of the other three generalized blocks becomes a proper circle.  The latter
statement also covers an original line missing the inversion centre, using
reflection in that line and Mathlib's inversion-of-hyperplane theorem.

The final theorem returns the six directed power equations themselves.  It
does not invoke their later algebraic consequence.
-/

namespace Erdos506.V1

open Erdos506.Block
open Erdos506.Block.BlockSystem
open Erdos506.Finite
open Erdos506.Incidence
open Erdos506.V3
open Erdos506.V4
open AffineSubspace

universe u

/-! ## The abstract equality design -/

/-- The five-block layer of an abstract block system, bundled as a type. -/
abbrev SixFiveBlock
    {Point Block : Type*} [Fintype Point] [Fintype Block]
    [DecidableEq Point] [DecidableEq Block]
    (S : BlockSystem Point Block) :=
  {b : Block // b ∈ S.blocksOfSize 5}

/-- Six five-blocks on ten points form the exact design consumed by the
checked canonical classifier. -/
noncomputable def sixFiveDesignOfBlockSystem
    {Point Block : Type*} [Fintype Point] [Fintype Block]
    [DecidableEq Point] [DecidableEq Block]
    (S : BlockSystem Point Block)
    (hPoint : Fintype.card Point = 10)
    (hSix : S.blockCount 5 = 6) :
    SixFiveDesign Point (SixFiveBlock S) := by
  classical
  let support : SixFiveBlock S → Finset Point := fun b => S.support b.1
  have hB : (Finset.univ : Finset (SixFiveBlock S)).card = 6 := by
    rw [Finset.card_univ, Fintype.card_coe]
    exact hSix
  have hcard : ∀ b ∈ (Finset.univ : Finset (SixFiveBlock S)),
      (support b).card = 5 := by
    intro b _hb
    exact S.mem_blocksOfSize.mp b.2
  have hinter : ∀ b ∈ (Finset.univ : Finset (SixFiveBlock S)),
      ∀ c ∈ (Finset.univ : Finset (SixFiveBlock S)), b ≠ c →
        (support b ∩ support c).card ≤ 2 := by
    intro b _hb c _hc hbc
    have hbc' : b.1 ≠ c.1 := by
      intro h
      exact hbc (Subtype.ext h)
    have hlt := S.distinct_block_inter_card_lt_three hbc'
    exact Nat.le_of_lt_succ hlt
  have hdegree :=
    incidenceDegree_eq_three_of_six_five_subsets_card_ten_inter_le_two
      (Finset.univ : Finset (SixFiveBlock S)) support
      hPoint hB hcard hinter
  have hpairs :=
    inter_eq_two_of_six_five_subsets_card_ten_inter_le_two
      (Finset.univ : Finset (SixFiveBlock S)) support
      hPoint hB hcard hinter
  exact {
    support := support
    point_card := hPoint
    block_card := by
      rw [Fintype.card_coe]
      exact hSix
    support_card := by
      intro b
      exact S.mem_blocksOfSize.mp b.2
    profile_card := by
      intro x
      rw [Finset.card_eq_sum_ones, Finset.sum_filter]
      simpa [incidenceDegree, incidenceIndicator, support] using hdegree x
    pair_inter_card := by
      intro b c hbc
      exact hpairs b (by simp) c (by simp) hbc }

@[simp] theorem sixFiveDesignOfBlockSystem_support
    {Point Block : Type*} [Fintype Point] [Fintype Block]
    [DecidableEq Point] [DecidableEq Block]
    (S : BlockSystem Point Block)
    (hPoint : Fintype.card Point = 10)
    (hSix : S.blockCount 5 = 6)
    (b : SixFiveBlock S) :
    (sixFiveDesignOfBlockSystem S hPoint hSix).support b = S.support b.1 :=
  rfl

/-! ## Inverting generalized blocks -/

/-- A determined affine line is nonempty, as witnessed by either label of
one of its spanning selected pairs. -/
@[reducible] noncomputable def determinedLineNonempty
    {α : Type*} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (L : DeterminedLine cfg) : Nonempty L.1 := by
  classical
  obtain ⟨A, hA⟩ := L.exists_pair
  have hApos : A.1.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨a, ha⟩ := hApos
  let L' : DeterminedLine cfg :=
    ⟨lineOfPair cfg A, lineOfPair_mem_determinedLines cfg A⟩
  have haL' : a ∈ lineSupport cfg L' := pair_subset_lineSupport cfg A ha
  have haGeom : cfg a ∈ lineOfPair cfg A := mem_lineSupport.mp haL'
  rw [hA] at haGeom
  exact ⟨⟨cfg a, haGeom⟩⟩

/-- The proper circle obtained by inverting a determined line that misses
the inversion centre.  Reflection supplies the second focus whose
perpendicular bisector is the original line. -/
noncomputable def invertedDeterminedLineCircle
    {α : Type*} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (p : α) (L : DeterminedLine cfg)
    (hp : p ∉ lineSupport cfg L) : ProperCircle := by
  letI : Nonempty L.1 := determinedLineNonempty cfg L
  let y : Point2 := EuclideanGeometry.reflection L.1 (cfg p)
  have hpGeom : cfg p ∉ L.1 := by
    intro h
    exact hp (mem_lineSupport.mpr h)
  have hy : y ≠ cfg p := by
    intro h
    exact hpGeom ((EuclideanGeometry.reflection_eq_self_iff
      (s := L.1) (cfg p)).mp h)
  exact ⟨⟨EuclideanGeometry.inversion (cfg p) 1 y,
      1 / dist y (cfg p)⟩, one_div_pos.mpr (dist_pos.mpr hy)⟩

/-- Every selected point on a line missing the pivot lands on the proper
circle constructed above. -/
theorem inversion_mem_invertedDeterminedLineCircle
    {α : Type*} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (p : α) (L : DeterminedLine cfg)
    (hp : p ∉ lineSupport cfg L) (x : α)
    (hx : x ∈ lineSupport cfg L) :
    EuclideanGeometry.inversion (cfg p) 1 (cfg x) ∈
      ((invertedDeterminedLineCircle cfg p L hp).1 : Set Point2) := by
  letI : Nonempty L.1 := determinedLineNonempty cfg L
  let y : Point2 := EuclideanGeometry.reflection L.1 (cfg p)
  have hpGeom : cfg p ∉ L.1 := by
    intro h
    exact hp (mem_lineSupport.mpr h)
  have hy : y ≠ cfg p := by
    intro h
    exact hpGeom ((EuclideanGeometry.reflection_eq_self_iff
      (s := L.1) (cfg p)).mp h)
  have hxLine : cfg x ∈ L.1 := mem_lineSupport.mp hx
  have hdist : dist (cfg x) y = dist (cfg x) (cfg p) :=
    EuclideanGeometry.dist_reflection_eq_of_mem L.1 hxLine (cfg p)
  have hxPerp : cfg x ∈ perpBisector (cfg p) y :=
    mem_perpBisector_iff_dist_eq.mpr hdist.symm
  have himage :
      EuclideanGeometry.inversion (cfg p) 1 (cfg x) ∈
        EuclideanGeometry.inversion (cfg p) 1 '' perpBisector (cfg p) y :=
    ⟨cfg x, hxPerp, rfl⟩
  rw [EuclideanGeometry.image_inversion_perpBisector one_ne_zero hy] at himage
  simpa [invertedDeterminedLineCircle, y] using himage.1

/-- A generalized block missing the pivot becomes a proper circle after
inversion, whether it was originally a circle or a line. -/
noncomputable def invertedAwayGeometricBlockCircle
    {α : Type*} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (p : α) (b : GeometricBlock cfg)
    (hp : p ∉ geometricBlockSupport cfg b) : ProperCircle := by
  cases b with
  | inl L =>
      exact invertedDeterminedLineCircle cfg p L (by
        simpa [geometricBlockSupport] using hp)
  | inr c =>
      exact invertedProperCircle (cfg p) c.1 (by
        intro h
        apply hp
        simpa [geometricBlockSupport] using (mem_circleTrace.mpr h))

/-- Membership dictionary for a generalized block missing the pivot. -/
theorem inversion_mem_invertedAwayGeometricBlockCircle
    {α : Type*} [Fintype α] [DecidableEq α]
    (cfg : Configuration α) (p : α) (b : GeometricBlock cfg)
    (hp : p ∉ geometricBlockSupport cfg b) (x : α)
    (hx : x ∈ geometricBlockSupport cfg b) :
    EuclideanGeometry.inversion (cfg p) 1 (cfg x) ∈
      ((invertedAwayGeometricBlockCircle cfg p b hp).1 : Set Point2) := by
  cases b with
  | inl L =>
      simpa [invertedAwayGeometricBlockCircle, geometricBlockSupport] using
        inversion_mem_invertedDeterminedLineCircle cfg p L
          (by simpa [geometricBlockSupport] using hp) x
          (by simpa [geometricBlockSupport] using hx)
  | inr c =>
      have hp' : cfg p ∉ (c.1.1 : Set Point2) := by
        intro h
        apply hp
        simpa [geometricBlockSupport] using (mem_circleTrace.mpr h)
      have hx' : cfg x ∈ (c.1.1 : Set Point2) :=
        mem_circleTrace.mp (by simpa [geometricBlockSupport] using hx)
      simpa [invertedAwayGeometricBlockCircle, geometricBlockSupport] using
        inversion_mem_invertedProperCircle (cfg p) (cfg x) c.1 hp' hx'

/-! ## Positive coordinate extraction -/

/-- Three points on a one-dimensional affine subspace parametrise every
other point on that subspace. -/
theorem exists_affineParamPoint_of_mem_affineLine
    (L : AffineSubspace ℝ Point2)
    (hfin : Module.finrank ℝ L.direction = 1)
    {A B X : Point2} (hAB : A ≠ B)
    (hA : A ∈ L) (hB : B ∈ L) (hX : X ∈ L) :
    ∃ t : ℝ, affineParamPoint A (B - A) t = X := by
  let l : AffineSubspace ℝ Point2 := line[ℝ, A, B]
  have hle : l ≤ L := affineSpan_pair_le_of_mem_of_mem hA hB
  have hdirle : l.direction ≤ L.direction := AffineSubspace.direction_le hle
  have hlfin : Module.finrank ℝ l.direction = 1 := by
    dsimp [l]
    rw [direction_affineSpan ℝ ({A, B} : Set Point2), vectorSpan_pair_rev]
    exact finrank_span_singleton (sub_ne_zero.mpr hAB.symm)
  have hdirection : l.direction = L.direction :=
    Submodule.eq_of_le_of_finrank_eq hdirle (hlfin.trans hfin.symm)
  have hlL : l = L := AffineSubspace.eq_of_direction_eq_of_nonempty_of_le
    hdirection ⟨A, left_mem_affineSpan_pair ℝ A B⟩ hle
  have hXline : X ∈ line[ℝ, A, B] := by
    change X ∈ l
    rw [hlL]
    exact hX
  obtain ⟨t, ht⟩ := mem_affineSpan_pair_iff_exists_lineMap_eq.mp hXline
  exact ⟨t, (affineParamPoint_eq_lineMap A B t).trans ht⟩

/-- The post-inversion triangle picture produces exactly the positive
coordinate record used by the reduction interface. -/
noncomputable def sixFivePowerData_of_triangle_pattern
    (A B C : Point2) (hAB : A ≠ B) (hAC : A ≠ C) (hBC : B ≠ C)
    {x y u v w z : ℝ}
    (hxy : DistinctSideParameters x y)
    (huv : DistinctSideParameters u v)
    (hwz : DistinctSideParameters w z)
    (Γ₄ Γ₅ Γ₆ : ProperCircle)
    (h4A : A ∈ (Γ₄.1 : Set Point2))
    (h4X : affineParamPoint A (B - A) x ∈ (Γ₄.1 : Set Point2))
    (h4U : affineParamPoint A (C - A) u ∈ (Γ₄.1 : Set Point2))
    (h4W : affineParamPoint B (C - B) w ∈ (Γ₄.1 : Set Point2))
    (h4Z : affineParamPoint B (C - B) z ∈ (Γ₄.1 : Set Point2))
    (h5B : B ∈ (Γ₅.1 : Set Point2))
    (h5Y : affineParamPoint A (B - A) y ∈ (Γ₅.1 : Set Point2))
    (h5U : affineParamPoint A (C - A) u ∈ (Γ₅.1 : Set Point2))
    (h5V : affineParamPoint A (C - A) v ∈ (Γ₅.1 : Set Point2))
    (h5W : affineParamPoint B (C - B) w ∈ (Γ₅.1 : Set Point2))
    (h6C : C ∈ (Γ₆.1 : Set Point2))
    (h6X : affineParamPoint A (B - A) x ∈ (Γ₆.1 : Set Point2))
    (h6Y : affineParamPoint A (B - A) y ∈ (Γ₆.1 : Set Point2))
    (h6V : affineParamPoint A (C - A) v ∈ (Γ₆.1 : Set Point2))
    (h6Z : affineParamPoint B (C - B) z ∈ (Γ₆.1 : Set Point2)) :
    SixFivePowerData := by
  rcases hxy with ⟨hx0, hx1, hy0, hy1, hxy⟩
  rcases huv with ⟨hu0, hu1, hv0, hv1, huv⟩
  rcases hwz with ⟨hw0, hw1, hz0, hz1, hwz⟩
  let a2 := directionSq (C - B)
  let b2 := directionSq (C - A)
  let c2 := directionSq (B - A)
  have ha2 : a2 ≠ 0 := directionSq_sub_ne_zero hBC.symm
  have hb2 : b2 ≠ 0 := directionSq_sub_ne_zero hAC.symm
  have hc2 : c2 ≠ 0 := directionSq_sub_ne_zero hAB.symm
  have h1 : c2 * (1 - x) = a2 * w * z := by
    have hp := directed_power_of_four_cocircular_points Γ₄ B (A - B) (C - B)
      (show (1 : ℝ) ≠ 1 - x by
        intro h
        apply hx0
        linarith)
      hwz
      (by simpa using h4A)
      (by simpa [affineParamPoint_reverse] using h4X)
      h4W h4Z
    simpa [a2, c2, directionSq_sub_comm] using hp
  have h2 : b2 * (1 - u) = a2 * (1 - w) * (1 - z) := by
    have hp := directed_power_of_four_cocircular_points Γ₄ C (A - C) (B - C)
      (show (1 : ℝ) ≠ 1 - u by
        intro h
        apply hu0
        linarith)
      (show (1 - w : ℝ) ≠ 1 - z by
        intro h
        apply hwz
        linarith)
      (by simpa using h4A)
      (by simpa [affineParamPoint_reverse] using h4U)
      (by simpa [affineParamPoint_reverse] using h4W)
      (by simpa [affineParamPoint_reverse] using h4Z)
    simpa [a2, b2, directionSq_sub_comm] using hp
  have h3 : c2 * y = b2 * u * v := by
    have hp := directed_power_of_four_cocircular_points Γ₅ A (B - A) (C - A)
      (show (1 : ℝ) ≠ y by exact hy1.symm)
      huv
      (by simpa using h5B)
      h5Y h5U h5V
    simpa [b2, c2] using hp
  have h4 : a2 * (1 - w) = b2 * (1 - u) * (1 - v) := by
    have hp := directed_power_of_four_cocircular_points Γ₅ C (B - C) (A - C)
      (show (1 : ℝ) ≠ 1 - w by
        intro h
        apply hw0
        linarith)
      (show (1 - u : ℝ) ≠ 1 - v by
        intro h
        apply huv
        linarith)
      (by simpa using h5B)
      (by simpa [affineParamPoint_reverse] using h5W)
      (by simpa [affineParamPoint_reverse] using h5U)
      (by simpa [affineParamPoint_reverse] using h5V)
    simpa [a2, b2, directionSq_sub_comm] using hp
  have h5 : c2 * x * y = b2 * v := by
    have hp := directed_power_of_four_cocircular_points Γ₆ A (B - A) (C - A)
      hxy
      (show (1 : ℝ) ≠ v by exact hv1.symm)
      h6X h6Y
      (by simpa using h6C)
      h6V
    simpa [b2, c2] using hp
  have h6 : c2 * (1 - x) * (1 - y) = a2 * z := by
    have hp := directed_power_of_four_cocircular_points Γ₆ B (A - B) (C - B)
      (show (1 - x : ℝ) ≠ 1 - y by
        intro h
        apply hxy
        linarith)
      (show (1 : ℝ) ≠ z by exact hz1.symm)
      (by simpa [affineParamPoint_reverse] using h6X)
      (by simpa [affineParamPoint_reverse] using h6Y)
      (by simpa using h6C)
      h6Z
    simpa [a2, c2, directionSq_sub_comm] using hp
  exact {
    a2 := a2
    b2 := b2
    c2 := c2
    x := x
    y := y
    u := u
    v := v
    w := w
    z := z
    a2_ne_zero := ha2
    b2_ne_zero := hb2
    c2_ne_zero := hc2
    v_ne_zero := hv0
    z_ne_zero := hz0
    u_ne_one := hu1
    v_ne_one := hv1
    w_ne_one := hw1
    power_one := h1
    power_two := h2
    power_three := h3
    power_four := h4
    power_five := h5
    power_six := h6 }

/-! ## Configuration-level adapter -/

/-- The first field of the ten-point residual interface follows from the
existing canonical design, generalized pivot dictionary, and directed power
API. -/
noncomputable def finite_sixFivePowerCoordinates
    {α : Type u} [Fintype α] [DecidableEq α]
    (cfg : Configuration α)
    (_hadm : Admissible cfg)
    (hcard : Fintype.card α = 10)
    (_hcap : BlockSizeCap (blockSystem cfg) 5)
    (hsix : (blockSystem cfg).blockCount 5 = 6) :
    SixFivePowerData := by
  classical
  let S := blockSystem cfg
  have hSixS : S.blockCount 5 = 6 := by
    simpa [S] using hsix
  let D : SixFiveDesign α (SixFiveBlock S) :=
    sixFiveDesignOfBlockSystem S hcard hSixS
  let hlabeling :
      ∃ (P : Fin 10 ≃ α) (B : Fin 6 ≃ SixFiveBlock S),
        ∀ i, D.relabeledProfiles P B i = sixFiveCanonicalProfile i :=
    D.exists_canonical_labeling
  let P : Fin 10 ≃ α := Classical.choose hlabeling
  have hP :
      ∃ B : Fin 6 ≃ SixFiveBlock S,
        ∀ i, D.relabeledProfiles P B i = sixFiveCanonicalProfile i :=
    Classical.choose_spec hlabeling
  let B : Fin 6 ≃ SixFiveBlock S := Classical.choose hP
  have hcanonical :
      ∀ i, D.relabeledProfiles P B i = sixFiveCanonicalProfile i :=
    Classical.choose_spec hP
  let G : Fin 6 → GeometricBlock cfg := fun j => (B j).1
  have hGcard (j : Fin 6) : (geometricBlockSupport cfg (G j)).card = 5 := by
    have hj := (B j).2
    simpa [S, G, blockSystem, geometricBlockSystem] using
      ((S.mem_blocksOfSize).mp hj)
  have hinc (i : Fin 10) (j : Fin 6) :
      P i ∈ geometricBlockSupport cfg (G j) ↔
        j ∈ sixFiveCanonicalProfile i := by
    have hrel := D.mem_relabeledProfiles P B i j
    rw [hcanonical i] at hrel
    change j ∈ sixFiveCanonicalProfile i ↔
      P i ∈ (sixFiveDesignOfBlockSystem S hcard hSixS).support (B j) at hrel
    rw [sixFiveDesignOfBlockSystem_support] at hrel
    simpa [S, G] using hrel.symm
  let p : Fin 10 → Point2 := fun i => cfg (P i)
  have hp : Function.Injective p := cfg.injective.comp P.injective
  let I : Fin 10 → Point2 := fun i =>
    EuclideanGeometry.inversion (p 0) 1 (p i)
  have hIinj : Function.Injective I :=
    (EuclideanGeometry.inversion_injective (p 0) one_ne_zero).comp hp
  have hIne {i j : Fin 10} (hij : i ≠ j) : I i ≠ I j := hIinj.ne hij

  let PB₀ : PivotBlock cfg (P 0) :=
    ⟨G 0, (hinc 0 0).2 (by decide), by rw [hGcard]; omega⟩
  let PB₁ : PivotBlock cfg (P 0) :=
    ⟨G 1, (hinc 0 1).2 (by decide), by rw [hGcard]; omega⟩
  let PB₂ : PivotBlock cfg (P 0) :=
    ⟨G 2, (hinc 0 2).2 (by decide), by rw [hGcard]; omega⟩
  let L₀ := blockToPivotLine cfg (P 0) PB₀
  let L₁ := blockToPivotLine cfg (P 0) PB₁
  let L₂ := blockToPivotLine cfg (P 0) PB₂
  have hL₀ {i : Fin 10} (hi : i ≠ 0)
      (hprof : (0 : Fin 6) ∈ sixFiveCanonicalProfile i) : I i ∈ L₀.1 := by
    let q : AwayFrom (P 0) := ⟨P i, P.injective.ne hi⟩
    have hq : q ∈ lineSupport (pivotInversion cfg (P 0)) L₀ := by
      change q ∈ lineSupport (pivotInversion cfg (P 0))
        (blockToPivotLine cfg (P 0) PB₀)
      rw [lineSupport_blockToPivotLine]
      exact mem_awaySupport.mpr ((hinc i 0).2 hprof)
    simpa [I, p, pivotInversion, q] using mem_lineSupport.mp hq
  have hL₁ {i : Fin 10} (hi : i ≠ 0)
      (hprof : (1 : Fin 6) ∈ sixFiveCanonicalProfile i) : I i ∈ L₁.1 := by
    let q : AwayFrom (P 0) := ⟨P i, P.injective.ne hi⟩
    have hq : q ∈ lineSupport (pivotInversion cfg (P 0)) L₁ := by
      change q ∈ lineSupport (pivotInversion cfg (P 0))
        (blockToPivotLine cfg (P 0) PB₁)
      rw [lineSupport_blockToPivotLine]
      exact mem_awaySupport.mpr ((hinc i 1).2 hprof)
    simpa [I, p, pivotInversion, q] using mem_lineSupport.mp hq
  have hL₂ {i : Fin 10} (hi : i ≠ 0)
      (hprof : (2 : Fin 6) ∈ sixFiveCanonicalProfile i) : I i ∈ L₂.1 := by
    let q : AwayFrom (P 0) := ⟨P i, P.injective.ne hi⟩
    have hq : q ∈ lineSupport (pivotInversion cfg (P 0)) L₂ := by
      change q ∈ lineSupport (pivotInversion cfg (P 0))
        (blockToPivotLine cfg (P 0) PB₂)
      rw [lineSupport_blockToPivotLine]
      exact mem_awaySupport.mpr ((hinc i 2).2 hprof)
    simpa [I, p, pivotInversion, q] using mem_lineSupport.mp hq

  let hxExists : ∃ t : ℝ,
      affineParamPoint (I 1) (I 2 - I 1) t = I 4 :=
    exists_affineParamPoint_of_mem_affineLine
      (L := L₀.1) (A := I 1) (B := I 2) (X := I 4)
      L₀.direction_finrank (hIne (by decide))
      (hL₀ (by decide) (by decide)) (hL₀ (by decide) (by decide))
      (hL₀ (by decide) (by decide))
  let x : ℝ := Classical.choose hxExists
  have hx : affineParamPoint (I 1) (I 2 - I 1) x = I 4 :=
    Classical.choose_spec hxExists
  let hyExists : ∃ t : ℝ,
      affineParamPoint (I 1) (I 2 - I 1) t = I 5 :=
    exists_affineParamPoint_of_mem_affineLine
      (L := L₀.1) (A := I 1) (B := I 2) (X := I 5)
      L₀.direction_finrank (hIne (by decide))
      (hL₀ (by decide) (by decide)) (hL₀ (by decide) (by decide))
      (hL₀ (by decide) (by decide))
  let y : ℝ := Classical.choose hyExists
  have hy : affineParamPoint (I 1) (I 2 - I 1) y = I 5 :=
    Classical.choose_spec hyExists
  let huExists : ∃ t : ℝ,
      affineParamPoint (I 1) (I 3 - I 1) t = I 6 :=
    exists_affineParamPoint_of_mem_affineLine
      (L := L₁.1) (A := I 1) (B := I 3) (X := I 6)
      L₁.direction_finrank (hIne (by decide))
      (hL₁ (by decide) (by decide)) (hL₁ (by decide) (by decide))
      (hL₁ (by decide) (by decide))
  let u : ℝ := Classical.choose huExists
  have hu : affineParamPoint (I 1) (I 3 - I 1) u = I 6 :=
    Classical.choose_spec huExists
  let hvExists : ∃ t : ℝ,
      affineParamPoint (I 1) (I 3 - I 1) t = I 7 :=
    exists_affineParamPoint_of_mem_affineLine
      (L := L₁.1) (A := I 1) (B := I 3) (X := I 7)
      L₁.direction_finrank (hIne (by decide))
      (hL₁ (by decide) (by decide)) (hL₁ (by decide) (by decide))
      (hL₁ (by decide) (by decide))
  let v : ℝ := Classical.choose hvExists
  have hv : affineParamPoint (I 1) (I 3 - I 1) v = I 7 :=
    Classical.choose_spec hvExists
  let hwExists : ∃ t : ℝ,
      affineParamPoint (I 2) (I 3 - I 2) t = I 8 :=
    exists_affineParamPoint_of_mem_affineLine
      (L := L₂.1) (A := I 2) (B := I 3) (X := I 8)
      L₂.direction_finrank (hIne (by decide))
      (hL₂ (by decide) (by decide)) (hL₂ (by decide) (by decide))
      (hL₂ (by decide) (by decide))
  let w : ℝ := Classical.choose hwExists
  have hw : affineParamPoint (I 2) (I 3 - I 2) w = I 8 :=
    Classical.choose_spec hwExists
  let hzExists : ∃ t : ℝ,
      affineParamPoint (I 2) (I 3 - I 2) t = I 9 :=
    exists_affineParamPoint_of_mem_affineLine
      (L := L₂.1) (A := I 2) (B := I 3) (X := I 9)
      L₂.direction_finrank (hIne (by decide))
      (hL₂ (by decide) (by decide)) (hL₂ (by decide) (by decide))
      (hL₂ (by decide) (by decide))
  let z : ℝ := Classical.choose hzExists
  have hz : affineParamPoint (I 2) (I 3 - I 2) z = I 9 :=
    Classical.choose_spec hzExists
  have hxy : DistinctSideParameters x y :=
    distinctSideParameters_of_distinct_points
      (hIne (by decide)) (hIne (by decide))
      (hIne (by decide)) (hIne (by decide)) (hIne (by decide)) hx hy
  have huv : DistinctSideParameters u v :=
    distinctSideParameters_of_distinct_points
      (hIne (by decide)) (hIne (by decide))
      (hIne (by decide)) (hIne (by decide)) (hIne (by decide)) hu hv
  have hwz : DistinctSideParameters w z :=
    distinctSideParameters_of_distinct_points
      (hIne (by decide)) (hIne (by decide))
      (hIne (by decide)) (hIne (by decide)) (hIne (by decide)) hw hz

  have hO₄ : P 0 ∉ geometricBlockSupport cfg (G 3) := by
    intro h
    have := (hinc 0 3).mp h
    revert this
    decide
  have hO₅ : P 0 ∉ geometricBlockSupport cfg (G 4) := by
    intro h
    have := (hinc 0 4).mp h
    revert this
    decide
  have hO₆ : P 0 ∉ geometricBlockSupport cfg (G 5) := by
    intro h
    have := (hinc 0 5).mp h
    revert this
    decide
  let Γ₄ := invertedAwayGeometricBlockCircle cfg (P 0) (G 3) hO₄
  let Γ₅ := invertedAwayGeometricBlockCircle cfg (P 0) (G 4) hO₅
  let Γ₆ := invertedAwayGeometricBlockCircle cfg (P 0) (G 5) hO₆
  have hG₄ {i : Fin 10} (hi : (3 : Fin 6) ∈ sixFiveCanonicalProfile i) :
      I i ∈ (Γ₄.1 : Set Point2) := by
    simpa [I, p, Γ₄] using
      inversion_mem_invertedAwayGeometricBlockCircle
        cfg (P 0) (G 3) hO₄ (P i) ((hinc i 3).2 hi)
  have hG₅ {i : Fin 10} (hi : (4 : Fin 6) ∈ sixFiveCanonicalProfile i) :
      I i ∈ (Γ₅.1 : Set Point2) := by
    simpa [I, p, Γ₅] using
      inversion_mem_invertedAwayGeometricBlockCircle
        cfg (P 0) (G 4) hO₅ (P i) ((hinc i 4).2 hi)
  have hG₆ {i : Fin 10} (hi : (5 : Fin 6) ∈ sixFiveCanonicalProfile i) :
      I i ∈ (Γ₆.1 : Set Point2) := by
    simpa [I, p, Γ₆] using
      inversion_mem_invertedAwayGeometricBlockCircle
        cfg (P 0) (G 5) hO₆ (P i) ((hinc i 5).2 hi)

  apply sixFivePowerData_of_triangle_pattern (I 1) (I 2) (I 3)
    (hIne (by decide)) (hIne (by decide)) (hIne (by decide))
    hxy huv hwz Γ₄ Γ₅ Γ₆
  · exact hG₄ (by decide)
  · rw [hx]
    exact hG₄ (by decide)
  · rw [hu]
    exact hG₄ (by decide)
  · rw [hw]
    exact hG₄ (by decide)
  · rw [hz]
    exact hG₄ (by decide)
  · exact hG₅ (by decide)
  · rw [hy]
    exact hG₅ (by decide)
  · rw [hu]
    exact hG₅ (by decide)
  · rw [hv]
    exact hG₅ (by decide)
  · rw [hw]
    exact hG₅ (by decide)
  · exact hG₆ (by decide)
  · rw [hx]
    exact hG₆ (by decide)
  · rw [hy]
    exact hG₆ (by decide)
  · rw [hv]
    exact hG₆ (by decide)
  · rw [hz]
    exact hG₆ (by decide)

end Erdos506.V1
