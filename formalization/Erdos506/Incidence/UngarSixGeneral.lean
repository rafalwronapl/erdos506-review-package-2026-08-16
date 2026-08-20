import Erdos506.Finite.UngarSixWeightedIntervals
import Erdos506.Incidence.UngarSixProof

/-!
# Coordinate-free entry to the general six-point direction theorem

The rotating-line argument may use an affine coordinate whose abscissae are
all distinct.  This file constructs such a coordinate by an explicit shear
and proves that equality of the resulting secant slopes is exactly equality
of the projective directions already used by `determinedDirections`.

No general-position hypothesis is introduced: only the fifteen pair
differences have to avoid the vertical kernel, and a real shear parameter
outside a finite set always exists.
-/

namespace Erdos506.Incidence

open Erdos506.Finite
open Erdos506.V1
open Erdos506.V4

/-- First coordinate after the invertible shear `(x,y) ↦ (x+t*y,y)`. -/
def shearAbscissa (t : ℝ) (p : Point2) : ℝ :=
  p 0 + t * p 1

/-- The second coordinate is unchanged by the shear. -/
def shearOrdinate (p : Point2) : ℝ :=
  p 1

/-- Secant slope in the sheared coordinate. -/
noncomputable def shearSlope (t : ℝ) (p q : Point2) : ℝ :=
  (shearOrdinate q - shearOrdinate p) /
    (shearAbscissa t q - shearAbscissa t p)

/-- A finite set of forbidden shear parameters.  For a pair `(i,j)` its
listed value is the only possible zero of the sheared abscissa difference
when the ordinate difference is nonzero. -/
private noncomputable def forbiddenShears
    (cfg : Configuration (Fin 6)) : Finset ℝ :=
  Finset.univ.image fun ij : Fin 6 × Fin 6 =>
    -((cfg ij.2) 0 - (cfg ij.1) 0) /
      ((cfg ij.2) 1 - (cfg ij.1) 1)

/-- Six distinct points have an invertible shear after which all six
abscissae are different. -/
theorem exists_shearAbscissa_injective
    (cfg : Configuration (Fin 6)) :
    ∃ t : ℝ, Function.Injective (fun i => shearAbscissa t (cfg i)) := by
  classical
  have hinfinite :
      ((forbiddenShears cfg : Set ℝ)ᶜ).Infinite :=
    (forbiddenShears cfg).finite_toSet.infinite_compl
  obtain ⟨t, ht⟩ := hinfinite.nonempty
  have htbad : t ∉ forbiddenShears cfg := by
    exact ht
  refine ⟨t, ?_⟩
  intro i j hij
  by_contra hne
  let dx : ℝ := (cfg j) 0 - (cfg i) 0
  let dy : ℝ := (cfg j) 1 - (cfg i) 1
  have hsum : dx + t * dy = 0 := by
    dsimp [dx, dy, shearAbscissa] at *
    linarith
  by_cases hdy : dy = 0
  · apply hne
    apply cfg.injective
    have hdx : dx = 0 := by
      simpa [hdy] using hsum
    ext k
    fin_cases k
    · exact (sub_eq_zero.mp (by simpa [dx] using hdx)).symm
    · exact (sub_eq_zero.mp (by simpa [dy] using hdy)).symm
  · have htvalue : t = -dx / dy := by
      apply (eq_div_iff hdy).2
      linarith
    apply htbad
    apply Finset.mem_image.mpr
    refine ⟨(i, j), Finset.mem_univ _, ?_⟩
    exact htvalue.symm

/-- Distinct sheared abscissae make every displayed secant denominator
nonzero. -/
theorem shearAbscissa_sub_ne_zero
    {t : ℝ} {p q : Point2}
    (hpq : shearAbscissa t p ≠ shearAbscissa t q) :
    shearAbscissa t q - shearAbscissa t p ≠ 0 :=
  sub_ne_zero.mpr hpq.symm

/-- In an invertible sheared coordinate, two secants have equal real slopes
if and only if their one-dimensional projective direction subspaces agree. -/
theorem directionOfPoints_eq_iff_shearSlope_eq
    (t : ℝ) {p q r s : Point2}
    (hpq : shearAbscissa t p ≠ shearAbscissa t q)
    (hrs : shearAbscissa t r ≠ shearAbscissa t s) :
    directionOfPoints p q = directionOfPoints r s ↔
      shearSlope t p q = shearSlope t r s := by
  let Xpq : ℝ := shearAbscissa t q - shearAbscissa t p
  let Xrs : ℝ := shearAbscissa t s - shearAbscissa t r
  let Ypq : ℝ := shearOrdinate q - shearOrdinate p
  let Yrs : ℝ := shearOrdinate s - shearOrdinate r
  have hXpq : Xpq ≠ 0 := by
    exact shearAbscissa_sub_ne_zero hpq
  have hXrs : Xrs ≠ 0 := by
    exact shearAbscissa_sub_ne_zero hrs
  constructor
  · intro hdir
    unfold directionOfPoints at hdir
    rw [Submodule.span_singleton_eq_span_singleton] at hdir
    obtain ⟨u, hu⟩ := hdir
    have hu0 : (u : ℝ) * (q 0 - p 0) = s 0 - r 0 := by
      have h := congrArg (fun z : Point2 => z 0) hu
      simpa only [Units.smul_def, Pi.smul_apply, PiLp.smul_apply,
        PiLp.sub_apply, smul_eq_mul] using h
    have hu1 : (u : ℝ) * (q 1 - p 1) = s 1 - r 1 := by
      have h := congrArg (fun z : Point2 => z 1) hu
      simpa only [Units.smul_def, Pi.smul_apply, PiLp.smul_apply,
        PiLp.sub_apply, smul_eq_mul] using h
    have hY : (u : ℝ) * Ypq = Yrs := by
      simpa only [Ypq, Yrs, shearOrdinate] using hu1
    have hX : (u : ℝ) * Xpq = Xrs := by
      dsimp [Xpq, Xrs, shearAbscissa]
      linear_combination hu0 + t * hu1
    apply (div_eq_div_iff hXpq hXrs).2
    change Ypq * Xrs = Yrs * Xpq
    rw [← hX, ← hY]
    ring
  · intro hslope
    have hcross : Ypq * Xrs = Yrs * Xpq := by
      apply (div_eq_div_iff hXpq hXrs).mp
      simpa only [shearSlope, Xpq, Xrs, Ypq, Yrs,
        shearOrdinate] using hslope
    let c : ℝ := Xrs / Xpq
    have hc : c ≠ 0 := div_ne_zero hXrs hXpq
    have hX : c * Xpq = Xrs := by
      exact div_mul_cancel₀ Xrs hXpq
    have hY : c * Ypq = Yrs := by
      dsimp [c]
      field_simp [hXpq]
      nlinarith [hcross]
    unfold directionOfPoints
    rw [Submodule.span_singleton_eq_span_singleton]
    refine ⟨Units.mk0 c hc, ?_⟩
    ext k
    fin_cases k
    · change c * (q 0 - p 0) = s 0 - r 0
      dsimp [Xpq, Xrs, shearAbscissa] at hX
      dsimp [Ypq, Yrs, shearOrdinate] at hY
      linear_combination hX - t * hY
    · change c * (q 1 - p 1) = s 1 - r 1
      simpa only [Ypq, Yrs, shearOrdinate] using hY

/-! ## Sorting the six labels in the generic abscissa -/

/-- A private copy of the six labels, used so that the order transported from
the sheared abscissa does not compete with the standard order on `Fin 6`. -/
private structure ShearLabel where
  val : Fin 6

private def shearLabelEquiv : ShearLabel ≃ Fin 6 where
  toFun := ShearLabel.val
  invFun := fun i => ⟨i⟩
  left_inv := by intro i; cases i; rfl
  right_inv := by intro i; rfl

private instance : Fintype ShearLabel :=
  Fintype.ofEquiv (Fin 6) shearLabelEquiv.symm

/-- The six labels, increasingly enumerated by their sheared abscissa. -/
noncomputable def shearSortedLabel
    (cfg : Configuration (Fin 6)) (t : ℝ)
    (hinj : Function.Injective (fun i => shearAbscissa t (cfg i))) :
    Fin 6 ≃ Fin 6 := by
  classical
  let coord : ShearLabel → ℝ := fun i => shearAbscissa t (cfg i.val)
  have hcoord : Function.Injective coord := by
    rintro ⟨a⟩ ⟨b⟩ hab
    have hab' : a = b := hinj hab
    subst b
    rfl
  letI : LinearOrder ShearLabel := LinearOrder.lift' coord hcoord
  have hcard : Fintype.card ShearLabel = 6 := by
    simpa using Fintype.card_congr shearLabelEquiv
  exact (Fintype.orderIsoFinOfCardEq ShearLabel hcard).toEquiv.trans
    shearLabelEquiv

theorem shearSortedLabel_abscissa_lt_iff
    (cfg : Configuration (Fin 6)) (t : ℝ)
    (hinj : Function.Injective (fun i => shearAbscissa t (cfg i)))
    (i j : Fin 6) :
    shearAbscissa t (cfg (shearSortedLabel cfg t hinj i)) <
      shearAbscissa t (cfg (shearSortedLabel cfg t hinj j)) ↔ i < j := by
  classical
  let coord : ShearLabel → ℝ := fun k => shearAbscissa t (cfg k.val)
  have hcoord : Function.Injective coord := by
    rintro ⟨a⟩ ⟨b⟩ hab
    have hab' : a = b := hinj hab
    subst b
    rfl
  letI : LinearOrder ShearLabel := LinearOrder.lift' coord hcoord
  have hcard : Fintype.card ShearLabel = 6 := by
    simpa using Fintype.card_congr shearLabelEquiv
  change ((Fintype.orderIsoFinOfCardEq ShearLabel hcard) i : ShearLabel) <
      (Fintype.orderIsoFinOfCardEq ShearLabel hcard) j ↔ i < j
  exact (Fintype.orderIsoFinOfCardEq ShearLabel hcard).lt_iff_lt

/-- The secant slope attached to one of the fifteen intervals in the
abscissa-sorted six-term row. -/
noncomputable def sixIntervalSlope
    (cfg : Configuration (Fin 6)) (t : ℝ)
    (hinj : Function.Injective (fun i => shearAbscissa t (cfg i)))
    (e : Fin 15) : ℝ :=
  shearSlope t
    (cfg (shearSortedLabel cfg t hinj (sixIntervalLeft e)))
    (cfg (shearSortedLabel cfg t hinj (sixIntervalRight e)))

/-- Projective direction of the same sorted-row interval. -/
noncomputable def sixIntervalDirection
    (cfg : Configuration (Fin 6)) (t : ℝ)
    (hinj : Function.Injective (fun i => shearAbscissa t (cfg i)))
    (e : Fin 15) : Submodule ℝ Point2 :=
  directionOfPoints
    (cfg (shearSortedLabel cfg t hinj (sixIntervalLeft e)))
    (cfg (shearSortedLabel cfg t hinj (sixIntervalRight e)))

/-- The finite slope census of the fifteen sorted-row intervals. -/
noncomputable def sixIntervalSlopes
    (cfg : Configuration (Fin 6)) (t : ℝ)
    (hinj : Function.Injective (fun i => shearAbscissa t (cfg i))) :
    Finset ℝ := by
  classical
  exact Finset.univ.image (sixIntervalSlope cfg t hinj)

/-- The corresponding finite projective-direction census. -/
noncomputable def sixIntervalDirections
    (cfg : Configuration (Fin 6)) (t : ℝ)
    (hinj : Function.Injective (fun i => shearAbscissa t (cfg i))) :
    Finset (Submodule ℝ Point2) := by
  classical
  exact Finset.univ.image (sixIntervalDirection cfg t hinj)

private theorem card_image_eq_card_image_of_eq_iff
    {X A B : Type*} [DecidableEq X] [DecidableEq A] [DecidableEq B]
    (s : Finset X) (f : X → A) (g : X → B)
    (hkernel : ∀ x ∈ s, ∀ y ∈ s, f x = f y ↔ g x = g y) :
    (s.image f).card = (s.image g).card := by
  classical
  let rep (a : A) (ha : a ∈ s.image f) : X :=
    Classical.choose (Finset.mem_image.mp ha)
  have hrep (a : A) (ha : a ∈ s.image f) :
      rep a ha ∈ s ∧ f (rep a ha) = a :=
    Classical.choose_spec (Finset.mem_image.mp ha)
  apply Finset.card_bij (fun a ha => g (rep a ha))
  · intro a ha
    exact Finset.mem_image.mpr ⟨rep a ha, (hrep a ha).1, rfl⟩
  · intro a ha b hb hab
    calc
      a = f (rep a ha) := (hrep a ha).2.symm
      _ = f (rep b hb) :=
        (hkernel _ (hrep a ha).1 _ (hrep b hb).1).2 hab
      _ = b := (hrep b hb).2
  · intro b hb
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hb
    have hfx : f x ∈ s.image f := Finset.mem_image.mpr ⟨x, hx, rfl⟩
    refine ⟨f x, hfx, ?_⟩
    apply (hkernel _ (hrep (f x) hfx).1 _ hx).1
    exact (hrep (f x) hfx).2

theorem sixIntervalDirection_eq_iff_slope_eq
    (cfg : Configuration (Fin 6)) (t : ℝ)
    (hinj : Function.Injective (fun i => shearAbscissa t (cfg i)))
    (e f : Fin 15) :
    sixIntervalDirection cfg t hinj e = sixIntervalDirection cfg t hinj f ↔
      sixIntervalSlope cfg t hinj e = sixIntervalSlope cfg t hinj f := by
  apply directionOfPoints_eq_iff_shearSlope_eq t
  · apply hinj.ne
    apply (shearSortedLabel cfg t hinj).injective.ne
    exact ne_of_lt (sixIntervalLeft_lt_right e)
  · apply hinj.ne
    apply (shearSortedLabel cfg t hinj).injective.ne
    exact ne_of_lt (sixIntervalLeft_lt_right f)

theorem card_sixIntervalSlopes_eq_card_sixIntervalDirections
    (cfg : Configuration (Fin 6)) (t : ℝ)
    (hinj : Function.Injective (fun i => shearAbscissa t (cfg i))) :
    (sixIntervalSlopes cfg t hinj).card =
      (sixIntervalDirections cfg t hinj).card := by
  classical
  apply card_image_eq_card_image_of_eq_iff Finset.univ
    (sixIntervalSlope cfg t hinj) (sixIntervalDirection cfg t hinj)
  intro e _ f _
  exact (sixIntervalDirection_eq_iff_slope_eq cfg t hinj e f).symm

theorem sixIntervalDirections_subset_determinedDirections
    (cfg : Configuration (Fin 6)) (t : ℝ)
    (hinj : Function.Injective (fun i => shearAbscissa t (cfg i))) :
    sixIntervalDirections cfg t hinj ⊆ determinedDirections cfg := by
  classical
  intro D hD
  obtain ⟨e, _he, rfl⟩ := Finset.mem_image.mp hD
  let a := shearSortedLabel cfg t hinj (sixIntervalLeft e)
  let b := shearSortedLabel cfg t hinj (sixIntervalRight e)
  have hab : a ≠ b := by
    exact (shearSortedLabel cfg t hinj).injective.ne
      (ne_of_lt (sixIntervalLeft_lt_right e))
  rw [show sixIntervalDirection cfg t hinj e =
      directionOfPair cfg ⟨{a, b}, by simp [hab]⟩ by
    symm
    exact directionOfPair_eq_directionOfPoints cfg hab]
  exact directionOfPair_mem_determinedDirections cfg _

theorem card_sixIntervalSlopes_le_determinedDirections
    (cfg : Configuration (Fin 6)) (t : ℝ)
    (hinj : Function.Injective (fun i => shearAbscissa t (cfg i))) :
    (sixIntervalSlopes cfg t hinj).card ≤
      (determinedDirections cfg).card := by
  rw [card_sixIntervalSlopes_eq_card_sixIntervalDirections]
  exact Finset.card_le_card
    (sixIntervalDirections_subset_determinedDirections cfg t hinj)

theorem sixIntervalSlope_index
    (cfg : Configuration (Fin 6)) (t : ℝ)
    (hinj : Function.Injective (fun i => shearAbscissa t (cfg i)))
    {i j : Fin 6} (hij : i < j) :
    sixIntervalSlope cfg t hinj (sixIntervalIndex i j) =
      shearSlope t
        (cfg (shearSortedLabel cfg t hinj i))
        (cfg (shearSortedLabel cfg t hinj j)) := by
  have hend := sixInterval_endpoints_index hij
  simp only [sixIntervalSlope, hend.1, hend.2]

/-- Every unordered selected pair is presented by a unique interval in the
sorted row, up to reversing its orientation. -/
theorem exists_sixInterval_directionOfPoints_eq
    (cfg : Configuration (Fin 6)) (t : ℝ)
    (hinj : Function.Injective (fun i => shearAbscissa t (cfg i)))
    {a b : Fin 6} (hab : a ≠ b) :
    ∃ e : Fin 15,
      directionOfPoints (cfg a) (cfg b) =
        directionOfPoints
          (cfg (shearSortedLabel cfg t hinj (sixIntervalLeft e)))
          (cfg (shearSortedLabel cfg t hinj (sixIntervalRight e))) := by
  let ia := (shearSortedLabel cfg t hinj).symm a
  let ib := (shearSortedLabel cfg t hinj).symm b
  have hiab : ia ≠ ib := by
    intro h
    apply hab
    simpa only [ia, ib] using
      (shearSortedLabel cfg t hinj).symm.injective h
  rcases lt_or_gt_of_ne hiab with hlt | hgt
  · let e := sixIntervalIndex ia ib
    refine ⟨e, ?_⟩
    have hend := sixInterval_endpoints_index hlt
    rw [show sixIntervalLeft e = ia by exact hend.1,
      show sixIntervalRight e = ib by exact hend.2]
    simp only [ia, ib, Equiv.apply_symm_apply]
  · let e := sixIntervalIndex ib ia
    refine ⟨e, ?_⟩
    have hend := sixInterval_endpoints_index hgt
    rw [show sixIntervalLeft e = ib by exact hend.1,
      show sixIntervalRight e = ia by exact hend.2]
    simp only [ia, ib, Equiv.apply_symm_apply]
    exact directionOfPoints_comm (cfg a) (cfg b)

/-! ## The weighted-average rule -/

/-- A secant slope over `[i,k]` is the positive weighted average of the
two secant slopes obtained by splitting at `j`. -/
theorem shearSlope_between_or_equal
    {cfg : Configuration (Fin 6)} {t : ℝ}
    (hinj : Function.Injective (fun i => shearAbscissa t (cfg i)))
    {i j k : Fin 6} (hij : i < j) (hjk : j < k) :
    let label := shearSortedLabel cfg t hinj
    let a := shearSlope t (cfg (label i)) (cfg (label j))
    let b := shearSlope t (cfg (label j)) (cfg (label k))
    let c := shearSlope t (cfg (label i)) (cfg (label k))
    (a = b ∧ c = a) ∨ (a < c ∧ c < b) ∨ (b < c ∧ c < a) := by
  dsimp only
  let label := shearSortedLabel cfg t hinj
  let xi := shearAbscissa t (cfg (label i))
  let xj := shearAbscissa t (cfg (label j))
  let xk := shearAbscissa t (cfg (label k))
  let yi := shearOrdinate (cfg (label i))
  let yj := shearOrdinate (cfg (label j))
  let yk := shearOrdinate (cfg (label k))
  have hxij : xi < xj := by
    exact (shearSortedLabel_abscissa_lt_iff cfg t hinj i j).2 hij
  have hxjk : xj < xk := by
    exact (shearSortedLabel_abscissa_lt_iff cfg t hinj j k).2 hjk
  have hxic : xi < xk := hxij.trans hxjk
  have hxij0 : xj - xi ≠ 0 := sub_ne_zero.mpr (ne_of_gt hxij)
  have hxjk0 : xk - xj ≠ 0 := sub_ne_zero.mpr (ne_of_gt hxjk)
  have hxic0 : xk - xi ≠ 0 := sub_ne_zero.mpr (ne_of_gt hxic)
  let a := (yj - yi) / (xj - xi)
  let b := (yk - yj) / (xk - xj)
  let c := (yk - yi) / (xk - xi)
  have ha :
      shearSlope t (cfg (label i)) (cfg (label j)) = a := rfl
  have hb :
      shearSlope t (cfg (label j)) (cfg (label k)) = b := rfl
  have hc :
      shearSlope t (cfg (label i)) (cfg (label k)) = c := rfl
  rw [ha, hb, hc]
  by_cases hab : a = b
  · left
    refine ⟨hab, ?_⟩
    dsimp [a, b, c] at hab ⊢
    field_simp [hxij0, hxjk0, hxic0] at hab ⊢
    nlinarith [hab]
  · rcases lt_or_gt_of_ne hab with hablt | habgt
    · right
      left
      constructor
      · dsimp [a, b, c] at *
        rw [div_lt_div_iff₀ (sub_pos.mpr hxij) (sub_pos.mpr hxic)]
        rw [div_lt_div_iff₀ (sub_pos.mpr hxij) (sub_pos.mpr hxjk)] at hablt
        nlinarith
      · dsimp [a, b, c] at *
        rw [div_lt_div_iff₀ (sub_pos.mpr hxic) (sub_pos.mpr hxjk)]
        rw [div_lt_div_iff₀ (sub_pos.mpr hxij) (sub_pos.mpr hxjk)] at hablt
        nlinarith
    · right
      right
      constructor
      · dsimp [a, b, c] at *
        rw [div_lt_div_iff₀ (sub_pos.mpr hxjk) (sub_pos.mpr hxic)]
        rw [div_lt_div_iff₀ (sub_pos.mpr hxjk) (sub_pos.mpr hxij)] at habgt
        nlinarith
      · dsimp [a, b, c] at *
        rw [div_lt_div_iff₀ (sub_pos.mpr hxic) (sub_pos.mpr hxij)]
        rw [div_lt_div_iff₀ (sub_pos.mpr hxjk) (sub_pos.mpr hxij)] at habgt
        nlinarith

/-! ## Ranking at most five slopes -/

/-- Increasing rank of a member of a finite real set inside a prescribed
finite ordinal. -/
noncomputable def finsetRealRankIntoFin
    {m : ℕ} (s : Finset ℝ) (hcard : s.card ≤ m)
    (x : ℝ) (hx : x ∈ s) : Fin m := by
  classical
  let S := {y : ℝ // y ∈ s}
  let rank : S → Fin (Fintype.card S) :=
    (Fintype.orderIsoFinOfCardEq S rfl).symm
  have hsize : Fintype.card S ≤ m := by
    simpa only [S, Fintype.card_coe] using hcard
  exact Fin.castLE hsize (rank ⟨x, hx⟩)

theorem finsetRealRankIntoFin_lt_iff
    {m : ℕ} (s : Finset ℝ) (hcard : s.card ≤ m)
    {x y : ℝ} (hx : x ∈ s) (hy : y ∈ s) :
    finsetRealRankIntoFin s hcard x hx <
        finsetRealRankIntoFin s hcard y hy ↔ x < y := by
  classical
  let S := {z : ℝ // z ∈ s}
  have hsize : Fintype.card S ≤ m := by
    simpa only [S, Fintype.card_coe] using hcard
  change Fin.castLE hsize
      ((Fintype.orderIsoFinOfCardEq S rfl).symm ⟨x, hx⟩) <
        Fin.castLE hsize
          ((Fintype.orderIsoFinOfCardEq S rfl).symm ⟨y, hy⟩) ↔ x < y
  rw [Fin.castLE_lt_castLE_iff hsize]
  exact (Fintype.orderIsoFinOfCardEq S rfl).symm.lt_iff_lt

theorem finsetRealRankIntoFin_eq_iff
    {m : ℕ} (s : Finset ℝ) (hcard : s.card ≤ m)
    {x y : ℝ} (hx : x ∈ s) (hy : y ∈ s) :
    finsetRealRankIntoFin s hcard x hx =
        finsetRealRankIntoFin s hcard y hy ↔ x = y := by
  constructor
  · intro h
    by_contra hxy
    rcases lt_or_gt_of_ne hxy with hlt | hgt
    · exact (ne_of_lt
        ((finsetRealRankIntoFin_lt_iff s hcard hx hy).2 hlt)) h
    · exact (ne_of_gt
        ((finsetRealRankIntoFin_lt_iff s hcard hy hx).2 hgt)) h
  · intro h
    subst y
    rfl

/-- Rank coloring of the fifteen interval slopes when their census has
cardinality at most five. -/
noncomputable def sixIntervalSlopeColoring
    (cfg : Configuration (Fin 6)) (t : ℝ)
    (hinj : Function.Injective (fun i => shearAbscissa t (cfg i)))
    (hcard : (sixIntervalSlopes cfg t hinj).card ≤ 5) :
    SixIntervalColoring := fun e =>
  finsetRealRankIntoFin (sixIntervalSlopes cfg t hinj) hcard
    (sixIntervalSlope cfg t hinj e)
    (Finset.mem_image.mpr ⟨e, Finset.mem_univ _, rfl⟩)

theorem sixIntervalSlopeColoring_lt_iff
    (cfg : Configuration (Fin 6)) (t : ℝ)
    (hinj : Function.Injective (fun i => shearAbscissa t (cfg i)))
    (hcard : (sixIntervalSlopes cfg t hinj).card ≤ 5)
    (e f : Fin 15) :
    sixIntervalSlopeColoring cfg t hinj hcard e <
        sixIntervalSlopeColoring cfg t hinj hcard f ↔
      sixIntervalSlope cfg t hinj e < sixIntervalSlope cfg t hinj f := by
  apply finsetRealRankIntoFin_lt_iff

theorem sixIntervalSlopeColoring_eq_iff
    (cfg : Configuration (Fin 6)) (t : ℝ)
    (hinj : Function.Injective (fun i => shearAbscissa t (cfg i)))
    (hcard : (sixIntervalSlopes cfg t hinj).card ≤ 5)
    (e f : Fin 15) :
    sixIntervalSlopeColoring cfg t hinj hcard e =
        sixIntervalSlopeColoring cfg t hinj hcard f ↔
      sixIntervalSlope cfg t hinj e = sixIntervalSlope cfg t hinj f := by
  apply finsetRealRankIntoFin_eq_iff

theorem sixIntervalSlopeColoring_allowed
    (cfg : Configuration (Fin 6)) (t : ℝ)
    (hinj : Function.Injective (fun i => shearAbscissa t (cfg i)))
    (hcard : (sixIntervalSlopes cfg t hinj).card ≤ 5) :
    ∀ e, NewIntervalAllowed
      (sixIntervalSlopeColoring cfg t hinj hcard) e
      (sixIntervalSlopeColoring cfg t hinj hcard e) := by
  intro e j hleft hright
  let a := sixIntervalIndex (sixIntervalLeft e) j
  let b := sixIntervalIndex j (sixIntervalRight e)
  have hleftSlope :
      sixIntervalSlope cfg t hinj a =
        shearSlope t
          (cfg (shearSortedLabel cfg t hinj (sixIntervalLeft e)))
          (cfg (shearSortedLabel cfg t hinj j)) :=
    sixIntervalSlope_index cfg t hinj hleft
  have hrightSlope :
      sixIntervalSlope cfg t hinj b =
        shearSlope t
          (cfg (shearSortedLabel cfg t hinj j))
          (cfg (shearSortedLabel cfg t hinj (sixIntervalRight e))) :=
    sixIntervalSlope_index cfg t hinj hright
  have hwholeSlope :
      sixIntervalSlope cfg t hinj e =
        shearSlope t
          (cfg (shearSortedLabel cfg t hinj (sixIntervalLeft e)))
          (cfg (shearSortedLabel cfg t hinj (sixIntervalRight e))) := rfl
  have hbetween := shearSlope_between_or_equal hinj hleft hright
  dsimp only at hbetween
  rw [← hleftSlope, ← hrightSlope, ← hwholeSlope] at hbetween
  unfold BetweenOrEqual
  rcases hbetween with hsame | hbetween | hbetween
  · left
    exact ⟨(sixIntervalSlopeColoring_eq_iff cfg t hinj hcard a b).2 hsame.1,
      (sixIntervalSlopeColoring_eq_iff cfg t hinj hcard e a).2 hsame.2⟩
  · right
    left
    exact ⟨(sixIntervalSlopeColoring_lt_iff cfg t hinj hcard a e).2 hbetween.1,
      (sixIntervalSlopeColoring_lt_iff cfg t hinj hcard e b).2 hbetween.2⟩
  · right
    right
    exact ⟨(sixIntervalSlopeColoring_lt_iff cfg t hinj hcard b e).2 hbetween.1,
      (sixIntervalSlopeColoring_lt_iff cfg t hinj hcard e a).2 hbetween.2⟩

/-! ## Ungar's six-point conclusion -/

/-- Every noncollinear configuration of six distinct real affine points
determines at least six projective directions. -/
theorem six_le_card_determinedDirections_of_noncollinear_finSix
    (cfg : Configuration (Fin 6)) (hnon : Noncollinear cfg) :
    6 ≤ (determinedDirections cfg).card := by
  classical
  by_contra hlt
  have hdirCard : (determinedDirections cfg).card ≤ 5 := by omega
  obtain ⟨t, hinj⟩ := exists_shearAbscissa_injective cfg
  have hslopeCard : (sixIntervalSlopes cfg t hinj).card ≤ 5 :=
    (card_sixIntervalSlopes_le_determinedDirections cfg t hinj).trans hdirCard
  let coloring := sixIntervalSlopeColoring cfg t hinj hslopeCard
  have hcolorConstant : ∀ e, coloring e = coloring 0 := by
    apply sixIntervalColoring_constant coloring
    exact sixIntervalSlopeColoring_allowed cfg t hinj hslopeCard
  have hslopeConstant :
      ∀ e f, sixIntervalSlope cfg t hinj e =
        sixIntervalSlope cfg t hinj f := by
    intro e f
    apply (sixIntervalSlopeColoring_eq_iff cfg t hinj hslopeCard e f).1
    exact (hcolorConstant e).trans (hcolorConstant f).symm
  obtain ⟨c, htriangle⟩ := exists_noncollinear_triple_finSix cfg hnon
  have hc0 : c ≠ 0 := by
    intro hc
    subst c
    apply htriangle
    simpa using (collinear_pair ℝ (cfg 1) (cfg 0))
  obtain ⟨e01, he01⟩ :=
    exists_sixInterval_directionOfPoints_eq cfg t hinj
      (show (0 : Fin 6) ≠ 1 by decide)
  obtain ⟨e0c, he0c⟩ :=
    exists_sixInterval_directionOfPoints_eq cfg t hinj hc0.symm
  apply directionOfPoints_ne_of_not_collinear htriangle
  calc
    directionOfPoints (cfg 0) (cfg 1) =
        sixIntervalDirection cfg t hinj e01 := by
      simpa only [sixIntervalDirection] using he01
    _ = sixIntervalDirection cfg t hinj e0c :=
      (sixIntervalDirection_eq_iff_slope_eq cfg t hinj e01 e0c).2
        (hslopeConstant e01 e0c)
    _ = directionOfPoints (cfg 0) (cfg c) := by
      simpa only [sixIntervalDirection] using he0c.symm

end Erdos506.Incidence
