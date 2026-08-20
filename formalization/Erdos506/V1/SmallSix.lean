import Erdos506.V1.RichBlockPencil
import Erdos506.V3.MenelausPower

/-!
# The corrected six-point V1 case

The rich-circle pencil gives seven circles from a four-point circle and its
two outsiders.  Equality is the only delicate case.  Its incidence pattern
is a complete quadrilateral carrying three specified four-point circles.
The geometric kernel below rules out precisely that pattern.  Unlike the
obsolete affine normalization, it retains the two squared direction lengths
and their mixed product, so every coordinate change used in the argument is
Euclidean-safe (equivalently, one may first apply a similarity).
-/

namespace Erdos506.V1

open Erdos506.V3
open Erdos506.V4

/-- The arithmetic equality face left by the six-point block rows.  Here
`B₃` is the number of three-blocks, `b` the number of four-circles, `L`
the number of three-point lines, and `C` the total circle count. -/
theorem six_terminal_census
    {B₃ b L C : ℕ}
    (htriple : B₃ + 4 * b = 20)
    (hpivot : 18 ≤ 3 * B₃)
    (hcircles : C = 20 - 3 * b - L)
    (hlines : L ≤ 4)
    (hsmall : C ≤ 7) :
    B₃ = 8 ∧ b = 3 ∧ L = 4 ∧ C = 7 := by
  omega

/-- Algebraic core of the similarity-safe complete-quadrilateral argument.
`E` and `F` are the squared lengths of two independent directions, `D` is
their scalar product, and `G,H` are the two remaining squared lengths. -/
theorem pasch_three_circles_algebra
    {a b t w E F D G H : ℝ}
    (hF : F ≠ 0) (hw : w ≠ 0) (hb0 : b ≠ 0) (hb1 : b ≠ 1)
    (hG : G = b ^ 2 * F - 2 * a * b * D + a ^ 2 * E)
    (hH : H = F - 2 * D + E)
    (hcoeff₁ : 1 - t = a * (1 - w))
    (hcoeff₂ : t = w * b)
    (hcircle₀ : a * (a - 1) * E = w * G)
    (hcircle₁ : (1 - a) * E = t * H)
    (hcircle₂ : a * E = b * F) : False := by
  have hrel : 1 - a = w * (b - a) := by
    rw [hcoeff₂] at hcoeff₁
    nlinarith
  have hrel₁ := congrArg (fun x : ℝ => x * E) hrel
  have hq₁ : (b - a) * E = b * H := by
    apply mul_left_cancel₀ hw
    calc
      w * ((b - a) * E) = (w * (b - a)) * E := by ring
      _ = (1 - a) * E := hrel₁.symm
      _ = t * H := hcircle₁
      _ = w * (b * H) := by rw [hcoeff₂]; ring
  have hrel₀ : a - 1 = w * (a - b) := by linarith
  have hrel₀' := congrArg (fun x : ℝ => a * x * E) hrel₀
  have hq₀ : a * (a - b) * E = G := by
    apply mul_left_cancel₀ hw
    calc
      w * (a * (a - b) * E) = a * (w * (a - b)) * E := by ring
      _ = a * (a - 1) * E := hrel₀'.symm
      _ = w * G := hcircle₀
  have hbDF : b * (D - F) = 0 := by
    rw [hH] at hq₁
    nlinarith
  have hDF : D = F := by
    exact sub_eq_zero.mp ((mul_eq_zero.mp hbDF).resolve_left hb0)
  rw [hDF] at hG
  have hcircle₂b := congrArg (fun x : ℝ => b * x) hcircle₂
  have hbFab : b * F * (a - b) = 0 := by
    nlinarith
  have hab : a = b := by
    have := (mul_eq_zero.mp hbFab).resolve_left (mul_ne_zero hb0 hF)
    exact sub_eq_zero.mp this
  rw [hab] at hcoeff₁
  rw [hcoeff₂] at hcoeff₁
  have : b = 1 := by
    nlinarith
  exact hb1 this

/-- Coefficient comparison at the fourth side of a complete quadrilateral.
The nonzero determinant says that the two displayed directions form a real
basis; no affine change of metric is made. -/
theorem pasch_parameter_relations
    {A B C X U W : Point2} {a b t w : ℝ}
    (hdet : det2 (B - A) (C - A) ≠ 0)
    (hX : affineParamPoint A (B - A) a = X)
    (hU : affineParamPoint A (C - A) b = U)
    (hW : affineParamPoint B (C - B) t = W)
    (hXUW : affineParamPoint X (U - X) w = W) :
    1 - t = a * (1 - w) ∧ t = w * b := by
  rw [← hX, ← hU, ← hW] at hXUW
  let r : ℝ := a * (1 - w) - (1 - t)
  let s : ℝ := w * b - t
  have hcoord (i : Fin 2) :
      r * (B - A) i + s * (C - A) i = 0 := by
    have hi := congrArg (fun q : Point2 => q i) hXUW
    simp [affineParamPoint] at hi
    dsimp [r, s]
    nlinarith
  have hrDet : r * det2 (B - A) (C - A) = 0 := by
    calc
      r * det2 (B - A) (C - A) =
          (C - A) 1 * (r * (B - A) 0 + s * (C - A) 0) -
            (C - A) 0 * (r * (B - A) 1 + s * (C - A) 1) := by
              simp [det2]
              ring
      _ = 0 := by rw [hcoord 0, hcoord 1]; ring
  have hsDet : s * det2 (B - A) (C - A) = 0 := by
    calc
      s * det2 (B - A) (C - A) =
          (B - A) 0 * (r * (B - A) 1 + s * (C - A) 1) -
            (B - A) 1 * (r * (B - A) 0 + s * (C - A) 0) := by
              simp [det2]
              ring
      _ = 0 := by rw [hcoord 0, hcoord 1]; ring
  have hr : r = 0 := (mul_eq_zero.mp hrDet).resolve_right hdet
  have hs : s = 0 := (mul_eq_zero.mp hsDet).resolve_right hdet
  constructor <;> dsimp [r, s] at hr hs <;> linarith

/-- Three four-point circles cannot occur on the six vertices of a real
complete quadrilateral in the indicated complementary-diagonal pattern.

This is the geometric obstruction needed on the equality face of the
six-point rich-circle pencil.  The proof is similarity-safe: `A,B,C` remain
an arbitrary noncollinear triangle, rather than being sent by a general
affine map to a right isosceles triangle. -/
theorem no_pasch_three_circle_pattern
    {A B C X U W : Point2} {a b t w : ℝ}
    (hdet : det2 (B - A) (C - A) ≠ 0)
    (ha0 : a ≠ 0) (ha1 : a ≠ 1)
    (hb0 : b ≠ 0) (hb1 : b ≠ 1)
    (ht1 : t ≠ 1) (hw0 : w ≠ 0) (hw1 : w ≠ 1)
    (hX : affineParamPoint A (B - A) a = X)
    (hU : affineParamPoint A (C - A) b = U)
    (hW : affineParamPoint B (C - B) t = W)
    (hXUW : affineParamPoint X (U - X) w = W)
    (c₀ c₁ c₂ : ProperCircle)
    (hc₀A : A ∈ (c₀.1 : Set Point2))
    (hc₀B : B ∈ (c₀.1 : Set Point2))
    (hc₀U : U ∈ (c₀.1 : Set Point2))
    (hc₀W : W ∈ (c₀.1 : Set Point2))
    (hc₁A : A ∈ (c₁.1 : Set Point2))
    (hc₁X : X ∈ (c₁.1 : Set Point2))
    (hc₁C : C ∈ (c₁.1 : Set Point2))
    (hc₁W : W ∈ (c₁.1 : Set Point2))
    (hc₂B : B ∈ (c₂.1 : Set Point2))
    (hc₂X : X ∈ (c₂.1 : Set Point2))
    (hc₂C : C ∈ (c₂.1 : Set Point2))
    (hc₂U : U ∈ (c₂.1 : Set Point2)) : False := by
  obtain ⟨hcoeff₁, hcoeff₂⟩ :=
    pasch_parameter_relations hdet hX hU hW hXUW
  let E := directionSq (B - A)
  let F := directionSq (C - A)
  let D := (B - A) 0 * (C - A) 0 + (B - A) 1 * (C - A) 1
  let G := directionSq (U - X)
  let H := directionSq (C - B)
  have hAB : A ≠ B := by
    intro h
    subst B
    simp [det2] at hdet
  have hAC : A ≠ C := by
    intro h
    subst C
    simp [det2] at hdet
  have hF : F ≠ 0 := by
    exact directionSq_sub_ne_zero hAC.symm
  have hG : G = b ^ 2 * F - 2 * a * b * D + a ^ 2 * E := by
    dsimp [G, F, D, E]
    rw [← hX, ← hU]
    simp [directionSq, affineParamPoint]
    ring
  have hH : H = F - 2 * D + E := by
    dsimp [H, F, D, E]
    simp [directionSq]
    ring
  have hXA : affineParamPoint X (B - A) (-a) = A := by
    rw [← hX]
    ext i
    simp [affineParamPoint]
  have hXB : affineParamPoint X (B - A) (1 - a) = B := by
    rw [← hX]
    ext i
    simp [affineParamPoint]
    ring
  have hp₀ := directed_power_of_four_cocircular_points c₀ X
    (B - A) (U - X) (t₁ := -a) (t₂ := 1 - a) (s₁ := 1) (s₂ := w)
    (by linarith) (by exact ne_comm.mp hw1)
    (by rw [hXA]; exact hc₀A) (by rw [hXB]; exact hc₀B)
    (by simpa using hc₀U) (by rw [hXUW]; exact hc₀W)
  have hcircle₀ : a * (a - 1) * E = w * G := by
    dsimp [E, G]
    nlinarith
  have hBX : affineParamPoint B (A - B) (1 - a) = X := by
    rw [← hX]
    ext i
    simp [affineParamPoint]
    ring
  have hp₁ := directed_power_of_four_cocircular_points c₁ B
    (A - B) (C - B) (t₁ := 1) (t₂ := 1 - a) (s₁ := 1) (s₂ := t)
    (by exact fun h => ha0 (by linarith)) (by exact ne_comm.mp ht1)
    (by simpa using hc₁A) (by rw [hBX]; exact hc₁X)
    (by simpa using hc₁C) (by rw [hW]; exact hc₁W)
  have hcircle₁ : (1 - a) * E = t * H := by
    dsimp [E, H]
    rw [directionSq_sub_comm A B] at hp₁
    nlinarith
  have hp₂ := directed_power_of_four_cocircular_points c₂ A
    (B - A) (C - A) (t₁ := 1) (t₂ := a) (s₁ := 1) (s₂ := b)
    (by exact ne_comm.mp ha1) (by exact ne_comm.mp hb1)
    (by simpa using hc₂B) (by rw [hX]; exact hc₂X)
    (by simpa using hc₂C) (by rw [hU]; exact hc₂U)
  have hcircle₂ : a * E = b * F := by
    dsimp [E, F]
    nlinarith
  exact pasch_three_circles_algebra hF hw0 hb0 hb1 hG hH
    hcoeff₁ hcoeff₂ hcircle₀ hcircle₁ hcircle₂

/-- Labelled form of `no_pasch_three_circle_pattern`.  This is the terminal
geometric interface expected from the finite equality classifier: the four
three-point lines are `012,034,135,245`, while the three four-circles are
`0145,0235,1234`. -/
theorem no_labelled_pasch_three_circle_pattern
    (p : Fin 6 → Point2) (hp : Function.Injective p)
    (hdet : det2 (p 1 - p 0) (p 3 - p 0) ≠ 0)
    (hline₂ : p 2 ∈ affineSpan ℝ ({p 0, p 1} : Set Point2))
    (hline₄ : p 4 ∈ affineSpan ℝ ({p 0, p 3} : Set Point2))
    (hline₅₁₃ : p 5 ∈ affineSpan ℝ ({p 1, p 3} : Set Point2))
    (hline₅₂₄ : p 5 ∈ affineSpan ℝ ({p 2, p 4} : Set Point2))
    (c₀ c₁ c₂ : ProperCircle)
    (hc₀ : ∀ i ∈ ({0, 1, 4, 5} : Finset (Fin 6)),
      p i ∈ (c₀.1 : Set Point2))
    (hc₁ : ∀ i ∈ ({0, 2, 3, 5} : Finset (Fin 6)),
      p i ∈ (c₁.1 : Set Point2))
    (hc₂ : ∀ i ∈ ({1, 2, 3, 4} : Finset (Fin 6)),
      p i ∈ (c₂.1 : Set Point2)) : False := by
  obtain ⟨a, haLine⟩ :=
    mem_affineSpan_pair_iff_exists_lineMap_eq.mp hline₂
  obtain ⟨b, hbLine⟩ :=
    mem_affineSpan_pair_iff_exists_lineMap_eq.mp hline₄
  obtain ⟨t, htLine⟩ :=
    mem_affineSpan_pair_iff_exists_lineMap_eq.mp hline₅₁₃
  obtain ⟨w, hwLine⟩ :=
    mem_affineSpan_pair_iff_exists_lineMap_eq.mp hline₅₂₄
  have ha : affineParamPoint (p 0) (p 1 - p 0) a = p 2 := by
    simpa [affineParamPoint, AffineMap.lineMap_apply, add_comm] using haLine
  have hb : affineParamPoint (p 0) (p 3 - p 0) b = p 4 := by
    simpa [affineParamPoint, AffineMap.lineMap_apply, add_comm] using hbLine
  have ht : affineParamPoint (p 1) (p 3 - p 1) t = p 5 := by
    simpa [affineParamPoint, AffineMap.lineMap_apply, add_comm] using htLine
  have hw : affineParamPoint (p 2) (p 4 - p 2) w = p 5 := by
    simpa [affineParamPoint, AffineMap.lineMap_apply, add_comm] using hwLine
  have ha0 : a ≠ 0 := by
    intro h
    have heq : p 2 = p 0 := by rw [← ha, h, affineParamPoint_zero]
    exact (by simpa using hp heq)
  have ha1 : a ≠ 1 := by
    intro h
    have heq : p 2 = p 1 := by rw [← ha, h, affineParamPoint_endpoint]
    exact (by simpa using hp heq)
  have hb0 : b ≠ 0 := by
    intro h
    have heq : p 4 = p 0 := by rw [← hb, h, affineParamPoint_zero]
    exact (by simpa using hp heq)
  have hb1 : b ≠ 1 := by
    intro h
    have heq : p 4 = p 3 := by rw [← hb, h, affineParamPoint_endpoint]
    exact (by simpa using hp heq)
  have ht1 : t ≠ 1 := by
    intro h
    have heq : p 5 = p 3 := by rw [← ht, h, affineParamPoint_endpoint]
    exact (by simpa using hp heq)
  have hw0 : w ≠ 0 := by
    intro h
    have heq : p 5 = p 2 := by rw [← hw, h, affineParamPoint_zero]
    exact (by simpa using hp heq)
  have hw1 : w ≠ 1 := by
    intro h
    have heq : p 5 = p 4 := by rw [← hw, h, affineParamPoint_endpoint]
    exact (by simpa using hp heq)
  exact no_pasch_three_circle_pattern hdet ha0 ha1 hb0 hb1 ht1 hw0 hw1
    ha hb ht hw c₀ c₁ c₂
    (hc₀ 0 (by decide)) (hc₀ 1 (by decide))
    (hc₀ 4 (by decide)) (hc₀ 5 (by decide))
    (hc₁ 0 (by decide)) (hc₁ 2 (by decide))
    (hc₁ 3 (by decide)) (hc₁ 5 (by decide))
    (hc₂ 1 (by decide)) (hc₂ 2 (by decide))
    (hc₂ 3 (by decide)) (hc₂ 4 (by decide))

end Erdos506.V1
